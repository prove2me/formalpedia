-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_compact_preleft_C2_physical_mesh_expected_L1_remainder_vanish
-- name    : AvramDividend.Classical.avram_b24_original_compact_preleft_C2_physical_mesh_expected_L1_remainder_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:12:19.963922+00:00
-- url     : https://prove2.me/theorems/afbbf0b9-2e90-4a0f-a475-447b557e6011
-- title:
--   Original compact pre-left C2 physical Ito mesh expected absolute remainder tends to zero
-- statement:
--   On a true original Levy process physical mesh restricted to a compact C2 pre-left postpayment reserve event, if all actual centred source cell increments vanish uniformly with refining mesh and their expected quadratic energy is uniformly bounded, then the expected absolute original C2 Taylor remainder tends to zero.
-- source:
--   New B24 epsilon-energy original compact mesh theorem plus proved uniform quadratic energy epsilon absorption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_compact_preleft_C2_physical_mesh_expected_L1_remainder_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (A : Set Ω) (S : ℕ → Finset ℕ) (s t : ℕ → ℕ → ℝ≥0)
    (M : ℝ) :
    let z : ℕ → Ω → ℕ → ℝ := fun k ω i =>
      Function.leftLim (fun u : ℝ≥0 =>
        x + X.X u ω - rightLimit D u ω) (s k i)
    let g : ℕ → Ω → ℕ → ℝ := fun k ω i =>
      X.X (t k i) ω - X.X (s k i) ω -
        ((t k i - s k i : ℝ≥0) : ℝ) * X.c
    let R : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ S k,
      (w (z k ω i + g k ω i) -
        taylorWithinEval w 1
          (Set.uIcc (z k ω i) (z k ω i + g k ω i))
          (z k ω i) (z k ω i + g k ω i) -
        (iteratedDeriv 2 w (z k ω i) * (g k ω i)^2) / 2)
    let Q : ℕ → Ω → ℝ := fun k ω =>
      ∑ i ∈ S k, (g k ω i)^2
    (∀ k, ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S k,
      z k ω i ∈ Icc a b ∧ z k ω i + g k ω i ∈ Icc a b ∧
        z k ω i ≠ z k ω i + g k ω i) →
    (∀ δ : ℝ, 0 < δ → ∃ K : ℕ, ∀ k, K ≤ k →
      ∀ᵐ ω ∂(P.restrict A), ∀ i ∈ S k,
        dist (z k ω i + g k ω i) (z k ω i) < δ) →
    (∀ k, AEStronglyMeasurable (Q k) (P.restrict A)) →
    (∀ k, AEStronglyMeasurable (fun ω => |R k ω|) (P.restrict A)) →
    (0 ≤ M) →
    (∀ k, (∫ ω in A, Q k ω ∂P) ≤ M) →
    Tendsto (fun k => ∫ ω in A, |R k ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
