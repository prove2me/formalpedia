-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_ordered_real_time_C2_physical_mesh_L1_remainder_vanish
-- name    : AvramDividend.Classical.avram_b24_original_ordered_real_time_C2_physical_mesh_L1_remainder_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:20:27.387194+00:00
-- url     : https://prove2.me/theorems/436ba446-bc9f-4e74-aee6-985e2ac37463
-- title:
--   Ordered original stopped Gaussian C2 physical real-time mesh expected L1 remainder vanishes
-- statement:
--   For a refining ordered physical source grid with real-time centred Gaussian increments, compact C2 pre-left reserve control, eventual vanishing physical increments, and uniformly bounded quadratic energy, the actual original source Taylor residual tends to zero in L1 on the compact stopped event.
-- source:
--   New B24 epsilon-energy original compact mesh theorem plus proved uniform quadratic energy epsilon absorption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_ordered_real_time_C2_physical_mesh_L1_remainder_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (A : Set Ω) (S : ℕ → Finset ℕ) (s t : ℕ → ℕ → ℝ≥0)
    (hOrdered : ∀ k i, i ∈ S k → s k i ≤ t k i)
    (M : ℝ) :
    let z : ℕ → Ω → ℕ → ℝ := fun k ω i =>
      Function.leftLim (fun u : ℝ≥0 =>
        x + X.X u ω - rightLimit D u ω) (s k i)
    let g : ℕ → Ω → ℕ → ℝ := fun k ω i =>
      X.X (t k i) ω - X.X (s k i) ω -
        ((t k i : ℝ) - (s k i : ℝ)) * X.c
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
