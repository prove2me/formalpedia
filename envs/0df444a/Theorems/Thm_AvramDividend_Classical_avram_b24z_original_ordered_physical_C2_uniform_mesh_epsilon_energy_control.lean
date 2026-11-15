-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24z_original_ordered_physical_C2_uniform_mesh_epsilon_energy_control
-- name    : AvramDividend.Classical.avram_b24z_original_ordered_physical_C2_uniform_mesh_epsilon_energy_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:35:22.512504+00:00
-- url     : https://prove2.me/theorems/2ac8f2b4-fc78-496a-95b3-f2b74af68b31
-- title:
--   Original ordered physical compact preleft C2 epsilon Taylor energy bound
-- statement:
--   For any actual original ordered physical mesh and arbitrary compact spatial interior band, the finite C2 second-order remainder has the original true L1 epsilon quadratic energy absorption bound. The order of endpoints is exactly the extra condition required to identify the subtracted NNReal time length with its real difference.
-- source:
--   A source-faithful specialization of Proved avram_b24_original_preleft_C2_compact_taylor_L1_automatic, rewriting NNReal.coe_sub using explicit ordered physical endpoints.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_preleft_C2_compact_taylor_L1_automatic
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b24z_original_ordered_physical_C2_uniform_mesh_epsilon_energy_control
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (A : Set Ω) (S : ℕ → Finset ℕ) (s t : ℕ → ℕ → ℝ≥0)
    (hOrdered : ∀ k i, s k i ≤ t k i) :
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
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k, K ≤ k →
      (∫ ω in A, |R k ω| ∂P) ≤
        ε * (∫ ω in A, Q k ω ∂P)  := by sorry
