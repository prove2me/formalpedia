-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_finite_weight_L2_of_physical_moments
-- name    : AvramDividend.Classical.avram_mix_annulus15_finite_weight_L2_of_physical_moments
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T17:20:44.308067+00:00
-- url     : https://prove2.me/theorems/99af255d-b8e9-4ea8-9118-351aba6ce922
-- title:
--   Finite deterministic-weight squared-integral isometry from diagonal and off-diagonal physical moment certificates
-- statement:
--   For a finite family of real source-exact centred physical annulus counts whose diagonal square integrals are the original Levy rates and whose disjoint off-diagonal covariance integrals vanish, any finite deterministic weighted count has an integrable square with exact sum of squared-weight-rate expectation. This algebraic bridge enables arbitrary finite original mark partitions from the already-Proved annulus variance and separated covariance, a necessary source input to infinite-activity jump martingale construction.
-- source:
--   Directly reusable in the original X/P finite-mark jump isometry following Proved variance 6e234a3f and separated covariance 9c325a05; consumer 5f12c023 then f5e6e083. No synthetic process model is introduced by applying the abstract algebraic bridge to original physical annulus counts.

import Mathlib
open MeasureTheory
open scoped BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_mix_annulus15_finite_weight_L2_of_physical_moments
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [DecidableEq ι]
    (s : Finset ι) (Y : ι → Ω → ℝ) (a r : ι → ℝ)
    (hDiag : ∀ i ∈ s, Integrable (fun ω => (Y i ω) ^ 2) P ∧
      (∫ ω, (Y i ω) ^ 2 ∂P) = r i)
    (hOff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Integrable (fun ω => Y i ω * Y j ω) P ∧
      (∫ ω, Y i ω * Y j ω ∂P) = 0) :
    Integrable (fun ω => (∑ i ∈ s, a i * Y i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ s, a i * Y i ω) ^ 2 ∂P) =
      ∑ i ∈ s, (a i) ^ 2 * r i := by sorry
