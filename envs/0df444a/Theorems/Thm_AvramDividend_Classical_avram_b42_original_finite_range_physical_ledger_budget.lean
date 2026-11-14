-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b42_original_finite_range_physical_ledger_budget
-- name    : AvramDividend.Classical.avram_b42_original_finite_range_physical_ledger_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:55:07.809375+00:00
-- url     : https://prove2.me/theorems/b1ee67cf-a6a4-45cb-a330-2149728ff7df
-- title:
--   Original finite-range physical mixed stopped Ito source ledger yields initial-event budget
-- statement:
--   At a genuine original finite-activity Levy finite-range stopping time, a signed stopped Ito-Meyer ledger upper bounding the true reward by its initial candidate, the intrinsic Gaussian and compensated jump channels and nonpositive residual implies the correct initial-event expectation budget.
-- source:
--   B40 true stopped mixed source, finite-range original Ito-Meyer verification ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b40_original_finite_range_intrinsic_centered_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b42_original_finite_range_physical_ledger_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (b : ℝ) (F B : Ω → ℝ) (hFI : Integrable F P)
    (hBsign : ∀ᵐ ω ∂(P.restrict A), B ω ≤ 0)
    (hLedger : ∀ (R Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) →
      ∀ᵐ ω ∂(P.restrict A),
        F ω ≤ b + R (τ ω) ω + Jsmall (τ ω) ω + B ω) :
    (∫ ω in A, F ω ∂P) ≤ b * (P A).toReal := by sorry
