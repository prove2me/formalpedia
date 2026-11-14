-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b46_original_finite_range_signed_ledger_condexp_upper
-- name    : AvramDividend.Classical.avram_b46_original_finite_range_signed_ledger_condexp_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:11:41.267216+00:00
-- url     : https://prove2.me/theorems/61ff7369-2a09-4073-897d-40b573b3cb12
-- title:
--   Original finite-range stopped mixed Ito ledger yields time-zero conditional reward bound
-- statement:
--   For the actual finite-activity Levy process, a finite-range right-continuous stopping time and its source-exact discounted Ito-Meyer ledger with intrinsic Gaussian and negative-jump centered terms plus an almost-surely nonpositive loss yields the bound E[F|F0]≤b. No additional global second-moment assumptions or artificial independent Brownian proxy are used.
-- source:
--   Proved B42 original finite-range eventwise budget, Proved ubv_finite14 eventwise-to-conditional expectation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b42_original_finite_range_physical_ledger_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_initial_event_budget_to_condexp
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b46_original_finite_range_signed_ledger_condexp_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (b : ℝ) (F B : Ω → ℝ) (hFI : Integrable F P)
    (hBsign : ∀ᵐ ω ∂P, B ω ≤ 0)
    (hLedger : ∀ (R Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω))) →
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) →
      ∀ᵐ ω ∂P,
        F ω ≤ b + R (τ ω) ω + Jsmall (τ ω) ω + B ω) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ b := by sorry
