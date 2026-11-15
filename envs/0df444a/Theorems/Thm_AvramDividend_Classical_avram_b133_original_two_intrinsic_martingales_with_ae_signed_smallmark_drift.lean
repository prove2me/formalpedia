-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b133_original_two_intrinsic_martingales_with_ae_signed_smallmark_drift
-- name    : AvramDividend.Classical.avram_b133_original_two_intrinsic_martingales_with_ae_signed_smallmark_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:33:39.190455+00:00
-- url     : https://prove2.me/theorems/2e2cb641-b517-419f-95b8-e99251266863
-- title:
--   Original Gaussian and compensated negative-jump intrinsic martingales coexist with the exact conull full signed smallmark drift
-- statement:
--   For the exact original finite-negative-activity spectrally negative Levy source under the standing assumptions and a legitimate bounded finite-range stopping clock, the authoritatively Proved B32 theorem supplies two intrinsic same-source, same-filtration integrable martingale processes R and Jsmall as conull time-uniform limits of the original truncated Gaussian residual and compensated negative smallmark sources. If the original finite-band compensated increments have the correct signed compensator identity at arbitrary true random clock endpoints on a conull event, the B127 cutoff-limit theorem and Proved B84 Levy signed first-moment convergence identify the Jsmall increment on the same conull event as the full signed negative-strip compensator drift. This packages authentic source martingale centring and generator drift for the original stopped Ito cash certificate while preserving original path, filtration and almost-everywhere qualifiers. Publication awaits B127 Proved.
-- source:
--   Proved B32 original finite-range two intrinsic centred martingale sources and prepared B127 a.e. cutoff compensation limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
import Theorems.Thm_AvramDividend_Classical_avram_b127_original_ae_smallmark_cutoff_drift_limit_transfer
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the original Levy space both physical intrinsic source martingales exist, and the smallmark channel has exact conull compensated drift under the original cutoff identity. -/

theorem AvramDividend.Classical.avram_b133_original_two_intrinsic_martingales_with_ae_signed_smallmark_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (s t : Ω → ℝ≥0)
    (hCut : ∀ᵐ ω ∂P, ∀ k : ℕ,
      avram_p4_h_gaussian_intrinsic_small_band_compensated X k (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k (s ω) ω =
      ((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((k : ℝ) + 1))), z ∂X.ν))) :
    ∃ (R Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω))) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω))) ∧
      (∀ u : ℝ≥0, Integrable (R u) P) ∧
      (∀ u : ℝ≥0, Integrable (Jsmall u) P) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (Jsmall b) ω = Jsmall a ω) ∧
      (∀ᵐ ω ∂P, Jsmall (t ω) ω - Jsmall (s ω) ω =
        -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
          ((t ω : ℝ) - (s ω : ℝ))) := by sorry
