-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b127_original_ae_smallmark_cutoff_drift_limit_transfer
-- name    : AvramDividend.Classical.avram_b127_original_ae_smallmark_cutoff_drift_limit_transfer
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:33:22.55042+00:00
-- url     : https://prove2.me/theorems/61fff9ba-5947-4780-9d2b-d01b197fdebb
-- title:
--   Original conull-event small-mark source compensator cutoff drifts converge to the exact full signed physical drift
-- statement:
--   On the original finite-negative-activity spectrally negative Levy source, let Jsmall be an actual same-source compensated small-mark cutoff limit valid simultaneously at every time on a conull event. Suppose the original finite cutoff compensated small-mark increments over two genuine possibly random physical clocks satisfy their exact signed finite-band compensator drift identity on a conull event. Proved B84 establishes signed Levy first-moment convergence from finite negative activity. Intersect the two conull events, take real limits on the same original paths and exact random clock endpoints, and obtain the limiting Jsmall clock increment equals the original full negative-strip compensator signed drift times elapsed time almost everywhere. This corrects stronger all-path hypotheses in older B82/B85 and isolates the genuine remaining hCut source obligation without replacing original process or assuming a global negative second moment.
-- source:
--   Proved B84 original negative moment DCT and Mathlib unique real limits; source HCut finite compensated band equality is explicit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the true original conull event, finite negative-band compensation identities converge to the full signed small-mark physical drift. -/

theorem AvramDividend.Classical.avram_b127_original_ae_smallmark_cutoff_drift_limit_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJlim : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto
        (fun n : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0)
    (hCut : ∀ᵐ ω ∂P, ∀ n : ℕ,
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω =
      ((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))) :
    ∀ᵐ ω ∂P,
      Jsmall (t ω) ω - Jsmall (s ω) ω =
        -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
          ((t ω : ℝ) - (s ω : ℝ)) := by sorry
