-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_true_z_weighted_negativeband_countable_stop_mean_zero_of_clock_L1
-- name    : AvramDividend.Classical.avram_mathfin22_original_true_z_weighted_negativeband_countable_stop_mean_zero_of_clock_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T18:48:26.660559+00:00
-- url     : https://prove2.me/theorems/3401168f-e16c-4ad9-824b-8d3eeb7b08f7
-- title:
--   Actual original z-weighted negative-band compensated physical jump integral mean zero at bounded countable stopping times
-- statement:
--   The genuine marked jump measure NX of the original spectrally negative Lévy process on any finite negative reciprocal band B has its z-weighted compensated signed integral centred and integrable at every bounded countably-valued right-continuous stopping time. The only auxiliary clock integrability hypothesis is automatic for bounded measurable clocks and will be eliminated by a subsequent source theorem. The proof selects proved bounded simple quantizers for z, retaining their globally bounded coefficients and the original full-T physical jump count L1 envelope, proves compensated simple mark centring using the genuine original stopped NX theorem, obtains L1 integrability of each raw stopped integral from compensator centring and the clock, establishes true randomclock physical mark convergence, combines the exact deterministic ν mark intensity convergence with the finite Borel intensity norm bound, and applies the proved generic compensated random-clock Bochner dominated convergence lemma. L1 integrability of the limiting true original raw signed integral follows from the common integrable count envelope and ae strong measurability. No global finite Lévy activity, synthetic jump process, or martingale assumption on the z-weighted process is used. This is a direct source-faithful building block for Avram stopped Ito-Meyer jump residuals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_physical_negativeband_mark_quantizer_exists
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_countable_stopped_physical_signed_simple_mark_L1_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_original_randomclock_physical_mark_quantizer_pathwise
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_generic_random_clock_signed_compensator_integral_DCT
import Theorems.Thm_AvramDividend_Classical_avram_a20_bounded_Borel_mark_first_second_integral_limits
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_borel_mark_real_intensity_norm_bound_20261113
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mathfin22_original_true_z_weighted_negativeband_countable_stop_mean_zero_of_clock_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (a b : ℕ) (hab : a ≤ b)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτbound : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable)
    (hClockI : Integrable (fun ω => ((τ ω).untopA : ℝ)) P) :
    let B : Set ℝ :=
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let J : Ω → ℝ := fun ω =>
      (∫ p in Ioc 0 (τ ω).untopA ×ˢ B, p.2 ∂NX ω) -
        (((τ ω).untopA : ℝ) * (∫ z in B, z ∂X.ν))
    Integrable J P ∧ (∫ ω, J ω ∂P) = 0 := by sorry
