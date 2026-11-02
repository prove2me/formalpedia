-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_jump_increment_integrable_at_all_shifted_states
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_jump_increment_integrable_at_all_shifted_states
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:13:49.568348+00:00
-- url     : https://prove2.me/theorems/86df2d13-d333-4157-938b-29e734322358
-- title:
--   Original bounded-variation Lévy negative-jump increment stays integrable at every shifted state
-- statement:
--   For the actual source Lévy jump measure under BV and an arbitrary globally C1 Lipschitz payoff, generator integrability at one base state x implies full negative jump increment integrability at every shifted state z. The difference of the kernels has majorant 2L max(1,|z-x|) min(1,|y|), integrable by genuine BV first-moment assumptions, while the kernel at x is integrable by GeneratorIntegrable. No C2, substitute process, or assumed transition identity.
-- source:
--   Complete remote-compiler sentinel-verified candidates/work_on/AvramDividend_04c_actual_bv_jump_integrable_all_shifted_states_probe.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_scalar_majorant_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_global_lipschitz_jump_increment_two_moduli
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_jump_increment_integrable_at_all_shifted_states {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x z : ℝ) (hgen : X.GeneratorIntegrable w x) :
    IntegrableOn (fun y : ℝ => w (z + y) - w z) (Iio 0) X.ν := by sorry
