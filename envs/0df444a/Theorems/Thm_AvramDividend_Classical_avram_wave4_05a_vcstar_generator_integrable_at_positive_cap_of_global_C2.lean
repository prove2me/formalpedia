-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_vcstar_generator_integrable_at_positive_cap_of_global_C2
-- name    : AvramDividend.Classical.avram_wave4_05a_vcstar_generator_integrable_at_positive_cap_of_global_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:54:22.644187+00:00
-- url     : https://prove2.me/theorems/fbf83acf-1bfd-45ee-8c96-930992cc1901
-- title:
--   Genuine dividend barrier value belongs to the source Levy generator domain at a positive cap under global C2 regularity
-- statement:
--   For an original spectrally negative Levy process with its q-scale W, at any positive finite real barrier a=cstar W, global C2 regularity of the original dividend barrier value vcstar W on (0,infinity) suffices to make the actual compensated Levy generator jump integrand integrable at exactly x=a. The proof uses a uniform quadratic Taylor remainder on sufficiently small negative jumps, the monotone zero-extended value function to bound larger jumps, and the Levy min(1,y^2) moment. Unlike previously proved interior-only theorems, it covers the endpoint itself and assumes neither prior generator integrability nor q-harmonicity.
-- source:
--   Original Avram-Palmowski-Pistorius 2007 source generator; Kuznetsov-Kyprianou-Rivero 2012 Section 3.5 domain caution. Root-frontier parent scaledW_generator_harmonic_at_positive_cstar e15c1757. Remote private exact pinned proof a72bc8af... passed sentinel, and the zero-Gaussian transport via generator_boundary_left_germ_congr_of_sigma_zero was separately probed. Mathematical child proves the previously absent endpoint generator-domain conjunct under the source pure C2 branch, without claiming harmonicity or closing the parent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_05a_vcstar_generator_integrable_at_positive_cap_of_global_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ha : 0 < (cstar W).toReal)
    (hC2 : ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ))) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal := by sorry
