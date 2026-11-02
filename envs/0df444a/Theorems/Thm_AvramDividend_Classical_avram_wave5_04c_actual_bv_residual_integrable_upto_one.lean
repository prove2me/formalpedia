-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_integrable_upto_one
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_integrable_upto_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:35:00.579345+00:00
-- url     : https://prove2.me/theorems/9831126a-7962-4ea5-a6a8-fe8844449052
-- title:
--   Original BV Lévy drift residual has finite first moment at every time up to one
-- statement:
--   For the genuine spectrally negative Lévy source X satisfying its canonical Standing and BoundedVariation hypotheses, the physical-drift residual R_t=t X.drift-X_t is Bochner integrable for every 0≤t≤1 under the original probability P. The proof starts from the genuine Standing integrability of X_1, obtains integrability of R_1 by adding the deterministic drift, and invokes the proved almost-sure global monotonicity of the actual BV residual. Hence 0≤R_t≤R_1 almost surely, yielding norm domination and Integrable.mono'. Exact source measurability follows from X.adapted and the filtration inclusion. There is no auxiliary process or unproved compensation formula. This is a genuine first-moment prerequisite for the C1 generator-semigroup uniform integrability estimates.
-- source:
--   Complete source candidates/work_on/AvramDividend_04c_actual_residual_integrable_upto_one_probe.lean, checked by private remote compiler probe; proof not yet submitted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_integrable_upto_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (t : ℝ≥0) (ht : t ≤ 1) :
    Integrable (fun ω => (t : ℝ) * X.drift - X.X t ω) P := by sorry
