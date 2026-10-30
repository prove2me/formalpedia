-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_bv_drawdown_zero_atom
-- name    : AvramDividend.Classical.avram_ws01b_actual_bv_drawdown_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:30:46.057141+00:00
-- url     : https://prove2.me/theorems/3d98f66c-15b2-4d48-945d-9c7cc51da918
-- title:
--   Exact zero-terminal-drawdown mass under the genuine original BV Lévy exponential clock
-- statement:
--   For the actual original spectrally negative Lévy law with Standing and BV, the probability of zero terminal drawdown at an independent exponential observation time Exp(R) is R/(Φ(R)*physical drift). It includes the finite-jump activity case with a genuine positive atom; no zero boundary assumption, source reflection shortcut, or compound-Poisson restriction is imposed.
-- source:
--   Accepted true original-law all-positive-β descending Wiener–Hopf MGF 892680b1, actual random-clock drawdown nonnegativity and measurability, accepted Laplace-transform atom identification b6e59826, and positive physical BV exponent slope fc81170b. Strong exact BV x=0 resolvent boundary input for c2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_wh_ratio_large_frequency
import Theorems.Thm_AvramDividend_Classical_nonnegative_laplace_transform_atom_zero_limit_nat
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
import Theorems.Thm_AvramDividend_Classical_bv_exponent_gap_div_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_actual_bv_drawdown_zero_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hstanding : X.Standing) (hBV : X.BoundedVariation)
    (R φ : ℝ) (hR : 0 < R) (hφ : 0 < φ)
    (hroot : X.ψ φ = R) :
    (∫ z : Ω × ℝ,
      if runningSup X z.2.toNNReal z.1 -
           X.X z.2.toNNReal z.1 = 0 then (1 : ℝ) else 0
      ∂(P.prod (expMeasure R))) =
    R / (φ * X.drift) := by sorry
