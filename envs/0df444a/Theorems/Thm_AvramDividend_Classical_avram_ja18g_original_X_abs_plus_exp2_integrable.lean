-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_X_abs_plus_exp2_integrable
-- name    : AvramDividend.Classical.avram_ja18g_original_X_abs_plus_exp2_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T07:17:17.20211+00:00
-- url     : https://prove2.me/theorems/f40aa6e0-d002-45fe-baaf-99aba4c1e718
-- title:
--   Original Levy X absolute first moment plus two-tilted exponential is integrable
-- statement:
--   On the ORIGINAL probability space, under Standing, the function |X(t)|+exp(2X(t)) is integrable. Reuse Proved original X fixed-time L1 and Proved original compensated exponential integrability for theta=2, and factor out its deterministic Laplace compensation.
-- source:
--   J-A18 integrable envelope component of original Laplace first derivative

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_X_abs_plus_exp2_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    ∀ t : ℝ≥0,
      Integrable (fun ω => |X.X t ω| + Real.exp (2 * X.X t ω)) P := by sorry
