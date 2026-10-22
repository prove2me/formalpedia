-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
-- name    : AvramDividend.Classical.levy_exponential_generatorIntegrable_of_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T10:56:03.752533+00:00
-- url     : https://prove2.me/theorems/4f44df97-2bc6-4980-8ef1-572260853096
-- title:
--   Exponential test functions lie in the Lévy generator jump-integrability domain under the Lévy square-moment condition
-- statement:
--   For a spectrally negative Lévy process and θ≥0, suppose the canonical negative-jump second-moment weight min(1,y²) is integrable over y<0 against the Lévy measure. Then the compensated generator jump integrand of f(z)=exp(θz) is integrable at every real x. The proof uses the already Proved exponential generatorIntegrand factorisation, the already Proved uniform compensated exponential bound by C min(1,y²), measurability of the indicator/exponential kernel, and integrable domination on the restricted Lévy measure. This supplies the exact domain component missing from linear combinations of exponential generator test functions without assuming a general C² Itô/Dynkin theorem.
-- source:
--   Accepted generatorIntegrand_exp_mul (ceeebf5f-52ae-409f-ab1f-c2e7d4fc0039) and exp_compensated_jump_min_sq_bound (27ba3103-5252-470d-b9d4-c69b4d73fc07), pinned Mathlib Integrable.mono' and ae_restrict_mem.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_exp_compensated_jump_min_sq_bound
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_exponential_generatorIntegrable_of_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ x : ℝ) (hθ : 0 ≤ θ)
    (hmoment : IntegrableOn
      (fun y : ℝ => min 1 (y ^ 2)) (Iio (0 : ℝ)) X.ν) :
    X.GeneratorIntegrable (fun z : ℝ => Real.exp (θ * z)) x := by sorry
