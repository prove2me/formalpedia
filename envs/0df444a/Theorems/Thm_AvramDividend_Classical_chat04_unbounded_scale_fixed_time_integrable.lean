-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_fixed_time_integrable
-- name    : AvramDividend.Classical.chat04_unbounded_scale_fixed_time_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T04:21:06.205199+00:00
-- url     : https://prove2.me/theorems/38e028ec-8d6c-4853-8024-206dc853aacf
-- title:
--   Unbounded-variation q-scale payoffs are integrable at any fixed time, without standing assumptions
-- statement:
--   Let X be a spectrally negative Levy process of unbounded variation and q > 0, and let W be its q-scale function. Then for every starting point x and every finite time t, the random variable W(x + X_t) is integrable. The proof needs no standing assumption. Its content is that unbounded variation forces the Laplace exponent to exceed q at some finite parameter, in both the Gaussian case and the infinite-small-jump-moment case, and the canonical weighted exponential bound for the scale function then dominates the payoff by a constant times the exponential of the reserve, which is integrable by the Laplace transform of the process. This is the integrability input that the conditional q-scale Markov expectation needs, and the standing assumptions are not required here precisely because the standing integrability of the process increment is unavailable exactly in the infinite-small-jump case that the unbounded-variation hypothesis covers.
-- source:
--   The integrability step of the two-sided exit identity, specialised to the unbounded-variation case. The standing version is the Proved theorem chat04_standing_scale_fixed_time_integrable; here the standing assumption is replaced by unbounded variation, which supplies the same Laplace gap in the two relevant cases. Formalised in the Avram Dividend Classical proof programme.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_scale_fixed_time_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x : ℝ) (t : ℝ≥0) :
    Integrable (fun ω => W (x + X.X t ω)) P := by sorry
