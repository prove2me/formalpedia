-- Prove2me | Theorems.Thm_AvramDividend_Classical_deriv_eq_zero_of_atomless_cumulative
-- name    : AvramDividend.Classical.deriv_eq_zero_of_atomless_cumulative
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T13:02:52.757526+00:00
-- url     : https://prove2.me/theorems/89f1f433-66f6-446a-8a1f-f60e5b15ebfb
-- title:
--   The derivative of the cumulative of an atomless measure vanishes where the cumulative is continuous
-- statement:
--   Let mu be an atomless measure on the real line and let g be a continuous function on the positive half-line which is the Ici-cumulative of mu there, that is mu.real (Ici x) = g x for every x > 0. Then g has vanishing derivative at every point of the positive half-line. This is the elementary fact that the derivative of a distribution function is its measure in the Lebesgue sense, specialised to an atomless measure: the derivative of the cumulative at a point is the atom of the measure at that point, and an atomless measure has no atoms. The proof uses the Mathlib description of the derivative of a Stieltjes function (StieltjesFunction.ae_hasDerivAt) together with the description of the atom of a Stieltjes measure as the jump of the cumulative (StieltjesFunction.measure_singleton), and the fact that an atomless measure gives zero jump because the cumulative is continuous. The statement is the missing second-derivative step in the C2 regularity of the q-scale function in the Gaussian branch of the mission: the excursion-height measure of the scale function is atomless, so the logarithmic derivative of the Esscher-tilted scale function has zero derivative, which makes the scale function twice continuously differentiable on the positive axis.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, eq. (3.3) and the Lemma 4 discussion: the q-scale function is C2 on the positive axis when the Gaussian coefficient is positive, because the excursion-height measure is atomless.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem deriv_eq_zero_of_atomless_cumulative
    (mu : Measure ℝ) [NullSingletonClass mu]
    (g : ℝ → ℝ)
    (hfin : ∀ x : ℝ, 0 < x → mu (Ici x) ≠ ⊤)
    (hcont : ContinuousOn g (Ioi (0 : ℝ)))
    (hcum : ∀ x : ℝ, 0 < x → mu.real (Ici x) = g x) :
    ∀ x : ℝ, 0 < x → deriv g x = 0 := by sorry

end AvramDividend.Classical
