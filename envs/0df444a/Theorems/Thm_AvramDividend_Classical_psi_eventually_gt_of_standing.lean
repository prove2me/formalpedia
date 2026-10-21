-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
-- name    : AvramDividend.Classical.psi_eventually_gt_of_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T15:14:33.819816+00:00
-- url     : https://prove2.me/theorems/1c25d564-09f2-49a4-973c-92bd7d9e67ee
-- title:
--   The Laplace exponent of a spectrally negative Levy process eventually exceeds every fixed level under the standing assumptions
-- statement:
--   Let X be a spectrally negative Levy process satisfying the standing assumptions of the paper, let q > 0, and let psi be the Laplace exponent of X. Then there is a beta_0 >= 0 such that q < psi(theta) for every theta >= beta_0. This is the general parameter bridge of the analytic core of Lemma 4 of Avram: the admissible parameters of the scale-function Laplace identity must contain a whole half-line, and the uniqueness theorem for the Laplace transform of the generator residual consumes such a half-line. The proof splits into the three cases of the standing Condition (3.3): the Gaussian case sigma > 0, the case of an infinite first moment of the small jumps, and the remaining case of an absolutely continuous Levy measure, in which the infinitesimal drift is positive and the compensated small-jump integral forces the Laplace exponent to infinity.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the admissible parameters of the scale-function Laplace identity contain a whole half-line, which supplies the hypothesis of the uniqueness step.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem psi_eventually_gt_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) :
    ∃ β₀ : ℝ, 0 ≤ β₀ ∧ ∀ θ : ℝ, β₀ ≤ θ → q < X.ψ θ := by sorry

end AvramDividend.Classical
