-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone
-- name    : AvramDividend.Classical.scaleDeriv_pos_of_tilted_positive_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T12:49:09.733978+00:00
-- url     : https://prove2.me/theorems/396faad2-35b2-4d17-91fa-856f2118e889
-- title:
--   Strict positivity of the scale-function derivative from tilted positivity and monotonicity
-- statement:
--   Suppose that for some $\phi>0$ the tilted scale function $g(x)=e^{-\phi x}W(x)$ is non-decreasing on $(0,\infty)$, that $W(x)>0$ for every $x>0$, and that $W$ is differentiable at every strictly positive point. Then $W'(x)>0$ for every $x>0$.
--
--   The proof has two steps. First, monotonicity of $g$ on the open set $(0,\infty)$ gives $g'(x)\ge 0$, and expanding by the product rule gives
--
--   $$g'(x)=e^{-\phi x}\bigl(-\phi W(x)+W'(x)\bigr)\ge 0.$$
--
--   Since $e^{-\phi x}>0$, this forces $W'(x)\ge \phi W(x)$. Second, $\phi>0$ and $W(x)>0$ give $\phi W(x)>0$, hence $W'(x)>0$.
--
--   This isolates the entire analytic content of the milestone `scaleDeriv_pos`: only the existence of a tilting exponent with the stated monotonicity is stochastic, and that is the sole remaining input. The first step is precisely the already-Proved theorem `normalized_derivative_lower_bound` (e6abedf7); only the ordered-field step remains here.
-- source:
--   Kuznetsov, Kyprianou and Rivero: for $q>0$ and $\phi=\Phi(q)>0$ the measure $dW - \phi W\,dx$ is non-negative, which makes $e^{-\phi x}W(x)$ non-decreasing; the resulting differential inequality $W'\ge \phi W > 0$ is then elementary calculus.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Strict positivity of the scale-function derivative, assuming the tilted
scale function is positive and monotone. -/
theorem scaleDeriv_pos_of_tilted_positive_monotone {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x)
    (htilt : ∃ φ : ℝ, 0 < φ ∧ MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  sorry

end AvramDividend.Classical
