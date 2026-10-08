-- Prove2me | Theorems.Thm_CVPricing_Regret_optPrice_lipschitz
-- name    : CVPricing.Regret.optPrice_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:14:50.95153+00:00
-- url     : https://prove2.me/theorems/89455e45-f896-4f6d-a980-3af63e50adea
-- title:
--   Eq. (18) — |p(a) − p(a⁽⁰⁾)| = O(‖a − a⁽⁰⁾‖) on a neighbourhood V of a⁽⁰⁾
-- statement:
--   There is a neighbourhood $V$ of $a^{(0)}$ in $\mathbb R^2$ and a constant $C > 0$ such that for all $a \in V$
--
--   $$|p(a) - p(a^{(0)})| \le C\, \|a - a^{(0)}\|, \tag{18}$$
--
--   where $p(a)$ is the maximizer of $r(\cdot, a)$ over $[p_l, p_h]$ and $\|\cdot\|$ is the Euclidean norm.
--
--   The optimal price is thus locally Lipschitz in the parameter, so the estimation error of $\hat a_t$ transfers to the pricing error of the certainty equivalent price $p(\hat a_t)$.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 782 (PDF 14), proof of Theorem 1, eq. (18)

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model
import Definitions.Def_CVPricing_Regret_CVP

open KeskinZeevi.SufficientConditions

namespace CVPricing.Regret

/-- Eq. (18) (den Boer–Zwart 2014, proof of Theorem 1, p. 782): there is a neighbourhood `V` of
`a⁽⁰⁾` and a constant `C > 0` such that for all `a ∈ V`,
`|p(a) − p(a⁽⁰⁾)| ≤ C ‖a − a⁽⁰⁾‖` (Euclidean norm), where `p(a)` is the maximizer of `r(·, a)` over
`[pl, ph]`. -/
theorem optPrice_lipschitz (M : Model) :
    ∃ V ∈ nhds M.a0, ∃ C : ℝ, 0 < C ∧ ∀ a ∈ V,
      |optPriceOf M a - pOpt M| ≤ C * euclidNorm (a - M.a0) := by sorry

end CVPricing.Regret
