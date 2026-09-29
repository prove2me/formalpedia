-- Prove2me | Theorems.Thm_ClarkeGradients_FlowInvariance_genDirDeriv_isGreatest
-- name    : ClarkeGradients.FlowInvariance.genDirDeriv_isGreatest
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:42:42.945107+00:00
-- url     : https://prove2.me/theorems/e5b0f22e-32ed-4899-bae9-d90621fb03da
-- title:
--   Proposition (1.4) — f°(x; ·) is the support function of ∂f(x)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be locally Lipschitz (Lipschitz on every bounded set), and let $x,v\in\mathbb R^n$. Then the generalized directional derivative (1.3) is the largest value of $\zeta\cdot v$ over the generalized gradient (1.1):
--
--   $$
--   f^\circ(x;v)=\max\{\zeta\cdot v:\ \zeta\in\partial f(x)\}.
--   $$
--
--   That is, $f^\circ(x;\cdot)$ is the support function of $\partial f(x)$, and the maximum is attained.
--
--   In this mission the proposition is applied to the distance function $d_F$: it identifies $d_F^\circ(x;v)$ with a maximum over $\partial d_F(x)$, which is how tangency of $v$ is read off from $d_F$.
--
--   **Formalization Note** "max" is encoded as `IsGreatest` of the image of $\partial f(x)$ under $\zeta\mapsto\langle\zeta,v\rangle$, which asserts both that $f^\circ(x;v)$ is an upper bound and that it is attained. The Lipschitz hypothesis is the §1 standing assumption and also guarantees that the real `limsup` in $f^\circ$ is not a junk value. The same statement is a milestone of mission I.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 248, Proposition (1.4)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), Proposition (1.4): for locally Lipschitz `f`,
`f°(x; v) = max {ζ · v : ζ ∈ ∂f(x)}`, i.e. `f°(x; ·)` is the support function of `∂f(x)`. -/
theorem genDirDeriv_isGreatest {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Shared.LipschitzOnBounded f) (x v : EuclideanSpace ℝ (Fin n)) :
    IsGreatest ((fun ζ => inner ℝ ζ v) '' Shared.generalizedGradient f x) (Shared.genDirDeriv f x v) := by sorry

end ClarkeGradients.FlowInvariance
