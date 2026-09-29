-- Prove2me | Theorems.Thm_ClarkeGradients_MaxFunctions_genDirDeriv_isGreatest
-- name    : ClarkeGradients.MaxFunctions.genDirDeriv_isGreatest
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:42:11.313001+00:00
-- url     : https://prove2.me/theorems/3f17ba67-2369-4247-b3f1-620a055ab082
-- title:
--   Proposition (1.4) — f°(x; ·) is the support function of ∂f(x)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be locally Lipschitz, and let $x,v\in\mathbb R^n$. Then the generalized directional derivative is the maximum of the linear functional $\zeta\mapsto\zeta\cdot v$ over the generalized gradient:
--
--   $$
--   f^\circ(x;v)=\max\{\zeta\cdot v:\ \zeta\in\partial f(x)\}.
--   $$
--
--   That is, $f^\circ(x;\cdot)$ is the support function of $\partial f(x)$. The maximum is attained.
--
--   This duality is the main tool of §1: it converts inequalities on difference quotients into membership in $\partial f(x)$ (Corollary (1.10)), and it gives the formula for $f^\circ$ in Theorem (2.1)(3).
--
--   **Formalization Note** "max" is `IsGreatest` of the image set, which asserts both that $f^\circ(x;v)$ is attained by some $\zeta\in\partial f(x)$ and that it bounds every $\zeta\cdot v$. The §1 standing assumption (locally Lipschitz) is the hypothesis `hf`.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 248, Proposition (1.4)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), Proposition (1.4): for locally Lipschitz `f`,
`f°(x; v) = max {ζ · v : ζ ∈ ∂f(x)}`, i.e. `f°(x; ·)` is the support function of `∂f(x)`. -/
theorem genDirDeriv_isGreatest {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Shared.LipschitzOnBounded f) (x v : EuclideanSpace ℝ (Fin n)) :
    IsGreatest ((fun ζ => inner ℝ ζ v) '' Shared.generalizedGradient f x) (Shared.genDirDeriv f x v) := by sorry

end ClarkeGradients.MaxFunctions
