-- Prove2me | Theorems.Thm_BregmanPPA_ProxMult_supdiff_formula
-- name    : BregmanPPA.ProxMult.supdiff_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:45.695951+00:00
-- url     : https://prove2.me/theorems/5e69cd7a-9be9-4dc4-81f6-dabc43c0d16b
-- title:
--   Proof of Theorem 8, p. 221 — the supergradients of l in p: ∂̂ₚl(x, p) = {g(x)} − ∂δ⁺(p)
-- statement:
--   For a problem of the form (10), every $x\in C$ and every $p\ge0$, the set of supergradients of the concave function $l(x,\cdot)$ at $p$ is
--
--   $$\hat\partial_p l(x,p)=\{g(x)\}-\partial\delta^+(p)=\{\,g(x)-u:\ u\in\partial\delta^+(p)\,\}.$$
--
--   Coordinatewise, this says $\hat\partial_{p_i}l(x,p)=\{g_i(x)\}$ when $p_i>0$ and $[g_i(x),\infty)$ when $p_i=0$. It is the step of the proof of Theorem 8 that identifies the $p$-update of (12) with the $p$-component of the proximal step on $K$.
--
--   **Formalization Note** The page prints $\{g(x)\}-\delta^+(p)$, using $\delta^+(p)$ for the subdifferential $\partial\delta^+(p)$ of the indicator (the normal cone of $\overline{\Omega^+}$ at $p$), as on p. 222. The statement uses $\partial\delta^+(p)$, built from `IsSubgradient` and the indicator `indicatorPos`.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 221, proof of Theorem 8 (supergradient set of l)

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_ProxMult_Saddle

namespace BregmanPPA.ProxMult

/-- Proof of Theorem 8, p. 221: for `x ∈ C` and `p ≥ 0`, the supergradients of `l(x, ·)` at `p`
are `∂̂ₚ l(x, p) = {g(x)} − ∂δ⁺(p)`. -/
theorem supdiff_formula {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g) :
    ∀ x ∈ C, ∀ p ∈ BregmanPPA.IneqMult.nonnegOrthant m,
      supdiffP C f g x p = {v | ∃ u ∈ BregmanPPA.Convergence.subdiffOp (BregmanPPA.IneqMult.indicatorPos m) p, v = BregmanPPA.IneqMult.gvec g x - u} := by sorry

end BregmanPPA.ProxMult
