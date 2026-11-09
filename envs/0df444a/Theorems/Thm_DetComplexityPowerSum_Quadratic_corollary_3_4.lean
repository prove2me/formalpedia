-- Prove2me | Theorems.Thm_DetComplexityPowerSum_Quadratic_corollary_3_4
-- name    : DetComplexityPowerSum.Quadratic.corollary_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:32:00.137291+00:00
-- url     : https://prove2.me/theorems/93243478-b834-468a-b602-c666d307f413
-- title:
--   Corollary 3.4 — one non-zero $\lambda$ gives every partial derivative as $\lambda u^TM_iv$
-- statement:
--   Let $M_0,M_1,\dots,M_n$ be arbitrary $m\times m$ complex matrices, put $M(x)=M_0+\sum_{i=1}^n x_iM_i$, and define $F(x)=\det M(x)$.
--
--   Let $a\in\mathbb C^n$ with $\operatorname{rank}M(a)=m-1$, and let $u,v$ be non-zero vectors with $u^TM(a)=0$ and $M(a)v=0$. Then there is a non-zero constant $\lambda$ such that, for every $i\in[n]$,
--   $$\frac{\partial F}{\partial x_i}(a)=\lambda\,u^TM_iv.$$
--
--   The same $\lambda$ serves all $n$ coordinates. At corank one points the partial derivatives therefore behave like a degree $2$ polynomial in the kernel vectors, which is the source of the proxy system. Lemma 2.1 on p. 4 is the same statement.
--
--   Differences from the source:
--   - generalization: $M$ is a determinantal representation of the power sum $F$ → $M_0,\dots,M_n$ arbitrary, with $F$ replaced by $\det M(x)$; reason: the claim uses no property of the power sum; taking $\det M=F$ gives the source
--   - encoding: $\operatorname{rank}M(a)=m-1$ → `rank + 1 = m`; reason: avoids truncated natural subtraction at $m=0$; the same condition for $m\ge 1$
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 6, Corollary 3.4 (also Lemma 2.1, p. 4)

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_DetComplexityPowerSum_Quadratic_KernelNormalizers
open Matrix MvPolynomial OAI.PermanentBorder

namespace DetComplexityPowerSum.Quadratic

theorem corollary_3_4 {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (a : Fin n → ℂ)
    (hrank : (pencil M₀ M a).rank + 1 = m)
    (u v : Fin m → ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hleft : u ᵥ* pencil M₀ M a = 0) (hright : pencil M₀ M a *ᵥ v = 0) :
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ i : Fin n,
      eval a (pderiv i (affineMatrixPolynomial m M₀ M)) = lam * (u ⬝ᵥ (M i *ᵥ v)) := by sorry

end DetComplexityPowerSum.Quadratic
