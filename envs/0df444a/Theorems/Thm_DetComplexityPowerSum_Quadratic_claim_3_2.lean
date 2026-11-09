-- Prove2me | Theorems.Thm_DetComplexityPowerSum_Quadratic_claim_3_2
-- name    : DetComplexityPowerSum.Quadratic.claim_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:32:02.393628+00:00
-- url     : https://prove2.me/theorems/8c5bbc5f-1355-47d2-a484-f5302e80341a
-- title:
--   Claim 3.2 — at corank one the adjugate is $\lambda vu^T$ with $\lambda\ne 0$
-- statement:
--   Let $M_0,M_1,\dots,M_n$ be arbitrary $m\times m$ complex matrices and put $M(x)=M_0+\sum_{i=1}^n x_iM_i$.
--
--   Let $a\in\mathbb C^n$ with $\operatorname{rank}M(a)=m-1$, and let $u,v\in\mathbb C^m$ be any non-zero vectors with $u^TM(a)=0$ and $M(a)v=0$. Then there is a non-zero constant $\lambda$ such that
--   $$\operatorname{Adj}(M(a))=\lambda\,vu^T.$$
--
--   This identifies the adjugate at a corank one point with the outer product of its kernel vectors, which turns the trace in Jacobi's formula into a bilinear form.
--
--   Differences from the source:
--   - generalization: $M$ is a determinantal representation of the power sum $F$ → $M_0,\dots,M_n$ arbitrary, with $F$ replaced by $\det M(x)$; reason: the claim uses no property of the power sum; taking $\det M=F$ gives the source
--   - encoding: $\operatorname{rank}M(a)=m-1$ → `rank + 1 = m`; reason: avoids truncated natural subtraction at $m=0$; the same condition for $m\ge 1$
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 5, Claim 3.2

import Mathlib
import Definitions.Def_DetComplexityPowerSum_Quadratic_KernelNormalizers
open Matrix

namespace DetComplexityPowerSum.Quadratic

theorem claim_3_2 {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (a : Fin n → ℂ)
    (hrank : (pencil M₀ M a).rank + 1 = m)
    (u v : Fin m → ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hleft : u ᵥ* pencil M₀ M a = 0) (hright : pencil M₀ M a *ᵥ v = 0) :
    ∃ lam : ℂ, lam ≠ 0 ∧ (pencil M₀ M a).adjugate = lam • vecMulVec v u := by sorry

end DetComplexityPowerSum.Quadratic
