-- Prove2me | Theorems.Thm_DetComplexityPowerSum_Quadratic_claim_3_5
-- name    : DetComplexityPowerSum.Quadratic.claim_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:32:13.152173+00:00
-- url     : https://prove2.me/theorems/1707a385-ebbf-4732-bcfd-40ab0ab56190
-- title:
--   Claim 3.5 — a smooth zero has matrix corank one, in particular on $S$
-- statement:
--   Let $M_0,M_1,\dots,M_n$ be arbitrary $m\times m$ complex matrices, put $M(x)=M_0+\sum_{i=1}^n x_iM_i$, and define $F(x)=\det M(x)$. Write $F_n(x)=\sum_{i=1}^n x_i^n$ and let $S$ be its polar slice from Definition 2.2.
--
--   1. Let $a\in\mathbb C^n$ be such that $F(a)=0$ and at least one of the first order partial derivatives of $F$ is non-zero at $a$. Then $\operatorname{rank}M(a)=m-1$.
--   2. If $n\ge2$ and $F=F_n$, then for every $a\in S$, $\operatorname{rank}M(a)=m-1$.
--
--   The second clause says that every point of the polar slice is a corank one point of the pencil, so the kernels used in the proxy system are lines.
--
--   **Formalization Note** In the first clause $F$ is written as the determinant polynomial of the pencil. The second clause carries the source's setting $n\ge 2$, $\det M(x)=F_n$ as hypotheses.
--
--   Differences from the source:
--   - generalization: the first clause is for the representation $\det M=F_n$ → the first clause holds for every pencil, with $F=\det M(x)$; reason: it uses no property of the power sum; the second clause keeps the source's setting
--   - encoding: $\operatorname{rank}M(a)=m-1$ → `rank + 1 = m`; reason: avoids truncated natural subtraction at $m=0$; the same condition for $m\ge 1$
--   - encoding: 1-based coordinates $x_{n-1}$ and $i\le n-2$ → 0-based `Fin n` with `IsPenultimate` (`i + 2 = n`) and `IsEarly` (`i + 2 < n`); reason: the same coordinates under the shift by one
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 6, Claim 3.5

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_DetComplexityPowerSum_Quadratic_KernelNormalizers
open Matrix MvPolynomial OAI.PermanentBorder

namespace DetComplexityPowerSum.Quadratic

theorem claim_3_5 {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) :
    (∀ a : Fin n → ℂ, eval a (affineMatrixPolynomial m M₀ M) = 0 →
      (∃ i : Fin n, eval a (pderiv i (affineMatrixPolynomial m M₀ M)) ≠ 0) →
      (pencil M₀ M a).rank + 1 = m) ∧
    (2 ≤ n → affineMatrixPolynomial m M₀ M = powerSum n →
      ∀ a ∈ polarSlice n, (pencil M₀ M a).rank + 1 = m) := by sorry

end DetComplexityPowerSum.Quadratic
