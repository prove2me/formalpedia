-- Prove2me | Theorems.Thm_DiagLinesLDT_proposition_4_6
-- name    : DiagLinesLDT.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:56:06.801203+00:00
-- url     : https://prove2.me/theorems/38b78c82-ad6a-43e3-a8c2-b7e7ed25fe82
-- title:
--   Proposition 4.6 — point measurements are projective
-- statement:
--   Let $\mathbb F_q$ have odd characteristic. For every $u\in\mathbb F_q^2$, the family $A^u=\{A^u_a\}_{a\in\mathbb F_q}$ is a projective measurement on $\mathcal H$: for all $a,b\in\mathbb F_q$,
--
--   $$(A^u_a)^\dagger=A^u_a,\qquad A^u_aA^u_b=\delta_{a,b}A^u_a,\qquad\sum_{a\in\mathbb F_q}A^u_a=I.$$
--
--   This gives Alice's and, by transposing, Bob's point measurements.
--
--   Differences from the source:
--   - generalization: q an odd prime, ω^t → any finite field of odd characteristic, χ(t), W_χ; reason: at q = p, χ(t) = ω^t and W_χ = W, so this specializes to the printed statement; §7.1 asserts the prime-power form
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Proposition 4.6, p.8 (Proposition 7.1, p.22, for odd prime powers)

import Mathlib
import Definitions.Def_DiagLinesLDT_oddStrategy

namespace DiagLinesLDT

/-- Point measurements are projective.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Proposition 4.6, p.8 (extended to odd prime powers in Proposition 7.1, p.22).

**Formalization Note** Stated for every finite field of odd characteristic; at `q` prime it is the
printed statement. -/
theorem proposition_4_6 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (u : Fin 2 → F) :
    (∀ a, (pointOdd F u a).conjTranspose = pointOdd F u a) ∧
      (∀ a b, pointOdd F u a * pointOdd F u b = if a = b then pointOdd F u a else 0) ∧
      ∑ a, pointOdd F u a = 1 := by sorry

end DiagLinesLDT
