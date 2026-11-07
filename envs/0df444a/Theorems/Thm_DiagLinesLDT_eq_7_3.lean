-- Prove2me | Theorems.Thm_DiagLinesLDT_eq_7_3
-- name    : DiagLinesLDT.eq_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:56:06.817474+00:00
-- url     : https://prove2.me/theorems/81557a70-3f6f-4ceb-8201-9cac4ea81549
-- title:
--   Eq. (7.3) — Weyl trace orthogonality
-- statement:
--   Let $\mathbb F_q$ have odd characteristic. For all $v,v'\in\mathbb F_q^3\oplus\mathbb F_q^3$,
--
--   $$\frac{1}{q^3}\operatorname{Tr}\big(W_\chi(v')^\dagger W_\chi(v)\big)=\delta_{v,v'}.$$
--
--   The Weyl operators are thus orthonormal for the normalized trace inner product, which makes the commutator norms exactly computable.
--
--   Differences from the source:
--   - encoding: odd prime power q → finite field F with ringChar F ≠ 2; reason: the same fields
--   - encoding: ½ in the phases → (2 : F)⁻¹; reason: the inverse of 2 in odd characteristic, the only case in which W_χ is used
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), eq. (7.3), p.22 (Lemma 6.1, p.17, for q prime)

import Mathlib
import Definitions.Def_DiagLinesLDT_labelMap

namespace DiagLinesLDT

/-- Weyl trace orthogonality, eq. (7.3) (for `q` prime: Lemma 6.1, p.17).

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), eq. (7.3), p.22.

**Formalization Note** Stated for every finite field of odd characteristic. -/
theorem eq_7_3 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (v v' : PS F) :
    ((Fintype.card F : ℂ) ^ 3)⁻¹ * ((Wop v').conjTranspose * Wop v).trace =
      if v = v' then 1 else 0 := by sorry

end DiagLinesLDT
