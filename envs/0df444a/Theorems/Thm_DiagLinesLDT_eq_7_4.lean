-- Prove2me | Theorems.Thm_DiagLinesLDT_eq_7_4
-- name    : DiagLinesLDT.eq_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:56:01.308637+00:00
-- url     : https://prove2.me/theorems/143bf8de-6106-4c84-ab3a-5353444eb66d
-- title:
--   Eq. (7.4) — characteristic-two Weyl relations
-- statement:
--   Let $q=2^r$. For $v=(p,r)$ and $v'=(p',r')$ in $\mathbb F_q^3\oplus\mathbb F_q^3$,
--
--   $$V(v)V(v')=\chi(p'\cdot r)V(v+v'),\qquad V(v)^\dagger=\chi(p\cdot r)V(v).$$
--
--   Unlike the odd case, these are not symmetrized by a half-phase, so the factor $\chi(p'\cdot r)$ survives on isotropic subspaces.
--
--   Differences from the source:
--   - encoding: q = 2^r → finite field F with ringChar F = 2; reason: the same fields
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), eq. (7.4), p.23

import Mathlib
import Definitions.Def_DiagLinesLDT_labelMap

namespace DiagLinesLDT

/-- The relations of the characteristic-two operators `V`, eq. (7.4).

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), eq. (7.4), p.23.

**Formalization Note** "`q = 2^r`" is `ringChar F = 2`. For `v = (p, r)` and `v' = (p', r')`, `p' · r` is
`v'.1 ⬝ᵥ v.2` and `p · r` is `v.1 ⬝ᵥ v.2`. -/
theorem eq_7_4 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F = 2)
    (v v' : PS F) :
    Vop v * Vop v' = chi F (v'.1 ⬝ᵥ v.2) • Vop (v + v') ∧
      (Vop v).conjTranspose = chi F (v.1 ⬝ᵥ v.2) • Vop v := by sorry

end DiagLinesLDT
