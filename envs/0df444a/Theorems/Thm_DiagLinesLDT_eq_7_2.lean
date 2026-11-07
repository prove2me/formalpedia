-- Prove2me | Theorems.Thm_DiagLinesLDT_eq_7_2
-- name    : DiagLinesLDT.eq_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:54:39.783318+00:00
-- url     : https://prove2.me/theorems/633d0099-f2ae-4cd4-a581-f85a43f21515
-- title:
--   Eq. (7.2) — Weyl multiplication law and adjoint
-- statement:
--   Let $\mathbb F_q$ be a finite field of odd characteristic. For all $v,v'\in\mathbb F_q^3\oplus\mathbb F_q^3$,
--
--   $$W_\chi(v)W_\chi(v')=\chi\big(\tfrac12\langle v,v'\rangle\big)W_\chi(v+v'),\qquad W_\chi(v)^\dagger=W_\chi(-v).$$
--
--   These two relations are the algebra of the construction in odd characteristic: they make the phase of a product depend only on the symplectic form.
--
--   Differences from the source:
--   - encoding: odd prime power q → finite field F with ringChar F ≠ 2; reason: the same fields
--   - encoding: ½ in the phases → (2 : F)⁻¹; reason: the inverse of 2 in odd characteristic, the only case in which W_χ is used
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), eq. (7.2), p.21 (Lemmas 4.2 and 4.3, p.7, for q prime)

import Mathlib
import Definitions.Def_DiagLinesLDT_labelMap

namespace DiagLinesLDT

/-- Weyl multiplication law and adjoint, eq. (7.2) (for `q` prime: Lemmas 4.2 and 4.3, p.7).

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), eq. (7.2), p.21.

**Formalization Note** Stated for every finite field of odd characteristic, with `½ = (2 : F)⁻¹`. -/
theorem eq_7_2 {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (v v' : PS F) :
    Wop v * Wop v' = chi F ((2 : F)⁻¹ * symp v v') • Wop (v + v') ∧
      (Wop v).conjTranspose = Wop (-v) := by sorry

end DiagLinesLDT
