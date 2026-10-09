-- Prove2me | Theorems.Thm_ADH2015_u12_recovers
-- name    : ADH2015.u12_recovers
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-09T09:00:37.156584+00:00
-- url     : https://prove2.me/theorems/5d5058aa-d22e-44fc-9e57-c6714008d5ae
-- title:
--   Eqs. (3.4)–(3.6) — the permutation $U_{12}$ recovers the state from qutrits 1 and 2
-- statement:
--   Let $|\tilde\imath\rangle=\tfrac1{\sqrt3}\sum_{a\in\mathbb Z_3}|a,\,a+i,\,a+2i\rangle$ ($i=0,1,2$), i.e. $|\tilde0\rangle=\tfrac1{\sqrt3}(|000\rangle+|111\rangle+|222\rangle)$, $|\tilde1\rangle=\tfrac1{\sqrt3}(|012\rangle+|120\rangle+|201\rangle)$, $|\tilde2\rangle=\tfrac1{\sqrt3}(|021\rangle+|102\rangle+|210\rangle)$ (Eq. (3.3)). Let $U_{12}$ be the permutation of two-qutrit basis states of Eq. (3.6):
--   $$|00\rangle\!\to\!|00\rangle,\ |11\rangle\!\to\!|01\rangle,\ |22\rangle\!\to\!|02\rangle,\ |01\rangle\!\to\!|12\rangle,\ |12\rangle\!\to\!|10\rangle,\ |20\rangle\!\to\!|11\rangle,\ |02\rangle\!\to\!|21\rangle,\ |10\rangle\!\to\!|22\rangle,\ |21\rangle\!\to\!|20\rangle .$$
--   Then $U_{12}$ is unitary, and acting on the first two qutrits it recovers the encoded state (Eq. (3.4)):
--   $$(U_{12}\otimes I_3)\,|\tilde\imath\rangle=|i\rangle\otimes\tfrac1{\sqrt3}\big(|00\rangle+|11\rangle+|22\rangle\big)\qquad(i=0,1,2).$$
-- source:
--   A. Almheiri, X. Dong, D. Harlow, Bulk Locality and Quantum Error Correction in AdS/CFT, JHEP 04 (2015) 163, https://arxiv.org/abs/1411.7041v3, Section 3.1, Eqs. (3.4)–(3.6)

import Mathlib
import Definitions.Def_ADH2015_defs

open Matrix
open scoped Kronecker

namespace ADH2015

theorem u12_recovers :
    U12ᴴ * U12 = 1 ∧
    ∀ i : Qutrit, (U12 ⊗ₖ (1 : Matrix Qutrit Qutrit ℂ)) *ᵥ codeKet i =
      fun x => if x.1.1 = i ∧ x.1.2 = x.2 then ((1 / Real.sqrt 3 : ℝ) : ℂ) else 0 := by sorry

end ADH2015
