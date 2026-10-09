-- Prove2me | Theorems.Thm_ADH2015_o12_logical
-- name    : ADH2015.o12_logical
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-09T09:01:07.086127+00:00
-- url     : https://prove2.me/theorems/7fddf7c7-eb2a-4d6e-af04-162a5aa4657f
-- title:
--   Eqs. (3.9)–(3.10) — $O_{12}=U_{12}^\dagger O U_{12}$ implements the logical operator on qutrits 1 and 2
-- statement:
--   Let $|\tilde\imath\rangle=\tfrac1{\sqrt3}\sum_{a\in\mathbb Z_3}|a,\,a+i,\,a+2i\rangle$ ($i=0,1,2$), i.e. $|\tilde0\rangle=\tfrac1{\sqrt3}(|000\rangle+|111\rangle+|222\rangle)$, $|\tilde1\rangle=\tfrac1{\sqrt3}(|012\rangle+|120\rangle+|201\rangle)$, $|\tilde2\rangle=\tfrac1{\sqrt3}(|021\rangle+|102\rangle+|210\rangle)$ (Eq. (3.3)). For every single-qutrit operator $O$ (matrix elements $O_{ji}$, $O|i\rangle=\sum_jO_{ji}|j\rangle$), the operator $O_{12}=U_{12}^\dagger(O\otimes I)U_{12}$ on the first two qutrits, with $O$ acting on the first qutrit and $U_{12}$ the permutation of Eq. (3.6), satisfies
--   $$(O_{12}\otimes I_3)\,|\tilde\imath\rangle=\sum_jO_{ji}\,|\tilde\jmath\rangle\qquad(i=0,1,2).$$
-- source:
--   A. Almheiri, X. Dong, D. Harlow, Bulk Locality and Quantum Error Correction in AdS/CFT, JHEP 04 (2015) 163, https://arxiv.org/abs/1411.7041v3, Section 3.1, Eqs. (3.7)–(3.10)

import Mathlib
import Definitions.Def_ADH2015_defs

open Matrix
open scoped Kronecker

namespace ADH2015

theorem o12_logical (O : Matrix Qutrit Qutrit ℂ) (i : Qutrit) :
    ((U12ᴴ * (O ⊗ₖ (1 : Matrix Qutrit Qutrit ℂ)) * U12) ⊗ₖ (1 : Matrix Qutrit Qutrit ℂ)) *ᵥ codeKet i =
      ∑ j, O j i • codeKet j := by sorry

end ADH2015
