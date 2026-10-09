-- Prove2me | Theorems.Thm_ADH2015_qutrit_marginals_maximallyMixed
-- name    : ADH2015.qutrit_marginals_maximallyMixed
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-09T08:59:59.494892+00:00
-- url     : https://prove2.me/theorems/258dbf26-2e96-48ae-9c08-767354bfa982
-- title:
--   Eq. (3.3) — every single qutrit of an encoded state is maximally mixed
-- statement:
--   Let $|\tilde\imath\rangle=\tfrac1{\sqrt3}\sum_{a\in\mathbb Z_3}|a,\,a+i,\,a+2i\rangle$ ($i=0,1,2$), i.e. $|\tilde0\rangle=\tfrac1{\sqrt3}(|000\rangle+|111\rangle+|222\rangle)$, $|\tilde1\rangle=\tfrac1{\sqrt3}(|012\rangle+|120\rangle+|201\rangle)$, $|\tilde2\rangle=\tfrac1{\sqrt3}(|021\rangle+|102\rangle+|210\rangle)$ (Eq. (3.3)). For every $a\in\mathbb C^3$ with $\sum_i|a_i|^2=1$, the encoded state $|\tilde\psi\rangle=\sum_i a_i|\tilde\imath\rangle$ has reduced density matrix $\tfrac13\mathbb 1$ on each of the three qutrits.
-- source:
--   A. Almheiri, X. Dong, D. Harlow, Bulk Locality and Quantum Error Correction in AdS/CFT, JHEP 04 (2015) 163, https://arxiv.org/abs/1411.7041v3, Section 3.1, Eqs. (3.1)–(3.3) and the sentence 'for any state the reduced density matrix on any one of the qutrits is maximally mixed'

import Mathlib
import Definitions.Def_ADH2015_defs

open Matrix
open scoped Kronecker

namespace ADH2015

theorem qutrit_marginals_maximallyMixed (a : Qutrit → ℂ) (ha : ∑ i, Complex.normSq (a i) = 1)
    (k : Fin 3) : reducedQutrit (encode a) k = (1 / 3 : ℂ) • 1 := by sorry

end ADH2015
