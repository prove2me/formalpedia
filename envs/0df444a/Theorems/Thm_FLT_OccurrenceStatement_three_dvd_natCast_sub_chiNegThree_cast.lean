-- Prove2me | Theorems.Thm_FLT_OccurrenceStatement_three_dvd_natCast_sub_chiNegThree_cast
-- name    : FLT.OccurrenceStatement.three_dvd_natCast_sub_chiNegThree_cast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/9ed1c100-23d0-56f1-8382-51d62f67ba60
-- title:
--   3 ∣ ℓ - χ₋₃(ℓ) in any commutative ring
-- statement:
--   Let $R$ be any commutative ring and let $\ell$ be a natural number. Write $\chi_{-3}$ for the integer-valued function on $\mathbb{N}$ defined by cases on the residue of the argument modulo $3$: `chiNegThree n` equals $1$ if $n \equiv 1 \pmod 3$, equals $-1$ if $n \equiv 2 \pmod 3$, and equals $0$ otherwise (that is, when $3 \mid n$). The assertion is that the element $3$ of $R$ divides the difference between the image of $\ell$ under the canonical map $\mathbb{N} \to R$ and the image in $R$ of the integer $\chi_{-3}(\ell)$; in symbols, $(3 : R) \mid (\ell : R) - (\chi_{-3}(\ell) : R)$. No hypotheses are placed on $R$ beyond commutativity of its ring structure: in particular $R$ may have characteristic dividing $3$, in which case the statement is vacuous, and $\ell$ is arbitrary, including $\ell \equiv 0 \pmod 3$, where the assertion reduces to $3 \mid \ell$ in $R$.
--
--   This is the elementary congruence $\ell \equiv \chi_{-3}(\ell) \pmod 3$, for the quadratic character of conductor $3$, transported into an arbitrary coefficient ring. It is used in the comparison of Hecke data at a prime $\ell$ with the character values attached to the weight-one Eisenstein series, being cited by [`LanglandsTunnell.liftTraceSeed_b_eq_chiNegThree_of_detDictionaryRow`](thm.html#LanglandsTunnell.liftTraceSeed_b_eq_chiNegThree_of_detDictionaryRow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_OccurrenceStatement_three_dvd_natCast_sub_chiNegThree_cast.lean

import Mathlib
import Definitions.Def_ModularForm_EisensteinChiNegThree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open EisensteinWeightOne

theorem FLT.OccurrenceStatement.three_dvd_natCast_sub_chiNegThree_cast
    (R : Type*) [CommRing R] (ℓ : ℕ) :
    (3 : R) ∣ (ℓ : R) - ((chiNegThree ℓ : ℤ) : R) := by sorry
