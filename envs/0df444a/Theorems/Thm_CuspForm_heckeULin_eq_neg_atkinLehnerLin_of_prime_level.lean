-- Prove2me | Theorems.Thm_CuspForm_heckeULin_eq_neg_atkinLehnerLin_of_prime_level
-- name    : CuspForm.heckeULin_eq_neg_atkinLehnerLin_of_prime_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/4bcbdf97-a9ea-5a4f-8252-7dd7ee7d5b75
-- title:
--   At prime level ℓ: U_ℓ = -w_ℓ on S₂(Γ₀(ℓ))
-- statement:
--   Let $\ell$ be a nonzero natural number which is prime, and let $A$ be an Atkin–Lehner datum for the pair $(\ell,\ell)$, that is: a natural number $A.R$ together with a factorisation $\ell = \ell \cdot A.R$ and integers $A.a$, $A.b$ satisfying the Bézout relation $\ell\, A.a - A.R\, A.b = 1$. Let $f$ be a cusp form of weight $2$ for $\mathrm{Gamma0}\,\ell$. The assertion is the equality, in the space of weight-$2$ cusp forms for $\mathrm{Gamma0}\,\ell$, of $\mathrm{heckeULin}\,2\,(\mathrm{dvd\_refl}\ \ell)$ applied to $f$ with the negative of $\mathrm{atkinLehnerLin}\,A\,2$ applied to $f$. Here the first operator is the $\mathbb{C}$-linear endomorphism induced, for the divisibility $\ell \mid \ell$, by the function-level operator $\mathrm{heckeU}\,2\,\ell\,g = \sum_{j<\ell} g \mid[2]\ \mathrm{heckeMatrix}\ \ell\ j$, and the second is the $\mathbb{C}$-linear endomorphism induced by $g \mapsto g \mid[2]\ A.\mathrm{alGL}$, the weight-$2$ slash action of the matrix attached to the datum $A$. Thus $U_\ell f = -w_\ell f$ on $S_2(\Gamma_0(\ell))$, for the involution $w_\ell$ determined by any such datum.
--
--   This is the classical relation of Atkin and Lehner identifying, at prime level, the operator $U_\ell$ with the negative of the Atkin–Lehner involution $w_\ell$ on weight-$2$ cusp forms, reflecting that at prime level every cusp form is $\ell$-new. It is used in the study of the Hecke algebra acting on $S_2(\Gamma_0(\ell))$, in particular by [`CuspForm.isReduced_heckeLatticeAlgebra`](thm.html#CuspForm.isReduced_heckeLatticeAlgebra).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeULin_eq_neg_atkinLehnerLin_of_prime_level.lean

import Mathlib
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.heckeULin_eq_neg_atkinLehnerLin_of_prime_level {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime)
    (A : ModularForm.AtkinLehnerDatum ℓ ℓ) (f : CuspForm (CongruenceSubgroup.Gamma0 ℓ) 2) :
    CuspForm.heckeULin 2 (dvd_refl ℓ) f = -CuspForm.atkinLehnerLin A 2 f := by sorry
