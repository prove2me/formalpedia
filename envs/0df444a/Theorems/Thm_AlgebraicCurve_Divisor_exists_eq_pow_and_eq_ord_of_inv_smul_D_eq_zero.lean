-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero
-- name    : AlgebraicCurve.Divisor.exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/2ded98aa-fa9c-517a-8118-27a17f28f89f
-- title:
--   Injectivity of the dlog recipe in characteristic p
-- statement:
--   Let $K$ be a perfect field of characteristic a prime $p$, and let $F$ be a field that is a $K$-algebra. Let $t \in F$ be such that $F$ is separable over the intermediate field $K(t) =$ `IntermediateField.adjoin K {t}` and such that the image $D_{K/F}(t)$ of $t$ under the universal derivation into the module of Kähler differentials $\Omega_{F/K}$ is non-zero. Let $D$ be a divisor of $F/K$, that is, a finitely supported function from the places of $F/K$ to $\mathbb{Z}$, where a place is a valuation subring of $F$ containing $\operatorname{im}(K \to F)$, distinct from $F$ itself, and a principal ideal ring; for a place $v$ the order $\operatorname{ord}_v(f)$ is minus the logarithm of the value of $f$ under the associated $\mathbb{Z}^{m0}$-valued adic valuation attached to the height-one prime of $v$. Let $f \in F$ be non-zero, and suppose that $p \cdot D(v) = \operatorname{ord}_v(f)$ for every place $v$, and that the logarithmic differential $f^{-1} \cdot D_{K/F}(f)$ vanishes in $\Omega_{F/K}$. Then there exists a non-zero $g \in F$ with $f = g^p$ and $D(v) = \operatorname{ord}_v(g)$ for every place $v$; in particular $D$ is the divisor of $g$.
--
--   This is the injectivity half of Serre's description of the $p$-torsion of the divisor class group in characteristic $p$ via the map sending a class with $pD = \operatorname{div}(f)$ to the logarithmic differential $df/f$: a class in the kernel of that map is already principal. It is used in the construction of the injective homomorphism on torsion given by [`AlgebraicCurve.Pic0.exists_injective_addMonoidHom_torsion_apply_eq_inv_smul_D`](thm.html#AlgebraicCurve.Pic0.exists_injective_addMonoidHom_torsion_apply_eq_inv_smul_D) and in the characterisation [`AlgebraicCurve.inv_smul_D_eq_zero_iff_exists_pow_eq`](thm.html#AlgebraicCurve.inv_smul_D_eq_zero_iff_exists_pow_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Divisor.exists_eq_pow_and_eq_ord_of_inv_smul_D_eq_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F] [PerfectField K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (t : F) (hsepK : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (D : AlgebraicCurve.Divisor K F) (f : F) (hf : f ≠ 0)
    (hD : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) * D v = v.ord f)
    (h0 : f⁻¹ • KaehlerDifferential.D K F f = 0) :
    ∃ g : F, g ≠ 0 ∧ f = g ^ p ∧ ∀ v : AlgebraicCurve.Place K F, D v = v.ord g := by sorry
