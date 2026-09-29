-- Prove2me | Theorems.Thm_AlgebraicCurve_SemilinearAut_eq_of_forall_smul_place_eq
-- name    : AlgebraicCurve.SemilinearAut.eq_of_forall_smul_place_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/913db3fd-cc01-5d43-955a-579a7d9be4d7
-- title:
--   A ℚ̄-linear automorphism is determined by its action on places
-- statement:
--   Let $F_0$ be a field in the lowest universe equipped with an algebra structure over $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, assumed to be a curve over $\overline{\mathbb Q}$ in the sense of `IsCurveOver` — that is: every nonzero $f \in F_0$ admits a divisor $D$ with $D(v) = \mathrm{ord}_v(f)$ at every place $v$ and $\deg D = 0$; every place has residue field finite as a $\overline{\mathbb Q}$-module; and the module of Kähler differentials $\Omega_{F_0/\overline{\mathbb Q}}$ is free of rank $1$ over $F_0$ — and assumed essentially of finite type over $\overline{\mathbb Q}$. Let $W, W'$ be two semilinear automorphisms, i.e. elements of the subgroup of $\mathrm{Aut}(F_0) \times \mathrm{Aut}(\overline{\mathbb Q})$ (ring automorphisms) consisting of pairs $(p_1, p_2)$ compatible with the structure map, $p_1(a \cdot 1) = p_2(a) \cdot 1$ for all $a \in \overline{\mathbb Q}$. Assume the base components of $W$ and of $W'$, namely their second coordinates `baseAut`, fix every element of $\overline{\mathbb Q}$, and that $W$ and $W'$ act identically on places: $W \bullet P = W' \bullet P$ for every place $P$ of $F_0$ over $\overline{\mathbb Q}$, a place being a valuation subring of $F_0$ containing the image of $\overline{\mathbb Q}$, distinct from $F_0$ itself, and a principal ideal ring. Then $W = W'$.
--
--   This is the rigidity statement that a $\overline{\mathbb Q}$-linear automorphism of a one-variable function field over $\overline{\mathbb Q}$ is determined by the induced permutation of the places of the field, phrased for semilinear automorphisms with trivial base component. It is used in the Čerednik–Drinfel'd part of the development, where abstractly defined involutions of a curve are identified with the ones coming from the moduli description once they are known to agree on places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemilinearAut_eq_of_forall_smul_place_eq.lean

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.SemilinearAut.eq_of_forall_smul_place_eq
    (F₀ : Type) [Field F₀] [Algebra (AlgebraicClosure ℚ) F₀] [IsCurveOver (AlgebraicClosure ℚ) F₀]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F₀]
    (W W' : SemilinearAut (AlgebraicClosure ℚ) F₀)
    (hW : ∀ a : AlgebraicClosure ℚ, SemilinearAut.baseAut W a = a)
    (hW' : ∀ a : AlgebraicClosure ℚ, SemilinearAut.baseAut W' a = a)
    (h : ∀ P : Place (AlgebraicClosure ℚ) F₀, W • P = W' • P) :
    W = W' := by sorry
