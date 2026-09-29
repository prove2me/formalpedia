-- Prove2me | Theorems.Thm_AlgebraicCurve_AlgEquiv_eq_one_of_forall_smul_place_eq
-- name    : AlgebraicCurve.AlgEquiv.eq_one_of_forall_smul_place_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/6992ba9a-27f7-540c-a9b1-315ecc42ba94
-- title:
--   A K-automorphism fixing every place is trivial
-- statement:
--   Let $K$ be an algebraically closed field and let $F$ be a field equipped with a $K$-algebra structure which is essentially of finite type over $K$ and satisfies `IsCurveOver K F`, i.e.: every nonzero $f \in F$ admits a divisor $D$ on the places of $F/K$ with $D(v) = \operatorname{ord}_v(f)$ at every place $v$ and $\deg D = 0$; the residue field of every place is a finite-dimensional $K$-vector space; and the module of Kähler differentials $\Omega[F/K]$ is free of rank one over $F$. Here a place of $F/K$ means a valuation subring of $F$ which contains the image of $K$ under the structure map, is not the whole of $F$, and is a principal ideal ring. The automorphism group $F \simeq_{\mathrm{alg}[K]} F$ acts on the set of places; the assertion is that if a $K$-algebra automorphism $\sigma$ of $F$ satisfies $\sigma \cdot v = v$ for every place $v$ of $F/K$, then $\sigma$ is the identity automorphism.
--
--   This is the classical rigidity statement that a $K$-automorphism of a function field of one variable over an algebraically closed field which fixes every place is trivial; geometrically, an automorphism of a smooth proper curve over an algebraically closed field fixing every closed point is the identity. It is used to prove the corresponding rigidity for semilinear automorphisms, [`AlgebraicCurve.SemilinearAut.eq_of_baseAut_eq_of_forall_smul_place_eq`](thm.html#AlgebraicCurve.SemilinearAut.eq_of_baseAut_eq_of_forall_smul_place_eq) and [`AlgebraicCurve.SemilinearAut.eq_of_forall_smul_place_eq`](thm.html#AlgebraicCurve.SemilinearAut.eq_of_forall_smul_place_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_AlgEquiv_eq_one_of_forall_smul_place_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

universe u v

theorem AlgebraicCurve.AlgEquiv.eq_one_of_forall_smul_place_eq
    {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Algebra.EssFiniteType K F]
    (σ : F ≃ₐ[K] F) (h : ∀ v : Place K F, σ • v = v) : σ = 1 := by sorry
