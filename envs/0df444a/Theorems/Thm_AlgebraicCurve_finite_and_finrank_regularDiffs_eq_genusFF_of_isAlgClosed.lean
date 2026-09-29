-- Prove2me | Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed
-- name    : AlgebraicCurve.finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/1b6e1290-8794-582f-92cd-84d4f5ed1ee8
-- title:
--   dim_K Ω_{reg} = g over an algebraically closed base
-- statement:
--   Let $K$ be an algebraically closed field and let $F$ be a field equipped with a $K$-algebra structure which is essentially of finite type over $K$ and satisfies [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15); the latter asserts that every nonzero $f \in F$ has a divisor, i.e. a finitely supported integer-valued function $D$ on the set of places of $F/K$ (valuation subrings of $F$ containing the image of $K$, different from $F$ itself, and principal ideal rings) with $D(v) = \mathrm{ord}_v(f)$ for all $v$ and $\deg D = 0$, that each residue field $v.\mathrm{ResidueField}$ is a finite-dimensional $K$-module, and that $\Omega_{F/K}$ is free of rank $1$ as an $F$-module. Write $\mathrm{regularDiffs}\,K\,F$ for the $K$-submodule of the module of Kähler differentials $\Omega_{F/K}$ spanned by those $\omega$ with $0 \le v.\mathrm{ordDiff}\,\omega$ at every place $v$. The conclusion is twofold: this submodule is a finite $K$-module, and its $K$-dimension equals $\mathrm{genusFF}\,K\,F$, the $K$-dimension of the first repartition cohomology $H^1$ of the zero divisor.
--
--   This is the equality $\ell(W) = g$ between the dimension of the space of regular (holomorphic) differentials and the adelic genus of the function field, here in the form needed over an algebraically closed base field of arbitrary characteristic. It feeds the genus bounds on torsion in degree-zero divisor classes obtained from the Cartier operator, and through these the results on Tate modules of modular and Drinfeld curves that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed.lean

import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem AlgebraicCurve.finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed
    {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [Algebra.EssFiniteType K F] :
    Module.Finite K ↥(AlgebraicCurve.regularDiffs K F) ∧
      Module.finrank K ↥(AlgebraicCurve.regularDiffs K F) = AlgebraicCurve.genusFF K F := by sorry
