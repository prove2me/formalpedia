-- Prove2me | Theorems.Thm_AlgebraicCurve_riemannGenusBounded_of_indexFinite
-- name    : AlgebraicCurve.riemannGenusBounded_of_indexFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/7e3aa6d1-aa9b-58fc-b2d3-ede5cebdb8c1
-- title:
--   Finite index of speciality bounds deg D-ℓ(D)
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume `IsCurveOver K F`: every nonzero $f \in F$ has a divisor $D$ with $D(v) = v.\mathrm{ord}(f)$ at every place and $\deg D = 0$, each residue field $\kappa(v)$ of a place $v$ of $F/K$ is a finite-dimensional $K$-vector space, and the module of Kähler differentials $\Omega_{F/K}$ is free of rank one over $F$. Here a place is a valuation subring of $F$, distinct from $F$ itself, containing the image of $K$ and a principal ideal ring, and a divisor is a finitely supported $\mathbb{Z}$-valued function on the places, with $\deg D = \sum_v D(v)\,[\kappa(v):K]$. Assume further that there is at least one place, and that the Riemann–Roch space of the zero divisor — the $K$-subspace of $f \in F$ with $v(f) \le 1$ for all $v$ — is finite-dimensional over $K$. The hypothesis `IndexOfSpecialtyFinite K F` is that for some divisor $D_0$ the quotient of the adele space $\bigsqcup_D \mathrm{adeleBdd}\,D \subseteq \prod_v F$ by the sum of the preimages of $\mathrm{adeleBdd}\,D_0$ and of `globalSub K F` under the inclusion of the adele space is a finite $K$-module. The conclusion `RiemannGenusBounded K F` asserts the existence of an integer $\gamma$ with $\deg D - \ell(D) \le \gamma$ for every divisor $D$, where $\ell(D)$ is the invariant `ell D` attached to $D$, viewed in $\mathbb{Z}$.
--
--   This is the step in the adelic (Stichtenoth-style) development of Riemann's inequality which converts the finiteness of the index of speciality at a single divisor into a uniform upper bound for $\deg D - \ell(D)$, the bound whose supremum is the genus. It is used in the construction of places with prescribed order behaviour, in [`AlgebraicCurve.exists_place_notMem_ord_neg_and_forall_ord_eq_one`](thm.html#AlgebraicCurve.exists_place_notMem_ord_neg_and_forall_ord_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_riemannGenusBounded_of_indexFinite.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PoleDivisorPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem riemannGenusBounded_of_indexFinite {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [Nonempty (Place K F)]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hfin : IndexOfSpecialtyFinite K F) :
    RiemannGenusBounded K F := by sorry
