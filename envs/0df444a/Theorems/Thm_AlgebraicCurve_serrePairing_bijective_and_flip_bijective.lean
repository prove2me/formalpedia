-- Prove2me | Theorems.Thm_AlgebraicCurve_serrePairing_bijective_and_flip_bijective
-- name    : AlgebraicCurve.serrePairing_bijective_and_flip_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/8ace0ab6-0038-5a38-9ee3-f4bae472c253
-- title:
--   Perfectness of the Čech residue pairing on a curve
-- statement:
--   Let $K$ be a perfect field and $F$ a field that is a $K$-algebra, essentially of finite type over $K$, and a curve over $K$ in the sense of `IsCurveOver`: every nonzero $f \in F$ has a divisor of degree $0$ recording its order at each place, every place has residue field finite over $K$, and $\Omega[F/K]$ is free of rank one over $F$. Assume in addition that every nonzero Kähler differential has an associated divisor with value $v.\mathrm{ordDifferential}\,\omega$ at each place $v$ (`HasCanonicalDivisor`), that at every place the element $v.\mathrm{dCoord}$ spans $\Omega[F/K]$ over $F$, and that a canonical local residue datum over $K$ is chosen at every place (`HasCanonicalLocalResidueKStar`). Two further hypotheses are assumed explicitly: `hC`, that the Riemann–Roch space of the zero divisor is exactly the image of $K$ in $F$, and `hRT`, the residue theorem, that for every nonzero $\omega \in \Omega[F/K]$ the Weil functional `weilOfKaehler` attached to $\omega$ annihilates the diagonal adele of every $f \in F$. Finally let $S_0, S_1$ be sets of places with $S_0 \cup S_1$ all places, and with some place outside $S_0$ and some place outside $S_1$. The conclusion is that the $K$-linear map `serrePairing hRT hcover`, sending a regular differential $\omega$ to the functional induced on $\check H^1 = L(S_0 \cap S_1, 0)/\mathrm{range}(\mathrm{cechDiff})$ by $f \mapsto$ the sum of the local residues of $f\omega$ over the places outside $S_0$, is bijective, and so is its flip, the map from $\check H^1$ to the $K$-dual of the space of regular differentials.
--
--   This is Serre duality $\check H^1(\{S_0,S_1\},\mathcal O) \cong H^0(\Omega^1)^\vee$ for a curve over a perfect field, stated as perfectness of the residue pairing in the two-chart Čech model, with the residue theorem taken as a hypothesis. It is the field-theoretic input to the scheme-level duality statement for a two-affine open cover, which in this development serves curves such as reductions of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_serrePairing_bijective_and_flip_bijective.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_SerrePairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem serrePairing_bijective_and_flip_bijective {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁) :
    Function.Bijective (serrePairing hRT hcover) ∧
      Function.Bijective (serrePairing hRT hcover).flip := by sorry
