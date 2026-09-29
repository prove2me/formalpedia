-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_residueField_eq_compositum_of_isConstantFieldExtension
-- name    : AlgebraicCurve.Place.residueField_eq_compositum_of_isConstantFieldExtension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/80d88159-d852-5293-b8fb-7406b33fc432
-- title:
--   Residue field of a place in a separable constant field extension
-- statement:
--   Let $K$, $K'$, $F$, $F'$ be fields forming a commuting square: $K'$ and $F$ are $K$-algebras, $F'$ is an algebra over both $K'$ and $F$, and the two resulting $K$-algebra structures on $F'$ agree with the one coming from $K$ (two scalar-tower hypotheses). Assume $K'/K$ is algebraic and separable, $F'/F$ is integral, and that $F'$ is generated as an $F$-algebra by the image of $K'$, i.e. the $F$-subalgebra $\mathrm{adjoin}_F(\mathrm{range}(K'\to F'))$ of $F'$ is the whole of $F'$; thus $F'$ is the constant field extension $FK'$. Let $W$ be a place of $F'$ over $K'$, that is, a valuation subring of $F'$ which contains the image of $K'$, is not all of $F'$, and is a principal ideal ring. Writing $W$ as a place over $K$ instead (the same valuation subring, `forgetConstants`) and restricting it to $F$ — the valuation subring $W\cap F$, a place $v$ of $F$ over $K$ — one gets an induced homomorphism of residue fields $\kappa(v)\to\kappa(W)$ (`restrictResidueMap`, functoriality of the residue field for the inclusion of valuation subrings). The assertion is that the intermediate field of $\kappa(W)$ generated over $K'$ by the image of this map is all of $\kappa(W)$: $\kappa(W)=K'\cdot\kappa(v)$.
--
--   This is the residue-field part of the classical theory of constant field extensions of function fields: in a separable algebraic constant extension the residue field at a place upstairs is the compositum of the new constants with the residue field of the place below. It is used in the proof of the invariance of degrees under constant extension ([`AlgebraicCurve.Place.sum_deg_fiberConstants_eq_deg_of_isCurveOver`](thm.html#AlgebraicCurve.Place.sum_deg_fiberConstants_eq_deg_of_isCurveOver)) and in a degree computation for places on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_residueField_eq_compositum_of_isConstantFieldExtension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.residueField_eq_compositum_of_isConstantFieldExtension
    {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
    [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
    [Algebra K F] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsAlgebraic K K'] [Algebra.IsSeparable K K'] [Algebra.IsIntegral F F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap K' F')) = ⊤)
    (W : Place K' F') :
    IntermediateField.adjoin K' (E := W.ResidueField)
        (Set.range ((W.forgetConstants (K := K)).restrictResidueMap (F := F))) = ⊤ := by sorry
