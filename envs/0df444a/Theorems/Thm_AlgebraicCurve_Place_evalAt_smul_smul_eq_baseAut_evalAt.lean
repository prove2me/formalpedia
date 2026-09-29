-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_evalAt_smul_smul_eq_baseAut_evalAt
-- name    : AlgebraicCurve.Place.evalAt_smul_smul_eq_baseAut_evalAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/a07ce1c1-a1fd-5d45-8415-ae355500563f
-- title:
--   Equivariance of evaluation at a place under semilinear automorphisms
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra. A semilinear automorphism is an element $\sigma$ of `SemilinearAut K F`, i.e. a pair $(\tau,\rho)$ consisting of a ring automorphism $\tau$ of $F$ and a ring automorphism $\rho$ of $K$ compatible over the structure map, $\tau(\mathrm{alg}_{K\to F}(a)) = \mathrm{alg}_{K\to F}(\rho(a))$ for all $a\in K$; its base automorphism `SemilinearAut.baseAut` $\sigma$ is the second component $\rho$, and $\sigma$ acts on $F$ through $\tau$ and on places through the induced action on valuation subrings. Let $v$ be a place of $F$ over $K$, that is, a valuation subring of $F$ which contains the image of $K$, is not all of $F$, and is a principal ideal ring. Assume $v$ is rational, meaning the composite $K \to \kappa(v)$ into the residue field of its valuation subring is surjective, and assume likewise that the translated place $\sigma\cdot v$ is rational. Then for every $f\in F$ one has $(\sigma\cdot v).\mathrm{evalAt}(\sigma\cdot f) = \rho\bigl(v.\mathrm{evalAt}(f)\bigr)$, where $\mathrm{evalAt}$ sends an element lying in the valuation subring to a chosen $K$-preimage (via `Function.invFun`) of its residue class, and sends an element outside the valuation subring to $0$.
--
--   This is the standard transport rule for evaluation of functions at rational places under a semilinear automorphism of the function field: translating both the place and the function by $\sigma$ transforms the value by the induced automorphism of the base field. It is used wherever places and residue values must be compared across a base-field automorphism, for instance in the component-chart and Tate-module constructions on semistable models that invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_evalAt_smul_smul_eq_baseAut_evalAt.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.evalAt_smul_smul_eq_baseAut_evalAt
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (σ : SemilinearAut K F) (v : AlgebraicCurve.Place K F)
    (hv : v.IsRational) (hσv : (σ • v).IsRational) (f : F) :
    (σ • v).evalAt (σ • f) = SemilinearAut.baseAut σ (v.evalAt f) := by sorry
