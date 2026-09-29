-- Prove2me | Theorems.Thm_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq
-- name    : FLT.ModelTransfer.card_eq_of_variableChange_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/9f3548d0-c723-56b6-a71e-ff2ac8703100
-- title:
--   Point count is invariant under a variable change
-- statement:
--   Let $K$ be a field (with decidable equality available), let $X$ and $Y$ be Weierstrass curves over $K$, i.e. tuples $(a_1,a_2,a_3,a_4,a_6)$ of coefficients in $K$, and let $E$ be an element of the group $\mathrm{VariableChange}\;K$ of admissible changes of variables over $K$, given by data $(u,r,s,t)$ with $u$ a unit. Assume that the action of $E$ on $X$ yields $Y$, that is $E \bullet X = Y$. The conclusion is the equality of natural numbers $Y.\mathrm{card} = X.\mathrm{card}$, where for a Weierstrass curve $W$ over $K$ the quantity $W.\mathrm{card}$ is defined as `Nat.card` of the type of points of the associated affine Weierstrass curve $W.\mathrm{toAffine}$, i.e. the cardinality (as a natural number, hence $0$ when the type is infinite) of the set consisting of the point at infinity together with the nonsingular affine $K$-points of the Weierstrass equation of $W$. No hypothesis of nonsingularity of $X$ or $Y$ is imposed.
--
--   This is the model-invariance of the number of rational points: curves related by an admissible change of variables have the same point count. It is the base case of the chain showing that the trace of Frobenius attached to a curve does not depend on the chosen integral model, and is used in [`FLT.ModelTransfer.apOfModel_eq_of_isGoodPrimeFor`](thm.html#FLT.ModelTransfer.apOfModel_eq_of_isGoodPrimeFor) and [`FLT.ModelTransfer.apOfModel_eq_of_isIntegralModelOf_odd`](thm.html#FLT.ModelTransfer.apOfModel_eq_of_isIntegralModelOf_odd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_ModelTransfer_card_eq_of_variableChange_smul_eq.lean

import Definitions.Def_FLTPrelim_Modularity
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve
namespace FLT.ModelTransfer

theorem card_eq_of_variableChange_smul_eq {K : Type*} [Field K] [DecidableEq K]
    {X Y : WeierstrassCurve K} {E : WeierstrassCurve.VariableChange K} (h : E • X = Y) :
    Y.card = X.card := by sorry
