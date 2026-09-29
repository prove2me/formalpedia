-- Prove2me | Theorems.Thm_FLT_ModelTransfer_apOfModel_eq_of_isIntegralModelOf_odd
-- name    : FLT.ModelTransfer.apOfModel_eq_of_isIntegralModelOf_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/382e0c8a-d212-51a1-9704-db5cbcb007e3
-- title:
--   Model-independence of a_q at a common good odd prime
-- statement:
--   Let $V$ and $W$ be Weierstrass curves with coefficients in $\mathbb{Z}$, let $E$ be a Weierstrass curve over $\mathbb{Q}$, and let $q$ be a natural number. Assume that each of $V$ and $W$ is an integral model of $E$ in the sense that there is a variable change $C$ over $\mathbb{Q}$ with $C \bullet E$ equal to the base change of the curve along $\mathbb{Z} \to \mathbb{Q}$ (one such change for $V$, another for $W$); assume $q$ is prime and $q \neq 2$; and assume that $q$ is a good prime for each of $V$ and $W$ in the sense that $(q : \mathbb{Z})$ divides neither the discriminant $V.\Delta$ nor $W.\Delta$. The conclusion is the equality $W.\mathtt{apOfModel}\ q = V.\mathtt{apOfModel}\ q$ of integers, where for an integral Weierstrass curve $X$ the quantity $X.\mathtt{apOfModel}\ q$ is the trace of Frobenius of the reduction $X \bmod q$, namely $\#\mathbb{Z}/q + 1 - \#(X \bmod q)$, the reduction being the base change of $X$ along $\mathbb{Z} \to \mathbb{Z}/q$ and the second cardinality being its point count. Note that $E$ is only required to be a Weierstrass curve over $\mathbb{Q}$; no nonsingularity is assumed.
--
--   This is the assertion that the trace of Frobenius at a prime of good reduction is an invariant of the curve rather than of the chosen integral Weierstrass model, here in the form covering all odd primes $q$, in particular $q = 3$. It is used by [`FreyPackage.freyCurveApOfModelThreeAgreement`](thm.html#FreyPackage.freyCurveApOfModelThreeAgreement), where a comparison of $a_3$ between two integral models of the Frey curve is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_ModelTransfer_apOfModel_eq_of_isIntegralModelOf_odd.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve
namespace FLT.ModelTransfer

theorem apOfModel_eq_of_isIntegralModelOf_odd {V W : WeierstrassCurve ℤ} {E : WeierstrassCurve ℚ} {q : ℕ}
    (hVE : V.IsIntegralModelOf E) (hWE : W.IsIntegralModelOf E)
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    W.apOfModel q = V.apOfModel q := by sorry
