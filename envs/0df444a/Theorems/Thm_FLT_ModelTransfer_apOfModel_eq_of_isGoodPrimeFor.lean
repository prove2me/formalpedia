-- Prove2me | Theorems.Thm_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor
-- name    : FLT.ModelTransfer.apOfModel_eq_of_isGoodPrimeFor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/5855b8bd-6425-5f12-b942-7a98ac9ea0b8
-- title:
--   Agreement of a_q for models related by a ℚ-change of variables
-- statement:
--   Let $V$ and $W$ be Weierstrass curves over $\mathbb{Z}$, let $C$ be an admissible change of variables over $\mathbb{Q}$, and let $q$ be a natural number. Assume $q$ is prime, $q \neq 2$ and $q \neq 3$; assume that $C$ carries the base change of $V$ along $\mathbb{Z} \to \mathbb{Q}$ to the base change of $W$, that is, $C \bullet (V \otimes \mathbb{Q}) = W \otimes \mathbb{Q}$; and assume that $q$ is a good prime for both models in the sense that $(q : \mathbb{Z})$ divides neither the discriminant $\Delta(V)$ nor $\Delta(W)$. The conclusion is the equality `W.apOfModel q = V.apOfModel q` of integers, where for an integral Weierstrass curve $X$ the quantity `X.apOfModel q` is the trace of Frobenius of the reduction $X \otimes \mathbb{Z}/q$, namely $\#(\mathbb{Z}/q) + 1$ minus the point count of that reduced curve. Thus the two integral models, which become isomorphic over $\mathbb{Q}$ via $C$, have the same $a_q$ at every prime $q \geq 5$ of good reduction for both.
--
--   This is the statement that the trace of Frobenius at a good prime $q \geq 5$ depends only on the elliptic curve over $\mathbb{Q}$ and not on the chosen integral Weierstrass model. It is used to show that $a_q$ is well defined on integral models of a fixed rational curve ([`FLT.ModelTransfer.apOfModel_eq_of_isIntegralModelOf`](thm.html#FLT.ModelTransfer.apOfModel_eq_of_isIntegralModelOf)), which in turn underlies the comparison of Frobenius traces for the models occurring in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_ModelTransfer_apOfModel_eq_of_isGoodPrimeFor.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve
namespace FLT.ModelTransfer

theorem apOfModel_eq_of_isGoodPrimeFor {V W : WeierstrassCurve ℤ}
    {C : WeierstrassCurve.VariableChange ℚ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    W.apOfModel q = V.apOfModel q := by sorry
