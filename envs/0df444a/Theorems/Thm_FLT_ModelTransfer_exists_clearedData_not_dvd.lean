-- Prove2me | Theorems.Thm_FLT_ModelTransfer_exists_clearedData_not_dvd
-- name    : FLT.ModelTransfer.exists_clearedData_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/24ef5ca7-8173-50f5-9571-b91737fc25cf
-- title:
--   Denominator-clearing data prime to q at a common good prime
-- statement:
--   Let $V$ and $W$ be Weierstrass curves over $\mathbb{Z}$, let $C$ be a Weierstrass variable change over $\mathbb{Q}$, i.e. a quadruple $(u,r,s,t)$ with $u$ a unit, and let $q$ be a prime natural number with $q \neq 2$ and $q \neq 3$. Assume that $C$ carries the base change of $V$ along $\mathbb{Z} \to \mathbb{Q}$ to the base change of $W$, that is $C \bullet (V \otimes \mathbb{Q}) = W \otimes \mathbb{Q}$, and that $q$ is a good prime for each of $V$ and $W$ in the sense that $(q : \mathbb{Z})$ divides neither the discriminant $\Delta(V)$ nor $\Delta(W)$. The conclusion is that there exists an element $D$ of [`FLT.ModelTransfer.ClearedData C`](def/ModelTransfer_ClearedData.html#L21), i.e. a nonzero natural number $N = D.N$ together with integers $U, U', R, S, T$ satisfying, as rational numbers, $U = N u$, $U' = N u^{-1}$, $R = N r$, $S = N s$ and $T = N t$, such that moreover $q$ does not divide $N$. Thus the five rational coefficients of $C$, together with $u^{-1}$, admit a common denominator prime to $q$.
--
--   This is the localisation step in the comparison of two integral Weierstrass models of the same curve over $\mathbb{Q}$: it says that the change of variables relating them is $q$-integral at every prime $q \geq 5$ of good reduction for both models, so that the relation survives reduction modulo $q$. It is used in the proof that the trace of Frobenius $a_q$ computed from either model agrees, via [`FLT.ModelTransfer.apOfModel_eq_of_isGoodPrimeFor`](thm.html#FLT.ModelTransfer.apOfModel_eq_of_isGoodPrimeFor).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_ModelTransfer_exists_clearedData_not_dvd.lean

import Definitions.Def_ModelTransfer_ClearedData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve
namespace FLT.ModelTransfer

theorem exists_clearedData_not_dvd {V W : WeierstrassCurve ℤ} {C : WeierstrassCurve.VariableChange ℚ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hq3 : q ≠ 3)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    ∃ D : FLT.ModelTransfer.ClearedData C, ¬ q ∣ D.N := by sorry
