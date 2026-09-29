-- Prove2me | Theorems.Thm_FLT_ModelTransfer_exists_clearedData_not_dvd_odd
-- name    : FLT.ModelTransfer.exists_clearedData_not_dvd_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/6ece9efd-fc87-5788-bcf6-58d1c2d1ad2c
-- title:
--   Cleared data prime to an odd good prime q
-- statement:
--   Let $V$ and $W$ be Weierstrass curves over $\mathbb{Z}$, let $C = (u,r,s,t)$ be a Weierstrass variable change over $\mathbb{Q}$, and let $q$ be a prime with $q \neq 2$. Assume that $C$ carries the base change of $V$ along $\mathbb{Z} \to \mathbb{Q}$ to the base change of $W$, i.e. $C \bullet V_{\mathbb{Q}} = W_{\mathbb{Q}}$ as Weierstrass curves over $\mathbb{Q}$, and that $q$ is a good prime for both models in the sense of the predicate `IsGoodPrimeFor`, which asserts exactly that $q \nmid \Delta(V)$ and $q \nmid \Delta(W)$ in $\mathbb{Z}$. The conclusion is that there is an element $D$ of `ClearedData C` with $q \nmid D.N$; that is, there exist a nonzero natural number $N$ with $q \nmid N$ and integers $U, U', R, S, T$ such that, in $\mathbb{Q}$, $U = N u$, $U' = N u^{-1}$, $R = N r$, $S = N s$ and $T = N t$. Equivalently, each of $u$, $u^{-1}$, $r$, $s$, $t$ is $q$-integral, with a single common denominator prime to $q$.
--
--   This is the statement that an isomorphism of Weierstrass models over $\mathbb{Q}$ between two integral models that both have good reduction at an odd prime $q$ is itself integral at $q$, packaged as denominator-clearing data whose denominator is prime to $q$. It is used by [`FLT.ModelTransfer.apOfModel_eq_of_isIntegralModelOf_odd`](thm.html#FLT.ModelTransfer.apOfModel_eq_of_isIntegralModelOf_odd), and thereby serves the model-independence of the local traces of Frobenius at odd good primes; compared with the variant excluding $q = 3$, the prime $3$ is permitted here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_ModelTransfer_exists_clearedData_not_dvd_odd.lean

import Definitions.Def_ModelTransfer_ClearedData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve
namespace FLT.ModelTransfer

theorem exists_clearedData_not_dvd_odd {V W : WeierstrassCurve ℤ} {C : WeierstrassCurve.VariableChange ℚ} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2)
    (hC : C • (V.map (Int.castRingHom ℚ)) = W.map (Int.castRingHom ℚ))
    (hV : V.IsGoodPrimeFor q) (hW : W.IsGoodPrimeFor q) :
    ∃ D : FLT.ModelTransfer.ClearedData C, ¬ q ∣ D.N := by sorry
