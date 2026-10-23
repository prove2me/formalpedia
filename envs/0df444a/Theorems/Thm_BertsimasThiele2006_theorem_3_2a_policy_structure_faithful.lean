-- Prove2me | Theorems.Thm_BertsimasThiele2006_theorem_3_2a_policy_structure_faithful
-- name    : BertsimasThiele2006.theorem_3_2a_policy_structure_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:00:31.273136+00:00
-- url     : https://prove2.me/theorems/77b17531-8c5d-496a-b0af-7259f201bd39
-- title:
--   Theorem 3.2(a), last clause: the optimal robust policy is (s,S), and (S,S) without fixed cost
-- statement:
--   Consider the single-station inventory model of §3.1 over horizon $T$: initial stock $x_0$, nominal demands $\bar w_k$, deviations $\hat w_k\ge 0$, budgets of uncertainty $\Gamma_k$ (nondecreasing, $\Gamma_0\ge0$, $\Gamma_{k+1}\le\Gamma_k+1$), ordering cost $C(u)=K\mathbf 1\{u>0\}+cu$ with $c>0$, $K\ge0$, and holding/shortage cost $R(x)=\max(hx,-px)$ with $h\ge0$, $p>c$. Let $A_k$ be the value of the linear program (13), $A_{-1}=0$, and $w'_k=\bar w_k+\frac{p-h}{p+h}(A_k-A_{k-1})$ the modified demand. For an order sequence $u$ write $x'_k=x_0+\sum_{i<k}(u_i-w'_i)$ for the modified stock.
--
--   Then there exist an optimal solution $(u,y,q,r)$ of the robust formulation (14) and thresholds $s_k\le S_k$ ($k<T$) such that
--
--   $$u_k=\begin{cases}S_k-x'_k,& x'_k<s_k,\\ 0,& x'_k\ge s_k,\end{cases}\qquad k<T,$$
--
--   and $s_k=S_k$ for all $k<T$ when $K=0$. That is, the optimal robust policy is $(s,S)$ in the sense of Definition 3.1, and $(S,S)$ without fixed cost.
--
--   This is the last clause of Theorem 3.2(a) of Bertsimas and Thiele (2006) ("In particular, it is (S, S) if there is no fixed cost and (s, S) if there is a fixed cost"), read for the policy chosen at time 0 for the whole horizon. The existing theorem RobustInventory.SingleStation.theorem_3_2 proves the rest of (a) and (d), and the $K=0$ case with prescribed thresholds $S_k=w'_k$ only under $w'\ge0$; this statement prescribes no thresholds and needs no sign condition.
--
--   **Formalization Note** The thresholds are evaluated along the deterministic modified stock $x'_k$, which is where the robust problem reduces to the nominal one. The model does not assume nonnegative demand ($\hat w_k\le\bar w_k$), so the statement covers slightly more instances than the paper.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), doi:10.1287/opre.1050.0238, p. 155, Theorem 3.2(a), last sentence ('In particular, it is (S, S) if there is no fixed cost and (s, S) if there is a fixed cost'), with Definition 3.1, p. 154

import Mathlib
import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust

open Finset RobustInventory.SingleStation

theorem BertsimasThiele2006.theorem_3_2a_policy_structure_faithful (M : Model) :
    ∃ (s S u y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.IsRobustOptimal u y q r ∧
      (M.K = 0 → ∀ k < M.T, s k = S k) ∧
      ∀ k < M.T, s k ≤ S k ∧
        u k = if M.x0 + ∑ i ∈ range k, (u i - M.wmod i) < s k
          then S k - (M.x0 + ∑ i ∈ range k, (u i - M.wmod i)) else 0 := by sorry
