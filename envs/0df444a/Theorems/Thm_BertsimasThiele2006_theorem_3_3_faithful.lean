-- Prove2me | Theorems.Thm_BertsimasThiele2006_theorem_3_3_faithful
-- name    : BertsimasThiele2006.theorem_3_3_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:00:33.335834+00:00
-- url     : https://prove2.me/theorems/eafa6ef0-8aa9-44d7-a4e6-439356b60ffe
-- title:
--   Theorem 3.3, p. 156 — capacitated orders: the robust policy is the nominal capacitated policy for w'
-- statement:
--   Consider the single-station inventory model of §3.1 over horizon $T$ with nonnegative demand ($0\le\hat w_k\le\bar w_k$), budgets of uncertainty $\Gamma_k$ (nondecreasing, $\Gamma_0\ge0$, $\Gamma_{k+1}\le\Gamma_k+1$), ordering cost $C(u)=K\mathbf 1\{u>0\}+cu$ with $c>0$, $K\ge0$, and holding/shortage cost $R(x)=\max(hx,-px)$ with $h\ge0$, $p>c$, and add the order capacity $u_k\le d$ (24) to the robust formulation (14). Let $A_k$ be the value of the linear program (13), $A_{-1}=0$, $w'_k=\bar w_k+\frac{p-h}{p+h}(A_k-A_{k-1})$, and $N_{w'}(u)$ the nominal cost of the orders $u$ under demand $w'$. Then, for every order sequence $u$,
--
--   $$u \text{ is the order part of an optimal solution of (14)+(24)} \iff u\in\arg\min\{N_{w'}(v):\ 0\le v_k\le d,\ k<T\}.$$
--
--   This is Theorem 3.3 of Bertsimas and Thiele (2006): with capacity on the orders, the optimal robust policy is the optimal nominal capacitated policy for the same modified demand as in the uncapacitated Theorem 3.2.
--
--   **Formalization Note** As in RobustInventory.SingleStation.theorem_3_2, the policy is the order sequence chosen at time 0 for the whole horizon and $A_k$ is the value of (13).
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), doi:10.1287/opre.1050.0238, p. 156, Theorem 3.3 and constraint (24)

import Mathlib
import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust

open Finset RobustInventory.SingleStation

theorem BertsimasThiele2006.theorem_3_3_faithful (M : Model)
    (hdem : ∀ k, M.what k ≤ M.wbar k) (d : ℝ) (u : ℕ → ℝ) :
    (∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ),
      (M.RobustFeasible u y q r ∧ ∀ k < M.T, u k ≤ d) ∧
      ∀ (u' y' q' : ℕ → ℝ) (r' : ℕ → ℕ → ℝ),
        (M.RobustFeasible u' y' q' r' ∧ ∀ k < M.T, u' k ≤ d) →
          M.robustObjective u y ≤ M.robustObjective u' y') ↔
    ((∀ k < M.T, 0 ≤ u k ∧ u k ≤ d) ∧
      ∀ u' : ℕ → ℝ, (∀ k < M.T, 0 ≤ u' k ∧ u' k ≤ d) →
        M.nominalCost M.wmod u ≤ M.nominalCost M.wmod u') := by sorry
