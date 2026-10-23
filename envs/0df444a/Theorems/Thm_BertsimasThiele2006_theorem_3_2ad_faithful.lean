-- Prove2me | Theorems.Thm_BertsimasThiele2006_theorem_3_2ad_faithful
-- name    : BertsimasThiele2006.theorem_3_2ad_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:00:28.953867+00:00
-- url     : https://prove2.me/theorems/23bffce4-039d-4a55-b4fe-48c4719776e6
-- title:
--   Theorem 3.2(a), (d), as stated in the paper (nonnegative demand, optimal policies and costs only)
-- statement:
--   Consider the single-station inventory model of §3.1 over horizon $T$: initial stock $x_0$, nominal demands $\bar w_k$ and deviations $\hat w_k$ with $0\le\hat w_k\le\bar w_k$ (nonnegative demand), budgets of uncertainty $\Gamma_k$ (nondecreasing, $\Gamma_0\ge0$, $\Gamma_{k+1}\le\Gamma_k+1$), ordering cost $C(u)=K\mathbf 1\{u>0\}+cu$ with $c>0$, $K\ge0$, and holding/shortage cost $R(x)=\max(hx,-px)$ with $h\ge0$, $p>c$. Let $A_k$ be the value of the linear program (13), $A_{-1}=0$, $w'_k=\bar w_k+\frac{p-h}{p+h}(A_k-A_{k-1})$, and let $N_{w'}(u)=\sum_{k<T}\big(C(u_k)+R(x_0+\sum_{i\le k}(u_i-w'_i))\big)$ be the nominal cost under demand $w'$. Then:
--
--   1. (a) an order sequence $u$ is the order part of an optimal solution $(u,y,q,r)$ of the robust formulation (14) if and only if $u$ minimizes $N_{w'}$ over $u\ge0$;
--   2. (d) for any optimal $(u,y,q,r)$ of (14) and any minimizer $u'$ of $N_{w'}$,
--   $$\sum_{k<T}\big(C(u_k)+y_k\big)=N_{w'}(u')+\frac{2ph}{p+h}\sum_{k=0}^{T-1}A_k.$$
--
--   This is Theorem 3.2(a) (without its last, policy-structure sentence) and (d) of Bertsimas and Thiele (2006), under the paper's assumption of nonnegative demand. The existing theorem RobustInventory.SingleStation.theorem_3_2 proves both without that assumption, together with a cost identity for every order sequence.
--
--   **Formalization Note** The policy is the order sequence chosen at time 0 for the whole horizon, and $A_k$ is the value of (13), which coincides with the paper's $q^*_k\Gamma_k+\sum_i r^*_{ik}$ when $h>0$.
-- source:
--   Bertsimas, Thiele, A Robust Optimization Approach to Inventory Theory, Operations Research 54(1):150–168 (2006), doi:10.1287/opre.1050.0238, p. 155, Theorem 3.2(a), (d); nonnegative demand stated on p. 156

import Mathlib
import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust

open Finset RobustInventory.SingleStation

theorem BertsimasThiele2006.theorem_3_2ad_faithful (M : Model)
    (hdem : ∀ k, M.what k ≤ M.wbar k) :
    (∀ u : ℕ → ℝ,
      (∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ), M.IsRobustOptimal u y q r) ↔
        M.IsNominalOptimal M.wmod u) ∧
    (∀ (u y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (u' : ℕ → ℝ),
      M.IsRobustOptimal u y q r → M.IsNominalOptimal M.wmod u' →
        M.robustObjective u y =
          M.nominalCost M.wmod u' + 2 * M.p * M.h / (M.p + M.h) * ∑ k ∈ range M.T, M.A k) := by sorry
