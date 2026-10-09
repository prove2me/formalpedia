-- Prove2me | Theorems.Thm_BalancedPrices_Extension_theorem_4_2_balanced
-- name    : BalancedPrices.Extension.theorem_4_2_balanced
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:08:58.750485+00:00
-- url     : https://prove2.me/theorems/687a069e-c7c5-4265-872e-188ed11d6c1d
-- title:
--   Theorem 4.2, p. 553 — knapsack prices x_i·v(ALG(v)) with s_i ≤ 1/2 are balanced (stated as (2, 1); the page prints (1, 2))
-- statement:
--   The knapsack allocation problem with no agent requesting more than half of the capacity. Agent $i$ has a size $s_i\le1/2$ and a value $v_i\in[0,1]$; outcomes are $X_i=[0,\tfrac12]$ with null outcome $0$, $\mathcal F=\{\mathbf x\mid\sum_ix_i\le1\}$, and $v_i(x_i)=v_i$ if $x_i\ge s_i$, $v_i(x_i)=0$ otherwise. Let $\mathrm{ALG}(\mathbf v)\in\mathcal F$ be an arbitrary feasible allocation and set
--   $$p_i(x_i\mid\mathbf y)=\begin{cases}x_i\cdot\mathbf v(\mathrm{ALG}(\mathbf v))&\text{if }(x_i,\mathbf y_{-i})\in\mathcal F,\\ \infty&\text{otherwise,}\end{cases}$$
--   and $\mathcal F_{\mathbf x}=\mathcal F$ if $\sum_ix_i<\tfrac12$, $\mathcal F_{\mathbf x}=\varnothing$ otherwise. Then the family $(\mathcal F_{\mathbf x})$ is exchange compatible, $p$ is a pricing rule, and $p$ is **$(2,1)$-balanced** with respect to $\mathrm{ALG}$ and $(\mathcal F_{\mathbf x})$.
--
--   With Theorem 3.2 ($1+\alpha\beta=3$) this gives the $3$-approximation behind the paper's "$(3+\epsilon)$-approximate" posted-price mechanism for knapsack.
--
--   **Formalization Note** The printed theorem says "$(1,2)$-balanced". Its proof establishes property (a) with factor $\tfrac12$ (so $\alpha=2$) and property (b) with factor $1$ (so $\beta=1$), and $(1,2)$ is false: with four agents of size $\tfrac12$, values $0,0,1,1$, ALG = OPT giving $\tfrac12$ to agents 3 and 4, and $\mathbf x=(0.45,0.45,0,0)$, property (a) with $\alpha=1$ would need $0.9\cdot2\ge2$. The statement here is the one the proof proves; both readings give $1+\alpha\beta=3$. Only the balancedness half of Theorem 4.2 is stated; the polynomial-time claim is not. Outcomes are the subtype `Set.Icc 0 (1/2)` and agents are `Fin n`, 0-based.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 553, §4, Theorem 4.2 (balancedness part) and its proof

import Mathlib
import Definitions.Def_BalancedPrices_Extension_Model

open scoped ENNReal

namespace BalancedPrices.Extension

open Classical in
theorem theorem_4_2_balanced {n : ℕ} (s w : Fin n → ℝ) (hs : ∀ i, s i ≤ 1 / 2)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (a : Fin n → Set.Icc (0 : ℝ) (1 / 2)) (ha : ∑ i, ((a i : Set.Icc (0 : ℝ) (1 / 2)) : ℝ) ≤ 1) :
    ExchFamily (X := fun _ : Fin n => Set.Icc (0 : ℝ) (1 / 2))
        {x | ∑ i, ((x i : Set.Icc (0 : ℝ) (1 / 2)) : ℝ) ≤ 1}
        (fun x => if ∑ i, ((x i : Set.Icc (0 : ℝ) (1 / 2)) : ℝ) < 1 / 2 then
          {x | ∑ i, ((x i : Set.Icc (0 : ℝ) (1 / 2)) : ℝ) ≤ 1} else ∅) ∧
      IsPricingRule (X := fun _ : Fin n => Set.Icc (0 : ℝ) (1 / 2))
        {x | ∑ i, ((x i : Set.Icc (0 : ℝ) (1 / 2)) : ℝ) ≤ 1}
        (fun i xi y => if Function.update y i xi ∈
            {x : Fin n → Set.Icc (0 : ℝ) (1 / 2) | ∑ i, ((x i : Set.Icc (0 : ℝ) (1 / 2)) : ℝ) ≤ 1}
          then ENNReal.ofReal ((xi : ℝ) *
            welfare (X := fun _ : Fin n => Set.Icc (0 : ℝ) (1 / 2))
              (fun i xi => if s i ≤ (xi : ℝ) then w i else 0) a)
          else ⊤) ∧
      Balanced (X := fun _ : Fin n => Set.Icc (0 : ℝ) (1 / 2))
        (fun _ => ⟨0, by norm_num⟩) 2 1
        {x | ∑ i, ((x i : Set.Icc (0 : ℝ) (1 / 2)) : ℝ) ≤ 1}
        (fun x => if ∑ i, ((x i : Set.Icc (0 : ℝ) (1 / 2)) : ℝ) < 1 / 2 then
          {x | ∑ i, ((x i : Set.Icc (0 : ℝ) (1 / 2)) : ℝ) ≤ 1} else ∅)
        (fun i xi => if s i ≤ (xi : ℝ) then w i else 0) a
        (fun i xi y => if Function.update y i xi ∈
            {x : Fin n → Set.Icc (0 : ℝ) (1 / 2) | ∑ i, ((x i : Set.Icc (0 : ℝ) (1 / 2)) : ℝ) ≤ 1}
          then ENNReal.ofReal ((xi : ℝ) *
            welfare (X := fun _ : Fin n => Set.Icc (0 : ℝ) (1 / 2))
              (fun i xi => if s i ≤ (xi : ℝ) then w i else 0) a)
          else ⊤) := by sorry

end BalancedPrices.Extension
