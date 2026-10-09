-- Prove2me | Theorems.Thm_BalancedPrices_Extension_claim_3_3
-- name    : BalancedPrices.Extension.claim_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:08:56.320138+00:00
-- url     : https://prove2.me/theorems/bd60d024-e950-4d62-94e6-a2d66091c15e
-- title:
--   Claim 3.3, p. 550 — the single-item price max_ℓ v_ℓ is (1, 1)-balanced with respect to OPT
-- statement:
--   The classic single-item setting: $n$ agents, $X_i=\{0,1\}$ (whether agent $i$ receives the item), null outcome $0$, and $\mathcal F=\{\mathbf x\mid\sum_ix_i\le1\}$. Agent $i$ has value $v_i\in[0,1]$ for the item and $0$ for nothing. Let $\mathbf a$ be a welfare-maximizing allocation, $\mathbf a\in\mathcal F$ with $\mathbf v(\mathbf a)=\mathbf v(\mathrm{OPT}(\mathbf v))$. Set
--   $$p_i(1\mid\mathbf x)=\begin{cases}\max_\ell v_\ell&\text{if }\mathbf x\text{ does not allocate the item},\\ \infty&\text{otherwise,}\end{cases}\qquad p_i(0\mid\mathbf x)=0,$$
--   and $\mathcal F_{\mathbf x}=\mathcal F$ if $\mathbf x$ does not allocate the item, $\mathcal F_{\mathbf x}=\varnothing$ otherwise. Then the family $(\mathcal F_{\mathbf x})$ is exchange compatible, $p$ is a pricing rule, and $p$ is $(1,1)$-balanced with respect to $\mathrm{OPT}$ and $(\mathcal F_{\mathbf x})$.
--
--   Together with Theorem 3.2 this rederives the classic factor-2 prophet inequality for a single item.
--
--   **Formalization Note** Outcomes are `Bool` (`true` = the item), agents are `Fin n`, 0-based, and $\max_\ell v_\ell$ is the real supremum `⨆ l, w l` (equal to $0$ when $n=0$). The valuation $v_i(0)=0$ is implicit in the paper's "$X_i=\{0,1\}$" and is made explicit. "With respect to OPT" is the hypothesis that the outcome `a` lies in $\mathcal F$ and attains the optimal welfare. Exchange compatibility of the family and the pricing-rule property, which the paper takes for granted, are part of the conclusion.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 550, §3.1, Claim 3.3 (proof pp. 550–551)

import Mathlib
import Definitions.Def_BalancedPrices_Extension_Model

open scoped ENNReal

namespace BalancedPrices.Extension

open Classical in
theorem claim_3_3 {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (a : Fin n → Bool)
    (ha : a ∈ {x : Fin n → Bool | (Finset.univ.filter fun i => x i = true).card ≤ 1})
    (hopt : welfare (X := fun _ : Fin n => Bool) (fun i b => if b then w i else 0) a =
      optVal (X := fun _ : Fin n => Bool) (fun i b => if b then w i else 0)
        {x : Fin n → Bool | (Finset.univ.filter fun i => x i = true).card ≤ 1}) :
    ExchFamily (X := fun _ : Fin n => Bool)
        {x : Fin n → Bool | (Finset.univ.filter fun i => x i = true).card ≤ 1}
        (fun x => if ∀ j, x j = false then
          {x : Fin n → Bool | (Finset.univ.filter fun i => x i = true).card ≤ 1} else ∅) ∧
      IsPricingRule (X := fun _ : Fin n => Bool)
        {x : Fin n → Bool | (Finset.univ.filter fun i => x i = true).card ≤ 1}
        (fun _ b y => if b then (if ∀ j, y j = false then ENNReal.ofReal (⨆ l, w l) else ⊤)
          else 0) ∧
      Balanced (X := fun _ : Fin n => Bool) (fun _ => false) 1 1
        {x : Fin n → Bool | (Finset.univ.filter fun i => x i = true).card ≤ 1}
        (fun x => if ∀ j, x j = false then
          {x : Fin n → Bool | (Finset.univ.filter fun i => x i = true).card ≤ 1} else ∅)
        (fun i b => if b then w i else 0) a
        (fun _ b y => if b then (if ∀ j, y j = false then ENNReal.ofReal (⨆ l, w l) else ⊤)
          else 0) := by sorry

end BalancedPrices.Extension
