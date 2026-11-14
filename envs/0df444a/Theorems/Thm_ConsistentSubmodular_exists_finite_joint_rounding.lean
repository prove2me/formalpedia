-- Prove2me | Theorems.Thm_ConsistentSubmodular_exists_finite_joint_rounding
-- name    : ConsistentSubmodular.exists_finite_joint_rounding
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:27.708227+00:00
-- url     : https://prove2.me/theorems/03462fa4-865d-4c71-93e6-98b91d3a4517
-- title:
--   Joint rounding of fractional vectors with size, value and recourse guarantees
-- statement:
--   Let $\tau$, $\iota$, $\varepsilon$ be finite index types, and let $z_t\in[0,1]^{n}$ ($t\in\tau$) be fractional vectors with $\sum_e z_t(e)\le\kappa$. Let $g_i$ ($i\in\iota$) be objectives on $[n]$, each with pair $(\ell_i,r_i)\in\tau^2$ (`left`, `right`), and let each $j\in\varepsilon$ be an edge with endpoints $(s_j,t_j)\in\tau^2$ (`edgeLeft`, `edgeRight`). Write $\mathbb E_{\min(z,z')}[g]$ for the expectation of $g(S)$ when $S$ contains each element $e$ independently with probability $\min(z(e),z'(e))$. Assume reals $a\ge 0$, $b>0$, $L,M,R>0$ with $b\le 2\kappa$ and:
--
--   - $g_i(\{e\})-g_i(\emptyset)\le L$ for all $i,e$;
--   - $\mathbb E_{\min(z_{\ell_i},z_{r_i})}[g_i]\le M$ for all $i$;
--   - $e^{-b^2/(4\kappa)}\le p_{\rm size}$ and $e^{-a^2/(2LM)}\le p_{\rm val}$;
--   - $\sum_{j}\sum_e |z_{s_j}(e)-z_{t_j}(e)|\le R\,p_{\rm cost}$;
--   - $|\tau|\,p_{\rm size}+|\iota|\,p_{\rm val}+p_{\rm cost}<1$.
--
--   Then there are sets $S_t\subseteq[n]$ ($t\in\tau$) such that
--
--   1. $e\notin S_t$ whenever $z_t(e)=0$, and $e\in S_t$ whenever $z_t(e)=1$;
--   2. $|S_t|\le\kappa+b$ for every $t$;
--   3. $\mathbb E_{\min(z_{\ell_i},z_{r_i})}[g_i]-a\le g_i\big(S_{\ell_i}\cap S_{r_i}\big)$ for every $i$;
--   4. $\sum_{j}|S_{s_j}\,\triangle\,S_{t_j}|<R$;
--   5. $S_s=S_t$ whenever $z_s=z_t$ as vectors.
--
--   This is the probabilistic rounding step of the deterministic reduction: a single coupled rounding of all the fractional vectors simultaneously keeps the sizes concentrated, preserves the value of each intersection, and keeps the total change between adjacent vectors below the recourse budget, with a union bound over the three kinds of failure.
--
--   **Formalization Note**: The randomness is encoded through `finiteExpectation`, the exact sum over all subsets with product (Bernoulli) weights; the statement is purely existential and the sets $S_t$ are returned directly.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/FiniteJointRounding.lean#L13-L56 (`ConsistentSubmodular.exists_finite_joint_rounding`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation

open scoped BigOperators
open ConsistentSubmodular

theorem ConsistentSubmodular.exists_finite_joint_rounding {n : ℕ} {τ ι ε : Type*}
    [Fintype τ] [Fintype ι] [Fintype ε]
    (z : τ → Fin n → ℝ) (hz : ∀ t e, 0 ≤ z t e ∧ z t e ≤ 1)
    (g : ι → Objective n) (left right : ι → τ) (edgeLeft edgeRight : ε → τ)
    (κ L M a b R pSize pValue pCost : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hb2 : b ≤ 2 * κ) (hR : 0 < R) (hL : 0 < L) (hM : 0 < M)
    (hsize : ∀ t, ∑ e, z t e ≤ κ)
    (hcap : ∀ i e, (g i).value {e} - (g i).value ∅ ≤ L)
    (hmean : ∀ i, finiteExpectation (fun e => min (z (left i) e) (z (right i) e))
      (g i).value ≤ M)
    (hsizeBudget : Real.exp (-(b ^ 2) / (4 * κ)) ≤ pSize)
    (hvalueBudget : Real.exp (-(a ^ 2) / (2 * L * M)) ≤ pValue)
    (hcostBudget : (∑ j, ∑ e, |z (edgeLeft j) e - z (edgeRight j) e|) ≤ R * pCost)
    (hbudget : (Fintype.card τ : ℝ) * pSize + (Fintype.card ι : ℝ) * pValue + pCost < 1) :
    ∃ S : τ → Finset (Fin n),
      (∀ t e, z t e = 0 → e ∉ S t) ∧
      (∀ t e, z t e = 1 → e ∈ S t) ∧
      (∀ t, (S t).card ≤ κ + b) ∧
      (∀ i, finiteExpectation (fun e => min (z (left i) e) (z (right i) e))
        (g i).value - a ≤ (g i).value (S (left i) ∩ S (right i))) ∧
      (∑ j, (recourse (S (edgeLeft j)) (S (edgeRight j)) : ℝ)) < R ∧
      (∀ s t, (∀ e, z s e = z t e) → S s = S t) := by sorry
