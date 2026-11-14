-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_exists_residual_rounding
-- name    : ConsistentSubmodular.Objective.exists_residual_rounding
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:37.203204+00:00
-- url     : https://prove2.me/theorems/d1bd3aef-dcbe-441a-91f2-b46e81d606e9
-- title:
--   Residual rounding with a forced set $D$ of fewer than $H$ elements
-- statement:
--   Let $f$ be an objective on $[n]$, $U\subseteq[n]$, and integers $\kappa\ge H>0$. Let $V>0$ with $f(A)\le V$ for all $A\subseteq U$ with $|A|\le\kappa$. Let $z_t\in[0,1]^n$ ($t\in\tau$) satisfy $z_t(e)=0$ for $e\notin U$ and $\sum_e z_t(e)\le\kappa$. Let $Q_i\subseteq[n]$, pairs $(\ell_i,r_i)\in\tau^2$ ($i\in\iota$), edges $(s_j,t_j)\in\tau^2$ ($j\in\varepsilon$), and targets $\mathrm{target}_i$ be such that
--   $$\mathrm{target}_i\le \mathbb E_{\min(z_{\ell_i},z_{r_i})}\big[f(Q_i\cup S)\big]\quad\text{for all } i,$$
--   where the expectation is over the random $S$ containing each $e$ independently with probability $\min(z_{\ell_i}(e),z_{r_i}(e))$. Let $a\ge0$, $b>0$ with $b\le 2\kappa$, $R>0$, and suppose
--   $e^{-b^2/(4\kappa)}\le p_{\rm size}$, $\ e^{-a^2/(2(V/H)(2V))}\le p_{\rm val}$, $\ \sum_j\sum_e|z_{s_j}(e)-z_{t_j}(e)|\le R\,p_{\rm cost}$ and $|\tau|\,p_{\rm size}+|\iota|\,p_{\rm val}+p_{\rm cost}<1$.
--
--   Then there exist $D\subseteq U$ with $|D|<H$ and sets $S_t\subseteq U$ ($t\in\tau$) such that
--
--   1. $e\notin S_t$ if $z_t(e)=0$ and $e\in S_t$ if $z_t(e)=1$;
--   2. $|S_t|\le\kappa+b$;
--   3. $\mathrm{target}_i-a\le f\big(Q_i\cup(D\cup(S_{\ell_i}\cap S_{r_i}))\big)$ for all $i$;
--   4. $\sum_j|S_{s_j}\triangle S_{t_j}|<R$;
--   5. $S_s=S_t$ whenever $z_s=z_t$.
--
--   This is the version of the joint rounding for a residual objective $S\mapsto f(Q\cup S)$ whose single-element marginals are not uniformly bounded: a small set $D$ of forced (heavy) elements is removed first so that the remaining marginals are at most $V/H$, and concentration then applies to the rest.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ResidualRounding.lean#L16-L72 (`ConsistentSubmodular.Objective.exists_residual_rounding`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.exists_residual_rounding {τ ι ε : Type*} [Fintype τ] [Fintype ι] [Fintype ε]
    (U : Finset (Fin n)) (κ H : ℕ) (hH : 0 < H) (hHκ : H ≤ κ)
    (V : ℝ) (hV : 0 < V) (hscale : ∀ A ⊆ U, A.card ≤ κ → f.value A ≤ V)
    (z : τ → Fin n → ℝ) (hz : ∀ t e, 0 ≤ z t e ∧ z t e ≤ 1)
    (hsupport : ∀ t e, e ∉ U → z t e = 0) (hsize : ∀ t, ∑ e, z t e ≤ κ)
    (Q : ι → Finset (Fin n)) (left right : ι → τ) (edgeLeft edgeRight : ε → τ)
    (target : ι → ℝ)
    (htarget : ∀ i, target i ≤ finiteExpectation
      (fun e => min (z (left i) e) (z (right i) e)) (fun S => f.value (Q i ∪ S)))
    (a b R pSize pValue pCost : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hb2 : b ≤ 2 * κ) (hR : 0 < R)
    (hsizeBudget : Real.exp (-(b ^ 2) / (4 * κ)) ≤ pSize)
    (hvalueBudget : Real.exp (-(a ^ 2) / (2 * (V / H) * (2 * V))) ≤ pValue)
    (hcostBudget : (∑ j, ∑ e, |z (edgeLeft j) e - z (edgeRight j) e|) ≤ R * pCost)
    (hbudget : (Fintype.card τ : ℝ) * pSize + (Fintype.card ι : ℝ) * pValue + pCost < 1) :
    ∃ D : Finset (Fin n), ∃ S : τ → Finset (Fin n), D ⊆ U ∧ D.card < H ∧
      (∀ t, S t ⊆ U) ∧
      (∀ t e, z t e = 0 → e ∉ S t) ∧
      (∀ t e, z t e = 1 → e ∈ S t) ∧
      (∀ t, (S t).card ≤ (κ : ℝ) + b) ∧
      (∀ i, target i - a ≤ f.value (Q i ∪ (D ∪ (S (left i) ∩ S (right i))))) ∧
      (∑ j, (recourse (S (edgeLeft j)) (S (edgeRight j)) : ℝ)) < R ∧
      (∀ s t, (∀ e, z s e = z t e) → S s = S t) := by sorry
