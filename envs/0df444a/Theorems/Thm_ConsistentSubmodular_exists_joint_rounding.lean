-- Prove2me | Theorems.Thm_ConsistentSubmodular_exists_joint_rounding
-- name    : ConsistentSubmodular.exists_joint_rounding
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:24.629453+00:00
-- url     : https://prove2.me/theorems/fe18d0bb-1a2f-419c-8584-6f6f8b2498e6
-- title:
--   Joint threshold rounding: sizes, intersection values and total recourse
-- statement:
--   Let $d,n\in\mathbb N$ and let $z_t\in[0,1]^n$ for $t\in\{0,\dots,d-1\}$ be fractional points. Let $\iota$ and $\varepsilon$ be finite index types; for $i\in\iota$ let $g_i$ be an objective on $[n]$ and let $\ell_i,r_i\in\{0,\dots,d-1\}$ be a pair of points; for $j\in\varepsilon$ let $\lambda_j,\rho_j\in\{0,\dots,d-1\}$ be a pair of points (an edge). Let $\kappa,L,M,a,b,R,p_{\rm size},p_{\rm val},p_{\rm cost}\in\mathbb R$ with $a\ge0$, $b>0$, $b\le2\kappa$, and $R,L,M>0$. Assume
--
--   * $\sum_e z_t(e)\le\kappa$ for every $t$;
--   * $g_i(\{e\})-g_i(\emptyset)\le L$ for all $i,e$;
--   * $\mathbb E_{A\sim\min(z_{\ell_i},z_{r_i})}[g_i(A)]\le M$ for every $i$;
--   * $e^{-b^2/(4\kappa)}\le p_{\rm size}$ and $e^{-a^2/(2LM)}\le p_{\rm val}$;
--   * $\sum_{j\in\varepsilon}\sum_e|z_{\lambda_j}(e)-z_{\rho_j}(e)|\le R\,p_{\rm cost}$;
--   * $d\,p_{\rm size}+|\iota|\,p_{\rm val}+p_{\rm cost}<1$.
--
--   Then there are sets $S_t\subseteq[n]$, $t<d$, such that
--
--   1. $e\notin S_t$ whenever $z_t(e)=0$, and $e\in S_t$ whenever $z_t(e)=1$;
--   2. $|S_t|\le\kappa+b$ for every $t$;
--   3. $\mathbb E_{A\sim\min(z_{\ell_i},z_{r_i})}[g_i(A)]-a\le g_i\big(S_{\ell_i}\cap S_{r_i}\big)$ for every $i\in\iota$;
--   4. $\sum_{j\in\varepsilon}|S_{\lambda_j}\triangle S_{\rho_j}|<R$;
--   5. if $z_s=z_t$ coordinatewise then $S_s=S_t$.
--
--   A single deterministic threshold assignment thus controls simultaneously all tested sizes, the objective values of tested intersections, and the total number of changes, with an explicit division-free probability budget independent of $n$. It is the probabilistic-method core of the rounding of fractional windows in Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/JointRounding.lean#L29-L138 (`ConsistentSubmodular.exists_joint_rounding`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation

open scoped BigOperators
set_option maxHeartbeats 2000000
open ConsistentSubmodular

theorem ConsistentSubmodular.exists_joint_rounding {n d : ℕ} {ι ε : Type*} [Fintype ι] [Fintype ε]
    (z : Fin d → Fin n → ℝ) (hz : ∀ t e, 0 ≤ z t e ∧ z t e ≤ 1)
    (g : ι → Objective n) (left right : ι → Fin d) (edgeLeft edgeRight : ε → Fin d)
    (κ L M a b R pSize pValue pCost : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hb2 : b ≤ 2 * κ) (hR : 0 < R) (hL : 0 < L) (hM : 0 < M)
    (hsize : ∀ t, ∑ e, z t e ≤ κ)
    (hcap : ∀ i e, (g i).value {e} - (g i).value ∅ ≤ L)
    (hmean : ∀ i, finiteExpectation (fun e => min (z (left i) e) (z (right i) e))
      (g i).value ≤ M)
    (hsizeBudget : Real.exp (-(b ^ 2) / (4 * κ)) ≤ pSize)
    (hvalueBudget : Real.exp (-(a ^ 2) / (2 * L * M)) ≤ pValue)
    (hcostBudget : (∑ j, ∑ e, |z (edgeLeft j) e - z (edgeRight j) e|) ≤ R * pCost)
    (hbudget : (d : ℝ) * pSize + (Fintype.card ι : ℝ) * pValue + pCost < 1) :
    ∃ S : Fin d → Finset (Fin n),
      (∀ t e, z t e = 0 → e ∉ S t) ∧
      (∀ t e, z t e = 1 → e ∈ S t) ∧
      (∀ t, (S t).card ≤ κ + b) ∧
      (∀ i, finiteExpectation (fun e => min (z (left i) e) (z (right i) e))
        (g i).value - a ≤ (g i).value (S (left i) ∩ S (right i))) ∧
      (∑ j, (recourse (S (edgeLeft j)) (S (edgeRight j)) : ℝ)) < R ∧
      (∀ s t, (∀ e, z s e = z t e) → S s = S t) := by sorry
