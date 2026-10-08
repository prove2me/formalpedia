-- Prove2me | Theorems.Thm_DemandSubstitution_Correlation_profit_realization_submodular
-- name    : DemandSubstitution.Correlation.profit_realization_submodular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:40.824195+00:00
-- url     : https://prove2.me/theorems/d21a5db1-899b-4ed0-baba-bb57c946ee72
-- title:
--   Proof of Proposition 2, p. 7 — the realized profit π(D) = Σ_i [(u_i + o_i) min(D^s_i, Q_i) − o_i Q_i] is submodular in D
-- statement:
--   Fix the substitution model and a stocking vector $Q\ge 0$. For a demand realization $D\in\mathbb R^n$ let $D^s_i = D_i + \sum_{j\ne i} a_{ji}(D_j-Q_j)^+$, let
--   $$\pi_k(D) = u_k D^s_k - u_k (D^s_k - Q_k)^+ - o_k (Q_k - D^s_k)^+$$
--   be the realized profit of product $k$ and $\pi(D)=\sum_k \pi_k(D)$ the realized centralized profit. Then:
--
--   1. $\pi$ has the form used in the proof of Proposition 2: for every $D$,
--   $$\pi(D) = \sum_i\Big[(u_i+o_i)\min\Big(D_i + \sum_{j\ne i} a_{ji}(D_j-Q_j)^+,\ Q_i\Big) - o_i Q_i\Big];$$
--   2. $\pi$ is submodular in $D$ (componentwise order on $\mathbb R^n$);
--   3. each $\pi_k$ is submodular in $D$.
--
--   Submodularity of the realized profit, i.e. supermodularity of $-\pi$, is what lets the supermodular stochastic order of the demand vectors be applied to expected profit.
--
--   **Formalization Note.** Submodularity of $f$ is `SupermodularOn (fun x => -f x) Set.univ`. Item 3, for each firm's profit, is the per-firm version used for Proposition 5.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 7, proof of Proposition 2, display of π(D)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_DemandSubstitution_Correlation_Setting

namespace DemandSubstitution.Correlation

open Supermodularity.Monotonicity

theorem profit_realization_submodular {n : ℕ} (M : Model n) (Q : Fin n → ℝ)
    (hQ : ∀ k, 0 ≤ Q k) :
    (∀ x, profitAt M Q x = ∑ i, ((M.u i + M.o i) * min (Ds M Q x i) (Q i) - M.o i * Q i)) ∧
      SupermodularOn (fun x => -profitAt M Q x) Set.univ ∧
      ∀ k, SupermodularOn (fun x => -firmProfitAt M Q x k) Set.univ := by sorry

end DemandSubstitution.Correlation
