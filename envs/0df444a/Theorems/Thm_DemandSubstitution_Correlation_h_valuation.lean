-- Prove2me | Theorems.Thm_DemandSubstitution_Correlation_h_valuation
-- name    : DemandSubstitution.Correlation.h_valuation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:36.751709+00:00
-- url     : https://prove2.me/theorems/d8e6564c-0412-40ca-bd9f-f93053fb3cc3
-- title:
--   Proof of Proposition 2, p. 7 — h(D) = D_i + Σ_{j≠i} a_ji (D_j − Q_j)⁺ is a valuation (both supermodular and submodular)
-- statement:
--   Fix the substitution model with data $a_{ji}$, a stocking vector $Q\ge 0$ and a product $i$. Consider the effective demand of product $i$ as a function of the demand realization $D\in\mathbb R^n$:
--   $$h(D) = D_i + \sum_{j\ne i} a_{ji}\,(D_j - Q_j)^+ .$$
--   Then $h$ is a **valuation** on the lattice $\mathbb R^n$ (componentwise order): it is both supermodular and submodular, i.e. for all $D, D'\in\mathbb R^n$,
--   $$h(D) + h(D') = h(D\vee D') + h(D\wedge D') .$$
--
--   The statement is the first step in showing that the realized profit is submodular in the demand vector, which combined with the supermodular ordering of normal laws gives Proposition 2.
--
--   **Formalization Note.** Supermodularity is the platform's `SupermodularOn … Set.univ` on `Fin n → ℝ` with its coordinatewise lattice operations; submodularity of $h$ is supermodularity of $-h$, and the theorem asserts both.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 7, proof of Proposition 2, display of h(D)

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_DemandSubstitution_Correlation_Setting

namespace DemandSubstitution.Correlation

open Supermodularity.Monotonicity

theorem h_valuation {n : ℕ} (M : Model n) (Q : Fin n → ℝ) (hQ : ∀ k, 0 ≤ Q k) (i : Fin n) :
    SupermodularOn (fun x => Ds M Q x i) Set.univ ∧
      SupermodularOn (fun x => -Ds M Q x i) Set.univ := by sorry

end DemandSubstitution.Correlation
