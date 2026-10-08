-- Prove2me | Theorems.Thm_DemandSubstitution_Correlation_min_h_submodular
-- name    : DemandSubstitution.Correlation.min_h_submodular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:32.11368+00:00
-- url     : https://prove2.me/theorems/6b689fab-8987-4531-9c85-c3c0d57cb5b1
-- title:
--   Proof of Proposition 2, p. 7 — min(h(D), Q_i) is submodular in D
-- statement:
--   Fix the substitution model (in particular $a_{ji}\ge 0$), a stocking vector $Q\ge 0$ and a product $i$, and let $h(D) = D_i + \sum_{j\ne i} a_{ji}(D_j-Q_j)^+$ be the effective demand of product $i$. Then the realized sales of product $i$,
--   $$D \longmapsto \min\big(h(D),\,Q_i\big),$$
--   are a **submodular** function of the demand realization $D\in\mathbb R^n$ (componentwise order): for all $D, D'$,
--   $$\min(h(D\vee D'),Q_i) + \min(h(D\wedge D'),Q_i) \le \min(h(D),Q_i) + \min(h(D'),Q_i).$$
--
--   This is the term-by-term submodularity on which the submodularity of the realized centralized and per-firm profits rests.
--
--   **Formalization Note.** Submodularity of $f$ is stated as `SupermodularOn (fun x => -f x) Set.univ`. Only this instance is stated, not a general composition rule.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 7, proof of Proposition 2

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_DemandSubstitution_Correlation_Setting

namespace DemandSubstitution.Correlation

open Supermodularity.Monotonicity

theorem min_h_submodular {n : ℕ} (M : Model n) (Q : Fin n → ℝ) (hQ : ∀ k, 0 ≤ Q k)
    (i : Fin n) :
    SupermodularOn (fun x => -(min (Ds M Q x i) (Q i))) Set.univ := by sorry

end DemandSubstitution.Correlation
