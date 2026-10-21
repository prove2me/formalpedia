-- Prove2me | Theorems.Thm_BundleSearch_MatureNew_theorem_1
-- name    : BundleSearch.MatureNew.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:26:22.58178+00:00
-- url     : https://prove2.me/theorems/1d3972c8-b3a7-41a2-bbea-0622774f80e0
-- title:
--   Theorem 1, p. 15 — bundling versus separate selling
-- statement:
--   In the market with one mature and one new product, let $R_B^*(c)$ be the greatest bundle revenue over nonnegative bundle prices, and let $R_S^*(c)$ be the greatest total separate-selling revenue over pairs of nonnegative prices. For every search cost $c\ge0$, both maxima exist, and
--
--   $$R_S^*(c)\le R_B^*(c)\iff c\le\frac{25}{512},\qquad R_S^*(c)<R_B^*(c)\iff c<\frac{25}{512}.$$
--
--   Thus bundling earns more up to the threshold and ties separate selling at the threshold. The comparison is between the optimized revenues derived from customer choices, not formulas stipulated as optimal values.
--
--   **Formalization Note** The paper says “higher” at a boundary where both revenues equal $9/16$. The weak and strict versions state this boundary explicitly. Existence of both greatest revenues is included so the comparison is not vacuous.
-- source:
--   Wu, Jin & Chen, Managing Customer Search via Product Bundling, SSRN working paper 3692871 (version of 2022-01-17), p. 15, Theorem 1

import Mathlib
import Definitions.Def_BundleSearch_MatureNew_Model

namespace BundleSearch.MatureNew

/-- Theorem 1, p. 15: bundling's optimal revenue is at least that of separate selling
exactly through search cost 25/512. The two maximum-existence clauses make this
comparison nonvacuous; the strict comparison records equality at the threshold. -/
theorem theorem_1 (c : ℝ) (hc : 0 ≤ c) :
    (∃ RB : ℝ, IsGreatest (bundleRevenue c '' Set.Ici (0 : ℝ)) RB) ∧
    (∃ RS : ℝ, IsGreatest
      ((fun q : ℝ × ℝ => sepRevenue c q.1 q.2) ''
        (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))) RS) ∧
    ∀ RB RS : ℝ, IsGreatest (bundleRevenue c '' Set.Ici (0 : ℝ)) RB →
      IsGreatest ((fun q : ℝ × ℝ => sepRevenue c q.1 q.2) ''
        (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ))) RS →
      ((RS ≤ RB ↔ c ≤ 25 / 512) ∧ (RS < RB ↔ c < 25 / 512)) := by sorry

end BundleSearch.MatureNew
