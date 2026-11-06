-- Prove2me | Theorems.Thm_FeedbackSwitching_lemma_6
-- name    : FeedbackSwitching.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:28.605567+00:00
-- url     : https://prove2.me/theorems/02c7c2e9-535b-403e-89a7-ddec07f7c19b
-- title:
--   Lemma 6 — logarithmic rooted assignment: the LP (19) has an optimal solution with value in $[1,3\log(e/v_{\min})]$
-- statement:
--   For every tournament on $K\ge2$ actions and every positive probability vector $v$:
--
--   1. $\mathcal C(v)$ contains a point with $\sum_s\rho_s\le3\log(e/v_{\min})$, where $v_{\min}=\min_iv_i$;
--   2. the linear program (19) has an optimal solution;
--   3. every optimal solution has value in $[1,\,3\log(e/v_{\min})]$.
--
--   The logarithmic total source weight is what keeps the importance weights of the estimator small.
--
--   **Formalization Note** "Its value lies in $[1,3\log(e/v_{\min})]$" is stated for the total source weight of every optimal solution.
--
--   Differences from the source: none.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Lemma 6, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_FeedbackSwitching_CSet

namespace FeedbackSwitching

/-- **Lemma 6 (Logarithmic rooted assignment)**, p.29 (PDF p.31). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

"For every tournament on `K ≥ 2` actions and every positive probability vector `v`, the set
`C(v)` of Definition 3 contains a point with `∑_s ρ_s ≤ 3 log(e/v_min)`, where
`v_min = min_i v_i`. The linear program in Eq. (19) has an optimal solution, and its value lies in
`[1, 3 log(e/v_min)]`."

**Formalization Note.** The value of the LP is the total source weight of any optimal solution;
the last clause is stated for every optimal solution. -/
theorem lemma_6 {K : ℕ} (hK : 2 ≤ K) (A : Fin K → Fin K → Prop) (hA : IsTournament A)
    (v : Fin K → ℝ) (hv : IsPosProbVec v) :
    (∃ z ∈ CSet A v, ∑ s, z.2 s ≤ 3 * Real.log (Real.exp 1 / vmin v)) ∧
    (∃ z, IsOptimalAssignment A v z) ∧
    ∀ z, IsOptimalAssignment A v z →
      1 ≤ ∑ s, z.2 s ∧ ∑ s, z.2 s ≤ 3 * Real.log (Real.exp 1 / vmin v) := by sorry

end FeedbackSwitching
