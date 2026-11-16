-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_Supplement_lemma_4_1
-- name    : CorrKClust.BalancedPivot.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:26:39.465856+00:00
-- url     : https://prove2.me/theorems/468bca00-1fc5-4ba1-908a-ba1af8af94cb
-- title:
--   Lemma 4.1 — approximate coarsening without splitting
-- statement:
--   Let $G$ be a finite graph, $k\ge1$, and $\alpha\ge1$. Let $Q$ be any unconstrained clustering with $\operatorname{Cost}_G(Q)\le\alpha\operatorname{OPT}_{CC}(G)$. There is a clustering $f$ using at most $k$ labels such that
--   $$Q(u)=Q(v)\Longrightarrow f(u)=f(v),\qquad
--   \operatorname{Cost}_G(f)\le(1+2\alpha)\operatorname{OPT}_k(G).$$
--   Thus a good unconstrained clustering has a good coarsening. No runtime claim is part of this lemma.
--
--   Differences from the source:
--   - encoding: arbitrary finite graphs and partitions → vertices Fin n, at most k labels, and the published disagreement objective; reason: every finite graph and every partition is represented up to relabeling; empty labels are allowed
--   - encoding: an α-approximation solution → the conventional approximation-factor range α≥1 and the cost inequality; reason: the factor convention is part of approximation terminology; a bare cost inequality on a zero-optimum graph would not exclude negative factors
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Lemma 4.1, p. 14

import Definitions.Def_CorrKClust_BalancedPivot_Instance

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot.Supplement

/-- Lemma 4.1, printed p.14: arbitrary approximate CC partition, without splitting. -/
theorem lemma_4_1 (n k : ℕ) (hk : 0 < k) (G : SimpleGraph (Fin n))
    (α : ℝ) (hα : 1 ≤ α) (Q : Fin n → Fin n) (hQ : (cost G Q : ℝ) ≤ α * optCC G) :
    ∃ f : Fin n → Fin k,
      (∀ u v, Q u = Q v → f u = f v) ∧
      (cost G f : ℝ) ≤ (1 + 2 * α) * optK G k := by sorry

end CorrKClust.BalancedPivot.Supplement
