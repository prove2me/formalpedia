-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_whole_target_charges
-- name    : ChenCapacityTerminals.Exact.whole_target_charges
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:34:26.667907+00:00
-- url     : https://prove2.me/theorems/e458632f-a39f-4f9d-b417-c727ad2a55c8
-- title:
--   Lemma 2.3 — whole-target entries charged by entering capacity
-- statement:
--   Under the hypotheses of Lemma 2.3, let $\tau=L/(4d)$ and suppose $X$ avoids the root and all early probes. Count only entering guide arcs whose associated target part is wholly contained in $X$. Then
--   $$
--   |\delta_{T,\mathrm{whole}}^-(X)|\le \frac{f(X)}{\tau}.
--   $$
--   For an ordinary join or final-predecessor arc, the original witness supplies more than $\tau$ units entering $X$. A dummy-root arc can have a wholly contained target only when that target is an unchanged final source; Lemma 2.2 then supplies at least $3\tau$ units from the greedy predecessors. The single-tail quotient rule, nonheavy targets, and target nodup conditions make all these original-arc charges disjoint.
--
--   This is exactly the “Targets wholly in $X$” paragraph of the proof of Lemma 2.3. Empty $X$ and zero-valued cuts are included.
--
--   **Formalization Note** The target decoration and whole-entry counter are in `ChenCapacityTerminals_Exact_GuideTargets`. The statement permits nonnegative real capacities, as does the parent theorem.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 5, PDF p. 6, Lemma 2.3, “Targets wholly in X” paragraph (using Lemma 2.2, PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=6

import Definitions.Def_ChenCapacityTerminals_Exact_GuideTargets

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.whole_target_charges
    (G : ChenCapacityTerminals.Exact.Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (c : ChenCapacityTerminals.Exact.Construction) (X : Finset ℕ)
    (hG : ChenCapacityTerminals.Exact.Prepared G r) (hd : 1 ≤ d) (hdn : d ≤ G.vertices.card)
    (hL : 0 < L) (hlower : ChenCapacityTerminals.Exact.RootLowerBound G r L)
    (hc : ChenCapacityTerminals.Exact.LegalConstruction G r d L b t c)
    (hX : X ⊆ G.vertices \ (c.earlyProbes G r ((L : ℝ) / (4 * d)) ∪ {r})) :
    (ChenCapacityTerminals.Exact.wholeTargetEntries c G ((L : ℝ) / (4 * d)) X : ℝ) ≤
      ChenCapacityTerminals.Exact.cut G X / ((L : ℝ) / (4 * d)) := by sorry
