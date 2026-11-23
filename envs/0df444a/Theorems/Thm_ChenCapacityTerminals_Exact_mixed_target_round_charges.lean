-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_mixed_target_round_charges
-- name    : ChenCapacityTerminals.Exact.mixed_target_round_charges
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:35:16.003047+00:00
-- url     : https://prove2.me/theorems/0ab64d73-2467-4c39-8da2-816f10e6ab0c
-- title:
--   Lemma 2.3 — mixed targets charged by formation round
-- statement:
--   Under the hypotheses of Lemma 2.3, put $\tau=L/(4d)$ and let $R$ be the construction’s stopping round. The mixed-target entries satisfy the roundwise bound
--   $$
--   |\delta_{T,\mathrm{mixed}}^-(X)|\le R\,\frac{f(X)}{\tau}.
--   $$
--   Every mixed target contains more than $\tau$ units of original entering capacity with both endpoints internal to that target. Targets formed in one round are pairwise disjoint. Consequently, for each formation round, the corresponding internal bundles can be assigned disjoint original arcs entering $X$, giving at most $f(X)/\tau$ targets in that round. Summing over the at most $R$ rounds proves the bound.
--
--   This is the round partition alternative in the “Mixed targets” paragraph of Lemma 2.3. The final targets are retained by the number of construction rounds, and arcs may be reused between different rounds, exactly as in the source proof.
--
--   **Formalization Note** The target decoration and mixed-entry counter are in `ChenCapacityTerminals_Exact_GuideTargets`. The hypotheses are kept identical to the parent leaf for a direct uniform reduction, even though some are not needed in this subargument.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 5, PDF p. 6, Lemma 2.3, “Mixed targets” paragraph, round-partition alternative; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=6

import Definitions.Def_ChenCapacityTerminals_Exact_GuideTargets

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.mixed_target_round_charges
    (G : ChenCapacityTerminals.Exact.Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (c : ChenCapacityTerminals.Exact.Construction) (X : Finset ℕ)
    (hG : ChenCapacityTerminals.Exact.Prepared G r) (hd : 1 ≤ d) (hdn : d ≤ G.vertices.card)
    (hL : 0 < L) (hlower : ChenCapacityTerminals.Exact.RootLowerBound G r L)
    (hc : ChenCapacityTerminals.Exact.LegalConstruction G r d L b t c)
    (hX : X ⊆ G.vertices \ (c.earlyProbes G r ((L : ℝ) / (4 * d)) ∪ {r})) :
    (ChenCapacityTerminals.Exact.mixedTargetEntries c G ((L : ℝ) / (4 * d)) X : ℝ) ≤
      c.rounds * ChenCapacityTerminals.Exact.cut G X / ((L : ℝ) / (4 * d)) := by sorry
