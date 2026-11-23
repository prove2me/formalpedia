-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_mixed_target_rank_charges
-- name    : ChenCapacityTerminals.Exact.mixed_target_rank_charges
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:37:23.0238+00:00
-- url     : https://prove2.me/theorems/6cbf703d-8708-4b5f-8ef5-bfd3ff1d6986
-- title:
--   Lemma 2.3 — mixed targets charged by cardinality rank
-- statement:
--   Under the hypotheses of Lemma 2.3, put $\tau=L/(4d)$ and $n=|V|$. The mixed-target entries also satisfy the rankwise bound
--   $$
--   |\delta_{T,\mathrm{mixed}}^-(X)|\le \lfloor\log_2 n\rfloor\,\frac{f(X)}{\tau}.
--   $$
--   Every mixed target has an internal original bundle of more than $\tau$ units entering its intersection with $X$. Two strictly nested mixed targets $A\subsetneq B$ satisfy $|B|\ge2|A|$, because $A$ is a nonheavy child and the parent containing it lies in $B$. Hence mixed targets with the same rank $\lfloor\log_2|C|\rfloor$ are disjoint. Within each rank their internal bundles yield at most $f(X)/\tau$ targets, and ranks range from $1$ through $\lfloor\log_2 n\rfloor$ because every mixed target has at least two vertices.
--
--   This is the rank partition alternative in the “Mixed targets” paragraph of Lemma 2.3. As in the paper, original arcs may recur in different ranks and in the separate whole-target count.
--
--   **Formalization Note** `Nat.log2` is the floor binary logarithm. The hypotheses match the parent leaf uniformly, although this subargument needs only the construction and cut-capacity data.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), p. 5, PDF p. 6, Lemma 2.3, “Mixed targets” paragraph, heavy-child/rank argument; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=6

import Definitions.Def_ChenCapacityTerminals_Exact_GuideTargets

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.mixed_target_rank_charges
    (G : ChenCapacityTerminals.Exact.Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (c : ChenCapacityTerminals.Exact.Construction) (X : Finset ℕ)
    (hG : ChenCapacityTerminals.Exact.Prepared G r) (hd : 1 ≤ d) (hdn : d ≤ G.vertices.card)
    (hL : 0 < L) (hlower : ChenCapacityTerminals.Exact.RootLowerBound G r L)
    (hc : ChenCapacityTerminals.Exact.LegalConstruction G r d L b t c)
    (hX : X ⊆ G.vertices \ (c.earlyProbes G r ((L : ℝ) / (4 * d)) ∪ {r})) :
    (ChenCapacityTerminals.Exact.mixedTargetEntries c G ((L : ℝ) / (4 * d)) X : ℝ) ≤
      (Nat.log2 G.vertices.card) * ChenCapacityTerminals.Exact.cut G X /
        ((L : ℝ) / (4 * d)) := by sorry
