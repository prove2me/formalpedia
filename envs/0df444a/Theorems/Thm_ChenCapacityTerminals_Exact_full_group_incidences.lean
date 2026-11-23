-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_full_group_incidences
-- name    : ChenCapacityTerminals.Exact.full_group_incidences
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T02:26:31.236801+00:00
-- url     : https://prove2.me/theorems/055d1d7d-a4bb-47b4-a8da-2ab3e5344a6f
-- title:
--   Full source-tail groups have at most $m$ incidences
-- statement:
--   For a prepared rooted network and a legal construction, concatenate the consecutive full groups of $d$ sorted positive external tails over all unchanged final sources excluding $r$. Every resulting group is a $d$-element subset of the vertex set, and their total incidence count satisfies
--
--   $$
--   \sum_{g\in\mathcal G}|g|\le |E(G)|.
--   $$
--
--   Indeed, every listed tail has a positive bundle into its source and therefore contributes an actual arc. Sources in the old partition have disjoint head sets, and the prepared network has positive, coalesced, loopless arc records. Thus charges belonging to different sources cannot reuse an arc record. This lemma supplies the incidence estimate used by the greedy-cover size bound in Lemma 2.2.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), PDF p. 5 (printed p. 4), Lemma 2.2, 'The final source parts are disjoint, so across all lists there are at most m incidences'; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=5

import Definitions.Def_ChenCapacityTerminals_Exact_Construction

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.full_group_incidences (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
    (c : Construction) (hprep : Prepared G r) (hd : 1 ≤ d)
    (hdn : d ≤ G.vertices.card) (hL : 0 < L)
    (hc : LegalConstruction G r d L b t c) :
    let groups := (unchangedSources G r ((L : ℝ) / (4 * d))
      (c.partitions (c.rounds - 1))).toList.flatMap fun A => fullGroups d (c.tails A)
    (∀ g ∈ groups, g ⊆ G.vertices ∧ g.card = d) ∧
      (groups.map Finset.card).sum ≤ G.arcs.length := by sorry
