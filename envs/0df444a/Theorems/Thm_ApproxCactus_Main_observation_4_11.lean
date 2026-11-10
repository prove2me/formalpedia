-- Prove2me | Theorems.Thm_ApproxCactus_Main_observation_4_11
-- name    : ApproxCactus.Main.observation_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:01:14.200764+00:00
-- url     : https://prove2.me/theorems/a67881ee-c35f-4e38-beda-a901dbcab4a5
-- title:
--   Observation 4.11 — ε-close ⇒ edit-distance ⩽ 2ε, and edit-distance ⩽ ε ⇒ ε-close
-- statement:
--   Let $s,t$ be separations of a finite graph $G$ and $\varepsilon\in\mathbb N$. (i) If $s$ and $t$ are $\varepsilon$-close, they have edit-distance $\le2\varepsilon$. (ii) If they have edit-distance $\le\varepsilon$, they are $\varepsilon$-close.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: a separation (A, B) of G → a pair (A, B) : Finset V × Finset V with IsSep G (A ∪ B = V(G), no edge between A ∖ B and B ∖ A); reason: the same objects; the predicate selects which pairs are separations
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Observation 4.11, printed p. 36 (PDF p. 39)

import Definitions.Def_ApproxCactus_Main_Separations

namespace ApproxCactus.Main

/-- **Observation 4.11**, p. 36: for separations `s, t` of `G` and `ε ∈ ℕ`,
(i) if `s` and `t` are `ε`-close, they have edit-distance `⩽ 2ε`;
(ii) if they have edit-distance `⩽ ε`, they are `ε`-close. -/
theorem observation_4_11 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (s t : Finset V × Finset V) (hs : IsSep G s) (ht : IsSep G t) (ε : ℕ) :
    (Close ε s t → EditDistLe (2 * ε) s t) ∧ (EditDistLe ε s t → Close ε s t) := by sorry

end ApproxCactus.Main
