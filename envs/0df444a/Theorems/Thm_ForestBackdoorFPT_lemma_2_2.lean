-- Prove2me | Theorems.Thm_ForestBackdoorFPT_lemma_2_2
-- name    : ForestBackdoorFPT.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:31:42.763431+00:00
-- url     : https://prove2.me/theorems/82f17465-7b2c-4a11-9524-bb569f0f5490
-- title:
--   Lemma 2.2 — the 2-core of a graph with $\mathrm{cyc}(G)\le c$ has at most $2^c-1$ simple cycles
-- statement:
--   Let $c\ge0$ be an integer and let $G$ be a finite graph with $\mathrm{cyc}(G)\le c$. Then the 2-core $\mathrm{core}_2(G)$ contains at most
--
--   $$
--   2^c - 1
--   $$
--
--   distinct simple cycles.
--
--   Lemma 4.7 uses this bound to partition the variables into $2^{O(c)}$ classes that kill the same cycles.
--
--   Differences from the source:
--   - encoding: distinct simple cycles → edge sets of closed walks that are cycles, counted as an extended natural number; reason: each simple cycle has one edge set and different cycles have different edge sets; counting in ℕ∞ cannot hide an infinite family
--   - encoding: core₂(G), an induced subgraph → the graph induced on core2Set G, on the subtype of its vertices; reason: its cycles are exactly the cycles of G
-- source:
--   Bilyk–Munduzbaev–Sharma–Siam, Strong Backdoor to Forests is FPT: Tight Linear-Time FPT for Essentially General SAT, STOC 2027 submission (manuscript sha256 7fd1a7a8…), Lemma 2.2, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_ForestBackdoorFPT_cyc
import Definitions.Def_ForestBackdoorFPT_core2Set
import Definitions.Def_ForestBackdoorFPT_cycleEdgeSets

set_option autoImplicit false

namespace ForestBackdoorFPT

/-- **Lemma 2.2** (Bilyk–Munduzbaev–Sharma–Siam, *Strong Backdoor to Forests is FPT: Tight Linear-Time FPT for
Essentially General SAT*, STOC 2027 submission (manuscript sha256 7fd1a7a8…), Lemma 2.2, p.5 (PDF p.6)): "Let c ≥ 0 be an integer and let G be a graph
with cyc(G) ≤ c. Then core₂(G) contains at most 2^c − 1 distinct simple cycles."

**Formalization Note** Graphs are finite (`Fintype`), simple (`SimpleGraph`), on any vertex type
(possibly empty). Distinct simple cycles are counted by their edge sets (`cycleEdgeSets`), in
`ℕ∞` (`encard`), so an infinite family could not be counted as `0`. `2^c − 1` is truncated
subtraction in `ℕ`, which is exact since `2^c ≥ 1`. -/
theorem lemma_2_2 {W : Type*} [Fintype W] (G : SimpleGraph W) (c : ℕ) (hc : cyc G ≤ c) :
    (cycleEdgeSets (core2 G)).encard ≤ ((2 ^ c - 1 : ℕ) : ℕ∞) := by sorry

end ForestBackdoorFPT
