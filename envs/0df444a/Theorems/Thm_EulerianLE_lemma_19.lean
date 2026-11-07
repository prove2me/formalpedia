-- Prove2me | Theorems.Thm_EulerianLE_lemma_19
-- name    : EulerianLE.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:04.484453+00:00
-- url     : https://prove2.me/theorems/5c33ed1f-8d89-43f9-8107-7ada4b82a89e
-- title:
--   Lemma 19 — the chunks satisfy the local conditions of Theorem 8 with $d=4$
-- statement:
--   Let $r\ge1$, and let a node with identifier $\mathrm{ID}$ and a port pairing $\pi$ execute its chunk $P^r_{\mathrm{ID}}$ of round $L_r$ (Counting, Check or Relay) on input $(\mathit{result},\pi)$. Under every pattern of pulse deliveries to its ports, in any order and at any times, including before it starts the chunk:
--
--   1. when the chunk completes, $\sum_i\tilde\sigma_i=\sum_i\tilde\rho_i$;
--   2. a port $i$ has terminated if and only if $\tilde\sigma_i+\tilde\rho_i=4$;
--   3. the node consumes every pulse that it observes, for every pattern of deliveries afterwards, even if there are none.
--
--   With Theorem 8 this reduces the composability of a round to its termination (Corollary 20): every port makes exactly four pulse interactions per round.
--
--   Differences from the source:
--   - reading: the pseudocode of Programs 1–8, with "arbitrary" choices and an unspecified interleaving of concurrent branches → the Lean programs `program1` / `chunkProg`, which pick the smallest port (the first stored pair at Program 6, Line 18) and run concurrent branches in list order; reason: a deterministic refinement of the pseudocode is an instance of the algorithm; the paper's arguments hold "whichever port each wait or consumption at several ports selects" (p.36)
--   - encoding: ports 1, …, deg(u) → ports `Fin deg` (0-based); the initial pairs (2h−1, 2h) become (2h, 2h+1); reason: a relabelling; lexicographic and smallest-port orders are unchanged
--   - reading: "for any arbitrary pattern of pulse deliveries", port termination, condition 3 → the local conditions `LocalCond1`, `LocalCond2 _ 4`, `LocalCond3` over local runs that start asleep; reason: as for Theorem 8; a local run starting asleep includes deliveries before the chunk starts
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), App. C.1, p.34 (PDF p.36), Lemma 19, with Table 3, p.35

import Mathlib
import Definitions.Def_EulerianLE_chunkCode
import Definitions.Def_EulerianLE_LReach

namespace EulerianLE

/-- **Lemma 19** (Local conditions of the chunk programs; Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), App. C.1,
p.34, PDF p.36). Let `r ≥ 1` and let `u` execute its chunk of `L_r`. For any arbitrary pattern of pulse
deliveries to `u`'s ports, in any order and at any times, including before `u` starts the chunk,
1. when the chunk completes, `∑_i σ̃_i = ∑_i ρ̃_i`;
2. a port `i` has terminated if and only if `σ̃_i + ρ̃_i = 4`; and
3. `u` consumes every pulse that it observes, for any arbitrary pattern of pulse deliveries afterwards,
   even if there are none.

**Formalization Note.** The chunk of `L_r` at a node with identifier `id` is `P^r_id` (`chunkKind r id`),
which for `r ≥ 1` is Counting, Check or Relay; its input `x = (result, π)` has `π` a port pairing of the
node (as in every valid configuration). The local runs (`LReach`) start asleep, so deliveries before the
chunk starts are included. In a run of the chunk alone, its counters σ̃, ρ̃ are the counters `sent`,
`consumed` of the local run. -/
theorem lemma_19 (r : ℕ) (hr : 1 ≤ r) (id deg : ℕ) (x : ChunkIO deg) (hx : IsPairing x.2) :
    LocalCond1 (chunkProg deg (chunkKind r id) x) ∧
    LocalCond2 (chunkProg deg (chunkKind r id) x) 4 ∧
    LocalCond3 (chunkProg deg (chunkKind r id) x) := by sorry

end EulerianLE
