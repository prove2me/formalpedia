-- Prove2me | Theorems.Thm_CrashLocal_ConsNbhd_lemma_10
-- name    : CrashLocal.ConsNbhd.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:01:26.071462+00:00
-- url     : https://prove2.me/theorems/1fb08587-48a9-4d8b-8563-f46766b01e08
-- title:
--   Lemma 10 — flooding with at most f crashes: first receptions and agreement within O(D·Δ·f) rounds
-- statement:
--   Setting (§3): G is a finite simple graph on a finite vertex type V with at most n nodes; the nodes carry distinct identifiers id(v) ∈ {1, …, max{2, n}^{c_ID}} (StandingGraph n c_ID id) and input labels lab(v) in an arbitrary type L. Executions are those of deterministic node programs in the synchronous LOCAL model with standard crash failures (definition CrashLocal.ConsNbhd.Model): a program sees only its own identifier, its own label and its neighbors' identifiers, sends one message per neighbor per round and updates from the identifier-tagged messages it receives; an adversary chooses for every node a crash time (never, before the initial computation = round 0, or a round t ≥ 1) and, for a node crashing in round t, exactly which neighbors receive its round-t message. config t v is v's state at the end of round t (none once v has crashed); a node is alive at round t if it has not crashed by the end of round t. Here H is a finite simple graph with identifiers satisfying the standing assumptions, X the initial holders of m, and the flooding of Algorithm 3 continues indefinitely; S is the set of nodes that never crash. There is an absolute constant C such that for all such H, X and all Δ ≥ 2, D ≥ 1, f ≥ 1: if H has maximum degree at most Δ, every connected component of H has diameter at most D (any two nodes joined in H are at distance ≤ D), and at most f nodes crash, then (a) every surviving node v ∉ X that is ever informed is informed by the end of round C·D·Δ·f; (b) for any two nodes u, w of the same surviving component, either both are informed at the end of round C·D·Δ·f or neither is ever informed.
--
--   Differences from the source:
--   - encoding: Algorithm 3 run on a fixed subgraph H ⊆ G, messages only along H → flood run with H itself as the communication graph; the message m is the Boolean flag true (false = no message); reason: Algorithm 3 sends only along edges of H, so the execution is the same; nodes keep G’s identifiers
--   - encoding: standard crash faults: crashes in any round or before the initial computation, an arbitrary subset of the crash-round messages delivered → Adversary with crashTime : V → Option ℕ (some 0 = before the initial computation) and delivered : V → V → Prop chosen per recipient; reason: this is exactly the standard model; atomic crashes are the case delivered = ⊥
--   - encoding: round r of the execution → config … r = states at the end of round r, round 0 = the initial computation; reason: indexing convention only
--   - reading: O(D·Δ·f) rounds → C·D·Δ·f rounds for one constant C : ℕ chosen before H, X, Δ, D, f and the execution; reason: the usual meaning of an absolute O(·) bound; the proof gives r + 1 ≤ (2D+1)Δf + f
--   - generalization: the standing identifier exponent c_ID is at least 1 → c_ID may be any natural number, including 0; reason: the extra case c_ID = 0 forces at most one vertex by injectivity and the identifier range {1}; gathering, flooding and all output guarantees remain valid on that case
--   - generalization: the model assumes a crash budget f < n → any f ≥ 1, subject only to crashCount ≤ f; reason: the counting argument uses only the crash count bound; larger f only increases the deadline, and if all nodes crash the survivor claims are vacuous
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, Lemma 10, p. 26

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Algorithms
import Definitions.Def_CrashLocal_ConsNbhd_Problem

open Classical

namespace CrashLocal.ConsNbhd

theorem lemma_10 : ∃ C : ℕ, ∀ {W : Type} [Fintype W] (n cID : ℕ)
    (H : SimpleGraph W) (id : W → ℕ), StandingGraph n cID id →
    ∀ (X : Set W) (Δ D f : ℕ), 2 ≤ Δ → 1 ≤ D → 1 ≤ f → MaxDegLe H Δ →
    (∀ u w, H.Reachable u w → w ∈ gBall H u D) →
    ∀ adv : Adversary W, adv.crashCount ≤ f →
      (∀ v ∈ adv.survivors, v ∉ X → (∃ r, informed H id X adv r v) →
        informed H id X adv (C * D * Δ * f) v) ∧
      (∀ u ∈ adv.survivors, ∀ w ∈ adv.survivors, ReachIn H adv.survivors u w →
        (informed H id X adv (C * D * Δ * f) u ∧ informed H id X adv (C * D * Δ * f) w) ∨
        (∀ r, ¬ informed H id X adv r u ∧ ¬ informed H id X adv r w)) := by sorry

end CrashLocal.ConsNbhd
