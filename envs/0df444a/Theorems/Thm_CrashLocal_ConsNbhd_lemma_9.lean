-- Prove2me | Theorems.Thm_CrashLocal_ConsNbhd_lemma_9
-- name    : CrashLocal.ConsNbhd.lemma_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:00:42.485296+00:00
-- url     : https://prove2.me/theorems/3753c243-b151-457e-ba47-999d6bb14364
-- title:
--   Lemma 9 — flooding and simple paths: surviving components agree by round L
-- statement:
--   Setting (§3): G is a finite simple graph on a finite vertex type V with at most n nodes; the nodes carry distinct identifiers id(v) ∈ {1, …, max{2, n}^{c_ID}} (StandingGraph n c_ID id) and input labels lab(v) in an arbitrary type L. Executions are those of deterministic node programs in the synchronous LOCAL model with standard crash failures (definition CrashLocal.ConsNbhd.Model): a program sees only its own identifier, its own label and its neighbors' identifiers, sends one message per neighbor per round and updates from the identifier-tagged messages it receives; an adversary chooses for every node a crash time (never, before the initial computation = round 0, or a round t ≥ 1) and, for a node crashing in round t, exactly which neighbors receive its round-t message. config t v is v's state at the end of round t (none once v has crashed); a node is alive at round t if it has not crashed by the end of round t. Here H is a finite simple graph (playing the role of the fixed subgraph of §5.2) with identifiers satisfying the standing assumptions, X ⊆ V(H) the nodes initially holding m, and the flooding of Algorithm 3 continues indefinitely against an arbitrary adversary; S is the set of nodes that never crash and a surviving component is a connected component of H[S]. Let L ≥ 0 be such that every simple path of H starting at a node of X has length at most L. Then (a) no node becomes informed after round L: a node informed at the end of a round r ≥ L is already informed at the end of round L; (b) for any two nodes u, w of the same surviving component, either both are informed at the end of round L or neither is ever informed; (c) if H is nonempty, any two nodes of the same surviving component agree on whether they are informed at the end of round |V(H)| − 1.
--
--   Differences from the source:
--   - encoding: Algorithm 3 run on a fixed subgraph H ⊆ G, messages only along H → flood run with H itself as the communication graph; the message m is the Boolean flag true (false = no message); reason: Algorithm 3 sends only along edges of H, so the execution is the same; nodes keep G’s identifiers
--   - encoding: standard crash faults: crashes in any round or before the initial computation, an arbitrary subset of the crash-round messages delivered → Adversary with crashTime : V → Option ℕ (some 0 = before the initial computation) and delivered : V → V → Prop chosen per recipient; reason: this is exactly the standard model; atomic crashes are the case delivered = ⊥
--   - encoding: round r of the execution → config … r = states at the end of round r, round 0 = the initial computation; reason: indexing convention only
--   - generalization: any number of crashes (§3.2: up to f < n crashes) → every adversary, every crash set including F = V; reason: more executions are covered; restricting to |F| < n gives the source statement
--   - generalization: the standing identifier exponent c_ID is at least 1 → c_ID may be any natural number, including 0; reason: the extra case c_ID = 0 forces at most one vertex by injectivity and the identifier range {1}; gathering, flooding and all output guarantees remain valid on that case
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, Lemma 9, p. 25

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Algorithms
import Definitions.Def_CrashLocal_ConsNbhd_Problem

open Classical

namespace CrashLocal.ConsNbhd

theorem lemma_9 {W : Type} [Fintype W] (n cID : ℕ) (H : SimpleGraph W)
    (id : W → ℕ) (hG : StandingGraph n cID id) (X : Set W) (adv : Adversary W) (Lb : ℕ)
    (hL : ∀ a ∈ X, ∀ b (p : H.Walk a b), p.IsPath → p.length ≤ Lb) :
    (∀ w r, Lb ≤ r → informed H id X adv r w → informed H id X adv Lb w) ∧
    (∀ u ∈ adv.survivors, ∀ w ∈ adv.survivors, ReachIn H adv.survivors u w →
      (informed H id X adv Lb u ∧ informed H id X adv Lb w) ∨
      (∀ r, ¬ informed H id X adv r u ∧ ¬ informed H id X adv r w)) ∧
    (Nonempty W → ∀ u ∈ adv.survivors, ∀ w ∈ adv.survivors, ReachIn H adv.survivors u w →
      (informed H id X adv (Fintype.card W - 1) u ↔
        informed H id X adv (Fintype.card W - 1) w)) := by sorry

end CrashLocal.ConsNbhd
