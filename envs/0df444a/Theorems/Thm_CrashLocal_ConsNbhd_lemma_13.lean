-- Prove2me | Theorems.Thm_CrashLocal_ConsNbhd_lemma_13
-- name    : CrashLocal.ConsNbhd.lemma_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:01:04.254062+00:00
-- url     : https://prove2.me/theorems/f4cd97fb-4dfb-442a-bef7-af21eb304dcb
-- title:
--   Lemma 13 — with T as in (2), surviving components of Γ_x agree on storing token x
-- statement:
--   Setting (§3): G is a finite simple graph on a finite vertex type V with at most n nodes; the nodes carry distinct identifiers id(v) ∈ {1, …, max{2, n}^{c_ID}} (StandingGraph n c_ID id) and input labels lab(v) in an arbitrary type L. Executions are those of deterministic node programs in the synchronous LOCAL model with standard crash failures (definition CrashLocal.ConsNbhd.Model): a program sees only its own identifier, its own label and its neighbors' identifiers, sends one message per neighbor per round and updates from the identifier-tagged messages it receives; an adversary chooses for every node a crash time (never, before the initial computation = round 0, or a round t ≥ 1) and, for a node crashing in round t, exactly which neighbors receive its round-t message. config t v is v's state at the end of round t (none once v has crashed); a node is alive at round t if it has not crashed by the end of round t. G has maximum degree at most Δ ≥ 2 and R ≥ 1. Choose T as in (2): T = Δ ∑_{i=0}^{R−1} (Δ−1)^i when Δ ≥ 3 (any adversary); T = c·Δ·R·f when a bound f ≥ 1 on the number of crashes is known (adversaries with at most f crashes in total); T = 2R when Δ = 2 (any adversary). There is c₀ such that for every c ≥ c₀ the following holds for every execution of Algorithm 5 (alg5 R T) under the corresponding choice: let S be the set of nodes that complete the algorithm (alive at the end of round R + T); for every x alive at the end of Phase I and every connected component of Γ_x[S ∩ V_x], either all its nodes store token x at the end of Phase II or none does. In particular the endpoints of every edge of Γ_x with both endpoints in S agree on whether they store token x.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) whose nodes programs know only by identifier → a finite type V ([Fintype V]) with G : SimpleGraph V and an injective id : V → ℕ; programs receive only identifiers; reason: every finite simple graph with identifiers is such a pair, and conversely
--   - encoding: standard crash faults: crashes in any round or before the initial computation, an arbitrary subset of the crash-round messages delivered → Adversary with crashTime : V → Option ℕ (some 0 = before the initial computation) and delivered : V → V → Prop chosen per recipient; reason: this is exactly the standard model; atomic crashes are the case delivered = ⊥
--   - encoding: round r of the execution → config … r = states at the end of round r, round 0 = the initial computation; reason: indexing convention only
--   - encoding: Phase II round r (rounds numbered from the start of each phase) → global round R + r of the single execution of alg5; reason: Phase I has exactly R rounds
--   - reading: T = c·Δ·R·f with 'c a sufficiently large positive integer constant' → ∃ c₀, ∀ c ≥ c₀; reason: standard reading of 'sufficiently large'; no fixed numeral is imposed (c₀ = 6 suffices by the count in Lemma 10's proof)
--   - generalization: any number of crashes (§3.2: up to f < n crashes) → every adversary, every crash set including F = V; reason: more executions are covered; restricting to |F| < n gives the source statement
--   - generalization: the standing identifier exponent c_ID is at least 1 → c_ID may be any natural number, including 0; reason: the extra case c_ID = 0 forces at most one vertex by injectivity and the identifier range {1}; gathering, flooding and all output guarantees remain valid on that case
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, Lemma 13, p. 29

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Algorithms
import Definitions.Def_CrashLocal_ConsNbhd_Problem

open Classical

namespace CrashLocal.ConsNbhd

theorem lemma_13 : ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c →
    ∀ {V L : Type} [Fintype V] (n cID Δ R T : ℕ), 2 ≤ Δ → 1 ≤ R →
    ∀ (G : SimpleGraph V) (id : V → ℕ) (lab : V → L), StandingGraph n cID id → MaxDegLe G Δ →
    ∀ adv : Adversary V, Choice2 c Δ R T adv → ∀ x, adv.alive R x →
      (∀ u w, ReachIn G ({v | adv.alive (R + T) v} ∩ propSet G id lab adv R T x) u w →
        (storesToken G id lab adv R T (R + T) u x ↔ storesToken G id lab adv R T (R + T) w x)) ∧
      (∀ u w, adv.alive (R + T) u → adv.alive (R + T) w → u ∈ propSet G id lab adv R T x →
        w ∈ propSet G id lab adv R T x → G.Adj u w →
        (storesToken G id lab adv R T (R + T) u x ↔ storesToken G id lab adv R T (R + T) w x)) := by sorry

end CrashLocal.ConsNbhd
