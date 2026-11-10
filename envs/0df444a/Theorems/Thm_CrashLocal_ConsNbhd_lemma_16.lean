-- Prove2me | Theorems.Thm_CrashLocal_ConsNbhd_lemma_16
-- name    : CrashLocal.ConsNbhd.lemma_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:00:51.215315+00:00
-- url     : https://prove2.me/theorems/adeb3b12-9ee1-4413-bb7c-7dda75f516cc
-- title:
--   Lemma 16 — with T as in (2), a crash-free run of Algorithm 5 outputs G[B_G(v, R)]
-- statement:
--   Setting (§3): G is a finite simple graph on a finite vertex type V with at most n nodes; the nodes carry distinct identifiers id(v) ∈ {1, …, max{2, n}^{c_ID}} (StandingGraph n c_ID id) and input labels lab(v) in an arbitrary type L. Executions are those of deterministic node programs in the synchronous LOCAL model with standard crash failures (definition CrashLocal.ConsNbhd.Model): a program sees only its own identifier, its own label and its neighbors' identifiers, sends one message per neighbor per round and updates from the identifier-tagged messages it receives; an adversary chooses for every node a crash time (never, before the initial computation = round 0, or a round t ≥ 1) and, for a node crashing in round t, exactly which neighbors receive its round-t message. config t v is v's state at the end of round t (none once v has crashed); a node is alive at round t if it has not crashed by the end of round t. G has maximum degree at most Δ ≥ 2 and R ≥ 1, and T is chosen as in (2). There is c₀ such that for every c ≥ c₀: if no node crashes in Algorithm 5 (alg5 R T), then every node v outputs, at the end of round R + T, the view H_v = G[B_G(v, R)] (the labeled subgraph of G induced by the radius-R ball).
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) whose nodes programs know only by identifier → a finite type V ([Fintype V]) with G : SimpleGraph V and an injective id : V → ℕ; programs receive only identifiers; reason: every finite simple graph with identifiers is such a pair, and conversely
--   - encoding: standard crash faults: crashes in any round or before the initial computation, an arbitrary subset of the crash-round messages delivered → Adversary with crashTime : V → Option ℕ (some 0 = before the initial computation) and delivered : V → V → Prop chosen per recipient; reason: this is exactly the standard model; atomic crashes are the case delivered = ⊥
--   - encoding: round r of the execution → config … r = states at the end of round r, round 0 = the initial computation; reason: indexing convention only
--   - encoding: a node outputs a labeled subgraph of G → a View on identifiers (node set, edge set, labels) that Represents a G.Subgraph K through id; reason: nodes can name other nodes only by identifier; id is injective, so the view determines K
--   - encoding: input labels if the problem has them → labels in an arbitrary type L; reason: an unlabeled problem is L = Unit
--   - reading: T = c·Δ·R·f with 'c a sufficiently large positive integer constant' → ∃ c₀, ∀ c ≥ c₀; reason: standard reading of 'sufficiently large'; no fixed numeral is imposed (c₀ = 6 suffices by the count in Lemma 10's proof)
--   - generalization: the standing identifier exponent c_ID is at least 1 → c_ID may be any natural number, including 0; reason: the extra case c_ID = 0 forces at most one vertex by injectivity and the identifier range {1}; gathering, flooding and all output guarantees remain valid on that case
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, Lemma 16, p. 31

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Algorithms
import Definitions.Def_CrashLocal_ConsNbhd_Problem

open Classical

namespace CrashLocal.ConsNbhd

theorem lemma_16 : ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c →
    ∀ {V L : Type} [Fintype V] (n cID Δ R T : ℕ), 2 ≤ Δ → 1 ≤ R →
    ∀ (G : SimpleGraph V) (id : V → ℕ) (lab : V → L), StandingGraph n cID id → MaxDegLe G Δ →
    ∀ adv : Adversary V, Choice2 c Δ R T adv → (∀ v, adv.crashTime v = none) →
    ∀ v, ∃ H, outputAt G id lab (alg5 R T) adv (R + T) v = some H ∧
      Represents id lab H ((⊤ : G.Subgraph).induce (gBall G v R)) := by sorry

end CrashLocal.ConsNbhd
