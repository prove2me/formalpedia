-- Prove2me | Theorems.Thm_CrashLocal_ConsNbhd_lemma_14
-- name    : CrashLocal.ConsNbhd.lemma_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:01:26.508588+00:00
-- url     : https://prove2.me/theorems/d5b9827a-9b38-4798-b78c-6a07c2b7b3af
-- title:
--   Lemma 14 — Algorithm 5 outputs are induced radius-R views containing every edge to an outputting neighbor
-- statement:
--   Setting (§3): G is a finite simple graph on a finite vertex type V with at most n nodes; the nodes carry distinct identifiers id(v) ∈ {1, …, max{2, n}^{c_ID}} (StandingGraph n c_ID id) and input labels lab(v) in an arbitrary type L. Executions are those of deterministic node programs in the synchronous LOCAL model with standard crash failures (definition CrashLocal.ConsNbhd.Model): a program sees only its own identifier, its own label and its neighbors' identifiers, sends one message per neighbor per round and updates from the identifier-tagged messages it receives; an adversary chooses for every node a crash time (never, before the initial computation = round 0, or a round t ≥ 1) and, for a node crashing in round t, exactly which neighbors receive its round-t message. config t v is v's state at the end of round t (none once v has crashed); a node is alive at round t if it has not crashed by the end of round t. G has maximum degree at most Δ ≥ 2; R ≥ 1, T ≥ 1, an arbitrary adversary, and an execution of Algorithm 5 (alg5 R T), whose outputs are produced at the end of round R + T. If v outputs H_v, then H_v is (represents) a labeled induced subgraph G[U] of G with v ∈ U ⊆ B_G(v, R), so it is a radius-R view centered at v. If two adjacent nodes u and v both output, then both H_u and H_v contain the edge {u, v}.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) whose nodes programs know only by identifier → a finite type V ([Fintype V]) with G : SimpleGraph V and an injective id : V → ℕ; programs receive only identifiers; reason: every finite simple graph with identifiers is such a pair, and conversely
--   - encoding: standard crash faults: crashes in any round or before the initial computation, an arbitrary subset of the crash-round messages delivered → Adversary with crashTime : V → Option ℕ (some 0 = before the initial computation) and delivered : V → V → Prop chosen per recipient; reason: this is exactly the standard model; atomic crashes are the case delivered = ⊥
--   - encoding: round r of the execution → config … r = states at the end of round r, round 0 = the initial computation; reason: indexing convention only
--   - encoding: a node outputs a labeled subgraph of G → a View on identifiers (node set, edge set, labels) that Represents a G.Subgraph K through id; reason: nodes can name other nodes only by identifier; id is injective, so the view determines K
--   - encoding: input labels if the problem has them → labels in an arbitrary type L; reason: an unlabeled problem is L = Unit
--   - generalization: any number of crashes (§3.2: up to f < n crashes) → every adversary, every crash set including F = V; reason: more executions are covered; restricting to |F| < n gives the source statement
--   - generalization: the standing identifier exponent c_ID is at least 1 → c_ID may be any natural number, including 0; reason: the extra case c_ID = 0 forces at most one vertex by injectivity and the identifier range {1}; gathering, flooding and all output guarantees remain valid on that case
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, Lemma 14, p. 30

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Algorithms
import Definitions.Def_CrashLocal_ConsNbhd_Problem

open Classical

namespace CrashLocal.ConsNbhd

theorem lemma_14 {V L : Type} [Fintype V] (n cID Δ R T : ℕ) (hΔ : 2 ≤ Δ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (G : SimpleGraph V) (id : V → ℕ) (lab : V → L)
    (hG : StandingGraph n cID id) (hdeg : MaxDegLe G Δ) (adv : Adversary V) :
    (∀ v H, outputAt G id lab (alg5 R T) adv (R + T) v = some H →
      ∃ U : Set V, Represents id lab H ((⊤ : G.Subgraph).induce U) ∧ v ∈ U ∧ U ⊆ gBall G v R) ∧
    (∀ u v Hu Hv, G.Adj u v → outputAt G id lab (alg5 R T) adv (R + T) u = some Hu →
      outputAt G id lab (alg5 R T) adv (R + T) v = some Hv →
      s(id u, id v) ∈ Hu.edges ∧ s(id u, id v) ∈ Hv.edges) := by sorry

end CrashLocal.ConsNbhd
