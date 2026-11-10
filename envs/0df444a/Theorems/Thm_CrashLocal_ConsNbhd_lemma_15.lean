-- Prove2me | Theorems.Thm_CrashLocal_ConsNbhd_lemma_15
-- name    : CrashLocal.ConsNbhd.lemma_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:01:16.795731+00:00
-- url     : https://prove2.me/theorems/58f3337b-0c8e-44f3-a715-996e33dc1226
-- title:
--   Lemma 15 — with T as in (2), Algorithm 5 outputs are consistent on the comparison sets
-- statement:
--   Setting (§3): G is a finite simple graph on a finite vertex type V with at most n nodes; the nodes carry distinct identifiers id(v) ∈ {1, …, max{2, n}^{c_ID}} (StandingGraph n c_ID id) and input labels lab(v) in an arbitrary type L. Executions are those of deterministic node programs in the synchronous LOCAL model with standard crash failures (definition CrashLocal.ConsNbhd.Model): a program sees only its own identifier, its own label and its neighbors' identifiers, sends one message per neighbor per round and updates from the identifier-tagged messages it receives; an adversary chooses for every node a crash time (never, before the initial computation = round 0, or a round t ≥ 1) and, for a node crashing in round t, exactly which neighbors receive its round-t message. config t v is v's state at the end of round t (none once v has crashed); a node is alive at round t if it has not crashed by the end of round t. G has maximum degree at most Δ ≥ 2 and R ≥ 1, and T is chosen as in (2) (as in Lemma 13, with the matching executions: any adversary for Δ ≥ 3 or Δ = 2, at most f crashes for T = c·Δ·R·f). There is c₀ such that for every c ≥ c₀: in every execution of Algorithm 5 (alg5 R T), if two adjacent nodes u and v both output H_u and H_v at the end of round R + T, then H_u[S_u(v)] = H_v[S_v(u)] as labeled graphs, where S_u(v) = B_{H_u}(u, R−1) ∪ B_{H_u}(v, R−1) and S_v(u) = B_{H_v}(u, R−1) ∪ B_{H_v}(v, R−1) are the comparison sets of Definition 2 computed in H_u and H_v.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) whose nodes programs know only by identifier → a finite type V ([Fintype V]) with G : SimpleGraph V and an injective id : V → ℕ; programs receive only identifiers; reason: every finite simple graph with identifiers is such a pair, and conversely
--   - encoding: standard crash faults: crashes in any round or before the initial computation, an arbitrary subset of the crash-round messages delivered → Adversary with crashTime : V → Option ℕ (some 0 = before the initial computation) and delivered : V → V → Prop chosen per recipient; reason: this is exactly the standard model; atomic crashes are the case delivered = ⊥
--   - encoding: round r of the execution → config … r = states at the end of round r, round 0 = the initial computation; reason: indexing convention only
--   - encoding: a node outputs a labeled subgraph of G → a View on identifiers (node set, edge set, labels) that Represents a G.Subgraph K through id; reason: nodes can name other nodes only by identifier; id is injective, so the view determines K
--   - encoding: input labels if the problem has them → labels in an arbitrary type L; reason: an unlabeled problem is L = Unit
--   - reading: T = c·Δ·R·f with 'c a sufficiently large positive integer constant' → ∃ c₀, ∀ c ≥ c₀; reason: standard reading of 'sufficiently large'; no fixed numeral is imposed (c₀ = 6 suffices by the count in Lemma 10's proof)
--   - generalization: any number of crashes (§3.2: up to f < n crashes) → every adversary, every crash set including F = V; reason: more executions are covered; restricting to |F| < n gives the source statement
--   - generalization: the standing identifier exponent c_ID is at least 1 → c_ID may be any natural number, including 0; reason: the extra case c_ID = 0 forces at most one vertex by injectivity and the identifier range {1}; gathering, flooding and all output guarantees remain valid on that case
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, Lemma 15, p. 30

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Algorithms
import Definitions.Def_CrashLocal_ConsNbhd_Problem

open Classical

namespace CrashLocal.ConsNbhd

theorem lemma_15 : ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c →
    ∀ {V L : Type} [Fintype V] (n cID Δ R T : ℕ), 2 ≤ Δ → 1 ≤ R →
    ∀ (G : SimpleGraph V) (id : V → ℕ) (lab : V → L), StandingGraph n cID id → MaxDegLe G Δ →
    ∀ adv : Adversary V, Choice2 c Δ R T adv →
    ∀ u v Hu Hv, G.Adj u v → outputAt G id lab (alg5 R T) adv (R + T) u = some Hu →
      outputAt G id lab (alg5 R T) adv (R + T) v = some Hv →
      View.LabEq (Hu.induce (Hu.compSet R (id u) (id v)))
        (Hv.induce (Hv.compSet R (id u) (id v))) := by sorry

end CrashLocal.ConsNbhd
