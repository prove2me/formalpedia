-- Prove2me | Theorems.Thm_CrashLocal_ConsNbhd_lemma_18
-- name    : CrashLocal.ConsNbhd.lemma_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:00:58.830261+00:00
-- url     : https://prove2.me/theorems/53ff6877-d366-43ca-be60-c11c42868ac1
-- title:
--   Lemma 18 — the round complexity of Algorithm 5 is O((Δ−1)^R), O(Δ·R·f), or 3R
-- statement:
--   Setting (§3): G is a finite simple graph on a finite vertex type V with at most n nodes; the nodes carry distinct identifiers id(v) ∈ {1, …, max{2, n}^{c_ID}} (StandingGraph n c_ID id) and input labels lab(v) in an arbitrary type L. Executions are those of deterministic node programs in the synchronous LOCAL model with standard crash failures (definition CrashLocal.ConsNbhd.Model): a program sees only its own identifier, its own label and its neighbors' identifiers, sends one message per neighbor per round and updates from the identifier-tagged messages it receives; an adversary chooses for every node a crash time (never, before the initial computation = round 0, or a round t ≥ 1) and, for a node crashing in round t, exactly which neighbors receive its round-t message. config t v is v's state at the end of round t (none once v has crashed); a node is alive at round t if it has not crashed by the end of round t. G has maximum degree at most Δ ≥ 2 and R ≥ 1, and T is chosen as in (2). There is c₀ such that for every c ≥ c₀ there is a constant C (independent of R, Δ, f, n, the graph and the execution) such that: Algorithm 5 (alg5 R T) has every node alive at the end of round R + T output at that round (so its round complexity is R + T), and R + T ≤ C·(Δ−1)^R for T = Δ ∑_{i=0}^{R−1} (Δ−1)^i with Δ ≥ 3; R + T ≤ C·Δ·R·f for T = c·Δ·R·f with f ≥ 1; and R + T = 3R for T = 2R with Δ = 2.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) whose nodes programs know only by identifier → a finite type V ([Fintype V]) with G : SimpleGraph V and an injective id : V → ℕ; programs receive only identifiers; reason: every finite simple graph with identifiers is such a pair, and conversely
--   - encoding: standard crash faults: crashes in any round or before the initial computation, an arbitrary subset of the crash-round messages delivered → Adversary with crashTime : V → Option ℕ (some 0 = before the initial computation) and delivered : V → V → Prop chosen per recipient; reason: this is exactly the standard model; atomic crashes are the case delivered = ⊥
--   - encoding: round r of the execution → config … r = states at the end of round r, round 0 = the initial computation; reason: indexing convention only
--   - reading: T = c·Δ·R·f with 'c a sufficiently large positive integer constant' → ∃ c₀, ∀ c ≥ c₀; reason: standard reading of 'sufficiently large'; no fixed numeral is imposed (c₀ = 6 suffices by the count in Lemma 10's proof)
--   - generalization: any number of crashes (§3.2: up to f < n crashes) → every adversary, every crash set including F = V; reason: more executions are covered; restricting to |F| < n gives the source statement
--   - reading: O((Δ−1)^R) and O(Δ·R·f) round complexity → R + T ≤ C·(Δ−1)^R and R + T ≤ C·Δ·R·f for a constant C chosen after c and before every other parameter; reason: the constant c of (2) is fixed, so the O-constant may depend on it and on nothing else; the proof gives R + T ≤ 4(Δ−1)^R and R + cΔRf ≤ (c+1)ΔRf
--   - generalization: the standing identifier exponent c_ID is at least 1 → c_ID may be any natural number, including 0; reason: the extra case c_ID = 0 forces at most one vertex by injectivity and the identifier range {1}; gathering, flooding and all output guarantees remain valid on that case
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, Lemma 18, p. 31

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Algorithms
import Definitions.Def_CrashLocal_ConsNbhd_Problem

open Classical

namespace CrashLocal.ConsNbhd

theorem lemma_18 : ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ C : ℕ,
    ∀ {V L : Type} [Fintype V] (n cID Δ R T : ℕ), 2 ≤ Δ → 1 ≤ R →
    ∀ (G : SimpleGraph V) (id : V → ℕ) (lab : V → L), StandingGraph n cID id → MaxDegLe G Δ →
    ∀ adv : Adversary V, Choice2 c Δ R T adv →
      (∀ v, adv.alive (R + T) v → ∃ H, outputAt G id lab (alg5 R T) adv (R + T) v = some H) ∧
      (3 ≤ Δ → T = Δ * ∑ i ∈ Finset.range R, (Δ - 1) ^ i → R + T ≤ C * (Δ - 1) ^ R) ∧
      (∀ f, 1 ≤ f → T = c * Δ * R * f → R + T ≤ C * (Δ * R * f)) ∧
      (Δ = 2 → T = 2 * R → R + T = 3 * R) := by sorry

end CrashLocal.ConsNbhd
