-- Prove2me | Theorems.Thm_CrashLocal_ConsNbhd_lemma_12
-- name    : CrashLocal.ConsNbhd.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:04:26.773189+00:00
-- url     : https://prove2.me/theorems/1dd4e8c4-d942-49db-b69e-84756035ba9f
-- title:
--   Lemma 12 — token x floods on the propagation graph Γ_x, which is connected with diameter ≤ 2R and few nodes
-- statement:
--   Setting (§3): G is a finite simple graph on a finite vertex type V with at most n nodes; the nodes carry distinct identifiers id(v) ∈ {1, …, max{2, n}^{c_ID}} (StandingGraph n c_ID id) and input labels lab(v) in an arbitrary type L. Executions are those of deterministic node programs in the synchronous LOCAL model with standard crash failures (definition CrashLocal.ConsNbhd.Model): a program sees only its own identifier, its own label and its neighbors' identifiers, sends one message per neighbor per round and updates from the identifier-tagged messages it receives; an adversary chooses for every node a crash time (never, before the initial computation = round 0, or a round t ≥ 1) and, for a node crashing in round t, exactly which neighbors receive its round-t message. config t v is v's state at the end of round t (none once v has crashed); a node is alive at round t if it has not crashed by the end of round t. G has maximum degree at most Δ ≥ 2. Fix R ≥ 1, T ≥ 1, an arbitrary adversary and an execution of Algorithm 5 (alg5 R T); let x be a node alive at the end of Phase I (round R), V_x = {x} ∪ {nodes holding σ_x at the end of some Phase I round} and Γ_x = G[V_x]. (i) Consider flooding (Algorithm 3) on Γ_x with token x held initially only by x, where nodes that crashed in rounds ≤ R are inactive from the start, a node crashing in global round R + r crashes in flooding round r, and in a crash round the flooding message reaches exactly the neighbors in Γ_x that receive the sender's Phase II transmission. For every 1 ≤ r ≤ T and every w ∈ V_x alive at the end of global round R + r: w stores token x at the end of round R + r iff w is informed at the end of flooding round r. Moreover only nodes of V_x store token x during Phase II. (ii) Γ_x (including nodes that crash) is connected, has maximum degree at most Δ and diameter at most 2R; V_x ⊆ B_G(x, R); |V_x| ≤ 1 + Δ ∑_{i=0}^{R−1} (Δ−1)^i if Δ ≥ 3, and |V_x| ≤ 2R + 1 if Δ = 2.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) whose nodes programs know only by identifier → a finite type V ([Fintype V]) with G : SimpleGraph V and an injective id : V → ℕ; programs receive only identifiers; reason: every finite simple graph with identifiers is such a pair, and conversely
--   - encoding: standard crash faults: crashes in any round or before the initial computation, an arbitrary subset of the crash-round messages delivered → Adversary with crashTime : V → Option ℕ (some 0 = before the initial computation) and delivered : V → V → Prop chosen per recipient; reason: this is exactly the standard model; atomic crashes are the case delivered = ⊥
--   - encoding: round r of the execution → config … r = states at the end of round r, round 0 = the initial computation; reason: indexing convention only
--   - encoding: Phase II round r (rounds numbered from the start of each phase) → global round R + r of the single execution of alg5; reason: Phase I has exactly R rounds
--   - encoding: Algorithm 3 run on a fixed subgraph H ⊆ G, messages only along H → flood run with H itself as the communication graph; the message m is the Boolean flag true (false = no message); reason: Algorithm 3 sends only along edges of H, so the execution is the same; nodes keep G’s identifiers
--   - generalization: any number of crashes (§3.2: up to f < n crashes) → every adversary, every crash set including F = V; reason: more executions are covered; restricting to |F| < n gives the source statement
--   - generalization: the standing identifier exponent c_ID is at least 1 → c_ID may be any natural number, including 0; reason: the extra case c_ID = 0 forces at most one vertex by injectivity and the identifier range {1}; gathering, flooding and all output guarantees remain valid on that case
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, Lemma 12, p. 29

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Algorithms
import Definitions.Def_CrashLocal_ConsNbhd_Problem

open Classical

namespace CrashLocal.ConsNbhd

theorem lemma_12 {V L : Type} [Fintype V] (n cID Δ R T : ℕ) (hΔ : 2 ≤ Δ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (G : SimpleGraph V) (id : V → ℕ) (lab : V → L)
    (hG : StandingGraph n cID id) (hdeg : MaxDegLe G Δ) (adv : Adversary V) (x : V)
    (hx : adv.alive R x) :
    (∀ r, 1 ≤ r → r ≤ T → ∀ w : propSet G id lab adv R T x, adv.alive (R + r) w.val →
      (storesToken G id lab adv R T (R + r) w.val x ↔
        informed (G.induce (propSet G id lab adv R T x)) (fun w => id w.val) {w | w.val = x}
          (floodAdv adv R (propSet G id lab adv R T x)) r w)) ∧
    (∀ r, 1 ≤ r → r ≤ T → ∀ w, storesToken G id lab adv R T (R + r) w x →
      w ∈ propSet G id lab adv R T x) ∧
    (G.induce (propSet G id lab adv R T x)).Connected ∧
    MaxDegLe (G.induce (propSet G id lab adv R T x)) Δ ∧
    (G.induce (propSet G id lab adv R T x)).ediam ≤ ((2 * R : ℕ) : ℕ∞) ∧
    propSet G id lab adv R T x ⊆ gBall G x R ∧
    (3 ≤ Δ → (propSet G id lab adv R T x).ncard ≤ 1 + Δ * ∑ i ∈ Finset.range R, (Δ - 1) ^ i) ∧
    (Δ = 2 → (propSet G id lab adv R T x).ncard ≤ 2 * R + 1) := by sorry

end CrashLocal.ConsNbhd
