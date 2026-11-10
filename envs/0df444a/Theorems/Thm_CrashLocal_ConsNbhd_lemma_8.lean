-- Prove2me | Theorems.Thm_CrashLocal_ConsNbhd_lemma_8
-- name    : CrashLocal.ConsNbhd.lemma_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:00:54.197698+00:00
-- url     : https://prove2.me/theorems/678c5277-6a62-45aa-bf7a-336d7237ba65
-- title:
--   Lemma 8 — full-information gathering: coverage, locality and first-reception paths
-- statement:
--   Setting (§3): G is a finite simple graph on a finite vertex type V with at most n nodes; the nodes carry distinct identifiers id(v) ∈ {1, …, max{2, n}^{c_ID}} (StandingGraph n c_ID id) and input labels lab(v) in an arbitrary type L. Executions are those of deterministic node programs in the synchronous LOCAL model with standard crash failures (definition CrashLocal.ConsNbhd.Model): a program sees only its own identifier, its own label and its neighbors' identifiers, sends one message per neighbor per round and updates from the identifier-tagged messages it receives; an adversary chooses for every node a crash time (never, before the initial computation = round 0, or a round t ≥ 1) and, for a node crashing in round t, exactly which neighbors receive its round-t message. config t v is v's state at the end of round t (none once v has crashed); a node is alive at round t if it has not crashed by the end of round t. Run Algorithm 2 (gather t) for t ≥ 0 rounds against an arbitrary adversary, and let A be the set of nodes alive at the end of round t. For every v ∈ A, with Q_v = {x : σ_x ∈ K_v}: (1) B_{G[A]}(v, t) ⊆ Q_v ⊆ B_G(v, t); (2) if v first learns σ_x in round r with 0 ≤ r ≤ t, there is a simple path x = p_0, p_1, …, p_r = v in G such that for every 1 ≤ i ≤ r node p_i first learns σ_x in round i and receives σ_x from p_{i−1} in round i, and every p_i lies in Q_v; and every x ∈ Q_v is joined to v by a walk of length ≤ t inside Q_v (dist_{G[Q_v]}(v, x) ≤ t). Moreover: the first-reception path of (2) exists for every node v that first learns σ_x in a round r ≤ t, whether or not v completes the primitive; for every v ∈ A the graph reconstructed from K_v is exactly the labeled induced subgraph G[Q_v]; and in a fault-free execution Q_v = B_G(v, t) for every v.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) whose nodes programs know only by identifier → a finite type V ([Fintype V]) with G : SimpleGraph V and an injective id : V → ℕ; programs receive only identifiers; reason: every finite simple graph with identifiers is such a pair, and conversely
--   - encoding: standard crash faults: crashes in any round or before the initial computation, an arbitrary subset of the crash-round messages delivered → Adversary with crashTime : V → Option ℕ (some 0 = before the initial computation) and delivered : V → V → Prop chosen per recipient; reason: this is exactly the standard model; atomic crashes are the case delivered = ⊥
--   - encoding: round r of the execution → config … r = states at the end of round r, round 0 = the initial computation; reason: indexing convention only
--   - generalization: any number of crashes (§3.2: up to f < n crashes) → every adversary, every crash set including F = V; reason: more executions are covered; restricting to |F| < n gives the source statement
--   - encoding: every v ∈ A can reconstruct G[Q_v] from its collected stars → the view reconstruct K_v Represents the induced subgraph G[Q_v]; reason: this is the reconstruction the algorithms perform
--   - generalization: the standing identifier exponent c_ID is at least 1 → c_ID may be any natural number, including 0; reason: the extra case c_ID = 0 forces at most one vertex by injectivity and the identifier range {1}; gathering, flooding and all output guarantees remain valid on that case
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, Lemma 8, p. 23

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Algorithms
import Definitions.Def_CrashLocal_ConsNbhd_Problem

open Classical

namespace CrashLocal.ConsNbhd

theorem lemma_8 {V L : Type} [Fintype V] (n cID : ℕ) (G : SimpleGraph V)
    (id : V → ℕ) (lab : V → L) (hG : StandingGraph n cID id) (t : ℕ) (adv : Adversary V) :
    (∀ v, adv.alive t v →
      (ballIn G {w | adv.alive t w} v t ⊆ Qset G id lab adv t v ∧
        Qset G id lab adv t v ⊆ gBall G v t) ∧
      (∀ x r, r ≤ t → firstLearns G id lab adv t r v x →
        ∃ p : ℕ → V, p 0 = x ∧ p r = v ∧ Set.InjOn p (Set.Iic r) ∧
          (∀ i < r, G.Adj (p i) (p (i + 1))) ∧
          (∀ i, 1 ≤ i → i ≤ r → firstLearns G id lab adv t i (p i) x ∧
            receivesStar G id lab adv t i (p (i - 1)) (p i) x) ∧
          (∀ i ≤ r, p i ∈ Qset G id lab adv t v)) ∧
      (∀ x ∈ Qset G id lab adv t v, x ∈ ballIn G (Qset G id lab adv t v) v t)) ∧
    (∀ v x r, r ≤ t → firstLearns G id lab adv t r v x →
      ∃ p : ℕ → V, p 0 = x ∧ p r = v ∧ Set.InjOn p (Set.Iic r) ∧
        (∀ i < r, G.Adj (p i) (p (i + 1))) ∧
        (∀ i, 1 ≤ i → i ≤ r → firstLearns G id lab adv t i (p i) x ∧
          receivesStar G id lab adv t i (p (i - 1)) (p i) x)) ∧
    (∀ v, adv.alive t v →
      Represents id lab (reconstruct (Kset G id lab adv t v))
        ((⊤ : G.Subgraph).induce (Qset G id lab adv t v))) ∧
    ((∀ v, adv.crashTime v = none) → ∀ v, Qset G id lab adv t v = gBall G v t) := by sorry

end CrashLocal.ConsNbhd
