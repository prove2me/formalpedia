-- Prove2me | Theorems.Thm_CrashLocal_ConsNbhd_lemma_19
-- name    : CrashLocal.ConsNbhd.lemma_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:01:38.874829+00:00
-- url     : https://prove2.me/theorems/753150fe-846b-478d-94f6-eaf0cbd78372
-- title:
--   Lemma 19 — on graphs of girth > 2R, gathering for R rounds and outputting G[Q_v] solves Π_CN(R) in R rounds
-- statement:
--   Setting (§3): G is a finite simple graph on a finite vertex type V with at most n nodes; the nodes carry distinct identifiers id(v) ∈ {1, …, max{2, n}^{c_ID}} (StandingGraph n c_ID id) and input labels lab(v) in an arbitrary type L. Executions are those of deterministic node programs in the synchronous LOCAL model with standard crash failures (definition CrashLocal.ConsNbhd.Model): a program sees only its own identifier, its own label and its neighbors' identifiers, sends one message per neighbor per round and updates from the identifier-tagged messages it receives; an adversary chooses for every node a crash time (never, before the initial computation = round 0, or a round t ≥ 1) and, for a node crashing in round t, exactly which neighbors receive its round-t message. config t v is v's state at the end of round t (none once v has crashed); a node is alive at round t if it has not crashed by the end of round t. Let R ≥ 1 and let G have girth greater than 2R (Mathlib's egirth, which is ∞ for forests). The algorithm girthAlg R — run Algorithm 2 for R rounds and let every node output H_v = G[Q_v] reconstructed from its collected stars — solves Π_CN(R) on G in R rounds against every adversary: in every execution, every surviving node first outputs at the end of round R a view satisfying all four properties of Definition 3.
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) whose nodes programs know only by identifier → a finite type V ([Fintype V]) with G : SimpleGraph V and an injective id : V → ℕ; programs receive only identifiers; reason: every finite simple graph with identifiers is such a pair, and conversely
--   - encoding: standard crash faults: crashes in any round or before the initial computation, an arbitrary subset of the crash-round messages delivered → Adversary with crashTime : V → Option ℕ (some 0 = before the initial computation) and delivered : V → V → Prop chosen per recipient; reason: this is exactly the standard model; atomic crashes are the case delivered = ⊥
--   - encoding: every surviving node outputs by the end of round T and the outputs are correct → SolvesCNWithin: in every admissible execution with unrestricted crash times, each survivor first outputs at some t ≤ T and those outputs satisfy CNOutputs; reason: the first non-none observation is the reported output; later state observations cannot replace it, and no restriction on future crashes is imposed
--   - encoding: a node outputs a labeled subgraph of G → a View on identifiers (node set, edge set, labels) that Represents a G.Subgraph K through id; reason: nodes can name other nodes only by identifier; id is injective, so the view determines K
--   - encoding: input labels if the problem has them → labels in an arbitrary type L; reason: an unlabeled problem is L = Unit
--   - generalization: any number of crashes (§3.2: up to f < n crashes) → every adversary, every crash set including F = V; reason: more executions are covered; restricting to |F| < n gives the source statement
--   - encoding: girth = length of a shortest cycle, ∞ for acyclic graphs → SimpleGraph.egirth : ℕ∞ with 2R < egirth; reason: egirth is ⊤ exactly for acyclic graphs
--   - generalization: the standing identifier exponent c_ID is at least 1 → c_ID may be any natural number, including 0; reason: the extra case c_ID = 0 forces at most one vertex by injectivity and the identifier range {1}; gathering, flooding and all output guarantees remain valid on that case
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, Lemma 19, p. 31

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Algorithms
import Definitions.Def_CrashLocal_ConsNbhd_Problem

open Classical

namespace CrashLocal.ConsNbhd

theorem lemma_19 {V L : Type} [Fintype V] (n cID R : ℕ) (hR : 1 ≤ R)
    (G : SimpleGraph V) (id : V → ℕ) (lab : V → L) (hG : StandingGraph n cID id)
    (hgirth : ((2 * R : ℕ) : ℕ∞) < G.egirth) :
    SolvesCNWithin G id lab (girthAlg R) R R (fun _ => True) := by sorry

end CrashLocal.ConsNbhd
