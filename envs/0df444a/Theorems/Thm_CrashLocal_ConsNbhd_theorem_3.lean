-- Prove2me | Theorems.Thm_CrashLocal_ConsNbhd_theorem_3
-- name    : CrashLocal.ConsNbhd.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:02:57.934199+00:00
-- url     : https://prove2.me/theorems/5dfd6651-d4ac-42a5-9c0b-9e3063cebc5f
-- title:
--   Theorem 3 — Π_CN(R) is solvable in O(n), O((Δ−1)^R) (Δ ≥ 3), O(Δ·R·f) rounds, and in O(R) rounds when Δ = 2 or the girth exceeds 2R
-- statement:
--   Setting (§3): G is a finite simple graph on a finite vertex type V with at most n nodes; the nodes carry distinct identifiers id(v) ∈ {1, …, max{2, n}^{c_ID}} (StandingGraph n c_ID id) and input labels lab(v) in an arbitrary type L. Executions are those of deterministic node programs in the synchronous LOCAL model with standard crash failures (definition CrashLocal.ConsNbhd.Model): a program sees only its own identifier, its own label and its neighbors' identifiers, sends one message per neighbor per round and updates from the identifier-tagged messages it receives; an adversary chooses for every node a crash time (never, before the initial computation = round 0, or a round t ≥ 1) and, for a node crashing in round t, exactly which neighbors receive its round-t message. config t v is v's state at the end of round t (none once v has crashed); a node is alive at round t if it has not crashed by the end of round t. Π_CN(R) is the consistent neighborhoods problem of Definition 3 (termination and radius, edge validity, consistency on the comparison sets, fault-free completeness), and 'P solves Π_CN(R) on G in T rounds' means that in every admissible execution, with unrestricted crash times, every surviving node produces its first output by round T and the outputs satisfy the four properties. There is one absolute constant C such that for every R ≥ 1 and all known bounds n and Δ ≥ 2 there are deterministic node programs, chosen knowing only n, Δ, R (and f in (iii)) and the label type, such that for every c_ID ≥ 1 and every graph G with at most n nodes, maximum degree at most Δ, identifiers in {1, …, max{2,n}^{c_ID}} and input labels: (i) a program solves Π_CN(R) on G in C·n rounds against any number of crashes; (ii) if Δ ≥ 3, a program solves it in C·(Δ−1)^R rounds against any number of crashes; (iii) for every known f ≥ 1, a program solves it in C·Δ·R·f rounds against every execution with at most f crashes; (iv) if Δ = 2, a program solves it in C·R rounds against any number of crashes, and a program solves it in C·R rounds against any number of crashes on every such G of girth greater than 2R (in particular on forests).
--
--   Differences from the source:
--   - encoding: a graph G = (V, E) whose nodes programs know only by identifier → a finite type V ([Fintype V]) with G : SimpleGraph V and an injective id : V → ℕ; programs receive only identifiers; reason: every finite simple graph with identifiers is such a pair, and conversely
--   - encoding: standard crash faults: crashes in any round or before the initial computation, an arbitrary subset of the crash-round messages delivered → Adversary with crashTime : V → Option ℕ (some 0 = before the initial computation) and delivered : V → V → Prop chosen per recipient; reason: this is exactly the standard model; atomic crashes are the case delivered = ⊥
--   - encoding: every surviving node outputs by the end of round T and the outputs are correct → SolvesCNWithin: in every admissible execution with unrestricted crash times, each survivor first outputs at some t ≤ T and those outputs satisfy CNOutputs; reason: the first non-none observation is the reported output; later state observations cannot replace it, and no restriction on future crashes is imposed
--   - encoding: a node outputs a labeled subgraph of G → a View on identifiers (node set, edge set, labels) that Represents a G.Subgraph K through id; reason: nodes can name other nodes only by identifier; id is injective, so the view determines K
--   - encoding: input labels if the problem has them → labels in an arbitrary type L; reason: an unlabeled problem is L = Unit
--   - generalization: any number of crashes (§3.2: up to f < n crashes) → every adversary, every crash set including F = V; reason: more executions are covered; restricting to |F| < n gives the source statement
--   - reading: O(n), O((Δ−1)^R), O(Δ·R·f), O(R) rounds → C·n, C·(Δ−1)^R, C·Δ·R·f, C·R rounds for one C : ℕ chosen before R, n, Δ, f, c_ID, L, the graph and the execution; reason: the usual meaning of one absolute O-constant; the proofs give n − 1, ≤ 4(Δ−1)^R, R + cΔRf, 3R and R
--   - generalization: c_ID is a fixed known integer (programs may depend on it) → the program is chosen before c_ID and works for every c_ID ≥ 1; reason: a program independent of c_ID is in particular one that knows it
--   - encoding: (iv) O(R) rounds if Δ = 2 or the girth exceeds 2R → two conjuncts: one program for Δ = 2, one program for the class of graphs with egirth > 2R; reason: the girth case is a statement about a graph class; egirth is ∞ for forests
-- source:
--   Ghinea, Kuhn, Liu-Zhang, Parsaeian 2026, arXiv:2611.04898, Theorem 3, p. 3

import Mathlib
import Definitions.Def_CrashLocal_ConsNbhd_Algorithms
import Definitions.Def_CrashLocal_ConsNbhd_Problem

open Classical

namespace CrashLocal.ConsNbhd

theorem theorem_3 : ∃ C : ℕ,
    -- (i) `C·n` rounds, any number of crashes
    (∀ R n Δ : ℕ, 1 ≤ R → 2 ≤ Δ → ∀ L : Type, ∃ P : NodeProgram L (View L),
      ∀ cID : ℕ, 1 ≤ cID → ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (id : V → ℕ)
        (lab : V → L), StandingGraph n cID id → MaxDegLe G Δ →
        SolvesCNWithin G id lab P R (C * n) (fun _ => True)) ∧
    -- (ii) `C·(Δ−1)^R` rounds when `Δ ≥ 3`, any number of crashes
    (∀ R n Δ : ℕ, 1 ≤ R → 3 ≤ Δ → ∀ L : Type, ∃ P : NodeProgram L (View L),
      ∀ cID : ℕ, 1 ≤ cID → ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (id : V → ℕ)
        (lab : V → L), StandingGraph n cID id → MaxDegLe G Δ →
        SolvesCNWithin G id lab P R (C * (Δ - 1) ^ R) (fun _ => True)) ∧
    -- (iii) `C·Δ·R·f` rounds against at most `f` crashes, `f ≥ 1` known
    (∀ R n Δ f : ℕ, 1 ≤ R → 2 ≤ Δ → 1 ≤ f → ∀ L : Type, ∃ P : NodeProgram L (View L),
      ∀ cID : ℕ, 1 ≤ cID → ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (id : V → ℕ)
        (lab : V → L), StandingGraph n cID id → MaxDegLe G Δ →
        SolvesCNWithin G id lab P R (C * Δ * R * f) (fun adv => adv.crashCount ≤ f)) ∧
    -- (iv) `C·R` rounds when `Δ = 2`, any number of crashes
    (∀ R n Δ : ℕ, 1 ≤ R → Δ = 2 → ∀ L : Type, ∃ P : NodeProgram L (View L),
      ∀ cID : ℕ, 1 ≤ cID → ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (id : V → ℕ)
        (lab : V → L), StandingGraph n cID id → MaxDegLe G Δ →
        SolvesCNWithin G id lab P R (C * R) (fun _ => True)) ∧
    -- (iv) `C·R` rounds on graphs of girth greater than `2R` (forests included), any crashes
    (∀ R n Δ : ℕ, 1 ≤ R → 2 ≤ Δ → ∀ L : Type, ∃ P : NodeProgram L (View L),
      ∀ cID : ℕ, 1 ≤ cID → ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (id : V → ℕ)
        (lab : V → L), StandingGraph n cID id → MaxDegLe G Δ →
        ((2 * R : ℕ) : ℕ∞) < G.egirth →
        SolvesCNWithin G id lab P R (C * R) (fun _ => True)) := by sorry

end CrashLocal.ConsNbhd
