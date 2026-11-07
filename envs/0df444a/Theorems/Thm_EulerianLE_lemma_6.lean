-- Prove2me | Theorems.Thm_EulerianLE_lemma_6
-- name    : EulerianLE.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:57:54.441405+00:00
-- url     : https://prove2.me/theorems/aa3d0c80-550e-4a84-882a-ff4c5b85e0aa
-- title:
--   Lemma 6 — a composition with a composable first phase splits into standalone executions
-- statement:
--   Let $A$ be composable on a class $I$ of inputs, $B$ any algorithm, $x\in I$, and $\rho$ a standalone execution (fair run) of the composition $(A,B)$ on $x$. Then there are standalone executions $\rho_A$ of $A$ on $x$, with outputs $y$, and $\rho_B$ of $B$ on $y$ such that:
--
--   1. for every node, its visible operations and local states during phase $A$ of $\rho$ are, in order, those of $\rho_A$;
--   2. for every node, its visible operations and local states during phase $B$ of $\rho$ are, in order, those of $\rho_B$;
--   3. if $B$ terminates on $y$, every node completes $(A,B)$ in $\rho$ with output $o$ if and only if it completes $B$ in $\rho_B$ with output $o$, that is,
--   $$(A,B)(I,S)=B(A(I,S_A),S_B).$$
--
--   The two standalone executions preserve each node's operations within each phase, not the global order of events of different phases. The lemma is the analogue of function composition for composable algorithms.
--
--   Differences from the source:
--   - generalization: the paper's network: a finite connected undirected Eulerian graph → any port-numbered multigraph (`Network`), with no Eulerian or connectivity hypothesis; reason: the statement concerns arbitrary algorithms and does not use the Eulerian property; Eulerian networks are a special case
--   - encoding: a scheduler generating WakeUp and PulseDeliver events, each after finitely many others; local computation takes no time → a fair run (`Run`, `IsFair`) in which wake-ups and deliveries occur only when no node can execute an instruction; reason: "Local computation takes no time" and "No delivery occurs between operations that a node performs at the same time" (pp.8, 10); the executions are the same
--   - reading: the execution under S_A (S_B) is equivalent to the execution of phase A (B) of (A, B) under S → per node, the sequences of visible operations and local states coincide (`SameSeq` of `phaseATrace`/`localTrace` and `phaseBTrace`/`localTrace`); reason: the paper's note after the lemma: they "preserve each node's operations within each phase, not the global order of events from different phases"
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §3.1, p.9 (PDF p.11), Lemma 6; proof App. A, pp.31–32

import Mathlib
import Definitions.Def_EulerianLE_IsComposable

namespace EulerianLE

/-- **Lemma 6** (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), §3.1, p.9, PDF p.11; proof App. A, p.31). Let `A` be
composable on an input `I` and let `B` be any algorithm. Let `S` be a scheduler of `(A, B)` on `I`. There
are schedulers `S_A` and `S_B` of standalone executions of `A` on `I` and of `B` on `A(I, S_A)` under which
the execution is equivalent to the execution of the phases of `(A, B)` under `S`, respectively. If `B`
terminates on `A(I, S_A)`, then `(A, B)(I, S) = B(A(I, S_A), S_B)`.

**Formalization Note.** A scheduler with its execution is a fair run. `A` is composable on the class
`I` and `x ∈ I`. "Equivalent" is read per node, as the paper's note does ("preserve each node's
operations within each phase, not the global order of events from different phases"): for every node,
the sequence of its visible operations and of its local states in phase A of `ρ` is that of `ρA`
(`phaseATrace`, `localTrace`), and in phase B that of `ρB` (`phaseBTrace`; the states of `ρB` are
paired with `B`'s input `y v`). The first part does not assume that `B` terminates. The last conjunct
is the equality of outputs: each node completes `(A, B)` with `o` exactly when it completes `B` with `o`
under `ρB`. -/
theorem lemma_6 {G : Network} {In O₁ O₂ : G.V → Type} (A : Algorithm G.V G.deg In O₁)
    (I : Set (∀ v, In v)) (hA : IsComposable A I) (B : Algorithm G.V G.deg O₁ O₂)
    (x : ∀ v, In v) (hx : x ∈ I) (ρ : Run ((A.comp B).progs x) (compTag A B x)) (hρ : IsFair ρ) :
    ∃ (ρA : Run (A.progs x) (stdTag _)) (y : ∀ v, O₁ v) (ρB : Run (B.progs y) (stdTag _)),
      IsFair ρA ∧ ρA.Outputs y ∧ IsFair ρB ∧
      (∀ v, SameSeq (ρ.phaseATrace v) (ρA.localTrace v)) ∧
      (∀ v, SameSeq (ρ.phaseBTrace v) fun t =>
        (ρB.localTrace v t).map fun e => (e.1, liftB (τ := fun o => (B v o).State) (y v) e.2)) ∧
      (TerminatesOn B {y} → ∀ v o, ρ.CompletesWith v o ↔ ρB.CompletesWith v o) := by sorry

end EulerianLE
