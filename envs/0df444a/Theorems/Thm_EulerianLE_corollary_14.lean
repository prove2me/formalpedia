-- Prove2me | Theorems.Thm_EulerianLE_corollary_14
-- name    : EulerianLE.corollary_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:20.411608+00:00
-- url     : https://prove2.me/theorems/d6cc278f-3f59-4343-8eb2-0b4ee9aeb476
-- title:
--   Corollary 14 — Program 1 is the composition of its rounds, elects the node with identifier $\mathrm{ID}_{\max}$, and is composable
-- statement:
--   Let $G$ be an Eulerian network with distinct identifiers. Then:
--
--   1. Program 1 is equivalent to $(L_0,\dots,L_{\mathrm{ID}_{\max}+1})$: for any standalone executions of the two with the same sequence of wake-ups and deliveries, the sequences of visible operations (sends, consumptions, successful queue tests and completions, with the node performing each) coincide, together with the node's variables when it performs each operation;
--   2. Program 1 elects the node with identifier $\mathrm{ID}_{\max}$: in every standalone execution it completes with output Leader and every other node with Non-Leader;
--   3. Program 1 is composable.
--
--   Differences from the source:
--   - generalization: a finite connected undirected Eulerian graph with ports numbered 1, …, deg(u) → a port-numbered multigraph (`Network`): a fixed-point-free involution `link` on ports, self-loops and parallel edges allowed; reason: every simple Eulerian graph with every port numbering is an instance, so the statement specializes to the source's; the paper's own proofs use self-loops and parallel edges (pp.33, 38, 43)
--   - encoding: a scheduler generating WakeUp and PulseDeliver events, each after finitely many others; local computation takes no time → a fair run (`Run`, `IsFair`) in which wake-ups and deliveries occur only when no node can execute an instruction; reason: "Local computation takes no time" and "No delivery occurs between operations that a node performs at the same time" (pp.8, 10); the executions are the same
--   - reading: the pseudocode of Programs 1–8, with "arbitrary" choices and an unspecified interleaving of concurrent branches → the Lean programs `program1` / `chunkProg`, which pick the smallest port (the first stored pair at Program 6, Line 18) and run concurrent branches in list order; reason: a deterministic refinement of the pseudocode is an instance of the algorithm; the paper's arguments hold "whichever port each wait or consumption at several ports selects" (p.36)
--   - reading: "equivalent": under the same wake-ups and deliveries, every node performs the same operations and passes through the same local states, except for the resettable counters → same sequence of visible operations, each with the variables (store) of the executing node, for runs with the same scheduler events; reason: program positions are positions in two different program texts and have no common type; they are compared through the operations they produce
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §5.2, p.25 (PDF p.27), Corollary 14, with pp.24–25 (equivalence)

import Mathlib
import Definitions.Def_EulerianLE_program1

namespace EulerianLE

/-- **Corollary 14** (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), §5.2, p.25, PDF p.27). On every Eulerian network,
Program 1 is equivalent to `(L₀, …, L_{IDmax+1})`, elects the node with identifier `IDmax`, and is
composable.

**Formalization Note.** Identifiers are distinct (§2, p.6). "Equivalent" (pp.24–25): "in standalone
executions under the same wake-ups and deliveries, every node performs the same operations and passes
through the same local states, except for the resettable counters". Here: for any standalone
executions (fair runs) `ρ₁` of Program 1 and `ρ₂` of the composition whose sequences of wake-ups and
deliveries coincide, the sequences of all visible operations (sends, consumptions, successful queue
tests, completions) coincide, together with the node's variables when it performs each of them
(`program1Store`, `roundsStore`: the variables of the chunk being run). Program positions are compared
through these operations (they are positions in two different program texts). "Elects the node with
identifier `IDmax`": in every fair run that node completes with `leader` and every other with
`nonLeader`. Program 1 has no input. -/
theorem corollary_14 (G : Network) (hG : G.IsEulerian) (ids : G.V → ℕ)
    (hid : Function.Injective ids) :
    (∀ (ρ₁ : Run ((program1Alg G ids).progs fun _ => ()) (stdTag _))
        (ρ₂ : Run ((roundsAlg G ids (IDmax G ids + 1)).progs (dummyInput G)) (stdTag _)),
        IsFair ρ₁ → IsFair ρ₂ → SameSeq ρ₁.schedTrace ρ₂.schedTrace →
        SameSeq (ρ₁.extTrace (α := fun v => Store (G.deg v)) fun v st => program1Store (ids v) (G.deg v) st)
          (ρ₂.extTrace (α := fun v => Store (G.deg v)) fun v st =>
            roundsStore (ids v) (G.deg v) (IDmax G ids + 1) (dummyInput G v) st)) ∧
    (∀ ρ : Run ((program1Alg G ids).progs fun _ => ()) (stdTag _), IsFair ρ →
      ∀ v, ρ.CompletesWith v (if ids v = IDmax G ids then .leader else .nonLeader)) ∧
    IsComposable (program1Alg G ids) {fun _ => ()} := by sorry

end EulerianLE
