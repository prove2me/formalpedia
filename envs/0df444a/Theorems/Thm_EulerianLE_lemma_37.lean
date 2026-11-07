-- Prove2me | Theorems.Thm_EulerianLE_lemma_37
-- name    : EulerianLE.lemma_37
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:34.047205+00:00
-- url     : https://prove2.me/theorems/1b4a4738-e44f-4f62-bf0a-3a5d49b23d52
-- title:
--   Lemma 37 — the elected leader terminates after every other node
-- statement:
--   Let $G$ be an Eulerian network with distinct identifiers. In every standalone execution of Program 1 on $G$, every node other than the one that completes with output Leader completes, and it does so strictly before that node completes.
--
--   Differences from the source:
--   - generalization: a finite connected undirected Eulerian graph with ports numbered 1, …, deg(u) → a port-numbered multigraph (`Network`): a fixed-point-free involution `link` on ports, self-loops and parallel edges allowed; reason: every simple Eulerian graph with every port numbering is an instance, so the statement specializes to the source's; the paper's own proofs use self-loops and parallel edges (pp.33, 38, 43)
--   - encoding: a scheduler generating WakeUp and PulseDeliver events, each after finitely many others; local computation takes no time → a fair run (`Run`, `IsFair`) in which wake-ups and deliveries occur only when no node can execute an instruction; reason: "Local computation takes no time" and "No delivery occurs between operations that a node performs at the same time" (pp.8, 10); the executions are the same
--   - reading: the pseudocode of Programs 1–8, with "arbitrary" choices and an unspecified interleaving of concurrent branches → the Lean programs `program1` / `chunkProg`, which pick the smallest port (the first stored pair at Program 6, Line 18) and run concurrent branches in list order; reason: a deterministic refinement of the pseudocode is an instance of the algorithm; the paper's arguments hold "whichever port each wait or consumption at several ports selects" (p.36)
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), App. C.7, p.46 (PDF p.48), Lemma 37

import Mathlib
import Definitions.Def_EulerianLE_program1

namespace EulerianLE

/-- **Lemma 37** (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), App. C.7, p.46, PDF p.48). In every standalone execution
of Program 1 on an Eulerian network, the elected leader executes `terminate` after every other node.

**Formalization Note.** Identifiers are distinct (§2, p.6). The elected leader is the node that
completes with output `leader`; every other node completes (executes `terminate`), and "after" is strict
in the steps of the run. -/
theorem lemma_37 (G : Network) (hG : G.IsEulerian) (ids : G.V → ℕ)
    (hid : Function.Injective ids) :
    ∀ ρ : Run (fun v => program1 (ids v) (G.deg v)) (stdTag _), IsFair ρ →
      ∀ ℓ, ρ.CompletesWith ℓ .leader →
        ∀ w, w ≠ ℓ → ∃ tw, ρ.CompletesAt w tw ∧ ∀ tℓ, ρ.CompletesAt ℓ tℓ → tw < tℓ := by sorry

end EulerianLE
