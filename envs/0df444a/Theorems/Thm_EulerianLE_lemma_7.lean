-- Prove2me | Theorems.Thm_EulerianLE_lemma_7
-- name    : EulerianLE.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:07.315204+00:00
-- url     : https://prove2.me/theorems/d7263eab-803f-4bbb-847a-d4b3e5a0e81b
-- title:
--   Lemma 7 — compositions of composable algorithms are composable
-- statement:
--   Let $A$ be composable on a class $I$ of inputs and suppose that every output of every standalone execution of $A$ on an input of $I$ belongs to a class $J$. If $B$ is composable on $J$, then the composition $(A,B)$ is composable on $I$.
--
--   By induction, a composition $(A_0,\dots,A_s)$ of composable algorithms with matching input and output classes is composable; the analysis of Program 1 as a composition of rounds rests on this.
--
--   Differences from the source:
--   - generalization: the paper's network: a finite connected undirected Eulerian graph → any port-numbered multigraph (`Network`), with no Eulerian or connectivity hypothesis; reason: the statement concerns arbitrary algorithms and does not use the Eulerian property; Eulerian networks are a special case
--   - encoding: a scheduler generating WakeUp and PulseDeliver events, each after finitely many others; local computation takes no time → a fair run (`Run`, `IsFair`) in which wake-ups and deliveries occur only when no node can execute an instruction; reason: "Local computation takes no time" and "No delivery occurs between operations that a node performs at the same time" (pp.8, 10); the executions are the same
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), §3.1, p.10 (PDF p.12), Lemma 7; proof App. A, p.32

import Mathlib
import Definitions.Def_EulerianLE_IsComposable

namespace EulerianLE

/-- **Lemma 7** (Frei, Gelles, Ghazy, Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission (manuscript sha256 90954a93…), §3.1, p.10, PDF p.12; proof App. A, p.32). If `A` is
composable on `I` with its outputs belonging to `J`, and `B` is composable on `J`, then `(A, B)` is
composable on `I`.

**Formalization Note.** "Its outputs belonging to `J`": every output tuple of every standalone execution
(fair run) of `A` on an input in `I` lies in `J`. -/
theorem lemma_7 {G : Network} {In O₁ O₂ : G.V → Type} (A : Algorithm G.V G.deg In O₁)
    (B : Algorithm G.V G.deg O₁ O₂) (I : Set (∀ v, In v)) (J : Set (∀ v, O₁ v))
    (hA : IsComposable A I)
    (hAJ : ∀ x ∈ I, ∀ ρ : Run (A.progs x) (stdTag _), IsFair ρ → ∀ y, ρ.Outputs y → y ∈ J)
    (hB : IsComposable B J) : IsComposable (A.comp B) I := by sorry

end EulerianLE
