-- Prove2me | Theorems.Thm_ForgetAlt_lemma_3_1
-- name    : ForgetAlt.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:25:23.513619+00:00
-- url     : https://prove2.me/theorems/4ee6b2c5-dead-4767-8642-547904a5f797
-- title:
--   Lemma 3.1: $\mathrm{cl}_K(y)\ne\mathrm{cl}_K(z)$ iff disjoint paths to two sinks; built in time linear in their out-degrees
-- statement:
--   Let $K$ be a finite DAG and $y\neq z$ vertices of $K$. Then
--
--   $$\mathrm{cl}_K(y)\neq\mathrm{cl}_K(z)\iff K\text{ has vertex-disjoint paths from }y\text{ and from }z\text{ to two distinct sinks.}$$
--
--   Moreover, given $\mathrm{cl}_K(\cdot)$ and $\phi:V(K)\to\mathbb N$ with $\phi(a)>\phi(b)$ on every arc $(a,b)$ and $\phi$ constant on the sinks, two such paths are constructed in time $O\big(\sum_{v\in P\cup Q}\deg^+(v)\big)$, linear in the total out-degree of their own vertices (not of $K$).
--
--   The first part is a Menger-type characterization of the postdominator classes; the second is the step that lets a double-path algorithm certify crossable edges cheaply.
--
--   Differences from the source:
--   - encoding: K a DAG → a finite type with an arc relation having no directed cycle; paths as duplicate-free vertex lists; reason: Lean convention
--   - reading: two such paths are constructed in time linear in the total out-degree of their vertices → there is one program of the published word RAM EndStatement (constants b, C) whose step count on the stated input layout is at most C·(bound + 1), at every word width W ≥ b·(⌊log₂ size⌋ + 1); reason: the paper's time bounds are word-RAM bounds with O(log n)-bit words; the + 1 only matters when the bound is 0
--   - encoding: the input K, cl_K and ϕ → adjacency lists, the arrays cl and ϕ, then y and z (DagInput layout); the width counts max ϕ; reason: ϕ's values must fit in machine words
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Lemma 3.1, printed p.16 (PDF p.17)

import Mathlib
import Definitions.Def_ForgetAlt_Layouts

namespace ForgetAlt

open BergeMatching.Core

/-- **Lemma 3.1**, printed p.16 (PDF p.17). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"Let `K` be a DAG, and let `y` and `z` be distinct vertices of `K`. Then `cl_K(y) ≠ cl_K(z)`
holds if and only if `K` admits vertex-disjoint paths from `y` and from `z` to two distinct
sinks. Moreover, given `cl_K(·)` and a function `ϕ : V(K) → ℕ` such that `ϕ(a) > ϕ(b)` holds for
every edge `(a, b)` and `ϕ` takes the same value on all sinks, two such paths are constructed in
time linear in the total out-degree of their vertices."

**Formalization Note.** First clause: any finite DAG given by an arc relation (acyclic: no arc
chain from a vertex back to itself). Vertex-disjoint paths to sinks end at distinct sinks.
Second clause: one word-RAM program (`EndStatement`) for all DAGs, given in the `DagInput`
layout (adjacency lists, `cl`, `ϕ`, then `y, z`); it halts within `C·(Σ_{v ∈ P ∪ Q} deg(v) + 1)`
steps, where `P, Q` are the two paths it outputs, at every width `W ≥ b·(⌊log₂ size⌋ + 1)`
(`size` counts `max ϕ`, so that the input fits in words). -/
theorem lemma_3_1 :
    (∀ (W : Type) [Finite W] (adj : W → W → Prop), (∀ a, ¬ Relation.TransGen adj a a) →
      ∀ y z : W, y ≠ z →
        (cl adj y ≠ cl adj z ↔
          ∃ P Q : List W, IsPathToSink adj y P ∧ IsPathToSink adj z Q ∧ List.Disjoint P Q)) ∧
    ∃ (prog : List EndStatement.Instr) (b C : ℕ), ∀ (N : ℕ) (x : DagInput N), x.Valid →
      ∀ W : ℕ, b * (Nat.log2 (dagSize x) + 1) ≤ W →
        ∃ (t : ℕ) (P Q : List (Fin N)),
          RunOutputs prog W t N (dagInput x) (fun out => Decodes out (encTwoPaths P Q)) ∧
          IsPathToSink x.arc x.y P ∧ IsPathToSink x.arc x.z Q ∧ List.Disjoint P Q ∧
          t ≤ C * (((P ++ Q).map x.deg).sum + 1) := by sorry

end ForgetAlt
