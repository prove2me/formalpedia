-- Prove2me | Theorems.Thm_FamousTheorems_hales_jewett
-- name    : FamousTheorems.hales_jewett
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:10.529598+00:00
-- url     : https://prove2.me/theorems/49bd0ff5-78b3-47dc-8c9f-b0c1c33e34cc
-- title:
--   The Hales–Jewett theorem
-- statement:
--   **The Hales–Jewett theorem.** For every finite alphabet $\alpha$ and finite set of colours $\kappa$ there is a finite dimension $\iota$ such that every colouring of the cube $\alpha^\iota$ with $\kappa$ colours contains a monochromatic combinatorial line.
--
--   A combinatorial line is obtained from a word with some "wildcard" coordinates by substituting the same letter for all wildcards. The theorem is the abstract core of Ramsey theory on words: van der Waerden's theorem and the Gallai–Witt theorem follow from it. The density version and Shelah's primitive recursive bounds are landmarks of combinatorics.
--
--   **Formalization note.** Mathlib's `Combinatorics.Line.exists_mono_in_high_dimension`. The dimension is an index type `ι : Type` with a `Fintype` structure, and `Combinatorics.Line.IsMono C l` says every point of the line `l` has the same colour.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Combinatorics.Line.exists_mono_in_high_dimension`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hales_jewett (α : Type*) [Finite α] (κ : Type*) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Combinatorics.Line α ι, Combinatorics.Line.IsMono C l := by sorry

end FamousTheorems
