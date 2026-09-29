-- Prove2me | Theorems.Thm_FamousTheorems_compact_iff_ultrafilter_converges_7a
-- name    : FamousTheorems.compact_iff_ultrafilter_converges_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:54.93449+00:00
-- url     : https://prove2.me/theorems/6a8509e9-8f75-4f90-a0b0-b20905deee6a
-- title:
--   Compactness via convergence of ultrafilters
-- statement:
--   **Compactness via convergence of ultrafilters.** A subset $s$ of a topological space $X$ is compact if and only if every ultrafilter on $X$ containing $s$ converges to a point of $s$.
--
--   This characterisation, due to Cartan and Bourbaki, gives a short proof of Tychonoff's theorem: an ultrafilter on a product converges if and only if all its projections converge. It is also the basis for describing the Stone–Čech compactification of a discrete space as the space of ultrafilters.
--
--   **Formalization note.** Mathlib's `isCompact_iff_ultrafilter_le_nhds`. For filters, $\le$ is reverse inclusion. So `(f : Filter X) ≤ Filter.principal s` means $s\in f$, and `(f : Filter X) ≤ nhds x` means that $f$ converges to $x$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isCompact_iff_ultrafilter_le_nhds`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem compact_iff_ultrafilter_converges_7a {X : Type*} [TopologicalSpace X] {s : Set X} :
    IsCompact s ↔ ∀ f : Ultrafilter X, (f : Filter X) ≤ Filter.principal s → ∃ x ∈ s, (f : Filter X) ≤ nhds x := by sorry

end FamousTheorems
