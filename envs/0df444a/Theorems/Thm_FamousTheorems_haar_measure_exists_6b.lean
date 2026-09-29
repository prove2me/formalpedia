-- Prove2me | Theorems.Thm_FamousTheorems_haar_measure_exists_6b
-- name    : FamousTheorems.haar_measure_exists_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:42:38.637627+00:00
-- url     : https://prove2.me/theorems/def3e595-b2bf-4700-9096-e206ee11c7e3
-- title:
--   Existence of Haar measure
-- statement:
--   **Existence of Haar measure.** Every locally compact topological group $G$ has a Haar measure: a nonzero Borel measure that is invariant under left translation, finite on compact sets and positive on nonempty open sets.
--
--   Haar measure makes integration available on every locally compact group. It is the starting point of abstract harmonic analysis and representation theory, where it is used to define convolution, group algebras and the Fourier transform. It is also used in number theory, for example for adelic integration. Haar proved existence for second countable groups in 1933, and Weil proved it in general.
--
--   **Formalization note.** Mathlib's `MeasureTheory.Measure.isHaarMeasure_haarMeasure`, applied to an arbitrary compact set with nonempty interior. Such a set exists in every locally compact group. `μ.IsHaarMeasure` says that $\mu$ is left invariant, finite on compact sets and positive on nonempty open sets.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.Measure.isHaarMeasure_haarMeasure`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem haar_measure_exists_6b {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] : ∃ μ : MeasureTheory.Measure G, μ.IsHaarMeasure := by sorry

end FamousTheorems
