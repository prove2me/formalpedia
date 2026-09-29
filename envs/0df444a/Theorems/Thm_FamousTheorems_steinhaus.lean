-- Prove2me | Theorems.Thm_FamousTheorems_steinhaus
-- name    : FamousTheorems.steinhaus
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:23.237965+00:00
-- url     : https://prove2.me/theorems/75293b76-10b7-405a-96d1-9c29bd077ce1
-- title:
--   Steinhaus's theorem
-- statement:
--   **Steinhaus's theorem.** In a locally compact topological group with an inner regular Haar measure $\mu$, if $E$ is measurable with $\mu(E)>0$ then $E\,E^{-1}=\{xy^{-1}:x,y\in E\}$ is a neighbourhood of the identity.
--
--   For $\mathbb R$ it says $E-E$ contains an interval around $0$ whenever $E$ has positive Lebesgue measure. Consequences include automatic continuity of measurable homomorphisms: every measurable additive $f:\mathbb R\to\mathbb R$ is linear.
--
--   **Formalization note.** Mathlib's `MeasureTheory.Measure.div_mem_nhds_one_of_haar_pos`, written multiplicatively as `E / E ∈ 𝓝 1` using pointwise division of sets.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.Measure.div_mem_nhds_one_of_haar_pos`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped Pointwise

theorem steinhaus {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] [LocallyCompactSpace G] [μ.InnerRegular] (E : Set G)
    (hE : MeasurableSet E) (hEpos : 0 < μ E) : E / E ∈ nhds (1 : G) := by sorry

end FamousTheorems
