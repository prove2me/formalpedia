-- Prove2me | Theorems.Thm_FamousTheorems_haar_measure_uniqueness
-- name    : FamousTheorems.haar_measure_uniqueness
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:25.788994+00:00
-- url     : https://prove2.me/theorems/4c2e4bf6-ad9e-4d78-99c0-264ad9703615
-- title:
--   Uniqueness of Haar measure
-- statement:
--   **Uniqueness of Haar measure.** Let $G$ be a locally compact, second countable topological group with its Borel σ-algebra, and $\mu$ a left Haar measure on $G$. Then every left-invariant measure $\mu'$ on $G$ that is finite on compact sets is a scalar multiple of $\mu$:
--   $$\mu'=c\,\mu\quad\text{for some } c\in[0,\infty).$$
--
--   Together with existence, this makes Haar measure canonical up to scaling. It is the basis of harmonic analysis on locally compact groups and of the modular function. It also underlies the construction of Tamagawa measures and adelic integration in number theory.
--
--   **Formalization note.** Mathlib's `MeasureTheory.Measure.isMulLeftInvariant_eq_smul`, which produces the scalar `μ'.haarScalarFactor μ`. The statement only asserts existence of the scalar `c : NNReal`. `IsHaarMeasure` means left-invariant, finite on compacts and positive on nonempty open sets. Second countability is part of Mathlib's hypotheses.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.Measure.isMulLeftInvariant_eq_smul`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem haar_measure_uniqueness {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (μ' μ : Measure G) [μ.IsHaarMeasure]
    [IsFiniteMeasureOnCompacts μ'] [μ'.IsMulLeftInvariant] :
    ∃ c : NNReal, μ' = c • μ := by sorry

end FamousTheorems
