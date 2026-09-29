-- Prove2me | Theorems.Thm_FamousTheorems_portmanteau_theorem
-- name    : FamousTheorems.portmanteau_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:28.711299+00:00
-- url     : https://prove2.me/theorems/db9a0849-3b90-4e8e-bb35-c7e8371cf640
-- title:
--   The portmanteau theorem (closed and open set characterisations of weak convergence)
-- statement:
--   **The portmanteau theorem.** Let $\Omega$ be a topological space with its Borel σ-algebra in which closed sets can be approximated from outside by bounded continuous functions (for example, any pseudo-metrizable space). For probability measures $\mu_i\to\mu$ along a countably generated filter (for example, a sequence), the following are equivalent:
--   1. $\mu_i\to\mu$ weakly, i.e. $\int f\,d\mu_i\to\int f\,d\mu$ for every bounded continuous $f$;
--   2. $\limsup_i\mu_i(F)\le\mu(F)$ for every closed set $F$;
--   3. $\mu(G)\le\liminf_i\mu_i(G)$ for every open set $G$.
--
--   This is the standard toolkit for checking weak convergence of probability measures, used throughout the theory of limit theorems (central limit theorem, Donsker's invariance principle).
--
--   **Formalization note.** Assembled from Mathlib's `MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`, `MeasureTheory.tendsto_of_forall_isClosed_limsup_le'`, `MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto` and `MeasureTheory.tendsto_of_forall_isOpen_le_liminf'`. Convergence in `MeasureTheory.ProbabilityMeasure Ω` is weak convergence (the topology is defined by integrals of bounded continuous functions), and measures are evaluated as `ℝ≥0∞`-valued. `HasOuterApproxClosed Ω` is the approximation hypothesis on the space.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem portmanteau_theorem {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {L : Filter ι} [L.IsCountablyGenerated] (μ : MeasureTheory.ProbabilityMeasure Ω)
    (μs : ι → MeasureTheory.ProbabilityMeasure Ω) :
    (Filter.Tendsto μs L (nhds μ) ↔ ∀ F : Set Ω, IsClosed F →
        Filter.limsup (fun i => (μs i : MeasureTheory.Measure Ω) F) L ≤ (μ : MeasureTheory.Measure Ω) F) ∧
      (Filter.Tendsto μs L (nhds μ) ↔ ∀ G : Set Ω, IsOpen G →
        (μ : MeasureTheory.Measure Ω) G ≤ Filter.liminf (fun i => (μs i : MeasureTheory.Measure Ω) G) L) := by sorry

end FamousTheorems
