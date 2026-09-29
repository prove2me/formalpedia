-- Prove2me | Theorems.Thm_FamousTheorems_continuous_mapping_theorem
-- name    : FamousTheorems.continuous_mapping_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:21.0555+00:00
-- url     : https://prove2.me/theorems/c4ea1b54-b8a8-4a0e-9f3b-8aefab5b31e9
-- title:
--   The continuous mapping theorem
-- statement:
--   **The continuous mapping theorem.** If random variables $X_n$ converge in distribution to $Z$ and $g$ is continuous, then $g(X_n)$ converges in distribution to $g(Z)$.
--
--   It is one of the most used tools of asymptotic statistics. Combined with the central limit theorem and Slutsky's theorem it gives the limiting distributions of test statistics, such as $\chi^2$ limits of squared normal statistics.
--
--   **Formalization note.** Mathlib's `MeasureTheory.TendstoInDistribution.continuous_comp`. The variables $X_i$ may live on different probability spaces `Ω i`, convergence is along an arbitrary filter `l`, and `TendstoInDistribution X l Z μ μ'` means the laws converge weakly as probability measures on `E`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.TendstoInDistribution.continuous_comp`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem continuous_mapping_theorem {ι E Ω' F : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)} {μ : ∀ i, MeasureTheory.Measure (Ω i)}
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)] {m' : MeasurableSpace Ω'} {μ' : MeasureTheory.Measure Ω'}
    [MeasureTheory.IsProbabilityMeasure μ'] {mE : MeasurableSpace E} {X : ∀ i, Ω i → E} {Z : Ω' → E}
    {l : Filter ι} [TopologicalSpace E] [OpensMeasurableSpace E] [TopologicalSpace F] [MeasurableSpace F]
    [BorelSpace F] {g : E → F} (hg : Continuous g) (h : MeasureTheory.TendstoInDistribution X l Z μ μ') :
    MeasureTheory.TendstoInDistribution (fun n => g ∘ X n) l (g ∘ Z) μ μ' := by sorry

end FamousTheorems
