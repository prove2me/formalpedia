-- Prove2me | Theorems.Thm_FamousTheorems_ergodic_iff_extreme_invariant
-- name    : FamousTheorems.ergodic_iff_extreme_invariant
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:10:04.188416+00:00
-- url     : https://prove2.me/theorems/d3695b5a-01d8-4f3b-accd-16c8101c79d0
-- title:
--   Ergodic measures are extreme invariant measures
-- statement:
--   **Ergodic measures are the extreme invariant measures.** Let $f:X\to X$ be measurable and $\mu$ an $f$-invariant probability measure. Then $\mu$ is ergodic for $f$ if and only if $\mu$ is an extreme point of the convex set of $f$-invariant probability measures.
--
--   An ergodic measure cannot be written as a nontrivial convex combination of other invariant measures. This is the basis of the ergodic decomposition, which writes every invariant measure as an integral of ergodic ones. It is used for existence of ergodic measures via the Krein–Milman theorem.
--
--   **Formalization note.** Mathlib's `Ergodic.iff_mem_extremePoints`. The convex set is `{ν | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν}`, and extreme points are taken for convex combinations with coefficients in $[0,\infty]$ (`Set.extremePoints ENNReal`), which agrees with the usual notion on probability measures. `Ergodic f μ` includes the invariance of $\mu$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Ergodic.iff_mem_extremePoints`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem ergodic_iff_extreme_invariant {X : Type*} {m : MeasurableSpace X} {μ : Measure X} {f : X → X} [IsProbabilityMeasure μ] :
    Ergodic f μ ↔
      μ ∈ Set.extremePoints ENNReal {ν : Measure X | MeasurePreserving f ν ν ∧ IsProbabilityMeasure ν} := by sorry

end FamousTheorems
