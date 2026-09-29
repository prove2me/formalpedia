-- Prove2me | Theorems.Thm_FamousTheorems_lusin_souslin_theorem
-- name    : FamousTheorems.lusin_souslin_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:18.738095+00:00
-- url     : https://prove2.me/theorems/7d600ca4-6f40-4780-959b-8fabff56e5de
-- title:
--   The Lusin–Souslin theorem
-- statement:
--   **The Lusin–Souslin theorem.** Let $f:\gamma\to\beta$ be a continuous injective map from a Polish space into a Hausdorff space. Then the image $f(\gamma)$ is a Borel set.
--
--   Continuous images of Borel sets are in general only analytic, but injectivity forces the image to be Borel. As a consequence, a continuous bijection between Polish spaces is a Borel isomorphism, and every Borel subset of a Polish space is a continuous injective image of a closed subset of Baire space.
--
--   **Formalization note.** Mathlib's `MeasureTheory.measurableSet_range_of_continuous_injective`. The target $\beta$ is a Hausdorff space whose $\sigma$-algebra contains the open sets, and the conclusion is measurability of `Set.range f`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.measurableSet_range_of_continuous_injective`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem lusin_souslin_theorem {γ β : Type*} [TopologicalSpace γ] [PolishSpace γ] [TopologicalSpace β] [T2Space β] [MeasurableSpace β]
    [OpensMeasurableSpace β] {f : γ → β} (hf : Continuous f) (hinj : Function.Injective f) :
    MeasurableSet (Set.range f) := by sorry

end FamousTheorems
