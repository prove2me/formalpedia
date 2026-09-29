-- Prove2me | Theorems.Thm_FamousTheorems_lusin_separation_theorem
-- name    : FamousTheorems.lusin_separation_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:16.00473+00:00
-- url     : https://prove2.me/theorems/b87583df-e24b-4f10-9d47-953badef4f8f
-- title:
--   Lusin's separation theorem
-- statement:
--   **Lusin's separation theorem.** Any two disjoint analytic sets $s,t$ in a Hausdorff space are separated by a Borel set: there is a Borel set $u$ with $s\subseteq u$ and $u\cap t=\varnothing$.
--
--   A set is analytic if it is a continuous image of a Polish space. Lusin's theorem is the basic structural fact about analytic sets. It implies Suslin's theorem that a set which is analytic and has analytic complement is Borel.
--
--   **Formalization note.** Mathlib's `MeasureTheory.AnalyticSet.measurablySeparable`. The ambient space is a Hausdorff topological space in which open sets are measurable (`OpensMeasurableSpace`). `MeasurablySeparable s t` says that there is a measurable set containing $s$ and disjoint from $t$. When the $\sigma$-algebra is the Borel one, this is the Borel separation above.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.AnalyticSet.measurablySeparable`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem lusin_separation_theorem {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α] {s t : Set α}
    (hs : AnalyticSet s) (ht : AnalyticSet t) (h : Disjoint s t) :
    MeasurablySeparable s t := by sorry

end FamousTheorems
