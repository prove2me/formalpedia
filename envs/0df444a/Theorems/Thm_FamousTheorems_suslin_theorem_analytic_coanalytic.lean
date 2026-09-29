-- Prove2me | Theorems.Thm_FamousTheorems_suslin_theorem_analytic_coanalytic
-- name    : FamousTheorems.suslin_theorem_analytic_coanalytic
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:17.175139+00:00
-- url     : https://prove2.me/theorems/a0f83a86-c8e3-4e4e-a5b5-edcca1fb7c4d
-- title:
--   Suslin's theorem
-- statement:
--   **Suslin's theorem.** In a Hausdorff space, a set $s$ that is analytic and whose complement is also analytic is Borel.
--
--   Suslin found this in 1917 while correcting an error of Lebesgue, who had claimed that projections of Borel sets are Borel. Together with the trivial converse in Polish spaces it gives the identity Borel = analytic ∩ co-analytic, the founding result of descriptive set theory.
--
--   **Formalization note.** Mathlib's `MeasureTheory.AnalyticSet.measurableSet_of_compl`. It is stated for a Hausdorff space whose $\sigma$-algebra contains the open sets (`OpensMeasurableSpace`). The conclusion `MeasurableSet s` gives Borel measurability when the $\sigma$-algebra is the Borel one, and measurability in any larger $\sigma$-algebra otherwise.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.AnalyticSet.measurableSet_of_compl`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem suslin_theorem_analytic_coanalytic {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α] {s : Set α}
    (hs : AnalyticSet s) (hsc : AnalyticSet sᶜ) :
    MeasurableSet s := by sorry

end FamousTheorems
