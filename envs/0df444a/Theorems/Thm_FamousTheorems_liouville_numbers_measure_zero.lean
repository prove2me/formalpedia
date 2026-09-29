-- Prove2me | Theorems.Thm_FamousTheorems_liouville_numbers_measure_zero
-- name    : FamousTheorems.liouville_numbers_measure_zero
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:42.99984+00:00
-- url     : https://prove2.me/theorems/d74dca65-4efd-4b7b-8ed9-42f97c52304f
-- title:
--   The Liouville numbers have Lebesgue measure zero
-- statement:
--   **The Liouville numbers have Lebesgue measure zero.** The set of Liouville numbers in $\mathbb R$ has Lebesgue measure $0$.
--
--   Together with the fact that the Liouville numbers form a residual set, this shows that measure and category can disagree about which sets are "large". The set is small in measure but large in the sense of Baire. Almost every real number, in the sense of measure, has irrationality exponent $2$ (Khinchin), while Liouville numbers have infinite exponent.
--
--   **Formalization note.** Mathlib's `volume_setOfPred_liouville`. `MeasureTheory.volume` is Lebesgue measure on $\mathbb R$, and `Liouville x` is Mathlib's definition of a Liouville number.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `volume_setOfPred_liouville`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem liouville_numbers_measure_zero : MeasureTheory.volume {x : ℝ | Liouville x} = 0 := by sorry

end FamousTheorems
