-- Prove2me | Theorems.Thm_FamousTheorems_maxchain_spec
-- name    : FamousTheorems.maxchain_spec
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:54:53.783218+00:00
-- url     : https://prove2.me/theorems/72ed0da2-886a-4b86-8cd5-d95962b4eaf0
-- title:
--   Hausdorff's maximality principle
-- statement:
--   **Hausdorff's maximality principle.** Every partially ordered set contains a maximal chain -- a totally ordered subset not properly contained in another. It is equivalent to Zorn's lemma and to the axiom of choice, and it is often the more convenient entry point: one obtains a maximal chain first and then takes its supremum, which is exactly how Zorn's lemma is usually derived from it. Hausdorff published it in 1914, well before Zorn's 1935 paper. **Formalization note.** `maxChain` is the constructed maximal chain and the statement asserts its defining property. The result is Mathlib's `maxChain_spec`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem maxchain_spec :
    ∀ {α : Type u_1} {r : α → α → Prop}, IsMaxChain r (maxChain r) := by sorry

end FamousTheorems
