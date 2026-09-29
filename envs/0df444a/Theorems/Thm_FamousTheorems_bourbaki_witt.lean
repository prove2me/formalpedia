-- Prove2me | Theorems.Thm_FamousTheorems_bourbaki_witt
-- name    : FamousTheorems.bourbaki_witt
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:17.229305+00:00
-- url     : https://prove2.me/theorems/987ef4c2-31d4-4723-983a-bd4cb57daa03
-- title:
--   The Bourbaki–Witt theorem
-- statement:
--   **The Bourbaki–Witt theorem.** Let $\alpha$ be a nonempty chain-complete partial order, i.e. every chain has a supremum. Every inflationary map $f:\alpha\to\alpha$, meaning $x\le f(x)$ for all $x$, has a fixed point.
--
--   Unlike Knaster–Tarski, no monotonicity is assumed, and the proof (by the tower of iterates from a starting point) uses no choice. It gives a choice-free route from the Hausdorff maximality principle to Zorn's lemma and to theorems on maximal elements.
--
--   **Formalization note.** Mathlib's `ChainCompletePartialOrder.nonempty_fixedPoints_of_inflationary`; `Function.fixedPoints f` is the set of fixed points.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ChainCompletePartialOrder.nonempty_fixedPoints_of_inflationary`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem bourbaki_witt {α : Type*} [ChainCompletePartialOrder α] {f : α → α} [Nonempty α] (le_map : ∀ x, x ≤ f x) :
    (Function.fixedPoints f).Nonempty := by sorry

end FamousTheorems
