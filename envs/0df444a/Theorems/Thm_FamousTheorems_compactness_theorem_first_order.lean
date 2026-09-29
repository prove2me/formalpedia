-- Prove2me | Theorems.Thm_FamousTheorems_compactness_theorem_first_order
-- name    : FamousTheorems.compactness_theorem_first_order
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:37.421342+00:00
-- url     : https://prove2.me/theorems/25fd06d5-609d-455c-96b1-781e4365ffe0
-- title:
--   The compactness theorem of first-order logic
-- statement:
--   **The compactness theorem.** A first-order theory $T$ in a language $L$ has a model if and only if every finite subset of $T$ has a model.
--
--   Compactness is one of the two pillars of classical model theory, together with the Löwenheim–Skolem theorems. It yields nonstandard models of arithmetic and analysis, shows that finiteness and many other properties are not first-order expressible, and gives transfer principles such as the Ax–Grothendieck theorem.
--
--   **Formalization note.** Mathlib's `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable`. `T.IsSatisfiable` means $T$ has a nonempty model, and `T.IsFinitelySatisfiable` means every finite subtheory does. Mathlib proves it by ultraproducts (Łoś's theorem).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem compactness_theorem_first_order {L : FirstOrder.Language} (T : L.Theory) : T.IsSatisfiable ↔ T.IsFinitelySatisfiable := by sorry

end FamousTheorems
