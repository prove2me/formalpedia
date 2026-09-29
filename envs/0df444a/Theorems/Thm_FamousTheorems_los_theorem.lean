-- Prove2me | Theorems.Thm_FamousTheorems_los_theorem
-- name    : FamousTheorems.los_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:29.731055+00:00
-- url     : https://prove2.me/theorems/91e53c78-31ff-49fe-9773-4b4d0c352719
-- title:
--   Łoś's theorem for ultraproducts
-- statement:
--   **Łoś's theorem.** Let $(M_a)_{a\in\alpha}$ be nonempty $L$-structures and $\mathcal U$ an ultrafilter on $\alpha$. A first-order sentence $\varphi$ holds in the ultraproduct $\prod_{\mathcal U}M_a$ if and only if $\{a : M_a\models\varphi\}\in\mathcal U$.
--
--   This is the fundamental theorem of ultraproducts. It gives a one-line proof of the compactness theorem, constructs nonstandard models (hyperreals, nonstandard arithmetic), and transfers first-order properties between structures, as in the Ax–Kochen and Ax–Grothendieck theorems.
--
--   **Formalization note.** Mathlib's `FirstOrder.Language.Ultraproduct.sentence_realize`; `(u : Filter α).Product M` is the ultraproduct structure.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `FirstOrder.Language.Ultraproduct.sentence_realize`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open FirstOrder FirstOrder.Language

theorem los_theorem {α : Type*} {M : α → Type*} {u : Ultrafilter α} {L : Language} [∀ a, L.Structure (M a)]
    [∀ a, Nonempty (M a)] (φ : L.Sentence) :
    (u : Filter α).Product M ⊨ φ ↔ ∀ᶠ a in (u : Filter α), M a ⊨ φ := by sorry

end FamousTheorems
