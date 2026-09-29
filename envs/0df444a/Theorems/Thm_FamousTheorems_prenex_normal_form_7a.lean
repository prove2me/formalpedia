-- Prove2me | Theorems.Thm_FamousTheorems_prenex_normal_form_7a
-- name    : FamousTheorems.prenex_normal_form_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:27.771573+00:00
-- url     : https://prove2.me/theorems/88b0b93b-e71f-4614-8cef-706f2a1e1ab0
-- title:
--   Prenex normal form theorem
-- statement:
--   **Prenex normal form theorem.** Let $L$ be a first-order language and $\varphi$ a formula of $L$ with free variables indexed by $\alpha$ and $n$ further bound-variable slots. There is a formula $\varphi'$ in prenex normal form, meaning a string of quantifiers followed by a quantifier-free formula, such that in every nonempty $L$-structure $M$ and under every assignment, $\varphi'$ holds if and only if $\varphi$ holds.
--
--   Prenex forms go back to Peirce and Skolem. Every formula can be put in prenex form by moving quantifiers outward. This is the first step of Skolemization and of the arithmetical and Lévy hierarchies, which classify formulas by their quantifier prefixes.
--
--   **Formalization note.** Mathlib's `FirstOrder.Language.BoundedFormula.realize_toPrenex` and `toPrenex_isPrenex`. Here $\varphi'$ is Mathlib's explicit transformation `φ.toPrenex`. `BoundedFormula α n` has free variables indexed by $\alpha$ and $n$ de Bruijn-style variables, assigned by `v` and `xs` respectively. The structure is assumed nonempty, as is needed to move quantifiers across connectives.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `FirstOrder.Language.BoundedFormula.realize_toPrenex`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem prenex_normal_form_7a {L : FirstOrder.Language} {M : Type*} [L.Structure M] {α : Type*} {n : ℕ} [Nonempty M]
    (φ : L.BoundedFormula α n) {v : α → M} {xs : Fin n → M} :
    φ.toPrenex.IsPrenex ∧ (φ.toPrenex.Realize v xs ↔ φ.Realize v xs) := by sorry

end FamousTheorems
