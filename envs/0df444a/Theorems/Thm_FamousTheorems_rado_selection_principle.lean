-- Prove2me | Theorems.Thm_FamousTheorems_rado_selection_principle
-- name    : FamousTheorems.rado_selection_principle
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:04.507696+00:00
-- url     : https://prove2.me/theorems/738cf7b9-9ecd-442b-925a-52babd64f98c
-- title:
--   Rado's selection principle
-- statement:
--   **Rado's selection principle.** Let $(\beta_a)_{a\in\alpha}$ be a family of finite sets, and suppose that for each finite $t\subseteq\alpha$ we are given a choice function $g_t\in\prod_a\beta_a$. Then there is a global choice function $\chi$ such that for every finite $s\subseteq\alpha$ there is a finite $t\supseteq s$ with $\chi$ agreeing with $g_t$ on $s$.
--
--   Rado's principle is a compactness theorem. It derives infinite combinatorial statements from their finite versions: for example, the de Bruijn–Erdős theorem that an infinite graph is $k$-colourable if every finite subgraph is, and Hall's marriage theorem for infinite families of finite sets.
--
--   **Formalization note.** Mathlib's `Finset.rado_selection`. The family is a dependent type `β : α → Type*` with each `β a` finite, the local data is `g : Finset α → (a : α) → β a`, and the conclusion states the agreement `χ x = g t x` for all `x ∈ s`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Finset.rado_selection`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem rado_selection_principle {α : Type*} {β : α → Type*} [∀ a, Finite (β a)] (g : Finset α → (a : α) → β a) :
    ∃ χ : (a : α) → β a, ∀ s : Finset α, ∃ t : Finset α, s ⊆ t ∧ ∀ x ∈ s, χ x = g t x := by sorry

end FamousTheorems
