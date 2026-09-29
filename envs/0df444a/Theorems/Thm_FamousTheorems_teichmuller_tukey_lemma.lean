-- Prove2me | Theorems.Thm_FamousTheorems_teichmuller_tukey_lemma
-- name    : FamousTheorems.teichmuller_tukey_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:13.125812+00:00
-- url     : https://prove2.me/theorems/f0b42f7f-b794-4f16-b78c-bb3247f178a1
-- title:
--   The Teichmüller–Tukey lemma
-- statement:
--   **The Teichmüller–Tukey lemma.** Let $\mathcal F$ be a family of subsets of a set $\alpha$ of finite character: a set belongs to $\mathcal F$ if and only if every finite subset of it does. Then every member $x\in\mathcal F$ is contained in a maximal member of $\mathcal F$ (with respect to inclusion).
--
--   This is one of the classical equivalents of the axiom of choice, alongside Zorn's lemma and the well-ordering theorem. It is often the most convenient form in algebra and logic, for example to extend a linearly independent set to a basis or a consistent set of sentences to a maximal consistent one.
--
--   **Formalization note.** Mathlib's `Order.IsOfFiniteCharacter.exists_maximal`. `Order.IsOfFiniteCharacter F` is the finite-character condition, and `Maximal (fun y => y ∈ F) m` says that $m\in\mathcal F$ and no member of $\mathcal F$ strictly contains $m$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Order.IsOfFiniteCharacter.exists_maximal`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem teichmuller_tukey_lemma {α : Type*} {F : Set (Set α)} (hF : Order.IsOfFiniteCharacter F) {x : Set α} (hx : x ∈ F) :
    ∃ m : Set α, x ⊆ m ∧ Maximal (fun y => y ∈ F) m := by sorry

end FamousTheorems
