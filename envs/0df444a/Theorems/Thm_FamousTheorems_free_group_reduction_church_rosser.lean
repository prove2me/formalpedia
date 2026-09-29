-- Prove2me | Theorems.Thm_FamousTheorems_free_group_reduction_church_rosser
-- name    : FamousTheorems.free_group_reduction_church_rosser
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:21:54.707901+00:00
-- url     : https://prove2.me/theorems/62d27a32-e3e3-4cc2-b784-260173ed9f46
-- title:
--   The Church–Rosser theorem for free groups
-- statement:
--   **The Church–Rosser theorem for free groups.** Consider words over the alphabet $\alpha\times\{\pm1\}$, and let $L\to L'$ mean that $L'$ is obtained from $L$ by a finite sequence of deletions of adjacent inverse pairs $x^{\varepsilon}x^{-\varepsilon}$. If $L_1\to L_2$ and $L_1\to L_3$, then there is a word $L_4$ with $L_2\to L_4$ and $L_3\to L_4$.
--
--   The confluence of free reduction implies that every word has a unique reduced form. This gives the normal form for elements of a free group and solves its word problem.
--
--   **Formalization note.** Mathlib's `FreeGroup.Red.church_rosser`. Words are `List (α × Bool)`, `FreeGroup.Red` is the reflexive-transitive closure of one-step reduction, and `Relation.Join FreeGroup.Red L₂ L₃` says that $L_2$ and $L_3$ reduce to a common word.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `FreeGroup.Red.church_rosser`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem free_group_reduction_church_rosser {α : Type*} {L₁ L₂ L₃ : List (α × Bool)} (h₁₂ : FreeGroup.Red L₁ L₂) (h₁₃ : FreeGroup.Red L₁ L₃) :
    Relation.Join FreeGroup.Red L₂ L₃ := by sorry

end FamousTheorems
