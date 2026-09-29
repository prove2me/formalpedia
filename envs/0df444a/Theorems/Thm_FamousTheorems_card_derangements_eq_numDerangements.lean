-- Prove2me | Theorems.Thm_FamousTheorems_card_derangements_eq_numDerangements
-- name    : FamousTheorems.card_derangements_eq_numDerangements
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:17:11.109986+00:00
-- url     : https://prove2.me/theorems/7922e656-2624-4a0d-81d9-af47cc6b69cd
-- title:
--   The derangements formula
-- statement:
--   **Counting permutations with no fixed point.**
--
--   The number of derangements of an $n$-element set — permutations leaving nothing in place — is
--   $$D_n \;=\; n!\sum_{k=0}^{n}\frac{(-1)^k}{k!},$$
--   equivalently the nearest integer to $n!/e$.
--
--   Inclusion–exclusion over the fixed points gives the alternating sum directly. The striking
--   consequence is that the *proportion* of derangements tends to $1/e \approx 0.368$ and does so
--   extremely fast — so in the hat-check problem, the chance nobody gets their own hat back is
--   essentially independent of the number of people.
--
--   Studied by Pierre de Montmort in 1708 as the *problème des rencontres*, and one of the founding
--   problems of enumerative combinatorics.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem card_derangements_eq_numDerangements : ∀ (α : Type*) [Fintype α] [DecidableEq α],
    Fintype.card (derangements α) = numDerangements (Fintype.card α) := by sorry

end FamousTheorems
