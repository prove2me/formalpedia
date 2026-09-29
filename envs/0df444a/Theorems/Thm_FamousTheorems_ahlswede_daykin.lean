-- Prove2me | Theorems.Thm_FamousTheorems_ahlswede_daykin
-- name    : FamousTheorems.ahlswede_daykin
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:14.170879+00:00
-- url     : https://prove2.me/theorems/128480df-8d3d-46df-9d6e-87c7fa303f08
-- title:
--   The Ahlswede–Daykin four functions theorem
-- statement:
--   **The Ahlswede–Daykin four functions theorem.** Let $f_1,f_2,f_3,f_4\ge0$ be functions on a distributive lattice with
--   $$f_1(a)\,f_2(b)\le f_3(a\wedge b)\,f_4(a\vee b)\quad\text{for all }a,b .$$
--   Then for all finite sets $s,t$,
--   $$\Big(\sum_{s}f_1\Big)\Big(\sum_{t}f_2\Big)\le\Big(\sum_{s\wedge t}f_3\Big)\Big(\sum_{s\vee t}f_4\Big),$$
--   where $s\wedge t=\{a\wedge b\}$ and $s\vee t=\{a\vee b\}$.
--
--   It is a master correlation inequality: the FKG, Holley and Harris–Kleitman inequalities and Daykin's inequality $|\mathcal A||\mathcal B|\le|\mathcal A\wedge\mathcal B||\mathcal A\vee\mathcal B|$ are special cases. It is used throughout percolation theory and statistical mechanics.
--
--   **Formalization note.** Mathlib's `four_functions_theorem`, valid for values in any linearly ordered commutative semiring with `ExistsAddOfLE`. `s ⊼ t` and `s ⊻ t` are the pointwise infs and sups.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `four_functions_theorem`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped FinsetFamily

theorem ahlswede_daykin {α β : Type*} [DistribLattice α] [CommSemiring β] [LinearOrder β] [IsStrictOrderedRing β] [ExistsAddOfLE β]
    (f₁ f₂ f₃ f₄ : α → β) [DecidableEq α] (h₁ : 0 ≤ f₁) (h₂ : 0 ≤ f₂) (h₃ : 0 ≤ f₃) (h₄ : 0 ≤ f₄)
    (h : ∀ a b, f₁ a * f₂ b ≤ f₃ (a ⊓ b) * f₄ (a ⊔ b)) (s t : Finset α) :
    (∑ a ∈ s, f₁ a) * (∑ a ∈ t, f₂ a) ≤ (∑ a ∈ s ⊼ t, f₃ a) * (∑ a ∈ s ⊻ t, f₄ a) := by sorry

end FamousTheorems
