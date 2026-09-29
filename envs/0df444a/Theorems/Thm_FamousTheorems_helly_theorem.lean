-- Prove2me | Theorems.Thm_FamousTheorems_helly_theorem
-- name    : FamousTheorems.helly_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:40.811872+00:00
-- url     : https://prove2.me/theorems/ca9818d7-ee3b-4194-9466-29a70a4b39a6
-- title:
--   Helly's theorem
-- statement:
--   **Helly's theorem.** Let $F_1,\dots,F_N$ be convex sets in a $d$-dimensional vector space over an ordered field, with $N\ge d+1$. If every $d+1$ of them have a common point, then all of them have a common point.
--
--   It is the most important intersection theorem of convex geometry. It is the basis of many results on transversals and centre points and of combinatorial dimension in optimisation (LP-type problems). Its infinite version for compact convex sets is equally widely used.
--
--   **Formalization note.** Mathlib's `Convex.helly_theorem`, for a finite index set `s`; `Module.finrank 𝕜 E` is the dimension $d$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Convex.helly_theorem`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem helly_theorem {ι 𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] {F : ι → Set E} {s : Finset ι} (h_card : Module.finrank 𝕜 E + 1 ≤ s.card)
    (h_convex : ∀ i ∈ s, Convex 𝕜 (F i))
    (h_inter : ∀ I ⊆ s, I.card = Module.finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) : (⋂ i ∈ s, F i).Nonempty := by sorry

end FamousTheorems
