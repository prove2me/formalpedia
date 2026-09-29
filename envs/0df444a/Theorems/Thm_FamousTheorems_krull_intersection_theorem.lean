-- Prove2me | Theorems.Thm_FamousTheorems_krull_intersection_theorem
-- name    : FamousTheorems.krull_intersection_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:45.532058+00:00
-- url     : https://prove2.me/theorems/50b0c97f-2d0c-4119-a739-3b88e17f4664
-- title:
--   Krull's intersection theorem (local rings)
-- statement:
--   **Krull's intersection theorem (local case).** Let $R$ be a Noetherian local ring and $I\ne R$ a proper ideal. Then
--   $$\bigcap_{n\ge0}I^n=0.$$
--
--   So the $I$-adic topology on a Noetherian local ring is Hausdorff, and elements of $R$ are determined by their images in the quotients $R/I^n$. This is fundamental for completions in commutative algebra and algebraic geometry. For example, it shows that a Noetherian local ring embeds in its completion.
--
--   **Formalization note.** Mathlib's `Ideal.iInf_pow_eq_bot_of_isLocalRing`. The intersection is the infimum `⨅ i : ℕ, I ^ i` in the lattice of ideals and `⊥` is the zero ideal. Mathlib also has the version for Noetherian domains, `Ideal.iInf_pow_eq_bot_of_isDomain`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Ideal.iInf_pow_eq_bot_of_isLocalRing`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem krull_intersection_theorem {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ⨅ i : ℕ, I ^ i = ⊥ := by sorry

end FamousTheorems
