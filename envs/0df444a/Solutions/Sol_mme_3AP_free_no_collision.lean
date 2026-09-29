-- Prove2me | solution 1 for mme_3AP_free_no_collision
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T17:51:57.135625+00:00
-- url     : https://prove2.me/submissions/5ac70b60-5403-49fd-8391-f146468cfc8a

import Mathlib.Combinatorics.Additive.AP.Three.Defs

theorem solution {n : ℕ}
    (S : Finset ℕ) (hS : ThreeAPFree (S : Set ℕ))
    (I J K : Fin n → ℕ)
    (hI : ∀ i, I i ∈ S) (hJ : ∀ i, J i ∈ S) (hK : ∀ i, K i ∈ S)
    (h : ∀ i, I i + K i = 2 * J i) :
    I = K := by
  funext i
  have hIi : I i ∈ (S : Set ℕ) := hI i
  have hJi : J i ∈ (S : Set ℕ) := hJ i
  have hKi : K i ∈ (S : Set ℕ) := hK i
  have hi := h i
  have heq : I i + K i = J i + J i := by omega
  have h1 : I i = J i := hS hIi hJi hKi heq
  omega
