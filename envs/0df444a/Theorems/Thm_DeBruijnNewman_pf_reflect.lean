-- Prove2me | Theorems.Thm_DeBruijnNewman_pf_reflect
-- name    : DeBruijnNewman.pf_reflect
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-23T18:03:51.588017+00:00
-- url     : https://prove2.me/theorems/e207376c-65e8-432d-8cf1-3fa3a304b8c5
-- title:
--   Pólya frequency functions are closed under reflection
-- statement:
--   Closure of Pólya frequency functions under reflection (Schoenberg 1947): if K is a Pólya frequency function then so is x ↦ K(−x). Proof: reversing both node families (i ↦ n−1−i) turns the reflected minor into a genuine K-minor on the reversed, still strictly increasing nodes; the two reversals contribute sign (−1)^(n(n−1)/2) twice, i.e. +1. Black-box role: even/odd symmetrization of kernels (de Bruijn's kernel is even) stays inside the PF class.
-- source:
--   Decomposition of DeBruijnNewman.schoenberg_polya_fourier_real_zeros (626a294b-1b0a-43b9-aebe-aef9f7c9a57a), Prove2Me The de Bruijn-Newman Constant is Non-negative mission

import Mathlib

namespace DeBruijnNewman

/-- A function `K : ℝ → ℝ` is a Pólya frequency function if the translation
kernel `(x, y) ↦ K (x - y)` is totally positive of every order: every
finite minor formed on strictly increasing nodes is nonnegative. -/
def IsPolyaFrequency (K : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x y : Fin n → ℝ),
    (∀ i j : Fin n, i < j → x i < x j) →
    (∀ i j : Fin n, i < j → y i < y j) →
    0 ≤ (Matrix.of fun i j => K (x i - y j)).det

end DeBruijnNewman

namespace DeBruijnNewman

theorem pf_reflect
    (K : ℝ → ℝ)
    (hK : IsPolyaFrequency K) :
    IsPolyaFrequency (fun x => K (-x)) := by
  sorry

end DeBruijnNewman
