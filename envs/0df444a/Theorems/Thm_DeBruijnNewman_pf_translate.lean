-- Prove2me | Theorems.Thm_DeBruijnNewman_pf_translate
-- name    : DeBruijnNewman.pf_translate
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-23T18:03:32.311425+00:00
-- url     : https://prove2.me/theorems/506b8682-d23a-450c-8a77-83a6dbcaaaaa
-- title:
--   Pólya frequency functions are closed under translation
-- statement:
--   Closure of Pólya frequency functions under translation (Schoenberg 1947): if K is a Pólya frequency function then so is x ↦ K(x − c) for every shift c. Proof: the minor entries K((x_i − c) − y_j) equal K(x_i − (y_j + c)), and shifting the y-nodes preserves strict increase, so the minor is a minor of K. Black-box role: recentering kernels (e.g. symmetrization arguments in de Bruijn's 1950 base case) stays inside the PF class.
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

theorem pf_translate
    (K : ℝ → ℝ) (c : ℝ)
    (hK : IsPolyaFrequency K) :
    IsPolyaFrequency (fun x => K (x - c)) := by
  sorry

end DeBruijnNewman
