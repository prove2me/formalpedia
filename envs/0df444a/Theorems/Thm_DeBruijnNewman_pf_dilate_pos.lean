-- Prove2me | Theorems.Thm_DeBruijnNewman_pf_dilate_pos
-- name    : DeBruijnNewman.pf_dilate_pos
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-23T18:03:44.141584+00:00
-- url     : https://prove2.me/theorems/c0bc943c-42bd-409b-9e7c-57f403c6cb4a
-- title:
--   Pólya frequency functions are closed under positive dilation
-- statement:
--   Closure of Pólya frequency functions under positive dilation (Schoenberg 1947): if K is a Pólya frequency function and c > 0, then x ↦ K(c·x) is a Pólya frequency function. Proof: the minor entries K(c·x_i − c·y_j) are the entries of a K-minor on the rescaled nodes c·x_i, c·y_j, which stay strictly increasing since c > 0. Black-box role: rescaling the argument (e.g. normalizing the width of the Gaussian factor in de Bruijn's kernel) stays inside the PF class.
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

theorem pf_dilate_pos
    (K : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hK : IsPolyaFrequency K) :
    IsPolyaFrequency (fun x => K (c * x)) := by
  sorry

end DeBruijnNewman
