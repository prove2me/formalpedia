-- Prove2me | Theorems.Thm_DeBruijnNewman_pf_tendsto_limit
-- name    : DeBruijnNewman.pf_tendsto_limit
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-23T18:03:56.071892+00:00
-- url     : https://prove2.me/theorems/9bef10d2-1387-4895-b53f-09b950d612c1
-- title:
--   Pointwise limits of Pólya frequency functions are Pólya frequency
-- statement:
--   Closure of Pólya frequency functions under pointwise limits (Schoenberg 1947): if each K_m is a Pólya frequency function and K_m(x) → Klim(x) for every x, then Klim is a Pólya frequency function. Proof: each minor of Klim is the limit of the corresponding (nonnegative) K_m-minors, using continuity of the determinant; nonnegativity is preserved under limits. Black-box role: the standard approximation step — PF proved on dense/compactly supported approximants passes to the limit kernel, the move de Bruijn's 1950 argument needs to handle the infinite series defining Φ.
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

theorem pf_tendsto_limit
    (K : ℕ → ℝ → ℝ) (Klim : ℝ → ℝ)
    (hPF : ∀ m : ℕ, IsPolyaFrequency (K m))
    (hlim : ∀ x : ℝ, Filter.Tendsto (fun m => K m x) Filter.atTop (nhds (Klim x))) :
    IsPolyaFrequency Klim := by
  sorry

end DeBruijnNewman
