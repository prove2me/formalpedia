-- Prove2me | Theorems.Thm_DeBruijnNewman_pf_smul_nonneg
-- name    : DeBruijnNewman.pf_smul_nonneg
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-23T18:03:14.394012+00:00
-- url     : https://prove2.me/theorems/b4804b17-fe78-40d7-b821-84be3f784fb0
-- title:
--   Pólya frequency functions are closed under nonnegative scalar multiples
-- statement:
--   Closure of Pólya frequency functions under nonnegative scalar multiples (I. J. Schoenberg, 1947, "On totally positive functions, distributions and Fourier transforms"): if K is a Pólya frequency function and a ≥ 0, then x ↦ a·K(x) is a Pólya frequency function. The proof is one determinant computation: the minor of the scaled kernel is a^n times the minor of K (Matrix.det_smul), hence nonnegative. Black-box role: lets later assembly scale PF kernels (e.g. normalizing the de Bruijn kernel) without leaving the PF class.
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

theorem pf_smul_nonneg
    (K : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hK : IsPolyaFrequency K) :
    IsPolyaFrequency (fun x => a * K x) := by
  sorry

end DeBruijnNewman
