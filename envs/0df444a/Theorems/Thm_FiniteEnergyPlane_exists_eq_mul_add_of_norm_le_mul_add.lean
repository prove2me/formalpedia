-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_eq_mul_add_of_norm_le_mul_add
-- name    : FiniteEnergyPlane.exists_eq_mul_add_of_norm_le_mul_add
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T09:58:49.005534+00:00
-- url     : https://prove2.me/theorems/6d081658-2663-4026-8209-b8e173c19892
-- title:
--   Entire functions of at most linear growth are affine
-- statement:
--   Let $f:\mathbb{C}\to\mathbb{C}$ be an entire function and suppose there are constants $C,K\in\mathbb{R}$ with $|f(z)|\le C|z|+K$ for all $z\in\mathbb{C}$. Then there are $A,B\in\mathbb{C}$ with $f(z)=Az+B$ for all $z$.
--
--   Role: a generalized Liouville theorem for maps of at most linear growth. It identifies a holomorphic reparametrization $\mathbb{C}\to\mathbb{C}$ between two finite-energy planes as an affine map, as in Hryniewicz's Lemma 6.25.
--
--   **Formalization Note** "Entire" is `Differentiable ℂ f`. No sign condition is put on $C$ or $K$.
-- source:
--   Classical (generalized Liouville theorem); used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.25

import Mathlib

namespace FiniteEnergyPlane

open Metric

/-- An entire function of at most linear growth is affine: if `f : ℂ → ℂ` is complex
differentiable and `‖f z‖ ≤ C ‖z‖ + K` for all `z`, then `f z = A z + B` for some `A, B ∈ ℂ`. -/
theorem exists_eq_mul_add_of_norm_le_mul_add (f : ℂ → ℂ) (hf : Differentiable ℂ f) (C K : ℝ)
    (hb : ∀ z, ‖f z‖ ≤ C * ‖z‖ + K) : ∃ A B : ℂ, ∀ z, f z = A * z + B := by
  sorry

end FiniteEnergyPlane
