-- Prove2me | Theorems.Thm_CauchyRiemannIndex_exists_plane_cutoff_family
-- name    : CauchyRiemannIndex.exists_plane_cutoff_family
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T11:49:56.19388+00:00
-- url     : https://prove2.me/theorems/1514ff8b-c6c5-4dc0-9a09-0e8525483852
-- title:
--   A family of smooth cutoffs on ℂ equal to 1 on the disk of radius R with derivative O(1/R)
-- statement:
--   There exist functions $c_R:\mathbb{C}\to\mathbb{C}$ for $R>0$ and a constant $M\ge 0$ such that for every $R>0$:
--   - $c_R$ is smooth (real sense), compactly supported and real-valued;
--   - $c_R(z)=1$ whenever $|z|\le R$;
--   - $\|Dc_R(z)\|\le M/R$ for all $z\in\mathbb{C}$.
--
--   These are the standard cutoff functions used to localise $L^2$ arguments on the plane.
--
--   **Formalization Note** The family is `c : ℝ → ℂ → ℂ`; real-valued is `starRingEnd ℂ (c R z) = c R z`; smooth is `ContDiff ℝ ∞ (c R)`; $\|Dc_R(z)\|$ is the operator norm of `fderiv ℝ (c R) z`. The conditions are only required for `R > 0`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, Proposition 5.20, p. 96 (auxiliary lemma)

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic

namespace CauchyRiemannIndex

open scoped ContDiff

/-- There are a family `c R : ℂ → ℂ` (`R > 0`) of smooth, compactly supported, real-valued
functions and a constant `M ≥ 0` such that `c R = 1` on the closed disk `‖z‖ ≤ R` and the
derivative satisfies `‖D(c R)(z)‖ ≤ M / R` everywhere.

Real-valued is expressed as `conj (c R z) = c R z`; `D` is the real Fréchet derivative. -/
theorem exists_plane_cutoff_family :
    ∃ (c : ℝ → ℂ → ℂ) (M : ℝ), 0 ≤ M ∧ ∀ R > 0,
      ContDiff ℝ ∞ (c R) ∧ HasCompactSupport (c R) ∧
      (∀ z, (starRingEnd ℂ) (c R z) = c R z) ∧
      (∀ z, ‖z‖ ≤ R → c R z = 1) ∧
      (∀ z, ‖fderiv ℝ (c R) z‖ ≤ M / R) := by
  sorry

end CauchyRiemannIndex
