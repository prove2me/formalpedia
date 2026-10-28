-- Prove2me | Theorems.Thm_Brouwer_det_fderiv_eq_zero_of_norm_eq_one
-- name    : Brouwer.det_fderiv_eq_zero_of_norm_eq_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:14.178982+00:00
-- url     : https://prove2.me/theorems/cc288dc0-4d22-487c-972b-6bfbe6e29e1e
-- title:
--   The derivative of a sphere-valued map is singular
-- statement:
--   Let $U \subseteq \mathbb{R}^d$ be a neighbourhood of a point $x$ and let
--   $r : \mathbb{R}^d \to \mathbb{R}^d$ take values in the unit sphere throughout $U$, that is
--   $\|r(y)\| = 1$ for all $y \in U$. If $r$ is differentiable at $x$, then its derivative there is
--   singular:
--
--   $$
--   \det\bigl(Dr(x)\bigr) \;=\; 0 .
--   $$
--
--   A map whose values are constrained to a hypersurface cannot have invertible derivative: the
--   sphere has dimension $d-1$, so the derivative loses at least one dimension. This is the
--   obstruction that makes smooth retractions onto a sphere impossible, and it is the only place
--   where the geometry of the sphere, as opposed to its topology, enters.
--
--   **Formalization Note** The derivative is `fderiv ℝ r x` and the determinant is
--   `ContinuousLinearMap.det`; the neighbourhood hypothesis is `U ∈ nhds x`.
-- source:
--   J. Milnor, Analytic proofs of the “hairy ball theorem” and the Brouwer fixed point theorem, Amer. Math. Monthly 85 (1978), 521–524, §1–§3; carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem Brouwer.det_fderiv_eq_zero_of_norm_eq_one {d : ℕ} (r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (U : Set (EuclideanSpace ℝ (Fin d))) (hU : U ∈ nhds x)
    (hr : DifferentiableAt ℝ r x) (hsph : ∀ y ∈ U, ‖r y‖ = 1) :
    (fderiv ℝ r x).det = 0 := by sorry
