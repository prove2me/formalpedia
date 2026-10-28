-- Prove2me | Theorems.Thm_Brouwer_norm_add_smul_sq
-- name    : Brouwer.norm_add_smul_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:21.196761+00:00
-- url     : https://prove2.me/theorems/7c16753e-328f-463b-b099-ec12631c8fdc
-- title:
--   Expanding `‖x + λ • v‖²` in a real inner product space
-- statement:
--   Let $x$ and $v$ be vectors in a real inner product space and let $\lambda \in \mathbb{R}$.
--   Then
--
--   $$
--   \|x + \lambda v\|^{2} \;=\; \|x\|^{2} \;+\; 2\lambda\,\langle x, v\rangle \;+\; \lambda^{2}\,\|v\|^{2}.
--   $$
--
--   The squared norm along a line is a quadratic polynomial in the line parameter, with the inner
--   product $\langle x, v\rangle$ as its linear coefficient. This is the identity behind every
--   "choose the step size" computation: minimizing the right-hand side over $\lambda$ is what turns
--   a geometric constraint into an inequality between inner products.
-- source:
--   Expansion of the norm in a real inner product space; carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem Brouwer.norm_add_smul_sq {d : ℕ} (x v : EuclideanSpace ℝ (Fin d)) (lam : ℝ) :
    ‖x + lam • v‖ ^ 2 = ‖x‖ ^ 2 + 2 * lam * inner ℝ x v + lam ^ 2 * ‖v‖ ^ 2 := by sorry
