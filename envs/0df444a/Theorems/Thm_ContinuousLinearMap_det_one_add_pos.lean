-- Prove2me | Theorems.Thm_ContinuousLinearMap_det_one_add_pos
-- name    : ContinuousLinearMap.det_one_add_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:17.05051+00:00
-- url     : https://prove2.me/theorems/ba936b84-020d-4ef8-85ec-f98994cfb7dd
-- title:
--   `det (1 + T) > 0` when `‖T‖ < 1`
-- statement:
--   Let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a linear map whose operator norm satisfies
--   $\|T\| < 1$. Then
--
--   $$
--   \det\bigl(I + T\bigr) \;>\; 0 .
--   $$
--
--   Not merely nonzero — positive. Invertibility of $I + T$ for $\|T\| < 1$ is the elementary
--   Neumann series statement; the sign is the extra information, and it is what allows a determinant
--   appearing under an integral sign to be handled without case distinctions, for instance when the
--   integral is recognized as a volume.
-- source:
--   J. Milnor, Analytic proofs of the “hairy ball theorem” and the Brouwer fixed point theorem, Amer. Math. Monthly 85 (1978), 521–524, §1–§3; carved from the accepted proof of ChanPangGQVI.ProjExistence.theorem_5_2, https://prove2.me/submissions/08ed2756-557a-470f-8493-8c93e6b779c8

import Mathlib

open Metric Set MeasureTheory

theorem ContinuousLinearMap.det_one_add_pos {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hT : ‖T‖ < 1) :
    0 < (1 + T).det := by sorry
