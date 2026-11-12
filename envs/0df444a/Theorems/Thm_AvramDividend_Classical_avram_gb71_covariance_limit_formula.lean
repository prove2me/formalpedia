-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb71_covariance_limit_formula
-- name    : AvramDividend.Classical.avram_gb71_covariance_limit_formula
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:11:02.813478+00:00
-- url     : https://prove2.me/theorems/bddcd36f-1e71-46fc-9714-0a909f1b5284
-- title:
--   Two-grid squared-difference limit from diagonal variance and covariance limits
-- statement:
--   For a real sequence of diagonal second moments a_n and a real two-index sequence of cross moments b_{nm}, if both the diagonal moments and the joint cross moments converge to the same finite value, the polarised two-index squared-difference expression a_n+a_m-2 b_{nm} tends to zero in the joint atTop product limit. This is the elementary deterministic bridge used to isolate the physical Gaussian cross-grid covariance problem.

import Mathlib
open Filter
open scoped Topology

theorem AvramDividend.Classical.avram_gb71_covariance_limit_formula
    (a : ℕ → ℝ) (b : ℕ × ℕ → ℝ) (v : ℝ)
    (ha : Tendsto a atTop (𝓝 v))
    (hb : Tendsto b atTop (𝓝 v)) :
    Tendsto (fun nm : ℕ × ℕ => a nm.1 + a nm.2 - 2 * b nm)
      atTop (𝓝 (0 : ℝ)) := by sorry
