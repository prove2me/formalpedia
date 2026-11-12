-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva19_positive_part_from_closed_grid_approximation
-- name    : AvramDividend.Classical.avram_bva19_positive_part_from_closed_grid_approximation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:43:41.5274+00:00
-- url     : https://prove2.me/theorems/f1c3382a-be11-48f8-b2fa-dde540bf0744
-- title:
--   Signed closed-cap grid comparison and convergent approximation imply original one-sided quadrature
-- statement:
--   A deterministic algebraic closure step for original stopped marked compensator estimates. If the continuous compensator K is approximated in ordinary real convergence by its inclusive closed-cap grid A and each inclusive grid A is at most the original strict interior physical-grid quantity J, then the positive discrepancy max(K−J,0) tends to zero. This is one-sided and does not assert a false two-sided convergence at zero reserve or cap contact.
-- source:
--   Necessary assembly of efbae9c3 later-ruin one-sided original-path negative marked quadrature, after the compact kernel and signed-mask lemmas; ordinary convergence is required only for K versus the closed-cap intermediate grid A.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva19_positive_part_from_closed_grid_approximation
    (K A J : ℕ → ℝ)
    (hApprox : Tendsto (fun n => K n - A n) atTop (𝓝 (0 : ℝ)))
    (hSigned : ∀ n, A n ≤ J n) :
    Tendsto (fun n => max (K n - J n) 0) atTop (𝓝 (0 : ℝ)) := by sorry
