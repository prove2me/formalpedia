-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_kernel_L1_from_initial_neumann
-- name    : AvramDividend.Classical.causal_kernel_L1_from_initial_neumann
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T21:29:35.304681+00:00
-- url     : https://prove2.me/theorems/b1213a06-b912-469b-aa03-f51c57addb18
-- title:
--   Initial Neumann-term integrability implies finite-horizon kernel integrability
-- statement:
--   The local L1 kernel assumption needed for Gaussian Neumann dominated-convergence follows from the integral-product premise for the initial constant Neumann coefficient. This eliminates a separate reflection-integrability obligation.
-- source:
--   The canonical Neumann DCT assumes integrability of B(x-s)Q_i(s), including i=0, and Q0=1/a with a>0. Multiplying that integrable function by a and cancelling a(1/a)=1 proves local integrability of the bare shifted kernel B(x-s). This discharges hB of causal_local_neumann_convolution_majorant from the existing hI premise, with no additional analytic assumption.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open MeasureTheory Set

theorem AvramDividend.Classical.causal_kernel_L1_from_initial_neumann
    (a : ℝ) (B : ℝ → ℝ) (Q : ℕ → ℝ → ℝ)
    (ha : 0 < a)
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hI0 : ∀ x : ℝ,
      IntegrableOn (fun s : ℝ => B (x - s) * Q 0 s)
        (Ioc (0 : ℝ) x) volume) :
    ∀ x : ℝ, IntegrableOn (fun s : ℝ => B (x - s))
      (Ioc (0 : ℝ) x) volume := by sorry
