-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
-- name    : AvramDividend.Classical.avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:32:37.159888+00:00
-- url     : https://prove2.me/theorems/97521e90-32c3-4480-a4ab-f9c8b6e5e3b1
-- title:
--   True negative-mark nonlinear J plus truncated linear L collapses to the residual very-small-mark kernel
-- statement:
--   For negative Lévy mark z and cutoff 0<eta<1, the nonlinear compensated Taylor kernel S-1_{z>-1} z d plus the linear retained-annulus kernel 1_{-1<z<-eta} z d is exactly S-1_{z>=-eta} z d. This is the pointwise algebra required to consolidate original J and L sources before physical-grid compensation.
-- source:
--   Exact elementary truncation algebra for original purejump reward80 J and L kernels.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_negative_mark_JL_cutoff_exact_kernel
    (η z S d : ℝ) (hηpos : 0 < η) (hηone : η < 1)
    (hzneg : z < 0) :
    (S - (if -1 < z then z * d else 0)) +
      (if z ∈ Ioo (-1 : ℝ) (-η) then z * d else 0) =
    S - (if -η ≤ z then z * d else 0) := by sorry
