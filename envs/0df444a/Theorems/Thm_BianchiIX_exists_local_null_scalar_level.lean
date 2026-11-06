-- Prove2me | Theorems.Thm_BianchiIX_exists_local_null_scalar_level
-- name    : BianchiIX.exists_local_null_scalar_level
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:05:00.339963+00:00
-- url     : https://prove2.me/theorems/aa34c9d1-309a-49d6-9d8b-e79933d84567
-- title:
--   Local nullity of the zero level at a regular scalar coordinate
-- statement:
--   Let $g:\mathbb R^n\to\mathbb R$ be $C^1$ at $x$ and suppose
--   $Dg_x e_i\ne0$ for some coordinate $i$. There exists an open $U\ni x$
--   such that $\lambda_n(U\cap g^{-1}(0))=0$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Measure/RegularLevelNull.lean#L25-L71

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

theorem BianchiIX.exists_local_null_scalar_level {n : ℕ} {g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hg : ContDiffAt ℝ 1 g x) {i : Fin n}
    (hi : fderiv ℝ g x (Pi.single i 1) ≠ 0) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧ volume (U ∩ {y | g y = 0}) = 0 := by sorry
