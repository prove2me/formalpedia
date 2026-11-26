-- Prove2me | Theorems.Thm_FD1D_finite_average_sqrt_le_sqrt_average
-- name    : FD1D.finite_average_sqrt_le_sqrt_average
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:24:56.492329+00:00
-- url     : https://prove2.me/theorems/e97daa5f-f4c8-4ac4-b24d-1c5367c287d6
-- title:
--   FD1 D: finite average sqrt le sqrt average
-- statement:
--   Jensen's inequality for the square root of a nonnegative finite average.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L199-L233
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/PotentialBounds.lean#L199-L233

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators

theorem FD1D.finite_average_sqrt_le_sqrt_average
    {T : ℕ} (hT : 0 < T) (f : ℕ → ℝ)
    (hf : ∀ t < T, 0 ≤ f t) :
    (∑ t ∈ Finset.range T, Real.sqrt (f t)) / T ≤
      Real.sqrt ((∑ t ∈ Finset.range T, f t) / T) := by sorry
