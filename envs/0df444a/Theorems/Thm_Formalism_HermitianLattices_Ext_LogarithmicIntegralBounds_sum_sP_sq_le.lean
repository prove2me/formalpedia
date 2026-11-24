-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sum_sP_sq_le
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_sP_sq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:47.209978+00:00
-- url     : https://prove2.me/theorems/a230e498-f9a0-457c-97e8-466eeecd824a
-- title:
--   Logarithmic Integral Bounds: sum s P sq le
-- statement:
--   The Logarithmic Integral Bounds construction uses the sum s P sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagB.lean#L316-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagB.lean#L316-L452

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_sP_sq_le : ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∑ p ∈ (Icc 1 ⌊x ^ 400⌋₊).filter Nat.Prime, sP (cN x) ⌊x ^ 400⌋₊ p ^ 2 ≤ C * x * Real.log x := by sorry
