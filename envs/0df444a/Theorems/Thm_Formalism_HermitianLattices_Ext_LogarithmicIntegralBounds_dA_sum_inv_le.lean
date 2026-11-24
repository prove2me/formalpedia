-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_sum_inv_le
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_sum_inv_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:32.110335+00:00
-- url     : https://prove2.me/theorems/77f8e0a5-59ca-4b1a-9928-3912f61ea668
-- title:
--   Logarithmic Integral Bounds: d A sum inv le
-- statement:
--   The Logarithmic Integral Bounds construction uses the d A sum inv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L151-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L151-L169

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
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
open ArithmeticFunction (vonMangoldt)

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_sum_inv_le (N : ℕ) (hN : 1 ≤ N) : ∑ n ∈ Icc 1 N, (1 : ℝ) / n ≤ 1 + Real.log N := by sorry
