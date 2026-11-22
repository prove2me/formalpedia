-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_one_le_log_of_exp_le
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_one_le_log_of_exp_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:07.022873+00:00
-- url     : https://prove2.me/theorems/fcfc1133-23fe-4ee6-b9d9-28ddd81446cf
-- title:
--   Logarithmic Integral Bounds: d A one le log of exp le
-- statement:
--   The Logarithmic Integral Bounds construction uses the d A one le log of exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L219-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L219-L221

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_one_le_log_of_exp_le {x : ℝ} (hx : Real.exp 1 ≤ x) : 1 ≤ Real.log x := by sorry
