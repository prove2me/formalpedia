-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_one_le_of_exp_le
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_one_le_of_exp_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:21.645007+00:00
-- url     : https://prove2.me/theorems/360670b2-548a-41b0-ab3d-b437c805d183
-- title:
--   Logarithmic Integral Bounds: d A one le of exp le
-- statement:
--   The Logarithmic Integral Bounds construction uses the d A one le of exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L215-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L215-L217

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_one_le_of_exp_le {x : ℝ} (hx : Real.exp 1 ≤ x) : 1 ≤ x := by sorry
