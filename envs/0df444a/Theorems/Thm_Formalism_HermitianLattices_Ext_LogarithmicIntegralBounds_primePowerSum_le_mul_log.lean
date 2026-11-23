-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_primePowerSum_le_mul_log
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.primePowerSum_le_mul_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:40.69269+00:00
-- url     : https://prove2.me/theorems/96acbfea-e18a-45a6-b28b-55dd1ca64741
-- title:
--   Logarithmic Integral Bounds: prime Power Sum le mul log
-- statement:
--   The Logarithmic Integral Bounds construction uses the prime Power Sum le mul log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L311-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L311-L355

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.primePowerSum_le_mul_log (x : ℝ) (hx : Real.exp 1 ≤ x) (p : ℕ) :
    sP (cN x) ⌊x ^ 400⌋₊ p ≤ 801 * Real.log x := by sorry
