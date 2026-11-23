-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_log_le_of_le_floor
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_log_le_of_le_floor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:24.130172+00:00
-- url     : https://prove2.me/theorems/7e01e72f-7037-4ecc-8be1-6810d8c6b42b
-- title:
--   Logarithmic Integral Bounds: d A log le of le floor
-- statement:
--   The Logarithmic Integral Bounds construction uses the d A log le of le floor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L228-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L228-L234

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_log_le_of_le_floor {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ ⌊x ^ 400⌋₊) :
    Real.log n ≤ 400 * Real.log x := by sorry
