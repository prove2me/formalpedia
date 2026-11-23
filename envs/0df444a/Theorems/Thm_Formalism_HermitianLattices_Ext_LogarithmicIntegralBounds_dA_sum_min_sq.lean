-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_sum_min_sq
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_sum_min_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:41.616246+00:00
-- url     : https://prove2.me/theorems/9fc839f6-bd54-4483-8c73-ecdf5619c36e
-- title:
--   Logarithmic Integral Bounds: d A sum min sq
-- statement:
--   The Logarithmic Integral Bounds construction uses the d A sum min sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L359-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L359-L387

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_sum_min_sq (x : ℝ) (hx : 1 ≤ x) (M : ℕ) :
    ∑ m ∈ Icc 1 M, min 1 (x / (m : ℝ) ^ 2) ≤ 3 * Real.sqrt x := by sorry
