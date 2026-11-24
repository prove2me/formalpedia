-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_tail_sq
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_tail_sq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:07.049639+00:00
-- url     : https://prove2.me/theorems/2bc7e2f6-af64-462c-a00e-76b72f02a616
-- title:
--   Logarithmic Integral Bounds: d A tail sq
-- statement:
--   The Logarithmic Integral Bounds construction uses the d A tail sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L185-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L185-L198

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_tail_sq (T : ℕ) (hT : 1 ≤ T) (M : ℕ) (hM : T ≤ M) :
    ∑ n ∈ Ioc T M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / T - 1 / M := by sorry
