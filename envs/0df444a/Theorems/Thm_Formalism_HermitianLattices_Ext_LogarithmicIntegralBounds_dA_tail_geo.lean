-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_tail_geo
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_tail_geo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:42.79009+00:00
-- url     : https://prove2.me/theorems/d361b3e6-f656-4cd0-aae3-8f1652523d22
-- title:
--   Logarithmic Integral Bounds: d A tail geo
-- statement:
--   The Logarithmic Integral Bounds construction uses the d A tail geo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L200-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqDiagA.lean#L200-L208

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_tail_geo (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (T M : ℕ) (hM : T ≤ M) :
    ∑ i ∈ Ioc T M, r ^ i + r ^ M ≤ r ^ T := by sorry
