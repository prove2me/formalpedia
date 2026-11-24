-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_TailSumsHookFormulaTorsion_exp_neg_le_div_pow_four
-- name    : Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.exp_neg_le_div_pow_four
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:06.429918+00:00
-- url     : https://prove2.me/theorems/3cbb0688-1ff9-4498-ad73-17cc23591a4c
-- title:
--   Tail Sums Hook Formula Torsion: exp neg le div pow four
-- statement:
--   The Tail Sums Hook Formula Torsion construction uses the exp neg le div pow four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L290-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpNegLeDivPowFour.lean#L290-L296

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion

theorem Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.exp_neg_le_div_pow_four (y : ℝ) (hy : 0 < y) : Real.exp (-y) ≤ 24 / y ^ 4 := by sorry
