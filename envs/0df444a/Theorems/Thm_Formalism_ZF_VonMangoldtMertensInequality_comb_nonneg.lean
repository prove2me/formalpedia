-- Prove2me | Theorems.Thm_Formalism_ZF_VonMangoldtMertensInequality_comb_nonneg
-- name    : Formalism.ZF.VonMangoldtMertensInequality.comb_nonneg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:42:06.373432+00:00
-- url     : https://prove2.me/theorems/4623a7f1-fb62-4241-8853-cc9a571a8a99
-- title:
--   Von Mangoldt Mertens Inequality: comb nonneg
-- statement:
--   The Von Mangoldt Mertens Inequality construction uses the comb nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ThreeFourOne.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ThreeFourOne.lean#L38-L41

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ThreeFourOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction
noncomputable section
open Formalism Formalism.ZF
open Formalism.ZF.VonMangoldtMertensInequality

theorem Formalism.ZF.VonMangoldtMertensInequality.comb_nonneg (a θ : ℝ) (ha : 0 ≤ a) :
    0 ≤ 3 * a + 4 * (a * Real.cos θ) + a * Real.cos (2 * θ) := by sorry
