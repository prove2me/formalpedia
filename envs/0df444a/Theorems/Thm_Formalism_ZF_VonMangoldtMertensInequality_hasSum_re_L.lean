-- Prove2me | Theorems.Thm_Formalism_ZF_VonMangoldtMertensInequality_hasSum_re_L
-- name    : Formalism.ZF.VonMangoldtMertensInequality.hasSum_re_L
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:40:51.087011+00:00
-- url     : https://prove2.me/theorems/326b0f66-5367-49de-9a12-dd41e21fc930
-- title:
--   Von Mangoldt Mertens Inequality: has Sum re L
-- statement:
--   The Von Mangoldt Mertens Inequality construction uses the has Sum re L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ThreeFourOne.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ThreeFourOne.lean#L30-L36

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

theorem Formalism.ZF.VonMangoldtMertensInequality.hasSum_re_L {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    HasSum (fun n => (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + y * I) n).re)
      (-(deriv riemannZeta ((σ : ℂ) + y * I) / riemannZeta ((σ : ℂ) + y * I))).re := by sorry
