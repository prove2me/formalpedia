-- Prove2me | Theorems.Thm_Formalism_ZF_VonMangoldtMertensInequality_re_term_vonMangoldt
-- name    : Formalism.ZF.VonMangoldtMertensInequality.re_term_vonMangoldt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:40:51.45714+00:00
-- url     : https://prove2.me/theorems/8cfb9ef9-ceee-48aa-a6cf-9081546f743f
-- title:
--   Von Mangoldt Mertens Inequality: re term von Mangoldt
-- statement:
--   The Von Mangoldt Mertens Inequality construction uses the re term von Mangoldt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ThreeFourOne.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ThreeFourOne.lean#L11-L28

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

theorem Formalism.ZF.VonMangoldtMertensInequality.re_term_vonMangoldt {n : ℕ} (hn : n ≠ 0) (σ y : ℝ) :
    (LSeries.term (fun m => (Λ m : ℂ)) ((σ : ℂ) + y * I) n).re =
      Λ n * Real.exp (-σ * Real.log n) * Real.cos (y * Real.log n) := by sorry
