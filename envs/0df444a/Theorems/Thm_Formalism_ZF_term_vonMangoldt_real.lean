-- Prove2me | Theorems.Thm_Formalism_ZF_term_vonMangoldt_real
-- name    : Formalism.ZF.term_vonMangoldt_real
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:31.535823+00:00
-- url     : https://prove2.me/theorems/5801cb71-a200-441d-a249-16b9d1f3d691
-- title:
--   ZF: term von Mangoldt real
-- statement:
--   The ZF construction uses the term von Mangoldt real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormLogDerivLeLamF.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/NormLogDerivLeLamF.lean#L24-L31

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormLogDerivLeLamF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.term_vonMangoldt_real (σ : ℝ) (n : ℕ) :
    term ↗Λ (σ : ℂ) n = ((‖term ↗Λ (σ : ℂ) n‖ : ℝ) : ℂ) := by sorry
