-- Prove2me | Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_choose_add
-- name    : Formalism.GM.gammaIntegralityLemmas.IVP.choose_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:35.5478+00:00
-- url     : https://prove2.me/theorems/f5cd5fff-4d8a-43b0-9c7e-60bd91a86121
-- title:
--   IVP: choose add
-- statement:
--   The IVP construction uses the choose add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L72-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamInt.lean#L72-L86

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.GM.gammaIntegralityLemmas.IVP.choose_add (c k : ℕ) : IVP p k (fun m => (((m + c).choose k : ℕ) : ℚ_[p])) := by sorry
