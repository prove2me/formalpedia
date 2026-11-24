-- Prove2me | Theorems.Thm_Formalism_REAL_CharId_card
-- name    : Formalism.REAL.CharId_card
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:20:38.108121+00:00
-- url     : https://prove2.me/theorems/2b90ceb2-bb5f-4862-8ad5-fa807af69395
-- title:
--   REAL: Char Id card
-- statement:
--   The REAL construction uses the Char Id card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CharId.lean#L106-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CharId.lean#L106-L115

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.CharId_card {n : ℕ} (t : Fin n) :
    (((univ.filter (fun a : Fin n => t < a)).card : ℕ) : ℂ) = (n : ℂ) - 1 - ((t : ℕ) : ℂ) := by sorry
