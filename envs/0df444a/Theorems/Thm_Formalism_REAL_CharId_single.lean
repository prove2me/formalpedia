-- Prove2me | Theorems.Thm_Formalism_REAL_CharId_single
-- name    : Formalism.REAL.CharId_single
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:19:43.249267+00:00
-- url     : https://prove2.me/theorems/aa564779-def5-4d52-97b0-cbf68b713836
-- title:
--   REAL: Char Id single
-- statement:
--   The REAL construction uses the Char Id single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CharId.lean#L181-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/CharId.lean#L181-L188

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

theorem Formalism.REAL.CharId_single {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (f : Fin n → Module.End ℂ V) (b : Fin n) (v : V) :
    ∑ c, f c ((Pi.single b v : Fin n → V) c) = f b v := by sorry
