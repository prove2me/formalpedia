-- Prove2me | Theorems.Thm_Formalism_REAL_arr_operators_gl_relation
-- name    : Formalism.REAL.arr_operators_gl_relation
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:20:16.57291+00:00
-- url     : https://prove2.me/theorems/f03058f4-4246-4ebd-acbe-a7a91978972d
-- title:
--   REAL: arr operators gl relation
-- statement:
--   The REAL construction uses the arr operators gl relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L403-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L403-L411

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.arr_operators_gl_relation {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) :
    GlRel (arrE E j) := by sorry
