-- Prove2me | Theorems.Thm_Formalism_REAL_pointwise_operator_gl_relation
-- name    : Formalism.REAL.pointwise_operator_gl_relation
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:24:20.184745+00:00
-- url     : https://prove2.me/theorems/69aa66d2-3b49-455a-ab26-9042fd10868d
-- title:
--   REAL: pointwise operator gl relation
-- statement:
--   The REAL construction uses the pointwise operator gl relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L357-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L357-L364

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

theorem Formalism.REAL.pointwise_operator_gl_relation {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (a b c d : Fin n) :
    (ptE E a b * ptE E c d - ptE E c d * ptE E a b : Module.End ℂ (Arr V n j)) =
      (if b = c then ptE E a d else 0) - (if d = a then ptE E c b else 0) := by sorry
