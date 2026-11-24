-- Prove2me | Theorems.Thm_Formalism_REAL_factorAction_commute_pointwiseAction
-- name    : Formalism.REAL.factorAction_commute_pointwiseAction
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:21:15.626249+00:00
-- url     : https://prove2.me/theorems/4aaffb8e-d344-43e1-adcd-d071cad9734d
-- title:
--   REAL: factor Action commute pointwise Action
-- statement:
--   The REAL construction uses the factor Action commute pointwise Action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L349-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L349-L355

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

theorem Formalism.REAL.factorAction_commute_pointwiseAction {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (i : Fin j) (a b c d : Fin n) :
    (factorAction i a b * ptE E c d : Module.End ℂ (Arr V n j)) = ptE E c d * factorAction i a b := by sorry
