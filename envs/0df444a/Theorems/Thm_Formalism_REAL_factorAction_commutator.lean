-- Prove2me | Theorems.Thm_Formalism_REAL_factorAction_commutator
-- name    : Formalism.REAL.factorAction_commutator
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:21:18.470811+00:00
-- url     : https://prove2.me/theorems/817d406e-d3f1-48e3-a9de-c2eca03e67f0
-- title:
--   REAL: factor Action commutator
-- statement:
--   The REAL construction uses the factor Action commutator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L325-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L325-L332

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

theorem Formalism.REAL.factorAction_commutator {j : ℕ} (i : Fin j) (a b c d : Fin n) :
    (factorAction i a b * factorAction i c d - factorAction i c d * factorAction i a b : Module.End ℂ (Arr V n j)) =
      (if b = c then factorAction i a d else 0) - (if d = a then factorAction i c b else 0) := by sorry
