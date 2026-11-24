-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_sw_rel
-- name    : Formalism.L2.G.Model.sw_rel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:08.064604+00:00
-- url     : https://prove2.me/theorems/2dfd23c8-3a2d-477c-831f-e89912471df1
-- title:
--   Model: sw rel
-- statement:
--   The Model construction uses the sw rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowDivZero.lean#L111-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowDivZero.lean#L111-L127

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model
open Formalism.GradedWeylDivisibility
variable (R : Type) [CommRing R] {r n : ℕ}

theorem Formalism.L2.G.Model.sw_rel (a b c d : Fin r) :
    DL R (n := n) a b * DL R c d - DL R c d * DL R a b =
      (if b = c then DL R a d else 0) - (if d = a then DL R c b else 0) := by sorry
