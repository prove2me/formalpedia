-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_sw_step_eq
-- name    : Formalism.L2.G.Model.sw_step_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:48.362814+00:00
-- url     : https://prove2.me/theorems/54189552-e7c4-4cd3-9a58-57fc83ccfb5f
-- title:
--   Model: sw step eq
-- statement:
--   The Model construction uses the sw step eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowDivZero.lean#L71-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowDivZero.lean#L71-L87

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

theorem Formalism.L2.G.Model.sw_step_eq (a : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    ((k + 1 : ℕ) : R) • rowDiv R a a (k + 1) f =
      rowDiv R a a k (Dop R a a f) - (k : R) • rowDiv R a a k f := by sorry
