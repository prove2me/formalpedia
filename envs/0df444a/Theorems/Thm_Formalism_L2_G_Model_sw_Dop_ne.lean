-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_sw_Dop_ne
-- name    : Formalism.L2.G.Model.sw_Dop_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:40.117966+00:00
-- url     : https://prove2.me/theorems/d56cbeee-1845-494f-bf09-ca0948e073ce
-- title:
--   Model: sw Dop ne
-- statement:
--   The Model construction uses the sw Dop ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowGenMonomial.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowGenMonomial.lean#L129-L133

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
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

theorem Formalism.L2.G.Model.sw_Dop_ne (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (hab : a ≠ b)
    (f : MvPolynomial (Fin r × Fin n) R) : Dop R a b f = rowDiv R a b 1 f := by sorry
