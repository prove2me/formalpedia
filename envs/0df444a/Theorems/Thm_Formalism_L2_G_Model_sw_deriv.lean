-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_sw_deriv
-- name    : Formalism.L2.G.Model.sw_deriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:13.701316+00:00
-- url     : https://prove2.me/theorems/870c1b1d-ff51-406a-9322-7e54d80bd56c
-- title:
--   Model: sw deriv
-- statement:
--   The Model construction uses the sw deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowDivZero.lean#L37-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowDivZero.lean#L37-L51

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

theorem Formalism.L2.G.Model.sw_deriv (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    (1 + if a = b then Polynomial.X else 0) * Polynomial.derivative (rowGen R a b f) =
      rowGen R a b (Dop R a b f) := by sorry
