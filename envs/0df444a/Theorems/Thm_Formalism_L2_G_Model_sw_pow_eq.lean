-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_sw_pow_eq
-- name    : Formalism.L2.G.Model.sw_pow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:35.561355+00:00
-- url     : https://prove2.me/theorems/097cbded-60d8-4257-81a3-85913cd14883
-- title:
--   Model: sw pow eq
-- statement:
--   The Model construction uses the sw pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowDivZero.lean#L97-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/SwRowDivZero.lean#L97-L109

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod

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

theorem Formalism.L2.G.Model.sw_pow_eq (a : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    ((k.factorial : ℕ) : R) • rowDiv R a a k f =
      (((List.range k).map fun j : ℕ => DL R (n := n) a a -
        (j : R) • (1 : Module.End R (MvPolynomial (Fin r × Fin n) R))).prod) f := by sorry
