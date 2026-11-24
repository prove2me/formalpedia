-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_cw_eval_coeffT
-- name    : Formalism.L2.G.Model.TS.cw_eval_coeffT
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:11.000791+00:00
-- url     : https://prove2.me/theorems/95b40370-fd13-4325-abd2-10929b291ddc
-- title:
--   TS: cw eval coeff T
-- statement:
--   The TS construction uses the cw eval coeff T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L209-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/CwlApplyWordAppendSingle.lean#L209-L219

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
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
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}

theorem Formalism.L2.G.Model.TS.cw_eval_coeffT (d : Fin r × Fin n →₀ ℕ) (y : Fin r × Fin n → R)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    eval y (cwl_coeffT d G) = coeff d (eval (fun v => C (y v)) G) := by sorry
