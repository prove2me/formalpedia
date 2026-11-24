-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_tsact_X_mul
-- name    : Formalism.L2.G.Model.TS.tsact_X_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:04.864608+00:00
-- url     : https://prove2.me/theorems/16325316-04d9-46a3-9830-e50b0508f19d
-- title:
--   TS: tsact X mul
-- statement:
--   The TS construction uses the tsact X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L102-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L102-L110

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingRowAction
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
variable {σ R : Type*} [CommRing R]

theorem Formalism.L2.G.Model.TS.tsact_X_mul (v : σ) (f h : MvPolynomial σ R) :
    fockR (f * X v) h = fockR f (pderiv v h) := by sorry
