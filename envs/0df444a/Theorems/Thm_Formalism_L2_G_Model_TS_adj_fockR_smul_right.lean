-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_adj_fockR_smul_right
-- name    : Formalism.L2.G.Model.TS.adj_fockR_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:12.735966+00:00
-- url     : https://prove2.me/theorems/f0eb549b-d891-4c5e-ad29-b2a5c0479811
-- title:
--   TS: adj fock R smul right
-- statement:
--   The TS construction uses the adj fock R smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingDividedAdjoint.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingDividedAdjoint.lean#L56-L58

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingDividedAdjoint
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

theorem Formalism.L2.G.Model.TS.adj_fockR_smul_right {σ R : Type*} [CommRing R] (a : R) (f g : MvPolynomial σ R) :
    fockR f (a • g) = a * fockR f g := by sorry
