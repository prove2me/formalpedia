-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_fockR_sum_right
-- name    : Formalism.L2.G.Model.TS.fockR_sum_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:02.724527+00:00
-- url     : https://prove2.me/theorems/68377700-81a4-4b44-b072-937128197095
-- title:
--   TS: fock R sum right
-- statement:
--   The TS construction uses the fock R sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L65-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L65-L68

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_ProdBlockEmbMonomial
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

theorem Formalism.L2.G.Model.TS.fockR_sum_right {ι : Type*} (t : Finset ι) (f : MvPolynomial σ R) (g : ι → MvPolynomial σ R) :
    fockR f (∑ i ∈ t, g i) = ∑ i ∈ t, fockR f (g i) := by sorry
