-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_fockR_map
-- name    : Formalism.L2.G.Model.TS.fockR_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:08.508639+00:00
-- url     : https://prove2.me/theorems/f6ced5d5-36fb-4061-896e-a77a343c4e98
-- title:
--   TS: fock R map
-- statement:
--   The TS construction uses the fock R map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L80-L84

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

theorem Formalism.L2.G.Model.TS.fockR_map {S : Type*} [CommRing S] (φ : R →+* S) (f g : MvPolynomial σ R) :
    fockR (map φ f) (map φ g) = φ (fockR f g) := by sorry
