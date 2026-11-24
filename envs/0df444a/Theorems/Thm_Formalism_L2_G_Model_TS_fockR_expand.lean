-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_fockR_expand
-- name    : Formalism.L2.G.Model.TS.fockR_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:28.530051+00:00
-- url     : https://prove2.me/theorems/ab8d2485-edac-4a06-9ec4-18536c28f00b
-- title:
--   TS: fock R expand
-- statement:
--   The TS construction uses the fock R expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L148-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L148-L153

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
variable {K S : Type*} [CommRing K] [Fintype S] {k n : ℕ}

theorem Formalism.L2.G.Model.TS.fockR_expand {τ : Type*} (f g : MvPolynomial τ K) :
    fockR f g = ∑ m ∈ f.support, ∑ m' ∈ g.support,
      fockR (monomial m (coeff m f)) (monomial m' (coeff m' g)) := by sorry
