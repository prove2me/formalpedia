-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_fockR_monomial
-- name    : Formalism.L2.G.Model.TS.fockR_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:26.896315+00:00
-- url     : https://prove2.me/theorems/ff87b3d2-b683-4eaf-ade5-cc6283f722d5
-- title:
--   TS: fock R monomial
-- statement:
--   The TS construction uses the fock R monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L70-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L70-L78

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

theorem Formalism.L2.G.Model.TS.fockR_monomial [DecidableEq (σ →₀ ℕ)] (m m' : σ →₀ ℕ) (a b : R) :
    fockR (monomial m a) (monomial m' b) =
      if m = m' then a * b * ((∏ k ∈ m.support, (m k).factorial : ℕ) : R) else 0 := by sorry
