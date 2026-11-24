-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_prod_monomial_eq
-- name    : Formalism.L2.G.Model.TS.prod_monomial_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:02.947384+00:00
-- url     : https://prove2.me/theorems/120fd1b8-5714-469d-adb2-bf9e3c35d489
-- title:
--   TS: prod monomial eq
-- statement:
--   The TS construction uses the prod monomial eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L92-L98

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

theorem Formalism.L2.G.Model.TS.prod_monomial_eq {ι τ : Type*} (t : Finset ι) (e : ι → τ →₀ ℕ) (a : ι → K) :
    ∏ i ∈ t, monomial (e i) (a i) = monomial (∑ i ∈ t, e i) (∏ i ∈ t, a i) := by sorry
