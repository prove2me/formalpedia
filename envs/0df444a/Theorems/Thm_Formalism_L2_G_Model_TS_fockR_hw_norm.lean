-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_fockR_hw_norm
-- name    : Formalism.L2.G.Model.TS.fockR_hw_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:27.265992+00:00
-- url     : https://prove2.me/theorems/f7318e57-b0b9-40a6-a251-34a6b063263a
-- title:
--   TS: fock R hw norm
-- statement:
--   The TS construction uses the fock R hw norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L186-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/ProdBlockEmbMonomial.lean#L186-L195

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

theorem Formalism.L2.G.Model.TS.fockR_hw_norm (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) : ∃ N : ℕ, 0 < N ∧
    ∀ (R : Type) [CommRing R], fockR (hw R hn ν) (hw R hn ν) = (N : R) := by sorry
