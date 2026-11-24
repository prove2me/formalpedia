-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_tsact_fact_succ
-- name    : Formalism.L2.G.Model.TS.tsact_fact_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:34.805044+00:00
-- url     : https://prove2.me/theorems/75293c6e-c429-4386-9882-0410f68895df
-- title:
--   TS: tsact fact succ
-- statement:
--   The TS construction uses the tsact fact succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L79-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingRowAction.lean#L79-L100

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

theorem Formalism.L2.G.Model.TS.tsact_fact_succ (m : σ →₀ ℕ) (v : σ) :
    ∏ k ∈ (m + Finsupp.single v 1).support, ((m + Finsupp.single v 1 : σ →₀ ℕ) k).factorial
      = (m v + 1) * ∏ k ∈ m.support, (m k).factorial := by sorry
