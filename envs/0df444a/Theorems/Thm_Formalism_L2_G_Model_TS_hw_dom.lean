-- Prove2me | Theorems.Thm_Formalism_L2_G_Model_TS_hw_dom
-- name    : Formalism.L2.G.Model.TS.hw_dom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:51.289376+00:00
-- url     : https://prove2.me/theorems/554e2c31-da6c-4fd3-b69e-541398c165c1
-- title:
--   TS: hw dom
-- statement:
--   The TS construction uses the hw dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingHighestWeightProof.lean#L13-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/TransposeWordsProofs/FockPairingHighestWeightProof.lean#L13-L41

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_FockPairingHighestWeightProof
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

theorem Formalism.L2.G.Model.TS.hw_dom {B : Type} [CommRing B] [IsDomain B] {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r)
    (f : MvPolynomial (Fin r × Fin n) B) (hf : f ∈ dualWeyl B r n ν) :
    ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a := by sorry
