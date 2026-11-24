-- Prove2me | Theorems.Thm_Formalism_RankSupermodularCovolume_mem_span_inf_of_mem_span
-- name    : Formalism.RankSupermodularCovolume.mem_span_inf_of_mem_span
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:26:25.364169+00:00
-- url     : https://prove2.me/theorems/f617c8c8-af9f-40c9-bf51-ecce38e64db6
-- title:
--   Rank Supermodular Covolume: mem span inf of mem span
-- statement:
--   The Rank Supermodular Covolume construction uses the mem span inf of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L38-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L38-L61

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.RankSupermodularCovolume
open Formalism.F
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Formalism.RankSupermodularCovolume.mem_span_inf_of_mem_span (L A B : Submodule ℤ E) [DiscreteTopology L] (hA : A ≤ L)
    (hB : B ≤ L) {b : E} (hbB : b ∈ B) (hbA : b ∈ span ℝ (A : Set E)) :
    b ∈ span ℝ ((A ⊓ B : Submodule ℤ E) : Set E) := by sorry
