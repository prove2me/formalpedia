-- Prove2me | Theorems.Thm_Formalism_RankSupermodularCovolume_covol_le_of_contraction
-- name    : Formalism.RankSupermodularCovolume.covol_le_of_contraction
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:26:19.140864+00:00
-- url     : https://prove2.me/theorems/65b30761-8135-4134-8b20-5fa47e16e675
-- title:
--   Rank Supermodular Covolume: covol le of contraction
-- statement:
--   The Rank Supermodular Covolume construction uses the covol le of contraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L131-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L131-L143

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

theorem Formalism.RankSupermodularCovolume.covol_le_of_contraction (Q1 Q2 : Submodule ℤ E) [DiscreteTopology Q1]
    [DiscreteTopology Q2] (φ : Q1 ≃ₗ[ℤ] Q2) (f : E →L[ℝ] E)
    (hf : ∀ x : Q1, ((φ x : Q2) : E) = f x) (hn : ∀ v, ‖f v‖ ≤ ‖v‖) : covol Q2 ≤ covol Q1 := by sorry
