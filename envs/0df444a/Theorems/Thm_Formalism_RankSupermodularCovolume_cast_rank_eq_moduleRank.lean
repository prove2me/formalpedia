-- Prove2me | Theorems.Thm_Formalism_RankSupermodularCovolume_cast_rank_eq_moduleRank
-- name    : Formalism.RankSupermodularCovolume.cast_rank_eq_moduleRank
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:26:15.473806+00:00
-- url     : https://prove2.me/theorems/d5bd679d-232e-4da7-a5ef-2a01a25affc8
-- title:
--   Rank Supermodular Covolume: cast rank eq module Rank
-- statement:
--   The Rank Supermodular Covolume construction uses the cast rank eq module Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L16-L19

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

theorem Formalism.RankSupermodularCovolume.cast_rank_eq_moduleRank (N : Submodule ℤ E) [DiscreteTopology N] :
    ((rk N : ℕ) : Cardinal) = Module.rank ℤ N := by sorry
