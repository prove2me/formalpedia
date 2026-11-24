-- Prove2me | Theorems.Thm_Formalism_RankSupermodularCovolume_mem_of_orthogonal_starProjection_eq_zero
-- name    : Formalism.RankSupermodularCovolume.mem_of_orthogonal_starProjection_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:26:20.678625+00:00
-- url     : https://prove2.me/theorems/d515c7a0-0b57-402e-9b72-87a7f435cbdb
-- title:
--   Rank Supermodular Covolume: mem of orthogonal star Projection eq zero
-- statement:
--   The Rank Supermodular Covolume construction uses the mem of orthogonal star Projection eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L126-L129

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

theorem Formalism.RankSupermodularCovolume.mem_of_orthogonal_starProjection_eq_zero {W : Submodule ℝ E} {x : E}
    (h : Wᗮ.starProjection x = 0) : x ∈ W := by sorry
