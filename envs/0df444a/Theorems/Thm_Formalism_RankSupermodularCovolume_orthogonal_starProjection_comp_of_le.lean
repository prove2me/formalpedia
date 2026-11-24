-- Prove2me | Theorems.Thm_Formalism_RankSupermodularCovolume_orthogonal_starProjection_comp_of_le
-- name    : Formalism.RankSupermodularCovolume.orthogonal_starProjection_comp_of_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:26:21.337599+00:00
-- url     : https://prove2.me/theorems/a40f7155-cc00-468c-91dc-7676a9da1e64
-- title:
--   Rank Supermodular Covolume: orthogonal star Projection comp of le
-- statement:
--   The Rank Supermodular Covolume construction uses the orthogonal star Projection comp of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L115-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L115-L124

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

theorem Formalism.RankSupermodularCovolume.orthogonal_starProjection_comp_of_le {U W : Submodule ℝ E} (hUW : U ≤ W) (x : E) :
    Wᗮ.starProjection (Uᗮ.starProjection x) = Wᗮ.starProjection x := by sorry
