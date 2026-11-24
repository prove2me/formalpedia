-- Prove2me | Theorems.Thm_Formalism_RankSupermodularCovolume_rk_sup_add_rk_inf
-- name    : Formalism.RankSupermodularCovolume.rk_sup_add_rk_inf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:26:13.995877+00:00
-- url     : https://prove2.me/theorems/346cf2a5-0b51-463b-86fa-a705884c8723
-- title:
--   Rank Supermodular Covolume: rk sup add rk inf
-- statement:
--   The Rank Supermodular Covolume construction uses the rk sup add rk inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermodZ.lean#L25-L36

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

theorem Formalism.RankSupermodularCovolume.rk_sup_add_rk_inf (L A B : Submodule ℤ E) [DiscreteTopology L] (hA : A ≤ L)
    (hB : B ≤ L) : rk (A ⊔ B) + rk (A ⊓ B) = rk A + rk B := by sorry
