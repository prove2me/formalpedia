-- Prove2me | Theorems.Thm_Formalism_HN_Rerealization_covol_rk_eq
-- name    : Formalism.HN.Rerealization.covol_rk_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:17.640736+00:00
-- url     : https://prove2.me/theorems/baad4de3-a5ff-44b4-8a1f-f92a2005ae83
-- title:
--   Rerealization: covol rk eq
-- statement:
--   The Rerealization construction uses the covol rk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Rerealize.lean#L84-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Rerealize.lean#L84-L127

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.Rerealization
variable {G E F : Type*} [AddCommGroup G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem Formalism.HN.Rerealization.covol_rk_eq (α : G →+ E) (β : G →+ F) (hn : ∀ g, ‖β g‖ = ‖α g‖) (H : AddSubgroup G)
    (hα : DiscreteTopology (H.map α).toIntSubmodule)
    (hβ : DiscreteTopology (H.map β).toIntSubmodule) :
    Formalism.F.covol (H.map β).toIntSubmodule = Formalism.F.covol (H.map α).toIntSubmodule ∧
      Formalism.F.rk (H.map β).toIntSubmodule = Formalism.F.rk (H.map α).toIntSubmodule := by sorry
