-- Prove2me | Theorems.Thm_Formalism_HN_rank_range_eq_and_degree_le
-- name    : Formalism.HN.rank_range_eq_and_degree_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:32.308452+00:00
-- url     : https://prove2.me/theorems/129b9a91-3dd4-4f5b-8f9a-d88dda24bc8e
-- title:
--   HN: rank range eq and degree le
-- statement:
--   The HN construction uses the rank range eq and degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean#L85-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean#L85-L139

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneq
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
open Formalism Formalism.HN
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem Formalism.HN.rank_range_eq_and_degree_le {G : Type*} [AddCommGroup G] (α : G →+ E) (β : G →+ F)
    (hαβ : ∀ g, α g = 0 → β g = 0) (hβα : ∀ g, β g = 0 → α g = 0)
    [DiscreteTopology (LinearMap.range α.toIntLinearMap)]
    [DiscreteTopology (LinearMap.range β.toIntLinearMap)]
    (C : ℝ) (hC : 0 < C) (h : ∀ g, ‖β g‖ ≤ C * ‖α g‖) :
    Formalism.F.rk (LinearMap.range β.toIntLinearMap) = Formalism.F.rk (LinearMap.range α.toIntLinearMap) ∧
    Formalism.F.deg (LinearMap.range α.toIntLinearMap) -
              (Formalism.F.rk (LinearMap.range α.toIntLinearMap) : ℝ) * Real.log C ≤
      Formalism.F.deg (LinearMap.range β.toIntLinearMap) := by sorry
