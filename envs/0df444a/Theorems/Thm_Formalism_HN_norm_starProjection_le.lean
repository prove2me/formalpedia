-- Prove2me | Theorems.Thm_Formalism_HN_norm_starProjection_le
-- name    : Formalism.HN.norm_starProjection_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:13.333397+00:00
-- url     : https://prove2.me/theorems/58e512c6-967f-445d-b39f-b82866f26ca6
-- title:
--   HN: norm star Projection le
-- statement:
--   The HN construction uses the norm star Projection le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean#L141-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SlopeIneq.lean#L141-L204

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

theorem Formalism.HN.norm_starProjection_le {G : Type*} [AddCommGroup G] (α : G →+ E) (β : G →+ F) (C : ℝ)
    (h : ∀ g, ‖β g‖ ≤ C * ‖α g‖) (S : Set G) (U' : Submodule ℝ F) (hS : ∀ s ∈ S, β s ∈ U')
    (g : G) :
    ‖U'ᗮ.starProjection (β g)‖ ≤ C * ‖(span ℝ (α '' S))ᗮ.starProjection (α g)‖ := by sorry
