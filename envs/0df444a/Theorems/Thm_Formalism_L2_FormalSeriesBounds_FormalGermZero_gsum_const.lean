-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FormalGermZero_gsum_const
-- name    : Formalism.L2.FormalSeriesBounds.FormalGermZero.gsum_const
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:46.575086+00:00
-- url     : https://prove2.me/theorems/a67b211f-1ca1-45c3-aa19-a8264aee29c5
-- title:
--   Formal Germ Zero: gsum const
-- statement:
--   The Formal Germ Zero construction uses the gsum const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L363-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoeffSingleSubstOfLowDegree.lean#L363-L369

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartAdd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.FormalGermZero
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem Formalism.L2.FormalSeriesBounds.FormalGermZero.gsum_const {σ ι : Type} (Y : FBChart C V O dd) (Γ : ι → Fin dd → MvPowerSeries σ C)
    (hΓ : ∀ c j, MvPowerSeries.constantCoeff (Γ c j) = 0) :
    ∀ (l : List ι) j, MvPowerSeries.constantCoeff (gsum Y.B.G.F Γ l j) = 0
  := by sorry
