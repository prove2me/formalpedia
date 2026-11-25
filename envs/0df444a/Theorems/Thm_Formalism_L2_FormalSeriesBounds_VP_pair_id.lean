-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_pair_id
-- name    : Formalism.L2.FormalSeriesBounds.VP.pair_id
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:39:51.971105+00:00
-- url     : https://prove2.me/theorems/e9ea0cbc-2235-5db7-9db6-401e99a89b4e
-- title:
--   VP: pair id
-- statement:
--   The VP construction uses the pair id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/TripleSubstSecondCoordinate.lean#L291-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/TripleSubstSecondCoordinate.lean#L291-L326

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_TripleSubstSecondCoordinate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mvExp
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
variable (Y : FBChart C V O dd)

theorem Formalism.L2.FormalSeriesBounds.VP.pair_id {X Z : Fin dd → MvPowerSeries τ C} (hX : ∀ i, MvPowerSeries.constantCoeff (X i) = 0)
    (hZ : ∀ i, MvPowerSeries.constantCoeff (Z i) = 0) :
    mvExp (hAt Y X (actAt Y Y.w0 Z) + hAt Y Z (actAt Y Y.w0 X) - hAt Y X Z) =
      MvPowerSeries.subst (P2 (actAt Y Y.w0 X) Z) Y.B.sy * MvPowerSeries.subst (P2 X Z) (Y.B.ad Y.w0) *
        MvPowerSeries.subst (P3 X (actAt Y Y.w0 Z) (actAt Y (star Y.w0) Z)) Y.B.ph2 := by sorry
