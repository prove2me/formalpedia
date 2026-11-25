-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_second_partial_law_at_points
-- name    : Formalism.L2.FormalSeriesBounds.VP.second_partial_law_at_points
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T09:40:33.734476+00:00
-- url     : https://prove2.me/theorems/40c8b489-7e89-56fa-aad4-b4b543af1937
-- title:
--   VP: second partial law at points
-- statement:
--   The VP construction uses the second partial law at points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/TripleSubstSecondCoordinate.lean#L228-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/TripleSubstSecondCoordinate.lean#L228-L249

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_TripleSubstSecondCoordinate
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
variable {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
  (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0)
include ha hb hc

theorem Formalism.L2.FormalSeriesBounds.VP.second_partial_law_at_points : MvPowerSeries.subst (P3 a b c) Y.B.ph2 =
    mvExp (hAt Y a b + hAt Y a c - hAt Y a (addAt Y b c)) := by sorry
