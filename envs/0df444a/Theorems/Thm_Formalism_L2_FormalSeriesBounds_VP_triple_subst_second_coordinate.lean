-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_triple_subst_second_coordinate
-- name    : Formalism.L2.FormalSeriesBounds.VP.triple_subst_second_coordinate
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:44:32.004903+00:00
-- url     : https://prove2.me/theorems/186777fe-14c8-519b-90c2-30bdcdf3a379
-- title:
--   VP: triple subst second coordinate
-- statement:
--   The VP construction uses the triple subst second coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/TripleSubstSecondCoordinate.lean#L216-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/TripleSubstSecondCoordinate.lean#L216-L220

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffTripleSubstitution
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_TripleSubstSecondCoordinate
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

theorem Formalism.L2.FormalSeriesBounds.VP.triple_subst_second_coordinate : (fun i => MvPowerSeries.subst (P3 a b c) (pt C dd (1 : Fin 3) i)) = b := by sorry
