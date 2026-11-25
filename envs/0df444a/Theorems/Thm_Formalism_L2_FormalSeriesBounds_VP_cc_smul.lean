-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_smul
-- name    : Formalism.L2.FormalSeriesBounds.VP.cc_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:27:20.934443+00:00
-- url     : https://prove2.me/theorems/669703f0-4c65-422d-ad77-9ddac8951587
-- title:
--   VP: cc smul
-- statement:
--   The VP construction uses the cc smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfLogUnitGerm.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfLogUnitGerm.lean#L17-L19

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSProd
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

theorem Formalism.L2.FormalSeriesBounds.VP.cc_smul {σ : Type} (c : C) {F : MvPowerSeries σ C} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (c • F) = 0 := by sorry
