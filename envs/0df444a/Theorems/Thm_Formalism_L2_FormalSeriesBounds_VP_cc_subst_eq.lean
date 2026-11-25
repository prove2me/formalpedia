-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_subst_eq
-- name    : Formalism.L2.FormalSeriesBounds.VP.cc_subst_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:57:51.112949+00:00
-- url     : https://prove2.me/theorems/6b9805d7-5995-567f-b3af-7a5b77d5e488
-- title:
--   VP: cc subst eq
-- statement:
--   The VP construction uses the cc subst eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LogCoordOfDpull.lean#L22-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LogCoordOfDpull.lean#L22-L36

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
open Formalism.L2.FormalSeriesBounds.VP

theorem Formalism.L2.FormalSeriesBounds.VP.cc_subst_eq {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by sorry
