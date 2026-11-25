-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_rowOf_prod
-- name    : Formalism.L2.FormalSeriesBounds.VP.rowOf_prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:34:19.439737+00:00
-- url     : https://prove2.me/theorems/154beddf-14a9-5b0f-b59f-273931e65df6
-- title:
--   VP: row Of prod
-- statement:
--   The VP construction uses the row Of prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffSinglePointZero.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffSinglePointZero.lean#L114-L117

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
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
variable {n : ℕ}

theorem Formalism.L2.FormalSeriesBounds.VP.rowOf_prod (b : Fin n) {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries (WVO I) C) :
    rowOf b (∏ i ∈ s, F i) = ∏ i ∈ s, rowOf b (F i) := by sorry
