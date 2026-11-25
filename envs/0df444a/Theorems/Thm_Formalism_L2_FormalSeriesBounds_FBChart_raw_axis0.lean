-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_raw_axis0
-- name    : Formalism.L2.FormalSeriesBounds.FBChart.raw_axis0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:37:26.994004+00:00
-- url     : https://prove2.me/theorems/fd2efed3-e3a9-40f4-8ff2-aa81fad0ca5c
-- title:
--   FBChart: raw axis0
-- statement:
--   The FBChart construction uses the raw axis0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L167-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L167-L172

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

theorem Formalism.L2.FormalSeriesBounds.FBChart.raw_axis0 (e : Fin 2 × Fin dd →₀ ℕ) (he : ∀ s ∈ e.support, s.1 ≠ 0) :
    MvPowerSeries.coeff e (Y.raw p).h = 0 := by sorry
