-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_ev_right
-- name    : Formalism.L2.FormalSeriesBounds.van_ev_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:46:29.454711+00:00
-- url     : https://prove2.me/theorems/1c7aa75c-41a4-4c1c-8ed4-7a9d72b72504
-- title:
--   Formal Series Bounds: van ev right
-- statement:
--   The Formal Series Bounds construction uses the van ev right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L473-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L473-L486

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.van_ev_right {h : PS C 2 dd}
    (hh : ∀ (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0)
    {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0) :
    Van (Tg dd 0) (ev (n := 2) ![pt C dd 0, comp1 φ (pt C dd 1)] h) := by sorry
