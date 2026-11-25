-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_bil_ev_right
-- name    : Formalism.L2.FormalSeriesBounds.bil_ev_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:21.898458+00:00
-- url     : https://prove2.me/theorems/b12fe642-9ac1-42b2-bd34-b879e9a3fa55
-- title:
--   Formal Series Bounds: bil ev right
-- statement:
--   The Formal Series Bounds construction uses the bil ev right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L421-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L421-L432

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
variable {dd : ℕ}
variable {h : PS C 2 dd}
  (hh : ∀ (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0)
  {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0)
include hh hφ

theorem Formalism.L2.FormalSeriesBounds.bil_ev_right (w v : Fin dd → C) :
    bil (ev (n := 2) ![pt C dd 0, comp1 φ (pt C dd 1)] h) w v = bil h w (linAct φ v) := by sorry
