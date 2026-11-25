-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_van_prod
-- name    : Formalism.L2.FormalSeriesBounds.van_prod
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:47:09.871892+00:00
-- url     : https://prove2.me/theorems/d9374f6c-821a-4735-8195-25d4b1dc6e03
-- title:
--   Formal Series Bounds: van prod
-- statement:
--   The Formal Series Bounds construction uses the van prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L26-L34

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod

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
variable {τ : Type}

theorem Formalism.L2.FormalSeriesBounds.van_prod {σ : Type} {T : Set τ} {a : σ → MvPowerSeries τ C} {e : σ →₀ ℕ} {s : σ} (hs : s ∈ e.support)
    (ha : Van T (a s)) : Van T (e.prod fun s m => a s ^ m) := by sorry
