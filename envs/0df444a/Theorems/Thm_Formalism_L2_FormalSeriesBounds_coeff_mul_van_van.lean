-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_mul_van_van
-- name    : Formalism.L2.FormalSeriesBounds.coeff_mul_van_van
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:45:31.300782+00:00
-- url     : https://prove2.me/theorems/16530473-4cbe-47a1-806c-daa020c674f8
-- title:
--   Formal Series Bounds: coeff mul van van
-- statement:
--   The Formal Series Bounds construction uses the coeff mul van van property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L36-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean#L36-L58

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
variable {τ : Type}

theorem Formalism.L2.FormalSeriesBounds.coeff_mul_van_van {T : Set τ} {F G : MvPowerSeries τ C} (hF : Van T F) (hG : Van T G) (e : τ →₀ ℕ) (P : τ)
    (he : ∀ s ∈ T, e s ≠ 0 → s = P) (hP : e P ≤ 1) : coeff e (F * G) = 0 := by sorry
