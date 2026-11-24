-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst
-- name    : Formalism.L2.FormalSeriesBounds.Van.subst
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:13.395044+00:00
-- url     : https://prove2.me/theorems/773eb74e-6df6-41c1-9b97-c7f16dedef68
-- title:
--   Van: subst
-- statement:
--   The Van construction uses the subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L42-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAxes.lean#L42-L61

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
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

theorem Formalism.L2.FormalSeriesBounds.Van.subst {σ : Type} [Finite σ] {T : Set τ} (S : Set σ) {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (haS : ∀ s ∈ S, Van T (a s)) {f : MvPowerSeries σ C}
    (hf : ∀ e : σ →₀ ℕ, (∀ s ∈ e.support, s ∉ S) → coeff e f = 0) : Van T (MvPowerSeries.subst a f) := by sorry
