-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_linear_coeff_eq_coeff_single
-- name    : Formalism.L2.FormalSeriesBounds.VP.linear_coeff_eq_coeff_single
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:46:44.607988+00:00
-- url     : https://prove2.me/theorems/25f9b3fe-0cd4-4877-8c87-6e43ac41a013
-- title:
--   VP: linear coeff eq coeff single
-- statement:
--   The VP construction uses the linear coeff eq coeff single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LinearCoeffSubstChainRule.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LinearCoeffSubstChainRule.lean#L18-L21

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LinearCoeffSubstChainRule
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

theorem Formalism.L2.FormalSeriesBounds.VP.linear_coeff_eq_coeff_single {σ : Type} (f : MvPowerSeries σ C) (j : σ) : lin1 f j = MvPowerSeries.coeff (Finsupp.single j 1) f := by sorry
