-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_linear_coeff_subst_chain_rule
-- name    : Formalism.L2.FormalSeriesBounds.VP.linear_coeff_subst_chain_rule
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:46:00.542634+00:00
-- url     : https://prove2.me/theorems/d9741ab2-57dd-4850-b50a-3d768683387b
-- title:
--   VP: linear coeff subst chain rule
-- statement:
--   The VP construction uses the linear coeff subst chain rule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LinearCoeffSubstChainRule.lean#L23-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LinearCoeffSubstChainRule.lean#L23-L113

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LinearCoeffSubstChainRule
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
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

theorem Formalism.L2.FormalSeriesBounds.VP.linear_coeff_subst_chain_rule {σ : Type} [Fintype σ] {A : σ → MvPowerSeries τ C}
    (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) (f : MvPowerSeries σ C) (j : τ) :
    lin1 (MvPowerSeries.subst A f) j = ∑ k, lin1 (A k) j * lin1 f k := by sorry
