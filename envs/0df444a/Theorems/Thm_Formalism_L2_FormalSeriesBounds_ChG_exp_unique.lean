-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ChG_exp_unique
-- name    : Formalism.L2.FormalSeriesBounds.ChG.exp_unique
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:11:01.846448+00:00
-- url     : https://prove2.me/theorems/9b192967-b5a3-564e-9060-21bb6204a3fc
-- title:
--   Ch G: exp unique
-- statement:
--   The Ch G construction uses the exp unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffPderivUncurry.lean#L22-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffPderivUncurry.lean#L22-L64

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieChar
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MfactMulCoeffMvExpLinF
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffPderivUncurry
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mvExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.L2.FormalSeriesBounds.ChG
variable {K : Type} [Field K] [CharZero K] {τ : Type} [Fintype τ]

theorem Formalism.L2.FormalSeriesBounds.ChG.exp_unique (y : τ → K) (Ψ : MvPowerSeries τ K) (h0 : MvPowerSeries.constantCoeff Ψ = 1)
    (hd : ∀ w, MvPowerSeries.pderiv K w Ψ = Ψ * MvPowerSeries.C (y w)) : Ψ = mvExp (linF y) := by sorry
