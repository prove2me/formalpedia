-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_lin_of_add
-- name    : Formalism.L2.FormalSeriesBounds.VP.lin_of_add
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:45:20.159808+00:00
-- url     : https://prove2.me/theorems/9fc13844-8b7b-4239-a3fa-6b811d4dff78
-- title:
--   VP: lin of add
-- statement:
--   The VP construction uses the lin of add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LinearCoeffSubstChainRule.lean#L124-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LinearCoeffSubstChainRule.lean#L124-L215

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LinearCoeffSubstChainRule
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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

theorem Formalism.L2.FormalSeriesBounds.VP.lin_of_add (f : MvPowerSeries (Fin dd) C) (h0 : MvPowerSeries.constantCoeff f = 0)
    (hadd : MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((0 : Fin 2), m) + MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd)) f =
      MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((0 : Fin 2), m) : PS C 2 dd)) f +
        MvPowerSeries.subst (fun m : Fin dd => (MvPowerSeries.X ((1 : Fin 2), m) : PS C 2 dd)) f) :
    f = ∑ j, lin1 f j • (MvPowerSeries.X j : MvPowerSeries (Fin dd) C) := by sorry
