-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationFitting_rpow_neg_succ
-- name    : Formalism.L2.FormalSeriesBounds.ValuationFitting.rpow_neg_succ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T18:36:08.893015+00:00
-- url     : https://prove2.me/theorems/451b3752-e311-43f2-8cdb-3729e0882314
-- title:
--   Valuation Fitting: rpow neg succ
-- statement:
--   The Valuation Fitting construction uses the rpow neg succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PlugUP.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PlugUP.lean#L96-L99

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_DualLattices_U10
import Definitions.Def_ReciprocityTheory_DualLattices_KilledGen
import Definitions.Def_ReciprocityTheory_DualLattices_IdemGen
import Definitions.Def_ReciprocityTheory_DualLattices_LenEx
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PlugUP
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
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.ValuationFitting
open ReciprocityTheory.PGsh.Up CharacteristicFromRanks
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.ValuationFitting.rpow_neg_succ {l : ℕ} (hl : 0 < l) (n : ℕ) :
    (l : ℝ) ^ (-((n : ℝ) + 1)) = ((l : ℝ) ^ (n + 1))⁻¹ := by sorry
