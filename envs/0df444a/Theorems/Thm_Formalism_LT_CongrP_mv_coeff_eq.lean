-- Prove2me | Theorems.Thm_Formalism_LT_CongrP_mv_coeff_eq
-- name    : Formalism.LT.CongrP.mv_coeff_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:10.272293+00:00
-- url     : https://prove2.me/theorems/053d77f6-bdbf-4fa1-b18c-c81b87b6bd67
-- title:
--   Congr P: mv coeff eq
-- statement:
--   The Congr P construction uses the mv coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L84-L87

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.CongrP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.CongrP.mv_coeff_eq (φ : PowerSeries K) (d : Unit →₀ ℕ) :
    MvPowerSeries.coeff d φ = coeff (d ()) φ := by sorry
