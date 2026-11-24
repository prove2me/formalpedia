-- Prove2me | Theorems.Thm_Formalism_LT_ExpP_norm_coeff_monomial_le
-- name    : Formalism.LT.ExpP.norm_coeff_monomial_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:20.149159+00:00
-- url     : https://prove2.me/theorems/ccf6009b-4806-4aeb-b977-789e290ccd5e
-- title:
--   Exp P: norm coeff monomial le
-- statement:
--   The Exp P construction uses the norm coeff monomial le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L126-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L126-L131

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
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
open Formalism Formalism.LT Formalism.LT.ExpP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.ExpP.norm_coeff_monomial_le (m k : ℕ) (e : Fin 2 →₀ ℕ) :
    ‖MvPowerSeries.coeff e
      ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ m * MvPowerSeries.X 1 ^ k)‖ ≤ 1 := by sorry
