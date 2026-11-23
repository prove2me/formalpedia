-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_coeff_exp
-- name    : Formalism.DworkPowerSeriesWeights.norm_coeff_exp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:58.090813+00:00
-- url     : https://prove2.me/theorems/b1d5edbe-9947-46c6-8ba9-a0021e3c9edc
-- title:
--   Dwork Power Series Weights: norm coeff exp
-- statement:
--   The Dwork Power Series Weights construction uses the norm coeff exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LogStep.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LogStep.lean#L30-L34

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogStep
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow

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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff)

theorem Formalism.DworkPowerSeriesWeights.norm_coeff_exp {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ}
    (hl : l.Prime) (hπ : ‖(l : K)‖ < 1) (k : ℕ) :
    ‖PowerSeries.coeff k (PowerSeries.exp K)‖ = (‖(l : K)‖ ^ padicValNat l k.factorial)⁻¹ := by sorry
