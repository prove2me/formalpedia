-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
-- name    : Formalism.DworkPowerSeriesWeights.low_subst_of_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:26.070122+00:00
-- url     : https://prove2.me/theorems/e3270102-bab9-4ef5-809b-a3f2ca74bb1d
-- title:
--   Dwork Power Series Weights: low subst of low
-- statement:
--   The Dwork Power Series Weights construction uses the low subst of low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LogarithmWeightComparison.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LogarithmWeightComparison.lean#L28-L39

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Theorems.Thm_Formalism_FG_SolveVAux_low_P
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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
open Formalism.FG.SolveVAux (Low low_mono low_add low_mul low_pow low_one_iff low_P)

theorem Formalism.DworkPowerSeriesWeights.low_subst_of_low {K : Type u} [Field K] {ι : Type v} [Finite ι] {τ : Type w}
    {k : ι → MvPowerSeries τ K} (hk : ∀ i, constantCoeff (k i) = 0) {m : ℕ}
    {f : MvPowerSeries ι K} (hf : Low m f) : Low m (subst k f) := by sorry
