-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_subst_genLogTrunc
-- name    : Formalism.DworkPowerSeriesWeights.subst_genLogTrunc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:24:50.982595+00:00
-- url     : https://prove2.me/theorems/81e5889b-9c2d-4495-9727-15bc51681f83
-- title:
--   Dwork Power Series Weights: subst gen Log Trunc
-- statement:
--   The Dwork Power Series Weights construction uses the subst gen Log Trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LogarithmWeightComparison.lean#L79-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LogarithmWeightComparison.lean#L79-L84

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
variable {K : Type u} [Field K] {τ : Type v} [DecidableEq τ]

theorem Formalism.DworkPowerSeriesWeights.subst_genLogTrunc [Finite τ] {g : τ → MvPowerSeries τ K} (hs : HasSubst g) (l : ℕ)
    (p : τ → τ) (x : τ) (M : ℕ) :
    subst g (genLogTrunc (K := K) l p x M) =
      ∑ e ∈ Finset.range M, ((l : K) ^ e)⁻¹ • (g (p^[e] x)) ^ ((l ^ 2) ^ e) := by sorry
