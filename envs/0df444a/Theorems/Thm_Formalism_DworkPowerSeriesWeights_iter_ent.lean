-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_iter_ent
-- name    : Formalism.DworkPowerSeriesWeights.iter_ent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:36.102596+00:00
-- url     : https://prove2.me/theorems/4e02b2da-c39a-486b-9a3b-95ff14db3b70
-- title:
--   Dwork Power Series Weights: iter ent
-- statement:
--   The Dwork Power Series Weights construction uses the iter ent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LogarithmWeightComparison.lean#L205-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/LogarithmWeightComparison.lean#L205-L215

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

theorem Formalism.DworkPowerSeriesWeights.iter_ent {d N0 N1 : ℕ} (x : ZV d N0 N1) (e : ℕ) :
    (fun y : ZV d N0 N1 => (y.1 - 2, y.2.1, y.2.2))^[e] x =
      (x.1 - 2 * (e : ZMod d), x.2.1, x.2.2) := by sorry
