-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_jetPair_le
-- name    : Formalism.DworkPowerSeriesWeights.norm_jetPair_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:53:56.543329+00:00
-- url     : https://prove2.me/theorems/d9923741-d3cf-4aa6-ace5-f95b0c6d6185
-- title:
--   Dwork Power Series Weights: norm jet Pair le
-- statement:
--   The Dwork Power Series Weights construction uses the norm jet Pair le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L210-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L210-L219

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial

theorem Formalism.DworkPowerSeriesWeights.norm_jetPair_le {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type}
    (P : MvPolynomial ι K) (hP : P ∈ opInt K ι) (F : MvPowerSeries ι K) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ κ ∈ P.support, ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ F‖ ≤ B) :
    ‖jetPair P F‖ ≤ B := by sorry
