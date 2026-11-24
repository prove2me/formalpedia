-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_C_mul_X_mem_opInt
-- name    : Formalism.DworkPowerSeriesWeights.C_mul_X_mem_opInt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:02:55.831453+00:00
-- url     : https://prove2.me/theorems/3e751d61-8ef0-4c61-a488-18e15c21bd6a
-- title:
--   Dwork Power Series Weights: C mul X mem op Int
-- statement:
--   The Dwork Power Series Weights construction uses the C mul X mem op Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L221-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L221-L227

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

theorem Formalism.DworkPowerSeriesWeights.C_mul_X_mem_opInt {K : Type u} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : K)
    (hc : ‖c‖ ≤ 1) (j : σ) : C c * X j ∈ opInt K σ := by sorry
