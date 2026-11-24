-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetsIntegral_subst
-- name    : Formalism.DworkPowerSeriesWeights.jetsIntegral_subst
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:03:19.361246+00:00
-- url     : https://prove2.me/theorems/309d6860-eca6-4dd5-8001-38a19ab77328
-- title:
--   Dwork Power Series Weights: jets Integral subst
-- statement:
--   The Dwork Power Series Weights construction uses the jets Integral subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L229-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L229-L240

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

theorem Formalism.DworkPowerSeriesWeights.jetsIntegral_subst {K : Type u} [NormedField K] [IsUltrametricDist K] {ι ι' : Type}
    [Fintype ι] [Fintype ι'] (A : ι → ι' → K) (hA : ∀ i j, ‖A i j‖ ≤ 1) (sg : MvPowerSeries ι' K)
    (hsg : JetsIntegral sg) :
    JetsIntegral (MvPowerSeries.subst
      (fun j : ι' => (∑ i : ι, MvPowerSeries.C (A i j) * MvPowerSeries.X i : MvPowerSeries ι K))
      sg) := by sorry
