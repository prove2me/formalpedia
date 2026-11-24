-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_rename_mem_opInt
-- name    : Formalism.DworkPowerSeriesWeights.rename_mem_opInt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:52:38.844493+00:00
-- url     : https://prove2.me/theorems/bbd98b58-9e17-4458-9b83-190459100a9b
-- title:
--   Dwork Power Series Weights: rename mem op Int
-- statement:
--   The Dwork Power Series Weights construction uses the rename mem op Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L446-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FirstRowMinorDegreeLeOne.lean#L446-L456

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {H : Type} {N0 : ℕ}

theorem Formalism.DworkPowerSeriesWeights.rename_mem_opInt {σ ρ : Type} (f : σ → ρ) (P : MvPolynomial σ K)
    (hP : P ∈ opInt K σ) : rename f P ∈ opInt K ρ := by sorry
