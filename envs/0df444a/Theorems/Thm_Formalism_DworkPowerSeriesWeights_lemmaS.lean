-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_lemmaS
-- name    : Formalism.DworkPowerSeriesWeights.lemmaS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:39:55.816405+00:00
-- url     : https://prove2.me/theorems/0d540e37-3709-4f90-affa-89002c167179
-- title:
--   Dwork Power Series Weights: lemma S
-- statement:
--   The Dwork Power Series Weights construction uses the lemma S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterRadius.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterRadius.lean#L17-L19

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogStep
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ExistsNeZeroOfFinsumNeZero
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffEvenDerivativeEqZero
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmOne
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi22_homW_prod__0e07eaea3260
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open Formalism Formalism.DworkPowerSeriesWeights

theorem Formalism.DworkPowerSeriesWeights.lemmaS : LemmaS.{u} := by sorry
