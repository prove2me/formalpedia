-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_exponential_weight_le
-- name    : Formalism.DworkPowerSeriesWeights.exponential_weight_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:20.229498+00:00
-- url     : https://prove2.me/theorems/1a4d18c9-e770-4ce8-b4fd-4d59ebc7add7
-- title:
--   Dwork Power Series Weights: exponential weight le
-- statement:
--   The Dwork Power Series Weights construction uses the exponential weight le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormNatCastEqPowPadicValNat.lean#L62-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/NormNatCastEqPowPadicValNat.lean#L62-L100

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormNatCastEqOneOfNotDvd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46

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

theorem Formalism.DworkPowerSeriesWeights.exponential_weight_le : ExpWtLe.{u, v} := by sorry
