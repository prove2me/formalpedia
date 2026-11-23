-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_pair_linearity
-- name    : Formalism.DworkPowerSeriesWeights.jet_pair_linearity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:14.590603+00:00
-- url     : https://prove2.me/theorems/3a45b593-9d9e-46dd-a6b4-ff3caf644809
-- title:
--   Dwork Power Series Weights: jet pair linearity
-- statement:
--   The Dwork Power Series Weights construction uses the jet pair linearity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L236-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L236-L278

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
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
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {K : Type u} [Field K] {ι ι' : Type} [Fintype ι] [Fintype ι']

theorem Formalism.DworkPowerSeriesWeights.jet_pair_linearity : JetPairLin.{u} := by sorry
