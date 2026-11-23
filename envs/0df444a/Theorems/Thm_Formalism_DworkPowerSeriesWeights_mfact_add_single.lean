-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_add_single
-- name    : Formalism.DworkPowerSeriesWeights.mfact_add_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:58:04.280035+00:00
-- url     : https://prove2.me/theorems/a04a2383-fceb-4ca9-ab31-0f14fc0abde7
-- title:
--   Dwork Power Series Weights: mfact add single
-- statement:
--   The Dwork Power Series Weights construction uses the mfact add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L86-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean#L86-L112

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
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
variable {K : Type u} [Field K] {ι : Type}

theorem Formalism.DworkPowerSeriesWeights.mfact_add_single (κ : ι →₀ ℕ) (i : ι) :
    mfact (κ + Finsupp.single i 1) = mfact κ * (κ i + 1) := by sorry
