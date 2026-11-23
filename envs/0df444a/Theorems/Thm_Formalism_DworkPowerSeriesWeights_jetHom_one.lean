-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetHom_one
-- name    : Formalism.DworkPowerSeriesWeights.jetHom_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:09.392839+00:00
-- url     : https://prove2.me/theorems/2e238162-d482-4465-a0bc-04615feab4af
-- title:
--   Dwork Power Series Weights: jet Hom one
-- statement:
--   The Dwork Power Series Weights construction uses the jet Hom one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAJet.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAJet.lean#L28-L34

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity
import Definitions.Def_Formalism_IncomingBounds_WeightIdentities
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameCoeffMulLin
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAJet
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
variable {K : Type u} [NormedField K] {ι σ : Type*} (lt : ι → σ)

theorem Formalism.DworkPowerSeriesWeights.jetHom_one : jetHom lt 0 (1 : MvPowerSeries ι K) := by sorry
