-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_collapse
-- name    : Formalism.DworkPowerSeriesWeights.jet_collapse
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:03:04.278823+00:00
-- url     : https://prove2.me/theorems/f3b79f26-4a90-4a11-b851-bb180eabcc03
-- title:
--   Dwork Power Series Weights: jet collapse
-- statement:
--   The Dwork Power Series Weights construction uses the jet collapse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAJet.lean#L87-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAJet.lean#L87-L120

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

theorem Formalism.DworkPowerSeriesWeights.jet_collapse {K : Type u} [NormedField K] [IsUltrametricDist K] {d N0 N1 : ℕ} [NeZero d]
    {ι : Type*}
    [Fintype ι] [DecidableEq ι] (lt : ι → ZMod d) (M : ZV d N0 N1 → ι → K)
    (hM1 : ∀ x i, ‖M x i‖ ≤ 1) (hMlt : ∀ x i, M x i ≠ 0 → lt i = x.1)
    (be : MvPowerSeries (ZMod d) K) (m : ι →₀ ℕ) :
    ‖MvPowerSeries.coeff m (bSum M be)‖ ≤ ‖MvPowerSeries.coeff (m.mapDomain lt) be‖ := by sorry
