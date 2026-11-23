-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_rowRad_nonneg
-- name    : Formalism.DworkPowerSeriesWeights.jet_rowRad_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:03:32.757006+00:00
-- url     : https://prove2.me/theorems/55b57b40-25f4-4ccb-b2fa-15acda484b14
-- title:
--   Dwork Power Series Weights: jet row Rad nonneg
-- statement:
--   The Dwork Power Series Weights construction uses the jet row Rad nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAJet.lean#L200-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAJet.lean#L200-L205

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
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs

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

theorem Formalism.DworkPowerSeriesWeights.jet_rowRad_nonneg {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (hs : ∀ s, 0 ≤ sig s)
    (he : ∀ s, 0 ≤ eps s) (i : ι) : 0 ≤ rowRad l sig eps lt isTop spec i := by sorry
