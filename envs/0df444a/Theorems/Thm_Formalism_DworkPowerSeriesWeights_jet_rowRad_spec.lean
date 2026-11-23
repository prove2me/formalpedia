-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_rowRad_spec
-- name    : Formalism.DworkPowerSeriesWeights.jet_rowRad_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:03:24.367659+00:00
-- url     : https://prove2.me/theorems/96a44bd3-cf9d-446f-af1c-08d5ca610e31
-- title:
--   Dwork Power Series Weights: jet row Rad spec
-- statement:
--   The Dwork Power Series Weights construction uses the jet row Rad spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAJet.lean#L212-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ThmAJet.lean#L212-L218

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

theorem Formalism.DworkPowerSeriesWeights.jet_rowRad_spec {d : ℕ} {ι : Type} (l : ℕ) (sig eps : ZMod d → ℝ) (lt : ι → ZMod d)
    (isTop : ι → Bool) (spec : ι → Option (ZMod d × ℤ)) (i : ι) (hi : isTop i = false)
    {s0 : ZMod d} {j : ℤ} (hs : spec i = some (s0, j)) :
    rowRad l sig eps lt isTop spec i = if 0 < j then max (sig (lt i)) (1 - (l : ℝ) ^ j.toNat * eps s0)
      else max (sig (lt i)) ((l : ℝ) ^ (-j).toNat)⁻¹ := by sorry
