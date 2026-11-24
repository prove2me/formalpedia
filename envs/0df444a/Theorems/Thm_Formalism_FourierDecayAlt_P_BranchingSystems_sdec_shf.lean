-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_sdec_shf
-- name    : Formalism.FourierDecayAlt.P.BranchingSystems.sdec_shf
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:52:34.661054+00:00
-- url     : https://prove2.me/theorems/fee662a9-846e-48d1-a05a-d3daf6cb81e2
-- title:
--   Branching Systems: sdec shf
-- statement:
--   The Branching Systems construction uses the sdec shf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L158-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L158-L167

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BranchingSystems
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem Formalism.FourierDecayAlt.P.BranchingSystems.sdec_shf {n : ℕ} (β : ℂ) {L : Fin n → ℤ} (hL : StrictAnti L) : SDec (shf β L) := by sorry
