-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_shf_update
-- name    : Formalism.FourierDecayAlt.P.BranchingSystems.shf_update
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:51:49.707529+00:00
-- url     : https://prove2.me/theorems/e92d64f6-1ce4-4ae5-8c6c-b9c5004f2c1d
-- title:
--   Branching Systems: shf update
-- statement:
--   The Branching Systems construction uses the shf update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L138-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L138-L144

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

theorem Formalism.FourierDecayAlt.P.BranchingSystems.shf_update {n : ℕ} (β : ℂ) (M : Fin n → ℤ) (i : Fin n) (t : ℤ) :
    Function.update (shf β M) i (β + (t : ℂ)) = shf β (Function.update M i t) := by sorry
