-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_shf_down
-- name    : Formalism.FourierDecayAlt.P.BranchingSystems.shf_down
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:52:19.007535+00:00
-- url     : https://prove2.me/theorems/42895a30-d303-4908-9858-aed33cf24b27
-- title:
--   Branching Systems: shf down
-- statement:
--   The Branching Systems construction uses the shf down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L152-L156

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

theorem Formalism.FourierDecayAlt.P.BranchingSystems.shf_down {n : ℕ} (β : ℂ) (M : Fin n → ℤ) (i : Fin n) :
    Function.update (shf β M) i (shf β M i - 1) = shf β (Function.update M i (M i - 1)) := by sorry
