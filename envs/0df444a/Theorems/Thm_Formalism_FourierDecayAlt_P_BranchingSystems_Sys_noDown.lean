-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_Sys_noDown
-- name    : Formalism.FourierDecayAlt.P.BranchingSystems.Sys.noDown
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:51:01.368572+00:00
-- url     : https://prove2.me/theorems/581de722-c20a-4680-bdc8-bdaa83c3e535
-- title:
--   Sys: no Down
-- statement:
--   The Sys construction uses the no Down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L108-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L108-L134

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BranchingSystems
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ

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
variable {n : ℕ} {L : Fin (n + 1) → ℤ} {P : (Fin n → ℤ) → Prop}

theorem Formalism.FourierDecayAlt.P.BranchingSystems.Sys.noDown (h : Sys L P) (M : Fin n → ℤ) (hM : Box L M) (i : Fin n) (hi : M i = L i.succ + 1) :
    ¬ P (Function.update M i (M i - 1)) := by sorry
