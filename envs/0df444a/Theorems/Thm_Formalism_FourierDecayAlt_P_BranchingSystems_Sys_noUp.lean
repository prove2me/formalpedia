-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_Sys_noUp
-- name    : Formalism.FourierDecayAlt.P.BranchingSystems.Sys.noUp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:50:42.147483+00:00
-- url     : https://prove2.me/theorems/c3917c38-0d33-4e6c-a25b-9053bc0d9190
-- title:
--   Sys: no Up
-- statement:
--   The Sys construction uses the no Up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L82-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L82-L106

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
variable {n : ℕ} {L : Fin (n + 1) → ℤ} {P : (Fin n → ℤ) → Prop}

theorem Formalism.FourierDecayAlt.P.BranchingSystems.Sys.noUp (h : Sys L P) (M : Fin n → ℤ) (hM : Box L M) (i : Fin n) (hi : M i = L i.castSucc) :
    ¬ P (Function.update M i (M i + 1)) := by sorry
