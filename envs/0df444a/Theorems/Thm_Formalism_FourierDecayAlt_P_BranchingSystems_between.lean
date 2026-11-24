-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BranchingSystems_between
-- name    : Formalism.FourierDecayAlt.P.BranchingSystems.between
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:51:11.170138+00:00
-- url     : https://prove2.me/theorems/3e4920b8-c07c-48b1-be91-97bbc8cda909
-- title:
--   Branching Systems: between
-- statement:
--   The Branching Systems construction uses the between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BranchingSystems.lean#L12-L21

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

theorem Formalism.FourierDecayAlt.P.BranchingSystems.between {n : ℕ} {L : Fin (n + 1) → ℤ} (hL : StrictAnti L) (i : Fin n) {x : ℤ}
    (h1 : L i.succ < x) (h2 : x < L i.castSucc) (j : Fin (n + 1)) : x ≠ L j := by sorry
