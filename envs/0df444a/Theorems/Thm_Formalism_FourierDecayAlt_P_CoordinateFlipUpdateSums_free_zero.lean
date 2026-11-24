-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CoordinateFlipUpdateSums_free_zero
-- name    : Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.free_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:35:13.879841+00:00
-- url     : https://prove2.me/theorems/0f4ba00f-fd00-416e-bf29-7f421556635f
-- title:
--   Coordinate Flip Update Sums: free zero
-- statement:
--   The Coordinate Flip Update Sums construction uses the free zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionUpdateSums.lean#L47-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionUpdateSums.lean#L47-L52

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_free_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.free_zero {a : S} {G : SlopeTestRemainingChoices S A} (hG : FreeOf a G) (u y : Ix S) (h : u a ≠ y a) :
    G u y = 0 := by sorry
