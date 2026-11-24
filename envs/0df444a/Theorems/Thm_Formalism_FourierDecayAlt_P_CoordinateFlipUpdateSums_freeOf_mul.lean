-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CoordinateFlipUpdateSums_freeOf_mul
-- name    : Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.freeOf_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:35:27.056126+00:00
-- url     : https://prove2.me/theorems/0a2c0f8f-fb9c-424f-b42d-6c1bc271adc0
-- title:
--   Coordinate Flip Update Sums: free Of mul
-- statement:
--   The Coordinate Flip Update Sums construction uses the free Of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionUpdateSums.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionUpdateSums.lean#L61-L62

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealWeightedForms
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
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

theorem Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.freeOf_mul {a : S} {M N : SlopeTestRemainingChoices S A} (hM : FreeOf a M) (hN : FreeOf a N) : FreeOf a (M * N) := by sorry
