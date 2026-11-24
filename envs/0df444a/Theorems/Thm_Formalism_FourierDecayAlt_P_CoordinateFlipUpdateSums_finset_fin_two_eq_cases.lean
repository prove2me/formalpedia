-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CoordinateFlipUpdateSums_finset_fin_two_eq_cases
-- name    : Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.finset_fin_two_eq_cases
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:41.82998+00:00
-- url     : https://prove2.me/theorems/69488c9e-f530-42c4-8e43-48f8af694aff
-- title:
--   Coordinate Flip Update Sums: finset fin two eq cases
-- statement:
--   The Coordinate Flip Update Sums construction uses the finset fin two eq cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionUpdateSums.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionUpdateSums.lean#L14-L16

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

theorem Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.finset_fin_two_eq_cases (i : Fin 2) : i = 0 ∨ i = 1 := by sorry
