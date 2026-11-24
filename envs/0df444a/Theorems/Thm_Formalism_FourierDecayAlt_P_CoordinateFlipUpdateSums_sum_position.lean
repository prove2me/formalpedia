-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CoordinateFlipUpdateSums_sum_position
-- name    : Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.sum_position
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:31.076491+00:00
-- url     : https://prove2.me/theorems/448cde4b-935f-45c6-a9a0-fc8c68b7ed26
-- title:
--   Coordinate Flip Update Sums: sum position
-- statement:
--   The Coordinate Flip Update Sums construction uses the sum position property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionUpdateSums.lean#L27-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionUpdateSums.lean#L27-L42

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

theorem Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.sum_position {M : Type} [AddCommMonoid M] (a : S) (F : Ix S → M) :
    ∑ u, F u = ∑ u, if u a = 0 then F u + F (Function.update u a 1) else 0 := by sorry
