-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CoordinateFlipUpdateSums_act_place
-- name    : Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.act_place
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:35:00.266299+00:00
-- url     : https://prove2.me/theorems/8aa69a17-fdf5-4549-a65e-ad7f4d914cdf
-- title:
--   Coordinate Flip Update Sums: act place
-- statement:
--   The Coordinate Flip Update Sums construction uses the act place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionUpdateSums.lean#L89-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PositionUpdateSums.lean#L89-L110

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
variable {A S V : Type} [Ring A] [Fintype S] [DecidableEq S] [AddCommGroup V] [Module A V]

theorem Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums.act_place {a : S} {G : SlopeTestRemainingChoices S A} (hG : FreeOf a G) (X : Ix S → V)
    (hX : ∀ u, u a ≠ 0 → X u = 0) (C : Fin 2 → A) (z : Ix S) :
    act G (fun u => C (u a) • X (Function.update u a 0)) z =
      act G (C (z a) • X) (Function.update z a 0) := by sorry
