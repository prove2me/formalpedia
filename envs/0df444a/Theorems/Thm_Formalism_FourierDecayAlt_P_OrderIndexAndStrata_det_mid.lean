-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_det_mid
-- name    : Formalism.FourierDecayAlt.P.OrderIndexAndStrata.det_mid
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:58.951913+00:00
-- url     : https://prove2.me/theorems/932247ad-2724-4bad-b47b-89ea143b8642
-- title:
--   Order Index And Strata: det mid
-- statement:
--   The Order Index And Strata construction uses the det mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderIndexAndStrata.lean#L129-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderIndexAndStrata.lean#L129-L146

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrderIndexAndStrata
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3

theorem Formalism.FourierDecayAlt.P.OrderIndexAndStrata.det_mid {A : Type} [CommRing A] {r k : ℕ} (x : Matrix (Idx r k) (Idx r k) A) (hx : IsUnit x.det)
    (h21 : b21 x = 0) (h31 : b31 x = 0) (h32 : b32 x = 0) : IsUnit (b22 x).det := by sorry
