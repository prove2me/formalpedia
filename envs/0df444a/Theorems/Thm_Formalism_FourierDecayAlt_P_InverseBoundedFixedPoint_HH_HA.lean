-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_HH_HA
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.HH_HA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:56.728798+00:00
-- url     : https://prove2.me/theorems/2ceb1dc4-8464-425d-a2b3-bc4666a4c641
-- title:
--   Inverse Bounded Fixed Point: HH HA
-- statement:
--   The Inverse Bounded Fixed Point construction uses the HH HA property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L598-L603
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L598-L603

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] {m : ℕ}

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.HH_HA : HH K m * HA K m = ((m + 1 : ℕ) : K) • (1 : Matrix (Fin m) (Fin m) K) := by sorry
