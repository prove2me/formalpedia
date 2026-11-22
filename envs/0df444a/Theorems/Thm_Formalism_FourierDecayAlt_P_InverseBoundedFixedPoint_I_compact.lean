-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_I_compact
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.I_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:57:06.633974+00:00
-- url     : https://prove2.me/theorems/1e547cec-c95b-4ae3-8840-ce9acdb83ce0
-- title:
--   Inverse Bounded Fixed Point: I compact
-- statement:
--   The Inverse Bounded Fixed Point construction uses the I compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L24-L30

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.I_compact {R : Subring K} (hc : IsCompact (R : Set K)) (a : K) : IsCompact (I R a) := by sorry
