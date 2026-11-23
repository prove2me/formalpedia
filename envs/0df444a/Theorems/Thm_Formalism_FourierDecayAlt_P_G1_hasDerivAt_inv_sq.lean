-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G1_hasDerivAt_inv_sq
-- name    : Formalism.FourierDecayAlt.P.G1.hasDerivAt_inv_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:07.32718+00:00
-- url     : https://prove2.me/theorems/c206bdcf-7744-4038-afef-08c357be527e
-- title:
--   G1: has Deriv At inv sq
-- statement:
--   The G1 construction uses the has Deriv At inv sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L33-L38

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G1
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G1.hasDerivAt_inv_sq (c Q a : ℂ) (ha : a ≠ 0) (hQ : Q ≠ 0) :
    HasDerivAt (fun ξ : ℂ => c / (ξ * Q) / ξ) (-(2 * c / (a * Q * a * a))) a := by sorry
