-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G1_hasDerivAt_inv_lin
-- name    : Formalism.FourierDecayAlt.P.G1.hasDerivAt_inv_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:56.81886+00:00
-- url     : https://prove2.me/theorems/cd0bd0ee-394a-49cd-ae94-8e0558b3e744
-- title:
--   G1: has Deriv At inv lin
-- statement:
--   The G1 construction uses the has Deriv At inv lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L26-L31

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

theorem Formalism.FourierDecayAlt.P.G1.hasDerivAt_inv_lin (c Q a : ℂ) (ha : a ≠ 0) (hQ : Q ≠ 0) :
    HasDerivAt (fun ξ : ℂ => c / (ξ * Q)) (-(c / (a * Q) / a)) a := by sorry
