-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx2_t_LatticeSumsJoint
-- name    : Formalism.FourierDecayAlt.P.Jx2.t_LatticeSumsJoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:28.410375+00:00
-- url     : https://prove2.me/theorems/dc55321a-b3f4-4a4d-af46-0a6d8e3a421a
-- title:
--   Jx2: t Lattice Sums Joint
-- statement:
--   The Jx2 construction uses the t Lattice Sums Joint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSizesJointMean.lean#L124-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelSizesJointMean.lean#L124-L166

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate

theorem Formalism.FourierDecayAlt.P.Jx2.t_LatticeSumsJoint : LatticeSumsJoint := by sorry
