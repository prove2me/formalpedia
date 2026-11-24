-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_poisson_level_joint
-- name    : Formalism.FourierDecayAlt.P.poisson_level_joint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:31.904432+00:00
-- url     : https://prove2.me/theorems/25e6a11a-ad58-46cf-bbd0-e5fafa544ea0
-- title:
--   P: poisson level joint
-- statement:
--   The P construction uses the poisson level joint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonJointFirstReduction.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PoissonJointFirstReduction.lean#L31-L39

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonJointFirstReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.poisson_level_joint : Formalism.FourierDecayAlt.J.PoissonStepJoint := by sorry
