-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_SchurProduct
-- name    : Formalism.FourierDecayAlt.P.Jx7.t_SchurProduct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:50:41.379365+00:00
-- url     : https://prove2.me/theorems/106fa406-82ff-4937-ad52-ab4ae1b13cf5
-- title:
--   Jx7: t Schur Product
-- statement:
--   The Jx7 construction uses the t Schur Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L874-L876
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L874-L876

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
open scoped ComplexOrder ComplexConjugate Matrix

theorem Formalism.FourierDecayAlt.P.Jx7.t_SchurProduct : SchurProduct := by sorry
