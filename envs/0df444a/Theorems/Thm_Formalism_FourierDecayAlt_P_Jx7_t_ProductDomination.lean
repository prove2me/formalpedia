-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_t_ProductDomination
-- name    : Formalism.FourierDecayAlt.P.Jx7.t_ProductDomination
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:50:48.702369+00:00
-- url     : https://prove2.me/theorems/cb991248-4e1d-414a-b32b-a7ca0d84b177
-- title:
--   Jx7: t Product Domination
-- statement:
--   The Jx7 construction uses the t Product Domination property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L878-L880
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JointInstanceTheoremA.lean#L878-L880

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

theorem Formalism.FourierDecayAlt.P.Jx7.t_ProductDomination : ProductDomination := by sorry
