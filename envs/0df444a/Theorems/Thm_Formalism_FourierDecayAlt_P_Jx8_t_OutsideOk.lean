-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_t_OutsideOk
-- name    : Formalism.FourierDecayAlt.P.Jx8.t_OutsideOk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:51:02.604976+00:00
-- url     : https://prove2.me/theorems/3d208a41-7625-43ae-b11c-529d068993be
-- title:
--   Jx8: t Outside Ok
-- statement:
--   The Jx8 construction uses the t Outside Ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L29-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L29-L54

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8

theorem Formalism.FourierDecayAlt.P.Jx8.t_OutsideOk : OutsideOk := by sorry
