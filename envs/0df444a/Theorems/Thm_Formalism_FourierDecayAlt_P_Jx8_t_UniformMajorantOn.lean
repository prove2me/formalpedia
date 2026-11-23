-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_t_UniformMajorantOn
-- name    : Formalism.FourierDecayAlt.P.Jx8.t_UniformMajorantOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:37.254673+00:00
-- url     : https://prove2.me/theorems/0e4a75f4-6b8d-4d36-89f5-e76784d02a6c
-- title:
--   Jx8: t Uniform Majorant On
-- statement:
--   The Jx8 construction uses the t Uniform Majorant On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L357-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L357-L430

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

theorem Formalism.FourierDecayAlt.P.Jx8.t_UniformMajorantOn : UniformMajorantOn := by sorry
