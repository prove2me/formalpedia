-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_shiftSmall_statement
-- name    : Formalism.FourierDecayAlt.P.shiftSmall_statement
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:09.732004+00:00
-- url     : https://prove2.me/theorems/3950689e-f33f-4165-97ec-56f200fa0cde
-- title:
--   P: shift Small statement
-- statement:
--   The P construction uses the shift Small statement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L466-L466
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L466-L466

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate

theorem Formalism.FourierDecayAlt.P.shiftSmall_statement : Formalism.FourierDecayAlt.A6.ShiftSmall := by sorry
