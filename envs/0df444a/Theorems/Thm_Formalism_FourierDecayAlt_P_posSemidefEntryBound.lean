-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_posSemidefEntryBound
-- name    : Formalism.FourierDecayAlt.P.posSemidefEntryBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:58.788152+00:00
-- url     : https://prove2.me/theorems/2d85a7ea-fea7-4ae5-8a84-4406c49a7253
-- title:
--   P: pos Semidef Entry Bound
-- statement:
--   The P construction uses the pos Semidef Entry Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PosSemidefEntryBound.lean#L188-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PosSemidefEntryBound.lean#L188-L188

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PosSemidefEntryBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.posSemidefEntryBound : Formalism.FourierDecayAlt.A6.PSDEntryBound := by sorry
