-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_inv_contOn
-- name    : Formalism.FourierDecayAlt.P.B2x2.inv_contOn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:43:57.388802+00:00
-- url     : https://prove2.me/theorems/077ad486-a50f-433a-b2e8-1484b23df4d8
-- title:
--   B2x2: inv cont On
-- statement:
--   The B2x2 construction uses the inv cont On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L510-L513
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L510-L513

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2

theorem Formalism.FourierDecayAlt.P.B2x2.inv_contOn {n : ℕ} : ContinuousOn (fun x : Matrix (Fin n) (Fin n) ℂ => x⁻¹) {x | IsUnit x.det} := by sorry
