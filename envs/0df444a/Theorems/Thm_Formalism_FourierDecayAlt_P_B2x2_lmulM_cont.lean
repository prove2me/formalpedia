-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lmulM_cont
-- name    : Formalism.FourierDecayAlt.P.B2x2.lmulM_cont
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:41:30.277731+00:00
-- url     : https://prove2.me/theorems/14560a2a-e33f-47cd-8dca-37a1fede446a
-- title:
--   B2x2: lmul M cont
-- statement:
--   The B2x2 construction uses the lmul M cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L245-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L245-L248

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

theorem Formalism.FourierDecayAlt.P.B2x2.lmulM_cont {k r : ℕ} (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by sorry
