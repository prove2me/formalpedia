-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_invM_contOn
-- name    : Formalism.FourierDecayAlt.P.B2x2.invM_contOn
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:53:25.928875+00:00
-- url     : https://prove2.me/theorems/da5f1653-b7d8-4101-9974-2d3deb2b6b51
-- title:
--   B2x2: inv M cont On
-- statement:
--   The B2x2 construction uses the inv M cont On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L515-L516
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L515-L516

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

theorem Formalism.FourierDecayAlt.P.B2x2.invM_contOn {k r : ℕ} : ContinuousOn (invM : Mt k r → Mt k r) {x | IsUnit (Matrix.of x : Mat k r).det} := by sorry
