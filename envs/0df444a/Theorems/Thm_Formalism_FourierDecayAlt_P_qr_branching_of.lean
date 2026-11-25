-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_qr_branching_of
-- name    : Formalism.FourierDecayAlt.P.qr_branching_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:19:35.451265+00:00
-- url     : https://prove2.me/theorems/f13ee48c-5b1f-4246-a2a0-189478cfd67b
-- title:
--   P: qr branching of
-- statement:
--   The P construction uses the qr branching of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductIntervalFrames.lean#L145-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ProductIntervalFrames.lean#L145-L152

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductIntervalFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem Formalism.FourierDecayAlt.P.qr_branching_of : Qr.BranchingK → Formalism.FourierDecayAlt.Q.Branching := by sorry
