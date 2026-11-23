-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_hs_succ
-- name    : Formalism.FourierDecayAlt.P.Sz3.hs_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:55.290795+00:00
-- url     : https://prove2.me/theorems/875b34c2-78dc-4625-a267-08343556a69a
-- title:
--   Sz3: hs succ
-- statement:
--   The Sz3 construction uses the hs succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L231-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L231-L235

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz3.hs_succ (n : ℕ) : hs (n + 1) = hs n + 1 / ((n : ℝ) + 1) := by sorry
