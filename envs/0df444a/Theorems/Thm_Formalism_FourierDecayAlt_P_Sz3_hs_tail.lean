-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_hs_tail
-- name    : Formalism.FourierDecayAlt.P.Sz3.hs_tail
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:08.794274+00:00
-- url     : https://prove2.me/theorems/6d0b8727-e2a2-4b28-899b-18e005b42a09
-- title:
--   Sz3: hs tail
-- statement:
--   The Sz3 construction uses the hs tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L239-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L239-L259

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

theorem Formalism.FourierDecayAlt.P.Sz3.hs_tail (p : ℕ) (hp : 1 ≤ p) : hs (2 * p) - hs p ≤ 7 / 10 - 1 / (4 * (p : ℝ) + 1) := by sorry
