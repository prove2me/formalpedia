-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_two_card_UT
-- name    : Formalism.FourierDecayAlt.P.G5.two_card_UT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:48.35944+00:00
-- url     : https://prove2.me/theorems/f5e19ed2-702d-441a-8ab1-393896802450
-- title:
--   G5: two card UT
-- statement:
--   The G5 construction uses the two card UT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L110-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L110-L111

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G5.two_card_UT (n : ℕ) : 2 * Fintype.card (UT n) = n * (n - 1) := by sorry
