-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_card_UT
-- name    : Formalism.FourierDecayAlt.P.G5.card_UT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:42:16.620807+00:00
-- url     : https://prove2.me/theorems/f3687a3f-e248-4ff0-9415-87570ba17f0a
-- title:
--   G5: card UT
-- statement:
--   The G5 construction uses the card UT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L100-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L100-L108

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

theorem Formalism.FourierDecayAlt.P.G5.card_UT (n : ℕ) : Fintype.card (UT n) = ∑ i ∈ Finset.range n, i := by sorry
