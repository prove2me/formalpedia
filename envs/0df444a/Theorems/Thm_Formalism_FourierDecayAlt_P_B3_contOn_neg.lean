-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_contOn_neg
-- name    : Formalism.FourierDecayAlt.P.B3.contOn_neg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:27:26.337794+00:00
-- url     : https://prove2.me/theorems/5b46e942-6e92-42e4-a7cf-78b443670e3b
-- title:
--   B3: cont On neg
-- statement:
--   The B3 construction uses the cont On neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L257-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L257-L259

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B

theorem Formalism.FourierDecayAlt.P.B3.contOn_neg {h : ℝ × ℝ → ℝ} (hh : ContinuousOn h Quad) : ContinuousOn (fun τ => max (-h τ) 0) Quad := by sorry
