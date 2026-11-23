-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_quart
-- name    : Formalism.FourierDecayAlt.P.Rec.quart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:00.60485+00:00
-- url     : https://prove2.me/theorems/1e55d868-1c6c-472f-bce3-108d67c64a53
-- title:
--   Rec: quart
-- statement:
--   The Rec construction uses the quart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L117-L121

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Rec
open Finset Real

theorem Formalism.FourierDecayAlt.P.Rec.quart (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : (1 + 2 * x) ^ 4 ≤ 1 + 80 * x := by sorry
