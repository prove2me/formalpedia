-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Rec_pow_bound
-- name    : Formalism.FourierDecayAlt.P.Rec.pow_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:56.626916+00:00
-- url     : https://prove2.me/theorems/f85460c8-b450-47d0-961f-9c16f8951bb0
-- title:
--   Rec: pow bound
-- statement:
--   The Rec construction uses the pow bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L123-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SharpRecursion.lean#L123-L149

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

theorem Formalism.FourierDecayAlt.P.Rec.pow_bound (r : ℕ) (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (hx : ((r:ℝ) + 1) * (ε + a) ≤ 1) :
    ((1 + ε + 2 * a) ^ (r+1)) ^ 2 ≤ 1 + 80 * ((r:ℝ) + 1) * (ε + a) := by sorry
