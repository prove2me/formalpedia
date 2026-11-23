-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_cj_of_eq
-- name    : Formalism.FourierDecayAlt.P.RuleGD.cj_of_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:51.971691+00:00
-- url     : https://prove2.me/theorems/963e095f-6dba-4139-923c-837e718241fb
-- title:
--   Rule GD: cj of eq
-- statement:
--   The Rule GD construction uses the cj of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L29-L30

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleGD
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
variable (g gi : A) (h : g * gi = 1) (h' : gi * g = 1)

theorem Formalism.FourierDecayAlt.P.RuleGD.cj_of_eq {x a : A} (hx : x * g = g * x + a * g) : cj g gi h h' x = x + cj g gi h h' a := by sorry
