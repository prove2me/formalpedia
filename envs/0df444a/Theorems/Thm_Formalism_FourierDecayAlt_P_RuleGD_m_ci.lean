-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_ci
-- name    : Formalism.FourierDecayAlt.P.RuleGD.m_ci
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:27.03717+00:00
-- url     : https://prove2.me/theorems/ccac776f-cd0c-4c52-b46e-0347017c2b11
-- title:
--   Rule GD: m ci
-- statement:
--   The Rule GD construction uses the m ci property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L79-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L79-L79

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
variable (L : LevelData A r)

theorem Formalism.FourierDecayAlt.P.RuleGD.m_ci (l) : L.ci l ∈ L.fns := by sorry
