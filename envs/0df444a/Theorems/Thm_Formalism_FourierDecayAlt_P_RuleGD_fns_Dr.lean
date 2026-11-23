-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_fns_Dr
-- name    : Formalism.FourierDecayAlt.P.RuleGD.fns_Dr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:42:26.559325+00:00
-- url     : https://prove2.me/theorems/84797de9-8932-4a23-8ebf-616a3c0cfc0b
-- title:
--   Rule GD: fns Dr
-- statement:
--   The Rule GD construction uses the fns Dr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L211-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L211-L212

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

theorem Formalism.FourierDecayAlt.P.RuleGD.fns_Dr (L : LevelData A r) {x : A} (hx : x ∈ L.fns) : x * L.Dr = L.Dr * x := by sorry
