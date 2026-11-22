-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_ofFn_shift
-- name    : Formalism.FourierDecayAlt.P.RuleSS.ofFn_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:53:53.438172+00:00
-- url     : https://prove2.me/theorems/0b32511e-06b7-4d83-b810-696b6a72a8b8
-- title:
--   Rule SS: of Fn shift
-- statement:
--   The Rule SS construction uses the of Fn shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L32-L44

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem Formalism.FourierDecayAlt.P.RuleSS.ofFn_shift (x : A) :
    ∀ (n : ℕ) (f : Fin n → A) (k : Fin n → ℂ), (∀ m, x * f m = f m * (x + algebraMap ℂ A (k m))) →
      x * (List.ofFn f).prod = (List.ofFn f).prod * (x + algebraMap ℂ A (∑ m, k m))
  := by sorry
