-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_comm_prod
-- name    : Formalism.FourierDecayAlt.P.RuleGD.comm_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:06:01.035724+00:00
-- url     : https://prove2.me/theorems/9f7871b3-1aba-4cef-872f-3ac1ab94798a
-- title:
--   Rule GD: comm prod
-- statement:
--   The Rule GD construction uses the comm prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L39-L44

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

theorem Formalism.FourierDecayAlt.P.RuleGD.comm_prod {n : ℕ} (f : Fin n → A) (x : A) (hx : ∀ i, x * f i = f i * x) :
    x * (List.ofFn f).prod = (List.ofFn f).prod * x := by sorry
