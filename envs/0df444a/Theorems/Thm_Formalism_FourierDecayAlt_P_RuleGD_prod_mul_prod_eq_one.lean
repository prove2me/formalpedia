-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_prod_mul_prod_eq_one
-- name    : Formalism.FourierDecayAlt.P.RuleGD.prod_mul_prod_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:53:29.749954+00:00
-- url     : https://prove2.me/theorems/d89638a6-5183-44b4-b94a-e79a2b6e4728
-- title:
--   Rule GD: prod mul prod eq one
-- statement:
--   The Rule GD construction uses the prod mul prod eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L57-L65

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

theorem Formalism.FourierDecayAlt.P.RuleGD.prod_mul_prod_eq_one {n : ℕ} (f g : Fin n → A) (hfg : ∀ i, f i * g i = 1)
    (hc : ∀ i j, g i * f j = f j * g i) : (List.ofFn f).prod * (List.ofFn g).prod = 1 := by sorry
