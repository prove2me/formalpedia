-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_shift_prod
-- name    : Formalism.FourierDecayAlt.P.RuleGD.shift_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:02.78881+00:00
-- url     : https://prove2.me/theorems/15d55afe-ff8b-4814-a942-28dac5722f21
-- title:
--   Rule GD: shift prod
-- statement:
--   The Rule GD construction uses the shift prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleGD.lean#L46-L55

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

theorem Formalism.FourierDecayAlt.P.RuleGD.shift_prod {n : ℕ} (f : Fin n → A) (x : A) (a : Fin n → ℂ)
    (hx : ∀ i, x * f i = f i * x + a i • f i) :
    x * (List.ofFn f).prod = (List.ofFn f).prod * x + (∑ i, a i) • (List.ofFn f).prod := by sorry
