-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_R_PInv_prod_mul_prod_eq_one
-- name    : Formalism.FourierDecayAlt.R.PInv.prod_mul_prod_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:01:39.677864+00:00
-- url     : https://prove2.me/theorems/3d8299f6-d75a-4b8f-b199-3788fec8c257
-- title:
--   PInv: prod mul prod eq one
-- statement:
--   The PInv construction uses the prod mul prod eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L21-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L21-L38

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.PInv
open Matrix LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem Formalism.FourierDecayAlt.R.PInv.prod_mul_prod_eq_one : ∀ (n : ℕ) (f g : Fin n → A), (∀ i, f i * g i = 1) →
    (∀ i j, Commute (f i) (g j)) → (List.ofFn f).prod * (List.ofFn g).prod = 1
  := by sorry
