-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_rev_prod_inter
-- name    : Formalism.FourierDecayAlt.P.RuleSS.rev_prod_inter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:12.325685+00:00
-- url     : https://prove2.me/theorems/7f6aaa44-a7ca-40d7-b1b7-cd1e285c71c3
-- title:
--   Rule SS: rev prod inter
-- statement:
--   The Rule SS construction uses the rev prod inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleSS.lean#L23-L30

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

theorem Formalism.FourierDecayAlt.P.RuleSS.rev_prod_inter {M : Type} [Monoid M] (d : M) :
    ∀ (n : ℕ) (f g : Fin n → M), (∀ i, f i * d = d * g i) →
      (List.ofFn f).reverse.prod * d = d * (List.ofFn g).reverse.prod
  := by sorry
