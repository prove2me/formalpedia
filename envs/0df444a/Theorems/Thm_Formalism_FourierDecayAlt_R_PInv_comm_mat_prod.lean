-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_R_PInv_comm_mat_prod
-- name    : Formalism.FourierDecayAlt.R.PInv.comm_mat_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:21.28404+00:00
-- url     : https://prove2.me/theorems/61b66049-655d-4dc5-9aae-0c30e50d41a3
-- title:
--   PInv: comm mat prod
-- statement:
--   The PInv construction uses the comm mat prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L9-L19

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

theorem Formalism.FourierDecayAlt.R.PInv.comm_mat_prod (x : A) :
    ∀ l : List (Matrix (Fin 2) (Fin 2) A), (∀ M ∈ l, ∀ i j, Commute x (M i j)) →
      ∀ i j, Commute x (l.prod i j)
  := by sorry
