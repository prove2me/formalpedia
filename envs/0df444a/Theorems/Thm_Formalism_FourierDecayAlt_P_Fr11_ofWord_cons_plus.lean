-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_ofWord_cons_plus
-- name    : Formalism.FourierDecayAlt.P.Fr11.ofWord_cons_plus
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:04.373931+00:00
-- url     : https://prove2.me/theorems/c0103ca7-7193-4cb2-bc0a-612d5b4d52cb
-- title:
--   Fr11: of Word cons plus
-- statement:
--   The Fr11 construction uses the of Word cons plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L181-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L181-L183

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
variable {r : ℕ} (L : LevelData A r) (st : Start A)

theorem Formalism.FourierDecayAlt.P.Fr11.ofWord_cons_plus (l : Letter ℂ S) (w : List (Letter ℂ S)) (h : l.plus = true) :
    ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by sorry
