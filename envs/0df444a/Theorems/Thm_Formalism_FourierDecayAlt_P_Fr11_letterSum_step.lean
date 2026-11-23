-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_letterSum_step
-- name    : Formalism.FourierDecayAlt.P.Fr11.letterSum_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:15.595805+00:00
-- url     : https://prove2.me/theorems/1ae9dea6-15e3-4d98-b0ca-c532f9aab4cf
-- title:
--   Fr11: letter Sum step
-- statement:
--   The Fr11 construction uses the letter Sum step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L165-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L165-L175

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

theorem Formalism.FourierDecayAlt.P.Fr11.letterSum_step (l : Letter ℂ S) (Y : ℂ) (hY : Y ≠ l.pt) :
    ∀ (w v : List (Letter ℂ S)), (∀ l' ∈ w, l.intersection_update_fsHerm_neg_one ≠ l'.intersection_update_fsHerm_neg_one ∧ Y ≠ l'.pt ∧ l.pt ≠ l'.pt) →
      Ph (eU l.intersection_update_fsHerm_neg_one 0 0 : SlopeTestRemainingChoices S A) (eU l.intersection_update_fsHerm_neg_one 1 1) (Y - l.pt)⁻¹ (letterSum v w Y) (letterSum v w l.pt) =
        letterSum (l :: v) w Y
  := by sorry
