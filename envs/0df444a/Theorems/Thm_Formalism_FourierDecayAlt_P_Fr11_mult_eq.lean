-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mult_eq
-- name    : Formalism.FourierDecayAlt.P.Fr11.mult_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:19.094554+00:00
-- url     : https://prove2.me/theorems/f13486bb-a168-4ad6-9c3b-b30b8e46f2d4
-- title:
--   Fr11: mult eq
-- statement:
--   The Fr11 construction uses the mult eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L115-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L115-L116

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

theorem Formalism.FourierDecayAlt.P.Fr11.mult_eq (v : List (Letter ℂ S)) (γ : ℂ) :
    (mult v γ : SlopeTestRemainingChoices S A) = dg fun e => (v.map fun l => 1 + sg (e l.intersection_update_fsHerm_neg_one) / (l.pt - γ)).prod := by sorry
