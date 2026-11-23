-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mult_cons
-- name    : Formalism.FourierDecayAlt.P.Fr11.mult_cons
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:33:03.827874+00:00
-- url     : https://prove2.me/theorems/0aaf75e5-4679-4084-a246-b362d443f855
-- title:
--   Fr11: mult cons
-- statement:
--   The Fr11 construction uses the mult cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L122-L124

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

theorem Formalism.FourierDecayAlt.P.Fr11.mult_cons (l : Letter ℂ S) (v : List (Letter ℂ S)) (γ : ℂ) :
    (mult (l :: v) γ : SlopeTestRemainingChoices S A) = mult [l] γ * mult v γ := by sorry
