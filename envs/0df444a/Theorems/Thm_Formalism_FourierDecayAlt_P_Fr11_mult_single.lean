-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mult_single
-- name    : Formalism.FourierDecayAlt.P.Fr11.mult_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:44.720644+00:00
-- url     : https://prove2.me/theorems/9946e724-b6d0-4075-acfd-b08059c749fe
-- title:
--   Fr11: mult single
-- statement:
--   The Fr11 construction uses the mult single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L126-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L126-L134

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

theorem Formalism.FourierDecayAlt.P.Fr11.mult_single (l : Letter ℂ S) (γ : ℂ) :
    (mult [l] γ : SlopeTestRemainingChoices S A) =
      (1 + 1 / (l.pt - γ)) • eU l.intersection_update_fsHerm_neg_one 0 0 + (1 - 1 / (l.pt - γ)) • eU l.intersection_update_fsHerm_neg_one 1 1 := by sorry
