-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_mult_single_eU
-- name    : Formalism.FourierDecayAlt.P.Fr11.mult_single_eU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:20.172156+00:00
-- url     : https://prove2.me/theorems/99845de4-18ec-4af7-9489-b87a2796105f
-- title:
--   Fr11: mult single e U
-- statement:
--   The Fr11 construction uses the mult single e U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L143-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L143-L148

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

theorem Formalism.FourierDecayAlt.P.Fr11.mult_single_eU (l : Letter ℂ S) (γ : ℂ) (b : S) (hb : l.intersection_update_fsHerm_neg_one ≠ b) (i j : Fin 2) :
    (mult [l] γ * eU b i j : SlopeTestRemainingChoices S A) = eU b i j * mult [l] γ := by sorry
