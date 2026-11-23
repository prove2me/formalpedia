-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_Ph_sum
-- name    : Formalism.FourierDecayAlt.P.Fr11.Ph_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:04.128799+00:00
-- url     : https://prove2.me/theorems/bb047b66-0b3b-4ea6-8d91-3e73e05b9750
-- title:
--   Fr11: Ph sum
-- statement:
--   The Fr11 construction uses the Ph sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L88-L92

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
variable {B : Type} [Ring B] [Algebra ℂ B] (p0 p1 : B) (c : ℂ)

theorem Formalism.FourierDecayAlt.P.Fr11.Ph_sum {J : Type} (s : Finset J) (U V : J → B) :
    Ph p0 p1 c (∑ j ∈ s, U j) (∑ j ∈ s, V j) = ∑ j ∈ s, Ph p0 p1 c (U j) (V j) := by sorry
