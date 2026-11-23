-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_io_smul
-- name    : Formalism.FourierDecayAlt.P.Fr11.io_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:16.545976+00:00
-- url     : https://prove2.me/theorems/10e0d573-b9b9-493f-aade-c43fd3e5c6aa
-- title:
--   Fr11: io smul
-- statement:
--   The Fr11 construction uses the io smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L218-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L218-L221

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

theorem Formalism.FourierDecayAlt.P.Fr11.io_smul (c : ℂ) (x : A) : (io (c • x) : SlopeTestRemainingChoices S A) = c • io x := by sorry
