-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_dg_add
-- name    : Formalism.FourierDecayAlt.P.Fr11.dg_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:02.00465+00:00
-- url     : https://prove2.me/theorems/0f0d9b42-5ba8-4dbd-8d67-658a210dca40
-- title:
--   Fr11: dg add
-- statement:
--   The Fr11 construction uses the dg add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L18-L21

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

theorem Formalism.FourierDecayAlt.P.Fr11.dg_add (g h : Ix S → ℂ) : (dg g + dg h : SlopeTestRemainingChoices S A) = dg (fun e => g e + h e) := by sorry
