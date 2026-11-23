-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Fr11_dg_smul
-- name    : Formalism.FourierDecayAlt.P.Fr11.dg_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:12.703076+00:00
-- url     : https://prove2.me/theorems/179467ec-7d05-4d2e-869b-2183549bde47
-- title:
--   Fr11: dg smul
-- statement:
--   The Fr11 construction uses the dg smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ResidueForm.lean#L23-L27

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

theorem Formalism.FourierDecayAlt.P.Fr11.dg_smul (c : ℂ) (g : Ix S → ℂ) : (c • dg g : SlopeTestRemainingChoices S A) = dg (fun e => c * g e) := by sorry
