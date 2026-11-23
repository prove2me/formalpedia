-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_baseGram_smul
-- name    : Formalism.FourierDecayAlt.P.BaseGramNonnegativity.baseGram_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:54.834917+00:00
-- url     : https://prove2.me/theorems/c283b8d7-a4cd-4999-844f-263a14cf3c4c
-- title:
--   Base Gram Nonnegativity: base Gram smul
-- statement:
--   The Base Gram Nonnegativity construction uses the base Gram smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockEstimatesSumForm.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockEstimatesSumForm.lean#L27-L29

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BaseGramNonnegativity
open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB
variable {E W : Type} [Field E] (D : Data E W)

theorem Formalism.FourierDecayAlt.P.BaseGramNonnegativity.baseGram_smul (ε : ℝ) (k : ℕ) (w : W) (Y : Finset (Pt E)) (r : ℝ) (κ : Pt E → Pt E → ℂ) :
    D.N0 ε k w Y (fun h h' => (r : ℂ) * κ h h') = r * D.N0 ε k w Y κ := by sorry
