-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_Wb_mono
-- name    : Formalism.FourierDecayAlt.P.BaseGramNonnegativity.Wb_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:58.036861+00:00
-- url     : https://prove2.me/theorems/27a67dea-7fc1-41c3-aa9b-689449b6fd5a
-- title:
--   Base Gram Nonnegativity: Wb mono
-- statement:
--   The Base Gram Nonnegativity construction uses the Wb mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockEstimatesSumForm.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockEstimatesSumForm.lean#L81-L84

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

theorem Formalism.FourierDecayAlt.P.BaseGramNonnegativity.Wb_mono {n m : ℕ} (h : n ≤ m) : D.Wb n ⊆ D.Wb m := by sorry
