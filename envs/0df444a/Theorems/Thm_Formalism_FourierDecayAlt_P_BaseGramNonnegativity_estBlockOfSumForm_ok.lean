-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_estBlockOfSumForm_ok
-- name    : Formalism.FourierDecayAlt.P.BaseGramNonnegativity.estBlockOfSumForm_ok
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:06.459237+00:00
-- url     : https://prove2.me/theorems/03104112-b82b-4534-af98-5b250a17c057
-- title:
--   Base Gram Nonnegativity: est Block Of Sum Form ok
-- statement:
--   The Base Gram Nonnegativity construction uses the est Block Of Sum Form ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockEstimatesSumForm.lean#L86-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockEstimatesSumForm.lean#L86-L106

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

theorem Formalism.FourierDecayAlt.P.BaseGramNonnegativity.estBlockOfSumForm_ok : EstBlockOfSumForm := by sorry
