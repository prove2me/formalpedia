-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_sum_re_nonneg
-- name    : Formalism.FourierDecayAlt.P.BaseGramNonnegativity.sum_re_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:09.255199+00:00
-- url     : https://prove2.me/theorems/e6ee0d32-0ab3-4d6f-bc9c-b871514a7a29
-- title:
--   Base Gram Nonnegativity: sum re nonneg
-- statement:
--   The Base Gram Nonnegativity construction uses the sum re nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockEstimatesSumForm.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockEstimatesSumForm.lean#L11-L19

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

theorem Formalism.FourierDecayAlt.P.BaseGramNonnegativity.sum_re_nonneg {α : Type} (Y : Finset α) (κ G : α → α → ℂ) (hκ : PSDOn Y κ) (hG : PSDOn Y G) :
    0 ≤ (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * G h h').re := by sorry
