-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_prod_le_of_ratio
-- name    : Formalism.FourierDecayAlt.P.Sz4.prod_le_of_ratio
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:10.334817+00:00
-- url     : https://prove2.me/theorems/92369107-78b4-495b-8b3f-36c28007f701
-- title:
--   Sz4: prod le of ratio
-- statement:
--   The Sz4 construction uses the prod le of ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L652-L655
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L652-L655

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz4.prod_le_of_ratio (s : Finset ℕ) (f g : ℕ → ℝ) (A : ℝ) (hg : ∀ i ∈ s, 0 < g i)
    (h : ∏ i ∈ s, f i / g i ≤ A) : ∏ i ∈ s, f i ≤ A * ∏ i ∈ s, g i := by sorry
