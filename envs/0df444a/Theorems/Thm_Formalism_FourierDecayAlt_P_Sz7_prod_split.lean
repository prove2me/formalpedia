-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz7_prod_split
-- name    : Formalism.FourierDecayAlt.P.Sz7.prod_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:06.318806+00:00
-- url     : https://prove2.me/theorems/521e151c-0d33-47b7-bf11-35eb3422f88c
-- title:
--   Sz7: prod split
-- statement:
--   The Sz7 construction uses the prod split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaBoundOnBoundary.lean#L149-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaBoundOnBoundary.lean#L149-L161

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_prod_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz7
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz7.prod_split (f : ℕ → ℝ) (k l : ℕ) (hl : 1 ≤ l) (hlk : l + 2 ≤ k) :
    ∏ i ∈ Icc 1 (k - 1), f i =
      (∏ i ∈ Ico 1 l, f i) * (f l * ((∏ i ∈ Ico (l + 1) (k - 1), f i) * f (k - 1))) := by sorry
