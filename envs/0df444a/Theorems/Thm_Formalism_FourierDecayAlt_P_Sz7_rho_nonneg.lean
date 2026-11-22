-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz7_rho_nonneg
-- name    : Formalism.FourierDecayAlt.P.Sz7.rho_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:16:24.715235+00:00
-- url     : https://prove2.me/theorems/c426c96a-8294-4399-a371-2b36312952d8
-- title:
--   Sz7: rho nonneg
-- statement:
--   The Sz7 construction uses the rho nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaBoundOnBoundary.lean#L71-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaBoundOnBoundary.lean#L71-L84

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaFactorisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaBoundOnBoundary
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

theorem Formalism.FourierDecayAlt.P.Sz7.rho_nonneg (c : Cfg) (de de' : ℕ → ℝ) (Y : ℝ) (l i : ℕ) (h : c.Ok)
    (hlk : l + 2 ≤ c.k) (hY : Y ∈ c.cutI l) : 0 ≤ c.rho de de' (-Y) i := by sorry
