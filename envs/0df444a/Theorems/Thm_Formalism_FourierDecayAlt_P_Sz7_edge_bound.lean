-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz7_edge_bound
-- name    : Formalism.FourierDecayAlt.P.Sz7.edge_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:39.106948+00:00
-- url     : https://prove2.me/theorems/4317dfa8-c0f3-433e-b12a-2d66799666b1
-- title:
--   Sz7: edge bound
-- statement:
--   The Sz7 construction uses the edge bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaBoundOnBoundary.lean#L105-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaBoundOnBoundary.lean#L105-L147

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

theorem Formalism.FourierDecayAlt.P.Sz7.edge_bound (c : Cfg) (de de' : ℕ → ℝ) (Y : ℝ) (l : ℕ) (h : c.Ok) (hw : IsWord c.k de)
    (hw' : IsWord c.k de') (hl : 1 ≤ l) (hlk : l + 2 ≤ c.k) (hY : Y ∈ c.cutI l) :
    0 < c.aeff ∧ c.U1 (-Y) * c.rho de de' (-Y) (c.k - 1) ≤ 8 / c.aeff := by sorry
