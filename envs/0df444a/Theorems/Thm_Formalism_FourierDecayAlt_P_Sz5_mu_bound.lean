-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_mu_bound
-- name    : Formalism.FourierDecayAlt.P.Sz5.mu_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:19.252191+00:00
-- url     : https://prove2.me/theorems/4d43572e-4eca-44ce-abdb-b04b0e6e9912
-- title:
--   Sz5: mu bound
-- statement:
--   The Sz5 construction uses the mu bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L492-L528
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L492-L528

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz5.mu_bound (c : Cfg) (h : c.Ok) (bb : ℝ) (hs : c.Small bb) :
    Real.exp (-(2 * c.m * Real.log bb / c.k)) ^ c.k * c.prodb ≤ 1 := by sorry
