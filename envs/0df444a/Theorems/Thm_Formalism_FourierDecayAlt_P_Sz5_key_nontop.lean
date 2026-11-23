-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_key_nontop
-- name    : Formalism.FourierDecayAlt.P.Sz5.key_nontop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:40.198804+00:00
-- url     : https://prove2.me/theorems/ea1669f5-3515-4fdd-8c1e-d9681a58e956
-- title:
--   Sz5: key nontop
-- statement:
--   The Sz5 construction uses the key nontop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L530-L584
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L530-L584

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

theorem Formalism.FourierDecayAlt.P.Sz5.key_nontop (hNT : VandNonTop) (hEF : EdgeFactors) (c : Cfg) (bb : ℝ) (de : ℕ → ℝ) (h : c.Ok)
    (hs : c.Small bb) (hw : IsWord c.k de) (htop : c.top = false) :
    0 ≤ cOne c bb * c.prodb / c.aeff ∧
    (cOne c bb * c.prodb / c.aeff) ^ c.k * Vand c.k (c.u de) ≤
      Vand (c.k - 1) c.v * c.prodb ^ (c.k - 1) / 2 := by sorry
