-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_fac_bound
-- name    : Formalism.FourierDecayAlt.P.Sz5.fac_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:28.923797+00:00
-- url     : https://prove2.me/theorems/f919f95c-5484-4c4c-8943-ca52cab2023d
-- title:
--   Sz5: fac bound
-- statement:
--   The Sz5 construction uses the fac bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L261-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L261-L322

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

theorem Formalism.FourierDecayAlt.P.Sz5.fac_bound (n : ℕ) (hn : 2 ≤ n) :
    2 * (0.38:ℝ) ^ (n + 2) * ((n:ℝ) + 2) ^ n * Real.exp (1/4) ^ (n + 1) ≤ 4 ^ n * (n.factorial : ℝ) := by sorry
