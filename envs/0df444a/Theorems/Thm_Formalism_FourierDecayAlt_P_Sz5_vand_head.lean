-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_vand_head
-- name    : Formalism.FourierDecayAlt.P.Sz5.vand_head
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:27.495892+00:00
-- url     : https://prove2.me/theorems/39556214-eddd-4478-9bed-89e44a5b829c
-- title:
--   Sz5: vand head
-- statement:
--   The Sz5 construction uses the vand head property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L458-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L458-L461

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

theorem Formalism.FourierDecayAlt.P.Sz5.vand_head (q : ℕ) (x : ℕ → ℝ) :
    Vand (q + 1) x = (∏ j ∈ Icc 1 q, (x 1 - x (j + 1))) * Vand q (fun j => x (j + 1)) := by sorry
