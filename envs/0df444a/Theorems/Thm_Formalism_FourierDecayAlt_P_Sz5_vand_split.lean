-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_vand_split
-- name    : Formalism.FourierDecayAlt.P.Sz5.vand_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:38.37538+00:00
-- url     : https://prove2.me/theorems/14f3dbb6-1a8c-4da8-a69f-56f3359a391e
-- title:
--   Sz5: vand split
-- statement:
--   The Sz5 construction uses the vand split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L22-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L22-L47

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

theorem Formalism.FourierDecayAlt.P.Sz5.vand_split (p q : ℕ) (x : ℕ → ℝ) :
    Vand (p + q) x = Vand p x * (∏ i ∈ Icc 1 p, ∏ j ∈ Icc 1 q, (x i - x (j + p))) *
      Vand q (fun j => x (j + p)) := by sorry
