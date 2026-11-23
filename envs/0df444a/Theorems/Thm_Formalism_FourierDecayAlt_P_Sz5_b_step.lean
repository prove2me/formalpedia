-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_b_step
-- name    : Formalism.FourierDecayAlt.P.Sz5.b_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:26.47091+00:00
-- url     : https://prove2.me/theorems/fe55ecde-690c-4be8-b8de-0a6fabef8674
-- title:
--   Sz5: b step
-- statement:
--   The Sz5 construction uses the b step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L73-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L73-L85

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

theorem Formalism.FourierDecayAlt.P.Sz5.b_step (c : Cfg) (h : c.Ok) (i : ℕ) (hi : 1 ≤ i) :
    ∀ j, i < j → j ≤ c.m → c.b i + 1 ≤ c.b j := by sorry
