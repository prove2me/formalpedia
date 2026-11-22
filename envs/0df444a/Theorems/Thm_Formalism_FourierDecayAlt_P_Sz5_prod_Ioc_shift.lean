-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_prod_Ioc_shift
-- name    : Formalism.FourierDecayAlt.P.Sz5.prod_Ioc_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:48.158799+00:00
-- url     : https://prove2.me/theorems/74b82b18-eae8-4b8e-8a5d-f35e0aba8939
-- title:
--   Sz5: prod Ioc shift
-- statement:
--   The Sz5 construction uses the prod Ioc shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L9-L15

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

theorem Formalism.FourierDecayAlt.P.Sz5.prod_Ioc_shift (f : ℕ → ℝ) (p a b : ℕ) :
    ∏ j ∈ Ioc (a + p) (b + p), f j = ∏ j ∈ Ioc a b, f (j + p) := by sorry
