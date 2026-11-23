-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_non_top_final_inequality
-- name    : Formalism.FourierDecayAlt.P.Sz5.non_top_final_inequality
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:34.697906+00:00
-- url     : https://prove2.me/theorems/22014396-c35b-43c1-97b5-0c5ec6ef102b
-- title:
--   Sz5: non top final inequality
-- statement:
--   The Sz5 construction uses the non top final inequality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L346-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L346-L387

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

theorem Formalism.FourierDecayAlt.P.Sz5.non_top_final_inequality (k : ℕ) (hk : 1 ≤ k) (e B α Vv Vu : ℝ) (hα : 1 ≤ α) (he : 0 ≤ e) (hB : 1 ≤ B)
    (hVv : 0 < Vv) (hs : e ^ k * B ≤ 1)
    (hVu : Vu ≤ (2 * α) ^ (k - 1) * (Real.exp (1/4) ^ k * Vv)) :
    (0.38 * e / (1 + 0) * B / α) ^ k * Vu ≤ Vv * B ^ (k - 1) / 2 := by sorry
