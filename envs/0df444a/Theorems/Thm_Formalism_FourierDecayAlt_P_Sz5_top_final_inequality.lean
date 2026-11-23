-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_top_final_inequality
-- name    : Formalism.FourierDecayAlt.P.Sz5.top_final_inequality
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:44.808118+00:00
-- url     : https://prove2.me/theorems/b1a92c9c-9632-400a-b9c3-dfc94185dc2c
-- title:
--   Sz5: top final inequality
-- statement:
--   The Sz5 construction uses the top final inequality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L389-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L389-L452

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

theorem Formalism.FourierDecayAlt.P.Sz5.top_final_inequality (k : ℕ) (hk : 4 ≤ k) (e B a b Del θ W Vu : ℝ) (he : 0 ≤ e) (hB : 1 ≤ B)
    (hW : 0 < W) (hs : e ^ k * B ≤ 1) (hθ : 1 ≤ θ) (ha : 0 < a) (hb : 0 < b) (hDel : 0 < Del)
    (hq : ((k:ℝ) * Del) ^ 2 * (a + b) ≤ a ^ 2 * b ^ 2)
    (hVu : Vu ≤ (a ^ (k - 2) * (a + b)) * ((Real.exp (1/4) ^ (k - 1) * W) * (b * θ) ^ (k - 2))) :
    (0.38 * e / θ * B / (a * b / ((k:ℝ) * Del))) ^ k * Vu ≤
      (W * (4 * Del) ^ (k - 2) * ((k - 2).factorial : ℝ)) * B ^ (k - 1) / 2 := by sorry
