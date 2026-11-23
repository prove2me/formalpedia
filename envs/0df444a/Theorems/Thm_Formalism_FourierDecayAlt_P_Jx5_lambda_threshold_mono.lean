-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx5_lambda_threshold_mono
-- name    : Formalism.FourierDecayAlt.P.Jx5.lambda_threshold_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:35.181401+00:00
-- url     : https://prove2.me/theorems/b0b14544-313d-4b3b-9c9d-e0850c2a7d9b
-- title:
--   Jx5: lambda threshold mono
-- statement:
--   The Jx5 construction uses the lambda threshold mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SupremumAIsMajorant.lean#L22-L29

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SupremumAIsMajorant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped Pointwise
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx5

theorem Formalism.FourierDecayAlt.P.Jx5.lambda_threshold_mono (m i s : ℕ) {C C' κ N I A : ℝ} (hC : 0 ≤ C) (h : C ≤ C') (hκ : 0 ≤ κ) (hN : 0 ≤ N)
    (hI : 0 ≤ I) (hA : 0 ≤ A) :
    0 ≤ Sz.lamThreshold m i s C κ N I A ∧ Sz.lamThreshold m i s C κ N I A ≤ Sz.lamThreshold m i s C' κ N I A := by sorry
