-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_top_alg
-- name    : Formalism.FourierDecayAlt.P.Sz5.top_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:42.234611+00:00
-- url     : https://prove2.me/theorems/a446fe34-6ea1-4ff9-880a-0654d6ee1ad3
-- title:
--   Sz5: top alg
-- statement:
--   The Sz5 construction uses the top alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L330-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L330-L344

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

theorem Formalism.FourierDecayAlt.P.Sz5.top_alg (n : ℕ) (κ e B a b K θ E W : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hθ : θ ≠ 0) :
    (κ * e / θ * B / (a * b / K)) ^ (n + 2) * ((a ^ n * (a + b)) * ((E ^ (n + 1) * W) * (b * θ) ^ n)) =
      (e ^ (n + 2) * B) * (K ^ 2 * (a + b) / (a ^ 2 * b ^ 2)) * (1 / θ ^ 2) *
        (κ ^ (n + 2) * K ^ n * E ^ (n + 1)) * (W * B ^ (n + 1)) := by sorry
