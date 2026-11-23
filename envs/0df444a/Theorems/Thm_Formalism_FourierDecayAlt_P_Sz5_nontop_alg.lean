-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_nontop_alg
-- name    : Formalism.FourierDecayAlt.P.Sz5.nontop_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:42.772356+00:00
-- url     : https://prove2.me/theorems/1cafc6bf-05b9-4b82-8a6c-4187a1b50ac2
-- title:
--   Sz5: nontop alg
-- statement:
--   The Sz5 construction uses the nontop alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L324-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L324-L328

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

theorem Formalism.FourierDecayAlt.P.Sz5.nontop_alg (n : ℕ) (κ e B α E Vv : ℝ) (hα : α ≠ 0) :
    (κ * e / (1 + 0) * B / α) ^ (n + 1) * ((2 * α) ^ n * (E ^ (n + 1) * Vv)) =
      (2 * κ * E) ^ (n + 1) * (e ^ (n + 1) * B) * (1 / α) * (Vv * B ^ n / 2) := by sorry
