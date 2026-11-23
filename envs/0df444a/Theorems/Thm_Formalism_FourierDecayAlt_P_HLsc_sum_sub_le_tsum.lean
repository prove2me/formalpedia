-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_sum_sub_le_tsum
-- name    : Formalism.FourierDecayAlt.P.HLsc.sum_sub_le_tsum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:14.261199+00:00
-- url     : https://prove2.me/theorems/7431610d-d5a6-48c2-bedf-8e7002fef447
-- title:
--   HLsc: sum sub le tsum
-- statement:
--   The HLsc construction uses the sum sub le tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L60-L64

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}

theorem Formalism.FourierDecayAlt.P.HLsc.sum_sub_le_tsum {κ : (Fin d → ℤ) → ℝ} (hκ0 : ∀ σ, 0 ≤ κ σ) (hκ : Summable κ)
    (B : Finset (Fin d → ℤ)) (σ : Fin d → ℤ) :
    ∑ σ' ∈ B, κ (σ - σ') ≤ ∑' τ, κ τ := by sorry
