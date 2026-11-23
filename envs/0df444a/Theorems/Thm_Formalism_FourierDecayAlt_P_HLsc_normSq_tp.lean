-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_normSq_tp
-- name    : Formalism.FourierDecayAlt.P.HLsc.normSq_tp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:03.107799+00:00
-- url     : https://prove2.me/theorems/70ca4c21-27fb-46cf-96d3-f4a1f1e9743e
-- title:
--   HLsc: norm Sq tp
-- statement:
--   The HLsc construction uses the norm Sq tp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L20-L29

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

theorem Formalism.FourierDecayAlt.P.HLsc.normSq_tp (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (y : Fin d → ℝ) :
    ((‖tp B c y‖ ^ 2 : ℝ) : ℂ) =
      ∑ σ ∈ B, ∑ σ' ∈ B, ee y (σ - σ') * c σ * starRingEnd ℂ (c σ') := by sorry
