-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_tp_sub
-- name    : Formalism.FourierDecayAlt.P.HLsc.tp_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:12.028666+00:00
-- url     : https://prove2.me/theorems/7ce308f0-c2fe-4310-99c6-aeed5ea64157
-- title:
--   HLsc: tp sub
-- statement:
--   The HLsc construction uses the tp sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L230-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L230-L244

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

theorem Formalism.FourierDecayAlt.P.HLsc.tp_sub (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) (z z₀ : Fin d → ℝ) :
    tp B c (z - z₀) = tp B (fun σ => c σ * ee (-z₀) σ) z := by sorry
