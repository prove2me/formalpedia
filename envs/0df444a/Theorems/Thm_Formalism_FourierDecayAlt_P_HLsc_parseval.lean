-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_parseval
-- name    : Formalism.FourierDecayAlt.P.HLsc.parseval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:56.673615+00:00
-- url     : https://prove2.me/theorems/7350e1fb-0682-4c57-9818-02ab367d2933
-- title:
--   HLsc: parseval
-- statement:
--   The HLsc construction uses the parseval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L186-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L186-L206

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

theorem Formalism.FourierDecayAlt.P.HLsc.parseval (B : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    ∫ z in cube d, ‖tp B c z‖ ^ 2 = ∑ σ ∈ B, ‖c σ‖ ^ 2 := by sorry
