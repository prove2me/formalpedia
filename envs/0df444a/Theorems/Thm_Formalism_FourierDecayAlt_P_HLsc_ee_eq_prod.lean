-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_ee_eq_prod
-- name    : Formalism.FourierDecayAlt.P.HLsc.ee_eq_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:25.852515+00:00
-- url     : https://prove2.me/theorems/f263f33c-102d-42b5-8f81-22a5a0c66b8e
-- title:
--   HLsc: ee eq prod
-- statement:
--   The HLsc construction uses the ee eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L149-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L149-L152

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

theorem Formalism.FourierDecayAlt.P.HLsc.ee_eq_prod (z : Fin d → ℝ) (τ : Fin d → ℤ) :
    ee z τ = ∏ j, Complex.exp (2 * π * Complex.I * (((τ j : ℝ) : ℂ) * (z j : ℂ))) := by sorry
