-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_integral_one_dim
-- name    : Formalism.FourierDecayAlt.P.HLsc.integral_one_dim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:55.786052+00:00
-- url     : https://prove2.me/theorems/ade0e5ce-129d-40dd-a660-00b072c01af6
-- title:
--   HLsc: integral one dim
-- statement:
--   The HLsc construction uses the integral one dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L129-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L129-L147

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

theorem Formalism.FourierDecayAlt.P.HLsc.integral_one_dim (m : ℤ) :
    ∫ t in Set.Icc (-(1 / 2) : ℝ) (1 / 2), Complex.exp (2 * π * Complex.I * (((m : ℝ) : ℂ) * (t : ℂ))) =
      if m = 0 then 1 else 0 := by sorry
