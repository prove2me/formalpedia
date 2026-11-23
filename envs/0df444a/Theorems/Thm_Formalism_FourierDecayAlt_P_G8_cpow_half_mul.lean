-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G8_cpow_half_mul
-- name    : Formalism.FourierDecayAlt.P.G8.cpow_half_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:00:33.003364+00:00
-- url     : https://prove2.me/theorems/bb72b687-1fbd-4c37-9614-47d062216731
-- title:
--   G8: cpow half mul
-- statement:
--   The G8 construction uses the cpow half mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L46-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L46-L68

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G8

theorem Formalism.FourierDecayAlt.P.G8.cpow_half_mul (u : ℂ) (hu : 0 < u.re) (R : ℝ) (hR : 0 < R) :
    ((Real.pi : ℂ) / u) ^ (1 / 2 : ℂ) * ((Real.pi : ℂ) / ((R : ℂ) / u)) ^ (1 / 2 : ℂ) =
      ((Real.pi / Real.sqrt R : ℝ) : ℂ) := by sorry
