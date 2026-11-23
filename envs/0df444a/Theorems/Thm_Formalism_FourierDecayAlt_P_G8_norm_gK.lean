-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G8_norm_gK
-- name    : Formalism.FourierDecayAlt.P.G8.norm_gK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:12.867287+00:00
-- url     : https://prove2.me/theorems/251d3581-9ac7-41f3-877e-e082233ab789
-- title:
--   G8: norm g K
-- statement:
--   The G8 construction uses the norm g K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L74-L79

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

theorem Formalism.FourierDecayAlt.P.G8.norm_gK (δ p q : ℝ) (z : ℝ × ℝ) :
    ‖gK δ p q z‖ = Real.exp (-δ * z.1 ^ 2) * Real.exp (-δ * z.2 ^ 2) := by sorry
