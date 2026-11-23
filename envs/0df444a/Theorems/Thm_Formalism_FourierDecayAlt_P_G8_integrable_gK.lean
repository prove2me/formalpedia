-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G8_integrable_gK
-- name    : Formalism.FourierDecayAlt.P.G8.integrable_gK
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:16.836415+00:00
-- url     : https://prove2.me/theorems/07cfd785-add3-410c-af35-c057d967dab1
-- title:
--   G8: integrable g K
-- statement:
--   The G8 construction uses the integrable g K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L81-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean#L81-L87

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

theorem Formalism.FourierDecayAlt.P.G8.integrable_gK (δ p q : ℝ) (hδ : 0 < δ) : Integrable (gK δ p q) (volume : Measure (ℝ × ℝ)) := by sorry
