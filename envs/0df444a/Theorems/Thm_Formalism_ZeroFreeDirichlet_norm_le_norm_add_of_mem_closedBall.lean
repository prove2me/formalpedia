-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_norm_le_norm_add_of_mem_closedBall
-- name    : Formalism.ZeroFreeDirichlet.norm_le_norm_add_of_mem_closedBall
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:42:48.453656+00:00
-- url     : https://prove2.me/theorems/e95472a6-b6ea-4de9-a5a3-32ff476c7635
-- title:
--   Zero Free Dirichlet: norm le norm add of mem closed Ball
-- statement:
--   The Zero Free Dirichlet construction uses the norm le norm add of mem closed Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LocalZerosOf.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LocalZerosOf.lean#L16-L20

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LocalZerosOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.norm_le_norm_add_of_mem_closedBall {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : ‖w‖ ≤ ‖z₀‖ + r := by sorry
