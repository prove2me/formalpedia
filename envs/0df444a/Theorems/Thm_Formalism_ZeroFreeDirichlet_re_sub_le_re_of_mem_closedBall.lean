-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_re_sub_le_re_of_mem_closedBall
-- name    : Formalism.ZeroFreeDirichlet.re_sub_le_re_of_mem_closedBall
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:44:08.668595+00:00
-- url     : https://prove2.me/theorems/4f283c68-8a46-45e4-b7c6-cc3be282849c
-- title:
--   Zero Free Dirichlet: re sub le re of mem closed Ball
-- statement:
--   The Zero Free Dirichlet construction uses the re sub le re of mem closed Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LocalZerosOf.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/LocalZerosOf.lean#L9-L14

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

theorem Formalism.ZeroFreeDirichlet.re_sub_le_re_of_mem_closedBall {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : z₀.re - r ≤ w.re := by sorry
