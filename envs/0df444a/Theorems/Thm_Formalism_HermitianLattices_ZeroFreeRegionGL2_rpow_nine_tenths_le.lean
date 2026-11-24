-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_rpow_nine_tenths_le
-- name    : Formalism.HermitianLattices.ZeroFreeRegionGL2.rpow_nine_tenths_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:04.466421+00:00
-- url     : https://prove2.me/theorems/ceb9bac1-0a6e-4f67-8615-75b8e71b8125
-- title:
--   Zero Free Region GL2: rpow nine tenths le
-- statement:
--   The Zero Free Region GL2 construction uses the rpow nine tenths le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SecondEstimateOfHypothesis.lean#L99-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SecondEstimateOfHypothesis.lean#L99-L124

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SecondEstimateOfHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem Formalism.HermitianLattices.ZeroFreeRegionGL2.rpow_nine_tenths_le (c₃ B Y : ℝ) (hc₃ : 0 < c₃) (hB : 0 < B) (hY : 0 < Y) (hl : 0 < Real.log Y)
    (h1 : 120 * Real.log B ≤ Real.log Y) (h2 : 40 * Real.log (40 / c₃) ≤ Real.log Y) :
    Y ^ (9 / 10 : ℝ) ≤ c₃ * 1 * B ^ (-6 : ℝ) * Y / Real.log Y := by sorry
