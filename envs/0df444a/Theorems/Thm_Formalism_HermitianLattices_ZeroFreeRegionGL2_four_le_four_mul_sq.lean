-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_four_le_four_mul_sq
-- name    : Formalism.HermitianLattices.ZeroFreeRegionGL2.four_le_four_mul_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:56.745909+00:00
-- url     : https://prove2.me/theorems/6a38db1f-0023-46d2-b519-bb367c32657d
-- title:
--   Zero Free Region GL2: four le four mul sq
-- statement:
--   The Zero Free Region GL2 construction uses the four le four mul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SecondEstimateOfHypothesis.lean#L173-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SecondEstimateOfHypothesis.lean#L173-L176

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

theorem Formalism.HermitianLattices.ZeroFreeRegionGL2.four_le_four_mul_sq (d N : ℝ) (hd : 1 ≤ d) (hN : 1 ≤ N) : 4 ≤ 4 * d * N ^ 2 := by sorry
