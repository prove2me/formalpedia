-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_rpow_eq_rpow_half_mul
-- name    : Formalism.HermitianLattices.ZeroFreeRegionGL2.rpow_eq_rpow_half_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:42.588665+00:00
-- url     : https://prove2.me/theorems/8db8d08b-a8c0-4af4-beb4-3a0ff3e92b98
-- title:
--   Zero Free Region GL2: rpow eq rpow half mul
-- statement:
--   The Zero Free Region GL2 construction uses the rpow eq rpow half mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SecondEstimateOfHypothesis.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SecondEstimateOfHypothesis.lean#L11-L12

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

theorem Formalism.HermitianLattices.ZeroFreeRegionGL2.rpow_eq_rpow_half_mul (x a : ℝ) (hx : 0 < x) : x ^ a = x ^ (a / 2) * x ^ (a / 2) := by sorry
