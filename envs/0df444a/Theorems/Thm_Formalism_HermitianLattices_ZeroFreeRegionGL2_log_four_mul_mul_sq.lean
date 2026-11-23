-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_log_four_mul_mul_sq
-- name    : Formalism.HermitianLattices.ZeroFreeRegionGL2.log_four_mul_mul_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:48.83593+00:00
-- url     : https://prove2.me/theorems/113108a5-e88c-44c3-9792-25b6af8b580a
-- title:
--   Zero Free Region GL2: log four mul mul sq
-- statement:
--   The Zero Free Region GL2 construction uses the log four mul mul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SecondEstimateOfHypothesis.lean#L168-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/SecondEstimateOfHypothesis.lean#L168-L171

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

theorem Formalism.HermitianLattices.ZeroFreeRegionGL2.log_four_mul_mul_sq (d N : ℝ) (hd : 0 < d) (hN : 0 < N) :
    Real.log (4 * d * N ^ 2) = Real.log 4 + Real.log d + 2 * Real.log N := by sorry
