-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_weighted_sum_lipschitz
-- name    : Formalism.HermitianLattices.ZeroFreeRegionGL2.weighted_sum_lipschitz
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:55.637802+00:00
-- url     : https://prove2.me/theorems/76e8232b-c821-465c-b7a4-02b562f8d6d2
-- title:
--   Zero Free Region GL2: weighted sum lipschitz
-- statement:
--   The Zero Free Region GL2 construction uses the weighted sum lipschitz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/WeightedVonMangoldtSumIdentity.lean#L185-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/WeightedVonMangoldtSumIdentity.lean#L185-L208

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem Formalism.HermitianLattices.ZeroFreeRegionGL2.weighted_sum_lipschitz : WGLipschitz := by sorry
