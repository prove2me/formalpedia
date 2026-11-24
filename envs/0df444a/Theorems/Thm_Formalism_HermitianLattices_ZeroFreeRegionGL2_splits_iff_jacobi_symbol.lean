-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_splits_iff_jacobi_symbol
-- name    : Formalism.HermitianLattices.ZeroFreeRegionGL2.splits_iff_jacobi_symbol
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:28.457715+00:00
-- url     : https://prove2.me/theorems/cd3d1c2e-1622-4682-9429-3b57c167d24b
-- title:
--   Zero Free Region GL2: splits iff jacobi symbol
-- statement:
--   The Zero Free Region GL2 construction uses the splits iff jacobi symbol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/WeightedVonMangoldtSumIdentity.lean#L381-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/WeightedVonMangoldtSumIdentity.lean#L381-L448

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

theorem Formalism.HermitianLattices.ZeroFreeRegionGL2.splits_iff_jacobi_symbol : SplitsIffJacobi := by sorry
