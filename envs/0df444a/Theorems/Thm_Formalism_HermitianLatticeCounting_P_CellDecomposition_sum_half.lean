-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_CellDecomposition_sum_half
-- name    : Formalism.HermitianLatticeCounting.P.CellDecomposition.sum_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:40.305045+00:00
-- url     : https://prove2.me/theorems/ede93b58-e5d6-4193-9a3e-bc3b894c8706
-- title:
--   Cell Decomposition: sum half
-- statement:
--   The Cell Decomposition construction uses the sum half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LiftingDecomposition.lean#L203-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/LiftingDecomposition.lean#L203-L206

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open CellDecomposition

theorem Formalism.HermitianLatticeCounting.P.CellDecomposition.sum_half (n : ℕ) : ∑ s ∈ Finset.Icc 1 n, (1 / 2 : ℝ) ^ s = 1 - (1 / 2) ^ n := by sorry
