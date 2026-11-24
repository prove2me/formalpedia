-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_integral_points_weight_sum_le
-- name    : Formalism.HermitianLatticeCounting.P.integral_points_weight_sum_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:37:12.88481+00:00
-- url     : https://prove2.me/theorems/bfad4adb-ac5e-4396-87ce-befcc0846c96
-- title:
--   P: integral points weight sum le
-- statement:
--   The P construction uses the integral points weight sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L602-L609
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L602-L609

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms

theorem Formalism.HermitianLatticeCounting.P.integral_points_weight_sum_le (hs : IdealInversePowerSum) (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (T : Finset E) (hT : ∀ x ∈ T, IsIntegral ℤ x) :
    ∑ D ∈ T, ∏ w : InfinitePlace E, ((1 + (w D) ^ 2) ^ 2)⁻¹ ≤ 16 ^ Fintype.card (InfinitePlace E) := by sorry
