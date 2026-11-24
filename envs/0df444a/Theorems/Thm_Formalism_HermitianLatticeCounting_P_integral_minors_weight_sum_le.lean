-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_integral_minors_weight_sum_le
-- name    : Formalism.HermitianLatticeCounting.P.integral_minors_weight_sum_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:50.671149+00:00
-- url     : https://prove2.me/theorems/8368d17d-bbd5-4806-a57b-0bd851a77d74
-- title:
--   P: integral minors weight sum le
-- statement:
--   The P construction uses the integral minors weight sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L611-L670
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/BlockMinorSumCounterexample.lean#L611-L670

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

theorem Formalism.HermitianLatticeCounting.P.integral_minors_weight_sum_le (hf : BlockEndMinorFibreFinite) (hs : IdealInversePowerSum) (E : Type) [Field E] [NumberField E]
    [NumberField.IsTotallyComplex E] (p : ℕ) (s : Fin p → ℕ) (hs1 : ∀ a, 1 ≤ s a)
    (T : Finset (Fin p → E))
    (hT : ∀ t ∈ T, ∀ a, IsIntegral ℤ (IndexedMinorEntry s t a) ∧ IndexedMinorEntry s t a ≠ 0) :
    ∑ t ∈ T, (∏ a : Fin p, ∏ w : InfinitePlace E, (1 + (w (IndexedMinorEntry s t a)) ^ 2) ^ 2)⁻¹ ≤
      ((∏ a, s a : ℕ) : ℝ) * 16 ^ (Fintype.card (InfinitePlace E) * p) := by sorry
