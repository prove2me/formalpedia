-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_card_separated_set_le_prod
-- name    : Formalism.HermitianLatticeCounting.P.card_separated_set_le_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:28:58.380072+00:00
-- url     : https://prove2.me/theorems/290fd06e-7f5e-4bcd-9d42-d84c58fe5813
-- title:
--   P: card separated set le prod
-- statement:
--   The P construction uses the card separated set le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L9-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L9-L68

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open MeasureTheory Metric

theorem Formalism.HermitianLatticeCounting.P.card_separated_set_le_prod {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (S : Finset (ι → F)) (r B : ι → ℝ) (hr : ∀ v, 0 < r v)
    (hB : ∀ v, 0 ≤ B v) (hS : ∀ c ∈ S, ∀ v, ‖c v‖ ≤ B v)
    (hsep : ∀ c ∈ S, ∀ d ∈ S, c ≠ d → ∃ v, 2 * r v ≤ ‖c v - d v‖) :
    (S.card : ℝ) ≤ ∏ v, ((B v + r v) / r v) ^ finrank ℝ F := by sorry
