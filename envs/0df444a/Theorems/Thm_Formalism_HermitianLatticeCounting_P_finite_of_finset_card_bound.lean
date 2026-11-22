-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_finite_of_finset_card_bound
-- name    : Formalism.HermitianLatticeCounting.P.finite_of_finset_card_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:32:36.805389+00:00
-- url     : https://prove2.me/theorems/e58ba535-046b-4bb8-883c-306bb9382c32
-- title:
--   P: finite of finset card bound
-- statement:
--   The P construction uses the finite of finset card bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L70-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/SchurAverage.lean#L70-L82

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

theorem Formalism.HermitianLatticeCounting.P.finite_of_finset_card_bound {α : Type*} (T : Set α) (C : ℝ)
    (h : ∀ S : Finset α, (↑S ⊆ T) → (S.card : ℝ) ≤ C) : T.Finite ∧ (T.ncard : ℝ) ≤ C := by sorry
