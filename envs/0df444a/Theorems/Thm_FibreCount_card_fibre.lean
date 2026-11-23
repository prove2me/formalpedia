-- Prove2me | Theorems.Thm_FibreCount_card_fibre
-- name    : FibreCount.card_fibre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:34.679242+00:00
-- url     : https://prove2.me/theorems/3b98d2b3-5aec-4cb5-b423-978d23c7e82b
-- title:
--   Fibre Count: card fibre
-- statement:
--   The Fibre Count construction uses the card fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/CardFibreCompl.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/CardFibreCompl.lean#L7-L17

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SplitDensity_CardFibreCompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
open FibreCount

theorem FibreCount.card_fibre {K V U : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U) (a : U) (x0 : V)
    (hx0 : φ x0 = a) :
    Nat.card {x : V // φ x = a} = Fintype.card K ^ finrank K (LinearMap.ker φ) := by sorry
