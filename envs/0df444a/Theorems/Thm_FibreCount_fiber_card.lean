-- Prove2me | Theorems.Thm_FibreCount_fiber_card
-- name    : FibreCount.fiber_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:30.351072+00:00
-- url     : https://prove2.me/theorems/303dbbc5-1f10-476d-a088-366fa0b97bd0
-- title:
--   Fibre Count: fiber card
-- statement:
--   The Fibre Count construction uses the fiber card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/CardFibreCompl.lean#L97-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/CardFibreCompl.lean#L97-L179

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

theorem FibreCount.fiber_card {K V U : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U)
    (hφ : Function.Surjective φ) {k : ℕ} (g : Fin k → U) :
    Nat.card {z : Fin k → V // LinearIndependent K z ∧ ∀ j, φ (z j) = g j} =
      Fintype.card K ^ (Module.finrank K (Submodule.span K (Set.range g)) *
        Module.finrank K (LinearMap.ker φ)) *
      ∏ i ∈ Finset.range (k - Module.finrank K (Submodule.span K (Set.range g))),
        (Fintype.card K ^ Module.finrank K (LinearMap.ker φ) - Fintype.card K ^ i) := by sorry
