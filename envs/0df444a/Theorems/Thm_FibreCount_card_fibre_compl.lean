-- Prove2me | Theorems.Thm_FibreCount_card_fibre_compl
-- name    : FibreCount.card_fibre_compl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:32.684325+00:00
-- url     : https://prove2.me/theorems/3315812b-5396-45f3-988f-007961121983
-- title:
--   Fibre Count: card fibre compl
-- statement:
--   The Fibre Count construction uses the card fibre compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/CardFibreCompl.lean#L21-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SplitDensity/CardFibreCompl.lean#L21-L95

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
open Classical

theorem FibreCount.card_fibre_compl {K V U : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup U] [Module K U] (φ : V →ₗ[K] U)
    (hφ : Function.Surjective φ) {k : ℕ} (z : Fin k → V) (hz : LinearIndependent K z)
    (a : U) :
    Nat.card {x : V // x ∉ span K (Set.range z) ∧ φ x = a} =
      if a ∈ span K (Set.range (fun j => φ (z j))) then
        Fintype.card K ^ finrank K (LinearMap.ker φ) -
          Fintype.card K ^ (k - finrank K (span K (Set.range (fun j => φ (z j)))))
      else Fintype.card K ^ finrank K (LinearMap.ker φ) := by sorry
