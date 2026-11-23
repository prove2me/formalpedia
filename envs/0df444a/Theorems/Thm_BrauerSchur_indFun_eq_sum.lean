-- Prove2me | Theorems.Thm_BrauerSchur_indFun_eq_sum
-- name    : BrauerSchur.indFun_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:17.544998+00:00
-- url     : https://prove2.me/theorems/b4e1187e-2455-4d39-b5bf-858ae85b3dd2
-- title:
--   Brauer Schur: ind Fun eq sum
-- statement:
--   The Brauer Schur construction uses the ind Fun eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RealInducedCharacters/Induced.lean#L101-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RealInducedCharacters/Induced.lean#L101-L136

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealInducedCharacters_InducedCharRealised
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RealInducedCharacters_Induced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open BrauerSchur
open scoped BigOperators
variable {G : Type*} [Group G] {K : Type*} [Field K] (H : Subgroup G) (ψ : H →* Kˣ)
variable {m : ℕ} (t : Fin m → G)

theorem BrauerSchur.indFun_eq_sum [Fintype G] [CharZero K] (ht : ∀ i j, (t i)⁻¹ * t j ∈ H ↔ i = j)
    (hc : ∀ x : G, ∃ i, (t i)⁻¹ * x ∈ H) (g : G) :
    indFun H (fun h => ((ψ h : Kˣ) : K)) g = ∑ i, dot H ψ ((t i)⁻¹ * g * t i) := by sorry
