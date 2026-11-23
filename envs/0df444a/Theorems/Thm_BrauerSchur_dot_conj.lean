-- Prove2me | Theorems.Thm_BrauerSchur_dot_conj
-- name    : BrauerSchur.dot_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:14.077703+00:00
-- url     : https://prove2.me/theorems/ce5d74d9-4252-4c08-a487-d27b61d840c0
-- title:
--   Brauer Schur: dot conj
-- statement:
--   The Brauer Schur construction uses the dot conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RealInducedCharacters/Induced.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RealInducedCharacters/Induced.lean#L29-L41

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

theorem BrauerSchur.dot_conj {h : G} (hh : h ∈ H) (y : G) : dot H ψ (h⁻¹ * y * h) = dot H ψ y := by sorry
