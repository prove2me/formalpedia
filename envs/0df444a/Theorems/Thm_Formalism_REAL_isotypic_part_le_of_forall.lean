-- Prove2me | Theorems.Thm_Formalism_REAL_isotypic_part_le_of_forall
-- name    : Formalism.REAL.isotypic_part_le_of_forall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:57.94746+00:00
-- url     : https://prove2.me/theorems/dcde8976-ff4e-4d66-a92f-3fb9ac4bd35a
-- title:
--   REAL: isotypic part le of forall
-- statement:
--   The REAL construction uses the isotypic part le of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L197-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L197-L200

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.isotypic_part_le_of_forall {W : Type} [AddCommGroup W] [Module ℂ W] {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} {T : Set (Fin n → ℝ)} {S M : Submodule ℂ W}
    (h : ∀ y ∈ S, ∀ μ ∈ T, KHighest ε F μ y → kSpan ε F y ≤ M) : isoPart ε F T S ≤ M := by sorry
