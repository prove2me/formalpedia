-- Prove2me | Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_bsym
-- name    : CompanionTheory.PlacePermOperatorBicommutantSpan.bsym
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:22.747178+00:00
-- url     : https://prove2.me/theorems/4bb8c9e9-e0f6-4ad8-b722-63b58423c3ce
-- title:
--   Place Perm Operator Bicommutant Span: bsym
-- statement:
--   The Place Perm Operator Bicommutant Span construction uses the bsym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/SqPosOfNe.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ThetaDilations/SqPosOfNe.lean#L14-L15

import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_IsOpenCoset
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_SqPosOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Set Matrix
open scoped ENNReal ComplexConjugate MatrixGroups
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
open GlobalTheory.CompanionTheory.SW.Core
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]

theorem CompanionTheory.PlacePermOperatorBicommutantSpan.bsym {B : Matrix ι ι R} (hB : B.IsSymm) (x y : ι → R) : x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by sorry
