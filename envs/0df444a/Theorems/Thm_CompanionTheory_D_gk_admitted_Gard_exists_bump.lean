-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_exists_bump
-- name    : CompanionTheory.D.gk.admitted.Gard.exists_bump
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:58.076791+00:00
-- url     : https://prove2.me/theorems/872bed8b-916e-437f-9698-b93c4e15e624
-- title:
--   Gard: exists bump
-- statement:
--   The Gard construction uses the exists bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingBump.lean#L56-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingBump.lean#L56-L75

import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GardingBump
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Topology Set Filter
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.Gard
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}

theorem CompanionTheory.D.gk.admitted.Gard.exists_bump {W : Set (Matrix (Fin n) (Fin n) ℂ)} (hW : W ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (f : Matrix (Fin n) (Fin n) ℂ → ℝ) (S : Set (Matrix (Fin n) (Fin n) ℂ)), ContDiff ℝ ∞ f ∧ 0 ≤ f ∧ f 1 ≠ 0 ∧
      IsCompact S ∧ S ⊆ W ∧ (∀ y, f y ≠ 0 → y ∈ S) ∧
      ∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ y, f (kᴴ * y * k) = f y := by sorry
