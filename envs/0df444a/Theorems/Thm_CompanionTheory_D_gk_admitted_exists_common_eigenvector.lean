-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_exists_common_eigenvector
-- name    : CompanionTheory.D.gk.admitted.exists_common_eigenvector
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:47.464519+00:00
-- url     : https://prove2.me/theorems/2278f4fe-b7c3-48f4-a574-8068e94f7067
-- title:
--   admitted: exists common eigenvector
-- statement:
--   The admitted construction uses the exists common eigenvector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GoodPI.lean#L13-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GoodPI.lean#L13-L55

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GoodPI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem CompanionTheory.D.gk.admitted.exists_common_eigenvector (h : ι → ℕ) (hinj : Function.Injective h) (W : Submodule ℂ (ι → ℂ))
    (hW : W ≠ ⊥) : ∃ w₀ ∈ W, w₀ ≠ 0 ∧ ∀ A : Matrix ι ι ℂ, A.BlockTriangular h → (∀ w ∈ W, A *ᵥ w ∈ W) →
      ∃ c : ℂ, A *ᵥ w₀ = c • w₀ := by sorry
