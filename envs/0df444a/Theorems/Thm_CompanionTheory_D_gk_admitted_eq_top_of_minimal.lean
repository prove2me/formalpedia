-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_eq_top_of_minimal
-- name    : CompanionTheory.D.gk.admitted.eq_top_of_minimal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:35.008055+00:00
-- url     : https://prove2.me/theorems/d734f096-c34d-4ba7-a5c3-bcd0703f8788
-- title:
--   admitted: eq top of minimal
-- statement:
--   The admitted construction uses the eq top of minimal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GoodPI.lean#L95-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GoodPI.lean#L95-L126

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

theorem CompanionTheory.D.gk.admitted.eq_top_of_minimal {G : Type} (A : G → Matrix ι ι ℂ) (hadj : ∀ g, ∃ g', A g' = (A g)ᴴ)
    (N : Submodule ℂ (ι → ℂ))
    (hN : ∀ W : Submodule ℂ (ι → ℂ), W ≠ ⊥ → (∀ g, ∀ w ∈ W, A g *ᵥ w ∈ W) →
      (∀ U : Submodule ℂ (ι → ℂ), U ≠ ⊥ → (∀ g, ∀ w ∈ U, A g *ᵥ w ∈ U) → U ≤ W → U = W) → W ≤ N) :
    N = ⊤ := by sorry
