-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_smoothOnH_conj
-- name    : CompanionTheory.D.gk.admitted.smoothOnH_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:20.072732+00:00
-- url     : https://prove2.me/theorems/1d089509-8f3d-43b3-ba3c-a6601efd3be8
-- title:
--   admitted: smooth On H conj
-- statement:
--   The admitted construction uses the smooth On H conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/AdmissibleOfFiniteRank.lean#L113-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/AdmissibleOfFiniteRank.lean#L113-L140

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_InPCommutatorOfInK
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_AdmissibleOfFiniteRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open PI.UpqRep
variable {n : ℕ} {ε : Fin n → Bool}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem CompanionTheory.D.gk.admitted.smoothOnH_conj {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A B P : Matrix (Fin n) (Fin n) ℂ}
    (hP : IsUnit P) (hAB : Pᴴ * A * P = B) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (h : SmoothOnH A fun g => f (P⁻¹ * g * P)) : SmoothOnH B f := by sorry
