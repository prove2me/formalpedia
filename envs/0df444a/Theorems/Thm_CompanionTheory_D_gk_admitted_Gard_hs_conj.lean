-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_hs_conj
-- name    : CompanionTheory.D.gk.admitted.Gard.hs_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:52.51655+00:00
-- url     : https://prove2.me/theorems/a9c2fbd2-a3da-4690-bcf0-015b0a01ceb6
-- title:
--   Gard: hs conj
-- statement:
--   The Gard construction uses the hs conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingBump.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingBump.lean#L37-L45

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

theorem CompanionTheory.D.gk.admitted.Gard.hs_conj {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (y : Matrix (Fin n) (Fin n) ℂ) : hs (kᴴ * y * k) = hs y := by sorry
