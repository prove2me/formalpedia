-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_Gard_contDiff_hs
-- name    : CompanionTheory.D.gk.admitted.Gard.contDiff_hs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:30:26.874803+00:00
-- url     : https://prove2.me/theorems/f720a4cb-5e26-4d04-8864-fece69bdb05f
-- title:
--   Gard: cont Diff hs
-- statement:
--   The Gard construction uses the cont Diff hs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingBump.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GardingBump.lean#L19-L21

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

theorem CompanionTheory.D.gk.admitted.Gard.contDiff_hs : ContDiff ℝ ∞ (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by sorry
