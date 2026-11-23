-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_perp_ne_bot
-- name    : CompanionTheory.D.gk.admitted.perp_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:02.92541+00:00
-- url     : https://prove2.me/theorems/ffd04ac1-7ace-4c87-b928-cdf55a5dd2d0
-- title:
--   admitted: perp ne bot
-- statement:
--   The admitted construction uses the perp ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GoodPI.lean#L69-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/GoodPI.lean#L69-L88

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

theorem CompanionTheory.D.gk.admitted.perp_ne_bot (T : Submodule ℂ (ι → ℂ)) (hT : T ≠ ⊤) : perp T ≠ ⊥ := by sorry
