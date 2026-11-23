-- Prove2me | Theorems.Thm_CompanionTheory_D_Inhab_HWRep_D_upper
-- name    : CompanionTheory.D.Inhab.HWRep.D_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:13.451664+00:00
-- url     : https://prove2.me/theorems/f0d78715-f2b8-4792-9994-93273d7ff383
-- title:
--   HWRep: D upper
-- statement:
--   The HWRep construction uses the D upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/HWRepD.lean#L57-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/HWRepD.lean#L57-L71

import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_NonemptyOfAntitone
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_HWRepD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Inhab CompanionTheory.D.Inhab.HWRep
variable {k : ℕ} {ν : Fin k → ℤ} (R : HWRep k ν)

theorem CompanionTheory.D.Inhab.HWRep.D_upper {a b : Fin k} (hab : a < b) : R.D (Matrix.single a b 1) *ᵥ R.v0 = 0 := by sorry
