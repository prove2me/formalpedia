-- Prove2me | Theorems.Thm_CompanionTheory_D_Inhab_HWRep_D_add
-- name    : CompanionTheory.D.Inhab.HWRep.D_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:15.919302+00:00
-- url     : https://prove2.me/theorems/db0c8cd9-47cf-4f38-ad2f-2e049a969183
-- title:
--   HWRep: D add
-- statement:
--   The HWRep construction uses the D add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/HWRepD.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/HWRepD.lean#L16-L19

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

theorem CompanionTheory.D.Inhab.HWRep.D_add (Y Z : Matrix (Fin k) (Fin k) ℂ) : R.D (Y + Z) = R.D Y + R.D Z := by sorry
