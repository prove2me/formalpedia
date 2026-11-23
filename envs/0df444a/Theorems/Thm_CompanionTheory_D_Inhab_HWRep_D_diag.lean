-- Prove2me | Theorems.Thm_CompanionTheory_D_Inhab_HWRep_D_diag
-- name    : CompanionTheory.D.Inhab.HWRep.D_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:27:17.424363+00:00
-- url     : https://prove2.me/theorems/73772d2a-1a97-4ea6-9fd5-cafe910c2afd
-- title:
--   HWRep: D diag
-- statement:
--   The HWRep construction uses the D diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/HWRepD.lean#L73-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/HWRepD.lean#L73-L103

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

theorem CompanionTheory.D.Inhab.HWRep.D_diag (a : Fin k) : R.D (Matrix.single a a 1) *ᵥ R.v0 = (ν a : ℂ) • R.v0 := by sorry
