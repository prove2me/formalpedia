-- Prove2me | Theorems.Thm_CompanionTheory_D_Inhab_HWRep_curve_tri
-- name    : CompanionTheory.D.Inhab.HWRep.curve_tri
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:31.423736+00:00
-- url     : https://prove2.me/theorems/b20eca0b-52e8-44fa-961c-7370dcc5f4e7
-- title:
--   HWRep: curve tri
-- statement:
--   The HWRep construction uses the curve tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/HWRepD.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/NonemptyRepresentations/HWRepD.lean#L50-L55

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

theorem CompanionTheory.D.Inhab.HWRep.curve_tri {a b : Fin k} (hab : a ≤ b) (t : ℂ) :
    (1 + t • Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ).BlockTriangular id := by sorry
