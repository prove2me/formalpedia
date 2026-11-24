-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLevelGenA_mem_of_disjoint
-- name    : Formalism.MainNotions.BridgeLevelGenA.mem_of_disjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:56.610972+00:00
-- url     : https://prove2.me/theorems/fe287939-003f-4217-be94-f97c8c158110
-- title:
--   Bridge Level Gen A: mem of disjoint
-- statement:
--   The Bridge Level Gen A construction uses the mem of disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGenA.lean#L18-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLevelGenA.lean#L18-L36

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGenA
open scoped nonZeroDivisors
variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem Formalism.MainNotions.BridgeLevelGenA.mem_of_disjoint (g : R) {P : Ideal R} (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hd : Disjoint (coprS g : Set R) (P : Set R)) : g ∈ P := by sorry
