-- Prove2me | Theorems.Thm_F6RotationSupport_mem_supportUnion
-- name    : F6RotationSupport.mem_supportUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:31:43.486847+00:00
-- url     : https://prove2.me/theorems/0c629044-13c9-5429-b03c-c52ae98631e5
-- title:
--   F6 Rotation Support: mem support Union
-- statement:
--   The F6 Rotation Support construction uses the mem support Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L36-L38
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/StableMarriageF6/F6RotationSupportCI2.lean#L36-L38

import Definitions.Def_StableMarriageF6_F6ConvexWindow
import Definitions.Def_StableMarriageF6_F6RotationSupportCI2
set_option autoImplicit true
noncomputable section
open F6RotationSupport
open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {R M : Type*} [Fintype R] [PartialOrder R] [Fintype M]

theorem F6RotationSupport.mem_supportUnion {supp : R → Finset M} {Q : Finset R} {m : M} :
    m ∈ supportUnion supp Q ↔ ∃ rho ∈ Q, m ∈ supp rho := by sorry
