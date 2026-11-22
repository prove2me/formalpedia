-- Prove2me | Theorems.Thm_APFPaper5_K2_mem_heldFamily_r2
-- name    : APFPaper5.K2.mem_heldFamily_r2
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T15:59:45.348801+00:00
-- url     : https://prove2.me/theorems/bf07f03a-4a88-43b4-9949-a3595638982f
-- title:
--   mem heldFamily
-- statement:
--   Scope and conditions: Recorded classes are indicators of the records kept by the true members of a supplied family. Their self-overlap equals supplied kept cost; nonnegative weights imply the record-ledger triangle inequality and exclude the stated turn table for 0<t<1. The relocated definitions and successor theorem records preserve old native versions and dependents. No statement identifies these recorded classes with a complete physical state or establishes a physical carrier.
--
--   Exact source statement:
--
--   theorem mem_heldFamily (reads : D → X → Bool) (S : Finset D) (x : X) (d : D) :
--       d ∈ heldFamily reads S x ↔ d ∈ S ∧ reads d x = true
--
--   Source parameters:
--
--   universe uX uD uW
--   variable {X : Type uX} {D : Type uD} {W : Type uW}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_recorded_classes:157; USB pullbacks v58 batch B; SHA-256 723174b6a77f546ff3e254cbe18930f113fce520b6db9d0ac87f426580d1edbd']

import Definitions.Def_APFPaper5_K2_RecordedClass
import Theorems.Thm_APFPaper5_K2_ind_mul_self
import Theorems.Thm_APFPaper5_K2_keptClass_cost_r2
import Theorems.Thm_APFPaper5_K2_keptClass_union_of_disjoint_r2
import Definitions.Def_APFPaper5_K1_record_tables_and_turns_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_triangle
import Theorems.Thm_APFPaper5_K1_atomTable_le_diag
import Theorems.Thm_APFPaper5_K1_sourcePartyScore_triangle
import Theorems.Thm_APFPaper5_K1_turnTable_symm
import Theorems.Thm_APFPaper5_K1_turnTable_breaks_triangle
import Theorems.Thm_APFPaper5_K1_no_record_ledger_has_turnTable
import Theorems.Thm_APFPaper5_K1_no_three_distinctions_have_turnTable
import Theorems.Thm_APFPaper5_K1_turnTable_half_form
import Theorems.Thm_APFPaper5_K1_turnTable_half_nonneg
import Theorems.Thm_APFPaper5_K1_turnTable_half_faithful
import Theorems.Thm_APFPaper5_K1_ownTable_eq
import Theorems.Thm_APFPaper5_K1_turnClass_negative
import Theorems.Thm_APFPaper5_K1_turnTable_on_classes
set_option autoImplicit false
universe apfNative_uX apfNative_uD

theorem APFPaper5.K2.mem_heldFamily_r2 :
∀ {X : Type apfNative_uX} {D : Type apfNative_uD} (reads : D → X → Bool) (S : Finset.{apfNative_uD} D) (x : X) (d : D),
  Iff
    (@Membership.mem.{apfNative_uD, apfNative_uD} D (Finset.{apfNative_uD} D)
      (@SetLike.instMembership.{apfNative_uD, apfNative_uD} (Finset.{apfNative_uD} D) D
        (@Finset.instSetLike.{apfNative_uD} D))
      (@APFPaper5.K2.heldFamily.{apfNative_uX, apfNative_uD} X D reads S x) d)
    (And
      (@Membership.mem.{apfNative_uD, apfNative_uD} D (Finset.{apfNative_uD} D)
        (@SetLike.instMembership.{apfNative_uD, apfNative_uD} (Finset.{apfNative_uD} D) D
          (@Finset.instSetLike.{apfNative_uD} D))
        S d)
      (@Eq.{1} Bool (reads d x) Bool.true)) := by sorry
