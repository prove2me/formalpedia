-- Prove2me | solution 1 for relDistanceToSet_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:22:20.015997+00:00
-- url     : https://prove2.me/submissions/b0d45d8c-3cb5-481e-a4cc-634026251584

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {D S : Type*} [Fintype D] [DecidableEq S]
    (f : D → S) (C : Set (D → S)) : 0 ≤ relDistanceToSet f C := by
  simp only [relDistanceToSet, relDistance]
  apply Real.sInf_nonneg
  rintro _ ⟨_, _, rfl⟩
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
