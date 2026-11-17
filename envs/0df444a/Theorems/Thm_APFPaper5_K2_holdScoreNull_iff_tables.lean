-- Prove2me | Theorems.Thm_APFPaper5_K2_holdScoreNull_iff_tables
-- name    : APFPaper5.K2.holdScoreNull_iff_tables
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T19:41:21.557204+00:00
-- url     : https://prove2.me/theorems/b4965277-b7b2-4f9c-8988-27e9edfe2e9a
-- title:
--   holdScoreNull iff tables
-- statement:
--   Result: holdScoreNull iff tables. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem holdScoreNull_iff_tables {κ : Type uK} [Fintype κ] (G : ι → ι → ℝ) (coef : κ → ℝ)
--       (sigma : κ → Equiv.Perm ι) :
--       HoldScoreNull G coef (fun k => (sigma k : ι → ι)) ↔
--         ∀ a j : ι, ∑ k, coef k * G ((sigma k).symm a) j = 0
--   ```
--
--   Module context and limits: The score uses a supplied table and precomposition of classes; side flips do not enter it. KeepsTable is an explicit hypothesis for inverse-as-adjoint and orientation results. The later author reading adopts preservation for holds but does not remove this Lean hypothesis or amend FOUNDATION_INPUTS.
--
--   Source scope parameters:
--
--   ```lean
--   universe uI uX uD uK
--   variable {ι : Type uI}
--   variable [Fintype ι] [DecidableEq ι]
--   variable {D P R Record : Type*} {ι' : Type*} [Fintype ι'] [DecidableEq ι'] [DecidableEq D]
--     [Fintype Record]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K2_hold_score:223; pullbacks v39; source SHA-256 6ef958f4665bf38b5d47b0b531068fdc57cee8a20b837c0e17f66f223c1413c7']

import Definitions.Def_APFPaper5_K2_HoldScore
import Definitions.Def_APFPaper5_K1_identity_exchange_Vocabulary
import Theorems.Thm_APFPaper5_K1_tableForm_markClass
import Theorems.Thm_APFPaper5_K1_table_linearizes
import Theorems.Thm_APFPaper5_K1_nondegenerate_of_faithful_identity
import Theorems.Thm_APFPaper5_K1_orientationForm_zero_of_symm
import Theorems.Thm_APFPaper5_K1_ledgerForm_eq_of_symm
import Theorems.Thm_APFPaper5_K1_sourcePartyScore_symm
import Theorems.Thm_APFPaper5_K1_source_counted_family_meets_all_of_K1_with_identity_exchange
import Theorems.Thm_APFPaper5_K1_tableForm_symm
import Theorems.Thm_APFPaper5_K1_roleExchange_respects_null
import Theorems.Thm_APFPaper5_K1_interchangeable_posDef
import Theorems.Thm_APFPaper5_K1_tableForm_isBilinear
import Theorems.Thm_APFPaper5_K1_interchangeable_marks_satisfy_K1
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Ring
set_option autoImplicit false
universe apfNative_uI apfNative_uK

theorem APFPaper5.K2.holdScoreNull_iff_tables :
∀ {ι : Type apfNative_uI} [inst : Fintype.{apfNative_uI} ι] [DecidableEq.{apfNative_uI + 1} ι] {κ : Type apfNative_uK}
  [inst_2 : Fintype.{apfNative_uK} κ] (G : ι → ι → Real) (coef : κ → Real)
  (sigma : κ → Equiv.Perm.{apfNative_uI + 1} ι),
  Iff
    (@APFPaper5.K2.HoldScoreNull.{apfNative_uI, apfNative_uK} ι inst κ inst_2 G coef fun (k : κ) =>
      @DFunLike.coe.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} (Equiv.Perm.{apfNative_uI + 1} ι) ι
        (fun (x : ι) => ι)
        (@EquivLike.toFunLike.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1} (Equiv.Perm.{apfNative_uI + 1} ι) ι
          ι (@Equiv.instEquivLike.{apfNative_uI + 1, apfNative_uI + 1} ι ι))
        (sigma k))
    (∀ (a j : ι),
      @Eq.{1} Real
        (@Finset.sum.{apfNative_uK, 0} κ Real Real.instAddCommMonoid (@Finset.univ.{apfNative_uK} κ inst_2)
          fun (k : κ) =>
          @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (coef k)
            (G
              (@DFunLike.coe.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1}
                (Equiv.{apfNative_uI + 1, apfNative_uI + 1} ι ι) ι (fun (x : ι) => ι)
                (@EquivLike.toFunLike.{apfNative_uI + 1, apfNative_uI + 1, apfNative_uI + 1}
                  (Equiv.{apfNative_uI + 1, apfNative_uI + 1} ι ι) ι ι
                  (@Equiv.instEquivLike.{apfNative_uI + 1, apfNative_uI + 1} ι ι))
                (@Equiv.symm.{apfNative_uI + 1, apfNative_uI + 1} ι ι (sigma k)) a)
              j))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) := by sorry
