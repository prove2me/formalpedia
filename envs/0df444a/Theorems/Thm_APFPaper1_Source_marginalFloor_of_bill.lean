-- Prove2me | Theorems.Thm_APFPaper1_Source_marginalFloor_of_bill
-- name    : APFPaper1.Source.marginalFloor_of_bill
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T13:41:51.809699+00:00
-- url     : https://prove2.me/theorems/247e4b8c-8507-45da-8278-a24bbc89c1d2
-- title:
--   marginalFloor of bill
-- statement:
--   Scope and conditions: On supplied protocol data, OneRecordEach is equivalent to KeepingDraws, and gives drawing monotonicity. The assigned record is a set, not necessarily a singleton or uniquely assigned. Feasible families have a protocol minimizing the natural-number count of kept records. With an exact nonnegative epsilon-per-record bill, that protocol attains the task infimum; with positive epsilon and support novelty, a feasible marginal step costs at least epsilon, yielding the declared MarginalFloor predicate. These implications do not certify the physical bill or current B06 typing, and do not derive B05 without their explicit bill premise.
--
--   Exact source statement:
--
--   theorem marginalFloor_of_bill {Context : Type*} {D P R Record : Context → Type*}
--       [∀ g, DecidableEq (D g)]
--       (wholeResource : (g : Context) → P g → R g)
--       (calibration : (g : Context) → R g → NNReal)
--       (maintained : (g : Context) → P g → Set (Record g))
--       (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
--       (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
--       (tested : (g : Context) → D g → Prop)
--       (C epsilon : Context → ℝ)
--       (kept : (g : Context) → P g → Finset (Record g))
--       (h : ∀ g, 0 < epsilon g ∧
--         BillIsEpsilonPerRecord (wholeResource g) (calibration g) (maintained g) (kept g)
--           (epsilon g)) :
--       APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize tested C
--         epsilon
--
--   Source parameters:
--
--   variable {D P R Record : Type*}
--   variable (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
--     (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
-- source:
--   ['Theorems.Thm_APFPaper1_one_record_each_and_the_floor_from_the_bill:308; USB pullbacks v58 batch B; SHA-256 ff8d45da4cfb73de5f0fe978e894c202fee211fbe350103befd119f5f55862cf']

import Definitions.Def_APFPaper1_OneRecordEach
import Definitions.Def_APF_B05_DeclaredInput_r2
set_option autoImplicit false
universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4 apfNative_u_5

theorem APFPaper1.Source.marginalFloor_of_bill :
∀ {Context : Type apfNative_u_1} {D : Context → Type apfNative_u_2} {P : Context → Type apfNative_u_3}
  {R : Context → Type apfNative_u_4} {Record : Context → Type apfNative_u_5}
  [inst : (g : Context) → DecidableEq.{apfNative_u_2 + 1} (D g)] (wholeResource : (g : Context) → P g → R g)
  (calibration : (g : Context) → R g → NNReal) (maintained : (g : Context) → P g → Set.{apfNative_u_5} (Record g))
  (sufficient : (g : Context) → P g → Set.{apfNative_u_5} (Record g) → D g → Prop)
  (usesToRealize : (g : Context) → P g → D g → Set.{apfNative_u_5} (Record g) → Prop)
  (tested : (g : Context) → D g → Prop) (C epsilon : Context → Real)
  (kept : (g : Context) → P g → Finset.{apfNative_u_5} (Record g))
  (h :
    ∀ (g : Context),
      And
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (epsilon g))
        (@APFPaper1.Source.BillIsEpsilonPerRecord.{apfNative_u_3, apfNative_u_4, apfNative_u_5} (P g) (R g) (Record g)
          (wholeResource g) (calibration g) (maintained g) (kept g) (epsilon g))),
  @APFB05.MarginalFloor.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4, apfNative_u_5} Context D P R Record
    inst wholeResource calibration maintained sufficient usesToRealize tested C epsilon := by sorry
