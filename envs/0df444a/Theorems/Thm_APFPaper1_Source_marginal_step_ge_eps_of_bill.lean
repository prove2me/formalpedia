-- Prove2me | Theorems.Thm_APFPaper1_Source_marginal_step_ge_eps_of_bill
-- name    : APFPaper1.Source.marginal_step_ge_eps_of_bill
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T14:11:35.822852+00:00
-- url     : https://prove2.me/theorems/a4aacb86-06c4-44e0-b219-529ff5ba16f9
-- title:
--   marginal step ge eps of bill
-- statement:
--   Scope and conditions: On supplied protocol data, OneRecordEach is equivalent to KeepingDraws, and gives drawing monotonicity. The assigned record is a set, not necessarily a singleton or uniquely assigned. Feasible families have a protocol minimizing the natural-number count of kept records. With an exact nonnegative epsilon-per-record bill, that protocol attains the task infimum; with positive epsilon and support novelty, a feasible marginal step costs at least epsilon, yielding the declared MarginalFloor predicate. These implications do not certify the physical bill or current B06 typing, and do not derive B05 without their explicit bill premise.
--
--   Exact source statement:
--
--   theorem marginal_step_ge_eps_of_bill [DecidableEq D] (kept : P → Finset Record) (eps : ℝ)
--       (h : BillIsEpsilonPerRecord wholeResource calibration maintained kept eps) (heps : 0 < eps)
--       (S : Finset D) (d : D)
--       (hS : familyFeasible maintained sufficient usesToRealize S)
--       (hT : familyFeasible maintained sufficient usesToRealize (insert d S))
--       (hnov : supportNovel wholeResource calibration maintained sufficient usesToRealize S d) :
--       eps ≤ familyCost wholeResource calibration maintained sufficient usesToRealize (insert d S) -
--         familyCost wholeResource calibration maintained sufficient usesToRealize S
--
--   Source parameters:
--
--   variable {D P R Record : Type*}
--   variable (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
--     (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
-- source:
--   ['Theorems.Thm_APFPaper1_one_record_each_and_the_floor_from_the_bill:251; USB pullbacks v58 batch B; SHA-256 ff8d45da4cfb73de5f0fe978e894c202fee211fbe350103befd119f5f55862cf']

import Definitions.Def_APFPaper1_OneRecordEach
import Definitions.Def_APF_B05_DeclaredInput_r2
set_option autoImplicit false
universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4

theorem APFPaper1.Source.marginal_step_ge_eps_of_bill :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set.{apfNative_u_4} Record)
  (sufficient : P → Set.{apfNative_u_4} Record → D → Prop) (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop)
  [inst : DecidableEq.{apfNative_u_1 + 1} D] (kept : P → Finset.{apfNative_u_4} Record) (eps : Real)
  (h :
    @APFPaper1.Source.BillIsEpsilonPerRecord.{apfNative_u_2, apfNative_u_3, apfNative_u_4} P R Record wholeResource
      calibration maintained kept eps)
  (heps : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps)
  (S : Finset.{apfNative_u_1} D) (d : D)
  (hS :
    @APFPaper1.Source.familyFeasible.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
      usesToRealize S)
  (hT :
    @APFPaper1.Source.familyFeasible.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
      usesToRealize
      (@Insert.insert.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
        (@Finset.instInsert.{apfNative_u_1} D inst) d S))
  (hnov :
    @APFPaper1.Source.supportNovel.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
      wholeResource calibration maintained sufficient usesToRealize S d),
  @LE.le.{0} Real Real.instLE eps
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
        wholeResource calibration maintained sufficient usesToRealize
        (@Insert.insert.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
          (@Finset.instInsert.{apfNative_u_1} D inst) d S))
      (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
        wholeResource calibration maintained sufficient usesToRealize S)) := by sorry
