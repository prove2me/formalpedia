-- Prove2me | Theorems.Thm_APFPaper1_Source_familyCost_eq_bill_of_fewest
-- name    : APFPaper1.Source.familyCost_eq_bill_of_fewest
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T13:39:56.660191+00:00
-- url     : https://prove2.me/theorems/9cf92e21-cd3b-40eb-adb4-3dd34747e508
-- title:
--   familyCost eq bill of fewest
-- statement:
--   Scope and conditions: On supplied protocol data, OneRecordEach is equivalent to KeepingDraws, and gives drawing monotonicity. The assigned record is a set, not necessarily a singleton or uniquely assigned. Feasible families have a protocol minimizing the natural-number count of kept records. With an exact nonnegative epsilon-per-record bill, that protocol attains the task infimum; with positive epsilon and support novelty, a feasible marginal step costs at least epsilon, yielding the declared MarginalFloor predicate. These implications do not certify the physical bill or current B06 typing, and do not derive B05 without their explicit bill premise.
--
--   Exact source statement:
--
--   theorem familyCost_eq_bill_of_fewest (kept : P → Finset Record) (eps : ℝ)
--       (h : BillIsEpsilonPerRecord wholeResource calibration maintained kept eps) (heps : 0 ≤ eps)
--       (S : Finset D) (p : P) (hp : SourceServes maintained sufficient usesToRealize p S)
--       (hmin : ∀ q : P, SourceServes maintained sufficient usesToRealize q S →
--         (kept p).card ≤ (kept q).card) :
--       familyCost wholeResource calibration maintained sufficient usesToRealize S =
--         eps * ((kept p).card : ℝ)
--
--   Source parameters:
--
--   variable {D P R Record : Type*}
--   variable (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
--     (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
-- source:
--   ['Theorems.Thm_APFPaper1_one_record_each_and_the_floor_from_the_bill:232; USB pullbacks v58 batch B; SHA-256 ff8d45da4cfb73de5f0fe978e894c202fee211fbe350103befd119f5f55862cf']

import Definitions.Def_APFPaper1_OneRecordEach
import Definitions.Def_APF_B05_DeclaredInput_r2
set_option autoImplicit false
universe apfNative_u_1 apfNative_u_2 apfNative_u_3 apfNative_u_4

theorem APFPaper1.Source.familyCost_eq_bill_of_fewest :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {R : Type apfNative_u_3} {Record : Type apfNative_u_4}
  (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set.{apfNative_u_4} Record)
  (sufficient : P → Set.{apfNative_u_4} Record → D → Prop) (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop)
  (kept : P → Finset.{apfNative_u_4} Record) (eps : Real)
  (h :
    @APFPaper1.Source.BillIsEpsilonPerRecord.{apfNative_u_2, apfNative_u_3, apfNative_u_4} P R Record wholeResource
      calibration maintained kept eps)
  (heps : @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps)
  (S : Finset.{apfNative_u_1} D) (p : P)
  (hp :
    @APFPaper5.K1.SourceServes.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
      usesToRealize p S)
  (hmin :
    ∀ (q : P),
      @APFPaper5.K1.SourceServes.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
          usesToRealize q S →
        @LE.le.{0} Nat instLENat (@Finset.card.{apfNative_u_4} Record (kept p))
          (@Finset.card.{apfNative_u_4} Record (kept q))),
  @Eq.{1} Real
    (@APFPaper1.Source.familyCost.{apfNative_u_1, apfNative_u_2, apfNative_u_3, apfNative_u_4} D P R Record
      wholeResource calibration maintained sufficient usesToRealize S)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) eps
      (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{apfNative_u_4} Record (kept p)))) := by sorry
