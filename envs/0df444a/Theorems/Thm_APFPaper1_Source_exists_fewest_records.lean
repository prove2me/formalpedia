-- Prove2me | Theorems.Thm_APFPaper1_Source_exists_fewest_records
-- name    : APFPaper1.Source.exists_fewest_records
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T13:39:53.898394+00:00
-- url     : https://prove2.me/theorems/6887a512-4909-4bce-ae62-86091a85e564
-- title:
--   exists fewest records
-- statement:
--   Scope and conditions: On supplied protocol data, OneRecordEach is equivalent to KeepingDraws, and gives drawing monotonicity. The assigned record is a set, not necessarily a singleton or uniquely assigned. Feasible families have a protocol minimizing the natural-number count of kept records. With an exact nonnegative epsilon-per-record bill, that protocol attains the task infimum; with positive epsilon and support novelty, a feasible marginal step costs at least epsilon, yielding the declared MarginalFloor predicate. These implications do not certify the physical bill or current B06 typing, and do not derive B05 without their explicit bill premise.
--
--   Exact source statement:
--
--   theorem exists_fewest_records (kept : P → Finset Record) (S : Finset D)
--       (hfeas : familyFeasible maintained sufficient usesToRealize S) :
--       ∃ p : P, SourceServes maintained sufficient usesToRealize p S ∧
--         ∀ q : P, SourceServes maintained sufficient usesToRealize q S →
--           (kept p).card ≤ (kept q).card
--
--   Source parameters:
--
--   variable {D P R Record : Type*}
--   variable (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
--     (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
-- source:
--   ['Theorems.Thm_APFPaper1_one_record_each_and_the_floor_from_the_bill:216; USB pullbacks v58 batch B; SHA-256 ff8d45da4cfb73de5f0fe978e894c202fee211fbe350103befd119f5f55862cf']

import Definitions.Def_APFPaper1_OneRecordEach
import Definitions.Def_APF_B05_DeclaredInput_r2
set_option autoImplicit false
universe apfNative_u_1 apfNative_u_2 apfNative_u_4

theorem APFPaper1.Source.exists_fewest_records :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_4}
  (maintained : P → Set.{apfNative_u_4} Record) (sufficient : P → Set.{apfNative_u_4} Record → D → Prop)
  (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop) (kept : P → Finset.{apfNative_u_4} Record)
  (S : Finset.{apfNative_u_1} D)
  (hfeas :
    @APFPaper1.Source.familyFeasible.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
      usesToRealize S),
  @Exists.{apfNative_u_2 + 1} P fun (p : P) =>
    And
      (@APFPaper5.K1.SourceServes.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
        usesToRealize p S)
      (∀ (q : P),
        @APFPaper5.K1.SourceServes.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
            usesToRealize q S →
          @LE.le.{0} Nat instLENat (@Finset.card.{apfNative_u_4} Record (kept p))
            (@Finset.card.{apfNative_u_4} Record (kept q))) := by sorry
