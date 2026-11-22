-- Prove2me | Theorems.Thm_APFPaper1_Source_record_subset_needs
-- name    : APFPaper1.Source.record_subset_needs
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T14:13:35.2628+00:00
-- url     : https://prove2.me/theorems/e19a8910-d326-4ae3-93fd-b835b156affd
-- title:
--   record subset needs
-- statement:
--   Scope and conditions: On supplied protocol data, OneRecordEach is equivalent to KeepingDraws, and gives drawing monotonicity. The assigned record is a set, not necessarily a singleton or uniquely assigned. Feasible families have a protocol minimizing the natural-number count of kept records. With an exact nonnegative epsilon-per-record bill, that protocol attains the task infimum; with positive epsilon and support novelty, a feasible marginal step costs at least epsilon, yielding the declared MarginalFloor predicate. These implications do not certify the physical bill or current B06 typing, and do not derive B05 without their explicit bill premise.
--
--   Exact source statement:
--
--   theorem record_subset_needs (recordOf : D → Set Record)
--       (hrec : ∀ (p : P) (d : D),
--         (∃ sigma : Set Record,
--             sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) ↔
--           recordOf d ⊆ maintained p)
--       (S : Finset D) (d : D) (hd : d ∈ S) :
--       recordOf d ⊆ sourceNeeds maintained sufficient usesToRealize S
--
--   Source parameters:
--
--   variable {D P R Record : Type*}
--   variable (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
--     (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
-- source:
--   ['Theorems.Thm_APFPaper1_one_record_each_and_the_floor_from_the_bill:182; USB pullbacks v58 batch B; SHA-256 ff8d45da4cfb73de5f0fe978e894c202fee211fbe350103befd119f5f55862cf']

import Definitions.Def_APFPaper1_OneRecordEach
import Definitions.Def_APF_B05_DeclaredInput_r2
set_option autoImplicit false
universe apfNative_u_1 apfNative_u_2 apfNative_u_4

theorem APFPaper1.Source.record_subset_needs :
∀ {D : Type apfNative_u_1} {P : Type apfNative_u_2} {Record : Type apfNative_u_4}
  (maintained : P → Set.{apfNative_u_4} Record) (sufficient : P → Set.{apfNative_u_4} Record → D → Prop)
  (usesToRealize : P → D → Set.{apfNative_u_4} Record → Prop) (recordOf : D → Set.{apfNative_u_4} Record)
  (hrec :
    ∀ (p : P) (d : D),
      Iff
        (@Exists.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record) fun (sigma : Set.{apfNative_u_4} Record) =>
          And
            (@LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record) sigma
              (maintained p))
            (And (sufficient p sigma d) (usesToRealize p d sigma)))
        (@LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record) (recordOf d)
          (maintained p)))
  (S : Finset.{apfNative_u_1} D) (d : D)
  (hd :
    @Membership.mem.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
      (@SetLike.instMembership.{apfNative_u_1, apfNative_u_1} (Finset.{apfNative_u_1} D) D
        (@Finset.instSetLike.{apfNative_u_1} D))
      S d),
  @LE.le.{apfNative_u_4} (Set.{apfNative_u_4} Record) (@Set.instLE.{apfNative_u_4} Record) (recordOf d)
    (@APFPaper5.K1.sourceNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
      usesToRealize S) := by sorry
