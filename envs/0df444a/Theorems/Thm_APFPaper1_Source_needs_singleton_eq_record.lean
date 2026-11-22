-- Prove2me | Theorems.Thm_APFPaper1_Source_needs_singleton_eq_record
-- name    : APFPaper1.Source.needs_singleton_eq_record
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T14:11:33.3898+00:00
-- url     : https://prove2.me/theorems/a5be706b-f977-4361-9d5f-52dfccd88a14
-- title:
--   needs singleton eq record
-- statement:
--   Scope and conditions: On supplied protocol data, OneRecordEach is equivalent to KeepingDraws, and gives drawing monotonicity. The assigned record is a set, not necessarily a singleton or uniquely assigned. Feasible families have a protocol minimizing the natural-number count of kept records. With an exact nonnegative epsilon-per-record bill, that protocol attains the task infimum; with positive epsilon and support novelty, a feasible marginal step costs at least epsilon, yielding the declared MarginalFloor predicate. These implications do not certify the physical bill or current B06 typing, and do not derive B05 without their explicit bill premise.
--
--   Exact source statement:
--
--   theorem needs_singleton_eq_record (recordOf : D → Set Record)
--       (hrec : ∀ (p : P) (d : D),
--         (∃ sigma : Set Record,
--             sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma) ↔
--           recordOf d ⊆ maintained p)
--       (d : D) (q : P) (hq : maintained q = recordOf d) :
--       sourceNeeds maintained sufficient usesToRealize ({d} : Finset D) = recordOf d
--
--   Source parameters:
--
--   variable {D P R Record : Type*}
--   variable (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
--     (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
-- source:
--   ['Theorems.Thm_APFPaper1_one_record_each_and_the_floor_from_the_bill:195; USB pullbacks v58 batch B; SHA-256 ff8d45da4cfb73de5f0fe978e894c202fee211fbe350103befd119f5f55862cf']

import Definitions.Def_APFPaper1_OneRecordEach
import Definitions.Def_APF_B05_DeclaredInput_r2
set_option autoImplicit false
universe apfNative_u_1 apfNative_u_2 apfNative_u_4

theorem APFPaper1.Source.needs_singleton_eq_record :
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
  (d : D) (q : P) (hq : @Eq.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record) (maintained q) (recordOf d)),
  @Eq.{apfNative_u_4 + 1} (Set.{apfNative_u_4} Record)
    (@APFPaper5.K1.sourceNeeds.{apfNative_u_1, apfNative_u_2, apfNative_u_4} D P Record maintained sufficient
      usesToRealize
      (@Singleton.singleton.{apfNative_u_1, apfNative_u_1} D (Finset.{apfNative_u_1} D)
        (@Finset.instSingleton.{apfNative_u_1} D) d))
    (recordOf d) := by sorry
