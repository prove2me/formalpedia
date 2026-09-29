-- Prove2me | solution 1 for syracuse_descends_range_199806_203806
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:52.478453+00:00
-- url     : https://prove2.me/submissions/41c5e1a5-ad06-4422-abb8-4c3f36a7b32a

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

/-- Half of all odd numbers descend in a single Syracuse step, uniformly. -/
theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- `Blo L x` : some Syracuse iterate of `x` drops below `L`. -/
abbrev Blo (L x : ℕ) : Prop := ∃ t : ℕ, syracuseStep^[t] x < L

theorem bbase {L x y : ℕ} (h : syracuseStep x = y) (hy : y < L) : Blo L x :=
  ⟨1, by rw [Function.iterate_one, h]; exact hy⟩

theorem bstep {L x y : ℕ} (h : syracuseStep x = y) (hy : Blo L y) : Blo L x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact ht⟩

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


theorem B983125 : Blo 199806 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B327917 : Blo 199806 327917 := bbase (se 3 (by rfl) ⟨61484, by rfl⟩ : syracuseStep 327917 = 122969) (by norm_num)
theorem B459445 : Blo 199806 459445 := bbase (se 5 (by rfl) ⟨21536, by rfl⟩ : syracuseStep 459445 = 43073) (by norm_num)
theorem B1016549 : Blo 199806 1016549 := bbase (se 4 (by rfl) ⟨95301, by rfl⟩ : syracuseStep 1016549 = 190603) (by norm_num)
theorem B1442549 : Blo 199806 1442549 := bbase (se 5 (by rfl) ⟨67619, by rfl⟩ : syracuseStep 1442549 = 135239) (by norm_num)
theorem B262909 : Blo 199806 262909 := bbase (se 3 (by rfl) ⟨49295, by rfl⟩ : syracuseStep 262909 = 98591) (by norm_num)
theorem B1737845 : Blo 199806 1737845 := bbase (se 5 (by rfl) ⟨81461, by rfl⟩ : syracuseStep 1737845 = 162923) (by norm_num)
theorem B427285 : Blo 199806 427285 := bbase (se 6 (by rfl) ⟨10014, by rfl⟩ : syracuseStep 427285 = 20029) (by norm_num)
theorem B427781 : Blo 199806 427781 := bbase (se 4 (by rfl) ⟨40104, by rfl⟩ : syracuseStep 427781 = 80209) (by norm_num)
theorem B1017845 : Blo 199806 1017845 := bbase (se 5 (by rfl) ⟨47711, by rfl⟩ : syracuseStep 1017845 = 95423) (by norm_num)
theorem B362765 : Blo 199806 362765 := bbase (se 3 (by rfl) ⟨68018, by rfl⟩ : syracuseStep 362765 = 136037) (by norm_num)
theorem B1968437 : Blo 199806 1968437 := bbase (se 5 (by rfl) ⟨92270, by rfl⟩ : syracuseStep 1968437 = 184541) (by norm_num)
theorem B1935701 : Blo 199806 1935701 := bbase (se 10 (by rfl) ⟨2835, by rfl⟩ : syracuseStep 1935701 = 5671) (by norm_num)
theorem B3705173 : Blo 199806 3705173 := bbase (se 10 (by rfl) ⟨5427, by rfl⟩ : syracuseStep 3705173 = 10855) (by norm_num)
theorem B3082645 : Blo 199806 3082645 := bbase (se 6 (by rfl) ⟨72249, by rfl⟩ : syracuseStep 3082645 = 144499) (by norm_num)
theorem B428645 : Blo 199806 428645 := bbase (se 4 (by rfl) ⟨40185, by rfl⟩ : syracuseStep 428645 = 80371) (by norm_num)
theorem B232057 : Blo 199806 232057 := bbase (se 2 (by rfl) ⟨87021, by rfl⟩ : syracuseStep 232057 = 174043) (by norm_num)
theorem B789173 : Blo 199806 789173 := bbase (se 5 (by rfl) ⟨36992, by rfl⟩ : syracuseStep 789173 = 73985) (by norm_num)
theorem B428789 : Blo 199806 428789 := bbase (se 5 (by rfl) ⟨20099, by rfl⟩ : syracuseStep 428789 = 40199) (by norm_num)
theorem B854981 : Blo 199806 854981 := bbase (se 4 (by rfl) ⟨80154, by rfl⟩ : syracuseStep 854981 = 160309) (by norm_num)
theorem B232409 : Blo 199806 232409 := bbase (se 2 (by rfl) ⟨87153, by rfl⟩ : syracuseStep 232409 = 174307) (by norm_num)
theorem B1019141 : Blo 199806 1019141 := bbase (se 4 (by rfl) ⟨95544, by rfl⟩ : syracuseStep 1019141 = 191089) (by norm_num)
theorem B920933 : Blo 199806 920933 := bbase (se 4 (by rfl) ⟨86337, by rfl⟩ : syracuseStep 920933 = 172675) (by norm_num)
theorem B429533 : Blo 199806 429533 := bbase (se 3 (by rfl) ⟨80537, by rfl⟩ : syracuseStep 429533 = 161075) (by norm_num)
theorem B822757 : Blo 199806 822757 := bbase (se 4 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 822757 = 154267) (by norm_num)
theorem B1445525 : Blo 199806 1445525 := bbase (se 6 (by rfl) ⟨33879, by rfl⟩ : syracuseStep 1445525 = 67759) (by norm_num)
theorem B364213 : Blo 199806 364213 := bbase (se 5 (by rfl) ⟨17072, by rfl⟩ : syracuseStep 364213 = 34145) (by norm_num)
theorem B495325 : Blo 199806 495325 := bbase (se 3 (by rfl) ⟨92873, by rfl⟩ : syracuseStep 495325 = 185747) (by norm_num)
theorem B691973 : Blo 199806 691973 := bbase (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) (by norm_num)
theorem B331589 : Blo 199806 331589 := bbase (se 4 (by rfl) ⟨31086, by rfl⟩ : syracuseStep 331589 = 62173) (by norm_num)
theorem B1544021 : Blo 199806 1544021 := bbase (se 9 (by rfl) ⟨4523, by rfl⟩ : syracuseStep 1544021 = 9047) (by norm_num)
theorem B200885 : Blo 199806 200885 := bbase (se 5 (by rfl) ⟨9416, by rfl⟩ : syracuseStep 200885 = 18833) (by norm_num)
theorem B430285 : Blo 199806 430285 := bbase (se 3 (by rfl) ⟨80678, by rfl⟩ : syracuseStep 430285 = 161357) (by norm_num)
theorem B430429 : Blo 199806 430429 := bbase (se 3 (by rfl) ⟨80705, by rfl⟩ : syracuseStep 430429 = 161411) (by norm_num)
theorem B1020437 : Blo 199806 1020437 := bbase (se 6 (by rfl) ⟨23916, by rfl⟩ : syracuseStep 1020437 = 47833) (by norm_num)
theorem B856757 : Blo 199806 856757 := bbase (se 5 (by rfl) ⟨40160, by rfl⟩ : syracuseStep 856757 = 80321) (by norm_num)
theorem B299717 : Blo 199806 299717 := bbase (se 4 (by rfl) ⟨28098, by rfl⟩ : syracuseStep 299717 = 56197) (by norm_num)
theorem B430805 : Blo 199806 430805 := bbase (se 7 (by rfl) ⟨5048, by rfl⟩ : syracuseStep 430805 = 10097) (by norm_num)
theorem B824021 : Blo 199806 824021 := bbase (se 7 (by rfl) ⟨9656, by rfl⟩ : syracuseStep 824021 = 19313) (by norm_num)
theorem B299741 : Blo 199806 299741 := bbase (se 3 (by rfl) ⟨56201, by rfl⟩ : syracuseStep 299741 = 112403) (by norm_num)
theorem B299765 : Blo 199806 299765 := bbase (se 5 (by rfl) ⟨14051, by rfl⟩ : syracuseStep 299765 = 28103) (by norm_num)
theorem B299789 : Blo 199806 299789 := bbase (se 3 (by rfl) ⟨56210, by rfl⟩ : syracuseStep 299789 = 112421) (by norm_num)
theorem B299813 : Blo 199806 299813 := bbase (se 4 (by rfl) ⟨28107, by rfl⟩ : syracuseStep 299813 = 56215) (by norm_num)
theorem B299837 : Blo 199806 299837 := bbase (se 3 (by rfl) ⟨56219, by rfl⟩ : syracuseStep 299837 = 112439) (by norm_num)
theorem B299861 : Blo 199806 299861 := bbase (se 9 (by rfl) ⟨878, by rfl⟩ : syracuseStep 299861 = 1757) (by norm_num)
theorem B824149 : Blo 199806 824149 := bbase (se 9 (by rfl) ⟨2414, by rfl⟩ : syracuseStep 824149 = 4829) (by norm_num)
theorem B299885 : Blo 199806 299885 := bbase (se 3 (by rfl) ⟨56228, by rfl⟩ : syracuseStep 299885 = 112457) (by norm_num)
theorem B299909 : Blo 199806 299909 := bbase (se 4 (by rfl) ⟨28116, by rfl⟩ : syracuseStep 299909 = 56233) (by norm_num)
theorem B299933 : Blo 199806 299933 := bbase (se 3 (by rfl) ⟨56237, by rfl⟩ : syracuseStep 299933 = 112475) (by norm_num)
theorem B299957 : Blo 199806 299957 := bbase (se 5 (by rfl) ⟨14060, by rfl⟩ : syracuseStep 299957 = 28121) (by norm_num)
theorem B299981 : Blo 199806 299981 := bbase (se 3 (by rfl) ⟨56246, by rfl⟩ : syracuseStep 299981 = 112493) (by norm_num)
theorem B300005 : Blo 199806 300005 := bbase (se 4 (by rfl) ⟨28125, by rfl⟩ : syracuseStep 300005 = 56251) (by norm_num)
theorem B300029 : Blo 199806 300029 := bbase (se 3 (by rfl) ⟨56255, by rfl⟩ : syracuseStep 300029 = 112511) (by norm_num)
theorem B300053 : Blo 199806 300053 := bbase (se 6 (by rfl) ⟨7032, by rfl⟩ : syracuseStep 300053 = 14065) (by norm_num)
theorem B365597 : Blo 199806 365597 := bbase (se 3 (by rfl) ⟨68549, by rfl⟩ : syracuseStep 365597 = 137099) (by norm_num)
theorem B300077 : Blo 199806 300077 := bbase (se 3 (by rfl) ⟨56264, by rfl⟩ : syracuseStep 300077 = 112529) (by norm_num)
theorem B300101 : Blo 199806 300101 := bbase (se 4 (by rfl) ⟨28134, by rfl⟩ : syracuseStep 300101 = 56269) (by norm_num)
theorem B431173 : Blo 199806 431173 := bbase (se 4 (by rfl) ⟨40422, by rfl⟩ : syracuseStep 431173 = 80845) (by norm_num)
theorem B300125 : Blo 199806 300125 := bbase (se 3 (by rfl) ⟨56273, by rfl⟩ : syracuseStep 300125 = 112547) (by norm_num)
theorem B300149 : Blo 199806 300149 := bbase (se 5 (by rfl) ⟨14069, by rfl⟩ : syracuseStep 300149 = 28139) (by norm_num)
theorem B300173 : Blo 199806 300173 := bbase (se 3 (by rfl) ⟨56282, by rfl⟩ : syracuseStep 300173 = 112565) (by norm_num)
theorem B300197 : Blo 199806 300197 := bbase (se 4 (by rfl) ⟨28143, by rfl⟩ : syracuseStep 300197 = 56287) (by norm_num)
theorem B300221 : Blo 199806 300221 := bbase (se 3 (by rfl) ⟨56291, by rfl⟩ : syracuseStep 300221 = 112583) (by norm_num)
theorem B300245 : Blo 199806 300245 := bbase (se 7 (by rfl) ⟨3518, by rfl⟩ : syracuseStep 300245 = 7037) (by norm_num)
theorem B300269 : Blo 199806 300269 := bbase (se 3 (by rfl) ⟨56300, by rfl⟩ : syracuseStep 300269 = 112601) (by norm_num)
theorem B300293 : Blo 199806 300293 := bbase (se 4 (by rfl) ⟨28152, by rfl⟩ : syracuseStep 300293 = 56305) (by norm_num)
theorem B300317 : Blo 199806 300317 := bbase (se 3 (by rfl) ⟨56309, by rfl⟩ : syracuseStep 300317 = 112619) (by norm_num)
theorem B300341 : Blo 199806 300341 := bbase (se 5 (by rfl) ⟨14078, by rfl⟩ : syracuseStep 300341 = 28157) (by norm_num)
theorem B300365 : Blo 199806 300365 := bbase (se 3 (by rfl) ⟨56318, by rfl⟩ : syracuseStep 300365 = 112637) (by norm_num)
theorem B300389 : Blo 199806 300389 := bbase (se 4 (by rfl) ⟨28161, by rfl⟩ : syracuseStep 300389 = 56323) (by norm_num)
theorem B300413 : Blo 199806 300413 := bbase (se 3 (by rfl) ⟨56327, by rfl⟩ : syracuseStep 300413 = 112655) (by norm_num)
theorem B300437 : Blo 199806 300437 := bbase (se 6 (by rfl) ⟨7041, by rfl⟩ : syracuseStep 300437 = 14083) (by norm_num)
theorem B300461 : Blo 199806 300461 := bbase (se 3 (by rfl) ⟨56336, by rfl⟩ : syracuseStep 300461 = 112673) (by norm_num)
theorem B300485 : Blo 199806 300485 := bbase (se 4 (by rfl) ⟨28170, by rfl⟩ : syracuseStep 300485 = 56341) (by norm_num)
theorem B759253 : Blo 199806 759253 := bbase (se 7 (by rfl) ⟨8897, by rfl⟩ : syracuseStep 759253 = 17795) (by norm_num)
theorem B300509 : Blo 199806 300509 := bbase (se 3 (by rfl) ⟨56345, by rfl⟩ : syracuseStep 300509 = 112691) (by norm_num)
theorem B300533 : Blo 199806 300533 := bbase (se 5 (by rfl) ⟨14087, by rfl⟩ : syracuseStep 300533 = 28175) (by norm_num)
theorem B300557 : Blo 199806 300557 := bbase (se 3 (by rfl) ⟨56354, by rfl⟩ : syracuseStep 300557 = 112709) (by norm_num)
theorem B300581 : Blo 199806 300581 := bbase (se 4 (by rfl) ⟨28179, by rfl⟩ : syracuseStep 300581 = 56359) (by norm_num)
theorem B300605 : Blo 199806 300605 := bbase (se 3 (by rfl) ⟨56363, by rfl⟩ : syracuseStep 300605 = 112727) (by norm_num)
theorem B300629 : Blo 199806 300629 := bbase (se 8 (by rfl) ⟨1761, by rfl⟩ : syracuseStep 300629 = 3523) (by norm_num)
theorem B300653 : Blo 199806 300653 := bbase (se 3 (by rfl) ⟨56372, by rfl⟩ : syracuseStep 300653 = 112745) (by norm_num)
theorem B1283701 : Blo 199806 1283701 := bbase (se 5 (by rfl) ⟨60173, by rfl⟩ : syracuseStep 1283701 = 120347) (by norm_num)
theorem B300677 : Blo 199806 300677 := bbase (se 4 (by rfl) ⟨28188, by rfl⟩ : syracuseStep 300677 = 56377) (by norm_num)
theorem B857749 : Blo 199806 857749 := bbase (se 6 (by rfl) ⟨20103, by rfl⟩ : syracuseStep 857749 = 40207) (by norm_num)
theorem B300701 : Blo 199806 300701 := bbase (se 3 (by rfl) ⟨56381, by rfl⟩ : syracuseStep 300701 = 112763) (by norm_num)
theorem B300725 : Blo 199806 300725 := bbase (se 5 (by rfl) ⟨14096, by rfl⟩ : syracuseStep 300725 = 28193) (by norm_num)
theorem B300749 : Blo 199806 300749 := bbase (se 3 (by rfl) ⟨56390, by rfl⟩ : syracuseStep 300749 = 112781) (by norm_num)
theorem B5183189 : Blo 199806 5183189 := bbase (se 7 (by rfl) ⟨60740, by rfl⟩ : syracuseStep 5183189 = 121481) (by norm_num)
theorem B300773 : Blo 199806 300773 := bbase (se 4 (by rfl) ⟨28197, by rfl⟩ : syracuseStep 300773 = 56395) (by norm_num)
theorem B300797 : Blo 199806 300797 := bbase (se 3 (by rfl) ⟨56399, by rfl⟩ : syracuseStep 300797 = 112799) (by norm_num)
theorem B759557 : Blo 199806 759557 := bbase (se 4 (by rfl) ⟨71208, by rfl⟩ : syracuseStep 759557 = 142417) (by norm_num)
theorem B300821 : Blo 199806 300821 := bbase (se 6 (by rfl) ⟨7050, by rfl⟩ : syracuseStep 300821 = 14101) (by norm_num)
theorem B1021733 : Blo 199806 1021733 := bbase (se 4 (by rfl) ⟨95787, by rfl⟩ : syracuseStep 1021733 = 191575) (by norm_num)
theorem B300845 : Blo 199806 300845 := bbase (se 3 (by rfl) ⟨56408, by rfl⟩ : syracuseStep 300845 = 112817) (by norm_num)
theorem B300869 : Blo 199806 300869 := bbase (se 4 (by rfl) ⟨28206, by rfl⟩ : syracuseStep 300869 = 56413) (by norm_num)
theorem B464717 : Blo 199806 464717 := bbase (se 3 (by rfl) ⟨87134, by rfl⟩ : syracuseStep 464717 = 174269) (by norm_num)
theorem B300893 : Blo 199806 300893 := bbase (se 3 (by rfl) ⟨56417, by rfl⟩ : syracuseStep 300893 = 112835) (by norm_num)
theorem B366437 : Blo 199806 366437 := bbase (se 4 (by rfl) ⟨34353, by rfl⟩ : syracuseStep 366437 = 68707) (by norm_num)
theorem B300917 : Blo 199806 300917 := bbase (se 5 (by rfl) ⟨14105, by rfl⟩ : syracuseStep 300917 = 28211) (by norm_num)
theorem B300941 : Blo 199806 300941 := bbase (se 3 (by rfl) ⟨56426, by rfl⟩ : syracuseStep 300941 = 112853) (by norm_num)
theorem B300965 : Blo 199806 300965 := bbase (se 4 (by rfl) ⟨28215, by rfl⟩ : syracuseStep 300965 = 56431) (by norm_num)
theorem B300989 : Blo 199806 300989 := bbase (se 3 (by rfl) ⟨56435, by rfl⟩ : syracuseStep 300989 = 112871) (by norm_num)
theorem B202693 : Blo 199806 202693 := bbase (se 4 (by rfl) ⟨19002, by rfl⟩ : syracuseStep 202693 = 38005) (by norm_num)
theorem B301013 : Blo 199806 301013 := bbase (se 7 (by rfl) ⟨3527, by rfl⟩ : syracuseStep 301013 = 7055) (by norm_num)
theorem B301037 : Blo 199806 301037 := bbase (se 3 (by rfl) ⟨56444, by rfl⟩ : syracuseStep 301037 = 112889) (by norm_num)
theorem B301061 : Blo 199806 301061 := bbase (se 4 (by rfl) ⟨28224, by rfl⟩ : syracuseStep 301061 = 56449) (by norm_num)
theorem B301085 : Blo 199806 301085 := bbase (se 3 (by rfl) ⟨56453, by rfl⟩ : syracuseStep 301085 = 112907) (by norm_num)
theorem B301109 : Blo 199806 301109 := bbase (se 5 (by rfl) ⟨14114, by rfl⟩ : syracuseStep 301109 = 28229) (by norm_num)
theorem B301133 : Blo 199806 301133 := bbase (se 3 (by rfl) ⟨56462, by rfl⟩ : syracuseStep 301133 = 112925) (by norm_num)
theorem B301157 : Blo 199806 301157 := bbase (se 4 (by rfl) ⟨28233, by rfl⟩ : syracuseStep 301157 = 56467) (by norm_num)
theorem B727157 : Blo 199806 727157 := bbase (se 5 (by rfl) ⟨34085, by rfl⟩ : syracuseStep 727157 = 68171) (by norm_num)
theorem B301181 : Blo 199806 301181 := bbase (se 3 (by rfl) ⟨56471, by rfl⟩ : syracuseStep 301181 = 112943) (by norm_num)
theorem B301205 : Blo 199806 301205 := bbase (se 6 (by rfl) ⟨7059, by rfl⟩ : syracuseStep 301205 = 14119) (by norm_num)
theorem B301229 : Blo 199806 301229 := bbase (se 3 (by rfl) ⟨56480, by rfl⟩ : syracuseStep 301229 = 112961) (by norm_num)
theorem B301253 : Blo 199806 301253 := bbase (se 4 (by rfl) ⟨28242, by rfl⟩ : syracuseStep 301253 = 56485) (by norm_num)
theorem B301277 : Blo 199806 301277 := bbase (se 3 (by rfl) ⟨56489, by rfl⟩ : syracuseStep 301277 = 112979) (by norm_num)
theorem B301301 : Blo 199806 301301 := bbase (se 5 (by rfl) ⟨14123, by rfl⟩ : syracuseStep 301301 = 28247) (by norm_num)
theorem B301325 : Blo 199806 301325 := bbase (se 3 (by rfl) ⟨56498, by rfl⟩ : syracuseStep 301325 = 112997) (by norm_num)
theorem B301349 : Blo 199806 301349 := bbase (se 4 (by rfl) ⟨28251, by rfl⟩ : syracuseStep 301349 = 56503) (by norm_num)
theorem B301373 : Blo 199806 301373 := bbase (se 3 (by rfl) ⟨56507, by rfl⟩ : syracuseStep 301373 = 113015) (by norm_num)
theorem B301397 : Blo 199806 301397 := bbase (se 10 (by rfl) ⟨441, by rfl⟩ : syracuseStep 301397 = 883) (by norm_num)
theorem B301421 : Blo 199806 301421 := bbase (se 3 (by rfl) ⟨56516, by rfl⟩ : syracuseStep 301421 = 113033) (by norm_num)
theorem B301445 : Blo 199806 301445 := bbase (se 4 (by rfl) ⟨28260, by rfl⟩ : syracuseStep 301445 = 56521) (by norm_num)
theorem B301469 : Blo 199806 301469 := bbase (se 3 (by rfl) ⟨56525, by rfl⟩ : syracuseStep 301469 = 113051) (by norm_num)
theorem B301493 : Blo 199806 301493 := bbase (se 5 (by rfl) ⟨14132, by rfl⟩ : syracuseStep 301493 = 28265) (by norm_num)
theorem B301517 : Blo 199806 301517 := bbase (se 3 (by rfl) ⟨56534, by rfl⟩ : syracuseStep 301517 = 113069) (by norm_num)
theorem B301541 : Blo 199806 301541 := bbase (se 4 (by rfl) ⟨28269, by rfl⟩ : syracuseStep 301541 = 56539) (by norm_num)
theorem B301565 : Blo 199806 301565 := bbase (se 3 (by rfl) ⟨56543, by rfl⟩ : syracuseStep 301565 = 113087) (by norm_num)
theorem B301589 : Blo 199806 301589 := bbase (se 6 (by rfl) ⟨7068, by rfl⟩ : syracuseStep 301589 = 14137) (by norm_num)
theorem B432677 : Blo 199806 432677 := bbase (se 4 (by rfl) ⟨40563, by rfl⟩ : syracuseStep 432677 = 81127) (by norm_num)
theorem B301613 : Blo 199806 301613 := bbase (se 3 (by rfl) ⟨56552, by rfl⟩ : syracuseStep 301613 = 113105) (by norm_num)
theorem B301637 : Blo 199806 301637 := bbase (se 4 (by rfl) ⟨28278, by rfl⟩ : syracuseStep 301637 = 56557) (by norm_num)
theorem B301661 : Blo 199806 301661 := bbase (se 3 (by rfl) ⟨56561, by rfl⟩ : syracuseStep 301661 = 113123) (by norm_num)
theorem B301685 : Blo 199806 301685 := bbase (se 5 (by rfl) ⟨14141, by rfl⟩ : syracuseStep 301685 = 28283) (by norm_num)
theorem B301709 : Blo 199806 301709 := bbase (se 3 (by rfl) ⟨56570, by rfl⟩ : syracuseStep 301709 = 113141) (by norm_num)
theorem B301733 : Blo 199806 301733 := bbase (se 4 (by rfl) ⟨28287, by rfl⟩ : syracuseStep 301733 = 56575) (by norm_num)
theorem B432821 : Blo 199806 432821 := bbase (se 5 (by rfl) ⟨20288, by rfl⟩ : syracuseStep 432821 = 40577) (by norm_num)
theorem B301757 : Blo 199806 301757 := bbase (se 3 (by rfl) ⟨56579, by rfl⟩ : syracuseStep 301757 = 113159) (by norm_num)
theorem B301781 : Blo 199806 301781 := bbase (se 7 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 301781 = 7073) (by norm_num)
theorem B301805 : Blo 199806 301805 := bbase (se 3 (by rfl) ⟨56588, by rfl⟩ : syracuseStep 301805 = 113177) (by norm_num)
theorem B301829 : Blo 199806 301829 := bbase (se 4 (by rfl) ⟨28296, by rfl⟩ : syracuseStep 301829 = 56593) (by norm_num)
theorem B301853 : Blo 199806 301853 := bbase (se 3 (by rfl) ⟨56597, by rfl⟩ : syracuseStep 301853 = 113195) (by norm_num)
theorem B301877 : Blo 199806 301877 := bbase (se 5 (by rfl) ⟨14150, by rfl⟩ : syracuseStep 301877 = 28301) (by norm_num)
theorem B301901 : Blo 199806 301901 := bbase (se 3 (by rfl) ⟨56606, by rfl⟩ : syracuseStep 301901 = 113213) (by norm_num)
theorem B301925 : Blo 199806 301925 := bbase (se 4 (by rfl) ⟨28305, by rfl⟩ : syracuseStep 301925 = 56611) (by norm_num)
theorem B301949 : Blo 199806 301949 := bbase (se 3 (by rfl) ⟨56615, by rfl⟩ : syracuseStep 301949 = 113231) (by norm_num)
theorem B301973 : Blo 199806 301973 := bbase (se 6 (by rfl) ⟨7077, by rfl⟩ : syracuseStep 301973 = 14155) (by norm_num)
theorem B301997 : Blo 199806 301997 := bbase (se 3 (by rfl) ⟨56624, by rfl⟩ : syracuseStep 301997 = 113249) (by norm_num)
theorem B302021 : Blo 199806 302021 := bbase (se 4 (by rfl) ⟨28314, by rfl⟩ : syracuseStep 302021 = 56629) (by norm_num)
theorem B302045 : Blo 199806 302045 := bbase (se 3 (by rfl) ⟨56633, by rfl⟩ : syracuseStep 302045 = 113267) (by norm_num)
theorem B302069 : Blo 199806 302069 := bbase (se 5 (by rfl) ⟨14159, by rfl⟩ : syracuseStep 302069 = 28319) (by norm_num)
theorem B302093 : Blo 199806 302093 := bbase (se 3 (by rfl) ⟨56642, by rfl⟩ : syracuseStep 302093 = 113285) (by norm_num)
theorem B433181 : Blo 199806 433181 := bbase (se 3 (by rfl) ⟨81221, by rfl⟩ : syracuseStep 433181 = 162443) (by norm_num)
theorem B302117 : Blo 199806 302117 := bbase (se 4 (by rfl) ⟨28323, by rfl⟩ : syracuseStep 302117 = 56647) (by norm_num)
theorem B1023029 : Blo 199806 1023029 := bbase (se 5 (by rfl) ⟨47954, by rfl⟩ : syracuseStep 1023029 = 95909) (by norm_num)
theorem B302141 : Blo 199806 302141 := bbase (se 3 (by rfl) ⟨56651, by rfl⟩ : syracuseStep 302141 = 113303) (by norm_num)
theorem B302165 : Blo 199806 302165 := bbase (se 8 (by rfl) ⟨1770, by rfl⟩ : syracuseStep 302165 = 3541) (by norm_num)
theorem B302189 : Blo 199806 302189 := bbase (se 3 (by rfl) ⟨56660, by rfl⟩ : syracuseStep 302189 = 113321) (by norm_num)
theorem B203897 : Blo 199806 203897 := bbase (se 2 (by rfl) ⟨76461, by rfl⟩ : syracuseStep 203897 = 152923) (by norm_num)
theorem B302213 : Blo 199806 302213 := bbase (se 4 (by rfl) ⟨28332, by rfl⟩ : syracuseStep 302213 = 56665) (by norm_num)
theorem B924821 : Blo 199806 924821 := bbase (se 6 (by rfl) ⟨21675, by rfl⟩ : syracuseStep 924821 = 43351) (by norm_num)
theorem B302237 : Blo 199806 302237 := bbase (se 3 (by rfl) ⟨56669, by rfl⟩ : syracuseStep 302237 = 113339) (by norm_num)
theorem B302261 : Blo 199806 302261 := bbase (se 5 (by rfl) ⟨14168, by rfl⟩ : syracuseStep 302261 = 28337) (by norm_num)
theorem B302285 : Blo 199806 302285 := bbase (se 3 (by rfl) ⟨56678, by rfl⟩ : syracuseStep 302285 = 113357) (by norm_num)
theorem B302309 : Blo 199806 302309 := bbase (se 4 (by rfl) ⟨28341, by rfl⟩ : syracuseStep 302309 = 56683) (by norm_num)
theorem B302333 : Blo 199806 302333 := bbase (se 3 (by rfl) ⟨56687, by rfl⟩ : syracuseStep 302333 = 113375) (by norm_num)
theorem B302357 : Blo 199806 302357 := bbase (se 6 (by rfl) ⟨7086, by rfl⟩ : syracuseStep 302357 = 14173) (by norm_num)
theorem B924965 : Blo 199806 924965 := bbase (se 4 (by rfl) ⟨86715, by rfl⟩ : syracuseStep 924965 = 173431) (by norm_num)
theorem B302381 : Blo 199806 302381 := bbase (se 3 (by rfl) ⟨56696, by rfl⟩ : syracuseStep 302381 = 113393) (by norm_num)
theorem B302405 : Blo 199806 302405 := bbase (se 4 (by rfl) ⟨28350, by rfl⟩ : syracuseStep 302405 = 56701) (by norm_num)
theorem B302429 : Blo 199806 302429 := bbase (se 3 (by rfl) ⟨56705, by rfl⟩ : syracuseStep 302429 = 113411) (by norm_num)
theorem B302453 : Blo 199806 302453 := bbase (se 5 (by rfl) ⟨14177, by rfl⟩ : syracuseStep 302453 = 28355) (by norm_num)
theorem B302477 : Blo 199806 302477 := bbase (se 3 (by rfl) ⟨56714, by rfl⟩ : syracuseStep 302477 = 113429) (by norm_num)
theorem B302501 : Blo 199806 302501 := bbase (se 4 (by rfl) ⟨28359, by rfl⟩ : syracuseStep 302501 = 56719) (by norm_num)
theorem B204205 : Blo 199806 204205 := bbase (se 3 (by rfl) ⟨38288, by rfl⟩ : syracuseStep 204205 = 76577) (by norm_num)
theorem B302525 : Blo 199806 302525 := bbase (se 3 (by rfl) ⟨56723, by rfl⟩ : syracuseStep 302525 = 113447) (by norm_num)
theorem B302549 : Blo 199806 302549 := bbase (se 7 (by rfl) ⟨3545, by rfl⟩ : syracuseStep 302549 = 7091) (by norm_num)
theorem B302573 : Blo 199806 302573 := bbase (se 3 (by rfl) ⟨56732, by rfl⟩ : syracuseStep 302573 = 113465) (by norm_num)
theorem B302597 : Blo 199806 302597 := bbase (se 4 (by rfl) ⟨28368, by rfl⟩ : syracuseStep 302597 = 56737) (by norm_num)
theorem B302621 : Blo 199806 302621 := bbase (se 3 (by rfl) ⟨56741, by rfl⟩ : syracuseStep 302621 = 113483) (by norm_num)
theorem B302645 : Blo 199806 302645 := bbase (se 5 (by rfl) ⟨14186, by rfl⟩ : syracuseStep 302645 = 28373) (by norm_num)
theorem B302669 : Blo 199806 302669 := bbase (se 3 (by rfl) ⟨56750, by rfl⟩ : syracuseStep 302669 = 113501) (by norm_num)
theorem B1154645 : Blo 199806 1154645 := bbase (se 8 (by rfl) ⟨6765, by rfl⟩ : syracuseStep 1154645 = 13531) (by norm_num)
theorem B302693 : Blo 199806 302693 := bbase (se 4 (by rfl) ⟨28377, by rfl⟩ : syracuseStep 302693 = 56755) (by norm_num)
theorem B302717 : Blo 199806 302717 := bbase (se 3 (by rfl) ⟨56759, by rfl⟩ : syracuseStep 302717 = 113519) (by norm_num)
theorem B302741 : Blo 199806 302741 := bbase (se 6 (by rfl) ⟨7095, by rfl⟩ : syracuseStep 302741 = 14191) (by norm_num)
theorem B302765 : Blo 199806 302765 := bbase (se 3 (by rfl) ⟨56768, by rfl⟩ : syracuseStep 302765 = 113537) (by norm_num)
theorem B302789 : Blo 199806 302789 := bbase (se 4 (by rfl) ⟨28386, by rfl⟩ : syracuseStep 302789 = 56773) (by norm_num)
theorem B302813 : Blo 199806 302813 := bbase (se 3 (by rfl) ⟨56777, by rfl⟩ : syracuseStep 302813 = 113555) (by norm_num)
theorem B302837 : Blo 199806 302837 := bbase (se 5 (by rfl) ⟨14195, by rfl⟩ : syracuseStep 302837 = 28391) (by norm_num)
theorem B302861 : Blo 199806 302861 := bbase (se 3 (by rfl) ⟨56786, by rfl⟩ : syracuseStep 302861 = 113573) (by norm_num)
theorem B1154837 : Blo 199806 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B302885 : Blo 199806 302885 := bbase (se 4 (by rfl) ⟨28395, by rfl⟩ : syracuseStep 302885 = 56791) (by norm_num)
theorem B302909 : Blo 199806 302909 := bbase (se 3 (by rfl) ⟨56795, by rfl⟩ : syracuseStep 302909 = 113591) (by norm_num)
theorem B761669 : Blo 199806 761669 := bbase (se 4 (by rfl) ⟨71406, by rfl⟩ : syracuseStep 761669 = 142813) (by norm_num)
theorem B302933 : Blo 199806 302933 := bbase (se 9 (by rfl) ⟨887, by rfl⟩ : syracuseStep 302933 = 1775) (by norm_num)
theorem B302957 : Blo 199806 302957 := bbase (se 3 (by rfl) ⟨56804, by rfl⟩ : syracuseStep 302957 = 113609) (by norm_num)
theorem B270197 : Blo 199806 270197 := bbase (se 5 (by rfl) ⟨12665, by rfl⟩ : syracuseStep 270197 = 25331) (by norm_num)
theorem B302981 : Blo 199806 302981 := bbase (se 4 (by rfl) ⟨28404, by rfl⟩ : syracuseStep 302981 = 56809) (by norm_num)
theorem B368533 : Blo 199806 368533 := bbase (se 6 (by rfl) ⟨8637, by rfl⟩ : syracuseStep 368533 = 17275) (by norm_num)
theorem B434069 : Blo 199806 434069 := bbase (se 6 (by rfl) ⟨10173, by rfl⟩ : syracuseStep 434069 = 20347) (by norm_num)
theorem B303005 : Blo 199806 303005 := bbase (se 3 (by rfl) ⟨56813, by rfl⟩ : syracuseStep 303005 = 113627) (by norm_num)
theorem B303029 : Blo 199806 303029 := bbase (se 5 (by rfl) ⟨14204, by rfl⟩ : syracuseStep 303029 = 28409) (by norm_num)
theorem B303053 : Blo 199806 303053 := bbase (se 3 (by rfl) ⟨56822, by rfl⟩ : syracuseStep 303053 = 113645) (by norm_num)
theorem B204769 : Blo 199806 204769 := bbase (se 2 (by rfl) ⟨76788, by rfl⟩ : syracuseStep 204769 = 153577) (by norm_num)
theorem B303077 : Blo 199806 303077 := bbase (se 4 (by rfl) ⟨28413, by rfl⟩ : syracuseStep 303077 = 56827) (by norm_num)
theorem B270317 : Blo 199806 270317 := bbase (se 3 (by rfl) ⟨50684, by rfl⟩ : syracuseStep 270317 = 101369) (by norm_num)
theorem B303101 : Blo 199806 303101 := bbase (se 3 (by rfl) ⟨56831, by rfl⟩ : syracuseStep 303101 = 113663) (by norm_num)
theorem B434173 : Blo 199806 434173 := bbase (se 3 (by rfl) ⟨81407, by rfl⟩ : syracuseStep 434173 = 162815) (by norm_num)
theorem B303125 : Blo 199806 303125 := bbase (se 6 (by rfl) ⟨7104, by rfl⟩ : syracuseStep 303125 = 14209) (by norm_num)
theorem B303149 : Blo 199806 303149 := bbase (se 3 (by rfl) ⟨56840, by rfl⟩ : syracuseStep 303149 = 113681) (by norm_num)
theorem B303173 : Blo 199806 303173 := bbase (se 4 (by rfl) ⟨28422, by rfl⟩ : syracuseStep 303173 = 56845) (by norm_num)
theorem B303197 : Blo 199806 303197 := bbase (se 3 (by rfl) ⟨56849, by rfl⟩ : syracuseStep 303197 = 113699) (by norm_num)
theorem B761957 : Blo 199806 761957 := bbase (se 4 (by rfl) ⟨71433, by rfl⟩ : syracuseStep 761957 = 142867) (by norm_num)
theorem B303221 : Blo 199806 303221 := bbase (se 5 (by rfl) ⟨14213, by rfl⟩ : syracuseStep 303221 = 28427) (by norm_num)
theorem B303245 : Blo 199806 303245 := bbase (se 3 (by rfl) ⟨56858, by rfl⟩ : syracuseStep 303245 = 113717) (by norm_num)
theorem B434317 : Blo 199806 434317 := bbase (se 3 (by rfl) ⟨81434, by rfl⟩ : syracuseStep 434317 = 162869) (by norm_num)
theorem B303269 : Blo 199806 303269 := bbase (se 4 (by rfl) ⟨28431, by rfl⟩ : syracuseStep 303269 = 56863) (by norm_num)
theorem B303293 : Blo 199806 303293 := bbase (se 3 (by rfl) ⟨56867, by rfl⟩ : syracuseStep 303293 = 113735) (by norm_num)
theorem B303317 : Blo 199806 303317 := bbase (se 7 (by rfl) ⟨3554, by rfl⟩ : syracuseStep 303317 = 7109) (by norm_num)
theorem B303341 : Blo 199806 303341 := bbase (se 3 (by rfl) ⟨56876, by rfl⟩ : syracuseStep 303341 = 113753) (by norm_num)
theorem B303365 : Blo 199806 303365 := bbase (se 4 (by rfl) ⟨28440, by rfl⟩ : syracuseStep 303365 = 56881) (by norm_num)
theorem B303389 : Blo 199806 303389 := bbase (se 3 (by rfl) ⟨56885, by rfl⟩ : syracuseStep 303389 = 113771) (by norm_num)
theorem B303413 : Blo 199806 303413 := bbase (se 5 (by rfl) ⟨14222, by rfl⟩ : syracuseStep 303413 = 28445) (by norm_num)
theorem B1024325 : Blo 199806 1024325 := bbase (se 4 (by rfl) ⟨96030, by rfl⟩ : syracuseStep 1024325 = 192061) (by norm_num)
theorem B303437 : Blo 199806 303437 := bbase (se 3 (by rfl) ⟨56894, by rfl⟩ : syracuseStep 303437 = 113789) (by norm_num)
theorem B303461 : Blo 199806 303461 := bbase (se 4 (by rfl) ⟨28449, by rfl⟩ : syracuseStep 303461 = 56899) (by norm_num)
theorem B303485 : Blo 199806 303485 := bbase (se 3 (by rfl) ⟨56903, by rfl⟩ : syracuseStep 303485 = 113807) (by norm_num)
theorem B1286549 : Blo 199806 1286549 := bbase (se 6 (by rfl) ⟨30153, by rfl⟩ : syracuseStep 1286549 = 60307) (by norm_num)
theorem B303509 : Blo 199806 303509 := bbase (se 6 (by rfl) ⟨7113, by rfl⟩ : syracuseStep 303509 = 14227) (by norm_num)
theorem B303533 : Blo 199806 303533 := bbase (se 3 (by rfl) ⟨56912, by rfl⟩ : syracuseStep 303533 = 113825) (by norm_num)
theorem B303557 : Blo 199806 303557 := bbase (se 4 (by rfl) ⟨28458, by rfl⟩ : syracuseStep 303557 = 56917) (by norm_num)
theorem B303581 : Blo 199806 303581 := bbase (se 3 (by rfl) ⟨56921, by rfl⟩ : syracuseStep 303581 = 113843) (by norm_num)
theorem B303605 : Blo 199806 303605 := bbase (se 5 (by rfl) ⟨14231, by rfl⟩ : syracuseStep 303605 = 28463) (by norm_num)
theorem B303629 : Blo 199806 303629 := bbase (se 3 (by rfl) ⟨56930, by rfl⟩ : syracuseStep 303629 = 113861) (by norm_num)
theorem B303653 : Blo 199806 303653 := bbase (se 4 (by rfl) ⟨28467, by rfl⟩ : syracuseStep 303653 = 56935) (by norm_num)
theorem B303677 : Blo 199806 303677 := bbase (se 3 (by rfl) ⟨56939, by rfl⟩ : syracuseStep 303677 = 113879) (by norm_num)
theorem B205373 : Blo 199806 205373 := bbase (se 3 (by rfl) ⟨38507, by rfl⟩ : syracuseStep 205373 = 77015) (by norm_num)
theorem B303701 : Blo 199806 303701 := bbase (se 8 (by rfl) ⟨1779, by rfl⟩ : syracuseStep 303701 = 3559) (by norm_num)
theorem B270949 : Blo 199806 270949 := bbase (se 4 (by rfl) ⟨25401, by rfl⟩ : syracuseStep 270949 = 50803) (by norm_num)
theorem B303725 : Blo 199806 303725 := bbase (se 3 (by rfl) ⟨56948, by rfl⟩ : syracuseStep 303725 = 113897) (by norm_num)
theorem B303749 : Blo 199806 303749 := bbase (se 4 (by rfl) ⟨28476, by rfl⟩ : syracuseStep 303749 = 56953) (by norm_num)
theorem B434821 : Blo 199806 434821 := bbase (se 4 (by rfl) ⟨40764, by rfl⟩ : syracuseStep 434821 = 81529) (by norm_num)
theorem B303773 : Blo 199806 303773 := bbase (se 3 (by rfl) ⟨56957, by rfl⟩ : syracuseStep 303773 = 113915) (by norm_num)
theorem B303797 : Blo 199806 303797 := bbase (se 5 (by rfl) ⟨14240, by rfl⟩ : syracuseStep 303797 = 28481) (by norm_num)
theorem B303821 : Blo 199806 303821 := bbase (se 3 (by rfl) ⟨56966, by rfl⟩ : syracuseStep 303821 = 113933) (by norm_num)
theorem B303845 : Blo 199806 303845 := bbase (se 4 (by rfl) ⟨28485, by rfl⟩ : syracuseStep 303845 = 56971) (by norm_num)
theorem B1155829 : Blo 199806 1155829 := bbase (se 5 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 1155829 = 108359) (by norm_num)
theorem B303869 : Blo 199806 303869 := bbase (se 3 (by rfl) ⟨56975, by rfl⟩ : syracuseStep 303869 = 113951) (by norm_num)
theorem B303893 : Blo 199806 303893 := bbase (se 6 (by rfl) ⟨7122, by rfl⟩ : syracuseStep 303893 = 14245) (by norm_num)
theorem B303917 : Blo 199806 303917 := bbase (se 3 (by rfl) ⟨56984, by rfl⟩ : syracuseStep 303917 = 113969) (by norm_num)
theorem B303925 : Blo 199806 303925 := bbase (se 5 (by rfl) ⟨14246, by rfl⟩ : syracuseStep 303925 = 28493) (by norm_num)
theorem B303941 : Blo 199806 303941 := bbase (se 4 (by rfl) ⟨28494, by rfl⟩ : syracuseStep 303941 = 56989) (by norm_num)
theorem B303965 : Blo 199806 303965 := bbase (se 3 (by rfl) ⟨56993, by rfl⟩ : syracuseStep 303965 = 113987) (by norm_num)
theorem B303989 : Blo 199806 303989 := bbase (se 5 (by rfl) ⟨14249, by rfl⟩ : syracuseStep 303989 = 28499) (by norm_num)
theorem B304013 : Blo 199806 304013 := bbase (se 3 (by rfl) ⟨57002, by rfl⟩ : syracuseStep 304013 = 114005) (by norm_num)
theorem B304037 : Blo 199806 304037 := bbase (se 4 (by rfl) ⟨28503, by rfl⟩ : syracuseStep 304037 = 57007) (by norm_num)
theorem B304061 : Blo 199806 304061 := bbase (se 3 (by rfl) ⟨57011, by rfl⟩ : syracuseStep 304061 = 114023) (by norm_num)
theorem B304085 : Blo 199806 304085 := bbase (se 7 (by rfl) ⟨3563, by rfl⟩ : syracuseStep 304085 = 7127) (by norm_num)
theorem B304109 : Blo 199806 304109 := bbase (se 3 (by rfl) ⟨57020, by rfl⟩ : syracuseStep 304109 = 114041) (by norm_num)
theorem B304133 : Blo 199806 304133 := bbase (se 4 (by rfl) ⟨28512, by rfl⟩ : syracuseStep 304133 = 57025) (by norm_num)
theorem B304157 : Blo 199806 304157 := bbase (se 3 (by rfl) ⟨57029, by rfl⟩ : syracuseStep 304157 = 114059) (by norm_num)
theorem B304181 : Blo 199806 304181 := bbase (se 5 (by rfl) ⟨14258, by rfl⟩ : syracuseStep 304181 = 28517) (by norm_num)
theorem B304205 : Blo 199806 304205 := bbase (se 3 (by rfl) ⟨57038, by rfl⟩ : syracuseStep 304205 = 114077) (by norm_num)
theorem B304229 : Blo 199806 304229 := bbase (se 4 (by rfl) ⟨28521, by rfl⟩ : syracuseStep 304229 = 57043) (by norm_num)
theorem B304253 : Blo 199806 304253 := bbase (se 3 (by rfl) ⟨57047, by rfl⟩ : syracuseStep 304253 = 114095) (by norm_num)
theorem B304277 : Blo 199806 304277 := bbase (se 6 (by rfl) ⟨7131, by rfl⟩ : syracuseStep 304277 = 14263) (by norm_num)
theorem B304301 : Blo 199806 304301 := bbase (se 3 (by rfl) ⟨57056, by rfl⟩ : syracuseStep 304301 = 114113) (by norm_num)
theorem B304325 : Blo 199806 304325 := bbase (se 4 (by rfl) ⟨28530, by rfl⟩ : syracuseStep 304325 = 57061) (by norm_num)
theorem B304349 : Blo 199806 304349 := bbase (se 3 (by rfl) ⟨57065, by rfl⟩ : syracuseStep 304349 = 114131) (by norm_num)
theorem B304373 : Blo 199806 304373 := bbase (se 5 (by rfl) ⟨14267, by rfl⟩ : syracuseStep 304373 = 28535) (by norm_num)
theorem B763141 : Blo 199806 763141 := bbase (se 4 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 763141 = 143089) (by norm_num)
theorem B304397 : Blo 199806 304397 := bbase (se 3 (by rfl) ⟨57074, by rfl⟩ : syracuseStep 304397 = 114149) (by norm_num)
theorem B337189 : Blo 199806 337189 := bbase (se 4 (by rfl) ⟨31611, by rfl⟩ : syracuseStep 337189 = 63223) (by norm_num)
theorem B304421 : Blo 199806 304421 := bbase (se 4 (by rfl) ⟨28539, by rfl⟩ : syracuseStep 304421 = 57079) (by norm_num)
theorem B271669 : Blo 199806 271669 := bbase (se 5 (by rfl) ⟨12734, by rfl⟩ : syracuseStep 271669 = 25469) (by norm_num)
theorem B304445 : Blo 199806 304445 := bbase (se 3 (by rfl) ⟨57083, by rfl⟩ : syracuseStep 304445 = 114167) (by norm_num)
theorem B304469 : Blo 199806 304469 := bbase (se 12 (by rfl) ⟨111, by rfl⟩ : syracuseStep 304469 = 223) (by norm_num)
theorem B304493 : Blo 199806 304493 := bbase (se 3 (by rfl) ⟨57092, by rfl⟩ : syracuseStep 304493 = 114185) (by norm_num)
theorem B337277 : Blo 199806 337277 := bbase (se 3 (by rfl) ⟨63239, by rfl⟩ : syracuseStep 337277 = 126479) (by norm_num)
theorem B304517 : Blo 199806 304517 := bbase (se 4 (by rfl) ⟨28548, by rfl⟩ : syracuseStep 304517 = 57097) (by norm_num)
theorem B304541 : Blo 199806 304541 := bbase (se 3 (by rfl) ⟨57101, by rfl⟩ : syracuseStep 304541 = 114203) (by norm_num)
theorem B304565 : Blo 199806 304565 := bbase (se 5 (by rfl) ⟨14276, by rfl⟩ : syracuseStep 304565 = 28553) (by norm_num)
theorem B206281 : Blo 199806 206281 := bbase (se 2 (by rfl) ⟨77355, by rfl⟩ : syracuseStep 206281 = 154711) (by norm_num)
theorem B304589 : Blo 199806 304589 := bbase (se 3 (by rfl) ⟨57110, by rfl⟩ : syracuseStep 304589 = 114221) (by norm_num)
theorem B304613 : Blo 199806 304613 := bbase (se 4 (by rfl) ⟨28557, by rfl⟩ : syracuseStep 304613 = 57115) (by norm_num)
theorem B337405 : Blo 199806 337405 := bbase (se 3 (by rfl) ⟨63263, by rfl⟩ : syracuseStep 337405 = 126527) (by norm_num)
theorem B304637 : Blo 199806 304637 := bbase (se 3 (by rfl) ⟨57119, by rfl⟩ : syracuseStep 304637 = 114239) (by norm_num)
theorem B304661 : Blo 199806 304661 := bbase (se 6 (by rfl) ⟨7140, by rfl⟩ : syracuseStep 304661 = 14281) (by norm_num)
theorem B304685 : Blo 199806 304685 := bbase (se 3 (by rfl) ⟨57128, by rfl⟩ : syracuseStep 304685 = 114257) (by norm_num)
theorem B763445 : Blo 199806 763445 := bbase (se 5 (by rfl) ⟨35786, by rfl⟩ : syracuseStep 763445 = 71573) (by norm_num)
theorem B304709 : Blo 199806 304709 := bbase (se 4 (by rfl) ⟨28566, by rfl⟩ : syracuseStep 304709 = 57133) (by norm_num)
theorem B337493 : Blo 199806 337493 := bbase (se 8 (by rfl) ⟨1977, by rfl⟩ : syracuseStep 337493 = 3955) (by norm_num)
theorem B1025621 : Blo 199806 1025621 := bbase (se 8 (by rfl) ⟨6009, by rfl⟩ : syracuseStep 1025621 = 12019) (by norm_num)
theorem B304733 : Blo 199806 304733 := bbase (se 3 (by rfl) ⟨57137, by rfl⟩ : syracuseStep 304733 = 114275) (by norm_num)
theorem B304757 : Blo 199806 304757 := bbase (se 5 (by rfl) ⟨14285, by rfl⟩ : syracuseStep 304757 = 28571) (by norm_num)
theorem B304781 : Blo 199806 304781 := bbase (se 3 (by rfl) ⟨57146, by rfl⟩ : syracuseStep 304781 = 114293) (by norm_num)
theorem B304805 : Blo 199806 304805 := bbase (se 4 (by rfl) ⟨28575, by rfl⟩ : syracuseStep 304805 = 57151) (by norm_num)
theorem B304829 : Blo 199806 304829 := bbase (se 3 (by rfl) ⟨57155, by rfl⟩ : syracuseStep 304829 = 114311) (by norm_num)
theorem B337621 : Blo 199806 337621 := bbase (se 7 (by rfl) ⟨3956, by rfl⟩ : syracuseStep 337621 = 7913) (by norm_num)
theorem B304853 : Blo 199806 304853 := bbase (se 7 (by rfl) ⟨3572, by rfl⟩ : syracuseStep 304853 = 7145) (by norm_num)
theorem B272101 : Blo 199806 272101 := bbase (se 4 (by rfl) ⟨25509, by rfl⟩ : syracuseStep 272101 = 51019) (by norm_num)
theorem B304877 : Blo 199806 304877 := bbase (se 3 (by rfl) ⟨57164, by rfl⟩ : syracuseStep 304877 = 114329) (by norm_num)
theorem B304901 : Blo 199806 304901 := bbase (se 4 (by rfl) ⟨28584, by rfl⟩ : syracuseStep 304901 = 57169) (by norm_num)
theorem B304925 : Blo 199806 304925 := bbase (se 3 (by rfl) ⟨57173, by rfl⟩ : syracuseStep 304925 = 114347) (by norm_num)
theorem B272165 : Blo 199806 272165 := bbase (se 4 (by rfl) ⟨25515, by rfl⟩ : syracuseStep 272165 = 51031) (by norm_num)
theorem B337709 : Blo 199806 337709 := bbase (se 3 (by rfl) ⟨63320, by rfl⟩ : syracuseStep 337709 = 126641) (by norm_num)
theorem B304949 : Blo 199806 304949 := bbase (se 5 (by rfl) ⟨14294, by rfl⟩ : syracuseStep 304949 = 28589) (by norm_num)
theorem B304973 : Blo 199806 304973 := bbase (se 3 (by rfl) ⟨57182, by rfl⟩ : syracuseStep 304973 = 114365) (by norm_num)
theorem B304997 : Blo 199806 304997 := bbase (se 4 (by rfl) ⟨28593, by rfl⟩ : syracuseStep 304997 = 57187) (by norm_num)
theorem B305021 : Blo 199806 305021 := bbase (se 3 (by rfl) ⟨57191, by rfl⟩ : syracuseStep 305021 = 114383) (by norm_num)
theorem B305045 : Blo 199806 305045 := bbase (se 6 (by rfl) ⟨7149, by rfl⟩ : syracuseStep 305045 = 14299) (by norm_num)
theorem B337837 : Blo 199806 337837 := bbase (se 3 (by rfl) ⟨63344, by rfl⟩ : syracuseStep 337837 = 126689) (by norm_num)
theorem B305069 : Blo 199806 305069 := bbase (se 3 (by rfl) ⟨57200, by rfl⟩ : syracuseStep 305069 = 114401) (by norm_num)
theorem B305093 : Blo 199806 305093 := bbase (se 4 (by rfl) ⟨28602, by rfl⟩ : syracuseStep 305093 = 57205) (by norm_num)
theorem B272333 : Blo 199806 272333 := bbase (se 3 (by rfl) ⟨51062, by rfl⟩ : syracuseStep 272333 = 102125) (by norm_num)
theorem B305117 : Blo 199806 305117 := bbase (se 3 (by rfl) ⟨57209, by rfl⟩ : syracuseStep 305117 = 114419) (by norm_num)
theorem B305141 : Blo 199806 305141 := bbase (se 5 (by rfl) ⟨14303, by rfl⟩ : syracuseStep 305141 = 28607) (by norm_num)
theorem B337925 : Blo 199806 337925 := bbase (se 4 (by rfl) ⟨31680, by rfl⟩ : syracuseStep 337925 = 63361) (by norm_num)
theorem B305165 : Blo 199806 305165 := bbase (se 3 (by rfl) ⟨57218, by rfl⟩ : syracuseStep 305165 = 114437) (by norm_num)
theorem B305189 : Blo 199806 305189 := bbase (se 4 (by rfl) ⟨28611, by rfl⟩ : syracuseStep 305189 = 57223) (by norm_num)
theorem B305213 : Blo 199806 305213 := bbase (se 3 (by rfl) ⟨57227, by rfl⟩ : syracuseStep 305213 = 114455) (by norm_num)
theorem B305237 : Blo 199806 305237 := bbase (se 8 (by rfl) ⟨1788, by rfl⟩ : syracuseStep 305237 = 3577) (by norm_num)
theorem B305261 : Blo 199806 305261 := bbase (se 3 (by rfl) ⟨57236, by rfl⟩ : syracuseStep 305261 = 114473) (by norm_num)
theorem B338053 : Blo 199806 338053 := bbase (se 4 (by rfl) ⟨31692, by rfl⟩ : syracuseStep 338053 = 63385) (by norm_num)
theorem B305285 : Blo 199806 305285 := bbase (se 4 (by rfl) ⟨28620, by rfl⟩ : syracuseStep 305285 = 57241) (by norm_num)
theorem B305309 : Blo 199806 305309 := bbase (se 3 (by rfl) ⟨57245, by rfl⟩ : syracuseStep 305309 = 114491) (by norm_num)
theorem B305333 : Blo 199806 305333 := bbase (se 5 (by rfl) ⟨14312, by rfl⟩ : syracuseStep 305333 = 28625) (by norm_num)
theorem B305357 : Blo 199806 305357 := bbase (se 3 (by rfl) ⟨57254, by rfl⟩ : syracuseStep 305357 = 114509) (by norm_num)
theorem B338141 : Blo 199806 338141 := bbase (se 3 (by rfl) ⟨63401, by rfl⟩ : syracuseStep 338141 = 126803) (by norm_num)
theorem B305381 : Blo 199806 305381 := bbase (se 4 (by rfl) ⟨28629, by rfl⟩ : syracuseStep 305381 = 57259) (by norm_num)
theorem B305405 : Blo 199806 305405 := bbase (se 3 (by rfl) ⟨57263, by rfl⟩ : syracuseStep 305405 = 114527) (by norm_num)
theorem B305429 : Blo 199806 305429 := bbase (se 6 (by rfl) ⟨7158, by rfl⟩ : syracuseStep 305429 = 14317) (by norm_num)
theorem B305453 : Blo 199806 305453 := bbase (se 3 (by rfl) ⟨57272, by rfl⟩ : syracuseStep 305453 = 114545) (by norm_num)
theorem B305477 : Blo 199806 305477 := bbase (se 4 (by rfl) ⟨28638, by rfl⟩ : syracuseStep 305477 = 57277) (by norm_num)
theorem B338269 : Blo 199806 338269 := bbase (se 3 (by rfl) ⟨63425, by rfl⟩ : syracuseStep 338269 = 126851) (by norm_num)
theorem B305501 : Blo 199806 305501 := bbase (se 3 (by rfl) ⟨57281, by rfl⟩ : syracuseStep 305501 = 114563) (by norm_num)
theorem B305525 : Blo 199806 305525 := bbase (se 5 (by rfl) ⟨14321, by rfl⟩ : syracuseStep 305525 = 28643) (by norm_num)
theorem B305549 : Blo 199806 305549 := bbase (se 3 (by rfl) ⟨57290, by rfl⟩ : syracuseStep 305549 = 114581) (by norm_num)
theorem B305573 : Blo 199806 305573 := bbase (se 4 (by rfl) ⟨28647, by rfl⟩ : syracuseStep 305573 = 57295) (by norm_num)
theorem B338357 : Blo 199806 338357 := bbase (se 5 (by rfl) ⟨15860, by rfl⟩ : syracuseStep 338357 = 31721) (by norm_num)
theorem B305597 : Blo 199806 305597 := bbase (se 3 (by rfl) ⟨57299, by rfl⟩ : syracuseStep 305597 = 114599) (by norm_num)
theorem B305621 : Blo 199806 305621 := bbase (se 7 (by rfl) ⟨3581, by rfl⟩ : syracuseStep 305621 = 7163) (by norm_num)
theorem B240089 : Blo 199806 240089 := bbase (se 2 (by rfl) ⟨90033, by rfl⟩ : syracuseStep 240089 = 180067) (by norm_num)
theorem B305645 : Blo 199806 305645 := bbase (se 3 (by rfl) ⟨57308, by rfl⟩ : syracuseStep 305645 = 114617) (by norm_num)
theorem B305669 : Blo 199806 305669 := bbase (se 4 (by rfl) ⟨28656, by rfl⟩ : syracuseStep 305669 = 57313) (by norm_num)
theorem B305693 : Blo 199806 305693 := bbase (se 3 (by rfl) ⟨57317, by rfl⟩ : syracuseStep 305693 = 114635) (by norm_num)
theorem B862757 : Blo 199806 862757 := bbase (se 4 (by rfl) ⟨80883, by rfl⟩ : syracuseStep 862757 = 161767) (by norm_num)
theorem B338485 : Blo 199806 338485 := bbase (se 5 (by rfl) ⟨15866, by rfl⟩ : syracuseStep 338485 = 31733) (by norm_num)
theorem B305797 : Blo 199806 305797 := bbase (se 4 (by rfl) ⟨28668, by rfl⟩ : syracuseStep 305797 = 57337) (by norm_num)
theorem B338573 : Blo 199806 338573 := bbase (se 3 (by rfl) ⟨63482, by rfl⟩ : syracuseStep 338573 = 126965) (by norm_num)
theorem B1157813 : Blo 199806 1157813 := bbase (se 5 (by rfl) ⟨54272, by rfl⟩ : syracuseStep 1157813 = 108545) (by norm_num)
theorem B338701 : Blo 199806 338701 := bbase (se 3 (by rfl) ⟨63506, by rfl⟩ : syracuseStep 338701 = 127013) (by norm_num)
theorem B240445 : Blo 199806 240445 := bbase (se 3 (by rfl) ⟨45083, by rfl⟩ : syracuseStep 240445 = 90167) (by norm_num)
theorem B863045 : Blo 199806 863045 := bbase (se 4 (by rfl) ⟨80910, by rfl⟩ : syracuseStep 863045 = 161821) (by norm_num)
theorem B338789 : Blo 199806 338789 := bbase (se 4 (by rfl) ⟨31761, by rfl⟩ : syracuseStep 338789 = 63523) (by norm_num)
theorem B1026917 : Blo 199806 1026917 := bbase (se 4 (by rfl) ⟨96273, by rfl⟩ : syracuseStep 1026917 = 192547) (by norm_num)
theorem B338917 : Blo 199806 338917 := bbase (se 4 (by rfl) ⟨31773, by rfl⟩ : syracuseStep 338917 = 63547) (by norm_num)
theorem B240637 : Blo 199806 240637 := bbase (se 3 (by rfl) ⟨45119, by rfl⟩ : syracuseStep 240637 = 90239) (by norm_num)
theorem B339005 : Blo 199806 339005 := bbase (se 3 (by rfl) ⟨63563, by rfl⟩ : syracuseStep 339005 = 127127) (by norm_num)
theorem B240781 : Blo 199806 240781 := bbase (se 3 (by rfl) ⟨45146, by rfl⟩ : syracuseStep 240781 = 90293) (by norm_num)
theorem B208013 : Blo 199806 208013 := bbase (se 3 (by rfl) ⟨39002, by rfl⟩ : syracuseStep 208013 = 78005) (by norm_num)
theorem B339133 : Blo 199806 339133 := bbase (se 3 (by rfl) ⟨63587, by rfl⟩ : syracuseStep 339133 = 127175) (by norm_num)
theorem B339221 : Blo 199806 339221 := bbase (se 6 (by rfl) ⟨7950, by rfl⟩ : syracuseStep 339221 = 15901) (by norm_num)
theorem B339349 : Blo 199806 339349 := bbase (se 6 (by rfl) ⟨7953, by rfl⟩ : syracuseStep 339349 = 15907) (by norm_num)
theorem B339437 : Blo 199806 339437 := bbase (se 3 (by rfl) ⟨63644, by rfl⟩ : syracuseStep 339437 = 127289) (by norm_num)
theorem B1715701 : Blo 199806 1715701 := bbase (se 5 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 1715701 = 160847) (by norm_num)
theorem B1453621 : Blo 199806 1453621 := bbase (se 5 (by rfl) ⟨68138, by rfl⟩ : syracuseStep 1453621 = 136277) (by norm_num)
theorem B863797 : Blo 199806 863797 := bbase (se 5 (by rfl) ⟨40490, by rfl⟩ : syracuseStep 863797 = 80981) (by norm_num)
theorem B339565 : Blo 199806 339565 := bbase (se 3 (by rfl) ⟨63668, by rfl⟩ : syracuseStep 339565 = 127337) (by norm_num)
theorem B765557 : Blo 199806 765557 := bbase (se 5 (by rfl) ⟨35885, by rfl⟩ : syracuseStep 765557 = 71771) (by norm_num)
theorem B339653 : Blo 199806 339653 := bbase (se 4 (by rfl) ⟨31842, by rfl⟩ : syracuseStep 339653 = 63685) (by norm_num)
theorem B306965 : Blo 199806 306965 := bbase (se 6 (by rfl) ⟨7194, by rfl⟩ : syracuseStep 306965 = 14389) (by norm_num)
theorem B438053 : Blo 199806 438053 := bbase (se 4 (by rfl) ⟨41067, by rfl⟩ : syracuseStep 438053 = 82135) (by norm_num)
theorem B339781 : Blo 199806 339781 := bbase (se 4 (by rfl) ⟨31854, by rfl⟩ : syracuseStep 339781 = 63709) (by norm_num)
theorem B1027957 : Blo 199806 1027957 := bbase (se 5 (by rfl) ⟨48185, by rfl⟩ : syracuseStep 1027957 = 96371) (by norm_num)
theorem B765845 : Blo 199806 765845 := bbase (se 6 (by rfl) ⟨17949, by rfl⟩ : syracuseStep 765845 = 35899) (by norm_num)
theorem B339869 : Blo 199806 339869 := bbase (se 3 (by rfl) ⟨63725, by rfl⟩ : syracuseStep 339869 = 127451) (by norm_num)
theorem B274349 : Blo 199806 274349 := bbase (se 3 (by rfl) ⟨51440, by rfl⟩ : syracuseStep 274349 = 102881) (by norm_num)
theorem B733141 : Blo 199806 733141 := bbase (se 7 (by rfl) ⟨8591, by rfl⟩ : syracuseStep 733141 = 17183) (by norm_num)
theorem B339997 : Blo 199806 339997 := bbase (se 3 (by rfl) ⟨63749, by rfl⟩ : syracuseStep 339997 = 127499) (by norm_num)
theorem B340085 : Blo 199806 340085 := bbase (se 5 (by rfl) ⟨15941, by rfl⟩ : syracuseStep 340085 = 31883) (by norm_num)
theorem B1028213 : Blo 199806 1028213 := bbase (se 5 (by rfl) ⟨48197, by rfl⟩ : syracuseStep 1028213 = 96395) (by norm_num)
theorem B340213 : Blo 199806 340213 := bbase (se 5 (by rfl) ⟨15947, by rfl⟩ : syracuseStep 340213 = 31895) (by norm_num)
theorem B864533 : Blo 199806 864533 := bbase (se 6 (by rfl) ⟨20262, by rfl⟩ : syracuseStep 864533 = 40525) (by norm_num)
theorem B340301 : Blo 199806 340301 := bbase (se 3 (by rfl) ⟨63806, by rfl⟩ : syracuseStep 340301 = 127613) (by norm_num)
theorem B340429 : Blo 199806 340429 := bbase (se 3 (by rfl) ⟨63830, by rfl⟩ : syracuseStep 340429 = 127661) (by norm_num)
theorem B340517 : Blo 199806 340517 := bbase (se 4 (by rfl) ⟨31923, by rfl⟩ : syracuseStep 340517 = 63847) (by norm_num)
theorem B242309 : Blo 199806 242309 := bbase (se 4 (by rfl) ⟨22716, by rfl⟩ : syracuseStep 242309 = 45433) (by norm_num)
theorem B340645 : Blo 199806 340645 := bbase (se 4 (by rfl) ⟨31935, by rfl⟩ : syracuseStep 340645 = 63871) (by norm_num)
theorem B406237 : Blo 199806 406237 := bbase (se 3 (by rfl) ⟨76169, by rfl⟩ : syracuseStep 406237 = 152339) (by norm_num)
theorem B340733 : Blo 199806 340733 := bbase (se 3 (by rfl) ⟨63887, by rfl⟩ : syracuseStep 340733 = 127775) (by norm_num)
theorem B1160021 : Blo 199806 1160021 := bbase (se 9 (by rfl) ⟨3398, by rfl⟩ : syracuseStep 1160021 = 6797) (by norm_num)
theorem B340861 : Blo 199806 340861 := bbase (se 3 (by rfl) ⟨63911, by rfl⟩ : syracuseStep 340861 = 127823) (by norm_num)
theorem B242617 : Blo 199806 242617 := bbase (se 2 (by rfl) ⟨90981, by rfl⟩ : syracuseStep 242617 = 181963) (by norm_num)
theorem B340949 : Blo 199806 340949 := bbase (se 7 (by rfl) ⟨3995, by rfl⟩ : syracuseStep 340949 = 7991) (by norm_num)
theorem B570341 : Blo 199806 570341 := bbase (se 4 (by rfl) ⟨53469, by rfl⟩ : syracuseStep 570341 = 106939) (by norm_num)
theorem B242713 : Blo 199806 242713 := bbase (se 2 (by rfl) ⟨91017, by rfl⟩ : syracuseStep 242713 = 182035) (by norm_num)
theorem B1520693 : Blo 199806 1520693 := bbase (se 5 (by rfl) ⟨71282, by rfl⟩ : syracuseStep 1520693 = 142565) (by norm_num)
theorem B767029 : Blo 199806 767029 := bbase (se 5 (by rfl) ⟨35954, by rfl⟩ : syracuseStep 767029 = 71909) (by norm_num)
theorem B341077 : Blo 199806 341077 := bbase (se 8 (by rfl) ⟨1998, by rfl⟩ : syracuseStep 341077 = 3997) (by norm_num)
theorem B734309 : Blo 199806 734309 := bbase (se 4 (by rfl) ⟨68841, by rfl⟩ : syracuseStep 734309 = 137683) (by norm_num)
theorem B2897045 : Blo 199806 2897045 := bbase (se 6 (by rfl) ⟨67899, by rfl⟩ : syracuseStep 2897045 = 135799) (by norm_num)
theorem B341165 : Blo 199806 341165 := bbase (se 3 (by rfl) ⟨63968, by rfl⟩ : syracuseStep 341165 = 127937) (by norm_num)
theorem B341293 : Blo 199806 341293 := bbase (se 3 (by rfl) ⟨63992, by rfl⟩ : syracuseStep 341293 = 127985) (by norm_num)
theorem B243001 : Blo 199806 243001 := bbase (se 2 (by rfl) ⟨91125, by rfl⟩ : syracuseStep 243001 = 182251) (by norm_num)
theorem B767333 : Blo 199806 767333 := bbase (se 4 (by rfl) ⟨71937, by rfl⟩ : syracuseStep 767333 = 143875) (by norm_num)
theorem B341381 : Blo 199806 341381 := bbase (se 4 (by rfl) ⟨32004, by rfl⟩ : syracuseStep 341381 = 64009) (by norm_num)
theorem B1029509 : Blo 199806 1029509 := bbase (se 4 (by rfl) ⟨96516, by rfl⟩ : syracuseStep 1029509 = 193033) (by norm_num)
theorem B210349 : Blo 199806 210349 := bbase (se 3 (by rfl) ⟨39440, by rfl⟩ : syracuseStep 210349 = 78881) (by norm_num)
theorem B1717685 : Blo 199806 1717685 := bbase (se 5 (by rfl) ⟨80516, by rfl⟩ : syracuseStep 1717685 = 161033) (by norm_num)
theorem B243193 : Blo 199806 243193 := bbase (se 2 (by rfl) ⟨91197, by rfl⟩ : syracuseStep 243193 = 182395) (by norm_num)
theorem B341509 : Blo 199806 341509 := bbase (se 4 (by rfl) ⟨32016, by rfl⟩ : syracuseStep 341509 = 64033) (by norm_num)
theorem B8336981 : Blo 199806 8336981 := bbase (se 8 (by rfl) ⟨48849, by rfl⟩ : syracuseStep 8336981 = 97699) (by norm_num)
theorem B341597 : Blo 199806 341597 := bbase (se 3 (by rfl) ⟨64049, by rfl⟩ : syracuseStep 341597 = 128099) (by norm_num)
theorem B308861 : Blo 199806 308861 := bbase (se 3 (by rfl) ⟨57911, by rfl⟩ : syracuseStep 308861 = 115823) (by norm_num)
theorem B571013 : Blo 199806 571013 := bbase (se 4 (by rfl) ⟨53532, by rfl⟩ : syracuseStep 571013 = 107065) (by norm_num)
theorem B341725 : Blo 199806 341725 := bbase (se 3 (by rfl) ⟨64073, by rfl⟩ : syracuseStep 341725 = 128147) (by norm_num)
theorem B341813 : Blo 199806 341813 := bbase (se 5 (by rfl) ⟨16022, by rfl⟩ : syracuseStep 341813 = 32045) (by norm_num)
theorem B407405 : Blo 199806 407405 := bbase (se 3 (by rfl) ⟨76388, by rfl⟩ : syracuseStep 407405 = 152777) (by norm_num)
theorem B341941 : Blo 199806 341941 := bbase (se 5 (by rfl) ⟨16028, by rfl⟩ : syracuseStep 341941 = 32057) (by norm_num)
theorem B342029 : Blo 199806 342029 := bbase (se 3 (by rfl) ⟨64130, by rfl⟩ : syracuseStep 342029 = 128261) (by norm_num)
theorem B505885 : Blo 199806 505885 := bbase (se 3 (by rfl) ⟨94853, by rfl⟩ : syracuseStep 505885 = 189707) (by norm_num)
theorem B571445 : Blo 199806 571445 := bbase (se 5 (by rfl) ⟨26786, by rfl⟩ : syracuseStep 571445 = 53573) (by norm_num)
theorem B309349 : Blo 199806 309349 := bbase (se 4 (by rfl) ⟨29001, by rfl⟩ : syracuseStep 309349 = 58003) (by norm_num)
theorem B505997 : Blo 199806 505997 := bbase (se 3 (by rfl) ⟨94874, by rfl⟩ : syracuseStep 505997 = 189749) (by norm_num)
theorem B342157 : Blo 199806 342157 := bbase (se 3 (by rfl) ⟨64154, by rfl⟩ : syracuseStep 342157 = 128309) (by norm_num)
theorem B342245 : Blo 199806 342245 := bbase (se 4 (by rfl) ⟨32085, by rfl⟩ : syracuseStep 342245 = 64171) (by norm_num)
theorem B506189 : Blo 199806 506189 := bbase (se 3 (by rfl) ⟨94910, by rfl⟩ : syracuseStep 506189 = 189821) (by norm_num)
theorem B342373 : Blo 199806 342373 := bbase (se 4 (by rfl) ⟨32097, by rfl⟩ : syracuseStep 342373 = 64195) (by norm_num)
theorem B244073 : Blo 199806 244073 := bbase (se 2 (by rfl) ⟨91527, by rfl⟩ : syracuseStep 244073 = 183055) (by norm_num)
theorem B342461 : Blo 199806 342461 := bbase (se 3 (by rfl) ⟨64211, by rfl⟩ : syracuseStep 342461 = 128423) (by norm_num)
theorem B1620533 : Blo 199806 1620533 := bbase (se 5 (by rfl) ⟨75962, by rfl⟩ : syracuseStep 1620533 = 151925) (by norm_num)
theorem B342589 : Blo 199806 342589 := bbase (se 3 (by rfl) ⟨64235, by rfl⟩ : syracuseStep 342589 = 128471) (by norm_num)
theorem B342677 : Blo 199806 342677 := bbase (se 6 (by rfl) ⟨8031, by rfl⟩ : syracuseStep 342677 = 16063) (by norm_num)
theorem B1030805 : Blo 199806 1030805 := bbase (se 6 (by rfl) ⟨24159, by rfl⟩ : syracuseStep 1030805 = 48319) (by norm_num)
theorem B506533 : Blo 199806 506533 := bbase (se 4 (by rfl) ⟨47487, by rfl⟩ : syracuseStep 506533 = 94975) (by norm_num)
theorem B506645 : Blo 199806 506645 := bbase (se 6 (by rfl) ⟨11874, by rfl⟩ : syracuseStep 506645 = 23749) (by norm_num)
theorem B342805 : Blo 199806 342805 := bbase (se 6 (by rfl) ⟨8034, by rfl⟩ : syracuseStep 342805 = 16069) (by norm_num)
theorem B572197 : Blo 199806 572197 := bbase (se 4 (by rfl) ⟨53643, by rfl⟩ : syracuseStep 572197 = 107287) (by norm_num)
theorem B244577 : Blo 199806 244577 := bbase (se 2 (by rfl) ⟨91716, by rfl⟩ : syracuseStep 244577 = 183433) (by norm_num)
theorem B342893 : Blo 199806 342893 := bbase (se 3 (by rfl) ⟨64292, by rfl⟩ : syracuseStep 342893 = 128585) (by norm_num)
theorem B244625 : Blo 199806 244625 := bbase (se 2 (by rfl) ⟨91734, by rfl⟩ : syracuseStep 244625 = 183469) (by norm_num)
theorem B277453 : Blo 199806 277453 := bbase (se 3 (by rfl) ⟨52022, by rfl⟩ : syracuseStep 277453 = 104045) (by norm_num)
theorem B506837 : Blo 199806 506837 := bbase (se 7 (by rfl) ⟨5939, by rfl⟩ : syracuseStep 506837 = 11879) (by norm_num)
theorem B343021 : Blo 199806 343021 := bbase (se 3 (by rfl) ⟨64316, by rfl⟩ : syracuseStep 343021 = 128633) (by norm_num)
theorem B965621 : Blo 199806 965621 := bbase (se 5 (by rfl) ⟨45263, by rfl⟩ : syracuseStep 965621 = 90527) (by norm_num)
theorem B343109 : Blo 199806 343109 := bbase (se 4 (by rfl) ⟨32166, by rfl⟩ : syracuseStep 343109 = 64333) (by norm_num)
theorem B343237 : Blo 199806 343237 := bbase (se 4 (by rfl) ⟨32178, by rfl⟩ : syracuseStep 343237 = 64357) (by norm_num)
theorem B343325 : Blo 199806 343325 := bbase (se 3 (by rfl) ⟨64373, by rfl⟩ : syracuseStep 343325 = 128747) (by norm_num)
theorem B507181 : Blo 199806 507181 := bbase (se 3 (by rfl) ⟨95096, by rfl⟩ : syracuseStep 507181 = 190193) (by norm_num)
theorem B507293 : Blo 199806 507293 := bbase (se 3 (by rfl) ⟨95117, by rfl⟩ : syracuseStep 507293 = 190235) (by norm_num)
theorem B343453 : Blo 199806 343453 := bbase (se 3 (by rfl) ⟨64397, by rfl⟩ : syracuseStep 343453 = 128795) (by norm_num)
theorem B769445 : Blo 199806 769445 := bbase (se 4 (by rfl) ⟨72135, by rfl⟩ : syracuseStep 769445 = 144271) (by norm_num)
theorem B867829 : Blo 199806 867829 := bbase (se 5 (by rfl) ⟨40679, by rfl⟩ : syracuseStep 867829 = 81359) (by norm_num)
theorem B343541 : Blo 199806 343541 := bbase (se 5 (by rfl) ⟨16103, by rfl⟩ : syracuseStep 343541 = 32207) (by norm_num)
theorem B507485 : Blo 199806 507485 := bbase (se 3 (by rfl) ⟨95153, by rfl⟩ : syracuseStep 507485 = 190307) (by norm_num)
theorem B343669 : Blo 199806 343669 := bbase (se 5 (by rfl) ⟨16109, by rfl⟩ : syracuseStep 343669 = 32219) (by norm_num)
theorem B769733 : Blo 199806 769733 := bbase (se 4 (by rfl) ⟨72162, by rfl⟩ : syracuseStep 769733 = 144325) (by norm_num)
theorem B343757 : Blo 199806 343757 := bbase (se 3 (by rfl) ⟨64454, by rfl⟩ : syracuseStep 343757 = 128909) (by norm_num)
theorem B540437 : Blo 199806 540437 := bbase (se 6 (by rfl) ⟨12666, by rfl⟩ : syracuseStep 540437 = 25333) (by norm_num)
theorem B343885 : Blo 199806 343885 := bbase (se 3 (by rfl) ⟨64478, by rfl⟩ : syracuseStep 343885 = 128957) (by norm_num)
theorem B376741 : Blo 199806 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B507829 : Blo 199806 507829 := bbase (se 5 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 507829 = 47609) (by norm_num)
theorem B507941 : Blo 199806 507941 := bbase (se 4 (by rfl) ⟨47619, by rfl⟩ : syracuseStep 507941 = 95239) (by norm_num)
theorem B508133 : Blo 199806 508133 := bbase (se 4 (by rfl) ⟨47637, by rfl⟩ : syracuseStep 508133 = 95275) (by norm_num)
theorem B344405 : Blo 199806 344405 := bbase (se 10 (by rfl) ⟨504, by rfl⟩ : syracuseStep 344405 = 1009) (by norm_num)
theorem B508477 : Blo 199806 508477 := bbase (se 3 (by rfl) ⟨95339, by rfl⟩ : syracuseStep 508477 = 190679) (by norm_num)
theorem B213673 : Blo 199806 213673 := bbase (se 2 (by rfl) ⟨80127, by rfl⟩ : syracuseStep 213673 = 160255) (by norm_num)
theorem B508589 : Blo 199806 508589 := bbase (se 3 (by rfl) ⟨95360, by rfl⟩ : syracuseStep 508589 = 190721) (by norm_num)
theorem B770917 : Blo 199806 770917 := bbase (se 4 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 770917 = 144547) (by norm_num)
theorem B508781 : Blo 199806 508781 := bbase (se 3 (by rfl) ⟨95396, by rfl⟩ : syracuseStep 508781 = 190793) (by norm_num)
theorem B345061 : Blo 199806 345061 := bbase (se 4 (by rfl) ⟨32349, by rfl⟩ : syracuseStep 345061 = 64699) (by norm_num)
theorem B214049 : Blo 199806 214049 := bbase (se 2 (by rfl) ⟨80268, by rfl⟩ : syracuseStep 214049 = 160537) (by norm_num)
theorem B214121 : Blo 199806 214121 := bbase (se 2 (by rfl) ⟨80295, by rfl⟩ : syracuseStep 214121 = 160591) (by norm_num)
theorem B771221 : Blo 199806 771221 := bbase (se 6 (by rfl) ⟨18075, by rfl⟩ : syracuseStep 771221 = 36151) (by norm_num)
theorem B509125 : Blo 199806 509125 := bbase (se 4 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 509125 = 95461) (by norm_num)
theorem B2606357 : Blo 199806 2606357 := bbase (se 6 (by rfl) ⟨61086, by rfl⟩ : syracuseStep 2606357 = 122173) (by norm_num)
theorem B214309 : Blo 199806 214309 := bbase (se 4 (by rfl) ⟨20091, by rfl⟩ : syracuseStep 214309 = 40183) (by norm_num)
theorem B509237 : Blo 199806 509237 := bbase (se 5 (by rfl) ⟨23870, by rfl⟩ : syracuseStep 509237 = 47741) (by norm_num)
theorem B247097 : Blo 199806 247097 := bbase (se 2 (by rfl) ⟨92661, by rfl⟩ : syracuseStep 247097 = 185323) (by norm_num)
theorem B771461 : Blo 199806 771461 := bbase (se 4 (by rfl) ⟨72324, by rfl⟩ : syracuseStep 771461 = 144649) (by norm_num)
theorem B247249 : Blo 199806 247249 := bbase (se 2 (by rfl) ⟨92718, by rfl⟩ : syracuseStep 247249 = 185437) (by norm_num)
theorem B214493 : Blo 199806 214493 := bbase (se 3 (by rfl) ⟨40217, by rfl⟩ : syracuseStep 214493 = 80435) (by norm_num)
theorem B509429 : Blo 199806 509429 := bbase (se 5 (by rfl) ⟨23879, by rfl⟩ : syracuseStep 509429 = 47759) (by norm_num)
theorem B575045 : Blo 199806 575045 := bbase (se 4 (by rfl) ⟨53910, by rfl⟩ : syracuseStep 575045 = 107821) (by norm_num)
theorem B345677 : Blo 199806 345677 := bbase (se 3 (by rfl) ⟨64814, by rfl⟩ : syracuseStep 345677 = 129629) (by norm_num)
theorem B345773 : Blo 199806 345773 := bbase (se 3 (by rfl) ⟨64832, by rfl⟩ : syracuseStep 345773 = 129665) (by norm_num)
theorem B509773 : Blo 199806 509773 := bbase (se 3 (by rfl) ⟨95582, by rfl⟩ : syracuseStep 509773 = 191165) (by norm_num)
theorem B411493 : Blo 199806 411493 := bbase (se 4 (by rfl) ⟨38577, by rfl⟩ : syracuseStep 411493 = 77155) (by norm_num)
theorem B542645 : Blo 199806 542645 := bbase (se 5 (by rfl) ⟨25436, by rfl⟩ : syracuseStep 542645 = 50873) (by norm_num)
theorem B509885 : Blo 199806 509885 := bbase (se 3 (by rfl) ⟨95603, by rfl⟩ : syracuseStep 509885 = 191207) (by norm_num)
theorem B870389 : Blo 199806 870389 := bbase (se 5 (by rfl) ⟨40799, by rfl⟩ : syracuseStep 870389 = 81599) (by norm_num)
theorem B968773 : Blo 199806 968773 := bbase (se 4 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 968773 = 181645) (by norm_num)
theorem B510077 : Blo 199806 510077 := bbase (se 3 (by rfl) ⟨95639, by rfl⟩ : syracuseStep 510077 = 191279) (by norm_num)
theorem B215245 : Blo 199806 215245 := bbase (se 3 (by rfl) ⟨40358, by rfl⟩ : syracuseStep 215245 = 80717) (by norm_num)
theorem B215317 : Blo 199806 215317 := bbase (se 6 (by rfl) ⟨5046, by rfl⟩ : syracuseStep 215317 = 10093) (by norm_num)
theorem B641429 : Blo 199806 641429 := bbase (se 6 (by rfl) ⟨15033, by rfl⟩ : syracuseStep 641429 = 30067) (by norm_num)
theorem B215497 : Blo 199806 215497 := bbase (se 2 (by rfl) ⟨80811, by rfl⟩ : syracuseStep 215497 = 161623) (by norm_num)
theorem B510421 : Blo 199806 510421 := bbase (se 7 (by rfl) ⟨5981, by rfl⟩ : syracuseStep 510421 = 11963) (by norm_num)
theorem B510533 : Blo 199806 510533 := bbase (se 4 (by rfl) ⟨47862, by rfl⟩ : syracuseStep 510533 = 95725) (by norm_num)
theorem B674405 : Blo 199806 674405 := bbase (se 4 (by rfl) ⟨63225, by rfl⟩ : syracuseStep 674405 = 126451) (by norm_num)
theorem B3263125 : Blo 199806 3263125 := bbase (se 6 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 3263125 = 152959) (by norm_num)
theorem B576229 : Blo 199806 576229 := bbase (se 4 (by rfl) ⟨54021, by rfl⟩ : syracuseStep 576229 = 108043) (by norm_num)
theorem B510725 : Blo 199806 510725 := bbase (se 4 (by rfl) ⟨47880, by rfl⟩ : syracuseStep 510725 = 95761) (by norm_num)
theorem B379741 : Blo 199806 379741 := bbase (se 3 (by rfl) ⟨71201, by rfl⟩ : syracuseStep 379741 = 142403) (by norm_num)
theorem B215941 : Blo 199806 215941 := bbase (se 4 (by rfl) ⟨20244, by rfl⟩ : syracuseStep 215941 = 40489) (by norm_num)
theorem B576389 : Blo 199806 576389 := bbase (se 4 (by rfl) ⟨54036, by rfl⟩ : syracuseStep 576389 = 108073) (by norm_num)
theorem B3263381 : Blo 199806 3263381 := bbase (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) (by norm_num)
theorem B379885 : Blo 199806 379885 := bbase (se 3 (by rfl) ⟨71228, by rfl⟩ : syracuseStep 379885 = 142457) (by norm_num)
theorem B216065 : Blo 199806 216065 := bbase (se 2 (by rfl) ⟨81024, by rfl⟩ : syracuseStep 216065 = 162049) (by norm_num)
theorem B674837 : Blo 199806 674837 := bbase (se 6 (by rfl) ⟨15816, by rfl⟩ : syracuseStep 674837 = 31633) (by norm_num)
theorem B511069 : Blo 199806 511069 := bbase (se 3 (by rfl) ⟨95825, by rfl⟩ : syracuseStep 511069 = 191651) (by norm_num)
theorem B576629 : Blo 199806 576629 := bbase (se 5 (by rfl) ⟨27029, by rfl⟩ : syracuseStep 576629 = 54059) (by norm_num)
theorem B380045 : Blo 199806 380045 := bbase (se 3 (by rfl) ⟨71258, by rfl⟩ : syracuseStep 380045 = 142517) (by norm_num)
theorem B511181 : Blo 199806 511181 := bbase (se 3 (by rfl) ⟨95846, by rfl⟩ : syracuseStep 511181 = 191693) (by norm_num)
theorem B773333 : Blo 199806 773333 := bbase (se 7 (by rfl) ⟨9062, by rfl⟩ : syracuseStep 773333 = 18125) (by norm_num)
theorem B216317 : Blo 199806 216317 := bbase (se 3 (by rfl) ⟨40559, by rfl⟩ : syracuseStep 216317 = 81119) (by norm_num)
theorem B380189 : Blo 199806 380189 := bbase (se 3 (by rfl) ⟨71285, by rfl⟩ : syracuseStep 380189 = 142571) (by norm_num)
theorem B576821 : Blo 199806 576821 := bbase (se 5 (by rfl) ⟨27038, by rfl⟩ : syracuseStep 576821 = 54077) (by norm_num)
theorem B511373 : Blo 199806 511373 := bbase (se 3 (by rfl) ⟨95882, by rfl⟩ : syracuseStep 511373 = 191765) (by norm_num)
theorem B675269 : Blo 199806 675269 := bbase (se 4 (by rfl) ⟨63306, by rfl⟩ : syracuseStep 675269 = 126613) (by norm_num)
theorem B773621 : Blo 199806 773621 := bbase (se 5 (by rfl) ⟨36263, by rfl⟩ : syracuseStep 773621 = 72527) (by norm_num)
theorem B380477 : Blo 199806 380477 := bbase (se 3 (by rfl) ⟨71339, by rfl⟩ : syracuseStep 380477 = 142679) (by norm_num)
theorem B609893 : Blo 199806 609893 := bbase (se 4 (by rfl) ⟨57177, by rfl⟩ : syracuseStep 609893 = 114355) (by norm_num)
theorem B216761 : Blo 199806 216761 := bbase (se 2 (by rfl) ⟨81285, by rfl⟩ : syracuseStep 216761 = 162571) (by norm_num)
theorem B380629 : Blo 199806 380629 := bbase (se 7 (by rfl) ⟨4460, by rfl⟩ : syracuseStep 380629 = 8921) (by norm_num)
theorem B642773 : Blo 199806 642773 := bbase (se 7 (by rfl) ⟨7532, by rfl⟩ : syracuseStep 642773 = 15065) (by norm_num)
theorem B511717 : Blo 199806 511717 := bbase (se 4 (by rfl) ⟨47973, by rfl⟩ : syracuseStep 511717 = 95947) (by norm_num)
theorem B511829 : Blo 199806 511829 := bbase (se 9 (by rfl) ⟨1499, by rfl⟩ : syracuseStep 511829 = 2999) (by norm_num)
theorem B675701 : Blo 199806 675701 := bbase (se 5 (by rfl) ⟨31673, by rfl⟩ : syracuseStep 675701 = 63347) (by norm_num)
theorem B217009 : Blo 199806 217009 := bbase (se 2 (by rfl) ⟨81378, by rfl⟩ : syracuseStep 217009 = 162757) (by norm_num)
theorem B380933 : Blo 199806 380933 := bbase (se 4 (by rfl) ⟨35712, by rfl⟩ : syracuseStep 380933 = 71425) (by norm_num)
theorem B512021 : Blo 199806 512021 := bbase (se 6 (by rfl) ⟨12000, by rfl⟩ : syracuseStep 512021 = 24001) (by norm_num)
theorem B577813 : Blo 199806 577813 := bbase (se 6 (by rfl) ⟨13542, by rfl⟩ : syracuseStep 577813 = 27085) (by norm_num)
theorem B676133 : Blo 199806 676133 := bbase (se 4 (by rfl) ⟨63387, by rfl⟩ : syracuseStep 676133 = 126775) (by norm_num)
theorem B512365 : Blo 199806 512365 := bbase (se 3 (by rfl) ⟨96068, by rfl⟩ : syracuseStep 512365 = 192137) (by norm_num)
theorem B217453 : Blo 199806 217453 := bbase (se 3 (by rfl) ⟨40772, by rfl⟩ : syracuseStep 217453 = 81545) (by norm_num)
theorem B217513 : Blo 199806 217513 := bbase (se 2 (by rfl) ⟨81567, by rfl⟩ : syracuseStep 217513 = 163135) (by norm_num)
theorem B512477 : Blo 199806 512477 := bbase (se 3 (by rfl) ⟨96089, by rfl⟩ : syracuseStep 512477 = 192179) (by norm_num)
theorem B545413 : Blo 199806 545413 := bbase (se 4 (by rfl) ⟨51132, by rfl⟩ : syracuseStep 545413 = 102265) (by norm_num)
theorem B1528469 : Blo 199806 1528469 := bbase (se 6 (by rfl) ⟨35823, by rfl⟩ : syracuseStep 1528469 = 71647) (by norm_num)
theorem B512669 : Blo 199806 512669 := bbase (se 3 (by rfl) ⟨96125, by rfl⟩ : syracuseStep 512669 = 192251) (by norm_num)
theorem B676565 : Blo 199806 676565 := bbase (se 7 (by rfl) ⟨7928, by rfl⟩ : syracuseStep 676565 = 15857) (by norm_num)
theorem B381685 : Blo 199806 381685 := bbase (se 5 (by rfl) ⟨17891, by rfl⟩ : syracuseStep 381685 = 35783) (by norm_num)
theorem B971621 : Blo 199806 971621 := bbase (se 4 (by rfl) ⟨91089, by rfl⟩ : syracuseStep 971621 = 182179) (by norm_num)
theorem B381829 : Blo 199806 381829 := bbase (se 4 (by rfl) ⟨35796, by rfl⟩ : syracuseStep 381829 = 71593) (by norm_num)
theorem B513013 : Blo 199806 513013 := bbase (se 5 (by rfl) ⟨24047, by rfl⟩ : syracuseStep 513013 = 48095) (by norm_num)
theorem B1463285 : Blo 199806 1463285 := bbase (se 5 (by rfl) ⟨68591, by rfl⟩ : syracuseStep 1463285 = 137183) (by norm_num)
theorem B414733 : Blo 199806 414733 := bbase (se 3 (by rfl) ⟨77762, by rfl⟩ : syracuseStep 414733 = 155525) (by norm_num)
theorem B381989 : Blo 199806 381989 := bbase (se 4 (by rfl) ⟨35811, by rfl⟩ : syracuseStep 381989 = 71623) (by norm_num)
theorem B513125 : Blo 199806 513125 := bbase (se 4 (by rfl) ⟨48105, by rfl⟩ : syracuseStep 513125 = 96211) (by norm_num)
theorem B676997 : Blo 199806 676997 := bbase (se 4 (by rfl) ⟨63468, by rfl⟩ : syracuseStep 676997 = 126937) (by norm_num)
theorem B382133 : Blo 199806 382133 := bbase (se 5 (by rfl) ⟨17912, by rfl⟩ : syracuseStep 382133 = 35825) (by norm_num)
theorem B513317 : Blo 199806 513317 := bbase (se 4 (by rfl) ⟨48123, by rfl⟩ : syracuseStep 513317 = 96247) (by norm_num)
theorem B1299797 : Blo 199806 1299797 := bbase (se 15 (by rfl) ⟨59, by rfl⟩ : syracuseStep 1299797 = 119) (by norm_num)
theorem B578917 : Blo 199806 578917 := bbase (se 4 (by rfl) ⟨54273, by rfl⟩ : syracuseStep 578917 = 108547) (by norm_num)
theorem B382421 : Blo 199806 382421 := bbase (se 7 (by rfl) ⟨4481, by rfl⟩ : syracuseStep 382421 = 8963) (by norm_num)
theorem B480773 : Blo 199806 480773 := bbase (se 4 (by rfl) ⟨45072, by rfl⟩ : syracuseStep 480773 = 90145) (by norm_num)
theorem B677429 : Blo 199806 677429 := bbase (se 5 (by rfl) ⟨31754, by rfl⟩ : syracuseStep 677429 = 63509) (by norm_num)
theorem B382573 : Blo 199806 382573 := bbase (se 3 (by rfl) ⟨71732, by rfl⟩ : syracuseStep 382573 = 143465) (by norm_num)
theorem B513661 : Blo 199806 513661 := bbase (se 3 (by rfl) ⟨96311, by rfl⟩ : syracuseStep 513661 = 192623) (by norm_num)
theorem B644773 : Blo 199806 644773 := bbase (se 4 (by rfl) ⟨60447, by rfl⟩ : syracuseStep 644773 = 120895) (by norm_num)
theorem B513773 : Blo 199806 513773 := bbase (se 3 (by rfl) ⟨96332, by rfl⟩ : syracuseStep 513773 = 192665) (by norm_num)
theorem B382877 : Blo 199806 382877 := bbase (se 3 (by rfl) ⟨71789, by rfl⟩ : syracuseStep 382877 = 143579) (by norm_num)
theorem B513965 : Blo 199806 513965 := bbase (se 3 (by rfl) ⟨96368, by rfl⟩ : syracuseStep 513965 = 192737) (by norm_num)
theorem B284629 : Blo 199806 284629 := bbase (se 7 (by rfl) ⟨3335, by rfl⟩ : syracuseStep 284629 = 6671) (by norm_num)
theorem B677861 : Blo 199806 677861 := bbase (se 4 (by rfl) ⟨63549, by rfl⟩ : syracuseStep 677861 = 127099) (by norm_num)
theorem B972965 : Blo 199806 972965 := bbase (se 4 (by rfl) ⟨91215, by rfl⟩ : syracuseStep 972965 = 182431) (by norm_num)
theorem B219329 : Blo 199806 219329 := bbase (se 2 (by rfl) ⟨82248, by rfl⟩ : syracuseStep 219329 = 164497) (by norm_num)
theorem B514309 : Blo 199806 514309 := bbase (se 4 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 514309 = 96433) (by norm_num)
theorem B285005 : Blo 199806 285005 := bbase (se 3 (by rfl) ⟨53438, by rfl⟩ : syracuseStep 285005 = 106877) (by norm_num)
theorem B514421 : Blo 199806 514421 := bbase (se 5 (by rfl) ⟨24113, by rfl⟩ : syracuseStep 514421 = 48227) (by norm_num)
theorem B678293 : Blo 199806 678293 := bbase (se 6 (by rfl) ⟨15897, by rfl⟩ : syracuseStep 678293 = 31795) (by norm_num)
theorem B514613 : Blo 199806 514613 := bbase (se 5 (by rfl) ⟨24122, by rfl⟩ : syracuseStep 514613 = 48245) (by norm_num)
theorem B383629 : Blo 199806 383629 := bbase (se 3 (by rfl) ⟨71930, by rfl⟩ : syracuseStep 383629 = 143861) (by norm_num)
theorem B383773 : Blo 199806 383773 := bbase (se 3 (by rfl) ⟨71957, by rfl⟩ : syracuseStep 383773 = 143915) (by norm_num)
theorem B678725 : Blo 199806 678725 := bbase (se 4 (by rfl) ⟨63630, by rfl⟩ : syracuseStep 678725 = 127261) (by norm_num)
theorem B514957 : Blo 199806 514957 := bbase (se 3 (by rfl) ⟨96554, by rfl⟩ : syracuseStep 514957 = 193109) (by norm_num)
theorem B383933 : Blo 199806 383933 := bbase (se 3 (by rfl) ⟨71987, by rfl⟩ : syracuseStep 383933 = 143975) (by norm_num)
theorem B547813 : Blo 199806 547813 := bbase (se 4 (by rfl) ⟨51357, by rfl⟩ : syracuseStep 547813 = 102715) (by norm_num)
theorem B515069 : Blo 199806 515069 := bbase (se 3 (by rfl) ⟨96575, by rfl⟩ : syracuseStep 515069 = 193151) (by norm_num)
theorem B547877 : Blo 199806 547877 := bbase (se 4 (by rfl) ⟨51363, by rfl⟩ : syracuseStep 547877 = 102727) (by norm_num)
theorem B252973 : Blo 199806 252973 := bbase (se 3 (by rfl) ⟨47432, by rfl⟩ : syracuseStep 252973 = 94865) (by norm_num)
theorem B220205 : Blo 199806 220205 := bbase (se 3 (by rfl) ⟨41288, by rfl⟩ : syracuseStep 220205 = 82577) (by norm_num)
theorem B384077 : Blo 199806 384077 := bbase (se 3 (by rfl) ⟨72014, by rfl⟩ : syracuseStep 384077 = 144029) (by norm_num)
theorem B449621 : Blo 199806 449621 := bbase (se 8 (by rfl) ⟨2634, by rfl⟩ : syracuseStep 449621 = 5269) (by norm_num)
theorem B449693 : Blo 199806 449693 := bbase (se 3 (by rfl) ⟨84317, by rfl⟩ : syracuseStep 449693 = 168635) (by norm_num)
theorem B515261 : Blo 199806 515261 := bbase (se 3 (by rfl) ⟨96611, by rfl⟩ : syracuseStep 515261 = 193223) (by norm_num)
theorem B253145 : Blo 199806 253145 := bbase (se 2 (by rfl) ⟨94929, by rfl⟩ : syracuseStep 253145 = 189859) (by norm_num)
theorem B449765 : Blo 199806 449765 := bbase (se 4 (by rfl) ⟨42165, by rfl⟩ : syracuseStep 449765 = 84331) (by norm_num)
theorem B679157 : Blo 199806 679157 := bbase (se 5 (by rfl) ⟨31835, by rfl⟩ : syracuseStep 679157 = 63671) (by norm_num)
theorem B253201 : Blo 199806 253201 := bbase (se 2 (by rfl) ⟨94950, by rfl⟩ : syracuseStep 253201 = 189901) (by norm_num)
theorem B449837 : Blo 199806 449837 := bbase (se 3 (by rfl) ⟨84344, by rfl⟩ : syracuseStep 449837 = 168689) (by norm_num)
theorem B384365 : Blo 199806 384365 := bbase (se 3 (by rfl) ⟨72068, by rfl⟩ : syracuseStep 384365 = 144137) (by norm_num)
theorem B253297 : Blo 199806 253297 := bbase (se 2 (by rfl) ⟨94986, by rfl⟩ : syracuseStep 253297 = 189973) (by norm_num)
theorem B449909 : Blo 199806 449909 := bbase (se 5 (by rfl) ⟨21089, by rfl⟩ : syracuseStep 449909 = 42179) (by norm_num)
theorem B515501 : Blo 199806 515501 := bbase (se 3 (by rfl) ⟨96656, by rfl⟩ : syracuseStep 515501 = 193313) (by norm_num)
theorem B449981 : Blo 199806 449981 := bbase (se 3 (by rfl) ⟨84371, by rfl⟩ : syracuseStep 449981 = 168743) (by norm_num)
theorem B482773 : Blo 199806 482773 := bbase (se 7 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 482773 = 11315) (by norm_num)
theorem B450053 : Blo 199806 450053 := bbase (se 4 (by rfl) ⟨42192, by rfl⟩ : syracuseStep 450053 = 84385) (by norm_num)
theorem B384517 : Blo 199806 384517 := bbase (se 4 (by rfl) ⟨36048, by rfl⟩ : syracuseStep 384517 = 72097) (by norm_num)
theorem B515605 : Blo 199806 515605 := bbase (se 6 (by rfl) ⟨12084, by rfl⟩ : syracuseStep 515605 = 24169) (by norm_num)
theorem B253469 : Blo 199806 253469 := bbase (se 3 (by rfl) ⟨47525, by rfl⟩ : syracuseStep 253469 = 95051) (by norm_num)
theorem B450125 : Blo 199806 450125 := bbase (se 3 (by rfl) ⟨84398, by rfl⟩ : syracuseStep 450125 = 168797) (by norm_num)
theorem B253525 : Blo 199806 253525 := bbase (se 8 (by rfl) ⟨1485, by rfl⟩ : syracuseStep 253525 = 2971) (by norm_num)
theorem B482917 : Blo 199806 482917 := bbase (se 4 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 482917 = 90547) (by norm_num)
theorem B515717 : Blo 199806 515717 := bbase (se 4 (by rfl) ⟨48348, by rfl⟩ : syracuseStep 515717 = 96697) (by norm_num)
theorem B450197 : Blo 199806 450197 := bbase (se 6 (by rfl) ⟨10551, by rfl⟩ : syracuseStep 450197 = 21103) (by norm_num)
theorem B679589 : Blo 199806 679589 := bbase (se 4 (by rfl) ⟨63711, by rfl⟩ : syracuseStep 679589 = 127423) (by norm_num)
theorem B253621 : Blo 199806 253621 := bbase (se 5 (by rfl) ⟨11888, by rfl⟩ : syracuseStep 253621 = 23777) (by norm_num)
theorem B450269 : Blo 199806 450269 := bbase (se 3 (by rfl) ⟨84425, by rfl⟩ : syracuseStep 450269 = 168851) (by norm_num)
theorem B286429 : Blo 199806 286429 := bbase (se 3 (by rfl) ⟨53705, by rfl⟩ : syracuseStep 286429 = 107411) (by norm_num)
theorem B450341 : Blo 199806 450341 := bbase (se 4 (by rfl) ⟨42219, by rfl⟩ : syracuseStep 450341 = 84439) (by norm_num)
theorem B384821 : Blo 199806 384821 := bbase (se 5 (by rfl) ⟨18038, by rfl⟩ : syracuseStep 384821 = 36077) (by norm_num)
theorem B253793 : Blo 199806 253793 := bbase (se 2 (by rfl) ⟨95172, by rfl⟩ : syracuseStep 253793 = 190345) (by norm_num)
theorem B450413 : Blo 199806 450413 := bbase (se 3 (by rfl) ⟨84452, by rfl⟩ : syracuseStep 450413 = 168905) (by norm_num)
theorem B548741 : Blo 199806 548741 := bbase (se 4 (by rfl) ⟨51444, by rfl⟩ : syracuseStep 548741 = 102889) (by norm_num)
theorem B253849 : Blo 199806 253849 := bbase (se 2 (by rfl) ⟨95193, by rfl⟩ : syracuseStep 253849 = 190387) (by norm_num)
theorem B810917 : Blo 199806 810917 := bbase (se 4 (by rfl) ⟨76023, by rfl⟩ : syracuseStep 810917 = 152047) (by norm_num)
theorem B450485 : Blo 199806 450485 := bbase (se 5 (by rfl) ⟨21116, by rfl⟩ : syracuseStep 450485 = 42233) (by norm_num)
theorem B253945 : Blo 199806 253945 := bbase (se 2 (by rfl) ⟨95229, by rfl⟩ : syracuseStep 253945 = 190459) (by norm_num)
theorem B450557 : Blo 199806 450557 := bbase (se 3 (by rfl) ⟨84479, by rfl⟩ : syracuseStep 450557 = 168959) (by norm_num)
theorem B450629 : Blo 199806 450629 := bbase (se 4 (by rfl) ⟨42246, by rfl⟩ : syracuseStep 450629 = 84493) (by norm_num)
theorem B680021 : Blo 199806 680021 := bbase (se 8 (by rfl) ⟨3984, by rfl⟩ : syracuseStep 680021 = 7969) (by norm_num)
theorem B450701 : Blo 199806 450701 := bbase (se 3 (by rfl) ⟨84506, by rfl⟩ : syracuseStep 450701 = 169013) (by norm_num)
theorem B254117 : Blo 199806 254117 := bbase (se 4 (by rfl) ⟨23823, by rfl⟩ : syracuseStep 254117 = 47647) (by norm_num)
theorem B483533 : Blo 199806 483533 := bbase (se 3 (by rfl) ⟨90662, by rfl⟩ : syracuseStep 483533 = 181325) (by norm_num)
theorem B450773 : Blo 199806 450773 := bbase (se 7 (by rfl) ⟨5282, by rfl⟩ : syracuseStep 450773 = 10565) (by norm_num)
theorem B254173 : Blo 199806 254173 := bbase (se 3 (by rfl) ⟨47657, by rfl⟩ : syracuseStep 254173 = 95315) (by norm_num)
theorem B516365 : Blo 199806 516365 := bbase (se 3 (by rfl) ⟨96818, by rfl⟩ : syracuseStep 516365 = 193637) (by norm_num)
theorem B450845 : Blo 199806 450845 := bbase (se 3 (by rfl) ⟨84533, by rfl⟩ : syracuseStep 450845 = 169067) (by norm_num)
theorem B287021 : Blo 199806 287021 := bbase (se 3 (by rfl) ⟨53816, by rfl⟩ : syracuseStep 287021 = 107633) (by norm_num)
theorem B254269 : Blo 199806 254269 := bbase (se 3 (by rfl) ⟨47675, by rfl⟩ : syracuseStep 254269 = 95351) (by norm_num)
theorem B450917 : Blo 199806 450917 := bbase (se 4 (by rfl) ⟨42273, by rfl⟩ : syracuseStep 450917 = 84547) (by norm_num)
theorem B287101 : Blo 199806 287101 := bbase (se 3 (by rfl) ⟨53831, by rfl⟩ : syracuseStep 287101 = 107663) (by norm_num)
theorem B450989 : Blo 199806 450989 := bbase (se 3 (by rfl) ⟨84560, by rfl⟩ : syracuseStep 450989 = 169121) (by norm_num)
theorem B254441 : Blo 199806 254441 := bbase (se 2 (by rfl) ⟨95415, by rfl⟩ : syracuseStep 254441 = 190831) (by norm_num)
theorem B451061 : Blo 199806 451061 := bbase (se 5 (by rfl) ⟨21143, by rfl⟩ : syracuseStep 451061 = 42287) (by norm_num)
theorem B287221 : Blo 199806 287221 := bbase (se 5 (by rfl) ⟨13463, by rfl⟩ : syracuseStep 287221 = 26927) (by norm_num)
theorem B1237493 : Blo 199806 1237493 := bbase (se 5 (by rfl) ⟨58007, by rfl⟩ : syracuseStep 1237493 = 116015) (by norm_num)
theorem B680453 : Blo 199806 680453 := bbase (se 4 (by rfl) ⟨63792, by rfl⟩ : syracuseStep 680453 = 127585) (by norm_num)
theorem B483869 : Blo 199806 483869 := bbase (se 3 (by rfl) ⟨90725, by rfl⟩ : syracuseStep 483869 = 181451) (by norm_num)
theorem B254497 : Blo 199806 254497 := bbase (se 2 (by rfl) ⟨95436, by rfl⟩ : syracuseStep 254497 = 190873) (by norm_num)
theorem B385573 : Blo 199806 385573 := bbase (se 4 (by rfl) ⟨36147, by rfl⟩ : syracuseStep 385573 = 72295) (by norm_num)
theorem B451133 : Blo 199806 451133 := bbase (se 3 (by rfl) ⟨84587, by rfl⟩ : syracuseStep 451133 = 169175) (by norm_num)
theorem B287317 : Blo 199806 287317 := bbase (se 8 (by rfl) ⟨1683, by rfl⟩ : syracuseStep 287317 = 3367) (by norm_num)
theorem B647797 : Blo 199806 647797 := bbase (se 5 (by rfl) ⟨30365, by rfl⟩ : syracuseStep 647797 = 60731) (by norm_num)
theorem B483965 : Blo 199806 483965 := bbase (se 3 (by rfl) ⟨90743, by rfl⟩ : syracuseStep 483965 = 181487) (by norm_num)
theorem B254593 : Blo 199806 254593 := bbase (se 2 (by rfl) ⟨95472, by rfl⟩ : syracuseStep 254593 = 190945) (by norm_num)
theorem B451205 : Blo 199806 451205 := bbase (se 4 (by rfl) ⟨42300, by rfl⟩ : syracuseStep 451205 = 84601) (by norm_num)
theorem B385717 : Blo 199806 385717 := bbase (se 5 (by rfl) ⟨18080, by rfl⟩ : syracuseStep 385717 = 36161) (by norm_num)
theorem B451277 : Blo 199806 451277 := bbase (se 3 (by rfl) ⟨84614, by rfl⟩ : syracuseStep 451277 = 169229) (by norm_num)
theorem B320221 : Blo 199806 320221 := bbase (se 3 (by rfl) ⟨60041, by rfl⟩ : syracuseStep 320221 = 120083) (by norm_num)
theorem B451349 : Blo 199806 451349 := bbase (se 6 (by rfl) ⟨10578, by rfl⟩ : syracuseStep 451349 = 21157) (by norm_num)
theorem B1237781 : Blo 199806 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B254765 : Blo 199806 254765 := bbase (se 3 (by rfl) ⟨47768, by rfl⟩ : syracuseStep 254765 = 95537) (by norm_num)
theorem B484157 : Blo 199806 484157 := bbase (se 3 (by rfl) ⟨90779, by rfl⟩ : syracuseStep 484157 = 181559) (by norm_num)
theorem B385877 : Blo 199806 385877 := bbase (se 9 (by rfl) ⟨1130, by rfl⟩ : syracuseStep 385877 = 2261) (by norm_num)
theorem B451421 : Blo 199806 451421 := bbase (se 3 (by rfl) ⟨84641, by rfl⟩ : syracuseStep 451421 = 169283) (by norm_num)
theorem B254821 : Blo 199806 254821 := bbase (se 4 (by rfl) ⟨23889, by rfl⟩ : syracuseStep 254821 = 47779) (by norm_num)
theorem B451493 : Blo 199806 451493 := bbase (se 4 (by rfl) ⟨42327, by rfl⟩ : syracuseStep 451493 = 84655) (by norm_num)
theorem B680885 : Blo 199806 680885 := bbase (se 5 (by rfl) ⟨31916, by rfl⟩ : syracuseStep 680885 = 63833) (by norm_num)
theorem B254917 : Blo 199806 254917 := bbase (se 4 (by rfl) ⟨23898, by rfl⟩ : syracuseStep 254917 = 47797) (by norm_num)
theorem B386021 : Blo 199806 386021 := bbase (se 4 (by rfl) ⟨36189, by rfl⟩ : syracuseStep 386021 = 72379) (by norm_num)
theorem B451565 : Blo 199806 451565 := bbase (se 3 (by rfl) ⟨84668, by rfl⟩ : syracuseStep 451565 = 169337) (by norm_num)
theorem B582661 : Blo 199806 582661 := bbase (se 4 (by rfl) ⟨54624, by rfl⟩ : syracuseStep 582661 = 109249) (by norm_num)
theorem B451637 : Blo 199806 451637 := bbase (se 5 (by rfl) ⟨21170, by rfl⟩ : syracuseStep 451637 = 42341) (by norm_num)
theorem B287813 : Blo 199806 287813 := bbase (se 4 (by rfl) ⟨26982, by rfl⟩ : syracuseStep 287813 = 53965) (by norm_num)
theorem B255089 : Blo 199806 255089 := bbase (se 2 (by rfl) ⟨95658, by rfl⟩ : syracuseStep 255089 = 191317) (by norm_num)
theorem B451709 : Blo 199806 451709 := bbase (se 3 (by rfl) ⟨84695, by rfl⟩ : syracuseStep 451709 = 169391) (by norm_num)
theorem B255145 : Blo 199806 255145 := bbase (se 2 (by rfl) ⟨95679, by rfl⟩ : syracuseStep 255145 = 191359) (by norm_num)
theorem B451781 : Blo 199806 451781 := bbase (se 4 (by rfl) ⟨42354, by rfl⟩ : syracuseStep 451781 = 84709) (by norm_num)
theorem B1729781 : Blo 199806 1729781 := bbase (se 5 (by rfl) ⟨81083, by rfl⟩ : syracuseStep 1729781 = 162167) (by norm_num)
theorem B386309 : Blo 199806 386309 := bbase (se 4 (by rfl) ⟨36216, by rfl⟩ : syracuseStep 386309 = 72433) (by norm_num)
theorem B255241 : Blo 199806 255241 := bbase (se 2 (by rfl) ⟨95715, by rfl⟩ : syracuseStep 255241 = 191431) (by norm_num)
theorem B451853 : Blo 199806 451853 := bbase (se 3 (by rfl) ⟨84722, by rfl⟩ : syracuseStep 451853 = 169445) (by norm_num)
theorem B386365 : Blo 199806 386365 := bbase (se 3 (by rfl) ⟨72443, by rfl⟩ : syracuseStep 386365 = 144887) (by norm_num)
theorem B451925 : Blo 199806 451925 := bbase (se 12 (by rfl) ⟨165, by rfl⟩ : syracuseStep 451925 = 331) (by norm_num)
theorem B681317 : Blo 199806 681317 := bbase (se 4 (by rfl) ⟨63873, by rfl⟩ : syracuseStep 681317 = 127747) (by norm_num)
theorem B451997 : Blo 199806 451997 := bbase (se 3 (by rfl) ⟨84749, by rfl⟩ : syracuseStep 451997 = 169499) (by norm_num)
theorem B386461 : Blo 199806 386461 := bbase (se 3 (by rfl) ⟨72461, by rfl⟩ : syracuseStep 386461 = 144923) (by norm_num)
theorem B255413 : Blo 199806 255413 := bbase (se 5 (by rfl) ⟨11972, by rfl⟩ : syracuseStep 255413 = 23945) (by norm_num)
theorem B452069 : Blo 199806 452069 := bbase (se 4 (by rfl) ⟨42381, by rfl⟩ : syracuseStep 452069 = 84763) (by norm_num)
theorem B255469 : Blo 199806 255469 := bbase (se 3 (by rfl) ⟨47900, by rfl⟩ : syracuseStep 255469 = 95801) (by norm_num)
theorem B452141 : Blo 199806 452141 := bbase (se 3 (by rfl) ⟨84776, by rfl⟩ : syracuseStep 452141 = 169553) (by norm_num)
theorem B255565 : Blo 199806 255565 := bbase (se 3 (by rfl) ⟨47918, by rfl⟩ : syracuseStep 255565 = 95837) (by norm_num)
theorem B288365 : Blo 199806 288365 := bbase (se 3 (by rfl) ⟨54068, by rfl⟩ : syracuseStep 288365 = 108137) (by norm_num)
theorem B452213 : Blo 199806 452213 := bbase (se 5 (by rfl) ⟨21197, by rfl⟩ : syracuseStep 452213 = 42395) (by norm_num)
theorem B452285 : Blo 199806 452285 := bbase (se 3 (by rfl) ⟨84803, by rfl⟩ : syracuseStep 452285 = 169607) (by norm_num)
theorem B386765 : Blo 199806 386765 := bbase (se 3 (by rfl) ⟨72518, by rfl⟩ : syracuseStep 386765 = 145037) (by norm_num)
theorem B255737 : Blo 199806 255737 := bbase (se 2 (by rfl) ⟨95901, by rfl⟩ : syracuseStep 255737 = 191803) (by norm_num)
theorem B452357 : Blo 199806 452357 := bbase (se 4 (by rfl) ⟨42408, by rfl⟩ : syracuseStep 452357 = 84817) (by norm_num)
theorem B681749 : Blo 199806 681749 := bbase (se 6 (by rfl) ⟨15978, by rfl⟩ : syracuseStep 681749 = 31957) (by norm_num)
theorem B255793 : Blo 199806 255793 := bbase (se 2 (by rfl) ⟨95922, by rfl⟩ : syracuseStep 255793 = 191845) (by norm_num)
theorem B976693 : Blo 199806 976693 := bbase (se 5 (by rfl) ⟨45782, by rfl⟩ : syracuseStep 976693 = 91565) (by norm_num)
theorem B321349 : Blo 199806 321349 := bbase (se 4 (by rfl) ⟨30126, by rfl⟩ : syracuseStep 321349 = 60253) (by norm_num)
theorem B452429 : Blo 199806 452429 := bbase (se 3 (by rfl) ⟨84830, by rfl⟩ : syracuseStep 452429 = 169661) (by norm_num)
theorem B255889 : Blo 199806 255889 := bbase (se 2 (by rfl) ⟨95958, by rfl⟩ : syracuseStep 255889 = 191917) (by norm_num)
theorem B452501 : Blo 199806 452501 := bbase (se 6 (by rfl) ⟨10605, by rfl⟩ : syracuseStep 452501 = 21211) (by norm_num)
theorem B485309 : Blo 199806 485309 := bbase (se 3 (by rfl) ⟨90995, by rfl⟩ : syracuseStep 485309 = 181991) (by norm_num)
theorem B452573 : Blo 199806 452573 := bbase (se 3 (by rfl) ⟨84857, by rfl⟩ : syracuseStep 452573 = 169715) (by norm_num)
theorem B1304597 : Blo 199806 1304597 := bbase (se 6 (by rfl) ⟨30576, by rfl⟩ : syracuseStep 1304597 = 61153) (by norm_num)
theorem B452645 : Blo 199806 452645 := bbase (se 4 (by rfl) ⟨42435, by rfl⟩ : syracuseStep 452645 = 84871) (by norm_num)
theorem B256061 : Blo 199806 256061 := bbase (se 3 (by rfl) ⟨48011, by rfl⟩ : syracuseStep 256061 = 96023) (by norm_num)
theorem B452717 : Blo 199806 452717 := bbase (se 3 (by rfl) ⟨84884, by rfl⟩ : syracuseStep 452717 = 169769) (by norm_num)
theorem B256117 : Blo 199806 256117 := bbase (se 5 (by rfl) ⟨12005, by rfl⟩ : syracuseStep 256117 = 24011) (by norm_num)
theorem B452789 : Blo 199806 452789 := bbase (se 5 (by rfl) ⟨21224, by rfl⟩ : syracuseStep 452789 = 42449) (by norm_num)
theorem B682181 : Blo 199806 682181 := bbase (se 4 (by rfl) ⟨63954, by rfl⟩ : syracuseStep 682181 = 127909) (by norm_num)
theorem B256213 : Blo 199806 256213 := bbase (se 7 (by rfl) ⟨3002, by rfl⟩ : syracuseStep 256213 = 6005) (by norm_num)
theorem B452861 : Blo 199806 452861 := bbase (se 3 (by rfl) ⟨84911, by rfl⟩ : syracuseStep 452861 = 169823) (by norm_num)
theorem B321797 : Blo 199806 321797 := bbase (se 4 (by rfl) ⟨30168, by rfl⟩ : syracuseStep 321797 = 60337) (by norm_num)
theorem B452933 : Blo 199806 452933 := bbase (se 4 (by rfl) ⟨42462, by rfl⟩ : syracuseStep 452933 = 84925) (by norm_num)
theorem B256333 : Blo 199806 256333 := bbase (se 3 (by rfl) ⟨48062, by rfl⟩ : syracuseStep 256333 = 96125) (by norm_num)
theorem B289117 : Blo 199806 289117 := bbase (se 3 (by rfl) ⟨54209, by rfl⟩ : syracuseStep 289117 = 108419) (by norm_num)
theorem B223585 : Blo 199806 223585 := bbase (se 2 (by rfl) ⟨83844, by rfl⟩ : syracuseStep 223585 = 167689) (by norm_num)
theorem B256385 : Blo 199806 256385 := bbase (se 2 (by rfl) ⟨96144, by rfl⟩ : syracuseStep 256385 = 192289) (by norm_num)
theorem B616837 : Blo 199806 616837 := bbase (se 4 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 616837 = 115657) (by norm_num)
theorem B453005 : Blo 199806 453005 := bbase (se 3 (by rfl) ⟨84938, by rfl⟩ : syracuseStep 453005 = 169877) (by norm_num)
theorem B256441 : Blo 199806 256441 := bbase (se 2 (by rfl) ⟨96165, by rfl⟩ : syracuseStep 256441 = 192331) (by norm_num)
theorem B453077 : Blo 199806 453077 := bbase (se 7 (by rfl) ⟨5309, by rfl⟩ : syracuseStep 453077 = 10619) (by norm_num)
theorem B256493 : Blo 199806 256493 := bbase (se 3 (by rfl) ⟨48092, by rfl⟩ : syracuseStep 256493 = 96185) (by norm_num)
theorem B256537 : Blo 199806 256537 := bbase (se 2 (by rfl) ⟨96201, by rfl⟩ : syracuseStep 256537 = 192403) (by norm_num)
theorem B453149 : Blo 199806 453149 := bbase (se 3 (by rfl) ⟨84965, by rfl⟩ : syracuseStep 453149 = 169931) (by norm_num)
theorem B453221 : Blo 199806 453221 := bbase (se 4 (by rfl) ⟨42489, by rfl⟩ : syracuseStep 453221 = 84979) (by norm_num)
theorem B682613 : Blo 199806 682613 := bbase (se 5 (by rfl) ⟨31997, by rfl⟩ : syracuseStep 682613 = 63995) (by norm_num)
theorem B453293 : Blo 199806 453293 := bbase (se 3 (by rfl) ⟨84992, by rfl⟩ : syracuseStep 453293 = 169985) (by norm_num)
theorem B256709 : Blo 199806 256709 := bbase (se 4 (by rfl) ⟨24066, by rfl⟩ : syracuseStep 256709 = 48133) (by norm_num)
theorem B453365 : Blo 199806 453365 := bbase (se 5 (by rfl) ⟨21251, by rfl⟩ : syracuseStep 453365 = 42503) (by norm_num)
theorem B256765 : Blo 199806 256765 := bbase (se 3 (by rfl) ⟨48143, by rfl⟩ : syracuseStep 256765 = 96287) (by norm_num)
theorem B453437 : Blo 199806 453437 := bbase (se 3 (by rfl) ⟨85019, by rfl⟩ : syracuseStep 453437 = 170039) (by norm_num)
theorem B256861 : Blo 199806 256861 := bbase (se 3 (by rfl) ⟨48161, by rfl⟩ : syracuseStep 256861 = 96323) (by norm_num)
theorem B453509 : Blo 199806 453509 := bbase (se 4 (by rfl) ⟨42516, by rfl⟩ : syracuseStep 453509 = 85033) (by norm_num)
theorem B453581 : Blo 199806 453581 := bbase (se 3 (by rfl) ⟨85046, by rfl⟩ : syracuseStep 453581 = 170093) (by norm_num)
theorem B257033 : Blo 199806 257033 := bbase (se 2 (by rfl) ⟨96387, by rfl⟩ : syracuseStep 257033 = 192775) (by norm_num)
theorem B453653 : Blo 199806 453653 := bbase (se 6 (by rfl) ⟨10632, by rfl⟩ : syracuseStep 453653 = 21265) (by norm_num)
theorem B683045 : Blo 199806 683045 := bbase (se 4 (by rfl) ⟨64035, by rfl⟩ : syracuseStep 683045 = 128071) (by norm_num)
theorem B257089 : Blo 199806 257089 := bbase (se 2 (by rfl) ⟨96408, by rfl⟩ : syracuseStep 257089 = 192817) (by norm_num)
theorem B453725 : Blo 199806 453725 := bbase (se 3 (by rfl) ⟨85073, by rfl⟩ : syracuseStep 453725 = 170147) (by norm_num)
theorem B289909 : Blo 199806 289909 := bbase (se 5 (by rfl) ⟨13589, by rfl⟩ : syracuseStep 289909 = 27179) (by norm_num)
theorem B519317 : Blo 199806 519317 := bbase (se 6 (by rfl) ⟨12171, by rfl⟩ : syracuseStep 519317 = 24343) (by norm_num)
theorem B257185 : Blo 199806 257185 := bbase (se 2 (by rfl) ⟨96444, by rfl⟩ : syracuseStep 257185 = 192889) (by norm_num)
theorem B453797 : Blo 199806 453797 := bbase (se 4 (by rfl) ⟨42543, by rfl⟩ : syracuseStep 453797 = 85087) (by norm_num)
theorem B257197 : Blo 199806 257197 := bbase (se 3 (by rfl) ⟨48224, by rfl⟩ : syracuseStep 257197 = 96449) (by norm_num)
theorem B453869 : Blo 199806 453869 := bbase (se 3 (by rfl) ⟨85100, by rfl⟩ : syracuseStep 453869 = 170201) (by norm_num)
theorem B453941 : Blo 199806 453941 := bbase (se 5 (by rfl) ⟨21278, by rfl⟩ : syracuseStep 453941 = 42557) (by norm_num)
theorem B257357 : Blo 199806 257357 := bbase (se 3 (by rfl) ⟨48254, by rfl⟩ : syracuseStep 257357 = 96509) (by norm_num)
theorem B454013 : Blo 199806 454013 := bbase (se 3 (by rfl) ⟨85127, by rfl⟩ : syracuseStep 454013 = 170255) (by norm_num)
theorem B257413 : Blo 199806 257413 := bbase (se 4 (by rfl) ⟨24132, by rfl⟩ : syracuseStep 257413 = 48265) (by norm_num)
theorem B454085 : Blo 199806 454085 := bbase (se 4 (by rfl) ⟨42570, by rfl⟩ : syracuseStep 454085 = 85141) (by norm_num)
theorem B585157 : Blo 199806 585157 := bbase (se 4 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 585157 = 109717) (by norm_num)
theorem B650693 : Blo 199806 650693 := bbase (se 4 (by rfl) ⟨61002, by rfl⟩ : syracuseStep 650693 = 122005) (by norm_num)
theorem B683477 : Blo 199806 683477 := bbase (se 7 (by rfl) ⟨8009, by rfl⟩ : syracuseStep 683477 = 16019) (by norm_num)
theorem B257509 : Blo 199806 257509 := bbase (se 4 (by rfl) ⟨24141, by rfl⟩ : syracuseStep 257509 = 48283) (by norm_num)
theorem B454157 : Blo 199806 454157 := bbase (se 3 (by rfl) ⟨85154, by rfl⟩ : syracuseStep 454157 = 170309) (by norm_num)
theorem B224797 : Blo 199806 224797 := bbase (se 3 (by rfl) ⟨42149, by rfl⟩ : syracuseStep 224797 = 84299) (by norm_num)
theorem B224833 : Blo 199806 224833 := bbase (se 2 (by rfl) ⟨84312, by rfl⟩ : syracuseStep 224833 = 168625) (by norm_num)
theorem B454229 : Blo 199806 454229 := bbase (se 8 (by rfl) ⟨2661, by rfl⟩ : syracuseStep 454229 = 5323) (by norm_num)
theorem B224869 : Blo 199806 224869 := bbase (se 4 (by rfl) ⟨21081, by rfl⟩ : syracuseStep 224869 = 42163) (by norm_num)
theorem B224905 : Blo 199806 224905 := bbase (se 2 (by rfl) ⟨84339, by rfl⟩ : syracuseStep 224905 = 168679) (by norm_num)
theorem B257681 : Blo 199806 257681 := bbase (se 2 (by rfl) ⟨96630, by rfl⟩ : syracuseStep 257681 = 193261) (by norm_num)
theorem B454301 : Blo 199806 454301 := bbase (se 3 (by rfl) ⟨85181, by rfl⟩ : syracuseStep 454301 = 170363) (by norm_num)
theorem B224941 : Blo 199806 224941 := bbase (se 3 (by rfl) ⟨42176, by rfl⟩ : syracuseStep 224941 = 84353) (by norm_num)
theorem B257737 : Blo 199806 257737 := bbase (se 2 (by rfl) ⟨96651, by rfl⟩ : syracuseStep 257737 = 193303) (by norm_num)
theorem B224977 : Blo 199806 224977 := bbase (se 2 (by rfl) ⟨84366, by rfl⟩ : syracuseStep 224977 = 168733) (by norm_num)
theorem B454373 : Blo 199806 454373 := bbase (se 4 (by rfl) ⟨42597, by rfl⟩ : syracuseStep 454373 = 85195) (by norm_num)
theorem B323309 : Blo 199806 323309 := bbase (se 3 (by rfl) ⟨60620, by rfl⟩ : syracuseStep 323309 = 121241) (by norm_num)
theorem B225013 : Blo 199806 225013 := bbase (se 5 (by rfl) ⟨10547, by rfl⟩ : syracuseStep 225013 = 21095) (by norm_num)
theorem B913157 : Blo 199806 913157 := bbase (se 4 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 913157 = 171217) (by norm_num)
theorem B225049 : Blo 199806 225049 := bbase (se 2 (by rfl) ⟨84393, by rfl⟩ : syracuseStep 225049 = 168787) (by norm_num)
theorem B257833 : Blo 199806 257833 := bbase (se 2 (by rfl) ⟨96687, by rfl⟩ : syracuseStep 257833 = 193375) (by norm_num)
theorem B454445 : Blo 199806 454445 := bbase (se 3 (by rfl) ⟨85208, by rfl⟩ : syracuseStep 454445 = 170417) (by norm_num)
theorem B225085 : Blo 199806 225085 := bbase (se 3 (by rfl) ⟨42203, by rfl⟩ : syracuseStep 225085 = 84407) (by norm_num)
theorem B225121 : Blo 199806 225121 := bbase (se 2 (by rfl) ⟨84420, by rfl⟩ : syracuseStep 225121 = 168841) (by norm_num)
theorem B323437 : Blo 199806 323437 := bbase (se 3 (by rfl) ⟨60644, by rfl⟩ : syracuseStep 323437 = 121289) (by norm_num)
theorem B454517 : Blo 199806 454517 := bbase (se 5 (by rfl) ⟨21305, by rfl⟩ : syracuseStep 454517 = 42611) (by norm_num)
theorem B225157 : Blo 199806 225157 := bbase (se 4 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 225157 = 42217) (by norm_num)
theorem B683909 : Blo 199806 683909 := bbase (se 4 (by rfl) ⟨64116, by rfl⟩ : syracuseStep 683909 = 128233) (by norm_num)
theorem B487309 : Blo 199806 487309 := bbase (se 3 (by rfl) ⟨91370, by rfl⟩ : syracuseStep 487309 = 182741) (by norm_num)
theorem B225193 : Blo 199806 225193 := bbase (se 2 (by rfl) ⟨84447, by rfl⟩ : syracuseStep 225193 = 168895) (by norm_num)
theorem B454589 : Blo 199806 454589 := bbase (se 3 (by rfl) ⟨85235, by rfl⟩ : syracuseStep 454589 = 170471) (by norm_num)
theorem B225229 : Blo 199806 225229 := bbase (se 3 (by rfl) ⟨42230, by rfl⟩ : syracuseStep 225229 = 84461) (by norm_num)
theorem B487405 : Blo 199806 487405 := bbase (se 3 (by rfl) ⟨91388, by rfl⟩ : syracuseStep 487405 = 182777) (by norm_num)
theorem B225265 : Blo 199806 225265 := bbase (se 2 (by rfl) ⟨84474, by rfl⟩ : syracuseStep 225265 = 168949) (by norm_num)
theorem B454661 : Blo 199806 454661 := bbase (se 4 (by rfl) ⟨42624, by rfl⟩ : syracuseStep 454661 = 85249) (by norm_num)
theorem B225301 : Blo 199806 225301 := bbase (se 6 (by rfl) ⟨5280, by rfl⟩ : syracuseStep 225301 = 10561) (by norm_num)
theorem B1634357 : Blo 199806 1634357 := bbase (se 5 (by rfl) ⟨76610, by rfl⟩ : syracuseStep 1634357 = 153221) (by norm_num)
theorem B225337 : Blo 199806 225337 := bbase (se 2 (by rfl) ⟨84501, by rfl⟩ : syracuseStep 225337 = 169003) (by norm_num)
theorem B454733 : Blo 199806 454733 := bbase (se 3 (by rfl) ⟨85262, by rfl⟩ : syracuseStep 454733 = 170525) (by norm_num)
theorem B225373 : Blo 199806 225373 := bbase (se 3 (by rfl) ⟨42257, by rfl⟩ : syracuseStep 225373 = 84515) (by norm_num)
theorem B225409 : Blo 199806 225409 := bbase (se 2 (by rfl) ⟨84528, by rfl⟩ : syracuseStep 225409 = 169057) (by norm_num)
theorem B454805 : Blo 199806 454805 := bbase (se 6 (by rfl) ⟨10659, by rfl⟩ : syracuseStep 454805 = 21319) (by norm_num)
theorem B225445 : Blo 199806 225445 := bbase (se 4 (by rfl) ⟨21135, by rfl⟩ : syracuseStep 225445 = 42271) (by norm_num)
theorem B225481 : Blo 199806 225481 := bbase (se 2 (by rfl) ⟨84555, by rfl⟩ : syracuseStep 225481 = 169111) (by norm_num)
theorem B454877 : Blo 199806 454877 := bbase (se 3 (by rfl) ⟨85289, by rfl⟩ : syracuseStep 454877 = 170579) (by norm_num)
theorem B225517 : Blo 199806 225517 := bbase (se 3 (by rfl) ⟨42284, by rfl⟩ : syracuseStep 225517 = 84569) (by norm_num)
theorem B1536245 : Blo 199806 1536245 := bbase (se 5 (by rfl) ⟨72011, by rfl⟩ : syracuseStep 1536245 = 144023) (by norm_num)
theorem B225553 : Blo 199806 225553 := bbase (se 2 (by rfl) ⟨84582, by rfl⟩ : syracuseStep 225553 = 169165) (by norm_num)
theorem B454949 : Blo 199806 454949 := bbase (se 4 (by rfl) ⟨42651, by rfl⟩ : syracuseStep 454949 = 85303) (by norm_num)
theorem B225589 : Blo 199806 225589 := bbase (se 5 (by rfl) ⟨10574, by rfl⟩ : syracuseStep 225589 = 21149) (by norm_num)
theorem B684341 : Blo 199806 684341 := bbase (se 5 (by rfl) ⟨32078, by rfl⟩ : syracuseStep 684341 = 64157) (by norm_num)
theorem B225625 : Blo 199806 225625 := bbase (se 2 (by rfl) ⟨84609, by rfl⟩ : syracuseStep 225625 = 169219) (by norm_num)
theorem B455021 : Blo 199806 455021 := bbase (se 3 (by rfl) ⟨85316, by rfl⟩ : syracuseStep 455021 = 170633) (by norm_num)
theorem B225661 : Blo 199806 225661 := bbase (se 3 (by rfl) ⟨42311, by rfl⟩ : syracuseStep 225661 = 84623) (by norm_num)
theorem B225697 : Blo 199806 225697 := bbase (se 2 (by rfl) ⟨84636, by rfl⟩ : syracuseStep 225697 = 169273) (by norm_num)
theorem B455093 : Blo 199806 455093 := bbase (se 5 (by rfl) ⟨21332, by rfl⟩ : syracuseStep 455093 = 42665) (by norm_num)
theorem B225733 : Blo 199806 225733 := bbase (se 4 (by rfl) ⟨21162, by rfl⟩ : syracuseStep 225733 = 42325) (by norm_num)
theorem B225769 : Blo 199806 225769 := bbase (se 2 (by rfl) ⟨84663, by rfl⟩ : syracuseStep 225769 = 169327) (by norm_num)
theorem B455165 : Blo 199806 455165 := bbase (se 3 (by rfl) ⟨85343, by rfl⟩ : syracuseStep 455165 = 170687) (by norm_num)
theorem B487949 : Blo 199806 487949 := bbase (se 3 (by rfl) ⟨91490, by rfl⟩ : syracuseStep 487949 = 182981) (by norm_num)
theorem B225805 : Blo 199806 225805 := bbase (se 3 (by rfl) ⟨42338, by rfl⟩ : syracuseStep 225805 = 84677) (by norm_num)
theorem B225841 : Blo 199806 225841 := bbase (se 2 (by rfl) ⟨84690, by rfl⟩ : syracuseStep 225841 = 169381) (by norm_num)
theorem B455237 : Blo 199806 455237 := bbase (se 4 (by rfl) ⟨42678, by rfl⟩ : syracuseStep 455237 = 85357) (by norm_num)
theorem B225877 : Blo 199806 225877 := bbase (se 8 (by rfl) ⟨1323, by rfl⟩ : syracuseStep 225877 = 2647) (by norm_num)
theorem B815717 : Blo 199806 815717 := bbase (se 4 (by rfl) ⟨76473, by rfl⟩ : syracuseStep 815717 = 152947) (by norm_num)
theorem B225913 : Blo 199806 225913 := bbase (se 2 (by rfl) ⟨84717, by rfl⟩ : syracuseStep 225913 = 169435) (by norm_num)
theorem B455309 : Blo 199806 455309 := bbase (se 3 (by rfl) ⟨85370, by rfl⟩ : syracuseStep 455309 = 170741) (by norm_num)
theorem B225949 : Blo 199806 225949 := bbase (se 3 (by rfl) ⟨42365, by rfl⟩ : syracuseStep 225949 = 84731) (by norm_num)
theorem B225985 : Blo 199806 225985 := bbase (se 2 (by rfl) ⟨84744, by rfl⟩ : syracuseStep 225985 = 169489) (by norm_num)
theorem B455381 : Blo 199806 455381 := bbase (se 7 (by rfl) ⟨5336, by rfl⟩ : syracuseStep 455381 = 10673) (by norm_num)
theorem B651989 : Blo 199806 651989 := bbase (se 7 (by rfl) ⟨7640, by rfl⟩ : syracuseStep 651989 = 15281) (by norm_num)
theorem B226021 : Blo 199806 226021 := bbase (se 4 (by rfl) ⟨21189, by rfl⟩ : syracuseStep 226021 = 42379) (by norm_num)
theorem B684773 : Blo 199806 684773 := bbase (se 4 (by rfl) ⟨64197, by rfl⟩ : syracuseStep 684773 = 128395) (by norm_num)
theorem B226057 : Blo 199806 226057 := bbase (se 2 (by rfl) ⟨84771, by rfl⟩ : syracuseStep 226057 = 169543) (by norm_num)
theorem B455453 : Blo 199806 455453 := bbase (se 3 (by rfl) ⟨85397, by rfl⟩ : syracuseStep 455453 = 170795) (by norm_num)
theorem B226093 : Blo 199806 226093 := bbase (se 3 (by rfl) ⟨42392, by rfl⟩ : syracuseStep 226093 = 84785) (by norm_num)
theorem B226129 : Blo 199806 226129 := bbase (se 2 (by rfl) ⟨84798, by rfl⟩ : syracuseStep 226129 = 169597) (by norm_num)
theorem B2290517 : Blo 199806 2290517 := bbase (se 9 (by rfl) ⟨6710, by rfl⟩ : syracuseStep 2290517 = 13421) (by norm_num)
theorem B455525 : Blo 199806 455525 := bbase (se 4 (by rfl) ⟨42705, by rfl⟩ : syracuseStep 455525 = 85411) (by norm_num)
theorem B226165 : Blo 199806 226165 := bbase (se 5 (by rfl) ⟨10601, by rfl⟩ : syracuseStep 226165 = 21203) (by norm_num)
theorem B226201 : Blo 199806 226201 := bbase (se 2 (by rfl) ⟨84825, by rfl⟩ : syracuseStep 226201 = 169651) (by norm_num)
theorem B455597 : Blo 199806 455597 := bbase (se 3 (by rfl) ⟨85424, by rfl⟩ : syracuseStep 455597 = 170849) (by norm_num)
theorem B1012661 : Blo 199806 1012661 := bbase (se 5 (by rfl) ⟨47468, by rfl⟩ : syracuseStep 1012661 = 94937) (by norm_num)
theorem B226237 : Blo 199806 226237 := bbase (se 3 (by rfl) ⟨42419, by rfl⟩ : syracuseStep 226237 = 84839) (by norm_num)
theorem B226273 : Blo 199806 226273 := bbase (se 2 (by rfl) ⟨84852, by rfl⟩ : syracuseStep 226273 = 169705) (by norm_num)
theorem B455669 : Blo 199806 455669 := bbase (se 5 (by rfl) ⟨21359, by rfl⟩ : syracuseStep 455669 = 42719) (by norm_num)
theorem B226309 : Blo 199806 226309 := bbase (se 4 (by rfl) ⟨21216, by rfl⟩ : syracuseStep 226309 = 42433) (by norm_num)
theorem B226345 : Blo 199806 226345 := bbase (se 2 (by rfl) ⟨84879, by rfl⟩ : syracuseStep 226345 = 169759) (by norm_num)
theorem B1373237 : Blo 199806 1373237 := bbase (se 5 (by rfl) ⟨64370, by rfl⟩ : syracuseStep 1373237 = 128741) (by norm_num)
theorem B488501 : Blo 199806 488501 := bbase (se 5 (by rfl) ⟨22898, by rfl⟩ : syracuseStep 488501 = 45797) (by norm_num)
theorem B455741 : Blo 199806 455741 := bbase (se 3 (by rfl) ⟨85451, by rfl⟩ : syracuseStep 455741 = 170903) (by norm_num)
theorem B226381 : Blo 199806 226381 := bbase (se 3 (by rfl) ⟨42446, by rfl⟩ : syracuseStep 226381 = 84893) (by norm_num)
theorem B226417 : Blo 199806 226417 := bbase (se 2 (by rfl) ⟨84906, by rfl⟩ : syracuseStep 226417 = 169813) (by norm_num)
theorem B455813 : Blo 199806 455813 := bbase (se 4 (by rfl) ⟨42732, by rfl⟩ : syracuseStep 455813 = 85465) (by norm_num)
theorem B226453 : Blo 199806 226453 := bbase (se 6 (by rfl) ⟨5307, by rfl⟩ : syracuseStep 226453 = 10615) (by norm_num)
theorem B685205 : Blo 199806 685205 := bbase (se 6 (by rfl) ⟨16059, by rfl⟩ : syracuseStep 685205 = 32119) (by norm_num)
theorem B226489 : Blo 199806 226489 := bbase (se 2 (by rfl) ⟨84933, by rfl⟩ : syracuseStep 226489 = 169867) (by norm_num)
theorem B455885 : Blo 199806 455885 := bbase (se 3 (by rfl) ⟨85478, by rfl⟩ : syracuseStep 455885 = 170957) (by norm_num)
theorem B324821 : Blo 199806 324821 := bbase (se 7 (by rfl) ⟨3806, by rfl⟩ : syracuseStep 324821 = 7613) (by norm_num)
theorem B226525 : Blo 199806 226525 := bbase (se 3 (by rfl) ⟨42473, by rfl⟩ : syracuseStep 226525 = 84947) (by norm_num)
theorem B292069 : Blo 199806 292069 := bbase (se 4 (by rfl) ⟨27381, by rfl⟩ : syracuseStep 292069 = 54763) (by norm_num)
theorem B226561 : Blo 199806 226561 := bbase (se 2 (by rfl) ⟨84960, by rfl⟩ : syracuseStep 226561 = 169921) (by norm_num)
theorem B455957 : Blo 199806 455957 := bbase (se 6 (by rfl) ⟨10686, by rfl⟩ : syracuseStep 455957 = 21373) (by norm_num)
theorem B226597 : Blo 199806 226597 := bbase (se 4 (by rfl) ⟨21243, by rfl⟩ : syracuseStep 226597 = 42487) (by norm_num)
theorem B226633 : Blo 199806 226633 := bbase (se 2 (by rfl) ⟨84987, by rfl⟩ : syracuseStep 226633 = 169975) (by norm_num)
theorem B456029 : Blo 199806 456029 := bbase (se 3 (by rfl) ⟨85505, by rfl⟩ : syracuseStep 456029 = 171011) (by norm_num)
theorem B226669 : Blo 199806 226669 := bbase (se 3 (by rfl) ⟨42500, by rfl⟩ : syracuseStep 226669 = 85001) (by norm_num)
theorem B226705 : Blo 199806 226705 := bbase (se 2 (by rfl) ⟨85014, by rfl⟩ : syracuseStep 226705 = 170029) (by norm_num)
theorem B456101 : Blo 199806 456101 := bbase (se 4 (by rfl) ⟨42759, by rfl⟩ : syracuseStep 456101 = 85519) (by norm_num)
theorem B226741 : Blo 199806 226741 := bbase (se 5 (by rfl) ⟨10628, by rfl⟩ : syracuseStep 226741 = 21257) (by norm_num)
theorem B226777 : Blo 199806 226777 := bbase (se 2 (by rfl) ⟨85041, by rfl⟩ : syracuseStep 226777 = 170083) (by norm_num)
theorem B456173 : Blo 199806 456173 := bbase (se 3 (by rfl) ⟨85532, by rfl⟩ : syracuseStep 456173 = 171065) (by norm_num)
theorem B226813 : Blo 199806 226813 := bbase (se 3 (by rfl) ⟨42527, by rfl⟩ : syracuseStep 226813 = 85055) (by norm_num)
theorem B226849 : Blo 199806 226849 := bbase (se 2 (by rfl) ⟨85068, by rfl⟩ : syracuseStep 226849 = 170137) (by norm_num)
theorem B292405 : Blo 199806 292405 := bbase (se 5 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 292405 = 27413) (by norm_num)
theorem B456245 : Blo 199806 456245 := bbase (se 5 (by rfl) ⟨21386, by rfl⟩ : syracuseStep 456245 = 42773) (by norm_num)
theorem B226885 : Blo 199806 226885 := bbase (se 4 (by rfl) ⟨21270, by rfl⟩ : syracuseStep 226885 = 42541) (by norm_num)
theorem B685637 : Blo 199806 685637 := bbase (se 4 (by rfl) ⟨64278, by rfl⟩ : syracuseStep 685637 = 128557) (by norm_num)
theorem B226921 : Blo 199806 226921 := bbase (se 2 (by rfl) ⟨85095, by rfl⟩ : syracuseStep 226921 = 170191) (by norm_num)
theorem B456317 : Blo 199806 456317 := bbase (se 3 (by rfl) ⟨85559, by rfl⟩ : syracuseStep 456317 = 171119) (by norm_num)
theorem B226957 : Blo 199806 226957 := bbase (se 3 (by rfl) ⟨42554, by rfl⟩ : syracuseStep 226957 = 85109) (by norm_num)
theorem B226993 : Blo 199806 226993 := bbase (se 2 (by rfl) ⟨85122, by rfl⟩ : syracuseStep 226993 = 170245) (by norm_num)
theorem B259781 : Blo 199806 259781 := bbase (se 4 (by rfl) ⟨24354, by rfl⟩ : syracuseStep 259781 = 48709) (by norm_num)
theorem B456389 : Blo 199806 456389 := bbase (se 4 (by rfl) ⟨42786, by rfl⟩ : syracuseStep 456389 = 85573) (by norm_num)
theorem B227029 : Blo 199806 227029 := bbase (se 7 (by rfl) ⟨2660, by rfl⟩ : syracuseStep 227029 = 5321) (by norm_num)
theorem B227065 : Blo 199806 227065 := bbase (se 2 (by rfl) ⟨85149, by rfl⟩ : syracuseStep 227065 = 170299) (by norm_num)
theorem B456461 : Blo 199806 456461 := bbase (se 3 (by rfl) ⟨85586, by rfl⟩ : syracuseStep 456461 = 171173) (by norm_num)
theorem B227101 : Blo 199806 227101 := bbase (se 3 (by rfl) ⟨42581, by rfl⟩ : syracuseStep 227101 = 85163) (by norm_num)
theorem B587557 : Blo 199806 587557 := bbase (se 4 (by rfl) ⟨55083, by rfl⟩ : syracuseStep 587557 = 110167) (by norm_num)
theorem B227137 : Blo 199806 227137 := bbase (se 2 (by rfl) ⟨85176, by rfl⟩ : syracuseStep 227137 = 170353) (by norm_num)
theorem B456533 : Blo 199806 456533 := bbase (se 9 (by rfl) ⟨1337, by rfl⟩ : syracuseStep 456533 = 2675) (by norm_num)
theorem B227173 : Blo 199806 227173 := bbase (se 4 (by rfl) ⟨21297, by rfl⟩ : syracuseStep 227173 = 42595) (by norm_num)
theorem B227209 : Blo 199806 227209 := bbase (se 2 (by rfl) ⟨85203, by rfl⟩ : syracuseStep 227209 = 170407) (by norm_num)
theorem B456605 : Blo 199806 456605 := bbase (se 3 (by rfl) ⟨85613, by rfl⟩ : syracuseStep 456605 = 171227) (by norm_num)
theorem B227245 : Blo 199806 227245 := bbase (se 3 (by rfl) ⟨42608, by rfl⟩ : syracuseStep 227245 = 85217) (by norm_num)
theorem B456653 : Blo 199806 456653 := bbase (se 3 (by rfl) ⟨85622, by rfl⟩ : syracuseStep 456653 = 171245) (by norm_num)
theorem B227281 : Blo 199806 227281 := bbase (se 2 (by rfl) ⟨85230, by rfl⟩ : syracuseStep 227281 = 170461) (by norm_num)
theorem B456677 : Blo 199806 456677 := bbase (se 4 (by rfl) ⟨42813, by rfl⟩ : syracuseStep 456677 = 85627) (by norm_num)
theorem B227317 : Blo 199806 227317 := bbase (se 5 (by rfl) ⟨10655, by rfl⟩ : syracuseStep 227317 = 21311) (by norm_num)
theorem B686069 : Blo 199806 686069 := bbase (se 5 (by rfl) ⟨32159, by rfl⟩ : syracuseStep 686069 = 64319) (by norm_num)
theorem B489461 : Blo 199806 489461 := bbase (se 5 (by rfl) ⟨22943, by rfl⟩ : syracuseStep 489461 = 45887) (by norm_num)
theorem B227353 : Blo 199806 227353 := bbase (se 2 (by rfl) ⟨85257, by rfl⟩ : syracuseStep 227353 = 170515) (by norm_num)
theorem B456749 : Blo 199806 456749 := bbase (se 3 (by rfl) ⟨85640, by rfl⟩ : syracuseStep 456749 = 171281) (by norm_num)
theorem B227389 : Blo 199806 227389 := bbase (se 3 (by rfl) ⟨42635, by rfl⟩ : syracuseStep 227389 = 85271) (by norm_num)
theorem B227425 : Blo 199806 227425 := bbase (se 2 (by rfl) ⟨85284, by rfl⟩ : syracuseStep 227425 = 170569) (by norm_num)
theorem B456821 : Blo 199806 456821 := bbase (se 5 (by rfl) ⟨21413, by rfl⟩ : syracuseStep 456821 = 42827) (by norm_num)
theorem B325757 : Blo 199806 325757 := bbase (se 3 (by rfl) ⟨61079, by rfl⟩ : syracuseStep 325757 = 122159) (by norm_num)
theorem B227461 : Blo 199806 227461 := bbase (se 4 (by rfl) ⟨21324, by rfl⟩ : syracuseStep 227461 = 42649) (by norm_num)
theorem B227497 : Blo 199806 227497 := bbase (se 2 (by rfl) ⟨85311, by rfl⟩ : syracuseStep 227497 = 170623) (by norm_num)
theorem B456893 : Blo 199806 456893 := bbase (se 3 (by rfl) ⟨85667, by rfl⟩ : syracuseStep 456893 = 171335) (by norm_num)
theorem B1013957 : Blo 199806 1013957 := bbase (se 4 (by rfl) ⟨95058, by rfl⟩ : syracuseStep 1013957 = 190117) (by norm_num)
theorem B227533 : Blo 199806 227533 := bbase (se 3 (by rfl) ⟨42662, by rfl⟩ : syracuseStep 227533 = 85325) (by norm_num)
theorem B227569 : Blo 199806 227569 := bbase (se 2 (by rfl) ⟨85338, by rfl⟩ : syracuseStep 227569 = 170677) (by norm_num)
theorem B456965 : Blo 199806 456965 := bbase (se 4 (by rfl) ⟨42840, by rfl⟩ : syracuseStep 456965 = 85681) (by norm_num)
theorem B227605 : Blo 199806 227605 := bbase (se 6 (by rfl) ⟨5334, by rfl⟩ : syracuseStep 227605 = 10669) (by norm_num)
theorem B260377 : Blo 199806 260377 := bbase (se 2 (by rfl) ⟨97641, by rfl⟩ : syracuseStep 260377 = 195283) (by norm_num)
theorem B227641 : Blo 199806 227641 := bbase (se 2 (by rfl) ⟨85365, by rfl⟩ : syracuseStep 227641 = 170731) (by norm_num)
theorem B457037 : Blo 199806 457037 := bbase (se 3 (by rfl) ⟨85694, by rfl⟩ : syracuseStep 457037 = 171389) (by norm_num)
theorem B1603925 : Blo 199806 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B227677 : Blo 199806 227677 := bbase (se 3 (by rfl) ⟨42689, by rfl⟩ : syracuseStep 227677 = 85379) (by norm_num)
theorem B227713 : Blo 199806 227713 := bbase (se 2 (by rfl) ⟨85392, by rfl⟩ : syracuseStep 227713 = 170785) (by norm_num)
theorem B457109 : Blo 199806 457109 := bbase (se 6 (by rfl) ⟨10713, by rfl⟩ : syracuseStep 457109 = 21427) (by norm_num)
theorem B227749 : Blo 199806 227749 := bbase (se 4 (by rfl) ⟨21351, by rfl⟩ : syracuseStep 227749 = 42703) (by norm_num)
theorem B686501 : Blo 199806 686501 := bbase (se 4 (by rfl) ⟨64359, by rfl⟩ : syracuseStep 686501 = 128719) (by norm_num)
theorem B227785 : Blo 199806 227785 := bbase (se 2 (by rfl) ⟨85419, by rfl⟩ : syracuseStep 227785 = 170839) (by norm_num)
theorem B457181 : Blo 199806 457181 := bbase (se 3 (by rfl) ⟨85721, by rfl⟩ : syracuseStep 457181 = 171443) (by norm_num)
theorem B227821 : Blo 199806 227821 := bbase (se 3 (by rfl) ⟨42716, by rfl⟩ : syracuseStep 227821 = 85433) (by norm_num)
theorem B227857 : Blo 199806 227857 := bbase (se 2 (by rfl) ⟨85446, by rfl⟩ : syracuseStep 227857 = 170893) (by norm_num)
theorem B457253 : Blo 199806 457253 := bbase (se 4 (by rfl) ⟨42867, by rfl⟩ : syracuseStep 457253 = 85735) (by norm_num)
theorem B227893 : Blo 199806 227893 := bbase (se 5 (by rfl) ⟨10682, by rfl⟩ : syracuseStep 227893 = 21365) (by norm_num)
theorem B227929 : Blo 199806 227929 := bbase (se 2 (by rfl) ⟨85473, by rfl⟩ : syracuseStep 227929 = 170947) (by norm_num)
theorem B457325 : Blo 199806 457325 := bbase (se 3 (by rfl) ⟨85748, by rfl⟩ : syracuseStep 457325 = 171497) (by norm_num)
theorem B227965 : Blo 199806 227965 := bbase (se 3 (by rfl) ⟨42743, by rfl⟩ : syracuseStep 227965 = 85487) (by norm_num)
theorem B228001 : Blo 199806 228001 := bbase (se 2 (by rfl) ⟨85500, by rfl⟩ : syracuseStep 228001 = 171001) (by norm_num)
theorem B457397 : Blo 199806 457397 := bbase (se 5 (by rfl) ⟨21440, by rfl⟩ : syracuseStep 457397 = 42881) (by norm_num)
theorem B228037 : Blo 199806 228037 := bbase (se 4 (by rfl) ⟨21378, by rfl⟩ : syracuseStep 228037 = 42757) (by norm_num)
theorem B228053 : Blo 199806 228053 := bbase (se 7 (by rfl) ⟨2672, by rfl⟩ : syracuseStep 228053 = 5345) (by norm_num)
theorem B228073 : Blo 199806 228073 := bbase (se 2 (by rfl) ⟨85527, by rfl⟩ : syracuseStep 228073 = 171055) (by norm_num)
theorem B457469 : Blo 199806 457469 := bbase (se 3 (by rfl) ⟨85775, by rfl⟩ : syracuseStep 457469 = 171551) (by norm_num)
theorem B326405 : Blo 199806 326405 := bbase (se 4 (by rfl) ⟨30600, by rfl⟩ : syracuseStep 326405 = 61201) (by norm_num)
theorem B228109 : Blo 199806 228109 := bbase (se 3 (by rfl) ⟨42770, by rfl⟩ : syracuseStep 228109 = 85541) (by norm_num)
theorem B1178389 : Blo 199806 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B228145 : Blo 199806 228145 := bbase (se 2 (by rfl) ⟨85554, by rfl⟩ : syracuseStep 228145 = 171109) (by norm_num)
theorem B457541 : Blo 199806 457541 := bbase (se 4 (by rfl) ⟨42894, by rfl⟩ : syracuseStep 457541 = 85789) (by norm_num)
theorem B228181 : Blo 199806 228181 := bbase (se 9 (by rfl) ⟨668, by rfl⟩ : syracuseStep 228181 = 1337) (by norm_num)
theorem B686933 : Blo 199806 686933 := bbase (se 9 (by rfl) ⟨2012, by rfl⟩ : syracuseStep 686933 = 4025) (by norm_num)
theorem B228217 : Blo 199806 228217 := bbase (se 2 (by rfl) ⟨85581, by rfl⟩ : syracuseStep 228217 = 171163) (by norm_num)
theorem B457613 : Blo 199806 457613 := bbase (se 3 (by rfl) ⟨85802, by rfl⟩ : syracuseStep 457613 = 171605) (by norm_num)
theorem B293773 : Blo 199806 293773 := bbase (se 3 (by rfl) ⟨55082, by rfl⟩ : syracuseStep 293773 = 110165) (by norm_num)
theorem B228253 : Blo 199806 228253 := bbase (se 3 (by rfl) ⟨42797, by rfl⟩ : syracuseStep 228253 = 85595) (by norm_num)
theorem B228289 : Blo 199806 228289 := bbase (se 2 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 228289 = 171217) (by norm_num)
theorem B457685 : Blo 199806 457685 := bbase (se 7 (by rfl) ⟨5363, by rfl⟩ : syracuseStep 457685 = 10727) (by norm_num)
theorem B228325 : Blo 199806 228325 := bbase (se 4 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 228325 = 42811) (by norm_num)
theorem B228361 : Blo 199806 228361 := bbase (se 2 (by rfl) ⟨85635, by rfl⟩ : syracuseStep 228361 = 171271) (by norm_num)
theorem B326669 : Blo 199806 326669 := bbase (se 3 (by rfl) ⟨61250, by rfl⟩ : syracuseStep 326669 = 122501) (by norm_num)
theorem B457757 : Blo 199806 457757 := bbase (se 3 (by rfl) ⟨85829, by rfl⟩ : syracuseStep 457757 = 171659) (by norm_num)
theorem B293917 : Blo 199806 293917 := bbase (se 3 (by rfl) ⟨55109, by rfl⟩ : syracuseStep 293917 = 110219) (by norm_num)
theorem B228397 : Blo 199806 228397 := bbase (se 3 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 228397 = 85649) (by norm_num)
theorem B228433 : Blo 199806 228433 := bbase (se 2 (by rfl) ⟨85662, by rfl⟩ : syracuseStep 228433 = 171325) (by norm_num)
theorem B457829 : Blo 199806 457829 := bbase (se 4 (by rfl) ⟨42921, by rfl⟩ : syracuseStep 457829 = 85843) (by norm_num)
theorem B228469 : Blo 199806 228469 := bbase (se 5 (by rfl) ⟨10709, by rfl⟩ : syracuseStep 228469 = 21419) (by norm_num)
theorem B228505 : Blo 199806 228505 := bbase (se 2 (by rfl) ⟨85689, by rfl⟩ : syracuseStep 228505 = 171379) (by norm_num)
theorem B457901 : Blo 199806 457901 := bbase (se 3 (by rfl) ⟨85856, by rfl⟩ : syracuseStep 457901 = 171713) (by norm_num)
theorem B228541 : Blo 199806 228541 := bbase (se 3 (by rfl) ⟨42851, by rfl⟩ : syracuseStep 228541 = 85703) (by norm_num)
theorem B228577 : Blo 199806 228577 := bbase (se 2 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 228577 = 171433) (by norm_num)
theorem B457973 : Blo 199806 457973 := bbase (se 5 (by rfl) ⟨21467, by rfl⟩ : syracuseStep 457973 = 42935) (by norm_num)
theorem B228613 : Blo 199806 228613 := bbase (se 4 (by rfl) ⟨21432, by rfl⟩ : syracuseStep 228613 = 42865) (by norm_num)
theorem B687365 : Blo 199806 687365 := bbase (se 4 (by rfl) ⟨64440, by rfl⟩ : syracuseStep 687365 = 128881) (by norm_num)
theorem B228649 : Blo 199806 228649 := bbase (se 2 (by rfl) ⟨85743, by rfl⟩ : syracuseStep 228649 = 171487) (by norm_num)
theorem B458045 : Blo 199806 458045 := bbase (se 3 (by rfl) ⟨85883, by rfl⟩ : syracuseStep 458045 = 171767) (by norm_num)
theorem B228685 : Blo 199806 228685 := bbase (se 3 (by rfl) ⟨42878, by rfl⟩ : syracuseStep 228685 = 85757) (by norm_num)
theorem B228721 : Blo 199806 228721 := bbase (se 2 (by rfl) ⟨85770, by rfl⟩ : syracuseStep 228721 = 171541) (by norm_num)
theorem B458117 : Blo 199806 458117 := bbase (se 4 (by rfl) ⟨42948, by rfl⟩ : syracuseStep 458117 = 85897) (by norm_num)
theorem B228757 : Blo 199806 228757 := bbase (se 6 (by rfl) ⟨5361, by rfl⟩ : syracuseStep 228757 = 10723) (by norm_num)
theorem B228793 : Blo 199806 228793 := bbase (se 2 (by rfl) ⟨85797, by rfl⟩ : syracuseStep 228793 = 171595) (by norm_num)
theorem B458189 : Blo 199806 458189 := bbase (se 3 (by rfl) ⟨85910, by rfl⟩ : syracuseStep 458189 = 171821) (by norm_num)
theorem B1015253 : Blo 199806 1015253 := bbase (se 7 (by rfl) ⟨11897, by rfl⟩ : syracuseStep 1015253 = 23795) (by norm_num)
theorem B228829 : Blo 199806 228829 := bbase (se 3 (by rfl) ⟨42905, by rfl⟩ : syracuseStep 228829 = 85811) (by norm_num)
theorem B228865 : Blo 199806 228865 := bbase (se 2 (by rfl) ⟨85824, by rfl⟩ : syracuseStep 228865 = 171649) (by norm_num)
theorem B458261 : Blo 199806 458261 := bbase (se 6 (by rfl) ⟨10740, by rfl⟩ : syracuseStep 458261 = 21481) (by norm_num)
theorem B228901 : Blo 199806 228901 := bbase (se 4 (by rfl) ⟨21459, by rfl⟩ : syracuseStep 228901 = 42919) (by norm_num)
theorem B228937 : Blo 199806 228937 := bbase (se 2 (by rfl) ⟨85851, by rfl⟩ : syracuseStep 228937 = 171703) (by norm_num)
theorem B458333 : Blo 199806 458333 := bbase (se 3 (by rfl) ⟨85937, by rfl⟩ : syracuseStep 458333 = 171875) (by norm_num)
theorem B228973 : Blo 199806 228973 := bbase (se 3 (by rfl) ⟨42932, by rfl⟩ : syracuseStep 228973 = 85865) (by norm_num)
theorem B327293 : Blo 199806 327293 := bbase (se 3 (by rfl) ⟨61367, by rfl⟩ : syracuseStep 327293 = 122735) (by norm_num)
theorem B229001 : Blo 199806 229001 := bbase (se 2 (by rfl) ⟨85875, by rfl⟩ : syracuseStep 229001 = 171751) (by norm_num)
theorem B229009 : Blo 199806 229009 := bbase (se 2 (by rfl) ⟨85878, by rfl⟩ : syracuseStep 229009 = 171757) (by norm_num)
theorem B458405 : Blo 199806 458405 := bbase (se 4 (by rfl) ⟨42975, by rfl⟩ : syracuseStep 458405 = 85951) (by norm_num)
theorem B229045 : Blo 199806 229045 := bbase (se 5 (by rfl) ⟨10736, by rfl⟩ : syracuseStep 229045 = 21473) (by norm_num)
theorem B687797 : Blo 199806 687797 := bbase (se 5 (by rfl) ⟨32240, by rfl⟩ : syracuseStep 687797 = 64481) (by norm_num)
theorem B1146581 : Blo 199806 1146581 := bbase (se 7 (by rfl) ⟨13436, by rfl⟩ : syracuseStep 1146581 = 26873) (by norm_num)
theorem B229081 : Blo 199806 229081 := bbase (se 2 (by rfl) ⟨85905, by rfl⟩ : syracuseStep 229081 = 171811) (by norm_num)
theorem B458477 : Blo 199806 458477 := bbase (se 3 (by rfl) ⟨85964, by rfl⟩ : syracuseStep 458477 = 171929) (by norm_num)
theorem B229117 : Blo 199806 229117 := bbase (se 3 (by rfl) ⟨42959, by rfl⟩ : syracuseStep 229117 = 85919) (by norm_num)
theorem B229153 : Blo 199806 229153 := bbase (se 2 (by rfl) ⟨85932, by rfl⟩ : syracuseStep 229153 = 171865) (by norm_num)
theorem B458549 : Blo 199806 458549 := bbase (se 5 (by rfl) ⟨21494, by rfl⟩ : syracuseStep 458549 = 42989) (by norm_num)
theorem B229189 : Blo 199806 229189 := bbase (se 4 (by rfl) ⟨21486, by rfl⟩ : syracuseStep 229189 = 42973) (by norm_num)
theorem B1408853 : Blo 199806 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B229225 : Blo 199806 229225 := bbase (se 2 (by rfl) ⟨85959, by rfl⟩ : syracuseStep 229225 = 171919) (by norm_num)
theorem B229261 : Blo 199806 229261 := bbase (se 3 (by rfl) ⟨42986, by rfl⟩ : syracuseStep 229261 = 85973) (by norm_num)
theorem B1310833 : Blo 199806 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B229603 : Blo 199806 229603 := bstep (se 1 (by rfl) ⟨172202, by rfl⟩ : syracuseStep 229603 = 344405) B344405
theorem B361265 : Blo 199806 361265 := bstep (se 2 (by rfl) ⟨135474, by rfl⟩ : syracuseStep 361265 = 270949) B270949
theorem B1737571 : Blo 199806 1737571 := bstep (se 1 (by rfl) ⟨1303178, by rfl⟩ : syracuseStep 1737571 = 2606357) B2606357
theorem B426961 : Blo 199806 426961 := bstep (se 2 (by rfl) ⟨160110, by rfl⟩ : syracuseStep 426961 = 320221) B320221
theorem B1541105 : Blo 199806 1541105 := bstep (se 2 (by rfl) ⟨577914, by rfl⟩ : syracuseStep 1541105 = 1155829) B1155829
theorem B230515 : Blo 199806 230515 := bstep (se 1 (by rfl) ⟨172886, by rfl⟩ : syracuseStep 230515 = 345773) B345773
theorem B361763 : Blo 199806 361763 := bstep (se 1 (by rfl) ⟨271322, by rfl⟩ : syracuseStep 361763 = 542645) B542645
theorem B460081 : Blo 199806 460081 := bstep (se 2 (by rfl) ⟨172530, by rfl⟩ : syracuseStep 460081 = 345061) B345061
theorem B1148357 : Blo 199806 1148357 := bstep (se 4 (by rfl) ⟨107658, by rfl⟩ : syracuseStep 1148357 = 215317) B215317
theorem B1312291 : Blo 199806 1312291 := bstep (se 1 (by rfl) ⟨984218, by rfl⟩ : syracuseStep 1312291 = 1968437) B1968437
theorem B427619 : Blo 199806 427619 := bstep (se 1 (by rfl) ⟨320714, by rfl⟩ : syracuseStep 427619 = 641429) B641429
theorem B1017521 : Blo 199806 1017521 := bstep (se 2 (by rfl) ⟨381570, by rfl⟩ : syracuseStep 1017521 = 763141) B763141
theorem B362225 : Blo 199806 362225 := bstep (se 2 (by rfl) ⟨135834, by rfl⟩ : syracuseStep 362225 = 271669) B271669
theorem B526115 : Blo 199806 526115 := bstep (se 1 (by rfl) ⟨394586, by rfl⟩ : syracuseStep 526115 = 789173) B789173
theorem B1148813 : Blo 199806 1148813 := bstep (se 3 (by rfl) ⟨215402, by rfl⟩ : syracuseStep 1148813 = 430805) B430805
theorem B329665 : Blo 199806 329665 := bstep (se 2 (by rfl) ⟨123624, by rfl⟩ : syracuseStep 329665 = 247249) B247249
theorem B362801 : Blo 199806 362801 := bstep (se 2 (by rfl) ⟨136050, by rfl⟩ : syracuseStep 362801 = 272101) B272101
theorem B428465 : Blo 199806 428465 := bstep (se 2 (by rfl) ⟨160674, by rfl⟩ : syracuseStep 428465 = 321349) B321349
theorem B461315 : Blo 199806 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B1018979 : Blo 199806 1018979 := bstep (se 1 (by rfl) ⟨764234, by rfl⟩ : syracuseStep 1018979 = 1528469) B1528469
theorem B199811 : Blo 199806 199811 := bstep (se 1 (by rfl) ⟨149858, by rfl⟩ : syracuseStep 199811 = 299717) B299717
theorem B199827 : Blo 199806 199827 := bstep (se 1 (by rfl) ⟨149870, by rfl⟩ : syracuseStep 199827 = 299741) B299741
theorem B199843 : Blo 199806 199843 := bstep (se 1 (by rfl) ⟨149882, by rfl⟩ : syracuseStep 199843 = 299765) B299765
theorem B822449 : Blo 199806 822449 := bstep (se 2 (by rfl) ⟨308418, by rfl⟩ : syracuseStep 822449 = 616837) B616837
theorem B199859 : Blo 199806 199859 := bstep (se 1 (by rfl) ⟨149894, by rfl⟩ : syracuseStep 199859 = 299789) B299789
theorem B199875 : Blo 199806 199875 := bstep (se 1 (by rfl) ⟨149906, by rfl⟩ : syracuseStep 199875 = 299813) B299813
theorem B199891 : Blo 199806 199891 := bstep (se 1 (by rfl) ⟨149918, by rfl⟩ : syracuseStep 199891 = 299837) B299837
theorem B199907 : Blo 199806 199907 := bstep (se 1 (by rfl) ⟨149930, by rfl⟩ : syracuseStep 199907 = 299861) B299861
theorem B199923 : Blo 199806 199923 := bstep (se 1 (by rfl) ⟨149942, by rfl⟩ : syracuseStep 199923 = 299885) B299885
theorem B199939 : Blo 199806 199939 := bstep (se 1 (by rfl) ⟨149954, by rfl⟩ : syracuseStep 199939 = 299909) B299909
theorem B199955 : Blo 199806 199955 := bstep (se 1 (by rfl) ⟨149966, by rfl⟩ : syracuseStep 199955 = 299933) B299933
theorem B199971 : Blo 199806 199971 := bstep (se 1 (by rfl) ⟨149978, by rfl⟩ : syracuseStep 199971 = 299957) B299957
theorem B199987 : Blo 199806 199987 := bstep (se 1 (by rfl) ⟨149990, by rfl⟩ : syracuseStep 199987 = 299981) B299981
theorem B200003 : Blo 199806 200003 := bstep (se 1 (by rfl) ⟨150002, by rfl⟩ : syracuseStep 200003 = 300005) B300005
theorem B200019 : Blo 199806 200019 := bstep (se 1 (by rfl) ⟨150014, by rfl⟩ : syracuseStep 200019 = 300029) B300029
theorem B200035 : Blo 199806 200035 := bstep (se 1 (by rfl) ⟨150026, by rfl⟩ : syracuseStep 200035 = 300053) B300053
theorem B200051 : Blo 199806 200051 := bstep (se 1 (by rfl) ⟨150038, by rfl⟩ : syracuseStep 200051 = 300077) B300077
theorem B200067 : Blo 199806 200067 := bstep (se 1 (by rfl) ⟨150050, by rfl⟩ : syracuseStep 200067 = 300101) B300101
theorem B200083 : Blo 199806 200083 := bstep (se 1 (by rfl) ⟨150062, by rfl⟩ : syracuseStep 200083 = 300125) B300125
theorem B200099 : Blo 199806 200099 := bstep (se 1 (by rfl) ⟨150074, by rfl⟩ : syracuseStep 200099 = 300149) B300149
theorem B200115 : Blo 199806 200115 := bstep (se 1 (by rfl) ⟨150086, by rfl⟩ : syracuseStep 200115 = 300173) B300173
theorem B200131 : Blo 199806 200131 := bstep (se 1 (by rfl) ⟨150098, by rfl⟩ : syracuseStep 200131 = 300197) B300197
theorem B200147 : Blo 199806 200147 := bstep (se 1 (by rfl) ⟨150110, by rfl⟩ : syracuseStep 200147 = 300221) B300221
theorem B200163 : Blo 199806 200163 := bstep (se 1 (by rfl) ⟨150122, by rfl⟩ : syracuseStep 200163 = 300245) B300245
theorem B658925 : Blo 199806 658925 := bstep (se 3 (by rfl) ⟨123548, by rfl⟩ : syracuseStep 658925 = 247097) B247097
theorem B200179 : Blo 199806 200179 := bstep (se 1 (by rfl) ⟨150134, by rfl⟩ : syracuseStep 200179 = 300269) B300269
theorem B200195 : Blo 199806 200195 := bstep (se 1 (by rfl) ⟨150146, by rfl⟩ : syracuseStep 200195 = 300293) B300293
theorem B200211 : Blo 199806 200211 := bstep (se 1 (by rfl) ⟨150158, by rfl⟩ : syracuseStep 200211 = 300317) B300317
theorem B200227 : Blo 199806 200227 := bstep (se 1 (by rfl) ⟨150170, by rfl⟩ : syracuseStep 200227 = 300341) B300341
theorem B200243 : Blo 199806 200243 := bstep (se 1 (by rfl) ⟨150182, by rfl⟩ : syracuseStep 200243 = 300365) B300365
theorem B200259 : Blo 199806 200259 := bstep (se 1 (by rfl) ⟨150194, by rfl⟩ : syracuseStep 200259 = 300389) B300389
theorem B200275 : Blo 199806 200275 := bstep (se 1 (by rfl) ⟨150206, by rfl⟩ : syracuseStep 200275 = 300413) B300413
theorem B200291 : Blo 199806 200291 := bstep (se 1 (by rfl) ⟨150218, by rfl⟩ : syracuseStep 200291 = 300437) B300437
theorem B200307 : Blo 199806 200307 := bstep (se 1 (by rfl) ⟨150230, by rfl⟩ : syracuseStep 200307 = 300461) B300461
theorem B200323 : Blo 199806 200323 := bstep (se 1 (by rfl) ⟨150242, by rfl⟩ : syracuseStep 200323 = 300485) B300485
theorem B200339 : Blo 199806 200339 := bstep (se 1 (by rfl) ⟨150254, by rfl⟩ : syracuseStep 200339 = 300509) B300509
theorem B200355 : Blo 199806 200355 := bstep (se 1 (by rfl) ⟨150266, by rfl⟩ : syracuseStep 200355 = 300533) B300533
theorem B200371 : Blo 199806 200371 := bstep (se 1 (by rfl) ⟨150278, by rfl⟩ : syracuseStep 200371 = 300557) B300557
theorem B200387 : Blo 199806 200387 := bstep (se 1 (by rfl) ⟨150290, by rfl⟩ : syracuseStep 200387 = 300581) B300581
theorem B200403 : Blo 199806 200403 := bstep (se 1 (by rfl) ⟨150302, by rfl⟩ : syracuseStep 200403 = 300605) B300605
theorem B200419 : Blo 199806 200419 := bstep (se 1 (by rfl) ⟨150314, by rfl⟩ : syracuseStep 200419 = 300629) B300629
theorem B200435 : Blo 199806 200435 := bstep (se 1 (by rfl) ⟨150326, by rfl⟩ : syracuseStep 200435 = 300653) B300653
theorem B200451 : Blo 199806 200451 := bstep (se 1 (by rfl) ⟨150338, by rfl⟩ : syracuseStep 200451 = 300677) B300677
theorem B200467 : Blo 199806 200467 := bstep (se 1 (by rfl) ⟨150350, by rfl⟩ : syracuseStep 200467 = 300701) B300701
theorem B200483 : Blo 199806 200483 := bstep (se 1 (by rfl) ⟨150362, by rfl⟩ : syracuseStep 200483 = 300725) B300725
theorem B200499 : Blo 199806 200499 := bstep (se 1 (by rfl) ⟨150374, by rfl⟩ : syracuseStep 200499 = 300749) B300749
theorem B200515 : Blo 199806 200515 := bstep (se 1 (by rfl) ⟨150386, by rfl⟩ : syracuseStep 200515 = 300773) B300773
theorem B200531 : Blo 199806 200531 := bstep (se 1 (by rfl) ⟨150398, by rfl⟩ : syracuseStep 200531 = 300797) B300797
theorem B200547 : Blo 199806 200547 := bstep (se 1 (by rfl) ⟨150410, by rfl⟩ : syracuseStep 200547 = 300821) B300821
theorem B200563 : Blo 199806 200563 := bstep (se 1 (by rfl) ⟨150422, by rfl⟩ : syracuseStep 200563 = 300845) B300845
theorem B200579 : Blo 199806 200579 := bstep (se 1 (by rfl) ⟨150434, by rfl⟩ : syracuseStep 200579 = 300869) B300869
theorem B1019789 : Blo 199806 1019789 := bstep (se 3 (by rfl) ⟨191210, by rfl⟩ : syracuseStep 1019789 = 382421) B382421
theorem B200595 : Blo 199806 200595 := bstep (se 1 (by rfl) ⟨150446, by rfl⟩ : syracuseStep 200595 = 300893) B300893
theorem B200611 : Blo 199806 200611 := bstep (se 1 (by rfl) ⟨150458, by rfl⟩ : syracuseStep 200611 = 300917) B300917
theorem B200627 : Blo 199806 200627 := bstep (se 1 (by rfl) ⟨150470, by rfl⟩ : syracuseStep 200627 = 300941) B300941
theorem B200643 : Blo 199806 200643 := bstep (se 1 (by rfl) ⟨150482, by rfl⟩ : syracuseStep 200643 = 300965) B300965
theorem B200659 : Blo 199806 200659 := bstep (se 1 (by rfl) ⟨150494, by rfl⟩ : syracuseStep 200659 = 300989) B300989
theorem B200675 : Blo 199806 200675 := bstep (se 1 (by rfl) ⟨150506, by rfl⟩ : syracuseStep 200675 = 301013) B301013
theorem B200691 : Blo 199806 200691 := bstep (se 1 (by rfl) ⟨150518, by rfl⟩ : syracuseStep 200691 = 301037) B301037
theorem B200707 : Blo 199806 200707 := bstep (se 1 (by rfl) ⟨150530, by rfl⟩ : syracuseStep 200707 = 301061) B301061
theorem B1282061 : Blo 199806 1282061 := bstep (se 3 (by rfl) ⟨240386, by rfl⟩ : syracuseStep 1282061 = 480773) B480773
theorem B200723 : Blo 199806 200723 := bstep (se 1 (by rfl) ⟨150542, by rfl⟩ : syracuseStep 200723 = 301085) B301085
theorem B200739 : Blo 199806 200739 := bstep (se 1 (by rfl) ⟨150554, by rfl⟩ : syracuseStep 200739 = 301109) B301109
theorem B200755 : Blo 199806 200755 := bstep (se 1 (by rfl) ⟨150566, by rfl⟩ : syracuseStep 200755 = 301133) B301133
theorem B200771 : Blo 199806 200771 := bstep (se 1 (by rfl) ⟨150578, by rfl⟩ : syracuseStep 200771 = 301157) B301157
theorem B200787 : Blo 199806 200787 := bstep (se 1 (by rfl) ⟨150590, by rfl⟩ : syracuseStep 200787 = 301181) B301181
theorem B200803 : Blo 199806 200803 := bstep (se 1 (by rfl) ⟨150602, by rfl⟩ : syracuseStep 200803 = 301205) B301205
theorem B200819 : Blo 199806 200819 := bstep (se 1 (by rfl) ⟨150614, by rfl⟩ : syracuseStep 200819 = 301229) B301229
theorem B200835 : Blo 199806 200835 := bstep (se 1 (by rfl) ⟨150626, by rfl⟩ : syracuseStep 200835 = 301253) B301253
theorem B200851 : Blo 199806 200851 := bstep (se 1 (by rfl) ⟨150638, by rfl⟩ : syracuseStep 200851 = 301277) B301277
theorem B200867 : Blo 199806 200867 := bstep (se 1 (by rfl) ⟨150650, by rfl⟩ : syracuseStep 200867 = 301301) B301301
theorem B200883 : Blo 199806 200883 := bstep (se 1 (by rfl) ⟨150662, by rfl⟩ : syracuseStep 200883 = 301325) B301325
theorem B200899 : Blo 199806 200899 := bstep (se 1 (by rfl) ⟨150674, by rfl⟩ : syracuseStep 200899 = 301349) B301349
theorem B200915 : Blo 199806 200915 := bstep (se 1 (by rfl) ⟨150686, by rfl⟩ : syracuseStep 200915 = 301373) B301373
theorem B200931 : Blo 199806 200931 := bstep (se 1 (by rfl) ⟨150698, by rfl⟩ : syracuseStep 200931 = 301397) B301397
theorem B200947 : Blo 199806 200947 := bstep (se 1 (by rfl) ⟨150710, by rfl⟩ : syracuseStep 200947 = 301421) B301421
theorem B200963 : Blo 199806 200963 := bstep (se 1 (by rfl) ⟨150722, by rfl⟩ : syracuseStep 200963 = 301445) B301445
theorem B200979 : Blo 199806 200979 := bstep (se 1 (by rfl) ⟨150734, by rfl⟩ : syracuseStep 200979 = 301469) B301469
theorem B200995 : Blo 199806 200995 := bstep (se 1 (by rfl) ⟨150746, by rfl⟩ : syracuseStep 200995 = 301493) B301493
theorem B201011 : Blo 199806 201011 := bstep (se 1 (by rfl) ⟨150758, by rfl⟩ : syracuseStep 201011 = 301517) B301517
theorem B201027 : Blo 199806 201027 := bstep (se 1 (by rfl) ⟨150770, by rfl⟩ : syracuseStep 201027 = 301541) B301541
theorem B201043 : Blo 199806 201043 := bstep (se 1 (by rfl) ⟨150782, by rfl⟩ : syracuseStep 201043 = 301565) B301565
theorem B201059 : Blo 199806 201059 := bstep (se 1 (by rfl) ⟨150794, by rfl⟩ : syracuseStep 201059 = 301589) B301589
theorem B201075 : Blo 199806 201075 := bstep (se 1 (by rfl) ⟨150806, by rfl⟩ : syracuseStep 201075 = 301613) B301613
theorem B201091 : Blo 199806 201091 := bstep (se 1 (by rfl) ⟨150818, by rfl⟩ : syracuseStep 201091 = 301637) B301637
theorem B201107 : Blo 199806 201107 := bstep (se 1 (by rfl) ⟨150830, by rfl⟩ : syracuseStep 201107 = 301661) B301661
theorem B201123 : Blo 199806 201123 := bstep (se 1 (by rfl) ⟨150842, by rfl⟩ : syracuseStep 201123 = 301685) B301685
theorem B201139 : Blo 199806 201139 := bstep (se 1 (by rfl) ⟨150854, by rfl⟩ : syracuseStep 201139 = 301709) B301709
theorem B201155 : Blo 199806 201155 := bstep (se 1 (by rfl) ⟨150866, by rfl⟩ : syracuseStep 201155 = 301733) B301733
theorem B201171 : Blo 199806 201171 := bstep (se 1 (by rfl) ⟨150878, by rfl⟩ : syracuseStep 201171 = 301757) B301757
theorem B201187 : Blo 199806 201187 := bstep (se 1 (by rfl) ⟨150890, by rfl⟩ : syracuseStep 201187 = 301781) B301781
theorem B201203 : Blo 199806 201203 := bstep (se 1 (by rfl) ⟨150902, by rfl⟩ : syracuseStep 201203 = 301805) B301805
theorem B201219 : Blo 199806 201219 := bstep (se 1 (by rfl) ⟨150914, by rfl⟩ : syracuseStep 201219 = 301829) B301829
theorem B692749 : Blo 199806 692749 := bstep (se 3 (by rfl) ⟨129890, by rfl⟩ : syracuseStep 692749 = 259781) B259781
theorem B201235 : Blo 199806 201235 := bstep (se 1 (by rfl) ⟨150926, by rfl⟩ : syracuseStep 201235 = 301853) B301853
theorem B201251 : Blo 199806 201251 := bstep (se 1 (by rfl) ⟨150938, by rfl⟩ : syracuseStep 201251 = 301877) B301877
theorem B201267 : Blo 199806 201267 := bstep (se 1 (by rfl) ⟨150950, by rfl⟩ : syracuseStep 201267 = 301901) B301901
theorem B201283 : Blo 199806 201283 := bstep (se 1 (by rfl) ⟨150962, by rfl⟩ : syracuseStep 201283 = 301925) B301925
theorem B201299 : Blo 199806 201299 := bstep (se 1 (by rfl) ⟨150974, by rfl⟩ : syracuseStep 201299 = 301949) B301949
theorem B201315 : Blo 199806 201315 := bstep (se 1 (by rfl) ⟨150986, by rfl⟩ : syracuseStep 201315 = 301973) B301973
theorem B201331 : Blo 199806 201331 := bstep (se 1 (by rfl) ⟨150998, by rfl⟩ : syracuseStep 201331 = 301997) B301997
theorem B201347 : Blo 199806 201347 := bstep (se 1 (by rfl) ⟨151010, by rfl⟩ : syracuseStep 201347 = 302021) B302021
theorem B201363 : Blo 199806 201363 := bstep (se 1 (by rfl) ⟨151022, by rfl⟩ : syracuseStep 201363 = 302045) B302045
theorem B201379 : Blo 199806 201379 := bstep (se 1 (by rfl) ⟨151034, by rfl⟩ : syracuseStep 201379 = 302069) B302069
theorem B201395 : Blo 199806 201395 := bstep (se 1 (by rfl) ⟨151046, by rfl⟩ : syracuseStep 201395 = 302093) B302093
theorem B201411 : Blo 199806 201411 := bstep (se 1 (by rfl) ⟨151058, by rfl⟩ : syracuseStep 201411 = 302117) B302117
theorem B365251 : Blo 199806 365251 := bstep (se 1 (by rfl) ⟨273938, by rfl⟩ : syracuseStep 365251 = 547877) B547877
theorem B299729 : Blo 199806 299729 := bstep (se 2 (by rfl) ⟨112398, by rfl⟩ : syracuseStep 299729 = 224797) B224797
theorem B201427 : Blo 199806 201427 := bstep (se 1 (by rfl) ⟨151070, by rfl⟩ : syracuseStep 201427 = 302141) B302141
theorem B299747 : Blo 199806 299747 := bstep (se 1 (by rfl) ⟨224810, by rfl⟩ : syracuseStep 299747 = 449621) B449621
theorem B201443 : Blo 199806 201443 := bstep (se 1 (by rfl) ⟨151082, by rfl⟩ : syracuseStep 201443 = 302165) B302165
theorem B1938161 : Blo 199806 1938161 := bstep (se 2 (by rfl) ⟨726810, by rfl⟩ : syracuseStep 1938161 = 1453621) B1453621
theorem B1151729 : Blo 199806 1151729 := bstep (se 2 (by rfl) ⟨431898, by rfl⟩ : syracuseStep 1151729 = 863797) B863797
theorem B201459 : Blo 199806 201459 := bstep (se 1 (by rfl) ⟨151094, by rfl⟩ : syracuseStep 201459 = 302189) B302189
theorem B299777 : Blo 199806 299777 := bstep (se 2 (by rfl) ⟨112416, by rfl⟩ : syracuseStep 299777 = 224833) B224833
theorem B201475 : Blo 199806 201475 := bstep (se 1 (by rfl) ⟨151106, by rfl⟩ : syracuseStep 201475 = 302213) B302213
theorem B725773 : Blo 199806 725773 := bstep (se 3 (by rfl) ⟨136082, by rfl⟩ : syracuseStep 725773 = 272165) B272165
theorem B299795 : Blo 199806 299795 := bstep (se 1 (by rfl) ⟨224846, by rfl⟩ : syracuseStep 299795 = 449693) B449693
theorem B201491 : Blo 199806 201491 := bstep (se 1 (by rfl) ⟨151118, by rfl⟩ : syracuseStep 201491 = 302237) B302237
theorem B201507 : Blo 199806 201507 := bstep (se 1 (by rfl) ⟨151130, by rfl⟩ : syracuseStep 201507 = 302261) B302261
theorem B299825 : Blo 199806 299825 := bstep (se 2 (by rfl) ⟨112434, by rfl⟩ : syracuseStep 299825 = 224869) B224869
theorem B201523 : Blo 199806 201523 := bstep (se 1 (by rfl) ⟨151142, by rfl⟩ : syracuseStep 201523 = 302285) B302285
theorem B299843 : Blo 199806 299843 := bstep (se 1 (by rfl) ⟨224882, by rfl⟩ : syracuseStep 299843 = 449765) B449765
theorem B201539 : Blo 199806 201539 := bstep (se 1 (by rfl) ⟨151154, by rfl⟩ : syracuseStep 201539 = 302309) B302309
theorem B201555 : Blo 199806 201555 := bstep (se 1 (by rfl) ⟨151166, by rfl⟩ : syracuseStep 201555 = 302333) B302333
theorem B299873 : Blo 199806 299873 := bstep (se 2 (by rfl) ⟨112452, by rfl⟩ : syracuseStep 299873 = 224905) B224905
theorem B201571 : Blo 199806 201571 := bstep (se 1 (by rfl) ⟨151178, by rfl⟩ : syracuseStep 201571 = 302357) B302357
theorem B299891 : Blo 199806 299891 := bstep (se 1 (by rfl) ⟨224918, by rfl⟩ : syracuseStep 299891 = 449837) B449837
theorem B201587 : Blo 199806 201587 := bstep (se 1 (by rfl) ⟨151190, by rfl⟩ : syracuseStep 201587 = 302381) B302381
theorem B201603 : Blo 199806 201603 := bstep (se 1 (by rfl) ⟨151202, by rfl⟩ : syracuseStep 201603 = 302405) B302405
theorem B299921 : Blo 199806 299921 := bstep (se 2 (by rfl) ⟨112470, by rfl⟩ : syracuseStep 299921 = 224941) B224941
theorem B201619 : Blo 199806 201619 := bstep (se 1 (by rfl) ⟨151214, by rfl⟩ : syracuseStep 201619 = 302429) B302429
theorem B299939 : Blo 199806 299939 := bstep (se 1 (by rfl) ⟨224954, by rfl⟩ : syracuseStep 299939 = 449909) B449909
theorem B201635 : Blo 199806 201635 := bstep (se 1 (by rfl) ⟨151226, by rfl⟩ : syracuseStep 201635 = 302453) B302453
theorem B201651 : Blo 199806 201651 := bstep (se 1 (by rfl) ⟨151238, by rfl⟩ : syracuseStep 201651 = 302477) B302477
theorem B299969 : Blo 199806 299969 := bstep (se 2 (by rfl) ⟨112488, by rfl⟩ : syracuseStep 299969 = 224977) B224977
theorem B201667 : Blo 199806 201667 := bstep (se 1 (by rfl) ⟨151250, by rfl⟩ : syracuseStep 201667 = 302501) B302501
theorem B660433 : Blo 199806 660433 := bstep (se 2 (by rfl) ⟨247662, by rfl⟩ : syracuseStep 660433 = 495325) B495325
theorem B299987 : Blo 199806 299987 := bstep (se 1 (by rfl) ⟨224990, by rfl⟩ : syracuseStep 299987 = 449981) B449981
theorem B201683 : Blo 199806 201683 := bstep (se 1 (by rfl) ⟨151262, by rfl⟩ : syracuseStep 201683 = 302525) B302525
theorem B201699 : Blo 199806 201699 := bstep (se 1 (by rfl) ⟨151274, by rfl⟩ : syracuseStep 201699 = 302549) B302549
theorem B300017 : Blo 199806 300017 := bstep (se 2 (by rfl) ⟨112506, by rfl⟩ : syracuseStep 300017 = 225013) B225013
theorem B201715 : Blo 199806 201715 := bstep (se 1 (by rfl) ⟨151286, by rfl⟩ : syracuseStep 201715 = 302573) B302573
theorem B300035 : Blo 199806 300035 := bstep (se 1 (by rfl) ⟨225026, by rfl⟩ : syracuseStep 300035 = 450053) B450053
theorem B201731 : Blo 199806 201731 := bstep (se 1 (by rfl) ⟨151298, by rfl⟩ : syracuseStep 201731 = 302597) B302597
theorem B201747 : Blo 199806 201747 := bstep (se 1 (by rfl) ⟨151310, by rfl⟩ : syracuseStep 201747 = 302621) B302621
theorem B300065 : Blo 199806 300065 := bstep (se 2 (by rfl) ⟨112524, by rfl⟩ : syracuseStep 300065 = 225049) B225049
theorem B201763 : Blo 199806 201763 := bstep (se 1 (by rfl) ⟨151322, by rfl⟩ : syracuseStep 201763 = 302645) B302645
theorem B300083 : Blo 199806 300083 := bstep (se 1 (by rfl) ⟨225062, by rfl⟩ : syracuseStep 300083 = 450125) B450125
theorem B201779 : Blo 199806 201779 := bstep (se 1 (by rfl) ⟨151334, by rfl⟩ : syracuseStep 201779 = 302669) B302669
theorem B201795 : Blo 199806 201795 := bstep (se 1 (by rfl) ⟨151346, by rfl⟩ : syracuseStep 201795 = 302693) B302693
theorem B300113 : Blo 199806 300113 := bstep (se 2 (by rfl) ⟨112542, by rfl⟩ : syracuseStep 300113 = 225085) B225085
theorem B201811 : Blo 199806 201811 := bstep (se 1 (by rfl) ⟨151358, by rfl⟩ : syracuseStep 201811 = 302717) B302717
theorem B300131 : Blo 199806 300131 := bstep (se 1 (by rfl) ⟨225098, by rfl⟩ : syracuseStep 300131 = 450197) B450197
theorem B201827 : Blo 199806 201827 := bstep (se 1 (by rfl) ⟨151370, by rfl⟩ : syracuseStep 201827 = 302741) B302741
theorem B201843 : Blo 199806 201843 := bstep (se 1 (by rfl) ⟨151382, by rfl⟩ : syracuseStep 201843 = 302765) B302765
theorem B300161 : Blo 199806 300161 := bstep (se 2 (by rfl) ⟨112560, by rfl⟩ : syracuseStep 300161 = 225121) B225121
theorem B201859 : Blo 199806 201859 := bstep (se 1 (by rfl) ⟨151394, by rfl⟩ : syracuseStep 201859 = 302789) B302789
theorem B431249 : Blo 199806 431249 := bstep (se 2 (by rfl) ⟨161718, by rfl⟩ : syracuseStep 431249 = 323437) B323437
theorem B300179 : Blo 199806 300179 := bstep (se 1 (by rfl) ⟨225134, by rfl⟩ : syracuseStep 300179 = 450269) B450269
theorem B201875 : Blo 199806 201875 := bstep (se 1 (by rfl) ⟨151406, by rfl⟩ : syracuseStep 201875 = 302813) B302813
theorem B201891 : Blo 199806 201891 := bstep (se 1 (by rfl) ⟨151418, by rfl⟩ : syracuseStep 201891 = 302837) B302837
theorem B300209 : Blo 199806 300209 := bstep (se 2 (by rfl) ⟨112578, by rfl⟩ : syracuseStep 300209 = 225157) B225157
theorem B201907 : Blo 199806 201907 := bstep (se 1 (by rfl) ⟨151430, by rfl⟩ : syracuseStep 201907 = 302861) B302861
theorem B300227 : Blo 199806 300227 := bstep (se 1 (by rfl) ⟨225170, by rfl⟩ : syracuseStep 300227 = 450341) B450341
theorem B201923 : Blo 199806 201923 := bstep (se 1 (by rfl) ⟨151442, by rfl⟩ : syracuseStep 201923 = 302885) B302885
theorem B726221 : Blo 199806 726221 := bstep (se 3 (by rfl) ⟨136166, by rfl⟩ : syracuseStep 726221 = 272333) B272333
theorem B201939 : Blo 199806 201939 := bstep (se 1 (by rfl) ⟨151454, by rfl⟩ : syracuseStep 201939 = 302909) B302909
theorem B300257 : Blo 199806 300257 := bstep (se 2 (by rfl) ⟨112596, by rfl⟩ : syracuseStep 300257 = 225193) B225193
theorem B201955 : Blo 199806 201955 := bstep (se 1 (by rfl) ⟨151466, by rfl⟩ : syracuseStep 201955 = 302933) B302933
theorem B300275 : Blo 199806 300275 := bstep (se 1 (by rfl) ⟨225206, by rfl⟩ : syracuseStep 300275 = 450413) B450413
theorem B201971 : Blo 199806 201971 := bstep (se 1 (by rfl) ⟨151478, by rfl⟩ : syracuseStep 201971 = 302957) B302957
theorem B201987 : Blo 199806 201987 := bstep (se 1 (by rfl) ⟨151490, by rfl⟩ : syracuseStep 201987 = 302981) B302981
theorem B300305 : Blo 199806 300305 := bstep (se 2 (by rfl) ⟨112614, by rfl⟩ : syracuseStep 300305 = 225229) B225229
theorem B202003 : Blo 199806 202003 := bstep (se 1 (by rfl) ⟨151502, by rfl⟩ : syracuseStep 202003 = 303005) B303005
theorem B300323 : Blo 199806 300323 := bstep (se 1 (by rfl) ⟨225242, by rfl⟩ : syracuseStep 300323 = 450485) B450485
theorem B202019 : Blo 199806 202019 := bstep (se 1 (by rfl) ⟨151514, by rfl⟩ : syracuseStep 202019 = 303029) B303029
theorem B202035 : Blo 199806 202035 := bstep (se 1 (by rfl) ⟨151526, by rfl⟩ : syracuseStep 202035 = 303053) B303053
theorem B300353 : Blo 199806 300353 := bstep (se 2 (by rfl) ⟨112632, by rfl⟩ : syracuseStep 300353 = 225265) B225265
theorem B202051 : Blo 199806 202051 := bstep (se 1 (by rfl) ⟨151538, by rfl⟩ : syracuseStep 202051 = 303077) B303077
theorem B300371 : Blo 199806 300371 := bstep (se 1 (by rfl) ⟨225278, by rfl⟩ : syracuseStep 300371 = 450557) B450557
theorem B202067 : Blo 199806 202067 := bstep (se 1 (by rfl) ⟨151550, by rfl⟩ : syracuseStep 202067 = 303101) B303101
theorem B202083 : Blo 199806 202083 := bstep (se 1 (by rfl) ⟨151562, by rfl⟩ : syracuseStep 202083 = 303125) B303125
theorem B300401 : Blo 199806 300401 := bstep (se 2 (by rfl) ⟨112650, by rfl⟩ : syracuseStep 300401 = 225301) B225301
theorem B202099 : Blo 199806 202099 := bstep (se 1 (by rfl) ⟨151574, by rfl⟩ : syracuseStep 202099 = 303149) B303149
theorem B300419 : Blo 199806 300419 := bstep (se 1 (by rfl) ⟨225314, by rfl⟩ : syracuseStep 300419 = 450629) B450629
theorem B202115 : Blo 199806 202115 := bstep (se 1 (by rfl) ⟨151586, by rfl⟩ : syracuseStep 202115 = 303173) B303173
theorem B3478925 : Blo 199806 3478925 := bstep (se 3 (by rfl) ⟨652298, by rfl⟩ : syracuseStep 3478925 = 1304597) B1304597
theorem B202131 : Blo 199806 202131 := bstep (se 1 (by rfl) ⟨151598, by rfl⟩ : syracuseStep 202131 = 303197) B303197
theorem B300449 : Blo 199806 300449 := bstep (se 2 (by rfl) ⟨112668, by rfl⟩ : syracuseStep 300449 = 225337) B225337
theorem B202147 : Blo 199806 202147 := bstep (se 1 (by rfl) ⟨151610, by rfl⟩ : syracuseStep 202147 = 303221) B303221
theorem B300467 : Blo 199806 300467 := bstep (se 1 (by rfl) ⟨225350, by rfl⟩ : syracuseStep 300467 = 450701) B450701
theorem B202163 : Blo 199806 202163 := bstep (se 1 (by rfl) ⟨151622, by rfl⟩ : syracuseStep 202163 = 303245) B303245
theorem B202179 : Blo 199806 202179 := bstep (se 1 (by rfl) ⟨151634, by rfl⟩ : syracuseStep 202179 = 303269) B303269
theorem B300497 : Blo 199806 300497 := bstep (se 2 (by rfl) ⟨112686, by rfl⟩ : syracuseStep 300497 = 225373) B225373
theorem B202195 : Blo 199806 202195 := bstep (se 1 (by rfl) ⟨151646, by rfl⟩ : syracuseStep 202195 = 303293) B303293
theorem B300515 : Blo 199806 300515 := bstep (se 1 (by rfl) ⟨225386, by rfl⟩ : syracuseStep 300515 = 450773) B450773
theorem B202211 : Blo 199806 202211 := bstep (se 1 (by rfl) ⟨151658, by rfl⟩ : syracuseStep 202211 = 303317) B303317
theorem B202227 : Blo 199806 202227 := bstep (se 1 (by rfl) ⟨151670, by rfl⟩ : syracuseStep 202227 = 303341) B303341
theorem B300545 : Blo 199806 300545 := bstep (se 2 (by rfl) ⟨112704, by rfl⟩ : syracuseStep 300545 = 225409) B225409
theorem B202243 : Blo 199806 202243 := bstep (se 1 (by rfl) ⟨151682, by rfl⟩ : syracuseStep 202243 = 303365) B303365
theorem B300563 : Blo 199806 300563 := bstep (se 1 (by rfl) ⟨225422, by rfl⟩ : syracuseStep 300563 = 450845) B450845
theorem B202259 : Blo 199806 202259 := bstep (se 1 (by rfl) ⟨151694, by rfl⟩ : syracuseStep 202259 = 303389) B303389
theorem B202275 : Blo 199806 202275 := bstep (se 1 (by rfl) ⟨151706, by rfl⟩ : syracuseStep 202275 = 303413) B303413
theorem B300593 : Blo 199806 300593 := bstep (se 2 (by rfl) ⟨112722, by rfl⟩ : syracuseStep 300593 = 225445) B225445
theorem B202291 : Blo 199806 202291 := bstep (se 1 (by rfl) ⟨151718, by rfl⟩ : syracuseStep 202291 = 303437) B303437
theorem B300611 : Blo 199806 300611 := bstep (se 1 (by rfl) ⟨225458, by rfl⟩ : syracuseStep 300611 = 450917) B450917
theorem B202307 : Blo 199806 202307 := bstep (se 1 (by rfl) ⟨151730, by rfl⟩ : syracuseStep 202307 = 303461) B303461
theorem B202323 : Blo 199806 202323 := bstep (se 1 (by rfl) ⟨151742, by rfl⟩ : syracuseStep 202323 = 303485) B303485
theorem B300641 : Blo 199806 300641 := bstep (se 2 (by rfl) ⟨112740, by rfl⟩ : syracuseStep 300641 = 225481) B225481
theorem B857699 : Blo 199806 857699 := bstep (se 1 (by rfl) ⟨643274, by rfl⟩ : syracuseStep 857699 = 1286549) B1286549
theorem B202339 : Blo 199806 202339 := bstep (se 1 (by rfl) ⟨151754, by rfl⟩ : syracuseStep 202339 = 303509) B303509
theorem B300659 : Blo 199806 300659 := bstep (se 1 (by rfl) ⟨225494, by rfl⟩ : syracuseStep 300659 = 450989) B450989
theorem B202355 : Blo 199806 202355 := bstep (se 1 (by rfl) ⟨151766, by rfl⟩ : syracuseStep 202355 = 303533) B303533
theorem B202371 : Blo 199806 202371 := bstep (se 1 (by rfl) ⟨151778, by rfl⟩ : syracuseStep 202371 = 303557) B303557
theorem B1939085 : Blo 199806 1939085 := bstep (se 3 (by rfl) ⟨363578, by rfl⟩ : syracuseStep 1939085 = 727157) B727157
theorem B300689 : Blo 199806 300689 := bstep (se 2 (by rfl) ⟨112758, by rfl⟩ : syracuseStep 300689 = 225517) B225517
theorem B202387 : Blo 199806 202387 := bstep (se 1 (by rfl) ⟨151790, by rfl⟩ : syracuseStep 202387 = 303581) B303581
theorem B300707 : Blo 199806 300707 := bstep (se 1 (by rfl) ⟨225530, by rfl⟩ : syracuseStep 300707 = 451061) B451061
theorem B202403 : Blo 199806 202403 := bstep (se 1 (by rfl) ⟨151802, by rfl⟩ : syracuseStep 202403 = 303605) B303605
theorem B824995 : Blo 199806 824995 := bstep (se 1 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 824995 = 1237493) B1237493
theorem B202419 : Blo 199806 202419 := bstep (se 1 (by rfl) ⟨151814, by rfl⟩ : syracuseStep 202419 = 303629) B303629
theorem B300737 : Blo 199806 300737 := bstep (se 2 (by rfl) ⟨112776, by rfl⟩ : syracuseStep 300737 = 225553) B225553
theorem B202435 : Blo 199806 202435 := bstep (se 1 (by rfl) ⟨151826, by rfl⟩ : syracuseStep 202435 = 303653) B303653
theorem B300755 : Blo 199806 300755 := bstep (se 1 (by rfl) ⟨225566, by rfl⟩ : syracuseStep 300755 = 451133) B451133
theorem B202451 : Blo 199806 202451 := bstep (se 1 (by rfl) ⟨151838, by rfl⟩ : syracuseStep 202451 = 303677) B303677
theorem B202467 : Blo 199806 202467 := bstep (se 1 (by rfl) ⟨151850, by rfl⟩ : syracuseStep 202467 = 303701) B303701
theorem B300785 : Blo 199806 300785 := bstep (se 2 (by rfl) ⟨112794, by rfl⟩ : syracuseStep 300785 = 225589) B225589
theorem B202483 : Blo 199806 202483 := bstep (se 1 (by rfl) ⟨151862, by rfl⟩ : syracuseStep 202483 = 303725) B303725
theorem B300803 : Blo 199806 300803 := bstep (se 1 (by rfl) ⟨225602, by rfl⟩ : syracuseStep 300803 = 451205) B451205
theorem B202499 : Blo 199806 202499 := bstep (se 1 (by rfl) ⟨151874, by rfl⟩ : syracuseStep 202499 = 303749) B303749
theorem B202515 : Blo 199806 202515 := bstep (se 1 (by rfl) ⟨151886, by rfl⟩ : syracuseStep 202515 = 303773) B303773
theorem B300833 : Blo 199806 300833 := bstep (se 2 (by rfl) ⟨112812, by rfl⟩ : syracuseStep 300833 = 225625) B225625
theorem B202531 : Blo 199806 202531 := bstep (se 1 (by rfl) ⟨151898, by rfl⟩ : syracuseStep 202531 = 303797) B303797
theorem B300851 : Blo 199806 300851 := bstep (se 1 (by rfl) ⟨225638, by rfl⟩ : syracuseStep 300851 = 451277) B451277
theorem B202547 : Blo 199806 202547 := bstep (se 1 (by rfl) ⟨151910, by rfl⟩ : syracuseStep 202547 = 303821) B303821
theorem B202563 : Blo 199806 202563 := bstep (se 1 (by rfl) ⟨151922, by rfl⟩ : syracuseStep 202563 = 303845) B303845
theorem B300881 : Blo 199806 300881 := bstep (se 2 (by rfl) ⟨112830, by rfl⟩ : syracuseStep 300881 = 225661) B225661
theorem B202579 : Blo 199806 202579 := bstep (se 1 (by rfl) ⟨151934, by rfl⟩ : syracuseStep 202579 = 303869) B303869
theorem B300899 : Blo 199806 300899 := bstep (se 1 (by rfl) ⟨225674, by rfl⟩ : syracuseStep 300899 = 451349) B451349
theorem B202595 : Blo 199806 202595 := bstep (se 1 (by rfl) ⟨151946, by rfl⟩ : syracuseStep 202595 = 303893) B303893
theorem B202611 : Blo 199806 202611 := bstep (se 1 (by rfl) ⟨151958, by rfl⟩ : syracuseStep 202611 = 303917) B303917
theorem B300929 : Blo 199806 300929 := bstep (se 2 (by rfl) ⟨112848, by rfl⟩ : syracuseStep 300929 = 225697) B225697
theorem B202627 : Blo 199806 202627 := bstep (se 1 (by rfl) ⟨151970, by rfl⟩ : syracuseStep 202627 = 303941) B303941
theorem B300947 : Blo 199806 300947 := bstep (se 1 (by rfl) ⟨225710, by rfl⟩ : syracuseStep 300947 = 451421) B451421
theorem B202643 : Blo 199806 202643 := bstep (se 1 (by rfl) ⟨151982, by rfl⟩ : syracuseStep 202643 = 303965) B303965
theorem B202659 : Blo 199806 202659 := bstep (se 1 (by rfl) ⟨151994, by rfl⟩ : syracuseStep 202659 = 303989) B303989
theorem B300977 : Blo 199806 300977 := bstep (se 2 (by rfl) ⟨112866, by rfl⟩ : syracuseStep 300977 = 225733) B225733
theorem B202675 : Blo 199806 202675 := bstep (se 1 (by rfl) ⟨152006, by rfl⟩ : syracuseStep 202675 = 304013) B304013
theorem B300995 : Blo 199806 300995 := bstep (se 1 (by rfl) ⟨225746, by rfl⟩ : syracuseStep 300995 = 451493) B451493
theorem B202691 : Blo 199806 202691 := bstep (se 1 (by rfl) ⟨152018, by rfl⟩ : syracuseStep 202691 = 304037) B304037
theorem B202707 : Blo 199806 202707 := bstep (se 1 (by rfl) ⟨152030, by rfl⟩ : syracuseStep 202707 = 304061) B304061
theorem B301025 : Blo 199806 301025 := bstep (se 2 (by rfl) ⟨112884, by rfl⟩ : syracuseStep 301025 = 225769) B225769
theorem B202723 : Blo 199806 202723 := bstep (se 1 (by rfl) ⟨152042, by rfl⟩ : syracuseStep 202723 = 304085) B304085
theorem B301043 : Blo 199806 301043 := bstep (se 1 (by rfl) ⟨225782, by rfl⟩ : syracuseStep 301043 = 451565) B451565
theorem B202739 : Blo 199806 202739 := bstep (se 1 (by rfl) ⟨152054, by rfl⟩ : syracuseStep 202739 = 304109) B304109
theorem B202755 : Blo 199806 202755 := bstep (se 1 (by rfl) ⟨152066, by rfl⟩ : syracuseStep 202755 = 304133) B304133
theorem B301073 : Blo 199806 301073 := bstep (se 2 (by rfl) ⟨112902, by rfl⟩ : syracuseStep 301073 = 225805) B225805
theorem B202771 : Blo 199806 202771 := bstep (se 1 (by rfl) ⟨152078, by rfl⟩ : syracuseStep 202771 = 304157) B304157
theorem B301091 : Blo 199806 301091 := bstep (se 1 (by rfl) ⟨225818, by rfl⟩ : syracuseStep 301091 = 451637) B451637
theorem B202787 : Blo 199806 202787 := bstep (se 1 (by rfl) ⟨152090, by rfl⟩ : syracuseStep 202787 = 304181) B304181
theorem B202803 : Blo 199806 202803 := bstep (se 1 (by rfl) ⟨152102, by rfl⟩ : syracuseStep 202803 = 304205) B304205
theorem B301121 : Blo 199806 301121 := bstep (se 2 (by rfl) ⟨112920, by rfl⟩ : syracuseStep 301121 = 225841) B225841
theorem B202819 : Blo 199806 202819 := bstep (se 1 (by rfl) ⟨152114, by rfl⟩ : syracuseStep 202819 = 304229) B304229
theorem B301139 : Blo 199806 301139 := bstep (se 1 (by rfl) ⟨225854, by rfl⟩ : syracuseStep 301139 = 451709) B451709
theorem B202835 : Blo 199806 202835 := bstep (se 1 (by rfl) ⟨152126, by rfl⟩ : syracuseStep 202835 = 304253) B304253
theorem B202851 : Blo 199806 202851 := bstep (se 1 (by rfl) ⟨152138, by rfl⟩ : syracuseStep 202851 = 304277) B304277
theorem B301169 : Blo 199806 301169 := bstep (se 2 (by rfl) ⟨112938, by rfl⟩ : syracuseStep 301169 = 225877) B225877
theorem B202867 : Blo 199806 202867 := bstep (se 1 (by rfl) ⟨152150, by rfl⟩ : syracuseStep 202867 = 304301) B304301
theorem B301187 : Blo 199806 301187 := bstep (se 1 (by rfl) ⟨225890, by rfl⟩ : syracuseStep 301187 = 451781) B451781
theorem B202883 : Blo 199806 202883 := bstep (se 1 (by rfl) ⟨152162, by rfl⟩ : syracuseStep 202883 = 304325) B304325
theorem B202899 : Blo 199806 202899 := bstep (se 1 (by rfl) ⟨152174, by rfl⟩ : syracuseStep 202899 = 304349) B304349
theorem B301217 : Blo 199806 301217 := bstep (se 2 (by rfl) ⟨112956, by rfl⟩ : syracuseStep 301217 = 225913) B225913
theorem B1153187 : Blo 199806 1153187 := bstep (se 1 (by rfl) ⟨864890, by rfl⟩ : syracuseStep 1153187 = 1729781) B1729781
theorem B202915 : Blo 199806 202915 := bstep (se 1 (by rfl) ⟨152186, by rfl⟩ : syracuseStep 202915 = 304373) B304373
theorem B727217 : Blo 199806 727217 := bstep (se 2 (by rfl) ⟨272706, by rfl⟩ : syracuseStep 727217 = 545413) B545413
theorem B301235 : Blo 199806 301235 := bstep (se 1 (by rfl) ⟨225926, by rfl⟩ : syracuseStep 301235 = 451853) B451853
theorem B202931 : Blo 199806 202931 := bstep (se 1 (by rfl) ⟨152198, by rfl⟩ : syracuseStep 202931 = 304397) B304397
theorem B202947 : Blo 199806 202947 := bstep (se 1 (by rfl) ⟨152210, by rfl⟩ : syracuseStep 202947 = 304421) B304421
theorem B760013 : Blo 199806 760013 := bstep (se 3 (by rfl) ⟨142502, by rfl⟩ : syracuseStep 760013 = 285005) B285005
theorem B301265 : Blo 199806 301265 := bstep (se 2 (by rfl) ⟨112974, by rfl⟩ : syracuseStep 301265 = 225949) B225949
theorem B202963 : Blo 199806 202963 := bstep (se 1 (by rfl) ⟨152222, by rfl⟩ : syracuseStep 202963 = 304445) B304445
theorem B301283 : Blo 199806 301283 := bstep (se 1 (by rfl) ⟨225962, by rfl⟩ : syracuseStep 301283 = 451925) B451925
theorem B202979 : Blo 199806 202979 := bstep (se 1 (by rfl) ⟨152234, by rfl⟩ : syracuseStep 202979 = 304469) B304469
theorem B202995 : Blo 199806 202995 := bstep (se 1 (by rfl) ⟨152246, by rfl⟩ : syracuseStep 202995 = 304493) B304493
theorem B301313 : Blo 199806 301313 := bstep (se 2 (by rfl) ⟨112992, by rfl⟩ : syracuseStep 301313 = 225985) B225985
theorem B203011 : Blo 199806 203011 := bstep (se 1 (by rfl) ⟨152258, by rfl⟩ : syracuseStep 203011 = 304517) B304517
theorem B301331 : Blo 199806 301331 := bstep (se 1 (by rfl) ⟨225998, by rfl⟩ : syracuseStep 301331 = 451997) B451997
theorem B203027 : Blo 199806 203027 := bstep (se 1 (by rfl) ⟨152270, by rfl⟩ : syracuseStep 203027 = 304541) B304541
theorem B203043 : Blo 199806 203043 := bstep (se 1 (by rfl) ⟨152282, by rfl⟩ : syracuseStep 203043 = 304565) B304565
theorem B301361 : Blo 199806 301361 := bstep (se 2 (by rfl) ⟨113010, by rfl⟩ : syracuseStep 301361 = 226021) B226021
theorem B203059 : Blo 199806 203059 := bstep (se 1 (by rfl) ⟨152294, by rfl⟩ : syracuseStep 203059 = 304589) B304589
theorem B301379 : Blo 199806 301379 := bstep (se 1 (by rfl) ⟨226034, by rfl⟩ : syracuseStep 301379 = 452069) B452069
theorem B203075 : Blo 199806 203075 := bstep (se 1 (by rfl) ⟨152306, by rfl⟩ : syracuseStep 203075 = 304613) B304613
theorem B203091 : Blo 199806 203091 := bstep (se 1 (by rfl) ⟨152318, by rfl⟩ : syracuseStep 203091 = 304637) B304637
theorem B301409 : Blo 199806 301409 := bstep (se 2 (by rfl) ⟨113028, by rfl⟩ : syracuseStep 301409 = 226057) B226057
theorem B203107 : Blo 199806 203107 := bstep (se 1 (by rfl) ⟨152330, by rfl⟩ : syracuseStep 203107 = 304661) B304661
theorem B301427 : Blo 199806 301427 := bstep (se 1 (by rfl) ⟨226070, by rfl⟩ : syracuseStep 301427 = 452141) B452141
theorem B203123 : Blo 199806 203123 := bstep (se 1 (by rfl) ⟨152342, by rfl⟩ : syracuseStep 203123 = 304685) B304685
theorem B203139 : Blo 199806 203139 := bstep (se 1 (by rfl) ⟨152354, by rfl⟩ : syracuseStep 203139 = 304709) B304709
theorem B301457 : Blo 199806 301457 := bstep (se 2 (by rfl) ⟨113046, by rfl⟩ : syracuseStep 301457 = 226093) B226093
theorem B203155 : Blo 199806 203155 := bstep (se 1 (by rfl) ⟨152366, by rfl⟩ : syracuseStep 203155 = 304733) B304733
theorem B301475 : Blo 199806 301475 := bstep (se 1 (by rfl) ⟨226106, by rfl⟩ : syracuseStep 301475 = 452213) B452213
theorem B203171 : Blo 199806 203171 := bstep (se 1 (by rfl) ⟨152378, by rfl⟩ : syracuseStep 203171 = 304757) B304757
theorem B203187 : Blo 199806 203187 := bstep (se 1 (by rfl) ⟨152390, by rfl⟩ : syracuseStep 203187 = 304781) B304781
theorem B301505 : Blo 199806 301505 := bstep (se 2 (by rfl) ⟨113064, by rfl⟩ : syracuseStep 301505 = 226129) B226129
theorem B203203 : Blo 199806 203203 := bstep (se 1 (by rfl) ⟨152402, by rfl⟩ : syracuseStep 203203 = 304805) B304805
theorem B301523 : Blo 199806 301523 := bstep (se 1 (by rfl) ⟨226142, by rfl⟩ : syracuseStep 301523 = 452285) B452285
theorem B203219 : Blo 199806 203219 := bstep (se 1 (by rfl) ⟨152414, by rfl⟩ : syracuseStep 203219 = 304829) B304829
theorem B203235 : Blo 199806 203235 := bstep (se 1 (by rfl) ⟨152426, by rfl⟩ : syracuseStep 203235 = 304853) B304853
theorem B301553 : Blo 199806 301553 := bstep (se 2 (by rfl) ⟨113082, by rfl⟩ : syracuseStep 301553 = 226165) B226165
theorem B203251 : Blo 199806 203251 := bstep (se 1 (by rfl) ⟨152438, by rfl⟩ : syracuseStep 203251 = 304877) B304877
theorem B301571 : Blo 199806 301571 := bstep (se 1 (by rfl) ⟨226178, by rfl⟩ : syracuseStep 301571 = 452357) B452357
theorem B203267 : Blo 199806 203267 := bstep (se 1 (by rfl) ⟨152450, by rfl⟩ : syracuseStep 203267 = 304901) B304901
theorem B203283 : Blo 199806 203283 := bstep (se 1 (by rfl) ⟨152462, by rfl⟩ : syracuseStep 203283 = 304925) B304925
theorem B301601 : Blo 199806 301601 := bstep (se 2 (by rfl) ⟨113100, by rfl⟩ : syracuseStep 301601 = 226201) B226201
theorem B203299 : Blo 199806 203299 := bstep (se 1 (by rfl) ⟨152474, by rfl⟩ : syracuseStep 203299 = 304949) B304949
theorem B301619 : Blo 199806 301619 := bstep (se 1 (by rfl) ⟨226214, by rfl⟩ : syracuseStep 301619 = 452429) B452429
theorem B203315 : Blo 199806 203315 := bstep (se 1 (by rfl) ⟨152486, by rfl⟩ : syracuseStep 203315 = 304973) B304973
theorem B203331 : Blo 199806 203331 := bstep (se 1 (by rfl) ⟨152498, by rfl⟩ : syracuseStep 203331 = 304997) B304997
theorem B301649 : Blo 199806 301649 := bstep (se 2 (by rfl) ⟨113118, by rfl⟩ : syracuseStep 301649 = 226237) B226237
theorem B203347 : Blo 199806 203347 := bstep (se 1 (by rfl) ⟨152510, by rfl⟩ : syracuseStep 203347 = 305021) B305021
theorem B301667 : Blo 199806 301667 := bstep (se 1 (by rfl) ⟨226250, by rfl⟩ : syracuseStep 301667 = 452501) B452501
theorem B203363 : Blo 199806 203363 := bstep (se 1 (by rfl) ⟨152522, by rfl⟩ : syracuseStep 203363 = 305045) B305045
theorem B203379 : Blo 199806 203379 := bstep (se 1 (by rfl) ⟨152534, by rfl⟩ : syracuseStep 203379 = 305069) B305069
theorem B301697 : Blo 199806 301697 := bstep (se 2 (by rfl) ⟨113136, by rfl⟩ : syracuseStep 301697 = 226273) B226273
theorem B203395 : Blo 199806 203395 := bstep (se 1 (by rfl) ⟨152546, by rfl⟩ : syracuseStep 203395 = 305093) B305093
theorem B301715 : Blo 199806 301715 := bstep (se 1 (by rfl) ⟨226286, by rfl⟩ : syracuseStep 301715 = 452573) B452573
theorem B203411 : Blo 199806 203411 := bstep (se 1 (by rfl) ⟨152558, by rfl⟩ : syracuseStep 203411 = 305117) B305117
theorem B203427 : Blo 199806 203427 := bstep (se 1 (by rfl) ⟨152570, by rfl⟩ : syracuseStep 203427 = 305141) B305141
theorem B301745 : Blo 199806 301745 := bstep (se 2 (by rfl) ⟨113154, by rfl⟩ : syracuseStep 301745 = 226309) B226309
theorem B203443 : Blo 199806 203443 := bstep (se 1 (by rfl) ⟨152582, by rfl⟩ : syracuseStep 203443 = 305165) B305165
theorem B301763 : Blo 199806 301763 := bstep (se 1 (by rfl) ⟨226322, by rfl⟩ : syracuseStep 301763 = 452645) B452645
theorem B203459 : Blo 199806 203459 := bstep (se 1 (by rfl) ⟨152594, by rfl⟩ : syracuseStep 203459 = 305189) B305189
theorem B203475 : Blo 199806 203475 := bstep (se 1 (by rfl) ⟨152606, by rfl⟩ : syracuseStep 203475 = 305213) B305213
theorem B301793 : Blo 199806 301793 := bstep (se 2 (by rfl) ⟨113172, by rfl⟩ : syracuseStep 301793 = 226345) B226345
theorem B203491 : Blo 199806 203491 := bstep (se 1 (by rfl) ⟨152618, by rfl⟩ : syracuseStep 203491 = 305237) B305237
theorem B1022705 : Blo 199806 1022705 := bstep (se 2 (by rfl) ⟨383514, by rfl⟩ : syracuseStep 1022705 = 767029) B767029
theorem B301811 : Blo 199806 301811 := bstep (se 1 (by rfl) ⟨226358, by rfl⟩ : syracuseStep 301811 = 452717) B452717
theorem B203507 : Blo 199806 203507 := bstep (se 1 (by rfl) ⟨152630, by rfl⟩ : syracuseStep 203507 = 305261) B305261
theorem B203523 : Blo 199806 203523 := bstep (se 1 (by rfl) ⟨152642, by rfl⟩ : syracuseStep 203523 = 305285) B305285
theorem B301841 : Blo 199806 301841 := bstep (se 2 (by rfl) ⟨113190, by rfl⟩ : syracuseStep 301841 = 226381) B226381
theorem B203539 : Blo 199806 203539 := bstep (se 1 (by rfl) ⟨152654, by rfl⟩ : syracuseStep 203539 = 305309) B305309
theorem B301859 : Blo 199806 301859 := bstep (se 1 (by rfl) ⟨226394, by rfl⟩ : syracuseStep 301859 = 452789) B452789
theorem B203555 : Blo 199806 203555 := bstep (se 1 (by rfl) ⟨152666, by rfl⟩ : syracuseStep 203555 = 305333) B305333
theorem B203571 : Blo 199806 203571 := bstep (se 1 (by rfl) ⟨152678, by rfl⟩ : syracuseStep 203571 = 305357) B305357
theorem B301889 : Blo 199806 301889 := bstep (se 2 (by rfl) ⟨113208, by rfl⟩ : syracuseStep 301889 = 226417) B226417
theorem B203587 : Blo 199806 203587 := bstep (se 1 (by rfl) ⟨152690, by rfl⟩ : syracuseStep 203587 = 305381) B305381
theorem B301907 : Blo 199806 301907 := bstep (se 1 (by rfl) ⟨226430, by rfl⟩ : syracuseStep 301907 = 452861) B452861
theorem B203603 : Blo 199806 203603 := bstep (se 1 (by rfl) ⟨152702, by rfl⟩ : syracuseStep 203603 = 305405) B305405
theorem B203619 : Blo 199806 203619 := bstep (se 1 (by rfl) ⟨152714, by rfl⟩ : syracuseStep 203619 = 305429) B305429
theorem B301937 : Blo 199806 301937 := bstep (se 2 (by rfl) ⟨113226, by rfl⟩ : syracuseStep 301937 = 226453) B226453
theorem B203635 : Blo 199806 203635 := bstep (se 1 (by rfl) ⟨152726, by rfl⟩ : syracuseStep 203635 = 305453) B305453
theorem B301955 : Blo 199806 301955 := bstep (se 1 (by rfl) ⟨226466, by rfl⟩ : syracuseStep 301955 = 452933) B452933
theorem B203651 : Blo 199806 203651 := bstep (se 1 (by rfl) ⟨152738, by rfl⟩ : syracuseStep 203651 = 305477) B305477
theorem B203667 : Blo 199806 203667 := bstep (se 1 (by rfl) ⟨152750, by rfl⟩ : syracuseStep 203667 = 305501) B305501
theorem B301985 : Blo 199806 301985 := bstep (se 2 (by rfl) ⟨113244, by rfl⟩ : syracuseStep 301985 = 226489) B226489
theorem B203683 : Blo 199806 203683 := bstep (se 1 (by rfl) ⟨152762, by rfl⟩ : syracuseStep 203683 = 305525) B305525
theorem B302003 : Blo 199806 302003 := bstep (se 1 (by rfl) ⟨226502, by rfl⟩ : syracuseStep 302003 = 453005) B453005
theorem B203699 : Blo 199806 203699 := bstep (se 1 (by rfl) ⟨152774, by rfl⟩ : syracuseStep 203699 = 305549) B305549
theorem B203715 : Blo 199806 203715 := bstep (se 1 (by rfl) ⟨152786, by rfl⟩ : syracuseStep 203715 = 305573) B305573
theorem B302033 : Blo 199806 302033 := bstep (se 2 (by rfl) ⟨113262, by rfl⟩ : syracuseStep 302033 = 226525) B226525
theorem B203731 : Blo 199806 203731 := bstep (se 1 (by rfl) ⟨152798, by rfl⟩ : syracuseStep 203731 = 305597) B305597
theorem B302051 : Blo 199806 302051 := bstep (se 1 (by rfl) ⟨226538, by rfl⟩ : syracuseStep 302051 = 453077) B453077
theorem B203747 : Blo 199806 203747 := bstep (se 1 (by rfl) ⟨152810, by rfl⟩ : syracuseStep 203747 = 305621) B305621
theorem B203763 : Blo 199806 203763 := bstep (se 1 (by rfl) ⟨152822, by rfl⟩ : syracuseStep 203763 = 305645) B305645
theorem B302081 : Blo 199806 302081 := bstep (se 2 (by rfl) ⟨113280, by rfl⟩ : syracuseStep 302081 = 226561) B226561
theorem B203779 : Blo 199806 203779 := bstep (se 1 (by rfl) ⟨152834, by rfl⟩ : syracuseStep 203779 = 305669) B305669
theorem B302099 : Blo 199806 302099 := bstep (se 1 (by rfl) ⟨226574, by rfl⟩ : syracuseStep 302099 = 453149) B453149
theorem B203795 : Blo 199806 203795 := bstep (se 1 (by rfl) ⟨152846, by rfl⟩ : syracuseStep 203795 = 305693) B305693
theorem B302129 : Blo 199806 302129 := bstep (se 2 (by rfl) ⟨113298, by rfl⟩ : syracuseStep 302129 = 226597) B226597
theorem B302147 : Blo 199806 302147 := bstep (se 1 (by rfl) ⟨226610, by rfl⟩ : syracuseStep 302147 = 453221) B453221
theorem B302177 : Blo 199806 302177 := bstep (se 2 (by rfl) ⟨113316, by rfl⟩ : syracuseStep 302177 = 226633) B226633
theorem B302195 : Blo 199806 302195 := bstep (se 1 (by rfl) ⟨226646, by rfl⟩ : syracuseStep 302195 = 453293) B453293
theorem B1154189 : Blo 199806 1154189 := bstep (se 3 (by rfl) ⟨216410, by rfl⟩ : syracuseStep 1154189 = 432821) B432821
theorem B302225 : Blo 199806 302225 := bstep (se 2 (by rfl) ⟨113334, by rfl⟩ : syracuseStep 302225 = 226669) B226669
theorem B302243 : Blo 199806 302243 := bstep (se 1 (by rfl) ⟨226682, by rfl⟩ : syracuseStep 302243 = 453365) B453365
theorem B302273 : Blo 199806 302273 := bstep (se 2 (by rfl) ⟨113352, by rfl⟩ : syracuseStep 302273 = 226705) B226705
theorem B302291 : Blo 199806 302291 := bstep (se 1 (by rfl) ⟨226718, by rfl⟩ : syracuseStep 302291 = 453437) B453437
theorem B302321 : Blo 199806 302321 := bstep (se 2 (by rfl) ⟨113370, by rfl⟩ : syracuseStep 302321 = 226741) B226741
theorem B302339 : Blo 199806 302339 := bstep (se 1 (by rfl) ⟨226754, by rfl⟩ : syracuseStep 302339 = 453509) B453509
theorem B302369 : Blo 199806 302369 := bstep (se 2 (by rfl) ⟨113388, by rfl⟩ : syracuseStep 302369 = 226777) B226777
theorem B302387 : Blo 199806 302387 := bstep (se 1 (by rfl) ⟨226790, by rfl⟩ : syracuseStep 302387 = 453581) B453581
theorem B302417 : Blo 199806 302417 := bstep (se 2 (by rfl) ⟨113406, by rfl⟩ : syracuseStep 302417 = 226813) B226813
theorem B302435 : Blo 199806 302435 := bstep (se 1 (by rfl) ⟨226826, by rfl⟩ : syracuseStep 302435 = 453653) B453653
theorem B302465 : Blo 199806 302465 := bstep (se 2 (by rfl) ⟨113424, by rfl⟩ : syracuseStep 302465 = 226849) B226849
theorem B302483 : Blo 199806 302483 := bstep (se 1 (by rfl) ⟨226862, by rfl⟩ : syracuseStep 302483 = 453725) B453725
theorem B302513 : Blo 199806 302513 := bstep (se 2 (by rfl) ⟨113442, by rfl⟩ : syracuseStep 302513 = 226885) B226885
theorem B302531 : Blo 199806 302531 := bstep (se 1 (by rfl) ⟨226898, by rfl⟩ : syracuseStep 302531 = 453797) B453797
theorem B302561 : Blo 199806 302561 := bstep (se 2 (by rfl) ⟨113460, by rfl⟩ : syracuseStep 302561 = 226921) B226921
theorem B1711601 : Blo 199806 1711601 := bstep (se 2 (by rfl) ⟨641850, by rfl⟩ : syracuseStep 1711601 = 1283701) B1283701
theorem B302579 : Blo 199806 302579 := bstep (se 1 (by rfl) ⟨226934, by rfl⟩ : syracuseStep 302579 = 453869) B453869
theorem B302609 : Blo 199806 302609 := bstep (se 2 (by rfl) ⟨113478, by rfl⟩ : syracuseStep 302609 = 226957) B226957
theorem B302627 : Blo 199806 302627 := bstep (se 1 (by rfl) ⟨226970, by rfl⟩ : syracuseStep 302627 = 453941) B453941
theorem B859697 : Blo 199806 859697 := bstep (se 2 (by rfl) ⟨322386, by rfl⟩ : syracuseStep 859697 = 644773) B644773
theorem B302657 : Blo 199806 302657 := bstep (se 2 (by rfl) ⟨113496, by rfl⟩ : syracuseStep 302657 = 226993) B226993
theorem B1121861 : Blo 199806 1121861 := bstep (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) B210349
theorem B302675 : Blo 199806 302675 := bstep (se 1 (by rfl) ⟨227006, by rfl⟩ : syracuseStep 302675 = 454013) B454013
theorem B302705 : Blo 199806 302705 := bstep (se 2 (by rfl) ⟨113514, by rfl⟩ : syracuseStep 302705 = 227029) B227029
theorem B302723 : Blo 199806 302723 := bstep (se 1 (by rfl) ⟨227042, by rfl⟩ : syracuseStep 302723 = 454085) B454085
theorem B302753 : Blo 199806 302753 := bstep (se 2 (by rfl) ⟨113532, by rfl⟩ : syracuseStep 302753 = 227065) B227065
theorem B302771 : Blo 199806 302771 := bstep (se 1 (by rfl) ⟨227078, by rfl⟩ : syracuseStep 302771 = 454157) B454157
theorem B302801 : Blo 199806 302801 := bstep (se 2 (by rfl) ⟨113550, by rfl⟩ : syracuseStep 302801 = 227101) B227101
theorem B302819 : Blo 199806 302819 := bstep (se 1 (by rfl) ⟨227114, by rfl⟩ : syracuseStep 302819 = 454229) B454229
theorem B302849 : Blo 199806 302849 := bstep (se 2 (by rfl) ⟨113568, by rfl⟩ : syracuseStep 302849 = 227137) B227137
theorem B302867 : Blo 199806 302867 := bstep (se 1 (by rfl) ⟨227150, by rfl⟩ : syracuseStep 302867 = 454301) B454301
theorem B302897 : Blo 199806 302897 := bstep (se 2 (by rfl) ⟨113586, by rfl⟩ : syracuseStep 302897 = 227173) B227173
theorem B302915 : Blo 199806 302915 := bstep (se 1 (by rfl) ⟨227186, by rfl⟩ : syracuseStep 302915 = 454373) B454373
theorem B302945 : Blo 199806 302945 := bstep (se 2 (by rfl) ⟨113604, by rfl⟩ : syracuseStep 302945 = 227209) B227209
theorem B204643 : Blo 199806 204643 := bstep (se 1 (by rfl) ⟨153482, by rfl⟩ : syracuseStep 204643 = 306965) B306965
theorem B302963 : Blo 199806 302963 := bstep (se 1 (by rfl) ⟨227222, by rfl⟩ : syracuseStep 302963 = 454445) B454445
theorem B302993 : Blo 199806 302993 := bstep (se 2 (by rfl) ⟨113622, by rfl⟩ : syracuseStep 302993 = 227245) B227245
theorem B303011 : Blo 199806 303011 := bstep (se 1 (by rfl) ⟨227258, by rfl⟩ : syracuseStep 303011 = 454517) B454517
theorem B270257 : Blo 199806 270257 := bstep (se 2 (by rfl) ⟨101346, by rfl⟩ : syracuseStep 270257 = 202693) B202693
theorem B303041 : Blo 199806 303041 := bstep (se 2 (by rfl) ⟨113640, by rfl⟩ : syracuseStep 303041 = 227281) B227281
theorem B303059 : Blo 199806 303059 := bstep (se 1 (by rfl) ⟨227294, by rfl⟩ : syracuseStep 303059 = 454589) B454589
theorem B303089 : Blo 199806 303089 := bstep (se 2 (by rfl) ⟨113658, by rfl⟩ : syracuseStep 303089 = 227317) B227317
theorem B303107 : Blo 199806 303107 := bstep (se 1 (by rfl) ⟨227330, by rfl⟩ : syracuseStep 303107 = 454661) B454661
theorem B303137 : Blo 199806 303137 := bstep (se 2 (by rfl) ⟨113676, by rfl⟩ : syracuseStep 303137 = 227353) B227353
theorem B1089571 : Blo 199806 1089571 := bstep (se 1 (by rfl) ⟨817178, by rfl⟩ : syracuseStep 1089571 = 1634357) B1634357
theorem B303155 : Blo 199806 303155 := bstep (se 1 (by rfl) ⟨227366, by rfl⟩ : syracuseStep 303155 = 454733) B454733
theorem B303185 : Blo 199806 303185 := bstep (se 2 (by rfl) ⟨113694, by rfl⟩ : syracuseStep 303185 = 227389) B227389
theorem B303203 : Blo 199806 303203 := bstep (se 1 (by rfl) ⟨227402, by rfl⟩ : syracuseStep 303203 = 454805) B454805
theorem B303233 : Blo 199806 303233 := bstep (se 2 (by rfl) ⟨113712, by rfl⟩ : syracuseStep 303233 = 227425) B227425
theorem B303251 : Blo 199806 303251 := bstep (se 1 (by rfl) ⟨227438, by rfl⟩ : syracuseStep 303251 = 454877) B454877
theorem B1024163 : Blo 199806 1024163 := bstep (se 1 (by rfl) ⟨768122, by rfl⟩ : syracuseStep 1024163 = 1536245) B1536245
theorem B303281 : Blo 199806 303281 := bstep (se 2 (by rfl) ⟨113730, by rfl⟩ : syracuseStep 303281 = 227461) B227461
theorem B303299 : Blo 199806 303299 := bstep (se 1 (by rfl) ⟨227474, by rfl⟩ : syracuseStep 303299 = 454949) B454949
theorem B303329 : Blo 199806 303329 := bstep (se 2 (by rfl) ⟨113748, by rfl⟩ : syracuseStep 303329 = 227497) B227497
theorem B303347 : Blo 199806 303347 := bstep (se 1 (by rfl) ⟨227510, by rfl⟩ : syracuseStep 303347 = 455021) B455021
theorem B303377 : Blo 199806 303377 := bstep (se 2 (by rfl) ⟨113766, by rfl⟩ : syracuseStep 303377 = 227533) B227533
theorem B303395 : Blo 199806 303395 := bstep (se 1 (by rfl) ⟨227546, by rfl⟩ : syracuseStep 303395 = 455093) B455093
theorem B303425 : Blo 199806 303425 := bstep (se 2 (by rfl) ⟨113784, by rfl⟩ : syracuseStep 303425 = 227569) B227569
theorem B303443 : Blo 199806 303443 := bstep (se 1 (by rfl) ⟨227582, by rfl⟩ : syracuseStep 303443 = 455165) B455165
theorem B303473 : Blo 199806 303473 := bstep (se 2 (by rfl) ⟨113802, by rfl⟩ : syracuseStep 303473 = 227605) B227605
theorem B303491 : Blo 199806 303491 := bstep (se 1 (by rfl) ⟨227618, by rfl⟩ : syracuseStep 303491 = 455237) B455237
theorem B303521 : Blo 199806 303521 := bstep (se 2 (by rfl) ⟨113820, by rfl⟩ : syracuseStep 303521 = 227641) B227641
theorem B303539 : Blo 199806 303539 := bstep (se 1 (by rfl) ⟨227654, by rfl⟩ : syracuseStep 303539 = 455309) B455309
theorem B303569 : Blo 199806 303569 := bstep (se 2 (by rfl) ⟨113838, by rfl⟩ : syracuseStep 303569 = 227677) B227677
theorem B303587 : Blo 199806 303587 := bstep (se 1 (by rfl) ⟨227690, by rfl⟩ : syracuseStep 303587 = 455381) B455381
theorem B434659 : Blo 199806 434659 := bstep (se 1 (by rfl) ⟨325994, by rfl⟩ : syracuseStep 434659 = 651989) B651989
theorem B303617 : Blo 199806 303617 := bstep (se 2 (by rfl) ⟨113856, by rfl⟩ : syracuseStep 303617 = 227713) B227713
theorem B303635 : Blo 199806 303635 := bstep (se 1 (by rfl) ⟨227726, by rfl⟩ : syracuseStep 303635 = 455453) B455453
theorem B303665 : Blo 199806 303665 := bstep (se 2 (by rfl) ⟨113874, by rfl⟩ : syracuseStep 303665 = 227749) B227749
theorem B303683 : Blo 199806 303683 := bstep (se 1 (by rfl) ⟨227762, by rfl⟩ : syracuseStep 303683 = 455525) B455525
theorem B303713 : Blo 199806 303713 := bstep (se 2 (by rfl) ⟨113892, by rfl⟩ : syracuseStep 303713 = 227785) B227785
theorem B303731 : Blo 199806 303731 := bstep (se 1 (by rfl) ⟨227798, by rfl⟩ : syracuseStep 303731 = 455597) B455597
theorem B303761 : Blo 199806 303761 := bstep (se 2 (by rfl) ⟨113910, by rfl⟩ : syracuseStep 303761 = 227821) B227821
theorem B303779 : Blo 199806 303779 := bstep (se 1 (by rfl) ⟨227834, by rfl⟩ : syracuseStep 303779 = 455669) B455669
theorem B303809 : Blo 199806 303809 := bstep (se 2 (by rfl) ⟨113928, by rfl⟩ : syracuseStep 303809 = 227857) B227857
theorem B303827 : Blo 199806 303827 := bstep (se 1 (by rfl) ⟨227870, by rfl⟩ : syracuseStep 303827 = 455741) B455741
theorem B303857 : Blo 199806 303857 := bstep (se 2 (by rfl) ⟨113946, by rfl⟩ : syracuseStep 303857 = 227893) B227893
theorem B303875 : Blo 199806 303875 := bstep (se 1 (by rfl) ⟨227906, by rfl⟩ : syracuseStep 303875 = 455813) B455813
theorem B303905 : Blo 199806 303905 := bstep (se 2 (by rfl) ⟨113964, by rfl⟩ : syracuseStep 303905 = 227929) B227929
theorem B303923 : Blo 199806 303923 := bstep (se 1 (by rfl) ⟨227942, by rfl⟩ : syracuseStep 303923 = 455885) B455885
theorem B303953 : Blo 199806 303953 := bstep (se 2 (by rfl) ⟨113982, by rfl⟩ : syracuseStep 303953 = 227965) B227965
theorem B303971 : Blo 199806 303971 := bstep (se 1 (by rfl) ⟨227978, by rfl⟩ : syracuseStep 303971 = 455957) B455957
theorem B304001 : Blo 199806 304001 := bstep (se 2 (by rfl) ⟨114000, by rfl⟩ : syracuseStep 304001 = 228001) B228001
theorem B304019 : Blo 199806 304019 := bstep (se 1 (by rfl) ⟨228014, by rfl⟩ : syracuseStep 304019 = 456029) B456029
theorem B304049 : Blo 199806 304049 := bstep (se 2 (by rfl) ⟨114018, by rfl⟩ : syracuseStep 304049 = 228037) B228037
theorem B304067 : Blo 199806 304067 := bstep (se 1 (by rfl) ⟨228050, by rfl⟩ : syracuseStep 304067 = 456101) B456101
theorem B1024973 : Blo 199806 1024973 := bstep (se 3 (by rfl) ⟨192182, by rfl⟩ : syracuseStep 1024973 = 384365) B384365
theorem B304097 : Blo 199806 304097 := bstep (se 2 (by rfl) ⟨114036, by rfl⟩ : syracuseStep 304097 = 228073) B228073
theorem B304115 : Blo 199806 304115 := bstep (se 1 (by rfl) ⟨228086, by rfl⟩ : syracuseStep 304115 = 456173) B456173
theorem B304145 : Blo 199806 304145 := bstep (se 2 (by rfl) ⟨114054, by rfl⟩ : syracuseStep 304145 = 228109) B228109
theorem B304163 : Blo 199806 304163 := bstep (se 1 (by rfl) ⟨228122, by rfl⟩ : syracuseStep 304163 = 456245) B456245
theorem B762929 : Blo 199806 762929 := bstep (se 2 (by rfl) ⟨286098, by rfl⟩ : syracuseStep 762929 = 572197) B572197
theorem B304193 : Blo 199806 304193 := bstep (se 2 (by rfl) ⟨114072, by rfl⟩ : syracuseStep 304193 = 228145) B228145
theorem B205907 : Blo 199806 205907 := bstep (se 1 (by rfl) ⟨154430, by rfl⟩ : syracuseStep 205907 = 308861) B308861
theorem B304211 : Blo 199806 304211 := bstep (se 1 (by rfl) ⟨228158, by rfl⟩ : syracuseStep 304211 = 456317) B456317
theorem B304241 : Blo 199806 304241 := bstep (se 2 (by rfl) ⟨114090, by rfl⟩ : syracuseStep 304241 = 228181) B228181
theorem B304259 : Blo 199806 304259 := bstep (se 1 (by rfl) ⟨228194, by rfl⟩ : syracuseStep 304259 = 456389) B456389
theorem B304289 : Blo 199806 304289 := bstep (se 2 (by rfl) ⟨114108, by rfl⟩ : syracuseStep 304289 = 228217) B228217
theorem B304307 : Blo 199806 304307 := bstep (se 1 (by rfl) ⟨228230, by rfl⟩ : syracuseStep 304307 = 456461) B456461
theorem B304337 : Blo 199806 304337 := bstep (se 2 (by rfl) ⟨114126, by rfl⟩ : syracuseStep 304337 = 228253) B228253
theorem B304355 : Blo 199806 304355 := bstep (se 1 (by rfl) ⟨228266, by rfl⟩ : syracuseStep 304355 = 456533) B456533
theorem B271603 : Blo 199806 271603 := bstep (se 1 (by rfl) ⟨203702, by rfl⟩ : syracuseStep 271603 = 407405) B407405
theorem B304385 : Blo 199806 304385 := bstep (se 2 (by rfl) ⟨114144, by rfl⟩ : syracuseStep 304385 = 228289) B228289
theorem B369937 : Blo 199806 369937 := bstep (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) B277453
theorem B304403 : Blo 199806 304403 := bstep (se 1 (by rfl) ⟨228302, by rfl⟩ : syracuseStep 304403 = 456605) B456605
theorem B730417 : Blo 199806 730417 := bstep (se 2 (by rfl) ⟨273906, by rfl⟩ : syracuseStep 730417 = 547813) B547813
theorem B304433 : Blo 199806 304433 := bstep (se 2 (by rfl) ⟨114162, by rfl⟩ : syracuseStep 304433 = 228325) B228325
theorem B304435 : Blo 199806 304435 := bstep (se 1 (by rfl) ⟨228326, by rfl⟩ : syracuseStep 304435 = 456653) B456653
theorem B304451 : Blo 199806 304451 := bstep (se 1 (by rfl) ⟨228338, by rfl⟩ : syracuseStep 304451 = 456677) B456677
theorem B304481 : Blo 199806 304481 := bstep (se 2 (by rfl) ⟨114180, by rfl⟩ : syracuseStep 304481 = 228361) B228361
theorem B304499 : Blo 199806 304499 := bstep (se 1 (by rfl) ⟨228374, by rfl⟩ : syracuseStep 304499 = 456749) B456749
theorem B337297 : Blo 199806 337297 := bstep (se 2 (by rfl) ⟨126486, by rfl⟩ : syracuseStep 337297 = 252973) B252973
theorem B304529 : Blo 199806 304529 := bstep (se 2 (by rfl) ⟨114198, by rfl⟩ : syracuseStep 304529 = 228397) B228397
theorem B304547 : Blo 199806 304547 := bstep (se 1 (by rfl) ⟨228410, by rfl⟩ : syracuseStep 304547 = 456821) B456821
theorem B337331 : Blo 199806 337331 := bstep (se 1 (by rfl) ⟨252998, by rfl⟩ : syracuseStep 337331 = 505997) B505997
theorem B304577 : Blo 199806 304577 := bstep (se 2 (by rfl) ⟨114216, by rfl⟩ : syracuseStep 304577 = 228433) B228433
theorem B304595 : Blo 199806 304595 := bstep (se 1 (by rfl) ⟨228446, by rfl⟩ : syracuseStep 304595 = 456893) B456893
theorem B304625 : Blo 199806 304625 := bstep (se 2 (by rfl) ⟨114234, by rfl⟩ : syracuseStep 304625 = 228469) B228469
theorem B304643 : Blo 199806 304643 := bstep (se 1 (by rfl) ⟨228482, by rfl⟩ : syracuseStep 304643 = 456965) B456965
theorem B304673 : Blo 199806 304673 := bstep (se 2 (by rfl) ⟨114252, by rfl⟩ : syracuseStep 304673 = 228505) B228505
theorem B337459 : Blo 199806 337459 := bstep (se 1 (by rfl) ⟨253094, by rfl⟩ : syracuseStep 337459 = 506189) B506189
theorem B304691 : Blo 199806 304691 := bstep (se 1 (by rfl) ⟨228518, by rfl⟩ : syracuseStep 304691 = 457037) B457037
theorem B304721 : Blo 199806 304721 := bstep (se 2 (by rfl) ⟨114270, by rfl⟩ : syracuseStep 304721 = 228541) B228541
theorem B304739 : Blo 199806 304739 := bstep (se 1 (by rfl) ⟨228554, by rfl⟩ : syracuseStep 304739 = 457109) B457109
theorem B304769 : Blo 199806 304769 := bstep (se 2 (by rfl) ⟨114288, by rfl⟩ : syracuseStep 304769 = 228577) B228577
theorem B304787 : Blo 199806 304787 := bstep (se 1 (by rfl) ⟨228590, by rfl⟩ : syracuseStep 304787 = 457181) B457181
theorem B304817 : Blo 199806 304817 := bstep (se 2 (by rfl) ⟨114306, by rfl⟩ : syracuseStep 304817 = 228613) B228613
theorem B337601 : Blo 199806 337601 := bstep (se 2 (by rfl) ⟨126600, by rfl⟩ : syracuseStep 337601 = 253201) B253201
theorem B304835 : Blo 199806 304835 := bstep (se 1 (by rfl) ⟨228626, by rfl⟩ : syracuseStep 304835 = 457253) B457253
theorem B304865 : Blo 199806 304865 := bstep (se 2 (by rfl) ⟨114324, by rfl⟩ : syracuseStep 304865 = 228649) B228649
theorem B304883 : Blo 199806 304883 := bstep (se 1 (by rfl) ⟨228662, by rfl⟩ : syracuseStep 304883 = 457325) B457325
theorem B304913 : Blo 199806 304913 := bstep (se 2 (by rfl) ⟨114342, by rfl⟩ : syracuseStep 304913 = 228685) B228685
theorem B304931 : Blo 199806 304931 := bstep (se 1 (by rfl) ⟨228698, by rfl⟩ : syracuseStep 304931 = 457397) B457397
theorem B337729 : Blo 199806 337729 := bstep (se 2 (by rfl) ⟨126648, by rfl⟩ : syracuseStep 337729 = 253297) B253297
theorem B304961 : Blo 199806 304961 := bstep (se 2 (by rfl) ⟨114360, by rfl⟩ : syracuseStep 304961 = 228721) B228721
theorem B304979 : Blo 199806 304979 := bstep (se 1 (by rfl) ⟨228734, by rfl⟩ : syracuseStep 304979 = 457469) B457469
theorem B337763 : Blo 199806 337763 := bstep (se 1 (by rfl) ⟨253322, by rfl⟩ : syracuseStep 337763 = 506645) B506645
theorem B305009 : Blo 199806 305009 := bstep (se 2 (by rfl) ⟨114378, by rfl⟩ : syracuseStep 305009 = 228757) B228757
theorem B305027 : Blo 199806 305027 := bstep (se 1 (by rfl) ⟨228770, by rfl⟩ : syracuseStep 305027 = 457541) B457541
theorem B1714061 : Blo 199806 1714061 := bstep (se 3 (by rfl) ⟨321386, by rfl⟩ : syracuseStep 1714061 = 642773) B642773
theorem B272273 : Blo 199806 272273 := bstep (se 2 (by rfl) ⟨102102, by rfl⟩ : syracuseStep 272273 = 204205) B204205
theorem B305057 : Blo 199806 305057 := bstep (se 2 (by rfl) ⟨114396, by rfl⟩ : syracuseStep 305057 = 228793) B228793
theorem B305075 : Blo 199806 305075 := bstep (se 1 (by rfl) ⟨228806, by rfl⟩ : syracuseStep 305075 = 457613) B457613
theorem B862157 : Blo 199806 862157 := bstep (se 3 (by rfl) ⟨161654, by rfl⟩ : syracuseStep 862157 = 323309) B323309
theorem B305105 : Blo 199806 305105 := bstep (se 2 (by rfl) ⟨114414, by rfl⟩ : syracuseStep 305105 = 228829) B228829
theorem B337891 : Blo 199806 337891 := bstep (se 1 (by rfl) ⟨253418, by rfl⟩ : syracuseStep 337891 = 506837) B506837
theorem B305123 : Blo 199806 305123 := bstep (se 1 (by rfl) ⟨228842, by rfl⟩ : syracuseStep 305123 = 457685) B457685
theorem B1157105 : Blo 199806 1157105 := bstep (se 2 (by rfl) ⟨433914, by rfl⟩ : syracuseStep 1157105 = 867829) B867829
theorem B305153 : Blo 199806 305153 := bstep (se 2 (by rfl) ⟨114432, by rfl⟩ : syracuseStep 305153 = 228865) B228865
theorem B305171 : Blo 199806 305171 := bstep (se 1 (by rfl) ⟨228878, by rfl⟩ : syracuseStep 305171 = 457757) B457757
theorem B305201 : Blo 199806 305201 := bstep (se 2 (by rfl) ⟨114450, by rfl⟩ : syracuseStep 305201 = 228901) B228901
theorem B305219 : Blo 199806 305219 := bstep (se 1 (by rfl) ⟨228914, by rfl⟩ : syracuseStep 305219 = 457829) B457829
theorem B305249 : Blo 199806 305249 := bstep (se 2 (by rfl) ⟨114468, by rfl⟩ : syracuseStep 305249 = 228937) B228937
theorem B338033 : Blo 199806 338033 := bstep (se 2 (by rfl) ⟨126762, by rfl⟩ : syracuseStep 338033 = 253525) B253525
theorem B305267 : Blo 199806 305267 := bstep (se 1 (by rfl) ⟨228950, by rfl⟩ : syracuseStep 305267 = 457901) B457901
theorem B305297 : Blo 199806 305297 := bstep (se 2 (by rfl) ⟨114486, by rfl⟩ : syracuseStep 305297 = 228973) B228973
theorem B305315 : Blo 199806 305315 := bstep (se 1 (by rfl) ⟨228986, by rfl⟩ : syracuseStep 305315 = 457973) B457973
theorem B305345 : Blo 199806 305345 := bstep (se 2 (by rfl) ⟨114504, by rfl⟩ : syracuseStep 305345 = 229009) B229009
theorem B2009285 : Blo 199806 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B305363 : Blo 199806 305363 := bstep (se 1 (by rfl) ⟨229022, by rfl⟩ : syracuseStep 305363 = 458045) B458045
theorem B338161 : Blo 199806 338161 := bstep (se 2 (by rfl) ⟨126810, by rfl⟩ : syracuseStep 338161 = 253621) B253621
theorem B305393 : Blo 199806 305393 := bstep (se 2 (by rfl) ⟨114522, by rfl⟩ : syracuseStep 305393 = 229045) B229045
theorem B305411 : Blo 199806 305411 := bstep (se 1 (by rfl) ⟨229058, by rfl⟩ : syracuseStep 305411 = 458117) B458117
theorem B338195 : Blo 199806 338195 := bstep (se 1 (by rfl) ⟨253646, by rfl⟩ : syracuseStep 338195 = 507293) B507293
theorem B305441 : Blo 199806 305441 := bstep (se 2 (by rfl) ⟨114540, by rfl⟩ : syracuseStep 305441 = 229081) B229081
theorem B305459 : Blo 199806 305459 := bstep (se 1 (by rfl) ⟨229094, by rfl⟩ : syracuseStep 305459 = 458189) B458189
theorem B305489 : Blo 199806 305489 := bstep (se 2 (by rfl) ⟨114558, by rfl⟩ : syracuseStep 305489 = 229117) B229117
theorem B305507 : Blo 199806 305507 := bstep (se 1 (by rfl) ⟨229130, by rfl⟩ : syracuseStep 305507 = 458261) B458261
theorem B305537 : Blo 199806 305537 := bstep (se 2 (by rfl) ⟨114576, by rfl⟩ : syracuseStep 305537 = 229153) B229153
theorem B338323 : Blo 199806 338323 := bstep (se 1 (by rfl) ⟨253742, by rfl⟩ : syracuseStep 338323 = 507485) B507485
theorem B305555 : Blo 199806 305555 := bstep (se 1 (by rfl) ⟨229166, by rfl⟩ : syracuseStep 305555 = 458333) B458333
theorem B305585 : Blo 199806 305585 := bstep (se 2 (by rfl) ⟨114594, by rfl⟩ : syracuseStep 305585 = 229189) B229189
theorem B305603 : Blo 199806 305603 := bstep (se 1 (by rfl) ⟨229202, by rfl⟩ : syracuseStep 305603 = 458405) B458405
theorem B731597 : Blo 199806 731597 := bstep (se 3 (by rfl) ⟨137174, by rfl⟩ : syracuseStep 731597 = 274349) B274349
theorem B305633 : Blo 199806 305633 := bstep (se 2 (by rfl) ⟨114612, by rfl⟩ : syracuseStep 305633 = 229225) B229225
theorem B764387 : Blo 199806 764387 := bstep (se 1 (by rfl) ⟨573290, by rfl⟩ : syracuseStep 764387 = 1146581) B1146581
theorem B305651 : Blo 199806 305651 := bstep (se 1 (by rfl) ⟨229238, by rfl⟩ : syracuseStep 305651 = 458477) B458477
theorem B305681 : Blo 199806 305681 := bstep (se 2 (by rfl) ⟨114630, by rfl⟩ : syracuseStep 305681 = 229261) B229261
theorem B338465 : Blo 199806 338465 := bstep (se 2 (by rfl) ⟨126924, by rfl⟩ : syracuseStep 338465 = 253849) B253849
theorem B305699 : Blo 199806 305699 := bstep (se 1 (by rfl) ⟨229274, by rfl⟩ : syracuseStep 305699 = 458549) B458549
theorem B273025 : Blo 199806 273025 := bstep (se 2 (by rfl) ⟨102384, by rfl⟩ : syracuseStep 273025 = 204769) B204769
theorem B338593 : Blo 199806 338593 := bstep (se 2 (by rfl) ⟨126972, by rfl⟩ : syracuseStep 338593 = 253945) B253945
theorem B338627 : Blo 199806 338627 := bstep (se 1 (by rfl) ⟨253970, by rfl⟩ : syracuseStep 338627 = 507941) B507941
theorem B338755 : Blo 199806 338755 := bstep (se 1 (by rfl) ⟨254066, by rfl⟩ : syracuseStep 338755 = 508133) B508133
theorem B338897 : Blo 199806 338897 := bstep (se 2 (by rfl) ⟨127086, by rfl⟩ : syracuseStep 338897 = 254173) B254173
theorem B339025 : Blo 199806 339025 := bstep (se 2 (by rfl) ⟨127134, by rfl⟩ : syracuseStep 339025 = 254269) B254269
theorem B339059 : Blo 199806 339059 := bstep (se 1 (by rfl) ⟨254294, by rfl⟩ : syracuseStep 339059 = 508589) B508589
theorem B339187 : Blo 199806 339187 := bstep (se 1 (by rfl) ⟨254390, by rfl⟩ : syracuseStep 339187 = 508781) B508781
theorem B339329 : Blo 199806 339329 := bstep (se 2 (by rfl) ⟨127248, by rfl⟩ : syracuseStep 339329 = 254497) B254497
theorem B1158563 : Blo 199806 1158563 := bstep (se 1 (by rfl) ⟨868922, by rfl⟩ : syracuseStep 1158563 = 1737845) B1737845
theorem B765389 : Blo 199806 765389 := bstep (se 3 (by rfl) ⟨143510, by rfl⟩ : syracuseStep 765389 = 287021) B287021
theorem B863729 : Blo 199806 863729 := bstep (se 2 (by rfl) ⟨323898, by rfl⟩ : syracuseStep 863729 = 647797) B647797
theorem B339457 : Blo 199806 339457 := bstep (se 2 (by rfl) ⟨127296, by rfl⟩ : syracuseStep 339457 = 254593) B254593
theorem B339491 : Blo 199806 339491 := bstep (se 1 (by rfl) ⟨254618, by rfl⟩ : syracuseStep 339491 = 509237) B509237
theorem B339619 : Blo 199806 339619 := bstep (se 1 (by rfl) ⟨254714, by rfl⟩ : syracuseStep 339619 = 509429) B509429
theorem B405233 : Blo 199806 405233 := bstep (se 2 (by rfl) ⟨151962, by rfl⟩ : syracuseStep 405233 = 303925) B303925
theorem B339761 : Blo 199806 339761 := bstep (se 2 (by rfl) ⟨127410, by rfl⟩ : syracuseStep 339761 = 254821) B254821
theorem B1027889 : Blo 199806 1027889 := bstep (se 2 (by rfl) ⟨385458, by rfl⟩ : syracuseStep 1027889 = 770917) B770917
theorem B339889 : Blo 199806 339889 := bstep (se 2 (by rfl) ⟨127458, by rfl⟩ : syracuseStep 339889 = 254917) B254917
theorem B339923 : Blo 199806 339923 := bstep (se 1 (by rfl) ⟨254942, by rfl⟩ : syracuseStep 339923 = 509885) B509885
theorem B340051 : Blo 199806 340051 := bstep (se 1 (by rfl) ⟨255038, by rfl⟩ : syracuseStep 340051 = 510077) B510077
theorem B1388677 : Blo 199806 1388677 := bstep (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) B260377
theorem B340193 : Blo 199806 340193 := bstep (se 2 (by rfl) ⟨127572, by rfl⟩ : syracuseStep 340193 = 255145) B255145
theorem B1290467 : Blo 199806 1290467 := bstep (se 1 (by rfl) ⟨967850, by rfl⟩ : syracuseStep 1290467 = 1935701) B1935701
theorem B2470115 : Blo 199806 2470115 := bstep (se 1 (by rfl) ⟨1852586, by rfl⟩ : syracuseStep 2470115 = 3705173) B3705173
theorem B2175245 : Blo 199806 2175245 := bstep (se 3 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 2175245 = 815717) B815717
theorem B340321 : Blo 199806 340321 := bstep (se 2 (by rfl) ⟨127620, by rfl⟩ : syracuseStep 340321 = 255241) B255241
theorem B340355 : Blo 199806 340355 := bstep (se 1 (by rfl) ⟨255266, by rfl⟩ : syracuseStep 340355 = 510533) B510533
theorem B340483 : Blo 199806 340483 := bstep (se 1 (by rfl) ⟨255362, by rfl⟩ : syracuseStep 340483 = 510725) B510725
theorem B2142773 : Blo 199806 2142773 := bstep (se 5 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 2142773 = 200885) B200885
theorem B275041 : Blo 199806 275041 := bstep (se 2 (by rfl) ⟨103140, by rfl⟩ : syracuseStep 275041 = 206281) B206281
theorem B2175587 : Blo 199806 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B569987 : Blo 199806 569987 := bstep (se 1 (by rfl) ⟨427490, by rfl⟩ : syracuseStep 569987 = 854981) B854981
theorem B3846797 : Blo 199806 3846797 := bstep (se 3 (by rfl) ⟨721274, by rfl⟩ : syracuseStep 3846797 = 1442549) B1442549
theorem B340625 : Blo 199806 340625 := bstep (se 2 (by rfl) ⟨127734, by rfl⟩ : syracuseStep 340625 = 255469) B255469
theorem B340753 : Blo 199806 340753 := bstep (se 2 (by rfl) ⟨127782, by rfl⟩ : syracuseStep 340753 = 255565) B255565
theorem B340787 : Blo 199806 340787 := bstep (se 1 (by rfl) ⟨255590, by rfl⟩ : syracuseStep 340787 = 511181) B511181
theorem B340915 : Blo 199806 340915 := bstep (se 1 (by rfl) ⟨255686, by rfl⟩ : syracuseStep 340915 = 511373) B511373
theorem B341057 : Blo 199806 341057 := bstep (se 2 (by rfl) ⟨127896, by rfl⟩ : syracuseStep 341057 = 255793) B255793
theorem B406595 : Blo 199806 406595 := bstep (se 1 (by rfl) ⟨304946, by rfl⟩ : syracuseStep 406595 = 609893) B609893
theorem B963683 : Blo 199806 963683 := bstep (se 1 (by rfl) ⟨722762, by rfl⟩ : syracuseStep 963683 = 1445525) B1445525
theorem B341185 : Blo 199806 341185 := bstep (se 2 (by rfl) ⟨127944, by rfl⟩ : syracuseStep 341185 = 255889) B255889
theorem B341219 : Blo 199806 341219 := bstep (se 1 (by rfl) ⟨255914, by rfl⟩ : syracuseStep 341219 = 511829) B511829
theorem B1029347 : Blo 199806 1029347 := bstep (se 1 (by rfl) ⟨772010, by rfl⟩ : syracuseStep 1029347 = 1544021) B1544021
theorem B341347 : Blo 199806 341347 := bstep (se 1 (by rfl) ⟨256010, by rfl⟩ : syracuseStep 341347 = 512021) B512021
theorem B570797 : Blo 199806 570797 := bstep (se 3 (by rfl) ⟨107024, by rfl⟩ : syracuseStep 570797 = 214049) B214049
theorem B1291697 : Blo 199806 1291697 := bstep (se 2 (by rfl) ⟨484386, by rfl⟩ : syracuseStep 1291697 = 968773) B968773
theorem B341489 : Blo 199806 341489 := bstep (se 2 (by rfl) ⟨128058, by rfl⟩ : syracuseStep 341489 = 256117) B256117
theorem B767501 : Blo 199806 767501 := bstep (se 3 (by rfl) ⟨143906, by rfl⟩ : syracuseStep 767501 = 287813) B287813
theorem B570989 : Blo 199806 570989 := bstep (se 3 (by rfl) ⟨107060, by rfl⟩ : syracuseStep 570989 = 214121) B214121
theorem B341617 : Blo 199806 341617 := bstep (se 2 (by rfl) ⟨128106, by rfl⟩ : syracuseStep 341617 = 256213) B256213
theorem B341651 : Blo 199806 341651 := bstep (se 1 (by rfl) ⟨256238, by rfl⟩ : syracuseStep 341651 = 512477) B512477
theorem B341777 : Blo 199806 341777 := bstep (se 2 (by rfl) ⟨128166, by rfl⟩ : syracuseStep 341777 = 256333) B256333
theorem B341779 : Blo 199806 341779 := bstep (se 1 (by rfl) ⟨256334, by rfl⟩ : syracuseStep 341779 = 512669) B512669
theorem B4110193 : Blo 199806 4110193 := bstep (se 2 (by rfl) ⟨1541322, by rfl⟩ : syracuseStep 4110193 = 3082645) B3082645
theorem B866189 : Blo 199806 866189 := bstep (se 3 (by rfl) ⟨162410, by rfl⟩ : syracuseStep 866189 = 324821) B324821
theorem B341921 : Blo 199806 341921 := bstep (se 2 (by rfl) ⟨128220, by rfl⟩ : syracuseStep 341921 = 256441) B256441
theorem B1030157 : Blo 199806 1030157 := bstep (se 3 (by rfl) ⟨193154, by rfl⟩ : syracuseStep 1030157 = 386309) B386309
theorem B243731 : Blo 199806 243731 := bstep (se 1 (by rfl) ⟨182798, by rfl⟩ : syracuseStep 243731 = 365597) B365597
theorem B342049 : Blo 199806 342049 := bstep (se 2 (by rfl) ⟨128268, by rfl⟩ : syracuseStep 342049 = 256537) B256537
theorem B342083 : Blo 199806 342083 := bstep (se 1 (by rfl) ⟨256562, by rfl⟩ : syracuseStep 342083 = 513125) B513125
theorem B407729 : Blo 199806 407729 := bstep (se 2 (by rfl) ⟨152898, by rfl⟩ : syracuseStep 407729 = 305797) B305797
theorem B342211 : Blo 199806 342211 := bstep (se 1 (by rfl) ⟨256658, by rfl⟩ : syracuseStep 342211 = 513317) B513317
theorem B866531 : Blo 199806 866531 := bstep (se 1 (by rfl) ⟨649898, by rfl⟩ : syracuseStep 866531 = 1299797) B1299797
theorem B768305 : Blo 199806 768305 := bstep (se 2 (by rfl) ⟨288114, by rfl⟩ : syracuseStep 768305 = 576229) B576229
theorem B342353 : Blo 199806 342353 := bstep (se 2 (by rfl) ⟨128382, by rfl⟩ : syracuseStep 342353 = 256765) B256765
theorem B506321 : Blo 199806 506321 := bstep (se 2 (by rfl) ⟨189870, by rfl⟩ : syracuseStep 506321 = 379741) B379741
theorem B342481 : Blo 199806 342481 := bstep (se 2 (by rfl) ⟨128430, by rfl⟩ : syracuseStep 342481 = 256861) B256861
theorem B3455459 : Blo 199806 3455459 := bstep (se 1 (by rfl) ⟨2591594, by rfl⟩ : syracuseStep 3455459 = 5183189) B5183189
theorem B342515 : Blo 199806 342515 := bstep (se 1 (by rfl) ⟨256886, by rfl⟩ : syracuseStep 342515 = 513773) B513773
theorem B506371 : Blo 199806 506371 := bstep (se 1 (by rfl) ⟨379778, by rfl⟩ : syracuseStep 506371 = 759557) B759557
theorem B244291 : Blo 199806 244291 := bstep (se 1 (by rfl) ⟨183218, by rfl⟩ : syracuseStep 244291 = 366437) B366437
theorem B571981 : Blo 199806 571981 := bstep (se 3 (by rfl) ⟨107246, by rfl⟩ : syracuseStep 571981 = 214493) B214493
theorem B342643 : Blo 199806 342643 := bstep (se 1 (by rfl) ⟨256982, by rfl⟩ : syracuseStep 342643 = 513965) B513965
theorem B506513 : Blo 199806 506513 := bstep (se 2 (by rfl) ⟨189942, by rfl⟩ : syracuseStep 506513 = 379885) B379885
theorem B342785 : Blo 199806 342785 := bstep (se 2 (by rfl) ⟨128544, by rfl⟩ : syracuseStep 342785 = 257089) B257089
theorem B342913 : Blo 199806 342913 := bstep (se 2 (by rfl) ⟨128592, by rfl⟩ : syracuseStep 342913 = 257185) B257185
theorem B342929 : Blo 199806 342929 := bstep (se 2 (by rfl) ⟨128598, by rfl⟩ : syracuseStep 342929 = 257197) B257197
theorem B342947 : Blo 199806 342947 := bstep (se 1 (by rfl) ⟨257210, by rfl⟩ : syracuseStep 342947 = 514421) B514421
theorem B768973 : Blo 199806 768973 := bstep (se 3 (by rfl) ⟨144182, by rfl⟩ : syracuseStep 768973 = 288365) B288365
theorem B343075 : Blo 199806 343075 := bstep (se 1 (by rfl) ⟨257306, by rfl⟩ : syracuseStep 343075 = 514613) B514613
theorem B343217 : Blo 199806 343217 := bstep (se 2 (by rfl) ⟨128706, by rfl⟩ : syracuseStep 343217 = 257413) B257413
theorem B1097009 : Blo 199806 1097009 := bstep (se 2 (by rfl) ⟨411378, by rfl⟩ : syracuseStep 1097009 = 822757) B822757
theorem B343345 : Blo 199806 343345 := bstep (se 2 (by rfl) ⟨128754, by rfl⟩ : syracuseStep 343345 = 257509) B257509
theorem B343379 : Blo 199806 343379 := bstep (se 1 (by rfl) ⟨257534, by rfl⟩ : syracuseStep 343379 = 515069) B515069
theorem B343507 : Blo 199806 343507 := bstep (se 1 (by rfl) ⟨257630, by rfl⟩ : syracuseStep 343507 = 515261) B515261
theorem B343649 : Blo 199806 343649 := bstep (se 2 (by rfl) ⟨128868, by rfl⟩ : syracuseStep 343649 = 257737) B257737
theorem B507505 : Blo 199806 507505 := bstep (se 2 (by rfl) ⟨190314, by rfl⟩ : syracuseStep 507505 = 380629) B380629
theorem B343667 : Blo 199806 343667 := bstep (se 1 (by rfl) ⟨257750, by rfl⟩ : syracuseStep 343667 = 515501) B515501
theorem B343777 : Blo 199806 343777 := bstep (se 2 (by rfl) ⟨128916, by rfl⟩ : syracuseStep 343777 = 257833) B257833
theorem B769763 : Blo 199806 769763 := bstep (se 1 (by rfl) ⟨577322, by rfl⟩ : syracuseStep 769763 = 1154645) B1154645
theorem B343811 : Blo 199806 343811 := bstep (se 1 (by rfl) ⟨257858, by rfl⟩ : syracuseStep 343811 = 515717) B515717
theorem B1294157 : Blo 199806 1294157 := bstep (se 3 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 1294157 = 485309) B485309
theorem B507779 : Blo 199806 507779 := bstep (se 1 (by rfl) ⟨380834, by rfl⟩ : syracuseStep 507779 = 761669) B761669
theorem B540611 : Blo 199806 540611 := bstep (se 1 (by rfl) ⟨405458, by rfl⟩ : syracuseStep 540611 = 810917) B810917
theorem B507971 : Blo 199806 507971 := bstep (se 1 (by rfl) ⟨380978, by rfl⟩ : syracuseStep 507971 = 761957) B761957
theorem B344243 : Blo 199806 344243 := bstep (se 1 (by rfl) ⟨258182, by rfl⟩ : syracuseStep 344243 = 516365) B516365
theorem B573713 : Blo 199806 573713 := bstep (se 2 (by rfl) ⟨215142, by rfl⟩ : syracuseStep 573713 = 430285) B430285
theorem B770417 : Blo 199806 770417 := bstep (se 2 (by rfl) ⟨288906, by rfl⟩ : syracuseStep 770417 = 577813) B577813
theorem B573905 : Blo 199806 573905 := bstep (se 2 (by rfl) ⟨215214, by rfl⟩ : syracuseStep 573905 = 430429) B430429
theorem B967373 : Blo 199806 967373 := bstep (se 3 (by rfl) ⟨181382, by rfl⟩ : syracuseStep 967373 = 362765) B362765
theorem B3687221 : Blo 199806 3687221 := bstep (se 5 (by rfl) ⟨172838, by rfl⟩ : syracuseStep 3687221 = 345677) B345677
theorem B541649 : Blo 199806 541649 := bstep (se 2 (by rfl) ⟨203118, by rfl⟩ : syracuseStep 541649 = 406237) B406237
theorem B508913 : Blo 199806 508913 := bstep (se 2 (by rfl) ⟨190842, by rfl⟩ : syracuseStep 508913 = 381685) B381685
theorem B508963 : Blo 199806 508963 := bstep (se 1 (by rfl) ⟨381722, by rfl⟩ : syracuseStep 508963 = 763445) B763445
theorem B1098865 : Blo 199806 1098865 := bstep (se 2 (by rfl) ⟨412074, by rfl⟩ : syracuseStep 1098865 = 824149) B824149
theorem B509105 : Blo 199806 509105 := bstep (se 2 (by rfl) ⟨190914, by rfl⟩ : syracuseStep 509105 = 381829) B381829
theorem B1557701 : Blo 199806 1557701 := bstep (se 4 (by rfl) ⟨146034, by rfl⟩ : syracuseStep 1557701 = 292069) B292069
theorem B640237 : Blo 199806 640237 := bstep (se 3 (by rfl) ⟨120044, by rfl⟩ : syracuseStep 640237 = 240089) B240089
theorem B574897 : Blo 199806 574897 := bstep (se 2 (by rfl) ⟨215586, by rfl⟩ : syracuseStep 574897 = 431173) B431173
theorem B2278853 : Blo 199806 2278853 := bstep (se 4 (by rfl) ⟨213642, by rfl⟩ : syracuseStep 2278853 = 427285) B427285
theorem B214531 : Blo 199806 214531 := bstep (se 1 (by rfl) ⟨160898, by rfl⟩ : syracuseStep 214531 = 321797) B321797
theorem B575171 : Blo 199806 575171 := bstep (se 1 (by rfl) ⟨431378, by rfl⟩ : syracuseStep 575171 = 862757) B862757
theorem B771875 : Blo 199806 771875 := bstep (se 1 (by rfl) ⟨578906, by rfl⟩ : syracuseStep 771875 = 1157813) B1157813
theorem B771889 : Blo 199806 771889 := bstep (se 2 (by rfl) ⟨289458, by rfl⟩ : syracuseStep 771889 = 578917) B578917
theorem B575363 : Blo 199806 575363 := bstep (se 1 (by rfl) ⟨431522, by rfl⟩ : syracuseStep 575363 = 863045) B863045
theorem B608141 : Blo 199806 608141 := bstep (se 3 (by rfl) ⟨114026, by rfl⟩ : syracuseStep 608141 = 228053) B228053
theorem B4769813 : Blo 199806 4769813 := bstep (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) B223585
theorem B346211 : Blo 199806 346211 := bstep (se 1 (by rfl) ⟨259658, by rfl⟩ : syracuseStep 346211 = 519317) B519317
theorem B510097 : Blo 199806 510097 := bstep (se 2 (by rfl) ⟨191286, by rfl⟩ : syracuseStep 510097 = 382573) B382573
theorem B510371 : Blo 199806 510371 := bstep (se 1 (by rfl) ⟨382778, by rfl⟩ : syracuseStep 510371 = 765557) B765557
theorem B608771 : Blo 199806 608771 := bstep (se 1 (by rfl) ⟨456578, by rfl⟩ : syracuseStep 608771 = 913157) B913157
theorem B510563 : Blo 199806 510563 := bstep (se 1 (by rfl) ⟨382922, by rfl⟩ : syracuseStep 510563 = 765845) B765845
theorem B379505 : Blo 199806 379505 := bstep (se 2 (by rfl) ⟨142314, by rfl⟩ : syracuseStep 379505 = 284629) B284629
theorem B2574989 : Blo 199806 2574989 := bstep (se 3 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 2574989 = 965621) B965621
theorem B576173 : Blo 199806 576173 := bstep (se 3 (by rfl) ⟨108032, by rfl⟩ : syracuseStep 576173 = 216065) B216065
theorem B871117 : Blo 199806 871117 := bstep (se 3 (by rfl) ⟨163334, by rfl⟩ : syracuseStep 871117 = 326669) B326669
theorem B674513 : Blo 199806 674513 := bstep (se 2 (by rfl) ⟨252942, by rfl⟩ : syracuseStep 674513 = 505885) B505885
theorem B9358037 : Blo 199806 9358037 := bstep (se 7 (by rfl) ⟨109664, by rfl⟩ : syracuseStep 9358037 = 219329) B219329
theorem B412465 : Blo 199806 412465 := bstep (se 2 (by rfl) ⟨154674, by rfl⟩ : syracuseStep 412465 = 309349) B309349
theorem B576355 : Blo 199806 576355 := bstep (se 1 (by rfl) ⟨432266, by rfl⟩ : syracuseStep 576355 = 864533) B864533
theorem B543725 : Blo 199806 543725 := bstep (se 3 (by rfl) ⟨101948, by rfl⟩ : syracuseStep 543725 = 203897) B203897
theorem B1527011 : Blo 199806 1527011 := bstep (se 1 (by rfl) ⟨1145258, by rfl⟩ : syracuseStep 1527011 = 2290517) B2290517
theorem B773347 : Blo 199806 773347 := bstep (se 1 (by rfl) ⟨580010, by rfl⟩ : syracuseStep 773347 = 1160021) B1160021
theorem B675053 : Blo 199806 675053 := bstep (se 3 (by rfl) ⟨126572, by rfl⟩ : syracuseStep 675053 = 253145) B253145
theorem B675107 : Blo 199806 675107 := bstep (se 1 (by rfl) ⟨506330, by rfl⟩ : syracuseStep 675107 = 1012661) B1012661
theorem B380227 : Blo 199806 380227 := bstep (se 1 (by rfl) ⟨285170, by rfl⟩ : syracuseStep 380227 = 570341) B570341
theorem B576845 : Blo 199806 576845 := bstep (se 3 (by rfl) ⟨108158, by rfl⟩ : syracuseStep 576845 = 216317) B216317
theorem B511505 : Blo 199806 511505 := bstep (se 2 (by rfl) ⟨191814, by rfl⟩ : syracuseStep 511505 = 383629) B383629
theorem B675377 : Blo 199806 675377 := bstep (se 2 (by rfl) ⟨253266, by rfl⟩ : syracuseStep 675377 = 506533) B506533
theorem B511555 : Blo 199806 511555 := bstep (se 1 (by rfl) ⟨383666, by rfl⟩ : syracuseStep 511555 = 767333) B767333
theorem B511697 : Blo 199806 511697 := bstep (se 2 (by rfl) ⟨191886, by rfl⟩ : syracuseStep 511697 = 383773) B383773
theorem B5557987 : Blo 199806 5557987 := bstep (se 1 (by rfl) ⟨4168490, by rfl⟩ : syracuseStep 5557987 = 8336981) B8336981
theorem B380675 : Blo 199806 380675 := bstep (se 1 (by rfl) ⟨285506, by rfl⟩ : syracuseStep 380675 = 571013) B571013
theorem B380963 : Blo 199806 380963 := bstep (se 1 (by rfl) ⟨285722, by rfl⟩ : syracuseStep 380963 = 571445) B571445
theorem B675917 : Blo 199806 675917 := bstep (se 3 (by rfl) ⟨126734, by rfl⟩ : syracuseStep 675917 = 253469) B253469
theorem B217171 : Blo 199806 217171 := bstep (se 1 (by rfl) ⟨162878, by rfl⟩ : syracuseStep 217171 = 325757) B325757
theorem B675971 : Blo 199806 675971 := bstep (se 1 (by rfl) ⟨506978, by rfl⟩ : syracuseStep 675971 = 1013957) B1013957
theorem B2609333 : Blo 199806 2609333 := bstep (se 5 (by rfl) ⟨122312, by rfl⟩ : syracuseStep 2609333 = 244625) B244625
theorem B3133637 : Blo 199806 3133637 := bstep (se 4 (by rfl) ⟨293778, by rfl⟩ : syracuseStep 3133637 = 587557) B587557
theorem B1069283 : Blo 199806 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B610669 : Blo 199806 610669 := bstep (se 3 (by rfl) ⟨114500, by rfl⟩ : syracuseStep 610669 = 229001) B229001
theorem B676241 : Blo 199806 676241 := bstep (se 2 (by rfl) ⟨253590, by rfl⟩ : syracuseStep 676241 = 507181) B507181
theorem B578029 : Blo 199806 578029 := bstep (se 3 (by rfl) ⟨108380, by rfl⟩ : syracuseStep 578029 = 216761) B216761
theorem B217603 : Blo 199806 217603 := bstep (se 1 (by rfl) ⟨163202, by rfl⟩ : syracuseStep 217603 = 326405) B326405
theorem B643697 : Blo 199806 643697 := bstep (se 2 (by rfl) ⟨241386, by rfl⟩ : syracuseStep 643697 = 482773) B482773
theorem B512689 : Blo 199806 512689 := bstep (se 2 (by rfl) ⟨192258, by rfl⟩ : syracuseStep 512689 = 384517) B384517
theorem B1168141 : Blo 199806 1168141 := bstep (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) B438053
theorem B643889 : Blo 199806 643889 := bstep (se 2 (by rfl) ⟨241458, by rfl⟩ : syracuseStep 643889 = 482917) B482917
theorem B676781 : Blo 199806 676781 := bstep (se 3 (by rfl) ⟨126896, by rfl⟩ : syracuseStep 676781 = 253793) B253793
theorem B512963 : Blo 199806 512963 := bstep (se 1 (by rfl) ⟨384722, by rfl⟩ : syracuseStep 512963 = 769445) B769445
theorem B381905 : Blo 199806 381905 := bstep (se 2 (by rfl) ⟨143214, by rfl⟩ : syracuseStep 381905 = 286429) B286429
theorem B676835 : Blo 199806 676835 := bstep (se 1 (by rfl) ⟨507626, by rfl⟩ : syracuseStep 676835 = 1015253) B1015253
theorem B1463309 : Blo 199806 1463309 := bstep (se 3 (by rfl) ⟨274370, by rfl⟩ : syracuseStep 1463309 = 548741) B548741
theorem B218195 : Blo 199806 218195 := bstep (se 1 (by rfl) ⟨163646, by rfl⟩ : syracuseStep 218195 = 327293) B327293
theorem B513155 : Blo 199806 513155 := bstep (se 1 (by rfl) ⟨384866, by rfl⟩ : syracuseStep 513155 = 769733) B769733
theorem B939235 : Blo 199806 939235 := bstep (se 1 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 939235 = 1408853) B1408853
theorem B677105 : Blo 199806 677105 := bstep (se 2 (by rfl) ⟨253914, by rfl⟩ : syracuseStep 677105 = 507829) B507829
theorem B578897 : Blo 199806 578897 := bstep (se 2 (by rfl) ⟨217086, by rfl⟩ : syracuseStep 578897 = 434173) B434173
theorem B218611 : Blo 199806 218611 := bstep (se 1 (by rfl) ⟨163958, by rfl⟩ : syracuseStep 218611 = 327917) B327917
theorem B579089 : Blo 199806 579089 := bstep (se 2 (by rfl) ⟨217158, by rfl⟩ : syracuseStep 579089 = 434317) B434317
theorem B677645 : Blo 199806 677645 := bstep (se 3 (by rfl) ⟨127058, by rfl⟩ : syracuseStep 677645 = 254117) B254117
theorem B677699 : Blo 199806 677699 := bstep (se 1 (by rfl) ⟨508274, by rfl⟩ : syracuseStep 677699 = 1016549) B1016549
theorem B382801 : Blo 199806 382801 := bstep (se 2 (by rfl) ⟨143550, by rfl⟩ : syracuseStep 382801 = 287101) B287101
theorem B382961 : Blo 199806 382961 := bstep (se 2 (by rfl) ⟨143610, by rfl⟩ : syracuseStep 382961 = 287221) B287221
theorem B514097 : Blo 199806 514097 := bstep (se 2 (by rfl) ⟨192786, by rfl⟩ : syracuseStep 514097 = 385573) B385573
theorem B677969 : Blo 199806 677969 := bstep (se 2 (by rfl) ⟨254238, by rfl⟩ : syracuseStep 677969 = 508477) B508477
theorem B514147 : Blo 199806 514147 := bstep (se 1 (by rfl) ⟨385610, by rfl⟩ : syracuseStep 514147 = 771221) B771221
theorem B579761 : Blo 199806 579761 := bstep (se 2 (by rfl) ⟨217410, by rfl⟩ : syracuseStep 579761 = 434821) B434821
theorem B284897 : Blo 199806 284897 := bstep (se 2 (by rfl) ⟨106836, by rfl⟩ : syracuseStep 284897 = 213673) B213673
theorem B612593 : Blo 199806 612593 := bstep (se 2 (by rfl) ⟨229722, by rfl⟩ : syracuseStep 612593 = 459445) B459445
theorem B514289 : Blo 199806 514289 := bstep (se 2 (by rfl) ⟨192858, by rfl⟩ : syracuseStep 514289 = 385717) B385717
theorem B514307 : Blo 199806 514307 := bstep (se 1 (by rfl) ⟨385730, by rfl⟩ : syracuseStep 514307 = 771461) B771461
theorem B383363 : Blo 199806 383363 := bstep (se 1 (by rfl) ⟨287522, by rfl⟩ : syracuseStep 383363 = 575045) B575045
theorem B678509 : Blo 199806 678509 := bstep (se 3 (by rfl) ⟨127220, by rfl⟩ : syracuseStep 678509 = 254441) B254441
theorem B580259 : Blo 199806 580259 := bstep (se 1 (by rfl) ⟨435194, by rfl⟩ : syracuseStep 580259 = 870389) B870389
theorem B678563 : Blo 199806 678563 := bstep (se 1 (by rfl) ⟨508922, by rfl⟩ : syracuseStep 678563 = 1017845) B1017845
theorem B776881 : Blo 199806 776881 := bstep (se 2 (by rfl) ⟨291330, by rfl⟩ : syracuseStep 776881 = 582661) B582661
theorem B1301197 : Blo 199806 1301197 := bstep (se 3 (by rfl) ⟨243974, by rfl⟩ : syracuseStep 1301197 = 487949) B487949
theorem B547661 : Blo 199806 547661 := bstep (se 3 (by rfl) ⟨102686, by rfl⟩ : syracuseStep 547661 = 205373) B205373
theorem B678833 : Blo 199806 678833 := bstep (se 2 (by rfl) ⟨254562, by rfl⟩ : syracuseStep 678833 = 509125) B509125
theorem B646157 : Blo 199806 646157 := bstep (se 3 (by rfl) ⟨121154, by rfl⟩ : syracuseStep 646157 = 242309) B242309
theorem B449585 : Blo 199806 449585 := bstep (se 2 (by rfl) ⟨168594, by rfl⟩ : syracuseStep 449585 = 337189) B337189
theorem B449603 : Blo 199806 449603 := bstep (se 1 (by rfl) ⟨337202, by rfl⟩ : syracuseStep 449603 = 674405) B674405
theorem B285763 : Blo 199806 285763 := bstep (se 1 (by rfl) ⟨214322, by rfl⟩ : syracuseStep 285763 = 428645) B428645
theorem B515153 : Blo 199806 515153 := bstep (se 2 (by rfl) ⟨193182, by rfl⟩ : syracuseStep 515153 = 386365) B386365
theorem B2284685 : Blo 199806 2284685 := bstep (se 3 (by rfl) ⟨428378, by rfl⟩ : syracuseStep 2284685 = 856757) B856757
theorem B285859 : Blo 199806 285859 := bstep (se 1 (by rfl) ⟨214394, by rfl⟩ : syracuseStep 285859 = 428789) B428789
theorem B515281 : Blo 199806 515281 := bstep (se 2 (by rfl) ⟨193230, by rfl⟩ : syracuseStep 515281 = 386461) B386461
theorem B384259 : Blo 199806 384259 := bstep (se 1 (by rfl) ⟨288194, by rfl⟩ : syracuseStep 384259 = 576389) B576389
theorem B810253 : Blo 199806 810253 := bstep (se 3 (by rfl) ⟨151922, by rfl⟩ : syracuseStep 810253 = 303845) B303845
theorem B449873 : Blo 199806 449873 := bstep (se 2 (by rfl) ⟨168702, by rfl⟩ : syracuseStep 449873 = 337405) B337405
theorem B449891 : Blo 199806 449891 := bstep (se 1 (by rfl) ⟨337418, by rfl⟩ : syracuseStep 449891 = 674837) B674837
theorem B3300749 : Blo 199806 3300749 := bstep (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) B1237781
theorem B384419 : Blo 199806 384419 := bstep (se 1 (by rfl) ⟨288314, by rfl⟩ : syracuseStep 384419 = 576629) B576629
theorem B253363 : Blo 199806 253363 := bstep (se 1 (by rfl) ⟨190022, by rfl⟩ : syracuseStep 253363 = 380045) B380045
theorem B679373 : Blo 199806 679373 := bstep (se 3 (by rfl) ⟨127382, by rfl⟩ : syracuseStep 679373 = 254765) B254765
theorem B515555 : Blo 199806 515555 := bstep (se 1 (by rfl) ⟨386666, by rfl⟩ : syracuseStep 515555 = 773333) B773333
theorem B679427 : Blo 199806 679427 := bstep (se 1 (by rfl) ⟨509570, by rfl⟩ : syracuseStep 679427 = 1019141) B1019141
theorem B253459 : Blo 199806 253459 := bstep (se 1 (by rfl) ⟨190094, by rfl⟩ : syracuseStep 253459 = 380189) B380189
theorem B613955 : Blo 199806 613955 := bstep (se 1 (by rfl) ⟨460466, by rfl⟩ : syracuseStep 613955 = 920933) B920933
theorem B450161 : Blo 199806 450161 := bstep (se 2 (by rfl) ⟨168810, by rfl⟩ : syracuseStep 450161 = 337621) B337621
theorem B450179 : Blo 199806 450179 := bstep (se 1 (by rfl) ⟨337634, by rfl⟩ : syracuseStep 450179 = 675269) B675269
theorem B286355 : Blo 199806 286355 := bstep (se 1 (by rfl) ⟨214766, by rfl⟩ : syracuseStep 286355 = 429533) B429533
theorem B515747 : Blo 199806 515747 := bstep (se 1 (by rfl) ⟨386810, by rfl⟩ : syracuseStep 515747 = 773621) B773621
theorem B1302257 : Blo 199806 1302257 := bstep (se 2 (by rfl) ⟨488346, by rfl⟩ : syracuseStep 1302257 = 976693) B976693
theorem B679697 : Blo 199806 679697 := bstep (se 2 (by rfl) ⟨254886, by rfl⟩ : syracuseStep 679697 = 509773) B509773
theorem B548657 : Blo 199806 548657 := bstep (se 2 (by rfl) ⟨205746, by rfl⟩ : syracuseStep 548657 = 411493) B411493
theorem B221059 : Blo 199806 221059 := bstep (se 1 (by rfl) ⟨165794, by rfl⟩ : syracuseStep 221059 = 331589) B331589
theorem B450449 : Blo 199806 450449 := bstep (se 2 (by rfl) ⟨168918, by rfl⟩ : syracuseStep 450449 = 337837) B337837
theorem B450467 : Blo 199806 450467 := bstep (se 1 (by rfl) ⟨337850, by rfl⟩ : syracuseStep 450467 = 675701) B675701
theorem B253955 : Blo 199806 253955 := bstep (se 1 (by rfl) ⟨190466, by rfl⟩ : syracuseStep 253955 = 380933) B380933
theorem B450737 : Blo 199806 450737 := bstep (se 2 (by rfl) ⟨169026, by rfl⟩ : syracuseStep 450737 = 338053) B338053
theorem B450755 : Blo 199806 450755 := bstep (se 1 (by rfl) ⟨338066, by rfl⟩ : syracuseStep 450755 = 676133) B676133
theorem B286993 : Blo 199806 286993 := bstep (se 2 (by rfl) ⟨107622, by rfl⟩ : syracuseStep 286993 = 215245) B215245
theorem B680237 : Blo 199806 680237 := bstep (se 3 (by rfl) ⟨127544, by rfl⟩ : syracuseStep 680237 = 255089) B255089
theorem B680291 : Blo 199806 680291 := bstep (se 1 (by rfl) ⟨510218, by rfl⟩ : syracuseStep 680291 = 1020437) B1020437
theorem B1532357 : Blo 199806 1532357 := bstep (se 4 (by rfl) ⟨143658, by rfl⟩ : syracuseStep 1532357 = 287317) B287317
theorem B451025 : Blo 199806 451025 := bstep (se 2 (by rfl) ⟨169134, by rfl⟩ : syracuseStep 451025 = 338269) B338269
theorem B385489 : Blo 199806 385489 := bstep (se 2 (by rfl) ⟨144558, by rfl⟩ : syracuseStep 385489 = 289117) B289117
theorem B451043 : Blo 199806 451043 := bstep (se 1 (by rfl) ⟨338282, by rfl⟩ : syracuseStep 451043 = 676565) B676565
theorem B549347 : Blo 199806 549347 := bstep (se 1 (by rfl) ⟨412010, by rfl⟩ : syracuseStep 549347 = 824021) B824021
theorem B647747 : Blo 199806 647747 := bstep (se 1 (by rfl) ⟨485810, by rfl⟩ : syracuseStep 647747 = 971621) B971621
theorem B287329 : Blo 199806 287329 := bstep (se 2 (by rfl) ⟨107748, by rfl⟩ : syracuseStep 287329 = 215497) B215497
theorem B680561 : Blo 199806 680561 := bstep (se 2 (by rfl) ⟨255210, by rfl⟩ : syracuseStep 680561 = 510421) B510421
theorem B1237637 : Blo 199806 1237637 := bstep (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) B232057
theorem B975523 : Blo 199806 975523 := bstep (se 1 (by rfl) ⟨731642, by rfl⟩ : syracuseStep 975523 = 1463285) B1463285
theorem B254659 : Blo 199806 254659 := bstep (se 1 (by rfl) ⟨190994, by rfl⟩ : syracuseStep 254659 = 381989) B381989
theorem B451313 : Blo 199806 451313 := bstep (se 2 (by rfl) ⟨169242, by rfl⟩ : syracuseStep 451313 = 338485) B338485
theorem B451331 : Blo 199806 451331 := bstep (se 1 (by rfl) ⟨338498, by rfl⟩ : syracuseStep 451331 = 676997) B676997
theorem B254755 : Blo 199806 254755 := bstep (se 1 (by rfl) ⟨191066, by rfl⟩ : syracuseStep 254755 = 382133) B382133
theorem B4350833 : Blo 199806 4350833 := bstep (se 2 (by rfl) ⟨1631562, by rfl⟩ : syracuseStep 4350833 = 3263125) B3263125
theorem B451601 : Blo 199806 451601 := bstep (se 2 (by rfl) ⟨169350, by rfl⟩ : syracuseStep 451601 = 338701) B338701
theorem B451619 : Blo 199806 451619 := bstep (se 1 (by rfl) ⟨338714, by rfl⟩ : syracuseStep 451619 = 677429) B677429
theorem B320593 : Blo 199806 320593 := bstep (se 2 (by rfl) ⟨120222, by rfl⟩ : syracuseStep 320593 = 240445) B240445
theorem B681101 : Blo 199806 681101 := bstep (se 3 (by rfl) ⟨127706, by rfl⟩ : syracuseStep 681101 = 255413) B255413
theorem B287921 : Blo 199806 287921 := bstep (se 2 (by rfl) ⟨107970, by rfl⟩ : syracuseStep 287921 = 215941) B215941
theorem B681155 : Blo 199806 681155 := bstep (se 1 (by rfl) ⟨510866, by rfl⟩ : syracuseStep 681155 = 1021733) B1021733
theorem B255251 : Blo 199806 255251 := bstep (se 1 (by rfl) ⟨191438, by rfl⟩ : syracuseStep 255251 = 382877) B382877
theorem B451889 : Blo 199806 451889 := bstep (se 2 (by rfl) ⟨169458, by rfl⟩ : syracuseStep 451889 = 338917) B338917
theorem B451907 : Blo 199806 451907 := bstep (se 1 (by rfl) ⟨338930, by rfl⟩ : syracuseStep 451907 = 677861) B677861
theorem B1402181 : Blo 199806 1402181 := bstep (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) B262909
theorem B320849 : Blo 199806 320849 := bstep (se 2 (by rfl) ⟨120318, by rfl⟩ : syracuseStep 320849 = 240637) B240637
theorem B648643 : Blo 199806 648643 := bstep (se 1 (by rfl) ⟨486482, by rfl⟩ : syracuseStep 648643 = 972965) B972965
theorem B681425 : Blo 199806 681425 := bstep (se 2 (by rfl) ⟨255534, by rfl⟩ : syracuseStep 681425 = 511069) B511069
theorem B386545 : Blo 199806 386545 := bstep (se 2 (by rfl) ⟨144954, by rfl⟩ : syracuseStep 386545 = 289909) B289909
theorem B321041 : Blo 199806 321041 := bstep (se 2 (by rfl) ⟨120390, by rfl⟩ : syracuseStep 321041 = 240781) B240781
theorem B452177 : Blo 199806 452177 := bstep (se 2 (by rfl) ⟨169566, by rfl⟩ : syracuseStep 452177 = 339133) B339133
theorem B452195 : Blo 199806 452195 := bstep (se 1 (by rfl) ⟨339146, by rfl⟩ : syracuseStep 452195 = 678293) B678293
theorem B288451 : Blo 199806 288451 := bstep (se 1 (by rfl) ⟨216338, by rfl⟩ : syracuseStep 288451 = 432677) B432677
theorem B452465 : Blo 199806 452465 := bstep (se 2 (by rfl) ⟨169674, by rfl⟩ : syracuseStep 452465 = 339349) B339349
theorem B452483 : Blo 199806 452483 := bstep (se 1 (by rfl) ⟨339362, by rfl⟩ : syracuseStep 452483 = 678725) B678725
theorem B780209 : Blo 199806 780209 := bstep (se 2 (by rfl) ⟨292578, by rfl⟩ : syracuseStep 780209 = 585157) B585157
theorem B255955 : Blo 199806 255955 := bstep (se 1 (by rfl) ⟨191966, by rfl⟩ : syracuseStep 255955 = 383933) B383933
theorem B681965 : Blo 199806 681965 := bstep (se 3 (by rfl) ⟨127868, by rfl⟩ : syracuseStep 681965 = 255737) B255737
theorem B2287601 : Blo 199806 2287601 := bstep (se 2 (by rfl) ⟨857850, by rfl⟩ : syracuseStep 2287601 = 1715701) B1715701
theorem B1140749 : Blo 199806 1140749 := bstep (se 3 (by rfl) ⟨213890, by rfl⟩ : syracuseStep 1140749 = 427781) B427781
theorem B288787 : Blo 199806 288787 := bstep (se 1 (by rfl) ⟨216590, by rfl⟩ : syracuseStep 288787 = 433181) B433181
theorem B682019 : Blo 199806 682019 := bstep (se 1 (by rfl) ⟨511514, by rfl⟩ : syracuseStep 682019 = 1023029) B1023029
theorem B256051 : Blo 199806 256051 := bstep (se 1 (by rfl) ⟨192038, by rfl⟩ : syracuseStep 256051 = 384077) B384077
theorem B616547 : Blo 199806 616547 := bstep (se 1 (by rfl) ⟨462410, by rfl⟩ : syracuseStep 616547 = 924821) B924821
theorem B452753 : Blo 199806 452753 := bstep (se 2 (by rfl) ⟨169782, by rfl⟩ : syracuseStep 452753 = 339565) B339565
theorem B452771 : Blo 199806 452771 := bstep (se 1 (by rfl) ⟨339578, by rfl⟩ : syracuseStep 452771 = 679157) B679157
theorem B616643 : Blo 199806 616643 := bstep (se 1 (by rfl) ⟨462482, by rfl⟩ : syracuseStep 616643 = 924965) B924965
theorem B1239245 : Blo 199806 1239245 := bstep (se 3 (by rfl) ⟨232358, by rfl⟩ : syracuseStep 1239245 = 464717) B464717
theorem B485617 : Blo 199806 485617 := bstep (se 2 (by rfl) ⟨182106, by rfl⟩ : syracuseStep 485617 = 364213) B364213
theorem B682289 : Blo 199806 682289 := bstep (se 2 (by rfl) ⟨255858, by rfl⟩ : syracuseStep 682289 = 511717) B511717
theorem B453041 : Blo 199806 453041 := bstep (se 2 (by rfl) ⟨169890, by rfl⟩ : syracuseStep 453041 = 339781) B339781
theorem B453059 : Blo 199806 453059 := bstep (se 1 (by rfl) ⟨339794, by rfl⟩ : syracuseStep 453059 = 679589) B679589
theorem B1370609 : Blo 199806 1370609 := bstep (se 2 (by rfl) ⟨513978, by rfl⟩ : syracuseStep 1370609 = 1027957) B1027957
theorem B649745 : Blo 199806 649745 := bstep (se 2 (by rfl) ⟨243654, by rfl⟩ : syracuseStep 649745 = 487309) B487309
theorem B256547 : Blo 199806 256547 := bstep (se 1 (by rfl) ⟨192410, by rfl⟩ : syracuseStep 256547 = 384821) B384821
theorem B289345 : Blo 199806 289345 := bstep (se 2 (by rfl) ⟨108504, by rfl⟩ : syracuseStep 289345 = 217009) B217009
theorem B289379 : Blo 199806 289379 := bstep (se 1 (by rfl) ⟨217034, by rfl⟩ : syracuseStep 289379 = 434069) B434069
theorem B977521 : Blo 199806 977521 := bstep (se 2 (by rfl) ⟨366570, by rfl⟩ : syracuseStep 977521 = 733141) B733141
theorem B1305229 : Blo 199806 1305229 := bstep (se 3 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 1305229 = 489461) B489461
theorem B649873 : Blo 199806 649873 := bstep (se 2 (by rfl) ⟨243702, by rfl⟩ : syracuseStep 649873 = 487405) B487405
theorem B453329 : Blo 199806 453329 := bstep (se 2 (by rfl) ⟨169998, by rfl⟩ : syracuseStep 453329 = 339997) B339997
theorem B453347 : Blo 199806 453347 := bstep (se 1 (by rfl) ⟨340010, by rfl⟩ : syracuseStep 453347 = 680021) B680021
theorem B322355 : Blo 199806 322355 := bstep (se 1 (by rfl) ⟨241766, by rfl⟩ : syracuseStep 322355 = 483533) B483533
theorem B813901 : Blo 199806 813901 := bstep (se 3 (by rfl) ⟨152606, by rfl⟩ : syracuseStep 813901 = 305213) B305213
theorem B682829 : Blo 199806 682829 := bstep (se 3 (by rfl) ⟨128030, by rfl⟩ : syracuseStep 682829 = 256061) B256061
theorem B682883 : Blo 199806 682883 := bstep (se 1 (by rfl) ⟨512162, by rfl⟩ : syracuseStep 682883 = 1024325) B1024325
theorem B453617 : Blo 199806 453617 := bstep (se 2 (by rfl) ⟨170106, by rfl⟩ : syracuseStep 453617 = 340213) B340213
theorem B453635 : Blo 199806 453635 := bstep (se 1 (by rfl) ⟨340226, by rfl⟩ : syracuseStep 453635 = 680453) B680453
theorem B322579 : Blo 199806 322579 := bstep (se 1 (by rfl) ⟨241934, by rfl⟩ : syracuseStep 322579 = 483869) B483869
theorem B322643 : Blo 199806 322643 := bstep (se 1 (by rfl) ⟨241982, by rfl⟩ : syracuseStep 322643 = 483965) B483965
theorem B683153 : Blo 199806 683153 := bstep (se 2 (by rfl) ⟨256182, by rfl⟩ : syracuseStep 683153 = 512365) B512365
theorem B289937 : Blo 199806 289937 := bstep (se 2 (by rfl) ⟨108726, by rfl⟩ : syracuseStep 289937 = 217453) B217453
theorem B322771 : Blo 199806 322771 := bstep (se 1 (by rfl) ⟨242078, by rfl⟩ : syracuseStep 322771 = 484157) B484157
theorem B290017 : Blo 199806 290017 := bstep (se 2 (by rfl) ⟨108756, by rfl⟩ : syracuseStep 290017 = 217513) B217513
theorem B257251 : Blo 199806 257251 := bstep (se 1 (by rfl) ⟨192938, by rfl⟩ : syracuseStep 257251 = 385877) B385877
theorem B453905 : Blo 199806 453905 := bstep (se 2 (by rfl) ⟨170214, by rfl⟩ : syracuseStep 453905 = 340429) B340429
theorem B453923 : Blo 199806 453923 := bstep (se 1 (by rfl) ⟨340442, by rfl⟩ : syracuseStep 453923 = 680885) B680885
theorem B257347 : Blo 199806 257347 := bstep (se 1 (by rfl) ⟨193010, by rfl⟩ : syracuseStep 257347 = 386021) B386021
theorem B454193 : Blo 199806 454193 := bstep (se 2 (by rfl) ⟨170322, by rfl⟩ : syracuseStep 454193 = 340645) B340645
theorem B454211 : Blo 199806 454211 := bstep (se 1 (by rfl) ⟨340658, by rfl⟩ : syracuseStep 454211 = 681317) B681317
theorem B224851 : Blo 199806 224851 := bstep (se 1 (by rfl) ⟨168638, by rfl⟩ : syracuseStep 224851 = 337277) B337277
theorem B650861 : Blo 199806 650861 := bstep (se 3 (by rfl) ⟨122036, by rfl⟩ : syracuseStep 650861 = 244073) B244073
theorem B683693 : Blo 199806 683693 := bstep (se 3 (by rfl) ⟨128192, by rfl⟩ : syracuseStep 683693 = 256385) B256385
theorem B224995 : Blo 199806 224995 := bstep (se 1 (by rfl) ⟨168746, by rfl⟩ : syracuseStep 224995 = 337493) B337493
theorem B683747 : Blo 199806 683747 := bstep (se 1 (by rfl) ⟨512810, by rfl⟩ : syracuseStep 683747 = 1025621) B1025621
theorem B257843 : Blo 199806 257843 := bstep (se 1 (by rfl) ⟨193382, by rfl⟩ : syracuseStep 257843 = 386765) B386765
theorem B454481 : Blo 199806 454481 := bstep (se 2 (by rfl) ⟨170430, by rfl⟩ : syracuseStep 454481 = 340861) B340861
theorem B454499 : Blo 199806 454499 := bstep (se 1 (by rfl) ⟨340874, by rfl⟩ : syracuseStep 454499 = 681749) B681749
theorem B225139 : Blo 199806 225139 := bstep (se 1 (by rfl) ⟨168854, by rfl⟩ : syracuseStep 225139 = 337709) B337709
theorem B323489 : Blo 199806 323489 := bstep (se 2 (by rfl) ⟨121308, by rfl⟩ : syracuseStep 323489 = 242617) B242617
theorem B683981 : Blo 199806 683981 := bstep (se 3 (by rfl) ⟨128246, by rfl⟩ : syracuseStep 683981 = 256493) B256493
theorem B684017 : Blo 199806 684017 := bstep (se 2 (by rfl) ⟨256506, by rfl⟩ : syracuseStep 684017 = 513013) B513013
theorem B225283 : Blo 199806 225283 := bstep (se 1 (by rfl) ⟨168962, by rfl⟩ : syracuseStep 225283 = 337925) B337925
theorem B552977 : Blo 199806 552977 := bstep (se 2 (by rfl) ⟨207366, by rfl⟩ : syracuseStep 552977 = 414733) B414733
theorem B323617 : Blo 199806 323617 := bstep (se 2 (by rfl) ⟨121356, by rfl⟩ : syracuseStep 323617 = 242713) B242713
theorem B454769 : Blo 199806 454769 := bstep (se 2 (by rfl) ⟨170538, by rfl⟩ : syracuseStep 454769 = 341077) B341077
theorem B454787 : Blo 199806 454787 := bstep (se 1 (by rfl) ⟨341090, by rfl⟩ : syracuseStep 454787 = 682181) B682181
theorem B4321421 : Blo 199806 4321421 := bstep (se 3 (by rfl) ⟨810266, by rfl⟩ : syracuseStep 4321421 = 1620533) B1620533
theorem B225427 : Blo 199806 225427 := bstep (se 1 (by rfl) ⟨169070, by rfl⟩ : syracuseStep 225427 = 338141) B338141
theorem B1142981 : Blo 199806 1142981 := bstep (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) B214309
theorem B225571 : Blo 199806 225571 := bstep (se 1 (by rfl) ⟨169178, by rfl⟩ : syracuseStep 225571 = 338357) B338357
theorem B455057 : Blo 199806 455057 := bstep (se 2 (by rfl) ⟨170646, by rfl⟩ : syracuseStep 455057 = 341293) B341293
theorem B324001 : Blo 199806 324001 := bstep (se 2 (by rfl) ⟨121500, by rfl⟩ : syracuseStep 324001 = 243001) B243001
theorem B455075 : Blo 199806 455075 := bstep (se 1 (by rfl) ⟨341306, by rfl⟩ : syracuseStep 455075 = 682613) B682613
theorem B225715 : Blo 199806 225715 := bstep (se 1 (by rfl) ⟨169286, by rfl⟩ : syracuseStep 225715 = 338573) B338573
theorem B684557 : Blo 199806 684557 := bstep (se 3 (by rfl) ⟨128354, by rfl⟩ : syracuseStep 684557 = 256709) B256709
theorem B225859 : Blo 199806 225859 := bstep (se 1 (by rfl) ⟨169394, by rfl⟩ : syracuseStep 225859 = 338789) B338789
theorem B684611 : Blo 199806 684611 := bstep (se 1 (by rfl) ⟨513458, by rfl⟩ : syracuseStep 684611 = 1026917) B1026917
theorem B1012337 : Blo 199806 1012337 := bstep (se 2 (by rfl) ⟨379626, by rfl⟩ : syracuseStep 1012337 = 759253) B759253
theorem B324257 : Blo 199806 324257 := bstep (se 2 (by rfl) ⟨121596, by rfl⟩ : syracuseStep 324257 = 243193) B243193
theorem B455345 : Blo 199806 455345 := bstep (se 2 (by rfl) ⟨170754, by rfl⟩ : syracuseStep 455345 = 341509) B341509
theorem B455363 : Blo 199806 455363 := bstep (se 1 (by rfl) ⟨341522, by rfl⟩ : syracuseStep 455363 = 683045) B683045
theorem B226003 : Blo 199806 226003 := bstep (se 1 (by rfl) ⟨169502, by rfl⟩ : syracuseStep 226003 = 339005) B339005
theorem B389873 : Blo 199806 389873 := bstep (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) B292405
theorem B684881 : Blo 199806 684881 := bstep (se 2 (by rfl) ⟨256830, by rfl⟩ : syracuseStep 684881 = 513661) B513661
theorem B226147 : Blo 199806 226147 := bstep (se 1 (by rfl) ⟨169610, by rfl⟩ : syracuseStep 226147 = 339221) B339221
theorem B1143665 : Blo 199806 1143665 := bstep (se 2 (by rfl) ⟨428874, by rfl⟩ : syracuseStep 1143665 = 857749) B857749
theorem B652205 : Blo 199806 652205 := bstep (se 3 (by rfl) ⟨122288, by rfl⟩ : syracuseStep 652205 = 244577) B244577
theorem B455633 : Blo 199806 455633 := bstep (se 2 (by rfl) ⟨170862, by rfl⟩ : syracuseStep 455633 = 341725) B341725
theorem B455651 : Blo 199806 455651 := bstep (se 1 (by rfl) ⟨341738, by rfl⟩ : syracuseStep 455651 = 683477) B683477
theorem B226291 : Blo 199806 226291 := bstep (se 1 (by rfl) ⟨169718, by rfl⟩ : syracuseStep 226291 = 339437) B339437
theorem B226435 : Blo 199806 226435 := bstep (se 1 (by rfl) ⟨169826, by rfl⟩ : syracuseStep 226435 = 339653) B339653
theorem B619757 : Blo 199806 619757 := bstep (se 3 (by rfl) ⟨116204, by rfl⟩ : syracuseStep 619757 = 232409) B232409
theorem B455921 : Blo 199806 455921 := bstep (se 2 (by rfl) ⟨170970, by rfl⟩ : syracuseStep 455921 = 341941) B341941
theorem B455939 : Blo 199806 455939 := bstep (se 1 (by rfl) ⟨341954, by rfl⟩ : syracuseStep 455939 = 683909) B683909
theorem B226579 : Blo 199806 226579 := bstep (se 1 (by rfl) ⟨169934, by rfl⟩ : syracuseStep 226579 = 339869) B339869
theorem B685421 : Blo 199806 685421 := bstep (se 3 (by rfl) ⟨128516, by rfl⟩ : syracuseStep 685421 = 257033) B257033
theorem B226723 : Blo 199806 226723 := bstep (se 1 (by rfl) ⟨170042, by rfl⟩ : syracuseStep 226723 = 340085) B340085
theorem B685475 : Blo 199806 685475 := bstep (se 1 (by rfl) ⟨514106, by rfl⟩ : syracuseStep 685475 = 1028213) B1028213
theorem B587213 : Blo 199806 587213 := bstep (se 3 (by rfl) ⟨110102, by rfl⟩ : syracuseStep 587213 = 220205) B220205
theorem B456209 : Blo 199806 456209 := bstep (se 2 (by rfl) ⟨171078, by rfl⟩ : syracuseStep 456209 = 342157) B342157
theorem B456227 : Blo 199806 456227 := bstep (se 1 (by rfl) ⟨342170, by rfl⟩ : syracuseStep 456227 = 684341) B684341
theorem B226867 : Blo 199806 226867 := bstep (se 1 (by rfl) ⟨170150, by rfl⟩ : syracuseStep 226867 = 340301) B340301
theorem B685745 : Blo 199806 685745 := bstep (se 2 (by rfl) ⟨257154, by rfl⟩ : syracuseStep 685745 = 514309) B514309
theorem B227011 : Blo 199806 227011 := bstep (se 1 (by rfl) ⟨170258, by rfl⟩ : syracuseStep 227011 = 340517) B340517
theorem B554701 : Blo 199806 554701 := bstep (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) B208013
theorem B456497 : Blo 199806 456497 := bstep (se 2 (by rfl) ⟨171186, by rfl⟩ : syracuseStep 456497 = 342373) B342373
theorem B456515 : Blo 199806 456515 := bstep (se 1 (by rfl) ⟨342386, by rfl⟩ : syracuseStep 456515 = 684773) B684773
theorem B227155 : Blo 199806 227155 := bstep (se 1 (by rfl) ⟨170366, by rfl⟩ : syracuseStep 227155 = 340733) B340733
theorem B227299 : Blo 199806 227299 := bstep (se 1 (by rfl) ⟨170474, by rfl⟩ : syracuseStep 227299 = 340949) B340949
theorem B1013795 : Blo 199806 1013795 := bstep (se 1 (by rfl) ⟨760346, by rfl⟩ : syracuseStep 1013795 = 1520693) B1520693
theorem B915491 : Blo 199806 915491 := bstep (se 1 (by rfl) ⟨686618, by rfl⟩ : syracuseStep 915491 = 1373237) B1373237
theorem B325667 : Blo 199806 325667 := bstep (se 1 (by rfl) ⟨244250, by rfl⟩ : syracuseStep 325667 = 488501) B488501
theorem B489539 : Blo 199806 489539 := bstep (se 1 (by rfl) ⟨367154, by rfl⟩ : syracuseStep 489539 = 734309) B734309
theorem B456785 : Blo 199806 456785 := bstep (se 2 (by rfl) ⟨171294, by rfl⟩ : syracuseStep 456785 = 342589) B342589
theorem B1931363 : Blo 199806 1931363 := bstep (se 1 (by rfl) ⟨1448522, by rfl⟩ : syracuseStep 1931363 = 2897045) B2897045
theorem B456803 : Blo 199806 456803 := bstep (se 1 (by rfl) ⟨342602, by rfl⟩ : syracuseStep 456803 = 685205) B685205
theorem B227443 : Blo 199806 227443 := bstep (se 1 (by rfl) ⟨170582, by rfl⟩ : syracuseStep 227443 = 341165) B341165
theorem B1538189 : Blo 199806 1538189 := bstep (se 3 (by rfl) ⟨288410, by rfl⟩ : syracuseStep 1538189 = 576821) B576821
theorem B686285 : Blo 199806 686285 := bstep (se 3 (by rfl) ⟨128678, by rfl⟩ : syracuseStep 686285 = 257357) B257357
theorem B227587 : Blo 199806 227587 := bstep (se 1 (by rfl) ⟨170690, by rfl⟩ : syracuseStep 227587 = 341381) B341381
theorem B686339 : Blo 199806 686339 := bstep (se 1 (by rfl) ⟨514754, by rfl⟩ : syracuseStep 686339 = 1029509) B1029509
theorem B1145123 : Blo 199806 1145123 := bstep (se 1 (by rfl) ⟨858842, by rfl⟩ : syracuseStep 1145123 = 1717685) B1717685
theorem B1571185 : Blo 199806 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B457073 : Blo 199806 457073 := bstep (se 2 (by rfl) ⟨171402, by rfl⟩ : syracuseStep 457073 = 342805) B342805
theorem B457091 : Blo 199806 457091 := bstep (se 1 (by rfl) ⟨342818, by rfl⟩ : syracuseStep 457091 = 685637) B685637
theorem B227731 : Blo 199806 227731 := bstep (se 1 (by rfl) ⟨170798, by rfl⟩ : syracuseStep 227731 = 341597) B341597
theorem B1735181 : Blo 199806 1735181 := bstep (se 3 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 1735181 = 650693) B650693
theorem B686609 : Blo 199806 686609 := bstep (se 2 (by rfl) ⟨257478, by rfl⟩ : syracuseStep 686609 = 514957) B514957
theorem B391697 : Blo 199806 391697 := bstep (se 2 (by rfl) ⟨146886, by rfl⟩ : syracuseStep 391697 = 293773) B293773
theorem B227875 : Blo 199806 227875 := bstep (se 1 (by rfl) ⟨170906, by rfl⟩ : syracuseStep 227875 = 341813) B341813
theorem B2882101 : Blo 199806 2882101 := bstep (se 5 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 2882101 = 270197) B270197
theorem B457361 : Blo 199806 457361 := bstep (se 2 (by rfl) ⟨171510, by rfl⟩ : syracuseStep 457361 = 343021) B343021
theorem B457379 : Blo 199806 457379 := bstep (se 1 (by rfl) ⟨343034, by rfl⟩ : syracuseStep 457379 = 686069) B686069
theorem B228019 : Blo 199806 228019 := bstep (se 1 (by rfl) ⟨171014, by rfl⟩ : syracuseStep 228019 = 342029) B342029
theorem B391889 : Blo 199806 391889 := bstep (se 2 (by rfl) ⟨146958, by rfl⟩ : syracuseStep 391889 = 293917) B293917
theorem B228163 : Blo 199806 228163 := bstep (se 1 (by rfl) ⟨171122, by rfl⟩ : syracuseStep 228163 = 342245) B342245
theorem B1014605 : Blo 199806 1014605 := bstep (se 3 (by rfl) ⟨190238, by rfl⟩ : syracuseStep 1014605 = 380477) B380477
theorem B457649 : Blo 199806 457649 := bstep (se 2 (by rfl) ⟨171618, by rfl⟩ : syracuseStep 457649 = 343237) B343237
theorem B457667 : Blo 199806 457667 := bstep (se 1 (by rfl) ⟨343250, by rfl⟩ : syracuseStep 457667 = 686501) B686501
theorem B228307 : Blo 199806 228307 := bstep (se 1 (by rfl) ⟨171230, by rfl⟩ : syracuseStep 228307 = 342461) B342461
theorem B687149 : Blo 199806 687149 := bstep (se 3 (by rfl) ⟨128840, by rfl⟩ : syracuseStep 687149 = 257681) B257681
theorem B228451 : Blo 199806 228451 := bstep (se 1 (by rfl) ⟨171338, by rfl⟩ : syracuseStep 228451 = 342677) B342677
theorem B687203 : Blo 199806 687203 := bstep (se 1 (by rfl) ⟨515402, by rfl⟩ : syracuseStep 687203 = 1030805) B1030805
theorem B457937 : Blo 199806 457937 := bstep (se 2 (by rfl) ⟨171726, by rfl⟩ : syracuseStep 457937 = 343453) B343453
theorem B457955 : Blo 199806 457955 := bstep (se 1 (by rfl) ⟨343466, by rfl⟩ : syracuseStep 457955 = 686933) B686933
theorem B228595 : Blo 199806 228595 := bstep (se 1 (by rfl) ⟨171446, by rfl⟩ : syracuseStep 228595 = 342893) B342893
theorem B687473 : Blo 199806 687473 := bstep (se 2 (by rfl) ⟨257802, by rfl⟩ : syracuseStep 687473 = 515605) B515605
theorem B228739 : Blo 199806 228739 := bstep (se 1 (by rfl) ⟨171554, by rfl⟩ : syracuseStep 228739 = 343109) B343109
theorem B1441165 : Blo 199806 1441165 := bstep (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) B540437
theorem B3079565 : Blo 199806 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B458225 : Blo 199806 458225 := bstep (se 2 (by rfl) ⟨171834, by rfl⟩ : syracuseStep 458225 = 343669) B343669
theorem B458243 : Blo 199806 458243 := bstep (se 1 (by rfl) ⟨343682, by rfl⟩ : syracuseStep 458243 = 687365) B687365
theorem B228883 : Blo 199806 228883 := bstep (se 1 (by rfl) ⟨171662, by rfl⟩ : syracuseStep 228883 = 343325) B343325
theorem B229027 : Blo 199806 229027 := bstep (se 1 (by rfl) ⟨171770, by rfl⟩ : syracuseStep 229027 = 343541) B343541
theorem B458513 : Blo 199806 458513 := bstep (se 2 (by rfl) ⟨171942, by rfl⟩ : syracuseStep 458513 = 343885) B343885
theorem B458531 : Blo 199806 458531 := bstep (se 1 (by rfl) ⟨343898, by rfl⟩ : syracuseStep 458531 = 687797) B687797
theorem B229171 : Blo 199806 229171 := bstep (se 1 (by rfl) ⟨171878, by rfl⟩ : syracuseStep 229171 = 343757) B343757
theorem B491377 : Blo 199806 491377 := bstep (se 2 (by rfl) ⟨184266, by rfl⟩ : syracuseStep 491377 = 368533) B368533
theorem B720845 : Blo 199806 720845 := bstep (se 3 (by rfl) ⟨135158, by rfl⟩ : syracuseStep 720845 = 270317) B270317
theorem B1015901 : Blo 199806 1015901 := bstep (se 3 (by rfl) ⟨190481, by rfl⟩ : syracuseStep 1015901 = 380963) B380963
theorem B229495 : Blo 199806 229495 := bstep (se 1 (by rfl) ⟨172121, by rfl⟩ : syracuseStep 229495 = 344243) B344243
theorem B2458147 : Blo 199806 2458147 := bstep (se 1 (by rfl) ⟨1843610, by rfl⟩ : syracuseStep 2458147 = 3687221) B3687221
theorem B2851421 : Blo 199806 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B361099 : Blo 199806 361099 := bstep (se 1 (by rfl) ⟨270824, by rfl⟩ : syracuseStep 361099 = 541649) B541649
theorem B2196341 : Blo 199806 2196341 := bstep (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) B205907
theorem B2327413 : Blo 199806 2327413 := bstep (se 5 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 2327413 = 218195) B218195
theorem B230807 : Blo 199806 230807 := bstep (se 1 (by rfl) ⟨173105, by rfl⟩ : syracuseStep 230807 = 346211) B346211
theorem B427457 : Blo 199806 427457 := bstep (se 2 (by rfl) ⟨160296, by rfl⟩ : syracuseStep 427457 = 320593) B320593
theorem B853649 : Blo 199806 853649 := bstep (se 2 (by rfl) ⟨320118, by rfl⟩ : syracuseStep 853649 = 640237) B640237
theorem B362137 : Blo 199806 362137 := bstep (se 2 (by rfl) ⟨135801, by rfl⟩ : syracuseStep 362137 = 271603) B271603
theorem B493249 : Blo 199806 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B362483 : Blo 199806 362483 := bstep (se 1 (by rfl) ⟨271862, by rfl⟩ : syracuseStep 362483 = 543725) B543725
theorem B1018007 : Blo 199806 1018007 := bstep (se 1 (by rfl) ⟨763505, by rfl⟩ : syracuseStep 1018007 = 1527011) B1527011
theorem B854707 : Blo 199806 854707 := bstep (se 1 (by rfl) ⟨641030, by rfl⟩ : syracuseStep 854707 = 1282061) B1282061
theorem B1739555 : Blo 199806 1739555 := bstep (se 1 (by rfl) ⟨1304666, by rfl⟩ : syracuseStep 1739555 = 2609333) B2609333
theorem B1149997 : Blo 199806 1149997 := bstep (se 3 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 1149997 = 431249) B431249
theorem B429131 : Blo 199806 429131 := bstep (se 1 (by rfl) ⟨321848, by rfl⟩ : syracuseStep 429131 = 643697) B643697
theorem B199819 : Blo 199806 199819 := bstep (se 1 (by rfl) ⟨149864, by rfl⟩ : syracuseStep 199819 = 299729) B299729
theorem B199831 : Blo 199806 199831 := bstep (se 1 (by rfl) ⟨149873, by rfl⟩ : syracuseStep 199831 = 299747) B299747
theorem B199851 : Blo 199806 199851 := bstep (se 1 (by rfl) ⟨149888, by rfl⟩ : syracuseStep 199851 = 299777) B299777
theorem B199863 : Blo 199806 199863 := bstep (se 1 (by rfl) ⟨149897, by rfl⟩ : syracuseStep 199863 = 299795) B299795
theorem B199883 : Blo 199806 199883 := bstep (se 1 (by rfl) ⟨149912, by rfl⟩ : syracuseStep 199883 = 299825) B299825
theorem B199895 : Blo 199806 199895 := bstep (se 1 (by rfl) ⟨149921, by rfl⟩ : syracuseStep 199895 = 299843) B299843
theorem B199915 : Blo 199806 199915 := bstep (se 1 (by rfl) ⟨149936, by rfl⟩ : syracuseStep 199915 = 299873) B299873
theorem B199927 : Blo 199806 199927 := bstep (se 1 (by rfl) ⟨149945, by rfl⟩ : syracuseStep 199927 = 299891) B299891
theorem B199947 : Blo 199806 199947 := bstep (se 1 (by rfl) ⟨149960, by rfl⟩ : syracuseStep 199947 = 299921) B299921
theorem B199959 : Blo 199806 199959 := bstep (se 1 (by rfl) ⟨149969, by rfl⟩ : syracuseStep 199959 = 299939) B299939
theorem B199979 : Blo 199806 199979 := bstep (se 1 (by rfl) ⟨149984, by rfl⟩ : syracuseStep 199979 = 299969) B299969
theorem B199991 : Blo 199806 199991 := bstep (se 1 (by rfl) ⟨149993, by rfl⟩ : syracuseStep 199991 = 299987) B299987
theorem B200011 : Blo 199806 200011 := bstep (se 1 (by rfl) ⟨150008, by rfl⟩ : syracuseStep 200011 = 300017) B300017
theorem B200023 : Blo 199806 200023 := bstep (se 1 (by rfl) ⟨150017, by rfl⟩ : syracuseStep 200023 = 300035) B300035
theorem B200043 : Blo 199806 200043 := bstep (se 1 (by rfl) ⟨150032, by rfl⟩ : syracuseStep 200043 = 300065) B300065
theorem B200055 : Blo 199806 200055 := bstep (se 1 (by rfl) ⟨150041, by rfl⟩ : syracuseStep 200055 = 300083) B300083
theorem B200075 : Blo 199806 200075 := bstep (se 1 (by rfl) ⟨150056, by rfl⟩ : syracuseStep 200075 = 300113) B300113
theorem B200087 : Blo 199806 200087 := bstep (se 1 (by rfl) ⟨150065, by rfl⟩ : syracuseStep 200087 = 300131) B300131
theorem B200107 : Blo 199806 200107 := bstep (se 1 (by rfl) ⟨150080, by rfl⟩ : syracuseStep 200107 = 300161) B300161
theorem B200119 : Blo 199806 200119 := bstep (se 1 (by rfl) ⟨150089, by rfl⟩ : syracuseStep 200119 = 300179) B300179
theorem B200139 : Blo 199806 200139 := bstep (se 1 (by rfl) ⟨150104, by rfl⟩ : syracuseStep 200139 = 300209) B300209
theorem B200151 : Blo 199806 200151 := bstep (se 1 (by rfl) ⟨150113, by rfl⟩ : syracuseStep 200151 = 300227) B300227
theorem B200171 : Blo 199806 200171 := bstep (se 1 (by rfl) ⟨150128, by rfl⟩ : syracuseStep 200171 = 300257) B300257
theorem B200183 : Blo 199806 200183 := bstep (se 1 (by rfl) ⟨150137, by rfl⟩ : syracuseStep 200183 = 300275) B300275
theorem B364033 : Blo 199806 364033 := bstep (se 2 (by rfl) ⟨136512, by rfl⟩ : syracuseStep 364033 = 273025) B273025
theorem B200203 : Blo 199806 200203 := bstep (se 1 (by rfl) ⟨150152, by rfl⟩ : syracuseStep 200203 = 300305) B300305
theorem B1740305 : Blo 199806 1740305 := bstep (se 2 (by rfl) ⟨652614, by rfl⟩ : syracuseStep 1740305 = 1305229) B1305229
theorem B200215 : Blo 199806 200215 := bstep (se 1 (by rfl) ⟨150161, by rfl⟩ : syracuseStep 200215 = 300323) B300323
theorem B200235 : Blo 199806 200235 := bstep (se 1 (by rfl) ⟨150176, by rfl⟩ : syracuseStep 200235 = 300353) B300353
theorem B200247 : Blo 199806 200247 := bstep (se 1 (by rfl) ⟨150185, by rfl⟩ : syracuseStep 200247 = 300371) B300371
theorem B200267 : Blo 199806 200267 := bstep (se 1 (by rfl) ⟨150200, by rfl⟩ : syracuseStep 200267 = 300401) B300401
theorem B200279 : Blo 199806 200279 := bstep (se 1 (by rfl) ⟨150209, by rfl⟩ : syracuseStep 200279 = 300419) B300419
theorem B200299 : Blo 199806 200299 := bstep (se 1 (by rfl) ⟨150224, by rfl⟩ : syracuseStep 200299 = 300449) B300449
theorem B200311 : Blo 199806 200311 := bstep (se 1 (by rfl) ⟨150233, by rfl⟩ : syracuseStep 200311 = 300467) B300467
theorem B200331 : Blo 199806 200331 := bstep (se 1 (by rfl) ⟨150248, by rfl⟩ : syracuseStep 200331 = 300497) B300497
theorem B200343 : Blo 199806 200343 := bstep (se 1 (by rfl) ⟨150257, by rfl⟩ : syracuseStep 200343 = 300515) B300515
theorem B200363 : Blo 199806 200363 := bstep (se 1 (by rfl) ⟨150272, by rfl⟩ : syracuseStep 200363 = 300545) B300545
theorem B200375 : Blo 199806 200375 := bstep (se 1 (by rfl) ⟨150281, by rfl⟩ : syracuseStep 200375 = 300563) B300563
theorem B200395 : Blo 199806 200395 := bstep (se 1 (by rfl) ⟨150296, by rfl⟩ : syracuseStep 200395 = 300593) B300593
theorem B200407 : Blo 199806 200407 := bstep (se 1 (by rfl) ⟨150305, by rfl⟩ : syracuseStep 200407 = 300611) B300611
theorem B200427 : Blo 199806 200427 := bstep (se 1 (by rfl) ⟨150320, by rfl⟩ : syracuseStep 200427 = 300641) B300641
theorem B200439 : Blo 199806 200439 := bstep (se 1 (by rfl) ⟨150329, by rfl⟩ : syracuseStep 200439 = 300659) B300659
theorem B200459 : Blo 199806 200459 := bstep (se 1 (by rfl) ⟨150344, by rfl⟩ : syracuseStep 200459 = 300689) B300689
theorem B1085201 : Blo 199806 1085201 := bstep (se 2 (by rfl) ⟨406950, by rfl⟩ : syracuseStep 1085201 = 813901) B813901
theorem B200471 : Blo 199806 200471 := bstep (se 1 (by rfl) ⟨150353, by rfl⟩ : syracuseStep 200471 = 300707) B300707
theorem B200491 : Blo 199806 200491 := bstep (se 1 (by rfl) ⟨150368, by rfl⟩ : syracuseStep 200491 = 300737) B300737
theorem B200503 : Blo 199806 200503 := bstep (se 1 (by rfl) ⟨150377, by rfl⟩ : syracuseStep 200503 = 300755) B300755
theorem B200523 : Blo 199806 200523 := bstep (se 1 (by rfl) ⟨150392, by rfl⟩ : syracuseStep 200523 = 300785) B300785
theorem B200535 : Blo 199806 200535 := bstep (se 1 (by rfl) ⟨150401, by rfl⟩ : syracuseStep 200535 = 300803) B300803
theorem B200555 : Blo 199806 200555 := bstep (se 1 (by rfl) ⟨150416, by rfl⟩ : syracuseStep 200555 = 300833) B300833
theorem B200567 : Blo 199806 200567 := bstep (se 1 (by rfl) ⟨150425, by rfl⟩ : syracuseStep 200567 = 300851) B300851
theorem B200587 : Blo 199806 200587 := bstep (se 1 (by rfl) ⟨150440, by rfl⟩ : syracuseStep 200587 = 300881) B300881
theorem B200599 : Blo 199806 200599 := bstep (se 1 (by rfl) ⟨150449, by rfl⟩ : syracuseStep 200599 = 300899) B300899
theorem B200619 : Blo 199806 200619 := bstep (se 1 (by rfl) ⟨150464, by rfl⟩ : syracuseStep 200619 = 300929) B300929
theorem B200631 : Blo 199806 200631 := bstep (se 1 (by rfl) ⟨150473, by rfl⟩ : syracuseStep 200631 = 300947) B300947
theorem B200651 : Blo 199806 200651 := bstep (se 1 (by rfl) ⟨150488, by rfl⟩ : syracuseStep 200651 = 300977) B300977
theorem B200663 : Blo 199806 200663 := bstep (se 1 (by rfl) ⟨150497, by rfl⟩ : syracuseStep 200663 = 300995) B300995
theorem B200683 : Blo 199806 200683 := bstep (se 1 (by rfl) ⟨150512, by rfl⟩ : syracuseStep 200683 = 301025) B301025
theorem B200695 : Blo 199806 200695 := bstep (se 1 (by rfl) ⟨150521, by rfl⟩ : syracuseStep 200695 = 301043) B301043
theorem B200715 : Blo 199806 200715 := bstep (se 1 (by rfl) ⟨150536, by rfl⟩ : syracuseStep 200715 = 301073) B301073
theorem B200727 : Blo 199806 200727 := bstep (se 1 (by rfl) ⟨150545, by rfl⟩ : syracuseStep 200727 = 301091) B301091
theorem B430105 : Blo 199806 430105 := bstep (se 2 (by rfl) ⟨161289, by rfl⟩ : syracuseStep 430105 = 322579) B322579
theorem B200747 : Blo 199806 200747 := bstep (se 1 (by rfl) ⟨150560, by rfl⟩ : syracuseStep 200747 = 301121) B301121
theorem B856109 : Blo 199806 856109 := bstep (se 3 (by rfl) ⟨160520, by rfl⟩ : syracuseStep 856109 = 321041) B321041
theorem B200759 : Blo 199806 200759 := bstep (se 1 (by rfl) ⟨150569, by rfl⟩ : syracuseStep 200759 = 301139) B301139
theorem B200779 : Blo 199806 200779 := bstep (se 1 (by rfl) ⟨150584, by rfl⟩ : syracuseStep 200779 = 301169) B301169
theorem B200791 : Blo 199806 200791 := bstep (se 1 (by rfl) ⟨150593, by rfl⟩ : syracuseStep 200791 = 301187) B301187
theorem B200811 : Blo 199806 200811 := bstep (se 1 (by rfl) ⟨150608, by rfl⟩ : syracuseStep 200811 = 301217) B301217
theorem B200823 : Blo 199806 200823 := bstep (se 1 (by rfl) ⟨150617, by rfl⟩ : syracuseStep 200823 = 301235) B301235
theorem B200843 : Blo 199806 200843 := bstep (se 1 (by rfl) ⟨150632, by rfl⟩ : syracuseStep 200843 = 301265) B301265
theorem B200855 : Blo 199806 200855 := bstep (se 1 (by rfl) ⟨150641, by rfl⟩ : syracuseStep 200855 = 301283) B301283
theorem B200875 : Blo 199806 200875 := bstep (se 1 (by rfl) ⟨150656, by rfl⟩ : syracuseStep 200875 = 301313) B301313
theorem B200887 : Blo 199806 200887 := bstep (se 1 (by rfl) ⟨150665, by rfl⟩ : syracuseStep 200887 = 301331) B301331
theorem B200907 : Blo 199806 200907 := bstep (se 1 (by rfl) ⟨150680, by rfl⟩ : syracuseStep 200907 = 301361) B301361
theorem B200919 : Blo 199806 200919 := bstep (se 1 (by rfl) ⟨150689, by rfl⟩ : syracuseStep 200919 = 301379) B301379
theorem B200939 : Blo 199806 200939 := bstep (se 1 (by rfl) ⟨150704, by rfl⟩ : syracuseStep 200939 = 301409) B301409
theorem B200951 : Blo 199806 200951 := bstep (se 1 (by rfl) ⟨150713, by rfl⟩ : syracuseStep 200951 = 301427) B301427
theorem B200971 : Blo 199806 200971 := bstep (se 1 (by rfl) ⟨150728, by rfl⟩ : syracuseStep 200971 = 301457) B301457
theorem B18583829 : Blo 199806 18583829 := bstep (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) B871117
theorem B200983 : Blo 199806 200983 := bstep (se 1 (by rfl) ⟨150737, by rfl⟩ : syracuseStep 200983 = 301475) B301475
theorem B430361 : Blo 199806 430361 := bstep (se 2 (by rfl) ⟨161385, by rfl⟩ : syracuseStep 430361 = 322771) B322771
theorem B201003 : Blo 199806 201003 := bstep (se 1 (by rfl) ⟨150752, by rfl⟩ : syracuseStep 201003 = 301505) B301505
theorem B201015 : Blo 199806 201015 := bstep (se 1 (by rfl) ⟨150761, by rfl⟩ : syracuseStep 201015 = 301523) B301523
theorem B201035 : Blo 199806 201035 := bstep (se 1 (by rfl) ⟨150776, by rfl⟩ : syracuseStep 201035 = 301553) B301553
theorem B201047 : Blo 199806 201047 := bstep (se 1 (by rfl) ⟨150785, by rfl⟩ : syracuseStep 201047 = 301571) B301571
theorem B201067 : Blo 199806 201067 := bstep (se 1 (by rfl) ⟨150800, by rfl⟩ : syracuseStep 201067 = 301601) B301601
theorem B201079 : Blo 199806 201079 := bstep (se 1 (by rfl) ⟨150809, by rfl⟩ : syracuseStep 201079 = 301619) B301619
theorem B201099 : Blo 199806 201099 := bstep (se 1 (by rfl) ⟨150824, by rfl⟩ : syracuseStep 201099 = 301649) B301649
theorem B201111 : Blo 199806 201111 := bstep (se 1 (by rfl) ⟨150833, by rfl⟩ : syracuseStep 201111 = 301667) B301667
theorem B201131 : Blo 199806 201131 := bstep (se 1 (by rfl) ⟨150848, by rfl⟩ : syracuseStep 201131 = 301697) B301697
theorem B201143 : Blo 199806 201143 := bstep (se 1 (by rfl) ⟨150857, by rfl⟩ : syracuseStep 201143 = 301715) B301715
theorem B201163 : Blo 199806 201163 := bstep (se 1 (by rfl) ⟨150872, by rfl⟩ : syracuseStep 201163 = 301745) B301745
theorem B201175 : Blo 199806 201175 := bstep (se 1 (by rfl) ⟨150881, by rfl⟩ : syracuseStep 201175 = 301763) B301763
theorem B201195 : Blo 199806 201195 := bstep (se 1 (by rfl) ⟨150896, by rfl⟩ : syracuseStep 201195 = 301793) B301793
theorem B201207 : Blo 199806 201207 := bstep (se 1 (by rfl) ⟨150905, by rfl⟩ : syracuseStep 201207 = 301811) B301811
theorem B201227 : Blo 199806 201227 := bstep (se 1 (by rfl) ⟨150920, by rfl⟩ : syracuseStep 201227 = 301841) B301841
theorem B201239 : Blo 199806 201239 := bstep (se 1 (by rfl) ⟨150929, by rfl⟩ : syracuseStep 201239 = 301859) B301859
theorem B201259 : Blo 199806 201259 := bstep (se 1 (by rfl) ⟨150944, by rfl⟩ : syracuseStep 201259 = 301889) B301889
theorem B201271 : Blo 199806 201271 := bstep (se 1 (by rfl) ⟨150953, by rfl⟩ : syracuseStep 201271 = 301907) B301907
theorem B201291 : Blo 199806 201291 := bstep (se 1 (by rfl) ⟨150968, by rfl⟩ : syracuseStep 201291 = 301937) B301937
theorem B201303 : Blo 199806 201303 := bstep (se 1 (by rfl) ⟨150977, by rfl⟩ : syracuseStep 201303 = 301955) B301955
theorem B201323 : Blo 199806 201323 := bstep (se 1 (by rfl) ⟨150992, by rfl⟩ : syracuseStep 201323 = 301985) B301985
theorem B201335 : Blo 199806 201335 := bstep (se 1 (by rfl) ⟨151001, by rfl⟩ : syracuseStep 201335 = 302003) B302003
theorem B201355 : Blo 199806 201355 := bstep (se 1 (by rfl) ⟨151016, by rfl⟩ : syracuseStep 201355 = 302033) B302033
theorem B201367 : Blo 199806 201367 := bstep (se 1 (by rfl) ⟨151025, by rfl⟩ : syracuseStep 201367 = 302051) B302051
theorem B201387 : Blo 199806 201387 := bstep (se 1 (by rfl) ⟨151040, by rfl⟩ : syracuseStep 201387 = 302081) B302081
theorem B430771 : Blo 199806 430771 := bstep (se 1 (by rfl) ⟨323078, by rfl⟩ : syracuseStep 430771 = 646157) B646157
theorem B201399 : Blo 199806 201399 := bstep (se 1 (by rfl) ⟨151049, by rfl⟩ : syracuseStep 201399 = 302099) B302099
theorem B299723 : Blo 199806 299723 := bstep (se 1 (by rfl) ⟨224792, by rfl⟩ : syracuseStep 299723 = 449585) B449585
theorem B201419 : Blo 199806 201419 := bstep (se 1 (by rfl) ⟨151064, by rfl⟩ : syracuseStep 201419 = 302129) B302129
theorem B299735 : Blo 199806 299735 := bstep (se 1 (by rfl) ⟨224801, by rfl⟩ : syracuseStep 299735 = 449603) B449603
theorem B201431 : Blo 199806 201431 := bstep (se 1 (by rfl) ⟨151073, by rfl⟩ : syracuseStep 201431 = 302147) B302147
theorem B201451 : Blo 199806 201451 := bstep (se 1 (by rfl) ⟨151088, by rfl⟩ : syracuseStep 201451 = 302177) B302177
theorem B201463 : Blo 199806 201463 := bstep (se 1 (by rfl) ⟨151097, by rfl⟩ : syracuseStep 201463 = 302195) B302195
theorem B201483 : Blo 199806 201483 := bstep (se 1 (by rfl) ⟨151112, by rfl⟩ : syracuseStep 201483 = 302225) B302225
theorem B201495 : Blo 199806 201495 := bstep (se 1 (by rfl) ⟨151121, by rfl⟩ : syracuseStep 201495 = 302243) B302243
theorem B299801 : Blo 199806 299801 := bstep (se 2 (by rfl) ⟨112425, by rfl⟩ : syracuseStep 299801 = 224851) B224851
theorem B201515 : Blo 199806 201515 := bstep (se 1 (by rfl) ⟨151136, by rfl⟩ : syracuseStep 201515 = 302273) B302273
theorem B201527 : Blo 199806 201527 := bstep (se 1 (by rfl) ⟨151145, by rfl⟩ : syracuseStep 201527 = 302291) B302291
theorem B201547 : Blo 199806 201547 := bstep (se 1 (by rfl) ⟨151160, by rfl⟩ : syracuseStep 201547 = 302321) B302321
theorem B201559 : Blo 199806 201559 := bstep (se 1 (by rfl) ⟨151169, by rfl⟩ : syracuseStep 201559 = 302339) B302339
theorem B201579 : Blo 199806 201579 := bstep (se 1 (by rfl) ⟨151184, by rfl⟩ : syracuseStep 201579 = 302369) B302369
theorem B201591 : Blo 199806 201591 := bstep (se 1 (by rfl) ⟨151193, by rfl⟩ : syracuseStep 201591 = 302387) B302387
theorem B299915 : Blo 199806 299915 := bstep (se 1 (by rfl) ⟨224936, by rfl⟩ : syracuseStep 299915 = 449873) B449873
theorem B201611 : Blo 199806 201611 := bstep (se 1 (by rfl) ⟨151208, by rfl⟩ : syracuseStep 201611 = 302417) B302417
theorem B299927 : Blo 199806 299927 := bstep (se 1 (by rfl) ⟨224945, by rfl⟩ : syracuseStep 299927 = 449891) B449891
theorem B201623 : Blo 199806 201623 := bstep (se 1 (by rfl) ⟨151217, by rfl⟩ : syracuseStep 201623 = 302435) B302435
theorem B201643 : Blo 199806 201643 := bstep (se 1 (by rfl) ⟨151232, by rfl⟩ : syracuseStep 201643 = 302465) B302465
theorem B2200499 : Blo 199806 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B201655 : Blo 199806 201655 := bstep (se 1 (by rfl) ⟨151241, by rfl⟩ : syracuseStep 201655 = 302483) B302483
theorem B201675 : Blo 199806 201675 := bstep (se 1 (by rfl) ⟨151256, by rfl⟩ : syracuseStep 201675 = 302513) B302513
theorem B201687 : Blo 199806 201687 := bstep (se 1 (by rfl) ⟨151265, by rfl⟩ : syracuseStep 201687 = 302531) B302531
theorem B299993 : Blo 199806 299993 := bstep (se 2 (by rfl) ⟨112497, by rfl⟩ : syracuseStep 299993 = 224995) B224995
theorem B7410649 : Blo 199806 7410649 := bstep (se 2 (by rfl) ⟨2778993, by rfl⟩ : syracuseStep 7410649 = 5557987) B5557987
theorem B201707 : Blo 199806 201707 := bstep (se 1 (by rfl) ⟨151280, by rfl⟩ : syracuseStep 201707 = 302561) B302561
theorem B201719 : Blo 199806 201719 := bstep (se 1 (by rfl) ⟨151289, by rfl⟩ : syracuseStep 201719 = 302579) B302579
theorem B201739 : Blo 199806 201739 := bstep (se 1 (by rfl) ⟨151304, by rfl⟩ : syracuseStep 201739 = 302609) B302609
theorem B201751 : Blo 199806 201751 := bstep (se 1 (by rfl) ⟨151313, by rfl⟩ : syracuseStep 201751 = 302627) B302627
theorem B201771 : Blo 199806 201771 := bstep (se 1 (by rfl) ⟨151328, by rfl⟩ : syracuseStep 201771 = 302657) B302657
theorem B201783 : Blo 199806 201783 := bstep (se 1 (by rfl) ⟨151337, by rfl⟩ : syracuseStep 201783 = 302675) B302675
theorem B300107 : Blo 199806 300107 := bstep (se 1 (by rfl) ⟨225080, by rfl⟩ : syracuseStep 300107 = 450161) B450161
theorem B201803 : Blo 199806 201803 := bstep (se 1 (by rfl) ⟨151352, by rfl⟩ : syracuseStep 201803 = 302705) B302705
theorem B300119 : Blo 199806 300119 := bstep (se 1 (by rfl) ⟨225089, by rfl⟩ : syracuseStep 300119 = 450179) B450179
theorem B201815 : Blo 199806 201815 := bstep (se 1 (by rfl) ⟨151361, by rfl⟩ : syracuseStep 201815 = 302723) B302723
theorem B201835 : Blo 199806 201835 := bstep (se 1 (by rfl) ⟨151376, by rfl⟩ : syracuseStep 201835 = 302753) B302753
theorem B201847 : Blo 199806 201847 := bstep (se 1 (by rfl) ⟨151385, by rfl⟩ : syracuseStep 201847 = 302771) B302771
theorem B201867 : Blo 199806 201867 := bstep (se 1 (by rfl) ⟨151400, by rfl⟩ : syracuseStep 201867 = 302801) B302801
theorem B201879 : Blo 199806 201879 := bstep (se 1 (by rfl) ⟨151409, by rfl⟩ : syracuseStep 201879 = 302819) B302819
theorem B300185 : Blo 199806 300185 := bstep (se 2 (by rfl) ⟨112569, by rfl⟩ : syracuseStep 300185 = 225139) B225139
theorem B201899 : Blo 199806 201899 := bstep (se 1 (by rfl) ⟨151424, by rfl⟩ : syracuseStep 201899 = 302849) B302849
theorem B201911 : Blo 199806 201911 := bstep (se 1 (by rfl) ⟨151433, by rfl⟩ : syracuseStep 201911 = 302867) B302867
theorem B201931 : Blo 199806 201931 := bstep (se 1 (by rfl) ⟨151448, by rfl⟩ : syracuseStep 201931 = 302897) B302897
theorem B365771 : Blo 199806 365771 := bstep (se 1 (by rfl) ⟨274328, by rfl⟩ : syracuseStep 365771 = 548657) B548657
theorem B201943 : Blo 199806 201943 := bstep (se 1 (by rfl) ⟨151457, by rfl⟩ : syracuseStep 201943 = 302915) B302915
theorem B201963 : Blo 199806 201963 := bstep (se 1 (by rfl) ⟨151472, by rfl⟩ : syracuseStep 201963 = 302945) B302945
theorem B201975 : Blo 199806 201975 := bstep (se 1 (by rfl) ⟨151481, by rfl⟩ : syracuseStep 201975 = 302963) B302963
theorem B300299 : Blo 199806 300299 := bstep (se 1 (by rfl) ⟨225224, by rfl⟩ : syracuseStep 300299 = 450449) B450449
theorem B201995 : Blo 199806 201995 := bstep (se 1 (by rfl) ⟨151496, by rfl⟩ : syracuseStep 201995 = 302993) B302993
theorem B300311 : Blo 199806 300311 := bstep (se 1 (by rfl) ⟨225233, by rfl⟩ : syracuseStep 300311 = 450467) B450467
theorem B202007 : Blo 199806 202007 := bstep (se 1 (by rfl) ⟨151505, by rfl⟩ : syracuseStep 202007 = 303011) B303011
theorem B202027 : Blo 199806 202027 := bstep (se 1 (by rfl) ⟨151520, by rfl⟩ : syracuseStep 202027 = 303041) B303041
theorem B202039 : Blo 199806 202039 := bstep (se 1 (by rfl) ⟨151529, by rfl⟩ : syracuseStep 202039 = 303059) B303059
theorem B202059 : Blo 199806 202059 := bstep (se 1 (by rfl) ⟨151544, by rfl⟩ : syracuseStep 202059 = 303089) B303089
theorem B202071 : Blo 199806 202071 := bstep (se 1 (by rfl) ⟨151553, by rfl⟩ : syracuseStep 202071 = 303107) B303107
theorem B300377 : Blo 199806 300377 := bstep (se 2 (by rfl) ⟨112641, by rfl⟩ : syracuseStep 300377 = 225283) B225283
theorem B202091 : Blo 199806 202091 := bstep (se 1 (by rfl) ⟨151568, by rfl⟩ : syracuseStep 202091 = 303137) B303137
theorem B202103 : Blo 199806 202103 := bstep (se 1 (by rfl) ⟨151577, by rfl⟩ : syracuseStep 202103 = 303155) B303155
theorem B431489 : Blo 199806 431489 := bstep (se 2 (by rfl) ⟨161808, by rfl⟩ : syracuseStep 431489 = 323617) B323617
theorem B202123 : Blo 199806 202123 := bstep (se 1 (by rfl) ⟨151592, by rfl⟩ : syracuseStep 202123 = 303185) B303185
theorem B12719501 : Blo 199806 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B202135 : Blo 199806 202135 := bstep (se 1 (by rfl) ⟨151601, by rfl⟩ : syracuseStep 202135 = 303203) B303203
theorem B202155 : Blo 199806 202155 := bstep (se 1 (by rfl) ⟨151616, by rfl⟩ : syracuseStep 202155 = 303233) B303233
theorem B202167 : Blo 199806 202167 := bstep (se 1 (by rfl) ⟨151625, by rfl⟩ : syracuseStep 202167 = 303251) B303251
theorem B300491 : Blo 199806 300491 := bstep (se 1 (by rfl) ⟨225368, by rfl⟩ : syracuseStep 300491 = 450737) B450737
theorem B202187 : Blo 199806 202187 := bstep (se 1 (by rfl) ⟨151640, by rfl⟩ : syracuseStep 202187 = 303281) B303281
theorem B300503 : Blo 199806 300503 := bstep (se 1 (by rfl) ⟨225377, by rfl⟩ : syracuseStep 300503 = 450755) B450755
theorem B202199 : Blo 199806 202199 := bstep (se 1 (by rfl) ⟨151649, by rfl⟩ : syracuseStep 202199 = 303299) B303299
theorem B202219 : Blo 199806 202219 := bstep (se 1 (by rfl) ⟨151664, by rfl⟩ : syracuseStep 202219 = 303329) B303329
theorem B202231 : Blo 199806 202231 := bstep (se 1 (by rfl) ⟨151673, by rfl⟩ : syracuseStep 202231 = 303347) B303347
theorem B202251 : Blo 199806 202251 := bstep (se 1 (by rfl) ⟨151688, by rfl⟩ : syracuseStep 202251 = 303377) B303377
theorem B202263 : Blo 199806 202263 := bstep (se 1 (by rfl) ⟨151697, by rfl⟩ : syracuseStep 202263 = 303395) B303395
theorem B300569 : Blo 199806 300569 := bstep (se 2 (by rfl) ⟨112713, by rfl⟩ : syracuseStep 300569 = 225427) B225427
theorem B202283 : Blo 199806 202283 := bstep (se 1 (by rfl) ⟨151712, by rfl⟩ : syracuseStep 202283 = 303425) B303425
theorem B202295 : Blo 199806 202295 := bstep (se 1 (by rfl) ⟨151721, by rfl⟩ : syracuseStep 202295 = 303443) B303443
theorem B202315 : Blo 199806 202315 := bstep (se 1 (by rfl) ⟨151736, by rfl⟩ : syracuseStep 202315 = 303473) B303473
theorem B202327 : Blo 199806 202327 := bstep (se 1 (by rfl) ⟨151745, by rfl⟩ : syracuseStep 202327 = 303491) B303491
theorem B202347 : Blo 199806 202347 := bstep (se 1 (by rfl) ⟨151760, by rfl⟩ : syracuseStep 202347 = 303521) B303521
theorem B202359 : Blo 199806 202359 := bstep (se 1 (by rfl) ⟨151769, by rfl⟩ : syracuseStep 202359 = 303539) B303539
theorem B1021571 : Blo 199806 1021571 := bstep (se 1 (by rfl) ⟨766178, by rfl⟩ : syracuseStep 1021571 = 1532357) B1532357
theorem B300683 : Blo 199806 300683 := bstep (se 1 (by rfl) ⟨225512, by rfl⟩ : syracuseStep 300683 = 451025) B451025
theorem B202379 : Blo 199806 202379 := bstep (se 1 (by rfl) ⟨151784, by rfl⟩ : syracuseStep 202379 = 303569) B303569
theorem B300695 : Blo 199806 300695 := bstep (se 1 (by rfl) ⟨225521, by rfl⟩ : syracuseStep 300695 = 451043) B451043
theorem B202391 : Blo 199806 202391 := bstep (se 1 (by rfl) ⟨151793, by rfl⟩ : syracuseStep 202391 = 303587) B303587
theorem B202411 : Blo 199806 202411 := bstep (se 1 (by rfl) ⟨151808, by rfl⟩ : syracuseStep 202411 = 303617) B303617
theorem B202423 : Blo 199806 202423 := bstep (se 1 (by rfl) ⟨151817, by rfl⟩ : syracuseStep 202423 = 303635) B303635
theorem B202443 : Blo 199806 202443 := bstep (se 1 (by rfl) ⟨151832, by rfl⟩ : syracuseStep 202443 = 303665) B303665
theorem B431831 : Blo 199806 431831 := bstep (se 1 (by rfl) ⟨323873, by rfl⟩ : syracuseStep 431831 = 647747) B647747
theorem B202455 : Blo 199806 202455 := bstep (se 1 (by rfl) ⟨151841, by rfl⟩ : syracuseStep 202455 = 303683) B303683
theorem B300761 : Blo 199806 300761 := bstep (se 2 (by rfl) ⟨112785, by rfl⟩ : syracuseStep 300761 = 225571) B225571
theorem B202475 : Blo 199806 202475 := bstep (se 1 (by rfl) ⟨151856, by rfl⟩ : syracuseStep 202475 = 303713) B303713
theorem B202487 : Blo 199806 202487 := bstep (se 1 (by rfl) ⟨151865, by rfl⟩ : syracuseStep 202487 = 303731) B303731
theorem B202507 : Blo 199806 202507 := bstep (se 1 (by rfl) ⟨151880, by rfl⟩ : syracuseStep 202507 = 303761) B303761
theorem B202519 : Blo 199806 202519 := bstep (se 1 (by rfl) ⟨151889, by rfl⟩ : syracuseStep 202519 = 303779) B303779
theorem B202539 : Blo 199806 202539 := bstep (se 1 (by rfl) ⟨151904, by rfl⟩ : syracuseStep 202539 = 303809) B303809
theorem B202551 : Blo 199806 202551 := bstep (se 1 (by rfl) ⟨151913, by rfl⟩ : syracuseStep 202551 = 303827) B303827
theorem B300875 : Blo 199806 300875 := bstep (se 1 (by rfl) ⟨225656, by rfl⟩ : syracuseStep 300875 = 451313) B451313
theorem B202571 : Blo 199806 202571 := bstep (se 1 (by rfl) ⟨151928, by rfl⟩ : syracuseStep 202571 = 303857) B303857
theorem B300887 : Blo 199806 300887 := bstep (se 1 (by rfl) ⟨225665, by rfl⟩ : syracuseStep 300887 = 451331) B451331
theorem B202583 : Blo 199806 202583 := bstep (se 1 (by rfl) ⟨151937, by rfl⟩ : syracuseStep 202583 = 303875) B303875
theorem B202603 : Blo 199806 202603 := bstep (se 1 (by rfl) ⟨151952, by rfl⟩ : syracuseStep 202603 = 303905) B303905
theorem B202615 : Blo 199806 202615 := bstep (se 1 (by rfl) ⟨151961, by rfl⟩ : syracuseStep 202615 = 303923) B303923
theorem B432001 : Blo 199806 432001 := bstep (se 2 (by rfl) ⟨162000, by rfl⟩ : syracuseStep 432001 = 324001) B324001
theorem B202635 : Blo 199806 202635 := bstep (se 1 (by rfl) ⟨151976, by rfl⟩ : syracuseStep 202635 = 303953) B303953
theorem B202647 : Blo 199806 202647 := bstep (se 1 (by rfl) ⟨151985, by rfl⟩ : syracuseStep 202647 = 303971) B303971
theorem B300953 : Blo 199806 300953 := bstep (se 2 (by rfl) ⟨112857, by rfl⟩ : syracuseStep 300953 = 225715) B225715
theorem B759725 : Blo 199806 759725 := bstep (se 3 (by rfl) ⟨142448, by rfl⟩ : syracuseStep 759725 = 284897) B284897
theorem B202667 : Blo 199806 202667 := bstep (se 1 (by rfl) ⟨152000, by rfl⟩ : syracuseStep 202667 = 304001) B304001
theorem B202679 : Blo 199806 202679 := bstep (se 1 (by rfl) ⟨152009, by rfl⟩ : syracuseStep 202679 = 304019) B304019
theorem B202699 : Blo 199806 202699 := bstep (se 1 (by rfl) ⟨152024, by rfl⟩ : syracuseStep 202699 = 304049) B304049
theorem B202711 : Blo 199806 202711 := bstep (se 1 (by rfl) ⟨152033, by rfl⟩ : syracuseStep 202711 = 304067) B304067
theorem B202731 : Blo 199806 202731 := bstep (se 1 (by rfl) ⟨152048, by rfl⟩ : syracuseStep 202731 = 304097) B304097
theorem B202743 : Blo 199806 202743 := bstep (se 1 (by rfl) ⟨152057, by rfl⟩ : syracuseStep 202743 = 304115) B304115
theorem B301067 : Blo 199806 301067 := bstep (se 1 (by rfl) ⟨225800, by rfl⟩ : syracuseStep 301067 = 451601) B451601
theorem B202763 : Blo 199806 202763 := bstep (se 1 (by rfl) ⟨152072, by rfl⟩ : syracuseStep 202763 = 304145) B304145
theorem B923665 : Blo 199806 923665 := bstep (se 2 (by rfl) ⟨346374, by rfl⟩ : syracuseStep 923665 = 692749) B692749
theorem B301079 : Blo 199806 301079 := bstep (se 1 (by rfl) ⟨225809, by rfl⟩ : syracuseStep 301079 = 451619) B451619
theorem B202775 : Blo 199806 202775 := bstep (se 1 (by rfl) ⟨152081, by rfl⟩ : syracuseStep 202775 = 304163) B304163
theorem B202795 : Blo 199806 202795 := bstep (se 1 (by rfl) ⟨152096, by rfl⟩ : syracuseStep 202795 = 304193) B304193
theorem B202807 : Blo 199806 202807 := bstep (se 1 (by rfl) ⟨152105, by rfl⟩ : syracuseStep 202807 = 304211) B304211
theorem B202827 : Blo 199806 202827 := bstep (se 1 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 202827 = 304241) B304241
theorem B202839 : Blo 199806 202839 := bstep (se 1 (by rfl) ⟨152129, by rfl⟩ : syracuseStep 202839 = 304259) B304259
theorem B301145 : Blo 199806 301145 := bstep (se 2 (by rfl) ⟨112929, by rfl⟩ : syracuseStep 301145 = 225859) B225859
theorem B202859 : Blo 199806 202859 := bstep (se 1 (by rfl) ⟨152144, by rfl⟩ : syracuseStep 202859 = 304289) B304289
theorem B202871 : Blo 199806 202871 := bstep (se 1 (by rfl) ⟨152153, by rfl⟩ : syracuseStep 202871 = 304307) B304307
theorem B202891 : Blo 199806 202891 := bstep (se 1 (by rfl) ⟨152168, by rfl⟩ : syracuseStep 202891 = 304337) B304337
theorem B202903 : Blo 199806 202903 := bstep (se 1 (by rfl) ⟨152177, by rfl⟩ : syracuseStep 202903 = 304355) B304355
theorem B202923 : Blo 199806 202923 := bstep (se 1 (by rfl) ⟨152192, by rfl⟩ : syracuseStep 202923 = 304385) B304385
theorem B202935 : Blo 199806 202935 := bstep (se 1 (by rfl) ⟨152201, by rfl⟩ : syracuseStep 202935 = 304403) B304403
theorem B301259 : Blo 199806 301259 := bstep (se 1 (by rfl) ⟨225944, by rfl⟩ : syracuseStep 301259 = 451889) B451889
theorem B202955 : Blo 199806 202955 := bstep (se 1 (by rfl) ⟨152216, by rfl⟩ : syracuseStep 202955 = 304433) B304433
theorem B301271 : Blo 199806 301271 := bstep (se 1 (by rfl) ⟨225953, by rfl⟩ : syracuseStep 301271 = 451907) B451907
theorem B202967 : Blo 199806 202967 := bstep (se 1 (by rfl) ⟨152225, by rfl⟩ : syracuseStep 202967 = 304451) B304451
theorem B202987 : Blo 199806 202987 := bstep (se 1 (by rfl) ⟨152240, by rfl⟩ : syracuseStep 202987 = 304481) B304481
theorem B202999 : Blo 199806 202999 := bstep (se 1 (by rfl) ⟨152249, by rfl⟩ : syracuseStep 202999 = 304499) B304499
theorem B203019 : Blo 199806 203019 := bstep (se 1 (by rfl) ⟨152264, by rfl⟩ : syracuseStep 203019 = 304529) B304529
theorem B203031 : Blo 199806 203031 := bstep (se 1 (by rfl) ⟨152273, by rfl⟩ : syracuseStep 203031 = 304547) B304547
theorem B301337 : Blo 199806 301337 := bstep (se 2 (by rfl) ⟨113001, by rfl⟩ : syracuseStep 301337 = 226003) B226003
theorem B203051 : Blo 199806 203051 := bstep (se 1 (by rfl) ⟨152288, by rfl⟩ : syracuseStep 203051 = 304577) B304577
theorem B203063 : Blo 199806 203063 := bstep (se 1 (by rfl) ⟨152297, by rfl⟩ : syracuseStep 203063 = 304595) B304595
theorem B203083 : Blo 199806 203083 := bstep (se 1 (by rfl) ⟨152312, by rfl⟩ : syracuseStep 203083 = 304625) B304625
theorem B203095 : Blo 199806 203095 := bstep (se 1 (by rfl) ⟨152321, by rfl⟩ : syracuseStep 203095 = 304643) B304643
theorem B203115 : Blo 199806 203115 := bstep (se 1 (by rfl) ⟨152336, by rfl⟩ : syracuseStep 203115 = 304673) B304673
theorem B203127 : Blo 199806 203127 := bstep (se 1 (by rfl) ⟨152345, by rfl⟩ : syracuseStep 203127 = 304691) B304691
theorem B301451 : Blo 199806 301451 := bstep (se 1 (by rfl) ⟨226088, by rfl⟩ : syracuseStep 301451 = 452177) B452177
theorem B203147 : Blo 199806 203147 := bstep (se 1 (by rfl) ⟨152360, by rfl⟩ : syracuseStep 203147 = 304721) B304721
theorem B301463 : Blo 199806 301463 := bstep (se 1 (by rfl) ⟨226097, by rfl⟩ : syracuseStep 301463 = 452195) B452195
theorem B203159 : Blo 199806 203159 := bstep (se 1 (by rfl) ⟨152369, by rfl⟩ : syracuseStep 203159 = 304739) B304739
theorem B203179 : Blo 199806 203179 := bstep (se 1 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 203179 = 304769) B304769
theorem B203191 : Blo 199806 203191 := bstep (se 1 (by rfl) ⟨152393, by rfl⟩ : syracuseStep 203191 = 304787) B304787
theorem B203211 : Blo 199806 203211 := bstep (se 1 (by rfl) ⟨152408, by rfl⟩ : syracuseStep 203211 = 304817) B304817
theorem B203223 : Blo 199806 203223 := bstep (se 1 (by rfl) ⟨152417, by rfl⟩ : syracuseStep 203223 = 304835) B304835
theorem B301529 : Blo 199806 301529 := bstep (se 2 (by rfl) ⟨113073, by rfl⟩ : syracuseStep 301529 = 226147) B226147
theorem B203243 : Blo 199806 203243 := bstep (se 1 (by rfl) ⟨152432, by rfl⟩ : syracuseStep 203243 = 304865) B304865
theorem B203255 : Blo 199806 203255 := bstep (se 1 (by rfl) ⟨152441, by rfl⟩ : syracuseStep 203255 = 304883) B304883
theorem B203275 : Blo 199806 203275 := bstep (se 1 (by rfl) ⟨152456, by rfl⟩ : syracuseStep 203275 = 304913) B304913
theorem B203287 : Blo 199806 203287 := bstep (se 1 (by rfl) ⟨152465, by rfl⟩ : syracuseStep 203287 = 304931) B304931
theorem B203307 : Blo 199806 203307 := bstep (se 1 (by rfl) ⟨152480, by rfl⟩ : syracuseStep 203307 = 304961) B304961
theorem B203319 : Blo 199806 203319 := bstep (se 1 (by rfl) ⟨152489, by rfl⟩ : syracuseStep 203319 = 304979) B304979
theorem B301643 : Blo 199806 301643 := bstep (se 1 (by rfl) ⟨226232, by rfl⟩ : syracuseStep 301643 = 452465) B452465
theorem B203339 : Blo 199806 203339 := bstep (se 1 (by rfl) ⟨152504, by rfl⟩ : syracuseStep 203339 = 305009) B305009
theorem B301655 : Blo 199806 301655 := bstep (se 1 (by rfl) ⟨226241, by rfl⟩ : syracuseStep 301655 = 452483) B452483
theorem B203351 : Blo 199806 203351 := bstep (se 1 (by rfl) ⟨152513, by rfl⟩ : syracuseStep 203351 = 305027) B305027
theorem B203371 : Blo 199806 203371 := bstep (se 1 (by rfl) ⟨152528, by rfl⟩ : syracuseStep 203371 = 305057) B305057
theorem B203383 : Blo 199806 203383 := bstep (se 1 (by rfl) ⟨152537, by rfl⟩ : syracuseStep 203383 = 305075) B305075
theorem B203403 : Blo 199806 203403 := bstep (se 1 (by rfl) ⟨152552, by rfl⟩ : syracuseStep 203403 = 305105) B305105
theorem B203415 : Blo 199806 203415 := bstep (se 1 (by rfl) ⟨152561, by rfl⟩ : syracuseStep 203415 = 305123) B305123
theorem B301721 : Blo 199806 301721 := bstep (se 2 (by rfl) ⟨113145, by rfl⟩ : syracuseStep 301721 = 226291) B226291
theorem B203435 : Blo 199806 203435 := bstep (se 1 (by rfl) ⟨152576, by rfl⟩ : syracuseStep 203435 = 305153) B305153
theorem B760499 : Blo 199806 760499 := bstep (se 1 (by rfl) ⟨570374, by rfl⟩ : syracuseStep 760499 = 1140749) B1140749
theorem B203447 : Blo 199806 203447 := bstep (se 1 (by rfl) ⟨152585, by rfl⟩ : syracuseStep 203447 = 305171) B305171
theorem B203467 : Blo 199806 203467 := bstep (se 1 (by rfl) ⟨152600, by rfl⟩ : syracuseStep 203467 = 305201) B305201
theorem B203479 : Blo 199806 203479 := bstep (se 1 (by rfl) ⟨152609, by rfl⟩ : syracuseStep 203479 = 305219) B305219
theorem B203499 : Blo 199806 203499 := bstep (se 1 (by rfl) ⟨152624, by rfl⟩ : syracuseStep 203499 = 305249) B305249
theorem B203511 : Blo 199806 203511 := bstep (se 1 (by rfl) ⟨152633, by rfl⟩ : syracuseStep 203511 = 305267) B305267
theorem B301835 : Blo 199806 301835 := bstep (se 1 (by rfl) ⟨226376, by rfl⟩ : syracuseStep 301835 = 452753) B452753
theorem B203531 : Blo 199806 203531 := bstep (se 1 (by rfl) ⟨152648, by rfl⟩ : syracuseStep 203531 = 305297) B305297
theorem B301847 : Blo 199806 301847 := bstep (se 1 (by rfl) ⟨226385, by rfl⟩ : syracuseStep 301847 = 452771) B452771
theorem B203543 : Blo 199806 203543 := bstep (se 1 (by rfl) ⟨152657, by rfl⟩ : syracuseStep 203543 = 305315) B305315
theorem B203563 : Blo 199806 203563 := bstep (se 1 (by rfl) ⟨152672, by rfl⟩ : syracuseStep 203563 = 305345) B305345
theorem B826163 : Blo 199806 826163 := bstep (se 1 (by rfl) ⟨619622, by rfl⟩ : syracuseStep 826163 = 1239245) B1239245
theorem B203575 : Blo 199806 203575 := bstep (se 1 (by rfl) ⟨152681, by rfl⟩ : syracuseStep 203575 = 305363) B305363
theorem B203595 : Blo 199806 203595 := bstep (se 1 (by rfl) ⟨152696, by rfl⟩ : syracuseStep 203595 = 305393) B305393
theorem B203607 : Blo 199806 203607 := bstep (se 1 (by rfl) ⟨152705, by rfl⟩ : syracuseStep 203607 = 305411) B305411
theorem B301913 : Blo 199806 301913 := bstep (se 2 (by rfl) ⟨113217, by rfl⟩ : syracuseStep 301913 = 226435) B226435
theorem B203627 : Blo 199806 203627 := bstep (se 1 (by rfl) ⟨152720, by rfl⟩ : syracuseStep 203627 = 305441) B305441
theorem B203639 : Blo 199806 203639 := bstep (se 1 (by rfl) ⟨152729, by rfl⟩ : syracuseStep 203639 = 305459) B305459
theorem B203659 : Blo 199806 203659 := bstep (se 1 (by rfl) ⟨152744, by rfl⟩ : syracuseStep 203659 = 305489) B305489
theorem B203671 : Blo 199806 203671 := bstep (se 1 (by rfl) ⟨152753, by rfl⟩ : syracuseStep 203671 = 305507) B305507
theorem B203691 : Blo 199806 203691 := bstep (se 1 (by rfl) ⟨152768, by rfl⟩ : syracuseStep 203691 = 305537) B305537
theorem B203703 : Blo 199806 203703 := bstep (se 1 (by rfl) ⟨152777, by rfl⟩ : syracuseStep 203703 = 305555) B305555
theorem B302027 : Blo 199806 302027 := bstep (se 1 (by rfl) ⟨226520, by rfl⟩ : syracuseStep 302027 = 453041) B453041
theorem B203723 : Blo 199806 203723 := bstep (se 1 (by rfl) ⟨152792, by rfl⟩ : syracuseStep 203723 = 305585) B305585
theorem B302039 : Blo 199806 302039 := bstep (se 1 (by rfl) ⟨226529, by rfl⟩ : syracuseStep 302039 = 453059) B453059
theorem B203735 : Blo 199806 203735 := bstep (se 1 (by rfl) ⟨152801, by rfl⟩ : syracuseStep 203735 = 305603) B305603
theorem B1252313 : Blo 199806 1252313 := bstep (se 2 (by rfl) ⟨469617, by rfl⟩ : syracuseStep 1252313 = 939235) B939235
theorem B203755 : Blo 199806 203755 := bstep (se 1 (by rfl) ⟨152816, by rfl⟩ : syracuseStep 203755 = 305633) B305633
theorem B203767 : Blo 199806 203767 := bstep (se 1 (by rfl) ⟨152825, by rfl⟩ : syracuseStep 203767 = 305651) B305651
theorem B433163 : Blo 199806 433163 := bstep (se 1 (by rfl) ⟨324872, by rfl⟩ : syracuseStep 433163 = 649745) B649745
theorem B203787 : Blo 199806 203787 := bstep (se 1 (by rfl) ⟨152840, by rfl⟩ : syracuseStep 203787 = 305681) B305681
theorem B203799 : Blo 199806 203799 := bstep (se 1 (by rfl) ⟨152849, by rfl⟩ : syracuseStep 203799 = 305699) B305699
theorem B302105 : Blo 199806 302105 := bstep (se 2 (by rfl) ⟨113289, by rfl⟩ : syracuseStep 302105 = 226579) B226579
theorem B302219 : Blo 199806 302219 := bstep (se 1 (by rfl) ⟨226664, by rfl⟩ : syracuseStep 302219 = 453329) B453329
theorem B302231 : Blo 199806 302231 := bstep (se 1 (by rfl) ⟨226673, by rfl⟩ : syracuseStep 302231 = 453347) B453347
theorem B302297 : Blo 199806 302297 := bstep (se 2 (by rfl) ⟨113361, by rfl⟩ : syracuseStep 302297 = 226723) B226723
theorem B302411 : Blo 199806 302411 := bstep (se 1 (by rfl) ⟨226808, by rfl⟩ : syracuseStep 302411 = 453617) B453617
theorem B302423 : Blo 199806 302423 := bstep (se 1 (by rfl) ⟨226817, by rfl⟩ : syracuseStep 302423 = 453635) B453635
theorem B302489 : Blo 199806 302489 := bstep (se 2 (by rfl) ⟨113433, by rfl⟩ : syracuseStep 302489 = 226867) B226867
theorem B302603 : Blo 199806 302603 := bstep (se 1 (by rfl) ⟨226952, by rfl⟩ : syracuseStep 302603 = 453905) B453905
theorem B302615 : Blo 199806 302615 := bstep (se 1 (by rfl) ⟨226961, by rfl⟩ : syracuseStep 302615 = 453923) B453923
theorem B302681 : Blo 199806 302681 := bstep (se 2 (by rfl) ⟨113505, by rfl⟩ : syracuseStep 302681 = 227011) B227011
theorem B302795 : Blo 199806 302795 := bstep (se 1 (by rfl) ⟨227096, by rfl⟩ : syracuseStep 302795 = 454193) B454193
theorem B302807 : Blo 199806 302807 := bstep (se 1 (by rfl) ⟨227105, by rfl⟩ : syracuseStep 302807 = 454211) B454211
theorem B433907 : Blo 199806 433907 := bstep (se 1 (by rfl) ⟨325430, by rfl⟩ : syracuseStep 433907 = 650861) B650861
theorem B302873 : Blo 199806 302873 := bstep (se 2 (by rfl) ⟨113577, by rfl⟩ : syracuseStep 302873 = 227155) B227155
theorem B5480257 : Blo 199806 5480257 := bstep (se 2 (by rfl) ⟨2055096, by rfl⟩ : syracuseStep 5480257 = 4110193) B4110193
theorem B270155 : Blo 199806 270155 := bstep (se 1 (by rfl) ⟨202616, by rfl⟩ : syracuseStep 270155 = 405233) B405233
theorem B302987 : Blo 199806 302987 := bstep (se 1 (by rfl) ⟨227240, by rfl⟩ : syracuseStep 302987 = 454481) B454481
theorem B302999 : Blo 199806 302999 := bstep (se 1 (by rfl) ⟨227249, by rfl⟩ : syracuseStep 302999 = 454499) B454499
theorem B303065 : Blo 199806 303065 := bstep (se 2 (by rfl) ⟨113649, by rfl⟩ : syracuseStep 303065 = 227299) B227299
theorem B368651 : Blo 199806 368651 := bstep (se 1 (by rfl) ⟨276488, by rfl⟩ : syracuseStep 368651 = 552977) B552977
theorem B303179 : Blo 199806 303179 := bstep (se 1 (by rfl) ⟨227384, by rfl⟩ : syracuseStep 303179 = 454769) B454769
theorem B303191 : Blo 199806 303191 := bstep (se 1 (by rfl) ⟨227393, by rfl⟩ : syracuseStep 303191 = 454787) B454787
theorem B761987 : Blo 199806 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B860311 : Blo 199806 860311 := bstep (se 1 (by rfl) ⟨645233, by rfl⟩ : syracuseStep 860311 = 1290467) B1290467
theorem B1646743 : Blo 199806 1646743 := bstep (se 1 (by rfl) ⟨1235057, by rfl⟩ : syracuseStep 1646743 = 2470115) B2470115
theorem B303257 : Blo 199806 303257 := bstep (se 2 (by rfl) ⟨113721, by rfl⟩ : syracuseStep 303257 = 227443) B227443
theorem B1450163 : Blo 199806 1450163 := bstep (se 1 (by rfl) ⟨1087622, by rfl⟩ : syracuseStep 1450163 = 2175245) B2175245
theorem B860381 : Blo 199806 860381 := bstep (se 3 (by rfl) ⟨161321, by rfl⟩ : syracuseStep 860381 = 322643) B322643
theorem B303371 : Blo 199806 303371 := bstep (se 1 (by rfl) ⟨227528, by rfl⟩ : syracuseStep 303371 = 455057) B455057
theorem B303383 : Blo 199806 303383 := bstep (se 1 (by rfl) ⟨227537, by rfl⟩ : syracuseStep 303383 = 455075) B455075
theorem B303449 : Blo 199806 303449 := bstep (se 2 (by rfl) ⟨113793, by rfl⟩ : syracuseStep 303449 = 227587) B227587
theorem B1450391 : Blo 199806 1450391 := bstep (se 1 (by rfl) ⟨1087793, by rfl⟩ : syracuseStep 1450391 = 2175587) B2175587
theorem B2564531 : Blo 199806 2564531 := bstep (se 1 (by rfl) ⟨1923398, by rfl⟩ : syracuseStep 2564531 = 3846797) B3846797
theorem B303563 : Blo 199806 303563 := bstep (se 1 (by rfl) ⟨227672, by rfl⟩ : syracuseStep 303563 = 455345) B455345
theorem B303575 : Blo 199806 303575 := bstep (se 1 (by rfl) ⟨227681, by rfl⟩ : syracuseStep 303575 = 455363) B455363
theorem B303641 : Blo 199806 303641 := bstep (se 2 (by rfl) ⟨113865, by rfl⟩ : syracuseStep 303641 = 227731) B227731
theorem B762443 : Blo 199806 762443 := bstep (se 1 (by rfl) ⟨571832, by rfl⟩ : syracuseStep 762443 = 1143665) B1143665
theorem B434803 : Blo 199806 434803 := bstep (se 1 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 434803 = 652205) B652205
theorem B303755 : Blo 199806 303755 := bstep (se 1 (by rfl) ⟨227816, by rfl⟩ : syracuseStep 303755 = 455633) B455633
theorem B303767 : Blo 199806 303767 := bstep (se 1 (by rfl) ⟨227825, by rfl⟩ : syracuseStep 303767 = 455651) B455651
theorem B271063 : Blo 199806 271063 := bstep (se 1 (by rfl) ⟨203297, by rfl⟩ : syracuseStep 271063 = 406595) B406595
theorem B303833 : Blo 199806 303833 := bstep (se 2 (by rfl) ⟨113937, by rfl⟩ : syracuseStep 303833 = 227875) B227875
theorem B3842801 : Blo 199806 3842801 := bstep (se 2 (by rfl) ⟨1441050, by rfl⟩ : syracuseStep 3842801 = 2882101) B2882101
theorem B762641 : Blo 199806 762641 := bstep (se 2 (by rfl) ⟨285990, by rfl⟩ : syracuseStep 762641 = 571981) B571981
theorem B303947 : Blo 199806 303947 := bstep (se 1 (by rfl) ⟨227960, by rfl⟩ : syracuseStep 303947 = 455921) B455921
theorem B303959 : Blo 199806 303959 := bstep (se 1 (by rfl) ⟨227969, by rfl⟩ : syracuseStep 303959 = 455939) B455939
theorem B304025 : Blo 199806 304025 := bstep (se 2 (by rfl) ⟨114009, by rfl⟩ : syracuseStep 304025 = 228019) B228019
theorem B861131 : Blo 199806 861131 := bstep (se 1 (by rfl) ⟨645848, by rfl⟩ : syracuseStep 861131 = 1291697) B1291697
theorem B304139 : Blo 199806 304139 := bstep (se 1 (by rfl) ⟨228104, by rfl⟩ : syracuseStep 304139 = 456209) B456209
theorem B304151 : Blo 199806 304151 := bstep (se 1 (by rfl) ⟨228113, by rfl⟩ : syracuseStep 304151 = 456227) B456227
theorem B304217 : Blo 199806 304217 := bstep (se 2 (by rfl) ⟨114081, by rfl⟩ : syracuseStep 304217 = 228163) B228163
theorem B304331 : Blo 199806 304331 := bstep (se 1 (by rfl) ⟨228248, by rfl⟩ : syracuseStep 304331 = 456497) B456497
theorem B304343 : Blo 199806 304343 := bstep (se 1 (by rfl) ⟨228257, by rfl⟩ : syracuseStep 304343 = 456515) B456515
theorem B1025297 : Blo 199806 1025297 := bstep (se 2 (by rfl) ⟨384486, by rfl⟩ : syracuseStep 1025297 = 768973) B768973
theorem B304409 : Blo 199806 304409 := bstep (se 2 (by rfl) ⟨114153, by rfl⟩ : syracuseStep 304409 = 228307) B228307
theorem B304523 : Blo 199806 304523 := bstep (se 1 (by rfl) ⟨228392, by rfl⟩ : syracuseStep 304523 = 456785) B456785
theorem B1287575 : Blo 199806 1287575 := bstep (se 1 (by rfl) ⟨965681, by rfl⟩ : syracuseStep 1287575 = 1931363) B1931363
theorem B304535 : Blo 199806 304535 := bstep (se 1 (by rfl) ⟨228401, by rfl⟩ : syracuseStep 304535 = 456803) B456803
theorem B1025459 : Blo 199806 1025459 := bstep (se 1 (by rfl) ⟨769094, by rfl⟩ : syracuseStep 1025459 = 1538189) B1538189
theorem B271819 : Blo 199806 271819 := bstep (se 1 (by rfl) ⟨203864, by rfl⟩ : syracuseStep 271819 = 407729) B407729
theorem B304601 : Blo 199806 304601 := bstep (se 2 (by rfl) ⟨114225, by rfl⟩ : syracuseStep 304601 = 228451) B228451
theorem B2991629 : Blo 199806 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B763415 : Blo 199806 763415 := bstep (se 1 (by rfl) ⟨572561, by rfl⟩ : syracuseStep 763415 = 1145123) B1145123
theorem B304715 : Blo 199806 304715 := bstep (se 1 (by rfl) ⟨228536, by rfl⟩ : syracuseStep 304715 = 457073) B457073
theorem B304727 : Blo 199806 304727 := bstep (se 1 (by rfl) ⟨228545, by rfl⟩ : syracuseStep 304727 = 457091) B457091
theorem B337547 : Blo 199806 337547 := bstep (se 1 (by rfl) ⟨253160, by rfl⟩ : syracuseStep 337547 = 506321) B506321
theorem B2303639 : Blo 199806 2303639 := bstep (se 1 (by rfl) ⟨1727729, by rfl⟩ : syracuseStep 2303639 = 3455459) B3455459
theorem B304793 : Blo 199806 304793 := bstep (se 2 (by rfl) ⟨114297, by rfl⟩ : syracuseStep 304793 = 228595) B228595
theorem B1156787 : Blo 199806 1156787 := bstep (se 1 (by rfl) ⟨867590, by rfl⟩ : syracuseStep 1156787 = 1735181) B1735181
theorem B763613 : Blo 199806 763613 := bstep (se 3 (by rfl) ⟨143177, by rfl⟩ : syracuseStep 763613 = 286355) B286355
theorem B337675 : Blo 199806 337675 := bstep (se 1 (by rfl) ⟨253256, by rfl⟩ : syracuseStep 337675 = 506513) B506513
theorem B304907 : Blo 199806 304907 := bstep (se 1 (by rfl) ⟨228680, by rfl⟩ : syracuseStep 304907 = 457361) B457361
theorem B304919 : Blo 199806 304919 := bstep (se 1 (by rfl) ⟨228689, by rfl⟩ : syracuseStep 304919 = 457379) B457379
theorem B304985 : Blo 199806 304985 := bstep (se 2 (by rfl) ⟨114369, by rfl⟩ : syracuseStep 304985 = 228739) B228739
theorem B337817 : Blo 199806 337817 := bstep (se 2 (by rfl) ⟨126681, by rfl⟩ : syracuseStep 337817 = 253363) B253363
theorem B305099 : Blo 199806 305099 := bstep (se 1 (by rfl) ⟨228824, by rfl⟩ : syracuseStep 305099 = 457649) B457649
theorem B305111 : Blo 199806 305111 := bstep (se 1 (by rfl) ⟨228833, by rfl⟩ : syracuseStep 305111 = 457667) B457667
theorem B337945 : Blo 199806 337945 := bstep (se 2 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 337945 = 253459) B253459
theorem B305177 : Blo 199806 305177 := bstep (se 2 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 305177 = 228883) B228883
theorem B305291 : Blo 199806 305291 := bstep (se 1 (by rfl) ⟨228968, by rfl⟩ : syracuseStep 305291 = 457937) B457937
theorem B305303 : Blo 199806 305303 := bstep (se 1 (by rfl) ⟨228977, by rfl⟩ : syracuseStep 305303 = 457955) B457955
theorem B731339 : Blo 199806 731339 := bstep (se 1 (by rfl) ⟨548504, by rfl⟩ : syracuseStep 731339 = 1097009) B1097009
theorem B3451085 : Blo 199806 3451085 := bstep (se 3 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 3451085 = 1294157) B1294157
theorem B305369 : Blo 199806 305369 := bstep (se 2 (by rfl) ⟨114513, by rfl⟩ : syracuseStep 305369 = 229027) B229027
theorem B305483 : Blo 199806 305483 := bstep (se 1 (by rfl) ⟨229112, by rfl⟩ : syracuseStep 305483 = 458225) B458225
theorem B305495 : Blo 199806 305495 := bstep (se 1 (by rfl) ⟨229121, by rfl⟩ : syracuseStep 305495 = 458243) B458243
theorem B305561 : Blo 199806 305561 := bstep (se 2 (by rfl) ⟨114585, by rfl⟩ : syracuseStep 305561 = 229171) B229171
theorem B272857 : Blo 199806 272857 := bstep (se 2 (by rfl) ⟨102321, by rfl⟩ : syracuseStep 272857 = 204643) B204643
theorem B305675 : Blo 199806 305675 := bstep (se 1 (by rfl) ⟨229256, by rfl⟩ : syracuseStep 305675 = 458513) B458513
theorem B305687 : Blo 199806 305687 := bstep (se 1 (by rfl) ⟨229265, by rfl⟩ : syracuseStep 305687 = 458531) B458531
theorem B338519 : Blo 199806 338519 := bstep (se 1 (by rfl) ⟨253889, by rfl⟩ : syracuseStep 338519 = 507779) B507779
theorem B338647 : Blo 199806 338647 := bstep (se 1 (by rfl) ⟨253985, by rfl⟩ : syracuseStep 338647 = 507971) B507971
theorem B1452761 : Blo 199806 1452761 := bstep (se 2 (by rfl) ⟨544785, by rfl⟩ : syracuseStep 1452761 = 1089571) B1089571
theorem B306137 : Blo 199806 306137 := bstep (se 2 (by rfl) ⟨114801, by rfl⟩ : syracuseStep 306137 = 229603) B229603
theorem B1158245 : Blo 199806 1158245 := bstep (se 4 (by rfl) ⟨108585, by rfl⟩ : syracuseStep 1158245 = 217171) B217171
theorem B6991109 : Blo 199806 6991109 := bstep (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) B1310833
theorem B339275 : Blo 199806 339275 := bstep (se 1 (by rfl) ⟨254456, by rfl⟩ : syracuseStep 339275 = 508913) B508913
theorem B1027403 : Blo 199806 1027403 := bstep (se 1 (by rfl) ⟨770552, by rfl⟩ : syracuseStep 1027403 = 1541105) B1541105
theorem B339403 : Blo 199806 339403 := bstep (se 1 (by rfl) ⟨254552, by rfl⟩ : syracuseStep 339403 = 509105) B509105
theorem B241175 : Blo 199806 241175 := bstep (se 1 (by rfl) ⟨180881, by rfl⟩ : syracuseStep 241175 = 361763) B361763
theorem B339545 : Blo 199806 339545 := bstep (se 2 (by rfl) ⟨127329, by rfl⟩ : syracuseStep 339545 = 254659) B254659
theorem B1519235 : Blo 199806 1519235 := bstep (se 1 (by rfl) ⟨1139426, by rfl⟩ : syracuseStep 1519235 = 2278853) B2278853
theorem B765571 : Blo 199806 765571 := bstep (se 1 (by rfl) ⟨574178, by rfl⟩ : syracuseStep 765571 = 1148357) B1148357
theorem B339673 : Blo 199806 339673 := bstep (se 2 (by rfl) ⟨127377, by rfl⟩ : syracuseStep 339673 = 254755) B254755
theorem B241483 : Blo 199806 241483 := bstep (se 1 (by rfl) ⟨181112, by rfl⟩ : syracuseStep 241483 = 362225) B362225
theorem B405427 : Blo 199806 405427 := bstep (se 1 (by rfl) ⟨304070, by rfl⟩ : syracuseStep 405427 = 608141) B608141
theorem B765875 : Blo 199806 765875 := bstep (se 1 (by rfl) ⟨574406, by rfl⟩ : syracuseStep 765875 = 1148813) B1148813
theorem B569281 : Blo 199806 569281 := bstep (se 2 (by rfl) ⟨213480, by rfl⟩ : syracuseStep 569281 = 426961) B426961
theorem B241867 : Blo 199806 241867 := bstep (se 1 (by rfl) ⟨181400, by rfl⟩ : syracuseStep 241867 = 362801) B362801
theorem B340247 : Blo 199806 340247 := bstep (se 1 (by rfl) ⟨255185, by rfl⟩ : syracuseStep 340247 = 510371) B510371
theorem B405847 : Blo 199806 405847 := bstep (se 1 (by rfl) ⟨304385, by rfl⟩ : syracuseStep 405847 = 608771) B608771
theorem B340375 : Blo 199806 340375 := bstep (se 1 (by rfl) ⟨255281, by rfl⟩ : syracuseStep 340375 = 510563) B510563
theorem B405913 : Blo 199806 405913 := bstep (se 2 (by rfl) ⟨152217, by rfl⟩ : syracuseStep 405913 = 304435) B304435
theorem B864685 : Blo 199806 864685 := bstep (se 3 (by rfl) ⟨162128, by rfl⟩ : syracuseStep 864685 = 324257) B324257
theorem B1716659 : Blo 199806 1716659 := bstep (se 1 (by rfl) ⟨1287494, by rfl⟩ : syracuseStep 1716659 = 2574989) B2574989
theorem B6238691 : Blo 199806 6238691 := bstep (se 1 (by rfl) ⟨4679018, by rfl⟩ : syracuseStep 6238691 = 9358037) B9358037
theorem B766529 : Blo 199806 766529 := bstep (se 2 (by rfl) ⟨287448, by rfl⟩ : syracuseStep 766529 = 574897) B574897
theorem B864857 : Blo 199806 864857 := bstep (se 2 (by rfl) ⟨324321, by rfl⟩ : syracuseStep 864857 = 648643) B648643
theorem B1749721 : Blo 199806 1749721 := bstep (se 2 (by rfl) ⟨656145, by rfl⟩ : syracuseStep 1749721 = 1312291) B1312291
theorem B1717037 : Blo 199806 1717037 := bstep (se 3 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 1717037 = 643889) B643889
theorem B439283 : Blo 199806 439283 := bstep (se 1 (by rfl) ⟨329462, by rfl⟩ : syracuseStep 439283 = 658925) B658925
theorem B341003 : Blo 199806 341003 := bstep (se 1 (by rfl) ⟨255752, by rfl⟩ : syracuseStep 341003 = 511505) B511505
theorem B1029185 : Blo 199806 1029185 := bstep (se 2 (by rfl) ⟨385944, by rfl⟩ : syracuseStep 1029185 = 771889) B771889
theorem B341131 : Blo 199806 341131 := bstep (se 1 (by rfl) ⟨255848, by rfl⟩ : syracuseStep 341131 = 511697) B511697
theorem B439553 : Blo 199806 439553 := bstep (se 2 (by rfl) ⟨164832, by rfl⟩ : syracuseStep 439553 = 329665) B329665
theorem B341273 : Blo 199806 341273 := bstep (se 2 (by rfl) ⟨127977, by rfl⟩ : syracuseStep 341273 = 255955) B255955
theorem B341401 : Blo 199806 341401 := bstep (se 2 (by rfl) ⟨128025, by rfl⟩ : syracuseStep 341401 = 256051) B256051
theorem B767789 : Blo 199806 767789 := bstep (se 3 (by rfl) ⟨143960, by rfl⟩ : syracuseStep 767789 = 287921) B287921
theorem B1292107 : Blo 199806 1292107 := bstep (se 1 (by rfl) ⟨969080, by rfl⟩ : syracuseStep 1292107 = 1938161) B1938161
theorem B767819 : Blo 199806 767819 := bstep (se 1 (by rfl) ⟨575864, by rfl⟩ : syracuseStep 767819 = 1151729) B1151729
theorem B341975 : Blo 199806 341975 := bstep (se 1 (by rfl) ⟨256481, by rfl⟩ : syracuseStep 341975 = 512963) B512963
theorem B14956597 : Blo 199806 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B342103 : Blo 199806 342103 := bstep (se 1 (by rfl) ⟨256577, by rfl⟩ : syracuseStep 342103 = 513155) B513155
theorem B866497 : Blo 199806 866497 := bstep (se 2 (by rfl) ⟨324936, by rfl⟩ : syracuseStep 866497 = 649873) B649873
theorem B571799 : Blo 199806 571799 := bstep (se 1 (by rfl) ⟨428849, by rfl⟩ : syracuseStep 571799 = 857699) B857699
theorem B1292723 : Blo 199806 1292723 := bstep (se 1 (by rfl) ⟨969542, by rfl⟩ : syracuseStep 1292723 = 1939085) B1939085
theorem B768473 : Blo 199806 768473 := bstep (se 2 (by rfl) ⟨288177, by rfl⟩ : syracuseStep 768473 = 576355) B576355
theorem B342731 : Blo 199806 342731 := bstep (se 1 (by rfl) ⟨257048, by rfl⟩ : syracuseStep 342731 = 514097) B514097
theorem B768791 : Blo 199806 768791 := bstep (se 1 (by rfl) ⟨576593, by rfl⟩ : syracuseStep 768791 = 1153187) B1153187
theorem B506675 : Blo 199806 506675 := bstep (se 1 (by rfl) ⟨380006, by rfl⟩ : syracuseStep 506675 = 760013) B760013
theorem B408395 : Blo 199806 408395 := bstep (se 1 (by rfl) ⟨306296, by rfl⟩ : syracuseStep 408395 = 612593) B612593
theorem B342859 : Blo 199806 342859 := bstep (se 1 (by rfl) ⟨257144, by rfl⟩ : syracuseStep 342859 = 514289) B514289
theorem B1358693 : Blo 199806 1358693 := bstep (se 4 (by rfl) ⟨127377, by rfl⟩ : syracuseStep 1358693 = 254755) B254755
theorem B1522637 : Blo 199806 1522637 := bstep (se 3 (by rfl) ⟨285494, by rfl⟩ : syracuseStep 1522637 = 570989) B570989
theorem B343001 : Blo 199806 343001 := bstep (se 2 (by rfl) ⟨128625, by rfl⟩ : syracuseStep 343001 = 257251) B257251
theorem B1031129 : Blo 199806 1031129 := bstep (se 2 (by rfl) ⟨386673, by rfl⟩ : syracuseStep 1031129 = 773347) B773347
theorem B506969 : Blo 199806 506969 := bstep (se 2 (by rfl) ⟨190113, by rfl⟩ : syracuseStep 506969 = 380227) B380227
theorem B343129 : Blo 199806 343129 := bstep (se 2 (by rfl) ⟨128673, by rfl⟩ : syracuseStep 343129 = 257347) B257347
theorem B343435 : Blo 199806 343435 := bstep (se 1 (by rfl) ⟨257576, by rfl⟩ : syracuseStep 343435 = 515153) B515153
theorem B1523123 : Blo 199806 1523123 := bstep (se 1 (by rfl) ⟨1142342, by rfl⟩ : syracuseStep 1523123 = 2284685) B2284685
theorem B769459 : Blo 199806 769459 := bstep (se 1 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 769459 = 1154189) B1154189
theorem B343703 : Blo 199806 343703 := bstep (se 1 (by rfl) ⟨257777, by rfl⟩ : syracuseStep 343703 = 515555) B515555
theorem B573131 : Blo 199806 573131 := bstep (se 1 (by rfl) ⟨429848, by rfl⟩ : syracuseStep 573131 = 859697) B859697
theorem B409303 : Blo 199806 409303 := bstep (se 1 (by rfl) ⟨306977, by rfl⟩ : syracuseStep 409303 = 613955) B613955
theorem B343831 : Blo 199806 343831 := bstep (se 1 (by rfl) ⟨257873, by rfl⟩ : syracuseStep 343831 = 515747) B515747
theorem B868171 : Blo 199806 868171 := bstep (se 1 (by rfl) ⟨651128, by rfl⟩ : syracuseStep 868171 = 1302257) B1302257
theorem B868445 : Blo 199806 868445 := bstep (se 3 (by rfl) ⟨162833, by rfl⟩ : syracuseStep 868445 = 325667) B325667
theorem B1851569 : Blo 199806 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B2900555 : Blo 199806 2900555 := bstep (se 1 (by rfl) ⟨2175416, by rfl⟩ : syracuseStep 2900555 = 4350833) B4350833
theorem B1229413 : Blo 199806 1229413 := bstep (se 4 (by rfl) ⟨115257, by rfl⟩ : syracuseStep 1229413 = 230515) B230515
theorem B770705 : Blo 199806 770705 := bstep (se 2 (by rfl) ⟨289014, by rfl⟩ : syracuseStep 770705 = 578029) B578029
theorem B508619 : Blo 199806 508619 := bstep (se 1 (by rfl) ⟨381464, by rfl⟩ : syracuseStep 508619 = 762929) B762929
theorem B1524581 : Blo 199806 1524581 := bstep (se 4 (by rfl) ⟨142929, by rfl⟩ : syracuseStep 1524581 = 285859) B285859
theorem B213899 : Blo 199806 213899 := bstep (se 1 (by rfl) ⟨160424, by rfl⟩ : syracuseStep 213899 = 320849) B320849
theorem B967697 : Blo 199806 967697 := bstep (se 2 (by rfl) ⟨362886, by rfl⟩ : syracuseStep 967697 = 725773) B725773
theorem B1557521 : Blo 199806 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B1950925 : Blo 199806 1950925 := bstep (se 3 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 1950925 = 731597) B731597
theorem B574771 : Blo 199806 574771 := bstep (se 1 (by rfl) ⟨431078, by rfl⟩ : syracuseStep 574771 = 862157) B862157
theorem B771403 : Blo 199806 771403 := bstep (se 1 (by rfl) ⟨578552, by rfl⟩ : syracuseStep 771403 = 1157105) B1157105
theorem B1525067 : Blo 199806 1525067 := bstep (se 1 (by rfl) ⟨1143800, by rfl⟩ : syracuseStep 1525067 = 2287601) B2287601
theorem B1230173 : Blo 199806 1230173 := bstep (se 3 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 1230173 = 461315) B461315
theorem B411031 : Blo 199806 411031 := bstep (se 1 (by rfl) ⟨308273, by rfl⟩ : syracuseStep 411031 = 616547) B616547
theorem B411095 : Blo 199806 411095 := bstep (se 1 (by rfl) ⟨308321, by rfl⟩ : syracuseStep 411095 = 616643) B616643
theorem B771677 : Blo 199806 771677 := bstep (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) B289379
theorem B509591 : Blo 199806 509591 := bstep (se 1 (by rfl) ⟨382193, by rfl⟩ : syracuseStep 509591 = 764387) B764387
theorem B214903 : Blo 199806 214903 := bstep (se 1 (by rfl) ⟨161177, by rfl⟩ : syracuseStep 214903 = 322355) B322355
theorem B1460429 : Blo 199806 1460429 := bstep (se 3 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 1460429 = 547661) B547661
theorem B1099993 : Blo 199806 1099993 := bstep (se 2 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 1099993 = 824995) B824995
theorem B739601 : Blo 199806 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B772375 : Blo 199806 772375 := bstep (se 1 (by rfl) ⟨579281, by rfl⟩ : syracuseStep 772375 = 1158563) B1158563
theorem B510259 : Blo 199806 510259 := bstep (se 1 (by rfl) ⟨382694, by rfl⟩ : syracuseStep 510259 = 765389) B765389
theorem B575819 : Blo 199806 575819 := bstep (se 1 (by rfl) ⟨431864, by rfl⟩ : syracuseStep 575819 = 863729) B863729
theorem B510401 : Blo 199806 510401 := bstep (se 2 (by rfl) ⟨191400, by rfl⟩ : syracuseStep 510401 = 382801) B382801
theorem B215659 : Blo 199806 215659 := bstep (se 1 (by rfl) ⟨161744, by rfl⟩ : syracuseStep 215659 = 323489) B323489
theorem B1428515 : Blo 199806 1428515 := bstep (se 1 (by rfl) ⟨1071386, by rfl⟩ : syracuseStep 1428515 = 2142773) B2142773
theorem B773165 : Blo 199806 773165 := bstep (se 3 (by rfl) ⟨144968, by rfl⟩ : syracuseStep 773165 = 289937) B289937
theorem B674891 : Blo 199806 674891 := bstep (se 1 (by rfl) ⟨506168, by rfl⟩ : syracuseStep 674891 = 1012337) B1012337
theorem B379991 : Blo 199806 379991 := bstep (se 1 (by rfl) ⟨284993, by rfl⟩ : syracuseStep 379991 = 569987) B569987
theorem B3853493 : Blo 199806 3853493 := bstep (se 5 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 3853493 = 361265) B361265
theorem B675161 : Blo 199806 675161 := bstep (se 2 (by rfl) ⟨253185, by rfl⟩ : syracuseStep 675161 = 506371) B506371
theorem B642455 : Blo 199806 642455 := bstep (se 1 (by rfl) ⟨481841, by rfl⟩ : syracuseStep 642455 = 963683) B963683
theorem B413171 : Blo 199806 413171 := bstep (se 1 (by rfl) ⟨309878, by rfl⟩ : syracuseStep 413171 = 619757) B619757
theorem B1035841 : Blo 199806 1035841 := bstep (se 2 (by rfl) ⟨388440, by rfl⟩ : syracuseStep 1035841 = 776881) B776881
theorem B380531 : Blo 199806 380531 := bstep (se 1 (by rfl) ⟨285398, by rfl⟩ : syracuseStep 380531 = 570797) B570797
theorem B511667 : Blo 199806 511667 := bstep (se 1 (by rfl) ⟨383750, by rfl⟩ : syracuseStep 511667 = 767501) B767501
theorem B577459 : Blo 199806 577459 := bstep (se 1 (by rfl) ⟨433094, by rfl⟩ : syracuseStep 577459 = 866189) B866189
theorem B675863 : Blo 199806 675863 := bstep (se 1 (by rfl) ⟨506897, by rfl⟩ : syracuseStep 675863 = 1013795) B1013795
theorem B610327 : Blo 199806 610327 := bstep (se 1 (by rfl) ⟨457745, by rfl⟩ : syracuseStep 610327 = 915491) B915491
theorem B381017 : Blo 199806 381017 := bstep (se 2 (by rfl) ⟨142881, by rfl⟩ : syracuseStep 381017 = 285763) B285763
theorem B577687 : Blo 199806 577687 := bstep (se 1 (by rfl) ⟨433265, by rfl⟩ : syracuseStep 577687 = 866531) B866531
theorem B2904245 : Blo 199806 2904245 := bstep (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) B272273
theorem B512203 : Blo 199806 512203 := bstep (se 1 (by rfl) ⟨384152, by rfl⟩ : syracuseStep 512203 = 768305) B768305
theorem B512345 : Blo 199806 512345 := bstep (se 2 (by rfl) ⟨192129, by rfl⟩ : syracuseStep 512345 = 384259) B384259
theorem B1921553 : Blo 199806 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B676403 : Blo 199806 676403 := bstep (se 1 (by rfl) ⟨507302, by rfl⟩ : syracuseStep 676403 = 1014605) B1014605
theorem B676673 : Blo 199806 676673 := bstep (se 2 (by rfl) ⟨253752, by rfl⟩ : syracuseStep 676673 = 507505) B507505
theorem B2053043 : Blo 199806 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B513175 : Blo 199806 513175 := bstep (se 1 (by rfl) ⟨384881, by rfl⟩ : syracuseStep 513175 = 769763) B769763
theorem B480563 : Blo 199806 480563 := bstep (se 1 (by rfl) ⟨360422, by rfl⟩ : syracuseStep 480563 = 720845) B720845
theorem B677213 : Blo 199806 677213 := bstep (se 3 (by rfl) ⟨126977, by rfl⟩ : syracuseStep 677213 = 253955) B253955
theorem B382475 : Blo 199806 382475 := bstep (se 1 (by rfl) ⟨286856, by rfl⟩ : syracuseStep 382475 = 573713) B573713
theorem B513611 : Blo 199806 513611 := bstep (se 1 (by rfl) ⟨385208, by rfl⟩ : syracuseStep 513611 = 770417) B770417
theorem B382657 : Blo 199806 382657 := bstep (se 2 (by rfl) ⟨143496, by rfl⟩ : syracuseStep 382657 = 286993) B286993
theorem B644915 : Blo 199806 644915 := bstep (se 1 (by rfl) ⟨483686, by rfl⟩ : syracuseStep 644915 = 967373) B967373
theorem B513985 : Blo 199806 513985 := bstep (se 2 (by rfl) ⟨192744, by rfl⟩ : syracuseStep 513985 = 385489) B385489
theorem B579545 : Blo 199806 579545 := bstep (se 2 (by rfl) ⟨217329, by rfl⟩ : syracuseStep 579545 = 434659) B434659
theorem B383105 : Blo 199806 383105 := bstep (se 2 (by rfl) ⟨143664, by rfl⟩ : syracuseStep 383105 = 287329) B287329
theorem B1038467 : Blo 199806 1038467 := bstep (se 1 (by rfl) ⟨778850, by rfl⟩ : syracuseStep 1038467 = 1557701) B1557701
theorem B1300697 : Blo 199806 1300697 := bstep (se 2 (by rfl) ⟨487761, by rfl⟩ : syracuseStep 1300697 = 975523) B975523
theorem B678347 : Blo 199806 678347 := bstep (se 1 (by rfl) ⟨508760, by rfl⟩ : syracuseStep 678347 = 1017521) B1017521
theorem B383447 : Blo 199806 383447 := bstep (se 1 (by rfl) ⟨287585, by rfl⟩ : syracuseStep 383447 = 575171) B575171
theorem B2316761 : Blo 199806 2316761 := bstep (se 2 (by rfl) ⟨868785, by rfl⟩ : syracuseStep 2316761 = 1737571) B1737571
theorem B350743 : Blo 199806 350743 := bstep (se 1 (by rfl) ⟨263057, by rfl⟩ : syracuseStep 350743 = 526115) B526115
theorem B514583 : Blo 199806 514583 := bstep (se 1 (by rfl) ⟨385937, by rfl⟩ : syracuseStep 514583 = 771875) B771875
theorem B1530413 : Blo 199806 1530413 := bstep (se 3 (by rfl) ⟨286952, by rfl⟩ : syracuseStep 1530413 = 573905) B573905
theorem B1464925 : Blo 199806 1464925 := bstep (se 3 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 1464925 = 549347) B549347
theorem B678617 : Blo 199806 678617 := bstep (se 2 (by rfl) ⟨254481, by rfl⟩ : syracuseStep 678617 = 508963) B508963
theorem B285643 : Blo 199806 285643 := bstep (se 1 (by rfl) ⟨214232, by rfl⟩ : syracuseStep 285643 = 428465) B428465
theorem B3300365 : Blo 199806 3300365 := bstep (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) B1237637
theorem B613441 : Blo 199806 613441 := bstep (se 2 (by rfl) ⟨230040, by rfl⟩ : syracuseStep 613441 = 460081) B460081
theorem B973889 : Blo 199806 973889 := bstep (se 2 (by rfl) ⟨365208, by rfl⟩ : syracuseStep 973889 = 730417) B730417
theorem B384115 : Blo 199806 384115 := bstep (se 1 (by rfl) ⟨288086, by rfl⟩ : syracuseStep 384115 = 576173) B576173
theorem B449675 : Blo 199806 449675 := bstep (se 1 (by rfl) ⟨337256, by rfl⟩ : syracuseStep 449675 = 674513) B674513
theorem B449729 : Blo 199806 449729 := bstep (se 2 (by rfl) ⟨168648, by rfl⟩ : syracuseStep 449729 = 337297) B337297
theorem B1039661 : Blo 199806 1039661 := bstep (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) B389873
theorem B515393 : Blo 199806 515393 := bstep (se 2 (by rfl) ⟨193272, by rfl⟩ : syracuseStep 515393 = 386545) B386545
theorem B679319 : Blo 199806 679319 := bstep (se 1 (by rfl) ⟨509489, by rfl⟩ : syracuseStep 679319 = 1018979) B1018979
theorem B449945 : Blo 199806 449945 := bstep (se 2 (by rfl) ⟨168729, by rfl⟩ : syracuseStep 449945 = 337459) B337459
theorem B548299 : Blo 199806 548299 := bstep (se 1 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 548299 = 822449) B822449
theorem B450035 : Blo 199806 450035 := bstep (se 1 (by rfl) ⟨337526, by rfl⟩ : syracuseStep 450035 = 675053) B675053
theorem B450071 : Blo 199806 450071 := bstep (se 1 (by rfl) ⟨337553, by rfl⟩ : syracuseStep 450071 = 675107) B675107
theorem B384563 : Blo 199806 384563 := bstep (se 1 (by rfl) ⟨288422, by rfl⟩ : syracuseStep 384563 = 576845) B576845
theorem B384601 : Blo 199806 384601 := bstep (se 2 (by rfl) ⟨144225, by rfl⟩ : syracuseStep 384601 = 288451) B288451
theorem B450251 : Blo 199806 450251 := bstep (se 1 (by rfl) ⟨337688, by rfl⟩ : syracuseStep 450251 = 675377) B675377
theorem B450305 : Blo 199806 450305 := bstep (se 2 (by rfl) ⟨168864, by rfl⟩ : syracuseStep 450305 = 337729) B337729
theorem B253783 : Blo 199806 253783 := bstep (se 1 (by rfl) ⟨190337, by rfl⟩ : syracuseStep 253783 = 380675) B380675
theorem B679859 : Blo 199806 679859 := bstep (se 1 (by rfl) ⟨509894, by rfl⟩ : syracuseStep 679859 = 1019789) B1019789
theorem B450521 : Blo 199806 450521 := bstep (se 2 (by rfl) ⟨168945, by rfl⟩ : syracuseStep 450521 = 337891) B337891
theorem B385049 : Blo 199806 385049 := bstep (se 2 (by rfl) ⟨144393, by rfl⟩ : syracuseStep 385049 = 288787) B288787
theorem B450611 : Blo 199806 450611 := bstep (se 1 (by rfl) ⟨337958, by rfl⟩ : syracuseStep 450611 = 675917) B675917
theorem B450647 : Blo 199806 450647 := bstep (se 1 (by rfl) ⟨337985, by rfl⟩ : syracuseStep 450647 = 675971) B675971
theorem B2089091 : Blo 199806 2089091 := bstep (se 1 (by rfl) ⟨1566818, by rfl⟩ : syracuseStep 2089091 = 3133637) B3133637
theorem B680129 : Blo 199806 680129 := bstep (se 2 (by rfl) ⟨255048, by rfl⟩ : syracuseStep 680129 = 510097) B510097
theorem B450827 : Blo 199806 450827 := bstep (se 1 (by rfl) ⟨338120, by rfl⟩ : syracuseStep 450827 = 676241) B676241
theorem B450881 : Blo 199806 450881 := bstep (se 2 (by rfl) ⟨169080, by rfl⟩ : syracuseStep 450881 = 338161) B338161
theorem B647489 : Blo 199806 647489 := bstep (se 2 (by rfl) ⟨242808, by rfl⟩ : syracuseStep 647489 = 485617) B485617
theorem B1466885 : Blo 199806 1466885 := bstep (se 4 (by rfl) ⟨137520, by rfl⟩ : syracuseStep 1466885 = 275041) B275041
theorem B451097 : Blo 199806 451097 := bstep (se 2 (by rfl) ⟨169161, by rfl⟩ : syracuseStep 451097 = 338323) B338323
theorem B451187 : Blo 199806 451187 := bstep (se 1 (by rfl) ⟨338390, by rfl⟩ : syracuseStep 451187 = 676781) B676781
theorem B254603 : Blo 199806 254603 := bstep (se 1 (by rfl) ⟨190952, by rfl⟩ : syracuseStep 254603 = 381905) B381905
theorem B451223 : Blo 199806 451223 := bstep (se 1 (by rfl) ⟨338417, by rfl⟩ : syracuseStep 451223 = 676835) B676835
theorem B975539 : Blo 199806 975539 := bstep (se 1 (by rfl) ⟨731654, by rfl⟩ : syracuseStep 975539 = 1463309) B1463309
theorem B680669 : Blo 199806 680669 := bstep (se 3 (by rfl) ⟨127625, by rfl⟩ : syracuseStep 680669 = 255251) B255251
theorem B385793 : Blo 199806 385793 := bstep (se 2 (by rfl) ⟨144672, by rfl⟩ : syracuseStep 385793 = 289345) B289345
theorem B484147 : Blo 199806 484147 := bstep (se 1 (by rfl) ⟨363110, by rfl⟩ : syracuseStep 484147 = 726221) B726221
theorem B1303361 : Blo 199806 1303361 := bstep (se 2 (by rfl) ⟨488760, by rfl⟩ : syracuseStep 1303361 = 977521) B977521
theorem B451403 : Blo 199806 451403 := bstep (se 1 (by rfl) ⟨338552, by rfl⟩ : syracuseStep 451403 = 677105) B677105
theorem B451457 : Blo 199806 451457 := bstep (se 2 (by rfl) ⟨169296, by rfl⟩ : syracuseStep 451457 = 338593) B338593
theorem B385931 : Blo 199806 385931 := bstep (se 1 (by rfl) ⟨289448, by rfl⟩ : syracuseStep 385931 = 578897) B578897
theorem B2319283 : Blo 199806 2319283 := bstep (se 1 (by rfl) ⟨1739462, by rfl⟩ : syracuseStep 2319283 = 3478925) B3478925
theorem B386059 : Blo 199806 386059 := bstep (se 1 (by rfl) ⟨289544, by rfl⟩ : syracuseStep 386059 = 579089) B579089
theorem B549953 : Blo 199806 549953 := bstep (se 2 (by rfl) ⟨206232, by rfl⟩ : syracuseStep 549953 = 412465) B412465
theorem B451673 : Blo 199806 451673 := bstep (se 2 (by rfl) ⟨169377, by rfl⟩ : syracuseStep 451673 = 338755) B338755
theorem B451763 : Blo 199806 451763 := bstep (se 1 (by rfl) ⟨338822, by rfl⟩ : syracuseStep 451763 = 677645) B677645
theorem B451799 : Blo 199806 451799 := bstep (se 1 (by rfl) ⟨338849, by rfl⟩ : syracuseStep 451799 = 677699) B677699
theorem B255307 : Blo 199806 255307 := bstep (se 1 (by rfl) ⟨191480, by rfl⟩ : syracuseStep 255307 = 382961) B382961
theorem B451979 : Blo 199806 451979 := bstep (se 1 (by rfl) ⟨338984, by rfl⟩ : syracuseStep 451979 = 677969) B677969
theorem B452033 : Blo 199806 452033 := bstep (se 2 (by rfl) ⟨169512, by rfl⟩ : syracuseStep 452033 = 339025) B339025
theorem B484811 : Blo 199806 484811 := bstep (se 1 (by rfl) ⟨363608, by rfl⟩ : syracuseStep 484811 = 727217) B727217
theorem B386507 : Blo 199806 386507 := bstep (se 1 (by rfl) ⟨289880, by rfl⟩ : syracuseStep 386507 = 579761) B579761
theorem B255575 : Blo 199806 255575 := bstep (se 1 (by rfl) ⟨191681, by rfl⟩ : syracuseStep 255575 = 383363) B383363
theorem B1140317 : Blo 199806 1140317 := bstep (se 3 (by rfl) ⟨213809, by rfl⟩ : syracuseStep 1140317 = 427619) B427619
theorem B386689 : Blo 199806 386689 := bstep (se 2 (by rfl) ⟨145008, by rfl⟩ : syracuseStep 386689 = 290017) B290017
theorem B452249 : Blo 199806 452249 := bstep (se 2 (by rfl) ⟨169593, by rfl⟩ : syracuseStep 452249 = 339187) B339187
theorem B812717 : Blo 199806 812717 := bstep (se 3 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 812717 = 304769) B304769
theorem B452339 : Blo 199806 452339 := bstep (se 1 (by rfl) ⟨339254, by rfl⟩ : syracuseStep 452339 = 678509) B678509
theorem B386839 : Blo 199806 386839 := bstep (se 1 (by rfl) ⟨290129, by rfl⟩ : syracuseStep 386839 = 580259) B580259
theorem B452375 : Blo 199806 452375 := bstep (se 1 (by rfl) ⟨339281, by rfl⟩ : syracuseStep 452375 = 678563) B678563
theorem B681803 : Blo 199806 681803 := bstep (se 1 (by rfl) ⟨511352, by rfl⟩ : syracuseStep 681803 = 1022705) B1022705
theorem B452555 : Blo 199806 452555 := bstep (se 1 (by rfl) ⟨339416, by rfl⟩ : syracuseStep 452555 = 678833) B678833
theorem B452609 : Blo 199806 452609 := bstep (se 2 (by rfl) ⟨169728, by rfl⟩ : syracuseStep 452609 = 339457) B339457
theorem B911405 : Blo 199806 911405 := bstep (se 3 (by rfl) ⟨170888, by rfl⟩ : syracuseStep 911405 = 341777) B341777
theorem B682073 : Blo 199806 682073 := bstep (se 2 (by rfl) ⟨255777, by rfl⟩ : syracuseStep 682073 = 511555) B511555
theorem B452825 : Blo 199806 452825 := bstep (se 2 (by rfl) ⟨169809, by rfl⟩ : syracuseStep 452825 = 339619) B339619
theorem B256279 : Blo 199806 256279 := bstep (se 1 (by rfl) ⟨192209, by rfl⟩ : syracuseStep 256279 = 384419) B384419
theorem B452915 : Blo 199806 452915 := bstep (se 1 (by rfl) ⟨339686, by rfl⟩ : syracuseStep 452915 = 679373) B679373
theorem B1141067 : Blo 199806 1141067 := bstep (se 1 (by rfl) ⟨855800, by rfl⟩ : syracuseStep 1141067 = 1711601) B1711601
theorem B452951 : Blo 199806 452951 := bstep (se 1 (by rfl) ⟨339713, by rfl⟩ : syracuseStep 452951 = 679427) B679427
theorem B1534301 : Blo 199806 1534301 := bstep (se 3 (by rfl) ⟨287681, by rfl⟩ : syracuseStep 1534301 = 575363) B575363
theorem B453131 : Blo 199806 453131 := bstep (se 1 (by rfl) ⟨339848, by rfl⟩ : syracuseStep 453131 = 679697) B679697
theorem B453185 : Blo 199806 453185 := bstep (se 2 (by rfl) ⟨169944, by rfl⟩ : syracuseStep 453185 = 339889) B339889
theorem B649949 : Blo 199806 649949 := bstep (se 3 (by rfl) ⟨121865, by rfl⟩ : syracuseStep 649949 = 243731) B243731
theorem B682775 : Blo 199806 682775 := bstep (se 1 (by rfl) ⟨512081, by rfl⟩ : syracuseStep 682775 = 1024163) B1024163
theorem B453401 : Blo 199806 453401 := bstep (se 2 (by rfl) ⟨170025, by rfl⟩ : syracuseStep 453401 = 340051) B340051
theorem B453491 : Blo 199806 453491 := bstep (se 1 (by rfl) ⟨340118, by rfl⟩ : syracuseStep 453491 = 680237) B680237
theorem B453527 : Blo 199806 453527 := bstep (se 1 (by rfl) ⟨340145, by rfl⟩ : syracuseStep 453527 = 680291) B680291
theorem B453707 : Blo 199806 453707 := bstep (se 1 (by rfl) ⟨340280, by rfl⟩ : syracuseStep 453707 = 680561) B680561
theorem B453761 : Blo 199806 453761 := bstep (se 2 (by rfl) ⟨170160, by rfl⟩ : syracuseStep 453761 = 340321) B340321
theorem B814225 : Blo 199806 814225 := bstep (se 2 (by rfl) ⟨305334, by rfl⟩ : syracuseStep 814225 = 610669) B610669
theorem B5860613 : Blo 199806 5860613 := bstep (se 4 (by rfl) ⟨549432, by rfl⟩ : syracuseStep 5860613 = 1098865) B1098865
theorem B683315 : Blo 199806 683315 := bstep (se 1 (by rfl) ⟨512486, by rfl⟩ : syracuseStep 683315 = 1024973) B1024973
theorem B453977 : Blo 199806 453977 := bstep (se 2 (by rfl) ⟨170241, by rfl⟩ : syracuseStep 453977 = 340483) B340483
theorem B290137 : Blo 199806 290137 := bstep (se 2 (by rfl) ⟨108801, by rfl⟩ : syracuseStep 290137 = 217603) B217603
theorem B1371485 : Blo 199806 1371485 := bstep (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) B514307
theorem B454067 : Blo 199806 454067 := bstep (se 1 (by rfl) ⟨340550, by rfl⟩ : syracuseStep 454067 = 681101) B681101
theorem B454103 : Blo 199806 454103 := bstep (se 1 (by rfl) ⟨340577, by rfl⟩ : syracuseStep 454103 = 681155) B681155
theorem B683585 : Blo 199806 683585 := bstep (se 2 (by rfl) ⟨256344, by rfl⟩ : syracuseStep 683585 = 512689) B512689
theorem B487001 : Blo 199806 487001 := bstep (se 2 (by rfl) ⟨182625, by rfl⟩ : syracuseStep 487001 = 365251) B365251
theorem B224887 : Blo 199806 224887 := bstep (se 1 (by rfl) ⟨168665, by rfl⟩ : syracuseStep 224887 = 337331) B337331
theorem B454283 : Blo 199806 454283 := bstep (se 1 (by rfl) ⟨340712, by rfl⟩ : syracuseStep 454283 = 681425) B681425
theorem B454337 : Blo 199806 454337 := bstep (se 2 (by rfl) ⟨170376, by rfl⟩ : syracuseStep 454337 = 340753) B340753
theorem B225067 : Blo 199806 225067 := bstep (se 1 (by rfl) ⟨168800, by rfl⟩ : syracuseStep 225067 = 337601) B337601
theorem B225175 : Blo 199806 225175 := bstep (se 1 (by rfl) ⟨168881, by rfl⟩ : syracuseStep 225175 = 337763) B337763
theorem B454553 : Blo 199806 454553 := bstep (se 2 (by rfl) ⟨170457, by rfl⟩ : syracuseStep 454553 = 340915) B340915
theorem B1142707 : Blo 199806 1142707 := bstep (se 1 (by rfl) ⟨857030, by rfl⟩ : syracuseStep 1142707 = 1714061) B1714061
theorem B880577 : Blo 199806 880577 := bstep (se 2 (by rfl) ⟨330216, by rfl⟩ : syracuseStep 880577 = 660433) B660433
theorem B520139 : Blo 199806 520139 := bstep (se 1 (by rfl) ⟨390104, by rfl⟩ : syracuseStep 520139 = 780209) B780209
theorem B454643 : Blo 199806 454643 := bstep (se 1 (by rfl) ⟨340982, by rfl⟩ : syracuseStep 454643 = 681965) B681965
theorem B454679 : Blo 199806 454679 := bstep (se 1 (by rfl) ⟨341009, by rfl⟩ : syracuseStep 454679 = 682019) B682019
theorem B225355 : Blo 199806 225355 := bstep (se 1 (by rfl) ⟨169016, by rfl⟩ : syracuseStep 225355 = 338033) B338033
theorem B684125 : Blo 199806 684125 := bstep (se 3 (by rfl) ⟨128273, by rfl⟩ : syracuseStep 684125 = 256547) B256547
theorem B1339523 : Blo 199806 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B225463 : Blo 199806 225463 := bstep (se 1 (by rfl) ⟨169097, by rfl⟩ : syracuseStep 225463 = 338195) B338195
theorem B454859 : Blo 199806 454859 := bstep (se 1 (by rfl) ⟨341144, by rfl⟩ : syracuseStep 454859 = 682289) B682289
theorem B454913 : Blo 199806 454913 := bstep (se 2 (by rfl) ⟨170592, by rfl⟩ : syracuseStep 454913 = 341185) B341185
theorem B1012013 : Blo 199806 1012013 := bstep (se 3 (by rfl) ⟨189752, by rfl⟩ : syracuseStep 1012013 = 379505) B379505
theorem B913739 : Blo 199806 913739 := bstep (se 1 (by rfl) ⟨685304, by rfl⟩ : syracuseStep 913739 = 1370609) B1370609
theorem B225643 : Blo 199806 225643 := bstep (se 1 (by rfl) ⟨169232, by rfl⟩ : syracuseStep 225643 = 338465) B338465
theorem B225751 : Blo 199806 225751 := bstep (se 1 (by rfl) ⟨169313, by rfl⟩ : syracuseStep 225751 = 338627) B338627
theorem B455129 : Blo 199806 455129 := bstep (se 2 (by rfl) ⟨170673, by rfl⟩ : syracuseStep 455129 = 341347) B341347
theorem B1045037 : Blo 199806 1045037 := bstep (se 3 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 1045037 = 391889) B391889
theorem B455219 : Blo 199806 455219 := bstep (se 1 (by rfl) ⟨341414, by rfl⟩ : syracuseStep 455219 = 682829) B682829
theorem B455255 : Blo 199806 455255 := bstep (se 1 (by rfl) ⟨341441, by rfl⟩ : syracuseStep 455255 = 682883) B682883
theorem B225931 : Blo 199806 225931 := bstep (se 1 (by rfl) ⟨169448, by rfl⟩ : syracuseStep 225931 = 338897) B338897
theorem B291481 : Blo 199806 291481 := bstep (se 2 (by rfl) ⟨109305, by rfl⟩ : syracuseStep 291481 = 218611) B218611
theorem B226039 : Blo 199806 226039 := bstep (se 1 (by rfl) ⟨169529, by rfl⟩ : syracuseStep 226039 = 339059) B339059
theorem B455435 : Blo 199806 455435 := bstep (se 1 (by rfl) ⟨341576, by rfl⟩ : syracuseStep 455435 = 683153) B683153
theorem B455489 : Blo 199806 455489 := bstep (se 2 (by rfl) ⟨170808, by rfl⟩ : syracuseStep 455489 = 341617) B341617
theorem B226219 : Blo 199806 226219 := bstep (se 1 (by rfl) ⟨169664, by rfl⟩ : syracuseStep 226219 = 339329) B339329
theorem B226327 : Blo 199806 226327 := bstep (se 1 (by rfl) ⟨169745, by rfl⟩ : syracuseStep 226327 = 339491) B339491
theorem B455705 : Blo 199806 455705 := bstep (se 2 (by rfl) ⟨170889, by rfl⟩ : syracuseStep 455705 = 341779) B341779
theorem B455795 : Blo 199806 455795 := bstep (se 1 (by rfl) ⟨341846, by rfl⟩ : syracuseStep 455795 = 683693) B683693
theorem B455831 : Blo 199806 455831 := bstep (se 1 (by rfl) ⟨341873, by rfl⟩ : syracuseStep 455831 = 683747) B683747
theorem B226507 : Blo 199806 226507 := bstep (se 1 (by rfl) ⟨169880, by rfl⟩ : syracuseStep 226507 = 339761) B339761
theorem B685259 : Blo 199806 685259 := bstep (se 1 (by rfl) ⟨513944, by rfl⟩ : syracuseStep 685259 = 1027889) B1027889
theorem B455987 : Blo 199806 455987 := bstep (se 1 (by rfl) ⟨341990, by rfl⟩ : syracuseStep 455987 = 683981) B683981
theorem B226615 : Blo 199806 226615 := bstep (se 1 (by rfl) ⟨169961, by rfl⟩ : syracuseStep 226615 = 339923) B339923
theorem B456011 : Blo 199806 456011 := bstep (se 1 (by rfl) ⟨342008, by rfl⟩ : syracuseStep 456011 = 684017) B684017
theorem B1144165 : Blo 199806 1144165 := bstep (se 4 (by rfl) ⟨107265, by rfl⟩ : syracuseStep 1144165 = 214531) B214531
theorem B456065 : Blo 199806 456065 := bstep (se 2 (by rfl) ⟨171024, by rfl⟩ : syracuseStep 456065 = 342049) B342049
theorem B2880947 : Blo 199806 2880947 := bstep (se 1 (by rfl) ⟨2160710, by rfl⟩ : syracuseStep 2880947 = 4321421) B4321421
theorem B685529 : Blo 199806 685529 := bstep (se 2 (by rfl) ⟨257073, by rfl⟩ : syracuseStep 685529 = 514147) B514147
theorem B226795 : Blo 199806 226795 := bstep (se 1 (by rfl) ⟨170096, by rfl⟩ : syracuseStep 226795 = 340193) B340193
theorem B226903 : Blo 199806 226903 := bstep (se 1 (by rfl) ⟨170177, by rfl⟩ : syracuseStep 226903 = 340355) B340355
theorem B456281 : Blo 199806 456281 := bstep (se 2 (by rfl) ⟨171105, by rfl⟩ : syracuseStep 456281 = 342211) B342211
theorem B456371 : Blo 199806 456371 := bstep (se 1 (by rfl) ⟨342278, by rfl⟩ : syracuseStep 456371 = 684557) B684557
theorem B456407 : Blo 199806 456407 := bstep (se 1 (by rfl) ⟨342305, by rfl⟩ : syracuseStep 456407 = 684611) B684611
theorem B227083 : Blo 199806 227083 := bstep (se 1 (by rfl) ⟨170312, by rfl⟩ : syracuseStep 227083 = 340625) B340625
theorem B2094913 : Blo 199806 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B227191 : Blo 199806 227191 := bstep (se 1 (by rfl) ⟨170393, by rfl⟩ : syracuseStep 227191 = 340787) B340787
theorem B456587 : Blo 199806 456587 := bstep (se 1 (by rfl) ⟨342440, by rfl⟩ : syracuseStep 456587 = 684881) B684881
theorem B456641 : Blo 199806 456641 := bstep (se 2 (by rfl) ⟨171240, by rfl⟩ : syracuseStep 456641 = 342481) B342481
theorem B227371 : Blo 199806 227371 := bstep (se 1 (by rfl) ⟨170528, by rfl⟩ : syracuseStep 227371 = 341057) B341057
theorem B325721 : Blo 199806 325721 := bstep (se 2 (by rfl) ⟨122145, by rfl⟩ : syracuseStep 325721 = 244291) B244291
theorem B227479 : Blo 199806 227479 := bstep (se 1 (by rfl) ⟨170609, by rfl⟩ : syracuseStep 227479 = 341219) B341219
theorem B686231 : Blo 199806 686231 := bstep (se 1 (by rfl) ⟨514673, by rfl⟩ : syracuseStep 686231 = 1029347) B1029347
theorem B456857 : Blo 199806 456857 := bstep (se 2 (by rfl) ⟨171321, by rfl⟩ : syracuseStep 456857 = 342643) B342643
theorem B456947 : Blo 199806 456947 := bstep (se 1 (by rfl) ⟨342710, by rfl⟩ : syracuseStep 456947 = 685421) B685421
theorem B1734929 : Blo 199806 1734929 := bstep (se 2 (by rfl) ⟨650598, by rfl⟩ : syracuseStep 1734929 = 1301197) B1301197
theorem B456983 : Blo 199806 456983 := bstep (se 1 (by rfl) ⟨342737, by rfl⟩ : syracuseStep 456983 = 685475) B685475
theorem B391475 : Blo 199806 391475 := bstep (se 1 (by rfl) ⟨293606, by rfl⟩ : syracuseStep 391475 = 587213) B587213
theorem B227659 : Blo 199806 227659 := bstep (se 1 (by rfl) ⟨170744, by rfl⟩ : syracuseStep 227659 = 341489) B341489
theorem B227767 : Blo 199806 227767 := bstep (se 1 (by rfl) ⟨170825, by rfl⟩ : syracuseStep 227767 = 341651) B341651
theorem B457163 : Blo 199806 457163 := bstep (se 1 (by rfl) ⟨342872, by rfl⟩ : syracuseStep 457163 = 685745) B685745
theorem B457217 : Blo 199806 457217 := bstep (se 2 (by rfl) ⟨171456, by rfl⟩ : syracuseStep 457217 = 342913) B342913
theorem B227947 : Blo 199806 227947 := bstep (se 1 (by rfl) ⟨170960, by rfl⟩ : syracuseStep 227947 = 341921) B341921
theorem B686771 : Blo 199806 686771 := bstep (se 1 (by rfl) ⟨515078, by rfl⟩ : syracuseStep 686771 = 1030157) B1030157
theorem B228055 : Blo 199806 228055 := bstep (se 1 (by rfl) ⟨171041, by rfl⟩ : syracuseStep 228055 = 342083) B342083
theorem B326359 : Blo 199806 326359 := bstep (se 1 (by rfl) ⟨244769, by rfl⟩ : syracuseStep 326359 = 489539) B489539
theorem B457433 : Blo 199806 457433 := bstep (se 2 (by rfl) ⟨171537, by rfl⟩ : syracuseStep 457433 = 343075) B343075
theorem B457523 : Blo 199806 457523 := bstep (se 1 (by rfl) ⟨343142, by rfl⟩ : syracuseStep 457523 = 686285) B686285
theorem B457559 : Blo 199806 457559 := bstep (se 1 (by rfl) ⟨343169, by rfl⟩ : syracuseStep 457559 = 686339) B686339
theorem B228235 : Blo 199806 228235 := bstep (se 1 (by rfl) ⟨171176, by rfl⟩ : syracuseStep 228235 = 342353) B342353
theorem B687041 : Blo 199806 687041 := bstep (se 2 (by rfl) ⟨257640, by rfl⟩ : syracuseStep 687041 = 515281) B515281
theorem B228343 : Blo 199806 228343 := bstep (se 1 (by rfl) ⟨171257, by rfl⟩ : syracuseStep 228343 = 342515) B342515
theorem B457739 : Blo 199806 457739 := bstep (se 1 (by rfl) ⟨343304, by rfl⟩ : syracuseStep 457739 = 686609) B686609
theorem B261131 : Blo 199806 261131 := bstep (se 1 (by rfl) ⟨195848, by rfl⟩ : syracuseStep 261131 = 391697) B391697
theorem B1080337 : Blo 199806 1080337 := bstep (se 2 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 1080337 = 810253) B810253
theorem B457793 : Blo 199806 457793 := bstep (se 2 (by rfl) ⟨171672, by rfl⟩ : syracuseStep 457793 = 343345) B343345
theorem B228523 : Blo 199806 228523 := bstep (se 1 (by rfl) ⟨171392, by rfl⟩ : syracuseStep 228523 = 342785) B342785
theorem B228619 : Blo 199806 228619 := bstep (se 1 (by rfl) ⟨171464, by rfl⟩ : syracuseStep 228619 = 342929) B342929
theorem B228631 : Blo 199806 228631 := bstep (se 1 (by rfl) ⟨171473, by rfl⟩ : syracuseStep 228631 = 342947) B342947
theorem B458009 : Blo 199806 458009 := bstep (se 2 (by rfl) ⟨171753, by rfl⟩ : syracuseStep 458009 = 343507) B343507
theorem B458099 : Blo 199806 458099 := bstep (se 1 (by rfl) ⟨343574, by rfl⟩ : syracuseStep 458099 = 687149) B687149
theorem B458135 : Blo 199806 458135 := bstep (se 1 (by rfl) ⟨343601, by rfl⟩ : syracuseStep 458135 = 687203) B687203
theorem B228811 : Blo 199806 228811 := bstep (se 1 (by rfl) ⟨171608, by rfl⟩ : syracuseStep 228811 = 343217) B343217
theorem B687581 : Blo 199806 687581 := bstep (se 3 (by rfl) ⟨128921, by rfl⟩ : syracuseStep 687581 = 257843) B257843
theorem B228919 : Blo 199806 228919 := bstep (se 1 (by rfl) ⟨171689, by rfl⟩ : syracuseStep 228919 = 343379) B343379
theorem B458315 : Blo 199806 458315 := bstep (se 1 (by rfl) ⟨343736, by rfl⟩ : syracuseStep 458315 = 687473) B687473
theorem B458369 : Blo 199806 458369 := bstep (se 2 (by rfl) ⟨171888, by rfl⟩ : syracuseStep 458369 = 343777) B343777
theorem B229099 : Blo 199806 229099 := bstep (se 1 (by rfl) ⟨171824, by rfl⟩ : syracuseStep 229099 = 343649) B343649
theorem B229111 : Blo 199806 229111 := bstep (se 1 (by rfl) ⟨171833, by rfl⟩ : syracuseStep 229111 = 343667) B343667
theorem B720685 : Blo 199806 720685 := bstep (se 3 (by rfl) ⟨135128, by rfl⟩ : syracuseStep 720685 = 270257) B270257
theorem B655169 : Blo 199806 655169 := bstep (se 2 (by rfl) ⟨245688, by rfl⟩ : syracuseStep 655169 = 491377) B491377
theorem B229207 : Blo 199806 229207 := bstep (se 1 (by rfl) ⟨171905, by rfl⟩ : syracuseStep 229207 = 343811) B343811
theorem B294745 : Blo 199806 294745 := bstep (se 2 (by rfl) ⟨110529, by rfl⟩ : syracuseStep 294745 = 221059) B221059
theorem B360407 : Blo 199806 360407 := bstep (se 1 (by rfl) ⟨270305, by rfl⟩ : syracuseStep 360407 = 540611) B540611
theorem B983069 : Blo 199806 983069 := bstep (se 3 (by rfl) ⟨184325, by rfl⟩ : syracuseStep 983069 = 368651) B368651
theorem B1147081 : Blo 199806 1147081 := bstep (se 2 (by rfl) ⟨430155, by rfl⟩ : syracuseStep 1147081 = 860311) B860311
theorem B2195657 : Blo 199806 2195657 := bstep (se 2 (by rfl) ⟨823371, by rfl⟩ : syracuseStep 2195657 = 1646743) B1646743
theorem B1933703 : Blo 199806 1933703 := bstep (se 1 (by rfl) ⟨1450277, by rfl⟩ : syracuseStep 1933703 = 2900555) B2900555
theorem B1016387 : Blo 199806 1016387 := bstep (se 1 (by rfl) ⟨762290, by rfl⟩ : syracuseStep 1016387 = 1524581) B1524581
theorem B3277529 : Blo 199806 3277529 := bstep (se 2 (by rfl) ⟨1229073, by rfl⟩ : syracuseStep 3277529 = 2458147) B2458147
theorem B1639217 : Blo 199806 1639217 := bstep (se 2 (by rfl) ⟨614706, by rfl⟩ : syracuseStep 1639217 = 1229413) B1229413
theorem B1016711 : Blo 199806 1016711 := bstep (se 1 (by rfl) ⟨762533, by rfl⟩ : syracuseStep 1016711 = 1525067) B1525067
theorem B820115 : Blo 199806 820115 := bstep (se 1 (by rfl) ⟨615086, by rfl⟩ : syracuseStep 820115 = 1230173) B1230173
theorem B361417 : Blo 199806 361417 := bstep (se 2 (by rfl) ⟨135531, by rfl⟩ : syracuseStep 361417 = 271063) B271063
theorem B3867709 : Blo 199806 3867709 := bstep (se 3 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 3867709 = 1450391) B1450391
theorem B493067 : Blo 199806 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B7603789 : Blo 199806 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B952343 : Blo 199806 952343 := bstep (se 1 (by rfl) ⟨714257, by rfl⟩ : syracuseStep 952343 = 1428515) B1428515
theorem B657665 : Blo 199806 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B428303 : Blo 199806 428303 := bstep (se 1 (by rfl) ⟨321227, by rfl⟩ : syracuseStep 428303 = 642455) B642455
theorem B723467 : Blo 199806 723467 := bstep (se 1 (by rfl) ⟨542600, by rfl⟩ : syracuseStep 723467 = 1085201) B1085201
theorem B2296349 : Blo 199806 2296349 := bstep (se 3 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 2296349 = 861131) B861131
theorem B1936163 : Blo 199806 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B12389219 : Blo 199806 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B1281035 : Blo 199806 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B199815 : Blo 199806 199815 := bstep (se 1 (by rfl) ⟨149861, by rfl⟩ : syracuseStep 199815 = 299723) B299723
theorem B199823 : Blo 199806 199823 := bstep (se 1 (by rfl) ⟨149867, by rfl⟩ : syracuseStep 199823 = 299735) B299735
theorem B199867 : Blo 199806 199867 := bstep (se 1 (by rfl) ⟨149900, by rfl⟩ : syracuseStep 199867 = 299801) B299801
theorem B199943 : Blo 199806 199943 := bstep (se 1 (by rfl) ⟨149957, by rfl⟩ : syracuseStep 199943 = 299915) B299915
theorem B199951 : Blo 199806 199951 := bstep (se 1 (by rfl) ⟨149963, by rfl⟩ : syracuseStep 199951 = 299927) B299927
theorem B363809 : Blo 199806 363809 := bstep (se 2 (by rfl) ⟨136428, by rfl⟩ : syracuseStep 363809 = 272857) B272857
theorem B199995 : Blo 199806 199995 := bstep (se 1 (by rfl) ⟨149996, by rfl⟩ : syracuseStep 199995 = 299993) B299993
theorem B200071 : Blo 199806 200071 := bstep (se 1 (by rfl) ⟨150053, by rfl⟩ : syracuseStep 200071 = 300107) B300107
theorem B200079 : Blo 199806 200079 := bstep (se 1 (by rfl) ⟨150059, by rfl⟩ : syracuseStep 200079 = 300119) B300119
theorem B200123 : Blo 199806 200123 := bstep (se 1 (by rfl) ⟨150092, by rfl⟩ : syracuseStep 200123 = 300185) B300185
theorem B1215965 : Blo 199806 1215965 := bstep (se 3 (by rfl) ⟨227993, by rfl⟩ : syracuseStep 1215965 = 455987) B455987
theorem B200199 : Blo 199806 200199 := bstep (se 1 (by rfl) ⟨150149, by rfl⟩ : syracuseStep 200199 = 300299) B300299
theorem B200207 : Blo 199806 200207 := bstep (se 1 (by rfl) ⟨150155, by rfl⟩ : syracuseStep 200207 = 300311) B300311
theorem B200251 : Blo 199806 200251 := bstep (se 1 (by rfl) ⟨150188, by rfl⟩ : syracuseStep 200251 = 300377) B300377
theorem B200327 : Blo 199806 200327 := bstep (se 1 (by rfl) ⟨150245, by rfl⟩ : syracuseStep 200327 = 300491) B300491
theorem B200335 : Blo 199806 200335 := bstep (se 1 (by rfl) ⟨150251, by rfl⟩ : syracuseStep 200335 = 300503) B300503
theorem B200379 : Blo 199806 200379 := bstep (se 1 (by rfl) ⟨150284, by rfl⟩ : syracuseStep 200379 = 300569) B300569
theorem B200455 : Blo 199806 200455 := bstep (se 1 (by rfl) ⟨150341, by rfl⟩ : syracuseStep 200455 = 300683) B300683
theorem B200463 : Blo 199806 200463 := bstep (se 1 (by rfl) ⟨150347, by rfl⟩ : syracuseStep 200463 = 300695) B300695
theorem B200507 : Blo 199806 200507 := bstep (se 1 (by rfl) ⟨150380, by rfl⟩ : syracuseStep 200507 = 300761) B300761
theorem B429943 : Blo 199806 429943 := bstep (se 1 (by rfl) ⟨322457, by rfl⟩ : syracuseStep 429943 = 644915) B644915
theorem B200583 : Blo 199806 200583 := bstep (se 1 (by rfl) ⟨150437, by rfl⟩ : syracuseStep 200583 = 300875) B300875
theorem B200591 : Blo 199806 200591 := bstep (se 1 (by rfl) ⟨150443, by rfl⟩ : syracuseStep 200591 = 300887) B300887
theorem B200635 : Blo 199806 200635 := bstep (se 1 (by rfl) ⟨150476, by rfl⟩ : syracuseStep 200635 = 300953) B300953
theorem B200711 : Blo 199806 200711 := bstep (se 1 (by rfl) ⟨150533, by rfl⟩ : syracuseStep 200711 = 301067) B301067
theorem B200719 : Blo 199806 200719 := bstep (se 1 (by rfl) ⟨150539, by rfl⟩ : syracuseStep 200719 = 301079) B301079
theorem B200763 : Blo 199806 200763 := bstep (se 1 (by rfl) ⟨150572, by rfl⟩ : syracuseStep 200763 = 301145) B301145
theorem B692311 : Blo 199806 692311 := bstep (se 1 (by rfl) ⟨519233, by rfl⟩ : syracuseStep 692311 = 1038467) B1038467
theorem B200839 : Blo 199806 200839 := bstep (se 1 (by rfl) ⟨150629, by rfl⟩ : syracuseStep 200839 = 301259) B301259
theorem B200847 : Blo 199806 200847 := bstep (se 1 (by rfl) ⟨150635, by rfl⟩ : syracuseStep 200847 = 301271) B301271
theorem B200891 : Blo 199806 200891 := bstep (se 1 (by rfl) ⟨150668, by rfl⟩ : syracuseStep 200891 = 301337) B301337
theorem B1085633 : Blo 199806 1085633 := bstep (se 2 (by rfl) ⟨407112, by rfl⟩ : syracuseStep 1085633 = 814225) B814225
theorem B200967 : Blo 199806 200967 := bstep (se 1 (by rfl) ⟨150725, by rfl⟩ : syracuseStep 200967 = 301451) B301451
theorem B200975 : Blo 199806 200975 := bstep (se 1 (by rfl) ⟨150731, by rfl⟩ : syracuseStep 200975 = 301463) B301463
theorem B201019 : Blo 199806 201019 := bstep (se 1 (by rfl) ⟨150764, by rfl⟩ : syracuseStep 201019 = 301529) B301529
theorem B1544507 : Blo 199806 1544507 := bstep (se 1 (by rfl) ⟨1158380, by rfl⟩ : syracuseStep 1544507 = 2316761) B2316761
theorem B1020275 : Blo 199806 1020275 := bstep (se 1 (by rfl) ⟨765206, by rfl⟩ : syracuseStep 1020275 = 1530413) B1530413
theorem B201095 : Blo 199806 201095 := bstep (se 1 (by rfl) ⟨150821, by rfl⟩ : syracuseStep 201095 = 301643) B301643
theorem B201103 : Blo 199806 201103 := bstep (se 1 (by rfl) ⟨150827, by rfl⟩ : syracuseStep 201103 = 301655) B301655
theorem B201147 : Blo 199806 201147 := bstep (se 1 (by rfl) ⟨150860, by rfl⟩ : syracuseStep 201147 = 301721) B301721
theorem B201223 : Blo 199806 201223 := bstep (se 1 (by rfl) ⟨150917, by rfl⟩ : syracuseStep 201223 = 301835) B301835
theorem B201231 : Blo 199806 201231 := bstep (se 1 (by rfl) ⟨150923, by rfl⟩ : syracuseStep 201231 = 301847) B301847
theorem B201275 : Blo 199806 201275 := bstep (se 1 (by rfl) ⟨150956, by rfl⟩ : syracuseStep 201275 = 301913) B301913
theorem B201351 : Blo 199806 201351 := bstep (se 1 (by rfl) ⟨151013, by rfl⟩ : syracuseStep 201351 = 302027) B302027
theorem B201359 : Blo 199806 201359 := bstep (se 1 (by rfl) ⟨151019, by rfl⟩ : syracuseStep 201359 = 302039) B302039
theorem B2200243 : Blo 199806 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B201403 : Blo 199806 201403 := bstep (se 1 (by rfl) ⟨151052, by rfl⟩ : syracuseStep 201403 = 302105) B302105
theorem B1381121 : Blo 199806 1381121 := bstep (se 2 (by rfl) ⟨517920, by rfl⟩ : syracuseStep 1381121 = 1035841) B1035841
theorem B299783 : Blo 199806 299783 := bstep (se 1 (by rfl) ⟨224837, by rfl⟩ : syracuseStep 299783 = 449675) B449675
theorem B201479 : Blo 199806 201479 := bstep (se 1 (by rfl) ⟨151109, by rfl⟩ : syracuseStep 201479 = 302219) B302219
theorem B201487 : Blo 199806 201487 := bstep (se 1 (by rfl) ⟨151115, by rfl⟩ : syracuseStep 201487 = 302231) B302231
theorem B299819 : Blo 199806 299819 := bstep (se 1 (by rfl) ⟨224864, by rfl⟩ : syracuseStep 299819 = 449729) B449729
theorem B201531 : Blo 199806 201531 := bstep (se 1 (by rfl) ⟨151148, by rfl⟩ : syracuseStep 201531 = 302297) B302297
theorem B299849 : Blo 199806 299849 := bstep (se 2 (by rfl) ⟨112443, by rfl⟩ : syracuseStep 299849 = 224887) B224887
theorem B1020761 : Blo 199806 1020761 := bstep (se 2 (by rfl) ⟨382785, by rfl⟩ : syracuseStep 1020761 = 765571) B765571
theorem B693107 : Blo 199806 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B201607 : Blo 199806 201607 := bstep (se 1 (by rfl) ⟨151205, by rfl⟩ : syracuseStep 201607 = 302411) B302411
theorem B201615 : Blo 199806 201615 := bstep (se 1 (by rfl) ⟨151211, by rfl⟩ : syracuseStep 201615 = 302423) B302423
theorem B299963 : Blo 199806 299963 := bstep (se 1 (by rfl) ⟨224972, by rfl⟩ : syracuseStep 299963 = 449945) B449945
theorem B201659 : Blo 199806 201659 := bstep (se 1 (by rfl) ⟨151244, by rfl⟩ : syracuseStep 201659 = 302489) B302489
theorem B300023 : Blo 199806 300023 := bstep (se 1 (by rfl) ⟨225017, by rfl⟩ : syracuseStep 300023 = 450035) B450035
theorem B201735 : Blo 199806 201735 := bstep (se 1 (by rfl) ⟨151301, by rfl⟩ : syracuseStep 201735 = 302603) B302603
theorem B300047 : Blo 199806 300047 := bstep (se 1 (by rfl) ⟨225035, by rfl⟩ : syracuseStep 300047 = 450071) B450071
theorem B201743 : Blo 199806 201743 := bstep (se 1 (by rfl) ⟨151307, by rfl⟩ : syracuseStep 201743 = 302615) B302615
theorem B300089 : Blo 199806 300089 := bstep (se 2 (by rfl) ⟨112533, by rfl⟩ : syracuseStep 300089 = 225067) B225067
theorem B201787 : Blo 199806 201787 := bstep (se 1 (by rfl) ⟨151340, by rfl⟩ : syracuseStep 201787 = 302681) B302681
theorem B300167 : Blo 199806 300167 := bstep (se 1 (by rfl) ⟨225125, by rfl⟩ : syracuseStep 300167 = 450251) B450251
theorem B201863 : Blo 199806 201863 := bstep (se 1 (by rfl) ⟨151397, by rfl⟩ : syracuseStep 201863 = 302795) B302795
theorem B201871 : Blo 199806 201871 := bstep (se 1 (by rfl) ⟨151403, by rfl⟩ : syracuseStep 201871 = 302807) B302807
theorem B300203 : Blo 199806 300203 := bstep (se 1 (by rfl) ⟨225152, by rfl⟩ : syracuseStep 300203 = 450305) B450305
theorem B201915 : Blo 199806 201915 := bstep (se 1 (by rfl) ⟨151436, by rfl⟩ : syracuseStep 201915 = 302873) B302873
theorem B300233 : Blo 199806 300233 := bstep (se 2 (by rfl) ⟨112587, by rfl⟩ : syracuseStep 300233 = 225175) B225175
theorem B759041 : Blo 199806 759041 := bstep (se 2 (by rfl) ⟨284640, by rfl⟩ : syracuseStep 759041 = 569281) B569281
theorem B201991 : Blo 199806 201991 := bstep (se 1 (by rfl) ⟨151493, by rfl⟩ : syracuseStep 201991 = 302987) B302987
theorem B201999 : Blo 199806 201999 := bstep (se 1 (by rfl) ⟨151499, by rfl⟩ : syracuseStep 201999 = 302999) B302999
theorem B300347 : Blo 199806 300347 := bstep (se 1 (by rfl) ⟨225260, by rfl⟩ : syracuseStep 300347 = 450521) B450521
theorem B202043 : Blo 199806 202043 := bstep (se 1 (by rfl) ⟨151532, by rfl⟩ : syracuseStep 202043 = 303065) B303065
theorem B300407 : Blo 199806 300407 := bstep (se 1 (by rfl) ⟨225305, by rfl⟩ : syracuseStep 300407 = 450611) B450611
theorem B202119 : Blo 199806 202119 := bstep (se 1 (by rfl) ⟨151589, by rfl⟩ : syracuseStep 202119 = 303179) B303179
theorem B300431 : Blo 199806 300431 := bstep (se 1 (by rfl) ⟨225323, by rfl⟩ : syracuseStep 300431 = 450647) B450647
theorem B202127 : Blo 199806 202127 := bstep (se 1 (by rfl) ⟨151595, by rfl⟩ : syracuseStep 202127 = 303191) B303191
theorem B300473 : Blo 199806 300473 := bstep (se 2 (by rfl) ⟨112677, by rfl⟩ : syracuseStep 300473 = 225355) B225355
theorem B202171 : Blo 199806 202171 := bstep (se 1 (by rfl) ⟨151628, by rfl⟩ : syracuseStep 202171 = 303257) B303257
theorem B300551 : Blo 199806 300551 := bstep (se 1 (by rfl) ⟨225413, by rfl⟩ : syracuseStep 300551 = 450827) B450827
theorem B202247 : Blo 199806 202247 := bstep (se 1 (by rfl) ⟨151685, by rfl⟩ : syracuseStep 202247 = 303371) B303371
theorem B202255 : Blo 199806 202255 := bstep (se 1 (by rfl) ⟨151691, by rfl⟩ : syracuseStep 202255 = 303383) B303383
theorem B300587 : Blo 199806 300587 := bstep (se 1 (by rfl) ⟨225440, by rfl⟩ : syracuseStep 300587 = 450881) B450881
theorem B431659 : Blo 199806 431659 := bstep (se 1 (by rfl) ⟨323744, by rfl⟩ : syracuseStep 431659 = 647489) B647489
theorem B202299 : Blo 199806 202299 := bstep (se 1 (by rfl) ⟨151724, by rfl⟩ : syracuseStep 202299 = 303449) B303449
theorem B300617 : Blo 199806 300617 := bstep (se 2 (by rfl) ⟨112731, by rfl⟩ : syracuseStep 300617 = 225463) B225463
theorem B1709687 : Blo 199806 1709687 := bstep (se 1 (by rfl) ⟨1282265, by rfl⟩ : syracuseStep 1709687 = 2564531) B2564531
theorem B202375 : Blo 199806 202375 := bstep (se 1 (by rfl) ⟨151781, by rfl⟩ : syracuseStep 202375 = 303563) B303563
theorem B202383 : Blo 199806 202383 := bstep (se 1 (by rfl) ⟨151787, by rfl⟩ : syracuseStep 202383 = 303575) B303575
theorem B300731 : Blo 199806 300731 := bstep (se 1 (by rfl) ⟨225548, by rfl⟩ : syracuseStep 300731 = 451097) B451097
theorem B202427 : Blo 199806 202427 := bstep (se 1 (by rfl) ⟨151820, by rfl⟩ : syracuseStep 202427 = 303641) B303641
theorem B300791 : Blo 199806 300791 := bstep (se 1 (by rfl) ⟨225593, by rfl⟩ : syracuseStep 300791 = 451187) B451187
theorem B202503 : Blo 199806 202503 := bstep (se 1 (by rfl) ⟨151877, by rfl⟩ : syracuseStep 202503 = 303755) B303755
theorem B300815 : Blo 199806 300815 := bstep (se 1 (by rfl) ⟨225611, by rfl⟩ : syracuseStep 300815 = 451223) B451223
theorem B202511 : Blo 199806 202511 := bstep (se 1 (by rfl) ⟨151883, by rfl⟩ : syracuseStep 202511 = 303767) B303767
theorem B300857 : Blo 199806 300857 := bstep (se 2 (by rfl) ⟨112821, by rfl⟩ : syracuseStep 300857 = 225643) B225643
theorem B202555 : Blo 199806 202555 := bstep (se 1 (by rfl) ⟨151916, by rfl⟩ : syracuseStep 202555 = 303833) B303833
theorem B2561867 : Blo 199806 2561867 := bstep (se 1 (by rfl) ⟨1921400, by rfl⟩ : syracuseStep 2561867 = 3842801) B3842801
theorem B300935 : Blo 199806 300935 := bstep (se 1 (by rfl) ⟨225701, by rfl⟩ : syracuseStep 300935 = 451403) B451403
theorem B202631 : Blo 199806 202631 := bstep (se 1 (by rfl) ⟨151973, by rfl⟩ : syracuseStep 202631 = 303947) B303947
theorem B202639 : Blo 199806 202639 := bstep (se 1 (by rfl) ⟨151979, by rfl⟩ : syracuseStep 202639 = 303959) B303959
theorem B1152913 : Blo 199806 1152913 := bstep (se 2 (by rfl) ⟨432342, by rfl⟩ : syracuseStep 1152913 = 864685) B864685
theorem B300971 : Blo 199806 300971 := bstep (se 1 (by rfl) ⟨225728, by rfl⟩ : syracuseStep 300971 = 451457) B451457
theorem B202683 : Blo 199806 202683 := bstep (se 1 (by rfl) ⟨152012, by rfl⟩ : syracuseStep 202683 = 304025) B304025
theorem B301001 : Blo 199806 301001 := bstep (se 2 (by rfl) ⟨112875, by rfl⟩ : syracuseStep 301001 = 225751) B225751
theorem B202759 : Blo 199806 202759 := bstep (se 1 (by rfl) ⟨152069, by rfl⟩ : syracuseStep 202759 = 304139) B304139
theorem B202767 : Blo 199806 202767 := bstep (se 1 (by rfl) ⟨152075, by rfl⟩ : syracuseStep 202767 = 304151) B304151
theorem B366635 : Blo 199806 366635 := bstep (se 1 (by rfl) ⟨274976, by rfl⟩ : syracuseStep 366635 = 549953) B549953
theorem B301115 : Blo 199806 301115 := bstep (se 1 (by rfl) ⟨225836, by rfl⟩ : syracuseStep 301115 = 451673) B451673
theorem B202811 : Blo 199806 202811 := bstep (se 1 (by rfl) ⟨152108, by rfl⟩ : syracuseStep 202811 = 304217) B304217
theorem B301175 : Blo 199806 301175 := bstep (se 1 (by rfl) ⟨225881, by rfl⟩ : syracuseStep 301175 = 451763) B451763
theorem B202887 : Blo 199806 202887 := bstep (se 1 (by rfl) ⟨152165, by rfl⟩ : syracuseStep 202887 = 304331) B304331
theorem B301199 : Blo 199806 301199 := bstep (se 1 (by rfl) ⟨225899, by rfl⟩ : syracuseStep 301199 = 451799) B451799
theorem B202895 : Blo 199806 202895 := bstep (se 1 (by rfl) ⟨152171, by rfl⟩ : syracuseStep 202895 = 304343) B304343
theorem B301241 : Blo 199806 301241 := bstep (se 2 (by rfl) ⟨112965, by rfl⟩ : syracuseStep 301241 = 225931) B225931
theorem B202939 : Blo 199806 202939 := bstep (se 1 (by rfl) ⟨152204, by rfl⟩ : syracuseStep 202939 = 304409) B304409
theorem B301319 : Blo 199806 301319 := bstep (se 1 (by rfl) ⟨225989, by rfl⟩ : syracuseStep 301319 = 451979) B451979
theorem B203015 : Blo 199806 203015 := bstep (se 1 (by rfl) ⟨152261, by rfl⟩ : syracuseStep 203015 = 304523) B304523
theorem B858383 : Blo 199806 858383 := bstep (se 1 (by rfl) ⟨643787, by rfl⟩ : syracuseStep 858383 = 1287575) B1287575
theorem B203023 : Blo 199806 203023 := bstep (se 1 (by rfl) ⟨152267, by rfl⟩ : syracuseStep 203023 = 304535) B304535
theorem B2332961 : Blo 199806 2332961 := bstep (se 2 (by rfl) ⟨874860, by rfl⟩ : syracuseStep 2332961 = 1749721) B1749721
theorem B301355 : Blo 199806 301355 := bstep (se 1 (by rfl) ⟨226016, by rfl⟩ : syracuseStep 301355 = 452033) B452033
theorem B203067 : Blo 199806 203067 := bstep (se 1 (by rfl) ⟨152300, by rfl⟩ : syracuseStep 203067 = 304601) B304601
theorem B301385 : Blo 199806 301385 := bstep (se 2 (by rfl) ⟨113019, by rfl⟩ : syracuseStep 301385 = 226039) B226039
theorem B203143 : Blo 199806 203143 := bstep (se 1 (by rfl) ⟨152357, by rfl⟩ : syracuseStep 203143 = 304715) B304715
theorem B203151 : Blo 199806 203151 := bstep (se 1 (by rfl) ⟨152363, by rfl⟩ : syracuseStep 203151 = 304727) B304727
theorem B760211 : Blo 199806 760211 := bstep (se 1 (by rfl) ⟨570158, by rfl⟩ : syracuseStep 760211 = 1140317) B1140317
theorem B301499 : Blo 199806 301499 := bstep (se 1 (by rfl) ⟨226124, by rfl⟩ : syracuseStep 301499 = 452249) B452249
theorem B203195 : Blo 199806 203195 := bstep (se 1 (by rfl) ⟨152396, by rfl⟩ : syracuseStep 203195 = 304793) B304793
theorem B301559 : Blo 199806 301559 := bstep (se 1 (by rfl) ⟨226169, by rfl⟩ : syracuseStep 301559 = 452339) B452339
theorem B203271 : Blo 199806 203271 := bstep (se 1 (by rfl) ⟨152453, by rfl⟩ : syracuseStep 203271 = 304907) B304907
theorem B301583 : Blo 199806 301583 := bstep (se 1 (by rfl) ⟨226187, by rfl⟩ : syracuseStep 301583 = 452375) B452375
theorem B203279 : Blo 199806 203279 := bstep (se 1 (by rfl) ⟨152459, by rfl⟩ : syracuseStep 203279 = 304919) B304919
theorem B301625 : Blo 199806 301625 := bstep (se 2 (by rfl) ⟨113109, by rfl⟩ : syracuseStep 301625 = 226219) B226219
theorem B203323 : Blo 199806 203323 := bstep (se 1 (by rfl) ⟨152492, by rfl⟩ : syracuseStep 203323 = 304985) B304985
theorem B301703 : Blo 199806 301703 := bstep (se 1 (by rfl) ⟨226277, by rfl⟩ : syracuseStep 301703 = 452555) B452555
theorem B203399 : Blo 199806 203399 := bstep (se 1 (by rfl) ⟨152549, by rfl⟩ : syracuseStep 203399 = 305099) B305099
theorem B203407 : Blo 199806 203407 := bstep (se 1 (by rfl) ⟨152555, by rfl⟩ : syracuseStep 203407 = 305111) B305111
theorem B301739 : Blo 199806 301739 := bstep (se 1 (by rfl) ⟨226304, by rfl⟩ : syracuseStep 301739 = 452609) B452609
theorem B203451 : Blo 199806 203451 := bstep (se 1 (by rfl) ⟨152588, by rfl⟩ : syracuseStep 203451 = 305177) B305177
theorem B301769 : Blo 199806 301769 := bstep (se 2 (by rfl) ⟨113163, by rfl⟩ : syracuseStep 301769 = 226327) B226327
theorem B203527 : Blo 199806 203527 := bstep (se 1 (by rfl) ⟨152645, by rfl⟩ : syracuseStep 203527 = 305291) B305291
theorem B203535 : Blo 199806 203535 := bstep (se 1 (by rfl) ⟨152651, by rfl⟩ : syracuseStep 203535 = 305303) B305303
theorem B2300723 : Blo 199806 2300723 := bstep (se 1 (by rfl) ⟨1725542, by rfl⟩ : syracuseStep 2300723 = 3451085) B3451085
theorem B301883 : Blo 199806 301883 := bstep (se 1 (by rfl) ⟨226412, by rfl⟩ : syracuseStep 301883 = 452825) B452825
theorem B203579 : Blo 199806 203579 := bstep (se 1 (by rfl) ⟨152684, by rfl⟩ : syracuseStep 203579 = 305369) B305369
theorem B301943 : Blo 199806 301943 := bstep (se 1 (by rfl) ⟨226457, by rfl⟩ : syracuseStep 301943 = 452915) B452915
theorem B760711 : Blo 199806 760711 := bstep (se 1 (by rfl) ⟨570533, by rfl⟩ : syracuseStep 760711 = 1141067) B1141067
theorem B203655 : Blo 199806 203655 := bstep (se 1 (by rfl) ⟨152741, by rfl⟩ : syracuseStep 203655 = 305483) B305483
theorem B301967 : Blo 199806 301967 := bstep (se 1 (by rfl) ⟨226475, by rfl⟩ : syracuseStep 301967 = 452951) B452951
theorem B203663 : Blo 199806 203663 := bstep (se 1 (by rfl) ⟨152747, by rfl⟩ : syracuseStep 203663 = 305495) B305495
theorem B1022867 : Blo 199806 1022867 := bstep (se 1 (by rfl) ⟨767150, by rfl⟩ : syracuseStep 1022867 = 1534301) B1534301
theorem B302009 : Blo 199806 302009 := bstep (se 2 (by rfl) ⟨113253, by rfl⟩ : syracuseStep 302009 = 226507) B226507
theorem B203707 : Blo 199806 203707 := bstep (se 1 (by rfl) ⟨152780, by rfl⟩ : syracuseStep 203707 = 305561) B305561
theorem B302087 : Blo 199806 302087 := bstep (se 1 (by rfl) ⟨226565, by rfl⟩ : syracuseStep 302087 = 453131) B453131
theorem B203783 : Blo 199806 203783 := bstep (se 1 (by rfl) ⟨152837, by rfl⟩ : syracuseStep 203783 = 305675) B305675
theorem B203791 : Blo 199806 203791 := bstep (se 1 (by rfl) ⟨152843, by rfl⟩ : syracuseStep 203791 = 305687) B305687
theorem B302123 : Blo 199806 302123 := bstep (se 1 (by rfl) ⟨226592, by rfl⟩ : syracuseStep 302123 = 453185) B453185
theorem B302153 : Blo 199806 302153 := bstep (se 2 (by rfl) ⟨113307, by rfl⟩ : syracuseStep 302153 = 226615) B226615
theorem B302267 : Blo 199806 302267 := bstep (se 1 (by rfl) ⟨226700, by rfl⟩ : syracuseStep 302267 = 453401) B453401
theorem B302327 : Blo 199806 302327 := bstep (se 1 (by rfl) ⟨226745, by rfl⟩ : syracuseStep 302327 = 453491) B453491
theorem B302351 : Blo 199806 302351 := bstep (se 1 (by rfl) ⟨226763, by rfl⟩ : syracuseStep 302351 = 453527) B453527
theorem B302393 : Blo 199806 302393 := bstep (se 2 (by rfl) ⟨113397, by rfl⟩ : syracuseStep 302393 = 226795) B226795
theorem B302471 : Blo 199806 302471 := bstep (se 1 (by rfl) ⟨226853, by rfl⟩ : syracuseStep 302471 = 453707) B453707
theorem B302507 : Blo 199806 302507 := bstep (se 1 (by rfl) ⟨226880, by rfl⟩ : syracuseStep 302507 = 453761) B453761
theorem B302537 : Blo 199806 302537 := bstep (se 2 (by rfl) ⟨113451, by rfl⟩ : syracuseStep 302537 = 226903) B226903
theorem B4660739 : Blo 199806 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B3907075 : Blo 199806 3907075 := bstep (se 1 (by rfl) ⟨2930306, by rfl⟩ : syracuseStep 3907075 = 5860613) B5860613
theorem B302651 : Blo 199806 302651 := bstep (se 1 (by rfl) ⟨226988, by rfl⟩ : syracuseStep 302651 = 453977) B453977
theorem B302711 : Blo 199806 302711 := bstep (se 1 (by rfl) ⟨227033, by rfl⟩ : syracuseStep 302711 = 454067) B454067
theorem B302735 : Blo 199806 302735 := bstep (se 1 (by rfl) ⟨227051, by rfl⟩ : syracuseStep 302735 = 454103) B454103
theorem B302777 : Blo 199806 302777 := bstep (se 2 (by rfl) ⟨113541, by rfl⟩ : syracuseStep 302777 = 227083) B227083
theorem B1449701 : Blo 199806 1449701 := bstep (se 4 (by rfl) ⟨135909, by rfl⟩ : syracuseStep 1449701 = 271819) B271819
theorem B2924261 : Blo 199806 2924261 := bstep (se 4 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 2924261 = 548299) B548299
theorem B2793217 : Blo 199806 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B302855 : Blo 199806 302855 := bstep (se 1 (by rfl) ⟨227141, by rfl⟩ : syracuseStep 302855 = 454283) B454283
theorem B302891 : Blo 199806 302891 := bstep (se 1 (by rfl) ⟨227168, by rfl⟩ : syracuseStep 302891 = 454337) B454337
theorem B302921 : Blo 199806 302921 := bstep (se 2 (by rfl) ⟨113595, by rfl⟩ : syracuseStep 302921 = 227191) B227191
theorem B303035 : Blo 199806 303035 := bstep (se 1 (by rfl) ⟨227276, by rfl⟩ : syracuseStep 303035 = 454553) B454553
theorem B303095 : Blo 199806 303095 := bstep (se 1 (by rfl) ⟨227321, by rfl⟩ : syracuseStep 303095 = 454643) B454643
theorem B1941509 : Blo 199806 1941509 := bstep (se 4 (by rfl) ⟨182016, by rfl⟩ : syracuseStep 1941509 = 364033) B364033
theorem B303119 : Blo 199806 303119 := bstep (se 1 (by rfl) ⟨227339, by rfl⟩ : syracuseStep 303119 = 454679) B454679
theorem B696349 : Blo 199806 696349 := bstep (se 3 (by rfl) ⟨130565, by rfl⟩ : syracuseStep 696349 = 261131) B261131
theorem B303161 : Blo 199806 303161 := bstep (se 2 (by rfl) ⟨113685, by rfl⟩ : syracuseStep 303161 = 227371) B227371
theorem B893015 : Blo 199806 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B303239 : Blo 199806 303239 := bstep (se 1 (by rfl) ⟨227429, by rfl⟩ : syracuseStep 303239 = 454859) B454859
theorem B303275 : Blo 199806 303275 := bstep (se 1 (by rfl) ⟨227456, by rfl⟩ : syracuseStep 303275 = 454913) B454913
theorem B303305 : Blo 199806 303305 := bstep (se 2 (by rfl) ⟨113739, by rfl⟩ : syracuseStep 303305 = 227479) B227479
theorem B1155329 : Blo 199806 1155329 := bstep (se 2 (by rfl) ⟨433248, by rfl⟩ : syracuseStep 1155329 = 866497) B866497
theorem B303419 : Blo 199806 303419 := bstep (se 1 (by rfl) ⟨227564, by rfl⟩ : syracuseStep 303419 = 455129) B455129
theorem B696691 : Blo 199806 696691 := bstep (se 1 (by rfl) ⟨522518, by rfl⟩ : syracuseStep 696691 = 1045037) B1045037
theorem B303479 : Blo 199806 303479 := bstep (se 1 (by rfl) ⟨227609, by rfl⟩ : syracuseStep 303479 = 455219) B455219
theorem B303503 : Blo 199806 303503 := bstep (se 1 (by rfl) ⟨227627, by rfl⟩ : syracuseStep 303503 = 455255) B455255
theorem B303545 : Blo 199806 303545 := bstep (se 2 (by rfl) ⟨113829, by rfl⟩ : syracuseStep 303545 = 227659) B227659
theorem B270793 : Blo 199806 270793 := bstep (se 2 (by rfl) ⟨101547, by rfl⟩ : syracuseStep 270793 = 203095) B203095
theorem B303623 : Blo 199806 303623 := bstep (se 1 (by rfl) ⟨227717, by rfl⟩ : syracuseStep 303623 = 455435) B455435
theorem B303659 : Blo 199806 303659 := bstep (se 1 (by rfl) ⟨227744, by rfl⟩ : syracuseStep 303659 = 455489) B455489
theorem B303689 : Blo 199806 303689 := bstep (se 2 (by rfl) ⟨113883, by rfl⟩ : syracuseStep 303689 = 227767) B227767
theorem B303803 : Blo 199806 303803 := bstep (se 1 (by rfl) ⟨227852, by rfl⟩ : syracuseStep 303803 = 455705) B455705
theorem B467657 : Blo 199806 467657 := bstep (se 2 (by rfl) ⟨175371, by rfl⟩ : syracuseStep 467657 = 350743) B350743
theorem B303863 : Blo 199806 303863 := bstep (se 1 (by rfl) ⟨227897, by rfl⟩ : syracuseStep 303863 = 455795) B455795
theorem B303887 : Blo 199806 303887 := bstep (se 1 (by rfl) ⟨227915, by rfl⟩ : syracuseStep 303887 = 455831) B455831
theorem B303929 : Blo 199806 303929 := bstep (se 2 (by rfl) ⟨113973, by rfl⟩ : syracuseStep 303929 = 227947) B227947
theorem B304007 : Blo 199806 304007 := bstep (se 1 (by rfl) ⟨228005, by rfl⟩ : syracuseStep 304007 = 456011) B456011
theorem B304043 : Blo 199806 304043 := bstep (se 1 (by rfl) ⟨228032, by rfl⟩ : syracuseStep 304043 = 456065) B456065
theorem B304073 : Blo 199806 304073 := bstep (se 2 (by rfl) ⟨114027, by rfl⟩ : syracuseStep 304073 = 228055) B228055
theorem B435145 : Blo 199806 435145 := bstep (se 2 (by rfl) ⟨163179, by rfl⟩ : syracuseStep 435145 = 326359) B326359
theorem B304187 : Blo 199806 304187 := bstep (se 1 (by rfl) ⟨228140, by rfl⟩ : syracuseStep 304187 = 456281) B456281
theorem B304247 : Blo 199806 304247 := bstep (se 1 (by rfl) ⟨228185, by rfl⟩ : syracuseStep 304247 = 456371) B456371
theorem B304271 : Blo 199806 304271 := bstep (se 1 (by rfl) ⟨228203, by rfl⟩ : syracuseStep 304271 = 456407) B456407
theorem B304313 : Blo 199806 304313 := bstep (se 2 (by rfl) ⟨114117, by rfl⟩ : syracuseStep 304313 = 228235) B228235
theorem B304391 : Blo 199806 304391 := bstep (se 1 (by rfl) ⟨228293, by rfl⟩ : syracuseStep 304391 = 456587) B456587
theorem B1221925 : Blo 199806 1221925 := bstep (se 4 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 1221925 = 229111) B229111
theorem B304427 : Blo 199806 304427 := bstep (se 1 (by rfl) ⟨228320, by rfl⟩ : syracuseStep 304427 = 456641) B456641
theorem B304457 : Blo 199806 304457 := bstep (se 2 (by rfl) ⟨114171, by rfl⟩ : syracuseStep 304457 = 228343) B228343
theorem B304571 : Blo 199806 304571 := bstep (se 1 (by rfl) ⟨228428, by rfl⟩ : syracuseStep 304571 = 456857) B456857
theorem B304631 : Blo 199806 304631 := bstep (se 1 (by rfl) ⟨228473, by rfl⟩ : syracuseStep 304631 = 456947) B456947
theorem B1156619 : Blo 199806 1156619 := bstep (se 1 (by rfl) ⟨867464, by rfl⟩ : syracuseStep 1156619 = 1734929) B1734929
theorem B304655 : Blo 199806 304655 := bstep (se 1 (by rfl) ⟨228491, by rfl⟩ : syracuseStep 304655 = 456983) B456983
theorem B304697 : Blo 199806 304697 := bstep (se 2 (by rfl) ⟨114261, by rfl⟩ : syracuseStep 304697 = 228523) B228523
theorem B861815 : Blo 199806 861815 := bstep (se 1 (by rfl) ⟨646361, by rfl⟩ : syracuseStep 861815 = 1292723) B1292723
theorem B304775 : Blo 199806 304775 := bstep (se 1 (by rfl) ⟨228581, by rfl⟩ : syracuseStep 304775 = 457163) B457163
theorem B304811 : Blo 199806 304811 := bstep (se 1 (by rfl) ⟨228608, by rfl⟩ : syracuseStep 304811 = 457217) B457217
theorem B304825 : Blo 199806 304825 := bstep (se 2 (by rfl) ⟨114309, by rfl⟩ : syracuseStep 304825 = 228619) B228619
theorem B304841 : Blo 199806 304841 := bstep (se 2 (by rfl) ⟨114315, by rfl⟩ : syracuseStep 304841 = 228631) B228631
theorem B304955 : Blo 199806 304955 := bstep (se 1 (by rfl) ⟨228716, by rfl⟩ : syracuseStep 304955 = 457433) B457433
theorem B337783 : Blo 199806 337783 := bstep (se 1 (by rfl) ⟨253337, by rfl⟩ : syracuseStep 337783 = 506675) B506675
theorem B305015 : Blo 199806 305015 := bstep (se 1 (by rfl) ⟨228761, by rfl⟩ : syracuseStep 305015 = 457523) B457523
theorem B272263 : Blo 199806 272263 := bstep (se 1 (by rfl) ⟨204197, by rfl⟩ : syracuseStep 272263 = 408395) B408395
theorem B305039 : Blo 199806 305039 := bstep (se 1 (by rfl) ⟨228779, by rfl⟩ : syracuseStep 305039 = 457559) B457559
theorem B1025945 : Blo 199806 1025945 := bstep (se 2 (by rfl) ⟨384729, by rfl⟩ : syracuseStep 1025945 = 769459) B769459
theorem B305081 : Blo 199806 305081 := bstep (se 2 (by rfl) ⟨114405, by rfl⟩ : syracuseStep 305081 = 228811) B228811
theorem B305159 : Blo 199806 305159 := bstep (se 1 (by rfl) ⟨228869, by rfl⟩ : syracuseStep 305159 = 457739) B457739
theorem B305195 : Blo 199806 305195 := bstep (se 1 (by rfl) ⟨228896, by rfl⟩ : syracuseStep 305195 = 457793) B457793
theorem B337979 : Blo 199806 337979 := bstep (se 1 (by rfl) ⟨253484, by rfl⟩ : syracuseStep 337979 = 506969) B506969
theorem B305225 : Blo 199806 305225 := bstep (se 2 (by rfl) ⟨114459, by rfl⟩ : syracuseStep 305225 = 228919) B228919
theorem B1747117 : Blo 199806 1747117 := bstep (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) B655169
theorem B305339 : Blo 199806 305339 := bstep (se 1 (by rfl) ⟨229004, by rfl⟩ : syracuseStep 305339 = 458009) B458009
theorem B305399 : Blo 199806 305399 := bstep (se 1 (by rfl) ⟨229049, by rfl⟩ : syracuseStep 305399 = 458099) B458099
theorem B305423 : Blo 199806 305423 := bstep (se 1 (by rfl) ⟨229067, by rfl⟩ : syracuseStep 305423 = 458135) B458135
theorem B305465 : Blo 199806 305465 := bstep (se 2 (by rfl) ⟨114549, by rfl⟩ : syracuseStep 305465 = 229099) B229099
theorem B305543 : Blo 199806 305543 := bstep (se 1 (by rfl) ⟨229157, by rfl⟩ : syracuseStep 305543 = 458315) B458315
theorem B960913 : Blo 199806 960913 := bstep (se 2 (by rfl) ⟨360342, by rfl⟩ : syracuseStep 960913 = 720685) B720685
theorem B305579 : Blo 199806 305579 := bstep (se 1 (by rfl) ⟨229184, by rfl⟩ : syracuseStep 305579 = 458369) B458369
theorem B1157561 : Blo 199806 1157561 := bstep (se 2 (by rfl) ⟨434085, by rfl⟩ : syracuseStep 1157561 = 868171) B868171
theorem B338377 : Blo 199806 338377 := bstep (se 2 (by rfl) ⟨126891, by rfl⟩ : syracuseStep 338377 = 253783) B253783
theorem B305609 : Blo 199806 305609 := bstep (se 2 (by rfl) ⟨114603, by rfl⟩ : syracuseStep 305609 = 229207) B229207
theorem B1387037 : Blo 199806 1387037 := bstep (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) B520139
theorem B961085 : Blo 199806 961085 := bstep (se 3 (by rfl) ⟨180203, by rfl⟩ : syracuseStep 961085 = 360407) B360407
theorem B305993 : Blo 199806 305993 := bstep (se 2 (by rfl) ⟨114747, by rfl⟩ : syracuseStep 305993 = 229495) B229495
theorem B339079 : Blo 199806 339079 := bstep (se 1 (by rfl) ⟨254309, by rfl⟩ : syracuseStep 339079 = 508619) B508619
theorem B2436637 : Blo 199806 2436637 := bstep (se 3 (by rfl) ⟨456869, by rfl⟩ : syracuseStep 2436637 = 913739) B913739
theorem B569099 : Blo 199806 569099 := bstep (se 1 (by rfl) ⟨426824, by rfl⟩ : syracuseStep 569099 = 853649) B853649
theorem B339727 : Blo 199806 339727 := bstep (se 1 (by rfl) ⟨254795, by rfl⟩ : syracuseStep 339727 = 509591) B509591
theorem B3092377 : Blo 199806 3092377 := bstep (se 2 (by rfl) ⟨1159641, by rfl⟩ : syracuseStep 3092377 = 2319283) B2319283
theorem B241655 : Blo 199806 241655 := bstep (se 1 (by rfl) ⟨181241, by rfl⟩ : syracuseStep 241655 = 362483) B362483
theorem B2601233 : Blo 199806 2601233 := bstep (se 2 (by rfl) ⟨975462, by rfl⟩ : syracuseStep 2601233 = 1950925) B1950925
theorem B340267 : Blo 199806 340267 := bstep (se 1 (by rfl) ⟨255200, by rfl⟩ : syracuseStep 340267 = 510401) B510401
theorem B766361 : Blo 199806 766361 := bstep (se 2 (by rfl) ⟨287385, by rfl⟩ : syracuseStep 766361 = 574771) B574771
theorem B1028537 : Blo 199806 1028537 := bstep (se 2 (by rfl) ⟨385701, by rfl⟩ : syracuseStep 1028537 = 771403) B771403
theorem B340409 : Blo 199806 340409 := bstep (se 2 (by rfl) ⟨127653, by rfl⟩ : syracuseStep 340409 = 255307) B255307
theorem B1159703 : Blo 199806 1159703 := bstep (se 1 (by rfl) ⟨869777, by rfl⟩ : syracuseStep 1159703 = 1739555) B1739555
theorem B2568995 : Blo 199806 2568995 := bstep (se 1 (by rfl) ⟨1926746, by rfl⟩ : syracuseStep 2568995 = 3853493) B3853493
theorem B275447 : Blo 199806 275447 := bstep (se 1 (by rfl) ⟨206585, by rfl⟩ : syracuseStep 275447 = 413171) B413171
theorem B1160203 : Blo 199806 1160203 := bstep (se 1 (by rfl) ⟨870152, by rfl⟩ : syracuseStep 1160203 = 1740305) B1740305
theorem B570397 : Blo 199806 570397 := bstep (se 3 (by rfl) ⟨106949, by rfl⟩ : syracuseStep 570397 = 213899) B213899
theorem B341111 : Blo 199806 341111 := bstep (se 1 (by rfl) ⟨255833, by rfl⟩ : syracuseStep 341111 = 511667) B511667
theorem B570739 : Blo 199806 570739 := bstep (se 1 (by rfl) ⟨428054, by rfl⟩ : syracuseStep 570739 = 856109) B856109
theorem B341563 : Blo 199806 341563 := bstep (se 1 (by rfl) ⟨256172, by rfl⟩ : syracuseStep 341563 = 512345) B512345
theorem B341705 : Blo 199806 341705 := bstep (se 2 (by rfl) ⟨128139, by rfl⟩ : syracuseStep 341705 = 256279) B256279
theorem B1029833 : Blo 199806 1029833 := bstep (se 2 (by rfl) ⟨386187, by rfl⟩ : syracuseStep 1029833 = 772375) B772375
theorem B1554565 : Blo 199806 1554565 := bstep (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) B291481
theorem B243847 : Blo 199806 243847 := bstep (se 1 (by rfl) ⟨182885, by rfl⟩ : syracuseStep 243847 = 365771) B365771
theorem B342407 : Blo 199806 342407 := bstep (se 1 (by rfl) ⟨256805, by rfl⟩ : syracuseStep 342407 = 513611) B513611
theorem B1096253 : Blo 199806 1096253 := bstep (se 3 (by rfl) ⟨205547, by rfl⟩ : syracuseStep 1096253 = 411095) B411095
theorem B506483 : Blo 199806 506483 := bstep (se 1 (by rfl) ⟨379862, by rfl⟩ : syracuseStep 506483 = 759725) B759725
theorem B867131 : Blo 199806 867131 := bstep (se 1 (by rfl) ⟨650348, by rfl⟩ : syracuseStep 867131 = 1300697) B1300697
theorem B343055 : Blo 199806 343055 := bstep (se 1 (by rfl) ⟨257291, by rfl⟩ : syracuseStep 343055 = 514583) B514583
theorem B506999 : Blo 199806 506999 := bstep (se 1 (by rfl) ⟨380249, by rfl⟩ : syracuseStep 506999 = 760499) B760499
theorem B834875 : Blo 199806 834875 := bstep (se 1 (by rfl) ⟨626156, by rfl⟩ : syracuseStep 834875 = 1252313) B1252313
theorem B343595 : Blo 199806 343595 := bstep (se 1 (by rfl) ⟨257696, by rfl⟩ : syracuseStep 343595 = 515393) B515393
theorem B540569 : Blo 199806 540569 := bstep (se 2 (by rfl) ⟨202713, by rfl⟩ : syracuseStep 540569 = 405427) B405427
theorem B1523609 : Blo 199806 1523609 := bstep (se 2 (by rfl) ⟨571353, by rfl⟩ : syracuseStep 1523609 = 1142707) B1142707
theorem B769945 : Blo 199806 769945 := bstep (se 2 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 769945 = 577459) B577459
theorem B573473 : Blo 199806 573473 := bstep (se 2 (by rfl) ⟨215052, by rfl⟩ : syracuseStep 573473 = 430105) B430105
theorem B507991 : Blo 199806 507991 := bstep (se 1 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 507991 = 761987) B761987
theorem B1392727 : Blo 199806 1392727 := bstep (se 1 (by rfl) ⟨1044545, by rfl⟩ : syracuseStep 1392727 = 2089091) B2089091
theorem B966775 : Blo 199806 966775 := bstep (se 1 (by rfl) ⟨725081, by rfl⟩ : syracuseStep 966775 = 1450163) B1450163
theorem B573587 : Blo 199806 573587 := bstep (se 1 (by rfl) ⟨430190, by rfl⟩ : syracuseStep 573587 = 860381) B860381
theorem B770249 : Blo 199806 770249 := bstep (se 2 (by rfl) ⟨288843, by rfl⟩ : syracuseStep 770249 = 577687) B577687
theorem B868589 : Blo 199806 868589 := bstep (se 3 (by rfl) ⟨162860, by rfl⟩ : syracuseStep 868589 = 325721) B325721
theorem B508295 : Blo 199806 508295 := bstep (se 1 (by rfl) ⟨381221, by rfl⟩ : syracuseStep 508295 = 762443) B762443
theorem B541129 : Blo 199806 541129 := bstep (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) B405847
theorem B508427 : Blo 199806 508427 := bstep (se 1 (by rfl) ⟨381320, by rfl⟩ : syracuseStep 508427 = 762641) B762641
theorem B541217 : Blo 199806 541217 := bstep (se 2 (by rfl) ⟨202956, by rfl⟩ : syracuseStep 541217 = 405913) B405913
theorem B868907 : Blo 199806 868907 := bstep (se 1 (by rfl) ⟨651680, by rfl⟩ : syracuseStep 868907 = 1303361) B1303361
theorem B574361 : Blo 199806 574361 := bstep (se 2 (by rfl) ⟨215385, by rfl⟩ : syracuseStep 574361 = 430771) B430771
theorem B508943 : Blo 199806 508943 := bstep (se 1 (by rfl) ⟨381707, by rfl⟩ : syracuseStep 508943 = 763415) B763415
theorem B541811 : Blo 199806 541811 := bstep (se 1 (by rfl) ⟨406358, by rfl⟩ : syracuseStep 541811 = 812717) B812717
theorem B771191 : Blo 199806 771191 := bstep (se 1 (by rfl) ⟨578393, by rfl⟩ : syracuseStep 771191 = 1156787) B1156787
theorem B509075 : Blo 199806 509075 := bstep (se 1 (by rfl) ⟨381806, by rfl⟩ : syracuseStep 509075 = 763613) B763613
theorem B9880865 : Blo 199806 9880865 := bstep (se 2 (by rfl) ⟨3705324, by rfl⟩ : syracuseStep 9880865 = 7410649) B7410649
theorem B607603 : Blo 199806 607603 := bstep (se 1 (by rfl) ⟨455702, by rfl⟩ : syracuseStep 607603 = 911405) B911405
theorem B1525553 : Blo 199806 1525553 := bstep (se 2 (by rfl) ⟨572082, by rfl⟩ : syracuseStep 1525553 = 1144165) B1144165
theorem B968507 : Blo 199806 968507 := bstep (se 1 (by rfl) ⟨726380, by rfl⟩ : syracuseStep 968507 = 1452761) B1452761
theorem B772163 : Blo 199806 772163 := bstep (se 1 (by rfl) ⟨579122, by rfl⟩ : syracuseStep 772163 = 1158245) B1158245
theorem B510209 : Blo 199806 510209 := bstep (se 2 (by rfl) ⟨191328, by rfl⟩ : syracuseStep 510209 = 382657) B382657
theorem B1722809 : Blo 199806 1722809 := bstep (se 2 (by rfl) ⟨646053, by rfl⟩ : syracuseStep 1722809 = 1292107) B1292107
theorem B576001 : Blo 199806 576001 := bstep (se 2 (by rfl) ⟨216000, by rfl⟩ : syracuseStep 576001 = 432001) B432001
theorem B510583 : Blo 199806 510583 := bstep (se 1 (by rfl) ⟨382937, by rfl⟩ : syracuseStep 510583 = 765875) B765875
theorem B1231553 : Blo 199806 1231553 := bstep (se 2 (by rfl) ⟨461832, by rfl⟩ : syracuseStep 1231553 = 923665) B923665
theorem B19942129 : Blo 199806 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B674675 : Blo 199806 674675 := bstep (se 1 (by rfl) ⟨506006, by rfl⟩ : syracuseStep 674675 = 1012013) B1012013
theorem B511019 : Blo 199806 511019 := bstep (se 1 (by rfl) ⟨383264, by rfl⟩ : syracuseStep 511019 = 766529) B766529
theorem B576571 : Blo 199806 576571 := bstep (se 1 (by rfl) ⟨432428, by rfl⟩ : syracuseStep 576571 = 864857) B864857
theorem B1953233 : Blo 199806 1953233 := bstep (se 2 (by rfl) ⟨732462, by rfl⟩ : syracuseStep 1953233 = 1464925) B1464925
theorem B1920631 : Blo 199806 1920631 := bstep (se 1 (by rfl) ⟨1440473, by rfl⟩ : syracuseStep 1920631 = 2880947) B2880947
theorem B511859 : Blo 199806 511859 := bstep (se 1 (by rfl) ⟨383894, by rfl⟩ : syracuseStep 511859 = 767789) B767789
theorem B511879 : Blo 199806 511879 := bstep (se 1 (by rfl) ⟨383909, by rfl⟩ : syracuseStep 511879 = 767819) B767819
theorem B380857 : Blo 199806 380857 := bstep (se 2 (by rfl) ⟨142821, by rfl⟩ : syracuseStep 380857 = 285643) B285643
theorem B643133 : Blo 199806 643133 := bstep (se 3 (by rfl) ⟨120587, by rfl⟩ : syracuseStep 643133 = 241175) B241175
theorem B512153 : Blo 199806 512153 := bstep (se 2 (by rfl) ⟨192057, by rfl⟩ : syracuseStep 512153 = 384115) B384115
theorem B381199 : Blo 199806 381199 := bstep (se 1 (by rfl) ⟨285899, by rfl⟩ : syracuseStep 381199 = 571799) B571799
theorem B512315 : Blo 199806 512315 := bstep (se 1 (by rfl) ⟨384236, by rfl⟩ : syracuseStep 512315 = 768473) B768473
theorem B512527 : Blo 199806 512527 := bstep (se 1 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 512527 = 768791) B768791
theorem B905795 : Blo 199806 905795 := bstep (se 1 (by rfl) ⟨679346, by rfl⟩ : syracuseStep 905795 = 1358693) B1358693
theorem B512801 : Blo 199806 512801 := bstep (se 2 (by rfl) ⟨192300, by rfl⟩ : syracuseStep 512801 = 384601) B384601
theorem B545737 : Blo 199806 545737 := bstep (se 2 (by rfl) ⟨204651, by rfl⟩ : syracuseStep 545737 = 409303) B409303
theorem B382087 : Blo 199806 382087 := bstep (se 1 (by rfl) ⟨286565, by rfl⟩ : syracuseStep 382087 = 573131) B573131
theorem B677267 : Blo 199806 677267 := bstep (se 1 (by rfl) ⟨507950, by rfl⟩ : syracuseStep 677267 = 1015901) B1015901
theorem B578963 : Blo 199806 578963 := bstep (se 1 (by rfl) ⟨434222, by rfl⟩ : syracuseStep 578963 = 868445) B868445
theorem B1234379 : Blo 199806 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B513803 : Blo 199806 513803 := bstep (se 1 (by rfl) ⟨385352, by rfl⟩ : syracuseStep 513803 = 770705) B770705
theorem B1464227 : Blo 199806 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B645131 : Blo 199806 645131 := bstep (se 1 (by rfl) ⟨483848, by rfl⟩ : syracuseStep 645131 = 967697) B967697
theorem B1038347 : Blo 199806 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B579737 : Blo 199806 579737 := bstep (se 2 (by rfl) ⟨217401, by rfl⟩ : syracuseStep 579737 = 434803) B434803
theorem B481465 : Blo 199806 481465 := bstep (se 2 (by rfl) ⟨180549, by rfl⟩ : syracuseStep 481465 = 361099) B361099
theorem B284971 : Blo 199806 284971 := bstep (se 1 (by rfl) ⟨213728, by rfl⟩ : syracuseStep 284971 = 427457) B427457
theorem B514451 : Blo 199806 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B3103217 : Blo 199806 3103217 := bstep (se 2 (by rfl) ⟨1163706, by rfl⟩ : syracuseStep 3103217 = 2327413) B2327413
theorem B514745 : Blo 199806 514745 := bstep (se 2 (by rfl) ⟨193029, by rfl⟩ : syracuseStep 514745 = 386059) B386059
theorem B678671 : Blo 199806 678671 := bstep (se 1 (by rfl) ⟨509003, by rfl⟩ : syracuseStep 678671 = 1018007) B1018007
theorem B973619 : Blo 199806 973619 := bstep (se 1 (by rfl) ⟨730214, by rfl⟩ : syracuseStep 973619 = 1460429) B1460429
theorem B383879 : Blo 199806 383879 := bstep (se 1 (by rfl) ⟨287909, by rfl⟩ : syracuseStep 383879 = 575819) B575819
theorem B678941 : Blo 199806 678941 := bstep (se 3 (by rfl) ⟨127301, by rfl⟩ : syracuseStep 678941 = 254603) B254603
theorem B548041 : Blo 199806 548041 := bstep (se 2 (by rfl) ⟨205515, by rfl⟩ : syracuseStep 548041 = 411031) B411031
theorem B515443 : Blo 199806 515443 := bstep (se 1 (by rfl) ⟨386582, by rfl⟩ : syracuseStep 515443 = 773165) B773165
theorem B449927 : Blo 199806 449927 := bstep (se 1 (by rfl) ⟨337445, by rfl⟩ : syracuseStep 449927 = 674891) B674891
theorem B286087 : Blo 199806 286087 := bstep (se 1 (by rfl) ⟨214565, by rfl⟩ : syracuseStep 286087 = 429131) B429131
theorem B515585 : Blo 199806 515585 := bstep (se 2 (by rfl) ⟨193344, by rfl⟩ : syracuseStep 515585 = 386689) B386689
theorem B482849 : Blo 199806 482849 := bstep (se 2 (by rfl) ⟨181068, by rfl⟩ : syracuseStep 482849 = 362137) B362137
theorem B450107 : Blo 199806 450107 := bstep (se 1 (by rfl) ⟨337580, by rfl⟩ : syracuseStep 450107 = 675161) B675161
theorem B450233 : Blo 199806 450233 := bstep (se 2 (by rfl) ⟨168837, by rfl⟩ : syracuseStep 450233 = 337675) B337675
theorem B253687 : Blo 199806 253687 := bstep (se 1 (by rfl) ⟨190265, by rfl⟩ : syracuseStep 253687 = 380531) B380531
theorem B1171421 : Blo 199806 1171421 := bstep (se 3 (by rfl) ⟨219641, by rfl⟩ : syracuseStep 1171421 = 439283) B439283
theorem B450575 : Blo 199806 450575 := bstep (se 1 (by rfl) ⟨337931, by rfl⟩ : syracuseStep 450575 = 675863) B675863
theorem B450593 : Blo 199806 450593 := bstep (se 2 (by rfl) ⟨168972, by rfl⟩ : syracuseStep 450593 = 337945) B337945
theorem B254011 : Blo 199806 254011 := bstep (se 1 (by rfl) ⟨190508, by rfl⟩ : syracuseStep 254011 = 381017) B381017
theorem B286907 : Blo 199806 286907 := bstep (se 1 (by rfl) ⟨215180, by rfl⟩ : syracuseStep 286907 = 430361) B430361
theorem B1466657 : Blo 199806 1466657 := bstep (se 2 (by rfl) ⟨549996, by rfl⟩ : syracuseStep 1466657 = 1099993) B1099993
theorem B450935 : Blo 199806 450935 := bstep (se 1 (by rfl) ⟨338201, by rfl⟩ : syracuseStep 450935 = 676403) B676403
theorem B680345 : Blo 199806 680345 := bstep (se 2 (by rfl) ⟨255129, by rfl⟩ : syracuseStep 680345 = 510259) B510259
theorem B451115 : Blo 199806 451115 := bstep (se 1 (by rfl) ⟨338336, by rfl⟩ : syracuseStep 451115 = 676673) B676673
theorem B1368695 : Blo 199806 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B1466999 : Blo 199806 1466999 := bstep (se 1 (by rfl) ⟨1100249, by rfl⟩ : syracuseStep 1466999 = 2200499) B2200499
theorem B1172141 : Blo 199806 1172141 := bstep (se 3 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 1172141 = 439553) B439553
theorem B287545 : Blo 199806 287545 := bstep (se 2 (by rfl) ⟨107829, by rfl⟩ : syracuseStep 287545 = 215659) B215659
theorem B320375 : Blo 199806 320375 := bstep (se 1 (by rfl) ⟨240281, by rfl⟩ : syracuseStep 320375 = 480563) B480563
theorem B451475 : Blo 199806 451475 := bstep (se 1 (by rfl) ⟨338606, by rfl⟩ : syracuseStep 451475 = 677213) B677213
theorem B1139609 : Blo 199806 1139609 := bstep (se 2 (by rfl) ⟨427353, by rfl⟩ : syracuseStep 1139609 = 854707) B854707
theorem B287659 : Blo 199806 287659 := bstep (se 1 (by rfl) ⟨215744, by rfl⟩ : syracuseStep 287659 = 431489) B431489
theorem B8479667 : Blo 199806 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B451529 : Blo 199806 451529 := bstep (se 2 (by rfl) ⟨169323, by rfl⟩ : syracuseStep 451529 = 338647) B338647
theorem B254983 : Blo 199806 254983 := bstep (se 1 (by rfl) ⟨191237, by rfl⟩ : syracuseStep 254983 = 382475) B382475
theorem B615485 : Blo 199806 615485 := bstep (se 3 (by rfl) ⟨115403, by rfl⟩ : syracuseStep 615485 = 230807) B230807
theorem B681047 : Blo 199806 681047 := bstep (se 1 (by rfl) ⟨510785, by rfl⟩ : syracuseStep 681047 = 1021571) B1021571
theorem B287887 : Blo 199806 287887 := bstep (se 1 (by rfl) ⟨215915, by rfl⟩ : syracuseStep 287887 = 431831) B431831
theorem B386363 : Blo 199806 386363 := bstep (se 1 (by rfl) ⟨289772, by rfl⟩ : syracuseStep 386363 = 579545) B579545
theorem B1533329 : Blo 199806 1533329 := bstep (se 2 (by rfl) ⟨574998, by rfl⟩ : syracuseStep 1533329 = 1149997) B1149997
theorem B255403 : Blo 199806 255403 := bstep (se 1 (by rfl) ⟨191552, by rfl⟩ : syracuseStep 255403 = 383105) B383105
theorem B681533 : Blo 199806 681533 := bstep (se 3 (by rfl) ⟨127787, by rfl⟩ : syracuseStep 681533 = 255575) B255575
theorem B2582117 : Blo 199806 2582117 := bstep (se 4 (by rfl) ⟨242073, by rfl⟩ : syracuseStep 2582117 = 484147) B484147
theorem B452231 : Blo 199806 452231 := bstep (se 1 (by rfl) ⟨339173, by rfl⟩ : syracuseStep 452231 = 678347) B678347
theorem B255631 : Blo 199806 255631 := bstep (se 1 (by rfl) ⟨191723, by rfl⟩ : syracuseStep 255631 = 383447) B383447
theorem B386849 : Blo 199806 386849 := bstep (se 2 (by rfl) ⟨145068, by rfl⟩ : syracuseStep 386849 = 290137) B290137
theorem B452411 : Blo 199806 452411 := bstep (se 1 (by rfl) ⟨339308, by rfl⟩ : syracuseStep 452411 = 678617) B678617
theorem B550775 : Blo 199806 550775 := bstep (se 1 (by rfl) ⟨413081, by rfl⟩ : syracuseStep 550775 = 826163) B826163
theorem B452537 : Blo 199806 452537 := bstep (se 2 (by rfl) ⟨169701, by rfl⟩ : syracuseStep 452537 = 339403) B339403
theorem B288775 : Blo 199806 288775 := bstep (se 1 (by rfl) ⟨216581, by rfl⟩ : syracuseStep 288775 = 433163) B433163
theorem B649259 : Blo 199806 649259 := bstep (se 1 (by rfl) ⟨486944, by rfl⟩ : syracuseStep 649259 = 973889) B973889
theorem B452879 : Blo 199806 452879 := bstep (se 1 (by rfl) ⟨339659, by rfl⟩ : syracuseStep 452879 = 679319) B679319
theorem B452897 : Blo 199806 452897 := bstep (se 2 (by rfl) ⟨169836, by rfl⟩ : syracuseStep 452897 = 339673) B339673
theorem B256375 : Blo 199806 256375 := bstep (se 1 (by rfl) ⟨192281, by rfl⟩ : syracuseStep 256375 = 384563) B384563
theorem B321977 : Blo 199806 321977 := bstep (se 2 (by rfl) ⟨120741, by rfl⟩ : syracuseStep 321977 = 241483) B241483
theorem B289271 : Blo 199806 289271 := bstep (se 1 (by rfl) ⟨216953, by rfl⟩ : syracuseStep 289271 = 433907) B433907
theorem B453239 : Blo 199806 453239 := bstep (se 1 (by rfl) ⟨339929, by rfl⟩ : syracuseStep 453239 = 679859) B679859
theorem B256699 : Blo 199806 256699 := bstep (se 1 (by rfl) ⟨192524, by rfl⟩ : syracuseStep 256699 = 385049) B385049
theorem B813769 : Blo 199806 813769 := bstep (se 2 (by rfl) ⟨305163, by rfl⟩ : syracuseStep 813769 = 610327) B610327
theorem B453419 : Blo 199806 453419 := bstep (se 1 (by rfl) ⟨340064, by rfl⟩ : syracuseStep 453419 = 680129) B680129
theorem B322489 : Blo 199806 322489 := bstep (se 2 (by rfl) ⟨120933, by rfl⟩ : syracuseStep 322489 = 241867) B241867
theorem B682937 : Blo 199806 682937 := bstep (se 2 (by rfl) ⟨256101, by rfl⟩ : syracuseStep 682937 = 512203) B512203
theorem B977923 : Blo 199806 977923 := bstep (se 1 (by rfl) ⟨733442, by rfl⟩ : syracuseStep 977923 = 1466885) B1466885
theorem B650359 : Blo 199806 650359 := bstep (se 1 (by rfl) ⟨487769, by rfl⟩ : syracuseStep 650359 = 975539) B975539
theorem B453779 : Blo 199806 453779 := bstep (se 1 (by rfl) ⟨340334, by rfl⟩ : syracuseStep 453779 = 680669) B680669
theorem B257195 : Blo 199806 257195 := bstep (se 1 (by rfl) ⟨192896, by rfl⟩ : syracuseStep 257195 = 385793) B385793
theorem B453833 : Blo 199806 453833 := bstep (se 2 (by rfl) ⟨170187, by rfl⟩ : syracuseStep 453833 = 340375) B340375
theorem B257287 : Blo 199806 257287 := bstep (se 1 (by rfl) ⟨192965, by rfl⟩ : syracuseStep 257287 = 385931) B385931
theorem B683531 : Blo 199806 683531 := bstep (se 1 (by rfl) ⟨512648, by rfl⟩ : syracuseStep 683531 = 1025297) B1025297
theorem B683639 : Blo 199806 683639 := bstep (se 1 (by rfl) ⟨512729, by rfl⟩ : syracuseStep 683639 = 1025459) B1025459
theorem B323207 : Blo 199806 323207 := bstep (se 1 (by rfl) ⟨242405, by rfl⟩ : syracuseStep 323207 = 484811) B484811
theorem B257671 : Blo 199806 257671 := bstep (se 1 (by rfl) ⟨193253, by rfl⟩ : syracuseStep 257671 = 386507) B386507
theorem B1994419 : Blo 199806 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B225031 : Blo 199806 225031 := bstep (se 1 (by rfl) ⟨168773, by rfl⟩ : syracuseStep 225031 = 337547) B337547
theorem B1535759 : Blo 199806 1535759 := bstep (se 1 (by rfl) ⟨1151819, by rfl⟩ : syracuseStep 1535759 = 2303639) B2303639
theorem B454535 : Blo 199806 454535 := bstep (se 1 (by rfl) ⟨340901, by rfl⟩ : syracuseStep 454535 = 681803) B681803
theorem B225211 : Blo 199806 225211 := bstep (se 1 (by rfl) ⟨168908, by rfl⟩ : syracuseStep 225211 = 337817) B337817
theorem B454715 : Blo 199806 454715 := bstep (se 1 (by rfl) ⟨341036, by rfl⟩ : syracuseStep 454715 = 682073) B682073
theorem B487559 : Blo 199806 487559 := bstep (se 1 (by rfl) ⟨365669, by rfl⟩ : syracuseStep 487559 = 731339) B731339
theorem B454841 : Blo 199806 454841 := bstep (se 2 (by rfl) ⟨170565, by rfl⟩ : syracuseStep 454841 = 341131) B341131
theorem B684233 : Blo 199806 684233 := bstep (se 2 (by rfl) ⟨256587, by rfl⟩ : syracuseStep 684233 = 513175) B513175
theorem B225679 : Blo 199806 225679 := bstep (se 1 (by rfl) ⟨169259, by rfl⟩ : syracuseStep 225679 = 338519) B338519
theorem B455183 : Blo 199806 455183 := bstep (se 1 (by rfl) ⟨341387, by rfl⟩ : syracuseStep 455183 = 682775) B682775
theorem B455201 : Blo 199806 455201 := bstep (se 2 (by rfl) ⟨170700, by rfl⟩ : syracuseStep 455201 = 341401) B341401
theorem B1733197 : Blo 199806 1733197 := bstep (se 3 (by rfl) ⟨324974, by rfl⟩ : syracuseStep 1733197 = 649949) B649949
theorem B455543 : Blo 199806 455543 := bstep (se 1 (by rfl) ⟨341657, by rfl⟩ : syracuseStep 455543 = 683315) B683315
theorem B226183 : Blo 199806 226183 := bstep (se 1 (by rfl) ⟨169637, by rfl⟩ : syracuseStep 226183 = 339275) B339275
theorem B684935 : Blo 199806 684935 := bstep (se 1 (by rfl) ⟨513701, by rfl⟩ : syracuseStep 684935 = 1027403) B1027403
theorem B914323 : Blo 199806 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B455723 : Blo 199806 455723 := bstep (se 1 (by rfl) ⟨341792, by rfl⟩ : syracuseStep 455723 = 683585) B683585
theorem B226363 : Blo 199806 226363 := bstep (se 1 (by rfl) ⟨169772, by rfl⟩ : syracuseStep 226363 = 339545) B339545
theorem B324667 : Blo 199806 324667 := bstep (se 1 (by rfl) ⟨243500, by rfl⟩ : syracuseStep 324667 = 487001) B487001
theorem B1012823 : Blo 199806 1012823 := bstep (se 1 (by rfl) ⟨759617, by rfl⟩ : syracuseStep 1012823 = 1519235) B1519235
theorem B816365 : Blo 199806 816365 := bstep (se 3 (by rfl) ⟨153068, by rfl⟩ : syracuseStep 816365 = 306137) B306137
theorem B685313 : Blo 199806 685313 := bstep (se 2 (by rfl) ⟨256992, by rfl⟩ : syracuseStep 685313 = 513985) B513985
theorem B587051 : Blo 199806 587051 := bstep (se 1 (by rfl) ⟨440288, by rfl⟩ : syracuseStep 587051 = 880577) B880577
theorem B456083 : Blo 199806 456083 := bstep (se 1 (by rfl) ⟨342062, by rfl⟩ : syracuseStep 456083 = 684125) B684125
theorem B456137 : Blo 199806 456137 := bstep (se 2 (by rfl) ⟨171051, by rfl⟩ : syracuseStep 456137 = 342103) B342103
theorem B226831 : Blo 199806 226831 := bstep (se 1 (by rfl) ⟨170123, by rfl⟩ : syracuseStep 226831 = 340247) B340247
theorem B1013309 : Blo 199806 1013309 := bstep (se 3 (by rfl) ⟨189995, by rfl⟩ : syracuseStep 1013309 = 379991) B379991
theorem B1144439 : Blo 199806 1144439 := bstep (se 1 (by rfl) ⟨858329, by rfl⟩ : syracuseStep 1144439 = 1716659) B1716659
theorem B4159127 : Blo 199806 4159127 := bstep (se 1 (by rfl) ⟨3119345, by rfl⟩ : syracuseStep 4159127 = 6238691) B6238691
theorem B1144691 : Blo 199806 1144691 := bstep (se 1 (by rfl) ⟨858518, by rfl⟩ : syracuseStep 1144691 = 1717037) B1717037
theorem B227335 : Blo 199806 227335 := bstep (se 1 (by rfl) ⟨170501, by rfl⟩ : syracuseStep 227335 = 341003) B341003
theorem B686123 : Blo 199806 686123 := bstep (se 1 (by rfl) ⟨514592, by rfl⟩ : syracuseStep 686123 = 1029185) B1029185
theorem B456839 : Blo 199806 456839 := bstep (se 1 (by rfl) ⟨342629, by rfl⟩ : syracuseStep 456839 = 685259) B685259
theorem B227515 : Blo 199806 227515 := bstep (se 1 (by rfl) ⟨170636, by rfl⟩ : syracuseStep 227515 = 341273) B341273
theorem B457019 : Blo 199806 457019 := bstep (se 1 (by rfl) ⟨342764, by rfl⟩ : syracuseStep 457019 = 685529) B685529
theorem B457145 : Blo 199806 457145 := bstep (se 2 (by rfl) ⟨171429, by rfl⟩ : syracuseStep 457145 = 342859) B342859
theorem B227983 : Blo 199806 227983 := bstep (se 1 (by rfl) ⟨170987, by rfl⟩ : syracuseStep 227983 = 341975) B341975
theorem B1440449 : Blo 199806 1440449 := bstep (se 2 (by rfl) ⟨540168, by rfl⟩ : syracuseStep 1440449 = 1080337) B1080337
theorem B817921 : Blo 199806 817921 := bstep (se 2 (by rfl) ⟨306720, by rfl⟩ : syracuseStep 817921 = 613441) B613441
theorem B457487 : Blo 199806 457487 := bstep (se 1 (by rfl) ⟨343115, by rfl⟩ : syracuseStep 457487 = 686231) B686231
theorem B457505 : Blo 199806 457505 := bstep (se 2 (by rfl) ⟨171564, by rfl⟩ : syracuseStep 457505 = 343129) B343129
theorem B2063141 : Blo 199806 2063141 := bstep (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) B386839
theorem B260983 : Blo 199806 260983 := bstep (se 1 (by rfl) ⟨195737, by rfl⟩ : syracuseStep 260983 = 391475) B391475
theorem B457847 : Blo 199806 457847 := bstep (se 1 (by rfl) ⟨343385, by rfl⟩ : syracuseStep 457847 = 686771) B686771
theorem B228487 : Blo 199806 228487 := bstep (se 1 (by rfl) ⟨171365, by rfl⟩ : syracuseStep 228487 = 342731) B342731
theorem B457913 : Blo 199806 457913 := bstep (se 2 (by rfl) ⟨171717, by rfl⟩ : syracuseStep 457913 = 343435) B343435
theorem B1146149 : Blo 199806 1146149 := bstep (se 4 (by rfl) ⟨107451, by rfl⟩ : syracuseStep 1146149 = 214903) B214903
theorem B458027 : Blo 199806 458027 := bstep (se 1 (by rfl) ⟨343520, by rfl⟩ : syracuseStep 458027 = 687041) B687041
theorem B1015091 : Blo 199806 1015091 := bstep (se 1 (by rfl) ⟨761318, by rfl⟩ : syracuseStep 1015091 = 1522637) B1522637
theorem B228667 : Blo 199806 228667 := bstep (se 1 (by rfl) ⟨171500, by rfl⟩ : syracuseStep 228667 = 343001) B343001
theorem B687419 : Blo 199806 687419 := bstep (se 1 (by rfl) ⟨515564, by rfl⟩ : syracuseStep 687419 = 1031129) B1031129
theorem B720413 : Blo 199806 720413 := bstep (se 3 (by rfl) ⟨135077, by rfl⟩ : syracuseStep 720413 = 270155) B270155
theorem B1015415 : Blo 199806 1015415 := bstep (se 1 (by rfl) ⟨761561, by rfl⟩ : syracuseStep 1015415 = 1523123) B1523123
theorem B458387 : Blo 199806 458387 := bstep (se 1 (by rfl) ⟨343790, by rfl⟩ : syracuseStep 458387 = 687581) B687581
theorem B458441 : Blo 199806 458441 := bstep (se 2 (by rfl) ⟨171915, by rfl⟩ : syracuseStep 458441 = 343831) B343831
theorem B7307009 : Blo 199806 7307009 := bstep (se 2 (by rfl) ⟨2740128, by rfl⟩ : syracuseStep 7307009 = 5480257) B5480257
theorem B229135 : Blo 199806 229135 := bstep (se 1 (by rfl) ⟨171851, by rfl⟩ : syracuseStep 229135 = 343703) B343703
theorem B392993 : Blo 199806 392993 := bstep (se 2 (by rfl) ⟨147372, by rfl⟩ : syracuseStep 392993 = 294745) B294745
theorem B655379 : Blo 199806 655379 := bstep (se 1 (by rfl) ⟨491534, by rfl⟩ : syracuseStep 655379 = 983069) B983069
theorem B1540133 : Blo 199806 1540133 := bstep (se 4 (by rfl) ⟨144387, by rfl⟩ : syracuseStep 1540133 = 288775) B288775
theorem B360811 : Blo 199806 360811 := bstep (se 1 (by rfl) ⟨270608, by rfl⟩ : syracuseStep 360811 = 541217) B541217
theorem B21955157 : Blo 199806 21955157 := bstep (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) B257287
theorem B721505 : Blo 199806 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B361057 : Blo 199806 361057 := bstep (se 2 (by rfl) ⟨135396, by rfl⟩ : syracuseStep 361057 = 270793) B270793
theorem B361207 : Blo 199806 361207 := bstep (se 1 (by rfl) ⟨270905, by rfl⟩ : syracuseStep 361207 = 541811) B541811
theorem B6587243 : Blo 199806 6587243 := bstep (se 1 (by rfl) ⟨4940432, by rfl⟩ : syracuseStep 6587243 = 9880865) B9880865
theorem B328711 : Blo 199806 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B1017035 : Blo 199806 1017035 := bstep (se 1 (by rfl) ⟨762776, by rfl⟩ : syracuseStep 1017035 = 1525553) B1525553
theorem B1148539 : Blo 199806 1148539 := bstep (se 1 (by rfl) ⟨861404, by rfl⟩ : syracuseStep 1148539 = 1722809) B1722809
theorem B821035 : Blo 199806 821035 := bstep (se 1 (by rfl) ⟨615776, by rfl⟩ : syracuseStep 821035 = 1231553) B1231553
theorem B8259479 : Blo 199806 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B854333 : Blo 199806 854333 := bstep (se 3 (by rfl) ⟨160187, by rfl⟩ : syracuseStep 854333 = 320375) B320375
theorem B363017 : Blo 199806 363017 := bstep (se 2 (by rfl) ⟨136131, by rfl⟩ : syracuseStep 363017 = 272263) B272263
theorem B428755 : Blo 199806 428755 := bstep (se 1 (by rfl) ⟨321566, by rfl⟩ : syracuseStep 428755 = 643133) B643133
theorem B723755 : Blo 199806 723755 := bstep (se 1 (by rfl) ⟨542816, by rfl⟩ : syracuseStep 723755 = 1085633) B1085633
theorem B1641293 : Blo 199806 1641293 := bstep (se 3 (by rfl) ⟨307742, by rfl⟩ : syracuseStep 1641293 = 615485) B615485
theorem B2329489 : Blo 199806 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B920747 : Blo 199806 920747 := bstep (se 1 (by rfl) ⟨690560, by rfl⟩ : syracuseStep 920747 = 1381121) B1381121
theorem B199855 : Blo 199806 199855 := bstep (se 1 (by rfl) ⟨149891, by rfl⟩ : syracuseStep 199855 = 299783) B299783
theorem B1281217 : Blo 199806 1281217 := bstep (se 2 (by rfl) ⟨480456, by rfl⟩ : syracuseStep 1281217 = 960913) B960913
theorem B199879 : Blo 199806 199879 := bstep (se 1 (by rfl) ⟨149909, by rfl⟩ : syracuseStep 199879 = 299819) B299819
theorem B199899 : Blo 199806 199899 := bstep (se 1 (by rfl) ⟨149924, by rfl⟩ : syracuseStep 199899 = 299849) B299849
theorem B462071 : Blo 199806 462071 := bstep (se 1 (by rfl) ⟨346553, by rfl⟩ : syracuseStep 462071 = 693107) B693107
theorem B199975 : Blo 199806 199975 := bstep (se 1 (by rfl) ⟨149981, by rfl⟩ : syracuseStep 199975 = 299963) B299963
theorem B200015 : Blo 199806 200015 := bstep (se 1 (by rfl) ⟨150011, by rfl⟩ : syracuseStep 200015 = 300023) B300023
theorem B200031 : Blo 199806 200031 := bstep (se 1 (by rfl) ⟨150023, by rfl⟩ : syracuseStep 200031 = 300047) B300047
theorem B200059 : Blo 199806 200059 := bstep (se 1 (by rfl) ⟨150044, by rfl⟩ : syracuseStep 200059 = 300089) B300089
theorem B200111 : Blo 199806 200111 := bstep (se 1 (by rfl) ⟨150083, by rfl⟩ : syracuseStep 200111 = 300167) B300167
theorem B200135 : Blo 199806 200135 := bstep (se 1 (by rfl) ⟨150101, by rfl⟩ : syracuseStep 200135 = 300203) B300203
theorem B200155 : Blo 199806 200155 := bstep (se 1 (by rfl) ⟨150116, by rfl⟩ : syracuseStep 200155 = 300233) B300233
theorem B200231 : Blo 199806 200231 := bstep (se 1 (by rfl) ⟨150173, by rfl⟩ : syracuseStep 200231 = 300347) B300347
theorem B200271 : Blo 199806 200271 := bstep (se 1 (by rfl) ⟨150203, by rfl⟩ : syracuseStep 200271 = 300407) B300407
theorem B200287 : Blo 199806 200287 := bstep (se 1 (by rfl) ⟨150215, by rfl⟩ : syracuseStep 200287 = 300431) B300431
theorem B200315 : Blo 199806 200315 := bstep (se 1 (by rfl) ⟨150236, by rfl⟩ : syracuseStep 200315 = 300473) B300473
theorem B200367 : Blo 199806 200367 := bstep (se 1 (by rfl) ⟨150275, by rfl⟩ : syracuseStep 200367 = 300551) B300551
theorem B200391 : Blo 199806 200391 := bstep (se 1 (by rfl) ⟨150293, by rfl⟩ : syracuseStep 200391 = 300587) B300587
theorem B200411 : Blo 199806 200411 := bstep (se 1 (by rfl) ⟨150308, by rfl⟩ : syracuseStep 200411 = 300617) B300617
theorem B200487 : Blo 199806 200487 := bstep (se 1 (by rfl) ⟨150365, by rfl⟩ : syracuseStep 200487 = 300731) B300731
theorem B200527 : Blo 199806 200527 := bstep (se 1 (by rfl) ⟨150395, by rfl⟩ : syracuseStep 200527 = 300791) B300791
theorem B200543 : Blo 199806 200543 := bstep (se 1 (by rfl) ⟨150407, by rfl⟩ : syracuseStep 200543 = 300815) B300815
theorem B200571 : Blo 199806 200571 := bstep (se 1 (by rfl) ⟨150428, by rfl⟩ : syracuseStep 200571 = 300857) B300857
theorem B1707911 : Blo 199806 1707911 := bstep (se 1 (by rfl) ⟨1280933, by rfl⟩ : syracuseStep 1707911 = 2561867) B2561867
theorem B429985 : Blo 199806 429985 := bstep (se 2 (by rfl) ⟨161244, by rfl⟩ : syracuseStep 429985 = 322489) B322489
theorem B200623 : Blo 199806 200623 := bstep (se 1 (by rfl) ⟨150467, by rfl⟩ : syracuseStep 200623 = 300935) B300935
theorem B200647 : Blo 199806 200647 := bstep (se 1 (by rfl) ⟨150485, by rfl⟩ : syracuseStep 200647 = 300971) B300971
theorem B200667 : Blo 199806 200667 := bstep (se 1 (by rfl) ⟨150500, by rfl⟩ : syracuseStep 200667 = 301001) B301001
theorem B4362245 : Blo 199806 4362245 := bstep (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) B817921
theorem B692231 : Blo 199806 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B200743 : Blo 199806 200743 := bstep (se 1 (by rfl) ⟨150557, by rfl⟩ : syracuseStep 200743 = 301115) B301115
theorem B200783 : Blo 199806 200783 := bstep (se 1 (by rfl) ⟨150587, by rfl⟩ : syracuseStep 200783 = 301175) B301175
theorem B200799 : Blo 199806 200799 := bstep (se 1 (by rfl) ⟨150599, by rfl⟩ : syracuseStep 200799 = 301199) B301199
theorem B200827 : Blo 199806 200827 := bstep (se 1 (by rfl) ⟨150620, by rfl⟩ : syracuseStep 200827 = 301241) B301241
theorem B200879 : Blo 199806 200879 := bstep (se 1 (by rfl) ⟨150659, by rfl⟩ : syracuseStep 200879 = 301319) B301319
theorem B200903 : Blo 199806 200903 := bstep (se 1 (by rfl) ⟨150677, by rfl⟩ : syracuseStep 200903 = 301355) B301355
theorem B200923 : Blo 199806 200923 := bstep (se 1 (by rfl) ⟨150692, by rfl⟩ : syracuseStep 200923 = 301385) B301385
theorem B200999 : Blo 199806 200999 := bstep (se 1 (by rfl) ⟨150749, by rfl⟩ : syracuseStep 200999 = 301499) B301499
theorem B2068811 : Blo 199806 2068811 := bstep (se 1 (by rfl) ⟨1551608, by rfl⟩ : syracuseStep 2068811 = 3103217) B3103217
theorem B201039 : Blo 199806 201039 := bstep (se 1 (by rfl) ⟨150779, by rfl⟩ : syracuseStep 201039 = 301559) B301559
theorem B201055 : Blo 199806 201055 := bstep (se 1 (by rfl) ⟨150791, by rfl⟩ : syracuseStep 201055 = 301583) B301583
theorem B201083 : Blo 199806 201083 := bstep (se 1 (by rfl) ⟨150812, by rfl⟩ : syracuseStep 201083 = 301625) B301625
theorem B201135 : Blo 199806 201135 := bstep (se 1 (by rfl) ⟨150851, by rfl⟩ : syracuseStep 201135 = 301703) B301703
theorem B201159 : Blo 199806 201159 := bstep (se 1 (by rfl) ⟨150869, by rfl⟩ : syracuseStep 201159 = 301739) B301739
theorem B201179 : Blo 199806 201179 := bstep (se 1 (by rfl) ⟨150884, by rfl⟩ : syracuseStep 201179 = 301769) B301769
theorem B201255 : Blo 199806 201255 := bstep (se 1 (by rfl) ⟨150941, by rfl⟩ : syracuseStep 201255 = 301883) B301883
theorem B201295 : Blo 199806 201295 := bstep (se 1 (by rfl) ⟨150971, by rfl⟩ : syracuseStep 201295 = 301943) B301943
theorem B201311 : Blo 199806 201311 := bstep (se 1 (by rfl) ⟨150983, by rfl⟩ : syracuseStep 201311 = 301967) B301967
theorem B201339 : Blo 199806 201339 := bstep (se 1 (by rfl) ⟨151004, by rfl⟩ : syracuseStep 201339 = 302009) B302009
theorem B201391 : Blo 199806 201391 := bstep (se 1 (by rfl) ⟨151043, by rfl⟩ : syracuseStep 201391 = 302087) B302087
theorem B201415 : Blo 199806 201415 := bstep (se 1 (by rfl) ⟨151061, by rfl⟩ : syracuseStep 201415 = 302123) B302123
theorem B3248849 : Blo 199806 3248849 := bstep (se 2 (by rfl) ⟨1218318, by rfl⟩ : syracuseStep 3248849 = 2436637) B2436637
theorem B201435 : Blo 199806 201435 := bstep (se 1 (by rfl) ⟨151076, by rfl⟩ : syracuseStep 201435 = 302153) B302153
theorem B201511 : Blo 199806 201511 := bstep (se 1 (by rfl) ⟨151133, by rfl⟩ : syracuseStep 201511 = 302267) B302267
theorem B2560841 : Blo 199806 2560841 := bstep (se 2 (by rfl) ⟨960315, by rfl⟩ : syracuseStep 2560841 = 1920631) B1920631
theorem B201551 : Blo 199806 201551 := bstep (se 1 (by rfl) ⟨151163, by rfl⟩ : syracuseStep 201551 = 302327) B302327
theorem B201567 : Blo 199806 201567 := bstep (se 1 (by rfl) ⟨151175, by rfl⟩ : syracuseStep 201567 = 302351) B302351
theorem B201595 : Blo 199806 201595 := bstep (se 1 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 201595 = 302393) B302393
theorem B2659225 : Blo 199806 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B299951 : Blo 199806 299951 := bstep (se 1 (by rfl) ⟨224963, by rfl⟩ : syracuseStep 299951 = 449927) B449927
theorem B201647 : Blo 199806 201647 := bstep (se 1 (by rfl) ⟨151235, by rfl⟩ : syracuseStep 201647 = 302471) B302471
theorem B201671 : Blo 199806 201671 := bstep (se 1 (by rfl) ⟨151253, by rfl⟩ : syracuseStep 201671 = 302507) B302507
theorem B201691 : Blo 199806 201691 := bstep (se 1 (by rfl) ⟨151268, by rfl⟩ : syracuseStep 201691 = 302537) B302537
theorem B300041 : Blo 199806 300041 := bstep (se 2 (by rfl) ⟨112515, by rfl⟩ : syracuseStep 300041 = 225031) B225031
theorem B300071 : Blo 199806 300071 := bstep (se 1 (by rfl) ⟨225053, by rfl⟩ : syracuseStep 300071 = 450107) B450107
theorem B201767 : Blo 199806 201767 := bstep (se 1 (by rfl) ⟨151325, by rfl⟩ : syracuseStep 201767 = 302651) B302651
theorem B201807 : Blo 199806 201807 := bstep (se 1 (by rfl) ⟨151355, by rfl⟩ : syracuseStep 201807 = 302711) B302711
theorem B201823 : Blo 199806 201823 := bstep (se 1 (by rfl) ⟨151367, by rfl⟩ : syracuseStep 201823 = 302735) B302735
theorem B300155 : Blo 199806 300155 := bstep (se 1 (by rfl) ⟨225116, by rfl⟩ : syracuseStep 300155 = 450233) B450233
theorem B201851 : Blo 199806 201851 := bstep (se 1 (by rfl) ⟨151388, by rfl⟩ : syracuseStep 201851 = 302777) B302777
theorem B201903 : Blo 199806 201903 := bstep (se 1 (by rfl) ⟨151427, by rfl⟩ : syracuseStep 201903 = 302855) B302855
theorem B201927 : Blo 199806 201927 := bstep (se 1 (by rfl) ⟨151445, by rfl⟩ : syracuseStep 201927 = 302891) B302891
theorem B201947 : Blo 199806 201947 := bstep (se 1 (by rfl) ⟨151460, by rfl⟩ : syracuseStep 201947 = 302921) B302921
theorem B300281 : Blo 199806 300281 := bstep (se 2 (by rfl) ⟨112605, by rfl⟩ : syracuseStep 300281 = 225211) B225211
theorem B202023 : Blo 199806 202023 := bstep (se 1 (by rfl) ⟨151517, by rfl⟩ : syracuseStep 202023 = 303035) B303035
theorem B202063 : Blo 199806 202063 := bstep (se 1 (by rfl) ⟨151547, by rfl⟩ : syracuseStep 202063 = 303095) B303095
theorem B300383 : Blo 199806 300383 := bstep (se 1 (by rfl) ⟨225287, by rfl⟩ : syracuseStep 300383 = 450575) B450575
theorem B202079 : Blo 199806 202079 := bstep (se 1 (by rfl) ⟨151559, by rfl⟩ : syracuseStep 202079 = 303119) B303119
theorem B300395 : Blo 199806 300395 := bstep (se 1 (by rfl) ⟨225296, by rfl⟩ : syracuseStep 300395 = 450593) B450593
theorem B202107 : Blo 199806 202107 := bstep (se 1 (by rfl) ⟨151580, by rfl⟩ : syracuseStep 202107 = 303161) B303161
theorem B595343 : Blo 199806 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B202159 : Blo 199806 202159 := bstep (se 1 (by rfl) ⟨151619, by rfl⟩ : syracuseStep 202159 = 303239) B303239
theorem B202183 : Blo 199806 202183 := bstep (se 1 (by rfl) ⟨151637, by rfl⟩ : syracuseStep 202183 = 303275) B303275
theorem B923081 : Blo 199806 923081 := bstep (se 2 (by rfl) ⟨346155, by rfl⟩ : syracuseStep 923081 = 692311) B692311
theorem B202203 : Blo 199806 202203 := bstep (se 1 (by rfl) ⟨151652, by rfl⟩ : syracuseStep 202203 = 303305) B303305
theorem B202279 : Blo 199806 202279 := bstep (se 1 (by rfl) ⟨151709, by rfl⟩ : syracuseStep 202279 = 303419) B303419
theorem B300623 : Blo 199806 300623 := bstep (se 1 (by rfl) ⟨225467, by rfl⟩ : syracuseStep 300623 = 450935) B450935
theorem B202319 : Blo 199806 202319 := bstep (se 1 (by rfl) ⟨151739, by rfl⟩ : syracuseStep 202319 = 303479) B303479
theorem B202335 : Blo 199806 202335 := bstep (se 1 (by rfl) ⟨151751, by rfl⟩ : syracuseStep 202335 = 303503) B303503
theorem B202363 : Blo 199806 202363 := bstep (se 1 (by rfl) ⟨151772, by rfl⟩ : syracuseStep 202363 = 303545) B303545
theorem B202415 : Blo 199806 202415 := bstep (se 1 (by rfl) ⟨151811, by rfl⟩ : syracuseStep 202415 = 303623) B303623
theorem B300743 : Blo 199806 300743 := bstep (se 1 (by rfl) ⟨225557, by rfl⟩ : syracuseStep 300743 = 451115) B451115
theorem B202439 : Blo 199806 202439 := bstep (se 1 (by rfl) ⟨151829, by rfl⟩ : syracuseStep 202439 = 303659) B303659
theorem B202459 : Blo 199806 202459 := bstep (se 1 (by rfl) ⟨151844, by rfl⟩ : syracuseStep 202459 = 303689) B303689
theorem B1545965 : Blo 199806 1545965 := bstep (se 3 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 1545965 = 579737) B579737
theorem B202535 : Blo 199806 202535 := bstep (se 1 (by rfl) ⟨151901, by rfl⟩ : syracuseStep 202535 = 303803) B303803
theorem B202575 : Blo 199806 202575 := bstep (se 1 (by rfl) ⟨151931, by rfl⟩ : syracuseStep 202575 = 303863) B303863
theorem B202591 : Blo 199806 202591 := bstep (se 1 (by rfl) ⟨151943, by rfl⟩ : syracuseStep 202591 = 303887) B303887
theorem B300905 : Blo 199806 300905 := bstep (se 2 (by rfl) ⟨112839, by rfl⟩ : syracuseStep 300905 = 225679) B225679
theorem B202619 : Blo 199806 202619 := bstep (se 1 (by rfl) ⟨151964, by rfl⟩ : syracuseStep 202619 = 303929) B303929
theorem B202671 : Blo 199806 202671 := bstep (se 1 (by rfl) ⟨152003, by rfl⟩ : syracuseStep 202671 = 304007) B304007
theorem B300983 : Blo 199806 300983 := bstep (se 1 (by rfl) ⟨225737, by rfl⟩ : syracuseStep 300983 = 451475) B451475
theorem B759739 : Blo 199806 759739 := bstep (se 1 (by rfl) ⟨569804, by rfl⟩ : syracuseStep 759739 = 1139609) B1139609
theorem B202695 : Blo 199806 202695 := bstep (se 1 (by rfl) ⟨152021, by rfl⟩ : syracuseStep 202695 = 304043) B304043
theorem B301019 : Blo 199806 301019 := bstep (se 1 (by rfl) ⟨225764, by rfl⟩ : syracuseStep 301019 = 451529) B451529
theorem B202715 : Blo 199806 202715 := bstep (se 1 (by rfl) ⟨152036, by rfl⟩ : syracuseStep 202715 = 304073) B304073
theorem B202791 : Blo 199806 202791 := bstep (se 1 (by rfl) ⟨152093, by rfl⟩ : syracuseStep 202791 = 304187) B304187
theorem B202831 : Blo 199806 202831 := bstep (se 1 (by rfl) ⟨152123, by rfl⟩ : syracuseStep 202831 = 304247) B304247
theorem B202847 : Blo 199806 202847 := bstep (se 1 (by rfl) ⟨152135, by rfl⟩ : syracuseStep 202847 = 304271) B304271
theorem B202875 : Blo 199806 202875 := bstep (se 1 (by rfl) ⟨152156, by rfl⟩ : syracuseStep 202875 = 304313) B304313
theorem B202927 : Blo 199806 202927 := bstep (se 1 (by rfl) ⟨152195, by rfl⟩ : syracuseStep 202927 = 304391) B304391
theorem B202951 : Blo 199806 202951 := bstep (se 1 (by rfl) ⟨152213, by rfl⟩ : syracuseStep 202951 = 304427) B304427
theorem B202971 : Blo 199806 202971 := bstep (se 1 (by rfl) ⟨152228, by rfl⟩ : syracuseStep 202971 = 304457) B304457
theorem B1022219 : Blo 199806 1022219 := bstep (se 1 (by rfl) ⟨766664, by rfl⟩ : syracuseStep 1022219 = 1533329) B1533329
theorem B203047 : Blo 199806 203047 := bstep (se 1 (by rfl) ⟨152285, by rfl⟩ : syracuseStep 203047 = 304571) B304571
theorem B203087 : Blo 199806 203087 := bstep (se 1 (by rfl) ⟨152315, by rfl⟩ : syracuseStep 203087 = 304631) B304631
theorem B203103 : Blo 199806 203103 := bstep (se 1 (by rfl) ⟨152327, by rfl⟩ : syracuseStep 203103 = 304655) B304655
theorem B203131 : Blo 199806 203131 := bstep (se 1 (by rfl) ⟨152348, by rfl⟩ : syracuseStep 203131 = 304697) B304697
theorem B301487 : Blo 199806 301487 := bstep (se 1 (by rfl) ⟨226115, by rfl⟩ : syracuseStep 301487 = 452231) B452231
theorem B203183 : Blo 199806 203183 := bstep (se 1 (by rfl) ⟨152387, by rfl⟩ : syracuseStep 203183 = 304775) B304775
theorem B203207 : Blo 199806 203207 := bstep (se 1 (by rfl) ⟨152405, by rfl⟩ : syracuseStep 203207 = 304811) B304811
theorem B203227 : Blo 199806 203227 := bstep (se 1 (by rfl) ⟨152420, by rfl⟩ : syracuseStep 203227 = 304841) B304841
theorem B301577 : Blo 199806 301577 := bstep (se 2 (by rfl) ⟨113091, by rfl⟩ : syracuseStep 301577 = 226183) B226183
theorem B1219097 : Blo 199806 1219097 := bstep (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) B914323
theorem B301607 : Blo 199806 301607 := bstep (se 1 (by rfl) ⟨226205, by rfl⟩ : syracuseStep 301607 = 452411) B452411
theorem B203303 : Blo 199806 203303 := bstep (se 1 (by rfl) ⟨152477, by rfl⟩ : syracuseStep 203303 = 304955) B304955
theorem B203343 : Blo 199806 203343 := bstep (se 1 (by rfl) ⟨152507, by rfl⟩ : syracuseStep 203343 = 305015) B305015
theorem B367183 : Blo 199806 367183 := bstep (se 1 (by rfl) ⟨275387, by rfl⟩ : syracuseStep 367183 = 550775) B550775
theorem B203359 : Blo 199806 203359 := bstep (se 1 (by rfl) ⟨152519, by rfl⟩ : syracuseStep 203359 = 305039) B305039
theorem B727649 : Blo 199806 727649 := bstep (se 2 (by rfl) ⟨272868, by rfl⟩ : syracuseStep 727649 = 545737) B545737
theorem B301691 : Blo 199806 301691 := bstep (se 1 (by rfl) ⟨226268, by rfl⟩ : syracuseStep 301691 = 452537) B452537
theorem B203387 : Blo 199806 203387 := bstep (se 1 (by rfl) ⟨152540, by rfl⟩ : syracuseStep 203387 = 305081) B305081
theorem B203439 : Blo 199806 203439 := bstep (se 1 (by rfl) ⟨152579, by rfl⟩ : syracuseStep 203439 = 305159) B305159
theorem B1546937 : Blo 199806 1546937 := bstep (se 2 (by rfl) ⟨580101, by rfl⟩ : syracuseStep 1546937 = 1160203) B1160203
theorem B432839 : Blo 199806 432839 := bstep (se 1 (by rfl) ⟨324629, by rfl⟩ : syracuseStep 432839 = 649259) B649259
theorem B203463 : Blo 199806 203463 := bstep (se 1 (by rfl) ⟨152597, by rfl⟩ : syracuseStep 203463 = 305195) B305195
theorem B760529 : Blo 199806 760529 := bstep (se 2 (by rfl) ⟨285198, by rfl⟩ : syracuseStep 760529 = 570397) B570397
theorem B203483 : Blo 199806 203483 := bstep (se 1 (by rfl) ⟨152612, by rfl⟩ : syracuseStep 203483 = 305225) B305225
theorem B301817 : Blo 199806 301817 := bstep (se 2 (by rfl) ⟨113181, by rfl⟩ : syracuseStep 301817 = 226363) B226363
theorem B203559 : Blo 199806 203559 := bstep (se 1 (by rfl) ⟨152669, by rfl⟩ : syracuseStep 203559 = 305339) B305339
theorem B203599 : Blo 199806 203599 := bstep (se 1 (by rfl) ⟨152699, by rfl⟩ : syracuseStep 203599 = 305399) B305399
theorem B301919 : Blo 199806 301919 := bstep (se 1 (by rfl) ⟨226439, by rfl⟩ : syracuseStep 301919 = 452879) B452879
theorem B203615 : Blo 199806 203615 := bstep (se 1 (by rfl) ⟨152711, by rfl⟩ : syracuseStep 203615 = 305423) B305423
theorem B301931 : Blo 199806 301931 := bstep (se 1 (by rfl) ⟨226448, by rfl⟩ : syracuseStep 301931 = 452897) B452897
theorem B203643 : Blo 199806 203643 := bstep (se 1 (by rfl) ⟨152732, by rfl⟩ : syracuseStep 203643 = 305465) B305465
theorem B203695 : Blo 199806 203695 := bstep (se 1 (by rfl) ⟨152771, by rfl⟩ : syracuseStep 203695 = 305543) B305543
theorem B203719 : Blo 199806 203719 := bstep (se 1 (by rfl) ⟨152789, by rfl⟩ : syracuseStep 203719 = 305579) B305579
theorem B203739 : Blo 199806 203739 := bstep (se 1 (by rfl) ⟨152804, by rfl⟩ : syracuseStep 203739 = 305609) B305609
theorem B924691 : Blo 199806 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B302159 : Blo 199806 302159 := bstep (se 1 (by rfl) ⟨226619, by rfl⟩ : syracuseStep 302159 = 453239) B453239
theorem B760985 : Blo 199806 760985 := bstep (se 2 (by rfl) ⟨285369, by rfl⟩ : syracuseStep 760985 = 570739) B570739
theorem B302279 : Blo 199806 302279 := bstep (se 1 (by rfl) ⟨226709, by rfl⟩ : syracuseStep 302279 = 453419) B453419
theorem B203995 : Blo 199806 203995 := bstep (se 1 (by rfl) ⟨152996, by rfl⟩ : syracuseStep 203995 = 305993) B305993
theorem B302441 : Blo 199806 302441 := bstep (se 2 (by rfl) ⟨113415, by rfl⟩ : syracuseStep 302441 = 226831) B226831
theorem B302519 : Blo 199806 302519 := bstep (se 1 (by rfl) ⟨226889, by rfl⟩ : syracuseStep 302519 = 453779) B453779
theorem B302555 : Blo 199806 302555 := bstep (se 1 (by rfl) ⟨226916, by rfl⟩ : syracuseStep 302555 = 453833) B453833
theorem B1023677 : Blo 199806 1023677 := bstep (se 3 (by rfl) ⟨191939, by rfl⟩ : syracuseStep 1023677 = 383879) B383879
theorem B1023839 : Blo 199806 1023839 := bstep (se 1 (by rfl) ⟨767879, by rfl⟩ : syracuseStep 1023839 = 1535759) B1535759
theorem B303023 : Blo 199806 303023 := bstep (se 1 (by rfl) ⟨227267, by rfl⟩ : syracuseStep 303023 = 454535) B454535
theorem B303113 : Blo 199806 303113 := bstep (se 2 (by rfl) ⟨113667, by rfl⟩ : syracuseStep 303113 = 227335) B227335
theorem B3416093 : Blo 199806 3416093 := bstep (se 3 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 3416093 = 1281035) B1281035
theorem B303143 : Blo 199806 303143 := bstep (se 1 (by rfl) ⟨227357, by rfl⟩ : syracuseStep 303143 = 454715) B454715
theorem B303227 : Blo 199806 303227 := bstep (se 1 (by rfl) ⟨227420, by rfl⟩ : syracuseStep 303227 = 454841) B454841
theorem B2072753 : Blo 199806 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B2302181 : Blo 199806 2302181 := bstep (se 4 (by rfl) ⟨215829, by rfl⟩ : syracuseStep 2302181 = 431659) B431659
theorem B303353 : Blo 199806 303353 := bstep (se 2 (by rfl) ⟨113757, by rfl⟩ : syracuseStep 303353 = 227515) B227515
theorem B303455 : Blo 199806 303455 := bstep (se 1 (by rfl) ⟨227591, by rfl⟩ : syracuseStep 303455 = 455183) B455183
theorem B303467 : Blo 199806 303467 := bstep (se 1 (by rfl) ⟨227600, by rfl⟩ : syracuseStep 303467 = 455201) B455201
theorem B1712663 : Blo 199806 1712663 := bstep (se 1 (by rfl) ⟨1284497, by rfl⟩ : syracuseStep 1712663 = 2568995) B2568995
theorem B303695 : Blo 199806 303695 := bstep (se 1 (by rfl) ⟨227771, by rfl⟩ : syracuseStep 303695 = 455543) B455543
theorem B303815 : Blo 199806 303815 := bstep (se 1 (by rfl) ⟨227861, by rfl⟩ : syracuseStep 303815 = 455723) B455723
theorem B303977 : Blo 199806 303977 := bstep (se 2 (by rfl) ⟨113991, by rfl⟩ : syracuseStep 303977 = 227983) B227983
theorem B304055 : Blo 199806 304055 := bstep (se 1 (by rfl) ⟨228041, by rfl⟩ : syracuseStep 304055 = 456083) B456083
theorem B304091 : Blo 199806 304091 := bstep (se 1 (by rfl) ⟨228068, by rfl⟩ : syracuseStep 304091 = 456137) B456137
theorem B762959 : Blo 199806 762959 := bstep (se 1 (by rfl) ⟨572219, by rfl⟩ : syracuseStep 762959 = 1144439) B1144439
theorem B763127 : Blo 199806 763127 := bstep (se 1 (by rfl) ⟨572345, by rfl⟩ : syracuseStep 763127 = 1144691) B1144691
theorem B304559 : Blo 199806 304559 := bstep (se 1 (by rfl) ⟨228419, by rfl⟩ : syracuseStep 304559 = 456839) B456839
theorem B304649 : Blo 199806 304649 := bstep (se 2 (by rfl) ⟨114243, by rfl⟩ : syracuseStep 304649 = 228487) B228487
theorem B304679 : Blo 199806 304679 := bstep (se 1 (by rfl) ⟨228509, by rfl⟩ : syracuseStep 304679 = 457019) B457019
theorem B730721 : Blo 199806 730721 := bstep (se 2 (by rfl) ⟨274020, by rfl⟩ : syracuseStep 730721 = 548041) B548041
theorem B304763 : Blo 199806 304763 := bstep (se 1 (by rfl) ⟨228572, by rfl⟩ : syracuseStep 304763 = 457145) B457145
theorem B730835 : Blo 199806 730835 := bstep (se 1 (by rfl) ⟨548126, by rfl⟩ : syracuseStep 730835 = 1096253) B1096253
theorem B337655 : Blo 199806 337655 := bstep (se 1 (by rfl) ⟨253241, by rfl⟩ : syracuseStep 337655 = 506483) B506483
theorem B304889 : Blo 199806 304889 := bstep (se 2 (by rfl) ⟨114333, by rfl⟩ : syracuseStep 304889 = 228667) B228667
theorem B960299 : Blo 199806 960299 := bstep (se 1 (by rfl) ⟨720224, by rfl⟩ : syracuseStep 960299 = 1440449) B1440449
theorem B304991 : Blo 199806 304991 := bstep (se 1 (by rfl) ⟨228743, by rfl⟩ : syracuseStep 304991 = 457487) B457487
theorem B305003 : Blo 199806 305003 := bstep (se 1 (by rfl) ⟨228752, by rfl⟩ : syracuseStep 305003 = 457505) B457505
theorem B337999 : Blo 199806 337999 := bstep (se 1 (by rfl) ⟨253499, by rfl⟩ : syracuseStep 337999 = 506999) B506999
theorem B305231 : Blo 199806 305231 := bstep (se 1 (by rfl) ⟨228923, by rfl⟩ : syracuseStep 305231 = 457847) B457847
theorem B305275 : Blo 199806 305275 := bstep (se 1 (by rfl) ⟨228956, by rfl⟩ : syracuseStep 305275 = 457913) B457913
theorem B764099 : Blo 199806 764099 := bstep (se 1 (by rfl) ⟨573074, by rfl⟩ : syracuseStep 764099 = 1146149) B1146149
theorem B305351 : Blo 199806 305351 := bstep (se 1 (by rfl) ⟨229013, by rfl⟩ : syracuseStep 305351 = 458027) B458027
theorem B338249 : Blo 199806 338249 := bstep (se 2 (by rfl) ⟨126843, by rfl⟩ : syracuseStep 338249 = 253687) B253687
theorem B305513 : Blo 199806 305513 := bstep (se 2 (by rfl) ⟨114567, by rfl⟩ : syracuseStep 305513 = 229135) B229135
theorem B305591 : Blo 199806 305591 := bstep (se 1 (by rfl) ⟨229193, by rfl⟩ : syracuseStep 305591 = 458387) B458387
theorem B305627 : Blo 199806 305627 := bstep (se 1 (by rfl) ⟨229220, by rfl⟩ : syracuseStep 305627 = 458441) B458441
theorem B1026593 : Blo 199806 1026593 := bstep (se 2 (by rfl) ⟨384972, by rfl⟩ : syracuseStep 1026593 = 769945) B769945
theorem B928465 : Blo 199806 928465 := bstep (se 2 (by rfl) ⟨348174, by rfl⟩ : syracuseStep 928465 = 696349) B696349
theorem B338681 : Blo 199806 338681 := bstep (se 2 (by rfl) ⟨127005, by rfl⟩ : syracuseStep 338681 = 254011) B254011
theorem B1289033 : Blo 199806 1289033 := bstep (se 2 (by rfl) ⟨483387, by rfl⟩ : syracuseStep 1289033 = 966775) B966775
theorem B338863 : Blo 199806 338863 := bstep (se 1 (by rfl) ⟨254147, by rfl⟩ : syracuseStep 338863 = 508295) B508295
theorem B1289135 : Blo 199806 1289135 := bstep (se 1 (by rfl) ⟨966851, by rfl⟩ : syracuseStep 1289135 = 1933703) B1933703
theorem B338951 : Blo 199806 338951 := bstep (se 1 (by rfl) ⟨254213, by rfl⟩ : syracuseStep 338951 = 508427) B508427
theorem B928921 : Blo 199806 928921 := bstep (se 2 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 928921 = 696691) B696691
theorem B765085 : Blo 199806 765085 := bstep (se 3 (by rfl) ⟨143453, by rfl⟩ : syracuseStep 765085 = 286907) B286907
theorem B339295 : Blo 199806 339295 := bstep (se 1 (by rfl) ⟨254471, by rfl⟩ : syracuseStep 339295 = 508943) B508943
theorem B339383 : Blo 199806 339383 := bstep (se 1 (by rfl) ⟨254537, by rfl⟩ : syracuseStep 339383 = 509075) B509075
theorem B339977 : Blo 199806 339977 := bstep (se 2 (by rfl) ⟨127491, by rfl⟩ : syracuseStep 339977 = 254983) B254983
theorem B634895 : Blo 199806 634895 := bstep (se 1 (by rfl) ⟨476171, by rfl⟩ : syracuseStep 634895 = 952343) B952343
theorem B5156945 : Blo 199806 5156945 := bstep (se 2 (by rfl) ⟨1933854, by rfl⟩ : syracuseStep 5156945 = 3867709) B3867709
theorem B340139 : Blo 199806 340139 := bstep (se 1 (by rfl) ⟨255104, by rfl⟩ : syracuseStep 340139 = 510209) B510209
theorem B438443 : Blo 199806 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B3649853 : Blo 199806 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B1290775 : Blo 199806 1290775 := bstep (se 1 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 1290775 = 1936163) B1936163
theorem B340537 : Blo 199806 340537 := bstep (se 2 (by rfl) ⟨127701, by rfl⟩ : syracuseStep 340537 = 255403) B255403
theorem B340679 : Blo 199806 340679 := bstep (se 1 (by rfl) ⟨255509, by rfl⟩ : syracuseStep 340679 = 511019) B511019
theorem B10138385 : Blo 199806 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B4371245 : Blo 199806 4371245 := bstep (se 3 (by rfl) ⟨819608, by rfl⟩ : syracuseStep 4371245 = 1639217) B1639217
theorem B340841 : Blo 199806 340841 := bstep (se 2 (by rfl) ⟨127815, by rfl⟩ : syracuseStep 340841 = 255631) B255631
theorem B406433 : Blo 199806 406433 := bstep (se 2 (by rfl) ⟨152412, by rfl⟩ : syracuseStep 406433 = 304825) B304825
theorem B341239 : Blo 199806 341239 := bstep (se 1 (by rfl) ⟨255929, by rfl⟩ : syracuseStep 341239 = 511859) B511859
theorem B734525 : Blo 199806 734525 := bstep (se 3 (by rfl) ⟨137723, by rfl⟩ : syracuseStep 734525 = 275447) B275447
theorem B341435 : Blo 199806 341435 := bstep (se 1 (by rfl) ⟨256076, by rfl⟩ : syracuseStep 341435 = 512153) B512153
theorem B341543 : Blo 199806 341543 := bstep (se 1 (by rfl) ⟨256157, by rfl⟩ : syracuseStep 341543 = 512315) B512315
theorem B1029671 : Blo 199806 1029671 := bstep (se 1 (by rfl) ⟨772253, by rfl⟩ : syracuseStep 1029671 = 1544507) B1544507
theorem B603863 : Blo 199806 603863 := bstep (se 1 (by rfl) ⟨452897, by rfl⟩ : syracuseStep 603863 = 905795) B905795
theorem B341833 : Blo 199806 341833 := bstep (se 2 (by rfl) ⟨128187, by rfl⟩ : syracuseStep 341833 = 256375) B256375
theorem B341867 : Blo 199806 341867 := bstep (se 1 (by rfl) ⟨256400, by rfl⟩ : syracuseStep 341867 = 512801) B512801
theorem B768001 : Blo 199806 768001 := bstep (se 2 (by rfl) ⟨288000, by rfl⟩ : syracuseStep 768001 = 576001) B576001
theorem B506027 : Blo 199806 506027 := bstep (se 1 (by rfl) ⟨379520, by rfl⟩ : syracuseStep 506027 = 759041) B759041
theorem B342265 : Blo 199806 342265 := bstep (se 2 (by rfl) ⟨128349, by rfl⟩ : syracuseStep 342265 = 256699) B256699
theorem B26589505 : Blo 199806 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B342535 : Blo 199806 342535 := bstep (se 1 (by rfl) ⟨256901, by rfl⟩ : syracuseStep 342535 = 513803) B513803
theorem B3291677 : Blo 199806 3291677 := bstep (se 3 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 3291677 = 1234379) B1234379
theorem B244423 : Blo 199806 244423 := bstep (se 1 (by rfl) ⟨183317, by rfl⟩ : syracuseStep 244423 = 366635) B366635
theorem B768761 : Blo 199806 768761 := bstep (se 2 (by rfl) ⟨288285, by rfl⟩ : syracuseStep 768761 = 576571) B576571
theorem B572255 : Blo 199806 572255 := bstep (se 1 (by rfl) ⟨429191, by rfl⟩ : syracuseStep 572255 = 858383) B858383
theorem B1555307 : Blo 199806 1555307 := bstep (se 1 (by rfl) ⟨1166480, by rfl⟩ : syracuseStep 1555307 = 2332961) B2332961
theorem B506807 : Blo 199806 506807 := bstep (se 1 (by rfl) ⟨380105, by rfl⟩ : syracuseStep 506807 = 760211) B760211
theorem B342967 : Blo 199806 342967 := bstep (se 1 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 342967 = 514451) B514451
theorem B343163 : Blo 199806 343163 := bstep (se 1 (by rfl) ⟨257372, by rfl⟩ : syracuseStep 343163 = 514745) B514745
theorem B343561 : Blo 199806 343561 := bstep (se 2 (by rfl) ⟨128835, by rfl⟩ : syracuseStep 343561 = 257671) B257671
theorem B343723 : Blo 199806 343723 := bstep (se 1 (by rfl) ⟨257792, by rfl⟩ : syracuseStep 343723 = 515585) B515585
theorem B966467 : Blo 199806 966467 := bstep (se 1 (by rfl) ⟨724850, by rfl⟩ : syracuseStep 966467 = 1449701) B1449701
theorem B1949507 : Blo 199806 1949507 := bstep (se 1 (by rfl) ⟨1462130, by rfl⟩ : syracuseStep 1949507 = 2924261) B2924261
theorem B573257 : Blo 199806 573257 := bstep (se 2 (by rfl) ⟨214971, by rfl⟩ : syracuseStep 573257 = 429943) B429943
theorem B507809 : Blo 199806 507809 := bstep (se 2 (by rfl) ⟨190428, by rfl⟩ : syracuseStep 507809 = 380857) B380857
theorem B1294339 : Blo 199806 1294339 := bstep (se 1 (by rfl) ⟨970754, by rfl⟩ : syracuseStep 1294339 = 1941509) B1941509
theorem B1720349 : Blo 199806 1720349 := bstep (se 3 (by rfl) ⟨322565, by rfl⟩ : syracuseStep 1720349 = 645131) B645131
theorem B770219 : Blo 199806 770219 := bstep (se 1 (by rfl) ⟨577664, by rfl⟩ : syracuseStep 770219 = 1155329) B1155329
theorem B508265 : Blo 199806 508265 := bstep (se 2 (by rfl) ⟨190599, by rfl⟩ : syracuseStep 508265 = 381199) B381199
theorem B311771 : Blo 199806 311771 := bstep (se 1 (by rfl) ⟨233828, by rfl⟩ : syracuseStep 311771 = 467657) B467657
theorem B5653111 : Blo 199806 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B2310929 : Blo 199806 2310929 := bstep (se 2 (by rfl) ⟨866598, by rfl⟩ : syracuseStep 2310929 = 1733197) B1733197
theorem B2933657 : Blo 199806 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B771079 : Blo 199806 771079 := bstep (se 1 (by rfl) ⟨578309, by rfl⟩ : syracuseStep 771079 = 1156619) B1156619
theorem B1721411 : Blo 199806 1721411 := bstep (se 1 (by rfl) ⟨1291058, by rfl⟩ : syracuseStep 1721411 = 2582117) B2582117
theorem B574543 : Blo 199806 574543 := bstep (se 1 (by rfl) ⟨430907, by rfl⟩ : syracuseStep 574543 = 861815) B861815
theorem B771389 : Blo 199806 771389 := bstep (se 3 (by rfl) ⟨144635, by rfl⟩ : syracuseStep 771389 = 289271) B289271
theorem B509449 : Blo 199806 509449 := bstep (se 2 (by rfl) ⟨191043, by rfl⟩ : syracuseStep 509449 = 382087) B382087
theorem B214651 : Blo 199806 214651 := bstep (se 1 (by rfl) ⟨160988, by rfl⟩ : syracuseStep 214651 = 321977) B321977
theorem B771707 : Blo 199806 771707 := bstep (se 1 (by rfl) ⟨578780, by rfl⟩ : syracuseStep 771707 = 1157561) B1157561
theorem B640723 : Blo 199806 640723 := bstep (se 1 (by rfl) ⟨480542, by rfl⟩ : syracuseStep 640723 = 961085) B961085
theorem B215471 : Blo 199806 215471 := bstep (se 1 (by rfl) ⟨161603, by rfl⟩ : syracuseStep 215471 = 323207) B323207
theorem B379399 : Blo 199806 379399 := bstep (se 1 (by rfl) ⟨284549, by rfl⟩ : syracuseStep 379399 = 569099) B569099
theorem B641953 : Blo 199806 641953 := bstep (se 2 (by rfl) ⟨240732, by rfl⟩ : syracuseStep 641953 = 481465) B481465
theorem B510907 : Blo 199806 510907 := bstep (se 1 (by rfl) ⟨383180, by rfl⟩ : syracuseStep 510907 = 766361) B766361
theorem B773135 : Blo 199806 773135 := bstep (se 1 (by rfl) ⟨579851, by rfl⟩ : syracuseStep 773135 = 1159703) B1159703
theorem B379961 : Blo 199806 379961 := bstep (se 2 (by rfl) ⟨142485, by rfl⟩ : syracuseStep 379961 = 284971) B284971
theorem B675215 : Blo 199806 675215 := bstep (se 1 (by rfl) ⟨506411, by rfl⟩ : syracuseStep 675215 = 1012823) B1012823
theorem B970157 : Blo 199806 970157 := bstep (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) B363809
theorem B544243 : Blo 199806 544243 := bstep (se 1 (by rfl) ⟨408182, by rfl⟩ : syracuseStep 544243 = 816365) B816365
theorem B675539 : Blo 199806 675539 := bstep (se 1 (by rfl) ⟨506654, by rfl⟩ : syracuseStep 675539 = 1013309) B1013309
theorem B2772751 : Blo 199806 2772751 := bstep (se 1 (by rfl) ⟨2079563, by rfl⟩ : syracuseStep 2772751 = 4159127) B4159127
theorem B347977 : Blo 199806 347977 := bstep (se 2 (by rfl) ⟨130491, by rfl⟩ : syracuseStep 347977 = 260983) B260983
theorem B381449 : Blo 199806 381449 := bstep (se 2 (by rfl) ⟨143043, by rfl⟩ : syracuseStep 381449 = 286087) B286087
theorem B578087 : Blo 199806 578087 := bstep (se 1 (by rfl) ⟨433565, by rfl⟩ : syracuseStep 578087 = 867131) B867131
theorem B676727 : Blo 199806 676727 := bstep (se 1 (by rfl) ⟨507545, by rfl⟩ : syracuseStep 676727 = 1015091) B1015091
theorem B3724289 : Blo 199806 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B480275 : Blo 199806 480275 := bstep (se 1 (by rfl) ⟨360206, by rfl⟩ : syracuseStep 480275 = 720413) B720413
theorem B676943 : Blo 199806 676943 := bstep (se 1 (by rfl) ⟨507707, by rfl⟩ : syracuseStep 676943 = 1015415) B1015415
theorem B4871339 : Blo 199806 4871339 := bstep (se 1 (by rfl) ⟨3653504, by rfl⟩ : syracuseStep 4871339 = 7307009) B7307009
theorem B2577653 : Blo 199806 2577653 := bstep (se 5 (by rfl) ⟨120827, by rfl⟩ : syracuseStep 2577653 = 241655) B241655
theorem B382315 : Blo 199806 382315 := bstep (se 1 (by rfl) ⟨286736, by rfl⟩ : syracuseStep 382315 = 573473) B573473
theorem B382391 : Blo 199806 382391 := bstep (se 1 (by rfl) ⟨286793, by rfl⟩ : syracuseStep 382391 = 573587) B573587
theorem B677321 : Blo 199806 677321 := bstep (se 2 (by rfl) ⟨253995, by rfl⟩ : syracuseStep 677321 = 507991) B507991
theorem B1856969 : Blo 199806 1856969 := bstep (se 2 (by rfl) ⟨696363, by rfl⟩ : syracuseStep 1856969 = 1392727) B1392727
theorem B513499 : Blo 199806 513499 := bstep (se 1 (by rfl) ⟨385124, by rfl⟩ : syracuseStep 513499 = 770249) B770249
theorem B1463771 : Blo 199806 1463771 := bstep (se 1 (by rfl) ⟨1097828, by rfl⟩ : syracuseStep 1463771 = 2195657) B2195657
theorem B579059 : Blo 199806 579059 := bstep (se 1 (by rfl) ⟨434294, by rfl⟩ : syracuseStep 579059 = 868589) B868589
theorem B1529441 : Blo 199806 1529441 := bstep (se 2 (by rfl) ⟨573540, by rfl⟩ : syracuseStep 1529441 = 1147081) B1147081
theorem B1300157 : Blo 199806 1300157 := bstep (se 3 (by rfl) ⟨243779, by rfl⟩ : syracuseStep 1300157 = 487559) B487559
theorem B579271 : Blo 199806 579271 := bstep (se 1 (by rfl) ⟨434453, by rfl⟩ : syracuseStep 579271 = 868907) B868907
theorem B677591 : Blo 199806 677591 := bstep (se 1 (by rfl) ⟨508193, by rfl⟩ : syracuseStep 677591 = 1016387) B1016387
theorem B2185019 : Blo 199806 2185019 := bstep (se 1 (by rfl) ⟨1638764, by rfl⟩ : syracuseStep 2185019 = 3277529) B3277529
theorem B677807 : Blo 199806 677807 := bstep (se 1 (by rfl) ⟨508355, by rfl⟩ : syracuseStep 677807 = 1016711) B1016711
theorem B546743 : Blo 199806 546743 := bstep (se 1 (by rfl) ⟨410057, by rfl⟩ : syracuseStep 546743 = 820115) B820115
theorem B382907 : Blo 199806 382907 := bstep (se 1 (by rfl) ⟨287180, by rfl⟩ : syracuseStep 382907 = 574361) B574361
theorem B514127 : Blo 199806 514127 := bstep (se 1 (by rfl) ⟨385595, by rfl⟩ : syracuseStep 514127 = 771191) B771191
theorem B383393 : Blo 199806 383393 := bstep (se 2 (by rfl) ⟨143772, by rfl⟩ : syracuseStep 383393 = 287545) B287545
theorem B645671 : Blo 199806 645671 := bstep (se 1 (by rfl) ⟨484253, by rfl⟩ : syracuseStep 645671 = 968507) B968507
theorem B383545 : Blo 199806 383545 := bstep (se 2 (by rfl) ⟨143829, by rfl⟩ : syracuseStep 383545 = 287659) B287659
theorem B481889 : Blo 199806 481889 := bstep (se 2 (by rfl) ⟨180708, by rfl⟩ : syracuseStep 481889 = 361417) B361417
theorem B580193 : Blo 199806 580193 := bstep (se 2 (by rfl) ⟨217572, by rfl⟩ : syracuseStep 580193 = 435145) B435145
theorem B514775 : Blo 199806 514775 := bstep (se 1 (by rfl) ⟨386081, by rfl⟩ : syracuseStep 514775 = 772163) B772163
theorem B285535 : Blo 199806 285535 := bstep (se 1 (by rfl) ⟨214151, by rfl⟩ : syracuseStep 285535 = 428303) B428303
theorem B383849 : Blo 199806 383849 := bstep (se 2 (by rfl) ⟨143943, by rfl⟩ : syracuseStep 383849 = 287887) B287887
theorem B482311 : Blo 199806 482311 := bstep (se 1 (by rfl) ⟨361733, by rfl⟩ : syracuseStep 482311 = 723467) B723467
theorem B1530899 : Blo 199806 1530899 := bstep (se 1 (by rfl) ⟨1148174, by rfl⟩ : syracuseStep 1530899 = 2296349) B2296349
theorem B1629233 : Blo 199806 1629233 := bstep (se 2 (by rfl) ⟨610962, by rfl⟩ : syracuseStep 1629233 = 1221925) B1221925
theorem B810137 : Blo 199806 810137 := bstep (se 2 (by rfl) ⟨303801, by rfl⟩ : syracuseStep 810137 = 607603) B607603
theorem B449783 : Blo 199806 449783 := bstep (se 1 (by rfl) ⟨337337, by rfl⟩ : syracuseStep 449783 = 674675) B674675
theorem B1302155 : Blo 199806 1302155 := bstep (se 1 (by rfl) ⟨976616, by rfl⟩ : syracuseStep 1302155 = 1953233) B1953233
theorem B810643 : Blo 199806 810643 := bstep (se 1 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 810643 = 1215965) B1215965
theorem B450377 : Blo 199806 450377 := bstep (se 2 (by rfl) ⟨168891, by rfl⟩ : syracuseStep 450377 = 337783) B337783
theorem B680183 : Blo 199806 680183 := bstep (se 1 (by rfl) ⟨510137, by rfl⟩ : syracuseStep 680183 = 1020275) B1020275
theorem B680507 : Blo 199806 680507 := bstep (se 1 (by rfl) ⟨510380, by rfl⟩ : syracuseStep 680507 = 1020761) B1020761
theorem B451169 : Blo 199806 451169 := bstep (se 2 (by rfl) ⟨169188, by rfl⟩ : syracuseStep 451169 = 338377) B338377
theorem B680777 : Blo 199806 680777 := bstep (se 2 (by rfl) ⟨255291, by rfl⟩ : syracuseStep 680777 = 510583) B510583
theorem B451511 : Blo 199806 451511 := bstep (se 1 (by rfl) ⟨338633, by rfl⟩ : syracuseStep 451511 = 677267) B677267
theorem B385975 : Blo 199806 385975 := bstep (se 1 (by rfl) ⟨289481, by rfl⟩ : syracuseStep 385975 = 578963) B578963
theorem B1139791 : Blo 199806 1139791 := bstep (se 1 (by rfl) ⟨854843, by rfl⟩ : syracuseStep 1139791 = 1709687) B1709687
theorem B976151 : Blo 199806 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B1303897 : Blo 199806 1303897 := bstep (se 2 (by rfl) ⟨488961, by rfl⟩ : syracuseStep 1303897 = 977923) B977923
theorem B452105 : Blo 199806 452105 := bstep (se 2 (by rfl) ⟨169539, by rfl⟩ : syracuseStep 452105 = 339079) B339079
theorem B17360405 : Blo 199806 17360405 := bstep (se 6 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 17360405 = 813769) B813769
theorem B452447 : Blo 199806 452447 := bstep (se 1 (by rfl) ⟨339335, by rfl⟩ : syracuseStep 452447 = 678671) B678671
theorem B1533815 : Blo 199806 1533815 := bstep (se 1 (by rfl) ⟨1150361, by rfl⟩ : syracuseStep 1533815 = 2300723) B2300723
theorem B649079 : Blo 199806 649079 := bstep (se 1 (by rfl) ⟨486809, by rfl⟩ : syracuseStep 649079 = 973619) B973619
theorem B681911 : Blo 199806 681911 := bstep (se 1 (by rfl) ⟨511433, by rfl⟩ : syracuseStep 681911 = 1022867) B1022867
theorem B452627 : Blo 199806 452627 := bstep (se 1 (by rfl) ⟨339470, by rfl⟩ : syracuseStep 452627 = 678941) B678941
theorem B3107159 : Blo 199806 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B452969 : Blo 199806 452969 := bstep (se 2 (by rfl) ⟨169863, by rfl⟩ : syracuseStep 452969 = 339727) B339727
theorem B321899 : Blo 199806 321899 := bstep (se 1 (by rfl) ⟨241424, by rfl⟩ : syracuseStep 321899 = 482849) B482849
theorem B682505 : Blo 199806 682505 := bstep (se 2 (by rfl) ⟨255939, by rfl⟩ : syracuseStep 682505 = 511879) B511879
theorem B4123169 : Blo 199806 4123169 := bstep (se 2 (by rfl) ⟨1546188, by rfl⟩ : syracuseStep 4123169 = 3092377) B3092377
theorem B780947 : Blo 199806 780947 := bstep (se 1 (by rfl) ⟨585710, by rfl⟩ : syracuseStep 780947 = 1171421) B1171421
theorem B977771 : Blo 199806 977771 := bstep (se 1 (by rfl) ⟨733328, by rfl⟩ : syracuseStep 977771 = 1466657) B1466657
theorem B453563 : Blo 199806 453563 := bstep (se 1 (by rfl) ⟨340172, by rfl⟩ : syracuseStep 453563 = 680345) B680345
theorem B1731557 : Blo 199806 1731557 := bstep (se 4 (by rfl) ⟨162333, by rfl⟩ : syracuseStep 1731557 = 324667) B324667
theorem B453689 : Blo 199806 453689 := bstep (se 2 (by rfl) ⟨170133, by rfl⟩ : syracuseStep 453689 = 340267) B340267
theorem B977999 : Blo 199806 977999 := bstep (se 1 (by rfl) ⟨733499, by rfl⟩ : syracuseStep 977999 = 1466999) B1466999
theorem B781427 : Blo 199806 781427 := bstep (se 1 (by rfl) ⟨586070, by rfl⟩ : syracuseStep 781427 = 1172141) B1172141
theorem B3468581 : Blo 199806 3468581 := bstep (se 4 (by rfl) ⟨325179, by rfl⟩ : syracuseStep 3468581 = 650359) B650359
theorem B683369 : Blo 199806 683369 := bstep (se 2 (by rfl) ⟨256263, by rfl⟩ : syracuseStep 683369 = 512527) B512527
theorem B454031 : Blo 199806 454031 := bstep (se 1 (by rfl) ⟨340523, by rfl⟩ : syracuseStep 454031 = 681047) B681047
theorem B257575 : Blo 199806 257575 := bstep (se 1 (by rfl) ⟨193181, by rfl⟩ : syracuseStep 257575 = 386363) B386363
theorem B913085 : Blo 199806 913085 := bstep (se 3 (by rfl) ⟨171203, by rfl⟩ : syracuseStep 913085 = 342407) B342407
theorem B454355 : Blo 199806 454355 := bstep (se 1 (by rfl) ⟨340766, by rfl⟩ : syracuseStep 454355 = 681533) B681533
theorem B257899 : Blo 199806 257899 := bstep (se 1 (by rfl) ⟨193424, by rfl⟩ : syracuseStep 257899 = 386849) B386849
theorem B683963 : Blo 199806 683963 := bstep (se 1 (by rfl) ⟨512972, by rfl⟩ : syracuseStep 683963 = 1025945) B1025945
theorem B225319 : Blo 199806 225319 := bstep (se 1 (by rfl) ⟨168989, by rfl⟩ : syracuseStep 225319 = 337979) B337979
theorem B455291 : Blo 199806 455291 := bstep (se 1 (by rfl) ⟨341468, by rfl⟩ : syracuseStep 455291 = 682937) B682937
theorem B455417 : Blo 199806 455417 := bstep (se 2 (by rfl) ⟨170781, by rfl⟩ : syracuseStep 455417 = 341563) B341563
theorem B455687 : Blo 199806 455687 := bstep (se 1 (by rfl) ⟨341765, by rfl⟩ : syracuseStep 455687 = 683531) B683531
theorem B455759 : Blo 199806 455759 := bstep (se 1 (by rfl) ⟨341819, by rfl⟩ : syracuseStep 455759 = 683639) B683639
theorem B1537217 : Blo 199806 1537217 := bstep (se 2 (by rfl) ⟨576456, by rfl⟩ : syracuseStep 1537217 = 1152913) B1152913
theorem B456155 : Blo 199806 456155 := bstep (se 1 (by rfl) ⟨342116, by rfl⟩ : syracuseStep 456155 = 684233) B684233
theorem B325129 : Blo 199806 325129 := bstep (se 2 (by rfl) ⟨121923, by rfl⟩ : syracuseStep 325129 = 243847) B243847
theorem B1734155 : Blo 199806 1734155 := bstep (se 1 (by rfl) ⟨1300616, by rfl⟩ : syracuseStep 1734155 = 2601233) B2601233
theorem B685691 : Blo 199806 685691 := bstep (se 1 (by rfl) ⟨514268, by rfl⟩ : syracuseStep 685691 = 1028537) B1028537
theorem B226939 : Blo 199806 226939 := bstep (se 1 (by rfl) ⟨170204, by rfl⟩ : syracuseStep 226939 = 340409) B340409
theorem B685853 : Blo 199806 685853 := bstep (se 3 (by rfl) ⟨128597, by rfl⟩ : syracuseStep 685853 = 257195) B257195
theorem B456623 : Blo 199806 456623 := bstep (se 1 (by rfl) ⟨342467, by rfl⟩ : syracuseStep 456623 = 684935) B684935
theorem B227407 : Blo 199806 227407 := bstep (se 1 (by rfl) ⟨170555, by rfl⟩ : syracuseStep 227407 = 341111) B341111
theorem B456875 : Blo 199806 456875 := bstep (se 1 (by rfl) ⟨342656, by rfl⟩ : syracuseStep 456875 = 685313) B685313
theorem B391367 : Blo 199806 391367 := bstep (se 1 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 391367 = 587051) B587051
theorem B227803 : Blo 199806 227803 := bstep (se 1 (by rfl) ⟨170852, by rfl⟩ : syracuseStep 227803 = 341705) B341705
theorem B686555 : Blo 199806 686555 := bstep (se 1 (by rfl) ⟨514916, by rfl⟩ : syracuseStep 686555 = 1029833) B1029833
theorem B1014281 : Blo 199806 1014281 := bstep (se 2 (by rfl) ⟨380355, by rfl⟩ : syracuseStep 1014281 = 760711) B760711
theorem B457415 : Blo 199806 457415 := bstep (se 1 (by rfl) ⟨343061, by rfl⟩ : syracuseStep 457415 = 686123) B686123
theorem B228271 : Blo 199806 228271 := bstep (se 1 (by rfl) ⟨171203, by rfl⟩ : syracuseStep 228271 = 342407) B342407
theorem B687257 : Blo 199806 687257 := bstep (se 2 (by rfl) ⟨257721, by rfl⟩ : syracuseStep 687257 = 515443) B515443
theorem B1375427 : Blo 199806 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B5209433 : Blo 199806 5209433 := bstep (se 2 (by rfl) ⟨1953537, by rfl⟩ : syracuseStep 5209433 = 3907075) B3907075
theorem B228703 : Blo 199806 228703 := bstep (se 1 (by rfl) ⟨171527, by rfl⟩ : syracuseStep 228703 = 343055) B343055
theorem B556583 : Blo 199806 556583 := bstep (se 1 (by rfl) ⟨417437, by rfl⟩ : syracuseStep 556583 = 834875) B834875
theorem B458279 : Blo 199806 458279 := bstep (se 1 (by rfl) ⟨343709, by rfl⟩ : syracuseStep 458279 = 687419) B687419
theorem B229063 : Blo 199806 229063 := bstep (se 1 (by rfl) ⟨171797, by rfl⟩ : syracuseStep 229063 = 343595) B343595
theorem B261995 : Blo 199806 261995 := bstep (se 1 (by rfl) ⟨196496, by rfl⟩ : syracuseStep 261995 = 392993) B392993
theorem B360379 : Blo 199806 360379 := bstep (se 1 (by rfl) ⟨270284, by rfl⟩ : syracuseStep 360379 = 540569) B540569
theorem B1015739 : Blo 199806 1015739 := bstep (se 1 (by rfl) ⟨761804, by rfl⟩ : syracuseStep 1015739 = 1523609) B1523609
theorem B1146899 : Blo 199806 1146899 := bstep (se 1 (by rfl) ⟨860174, by rfl⟩ : syracuseStep 1146899 = 1720349) B1720349
theorem B1540619 : Blo 199806 1540619 := bstep (se 1 (by rfl) ⟨1155464, by rfl⟩ : syracuseStep 1540619 = 2310929) B2310929
theorem B4391495 : Blo 199806 4391495 := bstep (se 1 (by rfl) ⟨3293621, by rfl⟩ : syracuseStep 4391495 = 6587243) B6587243
theorem B1147607 : Blo 199806 1147607 := bstep (se 1 (by rfl) ⟨860705, by rfl⟩ : syracuseStep 1147607 = 1721411) B1721411
theorem B7537481 : Blo 199806 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B5506319 : Blo 199806 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B1017197 : Blo 199806 1017197 := bstep (se 3 (by rfl) ⟨190724, by rfl⟩ : syracuseStep 1017197 = 381449) B381449
theorem B1738529 : Blo 199806 1738529 := bstep (se 2 (by rfl) ⟨651948, by rfl⟩ : syracuseStep 1738529 = 1303897) B1303897
theorem B854297 : Blo 199806 854297 := bstep (se 2 (by rfl) ⟨320361, by rfl⟩ : syracuseStep 854297 = 640723) B640723
theorem B1379207 : Blo 199806 1379207 := bstep (se 1 (by rfl) ⟨1034405, by rfl⟩ : syracuseStep 1379207 = 2068811) B2068811
theorem B1707227 : Blo 199806 1707227 := bstep (se 1 (by rfl) ⟨1280420, by rfl⟩ : syracuseStep 1707227 = 2560841) B2560841
theorem B199967 : Blo 199806 199967 := bstep (se 1 (by rfl) ⟨149975, by rfl⟩ : syracuseStep 199967 = 299951) B299951
theorem B200027 : Blo 199806 200027 := bstep (se 1 (by rfl) ⟨150020, by rfl⟩ : syracuseStep 200027 = 300041) B300041
theorem B200047 : Blo 199806 200047 := bstep (se 1 (by rfl) ⟨150035, by rfl⟩ : syracuseStep 200047 = 300071) B300071
theorem B200103 : Blo 199806 200103 := bstep (se 1 (by rfl) ⟨150077, by rfl⟩ : syracuseStep 200103 = 300155) B300155
theorem B3247559 : Blo 199806 3247559 := bstep (se 1 (by rfl) ⟨2435669, by rfl⟩ : syracuseStep 3247559 = 4871339) B4871339
theorem B200187 : Blo 199806 200187 := bstep (se 1 (by rfl) ⟨150140, by rfl⟩ : syracuseStep 200187 = 300281) B300281
theorem B200255 : Blo 199806 200255 := bstep (se 1 (by rfl) ⟨150191, by rfl⟩ : syracuseStep 200255 = 300383) B300383
theorem B200263 : Blo 199806 200263 := bstep (se 1 (by rfl) ⟨150197, by rfl⟩ : syracuseStep 200263 = 300395) B300395
theorem B396895 : Blo 199806 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B200415 : Blo 199806 200415 := bstep (se 1 (by rfl) ⟨150311, by rfl⟩ : syracuseStep 200415 = 300623) B300623
theorem B1019627 : Blo 199806 1019627 := bstep (se 1 (by rfl) ⟨764720, by rfl⟩ : syracuseStep 1019627 = 1529441) B1529441
theorem B4951813 : Blo 199806 4951813 := bstep (se 4 (by rfl) ⟨464232, by rfl⟩ : syracuseStep 4951813 = 928465) B928465
theorem B200495 : Blo 199806 200495 := bstep (se 1 (by rfl) ⟨150371, by rfl⟩ : syracuseStep 200495 = 300743) B300743
theorem B2461549 : Blo 199806 2461549 := bstep (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) B923081
theorem B855937 : Blo 199806 855937 := bstep (se 2 (by rfl) ⟨320976, by rfl⟩ : syracuseStep 855937 = 641953) B641953
theorem B200603 : Blo 199806 200603 := bstep (se 1 (by rfl) ⟨150452, by rfl⟩ : syracuseStep 200603 = 300905) B300905
theorem B200655 : Blo 199806 200655 := bstep (se 1 (by rfl) ⟨150491, by rfl⟩ : syracuseStep 200655 = 300983) B300983
theorem B364495 : Blo 199806 364495 := bstep (se 1 (by rfl) ⟨273371, by rfl⟩ : syracuseStep 364495 = 546743) B546743
theorem B200679 : Blo 199806 200679 := bstep (se 1 (by rfl) ⟨150509, by rfl⟩ : syracuseStep 200679 = 301019) B301019
theorem B1020113 : Blo 199806 1020113 := bstep (se 2 (by rfl) ⟨382542, by rfl⟩ : syracuseStep 1020113 = 765085) B765085
theorem B1708289 : Blo 199806 1708289 := bstep (se 2 (by rfl) ⟨640608, by rfl⟩ : syracuseStep 1708289 = 1281217) B1281217
theorem B200991 : Blo 199806 200991 := bstep (se 1 (by rfl) ⟨150743, by rfl⟩ : syracuseStep 200991 = 301487) B301487
theorem B201051 : Blo 199806 201051 := bstep (se 1 (by rfl) ⟨150788, by rfl⟩ : syracuseStep 201051 = 301577) B301577
theorem B201071 : Blo 199806 201071 := bstep (se 1 (by rfl) ⟨150803, by rfl⟩ : syracuseStep 201071 = 301607) B301607
theorem B430447 : Blo 199806 430447 := bstep (se 1 (by rfl) ⟨322835, by rfl⟩ : syracuseStep 430447 = 645671) B645671
theorem B201127 : Blo 199806 201127 := bstep (se 1 (by rfl) ⟨150845, by rfl⟩ : syracuseStep 201127 = 301691) B301691
theorem B201211 : Blo 199806 201211 := bstep (se 1 (by rfl) ⟨150908, by rfl⟩ : syracuseStep 201211 = 301817) B301817
theorem B201279 : Blo 199806 201279 := bstep (se 1 (by rfl) ⟨150959, by rfl⟩ : syracuseStep 201279 = 301919) B301919
theorem B201287 : Blo 199806 201287 := bstep (se 1 (by rfl) ⟨150965, by rfl⟩ : syracuseStep 201287 = 301931) B301931
theorem B725657 : Blo 199806 725657 := bstep (se 2 (by rfl) ⟨272121, by rfl⟩ : syracuseStep 725657 = 544243) B544243
theorem B1020599 : Blo 199806 1020599 := bstep (se 1 (by rfl) ⟨765449, by rfl⟩ : syracuseStep 1020599 = 1530899) B1530899
theorem B1086155 : Blo 199806 1086155 := bstep (se 1 (by rfl) ⟨814616, by rfl⟩ : syracuseStep 1086155 = 1629233) B1629233
theorem B201439 : Blo 199806 201439 := bstep (se 1 (by rfl) ⟨151079, by rfl⟩ : syracuseStep 201439 = 302159) B302159
theorem B201519 : Blo 199806 201519 := bstep (se 1 (by rfl) ⟨151139, by rfl⟩ : syracuseStep 201519 = 302279) B302279
theorem B299855 : Blo 199806 299855 := bstep (se 1 (by rfl) ⟨224891, by rfl⟩ : syracuseStep 299855 = 449783) B449783
theorem B201627 : Blo 199806 201627 := bstep (se 1 (by rfl) ⟨151220, by rfl⟩ : syracuseStep 201627 = 302441) B302441
theorem B201679 : Blo 199806 201679 := bstep (se 1 (by rfl) ⟨151259, by rfl⟩ : syracuseStep 201679 = 302519) B302519
theorem B201703 : Blo 199806 201703 := bstep (se 1 (by rfl) ⟨151277, by rfl⟩ : syracuseStep 201703 = 302555) B302555
theorem B463969 : Blo 199806 463969 := bstep (se 2 (by rfl) ⟨173988, by rfl⟩ : syracuseStep 463969 = 347977) B347977
theorem B1021085 : Blo 199806 1021085 := bstep (se 3 (by rfl) ⟨191453, by rfl⟩ : syracuseStep 1021085 = 382907) B382907
theorem B300251 : Blo 199806 300251 := bstep (se 1 (by rfl) ⟨225188, by rfl⟩ : syracuseStep 300251 = 450377) B450377
theorem B202015 : Blo 199806 202015 := bstep (se 1 (by rfl) ⟨151511, by rfl⟩ : syracuseStep 202015 = 303023) B303023
theorem B202075 : Blo 199806 202075 := bstep (se 1 (by rfl) ⟨151556, by rfl⟩ : syracuseStep 202075 = 303113) B303113
theorem B202095 : Blo 199806 202095 := bstep (se 1 (by rfl) ⟨151571, by rfl⟩ : syracuseStep 202095 = 303143) B303143
theorem B300425 : Blo 199806 300425 := bstep (se 2 (by rfl) ⟨112659, by rfl⟩ : syracuseStep 300425 = 225319) B225319
theorem B202151 : Blo 199806 202151 := bstep (se 1 (by rfl) ⟨151613, by rfl⟩ : syracuseStep 202151 = 303227) B303227
theorem B1381835 : Blo 199806 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B202235 : Blo 199806 202235 := bstep (se 1 (by rfl) ⟨151676, by rfl⟩ : syracuseStep 202235 = 303353) B303353
theorem B202303 : Blo 199806 202303 := bstep (se 1 (by rfl) ⟨151727, by rfl⟩ : syracuseStep 202303 = 303455) B303455
theorem B202311 : Blo 199806 202311 := bstep (se 1 (by rfl) ⟨151733, by rfl⟩ : syracuseStep 202311 = 303467) B303467
theorem B202463 : Blo 199806 202463 := bstep (se 1 (by rfl) ⟨151847, by rfl⟩ : syracuseStep 202463 = 303695) B303695
theorem B300779 : Blo 199806 300779 := bstep (se 1 (by rfl) ⟨225584, by rfl⟩ : syracuseStep 300779 = 451169) B451169
theorem B5936885 : Blo 199806 5936885 := bstep (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) B556583
theorem B202543 : Blo 199806 202543 := bstep (se 1 (by rfl) ⟨151907, by rfl⟩ : syracuseStep 202543 = 303815) B303815
theorem B202651 : Blo 199806 202651 := bstep (se 1 (by rfl) ⟨151988, by rfl⟩ : syracuseStep 202651 = 303977) B303977
theorem B301007 : Blo 199806 301007 := bstep (se 1 (by rfl) ⟨225755, by rfl⟩ : syracuseStep 301007 = 451511) B451511
theorem B202703 : Blo 199806 202703 := bstep (se 1 (by rfl) ⟨152027, by rfl⟩ : syracuseStep 202703 = 304055) B304055
theorem B202727 : Blo 199806 202727 := bstep (se 1 (by rfl) ⟨152045, by rfl⟩ : syracuseStep 202727 = 304091) B304091
theorem B203039 : Blo 199806 203039 := bstep (se 1 (by rfl) ⟨152279, by rfl⟩ : syracuseStep 203039 = 304559) B304559
theorem B301403 : Blo 199806 301403 := bstep (se 1 (by rfl) ⟨226052, by rfl⟩ : syracuseStep 301403 = 452105) B452105
theorem B203099 : Blo 199806 203099 := bstep (se 1 (by rfl) ⟨152324, by rfl⟩ : syracuseStep 203099 = 304649) B304649
theorem B11573603 : Blo 199806 11573603 := bstep (se 1 (by rfl) ⟨8680202, by rfl⟩ : syracuseStep 11573603 = 17360405) B17360405
theorem B203119 : Blo 199806 203119 := bstep (se 1 (by rfl) ⟨152339, by rfl⟩ : syracuseStep 203119 = 304679) B304679
theorem B203175 : Blo 199806 203175 := bstep (se 1 (by rfl) ⟨152381, by rfl⟩ : syracuseStep 203175 = 304763) B304763
theorem B1022381 : Blo 199806 1022381 := bstep (se 3 (by rfl) ⟨191696, by rfl⟩ : syracuseStep 1022381 = 383393) B383393
theorem B203259 : Blo 199806 203259 := bstep (se 1 (by rfl) ⟨152444, by rfl⟩ : syracuseStep 203259 = 304889) B304889
theorem B3545633 : Blo 199806 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B301631 : Blo 199806 301631 := bstep (se 1 (by rfl) ⟨226223, by rfl⟩ : syracuseStep 301631 = 452447) B452447
theorem B203327 : Blo 199806 203327 := bstep (se 1 (by rfl) ⟨152495, by rfl⟩ : syracuseStep 203327 = 304991) B304991
theorem B203335 : Blo 199806 203335 := bstep (se 1 (by rfl) ⟨152501, by rfl⟩ : syracuseStep 203335 = 305003) B305003
theorem B1022543 : Blo 199806 1022543 := bstep (se 1 (by rfl) ⟨766907, by rfl⟩ : syracuseStep 1022543 = 1533815) B1533815
theorem B432719 : Blo 199806 432719 := bstep (se 1 (by rfl) ⟨324539, by rfl⟩ : syracuseStep 432719 = 649079) B649079
theorem B301751 : Blo 199806 301751 := bstep (se 1 (by rfl) ⟨226313, by rfl⟩ : syracuseStep 301751 = 452627) B452627
theorem B203487 : Blo 199806 203487 := bstep (se 1 (by rfl) ⟨152615, by rfl⟩ : syracuseStep 203487 = 305231) B305231
theorem B3250925 : Blo 199806 3250925 := bstep (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) B1219097
theorem B203567 : Blo 199806 203567 := bstep (se 1 (by rfl) ⟨152675, by rfl⟩ : syracuseStep 203567 = 305351) B305351
theorem B2071439 : Blo 199806 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B301979 : Blo 199806 301979 := bstep (se 1 (by rfl) ⟨226484, by rfl⟩ : syracuseStep 301979 = 452969) B452969
theorem B203675 : Blo 199806 203675 := bstep (se 1 (by rfl) ⟨152756, by rfl⟩ : syracuseStep 203675 = 305513) B305513
theorem B203727 : Blo 199806 203727 := bstep (se 1 (by rfl) ⟨152795, by rfl⟩ : syracuseStep 203727 = 305591) B305591
theorem B203751 : Blo 199806 203751 := bstep (se 1 (by rfl) ⟨152813, by rfl⟩ : syracuseStep 203751 = 305627) B305627
theorem B859355 : Blo 199806 859355 := bstep (se 1 (by rfl) ⟨644516, by rfl⟩ : syracuseStep 859355 = 1289033) B1289033
theorem B859423 : Blo 199806 859423 := bstep (se 1 (by rfl) ⟨644567, by rfl⟩ : syracuseStep 859423 = 1289135) B1289135
theorem B302375 : Blo 199806 302375 := bstep (se 1 (by rfl) ⟨226781, by rfl⟩ : syracuseStep 302375 = 453563) B453563
theorem B1154371 : Blo 199806 1154371 := bstep (se 1 (by rfl) ⟨865778, by rfl⟩ : syracuseStep 1154371 = 1731557) B1731557
theorem B433505 : Blo 199806 433505 := bstep (se 2 (by rfl) ⟨162564, by rfl⟩ : syracuseStep 433505 = 325129) B325129
theorem B302459 : Blo 199806 302459 := bstep (se 1 (by rfl) ⟨226844, by rfl⟩ : syracuseStep 302459 = 453689) B453689
theorem B302585 : Blo 199806 302585 := bstep (se 2 (by rfl) ⟨113469, by rfl⟩ : syracuseStep 302585 = 226939) B226939
theorem B302687 : Blo 199806 302687 := bstep (se 1 (by rfl) ⟨227015, by rfl⟩ : syracuseStep 302687 = 454031) B454031
theorem B302903 : Blo 199806 302903 := bstep (se 1 (by rfl) ⟨227177, by rfl⟩ : syracuseStep 302903 = 454355) B454355
theorem B1024001 : Blo 199806 1024001 := bstep (se 2 (by rfl) ⟨384000, by rfl⟩ : syracuseStep 1024001 = 768001) B768001
theorem B303209 : Blo 199806 303209 := bstep (se 2 (by rfl) ⟨113703, by rfl⟩ : syracuseStep 303209 = 227407) B227407
theorem B2433235 : Blo 199806 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B303527 : Blo 199806 303527 := bstep (se 1 (by rfl) ⟨227645, by rfl⟩ : syracuseStep 303527 = 455291) B455291
theorem B303611 : Blo 199806 303611 := bstep (se 1 (by rfl) ⟨227708, by rfl⟩ : syracuseStep 303611 = 455417) B455417
theorem B6758923 : Blo 199806 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B270955 : Blo 199806 270955 := bstep (se 1 (by rfl) ⟨203216, by rfl⟩ : syracuseStep 270955 = 406433) B406433
theorem B303737 : Blo 199806 303737 := bstep (se 2 (by rfl) ⟨113901, by rfl⟩ : syracuseStep 303737 = 227803) B227803
theorem B303791 : Blo 199806 303791 := bstep (se 1 (by rfl) ⟨227843, by rfl⟩ : syracuseStep 303791 = 455687) B455687
theorem B303839 : Blo 199806 303839 := bstep (se 1 (by rfl) ⟨227879, by rfl⟩ : syracuseStep 303839 = 455759) B455759
theorem B1024811 : Blo 199806 1024811 := bstep (se 1 (by rfl) ⟨768608, by rfl⟩ : syracuseStep 1024811 = 1537217) B1537217
theorem B304103 : Blo 199806 304103 := bstep (se 1 (by rfl) ⟨228077, by rfl⟩ : syracuseStep 304103 = 456155) B456155
theorem B1156103 : Blo 199806 1156103 := bstep (se 1 (by rfl) ⟨867077, by rfl⟩ : syracuseStep 1156103 = 1734155) B1734155
theorem B402575 : Blo 199806 402575 := bstep (se 1 (by rfl) ⟨301931, by rfl⟩ : syracuseStep 402575 = 603863) B603863
theorem B304361 : Blo 199806 304361 := bstep (se 2 (by rfl) ⟨114135, by rfl⟩ : syracuseStep 304361 = 228271) B228271
theorem B304415 : Blo 199806 304415 := bstep (se 1 (by rfl) ⟨228311, by rfl⟩ : syracuseStep 304415 = 456623) B456623
theorem B337351 : Blo 199806 337351 := bstep (se 1 (by rfl) ⟨253013, by rfl⟩ : syracuseStep 337351 = 506027) B506027
theorem B304583 : Blo 199806 304583 := bstep (se 1 (by rfl) ⟨228437, by rfl⟩ : syracuseStep 304583 = 456875) B456875
theorem B271993 : Blo 199806 271993 := bstep (se 2 (by rfl) ⟨101997, by rfl⟩ : syracuseStep 271993 = 203995) B203995
theorem B304937 : Blo 199806 304937 := bstep (se 2 (by rfl) ⟨114351, by rfl⟩ : syracuseStep 304937 = 228703) B228703
theorem B304943 : Blo 199806 304943 := bstep (se 1 (by rfl) ⟨228707, by rfl⟩ : syracuseStep 304943 = 457415) B457415
theorem B337871 : Blo 199806 337871 := bstep (se 1 (by rfl) ⟨253403, by rfl⟩ : syracuseStep 337871 = 506807) B506807
theorem B305417 : Blo 199806 305417 := bstep (se 2 (by rfl) ⟨114531, by rfl⟩ : syracuseStep 305417 = 229063) B229063
theorem B698653 : Blo 199806 698653 := bstep (se 3 (by rfl) ⟨130997, by rfl⟩ : syracuseStep 698653 = 261995) B261995
theorem B305519 : Blo 199806 305519 := bstep (se 1 (by rfl) ⟨229139, by rfl⟩ : syracuseStep 305519 = 458279) B458279
theorem B338539 : Blo 199806 338539 := bstep (se 1 (by rfl) ⟨253904, by rfl⟩ : syracuseStep 338539 = 507809) B507809
theorem B436919 : Blo 199806 436919 := bstep (se 1 (by rfl) ⟨327689, by rfl⟩ : syracuseStep 436919 = 655379) B655379
theorem B1845949 : Blo 199806 1845949 := bstep (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) B692231
theorem B1026755 : Blo 199806 1026755 := bstep (se 1 (by rfl) ⟨770066, by rfl⟩ : syracuseStep 1026755 = 1540133) B1540133
theorem B338843 : Blo 199806 338843 := bstep (se 1 (by rfl) ⟨254132, by rfl⟩ : syracuseStep 338843 = 508265) B508265
theorem B207847 : Blo 199806 207847 := bstep (se 1 (by rfl) ⟨155885, by rfl⟩ : syracuseStep 207847 = 311771) B311771
theorem B1028105 : Blo 199806 1028105 := bstep (se 2 (by rfl) ⟨385539, by rfl⟩ : syracuseStep 1028105 = 771079) B771079
theorem B438281 : Blo 199806 438281 := bstep (se 2 (by rfl) ⟨164355, by rfl⟩ : syracuseStep 438281 = 328711) B328711
theorem B1519721 : Blo 199806 1519721 := bstep (se 2 (by rfl) ⟨569895, by rfl⟩ : syracuseStep 1519721 = 1139791) B1139791
theorem B766057 : Blo 199806 766057 := bstep (se 2 (by rfl) ⟨287271, by rfl⟩ : syracuseStep 766057 = 574543) B574543
theorem B569555 : Blo 199806 569555 := bstep (se 1 (by rfl) ⟨427166, by rfl⟩ : syracuseStep 569555 = 854333) B854333
theorem B242011 : Blo 199806 242011 := bstep (se 1 (by rfl) ⟨181508, by rfl⟩ : syracuseStep 242011 = 363017) B363017
theorem B8663597 : Blo 199806 8663597 := bstep (se 3 (by rfl) ⟨1624424, by rfl⟩ : syracuseStep 8663597 = 3248849) B3248849
theorem B1094195 : Blo 199806 1094195 := bstep (se 1 (by rfl) ⟨820646, by rfl⟩ : syracuseStep 1094195 = 1641293) B1641293
theorem B308047 : Blo 199806 308047 := bstep (se 1 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 308047 = 462071) B462071
theorem B407033 : Blo 199806 407033 := bstep (se 2 (by rfl) ⟨152637, by rfl⟩ : syracuseStep 407033 = 305275) B305275
theorem B505865 : Blo 199806 505865 := bstep (se 2 (by rfl) ⟨189699, by rfl⟩ : syracuseStep 505865 = 379399) B379399
theorem B1718435 : Blo 199806 1718435 := bstep (se 1 (by rfl) ⟨1288826, by rfl⟩ : syracuseStep 1718435 = 2577653) B2577653
theorem B571673 : Blo 199806 571673 := bstep (se 2 (by rfl) ⟨214377, by rfl⟩ : syracuseStep 571673 = 428755) B428755
theorem B866771 : Blo 199806 866771 := bstep (se 1 (by rfl) ⟨650078, by rfl⟩ : syracuseStep 866771 = 1300157) B1300157
theorem B1030643 : Blo 199806 1030643 := bstep (se 1 (by rfl) ⟨772982, by rfl⟩ : syracuseStep 1030643 = 1545965) B1545965
theorem B1456679 : Blo 199806 1456679 := bstep (se 1 (by rfl) ⟨1092509, by rfl⟩ : syracuseStep 1456679 = 2185019) B2185019
theorem B342751 : Blo 199806 342751 := bstep (se 1 (by rfl) ⟨257063, by rfl⟩ : syracuseStep 342751 = 514127) B514127
theorem B1031291 : Blo 199806 1031291 := bstep (se 1 (by rfl) ⟨773468, by rfl⟩ : syracuseStep 1031291 = 1546937) B1546937
theorem B507019 : Blo 199806 507019 := bstep (se 1 (by rfl) ⟨380264, by rfl⟩ : syracuseStep 507019 = 760529) B760529
theorem B343183 : Blo 199806 343183 := bstep (se 1 (by rfl) ⟨257387, by rfl⟩ : syracuseStep 343183 = 514775) B514775
theorem B343433 : Blo 199806 343433 := bstep (se 2 (by rfl) ⟨128787, by rfl⟩ : syracuseStep 343433 = 257575) B257575
theorem B540091 : Blo 199806 540091 := bstep (se 1 (by rfl) ⟨405068, by rfl⟩ : syracuseStep 540091 = 810137) B810137
theorem B507323 : Blo 199806 507323 := bstep (se 1 (by rfl) ⟨380492, by rfl⟩ : syracuseStep 507323 = 760985) B760985
theorem B868103 : Blo 199806 868103 := bstep (se 1 (by rfl) ⟨651077, by rfl⟩ : syracuseStep 868103 = 1302155) B1302155
theorem B343865 : Blo 199806 343865 := bstep (se 2 (by rfl) ⟨128949, by rfl⟩ : syracuseStep 343865 = 257899) B257899
theorem B573313 : Blo 199806 573313 := bstep (se 2 (by rfl) ⟨214992, by rfl⟩ : syracuseStep 573313 = 429985) B429985
theorem B2277395 : Blo 199806 2277395 := bstep (se 1 (by rfl) ⟨1708046, by rfl⟩ : syracuseStep 2277395 = 3416093) B3416093
theorem B1721033 : Blo 199806 1721033 := bstep (se 2 (by rfl) ⟨645387, by rfl⟩ : syracuseStep 1721033 = 1290775) B1290775
theorem B508639 : Blo 199806 508639 := bstep (se 1 (by rfl) ⟨381479, by rfl⟩ : syracuseStep 508639 = 762959) B762959
theorem B508751 : Blo 199806 508751 := bstep (se 1 (by rfl) ⟨381563, by rfl⟩ : syracuseStep 508751 = 763127) B763127
theorem B574589 : Blo 199806 574589 := bstep (se 3 (by rfl) ⟨107735, by rfl⟩ : syracuseStep 574589 = 215471) B215471
theorem B640199 : Blo 199806 640199 := bstep (se 1 (by rfl) ⟨480149, by rfl⟩ : syracuseStep 640199 = 960299) B960299
theorem B509399 : Blo 199806 509399 := bstep (se 1 (by rfl) ⟨382049, by rfl⟩ : syracuseStep 509399 = 764099) B764099
theorem B509753 : Blo 199806 509753 := bstep (se 2 (by rfl) ⟨191157, by rfl⟩ : syracuseStep 509753 = 382315) B382315
theorem B2312387 : Blo 199806 2312387 := bstep (se 1 (by rfl) ⟨1734290, by rfl⟩ : syracuseStep 2312387 = 3468581) B3468581
theorem B772361 : Blo 199806 772361 := bstep (se 2 (by rfl) ⟨289635, by rfl⟩ : syracuseStep 772361 = 579271) B579271
theorem B608723 : Blo 199806 608723 := bstep (se 1 (by rfl) ⟨456542, by rfl⟩ : syracuseStep 608723 = 913085) B913085
theorem B2607997 : Blo 199806 2607997 := bstep (se 3 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 2607997 = 977999) B977999
theorem B511393 : Blo 199806 511393 := bstep (se 2 (by rfl) ⟨191772, by rfl⟩ : syracuseStep 511393 = 383545) B383545
theorem B380713 : Blo 199806 380713 := bstep (se 2 (by rfl) ⟨142767, by rfl⟩ : syracuseStep 380713 = 285535) B285535
theorem B643081 : Blo 199806 643081 := bstep (se 2 (by rfl) ⟨241155, by rfl⟩ : syracuseStep 643081 = 482311) B482311
theorem B1232921 : Blo 199806 1232921 := bstep (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) B924691
theorem B4378853 : Blo 199806 4378853 := bstep (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) B821035
theorem B676187 : Blo 199806 676187 := bstep (se 1 (by rfl) ⟨507140, by rfl⟩ : syracuseStep 676187 = 1014281) B1014281
theorem B512507 : Blo 199806 512507 := bstep (se 1 (by rfl) ⟨384380, by rfl⟩ : syracuseStep 512507 = 768761) B768761
theorem B381503 : Blo 199806 381503 := bstep (se 1 (by rfl) ⟨286127, by rfl⟩ : syracuseStep 381503 = 572255) B572255
theorem B1036871 : Blo 199806 1036871 := bstep (se 1 (by rfl) ⟨777653, by rfl⟩ : syracuseStep 1036871 = 1555307) B1555307
theorem B644311 : Blo 199806 644311 := bstep (se 1 (by rfl) ⟨483233, by rfl⟩ : syracuseStep 644311 = 966467) B966467
theorem B1299671 : Blo 199806 1299671 := bstep (se 1 (by rfl) ⟨974753, by rfl⟩ : syracuseStep 1299671 = 1949507) B1949507
theorem B382171 : Blo 199806 382171 := bstep (se 1 (by rfl) ⟨286628, by rfl⟩ : syracuseStep 382171 = 573257) B573257
theorem B480505 : Blo 199806 480505 := bstep (se 2 (by rfl) ⟨180189, by rfl⟩ : syracuseStep 480505 = 360379) B360379
theorem B677159 : Blo 199806 677159 := bstep (se 1 (by rfl) ⟨507869, by rfl⟩ : syracuseStep 677159 = 1015739) B1015739
theorem B1725785 : Blo 199806 1725785 := bstep (se 2 (by rfl) ⟨647169, by rfl⟩ : syracuseStep 1725785 = 1294339) B1294339
theorem B513479 : Blo 199806 513479 := bstep (se 1 (by rfl) ⟨385109, by rfl⟩ : syracuseStep 513479 = 770219) B770219
theorem B14636771 : Blo 199806 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B481081 : Blo 199806 481081 := bstep (se 2 (by rfl) ⟨180405, by rfl⟩ : syracuseStep 481081 = 360811) B360811
theorem B1955771 : Blo 199806 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B481409 : Blo 199806 481409 := bstep (se 2 (by rfl) ⟨180528, by rfl⟩ : syracuseStep 481409 = 361057) B361057
theorem B678023 : Blo 199806 678023 := bstep (se 1 (by rfl) ⟨508517, by rfl⟩ : syracuseStep 678023 = 1017035) B1017035
theorem B514259 : Blo 199806 514259 := bstep (se 1 (by rfl) ⟨385694, by rfl⟩ : syracuseStep 514259 = 771389) B771389
theorem B481609 : Blo 199806 481609 := bstep (se 2 (by rfl) ⟨180603, by rfl⟩ : syracuseStep 481609 = 361207) B361207
theorem B514471 : Blo 199806 514471 := bstep (se 1 (by rfl) ⟨385853, by rfl⟩ : syracuseStep 514471 = 771707) B771707
theorem B514633 : Blo 199806 514633 := bstep (se 2 (by rfl) ⟨192987, by rfl⟩ : syracuseStep 514633 = 385975) B385975
theorem B1924013 : Blo 199806 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B515423 : Blo 199806 515423 := bstep (se 1 (by rfl) ⟨386567, by rfl⟩ : syracuseStep 515423 = 773135) B773135
theorem B679265 : Blo 199806 679265 := bstep (se 2 (by rfl) ⟨254724, by rfl⟩ : syracuseStep 679265 = 509449) B509449
theorem B253307 : Blo 199806 253307 := bstep (se 1 (by rfl) ⟨189980, by rfl⟩ : syracuseStep 253307 = 379961) B379961
theorem B613831 : Blo 199806 613831 := bstep (se 1 (by rfl) ⟨460373, by rfl⟩ : syracuseStep 613831 = 920747) B920747
theorem B286201 : Blo 199806 286201 := bstep (se 2 (by rfl) ⟨107325, by rfl⟩ : syracuseStep 286201 = 214651) B214651
theorem B1531385 : Blo 199806 1531385 := bstep (se 2 (by rfl) ⟨574269, by rfl⟩ : syracuseStep 1531385 = 1148539) B1148539
theorem B450143 : Blo 199806 450143 := bstep (se 1 (by rfl) ⟨337607, by rfl⟩ : syracuseStep 450143 = 675215) B675215
theorem B450359 : Blo 199806 450359 := bstep (se 1 (by rfl) ⟨337769, by rfl⟩ : syracuseStep 450359 = 675539) B675539
theorem B1138607 : Blo 199806 1138607 := bstep (se 1 (by rfl) ⟨853955, by rfl⟩ : syracuseStep 1138607 = 1707911) B1707911
theorem B2908163 : Blo 199806 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B450665 : Blo 199806 450665 := bstep (se 2 (by rfl) ⟨168999, by rfl⟩ : syracuseStep 450665 = 337999) B337999
theorem B385391 : Blo 199806 385391 := bstep (se 1 (by rfl) ⟨289043, by rfl⟩ : syracuseStep 385391 = 578087) B578087
theorem B451151 : Blo 199806 451151 := bstep (se 1 (by rfl) ⟨338363, by rfl⟩ : syracuseStep 451151 = 676727) B676727
theorem B2482859 : Blo 199806 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B320183 : Blo 199806 320183 := bstep (se 1 (by rfl) ⟨240137, by rfl⟩ : syracuseStep 320183 = 480275) B480275
theorem B451295 : Blo 199806 451295 := bstep (se 1 (by rfl) ⟨338471, by rfl⟩ : syracuseStep 451295 = 676943) B676943
theorem B254927 : Blo 199806 254927 := bstep (se 1 (by rfl) ⟨191195, by rfl⟩ : syracuseStep 254927 = 382391) B382391
theorem B451547 : Blo 199806 451547 := bstep (se 1 (by rfl) ⟨338660, by rfl⟩ : syracuseStep 451547 = 677321) B677321
theorem B1237979 : Blo 199806 1237979 := bstep (se 1 (by rfl) ⟨928484, by rfl⟩ : syracuseStep 1237979 = 1856969) B1856969
theorem B975847 : Blo 199806 975847 := bstep (se 1 (by rfl) ⟨731885, by rfl⟩ : syracuseStep 975847 = 1463771) B1463771
theorem B386039 : Blo 199806 386039 := bstep (se 1 (by rfl) ⟨289529, by rfl⟩ : syracuseStep 386039 = 579059) B579059
theorem B1303589 : Blo 199806 1303589 := bstep (se 4 (by rfl) ⟨122211, by rfl⟩ : syracuseStep 1303589 = 244423) B244423
theorem B3433589 : Blo 199806 3433589 := bstep (se 5 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 3433589 = 321899) B321899
theorem B451727 : Blo 199806 451727 := bstep (se 1 (by rfl) ⟨338795, by rfl⟩ : syracuseStep 451727 = 677591) B677591
theorem B3105985 : Blo 199806 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B451817 : Blo 199806 451817 := bstep (se 2 (by rfl) ⟨169431, by rfl⟩ : syracuseStep 451817 = 338863) B338863
theorem B681209 : Blo 199806 681209 := bstep (se 2 (by rfl) ⟨255453, by rfl⟩ : syracuseStep 681209 = 510907) B510907
theorem B451871 : Blo 199806 451871 := bstep (se 1 (by rfl) ⟨338903, by rfl⟩ : syracuseStep 451871 = 677807) B677807
theorem B681479 : Blo 199806 681479 := bstep (se 1 (by rfl) ⟨511109, by rfl⟩ : syracuseStep 681479 = 1022219) B1022219
theorem B1238561 : Blo 199806 1238561 := bstep (se 2 (by rfl) ⟨464460, by rfl⟩ : syracuseStep 1238561 = 928921) B928921
theorem B321259 : Blo 199806 321259 := bstep (se 1 (by rfl) ⟨240944, by rfl⟩ : syracuseStep 321259 = 481889) B481889
theorem B485099 : Blo 199806 485099 := bstep (se 1 (by rfl) ⟨363824, by rfl⟩ : syracuseStep 485099 = 727649) B727649
theorem B386795 : Blo 199806 386795 := bstep (se 1 (by rfl) ⟨290096, by rfl⟩ : syracuseStep 386795 = 580193) B580193
theorem B452393 : Blo 199806 452393 := bstep (se 2 (by rfl) ⟨169647, by rfl⟩ : syracuseStep 452393 = 339295) B339295
theorem B288559 : Blo 199806 288559 := bstep (se 1 (by rfl) ⟨216419, by rfl⟩ : syracuseStep 288559 = 432839) B432839
theorem B255899 : Blo 199806 255899 := bstep (se 1 (by rfl) ⟨191924, by rfl⟩ : syracuseStep 255899 = 383849) B383849
theorem B3697001 : Blo 199806 3697001 := bstep (se 2 (by rfl) ⟨1386375, by rfl⟩ : syracuseStep 3697001 = 2772751) B2772751
theorem B682451 : Blo 199806 682451 := bstep (se 1 (by rfl) ⟨511838, by rfl⟩ : syracuseStep 682451 = 1023677) B1023677
theorem B682559 : Blo 199806 682559 := bstep (se 1 (by rfl) ⟨511919, by rfl⟩ : syracuseStep 682559 = 1023839) B1023839
theorem B1534787 : Blo 199806 1534787 := bstep (se 1 (by rfl) ⟨1151090, by rfl⟩ : syracuseStep 1534787 = 2302181) B2302181
theorem B453455 : Blo 199806 453455 := bstep (se 1 (by rfl) ⟨340091, by rfl⟩ : syracuseStep 453455 = 680183) B680183
theorem B1141775 : Blo 199806 1141775 := bstep (se 1 (by rfl) ⟨856331, by rfl⟩ : syracuseStep 1141775 = 1712663) B1712663
theorem B453671 : Blo 199806 453671 := bstep (se 1 (by rfl) ⟨340253, by rfl⟩ : syracuseStep 453671 = 680507) B680507
theorem B453851 : Blo 199806 453851 := bstep (se 1 (by rfl) ⟨340388, by rfl⟩ : syracuseStep 453851 = 680777) B680777
theorem B454049 : Blo 199806 454049 := bstep (se 2 (by rfl) ⟨170268, by rfl⟩ : syracuseStep 454049 = 340537) B340537
theorem B650767 : Blo 199806 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B487147 : Blo 199806 487147 := bstep (se 1 (by rfl) ⟨365360, by rfl⟩ : syracuseStep 487147 = 730721) B730721
theorem B487223 : Blo 199806 487223 := bstep (se 1 (by rfl) ⟨365417, by rfl⟩ : syracuseStep 487223 = 730835) B730835
theorem B225103 : Blo 199806 225103 := bstep (se 1 (by rfl) ⟨168827, by rfl⟩ : syracuseStep 225103 = 337655) B337655
theorem B454607 : Blo 199806 454607 := bstep (se 1 (by rfl) ⟨340955, by rfl⟩ : syracuseStep 454607 = 681911) B681911
theorem B225499 : Blo 199806 225499 := bstep (se 1 (by rfl) ⟨169124, by rfl⟩ : syracuseStep 225499 = 338249) B338249
theorem B454985 : Blo 199806 454985 := bstep (se 2 (by rfl) ⟨170619, by rfl⟩ : syracuseStep 454985 = 341239) B341239
theorem B455003 : Blo 199806 455003 := bstep (se 1 (by rfl) ⟨341252, by rfl⟩ : syracuseStep 455003 = 682505) B682505
theorem B684395 : Blo 199806 684395 := bstep (se 1 (by rfl) ⟨513296, by rfl⟩ : syracuseStep 684395 = 1026593) B1026593
theorem B2748779 : Blo 199806 2748779 := bstep (se 1 (by rfl) ⟨2061584, by rfl⟩ : syracuseStep 2748779 = 4123169) B4123169
theorem B520631 : Blo 199806 520631 := bstep (se 1 (by rfl) ⟨390473, by rfl⟩ : syracuseStep 520631 = 780947) B780947
theorem B225787 : Blo 199806 225787 := bstep (se 1 (by rfl) ⟨169340, by rfl⟩ : syracuseStep 225787 = 338681) B338681
theorem B651847 : Blo 199806 651847 := bstep (se 1 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 651847 = 977771) B977771
theorem B684665 : Blo 199806 684665 := bstep (se 2 (by rfl) ⟨256749, by rfl⟩ : syracuseStep 684665 = 513499) B513499
theorem B225967 : Blo 199806 225967 := bstep (se 1 (by rfl) ⟨169475, by rfl⟩ : syracuseStep 225967 = 338951) B338951
theorem B520951 : Blo 199806 520951 := bstep (se 1 (by rfl) ⟨390713, by rfl⟩ : syracuseStep 520951 = 781427) B781427
theorem B1930013 : Blo 199806 1930013 := bstep (se 3 (by rfl) ⟨361877, by rfl⟩ : syracuseStep 1930013 = 723755) B723755
theorem B455579 : Blo 199806 455579 := bstep (se 1 (by rfl) ⟨341684, by rfl⟩ : syracuseStep 455579 = 683369) B683369
theorem B226255 : Blo 199806 226255 := bstep (se 1 (by rfl) ⟨169691, by rfl⟩ : syracuseStep 226255 = 339383) B339383
theorem B455777 : Blo 199806 455777 := bstep (se 2 (by rfl) ⟨170916, by rfl⟩ : syracuseStep 455777 = 341833) B341833
theorem B1012985 : Blo 199806 1012985 := bstep (se 2 (by rfl) ⟨379869, by rfl⟩ : syracuseStep 1012985 = 759739) B759739
theorem B455975 : Blo 199806 455975 := bstep (se 1 (by rfl) ⟨341981, by rfl⟩ : syracuseStep 455975 = 683963) B683963
theorem B226651 : Blo 199806 226651 := bstep (se 1 (by rfl) ⟨169988, by rfl⟩ : syracuseStep 226651 = 339977) B339977
theorem B423263 : Blo 199806 423263 := bstep (se 1 (by rfl) ⟨317447, by rfl⟩ : syracuseStep 423263 = 634895) B634895
theorem B3437963 : Blo 199806 3437963 := bstep (se 1 (by rfl) ⟨2578472, by rfl⟩ : syracuseStep 3437963 = 5156945) B5156945
theorem B292295 : Blo 199806 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B226759 : Blo 199806 226759 := bstep (se 1 (by rfl) ⟨170069, by rfl⟩ : syracuseStep 226759 = 340139) B340139
theorem B456353 : Blo 199806 456353 := bstep (se 2 (by rfl) ⟨171132, by rfl⟩ : syracuseStep 456353 = 342265) B342265
theorem B35452673 : Blo 199806 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B227119 : Blo 199806 227119 := bstep (se 1 (by rfl) ⟨170339, by rfl⟩ : syracuseStep 227119 = 340679) B340679
theorem B3667805 : Blo 199806 3667805 := bstep (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) B1375427
theorem B2914163 : Blo 199806 2914163 := bstep (se 1 (by rfl) ⟨2185622, by rfl⟩ : syracuseStep 2914163 = 4371245) B4371245
theorem B227227 : Blo 199806 227227 := bstep (se 1 (by rfl) ⟨170420, by rfl⟩ : syracuseStep 227227 = 340841) B340841
theorem B456713 : Blo 199806 456713 := bstep (se 2 (by rfl) ⟨171267, by rfl⟩ : syracuseStep 456713 = 342535) B342535
theorem B489577 : Blo 199806 489577 := bstep (se 2 (by rfl) ⟨183591, by rfl⟩ : syracuseStep 489577 = 367183) B367183
theorem B489683 : Blo 199806 489683 := bstep (se 1 (by rfl) ⟨367262, by rfl⟩ : syracuseStep 489683 = 734525) B734525
theorem B227623 : Blo 199806 227623 := bstep (se 1 (by rfl) ⟨170717, by rfl⟩ : syracuseStep 227623 = 341435) B341435
theorem B227695 : Blo 199806 227695 := bstep (se 1 (by rfl) ⟨170771, by rfl⟩ : syracuseStep 227695 = 341543) B341543
theorem B686447 : Blo 199806 686447 := bstep (se 1 (by rfl) ⟨514835, by rfl⟩ : syracuseStep 686447 = 1029671) B1029671
theorem B457127 : Blo 199806 457127 := bstep (se 1 (by rfl) ⟨342845, by rfl⟩ : syracuseStep 457127 = 685691) B685691
theorem B2587085 : Blo 199806 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B457235 : Blo 199806 457235 := bstep (se 1 (by rfl) ⟨342926, by rfl⟩ : syracuseStep 457235 = 685853) B685853
theorem B227911 : Blo 199806 227911 := bstep (se 1 (by rfl) ⟨170933, by rfl⟩ : syracuseStep 227911 = 341867) B341867
theorem B457289 : Blo 199806 457289 := bstep (se 2 (by rfl) ⟨171483, by rfl⟩ : syracuseStep 457289 = 342967) B342967
theorem B260911 : Blo 199806 260911 := bstep (se 1 (by rfl) ⟨195683, by rfl⟩ : syracuseStep 260911 = 391367) B391367
theorem B457703 : Blo 199806 457703 := bstep (se 1 (by rfl) ⟨343277, by rfl⟩ : syracuseStep 457703 = 686555) B686555
theorem B2194451 : Blo 199806 2194451 := bstep (se 1 (by rfl) ⟨1645838, by rfl⟩ : syracuseStep 2194451 = 3291677) B3291677
theorem B458081 : Blo 199806 458081 := bstep (se 2 (by rfl) ⟨171780, by rfl⟩ : syracuseStep 458081 = 343561) B343561
theorem B228775 : Blo 199806 228775 := bstep (se 1 (by rfl) ⟨171581, by rfl⟩ : syracuseStep 228775 = 343163) B343163
theorem B458171 : Blo 199806 458171 := bstep (se 1 (by rfl) ⟨343628, by rfl⟩ : syracuseStep 458171 = 687257) B687257
theorem B1080857 : Blo 199806 1080857 := bstep (se 2 (by rfl) ⟨405321, by rfl⟩ : syracuseStep 1080857 = 810643) B810643
theorem B458297 : Blo 199806 458297 := bstep (se 2 (by rfl) ⟨171861, by rfl⟩ : syracuseStep 458297 = 343723) B343723
theorem B3472955 : Blo 199806 3472955 := bstep (se 1 (by rfl) ⟨2604716, by rfl⟩ : syracuseStep 3472955 = 5209433) B5209433
theorem B3244313 : Blo 199806 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B1147355 : Blo 199806 1147355 := bstep (se 1 (by rfl) ⟨860516, by rfl⟩ : syracuseStep 1147355 = 1721033) B1721033
theorem B9011897 : Blo 199806 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B426799 : Blo 199806 426799 := bstep (se 1 (by rfl) ⟨320099, by rfl⟩ : syracuseStep 426799 = 640199) B640199
theorem B361273 : Blo 199806 361273 := bstep (se 2 (by rfl) ⟨135477, by rfl⟩ : syracuseStep 361273 = 270955) B270955
theorem B3670879 : Blo 199806 3670879 := bstep (se 1 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 3670879 = 5506319) B5506319
theorem B1541591 : Blo 199806 1541591 := bstep (se 1 (by rfl) ⟨1156193, by rfl⟩ : syracuseStep 1541591 = 2312387) B2312387
theorem B2917853 : Blo 199806 2917853 := bstep (se 3 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 2917853 = 1094195) B1094195
theorem B1935085 : Blo 199806 1935085 := bstep (se 3 (by rfl) ⟨362828, by rfl⟩ : syracuseStep 1935085 = 725657) B725657
theorem B6620957 : Blo 199806 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B919471 : Blo 199806 919471 := bstep (se 1 (by rfl) ⟨689603, by rfl⟩ : syracuseStep 919471 = 1379207) B1379207
theorem B362657 : Blo 199806 362657 := bstep (se 2 (by rfl) ⟨135996, by rfl⟩ : syracuseStep 362657 = 271993) B271993
theorem B2165039 : Blo 199806 2165039 := bstep (se 1 (by rfl) ⟨1623779, by rfl⟩ : syracuseStep 2165039 = 3247559) B3247559
theorem B428345 : Blo 199806 428345 := bstep (se 2 (by rfl) ⟨160629, by rfl⟩ : syracuseStep 428345 = 321259) B321259
theorem B821947 : Blo 199806 821947 := bstep (se 1 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 821947 = 1232921) B1232921
theorem B2919235 : Blo 199806 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B691247 : Blo 199806 691247 := bstep (se 1 (by rfl) ⟨518435, by rfl⟩ : syracuseStep 691247 = 1036871) B1036871
theorem B724103 : Blo 199806 724103 := bstep (se 1 (by rfl) ⟨543077, by rfl⟩ : syracuseStep 724103 = 1086155) B1086155
theorem B199903 : Blo 199806 199903 := bstep (se 1 (by rfl) ⟨149927, by rfl⟩ : syracuseStep 199903 = 299855) B299855
theorem B200167 : Blo 199806 200167 := bstep (se 1 (by rfl) ⟨150125, by rfl⟩ : syracuseStep 200167 = 300251) B300251
theorem B1150523 : Blo 199806 1150523 := bstep (se 1 (by rfl) ⟨862892, by rfl⟩ : syracuseStep 1150523 = 1725785) B1725785
theorem B2461265 : Blo 199806 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B200283 : Blo 199806 200283 := bstep (se 1 (by rfl) ⟨150212, by rfl⟩ : syracuseStep 200283 = 300425) B300425
theorem B921223 : Blo 199806 921223 := bstep (se 1 (by rfl) ⟨690917, by rfl⟩ : syracuseStep 921223 = 1381835) B1381835
theorem B200519 : Blo 199806 200519 := bstep (se 1 (by rfl) ⟨150389, by rfl⟩ : syracuseStep 200519 = 300779) B300779
theorem B3477329 : Blo 199806 3477329 := bstep (se 2 (by rfl) ⟨1303998, by rfl⟩ : syracuseStep 3477329 = 2607997) B2607997
theorem B200671 : Blo 199806 200671 := bstep (se 1 (by rfl) ⟨150503, by rfl⟩ : syracuseStep 200671 = 301007) B301007
theorem B200935 : Blo 199806 200935 := bstep (se 1 (by rfl) ⟨150701, by rfl⟩ : syracuseStep 200935 = 301403) B301403
theorem B2363755 : Blo 199806 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B201087 : Blo 199806 201087 := bstep (se 1 (by rfl) ⟨150815, by rfl⟩ : syracuseStep 201087 = 301631) B301631
theorem B201167 : Blo 199806 201167 := bstep (se 1 (by rfl) ⟨150875, by rfl⟩ : syracuseStep 201167 = 301751) B301751
theorem B2167283 : Blo 199806 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B1380959 : Blo 199806 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B201319 : Blo 199806 201319 := bstep (se 1 (by rfl) ⟨150989, by rfl⟩ : syracuseStep 201319 = 301979) B301979
theorem B529193 : Blo 199806 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B201583 : Blo 199806 201583 := bstep (se 1 (by rfl) ⟨151187, by rfl⟩ : syracuseStep 201583 = 302375) B302375
theorem B201639 : Blo 199806 201639 := bstep (se 1 (by rfl) ⟨151229, by rfl⟩ : syracuseStep 201639 = 302459) B302459
theorem B1020923 : Blo 199806 1020923 := bstep (se 1 (by rfl) ⟨765692, by rfl⟩ : syracuseStep 1020923 = 1531385) B1531385
theorem B201723 : Blo 199806 201723 := bstep (se 1 (by rfl) ⟨151292, by rfl⟩ : syracuseStep 201723 = 302585) B302585
theorem B300095 : Blo 199806 300095 := bstep (se 1 (by rfl) ⟨225071, by rfl⟩ : syracuseStep 300095 = 450143) B450143
theorem B201791 : Blo 199806 201791 := bstep (se 1 (by rfl) ⟨151343, by rfl⟩ : syracuseStep 201791 = 302687) B302687
theorem B300137 : Blo 199806 300137 := bstep (se 2 (by rfl) ⟨112551, by rfl⟩ : syracuseStep 300137 = 225103) B225103
theorem B3282065 : Blo 199806 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B300239 : Blo 199806 300239 := bstep (se 1 (by rfl) ⟨225179, by rfl⟩ : syracuseStep 300239 = 450359) B450359
theorem B201935 : Blo 199806 201935 := bstep (se 1 (by rfl) ⟨151451, by rfl⟩ : syracuseStep 201935 = 302903) B302903
theorem B759071 : Blo 199806 759071 := bstep (se 1 (by rfl) ⟨569303, by rfl⟩ : syracuseStep 759071 = 1138607) B1138607
theorem B857441 : Blo 199806 857441 := bstep (se 2 (by rfl) ⟨321540, by rfl⟩ : syracuseStep 857441 = 643081) B643081
theorem B300443 : Blo 199806 300443 := bstep (se 1 (by rfl) ⟨225332, by rfl⟩ : syracuseStep 300443 = 450665) B450665
theorem B202139 : Blo 199806 202139 := bstep (se 1 (by rfl) ⟨151604, by rfl⟩ : syracuseStep 202139 = 303209) B303209
theorem B1021409 : Blo 199806 1021409 := bstep (se 2 (by rfl) ⟨383028, by rfl⟩ : syracuseStep 1021409 = 766057) B766057
theorem B202351 : Blo 199806 202351 := bstep (se 1 (by rfl) ⟨151763, by rfl⟩ : syracuseStep 202351 = 303527) B303527
theorem B300665 : Blo 199806 300665 := bstep (se 2 (by rfl) ⟨112749, by rfl⟩ : syracuseStep 300665 = 225499) B225499
theorem B202407 : Blo 199806 202407 := bstep (se 1 (by rfl) ⟨151805, by rfl⟩ : syracuseStep 202407 = 303611) B303611
theorem B300767 : Blo 199806 300767 := bstep (se 1 (by rfl) ⟨225575, by rfl⟩ : syracuseStep 300767 = 451151) B451151
theorem B202491 : Blo 199806 202491 := bstep (se 1 (by rfl) ⟨151868, by rfl⟩ : syracuseStep 202491 = 303737) B303737
theorem B202527 : Blo 199806 202527 := bstep (se 1 (by rfl) ⟨151895, by rfl⟩ : syracuseStep 202527 = 303791) B303791
theorem B300863 : Blo 199806 300863 := bstep (se 1 (by rfl) ⟨225647, by rfl⟩ : syracuseStep 300863 = 451295) B451295
theorem B202559 : Blo 199806 202559 := bstep (se 1 (by rfl) ⟨151919, by rfl⟩ : syracuseStep 202559 = 303839) B303839
theorem B301031 : Blo 199806 301031 := bstep (se 1 (by rfl) ⟨225773, by rfl⟩ : syracuseStep 301031 = 451547) B451547
theorem B825319 : Blo 199806 825319 := bstep (se 1 (by rfl) ⟨618989, by rfl⟩ : syracuseStep 825319 = 1237979) B1237979
theorem B202735 : Blo 199806 202735 := bstep (se 1 (by rfl) ⟨152051, by rfl⟩ : syracuseStep 202735 = 304103) B304103
theorem B301049 : Blo 199806 301049 := bstep (se 2 (by rfl) ⟨112893, by rfl⟩ : syracuseStep 301049 = 225787) B225787
theorem B301151 : Blo 199806 301151 := bstep (se 1 (by rfl) ⟨225863, by rfl⟩ : syracuseStep 301151 = 451727) B451727
theorem B301211 : Blo 199806 301211 := bstep (se 1 (by rfl) ⟨225908, by rfl⟩ : syracuseStep 301211 = 451817) B451817
theorem B202907 : Blo 199806 202907 := bstep (se 1 (by rfl) ⟨152180, by rfl⟩ : syracuseStep 202907 = 304361) B304361
theorem B301247 : Blo 199806 301247 := bstep (se 1 (by rfl) ⟨225935, by rfl⟩ : syracuseStep 301247 = 451871) B451871
theorem B202943 : Blo 199806 202943 := bstep (se 1 (by rfl) ⟨152207, by rfl⟩ : syracuseStep 202943 = 304415) B304415
theorem B301289 : Blo 199806 301289 := bstep (se 2 (by rfl) ⟨112983, by rfl⟩ : syracuseStep 301289 = 225967) B225967
theorem B203055 : Blo 199806 203055 := bstep (se 1 (by rfl) ⟨152291, by rfl⟩ : syracuseStep 203055 = 304583) B304583
theorem B694601 : Blo 199806 694601 := bstep (se 2 (by rfl) ⟨260475, by rfl⟩ : syracuseStep 694601 = 520951) B520951
theorem B825707 : Blo 199806 825707 := bstep (se 1 (by rfl) ⟨619280, by rfl⟩ : syracuseStep 825707 = 1238561) B1238561
theorem B301595 : Blo 199806 301595 := bstep (se 1 (by rfl) ⟨226196, by rfl⟩ : syracuseStep 301595 = 452393) B452393
theorem B203291 : Blo 199806 203291 := bstep (se 1 (by rfl) ⟨152468, by rfl⟩ : syracuseStep 203291 = 304937) B304937
theorem B203295 : Blo 199806 203295 := bstep (se 1 (by rfl) ⟨152471, by rfl⟩ : syracuseStep 203295 = 304943) B304943
theorem B301673 : Blo 199806 301673 := bstep (se 2 (by rfl) ⟨113127, by rfl⟩ : syracuseStep 301673 = 226255) B226255
theorem B203611 : Blo 199806 203611 := bstep (se 1 (by rfl) ⟨152708, by rfl⟩ : syracuseStep 203611 = 305417) B305417
theorem B2464667 : Blo 199806 2464667 := bstep (se 1 (by rfl) ⟨1848500, by rfl⟩ : syracuseStep 2464667 = 3697001) B3697001
theorem B203679 : Blo 199806 203679 := bstep (se 1 (by rfl) ⟨152759, by rfl⟩ : syracuseStep 203679 = 305519) B305519
theorem B859081 : Blo 199806 859081 := bstep (se 2 (by rfl) ⟨322155, by rfl⟩ : syracuseStep 859081 = 644311) B644311
theorem B302201 : Blo 199806 302201 := bstep (se 2 (by rfl) ⟨113325, by rfl⟩ : syracuseStep 302201 = 226651) B226651
theorem B1023191 : Blo 199806 1023191 := bstep (se 1 (by rfl) ⟨767393, by rfl⟩ : syracuseStep 1023191 = 1534787) B1534787
theorem B302303 : Blo 199806 302303 := bstep (se 1 (by rfl) ⟨226727, by rfl⟩ : syracuseStep 302303 = 453455) B453455
theorem B302345 : Blo 199806 302345 := bstep (se 2 (by rfl) ⟨113379, by rfl⟩ : syracuseStep 302345 = 226759) B226759
theorem B761183 : Blo 199806 761183 := bstep (se 1 (by rfl) ⟨570887, by rfl⟩ : syracuseStep 761183 = 1141775) B1141775
theorem B302447 : Blo 199806 302447 := bstep (se 1 (by rfl) ⟨226835, by rfl⟩ : syracuseStep 302447 = 453671) B453671
theorem B302567 : Blo 199806 302567 := bstep (se 1 (by rfl) ⟨226925, by rfl⟩ : syracuseStep 302567 = 453851) B453851
theorem B302699 : Blo 199806 302699 := bstep (se 1 (by rfl) ⟨227024, by rfl⟩ : syracuseStep 302699 = 454049) B454049
theorem B302825 : Blo 199806 302825 := bstep (se 2 (by rfl) ⟨113559, by rfl⟩ : syracuseStep 302825 = 227119) B227119
theorem B302969 : Blo 199806 302969 := bstep (se 2 (by rfl) ⟨113613, by rfl⟩ : syracuseStep 302969 = 227227) B227227
theorem B303071 : Blo 199806 303071 := bstep (se 1 (by rfl) ⟨227303, by rfl⟩ : syracuseStep 303071 = 454607) B454607
theorem B303323 : Blo 199806 303323 := bstep (se 1 (by rfl) ⟨227492, by rfl⟩ : syracuseStep 303323 = 454985) B454985
theorem B303335 : Blo 199806 303335 := bstep (se 1 (by rfl) ⟨227501, by rfl⟩ : syracuseStep 303335 = 455003) B455003
theorem B5775731 : Blo 199806 5775731 := bstep (se 1 (by rfl) ⟨4331798, by rfl⟩ : syracuseStep 5775731 = 8663597) B8663597
theorem B303497 : Blo 199806 303497 := bstep (se 2 (by rfl) ⟨113811, by rfl⟩ : syracuseStep 303497 = 227623) B227623
theorem B303593 : Blo 199806 303593 := bstep (se 2 (by rfl) ⟨113847, by rfl⟩ : syracuseStep 303593 = 227695) B227695
theorem B1286675 : Blo 199806 1286675 := bstep (se 1 (by rfl) ⟨965006, by rfl⟩ : syracuseStep 1286675 = 1930013) B1930013
theorem B303719 : Blo 199806 303719 := bstep (se 1 (by rfl) ⟨227789, by rfl⟩ : syracuseStep 303719 = 455579) B455579
theorem B303851 : Blo 199806 303851 := bstep (se 1 (by rfl) ⟨227888, by rfl⟩ : syracuseStep 303851 = 455777) B455777
theorem B303881 : Blo 199806 303881 := bstep (se 2 (by rfl) ⟨113955, by rfl⟩ : syracuseStep 303881 = 227911) B227911
theorem B303983 : Blo 199806 303983 := bstep (se 1 (by rfl) ⟨227987, by rfl⟩ : syracuseStep 303983 = 455975) B455975
theorem B271355 : Blo 199806 271355 := bstep (se 1 (by rfl) ⟨203516, by rfl⟩ : syracuseStep 271355 = 407033) B407033
theorem B304235 : Blo 199806 304235 := bstep (se 1 (by rfl) ⟨228176, by rfl⟩ : syracuseStep 304235 = 456353) B456353
theorem B23635115 : Blo 199806 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B1942775 : Blo 199806 1942775 := bstep (se 1 (by rfl) ⟨1457081, by rfl⟩ : syracuseStep 1942775 = 2914163) B2914163
theorem B337243 : Blo 199806 337243 := bstep (se 1 (by rfl) ⟨252932, by rfl⟩ : syracuseStep 337243 = 505865) B505865
theorem B304475 : Blo 199806 304475 := bstep (se 1 (by rfl) ⟨228356, by rfl⟩ : syracuseStep 304475 = 456713) B456713
theorem B304751 : Blo 199806 304751 := bstep (se 1 (by rfl) ⟨228563, by rfl⟩ : syracuseStep 304751 = 457127) B457127
theorem B304823 : Blo 199806 304823 := bstep (se 1 (by rfl) ⟨228617, by rfl⟩ : syracuseStep 304823 = 457235) B457235
theorem B304859 : Blo 199806 304859 := bstep (se 1 (by rfl) ⟨228644, by rfl⟩ : syracuseStep 304859 = 457289) B457289
theorem B305033 : Blo 199806 305033 := bstep (se 2 (by rfl) ⟨114387, by rfl⟩ : syracuseStep 305033 = 228775) B228775
theorem B305135 : Blo 199806 305135 := bstep (se 1 (by rfl) ⟨228851, by rfl⟩ : syracuseStep 305135 = 457703) B457703
theorem B305387 : Blo 199806 305387 := bstep (se 1 (by rfl) ⟨229040, by rfl⟩ : syracuseStep 305387 = 458081) B458081
theorem B338215 : Blo 199806 338215 := bstep (se 1 (by rfl) ⟨253661, by rfl⟩ : syracuseStep 338215 = 507323) B507323
theorem B305447 : Blo 199806 305447 := bstep (se 1 (by rfl) ⟨229085, by rfl⟩ : syracuseStep 305447 = 458171) B458171
theorem B305531 : Blo 199806 305531 := bstep (se 1 (by rfl) ⟨229148, by rfl⟩ : syracuseStep 305531 = 458297) B458297
theorem B764417 : Blo 199806 764417 := bstep (se 2 (by rfl) ⟨286656, by rfl⟩ : syracuseStep 764417 = 573313) B573313
theorem B1518263 : Blo 199806 1518263 := bstep (se 1 (by rfl) ⟨1138697, by rfl⟩ : syracuseStep 1518263 = 2277395) B2277395
theorem B764599 : Blo 199806 764599 := bstep (se 1 (by rfl) ⟨573449, by rfl⟩ : syracuseStep 764599 = 1146899) B1146899
theorem B1027079 : Blo 199806 1027079 := bstep (se 1 (by rfl) ⟨770309, by rfl⟩ : syracuseStep 1027079 = 1540619) B1540619
theorem B2927663 : Blo 199806 2927663 := bstep (se 1 (by rfl) ⟨2195747, by rfl⟩ : syracuseStep 2927663 = 4391495) B4391495
theorem B765071 : Blo 199806 765071 := bstep (se 1 (by rfl) ⟨573803, by rfl⟩ : syracuseStep 765071 = 1147607) B1147607
theorem B5024987 : Blo 199806 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B339167 : Blo 199806 339167 := bstep (se 1 (by rfl) ⟨254375, by rfl⟩ : syracuseStep 339167 = 508751) B508751
theorem B339599 : Blo 199806 339599 := bstep (se 1 (by rfl) ⟨254699, by rfl⟩ : syracuseStep 339599 = 509399) B509399
theorem B1159019 : Blo 199806 1159019 := bstep (se 1 (by rfl) ⟨869264, by rfl⟩ : syracuseStep 1159019 = 1738529) B1738529
theorem B339835 : Blo 199806 339835 := bstep (se 1 (by rfl) ⟨254876, by rfl⟩ : syracuseStep 339835 = 509753) B509753
theorem B569531 : Blo 199806 569531 := bstep (se 1 (by rfl) ⟨427148, by rfl⟩ : syracuseStep 569531 = 854297) B854297
theorem B4141313 : Blo 199806 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B405815 : Blo 199806 405815 := bstep (se 1 (by rfl) ⟨304361, by rfl⟩ : syracuseStep 405815 = 608723) B608723
theorem B2568581 : Blo 199806 2568581 := bstep (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) B481609
theorem B1290725 : Blo 199806 1290725 := bstep (se 4 (by rfl) ⟨121005, by rfl⟩ : syracuseStep 1290725 = 242011) B242011
theorem B1029437 : Blo 199806 1029437 := bstep (se 3 (by rfl) ⟨193019, by rfl⟩ : syracuseStep 1029437 = 386039) B386039
theorem B341671 : Blo 199806 341671 := bstep (se 1 (by rfl) ⟨256253, by rfl⟩ : syracuseStep 341671 = 512507) B512507
theorem B931537 : Blo 199806 931537 := bstep (se 2 (by rfl) ⟨349326, by rfl⟩ : syracuseStep 931537 = 698653) B698653
theorem B866447 : Blo 199806 866447 := bstep (se 1 (by rfl) ⟨649835, by rfl⟩ : syracuseStep 866447 = 1299671) B1299671
theorem B1128701 : Blo 199806 1128701 := bstep (se 3 (by rfl) ⟨211631, by rfl⟩ : syracuseStep 1128701 = 423263) B423263
theorem B342319 : Blo 199806 342319 := bstep (se 1 (by rfl) ⟨256739, by rfl⟩ : syracuseStep 342319 = 513479) B513479
theorem B277129 : Blo 199806 277129 := bstep (se 2 (by rfl) ⟨103923, by rfl⟩ : syracuseStep 277129 = 207847) B207847
theorem B342839 : Blo 199806 342839 := bstep (se 1 (by rfl) ⟨257129, by rfl⟩ : syracuseStep 342839 = 514259) B514259
theorem B7715735 : Blo 199806 7715735 := bstep (se 1 (by rfl) ⟨5786801, by rfl⟩ : syracuseStep 7715735 = 11573603) B11573603
theorem B1391525 : Blo 199806 1391525 := bstep (se 4 (by rfl) ⟨130455, by rfl⟩ : syracuseStep 1391525 = 260911) B260911
theorem B1031453 : Blo 199806 1031453 := bstep (se 3 (by rfl) ⟨193397, by rfl⟩ : syracuseStep 1031453 = 386795) B386795
theorem B867689 : Blo 199806 867689 := bstep (se 2 (by rfl) ⟨325383, by rfl⟩ : syracuseStep 867689 = 650767) B650767
theorem B572903 : Blo 199806 572903 := bstep (se 1 (by rfl) ⟨429677, by rfl⟩ : syracuseStep 572903 = 859355) B859355
theorem B343615 : Blo 199806 343615 := bstep (se 1 (by rfl) ⟨257711, by rfl⟩ : syracuseStep 343615 = 515423) B515423
theorem B6602417 : Blo 199806 6602417 := bstep (se 2 (by rfl) ⟨2475906, by rfl⟩ : syracuseStep 6602417 = 4951813) B4951813
theorem B507617 : Blo 199806 507617 := bstep (se 2 (by rfl) ⟨190356, by rfl⟩ : syracuseStep 507617 = 380713) B380713
theorem B213455 : Blo 199806 213455 := bstep (se 1 (by rfl) ⟨160091, by rfl⟩ : syracuseStep 213455 = 320183) B320183
theorem B573929 : Blo 199806 573929 := bstep (se 2 (by rfl) ⟨215223, by rfl⟩ : syracuseStep 573929 = 430447) B430447
theorem B770735 : Blo 199806 770735 := bstep (se 1 (by rfl) ⟨578051, by rfl⟩ : syracuseStep 770735 = 1156103) B1156103
theorem B869059 : Blo 199806 869059 := bstep (se 1 (by rfl) ⟨651794, by rfl⟩ : syracuseStep 869059 = 1303589) B1303589
theorem B869129 : Blo 199806 869129 := bstep (se 2 (by rfl) ⟨325923, by rfl⟩ : syracuseStep 869129 = 651847) B651847
theorem B410729 : Blo 199806 410729 := bstep (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) B308047
theorem B509561 : Blo 199806 509561 := bstep (se 2 (by rfl) ⟨191085, by rfl⟩ : syracuseStep 509561 = 382171) B382171
theorem B640673 : Blo 199806 640673 := bstep (se 2 (by rfl) ⟨240252, by rfl⟩ : syracuseStep 640673 = 480505) B480505
theorem B1165117 : Blo 199806 1165117 := bstep (se 3 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 1165117 = 436919) B436919
theorem B641441 : Blo 199806 641441 := bstep (se 2 (by rfl) ⟨240540, by rfl⟩ : syracuseStep 641441 = 481081) B481081
theorem B5130701 : Blo 199806 5130701 := bstep (se 3 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 5130701 = 1924013) B1924013
theorem B379703 : Blo 199806 379703 := bstep (se 1 (by rfl) ⟨284777, by rfl⟩ : syracuseStep 379703 = 569555) B569555
theorem B347087 : Blo 199806 347087 := bstep (se 1 (by rfl) ⟨260315, by rfl⟩ : syracuseStep 347087 = 520631) B520631
theorem B675323 : Blo 199806 675323 := bstep (se 1 (by rfl) ⟨506492, by rfl⟩ : syracuseStep 675323 = 1012985) B1012985
theorem B675485 : Blo 199806 675485 := bstep (se 3 (by rfl) ⟨126653, by rfl⟩ : syracuseStep 675485 = 253307) B253307
theorem B2445203 : Blo 199806 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B676025 : Blo 199806 676025 := bstep (se 2 (by rfl) ⟨253509, by rfl⟩ : syracuseStep 676025 = 507019) B507019
theorem B381115 : Blo 199806 381115 := bstep (se 1 (by rfl) ⟨285836, by rfl⟩ : syracuseStep 381115 = 571673) B571673
theorem B1724723 : Blo 199806 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B577847 : Blo 199806 577847 := bstep (se 1 (by rfl) ⟨433385, by rfl⟩ : syracuseStep 577847 = 866771) B866771
theorem B971119 : Blo 199806 971119 := bstep (se 1 (by rfl) ⟨728339, by rfl⟩ : syracuseStep 971119 = 1456679) B1456679
theorem B381601 : Blo 199806 381601 := bstep (se 2 (by rfl) ⟨143100, by rfl⟩ : syracuseStep 381601 = 286201) B286201
theorem B1462967 : Blo 199806 1462967 := bstep (se 1 (by rfl) ⟨1097225, by rfl⟩ : syracuseStep 1462967 = 2194451) B2194451
theorem B2315303 : Blo 199806 2315303 := bstep (se 1 (by rfl) ⟨1736477, by rfl⟩ : syracuseStep 2315303 = 3472955) B3472955
theorem B578735 : Blo 199806 578735 := bstep (se 1 (by rfl) ⟨434051, by rfl⟩ : syracuseStep 578735 = 868103) B868103
theorem B7755101 : Blo 199806 7755101 := bstep (se 3 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 7755101 = 2908163) B2908163
theorem B383059 : Blo 199806 383059 := bstep (se 1 (by rfl) ⟨287294, by rfl⟩ : syracuseStep 383059 = 574589) B574589
theorem B678131 : Blo 199806 678131 := bstep (se 1 (by rfl) ⟨508598, by rfl⟩ : syracuseStep 678131 = 1017197) B1017197
theorem B678185 : Blo 199806 678185 := bstep (se 2 (by rfl) ⟨254319, by rfl⟩ : syracuseStep 678185 = 508639) B508639
theorem B1301129 : Blo 199806 1301129 := bstep (se 2 (by rfl) ⟨487923, by rfl⟩ : syracuseStep 1301129 = 975847) B975847
theorem B514907 : Blo 199806 514907 := bstep (se 1 (by rfl) ⟨386180, by rfl⟩ : syracuseStep 514907 = 772361) B772361
theorem B449801 : Blo 199806 449801 := bstep (se 2 (by rfl) ⟨168675, by rfl⟩ : syracuseStep 449801 = 337351) B337351
theorem B1138151 : Blo 199806 1138151 := bstep (se 1 (by rfl) ⟨853613, by rfl⟩ : syracuseStep 1138151 = 1707227) B1707227
theorem B384745 : Blo 199806 384745 := bstep (se 2 (by rfl) ⟨144279, by rfl⟩ : syracuseStep 384745 = 288559) B288559
theorem B679751 : Blo 199806 679751 := bstep (se 1 (by rfl) ⟨509813, by rfl⟩ : syracuseStep 679751 = 1019627) B1019627
theorem B679805 : Blo 199806 679805 := bstep (se 3 (by rfl) ⟨127463, by rfl⟩ : syracuseStep 679805 = 254927) B254927
theorem B680075 : Blo 199806 680075 := bstep (se 1 (by rfl) ⟨510056, by rfl⟩ : syracuseStep 680075 = 1020113) B1020113
theorem B1138859 : Blo 199806 1138859 := bstep (se 1 (by rfl) ⟨854144, by rfl⟩ : syracuseStep 1138859 = 1708289) B1708289
theorem B450791 : Blo 199806 450791 := bstep (se 1 (by rfl) ⟨338093, by rfl⟩ : syracuseStep 450791 = 676187) B676187
theorem B1073533 : Blo 199806 1073533 := bstep (se 3 (by rfl) ⟨201287, by rfl⟩ : syracuseStep 1073533 = 402575) B402575
theorem B254335 : Blo 199806 254335 := bstep (se 1 (by rfl) ⟨190751, by rfl⟩ : syracuseStep 254335 = 381503) B381503
theorem B680399 : Blo 199806 680399 := bstep (se 1 (by rfl) ⟨510299, by rfl⟩ : syracuseStep 680399 = 1020599) B1020599
theorem B680723 : Blo 199806 680723 := bstep (se 1 (by rfl) ⟨510542, by rfl⟩ : syracuseStep 680723 = 1021085) B1021085
theorem B451385 : Blo 199806 451385 := bstep (se 2 (by rfl) ⟨169269, by rfl⟩ : syracuseStep 451385 = 338539) B338539
theorem B451439 : Blo 199806 451439 := bstep (se 1 (by rfl) ⟨338579, by rfl⟩ : syracuseStep 451439 = 677159) B677159
theorem B9757847 : Blo 199806 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B3957923 : Blo 199806 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B779453 : Blo 199806 779453 := bstep (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) B292295
theorem B1303847 : Blo 199806 1303847 := bstep (se 1 (by rfl) ⟨977885, by rfl⟩ : syracuseStep 1303847 = 1955771) B1955771
theorem B320939 : Blo 199806 320939 := bstep (se 1 (by rfl) ⟨240704, by rfl⟩ : syracuseStep 320939 = 481409) B481409
theorem B452015 : Blo 199806 452015 := bstep (se 1 (by rfl) ⟨339011, by rfl⟩ : syracuseStep 452015 = 678023) B678023
theorem B681587 : Blo 199806 681587 := bstep (se 1 (by rfl) ⟨511190, by rfl⟩ : syracuseStep 681587 = 1022381) B1022381
theorem B681695 : Blo 199806 681695 := bstep (se 1 (by rfl) ⟨511271, by rfl⟩ : syracuseStep 681695 = 1022543) B1022543
theorem B288479 : Blo 199806 288479 := bstep (se 1 (by rfl) ⟨216359, by rfl⟩ : syracuseStep 288479 = 432719) B432719
theorem B681857 : Blo 199806 681857 := bstep (se 2 (by rfl) ⟨255696, by rfl⟩ : syracuseStep 681857 = 511393) B511393
theorem B452843 : Blo 199806 452843 := bstep (se 1 (by rfl) ⟨339632, by rfl⟩ : syracuseStep 452843 = 679265) B679265
theorem B289003 : Blo 199806 289003 := bstep (se 1 (by rfl) ⟨216752, by rfl⟩ : syracuseStep 289003 = 433505) B433505
theorem B649529 : Blo 199806 649529 := bstep (se 2 (by rfl) ⟨243573, by rfl⟩ : syracuseStep 649529 = 487147) B487147
theorem B682397 : Blo 199806 682397 := bstep (se 3 (by rfl) ⟨127949, by rfl⟩ : syracuseStep 682397 = 255899) B255899
theorem B1141249 : Blo 199806 1141249 := bstep (se 2 (by rfl) ⟨427968, by rfl⟩ : syracuseStep 1141249 = 855937) B855937
theorem B485993 : Blo 199806 485993 := bstep (se 2 (by rfl) ⟨182247, by rfl⟩ : syracuseStep 485993 = 364495) B364495
theorem B682667 : Blo 199806 682667 := bstep (se 1 (by rfl) ⟨512000, by rfl⟩ : syracuseStep 682667 = 1024001) B1024001
theorem B256927 : Blo 199806 256927 := bstep (se 1 (by rfl) ⟨192695, by rfl⟩ : syracuseStep 256927 = 385391) B385391
theorem B683207 : Blo 199806 683207 := bstep (se 1 (by rfl) ⟨512405, by rfl⟩ : syracuseStep 683207 = 1024811) B1024811
theorem B1305821 : Blo 199806 1305821 := bstep (se 3 (by rfl) ⟨244841, by rfl⟩ : syracuseStep 1305821 = 489683) B489683
theorem B2289059 : Blo 199806 2289059 := bstep (se 1 (by rfl) ⟨1716794, by rfl⟩ : syracuseStep 2289059 = 3433589) B3433589
theorem B454139 : Blo 199806 454139 := bstep (se 1 (by rfl) ⟨340604, by rfl⟩ : syracuseStep 454139 = 681209) B681209
theorem B454319 : Blo 199806 454319 := bstep (se 1 (by rfl) ⟨340739, by rfl⟩ : syracuseStep 454319 = 681479) B681479
theorem B323399 : Blo 199806 323399 := bstep (se 1 (by rfl) ⟨242549, by rfl⟩ : syracuseStep 323399 = 485099) B485099
theorem B225247 : Blo 199806 225247 := bstep (se 1 (by rfl) ⟨168935, by rfl⟩ : syracuseStep 225247 = 337871) B337871
theorem B618625 : Blo 199806 618625 := bstep (se 2 (by rfl) ⟨231984, by rfl⟩ : syracuseStep 618625 = 463969) B463969
theorem B454967 : Blo 199806 454967 := bstep (se 1 (by rfl) ⟨341225, by rfl⟩ : syracuseStep 454967 = 682451) B682451
theorem B455039 : Blo 199806 455039 := bstep (se 1 (by rfl) ⟨341279, by rfl⟩ : syracuseStep 455039 = 682559) B682559
theorem B684503 : Blo 199806 684503 := bstep (se 1 (by rfl) ⟨513377, by rfl⟩ : syracuseStep 684503 = 1026755) B1026755
theorem B225895 : Blo 199806 225895 := bstep (se 1 (by rfl) ⟨169421, by rfl⟩ : syracuseStep 225895 = 338843) B338843
theorem B2880485 : Blo 199806 2880485 := bstep (se 4 (by rfl) ⟨270045, by rfl⟩ : syracuseStep 2880485 = 540091) B540091
theorem B324815 : Blo 199806 324815 := bstep (se 1 (by rfl) ⟨243611, by rfl⟩ : syracuseStep 324815 = 487223) B487223
theorem B292187 : Blo 199806 292187 := bstep (se 1 (by rfl) ⟨219140, by rfl⟩ : syracuseStep 292187 = 438281) B438281
theorem B685403 : Blo 199806 685403 := bstep (se 1 (by rfl) ⟨514052, by rfl⟩ : syracuseStep 685403 = 1028105) B1028105
theorem B1013147 : Blo 199806 1013147 := bstep (se 1 (by rfl) ⟨759860, by rfl⟩ : syracuseStep 1013147 = 1519721) B1519721
theorem B652769 : Blo 199806 652769 := bstep (se 2 (by rfl) ⟨244788, by rfl⟩ : syracuseStep 652769 = 489577) B489577
theorem B1832519 : Blo 199806 1832519 := bstep (se 1 (by rfl) ⟨1374389, by rfl⟩ : syracuseStep 1832519 = 2748779) B2748779
theorem B456263 : Blo 199806 456263 := bstep (se 1 (by rfl) ⟨342197, by rfl⟩ : syracuseStep 456263 = 684395) B684395
theorem B456443 : Blo 199806 456443 := bstep (se 1 (by rfl) ⟨342332, by rfl⟩ : syracuseStep 456443 = 684665) B684665
theorem B685961 : Blo 199806 685961 := bstep (se 2 (by rfl) ⟨257235, by rfl⟩ : syracuseStep 685961 = 514471) B514471
theorem B686177 : Blo 199806 686177 := bstep (se 2 (by rfl) ⟨257316, by rfl⟩ : syracuseStep 686177 = 514633) B514633
theorem B2291975 : Blo 199806 2291975 := bstep (se 1 (by rfl) ⟨1718981, by rfl⟩ : syracuseStep 2291975 = 3437963) B3437963
theorem B457001 : Blo 199806 457001 := bstep (se 2 (by rfl) ⟨171375, by rfl⟩ : syracuseStep 457001 = 342751) B342751
theorem B1145623 : Blo 199806 1145623 := bstep (se 1 (by rfl) ⟨859217, by rfl⟩ : syracuseStep 1145623 = 1718435) B1718435
theorem B457577 : Blo 199806 457577 := bstep (se 2 (by rfl) ⟨171591, by rfl⟩ : syracuseStep 457577 = 343183) B343183
theorem B457631 : Blo 199806 457631 := bstep (se 1 (by rfl) ⟨343223, by rfl⟩ : syracuseStep 457631 = 686447) B686447
theorem B687095 : Blo 199806 687095 := bstep (se 1 (by rfl) ⟨515321, by rfl⟩ : syracuseStep 687095 = 1030643) B1030643
theorem B1145897 : Blo 199806 1145897 := bstep (se 2 (by rfl) ⟨429711, by rfl⟩ : syracuseStep 1145897 = 859423) B859423
theorem B1539161 : Blo 199806 1539161 := bstep (se 2 (by rfl) ⟨577185, by rfl⟩ : syracuseStep 1539161 = 1154371) B1154371
theorem B818441 : Blo 199806 818441 := bstep (se 2 (by rfl) ⟨306915, by rfl⟩ : syracuseStep 818441 = 613831) B613831
theorem B687527 : Blo 199806 687527 := bstep (se 1 (by rfl) ⟨515645, by rfl⟩ : syracuseStep 687527 = 1031291) B1031291
theorem B228955 : Blo 199806 228955 := bstep (se 1 (by rfl) ⟨171716, by rfl⟩ : syracuseStep 228955 = 343433) B343433
theorem B720571 : Blo 199806 720571 := bstep (se 1 (by rfl) ⟨540428, by rfl⟩ : syracuseStep 720571 = 1080857) B1080857
theorem B229243 : Blo 199806 229243 := bstep (se 1 (by rfl) ⟨171932, by rfl⟩ : syracuseStep 229243 = 343865) B343865
theorem B2162875 : Blo 199806 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B1082173 : Blo 199806 1082173 := bstep (se 3 (by rfl) ⟨202907, by rfl⟩ : syracuseStep 1082173 = 405815) B405815
theorem B427115 : Blo 199806 427115 := bstep (se 1 (by rfl) ⟨320336, by rfl⟩ : syracuseStep 427115 = 640673) B640673
theorem B1443359 : Blo 199806 1443359 := bstep (se 1 (by rfl) ⟨1082519, by rfl⟩ : syracuseStep 1443359 = 2165039) B2165039
theorem B427627 : Blo 199806 427627 := bstep (se 1 (by rfl) ⟨320720, by rfl⟩ : syracuseStep 427627 = 641441) B641441
theorem B231391 : Blo 199806 231391 := bstep (se 1 (by rfl) ⟨173543, by rfl⟩ : syracuseStep 231391 = 347087) B347087
theorem B460831 : Blo 199806 460831 := bstep (se 1 (by rfl) ⟨345623, by rfl⟩ : syracuseStep 460831 = 691247) B691247
theorem B1411181 : Blo 199806 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B1640843 : Blo 199806 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B723613 : Blo 199806 723613 := bstep (se 3 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 723613 = 271355) B271355
theorem B1149815 : Blo 199806 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B920639 : Blo 199806 920639 := bstep (se 1 (by rfl) ⟨690479, by rfl⟩ : syracuseStep 920639 = 1380959) B1380959
theorem B1543535 : Blo 199806 1543535 := bstep (se 1 (by rfl) ⟨1157651, by rfl⟩ : syracuseStep 1543535 = 2315303) B2315303
theorem B200063 : Blo 199806 200063 := bstep (se 1 (by rfl) ⟨150047, by rfl⟩ : syracuseStep 200063 = 300095) B300095
theorem B200091 : Blo 199806 200091 := bstep (se 1 (by rfl) ⟨150068, by rfl⟩ : syracuseStep 200091 = 300137) B300137
theorem B200159 : Blo 199806 200159 := bstep (se 1 (by rfl) ⟨150119, by rfl⟩ : syracuseStep 200159 = 300239) B300239
theorem B1019465 : Blo 199806 1019465 := bstep (se 2 (by rfl) ⟨382299, by rfl⟩ : syracuseStep 1019465 = 764599) B764599
theorem B200295 : Blo 199806 200295 := bstep (se 1 (by rfl) ⟨150221, by rfl⟩ : syracuseStep 200295 = 300443) B300443
theorem B200443 : Blo 199806 200443 := bstep (se 1 (by rfl) ⟨150332, by rfl⟩ : syracuseStep 200443 = 300665) B300665
theorem B200511 : Blo 199806 200511 := bstep (se 1 (by rfl) ⟨150383, by rfl⟩ : syracuseStep 200511 = 300767) B300767
theorem B200575 : Blo 199806 200575 := bstep (se 1 (by rfl) ⟨150431, by rfl⟩ : syracuseStep 200575 = 300863) B300863
theorem B200687 : Blo 199806 200687 := bstep (se 1 (by rfl) ⟨150515, by rfl⟩ : syracuseStep 200687 = 301031) B301031
theorem B200699 : Blo 199806 200699 := bstep (se 1 (by rfl) ⟨150524, by rfl⟩ : syracuseStep 200699 = 301049) B301049
theorem B200767 : Blo 199806 200767 := bstep (se 1 (by rfl) ⟨150575, by rfl⟩ : syracuseStep 200767 = 301151) B301151
theorem B200807 : Blo 199806 200807 := bstep (se 1 (by rfl) ⟨150605, by rfl⟩ : syracuseStep 200807 = 301211) B301211
theorem B200831 : Blo 199806 200831 := bstep (se 1 (by rfl) ⟨150623, by rfl⟩ : syracuseStep 200831 = 301247) B301247
theorem B200859 : Blo 199806 200859 := bstep (se 1 (by rfl) ⟨150644, by rfl⟩ : syracuseStep 200859 = 301289) B301289
theorem B463067 : Blo 199806 463067 := bstep (se 1 (by rfl) ⟨347300, by rfl⟩ : syracuseStep 463067 = 694601) B694601
theorem B201063 : Blo 199806 201063 := bstep (se 1 (by rfl) ⟨150797, by rfl⟩ : syracuseStep 201063 = 301595) B301595
theorem B201115 : Blo 199806 201115 := bstep (se 1 (by rfl) ⟨150836, by rfl⟩ : syracuseStep 201115 = 301673) B301673
theorem B1643111 : Blo 199806 1643111 := bstep (se 1 (by rfl) ⟨1232333, by rfl⟩ : syracuseStep 1643111 = 2464667) B2464667
theorem B201467 : Blo 199806 201467 := bstep (se 1 (by rfl) ⟨151100, by rfl⟩ : syracuseStep 201467 = 302201) B302201
theorem B201535 : Blo 199806 201535 := bstep (se 1 (by rfl) ⟨151151, by rfl⟩ : syracuseStep 201535 = 302303) B302303
theorem B299867 : Blo 199806 299867 := bstep (se 1 (by rfl) ⟨224900, by rfl⟩ : syracuseStep 299867 = 449801) B449801
theorem B201563 : Blo 199806 201563 := bstep (se 1 (by rfl) ⟨151172, by rfl⟩ : syracuseStep 201563 = 302345) B302345
theorem B201631 : Blo 199806 201631 := bstep (se 1 (by rfl) ⟨151223, by rfl⟩ : syracuseStep 201631 = 302447) B302447
theorem B758767 : Blo 199806 758767 := bstep (se 1 (by rfl) ⟨569075, by rfl⟩ : syracuseStep 758767 = 1138151) B1138151
theorem B201711 : Blo 199806 201711 := bstep (se 1 (by rfl) ⟨151283, by rfl⟩ : syracuseStep 201711 = 302567) B302567
theorem B201799 : Blo 199806 201799 := bstep (se 1 (by rfl) ⟨151349, by rfl⟩ : syracuseStep 201799 = 302699) B302699
theorem B201883 : Blo 199806 201883 := bstep (se 1 (by rfl) ⟨151412, by rfl⟩ : syracuseStep 201883 = 302825) B302825
theorem B201979 : Blo 199806 201979 := bstep (se 1 (by rfl) ⟨151484, by rfl⟩ : syracuseStep 201979 = 302969) B302969
theorem B300329 : Blo 199806 300329 := bstep (se 2 (by rfl) ⟨112623, by rfl⟩ : syracuseStep 300329 = 225247) B225247
theorem B202047 : Blo 199806 202047 := bstep (se 1 (by rfl) ⟨151535, by rfl⟩ : syracuseStep 202047 = 303071) B303071
theorem B759239 : Blo 199806 759239 := bstep (se 1 (by rfl) ⟨569429, by rfl⟩ : syracuseStep 759239 = 1138859) B1138859
theorem B202215 : Blo 199806 202215 := bstep (se 1 (by rfl) ⟨151661, by rfl⟩ : syracuseStep 202215 = 303323) B303323
theorem B300527 : Blo 199806 300527 := bstep (se 1 (by rfl) ⟨225395, by rfl⟩ : syracuseStep 300527 = 450791) B450791
theorem B202223 : Blo 199806 202223 := bstep (se 1 (by rfl) ⟨151667, by rfl⟩ : syracuseStep 202223 = 303335) B303335
theorem B824833 : Blo 199806 824833 := bstep (se 2 (by rfl) ⟨309312, by rfl⟩ : syracuseStep 824833 = 618625) B618625
theorem B202331 : Blo 199806 202331 := bstep (se 1 (by rfl) ⟨151748, by rfl⟩ : syracuseStep 202331 = 303497) B303497
theorem B202395 : Blo 199806 202395 := bstep (se 1 (by rfl) ⟨151796, by rfl⟩ : syracuseStep 202395 = 303593) B303593
theorem B857783 : Blo 199806 857783 := bstep (se 1 (by rfl) ⟨643337, by rfl⟩ : syracuseStep 857783 = 1286675) B1286675
theorem B202479 : Blo 199806 202479 := bstep (se 1 (by rfl) ⟨151859, by rfl⟩ : syracuseStep 202479 = 303719) B303719
theorem B3151673 : Blo 199806 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B202567 : Blo 199806 202567 := bstep (se 1 (by rfl) ⟨151925, by rfl⟩ : syracuseStep 202567 = 303851) B303851
theorem B202587 : Blo 199806 202587 := bstep (se 1 (by rfl) ⟨151940, by rfl⟩ : syracuseStep 202587 = 303881) B303881
theorem B300923 : Blo 199806 300923 := bstep (se 1 (by rfl) ⟨225692, by rfl⟩ : syracuseStep 300923 = 451385) B451385
theorem B300959 : Blo 199806 300959 := bstep (se 1 (by rfl) ⟨225719, by rfl⟩ : syracuseStep 300959 = 451439) B451439
theorem B202655 : Blo 199806 202655 := bstep (se 1 (by rfl) ⟨151991, by rfl⟩ : syracuseStep 202655 = 303983) B303983
theorem B202823 : Blo 199806 202823 := bstep (se 1 (by rfl) ⟨152117, by rfl⟩ : syracuseStep 202823 = 304235) B304235
theorem B301193 : Blo 199806 301193 := bstep (se 2 (by rfl) ⟨112947, by rfl⟩ : syracuseStep 301193 = 225895) B225895
theorem B202983 : Blo 199806 202983 := bstep (se 1 (by rfl) ⟨152237, by rfl⟩ : syracuseStep 202983 = 304475) B304475
theorem B301343 : Blo 199806 301343 := bstep (se 1 (by rfl) ⟨226007, by rfl⟩ : syracuseStep 301343 = 452015) B452015
theorem B203167 : Blo 199806 203167 := bstep (se 1 (by rfl) ⟨152375, by rfl⟩ : syracuseStep 203167 = 304751) B304751
theorem B203215 : Blo 199806 203215 := bstep (se 1 (by rfl) ⟨152411, by rfl⟩ : syracuseStep 203215 = 304823) B304823
theorem B203239 : Blo 199806 203239 := bstep (se 1 (by rfl) ⟨152429, by rfl⟩ : syracuseStep 203239 = 304859) B304859
theorem B203355 : Blo 199806 203355 := bstep (se 1 (by rfl) ⟨152516, by rfl⟩ : syracuseStep 203355 = 305033) B305033
theorem B203423 : Blo 199806 203423 := bstep (se 1 (by rfl) ⟨152567, by rfl⟩ : syracuseStep 203423 = 305135) B305135
theorem B301895 : Blo 199806 301895 := bstep (se 1 (by rfl) ⟨226421, by rfl⟩ : syracuseStep 301895 = 452843) B452843
theorem B203591 : Blo 199806 203591 := bstep (se 1 (by rfl) ⟨152693, by rfl⟩ : syracuseStep 203591 = 305387) B305387
theorem B203631 : Blo 199806 203631 := bstep (se 1 (by rfl) ⟨152723, by rfl⟩ : syracuseStep 203631 = 305447) B305447
theorem B433019 : Blo 199806 433019 := bstep (se 1 (by rfl) ⟨324764, by rfl⟩ : syracuseStep 433019 = 649529) B649529
theorem B203687 : Blo 199806 203687 := bstep (se 1 (by rfl) ⟨152765, by rfl⟩ : syracuseStep 203687 = 305531) B305531
theorem B3349991 : Blo 199806 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B302759 : Blo 199806 302759 := bstep (se 1 (by rfl) ⟨227069, by rfl⟩ : syracuseStep 302759 = 454139) B454139
theorem B302879 : Blo 199806 302879 := bstep (se 1 (by rfl) ⟨227159, by rfl⟩ : syracuseStep 302879 = 454319) B454319
theorem B2760875 : Blo 199806 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B303311 : Blo 199806 303311 := bstep (se 1 (by rfl) ⟨227483, by rfl⟩ : syracuseStep 303311 = 454967) B454967
theorem B303359 : Blo 199806 303359 := bstep (se 1 (by rfl) ⟨227519, by rfl⟩ : syracuseStep 303359 = 455039) B455039
theorem B1712387 : Blo 199806 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B860483 : Blo 199806 860483 := bstep (se 1 (by rfl) ⟨645362, by rfl⟩ : syracuseStep 860483 = 1290725) B1290725
theorem B369505 : Blo 199806 369505 := bstep (se 2 (by rfl) ⟨138564, by rfl⟩ : syracuseStep 369505 = 277129) B277129
theorem B435179 : Blo 199806 435179 := bstep (se 1 (by rfl) ⟨326384, by rfl⟩ : syracuseStep 435179 = 652769) B652769
theorem B1221679 : Blo 199806 1221679 := bstep (se 1 (by rfl) ⟨916259, by rfl⟩ : syracuseStep 1221679 = 1832519) B1832519
theorem B304175 : Blo 199806 304175 := bstep (se 1 (by rfl) ⟨228131, by rfl⟩ : syracuseStep 304175 = 456263) B456263
theorem B304295 : Blo 199806 304295 := bstep (se 1 (by rfl) ⟨228221, by rfl⟩ : syracuseStep 304295 = 456443) B456443
theorem B304667 : Blo 199806 304667 := bstep (se 1 (by rfl) ⟨228500, by rfl⟩ : syracuseStep 304667 = 457001) B457001
theorem B305051 : Blo 199806 305051 := bstep (se 1 (by rfl) ⟨228788, by rfl⟩ : syracuseStep 305051 = 457577) B457577
theorem B305087 : Blo 199806 305087 := bstep (se 1 (by rfl) ⟨228815, by rfl⟩ : syracuseStep 305087 = 457631) B457631
theorem B927683 : Blo 199806 927683 := bstep (se 1 (by rfl) ⟨695762, by rfl⟩ : syracuseStep 927683 = 1391525) B1391525
theorem B763931 : Blo 199806 763931 := bstep (se 1 (by rfl) ⟨572948, by rfl⟩ : syracuseStep 763931 = 1145897) B1145897
theorem B1026107 : Blo 199806 1026107 := bstep (se 1 (by rfl) ⟨769580, by rfl⟩ : syracuseStep 1026107 = 1539161) B1539161
theorem B305273 : Blo 199806 305273 := bstep (se 2 (by rfl) ⟨114477, by rfl⟩ : syracuseStep 305273 = 228955) B228955
theorem B862397 : Blo 199806 862397 := bstep (se 3 (by rfl) ⟨161699, by rfl⟩ : syracuseStep 862397 = 323399) B323399
theorem B960761 : Blo 199806 960761 := bstep (se 2 (by rfl) ⟨360285, by rfl⟩ : syracuseStep 960761 = 720571) B720571
theorem B4401611 : Blo 199806 4401611 := bstep (se 1 (by rfl) ⟨3301208, by rfl⟩ : syracuseStep 4401611 = 6602417) B6602417
theorem B338411 : Blo 199806 338411 := bstep (se 1 (by rfl) ⟨253808, by rfl⟩ : syracuseStep 338411 = 507617) B507617
theorem B305657 : Blo 199806 305657 := bstep (se 2 (by rfl) ⟨114621, by rfl⟩ : syracuseStep 305657 = 229243) B229243
theorem B764903 : Blo 199806 764903 := bstep (se 1 (by rfl) ⟨573677, by rfl⟩ : syracuseStep 764903 = 1147355) B1147355
theorem B6007931 : Blo 199806 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B1518749 : Blo 199806 1518749 := bstep (se 3 (by rfl) ⟨284765, by rfl⟩ : syracuseStep 1518749 = 569531) B569531
theorem B339113 : Blo 199806 339113 := bstep (se 2 (by rfl) ⟨127167, by rfl⟩ : syracuseStep 339113 = 254335) B254335
theorem B1158745 : Blo 199806 1158745 := bstep (se 2 (by rfl) ⟨434529, by rfl⟩ : syracuseStep 1158745 = 869059) B869059
theorem B1027727 : Blo 199806 1027727 := bstep (se 1 (by rfl) ⟨770795, by rfl⟩ : syracuseStep 1027727 = 1541591) B1541591
theorem B1945235 : Blo 199806 1945235 := bstep (se 1 (by rfl) ⟨1458926, by rfl⟩ : syracuseStep 1945235 = 2917853) B2917853
theorem B569065 : Blo 199806 569065 := bstep (se 2 (by rfl) ⟨213399, by rfl⟩ : syracuseStep 569065 = 426799) B426799
theorem B339707 : Blo 199806 339707 := bstep (se 1 (by rfl) ⟨254780, by rfl⟩ : syracuseStep 339707 = 509561) B509561
theorem B4894505 : Blo 199806 4894505 := bstep (se 2 (by rfl) ⟨1835439, by rfl⟩ : syracuseStep 4894505 = 3670879) B3670879
theorem B569213 : Blo 199806 569213 := bstep (se 3 (by rfl) ⟨106727, by rfl⟩ : syracuseStep 569213 = 213455) B213455
theorem B5779421 : Blo 199806 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B241771 : Blo 199806 241771 := bstep (se 1 (by rfl) ⟨181328, by rfl⟩ : syracuseStep 241771 = 362657) B362657
theorem B3420467 : Blo 199806 3420467 := bstep (se 1 (by rfl) ⟨2565350, by rfl⟩ : syracuseStep 3420467 = 5130701) B5130701
theorem B767015 : Blo 199806 767015 := bstep (se 1 (by rfl) ⟨575261, by rfl⟩ : syracuseStep 767015 = 1150523) B1150523
theorem B1553489 : Blo 199806 1553489 := bstep (se 2 (by rfl) ⟨582558, by rfl⟩ : syracuseStep 1553489 = 1165117) B1165117
theorem B1225961 : Blo 199806 1225961 := bstep (se 2 (by rfl) ⟨459735, by rfl⟩ : syracuseStep 1225961 = 919471) B919471
theorem B1095277 : Blo 199806 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B866173 : Blo 199806 866173 := bstep (se 3 (by rfl) ⟨162407, by rfl⟩ : syracuseStep 866173 = 324815) B324815
theorem B1521665 : Blo 199806 1521665 := bstep (se 2 (by rfl) ⟨570624, by rfl⟩ : syracuseStep 1521665 = 1141249) B1141249
theorem B506047 : Blo 199806 506047 := bstep (se 1 (by rfl) ⟨379535, by rfl⟩ : syracuseStep 506047 = 759071) B759071
theorem B571627 : Blo 199806 571627 := bstep (se 1 (by rfl) ⟨428720, by rfl⟩ : syracuseStep 571627 = 857441) B857441
theorem B1095929 : Blo 199806 1095929 := bstep (se 2 (by rfl) ⟨410973, by rfl⟩ : syracuseStep 1095929 = 821947) B821947
theorem B342569 : Blo 199806 342569 := bstep (se 2 (by rfl) ⟨128463, by rfl⟩ : syracuseStep 342569 = 256927) B256927
theorem B867419 : Blo 199806 867419 := bstep (se 1 (by rfl) ⟨650564, by rfl⟩ : syracuseStep 867419 = 1301129) B1301129
theorem B343271 : Blo 199806 343271 := bstep (se 1 (by rfl) ⟨257453, by rfl⟩ : syracuseStep 343271 = 514907) B514907
theorem B769277 : Blo 199806 769277 := bstep (se 3 (by rfl) ⟨144239, by rfl⟩ : syracuseStep 769277 = 288479) B288479
theorem B1228297 : Blo 199806 1228297 := bstep (se 2 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 1228297 = 921223) B921223
theorem B507455 : Blo 199806 507455 := bstep (se 1 (by rfl) ⟨380591, by rfl⟩ : syracuseStep 507455 = 761183) B761183
theorem B3850487 : Blo 199806 3850487 := bstep (se 1 (by rfl) ⟨2887865, by rfl⟩ : syracuseStep 3850487 = 5775731) B5775731
theorem B508153 : Blo 199806 508153 := bstep (se 2 (by rfl) ⟨190557, by rfl⟩ : syracuseStep 508153 = 381115) B381115
theorem B1294825 : Blo 199806 1294825 := bstep (se 2 (by rfl) ⟨485559, by rfl⟩ : syracuseStep 1294825 = 971119) B971119
theorem B6505231 : Blo 199806 6505231 := bstep (se 1 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 6505231 = 9757847) B9757847
theorem B2638615 : Blo 199806 2638615 := bstep (se 1 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 2638615 = 3957923) B3957923
theorem B1295183 : Blo 199806 1295183 := bstep (se 1 (by rfl) ⟨971387, by rfl⟩ : syracuseStep 1295183 = 1942775) B1942775
theorem B869231 : Blo 199806 869231 := bstep (se 1 (by rfl) ⟨651923, by rfl⟩ : syracuseStep 869231 = 1303847) B1303847
theorem B508801 : Blo 199806 508801 := bstep (se 2 (by rfl) ⟨190800, by rfl⟩ : syracuseStep 508801 = 381601) B381601
theorem B213959 : Blo 199806 213959 := bstep (se 1 (by rfl) ⟨160469, by rfl⟩ : syracuseStep 213959 = 320939) B320939
theorem B509611 : Blo 199806 509611 := bstep (se 1 (by rfl) ⟨382208, by rfl⟩ : syracuseStep 509611 = 764417) B764417
theorem B1951775 : Blo 199806 1951775 := bstep (se 1 (by rfl) ⟨1463831, by rfl⟩ : syracuseStep 1951775 = 2927663) B2927663
theorem B510047 : Blo 199806 510047 := bstep (se 1 (by rfl) ⟨382535, by rfl⟩ : syracuseStep 510047 = 765071) B765071
theorem B870547 : Blo 199806 870547 := bstep (se 1 (by rfl) ⟨652910, by rfl⟩ : syracuseStep 870547 = 1305821) B1305821
theorem B1526039 : Blo 199806 1526039 := bstep (se 1 (by rfl) ⟨1144529, by rfl⟩ : syracuseStep 1526039 = 2289059) B2289059
theorem B772679 : Blo 199806 772679 := bstep (se 1 (by rfl) ⟨579509, by rfl⟩ : syracuseStep 772679 = 1159019) B1159019
theorem B1100425 : Blo 199806 1100425 := bstep (se 2 (by rfl) ⟨412659, by rfl⟩ : syracuseStep 1100425 = 825319) B825319
theorem B510745 : Blo 199806 510745 := bstep (se 2 (by rfl) ⟨191529, by rfl⟩ : syracuseStep 510745 = 383059) B383059
theorem B1920323 : Blo 199806 1920323 := bstep (se 1 (by rfl) ⟨1440242, by rfl⟩ : syracuseStep 1920323 = 2880485) B2880485
theorem B675431 : Blo 199806 675431 := bstep (se 1 (by rfl) ⟨506573, by rfl⟩ : syracuseStep 675431 = 1013147) B1013147
theorem B1527497 : Blo 199806 1527497 := bstep (se 2 (by rfl) ⟨572811, by rfl⟩ : syracuseStep 1527497 = 1145623) B1145623
theorem B577631 : Blo 199806 577631 := bstep (se 1 (by rfl) ⟨433223, by rfl⟩ : syracuseStep 577631 = 866447) B866447
theorem B1527983 : Blo 199806 1527983 := bstep (se 1 (by rfl) ⟨1145987, by rfl⟩ : syracuseStep 1527983 = 2291975) B2291975
theorem B545627 : Blo 199806 545627 := bstep (se 1 (by rfl) ⟨409220, by rfl⟩ : syracuseStep 545627 = 818441) B818441
theorem B578459 : Blo 199806 578459 := bstep (se 1 (by rfl) ⟨433844, by rfl⟩ : syracuseStep 578459 = 867689) B867689
theorem B512993 : Blo 199806 512993 := bstep (se 2 (by rfl) ⟨192372, by rfl⟩ : syracuseStep 512993 = 384745) B384745
theorem B381935 : Blo 199806 381935 := bstep (se 1 (by rfl) ⟨286451, by rfl⟩ : syracuseStep 381935 = 572903) B572903
theorem B382619 : Blo 199806 382619 := bstep (se 1 (by rfl) ⟨286964, by rfl⟩ : syracuseStep 382619 = 573929) B573929
theorem B513823 : Blo 199806 513823 := bstep (se 1 (by rfl) ⟨385367, by rfl⟩ : syracuseStep 513823 = 770735) B770735
theorem B1431377 : Blo 199806 1431377 := bstep (se 2 (by rfl) ⟨536766, by rfl⟩ : syracuseStep 1431377 = 1073533) B1073533
theorem B579419 : Blo 199806 579419 := bstep (se 1 (by rfl) ⟨434564, by rfl⟩ : syracuseStep 579419 = 869129) B869129
theorem B481697 : Blo 199806 481697 := bstep (se 2 (by rfl) ⟨180636, by rfl⟩ : syracuseStep 481697 = 361273) B361273
theorem B4413971 : Blo 199806 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B285563 : Blo 199806 285563 := bstep (se 1 (by rfl) ⟨214172, by rfl⟩ : syracuseStep 285563 = 428345) B428345
theorem B449657 : Blo 199806 449657 := bstep (se 2 (by rfl) ⟨168621, by rfl⟩ : syracuseStep 449657 = 337243) B337243
theorem B253135 : Blo 199806 253135 := bstep (se 1 (by rfl) ⟨189851, by rfl⟩ : syracuseStep 253135 = 379703) B379703
theorem B482735 : Blo 199806 482735 := bstep (se 1 (by rfl) ⟨362051, by rfl⟩ : syracuseStep 482735 = 724103) B724103
theorem B2580113 : Blo 199806 2580113 := bstep (se 2 (by rfl) ⟨967542, by rfl⟩ : syracuseStep 2580113 = 1935085) B1935085
theorem B450215 : Blo 199806 450215 := bstep (se 1 (by rfl) ⟨337661, by rfl⟩ : syracuseStep 450215 = 675323) B675323
theorem B450323 : Blo 199806 450323 := bstep (se 1 (by rfl) ⟨337742, by rfl⟩ : syracuseStep 450323 = 675485) B675485
theorem B2318219 : Blo 199806 2318219 := bstep (se 1 (by rfl) ⟨1738664, by rfl⟩ : syracuseStep 2318219 = 3477329) B3477329
theorem B1630135 : Blo 199806 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B450683 : Blo 199806 450683 := bstep (se 1 (by rfl) ⟨338012, by rfl⟩ : syracuseStep 450683 = 676025) B676025
theorem B385231 : Blo 199806 385231 := bstep (se 1 (by rfl) ⟨288923, by rfl⟩ : syracuseStep 385231 = 577847) B577847
theorem B385337 : Blo 199806 385337 := bstep (se 2 (by rfl) ⟨144501, by rfl⟩ : syracuseStep 385337 = 289003) B289003
theorem B450953 : Blo 199806 450953 := bstep (se 2 (by rfl) ⟨169107, by rfl⟩ : syracuseStep 450953 = 338215) B338215
theorem B975311 : Blo 199806 975311 := bstep (se 1 (by rfl) ⟨731483, by rfl⟩ : syracuseStep 975311 = 1462967) B1462967
theorem B680615 : Blo 199806 680615 := bstep (se 1 (by rfl) ⟨510461, by rfl⟩ : syracuseStep 680615 = 1020923) B1020923
theorem B2188043 : Blo 199806 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B385823 : Blo 199806 385823 := bstep (se 1 (by rfl) ⟨289367, by rfl⟩ : syracuseStep 385823 = 578735) B578735
theorem B5170067 : Blo 199806 5170067 := bstep (se 1 (by rfl) ⟨3877550, by rfl⟩ : syracuseStep 5170067 = 7755101) B7755101
theorem B779165 : Blo 199806 779165 := bstep (se 3 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 779165 = 292187) B292187
theorem B680939 : Blo 199806 680939 := bstep (se 1 (by rfl) ⟨510704, by rfl⟩ : syracuseStep 680939 = 1021409) B1021409
theorem B3892313 : Blo 199806 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B452087 : Blo 199806 452087 := bstep (se 1 (by rfl) ⟨339065, by rfl⟩ : syracuseStep 452087 = 678131) B678131
theorem B452123 : Blo 199806 452123 := bstep (se 1 (by rfl) ⟨339092, by rfl⟩ : syracuseStep 452123 = 678185) B678185
theorem B550471 : Blo 199806 550471 := bstep (se 1 (by rfl) ⟨412853, by rfl⟩ : syracuseStep 550471 = 825707) B825707
theorem B682127 : Blo 199806 682127 := bstep (se 1 (by rfl) ⟨511595, by rfl⟩ : syracuseStep 682127 = 1023191) B1023191
theorem B453113 : Blo 199806 453113 := bstep (se 2 (by rfl) ⟨169917, by rfl⟩ : syracuseStep 453113 = 339835) B339835
theorem B453167 : Blo 199806 453167 := bstep (se 1 (by rfl) ⟨339875, by rfl⟩ : syracuseStep 453167 = 679751) B679751
theorem B453203 : Blo 199806 453203 := bstep (se 1 (by rfl) ⟨339902, by rfl⟩ : syracuseStep 453203 = 679805) B679805
theorem B453383 : Blo 199806 453383 := bstep (se 1 (by rfl) ⟨340037, by rfl⟩ : syracuseStep 453383 = 680075) B680075
theorem B453599 : Blo 199806 453599 := bstep (se 1 (by rfl) ⟨340199, by rfl⟩ : syracuseStep 453599 = 680399) B680399
theorem B453815 : Blo 199806 453815 := bstep (se 1 (by rfl) ⟨340361, by rfl⟩ : syracuseStep 453815 = 680723) B680723
theorem B3009869 : Blo 199806 3009869 := bstep (se 3 (by rfl) ⟨564350, by rfl⟩ : syracuseStep 3009869 = 1128701) B1128701
theorem B15756743 : Blo 199806 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B519635 : Blo 199806 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B454391 : Blo 199806 454391 := bstep (se 1 (by rfl) ⟨340793, by rfl⟩ : syracuseStep 454391 = 681587) B681587
theorem B454463 : Blo 199806 454463 := bstep (se 1 (by rfl) ⟨340847, by rfl⟩ : syracuseStep 454463 = 681695) B681695
theorem B454571 : Blo 199806 454571 := bstep (se 1 (by rfl) ⟨340928, by rfl⟩ : syracuseStep 454571 = 681857) B681857
theorem B454931 : Blo 199806 454931 := bstep (se 1 (by rfl) ⟨341198, by rfl⟩ : syracuseStep 454931 = 682397) B682397
theorem B323995 : Blo 199806 323995 := bstep (se 1 (by rfl) ⟨242996, by rfl⟩ : syracuseStep 323995 = 485993) B485993
theorem B455111 : Blo 199806 455111 := bstep (se 1 (by rfl) ⟨341333, by rfl⟩ : syracuseStep 455111 = 682667) B682667
theorem B1012175 : Blo 199806 1012175 := bstep (se 1 (by rfl) ⟨759131, by rfl⟩ : syracuseStep 1012175 = 1518263) B1518263
theorem B684719 : Blo 199806 684719 := bstep (se 1 (by rfl) ⟨513539, by rfl⟩ : syracuseStep 684719 = 1027079) B1027079
theorem B455471 : Blo 199806 455471 := bstep (se 1 (by rfl) ⟨341603, by rfl⟩ : syracuseStep 455471 = 683207) B683207
theorem B226111 : Blo 199806 226111 := bstep (se 1 (by rfl) ⟨169583, by rfl⟩ : syracuseStep 226111 = 339167) B339167
theorem B455561 : Blo 199806 455561 := bstep (se 2 (by rfl) ⟨170835, by rfl⟩ : syracuseStep 455561 = 341671) B341671
theorem B1242049 : Blo 199806 1242049 := bstep (se 2 (by rfl) ⟨465768, by rfl⟩ : syracuseStep 1242049 = 931537) B931537
theorem B226399 : Blo 199806 226399 := bstep (se 1 (by rfl) ⟨169799, by rfl⟩ : syracuseStep 226399 = 339599) B339599
theorem B456335 : Blo 199806 456335 := bstep (se 1 (by rfl) ⟨342251, by rfl⟩ : syracuseStep 456335 = 684503) B684503
theorem B456425 : Blo 199806 456425 := bstep (se 2 (by rfl) ⟨171159, by rfl⟩ : syracuseStep 456425 = 342319) B342319
theorem B686291 : Blo 199806 686291 := bstep (se 1 (by rfl) ⟨514718, by rfl⟩ : syracuseStep 686291 = 1029437) B1029437
theorem B456935 : Blo 199806 456935 := bstep (se 1 (by rfl) ⟨342701, by rfl⟩ : syracuseStep 456935 = 685403) B685403
theorem B457307 : Blo 199806 457307 := bstep (se 1 (by rfl) ⟨342980, by rfl⟩ : syracuseStep 457307 = 685961) B685961
theorem B1145441 : Blo 199806 1145441 := bstep (se 2 (by rfl) ⟨429540, by rfl⟩ : syracuseStep 1145441 = 859081) B859081
theorem B457451 : Blo 199806 457451 := bstep (se 1 (by rfl) ⟨343088, by rfl⟩ : syracuseStep 457451 = 686177) B686177
theorem B228559 : Blo 199806 228559 := bstep (se 1 (by rfl) ⟨171419, by rfl⟩ : syracuseStep 228559 = 342839) B342839
theorem B5143823 : Blo 199806 5143823 := bstep (se 1 (by rfl) ⟨3857867, by rfl⟩ : syracuseStep 5143823 = 7715735) B7715735
theorem B458063 : Blo 199806 458063 := bstep (se 1 (by rfl) ⟨343547, by rfl⟩ : syracuseStep 458063 = 687095) B687095
theorem B458153 : Blo 199806 458153 := bstep (se 2 (by rfl) ⟨171807, by rfl⟩ : syracuseStep 458153 = 343615) B343615
theorem B687635 : Blo 199806 687635 := bstep (se 1 (by rfl) ⟨515726, by rfl⟩ : syracuseStep 687635 = 1031453) B1031453
theorem B458351 : Blo 199806 458351 := bstep (se 1 (by rfl) ⟨343763, by rfl⟩ : syracuseStep 458351 = 687527) B687527
theorem B2883833 : Blo 199806 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B1442897 : Blo 199806 1442897 := bstep (se 2 (by rfl) ⟨541086, by rfl⟩ : syracuseStep 1442897 = 1082173) B1082173
theorem B1017359 : Blo 199806 1017359 := bstep (se 1 (by rfl) ⟨763019, by rfl⟩ : syracuseStep 1017359 = 1526039) B1526039
theorem B1083557 : Blo 199806 1083557 := bstep (se 4 (by rfl) ⟨101583, by rfl⟩ : syracuseStep 1083557 = 203167) B203167
theorem B1280215 : Blo 199806 1280215 := bstep (se 1 (by rfl) ⟨960161, by rfl⟩ : syracuseStep 1280215 = 1920323) B1920323
theorem B1542557 : Blo 199806 1542557 := bstep (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) B578459
theorem B1018331 : Blo 199806 1018331 := bstep (se 1 (by rfl) ⟨763748, by rfl⟩ : syracuseStep 1018331 = 1527497) B1527497
theorem B1018493 : Blo 199806 1018493 := bstep (se 3 (by rfl) ⟨190967, by rfl⟩ : syracuseStep 1018493 = 381935) B381935
theorem B1018655 : Blo 199806 1018655 := bstep (se 1 (by rfl) ⟨763991, by rfl⟩ : syracuseStep 1018655 = 1527983) B1527983
theorem B199911 : Blo 199806 199911 := bstep (se 1 (by rfl) ⟨149933, by rfl⟩ : syracuseStep 199911 = 299867) B299867
theorem B200219 : Blo 199806 200219 := bstep (se 1 (by rfl) ⟨150164, by rfl⟩ : syracuseStep 200219 = 300329) B300329
theorem B200351 : Blo 199806 200351 := bstep (se 1 (by rfl) ⟨150263, by rfl⟩ : syracuseStep 200351 = 300527) B300527
theorem B2101115 : Blo 199806 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B954251 : Blo 199806 954251 := bstep (se 1 (by rfl) ⟨715688, by rfl⟩ : syracuseStep 954251 = 1431377) B1431377
theorem B200615 : Blo 199806 200615 := bstep (se 1 (by rfl) ⟨150461, by rfl⟩ : syracuseStep 200615 = 300923) B300923
theorem B200639 : Blo 199806 200639 := bstep (se 1 (by rfl) ⟨150479, by rfl⟩ : syracuseStep 200639 = 300959) B300959
theorem B200795 : Blo 199806 200795 := bstep (se 1 (by rfl) ⟨150596, by rfl⟩ : syracuseStep 200795 = 301193) B301193
theorem B200895 : Blo 199806 200895 := bstep (se 1 (by rfl) ⟨150671, by rfl⟩ : syracuseStep 200895 = 301343) B301343
theorem B1970693 : Blo 199806 1970693 := bstep (se 4 (by rfl) ⟨184752, by rfl⟩ : syracuseStep 1970693 = 369505) B369505
theorem B201263 : Blo 199806 201263 := bstep (se 1 (by rfl) ⟨150947, by rfl⟩ : syracuseStep 201263 = 301895) B301895
theorem B299771 : Blo 199806 299771 := bstep (se 1 (by rfl) ⟨224828, by rfl⟩ : syracuseStep 299771 = 449657) B449657
theorem B1544993 : Blo 199806 1544993 := bstep (se 2 (by rfl) ⟨579372, by rfl⟩ : syracuseStep 1544993 = 1158745) B1158745
theorem B758753 : Blo 199806 758753 := bstep (se 2 (by rfl) ⟨284532, by rfl⟩ : syracuseStep 758753 = 569065) B569065
theorem B2233327 : Blo 199806 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B300143 : Blo 199806 300143 := bstep (se 1 (by rfl) ⟨225107, by rfl⟩ : syracuseStep 300143 = 450215) B450215
theorem B201839 : Blo 199806 201839 := bstep (se 1 (by rfl) ⟨151379, by rfl⟩ : syracuseStep 201839 = 302759) B302759
theorem B300215 : Blo 199806 300215 := bstep (se 1 (by rfl) ⟨225161, by rfl⟩ : syracuseStep 300215 = 450323) B450323
theorem B201919 : Blo 199806 201919 := bstep (se 1 (by rfl) ⟨151439, by rfl⟩ : syracuseStep 201919 = 302879) B302879
theorem B1545479 : Blo 199806 1545479 := bstep (se 1 (by rfl) ⟨1159109, by rfl⟩ : syracuseStep 1545479 = 2318219) B2318219
theorem B300455 : Blo 199806 300455 := bstep (se 1 (by rfl) ⟨225341, by rfl⟩ : syracuseStep 300455 = 450683) B450683
theorem B1840583 : Blo 199806 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B202207 : Blo 199806 202207 := bstep (se 1 (by rfl) ⟨151655, by rfl⟩ : syracuseStep 202207 = 303311) B303311
theorem B202239 : Blo 199806 202239 := bstep (se 1 (by rfl) ⟨151679, by rfl⟩ : syracuseStep 202239 = 303359) B303359
theorem B300635 : Blo 199806 300635 := bstep (se 1 (by rfl) ⟨225476, by rfl⟩ : syracuseStep 300635 = 450953) B450953
theorem B431993 : Blo 199806 431993 := bstep (se 2 (by rfl) ⟨161997, by rfl⟩ : syracuseStep 431993 = 323995) B323995
theorem B3446711 : Blo 199806 3446711 := bstep (se 1 (by rfl) ⟨2585033, by rfl⟩ : syracuseStep 3446711 = 5170067) B5170067
theorem B1218493 : Blo 199806 1218493 := bstep (se 3 (by rfl) ⟨228467, by rfl⟩ : syracuseStep 1218493 = 456935) B456935
theorem B202783 : Blo 199806 202783 := bstep (se 1 (by rfl) ⟨152087, by rfl⟩ : syracuseStep 202783 = 304175) B304175
theorem B2594875 : Blo 199806 2594875 := bstep (se 1 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 2594875 = 3892313) B3892313
theorem B202863 : Blo 199806 202863 := bstep (se 1 (by rfl) ⟨152147, by rfl⟩ : syracuseStep 202863 = 304295) B304295
theorem B301391 : Blo 199806 301391 := bstep (se 1 (by rfl) ⟨226043, by rfl⟩ : syracuseStep 301391 = 452087) B452087
theorem B301415 : Blo 199806 301415 := bstep (se 1 (by rfl) ⟨226061, by rfl⟩ : syracuseStep 301415 = 452123) B452123
theorem B203111 : Blo 199806 203111 := bstep (se 1 (by rfl) ⟨152333, by rfl⟩ : syracuseStep 203111 = 304667) B304667
theorem B301481 : Blo 199806 301481 := bstep (se 2 (by rfl) ⟨113055, by rfl⟩ : syracuseStep 301481 = 226111) B226111
theorem B203367 : Blo 199806 203367 := bstep (se 1 (by rfl) ⟨152525, by rfl⟩ : syracuseStep 203367 = 305051) B305051
theorem B203391 : Blo 199806 203391 := bstep (se 1 (by rfl) ⟨152543, by rfl⟩ : syracuseStep 203391 = 305087) B305087
theorem B203515 : Blo 199806 203515 := bstep (se 1 (by rfl) ⟨152636, by rfl⟩ : syracuseStep 203515 = 305273) B305273
theorem B301865 : Blo 199806 301865 := bstep (se 2 (by rfl) ⟨113199, by rfl⟩ : syracuseStep 301865 = 226399) B226399
theorem B302075 : Blo 199806 302075 := bstep (se 1 (by rfl) ⟨226556, by rfl⟩ : syracuseStep 302075 = 453113) B453113
theorem B203771 : Blo 199806 203771 := bstep (se 1 (by rfl) ⟨152828, by rfl⟩ : syracuseStep 203771 = 305657) B305657
theorem B302111 : Blo 199806 302111 := bstep (se 1 (by rfl) ⟨226583, by rfl⟩ : syracuseStep 302111 = 453167) B453167
theorem B302135 : Blo 199806 302135 := bstep (se 1 (by rfl) ⟨226601, by rfl⟩ : syracuseStep 302135 = 453203) B453203
theorem B302255 : Blo 199806 302255 := bstep (se 1 (by rfl) ⟨226691, by rfl⟩ : syracuseStep 302255 = 453383) B453383
theorem B302399 : Blo 199806 302399 := bstep (se 1 (by rfl) ⟨226799, by rfl⟩ : syracuseStep 302399 = 453599) B453599
theorem B4005287 : Blo 199806 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B302543 : Blo 199806 302543 := bstep (se 1 (by rfl) ⟨226907, by rfl⟩ : syracuseStep 302543 = 453815) B453815
theorem B2006579 : Blo 199806 2006579 := bstep (se 1 (by rfl) ⟨1504934, by rfl⟩ : syracuseStep 2006579 = 3009869) B3009869
theorem B761501 : Blo 199806 761501 := bstep (se 3 (by rfl) ⟨142781, by rfl⟩ : syracuseStep 761501 = 285563) B285563
theorem B302927 : Blo 199806 302927 := bstep (se 1 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 302927 = 454391) B454391
theorem B1154897 : Blo 199806 1154897 := bstep (se 2 (by rfl) ⟨433086, by rfl⟩ : syracuseStep 1154897 = 866173) B866173
theorem B302975 : Blo 199806 302975 := bstep (se 1 (by rfl) ⟨227231, by rfl⟩ : syracuseStep 302975 = 454463) B454463
theorem B303047 : Blo 199806 303047 := bstep (se 1 (by rfl) ⟨227285, by rfl⟩ : syracuseStep 303047 = 454571) B454571
theorem B303287 : Blo 199806 303287 := bstep (se 1 (by rfl) ⟨227465, by rfl⟩ : syracuseStep 303287 = 454931) B454931
theorem B303407 : Blo 199806 303407 := bstep (se 1 (by rfl) ⟨227555, by rfl⟩ : syracuseStep 303407 = 455111) B455111
theorem B762169 : Blo 199806 762169 := bstep (se 2 (by rfl) ⟨285813, by rfl⟩ : syracuseStep 762169 = 571627) B571627
theorem B303647 : Blo 199806 303647 := bstep (se 1 (by rfl) ⟨227735, by rfl⟩ : syracuseStep 303647 = 455471) B455471
theorem B303707 : Blo 199806 303707 := bstep (se 1 (by rfl) ⟨227780, by rfl⟩ : syracuseStep 303707 = 455561) B455561
theorem B304223 : Blo 199806 304223 := bstep (se 1 (by rfl) ⟨228167, by rfl⟩ : syracuseStep 304223 = 456335) B456335
theorem B304283 : Blo 199806 304283 := bstep (se 1 (by rfl) ⟨228212, by rfl⟩ : syracuseStep 304283 = 456425) B456425
theorem B730619 : Blo 199806 730619 := bstep (se 1 (by rfl) ⟨547964, by rfl⟩ : syracuseStep 730619 = 1095929) B1095929
theorem B337513 : Blo 199806 337513 := bstep (se 2 (by rfl) ⟨126567, by rfl⟩ : syracuseStep 337513 = 253135) B253135
theorem B304745 : Blo 199806 304745 := bstep (se 2 (by rfl) ⟨114279, by rfl⟩ : syracuseStep 304745 = 228559) B228559
theorem B304871 : Blo 199806 304871 := bstep (se 1 (by rfl) ⟨228653, by rfl⟩ : syracuseStep 304871 = 457307) B457307
theorem B763627 : Blo 199806 763627 := bstep (se 1 (by rfl) ⟨572720, by rfl⟩ : syracuseStep 763627 = 1145441) B1145441
theorem B304967 : Blo 199806 304967 := bstep (se 1 (by rfl) ⟨228725, by rfl⟩ : syracuseStep 304967 = 457451) B457451
theorem B305375 : Blo 199806 305375 := bstep (se 1 (by rfl) ⟨229031, by rfl⟩ : syracuseStep 305375 = 458063) B458063
theorem B305435 : Blo 199806 305435 := bstep (se 1 (by rfl) ⟨229076, by rfl⟩ : syracuseStep 305435 = 458153) B458153
theorem B338303 : Blo 199806 338303 := bstep (se 1 (by rfl) ⟨253727, by rfl⟩ : syracuseStep 338303 = 507455) B507455
theorem B305567 : Blo 199806 305567 := bstep (se 1 (by rfl) ⟨229175, by rfl⟩ : syracuseStep 305567 = 458351) B458351
theorem B2173513 : Blo 199806 2173513 := bstep (se 2 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 2173513 = 1630135) B1630135
theorem B2566991 : Blo 199806 2566991 := bstep (se 1 (by rfl) ⟨1925243, by rfl⟩ : syracuseStep 2566991 = 3850487) B3850487
theorem B863455 : Blo 199806 863455 := bstep (se 1 (by rfl) ⟨647591, by rfl⟩ : syracuseStep 863455 = 1295183) B1295183
theorem B4566365 : Blo 199806 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B1027565 : Blo 199806 1027565 := bstep (se 3 (by rfl) ⟨192668, by rfl⟩ : syracuseStep 1027565 = 385337) B385337
theorem B962239 : Blo 199806 962239 := bstep (se 1 (by rfl) ⟨721679, by rfl⟩ : syracuseStep 962239 = 1443359) B1443359
theorem B3518153 : Blo 199806 3518153 := bstep (se 2 (by rfl) ⟨1319307, by rfl⟩ : syracuseStep 3518153 = 2638615) B2638615
theorem B340031 : Blo 199806 340031 := bstep (se 1 (by rfl) ⟨255023, by rfl⟩ : syracuseStep 340031 = 510047) B510047
theorem B1093895 : Blo 199806 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B766543 : Blo 199806 766543 := bstep (se 1 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 766543 = 1149815) B1149815
theorem B1028861 : Blo 199806 1028861 := bstep (se 3 (by rfl) ⟨192911, by rfl⟩ : syracuseStep 1028861 = 385823) B385823
theorem B733961 : Blo 199806 733961 := bstep (se 2 (by rfl) ⟨275235, by rfl⟩ : syracuseStep 733961 = 550471) B550471
theorem B570169 : Blo 199806 570169 := bstep (se 2 (by rfl) ⟨213813, by rfl⟩ : syracuseStep 570169 = 427627) B427627
theorem B1455005 : Blo 199806 1455005 := bstep (se 3 (by rfl) ⟨272813, by rfl⟩ : syracuseStep 1455005 = 545627) B545627
theorem B1029023 : Blo 199806 1029023 := bstep (se 1 (by rfl) ⟨771767, by rfl⟩ : syracuseStep 1029023 = 1543535) B1543535
theorem B570557 : Blo 199806 570557 := bstep (se 3 (by rfl) ⟨106979, by rfl⟩ : syracuseStep 570557 = 213959) B213959
theorem B1160477 : Blo 199806 1160477 := bstep (se 3 (by rfl) ⟨217589, by rfl⟩ : syracuseStep 1160477 = 435179) B435179
theorem B308521 : Blo 199806 308521 := bstep (se 2 (by rfl) ⟨115695, by rfl⟩ : syracuseStep 308521 = 231391) B231391
theorem B308711 : Blo 199806 308711 := bstep (se 1 (by rfl) ⟨231533, by rfl⟩ : syracuseStep 308711 = 463067) B463067
theorem B1160729 : Blo 199806 1160729 := bstep (se 2 (by rfl) ⟨435273, by rfl⟩ : syracuseStep 1160729 = 870547) B870547
theorem B1095407 : Blo 199806 1095407 := bstep (se 1 (by rfl) ⟨821555, by rfl⟩ : syracuseStep 1095407 = 1643111) B1643111
theorem B341995 : Blo 199806 341995 := bstep (se 1 (by rfl) ⟨256496, by rfl⟩ : syracuseStep 341995 = 512993) B512993
theorem B964817 : Blo 199806 964817 := bstep (se 2 (by rfl) ⟨361806, by rfl⟩ : syracuseStep 964817 = 723613) B723613
theorem B506159 : Blo 199806 506159 := bstep (se 1 (by rfl) ⟨379619, by rfl⟩ : syracuseStep 506159 = 759239) B759239
theorem B571855 : Blo 199806 571855 := bstep (se 1 (by rfl) ⟨428891, by rfl⟩ : syracuseStep 571855 = 857783) B857783
theorem B1720075 : Blo 199806 1720075 := bstep (se 1 (by rfl) ⟨1290056, by rfl⟩ : syracuseStep 1720075 = 2580113) B2580113
theorem B573655 : Blo 199806 573655 := bstep (se 1 (by rfl) ⟨430241, by rfl⟩ : syracuseStep 573655 = 860483) B860483
theorem B1458695 : Blo 199806 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B1656065 : Blo 199806 1656065 := bstep (se 2 (by rfl) ⟨621024, by rfl⟩ : syracuseStep 1656065 = 1242049) B1242049
theorem B509287 : Blo 199806 509287 := bstep (se 1 (by rfl) ⟨381965, by rfl⟩ : syracuseStep 509287 = 763931) B763931
theorem B574931 : Blo 199806 574931 := bstep (se 1 (by rfl) ⟨431198, by rfl⟩ : syracuseStep 574931 = 862397) B862397
theorem B640507 : Blo 199806 640507 := bstep (se 1 (by rfl) ⟨480380, by rfl⟩ : syracuseStep 640507 = 960761) B960761
theorem B2934407 : Blo 199806 2934407 := bstep (se 1 (by rfl) ⟨2200805, by rfl⟩ : syracuseStep 2934407 = 4401611) B4401611
theorem B509935 : Blo 199806 509935 := bstep (se 1 (by rfl) ⟨382451, by rfl⟩ : syracuseStep 509935 = 764903) B764903
theorem B1099777 : Blo 199806 1099777 := bstep (se 2 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 1099777 = 824833) B824833
theorem B1460369 : Blo 199806 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B10504495 : Blo 199806 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B346423 : Blo 199806 346423 := bstep (se 1 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 346423 = 519635) B519635
theorem B1296823 : Blo 199806 1296823 := bstep (se 1 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 1296823 = 1945235) B1945235
theorem B3263003 : Blo 199806 3263003 := bstep (se 1 (by rfl) ⟨2447252, by rfl⟩ : syracuseStep 3263003 = 4894505) B4894505
theorem B379475 : Blo 199806 379475 := bstep (se 1 (by rfl) ⟨284606, by rfl⟩ : syracuseStep 379475 = 569213) B569213
theorem B3852947 : Blo 199806 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B2280311 : Blo 199806 2280311 := bstep (se 1 (by rfl) ⟨1710233, by rfl⟩ : syracuseStep 2280311 = 3420467) B3420467
theorem B674729 : Blo 199806 674729 := bstep (se 2 (by rfl) ⟨253023, by rfl⟩ : syracuseStep 674729 = 506047) B506047
theorem B674783 : Blo 199806 674783 := bstep (se 1 (by rfl) ⟨506087, by rfl⟩ : syracuseStep 674783 = 1012175) B1012175
theorem B511343 : Blo 199806 511343 := bstep (se 1 (by rfl) ⟨383507, by rfl⟩ : syracuseStep 511343 = 767015) B767015
theorem B1035659 : Blo 199806 1035659 := bstep (se 1 (by rfl) ⟨776744, by rfl⟩ : syracuseStep 1035659 = 1553489) B1553489
theorem B578279 : Blo 199806 578279 := bstep (se 1 (by rfl) ⟨433709, by rfl⟩ : syracuseStep 578279 = 867419) B867419
theorem B512851 : Blo 199806 512851 := bstep (se 1 (by rfl) ⟨384638, by rfl⟩ : syracuseStep 512851 = 769277) B769277
theorem B3429215 : Blo 199806 3429215 := bstep (se 1 (by rfl) ⟨2571911, by rfl⟩ : syracuseStep 3429215 = 5143823) B5143823
theorem B513641 : Blo 199806 513641 := bstep (se 2 (by rfl) ⟨192615, by rfl⟩ : syracuseStep 513641 = 385231) B385231
theorem B677537 : Blo 199806 677537 := bstep (se 2 (by rfl) ⟨254076, by rfl⟩ : syracuseStep 677537 = 508153) B508153
theorem B579487 : Blo 199806 579487 := bstep (se 1 (by rfl) ⟨434615, by rfl⟩ : syracuseStep 579487 = 869231) B869231
theorem B1726433 : Blo 199806 1726433 := bstep (se 2 (by rfl) ⟨647412, by rfl⟩ : syracuseStep 1726433 = 1294825) B1294825
theorem B284743 : Blo 199806 284743 := bstep (se 1 (by rfl) ⟨213557, by rfl⟩ : syracuseStep 284743 = 427115) B427115
theorem B8673641 : Blo 199806 8673641 := bstep (se 2 (by rfl) ⟨3252615, by rfl⟩ : syracuseStep 8673641 = 6505231) B6505231
theorem B678401 : Blo 199806 678401 := bstep (se 2 (by rfl) ⟨254400, by rfl⟩ : syracuseStep 678401 = 508801) B508801
theorem B1301183 : Blo 199806 1301183 := bstep (se 1 (by rfl) ⟨975887, by rfl⟩ : syracuseStep 1301183 = 1951775) B1951775
theorem B1628905 : Blo 199806 1628905 := bstep (se 2 (by rfl) ⟨610839, by rfl⟩ : syracuseStep 1628905 = 1221679) B1221679
theorem B940787 : Blo 199806 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B515119 : Blo 199806 515119 := bstep (se 1 (by rfl) ⟨386339, by rfl⟩ : syracuseStep 515119 = 772679) B772679
theorem B613759 : Blo 199806 613759 := bstep (se 1 (by rfl) ⟨460319, by rfl⟩ : syracuseStep 613759 = 920639) B920639
theorem B679481 : Blo 199806 679481 := bstep (se 2 (by rfl) ⟨254805, by rfl⟩ : syracuseStep 679481 = 509611) B509611
theorem B679643 : Blo 199806 679643 := bstep (se 1 (by rfl) ⟨509732, by rfl⟩ : syracuseStep 679643 = 1019465) B1019465
theorem B450287 : Blo 199806 450287 := bstep (se 1 (by rfl) ⟨337715, by rfl⟩ : syracuseStep 450287 = 675431) B675431
theorem B614441 : Blo 199806 614441 := bstep (se 2 (by rfl) ⟨230415, by rfl⟩ : syracuseStep 614441 = 460831) B460831
theorem B385087 : Blo 199806 385087 := bstep (se 1 (by rfl) ⟨288815, by rfl⟩ : syracuseStep 385087 = 577631) B577631
theorem B1467233 : Blo 199806 1467233 := bstep (se 2 (by rfl) ⟨550212, by rfl⟩ : syracuseStep 1467233 = 1100425) B1100425
theorem B680993 : Blo 199806 680993 := bstep (se 2 (by rfl) ⟨255372, by rfl⟩ : syracuseStep 680993 = 510745) B510745
theorem B255079 : Blo 199806 255079 := bstep (se 1 (by rfl) ⟨191309, by rfl⟩ : syracuseStep 255079 = 382619) B382619
theorem B386279 : Blo 199806 386279 := bstep (se 1 (by rfl) ⟨289709, by rfl⟩ : syracuseStep 386279 = 579419) B579419
theorem B321131 : Blo 199806 321131 := bstep (se 1 (by rfl) ⟨240848, by rfl⟩ : syracuseStep 321131 = 481697) B481697
theorem B2942647 : Blo 199806 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B288679 : Blo 199806 288679 := bstep (se 1 (by rfl) ⟨216509, by rfl⟩ : syracuseStep 288679 = 433019) B433019
theorem B321823 : Blo 199806 321823 := bstep (se 1 (by rfl) ⟨241367, by rfl⟩ : syracuseStep 321823 = 482735) B482735
theorem B322361 : Blo 199806 322361 := bstep (se 2 (by rfl) ⟨120885, by rfl⟩ : syracuseStep 322361 = 241771) B241771
theorem B650207 : Blo 199806 650207 := bstep (se 1 (by rfl) ⟨487655, by rfl⟩ : syracuseStep 650207 = 975311) B975311
theorem B453743 : Blo 199806 453743 := bstep (se 1 (by rfl) ⟨340307, by rfl⟩ : syracuseStep 453743 = 680615) B680615
theorem B1830109 : Blo 199806 1830109 := bstep (se 3 (by rfl) ⟨343145, by rfl⟩ : syracuseStep 1830109 = 686291) B686291
theorem B519443 : Blo 199806 519443 := bstep (se 1 (by rfl) ⟨389582, by rfl⟩ : syracuseStep 519443 = 779165) B779165
theorem B453959 : Blo 199806 453959 := bstep (se 1 (by rfl) ⟨340469, by rfl⟩ : syracuseStep 453959 = 680939) B680939
theorem B618455 : Blo 199806 618455 := bstep (se 1 (by rfl) ⟨463841, by rfl⟩ : syracuseStep 618455 = 927683) B927683
theorem B1011689 : Blo 199806 1011689 := bstep (se 2 (by rfl) ⟨379383, by rfl⟩ : syracuseStep 1011689 = 758767) B758767
theorem B684071 : Blo 199806 684071 := bstep (se 1 (by rfl) ⟨513053, by rfl⟩ : syracuseStep 684071 = 1026107) B1026107
theorem B454751 : Blo 199806 454751 := bstep (se 1 (by rfl) ⟨341063, by rfl⟩ : syracuseStep 454751 = 682127) B682127
theorem B225607 : Blo 199806 225607 := bstep (se 1 (by rfl) ⟨169205, by rfl⟩ : syracuseStep 225607 = 338411) B338411
theorem B1012499 : Blo 199806 1012499 := bstep (se 1 (by rfl) ⟨759374, by rfl⟩ : syracuseStep 1012499 = 1518749) B1518749
theorem B226075 : Blo 199806 226075 := bstep (se 1 (by rfl) ⟨169556, by rfl⟩ : syracuseStep 226075 = 339113) B339113
theorem B685097 : Blo 199806 685097 := bstep (se 2 (by rfl) ⟨256911, by rfl⟩ : syracuseStep 685097 = 513823) B513823
theorem B685151 : Blo 199806 685151 := bstep (se 1 (by rfl) ⟨513863, by rfl⟩ : syracuseStep 685151 = 1027727) B1027727
theorem B226471 : Blo 199806 226471 := bstep (se 1 (by rfl) ⟨169853, by rfl⟩ : syracuseStep 226471 = 339707) B339707
theorem B456479 : Blo 199806 456479 := bstep (se 1 (by rfl) ⟨342359, by rfl⟩ : syracuseStep 456479 = 684719) B684719
theorem B817307 : Blo 199806 817307 := bstep (se 1 (by rfl) ⟨612980, by rfl⟩ : syracuseStep 817307 = 1225961) B1225961
theorem B1014443 : Blo 199806 1014443 := bstep (se 1 (by rfl) ⟨760832, by rfl⟩ : syracuseStep 1014443 = 1521665) B1521665
theorem B228379 : Blo 199806 228379 := bstep (se 1 (by rfl) ⟨171284, by rfl⟩ : syracuseStep 228379 = 342569) B342569
theorem B1637729 : Blo 199806 1637729 := bstep (se 2 (by rfl) ⟨614148, by rfl⟩ : syracuseStep 1637729 = 1228297) B1228297
theorem B228847 : Blo 199806 228847 := bstep (se 1 (by rfl) ⟨171635, by rfl⟩ : syracuseStep 228847 = 343271) B343271
theorem B458423 : Blo 199806 458423 := bstep (se 1 (by rfl) ⟨343817, by rfl⟩ : syracuseStep 458423 = 687635) B687635
theorem B1016225 : Blo 199806 1016225 := bstep (se 2 (by rfl) ⟨381084, by rfl⟩ : syracuseStep 1016225 = 762169) B762169
theorem B722371 : Blo 199806 722371 := bstep (se 1 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 722371 = 1083557) B1083557
theorem B1542077 : Blo 199806 1542077 := bstep (se 3 (by rfl) ⟨289139, by rfl⟩ : syracuseStep 1542077 = 578279) B578279
theorem B854009 : Blo 199806 854009 := bstep (se 2 (by rfl) ⟨320253, by rfl⟩ : syracuseStep 854009 = 640507) B640507
theorem B690439 : Blo 199806 690439 := bstep (se 1 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 690439 = 1035659) B1035659
theorem B1018169 : Blo 199806 1018169 := bstep (se 2 (by rfl) ⟨381813, by rfl⟩ : syracuseStep 1018169 = 763627) B763627
theorem B1706953 : Blo 199806 1706953 := bstep (se 2 (by rfl) ⟨640107, by rfl⟩ : syracuseStep 1706953 = 1280215) B1280215
theorem B1313795 : Blo 199806 1313795 := bstep (se 1 (by rfl) ⟨985346, by rfl⟩ : syracuseStep 1313795 = 1970693) B1970693
theorem B429097 : Blo 199806 429097 := bstep (se 2 (by rfl) ⟨160911, by rfl⟩ : syracuseStep 429097 = 321823) B321823
theorem B461897 : Blo 199806 461897 := bstep (se 2 (by rfl) ⟨173211, by rfl⟩ : syracuseStep 461897 = 346423) B346423
theorem B199847 : Blo 199806 199847 := bstep (se 1 (by rfl) ⟨149885, by rfl⟩ : syracuseStep 199847 = 299771) B299771
theorem B200095 : Blo 199806 200095 := bstep (se 1 (by rfl) ⟨150071, by rfl⟩ : syracuseStep 200095 = 300143) B300143
theorem B200143 : Blo 199806 200143 := bstep (se 1 (by rfl) ⟨150107, by rfl⟩ : syracuseStep 200143 = 300215) B300215
theorem B200303 : Blo 199806 200303 := bstep (se 1 (by rfl) ⟨150227, by rfl⟩ : syracuseStep 200303 = 300455) B300455
theorem B200423 : Blo 199806 200423 := bstep (se 1 (by rfl) ⟨150317, by rfl⟩ : syracuseStep 200423 = 300635) B300635
theorem B823229 : Blo 199806 823229 := bstep (se 3 (by rfl) ⟨154355, by rfl⟩ : syracuseStep 823229 = 308711) B308711
theorem B2297807 : Blo 199806 2297807 := bstep (se 1 (by rfl) ⟨1723355, by rfl⟩ : syracuseStep 2297807 = 3446711) B3446711
theorem B1150955 : Blo 199806 1150955 := bstep (se 1 (by rfl) ⟨863216, by rfl⟩ : syracuseStep 1150955 = 1726433) B1726433
theorem B200927 : Blo 199806 200927 := bstep (se 1 (by rfl) ⟨150695, by rfl⟩ : syracuseStep 200927 = 301391) B301391
theorem B200943 : Blo 199806 200943 := bstep (se 1 (by rfl) ⟨150707, by rfl⟩ : syracuseStep 200943 = 301415) B301415
theorem B200987 : Blo 199806 200987 := bstep (se 1 (by rfl) ⟨150740, by rfl⟩ : syracuseStep 200987 = 301481) B301481
theorem B1151273 : Blo 199806 1151273 := bstep (se 2 (by rfl) ⟨431727, by rfl⟩ : syracuseStep 1151273 = 863455) B863455
theorem B627191 : Blo 199806 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B201243 : Blo 199806 201243 := bstep (se 1 (by rfl) ⟨150932, by rfl⟩ : syracuseStep 201243 = 301865) B301865
theorem B201383 : Blo 199806 201383 := bstep (se 1 (by rfl) ⟨151037, by rfl⟩ : syracuseStep 201383 = 302075) B302075
theorem B201407 : Blo 199806 201407 := bstep (se 1 (by rfl) ⟨151055, by rfl⟩ : syracuseStep 201407 = 302111) B302111
theorem B201423 : Blo 199806 201423 := bstep (se 1 (by rfl) ⟨151067, by rfl⟩ : syracuseStep 201423 = 302135) B302135
theorem B201503 : Blo 199806 201503 := bstep (se 1 (by rfl) ⟨151127, by rfl⟩ : syracuseStep 201503 = 302255) B302255
theorem B201599 : Blo 199806 201599 := bstep (se 1 (by rfl) ⟨151199, by rfl⟩ : syracuseStep 201599 = 302399) B302399
theorem B1282985 : Blo 199806 1282985 := bstep (se 2 (by rfl) ⟨481119, by rfl⟩ : syracuseStep 1282985 = 962239) B962239
theorem B201695 : Blo 199806 201695 := bstep (se 1 (by rfl) ⟨151271, by rfl⟩ : syracuseStep 201695 = 302543) B302543
theorem B1151981 : Blo 199806 1151981 := bstep (se 3 (by rfl) ⟨215996, by rfl⟩ : syracuseStep 1151981 = 431993) B431993
theorem B300191 : Blo 199806 300191 := bstep (se 1 (by rfl) ⟨225143, by rfl⟩ : syracuseStep 300191 = 450287) B450287
theorem B201951 : Blo 199806 201951 := bstep (se 1 (by rfl) ⟨151463, by rfl⟩ : syracuseStep 201951 = 302927) B302927
theorem B201983 : Blo 199806 201983 := bstep (se 1 (by rfl) ⟨151487, by rfl⟩ : syracuseStep 201983 = 302975) B302975
theorem B202031 : Blo 199806 202031 := bstep (se 1 (by rfl) ⟨151523, by rfl⟩ : syracuseStep 202031 = 303047) B303047
theorem B202191 : Blo 199806 202191 := bstep (se 1 (by rfl) ⟨151643, by rfl⟩ : syracuseStep 202191 = 303287) B303287
theorem B202271 : Blo 199806 202271 := bstep (se 1 (by rfl) ⟨151703, by rfl⟩ : syracuseStep 202271 = 303407) B303407
theorem B202431 : Blo 199806 202431 := bstep (se 1 (by rfl) ⟨151823, by rfl⟩ : syracuseStep 202431 = 303647) B303647
theorem B202471 : Blo 199806 202471 := bstep (se 1 (by rfl) ⟨151853, by rfl⟩ : syracuseStep 202471 = 303707) B303707
theorem B300809 : Blo 199806 300809 := bstep (se 2 (by rfl) ⟨112803, by rfl⟩ : syracuseStep 300809 = 225607) B225607
theorem B202815 : Blo 199806 202815 := bstep (se 1 (by rfl) ⟨152111, by rfl⟩ : syracuseStep 202815 = 304223) B304223
theorem B202855 : Blo 199806 202855 := bstep (se 1 (by rfl) ⟨152141, by rfl⟩ : syracuseStep 202855 = 304283) B304283
theorem B1022057 : Blo 199806 1022057 := bstep (se 2 (by rfl) ⟨383271, by rfl⟩ : syracuseStep 1022057 = 766543) B766543
theorem B301433 : Blo 199806 301433 := bstep (se 2 (by rfl) ⟨113037, by rfl⟩ : syracuseStep 301433 = 226075) B226075
theorem B203163 : Blo 199806 203163 := bstep (se 1 (by rfl) ⟨152372, by rfl⟩ : syracuseStep 203163 = 304745) B304745
theorem B760225 : Blo 199806 760225 := bstep (se 2 (by rfl) ⟨285084, by rfl⟩ : syracuseStep 760225 = 570169) B570169
theorem B203247 : Blo 199806 203247 := bstep (se 1 (by rfl) ⟨152435, by rfl⟩ : syracuseStep 203247 = 304871) B304871
theorem B203311 : Blo 199806 203311 := bstep (se 1 (by rfl) ⟨152483, by rfl⟩ : syracuseStep 203311 = 304967) B304967
theorem B203583 : Blo 199806 203583 := bstep (se 1 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 203583 = 305375) B305375
theorem B203623 : Blo 199806 203623 := bstep (se 1 (by rfl) ⟨152717, by rfl⟩ : syracuseStep 203623 = 305435) B305435
theorem B301961 : Blo 199806 301961 := bstep (se 2 (by rfl) ⟨113235, by rfl⟩ : syracuseStep 301961 = 226471) B226471
theorem B203711 : Blo 199806 203711 := bstep (se 1 (by rfl) ⟨152783, by rfl⟩ : syracuseStep 203711 = 305567) B305567
theorem B1711327 : Blo 199806 1711327 := bstep (se 1 (by rfl) ⟨1283495, by rfl⟩ : syracuseStep 1711327 = 2566991) B2566991
theorem B433471 : Blo 199806 433471 := bstep (se 1 (by rfl) ⟨325103, by rfl⟩ : syracuseStep 433471 = 650207) B650207
theorem B302495 : Blo 199806 302495 := bstep (se 1 (by rfl) ⟨226871, by rfl⟩ : syracuseStep 302495 = 453743) B453743
theorem B302639 : Blo 199806 302639 := bstep (se 1 (by rfl) ⟨226979, by rfl⟩ : syracuseStep 302639 = 453959) B453959
theorem B303167 : Blo 199806 303167 := bstep (se 1 (by rfl) ⟨227375, by rfl⟩ : syracuseStep 303167 = 454751) B454751
theorem B729263 : Blo 199806 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B762473 : Blo 199806 762473 := bstep (se 2 (by rfl) ⟨285927, by rfl⟩ : syracuseStep 762473 = 571855) B571855
theorem B2171873 : Blo 199806 2171873 := bstep (se 2 (by rfl) ⟨814452, by rfl⟩ : syracuseStep 2171873 = 1628905) B1628905
theorem B730271 : Blo 199806 730271 := bstep (se 1 (by rfl) ⟨547703, by rfl⟩ : syracuseStep 730271 = 1095407) B1095407
theorem B304319 : Blo 199806 304319 := bstep (se 1 (by rfl) ⟨228239, by rfl⟩ : syracuseStep 304319 = 456479) B456479
theorem B304505 : Blo 199806 304505 := bstep (se 2 (by rfl) ⟨114189, by rfl⟩ : syracuseStep 304505 = 228379) B228379
theorem B337439 : Blo 199806 337439 := bstep (se 1 (by rfl) ⟨253079, by rfl⟩ : syracuseStep 337439 = 506159) B506159
theorem B305129 : Blo 199806 305129 := bstep (se 2 (by rfl) ⟨114423, by rfl⟩ : syracuseStep 305129 = 228847) B228847
theorem B1091819 : Blo 199806 1091819 := bstep (se 1 (by rfl) ⟨818864, by rfl⟩ : syracuseStep 1091819 = 1637729) B1637729
theorem B305615 : Blo 199806 305615 := bstep (se 1 (by rfl) ⟨229211, by rfl⟩ : syracuseStep 305615 = 458423) B458423
theorem B764873 : Blo 199806 764873 := bstep (se 2 (by rfl) ⟨286827, by rfl⟩ : syracuseStep 764873 = 573655) B573655
theorem B961931 : Blo 199806 961931 := bstep (se 1 (by rfl) ⟨721448, by rfl⟩ : syracuseStep 961931 = 1442897) B1442897
theorem B340105 : Blo 199806 340105 := bstep (se 2 (by rfl) ⟨127539, by rfl⟩ : syracuseStep 340105 = 255079) B255079
theorem B1028371 : Blo 199806 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B2175335 : Blo 199806 2175335 := bstep (se 1 (by rfl) ⟨1631501, by rfl⟩ : syracuseStep 2175335 = 3263003) B3263003
theorem B2568631 : Blo 199806 2568631 := bstep (se 1 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 2568631 = 3852947) B3852947
theorem B1520207 : Blo 199806 1520207 := bstep (se 1 (by rfl) ⟨1140155, by rfl⟩ : syracuseStep 1520207 = 2280311) B2280311
theorem B340895 : Blo 199806 340895 := bstep (se 1 (by rfl) ⟨255671, by rfl⟩ : syracuseStep 340895 = 511343) B511343
theorem B636167 : Blo 199806 636167 := bstep (se 1 (by rfl) ⟨477125, by rfl⟩ : syracuseStep 636167 = 954251) B954251
theorem B14005993 : Blo 199806 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B1029995 : Blo 199806 1029995 := bstep (se 1 (by rfl) ⟨772496, by rfl⟩ : syracuseStep 1029995 = 1544993) B1544993
theorem B505835 : Blo 199806 505835 := bstep (se 1 (by rfl) ⟨379376, by rfl⟩ : syracuseStep 505835 = 758753) B758753
theorem B2898017 : Blo 199806 2898017 := bstep (se 2 (by rfl) ⟨1086756, by rfl⟩ : syracuseStep 2898017 = 2173513) B2173513
theorem B1030319 : Blo 199806 1030319 := bstep (se 1 (by rfl) ⟨772739, by rfl⟩ : syracuseStep 1030319 = 1545479) B1545479
theorem B342427 : Blo 199806 342427 := bstep (se 1 (by rfl) ⟨256820, by rfl⟩ : syracuseStep 342427 = 513641) B513641
theorem B5782427 : Blo 199806 5782427 := bstep (se 1 (by rfl) ⟨4336820, by rfl⟩ : syracuseStep 5782427 = 8673641) B8673641
theorem B2440145 : Blo 199806 2440145 := bstep (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) B1830109
theorem B867455 : Blo 199806 867455 := bstep (se 1 (by rfl) ⟨650591, by rfl⟩ : syracuseStep 867455 = 1301183) B1301183
theorem B2670191 : Blo 199806 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B507667 : Blo 199806 507667 := bstep (se 1 (by rfl) ⟨380750, by rfl⟩ : syracuseStep 507667 = 761501) B761501
theorem B769931 : Blo 199806 769931 := bstep (se 1 (by rfl) ⟨577448, by rfl⟩ : syracuseStep 769931 = 1154897) B1154897
theorem B409627 : Blo 199806 409627 := bstep (se 1 (by rfl) ⟨307220, by rfl⟩ : syracuseStep 409627 = 614441) B614441
theorem B214087 : Blo 199806 214087 := bstep (se 1 (by rfl) ⟨160565, by rfl⟩ : syracuseStep 214087 = 321131) B321131
theorem B411361 : Blo 199806 411361 := bstep (se 2 (by rfl) ⟨154260, by rfl⟩ : syracuseStep 411361 = 308521) B308521
theorem B214907 : Blo 199806 214907 := bstep (se 1 (by rfl) ⟨161180, by rfl⟩ : syracuseStep 214907 = 322361) B322361
theorem B346295 : Blo 199806 346295 := bstep (se 1 (by rfl) ⟨259721, by rfl⟩ : syracuseStep 346295 = 519443) B519443
theorem B2345435 : Blo 199806 2345435 := bstep (se 1 (by rfl) ⟨1759076, by rfl⟩ : syracuseStep 2345435 = 3518153) B3518153
theorem B772649 : Blo 199806 772649 := bstep (se 2 (by rfl) ⟨289743, by rfl⟩ : syracuseStep 772649 = 579487) B579487
theorem B1624657 : Blo 199806 1624657 := bstep (se 2 (by rfl) ⟨609246, by rfl⟩ : syracuseStep 1624657 = 1218493) B1218493
theorem B412303 : Blo 199806 412303 := bstep (se 1 (by rfl) ⟨309227, by rfl⟩ : syracuseStep 412303 = 618455) B618455
theorem B674459 : Blo 199806 674459 := bstep (se 1 (by rfl) ⟨505844, by rfl⟩ : syracuseStep 674459 = 1011689) B1011689
theorem B3459833 : Blo 199806 3459833 := bstep (se 2 (by rfl) ⟨1297437, by rfl⟩ : syracuseStep 3459833 = 2594875) B2594875
theorem B379657 : Blo 199806 379657 := bstep (se 2 (by rfl) ⟨142371, by rfl⟩ : syracuseStep 379657 = 284743) B284743
theorem B674999 : Blo 199806 674999 := bstep (se 1 (by rfl) ⟨506249, by rfl⟩ : syracuseStep 674999 = 1012499) B1012499
theorem B970003 : Blo 199806 970003 := bstep (se 1 (by rfl) ⟨727502, by rfl⟩ : syracuseStep 970003 = 1455005) B1455005
theorem B380371 : Blo 199806 380371 := bstep (se 1 (by rfl) ⟨285278, by rfl⟩ : syracuseStep 380371 = 570557) B570557
theorem B773651 : Blo 199806 773651 := bstep (se 1 (by rfl) ⟨580238, by rfl⟩ : syracuseStep 773651 = 1160477) B1160477
theorem B773819 : Blo 199806 773819 := bstep (se 1 (by rfl) ⟨580364, by rfl⟩ : syracuseStep 773819 = 1160729) B1160729
theorem B544871 : Blo 199806 544871 := bstep (se 1 (by rfl) ⟨408653, by rfl⟩ : syracuseStep 544871 = 817307) B817307
theorem B643211 : Blo 199806 643211 := bstep (se 1 (by rfl) ⟨482408, by rfl⟩ : syracuseStep 643211 = 964817) B964817
theorem B676295 : Blo 199806 676295 := bstep (se 1 (by rfl) ⟨507221, by rfl⟩ : syracuseStep 676295 = 1014443) B1014443
theorem B513449 : Blo 199806 513449 := bstep (se 2 (by rfl) ⟨192543, by rfl⟩ : syracuseStep 513449 = 385087) B385087
theorem B1922555 : Blo 199806 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B1104043 : Blo 199806 1104043 := bstep (se 1 (by rfl) ⟨828032, by rfl⟩ : syracuseStep 1104043 = 1656065) B1656065
theorem B383287 : Blo 199806 383287 := bstep (se 1 (by rfl) ⟨287465, by rfl⟩ : syracuseStep 383287 = 574931) B574931
theorem B678239 : Blo 199806 678239 := bstep (se 1 (by rfl) ⟨508679, by rfl⟩ : syracuseStep 678239 = 1017359) B1017359
theorem B1956271 : Blo 199806 1956271 := bstep (se 1 (by rfl) ⟨1467203, by rfl⟩ : syracuseStep 1956271 = 2934407) B2934407
theorem B3889853 : Blo 199806 3889853 := bstep (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) B1458695
theorem B678887 : Blo 199806 678887 := bstep (se 1 (by rfl) ⟨509165, by rfl⟩ : syracuseStep 678887 = 1018331) B1018331
theorem B252983 : Blo 199806 252983 := bstep (se 1 (by rfl) ⟨189737, by rfl⟩ : syracuseStep 252983 = 379475) B379475
theorem B678995 : Blo 199806 678995 := bstep (se 1 (by rfl) ⟨509246, by rfl⟩ : syracuseStep 678995 = 1018493) B1018493
theorem B679049 : Blo 199806 679049 := bstep (se 2 (by rfl) ⟨254643, by rfl⟩ : syracuseStep 679049 = 509287) B509287
theorem B679103 : Blo 199806 679103 := bstep (se 1 (by rfl) ⟨509327, by rfl⟩ : syracuseStep 679103 = 1018655) B1018655
theorem B449819 : Blo 199806 449819 := bstep (se 1 (by rfl) ⟨337364, by rfl⟩ : syracuseStep 449819 = 674729) B674729
theorem B449855 : Blo 199806 449855 := bstep (se 1 (by rfl) ⟨337391, by rfl⟩ : syracuseStep 449855 = 674783) B674783
theorem B1957229 : Blo 199806 1957229 := bstep (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) B733961
theorem B450017 : Blo 199806 450017 := bstep (se 2 (by rfl) ⟨168756, by rfl⟩ : syracuseStep 450017 = 337513) B337513
theorem B384905 : Blo 199806 384905 := bstep (se 2 (by rfl) ⟨144339, by rfl⟩ : syracuseStep 384905 = 288679) B288679
theorem B1400743 : Blo 199806 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B679913 : Blo 199806 679913 := bstep (se 2 (by rfl) ⟨254967, by rfl⟩ : syracuseStep 679913 = 509935) B509935
theorem B1466369 : Blo 199806 1466369 := bstep (se 2 (by rfl) ⟨549888, by rfl⟩ : syracuseStep 1466369 = 1099777) B1099777
theorem B2286143 : Blo 199806 2286143 := bstep (se 1 (by rfl) ⟨1714607, by rfl⟩ : syracuseStep 2286143 = 3429215) B3429215
theorem B1729097 : Blo 199806 1729097 := bstep (se 2 (by rfl) ⟨648411, by rfl⟩ : syracuseStep 1729097 = 1296823) B1296823
theorem B451691 : Blo 199806 451691 := bstep (se 1 (by rfl) ⟨338768, by rfl⟩ : syracuseStep 451691 = 677537) B677537
theorem B4908221 : Blo 199806 4908221 := bstep (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) B1840583
theorem B452267 : Blo 199806 452267 := bstep (se 1 (by rfl) ⟨339200, by rfl⟩ : syracuseStep 452267 = 678401) B678401
theorem B1337719 : Blo 199806 1337719 := bstep (se 1 (by rfl) ⟨1003289, by rfl⟩ : syracuseStep 1337719 = 2006579) B2006579
theorem B452987 : Blo 199806 452987 := bstep (se 1 (by rfl) ⟨339740, by rfl⟩ : syracuseStep 452987 = 679481) B679481
theorem B453095 : Blo 199806 453095 := bstep (se 1 (by rfl) ⟨339821, by rfl⟩ : syracuseStep 453095 = 679643) B679643
theorem B3894317 : Blo 199806 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B978155 : Blo 199806 978155 := bstep (se 1 (by rfl) ⟨733616, by rfl⟩ : syracuseStep 978155 = 1467233) B1467233
theorem B453995 : Blo 199806 453995 := bstep (se 1 (by rfl) ⟨340496, by rfl⟩ : syracuseStep 453995 = 680993) B680993
theorem B257519 : Blo 199806 257519 := bstep (se 1 (by rfl) ⟨193139, by rfl⟩ : syracuseStep 257519 = 386279) B386279
theorem B487079 : Blo 199806 487079 := bstep (se 1 (by rfl) ⟨365309, by rfl⟩ : syracuseStep 487079 = 730619) B730619
theorem B683801 : Blo 199806 683801 := bstep (se 2 (by rfl) ⟨256425, by rfl⟩ : syracuseStep 683801 = 512851) B512851
theorem B2977769 : Blo 199806 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B225535 : Blo 199806 225535 := bstep (se 1 (by rfl) ⟨169151, by rfl⟩ : syracuseStep 225535 = 338303) B338303
theorem B3044243 : Blo 199806 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B685043 : Blo 199806 685043 := bstep (se 1 (by rfl) ⟨513782, by rfl⟩ : syracuseStep 685043 = 1027565) B1027565
theorem B455993 : Blo 199806 455993 := bstep (se 2 (by rfl) ⟨170997, by rfl⟩ : syracuseStep 455993 = 341995) B341995
theorem B456047 : Blo 199806 456047 := bstep (se 1 (by rfl) ⟨342035, by rfl⟩ : syracuseStep 456047 = 684071) B684071
theorem B226687 : Blo 199806 226687 := bstep (se 1 (by rfl) ⟨170015, by rfl⟩ : syracuseStep 226687 = 340031) B340031
theorem B685907 : Blo 199806 685907 := bstep (se 1 (by rfl) ⟨514430, by rfl⟩ : syracuseStep 685907 = 1028861) B1028861
theorem B686015 : Blo 199806 686015 := bstep (se 1 (by rfl) ⟨514511, by rfl⟩ : syracuseStep 686015 = 1029023) B1029023
theorem B456731 : Blo 199806 456731 := bstep (se 1 (by rfl) ⟨342548, by rfl⟩ : syracuseStep 456731 = 685097) B685097
theorem B456767 : Blo 199806 456767 := bstep (se 1 (by rfl) ⟨342575, by rfl⟩ : syracuseStep 456767 = 685151) B685151
theorem B15694117 : Blo 199806 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B686825 : Blo 199806 686825 := bstep (se 2 (by rfl) ⟨257559, by rfl⟩ : syracuseStep 686825 = 515119) B515119
theorem B818345 : Blo 199806 818345 := bstep (se 2 (by rfl) ⟨306879, by rfl⟩ : syracuseStep 818345 = 613759) B613759
theorem B2293433 : Blo 199806 2293433 := bstep (se 2 (by rfl) ⟨860037, by rfl⟩ : syracuseStep 2293433 = 1720075) B1720075
theorem B230863 : Blo 199806 230863 := bstep (se 1 (by rfl) ⟨173147, by rfl⟩ : syracuseStep 230863 = 346295) B346295
theorem B363247 : Blo 199806 363247 := bstep (se 1 (by rfl) ⟨272435, by rfl⟩ : syracuseStep 363247 = 544871) B544871
theorem B428807 : Blo 199806 428807 := bstep (se 1 (by rfl) ⟨321605, by rfl⟩ : syracuseStep 428807 = 643211) B643211
theorem B920585 : Blo 199806 920585 := bstep (se 2 (by rfl) ⟨345219, by rfl⟩ : syracuseStep 920585 = 690439) B690439
theorem B855323 : Blo 199806 855323 := bstep (se 1 (by rfl) ⟨641492, by rfl⟩ : syracuseStep 855323 = 1282985) B1282985
theorem B200127 : Blo 199806 200127 := bstep (se 1 (by rfl) ⟨150095, by rfl⟩ : syracuseStep 200127 = 300191) B300191
theorem B2166209 : Blo 199806 2166209 := bstep (se 2 (by rfl) ⟨812328, by rfl⟩ : syracuseStep 2166209 = 1624657) B1624657
theorem B1281703 : Blo 199806 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B200539 : Blo 199806 200539 := bstep (se 1 (by rfl) ⟨150404, by rfl⟩ : syracuseStep 200539 = 300809) B300809
theorem B200955 : Blo 199806 200955 := bstep (se 1 (by rfl) ⟨150716, by rfl⟩ : syracuseStep 200955 = 301433) B301433
theorem B2593235 : Blo 199806 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B201307 : Blo 199806 201307 := bstep (se 1 (by rfl) ⟨150980, by rfl⟩ : syracuseStep 201307 = 301961) B301961
theorem B299879 : Blo 199806 299879 := bstep (se 1 (by rfl) ⟨224909, by rfl⟩ : syracuseStep 299879 = 449819) B449819
theorem B299903 : Blo 199806 299903 := bstep (se 1 (by rfl) ⟨224927, by rfl⟩ : syracuseStep 299903 = 449855) B449855
theorem B201663 : Blo 199806 201663 := bstep (se 1 (by rfl) ⟨151247, by rfl⟩ : syracuseStep 201663 = 302495) B302495
theorem B300011 : Blo 199806 300011 := bstep (se 1 (by rfl) ⟨225008, by rfl⟩ : syracuseStep 300011 = 450017) B450017
theorem B201759 : Blo 199806 201759 := bstep (se 1 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 201759 = 302639) B302639
theorem B202111 : Blo 199806 202111 := bstep (se 1 (by rfl) ⟨151583, by rfl⟩ : syracuseStep 202111 = 303167) B303167
theorem B300713 : Blo 199806 300713 := bstep (se 2 (by rfl) ⟨112767, by rfl⟩ : syracuseStep 300713 = 225535) B225535
theorem B1152731 : Blo 199806 1152731 := bstep (se 1 (by rfl) ⟨864548, by rfl⟩ : syracuseStep 1152731 = 1729097) B1729097
theorem B1447915 : Blo 199806 1447915 := bstep (se 1 (by rfl) ⟨1085936, by rfl⟩ : syracuseStep 1447915 = 2171873) B2171873
theorem B301127 : Blo 199806 301127 := bstep (se 1 (by rfl) ⟨225845, by rfl⟩ : syracuseStep 301127 = 451691) B451691
theorem B202879 : Blo 199806 202879 := bstep (se 1 (by rfl) ⟨152159, by rfl⟩ : syracuseStep 202879 = 304319) B304319
theorem B203003 : Blo 199806 203003 := bstep (se 1 (by rfl) ⟨152252, by rfl⟩ : syracuseStep 203003 = 304505) B304505
theorem B301511 : Blo 199806 301511 := bstep (se 1 (by rfl) ⟨226133, by rfl⟩ : syracuseStep 301511 = 452267) B452267
theorem B203419 : Blo 199806 203419 := bstep (se 1 (by rfl) ⟨152564, by rfl⟩ : syracuseStep 203419 = 305129) B305129
theorem B727879 : Blo 199806 727879 := bstep (se 1 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 727879 = 1091819) B1091819
theorem B301991 : Blo 199806 301991 := bstep (se 1 (by rfl) ⟨226493, by rfl⟩ : syracuseStep 301991 = 452987) B452987
theorem B203743 : Blo 199806 203743 := bstep (se 1 (by rfl) ⟨152807, by rfl⟩ : syracuseStep 203743 = 305615) B305615
theorem B302063 : Blo 199806 302063 := bstep (se 1 (by rfl) ⟨226547, by rfl⟩ : syracuseStep 302063 = 453095) B453095
theorem B302249 : Blo 199806 302249 := bstep (se 2 (by rfl) ⟨113343, by rfl⟩ : syracuseStep 302249 = 226687) B226687
theorem B2596211 : Blo 199806 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B302663 : Blo 199806 302663 := bstep (se 1 (by rfl) ⟨226997, by rfl⟩ : syracuseStep 302663 = 453995) B453995
theorem B1450223 : Blo 199806 1450223 := bstep (se 1 (by rfl) ⟨1087667, by rfl⟩ : syracuseStep 1450223 = 2175335) B2175335
theorem B303995 : Blo 199806 303995 := bstep (se 1 (by rfl) ⟨227996, by rfl⟩ : syracuseStep 303995 = 455993) B455993
theorem B304031 : Blo 199806 304031 := bstep (se 1 (by rfl) ⟨228023, by rfl⟩ : syracuseStep 304031 = 456047) B456047
theorem B337223 : Blo 199806 337223 := bstep (se 1 (by rfl) ⟨252917, by rfl⟩ : syracuseStep 337223 = 505835) B505835
theorem B304487 : Blo 199806 304487 := bstep (se 1 (by rfl) ⟨228365, by rfl⟩ : syracuseStep 304487 = 456731) B456731
theorem B304511 : Blo 199806 304511 := bstep (se 1 (by rfl) ⟨228383, by rfl⟩ : syracuseStep 304511 = 456767) B456767
theorem B1780127 : Blo 199806 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B7940717 : Blo 199806 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B4926901 : Blo 199806 4926901 := bstep (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) B461897
theorem B1028051 : Blo 199806 1028051 := bstep (se 1 (by rfl) ⟨771038, by rfl⟩ : syracuseStep 1028051 = 1542077) B1542077
theorem B569339 : Blo 199806 569339 := bstep (se 1 (by rfl) ⟨427004, by rfl⟩ : syracuseStep 569339 = 854009) B854009
theorem B83701957 : Blo 199806 83701957 := bstep (se 4 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 83701957 = 15694117) B15694117
theorem B2306555 : Blo 199806 2306555 := bstep (se 1 (by rfl) ⟨1729916, by rfl⟩ : syracuseStep 2306555 = 3459833) B3459833
theorem B963161 : Blo 199806 963161 := bstep (se 2 (by rfl) ⟨361185, by rfl⟩ : syracuseStep 963161 = 722371) B722371
theorem B767303 : Blo 199806 767303 := bstep (se 1 (by rfl) ⟨575477, by rfl⟩ : syracuseStep 767303 = 1150955) B1150955
theorem B767515 : Blo 199806 767515 := bstep (se 1 (by rfl) ⟨575636, by rfl⟩ : syracuseStep 767515 = 1151273) B1151273
theorem B1783625 : Blo 199806 1783625 := bstep (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) B1337719
theorem B767987 : Blo 199806 767987 := bstep (se 1 (by rfl) ⟨575990, by rfl⟩ : syracuseStep 767987 = 1151981) B1151981
theorem B342299 : Blo 199806 342299 := bstep (se 1 (by rfl) ⟨256724, by rfl⟩ : syracuseStep 342299 = 513449) B513449
theorem B506209 : Blo 199806 506209 := bstep (se 2 (by rfl) ⟨189828, by rfl⟩ : syracuseStep 506209 = 379657) B379657
theorem B2275937 : Blo 199806 2275937 := bstep (se 2 (by rfl) ⟨853476, by rfl⟩ : syracuseStep 2275937 = 1706953) B1706953
theorem B572129 : Blo 199806 572129 := bstep (se 2 (by rfl) ⟨214548, by rfl⟩ : syracuseStep 572129 = 429097) B429097
theorem B1293337 : Blo 199806 1293337 := bstep (se 2 (by rfl) ⟨485001, by rfl⟩ : syracuseStep 1293337 = 970003) B970003
theorem B507161 : Blo 199806 507161 := bstep (se 2 (by rfl) ⟨190185, by rfl⟩ : syracuseStep 507161 = 380371) B380371
theorem B573085 : Blo 199806 573085 := bstep (se 3 (by rfl) ⟨107453, by rfl⟩ : syracuseStep 573085 = 214907) B214907
theorem B1524095 : Blo 199806 1524095 := bstep (se 1 (by rfl) ⟨1143071, by rfl⟩ : syracuseStep 1524095 = 2286143) B2286143
theorem B508315 : Blo 199806 508315 := bstep (se 1 (by rfl) ⟨381236, by rfl⟩ : syracuseStep 508315 = 762473) B762473
theorem B3424841 : Blo 199806 3424841 := bstep (se 2 (by rfl) ⟨1284315, by rfl⟩ : syracuseStep 3424841 = 2568631) B2568631
theorem B509915 : Blo 199806 509915 := bstep (se 1 (by rfl) ⟨382436, by rfl⟩ : syracuseStep 509915 = 764873) B764873
theorem B641287 : Blo 199806 641287 := bstep (se 1 (by rfl) ⟨480965, by rfl⟩ : syracuseStep 641287 = 961931) B961931
theorem B674621 : Blo 199806 674621 := bstep (se 3 (by rfl) ⟨126491, by rfl⟩ : syracuseStep 674621 = 252983) B252983
theorem B511049 : Blo 199806 511049 := bstep (se 2 (by rfl) ⟨191643, by rfl⟩ : syracuseStep 511049 = 383287) B383287
theorem B2608361 : Blo 199806 2608361 := bstep (se 2 (by rfl) ⟨978135, by rfl⟩ : syracuseStep 2608361 = 1956271) B1956271
theorem B2281769 : Blo 199806 2281769 := bstep (se 2 (by rfl) ⟨855663, by rfl⟩ : syracuseStep 2281769 = 1711327) B1711327
theorem B577961 : Blo 199806 577961 := bstep (se 2 (by rfl) ⟨216735, by rfl⟩ : syracuseStep 577961 = 433471) B433471
theorem B3854951 : Blo 199806 3854951 := bstep (se 1 (by rfl) ⟨2891213, by rfl⟩ : syracuseStep 3854951 = 5782427) B5782427
theorem B1626763 : Blo 199806 1626763 := bstep (se 1 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 1626763 = 2440145) B2440145
theorem B578303 : Blo 199806 578303 := bstep (se 1 (by rfl) ⟨433727, by rfl⟩ : syracuseStep 578303 = 867455) B867455
theorem B545563 : Blo 199806 545563 := bstep (se 1 (by rfl) ⟨409172, by rfl⟩ : syracuseStep 545563 = 818345) B818345
theorem B676889 : Blo 199806 676889 := bstep (se 2 (by rfl) ⟨253833, by rfl⟩ : syracuseStep 676889 = 507667) B507667
theorem B1528955 : Blo 199806 1528955 := bstep (se 1 (by rfl) ⟨1146716, by rfl⟩ : syracuseStep 1528955 = 2293433) B2293433
theorem B513287 : Blo 199806 513287 := bstep (se 1 (by rfl) ⟨384965, by rfl⟩ : syracuseStep 513287 = 769931) B769931
theorem B2184677 : Blo 199806 2184677 := bstep (se 4 (by rfl) ⟨204813, by rfl⟩ : syracuseStep 2184677 = 409627) B409627
theorem B677483 : Blo 199806 677483 := bstep (se 1 (by rfl) ⟨508112, by rfl⟩ : syracuseStep 677483 = 1016225) B1016225
theorem B285449 : Blo 199806 285449 := bstep (se 2 (by rfl) ⟨107043, by rfl⟩ : syracuseStep 285449 = 214087) B214087
theorem B678779 : Blo 199806 678779 := bstep (se 1 (by rfl) ⟨509084, by rfl⟩ : syracuseStep 678779 = 1018169) B1018169
theorem B1563623 : Blo 199806 1563623 := bstep (se 1 (by rfl) ⟨1172717, by rfl⟩ : syracuseStep 1563623 = 2345435) B2345435
theorem B515099 : Blo 199806 515099 := bstep (se 1 (by rfl) ⟨386324, by rfl⟩ : syracuseStep 515099 = 772649) B772649
theorem B449639 : Blo 199806 449639 := bstep (se 1 (by rfl) ⟨337229, by rfl⟩ : syracuseStep 449639 = 674459) B674459
theorem B875863 : Blo 199806 875863 := bstep (se 1 (by rfl) ⟨656897, by rfl⟩ : syracuseStep 875863 = 1313795) B1313795
theorem B449999 : Blo 199806 449999 := bstep (se 1 (by rfl) ⟨337499, by rfl⟩ : syracuseStep 449999 = 674999) B674999
theorem B515767 : Blo 199806 515767 := bstep (se 1 (by rfl) ⟨386825, by rfl⟩ : syracuseStep 515767 = 773651) B773651
theorem B515879 : Blo 199806 515879 := bstep (se 1 (by rfl) ⟨386909, by rfl⟩ : syracuseStep 515879 = 773819) B773819
theorem B548819 : Blo 199806 548819 := bstep (se 1 (by rfl) ⟨411614, by rfl⟩ : syracuseStep 548819 = 823229) B823229
theorem B1531871 : Blo 199806 1531871 := bstep (se 1 (by rfl) ⟨1148903, by rfl⟩ : syracuseStep 1531871 = 2297807) B2297807
theorem B450863 : Blo 199806 450863 := bstep (se 1 (by rfl) ⟨338147, by rfl⟩ : syracuseStep 450863 = 676295) B676295
theorem B418127 : Blo 199806 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B549737 : Blo 199806 549737 := bstep (se 2 (by rfl) ⟨206151, by rfl⟩ : syracuseStep 549737 = 412303) B412303
theorem B681371 : Blo 199806 681371 := bstep (se 1 (by rfl) ⟨511028, by rfl⟩ : syracuseStep 681371 = 1022057) B1022057
theorem B452159 : Blo 199806 452159 := bstep (se 1 (by rfl) ⟨339119, by rfl⟩ : syracuseStep 452159 = 678239) B678239
theorem B452591 : Blo 199806 452591 := bstep (se 1 (by rfl) ⟨339443, by rfl⟩ : syracuseStep 452591 = 678887) B678887
theorem B8775701 : Blo 199806 8775701 := bstep (se 6 (by rfl) ⟨205680, by rfl⟩ : syracuseStep 8775701 = 411361) B411361
theorem B452663 : Blo 199806 452663 := bstep (se 1 (by rfl) ⟨339497, by rfl⟩ : syracuseStep 452663 = 678995) B678995
theorem B452699 : Blo 199806 452699 := bstep (se 1 (by rfl) ⟨339524, by rfl⟩ : syracuseStep 452699 = 679049) B679049
theorem B452735 : Blo 199806 452735 := bstep (se 1 (by rfl) ⟨339551, by rfl⟩ : syracuseStep 452735 = 679103) B679103
theorem B1304819 : Blo 199806 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B256603 : Blo 199806 256603 := bstep (se 1 (by rfl) ⟨192452, by rfl⟩ : syracuseStep 256603 = 384905) B384905
theorem B453275 : Blo 199806 453275 := bstep (se 1 (by rfl) ⟨339956, by rfl⟩ : syracuseStep 453275 = 679913) B679913
theorem B977579 : Blo 199806 977579 := bstep (se 1 (by rfl) ⟨733184, by rfl⟩ : syracuseStep 977579 = 1466369) B1466369
theorem B486175 : Blo 199806 486175 := bstep (se 1 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 486175 = 729263) B729263
theorem B453473 : Blo 199806 453473 := bstep (se 2 (by rfl) ⟨170052, by rfl⟩ : syracuseStep 453473 = 340105) B340105
theorem B1371161 : Blo 199806 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B486847 : Blo 199806 486847 := bstep (se 1 (by rfl) ⟨365135, by rfl⟩ : syracuseStep 486847 = 730271) B730271
theorem B3272147 : Blo 199806 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B224959 : Blo 199806 224959 := bstep (se 1 (by rfl) ⟨168719, by rfl⟩ : syracuseStep 224959 = 337439) B337439
theorem B652103 : Blo 199806 652103 := bstep (se 1 (by rfl) ⟨489077, by rfl⟩ : syracuseStep 652103 = 978155) B978155
theorem B18674657 : Blo 199806 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B324719 : Blo 199806 324719 := bstep (se 1 (by rfl) ⟨243539, by rfl⟩ : syracuseStep 324719 = 487079) B487079
theorem B455867 : Blo 199806 455867 := bstep (se 1 (by rfl) ⟨341900, by rfl⟩ : syracuseStep 455867 = 683801) B683801
theorem B1472057 : Blo 199806 1472057 := bstep (se 2 (by rfl) ⟨552021, by rfl⟩ : syracuseStep 1472057 = 1104043) B1104043
theorem B1013471 : Blo 199806 1013471 := bstep (se 1 (by rfl) ⟨760103, by rfl⟩ : syracuseStep 1013471 = 1520207) B1520207
theorem B456569 : Blo 199806 456569 := bstep (se 2 (by rfl) ⟨171213, by rfl⟩ : syracuseStep 456569 = 342427) B342427
theorem B1013633 : Blo 199806 1013633 := bstep (se 2 (by rfl) ⟨380112, by rfl⟩ : syracuseStep 1013633 = 760225) B760225
theorem B2029495 : Blo 199806 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B227263 : Blo 199806 227263 := bstep (se 1 (by rfl) ⟨170447, by rfl⟩ : syracuseStep 227263 = 340895) B340895
theorem B456695 : Blo 199806 456695 := bstep (se 1 (by rfl) ⟨342521, by rfl⟩ : syracuseStep 456695 = 685043) B685043
theorem B424111 : Blo 199806 424111 := bstep (se 1 (by rfl) ⟨318083, by rfl⟩ : syracuseStep 424111 = 636167) B636167
theorem B457271 : Blo 199806 457271 := bstep (se 1 (by rfl) ⟨342953, by rfl⟩ : syracuseStep 457271 = 685907) B685907
theorem B686663 : Blo 199806 686663 := bstep (se 1 (by rfl) ⟨514997, by rfl⟩ : syracuseStep 686663 = 1029995) B1029995
theorem B686717 : Blo 199806 686717 := bstep (se 3 (by rfl) ⟨128759, by rfl⟩ : syracuseStep 686717 = 257519) B257519
theorem B457343 : Blo 199806 457343 := bstep (se 1 (by rfl) ⟨343007, by rfl⟩ : syracuseStep 457343 = 686015) B686015
theorem B1932011 : Blo 199806 1932011 := bstep (se 1 (by rfl) ⟨1449008, by rfl⟩ : syracuseStep 1932011 = 2898017) B2898017
theorem B686879 : Blo 199806 686879 := bstep (se 1 (by rfl) ⟨515159, by rfl⟩ : syracuseStep 686879 = 1030319) B1030319
theorem B457883 : Blo 199806 457883 := bstep (se 1 (by rfl) ⟨343412, by rfl⟩ : syracuseStep 457883 = 686825) B686825
theorem B1867657 : Blo 199806 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B1016063 : Blo 199806 1016063 := bstep (se 1 (by rfl) ⟨762047, by rfl⟩ : syracuseStep 1016063 = 1524095) B1524095
theorem B1115005 : Blo 199806 1115005 := bstep (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) B418127
theorem B1738907 : Blo 199806 1738907 := bstep (se 1 (by rfl) ⟨1304180, by rfl⟩ : syracuseStep 1738907 = 2608361) B2608361
theorem B1444139 : Blo 199806 1444139 := bstep (se 1 (by rfl) ⟨1083104, by rfl⟩ : syracuseStep 1444139 = 2166209) B2166209
theorem B855049 : Blo 199806 855049 := bstep (se 2 (by rfl) ⟨320643, by rfl⟩ : syracuseStep 855049 = 641287) B641287
theorem B199919 : Blo 199806 199919 := bstep (se 1 (by rfl) ⟨149939, by rfl⟩ : syracuseStep 199919 = 299879) B299879
theorem B199935 : Blo 199806 199935 := bstep (se 1 (by rfl) ⟨149951, by rfl⟩ : syracuseStep 199935 = 299903) B299903
theorem B200007 : Blo 199806 200007 := bstep (se 1 (by rfl) ⟨150005, by rfl⟩ : syracuseStep 200007 = 300011) B300011
theorem B1019303 : Blo 199806 1019303 := bstep (se 1 (by rfl) ⟨764477, by rfl⟩ : syracuseStep 1019303 = 1528955) B1528955
theorem B200475 : Blo 199806 200475 := bstep (se 1 (by rfl) ⟨150356, by rfl⟩ : syracuseStep 200475 = 300713) B300713
theorem B1937317 : Blo 199806 1937317 := bstep (se 4 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 1937317 = 363247) B363247
theorem B200751 : Blo 199806 200751 := bstep (se 1 (by rfl) ⟨150563, by rfl⟩ : syracuseStep 200751 = 301127) B301127
theorem B201007 : Blo 199806 201007 := bstep (se 1 (by rfl) ⟨150755, by rfl⟩ : syracuseStep 201007 = 301511) B301511
theorem B201327 : Blo 199806 201327 := bstep (se 1 (by rfl) ⟨150995, by rfl⟩ : syracuseStep 201327 = 301991) B301991
theorem B201375 : Blo 199806 201375 := bstep (se 1 (by rfl) ⟨151031, by rfl⟩ : syracuseStep 201375 = 302063) B302063
theorem B299759 : Blo 199806 299759 := bstep (se 1 (by rfl) ⟨224819, by rfl⟩ : syracuseStep 299759 = 449639) B449639
theorem B201499 : Blo 199806 201499 := bstep (se 1 (by rfl) ⟨151124, by rfl⟩ : syracuseStep 201499 = 302249) B302249
theorem B4756333 : Blo 199806 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B1708937 : Blo 199806 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B299945 : Blo 199806 299945 := bstep (se 2 (by rfl) ⟨112479, by rfl⟩ : syracuseStep 299945 = 224959) B224959
theorem B299999 : Blo 199806 299999 := bstep (se 1 (by rfl) ⟨224999, by rfl⟩ : syracuseStep 299999 = 449999) B449999
theorem B201775 : Blo 199806 201775 := bstep (se 1 (by rfl) ⟨151331, by rfl⟩ : syracuseStep 201775 = 302663) B302663
theorem B365879 : Blo 199806 365879 := bstep (se 1 (by rfl) ⟨274409, by rfl⟩ : syracuseStep 365879 = 548819) B548819
theorem B1021247 : Blo 199806 1021247 := bstep (se 1 (by rfl) ⟨765935, by rfl⟩ : syracuseStep 1021247 = 1531871) B1531871
theorem B300575 : Blo 199806 300575 := bstep (se 1 (by rfl) ⟨225431, by rfl⟩ : syracuseStep 300575 = 450863) B450863
theorem B366491 : Blo 199806 366491 := bstep (se 1 (by rfl) ⟨274868, by rfl⟩ : syracuseStep 366491 = 549737) B549737
theorem B202663 : Blo 199806 202663 := bstep (se 1 (by rfl) ⟨151997, by rfl⟩ : syracuseStep 202663 = 303995) B303995
theorem B202687 : Blo 199806 202687 := bstep (se 1 (by rfl) ⟨152015, by rfl⟩ : syracuseStep 202687 = 304031) B304031
theorem B2169017 : Blo 199806 2169017 := bstep (se 2 (by rfl) ⟨813381, by rfl⟩ : syracuseStep 2169017 = 1626763) B1626763
theorem B202991 : Blo 199806 202991 := bstep (se 1 (by rfl) ⟨152243, by rfl⟩ : syracuseStep 202991 = 304487) B304487
theorem B203007 : Blo 199806 203007 := bstep (se 1 (by rfl) ⟨152255, by rfl⟩ : syracuseStep 203007 = 304511) B304511
theorem B727417 : Blo 199806 727417 := bstep (se 2 (by rfl) ⟨272781, by rfl⟩ : syracuseStep 727417 = 545563) B545563
theorem B301439 : Blo 199806 301439 := bstep (se 1 (by rfl) ⟨226079, by rfl⟩ : syracuseStep 301439 = 452159) B452159
theorem B301727 : Blo 199806 301727 := bstep (se 1 (by rfl) ⟨226295, by rfl⟩ : syracuseStep 301727 = 452591) B452591
theorem B301775 : Blo 199806 301775 := bstep (se 1 (by rfl) ⟨226331, by rfl⟩ : syracuseStep 301775 = 452663) B452663
theorem B301799 : Blo 199806 301799 := bstep (se 1 (by rfl) ⟨226349, by rfl⟩ : syracuseStep 301799 = 452699) B452699
theorem B301823 : Blo 199806 301823 := bstep (se 1 (by rfl) ⟨226367, by rfl⟩ : syracuseStep 301823 = 452735) B452735
theorem B1186751 : Blo 199806 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B302183 : Blo 199806 302183 := bstep (se 1 (by rfl) ⟨226637, by rfl⟩ : syracuseStep 302183 = 453275) B453275
theorem B302315 : Blo 199806 302315 := bstep (se 1 (by rfl) ⟨226736, by rfl⟩ : syracuseStep 302315 = 453473) B453473
theorem B761197 : Blo 199806 761197 := bstep (se 3 (by rfl) ⟨142724, by rfl⟩ : syracuseStep 761197 = 285449) B285449
theorem B1023353 : Blo 199806 1023353 := bstep (se 2 (by rfl) ⟨383757, by rfl⟩ : syracuseStep 1023353 = 767515) B767515
theorem B303017 : Blo 199806 303017 := bstep (se 2 (by rfl) ⟨113631, by rfl⟩ : syracuseStep 303017 = 227263) B227263
theorem B565481 : Blo 199806 565481 := bstep (se 2 (by rfl) ⟨212055, by rfl⟩ : syracuseStep 565481 = 424111) B424111
theorem B434735 : Blo 199806 434735 := bstep (se 1 (by rfl) ⟨326051, by rfl⟩ : syracuseStep 434735 = 652103) B652103
theorem B303911 : Blo 199806 303911 := bstep (se 1 (by rfl) ⟨227933, by rfl⟩ : syracuseStep 303911 = 455867) B455867
theorem B304379 : Blo 199806 304379 := bstep (se 1 (by rfl) ⟨228284, by rfl⟩ : syracuseStep 304379 = 456569) B456569
theorem B304463 : Blo 199806 304463 := bstep (se 1 (by rfl) ⟨228347, by rfl⟩ : syracuseStep 304463 = 456695) B456695
theorem B304847 : Blo 199806 304847 := bstep (se 1 (by rfl) ⟨228635, by rfl⟩ : syracuseStep 304847 = 457271) B457271
theorem B1517291 : Blo 199806 1517291 := bstep (se 1 (by rfl) ⟨1137968, by rfl⟩ : syracuseStep 1517291 = 2275937) B2275937
theorem B304895 : Blo 199806 304895 := bstep (se 1 (by rfl) ⟨228671, by rfl⟩ : syracuseStep 304895 = 457343) B457343
theorem B1288007 : Blo 199806 1288007 := bstep (se 1 (by rfl) ⟨966005, by rfl⟩ : syracuseStep 1288007 = 1932011) B1932011
theorem B305255 : Blo 199806 305255 := bstep (se 1 (by rfl) ⟨228941, by rfl⟩ : syracuseStep 305255 = 457883) B457883
theorem B338107 : Blo 199806 338107 := bstep (se 1 (by rfl) ⟨253580, by rfl⟩ : syracuseStep 338107 = 507161) B507161
theorem B764113 : Blo 199806 764113 := bstep (se 2 (by rfl) ⟨286542, by rfl⟩ : syracuseStep 764113 = 573085) B573085
theorem B339943 : Blo 199806 339943 := bstep (se 1 (by rfl) ⟨254957, by rfl⟩ : syracuseStep 339943 = 509915) B509915
theorem B307817 : Blo 199806 307817 := bstep (se 2 (by rfl) ⟨115431, by rfl⟩ : syracuseStep 307817 = 230863) B230863
theorem B340699 : Blo 199806 340699 := bstep (se 1 (by rfl) ⟨255524, by rfl⟩ : syracuseStep 340699 = 511049) B511049
theorem B570215 : Blo 199806 570215 := bstep (se 1 (by rfl) ⟨427661, by rfl⟩ : syracuseStep 570215 = 855323) B855323
theorem B1521179 : Blo 199806 1521179 := bstep (se 1 (by rfl) ⟨1140884, by rfl⟩ : syracuseStep 1521179 = 2281769) B2281769
theorem B2569967 : Blo 199806 2569967 := bstep (se 1 (by rfl) ⟨1927475, by rfl⟩ : syracuseStep 2569967 = 3854951) B3854951
theorem B342137 : Blo 199806 342137 := bstep (se 2 (by rfl) ⟨128301, by rfl⟩ : syracuseStep 342137 = 256603) B256603
theorem B342191 : Blo 199806 342191 := bstep (se 1 (by rfl) ⟨256643, by rfl⟩ : syracuseStep 342191 = 513287) B513287
theorem B1456451 : Blo 199806 1456451 := bstep (se 1 (by rfl) ⟨1092338, by rfl⟩ : syracuseStep 1456451 = 2184677) B2184677
theorem B768487 : Blo 199806 768487 := bstep (se 1 (by rfl) ⟨576365, by rfl⟩ : syracuseStep 768487 = 1152731) B1152731
theorem B6569201 : Blo 199806 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B343399 : Blo 199806 343399 := bstep (se 1 (by rfl) ⟨257549, by rfl⟩ : syracuseStep 343399 = 515099) B515099
theorem B343919 : Blo 199806 343919 := bstep (se 1 (by rfl) ⟨257939, by rfl⟩ : syracuseStep 343919 = 515879) B515879
theorem B966815 : Blo 199806 966815 := bstep (se 1 (by rfl) ⟨725111, by rfl⟩ : syracuseStep 966815 = 1450223) B1450223
theorem B5850467 : Blo 199806 5850467 := bstep (se 1 (by rfl) ⟨4387850, by rfl⟩ : syracuseStep 5850467 = 8775701) B8775701
theorem B869879 : Blo 199806 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B5293811 : Blo 199806 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B2181431 : Blo 199806 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B2705993 : Blo 199806 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B379559 : Blo 199806 379559 := bstep (se 1 (by rfl) ⟨284669, by rfl⟩ : syracuseStep 379559 = 569339) B569339
theorem B642107 : Blo 199806 642107 := bstep (se 1 (by rfl) ⟨481580, by rfl⟩ : syracuseStep 642107 = 963161) B963161
theorem B674945 : Blo 199806 674945 := bstep (se 2 (by rfl) ⟨253104, by rfl⟩ : syracuseStep 674945 = 506209) B506209
theorem B216479 : Blo 199806 216479 := bstep (se 1 (by rfl) ⟨162359, by rfl⟩ : syracuseStep 216479 = 324719) B324719
theorem B511535 : Blo 199806 511535 := bstep (se 1 (by rfl) ⟨383651, by rfl⟩ : syracuseStep 511535 = 767303) B767303
theorem B970505 : Blo 199806 970505 := bstep (se 2 (by rfl) ⟨363939, by rfl⟩ : syracuseStep 970505 = 727879) B727879
theorem B675647 : Blo 199806 675647 := bstep (se 1 (by rfl) ⟨506735, by rfl⟩ : syracuseStep 675647 = 1013471) B1013471
theorem B675755 : Blo 199806 675755 := bstep (se 1 (by rfl) ⟨506816, by rfl⟩ : syracuseStep 675755 = 1013633) B1013633
theorem B511991 : Blo 199806 511991 := bstep (se 1 (by rfl) ⟨383993, by rfl⟩ : syracuseStep 511991 = 767987) B767987
theorem B1724449 : Blo 199806 1724449 := bstep (se 2 (by rfl) ⟨646668, by rfl⟩ : syracuseStep 1724449 = 1293337) B1293337
theorem B1167817 : Blo 199806 1167817 := bstep (se 2 (by rfl) ⟨437931, by rfl⟩ : syracuseStep 1167817 = 875863) B875863
theorem B381419 : Blo 199806 381419 := bstep (se 1 (by rfl) ⟨286064, by rfl⟩ : syracuseStep 381419 = 572129) B572129
theorem B2283227 : Blo 199806 2283227 := bstep (se 1 (by rfl) ⟨1712420, by rfl⟩ : syracuseStep 2283227 = 3424841) B3424841
theorem B677753 : Blo 199806 677753 := bstep (se 2 (by rfl) ⟨254157, by rfl⟩ : syracuseStep 677753 = 508315) B508315
theorem B285871 : Blo 199806 285871 := bstep (se 1 (by rfl) ⟨214403, by rfl⟩ : syracuseStep 285871 = 428807) B428807
theorem B449747 : Blo 199806 449747 := bstep (se 1 (by rfl) ⟨337310, by rfl⟩ : syracuseStep 449747 = 674621) B674621
theorem B385307 : Blo 199806 385307 := bstep (se 1 (by rfl) ⟨288980, by rfl⟩ : syracuseStep 385307 = 577961) B577961
theorem B1728823 : Blo 199806 1728823 := bstep (se 1 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 1728823 = 2593235) B2593235
theorem B385535 : Blo 199806 385535 := bstep (se 1 (by rfl) ⟨289151, by rfl⟩ : syracuseStep 385535 = 578303) B578303
theorem B451259 : Blo 199806 451259 := bstep (se 1 (by rfl) ⟨338444, by rfl⟩ : syracuseStep 451259 = 676889) B676889
theorem B648233 : Blo 199806 648233 := bstep (se 2 (by rfl) ⟨243087, by rfl⟩ : syracuseStep 648233 = 486175) B486175
theorem B451655 : Blo 199806 451655 := bstep (se 1 (by rfl) ⟨338741, by rfl⟩ : syracuseStep 451655 = 677483) B677483
theorem B452519 : Blo 199806 452519 := bstep (se 1 (by rfl) ⟨339389, by rfl⟩ : syracuseStep 452519 = 678779) B678779
theorem B649129 : Blo 199806 649129 := bstep (se 2 (by rfl) ⟨243423, by rfl⟩ : syracuseStep 649129 = 486847) B486847
theorem B1042415 : Blo 199806 1042415 := bstep (se 1 (by rfl) ⟨781811, by rfl⟩ : syracuseStep 1042415 = 1563623) B1563623
theorem B1730807 : Blo 199806 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B111602609 : Blo 199806 111602609 := bstep (se 2 (by rfl) ⟨41850978, by rfl⟩ : syracuseStep 111602609 = 83701957) B83701957
theorem B224815 : Blo 199806 224815 := bstep (se 1 (by rfl) ⟨168611, by rfl⟩ : syracuseStep 224815 = 337223) B337223
theorem B454247 : Blo 199806 454247 := bstep (se 1 (by rfl) ⟨340685, by rfl⟩ : syracuseStep 454247 = 681371) B681371
theorem B651719 : Blo 199806 651719 := bstep (se 1 (by rfl) ⟨488789, by rfl⟩ : syracuseStep 651719 = 977579) B977579
theorem B914107 : Blo 199806 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B685367 : Blo 199806 685367 := bstep (se 1 (by rfl) ⟨514025, by rfl⟩ : syracuseStep 685367 = 1028051) B1028051
theorem B1930553 : Blo 199806 1930553 := bstep (se 2 (by rfl) ⟨723957, by rfl⟩ : syracuseStep 1930553 = 1447915) B1447915
theorem B2454893 : Blo 199806 2454893 := bstep (se 3 (by rfl) ⟨460292, by rfl⟩ : syracuseStep 2454893 = 920585) B920585
theorem B1537703 : Blo 199806 1537703 := bstep (se 1 (by rfl) ⟨1153277, by rfl⟩ : syracuseStep 1537703 = 2306555) B2306555
theorem B12449771 : Blo 199806 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B981371 : Blo 199806 981371 := bstep (se 1 (by rfl) ⟨736028, by rfl⟩ : syracuseStep 981371 = 1472057) B1472057
theorem B228199 : Blo 199806 228199 := bstep (se 1 (by rfl) ⟨171149, by rfl⟩ : syracuseStep 228199 = 342299) B342299
theorem B457775 : Blo 199806 457775 := bstep (se 1 (by rfl) ⟨343331, by rfl⟩ : syracuseStep 457775 = 686663) B686663
theorem B457811 : Blo 199806 457811 := bstep (se 1 (by rfl) ⟨343358, by rfl⟩ : syracuseStep 457811 = 686717) B686717
theorem B457919 : Blo 199806 457919 := bstep (se 1 (by rfl) ⟨343439, by rfl⟩ : syracuseStep 457919 = 686879) B686879
theorem B687689 : Blo 199806 687689 := bstep (se 2 (by rfl) ⟨257883, by rfl⟩ : syracuseStep 687689 = 515767) B515767
theorem B2490209 : Blo 199806 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B3900311 : Blo 199806 3900311 := bstep (se 1 (by rfl) ⟨2925233, by rfl⟩ : syracuseStep 3900311 = 5850467) B5850467
theorem B1803995 : Blo 199806 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B1018817 : Blo 199806 1018817 := bstep (se 2 (by rfl) ⟨382056, by rfl⟩ : syracuseStep 1018817 = 764113) B764113
theorem B199839 : Blo 199806 199839 := bstep (se 1 (by rfl) ⟨149879, by rfl⟩ : syracuseStep 199839 = 299759) B299759
theorem B199963 : Blo 199806 199963 := bstep (se 1 (by rfl) ⟨149972, by rfl⟩ : syracuseStep 199963 = 299945) B299945
theorem B199999 : Blo 199806 199999 := bstep (se 1 (by rfl) ⟨149999, by rfl⟩ : syracuseStep 199999 = 299999) B299999
theorem B200383 : Blo 199806 200383 := bstep (se 1 (by rfl) ⟨150287, by rfl⟩ : syracuseStep 200383 = 300575) B300575
theorem B1446011 : Blo 199806 1446011 := bstep (se 1 (by rfl) ⟨1084508, by rfl⟩ : syracuseStep 1446011 = 2169017) B2169017
theorem B200959 : Blo 199806 200959 := bstep (se 1 (by rfl) ⟨150719, by rfl⟩ : syracuseStep 200959 = 301439) B301439
theorem B201151 : Blo 199806 201151 := bstep (se 1 (by rfl) ⟨150863, by rfl⟩ : syracuseStep 201151 = 301727) B301727
theorem B201183 : Blo 199806 201183 := bstep (se 1 (by rfl) ⟨150887, by rfl⟩ : syracuseStep 201183 = 301775) B301775
theorem B201199 : Blo 199806 201199 := bstep (se 1 (by rfl) ⟨150899, by rfl⟩ : syracuseStep 201199 = 301799) B301799
theorem B201215 : Blo 199806 201215 := bstep (se 1 (by rfl) ⟨150911, by rfl⟩ : syracuseStep 201215 = 301823) B301823
theorem B791167 : Blo 199806 791167 := bstep (se 1 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 791167 = 1186751) B1186751
theorem B299753 : Blo 199806 299753 := bstep (se 2 (by rfl) ⟨112407, by rfl⟩ : syracuseStep 299753 = 224815) B224815
theorem B201455 : Blo 199806 201455 := bstep (se 1 (by rfl) ⟨151091, by rfl⟩ : syracuseStep 201455 = 302183) B302183
theorem B299831 : Blo 199806 299831 := bstep (se 1 (by rfl) ⟨224873, by rfl⟩ : syracuseStep 299831 = 449747) B449747
theorem B201543 : Blo 199806 201543 := bstep (se 1 (by rfl) ⟨151157, by rfl⟩ : syracuseStep 201543 = 302315) B302315
theorem B202011 : Blo 199806 202011 := bstep (se 1 (by rfl) ⟨151508, by rfl⟩ : syracuseStep 202011 = 303017) B303017
theorem B2299265 : Blo 199806 2299265 := bstep (se 2 (by rfl) ⟨862224, by rfl⟩ : syracuseStep 2299265 = 1724449) B1724449
theorem B300839 : Blo 199806 300839 := bstep (se 1 (by rfl) ⟨225629, by rfl⟩ : syracuseStep 300839 = 451259) B451259
theorem B202607 : Blo 199806 202607 := bstep (se 1 (by rfl) ⟨151955, by rfl⟩ : syracuseStep 202607 = 303911) B303911
theorem B432155 : Blo 199806 432155 := bstep (se 1 (by rfl) ⟨324116, by rfl⟩ : syracuseStep 432155 = 648233) B648233
theorem B301103 : Blo 199806 301103 := bstep (se 1 (by rfl) ⟨225827, by rfl⟩ : syracuseStep 301103 = 451655) B451655
theorem B202919 : Blo 199806 202919 := bstep (se 1 (by rfl) ⟨152189, by rfl⟩ : syracuseStep 202919 = 304379) B304379
theorem B202975 : Blo 199806 202975 := bstep (se 1 (by rfl) ⟨152231, by rfl⟩ : syracuseStep 202975 = 304463) B304463
theorem B1218809 : Blo 199806 1218809 := bstep (se 2 (by rfl) ⟨457053, by rfl⟩ : syracuseStep 1218809 = 914107) B914107
theorem B203231 : Blo 199806 203231 := bstep (se 1 (by rfl) ⟨152423, by rfl⟩ : syracuseStep 203231 = 304847) B304847
theorem B203263 : Blo 199806 203263 := bstep (se 1 (by rfl) ⟨152447, by rfl⟩ : syracuseStep 203263 = 304895) B304895
theorem B858671 : Blo 199806 858671 := bstep (se 1 (by rfl) ⟨644003, by rfl⟩ : syracuseStep 858671 = 1288007) B1288007
theorem B301679 : Blo 199806 301679 := bstep (se 1 (by rfl) ⟨226259, by rfl⟩ : syracuseStep 301679 = 452519) B452519
theorem B694943 : Blo 199806 694943 := bstep (se 1 (by rfl) ⟨521207, by rfl⟩ : syracuseStep 694943 = 1042415) B1042415
theorem B203503 : Blo 199806 203503 := bstep (se 1 (by rfl) ⟨152627, by rfl⟩ : syracuseStep 203503 = 305255) B305255
theorem B1153871 : Blo 199806 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B302831 : Blo 199806 302831 := bstep (se 1 (by rfl) ⟨227123, by rfl⟩ : syracuseStep 302831 = 454247) B454247
theorem B1712285 : Blo 199806 1712285 := bstep (se 3 (by rfl) ⟨321053, by rfl⟩ : syracuseStep 1712285 = 642107) B642107
theorem B434479 : Blo 199806 434479 := bstep (se 1 (by rfl) ⟨325859, by rfl⟩ : syracuseStep 434479 = 651719) B651719
theorem B205211 : Blo 199806 205211 := bstep (se 1 (by rfl) ⟨153908, by rfl⟩ : syracuseStep 205211 = 307817) B307817
theorem B1024649 : Blo 199806 1024649 := bstep (se 2 (by rfl) ⟨384243, by rfl⟩ : syracuseStep 1024649 = 768487) B768487
theorem B1287035 : Blo 199806 1287035 := bstep (se 1 (by rfl) ⟨965276, by rfl⟩ : syracuseStep 1287035 = 1930553) B1930553
theorem B1025135 : Blo 199806 1025135 := bstep (se 1 (by rfl) ⟨768851, by rfl⟩ : syracuseStep 1025135 = 1537703) B1537703
theorem B304265 : Blo 199806 304265 := bstep (se 2 (by rfl) ⟨114099, by rfl⟩ : syracuseStep 304265 = 228199) B228199
theorem B1713311 : Blo 199806 1713311 := bstep (se 1 (by rfl) ⟨1284983, by rfl⟩ : syracuseStep 1713311 = 2569967) B2569967
theorem B8299847 : Blo 199806 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B305183 : Blo 199806 305183 := bstep (se 1 (by rfl) ⟨228887, by rfl⟩ : syracuseStep 305183 = 457775) B457775
theorem B305207 : Blo 199806 305207 := bstep (se 1 (by rfl) ⟨228905, by rfl⟩ : syracuseStep 305207 = 457811) B457811
theorem B305279 : Blo 199806 305279 := bstep (se 1 (by rfl) ⟨228959, by rfl⟩ : syracuseStep 305279 = 457919) B457919
theorem B2305097 : Blo 199806 2305097 := bstep (se 2 (by rfl) ⟨864411, by rfl⟩ : syracuseStep 2305097 = 1728823) B1728823
theorem B1486673 : Blo 199806 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B1159271 : Blo 199806 1159271 := bstep (se 1 (by rfl) ⟨869453, by rfl⟩ : syracuseStep 1159271 = 1738907) B1738907
theorem B962759 : Blo 199806 962759 := bstep (se 1 (by rfl) ⟨722069, by rfl⟩ : syracuseStep 962759 = 1444139) B1444139
theorem B1454287 : Blo 199806 1454287 := bstep (se 1 (by rfl) ⟨1090715, by rfl⟩ : syracuseStep 1454287 = 2181431) B2181431
theorem B341023 : Blo 199806 341023 := bstep (se 1 (by rfl) ⟨255767, by rfl⟩ : syracuseStep 341023 = 511535) B511535
theorem B865505 : Blo 199806 865505 := bstep (se 2 (by rfl) ⟨324564, by rfl⟩ : syracuseStep 865505 = 649129) B649129
theorem B341327 : Blo 199806 341327 := bstep (se 1 (by rfl) ⟨255995, by rfl⟩ : syracuseStep 341327 = 511991) B511991
theorem B243919 : Blo 199806 243919 := bstep (se 1 (by rfl) ⟨182939, by rfl⟩ : syracuseStep 243919 = 365879) B365879
theorem B1522151 : Blo 199806 1522151 := bstep (se 1 (by rfl) ⟨1141613, by rfl⟩ : syracuseStep 1522151 = 2283227) B2283227
theorem B376987 : Blo 199806 376987 := bstep (se 1 (by rfl) ⟨282740, by rfl⟩ : syracuseStep 376987 = 565481) B565481
theorem B1557089 : Blo 199806 1557089 := bstep (se 2 (by rfl) ⟨583908, by rfl⟩ : syracuseStep 1557089 = 1167817) B1167817
theorem B6341777 : Blo 199806 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B74401739 : Blo 199806 74401739 := bstep (se 1 (by rfl) ⟨55801304, by rfl⟩ : syracuseStep 74401739 = 111602609) B111602609
theorem B969889 : Blo 199806 969889 := bstep (se 2 (by rfl) ⟨363708, by rfl⟩ : syracuseStep 969889 = 727417) B727417
theorem B380143 : Blo 199806 380143 := bstep (se 1 (by rfl) ⟨285107, by rfl⟩ : syracuseStep 380143 = 570215) B570215
theorem B577277 : Blo 199806 577277 := bstep (se 3 (by rfl) ⟨108239, by rfl⟩ : syracuseStep 577277 = 216479) B216479
theorem B970967 : Blo 199806 970967 := bstep (se 1 (by rfl) ⟨728225, by rfl⟩ : syracuseStep 970967 = 1456451) B1456451
theorem B381161 : Blo 199806 381161 := bstep (se 2 (by rfl) ⟨142935, by rfl⟩ : syracuseStep 381161 = 285871) B285871
theorem B4379467 : Blo 199806 4379467 := bstep (se 1 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 4379467 = 6569201) B6569201
theorem B1660139 : Blo 199806 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B644543 : Blo 199806 644543 := bstep (se 1 (by rfl) ⟨483407, by rfl⟩ : syracuseStep 644543 = 966815) B966815
theorem B677375 : Blo 199806 677375 := bstep (se 1 (by rfl) ⟨508031, by rfl⟩ : syracuseStep 677375 = 1016063) B1016063
theorem B3529207 : Blo 199806 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B253039 : Blo 199806 253039 := bstep (se 1 (by rfl) ⟨189779, by rfl⟩ : syracuseStep 253039 = 379559) B379559
theorem B449963 : Blo 199806 449963 := bstep (se 1 (by rfl) ⟨337472, by rfl⟩ : syracuseStep 449963 = 674945) B674945
theorem B679535 : Blo 199806 679535 := bstep (se 1 (by rfl) ⟨509651, by rfl⟩ : syracuseStep 679535 = 1019303) B1019303
theorem B647003 : Blo 199806 647003 := bstep (se 1 (by rfl) ⟨485252, by rfl⟩ : syracuseStep 647003 = 970505) B970505
theorem B450431 : Blo 199806 450431 := bstep (se 1 (by rfl) ⟨337823, by rfl⟩ : syracuseStep 450431 = 675647) B675647
theorem B450503 : Blo 199806 450503 := bstep (se 1 (by rfl) ⟨337877, by rfl⟩ : syracuseStep 450503 = 675755) B675755
theorem B450809 : Blo 199806 450809 := bstep (se 2 (by rfl) ⟨169053, by rfl⟩ : syracuseStep 450809 = 338107) B338107
theorem B254279 : Blo 199806 254279 := bstep (se 1 (by rfl) ⟨190709, by rfl⟩ : syracuseStep 254279 = 381419) B381419
theorem B1139291 : Blo 199806 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B680831 : Blo 199806 680831 := bstep (se 1 (by rfl) ⟨510623, by rfl⟩ : syracuseStep 680831 = 1021247) B1021247
theorem B451835 : Blo 199806 451835 := bstep (se 1 (by rfl) ⟨338876, by rfl⟩ : syracuseStep 451835 = 677753) B677753
theorem B2319677 : Blo 199806 2319677 := bstep (se 3 (by rfl) ⟨434939, by rfl⟩ : syracuseStep 2319677 = 869879) B869879
theorem B1140065 : Blo 199806 1140065 := bstep (se 2 (by rfl) ⟨427524, by rfl⟩ : syracuseStep 1140065 = 855049) B855049
theorem B682235 : Blo 199806 682235 := bstep (se 1 (by rfl) ⟨511676, by rfl⟩ : syracuseStep 682235 = 1023353) B1023353
theorem B977309 : Blo 199806 977309 := bstep (se 3 (by rfl) ⟨183245, by rfl⟩ : syracuseStep 977309 = 366491) B366491
theorem B2583089 : Blo 199806 2583089 := bstep (se 2 (by rfl) ⟨968658, by rfl⟩ : syracuseStep 2583089 = 1937317) B1937317
theorem B453257 : Blo 199806 453257 := bstep (se 2 (by rfl) ⟨169971, by rfl⟩ : syracuseStep 453257 = 339943) B339943
theorem B256871 : Blo 199806 256871 := bstep (se 1 (by rfl) ⟨192653, by rfl⟩ : syracuseStep 256871 = 385307) B385307
theorem B257023 : Blo 199806 257023 := bstep (se 1 (by rfl) ⟨192767, by rfl⟩ : syracuseStep 257023 = 385535) B385535
theorem B289823 : Blo 199806 289823 := bstep (se 1 (by rfl) ⟨217367, by rfl⟩ : syracuseStep 289823 = 434735) B434735
theorem B454265 : Blo 199806 454265 := bstep (se 2 (by rfl) ⟨170349, by rfl⟩ : syracuseStep 454265 = 340699) B340699
theorem B1011527 : Blo 199806 1011527 := bstep (se 1 (by rfl) ⟨758645, by rfl⟩ : syracuseStep 1011527 = 1517291) B1517291
theorem B456911 : Blo 199806 456911 := bstep (se 1 (by rfl) ⟨342683, by rfl⟩ : syracuseStep 456911 = 685367) B685367
theorem B1636595 : Blo 199806 1636595 := bstep (se 1 (by rfl) ⟨1227446, by rfl⟩ : syracuseStep 1636595 = 2454893) B2454893
theorem B1014119 : Blo 199806 1014119 := bstep (se 1 (by rfl) ⟨760589, by rfl⟩ : syracuseStep 1014119 = 1521179) B1521179
theorem B228091 : Blo 199806 228091 := bstep (se 1 (by rfl) ⟨171068, by rfl⟩ : syracuseStep 228091 = 342137) B342137
theorem B228127 : Blo 199806 228127 := bstep (se 1 (by rfl) ⟨171095, by rfl⟩ : syracuseStep 228127 = 342191) B342191
theorem B654247 : Blo 199806 654247 := bstep (se 1 (by rfl) ⟨490685, by rfl⟩ : syracuseStep 654247 = 981371) B981371
theorem B457865 : Blo 199806 457865 := bstep (se 2 (by rfl) ⟨171699, by rfl⟩ : syracuseStep 457865 = 343399) B343399
theorem B1014929 : Blo 199806 1014929 := bstep (se 2 (by rfl) ⟨380598, by rfl⟩ : syracuseStep 1014929 = 761197) B761197
theorem B458459 : Blo 199806 458459 := bstep (se 1 (by rfl) ⟨343844, by rfl⟩ : syracuseStep 458459 = 687689) B687689
theorem B229279 : Blo 199806 229279 := bstep (se 1 (by rfl) ⟨171959, by rfl⟩ : syracuseStep 229279 = 343919) B343919
theorem B4227851 : Blo 199806 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B199835 : Blo 199806 199835 := bstep (se 1 (by rfl) ⟨149876, by rfl⟩ : syracuseStep 199835 = 299753) B299753
theorem B199887 : Blo 199806 199887 := bstep (se 1 (by rfl) ⟨149915, by rfl⟩ : syracuseStep 199887 = 299831) B299831
theorem B429695 : Blo 199806 429695 := bstep (se 1 (by rfl) ⟨322271, by rfl⟩ : syracuseStep 429695 = 644543) B644543
theorem B200559 : Blo 199806 200559 := bstep (se 1 (by rfl) ⟨150419, by rfl⟩ : syracuseStep 200559 = 300839) B300839
theorem B200735 : Blo 199806 200735 := bstep (se 1 (by rfl) ⟨150551, by rfl⟩ : syracuseStep 200735 = 301103) B301103
theorem B201119 : Blo 199806 201119 := bstep (se 1 (by rfl) ⟨150839, by rfl⟩ : syracuseStep 201119 = 301679) B301679
theorem B463295 : Blo 199806 463295 := bstep (se 1 (by rfl) ⟨347471, by rfl⟩ : syracuseStep 463295 = 694943) B694943
theorem B299975 : Blo 199806 299975 := bstep (se 1 (by rfl) ⟨224981, by rfl⟩ : syracuseStep 299975 = 449963) B449963
theorem B201887 : Blo 199806 201887 := bstep (se 1 (by rfl) ⟨151415, by rfl⟩ : syracuseStep 201887 = 302831) B302831
theorem B431335 : Blo 199806 431335 := bstep (se 1 (by rfl) ⟨323501, by rfl⟩ : syracuseStep 431335 = 647003) B647003
theorem B300287 : Blo 199806 300287 := bstep (se 1 (by rfl) ⟨225215, by rfl⟩ : syracuseStep 300287 = 450431) B450431
theorem B300335 : Blo 199806 300335 := bstep (se 1 (by rfl) ⟨225251, by rfl⟩ : syracuseStep 300335 = 450503) B450503
theorem B1152413 : Blo 199806 1152413 := bstep (se 3 (by rfl) ⟨216077, by rfl⟩ : syracuseStep 1152413 = 432155) B432155
theorem B300539 : Blo 199806 300539 := bstep (se 1 (by rfl) ⟨225404, by rfl⟩ : syracuseStep 300539 = 450809) B450809
theorem B1939049 : Blo 199806 1939049 := bstep (se 2 (by rfl) ⟨727143, by rfl⟩ : syracuseStep 1939049 = 1454287) B1454287
theorem B759527 : Blo 199806 759527 := bstep (se 1 (by rfl) ⟨569645, by rfl⟩ : syracuseStep 759527 = 1139291) B1139291
theorem B858023 : Blo 199806 858023 := bstep (se 1 (by rfl) ⟨643517, by rfl⟩ : syracuseStep 858023 = 1287035) B1287035
theorem B202843 : Blo 199806 202843 := bstep (se 1 (by rfl) ⟨152132, by rfl⟩ : syracuseStep 202843 = 304265) B304265
theorem B301223 : Blo 199806 301223 := bstep (se 1 (by rfl) ⟨225917, by rfl⟩ : syracuseStep 301223 = 451835) B451835
theorem B1054889 : Blo 199806 1054889 := bstep (se 2 (by rfl) ⟨395583, by rfl⟩ : syracuseStep 1054889 = 791167) B791167
theorem B1546451 : Blo 199806 1546451 := bstep (se 1 (by rfl) ⟨1159838, by rfl⟩ : syracuseStep 1546451 = 2319677) B2319677
theorem B760043 : Blo 199806 760043 := bstep (se 1 (by rfl) ⟨570032, by rfl⟩ : syracuseStep 760043 = 1140065) B1140065
theorem B5839289 : Blo 199806 5839289 := bstep (se 2 (by rfl) ⟨2189733, by rfl⟩ : syracuseStep 5839289 = 4379467) B4379467
theorem B203455 : Blo 199806 203455 := bstep (se 1 (by rfl) ⟨152591, by rfl⟩ : syracuseStep 203455 = 305183) B305183
theorem B203471 : Blo 199806 203471 := bstep (se 1 (by rfl) ⟨152603, by rfl⟩ : syracuseStep 203471 = 305207) B305207
theorem B203519 : Blo 199806 203519 := bstep (se 1 (by rfl) ⟨152639, by rfl⟩ : syracuseStep 203519 = 305279) B305279
theorem B302171 : Blo 199806 302171 := bstep (se 1 (by rfl) ⟨226628, by rfl⟩ : syracuseStep 302171 = 453257) B453257
theorem B302843 : Blo 199806 302843 := bstep (se 1 (by rfl) ⟨227132, by rfl⟩ : syracuseStep 302843 = 454265) B454265
theorem B991115 : Blo 199806 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B304121 : Blo 199806 304121 := bstep (se 2 (by rfl) ⟨114045, by rfl⟩ : syracuseStep 304121 = 228091) B228091
theorem B304169 : Blo 199806 304169 := bstep (se 2 (by rfl) ⟨114063, by rfl⟩ : syracuseStep 304169 = 228127) B228127
theorem B304607 : Blo 199806 304607 := bstep (se 1 (by rfl) ⟨228455, by rfl⟩ : syracuseStep 304607 = 456911) B456911
theorem B337385 : Blo 199806 337385 := bstep (se 2 (by rfl) ⟨126519, by rfl⟩ : syracuseStep 337385 = 253039) B253039
theorem B1091063 : Blo 199806 1091063 := bstep (se 1 (by rfl) ⟨818297, by rfl⟩ : syracuseStep 1091063 = 1636595) B1636595
theorem B305243 : Blo 199806 305243 := bstep (se 1 (by rfl) ⟨228932, by rfl⟩ : syracuseStep 305243 = 457865) B457865
theorem B305639 : Blo 199806 305639 := bstep (se 1 (by rfl) ⟨229229, by rfl⟩ : syracuseStep 305639 = 458459) B458459
theorem B305705 : Blo 199806 305705 := bstep (se 2 (by rfl) ⟨114639, by rfl⟩ : syracuseStep 305705 = 229279) B229279
theorem B502649 : Blo 199806 502649 := bstep (se 2 (by rfl) ⟨188493, by rfl⟩ : syracuseStep 502649 = 376987) B376987
theorem B2600207 : Blo 199806 2600207 := bstep (se 1 (by rfl) ⟨1950155, by rfl⟩ : syracuseStep 2600207 = 3900311) B3900311
theorem B964007 : Blo 199806 964007 := bstep (se 1 (by rfl) ⟨723005, by rfl⟩ : syracuseStep 964007 = 1446011) B1446011
theorem B2308013 : Blo 199806 2308013 := bstep (se 3 (by rfl) ⟨432752, by rfl⟩ : syracuseStep 2308013 = 865505) B865505
theorem B342697 : Blo 199806 342697 := bstep (se 2 (by rfl) ⟨128511, by rfl⟩ : syracuseStep 342697 = 257023) B257023
theorem B1293185 : Blo 199806 1293185 := bstep (se 2 (by rfl) ⟨484944, by rfl⟩ : syracuseStep 1293185 = 969889) B969889
theorem B506857 : Blo 199806 506857 := bstep (se 2 (by rfl) ⟨190071, by rfl⟩ : syracuseStep 506857 = 380143) B380143
theorem B572447 : Blo 199806 572447 := bstep (se 1 (by rfl) ⟨429335, by rfl⟩ : syracuseStep 572447 = 858671) B858671
theorem B769247 : Blo 199806 769247 := bstep (se 1 (by rfl) ⟨576935, by rfl⟩ : syracuseStep 769247 = 1153871) B1153871
theorem B1722059 : Blo 199806 1722059 := bstep (se 1 (by rfl) ⟨1291544, by rfl⟩ : syracuseStep 1722059 = 2583089) B2583089
theorem B674351 : Blo 199806 674351 := bstep (se 1 (by rfl) ⟨505763, by rfl⟩ : syracuseStep 674351 = 1011527) B1011527
theorem B772847 : Blo 199806 772847 := bstep (se 1 (by rfl) ⟨579635, by rfl⟩ : syracuseStep 772847 = 1159271) B1159271
theorem B772861 : Blo 199806 772861 := bstep (se 3 (by rfl) ⟨144911, by rfl⟩ : syracuseStep 772861 = 289823) B289823
theorem B641839 : Blo 199806 641839 := bstep (se 1 (by rfl) ⟨481379, by rfl⟩ : syracuseStep 641839 = 962759) B962759
theorem B4705609 : Blo 199806 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B872329 : Blo 199806 872329 := bstep (se 2 (by rfl) ⟨327123, by rfl⟩ : syracuseStep 872329 = 654247) B654247
theorem B676079 : Blo 199806 676079 := bstep (se 1 (by rfl) ⟨507059, by rfl⟩ : syracuseStep 676079 = 1014119) B1014119
theorem B676619 : Blo 199806 676619 := bstep (se 1 (by rfl) ⟨507464, by rfl⟩ : syracuseStep 676619 = 1014929) B1014929
theorem B579305 : Blo 199806 579305 := bstep (se 2 (by rfl) ⟨217239, by rfl⟩ : syracuseStep 579305 = 434479) B434479
theorem B1038059 : Blo 199806 1038059 := bstep (se 1 (by rfl) ⟨778544, by rfl⟩ : syracuseStep 1038059 = 1557089) B1557089
theorem B678077 : Blo 199806 678077 := bstep (se 3 (by rfl) ⟨127139, by rfl⟩ : syracuseStep 678077 = 254279) B254279
theorem B547229 : Blo 199806 547229 := bstep (se 3 (by rfl) ⟨102605, by rfl⟩ : syracuseStep 547229 = 205211) B205211
theorem B1202663 : Blo 199806 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B49601159 : Blo 199806 49601159 := bstep (se 1 (by rfl) ⟨37200869, by rfl⟩ : syracuseStep 49601159 = 74401739) B74401739
theorem B679211 : Blo 199806 679211 := bstep (se 1 (by rfl) ⟨509408, by rfl⟩ : syracuseStep 679211 = 1018817) B1018817
theorem B384851 : Blo 199806 384851 := bstep (se 1 (by rfl) ⟨288638, by rfl⟩ : syracuseStep 384851 = 577277) B577277
theorem B647311 : Blo 199806 647311 := bstep (se 1 (by rfl) ⟨485483, by rfl⟩ : syracuseStep 647311 = 970967) B970967
theorem B254107 : Blo 199806 254107 := bstep (se 1 (by rfl) ⟨190580, by rfl⟩ : syracuseStep 254107 = 381161) B381161
theorem B1106759 : Blo 199806 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B1532843 : Blo 199806 1532843 := bstep (se 1 (by rfl) ⟨1149632, by rfl⟩ : syracuseStep 1532843 = 2299265) B2299265
theorem B451583 : Blo 199806 451583 := bstep (se 1 (by rfl) ⟨338687, by rfl⟩ : syracuseStep 451583 = 677375) B677375
theorem B812539 : Blo 199806 812539 := bstep (se 1 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 812539 = 1218809) B1218809
theorem B453023 : Blo 199806 453023 := bstep (se 1 (by rfl) ⟨339767, by rfl⟩ : syracuseStep 453023 = 679535) B679535
theorem B1141523 : Blo 199806 1141523 := bstep (se 1 (by rfl) ⟨856142, by rfl⟩ : syracuseStep 1141523 = 1712285) B1712285
theorem B683099 : Blo 199806 683099 := bstep (se 1 (by rfl) ⟨512324, by rfl⟩ : syracuseStep 683099 = 1024649) B1024649
theorem B453887 : Blo 199806 453887 := bstep (se 1 (by rfl) ⟨340415, by rfl⟩ : syracuseStep 453887 = 680831) B680831
theorem B683423 : Blo 199806 683423 := bstep (se 1 (by rfl) ⟨512567, by rfl⟩ : syracuseStep 683423 = 1025135) B1025135
theorem B1142207 : Blo 199806 1142207 := bstep (se 1 (by rfl) ⟨856655, by rfl⟩ : syracuseStep 1142207 = 1713311) B1713311
theorem B5533231 : Blo 199806 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B454697 : Blo 199806 454697 := bstep (se 2 (by rfl) ⟨170511, by rfl⟩ : syracuseStep 454697 = 341023) B341023
theorem B454823 : Blo 199806 454823 := bstep (se 1 (by rfl) ⟨341117, by rfl⟩ : syracuseStep 454823 = 682235) B682235
theorem B651539 : Blo 199806 651539 := bstep (se 1 (by rfl) ⟨488654, by rfl⟩ : syracuseStep 651539 = 977309) B977309
theorem B1536731 : Blo 199806 1536731 := bstep (se 1 (by rfl) ⟨1152548, by rfl⟩ : syracuseStep 1536731 = 2305097) B2305097
theorem B684989 : Blo 199806 684989 := bstep (se 3 (by rfl) ⟨128435, by rfl⟩ : syracuseStep 684989 = 256871) B256871
theorem B325225 : Blo 199806 325225 := bstep (se 2 (by rfl) ⟨121959, by rfl⟩ : syracuseStep 325225 = 243919) B243919
theorem B227551 : Blo 199806 227551 := bstep (se 1 (by rfl) ⟨170663, by rfl⟩ : syracuseStep 227551 = 341327) B341327
theorem B1014767 : Blo 199806 1014767 := bstep (se 1 (by rfl) ⟨761075, by rfl⟩ : syracuseStep 1014767 = 1522151) B1522151
theorem B2818567 : Blo 199806 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B1148039 : Blo 199806 1148039 := bstep (se 1 (by rfl) ⟨861029, by rfl⟩ : syracuseStep 1148039 = 1722059) B1722059
theorem B1083385 : Blo 199806 1083385 := bstep (se 2 (by rfl) ⟨406269, by rfl⟩ : syracuseStep 1083385 = 812539) B812539
theorem B199983 : Blo 199806 199983 := bstep (se 1 (by rfl) ⟨149987, by rfl⟩ : syracuseStep 199983 = 299975) B299975
theorem B200191 : Blo 199806 200191 := bstep (se 1 (by rfl) ⟨150143, by rfl⟩ : syracuseStep 200191 = 300287) B300287
theorem B200223 : Blo 199806 200223 := bstep (se 1 (by rfl) ⟨150167, by rfl⟩ : syracuseStep 200223 = 300335) B300335
theorem B200359 : Blo 199806 200359 := bstep (se 1 (by rfl) ⟨150269, by rfl⟩ : syracuseStep 200359 = 300539) B300539
theorem B855785 : Blo 199806 855785 := bstep (se 2 (by rfl) ⟨320919, by rfl⟩ : syracuseStep 855785 = 641839) B641839
theorem B692039 : Blo 199806 692039 := bstep (se 1 (by rfl) ⟨519029, by rfl⟩ : syracuseStep 692039 = 1038059) B1038059
theorem B200815 : Blo 199806 200815 := bstep (se 1 (by rfl) ⟨150611, by rfl⟩ : syracuseStep 200815 = 301223) B301223
theorem B364819 : Blo 199806 364819 := bstep (se 1 (by rfl) ⟨273614, by rfl⟩ : syracuseStep 364819 = 547229) B547229
theorem B33067439 : Blo 199806 33067439 := bstep (se 1 (by rfl) ⟨24800579, by rfl⟩ : syracuseStep 33067439 = 49601159) B49601159
theorem B201447 : Blo 199806 201447 := bstep (se 1 (by rfl) ⟨151085, by rfl⟩ : syracuseStep 201447 = 302171) B302171
theorem B7377641 : Blo 199806 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B201895 : Blo 199806 201895 := bstep (se 1 (by rfl) ⟨151421, by rfl⟩ : syracuseStep 201895 = 302843) B302843
theorem B660743 : Blo 199806 660743 := bstep (se 1 (by rfl) ⟨495557, by rfl⟩ : syracuseStep 660743 = 991115) B991115
theorem B1021895 : Blo 199806 1021895 := bstep (se 1 (by rfl) ⟨766421, by rfl⟩ : syracuseStep 1021895 = 1532843) B1532843
theorem B202747 : Blo 199806 202747 := bstep (se 1 (by rfl) ⟨152060, by rfl⟩ : syracuseStep 202747 = 304121) B304121
theorem B301055 : Blo 199806 301055 := bstep (se 1 (by rfl) ⟨225791, by rfl⟩ : syracuseStep 301055 = 451583) B451583
theorem B202779 : Blo 199806 202779 := bstep (se 1 (by rfl) ⟨152084, by rfl⟩ : syracuseStep 202779 = 304169) B304169
theorem B203071 : Blo 199806 203071 := bstep (se 1 (by rfl) ⟨152303, by rfl⟩ : syracuseStep 203071 = 304607) B304607
theorem B727375 : Blo 199806 727375 := bstep (se 1 (by rfl) ⟨545531, by rfl⟩ : syracuseStep 727375 = 1091063) B1091063
theorem B203495 : Blo 199806 203495 := bstep (se 1 (by rfl) ⟨152621, by rfl⟩ : syracuseStep 203495 = 305243) B305243
theorem B302015 : Blo 199806 302015 := bstep (se 1 (by rfl) ⟨226511, by rfl⟩ : syracuseStep 302015 = 453023) B453023
theorem B203759 : Blo 199806 203759 := bstep (se 1 (by rfl) ⟨152819, by rfl⟩ : syracuseStep 203759 = 305639) B305639
theorem B203803 : Blo 199806 203803 := bstep (se 1 (by rfl) ⟨152852, by rfl⟩ : syracuseStep 203803 = 305705) B305705
theorem B761015 : Blo 199806 761015 := bstep (se 1 (by rfl) ⟨570761, by rfl⟩ : syracuseStep 761015 = 1141523) B1141523
theorem B335099 : Blo 199806 335099 := bstep (se 1 (by rfl) ⟨251324, by rfl⟩ : syracuseStep 335099 = 502649) B502649
theorem B302591 : Blo 199806 302591 := bstep (se 1 (by rfl) ⟨226943, by rfl⟩ : syracuseStep 302591 = 453887) B453887
theorem B761471 : Blo 199806 761471 := bstep (se 1 (by rfl) ⟨571103, by rfl⟩ : syracuseStep 761471 = 1142207) B1142207
theorem B303131 : Blo 199806 303131 := bstep (se 1 (by rfl) ⟨227348, by rfl⟩ : syracuseStep 303131 = 454697) B454697
theorem B303215 : Blo 199806 303215 := bstep (se 1 (by rfl) ⟨227411, by rfl⟩ : syracuseStep 303215 = 454823) B454823
theorem B434359 : Blo 199806 434359 := bstep (se 1 (by rfl) ⟨325769, by rfl⟩ : syracuseStep 434359 = 651539) B651539
theorem B303401 : Blo 199806 303401 := bstep (se 2 (by rfl) ⟨113775, by rfl⟩ : syracuseStep 303401 = 227551) B227551
theorem B1024487 : Blo 199806 1024487 := bstep (se 1 (by rfl) ⟨768365, by rfl⟩ : syracuseStep 1024487 = 1536731) B1536731
theorem B862123 : Blo 199806 862123 := bstep (se 1 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 862123 = 1293185) B1293185
theorem B1026269 : Blo 199806 1026269 := bstep (se 3 (by rfl) ⟨192425, by rfl⟩ : syracuseStep 1026269 = 384851) B384851
theorem B863081 : Blo 199806 863081 := bstep (se 2 (by rfl) ⟨323655, by rfl⟩ : syracuseStep 863081 = 647311) B647311
theorem B338809 : Blo 199806 338809 := bstep (se 2 (by rfl) ⟨127053, by rfl⟩ : syracuseStep 338809 = 254107) B254107
theorem B308863 : Blo 199806 308863 := bstep (se 1 (by rfl) ⟨231647, by rfl⟩ : syracuseStep 308863 = 463295) B463295
theorem B768275 : Blo 199806 768275 := bstep (se 1 (by rfl) ⟨576206, by rfl⟩ : syracuseStep 768275 = 1152413) B1152413
theorem B1030481 : Blo 199806 1030481 := bstep (se 2 (by rfl) ⟨386430, by rfl⟩ : syracuseStep 1030481 = 772861) B772861
theorem B1292699 : Blo 199806 1292699 := bstep (se 1 (by rfl) ⟨969524, by rfl⟩ : syracuseStep 1292699 = 1939049) B1939049
theorem B506351 : Blo 199806 506351 := bstep (se 1 (by rfl) ⟨379763, by rfl⟩ : syracuseStep 506351 = 759527) B759527
theorem B572015 : Blo 199806 572015 := bstep (se 1 (by rfl) ⟨429011, by rfl⟩ : syracuseStep 572015 = 858023) B858023
theorem B703259 : Blo 199806 703259 := bstep (se 1 (by rfl) ⟨527444, by rfl⟩ : syracuseStep 703259 = 1054889) B1054889
theorem B1030967 : Blo 199806 1030967 := bstep (se 1 (by rfl) ⟨773225, by rfl⟩ : syracuseStep 1030967 = 1546451) B1546451
theorem B506695 : Blo 199806 506695 := bstep (se 1 (by rfl) ⟨380021, by rfl⟩ : syracuseStep 506695 = 760043) B760043
theorem B801775 : Blo 199806 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B6274145 : Blo 199806 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B1163105 : Blo 199806 1163105 := bstep (se 2 (by rfl) ⟨436164, by rfl⟩ : syracuseStep 1163105 = 872329) B872329
theorem B737839 : Blo 199806 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B575113 : Blo 199806 575113 := bstep (se 2 (by rfl) ⟨215667, by rfl⟩ : syracuseStep 575113 = 431335) B431335
theorem B1526525 : Blo 199806 1526525 := bstep (se 3 (by rfl) ⟨286223, by rfl⟩ : syracuseStep 1526525 = 572447) B572447
theorem B642671 : Blo 199806 642671 := bstep (se 1 (by rfl) ⟨482003, by rfl⟩ : syracuseStep 642671 = 964007) B964007
theorem B675809 : Blo 199806 675809 := bstep (se 2 (by rfl) ⟨253428, by rfl⟩ : syracuseStep 675809 = 506857) B506857
theorem B676511 : Blo 199806 676511 := bstep (se 1 (by rfl) ⟨507383, by rfl⟩ : syracuseStep 676511 = 1014767) B1014767
theorem B512831 : Blo 199806 512831 := bstep (se 1 (by rfl) ⟨384623, by rfl⟩ : syracuseStep 512831 = 769247) B769247
theorem B449567 : Blo 199806 449567 := bstep (se 1 (by rfl) ⟨337175, by rfl⟩ : syracuseStep 449567 = 674351) B674351
theorem B515231 : Blo 199806 515231 := bstep (se 1 (by rfl) ⟨386423, by rfl⟩ : syracuseStep 515231 = 772847) B772847
theorem B286463 : Blo 199806 286463 := bstep (se 1 (by rfl) ⟨214847, by rfl⟩ : syracuseStep 286463 = 429695) B429695
theorem B450719 : Blo 199806 450719 := bstep (se 1 (by rfl) ⟨338039, by rfl⟩ : syracuseStep 450719 = 676079) B676079
theorem B451079 : Blo 199806 451079 := bstep (se 1 (by rfl) ⟨338309, by rfl⟩ : syracuseStep 451079 = 676619) B676619
theorem B386203 : Blo 199806 386203 := bstep (se 1 (by rfl) ⟨289652, by rfl⟩ : syracuseStep 386203 = 579305) B579305
theorem B452051 : Blo 199806 452051 := bstep (se 1 (by rfl) ⟨339038, by rfl⟩ : syracuseStep 452051 = 678077) B678077
theorem B3892859 : Blo 199806 3892859 := bstep (se 1 (by rfl) ⟨2919644, by rfl⟩ : syracuseStep 3892859 = 5839289) B5839289
theorem B452807 : Blo 199806 452807 := bstep (se 1 (by rfl) ⟨339605, by rfl⟩ : syracuseStep 452807 = 679211) B679211
theorem B224923 : Blo 199806 224923 := bstep (se 1 (by rfl) ⟨168692, by rfl⟩ : syracuseStep 224923 = 337385) B337385
theorem B455399 : Blo 199806 455399 := bstep (se 1 (by rfl) ⟨341549, by rfl⟩ : syracuseStep 455399 = 683099) B683099
theorem B1733471 : Blo 199806 1733471 := bstep (se 1 (by rfl) ⟨1300103, by rfl⟩ : syracuseStep 1733471 = 2600207) B2600207
theorem B455615 : Blo 199806 455615 := bstep (se 1 (by rfl) ⟨341711, by rfl⟩ : syracuseStep 455615 = 683423) B683423
theorem B1734533 : Blo 199806 1734533 := bstep (se 4 (by rfl) ⟨162612, by rfl⟩ : syracuseStep 1734533 = 325225) B325225
theorem B456659 : Blo 199806 456659 := bstep (se 1 (by rfl) ⟨342494, by rfl⟩ : syracuseStep 456659 = 684989) B684989
theorem B456929 : Blo 199806 456929 := bstep (se 2 (by rfl) ⟨171348, by rfl⟩ : syracuseStep 456929 = 342697) B342697
theorem B1538675 : Blo 199806 1538675 := bstep (se 1 (by rfl) ⟨1154006, by rfl⟩ : syracuseStep 1538675 = 2308013) B2308013
theorem B1017683 : Blo 199806 1017683 := bstep (se 1 (by rfl) ⟨763262, by rfl⟩ : syracuseStep 1017683 = 1526525) B1526525
theorem B428447 : Blo 199806 428447 := bstep (se 1 (by rfl) ⟨321335, by rfl⟩ : syracuseStep 428447 = 642671) B642671
theorem B461359 : Blo 199806 461359 := bstep (se 1 (by rfl) ⟨346019, by rfl⟩ : syracuseStep 461359 = 692039) B692039
theorem B1149497 : Blo 199806 1149497 := bstep (se 2 (by rfl) ⟨431061, by rfl⟩ : syracuseStep 1149497 = 862123) B862123
theorem B1444513 : Blo 199806 1444513 := bstep (se 2 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 1444513 = 1083385) B1083385
theorem B3935141 : Blo 199806 3935141 := bstep (se 4 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 3935141 = 737839) B737839
theorem B4918427 : Blo 199806 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B200703 : Blo 199806 200703 := bstep (se 1 (by rfl) ⟨150527, by rfl⟩ : syracuseStep 200703 = 301055) B301055
theorem B201343 : Blo 199806 201343 := bstep (se 1 (by rfl) ⟨151007, by rfl⟩ : syracuseStep 201343 = 302015) B302015
theorem B299711 : Blo 199806 299711 := bstep (se 1 (by rfl) ⟨224783, by rfl⟩ : syracuseStep 299711 = 449567) B449567
theorem B299897 : Blo 199806 299897 := bstep (se 2 (by rfl) ⟨112461, by rfl⟩ : syracuseStep 299897 = 224923) B224923
theorem B201727 : Blo 199806 201727 := bstep (se 1 (by rfl) ⟨151295, by rfl⟩ : syracuseStep 201727 = 302591) B302591
theorem B202087 : Blo 199806 202087 := bstep (se 1 (by rfl) ⟨151565, by rfl⟩ : syracuseStep 202087 = 303131) B303131
theorem B202143 : Blo 199806 202143 := bstep (se 1 (by rfl) ⟨151607, by rfl⟩ : syracuseStep 202143 = 303215) B303215
theorem B300479 : Blo 199806 300479 := bstep (se 1 (by rfl) ⟨225359, by rfl⟩ : syracuseStep 300479 = 450719) B450719
theorem B202267 : Blo 199806 202267 := bstep (se 1 (by rfl) ⟨151700, by rfl⟩ : syracuseStep 202267 = 303401) B303401
theorem B300719 : Blo 199806 300719 := bstep (se 1 (by rfl) ⟨225539, by rfl⟩ : syracuseStep 300719 = 451079) B451079
theorem B301367 : Blo 199806 301367 := bstep (se 1 (by rfl) ⟨226025, by rfl⟩ : syracuseStep 301367 = 452051) B452051
theorem B2595239 : Blo 199806 2595239 := bstep (se 1 (by rfl) ⟨1946429, by rfl⟩ : syracuseStep 2595239 = 3892859) B3892859
theorem B301871 : Blo 199806 301871 := bstep (se 1 (by rfl) ⟨226403, by rfl⟩ : syracuseStep 301871 = 452807) B452807
theorem B303599 : Blo 199806 303599 := bstep (se 1 (by rfl) ⟨227699, by rfl⟩ : syracuseStep 303599 = 455399) B455399
theorem B1155647 : Blo 199806 1155647 := bstep (se 1 (by rfl) ⟨866735, by rfl⟩ : syracuseStep 1155647 = 1733471) B1733471
theorem B303743 : Blo 199806 303743 := bstep (se 1 (by rfl) ⟨227807, by rfl⟩ : syracuseStep 303743 = 455615) B455615
theorem B1156355 : Blo 199806 1156355 := bstep (se 1 (by rfl) ⟨867266, by rfl⟩ : syracuseStep 1156355 = 1734533) B1734533
theorem B304439 : Blo 199806 304439 := bstep (se 1 (by rfl) ⟨228329, by rfl⟩ : syracuseStep 304439 = 456659) B456659
theorem B304619 : Blo 199806 304619 := bstep (se 1 (by rfl) ⟨228464, by rfl⟩ : syracuseStep 304619 = 456929) B456929
theorem B861799 : Blo 199806 861799 := bstep (se 1 (by rfl) ⟨646349, by rfl⟩ : syracuseStep 861799 = 1292699) B1292699
theorem B337567 : Blo 199806 337567 := bstep (se 1 (by rfl) ⟨253175, by rfl⟩ : syracuseStep 337567 = 506351) B506351
theorem B1025783 : Blo 199806 1025783 := bstep (se 1 (by rfl) ⟨769337, by rfl⟩ : syracuseStep 1025783 = 1538675) B1538675
theorem B468839 : Blo 199806 468839 := bstep (se 1 (by rfl) ⟨351629, by rfl⟩ : syracuseStep 468839 = 703259) B703259
theorem B763901 : Blo 199806 763901 := bstep (se 3 (by rfl) ⟨143231, by rfl⟩ : syracuseStep 763901 = 286463) B286463
theorem B765359 : Blo 199806 765359 := bstep (se 1 (by rfl) ⟨574019, by rfl⟩ : syracuseStep 765359 = 1148039) B1148039
theorem B766817 : Blo 199806 766817 := bstep (se 2 (by rfl) ⟨287556, by rfl⟩ : syracuseStep 766817 = 575113) B575113
theorem B570523 : Blo 199806 570523 := bstep (se 1 (by rfl) ⟨427892, by rfl⟩ : syracuseStep 570523 = 855785) B855785
theorem B341887 : Blo 199806 341887 := bstep (se 1 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 341887 = 512831) B512831
theorem B440495 : Blo 199806 440495 := bstep (se 1 (by rfl) ⟨330371, by rfl⟩ : syracuseStep 440495 = 660743) B660743
theorem B343487 : Blo 199806 343487 := bstep (se 1 (by rfl) ⟨257615, by rfl⟩ : syracuseStep 343487 = 515231) B515231
theorem B507343 : Blo 199806 507343 := bstep (se 1 (by rfl) ⟨380507, by rfl⟩ : syracuseStep 507343 = 761015) B761015
theorem B507647 : Blo 199806 507647 := bstep (se 1 (by rfl) ⟨380735, by rfl⟩ : syracuseStep 507647 = 761471) B761471
theorem B575387 : Blo 199806 575387 := bstep (se 1 (by rfl) ⟨431540, by rfl⟩ : syracuseStep 575387 = 863081) B863081
theorem B411817 : Blo 199806 411817 := bstep (se 2 (by rfl) ⟨154431, by rfl⟩ : syracuseStep 411817 = 308863) B308863
theorem B969833 : Blo 199806 969833 := bstep (se 2 (by rfl) ⟨363687, by rfl⟩ : syracuseStep 969833 = 727375) B727375
theorem B675593 : Blo 199806 675593 := bstep (se 2 (by rfl) ⟨253347, by rfl⟩ : syracuseStep 675593 = 506695) B506695
theorem B1069033 : Blo 199806 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B512183 : Blo 199806 512183 := bstep (se 1 (by rfl) ⟨384137, by rfl⟩ : syracuseStep 512183 = 768275) B768275
theorem B381343 : Blo 199806 381343 := bstep (se 1 (by rfl) ⟨286007, by rfl⟩ : syracuseStep 381343 = 572015) B572015
theorem B4182763 : Blo 199806 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B775403 : Blo 199806 775403 := bstep (se 1 (by rfl) ⟨581552, by rfl⟩ : syracuseStep 775403 = 1163105) B1163105
theorem B579145 : Blo 199806 579145 := bstep (se 2 (by rfl) ⟨217179, by rfl⟩ : syracuseStep 579145 = 434359) B434359
theorem B3758089 : Blo 199806 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B514937 : Blo 199806 514937 := bstep (se 2 (by rfl) ⟨193101, by rfl⟩ : syracuseStep 514937 = 386203) B386203
theorem B1367549 : Blo 199806 1367549 := bstep (se 3 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 1367549 = 512831) B512831
theorem B450539 : Blo 199806 450539 := bstep (se 1 (by rfl) ⟨337904, by rfl⟩ : syracuseStep 450539 = 675809) B675809
theorem B22044959 : Blo 199806 22044959 := bstep (se 1 (by rfl) ⟨16533719, by rfl⟩ : syracuseStep 22044959 = 33067439) B33067439
theorem B451007 : Blo 199806 451007 := bstep (se 1 (by rfl) ⟨338255, by rfl⟩ : syracuseStep 451007 = 676511) B676511
theorem B451745 : Blo 199806 451745 := bstep (se 2 (by rfl) ⟨169404, by rfl⟩ : syracuseStep 451745 = 338809) B338809
theorem B681263 : Blo 199806 681263 := bstep (se 1 (by rfl) ⟨510947, by rfl⟩ : syracuseStep 681263 = 1021895) B1021895
theorem B223399 : Blo 199806 223399 := bstep (se 1 (by rfl) ⟨167549, by rfl⟩ : syracuseStep 223399 = 335099) B335099
theorem B682991 : Blo 199806 682991 := bstep (se 1 (by rfl) ⟨512243, by rfl⟩ : syracuseStep 682991 = 1024487) B1024487
theorem B486425 : Blo 199806 486425 := bstep (se 2 (by rfl) ⟨182409, by rfl⟩ : syracuseStep 486425 = 364819) B364819
theorem B684179 : Blo 199806 684179 := bstep (se 1 (by rfl) ⟨513134, by rfl⟩ : syracuseStep 684179 = 1026269) B1026269
theorem B686987 : Blo 199806 686987 := bstep (se 1 (by rfl) ⟨515240, by rfl⟩ : syracuseStep 686987 = 1030481) B1030481
theorem B687311 : Blo 199806 687311 := bstep (se 1 (by rfl) ⟨515483, by rfl⟩ : syracuseStep 687311 = 1030967) B1030967
theorem B2623427 : Blo 199806 2623427 := bstep (se 1 (by rfl) ⟨1967570, by rfl⟩ : syracuseStep 2623427 = 3935141) B3935141
theorem B3278951 : Blo 199806 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B1149065 : Blo 199806 1149065 := bstep (se 2 (by rfl) ⟨430899, by rfl⟩ : syracuseStep 1149065 = 861799) B861799
theorem B297865 : Blo 199806 297865 := bstep (se 2 (by rfl) ⟨111699, by rfl⟩ : syracuseStep 297865 = 223399) B223399
theorem B2460581 : Blo 199806 2460581 := bstep (se 4 (by rfl) ⟨230679, by rfl⟩ : syracuseStep 2460581 = 461359) B461359
theorem B199807 : Blo 199806 199807 := bstep (se 1 (by rfl) ⟨149855, by rfl⟩ : syracuseStep 199807 = 299711) B299711
theorem B199931 : Blo 199806 199931 := bstep (se 1 (by rfl) ⟨149948, by rfl⟩ : syracuseStep 199931 = 299897) B299897
theorem B200319 : Blo 199806 200319 := bstep (se 1 (by rfl) ⟨150239, by rfl⟩ : syracuseStep 200319 = 300479) B300479
theorem B200479 : Blo 199806 200479 := bstep (se 1 (by rfl) ⟨150359, by rfl⟩ : syracuseStep 200479 = 300719) B300719
theorem B200911 : Blo 199806 200911 := bstep (se 1 (by rfl) ⟨150683, by rfl⟩ : syracuseStep 200911 = 301367) B301367
theorem B201247 : Blo 199806 201247 := bstep (se 1 (by rfl) ⟨150935, by rfl⟩ : syracuseStep 201247 = 301871) B301871
theorem B300359 : Blo 199806 300359 := bstep (se 1 (by rfl) ⟨225269, by rfl⟩ : syracuseStep 300359 = 450539) B450539
theorem B300671 : Blo 199806 300671 := bstep (se 1 (by rfl) ⟨225503, by rfl⟩ : syracuseStep 300671 = 451007) B451007
theorem B202399 : Blo 199806 202399 := bstep (se 1 (by rfl) ⟨151799, by rfl⟩ : syracuseStep 202399 = 303599) B303599
theorem B202495 : Blo 199806 202495 := bstep (se 1 (by rfl) ⟨151871, by rfl⟩ : syracuseStep 202495 = 303743) B303743
theorem B301163 : Blo 199806 301163 := bstep (se 1 (by rfl) ⟨225872, by rfl⟩ : syracuseStep 301163 = 451745) B451745
theorem B202959 : Blo 199806 202959 := bstep (se 1 (by rfl) ⟨152219, by rfl⟩ : syracuseStep 202959 = 304439) B304439
theorem B5577017 : Blo 199806 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B203079 : Blo 199806 203079 := bstep (se 1 (by rfl) ⟨152309, by rfl⟩ : syracuseStep 203079 = 304619) B304619
theorem B760697 : Blo 199806 760697 := bstep (se 2 (by rfl) ⟨285261, by rfl⟩ : syracuseStep 760697 = 570523) B570523
theorem B338431 : Blo 199806 338431 := bstep (se 1 (by rfl) ⟨253823, by rfl⟩ : syracuseStep 338431 = 507647) B507647
theorem B766331 : Blo 199806 766331 := bstep (se 1 (by rfl) ⟨574748, by rfl⟩ : syracuseStep 766331 = 1149497) B1149497
theorem B341455 : Blo 199806 341455 := bstep (se 1 (by rfl) ⟨256091, by rfl⟩ : syracuseStep 341455 = 512183) B512183
theorem B343291 : Blo 199806 343291 := bstep (se 1 (by rfl) ⟨257468, by rfl⟩ : syracuseStep 343291 = 514937) B514937
theorem B1425377 : Blo 199806 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B14696639 : Blo 199806 14696639 := bstep (se 1 (by rfl) ⟨11022479, by rfl⟩ : syracuseStep 14696639 = 22044959) B22044959
theorem B770431 : Blo 199806 770431 := bstep (se 1 (by rfl) ⟨577823, by rfl⟩ : syracuseStep 770431 = 1155647) B1155647
theorem B508457 : Blo 199806 508457 := bstep (se 2 (by rfl) ⟨190671, by rfl⟩ : syracuseStep 508457 = 381343) B381343
theorem B770903 : Blo 199806 770903 := bstep (se 1 (by rfl) ⟨578177, by rfl⟩ : syracuseStep 770903 = 1156355) B1156355
theorem B312559 : Blo 199806 312559 := bstep (se 1 (by rfl) ⟨234419, by rfl⟩ : syracuseStep 312559 = 468839) B468839
theorem B509267 : Blo 199806 509267 := bstep (se 1 (by rfl) ⟨381950, by rfl⟩ : syracuseStep 509267 = 763901) B763901
theorem B772193 : Blo 199806 772193 := bstep (se 2 (by rfl) ⟨289572, by rfl⟩ : syracuseStep 772193 = 579145) B579145
theorem B510239 : Blo 199806 510239 := bstep (se 1 (by rfl) ⟨382679, by rfl⟩ : syracuseStep 510239 = 765359) B765359
theorem B1297133 : Blo 199806 1297133 := bstep (se 3 (by rfl) ⟨243212, by rfl⟩ : syracuseStep 1297133 = 486425) B486425
theorem B511211 : Blo 199806 511211 := bstep (se 1 (by rfl) ⟨383408, by rfl⟩ : syracuseStep 511211 = 766817) B766817
theorem B676457 : Blo 199806 676457 := bstep (se 2 (by rfl) ⟨253671, by rfl⟩ : syracuseStep 676457 = 507343) B507343
theorem B678455 : Blo 199806 678455 := bstep (se 1 (by rfl) ⟨508841, by rfl⟩ : syracuseStep 678455 = 1017683) B1017683
theorem B383591 : Blo 199806 383591 := bstep (se 1 (by rfl) ⟨287693, by rfl⟩ : syracuseStep 383591 = 575387) B575387
theorem B646555 : Blo 199806 646555 := bstep (se 1 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 646555 = 969833) B969833
theorem B450089 : Blo 199806 450089 := bstep (se 2 (by rfl) ⟨168783, by rfl⟩ : syracuseStep 450089 = 337567) B337567
theorem B450395 : Blo 199806 450395 := bstep (se 1 (by rfl) ⟨337796, by rfl⟩ : syracuseStep 450395 = 675593) B675593
theorem B549089 : Blo 199806 549089 := bstep (se 2 (by rfl) ⟨205908, by rfl⟩ : syracuseStep 549089 = 411817) B411817
theorem B516935 : Blo 199806 516935 := bstep (se 1 (by rfl) ⟨387701, by rfl⟩ : syracuseStep 516935 = 775403) B775403
theorem B1926017 : Blo 199806 1926017 := bstep (se 2 (by rfl) ⟨722256, by rfl⟩ : syracuseStep 1926017 = 1444513) B1444513
theorem B1730159 : Blo 199806 1730159 := bstep (se 1 (by rfl) ⟨1297619, by rfl⟩ : syracuseStep 1730159 = 2595239) B2595239
theorem B911699 : Blo 199806 911699 := bstep (se 1 (by rfl) ⟨683774, by rfl⟩ : syracuseStep 911699 = 1367549) B1367549
theorem B454175 : Blo 199806 454175 := bstep (se 1 (by rfl) ⟨340631, by rfl⟩ : syracuseStep 454175 = 681263) B681263
theorem B1142525 : Blo 199806 1142525 := bstep (se 3 (by rfl) ⟨214223, by rfl⟩ : syracuseStep 1142525 = 428447) B428447
theorem B683855 : Blo 199806 683855 := bstep (se 1 (by rfl) ⟨512891, by rfl⟩ : syracuseStep 683855 = 1025783) B1025783
theorem B455327 : Blo 199806 455327 := bstep (se 1 (by rfl) ⟨341495, by rfl⟩ : syracuseStep 455327 = 682991) B682991
theorem B455849 : Blo 199806 455849 := bstep (se 2 (by rfl) ⟨170943, by rfl⟩ : syracuseStep 455849 = 341887) B341887
theorem B5010785 : Blo 199806 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B456119 : Blo 199806 456119 := bstep (se 1 (by rfl) ⟨342089, by rfl⟩ : syracuseStep 456119 = 684179) B684179
theorem B293663 : Blo 199806 293663 := bstep (se 1 (by rfl) ⟨220247, by rfl⟩ : syracuseStep 293663 = 440495) B440495
theorem B457991 : Blo 199806 457991 := bstep (se 1 (by rfl) ⟨343493, by rfl⟩ : syracuseStep 457991 = 686987) B686987
theorem B458207 : Blo 199806 458207 := bstep (se 1 (by rfl) ⟨343655, by rfl⟩ : syracuseStep 458207 = 687311) B687311
theorem B228991 : Blo 199806 228991 := bstep (se 1 (by rfl) ⟨171743, by rfl⟩ : syracuseStep 228991 = 343487) B343487
theorem B9797759 : Blo 199806 9797759 := bstep (se 1 (by rfl) ⟨7348319, by rfl⟩ : syracuseStep 9797759 = 14696639) B14696639
theorem B1640387 : Blo 199806 1640387 := bstep (se 1 (by rfl) ⟨1230290, by rfl⟩ : syracuseStep 1640387 = 2460581) B2460581
theorem B200239 : Blo 199806 200239 := bstep (se 1 (by rfl) ⟨150179, by rfl⟩ : syracuseStep 200239 = 300359) B300359
theorem B200447 : Blo 199806 200447 := bstep (se 1 (by rfl) ⟨150335, by rfl⟩ : syracuseStep 200447 = 300671) B300671
theorem B397153 : Blo 199806 397153 := bstep (se 2 (by rfl) ⟨148932, by rfl⟩ : syracuseStep 397153 = 297865) B297865
theorem B200775 : Blo 199806 200775 := bstep (se 1 (by rfl) ⟨150581, by rfl⟩ : syracuseStep 200775 = 301163) B301163
theorem B300059 : Blo 199806 300059 := bstep (se 1 (by rfl) ⟨225044, by rfl⟩ : syracuseStep 300059 = 450089) B450089
theorem B300263 : Blo 199806 300263 := bstep (se 1 (by rfl) ⟨225197, by rfl⟩ : syracuseStep 300263 = 450395) B450395
theorem B366059 : Blo 199806 366059 := bstep (se 1 (by rfl) ⟨274544, by rfl⟩ : syracuseStep 366059 = 549089) B549089
theorem B1284011 : Blo 199806 1284011 := bstep (se 1 (by rfl) ⟨963008, by rfl⟩ : syracuseStep 1284011 = 1926017) B1926017
theorem B1153439 : Blo 199806 1153439 := bstep (se 1 (by rfl) ⟨865079, by rfl⟩ : syracuseStep 1153439 = 1730159) B1730159
theorem B302783 : Blo 199806 302783 := bstep (se 1 (by rfl) ⟨227087, by rfl⟩ : syracuseStep 302783 = 454175) B454175
theorem B761683 : Blo 199806 761683 := bstep (se 1 (by rfl) ⟨571262, by rfl⟩ : syracuseStep 761683 = 1142525) B1142525
theorem B303551 : Blo 199806 303551 := bstep (se 1 (by rfl) ⟨227663, by rfl⟩ : syracuseStep 303551 = 455327) B455327
theorem B303899 : Blo 199806 303899 := bstep (se 1 (by rfl) ⟨227924, by rfl⟩ : syracuseStep 303899 = 455849) B455849
theorem B304079 : Blo 199806 304079 := bstep (se 1 (by rfl) ⟨228059, by rfl⟩ : syracuseStep 304079 = 456119) B456119
theorem B862073 : Blo 199806 862073 := bstep (se 2 (by rfl) ⟨323277, by rfl⟩ : syracuseStep 862073 = 646555) B646555
theorem B305321 : Blo 199806 305321 := bstep (se 2 (by rfl) ⟨114495, by rfl⟩ : syracuseStep 305321 = 228991) B228991
theorem B305327 : Blo 199806 305327 := bstep (se 1 (by rfl) ⟨228995, by rfl⟩ : syracuseStep 305327 = 457991) B457991
theorem B305471 : Blo 199806 305471 := bstep (se 1 (by rfl) ⟨229103, by rfl⟩ : syracuseStep 305471 = 458207) B458207
theorem B338971 : Blo 199806 338971 := bstep (se 1 (by rfl) ⟨254228, by rfl⟩ : syracuseStep 338971 = 508457) B508457
theorem B1027241 : Blo 199806 1027241 := bstep (se 2 (by rfl) ⟨385215, by rfl⟩ : syracuseStep 1027241 = 770431) B770431
theorem B339511 : Blo 199806 339511 := bstep (se 1 (by rfl) ⟨254633, by rfl⟩ : syracuseStep 339511 = 509267) B509267
theorem B1748951 : Blo 199806 1748951 := bstep (se 1 (by rfl) ⟨1311713, by rfl⟩ : syracuseStep 1748951 = 2623427) B2623427
theorem B766043 : Blo 199806 766043 := bstep (se 1 (by rfl) ⟨574532, by rfl⟩ : syracuseStep 766043 = 1149065) B1149065
theorem B340159 : Blo 199806 340159 := bstep (se 1 (by rfl) ⟨255119, by rfl⟩ : syracuseStep 340159 = 510239) B510239
theorem B864755 : Blo 199806 864755 := bstep (se 1 (by rfl) ⟨648566, by rfl⟩ : syracuseStep 864755 = 1297133) B1297133
theorem B340807 : Blo 199806 340807 := bstep (se 1 (by rfl) ⟨255605, by rfl⟩ : syracuseStep 340807 = 511211) B511211
theorem B507131 : Blo 199806 507131 := bstep (se 1 (by rfl) ⟨380348, by rfl⟩ : syracuseStep 507131 = 760697) B760697
theorem B344623 : Blo 199806 344623 := bstep (se 1 (by rfl) ⟨258467, by rfl⟩ : syracuseStep 344623 = 516935) B516935
theorem B607799 : Blo 199806 607799 := bstep (se 1 (by rfl) ⟨455849, by rfl⟩ : syracuseStep 607799 = 911699) B911699
theorem B510887 : Blo 199806 510887 := bstep (se 1 (by rfl) ⟨383165, by rfl⟩ : syracuseStep 510887 = 766331) B766331
theorem B513935 : Blo 199806 513935 := bstep (se 1 (by rfl) ⟨385451, by rfl⟩ : syracuseStep 513935 = 770903) B770903
theorem B514795 : Blo 199806 514795 := bstep (se 1 (by rfl) ⟨386096, by rfl⟩ : syracuseStep 514795 = 772193) B772193
theorem B2185967 : Blo 199806 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B450971 : Blo 199806 450971 := bstep (se 1 (by rfl) ⟨338228, by rfl⟩ : syracuseStep 450971 = 676457) B676457
theorem B451241 : Blo 199806 451241 := bstep (se 2 (by rfl) ⟨169215, by rfl⟩ : syracuseStep 451241 = 338431) B338431
theorem B452303 : Blo 199806 452303 := bstep (se 1 (by rfl) ⟨339227, by rfl⟩ : syracuseStep 452303 = 678455) B678455
theorem B255727 : Blo 199806 255727 := bstep (se 1 (by rfl) ⟨191795, by rfl⟩ : syracuseStep 255727 = 383591) B383591
theorem B14872045 : Blo 199806 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B1666981 : Blo 199806 1666981 := bstep (se 4 (by rfl) ⟨156279, by rfl⟩ : syracuseStep 1666981 = 312559) B312559
theorem B455273 : Blo 199806 455273 := bstep (se 2 (by rfl) ⟨170727, by rfl⟩ : syracuseStep 455273 = 341455) B341455
theorem B783101 : Blo 199806 783101 := bstep (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) B293663
theorem B455903 : Blo 199806 455903 := bstep (se 1 (by rfl) ⟨341927, by rfl⟩ : syracuseStep 455903 = 683855) B683855
theorem B3340523 : Blo 199806 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B457721 : Blo 199806 457721 := bstep (se 2 (by rfl) ⟨171645, by rfl⟩ : syracuseStep 457721 = 343291) B343291
theorem B3801005 : Blo 199806 3801005 := bstep (se 3 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 3801005 = 1425377) B1425377
theorem B459497 : Blo 199806 459497 := bstep (se 2 (by rfl) ⟨172311, by rfl⟩ : syracuseStep 459497 = 344623) B344623
theorem B200039 : Blo 199806 200039 := bstep (se 1 (by rfl) ⟨150029, by rfl⟩ : syracuseStep 200039 = 300059) B300059
theorem B200175 : Blo 199806 200175 := bstep (se 1 (by rfl) ⟨150131, by rfl⟩ : syracuseStep 200175 = 300263) B300263
theorem B856007 : Blo 199806 856007 := bstep (se 1 (by rfl) ⟨642005, by rfl⟩ : syracuseStep 856007 = 1284011) B1284011
theorem B19829393 : Blo 199806 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B201855 : Blo 199806 201855 := bstep (se 1 (by rfl) ⟨151391, by rfl⟩ : syracuseStep 201855 = 302783) B302783
theorem B300647 : Blo 199806 300647 := bstep (se 1 (by rfl) ⟨225485, by rfl⟩ : syracuseStep 300647 = 450971) B450971
theorem B202367 : Blo 199806 202367 := bstep (se 1 (by rfl) ⟨151775, by rfl⟩ : syracuseStep 202367 = 303551) B303551
theorem B300827 : Blo 199806 300827 := bstep (se 1 (by rfl) ⟨225620, by rfl⟩ : syracuseStep 300827 = 451241) B451241
theorem B202599 : Blo 199806 202599 := bstep (se 1 (by rfl) ⟨151949, by rfl⟩ : syracuseStep 202599 = 303899) B303899
theorem B202719 : Blo 199806 202719 := bstep (se 1 (by rfl) ⟨152039, by rfl⟩ : syracuseStep 202719 = 304079) B304079
theorem B301535 : Blo 199806 301535 := bstep (se 1 (by rfl) ⟨226151, by rfl⟩ : syracuseStep 301535 = 452303) B452303
theorem B203547 : Blo 199806 203547 := bstep (se 1 (by rfl) ⟨152660, by rfl⟩ : syracuseStep 203547 = 305321) B305321
theorem B203551 : Blo 199806 203551 := bstep (se 1 (by rfl) ⟨152663, by rfl⟩ : syracuseStep 203551 = 305327) B305327
theorem B203647 : Blo 199806 203647 := bstep (se 1 (by rfl) ⟨152735, by rfl⟩ : syracuseStep 203647 = 305471) B305471
theorem B303515 : Blo 199806 303515 := bstep (se 1 (by rfl) ⟨227636, by rfl⟩ : syracuseStep 303515 = 455273) B455273
theorem B303935 : Blo 199806 303935 := bstep (se 1 (by rfl) ⟨227951, by rfl⟩ : syracuseStep 303935 = 455903) B455903
theorem B305147 : Blo 199806 305147 := bstep (se 1 (by rfl) ⟨228860, by rfl⟩ : syracuseStep 305147 = 457721) B457721
theorem B338087 : Blo 199806 338087 := bstep (se 1 (by rfl) ⟨253565, by rfl⟩ : syracuseStep 338087 = 507131) B507131
theorem B8890565 : Blo 199806 8890565 := bstep (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) B1666981
theorem B2534003 : Blo 199806 2534003 := bstep (se 1 (by rfl) ⟨1900502, by rfl⟩ : syracuseStep 2534003 = 3801005) B3801005
theorem B6531839 : Blo 199806 6531839 := bstep (se 1 (by rfl) ⟨4898879, by rfl⟩ : syracuseStep 6531839 = 9797759) B9797759
theorem B405199 : Blo 199806 405199 := bstep (se 1 (by rfl) ⟨303899, by rfl⟩ : syracuseStep 405199 = 607799) B607799
theorem B1093591 : Blo 199806 1093591 := bstep (se 1 (by rfl) ⟨820193, by rfl⟩ : syracuseStep 1093591 = 1640387) B1640387
theorem B340591 : Blo 199806 340591 := bstep (se 1 (by rfl) ⟨255443, by rfl⟩ : syracuseStep 340591 = 510887) B510887
theorem B340969 : Blo 199806 340969 := bstep (se 2 (by rfl) ⟨127863, by rfl⟩ : syracuseStep 340969 = 255727) B255727
theorem B244039 : Blo 199806 244039 := bstep (se 1 (by rfl) ⟨183029, by rfl⟩ : syracuseStep 244039 = 366059) B366059
theorem B342623 : Blo 199806 342623 := bstep (se 1 (by rfl) ⟨256967, by rfl⟩ : syracuseStep 342623 = 513935) B513935
theorem B768959 : Blo 199806 768959 := bstep (se 1 (by rfl) ⟨576719, by rfl⟩ : syracuseStep 768959 = 1153439) B1153439
theorem B574715 : Blo 199806 574715 := bstep (se 1 (by rfl) ⟨431036, by rfl⟩ : syracuseStep 574715 = 862073) B862073
theorem B1165967 : Blo 199806 1165967 := bstep (se 1 (by rfl) ⟨874475, by rfl⟩ : syracuseStep 1165967 = 1748951) B1748951
theorem B510695 : Blo 199806 510695 := bstep (se 1 (by rfl) ⟨383021, by rfl⟩ : syracuseStep 510695 = 766043) B766043
theorem B576503 : Blo 199806 576503 := bstep (se 1 (by rfl) ⟨432377, by rfl⟩ : syracuseStep 576503 = 864755) B864755
theorem B2118149 : Blo 199806 2118149 := bstep (se 4 (by rfl) ⟨198576, by rfl⟩ : syracuseStep 2118149 = 397153) B397153
theorem B451961 : Blo 199806 451961 := bstep (se 2 (by rfl) ⟨169485, by rfl⟩ : syracuseStep 451961 = 338971) B338971
theorem B452681 : Blo 199806 452681 := bstep (se 2 (by rfl) ⟨169755, by rfl⟩ : syracuseStep 452681 = 339511) B339511
theorem B453545 : Blo 199806 453545 := bstep (se 2 (by rfl) ⟨170079, by rfl⟩ : syracuseStep 453545 = 340159) B340159
theorem B8908061 : Blo 199806 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B454409 : Blo 199806 454409 := bstep (se 2 (by rfl) ⟨170403, by rfl⟩ : syracuseStep 454409 = 340807) B340807
theorem B5829245 : Blo 199806 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B684827 : Blo 199806 684827 := bstep (se 1 (by rfl) ⟨513620, by rfl⟩ : syracuseStep 684827 = 1027241) B1027241
theorem B522067 : Blo 199806 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B686393 : Blo 199806 686393 := bstep (se 2 (by rfl) ⟨257397, by rfl⟩ : syracuseStep 686393 = 514795) B514795
theorem B1015577 : Blo 199806 1015577 := bstep (se 2 (by rfl) ⟨380841, by rfl⟩ : syracuseStep 1015577 = 761683) B761683
theorem B1412099 : Blo 199806 1412099 := bstep (se 1 (by rfl) ⟨1059074, by rfl⟩ : syracuseStep 1412099 = 2118149) B2118149
theorem B200431 : Blo 199806 200431 := bstep (se 1 (by rfl) ⟨150323, by rfl⟩ : syracuseStep 200431 = 300647) B300647
theorem B200551 : Blo 199806 200551 := bstep (se 1 (by rfl) ⟨150413, by rfl⟩ : syracuseStep 200551 = 300827) B300827
theorem B201023 : Blo 199806 201023 := bstep (se 1 (by rfl) ⟨150767, by rfl⟩ : syracuseStep 201023 = 301535) B301535
theorem B202343 : Blo 199806 202343 := bstep (se 1 (by rfl) ⟨151757, by rfl⟩ : syracuseStep 202343 = 303515) B303515
theorem B202623 : Blo 199806 202623 := bstep (se 1 (by rfl) ⟨151967, by rfl⟩ : syracuseStep 202623 = 303935) B303935
theorem B301307 : Blo 199806 301307 := bstep (se 1 (by rfl) ⟨225980, by rfl⟩ : syracuseStep 301307 = 451961) B451961
theorem B203431 : Blo 199806 203431 := bstep (se 1 (by rfl) ⟨152573, by rfl⟩ : syracuseStep 203431 = 305147) B305147
theorem B301787 : Blo 199806 301787 := bstep (se 1 (by rfl) ⟨226340, by rfl⟩ : syracuseStep 301787 = 452681) B452681
theorem B302363 : Blo 199806 302363 := bstep (se 1 (by rfl) ⟨226772, by rfl⟩ : syracuseStep 302363 = 453545) B453545
theorem B696089 : Blo 199806 696089 := bstep (se 2 (by rfl) ⟨261033, by rfl⟩ : syracuseStep 696089 = 522067) B522067
theorem B302939 : Blo 199806 302939 := bstep (se 1 (by rfl) ⟨227204, by rfl⟩ : syracuseStep 302939 = 454409) B454409
theorem B340463 : Blo 199806 340463 := bstep (se 1 (by rfl) ⟨255347, by rfl⟩ : syracuseStep 340463 = 510695) B510695
theorem B1225325 : Blo 199806 1225325 := bstep (se 3 (by rfl) ⟨229748, by rfl⟩ : syracuseStep 1225325 = 459497) B459497
theorem B570671 : Blo 199806 570671 := bstep (se 1 (by rfl) ⟨428003, by rfl⟩ : syracuseStep 570671 = 856007) B856007
theorem B13219595 : Blo 199806 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B540265 : Blo 199806 540265 := bstep (se 2 (by rfl) ⟨202599, by rfl⟩ : syracuseStep 540265 = 405199) B405199
theorem B1458121 : Blo 199806 1458121 := bstep (se 2 (by rfl) ⟨546795, by rfl⟩ : syracuseStep 1458121 = 1093591) B1093591
theorem B23708173 : Blo 199806 23708173 := bstep (se 3 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 23708173 = 8890565) B8890565
theorem B1689335 : Blo 199806 1689335 := bstep (se 1 (by rfl) ⟨1267001, by rfl⟩ : syracuseStep 1689335 = 2534003) B2534003
theorem B3886163 : Blo 199806 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B512639 : Blo 199806 512639 := bstep (se 1 (by rfl) ⟨384479, by rfl⟩ : syracuseStep 512639 = 768959) B768959
theorem B677051 : Blo 199806 677051 := bstep (se 1 (by rfl) ⟨507788, by rfl⟩ : syracuseStep 677051 = 1015577) B1015577
theorem B383143 : Blo 199806 383143 := bstep (se 1 (by rfl) ⟨287357, by rfl⟩ : syracuseStep 383143 = 574715) B574715
theorem B777311 : Blo 199806 777311 := bstep (se 1 (by rfl) ⟨582983, by rfl⟩ : syracuseStep 777311 = 1165967) B1165967
theorem B384335 : Blo 199806 384335 := bstep (se 1 (by rfl) ⟨288251, by rfl⟩ : syracuseStep 384335 = 576503) B576503
theorem B454121 : Blo 199806 454121 := bstep (se 2 (by rfl) ⟨170295, by rfl⟩ : syracuseStep 454121 = 340591) B340591
theorem B454625 : Blo 199806 454625 := bstep (se 2 (by rfl) ⟨170484, by rfl⟩ : syracuseStep 454625 = 340969) B340969
theorem B225391 : Blo 199806 225391 := bstep (se 1 (by rfl) ⟨169043, by rfl⟩ : syracuseStep 225391 = 338087) B338087
theorem B4354559 : Blo 199806 4354559 := bstep (se 1 (by rfl) ⟨3265919, by rfl⟩ : syracuseStep 4354559 = 6531839) B6531839
theorem B325385 : Blo 199806 325385 := bstep (se 2 (by rfl) ⟨122019, by rfl⟩ : syracuseStep 325385 = 244039) B244039
theorem B456551 : Blo 199806 456551 := bstep (se 1 (by rfl) ⟨342413, by rfl⟩ : syracuseStep 456551 = 684827) B684827
theorem B23754829 : Blo 199806 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B457595 : Blo 199806 457595 := bstep (se 1 (by rfl) ⟨343196, by rfl⟩ : syracuseStep 457595 = 686393) B686393
theorem B228415 : Blo 199806 228415 := bstep (se 1 (by rfl) ⟨171311, by rfl⟩ : syracuseStep 228415 = 342623) B342623
theorem B2590775 : Blo 199806 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B200871 : Blo 199806 200871 := bstep (se 1 (by rfl) ⟨150653, by rfl⟩ : syracuseStep 200871 = 301307) B301307
theorem B201191 : Blo 199806 201191 := bstep (se 1 (by rfl) ⟨150893, by rfl⟩ : syracuseStep 201191 = 301787) B301787
theorem B201575 : Blo 199806 201575 := bstep (se 1 (by rfl) ⟨151181, by rfl⟩ : syracuseStep 201575 = 302363) B302363
theorem B464059 : Blo 199806 464059 := bstep (se 1 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 464059 = 696089) B696089
theorem B201959 : Blo 199806 201959 := bstep (se 1 (by rfl) ⟨151469, by rfl⟩ : syracuseStep 201959 = 302939) B302939
theorem B300521 : Blo 199806 300521 := bstep (se 2 (by rfl) ⟨112695, by rfl⟩ : syracuseStep 300521 = 225391) B225391
theorem B302747 : Blo 199806 302747 := bstep (se 1 (by rfl) ⟨227060, by rfl⟩ : syracuseStep 302747 = 454121) B454121
theorem B303083 : Blo 199806 303083 := bstep (se 1 (by rfl) ⟨227312, by rfl⟩ : syracuseStep 303083 = 454625) B454625
theorem B304367 : Blo 199806 304367 := bstep (se 1 (by rfl) ⟨228275, by rfl⟩ : syracuseStep 304367 = 456551) B456551
theorem B304553 : Blo 199806 304553 := bstep (se 2 (by rfl) ⟨114207, by rfl⟩ : syracuseStep 304553 = 228415) B228415
theorem B305063 : Blo 199806 305063 := bstep (se 1 (by rfl) ⟨228797, by rfl⟩ : syracuseStep 305063 = 457595) B457595
theorem B1944161 : Blo 199806 1944161 := bstep (se 2 (by rfl) ⟨729060, by rfl⟩ : syracuseStep 1944161 = 1458121) B1458121
theorem B1126223 : Blo 199806 1126223 := bstep (se 1 (by rfl) ⟨844667, by rfl⟩ : syracuseStep 1126223 = 1689335) B1689335
theorem B341759 : Blo 199806 341759 := bstep (se 1 (by rfl) ⟨256319, by rfl⟩ : syracuseStep 341759 = 512639) B512639
theorem B31673105 : Blo 199806 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B510857 : Blo 199806 510857 := bstep (se 2 (by rfl) ⟨191571, by rfl⟩ : syracuseStep 510857 = 383143) B383143
theorem B2903039 : Blo 199806 2903039 := bstep (se 1 (by rfl) ⟨2177279, by rfl⟩ : syracuseStep 2903039 = 4354559) B4354559
theorem B380447 : Blo 199806 380447 := bstep (se 1 (by rfl) ⟨285335, by rfl⟩ : syracuseStep 380447 = 570671) B570671
theorem B216923 : Blo 199806 216923 := bstep (se 1 (by rfl) ⟨162692, by rfl⟩ : syracuseStep 216923 = 325385) B325385
theorem B31610897 : Blo 199806 31610897 := bstep (se 2 (by rfl) ⟨11854086, by rfl⟩ : syracuseStep 31610897 = 23708173) B23708173
theorem B3267533 : Blo 199806 3267533 := bstep (se 3 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 3267533 = 1225325) B1225325
theorem B941399 : Blo 199806 941399 := bstep (se 1 (by rfl) ⟨706049, by rfl⟩ : syracuseStep 941399 = 1412099) B1412099
theorem B451367 : Blo 199806 451367 := bstep (se 1 (by rfl) ⟨338525, by rfl⟩ : syracuseStep 451367 = 677051) B677051
theorem B518207 : Blo 199806 518207 := bstep (se 1 (by rfl) ⟨388655, by rfl⟩ : syracuseStep 518207 = 777311) B777311
theorem B256223 : Blo 199806 256223 := bstep (se 1 (by rfl) ⟨192167, by rfl⟩ : syracuseStep 256223 = 384335) B384335
theorem B226975 : Blo 199806 226975 := bstep (se 1 (by rfl) ⟨170231, by rfl⟩ : syracuseStep 226975 = 340463) B340463
theorem B8813063 : Blo 199806 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B720353 : Blo 199806 720353 := bstep (se 2 (by rfl) ⟨270132, by rfl⟩ : syracuseStep 720353 = 540265) B540265
theorem B1935359 : Blo 199806 1935359 := bstep (se 1 (by rfl) ⟨1451519, by rfl⟩ : syracuseStep 1935359 = 2903039) B2903039
theorem B200347 : Blo 199806 200347 := bstep (se 1 (by rfl) ⟨150260, by rfl⟩ : syracuseStep 200347 = 300521) B300521
theorem B21073931 : Blo 199806 21073931 := bstep (se 1 (by rfl) ⟨15805448, by rfl⟩ : syracuseStep 21073931 = 31610897) B31610897
theorem B627599 : Blo 199806 627599 := bstep (se 1 (by rfl) ⟨470699, by rfl⟩ : syracuseStep 627599 = 941399) B941399
theorem B201831 : Blo 199806 201831 := bstep (se 1 (by rfl) ⟨151373, by rfl⟩ : syracuseStep 201831 = 302747) B302747
theorem B202055 : Blo 199806 202055 := bstep (se 1 (by rfl) ⟨151541, by rfl⟩ : syracuseStep 202055 = 303083) B303083
theorem B300911 : Blo 199806 300911 := bstep (se 1 (by rfl) ⟨225683, by rfl⟩ : syracuseStep 300911 = 451367) B451367
theorem B202911 : Blo 199806 202911 := bstep (se 1 (by rfl) ⟨152183, by rfl⟩ : syracuseStep 202911 = 304367) B304367
theorem B203035 : Blo 199806 203035 := bstep (se 1 (by rfl) ⟨152276, by rfl⟩ : syracuseStep 203035 = 304553) B304553
theorem B203375 : Blo 199806 203375 := bstep (se 1 (by rfl) ⟨152531, by rfl⟩ : syracuseStep 203375 = 305063) B305063
theorem B23501501 : Blo 199806 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B302633 : Blo 199806 302633 := bstep (se 2 (by rfl) ⟨113487, by rfl⟩ : syracuseStep 302633 = 226975) B226975
theorem B5875375 : Blo 199806 5875375 := bstep (se 1 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 5875375 = 8813063) B8813063
theorem B21115403 : Blo 199806 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B340571 : Blo 199806 340571 := bstep (se 1 (by rfl) ⟨255428, by rfl⟩ : syracuseStep 340571 = 510857) B510857
theorem B2178355 : Blo 199806 2178355 := bstep (se 1 (by rfl) ⟨1633766, by rfl⟩ : syracuseStep 2178355 = 3267533) B3267533
theorem B1296107 : Blo 199806 1296107 := bstep (se 1 (by rfl) ⟨972080, by rfl⟩ : syracuseStep 1296107 = 1944161) B1944161
theorem B2313845 : Blo 199806 2313845 := bstep (se 5 (by rfl) ⟨108461, by rfl⟩ : syracuseStep 2313845 = 216923) B216923
theorem B480235 : Blo 199806 480235 := bstep (se 1 (by rfl) ⟨360176, by rfl⟩ : syracuseStep 480235 = 720353) B720353
theorem B5527541 : Blo 199806 5527541 := bstep (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) B518207
theorem B1727183 : Blo 199806 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B253631 : Blo 199806 253631 := bstep (se 1 (by rfl) ⟨190223, by rfl⟩ : syracuseStep 253631 = 380447) B380447
theorem B683261 : Blo 199806 683261 := bstep (se 3 (by rfl) ⟨128111, by rfl⟩ : syracuseStep 683261 = 256223) B256223
theorem B618745 : Blo 199806 618745 := bstep (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) B464059
theorem B750815 : Blo 199806 750815 := bstep (se 1 (by rfl) ⟨563111, by rfl⟩ : syracuseStep 750815 = 1126223) B1126223
theorem B227839 : Blo 199806 227839 := bstep (se 1 (by rfl) ⟨170879, by rfl⟩ : syracuseStep 227839 = 341759) B341759
theorem B7833833 : Blo 199806 7833833 := bstep (se 2 (by rfl) ⟨2937687, by rfl⟩ : syracuseStep 7833833 = 5875375) B5875375
theorem B1673597 : Blo 199806 1673597 := bstep (se 3 (by rfl) ⟨313799, by rfl⟩ : syracuseStep 1673597 = 627599) B627599
theorem B1542563 : Blo 199806 1542563 := bstep (se 1 (by rfl) ⟨1156922, by rfl⟩ : syracuseStep 1542563 = 2313845) B2313845
theorem B200607 : Blo 199806 200607 := bstep (se 1 (by rfl) ⟨150455, by rfl⟩ : syracuseStep 200607 = 300911) B300911
theorem B15667667 : Blo 199806 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B1151455 : Blo 199806 1151455 := bstep (se 1 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 1151455 = 1727183) B1727183
theorem B201755 : Blo 199806 201755 := bstep (se 1 (by rfl) ⟨151316, by rfl⟩ : syracuseStep 201755 = 302633) B302633
theorem B824993 : Blo 199806 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B303785 : Blo 199806 303785 := bstep (se 2 (by rfl) ⟨113919, by rfl⟩ : syracuseStep 303785 = 227839) B227839
theorem B500543 : Blo 199806 500543 := bstep (se 1 (by rfl) ⟨375407, by rfl⟩ : syracuseStep 500543 = 750815) B750815
theorem B864071 : Blo 199806 864071 := bstep (se 1 (by rfl) ⟨648053, by rfl⟩ : syracuseStep 864071 = 1296107) B1296107
theorem B1290239 : Blo 199806 1290239 := bstep (se 1 (by rfl) ⟨967679, by rfl⟩ : syracuseStep 1290239 = 1935359) B1935359
theorem B3685027 : Blo 199806 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B640313 : Blo 199806 640313 := bstep (se 2 (by rfl) ⟨240117, by rfl⟩ : syracuseStep 640313 = 480235) B480235
theorem B14076935 : Blo 199806 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B2904473 : Blo 199806 2904473 := bstep (se 2 (by rfl) ⟨1089177, by rfl⟩ : syracuseStep 2904473 = 2178355) B2178355
theorem B676349 : Blo 199806 676349 := bstep (se 3 (by rfl) ⟨126815, by rfl⟩ : syracuseStep 676349 = 253631) B253631
theorem B14049287 : Blo 199806 14049287 := bstep (se 1 (by rfl) ⟨10536965, by rfl⟩ : syracuseStep 14049287 = 21073931) B21073931
theorem B455507 : Blo 199806 455507 := bstep (se 1 (by rfl) ⟨341630, by rfl⟩ : syracuseStep 455507 = 683261) B683261
theorem B227047 : Blo 199806 227047 := bstep (se 1 (by rfl) ⟨170285, by rfl⟩ : syracuseStep 227047 = 340571) B340571
theorem B426875 : Blo 199806 426875 := bstep (se 1 (by rfl) ⟨320156, by rfl⟩ : syracuseStep 426875 = 640313) B640313
theorem B1115731 : Blo 199806 1115731 := bstep (se 1 (by rfl) ⟨836798, by rfl⟩ : syracuseStep 1115731 = 1673597) B1673597
theorem B1936315 : Blo 199806 1936315 := bstep (se 1 (by rfl) ⟨1452236, by rfl⟩ : syracuseStep 1936315 = 2904473) B2904473
theorem B202523 : Blo 199806 202523 := bstep (se 1 (by rfl) ⟨151892, by rfl⟩ : syracuseStep 202523 = 303785) B303785
theorem B333695 : Blo 199806 333695 := bstep (se 1 (by rfl) ⟨250271, by rfl⟩ : syracuseStep 333695 = 500543) B500543
theorem B302729 : Blo 199806 302729 := bstep (se 2 (by rfl) ⟨113523, by rfl⟩ : syracuseStep 302729 = 227047) B227047
theorem B860159 : Blo 199806 860159 := bstep (se 1 (by rfl) ⟨645119, by rfl⟩ : syracuseStep 860159 = 1290239) B1290239
theorem B303671 : Blo 199806 303671 := bstep (se 1 (by rfl) ⟨227753, by rfl⟩ : syracuseStep 303671 = 455507) B455507
theorem B5222555 : Blo 199806 5222555 := bstep (se 1 (by rfl) ⟨3916916, by rfl⟩ : syracuseStep 5222555 = 7833833) B7833833
theorem B1028375 : Blo 199806 1028375 := bstep (se 1 (by rfl) ⟨771281, by rfl⟩ : syracuseStep 1028375 = 1542563) B1542563
theorem B9384623 : Blo 199806 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B576047 : Blo 199806 576047 := bstep (se 1 (by rfl) ⟨432035, by rfl⟩ : syracuseStep 576047 = 864071) B864071
theorem B10445111 : Blo 199806 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B450899 : Blo 199806 450899 := bstep (se 1 (by rfl) ⟨338174, by rfl⟩ : syracuseStep 450899 = 676349) B676349
theorem B549995 : Blo 199806 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B9366191 : Blo 199806 9366191 := bstep (se 1 (by rfl) ⟨7024643, by rfl⟩ : syracuseStep 9366191 = 14049287) B14049287
theorem B1535273 : Blo 199806 1535273 := bstep (se 2 (by rfl) ⟨575727, by rfl⟩ : syracuseStep 1535273 = 1151455) B1151455
theorem B4913369 : Blo 199806 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B5866613 : Blo 199806 5866613 := bstep (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) B549995
theorem B201819 : Blo 199806 201819 := bstep (se 1 (by rfl) ⟨151364, by rfl⟩ : syracuseStep 201819 = 302729) B302729
theorem B300599 : Blo 199806 300599 := bstep (se 1 (by rfl) ⟨225449, by rfl⟩ : syracuseStep 300599 = 450899) B450899
theorem B202447 : Blo 199806 202447 := bstep (se 1 (by rfl) ⟨151835, by rfl⟩ : syracuseStep 202447 = 303671) B303671
theorem B1023515 : Blo 199806 1023515 := bstep (se 1 (by rfl) ⟨767636, by rfl⟩ : syracuseStep 1023515 = 1535273) B1535273
theorem B3481703 : Blo 199806 3481703 := bstep (se 1 (by rfl) ⟨2611277, by rfl⟩ : syracuseStep 3481703 = 5222555) B5222555
theorem B1487641 : Blo 199806 1487641 := bstep (se 2 (by rfl) ⟨557865, by rfl⟩ : syracuseStep 1487641 = 1115731) B1115731
theorem B573439 : Blo 199806 573439 := bstep (se 1 (by rfl) ⟨430079, by rfl⟩ : syracuseStep 573439 = 860159) B860159
theorem B6963407 : Blo 199806 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B6244127 : Blo 199806 6244127 := bstep (se 1 (by rfl) ⟨4683095, by rfl⟩ : syracuseStep 6244127 = 9366191) B9366191
theorem B384031 : Blo 199806 384031 := bstep (se 1 (by rfl) ⟨288023, by rfl⟩ : syracuseStep 384031 = 576047) B576047
theorem B1138333 : Blo 199806 1138333 := bstep (se 3 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 1138333 = 426875) B426875
theorem B2581753 : Blo 199806 2581753 := bstep (se 2 (by rfl) ⟨968157, by rfl⟩ : syracuseStep 2581753 = 1936315) B1936315
theorem B222463 : Blo 199806 222463 := bstep (se 1 (by rfl) ⟨166847, by rfl⟩ : syracuseStep 222463 = 333695) B333695
theorem B685583 : Blo 199806 685583 := bstep (se 1 (by rfl) ⟨514187, by rfl⟩ : syracuseStep 685583 = 1028375) B1028375
theorem B6256415 : Blo 199806 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B3275579 : Blo 199806 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B4162751 : Blo 199806 4162751 := bstep (se 1 (by rfl) ⟨3122063, by rfl⟩ : syracuseStep 4162751 = 6244127) B6244127
theorem B3442337 : Blo 199806 3442337 := bstep (se 2 (by rfl) ⟨1290876, by rfl⟩ : syracuseStep 3442337 = 2581753) B2581753
theorem B296617 : Blo 199806 296617 := bstep (se 2 (by rfl) ⟨111231, by rfl⟩ : syracuseStep 296617 = 222463) B222463
theorem B200399 : Blo 199806 200399 := bstep (se 1 (by rfl) ⟨150299, by rfl⟩ : syracuseStep 200399 = 300599) B300599
theorem B4170943 : Blo 199806 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B1517777 : Blo 199806 1517777 := bstep (se 2 (by rfl) ⟨569166, by rfl⟩ : syracuseStep 1517777 = 1138333) B1138333
theorem B764585 : Blo 199806 764585 := bstep (se 2 (by rfl) ⟨286719, by rfl⟩ : syracuseStep 764585 = 573439) B573439
theorem B3911075 : Blo 199806 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B1983521 : Blo 199806 1983521 := bstep (se 2 (by rfl) ⟨743820, by rfl⟩ : syracuseStep 1983521 = 1487641) B1487641
theorem B8734877 : Blo 199806 8734877 := bstep (se 3 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 8734877 = 3275579) B3275579
theorem B512041 : Blo 199806 512041 := bstep (se 2 (by rfl) ⟨192015, by rfl⟩ : syracuseStep 512041 = 384031) B384031
theorem B4642271 : Blo 199806 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B682343 : Blo 199806 682343 := bstep (se 1 (by rfl) ⟨511757, by rfl⟩ : syracuseStep 682343 = 1023515) B1023515
theorem B2321135 : Blo 199806 2321135 := bstep (se 1 (by rfl) ⟨1740851, by rfl⟩ : syracuseStep 2321135 = 3481703) B3481703
theorem B457055 : Blo 199806 457055 := bstep (se 1 (by rfl) ⟨342791, by rfl⟩ : syracuseStep 457055 = 685583) B685583
theorem B2294891 : Blo 199806 2294891 := bstep (se 1 (by rfl) ⟨1721168, by rfl⟩ : syracuseStep 2294891 = 3442337) B3442337
theorem B395489 : Blo 199806 395489 := bstep (se 2 (by rfl) ⟨148308, by rfl⟩ : syracuseStep 395489 = 296617) B296617
theorem B1547423 : Blo 199806 1547423 := bstep (se 1 (by rfl) ⟨1160567, by rfl⟩ : syracuseStep 1547423 = 2321135) B2321135
theorem B304703 : Blo 199806 304703 := bstep (se 1 (by rfl) ⟨228527, by rfl⟩ : syracuseStep 304703 = 457055) B457055
theorem B1322347 : Blo 199806 1322347 := bstep (se 1 (by rfl) ⟨991760, by rfl⟩ : syracuseStep 1322347 = 1983521) B1983521
theorem B3094847 : Blo 199806 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B509723 : Blo 199806 509723 := bstep (se 1 (by rfl) ⟨382292, by rfl⟩ : syracuseStep 509723 = 764585) B764585
theorem B2607383 : Blo 199806 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B2775167 : Blo 199806 2775167 := bstep (se 1 (by rfl) ⟨2081375, by rfl⟩ : syracuseStep 2775167 = 4162751) B4162751
theorem B5823251 : Blo 199806 5823251 := bstep (se 1 (by rfl) ⟨4367438, by rfl⟩ : syracuseStep 5823251 = 8734877) B8734877
theorem B5561257 : Blo 199806 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B682721 : Blo 199806 682721 := bstep (se 2 (by rfl) ⟨256020, by rfl⟩ : syracuseStep 682721 = 512041) B512041
theorem B1011851 : Blo 199806 1011851 := bstep (se 1 (by rfl) ⟨758888, by rfl⟩ : syracuseStep 1011851 = 1517777) B1517777
theorem B454895 : Blo 199806 454895 := bstep (se 1 (by rfl) ⟨341171, by rfl⟩ : syracuseStep 454895 = 682343) B682343
theorem B1738255 : Blo 199806 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B1054637 : Blo 199806 1054637 := bstep (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) B395489
theorem B203135 : Blo 199806 203135 := bstep (se 1 (by rfl) ⟨152351, by rfl⟩ : syracuseStep 203135 = 304703) B304703
theorem B303263 : Blo 199806 303263 := bstep (se 1 (by rfl) ⟨227447, by rfl⟩ : syracuseStep 303263 = 454895) B454895
theorem B7415009 : Blo 199806 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B339815 : Blo 199806 339815 := bstep (se 1 (by rfl) ⟨254861, by rfl⟩ : syracuseStep 339815 = 509723) B509723
theorem B1850111 : Blo 199806 1850111 := bstep (se 1 (by rfl) ⟨1387583, by rfl⟩ : syracuseStep 1850111 = 2775167) B2775167
theorem B3882167 : Blo 199806 3882167 := bstep (se 1 (by rfl) ⟨2911625, by rfl⟩ : syracuseStep 3882167 = 5823251) B5823251
theorem B1031615 : Blo 199806 1031615 := bstep (se 1 (by rfl) ⟨773711, by rfl⟩ : syracuseStep 1031615 = 1547423) B1547423
theorem B674567 : Blo 199806 674567 := bstep (se 1 (by rfl) ⟨505925, by rfl⟩ : syracuseStep 674567 = 1011851) B1011851
theorem B1529927 : Blo 199806 1529927 := bstep (se 1 (by rfl) ⟨1147445, by rfl⟩ : syracuseStep 1529927 = 2294891) B2294891
theorem B1763129 : Blo 199806 1763129 := bstep (se 2 (by rfl) ⟨661173, by rfl⟩ : syracuseStep 1763129 = 1322347) B1322347
theorem B455147 : Blo 199806 455147 := bstep (se 1 (by rfl) ⟨341360, by rfl⟩ : syracuseStep 455147 = 682721) B682721
theorem B2063231 : Blo 199806 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B1019951 : Blo 199806 1019951 := bstep (se 1 (by rfl) ⟨764963, by rfl⟩ : syracuseStep 1019951 = 1529927) B1529927
theorem B202175 : Blo 199806 202175 := bstep (se 1 (by rfl) ⟨151631, by rfl⟩ : syracuseStep 202175 = 303263) B303263
theorem B303431 : Blo 199806 303431 := bstep (se 1 (by rfl) ⟨227573, by rfl⟩ : syracuseStep 303431 = 455147) B455147
theorem B703091 : Blo 199806 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B1233407 : Blo 199806 1233407 := bstep (se 1 (by rfl) ⟨925055, by rfl⟩ : syracuseStep 1233407 = 1850111) B1850111
theorem B449711 : Blo 199806 449711 := bstep (se 1 (by rfl) ⟨337283, by rfl⟩ : syracuseStep 449711 = 674567) B674567
theorem B2317673 : Blo 199806 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B4943339 : Blo 199806 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B1175419 : Blo 199806 1175419 := bstep (se 1 (by rfl) ⟨881564, by rfl⟩ : syracuseStep 1175419 = 1763129) B1763129
theorem B226543 : Blo 199806 226543 := bstep (se 1 (by rfl) ⟨169907, by rfl⟩ : syracuseStep 226543 = 339815) B339815
theorem B1375487 : Blo 199806 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B2588111 : Blo 199806 2588111 := bstep (se 1 (by rfl) ⟨1941083, by rfl⟩ : syracuseStep 2588111 = 3882167) B3882167
theorem B687743 : Blo 199806 687743 := bstep (se 1 (by rfl) ⟨515807, by rfl⟩ : syracuseStep 687743 = 1031615) B1031615
theorem B822271 : Blo 199806 822271 := bstep (se 1 (by rfl) ⟨616703, by rfl⟩ : syracuseStep 822271 = 1233407) B1233407
theorem B299807 : Blo 199806 299807 := bstep (se 1 (by rfl) ⟨224855, by rfl⟩ : syracuseStep 299807 = 449711) B449711
theorem B202287 : Blo 199806 202287 := bstep (se 1 (by rfl) ⟨151715, by rfl⟩ : syracuseStep 202287 = 303431) B303431
theorem B1874909 : Blo 199806 1874909 := bstep (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) B703091
theorem B302057 : Blo 199806 302057 := bstep (se 2 (by rfl) ⟨113271, by rfl⟩ : syracuseStep 302057 = 226543) B226543
theorem B3295559 : Blo 199806 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B6180461 : Blo 199806 6180461 := bstep (se 3 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 6180461 = 2317673) B2317673
theorem B1725407 : Blo 199806 1725407 := bstep (se 1 (by rfl) ⟨1294055, by rfl⟩ : syracuseStep 1725407 = 2588111) B2588111
theorem B679967 : Blo 199806 679967 := bstep (se 1 (by rfl) ⟨509975, by rfl⟩ : syracuseStep 679967 = 1019951) B1019951
theorem B1567225 : Blo 199806 1567225 := bstep (se 2 (by rfl) ⟨587709, by rfl⟩ : syracuseStep 1567225 = 1175419) B1175419
theorem B916991 : Blo 199806 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B458495 : Blo 199806 458495 := bstep (se 1 (by rfl) ⟨343871, by rfl⟩ : syracuseStep 458495 = 687743) B687743
theorem B2197039 : Blo 199806 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B199871 : Blo 199806 199871 := bstep (se 1 (by rfl) ⟨149903, by rfl⟩ : syracuseStep 199871 = 299807) B299807
theorem B1150271 : Blo 199806 1150271 := bstep (se 1 (by rfl) ⟨862703, by rfl⟩ : syracuseStep 1150271 = 1725407) B1725407
theorem B1249939 : Blo 199806 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B201371 : Blo 199806 201371 := bstep (se 1 (by rfl) ⟨151028, by rfl⟩ : syracuseStep 201371 = 302057) B302057
theorem B305663 : Blo 199806 305663 := bstep (se 1 (by rfl) ⟨229247, by rfl⟩ : syracuseStep 305663 = 458495) B458495
theorem B1096361 : Blo 199806 1096361 := bstep (se 2 (by rfl) ⟨411135, by rfl⟩ : syracuseStep 1096361 = 822271) B822271
theorem B611327 : Blo 199806 611327 := bstep (se 1 (by rfl) ⟨458495, by rfl⟩ : syracuseStep 611327 = 916991) B916991
theorem B4120307 : Blo 199806 4120307 := bstep (se 1 (by rfl) ⟨3090230, by rfl⟩ : syracuseStep 4120307 = 6180461) B6180461
theorem B2089633 : Blo 199806 2089633 := bstep (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) B1567225
theorem B453311 : Blo 199806 453311 := bstep (se 1 (by rfl) ⟨339983, by rfl⟩ : syracuseStep 453311 = 679967) B679967
theorem B2786177 : Blo 199806 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B203775 : Blo 199806 203775 := bstep (se 1 (by rfl) ⟨152831, by rfl⟩ : syracuseStep 203775 = 305663) B305663
theorem B302207 : Blo 199806 302207 := bstep (se 1 (by rfl) ⟨226655, by rfl⟩ : syracuseStep 302207 = 453311) B453311
theorem B730907 : Blo 199806 730907 := bstep (se 1 (by rfl) ⟨548180, by rfl⟩ : syracuseStep 730907 = 1096361) B1096361
theorem B2929385 : Blo 199806 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B766847 : Blo 199806 766847 := bstep (se 1 (by rfl) ⟨575135, by rfl⟩ : syracuseStep 766847 = 1150271) B1150271
theorem B1630205 : Blo 199806 1630205 := bstep (se 3 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 1630205 = 611327) B611327
theorem B2746871 : Blo 199806 2746871 := bstep (se 1 (by rfl) ⟨2060153, by rfl⟩ : syracuseStep 2746871 = 4120307) B4120307
theorem B1666585 : Blo 199806 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B201471 : Blo 199806 201471 := bstep (se 1 (by rfl) ⟨151103, by rfl⟩ : syracuseStep 201471 = 302207) B302207
theorem B1086803 : Blo 199806 1086803 := bstep (se 1 (by rfl) ⟨815102, by rfl⟩ : syracuseStep 1086803 = 1630205) B1630205
theorem B1952923 : Blo 199806 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B511231 : Blo 199806 511231 := bstep (se 1 (by rfl) ⟨383423, by rfl⟩ : syracuseStep 511231 = 766847) B766847
theorem B1857451 : Blo 199806 1857451 := bstep (se 1 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 1857451 = 2786177) B2786177
theorem B2222113 : Blo 199806 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B487271 : Blo 199806 487271 := bstep (se 1 (by rfl) ⟨365453, by rfl⟩ : syracuseStep 487271 = 730907) B730907
theorem B1831247 : Blo 199806 1831247 := bstep (se 1 (by rfl) ⟨1373435, by rfl⟩ : syracuseStep 1831247 = 2746871) B2746871
theorem B724535 : Blo 199806 724535 := bstep (se 1 (by rfl) ⟨543401, by rfl⟩ : syracuseStep 724535 = 1086803) B1086803
theorem B1220831 : Blo 199806 1220831 := bstep (se 1 (by rfl) ⟨915623, by rfl⟩ : syracuseStep 1220831 = 1831247) B1831247
theorem B2962817 : Blo 199806 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B2603897 : Blo 199806 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B2476601 : Blo 199806 2476601 := bstep (se 2 (by rfl) ⟨928725, by rfl⟩ : syracuseStep 2476601 = 1857451) B1857451
theorem B681641 : Blo 199806 681641 := bstep (se 2 (by rfl) ⟨255615, by rfl⟩ : syracuseStep 681641 = 511231) B511231
theorem B324847 : Blo 199806 324847 := bstep (se 1 (by rfl) ⟨243635, by rfl⟩ : syracuseStep 324847 = 487271) B487271
theorem B433129 : Blo 199806 433129 := bstep (se 2 (by rfl) ⟨162423, by rfl⟩ : syracuseStep 433129 = 324847) B324847
theorem B1975211 : Blo 199806 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B1651067 : Blo 199806 1651067 := bstep (se 1 (by rfl) ⟨1238300, by rfl⟩ : syracuseStep 1651067 = 2476601) B2476601
theorem B483023 : Blo 199806 483023 := bstep (se 1 (by rfl) ⟨362267, by rfl⟩ : syracuseStep 483023 = 724535) B724535
theorem B813887 : Blo 199806 813887 := bstep (se 1 (by rfl) ⟨610415, by rfl⟩ : syracuseStep 813887 = 1220831) B1220831
theorem B454427 : Blo 199806 454427 := bstep (se 1 (by rfl) ⟨340820, by rfl⟩ : syracuseStep 454427 = 681641) B681641
theorem B1735931 : Blo 199806 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B1316807 : Blo 199806 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B302951 : Blo 199806 302951 := bstep (se 1 (by rfl) ⟨227213, by rfl⟩ : syracuseStep 302951 = 454427) B454427
theorem B1288061 : Blo 199806 1288061 := bstep (se 3 (by rfl) ⟨241511, by rfl⟩ : syracuseStep 1288061 = 483023) B483023
theorem B1157287 : Blo 199806 1157287 := bstep (se 1 (by rfl) ⟨867965, by rfl⟩ : syracuseStep 1157287 = 1735931) B1735931
theorem B542591 : Blo 199806 542591 := bstep (se 1 (by rfl) ⟨406943, by rfl⟩ : syracuseStep 542591 = 813887) B813887
theorem B1100711 : Blo 199806 1100711 := bstep (se 1 (by rfl) ⟨825533, by rfl⟩ : syracuseStep 1100711 = 1651067) B1651067
theorem B577505 : Blo 199806 577505 := bstep (se 2 (by rfl) ⟨216564, by rfl⟩ : syracuseStep 577505 = 433129) B433129
theorem B361727 : Blo 199806 361727 := bstep (se 1 (by rfl) ⟨271295, by rfl⟩ : syracuseStep 361727 = 542591) B542591
theorem B1543049 : Blo 199806 1543049 := bstep (se 2 (by rfl) ⟨578643, by rfl⟩ : syracuseStep 1543049 = 1157287) B1157287
theorem B201967 : Blo 199806 201967 := bstep (se 1 (by rfl) ⟨151475, by rfl⟩ : syracuseStep 201967 = 302951) B302951
theorem B858707 : Blo 199806 858707 := bstep (se 1 (by rfl) ⟨644030, by rfl⟩ : syracuseStep 858707 = 1288061) B1288061
theorem B733807 : Blo 199806 733807 := bstep (se 1 (by rfl) ⟨550355, by rfl⟩ : syracuseStep 733807 = 1100711) B1100711
theorem B385003 : Blo 199806 385003 := bstep (se 1 (by rfl) ⟨288752, by rfl⟩ : syracuseStep 385003 = 577505) B577505
theorem B877871 : Blo 199806 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B241151 : Blo 199806 241151 := bstep (se 1 (by rfl) ⟨180863, by rfl⟩ : syracuseStep 241151 = 361727) B361727
theorem B1028699 : Blo 199806 1028699 := bstep (se 1 (by rfl) ⟨771524, by rfl⟩ : syracuseStep 1028699 = 1543049) B1543049
theorem B572471 : Blo 199806 572471 := bstep (se 1 (by rfl) ⟨429353, by rfl⟩ : syracuseStep 572471 = 858707) B858707
theorem B513337 : Blo 199806 513337 := bstep (se 2 (by rfl) ⟨192501, by rfl⟩ : syracuseStep 513337 = 385003) B385003
theorem B978409 : Blo 199806 978409 := bstep (se 2 (by rfl) ⟨366903, by rfl⟩ : syracuseStep 978409 = 733807) B733807
theorem B585247 : Blo 199806 585247 := bstep (se 1 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 585247 = 877871) B877871
theorem B5218181 : Blo 199806 5218181 := bstep (se 4 (by rfl) ⟨489204, by rfl⟩ : syracuseStep 5218181 = 978409) B978409
theorem B643069 : Blo 199806 643069 := bstep (se 3 (by rfl) ⟨120575, by rfl⟩ : syracuseStep 643069 = 241151) B241151
theorem B381647 : Blo 199806 381647 := bstep (se 1 (by rfl) ⟨286235, by rfl⟩ : syracuseStep 381647 = 572471) B572471
theorem B780329 : Blo 199806 780329 := bstep (se 2 (by rfl) ⟨292623, by rfl⟩ : syracuseStep 780329 = 585247) B585247
theorem B684449 : Blo 199806 684449 := bstep (se 2 (by rfl) ⟨256668, by rfl⟩ : syracuseStep 684449 = 513337) B513337
theorem B685799 : Blo 199806 685799 := bstep (se 1 (by rfl) ⟨514349, by rfl⟩ : syracuseStep 685799 = 1028699) B1028699
theorem B3478787 : Blo 199806 3478787 := bstep (se 1 (by rfl) ⟨2609090, by rfl⟩ : syracuseStep 3478787 = 5218181) B5218181
theorem B857425 : Blo 199806 857425 := bstep (se 2 (by rfl) ⟨321534, by rfl⟩ : syracuseStep 857425 = 643069) B643069
theorem B254431 : Blo 199806 254431 := bstep (se 1 (by rfl) ⟨190823, by rfl⟩ : syracuseStep 254431 = 381647) B381647
theorem B520219 : Blo 199806 520219 := bstep (se 1 (by rfl) ⟨390164, by rfl⟩ : syracuseStep 520219 = 780329) B780329
theorem B456299 : Blo 199806 456299 := bstep (se 1 (by rfl) ⟨342224, by rfl⟩ : syracuseStep 456299 = 684449) B684449
theorem B457199 : Blo 199806 457199 := bstep (se 1 (by rfl) ⟨342899, by rfl⟩ : syracuseStep 457199 = 685799) B685799
theorem B693625 : Blo 199806 693625 := bstep (se 2 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 693625 = 520219) B520219
theorem B304199 : Blo 199806 304199 := bstep (se 1 (by rfl) ⟨228149, by rfl⟩ : syracuseStep 304199 = 456299) B456299
theorem B304799 : Blo 199806 304799 := bstep (se 1 (by rfl) ⟨228599, by rfl⟩ : syracuseStep 304799 = 457199) B457199
theorem B339241 : Blo 199806 339241 := bstep (se 2 (by rfl) ⟨127215, by rfl⟩ : syracuseStep 339241 = 254431) B254431
theorem B2319191 : Blo 199806 2319191 := bstep (se 1 (by rfl) ⟨1739393, by rfl⟩ : syracuseStep 2319191 = 3478787) B3478787
theorem B1143233 : Blo 199806 1143233 := bstep (se 2 (by rfl) ⟨428712, by rfl⟩ : syracuseStep 1143233 = 857425) B857425
theorem B1546127 : Blo 199806 1546127 := bstep (se 1 (by rfl) ⟨1159595, by rfl⟩ : syracuseStep 1546127 = 2319191) B2319191
theorem B202799 : Blo 199806 202799 := bstep (se 1 (by rfl) ⟨152099, by rfl⟩ : syracuseStep 202799 = 304199) B304199
theorem B203199 : Blo 199806 203199 := bstep (se 1 (by rfl) ⟨152399, by rfl⟩ : syracuseStep 203199 = 304799) B304799
theorem B924833 : Blo 199806 924833 := bstep (se 2 (by rfl) ⟨346812, by rfl⟩ : syracuseStep 924833 = 693625) B693625
theorem B762155 : Blo 199806 762155 := bstep (se 1 (by rfl) ⟨571616, by rfl⟩ : syracuseStep 762155 = 1143233) B1143233
theorem B452321 : Blo 199806 452321 := bstep (se 2 (by rfl) ⟨169620, by rfl⟩ : syracuseStep 452321 = 339241) B339241
theorem B301547 : Blo 199806 301547 := bstep (se 1 (by rfl) ⟨226160, by rfl⟩ : syracuseStep 301547 = 452321) B452321
theorem B1030751 : Blo 199806 1030751 := bstep (se 1 (by rfl) ⟨773063, by rfl⟩ : syracuseStep 1030751 = 1546127) B1546127
theorem B508103 : Blo 199806 508103 := bstep (se 1 (by rfl) ⟨381077, by rfl⟩ : syracuseStep 508103 = 762155) B762155
theorem B616555 : Blo 199806 616555 := bstep (se 1 (by rfl) ⟨462416, by rfl⟩ : syracuseStep 616555 = 924833) B924833
theorem B822073 : Blo 199806 822073 := bstep (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) B616555
theorem B201031 : Blo 199806 201031 := bstep (se 1 (by rfl) ⟨150773, by rfl⟩ : syracuseStep 201031 = 301547) B301547
theorem B338735 : Blo 199806 338735 := bstep (se 1 (by rfl) ⟨254051, by rfl⟩ : syracuseStep 338735 = 508103) B508103
theorem B687167 : Blo 199806 687167 := bstep (se 1 (by rfl) ⟨515375, by rfl⟩ : syracuseStep 687167 = 1030751) B1030751
theorem B1096097 : Blo 199806 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B225823 : Blo 199806 225823 := bstep (se 1 (by rfl) ⟨169367, by rfl⟩ : syracuseStep 225823 = 338735) B338735
theorem B458111 : Blo 199806 458111 := bstep (se 1 (by rfl) ⟨343583, by rfl⟩ : syracuseStep 458111 = 687167) B687167
theorem B301097 : Blo 199806 301097 := bstep (se 2 (by rfl) ⟨112911, by rfl⟩ : syracuseStep 301097 = 225823) B225823
theorem B305407 : Blo 199806 305407 := bstep (se 1 (by rfl) ⟨229055, by rfl⟩ : syracuseStep 305407 = 458111) B458111
theorem B11691701 : Blo 199806 11691701 := bstep (se 5 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 11691701 = 1096097) B1096097
theorem B200731 : Blo 199806 200731 := bstep (se 1 (by rfl) ⟨150548, by rfl⟩ : syracuseStep 200731 = 301097) B301097
theorem B1628837 : Blo 199806 1628837 := bstep (se 4 (by rfl) ⟨152703, by rfl⟩ : syracuseStep 1628837 = 305407) B305407
theorem B7794467 : Blo 199806 7794467 := bstep (se 1 (by rfl) ⟨5845850, by rfl⟩ : syracuseStep 7794467 = 11691701) B11691701
theorem B1085891 : Blo 199806 1085891 := bstep (se 1 (by rfl) ⟨814418, by rfl⟩ : syracuseStep 1085891 = 1628837) B1628837
theorem B5196311 : Blo 199806 5196311 := bstep (se 1 (by rfl) ⟨3897233, by rfl⟩ : syracuseStep 5196311 = 7794467) B7794467
theorem B2895709 : Blo 199806 2895709 := bstep (se 3 (by rfl) ⟨542945, by rfl⟩ : syracuseStep 2895709 = 1085891) B1085891
theorem B3464207 : Blo 199806 3464207 := bstep (se 1 (by rfl) ⟨2598155, by rfl⟩ : syracuseStep 3464207 = 5196311) B5196311
theorem B2309471 : Blo 199806 2309471 := bstep (se 1 (by rfl) ⟨1732103, by rfl⟩ : syracuseStep 2309471 = 3464207) B3464207
theorem B3860945 : Blo 199806 3860945 := bstep (se 2 (by rfl) ⟨1447854, by rfl⟩ : syracuseStep 3860945 = 2895709) B2895709
theorem B2573963 : Blo 199806 2573963 := bstep (se 1 (by rfl) ⟨1930472, by rfl⟩ : syracuseStep 2573963 = 3860945) B3860945
theorem B1539647 : Blo 199806 1539647 := bstep (se 1 (by rfl) ⟨1154735, by rfl⟩ : syracuseStep 1539647 = 2309471) B2309471
theorem B1026431 : Blo 199806 1026431 := bstep (se 1 (by rfl) ⟨769823, by rfl⟩ : syracuseStep 1026431 = 1539647) B1539647
theorem B1715975 : Blo 199806 1715975 := bstep (se 1 (by rfl) ⟨1286981, by rfl⟩ : syracuseStep 1715975 = 2573963) B2573963
theorem B684287 : Blo 199806 684287 := bstep (se 1 (by rfl) ⟨513215, by rfl⟩ : syracuseStep 684287 = 1026431) B1026431
theorem B1143983 : Blo 199806 1143983 := bstep (se 1 (by rfl) ⟨857987, by rfl⟩ : syracuseStep 1143983 = 1715975) B1715975
theorem B762655 : Blo 199806 762655 := bstep (se 1 (by rfl) ⟨571991, by rfl⟩ : syracuseStep 762655 = 1143983) B1143983
theorem B456191 : Blo 199806 456191 := bstep (se 1 (by rfl) ⟨342143, by rfl⟩ : syracuseStep 456191 = 684287) B684287
theorem B1016873 : Blo 199806 1016873 := bstep (se 2 (by rfl) ⟨381327, by rfl⟩ : syracuseStep 1016873 = 762655) B762655
theorem B304127 : Blo 199806 304127 := bstep (se 1 (by rfl) ⟨228095, by rfl⟩ : syracuseStep 304127 = 456191) B456191
theorem B202751 : Blo 199806 202751 := bstep (se 1 (by rfl) ⟨152063, by rfl⟩ : syracuseStep 202751 = 304127) B304127
theorem B677915 : Blo 199806 677915 := bstep (se 1 (by rfl) ⟨508436, by rfl⟩ : syracuseStep 677915 = 1016873) B1016873
theorem B451943 : Blo 199806 451943 := bstep (se 1 (by rfl) ⟨338957, by rfl⟩ : syracuseStep 451943 = 677915) B677915
theorem B301295 : Blo 199806 301295 := bstep (se 1 (by rfl) ⟨225971, by rfl⟩ : syracuseStep 301295 = 451943) B451943
theorem B200863 : Blo 199806 200863 := bstep (se 1 (by rfl) ⟨150647, by rfl⟩ : syracuseStep 200863 = 301295) B301295

theorem C0 (j : ℕ) (h1 : 49951 ≤ j) (h2 : j ≤ 50650) : Blo 199806 (4 * j + 3) := by
  interval_cases j
  · exact B199807
  · exact B199811
  · exact B199815
  · exact B199819
  · exact B199823
  · exact B199827
  · exact B199831
  · exact B199835
  · exact B199839
  · exact B199843
  · exact B199847
  · exact B199851
  · exact B199855
  · exact B199859
  · exact B199863
  · exact B199867
  · exact B199871
  · exact B199875
  · exact B199879
  · exact B199883
  · exact B199887
  · exact B199891
  · exact B199895
  · exact B199899
  · exact B199903
  · exact B199907
  · exact B199911
  · exact B199915
  · exact B199919
  · exact B199923
  · exact B199927
  · exact B199931
  · exact B199935
  · exact B199939
  · exact B199943
  · exact B199947
  · exact B199951
  · exact B199955
  · exact B199959
  · exact B199963
  · exact B199967
  · exact B199971
  · exact B199975
  · exact B199979
  · exact B199983
  · exact B199987
  · exact B199991
  · exact B199995
  · exact B199999
  · exact B200003
  · exact B200007
  · exact B200011
  · exact B200015
  · exact B200019
  · exact B200023
  · exact B200027
  · exact B200031
  · exact B200035
  · exact B200039
  · exact B200043
  · exact B200047
  · exact B200051
  · exact B200055
  · exact B200059
  · exact B200063
  · exact B200067
  · exact B200071
  · exact B200075
  · exact B200079
  · exact B200083
  · exact B200087
  · exact B200091
  · exact B200095
  · exact B200099
  · exact B200103
  · exact B200107
  · exact B200111
  · exact B200115
  · exact B200119
  · exact B200123
  · exact B200127
  · exact B200131
  · exact B200135
  · exact B200139
  · exact B200143
  · exact B200147
  · exact B200151
  · exact B200155
  · exact B200159
  · exact B200163
  · exact B200167
  · exact B200171
  · exact B200175
  · exact B200179
  · exact B200183
  · exact B200187
  · exact B200191
  · exact B200195
  · exact B200199
  · exact B200203
  · exact B200207
  · exact B200211
  · exact B200215
  · exact B200219
  · exact B200223
  · exact B200227
  · exact B200231
  · exact B200235
  · exact B200239
  · exact B200243
  · exact B200247
  · exact B200251
  · exact B200255
  · exact B200259
  · exact B200263
  · exact B200267
  · exact B200271
  · exact B200275
  · exact B200279
  · exact B200283
  · exact B200287
  · exact B200291
  · exact B200295
  · exact B200299
  · exact B200303
  · exact B200307
  · exact B200311
  · exact B200315
  · exact B200319
  · exact B200323
  · exact B200327
  · exact B200331
  · exact B200335
  · exact B200339
  · exact B200343
  · exact B200347
  · exact B200351
  · exact B200355
  · exact B200359
  · exact B200363
  · exact B200367
  · exact B200371
  · exact B200375
  · exact B200379
  · exact B200383
  · exact B200387
  · exact B200391
  · exact B200395
  · exact B200399
  · exact B200403
  · exact B200407
  · exact B200411
  · exact B200415
  · exact B200419
  · exact B200423
  · exact B200427
  · exact B200431
  · exact B200435
  · exact B200439
  · exact B200443
  · exact B200447
  · exact B200451
  · exact B200455
  · exact B200459
  · exact B200463
  · exact B200467
  · exact B200471
  · exact B200475
  · exact B200479
  · exact B200483
  · exact B200487
  · exact B200491
  · exact B200495
  · exact B200499
  · exact B200503
  · exact B200507
  · exact B200511
  · exact B200515
  · exact B200519
  · exact B200523
  · exact B200527
  · exact B200531
  · exact B200535
  · exact B200539
  · exact B200543
  · exact B200547
  · exact B200551
  · exact B200555
  · exact B200559
  · exact B200563
  · exact B200567
  · exact B200571
  · exact B200575
  · exact B200579
  · exact B200583
  · exact B200587
  · exact B200591
  · exact B200595
  · exact B200599
  · exact B200603
  · exact B200607
  · exact B200611
  · exact B200615
  · exact B200619
  · exact B200623
  · exact B200627
  · exact B200631
  · exact B200635
  · exact B200639
  · exact B200643
  · exact B200647
  · exact B200651
  · exact B200655
  · exact B200659
  · exact B200663
  · exact B200667
  · exact B200671
  · exact B200675
  · exact B200679
  · exact B200683
  · exact B200687
  · exact B200691
  · exact B200695
  · exact B200699
  · exact B200703
  · exact B200707
  · exact B200711
  · exact B200715
  · exact B200719
  · exact B200723
  · exact B200727
  · exact B200731
  · exact B200735
  · exact B200739
  · exact B200743
  · exact B200747
  · exact B200751
  · exact B200755
  · exact B200759
  · exact B200763
  · exact B200767
  · exact B200771
  · exact B200775
  · exact B200779
  · exact B200783
  · exact B200787
  · exact B200791
  · exact B200795
  · exact B200799
  · exact B200803
  · exact B200807
  · exact B200811
  · exact B200815
  · exact B200819
  · exact B200823
  · exact B200827
  · exact B200831
  · exact B200835
  · exact B200839
  · exact B200843
  · exact B200847
  · exact B200851
  · exact B200855
  · exact B200859
  · exact B200863
  · exact B200867
  · exact B200871
  · exact B200875
  · exact B200879
  · exact B200883
  · exact B200887
  · exact B200891
  · exact B200895
  · exact B200899
  · exact B200903
  · exact B200907
  · exact B200911
  · exact B200915
  · exact B200919
  · exact B200923
  · exact B200927
  · exact B200931
  · exact B200935
  · exact B200939
  · exact B200943
  · exact B200947
  · exact B200951
  · exact B200955
  · exact B200959
  · exact B200963
  · exact B200967
  · exact B200971
  · exact B200975
  · exact B200979
  · exact B200983
  · exact B200987
  · exact B200991
  · exact B200995
  · exact B200999
  · exact B201003
  · exact B201007
  · exact B201011
  · exact B201015
  · exact B201019
  · exact B201023
  · exact B201027
  · exact B201031
  · exact B201035
  · exact B201039
  · exact B201043
  · exact B201047
  · exact B201051
  · exact B201055
  · exact B201059
  · exact B201063
  · exact B201067
  · exact B201071
  · exact B201075
  · exact B201079
  · exact B201083
  · exact B201087
  · exact B201091
  · exact B201095
  · exact B201099
  · exact B201103
  · exact B201107
  · exact B201111
  · exact B201115
  · exact B201119
  · exact B201123
  · exact B201127
  · exact B201131
  · exact B201135
  · exact B201139
  · exact B201143
  · exact B201147
  · exact B201151
  · exact B201155
  · exact B201159
  · exact B201163
  · exact B201167
  · exact B201171
  · exact B201175
  · exact B201179
  · exact B201183
  · exact B201187
  · exact B201191
  · exact B201195
  · exact B201199
  · exact B201203
  · exact B201207
  · exact B201211
  · exact B201215
  · exact B201219
  · exact B201223
  · exact B201227
  · exact B201231
  · exact B201235
  · exact B201239
  · exact B201243
  · exact B201247
  · exact B201251
  · exact B201255
  · exact B201259
  · exact B201263
  · exact B201267
  · exact B201271
  · exact B201275
  · exact B201279
  · exact B201283
  · exact B201287
  · exact B201291
  · exact B201295
  · exact B201299
  · exact B201303
  · exact B201307
  · exact B201311
  · exact B201315
  · exact B201319
  · exact B201323
  · exact B201327
  · exact B201331
  · exact B201335
  · exact B201339
  · exact B201343
  · exact B201347
  · exact B201351
  · exact B201355
  · exact B201359
  · exact B201363
  · exact B201367
  · exact B201371
  · exact B201375
  · exact B201379
  · exact B201383
  · exact B201387
  · exact B201391
  · exact B201395
  · exact B201399
  · exact B201403
  · exact B201407
  · exact B201411
  · exact B201415
  · exact B201419
  · exact B201423
  · exact B201427
  · exact B201431
  · exact B201435
  · exact B201439
  · exact B201443
  · exact B201447
  · exact B201451
  · exact B201455
  · exact B201459
  · exact B201463
  · exact B201467
  · exact B201471
  · exact B201475
  · exact B201479
  · exact B201483
  · exact B201487
  · exact B201491
  · exact B201495
  · exact B201499
  · exact B201503
  · exact B201507
  · exact B201511
  · exact B201515
  · exact B201519
  · exact B201523
  · exact B201527
  · exact B201531
  · exact B201535
  · exact B201539
  · exact B201543
  · exact B201547
  · exact B201551
  · exact B201555
  · exact B201559
  · exact B201563
  · exact B201567
  · exact B201571
  · exact B201575
  · exact B201579
  · exact B201583
  · exact B201587
  · exact B201591
  · exact B201595
  · exact B201599
  · exact B201603
  · exact B201607
  · exact B201611
  · exact B201615
  · exact B201619
  · exact B201623
  · exact B201627
  · exact B201631
  · exact B201635
  · exact B201639
  · exact B201643
  · exact B201647
  · exact B201651
  · exact B201655
  · exact B201659
  · exact B201663
  · exact B201667
  · exact B201671
  · exact B201675
  · exact B201679
  · exact B201683
  · exact B201687
  · exact B201691
  · exact B201695
  · exact B201699
  · exact B201703
  · exact B201707
  · exact B201711
  · exact B201715
  · exact B201719
  · exact B201723
  · exact B201727
  · exact B201731
  · exact B201735
  · exact B201739
  · exact B201743
  · exact B201747
  · exact B201751
  · exact B201755
  · exact B201759
  · exact B201763
  · exact B201767
  · exact B201771
  · exact B201775
  · exact B201779
  · exact B201783
  · exact B201787
  · exact B201791
  · exact B201795
  · exact B201799
  · exact B201803
  · exact B201807
  · exact B201811
  · exact B201815
  · exact B201819
  · exact B201823
  · exact B201827
  · exact B201831
  · exact B201835
  · exact B201839
  · exact B201843
  · exact B201847
  · exact B201851
  · exact B201855
  · exact B201859
  · exact B201863
  · exact B201867
  · exact B201871
  · exact B201875
  · exact B201879
  · exact B201883
  · exact B201887
  · exact B201891
  · exact B201895
  · exact B201899
  · exact B201903
  · exact B201907
  · exact B201911
  · exact B201915
  · exact B201919
  · exact B201923
  · exact B201927
  · exact B201931
  · exact B201935
  · exact B201939
  · exact B201943
  · exact B201947
  · exact B201951
  · exact B201955
  · exact B201959
  · exact B201963
  · exact B201967
  · exact B201971
  · exact B201975
  · exact B201979
  · exact B201983
  · exact B201987
  · exact B201991
  · exact B201995
  · exact B201999
  · exact B202003
  · exact B202007
  · exact B202011
  · exact B202015
  · exact B202019
  · exact B202023
  · exact B202027
  · exact B202031
  · exact B202035
  · exact B202039
  · exact B202043
  · exact B202047
  · exact B202051
  · exact B202055
  · exact B202059
  · exact B202063
  · exact B202067
  · exact B202071
  · exact B202075
  · exact B202079
  · exact B202083
  · exact B202087
  · exact B202091
  · exact B202095
  · exact B202099
  · exact B202103
  · exact B202107
  · exact B202111
  · exact B202115
  · exact B202119
  · exact B202123
  · exact B202127
  · exact B202131
  · exact B202135
  · exact B202139
  · exact B202143
  · exact B202147
  · exact B202151
  · exact B202155
  · exact B202159
  · exact B202163
  · exact B202167
  · exact B202171
  · exact B202175
  · exact B202179
  · exact B202183
  · exact B202187
  · exact B202191
  · exact B202195
  · exact B202199
  · exact B202203
  · exact B202207
  · exact B202211
  · exact B202215
  · exact B202219
  · exact B202223
  · exact B202227
  · exact B202231
  · exact B202235
  · exact B202239
  · exact B202243
  · exact B202247
  · exact B202251
  · exact B202255
  · exact B202259
  · exact B202263
  · exact B202267
  · exact B202271
  · exact B202275
  · exact B202279
  · exact B202283
  · exact B202287
  · exact B202291
  · exact B202295
  · exact B202299
  · exact B202303
  · exact B202307
  · exact B202311
  · exact B202315
  · exact B202319
  · exact B202323
  · exact B202327
  · exact B202331
  · exact B202335
  · exact B202339
  · exact B202343
  · exact B202347
  · exact B202351
  · exact B202355
  · exact B202359
  · exact B202363
  · exact B202367
  · exact B202371
  · exact B202375
  · exact B202379
  · exact B202383
  · exact B202387
  · exact B202391
  · exact B202395
  · exact B202399
  · exact B202403
  · exact B202407
  · exact B202411
  · exact B202415
  · exact B202419
  · exact B202423
  · exact B202427
  · exact B202431
  · exact B202435
  · exact B202439
  · exact B202443
  · exact B202447
  · exact B202451
  · exact B202455
  · exact B202459
  · exact B202463
  · exact B202467
  · exact B202471
  · exact B202475
  · exact B202479
  · exact B202483
  · exact B202487
  · exact B202491
  · exact B202495
  · exact B202499
  · exact B202503
  · exact B202507
  · exact B202511
  · exact B202515
  · exact B202519
  · exact B202523
  · exact B202527
  · exact B202531
  · exact B202535
  · exact B202539
  · exact B202543
  · exact B202547
  · exact B202551
  · exact B202555
  · exact B202559
  · exact B202563
  · exact B202567
  · exact B202571
  · exact B202575
  · exact B202579
  · exact B202583
  · exact B202587
  · exact B202591
  · exact B202595
  · exact B202599
  · exact B202603

theorem C1 (j : ℕ) (h1 : 50651 ≤ j) (h2 : j ≤ 50950) : Blo 199806 (4 * j + 3) := by
  interval_cases j
  · exact B202607
  · exact B202611
  · exact B202615
  · exact B202619
  · exact B202623
  · exact B202627
  · exact B202631
  · exact B202635
  · exact B202639
  · exact B202643
  · exact B202647
  · exact B202651
  · exact B202655
  · exact B202659
  · exact B202663
  · exact B202667
  · exact B202671
  · exact B202675
  · exact B202679
  · exact B202683
  · exact B202687
  · exact B202691
  · exact B202695
  · exact B202699
  · exact B202703
  · exact B202707
  · exact B202711
  · exact B202715
  · exact B202719
  · exact B202723
  · exact B202727
  · exact B202731
  · exact B202735
  · exact B202739
  · exact B202743
  · exact B202747
  · exact B202751
  · exact B202755
  · exact B202759
  · exact B202763
  · exact B202767
  · exact B202771
  · exact B202775
  · exact B202779
  · exact B202783
  · exact B202787
  · exact B202791
  · exact B202795
  · exact B202799
  · exact B202803
  · exact B202807
  · exact B202811
  · exact B202815
  · exact B202819
  · exact B202823
  · exact B202827
  · exact B202831
  · exact B202835
  · exact B202839
  · exact B202843
  · exact B202847
  · exact B202851
  · exact B202855
  · exact B202859
  · exact B202863
  · exact B202867
  · exact B202871
  · exact B202875
  · exact B202879
  · exact B202883
  · exact B202887
  · exact B202891
  · exact B202895
  · exact B202899
  · exact B202903
  · exact B202907
  · exact B202911
  · exact B202915
  · exact B202919
  · exact B202923
  · exact B202927
  · exact B202931
  · exact B202935
  · exact B202939
  · exact B202943
  · exact B202947
  · exact B202951
  · exact B202955
  · exact B202959
  · exact B202963
  · exact B202967
  · exact B202971
  · exact B202975
  · exact B202979
  · exact B202983
  · exact B202987
  · exact B202991
  · exact B202995
  · exact B202999
  · exact B203003
  · exact B203007
  · exact B203011
  · exact B203015
  · exact B203019
  · exact B203023
  · exact B203027
  · exact B203031
  · exact B203035
  · exact B203039
  · exact B203043
  · exact B203047
  · exact B203051
  · exact B203055
  · exact B203059
  · exact B203063
  · exact B203067
  · exact B203071
  · exact B203075
  · exact B203079
  · exact B203083
  · exact B203087
  · exact B203091
  · exact B203095
  · exact B203099
  · exact B203103
  · exact B203107
  · exact B203111
  · exact B203115
  · exact B203119
  · exact B203123
  · exact B203127
  · exact B203131
  · exact B203135
  · exact B203139
  · exact B203143
  · exact B203147
  · exact B203151
  · exact B203155
  · exact B203159
  · exact B203163
  · exact B203167
  · exact B203171
  · exact B203175
  · exact B203179
  · exact B203183
  · exact B203187
  · exact B203191
  · exact B203195
  · exact B203199
  · exact B203203
  · exact B203207
  · exact B203211
  · exact B203215
  · exact B203219
  · exact B203223
  · exact B203227
  · exact B203231
  · exact B203235
  · exact B203239
  · exact B203243
  · exact B203247
  · exact B203251
  · exact B203255
  · exact B203259
  · exact B203263
  · exact B203267
  · exact B203271
  · exact B203275
  · exact B203279
  · exact B203283
  · exact B203287
  · exact B203291
  · exact B203295
  · exact B203299
  · exact B203303
  · exact B203307
  · exact B203311
  · exact B203315
  · exact B203319
  · exact B203323
  · exact B203327
  · exact B203331
  · exact B203335
  · exact B203339
  · exact B203343
  · exact B203347
  · exact B203351
  · exact B203355
  · exact B203359
  · exact B203363
  · exact B203367
  · exact B203371
  · exact B203375
  · exact B203379
  · exact B203383
  · exact B203387
  · exact B203391
  · exact B203395
  · exact B203399
  · exact B203403
  · exact B203407
  · exact B203411
  · exact B203415
  · exact B203419
  · exact B203423
  · exact B203427
  · exact B203431
  · exact B203435
  · exact B203439
  · exact B203443
  · exact B203447
  · exact B203451
  · exact B203455
  · exact B203459
  · exact B203463
  · exact B203467
  · exact B203471
  · exact B203475
  · exact B203479
  · exact B203483
  · exact B203487
  · exact B203491
  · exact B203495
  · exact B203499
  · exact B203503
  · exact B203507
  · exact B203511
  · exact B203515
  · exact B203519
  · exact B203523
  · exact B203527
  · exact B203531
  · exact B203535
  · exact B203539
  · exact B203543
  · exact B203547
  · exact B203551
  · exact B203555
  · exact B203559
  · exact B203563
  · exact B203567
  · exact B203571
  · exact B203575
  · exact B203579
  · exact B203583
  · exact B203587
  · exact B203591
  · exact B203595
  · exact B203599
  · exact B203603
  · exact B203607
  · exact B203611
  · exact B203615
  · exact B203619
  · exact B203623
  · exact B203627
  · exact B203631
  · exact B203635
  · exact B203639
  · exact B203643
  · exact B203647
  · exact B203651
  · exact B203655
  · exact B203659
  · exact B203663
  · exact B203667
  · exact B203671
  · exact B203675
  · exact B203679
  · exact B203683
  · exact B203687
  · exact B203691
  · exact B203695
  · exact B203699
  · exact B203703
  · exact B203707
  · exact B203711
  · exact B203715
  · exact B203719
  · exact B203723
  · exact B203727
  · exact B203731
  · exact B203735
  · exact B203739
  · exact B203743
  · exact B203747
  · exact B203751
  · exact B203755
  · exact B203759
  · exact B203763
  · exact B203767
  · exact B203771
  · exact B203775
  · exact B203779
  · exact B203783
  · exact B203787
  · exact B203791
  · exact B203795
  · exact B203799
  · exact B203803

theorem solution (m : ℕ) (hlo : 199806 ≤ m) (hhi : m ≤ 203806) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 49951 ≤ j := by omega
    have hj2 : j ≤ 50950 := by omega
    have hb : Blo 199806 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 50651 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
