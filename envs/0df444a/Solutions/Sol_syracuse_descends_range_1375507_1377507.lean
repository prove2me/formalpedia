-- Prove2me | solution 1 for syracuse_descends_range_1375507_1377507
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:14.892074+00:00
-- url     : https://prove2.me/submissions/9ac56e44-6832-4041-b569-11986572f427

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


theorem B4407301 : Blo 1375507 4407301 := bbase (se 4 (by rfl) ⟨413184, by rfl⟩ : syracuseStep 4407301 = 826369) (by norm_num)
theorem B2064389 : Blo 1375507 2064389 := bbase (se 4 (by rfl) ⟨193536, by rfl⟩ : syracuseStep 2064389 = 387073) (by norm_num)
theorem B1548301 : Blo 1375507 1548301 := bbase (se 3 (by rfl) ⟨290306, by rfl⟩ : syracuseStep 1548301 = 580613) (by norm_num)
theorem B3309581 : Blo 1375507 3309581 := bbase (se 3 (by rfl) ⟨620546, by rfl⟩ : syracuseStep 3309581 = 1241093) (by norm_num)
theorem B3309589 : Blo 1375507 3309589 := bbase (se 6 (by rfl) ⟨77568, by rfl⟩ : syracuseStep 3309589 = 155137) (by norm_num)
theorem B2064413 : Blo 1375507 2064413 := bbase (se 3 (by rfl) ⟨387077, by rfl⟩ : syracuseStep 2064413 = 774155) (by norm_num)
theorem B1548337 : Blo 1375507 1548337 := bbase (se 2 (by rfl) ⟨580626, by rfl⟩ : syracuseStep 1548337 = 1161253) (by norm_num)
theorem B4644917 : Blo 1375507 4644917 := bbase (se 5 (by rfl) ⟨217730, by rfl⟩ : syracuseStep 4644917 = 435461) (by norm_num)
theorem B3096629 : Blo 1375507 3096629 := bbase (se 5 (by rfl) ⟨145154, by rfl⟩ : syracuseStep 3096629 = 290309) (by norm_num)
theorem B2064437 : Blo 1375507 2064437 := bbase (se 5 (by rfl) ⟨96770, by rfl⟩ : syracuseStep 2064437 = 193541) (by norm_num)
theorem B5226565 : Blo 1375507 5226565 := bbase (se 4 (by rfl) ⟨489990, by rfl⟩ : syracuseStep 5226565 = 979981) (by norm_num)
theorem B2064461 : Blo 1375507 2064461 := bbase (se 3 (by rfl) ⟨387086, by rfl⟩ : syracuseStep 2064461 = 774173) (by norm_num)
theorem B1548373 : Blo 1375507 1548373 := bbase (se 8 (by rfl) ⟨9072, by rfl⟩ : syracuseStep 1548373 = 18145) (by norm_num)
theorem B2064485 : Blo 1375507 2064485 := bbase (se 4 (by rfl) ⟨193545, by rfl⟩ : syracuseStep 2064485 = 387091) (by norm_num)
theorem B2941037 : Blo 1375507 2941037 := bbase (se 3 (by rfl) ⟨551444, by rfl⟩ : syracuseStep 2941037 = 1102889) (by norm_num)
theorem B1548409 : Blo 1375507 1548409 := bbase (se 2 (by rfl) ⟨580653, by rfl⟩ : syracuseStep 1548409 = 1161307) (by norm_num)
theorem B3096701 : Blo 1375507 3096701 := bbase (se 3 (by rfl) ⟨580631, by rfl⟩ : syracuseStep 3096701 = 1161263) (by norm_num)
theorem B2064509 : Blo 1375507 2064509 := bbase (se 3 (by rfl) ⟨387095, by rfl⟩ : syracuseStep 2064509 = 774191) (by norm_num)
theorem B9412757 : Blo 1375507 9412757 := bbase (se 6 (by rfl) ⟨220611, by rfl⟩ : syracuseStep 9412757 = 441223) (by norm_num)
theorem B2064533 : Blo 1375507 2064533 := bbase (se 6 (by rfl) ⟨48387, by rfl⟩ : syracuseStep 2064533 = 96775) (by norm_num)
theorem B2613397 : Blo 1375507 2613397 := bbase (se 6 (by rfl) ⟨61251, by rfl⟩ : syracuseStep 2613397 = 122503) (by norm_num)
theorem B1548445 : Blo 1375507 1548445 := bbase (se 3 (by rfl) ⟨290333, by rfl⟩ : syracuseStep 1548445 = 580667) (by norm_num)
theorem B2064557 : Blo 1375507 2064557 := bbase (se 3 (by rfl) ⟨387104, by rfl⟩ : syracuseStep 2064557 = 774209) (by norm_num)
theorem B2515117 : Blo 1375507 2515117 := bbase (se 3 (by rfl) ⟨471584, by rfl⟩ : syracuseStep 2515117 = 943169) (by norm_num)
theorem B1548481 : Blo 1375507 1548481 := bbase (se 2 (by rfl) ⟨580680, by rfl⟩ : syracuseStep 1548481 = 1161361) (by norm_num)
theorem B3096773 : Blo 1375507 3096773 := bbase (se 4 (by rfl) ⟨290322, by rfl⟩ : syracuseStep 3096773 = 580645) (by norm_num)
theorem B2064581 : Blo 1375507 2064581 := bbase (se 4 (by rfl) ⟨193554, by rfl⟩ : syracuseStep 2064581 = 387109) (by norm_num)
theorem B3481805 : Blo 1375507 3481805 := bbase (se 3 (by rfl) ⟨652838, by rfl⟩ : syracuseStep 3481805 = 1305677) (by norm_num)
theorem B2064605 : Blo 1375507 2064605 := bbase (se 3 (by rfl) ⟨387113, by rfl⟩ : syracuseStep 2064605 = 774227) (by norm_num)
theorem B1548517 : Blo 1375507 1548517 := bbase (se 4 (by rfl) ⟨145173, by rfl⟩ : syracuseStep 1548517 = 290347) (by norm_num)
theorem B2515181 : Blo 1375507 2515181 := bbase (se 3 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 2515181 = 943193) (by norm_num)
theorem B2064629 : Blo 1375507 2064629 := bbase (se 5 (by rfl) ⟨96779, by rfl⟩ : syracuseStep 2064629 = 193559) (by norm_num)
theorem B1548553 : Blo 1375507 1548553 := bbase (se 2 (by rfl) ⟨580707, by rfl⟩ : syracuseStep 1548553 = 1161415) (by norm_num)
theorem B3096845 : Blo 1375507 3096845 := bbase (se 3 (by rfl) ⟨580658, by rfl⟩ : syracuseStep 3096845 = 1161317) (by norm_num)
theorem B2064653 : Blo 1375507 2064653 := bbase (se 3 (by rfl) ⟨387122, by rfl⟩ : syracuseStep 2064653 = 774245) (by norm_num)
theorem B6971669 : Blo 1375507 6971669 := bbase (se 6 (by rfl) ⟨163398, by rfl⟩ : syracuseStep 6971669 = 326797) (by norm_num)
theorem B2064677 : Blo 1375507 2064677 := bbase (se 4 (by rfl) ⟨193563, by rfl⟩ : syracuseStep 2064677 = 387127) (by norm_num)
theorem B2613541 : Blo 1375507 2613541 := bbase (se 4 (by rfl) ⟨245019, by rfl⟩ : syracuseStep 2613541 = 490039) (by norm_num)
theorem B1548589 : Blo 1375507 1548589 := bbase (se 3 (by rfl) ⟨290360, by rfl⟩ : syracuseStep 1548589 = 580721) (by norm_num)
theorem B2064701 : Blo 1375507 2064701 := bbase (se 3 (by rfl) ⟨387131, by rfl⟩ : syracuseStep 2064701 = 774263) (by norm_num)
theorem B1548625 : Blo 1375507 1548625 := bbase (se 2 (by rfl) ⟨580734, by rfl⟩ : syracuseStep 1548625 = 1161469) (by norm_num)
theorem B3096917 : Blo 1375507 3096917 := bbase (se 10 (by rfl) ⟨4536, by rfl⟩ : syracuseStep 3096917 = 9073) (by norm_num)
theorem B2064725 : Blo 1375507 2064725 := bbase (se 10 (by rfl) ⟨3024, by rfl⟩ : syracuseStep 2064725 = 6049) (by norm_num)
theorem B2064749 : Blo 1375507 2064749 := bbase (se 3 (by rfl) ⟨387140, by rfl⟩ : syracuseStep 2064749 = 774281) (by norm_num)
theorem B1548661 : Blo 1375507 1548661 := bbase (se 5 (by rfl) ⟨72593, by rfl⟩ : syracuseStep 1548661 = 145187) (by norm_num)
theorem B5226869 : Blo 1375507 5226869 := bbase (se 5 (by rfl) ⟨245009, by rfl⟩ : syracuseStep 5226869 = 490019) (by norm_num)
theorem B2064773 : Blo 1375507 2064773 := bbase (se 4 (by rfl) ⟨193572, by rfl⟩ : syracuseStep 2064773 = 387145) (by norm_num)
theorem B1548697 : Blo 1375507 1548697 := bbase (se 2 (by rfl) ⟨580761, by rfl⟩ : syracuseStep 1548697 = 1161523) (by norm_num)
theorem B3096989 : Blo 1375507 3096989 := bbase (se 3 (by rfl) ⟨580685, by rfl⟩ : syracuseStep 3096989 = 1161371) (by norm_num)
theorem B2064797 : Blo 1375507 2064797 := bbase (se 3 (by rfl) ⟨387149, by rfl⟩ : syracuseStep 2064797 = 774299) (by norm_num)
theorem B2064821 : Blo 1375507 2064821 := bbase (se 5 (by rfl) ⟨96788, by rfl⟩ : syracuseStep 2064821 = 193577) (by norm_num)
theorem B1548733 : Blo 1375507 1548733 := bbase (se 3 (by rfl) ⟨290387, by rfl⟩ : syracuseStep 1548733 = 580775) (by norm_num)
theorem B2613701 : Blo 1375507 2613701 := bbase (se 4 (by rfl) ⟨245034, by rfl⟩ : syracuseStep 2613701 = 490069) (by norm_num)
theorem B2064845 : Blo 1375507 2064845 := bbase (se 3 (by rfl) ⟨387158, by rfl⟩ : syracuseStep 2064845 = 774317) (by norm_num)
theorem B1548769 : Blo 1375507 1548769 := bbase (se 2 (by rfl) ⟨580788, by rfl⟩ : syracuseStep 1548769 = 1161577) (by norm_num)
theorem B4645349 : Blo 1375507 4645349 := bbase (se 4 (by rfl) ⟨435501, by rfl⟩ : syracuseStep 4645349 = 871003) (by norm_num)
theorem B3097061 : Blo 1375507 3097061 := bbase (se 4 (by rfl) ⟨290349, by rfl⟩ : syracuseStep 3097061 = 580699) (by norm_num)
theorem B2064869 : Blo 1375507 2064869 := bbase (se 4 (by rfl) ⟨193581, by rfl⟩ : syracuseStep 2064869 = 387163) (by norm_num)
theorem B2064893 : Blo 1375507 2064893 := bbase (se 3 (by rfl) ⟨387167, by rfl⟩ : syracuseStep 2064893 = 774335) (by norm_num)
theorem B1548805 : Blo 1375507 1548805 := bbase (se 4 (by rfl) ⟨145200, by rfl⟩ : syracuseStep 1548805 = 290401) (by norm_num)
theorem B2064917 : Blo 1375507 2064917 := bbase (se 6 (by rfl) ⟨48396, by rfl⟩ : syracuseStep 2064917 = 96793) (by norm_num)
theorem B2204189 : Blo 1375507 2204189 := bbase (se 3 (by rfl) ⟨413285, by rfl⟩ : syracuseStep 2204189 = 826571) (by norm_num)
theorem B3482149 : Blo 1375507 3482149 := bbase (se 4 (by rfl) ⟨326451, by rfl⟩ : syracuseStep 3482149 = 652903) (by norm_num)
theorem B1548841 : Blo 1375507 1548841 := bbase (se 2 (by rfl) ⟨580815, by rfl⟩ : syracuseStep 1548841 = 1161631) (by norm_num)
theorem B3097133 : Blo 1375507 3097133 := bbase (se 3 (by rfl) ⟨580712, by rfl⟩ : syracuseStep 3097133 = 1161425) (by norm_num)
theorem B2064941 : Blo 1375507 2064941 := bbase (se 3 (by rfl) ⟨387176, by rfl⟩ : syracuseStep 2064941 = 774353) (by norm_num)
theorem B2064965 : Blo 1375507 2064965 := bbase (se 4 (by rfl) ⟨193590, by rfl⟩ : syracuseStep 2064965 = 387181) (by norm_num)
theorem B1548877 : Blo 1375507 1548877 := bbase (se 3 (by rfl) ⟨290414, by rfl⟩ : syracuseStep 1548877 = 580829) (by norm_num)
theorem B2613845 : Blo 1375507 2613845 := bbase (se 8 (by rfl) ⟨15315, by rfl⟩ : syracuseStep 2613845 = 30631) (by norm_num)
theorem B2064989 : Blo 1375507 2064989 := bbase (se 3 (by rfl) ⟨387185, by rfl⟩ : syracuseStep 2064989 = 774371) (by norm_num)
theorem B3531365 : Blo 1375507 3531365 := bbase (se 4 (by rfl) ⟨331065, by rfl⟩ : syracuseStep 3531365 = 662131) (by norm_num)
theorem B1548913 : Blo 1375507 1548913 := bbase (se 2 (by rfl) ⟨580842, by rfl⟩ : syracuseStep 1548913 = 1161685) (by norm_num)
theorem B3097205 : Blo 1375507 3097205 := bbase (se 5 (by rfl) ⟨145181, by rfl⟩ : syracuseStep 3097205 = 290363) (by norm_num)
theorem B2065013 : Blo 1375507 2065013 := bbase (se 5 (by rfl) ⟨96797, by rfl⟩ : syracuseStep 2065013 = 193595) (by norm_num)
theorem B2065037 : Blo 1375507 2065037 := bbase (se 3 (by rfl) ⟨387194, by rfl⟩ : syracuseStep 2065037 = 774389) (by norm_num)
theorem B3482261 : Blo 1375507 3482261 := bbase (se 6 (by rfl) ⟨81615, by rfl⟩ : syracuseStep 3482261 = 163231) (by norm_num)
theorem B1548949 : Blo 1375507 1548949 := bbase (se 6 (by rfl) ⟨36303, by rfl⟩ : syracuseStep 1548949 = 72607) (by norm_num)
theorem B3138205 : Blo 1375507 3138205 := bbase (se 3 (by rfl) ⟨588413, by rfl⟩ : syracuseStep 3138205 = 1176827) (by norm_num)
theorem B2065061 : Blo 1375507 2065061 := bbase (se 4 (by rfl) ⟨193599, by rfl⟩ : syracuseStep 2065061 = 387199) (by norm_num)
theorem B6963893 : Blo 1375507 6963893 := bbase (se 5 (by rfl) ⟨326432, by rfl⟩ : syracuseStep 6963893 = 652865) (by norm_num)
theorem B1548985 : Blo 1375507 1548985 := bbase (se 2 (by rfl) ⟨580869, by rfl⟩ : syracuseStep 1548985 = 1161739) (by norm_num)
theorem B3097277 : Blo 1375507 3097277 := bbase (se 3 (by rfl) ⟨580739, by rfl⟩ : syracuseStep 3097277 = 1161479) (by norm_num)
theorem B2065085 : Blo 1375507 2065085 := bbase (se 3 (by rfl) ⟨387203, by rfl⟩ : syracuseStep 2065085 = 774407) (by norm_num)
theorem B2065109 : Blo 1375507 2065109 := bbase (se 7 (by rfl) ⟨24200, by rfl⟩ : syracuseStep 2065109 = 48401) (by norm_num)
theorem B1549021 : Blo 1375507 1549021 := bbase (se 3 (by rfl) ⟨290441, by rfl⟩ : syracuseStep 1549021 = 580883) (by norm_num)
theorem B2065133 : Blo 1375507 2065133 := bbase (se 3 (by rfl) ⟨387212, by rfl⟩ : syracuseStep 2065133 = 774425) (by norm_num)
theorem B1549057 : Blo 1375507 1549057 := bbase (se 2 (by rfl) ⟨580896, by rfl⟩ : syracuseStep 1549057 = 1161793) (by norm_num)
theorem B3097349 : Blo 1375507 3097349 := bbase (se 4 (by rfl) ⟨290376, by rfl⟩ : syracuseStep 3097349 = 580753) (by norm_num)
theorem B2065157 : Blo 1375507 2065157 := bbase (se 4 (by rfl) ⟨193608, by rfl⟩ : syracuseStep 2065157 = 387217) (by norm_num)
theorem B2065181 : Blo 1375507 2065181 := bbase (se 3 (by rfl) ⟨387221, by rfl⟩ : syracuseStep 2065181 = 774443) (by norm_num)
theorem B1549093 : Blo 1375507 1549093 := bbase (se 4 (by rfl) ⟨145227, by rfl⟩ : syracuseStep 1549093 = 290455) (by norm_num)
theorem B2065205 : Blo 1375507 2065205 := bbase (se 5 (by rfl) ⟨96806, by rfl⟩ : syracuseStep 2065205 = 193613) (by norm_num)
theorem B1549129 : Blo 1375507 1549129 := bbase (se 2 (by rfl) ⟨580923, by rfl⟩ : syracuseStep 1549129 = 1161847) (by norm_num)
theorem B3097421 : Blo 1375507 3097421 := bbase (se 3 (by rfl) ⟨580766, by rfl⟩ : syracuseStep 3097421 = 1161533) (by norm_num)
theorem B2065229 : Blo 1375507 2065229 := bbase (se 3 (by rfl) ⟨387230, by rfl⟩ : syracuseStep 2065229 = 774461) (by norm_num)
theorem B3482453 : Blo 1375507 3482453 := bbase (se 9 (by rfl) ⟨10202, by rfl⟩ : syracuseStep 3482453 = 20405) (by norm_num)
theorem B6611797 : Blo 1375507 6611797 := bbase (se 9 (by rfl) ⟨19370, by rfl⟩ : syracuseStep 6611797 = 38741) (by norm_num)
theorem B2065253 : Blo 1375507 2065253 := bbase (se 4 (by rfl) ⟨193617, by rfl⟩ : syracuseStep 2065253 = 387235) (by norm_num)
theorem B1549165 : Blo 1375507 1549165 := bbase (se 3 (by rfl) ⟨290468, by rfl⟩ : syracuseStep 1549165 = 580937) (by norm_num)
theorem B2614133 : Blo 1375507 2614133 := bbase (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) (by norm_num)
theorem B2065277 : Blo 1375507 2065277 := bbase (se 3 (by rfl) ⟨387239, by rfl⟩ : syracuseStep 2065277 = 774479) (by norm_num)
theorem B1958789 : Blo 1375507 1958789 := bbase (se 4 (by rfl) ⟨183636, by rfl⟩ : syracuseStep 1958789 = 367273) (by norm_num)
theorem B1549201 : Blo 1375507 1549201 := bbase (se 2 (by rfl) ⟨580950, by rfl⟩ : syracuseStep 1549201 = 1161901) (by norm_num)
theorem B4645781 : Blo 1375507 4645781 := bbase (se 6 (by rfl) ⟨108885, by rfl⟩ : syracuseStep 4645781 = 217771) (by norm_num)
theorem B3097493 : Blo 1375507 3097493 := bbase (se 6 (by rfl) ⟨72597, by rfl⟩ : syracuseStep 3097493 = 145195) (by norm_num)
theorem B2065301 : Blo 1375507 2065301 := bbase (se 6 (by rfl) ⟨48405, by rfl⟩ : syracuseStep 2065301 = 96811) (by norm_num)
theorem B2065325 : Blo 1375507 2065325 := bbase (se 3 (by rfl) ⟨387248, by rfl⟩ : syracuseStep 2065325 = 774497) (by norm_num)
theorem B1549237 : Blo 1375507 1549237 := bbase (se 5 (by rfl) ⟨72620, by rfl⟩ : syracuseStep 1549237 = 145241) (by norm_num)
theorem B2065349 : Blo 1375507 2065349 := bbase (se 4 (by rfl) ⟨193626, by rfl⟩ : syracuseStep 2065349 = 387253) (by norm_num)
theorem B1549273 : Blo 1375507 1549273 := bbase (se 2 (by rfl) ⟨580977, by rfl⟩ : syracuseStep 1549273 = 1161955) (by norm_num)
theorem B3097565 : Blo 1375507 3097565 := bbase (se 3 (by rfl) ⟨580793, by rfl⟩ : syracuseStep 3097565 = 1161587) (by norm_num)
theorem B2065373 : Blo 1375507 2065373 := bbase (se 3 (by rfl) ⟨387257, by rfl⟩ : syracuseStep 2065373 = 774515) (by norm_num)
theorem B2941925 : Blo 1375507 2941925 := bbase (se 4 (by rfl) ⟨275805, by rfl⟩ : syracuseStep 2941925 = 551611) (by norm_num)
theorem B2065397 : Blo 1375507 2065397 := bbase (se 5 (by rfl) ⟨96815, by rfl⟩ : syracuseStep 2065397 = 193631) (by norm_num)
theorem B1549309 : Blo 1375507 1549309 := bbase (se 3 (by rfl) ⟨290495, by rfl⟩ : syracuseStep 1549309 = 580991) (by norm_num)
theorem B2065421 : Blo 1375507 2065421 := bbase (se 3 (by rfl) ⟨387266, by rfl⟩ : syracuseStep 2065421 = 774533) (by norm_num)
theorem B2614285 : Blo 1375507 2614285 := bbase (se 3 (by rfl) ⟨490178, by rfl⟩ : syracuseStep 2614285 = 980357) (by norm_num)
theorem B1885213 : Blo 1375507 1885213 := bbase (se 3 (by rfl) ⟨353477, by rfl⟩ : syracuseStep 1885213 = 706955) (by norm_num)
theorem B2204701 : Blo 1375507 2204701 := bbase (se 3 (by rfl) ⟨413381, by rfl⟩ : syracuseStep 2204701 = 826763) (by norm_num)
theorem B1549345 : Blo 1375507 1549345 := bbase (se 2 (by rfl) ⟨581004, by rfl⟩ : syracuseStep 1549345 = 1162009) (by norm_num)
theorem B3097637 : Blo 1375507 3097637 := bbase (se 4 (by rfl) ⟨290403, by rfl⟩ : syracuseStep 3097637 = 580807) (by norm_num)
theorem B2065445 : Blo 1375507 2065445 := bbase (se 4 (by rfl) ⟨193635, by rfl⟩ : syracuseStep 2065445 = 387271) (by norm_num)
theorem B2065469 : Blo 1375507 2065469 := bbase (se 3 (by rfl) ⟨387275, by rfl⟩ : syracuseStep 2065469 = 774551) (by norm_num)
theorem B1549381 : Blo 1375507 1549381 := bbase (se 4 (by rfl) ⟨145254, by rfl⟩ : syracuseStep 1549381 = 290509) (by norm_num)
theorem B2065493 : Blo 1375507 2065493 := bbase (se 8 (by rfl) ⟨12102, by rfl⟩ : syracuseStep 2065493 = 24205) (by norm_num)
theorem B1549417 : Blo 1375507 1549417 := bbase (se 2 (by rfl) ⟨581031, by rfl⟩ : syracuseStep 1549417 = 1162063) (by norm_num)
theorem B3097709 : Blo 1375507 3097709 := bbase (se 3 (by rfl) ⟨580820, by rfl⟩ : syracuseStep 3097709 = 1161641) (by norm_num)
theorem B2065517 : Blo 1375507 2065517 := bbase (se 3 (by rfl) ⟨387284, by rfl⟩ : syracuseStep 2065517 = 774569) (by norm_num)
theorem B2065541 : Blo 1375507 2065541 := bbase (se 4 (by rfl) ⟨193644, by rfl⟩ : syracuseStep 2065541 = 387289) (by norm_num)
theorem B1549453 : Blo 1375507 1549453 := bbase (se 3 (by rfl) ⟨290522, by rfl⟩ : syracuseStep 1549453 = 581045) (by norm_num)
theorem B4408469 : Blo 1375507 4408469 := bbase (se 6 (by rfl) ⟨103323, by rfl⟩ : syracuseStep 4408469 = 206647) (by norm_num)
theorem B2065565 : Blo 1375507 2065565 := bbase (se 3 (by rfl) ⟨387293, by rfl⟩ : syracuseStep 2065565 = 774587) (by norm_num)
theorem B3482797 : Blo 1375507 3482797 := bbase (se 3 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 3482797 = 1306049) (by norm_num)
theorem B1549489 : Blo 1375507 1549489 := bbase (se 2 (by rfl) ⟨581058, by rfl⟩ : syracuseStep 1549489 = 1162117) (by norm_num)
theorem B3097781 : Blo 1375507 3097781 := bbase (se 5 (by rfl) ⟨145208, by rfl⟩ : syracuseStep 3097781 = 290417) (by norm_num)
theorem B2065589 : Blo 1375507 2065589 := bbase (se 5 (by rfl) ⟨96824, by rfl⟩ : syracuseStep 2065589 = 193649) (by norm_num)
theorem B2065613 : Blo 1375507 2065613 := bbase (se 3 (by rfl) ⟨387302, by rfl⟩ : syracuseStep 2065613 = 774605) (by norm_num)
theorem B1549525 : Blo 1375507 1549525 := bbase (se 7 (by rfl) ⟨18158, by rfl⟩ : syracuseStep 1549525 = 36317) (by norm_num)
theorem B2065637 : Blo 1375507 2065637 := bbase (se 4 (by rfl) ⟨193653, by rfl⟩ : syracuseStep 2065637 = 387307) (by norm_num)
theorem B1885421 : Blo 1375507 1885421 := bbase (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) (by norm_num)
theorem B1549561 : Blo 1375507 1549561 := bbase (se 2 (by rfl) ⟨581085, by rfl⟩ : syracuseStep 1549561 = 1162171) (by norm_num)
theorem B3097853 : Blo 1375507 3097853 := bbase (se 3 (by rfl) ⟨580847, by rfl⟩ : syracuseStep 3097853 = 1161695) (by norm_num)
theorem B2065661 : Blo 1375507 2065661 := bbase (se 3 (by rfl) ⟨387311, by rfl⟩ : syracuseStep 2065661 = 774623) (by norm_num)
theorem B15680789 : Blo 1375507 15680789 := bbase (se 6 (by rfl) ⟨367518, by rfl⟩ : syracuseStep 15680789 = 735037) (by norm_num)
theorem B2065685 : Blo 1375507 2065685 := bbase (se 6 (by rfl) ⟨48414, by rfl⟩ : syracuseStep 2065685 = 96829) (by norm_num)
theorem B3482909 : Blo 1375507 3482909 := bbase (se 3 (by rfl) ⟨653045, by rfl⟩ : syracuseStep 3482909 = 1306091) (by norm_num)
theorem B1549597 : Blo 1375507 1549597 := bbase (se 3 (by rfl) ⟨290549, by rfl⟩ : syracuseStep 1549597 = 581099) (by norm_num)
theorem B2065709 : Blo 1375507 2065709 := bbase (se 3 (by rfl) ⟨387320, by rfl⟩ : syracuseStep 2065709 = 774641) (by norm_num)
theorem B2614589 : Blo 1375507 2614589 := bbase (se 3 (by rfl) ⟨490235, by rfl⟩ : syracuseStep 2614589 = 980471) (by norm_num)
theorem B1549633 : Blo 1375507 1549633 := bbase (se 2 (by rfl) ⟨581112, by rfl⟩ : syracuseStep 1549633 = 1162225) (by norm_num)
theorem B4646213 : Blo 1375507 4646213 := bbase (se 4 (by rfl) ⟨435582, by rfl⟩ : syracuseStep 4646213 = 871165) (by norm_num)
theorem B3097925 : Blo 1375507 3097925 := bbase (se 4 (by rfl) ⟨290430, by rfl⟩ : syracuseStep 3097925 = 580861) (by norm_num)
theorem B2065733 : Blo 1375507 2065733 := bbase (se 4 (by rfl) ⟨193662, by rfl⟩ : syracuseStep 2065733 = 387325) (by norm_num)
theorem B2065757 : Blo 1375507 2065757 := bbase (se 3 (by rfl) ⟨387329, by rfl⟩ : syracuseStep 2065757 = 774659) (by norm_num)
theorem B1549669 : Blo 1375507 1549669 := bbase (se 4 (by rfl) ⟨145281, by rfl⟩ : syracuseStep 1549669 = 290563) (by norm_num)
theorem B3581293 : Blo 1375507 3581293 := bbase (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) (by norm_num)
theorem B2065781 : Blo 1375507 2065781 := bbase (se 5 (by rfl) ⟨96833, by rfl⟩ : syracuseStep 2065781 = 193667) (by norm_num)
theorem B3097997 : Blo 1375507 3097997 := bbase (se 3 (by rfl) ⟨580874, by rfl⟩ : syracuseStep 3097997 = 1161749) (by norm_num)
theorem B2065805 : Blo 1375507 2065805 := bbase (se 3 (by rfl) ⟨387338, by rfl⟩ : syracuseStep 2065805 = 774677) (by norm_num)
theorem B2065829 : Blo 1375507 2065829 := bbase (se 4 (by rfl) ⟨193671, by rfl⟩ : syracuseStep 2065829 = 387343) (by norm_num)
theorem B2065853 : Blo 1375507 2065853 := bbase (se 3 (by rfl) ⟨387347, by rfl⟩ : syracuseStep 2065853 = 774695) (by norm_num)
theorem B35743189 : Blo 1375507 35743189 := bbase (se 7 (by rfl) ⟨418865, by rfl⟩ : syracuseStep 35743189 = 837731) (by norm_num)
theorem B3098069 : Blo 1375507 3098069 := bbase (se 7 (by rfl) ⟨36305, by rfl⟩ : syracuseStep 3098069 = 72611) (by norm_num)
theorem B2065877 : Blo 1375507 2065877 := bbase (se 7 (by rfl) ⟨24209, by rfl⟩ : syracuseStep 2065877 = 48419) (by norm_num)
theorem B3483101 : Blo 1375507 3483101 := bbase (se 3 (by rfl) ⟨653081, by rfl⟩ : syracuseStep 3483101 = 1306163) (by norm_num)
theorem B3139037 : Blo 1375507 3139037 := bbase (se 3 (by rfl) ⟨588569, by rfl⟩ : syracuseStep 3139037 = 1177139) (by norm_num)
theorem B2205157 : Blo 1375507 2205157 := bbase (se 4 (by rfl) ⟨206733, by rfl⟩ : syracuseStep 2205157 = 413467) (by norm_num)
theorem B2065901 : Blo 1375507 2065901 := bbase (se 3 (by rfl) ⟨387356, by rfl⟩ : syracuseStep 2065901 = 774713) (by norm_num)
theorem B12895733 : Blo 1375507 12895733 := bbase (se 5 (by rfl) ⟨604487, by rfl⟩ : syracuseStep 12895733 = 1208975) (by norm_num)
theorem B2065925 : Blo 1375507 2065925 := bbase (se 4 (by rfl) ⟨193680, by rfl⟩ : syracuseStep 2065925 = 387361) (by norm_num)
theorem B3098141 : Blo 1375507 3098141 := bbase (se 3 (by rfl) ⟨580901, by rfl⟩ : syracuseStep 3098141 = 1161803) (by norm_num)
theorem B2065949 : Blo 1375507 2065949 := bbase (se 3 (by rfl) ⟨387365, by rfl⟩ : syracuseStep 2065949 = 774731) (by norm_num)
theorem B6972965 : Blo 1375507 6972965 := bbase (se 4 (by rfl) ⟨653715, by rfl⟩ : syracuseStep 6972965 = 1307431) (by norm_num)
theorem B2065973 : Blo 1375507 2065973 := bbase (se 5 (by rfl) ⟨96842, by rfl⟩ : syracuseStep 2065973 = 193685) (by norm_num)
theorem B2065997 : Blo 1375507 2065997 := bbase (se 3 (by rfl) ⟨387374, by rfl⟩ : syracuseStep 2065997 = 774749) (by norm_num)
theorem B3098213 : Blo 1375507 3098213 := bbase (se 4 (by rfl) ⟨290457, by rfl⟩ : syracuseStep 3098213 = 580915) (by norm_num)
theorem B2066021 : Blo 1375507 2066021 := bbase (se 4 (by rfl) ⟨193689, by rfl⟩ : syracuseStep 2066021 = 387379) (by norm_num)
theorem B5883509 : Blo 1375507 5883509 := bbase (se 5 (by rfl) ⟨275789, by rfl⟩ : syracuseStep 5883509 = 551579) (by norm_num)
theorem B2066045 : Blo 1375507 2066045 := bbase (se 3 (by rfl) ⟨387383, by rfl⟩ : syracuseStep 2066045 = 774767) (by norm_num)
theorem B2066069 : Blo 1375507 2066069 := bbase (se 6 (by rfl) ⟨48423, by rfl⟩ : syracuseStep 2066069 = 96847) (by norm_num)
theorem B3098285 : Blo 1375507 3098285 := bbase (se 3 (by rfl) ⟨580928, by rfl⟩ : syracuseStep 3098285 = 1161857) (by norm_num)
theorem B2066093 : Blo 1375507 2066093 := bbase (se 3 (by rfl) ⟨387392, by rfl⟩ : syracuseStep 2066093 = 774785) (by norm_num)
theorem B2066117 : Blo 1375507 2066117 := bbase (se 4 (by rfl) ⟨193698, by rfl⟩ : syracuseStep 2066117 = 387397) (by norm_num)
theorem B2066141 : Blo 1375507 2066141 := bbase (se 3 (by rfl) ⟨387401, by rfl⟩ : syracuseStep 2066141 = 774803) (by norm_num)
theorem B4646645 : Blo 1375507 4646645 := bbase (se 5 (by rfl) ⟨217811, by rfl⟩ : syracuseStep 4646645 = 435623) (by norm_num)
theorem B3098357 : Blo 1375507 3098357 := bbase (se 5 (by rfl) ⟨145235, by rfl⟩ : syracuseStep 3098357 = 290471) (by norm_num)
theorem B2066165 : Blo 1375507 2066165 := bbase (se 5 (by rfl) ⟨96851, by rfl⟩ : syracuseStep 2066165 = 193703) (by norm_num)
theorem B2066189 : Blo 1375507 2066189 := bbase (se 3 (by rfl) ⟨387410, by rfl⟩ : syracuseStep 2066189 = 774821) (by norm_num)
theorem B2066213 : Blo 1375507 2066213 := bbase (se 4 (by rfl) ⟨193707, by rfl⟩ : syracuseStep 2066213 = 387415) (by norm_num)
theorem B3139373 : Blo 1375507 3139373 := bbase (se 3 (by rfl) ⟨588632, by rfl⟩ : syracuseStep 3139373 = 1177265) (by norm_num)
theorem B3483445 : Blo 1375507 3483445 := bbase (se 5 (by rfl) ⟨163286, by rfl⟩ : syracuseStep 3483445 = 326573) (by norm_num)
theorem B3098429 : Blo 1375507 3098429 := bbase (se 3 (by rfl) ⟨580955, by rfl⟩ : syracuseStep 3098429 = 1161911) (by norm_num)
theorem B2066237 : Blo 1375507 2066237 := bbase (se 3 (by rfl) ⟨387419, by rfl⟩ : syracuseStep 2066237 = 774839) (by norm_num)
theorem B2066261 : Blo 1375507 2066261 := bbase (se 9 (by rfl) ⟨6053, by rfl⟩ : syracuseStep 2066261 = 12107) (by norm_num)
theorem B5957477 : Blo 1375507 5957477 := bbase (se 4 (by rfl) ⟨558513, by rfl⟩ : syracuseStep 5957477 = 1117027) (by norm_num)
theorem B5883749 : Blo 1375507 5883749 := bbase (se 4 (by rfl) ⟨551601, by rfl⟩ : syracuseStep 5883749 = 1103203) (by norm_num)
theorem B3098501 : Blo 1375507 3098501 := bbase (se 4 (by rfl) ⟨290484, by rfl⟩ : syracuseStep 3098501 = 580969) (by norm_num)
theorem B1886101 : Blo 1375507 1886101 := bbase (se 6 (by rfl) ⟨44205, by rfl⟩ : syracuseStep 1886101 = 88411) (by norm_num)
theorem B3483557 : Blo 1375507 3483557 := bbase (se 4 (by rfl) ⟨326583, by rfl⟩ : syracuseStep 3483557 = 653167) (by norm_num)
theorem B7841717 : Blo 1375507 7841717 := bbase (se 5 (by rfl) ⟨367580, by rfl⟩ : syracuseStep 7841717 = 735161) (by norm_num)
theorem B6965189 : Blo 1375507 6965189 := bbase (se 4 (by rfl) ⟨652986, by rfl⟩ : syracuseStep 6965189 = 1305973) (by norm_num)
theorem B3098573 : Blo 1375507 3098573 := bbase (se 3 (by rfl) ⟨580982, by rfl⟩ : syracuseStep 3098573 = 1161965) (by norm_num)
theorem B5875685 : Blo 1375507 5875685 := bbase (se 4 (by rfl) ⟨550845, by rfl⟩ : syracuseStep 5875685 = 1101691) (by norm_num)
theorem B3098645 : Blo 1375507 3098645 := bbase (se 6 (by rfl) ⟨72624, by rfl⟩ : syracuseStep 3098645 = 145249) (by norm_num)
theorem B7440437 : Blo 1375507 7440437 := bbase (se 5 (by rfl) ⟨348770, by rfl⟩ : syracuseStep 7440437 = 697541) (by norm_num)
theorem B3917909 : Blo 1375507 3917909 := bbase (se 8 (by rfl) ⟨22956, by rfl⟩ : syracuseStep 3917909 = 45913) (by norm_num)
theorem B3098717 : Blo 1375507 3098717 := bbase (se 3 (by rfl) ⟨581009, by rfl⟩ : syracuseStep 3098717 = 1162019) (by norm_num)
theorem B3483749 : Blo 1375507 3483749 := bbase (se 4 (by rfl) ⟨326601, by rfl⟩ : syracuseStep 3483749 = 653203) (by norm_num)
theorem B1591417 : Blo 1375507 1591417 := bbase (se 2 (by rfl) ⟨596781, by rfl⟩ : syracuseStep 1591417 = 1193563) (by norm_num)
theorem B2205829 : Blo 1375507 2205829 := bbase (se 4 (by rfl) ⟨206796, by rfl⟩ : syracuseStep 2205829 = 413593) (by norm_num)
theorem B20400277 : Blo 1375507 20400277 := bbase (se 6 (by rfl) ⟨478131, by rfl⟩ : syracuseStep 20400277 = 956263) (by norm_num)
theorem B4647077 : Blo 1375507 4647077 := bbase (se 4 (by rfl) ⟨435663, by rfl⟩ : syracuseStep 4647077 = 871327) (by norm_num)
theorem B3098789 : Blo 1375507 3098789 := bbase (se 4 (by rfl) ⟨290511, by rfl⟩ : syracuseStep 3098789 = 581023) (by norm_num)
theorem B2648261 : Blo 1375507 2648261 := bbase (se 4 (by rfl) ⟨248274, by rfl⟩ : syracuseStep 2648261 = 496549) (by norm_num)
theorem B3098861 : Blo 1375507 3098861 := bbase (se 3 (by rfl) ⟨581036, by rfl⟩ : syracuseStep 3098861 = 1162073) (by norm_num)
theorem B1960213 : Blo 1375507 1960213 := bbase (se 6 (by rfl) ⟨45942, by rfl⟩ : syracuseStep 1960213 = 91885) (by norm_num)
theorem B10455317 : Blo 1375507 10455317 := bbase (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) (by norm_num)
theorem B3098933 : Blo 1375507 3098933 := bbase (se 5 (by rfl) ⟨145262, by rfl⟩ : syracuseStep 3098933 = 290525) (by norm_num)
theorem B3099005 : Blo 1375507 3099005 := bbase (se 3 (by rfl) ⟨581063, by rfl⟩ : syracuseStep 3099005 = 1162127) (by norm_num)
theorem B5228981 : Blo 1375507 5228981 := bbase (se 5 (by rfl) ⟨245108, by rfl⟩ : syracuseStep 5228981 = 490217) (by norm_num)
theorem B3484093 : Blo 1375507 3484093 := bbase (se 3 (by rfl) ⟨653267, by rfl⟩ : syracuseStep 3484093 = 1306535) (by norm_num)
theorem B3099077 : Blo 1375507 3099077 := bbase (se 4 (by rfl) ⟨290538, by rfl⟩ : syracuseStep 3099077 = 581077) (by norm_num)
theorem B5294549 : Blo 1375507 5294549 := bbase (se 7 (by rfl) ⟨62045, by rfl⟩ : syracuseStep 5294549 = 124091) (by norm_num)
theorem B3099149 : Blo 1375507 3099149 := bbase (se 3 (by rfl) ⟨581090, by rfl⟩ : syracuseStep 3099149 = 1162181) (by norm_num)
theorem B8825365 : Blo 1375507 8825365 := bbase (se 6 (by rfl) ⟨206844, by rfl⟩ : syracuseStep 8825365 = 413689) (by norm_num)
theorem B3484205 : Blo 1375507 3484205 := bbase (se 3 (by rfl) ⟨653288, by rfl⟩ : syracuseStep 3484205 = 1306577) (by norm_num)
theorem B2206253 : Blo 1375507 2206253 := bbase (se 3 (by rfl) ⟨413672, by rfl⟩ : syracuseStep 2206253 = 827345) (by norm_num)
theorem B4647509 : Blo 1375507 4647509 := bbase (se 8 (by rfl) ⟨27231, by rfl⟩ : syracuseStep 4647509 = 54463) (by norm_num)
theorem B3099221 : Blo 1375507 3099221 := bbase (se 8 (by rfl) ⟨18159, by rfl⟩ : syracuseStep 3099221 = 36319) (by norm_num)
theorem B1395289 : Blo 1375507 1395289 := bbase (se 2 (by rfl) ⟨523233, by rfl⟩ : syracuseStep 1395289 = 1046467) (by norm_num)
theorem B3099293 : Blo 1375507 3099293 := bbase (se 3 (by rfl) ⟨581117, by rfl⟩ : syracuseStep 3099293 = 1162235) (by norm_num)
theorem B10447541 : Blo 1375507 10447541 := bbase (se 5 (by rfl) ⟨489728, by rfl⟩ : syracuseStep 10447541 = 979457) (by norm_num)
theorem B5229269 : Blo 1375507 5229269 := bbase (se 7 (by rfl) ⟨61280, by rfl⟩ : syracuseStep 5229269 = 122561) (by norm_num)
theorem B3099365 : Blo 1375507 3099365 := bbase (se 4 (by rfl) ⟨290565, by rfl⟩ : syracuseStep 3099365 = 581131) (by norm_num)
theorem B3484397 : Blo 1375507 3484397 := bbase (se 3 (by rfl) ⟨653324, by rfl⟩ : syracuseStep 3484397 = 1306649) (by norm_num)
theorem B3918581 : Blo 1375507 3918581 := bbase (se 5 (by rfl) ⟨183683, by rfl⟩ : syracuseStep 3918581 = 367367) (by norm_num)
theorem B1469237 : Blo 1375507 1469237 := bbase (se 5 (by rfl) ⟨68870, by rfl⟩ : syracuseStep 1469237 = 137741) (by norm_num)
theorem B2091845 : Blo 1375507 2091845 := bbase (se 4 (by rfl) ⟨196110, by rfl⟩ : syracuseStep 2091845 = 392221) (by norm_num)
theorem B2321237 : Blo 1375507 2321237 := bbase (se 9 (by rfl) ⟨6800, by rfl⟩ : syracuseStep 2321237 = 13601) (by norm_num)
theorem B1960805 : Blo 1375507 1960805 := bbase (se 4 (by rfl) ⟨183825, by rfl⟩ : syracuseStep 1960805 = 367651) (by norm_num)
theorem B1469297 : Blo 1375507 1469297 := bbase (se 2 (by rfl) ⟨550986, by rfl⟩ : syracuseStep 1469297 = 1101973) (by norm_num)
theorem B3230597 : Blo 1375507 3230597 := bbase (se 4 (by rfl) ⟨302868, by rfl⟩ : syracuseStep 3230597 = 605737) (by norm_num)
theorem B2354093 : Blo 1375507 2354093 := bbase (se 3 (by rfl) ⟨441392, by rfl⟩ : syracuseStep 2354093 = 882785) (by norm_num)
theorem B1960885 : Blo 1375507 1960885 := bbase (se 5 (by rfl) ⟨91916, by rfl⟩ : syracuseStep 1960885 = 183833) (by norm_num)
theorem B3533765 : Blo 1375507 3533765 := bbase (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) (by norm_num)
theorem B2321365 : Blo 1375507 2321365 := bbase (se 7 (by rfl) ⟨27203, by rfl⟩ : syracuseStep 2321365 = 54407) (by norm_num)
theorem B4410325 : Blo 1375507 4410325 := bbase (se 7 (by rfl) ⟨51683, by rfl⟩ : syracuseStep 4410325 = 103367) (by norm_num)
theorem B1469425 : Blo 1375507 1469425 := bbase (se 2 (by rfl) ⟨551034, by rfl⟩ : syracuseStep 1469425 = 1102069) (by norm_num)
theorem B4647941 : Blo 1375507 4647941 := bbase (se 4 (by rfl) ⟨435744, by rfl⟩ : syracuseStep 4647941 = 871489) (by norm_num)
theorem B2321453 : Blo 1375507 2321453 := bbase (se 3 (by rfl) ⟨435272, by rfl⟩ : syracuseStep 2321453 = 870545) (by norm_num)
theorem B1961005 : Blo 1375507 1961005 := bbase (se 3 (by rfl) ⟨367688, by rfl⟩ : syracuseStep 1961005 = 735377) (by norm_num)
theorem B3484741 : Blo 1375507 3484741 := bbase (se 4 (by rfl) ⟨326694, by rfl⟩ : syracuseStep 3484741 = 653389) (by norm_num)
theorem B1961101 : Blo 1375507 1961101 := bbase (se 3 (by rfl) ⟨367706, by rfl⟩ : syracuseStep 1961101 = 735413) (by norm_num)
theorem B3919013 : Blo 1375507 3919013 := bbase (se 4 (by rfl) ⟨367407, by rfl⟩ : syracuseStep 3919013 = 734815) (by norm_num)
theorem B2321581 : Blo 1375507 2321581 := bbase (se 3 (by rfl) ⟨435296, by rfl⟩ : syracuseStep 2321581 = 870593) (by norm_num)
theorem B3484853 : Blo 1375507 3484853 := bbase (se 5 (by rfl) ⟨163352, by rfl⟩ : syracuseStep 3484853 = 326705) (by norm_num)
theorem B6966485 : Blo 1375507 6966485 := bbase (se 7 (by rfl) ⟨81638, by rfl⟩ : syracuseStep 6966485 = 163277) (by norm_num)
theorem B2321669 : Blo 1375507 2321669 := bbase (se 4 (by rfl) ⟨217656, by rfl⟩ : syracuseStep 2321669 = 435313) (by norm_num)
theorem B3140869 : Blo 1375507 3140869 := bbase (se 4 (by rfl) ⟨294456, by rfl⟩ : syracuseStep 3140869 = 588913) (by norm_num)
theorem B3485045 : Blo 1375507 3485045 := bbase (se 5 (by rfl) ⟨163361, by rfl⟩ : syracuseStep 3485045 = 326723) (by norm_num)
theorem B2321797 : Blo 1375507 2321797 := bbase (se 4 (by rfl) ⟨217668, by rfl⟩ : syracuseStep 2321797 = 435337) (by norm_num)
theorem B1764769 : Blo 1375507 1764769 := bbase (se 2 (by rfl) ⟨661788, by rfl⟩ : syracuseStep 1764769 = 1323577) (by norm_num)
theorem B1469869 : Blo 1375507 1469869 := bbase (se 3 (by rfl) ⟨275600, by rfl⟩ : syracuseStep 1469869 = 551201) (by norm_num)
theorem B4648373 : Blo 1375507 4648373 := bbase (se 5 (by rfl) ⟨217892, by rfl⟩ : syracuseStep 4648373 = 435785) (by norm_num)
theorem B1396165 : Blo 1375507 1396165 := bbase (se 4 (by rfl) ⟨130890, by rfl⟩ : syracuseStep 1396165 = 261781) (by norm_num)
theorem B2321885 : Blo 1375507 2321885 := bbase (se 3 (by rfl) ⟨435353, by rfl⟩ : syracuseStep 2321885 = 870707) (by norm_num)
theorem B1469989 : Blo 1375507 1469989 := bbase (se 4 (by rfl) ⟨137811, by rfl⟩ : syracuseStep 1469989 = 275623) (by norm_num)
theorem B2649677 : Blo 1375507 2649677 := bbase (se 3 (by rfl) ⟨496814, by rfl⟩ : syracuseStep 2649677 = 993629) (by norm_num)
theorem B1510997 : Blo 1375507 1510997 := bbase (se 8 (by rfl) ⟨8853, by rfl⟩ : syracuseStep 1510997 = 17707) (by norm_num)
theorem B3305053 : Blo 1375507 3305053 := bbase (se 3 (by rfl) ⟨619697, by rfl⟩ : syracuseStep 3305053 = 1239395) (by norm_num)
theorem B2322013 : Blo 1375507 2322013 := bbase (se 3 (by rfl) ⟨435377, by rfl⟩ : syracuseStep 2322013 = 870755) (by norm_num)
theorem B2092709 : Blo 1375507 2092709 := bbase (se 4 (by rfl) ⟨196191, by rfl⟩ : syracuseStep 2092709 = 392383) (by norm_num)
theorem B2322101 : Blo 1375507 2322101 := bbase (se 5 (by rfl) ⟨108848, by rfl⟩ : syracuseStep 2322101 = 217697) (by norm_num)
theorem B3485389 : Blo 1375507 3485389 := bbase (se 3 (by rfl) ⟨653510, by rfl⟩ : syracuseStep 3485389 = 1307021) (by norm_num)
theorem B5877461 : Blo 1375507 5877461 := bbase (se 7 (by rfl) ⟨68876, by rfl⟩ : syracuseStep 5877461 = 137753) (by norm_num)
theorem B1470241 : Blo 1375507 1470241 := bbase (se 2 (by rfl) ⟨551340, by rfl⟩ : syracuseStep 1470241 = 1102681) (by norm_num)
theorem B1470245 : Blo 1375507 1470245 := bbase (se 4 (by rfl) ⟨137835, by rfl⟩ : syracuseStep 1470245 = 275671) (by norm_num)
theorem B2322229 : Blo 1375507 2322229 := bbase (se 5 (by rfl) ⟨108854, by rfl⟩ : syracuseStep 2322229 = 217709) (by norm_num)
theorem B1568569 : Blo 1375507 1568569 := bbase (se 2 (by rfl) ⟨588213, by rfl⟩ : syracuseStep 1568569 = 1176427) (by norm_num)
theorem B3485501 : Blo 1375507 3485501 := bbase (se 3 (by rfl) ⟨653531, by rfl⟩ : syracuseStep 3485501 = 1307063) (by norm_num)
theorem B4771685 : Blo 1375507 4771685 := bbase (se 4 (by rfl) ⟨447345, by rfl⟩ : syracuseStep 4771685 = 894691) (by norm_num)
theorem B4648805 : Blo 1375507 4648805 := bbase (se 4 (by rfl) ⟨435825, by rfl⟩ : syracuseStep 4648805 = 871651) (by norm_num)
theorem B2322317 : Blo 1375507 2322317 := bbase (se 3 (by rfl) ⟨435434, by rfl⟩ : syracuseStep 2322317 = 870869) (by norm_num)
theorem B3919765 : Blo 1375507 3919765 := bbase (se 6 (by rfl) ⟨91869, by rfl⟩ : syracuseStep 3919765 = 183739) (by norm_num)
theorem B3485693 : Blo 1375507 3485693 := bbase (se 3 (by rfl) ⟨653567, by rfl⟩ : syracuseStep 3485693 = 1307135) (by norm_num)
theorem B2322445 : Blo 1375507 2322445 := bbase (se 3 (by rfl) ⟨435458, by rfl⟩ : syracuseStep 2322445 = 870917) (by norm_num)
theorem B2322533 : Blo 1375507 2322533 := bbase (se 4 (by rfl) ⟨217737, by rfl⟩ : syracuseStep 2322533 = 435475) (by norm_num)
theorem B1740953 : Blo 1375507 1740953 := bbase (se 2 (by rfl) ⟨652857, by rfl⟩ : syracuseStep 1740953 = 1305715) (by norm_num)
theorem B13234357 : Blo 1375507 13234357 := bbase (se 5 (by rfl) ⟨620360, by rfl⟩ : syracuseStep 13234357 = 1240721) (by norm_num)
theorem B1741009 : Blo 1375507 1741009 := bbase (se 2 (by rfl) ⟨652878, by rfl⟩ : syracuseStep 1741009 = 1305757) (by norm_num)
theorem B2322661 : Blo 1375507 2322661 := bbase (se 4 (by rfl) ⟨217749, by rfl⟩ : syracuseStep 2322661 = 435499) (by norm_num)
theorem B2093293 : Blo 1375507 2093293 := bbase (se 3 (by rfl) ⟨392492, by rfl⟩ : syracuseStep 2093293 = 784985) (by norm_num)
theorem B5222677 : Blo 1375507 5222677 := bbase (se 6 (by rfl) ⟨122406, by rfl⟩ : syracuseStep 5222677 = 244813) (by norm_num)
theorem B3305765 : Blo 1375507 3305765 := bbase (se 4 (by rfl) ⟨309915, by rfl⟩ : syracuseStep 3305765 = 619831) (by norm_num)
theorem B4411685 : Blo 1375507 4411685 := bbase (se 4 (by rfl) ⟨413595, by rfl⟩ : syracuseStep 4411685 = 827191) (by norm_num)
theorem B1741105 : Blo 1375507 1741105 := bbase (se 2 (by rfl) ⟨652914, by rfl⟩ : syracuseStep 1741105 = 1305829) (by norm_num)
theorem B2322749 : Blo 1375507 2322749 := bbase (se 3 (by rfl) ⟨435515, by rfl⟩ : syracuseStep 2322749 = 871031) (by norm_num)
theorem B2978117 : Blo 1375507 2978117 := bbase (se 4 (by rfl) ⟨279198, by rfl⟩ : syracuseStep 2978117 = 558397) (by norm_num)
theorem B3486037 : Blo 1375507 3486037 := bbase (se 10 (by rfl) ⟨5106, by rfl⟩ : syracuseStep 3486037 = 10213) (by norm_num)
theorem B1470809 : Blo 1375507 1470809 := bbase (se 2 (by rfl) ⟨551553, by rfl⟩ : syracuseStep 1470809 = 1103107) (by norm_num)
theorem B1765805 : Blo 1375507 1765805 := bbase (se 3 (by rfl) ⟨331088, by rfl⟩ : syracuseStep 1765805 = 662177) (by norm_num)
theorem B4960693 : Blo 1375507 4960693 := bbase (se 5 (by rfl) ⟨232532, by rfl⟩ : syracuseStep 4960693 = 465065) (by norm_num)
theorem B2322877 : Blo 1375507 2322877 := bbase (se 3 (by rfl) ⟨435539, by rfl⟩ : syracuseStep 2322877 = 871079) (by norm_num)
theorem B3486149 : Blo 1375507 3486149 := bbase (se 4 (by rfl) ⟨326826, by rfl⟩ : syracuseStep 3486149 = 653653) (by norm_num)
theorem B1741277 : Blo 1375507 1741277 := bbase (se 3 (by rfl) ⟨326489, by rfl⟩ : syracuseStep 1741277 = 652979) (by norm_num)
theorem B6967781 : Blo 1375507 6967781 := bbase (se 4 (by rfl) ⟨653229, by rfl⟩ : syracuseStep 6967781 = 1306459) (by norm_num)
theorem B1741333 : Blo 1375507 1741333 := bbase (se 6 (by rfl) ⟨40812, by rfl⟩ : syracuseStep 1741333 = 81625) (by norm_num)
theorem B2322965 : Blo 1375507 2322965 := bbase (se 6 (by rfl) ⟨54444, by rfl⟩ : syracuseStep 2322965 = 108889) (by norm_num)
theorem B1470997 : Blo 1375507 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B5222981 : Blo 1375507 5222981 := bbase (se 4 (by rfl) ⟨489654, by rfl⟩ : syracuseStep 5222981 = 979309) (by norm_num)
theorem B1741429 : Blo 1375507 1741429 := bbase (se 5 (by rfl) ⟨81629, by rfl⟩ : syracuseStep 1741429 = 163259) (by norm_num)
theorem B2093693 : Blo 1375507 2093693 := bbase (se 3 (by rfl) ⟨392567, by rfl⟩ : syracuseStep 2093693 = 785135) (by norm_num)
theorem B3486341 : Blo 1375507 3486341 := bbase (se 4 (by rfl) ⟨326844, by rfl⟩ : syracuseStep 3486341 = 653689) (by norm_num)
theorem B2323093 : Blo 1375507 2323093 := bbase (se 6 (by rfl) ⟨54447, by rfl⟩ : syracuseStep 2323093 = 108895) (by norm_num)
theorem B1569449 : Blo 1375507 1569449 := bbase (se 2 (by rfl) ⟨588543, by rfl⟩ : syracuseStep 1569449 = 1177087) (by norm_num)
theorem B7951061 : Blo 1375507 7951061 := bbase (se 7 (by rfl) ⟨93176, by rfl⟩ : syracuseStep 7951061 = 186353) (by norm_num)
theorem B2355925 : Blo 1375507 2355925 := bbase (se 7 (by rfl) ⟨27608, by rfl⟩ : syracuseStep 2355925 = 55217) (by norm_num)
theorem B2323181 : Blo 1375507 2323181 := bbase (se 3 (by rfl) ⟨435596, by rfl⟩ : syracuseStep 2323181 = 871193) (by norm_num)
theorem B1741601 : Blo 1375507 1741601 := bbase (se 2 (by rfl) ⟨653100, by rfl⟩ : syracuseStep 1741601 = 1306201) (by norm_num)
theorem B2790197 : Blo 1375507 2790197 := bbase (se 5 (by rfl) ⟨130790, by rfl⟩ : syracuseStep 2790197 = 261581) (by norm_num)
theorem B1741657 : Blo 1375507 1741657 := bbase (se 2 (by rfl) ⟨653121, by rfl⟩ : syracuseStep 1741657 = 1306243) (by norm_num)
theorem B2323309 : Blo 1375507 2323309 := bbase (se 3 (by rfl) ⟨435620, by rfl⟩ : syracuseStep 2323309 = 871241) (by norm_num)
theorem B2790293 : Blo 1375507 2790293 := bbase (se 6 (by rfl) ⟨65397, by rfl⟩ : syracuseStep 2790293 = 130795) (by norm_num)
theorem B1741753 : Blo 1375507 1741753 := bbase (se 2 (by rfl) ⟨653157, by rfl⟩ : syracuseStep 1741753 = 1306315) (by norm_num)
theorem B3306437 : Blo 1375507 3306437 := bbase (se 4 (by rfl) ⟨309978, by rfl⟩ : syracuseStep 3306437 = 619957) (by norm_num)
theorem B2323397 : Blo 1375507 2323397 := bbase (se 4 (by rfl) ⟨217818, by rfl⟩ : syracuseStep 2323397 = 435637) (by norm_num)
theorem B3486685 : Blo 1375507 3486685 := bbase (se 3 (by rfl) ⟨653753, by rfl⟩ : syracuseStep 3486685 = 1307507) (by norm_num)
theorem B2233405 : Blo 1375507 2233405 := bbase (se 3 (by rfl) ⟨418763, by rfl⟩ : syracuseStep 2233405 = 837527) (by norm_num)
theorem B2323525 : Blo 1375507 2323525 := bbase (se 4 (by rfl) ⟨217830, by rfl⟩ : syracuseStep 2323525 = 435661) (by norm_num)
theorem B3486797 : Blo 1375507 3486797 := bbase (se 3 (by rfl) ⟨653774, by rfl⟩ : syracuseStep 3486797 = 1307549) (by norm_num)
theorem B1741925 : Blo 1375507 1741925 := bbase (se 4 (by rfl) ⟨163305, by rfl⟩ : syracuseStep 1741925 = 326611) (by norm_num)
theorem B6616181 : Blo 1375507 6616181 := bbase (se 5 (by rfl) ⟨310133, by rfl⟩ : syracuseStep 6616181 = 620267) (by norm_num)
theorem B1741981 : Blo 1375507 1741981 := bbase (se 3 (by rfl) ⟨326621, by rfl⟩ : syracuseStep 1741981 = 653243) (by norm_num)
theorem B2323613 : Blo 1375507 2323613 := bbase (se 3 (by rfl) ⟨435677, by rfl⟩ : syracuseStep 2323613 = 871355) (by norm_num)
theorem B1676477 : Blo 1375507 1676477 := bbase (se 3 (by rfl) ⟨314339, by rfl⟩ : syracuseStep 1676477 = 628679) (by norm_num)
theorem B1742077 : Blo 1375507 1742077 := bbase (se 3 (by rfl) ⟨326639, by rfl⟩ : syracuseStep 1742077 = 653279) (by norm_num)
theorem B2938133 : Blo 1375507 2938133 := bbase (se 6 (by rfl) ⟨68862, by rfl⟩ : syracuseStep 2938133 = 137725) (by norm_num)
theorem B2323741 : Blo 1375507 2323741 := bbase (se 3 (by rfl) ⟨435701, by rfl⟩ : syracuseStep 2323741 = 871403) (by norm_num)
theorem B11310421 : Blo 1375507 11310421 := bbase (se 14 (by rfl) ⟨1035, by rfl⟩ : syracuseStep 11310421 = 2071) (by norm_num)
theorem B9925973 : Blo 1375507 9925973 := bbase (se 13 (by rfl) ⟨1817, by rfl⟩ : syracuseStep 9925973 = 3635) (by norm_num)
theorem B2323829 : Blo 1375507 2323829 := bbase (se 5 (by rfl) ⟨108929, by rfl⟩ : syracuseStep 2323829 = 217859) (by norm_num)
theorem B1742249 : Blo 1375507 1742249 := bbase (se 2 (by rfl) ⟨653343, by rfl⟩ : syracuseStep 1742249 = 1306687) (by norm_num)
theorem B1742305 : Blo 1375507 1742305 := bbase (se 2 (by rfl) ⟨653364, by rfl⟩ : syracuseStep 1742305 = 1306729) (by norm_num)
theorem B2323957 : Blo 1375507 2323957 := bbase (se 5 (by rfl) ⟨108935, by rfl⟩ : syracuseStep 2323957 = 217871) (by norm_num)
theorem B1742401 : Blo 1375507 1742401 := bbase (se 2 (by rfl) ⟨653400, by rfl⟩ : syracuseStep 1742401 = 1306801) (by norm_num)
theorem B2324045 : Blo 1375507 2324045 := bbase (se 3 (by rfl) ⟨435758, by rfl⟩ : syracuseStep 2324045 = 871517) (by norm_num)
theorem B1767037 : Blo 1375507 1767037 := bbase (se 3 (by rfl) ⟨331319, by rfl⟩ : syracuseStep 1767037 = 662639) (by norm_num)
theorem B5297861 : Blo 1375507 5297861 := bbase (se 4 (by rfl) ⟨496674, by rfl⟩ : syracuseStep 5297861 = 993349) (by norm_num)
theorem B2324173 : Blo 1375507 2324173 := bbase (se 3 (by rfl) ⟨435782, by rfl⟩ : syracuseStep 2324173 = 871565) (by norm_num)
theorem B1742573 : Blo 1375507 1742573 := bbase (se 3 (by rfl) ⟨326732, by rfl⟩ : syracuseStep 1742573 = 653465) (by norm_num)
theorem B6969077 : Blo 1375507 6969077 := bbase (se 5 (by rfl) ⟨326675, by rfl⟩ : syracuseStep 6969077 = 653351) (by norm_num)
theorem B17880853 : Blo 1375507 17880853 := bbase (se 6 (by rfl) ⟨419082, by rfl⟩ : syracuseStep 17880853 = 838165) (by norm_num)
theorem B1742629 : Blo 1375507 1742629 := bbase (se 4 (by rfl) ⟨163371, by rfl⟩ : syracuseStep 1742629 = 326743) (by norm_num)
theorem B2324261 : Blo 1375507 2324261 := bbase (se 4 (by rfl) ⟨217899, by rfl⟩ : syracuseStep 2324261 = 435799) (by norm_num)
theorem B1742725 : Blo 1375507 1742725 := bbase (se 4 (by rfl) ⟨163380, by rfl⟩ : syracuseStep 1742725 = 326761) (by norm_num)
theorem B2324389 : Blo 1375507 2324389 := bbase (se 4 (by rfl) ⟨217911, by rfl⟩ : syracuseStep 2324389 = 435823) (by norm_num)
theorem B2480053 : Blo 1375507 2480053 := bbase (se 5 (by rfl) ⟨116252, by rfl⟩ : syracuseStep 2480053 = 232505) (by norm_num)
theorem B4642757 : Blo 1375507 4642757 := bbase (se 4 (by rfl) ⟨435258, by rfl⟩ : syracuseStep 4642757 = 870517) (by norm_num)
theorem B2324477 : Blo 1375507 2324477 := bbase (se 3 (by rfl) ⟨435839, by rfl⟩ : syracuseStep 2324477 = 871679) (by norm_num)
theorem B1742897 : Blo 1375507 1742897 := bbase (se 2 (by rfl) ⟨653586, by rfl⟩ : syracuseStep 1742897 = 1307173) (by norm_num)
theorem B1742953 : Blo 1375507 1742953 := bbase (se 2 (by rfl) ⟨653607, by rfl⟩ : syracuseStep 1742953 = 1307215) (by norm_num)
theorem B2939021 : Blo 1375507 2939021 := bbase (se 3 (by rfl) ⟨551066, by rfl⟩ : syracuseStep 2939021 = 1102133) (by norm_num)
theorem B1743049 : Blo 1375507 1743049 := bbase (se 2 (by rfl) ⟨653643, by rfl⟩ : syracuseStep 1743049 = 1307287) (by norm_num)
theorem B1652945 : Blo 1375507 1652945 := bbase (se 2 (by rfl) ⟨619854, by rfl⟩ : syracuseStep 1652945 = 1239709) (by norm_num)
theorem B2480341 : Blo 1375507 2480341 := bbase (se 7 (by rfl) ⟨29066, by rfl⟩ : syracuseStep 2480341 = 58133) (by norm_num)
theorem B2611453 : Blo 1375507 2611453 := bbase (se 3 (by rfl) ⟨489647, by rfl⟩ : syracuseStep 2611453 = 979295) (by norm_num)
theorem B2234621 : Blo 1375507 2234621 := bbase (se 3 (by rfl) ⟨418991, by rfl⟩ : syracuseStep 2234621 = 837983) (by norm_num)
theorem B2939141 : Blo 1375507 2939141 := bbase (se 4 (by rfl) ⟨275544, by rfl⟩ : syracuseStep 2939141 = 551089) (by norm_num)
theorem B19855637 : Blo 1375507 19855637 := bbase (se 6 (by rfl) ⟨465366, by rfl⟩ : syracuseStep 19855637 = 930733) (by norm_num)
theorem B1653061 : Blo 1375507 1653061 := bbase (se 4 (by rfl) ⟨154974, by rfl⟩ : syracuseStep 1653061 = 309949) (by norm_num)
theorem B3094901 : Blo 1375507 3094901 := bbase (se 5 (by rfl) ⟨145073, by rfl⟩ : syracuseStep 3094901 = 290147) (by norm_num)
theorem B4643189 : Blo 1375507 4643189 := bbase (se 5 (by rfl) ⟨217649, by rfl⟩ : syracuseStep 4643189 = 435299) (by norm_num)
theorem B1743221 : Blo 1375507 1743221 := bbase (se 5 (by rfl) ⟨81713, by rfl⟩ : syracuseStep 1743221 = 163427) (by norm_num)
theorem B2611597 : Blo 1375507 2611597 := bbase (se 3 (by rfl) ⟨489674, by rfl⟩ : syracuseStep 2611597 = 979349) (by norm_num)
theorem B1743277 : Blo 1375507 1743277 := bbase (se 3 (by rfl) ⟨326864, by rfl⟩ : syracuseStep 1743277 = 653729) (by norm_num)
theorem B3094973 : Blo 1375507 3094973 := bbase (se 3 (by rfl) ⟨580307, by rfl⟩ : syracuseStep 3094973 = 1160615) (by norm_num)
theorem B3095045 : Blo 1375507 3095045 := bbase (se 4 (by rfl) ⟨290160, by rfl⟩ : syracuseStep 3095045 = 580321) (by norm_num)
theorem B1653257 : Blo 1375507 1653257 := bbase (se 2 (by rfl) ⟨619971, by rfl⟩ : syracuseStep 1653257 = 1239943) (by norm_num)
theorem B1743373 : Blo 1375507 1743373 := bbase (se 3 (by rfl) ⟨326882, by rfl⟩ : syracuseStep 1743373 = 653765) (by norm_num)
theorem B2611757 : Blo 1375507 2611757 := bbase (se 3 (by rfl) ⟨489704, by rfl⟩ : syracuseStep 2611757 = 979409) (by norm_num)
theorem B3095117 : Blo 1375507 3095117 := bbase (se 3 (by rfl) ⟨580334, by rfl⟩ : syracuseStep 3095117 = 1160669) (by norm_num)
theorem B5225093 : Blo 1375507 5225093 := bbase (se 4 (by rfl) ⟨489852, by rfl⟩ : syracuseStep 5225093 = 979705) (by norm_num)
theorem B3095189 : Blo 1375507 3095189 := bbase (se 6 (by rfl) ⟨72543, by rfl⟩ : syracuseStep 3095189 = 145087) (by norm_num)
theorem B2120357 : Blo 1375507 2120357 := bbase (se 4 (by rfl) ⟨198783, by rfl⟩ : syracuseStep 2120357 = 397567) (by norm_num)
theorem B3308197 : Blo 1375507 3308197 := bbase (se 4 (by rfl) ⟨310143, by rfl⟩ : syracuseStep 3308197 = 620287) (by norm_num)
theorem B3922613 : Blo 1375507 3922613 := bbase (se 5 (by rfl) ⟨183872, by rfl⟩ : syracuseStep 3922613 = 367745) (by norm_num)
theorem B2611901 : Blo 1375507 2611901 := bbase (se 3 (by rfl) ⟨489731, by rfl⟩ : syracuseStep 2611901 = 979463) (by norm_num)
theorem B16743125 : Blo 1375507 16743125 := bbase (se 7 (by rfl) ⟨196208, by rfl⟩ : syracuseStep 16743125 = 392417) (by norm_num)
theorem B3095261 : Blo 1375507 3095261 := bbase (se 3 (by rfl) ⟨580361, by rfl⟩ : syracuseStep 3095261 = 1160723) (by norm_num)
theorem B13220597 : Blo 1375507 13220597 := bbase (se 5 (by rfl) ⟨619715, by rfl⟩ : syracuseStep 13220597 = 1239431) (by norm_num)
theorem B3095333 : Blo 1375507 3095333 := bbase (se 4 (by rfl) ⟨290187, by rfl⟩ : syracuseStep 3095333 = 580375) (by norm_num)
theorem B4643621 : Blo 1375507 4643621 := bbase (se 4 (by rfl) ⟨435339, by rfl⟩ : syracuseStep 4643621 = 870679) (by norm_num)
theorem B3095405 : Blo 1375507 3095405 := bbase (se 3 (by rfl) ⟨580388, by rfl⟩ : syracuseStep 3095405 = 1160777) (by norm_num)
theorem B2939773 : Blo 1375507 2939773 := bbase (se 3 (by rfl) ⟨551207, by rfl⟩ : syracuseStep 2939773 = 1102415) (by norm_num)
theorem B2063261 : Blo 1375507 2063261 := bbase (se 3 (by rfl) ⟨386861, by rfl⟩ : syracuseStep 2063261 = 773723) (by norm_num)
theorem B5225381 : Blo 1375507 5225381 := bbase (se 4 (by rfl) ⟨489879, by rfl⟩ : syracuseStep 5225381 = 979759) (by norm_num)
theorem B2063285 : Blo 1375507 2063285 := bbase (se 5 (by rfl) ⟨96716, by rfl⟩ : syracuseStep 2063285 = 193433) (by norm_num)
theorem B3095477 : Blo 1375507 3095477 := bbase (se 5 (by rfl) ⟨145100, by rfl⟩ : syracuseStep 3095477 = 290201) (by norm_num)
theorem B2063309 : Blo 1375507 2063309 := bbase (se 3 (by rfl) ⟨386870, by rfl⟩ : syracuseStep 2063309 = 773741) (by norm_num)
theorem B4709333 : Blo 1375507 4709333 := bbase (se 7 (by rfl) ⟨55187, by rfl⟩ : syracuseStep 4709333 = 110375) (by norm_num)
theorem B2612189 : Blo 1375507 2612189 := bbase (se 3 (by rfl) ⟨489785, by rfl⟩ : syracuseStep 2612189 = 979571) (by norm_num)
theorem B2063333 : Blo 1375507 2063333 := bbase (se 4 (by rfl) ⟨193437, by rfl⟩ : syracuseStep 2063333 = 386875) (by norm_num)
theorem B2063357 : Blo 1375507 2063357 := bbase (se 3 (by rfl) ⟨386879, by rfl⟩ : syracuseStep 2063357 = 773759) (by norm_num)
theorem B3095549 : Blo 1375507 3095549 := bbase (se 3 (by rfl) ⟨580415, by rfl⟩ : syracuseStep 3095549 = 1160831) (by norm_num)
theorem B6970373 : Blo 1375507 6970373 := bbase (se 4 (by rfl) ⟨653472, by rfl⟩ : syracuseStep 6970373 = 1306945) (by norm_num)
theorem B2063381 : Blo 1375507 2063381 := bbase (se 6 (by rfl) ⟨48360, by rfl⟩ : syracuseStep 2063381 = 96721) (by norm_num)
theorem B2063405 : Blo 1375507 2063405 := bbase (se 3 (by rfl) ⟨386888, by rfl⟩ : syracuseStep 2063405 = 773777) (by norm_num)
theorem B1653805 : Blo 1375507 1653805 := bbase (se 3 (by rfl) ⟨310088, by rfl⟩ : syracuseStep 1653805 = 620177) (by norm_num)
theorem B2063429 : Blo 1375507 2063429 := bbase (se 4 (by rfl) ⟨193446, by rfl⟩ : syracuseStep 2063429 = 386893) (by norm_num)
theorem B3095621 : Blo 1375507 3095621 := bbase (se 4 (by rfl) ⟨290214, by rfl⟩ : syracuseStep 3095621 = 580429) (by norm_num)
theorem B2063453 : Blo 1375507 2063453 := bbase (se 3 (by rfl) ⟨386897, by rfl⟩ : syracuseStep 2063453 = 773795) (by norm_num)
theorem B2063477 : Blo 1375507 2063477 := bbase (se 5 (by rfl) ⟨96725, by rfl⟩ : syracuseStep 2063477 = 193451) (by norm_num)
theorem B2612341 : Blo 1375507 2612341 := bbase (se 5 (by rfl) ⟨122453, by rfl⟩ : syracuseStep 2612341 = 244907) (by norm_num)
theorem B2063501 : Blo 1375507 2063501 := bbase (se 3 (by rfl) ⟨386906, by rfl⟩ : syracuseStep 2063501 = 773813) (by norm_num)
theorem B3095693 : Blo 1375507 3095693 := bbase (se 3 (by rfl) ⟨580442, by rfl⟩ : syracuseStep 3095693 = 1160885) (by norm_num)
theorem B2063525 : Blo 1375507 2063525 := bbase (se 4 (by rfl) ⟨193455, by rfl⟩ : syracuseStep 2063525 = 386911) (by norm_num)
theorem B2063549 : Blo 1375507 2063549 := bbase (se 3 (by rfl) ⟨386915, by rfl⟩ : syracuseStep 2063549 = 773831) (by norm_num)
theorem B1653949 : Blo 1375507 1653949 := bbase (se 3 (by rfl) ⟨310115, by rfl⟩ : syracuseStep 1653949 = 620231) (by norm_num)
theorem B1547473 : Blo 1375507 1547473 := bbase (se 2 (by rfl) ⟨580302, by rfl⟩ : syracuseStep 1547473 = 1160605) (by norm_num)
theorem B2063573 : Blo 1375507 2063573 := bbase (se 7 (by rfl) ⟨24182, by rfl⟩ : syracuseStep 2063573 = 48365) (by norm_num)
theorem B3095765 : Blo 1375507 3095765 := bbase (se 7 (by rfl) ⟨36278, by rfl⟩ : syracuseStep 3095765 = 72557) (by norm_num)
theorem B4644053 : Blo 1375507 4644053 := bbase (se 7 (by rfl) ⟨54422, by rfl⟩ : syracuseStep 4644053 = 108845) (by norm_num)
theorem B2235613 : Blo 1375507 2235613 := bbase (se 3 (by rfl) ⟨419177, by rfl⟩ : syracuseStep 2235613 = 838355) (by norm_num)
theorem B2063597 : Blo 1375507 2063597 := bbase (se 3 (by rfl) ⟨386924, by rfl⟩ : syracuseStep 2063597 = 773849) (by norm_num)
theorem B1547509 : Blo 1375507 1547509 := bbase (se 5 (by rfl) ⟨72539, by rfl⟩ : syracuseStep 1547509 = 145079) (by norm_num)
theorem B2063621 : Blo 1375507 2063621 := bbase (se 4 (by rfl) ⟨193464, by rfl⟩ : syracuseStep 2063621 = 386929) (by norm_num)
theorem B3308813 : Blo 1375507 3308813 := bbase (se 3 (by rfl) ⟨620402, by rfl⟩ : syracuseStep 3308813 = 1240805) (by norm_num)
theorem B1547545 : Blo 1375507 1547545 := bbase (se 2 (by rfl) ⟨580329, by rfl⟩ : syracuseStep 1547545 = 1160659) (by norm_num)
theorem B2063645 : Blo 1375507 2063645 := bbase (se 3 (by rfl) ⟨386933, by rfl⟩ : syracuseStep 2063645 = 773867) (by norm_num)
theorem B3095837 : Blo 1375507 3095837 := bbase (se 3 (by rfl) ⟨580469, by rfl⟩ : syracuseStep 3095837 = 1160939) (by norm_num)
theorem B2481437 : Blo 1375507 2481437 := bbase (se 3 (by rfl) ⟨465269, by rfl⟩ : syracuseStep 2481437 = 930539) (by norm_num)
theorem B2063669 : Blo 1375507 2063669 := bbase (se 5 (by rfl) ⟨96734, by rfl⟩ : syracuseStep 2063669 = 193469) (by norm_num)
theorem B1547581 : Blo 1375507 1547581 := bbase (se 3 (by rfl) ⟨290171, by rfl⟩ : syracuseStep 1547581 = 580343) (by norm_num)
theorem B2063693 : Blo 1375507 2063693 := bbase (se 3 (by rfl) ⟨386942, by rfl⟩ : syracuseStep 2063693 = 773885) (by norm_num)
theorem B1547617 : Blo 1375507 1547617 := bbase (se 2 (by rfl) ⟨580356, by rfl⟩ : syracuseStep 1547617 = 1160713) (by norm_num)
theorem B2063717 : Blo 1375507 2063717 := bbase (se 4 (by rfl) ⟨193473, by rfl⟩ : syracuseStep 2063717 = 386947) (by norm_num)
theorem B3095909 : Blo 1375507 3095909 := bbase (se 4 (by rfl) ⟨290241, by rfl⟩ : syracuseStep 3095909 = 580483) (by norm_num)
theorem B4472165 : Blo 1375507 4472165 := bbase (se 4 (by rfl) ⟨419265, by rfl⟩ : syracuseStep 4472165 = 838531) (by norm_num)
theorem B2063741 : Blo 1375507 2063741 := bbase (se 3 (by rfl) ⟨386951, by rfl⟩ : syracuseStep 2063741 = 773903) (by norm_num)
theorem B1547653 : Blo 1375507 1547653 := bbase (se 4 (by rfl) ⟨145092, by rfl⟩ : syracuseStep 1547653 = 290185) (by norm_num)
theorem B2063765 : Blo 1375507 2063765 := bbase (se 6 (by rfl) ⟨48369, by rfl⟩ : syracuseStep 2063765 = 96739) (by norm_num)
theorem B2612645 : Blo 1375507 2612645 := bbase (se 4 (by rfl) ⟨244935, by rfl⟩ : syracuseStep 2612645 = 489871) (by norm_num)
theorem B1547689 : Blo 1375507 1547689 := bbase (se 2 (by rfl) ⟨580383, by rfl⟩ : syracuseStep 1547689 = 1160767) (by norm_num)
theorem B2063789 : Blo 1375507 2063789 := bbase (se 3 (by rfl) ⟨386960, by rfl⟩ : syracuseStep 2063789 = 773921) (by norm_num)
theorem B3095981 : Blo 1375507 3095981 := bbase (se 3 (by rfl) ⟨580496, by rfl⟩ : syracuseStep 3095981 = 1160993) (by norm_num)
theorem B2063813 : Blo 1375507 2063813 := bbase (se 4 (by rfl) ⟨193482, by rfl⟩ : syracuseStep 2063813 = 386965) (by norm_num)
theorem B1547725 : Blo 1375507 1547725 := bbase (se 3 (by rfl) ⟨290198, by rfl⟩ : syracuseStep 1547725 = 580397) (by norm_num)
theorem B2063837 : Blo 1375507 2063837 := bbase (se 3 (by rfl) ⟨386969, by rfl⟩ : syracuseStep 2063837 = 773939) (by norm_num)
theorem B1547761 : Blo 1375507 1547761 := bbase (se 2 (by rfl) ⟨580410, by rfl⟩ : syracuseStep 1547761 = 1160821) (by norm_num)
theorem B2063861 : Blo 1375507 2063861 := bbase (se 5 (by rfl) ⟨96743, by rfl⟩ : syracuseStep 2063861 = 193487) (by norm_num)
theorem B3096053 : Blo 1375507 3096053 := bbase (se 5 (by rfl) ⟨145127, by rfl⟩ : syracuseStep 3096053 = 290255) (by norm_num)
theorem B2063885 : Blo 1375507 2063885 := bbase (se 3 (by rfl) ⟨386978, by rfl⟩ : syracuseStep 2063885 = 773957) (by norm_num)
theorem B1547797 : Blo 1375507 1547797 := bbase (se 6 (by rfl) ⟨36276, by rfl⟩ : syracuseStep 1547797 = 72553) (by norm_num)
theorem B2063909 : Blo 1375507 2063909 := bbase (se 4 (by rfl) ⟨193491, by rfl⟩ : syracuseStep 2063909 = 386983) (by norm_num)
theorem B1547833 : Blo 1375507 1547833 := bbase (se 2 (by rfl) ⟨580437, by rfl⟩ : syracuseStep 1547833 = 1160875) (by norm_num)
theorem B2063933 : Blo 1375507 2063933 := bbase (se 3 (by rfl) ⟨386987, by rfl⟩ : syracuseStep 2063933 = 773975) (by norm_num)
theorem B3096125 : Blo 1375507 3096125 := bbase (se 3 (by rfl) ⟨580523, by rfl⟩ : syracuseStep 3096125 = 1161047) (by norm_num)
theorem B2063957 : Blo 1375507 2063957 := bbase (se 8 (by rfl) ⟨12093, by rfl⟩ : syracuseStep 2063957 = 24187) (by norm_num)
theorem B1547869 : Blo 1375507 1547869 := bbase (se 3 (by rfl) ⟨290225, by rfl⟩ : syracuseStep 1547869 = 580451) (by norm_num)
theorem B2063981 : Blo 1375507 2063981 := bbase (se 3 (by rfl) ⟨386996, by rfl⟩ : syracuseStep 2063981 = 773993) (by norm_num)
theorem B1547905 : Blo 1375507 1547905 := bbase (se 2 (by rfl) ⟨580464, by rfl⟩ : syracuseStep 1547905 = 1160929) (by norm_num)
theorem B2064005 : Blo 1375507 2064005 := bbase (se 4 (by rfl) ⟨193500, by rfl⟩ : syracuseStep 2064005 = 387001) (by norm_num)
theorem B3096197 : Blo 1375507 3096197 := bbase (se 4 (by rfl) ⟨290268, by rfl⟩ : syracuseStep 3096197 = 580537) (by norm_num)
theorem B4644485 : Blo 1375507 4644485 := bbase (se 4 (by rfl) ⟨435420, by rfl⟩ : syracuseStep 4644485 = 870841) (by norm_num)
theorem B2981509 : Blo 1375507 2981509 := bbase (se 4 (by rfl) ⟨279516, by rfl⟩ : syracuseStep 2981509 = 559033) (by norm_num)
theorem B2064029 : Blo 1375507 2064029 := bbase (se 3 (by rfl) ⟨387005, by rfl⟩ : syracuseStep 2064029 = 774011) (by norm_num)
theorem B1547941 : Blo 1375507 1547941 := bbase (se 4 (by rfl) ⟨145119, by rfl⟩ : syracuseStep 1547941 = 290239) (by norm_num)
theorem B2064053 : Blo 1375507 2064053 := bbase (se 5 (by rfl) ⟨96752, by rfl⟩ : syracuseStep 2064053 = 193505) (by norm_num)
theorem B1547977 : Blo 1375507 1547977 := bbase (se 2 (by rfl) ⟨580491, by rfl⟩ : syracuseStep 1547977 = 1160983) (by norm_num)
theorem B2064077 : Blo 1375507 2064077 := bbase (se 3 (by rfl) ⟨387014, by rfl⟩ : syracuseStep 2064077 = 774029) (by norm_num)
theorem B3096269 : Blo 1375507 3096269 := bbase (se 3 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 3096269 = 1161101) (by norm_num)
theorem B2064101 : Blo 1375507 2064101 := bbase (se 4 (by rfl) ⟨193509, by rfl⟩ : syracuseStep 2064101 = 387019) (by norm_num)
theorem B1548013 : Blo 1375507 1548013 := bbase (se 3 (by rfl) ⟨290252, by rfl⟩ : syracuseStep 1548013 = 580505) (by norm_num)
theorem B2940661 : Blo 1375507 2940661 := bbase (se 5 (by rfl) ⟨137843, by rfl⟩ : syracuseStep 2940661 = 275687) (by norm_num)
theorem B2064125 : Blo 1375507 2064125 := bbase (se 3 (by rfl) ⟨387023, by rfl⟩ : syracuseStep 2064125 = 774047) (by norm_num)
theorem B1548049 : Blo 1375507 1548049 := bbase (se 2 (by rfl) ⟨580518, by rfl⟩ : syracuseStep 1548049 = 1161037) (by norm_num)
theorem B2064149 : Blo 1375507 2064149 := bbase (se 6 (by rfl) ⟨48378, by rfl⟩ : syracuseStep 2064149 = 96757) (by norm_num)
theorem B3096341 : Blo 1375507 3096341 := bbase (se 6 (by rfl) ⟨72570, by rfl⟩ : syracuseStep 3096341 = 145141) (by norm_num)
theorem B23518997 : Blo 1375507 23518997 := bbase (se 6 (by rfl) ⟨551226, by rfl⟩ : syracuseStep 23518997 = 1102453) (by norm_num)
theorem B2064173 : Blo 1375507 2064173 := bbase (se 3 (by rfl) ⟨387032, by rfl⟩ : syracuseStep 2064173 = 774065) (by norm_num)
theorem B1548085 : Blo 1375507 1548085 := bbase (se 5 (by rfl) ⟨72566, by rfl⟩ : syracuseStep 1548085 = 145133) (by norm_num)
theorem B2064197 : Blo 1375507 2064197 := bbase (se 4 (by rfl) ⟨193518, by rfl⟩ : syracuseStep 2064197 = 387037) (by norm_num)
theorem B2178893 : Blo 1375507 2178893 := bbase (se 3 (by rfl) ⟨408542, by rfl⟩ : syracuseStep 2178893 = 817085) (by norm_num)
theorem B1548121 : Blo 1375507 1548121 := bbase (se 2 (by rfl) ⟨580545, by rfl⟩ : syracuseStep 1548121 = 1161091) (by norm_num)
theorem B2064221 : Blo 1375507 2064221 := bbase (se 3 (by rfl) ⟨387041, by rfl⟩ : syracuseStep 2064221 = 774083) (by norm_num)
theorem B3096413 : Blo 1375507 3096413 := bbase (se 3 (by rfl) ⟨580577, by rfl⟩ : syracuseStep 3096413 = 1161155) (by norm_num)
theorem B2940781 : Blo 1375507 2940781 := bbase (se 3 (by rfl) ⟨551396, by rfl⟩ : syracuseStep 2940781 = 1102793) (by norm_num)
theorem B2064245 : Blo 1375507 2064245 := bbase (se 5 (by rfl) ⟨96761, by rfl⟩ : syracuseStep 2064245 = 193523) (by norm_num)
theorem B2203517 : Blo 1375507 2203517 := bbase (se 3 (by rfl) ⟨413159, by rfl⟩ : syracuseStep 2203517 = 826319) (by norm_num)
theorem B1548157 : Blo 1375507 1548157 := bbase (se 3 (by rfl) ⟨290279, by rfl⟩ : syracuseStep 1548157 = 580559) (by norm_num)
theorem B5881733 : Blo 1375507 5881733 := bbase (se 4 (by rfl) ⟨551412, by rfl⟩ : syracuseStep 5881733 = 1102825) (by norm_num)
theorem B2064269 : Blo 1375507 2064269 := bbase (se 3 (by rfl) ⟨387050, by rfl⟩ : syracuseStep 2064269 = 774101) (by norm_num)
theorem B1548193 : Blo 1375507 1548193 := bbase (se 2 (by rfl) ⟨580572, by rfl⟩ : syracuseStep 1548193 = 1161145) (by norm_num)
theorem B2064293 : Blo 1375507 2064293 := bbase (se 4 (by rfl) ⟨193527, by rfl⟩ : syracuseStep 2064293 = 387055) (by norm_num)
theorem B3096485 : Blo 1375507 3096485 := bbase (se 4 (by rfl) ⟨290295, by rfl⟩ : syracuseStep 3096485 = 580591) (by norm_num)
theorem B2064317 : Blo 1375507 2064317 := bbase (se 3 (by rfl) ⟨387059, by rfl⟩ : syracuseStep 2064317 = 774119) (by norm_num)
theorem B1548229 : Blo 1375507 1548229 := bbase (se 4 (by rfl) ⟨145146, by rfl⟩ : syracuseStep 1548229 = 290293) (by norm_num)
theorem B2064341 : Blo 1375507 2064341 := bbase (se 7 (by rfl) ⟨24191, by rfl⟩ : syracuseStep 2064341 = 48383) (by norm_num)
theorem B1548265 : Blo 1375507 1548265 := bbase (se 2 (by rfl) ⟨580599, by rfl⟩ : syracuseStep 1548265 = 1161199) (by norm_num)
theorem B2064365 : Blo 1375507 2064365 := bbase (se 3 (by rfl) ⟨387068, by rfl⟩ : syracuseStep 2064365 = 774137) (by norm_num)
theorem B3096557 : Blo 1375507 3096557 := bbase (se 3 (by rfl) ⟨580604, by rfl⟩ : syracuseStep 3096557 = 1161209) (by norm_num)
theorem B1376259 : Blo 1375507 1376259 := bstep (se 1 (by rfl) ⟨1032194, by rfl⟩ : syracuseStep 1376259 = 2064389) B2064389
theorem B3096593 : Blo 1375507 3096593 := bstep (se 2 (by rfl) ⟨1161222, by rfl⟩ : syracuseStep 3096593 = 2322445) B2322445
theorem B2064401 : Blo 1375507 2064401 := bstep (se 2 (by rfl) ⟨774150, by rfl⟩ : syracuseStep 2064401 = 1548301) B1548301
theorem B1376275 : Blo 1375507 1376275 := bstep (se 1 (by rfl) ⟨1032206, by rfl⟩ : syracuseStep 1376275 = 2064413) B2064413
theorem B3096611 : Blo 1375507 3096611 := bstep (se 1 (by rfl) ⟨2322458, by rfl⟩ : syracuseStep 3096611 = 4644917) B4644917
theorem B2064419 : Blo 1375507 2064419 := bstep (se 1 (by rfl) ⟨1548314, by rfl⟩ : syracuseStep 2064419 = 3096629) B3096629
theorem B1376291 : Blo 1375507 1376291 := bstep (se 1 (by rfl) ⟨1032218, by rfl⟩ : syracuseStep 1376291 = 2064437) B2064437
theorem B1376307 : Blo 1375507 1376307 := bstep (se 1 (by rfl) ⟨1032230, by rfl⟩ : syracuseStep 1376307 = 2064461) B2064461
theorem B2064449 : Blo 1375507 2064449 := bstep (se 2 (by rfl) ⟨774168, by rfl⟩ : syracuseStep 2064449 = 1548337) B1548337
theorem B1548355 : Blo 1375507 1548355 := bstep (se 1 (by rfl) ⟨1161266, by rfl⟩ : syracuseStep 1548355 = 2322533) B2322533
theorem B1376323 : Blo 1375507 1376323 := bstep (se 1 (by rfl) ⟨1032242, by rfl⟩ : syracuseStep 1376323 = 2064485) B2064485
theorem B2064467 : Blo 1375507 2064467 := bstep (se 1 (by rfl) ⟨1548350, by rfl⟩ : syracuseStep 2064467 = 3096701) B3096701
theorem B1376339 : Blo 1375507 1376339 := bstep (se 1 (by rfl) ⟨1032254, by rfl⟩ : syracuseStep 1376339 = 2064509) B2064509
theorem B6275171 : Blo 1375507 6275171 := bstep (se 1 (by rfl) ⟨4706378, by rfl⟩ : syracuseStep 6275171 = 9412757) B9412757
theorem B1376355 : Blo 1375507 1376355 := bstep (se 1 (by rfl) ⟨1032266, by rfl⟩ : syracuseStep 1376355 = 2064533) B2064533
theorem B2064497 : Blo 1375507 2064497 := bstep (se 2 (by rfl) ⟨774186, by rfl⟩ : syracuseStep 2064497 = 1548373) B1548373
theorem B1376371 : Blo 1375507 1376371 := bstep (se 1 (by rfl) ⟨1032278, by rfl⟩ : syracuseStep 1376371 = 2064557) B2064557
theorem B2064515 : Blo 1375507 2064515 := bstep (se 1 (by rfl) ⟨1548386, by rfl⟩ : syracuseStep 2064515 = 3096773) B3096773
theorem B1376387 : Blo 1375507 1376387 := bstep (se 1 (by rfl) ⟨1032290, by rfl⟩ : syracuseStep 1376387 = 2064581) B2064581
theorem B1376403 : Blo 1375507 1376403 := bstep (se 1 (by rfl) ⟨1032302, by rfl⟩ : syracuseStep 1376403 = 2064605) B2064605
theorem B2064545 : Blo 1375507 2064545 := bstep (se 2 (by rfl) ⟨774204, by rfl⟩ : syracuseStep 2064545 = 1548409) B1548409
theorem B1376419 : Blo 1375507 1376419 := bstep (se 1 (by rfl) ⟨1032314, by rfl⟩ : syracuseStep 1376419 = 2064629) B2064629
theorem B2121889 : Blo 1375507 2121889 := bstep (se 2 (by rfl) ⟨795708, by rfl⟩ : syracuseStep 2121889 = 1591417) B1591417
theorem B2941105 : Blo 1375507 2941105 := bstep (se 2 (by rfl) ⟨1102914, by rfl⟩ : syracuseStep 2941105 = 2205829) B2205829
theorem B2064563 : Blo 1375507 2064563 := bstep (se 1 (by rfl) ⟨1548422, by rfl⟩ : syracuseStep 2064563 = 3096845) B3096845
theorem B1376435 : Blo 1375507 1376435 := bstep (se 1 (by rfl) ⟨1032326, by rfl⟩ : syracuseStep 1376435 = 2064653) B2064653
theorem B2203843 : Blo 1375507 2203843 := bstep (se 1 (by rfl) ⟨1652882, by rfl⟩ : syracuseStep 2203843 = 3305765) B3305765
theorem B1376451 : Blo 1375507 1376451 := bstep (se 1 (by rfl) ⟨1032338, by rfl⟩ : syracuseStep 1376451 = 2064677) B2064677
theorem B2941123 : Blo 1375507 2941123 := bstep (se 1 (by rfl) ⟨2205842, by rfl⟩ : syracuseStep 2941123 = 4411685) B4411685
theorem B2064593 : Blo 1375507 2064593 := bstep (se 2 (by rfl) ⟨774222, by rfl⟩ : syracuseStep 2064593 = 1548445) B1548445
theorem B1548499 : Blo 1375507 1548499 := bstep (se 1 (by rfl) ⟨1161374, by rfl⟩ : syracuseStep 1548499 = 2322749) B2322749
theorem B1376467 : Blo 1375507 1376467 := bstep (se 1 (by rfl) ⟨1032350, by rfl⟩ : syracuseStep 1376467 = 2064701) B2064701
theorem B2064611 : Blo 1375507 2064611 := bstep (se 1 (by rfl) ⟨1548458, by rfl⟩ : syracuseStep 2064611 = 3096917) B3096917
theorem B1376483 : Blo 1375507 1376483 := bstep (se 1 (by rfl) ⟨1032362, by rfl⟩ : syracuseStep 1376483 = 2064725) B2064725
theorem B17645809 : Blo 1375507 17645809 := bstep (se 2 (by rfl) ⟨6617178, by rfl⟩ : syracuseStep 17645809 = 13234357) B13234357
theorem B1376499 : Blo 1375507 1376499 := bstep (se 1 (by rfl) ⟨1032374, by rfl⟩ : syracuseStep 1376499 = 2064749) B2064749
theorem B2064641 : Blo 1375507 2064641 := bstep (se 2 (by rfl) ⟨774240, by rfl⟩ : syracuseStep 2064641 = 1548481) B1548481
theorem B1376515 : Blo 1375507 1376515 := bstep (se 1 (by rfl) ⟨1032386, by rfl⟩ : syracuseStep 1376515 = 2064773) B2064773
theorem B4645133 : Blo 1375507 4645133 := bstep (se 3 (by rfl) ⟨870962, by rfl⟩ : syracuseStep 4645133 = 1741925) B1741925
theorem B2064659 : Blo 1375507 2064659 := bstep (se 1 (by rfl) ⟨1548494, by rfl⟩ : syracuseStep 2064659 = 3096989) B3096989
theorem B1376531 : Blo 1375507 1376531 := bstep (se 1 (by rfl) ⟨1032398, by rfl⟩ : syracuseStep 1376531 = 2064797) B2064797
theorem B1376547 : Blo 1375507 1376547 := bstep (se 1 (by rfl) ⟨1032410, by rfl⟩ : syracuseStep 1376547 = 2064821) B2064821
theorem B3096881 : Blo 1375507 3096881 := bstep (se 2 (by rfl) ⟨1161330, by rfl⟩ : syracuseStep 3096881 = 2322661) B2322661
theorem B2064689 : Blo 1375507 2064689 := bstep (se 2 (by rfl) ⟨774258, by rfl⟩ : syracuseStep 2064689 = 1548517) B1548517
theorem B1376563 : Blo 1375507 1376563 := bstep (se 1 (by rfl) ⟨1032422, by rfl⟩ : syracuseStep 1376563 = 2064845) B2064845
theorem B4645187 : Blo 1375507 4645187 := bstep (se 1 (by rfl) ⟨3483890, by rfl⟩ : syracuseStep 4645187 = 6967781) B6967781
theorem B3096899 : Blo 1375507 3096899 := bstep (se 1 (by rfl) ⟨2322674, by rfl⟩ : syracuseStep 3096899 = 4645349) B4645349
theorem B11911493 : Blo 1375507 11911493 := bstep (se 4 (by rfl) ⟨1116702, by rfl⟩ : syracuseStep 11911493 = 2233405) B2233405
theorem B2064707 : Blo 1375507 2064707 := bstep (se 1 (by rfl) ⟨1548530, by rfl⟩ : syracuseStep 2064707 = 3097061) B3097061
theorem B1376579 : Blo 1375507 1376579 := bstep (se 1 (by rfl) ⟨1032434, by rfl⟩ : syracuseStep 1376579 = 2064869) B2064869
theorem B3481937 : Blo 1375507 3481937 := bstep (se 2 (by rfl) ⟨1305726, by rfl⟩ : syracuseStep 3481937 = 2611453) B2611453
theorem B1376595 : Blo 1375507 1376595 := bstep (se 1 (by rfl) ⟨1032446, by rfl⟩ : syracuseStep 1376595 = 2064893) B2064893
theorem B2064737 : Blo 1375507 2064737 := bstep (se 2 (by rfl) ⟨774276, by rfl⟩ : syracuseStep 2064737 = 1548553) B1548553
theorem B1548643 : Blo 1375507 1548643 := bstep (se 1 (by rfl) ⟨1161482, by rfl⟩ : syracuseStep 1548643 = 2322965) B2322965
theorem B1376611 : Blo 1375507 1376611 := bstep (se 1 (by rfl) ⟨1032458, by rfl⟩ : syracuseStep 1376611 = 2064917) B2064917
theorem B6963569 : Blo 1375507 6963569 := bstep (se 2 (by rfl) ⟨2611338, by rfl⟩ : syracuseStep 6963569 = 5222677) B5222677
theorem B2613617 : Blo 1375507 2613617 := bstep (se 2 (by rfl) ⟨980106, by rfl⟩ : syracuseStep 2613617 = 1960213) B1960213
theorem B2064755 : Blo 1375507 2064755 := bstep (se 1 (by rfl) ⟨1548566, by rfl⟩ : syracuseStep 2064755 = 3097133) B3097133
theorem B1376627 : Blo 1375507 1376627 := bstep (se 1 (by rfl) ⟨1032470, by rfl⟩ : syracuseStep 1376627 = 2064941) B2064941
theorem B3481987 : Blo 1375507 3481987 := bstep (se 1 (by rfl) ⟨2611490, by rfl⟩ : syracuseStep 3481987 = 5222981) B5222981
theorem B1376643 : Blo 1375507 1376643 := bstep (se 1 (by rfl) ⟨1032482, by rfl⟩ : syracuseStep 1376643 = 2064965) B2064965
theorem B2064785 : Blo 1375507 2064785 := bstep (se 2 (by rfl) ⟨774294, by rfl⟩ : syracuseStep 2064785 = 1548589) B1548589
theorem B1376659 : Blo 1375507 1376659 := bstep (se 1 (by rfl) ⟨1032494, by rfl⟩ : syracuseStep 1376659 = 2064989) B2064989
theorem B2064803 : Blo 1375507 2064803 := bstep (se 1 (by rfl) ⟨1548602, by rfl⟩ : syracuseStep 2064803 = 3097205) B3097205
theorem B1376675 : Blo 1375507 1376675 := bstep (se 1 (by rfl) ⟨1032506, by rfl⟩ : syracuseStep 1376675 = 2065013) B2065013
theorem B2204081 : Blo 1375507 2204081 := bstep (se 2 (by rfl) ⟨826530, by rfl⟩ : syracuseStep 2204081 = 1653061) B1653061
theorem B1376691 : Blo 1375507 1376691 := bstep (se 1 (by rfl) ⟨1032518, by rfl⟩ : syracuseStep 1376691 = 2065037) B2065037
theorem B2064833 : Blo 1375507 2064833 := bstep (se 2 (by rfl) ⟨774312, by rfl⟩ : syracuseStep 2064833 = 1548625) B1548625
theorem B1376707 : Blo 1375507 1376707 := bstep (se 1 (by rfl) ⟨1032530, by rfl⟩ : syracuseStep 1376707 = 2065061) B2065061
theorem B2064851 : Blo 1375507 2064851 := bstep (se 1 (by rfl) ⟨1548638, by rfl⟩ : syracuseStep 2064851 = 3097277) B3097277
theorem B1376723 : Blo 1375507 1376723 := bstep (se 1 (by rfl) ⟨1032542, by rfl⟩ : syracuseStep 1376723 = 2065085) B2065085
theorem B1376739 : Blo 1375507 1376739 := bstep (se 1 (by rfl) ⟨1032554, by rfl⟩ : syracuseStep 1376739 = 2065109) B2065109
theorem B2064881 : Blo 1375507 2064881 := bstep (se 2 (by rfl) ⟨774330, by rfl⟩ : syracuseStep 2064881 = 1548661) B1548661
theorem B1548787 : Blo 1375507 1548787 := bstep (se 1 (by rfl) ⟨1161590, by rfl⟩ : syracuseStep 1548787 = 2323181) B2323181
theorem B1376755 : Blo 1375507 1376755 := bstep (se 1 (by rfl) ⟨1032566, by rfl⟩ : syracuseStep 1376755 = 2065133) B2065133
theorem B2064899 : Blo 1375507 2064899 := bstep (se 1 (by rfl) ⟨1548674, by rfl⟩ : syracuseStep 2064899 = 3097349) B3097349
theorem B1376771 : Blo 1375507 1376771 := bstep (se 1 (by rfl) ⟨1032578, by rfl⟩ : syracuseStep 1376771 = 2065157) B2065157
theorem B7062029 : Blo 1375507 7062029 := bstep (se 3 (by rfl) ⟨1324130, by rfl⟩ : syracuseStep 7062029 = 2648261) B2648261
theorem B3482129 : Blo 1375507 3482129 := bstep (se 2 (by rfl) ⟨1305798, by rfl⟩ : syracuseStep 3482129 = 2611597) B2611597
theorem B1376787 : Blo 1375507 1376787 := bstep (se 1 (by rfl) ⟨1032590, by rfl⟩ : syracuseStep 1376787 = 2065181) B2065181
theorem B2064929 : Blo 1375507 2064929 := bstep (se 2 (by rfl) ⟨774348, by rfl⟩ : syracuseStep 2064929 = 1548697) B1548697
theorem B1860131 : Blo 1375507 1860131 := bstep (se 1 (by rfl) ⟨1395098, by rfl⟩ : syracuseStep 1860131 = 2790197) B2790197
theorem B1376803 : Blo 1375507 1376803 := bstep (se 1 (by rfl) ⟨1032602, by rfl⟩ : syracuseStep 1376803 = 2065205) B2065205
theorem B4407853 : Blo 1375507 4407853 := bstep (se 3 (by rfl) ⟨826472, by rfl⟩ : syracuseStep 4407853 = 1652945) B1652945
theorem B2064947 : Blo 1375507 2064947 := bstep (se 1 (by rfl) ⟨1548710, by rfl⟩ : syracuseStep 2064947 = 3097421) B3097421
theorem B1376819 : Blo 1375507 1376819 := bstep (se 1 (by rfl) ⟨1032614, by rfl⟩ : syracuseStep 1376819 = 2065229) B2065229
theorem B1376835 : Blo 1375507 1376835 := bstep (se 1 (by rfl) ⟨1032626, by rfl⟩ : syracuseStep 1376835 = 2065253) B2065253
theorem B4645457 : Blo 1375507 4645457 := bstep (se 2 (by rfl) ⟨1742046, by rfl⟩ : syracuseStep 4645457 = 3484093) B3484093
theorem B3097169 : Blo 1375507 3097169 := bstep (se 2 (by rfl) ⟨1161438, by rfl⟩ : syracuseStep 3097169 = 2322877) B2322877
theorem B2064977 : Blo 1375507 2064977 := bstep (se 2 (by rfl) ⟨774366, by rfl⟩ : syracuseStep 2064977 = 1548733) B1548733
theorem B1376851 : Blo 1375507 1376851 := bstep (se 1 (by rfl) ⟨1032638, by rfl⟩ : syracuseStep 1376851 = 2065277) B2065277
theorem B3097187 : Blo 1375507 3097187 := bstep (se 1 (by rfl) ⟨2322890, by rfl⟩ : syracuseStep 3097187 = 4645781) B4645781
theorem B2064995 : Blo 1375507 2064995 := bstep (se 1 (by rfl) ⟨1548746, by rfl⟩ : syracuseStep 2064995 = 3097493) B3097493
theorem B1376867 : Blo 1375507 1376867 := bstep (se 1 (by rfl) ⟨1032650, by rfl⟩ : syracuseStep 1376867 = 2065301) B2065301
theorem B1376883 : Blo 1375507 1376883 := bstep (se 1 (by rfl) ⟨1032662, by rfl⟩ : syracuseStep 1376883 = 2065325) B2065325
theorem B2065025 : Blo 1375507 2065025 := bstep (se 2 (by rfl) ⟨774384, by rfl⟩ : syracuseStep 2065025 = 1548769) B1548769
theorem B2204291 : Blo 1375507 2204291 := bstep (se 1 (by rfl) ⟨1653218, by rfl⟩ : syracuseStep 2204291 = 3306437) B3306437
theorem B1548931 : Blo 1375507 1548931 := bstep (se 1 (by rfl) ⟨1161698, by rfl⟩ : syracuseStep 1548931 = 2323397) B2323397
theorem B1376899 : Blo 1375507 1376899 := bstep (se 1 (by rfl) ⟨1032674, by rfl⟩ : syracuseStep 1376899 = 2065349) B2065349
theorem B2065043 : Blo 1375507 2065043 := bstep (se 1 (by rfl) ⟨1548782, by rfl⟩ : syracuseStep 2065043 = 3097565) B3097565
theorem B1376915 : Blo 1375507 1376915 := bstep (se 1 (by rfl) ⟨1032686, by rfl⟩ : syracuseStep 1376915 = 2065373) B2065373
theorem B1376931 : Blo 1375507 1376931 := bstep (se 1 (by rfl) ⟨1032698, by rfl⟩ : syracuseStep 1376931 = 2065397) B2065397
theorem B2065073 : Blo 1375507 2065073 := bstep (se 2 (by rfl) ⟨774402, by rfl⟩ : syracuseStep 2065073 = 1548805) B1548805
theorem B1376947 : Blo 1375507 1376947 := bstep (se 1 (by rfl) ⟨1032710, by rfl⟩ : syracuseStep 1376947 = 2065421) B2065421
theorem B2065091 : Blo 1375507 2065091 := bstep (se 1 (by rfl) ⟨1548818, by rfl⟩ : syracuseStep 2065091 = 3097637) B3097637
theorem B1376963 : Blo 1375507 1376963 := bstep (se 1 (by rfl) ⟨1032722, by rfl⟩ : syracuseStep 1376963 = 2065445) B2065445
theorem B15901381 : Blo 1375507 15901381 := bstep (se 4 (by rfl) ⟨1490754, by rfl⟩ : syracuseStep 15901381 = 2981509) B2981509
theorem B1376979 : Blo 1375507 1376979 := bstep (se 1 (by rfl) ⟨1032734, by rfl⟩ : syracuseStep 1376979 = 2065469) B2065469
theorem B2065121 : Blo 1375507 2065121 := bstep (se 2 (by rfl) ⟨774420, by rfl⟩ : syracuseStep 2065121 = 1548841) B1548841
theorem B1376995 : Blo 1375507 1376995 := bstep (se 1 (by rfl) ⟨1032746, by rfl⟩ : syracuseStep 1376995 = 2065493) B2065493
theorem B2065139 : Blo 1375507 2065139 := bstep (se 1 (by rfl) ⟨1548854, by rfl⟩ : syracuseStep 2065139 = 3097709) B3097709
theorem B1377011 : Blo 1375507 1377011 := bstep (se 1 (by rfl) ⟨1032758, by rfl⟩ : syracuseStep 1377011 = 2065517) B2065517
theorem B1377027 : Blo 1375507 1377027 := bstep (se 1 (by rfl) ⟨1032770, by rfl⟩ : syracuseStep 1377027 = 2065541) B2065541
theorem B2065169 : Blo 1375507 2065169 := bstep (se 2 (by rfl) ⟨774438, by rfl⟩ : syracuseStep 2065169 = 1548877) B1548877
theorem B1549075 : Blo 1375507 1549075 := bstep (se 1 (by rfl) ⟨1161806, by rfl⟩ : syracuseStep 1549075 = 2323613) B2323613
theorem B1377043 : Blo 1375507 1377043 := bstep (se 1 (by rfl) ⟨1032782, by rfl⟩ : syracuseStep 1377043 = 2065565) B2065565
theorem B2065187 : Blo 1375507 2065187 := bstep (se 1 (by rfl) ⟨1548890, by rfl⟩ : syracuseStep 2065187 = 3097781) B3097781
theorem B1377059 : Blo 1375507 1377059 := bstep (se 1 (by rfl) ⟨1032794, by rfl⟩ : syracuseStep 1377059 = 2065589) B2065589
theorem B1377075 : Blo 1375507 1377075 := bstep (se 1 (by rfl) ⟨1032806, by rfl⟩ : syracuseStep 1377075 = 2065613) B2065613
theorem B2065217 : Blo 1375507 2065217 := bstep (se 2 (by rfl) ⟨774456, by rfl⟩ : syracuseStep 2065217 = 1548913) B1548913
theorem B1377091 : Blo 1375507 1377091 := bstep (se 1 (by rfl) ⟨1032818, by rfl⟩ : syracuseStep 1377091 = 2065637) B2065637
theorem B2065235 : Blo 1375507 2065235 := bstep (se 1 (by rfl) ⟨1548926, by rfl⟩ : syracuseStep 2065235 = 3097853) B3097853
theorem B1377107 : Blo 1375507 1377107 := bstep (se 1 (by rfl) ⟨1032830, by rfl⟩ : syracuseStep 1377107 = 2065661) B2065661
theorem B1958755 : Blo 1375507 1958755 := bstep (se 1 (by rfl) ⟨1469066, by rfl⟩ : syracuseStep 1958755 = 2938133) B2938133
theorem B10453859 : Blo 1375507 10453859 := bstep (se 1 (by rfl) ⟨7840394, by rfl⟩ : syracuseStep 10453859 = 15680789) B15680789
theorem B1377123 : Blo 1375507 1377123 := bstep (se 1 (by rfl) ⟨1032842, by rfl⟩ : syracuseStep 1377123 = 2065685) B2065685
theorem B3097457 : Blo 1375507 3097457 := bstep (se 2 (by rfl) ⟨1161546, by rfl⟩ : syracuseStep 3097457 = 2323093) B2323093
theorem B2065265 : Blo 1375507 2065265 := bstep (se 2 (by rfl) ⟨774474, by rfl⟩ : syracuseStep 2065265 = 1548949) B1548949
theorem B1377139 : Blo 1375507 1377139 := bstep (se 1 (by rfl) ⟨1032854, by rfl⟩ : syracuseStep 1377139 = 2065709) B2065709
theorem B3097475 : Blo 1375507 3097475 := bstep (se 1 (by rfl) ⟨2323106, by rfl⟩ : syracuseStep 3097475 = 4646213) B4646213
theorem B2065283 : Blo 1375507 2065283 := bstep (se 1 (by rfl) ⟨1548962, by rfl⟩ : syracuseStep 2065283 = 3097925) B3097925
theorem B1377155 : Blo 1375507 1377155 := bstep (se 1 (by rfl) ⟨1032866, by rfl⟩ : syracuseStep 1377155 = 2065733) B2065733
theorem B1377171 : Blo 1375507 1377171 := bstep (se 1 (by rfl) ⟨1032878, by rfl⟩ : syracuseStep 1377171 = 2065757) B2065757
theorem B2065313 : Blo 1375507 2065313 := bstep (se 2 (by rfl) ⟨774492, by rfl⟩ : syracuseStep 2065313 = 1548985) B1548985
theorem B1549219 : Blo 1375507 1549219 := bstep (se 1 (by rfl) ⟨1161914, by rfl⟩ : syracuseStep 1549219 = 2323829) B2323829
theorem B1377187 : Blo 1375507 1377187 := bstep (se 1 (by rfl) ⟨1032890, by rfl⟩ : syracuseStep 1377187 = 2065781) B2065781
theorem B2065331 : Blo 1375507 2065331 := bstep (se 1 (by rfl) ⟨1548998, by rfl⟩ : syracuseStep 2065331 = 3097997) B3097997
theorem B1377203 : Blo 1375507 1377203 := bstep (se 1 (by rfl) ⟨1032902, by rfl⟩ : syracuseStep 1377203 = 2065805) B2065805
theorem B1377219 : Blo 1375507 1377219 := bstep (se 1 (by rfl) ⟨1032914, by rfl⟩ : syracuseStep 1377219 = 2065829) B2065829
theorem B2065361 : Blo 1375507 2065361 := bstep (se 2 (by rfl) ⟨774510, by rfl⟩ : syracuseStep 2065361 = 1549021) B1549021
theorem B1377235 : Blo 1375507 1377235 := bstep (se 1 (by rfl) ⟨1032926, by rfl⟩ : syracuseStep 1377235 = 2065853) B2065853
theorem B2065379 : Blo 1375507 2065379 := bstep (se 1 (by rfl) ⟨1549034, by rfl⟩ : syracuseStep 2065379 = 3098069) B3098069
theorem B1377251 : Blo 1375507 1377251 := bstep (se 1 (by rfl) ⟨1032938, by rfl⟩ : syracuseStep 1377251 = 2065877) B2065877
theorem B1377267 : Blo 1375507 1377267 := bstep (se 1 (by rfl) ⟨1032950, by rfl⟩ : syracuseStep 1377267 = 2065901) B2065901
theorem B2065409 : Blo 1375507 2065409 := bstep (se 2 (by rfl) ⟨774528, by rfl⟩ : syracuseStep 2065409 = 1549057) B1549057
theorem B1377283 : Blo 1375507 1377283 := bstep (se 1 (by rfl) ⟨1032962, by rfl⟩ : syracuseStep 1377283 = 2065925) B2065925
theorem B2065427 : Blo 1375507 2065427 := bstep (se 1 (by rfl) ⟨1549070, by rfl⟩ : syracuseStep 2065427 = 3098141) B3098141
theorem B1377299 : Blo 1375507 1377299 := bstep (se 1 (by rfl) ⟨1032974, by rfl⟩ : syracuseStep 1377299 = 2065949) B2065949
theorem B1377315 : Blo 1375507 1377315 := bstep (se 1 (by rfl) ⟨1032986, by rfl⟩ : syracuseStep 1377315 = 2065973) B2065973
theorem B2065457 : Blo 1375507 2065457 := bstep (se 2 (by rfl) ⟨774546, by rfl⟩ : syracuseStep 2065457 = 1549093) B1549093
theorem B1549363 : Blo 1375507 1549363 := bstep (se 1 (by rfl) ⟨1162022, by rfl⟩ : syracuseStep 1549363 = 2324045) B2324045
theorem B1377331 : Blo 1375507 1377331 := bstep (se 1 (by rfl) ⟨1032998, by rfl⟩ : syracuseStep 1377331 = 2065997) B2065997
theorem B2065475 : Blo 1375507 2065475 := bstep (se 1 (by rfl) ⟨1549106, by rfl⟩ : syracuseStep 2065475 = 3098213) B3098213
theorem B1377347 : Blo 1375507 1377347 := bstep (se 1 (by rfl) ⟨1033010, by rfl⟩ : syracuseStep 1377347 = 2066021) B2066021
theorem B1377363 : Blo 1375507 1377363 := bstep (se 1 (by rfl) ⟨1033022, by rfl⟩ : syracuseStep 1377363 = 2066045) B2066045
theorem B2065505 : Blo 1375507 2065505 := bstep (se 2 (by rfl) ⟨774564, by rfl⟩ : syracuseStep 2065505 = 1549129) B1549129
theorem B1377379 : Blo 1375507 1377379 := bstep (se 1 (by rfl) ⟨1033034, by rfl⟩ : syracuseStep 1377379 = 2066069) B2066069
theorem B4645997 : Blo 1375507 4645997 := bstep (se 3 (by rfl) ⟨871124, by rfl⟩ : syracuseStep 4645997 = 1742249) B1742249
theorem B8815729 : Blo 1375507 8815729 := bstep (se 2 (by rfl) ⟨3305898, by rfl⟩ : syracuseStep 8815729 = 6611797) B6611797
theorem B2065523 : Blo 1375507 2065523 := bstep (se 1 (by rfl) ⟨1549142, by rfl⟩ : syracuseStep 2065523 = 3098285) B3098285
theorem B1377395 : Blo 1375507 1377395 := bstep (se 1 (by rfl) ⟨1033046, by rfl⟩ : syracuseStep 1377395 = 2066093) B2066093
theorem B3531907 : Blo 1375507 3531907 := bstep (se 1 (by rfl) ⟨2648930, by rfl⟩ : syracuseStep 3531907 = 5297861) B5297861
theorem B1377411 : Blo 1375507 1377411 := bstep (se 1 (by rfl) ⟨1033058, by rfl⟩ : syracuseStep 1377411 = 2066117) B2066117
theorem B3097745 : Blo 1375507 3097745 := bstep (se 2 (by rfl) ⟨1161654, by rfl⟩ : syracuseStep 3097745 = 2323309) B2323309
theorem B2065553 : Blo 1375507 2065553 := bstep (se 2 (by rfl) ⟨774582, by rfl⟩ : syracuseStep 2065553 = 1549165) B1549165
theorem B1377427 : Blo 1375507 1377427 := bstep (se 1 (by rfl) ⟨1033070, by rfl⟩ : syracuseStep 1377427 = 2066141) B2066141
theorem B4646051 : Blo 1375507 4646051 := bstep (se 1 (by rfl) ⟨3484538, by rfl⟩ : syracuseStep 4646051 = 6969077) B6969077
theorem B3097763 : Blo 1375507 3097763 := bstep (se 1 (by rfl) ⟨2323322, by rfl⟩ : syracuseStep 3097763 = 4646645) B4646645
theorem B2065571 : Blo 1375507 2065571 := bstep (se 1 (by rfl) ⟨1549178, by rfl⟩ : syracuseStep 2065571 = 3098357) B3098357
theorem B1377443 : Blo 1375507 1377443 := bstep (se 1 (by rfl) ⟨1033082, by rfl⟩ : syracuseStep 1377443 = 2066165) B2066165
theorem B1377459 : Blo 1375507 1377459 := bstep (se 1 (by rfl) ⟨1033094, by rfl⟩ : syracuseStep 1377459 = 2066189) B2066189
theorem B2065601 : Blo 1375507 2065601 := bstep (se 2 (by rfl) ⟨774600, by rfl⟩ : syracuseStep 2065601 = 1549201) B1549201
theorem B1549507 : Blo 1375507 1549507 := bstep (se 1 (by rfl) ⟨1162130, by rfl⟩ : syracuseStep 1549507 = 2324261) B2324261
theorem B1377475 : Blo 1375507 1377475 := bstep (se 1 (by rfl) ⟨1033106, by rfl⟩ : syracuseStep 1377475 = 2066213) B2066213
theorem B2065619 : Blo 1375507 2065619 := bstep (se 1 (by rfl) ⟨1549214, by rfl⟩ : syracuseStep 2065619 = 3098429) B3098429
theorem B1377491 : Blo 1375507 1377491 := bstep (se 1 (by rfl) ⟨1033118, by rfl⟩ : syracuseStep 1377491 = 2066237) B2066237
theorem B1377507 : Blo 1375507 1377507 := bstep (se 1 (by rfl) ⟨1033130, by rfl⟩ : syracuseStep 1377507 = 2066261) B2066261
theorem B2065649 : Blo 1375507 2065649 := bstep (se 2 (by rfl) ⟨774618, by rfl⟩ : syracuseStep 2065649 = 1549237) B1549237
theorem B2614513 : Blo 1375507 2614513 := bstep (se 2 (by rfl) ⟨980442, by rfl⟩ : syracuseStep 2614513 = 1960885) B1960885
theorem B2065667 : Blo 1375507 2065667 := bstep (se 1 (by rfl) ⟨1549250, by rfl⟩ : syracuseStep 2065667 = 3098501) B3098501
theorem B2065697 : Blo 1375507 2065697 := bstep (se 2 (by rfl) ⟨774636, by rfl⟩ : syracuseStep 2065697 = 1549273) B1549273
theorem B5227811 : Blo 1375507 5227811 := bstep (se 1 (by rfl) ⟨3920858, by rfl⟩ : syracuseStep 5227811 = 7841717) B7841717
theorem B2065715 : Blo 1375507 2065715 := bstep (se 1 (by rfl) ⟨1549286, by rfl⟩ : syracuseStep 2065715 = 3098573) B3098573
theorem B1959233 : Blo 1375507 1959233 := bstep (se 2 (by rfl) ⟨734712, by rfl⟩ : syracuseStep 1959233 = 1469425) B1469425
theorem B3917123 : Blo 1375507 3917123 := bstep (se 1 (by rfl) ⟨2937842, by rfl⟩ : syracuseStep 3917123 = 5875685) B5875685
theorem B2065745 : Blo 1375507 2065745 := bstep (se 2 (by rfl) ⟨774654, by rfl⟩ : syracuseStep 2065745 = 1549309) B1549309
theorem B1549651 : Blo 1375507 1549651 := bstep (se 1 (by rfl) ⟨1162238, by rfl⟩ : syracuseStep 1549651 = 2324477) B2324477
theorem B2065763 : Blo 1375507 2065763 := bstep (se 1 (by rfl) ⟨1549322, by rfl⟩ : syracuseStep 2065763 = 3098645) B3098645
theorem B4408685 : Blo 1375507 4408685 := bstep (se 3 (by rfl) ⟨826628, by rfl⟩ : syracuseStep 4408685 = 1653257) B1653257
theorem B2065793 : Blo 1375507 2065793 := bstep (se 2 (by rfl) ⟨774672, by rfl⟩ : syracuseStep 2065793 = 1549345) B1549345
theorem B2205073 : Blo 1375507 2205073 := bstep (se 2 (by rfl) ⟨826902, by rfl⟩ : syracuseStep 2205073 = 1653805) B1653805
theorem B2614673 : Blo 1375507 2614673 := bstep (se 2 (by rfl) ⟨980502, by rfl⟩ : syracuseStep 2614673 = 1961005) B1961005
theorem B2065811 : Blo 1375507 2065811 := bstep (se 1 (by rfl) ⟨1549358, by rfl⟩ : syracuseStep 2065811 = 3098717) B3098717
theorem B4646321 : Blo 1375507 4646321 := bstep (se 2 (by rfl) ⟨1742370, by rfl⟩ : syracuseStep 4646321 = 3484741) B3484741
theorem B3098033 : Blo 1375507 3098033 := bstep (se 2 (by rfl) ⟨1161762, by rfl⟩ : syracuseStep 3098033 = 2323525) B2323525
theorem B1959347 : Blo 1375507 1959347 := bstep (se 1 (by rfl) ⟨1469510, by rfl⟩ : syracuseStep 1959347 = 2939021) B2939021
theorem B2065841 : Blo 1375507 2065841 := bstep (se 2 (by rfl) ⟨774690, by rfl⟩ : syracuseStep 2065841 = 1549381) B1549381
theorem B3098051 : Blo 1375507 3098051 := bstep (se 1 (by rfl) ⟨2323538, by rfl⟩ : syracuseStep 3098051 = 4647077) B4647077
theorem B2065859 : Blo 1375507 2065859 := bstep (se 1 (by rfl) ⟨1549394, by rfl⟩ : syracuseStep 2065859 = 3098789) B3098789
theorem B2065889 : Blo 1375507 2065889 := bstep (se 2 (by rfl) ⟨774708, by rfl⟩ : syracuseStep 2065889 = 1549417) B1549417
theorem B3483121 : Blo 1375507 3483121 := bstep (se 2 (by rfl) ⟨1306170, by rfl⟩ : syracuseStep 3483121 = 2612341) B2612341
theorem B2065907 : Blo 1375507 2065907 := bstep (se 1 (by rfl) ⟨1549430, by rfl⟩ : syracuseStep 2065907 = 3098861) B3098861
theorem B1959427 : Blo 1375507 1959427 := bstep (se 1 (by rfl) ⟨1469570, by rfl⟩ : syracuseStep 1959427 = 2939141) B2939141
theorem B7841285 : Blo 1375507 7841285 := bstep (se 4 (by rfl) ⟨735120, by rfl⟩ : syracuseStep 7841285 = 1470241) B1470241
theorem B2065937 : Blo 1375507 2065937 := bstep (se 2 (by rfl) ⟨774726, by rfl⟩ : syracuseStep 2065937 = 1549453) B1549453
theorem B2065955 : Blo 1375507 2065955 := bstep (se 1 (by rfl) ⟨1549466, by rfl⟩ : syracuseStep 2065955 = 3098933) B3098933
theorem B29763125 : Blo 1375507 29763125 := bstep (se 5 (by rfl) ⟨1395146, by rfl⟩ : syracuseStep 29763125 = 2790293) B2790293
theorem B2065985 : Blo 1375507 2065985 := bstep (se 2 (by rfl) ⟨774744, by rfl⟩ : syracuseStep 2065985 = 1549489) B1549489
theorem B2066003 : Blo 1375507 2066003 := bstep (se 1 (by rfl) ⟨1549502, by rfl⟩ : syracuseStep 2066003 = 3099005) B3099005
theorem B2066033 : Blo 1375507 2066033 := bstep (se 2 (by rfl) ⟨774762, by rfl⟩ : syracuseStep 2066033 = 1549525) B1549525
theorem B2066051 : Blo 1375507 2066051 := bstep (se 1 (by rfl) ⟨1549538, by rfl⟩ : syracuseStep 2066051 = 3099077) B3099077
theorem B2066081 : Blo 1375507 2066081 := bstep (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) B1549561
theorem B4187825 : Blo 1375507 4187825 := bstep (se 2 (by rfl) ⟨1570434, by rfl⟩ : syracuseStep 4187825 = 3140869) B3140869
theorem B2066099 : Blo 1375507 2066099 := bstep (se 1 (by rfl) ⟨1549574, by rfl⟩ : syracuseStep 2066099 = 3099149) B3099149
theorem B3098321 : Blo 1375507 3098321 := bstep (se 2 (by rfl) ⟨1161870, by rfl⟩ : syracuseStep 3098321 = 2323741) B2323741
theorem B2066129 : Blo 1375507 2066129 := bstep (se 2 (by rfl) ⟨774798, by rfl⟩ : syracuseStep 2066129 = 1549597) B1549597
theorem B3098339 : Blo 1375507 3098339 := bstep (se 1 (by rfl) ⟨2323754, by rfl⟩ : syracuseStep 3098339 = 4647509) B4647509
theorem B2066147 : Blo 1375507 2066147 := bstep (se 1 (by rfl) ⟨1549610, by rfl⟩ : syracuseStep 2066147 = 3099221) B3099221
theorem B2066177 : Blo 1375507 2066177 := bstep (se 2 (by rfl) ⟨774816, by rfl⟩ : syracuseStep 2066177 = 1549633) B1549633
theorem B3483395 : Blo 1375507 3483395 := bstep (se 1 (by rfl) ⟨2612546, by rfl⟩ : syracuseStep 3483395 = 5225093) B5225093
theorem B5654285 : Blo 1375507 5654285 := bstep (se 3 (by rfl) ⟨1060178, by rfl⟩ : syracuseStep 5654285 = 2120357) B2120357
theorem B2066195 : Blo 1375507 2066195 := bstep (se 1 (by rfl) ⟨1549646, by rfl⟩ : syracuseStep 2066195 = 3099293) B3099293
theorem B6965027 : Blo 1375507 6965027 := bstep (se 1 (by rfl) ⟨5223770, by rfl⟩ : syracuseStep 6965027 = 10447541) B10447541
theorem B2615075 : Blo 1375507 2615075 := bstep (se 1 (by rfl) ⟨1961306, by rfl⟩ : syracuseStep 2615075 = 3922613) B3922613
theorem B2066225 : Blo 1375507 2066225 := bstep (se 2 (by rfl) ⟨774834, by rfl⟩ : syracuseStep 2066225 = 1549669) B1549669
theorem B2066243 : Blo 1375507 2066243 := bstep (se 1 (by rfl) ⟨1549682, by rfl⟩ : syracuseStep 2066243 = 3099365) B3099365
theorem B2353025 : Blo 1375507 2353025 := bstep (se 2 (by rfl) ⟨882384, by rfl⟩ : syracuseStep 2353025 = 1764769) B1764769
theorem B21202829 : Blo 1375507 21202829 := bstep (se 3 (by rfl) ⟨3975530, by rfl⟩ : syracuseStep 21202829 = 7951061) B7951061
theorem B1861553 : Blo 1375507 1861553 := bstep (se 2 (by rfl) ⟨698082, by rfl⟩ : syracuseStep 1861553 = 1396165) B1396165
theorem B3483587 : Blo 1375507 3483587 := bstep (se 1 (by rfl) ⟨2612690, by rfl⟩ : syracuseStep 3483587 = 5225381) B5225381
theorem B4646861 : Blo 1375507 4646861 := bstep (se 3 (by rfl) ⟨871286, by rfl⟩ : syracuseStep 4646861 = 1742573) B1742573
theorem B3139555 : Blo 1375507 3139555 := bstep (se 1 (by rfl) ⟨2354666, by rfl⟩ : syracuseStep 3139555 = 4709333) B4709333
theorem B3098609 : Blo 1375507 3098609 := bstep (se 2 (by rfl) ⟨1161978, by rfl⟩ : syracuseStep 3098609 = 2323957) B2323957
theorem B4646915 : Blo 1375507 4646915 := bstep (se 1 (by rfl) ⟨3485186, by rfl⟩ : syracuseStep 4646915 = 6970373) B6970373
theorem B3098627 : Blo 1375507 3098627 := bstep (se 1 (by rfl) ⟨2323970, by rfl⟩ : syracuseStep 3098627 = 4647941) B4647941
theorem B1959985 : Blo 1375507 1959985 := bstep (se 2 (by rfl) ⟨734994, by rfl⟩ : syracuseStep 1959985 = 1469989) B1469989
theorem B3917965 : Blo 1375507 3917965 := bstep (se 3 (by rfl) ⟨734618, by rfl⟩ : syracuseStep 3917965 = 1469237) B1469237
theorem B2205875 : Blo 1375507 2205875 := bstep (se 1 (by rfl) ⟨1654406, by rfl⟩ : syracuseStep 2205875 = 3308813) B3308813
theorem B5810381 : Blo 1375507 5810381 := bstep (se 3 (by rfl) ⟨1089446, by rfl⟩ : syracuseStep 5810381 = 2178893) B2178893
theorem B5228813 : Blo 1375507 5228813 := bstep (se 3 (by rfl) ⟨980402, by rfl⟩ : syracuseStep 5228813 = 1960805) B1960805
theorem B4647185 : Blo 1375507 4647185 := bstep (se 2 (by rfl) ⟨1742694, by rfl⟩ : syracuseStep 4647185 = 3485389) B3485389
theorem B3098897 : Blo 1375507 3098897 := bstep (se 2 (by rfl) ⟨1162086, by rfl⟩ : syracuseStep 3098897 = 2324173) B2324173
theorem B3098915 : Blo 1375507 3098915 := bstep (se 1 (by rfl) ⟨2324186, by rfl⟩ : syracuseStep 3098915 = 4648373) B4648373
theorem B3918125 : Blo 1375507 3918125 := bstep (se 3 (by rfl) ⟨734648, by rfl⟩ : syracuseStep 3918125 = 1469297) B1469297
theorem B23841137 : Blo 1375507 23841137 := bstep (se 2 (by rfl) ⟨8940426, by rfl⟩ : syracuseStep 23841137 = 17880853) B17880853
theorem B2091425 : Blo 1375507 2091425 := bstep (se 2 (by rfl) ⟨784284, by rfl⟩ : syracuseStep 2091425 = 1568569) B1568569
theorem B1395139 : Blo 1375507 1395139 := bstep (se 1 (by rfl) ⟨1046354, by rfl⟩ : syracuseStep 1395139 = 2092709) B2092709
theorem B3918307 : Blo 1375507 3918307 := bstep (se 1 (by rfl) ⟨2938730, by rfl⟩ : syracuseStep 3918307 = 5877461) B5877461
theorem B9423373 : Blo 1375507 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B3099185 : Blo 1375507 3099185 := bstep (se 2 (by rfl) ⟨1162194, by rfl⟩ : syracuseStep 3099185 = 2324389) B2324389
theorem B3181123 : Blo 1375507 3181123 := bstep (se 1 (by rfl) ⟨2385842, by rfl⟩ : syracuseStep 3181123 = 4771685) B4771685
theorem B3099203 : Blo 1375507 3099203 := bstep (se 1 (by rfl) ⟨2324402, by rfl⟩ : syracuseStep 3099203 = 4648805) B4648805
theorem B6965837 : Blo 1375507 6965837 := bstep (se 3 (by rfl) ⟨1306094, by rfl⟩ : syracuseStep 6965837 = 2612189) B2612189
theorem B1469011 : Blo 1375507 1469011 := bstep (se 1 (by rfl) ⟨1101758, by rfl⟩ : syracuseStep 1469011 = 2203517) B2203517
theorem B5876401 : Blo 1375507 5876401 := bstep (se 2 (by rfl) ⟨2203650, by rfl⟩ : syracuseStep 5876401 = 4407301) B4407301
theorem B2206387 : Blo 1375507 2206387 := bstep (se 1 (by rfl) ⟨1654790, by rfl⟩ : syracuseStep 2206387 = 3309581) B3309581
theorem B1960691 : Blo 1375507 1960691 := bstep (se 1 (by rfl) ⟨1470518, by rfl⟩ : syracuseStep 1960691 = 2941037) B2941037
theorem B4647725 : Blo 1375507 4647725 := bstep (se 3 (by rfl) ⟨871448, by rfl⟩ : syracuseStep 4647725 = 1742897) B1742897
theorem B2321203 : Blo 1375507 2321203 := bstep (se 1 (by rfl) ⟨1740902, by rfl⟩ : syracuseStep 2321203 = 3481805) B3481805
theorem B10054469 : Blo 1375507 10054469 := bstep (se 4 (by rfl) ⟨942606, by rfl⟩ : syracuseStep 10054469 = 1885213) B1885213
theorem B11758405 : Blo 1375507 11758405 := bstep (se 4 (by rfl) ⟨1102350, by rfl⟩ : syracuseStep 11758405 = 2204701) B2204701
theorem B4647779 : Blo 1375507 4647779 := bstep (se 1 (by rfl) ⟨3485834, by rfl⟩ : syracuseStep 4647779 = 6971669) B6971669
theorem B3484529 : Blo 1375507 3484529 := bstep (se 2 (by rfl) ⟨1306698, by rfl⟩ : syracuseStep 3484529 = 2613397) B2613397
theorem B27200369 : Blo 1375507 27200369 := bstep (se 2 (by rfl) ⟨10200138, by rfl⟩ : syracuseStep 27200369 = 20400277) B20400277
theorem B1985411 : Blo 1375507 1985411 := bstep (se 1 (by rfl) ⟨1489058, by rfl⟩ : syracuseStep 1985411 = 2978117) B2978117
theorem B3353489 : Blo 1375507 3353489 := bstep (se 2 (by rfl) ⟨1257558, by rfl⟩ : syracuseStep 3353489 = 2515117) B2515117
theorem B3484579 : Blo 1375507 3484579 := bstep (se 1 (by rfl) ⟨2613434, by rfl⟩ : syracuseStep 3484579 = 5226869) B5226869
theorem B2321345 : Blo 1375507 2321345 := bstep (se 2 (by rfl) ⟨870504, by rfl⟩ : syracuseStep 2321345 = 1741009) B1741009
theorem B1469459 : Blo 1375507 1469459 := bstep (se 1 (by rfl) ⟨1102094, by rfl⟩ : syracuseStep 1469459 = 2204189) B2204189
theorem B3484721 : Blo 1375507 3484721 := bstep (se 2 (by rfl) ⟨1306770, by rfl⟩ : syracuseStep 3484721 = 2613541) B2613541
theorem B2321473 : Blo 1375507 2321473 := bstep (se 2 (by rfl) ⟨870552, by rfl⟩ : syracuseStep 2321473 = 1741105) B1741105
theorem B2354243 : Blo 1375507 2354243 := bstep (se 1 (by rfl) ⟨1765682, by rfl⟩ : syracuseStep 2354243 = 3531365) B3531365
theorem B2321507 : Blo 1375507 2321507 := bstep (se 1 (by rfl) ⟨1741130, by rfl⟩ : syracuseStep 2321507 = 3482261) B3482261
theorem B4648049 : Blo 1375507 4648049 := bstep (se 2 (by rfl) ⟨1743018, by rfl⟩ : syracuseStep 4648049 = 3486037) B3486037
theorem B7441541 : Blo 1375507 7441541 := bstep (se 4 (by rfl) ⟨697644, by rfl⟩ : syracuseStep 7441541 = 1395289) B1395289
theorem B2321635 : Blo 1375507 2321635 := bstep (se 1 (by rfl) ⟨1741226, by rfl⟩ : syracuseStep 2321635 = 3482453) B3482453
theorem B2321777 : Blo 1375507 2321777 := bstep (se 2 (by rfl) ⟨870666, by rfl⟩ : syracuseStep 2321777 = 1741333) B1741333
theorem B11767153 : Blo 1375507 11767153 := bstep (se 2 (by rfl) ⟨4412682, by rfl⟩ : syracuseStep 11767153 = 8825365) B8825365
theorem B1961329 : Blo 1375507 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B4410787 : Blo 1375507 4410787 := bstep (se 1 (by rfl) ⟨3308090, by rfl⟩ : syracuseStep 4410787 = 6616181) B6616181
theorem B2321905 : Blo 1375507 2321905 := bstep (se 2 (by rfl) ⟨870714, by rfl⟩ : syracuseStep 2321905 = 1741429) B1741429
theorem B2321939 : Blo 1375507 2321939 := bstep (se 1 (by rfl) ⟨1741454, by rfl⟩ : syracuseStep 2321939 = 3482909) B3482909
theorem B4410929 : Blo 1375507 4410929 := bstep (se 2 (by rfl) ⟨1654098, by rfl⟩ : syracuseStep 4410929 = 3308197) B3308197
theorem B3141233 : Blo 1375507 3141233 := bstep (se 2 (by rfl) ⟨1177962, by rfl⟩ : syracuseStep 3141233 = 2355925) B2355925
theorem B4648589 : Blo 1375507 4648589 := bstep (se 3 (by rfl) ⟨871610, by rfl⟩ : syracuseStep 4648589 = 1743221) B1743221
theorem B2322067 : Blo 1375507 2322067 := bstep (se 1 (by rfl) ⟨1741550, by rfl⟩ : syracuseStep 2322067 = 3483101) B3483101
theorem B2092691 : Blo 1375507 2092691 := bstep (se 1 (by rfl) ⟨1569518, by rfl⟩ : syracuseStep 2092691 = 3139037) B3139037
theorem B4648643 : Blo 1375507 4648643 := bstep (se 1 (by rfl) ⟨3486482, by rfl⟩ : syracuseStep 4648643 = 6972965) B6972965
theorem B2322209 : Blo 1375507 2322209 := bstep (se 2 (by rfl) ⟨870828, by rfl⟩ : syracuseStep 2322209 = 1741657) B1741657
theorem B3919697 : Blo 1375507 3919697 := bstep (se 2 (by rfl) ⟨1469886, by rfl⟩ : syracuseStep 3919697 = 2939773) B2939773
theorem B2092915 : Blo 1375507 2092915 := bstep (se 1 (by rfl) ⟨1569686, by rfl⟩ : syracuseStep 2092915 = 3139373) B3139373
theorem B2322337 : Blo 1375507 2322337 := bstep (se 2 (by rfl) ⟨870876, by rfl⟩ : syracuseStep 2322337 = 1741753) B1741753
theorem B2322371 : Blo 1375507 2322371 := bstep (se 1 (by rfl) ⟨1741778, by rfl⟩ : syracuseStep 2322371 = 3483557) B3483557
theorem B4648913 : Blo 1375507 4648913 := bstep (se 2 (by rfl) ⟨1743342, by rfl⟩ : syracuseStep 4648913 = 3486685) B3486685
theorem B3485713 : Blo 1375507 3485713 := bstep (se 2 (by rfl) ⟨1307142, by rfl⟩ : syracuseStep 3485713 = 2614285) B2614285
theorem B4960291 : Blo 1375507 4960291 := bstep (se 1 (by rfl) ⟨3720218, by rfl⟩ : syracuseStep 4960291 = 7440437) B7440437
theorem B2322499 : Blo 1375507 2322499 := bstep (se 1 (by rfl) ⟨1741874, by rfl⟩ : syracuseStep 2322499 = 3483749) B3483749
theorem B7065805 : Blo 1375507 7065805 := bstep (se 3 (by rfl) ⟨1324838, by rfl⟩ : syracuseStep 7065805 = 2649677) B2649677
theorem B2322641 : Blo 1375507 2322641 := bstep (se 2 (by rfl) ⟨870990, by rfl⟩ : syracuseStep 2322641 = 1741981) B1741981
theorem B3485987 : Blo 1375507 3485987 := bstep (se 1 (by rfl) ⟨2614490, by rfl⟩ : syracuseStep 3485987 = 5228981) B5228981
theorem B5583181 : Blo 1375507 5583181 := bstep (se 3 (by rfl) ⟨1046846, by rfl⟩ : syracuseStep 5583181 = 2093693) B2093693
theorem B2322769 : Blo 1375507 2322769 := bstep (se 2 (by rfl) ⟨871038, by rfl⟩ : syracuseStep 2322769 = 1742077) B1742077
theorem B1741171 : Blo 1375507 1741171 := bstep (se 1 (by rfl) ⟨1305878, by rfl⟩ : syracuseStep 1741171 = 2611757) B2611757
theorem B2322803 : Blo 1375507 2322803 := bstep (se 1 (by rfl) ⟨1742102, by rfl⟩ : syracuseStep 2322803 = 3484205) B3484205
theorem B1470835 : Blo 1375507 1470835 := bstep (se 1 (by rfl) ⟨1103126, by rfl⟩ : syracuseStep 1470835 = 2206253) B2206253
theorem B1741267 : Blo 1375507 1741267 := bstep (se 1 (by rfl) ⟨1305950, by rfl⟩ : syracuseStep 1741267 = 2611901) B2611901
theorem B11162083 : Blo 1375507 11162083 := bstep (se 1 (by rfl) ⟨8371562, by rfl⟩ : syracuseStep 11162083 = 16743125) B16743125
theorem B3486179 : Blo 1375507 3486179 := bstep (se 1 (by rfl) ⟨2614634, by rfl⟩ : syracuseStep 3486179 = 5229269) B5229269
theorem B2322931 : Blo 1375507 2322931 := bstep (se 1 (by rfl) ⟨1742198, by rfl⟩ : syracuseStep 2322931 = 3484397) B3484397
theorem B47657585 : Blo 1375507 47657585 := bstep (se 2 (by rfl) ⟨17871594, by rfl⟩ : syracuseStep 47657585 = 35743189) B35743189
theorem B1569395 : Blo 1375507 1569395 := bstep (se 1 (by rfl) ⟨1177046, by rfl⟩ : syracuseStep 1569395 = 2354093) B2354093
theorem B2323073 : Blo 1375507 2323073 := bstep (se 2 (by rfl) ⟨871152, by rfl⟩ : syracuseStep 2323073 = 1742305) B1742305
theorem B2323201 : Blo 1375507 2323201 := bstep (se 2 (by rfl) ⟨871200, by rfl⟩ : syracuseStep 2323201 = 1742401) B1742401
theorem B3920653 : Blo 1375507 3920653 := bstep (se 3 (by rfl) ⟨735122, by rfl⟩ : syracuseStep 3920653 = 1470245) B1470245
theorem B2323235 : Blo 1375507 2323235 := bstep (se 1 (by rfl) ⟨1742426, by rfl⟩ : syracuseStep 2323235 = 3484853) B3484853
theorem B2356049 : Blo 1375507 2356049 := bstep (se 2 (by rfl) ⟨883518, by rfl⟩ : syracuseStep 2356049 = 1767037) B1767037
theorem B2323363 : Blo 1375507 2323363 := bstep (se 1 (by rfl) ⟨1742522, by rfl⟩ : syracuseStep 2323363 = 3485045) B3485045
theorem B1741763 : Blo 1375507 1741763 := bstep (se 1 (by rfl) ⟨1306322, by rfl⟩ : syracuseStep 1741763 = 2612645) B2612645
theorem B26457029 : Blo 1375507 26457029 := bstep (se 4 (by rfl) ⟨2480346, by rfl⟩ : syracuseStep 26457029 = 4960693) B4960693
theorem B3920881 : Blo 1375507 3920881 := bstep (se 2 (by rfl) ⟨1470330, by rfl⟩ : syracuseStep 3920881 = 2940661) B2940661
theorem B5223437 : Blo 1375507 5223437 := bstep (se 3 (by rfl) ⟨979394, by rfl⟩ : syracuseStep 5223437 = 1958789) B1958789
theorem B2323505 : Blo 1375507 2323505 := bstep (se 2 (by rfl) ⟨871314, by rfl⟩ : syracuseStep 2323505 = 1742629) B1742629
theorem B3921041 : Blo 1375507 3921041 := bstep (se 2 (by rfl) ⟨1470390, by rfl⟩ : syracuseStep 3921041 = 2940781) B2940781
theorem B2323633 : Blo 1375507 2323633 := bstep (se 2 (by rfl) ⟨871362, by rfl⟩ : syracuseStep 2323633 = 1742725) B1742725
theorem B2323667 : Blo 1375507 2323667 := bstep (se 1 (by rfl) ⟨1742750, by rfl⟩ : syracuseStep 2323667 = 3485501) B3485501
theorem B3306737 : Blo 1375507 3306737 := bstep (se 2 (by rfl) ⟨1240026, by rfl⟩ : syracuseStep 3306737 = 2480053) B2480053
theorem B3921155 : Blo 1375507 3921155 := bstep (se 1 (by rfl) ⟨2940866, by rfl⟩ : syracuseStep 3921155 = 5881733) B5881733
theorem B7845133 : Blo 1375507 7845133 := bstep (se 3 (by rfl) ⟨1470962, by rfl⟩ : syracuseStep 7845133 = 2941925) B2941925
theorem B2323795 : Blo 1375507 2323795 := bstep (se 1 (by rfl) ⟨1742846, by rfl⟩ : syracuseStep 2323795 = 3485693) B3485693
theorem B6968753 : Blo 1375507 6968753 := bstep (se 2 (by rfl) ⟨2613282, by rfl⟩ : syracuseStep 6968753 = 5226565) B5226565
theorem B17651141 : Blo 1375507 17651141 := bstep (se 4 (by rfl) ⟨1654794, by rfl⟩ : syracuseStep 17651141 = 3309589) B3309589
theorem B2323937 : Blo 1375507 2323937 := bstep (se 2 (by rfl) ⟨871476, by rfl⟩ : syracuseStep 2323937 = 1742953) B1742953
theorem B2324065 : Blo 1375507 2324065 := bstep (se 2 (by rfl) ⟨871524, by rfl⟩ : syracuseStep 2324065 = 1743049) B1743049
theorem B3307121 : Blo 1375507 3307121 := bstep (se 2 (by rfl) ⟨1240170, by rfl⟩ : syracuseStep 3307121 = 2480341) B2480341
theorem B1742467 : Blo 1375507 1742467 := bstep (se 1 (by rfl) ⟨1306850, by rfl⟩ : syracuseStep 1742467 = 2613701) B2613701
theorem B2324099 : Blo 1375507 2324099 := bstep (se 1 (by rfl) ⟨1743074, by rfl⟩ : syracuseStep 2324099 = 3486149) B3486149
theorem B2791057 : Blo 1375507 2791057 := bstep (se 2 (by rfl) ⟨1046646, by rfl⟩ : syracuseStep 2791057 = 2093293) B2093293
theorem B1742563 : Blo 1375507 1742563 := bstep (se 1 (by rfl) ⟨1306922, by rfl⟩ : syracuseStep 1742563 = 2613845) B2613845
theorem B4642541 : Blo 1375507 4642541 := bstep (se 3 (by rfl) ⟨870476, by rfl⟩ : syracuseStep 4642541 = 1740953) B1740953
theorem B2324227 : Blo 1375507 2324227 := bstep (se 1 (by rfl) ⟨1743170, by rfl⟩ : syracuseStep 2324227 = 3486341) B3486341
theorem B40236821 : Blo 1375507 40236821 := bstep (se 6 (by rfl) ⟨943050, by rfl⟩ : syracuseStep 40236821 = 1886101) B1886101
theorem B4642595 : Blo 1375507 4642595 := bstep (se 1 (by rfl) ⟨3481946, by rfl⟩ : syracuseStep 4642595 = 6963893) B6963893
theorem B4470605 : Blo 1375507 4470605 := bstep (se 3 (by rfl) ⟨838238, by rfl⟩ : syracuseStep 4470605 = 1676477) B1676477
theorem B2324369 : Blo 1375507 2324369 := bstep (se 2 (by rfl) ⟨871638, by rfl⟩ : syracuseStep 2324369 = 1743277) B1743277
theorem B5027789 : Blo 1375507 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B2324497 : Blo 1375507 2324497 := bstep (se 2 (by rfl) ⟨871686, by rfl⟩ : syracuseStep 2324497 = 1743373) B1743373
theorem B4642865 : Blo 1375507 4642865 := bstep (se 2 (by rfl) ⟨1741074, by rfl⟩ : syracuseStep 4642865 = 3482149) B3482149
theorem B2324531 : Blo 1375507 2324531 := bstep (se 1 (by rfl) ⟨1743398, by rfl⟩ : syracuseStep 2324531 = 3486797) B3486797
theorem B10459205 : Blo 1375507 10459205 := bstep (se 4 (by rfl) ⟨980550, by rfl⟩ : syracuseStep 10459205 = 1961101) B1961101
theorem B2938979 : Blo 1375507 2938979 := bstep (se 1 (by rfl) ⟨2204234, by rfl⟩ : syracuseStep 2938979 = 4408469) B4408469
theorem B4184273 : Blo 1375507 4184273 := bstep (se 2 (by rfl) ⟨1569102, by rfl⟩ : syracuseStep 4184273 = 3138205) B3138205
theorem B1743059 : Blo 1375507 1743059 := bstep (se 1 (by rfl) ⟨1307294, by rfl⟩ : syracuseStep 1743059 = 2614589) B2614589
theorem B6617315 : Blo 1375507 6617315 := bstep (se 1 (by rfl) ⟨4962986, by rfl⟩ : syracuseStep 6617315 = 9925973) B9925973
theorem B3922157 : Blo 1375507 3922157 := bstep (se 3 (by rfl) ⟨735404, by rfl⟩ : syracuseStep 3922157 = 1470809) B1470809
theorem B8821061 : Blo 1375507 8821061 := bstep (se 4 (by rfl) ⟨826974, by rfl⟩ : syracuseStep 8821061 = 1653949) B1653949
theorem B3922339 : Blo 1375507 3922339 := bstep (se 1 (by rfl) ⟨2941754, by rfl⟩ : syracuseStep 3922339 = 5883509) B5883509
theorem B4708813 : Blo 1375507 4708813 := bstep (se 3 (by rfl) ⟨882902, by rfl⟩ : syracuseStep 4708813 = 1765805) B1765805
theorem B3971651 : Blo 1375507 3971651 := bstep (se 1 (by rfl) ⟨2978738, by rfl⟩ : syracuseStep 3971651 = 5957477) B5957477
theorem B3922499 : Blo 1375507 3922499 := bstep (se 1 (by rfl) ⟨2941874, by rfl⟩ : syracuseStep 3922499 = 5883749) B5883749
theorem B4643405 : Blo 1375507 4643405 := bstep (se 3 (by rfl) ⟨870638, by rfl⟩ : syracuseStep 4643405 = 1741277) B1741277
theorem B3095153 : Blo 1375507 3095153 := bstep (se 2 (by rfl) ⟨1160682, by rfl⟩ : syracuseStep 3095153 = 2321365) B2321365
theorem B5880433 : Blo 1375507 5880433 := bstep (se 2 (by rfl) ⟨2205162, by rfl⟩ : syracuseStep 5880433 = 4410325) B4410325
theorem B3095171 : Blo 1375507 3095171 := bstep (se 1 (by rfl) ⟨2321378, by rfl⟩ : syracuseStep 3095171 = 4642757) B4642757
theorem B4643459 : Blo 1375507 4643459 := bstep (se 1 (by rfl) ⟨3482594, by rfl⟩ : syracuseStep 4643459 = 6965189) B6965189
theorem B34388621 : Blo 1375507 34388621 := bstep (se 3 (by rfl) ⟨6447866, by rfl⟩ : syracuseStep 34388621 = 12895733) B12895733
theorem B2611939 : Blo 1375507 2611939 := bstep (se 1 (by rfl) ⟨1958954, by rfl⟩ : syracuseStep 2611939 = 3917909) B3917909
theorem B1489747 : Blo 1375507 1489747 := bstep (se 1 (by rfl) ⟨1117310, by rfl⟩ : syracuseStep 1489747 = 2234621) B2234621
theorem B6970211 : Blo 1375507 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B13237091 : Blo 1375507 13237091 := bstep (se 1 (by rfl) ⟨9927818, by rfl⟩ : syracuseStep 13237091 = 19855637) B19855637
theorem B4029325 : Blo 1375507 4029325 := bstep (se 3 (by rfl) ⟨755498, by rfl⟩ : syracuseStep 4029325 = 1510997) B1510997
theorem B3095441 : Blo 1375507 3095441 := bstep (se 2 (by rfl) ⟨1160790, by rfl⟩ : syracuseStep 3095441 = 2321581) B2321581
theorem B4643729 : Blo 1375507 4643729 := bstep (se 2 (by rfl) ⟨1741398, by rfl⟩ : syracuseStep 4643729 = 3482797) B3482797
theorem B2063267 : Blo 1375507 2063267 := bstep (se 1 (by rfl) ⟨1547450, by rfl⟩ : syracuseStep 2063267 = 3094901) B3094901
theorem B3095459 : Blo 1375507 3095459 := bstep (se 1 (by rfl) ⟨2321594, by rfl⟩ : syracuseStep 3095459 = 4643189) B4643189
theorem B2063297 : Blo 1375507 2063297 := bstep (se 2 (by rfl) ⟨773736, by rfl⟩ : syracuseStep 2063297 = 1547473) B1547473
theorem B2980817 : Blo 1375507 2980817 := bstep (se 2 (by rfl) ⟨1117806, by rfl⟩ : syracuseStep 2980817 = 2235613) B2235613
theorem B2063315 : Blo 1375507 2063315 := bstep (se 1 (by rfl) ⟨1547486, by rfl⟩ : syracuseStep 2063315 = 3094973) B3094973
theorem B3529699 : Blo 1375507 3529699 := bstep (se 1 (by rfl) ⟨2647274, by rfl⟩ : syracuseStep 3529699 = 5294549) B5294549
theorem B2063345 : Blo 1375507 2063345 := bstep (se 2 (by rfl) ⟨773754, by rfl⟩ : syracuseStep 2063345 = 1547509) B1547509
theorem B2063363 : Blo 1375507 2063363 := bstep (se 1 (by rfl) ⟨1547522, by rfl⟩ : syracuseStep 2063363 = 3095045) B3095045
theorem B2063393 : Blo 1375507 2063393 := bstep (se 2 (by rfl) ⟨773772, by rfl⟩ : syracuseStep 2063393 = 1547545) B1547545
theorem B2063411 : Blo 1375507 2063411 := bstep (se 1 (by rfl) ⟨1547558, by rfl⟩ : syracuseStep 2063411 = 3095117) B3095117
theorem B2063441 : Blo 1375507 2063441 := bstep (se 2 (by rfl) ⟨773790, by rfl⟩ : syracuseStep 2063441 = 1547581) B1547581
theorem B2063459 : Blo 1375507 2063459 := bstep (se 1 (by rfl) ⟨1547594, by rfl⟩ : syracuseStep 2063459 = 3095189) B3095189
theorem B4185197 : Blo 1375507 4185197 := bstep (se 3 (by rfl) ⟨784724, by rfl⟩ : syracuseStep 4185197 = 1569449) B1569449
theorem B15080561 : Blo 1375507 15080561 := bstep (se 2 (by rfl) ⟨5655210, by rfl⟩ : syracuseStep 15080561 = 11310421) B11310421
theorem B2063489 : Blo 1375507 2063489 := bstep (se 2 (by rfl) ⟨773808, by rfl⟩ : syracuseStep 2063489 = 1547617) B1547617
theorem B4775057 : Blo 1375507 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B2063507 : Blo 1375507 2063507 := bstep (se 1 (by rfl) ⟨1547630, by rfl⟩ : syracuseStep 2063507 = 3095261) B3095261
theorem B8813731 : Blo 1375507 8813731 := bstep (se 1 (by rfl) ⟨6610298, by rfl⟩ : syracuseStep 8813731 = 13220597) B13220597
theorem B2612387 : Blo 1375507 2612387 := bstep (se 1 (by rfl) ⟨1959290, by rfl⟩ : syracuseStep 2612387 = 3918581) B3918581
theorem B2063537 : Blo 1375507 2063537 := bstep (se 2 (by rfl) ⟨773826, by rfl⟩ : syracuseStep 2063537 = 1547653) B1547653
theorem B3095729 : Blo 1375507 3095729 := bstep (se 2 (by rfl) ⟨1160898, by rfl⟩ : syracuseStep 3095729 = 2321797) B2321797
theorem B2063555 : Blo 1375507 2063555 := bstep (se 1 (by rfl) ⟨1547666, by rfl⟩ : syracuseStep 2063555 = 3095333) B3095333
theorem B3095747 : Blo 1375507 3095747 := bstep (se 1 (by rfl) ⟨2321810, by rfl⟩ : syracuseStep 3095747 = 4643621) B4643621
theorem B2063585 : Blo 1375507 2063585 := bstep (se 2 (by rfl) ⟨773844, by rfl⟩ : syracuseStep 2063585 = 1547689) B1547689
theorem B1547491 : Blo 1375507 1547491 := bstep (se 1 (by rfl) ⟨1160618, by rfl⟩ : syracuseStep 1547491 = 2321237) B2321237
theorem B2063603 : Blo 1375507 2063603 := bstep (se 1 (by rfl) ⟨1547702, by rfl⟩ : syracuseStep 2063603 = 3095405) B3095405
theorem B2153731 : Blo 1375507 2153731 := bstep (se 1 (by rfl) ⟨1615298, by rfl⟩ : syracuseStep 2153731 = 3230597) B3230597
theorem B2063633 : Blo 1375507 2063633 := bstep (se 2 (by rfl) ⟨773862, by rfl⟩ : syracuseStep 2063633 = 1547725) B1547725
theorem B1375507 : Blo 1375507 1375507 := bstep (se 1 (by rfl) ⟨1031630, by rfl⟩ : syracuseStep 1375507 = 2063261) B2063261
theorem B1375523 : Blo 1375507 1375523 := bstep (se 1 (by rfl) ⟨1031642, by rfl⟩ : syracuseStep 1375523 = 2063285) B2063285
theorem B2063651 : Blo 1375507 2063651 := bstep (se 1 (by rfl) ⟨1547738, by rfl⟩ : syracuseStep 2063651 = 3095477) B3095477
theorem B2940209 : Blo 1375507 2940209 := bstep (se 2 (by rfl) ⟨1102578, by rfl⟩ : syracuseStep 2940209 = 2205157) B2205157
theorem B1375539 : Blo 1375507 1375539 := bstep (se 1 (by rfl) ⟨1031654, by rfl⟩ : syracuseStep 1375539 = 2063309) B2063309
theorem B2063681 : Blo 1375507 2063681 := bstep (se 2 (by rfl) ⟨773880, by rfl⟩ : syracuseStep 2063681 = 1547761) B1547761
theorem B1375555 : Blo 1375507 1375555 := bstep (se 1 (by rfl) ⟨1031666, by rfl⟩ : syracuseStep 1375555 = 2063333) B2063333
theorem B1375571 : Blo 1375507 1375571 := bstep (se 1 (by rfl) ⟨1031678, by rfl⟩ : syracuseStep 1375571 = 2063357) B2063357
theorem B2063699 : Blo 1375507 2063699 := bstep (se 1 (by rfl) ⟨1547774, by rfl⟩ : syracuseStep 2063699 = 3095549) B3095549
theorem B1375587 : Blo 1375507 1375587 := bstep (se 1 (by rfl) ⟨1031690, by rfl⟩ : syracuseStep 1375587 = 2063381) B2063381
theorem B2063729 : Blo 1375507 2063729 := bstep (se 2 (by rfl) ⟨773898, by rfl⟩ : syracuseStep 2063729 = 1547797) B1547797
theorem B1375603 : Blo 1375507 1375603 := bstep (se 1 (by rfl) ⟨1031702, by rfl⟩ : syracuseStep 1375603 = 2063405) B2063405
theorem B1547635 : Blo 1375507 1547635 := bstep (se 1 (by rfl) ⟨1160726, by rfl⟩ : syracuseStep 1547635 = 2321453) B2321453
theorem B1375619 : Blo 1375507 1375619 := bstep (se 1 (by rfl) ⟨1031714, by rfl⟩ : syracuseStep 1375619 = 2063429) B2063429
theorem B2063747 : Blo 1375507 2063747 := bstep (se 1 (by rfl) ⟨1547810, by rfl⟩ : syracuseStep 2063747 = 3095621) B3095621
theorem B1375635 : Blo 1375507 1375635 := bstep (se 1 (by rfl) ⟨1031726, by rfl⟩ : syracuseStep 1375635 = 2063453) B2063453
theorem B2063777 : Blo 1375507 2063777 := bstep (se 2 (by rfl) ⟨773916, by rfl⟩ : syracuseStep 2063777 = 1547833) B1547833
theorem B1375651 : Blo 1375507 1375651 := bstep (se 1 (by rfl) ⟨1031738, by rfl⟩ : syracuseStep 1375651 = 2063477) B2063477
theorem B4644269 : Blo 1375507 4644269 := bstep (se 3 (by rfl) ⟨870800, by rfl⟩ : syracuseStep 4644269 = 1741601) B1741601
theorem B1375667 : Blo 1375507 1375667 := bstep (se 1 (by rfl) ⟨1031750, by rfl⟩ : syracuseStep 1375667 = 2063501) B2063501
theorem B2063795 : Blo 1375507 2063795 := bstep (se 1 (by rfl) ⟨1547846, by rfl⟩ : syracuseStep 2063795 = 3095693) B3095693
theorem B1375683 : Blo 1375507 1375683 := bstep (se 1 (by rfl) ⟨1031762, by rfl⟩ : syracuseStep 1375683 = 2063525) B2063525
theorem B2612675 : Blo 1375507 2612675 := bstep (se 1 (by rfl) ⟨1959506, by rfl⟩ : syracuseStep 2612675 = 3919013) B3919013
theorem B4406737 : Blo 1375507 4406737 := bstep (se 2 (by rfl) ⟨1652526, by rfl⟩ : syracuseStep 4406737 = 3305053) B3305053
theorem B2063825 : Blo 1375507 2063825 := bstep (se 2 (by rfl) ⟨773934, by rfl⟩ : syracuseStep 2063825 = 1547869) B1547869
theorem B1375699 : Blo 1375507 1375699 := bstep (se 1 (by rfl) ⟨1031774, by rfl⟩ : syracuseStep 1375699 = 2063549) B2063549
theorem B3096017 : Blo 1375507 3096017 := bstep (se 2 (by rfl) ⟨1161006, by rfl⟩ : syracuseStep 3096017 = 2322013) B2322013
theorem B1375715 : Blo 1375507 1375715 := bstep (se 1 (by rfl) ⟨1031786, by rfl⟩ : syracuseStep 1375715 = 2063573) B2063573
theorem B2063843 : Blo 1375507 2063843 := bstep (se 1 (by rfl) ⟨1547882, by rfl⟩ : syracuseStep 2063843 = 3095765) B3095765
theorem B3096035 : Blo 1375507 3096035 := bstep (se 1 (by rfl) ⟨2322026, by rfl⟩ : syracuseStep 3096035 = 4644053) B4644053
theorem B4644323 : Blo 1375507 4644323 := bstep (se 1 (by rfl) ⟨3483242, by rfl⟩ : syracuseStep 4644323 = 6966485) B6966485
theorem B1375731 : Blo 1375507 1375731 := bstep (se 1 (by rfl) ⟨1031798, by rfl⟩ : syracuseStep 1375731 = 2063597) B2063597
theorem B2063873 : Blo 1375507 2063873 := bstep (se 2 (by rfl) ⟨773952, by rfl⟩ : syracuseStep 2063873 = 1547905) B1547905
theorem B1375747 : Blo 1375507 1375747 := bstep (se 1 (by rfl) ⟨1031810, by rfl⟩ : syracuseStep 1375747 = 2063621) B2063621
theorem B1547779 : Blo 1375507 1547779 := bstep (se 1 (by rfl) ⟨1160834, by rfl⟩ : syracuseStep 1547779 = 2321669) B2321669
theorem B5578253 : Blo 1375507 5578253 := bstep (se 3 (by rfl) ⟨1045922, by rfl⟩ : syracuseStep 5578253 = 2091845) B2091845
theorem B1375763 : Blo 1375507 1375763 := bstep (se 1 (by rfl) ⟨1031822, by rfl⟩ : syracuseStep 1375763 = 2063645) B2063645
theorem B2063891 : Blo 1375507 2063891 := bstep (se 1 (by rfl) ⟨1547918, by rfl⟩ : syracuseStep 2063891 = 3095837) B3095837
theorem B1654291 : Blo 1375507 1654291 := bstep (se 1 (by rfl) ⟨1240718, by rfl⟩ : syracuseStep 1654291 = 2481437) B2481437
theorem B1375779 : Blo 1375507 1375779 := bstep (se 1 (by rfl) ⟨1031834, by rfl⟩ : syracuseStep 1375779 = 2063669) B2063669
theorem B2063921 : Blo 1375507 2063921 := bstep (se 2 (by rfl) ⟨773970, by rfl⟩ : syracuseStep 2063921 = 1547941) B1547941
theorem B1375795 : Blo 1375507 1375795 := bstep (se 1 (by rfl) ⟨1031846, by rfl⟩ : syracuseStep 1375795 = 2063693) B2063693
theorem B1375811 : Blo 1375507 1375811 := bstep (se 1 (by rfl) ⟨1031858, by rfl⟩ : syracuseStep 1375811 = 2063717) B2063717
theorem B2063939 : Blo 1375507 2063939 := bstep (se 1 (by rfl) ⟨1547954, by rfl⟩ : syracuseStep 2063939 = 3095909) B3095909
theorem B7839301 : Blo 1375507 7839301 := bstep (se 4 (by rfl) ⟨734934, by rfl⟩ : syracuseStep 7839301 = 1469869) B1469869
theorem B2981443 : Blo 1375507 2981443 := bstep (se 1 (by rfl) ⟨2236082, by rfl⟩ : syracuseStep 2981443 = 4472165) B4472165
theorem B1375827 : Blo 1375507 1375827 := bstep (se 1 (by rfl) ⟨1031870, by rfl⟩ : syracuseStep 1375827 = 2063741) B2063741
theorem B2063969 : Blo 1375507 2063969 := bstep (se 2 (by rfl) ⟨773988, by rfl⟩ : syracuseStep 2063969 = 1547977) B1547977
theorem B1375843 : Blo 1375507 1375843 := bstep (se 1 (by rfl) ⟨1031882, by rfl⟩ : syracuseStep 1375843 = 2063765) B2063765
theorem B1375859 : Blo 1375507 1375859 := bstep (se 1 (by rfl) ⟨1031894, by rfl⟩ : syracuseStep 1375859 = 2063789) B2063789
theorem B2063987 : Blo 1375507 2063987 := bstep (se 1 (by rfl) ⟨1547990, by rfl⟩ : syracuseStep 2063987 = 3095981) B3095981
theorem B1375875 : Blo 1375507 1375875 := bstep (se 1 (by rfl) ⟨1031906, by rfl⟩ : syracuseStep 1375875 = 2063813) B2063813
theorem B6971021 : Blo 1375507 6971021 := bstep (se 3 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 6971021 = 2614133) B2614133
theorem B2064017 : Blo 1375507 2064017 := bstep (se 2 (by rfl) ⟨774006, by rfl⟩ : syracuseStep 2064017 = 1548013) B1548013
theorem B1375891 : Blo 1375507 1375891 := bstep (se 1 (by rfl) ⟨1031918, by rfl⟩ : syracuseStep 1375891 = 2063837) B2063837
theorem B1547923 : Blo 1375507 1547923 := bstep (se 1 (by rfl) ⟨1160942, by rfl⟩ : syracuseStep 1547923 = 2321885) B2321885
theorem B1375907 : Blo 1375507 1375907 := bstep (se 1 (by rfl) ⟨1031930, by rfl⟩ : syracuseStep 1375907 = 2063861) B2063861
theorem B2064035 : Blo 1375507 2064035 := bstep (se 1 (by rfl) ⟨1548026, by rfl⟩ : syracuseStep 2064035 = 3096053) B3096053
theorem B1375923 : Blo 1375507 1375923 := bstep (se 1 (by rfl) ⟨1031942, by rfl⟩ : syracuseStep 1375923 = 2063885) B2063885
theorem B2064065 : Blo 1375507 2064065 := bstep (se 2 (by rfl) ⟨774024, by rfl⟩ : syracuseStep 2064065 = 1548049) B1548049
theorem B1375939 : Blo 1375507 1375939 := bstep (se 1 (by rfl) ⟨1031954, by rfl⟩ : syracuseStep 1375939 = 2063909) B2063909
theorem B1375955 : Blo 1375507 1375955 := bstep (se 1 (by rfl) ⟨1031966, by rfl⟩ : syracuseStep 1375955 = 2063933) B2063933
theorem B2064083 : Blo 1375507 2064083 := bstep (se 1 (by rfl) ⟨1548062, by rfl⟩ : syracuseStep 2064083 = 3096125) B3096125
theorem B1375971 : Blo 1375507 1375971 := bstep (se 1 (by rfl) ⟨1031978, by rfl⟩ : syracuseStep 1375971 = 2063957) B2063957
theorem B2064113 : Blo 1375507 2064113 := bstep (se 2 (by rfl) ⟨774042, by rfl⟩ : syracuseStep 2064113 = 1548085) B1548085
theorem B3096305 : Blo 1375507 3096305 := bstep (se 2 (by rfl) ⟨1161114, by rfl⟩ : syracuseStep 3096305 = 2322229) B2322229
theorem B1375987 : Blo 1375507 1375987 := bstep (se 1 (by rfl) ⟨1031990, by rfl⟩ : syracuseStep 1375987 = 2063981) B2063981
theorem B4644593 : Blo 1375507 4644593 := bstep (se 2 (by rfl) ⟨1741722, by rfl⟩ : syracuseStep 4644593 = 3483445) B3483445
theorem B1376003 : Blo 1375507 1376003 := bstep (se 1 (by rfl) ⟨1032002, by rfl⟩ : syracuseStep 1376003 = 2064005) B2064005
theorem B2064131 : Blo 1375507 2064131 := bstep (se 1 (by rfl) ⟨1548098, by rfl⟩ : syracuseStep 2064131 = 3096197) B3096197
theorem B3096323 : Blo 1375507 3096323 := bstep (se 1 (by rfl) ⟨2322242, by rfl⟩ : syracuseStep 3096323 = 4644485) B4644485
theorem B1376019 : Blo 1375507 1376019 := bstep (se 1 (by rfl) ⟨1032014, by rfl⟩ : syracuseStep 1376019 = 2064029) B2064029
theorem B2064161 : Blo 1375507 2064161 := bstep (se 2 (by rfl) ⟨774060, by rfl⟩ : syracuseStep 2064161 = 1548121) B1548121
theorem B1376035 : Blo 1375507 1376035 := bstep (se 1 (by rfl) ⟨1032026, by rfl⟩ : syracuseStep 1376035 = 2064053) B2064053
theorem B1548067 : Blo 1375507 1548067 := bstep (se 1 (by rfl) ⟨1161050, by rfl⟩ : syracuseStep 1548067 = 2322101) B2322101
theorem B1376051 : Blo 1375507 1376051 := bstep (se 1 (by rfl) ⟨1032038, by rfl⟩ : syracuseStep 1376051 = 2064077) B2064077
theorem B2064179 : Blo 1375507 2064179 := bstep (se 1 (by rfl) ⟨1548134, by rfl⟩ : syracuseStep 2064179 = 3096269) B3096269
theorem B26828597 : Blo 1375507 26828597 := bstep (se 5 (by rfl) ⟨1257590, by rfl⟩ : syracuseStep 26828597 = 2515181) B2515181
theorem B1376067 : Blo 1375507 1376067 := bstep (se 1 (by rfl) ⟨1032050, by rfl⟩ : syracuseStep 1376067 = 2064101) B2064101
theorem B2064209 : Blo 1375507 2064209 := bstep (se 2 (by rfl) ⟨774078, by rfl⟩ : syracuseStep 2064209 = 1548157) B1548157
theorem B1376083 : Blo 1375507 1376083 := bstep (se 1 (by rfl) ⟨1032062, by rfl⟩ : syracuseStep 1376083 = 2064125) B2064125
theorem B1376099 : Blo 1375507 1376099 := bstep (se 1 (by rfl) ⟨1032074, by rfl⟩ : syracuseStep 1376099 = 2064149) B2064149
theorem B2064227 : Blo 1375507 2064227 := bstep (se 1 (by rfl) ⟨1548170, by rfl⟩ : syracuseStep 2064227 = 3096341) B3096341
theorem B15679331 : Blo 1375507 15679331 := bstep (se 1 (by rfl) ⟨11759498, by rfl⟩ : syracuseStep 15679331 = 23518997) B23518997
theorem B5226353 : Blo 1375507 5226353 := bstep (se 2 (by rfl) ⟨1959882, by rfl⟩ : syracuseStep 5226353 = 3919765) B3919765
theorem B1376115 : Blo 1375507 1376115 := bstep (se 1 (by rfl) ⟨1032086, by rfl⟩ : syracuseStep 1376115 = 2064173) B2064173
theorem B2064257 : Blo 1375507 2064257 := bstep (se 2 (by rfl) ⟨774096, by rfl⟩ : syracuseStep 2064257 = 1548193) B1548193
theorem B1376131 : Blo 1375507 1376131 := bstep (se 1 (by rfl) ⟨1032098, by rfl⟩ : syracuseStep 1376131 = 2064197) B2064197
theorem B1376147 : Blo 1375507 1376147 := bstep (se 1 (by rfl) ⟨1032110, by rfl⟩ : syracuseStep 1376147 = 2064221) B2064221
theorem B2064275 : Blo 1375507 2064275 := bstep (se 1 (by rfl) ⟨1548206, by rfl⟩ : syracuseStep 2064275 = 3096413) B3096413
theorem B1376163 : Blo 1375507 1376163 := bstep (se 1 (by rfl) ⟨1032122, by rfl⟩ : syracuseStep 1376163 = 2064245) B2064245
theorem B2064305 : Blo 1375507 2064305 := bstep (se 2 (by rfl) ⟨774114, by rfl⟩ : syracuseStep 2064305 = 1548229) B1548229
theorem B1376179 : Blo 1375507 1376179 := bstep (se 1 (by rfl) ⟨1032134, by rfl⟩ : syracuseStep 1376179 = 2064269) B2064269
theorem B1548211 : Blo 1375507 1548211 := bstep (se 1 (by rfl) ⟨1161158, by rfl⟩ : syracuseStep 1548211 = 2322317) B2322317
theorem B1376195 : Blo 1375507 1376195 := bstep (se 1 (by rfl) ⟨1032146, by rfl⟩ : syracuseStep 1376195 = 2064293) B2064293
theorem B2064323 : Blo 1375507 2064323 := bstep (se 1 (by rfl) ⟨1548242, by rfl⟩ : syracuseStep 2064323 = 3096485) B3096485
theorem B1376211 : Blo 1375507 1376211 := bstep (se 1 (by rfl) ⟨1032158, by rfl⟩ : syracuseStep 1376211 = 2064317) B2064317
theorem B2064353 : Blo 1375507 2064353 := bstep (se 2 (by rfl) ⟨774132, by rfl⟩ : syracuseStep 2064353 = 1548265) B1548265
theorem B1376227 : Blo 1375507 1376227 := bstep (se 1 (by rfl) ⟨1032170, by rfl⟩ : syracuseStep 1376227 = 2064341) B2064341
theorem B1376243 : Blo 1375507 1376243 := bstep (se 1 (by rfl) ⟨1032182, by rfl⟩ : syracuseStep 1376243 = 2064365) B2064365
theorem B2064371 : Blo 1375507 2064371 := bstep (se 1 (by rfl) ⟨1548278, by rfl⟩ : syracuseStep 2064371 = 3096557) B3096557
theorem B2064395 : Blo 1375507 2064395 := bstep (se 1 (by rfl) ⟨1548296, by rfl⟩ : syracuseStep 2064395 = 3096593) B3096593
theorem B1376267 : Blo 1375507 1376267 := bstep (se 1 (by rfl) ⟨1032200, by rfl⟩ : syracuseStep 1376267 = 2064401) B2064401
theorem B2064407 : Blo 1375507 2064407 := bstep (se 1 (by rfl) ⟨1548305, by rfl⟩ : syracuseStep 2064407 = 3096611) B3096611
theorem B1376279 : Blo 1375507 1376279 := bstep (se 1 (by rfl) ⟨1032209, by rfl⟩ : syracuseStep 1376279 = 2064419) B2064419
theorem B1376299 : Blo 1375507 1376299 := bstep (se 1 (by rfl) ⟨1032224, by rfl⟩ : syracuseStep 1376299 = 2064449) B2064449
theorem B1376311 : Blo 1375507 1376311 := bstep (se 1 (by rfl) ⟨1032233, by rfl⟩ : syracuseStep 1376311 = 2064467) B2064467
theorem B2613313 : Blo 1375507 2613313 := bstep (se 2 (by rfl) ⟨979992, by rfl⟩ : syracuseStep 2613313 = 1959985) B1959985
theorem B1376331 : Blo 1375507 1376331 := bstep (se 1 (by rfl) ⟨1032248, by rfl⟩ : syracuseStep 1376331 = 2064497) B2064497
theorem B1376343 : Blo 1375507 1376343 := bstep (se 1 (by rfl) ⟨1032257, by rfl⟩ : syracuseStep 1376343 = 2064515) B2064515
theorem B3096665 : Blo 1375507 3096665 := bstep (se 2 (by rfl) ⟨1161249, by rfl⟩ : syracuseStep 3096665 = 2322499) B2322499
theorem B2064473 : Blo 1375507 2064473 := bstep (se 2 (by rfl) ⟨774177, by rfl⟩ : syracuseStep 2064473 = 1548355) B1548355
theorem B1376363 : Blo 1375507 1376363 := bstep (se 1 (by rfl) ⟨1032272, by rfl⟩ : syracuseStep 1376363 = 2064545) B2064545
theorem B1376375 : Blo 1375507 1376375 := bstep (se 1 (by rfl) ⟨1032281, by rfl⟩ : syracuseStep 1376375 = 2064563) B2064563
theorem B1548427 : Blo 1375507 1548427 := bstep (se 1 (by rfl) ⟨1161320, by rfl⟩ : syracuseStep 1548427 = 2322641) B2322641
theorem B1376395 : Blo 1375507 1376395 := bstep (se 1 (by rfl) ⟨1032296, by rfl⟩ : syracuseStep 1376395 = 2064593) B2064593
theorem B1376407 : Blo 1375507 1376407 := bstep (se 1 (by rfl) ⟨1032305, by rfl⟩ : syracuseStep 1376407 = 2064611) B2064611
theorem B1376427 : Blo 1375507 1376427 := bstep (se 1 (by rfl) ⟨1032320, by rfl⟩ : syracuseStep 1376427 = 2064641) B2064641
theorem B3096755 : Blo 1375507 3096755 := bstep (se 1 (by rfl) ⟨2322566, by rfl⟩ : syracuseStep 3096755 = 4645133) B4645133
theorem B1376439 : Blo 1375507 1376439 := bstep (se 1 (by rfl) ⟨1032329, by rfl⟩ : syracuseStep 1376439 = 2064659) B2064659
theorem B2064587 : Blo 1375507 2064587 := bstep (se 1 (by rfl) ⟨1548440, by rfl⟩ : syracuseStep 2064587 = 3096881) B3096881
theorem B1376459 : Blo 1375507 1376459 := bstep (se 1 (by rfl) ⟨1032344, by rfl⟩ : syracuseStep 1376459 = 2064689) B2064689
theorem B3096791 : Blo 1375507 3096791 := bstep (se 1 (by rfl) ⟨2322593, by rfl⟩ : syracuseStep 3096791 = 4645187) B4645187
theorem B2064599 : Blo 1375507 2064599 := bstep (se 1 (by rfl) ⟨1548449, by rfl⟩ : syracuseStep 2064599 = 3096899) B3096899
theorem B1376471 : Blo 1375507 1376471 := bstep (se 1 (by rfl) ⟨1032353, by rfl⟩ : syracuseStep 1376471 = 2064707) B2064707
theorem B1376491 : Blo 1375507 1376491 := bstep (se 1 (by rfl) ⟨1032368, by rfl⟩ : syracuseStep 1376491 = 2064737) B2064737
theorem B1548535 : Blo 1375507 1548535 := bstep (se 1 (by rfl) ⟨1161401, by rfl⟩ : syracuseStep 1548535 = 2322803) B2322803
theorem B1376503 : Blo 1375507 1376503 := bstep (se 1 (by rfl) ⟨1032377, by rfl⟩ : syracuseStep 1376503 = 2064755) B2064755
theorem B1376523 : Blo 1375507 1376523 := bstep (se 1 (by rfl) ⟨1032392, by rfl⟩ : syracuseStep 1376523 = 2064785) B2064785
theorem B9421073 : Blo 1375507 9421073 := bstep (se 2 (by rfl) ⟨3532902, by rfl⟩ : syracuseStep 9421073 = 7065805) B7065805
theorem B1376535 : Blo 1375507 1376535 := bstep (se 1 (by rfl) ⟨1032401, by rfl⟩ : syracuseStep 1376535 = 2064803) B2064803
theorem B2064665 : Blo 1375507 2064665 := bstep (se 2 (by rfl) ⟨774249, by rfl⟩ : syracuseStep 2064665 = 1548499) B1548499
theorem B1376555 : Blo 1375507 1376555 := bstep (se 1 (by rfl) ⟨1032416, by rfl⟩ : syracuseStep 1376555 = 2064833) B2064833
theorem B1376567 : Blo 1375507 1376567 := bstep (se 1 (by rfl) ⟨1032425, by rfl⟩ : syracuseStep 1376567 = 2064851) B2064851
theorem B23527745 : Blo 1375507 23527745 := bstep (se 2 (by rfl) ⟨8822904, by rfl⟩ : syracuseStep 23527745 = 17645809) B17645809
theorem B1376587 : Blo 1375507 1376587 := bstep (se 1 (by rfl) ⟨1032440, by rfl⟩ : syracuseStep 1376587 = 2064881) B2064881
theorem B1376599 : Blo 1375507 1376599 := bstep (se 1 (by rfl) ⟨1032449, by rfl⟩ : syracuseStep 1376599 = 2064899) B2064899
theorem B1376619 : Blo 1375507 1376619 := bstep (se 1 (by rfl) ⟨1032464, by rfl⟩ : syracuseStep 1376619 = 2064929) B2064929
theorem B1376631 : Blo 1375507 1376631 := bstep (se 1 (by rfl) ⟨1032473, by rfl⟩ : syracuseStep 1376631 = 2064947) B2064947
theorem B3096971 : Blo 1375507 3096971 := bstep (se 1 (by rfl) ⟨2322728, by rfl⟩ : syracuseStep 3096971 = 4645457) B4645457
theorem B2064779 : Blo 1375507 2064779 := bstep (se 1 (by rfl) ⟨1548584, by rfl⟩ : syracuseStep 2064779 = 3097169) B3097169
theorem B1376651 : Blo 1375507 1376651 := bstep (se 1 (by rfl) ⟨1032488, by rfl⟩ : syracuseStep 1376651 = 2064977) B2064977
theorem B2064791 : Blo 1375507 2064791 := bstep (se 1 (by rfl) ⟨1548593, by rfl⟩ : syracuseStep 2064791 = 3097187) B3097187
theorem B1376663 : Blo 1375507 1376663 := bstep (se 1 (by rfl) ⟨1032497, by rfl⟩ : syracuseStep 1376663 = 2064995) B2064995
theorem B1548715 : Blo 1375507 1548715 := bstep (se 1 (by rfl) ⟨1161536, by rfl⟩ : syracuseStep 1548715 = 2323073) B2323073
theorem B1376683 : Blo 1375507 1376683 := bstep (se 1 (by rfl) ⟨1032512, by rfl⟩ : syracuseStep 1376683 = 2065025) B2065025
theorem B1376695 : Blo 1375507 1376695 := bstep (se 1 (by rfl) ⟨1032521, by rfl⟩ : syracuseStep 1376695 = 2065043) B2065043
theorem B3097025 : Blo 1375507 3097025 := bstep (se 2 (by rfl) ⟨1161384, by rfl⟩ : syracuseStep 3097025 = 2322769) B2322769
theorem B1376715 : Blo 1375507 1376715 := bstep (se 1 (by rfl) ⟨1032536, by rfl⟩ : syracuseStep 1376715 = 2065073) B2065073
theorem B1376727 : Blo 1375507 1376727 := bstep (se 1 (by rfl) ⟨1032545, by rfl⟩ : syracuseStep 1376727 = 2065091) B2065091
theorem B2064857 : Blo 1375507 2064857 := bstep (se 2 (by rfl) ⟨774321, by rfl⟩ : syracuseStep 2064857 = 1548643) B1548643
theorem B1376747 : Blo 1375507 1376747 := bstep (se 1 (by rfl) ⟨1032560, by rfl⟩ : syracuseStep 1376747 = 2065121) B2065121
theorem B1376759 : Blo 1375507 1376759 := bstep (se 1 (by rfl) ⟨1032569, by rfl⟩ : syracuseStep 1376759 = 2065139) B2065139
theorem B1376779 : Blo 1375507 1376779 := bstep (se 1 (by rfl) ⟨1032584, by rfl⟩ : syracuseStep 1376779 = 2065169) B2065169
theorem B1548823 : Blo 1375507 1548823 := bstep (se 1 (by rfl) ⟨1161617, by rfl⟩ : syracuseStep 1548823 = 2323235) B2323235
theorem B1376791 : Blo 1375507 1376791 := bstep (se 1 (by rfl) ⟨1032593, by rfl⟩ : syracuseStep 1376791 = 2065187) B2065187
theorem B1376811 : Blo 1375507 1376811 := bstep (se 1 (by rfl) ⟨1032608, by rfl⟩ : syracuseStep 1376811 = 2065217) B2065217
theorem B1376823 : Blo 1375507 1376823 := bstep (se 1 (by rfl) ⟨1032617, by rfl⟩ : syracuseStep 1376823 = 2065235) B2065235
theorem B2064971 : Blo 1375507 2064971 := bstep (se 1 (by rfl) ⟨1548728, by rfl⟩ : syracuseStep 2064971 = 3097457) B3097457
theorem B1376843 : Blo 1375507 1376843 := bstep (se 1 (by rfl) ⟨1032632, by rfl⟩ : syracuseStep 1376843 = 2065265) B2065265
theorem B2064983 : Blo 1375507 2064983 := bstep (se 1 (by rfl) ⟨1548737, by rfl⟩ : syracuseStep 2064983 = 3097475) B3097475
theorem B1376855 : Blo 1375507 1376855 := bstep (se 1 (by rfl) ⟨1032641, by rfl⟩ : syracuseStep 1376855 = 2065283) B2065283
theorem B1860185 : Blo 1375507 1860185 := bstep (se 2 (by rfl) ⟨697569, by rfl⟩ : syracuseStep 1860185 = 1395139) B1395139
theorem B17646173 : Blo 1375507 17646173 := bstep (se 3 (by rfl) ⟨3308657, by rfl⟩ : syracuseStep 17646173 = 6617315) B6617315
theorem B1376875 : Blo 1375507 1376875 := bstep (se 1 (by rfl) ⟨1032656, by rfl⟩ : syracuseStep 1376875 = 2065313) B2065313
theorem B1376887 : Blo 1375507 1376887 := bstep (se 1 (by rfl) ⟨1032665, by rfl⟩ : syracuseStep 1376887 = 2065331) B2065331
theorem B17638019 : Blo 1375507 17638019 := bstep (se 1 (by rfl) ⟨13228514, by rfl⟩ : syracuseStep 17638019 = 26457029) B26457029
theorem B1376907 : Blo 1375507 1376907 := bstep (se 1 (by rfl) ⟨1032680, by rfl⟩ : syracuseStep 1376907 = 2065361) B2065361
theorem B1376919 : Blo 1375507 1376919 := bstep (se 1 (by rfl) ⟨1032689, by rfl⟩ : syracuseStep 1376919 = 2065379) B2065379
theorem B3097241 : Blo 1375507 3097241 := bstep (se 2 (by rfl) ⟨1161465, by rfl⟩ : syracuseStep 3097241 = 2322931) B2322931
theorem B2065049 : Blo 1375507 2065049 := bstep (se 2 (by rfl) ⟨774393, by rfl⟩ : syracuseStep 2065049 = 1548787) B1548787
theorem B1376939 : Blo 1375507 1376939 := bstep (se 1 (by rfl) ⟨1032704, by rfl⟩ : syracuseStep 1376939 = 2065409) B2065409
theorem B3482291 : Blo 1375507 3482291 := bstep (se 1 (by rfl) ⟨2611718, by rfl⟩ : syracuseStep 3482291 = 5223437) B5223437
theorem B1376951 : Blo 1375507 1376951 := bstep (se 1 (by rfl) ⟨1032713, by rfl⟩ : syracuseStep 1376951 = 2065427) B2065427
theorem B1549003 : Blo 1375507 1549003 := bstep (se 1 (by rfl) ⟨1161752, by rfl⟩ : syracuseStep 1549003 = 2323505) B2323505
theorem B1376971 : Blo 1375507 1376971 := bstep (se 1 (by rfl) ⟨1032728, by rfl⟩ : syracuseStep 1376971 = 2065457) B2065457
theorem B1376983 : Blo 1375507 1376983 := bstep (se 1 (by rfl) ⟨1032737, by rfl⟩ : syracuseStep 1376983 = 2065475) B2065475
theorem B1377003 : Blo 1375507 1377003 := bstep (se 1 (by rfl) ⟨1032752, by rfl⟩ : syracuseStep 1377003 = 2065505) B2065505
theorem B3097331 : Blo 1375507 3097331 := bstep (se 1 (by rfl) ⟨2322998, by rfl⟩ : syracuseStep 3097331 = 4645997) B4645997
theorem B1377015 : Blo 1375507 1377015 := bstep (se 1 (by rfl) ⟨1032761, by rfl⟩ : syracuseStep 1377015 = 2065523) B2065523
theorem B2065163 : Blo 1375507 2065163 := bstep (se 1 (by rfl) ⟨1548872, by rfl⟩ : syracuseStep 2065163 = 3097745) B3097745
theorem B2614027 : Blo 1375507 2614027 := bstep (se 1 (by rfl) ⟨1960520, by rfl⟩ : syracuseStep 2614027 = 3921041) B3921041
theorem B1377035 : Blo 1375507 1377035 := bstep (se 1 (by rfl) ⟨1032776, by rfl⟩ : syracuseStep 1377035 = 2065553) B2065553
theorem B3097367 : Blo 1375507 3097367 := bstep (se 1 (by rfl) ⟨2323025, by rfl⟩ : syracuseStep 3097367 = 4646051) B4646051
theorem B2065175 : Blo 1375507 2065175 := bstep (se 1 (by rfl) ⟨1548881, by rfl⟩ : syracuseStep 2065175 = 3097763) B3097763
theorem B1958681 : Blo 1375507 1958681 := bstep (se 2 (by rfl) ⟨734505, by rfl⟩ : syracuseStep 1958681 = 1469011) B1469011
theorem B1377047 : Blo 1375507 1377047 := bstep (se 1 (by rfl) ⟨1032785, by rfl⟩ : syracuseStep 1377047 = 2065571) B2065571
theorem B1377067 : Blo 1375507 1377067 := bstep (se 1 (by rfl) ⟨1032800, by rfl⟩ : syracuseStep 1377067 = 2065601) B2065601
theorem B1549111 : Blo 1375507 1549111 := bstep (se 1 (by rfl) ⟨1161833, by rfl⟩ : syracuseStep 1549111 = 2323667) B2323667
theorem B1377079 : Blo 1375507 1377079 := bstep (se 1 (by rfl) ⟨1032809, by rfl⟩ : syracuseStep 1377079 = 2065619) B2065619
theorem B7840577 : Blo 1375507 7840577 := bstep (se 2 (by rfl) ⟨2940216, by rfl⟩ : syracuseStep 7840577 = 5880433) B5880433
theorem B2204491 : Blo 1375507 2204491 := bstep (se 1 (by rfl) ⟨1653368, by rfl⟩ : syracuseStep 2204491 = 3306737) B3306737
theorem B1377099 : Blo 1375507 1377099 := bstep (se 1 (by rfl) ⟨1032824, by rfl⟩ : syracuseStep 1377099 = 2065649) B2065649
theorem B2614103 : Blo 1375507 2614103 := bstep (se 1 (by rfl) ⟨1960577, by rfl⟩ : syracuseStep 2614103 = 3921155) B3921155
theorem B2065241 : Blo 1375507 2065241 := bstep (se 2 (by rfl) ⟨774465, by rfl⟩ : syracuseStep 2065241 = 1548931) B1548931
theorem B1377111 : Blo 1375507 1377111 := bstep (se 1 (by rfl) ⟨1032833, by rfl⟩ : syracuseStep 1377111 = 2065667) B2065667
theorem B1377131 : Blo 1375507 1377131 := bstep (se 1 (by rfl) ⟨1032848, by rfl⟩ : syracuseStep 1377131 = 2065697) B2065697
theorem B1377143 : Blo 1375507 1377143 := bstep (se 1 (by rfl) ⟨1032857, by rfl⟩ : syracuseStep 1377143 = 2065715) B2065715
theorem B1377163 : Blo 1375507 1377163 := bstep (se 1 (by rfl) ⟨1032872, by rfl⟩ : syracuseStep 1377163 = 2065745) B2065745
theorem B1377175 : Blo 1375507 1377175 := bstep (se 1 (by rfl) ⟨1032881, by rfl⟩ : syracuseStep 1377175 = 2065763) B2065763
theorem B2941849 : Blo 1375507 2941849 := bstep (se 2 (by rfl) ⟨1103193, by rfl⟩ : syracuseStep 2941849 = 2206387) B2206387
theorem B1377195 : Blo 1375507 1377195 := bstep (se 1 (by rfl) ⟨1032896, by rfl⟩ : syracuseStep 1377195 = 2065793) B2065793
theorem B21201841 : Blo 1375507 21201841 := bstep (se 2 (by rfl) ⟨7950690, by rfl⟩ : syracuseStep 21201841 = 15901381) B15901381
theorem B1377207 : Blo 1375507 1377207 := bstep (se 1 (by rfl) ⟨1032905, by rfl⟩ : syracuseStep 1377207 = 2065811) B2065811
theorem B4645835 : Blo 1375507 4645835 := bstep (se 1 (by rfl) ⟨3484376, by rfl⟩ : syracuseStep 4645835 = 6968753) B6968753
theorem B3097547 : Blo 1375507 3097547 := bstep (se 1 (by rfl) ⟨2323160, by rfl⟩ : syracuseStep 3097547 = 4646321) B4646321
theorem B2065355 : Blo 1375507 2065355 := bstep (se 1 (by rfl) ⟨1549016, by rfl⟩ : syracuseStep 2065355 = 3098033) B3098033
theorem B1377227 : Blo 1375507 1377227 := bstep (se 1 (by rfl) ⟨1032920, by rfl⟩ : syracuseStep 1377227 = 2065841) B2065841
theorem B2065367 : Blo 1375507 2065367 := bstep (se 1 (by rfl) ⟨1549025, by rfl⟩ : syracuseStep 2065367 = 3098051) B3098051
theorem B1377239 : Blo 1375507 1377239 := bstep (se 1 (by rfl) ⟨1032929, by rfl⟩ : syracuseStep 1377239 = 2065859) B2065859
theorem B3482585 : Blo 1375507 3482585 := bstep (se 2 (by rfl) ⟨1305969, by rfl⟩ : syracuseStep 3482585 = 2611939) B2611939
theorem B1549291 : Blo 1375507 1549291 := bstep (se 1 (by rfl) ⟨1161968, by rfl⟩ : syracuseStep 1549291 = 2323937) B2323937
theorem B1377259 : Blo 1375507 1377259 := bstep (se 1 (by rfl) ⟨1032944, by rfl⟩ : syracuseStep 1377259 = 2065889) B2065889
theorem B1377271 : Blo 1375507 1377271 := bstep (se 1 (by rfl) ⟨1032953, by rfl⟩ : syracuseStep 1377271 = 2065907) B2065907
theorem B3097601 : Blo 1375507 3097601 := bstep (se 2 (by rfl) ⟨1161600, by rfl⟩ : syracuseStep 3097601 = 2323201) B2323201
theorem B5227523 : Blo 1375507 5227523 := bstep (se 1 (by rfl) ⟨3920642, by rfl⟩ : syracuseStep 5227523 = 7841285) B7841285
theorem B1377291 : Blo 1375507 1377291 := bstep (se 1 (by rfl) ⟨1032968, by rfl⟩ : syracuseStep 1377291 = 2065937) B2065937
theorem B5227537 : Blo 1375507 5227537 := bstep (se 2 (by rfl) ⟨1960326, by rfl⟩ : syracuseStep 5227537 = 3920653) B3920653
theorem B1377303 : Blo 1375507 1377303 := bstep (se 1 (by rfl) ⟨1032977, by rfl⟩ : syracuseStep 1377303 = 2065955) B2065955
theorem B2065433 : Blo 1375507 2065433 := bstep (se 2 (by rfl) ⟨774537, by rfl⟩ : syracuseStep 2065433 = 1549075) B1549075
theorem B19842083 : Blo 1375507 19842083 := bstep (se 1 (by rfl) ⟨14881562, by rfl⟩ : syracuseStep 19842083 = 29763125) B29763125
theorem B1377323 : Blo 1375507 1377323 := bstep (se 1 (by rfl) ⟨1032992, by rfl⟩ : syracuseStep 1377323 = 2065985) B2065985
theorem B1377335 : Blo 1375507 1377335 := bstep (se 1 (by rfl) ⟨1033001, by rfl⟩ : syracuseStep 1377335 = 2066003) B2066003
theorem B2204747 : Blo 1375507 2204747 := bstep (se 1 (by rfl) ⟨1653560, by rfl⟩ : syracuseStep 2204747 = 3307121) B3307121
theorem B1377355 : Blo 1375507 1377355 := bstep (se 1 (by rfl) ⟨1033016, by rfl⟩ : syracuseStep 1377355 = 2066033) B2066033
theorem B1549399 : Blo 1375507 1549399 := bstep (se 1 (by rfl) ⟨1162049, by rfl⟩ : syracuseStep 1549399 = 2324099) B2324099
theorem B1377367 : Blo 1375507 1377367 := bstep (se 1 (by rfl) ⟨1033025, by rfl⟩ : syracuseStep 1377367 = 2066051) B2066051
theorem B1377387 : Blo 1375507 1377387 := bstep (se 1 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 1377387 = 2066081) B2066081
theorem B1377399 : Blo 1375507 1377399 := bstep (se 1 (by rfl) ⟨1033049, by rfl⟩ : syracuseStep 1377399 = 2066099) B2066099
theorem B2065547 : Blo 1375507 2065547 := bstep (se 1 (by rfl) ⟨1549160, by rfl⟩ : syracuseStep 2065547 = 3098321) B3098321
theorem B1377419 : Blo 1375507 1377419 := bstep (se 1 (by rfl) ⟨1033064, by rfl⟩ : syracuseStep 1377419 = 2066129) B2066129
theorem B2065559 : Blo 1375507 2065559 := bstep (se 1 (by rfl) ⟨1549169, by rfl⟩ : syracuseStep 2065559 = 3098339) B3098339
theorem B1377431 : Blo 1375507 1377431 := bstep (se 1 (by rfl) ⟨1033073, by rfl⟩ : syracuseStep 1377431 = 2066147) B2066147
theorem B1377451 : Blo 1375507 1377451 := bstep (se 1 (by rfl) ⟨1033088, by rfl⟩ : syracuseStep 1377451 = 2066177) B2066177
theorem B3769523 : Blo 1375507 3769523 := bstep (se 1 (by rfl) ⟨2827142, by rfl⟩ : syracuseStep 3769523 = 5654285) B5654285
theorem B160859317 : Blo 1375507 160859317 := bstep (se 5 (by rfl) ⟨7540280, by rfl⟩ : syracuseStep 160859317 = 15080561) B15080561
theorem B1377463 : Blo 1375507 1377463 := bstep (se 1 (by rfl) ⟨1033097, by rfl⟩ : syracuseStep 1377463 = 2066195) B2066195
theorem B1377483 : Blo 1375507 1377483 := bstep (se 1 (by rfl) ⟨1033112, by rfl⟩ : syracuseStep 1377483 = 2066225) B2066225
theorem B1377495 : Blo 1375507 1377495 := bstep (se 1 (by rfl) ⟨1033121, by rfl⟩ : syracuseStep 1377495 = 2066243) B2066243
theorem B4646105 : Blo 1375507 4646105 := bstep (se 2 (by rfl) ⟨1742289, by rfl⟩ : syracuseStep 4646105 = 3484579) B3484579
theorem B3097817 : Blo 1375507 3097817 := bstep (se 2 (by rfl) ⟨1161681, by rfl⟩ : syracuseStep 3097817 = 2323363) B2323363
theorem B2065625 : Blo 1375507 2065625 := bstep (se 2 (by rfl) ⟨774609, by rfl⟩ : syracuseStep 2065625 = 1549219) B1549219
theorem B1549579 : Blo 1375507 1549579 := bstep (se 1 (by rfl) ⟨1162184, by rfl⟩ : syracuseStep 1549579 = 2324369) B2324369
theorem B3097907 : Blo 1375507 3097907 := bstep (se 1 (by rfl) ⟨2323430, by rfl⟩ : syracuseStep 3097907 = 4646861) B4646861
theorem B5227841 : Blo 1375507 5227841 := bstep (se 2 (by rfl) ⟨1960440, by rfl⟩ : syracuseStep 5227841 = 3920881) B3920881
theorem B2065739 : Blo 1375507 2065739 := bstep (se 1 (by rfl) ⟨1549304, by rfl⟩ : syracuseStep 2065739 = 3098609) B3098609
theorem B3097943 : Blo 1375507 3097943 := bstep (se 1 (by rfl) ⟨2323457, by rfl⟩ : syracuseStep 3097943 = 4646915) B4646915
theorem B2065751 : Blo 1375507 2065751 := bstep (se 1 (by rfl) ⟨1549313, by rfl⟩ : syracuseStep 2065751 = 3098627) B3098627
theorem B1549687 : Blo 1375507 1549687 := bstep (se 1 (by rfl) ⟨1162265, by rfl⟩ : syracuseStep 1549687 = 2324531) B2324531
theorem B6972803 : Blo 1375507 6972803 := bstep (se 1 (by rfl) ⟨5229602, by rfl⟩ : syracuseStep 6972803 = 10459205) B10459205
theorem B1959319 : Blo 1375507 1959319 := bstep (se 1 (by rfl) ⟨1469489, by rfl⟩ : syracuseStep 1959319 = 2938979) B2938979
theorem B2065817 : Blo 1375507 2065817 := bstep (se 2 (by rfl) ⟨774681, by rfl⟩ : syracuseStep 2065817 = 1549363) B1549363
theorem B2614771 : Blo 1375507 2614771 := bstep (se 1 (by rfl) ⟨1961078, by rfl⟩ : syracuseStep 2614771 = 3922157) B3922157
theorem B3098123 : Blo 1375507 3098123 := bstep (se 1 (by rfl) ⟨2323592, by rfl⟩ : syracuseStep 3098123 = 4647185) B4647185
theorem B2065931 : Blo 1375507 2065931 := bstep (se 1 (by rfl) ⟨1549448, by rfl⟩ : syracuseStep 2065931 = 3098897) B3098897
theorem B2065943 : Blo 1375507 2065943 := bstep (se 1 (by rfl) ⟨1549457, by rfl⟩ : syracuseStep 2065943 = 3098915) B3098915
theorem B3098177 : Blo 1375507 3098177 := bstep (se 2 (by rfl) ⟨1161816, by rfl⟩ : syracuseStep 3098177 = 2323633) B2323633
theorem B15894091 : Blo 1375507 15894091 := bstep (se 1 (by rfl) ⟨11920568, by rfl⟩ : syracuseStep 15894091 = 23841137) B23841137
theorem B2066009 : Blo 1375507 2066009 := bstep (se 2 (by rfl) ⟨774753, by rfl⟩ : syracuseStep 2066009 = 1549507) B1549507
theorem B2066123 : Blo 1375507 2066123 := bstep (se 1 (by rfl) ⟨1549592, by rfl⟩ : syracuseStep 2066123 = 3099185) B3099185
theorem B2066135 : Blo 1375507 2066135 := bstep (se 1 (by rfl) ⟨1549601, by rfl⟩ : syracuseStep 2066135 = 3099203) B3099203
theorem B2614999 : Blo 1375507 2614999 := bstep (se 1 (by rfl) ⟨1961249, by rfl⟩ : syracuseStep 2614999 = 3922499) B3922499
theorem B3098393 : Blo 1375507 3098393 := bstep (se 2 (by rfl) ⟨1161897, by rfl⟩ : syracuseStep 3098393 = 2323795) B2323795
theorem B2066201 : Blo 1375507 2066201 := bstep (se 2 (by rfl) ⟨774825, by rfl⟩ : syracuseStep 2066201 = 1549651) B1549651
theorem B15689537 : Blo 1375507 15689537 := bstep (se 2 (by rfl) ⟨5883576, by rfl⟩ : syracuseStep 15689537 = 11767153) B11767153
theorem B2615105 : Blo 1375507 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B3098483 : Blo 1375507 3098483 := bstep (se 1 (by rfl) ⟨2323862, by rfl⟩ : syracuseStep 3098483 = 4647725) B4647725
theorem B4646807 : Blo 1375507 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B3098519 : Blo 1375507 3098519 := bstep (se 1 (by rfl) ⟨2323889, by rfl⟩ : syracuseStep 3098519 = 4647779) B4647779
theorem B8824727 : Blo 1375507 8824727 := bstep (se 1 (by rfl) ⟨6618545, by rfl⟩ : syracuseStep 8824727 = 13237091) B13237091
theorem B5875649 : Blo 1375507 5875649 := bstep (se 2 (by rfl) ⟨2203368, by rfl⟩ : syracuseStep 5875649 = 4406737) B4406737
theorem B5228509 : Blo 1375507 5228509 := bstep (se 3 (by rfl) ⟨980345, by rfl⟩ : syracuseStep 5228509 = 1960691) B1960691
theorem B2205721 : Blo 1375507 2205721 := bstep (se 2 (by rfl) ⟨827145, by rfl⟩ : syracuseStep 2205721 = 1654291) B1654291
theorem B21489733 : Blo 1375507 21489733 := bstep (se 4 (by rfl) ⟨2014662, by rfl⟩ : syracuseStep 21489733 = 4029325) B4029325
theorem B3098699 : Blo 1375507 3098699 := bstep (se 1 (by rfl) ⟨2324024, by rfl⟩ : syracuseStep 3098699 = 4648049) B4648049
theorem B3975257 : Blo 1375507 3975257 := bstep (se 2 (by rfl) ⟨1490721, by rfl⟩ : syracuseStep 3975257 = 2981443) B2981443
theorem B3098753 : Blo 1375507 3098753 := bstep (se 2 (by rfl) ⟨1162032, by rfl⟩ : syracuseStep 3098753 = 2324065) B2324065
theorem B3721409 : Blo 1375507 3721409 := bstep (se 2 (by rfl) ⟨1395528, by rfl⟩ : syracuseStep 3721409 = 2791057) B2791057
theorem B1960139 : Blo 1375507 1960139 := bstep (se 1 (by rfl) ⟨1470104, by rfl⟩ : syracuseStep 1960139 = 2940209) B2940209
theorem B3098969 : Blo 1375507 3098969 := bstep (se 2 (by rfl) ⟨1162113, by rfl⟩ : syracuseStep 3098969 = 2324227) B2324227
theorem B5294429 : Blo 1375507 5294429 := bstep (se 3 (by rfl) ⟨992705, by rfl⟩ : syracuseStep 5294429 = 1985411) B1985411
theorem B4647347 : Blo 1375507 4647347 := bstep (se 1 (by rfl) ⟨3485510, by rfl⟩ : syracuseStep 4647347 = 6971021) B6971021
theorem B3099059 : Blo 1375507 3099059 := bstep (se 1 (by rfl) ⟨2324294, by rfl⟩ : syracuseStep 3099059 = 4648589) B4648589
theorem B1395127 : Blo 1375507 1395127 := bstep (se 1 (by rfl) ⟨1046345, by rfl⟩ : syracuseStep 1395127 = 2092691) B2092691
theorem B3099095 : Blo 1375507 3099095 := bstep (se 1 (by rfl) ⟨2324321, by rfl⟩ : syracuseStep 3099095 = 4648643) B4648643
theorem B17885731 : Blo 1375507 17885731 := bstep (se 1 (by rfl) ⟨13414298, by rfl⟩ : syracuseStep 17885731 = 26828597) B26828597
theorem B3484235 : Blo 1375507 3484235 := bstep (se 1 (by rfl) ⟨2613176, by rfl⟩ : syracuseStep 3484235 = 5226353) B5226353
theorem B3099275 : Blo 1375507 3099275 := bstep (se 1 (by rfl) ⟨2324456, by rfl⟩ : syracuseStep 3099275 = 4648913) B4648913
theorem B4647617 : Blo 1375507 4647617 := bstep (se 2 (by rfl) ⟨1742856, by rfl⟩ : syracuseStep 4647617 = 3485713) B3485713
theorem B3099329 : Blo 1375507 3099329 := bstep (se 2 (by rfl) ⟨1162248, by rfl⟩ : syracuseStep 3099329 = 2324497) B2324497
theorem B6613721 : Blo 1375507 6613721 := bstep (se 2 (by rfl) ⟨2480145, by rfl⟩ : syracuseStep 6613721 = 4960291) B4960291
theorem B3918557 : Blo 1375507 3918557 := bstep (se 3 (by rfl) ⟨734729, by rfl⟩ : syracuseStep 3918557 = 1469459) B1469459
theorem B6277981 : Blo 1375507 6277981 := bstep (se 3 (by rfl) ⟨1177121, by rfl⟩ : syracuseStep 6277981 = 2354243) B2354243
theorem B2829185 : Blo 1375507 2829185 := bstep (se 2 (by rfl) ⟨1060944, by rfl⟩ : syracuseStep 2829185 = 2121889) B2121889
theorem B2321291 : Blo 1375507 2321291 := bstep (se 1 (by rfl) ⟨1740968, by rfl⟩ : syracuseStep 2321291 = 3481937) B3481937
theorem B1469387 : Blo 1375507 1469387 := bstep (se 1 (by rfl) ⟨1102040, by rfl⟩ : syracuseStep 1469387 = 2204081) B2204081
theorem B2321419 : Blo 1375507 2321419 := bstep (se 1 (by rfl) ⟨1741064, by rfl⟩ : syracuseStep 2321419 = 3482129) B3482129
theorem B31771723 : Blo 1375507 31771723 := bstep (se 1 (by rfl) ⟨23828792, by rfl⟩ : syracuseStep 31771723 = 47657585) B47657585
theorem B2321561 : Blo 1375507 2321561 := bstep (se 2 (by rfl) ⟨870585, by rfl⟩ : syracuseStep 2321561 = 1741171) B1741171
theorem B1961113 : Blo 1375507 1961113 := bstep (se 2 (by rfl) ⟨735417, by rfl⟩ : syracuseStep 1961113 = 1470835) B1470835
theorem B5229785 : Blo 1375507 5229785 := bstep (se 2 (by rfl) ⟨1961169, by rfl⟩ : syracuseStep 5229785 = 3922339) B3922339
theorem B4648157 : Blo 1375507 4648157 := bstep (se 3 (by rfl) ⟨871529, by rfl⟩ : syracuseStep 4648157 = 1743059) B1743059
theorem B6278417 : Blo 1375507 6278417 := bstep (se 2 (by rfl) ⟨2354406, by rfl⟩ : syracuseStep 6278417 = 4708813) B4708813
theorem B2321689 : Blo 1375507 2321689 := bstep (se 2 (by rfl) ⟨870633, by rfl⟩ : syracuseStep 2321689 = 1741267) B1741267
theorem B18836837 : Blo 1375507 18836837 := bstep (se 4 (by rfl) ⟨1765953, by rfl⟩ : syracuseStep 18836837 = 3531907) B3531907
theorem B5877137 : Blo 1375507 5877137 := bstep (se 2 (by rfl) ⟨2203926, by rfl⟩ : syracuseStep 5877137 = 4407853) B4407853
theorem B31763981 : Blo 1375507 31763981 := bstep (se 3 (by rfl) ⟨5955746, by rfl⟩ : syracuseStep 31763981 = 11911493) B11911493
theorem B3485207 : Blo 1375507 3485207 := bstep (se 1 (by rfl) ⟨2613905, by rfl⟩ : syracuseStep 3485207 = 5227811) B5227811
theorem B7835201 : Blo 1375507 7835201 := bstep (se 2 (by rfl) ⟨2938200, by rfl⟩ : syracuseStep 7835201 = 5876401) B5876401
theorem B11767427 : Blo 1375507 11767427 := bstep (se 1 (by rfl) ⟨8825570, by rfl⟩ : syracuseStep 11767427 = 17651141) B17651141
theorem B1986329 : Blo 1375507 1986329 := bstep (se 2 (by rfl) ⟨744873, by rfl⟩ : syracuseStep 1986329 = 1489747) B1489747
theorem B2322263 : Blo 1375507 2322263 := bstep (se 1 (by rfl) ⟨1741697, by rfl⟩ : syracuseStep 2322263 = 3483395) B3483395
theorem B6967133 : Blo 1375507 6967133 := bstep (se 3 (by rfl) ⟨1306337, by rfl⟩ : syracuseStep 6967133 = 2612675) B2612675
theorem B26824547 : Blo 1375507 26824547 := bstep (se 1 (by rfl) ⟨20118410, by rfl⟩ : syracuseStep 26824547 = 40236821) B40236821
theorem B1568683 : Blo 1375507 1568683 := bstep (se 1 (by rfl) ⟨1176512, by rfl⟩ : syracuseStep 1568683 = 2353025) B2353025
theorem B14135219 : Blo 1375507 14135219 := bstep (se 1 (by rfl) ⟨10601414, by rfl⟩ : syracuseStep 14135219 = 21202829) B21202829
theorem B2322391 : Blo 1375507 2322391 := bstep (se 1 (by rfl) ⟨1741793, by rfl⟩ : syracuseStep 2322391 = 3483587) B3483587
theorem B4960349 : Blo 1375507 4960349 := bstep (se 3 (by rfl) ⟨930065, by rfl⟩ : syracuseStep 4960349 = 1860131) B1860131
theorem B1470583 : Blo 1375507 1470583 := bstep (se 1 (by rfl) ⟨1102937, by rfl⟩ : syracuseStep 1470583 = 2205875) B2205875
theorem B2789515 : Blo 1375507 2789515 := bstep (se 1 (by rfl) ⟨2092136, by rfl⟩ : syracuseStep 2789515 = 4184273) B4184273
theorem B3485875 : Blo 1375507 3485875 := bstep (se 1 (by rfl) ⟨2614406, by rfl⟩ : syracuseStep 3485875 = 5228813) B5228813
theorem B11751641 : Blo 1375507 11751641 := bstep (se 2 (by rfl) ⟨4406865, by rfl⟩ : syracuseStep 11751641 = 8813731) B8813731
theorem B3486017 : Blo 1375507 3486017 := bstep (se 2 (by rfl) ⟨1307256, by rfl⟩ : syracuseStep 3486017 = 2614513) B2614513
theorem B2871641 : Blo 1375507 2871641 := bstep (se 2 (by rfl) ⟨1076865, by rfl⟩ : syracuseStep 2871641 = 2153731) B2153731
theorem B5878109 : Blo 1375507 5878109 := bstep (se 3 (by rfl) ⟨1102145, by rfl⟩ : syracuseStep 5878109 = 2204291) B2204291
theorem B22925747 : Blo 1375507 22925747 := bstep (se 1 (by rfl) ⟨17194310, by rfl⟩ : syracuseStep 22925747 = 34388621) B34388621
theorem B2323019 : Blo 1375507 2323019 := bstep (se 1 (by rfl) ⟨1742264, by rfl⟩ : syracuseStep 2323019 = 3484529) B3484529
theorem B18133579 : Blo 1375507 18133579 := bstep (se 1 (by rfl) ⟨13600184, by rfl⟩ : syracuseStep 18133579 = 27200369) B27200369
theorem B1987211 : Blo 1375507 1987211 := bstep (se 1 (by rfl) ⟨1490408, by rfl⟩ : syracuseStep 1987211 = 2980817) B2980817
theorem B2323147 : Blo 1375507 2323147 := bstep (se 1 (by rfl) ⟨1742360, by rfl⟩ : syracuseStep 2323147 = 3484721) B3484721
theorem B2790131 : Blo 1375507 2790131 := bstep (se 1 (by rfl) ⟨2092598, by rfl⟩ : syracuseStep 2790131 = 4185197) B4185197
theorem B4961027 : Blo 1375507 4961027 := bstep (se 1 (by rfl) ⟨3720770, by rfl⟩ : syracuseStep 4961027 = 7441541) B7441541
theorem B11760389 : Blo 1375507 11760389 := bstep (se 4 (by rfl) ⟨1102536, by rfl⟩ : syracuseStep 11760389 = 2205073) B2205073
theorem B3183371 : Blo 1375507 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B1741591 : Blo 1375507 1741591 := bstep (se 1 (by rfl) ⟨1306193, by rfl⟩ : syracuseStep 1741591 = 2612387) B2612387
theorem B2323289 : Blo 1375507 2323289 := bstep (se 2 (by rfl) ⟨871233, by rfl⟩ : syracuseStep 2323289 = 1742467) B1742467
theorem B2323417 : Blo 1375507 2323417 := bstep (se 2 (by rfl) ⟨871281, by rfl⟩ : syracuseStep 2323417 = 1742563) B1742563
theorem B2094155 : Blo 1375507 2094155 := bstep (se 1 (by rfl) ⟨1570616, by rfl⟩ : syracuseStep 2094155 = 3141233) B3141233
theorem B2790553 : Blo 1375507 2790553 := bstep (se 2 (by rfl) ⟨1046457, by rfl⟩ : syracuseStep 2790553 = 2092915) B2092915
theorem B13407437 : Blo 1375507 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B4183447 : Blo 1375507 4183447 := bstep (se 1 (by rfl) ⟨3137585, by rfl⟩ : syracuseStep 4183447 = 6275171) B6275171
theorem B5223953 : Blo 1375507 5223953 := bstep (se 2 (by rfl) ⟨1958982, by rfl⟩ : syracuseStep 5223953 = 3917965) B3917965
theorem B2323991 : Blo 1375507 2323991 := bstep (se 1 (by rfl) ⟨1742993, by rfl⟩ : syracuseStep 2323991 = 3485987) B3485987
theorem B3921473 : Blo 1375507 3921473 := bstep (se 2 (by rfl) ⟨1470552, by rfl⟩ : syracuseStep 3921473 = 2941105) B2941105
theorem B4642379 : Blo 1375507 4642379 := bstep (se 1 (by rfl) ⟨3481784, by rfl⟩ : syracuseStep 4642379 = 6963569) B6963569
theorem B1742411 : Blo 1375507 1742411 := bstep (se 1 (by rfl) ⟨1306808, by rfl⟩ : syracuseStep 1742411 = 2613617) B2613617
theorem B2938457 : Blo 1375507 2938457 := bstep (se 2 (by rfl) ⟨1101921, by rfl⟩ : syracuseStep 2938457 = 2203843) B2203843
theorem B3921497 : Blo 1375507 3921497 := bstep (se 2 (by rfl) ⟨1470561, by rfl⟩ : syracuseStep 3921497 = 2941123) B2941123
theorem B2324119 : Blo 1375507 2324119 := bstep (se 1 (by rfl) ⟨1743089, by rfl⟩ : syracuseStep 2324119 = 3486179) B3486179
theorem B4708019 : Blo 1375507 4708019 := bstep (se 1 (by rfl) ⟨3531014, by rfl⟩ : syracuseStep 4708019 = 7062029) B7062029
theorem B7444241 : Blo 1375507 7444241 := bstep (se 2 (by rfl) ⟨2791590, by rfl⟩ : syracuseStep 7444241 = 5583181) B5583181
theorem B4642649 : Blo 1375507 4642649 := bstep (se 2 (by rfl) ⟨1740993, by rfl⟩ : syracuseStep 4642649 = 3481987) B3481987
theorem B1570699 : Blo 1375507 1570699 := bstep (se 1 (by rfl) ⟨1178024, by rfl⟩ : syracuseStep 1570699 = 2356049) B2356049
theorem B6969239 : Blo 1375507 6969239 := bstep (se 1 (by rfl) ⟨5226929, by rfl⟩ : syracuseStep 6969239 = 10453859) B10453859
theorem B5224409 : Blo 1375507 5224409 := bstep (se 2 (by rfl) ⟨1959153, by rfl⟩ : syracuseStep 5224409 = 3918307) B3918307
theorem B14882777 : Blo 1375507 14882777 := bstep (se 2 (by rfl) ⟨5581041, by rfl⟩ : syracuseStep 14882777 = 11162083) B11162083
theorem B12564497 : Blo 1375507 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B4241497 : Blo 1375507 4241497 := bstep (se 2 (by rfl) ⟨1590561, by rfl⟩ : syracuseStep 4241497 = 3181123) B3181123
theorem B5224621 : Blo 1375507 5224621 := bstep (se 3 (by rfl) ⟨979616, by rfl⟩ : syracuseStep 5224621 = 1959233) B1959233
theorem B2611415 : Blo 1375507 2611415 := bstep (se 1 (by rfl) ⟨1958561, by rfl⟩ : syracuseStep 2611415 = 3917123) B3917123
theorem B2939123 : Blo 1375507 2939123 := bstep (se 1 (by rfl) ⟨2204342, by rfl⟩ : syracuseStep 2939123 = 4408685) B4408685
theorem B1743115 : Blo 1375507 1743115 := bstep (se 1 (by rfl) ⟨1307336, by rfl⟩ : syracuseStep 1743115 = 2614673) B2614673
theorem B3094937 : Blo 1375507 3094937 := bstep (se 2 (by rfl) ⟨1160601, by rfl⟩ : syracuseStep 3094937 = 2321203) B2321203
theorem B5577133 : Blo 1375507 5577133 := bstep (se 3 (by rfl) ⟨1045712, by rfl⟩ : syracuseStep 5577133 = 2091425) B2091425
theorem B15677873 : Blo 1375507 15677873 := bstep (se 2 (by rfl) ⟨5879202, by rfl⟩ : syracuseStep 15677873 = 11758405) B11758405
theorem B2791883 : Blo 1375507 2791883 := bstep (se 1 (by rfl) ⟨2093912, by rfl⟩ : syracuseStep 2791883 = 4187825) B4187825
theorem B2611673 : Blo 1375507 2611673 := bstep (se 2 (by rfl) ⟨979377, by rfl⟩ : syracuseStep 2611673 = 1958755) B1958755
theorem B5224925 : Blo 1375507 5224925 := bstep (se 3 (by rfl) ⟨979673, by rfl⟩ : syracuseStep 5224925 = 1959347) B1959347
theorem B3095027 : Blo 1375507 3095027 := bstep (se 1 (by rfl) ⟨2321270, by rfl⟩ : syracuseStep 3095027 = 4642541) B4642541
theorem B3095063 : Blo 1375507 3095063 := bstep (se 1 (by rfl) ⟨2321297, by rfl⟩ : syracuseStep 3095063 = 4642595) B4642595
theorem B4643351 : Blo 1375507 4643351 := bstep (se 1 (by rfl) ⟨3482513, by rfl⟩ : syracuseStep 4643351 = 6965027) B6965027
theorem B1743383 : Blo 1375507 1743383 := bstep (se 1 (by rfl) ⟨1307537, by rfl⟩ : syracuseStep 1743383 = 2615075) B2615075
theorem B2980403 : Blo 1375507 2980403 := bstep (se 1 (by rfl) ⟨2235302, by rfl⟩ : syracuseStep 2980403 = 4470605) B4470605
theorem B3095243 : Blo 1375507 3095243 := bstep (se 1 (by rfl) ⟨2321432, by rfl⟩ : syracuseStep 3095243 = 4642865) B4642865
theorem B3095297 : Blo 1375507 3095297 := bstep (se 2 (by rfl) ⟨1160736, by rfl⟩ : syracuseStep 3095297 = 2321473) B2321473
theorem B3873587 : Blo 1375507 3873587 := bstep (se 1 (by rfl) ⟨2905190, by rfl⟩ : syracuseStep 3873587 = 5810381) B5810381
theorem B11754305 : Blo 1375507 11754305 := bstep (se 2 (by rfl) ⟨4407864, by rfl⟩ : syracuseStep 11754305 = 8815729) B8815729
theorem B10591069 : Blo 1375507 10591069 := bstep (se 3 (by rfl) ⟨1985825, by rfl⟩ : syracuseStep 10591069 = 3971651) B3971651
theorem B2612083 : Blo 1375507 2612083 := bstep (se 1 (by rfl) ⟨1959062, by rfl⟩ : syracuseStep 2612083 = 3918125) B3918125
theorem B5880707 : Blo 1375507 5880707 := bstep (se 1 (by rfl) ⟨4410530, by rfl⟩ : syracuseStep 5880707 = 8821061) B8821061
theorem B2063321 : Blo 1375507 2063321 := bstep (se 2 (by rfl) ⟨773745, by rfl⟩ : syracuseStep 2063321 = 1547491) B1547491
theorem B3095513 : Blo 1375507 3095513 := bstep (se 2 (by rfl) ⟨1160817, by rfl⟩ : syracuseStep 3095513 = 2321635) B2321635
theorem B4185053 : Blo 1375507 4185053 := bstep (se 3 (by rfl) ⟨784697, by rfl⟩ : syracuseStep 4185053 = 1569395) B1569395
theorem B10460177 : Blo 1375507 10460177 := bstep (se 2 (by rfl) ⟨3922566, by rfl⟩ : syracuseStep 10460177 = 7845133) B7845133
theorem B3095603 : Blo 1375507 3095603 := bstep (se 1 (by rfl) ⟨2321702, by rfl⟩ : syracuseStep 3095603 = 4643405) B4643405
theorem B4643891 : Blo 1375507 4643891 := bstep (se 1 (by rfl) ⟨3482918, by rfl⟩ : syracuseStep 4643891 = 6965837) B6965837
theorem B2063435 : Blo 1375507 2063435 := bstep (se 1 (by rfl) ⟨1547576, by rfl⟩ : syracuseStep 2063435 = 3095153) B3095153
theorem B2063447 : Blo 1375507 2063447 := bstep (se 1 (by rfl) ⟨1547585, by rfl⟩ : syracuseStep 2063447 = 3095171) B3095171
theorem B3095639 : Blo 1375507 3095639 := bstep (se 1 (by rfl) ⟨2321729, by rfl⟩ : syracuseStep 3095639 = 4643459) B4643459
theorem B2063513 : Blo 1375507 2063513 := bstep (se 2 (by rfl) ⟨773817, by rfl⟩ : syracuseStep 2063513 = 1547635) B1547635
theorem B5881049 : Blo 1375507 5881049 := bstep (se 2 (by rfl) ⟨2205393, by rfl⟩ : syracuseStep 5881049 = 4410787) B4410787
theorem B2063627 : Blo 1375507 2063627 := bstep (se 1 (by rfl) ⟨1547720, by rfl⟩ : syracuseStep 2063627 = 3095441) B3095441
theorem B3095819 : Blo 1375507 3095819 := bstep (se 1 (by rfl) ⟨2321864, by rfl⟩ : syracuseStep 3095819 = 4643729) B4643729
theorem B2235659 : Blo 1375507 2235659 := bstep (se 1 (by rfl) ⟨1676744, by rfl⟩ : syracuseStep 2235659 = 3353489) B3353489
theorem B1375511 : Blo 1375507 1375511 := bstep (se 1 (by rfl) ⟨1031633, by rfl⟩ : syracuseStep 1375511 = 2063267) B2063267
theorem B2063639 : Blo 1375507 2063639 := bstep (se 1 (by rfl) ⟨1547729, by rfl⟩ : syracuseStep 2063639 = 3095459) B3095459
theorem B1375531 : Blo 1375507 1375531 := bstep (se 1 (by rfl) ⟨1031648, by rfl⟩ : syracuseStep 1375531 = 2063297) B2063297
theorem B1547563 : Blo 1375507 1547563 := bstep (se 1 (by rfl) ⟨1160672, by rfl⟩ : syracuseStep 1547563 = 2321345) B2321345
theorem B1375543 : Blo 1375507 1375543 := bstep (se 1 (by rfl) ⟨1031657, by rfl⟩ : syracuseStep 1375543 = 2063315) B2063315
theorem B3095873 : Blo 1375507 3095873 := bstep (se 2 (by rfl) ⟨1160952, by rfl⟩ : syracuseStep 3095873 = 2321905) B2321905
theorem B4644161 : Blo 1375507 4644161 := bstep (se 2 (by rfl) ⟨1741560, by rfl⟩ : syracuseStep 4644161 = 3483121) B3483121
theorem B1375563 : Blo 1375507 1375563 := bstep (se 1 (by rfl) ⟨1031672, by rfl⟩ : syracuseStep 1375563 = 2063345) B2063345
theorem B1375575 : Blo 1375507 1375575 := bstep (se 1 (by rfl) ⟨1031681, by rfl⟩ : syracuseStep 1375575 = 2063363) B2063363
theorem B2063705 : Blo 1375507 2063705 := bstep (se 2 (by rfl) ⟨773889, by rfl⟩ : syracuseStep 2063705 = 1547779) B1547779
theorem B2612569 : Blo 1375507 2612569 := bstep (se 2 (by rfl) ⟨979713, by rfl⟩ : syracuseStep 2612569 = 1959427) B1959427
theorem B1375595 : Blo 1375507 1375595 := bstep (se 1 (by rfl) ⟨1031696, by rfl⟩ : syracuseStep 1375595 = 2063393) B2063393
theorem B1375607 : Blo 1375507 1375607 := bstep (se 1 (by rfl) ⟨1031705, by rfl⟩ : syracuseStep 1375607 = 2063411) B2063411
theorem B1375627 : Blo 1375507 1375627 := bstep (se 1 (by rfl) ⟨1031720, by rfl⟩ : syracuseStep 1375627 = 2063441) B2063441
theorem B1375639 : Blo 1375507 1375639 := bstep (se 1 (by rfl) ⟨1031729, by rfl⟩ : syracuseStep 1375639 = 2063459) B2063459
theorem B1547671 : Blo 1375507 1547671 := bstep (se 1 (by rfl) ⟨1160753, by rfl⟩ : syracuseStep 1547671 = 2321507) B2321507
theorem B1375659 : Blo 1375507 1375659 := bstep (se 1 (by rfl) ⟨1031744, by rfl⟩ : syracuseStep 1375659 = 2063489) B2063489
theorem B10452401 : Blo 1375507 10452401 := bstep (se 2 (by rfl) ⟨3919650, by rfl⟩ : syracuseStep 10452401 = 7839301) B7839301
theorem B1375671 : Blo 1375507 1375671 := bstep (se 1 (by rfl) ⟨1031753, by rfl⟩ : syracuseStep 1375671 = 2063507) B2063507
theorem B1375691 : Blo 1375507 1375691 := bstep (se 1 (by rfl) ⟨1031768, by rfl⟩ : syracuseStep 1375691 = 2063537) B2063537
theorem B2063819 : Blo 1375507 2063819 := bstep (se 1 (by rfl) ⟨1547864, by rfl⟩ : syracuseStep 2063819 = 3095729) B3095729
theorem B1375703 : Blo 1375507 1375703 := bstep (se 1 (by rfl) ⟨1031777, by rfl⟩ : syracuseStep 1375703 = 2063555) B2063555
theorem B2063831 : Blo 1375507 2063831 := bstep (se 1 (by rfl) ⟨1547873, by rfl⟩ : syracuseStep 2063831 = 3095747) B3095747
theorem B1375723 : Blo 1375507 1375723 := bstep (se 1 (by rfl) ⟨1031792, by rfl⟩ : syracuseStep 1375723 = 2063585) B2063585
theorem B1375735 : Blo 1375507 1375735 := bstep (se 1 (by rfl) ⟨1031801, by rfl⟩ : syracuseStep 1375735 = 2063603) B2063603
theorem B1375755 : Blo 1375507 1375755 := bstep (se 1 (by rfl) ⟨1031816, by rfl⟩ : syracuseStep 1375755 = 2063633) B2063633
theorem B26811917 : Blo 1375507 26811917 := bstep (se 3 (by rfl) ⟨5027234, by rfl⟩ : syracuseStep 26811917 = 10054469) B10054469
theorem B1375767 : Blo 1375507 1375767 := bstep (se 1 (by rfl) ⟨1031825, by rfl⟩ : syracuseStep 1375767 = 2063651) B2063651
theorem B2063897 : Blo 1375507 2063897 := bstep (se 2 (by rfl) ⟨773961, by rfl⟩ : syracuseStep 2063897 = 1547923) B1547923
theorem B3096089 : Blo 1375507 3096089 := bstep (se 2 (by rfl) ⟨1161033, by rfl⟩ : syracuseStep 3096089 = 2322067) B2322067
theorem B1375787 : Blo 1375507 1375787 := bstep (se 1 (by rfl) ⟨1031840, by rfl⟩ : syracuseStep 1375787 = 2063681) B2063681
theorem B1375799 : Blo 1375507 1375799 := bstep (se 1 (by rfl) ⟨1031849, by rfl⟩ : syracuseStep 1375799 = 2063699) B2063699
theorem B1375819 : Blo 1375507 1375819 := bstep (se 1 (by rfl) ⟨1031864, by rfl⟩ : syracuseStep 1375819 = 2063729) B2063729
theorem B1547851 : Blo 1375507 1547851 := bstep (se 1 (by rfl) ⟨1160888, by rfl⟩ : syracuseStep 1547851 = 2321777) B2321777
theorem B1375831 : Blo 1375507 1375831 := bstep (se 1 (by rfl) ⟨1031873, by rfl⟩ : syracuseStep 1375831 = 2063747) B2063747
theorem B1375851 : Blo 1375507 1375851 := bstep (se 1 (by rfl) ⟨1031888, by rfl⟩ : syracuseStep 1375851 = 2063777) B2063777
theorem B3096179 : Blo 1375507 3096179 := bstep (se 1 (by rfl) ⟨2322134, by rfl⟩ : syracuseStep 3096179 = 4644269) B4644269
theorem B1375863 : Blo 1375507 1375863 := bstep (se 1 (by rfl) ⟨1031897, by rfl⟩ : syracuseStep 1375863 = 2063795) B2063795
theorem B1375883 : Blo 1375507 1375883 := bstep (se 1 (by rfl) ⟨1031912, by rfl⟩ : syracuseStep 1375883 = 2063825) B2063825
theorem B2064011 : Blo 1375507 2064011 := bstep (se 1 (by rfl) ⟨1548008, by rfl⟩ : syracuseStep 2064011 = 3096017) B3096017
theorem B1375895 : Blo 1375507 1375895 := bstep (se 1 (by rfl) ⟨1031921, by rfl⟩ : syracuseStep 1375895 = 2063843) B2063843
theorem B2064023 : Blo 1375507 2064023 := bstep (se 1 (by rfl) ⟨1548017, by rfl⟩ : syracuseStep 2064023 = 3096035) B3096035
theorem B3096215 : Blo 1375507 3096215 := bstep (se 1 (by rfl) ⟨2322161, by rfl⟩ : syracuseStep 3096215 = 4644323) B4644323
theorem B1375915 : Blo 1375507 1375915 := bstep (se 1 (by rfl) ⟨1031936, by rfl⟩ : syracuseStep 1375915 = 2063873) B2063873
theorem B3718835 : Blo 1375507 3718835 := bstep (se 1 (by rfl) ⟨2789126, by rfl⟩ : syracuseStep 3718835 = 5578253) B5578253
theorem B1375927 : Blo 1375507 1375927 := bstep (se 1 (by rfl) ⟨1031945, by rfl⟩ : syracuseStep 1375927 = 2063891) B2063891
theorem B1547959 : Blo 1375507 1547959 := bstep (se 1 (by rfl) ⟨1160969, by rfl⟩ : syracuseStep 1547959 = 2321939) B2321939
theorem B1375947 : Blo 1375507 1375947 := bstep (se 1 (by rfl) ⟨1031960, by rfl⟩ : syracuseStep 1375947 = 2063921) B2063921
theorem B2940619 : Blo 1375507 2940619 := bstep (se 1 (by rfl) ⟨2205464, by rfl⟩ : syracuseStep 2940619 = 4410929) B4410929
theorem B1375959 : Blo 1375507 1375959 := bstep (se 1 (by rfl) ⟨1031969, by rfl⟩ : syracuseStep 1375959 = 2063939) B2063939
theorem B2064089 : Blo 1375507 2064089 := bstep (se 2 (by rfl) ⟨774033, by rfl⟩ : syracuseStep 2064089 = 1548067) B1548067
theorem B1375979 : Blo 1375507 1375979 := bstep (se 1 (by rfl) ⟨1031984, by rfl⟩ : syracuseStep 1375979 = 2063969) B2063969
theorem B1375991 : Blo 1375507 1375991 := bstep (se 1 (by rfl) ⟨1031993, by rfl⟩ : syracuseStep 1375991 = 2063987) B2063987
theorem B1376011 : Blo 1375507 1376011 := bstep (se 1 (by rfl) ⟨1032008, by rfl⟩ : syracuseStep 1376011 = 2064017) B2064017
theorem B1376023 : Blo 1375507 1376023 := bstep (se 1 (by rfl) ⟨1032017, by rfl⟩ : syracuseStep 1376023 = 2064035) B2064035
theorem B1376043 : Blo 1375507 1376043 := bstep (se 1 (by rfl) ⟨1032032, by rfl⟩ : syracuseStep 1376043 = 2064065) B2064065
theorem B4964141 : Blo 1375507 4964141 := bstep (se 3 (by rfl) ⟨930776, by rfl⟩ : syracuseStep 4964141 = 1861553) B1861553
theorem B1376055 : Blo 1375507 1376055 := bstep (se 1 (by rfl) ⟨1032041, by rfl⟩ : syracuseStep 1376055 = 2064083) B2064083
theorem B1376075 : Blo 1375507 1376075 := bstep (se 1 (by rfl) ⟨1032056, by rfl⟩ : syracuseStep 1376075 = 2064113) B2064113
theorem B2064203 : Blo 1375507 2064203 := bstep (se 1 (by rfl) ⟨1548152, by rfl⟩ : syracuseStep 2064203 = 3096305) B3096305
theorem B3096395 : Blo 1375507 3096395 := bstep (se 1 (by rfl) ⟨2322296, by rfl⟩ : syracuseStep 3096395 = 4644593) B4644593
theorem B1376087 : Blo 1375507 1376087 := bstep (se 1 (by rfl) ⟨1032065, by rfl⟩ : syracuseStep 1376087 = 2064131) B2064131
theorem B2064215 : Blo 1375507 2064215 := bstep (se 1 (by rfl) ⟨1548161, by rfl⟩ : syracuseStep 2064215 = 3096323) B3096323
theorem B4644701 : Blo 1375507 4644701 := bstep (se 3 (by rfl) ⟨870881, by rfl⟩ : syracuseStep 4644701 = 1741763) B1741763
theorem B18825061 : Blo 1375507 18825061 := bstep (se 4 (by rfl) ⟨1764849, by rfl⟩ : syracuseStep 18825061 = 3529699) B3529699
theorem B1376107 : Blo 1375507 1376107 := bstep (se 1 (by rfl) ⟨1032080, by rfl⟩ : syracuseStep 1376107 = 2064161) B2064161
theorem B1548139 : Blo 1375507 1548139 := bstep (se 1 (by rfl) ⟨1161104, by rfl⟩ : syracuseStep 1548139 = 2322209) B2322209
theorem B1376119 : Blo 1375507 1376119 := bstep (se 1 (by rfl) ⟨1032089, by rfl⟩ : syracuseStep 1376119 = 2064179) B2064179
theorem B3096449 : Blo 1375507 3096449 := bstep (se 2 (by rfl) ⟨1161168, by rfl⟩ : syracuseStep 3096449 = 2322337) B2322337
theorem B1376139 : Blo 1375507 1376139 := bstep (se 1 (by rfl) ⟨1032104, by rfl⟩ : syracuseStep 1376139 = 2064209) B2064209
theorem B2613131 : Blo 1375507 2613131 := bstep (se 1 (by rfl) ⟨1959848, by rfl⟩ : syracuseStep 2613131 = 3919697) B3919697
theorem B1376151 : Blo 1375507 1376151 := bstep (se 1 (by rfl) ⟨1032113, by rfl⟩ : syracuseStep 1376151 = 2064227) B2064227
theorem B10452887 : Blo 1375507 10452887 := bstep (se 1 (by rfl) ⟨7839665, by rfl⟩ : syracuseStep 10452887 = 15679331) B15679331
theorem B2064281 : Blo 1375507 2064281 := bstep (se 2 (by rfl) ⟨774105, by rfl⟩ : syracuseStep 2064281 = 1548211) B1548211
theorem B1376171 : Blo 1375507 1376171 := bstep (se 1 (by rfl) ⟨1032128, by rfl⟩ : syracuseStep 1376171 = 2064257) B2064257
theorem B1376183 : Blo 1375507 1376183 := bstep (se 1 (by rfl) ⟨1032137, by rfl⟩ : syracuseStep 1376183 = 2064275) B2064275
theorem B1376203 : Blo 1375507 1376203 := bstep (se 1 (by rfl) ⟨1032152, by rfl⟩ : syracuseStep 1376203 = 2064305) B2064305
theorem B1376215 : Blo 1375507 1376215 := bstep (se 1 (by rfl) ⟨1032161, by rfl⟩ : syracuseStep 1376215 = 2064323) B2064323
theorem B1548247 : Blo 1375507 1548247 := bstep (se 1 (by rfl) ⟨1161185, by rfl⟩ : syracuseStep 1548247 = 2322371) B2322371
theorem B4186073 : Blo 1375507 4186073 := bstep (se 2 (by rfl) ⟨1569777, by rfl⟩ : syracuseStep 4186073 = 3139555) B3139555
theorem B1376235 : Blo 1375507 1376235 := bstep (se 1 (by rfl) ⟨1032176, by rfl⟩ : syracuseStep 1376235 = 2064353) B2064353
theorem B1376247 : Blo 1375507 1376247 := bstep (se 1 (by rfl) ⟨1032185, by rfl⟩ : syracuseStep 1376247 = 2064371) B2064371
theorem B1376263 : Blo 1375507 1376263 := bstep (se 1 (by rfl) ⟨1032197, by rfl⟩ : syracuseStep 1376263 = 2064395) B2064395
theorem B1376271 : Blo 1375507 1376271 := bstep (se 1 (by rfl) ⟨1032203, by rfl⟩ : syracuseStep 1376271 = 2064407) B2064407
theorem B2940961 : Blo 1375507 2940961 := bstep (se 2 (by rfl) ⟨1102860, by rfl⟩ : syracuseStep 2940961 = 2205721) B2205721
theorem B2064443 : Blo 1375507 2064443 := bstep (se 1 (by rfl) ⟨1548332, by rfl⟩ : syracuseStep 2064443 = 3096665) B3096665
theorem B1376315 : Blo 1375507 1376315 := bstep (se 1 (by rfl) ⟨1032236, by rfl⟩ : syracuseStep 1376315 = 2064473) B2064473
theorem B2064503 : Blo 1375507 2064503 := bstep (se 1 (by rfl) ⟨1548377, by rfl⟩ : syracuseStep 2064503 = 3096755) B3096755
theorem B1376391 : Blo 1375507 1376391 := bstep (se 1 (by rfl) ⟨1032293, by rfl⟩ : syracuseStep 1376391 = 2064587) B2064587
theorem B2064527 : Blo 1375507 2064527 := bstep (se 1 (by rfl) ⟨1548395, by rfl⟩ : syracuseStep 2064527 = 3096791) B3096791
theorem B1376399 : Blo 1375507 1376399 := bstep (se 1 (by rfl) ⟨1032299, by rfl⟩ : syracuseStep 1376399 = 2064599) B2064599
theorem B3719353 : Blo 1375507 3719353 := bstep (se 2 (by rfl) ⟨1394757, by rfl⟩ : syracuseStep 3719353 = 2789515) B2789515
theorem B2064569 : Blo 1375507 2064569 := bstep (se 2 (by rfl) ⟨774213, by rfl⟩ : syracuseStep 2064569 = 1548427) B1548427
theorem B1376443 : Blo 1375507 1376443 := bstep (se 1 (by rfl) ⟨1032332, by rfl⟩ : syracuseStep 1376443 = 2064665) B2064665
theorem B2064647 : Blo 1375507 2064647 := bstep (se 1 (by rfl) ⟨1548485, by rfl⟩ : syracuseStep 2064647 = 3096971) B3096971
theorem B1376519 : Blo 1375507 1376519 := bstep (se 1 (by rfl) ⟨1032389, by rfl⟩ : syracuseStep 1376519 = 2064779) B2064779
theorem B1376527 : Blo 1375507 1376527 := bstep (se 1 (by rfl) ⟨1032395, by rfl⟩ : syracuseStep 1376527 = 2064791) B2064791
theorem B2064683 : Blo 1375507 2064683 := bstep (se 1 (by rfl) ⟨1548512, by rfl⟩ : syracuseStep 2064683 = 3097025) B3097025
theorem B1376571 : Blo 1375507 1376571 := bstep (se 1 (by rfl) ⟨1032428, by rfl⟩ : syracuseStep 1376571 = 2064857) B2064857
theorem B2064713 : Blo 1375507 2064713 := bstep (se 2 (by rfl) ⟨774267, by rfl⟩ : syracuseStep 2064713 = 1548535) B1548535
theorem B1548679 : Blo 1375507 1548679 := bstep (se 1 (by rfl) ⟨1161509, by rfl⟩ : syracuseStep 1548679 = 2323019) B2323019
theorem B1376647 : Blo 1375507 1376647 := bstep (se 1 (by rfl) ⟨1032485, by rfl⟩ : syracuseStep 1376647 = 2064971) B2064971
theorem B1376655 : Blo 1375507 1376655 := bstep (se 1 (by rfl) ⟨1032491, by rfl⟩ : syracuseStep 1376655 = 2064983) B2064983
theorem B11764115 : Blo 1375507 11764115 := bstep (se 1 (by rfl) ⟨8823086, by rfl⟩ : syracuseStep 11764115 = 17646173) B17646173
theorem B2064827 : Blo 1375507 2064827 := bstep (se 1 (by rfl) ⟨1548620, by rfl⟩ : syracuseStep 2064827 = 3097241) B3097241
theorem B1376699 : Blo 1375507 1376699 := bstep (se 1 (by rfl) ⟨1032524, by rfl⟩ : syracuseStep 1376699 = 2065049) B2065049
theorem B2064887 : Blo 1375507 2064887 := bstep (se 1 (by rfl) ⟨1548665, by rfl⟩ : syracuseStep 2064887 = 3097331) B3097331
theorem B7840259 : Blo 1375507 7840259 := bstep (se 1 (by rfl) ⟨5880194, by rfl⟩ : syracuseStep 7840259 = 11760389) B11760389
theorem B1376775 : Blo 1375507 1376775 := bstep (se 1 (by rfl) ⟨1032581, by rfl⟩ : syracuseStep 1376775 = 2065163) B2065163
theorem B2122247 : Blo 1375507 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B2064911 : Blo 1375507 2064911 := bstep (se 1 (by rfl) ⟨1548683, by rfl⟩ : syracuseStep 2064911 = 3097367) B3097367
theorem B1376783 : Blo 1375507 1376783 := bstep (se 1 (by rfl) ⟨1032587, by rfl⟩ : syracuseStep 1376783 = 2065175) B2065175
theorem B5227037 : Blo 1375507 5227037 := bstep (se 3 (by rfl) ⟨980069, by rfl⟩ : syracuseStep 5227037 = 1960139) B1960139
theorem B5227051 : Blo 1375507 5227051 := bstep (se 1 (by rfl) ⟨3920288, by rfl⟩ : syracuseStep 5227051 = 7840577) B7840577
theorem B2064953 : Blo 1375507 2064953 := bstep (se 2 (by rfl) ⟨774357, by rfl⟩ : syracuseStep 2064953 = 1548715) B1548715
theorem B1548859 : Blo 1375507 1548859 := bstep (se 1 (by rfl) ⟨1161644, by rfl⟩ : syracuseStep 1548859 = 2323289) B2323289
theorem B1376827 : Blo 1375507 1376827 := bstep (se 1 (by rfl) ⟨1032620, by rfl⟩ : syracuseStep 1376827 = 2065241) B2065241
theorem B1860169 : Blo 1375507 1860169 := bstep (se 2 (by rfl) ⟨697563, by rfl⟩ : syracuseStep 1860169 = 1395127) B1395127
theorem B3097223 : Blo 1375507 3097223 := bstep (se 1 (by rfl) ⟨2322917, by rfl⟩ : syracuseStep 3097223 = 4645835) B4645835
theorem B2065031 : Blo 1375507 2065031 := bstep (se 1 (by rfl) ⟨1548773, by rfl⟩ : syracuseStep 2065031 = 3097547) B3097547
theorem B1376903 : Blo 1375507 1376903 := bstep (se 1 (by rfl) ⟨1032677, by rfl⟩ : syracuseStep 1376903 = 2065355) B2065355
theorem B1376911 : Blo 1375507 1376911 := bstep (se 1 (by rfl) ⟨1032683, by rfl⟩ : syracuseStep 1376911 = 2065367) B2065367
theorem B2065067 : Blo 1375507 2065067 := bstep (se 1 (by rfl) ⟨1548800, by rfl⟩ : syracuseStep 2065067 = 3097601) B3097601
theorem B1376955 : Blo 1375507 1376955 := bstep (se 1 (by rfl) ⟨1032716, by rfl⟩ : syracuseStep 1376955 = 2065433) B2065433
theorem B2065097 : Blo 1375507 2065097 := bstep (se 2 (by rfl) ⟨774411, by rfl⟩ : syracuseStep 2065097 = 1548823) B1548823
theorem B23847641 : Blo 1375507 23847641 := bstep (se 2 (by rfl) ⟨8942865, by rfl⟩ : syracuseStep 23847641 = 17885731) B17885731
theorem B1377031 : Blo 1375507 1377031 := bstep (se 1 (by rfl) ⟨1032773, by rfl⟩ : syracuseStep 1377031 = 2065547) B2065547
theorem B1377039 : Blo 1375507 1377039 := bstep (se 1 (by rfl) ⟨1032779, by rfl⟩ : syracuseStep 1377039 = 2065559) B2065559
theorem B8938291 : Blo 1375507 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B3097403 : Blo 1375507 3097403 := bstep (se 1 (by rfl) ⟨2323052, by rfl⟩ : syracuseStep 3097403 = 4646105) B4646105
theorem B2065211 : Blo 1375507 2065211 := bstep (se 1 (by rfl) ⟨1548908, by rfl⟩ : syracuseStep 2065211 = 3097817) B3097817
theorem B1377083 : Blo 1375507 1377083 := bstep (se 1 (by rfl) ⟨1032812, by rfl⟩ : syracuseStep 1377083 = 2065625) B2065625
theorem B2065271 : Blo 1375507 2065271 := bstep (se 1 (by rfl) ⟨1548953, by rfl⟩ : syracuseStep 2065271 = 3097907) B3097907
theorem B1377159 : Blo 1375507 1377159 := bstep (se 1 (by rfl) ⟨1032869, by rfl⟩ : syracuseStep 1377159 = 2065739) B2065739
theorem B2065295 : Blo 1375507 2065295 := bstep (se 1 (by rfl) ⟨1548971, by rfl⟩ : syracuseStep 2065295 = 3097943) B3097943
theorem B1377167 : Blo 1375507 1377167 := bstep (se 1 (by rfl) ⟨1032875, by rfl⟩ : syracuseStep 1377167 = 2065751) B2065751
theorem B3097529 : Blo 1375507 3097529 := bstep (se 2 (by rfl) ⟨1161573, by rfl⟩ : syracuseStep 3097529 = 2323147) B2323147
theorem B2065337 : Blo 1375507 2065337 := bstep (se 2 (by rfl) ⟨774501, by rfl⟩ : syracuseStep 2065337 = 1549003) B1549003
theorem B1377211 : Blo 1375507 1377211 := bstep (se 1 (by rfl) ⟨1032908, by rfl⟩ : syracuseStep 1377211 = 2065817) B2065817
theorem B2065415 : Blo 1375507 2065415 := bstep (se 1 (by rfl) ⟨1549061, by rfl⟩ : syracuseStep 2065415 = 3098123) B3098123
theorem B1377287 : Blo 1375507 1377287 := bstep (se 1 (by rfl) ⟨1032965, by rfl⟩ : syracuseStep 1377287 = 2065931) B2065931
theorem B3482635 : Blo 1375507 3482635 := bstep (se 1 (by rfl) ⟨2611976, by rfl⟩ : syracuseStep 3482635 = 5223953) B5223953
theorem B1549327 : Blo 1375507 1549327 := bstep (se 1 (by rfl) ⟨1161995, by rfl⟩ : syracuseStep 1549327 = 2323991) B2323991
theorem B1377295 : Blo 1375507 1377295 := bstep (se 1 (by rfl) ⟨1032971, by rfl⟩ : syracuseStep 1377295 = 2065943) B2065943
theorem B2065451 : Blo 1375507 2065451 := bstep (se 1 (by rfl) ⟨1549088, by rfl⟩ : syracuseStep 2065451 = 3098177) B3098177
theorem B2614331 : Blo 1375507 2614331 := bstep (se 1 (by rfl) ⟨1960748, by rfl⟩ : syracuseStep 2614331 = 3921497) B3921497
theorem B1377339 : Blo 1375507 1377339 := bstep (se 1 (by rfl) ⟨1033004, by rfl⟩ : syracuseStep 1377339 = 2066009) B2066009
theorem B2065481 : Blo 1375507 2065481 := bstep (se 2 (by rfl) ⟨774555, by rfl⟩ : syracuseStep 2065481 = 1549111) B1549111
theorem B3138679 : Blo 1375507 3138679 := bstep (se 1 (by rfl) ⟨2354009, by rfl⟩ : syracuseStep 3138679 = 4708019) B4708019
theorem B1377415 : Blo 1375507 1377415 := bstep (se 1 (by rfl) ⟨1033061, by rfl⟩ : syracuseStep 1377415 = 2066123) B2066123
theorem B1377423 : Blo 1375507 1377423 := bstep (se 1 (by rfl) ⟨1033067, by rfl⟩ : syracuseStep 1377423 = 2066135) B2066135
theorem B3482777 : Blo 1375507 3482777 := bstep (se 2 (by rfl) ⟨1306041, by rfl⟩ : syracuseStep 3482777 = 2612083) B2612083
theorem B2065595 : Blo 1375507 2065595 := bstep (se 1 (by rfl) ⟨1549196, by rfl⟩ : syracuseStep 2065595 = 3098393) B3098393
theorem B1377467 : Blo 1375507 1377467 := bstep (se 1 (by rfl) ⟨1033100, by rfl⟩ : syracuseStep 1377467 = 2066201) B2066201
theorem B2065655 : Blo 1375507 2065655 := bstep (se 1 (by rfl) ⟨1549241, by rfl⟩ : syracuseStep 2065655 = 3098483) B3098483
theorem B4646159 : Blo 1375507 4646159 := bstep (se 1 (by rfl) ⟨3484619, by rfl⟩ : syracuseStep 4646159 = 6969239) B6969239
theorem B3097871 : Blo 1375507 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B2065679 : Blo 1375507 2065679 := bstep (se 1 (by rfl) ⟨1549259, by rfl⟩ : syracuseStep 2065679 = 3098519) B3098519
theorem B5883151 : Blo 1375507 5883151 := bstep (se 1 (by rfl) ⟨4412363, by rfl⟩ : syracuseStep 5883151 = 8824727) B8824727
theorem B3097889 : Blo 1375507 3097889 := bstep (se 2 (by rfl) ⟨1161708, by rfl⟩ : syracuseStep 3097889 = 2323417) B2323417
theorem B3917099 : Blo 1375507 3917099 := bstep (se 1 (by rfl) ⟨2937824, by rfl⟩ : syracuseStep 3917099 = 5875649) B5875649
theorem B2065721 : Blo 1375507 2065721 := bstep (se 2 (by rfl) ⟨774645, by rfl⟩ : syracuseStep 2065721 = 1549291) B1549291
theorem B3482939 : Blo 1375507 3482939 := bstep (se 1 (by rfl) ⟨2612204, by rfl⟩ : syracuseStep 3482939 = 5224409) B5224409
theorem B9921851 : Blo 1375507 9921851 := bstep (se 1 (by rfl) ⟨7441388, by rfl⟩ : syracuseStep 9921851 = 14882777) B14882777
theorem B2065799 : Blo 1375507 2065799 := bstep (se 1 (by rfl) ⟨1549349, by rfl⟩ : syracuseStep 2065799 = 3098699) B3098699
theorem B2065835 : Blo 1375507 2065835 := bstep (se 1 (by rfl) ⟨1549376, by rfl⟩ : syracuseStep 2065835 = 3098753) B3098753
theorem B42362297 : Blo 1375507 42362297 := bstep (se 2 (by rfl) ⟨15885861, by rfl⟩ : syracuseStep 42362297 = 31771723) B31771723
theorem B2065865 : Blo 1375507 2065865 := bstep (se 2 (by rfl) ⟨774699, by rfl⟩ : syracuseStep 2065865 = 1549399) B1549399
theorem B4646429 : Blo 1375507 4646429 := bstep (se 3 (by rfl) ⟨871205, by rfl⟩ : syracuseStep 4646429 = 1742411) B1742411
theorem B3720737 : Blo 1375507 3720737 := bstep (se 2 (by rfl) ⟨1395276, by rfl⟩ : syracuseStep 3720737 = 2790553) B2790553
theorem B2614817 : Blo 1375507 2614817 := bstep (se 2 (by rfl) ⟨980556, by rfl⟩ : syracuseStep 2614817 = 1961113) B1961113
theorem B2065979 : Blo 1375507 2065979 := bstep (se 1 (by rfl) ⟨1549484, by rfl⟩ : syracuseStep 2065979 = 3098969) B3098969
theorem B3098231 : Blo 1375507 3098231 := bstep (se 1 (by rfl) ⟨2323673, by rfl⟩ : syracuseStep 3098231 = 4647347) B4647347
theorem B2066039 : Blo 1375507 2066039 := bstep (se 1 (by rfl) ⟨1549529, by rfl⟩ : syracuseStep 2066039 = 3099059) B3099059
theorem B1861255 : Blo 1375507 1861255 := bstep (se 1 (by rfl) ⟨1395941, by rfl⟩ : syracuseStep 1861255 = 2791883) B2791883
theorem B2066063 : Blo 1375507 2066063 := bstep (se 1 (by rfl) ⟨1549547, by rfl⟩ : syracuseStep 2066063 = 3099095) B3099095
theorem B3483283 : Blo 1375507 3483283 := bstep (se 1 (by rfl) ⟨2612462, by rfl⟩ : syracuseStep 3483283 = 5224925) B5224925
theorem B2066105 : Blo 1375507 2066105 := bstep (se 2 (by rfl) ⟨774789, by rfl⟩ : syracuseStep 2066105 = 1549579) B1549579
theorem B2066183 : Blo 1375507 2066183 := bstep (se 1 (by rfl) ⟨1549637, by rfl⟩ : syracuseStep 2066183 = 3099275) B3099275
theorem B3483425 : Blo 1375507 3483425 := bstep (se 2 (by rfl) ⟨1306284, by rfl⟩ : syracuseStep 3483425 = 2612569) B2612569
theorem B3098411 : Blo 1375507 3098411 := bstep (se 1 (by rfl) ⟨2323808, by rfl⟩ : syracuseStep 3098411 = 4647617) B4647617
theorem B2066219 : Blo 1375507 2066219 := bstep (se 1 (by rfl) ⟨1549664, by rfl⟩ : syracuseStep 2066219 = 3099329) B3099329
theorem B4409147 : Blo 1375507 4409147 := bstep (se 1 (by rfl) ⟨3306860, by rfl⟩ : syracuseStep 4409147 = 6613721) B6613721
theorem B2066249 : Blo 1375507 2066249 := bstep (se 2 (by rfl) ⟨774843, by rfl⟩ : syracuseStep 2066249 = 1549687) B1549687
theorem B1886123 : Blo 1375507 1886123 := bstep (se 1 (by rfl) ⟨1414592, by rfl⟩ : syracuseStep 1886123 = 2829185) B2829185
theorem B7440349 : Blo 1375507 7440349 := bstep (se 3 (by rfl) ⟨1395065, by rfl⟩ : syracuseStep 7440349 = 2790131) B2790131
theorem B6973451 : Blo 1375507 6973451 := bstep (se 1 (by rfl) ⟨5230088, by rfl⟩ : syracuseStep 6973451 = 10460177) B10460177
theorem B3098771 : Blo 1375507 3098771 := bstep (se 1 (by rfl) ⟨2324078, by rfl⟩ : syracuseStep 3098771 = 4648157) B4648157
theorem B6973613 : Blo 1375507 6973613 := bstep (se 3 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 6973613 = 2615105) B2615105
theorem B3098825 : Blo 1375507 3098825 := bstep (se 2 (by rfl) ⟨1162059, by rfl⟩ : syracuseStep 3098825 = 2324119) B2324119
theorem B3918091 : Blo 1375507 3918091 := bstep (se 1 (by rfl) ⟨2938568, by rfl⟩ : syracuseStep 3918091 = 5877137) B5877137
theorem B3918365 : Blo 1375507 3918365 := bstep (se 3 (by rfl) ⟨734693, by rfl⟩ : syracuseStep 3918365 = 1469387) B1469387
theorem B2091577 : Blo 1375507 2091577 := bstep (se 2 (by rfl) ⟨784341, by rfl⟩ : syracuseStep 2091577 = 1568683) B1568683
theorem B9423479 : Blo 1375507 9423479 := bstep (se 1 (by rfl) ⟨7067609, by rfl⟩ : syracuseStep 9423479 = 14135219) B14135219
theorem B3484417 : Blo 1375507 3484417 := bstep (se 2 (by rfl) ⟨1306656, by rfl⟩ : syracuseStep 3484417 = 2613313) B2613313
theorem B5655329 : Blo 1375507 5655329 := bstep (se 2 (by rfl) ⟨2120748, by rfl⟩ : syracuseStep 5655329 = 4241497) B4241497
theorem B7834427 : Blo 1375507 7834427 := bstep (se 1 (by rfl) ⟨5875820, by rfl⟩ : syracuseStep 7834427 = 11751641) B11751641
theorem B1960777 : Blo 1375507 1960777 := bstep (se 2 (by rfl) ⟨735291, by rfl⟩ : syracuseStep 1960777 = 1470583) B1470583
theorem B6966161 : Blo 1375507 6966161 := bstep (se 2 (by rfl) ⟨2612310, by rfl⟩ : syracuseStep 6966161 = 5224621) B5224621
theorem B4647833 : Blo 1375507 4647833 := bstep (se 2 (by rfl) ⟨1742937, by rfl⟩ : syracuseStep 4647833 = 3485875) B3485875
theorem B11758679 : Blo 1375507 11758679 := bstep (se 1 (by rfl) ⟨8819009, by rfl⟩ : syracuseStep 11758679 = 17638019) B17638019
theorem B2321527 : Blo 1375507 2321527 := bstep (se 1 (by rfl) ⟨1741145, by rfl⟩ : syracuseStep 2321527 = 3482291) B3482291
theorem B2321723 : Blo 1375507 2321723 := bstep (se 1 (by rfl) ⟨1741292, by rfl⟩ : syracuseStep 2321723 = 3482585) B3482585
theorem B3485015 : Blo 1375507 3485015 := bstep (se 1 (by rfl) ⟨2613761, by rfl⟩ : syracuseStep 3485015 = 5227523) B5227523
theorem B1469831 : Blo 1375507 1469831 := bstep (se 1 (by rfl) ⟨1102373, by rfl⟩ : syracuseStep 1469831 = 2204747) B2204747
theorem B24178105 : Blo 1375507 24178105 := bstep (se 2 (by rfl) ⟨9066789, by rfl⟩ : syracuseStep 24178105 = 18133579) B18133579
theorem B3485227 : Blo 1375507 3485227 := bstep (se 1 (by rfl) ⟨2613920, by rfl⟩ : syracuseStep 3485227 = 5227841) B5227841
theorem B15674957 : Blo 1375507 15674957 := bstep (se 3 (by rfl) ⟨2939054, by rfl⟩ : syracuseStep 15674957 = 5878109) B5878109
theorem B4648535 : Blo 1375507 4648535 := bstep (se 1 (by rfl) ⟨3486401, by rfl⟩ : syracuseStep 4648535 = 6972803) B6972803
theorem B3485369 : Blo 1375507 3485369 := bstep (se 2 (by rfl) ⟨1307013, by rfl⟩ : syracuseStep 3485369 = 2614027) B2614027
theorem B2322121 : Blo 1375507 2322121 := bstep (se 2 (by rfl) ⟨870795, by rfl⟩ : syracuseStep 2322121 = 1741591) B1741591
theorem B8376331 : Blo 1375507 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B2650171 : Blo 1375507 2650171 := bstep (se 1 (by rfl) ⟨1987628, by rfl⟩ : syracuseStep 2650171 = 3975257) B3975257
theorem B4649021 : Blo 1375507 4649021 := bstep (se 3 (by rfl) ⟨871691, by rfl⟩ : syracuseStep 4649021 = 1743383) B1743383
theorem B1740943 : Blo 1375507 1740943 := bstep (se 1 (by rfl) ⟨1305707, by rfl⟩ : syracuseStep 1740943 = 2611415) B2611415
theorem B10457261 : Blo 1375507 10457261 := bstep (se 3 (by rfl) ⟨1960736, by rfl⟩ : syracuseStep 10457261 = 3921473) B3921473
theorem B7835885 : Blo 1375507 7835885 := bstep (se 3 (by rfl) ⟨1469228, by rfl⟩ : syracuseStep 7835885 = 2938457) B2938457
theorem B4960493 : Blo 1375507 4960493 := bstep (se 3 (by rfl) ⟨930092, by rfl⟩ : syracuseStep 4960493 = 1860185) B1860185
theorem B214479089 : Blo 1375507 214479089 := bstep (se 2 (by rfl) ⟨80429658, by rfl⟩ : syracuseStep 214479089 = 160859317) B160859317
theorem B1741115 : Blo 1375507 1741115 := bstep (se 1 (by rfl) ⟨1305836, by rfl⟩ : syracuseStep 1741115 = 2611673) B2611673
theorem B1986935 : Blo 1375507 1986935 := bstep (se 1 (by rfl) ⟨1490201, by rfl⟩ : syracuseStep 1986935 = 2980403) B2980403
theorem B2322823 : Blo 1375507 2322823 := bstep (se 1 (by rfl) ⟨1742117, by rfl⟩ : syracuseStep 2322823 = 3484235) B3484235
theorem B7836203 : Blo 1375507 7836203 := bstep (se 1 (by rfl) ⟨5877152, by rfl⟩ : syracuseStep 7836203 = 11754305) B11754305
theorem B10449485 : Blo 1375507 10449485 := bstep (se 3 (by rfl) ⟨1959278, by rfl⟩ : syracuseStep 10449485 = 3918557) B3918557
theorem B3920471 : Blo 1375507 3920471 := bstep (se 1 (by rfl) ⟨2940353, by rfl⟩ : syracuseStep 3920471 = 5880707) B5880707
theorem B2790035 : Blo 1375507 2790035 := bstep (se 1 (by rfl) ⟨2092526, by rfl⟩ : syracuseStep 2790035 = 4185053) B4185053
theorem B3486361 : Blo 1375507 3486361 := bstep (se 2 (by rfl) ⟨1307385, by rfl⟩ : syracuseStep 3486361 = 2614771) B2614771
theorem B5223149 : Blo 1375507 5223149 := bstep (se 3 (by rfl) ⟨979340, by rfl⟩ : syracuseStep 5223149 = 1958681) B1958681
theorem B5296877 : Blo 1375507 5296877 := bstep (se 3 (by rfl) ⟨993164, by rfl⟩ : syracuseStep 5296877 = 1986329) B1986329
theorem B3920699 : Blo 1375507 3920699 := bstep (se 1 (by rfl) ⟨2940524, by rfl⟩ : syracuseStep 3920699 = 5881049) B5881049
theorem B3486523 : Blo 1375507 3486523 := bstep (se 1 (by rfl) ⟨2614892, by rfl⟩ : syracuseStep 3486523 = 5229785) B5229785
theorem B3920825 : Blo 1375507 3920825 := bstep (se 2 (by rfl) ⟨1470309, by rfl⟩ : syracuseStep 3920825 = 2940619) B2940619
theorem B3486665 : Blo 1375507 3486665 := bstep (se 2 (by rfl) ⟨1307499, by rfl⟩ : syracuseStep 3486665 = 2614999) B2614999
theorem B6968267 : Blo 1375507 6968267 := bstep (se 1 (by rfl) ⟨5226200, by rfl⟩ : syracuseStep 6968267 = 10452401) B10452401
theorem B2323471 : Blo 1375507 2323471 := bstep (se 1 (by rfl) ⟨1742603, by rfl⟩ : syracuseStep 2323471 = 3485207) B3485207
theorem B5223467 : Blo 1375507 5223467 := bstep (se 1 (by rfl) ⟨3917600, by rfl⟩ : syracuseStep 5223467 = 7835201) B7835201
theorem B7844951 : Blo 1375507 7844951 := bstep (se 1 (by rfl) ⟨5883713, by rfl⟩ : syracuseStep 7844951 = 11767427) B11767427
theorem B2479223 : Blo 1375507 2479223 := bstep (se 1 (by rfl) ⟨1859417, by rfl⟩ : syracuseStep 2479223 = 3718835) B3718835
theorem B2094265 : Blo 1375507 2094265 := bstep (se 2 (by rfl) ⟨785349, by rfl⟩ : syracuseStep 2094265 = 1570699) B1570699
theorem B1742087 : Blo 1375507 1742087 := bstep (se 1 (by rfl) ⟨1306565, by rfl⟩ : syracuseStep 1742087 = 2613131) B2613131
theorem B6968591 : Blo 1375507 6968591 := bstep (se 1 (by rfl) ⟨5226443, by rfl⟩ : syracuseStep 6968591 = 10452887) B10452887
theorem B2790715 : Blo 1375507 2790715 := bstep (se 1 (by rfl) ⟨2093036, by rfl⟩ : syracuseStep 2790715 = 4186073) B4186073
theorem B3306899 : Blo 1375507 3306899 := bstep (se 1 (by rfl) ⟨2480174, by rfl⟩ : syracuseStep 3306899 = 4960349) B4960349
theorem B28652977 : Blo 1375507 28652977 := bstep (se 2 (by rfl) ⟨10744866, by rfl⟩ : syracuseStep 28652977 = 21489733) B21489733
theorem B6280715 : Blo 1375507 6280715 := bstep (se 1 (by rfl) ⟨4710536, by rfl⟩ : syracuseStep 6280715 = 9421073) B9421073
theorem B15685163 : Blo 1375507 15685163 := bstep (se 1 (by rfl) ⟨11763872, by rfl⟩ : syracuseStep 15685163 = 23527745) B23527745
theorem B2324011 : Blo 1375507 2324011 := bstep (se 1 (by rfl) ⟨1743008, by rfl⟩ : syracuseStep 2324011 = 3486017) B3486017
theorem B1914427 : Blo 1375507 1914427 := bstep (se 1 (by rfl) ⟨1435820, by rfl⟩ : syracuseStep 1914427 = 2871641) B2871641
theorem B15283831 : Blo 1375507 15283831 := bstep (se 1 (by rfl) ⟨11462873, by rfl⟩ : syracuseStep 15283831 = 22925747) B22925747
theorem B2324153 : Blo 1375507 2324153 := bstep (se 2 (by rfl) ⟨871557, by rfl⟩ : syracuseStep 2324153 = 1743115) B1743115
theorem B41318261 : Blo 1375507 41318261 := bstep (se 5 (by rfl) ⟨1936793, by rfl⟩ : syracuseStep 41318261 = 3873587) B3873587
theorem B1742735 : Blo 1375507 1742735 := bstep (se 1 (by rfl) ⟨1307051, by rfl⟩ : syracuseStep 1742735 = 2614103) B2614103
theorem B7436177 : Blo 1375507 7436177 := bstep (se 2 (by rfl) ⟨2788566, by rfl⟩ : syracuseStep 7436177 = 5577133) B5577133
theorem B7837661 : Blo 1375507 7837661 := bstep (se 3 (by rfl) ⟨1469561, by rfl⟩ : syracuseStep 7837661 = 2939123) B2939123
theorem B13228055 : Blo 1375507 13228055 := bstep (se 1 (by rfl) ⟨9921041, by rfl⟩ : syracuseStep 13228055 = 19842083) B19842083
theorem B5961757 : Blo 1375507 5961757 := bstep (se 3 (by rfl) ⟨1117829, by rfl⟩ : syracuseStep 5961757 = 2235659) B2235659
theorem B22337653 : Blo 1375507 22337653 := bstep (se 5 (by rfl) ⟨1047077, by rfl⟩ : syracuseStep 22337653 = 2094155) B2094155
theorem B2513015 : Blo 1375507 2513015 := bstep (se 1 (by rfl) ⟨1884761, by rfl⟩ : syracuseStep 2513015 = 3769523) B3769523
theorem B3094919 : Blo 1375507 3094919 := bstep (se 1 (by rfl) ⟨2321189, by rfl⟩ : syracuseStep 3094919 = 4642379) B4642379
theorem B2939321 : Blo 1375507 2939321 := bstep (se 2 (by rfl) ⟨1102245, by rfl⟩ : syracuseStep 2939321 = 2204491) B2204491
theorem B14121425 : Blo 1375507 14121425 := bstep (se 2 (by rfl) ⟨5295534, by rfl⟩ : syracuseStep 14121425 = 10591069) B10591069
theorem B8370641 : Blo 1375507 8370641 := bstep (se 2 (by rfl) ⟨3138990, by rfl⟩ : syracuseStep 8370641 = 6277981) B6277981
theorem B4962827 : Blo 1375507 4962827 := bstep (se 1 (by rfl) ⟨3722120, by rfl⟩ : syracuseStep 4962827 = 7444241) B7444241
theorem B3922465 : Blo 1375507 3922465 := bstep (se 2 (by rfl) ⟨1470924, by rfl⟩ : syracuseStep 3922465 = 2941849) B2941849
theorem B10459691 : Blo 1375507 10459691 := bstep (se 1 (by rfl) ⟨7844768, by rfl⟩ : syracuseStep 10459691 = 15689537) B15689537
theorem B3095099 : Blo 1375507 3095099 := bstep (se 1 (by rfl) ⟨2321324, by rfl⟩ : syracuseStep 3095099 = 4642649) B4642649
theorem B28269121 : Blo 1375507 28269121 := bstep (se 2 (by rfl) ⟨10600920, by rfl⟩ : syracuseStep 28269121 = 21201841) B21201841
theorem B3095225 : Blo 1375507 3095225 := bstep (se 2 (by rfl) ⟨1160709, by rfl⟩ : syracuseStep 3095225 = 2321419) B2321419
theorem B6970049 : Blo 1375507 6970049 := bstep (se 2 (by rfl) ⟨2613768, by rfl⟩ : syracuseStep 6970049 = 5227537) B5227537
theorem B2480939 : Blo 1375507 2480939 := bstep (se 1 (by rfl) ⟨1860704, by rfl⟩ : syracuseStep 2480939 = 3721409) B3721409
theorem B3529619 : Blo 1375507 3529619 := bstep (se 1 (by rfl) ⟨2647214, by rfl⟩ : syracuseStep 3529619 = 5294429) B5294429
theorem B2063291 : Blo 1375507 2063291 := bstep (se 1 (by rfl) ⟨1547468, by rfl⟩ : syracuseStep 2063291 = 3094937) B3094937
theorem B10451915 : Blo 1375507 10451915 := bstep (se 1 (by rfl) ⟨7838936, by rfl⟩ : syracuseStep 10451915 = 15677873) B15677873
theorem B2063351 : Blo 1375507 2063351 := bstep (se 1 (by rfl) ⟨1547513, by rfl⟩ : syracuseStep 2063351 = 3095027) B3095027
theorem B2063375 : Blo 1375507 2063375 := bstep (se 1 (by rfl) ⟨1547531, by rfl⟩ : syracuseStep 2063375 = 3095063) B3095063
theorem B3095567 : Blo 1375507 3095567 := bstep (se 1 (by rfl) ⟨2321675, by rfl⟩ : syracuseStep 3095567 = 4643351) B4643351
theorem B5299229 : Blo 1375507 5299229 := bstep (se 3 (by rfl) ⟨993605, by rfl⟩ : syracuseStep 5299229 = 1987211) B1987211
theorem B3095585 : Blo 1375507 3095585 := bstep (se 2 (by rfl) ⟨1160844, by rfl⟩ : syracuseStep 3095585 = 2321689) B2321689
theorem B2063417 : Blo 1375507 2063417 := bstep (se 2 (by rfl) ⟨773781, by rfl⟩ : syracuseStep 2063417 = 1547563) B1547563
theorem B2063495 : Blo 1375507 2063495 := bstep (se 1 (by rfl) ⟨1547621, by rfl⟩ : syracuseStep 2063495 = 3095243) B3095243
theorem B2063531 : Blo 1375507 2063531 := bstep (se 1 (by rfl) ⟨1547648, by rfl⟩ : syracuseStep 2063531 = 3095297) B3095297
theorem B2063561 : Blo 1375507 2063561 := bstep (se 2 (by rfl) ⟨773835, by rfl⟩ : syracuseStep 2063561 = 1547671) B1547671
theorem B5577929 : Blo 1375507 5577929 := bstep (se 2 (by rfl) ⟨2091723, by rfl⟩ : syracuseStep 5577929 = 4183447) B4183447
theorem B2612425 : Blo 1375507 2612425 := bstep (se 2 (by rfl) ⟨979659, by rfl⟩ : syracuseStep 2612425 = 1959319) B1959319
theorem B1547527 : Blo 1375507 1547527 := bstep (se 1 (by rfl) ⟨1160645, by rfl⟩ : syracuseStep 1547527 = 2321291) B2321291
theorem B1375547 : Blo 1375507 1375547 := bstep (se 1 (by rfl) ⟨1031660, by rfl⟩ : syracuseStep 1375547 = 2063321) B2063321
theorem B2063675 : Blo 1375507 2063675 := bstep (se 1 (by rfl) ⟨1547756, by rfl⟩ : syracuseStep 2063675 = 3095513) B3095513
theorem B13229405 : Blo 1375507 13229405 := bstep (se 3 (by rfl) ⟨2480513, by rfl⟩ : syracuseStep 13229405 = 4961027) B4961027
theorem B2063735 : Blo 1375507 2063735 := bstep (se 1 (by rfl) ⟨1547801, by rfl⟩ : syracuseStep 2063735 = 3095603) B3095603
theorem B3095927 : Blo 1375507 3095927 := bstep (se 1 (by rfl) ⟨2321945, by rfl⟩ : syracuseStep 3095927 = 4643891) B4643891
theorem B1375623 : Blo 1375507 1375623 := bstep (se 1 (by rfl) ⟨1031717, by rfl⟩ : syracuseStep 1375623 = 2063435) B2063435
theorem B1375631 : Blo 1375507 1375631 := bstep (se 1 (by rfl) ⟨1031723, by rfl⟩ : syracuseStep 1375631 = 2063447) B2063447
theorem B2063759 : Blo 1375507 2063759 := bstep (se 1 (by rfl) ⟨1547819, by rfl⟩ : syracuseStep 2063759 = 3095639) B3095639
theorem B2063801 : Blo 1375507 2063801 := bstep (se 2 (by rfl) ⟨773925, by rfl⟩ : syracuseStep 2063801 = 1547851) B1547851
theorem B21192121 : Blo 1375507 21192121 := bstep (se 2 (by rfl) ⟨7947045, by rfl⟩ : syracuseStep 21192121 = 15894091) B15894091
theorem B1375675 : Blo 1375507 1375675 := bstep (se 1 (by rfl) ⟨1031756, by rfl⟩ : syracuseStep 1375675 = 2063513) B2063513
theorem B1547707 : Blo 1375507 1547707 := bstep (se 1 (by rfl) ⟨1160780, by rfl⟩ : syracuseStep 1547707 = 2321561) B2321561
theorem B1375751 : Blo 1375507 1375751 := bstep (se 1 (by rfl) ⟨1031813, by rfl⟩ : syracuseStep 1375751 = 2063627) B2063627
theorem B2063879 : Blo 1375507 2063879 := bstep (se 1 (by rfl) ⟨1547909, by rfl⟩ : syracuseStep 2063879 = 3095819) B3095819
theorem B4185611 : Blo 1375507 4185611 := bstep (se 1 (by rfl) ⟨3139208, by rfl⟩ : syracuseStep 4185611 = 6278417) B6278417
theorem B1375759 : Blo 1375507 1375759 := bstep (se 1 (by rfl) ⟨1031819, by rfl⟩ : syracuseStep 1375759 = 2063639) B2063639
theorem B2063915 : Blo 1375507 2063915 := bstep (se 1 (by rfl) ⟨1547936, by rfl⟩ : syracuseStep 2063915 = 3095873) B3095873
theorem B3096107 : Blo 1375507 3096107 := bstep (se 1 (by rfl) ⟨2322080, by rfl⟩ : syracuseStep 3096107 = 4644161) B4644161
theorem B1375803 : Blo 1375507 1375803 := bstep (se 1 (by rfl) ⟨1031852, by rfl⟩ : syracuseStep 1375803 = 2063705) B2063705
theorem B12557891 : Blo 1375507 12557891 := bstep (se 1 (by rfl) ⟨9418418, by rfl⟩ : syracuseStep 12557891 = 18836837) B18836837
theorem B2063945 : Blo 1375507 2063945 := bstep (se 2 (by rfl) ⟨773979, by rfl⟩ : syracuseStep 2063945 = 1547959) B1547959
theorem B1375879 : Blo 1375507 1375879 := bstep (se 1 (by rfl) ⟨1031909, by rfl⟩ : syracuseStep 1375879 = 2063819) B2063819
theorem B1375887 : Blo 1375507 1375887 := bstep (se 1 (by rfl) ⟨1031915, by rfl⟩ : syracuseStep 1375887 = 2063831) B2063831
theorem B21175987 : Blo 1375507 21175987 := bstep (se 1 (by rfl) ⟨15881990, by rfl⟩ : syracuseStep 21175987 = 31763981) B31763981
theorem B17874611 : Blo 1375507 17874611 := bstep (se 1 (by rfl) ⟨13405958, by rfl⟩ : syracuseStep 17874611 = 26811917) B26811917
theorem B1375931 : Blo 1375507 1375931 := bstep (se 1 (by rfl) ⟨1031948, by rfl⟩ : syracuseStep 1375931 = 2063897) B2063897
theorem B2064059 : Blo 1375507 2064059 := bstep (se 1 (by rfl) ⟨1548044, by rfl⟩ : syracuseStep 2064059 = 3096089) B3096089
theorem B2064119 : Blo 1375507 2064119 := bstep (se 1 (by rfl) ⟨1548089, by rfl⟩ : syracuseStep 2064119 = 3096179) B3096179
theorem B1376007 : Blo 1375507 1376007 := bstep (se 1 (by rfl) ⟨1032005, by rfl⟩ : syracuseStep 1376007 = 2064011) B2064011
theorem B1376015 : Blo 1375507 1376015 := bstep (se 1 (by rfl) ⟨1032011, by rfl⟩ : syracuseStep 1376015 = 2064023) B2064023
theorem B2064143 : Blo 1375507 2064143 := bstep (se 1 (by rfl) ⟨1548107, by rfl⟩ : syracuseStep 2064143 = 3096215) B3096215
theorem B25100081 : Blo 1375507 25100081 := bstep (se 2 (by rfl) ⟨9412530, by rfl⟩ : syracuseStep 25100081 = 18825061) B18825061
theorem B2064185 : Blo 1375507 2064185 := bstep (se 2 (by rfl) ⟨774069, by rfl⟩ : syracuseStep 2064185 = 1548139) B1548139
theorem B1376059 : Blo 1375507 1376059 := bstep (se 1 (by rfl) ⟨1032044, by rfl⟩ : syracuseStep 1376059 = 2064089) B2064089
theorem B3309427 : Blo 1375507 3309427 := bstep (se 1 (by rfl) ⟨2482070, by rfl⟩ : syracuseStep 3309427 = 4964141) B4964141
theorem B1376135 : Blo 1375507 1376135 := bstep (se 1 (by rfl) ⟨1032101, by rfl⟩ : syracuseStep 1376135 = 2064203) B2064203
theorem B2064263 : Blo 1375507 2064263 := bstep (se 1 (by rfl) ⟨1548197, by rfl⟩ : syracuseStep 2064263 = 3096395) B3096395
theorem B1376143 : Blo 1375507 1376143 := bstep (se 1 (by rfl) ⟨1032107, by rfl⟩ : syracuseStep 1376143 = 2064215) B2064215
theorem B1548175 : Blo 1375507 1548175 := bstep (se 1 (by rfl) ⟨1161131, by rfl⟩ : syracuseStep 1548175 = 2322263) B2322263
theorem B3096467 : Blo 1375507 3096467 := bstep (se 1 (by rfl) ⟨2322350, by rfl⟩ : syracuseStep 3096467 = 4644701) B4644701
theorem B4644755 : Blo 1375507 4644755 := bstep (se 1 (by rfl) ⟨3483566, by rfl⟩ : syracuseStep 4644755 = 6967133) B6967133
theorem B17883031 : Blo 1375507 17883031 := bstep (se 1 (by rfl) ⟨13412273, by rfl⟩ : syracuseStep 17883031 = 26824547) B26824547
theorem B2064299 : Blo 1375507 2064299 := bstep (se 1 (by rfl) ⟨1548224, by rfl⟩ : syracuseStep 2064299 = 3096449) B3096449
theorem B1376187 : Blo 1375507 1376187 := bstep (se 1 (by rfl) ⟨1032140, by rfl⟩ : syracuseStep 1376187 = 2064281) B2064281
theorem B2064329 : Blo 1375507 2064329 := bstep (se 2 (by rfl) ⟨774123, by rfl⟩ : syracuseStep 2064329 = 1548247) B1548247
theorem B3096521 : Blo 1375507 3096521 := bstep (se 2 (by rfl) ⟨1161195, by rfl⟩ : syracuseStep 3096521 = 2322391) B2322391
theorem B6971345 : Blo 1375507 6971345 := bstep (se 2 (by rfl) ⟨2614254, by rfl⟩ : syracuseStep 6971345 = 5228509) B5228509
theorem B1376295 : Blo 1375507 1376295 := bstep (se 1 (by rfl) ⟨1032221, by rfl⟩ : syracuseStep 1376295 = 2064443) B2064443
theorem B1376335 : Blo 1375507 1376335 := bstep (se 1 (by rfl) ⟨1032251, by rfl⟩ : syracuseStep 1376335 = 2064503) B2064503
theorem B1376351 : Blo 1375507 1376351 := bstep (se 1 (by rfl) ⟨1032263, by rfl⟩ : syracuseStep 1376351 = 2064527) B2064527
theorem B6971507 : Blo 1375507 6971507 := bstep (se 1 (by rfl) ⟨5228630, by rfl⟩ : syracuseStep 6971507 = 10457261) B10457261
theorem B1376379 : Blo 1375507 1376379 := bstep (se 1 (by rfl) ⟨1032284, by rfl⟩ : syracuseStep 1376379 = 2064569) B2064569
theorem B1376431 : Blo 1375507 1376431 := bstep (se 1 (by rfl) ⟨1032323, by rfl⟩ : syracuseStep 1376431 = 2064647) B2064647
theorem B1376455 : Blo 1375507 1376455 := bstep (se 1 (by rfl) ⟨1032341, by rfl⟩ : syracuseStep 1376455 = 2064683) B2064683
theorem B1376475 : Blo 1375507 1376475 := bstep (se 1 (by rfl) ⟨1032356, by rfl⟩ : syracuseStep 1376475 = 2064713) B2064713
theorem B1376551 : Blo 1375507 1376551 := bstep (se 1 (by rfl) ⟨1032413, by rfl⟩ : syracuseStep 1376551 = 2064827) B2064827
theorem B1376591 : Blo 1375507 1376591 := bstep (se 1 (by rfl) ⟨1032443, by rfl⟩ : syracuseStep 1376591 = 2064887) B2064887
theorem B5226839 : Blo 1375507 5226839 := bstep (se 1 (by rfl) ⟨3920129, by rfl⟩ : syracuseStep 5226839 = 7840259) B7840259
theorem B1376607 : Blo 1375507 1376607 := bstep (se 1 (by rfl) ⟨1032455, by rfl⟩ : syracuseStep 1376607 = 2064911) B2064911
theorem B1376635 : Blo 1375507 1376635 := bstep (se 1 (by rfl) ⟨1032476, by rfl⟩ : syracuseStep 1376635 = 2064953) B2064953
theorem B2613647 : Blo 1375507 2613647 := bstep (se 1 (by rfl) ⟨1960235, by rfl⟩ : syracuseStep 2613647 = 3920471) B3920471
theorem B2064815 : Blo 1375507 2064815 := bstep (se 1 (by rfl) ⟨1548611, by rfl⟩ : syracuseStep 2064815 = 3097223) B3097223
theorem B1376687 : Blo 1375507 1376687 := bstep (se 1 (by rfl) ⟨1032515, by rfl⟩ : syracuseStep 1376687 = 2065031) B2065031
theorem B1860023 : Blo 1375507 1860023 := bstep (se 1 (by rfl) ⟨1395017, by rfl⟩ : syracuseStep 1860023 = 2790035) B2790035
theorem B1376711 : Blo 1375507 1376711 := bstep (se 1 (by rfl) ⟨1032533, by rfl⟩ : syracuseStep 1376711 = 2065067) B2065067
theorem B1376731 : Blo 1375507 1376731 := bstep (se 1 (by rfl) ⟨1032548, by rfl⟩ : syracuseStep 1376731 = 2065097) B2065097
theorem B3482099 : Blo 1375507 3482099 := bstep (se 1 (by rfl) ⟨2611574, by rfl⟩ : syracuseStep 3482099 = 5223149) B5223149
theorem B3531251 : Blo 1375507 3531251 := bstep (se 1 (by rfl) ⟨2648438, by rfl⟩ : syracuseStep 3531251 = 5296877) B5296877
theorem B3097097 : Blo 1375507 3097097 := bstep (se 2 (by rfl) ⟨1161411, by rfl⟩ : syracuseStep 3097097 = 2322823) B2322823
theorem B2064905 : Blo 1375507 2064905 := bstep (se 2 (by rfl) ⟨774339, by rfl⟩ : syracuseStep 2064905 = 1548679) B1548679
theorem B2064935 : Blo 1375507 2064935 := bstep (se 1 (by rfl) ⟨1548701, by rfl⟩ : syracuseStep 2064935 = 3097403) B3097403
theorem B1376807 : Blo 1375507 1376807 := bstep (se 1 (by rfl) ⟨1032605, by rfl⟩ : syracuseStep 1376807 = 2065211) B2065211
theorem B2613799 : Blo 1375507 2613799 := bstep (se 1 (by rfl) ⟨1960349, by rfl⟩ : syracuseStep 2613799 = 3920699) B3920699
theorem B1376847 : Blo 1375507 1376847 := bstep (se 1 (by rfl) ⟨1032635, by rfl⟩ : syracuseStep 1376847 = 2065271) B2065271
theorem B1376863 : Blo 1375507 1376863 := bstep (se 1 (by rfl) ⟨1032647, by rfl⟩ : syracuseStep 1376863 = 2065295) B2065295
theorem B2065019 : Blo 1375507 2065019 := bstep (se 1 (by rfl) ⟨1548764, by rfl⟩ : syracuseStep 2065019 = 3097529) B3097529
theorem B2613883 : Blo 1375507 2613883 := bstep (se 1 (by rfl) ⟨1960412, by rfl⟩ : syracuseStep 2613883 = 3920825) B3920825
theorem B1376891 : Blo 1375507 1376891 := bstep (se 1 (by rfl) ⟨1032668, by rfl⟩ : syracuseStep 1376891 = 2065337) B2065337
theorem B4645511 : Blo 1375507 4645511 := bstep (se 1 (by rfl) ⟨3484133, by rfl⟩ : syracuseStep 4645511 = 6968267) B6968267
theorem B1376943 : Blo 1375507 1376943 := bstep (se 1 (by rfl) ⟨1032707, by rfl⟩ : syracuseStep 1376943 = 2065415) B2065415
theorem B4645565 : Blo 1375507 4645565 := bstep (se 3 (by rfl) ⟨871043, by rfl⟩ : syracuseStep 4645565 = 1742087) B1742087
theorem B3482311 : Blo 1375507 3482311 := bstep (se 1 (by rfl) ⟨2611733, by rfl⟩ : syracuseStep 3482311 = 5223467) B5223467
theorem B1376967 : Blo 1375507 1376967 := bstep (se 1 (by rfl) ⟨1032725, by rfl⟩ : syracuseStep 1376967 = 2065451) B2065451
theorem B1376987 : Blo 1375507 1376987 := bstep (se 1 (by rfl) ⟨1032740, by rfl⟩ : syracuseStep 1376987 = 2065481) B2065481
theorem B2065145 : Blo 1375507 2065145 := bstep (se 2 (by rfl) ⟨774429, by rfl⟩ : syracuseStep 2065145 = 1548859) B1548859
theorem B37692161 : Blo 1375507 37692161 := bstep (se 2 (by rfl) ⟨14134560, by rfl⟩ : syracuseStep 37692161 = 28269121) B28269121
theorem B10445597 : Blo 1375507 10445597 := bstep (se 3 (by rfl) ⟨1958549, by rfl⟩ : syracuseStep 10445597 = 3917099) B3917099
theorem B1377063 : Blo 1375507 1377063 := bstep (se 1 (by rfl) ⟨1032797, by rfl⟩ : syracuseStep 1377063 = 2065595) B2065595
theorem B1377103 : Blo 1375507 1377103 := bstep (se 1 (by rfl) ⟨1032827, by rfl⟩ : syracuseStep 1377103 = 2065655) B2065655
theorem B4645727 : Blo 1375507 4645727 := bstep (se 1 (by rfl) ⟨3484295, by rfl⟩ : syracuseStep 4645727 = 6968591) B6968591
theorem B3097439 : Blo 1375507 3097439 := bstep (se 1 (by rfl) ⟨2323079, by rfl⟩ : syracuseStep 3097439 = 4646159) B4646159
theorem B2065247 : Blo 1375507 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B1377119 : Blo 1375507 1377119 := bstep (se 1 (by rfl) ⟨1032839, by rfl⟩ : syracuseStep 1377119 = 2065679) B2065679
theorem B2065259 : Blo 1375507 2065259 := bstep (se 1 (by rfl) ⟨1548944, by rfl⟩ : syracuseStep 2065259 = 3097889) B3097889
theorem B1377147 : Blo 1375507 1377147 := bstep (se 1 (by rfl) ⟨1032860, by rfl⟩ : syracuseStep 1377147 = 2065721) B2065721
theorem B1377199 : Blo 1375507 1377199 := bstep (se 1 (by rfl) ⟨1032899, by rfl⟩ : syracuseStep 1377199 = 2065799) B2065799
theorem B2204599 : Blo 1375507 2204599 := bstep (se 1 (by rfl) ⟨1653449, by rfl⟩ : syracuseStep 2204599 = 3306899) B3306899
theorem B1377223 : Blo 1375507 1377223 := bstep (se 1 (by rfl) ⟨1032917, by rfl⟩ : syracuseStep 1377223 = 2065835) B2065835
theorem B1377243 : Blo 1375507 1377243 := bstep (se 1 (by rfl) ⟨1032932, by rfl⟩ : syracuseStep 1377243 = 2065865) B2065865
theorem B4645889 : Blo 1375507 4645889 := bstep (se 2 (by rfl) ⟨1742208, by rfl⟩ : syracuseStep 4645889 = 3484417) B3484417
theorem B4187143 : Blo 1375507 4187143 := bstep (se 1 (by rfl) ⟨3140357, by rfl⟩ : syracuseStep 4187143 = 6280715) B6280715
theorem B3097619 : Blo 1375507 3097619 := bstep (se 1 (by rfl) ⟨2323214, by rfl⟩ : syracuseStep 3097619 = 4646429) B4646429
theorem B1377319 : Blo 1375507 1377319 := bstep (se 1 (by rfl) ⟨1032989, by rfl⟩ : syracuseStep 1377319 = 2065979) B2065979
theorem B2065487 : Blo 1375507 2065487 := bstep (se 1 (by rfl) ⟨1549115, by rfl⟩ : syracuseStep 2065487 = 3098231) B3098231
theorem B1377359 : Blo 1375507 1377359 := bstep (se 1 (by rfl) ⟨1033019, by rfl⟩ : syracuseStep 1377359 = 2066039) B2066039
theorem B1377375 : Blo 1375507 1377375 := bstep (se 1 (by rfl) ⟨1033031, by rfl⟩ : syracuseStep 1377375 = 2066063) B2066063
theorem B2614369 : Blo 1375507 2614369 := bstep (se 2 (by rfl) ⟨980388, by rfl⟩ : syracuseStep 2614369 = 1960777) B1960777
theorem B1549435 : Blo 1375507 1549435 := bstep (se 1 (by rfl) ⟨1162076, by rfl⟩ : syracuseStep 1549435 = 2324153) B2324153
theorem B1377403 : Blo 1375507 1377403 := bstep (se 1 (by rfl) ⟨1033052, by rfl⟩ : syracuseStep 1377403 = 2066105) B2066105
theorem B1377455 : Blo 1375507 1377455 := bstep (se 1 (by rfl) ⟨1033091, by rfl⟩ : syracuseStep 1377455 = 2066183) B2066183
theorem B2065607 : Blo 1375507 2065607 := bstep (se 1 (by rfl) ⟨1549205, by rfl⟩ : syracuseStep 2065607 = 3098411) B3098411
theorem B1377479 : Blo 1375507 1377479 := bstep (se 1 (by rfl) ⟨1033109, by rfl⟩ : syracuseStep 1377479 = 2066219) B2066219
theorem B1377499 : Blo 1375507 1377499 := bstep (se 1 (by rfl) ⟨1033124, by rfl⟩ : syracuseStep 1377499 = 2066249) B2066249
theorem B4957451 : Blo 1375507 4957451 := bstep (se 1 (by rfl) ⟨3718088, by rfl⟩ : syracuseStep 4957451 = 7436177) B7436177
theorem B3097961 : Blo 1375507 3097961 := bstep (se 2 (by rfl) ⟨1161735, by rfl⟩ : syracuseStep 3097961 = 2323471) B2323471
theorem B2065769 : Blo 1375507 2065769 := bstep (se 2 (by rfl) ⟨774663, by rfl⟩ : syracuseStep 2065769 = 1549327) B1549327
theorem B2065847 : Blo 1375507 2065847 := bstep (se 1 (by rfl) ⟨1549385, by rfl⟩ : syracuseStep 2065847 = 3098771) B3098771
theorem B2065883 : Blo 1375507 2065883 := bstep (se 1 (by rfl) ⟨1549412, by rfl⟩ : syracuseStep 2065883 = 3098825) B3098825
theorem B3483233 : Blo 1375507 3483233 := bstep (se 2 (by rfl) ⟨1306212, by rfl⟩ : syracuseStep 3483233 = 2612425) B2612425
theorem B1959547 : Blo 1375507 1959547 := bstep (se 1 (by rfl) ⟨1469660, by rfl⟩ : syracuseStep 1959547 = 2939321) B2939321
theorem B5580427 : Blo 1375507 5580427 := bstep (se 1 (by rfl) ⟨4185320, by rfl⟩ : syracuseStep 5580427 = 8370641) B8370641
theorem B6973127 : Blo 1375507 6973127 := bstep (se 1 (by rfl) ⟨5229845, by rfl⟩ : syracuseStep 6973127 = 10459691) B10459691
theorem B3720953 : Blo 1375507 3720953 := bstep (se 2 (by rfl) ⟨1395357, by rfl⟩ : syracuseStep 3720953 = 2790715) B2790715
theorem B4646699 : Blo 1375507 4646699 := bstep (se 1 (by rfl) ⟨3485024, by rfl⟩ : syracuseStep 4646699 = 6970049) B6970049
theorem B3770219 : Blo 1375507 3770219 := bstep (se 1 (by rfl) ⟨2827664, by rfl⟩ : syracuseStep 3770219 = 5655329) B5655329
theorem B28256161 : Blo 1375507 28256161 := bstep (se 2 (by rfl) ⟨10596060, by rfl⟩ : syracuseStep 28256161 = 21192121) B21192121
theorem B32237473 : Blo 1375507 32237473 := bstep (se 2 (by rfl) ⟨12089052, by rfl⟩ : syracuseStep 32237473 = 24178105) B24178105
theorem B2353079 : Blo 1375507 2353079 := bstep (se 1 (by rfl) ⟨1764809, by rfl⟩ : syracuseStep 2353079 = 3529619) B3529619
theorem B3098555 : Blo 1375507 3098555 := bstep (se 1 (by rfl) ⟨2323916, by rfl⟩ : syracuseStep 3098555 = 4647833) B4647833
theorem B3532819 : Blo 1375507 3532819 := bstep (se 1 (by rfl) ⟨2649614, by rfl⟩ : syracuseStep 3532819 = 5299229) B5299229
theorem B4646969 : Blo 1375507 4646969 := bstep (se 2 (by rfl) ⟨1742613, by rfl⟩ : syracuseStep 4646969 = 3485227) B3485227
theorem B3098681 : Blo 1375507 3098681 := bstep (se 2 (by rfl) ⟨1162005, by rfl⟩ : syracuseStep 3098681 = 2324011) B2324011
theorem B4647293 : Blo 1375507 4647293 := bstep (se 3 (by rfl) ⟨871367, by rfl⟩ : syracuseStep 4647293 = 1742735) B1742735
theorem B3099023 : Blo 1375507 3099023 := bstep (se 1 (by rfl) ⟨2324267, by rfl⟩ : syracuseStep 3099023 = 4648535) B4648535
theorem B4647563 : Blo 1375507 4647563 := bstep (se 1 (by rfl) ⟨3485672, by rfl⟩ : syracuseStep 4647563 = 6971345) B6971345
theorem B11168441 : Blo 1375507 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B7949009 : Blo 1375507 7949009 := bstep (se 2 (by rfl) ⟨2980878, by rfl⟩ : syracuseStep 7949009 = 5961757) B5961757
theorem B3099347 : Blo 1375507 3099347 := bstep (se 1 (by rfl) ⟨2324510, by rfl⟩ : syracuseStep 3099347 = 4649021) B4649021
theorem B3533561 : Blo 1375507 3533561 := bstep (se 2 (by rfl) ⟨1325085, by rfl⟩ : syracuseStep 3533561 = 2650171) B2650171
theorem B142986059 : Blo 1375507 142986059 := bstep (se 1 (by rfl) ⟨107239544, by rfl⟩ : syracuseStep 142986059 = 214479089) B214479089
theorem B2321257 : Blo 1375507 2321257 := bstep (se 2 (by rfl) ⟨870471, by rfl⟩ : syracuseStep 2321257 = 1740943) B1740943
theorem B4959137 : Blo 1375507 4959137 := bstep (se 2 (by rfl) ⟨1859676, by rfl⟩ : syracuseStep 4959137 = 3719353) B3719353
theorem B7842743 : Blo 1375507 7842743 := bstep (se 1 (by rfl) ⟨5882057, by rfl⟩ : syracuseStep 7842743 = 11764115) B11764115
theorem B10210277 : Blo 1375507 10210277 := bstep (se 4 (by rfl) ⟨957213, by rfl⟩ : syracuseStep 10210277 = 1914427) B1914427
theorem B3484691 : Blo 1375507 3484691 := bstep (se 1 (by rfl) ⟨2613518, by rfl⟩ : syracuseStep 3484691 = 5227037) B5227037
theorem B6966323 : Blo 1375507 6966323 := bstep (se 1 (by rfl) ⟨5224742, by rfl⟩ : syracuseStep 6966323 = 10449485) B10449485
theorem B5229953 : Blo 1375507 5229953 := bstep (se 2 (by rfl) ⟨1961232, by rfl⟩ : syracuseStep 5229953 = 3922465) B3922465
theorem B5229967 : Blo 1375507 5229967 := bstep (se 1 (by rfl) ⟨3922475, by rfl⟩ : syracuseStep 5229967 = 7844951) B7844951
theorem B2788769 : Blo 1375507 2788769 := bstep (se 2 (by rfl) ⟨1045788, by rfl⟩ : syracuseStep 2788769 = 2091577) B2091577
theorem B2321851 : Blo 1375507 2321851 := bstep (se 1 (by rfl) ⟨1741388, by rfl⟩ : syracuseStep 2321851 = 3482777) B3482777
theorem B4648481 : Blo 1375507 4648481 := bstep (se 2 (by rfl) ⟨1743180, by rfl⟩ : syracuseStep 4648481 = 3486361) B3486361
theorem B2321959 : Blo 1375507 2321959 := bstep (se 1 (by rfl) ⟨1741469, by rfl⟩ : syracuseStep 2321959 = 3482939) B3482939
theorem B6614567 : Blo 1375507 6614567 := bstep (se 1 (by rfl) ⟨4960925, by rfl⟩ : syracuseStep 6614567 = 9921851) B9921851
theorem B28241531 : Blo 1375507 28241531 := bstep (se 1 (by rfl) ⟨21181148, by rfl⟩ : syracuseStep 28241531 = 42362297) B42362297
theorem B11169413 : Blo 1375507 11169413 := bstep (se 4 (by rfl) ⟨1047132, by rfl⟩ : syracuseStep 11169413 = 2094265) B2094265
theorem B3919549 : Blo 1375507 3919549 := bstep (se 3 (by rfl) ⟨734915, by rfl⟩ : syracuseStep 3919549 = 1469831) B1469831
theorem B10456775 : Blo 1375507 10456775 := bstep (se 1 (by rfl) ⟨7842581, by rfl⟩ : syracuseStep 10456775 = 15685163) B15685163
theorem B4648697 : Blo 1375507 4648697 := bstep (se 2 (by rfl) ⟨1743261, by rfl⟩ : syracuseStep 4648697 = 3486523) B3486523
theorem B2322283 : Blo 1375507 2322283 := bstep (se 1 (by rfl) ⟨1741712, by rfl⟩ : syracuseStep 2322283 = 3483425) B3483425
theorem B27545507 : Blo 1375507 27545507 := bstep (se 1 (by rfl) ⟨20659130, by rfl⟩ : syracuseStep 27545507 = 41318261) B41318261
theorem B4648967 : Blo 1375507 4648967 := bstep (se 1 (by rfl) ⟨3486725, by rfl⟩ : syracuseStep 4648967 = 6973451) B6973451
theorem B8818703 : Blo 1375507 8818703 := bstep (se 1 (by rfl) ⟨6614027, by rfl⟩ : syracuseStep 8818703 = 13228055) B13228055
theorem B13234205 : Blo 1375507 13234205 := bstep (se 3 (by rfl) ⟨2481413, by rfl⟩ : syracuseStep 13234205 = 4962827) B4962827
theorem B1675343 : Blo 1375507 1675343 := bstep (se 1 (by rfl) ⟨1256507, by rfl⟩ : syracuseStep 1675343 = 2513015) B2513015
theorem B4649075 : Blo 1375507 4649075 := bstep (se 1 (by rfl) ⟨3486806, by rfl⟩ : syracuseStep 4649075 = 6973613) B6973613
theorem B7844201 : Blo 1375507 7844201 := bstep (se 2 (by rfl) ⟨2941575, by rfl⟩ : syracuseStep 7844201 = 5883151) B5883151
theorem B5222951 : Blo 1375507 5222951 := bstep (se 1 (by rfl) ⟨3917213, by rfl⟩ : syracuseStep 5222951 = 7834427) B7834427
theorem B38203969 : Blo 1375507 38203969 := bstep (se 2 (by rfl) ⟨14326488, by rfl⟩ : syracuseStep 38203969 = 28652977) B28652977
theorem B6967943 : Blo 1375507 6967943 := bstep (se 1 (by rfl) ⟨5225957, by rfl⟩ : syracuseStep 6967943 = 10451915) B10451915
theorem B20378441 : Blo 1375507 20378441 := bstep (se 2 (by rfl) ⟨7641915, by rfl⟩ : syracuseStep 20378441 = 15283831) B15283831
theorem B2323343 : Blo 1375507 2323343 := bstep (se 1 (by rfl) ⟨1742507, by rfl⟩ : syracuseStep 2323343 = 3485015) B3485015
theorem B8819603 : Blo 1375507 8819603 := bstep (se 1 (by rfl) ⟨6614702, by rfl⟩ : syracuseStep 8819603 = 13229405) B13229405
theorem B28234649 : Blo 1375507 28234649 := bstep (se 2 (by rfl) ⟨10587993, by rfl⟩ : syracuseStep 28234649 = 21175987) B21175987
theorem B2790407 : Blo 1375507 2790407 := bstep (se 1 (by rfl) ⟨2092805, by rfl⟩ : syracuseStep 2790407 = 4185611) B4185611
theorem B10449971 : Blo 1375507 10449971 := bstep (se 1 (by rfl) ⟨7837478, by rfl⟩ : syracuseStep 10449971 = 15674957) B15674957
theorem B11916407 : Blo 1375507 11916407 := bstep (se 1 (by rfl) ⟨8937305, by rfl⟩ : syracuseStep 11916407 = 17874611) B17874611
theorem B2323579 : Blo 1375507 2323579 := bstep (se 1 (by rfl) ⟨1742684, by rfl⟩ : syracuseStep 2323579 = 3485369) B3485369
theorem B4412569 : Blo 1375507 4412569 := bstep (se 2 (by rfl) ⟨1654713, by rfl⟩ : syracuseStep 4412569 = 3309427) B3309427
theorem B23844041 : Blo 1375507 23844041 := bstep (se 2 (by rfl) ⟨8941515, by rfl⟩ : syracuseStep 23844041 = 17883031) B17883031
theorem B16733387 : Blo 1375507 16733387 := bstep (se 1 (by rfl) ⟨12550040, by rfl⟩ : syracuseStep 16733387 = 25100081) B25100081
theorem B3921281 : Blo 1375507 3921281 := bstep (se 2 (by rfl) ⟨1470480, by rfl⟩ : syracuseStep 3921281 = 2940961) B2940961
theorem B29783537 : Blo 1375507 29783537 := bstep (se 2 (by rfl) ⟨11168826, by rfl⟩ : syracuseStep 29783537 = 22337653) B22337653
theorem B5223923 : Blo 1375507 5223923 := bstep (se 1 (by rfl) ⟨3917942, by rfl⟩ : syracuseStep 5223923 = 7835885) B7835885
theorem B3306995 : Blo 1375507 3306995 := bstep (se 1 (by rfl) ⟨2480246, by rfl⟩ : syracuseStep 3306995 = 4960493) B4960493
theorem B1414831 : Blo 1375507 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B5224121 : Blo 1375507 5224121 := bstep (se 2 (by rfl) ⟨1959045, by rfl⟩ : syracuseStep 5224121 = 3918091) B3918091
theorem B5224135 : Blo 1375507 5224135 := bstep (se 1 (by rfl) ⟨3918101, by rfl⟩ : syracuseStep 5224135 = 7836203) B7836203
theorem B15898427 : Blo 1375507 15898427 := bstep (se 1 (by rfl) ⟨11923820, by rfl⟩ : syracuseStep 15898427 = 23847641) B23847641
theorem B2324443 : Blo 1375507 2324443 := bstep (se 1 (by rfl) ⟨1743332, by rfl⟩ : syracuseStep 2324443 = 3486665) B3486665
theorem B1742887 : Blo 1375507 1742887 := bstep (se 1 (by rfl) ⟨1307165, by rfl⟩ : syracuseStep 1742887 = 2614331) B2614331
theorem B6969401 : Blo 1375507 6969401 := bstep (se 2 (by rfl) ⟨2613525, by rfl⟩ : syracuseStep 6969401 = 5227051) B5227051
theorem B1652815 : Blo 1375507 1652815 := bstep (se 1 (by rfl) ⟨1239611, by rfl⟩ : syracuseStep 1652815 = 2479223) B2479223
theorem B2480225 : Blo 1375507 2480225 := bstep (se 2 (by rfl) ⟨930084, by rfl⟩ : syracuseStep 2480225 = 1860169) B1860169
theorem B4642973 : Blo 1375507 4642973 := bstep (se 3 (by rfl) ⟨870557, by rfl⟩ : syracuseStep 4642973 = 1741115) B1741115
theorem B5298493 : Blo 1375507 5298493 := bstep (se 3 (by rfl) ⟨993467, by rfl⟩ : syracuseStep 5298493 = 1986935) B1986935
theorem B2480491 : Blo 1375507 2480491 := bstep (se 1 (by rfl) ⟨1860368, by rfl⟩ : syracuseStep 2480491 = 3720737) B3720737
theorem B1743211 : Blo 1375507 1743211 := bstep (se 1 (by rfl) ⟨1307408, by rfl⟩ : syracuseStep 1743211 = 2614817) B2614817
theorem B11917721 : Blo 1375507 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B2939431 : Blo 1375507 2939431 := bstep (se 1 (by rfl) ⟨2204573, by rfl⟩ : syracuseStep 2939431 = 4409147) B4409147
theorem B37657133 : Blo 1375507 37657133 := bstep (se 3 (by rfl) ⟨7060712, by rfl⟩ : syracuseStep 37657133 = 14121425) B14121425
theorem B5225107 : Blo 1375507 5225107 := bstep (se 1 (by rfl) ⟨3918830, by rfl⟩ : syracuseStep 5225107 = 7837661) B7837661
theorem B4643513 : Blo 1375507 4643513 := bstep (se 2 (by rfl) ⟨1741317, by rfl⟩ : syracuseStep 4643513 = 3482635) B3482635
theorem B3095369 : Blo 1375507 3095369 := bstep (se 2 (by rfl) ⟨1160763, by rfl⟩ : syracuseStep 3095369 = 2321527) B2321527
theorem B4184905 : Blo 1375507 4184905 := bstep (se 2 (by rfl) ⟨1569339, by rfl⟩ : syracuseStep 4184905 = 3138679) B3138679
theorem B2063279 : Blo 1375507 2063279 := bstep (se 1 (by rfl) ⟨1547459, by rfl⟩ : syracuseStep 2063279 = 3094919) B3094919
theorem B2063369 : Blo 1375507 2063369 := bstep (se 2 (by rfl) ⟨773763, by rfl⟩ : syracuseStep 2063369 = 1547527) B1547527
theorem B2612243 : Blo 1375507 2612243 := bstep (se 1 (by rfl) ⟨1959182, by rfl⟩ : syracuseStep 2612243 = 3918365) B3918365
theorem B2063399 : Blo 1375507 2063399 := bstep (se 1 (by rfl) ⟨1547549, by rfl⟩ : syracuseStep 2063399 = 3095099) B3095099
theorem B6282319 : Blo 1375507 6282319 := bstep (se 1 (by rfl) ⟨4711739, by rfl⟩ : syracuseStep 6282319 = 9423479) B9423479
theorem B2063483 : Blo 1375507 2063483 := bstep (se 1 (by rfl) ⟨1547612, by rfl⟩ : syracuseStep 2063483 = 3095225) B3095225
theorem B1653959 : Blo 1375507 1653959 := bstep (se 1 (by rfl) ⟨1240469, by rfl⟩ : syracuseStep 1653959 = 2480939) B2480939
theorem B2063609 : Blo 1375507 2063609 := bstep (se 2 (by rfl) ⟨773853, by rfl⟩ : syracuseStep 2063609 = 1547707) B1547707
theorem B4644107 : Blo 1375507 4644107 := bstep (se 1 (by rfl) ⟨3483080, by rfl⟩ : syracuseStep 4644107 = 6966161) B6966161
theorem B1375527 : Blo 1375507 1375527 := bstep (se 1 (by rfl) ⟨1031645, by rfl⟩ : syracuseStep 1375527 = 2063291) B2063291
theorem B1375567 : Blo 1375507 1375567 := bstep (se 1 (by rfl) ⟨1031675, by rfl⟩ : syracuseStep 1375567 = 2063351) B2063351
theorem B1375583 : Blo 1375507 1375583 := bstep (se 1 (by rfl) ⟨1031687, by rfl⟩ : syracuseStep 1375583 = 2063375) B2063375
theorem B2063711 : Blo 1375507 2063711 := bstep (se 1 (by rfl) ⟨1547783, by rfl⟩ : syracuseStep 2063711 = 3095567) B3095567
theorem B2063723 : Blo 1375507 2063723 := bstep (se 1 (by rfl) ⟨1547792, by rfl⟩ : syracuseStep 2063723 = 3095585) B3095585
theorem B1375611 : Blo 1375507 1375611 := bstep (se 1 (by rfl) ⟨1031708, by rfl⟩ : syracuseStep 1375611 = 2063417) B2063417
theorem B7839119 : Blo 1375507 7839119 := bstep (se 1 (by rfl) ⟨5879339, by rfl⟩ : syracuseStep 7839119 = 11758679) B11758679
theorem B1375663 : Blo 1375507 1375663 := bstep (se 1 (by rfl) ⟨1031747, by rfl⟩ : syracuseStep 1375663 = 2063495) B2063495
theorem B1375687 : Blo 1375507 1375687 := bstep (se 1 (by rfl) ⟨1031765, by rfl⟩ : syracuseStep 1375687 = 2063531) B2063531
theorem B1375707 : Blo 1375507 1375707 := bstep (se 1 (by rfl) ⟨1031780, by rfl⟩ : syracuseStep 1375707 = 2063561) B2063561
theorem B3718619 : Blo 1375507 3718619 := bstep (se 1 (by rfl) ⟨2788964, by rfl⟩ : syracuseStep 3718619 = 5577929) B5577929
theorem B2481673 : Blo 1375507 2481673 := bstep (se 2 (by rfl) ⟨930627, by rfl⟩ : syracuseStep 2481673 = 1861255) B1861255
theorem B4644377 : Blo 1375507 4644377 := bstep (se 2 (by rfl) ⟨1741641, by rfl⟩ : syracuseStep 4644377 = 3483283) B3483283
theorem B1375783 : Blo 1375507 1375783 := bstep (se 1 (by rfl) ⟨1031837, by rfl⟩ : syracuseStep 1375783 = 2063675) B2063675
theorem B1547815 : Blo 1375507 1547815 := bstep (se 1 (by rfl) ⟨1160861, by rfl⟩ : syracuseStep 1547815 = 2321723) B2321723
theorem B1375823 : Blo 1375507 1375823 := bstep (se 1 (by rfl) ⟨1031867, by rfl⟩ : syracuseStep 1375823 = 2063735) B2063735
theorem B2063951 : Blo 1375507 2063951 := bstep (se 1 (by rfl) ⟨1547963, by rfl⟩ : syracuseStep 2063951 = 3095927) B3095927
theorem B1375839 : Blo 1375507 1375839 := bstep (se 1 (by rfl) ⟨1031879, by rfl⟩ : syracuseStep 1375839 = 2063759) B2063759
theorem B3096161 : Blo 1375507 3096161 := bstep (se 2 (by rfl) ⟨1161060, by rfl⟩ : syracuseStep 3096161 = 2322121) B2322121
theorem B1375867 : Blo 1375507 1375867 := bstep (se 1 (by rfl) ⟨1031900, by rfl⟩ : syracuseStep 1375867 = 2063801) B2063801
theorem B1375919 : Blo 1375507 1375919 := bstep (se 1 (by rfl) ⟨1031939, by rfl⟩ : syracuseStep 1375919 = 2063879) B2063879
theorem B1375943 : Blo 1375507 1375943 := bstep (se 1 (by rfl) ⟨1031957, by rfl⟩ : syracuseStep 1375943 = 2063915) B2063915
theorem B2064071 : Blo 1375507 2064071 := bstep (se 1 (by rfl) ⟨1548053, by rfl⟩ : syracuseStep 2064071 = 3096107) B3096107
theorem B8371927 : Blo 1375507 8371927 := bstep (se 1 (by rfl) ⟨6278945, by rfl⟩ : syracuseStep 8371927 = 12557891) B12557891
theorem B1375963 : Blo 1375507 1375963 := bstep (se 1 (by rfl) ⟨1031972, by rfl⟩ : syracuseStep 1375963 = 2063945) B2063945
theorem B5029661 : Blo 1375507 5029661 := bstep (se 3 (by rfl) ⟨943061, by rfl⟩ : syracuseStep 5029661 = 1886123) B1886123
theorem B1376039 : Blo 1375507 1376039 := bstep (se 1 (by rfl) ⟨1032029, by rfl⟩ : syracuseStep 1376039 = 2064059) B2064059
theorem B1376079 : Blo 1375507 1376079 := bstep (se 1 (by rfl) ⟨1032059, by rfl⟩ : syracuseStep 1376079 = 2064119) B2064119
theorem B1376095 : Blo 1375507 1376095 := bstep (se 1 (by rfl) ⟨1032071, by rfl⟩ : syracuseStep 1376095 = 2064143) B2064143
theorem B2064233 : Blo 1375507 2064233 := bstep (se 2 (by rfl) ⟨774087, by rfl⟩ : syracuseStep 2064233 = 1548175) B1548175
theorem B1376123 : Blo 1375507 1376123 := bstep (se 1 (by rfl) ⟨1032092, by rfl⟩ : syracuseStep 1376123 = 2064185) B2064185
theorem B1376175 : Blo 1375507 1376175 := bstep (se 1 (by rfl) ⟨1032131, by rfl⟩ : syracuseStep 1376175 = 2064263) B2064263
theorem B2064311 : Blo 1375507 2064311 := bstep (se 1 (by rfl) ⟨1548233, by rfl⟩ : syracuseStep 2064311 = 3096467) B3096467
theorem B3096503 : Blo 1375507 3096503 := bstep (se 1 (by rfl) ⟨2322377, by rfl⟩ : syracuseStep 3096503 = 4644755) B4644755
theorem B1376199 : Blo 1375507 1376199 := bstep (se 1 (by rfl) ⟨1032149, by rfl⟩ : syracuseStep 1376199 = 2064299) B2064299
theorem B9920465 : Blo 1375507 9920465 := bstep (se 2 (by rfl) ⟨3720174, by rfl⟩ : syracuseStep 9920465 = 7440349) B7440349
theorem B1376219 : Blo 1375507 1376219 := bstep (se 1 (by rfl) ⟨1032164, by rfl⟩ : syracuseStep 1376219 = 2064329) B2064329
theorem B2064347 : Blo 1375507 2064347 := bstep (se 1 (by rfl) ⟨1548260, by rfl⟩ : syracuseStep 2064347 = 3096521) B3096521
theorem B8822803 : Blo 1375507 8822803 := bstep (se 1 (by rfl) ⟨6617102, by rfl⟩ : syracuseStep 8822803 = 13234205) B13234205
theorem B4710425 : Blo 1375507 4710425 := bstep (se 2 (by rfl) ⟨1766409, by rfl⟩ : syracuseStep 4710425 = 3532819) B3532819
theorem B1376543 : Blo 1375507 1376543 := bstep (se 1 (by rfl) ⟨1032407, by rfl⟩ : syracuseStep 1376543 = 2064815) B2064815
theorem B31777085 : Blo 1375507 31777085 := bstep (se 3 (by rfl) ⟨5958203, by rfl⟩ : syracuseStep 31777085 = 11916407) B11916407
theorem B2064731 : Blo 1375507 2064731 := bstep (se 1 (by rfl) ⟨1548548, by rfl⟩ : syracuseStep 2064731 = 3097097) B3097097
theorem B1376603 : Blo 1375507 1376603 := bstep (se 1 (by rfl) ⟨1032452, by rfl⟩ : syracuseStep 1376603 = 2064905) B2064905
theorem B3481967 : Blo 1375507 3481967 := bstep (se 1 (by rfl) ⟨2611475, by rfl⟩ : syracuseStep 3481967 = 5222951) B5222951
theorem B1376623 : Blo 1375507 1376623 := bstep (se 1 (by rfl) ⟨1032467, by rfl⟩ : syracuseStep 1376623 = 2064935) B2064935
theorem B8815013 : Blo 1375507 8815013 := bstep (se 4 (by rfl) ⟨826407, by rfl⟩ : syracuseStep 8815013 = 1652815) B1652815
theorem B1376679 : Blo 1375507 1376679 := bstep (se 1 (by rfl) ⟨1032509, by rfl⟩ : syracuseStep 1376679 = 2065019) B2065019
theorem B4645295 : Blo 1375507 4645295 := bstep (se 1 (by rfl) ⟨3483971, by rfl⟩ : syracuseStep 4645295 = 6967943) B6967943
theorem B3097007 : Blo 1375507 3097007 := bstep (se 1 (by rfl) ⟨2322755, by rfl⟩ : syracuseStep 3097007 = 4645511) B4645511
theorem B3097043 : Blo 1375507 3097043 := bstep (se 1 (by rfl) ⟨2322782, by rfl⟩ : syracuseStep 3097043 = 4645565) B4645565
theorem B1376763 : Blo 1375507 1376763 := bstep (se 1 (by rfl) ⟨1032572, by rfl⟩ : syracuseStep 1376763 = 2065145) B2065145
theorem B6963731 : Blo 1375507 6963731 := bstep (se 1 (by rfl) ⟨5222798, by rfl⟩ : syracuseStep 6963731 = 10445597) B10445597
theorem B3097151 : Blo 1375507 3097151 := bstep (se 1 (by rfl) ⟨2322863, by rfl⟩ : syracuseStep 3097151 = 4645727) B4645727
theorem B2064959 : Blo 1375507 2064959 := bstep (se 1 (by rfl) ⟨1548719, by rfl⟩ : syracuseStep 2064959 = 3097439) B3097439
theorem B1376831 : Blo 1375507 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B1376839 : Blo 1375507 1376839 := bstep (se 1 (by rfl) ⟨1032629, by rfl⟩ : syracuseStep 1376839 = 2065259) B2065259
theorem B1548895 : Blo 1375507 1548895 := bstep (se 1 (by rfl) ⟨1161671, by rfl⟩ : syracuseStep 1548895 = 2323343) B2323343
theorem B3097259 : Blo 1375507 3097259 := bstep (se 1 (by rfl) ⟨2322944, by rfl⟩ : syracuseStep 3097259 = 4645889) B4645889
theorem B2065079 : Blo 1375507 2065079 := bstep (se 1 (by rfl) ⟨1548809, by rfl⟩ : syracuseStep 2065079 = 3097619) B3097619
theorem B1376991 : Blo 1375507 1376991 := bstep (se 1 (by rfl) ⟨1032743, by rfl⟩ : syracuseStep 1376991 = 2065487) B2065487
theorem B50938625 : Blo 1375507 50938625 := bstep (se 2 (by rfl) ⟨19101984, by rfl⟩ : syracuseStep 50938625 = 38203969) B38203969
theorem B1377071 : Blo 1375507 1377071 := bstep (se 1 (by rfl) ⟨1032803, by rfl⟩ : syracuseStep 1377071 = 2065607) B2065607
theorem B2065307 : Blo 1375507 2065307 := bstep (se 1 (by rfl) ⟨1548980, by rfl⟩ : syracuseStep 2065307 = 3097961) B3097961
theorem B1377179 : Blo 1375507 1377179 := bstep (se 1 (by rfl) ⟨1032884, by rfl⟩ : syracuseStep 1377179 = 2065769) B2065769
theorem B2614187 : Blo 1375507 2614187 := bstep (se 1 (by rfl) ⟨1960640, by rfl⟩ : syracuseStep 2614187 = 3921281) B3921281
theorem B1377231 : Blo 1375507 1377231 := bstep (se 1 (by rfl) ⟨1032923, by rfl⟩ : syracuseStep 1377231 = 2065847) B2065847
theorem B1377255 : Blo 1375507 1377255 := bstep (se 1 (by rfl) ⟨1032941, by rfl⟩ : syracuseStep 1377255 = 2065883) B2065883
theorem B3482615 : Blo 1375507 3482615 := bstep (se 1 (by rfl) ⟨2611961, by rfl⟩ : syracuseStep 3482615 = 5223923) B5223923
theorem B2204663 : Blo 1375507 2204663 := bstep (se 1 (by rfl) ⟨1653497, by rfl⟩ : syracuseStep 2204663 = 3306995) B3306995
theorem B5579873 : Blo 1375507 5579873 := bstep (se 2 (by rfl) ⟨2092452, by rfl⟩ : syracuseStep 5579873 = 4184905) B4184905
theorem B3482747 : Blo 1375507 3482747 := bstep (se 1 (by rfl) ⟨2612060, by rfl⟩ : syracuseStep 3482747 = 5224121) B5224121
theorem B3097799 : Blo 1375507 3097799 := bstep (se 1 (by rfl) ⟨2323349, by rfl⟩ : syracuseStep 3097799 = 4646699) B4646699
theorem B2065703 : Blo 1375507 2065703 := bstep (se 1 (by rfl) ⟨1549277, by rfl⟩ : syracuseStep 2065703 = 3098555) B3098555
theorem B4646267 : Blo 1375507 4646267 := bstep (se 1 (by rfl) ⟨3484700, by rfl⟩ : syracuseStep 4646267 = 6969401) B6969401
theorem B3097979 : Blo 1375507 3097979 := bstep (se 1 (by rfl) ⟨2323484, by rfl⟩ : syracuseStep 3097979 = 4646969) B4646969
theorem B2065787 : Blo 1375507 2065787 := bstep (se 1 (by rfl) ⟨1549340, by rfl⟩ : syracuseStep 2065787 = 3098681) B3098681
theorem B3098105 : Blo 1375507 3098105 := bstep (se 2 (by rfl) ⟨1161789, by rfl⟩ : syracuseStep 3098105 = 2323579) B2323579
theorem B2065913 : Blo 1375507 2065913 := bstep (se 2 (by rfl) ⟨774717, by rfl⟩ : syracuseStep 2065913 = 1549435) B1549435
theorem B5883425 : Blo 1375507 5883425 := bstep (se 2 (by rfl) ⟨2206284, by rfl⟩ : syracuseStep 5883425 = 4412569) B4412569
theorem B3098195 : Blo 1375507 3098195 := bstep (se 1 (by rfl) ⟨2323646, by rfl⟩ : syracuseStep 3098195 = 4647293) B4647293
theorem B2066015 : Blo 1375507 2066015 := bstep (se 1 (by rfl) ⟨1549511, by rfl⟩ : syracuseStep 2066015 = 3099023) B3099023
theorem B3098375 : Blo 1375507 3098375 := bstep (se 1 (by rfl) ⟨2323781, by rfl⟩ : syracuseStep 3098375 = 4647563) B4647563
theorem B2066231 : Blo 1375507 2066231 := bstep (se 1 (by rfl) ⟨1549673, by rfl⟩ : syracuseStep 2066231 = 3099347) B3099347
theorem B6973289 : Blo 1375507 6973289 := bstep (se 2 (by rfl) ⟨2614983, by rfl⟩ : syracuseStep 6973289 = 5229967) B5229967
theorem B95324039 : Blo 1375507 95324039 := bstep (se 1 (by rfl) ⟨71493029, by rfl⟩ : syracuseStep 95324039 = 142986059) B142986059
theorem B5228495 : Blo 1375507 5228495 := bstep (se 1 (by rfl) ⟨3921371, by rfl⟩ : syracuseStep 5228495 = 7842743) B7842743
theorem B7440569 : Blo 1375507 7440569 := bstep (se 2 (by rfl) ⟨2790213, by rfl⟩ : syracuseStep 7440569 = 5580427) B5580427
theorem B1886441 : Blo 1375507 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B6965513 : Blo 1375507 6965513 := bstep (se 2 (by rfl) ⟨2612067, by rfl⟩ : syracuseStep 6965513 = 5224135) B5224135
theorem B3098987 : Blo 1375507 3098987 := bstep (se 1 (by rfl) ⟨2324240, by rfl⟩ : syracuseStep 3098987 = 4648481) B4648481
theorem B4409711 : Blo 1375507 4409711 := bstep (se 1 (by rfl) ⟨3307283, by rfl⟩ : syracuseStep 4409711 = 6614567) B6614567
theorem B18827687 : Blo 1375507 18827687 := bstep (se 1 (by rfl) ⟨14120765, by rfl⟩ : syracuseStep 18827687 = 28241531) B28241531
theorem B3099131 : Blo 1375507 3099131 := bstep (se 1 (by rfl) ⟨2324348, by rfl⟩ : syracuseStep 3099131 = 4648697) B4648697
theorem B3353107 : Blo 1375507 3353107 := bstep (se 1 (by rfl) ⟨2514830, by rfl⟩ : syracuseStep 3353107 = 5029661) B5029661
theorem B3099257 : Blo 1375507 3099257 := bstep (se 2 (by rfl) ⟨1162221, by rfl⟩ : syracuseStep 3099257 = 2324443) B2324443
theorem B6613643 : Blo 1375507 6613643 := bstep (se 1 (by rfl) ⟨4960232, by rfl⟩ : syracuseStep 6613643 = 9920465) B9920465
theorem B3099311 : Blo 1375507 3099311 := bstep (se 1 (by rfl) ⟨2324483, by rfl⟩ : syracuseStep 3099311 = 4648967) B4648967
theorem B7441085 : Blo 1375507 7441085 := bstep (se 3 (by rfl) ⟨1395203, by rfl⟩ : syracuseStep 7441085 = 2790407) B2790407
theorem B4647671 : Blo 1375507 4647671 := bstep (se 1 (by rfl) ⟨3485753, by rfl⟩ : syracuseStep 4647671 = 6971507) B6971507
theorem B3099383 : Blo 1375507 3099383 := bstep (se 1 (by rfl) ⟨2324537, by rfl⟩ : syracuseStep 3099383 = 4649075) B4649075
theorem B4467581 : Blo 1375507 4467581 := bstep (se 3 (by rfl) ⟨837671, by rfl⟩ : syracuseStep 4467581 = 1675343) B1675343
theorem B3484559 : Blo 1375507 3484559 := bstep (se 1 (by rfl) ⟨2613419, by rfl⟩ : syracuseStep 3484559 = 5226839) B5226839
theorem B5229467 : Blo 1375507 5229467 := bstep (se 1 (by rfl) ⟨3922100, by rfl⟩ : syracuseStep 5229467 = 7844201) B7844201
theorem B6613933 : Blo 1375507 6613933 := bstep (se 3 (by rfl) ⟨1240112, by rfl⟩ : syracuseStep 6613933 = 2480225) B2480225
theorem B2321399 : Blo 1375507 2321399 := bstep (se 1 (by rfl) ⟨1741049, by rfl⟩ : syracuseStep 2321399 = 3482099) B3482099
theorem B2354167 : Blo 1375507 2354167 := bstep (se 1 (by rfl) ⟨1765625, by rfl⟩ : syracuseStep 2354167 = 3531251) B3531251
theorem B7064657 : Blo 1375507 7064657 := bstep (se 2 (by rfl) ⟨2649246, by rfl⟩ : syracuseStep 7064657 = 5298493) B5298493
theorem B25128107 : Blo 1375507 25128107 := bstep (se 1 (by rfl) ⟨18846080, by rfl⟩ : syracuseStep 25128107 = 37692161) B37692161
theorem B4410557 : Blo 1375507 4410557 := bstep (se 3 (by rfl) ⟨826979, by rfl⟩ : syracuseStep 4410557 = 1653959) B1653959
theorem B13585627 : Blo 1375507 13585627 := bstep (se 1 (by rfl) ⟨10189220, by rfl⟩ : syracuseStep 13585627 = 20378441) B20378441
theorem B6966647 : Blo 1375507 6966647 := bstep (se 1 (by rfl) ⟨5224985, by rfl⟩ : syracuseStep 6966647 = 10449971) B10449971
theorem B3919241 : Blo 1375507 3919241 := bstep (se 2 (by rfl) ⟨1469715, by rfl⟩ : syracuseStep 3919241 = 2939431) B2939431
theorem B3485065 : Blo 1375507 3485065 := bstep (se 2 (by rfl) ⟨1306899, by rfl⟩ : syracuseStep 3485065 = 2613799) B2613799
theorem B15896027 : Blo 1375507 15896027 := bstep (se 1 (by rfl) ⟨11922020, by rfl⟩ : syracuseStep 15896027 = 23844041) B23844041
theorem B3485177 : Blo 1375507 3485177 := bstep (se 2 (by rfl) ⟨1306941, by rfl⟩ : syracuseStep 3485177 = 2613883) B2613883
theorem B3304967 : Blo 1375507 3304967 := bstep (se 1 (by rfl) ⟨2478725, by rfl⟩ : syracuseStep 3304967 = 4957451) B4957451
theorem B6966809 : Blo 1375507 6966809 := bstep (se 2 (by rfl) ⟨2612553, by rfl⟩ : syracuseStep 6966809 = 5225107) B5225107
theorem B2322155 : Blo 1375507 2322155 := bstep (se 1 (by rfl) ⟨1741616, by rfl⟩ : syracuseStep 2322155 = 3483233) B3483233
theorem B4648751 : Blo 1375507 4648751 := bstep (se 1 (by rfl) ⟨3486563, by rfl⟩ : syracuseStep 4648751 = 6973127) B6973127
theorem B4960061 : Blo 1375507 4960061 := bstep (se 3 (by rfl) ⟨930011, by rfl⟩ : syracuseStep 4960061 = 1860023) B1860023
theorem B1568719 : Blo 1375507 1568719 := bstep (se 1 (by rfl) ⟨1176539, by rfl⟩ : syracuseStep 1568719 = 2353079) B2353079
theorem B5582857 : Blo 1375507 5582857 := bstep (se 2 (by rfl) ⟨2093571, by rfl⟩ : syracuseStep 5582857 = 4187143) B4187143
theorem B8376425 : Blo 1375507 8376425 := bstep (se 2 (by rfl) ⟨3141159, by rfl⟩ : syracuseStep 8376425 = 6282319) B6282319
theorem B3485825 : Blo 1375507 3485825 := bstep (se 2 (by rfl) ⟨1307184, by rfl⟩ : syracuseStep 3485825 = 2614369) B2614369
theorem B25104755 : Blo 1375507 25104755 := bstep (se 1 (by rfl) ⟨18828566, by rfl⟩ : syracuseStep 25104755 = 37657133) B37657133
theorem B2355707 : Blo 1375507 2355707 := bstep (se 1 (by rfl) ⟨1766780, by rfl⟩ : syracuseStep 2355707 = 3533561) B3533561
theorem B3306091 : Blo 1375507 3306091 := bstep (se 1 (by rfl) ⟨2479568, by rfl⟩ : syracuseStep 3306091 = 4959137) B4959137
theorem B1741495 : Blo 1375507 1741495 := bstep (se 1 (by rfl) ⟨1306121, by rfl⟩ : syracuseStep 1741495 = 2612243) B2612243
theorem B2323127 : Blo 1375507 2323127 := bstep (se 1 (by rfl) ⟨1742345, by rfl⟩ : syracuseStep 2323127 = 3484691) B3484691
theorem B3486635 : Blo 1375507 3486635 := bstep (se 1 (by rfl) ⟨2614976, by rfl⟩ : syracuseStep 3486635 = 5229953) B5229953
theorem B11162569 : Blo 1375507 11162569 := bstep (se 2 (by rfl) ⟨4185963, by rfl⟩ : syracuseStep 11162569 = 8371927) B8371927
theorem B2479079 : Blo 1375507 2479079 := bstep (se 1 (by rfl) ⟨1859309, by rfl⟩ : syracuseStep 2479079 = 3718619) B3718619
theorem B18363671 : Blo 1375507 18363671 := bstep (se 1 (by rfl) ⟨13772753, by rfl⟩ : syracuseStep 18363671 = 27545507) B27545507
theorem B5879135 : Blo 1375507 5879135 := bstep (se 1 (by rfl) ⟨4409351, by rfl⟩ : syracuseStep 5879135 = 8818703) B8818703
theorem B2323849 : Blo 1375507 2323849 := bstep (se 2 (by rfl) ⟨871443, by rfl⟩ : syracuseStep 2323849 = 1742887) B1742887
theorem B3307321 : Blo 1375507 3307321 := bstep (se 2 (by rfl) ⟨1240245, by rfl⟩ : syracuseStep 3307321 = 2480491) B2480491
theorem B2324281 : Blo 1375507 2324281 := bstep (se 2 (by rfl) ⟨871605, by rfl⟩ : syracuseStep 2324281 = 1743211) B1743211
theorem B5879735 : Blo 1375507 5879735 := bstep (se 1 (by rfl) ⟨4409801, by rfl⟩ : syracuseStep 5879735 = 8819603) B8819603
theorem B18823099 : Blo 1375507 18823099 := bstep (se 1 (by rfl) ⟨14117324, by rfl⟩ : syracuseStep 18823099 = 28234649) B28234649
theorem B11155591 : Blo 1375507 11155591 := bstep (se 1 (by rfl) ⟨8366693, by rfl⟩ : syracuseStep 11155591 = 16733387) B16733387
theorem B4643081 : Blo 1375507 4643081 := bstep (se 2 (by rfl) ⟨1741155, by rfl⟩ : syracuseStep 4643081 = 3482311) B3482311
theorem B19855691 : Blo 1375507 19855691 := bstep (se 1 (by rfl) ⟨14891768, by rfl⟩ : syracuseStep 19855691 = 29783537) B29783537
theorem B6969725 : Blo 1375507 6969725 := bstep (se 3 (by rfl) ⟨1306823, by rfl⟩ : syracuseStep 6969725 = 2613647) B2613647
theorem B7436717 : Blo 1375507 7436717 := bstep (se 3 (by rfl) ⟨1394384, by rfl⟩ : syracuseStep 7436717 = 2788769) B2788769
theorem B3095009 : Blo 1375507 3095009 := bstep (se 2 (by rfl) ⟨1160628, by rfl⟩ : syracuseStep 3095009 = 2321257) B2321257
theorem B2480635 : Blo 1375507 2480635 := bstep (se 1 (by rfl) ⟨1860476, by rfl⟩ : syracuseStep 2480635 = 3720953) B3720953
theorem B10598951 : Blo 1375507 10598951 := bstep (se 1 (by rfl) ⟨7949213, by rfl⟩ : syracuseStep 10598951 = 15898427) B15898427
theorem B2513479 : Blo 1375507 2513479 := bstep (se 1 (by rfl) ⟨1885109, by rfl⟩ : syracuseStep 2513479 = 3770219) B3770219
theorem B2939465 : Blo 1375507 2939465 := bstep (se 2 (by rfl) ⟨1102299, by rfl⟩ : syracuseStep 2939465 = 2204599) B2204599
theorem B3095315 : Blo 1375507 3095315 := bstep (se 1 (by rfl) ⟨2321486, by rfl⟩ : syracuseStep 3095315 = 4642973) B4642973
theorem B7945147 : Blo 1375507 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B3095675 : Blo 1375507 3095675 := bstep (se 1 (by rfl) ⟨2321756, by rfl⟩ : syracuseStep 3095675 = 4643513) B4643513
theorem B7445627 : Blo 1375507 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B5299339 : Blo 1375507 5299339 := bstep (se 1 (by rfl) ⟨3974504, by rfl⟩ : syracuseStep 5299339 = 7949009) B7949009
theorem B2063579 : Blo 1375507 2063579 := bstep (se 1 (by rfl) ⟨1547684, by rfl⟩ : syracuseStep 2063579 = 3095369) B3095369
theorem B3095801 : Blo 1375507 3095801 := bstep (se 2 (by rfl) ⟨1160925, by rfl⟩ : syracuseStep 3095801 = 2321851) B2321851
theorem B1375519 : Blo 1375507 1375519 := bstep (se 1 (by rfl) ⟨1031639, by rfl⟩ : syracuseStep 1375519 = 2063279) B2063279
theorem B6806851 : Blo 1375507 6806851 := bstep (se 1 (by rfl) ⟨5105138, by rfl⟩ : syracuseStep 6806851 = 10210277) B10210277
theorem B1375579 : Blo 1375507 1375579 := bstep (se 1 (by rfl) ⟨1031684, by rfl⟩ : syracuseStep 1375579 = 2063369) B2063369
theorem B3308897 : Blo 1375507 3308897 := bstep (se 2 (by rfl) ⟨1240836, by rfl⟩ : syracuseStep 3308897 = 2481673) B2481673
theorem B1375599 : Blo 1375507 1375599 := bstep (se 1 (by rfl) ⟨1031699, by rfl⟩ : syracuseStep 1375599 = 2063399) B2063399
theorem B4644215 : Blo 1375507 4644215 := bstep (se 1 (by rfl) ⟨3483161, by rfl⟩ : syracuseStep 4644215 = 6966323) B6966323
theorem B2063753 : Blo 1375507 2063753 := bstep (se 2 (by rfl) ⟨773907, by rfl⟩ : syracuseStep 2063753 = 1547815) B1547815
theorem B3095945 : Blo 1375507 3095945 := bstep (se 2 (by rfl) ⟨1160979, by rfl⟩ : syracuseStep 3095945 = 2321959) B2321959
theorem B1375655 : Blo 1375507 1375655 := bstep (se 1 (by rfl) ⟨1031741, by rfl⟩ : syracuseStep 1375655 = 2063483) B2063483
theorem B2612729 : Blo 1375507 2612729 := bstep (se 2 (by rfl) ⟨979773, by rfl⟩ : syracuseStep 2612729 = 1959547) B1959547
theorem B1375739 : Blo 1375507 1375739 := bstep (se 1 (by rfl) ⟨1031804, by rfl⟩ : syracuseStep 1375739 = 2063609) B2063609
theorem B3096071 : Blo 1375507 3096071 := bstep (se 1 (by rfl) ⟨2322053, by rfl⟩ : syracuseStep 3096071 = 4644107) B4644107
theorem B1375807 : Blo 1375507 1375807 := bstep (se 1 (by rfl) ⟨1031855, by rfl⟩ : syracuseStep 1375807 = 2063711) B2063711
theorem B1375815 : Blo 1375507 1375815 := bstep (se 1 (by rfl) ⟨1031861, by rfl⟩ : syracuseStep 1375815 = 2063723) B2063723
theorem B5226065 : Blo 1375507 5226065 := bstep (se 2 (by rfl) ⟨1959774, by rfl⟩ : syracuseStep 5226065 = 3919549) B3919549
theorem B5226079 : Blo 1375507 5226079 := bstep (se 1 (by rfl) ⟨3919559, by rfl⟩ : syracuseStep 5226079 = 7839119) B7839119
theorem B3096251 : Blo 1375507 3096251 := bstep (se 1 (by rfl) ⟨2322188, by rfl⟩ : syracuseStep 3096251 = 4644377) B4644377
theorem B1375967 : Blo 1375507 1375967 := bstep (se 1 (by rfl) ⟨1031975, by rfl⟩ : syracuseStep 1375967 = 2063951) B2063951
theorem B2064107 : Blo 1375507 2064107 := bstep (se 1 (by rfl) ⟨1548080, by rfl⟩ : syracuseStep 2064107 = 3096161) B3096161
theorem B7446275 : Blo 1375507 7446275 := bstep (se 1 (by rfl) ⟨5584706, by rfl⟩ : syracuseStep 7446275 = 11169413) B11169413
theorem B1376047 : Blo 1375507 1376047 := bstep (se 1 (by rfl) ⟨1032035, by rfl⟩ : syracuseStep 1376047 = 2064071) B2064071
theorem B6971183 : Blo 1375507 6971183 := bstep (se 1 (by rfl) ⟨5228387, by rfl⟩ : syracuseStep 6971183 = 10456775) B10456775
theorem B3096377 : Blo 1375507 3096377 := bstep (se 2 (by rfl) ⟨1161141, by rfl⟩ : syracuseStep 3096377 = 2322283) B2322283
theorem B37674881 : Blo 1375507 37674881 := bstep (se 2 (by rfl) ⟨14128080, by rfl⟩ : syracuseStep 37674881 = 28256161) B28256161
theorem B42983297 : Blo 1375507 42983297 := bstep (se 2 (by rfl) ⟨16118736, by rfl⟩ : syracuseStep 42983297 = 32237473) B32237473
theorem B1376155 : Blo 1375507 1376155 := bstep (se 1 (by rfl) ⟨1032116, by rfl⟩ : syracuseStep 1376155 = 2064233) B2064233
theorem B1376207 : Blo 1375507 1376207 := bstep (se 1 (by rfl) ⟨1032155, by rfl⟩ : syracuseStep 1376207 = 2064311) B2064311
theorem B2064335 : Blo 1375507 2064335 := bstep (se 1 (by rfl) ⟨1548251, by rfl⟩ : syracuseStep 2064335 = 3096503) B3096503
theorem B1376231 : Blo 1375507 1376231 := bstep (se 1 (by rfl) ⟨1032173, by rfl⟩ : syracuseStep 1376231 = 2064347) B2064347
theorem B11763737 : Blo 1375507 11763737 := bstep (se 2 (by rfl) ⟨4411401, by rfl⟩ : syracuseStep 11763737 = 8822803) B8822803
theorem B21184723 : Blo 1375507 21184723 := bstep (se 1 (by rfl) ⟨15888542, by rfl⟩ : syracuseStep 21184723 = 31777085) B31777085
theorem B1376487 : Blo 1375507 1376487 := bstep (se 1 (by rfl) ⟨1032365, by rfl⟩ : syracuseStep 1376487 = 2064731) B2064731
theorem B16736503 : Blo 1375507 16736503 := bstep (se 1 (by rfl) ⟨12552377, by rfl⟩ : syracuseStep 16736503 = 25104755) B25104755
theorem B3096863 : Blo 1375507 3096863 := bstep (se 1 (by rfl) ⟨2322647, by rfl⟩ : syracuseStep 3096863 = 4645295) B4645295
theorem B2064671 : Blo 1375507 2064671 := bstep (se 1 (by rfl) ⟨1548503, by rfl⟩ : syracuseStep 2064671 = 3097007) B3097007
theorem B2064695 : Blo 1375507 2064695 := bstep (se 1 (by rfl) ⟨1548521, by rfl⟩ : syracuseStep 2064695 = 3097043) B3097043
theorem B2064767 : Blo 1375507 2064767 := bstep (se 1 (by rfl) ⟨1548575, by rfl⟩ : syracuseStep 2064767 = 3097151) B3097151
theorem B1376639 : Blo 1375507 1376639 := bstep (se 1 (by rfl) ⟨1032479, by rfl⟩ : syracuseStep 1376639 = 2064959) B2064959
theorem B2064839 : Blo 1375507 2064839 := bstep (se 1 (by rfl) ⟨1548629, by rfl⟩ : syracuseStep 2064839 = 3097259) B3097259
theorem B1548751 : Blo 1375507 1548751 := bstep (se 1 (by rfl) ⟨1161563, by rfl⟩ : syracuseStep 1548751 = 2323127) B2323127
theorem B1376719 : Blo 1375507 1376719 := bstep (se 1 (by rfl) ⟨1032539, by rfl⟩ : syracuseStep 1376719 = 2065079) B2065079
theorem B1376871 : Blo 1375507 1376871 := bstep (se 1 (by rfl) ⟨1032653, by rfl⟩ : syracuseStep 1376871 = 2065307) B2065307
theorem B3719915 : Blo 1375507 3719915 := bstep (se 1 (by rfl) ⟨2789936, by rfl⟩ : syracuseStep 3719915 = 5579873) B5579873
theorem B3351305 : Blo 1375507 3351305 := bstep (se 2 (by rfl) ⟨1256739, by rfl⟩ : syracuseStep 3351305 = 2513479) B2513479
theorem B2065193 : Blo 1375507 2065193 := bstep (se 2 (by rfl) ⟨774447, by rfl⟩ : syracuseStep 2065193 = 1548895) B1548895
theorem B2065199 : Blo 1375507 2065199 := bstep (se 1 (by rfl) ⟨1548899, by rfl⟩ : syracuseStep 2065199 = 3097799) B3097799
theorem B4408121 : Blo 1375507 4408121 := bstep (se 2 (by rfl) ⟨1653045, by rfl⟩ : syracuseStep 4408121 = 3306091) B3306091
theorem B1377135 : Blo 1375507 1377135 := bstep (se 1 (by rfl) ⟨1032851, by rfl⟩ : syracuseStep 1377135 = 2065703) B2065703
theorem B3097511 : Blo 1375507 3097511 := bstep (se 1 (by rfl) ⟨2323133, by rfl⟩ : syracuseStep 3097511 = 4646267) B4646267
theorem B2065319 : Blo 1375507 2065319 := bstep (se 1 (by rfl) ⟨1548989, by rfl⟩ : syracuseStep 2065319 = 3097979) B3097979
theorem B1377191 : Blo 1375507 1377191 := bstep (se 1 (by rfl) ⟨1032893, by rfl⟩ : syracuseStep 1377191 = 2065787) B2065787
theorem B8823725 : Blo 1375507 8823725 := bstep (se 3 (by rfl) ⟨1654448, by rfl⟩ : syracuseStep 8823725 = 3308897) B3308897
theorem B2065403 : Blo 1375507 2065403 := bstep (se 1 (by rfl) ⟨1549052, by rfl⟩ : syracuseStep 2065403 = 3098105) B3098105
theorem B1377275 : Blo 1375507 1377275 := bstep (se 1 (by rfl) ⟨1032956, by rfl⟩ : syracuseStep 1377275 = 2065913) B2065913
theorem B2065463 : Blo 1375507 2065463 := bstep (se 1 (by rfl) ⟨1549097, by rfl⟩ : syracuseStep 2065463 = 3098195) B3098195
theorem B1377343 : Blo 1375507 1377343 := bstep (se 1 (by rfl) ⟨1033007, by rfl⟩ : syracuseStep 1377343 = 2066015) B2066015
theorem B2065583 : Blo 1375507 2065583 := bstep (se 1 (by rfl) ⟨1549187, by rfl⟩ : syracuseStep 2065583 = 3098375) B3098375
theorem B1377487 : Blo 1375507 1377487 := bstep (se 1 (by rfl) ⟨1033115, by rfl⟩ : syracuseStep 1377487 = 2066231) B2066231
theorem B10593529 : Blo 1375507 10593529 := bstep (se 2 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 10593529 = 7945147) B7945147
theorem B145212821 : Blo 1375507 145212821 := bstep (se 6 (by rfl) ⟨3403425, by rfl⟩ : syracuseStep 145212821 = 6806851) B6806851
theorem B2065991 : Blo 1375507 2065991 := bstep (se 1 (by rfl) ⟨1549493, by rfl⟩ : syracuseStep 2065991 = 3098987) B3098987
theorem B4646483 : Blo 1375507 4646483 := bstep (se 1 (by rfl) ⟨3484862, by rfl⟩ : syracuseStep 4646483 = 6969725) B6969725
theorem B4957811 : Blo 1375507 4957811 := bstep (se 1 (by rfl) ⟨3718358, by rfl⟩ : syracuseStep 4957811 = 7436717) B7436717
theorem B17639045 : Blo 1375507 17639045 := bstep (se 4 (by rfl) ⟨1653660, by rfl⟩ : syracuseStep 17639045 = 3307321) B3307321
theorem B2066087 : Blo 1375507 2066087 := bstep (se 1 (by rfl) ⟨1549565, by rfl⟩ : syracuseStep 2066087 = 3099131) B3099131
theorem B1959643 : Blo 1375507 1959643 := bstep (se 1 (by rfl) ⟨1469732, by rfl⟩ : syracuseStep 1959643 = 2939465) B2939465
theorem B2066171 : Blo 1375507 2066171 := bstep (se 1 (by rfl) ⟨1549628, by rfl⟩ : syracuseStep 2066171 = 3099257) B3099257
theorem B4409095 : Blo 1375507 4409095 := bstep (se 1 (by rfl) ⟨3306821, by rfl⟩ : syracuseStep 4409095 = 6613643) B6613643
theorem B2066207 : Blo 1375507 2066207 := bstep (se 1 (by rfl) ⟨1549655, by rfl⟩ : syracuseStep 2066207 = 3099311) B3099311
theorem B19842893 : Blo 1375507 19842893 := bstep (se 3 (by rfl) ⟨3720542, by rfl⟩ : syracuseStep 19842893 = 7441085) B7441085
theorem B3098447 : Blo 1375507 3098447 := bstep (se 1 (by rfl) ⟨2323835, by rfl⟩ : syracuseStep 3098447 = 4647671) B4647671
theorem B2066255 : Blo 1375507 2066255 := bstep (se 1 (by rfl) ⟨1549691, by rfl⟩ : syracuseStep 2066255 = 3099383) B3099383
theorem B4646753 : Blo 1375507 4646753 := bstep (se 2 (by rfl) ⟨1742532, by rfl⟩ : syracuseStep 4646753 = 3485065) B3485065
theorem B3098465 : Blo 1375507 3098465 := bstep (se 2 (by rfl) ⟨1161924, by rfl⟩ : syracuseStep 3098465 = 2323849) B2323849
theorem B3484043 : Blo 1375507 3484043 := bstep (se 1 (by rfl) ⟨2613032, by rfl⟩ : syracuseStep 3484043 = 5226065) B5226065
theorem B3099041 : Blo 1375507 3099041 := bstep (se 2 (by rfl) ⟨1162140, by rfl⟩ : syracuseStep 3099041 = 2324281) B2324281
theorem B20122037 : Blo 1375507 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B4647455 : Blo 1375507 4647455 := bstep (se 1 (by rfl) ⟨3485591, by rfl⟩ : syracuseStep 4647455 = 6971183) B6971183
theorem B3099167 : Blo 1375507 3099167 := bstep (se 1 (by rfl) ⟨2324375, by rfl⟩ : syracuseStep 3099167 = 4648751) B4648751
theorem B2091625 : Blo 1375507 2091625 := bstep (se 2 (by rfl) ⟨784359, by rfl⟩ : syracuseStep 2091625 = 1568719) B1568719
theorem B2321311 : Blo 1375507 2321311 := bstep (se 1 (by rfl) ⟨1740983, by rfl⟩ : syracuseStep 2321311 = 3481967) B3481967
theorem B50244533 : Blo 1375507 50244533 := bstep (se 5 (by rfl) ⟨2355212, by rfl⟩ : syracuseStep 50244533 = 4710425) B4710425
theorem B5876675 : Blo 1375507 5876675 := bstep (se 1 (by rfl) ⟨4407506, by rfl⟩ : syracuseStep 5876675 = 8815013) B8815013
theorem B33959083 : Blo 1375507 33959083 := bstep (se 1 (by rfl) ⟨25469312, by rfl⟩ : syracuseStep 33959083 = 50938625) B50938625
theorem B2321743 : Blo 1375507 2321743 := bstep (se 1 (by rfl) ⟨1741307, by rfl⟩ : syracuseStep 2321743 = 3482615) B3482615
theorem B2321831 : Blo 1375507 2321831 := bstep (se 1 (by rfl) ⟨1741373, by rfl⟩ : syracuseStep 2321831 = 3482747) B3482747
theorem B12242447 : Blo 1375507 12242447 := bstep (se 1 (by rfl) ⟨9181835, by rfl⟩ : syracuseStep 12242447 = 18363671) B18363671
theorem B3919423 : Blo 1375507 3919423 := bstep (se 1 (by rfl) ⟨2939567, by rfl⟩ : syracuseStep 3919423 = 5879135) B5879135
theorem B2321993 : Blo 1375507 2321993 := bstep (se 2 (by rfl) ⟨870747, by rfl⟩ : syracuseStep 2321993 = 1741495) B1741495
theorem B8818577 : Blo 1375507 8818577 := bstep (se 2 (by rfl) ⟨3306966, by rfl⟩ : syracuseStep 8818577 = 6613933) B6613933
theorem B4648859 : Blo 1375507 4648859 := bstep (se 1 (by rfl) ⟨3486644, by rfl⟩ : syracuseStep 4648859 = 6973289) B6973289
theorem B42389405 : Blo 1375507 42389405 := bstep (se 3 (by rfl) ⟨7948013, by rfl⟩ : syracuseStep 42389405 = 15896027) B15896027
theorem B63549359 : Blo 1375507 63549359 := bstep (se 1 (by rfl) ⟨47662019, by rfl⟩ : syracuseStep 63549359 = 95324039) B95324039
theorem B3919823 : Blo 1375507 3919823 := bstep (se 1 (by rfl) ⟨2939867, by rfl⟩ : syracuseStep 3919823 = 5879735) B5879735
theorem B3485663 : Blo 1375507 3485663 := bstep (se 1 (by rfl) ⟨2614247, by rfl⟩ : syracuseStep 3485663 = 5228495) B5228495
theorem B4960379 : Blo 1375507 4960379 := bstep (se 1 (by rfl) ⟨3720284, by rfl⟩ : syracuseStep 4960379 = 7440569) B7440569
theorem B7065785 : Blo 1375507 7065785 := bstep (se 2 (by rfl) ⟨2649669, by rfl⟩ : syracuseStep 7065785 = 5299339) B5299339
theorem B7065967 : Blo 1375507 7065967 := bstep (se 1 (by rfl) ⟨5299475, by rfl⟩ : syracuseStep 7065967 = 10598951) B10598951
theorem B4963751 : Blo 1375507 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B2978387 : Blo 1375507 2978387 := bstep (se 1 (by rfl) ⟨2233790, by rfl⟩ : syracuseStep 2978387 = 4467581) B4467581
theorem B2323039 : Blo 1375507 2323039 := bstep (se 1 (by rfl) ⟨1742279, by rfl⟩ : syracuseStep 2323039 = 3484559) B3484559
theorem B3486311 : Blo 1375507 3486311 := bstep (se 1 (by rfl) ⟨2614733, by rfl⟩ : syracuseStep 3486311 = 5229467) B5229467
theorem B6968105 : Blo 1375507 6968105 := bstep (se 2 (by rfl) ⟨2613039, by rfl⟩ : syracuseStep 6968105 = 5226079) B5226079
theorem B1741819 : Blo 1375507 1741819 := bstep (se 1 (by rfl) ⟨1306364, by rfl⟩ : syracuseStep 1741819 = 2612729) B2612729
theorem B2323451 : Blo 1375507 2323451 := bstep (se 1 (by rfl) ⟨1742588, by rfl⟩ : syracuseStep 2323451 = 3485177) B3485177
theorem B3306707 : Blo 1375507 3306707 := bstep (se 1 (by rfl) ⟨2480030, by rfl⟩ : syracuseStep 3306707 = 4960061) B4960061
theorem B25097465 : Blo 1375507 25097465 := bstep (se 2 (by rfl) ⟨9411549, by rfl⟩ : syracuseStep 25097465 = 18823099) B18823099
theorem B12555557 : Blo 1375507 12555557 := bstep (se 4 (by rfl) ⟨1177083, by rfl⟩ : syracuseStep 12555557 = 2354167) B2354167
theorem B5879101 : Blo 1375507 5879101 := bstep (se 3 (by rfl) ⟨1102331, by rfl⟩ : syracuseStep 5879101 = 2204663) B2204663
theorem B7443809 : Blo 1375507 7443809 := bstep (se 2 (by rfl) ⟨2791428, by rfl⟩ : syracuseStep 7443809 = 5582857) B5582857
theorem B5584283 : Blo 1375507 5584283 := bstep (se 1 (by rfl) ⟨4188212, by rfl⟩ : syracuseStep 5584283 = 8376425) B8376425
theorem B2323883 : Blo 1375507 2323883 := bstep (se 1 (by rfl) ⟨1742912, by rfl⟩ : syracuseStep 2323883 = 3485825) B3485825
theorem B14874121 : Blo 1375507 14874121 := bstep (se 2 (by rfl) ⟨5577795, by rfl⟩ : syracuseStep 14874121 = 11155591) B11155591
theorem B1570471 : Blo 1375507 1570471 := bstep (se 1 (by rfl) ⟨1177853, by rfl⟩ : syracuseStep 1570471 = 2355707) B2355707
theorem B4642487 : Blo 1375507 4642487 := bstep (se 1 (by rfl) ⟨3481865, by rfl⟩ : syracuseStep 4642487 = 6963731) B6963731
theorem B1742791 : Blo 1375507 1742791 := bstep (se 1 (by rfl) ⟨1307093, by rfl⟩ : syracuseStep 1742791 = 2614187) B2614187
theorem B2324423 : Blo 1375507 2324423 := bstep (se 1 (by rfl) ⟨1743317, by rfl⟩ : syracuseStep 2324423 = 3486635) B3486635
theorem B1652719 : Blo 1375507 1652719 := bstep (se 1 (by rfl) ⟨1239539, by rfl⟩ : syracuseStep 1652719 = 2479079) B2479079
theorem B4470809 : Blo 1375507 4470809 := bstep (se 2 (by rfl) ⟨1676553, by rfl⟩ : syracuseStep 4470809 = 3353107) B3353107
theorem B3922283 : Blo 1375507 3922283 := bstep (se 1 (by rfl) ⟨2941712, by rfl⟩ : syracuseStep 3922283 = 5883425) B5883425
theorem B50207165 : Blo 1375507 50207165 := bstep (se 3 (by rfl) ⟨9413843, by rfl⟩ : syracuseStep 50207165 = 18827687) B18827687
theorem B72456677 : Blo 1375507 72456677 := bstep (se 4 (by rfl) ⟨6792813, by rfl⟩ : syracuseStep 72456677 = 13585627) B13585627
theorem B14883425 : Blo 1375507 14883425 := bstep (se 2 (by rfl) ⟨5581284, by rfl⟩ : syracuseStep 14883425 = 11162569) B11162569
theorem B8813245 : Blo 1375507 8813245 := bstep (se 3 (by rfl) ⟨1652483, by rfl⟩ : syracuseStep 8813245 = 3304967) B3304967
theorem B3095387 : Blo 1375507 3095387 := bstep (se 1 (by rfl) ⟨2321540, by rfl⟩ : syracuseStep 3095387 = 4643081) B4643081
theorem B4643675 : Blo 1375507 4643675 := bstep (se 1 (by rfl) ⟨3482756, by rfl⟩ : syracuseStep 4643675 = 6965513) B6965513
theorem B13237127 : Blo 1375507 13237127 := bstep (se 1 (by rfl) ⟨9927845, by rfl⟩ : syracuseStep 13237127 = 19855691) B19855691
theorem B2939807 : Blo 1375507 2939807 := bstep (se 1 (by rfl) ⟨2204855, by rfl⟩ : syracuseStep 2939807 = 4409711) B4409711
theorem B2063339 : Blo 1375507 2063339 := bstep (se 1 (by rfl) ⟨1547504, by rfl⟩ : syracuseStep 2063339 = 3095009) B3095009
theorem B2063543 : Blo 1375507 2063543 := bstep (se 1 (by rfl) ⟨1547657, by rfl⟩ : syracuseStep 2063543 = 3095315) B3095315
theorem B1547599 : Blo 1375507 1547599 := bstep (se 1 (by rfl) ⟨1160699, by rfl⟩ : syracuseStep 1547599 = 2321399) B2321399
theorem B4709771 : Blo 1375507 4709771 := bstep (se 1 (by rfl) ⟨3532328, by rfl⟩ : syracuseStep 4709771 = 7064657) B7064657
theorem B2063783 : Blo 1375507 2063783 := bstep (se 1 (by rfl) ⟨1547837, by rfl⟩ : syracuseStep 2063783 = 3095675) B3095675
theorem B16752071 : Blo 1375507 16752071 := bstep (se 1 (by rfl) ⟨12564053, by rfl⟩ : syracuseStep 16752071 = 25128107) B25128107
theorem B2940371 : Blo 1375507 2940371 := bstep (se 1 (by rfl) ⟨2205278, by rfl⟩ : syracuseStep 2940371 = 4410557) B4410557
theorem B1375719 : Blo 1375507 1375719 := bstep (se 1 (by rfl) ⟨1031789, by rfl⟩ : syracuseStep 1375719 = 2063579) B2063579
theorem B2063867 : Blo 1375507 2063867 := bstep (se 1 (by rfl) ⟨1547900, by rfl⟩ : syracuseStep 2063867 = 3095801) B3095801
theorem B3096143 : Blo 1375507 3096143 := bstep (se 1 (by rfl) ⟨2322107, by rfl⟩ : syracuseStep 3096143 = 4644215) B4644215
theorem B4644431 : Blo 1375507 4644431 := bstep (se 1 (by rfl) ⟨3483323, by rfl⟩ : syracuseStep 4644431 = 6966647) B6966647
theorem B1375835 : Blo 1375507 1375835 := bstep (se 1 (by rfl) ⟨1031876, by rfl⟩ : syracuseStep 1375835 = 2063753) B2063753
theorem B2063963 : Blo 1375507 2063963 := bstep (se 1 (by rfl) ⟨1547972, by rfl⟩ : syracuseStep 2063963 = 3095945) B3095945
theorem B2612827 : Blo 1375507 2612827 := bstep (se 1 (by rfl) ⟨1959620, by rfl⟩ : syracuseStep 2612827 = 3919241) B3919241
theorem B2064047 : Blo 1375507 2064047 := bstep (se 1 (by rfl) ⟨1548035, by rfl⟩ : syracuseStep 2064047 = 3096071) B3096071
theorem B4644539 : Blo 1375507 4644539 := bstep (se 1 (by rfl) ⟨3483404, by rfl⟩ : syracuseStep 4644539 = 6966809) B6966809
theorem B2064167 : Blo 1375507 2064167 := bstep (se 1 (by rfl) ⟨1548125, by rfl⟩ : syracuseStep 2064167 = 3096251) B3096251
theorem B1376071 : Blo 1375507 1376071 := bstep (se 1 (by rfl) ⟨1032053, by rfl⟩ : syracuseStep 1376071 = 2064107) B2064107
theorem B1548103 : Blo 1375507 1548103 := bstep (se 1 (by rfl) ⟨1161077, by rfl⟩ : syracuseStep 1548103 = 2322155) B2322155
theorem B4964183 : Blo 1375507 4964183 := bstep (se 1 (by rfl) ⟨3723137, by rfl⟩ : syracuseStep 4964183 = 7446275) B7446275
theorem B2064251 : Blo 1375507 2064251 := bstep (se 1 (by rfl) ⟨1548188, by rfl⟩ : syracuseStep 2064251 = 3096377) B3096377
theorem B25116587 : Blo 1375507 25116587 := bstep (se 1 (by rfl) ⟨18837440, by rfl⟩ : syracuseStep 25116587 = 37674881) B37674881
theorem B28655531 : Blo 1375507 28655531 := bstep (se 1 (by rfl) ⟨21491648, by rfl⟩ : syracuseStep 28655531 = 42983297) B42983297
theorem B1376223 : Blo 1375507 1376223 := bstep (se 1 (by rfl) ⟨1032167, by rfl⟩ : syracuseStep 1376223 = 2064335) B2064335
theorem B13230053 : Blo 1375507 13230053 := bstep (se 4 (by rfl) ⟨1240317, by rfl⟩ : syracuseStep 13230053 = 2480635) B2480635
theorem B4710523 : Blo 1375507 4710523 := bstep (se 1 (by rfl) ⟨3532892, by rfl⟩ : syracuseStep 4710523 = 7065785) B7065785
theorem B2064575 : Blo 1375507 2064575 := bstep (se 1 (by rfl) ⟨1548431, by rfl⟩ : syracuseStep 2064575 = 3096863) B3096863
theorem B1376447 : Blo 1375507 1376447 := bstep (se 1 (by rfl) ⟨1032335, by rfl⟩ : syracuseStep 1376447 = 2064671) B2064671
theorem B1376463 : Blo 1375507 1376463 := bstep (se 1 (by rfl) ⟨1032347, by rfl⟩ : syracuseStep 1376463 = 2064695) B2064695
theorem B1376511 : Blo 1375507 1376511 := bstep (se 1 (by rfl) ⟨1032383, by rfl⟩ : syracuseStep 1376511 = 2064767) B2064767
theorem B1376559 : Blo 1375507 1376559 := bstep (se 1 (by rfl) ⟨1032419, by rfl⟩ : syracuseStep 1376559 = 2064839) B2064839
theorem B22315337 : Blo 1375507 22315337 := bstep (se 2 (by rfl) ⟨8368251, by rfl⟩ : syracuseStep 22315337 = 16736503) B16736503
theorem B9421289 : Blo 1375507 9421289 := bstep (se 2 (by rfl) ⟨3532983, by rfl⟩ : syracuseStep 9421289 = 7065967) B7065967
theorem B4645403 : Blo 1375507 4645403 := bstep (se 1 (by rfl) ⟨3484052, by rfl⟩ : syracuseStep 4645403 = 6968105) B6968105
theorem B1376795 : Blo 1375507 1376795 := bstep (se 1 (by rfl) ⟨1032596, by rfl⟩ : syracuseStep 1376795 = 2065193) B2065193
theorem B1376799 : Blo 1375507 1376799 := bstep (se 1 (by rfl) ⟨1032599, by rfl⟩ : syracuseStep 1376799 = 2065199) B2065199
theorem B2065001 : Blo 1375507 2065001 := bstep (se 2 (by rfl) ⟨774375, by rfl⟩ : syracuseStep 2065001 = 1548751) B1548751
theorem B2065007 : Blo 1375507 2065007 := bstep (se 1 (by rfl) ⟨1548755, by rfl⟩ : syracuseStep 2065007 = 3097511) B3097511
theorem B1376879 : Blo 1375507 1376879 := bstep (se 1 (by rfl) ⟨1032659, by rfl⟩ : syracuseStep 1376879 = 2065319) B2065319
theorem B5882483 : Blo 1375507 5882483 := bstep (se 1 (by rfl) ⟨4411862, by rfl⟩ : syracuseStep 5882483 = 8823725) B8823725
theorem B1548967 : Blo 1375507 1548967 := bstep (se 1 (by rfl) ⟨1161725, by rfl⟩ : syracuseStep 1548967 = 2323451) B2323451
theorem B1376935 : Blo 1375507 1376935 := bstep (se 1 (by rfl) ⟨1032701, by rfl⟩ : syracuseStep 1376935 = 2065403) B2065403
theorem B1376975 : Blo 1375507 1376975 := bstep (se 1 (by rfl) ⟨1032731, by rfl⟩ : syracuseStep 1376975 = 2065463) B2065463
theorem B1377055 : Blo 1375507 1377055 := bstep (se 1 (by rfl) ⟨1032791, by rfl⟩ : syracuseStep 1377055 = 2065583) B2065583
theorem B3097385 : Blo 1375507 3097385 := bstep (se 2 (by rfl) ⟨1161519, by rfl⟩ : syracuseStep 3097385 = 2323039) B2323039
theorem B2204471 : Blo 1375507 2204471 := bstep (se 1 (by rfl) ⟨1653353, by rfl⟩ : syracuseStep 2204471 = 3306707) B3306707
theorem B1549255 : Blo 1375507 1549255 := bstep (se 1 (by rfl) ⟨1161941, by rfl⟩ : syracuseStep 1549255 = 2323883) B2323883
theorem B1377327 : Blo 1375507 1377327 := bstep (se 1 (by rfl) ⟨1032995, by rfl⟩ : syracuseStep 1377327 = 2065991) B2065991
theorem B3097655 : Blo 1375507 3097655 := bstep (se 1 (by rfl) ⟨2323241, by rfl⟩ : syracuseStep 3097655 = 4646483) B4646483
theorem B112985189 : Blo 1375507 112985189 := bstep (se 4 (by rfl) ⟨10592361, by rfl⟩ : syracuseStep 112985189 = 21184723) B21184723
theorem B1377391 : Blo 1375507 1377391 := bstep (se 1 (by rfl) ⟨1033043, by rfl⟩ : syracuseStep 1377391 = 2066087) B2066087
theorem B1377447 : Blo 1375507 1377447 := bstep (se 1 (by rfl) ⟨1033085, by rfl⟩ : syracuseStep 1377447 = 2066171) B2066171
theorem B1377471 : Blo 1375507 1377471 := bstep (se 1 (by rfl) ⟨1033103, by rfl⟩ : syracuseStep 1377471 = 2066207) B2066207
theorem B2065631 : Blo 1375507 2065631 := bstep (se 1 (by rfl) ⟨1549223, by rfl⟩ : syracuseStep 2065631 = 3098447) B3098447
theorem B1377503 : Blo 1375507 1377503 := bstep (se 1 (by rfl) ⟨1033127, by rfl⟩ : syracuseStep 1377503 = 2066255) B2066255
theorem B3097835 : Blo 1375507 3097835 := bstep (se 1 (by rfl) ⟨2323376, by rfl⟩ : syracuseStep 3097835 = 4646753) B4646753
theorem B2065643 : Blo 1375507 2065643 := bstep (se 1 (by rfl) ⟨1549232, by rfl⟩ : syracuseStep 2065643 = 3098465) B3098465
theorem B1549615 : Blo 1375507 1549615 := bstep (se 1 (by rfl) ⟨1162211, by rfl⟩ : syracuseStep 1549615 = 2324423) B2324423
theorem B45278777 : Blo 1375507 45278777 := bstep (se 2 (by rfl) ⟨16979541, by rfl⟩ : syracuseStep 45278777 = 33959083) B33959083
theorem B2614855 : Blo 1375507 2614855 := bstep (se 1 (by rfl) ⟨1961141, by rfl⟩ : syracuseStep 2614855 = 3922283) B3922283
theorem B2066027 : Blo 1375507 2066027 := bstep (se 1 (by rfl) ⟨1549520, by rfl⟩ : syracuseStep 2066027 = 3099041) B3099041
theorem B3098303 : Blo 1375507 3098303 := bstep (se 1 (by rfl) ⟨2323727, by rfl⟩ : syracuseStep 3098303 = 4647455) B4647455
theorem B2066111 : Blo 1375507 2066111 := bstep (se 1 (by rfl) ⟨1549583, by rfl⟩ : syracuseStep 2066111 = 3099167) B3099167
theorem B9922283 : Blo 1375507 9922283 := bstep (se 1 (by rfl) ⟨7441712, by rfl⟩ : syracuseStep 9922283 = 14883425) B14883425
theorem B8824751 : Blo 1375507 8824751 := bstep (se 1 (by rfl) ⟨6618563, by rfl⟩ : syracuseStep 8824751 = 13237127) B13237127
theorem B1959871 : Blo 1375507 1959871 := bstep (se 1 (by rfl) ⟨1469903, by rfl⟩ : syracuseStep 1959871 = 2939807) B2939807
theorem B3917783 : Blo 1375507 3917783 := bstep (se 1 (by rfl) ⟨2938337, by rfl⟩ : syracuseStep 3917783 = 5876675) B5876675
theorem B3483769 : Blo 1375507 3483769 := bstep (se 2 (by rfl) ⟨1306413, by rfl⟩ : syracuseStep 3483769 = 2612827) B2612827
theorem B3139847 : Blo 1375507 3139847 := bstep (se 1 (by rfl) ⟨2354885, by rfl⟩ : syracuseStep 3139847 = 4709771) B4709771
theorem B11168047 : Blo 1375507 11168047 := bstep (se 1 (by rfl) ⟨8376035, by rfl⟩ : syracuseStep 11168047 = 16752071) B16752071
theorem B1960247 : Blo 1375507 1960247 := bstep (se 1 (by rfl) ⟨1470185, by rfl⟩ : syracuseStep 1960247 = 2940371) B2940371
theorem B8161631 : Blo 1375507 8161631 := bstep (se 1 (by rfl) ⟨6121223, by rfl⟩ : syracuseStep 8161631 = 12242447) B12242447
theorem B225995285 : Blo 1375507 225995285 := bstep (se 6 (by rfl) ⟨5296764, by rfl⟩ : syracuseStep 225995285 = 10593529) B10593529
theorem B3099239 : Blo 1375507 3099239 := bstep (se 1 (by rfl) ⟨2324429, by rfl⟩ : syracuseStep 3099239 = 4648859) B4648859
theorem B7842491 : Blo 1375507 7842491 := bstep (se 1 (by rfl) ⟨5881868, by rfl⟩ : syracuseStep 7842491 = 11763737) B11763737
theorem B11922157 : Blo 1375507 11922157 := bstep (se 3 (by rfl) ⟨2235404, by rfl⟩ : syracuseStep 11922157 = 4470809) B4470809
theorem B1985591 : Blo 1375507 1985591 := bstep (se 1 (by rfl) ⟨1489193, by rfl⟩ : syracuseStep 1985591 = 2978387) B2978387
theorem B16731643 : Blo 1375507 16731643 := bstep (se 1 (by rfl) ⟨12548732, by rfl⟩ : syracuseStep 16731643 = 25097465) B25097465
theorem B8375845 : Blo 1375507 8375845 := bstep (se 4 (by rfl) ⟨785235, by rfl⟩ : syracuseStep 8375845 = 1570471) B1570471
theorem B11750993 : Blo 1375507 11750993 := bstep (se 2 (by rfl) ⟨4406622, by rfl⟩ : syracuseStep 11750993 = 8813245) B8813245
theorem B96808547 : Blo 1375507 96808547 := bstep (se 1 (by rfl) ⟨72606410, by rfl⟩ : syracuseStep 96808547 = 145212821) B145212821
theorem B3722855 : Blo 1375507 3722855 := bstep (se 1 (by rfl) ⟨2792141, by rfl⟩ : syracuseStep 3722855 = 5584283) B5584283
theorem B3305207 : Blo 1375507 3305207 := bstep (se 1 (by rfl) ⟨2478905, by rfl⟩ : syracuseStep 3305207 = 4957811) B4957811
theorem B11759363 : Blo 1375507 11759363 := bstep (se 1 (by rfl) ⟨8819522, by rfl⟩ : syracuseStep 11759363 = 17639045) B17639045
theorem B2322425 : Blo 1375507 2322425 := bstep (se 2 (by rfl) ⟨870909, by rfl⟩ : syracuseStep 2322425 = 1741819) B1741819
theorem B2322695 : Blo 1375507 2322695 := bstep (se 1 (by rfl) ⟨1742021, by rfl⟩ : syracuseStep 2322695 = 3484043) B3484043
theorem B13414691 : Blo 1375507 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B48304451 : Blo 1375507 48304451 := bstep (se 1 (by rfl) ⟨36228338, by rfl⟩ : syracuseStep 48304451 = 72456677) B72456677
theorem B5878793 : Blo 1375507 5878793 := bstep (se 2 (by rfl) ⟨2204547, by rfl⟩ : syracuseStep 5878793 = 4409095) B4409095
theorem B2323721 : Blo 1375507 2323721 := bstep (se 2 (by rfl) ⟨871395, by rfl⟩ : syracuseStep 2323721 = 1742791) B1742791
theorem B5879051 : Blo 1375507 5879051 := bstep (se 1 (by rfl) ⟨4409288, by rfl⟩ : syracuseStep 5879051 = 8818577) B8818577
theorem B28259603 : Blo 1375507 28259603 := bstep (se 1 (by rfl) ⟨21194702, by rfl⟩ : syracuseStep 28259603 = 42389405) B42389405
theorem B42366239 : Blo 1375507 42366239 := bstep (se 1 (by rfl) ⟨31774679, by rfl⟩ : syracuseStep 42366239 = 63549359) B63549359
theorem B2323775 : Blo 1375507 2323775 := bstep (se 1 (by rfl) ⟨1742831, by rfl⟩ : syracuseStep 2323775 = 3485663) B3485663
theorem B8820035 : Blo 1375507 8820035 := bstep (se 1 (by rfl) ⟨6615026, by rfl⟩ : syracuseStep 8820035 = 13230053) B13230053
theorem B3306919 : Blo 1375507 3306919 := bstep (se 1 (by rfl) ⟨2480189, by rfl⟩ : syracuseStep 3306919 = 4960379) B4960379
theorem B2324207 : Blo 1375507 2324207 := bstep (se 1 (by rfl) ⟨1743155, by rfl⟩ : syracuseStep 2324207 = 3486311) B3486311
theorem B2479943 : Blo 1375507 2479943 := bstep (se 1 (by rfl) ⟨1859957, by rfl⟩ : syracuseStep 2479943 = 3719915) B3719915
theorem B11155333 : Blo 1375507 11155333 := bstep (se 4 (by rfl) ⟨1045812, by rfl⟩ : syracuseStep 11155333 = 2091625) B2091625
theorem B8370371 : Blo 1375507 8370371 := bstep (se 1 (by rfl) ⟨6277778, by rfl⟩ : syracuseStep 8370371 = 12555557) B12555557
theorem B4962539 : Blo 1375507 4962539 := bstep (se 1 (by rfl) ⟨3721904, by rfl⟩ : syracuseStep 4962539 = 7443809) B7443809
theorem B3094991 : Blo 1375507 3094991 := bstep (se 1 (by rfl) ⟨2321243, by rfl⟩ : syracuseStep 3094991 = 4642487) B4642487
theorem B10451429 : Blo 1375507 10451429 := bstep (se 4 (by rfl) ⟨979821, by rfl⟩ : syracuseStep 10451429 = 1959643) B1959643
theorem B3095081 : Blo 1375507 3095081 := bstep (se 2 (by rfl) ⟨1160655, by rfl⟩ : syracuseStep 3095081 = 2321311) B2321311
theorem B13228595 : Blo 1375507 13228595 := bstep (se 1 (by rfl) ⟨9921446, by rfl⟩ : syracuseStep 13228595 = 19842893) B19842893
theorem B33471443 : Blo 1375507 33471443 := bstep (se 1 (by rfl) ⟨25103582, by rfl⟩ : syracuseStep 33471443 = 50207165) B50207165
theorem B7838801 : Blo 1375507 7838801 := bstep (se 2 (by rfl) ⟨2939550, by rfl⟩ : syracuseStep 7838801 = 5879101) B5879101
theorem B2063465 : Blo 1375507 2063465 := bstep (se 2 (by rfl) ⟨773799, by rfl⟩ : syracuseStep 2063465 = 1547599) B1547599
theorem B3095657 : Blo 1375507 3095657 := bstep (se 2 (by rfl) ⟨1160871, by rfl⟩ : syracuseStep 3095657 = 2321743) B2321743
theorem B2063591 : Blo 1375507 2063591 := bstep (se 1 (by rfl) ⟨1547693, by rfl⟩ : syracuseStep 2063591 = 3095387) B3095387
theorem B3095783 : Blo 1375507 3095783 := bstep (se 1 (by rfl) ⟨2321837, by rfl⟩ : syracuseStep 3095783 = 4643675) B4643675
theorem B33496355 : Blo 1375507 33496355 := bstep (se 1 (by rfl) ⟨25122266, by rfl⟩ : syracuseStep 33496355 = 50244533) B50244533
theorem B1375559 : Blo 1375507 1375559 := bstep (se 1 (by rfl) ⟨1031669, by rfl⟩ : syracuseStep 1375559 = 2063339) B2063339
theorem B19832161 : Blo 1375507 19832161 := bstep (se 2 (by rfl) ⟨7437060, by rfl⟩ : syracuseStep 19832161 = 14874121) B14874121
theorem B8936813 : Blo 1375507 8936813 := bstep (se 3 (by rfl) ⟨1675652, by rfl⟩ : syracuseStep 8936813 = 3351305) B3351305
theorem B5225897 : Blo 1375507 5225897 := bstep (se 2 (by rfl) ⟨1959711, by rfl⟩ : syracuseStep 5225897 = 3919423) B3919423
theorem B1375695 : Blo 1375507 1375695 := bstep (se 1 (by rfl) ⟨1031771, by rfl⟩ : syracuseStep 1375695 = 2063543) B2063543
theorem B11754989 : Blo 1375507 11754989 := bstep (se 3 (by rfl) ⟨2204060, by rfl⟩ : syracuseStep 11754989 = 4408121) B4408121
theorem B1375855 : Blo 1375507 1375855 := bstep (se 1 (by rfl) ⟨1031891, by rfl⟩ : syracuseStep 1375855 = 2063783) B2063783
theorem B1547887 : Blo 1375507 1547887 := bstep (se 1 (by rfl) ⟨1160915, by rfl⟩ : syracuseStep 1547887 = 2321831) B2321831
theorem B3309167 : Blo 1375507 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B1375911 : Blo 1375507 1375911 := bstep (se 1 (by rfl) ⟨1031933, by rfl⟩ : syracuseStep 1375911 = 2063867) B2063867
theorem B1547995 : Blo 1375507 1547995 := bstep (se 1 (by rfl) ⟨1160996, by rfl⟩ : syracuseStep 1547995 = 2321993) B2321993
theorem B2064095 : Blo 1375507 2064095 := bstep (se 1 (by rfl) ⟨1548071, by rfl⟩ : syracuseStep 2064095 = 3096143) B3096143
theorem B3096287 : Blo 1375507 3096287 := bstep (se 1 (by rfl) ⟨2322215, by rfl⟩ : syracuseStep 3096287 = 4644431) B4644431
theorem B1375975 : Blo 1375507 1375975 := bstep (se 1 (by rfl) ⟨1031981, by rfl⟩ : syracuseStep 1375975 = 2063963) B2063963
theorem B2064137 : Blo 1375507 2064137 := bstep (se 2 (by rfl) ⟨774051, by rfl⟩ : syracuseStep 2064137 = 1548103) B1548103
theorem B1376031 : Blo 1375507 1376031 := bstep (se 1 (by rfl) ⟨1032023, by rfl⟩ : syracuseStep 1376031 = 2064047) B2064047
theorem B3096359 : Blo 1375507 3096359 := bstep (se 1 (by rfl) ⟨2322269, by rfl⟩ : syracuseStep 3096359 = 4644539) B4644539
theorem B1376111 : Blo 1375507 1376111 := bstep (se 1 (by rfl) ⟨1032083, by rfl⟩ : syracuseStep 1376111 = 2064167) B2064167
theorem B3309455 : Blo 1375507 3309455 := bstep (se 1 (by rfl) ⟨2482091, by rfl⟩ : syracuseStep 3309455 = 4964183) B4964183
theorem B1376167 : Blo 1375507 1376167 := bstep (se 1 (by rfl) ⟨1032125, by rfl⟩ : syracuseStep 1376167 = 2064251) B2064251
theorem B16744391 : Blo 1375507 16744391 := bstep (se 1 (by rfl) ⟨12558293, by rfl⟩ : syracuseStep 16744391 = 25116587) B25116587
theorem B19103687 : Blo 1375507 19103687 := bstep (se 1 (by rfl) ⟨14327765, by rfl⟩ : syracuseStep 19103687 = 28655531) B28655531
theorem B2613215 : Blo 1375507 2613215 := bstep (se 1 (by rfl) ⟨1959911, by rfl⟩ : syracuseStep 2613215 = 3919823) B3919823
theorem B2203625 : Blo 1375507 2203625 := bstep (se 2 (by rfl) ⟨826359, by rfl⟩ : syracuseStep 2203625 = 1652719) B1652719
theorem B1376383 : Blo 1375507 1376383 := bstep (se 1 (by rfl) ⟨1032287, by rfl⟩ : syracuseStep 1376383 = 2064575) B2064575
theorem B4645025 : Blo 1375507 4645025 := bstep (se 2 (by rfl) ⟨1741884, by rfl⟩ : syracuseStep 4645025 = 3483769) B3483769
theorem B1548463 : Blo 1375507 1548463 := bstep (se 1 (by rfl) ⟨1161347, by rfl⟩ : syracuseStep 1548463 = 2322695) B2322695
theorem B32202967 : Blo 1375507 32202967 := bstep (se 1 (by rfl) ⟨24152225, by rfl⟩ : syracuseStep 32202967 = 48304451) B48304451
theorem B14876891 : Blo 1375507 14876891 := bstep (se 1 (by rfl) ⟨11157668, by rfl⟩ : syracuseStep 14876891 = 22315337) B22315337
theorem B3096935 : Blo 1375507 3096935 := bstep (se 1 (by rfl) ⟨2322701, by rfl⟩ : syracuseStep 3096935 = 4645403) B4645403
theorem B1376667 : Blo 1375507 1376667 := bstep (se 1 (by rfl) ⟨1032500, by rfl⟩ : syracuseStep 1376667 = 2065001) B2065001
theorem B1376671 : Blo 1375507 1376671 := bstep (se 1 (by rfl) ⟨1032503, by rfl⟩ : syracuseStep 1376671 = 2065007) B2065007
theorem B2064923 : Blo 1375507 2064923 := bstep (se 1 (by rfl) ⟨1548692, by rfl⟩ : syracuseStep 2064923 = 3097385) B3097385
theorem B2065103 : Blo 1375507 2065103 := bstep (se 1 (by rfl) ⟨1548827, by rfl⟩ : syracuseStep 2065103 = 3097655) B3097655
theorem B5227325 : Blo 1375507 5227325 := bstep (se 3 (by rfl) ⟨980123, by rfl⟩ : syracuseStep 5227325 = 1960247) B1960247
theorem B1377087 : Blo 1375507 1377087 := bstep (se 1 (by rfl) ⟨1032815, by rfl⟩ : syracuseStep 1377087 = 2065631) B2065631
theorem B2065223 : Blo 1375507 2065223 := bstep (se 1 (by rfl) ⟨1548917, by rfl⟩ : syracuseStep 2065223 = 3097835) B3097835
theorem B1377095 : Blo 1375507 1377095 := bstep (se 1 (by rfl) ⟨1032821, by rfl⟩ : syracuseStep 1377095 = 2065643) B2065643
theorem B1549147 : Blo 1375507 1549147 := bstep (se 1 (by rfl) ⟨1161860, by rfl⟩ : syracuseStep 1549147 = 2323721) B2323721
theorem B1549183 : Blo 1375507 1549183 := bstep (se 1 (by rfl) ⟨1161887, by rfl⟩ : syracuseStep 1549183 = 2323775) B2323775
theorem B2065289 : Blo 1375507 2065289 := bstep (se 2 (by rfl) ⟨774483, by rfl⟩ : syracuseStep 2065289 = 1548967) B1548967
theorem B1377351 : Blo 1375507 1377351 := bstep (se 1 (by rfl) ⟨1033013, by rfl⟩ : syracuseStep 1377351 = 2066027) B2066027
theorem B2065535 : Blo 1375507 2065535 := bstep (se 1 (by rfl) ⟨1549151, by rfl⟩ : syracuseStep 2065535 = 3098303) B3098303
theorem B1377407 : Blo 1375507 1377407 := bstep (se 1 (by rfl) ⟨1033055, by rfl⟩ : syracuseStep 1377407 = 2066111) B2066111
theorem B1549471 : Blo 1375507 1549471 := bstep (se 1 (by rfl) ⟨1162103, by rfl⟩ : syracuseStep 1549471 = 2324207) B2324207
theorem B2065673 : Blo 1375507 2065673 := bstep (se 2 (by rfl) ⟨774627, by rfl⟩ : syracuseStep 2065673 = 1549255) B1549255
theorem B5883167 : Blo 1375507 5883167 := bstep (se 1 (by rfl) ⟨4412375, by rfl⟩ : syracuseStep 5883167 = 8824751) B8824751
theorem B602654093 : Blo 1375507 602654093 := bstep (se 3 (by rfl) ⟨112997642, by rfl⟩ : syracuseStep 602654093 = 225995285) B225995285
theorem B5580247 : Blo 1375507 5580247 := bstep (se 1 (by rfl) ⟨4185185, by rfl⟩ : syracuseStep 5580247 = 8370371) B8370371
theorem B120743405 : Blo 1375507 120743405 := bstep (se 3 (by rfl) ⟨22639388, by rfl⟩ : syracuseStep 120743405 = 45278777) B45278777
theorem B5441087 : Blo 1375507 5441087 := bstep (se 1 (by rfl) ⟨4080815, by rfl⟩ : syracuseStep 5441087 = 8161631) B8161631
theorem B2066153 : Blo 1375507 2066153 := bstep (se 2 (by rfl) ⟨774807, by rfl⟩ : syracuseStep 2066153 = 1549615) B1549615
theorem B2066159 : Blo 1375507 2066159 := bstep (se 1 (by rfl) ⟨1549619, by rfl⟩ : syracuseStep 2066159 = 3099239) B3099239
theorem B5228327 : Blo 1375507 5228327 := bstep (se 1 (by rfl) ⟨3921245, by rfl⟩ : syracuseStep 5228327 = 7842491) B7842491
theorem B4409225 : Blo 1375507 4409225 := bstep (se 2 (by rfl) ⟨1653459, by rfl⟩ : syracuseStep 4409225 = 3306919) B3306919
theorem B22308857 : Blo 1375507 22308857 := bstep (se 2 (by rfl) ⟨8365821, by rfl⟩ : syracuseStep 22308857 = 16731643) B16731643
theorem B11167793 : Blo 1375507 11167793 := bstep (se 2 (by rfl) ⟨4187922, by rfl⟩ : syracuseStep 11167793 = 8375845) B8375845
theorem B6613181 : Blo 1375507 6613181 := bstep (se 3 (by rfl) ⟨1239971, by rfl⟩ : syracuseStep 6613181 = 2479943) B2479943
theorem B5957875 : Blo 1375507 5957875 := bstep (se 1 (by rfl) ⟨4468406, by rfl⟩ : syracuseStep 5957875 = 8936813) B8936813
theorem B3483931 : Blo 1375507 3483931 := bstep (se 1 (by rfl) ⟨2612948, by rfl⟩ : syracuseStep 3483931 = 5225897) B5225897
theorem B8825213 : Blo 1375507 8825213 := bstep (se 3 (by rfl) ⟨1654727, by rfl⟩ : syracuseStep 8825213 = 3309455) B3309455
theorem B7833995 : Blo 1375507 7833995 := bstep (se 1 (by rfl) ⟨5875496, by rfl⟩ : syracuseStep 7833995 = 11750993) B11750993
theorem B64539031 : Blo 1375507 64539031 := bstep (se 1 (by rfl) ⟨48404273, by rfl⟩ : syracuseStep 64539031 = 96808547) B96808547
theorem B2206111 : Blo 1375507 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B5876333 : Blo 1375507 5876333 := bstep (se 3 (by rfl) ⟨1101812, by rfl⟩ : syracuseStep 5876333 = 2203625) B2203625
theorem B5294909 : Blo 1375507 5294909 := bstep (se 3 (by rfl) ⟨992795, by rfl⟩ : syracuseStep 5294909 = 1985591) B1985591
theorem B1469647 : Blo 1375507 1469647 := bstep (se 1 (by rfl) ⟨1102235, by rfl⟩ : syracuseStep 1469647 = 2204471) B2204471
theorem B3919195 : Blo 1375507 3919195 := bstep (se 1 (by rfl) ⟨2939396, by rfl⟩ : syracuseStep 3919195 = 5878793) B5878793
theorem B3919367 : Blo 1375507 3919367 := bstep (se 1 (by rfl) ⟨2939525, by rfl⟩ : syracuseStep 3919367 = 5879051) B5879051
theorem B6614855 : Blo 1375507 6614855 := bstep (se 1 (by rfl) ⟨4961141, by rfl⟩ : syracuseStep 6614855 = 9922283) B9922283
theorem B2093231 : Blo 1375507 2093231 := bstep (se 1 (by rfl) ⟨1569923, by rfl⟩ : syracuseStep 2093231 = 3139847) B3139847
theorem B6967619 : Blo 1375507 6967619 := bstep (se 1 (by rfl) ⟨5225714, by rfl⟩ : syracuseStep 6967619 = 10451429) B10451429
theorem B8819063 : Blo 1375507 8819063 := bstep (se 1 (by rfl) ⟨6614297, by rfl⟩ : syracuseStep 8819063 = 13228595) B13228595
theorem B3486473 : Blo 1375507 3486473 := bstep (se 2 (by rfl) ⟨1307427, by rfl⟩ : syracuseStep 3486473 = 2614855) B2614855
theorem B7836659 : Blo 1375507 7836659 := bstep (se 1 (by rfl) ⟨5877494, by rfl⟩ : syracuseStep 7836659 = 11754989) B11754989
theorem B14873777 : Blo 1375507 14873777 := bstep (se 2 (by rfl) ⟨5577666, by rfl⟩ : syracuseStep 14873777 = 11155333) B11155333
theorem B11162927 : Blo 1375507 11162927 := bstep (se 1 (by rfl) ⟨8372195, by rfl⟩ : syracuseStep 11162927 = 16744391) B16744391
theorem B12735791 : Blo 1375507 12735791 := bstep (se 1 (by rfl) ⟨9551843, by rfl⟩ : syracuseStep 12735791 = 19103687) B19103687
theorem B1742143 : Blo 1375507 1742143 := bstep (se 1 (by rfl) ⟨1306607, by rfl⟩ : syracuseStep 1742143 = 2613215) B2613215
theorem B6280697 : Blo 1375507 6280697 := bstep (se 2 (by rfl) ⟨2355261, by rfl⟩ : syracuseStep 6280697 = 4710523) B4710523
theorem B6280859 : Blo 1375507 6280859 := bstep (se 1 (by rfl) ⟨4710644, by rfl⟩ : syracuseStep 6280859 = 9421289) B9421289
theorem B14890729 : Blo 1375507 14890729 := bstep (se 2 (by rfl) ⟨5584023, by rfl⟩ : syracuseStep 14890729 = 11168047) B11168047
theorem B75323459 : Blo 1375507 75323459 := bstep (se 1 (by rfl) ⟨56492594, by rfl⟩ : syracuseStep 75323459 = 112985189) B112985189
theorem B35772509 : Blo 1375507 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B18839735 : Blo 1375507 18839735 := bstep (se 1 (by rfl) ⟨14129801, by rfl⟩ : syracuseStep 18839735 = 28259603) B28259603
theorem B28244159 : Blo 1375507 28244159 := bstep (se 1 (by rfl) ⟨21183119, by rfl⟩ : syracuseStep 28244159 = 42366239) B42366239
theorem B5880023 : Blo 1375507 5880023 := bstep (se 1 (by rfl) ⟨4410017, by rfl⟩ : syracuseStep 5880023 = 8820035) B8820035
theorem B63584837 : Blo 1375507 63584837 := bstep (se 4 (by rfl) ⟨5961078, by rfl⟩ : syracuseStep 63584837 = 11922157) B11922157
theorem B2611855 : Blo 1375507 2611855 := bstep (se 1 (by rfl) ⟨1958891, by rfl⟩ : syracuseStep 2611855 = 3917783) B3917783
theorem B3308359 : Blo 1375507 3308359 := bstep (se 1 (by rfl) ⟨2481269, by rfl⟩ : syracuseStep 3308359 = 4962539) B4962539
theorem B9927613 : Blo 1375507 9927613 := bstep (se 3 (by rfl) ⟨1861427, by rfl⟩ : syracuseStep 9927613 = 3722855) B3722855
theorem B2063327 : Blo 1375507 2063327 := bstep (se 1 (by rfl) ⟨1547495, by rfl⟩ : syracuseStep 2063327 = 3094991) B3094991
theorem B15686621 : Blo 1375507 15686621 := bstep (se 3 (by rfl) ⟨2941241, by rfl⟩ : syracuseStep 15686621 = 5882483) B5882483
theorem B2063387 : Blo 1375507 2063387 := bstep (se 1 (by rfl) ⟨1547540, by rfl⟩ : syracuseStep 2063387 = 3095081) B3095081
theorem B26442881 : Blo 1375507 26442881 := bstep (se 2 (by rfl) ⟨9916080, by rfl⟩ : syracuseStep 26442881 = 19832161) B19832161
theorem B1548283 : Blo 1375507 1548283 := bstep (se 1 (by rfl) ⟨1161212, by rfl⟩ : syracuseStep 1548283 = 2322425) B2322425
theorem B22314295 : Blo 1375507 22314295 := bstep (se 1 (by rfl) ⟨16735721, by rfl⟩ : syracuseStep 22314295 = 33471443) B33471443
theorem B5225867 : Blo 1375507 5225867 := bstep (se 1 (by rfl) ⟨3919400, by rfl⟩ : syracuseStep 5225867 = 7838801) B7838801
theorem B1375643 : Blo 1375507 1375643 := bstep (se 1 (by rfl) ⟨1031732, by rfl⟩ : syracuseStep 1375643 = 2063465) B2063465
theorem B2063771 : Blo 1375507 2063771 := bstep (se 1 (by rfl) ⟨1547828, by rfl⟩ : syracuseStep 2063771 = 3095657) B3095657
theorem B2063849 : Blo 1375507 2063849 := bstep (se 2 (by rfl) ⟨773943, by rfl⟩ : syracuseStep 2063849 = 1547887) B1547887
theorem B1375727 : Blo 1375507 1375727 := bstep (se 1 (by rfl) ⟨1031795, by rfl⟩ : syracuseStep 1375727 = 2063591) B2063591
theorem B2063855 : Blo 1375507 2063855 := bstep (se 1 (by rfl) ⟨1547891, by rfl⟩ : syracuseStep 2063855 = 3095783) B3095783
theorem B22330903 : Blo 1375507 22330903 := bstep (se 1 (by rfl) ⟨16748177, by rfl⟩ : syracuseStep 22330903 = 33496355) B33496355
theorem B2063993 : Blo 1375507 2063993 := bstep (se 2 (by rfl) ⟨773997, by rfl⟩ : syracuseStep 2063993 = 1547995) B1547995
theorem B1376063 : Blo 1375507 1376063 := bstep (se 1 (by rfl) ⟨1032047, by rfl⟩ : syracuseStep 1376063 = 2064095) B2064095
theorem B2064191 : Blo 1375507 2064191 := bstep (se 1 (by rfl) ⟨1548143, by rfl⟩ : syracuseStep 2064191 = 3096287) B3096287
theorem B2203471 : Blo 1375507 2203471 := bstep (se 1 (by rfl) ⟨1652603, by rfl⟩ : syracuseStep 2203471 = 3305207) B3305207
theorem B7839575 : Blo 1375507 7839575 := bstep (se 1 (by rfl) ⟨5879681, by rfl⟩ : syracuseStep 7839575 = 11759363) B11759363
theorem B1376091 : Blo 1375507 1376091 := bstep (se 1 (by rfl) ⟨1032068, by rfl⟩ : syracuseStep 1376091 = 2064137) B2064137
theorem B2064239 : Blo 1375507 2064239 := bstep (se 1 (by rfl) ⟨1548179, by rfl⟩ : syracuseStep 2064239 = 3096359) B3096359
theorem B2613161 : Blo 1375507 2613161 := bstep (se 2 (by rfl) ⟨979935, by rfl⟩ : syracuseStep 2613161 = 1959871) B1959871
theorem B3096683 : Blo 1375507 3096683 := bstep (se 1 (by rfl) ⟨2322512, by rfl⟩ : syracuseStep 3096683 = 4645025) B4645025
theorem B4645079 : Blo 1375507 4645079 := bstep (se 1 (by rfl) ⟨3483809, by rfl⟩ : syracuseStep 4645079 = 6967619) B6967619
theorem B2064617 : Blo 1375507 2064617 := bstep (se 2 (by rfl) ⟨774231, by rfl⟩ : syracuseStep 2064617 = 1548463) B1548463
theorem B2064623 : Blo 1375507 2064623 := bstep (se 1 (by rfl) ⟨1548467, by rfl⟩ : syracuseStep 2064623 = 3096935) B3096935
theorem B1376615 : Blo 1375507 1376615 := bstep (se 1 (by rfl) ⟨1032461, by rfl⟩ : syracuseStep 1376615 = 2064923) B2064923
theorem B4645241 : Blo 1375507 4645241 := bstep (se 2 (by rfl) ⟨1741965, by rfl⟩ : syracuseStep 4645241 = 3483931) B3483931
theorem B1376735 : Blo 1375507 1376735 := bstep (se 1 (by rfl) ⟨1032551, by rfl⟩ : syracuseStep 1376735 = 2065103) B2065103
theorem B1376815 : Blo 1375507 1376815 := bstep (se 1 (by rfl) ⟨1032611, by rfl⟩ : syracuseStep 1376815 = 2065223) B2065223
theorem B2941481 : Blo 1375507 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B1376859 : Blo 1375507 1376859 := bstep (se 1 (by rfl) ⟨1032644, by rfl⟩ : syracuseStep 1376859 = 2065289) B2065289
theorem B1377023 : Blo 1375507 1377023 := bstep (se 1 (by rfl) ⟨1032767, by rfl⟩ : syracuseStep 1377023 = 2065535) B2065535
theorem B1377115 : Blo 1375507 1377115 := bstep (se 1 (by rfl) ⟨1032836, by rfl⟩ : syracuseStep 1377115 = 2065673) B2065673
theorem B3482473 : Blo 1375507 3482473 := bstep (se 2 (by rfl) ⟨1305927, by rfl⟩ : syracuseStep 3482473 = 2611855) B2611855
theorem B401769395 : Blo 1375507 401769395 := bstep (se 1 (by rfl) ⟨301327046, by rfl⟩ : syracuseStep 401769395 = 602654093) B602654093
theorem B80495603 : Blo 1375507 80495603 := bstep (se 1 (by rfl) ⟨60371702, by rfl⟩ : syracuseStep 80495603 = 120743405) B120743405
theorem B2065529 : Blo 1375507 2065529 := bstep (se 2 (by rfl) ⟨774573, by rfl⟩ : syracuseStep 2065529 = 1549147) B1549147
theorem B1377435 : Blo 1375507 1377435 := bstep (se 1 (by rfl) ⟨1033076, by rfl⟩ : syracuseStep 1377435 = 2066153) B2066153
theorem B1377439 : Blo 1375507 1377439 := bstep (se 1 (by rfl) ⟨1033079, by rfl⟩ : syracuseStep 1377439 = 2066159) B2066159
theorem B2065577 : Blo 1375507 2065577 := bstep (se 2 (by rfl) ⟨774591, by rfl⟩ : syracuseStep 2065577 = 1549183) B1549183
theorem B23848339 : Blo 1375507 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B12559823 : Blo 1375507 12559823 := bstep (se 1 (by rfl) ⟨9419867, by rfl⟩ : syracuseStep 12559823 = 18839735) B18839735
theorem B4408787 : Blo 1375507 4408787 := bstep (se 1 (by rfl) ⟨3306590, by rfl⟩ : syracuseStep 4408787 = 6613181) B6613181
theorem B2065961 : Blo 1375507 2065961 := bstep (se 2 (by rfl) ⟨774735, by rfl⟩ : syracuseStep 2065961 = 1549471) B1549471
theorem B5883475 : Blo 1375507 5883475 := bstep (se 1 (by rfl) ⟨4412606, by rfl⟩ : syracuseStep 5883475 = 8825213) B8825213
theorem B3917555 : Blo 1375507 3917555 := bstep (se 1 (by rfl) ⟨2938166, by rfl⟩ : syracuseStep 3917555 = 5876333) B5876333
theorem B7440329 : Blo 1375507 7440329 := bstep (se 2 (by rfl) ⟨2790123, by rfl⟩ : syracuseStep 7440329 = 5580247) B5580247
theorem B3483911 : Blo 1375507 3483911 := bstep (se 1 (by rfl) ⟨2612933, by rfl⟩ : syracuseStep 3483911 = 5225867) B5225867
theorem B52947269 : Blo 1375507 52947269 := bstep (se 4 (by rfl) ⟨4963806, by rfl⟩ : syracuseStep 52947269 = 9927613) B9927613
theorem B4409903 : Blo 1375507 4409903 := bstep (se 1 (by rfl) ⟨3307427, by rfl⟩ : syracuseStep 4409903 = 6614855) B6614855
theorem B1395487 : Blo 1375507 1395487 := bstep (se 1 (by rfl) ⟨1046615, by rfl⟩ : syracuseStep 1395487 = 2093231) B2093231
theorem B42937289 : Blo 1375507 42937289 := bstep (se 2 (by rfl) ⟨16101483, by rfl⟩ : syracuseStep 42937289 = 32202967) B32202967
theorem B86052041 : Blo 1375507 86052041 := bstep (se 2 (by rfl) ⟨32269515, by rfl⟩ : syracuseStep 86052041 = 64539031) B64539031
theorem B3484883 : Blo 1375507 3484883 := bstep (se 1 (by rfl) ⟨2613662, by rfl⟩ : syracuseStep 3484883 = 5227325) B5227325
theorem B9915851 : Blo 1375507 9915851 := bstep (se 1 (by rfl) ⟨7436888, by rfl⟩ : syracuseStep 9915851 = 14873777) B14873777
theorem B7441951 : Blo 1375507 7441951 := bstep (se 1 (by rfl) ⟨5581463, by rfl⟩ : syracuseStep 7441951 = 11162927) B11162927
theorem B8490527 : Blo 1375507 8490527 := bstep (se 1 (by rfl) ⟨6367895, by rfl⟩ : syracuseStep 8490527 = 12735791) B12735791
theorem B4411145 : Blo 1375507 4411145 := bstep (se 2 (by rfl) ⟨1654179, by rfl⟩ : syracuseStep 4411145 = 3308359) B3308359
theorem B3485551 : Blo 1375507 3485551 := bstep (se 1 (by rfl) ⟨2614163, by rfl⟩ : syracuseStep 3485551 = 5228327) B5228327
theorem B16748525 : Blo 1375507 16748525 := bstep (se 3 (by rfl) ⟨3140348, by rfl⟩ : syracuseStep 16748525 = 6280697) B6280697
theorem B14872571 : Blo 1375507 14872571 := bstep (se 1 (by rfl) ⟨11154428, by rfl⟩ : syracuseStep 14872571 = 22308857) B22308857
theorem B18829439 : Blo 1375507 18829439 := bstep (se 1 (by rfl) ⟨14122079, by rfl⟩ : syracuseStep 18829439 = 28244159) B28244159
theorem B3920015 : Blo 1375507 3920015 := bstep (se 1 (by rfl) ⟨2940011, by rfl⟩ : syracuseStep 3920015 = 5880023) B5880023
theorem B5222663 : Blo 1375507 5222663 := bstep (se 1 (by rfl) ⟨3916997, by rfl⟩ : syracuseStep 5222663 = 7833995) B7833995
theorem B42389891 : Blo 1375507 42389891 := bstep (se 1 (by rfl) ⟨31792418, by rfl⟩ : syracuseStep 42389891 = 63584837) B63584837
theorem B16748957 : Blo 1375507 16748957 := bstep (se 3 (by rfl) ⟨3140429, by rfl⟩ : syracuseStep 16748957 = 6280859) B6280859
theorem B2322857 : Blo 1375507 2322857 := bstep (se 2 (by rfl) ⟨871071, by rfl⟩ : syracuseStep 2322857 = 1742143) B1742143
theorem B10457747 : Blo 1375507 10457747 := bstep (se 1 (by rfl) ⟨7843310, by rfl⟩ : syracuseStep 10457747 = 15686621) B15686621
theorem B29774537 : Blo 1375507 29774537 := bstep (se 2 (by rfl) ⟨11165451, by rfl⟩ : syracuseStep 29774537 = 22330903) B22330903
theorem B19854305 : Blo 1375507 19854305 := bstep (se 2 (by rfl) ⟨7445364, by rfl⟩ : syracuseStep 19854305 = 14890729) B14890729
theorem B2937961 : Blo 1375507 2937961 := bstep (se 2 (by rfl) ⟨1101735, by rfl⟩ : syracuseStep 2937961 = 2203471) B2203471
theorem B6968429 : Blo 1375507 6968429 := bstep (se 3 (by rfl) ⟨1306580, by rfl⟩ : syracuseStep 6968429 = 2613161) B2613161
theorem B9917927 : Blo 1375507 9917927 := bstep (se 1 (by rfl) ⟨7438445, by rfl⟩ : syracuseStep 9917927 = 14876891) B14876891
theorem B5879375 : Blo 1375507 5879375 := bstep (se 1 (by rfl) ⟨4409531, by rfl⟩ : syracuseStep 5879375 = 8819063) B8819063
theorem B2324315 : Blo 1375507 2324315 := bstep (se 1 (by rfl) ⟨1743236, by rfl⟩ : syracuseStep 2324315 = 3486473) B3486473
theorem B5224439 : Blo 1375507 5224439 := bstep (se 1 (by rfl) ⟨3918329, by rfl⟩ : syracuseStep 5224439 = 7836659) B7836659
theorem B3922111 : Blo 1375507 3922111 := bstep (se 1 (by rfl) ⟨2941583, by rfl⟩ : syracuseStep 3922111 = 5883167) B5883167
theorem B3627391 : Blo 1375507 3627391 := bstep (se 1 (by rfl) ⟨2720543, by rfl⟩ : syracuseStep 3627391 = 5441087) B5441087
theorem B7838117 : Blo 1375507 7838117 := bstep (se 4 (by rfl) ⟨734823, by rfl⟩ : syracuseStep 7838117 = 1469647) B1469647
theorem B2939483 : Blo 1375507 2939483 := bstep (se 1 (by rfl) ⟨2204612, by rfl⟩ : syracuseStep 2939483 = 4409225) B4409225
theorem B31775333 : Blo 1375507 31775333 := bstep (se 4 (by rfl) ⟨2978937, by rfl⟩ : syracuseStep 31775333 = 5957875) B5957875
theorem B7445195 : Blo 1375507 7445195 := bstep (se 1 (by rfl) ⟨5583896, by rfl⟩ : syracuseStep 7445195 = 11167793) B11167793
theorem B50215639 : Blo 1375507 50215639 := bstep (se 1 (by rfl) ⟨37661729, by rfl⟩ : syracuseStep 50215639 = 75323459) B75323459
theorem B29752393 : Blo 1375507 29752393 := bstep (se 2 (by rfl) ⟨11157147, by rfl⟩ : syracuseStep 29752393 = 22314295) B22314295
theorem B5225593 : Blo 1375507 5225593 := bstep (se 2 (by rfl) ⟨1959597, by rfl⟩ : syracuseStep 5225593 = 3919195) B3919195
theorem B3529939 : Blo 1375507 3529939 := bstep (se 1 (by rfl) ⟨2647454, by rfl⟩ : syracuseStep 3529939 = 5294909) B5294909
theorem B1375551 : Blo 1375507 1375551 := bstep (se 1 (by rfl) ⟨1031663, by rfl⟩ : syracuseStep 1375551 = 2063327) B2063327
theorem B1375591 : Blo 1375507 1375591 := bstep (se 1 (by rfl) ⟨1031693, by rfl⟩ : syracuseStep 1375591 = 2063387) B2063387
theorem B17628587 : Blo 1375507 17628587 := bstep (se 1 (by rfl) ⟨13221440, by rfl⟩ : syracuseStep 17628587 = 26442881) B26442881
theorem B1375847 : Blo 1375507 1375847 := bstep (se 1 (by rfl) ⟨1031885, by rfl⟩ : syracuseStep 1375847 = 2063771) B2063771
theorem B1375899 : Blo 1375507 1375899 := bstep (se 1 (by rfl) ⟨1031924, by rfl⟩ : syracuseStep 1375899 = 2063849) B2063849
theorem B1375903 : Blo 1375507 1375903 := bstep (se 1 (by rfl) ⟨1031927, by rfl⟩ : syracuseStep 1375903 = 2063855) B2063855
theorem B2612911 : Blo 1375507 2612911 := bstep (se 1 (by rfl) ⟨1959683, by rfl⟩ : syracuseStep 2612911 = 3919367) B3919367
theorem B1375995 : Blo 1375507 1375995 := bstep (se 1 (by rfl) ⟨1031996, by rfl⟩ : syracuseStep 1375995 = 2063993) B2063993
theorem B1376127 : Blo 1375507 1376127 := bstep (se 1 (by rfl) ⟨1032095, by rfl⟩ : syracuseStep 1376127 = 2064191) B2064191
theorem B5226383 : Blo 1375507 5226383 := bstep (se 1 (by rfl) ⟨3919787, by rfl⟩ : syracuseStep 5226383 = 7839575) B7839575
theorem B1376159 : Blo 1375507 1376159 := bstep (se 1 (by rfl) ⟨1032119, by rfl⟩ : syracuseStep 1376159 = 2064239) B2064239
theorem B2064377 : Blo 1375507 2064377 := bstep (se 2 (by rfl) ⟨774141, by rfl⟩ : syracuseStep 2064377 = 1548283) B1548283
theorem B2064455 : Blo 1375507 2064455 := bstep (se 1 (by rfl) ⟨1548341, by rfl⟩ : syracuseStep 2064455 = 3096683) B3096683
theorem B3096719 : Blo 1375507 3096719 := bstep (se 1 (by rfl) ⟨2322539, by rfl⟩ : syracuseStep 3096719 = 4645079) B4645079
theorem B1376411 : Blo 1375507 1376411 := bstep (se 1 (by rfl) ⟨1032308, by rfl⟩ : syracuseStep 1376411 = 2064617) B2064617
theorem B1376415 : Blo 1375507 1376415 := bstep (se 1 (by rfl) ⟨1032311, by rfl⟩ : syracuseStep 1376415 = 2064623) B2064623
theorem B3481775 : Blo 1375507 3481775 := bstep (se 1 (by rfl) ⟨2611331, by rfl⟩ : syracuseStep 3481775 = 5222663) B5222663
theorem B3096827 : Blo 1375507 3096827 := bstep (se 1 (by rfl) ⟨2322620, by rfl⟩ : syracuseStep 3096827 = 4645241) B4645241
theorem B1548571 : Blo 1375507 1548571 := bstep (se 1 (by rfl) ⟨1161428, by rfl⟩ : syracuseStep 1548571 = 2322857) B2322857
theorem B10453373 : Blo 1375507 10453373 := bstep (se 3 (by rfl) ⟨1960007, by rfl⟩ : syracuseStep 10453373 = 3920015) B3920015
theorem B6971831 : Blo 1375507 6971831 := bstep (se 1 (by rfl) ⟨5228873, by rfl⟩ : syracuseStep 6971831 = 10457747) B10457747
theorem B19849691 : Blo 1375507 19849691 := bstep (se 1 (by rfl) ⟨14887268, by rfl⟩ : syracuseStep 19849691 = 29774537) B29774537
theorem B267846263 : Blo 1375507 267846263 := bstep (se 1 (by rfl) ⟨200884697, by rfl⟩ : syracuseStep 267846263 = 401769395) B401769395
theorem B4645619 : Blo 1375507 4645619 := bstep (se 1 (by rfl) ⟨3484214, by rfl⟩ : syracuseStep 4645619 = 6968429) B6968429
theorem B1377019 : Blo 1375507 1377019 := bstep (se 1 (by rfl) ⟨1032764, by rfl⟩ : syracuseStep 1377019 = 2065529) B2065529
theorem B1377051 : Blo 1375507 1377051 := bstep (se 1 (by rfl) ⟨1032788, by rfl⟩ : syracuseStep 1377051 = 2065577) B2065577
theorem B66954185 : Blo 1375507 66954185 := bstep (se 2 (by rfl) ⟨25107819, by rfl⟩ : syracuseStep 66954185 = 50215639) B50215639
theorem B8373215 : Blo 1375507 8373215 := bstep (se 1 (by rfl) ⟨6279911, by rfl⟩ : syracuseStep 8373215 = 12559823) B12559823
theorem B6611951 : Blo 1375507 6611951 := bstep (se 1 (by rfl) ⟨4958963, by rfl⟩ : syracuseStep 6611951 = 9917927) B9917927
theorem B1377307 : Blo 1375507 1377307 := bstep (se 1 (by rfl) ⟨1032980, by rfl⟩ : syracuseStep 1377307 = 2065961) B2065961
theorem B338936885 : Blo 1375507 338936885 := bstep (se 5 (by rfl) ⟨15887666, by rfl⟩ : syracuseStep 338936885 = 31775333) B31775333
theorem B44663885 : Blo 1375507 44663885 := bstep (se 3 (by rfl) ⟨8374478, by rfl⟩ : syracuseStep 44663885 = 16748957) B16748957
theorem B11756765 : Blo 1375507 11756765 := bstep (se 3 (by rfl) ⟨2204393, by rfl⟩ : syracuseStep 11756765 = 4408787) B4408787
theorem B1549543 : Blo 1375507 1549543 := bstep (se 1 (by rfl) ⟨1162157, by rfl⟩ : syracuseStep 1549543 = 2324315) B2324315
theorem B3482959 : Blo 1375507 3482959 := bstep (se 1 (by rfl) ⟨2612219, by rfl⟩ : syracuseStep 3482959 = 5224439) B5224439
theorem B1959655 : Blo 1375507 1959655 := bstep (se 1 (by rfl) ⟨1469741, by rfl⟩ : syracuseStep 1959655 = 2939483) B2939483
theorem B28624859 : Blo 1375507 28624859 := bstep (se 1 (by rfl) ⟨21468644, by rfl⟩ : syracuseStep 28624859 = 42937289) B42937289
theorem B9922601 : Blo 1375507 9922601 := bstep (se 2 (by rfl) ⟨3720975, by rfl⟩ : syracuseStep 9922601 = 7441951) B7441951
theorem B3483881 : Blo 1375507 3483881 := bstep (se 2 (by rfl) ⟨1306455, by rfl⟩ : syracuseStep 3483881 = 2612911) B2612911
theorem B4647401 : Blo 1375507 4647401 := bstep (se 2 (by rfl) ⟨1742775, by rfl⟩ : syracuseStep 4647401 = 3485551) B3485551
theorem B3484255 : Blo 1375507 3484255 := bstep (se 1 (by rfl) ⟨2613191, by rfl⟩ : syracuseStep 3484255 = 5226383) B5226383
theorem B9915047 : Blo 1375507 9915047 := bstep (se 1 (by rfl) ⟨7436285, by rfl⟩ : syracuseStep 9915047 = 14872571) B14872571
theorem B12552959 : Blo 1375507 12552959 := bstep (se 1 (by rfl) ⟨9414719, by rfl⟩ : syracuseStep 12552959 = 18829439) B18829439
theorem B5229481 : Blo 1375507 5229481 := bstep (se 2 (by rfl) ⟨1961055, by rfl⟩ : syracuseStep 5229481 = 3922111) B3922111
theorem B4836521 : Blo 1375507 4836521 := bstep (se 2 (by rfl) ⟨1813695, by rfl⟩ : syracuseStep 4836521 = 3627391) B3627391
theorem B3919583 : Blo 1375507 3919583 := bstep (se 1 (by rfl) ⟨2939687, by rfl⟩ : syracuseStep 3919583 = 5879375) B5879375
theorem B4960219 : Blo 1375507 4960219 := bstep (se 1 (by rfl) ⟨3720164, by rfl⟩ : syracuseStep 4960219 = 7440329) B7440329
theorem B39669857 : Blo 1375507 39669857 := bstep (se 2 (by rfl) ⟨14876196, by rfl⟩ : syracuseStep 39669857 = 29752393) B29752393
theorem B7843949 : Blo 1375507 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B11759741 : Blo 1375507 11759741 := bstep (se 3 (by rfl) ⟨2204951, by rfl⟩ : syracuseStep 11759741 = 4409903) B4409903
theorem B6967457 : Blo 1375507 6967457 := bstep (se 2 (by rfl) ⟨2612796, by rfl⟩ : syracuseStep 6967457 = 5225593) B5225593
theorem B7442597 : Blo 1375507 7442597 := bstep (se 4 (by rfl) ⟨697743, by rfl⟩ : syracuseStep 7442597 = 1395487) B1395487
theorem B2322607 : Blo 1375507 2322607 := bstep (se 1 (by rfl) ⟨1741955, by rfl⟩ : syracuseStep 2322607 = 3483911) B3483911
theorem B4706585 : Blo 1375507 4706585 := bstep (se 2 (by rfl) ⟨1764969, by rfl⟩ : syracuseStep 4706585 = 3529939) B3529939
theorem B31797785 : Blo 1375507 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B7844633 : Blo 1375507 7844633 := bstep (se 2 (by rfl) ⟨2941737, by rfl⟩ : syracuseStep 7844633 = 5883475) B5883475
theorem B2323255 : Blo 1375507 2323255 := bstep (se 1 (by rfl) ⟨1742441, by rfl⟩ : syracuseStep 2323255 = 3484883) B3484883
theorem B11752391 : Blo 1375507 11752391 := bstep (se 1 (by rfl) ⟨8814293, by rfl⟩ : syracuseStep 11752391 = 17628587) B17628587
theorem B28259927 : Blo 1375507 28259927 := bstep (se 1 (by rfl) ⟨21194945, by rfl⟩ : syracuseStep 28259927 = 42389891) B42389891
theorem B15669125 : Blo 1375507 15669125 := bstep (se 4 (by rfl) ⟨1468980, by rfl⟩ : syracuseStep 15669125 = 2937961) B2937961
theorem B13236203 : Blo 1375507 13236203 := bstep (se 1 (by rfl) ⟨9927152, by rfl⟩ : syracuseStep 13236203 = 19854305) B19854305
theorem B53663735 : Blo 1375507 53663735 := bstep (se 1 (by rfl) ⟨40247801, by rfl⟩ : syracuseStep 53663735 = 80495603) B80495603
theorem B4643297 : Blo 1375507 4643297 := bstep (se 2 (by rfl) ⟨1741236, by rfl⟩ : syracuseStep 4643297 = 3482473) B3482473
theorem B2611703 : Blo 1375507 2611703 := bstep (se 1 (by rfl) ⟨1958777, by rfl⟩ : syracuseStep 2611703 = 3917555) B3917555
theorem B35298179 : Blo 1375507 35298179 := bstep (se 1 (by rfl) ⟨26473634, by rfl⟩ : syracuseStep 35298179 = 52947269) B52947269
theorem B5225411 : Blo 1375507 5225411 := bstep (se 1 (by rfl) ⟨3919058, by rfl⟩ : syracuseStep 5225411 = 7838117) B7838117
theorem B4963463 : Blo 1375507 4963463 := bstep (se 1 (by rfl) ⟨3722597, by rfl⟩ : syracuseStep 4963463 = 7445195) B7445195
theorem B11763053 : Blo 1375507 11763053 := bstep (se 3 (by rfl) ⟨2205572, by rfl⟩ : syracuseStep 11763053 = 4411145) B4411145
theorem B57368027 : Blo 1375507 57368027 := bstep (se 1 (by rfl) ⟨43026020, by rfl⟩ : syracuseStep 57368027 = 86052041) B86052041
theorem B6610567 : Blo 1375507 6610567 := bstep (se 1 (by rfl) ⟨4957925, by rfl⟩ : syracuseStep 6610567 = 9915851) B9915851
theorem B5660351 : Blo 1375507 5660351 := bstep (se 1 (by rfl) ⟨4245263, by rfl⟩ : syracuseStep 5660351 = 8490527) B8490527
theorem B11165683 : Blo 1375507 11165683 := bstep (se 1 (by rfl) ⟨8374262, by rfl⟩ : syracuseStep 11165683 = 16748525) B16748525
theorem B1376251 : Blo 1375507 1376251 := bstep (se 1 (by rfl) ⟨1032188, by rfl⟩ : syracuseStep 1376251 = 2064377) B2064377
theorem B1376303 : Blo 1375507 1376303 := bstep (se 1 (by rfl) ⟨1032227, by rfl⟩ : syracuseStep 1376303 = 2064455) B2064455
theorem B7839827 : Blo 1375507 7839827 := bstep (se 1 (by rfl) ⟨5879870, by rfl⟩ : syracuseStep 7839827 = 11759741) B11759741
theorem B2064479 : Blo 1375507 2064479 := bstep (se 1 (by rfl) ⟨1548359, by rfl⟩ : syracuseStep 2064479 = 3096719) B3096719
theorem B4644971 : Blo 1375507 4644971 := bstep (se 1 (by rfl) ⟨3483728, by rfl⟩ : syracuseStep 4644971 = 6967457) B6967457
theorem B2064551 : Blo 1375507 2064551 := bstep (se 1 (by rfl) ⟨1548413, by rfl⟩ : syracuseStep 2064551 = 3096827) B3096827
theorem B3137723 : Blo 1375507 3137723 := bstep (se 1 (by rfl) ⟨2353292, by rfl⟩ : syracuseStep 3137723 = 4706585) B4706585
theorem B3096809 : Blo 1375507 3096809 := bstep (se 2 (by rfl) ⟨1161303, by rfl⟩ : syracuseStep 3096809 = 2322607) B2322607
theorem B2064761 : Blo 1375507 2064761 := bstep (se 2 (by rfl) ⟨774285, by rfl⟩ : syracuseStep 2064761 = 1548571) B1548571
theorem B3097079 : Blo 1375507 3097079 := bstep (se 1 (by rfl) ⟨2322809, by rfl⟩ : syracuseStep 3097079 = 4645619) B4645619
theorem B4407967 : Blo 1375507 4407967 := bstep (se 1 (by rfl) ⟨3305975, by rfl⟩ : syracuseStep 4407967 = 6611951) B6611951
theorem B4645673 : Blo 1375507 4645673 := bstep (se 2 (by rfl) ⟨1742127, by rfl⟩ : syracuseStep 4645673 = 3484255) B3484255
theorem B3097673 : Blo 1375507 3097673 := bstep (se 2 (by rfl) ⟨1161627, by rfl⟩ : syracuseStep 3097673 = 2323255) B2323255
theorem B6972641 : Blo 1375507 6972641 := bstep (se 2 (by rfl) ⟨2614740, by rfl⟩ : syracuseStep 6972641 = 5229481) B5229481
theorem B10446083 : Blo 1375507 10446083 := bstep (se 1 (by rfl) ⟨7834562, by rfl⟩ : syracuseStep 10446083 = 15669125) B15669125
theorem B6964541 : Blo 1375507 6964541 := bstep (se 3 (by rfl) ⟨1305851, by rfl⟩ : syracuseStep 6964541 = 2611703) B2611703
theorem B8824135 : Blo 1375507 8824135 := bstep (se 1 (by rfl) ⟨6618101, by rfl⟩ : syracuseStep 8824135 = 13236203) B13236203
theorem B2066057 : Blo 1375507 2066057 := bstep (se 2 (by rfl) ⟨774771, by rfl⟩ : syracuseStep 2066057 = 1549543) B1549543
theorem B3098267 : Blo 1375507 3098267 := bstep (se 1 (by rfl) ⟨2323700, by rfl⟩ : syracuseStep 3098267 = 4647401) B4647401
theorem B3483607 : Blo 1375507 3483607 := bstep (se 1 (by rfl) ⟨2612705, by rfl⟩ : syracuseStep 3483607 = 5225411) B5225411
theorem B7842035 : Blo 1375507 7842035 := bstep (se 1 (by rfl) ⟨5881526, by rfl⟩ : syracuseStep 7842035 = 11763053) B11763053
theorem B6613625 : Blo 1375507 6613625 := bstep (se 2 (by rfl) ⟨2480109, by rfl⟩ : syracuseStep 6613625 = 4960219) B4960219
theorem B14887577 : Blo 1375507 14887577 := bstep (se 2 (by rfl) ⟨5582841, by rfl⟩ : syracuseStep 14887577 = 11165683) B11165683
theorem B26446571 : Blo 1375507 26446571 := bstep (se 1 (by rfl) ⟨19834928, by rfl⟩ : syracuseStep 26446571 = 39669857) B39669857
theorem B5229299 : Blo 1375507 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B2321183 : Blo 1375507 2321183 := bstep (se 1 (by rfl) ⟨1740887, by rfl⟩ : syracuseStep 2321183 = 3481775) B3481775
theorem B4647887 : Blo 1375507 4647887 := bstep (se 1 (by rfl) ⟨3485915, by rfl⟩ : syracuseStep 4647887 = 6971831) B6971831
theorem B13233127 : Blo 1375507 13233127 := bstep (se 1 (by rfl) ⟨9924845, by rfl⟩ : syracuseStep 13233127 = 19849691) B19849691
theorem B178564175 : Blo 1375507 178564175 := bstep (se 1 (by rfl) ⟨133923131, by rfl⟩ : syracuseStep 178564175 = 267846263) B267846263
theorem B12897389 : Blo 1375507 12897389 := bstep (se 3 (by rfl) ⟨2418260, by rfl⟩ : syracuseStep 12897389 = 4836521) B4836521
theorem B5229755 : Blo 1375507 5229755 := bstep (se 1 (by rfl) ⟨3922316, by rfl⟩ : syracuseStep 5229755 = 7844633) B7844633
theorem B7834927 : Blo 1375507 7834927 := bstep (se 1 (by rfl) ⟨5876195, by rfl⟩ : syracuseStep 7834927 = 11752391) B11752391
theorem B5582143 : Blo 1375507 5582143 := bstep (se 1 (by rfl) ⟨4186607, by rfl⟩ : syracuseStep 5582143 = 8373215) B8373215
theorem B19083239 : Blo 1375507 19083239 := bstep (se 1 (by rfl) ⟨14312429, by rfl⟩ : syracuseStep 19083239 = 28624859) B28624859
theorem B6615067 : Blo 1375507 6615067 := bstep (se 1 (by rfl) ⟨4961300, by rfl⟩ : syracuseStep 6615067 = 9922601) B9922601
theorem B2322587 : Blo 1375507 2322587 := bstep (se 1 (by rfl) ⟨1741940, by rfl⟩ : syracuseStep 2322587 = 3483881) B3483881
theorem B8368639 : Blo 1375507 8368639 := bstep (se 1 (by rfl) ⟨6276479, by rfl⟩ : syracuseStep 8368639 = 12552959) B12552959
theorem B23532119 : Blo 1375507 23532119 := bstep (se 1 (by rfl) ⟨17649089, by rfl⟩ : syracuseStep 23532119 = 35298179) B35298179
theorem B38245351 : Blo 1375507 38245351 := bstep (se 1 (by rfl) ⟨28684013, by rfl⟩ : syracuseStep 38245351 = 57368027) B57368027
theorem B3773567 : Blo 1375507 3773567 := bstep (se 1 (by rfl) ⟨2830175, by rfl⟩ : syracuseStep 3773567 = 5660351) B5660351
theorem B143103293 : Blo 1375507 143103293 := bstep (se 3 (by rfl) ⟨26831867, by rfl⟩ : syracuseStep 143103293 = 53663735) B53663735
theorem B4961731 : Blo 1375507 4961731 := bstep (se 1 (by rfl) ⟨3721298, by rfl⟩ : syracuseStep 4961731 = 7442597) B7442597
theorem B6968915 : Blo 1375507 6968915 := bstep (se 1 (by rfl) ⟨5226686, by rfl⟩ : syracuseStep 6968915 = 10453373) B10453373
theorem B21198523 : Blo 1375507 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B44636123 : Blo 1375507 44636123 := bstep (se 1 (by rfl) ⟨33477092, by rfl⟩ : syracuseStep 44636123 = 66954185) B66954185
theorem B225957923 : Blo 1375507 225957923 := bstep (se 1 (by rfl) ⟨169468442, by rfl⟩ : syracuseStep 225957923 = 338936885) B338936885
theorem B29775923 : Blo 1375507 29775923 := bstep (se 1 (by rfl) ⟨22331942, by rfl⟩ : syracuseStep 29775923 = 44663885) B44663885
theorem B7837843 : Blo 1375507 7837843 := bstep (se 1 (by rfl) ⟨5878382, by rfl⟩ : syracuseStep 7837843 = 11756765) B11756765
theorem B18839951 : Blo 1375507 18839951 := bstep (se 1 (by rfl) ⟨14129963, by rfl⟩ : syracuseStep 18839951 = 28259927) B28259927
theorem B3095531 : Blo 1375507 3095531 := bstep (se 1 (by rfl) ⟨2321648, by rfl⟩ : syracuseStep 3095531 = 4643297) B4643297
theorem B4643945 : Blo 1375507 4643945 := bstep (se 2 (by rfl) ⟨1741479, by rfl⟩ : syracuseStep 4643945 = 3482959) B3482959
theorem B6610031 : Blo 1375507 6610031 := bstep (se 1 (by rfl) ⟨4957523, by rfl⟩ : syracuseStep 6610031 = 9915047) B9915047
theorem B3308975 : Blo 1375507 3308975 := bstep (se 1 (by rfl) ⟨2481731, by rfl⟩ : syracuseStep 3308975 = 4963463) B4963463
theorem B8814089 : Blo 1375507 8814089 := bstep (se 2 (by rfl) ⟨3305283, by rfl⟩ : syracuseStep 8814089 = 6610567) B6610567
theorem B2612873 : Blo 1375507 2612873 := bstep (se 2 (by rfl) ⟨979827, by rfl⟩ : syracuseStep 2612873 = 1959655) B1959655
theorem B2613055 : Blo 1375507 2613055 := bstep (se 1 (by rfl) ⟨1959791, by rfl⟩ : syracuseStep 2613055 = 3919583) B3919583
theorem B5226551 : Blo 1375507 5226551 := bstep (se 1 (by rfl) ⟨3919913, by rfl⟩ : syracuseStep 5226551 = 7839827) B7839827
theorem B1376319 : Blo 1375507 1376319 := bstep (se 1 (by rfl) ⟨1032239, by rfl⟩ : syracuseStep 1376319 = 2064479) B2064479
theorem B3096647 : Blo 1375507 3096647 := bstep (se 1 (by rfl) ⟨2322485, by rfl⟩ : syracuseStep 3096647 = 4644971) B4644971
theorem B1548391 : Blo 1375507 1548391 := bstep (se 1 (by rfl) ⟨1161293, by rfl⟩ : syracuseStep 1548391 = 2322587) B2322587
theorem B1376367 : Blo 1375507 1376367 := bstep (se 1 (by rfl) ⟨1032275, by rfl⟩ : syracuseStep 1376367 = 2064551) B2064551
theorem B2064539 : Blo 1375507 2064539 := bstep (se 1 (by rfl) ⟨1548404, by rfl⟩ : syracuseStep 2064539 = 3096809) B3096809
theorem B1376507 : Blo 1375507 1376507 := bstep (se 1 (by rfl) ⟨1032380, by rfl⟩ : syracuseStep 1376507 = 2064761) B2064761
theorem B2064719 : Blo 1375507 2064719 := bstep (se 1 (by rfl) ⟨1548539, by rfl⟩ : syracuseStep 2064719 = 3097079) B3097079
theorem B15688079 : Blo 1375507 15688079 := bstep (se 1 (by rfl) ⟨11766059, by rfl⟩ : syracuseStep 15688079 = 23532119) B23532119
theorem B3097115 : Blo 1375507 3097115 := bstep (se 1 (by rfl) ⟨2322836, by rfl⟩ : syracuseStep 3097115 = 4645673) B4645673
theorem B2065115 : Blo 1375507 2065115 := bstep (se 1 (by rfl) ⟨1548836, by rfl⟩ : syracuseStep 2065115 = 3097673) B3097673
theorem B2515711 : Blo 1375507 2515711 := bstep (se 1 (by rfl) ⟨1886783, by rfl⟩ : syracuseStep 2515711 = 3773567) B3773567
theorem B6964055 : Blo 1375507 6964055 := bstep (se 1 (by rfl) ⟨5223041, by rfl⟩ : syracuseStep 6964055 = 10446083) B10446083
theorem B4645943 : Blo 1375507 4645943 := bstep (se 1 (by rfl) ⟨3484457, by rfl⟩ : syracuseStep 4645943 = 6968915) B6968915
theorem B1377371 : Blo 1375507 1377371 := bstep (se 1 (by rfl) ⟨1033028, by rfl⟩ : syracuseStep 1377371 = 2066057) B2066057
theorem B2065511 : Blo 1375507 2065511 := bstep (se 1 (by rfl) ⟨1549133, by rfl⟩ : syracuseStep 2065511 = 3098267) B3098267
theorem B19850615 : Blo 1375507 19850615 := bstep (se 1 (by rfl) ⟨14887961, by rfl⟩ : syracuseStep 19850615 = 29775923) B29775923
theorem B5228023 : Blo 1375507 5228023 := bstep (se 1 (by rfl) ⟨3921017, by rfl⟩ : syracuseStep 5228023 = 7842035) B7842035
theorem B12559967 : Blo 1375507 12559967 := bstep (se 1 (by rfl) ⟨9419975, by rfl⟩ : syracuseStep 12559967 = 18839951) B18839951
theorem B10446569 : Blo 1375507 10446569 := bstep (se 2 (by rfl) ⟨3917463, by rfl⟩ : syracuseStep 10446569 = 7834927) B7834927
theorem B4409083 : Blo 1375507 4409083 := bstep (se 1 (by rfl) ⟨3306812, by rfl⟩ : syracuseStep 4409083 = 6613625) B6613625
theorem B11765513 : Blo 1375507 11765513 := bstep (se 2 (by rfl) ⟨4412067, by rfl⟩ : syracuseStep 11765513 = 8824135) B8824135
theorem B17631047 : Blo 1375507 17631047 := bstep (se 1 (by rfl) ⟨13223285, by rfl⟩ : syracuseStep 17631047 = 26446571) B26446571
theorem B3098591 : Blo 1375507 3098591 := bstep (se 1 (by rfl) ⟨2323943, by rfl⟩ : syracuseStep 3098591 = 4647887) B4647887
theorem B28264697 : Blo 1375507 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B2205983 : Blo 1375507 2205983 := bstep (se 1 (by rfl) ⟨1654487, by rfl⟩ : syracuseStep 2205983 = 3308975) B3308975
theorem B5876059 : Blo 1375507 5876059 := bstep (se 1 (by rfl) ⟨4407044, by rfl⟩ : syracuseStep 5876059 = 8814089) B8814089
theorem B3484073 : Blo 1375507 3484073 := bstep (se 2 (by rfl) ⟨1306527, by rfl⟩ : syracuseStep 3484073 = 2613055) B2613055
theorem B44632741 : Blo 1375507 44632741 := bstep (se 4 (by rfl) ⟨4184319, by rfl⟩ : syracuseStep 44632741 = 8368639) B8368639
theorem B2091815 : Blo 1375507 2091815 := bstep (se 1 (by rfl) ⟨1568861, by rfl⟩ : syracuseStep 2091815 = 3137723) B3137723
theorem B4648427 : Blo 1375507 4648427 := bstep (se 1 (by rfl) ⟨3486320, by rfl⟩ : syracuseStep 4648427 = 6972641) B6972641
theorem B5877289 : Blo 1375507 5877289 := bstep (se 2 (by rfl) ⟨2203983, by rfl⟩ : syracuseStep 5877289 = 4407967) B4407967
theorem B29757415 : Blo 1375507 29757415 := bstep (se 1 (by rfl) ⟨22318061, by rfl⟩ : syracuseStep 29757415 = 44636123) B44636123
theorem B150638615 : Blo 1375507 150638615 := bstep (se 1 (by rfl) ⟨112978961, by rfl⟩ : syracuseStep 150638615 = 225957923) B225957923
theorem B7442857 : Blo 1375507 7442857 := bstep (se 2 (by rfl) ⟨2791071, by rfl⟩ : syracuseStep 7442857 = 5582143) B5582143
theorem B9925051 : Blo 1375507 9925051 := bstep (se 1 (by rfl) ⟨7443788, by rfl⟩ : syracuseStep 9925051 = 14887577) B14887577
theorem B3486199 : Blo 1375507 3486199 := bstep (se 1 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 3486199 = 5229299) B5229299
theorem B6615641 : Blo 1375507 6615641 := bstep (se 2 (by rfl) ⟨2480865, by rfl⟩ : syracuseStep 6615641 = 4961731) B4961731
theorem B119042783 : Blo 1375507 119042783 := bstep (se 1 (by rfl) ⟨89282087, by rfl⟩ : syracuseStep 119042783 = 178564175) B178564175
theorem B8598259 : Blo 1375507 8598259 := bstep (se 1 (by rfl) ⟨6448694, by rfl⟩ : syracuseStep 8598259 = 12897389) B12897389
theorem B3486503 : Blo 1375507 3486503 := bstep (se 1 (by rfl) ⟨2614877, by rfl⟩ : syracuseStep 3486503 = 5229755) B5229755
theorem B1741915 : Blo 1375507 1741915 := bstep (se 1 (by rfl) ⟨1306436, by rfl⟩ : syracuseStep 1741915 = 2612873) B2612873
theorem B8820089 : Blo 1375507 8820089 := bstep (se 2 (by rfl) ⟨3307533, by rfl⟩ : syracuseStep 8820089 = 6615067) B6615067
theorem B10450457 : Blo 1375507 10450457 := bstep (se 2 (by rfl) ⟨3918921, by rfl⟩ : syracuseStep 10450457 = 7837843) B7837843
theorem B4643027 : Blo 1375507 4643027 := bstep (se 1 (by rfl) ⟨3482270, by rfl⟩ : syracuseStep 4643027 = 6964541) B6964541
theorem B95402195 : Blo 1375507 95402195 := bstep (se 1 (by rfl) ⟨71551646, by rfl⟩ : syracuseStep 95402195 = 143103293) B143103293
theorem B50993801 : Blo 1375507 50993801 := bstep (se 2 (by rfl) ⟨19122675, by rfl⟩ : syracuseStep 50993801 = 38245351) B38245351
theorem B17644169 : Blo 1375507 17644169 := bstep (se 2 (by rfl) ⟨6616563, by rfl⟩ : syracuseStep 17644169 = 13233127) B13233127
theorem B1547455 : Blo 1375507 1547455 := bstep (se 1 (by rfl) ⟨1160591, by rfl⟩ : syracuseStep 1547455 = 2321183) B2321183
theorem B2063687 : Blo 1375507 2063687 := bstep (se 1 (by rfl) ⟨1547765, by rfl⟩ : syracuseStep 2063687 = 3095531) B3095531
theorem B3095963 : Blo 1375507 3095963 := bstep (se 1 (by rfl) ⟨2321972, by rfl⟩ : syracuseStep 3095963 = 4643945) B4643945
theorem B4406687 : Blo 1375507 4406687 := bstep (se 1 (by rfl) ⟨3305015, by rfl⟩ : syracuseStep 4406687 = 6610031) B6610031
theorem B4644809 : Blo 1375507 4644809 := bstep (se 2 (by rfl) ⟨1741803, by rfl⟩ : syracuseStep 4644809 = 3483607) B3483607
theorem B12722159 : Blo 1375507 12722159 := bstep (se 1 (by rfl) ⟨9541619, by rfl⟩ : syracuseStep 12722159 = 19083239) B19083239
theorem B100425743 : Blo 1375507 100425743 := bstep (se 1 (by rfl) ⟨75319307, by rfl⟩ : syracuseStep 100425743 = 150638615) B150638615
theorem B2064431 : Blo 1375507 2064431 := bstep (se 1 (by rfl) ⟨1548323, by rfl⟩ : syracuseStep 2064431 = 3096647) B3096647
theorem B1376359 : Blo 1375507 1376359 := bstep (se 1 (by rfl) ⟨1032269, by rfl⟩ : syracuseStep 1376359 = 2064539) B2064539
theorem B2064521 : Blo 1375507 2064521 := bstep (se 2 (by rfl) ⟨774195, by rfl⟩ : syracuseStep 2064521 = 1548391) B1548391
theorem B1376479 : Blo 1375507 1376479 := bstep (se 1 (by rfl) ⟨1032359, by rfl⟩ : syracuseStep 1376479 = 2064719) B2064719
theorem B2064743 : Blo 1375507 2064743 := bstep (se 1 (by rfl) ⟨1548557, by rfl⟩ : syracuseStep 2064743 = 3097115) B3097115
theorem B1376743 : Blo 1375507 1376743 := bstep (se 1 (by rfl) ⟨1032557, by rfl⟩ : syracuseStep 1376743 = 2065115) B2065115
theorem B3097295 : Blo 1375507 3097295 := bstep (se 1 (by rfl) ⟨2322971, by rfl⟩ : syracuseStep 3097295 = 4645943) B4645943
theorem B1377007 : Blo 1375507 1377007 := bstep (se 1 (by rfl) ⟨1032755, by rfl⟩ : syracuseStep 1377007 = 2065511) B2065511
theorem B8373311 : Blo 1375507 8373311 := bstep (se 1 (by rfl) ⟨6279983, by rfl⟩ : syracuseStep 8373311 = 12559967) B12559967
theorem B6964379 : Blo 1375507 6964379 := bstep (se 1 (by rfl) ⟨5223284, by rfl⟩ : syracuseStep 6964379 = 10446569) B10446569
theorem B2065727 : Blo 1375507 2065727 := bstep (se 1 (by rfl) ⟨1549295, by rfl⟩ : syracuseStep 2065727 = 3098591) B3098591
theorem B18843131 : Blo 1375507 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B1394543 : Blo 1375507 1394543 := bstep (se 1 (by rfl) ⟨1045907, by rfl⟩ : syracuseStep 1394543 = 2091815) B2091815
theorem B3098951 : Blo 1375507 3098951 := bstep (se 1 (by rfl) ⟨2324213, by rfl⟩ : syracuseStep 3098951 = 4648427) B4648427
theorem B39676553 : Blo 1375507 39676553 := bstep (se 2 (by rfl) ⟨14878707, by rfl⟩ : syracuseStep 39676553 = 29757415) B29757415
theorem B8481439 : Blo 1375507 8481439 := bstep (se 1 (by rfl) ⟨6361079, by rfl⟩ : syracuseStep 8481439 = 12722159) B12722159
theorem B3484367 : Blo 1375507 3484367 := bstep (se 1 (by rfl) ⟨2613275, by rfl⟩ : syracuseStep 3484367 = 5226551) B5226551
theorem B7834745 : Blo 1375507 7834745 := bstep (se 2 (by rfl) ⟨2938029, by rfl⟩ : syracuseStep 7834745 = 5876059) B5876059
theorem B9923809 : Blo 1375507 9923809 := bstep (se 2 (by rfl) ⟨3721428, by rfl⟩ : syracuseStep 9923809 = 7442857) B7442857
theorem B13233401 : Blo 1375507 13233401 := bstep (se 2 (by rfl) ⟨4962525, by rfl⟩ : syracuseStep 13233401 = 9925051) B9925051
theorem B4648265 : Blo 1375507 4648265 := bstep (se 2 (by rfl) ⟨1743099, by rfl⟩ : syracuseStep 4648265 = 3486199) B3486199
theorem B59510321 : Blo 1375507 59510321 := bstep (se 2 (by rfl) ⟨22316370, by rfl⟩ : syracuseStep 59510321 = 44632741) B44632741
theorem B13233743 : Blo 1375507 13233743 := bstep (se 1 (by rfl) ⟨9925307, by rfl⟩ : syracuseStep 13233743 = 19850615) B19850615
theorem B11464345 : Blo 1375507 11464345 := bstep (se 2 (by rfl) ⟨4299129, by rfl⟩ : syracuseStep 11464345 = 8598259) B8598259
theorem B3354281 : Blo 1375507 3354281 := bstep (se 2 (by rfl) ⟨1257855, by rfl⟩ : syracuseStep 3354281 = 2515711) B2515711
theorem B6966971 : Blo 1375507 6966971 := bstep (se 1 (by rfl) ⟨5225228, by rfl⟩ : syracuseStep 6966971 = 10450457) B10450457
theorem B7843675 : Blo 1375507 7843675 := bstep (se 1 (by rfl) ⟨5882756, by rfl⟩ : syracuseStep 7843675 = 11765513) B11765513
theorem B2322553 : Blo 1375507 2322553 := bstep (se 2 (by rfl) ⟨870957, by rfl⟩ : syracuseStep 2322553 = 1741915) B1741915
theorem B1470655 : Blo 1375507 1470655 := bstep (se 1 (by rfl) ⟨1102991, by rfl⟩ : syracuseStep 1470655 = 2205983) B2205983
theorem B17641709 : Blo 1375507 17641709 := bstep (se 3 (by rfl) ⟨3307820, by rfl⟩ : syracuseStep 17641709 = 6615641) B6615641
theorem B2322715 : Blo 1375507 2322715 := bstep (se 1 (by rfl) ⟨1742036, by rfl⟩ : syracuseStep 2322715 = 3484073) B3484073
theorem B7836385 : Blo 1375507 7836385 := bstep (se 2 (by rfl) ⟨2938644, by rfl⟩ : syracuseStep 7836385 = 5877289) B5877289
theorem B2937791 : Blo 1375507 2937791 := bstep (se 1 (by rfl) ⟨2203343, by rfl⟩ : syracuseStep 2937791 = 4406687) B4406687
theorem B5878777 : Blo 1375507 5878777 := bstep (se 2 (by rfl) ⟨2204541, by rfl⟩ : syracuseStep 5878777 = 4409083) B4409083
theorem B10458719 : Blo 1375507 10458719 := bstep (se 1 (by rfl) ⟨7844039, by rfl⟩ : syracuseStep 10458719 = 15688079) B15688079
theorem B79361855 : Blo 1375507 79361855 := bstep (se 1 (by rfl) ⟨59521391, by rfl⟩ : syracuseStep 79361855 = 119042783) B119042783
theorem B2324335 : Blo 1375507 2324335 := bstep (se 1 (by rfl) ⟨1743251, by rfl⟩ : syracuseStep 2324335 = 3486503) B3486503
theorem B4642703 : Blo 1375507 4642703 := bstep (se 1 (by rfl) ⟨3482027, by rfl⟩ : syracuseStep 4642703 = 6964055) B6964055
theorem B5880059 : Blo 1375507 5880059 := bstep (se 1 (by rfl) ⟨4410044, by rfl⟩ : syracuseStep 5880059 = 8820089) B8820089
theorem B11754031 : Blo 1375507 11754031 := bstep (se 1 (by rfl) ⟨8815523, by rfl⟩ : syracuseStep 11754031 = 17631047) B17631047
theorem B3095351 : Blo 1375507 3095351 := bstep (se 1 (by rfl) ⟨2321513, by rfl⟩ : syracuseStep 3095351 = 4643027) B4643027
theorem B63601463 : Blo 1375507 63601463 := bstep (se 1 (by rfl) ⟨47701097, by rfl⟩ : syracuseStep 63601463 = 95402195) B95402195
theorem B2063273 : Blo 1375507 2063273 := bstep (se 2 (by rfl) ⟨773727, by rfl⟩ : syracuseStep 2063273 = 1547455) B1547455
theorem B33995867 : Blo 1375507 33995867 := bstep (se 1 (by rfl) ⟨25496900, by rfl⟩ : syracuseStep 33995867 = 50993801) B50993801
theorem B11762779 : Blo 1375507 11762779 := bstep (se 1 (by rfl) ⟨8822084, by rfl⟩ : syracuseStep 11762779 = 17644169) B17644169
theorem B6970697 : Blo 1375507 6970697 := bstep (se 2 (by rfl) ⟨2614011, by rfl⟩ : syracuseStep 6970697 = 5228023) B5228023
theorem B1375791 : Blo 1375507 1375791 := bstep (se 1 (by rfl) ⟨1031843, by rfl⟩ : syracuseStep 1375791 = 2063687) B2063687
theorem B2063975 : Blo 1375507 2063975 := bstep (se 1 (by rfl) ⟨1547981, by rfl⟩ : syracuseStep 2063975 = 3095963) B3095963
theorem B3096539 : Blo 1375507 3096539 := bstep (se 1 (by rfl) ⟨2322404, by rfl⟩ : syracuseStep 3096539 = 4644809) B4644809
theorem B1376287 : Blo 1375507 1376287 := bstep (se 1 (by rfl) ⟨1032215, by rfl⟩ : syracuseStep 1376287 = 2064431) B2064431
theorem B1376347 : Blo 1375507 1376347 := bstep (se 1 (by rfl) ⟨1032260, by rfl⟩ : syracuseStep 1376347 = 2064521) B2064521
theorem B3096737 : Blo 1375507 3096737 := bstep (se 2 (by rfl) ⟨1161276, by rfl⟩ : syracuseStep 3096737 = 2322553) B2322553
theorem B1376495 : Blo 1375507 1376495 := bstep (se 1 (by rfl) ⟨1032371, by rfl⟩ : syracuseStep 1376495 = 2064743) B2064743
theorem B3096953 : Blo 1375507 3096953 := bstep (se 2 (by rfl) ⟨1161357, by rfl⟩ : syracuseStep 3096953 = 2322715) B2322715
theorem B2064863 : Blo 1375507 2064863 := bstep (se 1 (by rfl) ⟨1548647, by rfl⟩ : syracuseStep 2064863 = 3097295) B3097295
theorem B1958527 : Blo 1375507 1958527 := bstep (se 1 (by rfl) ⟨1468895, by rfl⟩ : syracuseStep 1958527 = 2937791) B2937791
theorem B15672041 : Blo 1375507 15672041 := bstep (se 2 (by rfl) ⟨5877015, by rfl⟩ : syracuseStep 15672041 = 11754031) B11754031
theorem B1377151 : Blo 1375507 1377151 := bstep (se 1 (by rfl) ⟨1032863, by rfl⟩ : syracuseStep 1377151 = 2065727) B2065727
theorem B6972479 : Blo 1375507 6972479 := bstep (se 1 (by rfl) ⟨5229359, by rfl⟩ : syracuseStep 6972479 = 10458719) B10458719
theorem B2065967 : Blo 1375507 2065967 := bstep (se 1 (by rfl) ⟨1549475, by rfl⟩ : syracuseStep 2065967 = 3098951) B3098951
theorem B13231745 : Blo 1375507 13231745 := bstep (se 2 (by rfl) ⟨4961904, by rfl⟩ : syracuseStep 13231745 = 9923809) B9923809
theorem B4647131 : Blo 1375507 4647131 := bstep (se 1 (by rfl) ⟨3485348, by rfl⟩ : syracuseStep 4647131 = 6970697) B6970697
theorem B3098843 : Blo 1375507 3098843 := bstep (se 1 (by rfl) ⟨2324132, by rfl⟩ : syracuseStep 3098843 = 4648265) B4648265
theorem B3099113 : Blo 1375507 3099113 := bstep (se 2 (by rfl) ⟨1162167, by rfl⟩ : syracuseStep 3099113 = 2324335) B2324335
theorem B90655645 : Blo 1375507 90655645 := bstep (se 3 (by rfl) ⟨16997933, by rfl⟩ : syracuseStep 90655645 = 33995867) B33995867
theorem B5582207 : Blo 1375507 5582207 := bstep (se 1 (by rfl) ⟨4186655, by rfl⟩ : syracuseStep 5582207 = 8373311) B8373311
theorem B11308585 : Blo 1375507 11308585 := bstep (se 2 (by rfl) ⟨4240719, by rfl⟩ : syracuseStep 11308585 = 8481439) B8481439
theorem B10448513 : Blo 1375507 10448513 := bstep (se 2 (by rfl) ⟨3918192, by rfl⟩ : syracuseStep 10448513 = 7836385) B7836385
theorem B7843493 : Blo 1375507 7843493 := bstep (se 4 (by rfl) ⟨735327, by rfl⟩ : syracuseStep 7843493 = 1470655) B1470655
theorem B12562087 : Blo 1375507 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B52907903 : Blo 1375507 52907903 := bstep (se 1 (by rfl) ⟨39680927, by rfl⟩ : syracuseStep 52907903 = 79361855) B79361855
theorem B15683705 : Blo 1375507 15683705 := bstep (se 2 (by rfl) ⟨5881389, by rfl⟩ : syracuseStep 15683705 = 11762779) B11762779
theorem B3920039 : Blo 1375507 3920039 := bstep (se 1 (by rfl) ⟨2940029, by rfl⟩ : syracuseStep 3920039 = 5880059) B5880059
theorem B2322911 : Blo 1375507 2322911 := bstep (se 1 (by rfl) ⟨1742183, by rfl⟩ : syracuseStep 2322911 = 3484367) B3484367
theorem B5223163 : Blo 1375507 5223163 := bstep (se 1 (by rfl) ⟨3917372, by rfl⟩ : syracuseStep 5223163 = 7834745) B7834745
theorem B169603901 : Blo 1375507 169603901 := bstep (se 3 (by rfl) ⟨31800731, by rfl⟩ : syracuseStep 169603901 = 63601463) B63601463
theorem B10458233 : Blo 1375507 10458233 := bstep (se 2 (by rfl) ⟨3921837, by rfl⟩ : syracuseStep 10458233 = 7843675) B7843675
theorem B66950495 : Blo 1375507 66950495 := bstep (se 1 (by rfl) ⟨50212871, by rfl⟩ : syracuseStep 66950495 = 100425743) B100425743
theorem B11761139 : Blo 1375507 11761139 := bstep (se 1 (by rfl) ⟨8820854, by rfl⟩ : syracuseStep 11761139 = 17641709) B17641709
theorem B4642919 : Blo 1375507 4642919 := bstep (se 1 (by rfl) ⟨3482189, by rfl⟩ : syracuseStep 4642919 = 6964379) B6964379
theorem B3095135 : Blo 1375507 3095135 := bstep (se 1 (by rfl) ⟨2321351, by rfl⟩ : syracuseStep 3095135 = 4642703) B4642703
theorem B7838369 : Blo 1375507 7838369 := bstep (se 2 (by rfl) ⟨2939388, by rfl⟩ : syracuseStep 7838369 = 5878777) B5878777
theorem B26451035 : Blo 1375507 26451035 := bstep (se 1 (by rfl) ⟨19838276, by rfl⟩ : syracuseStep 26451035 = 39676553) B39676553
theorem B2063567 : Blo 1375507 2063567 := bstep (se 1 (by rfl) ⟨1547675, by rfl⟩ : syracuseStep 2063567 = 3095351) B3095351
theorem B1375515 : Blo 1375507 1375515 := bstep (se 1 (by rfl) ⟨1031636, by rfl⟩ : syracuseStep 1375515 = 2063273) B2063273
theorem B8822267 : Blo 1375507 8822267 := bstep (se 1 (by rfl) ⟨6616700, by rfl⟩ : syracuseStep 8822267 = 13233401) B13233401
theorem B15285793 : Blo 1375507 15285793 := bstep (se 2 (by rfl) ⟨5732172, by rfl⟩ : syracuseStep 15285793 = 11464345) B11464345
theorem B3718781 : Blo 1375507 3718781 := bstep (se 3 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 3718781 = 1394543) B1394543
theorem B39673547 : Blo 1375507 39673547 := bstep (se 1 (by rfl) ⟨29755160, by rfl⟩ : syracuseStep 39673547 = 59510321) B59510321
theorem B8822495 : Blo 1375507 8822495 := bstep (se 1 (by rfl) ⟨6616871, by rfl⟩ : syracuseStep 8822495 = 13233743) B13233743
theorem B1375983 : Blo 1375507 1375983 := bstep (se 1 (by rfl) ⟨1031987, by rfl⟩ : syracuseStep 1375983 = 2063975) B2063975
theorem B2236187 : Blo 1375507 2236187 := bstep (se 1 (by rfl) ⟨1677140, by rfl⟩ : syracuseStep 2236187 = 3354281) B3354281
theorem B4644647 : Blo 1375507 4644647 := bstep (se 1 (by rfl) ⟨3483485, by rfl⟩ : syracuseStep 4644647 = 6966971) B6966971
theorem B2064359 : Blo 1375507 2064359 := bstep (se 1 (by rfl) ⟨1548269, by rfl⟩ : syracuseStep 2064359 = 3096539) B3096539
theorem B2064491 : Blo 1375507 2064491 := bstep (se 1 (by rfl) ⟨1548368, by rfl⟩ : syracuseStep 2064491 = 3096737) B3096737
theorem B2613359 : Blo 1375507 2613359 := bstep (se 1 (by rfl) ⟨1960019, by rfl⟩ : syracuseStep 2613359 = 3920039) B3920039
theorem B2064635 : Blo 1375507 2064635 := bstep (se 1 (by rfl) ⟨1548476, by rfl⟩ : syracuseStep 2064635 = 3096953) B3096953
theorem B1548607 : Blo 1375507 1548607 := bstep (se 1 (by rfl) ⟨1161455, by rfl⟩ : syracuseStep 1548607 = 2322911) B2322911
theorem B1376575 : Blo 1375507 1376575 := bstep (se 1 (by rfl) ⟨1032431, by rfl⟩ : syracuseStep 1376575 = 2064863) B2064863
theorem B6972155 : Blo 1375507 6972155 := bstep (se 1 (by rfl) ⟨5229116, by rfl⟩ : syracuseStep 6972155 = 10458233) B10458233
theorem B6964217 : Blo 1375507 6964217 := bstep (se 2 (by rfl) ⟨2611581, by rfl⟩ : syracuseStep 6964217 = 5223163) B5223163
theorem B7840759 : Blo 1375507 7840759 := bstep (se 1 (by rfl) ⟨5880569, by rfl⟩ : syracuseStep 7840759 = 11761139) B11761139
theorem B1377311 : Blo 1375507 1377311 := bstep (se 1 (by rfl) ⟨1032983, by rfl⟩ : syracuseStep 1377311 = 2065967) B2065967
theorem B120874193 : Blo 1375507 120874193 := bstep (se 2 (by rfl) ⟨45327822, by rfl⟩ : syracuseStep 120874193 = 90655645) B90655645
theorem B3098087 : Blo 1375507 3098087 := bstep (se 1 (by rfl) ⟨2323565, by rfl⟩ : syracuseStep 3098087 = 4647131) B4647131
theorem B2065895 : Blo 1375507 2065895 := bstep (se 1 (by rfl) ⟨1549421, by rfl⟩ : syracuseStep 2065895 = 3098843) B3098843
theorem B2066075 : Blo 1375507 2066075 := bstep (se 1 (by rfl) ⟨1549556, by rfl⟩ : syracuseStep 2066075 = 3099113) B3099113
theorem B3721471 : Blo 1375507 3721471 := bstep (se 1 (by rfl) ⟨2791103, by rfl⟩ : syracuseStep 3721471 = 5582207) B5582207
theorem B6965675 : Blo 1375507 6965675 := bstep (se 1 (by rfl) ⟨5224256, by rfl⟩ : syracuseStep 6965675 = 10448513) B10448513
theorem B5228995 : Blo 1375507 5228995 := bstep (se 1 (by rfl) ⟨3921746, by rfl⟩ : syracuseStep 5228995 = 7843493) B7843493
theorem B10455803 : Blo 1375507 10455803 := bstep (se 1 (by rfl) ⟨7841852, by rfl⟩ : syracuseStep 10455803 = 15683705) B15683705
theorem B10448027 : Blo 1375507 10448027 := bstep (se 1 (by rfl) ⟨7836020, by rfl⟩ : syracuseStep 10448027 = 15672041) B15672041
theorem B113069267 : Blo 1375507 113069267 := bstep (se 1 (by rfl) ⟨84801950, by rfl⟩ : syracuseStep 113069267 = 169603901) B169603901
theorem B4648319 : Blo 1375507 4648319 := bstep (se 1 (by rfl) ⟨3486239, by rfl⟩ : syracuseStep 4648319 = 6972479) B6972479
theorem B44633663 : Blo 1375507 44633663 := bstep (se 1 (by rfl) ⟨33475247, by rfl⟩ : syracuseStep 44633663 = 66950495) B66950495
theorem B15078113 : Blo 1375507 15078113 := bstep (se 2 (by rfl) ⟨5654292, by rfl⟩ : syracuseStep 15078113 = 11308585) B11308585
theorem B17634023 : Blo 1375507 17634023 := bstep (se 1 (by rfl) ⟨13225517, by rfl⟩ : syracuseStep 17634023 = 26451035) B26451035
theorem B16749449 : Blo 1375507 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B2479187 : Blo 1375507 2479187 := bstep (se 1 (by rfl) ⟨1859390, by rfl⟩ : syracuseStep 2479187 = 3718781) B3718781
theorem B26449031 : Blo 1375507 26449031 := bstep (se 1 (by rfl) ⟨19836773, by rfl⟩ : syracuseStep 26449031 = 39673547) B39673547
theorem B35271935 : Blo 1375507 35271935 := bstep (se 1 (by rfl) ⟨26453951, by rfl⟩ : syracuseStep 35271935 = 52907903) B52907903
theorem B2611369 : Blo 1375507 2611369 := bstep (se 2 (by rfl) ⟨979263, by rfl⟩ : syracuseStep 2611369 = 1958527) B1958527
theorem B8821163 : Blo 1375507 8821163 := bstep (se 1 (by rfl) ⟨6615872, by rfl⟩ : syracuseStep 8821163 = 13231745) B13231745
theorem B3095279 : Blo 1375507 3095279 := bstep (se 1 (by rfl) ⟨2321459, by rfl⟩ : syracuseStep 3095279 = 4642919) B4642919
theorem B2063423 : Blo 1375507 2063423 := bstep (se 1 (by rfl) ⟨1547567, by rfl⟩ : syracuseStep 2063423 = 3095135) B3095135
theorem B5225579 : Blo 1375507 5225579 := bstep (se 1 (by rfl) ⟨3919184, by rfl⟩ : syracuseStep 5225579 = 7838369) B7838369
theorem B20381057 : Blo 1375507 20381057 := bstep (se 2 (by rfl) ⟨7642896, by rfl⟩ : syracuseStep 20381057 = 15285793) B15285793
theorem B5963165 : Blo 1375507 5963165 := bstep (se 3 (by rfl) ⟨1118093, by rfl⟩ : syracuseStep 5963165 = 2236187) B2236187
theorem B1375711 : Blo 1375507 1375711 := bstep (se 1 (by rfl) ⟨1031783, by rfl⟩ : syracuseStep 1375711 = 2063567) B2063567
theorem B5881511 : Blo 1375507 5881511 := bstep (se 1 (by rfl) ⟨4411133, by rfl⟩ : syracuseStep 5881511 = 8822267) B8822267
theorem B5881663 : Blo 1375507 5881663 := bstep (se 1 (by rfl) ⟨4411247, by rfl⟩ : syracuseStep 5881663 = 8822495) B8822495
theorem B3096431 : Blo 1375507 3096431 := bstep (se 1 (by rfl) ⟨2322323, by rfl⟩ : syracuseStep 3096431 = 4644647) B4644647
theorem B1376239 : Blo 1375507 1376239 := bstep (se 1 (by rfl) ⟨1032179, by rfl⟩ : syracuseStep 1376239 = 2064359) B2064359
theorem B1376327 : Blo 1375507 1376327 := bstep (se 1 (by rfl) ⟨1032245, by rfl⟩ : syracuseStep 1376327 = 2064491) B2064491
theorem B1376423 : Blo 1375507 1376423 := bstep (se 1 (by rfl) ⟨1032317, by rfl⟩ : syracuseStep 1376423 = 2064635) B2064635
theorem B6611165 : Blo 1375507 6611165 := bstep (se 3 (by rfl) ⟨1239593, by rfl⟩ : syracuseStep 6611165 = 2479187) B2479187
theorem B3481825 : Blo 1375507 3481825 := bstep (se 2 (by rfl) ⟨1305684, by rfl⟩ : syracuseStep 3481825 = 2611369) B2611369
theorem B2064809 : Blo 1375507 2064809 := bstep (se 2 (by rfl) ⟨774303, by rfl⟩ : syracuseStep 2064809 = 1548607) B1548607
theorem B10052075 : Blo 1375507 10052075 := bstep (se 1 (by rfl) ⟨7539056, by rfl⟩ : syracuseStep 10052075 = 15078113) B15078113
theorem B11756015 : Blo 1375507 11756015 := bstep (se 1 (by rfl) ⟨8817011, by rfl⟩ : syracuseStep 11756015 = 17634023) B17634023
theorem B6971993 : Blo 1375507 6971993 := bstep (se 2 (by rfl) ⟨2614497, by rfl⟩ : syracuseStep 6971993 = 5228995) B5228995
theorem B11166299 : Blo 1375507 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B2065391 : Blo 1375507 2065391 := bstep (se 1 (by rfl) ⟨1549043, by rfl⟩ : syracuseStep 2065391 = 3098087) B3098087
theorem B1377263 : Blo 1375507 1377263 := bstep (se 1 (by rfl) ⟨1032947, by rfl⟩ : syracuseStep 1377263 = 2065895) B2065895
theorem B1377383 : Blo 1375507 1377383 := bstep (se 1 (by rfl) ⟨1033037, by rfl⟩ : syracuseStep 1377383 = 2066075) B2066075
theorem B10454345 : Blo 1375507 10454345 := bstep (se 2 (by rfl) ⟨3920379, by rfl⟩ : syracuseStep 10454345 = 7840759) B7840759
theorem B3483719 : Blo 1375507 3483719 := bstep (se 1 (by rfl) ⟨2612789, by rfl⟩ : syracuseStep 3483719 = 5225579) B5225579
theorem B6965351 : Blo 1375507 6965351 := bstep (se 1 (by rfl) ⟨5224013, by rfl⟩ : syracuseStep 6965351 = 10448027) B10448027
theorem B3098879 : Blo 1375507 3098879 := bstep (se 1 (by rfl) ⟨2324159, by rfl⟩ : syracuseStep 3098879 = 4648319) B4648319
theorem B3975443 : Blo 1375507 3975443 := bstep (se 1 (by rfl) ⟨2981582, by rfl⟩ : syracuseStep 3975443 = 5963165) B5963165
theorem B29755775 : Blo 1375507 29755775 := bstep (se 1 (by rfl) ⟨22316831, by rfl⟩ : syracuseStep 29755775 = 44633663) B44633663
theorem B7842217 : Blo 1375507 7842217 := bstep (se 2 (by rfl) ⟨2940831, by rfl⟩ : syracuseStep 7842217 = 5881663) B5881663
theorem B4648103 : Blo 1375507 4648103 := bstep (se 1 (by rfl) ⟨3486077, by rfl⟩ : syracuseStep 4648103 = 6972155) B6972155
theorem B17632687 : Blo 1375507 17632687 := bstep (se 1 (by rfl) ⟨13224515, by rfl⟩ : syracuseStep 17632687 = 26449031) B26449031
theorem B23514623 : Blo 1375507 23514623 := bstep (se 1 (by rfl) ⟨17635967, by rfl⟩ : syracuseStep 23514623 = 35271935) B35271935
theorem B75379511 : Blo 1375507 75379511 := bstep (se 1 (by rfl) ⟨56534633, by rfl⟩ : syracuseStep 75379511 = 113069267) B113069267
theorem B13587371 : Blo 1375507 13587371 := bstep (se 1 (by rfl) ⟨10190528, by rfl⟩ : syracuseStep 13587371 = 20381057) B20381057
theorem B3921007 : Blo 1375507 3921007 := bstep (se 1 (by rfl) ⟨2940755, by rfl⟩ : syracuseStep 3921007 = 5881511) B5881511
theorem B1742239 : Blo 1375507 1742239 := bstep (se 1 (by rfl) ⟨1306679, by rfl⟩ : syracuseStep 1742239 = 2613359) B2613359
theorem B4642811 : Blo 1375507 4642811 := bstep (se 1 (by rfl) ⟨3482108, by rfl⟩ : syracuseStep 4642811 = 6964217) B6964217
theorem B80582795 : Blo 1375507 80582795 := bstep (se 1 (by rfl) ⟨60437096, by rfl⟩ : syracuseStep 80582795 = 120874193) B120874193
theorem B19847845 : Blo 1375507 19847845 := bstep (se 4 (by rfl) ⟨1860735, by rfl⟩ : syracuseStep 19847845 = 3721471) B3721471
theorem B4643783 : Blo 1375507 4643783 := bstep (se 1 (by rfl) ⟨3482837, by rfl⟩ : syracuseStep 4643783 = 6965675) B6965675
theorem B5880775 : Blo 1375507 5880775 := bstep (se 1 (by rfl) ⟨4410581, by rfl⟩ : syracuseStep 5880775 = 8821163) B8821163
theorem B2063519 : Blo 1375507 2063519 := bstep (se 1 (by rfl) ⟨1547639, by rfl⟩ : syracuseStep 2063519 = 3095279) B3095279
theorem B6970535 : Blo 1375507 6970535 := bstep (se 1 (by rfl) ⟨5227901, by rfl⟩ : syracuseStep 6970535 = 10455803) B10455803
theorem B1375615 : Blo 1375507 1375615 := bstep (se 1 (by rfl) ⟨1031711, by rfl⟩ : syracuseStep 1375615 = 2063423) B2063423
theorem B2064287 : Blo 1375507 2064287 := bstep (se 1 (by rfl) ⟨1548215, by rfl⟩ : syracuseStep 2064287 = 3096431) B3096431
theorem B4407443 : Blo 1375507 4407443 := bstep (se 1 (by rfl) ⟨3305582, by rfl⟩ : syracuseStep 4407443 = 6611165) B6611165
theorem B1376539 : Blo 1375507 1376539 := bstep (se 1 (by rfl) ⟨1032404, by rfl⟩ : syracuseStep 1376539 = 2064809) B2064809
theorem B6701383 : Blo 1375507 6701383 := bstep (se 1 (by rfl) ⟨5026037, by rfl⟩ : syracuseStep 6701383 = 10052075) B10052075
theorem B1376927 : Blo 1375507 1376927 := bstep (se 1 (by rfl) ⟨1032695, by rfl⟩ : syracuseStep 1376927 = 2065391) B2065391
theorem B7841033 : Blo 1375507 7841033 := bstep (se 2 (by rfl) ⟨2940387, by rfl⟩ : syracuseStep 7841033 = 5880775) B5880775
theorem B5228009 : Blo 1375507 5228009 := bstep (se 2 (by rfl) ⟨1960503, by rfl⟩ : syracuseStep 5228009 = 3921007) B3921007
theorem B2065919 : Blo 1375507 2065919 := bstep (se 1 (by rfl) ⟨1549439, by rfl⟩ : syracuseStep 2065919 = 3098879) B3098879
theorem B4647023 : Blo 1375507 4647023 := bstep (se 1 (by rfl) ⟨3485267, by rfl⟩ : syracuseStep 4647023 = 6970535) B6970535
theorem B3098735 : Blo 1375507 3098735 := bstep (se 1 (by rfl) ⟨2324051, by rfl⟩ : syracuseStep 3098735 = 4648103) B4648103
theorem B4647995 : Blo 1375507 4647995 := bstep (se 1 (by rfl) ⟨3485996, by rfl⟩ : syracuseStep 4647995 = 6971993) B6971993
theorem B50253007 : Blo 1375507 50253007 := bstep (se 1 (by rfl) ⟨37689755, by rfl⟩ : syracuseStep 50253007 = 75379511) B75379511
theorem B10456289 : Blo 1375507 10456289 := bstep (se 2 (by rfl) ⟨3921108, by rfl⟩ : syracuseStep 10456289 = 7842217) B7842217
theorem B26463793 : Blo 1375507 26463793 := bstep (se 2 (by rfl) ⟨9923922, by rfl⟩ : syracuseStep 26463793 = 19847845) B19847845
theorem B2322479 : Blo 1375507 2322479 := bstep (se 1 (by rfl) ⟨1741859, by rfl⟩ : syracuseStep 2322479 = 3483719) B3483719
theorem B2650295 : Blo 1375507 2650295 := bstep (se 1 (by rfl) ⟨1987721, by rfl⟩ : syracuseStep 2650295 = 3975443) B3975443
theorem B19837183 : Blo 1375507 19837183 := bstep (se 1 (by rfl) ⟨14877887, by rfl⟩ : syracuseStep 19837183 = 29755775) B29755775
theorem B2322985 : Blo 1375507 2322985 := bstep (se 2 (by rfl) ⟨871119, by rfl⟩ : syracuseStep 2322985 = 1742239) B1742239
theorem B15676415 : Blo 1375507 15676415 := bstep (se 1 (by rfl) ⟨11757311, by rfl⟩ : syracuseStep 15676415 = 23514623) B23514623
theorem B4642433 : Blo 1375507 4642433 := bstep (se 2 (by rfl) ⟨1740912, by rfl⟩ : syracuseStep 4642433 = 3481825) B3481825
theorem B7837343 : Blo 1375507 7837343 := bstep (se 1 (by rfl) ⟨5878007, by rfl⟩ : syracuseStep 7837343 = 11756015) B11756015
theorem B7444199 : Blo 1375507 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B9058247 : Blo 1375507 9058247 := bstep (se 1 (by rfl) ⟨6793685, by rfl⟩ : syracuseStep 9058247 = 13587371) B13587371
theorem B6969563 : Blo 1375507 6969563 := bstep (se 1 (by rfl) ⟨5227172, by rfl⟩ : syracuseStep 6969563 = 10454345) B10454345
theorem B3095207 : Blo 1375507 3095207 := bstep (se 1 (by rfl) ⟨2321405, by rfl⟩ : syracuseStep 3095207 = 4642811) B4642811
theorem B4643567 : Blo 1375507 4643567 := bstep (se 1 (by rfl) ⟨3482675, by rfl⟩ : syracuseStep 4643567 = 6965351) B6965351
theorem B53721863 : Blo 1375507 53721863 := bstep (se 1 (by rfl) ⟨40291397, by rfl⟩ : syracuseStep 53721863 = 80582795) B80582795
theorem B23510249 : Blo 1375507 23510249 := bstep (se 2 (by rfl) ⟨8816343, by rfl⟩ : syracuseStep 23510249 = 17632687) B17632687
theorem B3095855 : Blo 1375507 3095855 := bstep (se 1 (by rfl) ⟨2321891, by rfl⟩ : syracuseStep 3095855 = 4643783) B4643783
theorem B1375679 : Blo 1375507 1375679 := bstep (se 1 (by rfl) ⟨1031759, by rfl⟩ : syracuseStep 1375679 = 2063519) B2063519
theorem B1376191 : Blo 1375507 1376191 := bstep (se 1 (by rfl) ⟨1032143, by rfl⟩ : syracuseStep 1376191 = 2064287) B2064287
theorem B1548319 : Blo 1375507 1548319 := bstep (se 1 (by rfl) ⟨1161239, by rfl⟩ : syracuseStep 1548319 = 2322479) B2322479
theorem B3097313 : Blo 1375507 3097313 := bstep (se 2 (by rfl) ⟨1161492, by rfl⟩ : syracuseStep 3097313 = 2322985) B2322985
theorem B5227355 : Blo 1375507 5227355 := bstep (se 1 (by rfl) ⟨3920516, by rfl⟩ : syracuseStep 5227355 = 7841033) B7841033
theorem B1377279 : Blo 1375507 1377279 := bstep (se 1 (by rfl) ⟨1032959, by rfl⟩ : syracuseStep 1377279 = 2065919) B2065919
theorem B6038831 : Blo 1375507 6038831 := bstep (se 1 (by rfl) ⟨4529123, by rfl⟩ : syracuseStep 6038831 = 9058247) B9058247
theorem B3098015 : Blo 1375507 3098015 := bstep (se 1 (by rfl) ⟨2323511, by rfl⟩ : syracuseStep 3098015 = 4647023) B4647023
theorem B2065823 : Blo 1375507 2065823 := bstep (se 1 (by rfl) ⟨1549367, by rfl⟩ : syracuseStep 2065823 = 3098735) B3098735
theorem B4646375 : Blo 1375507 4646375 := bstep (se 1 (by rfl) ⟨3484781, by rfl⟩ : syracuseStep 4646375 = 6969563) B6969563
theorem B67004009 : Blo 1375507 67004009 := bstep (se 2 (by rfl) ⟨25126503, by rfl⟩ : syracuseStep 67004009 = 50253007) B50253007
theorem B3098663 : Blo 1375507 3098663 := bstep (se 1 (by rfl) ⟨2323997, by rfl⟩ : syracuseStep 3098663 = 4647995) B4647995
theorem B35285057 : Blo 1375507 35285057 := bstep (se 2 (by rfl) ⟨13231896, by rfl⟩ : syracuseStep 35285057 = 26463793) B26463793
theorem B15673499 : Blo 1375507 15673499 := bstep (se 1 (by rfl) ⟨11755124, by rfl⟩ : syracuseStep 15673499 = 23510249) B23510249
theorem B3485339 : Blo 1375507 3485339 := bstep (se 1 (by rfl) ⟨2614004, by rfl⟩ : syracuseStep 3485339 = 5228009) B5228009
theorem B2938295 : Blo 1375507 2938295 := bstep (se 1 (by rfl) ⟨2203721, by rfl⟩ : syracuseStep 2938295 = 4407443) B4407443
theorem B1766863 : Blo 1375507 1766863 := bstep (se 1 (by rfl) ⟨1325147, by rfl⟩ : syracuseStep 1766863 = 2650295) B2650295
theorem B26449577 : Blo 1375507 26449577 := bstep (se 2 (by rfl) ⟨9918591, by rfl⟩ : syracuseStep 26449577 = 19837183) B19837183
theorem B8935177 : Blo 1375507 8935177 := bstep (se 2 (by rfl) ⟨3350691, by rfl⟩ : syracuseStep 8935177 = 6701383) B6701383
theorem B10450943 : Blo 1375507 10450943 := bstep (se 1 (by rfl) ⟨7838207, by rfl⟩ : syracuseStep 10450943 = 15676415) B15676415
theorem B3094955 : Blo 1375507 3094955 := bstep (se 1 (by rfl) ⟨2321216, by rfl⟩ : syracuseStep 3094955 = 4642433) B4642433
theorem B5224895 : Blo 1375507 5224895 := bstep (se 1 (by rfl) ⟨3918671, by rfl⟩ : syracuseStep 5224895 = 7837343) B7837343
theorem B4962799 : Blo 1375507 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B2063471 : Blo 1375507 2063471 := bstep (se 1 (by rfl) ⟨1547603, by rfl⟩ : syracuseStep 2063471 = 3095207) B3095207
theorem B3095711 : Blo 1375507 3095711 := bstep (se 1 (by rfl) ⟨2321783, by rfl⟩ : syracuseStep 3095711 = 4643567) B4643567
theorem B35814575 : Blo 1375507 35814575 := bstep (se 1 (by rfl) ⟨26860931, by rfl⟩ : syracuseStep 35814575 = 53721863) B53721863
theorem B6970859 : Blo 1375507 6970859 := bstep (se 1 (by rfl) ⟨5228144, by rfl⟩ : syracuseStep 6970859 = 10456289) B10456289
theorem B2063903 : Blo 1375507 2063903 := bstep (se 1 (by rfl) ⟨1547927, by rfl⟩ : syracuseStep 2063903 = 3095855) B3095855
theorem B2064425 : Blo 1375507 2064425 := bstep (se 2 (by rfl) ⟨774159, by rfl⟩ : syracuseStep 2064425 = 1548319) B1548319
theorem B2064875 : Blo 1375507 2064875 := bstep (se 1 (by rfl) ⟨1548656, by rfl⟩ : syracuseStep 2064875 = 3097313) B3097313
theorem B2065343 : Blo 1375507 2065343 := bstep (se 1 (by rfl) ⟨1549007, by rfl⟩ : syracuseStep 2065343 = 3098015) B3098015
theorem B1377215 : Blo 1375507 1377215 := bstep (se 1 (by rfl) ⟨1032911, by rfl⟩ : syracuseStep 1377215 = 2065823) B2065823
theorem B3097583 : Blo 1375507 3097583 := bstep (se 1 (by rfl) ⟨2323187, by rfl⟩ : syracuseStep 3097583 = 4646375) B4646375
theorem B2065775 : Blo 1375507 2065775 := bstep (se 1 (by rfl) ⟨1549331, by rfl⟩ : syracuseStep 2065775 = 3098663) B3098663
theorem B3483263 : Blo 1375507 3483263 := bstep (se 1 (by rfl) ⟨2612447, by rfl⟩ : syracuseStep 3483263 = 5224895) B5224895
theorem B4647239 : Blo 1375507 4647239 := bstep (se 1 (by rfl) ⟨3485429, by rfl⟩ : syracuseStep 4647239 = 6970859) B6970859
theorem B11913569 : Blo 1375507 11913569 := bstep (se 2 (by rfl) ⟨4467588, by rfl⟩ : syracuseStep 11913569 = 8935177) B8935177
theorem B3484903 : Blo 1375507 3484903 := bstep (se 1 (by rfl) ⟨2613677, by rfl⟩ : syracuseStep 3484903 = 5227355) B5227355
theorem B17633051 : Blo 1375507 17633051 := bstep (se 1 (by rfl) ⟨13224788, by rfl⟩ : syracuseStep 17633051 = 26449577) B26449577
theorem B7835453 : Blo 1375507 7835453 := bstep (se 3 (by rfl) ⟨1469147, by rfl⟩ : syracuseStep 7835453 = 2938295) B2938295
theorem B6967295 : Blo 1375507 6967295 := bstep (se 1 (by rfl) ⟨5225471, by rfl⟩ : syracuseStep 6967295 = 10450943) B10450943
theorem B23523371 : Blo 1375507 23523371 := bstep (se 1 (by rfl) ⟨17642528, by rfl⟩ : syracuseStep 23523371 = 35285057) B35285057
theorem B10448999 : Blo 1375507 10448999 := bstep (se 1 (by rfl) ⟨7836749, by rfl⟩ : syracuseStep 10448999 = 15673499) B15673499
theorem B2355817 : Blo 1375507 2355817 := bstep (se 2 (by rfl) ⟨883431, by rfl⟩ : syracuseStep 2355817 = 1766863) B1766863
theorem B23876383 : Blo 1375507 23876383 := bstep (se 1 (by rfl) ⟨17907287, by rfl⟩ : syracuseStep 23876383 = 35814575) B35814575
theorem B2323559 : Blo 1375507 2323559 := bstep (se 1 (by rfl) ⟨1742669, by rfl⟩ : syracuseStep 2323559 = 3485339) B3485339
theorem B6617065 : Blo 1375507 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B16103549 : Blo 1375507 16103549 := bstep (se 3 (by rfl) ⟨3019415, by rfl⟩ : syracuseStep 16103549 = 6038831) B6038831
theorem B44669339 : Blo 1375507 44669339 := bstep (se 1 (by rfl) ⟨33502004, by rfl⟩ : syracuseStep 44669339 = 67004009) B67004009
theorem B2063303 : Blo 1375507 2063303 := bstep (se 1 (by rfl) ⟨1547477, by rfl⟩ : syracuseStep 2063303 = 3094955) B3094955
theorem B1375647 : Blo 1375507 1375647 := bstep (se 1 (by rfl) ⟨1031735, by rfl⟩ : syracuseStep 1375647 = 2063471) B2063471
theorem B2063807 : Blo 1375507 2063807 := bstep (se 1 (by rfl) ⟨1547855, by rfl⟩ : syracuseStep 2063807 = 3095711) B3095711
theorem B1375935 : Blo 1375507 1375935 := bstep (se 1 (by rfl) ⟨1031951, by rfl⟩ : syracuseStep 1375935 = 2063903) B2063903
theorem B1376283 : Blo 1375507 1376283 := bstep (se 1 (by rfl) ⟨1032212, by rfl⟩ : syracuseStep 1376283 = 2064425) B2064425
theorem B1376583 : Blo 1375507 1376583 := bstep (se 1 (by rfl) ⟨1032437, by rfl⟩ : syracuseStep 1376583 = 2064875) B2064875
theorem B1376895 : Blo 1375507 1376895 := bstep (se 1 (by rfl) ⟨1032671, by rfl⟩ : syracuseStep 1376895 = 2065343) B2065343
theorem B2065055 : Blo 1375507 2065055 := bstep (se 1 (by rfl) ⟨1548791, by rfl⟩ : syracuseStep 2065055 = 3097583) B3097583
theorem B1549039 : Blo 1375507 1549039 := bstep (se 1 (by rfl) ⟨1161779, by rfl⟩ : syracuseStep 1549039 = 2323559) B2323559
theorem B1377183 : Blo 1375507 1377183 := bstep (se 1 (by rfl) ⟨1032887, by rfl⟩ : syracuseStep 1377183 = 2065775) B2065775
theorem B31835177 : Blo 1375507 31835177 := bstep (se 2 (by rfl) ⟨11938191, by rfl⟩ : syracuseStep 31835177 = 23876383) B23876383
theorem B3098159 : Blo 1375507 3098159 := bstep (se 1 (by rfl) ⟨2323619, by rfl⟩ : syracuseStep 3098159 = 4647239) B4647239
theorem B29779559 : Blo 1375507 29779559 := bstep (se 1 (by rfl) ⟨22334669, by rfl⟩ : syracuseStep 29779559 = 44669339) B44669339
theorem B4646537 : Blo 1375507 4646537 := bstep (se 2 (by rfl) ⟨1742451, by rfl⟩ : syracuseStep 4646537 = 3484903) B3484903
theorem B15682247 : Blo 1375507 15682247 := bstep (se 1 (by rfl) ⟨11761685, by rfl⟩ : syracuseStep 15682247 = 23523371) B23523371
theorem B6965999 : Blo 1375507 6965999 := bstep (se 1 (by rfl) ⟨5224499, by rfl⟩ : syracuseStep 6965999 = 10448999) B10448999
theorem B3141089 : Blo 1375507 3141089 := bstep (se 2 (by rfl) ⟨1177908, by rfl⟩ : syracuseStep 3141089 = 2355817) B2355817
theorem B2322175 : Blo 1375507 2322175 := bstep (se 1 (by rfl) ⟨1741631, by rfl⟩ : syracuseStep 2322175 = 3483263) B3483263
theorem B10735699 : Blo 1375507 10735699 := bstep (se 1 (by rfl) ⟨8051774, by rfl⟩ : syracuseStep 10735699 = 16103549) B16103549
theorem B7942379 : Blo 1375507 7942379 := bstep (se 1 (by rfl) ⟨5956784, by rfl⟩ : syracuseStep 7942379 = 11913569) B11913569
theorem B5223635 : Blo 1375507 5223635 := bstep (se 1 (by rfl) ⟨3917726, by rfl⟩ : syracuseStep 5223635 = 7835453) B7835453
theorem B4644863 : Blo 1375507 4644863 := bstep (se 1 (by rfl) ⟨3483647, by rfl⟩ : syracuseStep 4644863 = 6967295) B6967295
theorem B1375535 : Blo 1375507 1375535 := bstep (se 1 (by rfl) ⟨1031651, by rfl⟩ : syracuseStep 1375535 = 2063303) B2063303
theorem B1375871 : Blo 1375507 1375871 := bstep (se 1 (by rfl) ⟨1031903, by rfl⟩ : syracuseStep 1375871 = 2063807) B2063807
theorem B11755367 : Blo 1375507 11755367 := bstep (se 1 (by rfl) ⟨8816525, by rfl⟩ : syracuseStep 11755367 = 17633051) B17633051
theorem B8822753 : Blo 1375507 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B1376703 : Blo 1375507 1376703 := bstep (se 1 (by rfl) ⟨1032527, by rfl⟩ : syracuseStep 1376703 = 2065055) B2065055
theorem B3482423 : Blo 1375507 3482423 := bstep (se 1 (by rfl) ⟨2611817, by rfl⟩ : syracuseStep 3482423 = 5223635) B5223635
theorem B2065385 : Blo 1375507 2065385 := bstep (se 2 (by rfl) ⟨774519, by rfl⟩ : syracuseStep 2065385 = 1549039) B1549039
theorem B2065439 : Blo 1375507 2065439 := bstep (se 1 (by rfl) ⟨1549079, by rfl⟩ : syracuseStep 2065439 = 3098159) B3098159
theorem B3097691 : Blo 1375507 3097691 := bstep (se 1 (by rfl) ⟨2323268, by rfl⟩ : syracuseStep 3097691 = 4646537) B4646537
theorem B10454831 : Blo 1375507 10454831 := bstep (se 1 (by rfl) ⟨7841123, by rfl⟩ : syracuseStep 10454831 = 15682247) B15682247
theorem B14314265 : Blo 1375507 14314265 := bstep (se 2 (by rfl) ⟨5367849, by rfl⟩ : syracuseStep 14314265 = 10735699) B10735699
theorem B19853039 : Blo 1375507 19853039 := bstep (se 1 (by rfl) ⟨14889779, by rfl⟩ : syracuseStep 19853039 = 29779559) B29779559
theorem B2094059 : Blo 1375507 2094059 := bstep (se 1 (by rfl) ⟨1570544, by rfl⟩ : syracuseStep 2094059 = 3141089) B3141089
theorem B84718709 : Blo 1375507 84718709 := bstep (se 5 (by rfl) ⟨3971189, by rfl⟩ : syracuseStep 84718709 = 7942379) B7942379
theorem B7836911 : Blo 1375507 7836911 := bstep (se 1 (by rfl) ⟨5877683, by rfl⟩ : syracuseStep 7836911 = 11755367) B11755367
theorem B21223451 : Blo 1375507 21223451 := bstep (se 1 (by rfl) ⟨15917588, by rfl⟩ : syracuseStep 21223451 = 31835177) B31835177
theorem B4643999 : Blo 1375507 4643999 := bstep (se 1 (by rfl) ⟨3482999, by rfl⟩ : syracuseStep 4643999 = 6965999) B6965999
theorem B3096233 : Blo 1375507 3096233 := bstep (se 2 (by rfl) ⟨1161087, by rfl⟩ : syracuseStep 3096233 = 2322175) B2322175
theorem B5881835 : Blo 1375507 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B3096575 : Blo 1375507 3096575 := bstep (se 1 (by rfl) ⟨2322431, by rfl⟩ : syracuseStep 3096575 = 4644863) B4644863
theorem B1376923 : Blo 1375507 1376923 := bstep (se 1 (by rfl) ⟨1032692, by rfl⟩ : syracuseStep 1376923 = 2065385) B2065385
theorem B1376959 : Blo 1375507 1376959 := bstep (se 1 (by rfl) ⟨1032719, by rfl⟩ : syracuseStep 1376959 = 2065439) B2065439
theorem B2065127 : Blo 1375507 2065127 := bstep (se 1 (by rfl) ⟨1548845, by rfl⟩ : syracuseStep 2065127 = 3097691) B3097691
theorem B14148967 : Blo 1375507 14148967 := bstep (se 1 (by rfl) ⟨10611725, by rfl⟩ : syracuseStep 14148967 = 21223451) B21223451
theorem B2321615 : Blo 1375507 2321615 := bstep (se 1 (by rfl) ⟨1741211, by rfl⟩ : syracuseStep 2321615 = 3482423) B3482423
theorem B1396039 : Blo 1375507 1396039 := bstep (se 1 (by rfl) ⟨1047029, by rfl⟩ : syracuseStep 1396039 = 2094059) B2094059
theorem B56479139 : Blo 1375507 56479139 := bstep (se 1 (by rfl) ⟨42359354, by rfl⟩ : syracuseStep 56479139 = 84718709) B84718709
theorem B13235359 : Blo 1375507 13235359 := bstep (se 1 (by rfl) ⟨9926519, by rfl⟩ : syracuseStep 13235359 = 19853039) B19853039
theorem B3921223 : Blo 1375507 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B5224607 : Blo 1375507 5224607 := bstep (se 1 (by rfl) ⟨3918455, by rfl⟩ : syracuseStep 5224607 = 7836911) B7836911
theorem B6969887 : Blo 1375507 6969887 := bstep (se 1 (by rfl) ⟨5227415, by rfl⟩ : syracuseStep 6969887 = 10454831) B10454831
theorem B2064383 : Blo 1375507 2064383 := bstep (se 1 (by rfl) ⟨1548287, by rfl⟩ : syracuseStep 2064383 = 3096575) B3096575
theorem B9542843 : Blo 1375507 9542843 := bstep (se 1 (by rfl) ⟨7157132, by rfl⟩ : syracuseStep 9542843 = 14314265) B14314265
theorem B3095999 : Blo 1375507 3095999 := bstep (se 1 (by rfl) ⟨2321999, by rfl⟩ : syracuseStep 3095999 = 4643999) B4643999
theorem B2064155 : Blo 1375507 2064155 := bstep (se 1 (by rfl) ⟨1548116, by rfl⟩ : syracuseStep 2064155 = 3096233) B3096233
theorem B1376751 : Blo 1375507 1376751 := bstep (se 1 (by rfl) ⟨1032563, by rfl⟩ : syracuseStep 1376751 = 2065127) B2065127
theorem B3483071 : Blo 1375507 3483071 := bstep (se 1 (by rfl) ⟨2612303, by rfl⟩ : syracuseStep 3483071 = 5224607) B5224607
theorem B17647145 : Blo 1375507 17647145 := bstep (se 2 (by rfl) ⟨6617679, by rfl⟩ : syracuseStep 17647145 = 13235359) B13235359
theorem B4646591 : Blo 1375507 4646591 := bstep (se 1 (by rfl) ⟨3484943, by rfl⟩ : syracuseStep 4646591 = 6969887) B6969887
theorem B5228297 : Blo 1375507 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B1861385 : Blo 1375507 1861385 := bstep (se 2 (by rfl) ⟨698019, by rfl⟩ : syracuseStep 1861385 = 1396039) B1396039
theorem B1376255 : Blo 1375507 1376255 := bstep (se 1 (by rfl) ⟨1032191, by rfl⟩ : syracuseStep 1376255 = 2064383) B2064383
theorem B37652759 : Blo 1375507 37652759 := bstep (se 1 (by rfl) ⟨28239569, by rfl⟩ : syracuseStep 37652759 = 56479139) B56479139
theorem B6361895 : Blo 1375507 6361895 := bstep (se 1 (by rfl) ⟨4771421, by rfl⟩ : syracuseStep 6361895 = 9542843) B9542843
theorem B18865289 : Blo 1375507 18865289 := bstep (se 2 (by rfl) ⟨7074483, by rfl⟩ : syracuseStep 18865289 = 14148967) B14148967
theorem B1547743 : Blo 1375507 1547743 := bstep (se 1 (by rfl) ⟨1160807, by rfl⟩ : syracuseStep 1547743 = 2321615) B2321615
theorem B2063999 : Blo 1375507 2063999 := bstep (se 1 (by rfl) ⟨1547999, by rfl⟩ : syracuseStep 2063999 = 3095999) B3095999
theorem B1376103 : Blo 1375507 1376103 := bstep (se 1 (by rfl) ⟨1032077, by rfl⟩ : syracuseStep 1376103 = 2064155) B2064155
theorem B50307437 : Blo 1375507 50307437 := bstep (se 3 (by rfl) ⟨9432644, by rfl⟩ : syracuseStep 50307437 = 18865289) B18865289
theorem B11764763 : Blo 1375507 11764763 := bstep (se 1 (by rfl) ⟨8823572, by rfl⟩ : syracuseStep 11764763 = 17647145) B17647145
theorem B3097727 : Blo 1375507 3097727 := bstep (se 1 (by rfl) ⟨2323295, by rfl⟩ : syracuseStep 3097727 = 4646591) B4646591
theorem B25101839 : Blo 1375507 25101839 := bstep (se 1 (by rfl) ⟨18826379, by rfl⟩ : syracuseStep 25101839 = 37652759) B37652759
theorem B2322047 : Blo 1375507 2322047 := bstep (se 1 (by rfl) ⟨1741535, by rfl⟩ : syracuseStep 2322047 = 3483071) B3483071
theorem B3485531 : Blo 1375507 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B4241263 : Blo 1375507 4241263 := bstep (se 1 (by rfl) ⟨3180947, by rfl⟩ : syracuseStep 4241263 = 6361895) B6361895
theorem B2063657 : Blo 1375507 2063657 := bstep (se 2 (by rfl) ⟨773871, by rfl⟩ : syracuseStep 2063657 = 1547743) B1547743
theorem B4963693 : Blo 1375507 4963693 := bstep (se 3 (by rfl) ⟨930692, by rfl⟩ : syracuseStep 4963693 = 1861385) B1861385
theorem B1375999 : Blo 1375507 1375999 := bstep (se 1 (by rfl) ⟨1031999, by rfl⟩ : syracuseStep 1375999 = 2063999) B2063999
theorem B2065151 : Blo 1375507 2065151 := bstep (se 1 (by rfl) ⟨1548863, by rfl⟩ : syracuseStep 2065151 = 3097727) B3097727
theorem B134153165 : Blo 1375507 134153165 := bstep (se 3 (by rfl) ⟨25153718, by rfl⟩ : syracuseStep 134153165 = 50307437) B50307437
theorem B5655017 : Blo 1375507 5655017 := bstep (se 2 (by rfl) ⟨2120631, by rfl⟩ : syracuseStep 5655017 = 4241263) B4241263
theorem B7843175 : Blo 1375507 7843175 := bstep (se 1 (by rfl) ⟨5882381, by rfl⟩ : syracuseStep 7843175 = 11764763) B11764763
theorem B2323687 : Blo 1375507 2323687 := bstep (se 1 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 2323687 = 3485531) B3485531
theorem B16734559 : Blo 1375507 16734559 := bstep (se 1 (by rfl) ⟨12550919, by rfl⟩ : syracuseStep 16734559 = 25101839) B25101839
theorem B6618257 : Blo 1375507 6618257 := bstep (se 2 (by rfl) ⟨2481846, by rfl⟩ : syracuseStep 6618257 = 4963693) B4963693
theorem B1375771 : Blo 1375507 1375771 := bstep (se 1 (by rfl) ⟨1031828, by rfl⟩ : syracuseStep 1375771 = 2063657) B2063657
theorem B1548031 : Blo 1375507 1548031 := bstep (se 1 (by rfl) ⟨1161023, by rfl⟩ : syracuseStep 1548031 = 2322047) B2322047
theorem B1376767 : Blo 1375507 1376767 := bstep (se 1 (by rfl) ⟨1032575, by rfl⟩ : syracuseStep 1376767 = 2065151) B2065151
theorem B3098249 : Blo 1375507 3098249 := bstep (se 2 (by rfl) ⟨1161843, by rfl⟩ : syracuseStep 3098249 = 2323687) B2323687
theorem B3770011 : Blo 1375507 3770011 := bstep (se 1 (by rfl) ⟨2827508, by rfl⟩ : syracuseStep 3770011 = 5655017) B5655017
theorem B5228783 : Blo 1375507 5228783 := bstep (se 1 (by rfl) ⟨3921587, by rfl⟩ : syracuseStep 5228783 = 7843175) B7843175
theorem B89435443 : Blo 1375507 89435443 := bstep (se 1 (by rfl) ⟨67076582, by rfl⟩ : syracuseStep 89435443 = 134153165) B134153165
theorem B4412171 : Blo 1375507 4412171 := bstep (se 1 (by rfl) ⟨3309128, by rfl⟩ : syracuseStep 4412171 = 6618257) B6618257
theorem B22312745 : Blo 1375507 22312745 := bstep (se 2 (by rfl) ⟨8367279, by rfl⟩ : syracuseStep 22312745 = 16734559) B16734559
theorem B2064041 : Blo 1375507 2064041 := bstep (se 2 (by rfl) ⟨774015, by rfl⟩ : syracuseStep 2064041 = 1548031) B1548031
theorem B2941447 : Blo 1375507 2941447 := bstep (se 1 (by rfl) ⟨2206085, by rfl⟩ : syracuseStep 2941447 = 4412171) B4412171
theorem B2065499 : Blo 1375507 2065499 := bstep (se 1 (by rfl) ⟨1549124, by rfl⟩ : syracuseStep 2065499 = 3098249) B3098249
theorem B3485855 : Blo 1375507 3485855 := bstep (se 1 (by rfl) ⟨2614391, by rfl⟩ : syracuseStep 3485855 = 5228783) B5228783
theorem B119247257 : Blo 1375507 119247257 := bstep (se 2 (by rfl) ⟨44717721, by rfl⟩ : syracuseStep 119247257 = 89435443) B89435443
theorem B5026681 : Blo 1375507 5026681 := bstep (se 2 (by rfl) ⟨1885005, by rfl⟩ : syracuseStep 5026681 = 3770011) B3770011
theorem B14875163 : Blo 1375507 14875163 := bstep (se 1 (by rfl) ⟨11156372, by rfl⟩ : syracuseStep 14875163 = 22312745) B22312745
theorem B1376027 : Blo 1375507 1376027 := bstep (se 1 (by rfl) ⟨1032020, by rfl⟩ : syracuseStep 1376027 = 2064041) B2064041
theorem B1376999 : Blo 1375507 1376999 := bstep (se 1 (by rfl) ⟨1032749, by rfl⟩ : syracuseStep 1376999 = 2065499) B2065499
theorem B79498171 : Blo 1375507 79498171 := bstep (se 1 (by rfl) ⟨59623628, by rfl⟩ : syracuseStep 79498171 = 119247257) B119247257
theorem B9916775 : Blo 1375507 9916775 := bstep (se 1 (by rfl) ⟨7437581, by rfl⟩ : syracuseStep 9916775 = 14875163) B14875163
theorem B26808965 : Blo 1375507 26808965 := bstep (se 4 (by rfl) ⟨2513340, by rfl⟩ : syracuseStep 26808965 = 5026681) B5026681
theorem B2323903 : Blo 1375507 2323903 := bstep (se 1 (by rfl) ⟨1742927, by rfl⟩ : syracuseStep 2323903 = 3485855) B3485855
theorem B3921929 : Blo 1375507 3921929 := bstep (se 2 (by rfl) ⟨1470723, by rfl⟩ : syracuseStep 3921929 = 2941447) B2941447
theorem B6611183 : Blo 1375507 6611183 := bstep (se 1 (by rfl) ⟨4958387, by rfl⟩ : syracuseStep 6611183 = 9916775) B9916775
theorem B105997561 : Blo 1375507 105997561 := bstep (se 2 (by rfl) ⟨39749085, by rfl⟩ : syracuseStep 105997561 = 79498171) B79498171
theorem B2614619 : Blo 1375507 2614619 := bstep (se 1 (by rfl) ⟨1960964, by rfl⟩ : syracuseStep 2614619 = 3921929) B3921929
theorem B3098537 : Blo 1375507 3098537 := bstep (se 2 (by rfl) ⟨1161951, by rfl⟩ : syracuseStep 3098537 = 2323903) B2323903
theorem B17872643 : Blo 1375507 17872643 := bstep (se 1 (by rfl) ⟨13404482, by rfl⟩ : syracuseStep 17872643 = 26808965) B26808965
theorem B4407455 : Blo 1375507 4407455 := bstep (se 1 (by rfl) ⟨3305591, by rfl⟩ : syracuseStep 4407455 = 6611183) B6611183
theorem B6972317 : Blo 1375507 6972317 := bstep (se 3 (by rfl) ⟨1307309, by rfl⟩ : syracuseStep 6972317 = 2614619) B2614619
theorem B2065691 : Blo 1375507 2065691 := bstep (se 1 (by rfl) ⟨1549268, by rfl⟩ : syracuseStep 2065691 = 3098537) B3098537
theorem B11915095 : Blo 1375507 11915095 := bstep (se 1 (by rfl) ⟨8936321, by rfl⟩ : syracuseStep 11915095 = 17872643) B17872643
theorem B565320325 : Blo 1375507 565320325 := bstep (se 4 (by rfl) ⟨52998780, by rfl⟩ : syracuseStep 565320325 = 105997561) B105997561
theorem B1377127 : Blo 1375507 1377127 := bstep (se 1 (by rfl) ⟨1032845, by rfl⟩ : syracuseStep 1377127 = 2065691) B2065691
theorem B15886793 : Blo 1375507 15886793 := bstep (se 2 (by rfl) ⟨5957547, by rfl⟩ : syracuseStep 15886793 = 11915095) B11915095
theorem B4648211 : Blo 1375507 4648211 := bstep (se 1 (by rfl) ⟨3486158, by rfl⟩ : syracuseStep 4648211 = 6972317) B6972317
theorem B2938303 : Blo 1375507 2938303 := bstep (se 1 (by rfl) ⟨2203727, by rfl⟩ : syracuseStep 2938303 = 4407455) B4407455
theorem B753760433 : Blo 1375507 753760433 := bstep (se 2 (by rfl) ⟨282660162, by rfl⟩ : syracuseStep 753760433 = 565320325) B565320325
theorem B502506955 : Blo 1375507 502506955 := bstep (se 1 (by rfl) ⟨376880216, by rfl⟩ : syracuseStep 502506955 = 753760433) B753760433
theorem B3917737 : Blo 1375507 3917737 := bstep (se 2 (by rfl) ⟨1469151, by rfl⟩ : syracuseStep 3917737 = 2938303) B2938303
theorem B3098807 : Blo 1375507 3098807 := bstep (se 1 (by rfl) ⟨2324105, by rfl⟩ : syracuseStep 3098807 = 4648211) B4648211
theorem B10591195 : Blo 1375507 10591195 := bstep (se 1 (by rfl) ⟨7943396, by rfl⟩ : syracuseStep 10591195 = 15886793) B15886793
theorem B2065871 : Blo 1375507 2065871 := bstep (se 1 (by rfl) ⟨1549403, by rfl⟩ : syracuseStep 2065871 = 3098807) B3098807
theorem B5223649 : Blo 1375507 5223649 := bstep (se 2 (by rfl) ⟨1958868, by rfl⟩ : syracuseStep 5223649 = 3917737) B3917737
theorem B14121593 : Blo 1375507 14121593 := bstep (se 2 (by rfl) ⟨5295597, by rfl⟩ : syracuseStep 14121593 = 10591195) B10591195
theorem B2680037093 : Blo 1375507 2680037093 := bstep (se 4 (by rfl) ⟨251253477, by rfl⟩ : syracuseStep 2680037093 = 502506955) B502506955
theorem B1377247 : Blo 1375507 1377247 := bstep (se 1 (by rfl) ⟨1032935, by rfl⟩ : syracuseStep 1377247 = 2065871) B2065871
theorem B6964865 : Blo 1375507 6964865 := bstep (se 2 (by rfl) ⟨2611824, by rfl⟩ : syracuseStep 6964865 = 5223649) B5223649
theorem B9414395 : Blo 1375507 9414395 := bstep (se 1 (by rfl) ⟨7060796, by rfl⟩ : syracuseStep 9414395 = 14121593) B14121593
theorem B1786691395 : Blo 1375507 1786691395 := bstep (se 1 (by rfl) ⟨1340018546, by rfl⟩ : syracuseStep 1786691395 = 2680037093) B2680037093
theorem B6276263 : Blo 1375507 6276263 := bstep (se 1 (by rfl) ⟨4707197, by rfl⟩ : syracuseStep 6276263 = 9414395) B9414395
theorem B2382255193 : Blo 1375507 2382255193 := bstep (se 2 (by rfl) ⟨893345697, by rfl⟩ : syracuseStep 2382255193 = 1786691395) B1786691395
theorem B4643243 : Blo 1375507 4643243 := bstep (se 1 (by rfl) ⟨3482432, by rfl⟩ : syracuseStep 4643243 = 6964865) B6964865
theorem B16736701 : Blo 1375507 16736701 := bstep (se 3 (by rfl) ⟨3138131, by rfl⟩ : syracuseStep 16736701 = 6276263) B6276263
theorem B3176340257 : Blo 1375507 3176340257 := bstep (se 2 (by rfl) ⟨1191127596, by rfl⟩ : syracuseStep 3176340257 = 2382255193) B2382255193
theorem B3095495 : Blo 1375507 3095495 := bstep (se 1 (by rfl) ⟨2321621, by rfl⟩ : syracuseStep 3095495 = 4643243) B4643243
theorem B22315601 : Blo 1375507 22315601 := bstep (se 2 (by rfl) ⟨8368350, by rfl⟩ : syracuseStep 22315601 = 16736701) B16736701
theorem B2117560171 : Blo 1375507 2117560171 := bstep (se 1 (by rfl) ⟨1588170128, by rfl⟩ : syracuseStep 2117560171 = 3176340257) B3176340257
theorem B2063663 : Blo 1375507 2063663 := bstep (se 1 (by rfl) ⟨1547747, by rfl⟩ : syracuseStep 2063663 = 3095495) B3095495
theorem B14877067 : Blo 1375507 14877067 := bstep (se 1 (by rfl) ⟨11157800, by rfl⟩ : syracuseStep 14877067 = 22315601) B22315601
theorem B1375775 : Blo 1375507 1375775 := bstep (se 1 (by rfl) ⟨1031831, by rfl⟩ : syracuseStep 1375775 = 2063663) B2063663
theorem B2823413561 : Blo 1375507 2823413561 := bstep (se 2 (by rfl) ⟨1058780085, by rfl⟩ : syracuseStep 2823413561 = 2117560171) B2117560171
theorem B19836089 : Blo 1375507 19836089 := bstep (se 2 (by rfl) ⟨7438533, by rfl⟩ : syracuseStep 19836089 = 14877067) B14877067
theorem B1882275707 : Blo 1375507 1882275707 := bstep (se 1 (by rfl) ⟨1411706780, by rfl⟩ : syracuseStep 1882275707 = 2823413561) B2823413561
theorem B13224059 : Blo 1375507 13224059 := bstep (se 1 (by rfl) ⟨9918044, by rfl⟩ : syracuseStep 13224059 = 19836089) B19836089
theorem B1254850471 : Blo 1375507 1254850471 := bstep (se 1 (by rfl) ⟨941137853, by rfl⟩ : syracuseStep 1254850471 = 1882275707) B1882275707
theorem B8816039 : Blo 1375507 8816039 := bstep (se 1 (by rfl) ⟨6612029, by rfl⟩ : syracuseStep 8816039 = 13224059) B13224059
theorem B6692535845 : Blo 1375507 6692535845 := bstep (se 4 (by rfl) ⟨627425235, by rfl⟩ : syracuseStep 6692535845 = 1254850471) B1254850471
theorem B5877359 : Blo 1375507 5877359 := bstep (se 1 (by rfl) ⟨4408019, by rfl⟩ : syracuseStep 5877359 = 8816039) B8816039
theorem B4461690563 : Blo 1375507 4461690563 := bstep (se 1 (by rfl) ⟨3346267922, by rfl⟩ : syracuseStep 4461690563 = 6692535845) B6692535845
theorem B3918239 : Blo 1375507 3918239 := bstep (se 1 (by rfl) ⟨2938679, by rfl⟩ : syracuseStep 3918239 = 5877359) B5877359
theorem B2974460375 : Blo 1375507 2974460375 := bstep (se 1 (by rfl) ⟨2230845281, by rfl⟩ : syracuseStep 2974460375 = 4461690563) B4461690563
theorem B1982973583 : Blo 1375507 1982973583 := bstep (se 1 (by rfl) ⟨1487230187, by rfl⟩ : syracuseStep 1982973583 = 2974460375) B2974460375
theorem B2612159 : Blo 1375507 2612159 := bstep (se 1 (by rfl) ⟨1959119, by rfl⟩ : syracuseStep 2612159 = 3918239) B3918239
theorem B1741439 : Blo 1375507 1741439 := bstep (se 1 (by rfl) ⟨1306079, by rfl⟩ : syracuseStep 1741439 = 2612159) B2612159
theorem B2643964777 : Blo 1375507 2643964777 := bstep (se 2 (by rfl) ⟨991486791, by rfl⟩ : syracuseStep 2643964777 = 1982973583) B1982973583
theorem B3525286369 : Blo 1375507 3525286369 := bstep (se 2 (by rfl) ⟨1321982388, by rfl⟩ : syracuseStep 3525286369 = 2643964777) B2643964777
theorem B4643837 : Blo 1375507 4643837 := bstep (se 3 (by rfl) ⟨870719, by rfl⟩ : syracuseStep 4643837 = 1741439) B1741439
theorem B4700381825 : Blo 1375507 4700381825 := bstep (se 2 (by rfl) ⟨1762643184, by rfl⟩ : syracuseStep 4700381825 = 3525286369) B3525286369
theorem B3095891 : Blo 1375507 3095891 := bstep (se 1 (by rfl) ⟨2321918, by rfl⟩ : syracuseStep 3095891 = 4643837) B4643837
theorem B3133587883 : Blo 1375507 3133587883 := bstep (se 1 (by rfl) ⟨2350190912, by rfl⟩ : syracuseStep 3133587883 = 4700381825) B4700381825
theorem B2063927 : Blo 1375507 2063927 := bstep (se 1 (by rfl) ⟨1547945, by rfl⟩ : syracuseStep 2063927 = 3095891) B3095891
theorem B4178117177 : Blo 1375507 4178117177 := bstep (se 2 (by rfl) ⟨1566793941, by rfl⟩ : syracuseStep 4178117177 = 3133587883) B3133587883
theorem B1375951 : Blo 1375507 1375951 := bstep (se 1 (by rfl) ⟨1031963, by rfl⟩ : syracuseStep 1375951 = 2063927) B2063927
theorem B2785411451 : Blo 1375507 2785411451 := bstep (se 1 (by rfl) ⟨2089058588, by rfl⟩ : syracuseStep 2785411451 = 4178117177) B4178117177
theorem B1856940967 : Blo 1375507 1856940967 := bstep (se 1 (by rfl) ⟨1392705725, by rfl⟩ : syracuseStep 1856940967 = 2785411451) B2785411451
theorem B2475921289 : Blo 1375507 2475921289 := bstep (se 2 (by rfl) ⟨928470483, by rfl⟩ : syracuseStep 2475921289 = 1856940967) B1856940967
theorem B3301228385 : Blo 1375507 3301228385 := bstep (se 2 (by rfl) ⟨1237960644, by rfl⟩ : syracuseStep 3301228385 = 2475921289) B2475921289
theorem B2200818923 : Blo 1375507 2200818923 := bstep (se 1 (by rfl) ⟨1650614192, by rfl⟩ : syracuseStep 2200818923 = 3301228385) B3301228385
theorem B1467212615 : Blo 1375507 1467212615 := bstep (se 1 (by rfl) ⟨1100409461, by rfl⟩ : syracuseStep 1467212615 = 2200818923) B2200818923
theorem B978141743 : Blo 1375507 978141743 := bstep (se 1 (by rfl) ⟨733606307, by rfl⟩ : syracuseStep 978141743 = 1467212615) B1467212615
theorem B652094495 : Blo 1375507 652094495 := bstep (se 1 (by rfl) ⟨489070871, by rfl⟩ : syracuseStep 652094495 = 978141743) B978141743
theorem B434729663 : Blo 1375507 434729663 := bstep (se 1 (by rfl) ⟨326047247, by rfl⟩ : syracuseStep 434729663 = 652094495) B652094495
theorem B289819775 : Blo 1375507 289819775 := bstep (se 1 (by rfl) ⟨217364831, by rfl⟩ : syracuseStep 289819775 = 434729663) B434729663
theorem B193213183 : Blo 1375507 193213183 := bstep (se 1 (by rfl) ⟨144909887, by rfl⟩ : syracuseStep 193213183 = 289819775) B289819775
theorem B257617577 : Blo 1375507 257617577 := bstep (se 2 (by rfl) ⟨96606591, by rfl⟩ : syracuseStep 257617577 = 193213183) B193213183
theorem B171745051 : Blo 1375507 171745051 := bstep (se 1 (by rfl) ⟨128808788, by rfl⟩ : syracuseStep 171745051 = 257617577) B257617577
theorem B228993401 : Blo 1375507 228993401 := bstep (se 2 (by rfl) ⟨85872525, by rfl⟩ : syracuseStep 228993401 = 171745051) B171745051
theorem B152662267 : Blo 1375507 152662267 := bstep (se 1 (by rfl) ⟨114496700, by rfl⟩ : syracuseStep 152662267 = 228993401) B228993401
theorem B203549689 : Blo 1375507 203549689 := bstep (se 2 (by rfl) ⟨76331133, by rfl⟩ : syracuseStep 203549689 = 152662267) B152662267
theorem B271399585 : Blo 1375507 271399585 := bstep (se 2 (by rfl) ⟨101774844, by rfl⟩ : syracuseStep 271399585 = 203549689) B203549689
theorem B361866113 : Blo 1375507 361866113 := bstep (se 2 (by rfl) ⟨135699792, by rfl⟩ : syracuseStep 361866113 = 271399585) B271399585
theorem B241244075 : Blo 1375507 241244075 := bstep (se 1 (by rfl) ⟨180933056, by rfl⟩ : syracuseStep 241244075 = 361866113) B361866113
theorem B160829383 : Blo 1375507 160829383 := bstep (se 1 (by rfl) ⟨120622037, by rfl⟩ : syracuseStep 160829383 = 241244075) B241244075
theorem B214439177 : Blo 1375507 214439177 := bstep (se 2 (by rfl) ⟨80414691, by rfl⟩ : syracuseStep 214439177 = 160829383) B160829383
theorem B142959451 : Blo 1375507 142959451 := bstep (se 1 (by rfl) ⟨107219588, by rfl⟩ : syracuseStep 142959451 = 214439177) B214439177
theorem B190612601 : Blo 1375507 190612601 := bstep (se 2 (by rfl) ⟨71479725, by rfl⟩ : syracuseStep 190612601 = 142959451) B142959451
theorem B127075067 : Blo 1375507 127075067 := bstep (se 1 (by rfl) ⟨95306300, by rfl⟩ : syracuseStep 127075067 = 190612601) B190612601
theorem B84716711 : Blo 1375507 84716711 := bstep (se 1 (by rfl) ⟨63537533, by rfl⟩ : syracuseStep 84716711 = 127075067) B127075067
theorem B56477807 : Blo 1375507 56477807 := bstep (se 1 (by rfl) ⟨42358355, by rfl⟩ : syracuseStep 56477807 = 84716711) B84716711
theorem B37651871 : Blo 1375507 37651871 := bstep (se 1 (by rfl) ⟨28238903, by rfl⟩ : syracuseStep 37651871 = 56477807) B56477807
theorem B25101247 : Blo 1375507 25101247 := bstep (se 1 (by rfl) ⟨18825935, by rfl⟩ : syracuseStep 25101247 = 37651871) B37651871
theorem B33468329 : Blo 1375507 33468329 := bstep (se 2 (by rfl) ⟨12550623, by rfl⟩ : syracuseStep 33468329 = 25101247) B25101247
theorem B22312219 : Blo 1375507 22312219 := bstep (se 1 (by rfl) ⟨16734164, by rfl⟩ : syracuseStep 22312219 = 33468329) B33468329
theorem B29749625 : Blo 1375507 29749625 := bstep (se 2 (by rfl) ⟨11156109, by rfl⟩ : syracuseStep 29749625 = 22312219) B22312219
theorem B19833083 : Blo 1375507 19833083 := bstep (se 1 (by rfl) ⟨14874812, by rfl⟩ : syracuseStep 19833083 = 29749625) B29749625
theorem B13222055 : Blo 1375507 13222055 := bstep (se 1 (by rfl) ⟨9916541, by rfl⟩ : syracuseStep 13222055 = 19833083) B19833083
theorem B35258813 : Blo 1375507 35258813 := bstep (se 3 (by rfl) ⟨6611027, by rfl⟩ : syracuseStep 35258813 = 13222055) B13222055
theorem B23505875 : Blo 1375507 23505875 := bstep (se 1 (by rfl) ⟨17629406, by rfl⟩ : syracuseStep 23505875 = 35258813) B35258813
theorem B15670583 : Blo 1375507 15670583 := bstep (se 1 (by rfl) ⟨11752937, by rfl⟩ : syracuseStep 15670583 = 23505875) B23505875
theorem B10447055 : Blo 1375507 10447055 := bstep (se 1 (by rfl) ⟨7835291, by rfl⟩ : syracuseStep 10447055 = 15670583) B15670583
theorem B6964703 : Blo 1375507 6964703 := bstep (se 1 (by rfl) ⟨5223527, by rfl⟩ : syracuseStep 6964703 = 10447055) B10447055
theorem B4643135 : Blo 1375507 4643135 := bstep (se 1 (by rfl) ⟨3482351, by rfl⟩ : syracuseStep 4643135 = 6964703) B6964703
theorem B3095423 : Blo 1375507 3095423 := bstep (se 1 (by rfl) ⟨2321567, by rfl⟩ : syracuseStep 3095423 = 4643135) B4643135
theorem B2063615 : Blo 1375507 2063615 := bstep (se 1 (by rfl) ⟨1547711, by rfl⟩ : syracuseStep 2063615 = 3095423) B3095423
theorem B1375743 : Blo 1375507 1375743 := bstep (se 1 (by rfl) ⟨1031807, by rfl⟩ : syracuseStep 1375743 = 2063615) B2063615

theorem C0 (j : ℕ) (h1 : 343876 ≤ j) (h2 : j ≤ 344376) : Blo 1375507 (4 * j + 3) := by
  interval_cases j
  · exact B1375507
  · exact B1375511
  · exact B1375515
  · exact B1375519
  · exact B1375523
  · exact B1375527
  · exact B1375531
  · exact B1375535
  · exact B1375539
  · exact B1375543
  · exact B1375547
  · exact B1375551
  · exact B1375555
  · exact B1375559
  · exact B1375563
  · exact B1375567
  · exact B1375571
  · exact B1375575
  · exact B1375579
  · exact B1375583
  · exact B1375587
  · exact B1375591
  · exact B1375595
  · exact B1375599
  · exact B1375603
  · exact B1375607
  · exact B1375611
  · exact B1375615
  · exact B1375619
  · exact B1375623
  · exact B1375627
  · exact B1375631
  · exact B1375635
  · exact B1375639
  · exact B1375643
  · exact B1375647
  · exact B1375651
  · exact B1375655
  · exact B1375659
  · exact B1375663
  · exact B1375667
  · exact B1375671
  · exact B1375675
  · exact B1375679
  · exact B1375683
  · exact B1375687
  · exact B1375691
  · exact B1375695
  · exact B1375699
  · exact B1375703
  · exact B1375707
  · exact B1375711
  · exact B1375715
  · exact B1375719
  · exact B1375723
  · exact B1375727
  · exact B1375731
  · exact B1375735
  · exact B1375739
  · exact B1375743
  · exact B1375747
  · exact B1375751
  · exact B1375755
  · exact B1375759
  · exact B1375763
  · exact B1375767
  · exact B1375771
  · exact B1375775
  · exact B1375779
  · exact B1375783
  · exact B1375787
  · exact B1375791
  · exact B1375795
  · exact B1375799
  · exact B1375803
  · exact B1375807
  · exact B1375811
  · exact B1375815
  · exact B1375819
  · exact B1375823
  · exact B1375827
  · exact B1375831
  · exact B1375835
  · exact B1375839
  · exact B1375843
  · exact B1375847
  · exact B1375851
  · exact B1375855
  · exact B1375859
  · exact B1375863
  · exact B1375867
  · exact B1375871
  · exact B1375875
  · exact B1375879
  · exact B1375883
  · exact B1375887
  · exact B1375891
  · exact B1375895
  · exact B1375899
  · exact B1375903
  · exact B1375907
  · exact B1375911
  · exact B1375915
  · exact B1375919
  · exact B1375923
  · exact B1375927
  · exact B1375931
  · exact B1375935
  · exact B1375939
  · exact B1375943
  · exact B1375947
  · exact B1375951
  · exact B1375955
  · exact B1375959
  · exact B1375963
  · exact B1375967
  · exact B1375971
  · exact B1375975
  · exact B1375979
  · exact B1375983
  · exact B1375987
  · exact B1375991
  · exact B1375995
  · exact B1375999
  · exact B1376003
  · exact B1376007
  · exact B1376011
  · exact B1376015
  · exact B1376019
  · exact B1376023
  · exact B1376027
  · exact B1376031
  · exact B1376035
  · exact B1376039
  · exact B1376043
  · exact B1376047
  · exact B1376051
  · exact B1376055
  · exact B1376059
  · exact B1376063
  · exact B1376067
  · exact B1376071
  · exact B1376075
  · exact B1376079
  · exact B1376083
  · exact B1376087
  · exact B1376091
  · exact B1376095
  · exact B1376099
  · exact B1376103
  · exact B1376107
  · exact B1376111
  · exact B1376115
  · exact B1376119
  · exact B1376123
  · exact B1376127
  · exact B1376131
  · exact B1376135
  · exact B1376139
  · exact B1376143
  · exact B1376147
  · exact B1376151
  · exact B1376155
  · exact B1376159
  · exact B1376163
  · exact B1376167
  · exact B1376171
  · exact B1376175
  · exact B1376179
  · exact B1376183
  · exact B1376187
  · exact B1376191
  · exact B1376195
  · exact B1376199
  · exact B1376203
  · exact B1376207
  · exact B1376211
  · exact B1376215
  · exact B1376219
  · exact B1376223
  · exact B1376227
  · exact B1376231
  · exact B1376235
  · exact B1376239
  · exact B1376243
  · exact B1376247
  · exact B1376251
  · exact B1376255
  · exact B1376259
  · exact B1376263
  · exact B1376267
  · exact B1376271
  · exact B1376275
  · exact B1376279
  · exact B1376283
  · exact B1376287
  · exact B1376291
  · exact B1376295
  · exact B1376299
  · exact B1376303
  · exact B1376307
  · exact B1376311
  · exact B1376315
  · exact B1376319
  · exact B1376323
  · exact B1376327
  · exact B1376331
  · exact B1376335
  · exact B1376339
  · exact B1376343
  · exact B1376347
  · exact B1376351
  · exact B1376355
  · exact B1376359
  · exact B1376363
  · exact B1376367
  · exact B1376371
  · exact B1376375
  · exact B1376379
  · exact B1376383
  · exact B1376387
  · exact B1376391
  · exact B1376395
  · exact B1376399
  · exact B1376403
  · exact B1376407
  · exact B1376411
  · exact B1376415
  · exact B1376419
  · exact B1376423
  · exact B1376427
  · exact B1376431
  · exact B1376435
  · exact B1376439
  · exact B1376443
  · exact B1376447
  · exact B1376451
  · exact B1376455
  · exact B1376459
  · exact B1376463
  · exact B1376467
  · exact B1376471
  · exact B1376475
  · exact B1376479
  · exact B1376483
  · exact B1376487
  · exact B1376491
  · exact B1376495
  · exact B1376499
  · exact B1376503
  · exact B1376507
  · exact B1376511
  · exact B1376515
  · exact B1376519
  · exact B1376523
  · exact B1376527
  · exact B1376531
  · exact B1376535
  · exact B1376539
  · exact B1376543
  · exact B1376547
  · exact B1376551
  · exact B1376555
  · exact B1376559
  · exact B1376563
  · exact B1376567
  · exact B1376571
  · exact B1376575
  · exact B1376579
  · exact B1376583
  · exact B1376587
  · exact B1376591
  · exact B1376595
  · exact B1376599
  · exact B1376603
  · exact B1376607
  · exact B1376611
  · exact B1376615
  · exact B1376619
  · exact B1376623
  · exact B1376627
  · exact B1376631
  · exact B1376635
  · exact B1376639
  · exact B1376643
  · exact B1376647
  · exact B1376651
  · exact B1376655
  · exact B1376659
  · exact B1376663
  · exact B1376667
  · exact B1376671
  · exact B1376675
  · exact B1376679
  · exact B1376683
  · exact B1376687
  · exact B1376691
  · exact B1376695
  · exact B1376699
  · exact B1376703
  · exact B1376707
  · exact B1376711
  · exact B1376715
  · exact B1376719
  · exact B1376723
  · exact B1376727
  · exact B1376731
  · exact B1376735
  · exact B1376739
  · exact B1376743
  · exact B1376747
  · exact B1376751
  · exact B1376755
  · exact B1376759
  · exact B1376763
  · exact B1376767
  · exact B1376771
  · exact B1376775
  · exact B1376779
  · exact B1376783
  · exact B1376787
  · exact B1376791
  · exact B1376795
  · exact B1376799
  · exact B1376803
  · exact B1376807
  · exact B1376811
  · exact B1376815
  · exact B1376819
  · exact B1376823
  · exact B1376827
  · exact B1376831
  · exact B1376835
  · exact B1376839
  · exact B1376843
  · exact B1376847
  · exact B1376851
  · exact B1376855
  · exact B1376859
  · exact B1376863
  · exact B1376867
  · exact B1376871
  · exact B1376875
  · exact B1376879
  · exact B1376883
  · exact B1376887
  · exact B1376891
  · exact B1376895
  · exact B1376899
  · exact B1376903
  · exact B1376907
  · exact B1376911
  · exact B1376915
  · exact B1376919
  · exact B1376923
  · exact B1376927
  · exact B1376931
  · exact B1376935
  · exact B1376939
  · exact B1376943
  · exact B1376947
  · exact B1376951
  · exact B1376955
  · exact B1376959
  · exact B1376963
  · exact B1376967
  · exact B1376971
  · exact B1376975
  · exact B1376979
  · exact B1376983
  · exact B1376987
  · exact B1376991
  · exact B1376995
  · exact B1376999
  · exact B1377003
  · exact B1377007
  · exact B1377011
  · exact B1377015
  · exact B1377019
  · exact B1377023
  · exact B1377027
  · exact B1377031
  · exact B1377035
  · exact B1377039
  · exact B1377043
  · exact B1377047
  · exact B1377051
  · exact B1377055
  · exact B1377059
  · exact B1377063
  · exact B1377067
  · exact B1377071
  · exact B1377075
  · exact B1377079
  · exact B1377083
  · exact B1377087
  · exact B1377091
  · exact B1377095
  · exact B1377099
  · exact B1377103
  · exact B1377107
  · exact B1377111
  · exact B1377115
  · exact B1377119
  · exact B1377123
  · exact B1377127
  · exact B1377131
  · exact B1377135
  · exact B1377139
  · exact B1377143
  · exact B1377147
  · exact B1377151
  · exact B1377155
  · exact B1377159
  · exact B1377163
  · exact B1377167
  · exact B1377171
  · exact B1377175
  · exact B1377179
  · exact B1377183
  · exact B1377187
  · exact B1377191
  · exact B1377195
  · exact B1377199
  · exact B1377203
  · exact B1377207
  · exact B1377211
  · exact B1377215
  · exact B1377219
  · exact B1377223
  · exact B1377227
  · exact B1377231
  · exact B1377235
  · exact B1377239
  · exact B1377243
  · exact B1377247
  · exact B1377251
  · exact B1377255
  · exact B1377259
  · exact B1377263
  · exact B1377267
  · exact B1377271
  · exact B1377275
  · exact B1377279
  · exact B1377283
  · exact B1377287
  · exact B1377291
  · exact B1377295
  · exact B1377299
  · exact B1377303
  · exact B1377307
  · exact B1377311
  · exact B1377315
  · exact B1377319
  · exact B1377323
  · exact B1377327
  · exact B1377331
  · exact B1377335
  · exact B1377339
  · exact B1377343
  · exact B1377347
  · exact B1377351
  · exact B1377355
  · exact B1377359
  · exact B1377363
  · exact B1377367
  · exact B1377371
  · exact B1377375
  · exact B1377379
  · exact B1377383
  · exact B1377387
  · exact B1377391
  · exact B1377395
  · exact B1377399
  · exact B1377403
  · exact B1377407
  · exact B1377411
  · exact B1377415
  · exact B1377419
  · exact B1377423
  · exact B1377427
  · exact B1377431
  · exact B1377435
  · exact B1377439
  · exact B1377443
  · exact B1377447
  · exact B1377451
  · exact B1377455
  · exact B1377459
  · exact B1377463
  · exact B1377467
  · exact B1377471
  · exact B1377475
  · exact B1377479
  · exact B1377483
  · exact B1377487
  · exact B1377491
  · exact B1377495
  · exact B1377499
  · exact B1377503
  · exact B1377507

theorem solution (m : ℕ) (hlo : 1375507 ≤ m) (hhi : m ≤ 1377507) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 343876 ≤ j := by omega
    have hj2 : j ≤ 344376 := by omega
    have hb : Blo 1375507 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
