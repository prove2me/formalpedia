-- Prove2me | solution 1 for syracuse_descends_range_1772087_1774087
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:42:14.906325+00:00
-- url     : https://prove2.me/submissions/fe7885e1-4dc6-46d5-81fe-b05426b7c4c5

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


theorem B3366917 : Blo 1772087 3366917 := bbase (se 4 (by rfl) ⟨315648, by rfl⟩ : syracuseStep 3366917 = 631297) (by norm_num)
theorem B2768933 : Blo 1772087 2768933 := bbase (se 4 (by rfl) ⟨259587, by rfl⟩ : syracuseStep 2768933 = 519175) (by norm_num)
theorem B4489253 : Blo 1772087 4489253 := bbase (se 4 (by rfl) ⟨420867, by rfl⟩ : syracuseStep 4489253 = 841735) (by norm_num)
theorem B1892413 : Blo 1772087 1892413 := bbase (se 3 (by rfl) ⟨354827, by rfl⟩ : syracuseStep 1892413 = 709655) (by norm_num)
theorem B4259909 : Blo 1772087 4259909 := bbase (se 4 (by rfl) ⟨399366, by rfl⟩ : syracuseStep 4259909 = 798733) (by norm_num)
theorem B3989573 : Blo 1772087 3989573 := bbase (se 4 (by rfl) ⟨374022, by rfl⟩ : syracuseStep 3989573 = 748045) (by norm_num)
theorem B2130013 : Blo 1772087 2130013 := bbase (se 3 (by rfl) ⟨399377, by rfl⟩ : syracuseStep 2130013 = 798755) (by norm_num)
theorem B6733925 : Blo 1772087 6733925 := bbase (se 4 (by rfl) ⟨631305, by rfl⟩ : syracuseStep 6733925 = 1262611) (by norm_num)
theorem B4317293 : Blo 1772087 4317293 := bbase (se 3 (by rfl) ⟨809492, by rfl⟩ : syracuseStep 4317293 = 1618985) (by norm_num)
theorem B3989645 : Blo 1772087 3989645 := bbase (se 3 (by rfl) ⟨748058, by rfl⟩ : syracuseStep 3989645 = 1496117) (by norm_num)
theorem B2244773 : Blo 1772087 2244773 := bbase (se 4 (by rfl) ⟨210447, by rfl⟩ : syracuseStep 2244773 = 420895) (by norm_num)
theorem B3989717 : Blo 1772087 3989717 := bbase (se 7 (by rfl) ⟨46754, by rfl⟩ : syracuseStep 3989717 = 93509) (by norm_num)
theorem B2244829 : Blo 1772087 2244829 := bbase (se 3 (by rfl) ⟨420905, by rfl⟩ : syracuseStep 2244829 = 841811) (by norm_num)
theorem B4489445 : Blo 1772087 4489445 := bbase (se 4 (by rfl) ⟨420885, by rfl⟩ : syracuseStep 4489445 = 841771) (by norm_num)
theorem B8085749 : Blo 1772087 8085749 := bbase (se 5 (by rfl) ⟨379019, by rfl⟩ : syracuseStep 8085749 = 758039) (by norm_num)
theorem B2130205 : Blo 1772087 2130205 := bbase (se 3 (by rfl) ⟨399413, by rfl⟩ : syracuseStep 2130205 = 798827) (by norm_num)
theorem B3989789 : Blo 1772087 3989789 := bbase (se 3 (by rfl) ⟨748085, by rfl⟩ : syracuseStep 3989789 = 1496171) (by norm_num)
theorem B2244925 : Blo 1772087 2244925 := bbase (se 3 (by rfl) ⟨420923, by rfl⟩ : syracuseStep 2244925 = 841847) (by norm_num)
theorem B2990405 : Blo 1772087 2990405 := bbase (se 4 (by rfl) ⟨280350, by rfl⟩ : syracuseStep 2990405 = 560701) (by norm_num)
theorem B13648213 : Blo 1772087 13648213 := bbase (se 10 (by rfl) ⟨19992, by rfl⟩ : syracuseStep 13648213 = 39985) (by norm_num)
theorem B3989861 : Blo 1772087 3989861 := bbase (se 4 (by rfl) ⟨374049, by rfl⟩ : syracuseStep 3989861 = 748099) (by norm_num)
theorem B5677445 : Blo 1772087 5677445 := bbase (se 4 (by rfl) ⟨532260, by rfl⟩ : syracuseStep 5677445 = 1064521) (by norm_num)
theorem B2523565 : Blo 1772087 2523565 := bbase (se 3 (by rfl) ⟨473168, by rfl⟩ : syracuseStep 2523565 = 946337) (by norm_num)
theorem B2130349 : Blo 1772087 2130349 := bbase (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) (by norm_num)
theorem B3989933 : Blo 1772087 3989933 := bbase (se 3 (by rfl) ⟨748112, by rfl⟩ : syracuseStep 3989933 = 1496225) (by norm_num)
theorem B12779957 : Blo 1772087 12779957 := bbase (se 5 (by rfl) ⟨599060, by rfl⟩ : syracuseStep 12779957 = 1198121) (by norm_num)
theorem B2990533 : Blo 1772087 2990533 := bbase (se 4 (by rfl) ⟨280362, by rfl⟩ : syracuseStep 2990533 = 560725) (by norm_num)
theorem B8085989 : Blo 1772087 8085989 := bbase (se 4 (by rfl) ⟨758061, by rfl⟩ : syracuseStep 8085989 = 1516123) (by norm_num)
theorem B2245097 : Blo 1772087 2245097 := bbase (se 2 (by rfl) ⟨841911, by rfl⟩ : syracuseStep 2245097 = 1683823) (by norm_num)
theorem B1892845 : Blo 1772087 1892845 := bbase (se 3 (by rfl) ⟨354908, by rfl⟩ : syracuseStep 1892845 = 709817) (by norm_num)
theorem B3990005 : Blo 1772087 3990005 := bbase (se 5 (by rfl) ⟨187031, by rfl⟩ : syracuseStep 3990005 = 374063) (by norm_num)
theorem B5677573 : Blo 1772087 5677573 := bbase (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) (by norm_num)
theorem B2990621 : Blo 1772087 2990621 := bbase (se 3 (by rfl) ⟨560741, by rfl⟩ : syracuseStep 2990621 = 1121483) (by norm_num)
theorem B2245153 : Blo 1772087 2245153 := bbase (se 2 (by rfl) ⟨841932, by rfl⟩ : syracuseStep 2245153 = 1683865) (by norm_num)
theorem B1892917 : Blo 1772087 1892917 := bbase (se 5 (by rfl) ⟨88730, by rfl⟩ : syracuseStep 1892917 = 177461) (by norm_num)
theorem B3990077 : Blo 1772087 3990077 := bbase (se 3 (by rfl) ⟨748139, by rfl⟩ : syracuseStep 3990077 = 1496279) (by norm_num)
theorem B4489789 : Blo 1772087 4489789 := bbase (se 3 (by rfl) ⟨841835, by rfl⟩ : syracuseStep 4489789 = 1683671) (by norm_num)
theorem B2245249 : Blo 1772087 2245249 := bbase (se 2 (by rfl) ⟨841968, by rfl⟩ : syracuseStep 2245249 = 1683937) (by norm_num)
theorem B3990149 : Blo 1772087 3990149 := bbase (se 4 (by rfl) ⟨374076, by rfl⟩ : syracuseStep 3990149 = 748153) (by norm_num)
theorem B6062741 : Blo 1772087 6062741 := bbase (se 6 (by rfl) ⟨142095, by rfl⟩ : syracuseStep 6062741 = 284191) (by norm_num)
theorem B2990749 : Blo 1772087 2990749 := bbase (se 3 (by rfl) ⟨560765, by rfl⟩ : syracuseStep 2990749 = 1121531) (by norm_num)
theorem B4489901 : Blo 1772087 4489901 := bbase (se 3 (by rfl) ⟨841856, by rfl⟩ : syracuseStep 4489901 = 1683713) (by norm_num)
theorem B3990221 : Blo 1772087 3990221 := bbase (se 3 (by rfl) ⟨748166, by rfl⟩ : syracuseStep 3990221 = 1496333) (by norm_num)
theorem B8086229 : Blo 1772087 8086229 := bbase (se 7 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 8086229 = 189521) (by norm_num)
theorem B8979173 : Blo 1772087 8979173 := bbase (se 4 (by rfl) ⟨841797, by rfl⟩ : syracuseStep 8979173 = 1683595) (by norm_num)
theorem B9102053 : Blo 1772087 9102053 := bbase (se 4 (by rfl) ⟨853317, by rfl⟩ : syracuseStep 9102053 = 1706635) (by norm_num)
theorem B2990837 : Blo 1772087 2990837 := bbase (se 5 (by rfl) ⟨140195, by rfl⟩ : syracuseStep 2990837 = 280391) (by norm_num)
theorem B3367669 : Blo 1772087 3367669 := bbase (se 5 (by rfl) ⟨157859, by rfl⟩ : syracuseStep 3367669 = 315719) (by norm_num)
theorem B2523901 : Blo 1772087 2523901 := bbase (se 3 (by rfl) ⟨473231, by rfl⟩ : syracuseStep 2523901 = 946463) (by norm_num)
theorem B5677829 : Blo 1772087 5677829 := bbase (se 4 (by rfl) ⟨532296, by rfl⟩ : syracuseStep 5677829 = 1064593) (by norm_num)
theorem B3990293 : Blo 1772087 3990293 := bbase (se 6 (by rfl) ⟨93522, by rfl⟩ : syracuseStep 3990293 = 187045) (by norm_num)
theorem B5391157 : Blo 1772087 5391157 := bbase (se 5 (by rfl) ⟨252710, by rfl⟩ : syracuseStep 5391157 = 505421) (by norm_num)
theorem B3990365 : Blo 1772087 3990365 := bbase (se 3 (by rfl) ⟨748193, by rfl⟩ : syracuseStep 3990365 = 1496387) (by norm_num)
theorem B4490093 : Blo 1772087 4490093 := bbase (se 3 (by rfl) ⟨841892, by rfl⟩ : syracuseStep 4490093 = 1683785) (by norm_num)
theorem B2990965 : Blo 1772087 2990965 := bbase (se 5 (by rfl) ⟨140201, by rfl⟩ : syracuseStep 2990965 = 280403) (by norm_num)
theorem B3367813 : Blo 1772087 3367813 := bbase (se 4 (by rfl) ⟨315732, by rfl⟩ : syracuseStep 3367813 = 631465) (by norm_num)
theorem B3785629 : Blo 1772087 3785629 := bbase (se 3 (by rfl) ⟨709805, by rfl⟩ : syracuseStep 3785629 = 1419611) (by norm_num)
theorem B5981093 : Blo 1772087 5981093 := bbase (se 4 (by rfl) ⟨560727, by rfl⟩ : syracuseStep 5981093 = 1121455) (by norm_num)
theorem B3990437 : Blo 1772087 3990437 := bbase (se 4 (by rfl) ⟨374103, by rfl⟩ : syracuseStep 3990437 = 748207) (by norm_num)
theorem B1893289 : Blo 1772087 1893289 := bbase (se 2 (by rfl) ⟨709983, by rfl⟩ : syracuseStep 1893289 = 1419967) (by norm_num)
theorem B2991053 : Blo 1772087 2991053 := bbase (se 3 (by rfl) ⟨560822, by rfl⟩ : syracuseStep 2991053 = 1121645) (by norm_num)
theorem B2524117 : Blo 1772087 2524117 := bbase (se 7 (by rfl) ⟨29579, by rfl⟩ : syracuseStep 2524117 = 59159) (by norm_num)
theorem B3990509 : Blo 1772087 3990509 := bbase (se 3 (by rfl) ⟨748220, by rfl⟩ : syracuseStep 3990509 = 1496441) (by norm_num)
theorem B3367973 : Blo 1772087 3367973 := bbase (se 4 (by rfl) ⟨315747, by rfl⟩ : syracuseStep 3367973 = 631495) (by norm_num)
theorem B3990581 : Blo 1772087 3990581 := bbase (se 5 (by rfl) ⟨187058, by rfl⟩ : syracuseStep 3990581 = 374117) (by norm_num)
theorem B2991181 : Blo 1772087 2991181 := bbase (se 3 (by rfl) ⟨560846, by rfl⟩ : syracuseStep 2991181 = 1121693) (by norm_num)
theorem B3990653 : Blo 1772087 3990653 := bbase (se 3 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 3990653 = 1496495) (by norm_num)
theorem B8971397 : Blo 1772087 8971397 := bbase (se 4 (by rfl) ⟨841068, by rfl⟩ : syracuseStep 8971397 = 1682137) (by norm_num)
theorem B2991269 : Blo 1772087 2991269 := bbase (se 4 (by rfl) ⟨280431, by rfl⟩ : syracuseStep 2991269 = 560863) (by norm_num)
theorem B3990725 : Blo 1772087 3990725 := bbase (se 4 (by rfl) ⟨374130, by rfl⟩ : syracuseStep 3990725 = 748261) (by norm_num)
theorem B4490437 : Blo 1772087 4490437 := bbase (se 4 (by rfl) ⟨420978, by rfl⟩ : syracuseStep 4490437 = 841957) (by norm_num)
theorem B11355349 : Blo 1772087 11355349 := bbase (se 7 (by rfl) ⟨133070, by rfl⟩ : syracuseStep 11355349 = 266141) (by norm_num)
theorem B6735109 : Blo 1772087 6735109 := bbase (se 4 (by rfl) ⟨631416, by rfl⟩ : syracuseStep 6735109 = 1262833) (by norm_num)
theorem B3990797 : Blo 1772087 3990797 := bbase (se 3 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 3990797 = 1496549) (by norm_num)
theorem B1893665 : Blo 1772087 1893665 := bbase (se 2 (by rfl) ⟨710124, by rfl⟩ : syracuseStep 1893665 = 1420249) (by norm_num)
theorem B2991397 : Blo 1772087 2991397 := bbase (se 4 (by rfl) ⟨280443, by rfl⟩ : syracuseStep 2991397 = 560887) (by norm_num)
theorem B4490549 : Blo 1772087 4490549 := bbase (se 5 (by rfl) ⟨210494, by rfl⟩ : syracuseStep 4490549 = 420989) (by norm_num)
theorem B2524493 : Blo 1772087 2524493 := bbase (se 3 (by rfl) ⟨473342, by rfl⟩ : syracuseStep 2524493 = 946685) (by norm_num)
theorem B5981525 : Blo 1772087 5981525 := bbase (se 12 (by rfl) ⟨2190, by rfl⟩ : syracuseStep 5981525 = 4381) (by norm_num)
theorem B3990869 : Blo 1772087 3990869 := bbase (se 12 (by rfl) ⟨1461, by rfl⟩ : syracuseStep 3990869 = 2923) (by norm_num)
theorem B1893737 : Blo 1772087 1893737 := bbase (se 2 (by rfl) ⟨710151, by rfl⟩ : syracuseStep 1893737 = 1420303) (by norm_num)
theorem B2991485 : Blo 1772087 2991485 := bbase (se 3 (by rfl) ⟨560903, by rfl⟩ : syracuseStep 2991485 = 1121807) (by norm_num)
theorem B3990941 : Blo 1772087 3990941 := bbase (se 3 (by rfl) ⟨748301, by rfl⟩ : syracuseStep 3990941 = 1496603) (by norm_num)
theorem B5047733 : Blo 1772087 5047733 := bbase (se 5 (by rfl) ⟨236612, by rfl⟩ : syracuseStep 5047733 = 473225) (by norm_num)
theorem B3991013 : Blo 1772087 3991013 := bbase (se 4 (by rfl) ⟨374157, by rfl⟩ : syracuseStep 3991013 = 748315) (by norm_num)
theorem B2991613 : Blo 1772087 2991613 := bbase (se 3 (by rfl) ⟨560927, by rfl⟩ : syracuseStep 2991613 = 1121855) (by norm_num)
theorem B1893925 : Blo 1772087 1893925 := bbase (se 4 (by rfl) ⟨177555, by rfl⟩ : syracuseStep 1893925 = 355111) (by norm_num)
theorem B3991085 : Blo 1772087 3991085 := bbase (se 3 (by rfl) ⟨748328, by rfl⟩ : syracuseStep 3991085 = 1496657) (by norm_num)
theorem B6735413 : Blo 1772087 6735413 := bbase (se 5 (by rfl) ⟨315722, by rfl⟩ : syracuseStep 6735413 = 631445) (by norm_num)
theorem B2991701 : Blo 1772087 2991701 := bbase (se 8 (by rfl) ⟨17529, by rfl⟩ : syracuseStep 2991701 = 35059) (by norm_num)
theorem B3991157 : Blo 1772087 3991157 := bbase (se 5 (by rfl) ⟨187085, by rfl⟩ : syracuseStep 3991157 = 374171) (by norm_num)
theorem B21849749 : Blo 1772087 21849749 := bbase (se 6 (by rfl) ⟨512103, by rfl⟩ : syracuseStep 21849749 = 1024207) (by norm_num)
theorem B7677589 : Blo 1772087 7677589 := bbase (se 6 (by rfl) ⟨179943, by rfl⟩ : syracuseStep 7677589 = 359887) (by norm_num)
theorem B3991229 : Blo 1772087 3991229 := bbase (se 3 (by rfl) ⟨748355, by rfl⟩ : syracuseStep 3991229 = 1496711) (by norm_num)
theorem B7186133 : Blo 1772087 7186133 := bbase (se 7 (by rfl) ⟨84212, by rfl⟩ : syracuseStep 7186133 = 168425) (by norm_num)
theorem B2991829 : Blo 1772087 2991829 := bbase (se 7 (by rfl) ⟨35060, by rfl⟩ : syracuseStep 2991829 = 70121) (by norm_num)
theorem B1894109 : Blo 1772087 1894109 := bbase (se 3 (by rfl) ⟨355145, by rfl⟩ : syracuseStep 1894109 = 710291) (by norm_num)
theorem B17032949 : Blo 1772087 17032949 := bbase (se 5 (by rfl) ⟨798419, by rfl⟩ : syracuseStep 17032949 = 1596839) (by norm_num)
theorem B5981957 : Blo 1772087 5981957 := bbase (se 4 (by rfl) ⟨560808, by rfl⟩ : syracuseStep 5981957 = 1121617) (by norm_num)
theorem B3991301 : Blo 1772087 3991301 := bbase (se 4 (by rfl) ⟨374184, by rfl⟩ : syracuseStep 3991301 = 748369) (by norm_num)
theorem B3786517 : Blo 1772087 3786517 := bbase (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) (by norm_num)
theorem B2991917 : Blo 1772087 2991917 := bbase (se 3 (by rfl) ⟨560984, by rfl⟩ : syracuseStep 2991917 = 1121969) (by norm_num)
theorem B3991373 : Blo 1772087 3991373 := bbase (se 3 (by rfl) ⟨748382, by rfl⟩ : syracuseStep 3991373 = 1496765) (by norm_num)
theorem B11364245 : Blo 1772087 11364245 := bbase (se 6 (by rfl) ⟨266349, by rfl⟩ : syracuseStep 11364245 = 532699) (by norm_num)
theorem B3991445 : Blo 1772087 3991445 := bbase (se 6 (by rfl) ⟨93549, by rfl⟩ : syracuseStep 3991445 = 187099) (by norm_num)
theorem B2992045 : Blo 1772087 2992045 := bbase (se 3 (by rfl) ⟨561008, by rfl⟩ : syracuseStep 2992045 = 1122017) (by norm_num)
theorem B9586613 : Blo 1772087 9586613 := bbase (se 5 (by rfl) ⟨449372, by rfl⟩ : syracuseStep 9586613 = 898745) (by norm_num)
theorem B5392325 : Blo 1772087 5392325 := bbase (se 4 (by rfl) ⟨505530, by rfl⟩ : syracuseStep 5392325 = 1011061) (by norm_num)
theorem B3991517 : Blo 1772087 3991517 := bbase (se 3 (by rfl) ⟨748409, by rfl⟩ : syracuseStep 3991517 = 1496819) (by norm_num)
theorem B8980469 : Blo 1772087 8980469 := bbase (se 5 (by rfl) ⟨420959, by rfl⟩ : syracuseStep 8980469 = 841919) (by norm_num)
theorem B2992133 : Blo 1772087 2992133 := bbase (se 4 (by rfl) ⟨280512, by rfl⟩ : syracuseStep 2992133 = 561025) (by norm_num)
theorem B4261909 : Blo 1772087 4261909 := bbase (se 6 (by rfl) ⟨99888, by rfl⟩ : syracuseStep 4261909 = 199777) (by norm_num)
theorem B3991589 : Blo 1772087 3991589 := bbase (se 4 (by rfl) ⟨374211, by rfl⟩ : syracuseStep 3991589 = 748423) (by norm_num)
theorem B10094645 : Blo 1772087 10094645 := bbase (se 5 (by rfl) ⟨473186, by rfl⟩ : syracuseStep 10094645 = 946373) (by norm_num)
theorem B3991661 : Blo 1772087 3991661 := bbase (se 3 (by rfl) ⟨748436, by rfl⟩ : syracuseStep 3991661 = 1496873) (by norm_num)
theorem B2050165 : Blo 1772087 2050165 := bbase (se 5 (by rfl) ⟨96101, by rfl⟩ : syracuseStep 2050165 = 192203) (by norm_num)
theorem B2992261 : Blo 1772087 2992261 := bbase (se 4 (by rfl) ⟨280524, by rfl⟩ : syracuseStep 2992261 = 561049) (by norm_num)
theorem B4262053 : Blo 1772087 4262053 := bbase (se 4 (by rfl) ⟨399567, by rfl⟩ : syracuseStep 4262053 = 799135) (by norm_num)
theorem B5982389 : Blo 1772087 5982389 := bbase (se 5 (by rfl) ⟨280424, by rfl⟩ : syracuseStep 5982389 = 560849) (by norm_num)
theorem B7678165 : Blo 1772087 7678165 := bbase (se 7 (by rfl) ⟨89978, by rfl⟩ : syracuseStep 7678165 = 179957) (by norm_num)
theorem B2992349 : Blo 1772087 2992349 := bbase (se 3 (by rfl) ⟨561065, by rfl⟩ : syracuseStep 2992349 = 1122131) (by norm_num)
theorem B3787013 : Blo 1772087 3787013 := bbase (se 4 (by rfl) ⟨355032, by rfl⟩ : syracuseStep 3787013 = 710065) (by norm_num)
theorem B2992477 : Blo 1772087 2992477 := bbase (se 3 (by rfl) ⟨561089, by rfl⟩ : syracuseStep 2992477 = 1122179) (by norm_num)
theorem B1796465 : Blo 1772087 1796465 := bbase (se 2 (by rfl) ⟨673674, by rfl⟩ : syracuseStep 1796465 = 1347349) (by norm_num)
theorem B8972693 : Blo 1772087 8972693 := bbase (se 6 (by rfl) ⟨210297, by rfl⟩ : syracuseStep 8972693 = 420595) (by norm_num)
theorem B2992565 : Blo 1772087 2992565 := bbase (se 5 (by rfl) ⟨140276, by rfl⟩ : syracuseStep 2992565 = 280553) (by norm_num)
theorem B2992693 : Blo 1772087 2992693 := bbase (se 5 (by rfl) ⟨140282, by rfl⟩ : syracuseStep 2992693 = 280565) (by norm_num)
theorem B5982821 : Blo 1772087 5982821 := bbase (se 4 (by rfl) ⟨560889, by rfl⟩ : syracuseStep 5982821 = 1121779) (by norm_num)
theorem B2992781 : Blo 1772087 2992781 := bbase (se 3 (by rfl) ⟨561146, by rfl⟩ : syracuseStep 2992781 = 1122293) (by norm_num)
theorem B2525917 : Blo 1772087 2525917 := bbase (se 3 (by rfl) ⟨473609, by rfl⟩ : syracuseStep 2525917 = 947219) (by norm_num)
theorem B2992909 : Blo 1772087 2992909 := bbase (se 3 (by rfl) ⟨561170, by rfl⟩ : syracuseStep 2992909 = 1122341) (by norm_num)
theorem B2992997 : Blo 1772087 2992997 := bbase (se 4 (by rfl) ⟨280593, by rfl⟩ : syracuseStep 2992997 = 561187) (by norm_num)
theorem B4795253 : Blo 1772087 4795253 := bbase (se 5 (by rfl) ⟨224777, by rfl⟩ : syracuseStep 4795253 = 449555) (by norm_num)
theorem B1993621 : Blo 1772087 1993621 := bbase (se 6 (by rfl) ⟨46725, by rfl⟩ : syracuseStep 1993621 = 93451) (by norm_num)
theorem B1993657 : Blo 1772087 1993657 := bbase (se 2 (by rfl) ⟨747621, by rfl⟩ : syracuseStep 1993657 = 1495243) (by norm_num)
theorem B1797061 : Blo 1772087 1797061 := bbase (se 4 (by rfl) ⟨168474, by rfl⟩ : syracuseStep 1797061 = 336949) (by norm_num)
theorem B2878421 : Blo 1772087 2878421 := bbase (se 7 (by rfl) ⟨33731, by rfl⟩ : syracuseStep 2878421 = 67463) (by norm_num)
theorem B1993693 : Blo 1772087 1993693 := bbase (se 3 (by rfl) ⟨373817, by rfl⟩ : syracuseStep 1993693 = 747635) (by norm_num)
theorem B7187429 : Blo 1772087 7187429 := bbase (se 4 (by rfl) ⟨673821, by rfl⟩ : syracuseStep 7187429 = 1347643) (by norm_num)
theorem B5049317 : Blo 1772087 5049317 := bbase (se 4 (by rfl) ⟨473373, by rfl⟩ : syracuseStep 5049317 = 946747) (by norm_num)
theorem B2993125 : Blo 1772087 2993125 := bbase (se 4 (by rfl) ⟨280605, by rfl⟩ : syracuseStep 2993125 = 561211) (by norm_num)
theorem B1993729 : Blo 1772087 1993729 := bbase (se 2 (by rfl) ⟨747648, by rfl⟩ : syracuseStep 1993729 = 1495297) (by norm_num)
theorem B5983253 : Blo 1772087 5983253 := bbase (se 6 (by rfl) ⟨140232, by rfl⟩ : syracuseStep 5983253 = 280465) (by norm_num)
theorem B1993765 : Blo 1772087 1993765 := bbase (se 4 (by rfl) ⟨186915, by rfl⟩ : syracuseStep 1993765 = 373831) (by norm_num)
theorem B2993213 : Blo 1772087 2993213 := bbase (se 3 (by rfl) ⟨561227, by rfl⟩ : syracuseStep 2993213 = 1122455) (by norm_num)
theorem B1920061 : Blo 1772087 1920061 := bbase (se 3 (by rfl) ⟨360011, by rfl⟩ : syracuseStep 1920061 = 720023) (by norm_num)
theorem B1993801 : Blo 1772087 1993801 := bbase (se 2 (by rfl) ⟨747675, by rfl⟩ : syracuseStep 1993801 = 1495351) (by norm_num)
theorem B3787877 : Blo 1772087 3787877 := bbase (se 4 (by rfl) ⟨355113, by rfl⟩ : syracuseStep 3787877 = 710227) (by norm_num)
theorem B1993837 : Blo 1772087 1993837 := bbase (se 3 (by rfl) ⟨373844, by rfl⟩ : syracuseStep 1993837 = 747689) (by norm_num)
theorem B3034253 : Blo 1772087 3034253 := bbase (se 3 (by rfl) ⟨568922, by rfl⟩ : syracuseStep 3034253 = 1137845) (by norm_num)
theorem B1993873 : Blo 1772087 1993873 := bbase (se 2 (by rfl) ⟨747702, by rfl⟩ : syracuseStep 1993873 = 1495405) (by norm_num)
theorem B5680277 : Blo 1772087 5680277 := bbase (se 6 (by rfl) ⟨133131, by rfl⟩ : syracuseStep 5680277 = 266263) (by norm_num)
theorem B1993909 : Blo 1772087 1993909 := bbase (se 5 (by rfl) ⟨93464, by rfl⟩ : syracuseStep 1993909 = 186929) (by norm_num)
theorem B2993341 : Blo 1772087 2993341 := bbase (se 3 (by rfl) ⟨561251, by rfl⟩ : syracuseStep 2993341 = 1122503) (by norm_num)
theorem B1993945 : Blo 1772087 1993945 := bbase (se 2 (by rfl) ⟨747729, by rfl⟩ : syracuseStep 1993945 = 1495459) (by norm_num)
theorem B3788021 : Blo 1772087 3788021 := bbase (se 5 (by rfl) ⟨177563, by rfl⟩ : syracuseStep 3788021 = 355127) (by norm_num)
theorem B1993981 : Blo 1772087 1993981 := bbase (se 3 (by rfl) ⟨373871, by rfl⟩ : syracuseStep 1993981 = 747743) (by norm_num)
theorem B2993429 : Blo 1772087 2993429 := bbase (se 6 (by rfl) ⟨70158, by rfl⟩ : syracuseStep 2993429 = 140317) (by norm_num)
theorem B1994017 : Blo 1772087 1994017 := bbase (se 2 (by rfl) ⟨747756, by rfl⟩ : syracuseStep 1994017 = 1495513) (by norm_num)
theorem B1994053 : Blo 1772087 1994053 := bbase (se 4 (by rfl) ⟨186942, by rfl⟩ : syracuseStep 1994053 = 373885) (by norm_num)
theorem B12782933 : Blo 1772087 12782933 := bbase (se 11 (by rfl) ⟨9362, by rfl⟩ : syracuseStep 12782933 = 18725) (by norm_num)
theorem B1994089 : Blo 1772087 1994089 := bbase (se 2 (by rfl) ⟨747783, by rfl⟩ : syracuseStep 1994089 = 1495567) (by norm_num)
theorem B1822061 : Blo 1772087 1822061 := bbase (se 3 (by rfl) ⟨341636, by rfl⟩ : syracuseStep 1822061 = 683273) (by norm_num)
theorem B1994125 : Blo 1772087 1994125 := bbase (se 3 (by rfl) ⟨373898, by rfl⟩ : syracuseStep 1994125 = 747797) (by norm_num)
theorem B2993557 : Blo 1772087 2993557 := bbase (se 6 (by rfl) ⟨70161, by rfl⟩ : syracuseStep 2993557 = 140323) (by norm_num)
theorem B1994161 : Blo 1772087 1994161 := bbase (se 2 (by rfl) ⟨747810, by rfl⟩ : syracuseStep 1994161 = 1495621) (by norm_num)
theorem B2305477 : Blo 1772087 2305477 := bbase (se 4 (by rfl) ⟨216138, by rfl⟩ : syracuseStep 2305477 = 432277) (by norm_num)
theorem B5983685 : Blo 1772087 5983685 := bbase (se 4 (by rfl) ⟨560970, by rfl⟩ : syracuseStep 5983685 = 1121941) (by norm_num)
theorem B3034565 : Blo 1772087 3034565 := bbase (se 4 (by rfl) ⟨284490, by rfl⟩ : syracuseStep 3034565 = 568981) (by norm_num)
theorem B1994197 : Blo 1772087 1994197 := bbase (se 7 (by rfl) ⟨23369, by rfl⟩ : syracuseStep 1994197 = 46739) (by norm_num)
theorem B2993645 : Blo 1772087 2993645 := bbase (se 3 (by rfl) ⟨561308, by rfl⟩ : syracuseStep 2993645 = 1122617) (by norm_num)
theorem B1994233 : Blo 1772087 1994233 := bbase (se 2 (by rfl) ⟨747837, by rfl⟩ : syracuseStep 1994233 = 1495675) (by norm_num)
theorem B1994269 : Blo 1772087 1994269 := bbase (se 3 (by rfl) ⟨373925, by rfl⟩ : syracuseStep 1994269 = 747851) (by norm_num)
theorem B1994305 : Blo 1772087 1994305 := bbase (se 2 (by rfl) ⟨747864, by rfl⟩ : syracuseStep 1994305 = 1495729) (by norm_num)
theorem B1994341 : Blo 1772087 1994341 := bbase (se 4 (by rfl) ⟨186969, by rfl⟩ : syracuseStep 1994341 = 373939) (by norm_num)
theorem B2993773 : Blo 1772087 2993773 := bbase (se 3 (by rfl) ⟨561332, by rfl⟩ : syracuseStep 2993773 = 1122665) (by norm_num)
theorem B5049989 : Blo 1772087 5049989 := bbase (se 4 (by rfl) ⟨473436, by rfl⟩ : syracuseStep 5049989 = 946873) (by norm_num)
theorem B1994377 : Blo 1772087 1994377 := bbase (se 2 (by rfl) ⟨747891, by rfl⟩ : syracuseStep 1994377 = 1495783) (by norm_num)
theorem B8973989 : Blo 1772087 8973989 := bbase (se 4 (by rfl) ⟨841311, by rfl⟩ : syracuseStep 8973989 = 1682623) (by norm_num)
theorem B1994413 : Blo 1772087 1994413 := bbase (se 3 (by rfl) ⟨373952, by rfl⟩ : syracuseStep 1994413 = 747905) (by norm_num)
theorem B1994449 : Blo 1772087 1994449 := bbase (se 2 (by rfl) ⟨747918, by rfl⟩ : syracuseStep 1994449 = 1495837) (by norm_num)
theorem B1847009 : Blo 1772087 1847009 := bbase (se 2 (by rfl) ⟨692628, by rfl⟩ : syracuseStep 1847009 = 1385257) (by norm_num)
theorem B1994485 : Blo 1772087 1994485 := bbase (se 5 (by rfl) ⟨93491, by rfl⟩ : syracuseStep 1994485 = 186983) (by norm_num)
theorem B2559757 : Blo 1772087 2559757 := bbase (se 3 (by rfl) ⟨479954, by rfl⟩ : syracuseStep 2559757 = 959909) (by norm_num)
theorem B1994521 : Blo 1772087 1994521 := bbase (se 2 (by rfl) ⟨747945, by rfl⟩ : syracuseStep 1994521 = 1495891) (by norm_num)
theorem B1994557 : Blo 1772087 1994557 := bbase (se 3 (by rfl) ⟨373979, by rfl⟩ : syracuseStep 1994557 = 747959) (by norm_num)
theorem B1994593 : Blo 1772087 1994593 := bbase (se 2 (by rfl) ⟨747972, by rfl⟩ : syracuseStep 1994593 = 1495945) (by norm_num)
theorem B2658149 : Blo 1772087 2658149 := bbase (se 4 (by rfl) ⟨249201, by rfl⟩ : syracuseStep 2658149 = 498403) (by norm_num)
theorem B2396021 : Blo 1772087 2396021 := bbase (se 5 (by rfl) ⟨112313, by rfl⟩ : syracuseStep 2396021 = 224627) (by norm_num)
theorem B5984117 : Blo 1772087 5984117 := bbase (se 5 (by rfl) ⟨280505, by rfl⟩ : syracuseStep 5984117 = 561011) (by norm_num)
theorem B2658173 : Blo 1772087 2658173 := bbase (se 3 (by rfl) ⟨498407, by rfl⟩ : syracuseStep 2658173 = 996815) (by norm_num)
theorem B1994629 : Blo 1772087 1994629 := bbase (se 4 (by rfl) ⟨186996, by rfl⟩ : syracuseStep 1994629 = 373993) (by norm_num)
theorem B4042637 : Blo 1772087 4042637 := bbase (se 3 (by rfl) ⟨757994, by rfl⟩ : syracuseStep 4042637 = 1515989) (by norm_num)
theorem B2658197 : Blo 1772087 2658197 := bbase (se 6 (by rfl) ⟨62301, by rfl⟩ : syracuseStep 2658197 = 124603) (by norm_num)
theorem B2158489 : Blo 1772087 2158489 := bbase (se 2 (by rfl) ⟨809433, by rfl⟩ : syracuseStep 2158489 = 1618867) (by norm_num)
theorem B1994665 : Blo 1772087 1994665 := bbase (se 2 (by rfl) ⟨747999, by rfl⟩ : syracuseStep 1994665 = 1495999) (by norm_num)
theorem B2658221 : Blo 1772087 2658221 := bbase (se 3 (by rfl) ⟨498416, by rfl⟩ : syracuseStep 2658221 = 996833) (by norm_num)
theorem B2658245 : Blo 1772087 2658245 := bbase (se 4 (by rfl) ⟨249210, by rfl⟩ : syracuseStep 2658245 = 498421) (by norm_num)
theorem B7573445 : Blo 1772087 7573445 := bbase (se 4 (by rfl) ⟨710010, by rfl⟩ : syracuseStep 7573445 = 1420021) (by norm_num)
theorem B1994701 : Blo 1772087 1994701 := bbase (se 3 (by rfl) ⟨374006, by rfl⟩ : syracuseStep 1994701 = 748013) (by norm_num)
theorem B2658269 : Blo 1772087 2658269 := bbase (se 3 (by rfl) ⟨498425, by rfl⟩ : syracuseStep 2658269 = 996851) (by norm_num)
theorem B3788765 : Blo 1772087 3788765 := bbase (se 3 (by rfl) ⟨710393, by rfl⟩ : syracuseStep 3788765 = 1420787) (by norm_num)
theorem B1994737 : Blo 1772087 1994737 := bbase (se 2 (by rfl) ⟨748026, by rfl⟩ : syracuseStep 1994737 = 1496053) (by norm_num)
theorem B2658293 : Blo 1772087 2658293 := bbase (se 5 (by rfl) ⟨124607, by rfl⟩ : syracuseStep 2658293 = 249215) (by norm_num)
theorem B2658317 : Blo 1772087 2658317 := bbase (se 3 (by rfl) ⟨498434, by rfl⟩ : syracuseStep 2658317 = 996869) (by norm_num)
theorem B4550669 : Blo 1772087 4550669 := bbase (se 3 (by rfl) ⟨853250, by rfl⟩ : syracuseStep 4550669 = 1706501) (by norm_num)
theorem B6729749 : Blo 1772087 6729749 := bbase (se 6 (by rfl) ⟨157728, by rfl⟩ : syracuseStep 6729749 = 315457) (by norm_num)
theorem B1994773 : Blo 1772087 1994773 := bbase (se 6 (by rfl) ⟨46752, by rfl⟩ : syracuseStep 1994773 = 93505) (by norm_num)
theorem B2658341 : Blo 1772087 2658341 := bbase (se 4 (by rfl) ⟨249219, by rfl⟩ : syracuseStep 2658341 = 498439) (by norm_num)
theorem B5050421 : Blo 1772087 5050421 := bbase (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) (by norm_num)
theorem B1994809 : Blo 1772087 1994809 := bbase (se 2 (by rfl) ⟨748053, by rfl⟩ : syracuseStep 1994809 = 1496107) (by norm_num)
theorem B2658365 : Blo 1772087 2658365 := bbase (se 3 (by rfl) ⟨498443, by rfl⟩ : syracuseStep 2658365 = 996887) (by norm_num)
theorem B2658389 : Blo 1772087 2658389 := bbase (se 8 (by rfl) ⟨15576, by rfl⟩ : syracuseStep 2658389 = 31153) (by norm_num)
theorem B1994845 : Blo 1772087 1994845 := bbase (se 3 (by rfl) ⟨374033, by rfl⟩ : syracuseStep 1994845 = 748067) (by norm_num)
theorem B2658413 : Blo 1772087 2658413 := bbase (se 3 (by rfl) ⟨498452, by rfl⟩ : syracuseStep 2658413 = 996905) (by norm_num)
theorem B8523893 : Blo 1772087 8523893 := bbase (se 5 (by rfl) ⟨399557, by rfl⟩ : syracuseStep 8523893 = 799115) (by norm_num)
theorem B1994881 : Blo 1772087 1994881 := bbase (se 2 (by rfl) ⟨748080, by rfl⟩ : syracuseStep 1994881 = 1496161) (by norm_num)
theorem B2658437 : Blo 1772087 2658437 := bbase (se 4 (by rfl) ⟨249228, by rfl⟩ : syracuseStep 2658437 = 498457) (by norm_num)
theorem B2658461 : Blo 1772087 2658461 := bbase (se 3 (by rfl) ⟨498461, by rfl⟩ : syracuseStep 2658461 = 996923) (by norm_num)
theorem B1994917 : Blo 1772087 1994917 := bbase (se 4 (by rfl) ⟨187023, by rfl⟩ : syracuseStep 1994917 = 374047) (by norm_num)
theorem B2838709 : Blo 1772087 2838709 := bbase (se 5 (by rfl) ⟨133064, by rfl⟩ : syracuseStep 2838709 = 266129) (by norm_num)
theorem B2658485 : Blo 1772087 2658485 := bbase (se 5 (by rfl) ⟨124616, by rfl⟩ : syracuseStep 2658485 = 249233) (by norm_num)
theorem B1994953 : Blo 1772087 1994953 := bbase (se 2 (by rfl) ⟨748107, by rfl⟩ : syracuseStep 1994953 = 1496215) (by norm_num)
theorem B2658509 : Blo 1772087 2658509 := bbase (se 3 (by rfl) ⟨498470, by rfl⟩ : syracuseStep 2658509 = 996941) (by norm_num)
theorem B2658533 : Blo 1772087 2658533 := bbase (se 4 (by rfl) ⟨249237, by rfl⟩ : syracuseStep 2658533 = 498475) (by norm_num)
theorem B1994989 : Blo 1772087 1994989 := bbase (se 3 (by rfl) ⟨374060, by rfl⟩ : syracuseStep 1994989 = 748121) (by norm_num)
theorem B2658557 : Blo 1772087 2658557 := bbase (se 3 (by rfl) ⟨498479, by rfl⟩ : syracuseStep 2658557 = 996959) (by norm_num)
theorem B1995025 : Blo 1772087 1995025 := bbase (se 2 (by rfl) ⟨748134, by rfl⟩ : syracuseStep 1995025 = 1496269) (by norm_num)
theorem B2658581 : Blo 1772087 2658581 := bbase (se 6 (by rfl) ⟨62310, by rfl⟩ : syracuseStep 2658581 = 124621) (by norm_num)
theorem B5984549 : Blo 1772087 5984549 := bbase (se 4 (by rfl) ⟨561051, by rfl⟩ : syracuseStep 5984549 = 1122103) (by norm_num)
theorem B2658605 : Blo 1772087 2658605 := bbase (se 3 (by rfl) ⟨498488, by rfl⟩ : syracuseStep 2658605 = 996977) (by norm_num)
theorem B6730037 : Blo 1772087 6730037 := bbase (se 5 (by rfl) ⟨315470, by rfl⟩ : syracuseStep 6730037 = 630941) (by norm_num)
theorem B1995061 : Blo 1772087 1995061 := bbase (se 5 (by rfl) ⟨93518, by rfl⟩ : syracuseStep 1995061 = 187037) (by norm_num)
theorem B2658629 : Blo 1772087 2658629 := bbase (se 4 (by rfl) ⟨249246, by rfl⟩ : syracuseStep 2658629 = 498493) (by norm_num)
theorem B5394757 : Blo 1772087 5394757 := bbase (se 4 (by rfl) ⟨505758, by rfl⟩ : syracuseStep 5394757 = 1011517) (by norm_num)
theorem B1995097 : Blo 1772087 1995097 := bbase (se 2 (by rfl) ⟨748161, by rfl⟩ : syracuseStep 1995097 = 1496323) (by norm_num)
theorem B2658653 : Blo 1772087 2658653 := bbase (se 3 (by rfl) ⟨498497, by rfl⟩ : syracuseStep 2658653 = 996995) (by norm_num)
theorem B4551005 : Blo 1772087 4551005 := bbase (se 3 (by rfl) ⟨853313, by rfl⟩ : syracuseStep 4551005 = 1706627) (by norm_num)
theorem B2658677 : Blo 1772087 2658677 := bbase (se 5 (by rfl) ⟨124625, by rfl⟩ : syracuseStep 2658677 = 249251) (by norm_num)
theorem B5394805 : Blo 1772087 5394805 := bbase (se 5 (by rfl) ⟨252881, by rfl⟩ : syracuseStep 5394805 = 505763) (by norm_num)
theorem B1995133 : Blo 1772087 1995133 := bbase (se 3 (by rfl) ⟨374087, by rfl⟩ : syracuseStep 1995133 = 748175) (by norm_num)
theorem B8515973 : Blo 1772087 8515973 := bbase (se 4 (by rfl) ⟨798372, by rfl⟩ : syracuseStep 8515973 = 1596745) (by norm_num)
theorem B2658701 : Blo 1772087 2658701 := bbase (se 3 (by rfl) ⟨498506, by rfl⟩ : syracuseStep 2658701 = 997013) (by norm_num)
theorem B2396557 : Blo 1772087 2396557 := bbase (se 3 (by rfl) ⟨449354, by rfl⟩ : syracuseStep 2396557 = 898709) (by norm_num)
theorem B34550165 : Blo 1772087 34550165 := bbase (se 6 (by rfl) ⟨809769, by rfl⟩ : syracuseStep 34550165 = 1619539) (by norm_num)
theorem B1995169 : Blo 1772087 1995169 := bbase (se 2 (by rfl) ⟨748188, by rfl⟩ : syracuseStep 1995169 = 1496377) (by norm_num)
theorem B2658725 : Blo 1772087 2658725 := bbase (se 4 (by rfl) ⟨249255, by rfl⟩ : syracuseStep 2658725 = 498511) (by norm_num)
theorem B5394853 : Blo 1772087 5394853 := bbase (se 4 (by rfl) ⟨505767, by rfl⟩ : syracuseStep 5394853 = 1011535) (by norm_num)
theorem B14373301 : Blo 1772087 14373301 := bbase (se 5 (by rfl) ⟨673748, by rfl⟩ : syracuseStep 14373301 = 1347497) (by norm_num)
theorem B2658749 : Blo 1772087 2658749 := bbase (se 3 (by rfl) ⟨498515, by rfl⟩ : syracuseStep 2658749 = 997031) (by norm_num)
theorem B1995205 : Blo 1772087 1995205 := bbase (se 4 (by rfl) ⟨187050, by rfl⟩ : syracuseStep 1995205 = 374101) (by norm_num)
theorem B2658773 : Blo 1772087 2658773 := bbase (se 7 (by rfl) ⟨31157, by rfl⟩ : syracuseStep 2658773 = 62315) (by norm_num)
theorem B5681621 : Blo 1772087 5681621 := bbase (se 7 (by rfl) ⟨66581, by rfl⟩ : syracuseStep 5681621 = 133163) (by norm_num)
theorem B3412453 : Blo 1772087 3412453 := bbase (se 4 (by rfl) ⟨319917, by rfl⟩ : syracuseStep 3412453 = 639835) (by norm_num)
theorem B1995241 : Blo 1772087 1995241 := bbase (se 2 (by rfl) ⟨748215, by rfl⟩ : syracuseStep 1995241 = 1496431) (by norm_num)
theorem B2658797 : Blo 1772087 2658797 := bbase (se 3 (by rfl) ⟨498524, by rfl⟩ : syracuseStep 2658797 = 997049) (by norm_num)
theorem B2273789 : Blo 1772087 2273789 := bbase (se 3 (by rfl) ⟨426335, by rfl⟩ : syracuseStep 2273789 = 852671) (by norm_num)
theorem B2658821 : Blo 1772087 2658821 := bbase (se 4 (by rfl) ⟨249264, by rfl⟩ : syracuseStep 2658821 = 498529) (by norm_num)
theorem B1995277 : Blo 1772087 1995277 := bbase (se 3 (by rfl) ⟨374114, by rfl⟩ : syracuseStep 1995277 = 748229) (by norm_num)
theorem B25571861 : Blo 1772087 25571861 := bbase (se 6 (by rfl) ⟨599340, by rfl⟩ : syracuseStep 25571861 = 1198681) (by norm_num)
theorem B2658845 : Blo 1772087 2658845 := bbase (se 3 (by rfl) ⟨498533, by rfl⟩ : syracuseStep 2658845 = 997067) (by norm_num)
theorem B1995313 : Blo 1772087 1995313 := bbase (se 2 (by rfl) ⟨748242, by rfl⟩ : syracuseStep 1995313 = 1496485) (by norm_num)
theorem B2658869 : Blo 1772087 2658869 := bbase (se 5 (by rfl) ⟨124634, by rfl⟩ : syracuseStep 2658869 = 249269) (by norm_num)
theorem B4043333 : Blo 1772087 4043333 := bbase (se 4 (by rfl) ⟨379062, by rfl⟩ : syracuseStep 4043333 = 758125) (by norm_num)
theorem B2658893 : Blo 1772087 2658893 := bbase (se 3 (by rfl) ⟨498542, by rfl⟩ : syracuseStep 2658893 = 997085) (by norm_num)
theorem B1995349 : Blo 1772087 1995349 := bbase (se 8 (by rfl) ⟨11691, by rfl⟩ : syracuseStep 1995349 = 23383) (by norm_num)
theorem B2839133 : Blo 1772087 2839133 := bbase (se 3 (by rfl) ⟨532337, by rfl⟩ : syracuseStep 2839133 = 1064675) (by norm_num)
theorem B2658917 : Blo 1772087 2658917 := bbase (se 4 (by rfl) ⟨249273, by rfl⟩ : syracuseStep 2658917 = 498547) (by norm_num)
theorem B1995385 : Blo 1772087 1995385 := bbase (se 2 (by rfl) ⟨748269, by rfl⟩ : syracuseStep 1995385 = 1496539) (by norm_num)
theorem B2658941 : Blo 1772087 2658941 := bbase (se 3 (by rfl) ⟨498551, by rfl⟩ : syracuseStep 2658941 = 997103) (by norm_num)
theorem B2658965 : Blo 1772087 2658965 := bbase (se 6 (by rfl) ⟨62319, by rfl⟩ : syracuseStep 2658965 = 124639) (by norm_num)
theorem B1995421 : Blo 1772087 1995421 := bbase (se 3 (by rfl) ⟨374141, by rfl⟩ : syracuseStep 1995421 = 748283) (by norm_num)
theorem B2658989 : Blo 1772087 2658989 := bbase (se 3 (by rfl) ⟨498560, by rfl⟩ : syracuseStep 2658989 = 997121) (by norm_num)
theorem B1995457 : Blo 1772087 1995457 := bbase (se 2 (by rfl) ⟨748296, by rfl⟩ : syracuseStep 1995457 = 1496593) (by norm_num)
theorem B2659013 : Blo 1772087 2659013 := bbase (se 4 (by rfl) ⟨249282, by rfl⟩ : syracuseStep 2659013 = 498565) (by norm_num)
theorem B5984981 : Blo 1772087 5984981 := bbase (se 7 (by rfl) ⟨70136, by rfl⟩ : syracuseStep 5984981 = 140273) (by norm_num)
theorem B2659037 : Blo 1772087 2659037 := bbase (se 3 (by rfl) ⟨498569, by rfl⟩ : syracuseStep 2659037 = 997139) (by norm_num)
theorem B1995493 : Blo 1772087 1995493 := bbase (se 4 (by rfl) ⟨187077, by rfl⟩ : syracuseStep 1995493 = 374155) (by norm_num)
theorem B2659061 : Blo 1772087 2659061 := bbase (se 5 (by rfl) ⟨124643, by rfl⟩ : syracuseStep 2659061 = 249287) (by norm_num)
theorem B1995529 : Blo 1772087 1995529 := bbase (se 2 (by rfl) ⟨748323, by rfl⟩ : syracuseStep 1995529 = 1496647) (by norm_num)
theorem B4485901 : Blo 1772087 4485901 := bbase (se 3 (by rfl) ⟨841106, by rfl⟩ : syracuseStep 4485901 = 1682213) (by norm_num)
theorem B2659085 : Blo 1772087 2659085 := bbase (se 3 (by rfl) ⟨498578, by rfl⟩ : syracuseStep 2659085 = 997157) (by norm_num)
theorem B3838733 : Blo 1772087 3838733 := bbase (se 3 (by rfl) ⟨719762, by rfl⟩ : syracuseStep 3838733 = 1439525) (by norm_num)
theorem B2659109 : Blo 1772087 2659109 := bbase (se 4 (by rfl) ⟨249291, by rfl⟩ : syracuseStep 2659109 = 498583) (by norm_num)
theorem B5051173 : Blo 1772087 5051173 := bbase (se 4 (by rfl) ⟨473547, by rfl⟩ : syracuseStep 5051173 = 947095) (by norm_num)
theorem B1995565 : Blo 1772087 1995565 := bbase (se 3 (by rfl) ⟨374168, by rfl⟩ : syracuseStep 1995565 = 748337) (by norm_num)
theorem B2077489 : Blo 1772087 2077489 := bbase (se 2 (by rfl) ⟨779058, by rfl⟩ : syracuseStep 2077489 = 1558117) (by norm_num)
theorem B2659133 : Blo 1772087 2659133 := bbase (se 3 (by rfl) ⟨498587, by rfl⟩ : syracuseStep 2659133 = 997175) (by norm_num)
theorem B1995601 : Blo 1772087 1995601 := bbase (se 2 (by rfl) ⟨748350, by rfl⟩ : syracuseStep 1995601 = 1496701) (by norm_num)
theorem B2659157 : Blo 1772087 2659157 := bbase (se 9 (by rfl) ⟨7790, by rfl⟩ : syracuseStep 2659157 = 15581) (by norm_num)
theorem B20206421 : Blo 1772087 20206421 := bbase (se 9 (by rfl) ⟨59198, by rfl⟩ : syracuseStep 20206421 = 118397) (by norm_num)
theorem B2659181 : Blo 1772087 2659181 := bbase (se 3 (by rfl) ⟨498596, by rfl⟩ : syracuseStep 2659181 = 997193) (by norm_num)
theorem B1995637 : Blo 1772087 1995637 := bbase (se 5 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 1995637 = 187091) (by norm_num)
theorem B4486013 : Blo 1772087 4486013 := bbase (se 3 (by rfl) ⟨841127, by rfl⟩ : syracuseStep 4486013 = 1682255) (by norm_num)
theorem B2839421 : Blo 1772087 2839421 := bbase (se 3 (by rfl) ⟨532391, by rfl⟩ : syracuseStep 2839421 = 1064783) (by norm_num)
theorem B2659205 : Blo 1772087 2659205 := bbase (se 4 (by rfl) ⟨249300, by rfl⟩ : syracuseStep 2659205 = 498601) (by norm_num)
theorem B1995673 : Blo 1772087 1995673 := bbase (se 2 (by rfl) ⟨748377, by rfl⟩ : syracuseStep 1995673 = 1496755) (by norm_num)
theorem B2659229 : Blo 1772087 2659229 := bbase (se 3 (by rfl) ⟨498605, by rfl⟩ : syracuseStep 2659229 = 997211) (by norm_num)
theorem B2659253 : Blo 1772087 2659253 := bbase (se 5 (by rfl) ⟨124652, by rfl⟩ : syracuseStep 2659253 = 249305) (by norm_num)
theorem B8975285 : Blo 1772087 8975285 := bbase (se 5 (by rfl) ⟨420716, by rfl⟩ : syracuseStep 8975285 = 841433) (by norm_num)
theorem B1995709 : Blo 1772087 1995709 := bbase (se 3 (by rfl) ⟨374195, by rfl⟩ : syracuseStep 1995709 = 748391) (by norm_num)
theorem B2659277 : Blo 1772087 2659277 := bbase (se 3 (by rfl) ⟨498614, by rfl⟩ : syracuseStep 2659277 = 997229) (by norm_num)
theorem B1995745 : Blo 1772087 1995745 := bbase (se 2 (by rfl) ⟨748404, by rfl⟩ : syracuseStep 1995745 = 1496809) (by norm_num)
theorem B2659301 : Blo 1772087 2659301 := bbase (se 4 (by rfl) ⟨249309, by rfl⟩ : syracuseStep 2659301 = 498619) (by norm_num)
theorem B2659325 : Blo 1772087 2659325 := bbase (se 3 (by rfl) ⟨498623, by rfl⟩ : syracuseStep 2659325 = 997247) (by norm_num)
theorem B1995781 : Blo 1772087 1995781 := bbase (se 4 (by rfl) ⟨187104, by rfl⟩ : syracuseStep 1995781 = 374209) (by norm_num)
theorem B2274313 : Blo 1772087 2274313 := bbase (se 2 (by rfl) ⟨852867, by rfl⟩ : syracuseStep 2274313 = 1705735) (by norm_num)
theorem B2659349 : Blo 1772087 2659349 := bbase (se 6 (by rfl) ⟨62328, by rfl⟩ : syracuseStep 2659349 = 124657) (by norm_num)
theorem B1995817 : Blo 1772087 1995817 := bbase (se 2 (by rfl) ⟨748431, by rfl⟩ : syracuseStep 1995817 = 1496863) (by norm_num)
theorem B2659373 : Blo 1772087 2659373 := bbase (se 3 (by rfl) ⟨498632, by rfl⟩ : syracuseStep 2659373 = 997265) (by norm_num)
theorem B13464629 : Blo 1772087 13464629 := bbase (se 5 (by rfl) ⟨631154, by rfl⟩ : syracuseStep 13464629 = 1262309) (by norm_num)
theorem B4486205 : Blo 1772087 4486205 := bbase (se 3 (by rfl) ⟨841163, by rfl⟩ : syracuseStep 4486205 = 1682327) (by norm_num)
theorem B2659397 : Blo 1772087 2659397 := bbase (se 4 (by rfl) ⟨249318, by rfl⟩ : syracuseStep 2659397 = 498637) (by norm_num)
theorem B2839645 : Blo 1772087 2839645 := bbase (se 3 (by rfl) ⟨532433, by rfl⟩ : syracuseStep 2839645 = 1064867) (by norm_num)
theorem B2659421 : Blo 1772087 2659421 := bbase (se 3 (by rfl) ⟨498641, by rfl⟩ : syracuseStep 2659421 = 997283) (by norm_num)
theorem B2659445 : Blo 1772087 2659445 := bbase (se 5 (by rfl) ⟨124661, by rfl⟩ : syracuseStep 2659445 = 249323) (by norm_num)
theorem B5985413 : Blo 1772087 5985413 := bbase (se 4 (by rfl) ⟨561132, by rfl⟩ : syracuseStep 5985413 = 1122265) (by norm_num)
theorem B2659469 : Blo 1772087 2659469 := bbase (se 3 (by rfl) ⟨498650, by rfl⟩ : syracuseStep 2659469 = 997301) (by norm_num)
theorem B2659493 : Blo 1772087 2659493 := bbase (se 4 (by rfl) ⟨249327, by rfl⟩ : syracuseStep 2659493 = 498655) (by norm_num)
theorem B2659517 : Blo 1772087 2659517 := bbase (se 3 (by rfl) ⟨498659, by rfl⟩ : syracuseStep 2659517 = 997319) (by norm_num)
theorem B2659541 : Blo 1772087 2659541 := bbase (se 7 (by rfl) ⟨31166, by rfl⟩ : syracuseStep 2659541 = 62333) (by norm_num)
theorem B2659565 : Blo 1772087 2659565 := bbase (se 3 (by rfl) ⟨498668, by rfl⟩ : syracuseStep 2659565 = 997337) (by norm_num)
theorem B2659589 : Blo 1772087 2659589 := bbase (se 4 (by rfl) ⟨249336, by rfl⟩ : syracuseStep 2659589 = 498673) (by norm_num)
theorem B2659613 : Blo 1772087 2659613 := bbase (se 3 (by rfl) ⟨498677, by rfl⟩ : syracuseStep 2659613 = 997355) (by norm_num)
theorem B2659637 : Blo 1772087 2659637 := bbase (se 5 (by rfl) ⟨124670, by rfl⟩ : syracuseStep 2659637 = 249341) (by norm_num)
theorem B2659661 : Blo 1772087 2659661 := bbase (se 3 (by rfl) ⟨498686, by rfl⟩ : syracuseStep 2659661 = 997373) (by norm_num)
theorem B2659685 : Blo 1772087 2659685 := bbase (se 4 (by rfl) ⟨249345, by rfl⟩ : syracuseStep 2659685 = 498691) (by norm_num)
theorem B2659709 : Blo 1772087 2659709 := bbase (se 3 (by rfl) ⟨498695, by rfl⟩ : syracuseStep 2659709 = 997391) (by norm_num)
theorem B3364229 : Blo 1772087 3364229 := bbase (se 4 (by rfl) ⟨315396, by rfl⟩ : syracuseStep 3364229 = 630793) (by norm_num)
theorem B4486549 : Blo 1772087 4486549 := bbase (se 6 (by rfl) ⟨105153, by rfl⟩ : syracuseStep 4486549 = 210307) (by norm_num)
theorem B2659733 : Blo 1772087 2659733 := bbase (se 6 (by rfl) ⟨62337, by rfl⟩ : syracuseStep 2659733 = 124675) (by norm_num)
theorem B2659757 : Blo 1772087 2659757 := bbase (se 3 (by rfl) ⟨498704, by rfl⟩ : syracuseStep 2659757 = 997409) (by norm_num)
theorem B2659781 : Blo 1772087 2659781 := bbase (se 4 (by rfl) ⟨249354, by rfl⟩ : syracuseStep 2659781 = 498709) (by norm_num)
theorem B13456853 : Blo 1772087 13456853 := bbase (se 7 (by rfl) ⟨157697, by rfl⟩ : syracuseStep 13456853 = 315395) (by norm_num)
theorem B6731221 : Blo 1772087 6731221 := bbase (se 7 (by rfl) ⟨78881, by rfl⟩ : syracuseStep 6731221 = 157763) (by norm_num)
theorem B2659805 : Blo 1772087 2659805 := bbase (se 3 (by rfl) ⟨498713, by rfl⟩ : syracuseStep 2659805 = 997427) (by norm_num)
theorem B2659829 : Blo 1772087 2659829 := bbase (se 5 (by rfl) ⟨124679, by rfl⟩ : syracuseStep 2659829 = 249359) (by norm_num)
theorem B15152629 : Blo 1772087 15152629 := bbase (se 5 (by rfl) ⟨710279, by rfl⟩ : syracuseStep 15152629 = 1420559) (by norm_num)
theorem B4486661 : Blo 1772087 4486661 := bbase (se 4 (by rfl) ⟨420624, by rfl⟩ : syracuseStep 4486661 = 841249) (by norm_num)
theorem B2659853 : Blo 1772087 2659853 := bbase (se 3 (by rfl) ⟨498722, by rfl⟩ : syracuseStep 2659853 = 997445) (by norm_num)
theorem B2160145 : Blo 1772087 2160145 := bbase (se 2 (by rfl) ⟨810054, by rfl⟩ : syracuseStep 2160145 = 1620109) (by norm_num)
theorem B2659877 : Blo 1772087 2659877 := bbase (se 4 (by rfl) ⟨249363, by rfl⟩ : syracuseStep 2659877 = 498727) (by norm_num)
theorem B5985845 : Blo 1772087 5985845 := bbase (se 5 (by rfl) ⟨280586, by rfl⟩ : syracuseStep 5985845 = 561173) (by norm_num)
theorem B2659901 : Blo 1772087 2659901 := bbase (se 3 (by rfl) ⟨498731, by rfl⟩ : syracuseStep 2659901 = 997463) (by norm_num)
theorem B2659925 : Blo 1772087 2659925 := bbase (se 8 (by rfl) ⟨15585, by rfl⟩ : syracuseStep 2659925 = 31171) (by norm_num)
theorem B2659949 : Blo 1772087 2659949 := bbase (se 3 (by rfl) ⟨498740, by rfl⟩ : syracuseStep 2659949 = 997481) (by norm_num)
theorem B3593845 : Blo 1772087 3593845 := bbase (se 5 (by rfl) ⟨168461, by rfl⟩ : syracuseStep 3593845 = 336923) (by norm_num)
theorem B2659973 : Blo 1772087 2659973 := bbase (se 4 (by rfl) ⟨249372, by rfl⟩ : syracuseStep 2659973 = 498745) (by norm_num)
theorem B2659997 : Blo 1772087 2659997 := bbase (se 3 (by rfl) ⟨498749, by rfl⟩ : syracuseStep 2659997 = 997499) (by norm_num)
theorem B3364517 : Blo 1772087 3364517 := bbase (se 4 (by rfl) ⟨315423, by rfl⟩ : syracuseStep 3364517 = 630847) (by norm_num)
theorem B2660021 : Blo 1772087 2660021 := bbase (se 5 (by rfl) ⟨124688, by rfl⟩ : syracuseStep 2660021 = 249377) (by norm_num)
theorem B7575221 : Blo 1772087 7575221 := bbase (se 5 (by rfl) ⟨355088, by rfl⟩ : syracuseStep 7575221 = 710177) (by norm_num)
theorem B4486853 : Blo 1772087 4486853 := bbase (se 4 (by rfl) ⟨420642, by rfl⟩ : syracuseStep 4486853 = 841285) (by norm_num)
theorem B2660045 : Blo 1772087 2660045 := bbase (se 3 (by rfl) ⟨498758, by rfl⟩ : syracuseStep 2660045 = 997517) (by norm_num)
theorem B2660069 : Blo 1772087 2660069 := bbase (se 4 (by rfl) ⟨249381, by rfl⟩ : syracuseStep 2660069 = 498763) (by norm_num)
theorem B3987197 : Blo 1772087 3987197 := bbase (se 3 (by rfl) ⟨747599, by rfl⟩ : syracuseStep 3987197 = 1495199) (by norm_num)
theorem B2660093 : Blo 1772087 2660093 := bbase (se 3 (by rfl) ⟨498767, by rfl⟩ : syracuseStep 2660093 = 997535) (by norm_num)
theorem B6731525 : Blo 1772087 6731525 := bbase (se 4 (by rfl) ⟨631080, by rfl⟩ : syracuseStep 6731525 = 1262161) (by norm_num)
theorem B2660117 : Blo 1772087 2660117 := bbase (se 6 (by rfl) ⟨62346, by rfl⟩ : syracuseStep 2660117 = 124693) (by norm_num)
theorem B2660141 : Blo 1772087 2660141 := bbase (se 3 (by rfl) ⟨498776, by rfl⟩ : syracuseStep 2660141 = 997553) (by norm_num)
theorem B3364669 : Blo 1772087 3364669 := bbase (se 3 (by rfl) ⟨630875, by rfl⟩ : syracuseStep 3364669 = 1261751) (by norm_num)
theorem B3987269 : Blo 1772087 3987269 := bbase (se 4 (by rfl) ⟨373806, by rfl⟩ : syracuseStep 3987269 = 747613) (by norm_num)
theorem B2660165 : Blo 1772087 2660165 := bbase (se 4 (by rfl) ⟨249390, by rfl⟩ : syracuseStep 2660165 = 498781) (by norm_num)
theorem B2660189 : Blo 1772087 2660189 := bbase (se 3 (by rfl) ⟨498785, by rfl⟩ : syracuseStep 2660189 = 997571) (by norm_num)
theorem B2660213 : Blo 1772087 2660213 := bbase (se 5 (by rfl) ⟨124697, by rfl⟩ : syracuseStep 2660213 = 249395) (by norm_num)
theorem B3987341 : Blo 1772087 3987341 := bbase (se 3 (by rfl) ⟨747626, by rfl⟩ : syracuseStep 3987341 = 1495253) (by norm_num)
theorem B2660237 : Blo 1772087 2660237 := bbase (se 3 (by rfl) ⟨498794, by rfl⟩ : syracuseStep 2660237 = 997589) (by norm_num)
theorem B2660261 : Blo 1772087 2660261 := bbase (se 4 (by rfl) ⟨249399, by rfl⟩ : syracuseStep 2660261 = 498799) (by norm_num)
theorem B2660285 : Blo 1772087 2660285 := bbase (se 3 (by rfl) ⟨498803, by rfl⟩ : syracuseStep 2660285 = 997607) (by norm_num)
theorem B3987413 : Blo 1772087 3987413 := bbase (se 7 (by rfl) ⟨46727, by rfl⟩ : syracuseStep 3987413 = 93455) (by norm_num)
theorem B2660309 : Blo 1772087 2660309 := bbase (se 7 (by rfl) ⟨31175, by rfl⟩ : syracuseStep 2660309 = 62351) (by norm_num)
theorem B5986277 : Blo 1772087 5986277 := bbase (se 4 (by rfl) ⟨561213, by rfl⟩ : syracuseStep 5986277 = 1122427) (by norm_num)
theorem B2660333 : Blo 1772087 2660333 := bbase (se 3 (by rfl) ⟨498812, by rfl⟩ : syracuseStep 2660333 = 997625) (by norm_num)
theorem B2660357 : Blo 1772087 2660357 := bbase (se 4 (by rfl) ⟨249408, by rfl⟩ : syracuseStep 2660357 = 498817) (by norm_num)
theorem B3987485 : Blo 1772087 3987485 := bbase (se 3 (by rfl) ⟨747653, by rfl⟩ : syracuseStep 3987485 = 1495307) (by norm_num)
theorem B4487197 : Blo 1772087 4487197 := bbase (se 3 (by rfl) ⟨841349, by rfl⟩ : syracuseStep 4487197 = 1682699) (by norm_num)
theorem B2660381 : Blo 1772087 2660381 := bbase (se 3 (by rfl) ⟨498821, by rfl⟩ : syracuseStep 2660381 = 997643) (by norm_num)
theorem B2660405 : Blo 1772087 2660405 := bbase (se 5 (by rfl) ⟨124706, by rfl⟩ : syracuseStep 2660405 = 249413) (by norm_num)
theorem B2660429 : Blo 1772087 2660429 := bbase (se 3 (by rfl) ⟨498830, by rfl⟩ : syracuseStep 2660429 = 997661) (by norm_num)
theorem B3987557 : Blo 1772087 3987557 := bbase (se 4 (by rfl) ⟨373833, by rfl⟩ : syracuseStep 3987557 = 747667) (by norm_num)
theorem B2660453 : Blo 1772087 2660453 := bbase (se 4 (by rfl) ⟨249417, by rfl⟩ : syracuseStep 2660453 = 498835) (by norm_num)
theorem B3364973 : Blo 1772087 3364973 := bbase (se 3 (by rfl) ⟨630932, by rfl⟩ : syracuseStep 3364973 = 1261865) (by norm_num)
theorem B2021501 : Blo 1772087 2021501 := bbase (se 3 (by rfl) ⟨379031, by rfl⟩ : syracuseStep 2021501 = 758063) (by norm_num)
theorem B2660477 : Blo 1772087 2660477 := bbase (se 3 (by rfl) ⟨498839, by rfl⟩ : syracuseStep 2660477 = 997679) (by norm_num)
theorem B4487309 : Blo 1772087 4487309 := bbase (se 3 (by rfl) ⟨841370, by rfl⟩ : syracuseStep 4487309 = 1682741) (by norm_num)
theorem B2660501 : Blo 1772087 2660501 := bbase (se 6 (by rfl) ⟨62355, by rfl⟩ : syracuseStep 2660501 = 124711) (by norm_num)
theorem B4257949 : Blo 1772087 4257949 := bbase (se 3 (by rfl) ⟨798365, by rfl⟩ : syracuseStep 4257949 = 1596731) (by norm_num)
theorem B3987629 : Blo 1772087 3987629 := bbase (se 3 (by rfl) ⟨747680, by rfl⟩ : syracuseStep 3987629 = 1495361) (by norm_num)
theorem B2660525 : Blo 1772087 2660525 := bbase (se 3 (by rfl) ⟨498848, by rfl⟩ : syracuseStep 2660525 = 997697) (by norm_num)
theorem B8976581 : Blo 1772087 8976581 := bbase (se 4 (by rfl) ⟨841554, by rfl⟩ : syracuseStep 8976581 = 1683109) (by norm_num)
theorem B2840773 : Blo 1772087 2840773 := bbase (se 4 (by rfl) ⟨266322, by rfl⟩ : syracuseStep 2840773 = 532645) (by norm_num)
theorem B2660549 : Blo 1772087 2660549 := bbase (se 4 (by rfl) ⟨249426, by rfl⟩ : syracuseStep 2660549 = 498853) (by norm_num)
theorem B8091845 : Blo 1772087 8091845 := bbase (se 4 (by rfl) ⟨758610, by rfl⟩ : syracuseStep 8091845 = 1517221) (by norm_num)
theorem B4856021 : Blo 1772087 4856021 := bbase (se 7 (by rfl) ⟨56906, by rfl⟩ : syracuseStep 4856021 = 113813) (by norm_num)
theorem B2021593 : Blo 1772087 2021593 := bbase (se 2 (by rfl) ⟨758097, by rfl⟩ : syracuseStep 2021593 = 1516195) (by norm_num)
theorem B3594461 : Blo 1772087 3594461 := bbase (se 3 (by rfl) ⟨673961, by rfl⟩ : syracuseStep 3594461 = 1347923) (by norm_num)
theorem B2660573 : Blo 1772087 2660573 := bbase (se 3 (by rfl) ⟨498857, by rfl⟩ : syracuseStep 2660573 = 997715) (by norm_num)
theorem B2275565 : Blo 1772087 2275565 := bbase (se 3 (by rfl) ⟨426668, by rfl⟩ : syracuseStep 2275565 = 853337) (by norm_num)
theorem B3987701 : Blo 1772087 3987701 := bbase (se 5 (by rfl) ⟨186923, by rfl⟩ : syracuseStep 3987701 = 373847) (by norm_num)
theorem B2660597 : Blo 1772087 2660597 := bbase (se 5 (by rfl) ⟨124715, by rfl⟩ : syracuseStep 2660597 = 249431) (by norm_num)
theorem B3594493 : Blo 1772087 3594493 := bbase (se 3 (by rfl) ⟨673967, by rfl⟩ : syracuseStep 3594493 = 1347935) (by norm_num)
theorem B2242829 : Blo 1772087 2242829 := bbase (se 3 (by rfl) ⟨420530, by rfl⟩ : syracuseStep 2242829 = 841061) (by norm_num)
theorem B2660621 : Blo 1772087 2660621 := bbase (se 3 (by rfl) ⟨498866, by rfl⟩ : syracuseStep 2660621 = 997733) (by norm_num)
theorem B4045085 : Blo 1772087 4045085 := bbase (se 3 (by rfl) ⟨758453, by rfl⟩ : syracuseStep 4045085 = 1516907) (by norm_num)
theorem B2660645 : Blo 1772087 2660645 := bbase (se 4 (by rfl) ⟨249435, by rfl⟩ : syracuseStep 2660645 = 498871) (by norm_num)
theorem B3987773 : Blo 1772087 3987773 := bbase (se 3 (by rfl) ⟨747707, by rfl⟩ : syracuseStep 3987773 = 1495415) (by norm_num)
theorem B2660669 : Blo 1772087 2660669 := bbase (se 3 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 2660669 = 997751) (by norm_num)
theorem B2242885 : Blo 1772087 2242885 := bbase (se 4 (by rfl) ⟨210270, by rfl⟩ : syracuseStep 2242885 = 420541) (by norm_num)
theorem B4487501 : Blo 1772087 4487501 := bbase (se 3 (by rfl) ⟨841406, by rfl⟩ : syracuseStep 4487501 = 1682813) (by norm_num)
theorem B8517973 : Blo 1772087 8517973 := bbase (se 10 (by rfl) ⟨12477, by rfl⟩ : syracuseStep 8517973 = 24955) (by norm_num)
theorem B2660693 : Blo 1772087 2660693 := bbase (se 10 (by rfl) ⟨3897, by rfl⟩ : syracuseStep 2660693 = 7795) (by norm_num)
theorem B2660717 : Blo 1772087 2660717 := bbase (se 3 (by rfl) ⟨498884, by rfl⟩ : syracuseStep 2660717 = 997769) (by norm_num)
theorem B3987845 : Blo 1772087 3987845 := bbase (se 4 (by rfl) ⟨373860, by rfl⟩ : syracuseStep 3987845 = 747721) (by norm_num)
theorem B2660741 : Blo 1772087 2660741 := bbase (se 4 (by rfl) ⟨249444, by rfl⟩ : syracuseStep 2660741 = 498889) (by norm_num)
theorem B5986709 : Blo 1772087 5986709 := bbase (se 6 (by rfl) ⟨140313, by rfl⟩ : syracuseStep 5986709 = 280627) (by norm_num)
theorem B2660765 : Blo 1772087 2660765 := bbase (se 3 (by rfl) ⟨498893, by rfl⟩ : syracuseStep 2660765 = 997787) (by norm_num)
theorem B2242981 : Blo 1772087 2242981 := bbase (se 4 (by rfl) ⟨210279, by rfl⟩ : syracuseStep 2242981 = 420559) (by norm_num)
theorem B4045229 : Blo 1772087 4045229 := bbase (se 3 (by rfl) ⟨758480, by rfl⟩ : syracuseStep 4045229 = 1516961) (by norm_num)
theorem B2660789 : Blo 1772087 2660789 := bbase (se 5 (by rfl) ⟨124724, by rfl⟩ : syracuseStep 2660789 = 249449) (by norm_num)
theorem B3987917 : Blo 1772087 3987917 := bbase (se 3 (by rfl) ⟨747734, by rfl⟩ : syracuseStep 3987917 = 1495469) (by norm_num)
theorem B2660813 : Blo 1772087 2660813 := bbase (se 3 (by rfl) ⟨498902, by rfl⟩ : syracuseStep 2660813 = 997805) (by norm_num)
theorem B2660837 : Blo 1772087 2660837 := bbase (se 4 (by rfl) ⟨249453, by rfl⟩ : syracuseStep 2660837 = 498907) (by norm_num)
theorem B2660861 : Blo 1772087 2660861 := bbase (se 3 (by rfl) ⟨498911, by rfl⟩ : syracuseStep 2660861 = 997823) (by norm_num)
theorem B3987989 : Blo 1772087 3987989 := bbase (se 6 (by rfl) ⟨93468, by rfl⟩ : syracuseStep 3987989 = 186937) (by norm_num)
theorem B7191061 : Blo 1772087 7191061 := bbase (se 6 (by rfl) ⟨168540, by rfl⟩ : syracuseStep 7191061 = 337081) (by norm_num)
theorem B2660885 : Blo 1772087 2660885 := bbase (se 6 (by rfl) ⟨62364, by rfl⟩ : syracuseStep 2660885 = 124729) (by norm_num)
theorem B2660909 : Blo 1772087 2660909 := bbase (se 3 (by rfl) ⟨498920, by rfl⟩ : syracuseStep 2660909 = 997841) (by norm_num)
theorem B2660933 : Blo 1772087 2660933 := bbase (se 4 (by rfl) ⟨249462, by rfl⟩ : syracuseStep 2660933 = 498925) (by norm_num)
theorem B2243153 : Blo 1772087 2243153 := bbase (se 2 (by rfl) ⟨841182, by rfl⟩ : syracuseStep 2243153 = 1682365) (by norm_num)
theorem B3988061 : Blo 1772087 3988061 := bbase (se 3 (by rfl) ⟨747761, by rfl⟩ : syracuseStep 3988061 = 1495523) (by norm_num)
theorem B2660957 : Blo 1772087 2660957 := bbase (se 3 (by rfl) ⟨498929, by rfl⟩ : syracuseStep 2660957 = 997859) (by norm_num)
theorem B2660981 : Blo 1772087 2660981 := bbase (se 5 (by rfl) ⟨124733, by rfl⟩ : syracuseStep 2660981 = 249467) (by norm_num)
theorem B2841221 : Blo 1772087 2841221 := bbase (se 4 (by rfl) ⟨266364, by rfl⟩ : syracuseStep 2841221 = 532729) (by norm_num)
theorem B2243209 : Blo 1772087 2243209 := bbase (se 2 (by rfl) ⟨841203, by rfl⟩ : syracuseStep 2243209 = 1682407) (by norm_num)
theorem B2661005 : Blo 1772087 2661005 := bbase (se 3 (by rfl) ⟨498938, by rfl⟩ : syracuseStep 2661005 = 997877) (by norm_num)
theorem B7576213 : Blo 1772087 7576213 := bbase (se 6 (by rfl) ⟨177567, by rfl⟩ : syracuseStep 7576213 = 355135) (by norm_num)
theorem B4258469 : Blo 1772087 4258469 := bbase (se 4 (by rfl) ⟨399231, by rfl⟩ : syracuseStep 4258469 = 798463) (by norm_num)
theorem B3988133 : Blo 1772087 3988133 := bbase (se 4 (by rfl) ⟨373887, by rfl⟩ : syracuseStep 3988133 = 747775) (by norm_num)
theorem B4487845 : Blo 1772087 4487845 := bbase (se 4 (by rfl) ⟨420735, by rfl⟩ : syracuseStep 4487845 = 841471) (by norm_num)
theorem B2661029 : Blo 1772087 2661029 := bbase (se 4 (by rfl) ⟨249471, by rfl⟩ : syracuseStep 2661029 = 498943) (by norm_num)
theorem B2661053 : Blo 1772087 2661053 := bbase (se 3 (by rfl) ⟨498947, by rfl⟩ : syracuseStep 2661053 = 997895) (by norm_num)
theorem B2661077 : Blo 1772087 2661077 := bbase (se 7 (by rfl) ⟨31184, by rfl⟩ : syracuseStep 2661077 = 62369) (by norm_num)
theorem B2243305 : Blo 1772087 2243305 := bbase (se 2 (by rfl) ⟨841239, by rfl⟩ : syracuseStep 2243305 = 1682479) (by norm_num)
theorem B3988205 : Blo 1772087 3988205 := bbase (se 3 (by rfl) ⟨747788, by rfl⟩ : syracuseStep 3988205 = 1495577) (by norm_num)
theorem B2661101 : Blo 1772087 2661101 := bbase (se 3 (by rfl) ⟨498956, by rfl⟩ : syracuseStep 2661101 = 997913) (by norm_num)
theorem B4258565 : Blo 1772087 4258565 := bbase (se 4 (by rfl) ⟨399240, by rfl⟩ : syracuseStep 4258565 = 798481) (by norm_num)
theorem B2661125 : Blo 1772087 2661125 := bbase (se 4 (by rfl) ⟨249480, by rfl⟩ : syracuseStep 2661125 = 498961) (by norm_num)
theorem B4487957 : Blo 1772087 4487957 := bbase (se 6 (by rfl) ⟨105186, by rfl⟩ : syracuseStep 4487957 = 210373) (by norm_num)
theorem B3988277 : Blo 1772087 3988277 := bbase (se 5 (by rfl) ⟨186950, by rfl⟩ : syracuseStep 3988277 = 373901) (by norm_num)
theorem B5987141 : Blo 1772087 5987141 := bbase (se 4 (by rfl) ⟨561294, by rfl⟩ : syracuseStep 5987141 = 1122589) (by norm_num)
theorem B3365725 : Blo 1772087 3365725 := bbase (se 3 (by rfl) ⟨631073, by rfl⟩ : syracuseStep 3365725 = 1262147) (by norm_num)
theorem B6478709 : Blo 1772087 6478709 := bbase (se 5 (by rfl) ⟨303689, by rfl⟩ : syracuseStep 6478709 = 607379) (by norm_num)
theorem B3988349 : Blo 1772087 3988349 := bbase (se 3 (by rfl) ⟨747815, by rfl⟩ : syracuseStep 3988349 = 1495631) (by norm_num)
theorem B2243477 : Blo 1772087 2243477 := bbase (se 6 (by rfl) ⟨52581, by rfl⟩ : syracuseStep 2243477 = 105163) (by norm_num)
theorem B7674821 : Blo 1772087 7674821 := bbase (se 4 (by rfl) ⟨719514, by rfl⟩ : syracuseStep 7674821 = 1439029) (by norm_num)
theorem B3988421 : Blo 1772087 3988421 := bbase (se 4 (by rfl) ⟨373914, by rfl⟩ : syracuseStep 3988421 = 747829) (by norm_num)
theorem B2243533 : Blo 1772087 2243533 := bbase (se 3 (by rfl) ⟨420662, by rfl⟩ : syracuseStep 2243533 = 841325) (by norm_num)
theorem B4488149 : Blo 1772087 4488149 := bbase (se 7 (by rfl) ⟨52595, by rfl⟩ : syracuseStep 4488149 = 105191) (by norm_num)
theorem B2022377 : Blo 1772087 2022377 := bbase (se 2 (by rfl) ⟨758391, by rfl⟩ : syracuseStep 2022377 = 1516783) (by norm_num)
theorem B3365869 : Blo 1772087 3365869 := bbase (se 3 (by rfl) ⟨631100, by rfl⟩ : syracuseStep 3365869 = 1262201) (by norm_num)
theorem B3988493 : Blo 1772087 3988493 := bbase (se 3 (by rfl) ⟨747842, by rfl⟩ : syracuseStep 3988493 = 1495685) (by norm_num)
theorem B2243629 : Blo 1772087 2243629 := bbase (se 3 (by rfl) ⟨420680, by rfl⟩ : syracuseStep 2243629 = 841361) (by norm_num)
theorem B3988565 : Blo 1772087 3988565 := bbase (se 8 (by rfl) ⟨23370, by rfl⟩ : syracuseStep 3988565 = 46741) (by norm_num)
theorem B11361397 : Blo 1772087 11361397 := bbase (se 5 (by rfl) ⟨532565, by rfl⟩ : syracuseStep 11361397 = 1065131) (by norm_num)
theorem B3366029 : Blo 1772087 3366029 := bbase (se 3 (by rfl) ⟨631130, by rfl⟩ : syracuseStep 3366029 = 1262261) (by norm_num)
theorem B3988637 : Blo 1772087 3988637 := bbase (se 3 (by rfl) ⟨747869, by rfl⟩ : syracuseStep 3988637 = 1495739) (by norm_num)
theorem B2243801 : Blo 1772087 2243801 := bbase (se 2 (by rfl) ⟨841425, by rfl⟩ : syracuseStep 2243801 = 1682851) (by norm_num)
theorem B3988709 : Blo 1772087 3988709 := bbase (se 4 (by rfl) ⟨373941, by rfl⟩ : syracuseStep 3988709 = 747883) (by norm_num)
theorem B2243857 : Blo 1772087 2243857 := bbase (se 2 (by rfl) ⟨841446, by rfl⟩ : syracuseStep 2243857 = 1682893) (by norm_num)
theorem B3366173 : Blo 1772087 3366173 := bbase (se 3 (by rfl) ⟨631157, by rfl⟩ : syracuseStep 3366173 = 1262315) (by norm_num)
theorem B3988781 : Blo 1772087 3988781 := bbase (se 3 (by rfl) ⟨747896, by rfl⟩ : syracuseStep 3988781 = 1495793) (by norm_num)
theorem B4488493 : Blo 1772087 4488493 := bbase (se 3 (by rfl) ⟨841592, by rfl⟩ : syracuseStep 4488493 = 1683185) (by norm_num)
theorem B2243953 : Blo 1772087 2243953 := bbase (se 2 (by rfl) ⟨841482, by rfl⟩ : syracuseStep 2243953 = 1682965) (by norm_num)
theorem B3988853 : Blo 1772087 3988853 := bbase (se 5 (by rfl) ⟨186977, by rfl⟩ : syracuseStep 3988853 = 373955) (by norm_num)
theorem B4488605 : Blo 1772087 4488605 := bbase (se 3 (by rfl) ⟨841613, by rfl⟩ : syracuseStep 4488605 = 1683227) (by norm_num)
theorem B15154613 : Blo 1772087 15154613 := bbase (se 5 (by rfl) ⟨710372, by rfl⟩ : syracuseStep 15154613 = 1420745) (by norm_num)
theorem B3988925 : Blo 1772087 3988925 := bbase (se 3 (by rfl) ⟨747923, by rfl⟩ : syracuseStep 3988925 = 1495847) (by norm_num)
theorem B2694605 : Blo 1772087 2694605 := bbase (se 3 (by rfl) ⟨505238, by rfl⟩ : syracuseStep 2694605 = 1010477) (by norm_num)
theorem B8977877 : Blo 1772087 8977877 := bbase (se 7 (by rfl) ⟨105209, by rfl⟩ : syracuseStep 8977877 = 210419) (by norm_num)
theorem B3988997 : Blo 1772087 3988997 := bbase (se 4 (by rfl) ⟨373968, by rfl⟩ : syracuseStep 3988997 = 747937) (by norm_num)
theorem B2244125 : Blo 1772087 2244125 := bbase (se 3 (by rfl) ⟨420773, by rfl⟩ : syracuseStep 2244125 = 841547) (by norm_num)
theorem B3366461 : Blo 1772087 3366461 := bbase (se 3 (by rfl) ⟨631211, by rfl⟩ : syracuseStep 3366461 = 1262423) (by norm_num)
theorem B3989069 : Blo 1772087 3989069 := bbase (se 3 (by rfl) ⟨747950, by rfl⟩ : syracuseStep 3989069 = 1495901) (by norm_num)
theorem B2244181 : Blo 1772087 2244181 := bbase (se 8 (by rfl) ⟨13149, by rfl⟩ : syracuseStep 2244181 = 26299) (by norm_num)
theorem B4488797 : Blo 1772087 4488797 := bbase (se 3 (by rfl) ⟨841649, by rfl⟩ : syracuseStep 4488797 = 1683299) (by norm_num)
theorem B3989141 : Blo 1772087 3989141 := bbase (se 6 (by rfl) ⟨93495, by rfl⟩ : syracuseStep 3989141 = 186991) (by norm_num)
theorem B14384789 : Blo 1772087 14384789 := bbase (se 6 (by rfl) ⟨337143, by rfl⟩ : syracuseStep 14384789 = 674287) (by norm_num)
theorem B2244277 : Blo 1772087 2244277 := bbase (se 5 (by rfl) ⟨105200, by rfl⟩ : syracuseStep 2244277 = 210401) (by norm_num)
theorem B3366613 : Blo 1772087 3366613 := bbase (se 7 (by rfl) ⟨39452, by rfl⟩ : syracuseStep 3366613 = 78905) (by norm_num)
theorem B3989213 : Blo 1772087 3989213 := bbase (se 3 (by rfl) ⟨747977, by rfl⟩ : syracuseStep 3989213 = 1495955) (by norm_num)
theorem B2129657 : Blo 1772087 2129657 := bbase (se 2 (by rfl) ⟨798621, by rfl⟩ : syracuseStep 2129657 = 1597243) (by norm_num)
theorem B3989285 : Blo 1772087 3989285 := bbase (se 4 (by rfl) ⟨373995, by rfl⟩ : syracuseStep 3989285 = 747991) (by norm_num)
theorem B6733637 : Blo 1772087 6733637 := bbase (se 4 (by rfl) ⟨631278, by rfl⟩ : syracuseStep 6733637 = 1262557) (by norm_num)
theorem B2244449 : Blo 1772087 2244449 := bbase (se 2 (by rfl) ⟨841668, by rfl⟩ : syracuseStep 2244449 = 1683337) (by norm_num)
theorem B3989357 : Blo 1772087 3989357 := bbase (se 3 (by rfl) ⟨748004, by rfl⟩ : syracuseStep 3989357 = 1496009) (by norm_num)
theorem B2244505 : Blo 1772087 2244505 := bbase (se 2 (by rfl) ⟨841689, by rfl⟩ : syracuseStep 2244505 = 1683379) (by norm_num)
theorem B3989429 : Blo 1772087 3989429 := bbase (se 5 (by rfl) ⟨187004, by rfl⟩ : syracuseStep 3989429 = 374009) (by norm_num)
theorem B4489141 : Blo 1772087 4489141 := bbase (se 5 (by rfl) ⟨210428, by rfl⟩ : syracuseStep 4489141 = 420857) (by norm_num)
theorem B20742101 : Blo 1772087 20742101 := bbase (se 7 (by rfl) ⟨243071, by rfl⟩ : syracuseStep 20742101 = 486143) (by norm_num)
theorem B2244601 : Blo 1772087 2244601 := bbase (se 2 (by rfl) ⟨841725, by rfl⟩ : syracuseStep 2244601 = 1683451) (by norm_num)
theorem B3989501 : Blo 1772087 3989501 := bbase (se 3 (by rfl) ⟨748031, by rfl⟩ : syracuseStep 3989501 = 1496063) (by norm_num)
theorem B2244611 : Blo 1772087 2244611 := bstep (se 1 (by rfl) ⟨1683458, by rfl⟩ : syracuseStep 2244611 = 3366917) B3366917
theorem B3366947 : Blo 1772087 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B4489283 : Blo 1772087 4489283 := bstep (se 1 (by rfl) ⟨3366962, by rfl⟩ : syracuseStep 4489283 = 6733925) B6733925
theorem B3989681 : Blo 1772087 3989681 := bstep (se 2 (by rfl) ⟨1496130, by rfl⟩ : syracuseStep 3989681 = 2992261) B2992261
theorem B3989699 : Blo 1772087 3989699 := bstep (se 1 (by rfl) ⟨2992274, by rfl⟩ : syracuseStep 3989699 = 5984549) B5984549
theorem B10100933 : Blo 1772087 10100933 := bstep (se 4 (by rfl) ⟨946962, by rfl⟩ : syracuseStep 10100933 = 1893925) B1893925
theorem B5677265 : Blo 1772087 5677265 := bstep (se 2 (by rfl) ⟨2128974, by rfl⟩ : syracuseStep 5677265 = 4257949) B4257949
theorem B3784963 : Blo 1772087 3784963 := bstep (se 1 (by rfl) ⟨2838722, by rfl⟩ : syracuseStep 3784963 = 5677445) B5677445
theorem B2695457 : Blo 1772087 2695457 := bstep (se 2 (by rfl) ⟨1010796, by rfl⟩ : syracuseStep 2695457 = 2021593) B2021593
theorem B5390659 : Blo 1772087 5390659 := bstep (se 1 (by rfl) ⟨4042994, by rfl⟩ : syracuseStep 5390659 = 8085989) B8085989
theorem B10092869 : Blo 1772087 10092869 := bstep (se 4 (by rfl) ⟨946206, by rfl⟩ : syracuseStep 10092869 = 1892413) B1892413
theorem B5390669 : Blo 1772087 5390669 := bstep (se 3 (by rfl) ⟨1010750, by rfl⟩ : syracuseStep 5390669 = 2021501) B2021501
theorem B4792657 : Blo 1772087 4792657 := bstep (se 2 (by rfl) ⟨1797246, by rfl⟩ : syracuseStep 4792657 = 3594493) B3594493
theorem B17047907 : Blo 1772087 17047907 := bstep (se 1 (by rfl) ⟨12785930, by rfl⟩ : syracuseStep 17047907 = 25571861) B25571861
theorem B2695555 : Blo 1772087 2695555 := bstep (se 1 (by rfl) ⟨2021666, by rfl⟩ : syracuseStep 2695555 = 4043333) B4043333
theorem B1892755 : Blo 1772087 1892755 := bstep (se 1 (by rfl) ⟨1419566, by rfl⟩ : syracuseStep 1892755 = 2839133) B2839133
theorem B2990513 : Blo 1772087 2990513 := bstep (se 2 (by rfl) ⟨1121442, by rfl⟩ : syracuseStep 2990513 = 2242885) B2242885
theorem B7193009 : Blo 1772087 7193009 := bstep (se 2 (by rfl) ⟨2697378, by rfl⟩ : syracuseStep 7193009 = 5394757) B5394757
theorem B3989969 : Blo 1772087 3989969 := bstep (se 2 (by rfl) ⟨1496238, by rfl⟩ : syracuseStep 3989969 = 2992477) B2992477
theorem B5390819 : Blo 1772087 5390819 := bstep (se 1 (by rfl) ⟨4043114, by rfl⟩ : syracuseStep 5390819 = 8086229) B8086229
theorem B3989987 : Blo 1772087 3989987 := bstep (se 1 (by rfl) ⟨2992490, by rfl⟩ : syracuseStep 3989987 = 5984981) B5984981
theorem B3785219 : Blo 1772087 3785219 := bstep (se 1 (by rfl) ⟨2838914, by rfl⟩ : syracuseStep 3785219 = 5677829) B5677829
theorem B3195409 : Blo 1772087 3195409 := bstep (se 2 (by rfl) ⟨1198278, by rfl⟩ : syracuseStep 3195409 = 2396557) B2396557
theorem B2990641 : Blo 1772087 2990641 := bstep (se 2 (by rfl) ⟨1121490, by rfl⟩ : syracuseStep 2990641 = 2242981) B2242981
theorem B9585229 : Blo 1772087 9585229 := bstep (se 3 (by rfl) ⟨1797230, by rfl⟩ : syracuseStep 9585229 = 3594461) B3594461
theorem B2990675 : Blo 1772087 2990675 := bstep (se 1 (by rfl) ⟨2243006, by rfl⟩ : syracuseStep 2990675 = 4486013) B4486013
theorem B2523793 : Blo 1772087 2523793 := bstep (se 2 (by rfl) ⟨946422, by rfl⟩ : syracuseStep 2523793 = 1892845) B1892845
theorem B7570097 : Blo 1772087 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B2245315 : Blo 1772087 2245315 := bstep (se 1 (by rfl) ⟨1683986, by rfl⟩ : syracuseStep 2245315 = 3367973) B3367973
theorem B5980877 : Blo 1772087 5980877 := bstep (se 3 (by rfl) ⟨1121414, by rfl⟩ : syracuseStep 5980877 = 2242829) B2242829
theorem B2990803 : Blo 1772087 2990803 := bstep (se 1 (by rfl) ⟨2243102, by rfl⟩ : syracuseStep 2990803 = 4486205) B4486205
theorem B2523889 : Blo 1772087 2523889 := bstep (se 2 (by rfl) ⟨946458, by rfl⟩ : syracuseStep 2523889 = 1892917) B1892917
theorem B3990257 : Blo 1772087 3990257 := bstep (se 2 (by rfl) ⟨1496346, by rfl⟩ : syracuseStep 3990257 = 2992693) B2992693
theorem B5980931 : Blo 1772087 5980931 := bstep (se 1 (by rfl) ⟨4485698, by rfl⟩ : syracuseStep 5980931 = 8971397) B8971397
theorem B3990275 : Blo 1772087 3990275 := bstep (se 1 (by rfl) ⟨2992706, by rfl⟩ : syracuseStep 3990275 = 5985413) B5985413
theorem B2990945 : Blo 1772087 2990945 := bstep (se 2 (by rfl) ⟨1121604, by rfl⟩ : syracuseStep 2990945 = 2243209) B2243209
theorem B10101617 : Blo 1772087 10101617 := bstep (se 2 (by rfl) ⟨3788106, by rfl⟩ : syracuseStep 10101617 = 7576213) B7576213
theorem B15139781 : Blo 1772087 15139781 := bstep (se 4 (by rfl) ⟨1419354, by rfl⟩ : syracuseStep 15139781 = 2838709) B2838709
theorem B4858829 : Blo 1772087 4858829 := bstep (se 3 (by rfl) ⟨911030, by rfl⟩ : syracuseStep 4858829 = 1822061) B1822061
theorem B3367889 : Blo 1772087 3367889 := bstep (se 2 (by rfl) ⟨1262958, by rfl⟩ : syracuseStep 3367889 = 2525917) B2525917
theorem B2991073 : Blo 1772087 2991073 := bstep (se 2 (by rfl) ⟨1121652, by rfl⟩ : syracuseStep 2991073 = 2243305) B2243305
theorem B8971235 : Blo 1772087 8971235 := bstep (se 1 (by rfl) ⟨6728426, by rfl⟩ : syracuseStep 8971235 = 13456853) B13456853
theorem B4490225 : Blo 1772087 4490225 := bstep (se 2 (by rfl) ⟨1683834, by rfl⟩ : syracuseStep 4490225 = 3367669) B3367669
theorem B2991107 : Blo 1772087 2991107 := bstep (se 1 (by rfl) ⟨2243330, by rfl⟩ : syracuseStep 2991107 = 4486661) B4486661
theorem B22709261 : Blo 1772087 22709261 := bstep (se 3 (by rfl) ⟨4257986, by rfl⟩ : syracuseStep 22709261 = 8515973) B8515973
theorem B5981201 : Blo 1772087 5981201 := bstep (se 2 (by rfl) ⟨2242950, by rfl⟩ : syracuseStep 5981201 = 4485901) B4485901
theorem B3990545 : Blo 1772087 3990545 := bstep (se 2 (by rfl) ⟨1496454, by rfl⟩ : syracuseStep 3990545 = 2992909) B2992909
theorem B3990563 : Blo 1772087 3990563 := bstep (se 1 (by rfl) ⟨2992922, by rfl⟩ : syracuseStep 3990563 = 5985845) B5985845
theorem B4490275 : Blo 1772087 4490275 := bstep (se 1 (by rfl) ⟨3367706, by rfl⟩ : syracuseStep 4490275 = 6735413) B6735413
theorem B6734897 : Blo 1772087 6734897 := bstep (se 2 (by rfl) ⟨2525586, by rfl⟩ : syracuseStep 6734897 = 5051173) B5051173
theorem B2769985 : Blo 1772087 2769985 := bstep (se 2 (by rfl) ⟨1038744, by rfl⟩ : syracuseStep 2769985 = 2077489) B2077489
theorem B14566499 : Blo 1772087 14566499 := bstep (se 1 (by rfl) ⟨10924874, by rfl⟩ : syracuseStep 14566499 = 21849749) B21849749
theorem B2991235 : Blo 1772087 2991235 := bstep (se 1 (by rfl) ⟨2243426, by rfl⟩ : syracuseStep 2991235 = 4486853) B4486853
theorem B34079885 : Blo 1772087 34079885 := bstep (se 3 (by rfl) ⟨6389978, by rfl⟩ : syracuseStep 34079885 = 12779957) B12779957
theorem B11355299 : Blo 1772087 11355299 := bstep (se 1 (by rfl) ⟨8516474, by rfl⟩ : syracuseStep 11355299 = 17032949) B17032949
theorem B4490417 : Blo 1772087 4490417 := bstep (se 2 (by rfl) ⟨1683906, by rfl⟩ : syracuseStep 4490417 = 3367813) B3367813
theorem B7185613 : Blo 1772087 7185613 := bstep (se 3 (by rfl) ⟨1347302, by rfl⟩ : syracuseStep 7185613 = 2694605) B2694605
theorem B5047505 : Blo 1772087 5047505 := bstep (se 2 (by rfl) ⟨1892814, by rfl⟩ : syracuseStep 5047505 = 3785629) B3785629
theorem B2524385 : Blo 1772087 2524385 := bstep (se 2 (by rfl) ⟨946644, by rfl⟩ : syracuseStep 2524385 = 1893289) B1893289
theorem B2991377 : Blo 1772087 2991377 := bstep (se 2 (by rfl) ⟨1121766, by rfl⟩ : syracuseStep 2991377 = 2243533) B2243533
theorem B6391075 : Blo 1772087 6391075 := bstep (se 1 (by rfl) ⟨4793306, by rfl⟩ : syracuseStep 6391075 = 9586613) B9586613
theorem B3990833 : Blo 1772087 3990833 := bstep (se 2 (by rfl) ⟨1496562, by rfl⟩ : syracuseStep 3990833 = 2993125) B2993125
theorem B3990851 : Blo 1772087 3990851 := bstep (se 1 (by rfl) ⟨2993138, by rfl⟩ : syracuseStep 3990851 = 5986277) B5986277
theorem B6063437 : Blo 1772087 6063437 := bstep (se 3 (by rfl) ⟨1136894, by rfl⟩ : syracuseStep 6063437 = 2273789) B2273789
theorem B3032417 : Blo 1772087 3032417 := bstep (se 2 (by rfl) ⟨1137156, by rfl⟩ : syracuseStep 3032417 = 2274313) B2274313
theorem B2991505 : Blo 1772087 2991505 := bstep (se 2 (by rfl) ⟨1121814, by rfl⟩ : syracuseStep 2991505 = 2243629) B2243629
theorem B2991539 : Blo 1772087 2991539 := bstep (se 1 (by rfl) ⟨2243654, by rfl⟩ : syracuseStep 2991539 = 4487309) B4487309
theorem B20194757 : Blo 1772087 20194757 := bstep (se 4 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 20194757 = 3786517) B3786517
theorem B3786193 : Blo 1772087 3786193 := bstep (se 2 (by rfl) ⟨1419822, by rfl⟩ : syracuseStep 3786193 = 2839645) B2839645
theorem B3237347 : Blo 1772087 3237347 := bstep (se 1 (by rfl) ⟨2428010, by rfl⟩ : syracuseStep 3237347 = 4856021) B4856021
theorem B15148529 : Blo 1772087 15148529 := bstep (se 2 (by rfl) ⟨5680698, by rfl⟩ : syracuseStep 15148529 = 11361397) B11361397
theorem B2696723 : Blo 1772087 2696723 := bstep (se 1 (by rfl) ⟨2022542, by rfl⟩ : syracuseStep 2696723 = 4045085) B4045085
theorem B5981741 : Blo 1772087 5981741 := bstep (se 3 (by rfl) ⟨1121576, by rfl⟩ : syracuseStep 5981741 = 2243153) B2243153
theorem B2991667 : Blo 1772087 2991667 := bstep (se 1 (by rfl) ⟨2243750, by rfl⟩ : syracuseStep 2991667 = 4487501) B4487501
theorem B3991121 : Blo 1772087 3991121 := bstep (se 2 (by rfl) ⟨1496670, by rfl⟩ : syracuseStep 3991121 = 2993341) B2993341
theorem B5981795 : Blo 1772087 5981795 := bstep (se 1 (by rfl) ⟨4486346, by rfl⟩ : syracuseStep 5981795 = 8972693) B8972693
theorem B3991139 : Blo 1772087 3991139 := bstep (se 1 (by rfl) ⟨2993354, by rfl⟩ : syracuseStep 3991139 = 5986709) B5986709
theorem B15140465 : Blo 1772087 15140465 := bstep (se 2 (by rfl) ⟨5677674, by rfl⟩ : syracuseStep 15140465 = 11355349) B11355349
theorem B2696819 : Blo 1772087 2696819 := bstep (se 1 (by rfl) ⟨2022614, by rfl⟩ : syracuseStep 2696819 = 4045229) B4045229
theorem B8980145 : Blo 1772087 8980145 := bstep (se 2 (by rfl) ⟨3367554, by rfl⟩ : syracuseStep 8980145 = 6735109) B6735109
theorem B2991809 : Blo 1772087 2991809 := bstep (se 2 (by rfl) ⟨1121928, by rfl⟩ : syracuseStep 2991809 = 2243857) B2243857
theorem B1894147 : Blo 1772087 1894147 := bstep (se 1 (by rfl) ⟨1420610, by rfl⟩ : syracuseStep 1894147 = 2841221) B2841221
theorem B8972045 : Blo 1772087 8972045 := bstep (se 3 (by rfl) ⟨1682258, by rfl⟩ : syracuseStep 8972045 = 3364517) B3364517
theorem B2991937 : Blo 1772087 2991937 := bstep (se 2 (by rfl) ⟨1121976, by rfl⟩ : syracuseStep 2991937 = 2243953) B2243953
theorem B2991971 : Blo 1772087 2991971 := bstep (se 1 (by rfl) ⟨2243978, by rfl⟩ : syracuseStep 2991971 = 4487957) B4487957
theorem B5982065 : Blo 1772087 5982065 := bstep (se 2 (by rfl) ⟨2243274, by rfl⟩ : syracuseStep 5982065 = 4486549) B4486549
theorem B3991409 : Blo 1772087 3991409 := bstep (se 2 (by rfl) ⟨1496778, by rfl⟩ : syracuseStep 3991409 = 2993557) B2993557
theorem B3991427 : Blo 1772087 3991427 := bstep (se 1 (by rfl) ⟨2993570, by rfl⟩ : syracuseStep 3991427 = 5987141) B5987141
theorem B3196835 : Blo 1772087 3196835 := bstep (se 1 (by rfl) ⟨2397626, by rfl⟩ : syracuseStep 3196835 = 4795253) B4795253
theorem B4925357 : Blo 1772087 4925357 := bstep (se 3 (by rfl) ⟨923504, by rfl⟩ : syracuseStep 4925357 = 1847009) B1847009
theorem B3073969 : Blo 1772087 3073969 := bstep (se 2 (by rfl) ⟨1152738, by rfl⟩ : syracuseStep 3073969 = 2305477) B2305477
theorem B28772293 : Blo 1772087 28772293 := bstep (se 4 (by rfl) ⟨2697402, by rfl⟩ : syracuseStep 28772293 = 5394805) B5394805
theorem B2992099 : Blo 1772087 2992099 := bstep (se 1 (by rfl) ⟨2244074, by rfl⟩ : syracuseStep 2992099 = 4488149) B4488149
theorem B5679085 : Blo 1772087 5679085 := bstep (se 3 (by rfl) ⟨1064828, by rfl⟩ : syracuseStep 5679085 = 2129657) B2129657
theorem B20203505 : Blo 1772087 20203505 := bstep (se 2 (by rfl) ⟨7576314, by rfl⟩ : syracuseStep 20203505 = 15152629) B15152629
theorem B32368693 : Blo 1772087 32368693 := bstep (se 5 (by rfl) ⟨1517282, by rfl⟩ : syracuseStep 32368693 = 3034565) B3034565
theorem B2525251 : Blo 1772087 2525251 := bstep (se 1 (by rfl) ⟨1893938, by rfl⟩ : syracuseStep 2525251 = 3787877) B3787877
theorem B3786851 : Blo 1772087 3786851 := bstep (se 1 (by rfl) ⟨2840138, by rfl⟩ : syracuseStep 3786851 = 5680277) B5680277
theorem B2992241 : Blo 1772087 2992241 := bstep (se 2 (by rfl) ⟨1122090, by rfl⟩ : syracuseStep 2992241 = 2244181) B2244181
theorem B3991697 : Blo 1772087 3991697 := bstep (se 2 (by rfl) ⟨1496886, by rfl⟩ : syracuseStep 3991697 = 2993773) B2993773
theorem B2525347 : Blo 1772087 2525347 := bstep (se 1 (by rfl) ⟨1894010, by rfl⟩ : syracuseStep 2525347 = 3788021) B3788021
theorem B28772549 : Blo 1772087 28772549 := bstep (se 4 (by rfl) ⟨2697426, by rfl⟩ : syracuseStep 28772549 = 5394853) B5394853
theorem B8521955 : Blo 1772087 8521955 := bstep (se 1 (by rfl) ⟨6391466, by rfl⟩ : syracuseStep 8521955 = 12782933) B12782933
theorem B2992369 : Blo 1772087 2992369 := bstep (se 2 (by rfl) ⟨1122138, by rfl⟩ : syracuseStep 2992369 = 2244277) B2244277
theorem B2992403 : Blo 1772087 2992403 := bstep (se 1 (by rfl) ⟨2244302, by rfl⟩ : syracuseStep 2992403 = 4488605) B4488605
theorem B10103075 : Blo 1772087 10103075 := bstep (se 1 (by rfl) ⟨7577306, by rfl⟩ : syracuseStep 10103075 = 15154613) B15154613
theorem B7571789 : Blo 1772087 7571789 := bstep (se 3 (by rfl) ⟨1419710, by rfl⟩ : syracuseStep 7571789 = 2839421) B2839421
theorem B5982605 : Blo 1772087 5982605 := bstep (se 3 (by rfl) ⟨1121738, by rfl⟩ : syracuseStep 5982605 = 2243477) B2243477
theorem B2992531 : Blo 1772087 2992531 := bstep (se 1 (by rfl) ⟨2244398, by rfl⟩ : syracuseStep 2992531 = 4488797) B4488797
theorem B21572021 : Blo 1772087 21572021 := bstep (se 5 (by rfl) ⟨1011188, by rfl⟩ : syracuseStep 21572021 = 2022377) B2022377
theorem B5982659 : Blo 1772087 5982659 := bstep (se 1 (by rfl) ⟨4486994, by rfl⟩ : syracuseStep 5982659 = 8973989) B8973989
theorem B2877985 : Blo 1772087 2877985 := bstep (se 2 (by rfl) ⟨1079244, by rfl⟩ : syracuseStep 2877985 = 2158489) B2158489
theorem B2992673 : Blo 1772087 2992673 := bstep (se 2 (by rfl) ⟨1122252, by rfl⟩ : syracuseStep 2992673 = 2244505) B2244505
theorem B86247989 : Blo 1772087 86247989 := bstep (se 5 (by rfl) ⟨4042874, by rfl⟩ : syracuseStep 86247989 = 8085749) B8085749
theorem B1772099 : Blo 1772087 1772099 := bstep (se 1 (by rfl) ⟨1329074, by rfl⟩ : syracuseStep 1772099 = 2658149) B2658149
theorem B1772115 : Blo 1772087 1772115 := bstep (se 1 (by rfl) ⟨1329086, by rfl⟩ : syracuseStep 1772115 = 2658173) B2658173
theorem B1772131 : Blo 1772087 1772131 := bstep (se 1 (by rfl) ⟨1329098, by rfl⟩ : syracuseStep 1772131 = 2658197) B2658197
theorem B1772147 : Blo 1772087 1772147 := bstep (se 1 (by rfl) ⟨1329110, by rfl⟩ : syracuseStep 1772147 = 2658221) B2658221
theorem B1772163 : Blo 1772087 1772163 := bstep (se 1 (by rfl) ⟨1329122, by rfl⟩ : syracuseStep 1772163 = 2658245) B2658245
theorem B5048963 : Blo 1772087 5048963 := bstep (se 1 (by rfl) ⟨3786722, by rfl⟩ : syracuseStep 5048963 = 7573445) B7573445
theorem B1772179 : Blo 1772087 1772179 := bstep (se 1 (by rfl) ⟨1329134, by rfl⟩ : syracuseStep 1772179 = 2658269) B2658269
theorem B2525843 : Blo 1772087 2525843 := bstep (se 1 (by rfl) ⟨1894382, by rfl⟩ : syracuseStep 2525843 = 3788765) B3788765
theorem B2992801 : Blo 1772087 2992801 := bstep (se 2 (by rfl) ⟨1122300, by rfl⟩ : syracuseStep 2992801 = 2244601) B2244601
theorem B1772195 : Blo 1772087 1772195 := bstep (se 1 (by rfl) ⟨1329146, by rfl⟩ : syracuseStep 1772195 = 2658293) B2658293
theorem B1772211 : Blo 1772087 1772211 := bstep (se 1 (by rfl) ⟨1329158, by rfl⟩ : syracuseStep 1772211 = 2658317) B2658317
theorem B3033779 : Blo 1772087 3033779 := bstep (se 1 (by rfl) ⟨2275334, by rfl⟩ : syracuseStep 3033779 = 4550669) B4550669
theorem B1772227 : Blo 1772087 1772227 := bstep (se 1 (by rfl) ⟨1329170, by rfl⟩ : syracuseStep 1772227 = 2658341) B2658341
theorem B2992835 : Blo 1772087 2992835 := bstep (se 1 (by rfl) ⟨2244626, by rfl⟩ : syracuseStep 2992835 = 4489253) B4489253
theorem B5982929 : Blo 1772087 5982929 := bstep (se 2 (by rfl) ⟨2243598, by rfl⟩ : syracuseStep 5982929 = 4487197) B4487197
theorem B1772243 : Blo 1772087 1772243 := bstep (se 1 (by rfl) ⟨1329182, by rfl⟩ : syracuseStep 1772243 = 2658365) B2658365
theorem B1772259 : Blo 1772087 1772259 := bstep (se 1 (by rfl) ⟨1329194, by rfl⟩ : syracuseStep 1772259 = 2658389) B2658389
theorem B1772275 : Blo 1772087 1772275 := bstep (se 1 (by rfl) ⟨1329206, by rfl⟩ : syracuseStep 1772275 = 2658413) B2658413
theorem B2878195 : Blo 1772087 2878195 := bstep (se 1 (by rfl) ⟨2158646, by rfl⟩ : syracuseStep 2878195 = 4317293) B4317293
theorem B1772291 : Blo 1772087 1772291 := bstep (se 1 (by rfl) ⟨1329218, by rfl⟩ : syracuseStep 1772291 = 2658437) B2658437
theorem B7383821 : Blo 1772087 7383821 := bstep (se 3 (by rfl) ⟨1384466, by rfl⟩ : syracuseStep 7383821 = 2768933) B2768933
theorem B1772307 : Blo 1772087 1772307 := bstep (se 1 (by rfl) ⟨1329230, by rfl⟩ : syracuseStep 1772307 = 2658461) B2658461
theorem B1772323 : Blo 1772087 1772323 := bstep (se 1 (by rfl) ⟨1329242, by rfl⟩ : syracuseStep 1772323 = 2658485) B2658485
theorem B1772339 : Blo 1772087 1772339 := bstep (se 1 (by rfl) ⟨1329254, by rfl⟩ : syracuseStep 1772339 = 2658509) B2658509
theorem B1772355 : Blo 1772087 1772355 := bstep (se 1 (by rfl) ⟨1329266, by rfl⟩ : syracuseStep 1772355 = 2658533) B2658533
theorem B2992963 : Blo 1772087 2992963 := bstep (se 1 (by rfl) ⟨2244722, by rfl⟩ : syracuseStep 2992963 = 4489445) B4489445
theorem B1772371 : Blo 1772087 1772371 := bstep (se 1 (by rfl) ⟨1329278, by rfl⟩ : syracuseStep 1772371 = 2658557) B2658557
theorem B1772387 : Blo 1772087 1772387 := bstep (se 1 (by rfl) ⟨1329290, by rfl⟩ : syracuseStep 1772387 = 2658581) B2658581
theorem B1772403 : Blo 1772087 1772403 := bstep (se 1 (by rfl) ⟨1329302, by rfl⟩ : syracuseStep 1772403 = 2658605) B2658605
theorem B1993603 : Blo 1772087 1993603 := bstep (se 1 (by rfl) ⟨1495202, by rfl⟩ : syracuseStep 1993603 = 2990405) B2990405
theorem B1772419 : Blo 1772087 1772419 := bstep (se 1 (by rfl) ⟨1329314, by rfl⟩ : syracuseStep 1772419 = 2658629) B2658629
theorem B1772435 : Blo 1772087 1772435 := bstep (se 1 (by rfl) ⟨1329326, by rfl⟩ : syracuseStep 1772435 = 2658653) B2658653
theorem B1772451 : Blo 1772087 1772451 := bstep (se 1 (by rfl) ⟨1329338, by rfl⟩ : syracuseStep 1772451 = 2658677) B2658677
theorem B3787697 : Blo 1772087 3787697 := bstep (se 2 (by rfl) ⟨1420386, by rfl⟩ : syracuseStep 3787697 = 2840773) B2840773
theorem B1772467 : Blo 1772087 1772467 := bstep (se 1 (by rfl) ⟨1329350, by rfl⟩ : syracuseStep 1772467 = 2658701) B2658701
theorem B1772483 : Blo 1772087 1772483 := bstep (se 1 (by rfl) ⟨1329362, by rfl⟩ : syracuseStep 1772483 = 2658725) B2658725
theorem B2993105 : Blo 1772087 2993105 := bstep (se 2 (by rfl) ⟨1122414, by rfl⟩ : syracuseStep 2993105 = 2244829) B2244829
theorem B1772499 : Blo 1772087 1772499 := bstep (se 1 (by rfl) ⟨1329374, by rfl⟩ : syracuseStep 1772499 = 2658749) B2658749
theorem B1772515 : Blo 1772087 1772515 := bstep (se 1 (by rfl) ⟨1329386, by rfl⟩ : syracuseStep 1772515 = 2658773) B2658773
theorem B1772531 : Blo 1772087 1772531 := bstep (se 1 (by rfl) ⟨1329398, by rfl⟩ : syracuseStep 1772531 = 2658797) B2658797
theorem B1772547 : Blo 1772087 1772547 := bstep (se 1 (by rfl) ⟨1329410, by rfl⟩ : syracuseStep 1772547 = 2658821) B2658821
theorem B1993747 : Blo 1772087 1993747 := bstep (se 1 (by rfl) ⟨1495310, by rfl⟩ : syracuseStep 1993747 = 2990621) B2990621
theorem B1772563 : Blo 1772087 1772563 := bstep (se 1 (by rfl) ⟨1329422, by rfl⟩ : syracuseStep 1772563 = 2658845) B2658845
theorem B1772579 : Blo 1772087 1772579 := bstep (se 1 (by rfl) ⟨1329434, by rfl⟩ : syracuseStep 1772579 = 2658869) B2658869
theorem B1772595 : Blo 1772087 1772595 := bstep (se 1 (by rfl) ⟨1329446, by rfl⟩ : syracuseStep 1772595 = 2658893) B2658893
theorem B1772611 : Blo 1772087 1772611 := bstep (se 1 (by rfl) ⟨1329458, by rfl⟩ : syracuseStep 1772611 = 2658917) B2658917
theorem B2993233 : Blo 1772087 2993233 := bstep (se 2 (by rfl) ⟨1122462, by rfl⟩ : syracuseStep 2993233 = 2244925) B2244925
theorem B1772627 : Blo 1772087 1772627 := bstep (se 1 (by rfl) ⟨1329470, by rfl⟩ : syracuseStep 1772627 = 2658941) B2658941
theorem B4041827 : Blo 1772087 4041827 := bstep (se 1 (by rfl) ⟨3031370, by rfl⟩ : syracuseStep 4041827 = 6062741) B6062741
theorem B1772643 : Blo 1772087 1772643 := bstep (se 1 (by rfl) ⟨1329482, by rfl⟩ : syracuseStep 1772643 = 2658965) B2658965
theorem B11357297 : Blo 1772087 11357297 := bstep (se 2 (by rfl) ⟨4258986, by rfl⟩ : syracuseStep 11357297 = 8517973) B8517973
theorem B18197617 : Blo 1772087 18197617 := bstep (se 2 (by rfl) ⟨6824106, by rfl⟩ : syracuseStep 18197617 = 13648213) B13648213
theorem B1772659 : Blo 1772087 1772659 := bstep (se 1 (by rfl) ⟨1329494, by rfl⟩ : syracuseStep 1772659 = 2658989) B2658989
theorem B2993267 : Blo 1772087 2993267 := bstep (se 1 (by rfl) ⟨2244950, by rfl⟩ : syracuseStep 2993267 = 4489901) B4489901
theorem B1772675 : Blo 1772087 1772675 := bstep (se 1 (by rfl) ⟨1329506, by rfl⟩ : syracuseStep 1772675 = 2659013) B2659013
theorem B1772691 : Blo 1772087 1772691 := bstep (se 1 (by rfl) ⟨1329518, by rfl⟩ : syracuseStep 1772691 = 2659037) B2659037
theorem B1993891 : Blo 1772087 1993891 := bstep (se 1 (by rfl) ⟨1495418, by rfl⟩ : syracuseStep 1993891 = 2990837) B2990837
theorem B1772707 : Blo 1772087 1772707 := bstep (se 1 (by rfl) ⟨1329530, by rfl⟩ : syracuseStep 1772707 = 2659061) B2659061
theorem B1772723 : Blo 1772087 1772723 := bstep (se 1 (by rfl) ⟨1329542, by rfl⟩ : syracuseStep 1772723 = 2659085) B2659085
theorem B2559155 : Blo 1772087 2559155 := bstep (se 1 (by rfl) ⟨1919366, by rfl⟩ : syracuseStep 2559155 = 3838733) B3838733
theorem B1772739 : Blo 1772087 1772739 := bstep (se 1 (by rfl) ⟨1329554, by rfl⟩ : syracuseStep 1772739 = 2659109) B2659109
theorem B1772755 : Blo 1772087 1772755 := bstep (se 1 (by rfl) ⟨1329566, by rfl⟩ : syracuseStep 1772755 = 2659133) B2659133
theorem B1772771 : Blo 1772087 1772771 := bstep (se 1 (by rfl) ⟨1329578, by rfl⟩ : syracuseStep 1772771 = 2659157) B2659157
theorem B13470947 : Blo 1772087 13470947 := bstep (se 1 (by rfl) ⟨10103210, by rfl⟩ : syracuseStep 13470947 = 20206421) B20206421
theorem B5983469 : Blo 1772087 5983469 := bstep (se 3 (by rfl) ⟨1121900, by rfl⟩ : syracuseStep 5983469 = 2243801) B2243801
theorem B19164401 : Blo 1772087 19164401 := bstep (se 2 (by rfl) ⟨7186650, by rfl⟩ : syracuseStep 19164401 = 14373301) B14373301
theorem B1772787 : Blo 1772087 1772787 := bstep (se 1 (by rfl) ⟨1329590, by rfl⟩ : syracuseStep 1772787 = 2659181) B2659181
theorem B2993395 : Blo 1772087 2993395 := bstep (se 1 (by rfl) ⟨2245046, by rfl⟩ : syracuseStep 2993395 = 4490093) B4490093
theorem B1772803 : Blo 1772087 1772803 := bstep (se 1 (by rfl) ⟨1329602, by rfl⟩ : syracuseStep 1772803 = 2659205) B2659205
theorem B1772819 : Blo 1772087 1772819 := bstep (se 1 (by rfl) ⟨1329614, by rfl⟩ : syracuseStep 1772819 = 2659229) B2659229
theorem B1772835 : Blo 1772087 1772835 := bstep (se 1 (by rfl) ⟨1329626, by rfl⟩ : syracuseStep 1772835 = 2659253) B2659253
theorem B5983523 : Blo 1772087 5983523 := bstep (se 1 (by rfl) ⟨4487642, by rfl⟩ : syracuseStep 5983523 = 8975285) B8975285
theorem B4549937 : Blo 1772087 4549937 := bstep (se 2 (by rfl) ⟨1706226, by rfl⟩ : syracuseStep 4549937 = 3412453) B3412453
theorem B1994035 : Blo 1772087 1994035 := bstep (se 1 (by rfl) ⟨1495526, by rfl⟩ : syracuseStep 1994035 = 2991053) B2991053
theorem B1772851 : Blo 1772087 1772851 := bstep (se 1 (by rfl) ⟨1329638, by rfl⟩ : syracuseStep 1772851 = 2659277) B2659277
theorem B1772867 : Blo 1772087 1772867 := bstep (se 1 (by rfl) ⟨1329650, by rfl⟩ : syracuseStep 1772867 = 2659301) B2659301
theorem B1772883 : Blo 1772087 1772883 := bstep (se 1 (by rfl) ⟨1329662, by rfl⟩ : syracuseStep 1772883 = 2659325) B2659325
theorem B1772899 : Blo 1772087 1772899 := bstep (se 1 (by rfl) ⟨1329674, by rfl⟩ : syracuseStep 1772899 = 2659349) B2659349
theorem B1772915 : Blo 1772087 1772915 := bstep (se 1 (by rfl) ⟨1329686, by rfl⟩ : syracuseStep 1772915 = 2659373) B2659373
theorem B2993537 : Blo 1772087 2993537 := bstep (se 2 (by rfl) ⟨1122576, by rfl⟩ : syracuseStep 2993537 = 2245153) B2245153
theorem B1772931 : Blo 1772087 1772931 := bstep (se 1 (by rfl) ⟨1329698, by rfl⟩ : syracuseStep 1772931 = 2659397) B2659397
theorem B1772947 : Blo 1772087 1772947 := bstep (se 1 (by rfl) ⟨1329710, by rfl⟩ : syracuseStep 1772947 = 2659421) B2659421
theorem B1772963 : Blo 1772087 1772963 := bstep (se 1 (by rfl) ⟨1329722, by rfl⟩ : syracuseStep 1772963 = 2659445) B2659445
theorem B5049773 : Blo 1772087 5049773 := bstep (se 3 (by rfl) ⟨946832, by rfl⟩ : syracuseStep 5049773 = 1893665) B1893665
theorem B1772979 : Blo 1772087 1772979 := bstep (se 1 (by rfl) ⟨1329734, by rfl⟩ : syracuseStep 1772979 = 2659469) B2659469
theorem B1994179 : Blo 1772087 1994179 := bstep (se 1 (by rfl) ⟨1495634, by rfl⟩ : syracuseStep 1994179 = 2991269) B2991269
theorem B1772995 : Blo 1772087 1772995 := bstep (se 1 (by rfl) ⟨1329746, by rfl⟩ : syracuseStep 1772995 = 2659493) B2659493
theorem B1773011 : Blo 1772087 1773011 := bstep (se 1 (by rfl) ⟨1329758, by rfl⟩ : syracuseStep 1773011 = 2659517) B2659517
theorem B1773027 : Blo 1772087 1773027 := bstep (se 1 (by rfl) ⟨1329770, by rfl⟩ : syracuseStep 1773027 = 2659541) B2659541
theorem B1773043 : Blo 1772087 1773043 := bstep (se 1 (by rfl) ⟨1329782, by rfl⟩ : syracuseStep 1773043 = 2659565) B2659565
theorem B2993665 : Blo 1772087 2993665 := bstep (se 2 (by rfl) ⟨1122624, by rfl⟩ : syracuseStep 2993665 = 2245249) B2245249
theorem B1773059 : Blo 1772087 1773059 := bstep (se 1 (by rfl) ⟨1329794, by rfl⟩ : syracuseStep 1773059 = 2659589) B2659589
theorem B1773075 : Blo 1772087 1773075 := bstep (se 1 (by rfl) ⟨1329806, by rfl⟩ : syracuseStep 1773075 = 2659613) B2659613
theorem B1773091 : Blo 1772087 1773091 := bstep (se 1 (by rfl) ⟨1329818, by rfl⟩ : syracuseStep 1773091 = 2659637) B2659637
theorem B2993699 : Blo 1772087 2993699 := bstep (se 1 (by rfl) ⟨2245274, by rfl⟩ : syracuseStep 2993699 = 4490549) B4490549
theorem B5983793 : Blo 1772087 5983793 := bstep (se 2 (by rfl) ⟨2243922, by rfl⟩ : syracuseStep 5983793 = 4487845) B4487845
theorem B1773107 : Blo 1772087 1773107 := bstep (se 1 (by rfl) ⟨1329830, by rfl⟩ : syracuseStep 1773107 = 2659661) B2659661
theorem B1773123 : Blo 1772087 1773123 := bstep (se 1 (by rfl) ⟨1329842, by rfl⟩ : syracuseStep 1773123 = 2659685) B2659685
theorem B12136013 : Blo 1772087 12136013 := bstep (se 3 (by rfl) ⟨2275502, by rfl⟩ : syracuseStep 12136013 = 4551005) B4551005
theorem B1994323 : Blo 1772087 1994323 := bstep (se 1 (by rfl) ⟨1495742, by rfl⟩ : syracuseStep 1994323 = 2991485) B2991485
theorem B1773139 : Blo 1772087 1773139 := bstep (se 1 (by rfl) ⟨1329854, by rfl⟩ : syracuseStep 1773139 = 2659709) B2659709
theorem B1773155 : Blo 1772087 1773155 := bstep (se 1 (by rfl) ⟨1329866, by rfl⟩ : syracuseStep 1773155 = 2659733) B2659733
theorem B5049965 : Blo 1772087 5049965 := bstep (se 3 (by rfl) ⟨946868, by rfl⟩ : syracuseStep 5049965 = 1893737) B1893737
theorem B1773171 : Blo 1772087 1773171 := bstep (se 1 (by rfl) ⟨1329878, by rfl⟩ : syracuseStep 1773171 = 2659757) B2659757
theorem B1773187 : Blo 1772087 1773187 := bstep (se 1 (by rfl) ⟨1329890, by rfl⟩ : syracuseStep 1773187 = 2659781) B2659781
theorem B1773203 : Blo 1772087 1773203 := bstep (se 1 (by rfl) ⟨1329902, by rfl⟩ : syracuseStep 1773203 = 2659805) B2659805
theorem B1773219 : Blo 1772087 1773219 := bstep (se 1 (by rfl) ⟨1329914, by rfl⟩ : syracuseStep 1773219 = 2659829) B2659829
theorem B1773235 : Blo 1772087 1773235 := bstep (se 1 (by rfl) ⟨1329926, by rfl⟩ : syracuseStep 1773235 = 2659853) B2659853
theorem B1773251 : Blo 1772087 1773251 := bstep (se 1 (by rfl) ⟨1329938, by rfl⟩ : syracuseStep 1773251 = 2659877) B2659877
theorem B1773267 : Blo 1772087 1773267 := bstep (se 1 (by rfl) ⟨1329950, by rfl⟩ : syracuseStep 1773267 = 2659901) B2659901
theorem B1994467 : Blo 1772087 1994467 := bstep (se 1 (by rfl) ⟨1495850, by rfl⟩ : syracuseStep 1994467 = 2991701) B2991701
theorem B1773283 : Blo 1772087 1773283 := bstep (se 1 (by rfl) ⟨1329962, by rfl⟩ : syracuseStep 1773283 = 2659925) B2659925
theorem B7188209 : Blo 1772087 7188209 := bstep (se 2 (by rfl) ⟨2695578, by rfl⟩ : syracuseStep 7188209 = 5391157) B5391157
theorem B1773299 : Blo 1772087 1773299 := bstep (se 1 (by rfl) ⟨1329974, by rfl⟩ : syracuseStep 1773299 = 2659949) B2659949
theorem B1773315 : Blo 1772087 1773315 := bstep (se 1 (by rfl) ⟨1329986, by rfl⟩ : syracuseStep 1773315 = 2659973) B2659973
theorem B1773331 : Blo 1772087 1773331 := bstep (se 1 (by rfl) ⟨1329998, by rfl⟩ : syracuseStep 1773331 = 2659997) B2659997
theorem B1773347 : Blo 1772087 1773347 := bstep (se 1 (by rfl) ⟨1330010, by rfl⟩ : syracuseStep 1773347 = 2660021) B2660021
theorem B1773363 : Blo 1772087 1773363 := bstep (se 1 (by rfl) ⟨1330022, by rfl⟩ : syracuseStep 1773363 = 2660045) B2660045
theorem B1773379 : Blo 1772087 1773379 := bstep (se 1 (by rfl) ⟨1330034, by rfl⟩ : syracuseStep 1773379 = 2660069) B2660069
theorem B2658131 : Blo 1772087 2658131 := bstep (se 1 (by rfl) ⟨1993598, by rfl⟩ : syracuseStep 2658131 = 3987197) B3987197
theorem B1773395 : Blo 1772087 1773395 := bstep (se 1 (by rfl) ⟨1330046, by rfl⟩ : syracuseStep 1773395 = 2660093) B2660093
theorem B1773411 : Blo 1772087 1773411 := bstep (se 1 (by rfl) ⟨1330058, by rfl⟩ : syracuseStep 1773411 = 2660117) B2660117
theorem B2658161 : Blo 1772087 2658161 := bstep (se 2 (by rfl) ⟨996810, by rfl⟩ : syracuseStep 2658161 = 1993621) B1993621
theorem B1994611 : Blo 1772087 1994611 := bstep (se 1 (by rfl) ⟨1495958, by rfl⟩ : syracuseStep 1994611 = 2991917) B2991917
theorem B1773427 : Blo 1772087 1773427 := bstep (se 1 (by rfl) ⟨1330070, by rfl⟩ : syracuseStep 1773427 = 2660141) B2660141
theorem B2658179 : Blo 1772087 2658179 := bstep (se 1 (by rfl) ⟨1993634, by rfl⟩ : syracuseStep 2658179 = 3987269) B3987269
theorem B1773443 : Blo 1772087 1773443 := bstep (se 1 (by rfl) ⟨1330082, by rfl⟩ : syracuseStep 1773443 = 2660165) B2660165
theorem B15150989 : Blo 1772087 15150989 := bstep (se 3 (by rfl) ⟨2840810, by rfl⟩ : syracuseStep 15150989 = 5681621) B5681621
theorem B1773459 : Blo 1772087 1773459 := bstep (se 1 (by rfl) ⟨1330094, by rfl⟩ : syracuseStep 1773459 = 2660189) B2660189
theorem B2658209 : Blo 1772087 2658209 := bstep (se 2 (by rfl) ⟨996828, by rfl⟩ : syracuseStep 2658209 = 1993657) B1993657
theorem B1773475 : Blo 1772087 1773475 := bstep (se 1 (by rfl) ⟨1330106, by rfl⟩ : syracuseStep 1773475 = 2660213) B2660213
theorem B2396081 : Blo 1772087 2396081 := bstep (se 2 (by rfl) ⟨898530, by rfl⟩ : syracuseStep 2396081 = 1797061) B1797061
theorem B2658227 : Blo 1772087 2658227 := bstep (se 1 (by rfl) ⟨1993670, by rfl⟩ : syracuseStep 2658227 = 3987341) B3987341
theorem B1773491 : Blo 1772087 1773491 := bstep (se 1 (by rfl) ⟨1330118, by rfl⟩ : syracuseStep 1773491 = 2660237) B2660237
theorem B1773507 : Blo 1772087 1773507 := bstep (se 1 (by rfl) ⟨1330130, by rfl⟩ : syracuseStep 1773507 = 2660261) B2660261
theorem B2658257 : Blo 1772087 2658257 := bstep (se 2 (by rfl) ⟨996846, by rfl⟩ : syracuseStep 2658257 = 1993693) B1993693
theorem B1773523 : Blo 1772087 1773523 := bstep (se 1 (by rfl) ⟨1330142, by rfl⟩ : syracuseStep 1773523 = 2660285) B2660285
theorem B2658275 : Blo 1772087 2658275 := bstep (se 1 (by rfl) ⟨1993706, by rfl⟩ : syracuseStep 2658275 = 3987413) B3987413
theorem B1773539 : Blo 1772087 1773539 := bstep (se 1 (by rfl) ⟨1330154, by rfl⟩ : syracuseStep 1773539 = 2660309) B2660309
theorem B1773555 : Blo 1772087 1773555 := bstep (se 1 (by rfl) ⟨1330166, by rfl⟩ : syracuseStep 1773555 = 2660333) B2660333
theorem B2658305 : Blo 1772087 2658305 := bstep (se 2 (by rfl) ⟨996864, by rfl⟩ : syracuseStep 2658305 = 1993729) B1993729
theorem B1994755 : Blo 1772087 1994755 := bstep (se 1 (by rfl) ⟨1496066, by rfl⟩ : syracuseStep 1994755 = 2992133) B2992133
theorem B1773571 : Blo 1772087 1773571 := bstep (se 1 (by rfl) ⟨1330178, by rfl⟩ : syracuseStep 1773571 = 2660357) B2660357
theorem B2658323 : Blo 1772087 2658323 := bstep (se 1 (by rfl) ⟨1993742, by rfl⟩ : syracuseStep 2658323 = 3987485) B3987485
theorem B1773587 : Blo 1772087 1773587 := bstep (se 1 (by rfl) ⟨1330190, by rfl⟩ : syracuseStep 1773587 = 2660381) B2660381
theorem B6729763 : Blo 1772087 6729763 := bstep (se 1 (by rfl) ⟨5047322, by rfl⟩ : syracuseStep 6729763 = 10094645) B10094645
theorem B1773603 : Blo 1772087 1773603 := bstep (se 1 (by rfl) ⟨1330202, by rfl⟩ : syracuseStep 1773603 = 2660405) B2660405
theorem B2658353 : Blo 1772087 2658353 := bstep (se 2 (by rfl) ⟨996882, by rfl⟩ : syracuseStep 2658353 = 1993765) B1993765
theorem B1773619 : Blo 1772087 1773619 := bstep (se 1 (by rfl) ⟨1330214, by rfl⟩ : syracuseStep 1773619 = 2660429) B2660429
theorem B2658371 : Blo 1772087 2658371 := bstep (se 1 (by rfl) ⟨1993778, by rfl⟩ : syracuseStep 2658371 = 3987557) B3987557
theorem B1773635 : Blo 1772087 1773635 := bstep (se 1 (by rfl) ⟨1330226, by rfl⟩ : syracuseStep 1773635 = 2660453) B2660453
theorem B5984333 : Blo 1772087 5984333 := bstep (se 3 (by rfl) ⟨1122062, by rfl⟩ : syracuseStep 5984333 = 2244125) B2244125
theorem B2560081 : Blo 1772087 2560081 := bstep (se 2 (by rfl) ⟨960030, by rfl⟩ : syracuseStep 2560081 = 1920061) B1920061
theorem B1773651 : Blo 1772087 1773651 := bstep (se 1 (by rfl) ⟨1330238, by rfl⟩ : syracuseStep 1773651 = 2660477) B2660477
theorem B2658401 : Blo 1772087 2658401 := bstep (se 2 (by rfl) ⟨996900, by rfl⟩ : syracuseStep 2658401 = 1993801) B1993801
theorem B1773667 : Blo 1772087 1773667 := bstep (se 1 (by rfl) ⟨1330250, by rfl⟩ : syracuseStep 1773667 = 2660501) B2660501
theorem B2658419 : Blo 1772087 2658419 := bstep (se 1 (by rfl) ⟨1993814, by rfl⟩ : syracuseStep 2658419 = 3987629) B3987629
theorem B1773683 : Blo 1772087 1773683 := bstep (se 1 (by rfl) ⟨1330262, by rfl⟩ : syracuseStep 1773683 = 2660525) B2660525
theorem B5984387 : Blo 1772087 5984387 := bstep (se 1 (by rfl) ⟨4488290, by rfl⟩ : syracuseStep 5984387 = 8976581) B8976581
theorem B1773699 : Blo 1772087 1773699 := bstep (se 1 (by rfl) ⟨1330274, by rfl⟩ : syracuseStep 1773699 = 2660549) B2660549
theorem B5394563 : Blo 1772087 5394563 := bstep (se 1 (by rfl) ⟨4045922, by rfl⟩ : syracuseStep 5394563 = 8091845) B8091845
theorem B2658449 : Blo 1772087 2658449 := bstep (se 2 (by rfl) ⟨996918, by rfl⟩ : syracuseStep 2658449 = 1993837) B1993837
theorem B1994899 : Blo 1772087 1994899 := bstep (se 1 (by rfl) ⟨1496174, by rfl⟩ : syracuseStep 1994899 = 2992349) B2992349
theorem B1773715 : Blo 1772087 1773715 := bstep (se 1 (by rfl) ⟨1330286, by rfl⟩ : syracuseStep 1773715 = 2660573) B2660573
theorem B2658467 : Blo 1772087 2658467 := bstep (se 1 (by rfl) ⟨1993850, by rfl⟩ : syracuseStep 2658467 = 3987701) B3987701
theorem B1773731 : Blo 1772087 1773731 := bstep (se 1 (by rfl) ⟨1330298, by rfl⟩ : syracuseStep 1773731 = 2660597) B2660597
theorem B1773747 : Blo 1772087 1773747 := bstep (se 1 (by rfl) ⟨1330310, by rfl⟩ : syracuseStep 1773747 = 2660621) B2660621
theorem B2658497 : Blo 1772087 2658497 := bstep (se 2 (by rfl) ⟨996936, by rfl⟩ : syracuseStep 2658497 = 1993873) B1993873
theorem B1773763 : Blo 1772087 1773763 := bstep (se 1 (by rfl) ⟨1330322, by rfl⟩ : syracuseStep 1773763 = 2660645) B2660645
theorem B2658515 : Blo 1772087 2658515 := bstep (se 1 (by rfl) ⟨1993886, by rfl⟩ : syracuseStep 2658515 = 3987773) B3987773
theorem B1773779 : Blo 1772087 1773779 := bstep (se 1 (by rfl) ⟨1330334, by rfl⟩ : syracuseStep 1773779 = 2660669) B2660669
theorem B1773795 : Blo 1772087 1773795 := bstep (se 1 (by rfl) ⟨1330346, by rfl⟩ : syracuseStep 1773795 = 2660693) B2660693
theorem B2658545 : Blo 1772087 2658545 := bstep (se 2 (by rfl) ⟨996954, by rfl⟩ : syracuseStep 2658545 = 1993909) B1993909
theorem B1773811 : Blo 1772087 1773811 := bstep (se 1 (by rfl) ⟨1330358, by rfl⟩ : syracuseStep 1773811 = 2660717) B2660717
theorem B2658563 : Blo 1772087 2658563 := bstep (se 1 (by rfl) ⟨1993922, by rfl⟩ : syracuseStep 2658563 = 3987845) B3987845
theorem B1773827 : Blo 1772087 1773827 := bstep (se 1 (by rfl) ⟨1330370, by rfl⟩ : syracuseStep 1773827 = 2660741) B2660741
theorem B1773843 : Blo 1772087 1773843 := bstep (se 1 (by rfl) ⟨1330382, by rfl⟩ : syracuseStep 1773843 = 2660765) B2660765
theorem B2658593 : Blo 1772087 2658593 := bstep (se 2 (by rfl) ⟨996972, by rfl⟩ : syracuseStep 2658593 = 1993945) B1993945
theorem B1995043 : Blo 1772087 1995043 := bstep (se 1 (by rfl) ⟨1496282, by rfl⟩ : syracuseStep 1995043 = 2992565) B2992565
theorem B1773859 : Blo 1772087 1773859 := bstep (se 1 (by rfl) ⟨1330394, by rfl⟩ : syracuseStep 1773859 = 2660789) B2660789
theorem B2658611 : Blo 1772087 2658611 := bstep (se 1 (by rfl) ⟨1993958, by rfl⟩ : syracuseStep 2658611 = 3987917) B3987917
theorem B1773875 : Blo 1772087 1773875 := bstep (se 1 (by rfl) ⟨1330406, by rfl⟩ : syracuseStep 1773875 = 2660813) B2660813
theorem B1773891 : Blo 1772087 1773891 := bstep (se 1 (by rfl) ⟨1330418, by rfl⟩ : syracuseStep 1773891 = 2660837) B2660837
theorem B2658641 : Blo 1772087 2658641 := bstep (se 2 (by rfl) ⟨996990, by rfl⟩ : syracuseStep 2658641 = 1993981) B1993981
theorem B1773907 : Blo 1772087 1773907 := bstep (se 1 (by rfl) ⟨1330430, by rfl⟩ : syracuseStep 1773907 = 2660861) B2660861
theorem B2658659 : Blo 1772087 2658659 := bstep (se 1 (by rfl) ⟨1993994, by rfl⟩ : syracuseStep 2658659 = 3987989) B3987989
theorem B1773923 : Blo 1772087 1773923 := bstep (se 1 (by rfl) ⟨1330442, by rfl⟩ : syracuseStep 1773923 = 2660885) B2660885
theorem B1773939 : Blo 1772087 1773939 := bstep (se 1 (by rfl) ⟨1330454, by rfl⟩ : syracuseStep 1773939 = 2660909) B2660909
theorem B2658689 : Blo 1772087 2658689 := bstep (se 2 (by rfl) ⟨997008, by rfl⟩ : syracuseStep 2658689 = 1994017) B1994017
theorem B1773955 : Blo 1772087 1773955 := bstep (se 1 (by rfl) ⟨1330466, by rfl⟩ : syracuseStep 1773955 = 2660933) B2660933
theorem B5984657 : Blo 1772087 5984657 := bstep (se 2 (by rfl) ⟨2244246, by rfl⟩ : syracuseStep 5984657 = 4488493) B4488493
theorem B2658707 : Blo 1772087 2658707 := bstep (se 1 (by rfl) ⟨1994030, by rfl⟩ : syracuseStep 2658707 = 3988061) B3988061
theorem B1773971 : Blo 1772087 1773971 := bstep (se 1 (by rfl) ⟨1330478, by rfl⟩ : syracuseStep 1773971 = 2660957) B2660957
theorem B1773987 : Blo 1772087 1773987 := bstep (se 1 (by rfl) ⟨1330490, by rfl⟩ : syracuseStep 1773987 = 2660981) B2660981
theorem B2658737 : Blo 1772087 2658737 := bstep (se 2 (by rfl) ⟨997026, by rfl⟩ : syracuseStep 2658737 = 1994053) B1994053
theorem B1995187 : Blo 1772087 1995187 := bstep (se 1 (by rfl) ⟨1496390, by rfl⟩ : syracuseStep 1995187 = 2992781) B2992781
theorem B1774003 : Blo 1772087 1774003 := bstep (se 1 (by rfl) ⟨1330502, by rfl⟩ : syracuseStep 1774003 = 2661005) B2661005
theorem B2838979 : Blo 1772087 2838979 := bstep (se 1 (by rfl) ⟨2129234, by rfl⟩ : syracuseStep 2838979 = 4258469) B4258469
theorem B2658755 : Blo 1772087 2658755 := bstep (se 1 (by rfl) ⟨1994066, by rfl⟩ : syracuseStep 2658755 = 3988133) B3988133
theorem B1774019 : Blo 1772087 1774019 := bstep (se 1 (by rfl) ⟨1330514, by rfl⟩ : syracuseStep 1774019 = 2661029) B2661029
theorem B1774035 : Blo 1772087 1774035 := bstep (se 1 (by rfl) ⟨1330526, by rfl⟩ : syracuseStep 1774035 = 2661053) B2661053
theorem B2658785 : Blo 1772087 2658785 := bstep (se 2 (by rfl) ⟨997044, by rfl⟩ : syracuseStep 2658785 = 1994089) B1994089
theorem B1774051 : Blo 1772087 1774051 := bstep (se 1 (by rfl) ⟨1330538, by rfl⟩ : syracuseStep 1774051 = 2661077) B2661077
theorem B2658803 : Blo 1772087 2658803 := bstep (se 1 (by rfl) ⟨1994102, by rfl⟩ : syracuseStep 2658803 = 3988205) B3988205
theorem B1774067 : Blo 1772087 1774067 := bstep (se 1 (by rfl) ⟨1330550, by rfl⟩ : syracuseStep 1774067 = 2661101) B2661101
theorem B2839043 : Blo 1772087 2839043 := bstep (se 1 (by rfl) ⟨2129282, by rfl⟩ : syracuseStep 2839043 = 4258565) B4258565
theorem B1774083 : Blo 1772087 1774083 := bstep (se 1 (by rfl) ⟨1330562, by rfl⟩ : syracuseStep 1774083 = 2661125) B2661125
theorem B2658833 : Blo 1772087 2658833 := bstep (se 2 (by rfl) ⟨997062, by rfl⟩ : syracuseStep 2658833 = 1994125) B1994125
theorem B2658851 : Blo 1772087 2658851 := bstep (se 1 (by rfl) ⟨1994138, by rfl⟩ : syracuseStep 2658851 = 3988277) B3988277
theorem B2658881 : Blo 1772087 2658881 := bstep (se 2 (by rfl) ⟨997080, by rfl⟩ : syracuseStep 2658881 = 1994161) B1994161
theorem B1995331 : Blo 1772087 1995331 := bstep (se 1 (by rfl) ⟨1496498, by rfl⟩ : syracuseStep 1995331 = 2992997) B2992997
theorem B5050957 : Blo 1772087 5050957 := bstep (se 3 (by rfl) ⟨947054, by rfl⟩ : syracuseStep 5050957 = 1894109) B1894109
theorem B2658899 : Blo 1772087 2658899 := bstep (se 1 (by rfl) ⟨1994174, by rfl⟩ : syracuseStep 2658899 = 3988349) B3988349
theorem B2658929 : Blo 1772087 2658929 := bstep (se 2 (by rfl) ⟨997098, by rfl⟩ : syracuseStep 2658929 = 1994197) B1994197
theorem B8974961 : Blo 1772087 8974961 := bstep (se 2 (by rfl) ⟨3365610, by rfl⟩ : syracuseStep 8974961 = 6731221) B6731221
theorem B5116547 : Blo 1772087 5116547 := bstep (se 1 (by rfl) ⟨3837410, by rfl⟩ : syracuseStep 5116547 = 7674821) B7674821
theorem B2658947 : Blo 1772087 2658947 := bstep (se 1 (by rfl) ⟨1994210, by rfl⟩ : syracuseStep 2658947 = 3988421) B3988421
theorem B2658977 : Blo 1772087 2658977 := bstep (se 2 (by rfl) ⟨997116, by rfl⟩ : syracuseStep 2658977 = 1994233) B1994233
theorem B2658995 : Blo 1772087 2658995 := bstep (se 1 (by rfl) ⟨1994246, by rfl⟩ : syracuseStep 2658995 = 3988493) B3988493
theorem B2880193 : Blo 1772087 2880193 := bstep (se 2 (by rfl) ⟨1080072, by rfl⟩ : syracuseStep 2880193 = 2160145) B2160145
theorem B2659025 : Blo 1772087 2659025 := bstep (se 2 (by rfl) ⟨997134, by rfl⟩ : syracuseStep 2659025 = 1994269) B1994269
theorem B1995475 : Blo 1772087 1995475 := bstep (se 1 (by rfl) ⟨1496606, by rfl⟩ : syracuseStep 1995475 = 2993213) B2993213
theorem B2659043 : Blo 1772087 2659043 := bstep (se 1 (by rfl) ⟨1994282, by rfl⟩ : syracuseStep 2659043 = 3988565) B3988565
theorem B2659073 : Blo 1772087 2659073 := bstep (se 2 (by rfl) ⟨997152, by rfl⟩ : syracuseStep 2659073 = 1994305) B1994305
theorem B2659091 : Blo 1772087 2659091 := bstep (se 1 (by rfl) ⟨1994318, by rfl⟩ : syracuseStep 2659091 = 3988637) B3988637
theorem B2659121 : Blo 1772087 2659121 := bstep (se 2 (by rfl) ⟨997170, by rfl⟩ : syracuseStep 2659121 = 1994341) B1994341
theorem B2659139 : Blo 1772087 2659139 := bstep (se 1 (by rfl) ⟨1994354, by rfl⟩ : syracuseStep 2659139 = 3988709) B3988709
theorem B2659169 : Blo 1772087 2659169 := bstep (se 2 (by rfl) ⟨997188, by rfl⟩ : syracuseStep 2659169 = 1994377) B1994377
theorem B1995619 : Blo 1772087 1995619 := bstep (se 1 (by rfl) ⟨1496714, by rfl⟩ : syracuseStep 1995619 = 2993429) B2993429
theorem B10236785 : Blo 1772087 10236785 := bstep (se 2 (by rfl) ⟨3838794, by rfl⟩ : syracuseStep 10236785 = 7677589) B7677589
theorem B2659187 : Blo 1772087 2659187 := bstep (se 1 (by rfl) ⟨1994390, by rfl⟩ : syracuseStep 2659187 = 3988781) B3988781
theorem B2659217 : Blo 1772087 2659217 := bstep (se 2 (by rfl) ⟨997206, by rfl⟩ : syracuseStep 2659217 = 1994413) B1994413
theorem B2659235 : Blo 1772087 2659235 := bstep (se 1 (by rfl) ⟨1994426, by rfl⟩ : syracuseStep 2659235 = 3988853) B3988853
theorem B5985197 : Blo 1772087 5985197 := bstep (se 3 (by rfl) ⟨1122224, by rfl⟩ : syracuseStep 5985197 = 2244449) B2244449
theorem B2659265 : Blo 1772087 2659265 := bstep (se 2 (by rfl) ⟨997224, by rfl⟩ : syracuseStep 2659265 = 1994449) B1994449
theorem B2659283 : Blo 1772087 2659283 := bstep (se 1 (by rfl) ⟨1994462, by rfl⟩ : syracuseStep 2659283 = 3988925) B3988925
theorem B5985251 : Blo 1772087 5985251 := bstep (se 1 (by rfl) ⟨4488938, by rfl⟩ : syracuseStep 5985251 = 8977877) B8977877
theorem B2659313 : Blo 1772087 2659313 := bstep (se 2 (by rfl) ⟨997242, by rfl⟩ : syracuseStep 2659313 = 1994485) B1994485
theorem B1995763 : Blo 1772087 1995763 := bstep (se 1 (by rfl) ⟨1496822, by rfl⟩ : syracuseStep 1995763 = 2993645) B2993645
theorem B2659331 : Blo 1772087 2659331 := bstep (se 1 (by rfl) ⟨1994498, by rfl⟩ : syracuseStep 2659331 = 3988997) B3988997
theorem B3413009 : Blo 1772087 3413009 := bstep (se 2 (by rfl) ⟨1279878, by rfl⟩ : syracuseStep 3413009 = 2559757) B2559757
theorem B2659361 : Blo 1772087 2659361 := bstep (se 2 (by rfl) ⟨997260, by rfl⟩ : syracuseStep 2659361 = 1994521) B1994521
theorem B2659379 : Blo 1772087 2659379 := bstep (se 1 (by rfl) ⟨1994534, by rfl⟩ : syracuseStep 2659379 = 3989069) B3989069
theorem B4486225 : Blo 1772087 4486225 := bstep (se 2 (by rfl) ⟨1682334, by rfl⟩ : syracuseStep 4486225 = 3364669) B3364669
theorem B2659409 : Blo 1772087 2659409 := bstep (se 2 (by rfl) ⟨997278, by rfl⟩ : syracuseStep 2659409 = 1994557) B1994557
theorem B2659427 : Blo 1772087 2659427 := bstep (se 1 (by rfl) ⟨1994570, by rfl⟩ : syracuseStep 2659427 = 3989141) B3989141
theorem B9589859 : Blo 1772087 9589859 := bstep (se 1 (by rfl) ⟨7192394, by rfl⟩ : syracuseStep 9589859 = 14384789) B14384789
theorem B2659457 : Blo 1772087 2659457 := bstep (se 2 (by rfl) ⟨997296, by rfl⟩ : syracuseStep 2659457 = 1994593) B1994593
theorem B2659475 : Blo 1772087 2659475 := bstep (se 1 (by rfl) ⟨1994606, by rfl⟩ : syracuseStep 2659475 = 3989213) B3989213
theorem B2659505 : Blo 1772087 2659505 := bstep (se 2 (by rfl) ⟨997314, by rfl⟩ : syracuseStep 2659505 = 1994629) B1994629
theorem B2659523 : Blo 1772087 2659523 := bstep (se 1 (by rfl) ⟨1994642, by rfl⟩ : syracuseStep 2659523 = 3989285) B3989285
theorem B2659553 : Blo 1772087 2659553 := bstep (se 2 (by rfl) ⟨997332, by rfl⟩ : syracuseStep 2659553 = 1994665) B1994665
theorem B5985521 : Blo 1772087 5985521 := bstep (se 2 (by rfl) ⟨2244570, by rfl⟩ : syracuseStep 5985521 = 4489141) B4489141
theorem B2659571 : Blo 1772087 2659571 := bstep (se 1 (by rfl) ⟨1994678, by rfl⟩ : syracuseStep 2659571 = 3989357) B3989357
theorem B2659601 : Blo 1772087 2659601 := bstep (se 2 (by rfl) ⟨997350, by rfl⟩ : syracuseStep 2659601 = 1994701) B1994701
theorem B2659619 : Blo 1772087 2659619 := bstep (se 1 (by rfl) ⟨1994714, by rfl⟩ : syracuseStep 2659619 = 3989429) B3989429
theorem B2659649 : Blo 1772087 2659649 := bstep (se 2 (by rfl) ⟨997368, by rfl⟩ : syracuseStep 2659649 = 1994737) B1994737
theorem B2659667 : Blo 1772087 2659667 := bstep (se 1 (by rfl) ⟨1994750, by rfl⟩ : syracuseStep 2659667 = 3989501) B3989501
theorem B4486499 : Blo 1772087 4486499 := bstep (se 1 (by rfl) ⟨3364874, by rfl⟩ : syracuseStep 4486499 = 6729749) B6729749
theorem B2659697 : Blo 1772087 2659697 := bstep (se 2 (by rfl) ⟨997386, by rfl⟩ : syracuseStep 2659697 = 1994773) B1994773
theorem B5682545 : Blo 1772087 5682545 := bstep (se 2 (by rfl) ⟨2130954, by rfl⟩ : syracuseStep 5682545 = 4261909) B4261909
theorem B2659715 : Blo 1772087 2659715 := bstep (se 1 (by rfl) ⟨1994786, by rfl⟩ : syracuseStep 2659715 = 3989573) B3989573
theorem B2659745 : Blo 1772087 2659745 := bstep (se 2 (by rfl) ⟨997404, by rfl⟩ : syracuseStep 2659745 = 1994809) B1994809
theorem B2659763 : Blo 1772087 2659763 := bstep (se 1 (by rfl) ⟨1994822, by rfl⟩ : syracuseStep 2659763 = 3989645) B3989645
theorem B2840017 : Blo 1772087 2840017 := bstep (se 2 (by rfl) ⟨1065006, by rfl⟩ : syracuseStep 2840017 = 2130013) B2130013
theorem B2659793 : Blo 1772087 2659793 := bstep (se 2 (by rfl) ⟨997422, by rfl⟩ : syracuseStep 2659793 = 1994845) B1994845
theorem B2659811 : Blo 1772087 2659811 := bstep (se 1 (by rfl) ⟨1994858, by rfl⟩ : syracuseStep 2659811 = 3989717) B3989717
theorem B2733553 : Blo 1772087 2733553 := bstep (se 2 (by rfl) ⟨1025082, by rfl⟩ : syracuseStep 2733553 = 2050165) B2050165
theorem B2659841 : Blo 1772087 2659841 := bstep (se 2 (by rfl) ⟨997440, by rfl⟩ : syracuseStep 2659841 = 1994881) B1994881
theorem B11359757 : Blo 1772087 11359757 := bstep (se 3 (by rfl) ⟨2129954, by rfl⟩ : syracuseStep 11359757 = 4259909) B4259909
theorem B2659859 : Blo 1772087 2659859 := bstep (se 1 (by rfl) ⟨1994894, by rfl⟩ : syracuseStep 2659859 = 3989789) B3989789
theorem B4486691 : Blo 1772087 4486691 := bstep (se 1 (by rfl) ⟨3365018, by rfl⟩ : syracuseStep 4486691 = 6730037) B6730037
theorem B2659889 : Blo 1772087 2659889 := bstep (se 2 (by rfl) ⟨997458, by rfl⟩ : syracuseStep 2659889 = 1994917) B1994917
theorem B5682737 : Blo 1772087 5682737 := bstep (se 2 (by rfl) ⟨2131026, by rfl⟩ : syracuseStep 5682737 = 4262053) B4262053
theorem B2659907 : Blo 1772087 2659907 := bstep (se 1 (by rfl) ⟨1994930, by rfl⟩ : syracuseStep 2659907 = 3989861) B3989861
theorem B2659937 : Blo 1772087 2659937 := bstep (se 2 (by rfl) ⟨997476, by rfl⟩ : syracuseStep 2659937 = 1994953) B1994953
theorem B23033443 : Blo 1772087 23033443 := bstep (se 1 (by rfl) ⟨17275082, by rfl⟩ : syracuseStep 23033443 = 34550165) B34550165
theorem B10237553 : Blo 1772087 10237553 := bstep (se 2 (by rfl) ⟨3839082, by rfl⟩ : syracuseStep 10237553 = 7678165) B7678165
theorem B2659955 : Blo 1772087 2659955 := bstep (se 1 (by rfl) ⟨1994966, by rfl⟩ : syracuseStep 2659955 = 3989933) B3989933
theorem B22730381 : Blo 1772087 22730381 := bstep (se 3 (by rfl) ⟨4261946, by rfl⟩ : syracuseStep 22730381 = 8523893) B8523893
theorem B2659985 : Blo 1772087 2659985 := bstep (se 2 (by rfl) ⟨997494, by rfl⟩ : syracuseStep 2659985 = 1994989) B1994989
theorem B2660003 : Blo 1772087 2660003 := bstep (se 1 (by rfl) ⟨1995002, by rfl⟩ : syracuseStep 2660003 = 3990005) B3990005
theorem B2660033 : Blo 1772087 2660033 := bstep (se 2 (by rfl) ⟨997512, by rfl⟩ : syracuseStep 2660033 = 1995025) B1995025
theorem B2840273 : Blo 1772087 2840273 := bstep (se 2 (by rfl) ⟨1065102, by rfl⟩ : syracuseStep 2840273 = 2130205) B2130205
theorem B2660051 : Blo 1772087 2660051 := bstep (se 1 (by rfl) ⟨1995038, by rfl⟩ : syracuseStep 2660051 = 3990077) B3990077
theorem B2660081 : Blo 1772087 2660081 := bstep (se 2 (by rfl) ⟨997530, by rfl⟩ : syracuseStep 2660081 = 1995061) B1995061
theorem B2660099 : Blo 1772087 2660099 := bstep (se 1 (by rfl) ⟨1995074, by rfl⟩ : syracuseStep 2660099 = 3990149) B3990149
theorem B5986061 : Blo 1772087 5986061 := bstep (se 3 (by rfl) ⟨1122386, by rfl⟩ : syracuseStep 5986061 = 2244773) B2244773
theorem B153409301 : Blo 1772087 153409301 := bstep (se 6 (by rfl) ⟨3595530, by rfl⟩ : syracuseStep 153409301 = 7191061) B7191061
theorem B2660129 : Blo 1772087 2660129 := bstep (se 2 (by rfl) ⟨997548, by rfl⟩ : syracuseStep 2660129 = 1995097) B1995097
theorem B2660147 : Blo 1772087 2660147 := bstep (se 1 (by rfl) ⟨1995110, by rfl⟩ : syracuseStep 2660147 = 3990221) B3990221
theorem B5986115 : Blo 1772087 5986115 := bstep (se 1 (by rfl) ⟨4489586, by rfl⟩ : syracuseStep 5986115 = 8979173) B8979173
theorem B6068035 : Blo 1772087 6068035 := bstep (se 1 (by rfl) ⟨4551026, by rfl⟩ : syracuseStep 6068035 = 9102053) B9102053
theorem B2660177 : Blo 1772087 2660177 := bstep (se 2 (by rfl) ⟨997566, by rfl⟩ : syracuseStep 2660177 = 1995133) B1995133
theorem B2660195 : Blo 1772087 2660195 := bstep (se 1 (by rfl) ⟨1995146, by rfl⟩ : syracuseStep 2660195 = 3990293) B3990293
theorem B2660225 : Blo 1772087 2660225 := bstep (se 2 (by rfl) ⟨997584, by rfl⟩ : syracuseStep 2660225 = 1995169) B1995169
theorem B3364753 : Blo 1772087 3364753 := bstep (se 2 (by rfl) ⟨1261782, by rfl⟩ : syracuseStep 3364753 = 2523565) B2523565
theorem B2840465 : Blo 1772087 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B2660243 : Blo 1772087 2660243 := bstep (se 1 (by rfl) ⟨1995182, by rfl⟩ : syracuseStep 2660243 = 3990365) B3990365
theorem B3987377 : Blo 1772087 3987377 := bstep (se 2 (by rfl) ⟨1495266, by rfl⟩ : syracuseStep 3987377 = 2990533) B2990533
theorem B2660273 : Blo 1772087 2660273 := bstep (se 2 (by rfl) ⟨997602, by rfl⟩ : syracuseStep 2660273 = 1995205) B1995205
theorem B3987395 : Blo 1772087 3987395 := bstep (se 1 (by rfl) ⟨2990546, by rfl⟩ : syracuseStep 3987395 = 5981093) B5981093
theorem B2660291 : Blo 1772087 2660291 := bstep (se 1 (by rfl) ⟨1995218, by rfl⟩ : syracuseStep 2660291 = 3990437) B3990437
theorem B2660321 : Blo 1772087 2660321 := bstep (se 2 (by rfl) ⟨997620, by rfl⟩ : syracuseStep 2660321 = 1995241) B1995241
theorem B2660339 : Blo 1772087 2660339 := bstep (se 1 (by rfl) ⟨1995254, by rfl⟩ : syracuseStep 2660339 = 3990509) B3990509
theorem B10098701 : Blo 1772087 10098701 := bstep (se 3 (by rfl) ⟨1893506, by rfl⟩ : syracuseStep 10098701 = 3787013) B3787013
theorem B2660369 : Blo 1772087 2660369 := bstep (se 2 (by rfl) ⟨997638, by rfl⟩ : syracuseStep 2660369 = 1995277) B1995277
theorem B8976419 : Blo 1772087 8976419 := bstep (se 1 (by rfl) ⟨6732314, by rfl⟩ : syracuseStep 8976419 = 13464629) B13464629
theorem B2660387 : Blo 1772087 2660387 := bstep (se 1 (by rfl) ⟨1995290, by rfl⟩ : syracuseStep 2660387 = 3990581) B3990581
theorem B2660417 : Blo 1772087 2660417 := bstep (se 2 (by rfl) ⟨997656, by rfl⟩ : syracuseStep 2660417 = 1995313) B1995313
theorem B5986385 : Blo 1772087 5986385 := bstep (se 2 (by rfl) ⟨2244894, by rfl⟩ : syracuseStep 5986385 = 4489789) B4489789
theorem B2660435 : Blo 1772087 2660435 := bstep (se 1 (by rfl) ⟨1995326, by rfl⟩ : syracuseStep 2660435 = 3990653) B3990653
theorem B2660465 : Blo 1772087 2660465 := bstep (se 2 (by rfl) ⟨997674, by rfl⟩ : syracuseStep 2660465 = 1995349) B1995349
theorem B2660483 : Blo 1772087 2660483 := bstep (se 1 (by rfl) ⟨1995362, by rfl⟩ : syracuseStep 2660483 = 3990725) B3990725
theorem B2660513 : Blo 1772087 2660513 := bstep (se 2 (by rfl) ⟨997692, by rfl⟩ : syracuseStep 2660513 = 1995385) B1995385
theorem B2660531 : Blo 1772087 2660531 := bstep (se 1 (by rfl) ⟨1995398, by rfl⟩ : syracuseStep 2660531 = 3990797) B3990797
theorem B6731981 : Blo 1772087 6731981 := bstep (se 3 (by rfl) ⟨1262246, by rfl⟩ : syracuseStep 6731981 = 2524493) B2524493
theorem B3987665 : Blo 1772087 3987665 := bstep (se 2 (by rfl) ⟨1495374, by rfl⟩ : syracuseStep 3987665 = 2990749) B2990749
theorem B2660561 : Blo 1772087 2660561 := bstep (se 2 (by rfl) ⟨997710, by rfl⟩ : syracuseStep 2660561 = 1995421) B1995421
theorem B3987683 : Blo 1772087 3987683 := bstep (se 1 (by rfl) ⟨2990762, by rfl⟩ : syracuseStep 3987683 = 5981525) B5981525
theorem B2660579 : Blo 1772087 2660579 := bstep (se 1 (by rfl) ⟨1995434, by rfl⟩ : syracuseStep 2660579 = 3990869) B3990869
theorem B2660609 : Blo 1772087 2660609 := bstep (se 2 (by rfl) ⟨997728, by rfl⟩ : syracuseStep 2660609 = 1995457) B1995457
theorem B2242819 : Blo 1772087 2242819 := bstep (se 1 (by rfl) ⟨1682114, by rfl⟩ : syracuseStep 2242819 = 3364229) B3364229
theorem B2660627 : Blo 1772087 2660627 := bstep (se 1 (by rfl) ⟨1995470, by rfl⟩ : syracuseStep 2660627 = 3990941) B3990941
theorem B3365155 : Blo 1772087 3365155 := bstep (se 1 (by rfl) ⟨2523866, by rfl⟩ : syracuseStep 3365155 = 5047733) B5047733
theorem B4790573 : Blo 1772087 4790573 := bstep (se 3 (by rfl) ⟨898232, by rfl⟩ : syracuseStep 4790573 = 1796465) B1796465
theorem B2660657 : Blo 1772087 2660657 := bstep (se 2 (by rfl) ⟨997746, by rfl⟩ : syracuseStep 2660657 = 1995493) B1995493
theorem B2660675 : Blo 1772087 2660675 := bstep (se 1 (by rfl) ⟨1995506, by rfl⟩ : syracuseStep 2660675 = 3991013) B3991013
theorem B3365201 : Blo 1772087 3365201 := bstep (se 2 (by rfl) ⟨1261950, by rfl⟩ : syracuseStep 3365201 = 2523901) B2523901
theorem B2660705 : Blo 1772087 2660705 := bstep (se 2 (by rfl) ⟨997764, by rfl⟩ : syracuseStep 2660705 = 1995529) B1995529
theorem B2660723 : Blo 1772087 2660723 := bstep (se 1 (by rfl) ⟨1995542, by rfl⟩ : syracuseStep 2660723 = 3991085) B3991085
theorem B2660753 : Blo 1772087 2660753 := bstep (se 2 (by rfl) ⟨997782, by rfl⟩ : syracuseStep 2660753 = 1995565) B1995565
theorem B2660771 : Blo 1772087 2660771 := bstep (se 1 (by rfl) ⟨1995578, by rfl⟩ : syracuseStep 2660771 = 3991157) B3991157
theorem B2660801 : Blo 1772087 2660801 := bstep (se 2 (by rfl) ⟨997800, by rfl⟩ : syracuseStep 2660801 = 1995601) B1995601
theorem B4487633 : Blo 1772087 4487633 := bstep (se 2 (by rfl) ⟨1682862, by rfl⟩ : syracuseStep 4487633 = 3365725) B3365725
theorem B2660819 : Blo 1772087 2660819 := bstep (se 1 (by rfl) ⟨1995614, by rfl⟩ : syracuseStep 2660819 = 3991229) B3991229
theorem B4790755 : Blo 1772087 4790755 := bstep (se 1 (by rfl) ⟨3593066, by rfl⟩ : syracuseStep 4790755 = 7186133) B7186133
theorem B3987953 : Blo 1772087 3987953 := bstep (se 2 (by rfl) ⟨1495482, by rfl⟩ : syracuseStep 3987953 = 2990965) B2990965
theorem B2660849 : Blo 1772087 2660849 := bstep (se 2 (by rfl) ⟨997818, by rfl⟩ : syracuseStep 2660849 = 1995637) B1995637
theorem B3987971 : Blo 1772087 3987971 := bstep (se 1 (by rfl) ⟨2990978, by rfl⟩ : syracuseStep 3987971 = 5981957) B5981957
theorem B4487683 : Blo 1772087 4487683 := bstep (se 1 (by rfl) ⟨3365762, by rfl⟩ : syracuseStep 4487683 = 6731525) B6731525
theorem B2660867 : Blo 1772087 2660867 := bstep (se 1 (by rfl) ⟨1995650, by rfl⟩ : syracuseStep 2660867 = 3991301) B3991301
theorem B2660897 : Blo 1772087 2660897 := bstep (se 2 (by rfl) ⟨997836, by rfl⟩ : syracuseStep 2660897 = 1995673) B1995673
theorem B2660915 : Blo 1772087 2660915 := bstep (se 1 (by rfl) ⟨1995686, by rfl⟩ : syracuseStep 2660915 = 3991373) B3991373
theorem B2660945 : Blo 1772087 2660945 := bstep (se 2 (by rfl) ⟨997854, by rfl⟩ : syracuseStep 2660945 = 1995709) B1995709
theorem B7576163 : Blo 1772087 7576163 := bstep (se 1 (by rfl) ⟨5682122, by rfl⟩ : syracuseStep 7576163 = 11364245) B11364245
theorem B2660963 : Blo 1772087 2660963 := bstep (se 1 (by rfl) ⟨1995722, by rfl⟩ : syracuseStep 2660963 = 3991445) B3991445
theorem B5986925 : Blo 1772087 5986925 := bstep (se 3 (by rfl) ⟨1122548, by rfl⟩ : syracuseStep 5986925 = 2245097) B2245097
theorem B3365489 : Blo 1772087 3365489 := bstep (se 2 (by rfl) ⟨1262058, by rfl⟩ : syracuseStep 3365489 = 2524117) B2524117
theorem B2660993 : Blo 1772087 2660993 := bstep (se 2 (by rfl) ⟨997872, by rfl⟩ : syracuseStep 2660993 = 1995745) B1995745
theorem B3594883 : Blo 1772087 3594883 := bstep (se 1 (by rfl) ⟨2696162, by rfl⟩ : syracuseStep 3594883 = 5392325) B5392325
theorem B4487825 : Blo 1772087 4487825 := bstep (se 2 (by rfl) ⟨1682934, by rfl⟩ : syracuseStep 4487825 = 3365869) B3365869
theorem B2661011 : Blo 1772087 2661011 := bstep (se 1 (by rfl) ⟨1995758, by rfl⟩ : syracuseStep 2661011 = 3991517) B3991517
theorem B5986979 : Blo 1772087 5986979 := bstep (se 1 (by rfl) ⟨4490234, by rfl⟩ : syracuseStep 5986979 = 8980469) B8980469
theorem B2661041 : Blo 1772087 2661041 := bstep (se 2 (by rfl) ⟨997890, by rfl⟩ : syracuseStep 2661041 = 1995781) B1995781
theorem B2661059 : Blo 1772087 2661059 := bstep (se 1 (by rfl) ⟨1995794, by rfl⟩ : syracuseStep 2661059 = 3991589) B3991589
theorem B2661089 : Blo 1772087 2661089 := bstep (se 2 (by rfl) ⟨997908, by rfl⟩ : syracuseStep 2661089 = 1995817) B1995817
theorem B2243315 : Blo 1772087 2243315 := bstep (se 1 (by rfl) ⟨1682486, by rfl⟩ : syracuseStep 2243315 = 3364973) B3364973
theorem B2661107 : Blo 1772087 2661107 := bstep (se 1 (by rfl) ⟨1995830, by rfl⟩ : syracuseStep 2661107 = 3991661) B3991661
theorem B3988241 : Blo 1772087 3988241 := bstep (se 2 (by rfl) ⟨1495590, by rfl⟩ : syracuseStep 3988241 = 2991181) B2991181
theorem B3988259 : Blo 1772087 3988259 := bstep (se 1 (by rfl) ⟨2991194, by rfl⟩ : syracuseStep 3988259 = 5982389) B5982389
theorem B8977229 : Blo 1772087 8977229 := bstep (se 3 (by rfl) ⟨1683230, by rfl⟩ : syracuseStep 8977229 = 3366461) B3366461
theorem B5987249 : Blo 1772087 5987249 := bstep (se 2 (by rfl) ⟨2245218, by rfl⟩ : syracuseStep 5987249 = 4490437) B4490437
theorem B3988529 : Blo 1772087 3988529 := bstep (se 2 (by rfl) ⟨1495698, by rfl⟩ : syracuseStep 3988529 = 2991397) B2991397
theorem B3988547 : Blo 1772087 3988547 := bstep (se 1 (by rfl) ⟨2991410, by rfl⟩ : syracuseStep 3988547 = 5982821) B5982821
theorem B20200589 : Blo 1772087 20200589 := bstep (se 3 (by rfl) ⟨3787610, by rfl⟩ : syracuseStep 20200589 = 7575221) B7575221
theorem B4791619 : Blo 1772087 4791619 := bstep (se 1 (by rfl) ⟨3593714, by rfl⟩ : syracuseStep 4791619 = 7187429) B7187429
theorem B3366211 : Blo 1772087 3366211 := bstep (se 1 (by rfl) ⟨2524658, by rfl⟩ : syracuseStep 3366211 = 5049317) B5049317
theorem B3988817 : Blo 1772087 3988817 := bstep (se 2 (by rfl) ⟨1495806, by rfl⟩ : syracuseStep 3988817 = 2991613) B2991613
theorem B3988835 : Blo 1772087 3988835 := bstep (se 1 (by rfl) ⟨2991626, by rfl⟩ : syracuseStep 3988835 = 5983253) B5983253
theorem B2244019 : Blo 1772087 2244019 := bstep (se 1 (by rfl) ⟨1683014, by rfl⟩ : syracuseStep 2244019 = 3366029) B3366029
theorem B2022835 : Blo 1772087 2022835 := bstep (se 1 (by rfl) ⟨1517126, by rfl⟩ : syracuseStep 2022835 = 3034253) B3034253
theorem B4791793 : Blo 1772087 4791793 := bstep (se 2 (by rfl) ⟨1796922, by rfl⟩ : syracuseStep 4791793 = 3593845) B3593845
theorem B2244115 : Blo 1772087 2244115 := bstep (se 1 (by rfl) ⟨1683086, by rfl⟩ : syracuseStep 2244115 = 3366173) B3366173
theorem B30703157 : Blo 1772087 30703157 := bstep (se 5 (by rfl) ⟨1439210, by rfl⟩ : syracuseStep 30703157 = 2878421) B2878421
theorem B3989105 : Blo 1772087 3989105 := bstep (se 2 (by rfl) ⟨1495914, by rfl⟩ : syracuseStep 3989105 = 2991829) B2991829
theorem B4488817 : Blo 1772087 4488817 := bstep (se 2 (by rfl) ⟨1683306, by rfl⟩ : syracuseStep 4488817 = 3366613) B3366613
theorem B3989123 : Blo 1772087 3989123 := bstep (se 1 (by rfl) ⟨2991842, by rfl⟩ : syracuseStep 3989123 = 5983685) B5983685
theorem B6389389 : Blo 1772087 6389389 := bstep (se 3 (by rfl) ⟨1198010, by rfl⟩ : syracuseStep 6389389 = 2396021) B2396021
theorem B17276557 : Blo 1772087 17276557 := bstep (se 3 (by rfl) ⟨3239354, by rfl⟩ : syracuseStep 17276557 = 6478709) B6478709
theorem B3366659 : Blo 1772087 3366659 := bstep (se 1 (by rfl) ⟨2524994, by rfl⟩ : syracuseStep 3366659 = 5049989) B5049989
theorem B24272693 : Blo 1772087 24272693 := bstep (se 5 (by rfl) ⟨1137782, by rfl⟩ : syracuseStep 24272693 = 2275565) B2275565
theorem B4489091 : Blo 1772087 4489091 := bstep (se 1 (by rfl) ⟨3366818, by rfl⟩ : syracuseStep 4489091 = 6733637) B6733637
theorem B3989393 : Blo 1772087 3989393 := bstep (se 2 (by rfl) ⟨1496022, by rfl⟩ : syracuseStep 3989393 = 2992045) B2992045
theorem B3989411 : Blo 1772087 3989411 := bstep (se 1 (by rfl) ⟨2992058, by rfl⟩ : syracuseStep 3989411 = 5984117) B5984117
theorem B2695091 : Blo 1772087 2695091 := bstep (se 1 (by rfl) ⟨2021318, by rfl⟩ : syracuseStep 2695091 = 4042637) B4042637
theorem B13828067 : Blo 1772087 13828067 := bstep (se 1 (by rfl) ⟨10371050, by rfl⟩ : syracuseStep 13828067 = 20742101) B20742101
theorem B3989555 : Blo 1772087 3989555 := bstep (se 1 (by rfl) ⟨2992166, by rfl⟩ : syracuseStep 3989555 = 5984333) B5984333
theorem B3989591 : Blo 1772087 3989591 := bstep (se 1 (by rfl) ⟨2992193, by rfl⟩ : syracuseStep 3989591 = 5984387) B5984387
theorem B3367001 : Blo 1772087 3367001 := bstep (se 2 (by rfl) ⟨1262625, by rfl⟩ : syracuseStep 3367001 = 2525251) B2525251
theorem B3596375 : Blo 1772087 3596375 := bstep (se 1 (by rfl) ⟨2697281, by rfl⟩ : syracuseStep 3596375 = 5394563) B5394563
theorem B8978525 : Blo 1772087 8978525 := bstep (se 3 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 8978525 = 3366947) B3366947
theorem B6733955 : Blo 1772087 6733955 := bstep (se 1 (by rfl) ⟨5050466, by rfl⟩ : syracuseStep 6733955 = 10100933) B10100933
theorem B3784843 : Blo 1772087 3784843 := bstep (se 1 (by rfl) ⟨2838632, by rfl⟩ : syracuseStep 3784843 = 5677265) B5677265
theorem B3989771 : Blo 1772087 3989771 := bstep (se 1 (by rfl) ⟨2992328, by rfl⟩ : syracuseStep 3989771 = 5984657) B5984657
theorem B3989825 : Blo 1772087 3989825 := bstep (se 2 (by rfl) ⟨1496184, by rfl⟩ : syracuseStep 3989825 = 2992369) B2992369
theorem B2523479 : Blo 1772087 2523479 := bstep (se 1 (by rfl) ⟨1892609, by rfl⟩ : syracuseStep 2523479 = 3785219) B3785219
theorem B1892695 : Blo 1772087 1892695 := bstep (se 1 (by rfl) ⟨1419521, by rfl⟩ : syracuseStep 1892695 = 2839043) B2839043
theorem B2990425 : Blo 1772087 2990425 := bstep (se 2 (by rfl) ⟨1121409, by rfl⟩ : syracuseStep 2990425 = 2242819) B2242819
theorem B5046617 : Blo 1772087 5046617 := bstep (se 2 (by rfl) ⟨1892481, by rfl⟩ : syracuseStep 5046617 = 3784963) B3784963
theorem B6390209 : Blo 1772087 6390209 := bstep (se 2 (by rfl) ⟨2396328, by rfl⟩ : syracuseStep 6390209 = 4792657) B4792657
theorem B5046731 : Blo 1772087 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B6824413 : Blo 1772087 6824413 := bstep (se 3 (by rfl) ⟨1279577, by rfl⟩ : syracuseStep 6824413 = 2559155) B2559155
theorem B2523673 : Blo 1772087 2523673 := bstep (se 2 (by rfl) ⟨946377, by rfl⟩ : syracuseStep 2523673 = 1892755) B1892755
theorem B3990041 : Blo 1772087 3990041 := bstep (se 2 (by rfl) ⟨1496265, by rfl⟩ : syracuseStep 3990041 = 2992531) B2992531
theorem B6734411 : Blo 1772087 6734411 := bstep (se 1 (by rfl) ⟨5050808, by rfl⟩ : syracuseStep 6734411 = 10101617) B10101617
theorem B3785305 : Blo 1772087 3785305 := bstep (se 2 (by rfl) ⟨1419489, by rfl⟩ : syracuseStep 3785305 = 2838979) B2838979
theorem B3990131 : Blo 1772087 3990131 := bstep (se 1 (by rfl) ⟨2992598, by rfl⟩ : syracuseStep 3990131 = 5985197) B5985197
theorem B10093187 : Blo 1772087 10093187 := bstep (se 1 (by rfl) ⟨7569890, by rfl⟩ : syracuseStep 10093187 = 15139781) B15139781
theorem B2245259 : Blo 1772087 2245259 := bstep (se 1 (by rfl) ⟨1683944, by rfl⟩ : syracuseStep 2245259 = 3367889) B3367889
theorem B5980823 : Blo 1772087 5980823 := bstep (se 1 (by rfl) ⟨4485617, by rfl⟩ : syracuseStep 5980823 = 8971235) B8971235
theorem B3990167 : Blo 1772087 3990167 := bstep (se 1 (by rfl) ⟨2992625, by rfl⟩ : syracuseStep 3990167 = 5985251) B5985251
theorem B15139507 : Blo 1772087 15139507 := bstep (se 1 (by rfl) ⟨11354630, by rfl⟩ : syracuseStep 15139507 = 22709261) B22709261
theorem B4260545 : Blo 1772087 4260545 := bstep (se 2 (by rfl) ⟨1597704, by rfl⟩ : syracuseStep 4260545 = 3195409) B3195409
theorem B4489931 : Blo 1772087 4489931 := bstep (se 1 (by rfl) ⟨3367448, by rfl⟩ : syracuseStep 4489931 = 6734897) B6734897
theorem B12780305 : Blo 1772087 12780305 := bstep (se 2 (by rfl) ⟨4792614, by rfl⟩ : syracuseStep 12780305 = 9585229) B9585229
theorem B6734609 : Blo 1772087 6734609 := bstep (se 2 (by rfl) ⟨2525478, by rfl⟩ : syracuseStep 6734609 = 5050957) B5050957
theorem B7570199 : Blo 1772087 7570199 := bstep (se 1 (by rfl) ⟨5677649, by rfl⟩ : syracuseStep 7570199 = 11355299) B11355299
theorem B12133165 : Blo 1772087 12133165 := bstep (se 3 (by rfl) ⟨2274968, by rfl⟩ : syracuseStep 12133165 = 4549937) B4549937
theorem B3990347 : Blo 1772087 3990347 := bstep (se 1 (by rfl) ⟨2992760, by rfl⟩ : syracuseStep 3990347 = 5985521) B5985521
theorem B4793177 : Blo 1772087 4793177 := bstep (se 2 (by rfl) ⟨1797441, by rfl⟩ : syracuseStep 4793177 = 3594883) B3594883
theorem B13468517 : Blo 1772087 13468517 := bstep (se 4 (by rfl) ⟨1262673, by rfl⟩ : syracuseStep 13468517 = 2525347) B2525347
theorem B3990401 : Blo 1772087 3990401 := bstep (se 2 (by rfl) ⟨1496400, by rfl⟩ : syracuseStep 3990401 = 2992801) B2992801
theorem B2990999 : Blo 1772087 2990999 := bstep (se 1 (by rfl) ⟨2243249, by rfl⟩ : syracuseStep 2990999 = 4486499) B4486499
theorem B2991127 : Blo 1772087 2991127 := bstep (se 1 (by rfl) ⟨2243345, by rfl⟩ : syracuseStep 2991127 = 4486691) B4486691
theorem B10093643 : Blo 1772087 10093643 := bstep (se 1 (by rfl) ⟨7570232, by rfl⟩ : syracuseStep 10093643 = 15140465) B15140465
theorem B6825035 : Blo 1772087 6825035 := bstep (se 1 (by rfl) ⟨5118776, by rfl⟩ : syracuseStep 6825035 = 10237553) B10237553
theorem B3990617 : Blo 1772087 3990617 := bstep (se 2 (by rfl) ⟨1496481, by rfl⟩ : syracuseStep 3990617 = 2992963) B2992963
theorem B1893515 : Blo 1772087 1893515 := bstep (se 1 (by rfl) ⟨1420136, by rfl⟩ : syracuseStep 1893515 = 2840273) B2840273
theorem B5981363 : Blo 1772087 5981363 := bstep (se 1 (by rfl) ⟨4486022, by rfl⟩ : syracuseStep 5981363 = 8972045) B8972045
theorem B3990707 : Blo 1772087 3990707 := bstep (se 1 (by rfl) ⟨2993030, by rfl⟩ : syracuseStep 3990707 = 5986061) B5986061
theorem B3990743 : Blo 1772087 3990743 := bstep (se 1 (by rfl) ⟨2993057, by rfl⟩ : syracuseStep 3990743 = 5986115) B5986115
theorem B13460741 : Blo 1772087 13460741 := bstep (se 4 (by rfl) ⟨1261944, by rfl⟩ : syracuseStep 13460741 = 2523889) B2523889
theorem B2131223 : Blo 1772087 2131223 := bstep (se 1 (by rfl) ⟨1598417, by rfl⟩ : syracuseStep 2131223 = 3196835) B3196835
theorem B13469003 : Blo 1772087 13469003 := bstep (se 1 (by rfl) ⟨10101752, by rfl⟩ : syracuseStep 13469003 = 20203505) B20203505
theorem B10102117 : Blo 1772087 10102117 := bstep (se 4 (by rfl) ⟨947073, by rfl⟩ : syracuseStep 10102117 = 1894147) B1894147
theorem B3990923 : Blo 1772087 3990923 := bstep (se 1 (by rfl) ⟨2993192, by rfl⟩ : syracuseStep 3990923 = 5986385) B5986385
theorem B5981633 : Blo 1772087 5981633 := bstep (se 2 (by rfl) ⟨2243112, by rfl⟩ : syracuseStep 5981633 = 4486225) B4486225
theorem B3990977 : Blo 1772087 3990977 := bstep (se 2 (by rfl) ⟨1496616, by rfl⟩ : syracuseStep 3990977 = 2993233) B2993233
theorem B6735383 : Blo 1772087 6735383 := bstep (se 1 (by rfl) ⟨5051537, by rfl⟩ : syracuseStep 6735383 = 10103075) B10103075
theorem B5047859 : Blo 1772087 5047859 := bstep (se 1 (by rfl) ⟨3785894, by rfl⟩ : syracuseStep 5047859 = 7571789) B7571789
theorem B2991755 : Blo 1772087 2991755 := bstep (se 1 (by rfl) ⟨2243816, by rfl⟩ : syracuseStep 2991755 = 4487633) B4487633
theorem B3991193 : Blo 1772087 3991193 := bstep (se 2 (by rfl) ⟨1496697, by rfl⟩ : syracuseStep 3991193 = 2993395) B2993395
theorem B8521433 : Blo 1772087 8521433 := bstep (se 2 (by rfl) ⟨3195537, by rfl⟩ : syracuseStep 8521433 = 6391075) B6391075
theorem B6735581 : Blo 1772087 6735581 := bstep (se 3 (by rfl) ⟨1262921, by rfl⟩ : syracuseStep 6735581 = 2525843) B2525843
theorem B3991283 : Blo 1772087 3991283 := bstep (se 1 (by rfl) ⟨2993462, by rfl⟩ : syracuseStep 3991283 = 5986925) B5986925
theorem B2991883 : Blo 1772087 2991883 := bstep (se 1 (by rfl) ⟨2243912, by rfl⟩ : syracuseStep 2991883 = 4487825) B4487825
theorem B3991319 : Blo 1772087 3991319 := bstep (se 1 (by rfl) ⟨2993489, by rfl⟩ : syracuseStep 3991319 = 5986979) B5986979
theorem B28747637 : Blo 1772087 28747637 := bstep (se 5 (by rfl) ⟨1347545, by rfl⟩ : syracuseStep 28747637 = 2695091) B2695091
theorem B2992025 : Blo 1772087 2992025 := bstep (se 2 (by rfl) ⟨1122009, by rfl⟩ : syracuseStep 2992025 = 2244019) B2244019
theorem B2697113 : Blo 1772087 2697113 := bstep (se 2 (by rfl) ⟨1011417, by rfl⟩ : syracuseStep 2697113 = 2022835) B2022835
theorem B5048257 : Blo 1772087 5048257 := bstep (se 2 (by rfl) ⟨1893096, by rfl⟩ : syracuseStep 5048257 = 3786193) B3786193
theorem B3786689 : Blo 1772087 3786689 := bstep (se 2 (by rfl) ⟨1420008, by rfl⟩ : syracuseStep 3786689 = 2840017) B2840017
theorem B2525131 : Blo 1772087 2525131 := bstep (se 1 (by rfl) ⟨1893848, by rfl⟩ : syracuseStep 2525131 = 3787697) B3787697
theorem B3991499 : Blo 1772087 3991499 := bstep (se 1 (by rfl) ⟨2993624, by rfl⟩ : syracuseStep 3991499 = 5987249) B5987249
theorem B5982173 : Blo 1772087 5982173 := bstep (se 3 (by rfl) ⟨1121657, by rfl⟩ : syracuseStep 5982173 = 2243315) B2243315
theorem B3991553 : Blo 1772087 3991553 := bstep (se 2 (by rfl) ⟨1496832, by rfl⟩ : syracuseStep 3991553 = 2993665) B2993665
theorem B2992153 : Blo 1772087 2992153 := bstep (se 2 (by rfl) ⟨1122057, by rfl⟩ : syracuseStep 2992153 = 2244115) B2244115
theorem B7571531 : Blo 1772087 7571531 := bstep (se 1 (by rfl) ⟨5678648, by rfl⟩ : syracuseStep 7571531 = 11357297) B11357297
theorem B8980631 : Blo 1772087 8980631 := bstep (se 1 (by rfl) ⟨6735473, by rfl⟩ : syracuseStep 8980631 = 13470947) B13470947
theorem B16394501 : Blo 1772087 16394501 := bstep (se 4 (by rfl) ⟨1536984, by rfl⟩ : syracuseStep 16394501 = 3073969) B3073969
theorem B27298093 : Blo 1772087 27298093 := bstep (se 3 (by rfl) ⟨5118392, by rfl⟩ : syracuseStep 27298093 = 10236785) B10236785
theorem B16181795 : Blo 1772087 16181795 := bstep (se 1 (by rfl) ⟨12136346, by rfl⟩ : syracuseStep 16181795 = 24272693) B24272693
theorem B1772087 : Blo 1772087 1772087 := bstep (se 1 (by rfl) ⟨1329065, by rfl⟩ : syracuseStep 1772087 = 2658131) B2658131
theorem B1772107 : Blo 1772087 1772107 := bstep (se 1 (by rfl) ⟨1329080, by rfl⟩ : syracuseStep 1772107 = 2658161) B2658161
theorem B1772119 : Blo 1772087 1772119 := bstep (se 1 (by rfl) ⟨1329089, by rfl⟩ : syracuseStep 1772119 = 2658179) B2658179
theorem B2992727 : Blo 1772087 2992727 := bstep (se 1 (by rfl) ⟨2244545, by rfl⟩ : syracuseStep 2992727 = 4489091) B4489091
theorem B1772139 : Blo 1772087 1772139 := bstep (se 1 (by rfl) ⟨1329104, by rfl⟩ : syracuseStep 1772139 = 2658209) B2658209
theorem B1772151 : Blo 1772087 1772151 := bstep (se 1 (by rfl) ⟨1329113, by rfl⟩ : syracuseStep 1772151 = 2658227) B2658227
theorem B1772171 : Blo 1772087 1772171 := bstep (se 1 (by rfl) ⟨1329128, by rfl⟩ : syracuseStep 1772171 = 2658257) B2658257
theorem B7572113 : Blo 1772087 7572113 := bstep (se 2 (by rfl) ⟨2839542, by rfl⟩ : syracuseStep 7572113 = 5679085) B5679085
theorem B1772183 : Blo 1772087 1772183 := bstep (se 1 (by rfl) ⟨1329137, by rfl⟩ : syracuseStep 1772183 = 2658275) B2658275
theorem B9218711 : Blo 1772087 9218711 := bstep (se 1 (by rfl) ⟨6914033, by rfl⟩ : syracuseStep 9218711 = 13828067) B13828067
theorem B1772203 : Blo 1772087 1772203 := bstep (se 1 (by rfl) ⟨1329152, by rfl⟩ : syracuseStep 1772203 = 2658305) B2658305
theorem B1772215 : Blo 1772087 1772215 := bstep (se 1 (by rfl) ⟨1329161, by rfl⟩ : syracuseStep 1772215 = 2658323) B2658323
theorem B1772235 : Blo 1772087 1772235 := bstep (se 1 (by rfl) ⟨1329176, by rfl⟩ : syracuseStep 1772235 = 2658353) B2658353
theorem B1772247 : Blo 1772087 1772247 := bstep (se 1 (by rfl) ⟨1329185, by rfl⟩ : syracuseStep 1772247 = 2658371) B2658371
theorem B2992855 : Blo 1772087 2992855 := bstep (se 1 (by rfl) ⟨2244641, by rfl⟩ : syracuseStep 2992855 = 4489283) B4489283
theorem B8973017 : Blo 1772087 8973017 := bstep (se 2 (by rfl) ⟨3364881, by rfl⟩ : syracuseStep 8973017 = 6729763) B6729763
theorem B1772267 : Blo 1772087 1772267 := bstep (se 1 (by rfl) ⟨1329200, by rfl⟩ : syracuseStep 1772267 = 2658401) B2658401
theorem B43158257 : Blo 1772087 43158257 := bstep (se 2 (by rfl) ⟨16184346, by rfl⟩ : syracuseStep 43158257 = 32368693) B32368693
theorem B1772279 : Blo 1772087 1772279 := bstep (se 1 (by rfl) ⟨1329209, by rfl⟩ : syracuseStep 1772279 = 2658419) B2658419
theorem B1772299 : Blo 1772087 1772299 := bstep (se 1 (by rfl) ⟨1329224, by rfl⟩ : syracuseStep 1772299 = 2658449) B2658449
theorem B1772311 : Blo 1772087 1772311 := bstep (se 1 (by rfl) ⟨1329233, by rfl⟩ : syracuseStep 1772311 = 2658467) B2658467
theorem B1772331 : Blo 1772087 1772331 := bstep (se 1 (by rfl) ⟨1329248, by rfl⟩ : syracuseStep 1772331 = 2658497) B2658497
theorem B1772343 : Blo 1772087 1772343 := bstep (se 1 (by rfl) ⟨1329257, by rfl⟩ : syracuseStep 1772343 = 2658515) B2658515
theorem B1772363 : Blo 1772087 1772363 := bstep (se 1 (by rfl) ⟨1329272, by rfl⟩ : syracuseStep 1772363 = 2658545) B2658545
theorem B1772375 : Blo 1772087 1772375 := bstep (se 1 (by rfl) ⟨1329281, by rfl⟩ : syracuseStep 1772375 = 2658563) B2658563
theorem B1772395 : Blo 1772087 1772395 := bstep (se 1 (by rfl) ⟨1329296, by rfl⟩ : syracuseStep 1772395 = 2658593) B2658593
theorem B1796971 : Blo 1772087 1796971 := bstep (se 1 (by rfl) ⟨1347728, by rfl⟩ : syracuseStep 1796971 = 2695457) B2695457
theorem B1772407 : Blo 1772087 1772407 := bstep (se 1 (by rfl) ⟨1329305, by rfl⟩ : syracuseStep 1772407 = 2658611) B2658611
theorem B6728579 : Blo 1772087 6728579 := bstep (se 1 (by rfl) ⟨5046434, by rfl⟩ : syracuseStep 6728579 = 10092869) B10092869
theorem B1772427 : Blo 1772087 1772427 := bstep (se 1 (by rfl) ⟨1329320, by rfl⟩ : syracuseStep 1772427 = 2658641) B2658641
theorem B1772439 : Blo 1772087 1772439 := bstep (se 1 (by rfl) ⟨1329329, by rfl⟩ : syracuseStep 1772439 = 2658659) B2658659
theorem B11365271 : Blo 1772087 11365271 := bstep (se 1 (by rfl) ⟨8523953, by rfl⟩ : syracuseStep 11365271 = 17047907) B17047907
theorem B1772459 : Blo 1772087 1772459 := bstep (se 1 (by rfl) ⟨1329344, by rfl⟩ : syracuseStep 1772459 = 2658689) B2658689
theorem B1772471 : Blo 1772087 1772471 := bstep (se 1 (by rfl) ⟨1329353, by rfl⟩ : syracuseStep 1772471 = 2658707) B2658707
theorem B1993675 : Blo 1772087 1993675 := bstep (se 1 (by rfl) ⟨1495256, by rfl⟩ : syracuseStep 1993675 = 2990513) B2990513
theorem B1772491 : Blo 1772087 1772491 := bstep (se 1 (by rfl) ⟨1329368, by rfl⟩ : syracuseStep 1772491 = 2658737) B2658737
theorem B1772503 : Blo 1772087 1772503 := bstep (se 1 (by rfl) ⟨1329377, by rfl⟩ : syracuseStep 1772503 = 2658755) B2658755
theorem B1772523 : Blo 1772087 1772523 := bstep (se 1 (by rfl) ⟨1329392, by rfl⟩ : syracuseStep 1772523 = 2658785) B2658785
theorem B1772535 : Blo 1772087 1772535 := bstep (se 1 (by rfl) ⟨1329401, by rfl⟩ : syracuseStep 1772535 = 2658803) B2658803
theorem B1772555 : Blo 1772087 1772555 := bstep (se 1 (by rfl) ⟨1329416, by rfl⟩ : syracuseStep 1772555 = 2658833) B2658833
theorem B1772567 : Blo 1772087 1772567 := bstep (se 1 (by rfl) ⟨1329425, by rfl⟩ : syracuseStep 1772567 = 2658851) B2658851
theorem B1772587 : Blo 1772087 1772587 := bstep (se 1 (by rfl) ⟨1329440, by rfl⟩ : syracuseStep 1772587 = 2658881) B2658881
theorem B1993783 : Blo 1772087 1993783 := bstep (se 1 (by rfl) ⟨1495337, by rfl⟩ : syracuseStep 1993783 = 2990675) B2990675
theorem B1772599 : Blo 1772087 1772599 := bstep (se 1 (by rfl) ⟨1329449, by rfl⟩ : syracuseStep 1772599 = 2658899) B2658899
theorem B1772619 : Blo 1772087 1772619 := bstep (se 1 (by rfl) ⟨1329464, by rfl⟩ : syracuseStep 1772619 = 2658929) B2658929
theorem B5983307 : Blo 1772087 5983307 := bstep (se 1 (by rfl) ⟨4487480, by rfl⟩ : syracuseStep 5983307 = 8974961) B8974961
theorem B1772631 : Blo 1772087 1772631 := bstep (se 1 (by rfl) ⟨1329473, by rfl⟩ : syracuseStep 1772631 = 2658947) B2658947
theorem B7187545 : Blo 1772087 7187545 := bstep (se 2 (by rfl) ⟨2695329, by rfl⟩ : syracuseStep 7187545 = 5390659) B5390659
theorem B1772651 : Blo 1772087 1772651 := bstep (se 1 (by rfl) ⟨1329488, by rfl⟩ : syracuseStep 1772651 = 2658977) B2658977
theorem B1772663 : Blo 1772087 1772663 := bstep (se 1 (by rfl) ⟨1329497, by rfl⟩ : syracuseStep 1772663 = 2658995) B2658995
theorem B1772683 : Blo 1772087 1772683 := bstep (se 1 (by rfl) ⟨1329512, by rfl⟩ : syracuseStep 1772683 = 2659025) B2659025
theorem B1772695 : Blo 1772087 1772695 := bstep (se 1 (by rfl) ⟨1329521, by rfl⟩ : syracuseStep 1772695 = 2659043) B2659043
theorem B1772715 : Blo 1772087 1772715 := bstep (se 1 (by rfl) ⟨1329536, by rfl⟩ : syracuseStep 1772715 = 2659073) B2659073
theorem B1772727 : Blo 1772087 1772727 := bstep (se 1 (by rfl) ⟨1329545, by rfl⟩ : syracuseStep 1772727 = 2659091) B2659091
theorem B1772747 : Blo 1772087 1772747 := bstep (se 1 (by rfl) ⟨1329560, by rfl⟩ : syracuseStep 1772747 = 2659121) B2659121
theorem B1772759 : Blo 1772087 1772759 := bstep (se 1 (by rfl) ⟨1329569, by rfl⟩ : syracuseStep 1772759 = 2659139) B2659139
theorem B1993963 : Blo 1772087 1993963 := bstep (se 1 (by rfl) ⟨1495472, by rfl⟩ : syracuseStep 1993963 = 2990945) B2990945
theorem B1772779 : Blo 1772087 1772779 := bstep (se 1 (by rfl) ⟨1329584, by rfl⟩ : syracuseStep 1772779 = 2659169) B2659169
theorem B1772791 : Blo 1772087 1772791 := bstep (se 1 (by rfl) ⟨1329593, by rfl⟩ : syracuseStep 1772791 = 2659187) B2659187
theorem B1772811 : Blo 1772087 1772811 := bstep (se 1 (by rfl) ⟨1329608, by rfl⟩ : syracuseStep 1772811 = 2659217) B2659217
theorem B1772823 : Blo 1772087 1772823 := bstep (se 1 (by rfl) ⟨1329617, by rfl⟩ : syracuseStep 1772823 = 2659235) B2659235
theorem B1772843 : Blo 1772087 1772843 := bstep (se 1 (by rfl) ⟨1329632, by rfl⟩ : syracuseStep 1772843 = 2659265) B2659265
theorem B3239219 : Blo 1772087 3239219 := bstep (se 1 (by rfl) ⟨2429414, by rfl⟩ : syracuseStep 3239219 = 4858829) B4858829
theorem B1772855 : Blo 1772087 1772855 := bstep (se 1 (by rfl) ⟨1329641, by rfl⟩ : syracuseStep 1772855 = 2659283) B2659283
theorem B1772875 : Blo 1772087 1772875 := bstep (se 1 (by rfl) ⟨1329656, by rfl⟩ : syracuseStep 1772875 = 2659313) B2659313
theorem B2993483 : Blo 1772087 2993483 := bstep (se 1 (by rfl) ⟨2245112, by rfl⟩ : syracuseStep 2993483 = 4490225) B4490225
theorem B1994071 : Blo 1772087 1994071 := bstep (se 1 (by rfl) ⟨1495553, by rfl⟩ : syracuseStep 1994071 = 2991107) B2991107
theorem B1772887 : Blo 1772087 1772887 := bstep (se 1 (by rfl) ⟨1329665, by rfl⟩ : syracuseStep 1772887 = 2659331) B2659331
theorem B5983577 : Blo 1772087 5983577 := bstep (se 2 (by rfl) ⟨2243841, by rfl⟩ : syracuseStep 5983577 = 4487683) B4487683
theorem B1772907 : Blo 1772087 1772907 := bstep (se 1 (by rfl) ⟨1329680, by rfl⟩ : syracuseStep 1772907 = 2659361) B2659361
theorem B1772919 : Blo 1772087 1772919 := bstep (se 1 (by rfl) ⟨1329689, by rfl⟩ : syracuseStep 1772919 = 2659379) B2659379
theorem B3837313 : Blo 1772087 3837313 := bstep (se 2 (by rfl) ⟨1438992, by rfl⟩ : syracuseStep 3837313 = 2877985) B2877985
theorem B1772939 : Blo 1772087 1772939 := bstep (se 1 (by rfl) ⟨1329704, by rfl⟩ : syracuseStep 1772939 = 2659409) B2659409
theorem B9710999 : Blo 1772087 9710999 := bstep (se 1 (by rfl) ⟨7283249, by rfl⟩ : syracuseStep 9710999 = 14566499) B14566499
theorem B1772951 : Blo 1772087 1772951 := bstep (se 1 (by rfl) ⟨1329713, by rfl⟩ : syracuseStep 1772951 = 2659427) B2659427
theorem B6393239 : Blo 1772087 6393239 := bstep (se 1 (by rfl) ⟨4794929, by rfl⟩ : syracuseStep 6393239 = 9589859) B9589859
theorem B1772971 : Blo 1772087 1772971 := bstep (se 1 (by rfl) ⟨1329728, by rfl⟩ : syracuseStep 1772971 = 2659457) B2659457
theorem B22719923 : Blo 1772087 22719923 := bstep (se 1 (by rfl) ⟨17039942, by rfl⟩ : syracuseStep 22719923 = 34079885) B34079885
theorem B1772983 : Blo 1772087 1772983 := bstep (se 1 (by rfl) ⟨1329737, by rfl⟩ : syracuseStep 1772983 = 2659475) B2659475
theorem B1773003 : Blo 1772087 1773003 := bstep (se 1 (by rfl) ⟨1329752, by rfl⟩ : syracuseStep 1773003 = 2659505) B2659505
theorem B2993611 : Blo 1772087 2993611 := bstep (se 1 (by rfl) ⟨2245208, by rfl⟩ : syracuseStep 2993611 = 4490417) B4490417
theorem B1773015 : Blo 1772087 1773015 := bstep (se 1 (by rfl) ⟨1329761, by rfl⟩ : syracuseStep 1773015 = 2659523) B2659523
theorem B1773035 : Blo 1772087 1773035 := bstep (se 1 (by rfl) ⟨1329776, by rfl⟩ : syracuseStep 1773035 = 2659553) B2659553
theorem B1773047 : Blo 1772087 1773047 := bstep (se 1 (by rfl) ⟨1329785, by rfl⟩ : syracuseStep 1773047 = 2659571) B2659571
theorem B1994251 : Blo 1772087 1994251 := bstep (se 1 (by rfl) ⟨1495688, by rfl⟩ : syracuseStep 1994251 = 2991377) B2991377
theorem B1773067 : Blo 1772087 1773067 := bstep (se 1 (by rfl) ⟨1329800, by rfl⟩ : syracuseStep 1773067 = 2659601) B2659601
theorem B1773079 : Blo 1772087 1773079 := bstep (se 1 (by rfl) ⟨1329809, by rfl⟩ : syracuseStep 1773079 = 2659619) B2659619
theorem B1773099 : Blo 1772087 1773099 := bstep (se 1 (by rfl) ⟨1329824, by rfl⟩ : syracuseStep 1773099 = 2659649) B2659649
theorem B1773111 : Blo 1772087 1773111 := bstep (se 1 (by rfl) ⟨1329833, by rfl⟩ : syracuseStep 1773111 = 2659667) B2659667
theorem B1773131 : Blo 1772087 1773131 := bstep (se 1 (by rfl) ⟨1329848, by rfl⟩ : syracuseStep 1773131 = 2659697) B2659697
theorem B3788363 : Blo 1772087 3788363 := bstep (se 1 (by rfl) ⟨2841272, by rfl⟩ : syracuseStep 3788363 = 5682545) B5682545
theorem B1773143 : Blo 1772087 1773143 := bstep (se 1 (by rfl) ⟨1329857, by rfl⟩ : syracuseStep 1773143 = 2659715) B2659715
theorem B2993753 : Blo 1772087 2993753 := bstep (se 2 (by rfl) ⟨1122657, by rfl⟩ : syracuseStep 2993753 = 2245315) B2245315
theorem B1773163 : Blo 1772087 1773163 := bstep (se 1 (by rfl) ⟨1329872, by rfl⟩ : syracuseStep 1773163 = 2659745) B2659745
theorem B1994359 : Blo 1772087 1994359 := bstep (se 1 (by rfl) ⟨1495769, by rfl⟩ : syracuseStep 1994359 = 2991539) B2991539
theorem B1773175 : Blo 1772087 1773175 := bstep (se 1 (by rfl) ⟨1329881, by rfl⟩ : syracuseStep 1773175 = 2659763) B2659763
theorem B13463171 : Blo 1772087 13463171 := bstep (se 1 (by rfl) ⟨10097378, by rfl⟩ : syracuseStep 13463171 = 20194757) B20194757
theorem B1773195 : Blo 1772087 1773195 := bstep (se 1 (by rfl) ⟨1329896, by rfl⟩ : syracuseStep 1773195 = 2659793) B2659793
theorem B1773207 : Blo 1772087 1773207 := bstep (se 1 (by rfl) ⟨1329905, by rfl⟩ : syracuseStep 1773207 = 2659811) B2659811
theorem B3837593 : Blo 1772087 3837593 := bstep (se 2 (by rfl) ⟨1439097, by rfl⟩ : syracuseStep 3837593 = 2878195) B2878195
theorem B1773227 : Blo 1772087 1773227 := bstep (se 1 (by rfl) ⟨1329920, by rfl⟩ : syracuseStep 1773227 = 2659841) B2659841
theorem B7573171 : Blo 1772087 7573171 := bstep (se 1 (by rfl) ⟨5679878, by rfl⟩ : syracuseStep 7573171 = 11359757) B11359757
theorem B1773239 : Blo 1772087 1773239 := bstep (se 1 (by rfl) ⟨1329929, by rfl⟩ : syracuseStep 1773239 = 2659859) B2659859
theorem B1797815 : Blo 1772087 1797815 := bstep (se 1 (by rfl) ⟨1348361, by rfl⟩ : syracuseStep 1797815 = 2696723) B2696723
theorem B1773259 : Blo 1772087 1773259 := bstep (se 1 (by rfl) ⟨1329944, by rfl⟩ : syracuseStep 1773259 = 2659889) B2659889
theorem B1773271 : Blo 1772087 1773271 := bstep (se 1 (by rfl) ⟨1329953, by rfl⟩ : syracuseStep 1773271 = 2659907) B2659907
theorem B1773291 : Blo 1772087 1773291 := bstep (se 1 (by rfl) ⟨1329968, by rfl⟩ : syracuseStep 1773291 = 2659937) B2659937
theorem B1773303 : Blo 1772087 1773303 := bstep (se 1 (by rfl) ⟨1329977, by rfl⟩ : syracuseStep 1773303 = 2659955) B2659955
theorem B1773323 : Blo 1772087 1773323 := bstep (se 1 (by rfl) ⟨1329992, by rfl⟩ : syracuseStep 1773323 = 2659985) B2659985
theorem B1773335 : Blo 1772087 1773335 := bstep (se 1 (by rfl) ⟨1330001, by rfl⟩ : syracuseStep 1773335 = 2660003) B2660003
theorem B1994539 : Blo 1772087 1994539 := bstep (se 1 (by rfl) ⟨1495904, by rfl⟩ : syracuseStep 1994539 = 2991809) B2991809
theorem B1773355 : Blo 1772087 1773355 := bstep (se 1 (by rfl) ⟨1330016, by rfl⟩ : syracuseStep 1773355 = 2660033) B2660033
theorem B19181357 : Blo 1772087 19181357 := bstep (se 3 (by rfl) ⟨3596504, by rfl⟩ : syracuseStep 19181357 = 7193009) B7193009
theorem B1773367 : Blo 1772087 1773367 := bstep (se 1 (by rfl) ⟨1330025, by rfl⟩ : syracuseStep 1773367 = 2660051) B2660051
theorem B1773387 : Blo 1772087 1773387 := bstep (se 1 (by rfl) ⟨1330040, by rfl⟩ : syracuseStep 1773387 = 2660081) B2660081
theorem B1773399 : Blo 1772087 1773399 := bstep (se 1 (by rfl) ⟨1330049, by rfl⟩ : syracuseStep 1773399 = 2660099) B2660099
theorem B2658137 : Blo 1772087 2658137 := bstep (se 2 (by rfl) ⟨996801, by rfl⟩ : syracuseStep 2658137 = 1993603) B1993603
theorem B102272867 : Blo 1772087 102272867 := bstep (se 1 (by rfl) ⟨76704650, by rfl⟩ : syracuseStep 102272867 = 153409301) B153409301
theorem B1773419 : Blo 1772087 1773419 := bstep (se 1 (by rfl) ⟨1330064, by rfl⟩ : syracuseStep 1773419 = 2660129) B2660129
theorem B1773431 : Blo 1772087 1773431 := bstep (se 1 (by rfl) ⟨1330073, by rfl⟩ : syracuseStep 1773431 = 2660147) B2660147
theorem B1773451 : Blo 1772087 1773451 := bstep (se 1 (by rfl) ⟨1330088, by rfl⟩ : syracuseStep 1773451 = 2660177) B2660177
theorem B1994647 : Blo 1772087 1994647 := bstep (se 1 (by rfl) ⟨1495985, by rfl⟩ : syracuseStep 1994647 = 2991971) B2991971
theorem B1773463 : Blo 1772087 1773463 := bstep (se 1 (by rfl) ⟨1330097, by rfl⟩ : syracuseStep 1773463 = 2660195) B2660195
theorem B1773483 : Blo 1772087 1773483 := bstep (se 1 (by rfl) ⟨1330112, by rfl⟩ : syracuseStep 1773483 = 2660225) B2660225
theorem B1773495 : Blo 1772087 1773495 := bstep (se 1 (by rfl) ⟨1330121, by rfl⟩ : syracuseStep 1773495 = 2660243) B2660243
theorem B2658251 : Blo 1772087 2658251 := bstep (se 1 (by rfl) ⟨1993688, by rfl⟩ : syracuseStep 2658251 = 3987377) B3987377
theorem B1773515 : Blo 1772087 1773515 := bstep (se 1 (by rfl) ⟨1330136, by rfl⟩ : syracuseStep 1773515 = 2660273) B2660273
theorem B2658263 : Blo 1772087 2658263 := bstep (se 1 (by rfl) ⟨1993697, by rfl⟩ : syracuseStep 2658263 = 3987395) B3987395
theorem B1773527 : Blo 1772087 1773527 := bstep (se 1 (by rfl) ⟨1330145, by rfl⟩ : syracuseStep 1773527 = 2660291) B2660291
theorem B1773547 : Blo 1772087 1773547 := bstep (se 1 (by rfl) ⟨1330160, by rfl⟩ : syracuseStep 1773547 = 2660321) B2660321
theorem B1773559 : Blo 1772087 1773559 := bstep (se 1 (by rfl) ⟨1330169, by rfl⟩ : syracuseStep 1773559 = 2660339) B2660339
theorem B1773579 : Blo 1772087 1773579 := bstep (se 1 (by rfl) ⟨1330184, by rfl⟩ : syracuseStep 1773579 = 2660369) B2660369
theorem B5984279 : Blo 1772087 5984279 := bstep (se 1 (by rfl) ⟨4488209, by rfl⟩ : syracuseStep 5984279 = 8976419) B8976419
theorem B2658329 : Blo 1772087 2658329 := bstep (se 2 (by rfl) ⟨996873, by rfl⟩ : syracuseStep 2658329 = 1993747) B1993747
theorem B1773591 : Blo 1772087 1773591 := bstep (se 1 (by rfl) ⟨1330193, by rfl⟩ : syracuseStep 1773591 = 2660387) B2660387
theorem B1773611 : Blo 1772087 1773611 := bstep (se 1 (by rfl) ⟨1330208, by rfl⟩ : syracuseStep 1773611 = 2660417) B2660417
theorem B1773623 : Blo 1772087 1773623 := bstep (se 1 (by rfl) ⟨1330217, by rfl⟩ : syracuseStep 1773623 = 2660435) B2660435
theorem B1994827 : Blo 1772087 1994827 := bstep (se 1 (by rfl) ⟨1496120, by rfl⟩ : syracuseStep 1994827 = 2992241) B2992241
theorem B1773643 : Blo 1772087 1773643 := bstep (se 1 (by rfl) ⟨1330232, by rfl⟩ : syracuseStep 1773643 = 2660465) B2660465
theorem B1773655 : Blo 1772087 1773655 := bstep (se 1 (by rfl) ⟨1330241, by rfl⟩ : syracuseStep 1773655 = 2660483) B2660483
theorem B1773675 : Blo 1772087 1773675 := bstep (se 1 (by rfl) ⟨1330256, by rfl⟩ : syracuseStep 1773675 = 2660513) B2660513
theorem B1773687 : Blo 1772087 1773687 := bstep (se 1 (by rfl) ⟨1330265, by rfl⟩ : syracuseStep 1773687 = 2660531) B2660531
theorem B19181699 : Blo 1772087 19181699 := bstep (se 1 (by rfl) ⟨14386274, by rfl⟩ : syracuseStep 19181699 = 28772549) B28772549
theorem B2658443 : Blo 1772087 2658443 := bstep (se 1 (by rfl) ⟨1993832, by rfl⟩ : syracuseStep 2658443 = 3987665) B3987665
theorem B1773707 : Blo 1772087 1773707 := bstep (se 1 (by rfl) ⟨1330280, by rfl⟩ : syracuseStep 1773707 = 2660561) B2660561
theorem B2658455 : Blo 1772087 2658455 := bstep (se 1 (by rfl) ⟨1993841, by rfl⟩ : syracuseStep 2658455 = 3987683) B3987683
theorem B5681303 : Blo 1772087 5681303 := bstep (se 1 (by rfl) ⟨4260977, by rfl⟩ : syracuseStep 5681303 = 8521955) B8521955
theorem B1773719 : Blo 1772087 1773719 := bstep (se 1 (by rfl) ⟨1330289, by rfl⟩ : syracuseStep 1773719 = 2660579) B2660579
theorem B1773739 : Blo 1772087 1773739 := bstep (se 1 (by rfl) ⟨1330304, by rfl⟩ : syracuseStep 1773739 = 2660609) B2660609
theorem B1994935 : Blo 1772087 1994935 := bstep (se 1 (by rfl) ⟨1496201, by rfl⟩ : syracuseStep 1994935 = 2992403) B2992403
theorem B1773751 : Blo 1772087 1773751 := bstep (se 1 (by rfl) ⟨1330313, by rfl⟩ : syracuseStep 1773751 = 2660627) B2660627
theorem B1773771 : Blo 1772087 1773771 := bstep (se 1 (by rfl) ⟨1330328, by rfl⟩ : syracuseStep 1773771 = 2660657) B2660657
theorem B1773783 : Blo 1772087 1773783 := bstep (se 1 (by rfl) ⟨1330337, by rfl⟩ : syracuseStep 1773783 = 2660675) B2660675
theorem B2658521 : Blo 1772087 2658521 := bstep (se 2 (by rfl) ⟨996945, by rfl⟩ : syracuseStep 2658521 = 1993891) B1993891
theorem B1773803 : Blo 1772087 1773803 := bstep (se 1 (by rfl) ⟨1330352, by rfl⟩ : syracuseStep 1773803 = 2660705) B2660705
theorem B1773815 : Blo 1772087 1773815 := bstep (se 1 (by rfl) ⟨1330361, by rfl⟩ : syracuseStep 1773815 = 2660723) B2660723
theorem B1773835 : Blo 1772087 1773835 := bstep (se 1 (by rfl) ⟨1330376, by rfl⟩ : syracuseStep 1773835 = 2660753) B2660753
theorem B9580817 : Blo 1772087 9580817 := bstep (se 2 (by rfl) ⟨3592806, by rfl⟩ : syracuseStep 9580817 = 7185613) B7185613
theorem B1773847 : Blo 1772087 1773847 := bstep (se 1 (by rfl) ⟨1330385, by rfl⟩ : syracuseStep 1773847 = 2660771) B2660771
theorem B14381347 : Blo 1772087 14381347 := bstep (se 1 (by rfl) ⟨10786010, by rfl⟩ : syracuseStep 14381347 = 21572021) B21572021
theorem B1773867 : Blo 1772087 1773867 := bstep (se 1 (by rfl) ⟨1330400, by rfl⟩ : syracuseStep 1773867 = 2660801) B2660801
theorem B8974637 : Blo 1772087 8974637 := bstep (se 3 (by rfl) ⟨1682744, by rfl⟩ : syracuseStep 8974637 = 3365489) B3365489
theorem B1773879 : Blo 1772087 1773879 := bstep (se 1 (by rfl) ⟨1330409, by rfl⟩ : syracuseStep 1773879 = 2660819) B2660819
theorem B2658635 : Blo 1772087 2658635 := bstep (se 1 (by rfl) ⟨1993976, by rfl⟩ : syracuseStep 2658635 = 3987953) B3987953
theorem B1773899 : Blo 1772087 1773899 := bstep (se 1 (by rfl) ⟨1330424, by rfl⟩ : syracuseStep 1773899 = 2660849) B2660849
theorem B2658647 : Blo 1772087 2658647 := bstep (se 1 (by rfl) ⟨1993985, by rfl⟩ : syracuseStep 2658647 = 3987971) B3987971
theorem B1773911 : Blo 1772087 1773911 := bstep (se 1 (by rfl) ⟨1330433, by rfl⟩ : syracuseStep 1773911 = 2660867) B2660867
theorem B13644125 : Blo 1772087 13644125 := bstep (se 3 (by rfl) ⟨2558273, by rfl⟩ : syracuseStep 13644125 = 5116547) B5116547
theorem B25555301 : Blo 1772087 25555301 := bstep (se 4 (by rfl) ⟨2395809, by rfl⟩ : syracuseStep 25555301 = 4791619) B4791619
theorem B1995115 : Blo 1772087 1995115 := bstep (se 1 (by rfl) ⟨1496336, by rfl⟩ : syracuseStep 1995115 = 2992673) B2992673
theorem B1773931 : Blo 1772087 1773931 := bstep (se 1 (by rfl) ⟨1330448, by rfl⟩ : syracuseStep 1773931 = 2660897) B2660897
theorem B1773943 : Blo 1772087 1773943 := bstep (se 1 (by rfl) ⟨1330457, by rfl⟩ : syracuseStep 1773943 = 2660915) B2660915
theorem B1773963 : Blo 1772087 1773963 := bstep (se 1 (by rfl) ⟨1330472, by rfl⟩ : syracuseStep 1773963 = 2660945) B2660945
theorem B5050775 : Blo 1772087 5050775 := bstep (se 1 (by rfl) ⟨3788081, by rfl⟩ : syracuseStep 5050775 = 7576163) B7576163
theorem B1773975 : Blo 1772087 1773975 := bstep (se 1 (by rfl) ⟨1330481, by rfl⟩ : syracuseStep 1773975 = 2660963) B2660963
theorem B2658713 : Blo 1772087 2658713 := bstep (se 2 (by rfl) ⟨997017, by rfl⟩ : syracuseStep 2658713 = 1994035) B1994035
theorem B1773995 : Blo 1772087 1773995 := bstep (se 1 (by rfl) ⟨1330496, by rfl⟩ : syracuseStep 1773995 = 2660993) B2660993
theorem B1774007 : Blo 1772087 1774007 := bstep (se 1 (by rfl) ⟨1330505, by rfl⟩ : syracuseStep 1774007 = 2661011) B2661011
theorem B1774027 : Blo 1772087 1774027 := bstep (se 1 (by rfl) ⟨1330520, by rfl⟩ : syracuseStep 1774027 = 2661041) B2661041
theorem B1995223 : Blo 1772087 1995223 := bstep (se 1 (by rfl) ⟨1496417, by rfl⟩ : syracuseStep 1995223 = 2992835) B2992835
theorem B1774039 : Blo 1772087 1774039 := bstep (se 1 (by rfl) ⟨1330529, by rfl⟩ : syracuseStep 1774039 = 2661059) B2661059
theorem B8090077 : Blo 1772087 8090077 := bstep (se 3 (by rfl) ⟨1516889, by rfl⟩ : syracuseStep 8090077 = 3033779) B3033779
theorem B1774059 : Blo 1772087 1774059 := bstep (se 1 (by rfl) ⟨1330544, by rfl⟩ : syracuseStep 1774059 = 2661089) B2661089
theorem B1774071 : Blo 1772087 1774071 := bstep (se 1 (by rfl) ⟨1330553, by rfl⟩ : syracuseStep 1774071 = 2661107) B2661107
theorem B2658827 : Blo 1772087 2658827 := bstep (se 1 (by rfl) ⟨1994120, by rfl⟩ : syracuseStep 2658827 = 3988241) B3988241
theorem B2658839 : Blo 1772087 2658839 := bstep (se 1 (by rfl) ⟨1994129, by rfl⟩ : syracuseStep 2658839 = 3988259) B3988259
theorem B5984819 : Blo 1772087 5984819 := bstep (se 1 (by rfl) ⟨4488614, by rfl⟩ : syracuseStep 5984819 = 8977229) B8977229
theorem B2658905 : Blo 1772087 2658905 := bstep (se 2 (by rfl) ⟨997089, by rfl⟩ : syracuseStep 2658905 = 1994179) B1994179
theorem B1995403 : Blo 1772087 1995403 := bstep (se 1 (by rfl) ⟨1496552, by rfl⟩ : syracuseStep 1995403 = 2993105) B2993105
theorem B2659019 : Blo 1772087 2659019 := bstep (se 1 (by rfl) ⟨1994264, by rfl⟩ : syracuseStep 2659019 = 3988529) B3988529
theorem B19690189 : Blo 1772087 19690189 := bstep (se 3 (by rfl) ⟨3691910, by rfl⟩ : syracuseStep 19690189 = 7383821) B7383821
theorem B2659031 : Blo 1772087 2659031 := bstep (se 1 (by rfl) ⟨1994273, by rfl⟩ : syracuseStep 2659031 = 3988547) B3988547
theorem B1995511 : Blo 1772087 1995511 := bstep (se 1 (by rfl) ⟨1496633, by rfl⟩ : syracuseStep 1995511 = 2993267) B2993267
theorem B2659097 : Blo 1772087 2659097 := bstep (se 2 (by rfl) ⟨997161, by rfl⟩ : syracuseStep 2659097 = 1994323) B1994323
theorem B5985089 : Blo 1772087 5985089 := bstep (se 2 (by rfl) ⟨2244408, by rfl⟩ : syracuseStep 5985089 = 4488817) B4488817
theorem B12776267 : Blo 1772087 12776267 := bstep (se 1 (by rfl) ⟨9582200, by rfl⟩ : syracuseStep 12776267 = 19164401) B19164401
theorem B2659211 : Blo 1772087 2659211 := bstep (se 1 (by rfl) ⟨1994408, by rfl⟩ : syracuseStep 2659211 = 3988817) B3988817
theorem B2659223 : Blo 1772087 2659223 := bstep (se 1 (by rfl) ⟨1994417, by rfl⟩ : syracuseStep 2659223 = 3988835) B3988835
theorem B1995691 : Blo 1772087 1995691 := bstep (se 1 (by rfl) ⟨1496768, by rfl⟩ : syracuseStep 1995691 = 2993537) B2993537
theorem B2659289 : Blo 1772087 2659289 := bstep (se 2 (by rfl) ⟨997233, by rfl⟩ : syracuseStep 2659289 = 1994467) B1994467
theorem B1995799 : Blo 1772087 1995799 := bstep (se 1 (by rfl) ⟨1496849, by rfl⟩ : syracuseStep 1995799 = 2993699) B2993699
theorem B20468771 : Blo 1772087 20468771 := bstep (se 1 (by rfl) ⟨15351578, by rfl⟩ : syracuseStep 20468771 = 30703157) B30703157
theorem B7574573 : Blo 1772087 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B8090675 : Blo 1772087 8090675 := bstep (se 1 (by rfl) ⟨6068006, by rfl⟩ : syracuseStep 8090675 = 12136013) B12136013
theorem B2659403 : Blo 1772087 2659403 := bstep (se 1 (by rfl) ⟨1994552, by rfl⟩ : syracuseStep 2659403 = 3989105) B3989105
theorem B2659415 : Blo 1772087 2659415 := bstep (se 1 (by rfl) ⟨1994561, by rfl⟩ : syracuseStep 2659415 = 3989123) B3989123
theorem B8090713 : Blo 1772087 8090713 := bstep (se 2 (by rfl) ⟨3034017, by rfl⟩ : syracuseStep 8090713 = 6068035) B6068035
theorem B2659481 : Blo 1772087 2659481 := bstep (se 2 (by rfl) ⟨997305, by rfl⟩ : syracuseStep 2659481 = 1994611) B1994611
theorem B4486337 : Blo 1772087 4486337 := bstep (se 2 (by rfl) ⟨1682376, by rfl⟩ : syracuseStep 4486337 = 3364753) B3364753
theorem B14578949 : Blo 1772087 14578949 := bstep (se 4 (by rfl) ⟨1366776, by rfl⟩ : syracuseStep 14578949 = 2733553) B2733553
theorem B2659595 : Blo 1772087 2659595 := bstep (se 1 (by rfl) ⟨1994696, by rfl⟩ : syracuseStep 2659595 = 3989393) B3989393
theorem B2659607 : Blo 1772087 2659607 := bstep (se 1 (by rfl) ⟨1994705, by rfl⟩ : syracuseStep 2659607 = 3989411) B3989411
theorem B2659673 : Blo 1772087 2659673 := bstep (se 2 (by rfl) ⟨997377, by rfl⟩ : syracuseStep 2659673 = 1994755) B1994755
theorem B5985629 : Blo 1772087 5985629 := bstep (se 3 (by rfl) ⟨1122305, by rfl⟩ : syracuseStep 5985629 = 2244611) B2244611
theorem B3413441 : Blo 1772087 3413441 := bstep (se 2 (by rfl) ⟨1280040, by rfl⟩ : syracuseStep 3413441 = 2560081) B2560081
theorem B2659787 : Blo 1772087 2659787 := bstep (se 1 (by rfl) ⟨1994840, by rfl⟩ : syracuseStep 2659787 = 3989681) B3989681
theorem B2659799 : Blo 1772087 2659799 := bstep (se 1 (by rfl) ⟨1994849, by rfl⟩ : syracuseStep 2659799 = 3989699) B3989699
theorem B2659865 : Blo 1772087 2659865 := bstep (se 2 (by rfl) ⟨997449, by rfl⟩ : syracuseStep 2659865 = 1994899) B1994899
theorem B10098269 : Blo 1772087 10098269 := bstep (se 3 (by rfl) ⟨1893425, by rfl⟩ : syracuseStep 10098269 = 3786851) B3786851
theorem B2659979 : Blo 1772087 2659979 := bstep (se 1 (by rfl) ⟨1994984, by rfl⟩ : syracuseStep 2659979 = 3989969) B3989969
theorem B3593879 : Blo 1772087 3593879 := bstep (se 1 (by rfl) ⟨2695409, by rfl⟩ : syracuseStep 3593879 = 5390819) B5390819
theorem B2659991 : Blo 1772087 2659991 := bstep (se 1 (by rfl) ⟨1994993, by rfl⟩ : syracuseStep 2659991 = 3989987) B3989987
theorem B4486873 : Blo 1772087 4486873 := bstep (se 2 (by rfl) ⟨1682577, by rfl⟩ : syracuseStep 4486873 = 3365155) B3365155
theorem B2660057 : Blo 1772087 2660057 := bstep (se 2 (by rfl) ⟨997521, by rfl⟩ : syracuseStep 2660057 = 1995043) B1995043
theorem B3987251 : Blo 1772087 3987251 := bstep (se 1 (by rfl) ⟨2990438, by rfl⟩ : syracuseStep 3987251 = 5980877) B5980877
theorem B2660171 : Blo 1772087 2660171 := bstep (se 1 (by rfl) ⟨1995128, by rfl⟩ : syracuseStep 2660171 = 3990257) B3990257
theorem B3987287 : Blo 1772087 3987287 := bstep (se 1 (by rfl) ⟨2990465, by rfl⟩ : syracuseStep 3987287 = 5980931) B5980931
theorem B2660183 : Blo 1772087 2660183 := bstep (se 1 (by rfl) ⟨1995137, by rfl⟩ : syracuseStep 2660183 = 3990275) B3990275
theorem B3594073 : Blo 1772087 3594073 := bstep (se 2 (by rfl) ⟨1347777, by rfl⟩ : syracuseStep 3594073 = 2695555) B2695555
theorem B2660249 : Blo 1772087 2660249 := bstep (se 2 (by rfl) ⟨997593, by rfl⟩ : syracuseStep 2660249 = 1995187) B1995187
theorem B6731693 : Blo 1772087 6731693 := bstep (se 3 (by rfl) ⟨1262192, by rfl⟩ : syracuseStep 6731693 = 2524385) B2524385
theorem B6387673 : Blo 1772087 6387673 := bstep (se 2 (by rfl) ⟨2395377, by rfl⟩ : syracuseStep 6387673 = 4790755) B4790755
theorem B3987467 : Blo 1772087 3987467 := bstep (se 1 (by rfl) ⟨2990600, by rfl⟩ : syracuseStep 3987467 = 5981201) B5981201
theorem B2660363 : Blo 1772087 2660363 := bstep (se 1 (by rfl) ⟨1995272, by rfl⟩ : syracuseStep 2660363 = 3990545) B3990545
theorem B2275339 : Blo 1772087 2275339 := bstep (se 1 (by rfl) ⟨1706504, by rfl⟩ : syracuseStep 2275339 = 3413009) B3413009
theorem B2660375 : Blo 1772087 2660375 := bstep (se 1 (by rfl) ⟨1995281, by rfl⟩ : syracuseStep 2660375 = 3990563) B3990563
theorem B3987521 : Blo 1772087 3987521 := bstep (se 2 (by rfl) ⟨1495320, by rfl⟩ : syracuseStep 3987521 = 2990641) B2990641
theorem B2660441 : Blo 1772087 2660441 := bstep (se 2 (by rfl) ⟨997665, by rfl⟩ : syracuseStep 2660441 = 1995331) B1995331
theorem B3365003 : Blo 1772087 3365003 := bstep (se 1 (by rfl) ⟨2523752, by rfl⟩ : syracuseStep 3365003 = 5047505) B5047505
theorem B3365057 : Blo 1772087 3365057 := bstep (se 2 (by rfl) ⟨1261896, by rfl⟩ : syracuseStep 3365057 = 2523793) B2523793
theorem B2660555 : Blo 1772087 2660555 := bstep (se 1 (by rfl) ⟨1995416, by rfl⟩ : syracuseStep 2660555 = 3990833) B3990833
theorem B16169165 : Blo 1772087 16169165 := bstep (se 3 (by rfl) ⟨3031718, by rfl⟩ : syracuseStep 16169165 = 6063437) B6063437
theorem B14375117 : Blo 1772087 14375117 := bstep (se 3 (by rfl) ⟨2695334, by rfl⟩ : syracuseStep 14375117 = 5390669) B5390669
theorem B2660567 : Blo 1772087 2660567 := bstep (se 1 (by rfl) ⟨1995425, by rfl⟩ : syracuseStep 2660567 = 3990851) B3990851
theorem B2021611 : Blo 1772087 2021611 := bstep (se 1 (by rfl) ⟨1516208, by rfl⟩ : syracuseStep 2021611 = 3032417) B3032417
theorem B3840257 : Blo 1772087 3840257 := bstep (se 2 (by rfl) ⟨1440096, by rfl⟩ : syracuseStep 3840257 = 2880193) B2880193
theorem B3987737 : Blo 1772087 3987737 := bstep (se 2 (by rfl) ⟨1495401, by rfl⟩ : syracuseStep 3987737 = 2990803) B2990803
theorem B2660633 : Blo 1772087 2660633 := bstep (se 2 (by rfl) ⟨997737, by rfl⟩ : syracuseStep 2660633 = 1995475) B1995475
theorem B10099019 : Blo 1772087 10099019 := bstep (se 1 (by rfl) ⟨7574264, by rfl⟩ : syracuseStep 10099019 = 15148529) B15148529
theorem B3987827 : Blo 1772087 3987827 := bstep (se 1 (by rfl) ⟨2990870, by rfl⟩ : syracuseStep 3987827 = 5981741) B5981741
theorem B2660747 : Blo 1772087 2660747 := bstep (se 1 (by rfl) ⟨1995560, by rfl⟩ : syracuseStep 2660747 = 3991121) B3991121
theorem B3987863 : Blo 1772087 3987863 := bstep (se 1 (by rfl) ⟨2990897, by rfl⟩ : syracuseStep 3987863 = 5981795) B5981795
theorem B2660759 : Blo 1772087 2660759 := bstep (se 1 (by rfl) ⟨1995569, by rfl⟩ : syracuseStep 2660759 = 3991139) B3991139
theorem B15153587 : Blo 1772087 15153587 := bstep (se 1 (by rfl) ⟨11365190, by rfl⟩ : syracuseStep 15153587 = 22730381) B22730381
theorem B5986763 : Blo 1772087 5986763 := bstep (se 1 (by rfl) ⟨4490072, by rfl⟩ : syracuseStep 5986763 = 8980145) B8980145
theorem B2660825 : Blo 1772087 2660825 := bstep (se 2 (by rfl) ⟨997809, by rfl⟩ : syracuseStep 2660825 = 1995619) B1995619
theorem B3988043 : Blo 1772087 3988043 := bstep (se 1 (by rfl) ⟨2991032, by rfl⟩ : syracuseStep 3988043 = 5982065) B5982065
theorem B2660939 : Blo 1772087 2660939 := bstep (se 1 (by rfl) ⟨1995704, by rfl⟩ : syracuseStep 2660939 = 3991409) B3991409
theorem B2660951 : Blo 1772087 2660951 := bstep (se 1 (by rfl) ⟨1995713, by rfl⟩ : syracuseStep 2660951 = 3991427) B3991427
theorem B8632925 : Blo 1772087 8632925 := bstep (se 3 (by rfl) ⟨1618673, by rfl⟩ : syracuseStep 8632925 = 3237347) B3237347
theorem B3283571 : Blo 1772087 3283571 := bstep (se 1 (by rfl) ⟨2462678, by rfl⟩ : syracuseStep 3283571 = 4925357) B4925357
theorem B3988097 : Blo 1772087 3988097 := bstep (se 2 (by rfl) ⟨1495536, by rfl⟩ : syracuseStep 3988097 = 2991073) B2991073
theorem B2661017 : Blo 1772087 2661017 := bstep (se 2 (by rfl) ⟨997881, by rfl⟩ : syracuseStep 2661017 = 1995763) B1995763
theorem B6732467 : Blo 1772087 6732467 := bstep (se 1 (by rfl) ⟨5049350, by rfl⟩ : syracuseStep 6732467 = 10098701) B10098701
theorem B5987033 : Blo 1772087 5987033 := bstep (se 2 (by rfl) ⟨2245137, by rfl⟩ : syracuseStep 5987033 = 4490275) B4490275
theorem B3693313 : Blo 1772087 3693313 := bstep (se 2 (by rfl) ⟨1384992, by rfl⟩ : syracuseStep 3693313 = 2769985) B2769985
theorem B2661131 : Blo 1772087 2661131 := bstep (se 1 (by rfl) ⟨1995848, by rfl⟩ : syracuseStep 2661131 = 3991697) B3991697
theorem B15153965 : Blo 1772087 15153965 := bstep (se 3 (by rfl) ⟨2841368, by rfl⟩ : syracuseStep 15153965 = 5682737) B5682737
theorem B4487987 : Blo 1772087 4487987 := bstep (se 1 (by rfl) ⟨3365990, by rfl⟩ : syracuseStep 4487987 = 6731981) B6731981
theorem B24263489 : Blo 1772087 24263489 := bstep (se 2 (by rfl) ⟨9098808, by rfl⟩ : syracuseStep 24263489 = 18197617) B18197617
theorem B3988313 : Blo 1772087 3988313 := bstep (se 2 (by rfl) ⟨1495617, by rfl⟩ : syracuseStep 3988313 = 2991235) B2991235
theorem B3193715 : Blo 1772087 3193715 := bstep (se 1 (by rfl) ⟨2395286, by rfl⟩ : syracuseStep 3193715 = 4790573) B4790573
theorem B2243467 : Blo 1772087 2243467 := bstep (se 1 (by rfl) ⟨1682600, by rfl⟩ : syracuseStep 2243467 = 3365201) B3365201
theorem B3988403 : Blo 1772087 3988403 := bstep (se 1 (by rfl) ⟨2991302, by rfl⟩ : syracuseStep 3988403 = 5982605) B5982605
theorem B13466573 : Blo 1772087 13466573 := bstep (se 3 (by rfl) ⟨2524982, by rfl⟩ : syracuseStep 13466573 = 5049965) B5049965
theorem B3988439 : Blo 1772087 3988439 := bstep (se 1 (by rfl) ⟨2991329, by rfl⟩ : syracuseStep 3988439 = 5982659) B5982659
theorem B7191517 : Blo 1772087 7191517 := bstep (se 3 (by rfl) ⟨1348409, by rfl⟩ : syracuseStep 7191517 = 2696819) B2696819
theorem B57498659 : Blo 1772087 57498659 := bstep (se 1 (by rfl) ⟨43123994, by rfl⟩ : syracuseStep 57498659 = 86247989) B86247989
theorem B3365975 : Blo 1772087 3365975 := bstep (se 1 (by rfl) ⟨2524481, by rfl⟩ : syracuseStep 3365975 = 5048963) B5048963
theorem B4488281 : Blo 1772087 4488281 := bstep (se 2 (by rfl) ⟨1683105, by rfl⟩ : syracuseStep 4488281 = 3366211) B3366211
theorem B3988619 : Blo 1772087 3988619 := bstep (se 1 (by rfl) ⟨2991464, by rfl⟩ : syracuseStep 3988619 = 5982929) B5982929
theorem B3988673 : Blo 1772087 3988673 := bstep (se 2 (by rfl) ⟨1495752, by rfl⟩ : syracuseStep 3988673 = 2991505) B2991505
theorem B6389057 : Blo 1772087 6389057 := bstep (se 2 (by rfl) ⟨2395896, by rfl⟩ : syracuseStep 6389057 = 4791793) B4791793
theorem B2694551 : Blo 1772087 2694551 := bstep (se 1 (by rfl) ⟨2020913, by rfl⟩ : syracuseStep 2694551 = 4041827) B4041827
theorem B3988889 : Blo 1772087 3988889 := bstep (se 2 (by rfl) ⟨1495833, by rfl⟩ : syracuseStep 3988889 = 2991667) B2991667
theorem B13467059 : Blo 1772087 13467059 := bstep (se 1 (by rfl) ⟨10100294, by rfl⟩ : syracuseStep 13467059 = 20200589) B20200589
theorem B30711257 : Blo 1772087 30711257 := bstep (se 2 (by rfl) ⟨11516721, by rfl⟩ : syracuseStep 30711257 = 23033443) B23033443
theorem B3988979 : Blo 1772087 3988979 := bstep (se 1 (by rfl) ⟨2991734, by rfl⟩ : syracuseStep 3988979 = 5983469) B5983469
theorem B8519185 : Blo 1772087 8519185 := bstep (se 2 (by rfl) ⟨3194694, by rfl⟩ : syracuseStep 8519185 = 6389389) B6389389
theorem B23035409 : Blo 1772087 23035409 := bstep (se 2 (by rfl) ⟨8638278, by rfl⟩ : syracuseStep 23035409 = 17276557) B17276557
theorem B3989015 : Blo 1772087 3989015 := bstep (se 1 (by rfl) ⟨2991761, by rfl⟩ : syracuseStep 3989015 = 5983523) B5983523
theorem B3366515 : Blo 1772087 3366515 := bstep (se 1 (by rfl) ⟨2524886, by rfl⟩ : syracuseStep 3366515 = 5049773) B5049773
theorem B3989195 : Blo 1772087 3989195 := bstep (se 1 (by rfl) ⟨2991896, by rfl⟩ : syracuseStep 3989195 = 5983793) B5983793
theorem B3989249 : Blo 1772087 3989249 := bstep (se 2 (by rfl) ⟨1495968, by rfl⟩ : syracuseStep 3989249 = 2991937) B2991937
theorem B6389549 : Blo 1772087 6389549 := bstep (se 3 (by rfl) ⟨1198040, by rfl⟩ : syracuseStep 6389549 = 2396081) B2396081
theorem B4792139 : Blo 1772087 4792139 := bstep (se 1 (by rfl) ⟨3594104, by rfl⟩ : syracuseStep 4792139 = 7188209) B7188209
theorem B2244439 : Blo 1772087 2244439 := bstep (se 1 (by rfl) ⟨1683329, by rfl⟩ : syracuseStep 2244439 = 3366659) B3366659
theorem B38363057 : Blo 1772087 38363057 := bstep (se 2 (by rfl) ⟨14386146, by rfl⟩ : syracuseStep 38363057 = 28772293) B28772293
theorem B10100659 : Blo 1772087 10100659 := bstep (se 1 (by rfl) ⟨7575494, by rfl⟩ : syracuseStep 10100659 = 15150989) B15150989
theorem B3989465 : Blo 1772087 3989465 := bstep (se 2 (by rfl) ⟨1496049, by rfl⟩ : syracuseStep 3989465 = 2992099) B2992099
theorem B3989519 : Blo 1772087 3989519 := bstep (se 1 (by rfl) ⟨2992139, by rfl⟩ : syracuseStep 3989519 = 5984279) B5984279
theorem B3989537 : Blo 1772087 3989537 := bstep (se 2 (by rfl) ⟨1496076, by rfl⟩ : syracuseStep 3989537 = 2992153) B2992153
theorem B2244667 : Blo 1772087 2244667 := bstep (se 1 (by rfl) ⟨1683500, by rfl⟩ : syracuseStep 2244667 = 3367001) B3367001
theorem B4489303 : Blo 1772087 4489303 := bstep (se 1 (by rfl) ⟨3366977, by rfl⟩ : syracuseStep 4489303 = 6733955) B6733955
theorem B12787799 : Blo 1772087 12787799 := bstep (se 1 (by rfl) ⟨9590849, by rfl⟩ : syracuseStep 12787799 = 19181699) B19181699
theorem B5046457 : Blo 1772087 5046457 := bstep (se 2 (by rfl) ⟨1892421, by rfl⟩ : syracuseStep 5046457 = 3784843) B3784843
theorem B22733045 : Blo 1772087 22733045 := bstep (se 5 (by rfl) ⟨1065611, by rfl⟩ : syracuseStep 22733045 = 2131223) B2131223
theorem B3367183 : Blo 1772087 3367183 := bstep (se 1 (by rfl) ⟨2525387, by rfl⟩ : syracuseStep 3367183 = 5050775) B5050775
theorem B2695481 : Blo 1772087 2695481 := bstep (se 2 (by rfl) ⟨1010805, by rfl⟩ : syracuseStep 2695481 = 2021611) B2021611
theorem B3989879 : Blo 1772087 3989879 := bstep (se 1 (by rfl) ⟨2992409, by rfl⟩ : syracuseStep 3989879 = 5984819) B5984819
theorem B4489607 : Blo 1772087 4489607 := bstep (se 1 (by rfl) ⟨3367205, by rfl⟩ : syracuseStep 4489607 = 6734411) B6734411
theorem B36397457 : Blo 1772087 36397457 := bstep (se 2 (by rfl) ⟨13649046, by rfl⟩ : syracuseStep 36397457 = 27298093) B27298093
theorem B2523593 : Blo 1772087 2523593 := bstep (se 2 (by rfl) ⟨946347, by rfl⟩ : syracuseStep 2523593 = 1892695) B1892695
theorem B8520203 : Blo 1772087 8520203 := bstep (se 1 (by rfl) ⟨6390152, by rfl⟩ : syracuseStep 8520203 = 12780305) B12780305
theorem B4489739 : Blo 1772087 4489739 := bstep (se 1 (by rfl) ⟨3367304, by rfl⟩ : syracuseStep 4489739 = 6734609) B6734609
theorem B5046799 : Blo 1772087 5046799 := bstep (se 1 (by rfl) ⟨3785099, by rfl⟩ : syracuseStep 5046799 = 7570199) B7570199
theorem B3990059 : Blo 1772087 3990059 := bstep (se 1 (by rfl) ⟨2992544, by rfl⟩ : syracuseStep 3990059 = 5985089) B5985089
theorem B3195451 : Blo 1772087 3195451 := bstep (se 1 (by rfl) ⟨2396588, by rfl⟩ : syracuseStep 3195451 = 4793177) B4793177
theorem B8979011 : Blo 1772087 8979011 := bstep (se 1 (by rfl) ⟨6734258, by rfl⟩ : syracuseStep 8979011 = 13468517) B13468517
theorem B10240685 : Blo 1772087 10240685 := bstep (se 3 (by rfl) ⟨1920128, by rfl⟩ : syracuseStep 10240685 = 3840257) B3840257
theorem B5047073 : Blo 1772087 5047073 := bstep (se 2 (by rfl) ⟨1892652, by rfl⟩ : syracuseStep 5047073 = 3785305) B3785305
theorem B2990891 : Blo 1772087 2990891 := bstep (se 1 (by rfl) ⟨2243168, by rfl⟩ : syracuseStep 2990891 = 4486337) B4486337
theorem B8979335 : Blo 1772087 8979335 := bstep (se 1 (by rfl) ⟨6734501, by rfl⟩ : syracuseStep 8979335 = 13469003) B13469003
theorem B3990419 : Blo 1772087 3990419 := bstep (se 1 (by rfl) ⟨2992814, by rfl⟩ : syracuseStep 3990419 = 5985629) B5985629
theorem B20186009 : Blo 1772087 20186009 := bstep (se 2 (by rfl) ⟨7569753, by rfl⟩ : syracuseStep 20186009 = 15139507) B15139507
theorem B3990473 : Blo 1772087 3990473 := bstep (se 2 (by rfl) ⟨1496427, by rfl⟩ : syracuseStep 3990473 = 2992855) B2992855
theorem B4490255 : Blo 1772087 4490255 := bstep (se 1 (by rfl) ⟨3367691, by rfl⟩ : syracuseStep 4490255 = 6735383) B6735383
theorem B7185469 : Blo 1772087 7185469 := bstep (se 3 (by rfl) ⟨1347275, by rfl⟩ : syracuseStep 7185469 = 2694551) B2694551
theorem B105014341 : Blo 1772087 105014341 := bstep (se 4 (by rfl) ⟨9845094, by rfl⟩ : syracuseStep 105014341 = 19690189) B19690189
theorem B4490387 : Blo 1772087 4490387 := bstep (se 1 (by rfl) ⟨3367790, by rfl⟩ : syracuseStep 4490387 = 6735581) B6735581
theorem B17040557 : Blo 1772087 17040557 := bstep (se 3 (by rfl) ⟨3195104, by rfl⟩ : syracuseStep 17040557 = 6390209) B6390209
theorem B2991289 : Blo 1772087 2991289 := bstep (se 2 (by rfl) ⟨1121733, by rfl⟩ : syracuseStep 2991289 = 2243467) B2243467
theorem B2524459 : Blo 1772087 2524459 := bstep (se 1 (by rfl) ⟨1893344, by rfl⟩ : syracuseStep 2524459 = 3786689) B3786689
theorem B5047687 : Blo 1772087 5047687 := bstep (se 1 (by rfl) ⟨3785765, by rfl⟩ : syracuseStep 5047687 = 7571531) B7571531
theorem B10929667 : Blo 1772087 10929667 := bstep (se 1 (by rfl) ⟨8197250, by rfl⟩ : syracuseStep 10929667 = 16394501) B16394501
theorem B10102391 : Blo 1772087 10102391 := bstep (se 1 (by rfl) ⟨7576793, by rfl⟩ : syracuseStep 10102391 = 15153587) B15153587
theorem B3991175 : Blo 1772087 3991175 := bstep (se 1 (by rfl) ⟨2993381, by rfl⟩ : syracuseStep 3991175 = 5986763) B5986763
theorem B2189047 : Blo 1772087 2189047 := bstep (se 1 (by rfl) ⟨1641785, by rfl⟩ : syracuseStep 2189047 = 3283571) B3283571
theorem B5048075 : Blo 1772087 5048075 := bstep (se 1 (by rfl) ⟨3786056, by rfl⟩ : syracuseStep 5048075 = 7572113) B7572113
theorem B6145807 : Blo 1772087 6145807 := bstep (se 1 (by rfl) ⟨4609355, by rfl⟩ : syracuseStep 6145807 = 9218711) B9218711
theorem B13469489 : Blo 1772087 13469489 := bstep (se 2 (by rfl) ⟨5051058, by rfl⟩ : syracuseStep 13469489 = 10102117) B10102117
theorem B5982011 : Blo 1772087 5982011 := bstep (se 1 (by rfl) ⟨4486508, by rfl⟩ : syracuseStep 5982011 = 8973017) B8973017
theorem B3991355 : Blo 1772087 3991355 := bstep (se 1 (by rfl) ⟨2993516, by rfl⟩ : syracuseStep 3991355 = 5987033) B5987033
theorem B4794173 : Blo 1772087 4794173 := bstep (se 3 (by rfl) ⟨898907, by rfl⟩ : syracuseStep 4794173 = 1797815) B1797815
theorem B28772171 : Blo 1772087 28772171 := bstep (se 1 (by rfl) ⟨21579128, by rfl⟩ : syracuseStep 28772171 = 43158257) B43158257
theorem B10102643 : Blo 1772087 10102643 := bstep (se 1 (by rfl) ⟨7576982, by rfl⟩ : syracuseStep 10102643 = 15153965) B15153965
theorem B2991991 : Blo 1772087 2991991 := bstep (se 1 (by rfl) ⟨2243993, by rfl⟩ : syracuseStep 2991991 = 4487987) B4487987
theorem B3991481 : Blo 1772087 3991481 := bstep (se 2 (by rfl) ⟨1496805, by rfl⟩ : syracuseStep 3991481 = 2993611) B2993611
theorem B20465669 : Blo 1772087 20465669 := bstep (se 4 (by rfl) ⟨1918656, by rfl⟩ : syracuseStep 20465669 = 3837313) B3837313
theorem B38332439 : Blo 1772087 38332439 := bstep (se 1 (by rfl) ⟨28749329, by rfl⟩ : syracuseStep 38332439 = 57498659) B57498659
theorem B2992187 : Blo 1772087 2992187 := bstep (se 1 (by rfl) ⟨2244140, by rfl⟩ : syracuseStep 2992187 = 4488281) B4488281
theorem B64702637 : Blo 1772087 64702637 := bstep (se 3 (by rfl) ⟨12131744, by rfl⟩ : syracuseStep 64702637 = 24263489) B24263489
theorem B6473999 : Blo 1772087 6473999 := bstep (se 1 (by rfl) ⟨4855499, by rfl⟩ : syracuseStep 6473999 = 9710999) B9710999
theorem B4262159 : Blo 1772087 4262159 := bstep (se 1 (by rfl) ⟨3196619, by rfl⟩ : syracuseStep 4262159 = 6393239) B6393239
theorem B5982497 : Blo 1772087 5982497 := bstep (se 2 (by rfl) ⟨2243436, by rfl⟩ : syracuseStep 5982497 = 4486873) B4486873
theorem B20474171 : Blo 1772087 20474171 := bstep (se 1 (by rfl) ⟨15355628, by rfl⟩ : syracuseStep 20474171 = 30711257) B30711257
theorem B2525575 : Blo 1772087 2525575 := bstep (se 1 (by rfl) ⟨1894181, by rfl⟩ : syracuseStep 2525575 = 3788363) B3788363
theorem B2558395 : Blo 1772087 2558395 := bstep (se 1 (by rfl) ⟨1918796, by rfl⟩ : syracuseStep 2558395 = 3837593) B3837593
theorem B2992585 : Blo 1772087 2992585 := bstep (se 2 (by rfl) ⟨1122219, by rfl⟩ : syracuseStep 2992585 = 2244439) B2244439
theorem B1772091 : Blo 1772087 1772091 := bstep (se 1 (by rfl) ⟨1329068, by rfl⟩ : syracuseStep 1772091 = 2658137) B2658137
theorem B1772167 : Blo 1772087 1772167 := bstep (se 1 (by rfl) ⟨1329125, by rfl⟩ : syracuseStep 1772167 = 2658251) B2658251
theorem B1772175 : Blo 1772087 1772175 := bstep (se 1 (by rfl) ⟨1329131, by rfl⟩ : syracuseStep 1772175 = 2658263) B2658263
theorem B3033785 : Blo 1772087 3033785 := bstep (se 2 (by rfl) ⟨1137669, by rfl⟩ : syracuseStep 3033785 = 2275339) B2275339
theorem B1772219 : Blo 1772087 1772219 := bstep (se 1 (by rfl) ⟨1329164, by rfl⟩ : syracuseStep 1772219 = 2658329) B2658329
theorem B1772295 : Blo 1772087 1772295 := bstep (se 1 (by rfl) ⟨1329221, by rfl⟩ : syracuseStep 1772295 = 2658443) B2658443
theorem B1772303 : Blo 1772087 1772303 := bstep (se 1 (by rfl) ⟨1329227, by rfl⟩ : syracuseStep 1772303 = 2658455) B2658455
theorem B3787535 : Blo 1772087 3787535 := bstep (se 1 (by rfl) ⟨2840651, by rfl⟩ : syracuseStep 3787535 = 5681303) B5681303
theorem B1772347 : Blo 1772087 1772347 := bstep (se 1 (by rfl) ⟨1329260, by rfl⟩ : syracuseStep 1772347 = 2658521) B2658521
theorem B5983091 : Blo 1772087 5983091 := bstep (se 1 (by rfl) ⟨4487318, by rfl⟩ : syracuseStep 5983091 = 8974637) B8974637
theorem B1772423 : Blo 1772087 1772423 := bstep (se 1 (by rfl) ⟨1329317, by rfl⟩ : syracuseStep 1772423 = 2658635) B2658635
theorem B1772431 : Blo 1772087 1772431 := bstep (se 1 (by rfl) ⟨1329323, by rfl⟩ : syracuseStep 1772431 = 2658647) B2658647
theorem B9096083 : Blo 1772087 9096083 := bstep (se 1 (by rfl) ⟨6822062, by rfl⟩ : syracuseStep 9096083 = 13644125) B13644125
theorem B1772475 : Blo 1772087 1772475 := bstep (se 1 (by rfl) ⟨1329356, by rfl⟩ : syracuseStep 1772475 = 2658713) B2658713
theorem B1772551 : Blo 1772087 1772551 := bstep (se 1 (by rfl) ⟨1329413, by rfl⟩ : syracuseStep 1772551 = 2658827) B2658827
theorem B1772559 : Blo 1772087 1772559 := bstep (se 1 (by rfl) ⟨1329419, by rfl⟩ : syracuseStep 1772559 = 2658839) B2658839
theorem B8973341 : Blo 1772087 8973341 := bstep (se 3 (by rfl) ⟨1682501, by rfl⟩ : syracuseStep 8973341 = 3365003) B3365003
theorem B5049373 : Blo 1772087 5049373 := bstep (se 3 (by rfl) ⟨946757, by rfl⟩ : syracuseStep 5049373 = 1893515) B1893515
theorem B1772603 : Blo 1772087 1772603 := bstep (se 1 (by rfl) ⟨1329452, by rfl⟩ : syracuseStep 1772603 = 2658905) B2658905
theorem B6728791 : Blo 1772087 6728791 := bstep (se 1 (by rfl) ⟨5046593, by rfl⟩ : syracuseStep 6728791 = 10093187) B10093187
theorem B1772679 : Blo 1772087 1772679 := bstep (se 1 (by rfl) ⟨1329509, by rfl⟩ : syracuseStep 1772679 = 2659019) B2659019
theorem B2993287 : Blo 1772087 2993287 := bstep (se 1 (by rfl) ⟨2244965, by rfl⟩ : syracuseStep 2993287 = 4489931) B4489931
theorem B1772687 : Blo 1772087 1772687 := bstep (se 1 (by rfl) ⟨1329515, by rfl⟩ : syracuseStep 1772687 = 2659031) B2659031
theorem B1772731 : Blo 1772087 1772731 := bstep (se 1 (by rfl) ⟨1329548, by rfl⟩ : syracuseStep 1772731 = 2659097) B2659097
theorem B38333645 : Blo 1772087 38333645 := bstep (se 3 (by rfl) ⟨7187558, by rfl⟩ : syracuseStep 38333645 = 14375117) B14375117
theorem B1772807 : Blo 1772087 1772807 := bstep (se 1 (by rfl) ⟨1329605, by rfl⟩ : syracuseStep 1772807 = 2659211) B2659211
theorem B1993999 : Blo 1772087 1993999 := bstep (se 1 (by rfl) ⟨1495499, by rfl⟩ : syracuseStep 1993999 = 2990999) B2990999
theorem B1772815 : Blo 1772087 1772815 := bstep (se 1 (by rfl) ⟨1329611, by rfl⟩ : syracuseStep 1772815 = 2659223) B2659223
theorem B1772859 : Blo 1772087 1772859 := bstep (se 1 (by rfl) ⟨1329644, by rfl⟩ : syracuseStep 1772859 = 2659289) B2659289
theorem B5049715 : Blo 1772087 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B5393783 : Blo 1772087 5393783 := bstep (se 1 (by rfl) ⟨4045337, by rfl⟩ : syracuseStep 5393783 = 8090675) B8090675
theorem B6729095 : Blo 1772087 6729095 := bstep (se 1 (by rfl) ⟨5046821, by rfl⟩ : syracuseStep 6729095 = 10093643) B10093643
theorem B1772935 : Blo 1772087 1772935 := bstep (se 1 (by rfl) ⟨1329701, by rfl⟩ : syracuseStep 1772935 = 2659403) B2659403
theorem B4550023 : Blo 1772087 4550023 := bstep (se 1 (by rfl) ⟨3412517, by rfl⟩ : syracuseStep 4550023 = 6825035) B6825035
theorem B1772943 : Blo 1772087 1772943 := bstep (se 1 (by rfl) ⟨1329707, by rfl⟩ : syracuseStep 1772943 = 2659415) B2659415
theorem B1772987 : Blo 1772087 1772987 := bstep (se 1 (by rfl) ⟨1329740, by rfl⟩ : syracuseStep 1772987 = 2659481) B2659481
theorem B8973827 : Blo 1772087 8973827 := bstep (se 1 (by rfl) ⟨6730370, by rfl⟩ : syracuseStep 8973827 = 13460741) B13460741
theorem B9719299 : Blo 1772087 9719299 := bstep (se 1 (by rfl) ⟨7289474, by rfl⟩ : syracuseStep 9719299 = 14578949) B14578949
theorem B1773063 : Blo 1772087 1773063 := bstep (se 1 (by rfl) ⟨1329797, by rfl⟩ : syracuseStep 1773063 = 2659595) B2659595
theorem B1773071 : Blo 1772087 1773071 := bstep (se 1 (by rfl) ⟨1329803, by rfl⟩ : syracuseStep 1773071 = 2659607) B2659607
theorem B1773115 : Blo 1772087 1773115 := bstep (se 1 (by rfl) ⟨1329836, by rfl⟩ : syracuseStep 1773115 = 2659673) B2659673
theorem B6729277 : Blo 1772087 6729277 := bstep (se 3 (by rfl) ⟨1261739, by rfl⟩ : syracuseStep 6729277 = 2523479) B2523479
theorem B1773191 : Blo 1772087 1773191 := bstep (se 1 (by rfl) ⟨1329893, by rfl⟩ : syracuseStep 1773191 = 2659787) B2659787
theorem B1773199 : Blo 1772087 1773199 := bstep (se 1 (by rfl) ⟨1329899, by rfl⟩ : syracuseStep 1773199 = 2659799) B2659799
theorem B1773243 : Blo 1772087 1773243 := bstep (se 1 (by rfl) ⟨1329932, by rfl⟩ : syracuseStep 1773243 = 2659865) B2659865
theorem B1994503 : Blo 1772087 1994503 := bstep (se 1 (by rfl) ⟨1495877, by rfl⟩ : syracuseStep 1994503 = 2991755) B2991755
theorem B1773319 : Blo 1772087 1773319 := bstep (se 1 (by rfl) ⟨1329989, by rfl⟩ : syracuseStep 1773319 = 2659979) B2659979
theorem B2395919 : Blo 1772087 2395919 := bstep (se 1 (by rfl) ⟨1796939, by rfl⟩ : syracuseStep 2395919 = 3593879) B3593879
theorem B1773327 : Blo 1772087 1773327 := bstep (se 1 (by rfl) ⟨1329995, by rfl⟩ : syracuseStep 1773327 = 2659991) B2659991
theorem B2395961 : Blo 1772087 2395961 := bstep (se 2 (by rfl) ⟨898485, by rfl⟩ : syracuseStep 2395961 = 1796971) B1796971
theorem B5680955 : Blo 1772087 5680955 := bstep (se 1 (by rfl) ⟨4260716, by rfl⟩ : syracuseStep 5680955 = 8521433) B8521433
theorem B1773371 : Blo 1772087 1773371 := bstep (se 1 (by rfl) ⟨1330028, by rfl⟩ : syracuseStep 1773371 = 2660057) B2660057
theorem B2658167 : Blo 1772087 2658167 := bstep (se 1 (by rfl) ⟨1993625, by rfl⟩ : syracuseStep 2658167 = 3987251) B3987251
theorem B1773447 : Blo 1772087 1773447 := bstep (se 1 (by rfl) ⟨1330085, by rfl⟩ : syracuseStep 1773447 = 2660171) B2660171
theorem B2658191 : Blo 1772087 2658191 := bstep (se 1 (by rfl) ⟨1993643, by rfl⟩ : syracuseStep 2658191 = 3987287) B3987287
theorem B1773455 : Blo 1772087 1773455 := bstep (se 1 (by rfl) ⟨1330091, by rfl⟩ : syracuseStep 1773455 = 2660183) B2660183
theorem B19165091 : Blo 1772087 19165091 := bstep (se 1 (by rfl) ⟨14373818, by rfl⟩ : syracuseStep 19165091 = 28747637) B28747637
theorem B2658233 : Blo 1772087 2658233 := bstep (se 2 (by rfl) ⟨996837, by rfl⟩ : syracuseStep 2658233 = 1993675) B1993675
theorem B1994683 : Blo 1772087 1994683 := bstep (se 1 (by rfl) ⟨1496012, by rfl⟩ : syracuseStep 1994683 = 2992025) B2992025
theorem B1773499 : Blo 1772087 1773499 := bstep (se 1 (by rfl) ⟨1330124, by rfl⟩ : syracuseStep 1773499 = 2660249) B2660249
theorem B1798075 : Blo 1772087 1798075 := bstep (se 1 (by rfl) ⟨1348556, by rfl⟩ : syracuseStep 1798075 = 2697113) B2697113
theorem B9588689 : Blo 1772087 9588689 := bstep (se 2 (by rfl) ⟨3595758, by rfl⟩ : syracuseStep 9588689 = 7191517) B7191517
theorem B19697669 : Blo 1772087 19697669 := bstep (se 4 (by rfl) ⟨1846656, by rfl⟩ : syracuseStep 19697669 = 3693313) B3693313
theorem B2658311 : Blo 1772087 2658311 := bstep (se 1 (by rfl) ⟨1993733, by rfl⟩ : syracuseStep 2658311 = 3987467) B3987467
theorem B1773575 : Blo 1772087 1773575 := bstep (se 1 (by rfl) ⟨1330181, by rfl⟩ : syracuseStep 1773575 = 2660363) B2660363
theorem B1773583 : Blo 1772087 1773583 := bstep (se 1 (by rfl) ⟨1330187, by rfl⟩ : syracuseStep 1773583 = 2660375) B2660375
theorem B2658347 : Blo 1772087 2658347 := bstep (se 1 (by rfl) ⟨1993760, by rfl⟩ : syracuseStep 2658347 = 3987521) B3987521
theorem B1773627 : Blo 1772087 1773627 := bstep (se 1 (by rfl) ⟨1330220, by rfl⟩ : syracuseStep 1773627 = 2660441) B2660441
theorem B2658377 : Blo 1772087 2658377 := bstep (se 2 (by rfl) ⟨996891, by rfl⟩ : syracuseStep 2658377 = 1993783) B1993783
theorem B1773703 : Blo 1772087 1773703 := bstep (se 1 (by rfl) ⟨1330277, by rfl⟩ : syracuseStep 1773703 = 2660555) B2660555
theorem B1773711 : Blo 1772087 1773711 := bstep (se 1 (by rfl) ⟨1330283, by rfl⟩ : syracuseStep 1773711 = 2660567) B2660567
theorem B2658491 : Blo 1772087 2658491 := bstep (se 1 (by rfl) ⟨1993868, by rfl⟩ : syracuseStep 2658491 = 3987737) B3987737
theorem B1773755 : Blo 1772087 1773755 := bstep (se 1 (by rfl) ⟨1330316, by rfl⟩ : syracuseStep 1773755 = 2660633) B2660633
theorem B2658551 : Blo 1772087 2658551 := bstep (se 1 (by rfl) ⟨1993913, by rfl⟩ : syracuseStep 2658551 = 3987827) B3987827
theorem B1773831 : Blo 1772087 1773831 := bstep (se 1 (by rfl) ⟨1330373, by rfl⟩ : syracuseStep 1773831 = 2660747) B2660747
theorem B2658575 : Blo 1772087 2658575 := bstep (se 1 (by rfl) ⟨1993931, by rfl⟩ : syracuseStep 2658575 = 3987863) B3987863
theorem B1773839 : Blo 1772087 1773839 := bstep (se 1 (by rfl) ⟨1330379, by rfl⟩ : syracuseStep 1773839 = 2660759) B2660759
theorem B2658617 : Blo 1772087 2658617 := bstep (se 2 (by rfl) ⟨996981, by rfl⟩ : syracuseStep 2658617 = 1993963) B1993963
theorem B1773883 : Blo 1772087 1773883 := bstep (se 1 (by rfl) ⟨1330412, by rfl⟩ : syracuseStep 1773883 = 2660825) B2660825
theorem B2658695 : Blo 1772087 2658695 := bstep (se 1 (by rfl) ⟨1994021, by rfl⟩ : syracuseStep 2658695 = 3988043) B3988043
theorem B1773959 : Blo 1772087 1773959 := bstep (se 1 (by rfl) ⟨1330469, by rfl⟩ : syracuseStep 1773959 = 2660939) B2660939
theorem B1995151 : Blo 1772087 1995151 := bstep (se 1 (by rfl) ⟨1496363, by rfl⟩ : syracuseStep 1995151 = 2992727) B2992727
theorem B1773967 : Blo 1772087 1773967 := bstep (se 1 (by rfl) ⟨1330475, by rfl⟩ : syracuseStep 1773967 = 2660951) B2660951
theorem B5755283 : Blo 1772087 5755283 := bstep (se 1 (by rfl) ⟨4316462, by rfl⟩ : syracuseStep 5755283 = 8632925) B8632925
theorem B2658731 : Blo 1772087 2658731 := bstep (se 1 (by rfl) ⟨1994048, by rfl⟩ : syracuseStep 2658731 = 3988097) B3988097
theorem B1774011 : Blo 1772087 1774011 := bstep (se 1 (by rfl) ⟨1330508, by rfl⟩ : syracuseStep 1774011 = 2661017) B2661017
theorem B2658761 : Blo 1772087 2658761 := bstep (se 2 (by rfl) ⟨997035, by rfl⟩ : syracuseStep 2658761 = 1994071) B1994071
theorem B1774087 : Blo 1772087 1774087 := bstep (se 1 (by rfl) ⟨1330565, by rfl⟩ : syracuseStep 1774087 = 2661131) B2661131
theorem B2658875 : Blo 1772087 2658875 := bstep (se 1 (by rfl) ⟨1994156, by rfl⟩ : syracuseStep 2658875 = 3988313) B3988313
theorem B4485719 : Blo 1772087 4485719 := bstep (se 1 (by rfl) ⟨3364289, by rfl⟩ : syracuseStep 4485719 = 6728579) B6728579
theorem B2658935 : Blo 1772087 2658935 := bstep (se 1 (by rfl) ⟨1994201, by rfl⟩ : syracuseStep 2658935 = 3988403) B3988403
theorem B2658959 : Blo 1772087 2658959 := bstep (se 1 (by rfl) ⟨1994219, by rfl⟩ : syracuseStep 2658959 = 3988439) B3988439
theorem B2659001 : Blo 1772087 2659001 := bstep (se 2 (by rfl) ⟨997125, by rfl⟩ : syracuseStep 2659001 = 1994251) B1994251
theorem B11358913 : Blo 1772087 11358913 := bstep (se 2 (by rfl) ⟨4259592, by rfl⟩ : syracuseStep 11358913 = 8519185) B8519185
theorem B2659079 : Blo 1772087 2659079 := bstep (se 1 (by rfl) ⟨1994309, by rfl⟩ : syracuseStep 2659079 = 3988619) B3988619
theorem B2659115 : Blo 1772087 2659115 := bstep (se 1 (by rfl) ⟨1994336, by rfl⟩ : syracuseStep 2659115 = 3988673) B3988673
theorem B2659145 : Blo 1772087 2659145 := bstep (se 2 (by rfl) ⟨997179, by rfl⟩ : syracuseStep 2659145 = 1994359) B1994359
theorem B2159479 : Blo 1772087 2159479 := bstep (se 1 (by rfl) ⟨1619609, by rfl⟩ : syracuseStep 2159479 = 3239219) B3239219
theorem B1995655 : Blo 1772087 1995655 := bstep (se 1 (by rfl) ⟨1496741, by rfl⟩ : syracuseStep 1995655 = 2993483) B2993483
theorem B10097561 : Blo 1772087 10097561 := bstep (se 2 (by rfl) ⟨3786585, by rfl⟩ : syracuseStep 10097561 = 7573171) B7573171
theorem B2659259 : Blo 1772087 2659259 := bstep (se 1 (by rfl) ⟨1994444, by rfl⟩ : syracuseStep 2659259 = 3988889) B3988889
theorem B8516573 : Blo 1772087 8516573 := bstep (se 3 (by rfl) ⟨1596857, by rfl⟩ : syracuseStep 8516573 = 3193715) B3193715
theorem B2659319 : Blo 1772087 2659319 := bstep (se 1 (by rfl) ⟨1994489, by rfl⟩ : syracuseStep 2659319 = 3988979) B3988979
theorem B15356939 : Blo 1772087 15356939 := bstep (se 1 (by rfl) ⟨11517704, by rfl⟩ : syracuseStep 15356939 = 23035409) B23035409
theorem B2659343 : Blo 1772087 2659343 := bstep (se 1 (by rfl) ⟨1994507, by rfl⟩ : syracuseStep 2659343 = 3989015) B3989015
theorem B2659385 : Blo 1772087 2659385 := bstep (se 2 (by rfl) ⟨997269, by rfl⟩ : syracuseStep 2659385 = 1994539) B1994539
theorem B1995835 : Blo 1772087 1995835 := bstep (se 1 (by rfl) ⟨1496876, by rfl⟩ : syracuseStep 1995835 = 2993753) B2993753
theorem B8975447 : Blo 1772087 8975447 := bstep (se 1 (by rfl) ⟨6731585, by rfl⟩ : syracuseStep 8975447 = 13463171) B13463171
theorem B2659463 : Blo 1772087 2659463 := bstep (se 1 (by rfl) ⟨1994597, by rfl⟩ : syracuseStep 2659463 = 3989195) B3989195
theorem B2659499 : Blo 1772087 2659499 := bstep (se 1 (by rfl) ⟨1994624, by rfl⟩ : syracuseStep 2659499 = 3989249) B3989249
theorem B2659529 : Blo 1772087 2659529 := bstep (se 2 (by rfl) ⟨997323, by rfl⟩ : syracuseStep 2659529 = 1994647) B1994647
theorem B6731009 : Blo 1772087 6731009 := bstep (se 2 (by rfl) ⟨2524128, by rfl⟩ : syracuseStep 6731009 = 5048257) B5048257
theorem B8516897 : Blo 1772087 8516897 := bstep (se 2 (by rfl) ⟨3193836, by rfl⟩ : syracuseStep 8516897 = 6387673) B6387673
theorem B2659643 : Blo 1772087 2659643 := bstep (se 1 (by rfl) ⟨1994732, by rfl⟩ : syracuseStep 2659643 = 3989465) B3989465
theorem B2659703 : Blo 1772087 2659703 := bstep (se 1 (by rfl) ⟨1994777, by rfl⟩ : syracuseStep 2659703 = 3989555) B3989555
theorem B2659727 : Blo 1772087 2659727 := bstep (se 1 (by rfl) ⟨1994795, by rfl⟩ : syracuseStep 2659727 = 3989591) B3989591
theorem B2397583 : Blo 1772087 2397583 := bstep (se 1 (by rfl) ⟨1798187, by rfl⟩ : syracuseStep 2397583 = 3596375) B3596375
theorem B5985683 : Blo 1772087 5985683 := bstep (se 1 (by rfl) ⟨4489262, by rfl⟩ : syracuseStep 5985683 = 8978525) B8978525
theorem B2659769 : Blo 1772087 2659769 := bstep (se 2 (by rfl) ⟨997413, by rfl⟩ : syracuseStep 2659769 = 1994827) B1994827
theorem B2659847 : Blo 1772087 2659847 := bstep (se 1 (by rfl) ⟨1994885, by rfl⟩ : syracuseStep 2659847 = 3989771) B3989771
theorem B6387211 : Blo 1772087 6387211 := bstep (se 1 (by rfl) ⟨4790408, by rfl⟩ : syracuseStep 6387211 = 9580817) B9580817
theorem B2659883 : Blo 1772087 2659883 := bstep (se 1 (by rfl) ⟨1994912, by rfl⟩ : syracuseStep 2659883 = 3989825) B3989825
theorem B3364411 : Blo 1772087 3364411 := bstep (se 1 (by rfl) ⟨2523308, by rfl⟩ : syracuseStep 3364411 = 5046617) B5046617
theorem B8975933 : Blo 1772087 8975933 := bstep (se 3 (by rfl) ⟨1682987, by rfl⟩ : syracuseStep 8975933 = 3365975) B3365975
theorem B17036867 : Blo 1772087 17036867 := bstep (se 1 (by rfl) ⟨12777650, by rfl⟩ : syracuseStep 17036867 = 25555301) B25555301
theorem B2659913 : Blo 1772087 2659913 := bstep (se 2 (by rfl) ⟨997467, by rfl⟩ : syracuseStep 2659913 = 1994935) B1994935
theorem B3364487 : Blo 1772087 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B2660027 : Blo 1772087 2660027 := bstep (se 1 (by rfl) ⟨1995020, by rfl⟩ : syracuseStep 2660027 = 3990041) B3990041
theorem B19175129 : Blo 1772087 19175129 := bstep (se 2 (by rfl) ⟨7190673, by rfl⟩ : syracuseStep 19175129 = 14381347) B14381347
theorem B2660087 : Blo 1772087 2660087 := bstep (se 1 (by rfl) ⟨1995065, by rfl⟩ : syracuseStep 2660087 = 3990131) B3990131
theorem B3987215 : Blo 1772087 3987215 := bstep (se 1 (by rfl) ⟨2990411, by rfl⟩ : syracuseStep 3987215 = 5980823) B5980823
theorem B2660111 : Blo 1772087 2660111 := bstep (se 1 (by rfl) ⟨1995083, by rfl⟩ : syracuseStep 2660111 = 3990167) B3990167
theorem B3987233 : Blo 1772087 3987233 := bstep (se 2 (by rfl) ⟨1495212, by rfl⟩ : syracuseStep 3987233 = 2990425) B2990425
theorem B2840363 : Blo 1772087 2840363 := bstep (se 1 (by rfl) ⟨2130272, by rfl⟩ : syracuseStep 2840363 = 4260545) B4260545
theorem B2660153 : Blo 1772087 2660153 := bstep (se 2 (by rfl) ⟨997557, by rfl⟩ : syracuseStep 2660153 = 1995115) B1995115
theorem B8517511 : Blo 1772087 8517511 := bstep (se 1 (by rfl) ⟨6388133, by rfl⟩ : syracuseStep 8517511 = 12776267) B12776267
theorem B2660231 : Blo 1772087 2660231 := bstep (se 1 (by rfl) ⟨1995173, by rfl⟩ : syracuseStep 2660231 = 3990347) B3990347
theorem B2660267 : Blo 1772087 2660267 := bstep (se 1 (by rfl) ⟨1995200, by rfl⟩ : syracuseStep 2660267 = 3990401) B3990401
theorem B2660297 : Blo 1772087 2660297 := bstep (se 2 (by rfl) ⟨997611, by rfl⟩ : syracuseStep 2660297 = 1995223) B1995223
theorem B9099217 : Blo 1772087 9099217 := bstep (se 2 (by rfl) ⟨3412206, by rfl⟩ : syracuseStep 9099217 = 6824413) B6824413
theorem B10786769 : Blo 1772087 10786769 := bstep (se 2 (by rfl) ⟨4045038, by rfl⟩ : syracuseStep 10786769 = 8090077) B8090077
theorem B13645847 : Blo 1772087 13645847 := bstep (se 1 (by rfl) ⟨10234385, by rfl⟩ : syracuseStep 13645847 = 20468771) B20468771
theorem B3364897 : Blo 1772087 3364897 := bstep (se 2 (by rfl) ⟨1261836, by rfl⟩ : syracuseStep 3364897 = 2523673) B2523673
theorem B2660411 : Blo 1772087 2660411 := bstep (se 1 (by rfl) ⟨1995308, by rfl⟩ : syracuseStep 2660411 = 3990617) B3990617
theorem B3987575 : Blo 1772087 3987575 := bstep (se 1 (by rfl) ⟨2990681, by rfl⟩ : syracuseStep 3987575 = 5981363) B5981363
theorem B2660471 : Blo 1772087 2660471 := bstep (se 1 (by rfl) ⟨1995353, by rfl⟩ : syracuseStep 2660471 = 3990707) B3990707
theorem B2660495 : Blo 1772087 2660495 := bstep (se 1 (by rfl) ⟨1995371, by rfl⟩ : syracuseStep 2660495 = 3990743) B3990743
theorem B2660537 : Blo 1772087 2660537 := bstep (se 2 (by rfl) ⟨997701, by rfl⟩ : syracuseStep 2660537 = 1995403) B1995403
theorem B2660615 : Blo 1772087 2660615 := bstep (se 1 (by rfl) ⟨1995461, by rfl⟩ : syracuseStep 2660615 = 3990923) B3990923
theorem B3987755 : Blo 1772087 3987755 := bstep (se 1 (by rfl) ⟨2990816, by rfl⟩ : syracuseStep 3987755 = 5981633) B5981633
theorem B2660651 : Blo 1772087 2660651 := bstep (se 1 (by rfl) ⟨1995488, by rfl⟩ : syracuseStep 2660651 = 3990977) B3990977
theorem B2275627 : Blo 1772087 2275627 := bstep (se 1 (by rfl) ⟨1706720, by rfl⟩ : syracuseStep 2275627 = 3413441) B3413441
theorem B2660681 : Blo 1772087 2660681 := bstep (se 2 (by rfl) ⟨997755, by rfl⟩ : syracuseStep 2660681 = 1995511) B1995511
theorem B3365239 : Blo 1772087 3365239 := bstep (se 1 (by rfl) ⟨2523929, by rfl⟩ : syracuseStep 3365239 = 5047859) B5047859
theorem B16177553 : Blo 1772087 16177553 := bstep (se 2 (by rfl) ⟨6066582, by rfl⟩ : syracuseStep 16177553 = 12133165) B12133165
theorem B6732179 : Blo 1772087 6732179 := bstep (se 1 (by rfl) ⟨5049134, by rfl⟩ : syracuseStep 6732179 = 10098269) B10098269
theorem B2660795 : Blo 1772087 2660795 := bstep (se 1 (by rfl) ⟨1995596, by rfl⟩ : syracuseStep 2660795 = 3991193) B3991193
theorem B2660855 : Blo 1772087 2660855 := bstep (se 1 (by rfl) ⟨1995641, by rfl⟩ : syracuseStep 2660855 = 3991283) B3991283
theorem B2660879 : Blo 1772087 2660879 := bstep (se 1 (by rfl) ⟨1995659, by rfl⟩ : syracuseStep 2660879 = 3991319) B3991319
theorem B2660921 : Blo 1772087 2660921 := bstep (se 2 (by rfl) ⟨997845, by rfl⟩ : syracuseStep 2660921 = 1995691) B1995691
theorem B4487795 : Blo 1772087 4487795 := bstep (se 1 (by rfl) ⟨3365846, by rfl⟩ : syracuseStep 4487795 = 6731693) B6731693
theorem B2660999 : Blo 1772087 2660999 := bstep (se 1 (by rfl) ⟨1995749, by rfl⟩ : syracuseStep 2660999 = 3991499) B3991499
theorem B3988115 : Blo 1772087 3988115 := bstep (se 1 (by rfl) ⟨2991086, by rfl⟩ : syracuseStep 3988115 = 5982173) B5982173
theorem B2661035 : Blo 1772087 2661035 := bstep (se 1 (by rfl) ⟨1995776, by rfl⟩ : syracuseStep 2661035 = 3991553) B3991553
theorem B3988169 : Blo 1772087 3988169 := bstep (se 2 (by rfl) ⟨1495563, by rfl⟩ : syracuseStep 3988169 = 2991127) B2991127
theorem B2661065 : Blo 1772087 2661065 := bstep (se 2 (by rfl) ⟨997899, by rfl⟩ : syracuseStep 2661065 = 1995799) B1995799
theorem B5987087 : Blo 1772087 5987087 := bstep (se 1 (by rfl) ⟨4490315, by rfl⟩ : syracuseStep 5987087 = 8980631) B8980631
theorem B9583393 : Blo 1772087 9583393 := bstep (se 2 (by rfl) ⟨3593772, by rfl⟩ : syracuseStep 9583393 = 7187545) B7187545
theorem B10787617 : Blo 1772087 10787617 := bstep (se 2 (by rfl) ⟨4045356, by rfl⟩ : syracuseStep 10787617 = 8090713) B8090713
theorem B2243371 : Blo 1772087 2243371 := bstep (se 1 (by rfl) ⟨1682528, by rfl⟩ : syracuseStep 2243371 = 3365057) B3365057
theorem B10779443 : Blo 1772087 10779443 := bstep (se 1 (by rfl) ⟨8084582, by rfl⟩ : syracuseStep 10779443 = 16169165) B16169165
theorem B6732679 : Blo 1772087 6732679 := bstep (se 1 (by rfl) ⟨5049509, by rfl⟩ : syracuseStep 6732679 = 10099019) B10099019
theorem B10787863 : Blo 1772087 10787863 := bstep (se 1 (by rfl) ⟨8090897, by rfl⟩ : syracuseStep 10787863 = 16181795) B16181795
theorem B5987357 : Blo 1772087 5987357 := bstep (se 3 (by rfl) ⟨1122629, by rfl⟩ : syracuseStep 5987357 = 2245259) B2245259
theorem B4488311 : Blo 1772087 4488311 := bstep (se 1 (by rfl) ⟨3366233, by rfl⟩ : syracuseStep 4488311 = 6732467) B6732467
theorem B7576847 : Blo 1772087 7576847 := bstep (se 1 (by rfl) ⟨5682635, by rfl⟩ : syracuseStep 7576847 = 11365271) B11365271
theorem B8977715 : Blo 1772087 8977715 := bstep (se 1 (by rfl) ⟨6733286, by rfl⟩ : syracuseStep 8977715 = 13466573) B13466573
theorem B3988871 : Blo 1772087 3988871 := bstep (se 1 (by rfl) ⟨2991653, by rfl⟩ : syracuseStep 3988871 = 5983307) B5983307
theorem B4259371 : Blo 1772087 4259371 := bstep (se 1 (by rfl) ⟨3194528, by rfl⟩ : syracuseStep 4259371 = 6389057) B6389057
theorem B3989051 : Blo 1772087 3989051 := bstep (se 1 (by rfl) ⟨2991788, by rfl⟩ : syracuseStep 3989051 = 5983577) B5983577
theorem B15146615 : Blo 1772087 15146615 := bstep (se 1 (by rfl) ⟨11359961, by rfl⟩ : syracuseStep 15146615 = 22719923) B22719923
theorem B8978039 : Blo 1772087 8978039 := bstep (se 1 (by rfl) ⟨6733529, by rfl⟩ : syracuseStep 8978039 = 13467059) B13467059
theorem B3989177 : Blo 1772087 3989177 := bstep (se 2 (by rfl) ⟨1495941, by rfl⟩ : syracuseStep 3989177 = 2991883) B2991883
theorem B2244343 : Blo 1772087 2244343 := bstep (se 1 (by rfl) ⟨1683257, by rfl⟩ : syracuseStep 2244343 = 3366515) B3366515
theorem B4792097 : Blo 1772087 4792097 := bstep (se 2 (by rfl) ⟨1797036, by rfl⟩ : syracuseStep 4792097 = 3594073) B3594073
theorem B4259699 : Blo 1772087 4259699 := bstep (se 1 (by rfl) ⟨3194774, by rfl⟩ : syracuseStep 4259699 = 6389549) B6389549
theorem B12787571 : Blo 1772087 12787571 := bstep (se 1 (by rfl) ⟨9590678, by rfl⟩ : syracuseStep 12787571 = 19181357) B19181357
theorem B3194759 : Blo 1772087 3194759 := bstep (se 1 (by rfl) ⟨2396069, by rfl⟩ : syracuseStep 3194759 = 4792139) B4792139
theorem B68181911 : Blo 1772087 68181911 := bstep (se 1 (by rfl) ⟨51136433, by rfl⟩ : syracuseStep 68181911 = 102272867) B102272867
theorem B13467545 : Blo 1772087 13467545 := bstep (se 2 (by rfl) ⟨5050329, by rfl⟩ : syracuseStep 13467545 = 10100659) B10100659
theorem B3366841 : Blo 1772087 3366841 := bstep (se 2 (by rfl) ⟨1262565, by rfl⟩ : syracuseStep 3366841 = 2525131) B2525131
theorem B25575371 : Blo 1772087 25575371 := bstep (se 1 (by rfl) ⟨19181528, by rfl⟩ : syracuseStep 25575371 = 38363057) B38363057
theorem B13131779 : Blo 1772087 13131779 := bstep (se 1 (by rfl) ⟨9848834, by rfl⟩ : syracuseStep 13131779 = 19697669) B19697669
theorem B54575117 : Blo 1772087 54575117 := bstep (se 3 (by rfl) ⟨10232834, by rfl⟩ : syracuseStep 54575117 = 20465669) B20465669
theorem B40951837 : Blo 1772087 40951837 := bstep (se 3 (by rfl) ⟨7678469, by rfl⟩ : syracuseStep 40951837 = 15356939) B15356939
theorem B36388925 : Blo 1772087 36388925 := bstep (se 3 (by rfl) ⟨6822923, by rfl⟩ : syracuseStep 36388925 = 13645847) B13645847
theorem B15155363 : Blo 1772087 15155363 := bstep (se 1 (by rfl) ⟨11366522, by rfl⟩ : syracuseStep 15155363 = 22733045) B22733045
theorem B24264971 : Blo 1772087 24264971 := bstep (se 1 (by rfl) ⟨18198728, by rfl⟩ : syracuseStep 24264971 = 36397457) B36397457
theorem B4489577 : Blo 1772087 4489577 := bstep (se 2 (by rfl) ⟨1683591, by rfl⟩ : syracuseStep 4489577 = 3367183) B3367183
theorem B2990479 : Blo 1772087 2990479 := bstep (se 1 (by rfl) ⟨2242859, by rfl⟩ : syracuseStep 2990479 = 4485719) B4485719
theorem B45441485 : Blo 1772087 45441485 := bstep (se 3 (by rfl) ⟨8520278, by rfl⟩ : syracuseStep 45441485 = 17040557) B17040557
theorem B3367433 : Blo 1772087 3367433 := bstep (se 2 (by rfl) ⟨1262787, by rfl⟩ : syracuseStep 3367433 = 2525575) B2525575
theorem B3990113 : Blo 1772087 3990113 := bstep (se 2 (by rfl) ⟨1496292, by rfl⟩ : syracuseStep 3990113 = 2992585) B2992585
theorem B5677715 : Blo 1772087 5677715 := bstep (se 1 (by rfl) ⟨4258286, by rfl⟩ : syracuseStep 5677715 = 8516573) B8516573
theorem B4260601 : Blo 1772087 4260601 := bstep (se 2 (by rfl) ⟨1597725, by rfl⟩ : syracuseStep 4260601 = 3195451) B3195451
theorem B5677931 : Blo 1772087 5677931 := bstep (se 1 (by rfl) ⟨4258448, by rfl⟩ : syracuseStep 5677931 = 8516897) B8516897
theorem B3990455 : Blo 1772087 3990455 := bstep (se 1 (by rfl) ⟨2992841, by rfl⟩ : syracuseStep 3990455 = 5985683) B5985683
theorem B2991161 : Blo 1772087 2991161 := bstep (se 2 (by rfl) ⟨1121685, by rfl⟩ : syracuseStep 2991161 = 2243371) B2243371
theorem B6734927 : Blo 1772087 6734927 := bstep (se 1 (by rfl) ⟨5051195, by rfl⟩ : syracuseStep 6734927 = 10102391) B10102391
theorem B1893575 : Blo 1772087 1893575 := bstep (se 1 (by rfl) ⟨1420181, by rfl⟩ : syracuseStep 1893575 = 2840363) B2840363
theorem B8979659 : Blo 1772087 8979659 := bstep (se 1 (by rfl) ⟨6734744, by rfl⟩ : syracuseStep 8979659 = 13469489) B13469489
theorem B3196115 : Blo 1772087 3196115 := bstep (se 1 (by rfl) ⟨2397086, by rfl⟩ : syracuseStep 3196115 = 4794173) B4794173
theorem B6735095 : Blo 1772087 6735095 := bstep (se 1 (by rfl) ⟨5051321, by rfl⟩ : syracuseStep 6735095 = 10102643) B10102643
theorem B140019121 : Blo 1772087 140019121 := bstep (se 2 (by rfl) ⟨52507170, by rfl⟩ : syracuseStep 140019121 = 105014341) B105014341
theorem B8971721 : Blo 1772087 8971721 := bstep (se 2 (by rfl) ⟨3364395, by rfl⟩ : syracuseStep 8971721 = 6728791) B6728791
theorem B3991049 : Blo 1772087 3991049 := bstep (se 2 (by rfl) ⟨1496643, by rfl⟩ : syracuseStep 3991049 = 2993287) B2993287
theorem B13649447 : Blo 1772087 13649447 := bstep (se 1 (by rfl) ⟨10237085, by rfl⟩ : syracuseStep 13649447 = 20474171) B20474171
theorem B2991863 : Blo 1772087 2991863 := bstep (se 1 (by rfl) ⟨2243897, by rfl⟩ : syracuseStep 2991863 = 4487795) B4487795
theorem B2525023 : Blo 1772087 2525023 := bstep (se 1 (by rfl) ⟨1893767, by rfl⟩ : syracuseStep 2525023 = 3787535) B3787535
theorem B3991391 : Blo 1772087 3991391 := bstep (se 1 (by rfl) ⟨2993543, by rfl⟩ : syracuseStep 3991391 = 5987087) B5987087
theorem B7186295 : Blo 1772087 7186295 := bstep (se 1 (by rfl) ⟨5389721, by rfl⟩ : syracuseStep 7186295 = 10779443) B10779443
theorem B6064055 : Blo 1772087 6064055 := bstep (se 1 (by rfl) ⟨4548041, by rfl⟩ : syracuseStep 6064055 = 9096083) B9096083
theorem B5982227 : Blo 1772087 5982227 := bstep (se 1 (by rfl) ⟨4486670, by rfl⟩ : syracuseStep 5982227 = 8973341) B8973341
theorem B3991571 : Blo 1772087 3991571 := bstep (se 1 (by rfl) ⟨2993678, by rfl⟩ : syracuseStep 3991571 = 5987357) B5987357
theorem B5679161 : Blo 1772087 5679161 := bstep (se 2 (by rfl) ⟨2129685, by rfl⟩ : syracuseStep 5679161 = 4259371) B4259371
theorem B2992207 : Blo 1772087 2992207 := bstep (se 1 (by rfl) ⟨2244155, by rfl⟩ : syracuseStep 2992207 = 4488311) B4488311
theorem B8972369 : Blo 1772087 8972369 := bstep (se 2 (by rfl) ⟨3364638, by rfl⟩ : syracuseStep 8972369 = 6729277) B6729277
theorem B15149213 : Blo 1772087 15149213 := bstep (se 3 (by rfl) ⟨2840477, by rfl⟩ : syracuseStep 15149213 = 5680955) B5680955
theorem B2992457 : Blo 1772087 2992457 := bstep (se 2 (by rfl) ⟨1122171, by rfl⟩ : syracuseStep 2992457 = 2244343) B2244343
theorem B2918729 : Blo 1772087 2918729 := bstep (se 2 (by rfl) ⟨1094523, by rfl⟩ : syracuseStep 2918729 = 2189047) B2189047
theorem B5982551 : Blo 1772087 5982551 := bstep (se 1 (by rfl) ⟨4486913, by rfl⟩ : syracuseStep 5982551 = 8973827) B8973827
theorem B8194409 : Blo 1772087 8194409 := bstep (se 2 (by rfl) ⟨3072903, by rfl⟩ : syracuseStep 8194409 = 6145807) B6145807
theorem B11356681 : Blo 1772087 11356681 := bstep (se 2 (by rfl) ⟨4258755, by rfl⟩ : syracuseStep 11356681 = 8517511) B8517511
theorem B1772111 : Blo 1772087 1772111 := bstep (se 1 (by rfl) ⟨1329083, by rfl⟩ : syracuseStep 1772111 = 2658167) B2658167
theorem B1772127 : Blo 1772087 1772127 := bstep (se 1 (by rfl) ⟨1329095, by rfl⟩ : syracuseStep 1772127 = 2658191) B2658191
theorem B1772155 : Blo 1772087 1772155 := bstep (se 1 (by rfl) ⟨1329116, by rfl⟩ : syracuseStep 1772155 = 2658233) B2658233
theorem B17050247 : Blo 1772087 17050247 := bstep (se 1 (by rfl) ⟨12787685, by rfl⟩ : syracuseStep 17050247 = 25575371) B25575371
theorem B6392459 : Blo 1772087 6392459 := bstep (se 1 (by rfl) ⟨4794344, by rfl⟩ : syracuseStep 6392459 = 9588689) B9588689
theorem B1772207 : Blo 1772087 1772207 := bstep (se 1 (by rfl) ⟨1329155, by rfl⟩ : syracuseStep 1772207 = 2658311) B2658311
theorem B1772231 : Blo 1772087 1772231 := bstep (se 1 (by rfl) ⟨1329173, by rfl⟩ : syracuseStep 1772231 = 2658347) B2658347
theorem B1772251 : Blo 1772087 1772251 := bstep (se 1 (by rfl) ⟨1329188, by rfl⟩ : syracuseStep 1772251 = 2658377) B2658377
theorem B2992889 : Blo 1772087 2992889 := bstep (se 2 (by rfl) ⟨1122333, by rfl⟩ : syracuseStep 2992889 = 2244667) B2244667
theorem B1772327 : Blo 1772087 1772327 := bstep (se 1 (by rfl) ⟨1329245, by rfl⟩ : syracuseStep 1772327 = 2658491) B2658491
theorem B1772367 : Blo 1772087 1772367 := bstep (se 1 (by rfl) ⟨1329275, by rfl⟩ : syracuseStep 1772367 = 2658551) B2658551
theorem B1772383 : Blo 1772087 1772383 := bstep (se 1 (by rfl) ⟨1329287, by rfl⟩ : syracuseStep 1772383 = 2658575) B2658575
theorem B1772411 : Blo 1772087 1772411 := bstep (se 1 (by rfl) ⟨1329308, by rfl⟩ : syracuseStep 1772411 = 2658617) B2658617
theorem B1796987 : Blo 1772087 1796987 := bstep (se 1 (by rfl) ⟨1347740, by rfl⟩ : syracuseStep 1796987 = 2695481) B2695481
theorem B6728609 : Blo 1772087 6728609 := bstep (se 2 (by rfl) ⟨2523228, by rfl⟩ : syracuseStep 6728609 = 5046457) B5046457
theorem B1772463 : Blo 1772087 1772463 := bstep (se 1 (by rfl) ⟨1329347, by rfl⟩ : syracuseStep 1772463 = 2658695) B2658695
theorem B2993071 : Blo 1772087 2993071 := bstep (se 1 (by rfl) ⟨2244803, by rfl⟩ : syracuseStep 2993071 = 4489607) B4489607
theorem B3836855 : Blo 1772087 3836855 := bstep (se 1 (by rfl) ⟨2877641, by rfl⟩ : syracuseStep 3836855 = 5755283) B5755283
theorem B1772487 : Blo 1772087 1772487 := bstep (se 1 (by rfl) ⟨1329365, by rfl⟩ : syracuseStep 1772487 = 2658731) B2658731
theorem B1772507 : Blo 1772087 1772507 := bstep (se 1 (by rfl) ⟨1329380, by rfl⟩ : syracuseStep 1772507 = 2658761) B2658761
theorem B5680135 : Blo 1772087 5680135 := bstep (se 1 (by rfl) ⟨4260101, by rfl⟩ : syracuseStep 5680135 = 8520203) B8520203
theorem B2993159 : Blo 1772087 2993159 := bstep (se 1 (by rfl) ⟨2244869, by rfl⟩ : syracuseStep 2993159 = 4489739) B4489739
theorem B1772583 : Blo 1772087 1772583 := bstep (se 1 (by rfl) ⟨1329437, by rfl⟩ : syracuseStep 1772583 = 2658875) B2658875
theorem B3034169 : Blo 1772087 3034169 := bstep (se 2 (by rfl) ⟨1137813, by rfl⟩ : syracuseStep 3034169 = 2275627) B2275627
theorem B1772623 : Blo 1772087 1772623 := bstep (se 1 (by rfl) ⟨1329467, by rfl⟩ : syracuseStep 1772623 = 2658935) B2658935
theorem B1772639 : Blo 1772087 1772639 := bstep (se 1 (by rfl) ⟨1329479, by rfl⟩ : syracuseStep 1772639 = 2658959) B2658959
theorem B6827123 : Blo 1772087 6827123 := bstep (se 1 (by rfl) ⟨5120342, by rfl⟩ : syracuseStep 6827123 = 10240685) B10240685
theorem B1772667 : Blo 1772087 1772667 := bstep (se 1 (by rfl) ⟨1329500, by rfl⟩ : syracuseStep 1772667 = 2659001) B2659001
theorem B1772719 : Blo 1772087 1772719 := bstep (se 1 (by rfl) ⟨1329539, by rfl⟩ : syracuseStep 1772719 = 2659079) B2659079
theorem B1993927 : Blo 1772087 1993927 := bstep (se 1 (by rfl) ⟨1495445, by rfl⟩ : syracuseStep 1993927 = 2990891) B2990891
theorem B1772743 : Blo 1772087 1772743 := bstep (se 1 (by rfl) ⟨1329557, by rfl⟩ : syracuseStep 1772743 = 2659115) B2659115
theorem B1772763 : Blo 1772087 1772763 := bstep (se 1 (by rfl) ⟨1329572, by rfl⟩ : syracuseStep 1772763 = 2659145) B2659145
theorem B3411193 : Blo 1772087 3411193 := bstep (se 2 (by rfl) ⟨1279197, by rfl⟩ : syracuseStep 3411193 = 2558395) B2558395
theorem B1772839 : Blo 1772087 1772839 := bstep (se 1 (by rfl) ⟨1329629, by rfl⟩ : syracuseStep 1772839 = 2659259) B2659259
theorem B1772879 : Blo 1772087 1772879 := bstep (se 1 (by rfl) ⟨1329659, by rfl⟩ : syracuseStep 1772879 = 2659319) B2659319
theorem B1772895 : Blo 1772087 1772895 := bstep (se 1 (by rfl) ⟨1329671, by rfl⟩ : syracuseStep 1772895 = 2659343) B2659343
theorem B2993503 : Blo 1772087 2993503 := bstep (se 1 (by rfl) ⟨2245127, by rfl⟩ : syracuseStep 2993503 = 4490255) B4490255
theorem B6729065 : Blo 1772087 6729065 := bstep (se 2 (by rfl) ⟨2523399, by rfl⟩ : syracuseStep 6729065 = 5046799) B5046799
theorem B1772923 : Blo 1772087 1772923 := bstep (se 1 (by rfl) ⟨1329692, by rfl⟩ : syracuseStep 1772923 = 2659385) B2659385
theorem B11365757 : Blo 1772087 11365757 := bstep (se 3 (by rfl) ⟨2131079, by rfl⟩ : syracuseStep 11365757 = 4262159) B4262159
theorem B5983631 : Blo 1772087 5983631 := bstep (se 1 (by rfl) ⟨4487723, by rfl⟩ : syracuseStep 5983631 = 8975447) B8975447
theorem B1772975 : Blo 1772087 1772975 := bstep (se 1 (by rfl) ⟨1329731, by rfl⟩ : syracuseStep 1772975 = 2659463) B2659463
theorem B2993591 : Blo 1772087 2993591 := bstep (se 1 (by rfl) ⟨2245193, by rfl⟩ : syracuseStep 2993591 = 4490387) B4490387
theorem B1772999 : Blo 1772087 1772999 := bstep (se 1 (by rfl) ⟨1329749, by rfl⟩ : syracuseStep 1772999 = 2659499) B2659499
theorem B1773019 : Blo 1772087 1773019 := bstep (se 1 (by rfl) ⟨1329764, by rfl⟩ : syracuseStep 1773019 = 2659529) B2659529
theorem B1773095 : Blo 1772087 1773095 := bstep (se 1 (by rfl) ⟨1329821, by rfl⟩ : syracuseStep 1773095 = 2659643) B2659643
theorem B1773135 : Blo 1772087 1773135 := bstep (se 1 (by rfl) ⟨1329851, by rfl⟩ : syracuseStep 1773135 = 2659703) B2659703
theorem B1773151 : Blo 1772087 1773151 := bstep (se 1 (by rfl) ⟨1329863, by rfl⟩ : syracuseStep 1773151 = 2659727) B2659727
theorem B1773179 : Blo 1772087 1773179 := bstep (se 1 (by rfl) ⟨1329884, by rfl⟩ : syracuseStep 1773179 = 2659769) B2659769
theorem B1773231 : Blo 1772087 1773231 := bstep (se 1 (by rfl) ⟨1329923, by rfl⟩ : syracuseStep 1773231 = 2659847) B2659847
theorem B1773255 : Blo 1772087 1773255 := bstep (se 1 (by rfl) ⟨1329941, by rfl⟩ : syracuseStep 1773255 = 2659883) B2659883
theorem B5983955 : Blo 1772087 5983955 := bstep (se 1 (by rfl) ⟨4487966, by rfl⟩ : syracuseStep 5983955 = 8975933) B8975933
theorem B11357911 : Blo 1772087 11357911 := bstep (se 1 (by rfl) ⟨8518433, by rfl⟩ : syracuseStep 11357911 = 17036867) B17036867
theorem B1773275 : Blo 1772087 1773275 := bstep (se 1 (by rfl) ⟨1329956, by rfl⟩ : syracuseStep 1773275 = 2659913) B2659913
theorem B1773351 : Blo 1772087 1773351 := bstep (se 1 (by rfl) ⟨1330013, by rfl⟩ : syracuseStep 1773351 = 2660027) B2660027
theorem B12783419 : Blo 1772087 12783419 := bstep (se 1 (by rfl) ⟨9587564, by rfl⟩ : syracuseStep 12783419 = 19175129) B19175129
theorem B1773391 : Blo 1772087 1773391 := bstep (se 1 (by rfl) ⟨1330043, by rfl⟩ : syracuseStep 1773391 = 2660087) B2660087
theorem B2658143 : Blo 1772087 2658143 := bstep (se 1 (by rfl) ⟨1993607, by rfl⟩ : syracuseStep 2658143 = 3987215) B3987215
theorem B1773407 : Blo 1772087 1773407 := bstep (se 1 (by rfl) ⟨1330055, by rfl⟩ : syracuseStep 1773407 = 2660111) B2660111
theorem B2658155 : Blo 1772087 2658155 := bstep (se 1 (by rfl) ⟨1993616, by rfl⟩ : syracuseStep 2658155 = 3987233) B3987233
theorem B6729581 : Blo 1772087 6729581 := bstep (se 3 (by rfl) ⟨1261796, by rfl⟩ : syracuseStep 6729581 = 2523593) B2523593
theorem B1773435 : Blo 1772087 1773435 := bstep (se 1 (by rfl) ⟨1330076, by rfl⟩ : syracuseStep 1773435 = 2660153) B2660153
theorem B19181447 : Blo 1772087 19181447 := bstep (se 1 (by rfl) ⟨14386085, by rfl⟩ : syracuseStep 19181447 = 28772171) B28772171
theorem B1773487 : Blo 1772087 1773487 := bstep (se 1 (by rfl) ⟨1330115, by rfl⟩ : syracuseStep 1773487 = 2660231) B2660231
theorem B1773511 : Blo 1772087 1773511 := bstep (se 1 (by rfl) ⟨1330133, by rfl⟩ : syracuseStep 1773511 = 2660267) B2660267
theorem B1773531 : Blo 1772087 1773531 := bstep (se 1 (by rfl) ⟨1330148, by rfl⟩ : syracuseStep 1773531 = 2660297) B2660297
theorem B25554959 : Blo 1772087 25554959 := bstep (se 1 (by rfl) ⟨19166219, by rfl⟩ : syracuseStep 25554959 = 38332439) B38332439
theorem B1994791 : Blo 1772087 1994791 := bstep (se 1 (by rfl) ⟨1496093, by rfl⟩ : syracuseStep 1994791 = 2992187) B2992187
theorem B1773607 : Blo 1772087 1773607 := bstep (se 1 (by rfl) ⟨1330205, by rfl⟩ : syracuseStep 1773607 = 2660411) B2660411
theorem B2658383 : Blo 1772087 2658383 := bstep (se 1 (by rfl) ⟨1993787, by rfl⟩ : syracuseStep 2658383 = 3987575) B3987575
theorem B1773647 : Blo 1772087 1773647 := bstep (se 1 (by rfl) ⟨1330235, by rfl⟩ : syracuseStep 1773647 = 2660471) B2660471
theorem B9580625 : Blo 1772087 9580625 := bstep (se 2 (by rfl) ⟨3592734, by rfl⟩ : syracuseStep 9580625 = 7185469) B7185469
theorem B1773663 : Blo 1772087 1773663 := bstep (se 1 (by rfl) ⟨1330247, by rfl⟩ : syracuseStep 1773663 = 2660495) B2660495
theorem B43135091 : Blo 1772087 43135091 := bstep (se 1 (by rfl) ⟨32351318, by rfl⟩ : syracuseStep 43135091 = 64702637) B64702637
theorem B1773691 : Blo 1772087 1773691 := bstep (se 1 (by rfl) ⟨1330268, by rfl⟩ : syracuseStep 1773691 = 2660537) B2660537
theorem B1773743 : Blo 1772087 1773743 := bstep (se 1 (by rfl) ⟨1330307, by rfl⟩ : syracuseStep 1773743 = 2660615) B2660615
theorem B2658503 : Blo 1772087 2658503 := bstep (se 1 (by rfl) ⟨1993877, by rfl⟩ : syracuseStep 2658503 = 3987755) B3987755
theorem B1773767 : Blo 1772087 1773767 := bstep (se 1 (by rfl) ⟨1330325, by rfl⟩ : syracuseStep 1773767 = 2660651) B2660651
theorem B1773787 : Blo 1772087 1773787 := bstep (se 1 (by rfl) ⟨1330340, by rfl⟩ : syracuseStep 1773787 = 2660681) B2660681
theorem B10785035 : Blo 1772087 10785035 := bstep (se 1 (by rfl) ⟨8088776, by rfl⟩ : syracuseStep 10785035 = 16177553) B16177553
theorem B1773863 : Blo 1772087 1773863 := bstep (se 1 (by rfl) ⟨1330397, by rfl⟩ : syracuseStep 1773863 = 2660795) B2660795
theorem B1773903 : Blo 1772087 1773903 := bstep (se 1 (by rfl) ⟨1330427, by rfl⟩ : syracuseStep 1773903 = 2660855) B2660855
theorem B1773919 : Blo 1772087 1773919 := bstep (se 1 (by rfl) ⟨1330439, by rfl⟩ : syracuseStep 1773919 = 2660879) B2660879
theorem B2658665 : Blo 1772087 2658665 := bstep (se 2 (by rfl) ⟨996999, by rfl⟩ : syracuseStep 2658665 = 1993999) B1993999
theorem B1773947 : Blo 1772087 1773947 := bstep (se 1 (by rfl) ⟨1330460, by rfl⟩ : syracuseStep 1773947 = 2660921) B2660921
theorem B1773999 : Blo 1772087 1773999 := bstep (se 1 (by rfl) ⟨1330499, by rfl⟩ : syracuseStep 1773999 = 2660999) B2660999
theorem B2658743 : Blo 1772087 2658743 := bstep (se 1 (by rfl) ⟨1994057, by rfl⟩ : syracuseStep 2658743 = 3988115) B3988115
theorem B1774023 : Blo 1772087 1774023 := bstep (se 1 (by rfl) ⟨1330517, by rfl⟩ : syracuseStep 1774023 = 2661035) B2661035
theorem B2658779 : Blo 1772087 2658779 := bstep (se 1 (by rfl) ⟨1994084, by rfl⟩ : syracuseStep 2658779 = 3988169) B3988169
theorem B1774043 : Blo 1772087 1774043 := bstep (se 1 (by rfl) ⟨1330532, by rfl⟩ : syracuseStep 1774043 = 2661065) B2661065
theorem B8090093 : Blo 1772087 8090093 := bstep (se 3 (by rfl) ⟨1516892, by rfl⟩ : syracuseStep 8090093 = 3033785) B3033785
theorem B6730249 : Blo 1772087 6730249 := bstep (se 2 (by rfl) ⟨2523843, by rfl⟩ : syracuseStep 6730249 = 5047687) B5047687
theorem B6066697 : Blo 1772087 6066697 := bstep (se 2 (by rfl) ⟨2275011, by rfl⟩ : syracuseStep 6066697 = 4550023) B4550023
theorem B8516281 : Blo 1772087 8516281 := bstep (se 2 (by rfl) ⟨3193605, by rfl⟩ : syracuseStep 8516281 = 6387211) B6387211
theorem B4485881 : Blo 1772087 4485881 := bstep (se 2 (by rfl) ⟨1682205, by rfl⟩ : syracuseStep 4485881 = 3364411) B3364411
theorem B25555763 : Blo 1772087 25555763 := bstep (se 1 (by rfl) ⟨19166822, by rfl⟩ : syracuseStep 25555763 = 38333645) B38333645
theorem B5051231 : Blo 1772087 5051231 := bstep (se 1 (by rfl) ⟨3788423, by rfl⟩ : syracuseStep 5051231 = 7576847) B7576847
theorem B5985143 : Blo 1772087 5985143 := bstep (se 1 (by rfl) ⟨4488857, by rfl⟩ : syracuseStep 5985143 = 8977715) B8977715
theorem B4486063 : Blo 1772087 4486063 := bstep (se 1 (by rfl) ⟨3364547, by rfl⟩ : syracuseStep 4486063 = 6729095) B6729095
theorem B2659247 : Blo 1772087 2659247 := bstep (se 1 (by rfl) ⟨1994435, by rfl⟩ : syracuseStep 2659247 = 3988871) B3988871
theorem B2659337 : Blo 1772087 2659337 := bstep (se 2 (by rfl) ⟨997251, by rfl⟩ : syracuseStep 2659337 = 1994503) B1994503
theorem B2659367 : Blo 1772087 2659367 := bstep (se 1 (by rfl) ⟨1994525, by rfl⟩ : syracuseStep 2659367 = 3989051) B3989051
theorem B10097743 : Blo 1772087 10097743 := bstep (se 1 (by rfl) ⟨7573307, by rfl⟩ : syracuseStep 10097743 = 15146615) B15146615
theorem B5985359 : Blo 1772087 5985359 := bstep (se 1 (by rfl) ⟨4489019, by rfl⟩ : syracuseStep 5985359 = 8978039) B8978039
theorem B51106909 : Blo 1772087 51106909 := bstep (se 3 (by rfl) ⟨9582545, by rfl⟩ : syracuseStep 51106909 = 19165091) B19165091
theorem B2659451 : Blo 1772087 2659451 := bstep (se 1 (by rfl) ⟨1994588, by rfl⟩ : syracuseStep 2659451 = 3989177) B3989177
theorem B2839799 : Blo 1772087 2839799 := bstep (se 1 (by rfl) ⟨2129849, by rfl⟩ : syracuseStep 2839799 = 4259699) B4259699
theorem B8525047 : Blo 1772087 8525047 := bstep (se 1 (by rfl) ⟨6393785, by rfl⟩ : syracuseStep 8525047 = 12787571) B12787571
theorem B2659577 : Blo 1772087 2659577 := bstep (se 2 (by rfl) ⟨997341, by rfl⟩ : syracuseStep 2659577 = 1994683) B1994683
theorem B2397433 : Blo 1772087 2397433 := bstep (se 2 (by rfl) ⟨899037, by rfl⟩ : syracuseStep 2397433 = 1798075) B1798075
theorem B45454607 : Blo 1772087 45454607 := bstep (se 1 (by rfl) ⟨34090955, by rfl⟩ : syracuseStep 45454607 = 68181911) B68181911
theorem B2659679 : Blo 1772087 2659679 := bstep (se 1 (by rfl) ⟨1994759, by rfl⟩ : syracuseStep 2659679 = 3989519) B3989519
theorem B2659691 : Blo 1772087 2659691 := bstep (se 1 (by rfl) ⟨1994768, by rfl⟩ : syracuseStep 2659691 = 3989537) B3989537
theorem B4486529 : Blo 1772087 4486529 := bstep (se 2 (by rfl) ⟨1682448, by rfl⟩ : syracuseStep 4486529 = 3364897) B3364897
theorem B5985737 : Blo 1772087 5985737 := bstep (se 2 (by rfl) ⟨2244651, by rfl⟩ : syracuseStep 5985737 = 4489303) B4489303
theorem B34100797 : Blo 1772087 34100797 := bstep (se 3 (by rfl) ⟨6393899, by rfl⟩ : syracuseStep 34100797 = 12787799) B12787799
theorem B2659919 : Blo 1772087 2659919 := bstep (se 1 (by rfl) ⟨1994939, by rfl⟩ : syracuseStep 2659919 = 3989879) B3989879
theorem B2660039 : Blo 1772087 2660039 := bstep (se 1 (by rfl) ⟨1995029, by rfl⟩ : syracuseStep 2660039 = 3990059) B3990059
theorem B5986007 : Blo 1772087 5986007 := bstep (se 1 (by rfl) ⟨4489505, by rfl⟩ : syracuseStep 5986007 = 8979011) B8979011
theorem B4486985 : Blo 1772087 4486985 := bstep (se 2 (by rfl) ⟨1682619, by rfl⟩ : syracuseStep 4486985 = 3365239) B3365239
theorem B2660201 : Blo 1772087 2660201 := bstep (se 2 (by rfl) ⟨997575, by rfl⟩ : syracuseStep 2660201 = 1995151) B1995151
theorem B3364715 : Blo 1772087 3364715 := bstep (se 1 (by rfl) ⟨2523536, by rfl⟩ : syracuseStep 3364715 = 5047073) B5047073
theorem B5986223 : Blo 1772087 5986223 := bstep (se 1 (by rfl) ⟨4489667, by rfl⟩ : syracuseStep 5986223 = 8979335) B8979335
theorem B25556917 : Blo 1772087 25556917 := bstep (se 5 (by rfl) ⟨1197980, by rfl⟩ : syracuseStep 25556917 = 2395961) B2395961
theorem B2660279 : Blo 1772087 2660279 := bstep (se 1 (by rfl) ⟨1995209, by rfl⟩ : syracuseStep 2660279 = 3990419) B3990419
theorem B13457339 : Blo 1772087 13457339 := bstep (se 1 (by rfl) ⟨10093004, by rfl⟩ : syracuseStep 13457339 = 20186009) B20186009
theorem B6731707 : Blo 1772087 6731707 := bstep (se 1 (by rfl) ⟨5048780, by rfl⟩ : syracuseStep 6731707 = 10097561) B10097561
theorem B2660315 : Blo 1772087 2660315 := bstep (se 1 (by rfl) ⟨1995236, by rfl⟩ : syracuseStep 2660315 = 3990473) B3990473
theorem B4487339 : Blo 1772087 4487339 := bstep (se 1 (by rfl) ⟨3365504, by rfl⟩ : syracuseStep 4487339 = 6731009) B6731009
theorem B15145217 : Blo 1772087 15145217 := bstep (se 2 (by rfl) ⟨5679456, by rfl⟩ : syracuseStep 15145217 = 11358913) B11358913
theorem B14383421 : Blo 1772087 14383421 := bstep (se 3 (by rfl) ⟨2696891, by rfl⟩ : syracuseStep 14383421 = 5393783) B5393783
theorem B12777857 : Blo 1772087 12777857 := bstep (se 2 (by rfl) ⟨4791696, by rfl⟩ : syracuseStep 12777857 = 9583393) B9583393
theorem B14383489 : Blo 1772087 14383489 := bstep (se 2 (by rfl) ⟨5393808, by rfl⟩ : syracuseStep 14383489 = 10787617) B10787617
theorem B2242991 : Blo 1772087 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B2660783 : Blo 1772087 2660783 := bstep (se 1 (by rfl) ⟨1995587, by rfl⟩ : syracuseStep 2660783 = 3991175) B3991175
theorem B3365383 : Blo 1772087 3365383 := bstep (se 1 (by rfl) ⟨2524037, by rfl⟩ : syracuseStep 3365383 = 5048075) B5048075
theorem B8976905 : Blo 1772087 8976905 := bstep (se 2 (by rfl) ⟨3366339, by rfl⟩ : syracuseStep 8976905 = 6732679) B6732679
theorem B2660873 : Blo 1772087 2660873 := bstep (se 2 (by rfl) ⟨997827, by rfl⟩ : syracuseStep 2660873 = 1995655) B1995655
theorem B3988007 : Blo 1772087 3988007 := bstep (se 1 (by rfl) ⟨2991005, by rfl⟩ : syracuseStep 3988007 = 5982011) B5982011
theorem B2660903 : Blo 1772087 2660903 := bstep (se 1 (by rfl) ⟨1995677, by rfl⟩ : syracuseStep 2660903 = 3991355) B3991355
theorem B2660987 : Blo 1772087 2660987 := bstep (se 1 (by rfl) ⟨1995740, by rfl⟩ : syracuseStep 2660987 = 3991481) B3991481
theorem B7191179 : Blo 1772087 7191179 := bstep (se 1 (by rfl) ⟨5393384, by rfl⟩ : syracuseStep 7191179 = 10786769) B10786769
theorem B14383817 : Blo 1772087 14383817 := bstep (se 2 (by rfl) ⟨5393931, by rfl⟩ : syracuseStep 14383817 = 10787863) B10787863
theorem B6732497 : Blo 1772087 6732497 := bstep (se 2 (by rfl) ⟨2524686, by rfl⟩ : syracuseStep 6732497 = 5049373) B5049373
theorem B2661113 : Blo 1772087 2661113 := bstep (se 2 (by rfl) ⟨997917, by rfl⟩ : syracuseStep 2661113 = 1995835) B1995835
theorem B4315999 : Blo 1772087 4315999 := bstep (se 1 (by rfl) ⟨3236999, by rfl⟩ : syracuseStep 4315999 = 6473999) B6473999
theorem B3988331 : Blo 1772087 3988331 := bstep (se 1 (by rfl) ⟨2991248, by rfl⟩ : syracuseStep 3988331 = 5982497) B5982497
theorem B3988385 : Blo 1772087 3988385 := bstep (se 2 (by rfl) ⟨1495644, by rfl⟩ : syracuseStep 3988385 = 2991289) B2991289
theorem B4488119 : Blo 1772087 4488119 := bstep (se 1 (by rfl) ⟨3366089, by rfl⟩ : syracuseStep 4488119 = 6732179) B6732179
theorem B3365945 : Blo 1772087 3365945 := bstep (se 2 (by rfl) ⟨1262229, by rfl⟩ : syracuseStep 3365945 = 2524459) B2524459
theorem B6732953 : Blo 1772087 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B3988727 : Blo 1772087 3988727 := bstep (se 1 (by rfl) ⟨2991545, by rfl⟩ : syracuseStep 3988727 = 5983091) B5983091
theorem B11517221 : Blo 1772087 11517221 := bstep (se 4 (by rfl) ⟨1079739, by rfl⟩ : syracuseStep 11517221 = 2159479) B2159479
theorem B14572889 : Blo 1772087 14572889 := bstep (se 2 (by rfl) ⟨5464833, by rfl⟩ : syracuseStep 14572889 = 10929667) B10929667
theorem B12959065 : Blo 1772087 12959065 := bstep (se 2 (by rfl) ⟨4859649, by rfl⟩ : syracuseStep 12959065 = 9719299) B9719299
theorem B6389117 : Blo 1772087 6389117 := bstep (se 3 (by rfl) ⟨1197959, by rfl⟩ : syracuseStep 6389117 = 2395919) B2395919
theorem B12787109 : Blo 1772087 12787109 := bstep (se 4 (by rfl) ⟨1198791, by rfl⟩ : syracuseStep 12787109 = 2397583) B2397583
theorem B8519357 : Blo 1772087 8519357 := bstep (se 3 (by rfl) ⟨1597379, by rfl⟩ : syracuseStep 8519357 = 3194759) B3194759
theorem B3989321 : Blo 1772087 3989321 := bstep (se 2 (by rfl) ⟨1495995, by rfl⟩ : syracuseStep 3989321 = 2991991) B2991991
theorem B3194731 : Blo 1772087 3194731 := bstep (se 1 (by rfl) ⟨2396048, by rfl⟩ : syracuseStep 3194731 = 4792097) B4792097
theorem B4489121 : Blo 1772087 4489121 := bstep (se 2 (by rfl) ⟨1683420, by rfl⟩ : syracuseStep 4489121 = 3366841) B3366841
theorem B8978363 : Blo 1772087 8978363 := bstep (se 1 (by rfl) ⟨6733772, by rfl⟩ : syracuseStep 8978363 = 13467545) B13467545
theorem B12132289 : Blo 1772087 12132289 := bstep (se 2 (by rfl) ⟨4549608, by rfl⟩ : syracuseStep 12132289 = 9099217) B9099217
theorem B3989609 : Blo 1772087 3989609 := bstep (se 2 (by rfl) ⟨1496103, by rfl⟩ : syracuseStep 3989609 = 2992207) B2992207
theorem B30294323 : Blo 1772087 30294323 := bstep (se 1 (by rfl) ⟨22720742, by rfl⟩ : syracuseStep 30294323 = 45441485) B45441485
theorem B3785143 : Blo 1772087 3785143 := bstep (se 1 (by rfl) ⟨2838857, by rfl⟩ : syracuseStep 3785143 = 5677715) B5677715
theorem B2990587 : Blo 1772087 2990587 := bstep (se 1 (by rfl) ⟨2242940, by rfl⟩ : syracuseStep 2990587 = 4485881) B4485881
theorem B19177985 : Blo 1772087 19177985 := bstep (se 2 (by rfl) ⟨7191744, by rfl⟩ : syracuseStep 19177985 = 14383489) B14383489
theorem B3367487 : Blo 1772087 3367487 := bstep (se 1 (by rfl) ⟨2525615, by rfl⟩ : syracuseStep 3367487 = 5051231) B5051231
theorem B3785287 : Blo 1772087 3785287 := bstep (se 1 (by rfl) ⟨2838965, by rfl⟩ : syracuseStep 3785287 = 5677931) B5677931
theorem B3990095 : Blo 1772087 3990095 := bstep (se 1 (by rfl) ⟨2992571, by rfl⟩ : syracuseStep 3990095 = 5985143) B5985143
theorem B3990239 : Blo 1772087 3990239 := bstep (se 1 (by rfl) ⟨2992679, by rfl⟩ : syracuseStep 3990239 = 5985359) B5985359
theorem B4489951 : Blo 1772087 4489951 := bstep (se 1 (by rfl) ⟨3367463, by rfl⟩ : syracuseStep 4489951 = 6734927) B6734927
theorem B2130743 : Blo 1772087 2130743 := bstep (se 1 (by rfl) ⟨1598057, by rfl⟩ : syracuseStep 2130743 = 3196115) B3196115
theorem B4490063 : Blo 1772087 4490063 := bstep (se 1 (by rfl) ⟨3367547, by rfl⟩ : syracuseStep 4490063 = 6735095) B6735095
theorem B30303071 : Blo 1772087 30303071 := bstep (se 1 (by rfl) ⟨22727303, by rfl⟩ : syracuseStep 30303071 = 45454607) B45454607
theorem B11355041 : Blo 1772087 11355041 := bstep (se 2 (by rfl) ⟨4258140, by rfl⟩ : syracuseStep 11355041 = 8516281) B8516281
theorem B2991019 : Blo 1772087 2991019 := bstep (se 1 (by rfl) ⟨2243264, by rfl⟩ : syracuseStep 2991019 = 4486529) B4486529
theorem B5981147 : Blo 1772087 5981147 := bstep (se 1 (by rfl) ⟨4485860, by rfl⟩ : syracuseStep 5981147 = 8971721) B8971721
theorem B3990491 : Blo 1772087 3990491 := bstep (se 1 (by rfl) ⟨2992868, by rfl⟩ : syracuseStep 3990491 = 5985737) B5985737
theorem B5981309 : Blo 1772087 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B3990671 : Blo 1772087 3990671 := bstep (se 1 (by rfl) ⟨2993003, by rfl⟩ : syracuseStep 3990671 = 5986007) B5986007
theorem B2991323 : Blo 1772087 2991323 := bstep (se 1 (by rfl) ⟨2243492, by rfl⟩ : syracuseStep 2991323 = 4486985) B4486985
theorem B5981417 : Blo 1772087 5981417 := bstep (se 2 (by rfl) ⟨2243031, by rfl⟩ : syracuseStep 5981417 = 4486063) B4486063
theorem B3990761 : Blo 1772087 3990761 := bstep (se 2 (by rfl) ⟨1496535, by rfl⟩ : syracuseStep 3990761 = 2993071) B2993071
theorem B3990815 : Blo 1772087 3990815 := bstep (se 1 (by rfl) ⟨2993111, by rfl⟩ : syracuseStep 3990815 = 5986223) B5986223
theorem B8971559 : Blo 1772087 8971559 := bstep (se 1 (by rfl) ⟨6728669, by rfl⟩ : syracuseStep 8971559 = 13457339) B13457339
theorem B8979821 : Blo 1772087 8979821 := bstep (se 3 (by rfl) ⟨1683716, by rfl⟩ : syracuseStep 8979821 = 3367433) B3367433
theorem B3786107 : Blo 1772087 3786107 := bstep (se 1 (by rfl) ⟨2839580, by rfl⟩ : syracuseStep 3786107 = 5679161) B5679161
theorem B5981579 : Blo 1772087 5981579 := bstep (se 1 (by rfl) ⟨4486184, by rfl⟩ : syracuseStep 5981579 = 8972369) B8972369
theorem B2991559 : Blo 1772087 2991559 := bstep (se 1 (by rfl) ⟨2243669, by rfl⟩ : syracuseStep 2991559 = 4487339) B4487339
theorem B68142545 : Blo 1772087 68142545 := bstep (se 2 (by rfl) ⟨25553454, by rfl⟩ : syracuseStep 68142545 = 51106909) B51106909
theorem B4548257 : Blo 1772087 4548257 := bstep (se 2 (by rfl) ⟨1705596, by rfl⟩ : syracuseStep 4548257 = 3411193) B3411193
theorem B3196577 : Blo 1772087 3196577 := bstep (se 2 (by rfl) ⟨1198716, by rfl⟩ : syracuseStep 3196577 = 2397433) B2397433
theorem B4794119 : Blo 1772087 4794119 := bstep (se 1 (by rfl) ⟨3595589, by rfl⟩ : syracuseStep 4794119 = 7191179) B7191179
theorem B17278753 : Blo 1772087 17278753 := bstep (se 2 (by rfl) ⟨6479532, by rfl⟩ : syracuseStep 17278753 = 12959065) B12959065
theorem B3991337 : Blo 1772087 3991337 := bstep (se 2 (by rfl) ⟨1496751, by rfl⟩ : syracuseStep 3991337 = 2993503) B2993503
theorem B2557903 : Blo 1772087 2557903 := bstep (se 1 (by rfl) ⟨1918427, by rfl⟩ : syracuseStep 2557903 = 3836855) B3836855
theorem B2992079 : Blo 1772087 2992079 := bstep (se 1 (by rfl) ⟨2244059, by rfl⟩ : syracuseStep 2992079 = 4488119) B4488119
theorem B45467729 : Blo 1772087 45467729 := bstep (se 2 (by rfl) ⟨17050398, by rfl⟩ : syracuseStep 45467729 = 34100797) B34100797
theorem B7678147 : Blo 1772087 7678147 := bstep (se 1 (by rfl) ⟨5758610, by rfl⟩ : syracuseStep 7678147 = 11517221) B11517221
theorem B746768645 : Blo 1772087 746768645 := bstep (se 4 (by rfl) ⟨70009560, by rfl⟩ : syracuseStep 746768645 = 140019121) B140019121
theorem B5679571 : Blo 1772087 5679571 := bstep (se 1 (by rfl) ⟨4259678, by rfl⟩ : syracuseStep 5679571 = 8519357) B8519357
theorem B8522279 : Blo 1772087 8522279 := bstep (se 1 (by rfl) ⟨6391709, by rfl⟩ : syracuseStep 8522279 = 12783419) B12783419
theorem B1772095 : Blo 1772087 1772095 := bstep (se 1 (by rfl) ⟨1329071, by rfl⟩ : syracuseStep 1772095 = 2658143) B2658143
theorem B1772103 : Blo 1772087 1772103 := bstep (se 1 (by rfl) ⟨1329077, by rfl⟩ : syracuseStep 1772103 = 2658155) B2658155
theorem B2992747 : Blo 1772087 2992747 := bstep (se 1 (by rfl) ⟨2244560, by rfl⟩ : syracuseStep 2992747 = 4489121) B4489121
theorem B36383411 : Blo 1772087 36383411 := bstep (se 1 (by rfl) ⟨27287558, by rfl⟩ : syracuseStep 36383411 = 54575117) B54575117
theorem B24259283 : Blo 1772087 24259283 := bstep (se 1 (by rfl) ⟨18194462, by rfl⟩ : syracuseStep 24259283 = 36388925) B36388925
theorem B1772255 : Blo 1772087 1772255 := bstep (se 1 (by rfl) ⟨1329191, by rfl⟩ : syracuseStep 1772255 = 2658383) B2658383
theorem B28756727 : Blo 1772087 28756727 := bstep (se 1 (by rfl) ⟨21567545, by rfl⟩ : syracuseStep 28756727 = 43135091) B43135091
theorem B10103575 : Blo 1772087 10103575 := bstep (se 1 (by rfl) ⟨7577681, by rfl⟩ : syracuseStep 10103575 = 15155363) B15155363
theorem B1772335 : Blo 1772087 1772335 := bstep (se 1 (by rfl) ⟨1329251, by rfl⟩ : syracuseStep 1772335 = 2658503) B2658503
theorem B218409797 : Blo 1772087 218409797 := bstep (se 4 (by rfl) ⟨20475918, by rfl⟩ : syracuseStep 218409797 = 40951837) B40951837
theorem B1772443 : Blo 1772087 1772443 := bstep (se 1 (by rfl) ⟨1329332, by rfl⟩ : syracuseStep 1772443 = 2658665) B2658665
theorem B2993051 : Blo 1772087 2993051 := bstep (se 1 (by rfl) ⟨2244788, by rfl⟩ : syracuseStep 2993051 = 4489577) B4489577
theorem B1772495 : Blo 1772087 1772495 := bstep (se 1 (by rfl) ⟨1329371, by rfl⟩ : syracuseStep 1772495 = 2658743) B2658743
theorem B18205661 : Blo 1772087 18205661 := bstep (se 3 (by rfl) ⟨3413561, by rfl⟩ : syracuseStep 18205661 = 6827123) B6827123
theorem B1772519 : Blo 1772087 1772519 := bstep (se 1 (by rfl) ⟨1329389, by rfl⟩ : syracuseStep 1772519 = 2658779) B2658779
theorem B5393395 : Blo 1772087 5393395 := bstep (se 1 (by rfl) ⟨4045046, by rfl⟩ : syracuseStep 5393395 = 8090093) B8090093
theorem B5049533 : Blo 1772087 5049533 := bstep (se 3 (by rfl) ⟨946787, by rfl⟩ : syracuseStep 5049533 = 1893575) B1893575
theorem B1772831 : Blo 1772087 1772831 := bstep (se 1 (by rfl) ⟨1329623, by rfl⟩ : syracuseStep 1772831 = 2659247) B2659247
theorem B7572797 : Blo 1772087 7572797 := bstep (se 3 (by rfl) ⟨1419899, by rfl⟩ : syracuseStep 7572797 = 2839799) B2839799
theorem B1772891 : Blo 1772087 1772891 := bstep (se 1 (by rfl) ⟨1329668, by rfl⟩ : syracuseStep 1772891 = 2659337) B2659337
theorem B15142241 : Blo 1772087 15142241 := bstep (se 2 (by rfl) ⟨5678340, by rfl⟩ : syracuseStep 15142241 = 11356681) B11356681
theorem B8973665 : Blo 1772087 8973665 := bstep (se 2 (by rfl) ⟨3365124, by rfl⟩ : syracuseStep 8973665 = 6730249) B6730249
theorem B8088929 : Blo 1772087 8088929 := bstep (se 2 (by rfl) ⟨3033348, by rfl⟩ : syracuseStep 8088929 = 6066697) B6066697
theorem B1772911 : Blo 1772087 1772911 := bstep (se 1 (by rfl) ⟨1329683, by rfl⟩ : syracuseStep 1772911 = 2659367) B2659367
theorem B1994107 : Blo 1772087 1994107 := bstep (se 1 (by rfl) ⟨1495580, by rfl⟩ : syracuseStep 1994107 = 2991161) B2991161
theorem B1772967 : Blo 1772087 1772967 := bstep (se 1 (by rfl) ⟨1329725, by rfl⟩ : syracuseStep 1772967 = 2659451) B2659451
theorem B1773051 : Blo 1772087 1773051 := bstep (se 1 (by rfl) ⟨1329788, by rfl⟩ : syracuseStep 1773051 = 2659577) B2659577
theorem B1773119 : Blo 1772087 1773119 := bstep (se 1 (by rfl) ⟨1329839, by rfl⟩ : syracuseStep 1773119 = 2659679) B2659679
theorem B1773127 : Blo 1772087 1773127 := bstep (se 1 (by rfl) ⟨1329845, by rfl⟩ : syracuseStep 1773127 = 2659691) B2659691
theorem B5680801 : Blo 1772087 5680801 := bstep (se 2 (by rfl) ⟨2130300, by rfl⟩ : syracuseStep 5680801 = 4260601) B4260601
theorem B1773279 : Blo 1772087 1773279 := bstep (se 1 (by rfl) ⟨1329959, by rfl⟩ : syracuseStep 1773279 = 2659919) B2659919
theorem B5754665 : Blo 1772087 5754665 := bstep (se 2 (by rfl) ⟨2157999, by rfl⟩ : syracuseStep 5754665 = 4315999) B4315999
theorem B1773359 : Blo 1772087 1773359 := bstep (se 1 (by rfl) ⟨1330019, by rfl⟩ : syracuseStep 1773359 = 2660039) B2660039
theorem B1994575 : Blo 1772087 1994575 := bstep (se 1 (by rfl) ⟨1495931, by rfl⟩ : syracuseStep 1994575 = 2991863) B2991863
theorem B1773467 : Blo 1772087 1773467 := bstep (se 1 (by rfl) ⟨1330100, by rfl⟩ : syracuseStep 1773467 = 2660201) B2660201
theorem B4042703 : Blo 1772087 4042703 := bstep (se 1 (by rfl) ⟨3032027, by rfl⟩ : syracuseStep 4042703 = 6064055) B6064055
theorem B1773519 : Blo 1772087 1773519 := bstep (se 1 (by rfl) ⟨1330139, by rfl⟩ : syracuseStep 1773519 = 2660279) B2660279
theorem B1773543 : Blo 1772087 1773543 := bstep (se 1 (by rfl) ⟨1330157, by rfl⟩ : syracuseStep 1773543 = 2660315) B2660315
theorem B7573513 : Blo 1772087 7573513 := bstep (se 2 (by rfl) ⟨2840067, by rfl⟩ : syracuseStep 7573513 = 5680135) B5680135
theorem B13463657 : Blo 1772087 13463657 := bstep (se 2 (by rfl) ⟨5048871, by rfl⟩ : syracuseStep 13463657 = 10097743) B10097743
theorem B10096811 : Blo 1772087 10096811 := bstep (se 1 (by rfl) ⟨7572608, by rfl⟩ : syracuseStep 10096811 = 15145217) B15145217
theorem B9588947 : Blo 1772087 9588947 := bstep (se 1 (by rfl) ⟨7191710, by rfl⟩ : syracuseStep 9588947 = 14383421) B14383421
theorem B1994971 : Blo 1772087 1994971 := bstep (se 1 (by rfl) ⟨1496228, by rfl⟩ : syracuseStep 1994971 = 2992457) B2992457
theorem B1945819 : Blo 1772087 1945819 := bstep (se 1 (by rfl) ⟨1459364, by rfl⟩ : syracuseStep 1945819 = 2918729) B2918729
theorem B2658569 : Blo 1772087 2658569 := bstep (se 2 (by rfl) ⟨996963, by rfl⟩ : syracuseStep 2658569 = 1993927) B1993927
theorem B1773855 : Blo 1772087 1773855 := bstep (se 1 (by rfl) ⟨1330391, by rfl⟩ : syracuseStep 1773855 = 2660783) B2660783
theorem B11366729 : Blo 1772087 11366729 := bstep (se 2 (by rfl) ⟨4262523, by rfl⟩ : syracuseStep 11366729 = 8525047) B8525047
theorem B5984603 : Blo 1772087 5984603 := bstep (se 1 (by rfl) ⟨4488452, by rfl⟩ : syracuseStep 5984603 = 8976905) B8976905
theorem B1773915 : Blo 1772087 1773915 := bstep (se 1 (by rfl) ⟨1330436, by rfl⟩ : syracuseStep 1773915 = 2660873) B2660873
theorem B2658671 : Blo 1772087 2658671 := bstep (se 1 (by rfl) ⟨1994003, by rfl⟩ : syracuseStep 2658671 = 3988007) B3988007
theorem B1773935 : Blo 1772087 1773935 := bstep (se 1 (by rfl) ⟨1330451, by rfl⟩ : syracuseStep 1773935 = 2660903) B2660903
theorem B1773991 : Blo 1772087 1773991 := bstep (se 1 (by rfl) ⟨1330493, by rfl⟩ : syracuseStep 1773991 = 2660987) B2660987
theorem B11366831 : Blo 1772087 11366831 := bstep (se 1 (by rfl) ⟨8525123, by rfl⟩ : syracuseStep 11366831 = 17050247) B17050247
theorem B9589211 : Blo 1772087 9589211 := bstep (se 1 (by rfl) ⟨7191908, by rfl⟩ : syracuseStep 9589211 = 14383817) B14383817
theorem B1995259 : Blo 1772087 1995259 := bstep (se 1 (by rfl) ⟨1496444, by rfl⟩ : syracuseStep 1995259 = 2992889) B2992889
theorem B1774075 : Blo 1772087 1774075 := bstep (se 1 (by rfl) ⟨1330556, by rfl⟩ : syracuseStep 1774075 = 2661113) B2661113
theorem B2658887 : Blo 1772087 2658887 := bstep (se 1 (by rfl) ⟨1994165, by rfl⟩ : syracuseStep 2658887 = 3988331) B3988331
theorem B4485739 : Blo 1772087 4485739 := bstep (se 1 (by rfl) ⟨3364304, by rfl⟩ : syracuseStep 4485739 = 6728609) B6728609
theorem B2658923 : Blo 1772087 2658923 := bstep (se 1 (by rfl) ⟨1994192, by rfl⟩ : syracuseStep 2658923 = 3988385) B3988385
theorem B1995439 : Blo 1772087 1995439 := bstep (se 1 (by rfl) ⟨1496579, by rfl⟩ : syracuseStep 1995439 = 2993159) B2993159
theorem B2659151 : Blo 1772087 2659151 := bstep (se 1 (by rfl) ⟨1994363, by rfl⟩ : syracuseStep 2659151 = 3988727) B3988727
theorem B4486043 : Blo 1772087 4486043 := bstep (se 1 (by rfl) ⟨3364532, by rfl⟩ : syracuseStep 4486043 = 6729065) B6729065
theorem B8524739 : Blo 1772087 8524739 := bstep (se 1 (by rfl) ⟨6393554, by rfl⟩ : syracuseStep 8524739 = 12787109) B12787109
theorem B15143881 : Blo 1772087 15143881 := bstep (se 2 (by rfl) ⟨5678955, by rfl⟩ : syracuseStep 15143881 = 11357911) B11357911
theorem B1995727 : Blo 1772087 1995727 := bstep (se 1 (by rfl) ⟨1496795, by rfl⟩ : syracuseStep 1995727 = 2993591) B2993591
theorem B2659547 : Blo 1772087 2659547 := bstep (se 1 (by rfl) ⟨1994660, by rfl⟩ : syracuseStep 2659547 = 3989321) B3989321
theorem B34075889 : Blo 1772087 34075889 := bstep (se 2 (by rfl) ⟨12778458, by rfl⟩ : syracuseStep 34075889 = 25556917) B25556917
theorem B4486387 : Blo 1772087 4486387 := bstep (se 1 (by rfl) ⟨3364790, by rfl⟩ : syracuseStep 4486387 = 6729581) B6729581
theorem B8975609 : Blo 1772087 8975609 := bstep (se 2 (by rfl) ⟨3365853, by rfl⟩ : syracuseStep 8975609 = 6731707) B6731707
theorem B16176385 : Blo 1772087 16176385 := bstep (se 2 (by rfl) ⟨6066144, by rfl⟩ : syracuseStep 16176385 = 12132289) B12132289
theorem B5985575 : Blo 1772087 5985575 := bstep (se 1 (by rfl) ⟨4489181, by rfl⟩ : syracuseStep 5985575 = 8978363) B8978363
theorem B35018077 : Blo 1772087 35018077 := bstep (se 3 (by rfl) ⟨6565889, by rfl⟩ : syracuseStep 35018077 = 13131779) B13131779
theorem B17036639 : Blo 1772087 17036639 := bstep (se 1 (by rfl) ⟨12777479, by rfl⟩ : syracuseStep 17036639 = 25554959) B25554959
theorem B2659721 : Blo 1772087 2659721 := bstep (se 2 (by rfl) ⟨997395, by rfl⟩ : syracuseStep 2659721 = 1994791) B1994791
theorem B6387083 : Blo 1772087 6387083 := bstep (se 1 (by rfl) ⟨4790312, by rfl⟩ : syracuseStep 6387083 = 9580625) B9580625
theorem B16176647 : Blo 1772087 16176647 := bstep (se 1 (by rfl) ⟨12132485, by rfl⟩ : syracuseStep 16176647 = 24264971) B24264971
theorem B2660075 : Blo 1772087 2660075 := bstep (se 1 (by rfl) ⟨1995056, by rfl⟩ : syracuseStep 2660075 = 3990113) B3990113
theorem B3987305 : Blo 1772087 3987305 := bstep (se 2 (by rfl) ⟨1495239, by rfl⟩ : syracuseStep 3987305 = 2990479) B2990479
theorem B17037175 : Blo 1772087 17037175 := bstep (se 1 (by rfl) ⟨12777881, by rfl⟩ : syracuseStep 17037175 = 25555763) B25555763
theorem B2660303 : Blo 1772087 2660303 := bstep (se 1 (by rfl) ⟨1995227, by rfl⟩ : syracuseStep 2660303 = 3990455) B3990455
theorem B4487177 : Blo 1772087 4487177 := bstep (se 2 (by rfl) ⟨1682691, by rfl⟩ : syracuseStep 4487177 = 3365383) B3365383
theorem B28760093 : Blo 1772087 28760093 := bstep (se 3 (by rfl) ⟨5392517, by rfl⟩ : syracuseStep 28760093 = 10785035) B10785035
theorem B5986439 : Blo 1772087 5986439 := bstep (se 1 (by rfl) ⟨4489829, by rfl⟩ : syracuseStep 5986439 = 8979659) B8979659
theorem B2660699 : Blo 1772087 2660699 := bstep (se 1 (by rfl) ⟨1995524, by rfl⟩ : syracuseStep 2660699 = 3991049) B3991049
theorem B9099631 : Blo 1772087 9099631 := bstep (se 1 (by rfl) ⟨6824723, by rfl⟩ : syracuseStep 9099631 = 13649447) B13649447
theorem B2660927 : Blo 1772087 2660927 := bstep (se 1 (by rfl) ⟨1995695, by rfl⟩ : syracuseStep 2660927 = 3991391) B3991391
theorem B2243143 : Blo 1772087 2243143 := bstep (se 1 (by rfl) ⟨1682357, by rfl⟩ : syracuseStep 2243143 = 3364715) B3364715
theorem B4790863 : Blo 1772087 4790863 := bstep (se 1 (by rfl) ⟨3593147, by rfl⟩ : syracuseStep 4790863 = 7186295) B7186295
theorem B3988151 : Blo 1772087 3988151 := bstep (se 1 (by rfl) ⟨2991113, by rfl⟩ : syracuseStep 3988151 = 5982227) B5982227
theorem B2661047 : Blo 1772087 2661047 := bstep (se 1 (by rfl) ⟨1995785, by rfl⟩ : syracuseStep 2661047 = 3991571) B3991571
theorem B10099475 : Blo 1772087 10099475 := bstep (se 1 (by rfl) ⟨7574606, by rfl⟩ : syracuseStep 10099475 = 15149213) B15149213
theorem B3988367 : Blo 1772087 3988367 := bstep (se 1 (by rfl) ⟨2991275, by rfl⟩ : syracuseStep 3988367 = 5982551) B5982551
theorem B5462939 : Blo 1772087 5462939 := bstep (se 1 (by rfl) ⟨4097204, by rfl⟩ : syracuseStep 5462939 = 8194409) B8194409
theorem B8518571 : Blo 1772087 8518571 := bstep (se 1 (by rfl) ⟨6388928, by rfl⟩ : syracuseStep 8518571 = 12777857) B12777857
theorem B17046557 : Blo 1772087 17046557 := bstep (se 3 (by rfl) ⟨3196229, by rfl⟩ : syracuseStep 17046557 = 6392459) B6392459
theorem B4488331 : Blo 1772087 4488331 := bstep (se 1 (by rfl) ⟨3366248, by rfl⟩ : syracuseStep 4488331 = 6732497) B6732497
theorem B2243963 : Blo 1772087 2243963 := bstep (se 1 (by rfl) ⟨1682972, by rfl⟩ : syracuseStep 2243963 = 3365945) B3365945
theorem B2022779 : Blo 1772087 2022779 := bstep (se 1 (by rfl) ⟨1517084, by rfl⟩ : syracuseStep 2022779 = 3034169) B3034169
theorem B4488635 : Blo 1772087 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B9715259 : Blo 1772087 9715259 := bstep (se 1 (by rfl) ⟨7286444, by rfl⟩ : syracuseStep 9715259 = 14572889) B14572889
theorem B4259411 : Blo 1772087 4259411 := bstep (se 1 (by rfl) ⟨3194558, by rfl⟩ : syracuseStep 4259411 = 6389117) B6389117
theorem B7577171 : Blo 1772087 7577171 := bstep (se 1 (by rfl) ⟨5682878, by rfl⟩ : syracuseStep 7577171 = 11365757) B11365757
theorem B3989087 : Blo 1772087 3989087 := bstep (se 1 (by rfl) ⟨2991815, by rfl⟩ : syracuseStep 3989087 = 5983631) B5983631
theorem B4791965 : Blo 1772087 4791965 := bstep (se 3 (by rfl) ⟨898493, by rfl⟩ : syracuseStep 4791965 = 1796987) B1796987
theorem B3366697 : Blo 1772087 3366697 := bstep (se 2 (by rfl) ⟨1262511, by rfl⟩ : syracuseStep 3366697 = 2525023) B2525023
theorem B3989303 : Blo 1772087 3989303 := bstep (se 1 (by rfl) ⟨2991977, by rfl⟩ : syracuseStep 3989303 = 5983955) B5983955
theorem B4259641 : Blo 1772087 4259641 := bstep (se 2 (by rfl) ⟨1597365, by rfl⟩ : syracuseStep 4259641 = 3194731) B3194731
theorem B12787631 : Blo 1772087 12787631 := bstep (se 1 (by rfl) ⟨9590723, by rfl⟩ : syracuseStep 12787631 = 19181447) B19181447
theorem B7577819 : Blo 1772087 7577819 := bstep (se 1 (by rfl) ⟨5683364, by rfl⟩ : syracuseStep 7577819 = 11366729) B11366729
theorem B3989735 : Blo 1772087 3989735 := bstep (se 1 (by rfl) ⟨2992301, by rfl⟩ : syracuseStep 3989735 = 5984603) B5984603
theorem B7577887 : Blo 1772087 7577887 := bstep (se 1 (by rfl) ⟨5683415, by rfl⟩ : syracuseStep 7577887 = 11366831) B11366831
theorem B2244991 : Blo 1772087 2244991 := bstep (se 1 (by rfl) ⟨1683743, by rfl⟩ : syracuseStep 2244991 = 3367487) B3367487
theorem B12132841 : Blo 1772087 12132841 := bstep (se 2 (by rfl) ⟨4549815, by rfl⟩ : syracuseStep 12132841 = 9099631) B9099631
theorem B20202047 : Blo 1772087 20202047 := bstep (se 1 (by rfl) ⟨15151535, by rfl⟩ : syracuseStep 20202047 = 30303071) B30303071
theorem B5046857 : Blo 1772087 5046857 := bstep (se 2 (by rfl) ⟨1892571, by rfl⟩ : syracuseStep 5046857 = 3785143) B3785143
theorem B2990695 : Blo 1772087 2990695 := bstep (se 1 (by rfl) ⟨2243021, by rfl⟩ : syracuseStep 2990695 = 4486043) B4486043
theorem B7570027 : Blo 1772087 7570027 := bstep (se 1 (by rfl) ⟨5677520, by rfl⟩ : syracuseStep 7570027 = 11355041) B11355041
theorem B5047049 : Blo 1772087 5047049 := bstep (se 2 (by rfl) ⟨1892643, by rfl⟩ : syracuseStep 5047049 = 3785287) B3785287
theorem B2990857 : Blo 1772087 2990857 := bstep (se 2 (by rfl) ⟨1121571, by rfl⟩ : syracuseStep 2990857 = 2243143) B2243143
theorem B5980985 : Blo 1772087 5980985 := bstep (se 2 (by rfl) ⟨2242869, by rfl⟩ : syracuseStep 5980985 = 4485739) B4485739
theorem B3990329 : Blo 1772087 3990329 := bstep (se 2 (by rfl) ⟨1496373, by rfl⟩ : syracuseStep 3990329 = 2992747) B2992747
theorem B22717259 : Blo 1772087 22717259 := bstep (se 1 (by rfl) ⟨17037944, by rfl⟩ : syracuseStep 22717259 = 34075889) B34075889
theorem B5981039 : Blo 1772087 5981039 := bstep (se 1 (by rfl) ⟨4485779, by rfl⟩ : syracuseStep 5981039 = 8971559) B8971559
theorem B3990383 : Blo 1772087 3990383 := bstep (se 1 (by rfl) ⟨2992787, by rfl⟩ : syracuseStep 3990383 = 5985575) B5985575
theorem B3032171 : Blo 1772087 3032171 := bstep (se 1 (by rfl) ⟨2274128, by rfl⟩ : syracuseStep 3032171 = 4548257) B4548257
theorem B2131051 : Blo 1772087 2131051 := bstep (se 1 (by rfl) ⟨1598288, by rfl⟩ : syracuseStep 2131051 = 3196577) B3196577
theorem B3196079 : Blo 1772087 3196079 := bstep (se 1 (by rfl) ⟨2397059, by rfl⟩ : syracuseStep 3196079 = 4794119) B4794119
theorem B2991451 : Blo 1772087 2991451 := bstep (se 1 (by rfl) ⟨2243588, by rfl⟩ : syracuseStep 2991451 = 4487177) B4487177
theorem B30311819 : Blo 1772087 30311819 := bstep (se 1 (by rfl) ⟨22733864, by rfl⟩ : syracuseStep 30311819 = 45467729) B45467729
theorem B3990959 : Blo 1772087 3990959 := bstep (se 1 (by rfl) ⟨2993219, by rfl⟩ : syracuseStep 3990959 = 5986439) B5986439
theorem B497845763 : Blo 1772087 497845763 := bstep (se 1 (by rfl) ⟨373384322, by rfl⟩ : syracuseStep 497845763 = 746768645) B746768645
theorem B5981849 : Blo 1772087 5981849 := bstep (se 2 (by rfl) ⟨2243193, by rfl⟩ : syracuseStep 5981849 = 4486387) B4486387
theorem B16172855 : Blo 1772087 16172855 := bstep (se 1 (by rfl) ⟨12129641, by rfl⟩ : syracuseStep 16172855 = 24259283) B24259283
theorem B19171151 : Blo 1772087 19171151 := bstep (se 1 (by rfl) ⟨14378363, by rfl⟩ : syracuseStep 19171151 = 28756727) B28756727
theorem B145606531 : Blo 1772087 145606531 := bstep (se 1 (by rfl) ⟨109204898, by rfl⟩ : syracuseStep 145606531 = 218409797) B218409797
theorem B5679047 : Blo 1772087 5679047 := bstep (se 1 (by rfl) ⟨4259285, by rfl⟩ : syracuseStep 5679047 = 8518571) B8518571
theorem B11364371 : Blo 1772087 11364371 := bstep (se 1 (by rfl) ⟨8523278, by rfl⟩ : syracuseStep 11364371 = 17046557) B17046557
theorem B5048531 : Blo 1772087 5048531 := bstep (se 1 (by rfl) ⟨3786398, by rfl⟩ : syracuseStep 5048531 = 7572797) B7572797
theorem B10094827 : Blo 1772087 10094827 := bstep (se 1 (by rfl) ⟨7571120, by rfl⟩ : syracuseStep 10094827 = 15142241) B15142241
theorem B5982443 : Blo 1772087 5982443 := bstep (se 1 (by rfl) ⟨4486832, by rfl⟩ : syracuseStep 5982443 = 8973665) B8973665
theorem B5392619 : Blo 1772087 5392619 := bstep (se 1 (by rfl) ⟨4044464, by rfl⟩ : syracuseStep 5392619 = 8088929) B8088929
theorem B2992423 : Blo 1772087 2992423 := bstep (se 1 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 2992423 = 4488635) B4488635
theorem B23038337 : Blo 1772087 23038337 := bstep (se 2 (by rfl) ⟨8639376, by rfl⟩ : syracuseStep 23038337 = 17278753) B17278753
theorem B5679521 : Blo 1772087 5679521 := bstep (se 2 (by rfl) ⟨2129820, by rfl⟩ : syracuseStep 5679521 = 4259641) B4259641
theorem B3836443 : Blo 1772087 3836443 := bstep (se 1 (by rfl) ⟨2877332, by rfl⟩ : syracuseStep 3836443 = 5754665) B5754665
theorem B48548429 : Blo 1772087 48548429 := bstep (se 3 (by rfl) ⟨9102830, by rfl⟩ : syracuseStep 48548429 = 18205661) B18205661
theorem B3410537 : Blo 1772087 3410537 := bstep (se 2 (by rfl) ⟨1278951, by rfl⟩ : syracuseStep 3410537 = 2557903) B2557903
theorem B1772379 : Blo 1772087 1772379 := bstep (se 1 (by rfl) ⟨1329284, by rfl⟩ : syracuseStep 1772379 = 2658569) B2658569
theorem B20196215 : Blo 1772087 20196215 := bstep (se 1 (by rfl) ⟨15147161, by rfl⟩ : syracuseStep 20196215 = 30294323) B30294323
theorem B1772447 : Blo 1772087 1772447 := bstep (se 1 (by rfl) ⟨1329335, by rfl⟩ : syracuseStep 1772447 = 2658671) B2658671
theorem B6392807 : Blo 1772087 6392807 := bstep (se 1 (by rfl) ⟨4794605, by rfl⟩ : syracuseStep 6392807 = 9589211) B9589211
theorem B1772591 : Blo 1772087 1772591 := bstep (se 1 (by rfl) ⟨1329443, by rfl⟩ : syracuseStep 1772591 = 2658887) B2658887
theorem B1772615 : Blo 1772087 1772615 := bstep (se 1 (by rfl) ⟨1329461, by rfl⟩ : syracuseStep 1772615 = 2658923) B2658923
theorem B25570525 : Blo 1772087 25570525 := bstep (se 3 (by rfl) ⟨4794473, by rfl⟩ : syracuseStep 25570525 = 9588947) B9588947
theorem B1772767 : Blo 1772087 1772767 := bstep (se 1 (by rfl) ⟨1329575, by rfl⟩ : syracuseStep 1772767 = 2659151) B2659151
theorem B2993375 : Blo 1772087 2993375 := bstep (se 1 (by rfl) ⟨2245031, by rfl⟩ : syracuseStep 2993375 = 4490063) B4490063
theorem B7572761 : Blo 1772087 7572761 := bstep (se 2 (by rfl) ⟨2839785, by rfl⟩ : syracuseStep 7572761 = 5679571) B5679571
theorem B1994215 : Blo 1772087 1994215 := bstep (se 1 (by rfl) ⟨1495661, by rfl⟩ : syracuseStep 1994215 = 2991323) B2991323
theorem B1773031 : Blo 1772087 1773031 := bstep (se 1 (by rfl) ⟨1329773, by rfl⟩ : syracuseStep 1773031 = 2659547) B2659547
theorem B5983739 : Blo 1772087 5983739 := bstep (se 1 (by rfl) ⟨4487804, by rfl⟩ : syracuseStep 5983739 = 8975609) B8975609
theorem B11357759 : Blo 1772087 11357759 := bstep (se 1 (by rfl) ⟨8518319, by rfl⟩ : syracuseStep 11357759 = 17036639) B17036639
theorem B1773147 : Blo 1772087 1773147 := bstep (se 1 (by rfl) ⟨1329860, by rfl⟩ : syracuseStep 1773147 = 2659721) B2659721
theorem B45428363 : Blo 1772087 45428363 := bstep (se 1 (by rfl) ⟨34071272, by rfl⟩ : syracuseStep 45428363 = 68142545) B68142545
theorem B10096285 : Blo 1772087 10096285 := bstep (se 3 (by rfl) ⟨1893053, by rfl⟩ : syracuseStep 10096285 = 3786107) B3786107
theorem B5983901 : Blo 1772087 5983901 := bstep (se 3 (by rfl) ⟨1121981, by rfl⟩ : syracuseStep 5983901 = 2243963) B2243963
theorem B5394077 : Blo 1772087 5394077 := bstep (se 3 (by rfl) ⟨1011389, by rfl⟩ : syracuseStep 5394077 = 2022779) B2022779
theorem B10784431 : Blo 1772087 10784431 := bstep (se 1 (by rfl) ⟨8088323, by rfl⟩ : syracuseStep 10784431 = 16176647) B16176647
theorem B13471433 : Blo 1772087 13471433 := bstep (se 2 (by rfl) ⟨5051787, by rfl⟩ : syracuseStep 13471433 = 10103575) B10103575
theorem B1773383 : Blo 1772087 1773383 := bstep (se 1 (by rfl) ⟨1330037, by rfl⟩ : syracuseStep 1773383 = 2660075) B2660075
theorem B2658203 : Blo 1772087 2658203 := bstep (se 1 (by rfl) ⟨1993652, by rfl⟩ : syracuseStep 2658203 = 3987305) B3987305
theorem B1994719 : Blo 1772087 1994719 := bstep (se 1 (by rfl) ⟨1496039, by rfl⟩ : syracuseStep 1994719 = 2992079) B2992079
theorem B1773535 : Blo 1772087 1773535 := bstep (se 1 (by rfl) ⟨1330151, by rfl⟩ : syracuseStep 1773535 = 2660303) B2660303
theorem B19173395 : Blo 1772087 19173395 := bstep (se 1 (by rfl) ⟨14380046, by rfl⟩ : syracuseStep 19173395 = 28760093) B28760093
theorem B25907357 : Blo 1772087 25907357 := bstep (se 3 (by rfl) ⟨4857629, by rfl⟩ : syracuseStep 25907357 = 9715259) B9715259
theorem B5984441 : Blo 1772087 5984441 := bstep (se 2 (by rfl) ⟨2244165, by rfl⟩ : syracuseStep 5984441 = 4488331) B4488331
theorem B1773799 : Blo 1772087 1773799 := bstep (se 1 (by rfl) ⟨1330349, by rfl⟩ : syracuseStep 1773799 = 2660699) B2660699
theorem B5681519 : Blo 1772087 5681519 := bstep (se 1 (by rfl) ⟨4261139, by rfl⟩ : syracuseStep 5681519 = 8522279) B8522279
theorem B1773951 : Blo 1772087 1773951 := bstep (se 1 (by rfl) ⟨1330463, by rfl⟩ : syracuseStep 1773951 = 2660927) B2660927
theorem B2658767 : Blo 1772087 2658767 := bstep (se 1 (by rfl) ⟨1994075, by rfl⟩ : syracuseStep 2658767 = 3988151) B3988151
theorem B46690769 : Blo 1772087 46690769 := bstep (se 2 (by rfl) ⟨17509038, by rfl⟩ : syracuseStep 46690769 = 35018077) B35018077
theorem B1774031 : Blo 1772087 1774031 := bstep (se 1 (by rfl) ⟨1330523, by rfl⟩ : syracuseStep 1774031 = 2661047) B2661047
theorem B2658809 : Blo 1772087 2658809 := bstep (se 2 (by rfl) ⟨997053, by rfl⟩ : syracuseStep 2658809 = 1994107) B1994107
theorem B2658911 : Blo 1772087 2658911 := bstep (se 1 (by rfl) ⟨1994183, by rfl⟩ : syracuseStep 2658911 = 3988367) B3988367
theorem B3641959 : Blo 1772087 3641959 := bstep (se 1 (by rfl) ⟨2731469, by rfl⟩ : syracuseStep 3641959 = 5462939) B5462939
theorem B1995367 : Blo 1772087 1995367 := bstep (se 1 (by rfl) ⟨1496525, by rfl⟩ : syracuseStep 1995367 = 2993051) B2993051
theorem B5681981 : Blo 1772087 5681981 := bstep (se 3 (by rfl) ⟨1065371, by rfl⟩ : syracuseStep 5681981 = 2130743) B2130743
theorem B7574401 : Blo 1772087 7574401 := bstep (se 2 (by rfl) ⟨2840400, by rfl⟩ : syracuseStep 7574401 = 5680801) B5680801
theorem B2839607 : Blo 1772087 2839607 := bstep (se 1 (by rfl) ⟨2129705, by rfl⟩ : syracuseStep 2839607 = 4259411) B4259411
theorem B5051447 : Blo 1772087 5051447 := bstep (se 1 (by rfl) ⟨3788585, by rfl⟩ : syracuseStep 5051447 = 7577171) B7577171
theorem B2659391 : Blo 1772087 2659391 := bstep (se 1 (by rfl) ⟨1994543, by rfl⟩ : syracuseStep 2659391 = 3989087) B3989087
theorem B2659433 : Blo 1772087 2659433 := bstep (se 2 (by rfl) ⟨997287, by rfl⟩ : syracuseStep 2659433 = 1994575) B1994575
theorem B2659535 : Blo 1772087 2659535 := bstep (se 1 (by rfl) ⟨1994651, by rfl⟩ : syracuseStep 2659535 = 3989303) B3989303
theorem B8525087 : Blo 1772087 8525087 := bstep (se 1 (by rfl) ⟨6393815, by rfl⟩ : syracuseStep 8525087 = 12787631) B12787631
theorem B10098017 : Blo 1772087 10098017 := bstep (se 2 (by rfl) ⟨3786756, by rfl⟩ : syracuseStep 10098017 = 7573513) B7573513
theorem B8975771 : Blo 1772087 8975771 := bstep (se 1 (by rfl) ⟨6731828, by rfl⟩ : syracuseStep 8975771 = 13463657) B13463657
theorem B2659739 : Blo 1772087 2659739 := bstep (se 1 (by rfl) ⟨1994804, by rfl⟩ : syracuseStep 2659739 = 3989609) B3989609
theorem B6731207 : Blo 1772087 6731207 := bstep (se 1 (by rfl) ⟨5048405, by rfl⟩ : syracuseStep 6731207 = 10096811) B10096811
theorem B10237529 : Blo 1772087 10237529 := bstep (se 2 (by rfl) ⟨3839073, by rfl⟩ : syracuseStep 10237529 = 7678147) B7678147
theorem B2659961 : Blo 1772087 2659961 := bstep (se 2 (by rfl) ⟨997485, by rfl⟩ : syracuseStep 2659961 = 1994971) B1994971
theorem B2594425 : Blo 1772087 2594425 := bstep (se 2 (by rfl) ⟨972909, by rfl⟩ : syracuseStep 2594425 = 1945819) B1945819
theorem B12785323 : Blo 1772087 12785323 := bstep (se 1 (by rfl) ⟨9588992, by rfl⟩ : syracuseStep 12785323 = 19177985) B19177985
theorem B2660063 : Blo 1772087 2660063 := bstep (se 1 (by rfl) ⟨1995047, by rfl⟩ : syracuseStep 2660063 = 3990095) B3990095
theorem B2660159 : Blo 1772087 2660159 := bstep (se 1 (by rfl) ⟨1995119, by rfl⟩ : syracuseStep 2660159 = 3990239) B3990239
theorem B5683159 : Blo 1772087 5683159 := bstep (se 1 (by rfl) ⟨4262369, by rfl⟩ : syracuseStep 5683159 = 8524739) B8524739
theorem B3987431 : Blo 1772087 3987431 := bstep (se 1 (by rfl) ⟨2990573, by rfl⟩ : syracuseStep 3987431 = 5981147) B5981147
theorem B2660327 : Blo 1772087 2660327 := bstep (se 1 (by rfl) ⟨1995245, by rfl⟩ : syracuseStep 2660327 = 3990491) B3990491
theorem B3987449 : Blo 1772087 3987449 := bstep (se 2 (by rfl) ⟨1495293, by rfl⟩ : syracuseStep 3987449 = 2990587) B2990587
theorem B2660345 : Blo 1772087 2660345 := bstep (se 2 (by rfl) ⟨997629, by rfl⟩ : syracuseStep 2660345 = 1995259) B1995259
theorem B3987539 : Blo 1772087 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B2660447 : Blo 1772087 2660447 := bstep (se 1 (by rfl) ⟨1995335, by rfl⟩ : syracuseStep 2660447 = 3990671) B3990671
theorem B6387817 : Blo 1772087 6387817 := bstep (se 2 (by rfl) ⟨2395431, by rfl⟩ : syracuseStep 6387817 = 4790863) B4790863
theorem B3987611 : Blo 1772087 3987611 := bstep (se 1 (by rfl) ⟨2990708, by rfl⟩ : syracuseStep 3987611 = 5981417) B5981417
theorem B2660507 : Blo 1772087 2660507 := bstep (se 1 (by rfl) ⟨1995380, by rfl⟩ : syracuseStep 2660507 = 3990761) B3990761
theorem B2660543 : Blo 1772087 2660543 := bstep (se 1 (by rfl) ⟨1995407, by rfl⟩ : syracuseStep 2660543 = 3990815) B3990815
theorem B2660585 : Blo 1772087 2660585 := bstep (se 2 (by rfl) ⟨997719, by rfl⟩ : syracuseStep 2660585 = 1995439) B1995439
theorem B5986547 : Blo 1772087 5986547 := bstep (se 1 (by rfl) ⟨4489910, by rfl⟩ : syracuseStep 5986547 = 8979821) B8979821
theorem B4258055 : Blo 1772087 4258055 := bstep (se 1 (by rfl) ⟨3193541, by rfl⟩ : syracuseStep 4258055 = 6387083) B6387083
theorem B3987719 : Blo 1772087 3987719 := bstep (se 1 (by rfl) ⟨2990789, by rfl⟩ : syracuseStep 3987719 = 5981579) B5981579
theorem B5986601 : Blo 1772087 5986601 := bstep (se 2 (by rfl) ⟨2244975, by rfl⟩ : syracuseStep 5986601 = 4489951) B4489951
theorem B2660891 : Blo 1772087 2660891 := bstep (se 1 (by rfl) ⟨1995668, by rfl⟩ : syracuseStep 2660891 = 3991337) B3991337
theorem B3988025 : Blo 1772087 3988025 := bstep (se 2 (by rfl) ⟨1495509, by rfl⟩ : syracuseStep 3988025 = 2991019) B2991019
theorem B20191841 : Blo 1772087 20191841 := bstep (se 2 (by rfl) ⟨7571940, by rfl⟩ : syracuseStep 20191841 = 15143881) B15143881
theorem B2660969 : Blo 1772087 2660969 := bstep (se 2 (by rfl) ⟨997863, by rfl⟩ : syracuseStep 2660969 = 1995727) B1995727
theorem B7191193 : Blo 1772087 7191193 := bstep (se 2 (by rfl) ⟨2696697, by rfl⟩ : syracuseStep 7191193 = 5393395) B5393395
theorem B21568513 : Blo 1772087 21568513 := bstep (se 2 (by rfl) ⟨8088192, by rfl⟩ : syracuseStep 21568513 = 16176385) B16176385
theorem B12778573 : Blo 1772087 12778573 := bstep (se 3 (by rfl) ⟨2395982, by rfl⟩ : syracuseStep 12778573 = 4791965) B4791965
theorem B24255607 : Blo 1772087 24255607 := bstep (se 1 (by rfl) ⟨18191705, by rfl⟩ : syracuseStep 24255607 = 36383411) B36383411
theorem B6732983 : Blo 1772087 6732983 := bstep (se 1 (by rfl) ⟨5049737, by rfl⟩ : syracuseStep 6732983 = 10099475) B10099475
theorem B3988745 : Blo 1772087 3988745 := bstep (se 2 (by rfl) ⟨1495779, by rfl⟩ : syracuseStep 3988745 = 2991559) B2991559
theorem B3366355 : Blo 1772087 3366355 := bstep (se 1 (by rfl) ⟨2524766, by rfl⟩ : syracuseStep 3366355 = 5049533) B5049533
theorem B4488929 : Blo 1772087 4488929 := bstep (se 2 (by rfl) ⟨1683348, by rfl⟩ : syracuseStep 4488929 = 3366697) B3366697
theorem B22716233 : Blo 1772087 22716233 := bstep (se 2 (by rfl) ⟨8518587, by rfl⟩ : syracuseStep 22716233 = 17037175) B17037175
theorem B2695135 : Blo 1772087 2695135 := bstep (se 1 (by rfl) ⟨2021351, by rfl⟩ : syracuseStep 2695135 = 4042703) B4042703
theorem B3989627 : Blo 1772087 3989627 := bstep (se 1 (by rfl) ⟨2992220, by rfl⟩ : syracuseStep 3989627 = 5984441) B5984441
theorem B13459769 : Blo 1772087 13459769 := bstep (se 2 (by rfl) ⟨5047413, by rfl⟩ : syracuseStep 13459769 = 10094827) B10094827
theorem B13468031 : Blo 1772087 13468031 := bstep (se 1 (by rfl) ⟨10101023, by rfl⟩ : syracuseStep 13468031 = 20202047) B20202047
theorem B3989897 : Blo 1772087 3989897 := bstep (se 2 (by rfl) ⟨1496211, by rfl⟩ : syracuseStep 3989897 = 2992423) B2992423
theorem B11354813 : Blo 1772087 11354813 := bstep (se 3 (by rfl) ⟨2129027, by rfl⟩ : syracuseStep 11354813 = 4258055) B4258055
theorem B1893071 : Blo 1772087 1893071 := bstep (se 1 (by rfl) ⟨1419803, by rfl⟩ : syracuseStep 1893071 = 2839607) B2839607
theorem B3367631 : Blo 1772087 3367631 := bstep (se 1 (by rfl) ⟨2525723, by rfl⟩ : syracuseStep 3367631 = 5051447) B5051447
theorem B2130719 : Blo 1772087 2130719 := bstep (se 1 (by rfl) ⟨1598039, by rfl⟩ : syracuseStep 2130719 = 3196079) B3196079
theorem B10093369 : Blo 1772087 10093369 := bstep (se 2 (by rfl) ⟨3785013, by rfl⟩ : syracuseStep 10093369 = 7570027) B7570027
theorem B6825019 : Blo 1772087 6825019 := bstep (se 1 (by rfl) ⟨5118764, by rfl⟩ : syracuseStep 6825019 = 10237529) B10237529
theorem B10781903 : Blo 1772087 10781903 := bstep (se 1 (by rfl) ⟨8086427, by rfl⟩ : syracuseStep 10781903 = 16172855) B16172855
theorem B12780767 : Blo 1772087 12780767 := bstep (se 1 (by rfl) ⟨9585575, by rfl⟩ : syracuseStep 12780767 = 19171151) B19171151
theorem B3786031 : Blo 1772087 3786031 := bstep (se 1 (by rfl) ⟨2839523, by rfl⟩ : syracuseStep 3786031 = 5679047) B5679047
theorem B3991031 : Blo 1772087 3991031 := bstep (se 1 (by rfl) ⟨2993273, by rfl⟩ : syracuseStep 3991031 = 5986547) B5986547
theorem B3991067 : Blo 1772087 3991067 := bstep (se 1 (by rfl) ⟨2993300, by rfl⟩ : syracuseStep 3991067 = 5986601) B5986601
theorem B9094765 : Blo 1772087 9094765 := bstep (se 3 (by rfl) ⟨1705268, by rfl⟩ : syracuseStep 9094765 = 3410537) B3410537
theorem B3786347 : Blo 1772087 3786347 := bstep (se 1 (by rfl) ⟨2839760, by rfl⟩ : syracuseStep 3786347 = 5679521) B5679521
theorem B13461227 : Blo 1772087 13461227 := bstep (se 1 (by rfl) ⟨10095920, by rfl⟩ : syracuseStep 13461227 = 20191841) B20191841
theorem B4261871 : Blo 1772087 4261871 := bstep (se 1 (by rfl) ⟨3196403, by rfl⟩ : syracuseStep 4261871 = 6392807) B6392807
theorem B3459233 : Blo 1772087 3459233 := bstep (se 2 (by rfl) ⟨1297212, by rfl⟩ : syracuseStep 3459233 = 2594425) B2594425
theorem B5048507 : Blo 1772087 5048507 := bstep (se 1 (by rfl) ⟨3786380, by rfl⟩ : syracuseStep 5048507 = 7572761) B7572761
theorem B13461713 : Blo 1772087 13461713 := bstep (se 2 (by rfl) ⟨5048142, by rfl⟩ : syracuseStep 13461713 = 10096285) B10096285
theorem B14379241 : Blo 1772087 14379241 := bstep (se 2 (by rfl) ⟨5392215, by rfl⟩ : syracuseStep 14379241 = 10784431) B10784431
theorem B7571839 : Blo 1772087 7571839 := bstep (se 1 (by rfl) ⟨5678879, by rfl⟩ : syracuseStep 7571839 = 11357759) B11357759
theorem B8980955 : Blo 1772087 8980955 := bstep (se 1 (by rfl) ⟨6735716, by rfl⟩ : syracuseStep 8980955 = 13471433) B13471433
theorem B2992619 : Blo 1772087 2992619 := bstep (se 1 (by rfl) ⟨2244464, by rfl⟩ : syracuseStep 2992619 = 4488929) B4488929
theorem B1772135 : Blo 1772087 1772135 := bstep (se 1 (by rfl) ⟨1329101, by rfl⟩ : syracuseStep 1772135 = 2658203) B2658203
theorem B51129053 : Blo 1772087 51129053 := bstep (se 3 (by rfl) ⟨9586697, by rfl⟩ : syracuseStep 51129053 = 19173395) B19173395
theorem B17271571 : Blo 1772087 17271571 := bstep (se 1 (by rfl) ⟨12953678, by rfl⟩ : syracuseStep 17271571 = 25907357) B25907357
theorem B3787679 : Blo 1772087 3787679 := bstep (se 1 (by rfl) ⟨2840759, by rfl⟩ : syracuseStep 3787679 = 5681519) B5681519
theorem B1772511 : Blo 1772087 1772511 := bstep (se 1 (by rfl) ⟨1329383, by rfl⟩ : syracuseStep 1772511 = 2658767) B2658767
theorem B1772539 : Blo 1772087 1772539 := bstep (se 1 (by rfl) ⟨1329404, by rfl⟩ : syracuseStep 1772539 = 2658809) B2658809
theorem B10103849 : Blo 1772087 10103849 := bstep (se 2 (by rfl) ⟨3788943, by rfl⟩ : syracuseStep 10103849 = 7577887) B7577887
theorem B1772607 : Blo 1772087 1772607 := bstep (se 1 (by rfl) ⟨1329455, by rfl⟩ : syracuseStep 1772607 = 2658911) B2658911
theorem B2993321 : Blo 1772087 2993321 := bstep (se 2 (by rfl) ⟨1122495, by rfl⟩ : syracuseStep 2993321 = 2244991) B2244991
theorem B3787987 : Blo 1772087 3787987 := bstep (se 1 (by rfl) ⟨2840990, by rfl⟩ : syracuseStep 3787987 = 5681981) B5681981
theorem B5115257 : Blo 1772087 5115257 := bstep (se 2 (by rfl) ⟨1918221, by rfl⟩ : syracuseStep 5115257 = 3836443) B3836443
theorem B1772927 : Blo 1772087 1772927 := bstep (se 1 (by rfl) ⟨1329695, by rfl⟩ : syracuseStep 1772927 = 2659391) B2659391
theorem B1772955 : Blo 1772087 1772955 := bstep (se 1 (by rfl) ⟨1329716, by rfl⟩ : syracuseStep 1772955 = 2659433) B2659433
theorem B1773023 : Blo 1772087 1773023 := bstep (se 1 (by rfl) ⟨1329767, by rfl⟩ : syracuseStep 1773023 = 2659535) B2659535
theorem B9588257 : Blo 1772087 9588257 := bstep (se 2 (by rfl) ⟨3595596, by rfl⟩ : syracuseStep 9588257 = 7191193) B7191193
theorem B5983847 : Blo 1772087 5983847 := bstep (se 1 (by rfl) ⟨4487885, by rfl⟩ : syracuseStep 5983847 = 8975771) B8975771
theorem B1773159 : Blo 1772087 1773159 := bstep (se 1 (by rfl) ⟨1329869, by rfl⟩ : syracuseStep 1773159 = 2659739) B2659739
theorem B1773307 : Blo 1772087 1773307 := bstep (se 1 (by rfl) ⟨1329980, by rfl⟩ : syracuseStep 1773307 = 2659961) B2659961
theorem B1773375 : Blo 1772087 1773375 := bstep (se 1 (by rfl) ⟨1330031, by rfl⟩ : syracuseStep 1773375 = 2660063) B2660063
theorem B1773439 : Blo 1772087 1773439 := bstep (se 1 (by rfl) ⟨1330079, by rfl⟩ : syracuseStep 1773439 = 2660159) B2660159
theorem B2658287 : Blo 1772087 2658287 := bstep (se 1 (by rfl) ⟨1993715, by rfl⟩ : syracuseStep 2658287 = 3987431) B3987431
theorem B1773551 : Blo 1772087 1773551 := bstep (se 1 (by rfl) ⟨1330163, by rfl⟩ : syracuseStep 1773551 = 2660327) B2660327
theorem B2658299 : Blo 1772087 2658299 := bstep (se 1 (by rfl) ⟨1993724, by rfl⟩ : syracuseStep 2658299 = 3987449) B3987449
theorem B1773563 : Blo 1772087 1773563 := bstep (se 1 (by rfl) ⟨1330172, by rfl⟩ : syracuseStep 1773563 = 2660345) B2660345
theorem B28758017 : Blo 1772087 28758017 := bstep (se 2 (by rfl) ⟨10784256, by rfl⟩ : syracuseStep 28758017 = 21568513) B21568513
theorem B2658359 : Blo 1772087 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B1773631 : Blo 1772087 1773631 := bstep (se 1 (by rfl) ⟨1330223, by rfl⟩ : syracuseStep 1773631 = 2660447) B2660447
theorem B2658407 : Blo 1772087 2658407 := bstep (se 1 (by rfl) ⟨1993805, by rfl⟩ : syracuseStep 2658407 = 3987611) B3987611
theorem B1773671 : Blo 1772087 1773671 := bstep (se 1 (by rfl) ⟨1330253, by rfl⟩ : syracuseStep 1773671 = 2660507) B2660507
theorem B1773695 : Blo 1772087 1773695 := bstep (se 1 (by rfl) ⟨1330271, by rfl⟩ : syracuseStep 1773695 = 2660543) B2660543
theorem B1773723 : Blo 1772087 1773723 := bstep (se 1 (by rfl) ⟨1330292, by rfl⟩ : syracuseStep 1773723 = 2660585) B2660585
theorem B2658479 : Blo 1772087 2658479 := bstep (se 1 (by rfl) ⟨1993859, by rfl⟩ : syracuseStep 2658479 = 3987719) B3987719
theorem B1773927 : Blo 1772087 1773927 := bstep (se 1 (by rfl) ⟨1330445, by rfl⟩ : syracuseStep 1773927 = 2660891) B2660891
theorem B2658683 : Blo 1772087 2658683 := bstep (se 1 (by rfl) ⟨1994012, by rfl⟩ : syracuseStep 2658683 = 3988025) B3988025
theorem B1773979 : Blo 1772087 1773979 := bstep (se 1 (by rfl) ⟨1330484, by rfl⟩ : syracuseStep 1773979 = 2660969) B2660969
theorem B13464143 : Blo 1772087 13464143 := bstep (se 1 (by rfl) ⟨10098107, by rfl⟩ : syracuseStep 13464143 = 20196215) B20196215
theorem B2658953 : Blo 1772087 2658953 := bstep (se 2 (by rfl) ⟨997107, by rfl⟩ : syracuseStep 2658953 = 1994215) B1994215
theorem B1995583 : Blo 1772087 1995583 := bstep (se 1 (by rfl) ⟨1496687, by rfl⟩ : syracuseStep 1995583 = 2993375) B2993375
theorem B2659163 : Blo 1772087 2659163 := bstep (se 1 (by rfl) ⟨1994372, by rfl⟩ : syracuseStep 2659163 = 3988745) B3988745
theorem B15144155 : Blo 1772087 15144155 := bstep (se 1 (by rfl) ⟨11358116, by rfl⟩ : syracuseStep 15144155 = 22716233) B22716233
theorem B3593513 : Blo 1772087 3593513 := bstep (se 2 (by rfl) ⟨1347567, by rfl⟩ : syracuseStep 3593513 = 2695135) B2695135
theorem B2659625 : Blo 1772087 2659625 := bstep (se 2 (by rfl) ⟨997359, by rfl⟩ : syracuseStep 2659625 = 1994719) B1994719
theorem B8517089 : Blo 1772087 8517089 := bstep (se 2 (by rfl) ⟨3193908, by rfl⟩ : syracuseStep 8517089 = 6387817) B6387817
theorem B5051879 : Blo 1772087 5051879 := bstep (se 1 (by rfl) ⟨3788909, by rfl⟩ : syracuseStep 5051879 = 7577819) B7577819
theorem B2659823 : Blo 1772087 2659823 := bstep (se 1 (by rfl) ⟨1994867, by rfl⟩ : syracuseStep 2659823 = 3989735) B3989735
theorem B31127179 : Blo 1772087 31127179 := bstep (se 1 (by rfl) ⟨23345384, by rfl⟩ : syracuseStep 31127179 = 46690769) B46690769
theorem B3364571 : Blo 1772087 3364571 := bstep (se 1 (by rfl) ⟨2523428, by rfl⟩ : syracuseStep 3364571 = 5046857) B5046857
theorem B3987323 : Blo 1772087 3987323 := bstep (se 1 (by rfl) ⟨2990492, by rfl⟩ : syracuseStep 3987323 = 5980985) B5980985
theorem B2660219 : Blo 1772087 2660219 := bstep (se 1 (by rfl) ⟨1995164, by rfl⟩ : syracuseStep 2660219 = 3990329) B3990329
theorem B15144839 : Blo 1772087 15144839 := bstep (se 1 (by rfl) ⟨11358629, by rfl⟩ : syracuseStep 15144839 = 22717259) B22717259
theorem B3987359 : Blo 1772087 3987359 := bstep (se 1 (by rfl) ⟨2990519, by rfl⟩ : syracuseStep 3987359 = 5981039) B5981039
theorem B2660255 : Blo 1772087 2660255 := bstep (se 1 (by rfl) ⟨1995191, by rfl⟩ : syracuseStep 2660255 = 3990383) B3990383
theorem B16177121 : Blo 1772087 16177121 := bstep (se 2 (by rfl) ⟨6066420, by rfl⟩ : syracuseStep 16177121 = 12132841) B12132841
theorem B2021447 : Blo 1772087 2021447 := bstep (se 1 (by rfl) ⟨1516085, by rfl⟩ : syracuseStep 2021447 = 3032171) B3032171
theorem B3987593 : Blo 1772087 3987593 := bstep (se 2 (by rfl) ⟨1495347, by rfl⟩ : syracuseStep 3987593 = 2990695) B2990695
theorem B4855945 : Blo 1772087 4855945 := bstep (se 2 (by rfl) ⟨1820979, by rfl⟩ : syracuseStep 4855945 = 3641959) B3641959
theorem B2660489 : Blo 1772087 2660489 := bstep (se 2 (by rfl) ⟨997683, by rfl⟩ : syracuseStep 2660489 = 1995367) B1995367
theorem B5683391 : Blo 1772087 5683391 := bstep (se 1 (by rfl) ⟨4262543, by rfl⟩ : syracuseStep 5683391 = 8525087) B8525087
theorem B6732011 : Blo 1772087 6732011 := bstep (se 1 (by rfl) ⟨5049008, by rfl⟩ : syracuseStep 6732011 = 10098017) B10098017
theorem B20207879 : Blo 1772087 20207879 := bstep (se 1 (by rfl) ⟨15155909, by rfl⟩ : syracuseStep 20207879 = 30311819) B30311819
theorem B2660639 : Blo 1772087 2660639 := bstep (se 1 (by rfl) ⟨1995479, by rfl⟩ : syracuseStep 2660639 = 3990959) B3990959
theorem B4487471 : Blo 1772087 4487471 := bstep (se 1 (by rfl) ⟨3365603, by rfl⟩ : syracuseStep 4487471 = 6731207) B6731207
theorem B331897175 : Blo 1772087 331897175 := bstep (se 1 (by rfl) ⟨248922881, by rfl⟩ : syracuseStep 331897175 = 497845763) B497845763
theorem B3987809 : Blo 1772087 3987809 := bstep (se 2 (by rfl) ⟨1495428, by rfl⟩ : syracuseStep 3987809 = 2990857) B2990857
theorem B3987899 : Blo 1772087 3987899 := bstep (se 1 (by rfl) ⟨2990924, by rfl⟩ : syracuseStep 3987899 = 5981849) B5981849
theorem B10099201 : Blo 1772087 10099201 := bstep (se 2 (by rfl) ⟨3787200, by rfl⟩ : syracuseStep 10099201 = 7574401) B7574401
theorem B7576247 : Blo 1772087 7576247 := bstep (se 1 (by rfl) ⟨5682185, by rfl⟩ : syracuseStep 7576247 = 11364371) B11364371
theorem B17038097 : Blo 1772087 17038097 := bstep (se 2 (by rfl) ⟨6389286, by rfl⟩ : syracuseStep 17038097 = 12778573) B12778573
theorem B3365687 : Blo 1772087 3365687 := bstep (se 1 (by rfl) ⟨2524265, by rfl⟩ : syracuseStep 3365687 = 5048531) B5048531
theorem B2841401 : Blo 1772087 2841401 := bstep (se 2 (by rfl) ⟨1065525, by rfl⟩ : syracuseStep 2841401 = 2131051) B2131051
theorem B3988295 : Blo 1772087 3988295 := bstep (se 1 (by rfl) ⟨2991221, by rfl⟩ : syracuseStep 3988295 = 5982443) B5982443
theorem B32340809 : Blo 1772087 32340809 := bstep (se 2 (by rfl) ⟨12127803, by rfl⟩ : syracuseStep 32340809 = 24255607) B24255607
theorem B3595079 : Blo 1772087 3595079 := bstep (se 1 (by rfl) ⟨2696309, by rfl⟩ : syracuseStep 3595079 = 5392619) B5392619
theorem B15358891 : Blo 1772087 15358891 := bstep (se 1 (by rfl) ⟨11519168, by rfl⟩ : syracuseStep 15358891 = 23038337) B23038337
theorem B34094033 : Blo 1772087 34094033 := bstep (se 2 (by rfl) ⟨12785262, by rfl⟩ : syracuseStep 34094033 = 25570525) B25570525
theorem B32365619 : Blo 1772087 32365619 := bstep (se 1 (by rfl) ⟨24274214, by rfl⟩ : syracuseStep 32365619 = 48548429) B48548429
theorem B3988601 : Blo 1772087 3988601 := bstep (se 2 (by rfl) ⟨1495725, by rfl⟩ : syracuseStep 3988601 = 2991451) B2991451
theorem B4488473 : Blo 1772087 4488473 := bstep (se 2 (by rfl) ⟨1683177, by rfl⟩ : syracuseStep 4488473 = 3366355) B3366355
theorem B13458797 : Blo 1772087 13458797 := bstep (se 3 (by rfl) ⟨2523524, by rfl⟩ : syracuseStep 13458797 = 5047049) B5047049
theorem B4488655 : Blo 1772087 4488655 := bstep (se 1 (by rfl) ⟨3366491, by rfl⟩ : syracuseStep 4488655 = 6732983) B6732983
theorem B17047097 : Blo 1772087 17047097 := bstep (se 2 (by rfl) ⟨6392661, by rfl⟩ : syracuseStep 17047097 = 12785323) B12785323
theorem B3989159 : Blo 1772087 3989159 := bstep (se 1 (by rfl) ⟨2991869, by rfl⟩ : syracuseStep 3989159 = 5983739) B5983739
theorem B30285575 : Blo 1772087 30285575 := bstep (se 1 (by rfl) ⟨22714181, by rfl⟩ : syracuseStep 30285575 = 45428363) B45428363
theorem B3989267 : Blo 1772087 3989267 := bstep (se 1 (by rfl) ⟨2991950, by rfl⟩ : syracuseStep 3989267 = 5983901) B5983901
theorem B3596051 : Blo 1772087 3596051 := bstep (se 1 (by rfl) ⟨2697038, by rfl⟩ : syracuseStep 3596051 = 5394077) B5394077
theorem B194142041 : Blo 1772087 194142041 := bstep (se 2 (by rfl) ⟨72803265, by rfl⟩ : syracuseStep 194142041 = 145606531) B145606531
theorem B7577545 : Blo 1772087 7577545 := bstep (se 2 (by rfl) ⟨2841579, by rfl⟩ : syracuseStep 7577545 = 5683159) B5683159
theorem B5390525 : Blo 1772087 5390525 := bstep (se 3 (by rfl) ⟨1010723, by rfl⟩ : syracuseStep 5390525 = 2021447) B2021447
theorem B8978687 : Blo 1772087 8978687 := bstep (se 1 (by rfl) ⟨6734015, by rfl⟩ : syracuseStep 8978687 = 13468031) B13468031
theorem B7569875 : Blo 1772087 7569875 := bstep (se 1 (by rfl) ⟨5677406, by rfl⟩ : syracuseStep 7569875 = 11354813) B11354813
theorem B2245087 : Blo 1772087 2245087 := bstep (se 1 (by rfl) ⟨1683815, by rfl⟩ : syracuseStep 2245087 = 3367631) B3367631
theorem B8520511 : Blo 1772087 8520511 := bstep (se 1 (by rfl) ⟨6390383, by rfl⟩ : syracuseStep 8520511 = 12780767) B12780767
theorem B3367919 : Blo 1772087 3367919 := bstep (se 1 (by rfl) ⟨2525939, by rfl⟩ : syracuseStep 3367919 = 5051879) B5051879
theorem B23028761 : Blo 1772087 23028761 := bstep (se 2 (by rfl) ⟨8635785, by rfl⟩ : syracuseStep 23028761 = 17271571) B17271571
theorem B2524231 : Blo 1772087 2524231 := bstep (se 1 (by rfl) ⟨1893173, by rfl⟩ : syracuseStep 2524231 = 3786347) B3786347
theorem B2991647 : Blo 1772087 2991647 := bstep (se 1 (by rfl) ⟨2243735, by rfl⟩ : syracuseStep 2991647 = 4487471) B4487471
theorem B5048041 : Blo 1772087 5048041 := bstep (se 2 (by rfl) ⟨1893015, by rfl⟩ : syracuseStep 5048041 = 3786031) B3786031
theorem B1894267 : Blo 1772087 1894267 := bstep (se 1 (by rfl) ⟨1420700, by rfl⟩ : syracuseStep 1894267 = 2841401) B2841401
theorem B5048189 : Blo 1772087 5048189 := bstep (se 3 (by rfl) ⟨946535, by rfl⟩ : syracuseStep 5048189 = 1893071) B1893071
theorem B6735899 : Blo 1772087 6735899 := bstep (se 1 (by rfl) ⟨5051924, by rfl⟩ : syracuseStep 6735899 = 10103849) B10103849
theorem B12126353 : Blo 1772087 12126353 := bstep (se 2 (by rfl) ⟨4547382, by rfl⟩ : syracuseStep 12126353 = 9094765) B9094765
theorem B41502905 : Blo 1772087 41502905 := bstep (se 2 (by rfl) ⟨15563589, by rfl⟩ : syracuseStep 41502905 = 31127179) B31127179
theorem B2992315 : Blo 1772087 2992315 := bstep (se 1 (by rfl) ⟨2244236, by rfl⟩ : syracuseStep 2992315 = 4488473) B4488473
theorem B8972531 : Blo 1772087 8972531 := bstep (se 1 (by rfl) ⟨6729398, by rfl⟩ : syracuseStep 8972531 = 13458797) B13458797
theorem B3410171 : Blo 1772087 3410171 := bstep (se 1 (by rfl) ⟨2557628, by rfl⟩ : syracuseStep 3410171 = 5115257) B5115257
theorem B6392171 : Blo 1772087 6392171 := bstep (se 1 (by rfl) ⟨4794128, by rfl⟩ : syracuseStep 6392171 = 9588257) B9588257
theorem B11364731 : Blo 1772087 11364731 := bstep (se 1 (by rfl) ⟨8523548, by rfl⟩ : syracuseStep 11364731 = 17047097) B17047097
theorem B129428027 : Blo 1772087 129428027 := bstep (se 1 (by rfl) ⟨97071020, by rfl⟩ : syracuseStep 129428027 = 194142041) B194142041
theorem B10103393 : Blo 1772087 10103393 := bstep (se 2 (by rfl) ⟨3788772, by rfl⟩ : syracuseStep 10103393 = 7577545) B7577545
theorem B1772191 : Blo 1772087 1772191 := bstep (se 1 (by rfl) ⟨1329143, by rfl⟩ : syracuseStep 1772191 = 2658287) B2658287
theorem B1772199 : Blo 1772087 1772199 := bstep (se 1 (by rfl) ⟨1329149, by rfl⟩ : syracuseStep 1772199 = 2658299) B2658299
theorem B76688045 : Blo 1772087 76688045 := bstep (se 3 (by rfl) ⟨14379008, by rfl⟩ : syracuseStep 76688045 = 28758017) B28758017
theorem B1772239 : Blo 1772087 1772239 := bstep (se 1 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 1772239 = 2658359) B2658359
theorem B1772271 : Blo 1772087 1772271 := bstep (se 1 (by rfl) ⟨1329203, by rfl⟩ : syracuseStep 1772271 = 2658407) B2658407
theorem B1772319 : Blo 1772087 1772319 := bstep (se 1 (by rfl) ⟨1329239, by rfl⟩ : syracuseStep 1772319 = 2658479) B2658479
theorem B6474593 : Blo 1772087 6474593 := bstep (se 2 (by rfl) ⟨2427972, by rfl⟩ : syracuseStep 6474593 = 4855945) B4855945
theorem B8973179 : Blo 1772087 8973179 := bstep (se 1 (by rfl) ⟨6729884, by rfl⟩ : syracuseStep 8973179 = 13459769) B13459769
theorem B1772455 : Blo 1772087 1772455 := bstep (se 1 (by rfl) ⟨1329341, by rfl⟩ : syracuseStep 1772455 = 2658683) B2658683
theorem B19172321 : Blo 1772087 19172321 := bstep (se 2 (by rfl) ⟨7189620, by rfl⟩ : syracuseStep 19172321 = 14379241) B14379241
theorem B1772635 : Blo 1772087 1772635 := bstep (se 1 (by rfl) ⟨1329476, by rfl⟩ : syracuseStep 1772635 = 2658953) B2658953
theorem B13462685 : Blo 1772087 13462685 := bstep (se 3 (by rfl) ⟨2524253, by rfl⟩ : syracuseStep 13462685 = 5048507) B5048507
theorem B10095785 : Blo 1772087 10095785 := bstep (se 2 (by rfl) ⟨3785919, by rfl⟩ : syracuseStep 10095785 = 7571839) B7571839
theorem B1772775 : Blo 1772087 1772775 := bstep (se 1 (by rfl) ⟨1329581, by rfl⟩ : syracuseStep 1772775 = 2659163) B2659163
theorem B7187935 : Blo 1772087 7187935 := bstep (se 1 (by rfl) ⟨5390951, by rfl⟩ : syracuseStep 7187935 = 10781903) B10781903
theorem B10096103 : Blo 1772087 10096103 := bstep (se 1 (by rfl) ⟨7572077, by rfl⟩ : syracuseStep 10096103 = 15144155) B15144155
theorem B2395675 : Blo 1772087 2395675 := bstep (se 1 (by rfl) ⟨1796756, by rfl⟩ : syracuseStep 2395675 = 3593513) B3593513
theorem B1773083 : Blo 1772087 1773083 := bstep (se 1 (by rfl) ⟨1329812, by rfl⟩ : syracuseStep 1773083 = 2659625) B2659625
theorem B1773215 : Blo 1772087 1773215 := bstep (se 1 (by rfl) ⟨1329911, by rfl⟩ : syracuseStep 1773215 = 2659823) B2659823
theorem B8974151 : Blo 1772087 8974151 := bstep (se 1 (by rfl) ⟨6730613, by rfl⟩ : syracuseStep 8974151 = 13461227) B13461227
theorem B2658215 : Blo 1772087 2658215 := bstep (se 1 (by rfl) ⟨1993661, by rfl⟩ : syracuseStep 2658215 = 3987323) B3987323
theorem B1773479 : Blo 1772087 1773479 := bstep (se 1 (by rfl) ⟨1330109, by rfl⟩ : syracuseStep 1773479 = 2660219) B2660219
theorem B22712237 : Blo 1772087 22712237 := bstep (se 3 (by rfl) ⟨4258544, by rfl⟩ : syracuseStep 22712237 = 8517089) B8517089
theorem B10096559 : Blo 1772087 10096559 := bstep (se 1 (by rfl) ⟨7572419, by rfl⟩ : syracuseStep 10096559 = 15144839) B15144839
theorem B2658239 : Blo 1772087 2658239 := bstep (se 1 (by rfl) ⟨1993679, by rfl⟩ : syracuseStep 2658239 = 3987359) B3987359
theorem B1773503 : Blo 1772087 1773503 := bstep (se 1 (by rfl) ⟨1330127, by rfl⟩ : syracuseStep 1773503 = 2660255) B2660255
theorem B10784747 : Blo 1772087 10784747 := bstep (se 1 (by rfl) ⟨8088560, by rfl⟩ : syracuseStep 10784747 = 16177121) B16177121
theorem B2658395 : Blo 1772087 2658395 := bstep (se 1 (by rfl) ⟨1993796, by rfl⟩ : syracuseStep 2658395 = 3987593) B3987593
theorem B1773659 : Blo 1772087 1773659 := bstep (se 1 (by rfl) ⟨1330244, by rfl⟩ : syracuseStep 1773659 = 2660489) B2660489
theorem B2306155 : Blo 1772087 2306155 := bstep (se 1 (by rfl) ⟨1729616, by rfl⟩ : syracuseStep 2306155 = 3459233) B3459233
theorem B3788927 : Blo 1772087 3788927 := bstep (se 1 (by rfl) ⟨2841695, by rfl⟩ : syracuseStep 3788927 = 5683391) B5683391
theorem B8974475 : Blo 1772087 8974475 := bstep (se 1 (by rfl) ⟨6730856, by rfl⟩ : syracuseStep 8974475 = 13461713) B13461713
theorem B13471919 : Blo 1772087 13471919 := bstep (se 1 (by rfl) ⟨10103939, by rfl⟩ : syracuseStep 13471919 = 20207879) B20207879
theorem B1773759 : Blo 1772087 1773759 := bstep (se 1 (by rfl) ⟨1330319, by rfl⟩ : syracuseStep 1773759 = 2660639) B2660639
theorem B2658539 : Blo 1772087 2658539 := bstep (se 1 (by rfl) ⟨1993904, by rfl⟩ : syracuseStep 2658539 = 3987809) B3987809
theorem B5050649 : Blo 1772087 5050649 := bstep (se 2 (by rfl) ⟨1893993, by rfl⟩ : syracuseStep 5050649 = 3787987) B3787987
theorem B2658599 : Blo 1772087 2658599 := bstep (se 1 (by rfl) ⟨1993949, by rfl⟩ : syracuseStep 2658599 = 3987899) B3987899
theorem B1995079 : Blo 1772087 1995079 := bstep (se 1 (by rfl) ⟨1496309, by rfl⟩ : syracuseStep 1995079 = 2992619) B2992619
theorem B5050831 : Blo 1772087 5050831 := bstep (se 1 (by rfl) ⟨3788123, by rfl⟩ : syracuseStep 5050831 = 7576247) B7576247
theorem B11358731 : Blo 1772087 11358731 := bstep (se 1 (by rfl) ⟨8519048, by rfl⟩ : syracuseStep 11358731 = 17038097) B17038097
theorem B2658863 : Blo 1772087 2658863 := bstep (se 1 (by rfl) ⟨1994147, by rfl⟩ : syracuseStep 2658863 = 3988295) B3988295
theorem B2396719 : Blo 1772087 2396719 := bstep (se 1 (by rfl) ⟨1797539, by rfl⟩ : syracuseStep 2396719 = 3595079) B3595079
theorem B5984873 : Blo 1772087 5984873 := bstep (se 2 (by rfl) ⟨2244327, by rfl⟩ : syracuseStep 5984873 = 4488655) B4488655
theorem B22729355 : Blo 1772087 22729355 := bstep (se 1 (by rfl) ⟨17047016, by rfl⟩ : syracuseStep 22729355 = 34094033) B34094033
theorem B2659067 : Blo 1772087 2659067 := bstep (se 1 (by rfl) ⟨1994300, by rfl⟩ : syracuseStep 2659067 = 3988601) B3988601
theorem B5681917 : Blo 1772087 5681917 := bstep (se 3 (by rfl) ⟨1065359, by rfl⟩ : syracuseStep 5681917 = 2130719) B2130719
theorem B1995547 : Blo 1772087 1995547 := bstep (se 1 (by rfl) ⟨1496660, by rfl⟩ : syracuseStep 1995547 = 2993321) B2993321
theorem B2659439 : Blo 1772087 2659439 := bstep (se 1 (by rfl) ⟨1994579, by rfl⟩ : syracuseStep 2659439 = 3989159) B3989159
theorem B20190383 : Blo 1772087 20190383 := bstep (se 1 (by rfl) ⟨15142787, by rfl⟩ : syracuseStep 20190383 = 30285575) B30285575
theorem B2659511 : Blo 1772087 2659511 := bstep (se 1 (by rfl) ⟨1994633, by rfl⟩ : syracuseStep 2659511 = 3989267) B3989267
theorem B2397367 : Blo 1772087 2397367 := bstep (se 1 (by rfl) ⟨1798025, by rfl⟩ : syracuseStep 2397367 = 3596051) B3596051
theorem B2659751 : Blo 1772087 2659751 := bstep (se 1 (by rfl) ⟨1994813, by rfl⟩ : syracuseStep 2659751 = 3989627) B3989627
theorem B2659931 : Blo 1772087 2659931 := bstep (se 1 (by rfl) ⟨1994948, by rfl⟩ : syracuseStep 2659931 = 3989897) B3989897
theorem B8976095 : Blo 1772087 8976095 := bstep (se 1 (by rfl) ⟨6732071, by rfl⟩ : syracuseStep 8976095 = 13464143) B13464143
theorem B13465601 : Blo 1772087 13465601 := bstep (se 2 (by rfl) ⟨5049600, by rfl⟩ : syracuseStep 13465601 = 10099201) B10099201
theorem B2660687 : Blo 1772087 2660687 := bstep (se 1 (by rfl) ⟨1995515, by rfl⟩ : syracuseStep 2660687 = 3991031) B3991031
theorem B2660711 : Blo 1772087 2660711 := bstep (se 1 (by rfl) ⟨1995533, by rfl⟩ : syracuseStep 2660711 = 3991067) B3991067
theorem B13457825 : Blo 1772087 13457825 := bstep (se 2 (by rfl) ⟨5046684, by rfl⟩ : syracuseStep 13457825 = 10093369) B10093369
theorem B2660777 : Blo 1772087 2660777 := bstep (se 2 (by rfl) ⟨997791, by rfl⟩ : syracuseStep 2660777 = 1995583) B1995583
theorem B2243047 : Blo 1772087 2243047 := bstep (se 1 (by rfl) ⟨1682285, by rfl⟩ : syracuseStep 2243047 = 3364571) B3364571
theorem B20478521 : Blo 1772087 20478521 := bstep (se 2 (by rfl) ⟨7679445, by rfl⟩ : syracuseStep 20478521 = 15358891) B15358891
theorem B2841247 : Blo 1772087 2841247 := bstep (se 1 (by rfl) ⟨2130935, by rfl⟩ : syracuseStep 2841247 = 4261871) B4261871
theorem B9100025 : Blo 1772087 9100025 := bstep (se 2 (by rfl) ⟨3412509, by rfl⟩ : syracuseStep 9100025 = 6825019) B6825019
theorem B4488007 : Blo 1772087 4488007 := bstep (se 1 (by rfl) ⟨3366005, by rfl⟩ : syracuseStep 4488007 = 6732011) B6732011
theorem B221264783 : Blo 1772087 221264783 := bstep (se 1 (by rfl) ⟨165948587, by rfl⟩ : syracuseStep 221264783 = 331897175) B331897175
theorem B5987303 : Blo 1772087 5987303 := bstep (se 1 (by rfl) ⟨4490477, by rfl⟩ : syracuseStep 5987303 = 8980955) B8980955
theorem B34086035 : Blo 1772087 34086035 := bstep (se 1 (by rfl) ⟨25564526, by rfl⟩ : syracuseStep 34086035 = 51129053) B51129053
theorem B2243791 : Blo 1772087 2243791 := bstep (se 1 (by rfl) ⟨1682843, by rfl⟩ : syracuseStep 2243791 = 3365687) B3365687
theorem B21560539 : Blo 1772087 21560539 := bstep (se 1 (by rfl) ⟨16170404, by rfl⟩ : syracuseStep 21560539 = 32340809) B32340809
theorem B21577079 : Blo 1772087 21577079 := bstep (se 1 (by rfl) ⟨16182809, by rfl⟩ : syracuseStep 21577079 = 32365619) B32365619
theorem B3989231 : Blo 1772087 3989231 := bstep (se 1 (by rfl) ⟨2991923, by rfl⟩ : syracuseStep 3989231 = 5983847) B5983847
theorem B10100477 : Blo 1772087 10100477 := bstep (se 3 (by rfl) ⟨1893839, by rfl⟩ : syracuseStep 10100477 = 3787679) B3787679
theorem B3367099 : Blo 1772087 3367099 := bstep (se 1 (by rfl) ⟨2525324, by rfl⟩ : syracuseStep 3367099 = 5050649) B5050649
theorem B3989753 : Blo 1772087 3989753 := bstep (se 2 (by rfl) ⟨1496157, by rfl⟩ : syracuseStep 3989753 = 2992315) B2992315
theorem B5046583 : Blo 1772087 5046583 := bstep (se 1 (by rfl) ⟨3784937, by rfl⟩ : syracuseStep 5046583 = 7569875) B7569875
theorem B3989915 : Blo 1772087 3989915 := bstep (se 1 (by rfl) ⟨2992436, by rfl⟩ : syracuseStep 3989915 = 5984873) B5984873
theorem B6734441 : Blo 1772087 6734441 := bstep (se 2 (by rfl) ⟨2525415, by rfl⟩ : syracuseStep 6734441 = 5050831) B5050831
theorem B2990729 : Blo 1772087 2990729 := bstep (se 2 (by rfl) ⟨1121523, by rfl⟩ : syracuseStep 2990729 = 2243047) B2243047
theorem B15352507 : Blo 1772087 15352507 := bstep (se 1 (by rfl) ⟨11514380, by rfl⟩ : syracuseStep 15352507 = 23028761) B23028761
theorem B3195625 : Blo 1772087 3195625 := bstep (se 2 (by rfl) ⟨1198359, by rfl⟩ : syracuseStep 3195625 = 2396719) B2396719
theorem B13460255 : Blo 1772087 13460255 := bstep (se 1 (by rfl) ⟨10095191, by rfl⟩ : syracuseStep 13460255 = 20190383) B20190383
theorem B4490599 : Blo 1772087 4490599 := bstep (se 1 (by rfl) ⟨3367949, by rfl⟩ : syracuseStep 4490599 = 6735899) B6735899
theorem B5981687 : Blo 1772087 5981687 := bstep (se 1 (by rfl) ⟨4486265, by rfl⟩ : syracuseStep 5981687 = 8972531) B8972531
theorem B4261447 : Blo 1772087 4261447 := bstep (se 1 (by rfl) ⟨3196085, by rfl⟩ : syracuseStep 4261447 = 6392171) B6392171
theorem B3196489 : Blo 1772087 3196489 := bstep (se 2 (by rfl) ⟨1198683, by rfl⟩ : syracuseStep 3196489 = 2397367) B2397367
theorem B2991721 : Blo 1772087 2991721 := bstep (se 2 (by rfl) ⟨1121895, by rfl⟩ : syracuseStep 2991721 = 2243791) B2243791
theorem B8971883 : Blo 1772087 8971883 := bstep (se 1 (by rfl) ⟨6728912, by rfl⟩ : syracuseStep 8971883 = 13457825) B13457825
theorem B28747385 : Blo 1772087 28747385 := bstep (se 2 (by rfl) ⟨10780269, by rfl⟩ : syracuseStep 28747385 = 21560539) B21560539
theorem B6735595 : Blo 1772087 6735595 := bstep (se 1 (by rfl) ⟨5051696, by rfl⟩ : syracuseStep 6735595 = 10103393) B10103393
theorem B5982119 : Blo 1772087 5982119 := bstep (se 1 (by rfl) ⟨4486589, by rfl⟩ : syracuseStep 5982119 = 8973179) B8973179
theorem B12781547 : Blo 1772087 12781547 := bstep (se 1 (by rfl) ⟨9586160, by rfl⟩ : syracuseStep 12781547 = 19172321) B19172321
theorem B3991535 : Blo 1772087 3991535 := bstep (se 1 (by rfl) ⟨2993651, by rfl⟩ : syracuseStep 3991535 = 5987303) B5987303
theorem B2525689 : Blo 1772087 2525689 := bstep (se 2 (by rfl) ⟨947133, by rfl⟩ : syracuseStep 2525689 = 1894267) B1894267
theorem B5982767 : Blo 1772087 5982767 := bstep (se 1 (by rfl) ⟨4487075, by rfl⟩ : syracuseStep 5982767 = 8974151) B8974151
theorem B1772143 : Blo 1772087 1772143 := bstep (se 1 (by rfl) ⟨1329107, by rfl⟩ : syracuseStep 1772143 = 2658215) B2658215
theorem B15141491 : Blo 1772087 15141491 := bstep (se 1 (by rfl) ⟨11356118, by rfl⟩ : syracuseStep 15141491 = 22712237) B22712237
theorem B8981117 : Blo 1772087 8981117 := bstep (se 3 (by rfl) ⟨1683959, by rfl⟩ : syracuseStep 8981117 = 3367919) B3367919
theorem B1772159 : Blo 1772087 1772159 := bstep (se 1 (by rfl) ⟨1329119, by rfl⟩ : syracuseStep 1772159 = 2658239) B2658239
theorem B1772263 : Blo 1772087 1772263 := bstep (se 1 (by rfl) ⟨1329197, by rfl⟩ : syracuseStep 1772263 = 2658395) B2658395
theorem B2525951 : Blo 1772087 2525951 := bstep (se 1 (by rfl) ⟨1894463, by rfl⟩ : syracuseStep 2525951 = 3788927) B3788927
theorem B5982983 : Blo 1772087 5982983 := bstep (se 1 (by rfl) ⟨4487237, by rfl⟩ : syracuseStep 5982983 = 8974475) B8974475
theorem B8981279 : Blo 1772087 8981279 := bstep (se 1 (by rfl) ⟨6735959, by rfl⟩ : syracuseStep 8981279 = 13471919) B13471919
theorem B3074873 : Blo 1772087 3074873 := bstep (se 2 (by rfl) ⟨1153077, by rfl⟩ : syracuseStep 3074873 = 2306155) B2306155
theorem B1772359 : Blo 1772087 1772359 := bstep (se 1 (by rfl) ⟨1329269, by rfl⟩ : syracuseStep 1772359 = 2658539) B2658539
theorem B1772399 : Blo 1772087 1772399 := bstep (se 1 (by rfl) ⟨1329299, by rfl⟩ : syracuseStep 1772399 = 2658599) B2658599
theorem B1772575 : Blo 1772087 1772575 := bstep (se 1 (by rfl) ⟨1329431, by rfl⟩ : syracuseStep 1772575 = 2658863) B2658863
theorem B32336941 : Blo 1772087 32336941 := bstep (se 3 (by rfl) ⟨6063176, by rfl⟩ : syracuseStep 32336941 = 12126353) B12126353
theorem B1772711 : Blo 1772087 1772711 := bstep (se 1 (by rfl) ⟨1329533, by rfl⟩ : syracuseStep 1772711 = 2659067) B2659067
theorem B2993449 : Blo 1772087 2993449 := bstep (se 2 (by rfl) ⟨1122543, by rfl⟩ : syracuseStep 2993449 = 2245087) B2245087
theorem B1772959 : Blo 1772087 1772959 := bstep (se 1 (by rfl) ⟨1329719, by rfl⟩ : syracuseStep 1772959 = 2659439) B2659439
theorem B1773007 : Blo 1772087 1773007 := bstep (se 1 (by rfl) ⟨1329755, by rfl⟩ : syracuseStep 1773007 = 2659511) B2659511
theorem B3788329 : Blo 1772087 3788329 := bstep (se 2 (by rfl) ⟨1420623, by rfl⟩ : syracuseStep 3788329 = 2841247) B2841247
theorem B1773167 : Blo 1772087 1773167 := bstep (se 1 (by rfl) ⟨1329875, by rfl⟩ : syracuseStep 1773167 = 2659751) B2659751
theorem B1994431 : Blo 1772087 1994431 := bstep (se 1 (by rfl) ⟨1495823, by rfl⟩ : syracuseStep 1994431 = 2991647) B2991647
theorem B1773287 : Blo 1772087 1773287 := bstep (se 1 (by rfl) ⟨1329965, by rfl⟩ : syracuseStep 1773287 = 2659931) B2659931
theorem B5984009 : Blo 1772087 5984009 := bstep (se 2 (by rfl) ⟨2244003, by rfl⟩ : syracuseStep 5984009 = 4488007) B4488007
theorem B5984063 : Blo 1772087 5984063 := bstep (se 1 (by rfl) ⟨4488047, by rfl⟩ : syracuseStep 5984063 = 8976095) B8976095
theorem B30289949 : Blo 1772087 30289949 := bstep (se 3 (by rfl) ⟨5679365, by rfl⟩ : syracuseStep 30289949 = 11358731) B11358731
theorem B27668603 : Blo 1772087 27668603 := bstep (se 1 (by rfl) ⟨20751452, by rfl⟩ : syracuseStep 27668603 = 41502905) B41502905
theorem B2273447 : Blo 1772087 2273447 := bstep (se 1 (by rfl) ⟨1705085, by rfl⟩ : syracuseStep 2273447 = 3410171) B3410171
theorem B1773791 : Blo 1772087 1773791 := bstep (se 1 (by rfl) ⟨1330343, by rfl⟩ : syracuseStep 1773791 = 2660687) B2660687
theorem B1773807 : Blo 1772087 1773807 := bstep (se 1 (by rfl) ⟨1330355, by rfl⟩ : syracuseStep 1773807 = 2660711) B2660711
theorem B1773851 : Blo 1772087 1773851 := bstep (se 1 (by rfl) ⟨1330388, by rfl⟩ : syracuseStep 1773851 = 2660777) B2660777
theorem B13652347 : Blo 1772087 13652347 := bstep (se 1 (by rfl) ⟨10239260, by rfl⟩ : syracuseStep 13652347 = 20478521) B20478521
theorem B6066683 : Blo 1772087 6066683 := bstep (se 1 (by rfl) ⟨4550012, by rfl⟩ : syracuseStep 6066683 = 9100025) B9100025
theorem B147509855 : Blo 1772087 147509855 := bstep (se 1 (by rfl) ⟨110632391, by rfl⟩ : syracuseStep 147509855 = 221264783) B221264783
theorem B8975123 : Blo 1772087 8975123 := bstep (se 1 (by rfl) ⟨6731342, by rfl⟩ : syracuseStep 8975123 = 13462685) B13462685
theorem B6730523 : Blo 1772087 6730523 := bstep (se 1 (by rfl) ⟨5047892, by rfl⟩ : syracuseStep 6730523 = 10095785) B10095785
theorem B17265581 : Blo 1772087 17265581 := bstep (se 3 (by rfl) ⟨3237296, by rfl⟩ : syracuseStep 17265581 = 6474593) B6474593
theorem B6730721 : Blo 1772087 6730721 := bstep (se 2 (by rfl) ⟨2524020, by rfl⟩ : syracuseStep 6730721 = 5048041) B5048041
theorem B6730735 : Blo 1772087 6730735 := bstep (se 1 (by rfl) ⟨5048051, by rfl⟩ : syracuseStep 6730735 = 10096103) B10096103
theorem B2659487 : Blo 1772087 2659487 := bstep (se 1 (by rfl) ⟨1994615, by rfl⟩ : syracuseStep 2659487 = 3989231) B3989231
theorem B6731039 : Blo 1772087 6731039 := bstep (se 1 (by rfl) ⟨5048279, by rfl⟩ : syracuseStep 6731039 = 10096559) B10096559
theorem B7189831 : Blo 1772087 7189831 := bstep (se 1 (by rfl) ⟨5392373, by rfl⟩ : syracuseStep 7189831 = 10784747) B10784747
theorem B3593683 : Blo 1772087 3593683 := bstep (se 1 (by rfl) ⟨2695262, by rfl⟩ : syracuseStep 3593683 = 5390525) B5390525
theorem B12776933 : Blo 1772087 12776933 := bstep (se 4 (by rfl) ⟨1197837, by rfl⟩ : syracuseStep 12776933 = 2395675) B2395675
theorem B5985791 : Blo 1772087 5985791 := bstep (se 1 (by rfl) ⟨4489343, by rfl⟩ : syracuseStep 5985791 = 8978687) B8978687
theorem B15152903 : Blo 1772087 15152903 := bstep (se 1 (by rfl) ⟨11364677, by rfl⟩ : syracuseStep 15152903 = 22729355) B22729355
theorem B2660105 : Blo 1772087 2660105 := bstep (se 2 (by rfl) ⟨997539, by rfl⟩ : syracuseStep 2660105 = 1995079) B1995079
theorem B7575889 : Blo 1772087 7575889 := bstep (se 2 (by rfl) ⟨2840958, by rfl⟩ : syracuseStep 7575889 = 5681917) B5681917
theorem B2660729 : Blo 1772087 2660729 := bstep (se 2 (by rfl) ⟨997773, by rfl⟩ : syracuseStep 2660729 = 1995547) B1995547
theorem B11360681 : Blo 1772087 11360681 := bstep (se 2 (by rfl) ⟨4260255, by rfl⟩ : syracuseStep 11360681 = 8520511) B8520511
theorem B3365459 : Blo 1772087 3365459 := bstep (se 1 (by rfl) ⟨2524094, by rfl⟩ : syracuseStep 3365459 = 5048189) B5048189
theorem B8977067 : Blo 1772087 8977067 := bstep (se 1 (by rfl) ⟨6732800, by rfl⟩ : syracuseStep 8977067 = 13465601) B13465601
theorem B3365641 : Blo 1772087 3365641 := bstep (se 2 (by rfl) ⟨1262115, by rfl⟩ : syracuseStep 3365641 = 2524231) B2524231
theorem B7576487 : Blo 1772087 7576487 := bstep (se 1 (by rfl) ⟨5682365, by rfl⟩ : syracuseStep 7576487 = 11364731) B11364731
theorem B86285351 : Blo 1772087 86285351 := bstep (se 1 (by rfl) ⟨64714013, by rfl⟩ : syracuseStep 86285351 = 129428027) B129428027
theorem B51125363 : Blo 1772087 51125363 := bstep (se 1 (by rfl) ⟨38344022, by rfl⟩ : syracuseStep 51125363 = 76688045) B76688045
theorem B9583913 : Blo 1772087 9583913 := bstep (se 2 (by rfl) ⟨3593967, by rfl⟩ : syracuseStep 9583913 = 7187935) B7187935
theorem B22724023 : Blo 1772087 22724023 := bstep (se 1 (by rfl) ⟨17043017, by rfl⟩ : syracuseStep 22724023 = 34086035) B34086035
theorem B14384719 : Blo 1772087 14384719 := bstep (se 1 (by rfl) ⟨10788539, by rfl⟩ : syracuseStep 14384719 = 21577079) B21577079
theorem B6733651 : Blo 1772087 6733651 := bstep (se 1 (by rfl) ⟨5050238, by rfl⟩ : syracuseStep 6733651 = 10100477) B10100477
theorem B20193299 : Blo 1772087 20193299 := bstep (se 1 (by rfl) ⟨15144974, by rfl⟩ : syracuseStep 20193299 = 30289949) B30289949
theorem B4489465 : Blo 1772087 4489465 := bstep (se 2 (by rfl) ⟨1683549, by rfl⟩ : syracuseStep 4489465 = 3367099) B3367099
theorem B4489627 : Blo 1772087 4489627 := bstep (se 1 (by rfl) ⟨3367220, by rfl⟩ : syracuseStep 4489627 = 6734441) B6734441
theorem B6062525 : Blo 1772087 6062525 := bstep (se 3 (by rfl) ⟨1136723, by rfl⟩ : syracuseStep 6062525 = 2273447) B2273447
theorem B10101185 : Blo 1772087 10101185 := bstep (se 2 (by rfl) ⟨3787944, by rfl⟩ : syracuseStep 10101185 = 7575889) B7575889
theorem B18203129 : Blo 1772087 18203129 := bstep (se 2 (by rfl) ⟨6826173, by rfl⟩ : syracuseStep 18203129 = 13652347) B13652347
theorem B11510387 : Blo 1772087 11510387 := bstep (se 1 (by rfl) ⟨8632790, by rfl⟩ : syracuseStep 11510387 = 17265581) B17265581
theorem B3367585 : Blo 1772087 3367585 := bstep (se 2 (by rfl) ⟨1262844, by rfl⟩ : syracuseStep 3367585 = 2525689) B2525689
theorem B4260833 : Blo 1772087 4260833 := bstep (se 2 (by rfl) ⟨1597812, by rfl⟩ : syracuseStep 4260833 = 3195625) B3195625
theorem B3990527 : Blo 1772087 3990527 := bstep (se 1 (by rfl) ⟨2992895, by rfl⟩ : syracuseStep 3990527 = 5985791) B5985791
theorem B5981255 : Blo 1772087 5981255 := bstep (se 1 (by rfl) ⟨4485941, by rfl⟩ : syracuseStep 5981255 = 8971883) B8971883
theorem B10101935 : Blo 1772087 10101935 := bstep (se 1 (by rfl) ⟨7576451, by rfl⟩ : syracuseStep 10101935 = 15152903) B15152903
theorem B8521031 : Blo 1772087 8521031 := bstep (se 1 (by rfl) ⟨6390773, by rfl⟩ : syracuseStep 8521031 = 12781547) B12781547
theorem B43115921 : Blo 1772087 43115921 := bstep (se 2 (by rfl) ⟨16168470, by rfl⟩ : syracuseStep 43115921 = 32336941) B32336941
theorem B3991265 : Blo 1772087 3991265 := bstep (se 2 (by rfl) ⟨1496724, by rfl⟩ : syracuseStep 3991265 = 2993449) B2993449
theorem B10094327 : Blo 1772087 10094327 := bstep (se 1 (by rfl) ⟨7570745, by rfl⟩ : syracuseStep 10094327 = 15141491) B15141491
theorem B9586441 : Blo 1772087 9586441 := bstep (se 2 (by rfl) ⟨3594915, by rfl⟩ : syracuseStep 9586441 = 7189831) B7189831
theorem B6735869 : Blo 1772087 6735869 := bstep (se 3 (by rfl) ⟨1262975, by rfl⟩ : syracuseStep 6735869 = 2525951) B2525951
theorem B4261985 : Blo 1772087 4261985 := bstep (se 2 (by rfl) ⟨1598244, by rfl⟩ : syracuseStep 4261985 = 3196489) B3196489
theorem B19179625 : Blo 1772087 19179625 := bstep (se 2 (by rfl) ⟨7192359, by rfl⟩ : syracuseStep 19179625 = 14384719) B14384719
theorem B8980793 : Blo 1772087 8980793 := bstep (se 2 (by rfl) ⟨3367797, by rfl⟩ : syracuseStep 8980793 = 6735595) B6735595
theorem B98339903 : Blo 1772087 98339903 := bstep (se 1 (by rfl) ⟨73754927, by rfl⟩ : syracuseStep 98339903 = 147509855) B147509855
theorem B6728777 : Blo 1772087 6728777 := bstep (se 2 (by rfl) ⟨2523291, by rfl⟩ : syracuseStep 6728777 = 5046583) B5046583
theorem B1993819 : Blo 1772087 1993819 := bstep (se 1 (by rfl) ⟨1495364, by rfl⟩ : syracuseStep 1993819 = 2990729) B2990729
theorem B5983415 : Blo 1772087 5983415 := bstep (se 1 (by rfl) ⟨4487561, by rfl⟩ : syracuseStep 5983415 = 8975123) B8975123
theorem B8973503 : Blo 1772087 8973503 := bstep (se 1 (by rfl) ⟨6730127, by rfl⟩ : syracuseStep 8973503 = 13460255) B13460255
theorem B1772991 : Blo 1772087 1772991 := bstep (se 1 (by rfl) ⟨1329743, by rfl⟩ : syracuseStep 1772991 = 2659487) B2659487
theorem B19164923 : Blo 1772087 19164923 := bstep (se 1 (by rfl) ⟨14373692, by rfl⟩ : syracuseStep 19164923 = 28747385) B28747385
theorem B1773403 : Blo 1772087 1773403 := bstep (se 1 (by rfl) ⟨1330052, by rfl⟩ : syracuseStep 1773403 = 2660105) B2660105
theorem B8974313 : Blo 1772087 8974313 := bstep (se 2 (by rfl) ⟨3365367, by rfl⟩ : syracuseStep 8974313 = 6730735) B6730735
theorem B1773819 : Blo 1772087 1773819 := bstep (se 1 (by rfl) ⟨1330364, by rfl⟩ : syracuseStep 1773819 = 2660729) B2660729
theorem B7573787 : Blo 1772087 7573787 := bstep (se 1 (by rfl) ⟨5680340, by rfl⟩ : syracuseStep 7573787 = 11360681) B11360681
theorem B5984711 : Blo 1772087 5984711 := bstep (se 1 (by rfl) ⟨4488533, by rfl⟩ : syracuseStep 5984711 = 8977067) B8977067
theorem B30298697 : Blo 1772087 30298697 := bstep (se 2 (by rfl) ⟨11362011, by rfl⟩ : syracuseStep 30298697 = 22724023) B22724023
theorem B5050991 : Blo 1772087 5050991 := bstep (se 1 (by rfl) ⟨3788243, by rfl⟩ : syracuseStep 5050991 = 7576487) B7576487
theorem B5051105 : Blo 1772087 5051105 := bstep (se 2 (by rfl) ⟨1894164, by rfl⟩ : syracuseStep 5051105 = 3788329) B3788329
theorem B34083575 : Blo 1772087 34083575 := bstep (se 1 (by rfl) ⟨25562681, by rfl⟩ : syracuseStep 34083575 = 51125363) B51125363
theorem B5681929 : Blo 1772087 5681929 := bstep (se 2 (by rfl) ⟨2130723, by rfl⟩ : syracuseStep 5681929 = 4261447) B4261447
theorem B2659241 : Blo 1772087 2659241 := bstep (se 2 (by rfl) ⟨997215, by rfl⟩ : syracuseStep 2659241 = 1994431) B1994431
theorem B18445735 : Blo 1772087 18445735 := bstep (se 1 (by rfl) ⟨13834301, by rfl⟩ : syracuseStep 18445735 = 27668603) B27668603
theorem B2659835 : Blo 1772087 2659835 := bstep (se 1 (by rfl) ⟨1994876, by rfl⟩ : syracuseStep 2659835 = 3989753) B3989753
theorem B2659943 : Blo 1772087 2659943 := bstep (se 1 (by rfl) ⟨1994957, by rfl⟩ : syracuseStep 2659943 = 3989915) B3989915
theorem B4044455 : Blo 1772087 4044455 := bstep (se 1 (by rfl) ⟨3033341, by rfl⟩ : syracuseStep 4044455 = 6066683) B6066683
theorem B4487015 : Blo 1772087 4487015 := bstep (se 1 (by rfl) ⟨3365261, by rfl⟩ : syracuseStep 4487015 = 6730523) B6730523
theorem B32798645 : Blo 1772087 32798645 := bstep (se 5 (by rfl) ⟨1537436, by rfl⟩ : syracuseStep 32798645 = 3074873) B3074873
theorem B4487147 : Blo 1772087 4487147 := bstep (se 1 (by rfl) ⟨3365360, by rfl⟩ : syracuseStep 4487147 = 6730721) B6730721
theorem B4487359 : Blo 1772087 4487359 := bstep (se 1 (by rfl) ⟨3365519, by rfl⟩ : syracuseStep 4487359 = 6731039) B6731039
theorem B20470009 : Blo 1772087 20470009 := bstep (se 2 (by rfl) ⟨7676253, by rfl⟩ : syracuseStep 20470009 = 15352507) B15352507
theorem B8517955 : Blo 1772087 8517955 := bstep (se 1 (by rfl) ⟨6388466, by rfl⟩ : syracuseStep 8517955 = 12776933) B12776933
theorem B3987791 : Blo 1772087 3987791 := bstep (se 1 (by rfl) ⟨2990843, by rfl⟩ : syracuseStep 3987791 = 5981687) B5981687
theorem B4487521 : Blo 1772087 4487521 := bstep (se 2 (by rfl) ⟨1682820, by rfl⟩ : syracuseStep 4487521 = 3365641) B3365641
theorem B3988079 : Blo 1772087 3988079 := bstep (se 1 (by rfl) ⟨2991059, by rfl⟩ : syracuseStep 3988079 = 5982119) B5982119
theorem B2661023 : Blo 1772087 2661023 := bstep (se 1 (by rfl) ⟨1995767, by rfl⟩ : syracuseStep 2661023 = 3991535) B3991535
theorem B3988511 : Blo 1772087 3988511 := bstep (se 1 (by rfl) ⟨2991383, by rfl⟩ : syracuseStep 3988511 = 5982767) B5982767
theorem B2243639 : Blo 1772087 2243639 := bstep (se 1 (by rfl) ⟨1682729, by rfl⟩ : syracuseStep 2243639 = 3365459) B3365459
theorem B5987411 : Blo 1772087 5987411 := bstep (se 1 (by rfl) ⟨4490558, by rfl⟩ : syracuseStep 5987411 = 8981117) B8981117
theorem B5987465 : Blo 1772087 5987465 := bstep (se 2 (by rfl) ⟨2245299, by rfl⟩ : syracuseStep 5987465 = 4490599) B4490599
theorem B3988655 : Blo 1772087 3988655 := bstep (se 1 (by rfl) ⟨2991491, by rfl⟩ : syracuseStep 3988655 = 5982983) B5982983
theorem B5987519 : Blo 1772087 5987519 := bstep (se 1 (by rfl) ⟨4490639, by rfl⟩ : syracuseStep 5987519 = 8981279) B8981279
theorem B4791577 : Blo 1772087 4791577 := bstep (se 2 (by rfl) ⟨1796841, by rfl⟩ : syracuseStep 4791577 = 3593683) B3593683
theorem B57523567 : Blo 1772087 57523567 := bstep (se 1 (by rfl) ⟨43142675, by rfl⟩ : syracuseStep 57523567 = 86285351) B86285351
theorem B3988961 : Blo 1772087 3988961 := bstep (se 2 (by rfl) ⟨1495860, by rfl⟩ : syracuseStep 3988961 = 2991721) B2991721
theorem B6389275 : Blo 1772087 6389275 := bstep (se 1 (by rfl) ⟨4791956, by rfl⟩ : syracuseStep 6389275 = 9583913) B9583913
theorem B8978201 : Blo 1772087 8978201 := bstep (se 2 (by rfl) ⟨3366825, by rfl⟩ : syracuseStep 8978201 = 6733651) B6733651
theorem B3989339 : Blo 1772087 3989339 := bstep (se 1 (by rfl) ⟨2992004, by rfl⟩ : syracuseStep 3989339 = 5984009) B5984009
theorem B3989375 : Blo 1772087 3989375 := bstep (se 1 (by rfl) ⟨2992031, by rfl⟩ : syracuseStep 3989375 = 5984063) B5984063
theorem B6734123 : Blo 1772087 6734123 := bstep (se 1 (by rfl) ⟨5050592, by rfl⟩ : syracuseStep 6734123 = 10101185) B10101185
theorem B3989807 : Blo 1772087 3989807 := bstep (se 1 (by rfl) ⟨2992355, by rfl⟩ : syracuseStep 3989807 = 5984711) B5984711
theorem B3367327 : Blo 1772087 3367327 := bstep (se 1 (by rfl) ⟨2525495, by rfl⟩ : syracuseStep 3367327 = 5050991) B5050991
theorem B3367403 : Blo 1772087 3367403 := bstep (se 1 (by rfl) ⟨2525552, by rfl⟩ : syracuseStep 3367403 = 5051105) B5051105
theorem B6734623 : Blo 1772087 6734623 := bstep (se 1 (by rfl) ⟨5050967, by rfl⟩ : syracuseStep 6734623 = 10101935) B10101935
theorem B4490113 : Blo 1772087 4490113 := bstep (se 2 (by rfl) ⟨1683792, by rfl⟩ : syracuseStep 4490113 = 3367585) B3367585
theorem B2696303 : Blo 1772087 2696303 := bstep (se 1 (by rfl) ⟨2022227, by rfl⟩ : syracuseStep 2696303 = 4044455) B4044455
theorem B2991343 : Blo 1772087 2991343 := bstep (se 1 (by rfl) ⟨2243507, by rfl⟩ : syracuseStep 2991343 = 4487015) B4487015
theorem B21865763 : Blo 1772087 21865763 := bstep (se 1 (by rfl) ⟨16399322, by rfl⟩ : syracuseStep 21865763 = 32798645) B32798645
theorem B2991431 : Blo 1772087 2991431 := bstep (se 1 (by rfl) ⟨2243573, by rfl⟩ : syracuseStep 2991431 = 4487147) B4487147
theorem B4490579 : Blo 1772087 4490579 := bstep (se 1 (by rfl) ⟨3367934, by rfl⟩ : syracuseStep 4490579 = 6735869) B6735869
theorem B3991607 : Blo 1772087 3991607 := bstep (se 1 (by rfl) ⟨2993705, by rfl⟩ : syracuseStep 3991607 = 5987411) B5987411
theorem B3991643 : Blo 1772087 3991643 := bstep (se 1 (by rfl) ⟨2993732, by rfl⟩ : syracuseStep 3991643 = 5987465) B5987465
theorem B5982335 : Blo 1772087 5982335 := bstep (se 1 (by rfl) ⟨4486751, by rfl⟩ : syracuseStep 5982335 = 8973503) B8973503
theorem B3991679 : Blo 1772087 3991679 := bstep (se 1 (by rfl) ⟨2993759, by rfl⟩ : syracuseStep 3991679 = 5987519) B5987519
theorem B12781921 : Blo 1772087 12781921 := bstep (se 2 (by rfl) ⟨4793220, by rfl⟩ : syracuseStep 12781921 = 9586441) B9586441
theorem B5982875 : Blo 1772087 5982875 := bstep (se 1 (by rfl) ⟨4487156, by rfl⟩ : syracuseStep 5982875 = 8974313) B8974313
theorem B13462199 : Blo 1772087 13462199 := bstep (se 1 (by rfl) ⟨10096649, by rfl⟩ : syracuseStep 13462199 = 20193299) B20193299
theorem B5983037 : Blo 1772087 5983037 := bstep (se 3 (by rfl) ⟨1121819, by rfl⟩ : syracuseStep 5983037 = 2243639) B2243639
theorem B5049191 : Blo 1772087 5049191 := bstep (se 1 (by rfl) ⟨3786893, by rfl⟩ : syracuseStep 5049191 = 7573787) B7573787
theorem B5983145 : Blo 1772087 5983145 := bstep (se 2 (by rfl) ⟨2243679, by rfl⟩ : syracuseStep 5983145 = 4487359) B4487359
theorem B4041683 : Blo 1772087 4041683 := bstep (se 1 (by rfl) ⟨3031262, by rfl⟩ : syracuseStep 4041683 = 6062525) B6062525
theorem B12135419 : Blo 1772087 12135419 := bstep (se 1 (by rfl) ⟨9101564, by rfl⟩ : syracuseStep 12135419 = 18203129) B18203129
theorem B11357273 : Blo 1772087 11357273 := bstep (se 2 (by rfl) ⟨4258977, by rfl⟩ : syracuseStep 11357273 = 8517955) B8517955
theorem B5983361 : Blo 1772087 5983361 := bstep (se 2 (by rfl) ⟨2243760, by rfl⟩ : syracuseStep 5983361 = 4487521) B4487521
theorem B1772827 : Blo 1772087 1772827 := bstep (se 1 (by rfl) ⟨1329620, by rfl⟩ : syracuseStep 1772827 = 2659241) B2659241
theorem B5680687 : Blo 1772087 5680687 := bstep (se 1 (by rfl) ⟨4260515, by rfl⟩ : syracuseStep 5680687 = 8521031) B8521031
theorem B1773223 : Blo 1772087 1773223 := bstep (se 1 (by rfl) ⟨1329917, by rfl⟩ : syracuseStep 1773223 = 2659835) B2659835
theorem B1773295 : Blo 1772087 1773295 := bstep (se 1 (by rfl) ⟨1329971, by rfl⟩ : syracuseStep 1773295 = 2659943) B2659943
theorem B6729551 : Blo 1772087 6729551 := bstep (se 1 (by rfl) ⟨5047163, by rfl⟩ : syracuseStep 6729551 = 10094327) B10094327
theorem B2658425 : Blo 1772087 2658425 := bstep (se 2 (by rfl) ⟨996909, by rfl⟩ : syracuseStep 2658425 = 1993819) B1993819
theorem B2658527 : Blo 1772087 2658527 := bstep (se 1 (by rfl) ⟨1993895, by rfl⟩ : syracuseStep 2658527 = 3987791) B3987791
theorem B2658719 : Blo 1772087 2658719 := bstep (se 1 (by rfl) ⟨1994039, by rfl⟩ : syracuseStep 2658719 = 3988079) B3988079
theorem B1774015 : Blo 1772087 1774015 := bstep (se 1 (by rfl) ⟨1330511, by rfl⟩ : syracuseStep 1774015 = 2661023) B2661023
theorem B76698089 : Blo 1772087 76698089 := bstep (se 2 (by rfl) ⟨28761783, by rfl⟩ : syracuseStep 76698089 = 57523567) B57523567
theorem B2659007 : Blo 1772087 2659007 := bstep (se 1 (by rfl) ⟨1994255, by rfl⟩ : syracuseStep 2659007 = 3988511) B3988511
theorem B4485851 : Blo 1772087 4485851 := bstep (se 1 (by rfl) ⟨3364388, by rfl⟩ : syracuseStep 4485851 = 6728777) B6728777
theorem B2659103 : Blo 1772087 2659103 := bstep (se 1 (by rfl) ⟨1994327, by rfl⟩ : syracuseStep 2659103 = 3988655) B3988655
theorem B2659307 : Blo 1772087 2659307 := bstep (se 1 (by rfl) ⟨1994480, by rfl⟩ : syracuseStep 2659307 = 3988961) B3988961
theorem B12776615 : Blo 1772087 12776615 := bstep (se 1 (by rfl) ⟨9582461, by rfl⟩ : syracuseStep 12776615 = 19164923) B19164923
theorem B5985467 : Blo 1772087 5985467 := bstep (se 1 (by rfl) ⟨4489100, by rfl⟩ : syracuseStep 5985467 = 8978201) B8978201
theorem B2659559 : Blo 1772087 2659559 := bstep (se 1 (by rfl) ⟨1994669, by rfl⟩ : syracuseStep 2659559 = 3989339) B3989339
theorem B2659583 : Blo 1772087 2659583 := bstep (se 1 (by rfl) ⟨1994687, by rfl⟩ : syracuseStep 2659583 = 3989375) B3989375
theorem B25572833 : Blo 1772087 25572833 := bstep (se 2 (by rfl) ⟨9589812, by rfl⟩ : syracuseStep 25572833 = 19179625) B19179625
theorem B27293345 : Blo 1772087 27293345 := bstep (se 2 (by rfl) ⟨10235004, by rfl⟩ : syracuseStep 27293345 = 20470009) B20470009
theorem B5985953 : Blo 1772087 5985953 := bstep (se 2 (by rfl) ⟨2244732, by rfl⟩ : syracuseStep 5985953 = 4489465) B4489465
theorem B20199131 : Blo 1772087 20199131 := bstep (se 1 (by rfl) ⟨15149348, by rfl⟩ : syracuseStep 20199131 = 30298697) B30298697
theorem B7673591 : Blo 1772087 7673591 := bstep (se 1 (by rfl) ⟨5755193, by rfl⟩ : syracuseStep 7673591 = 11510387) B11510387
theorem B22722383 : Blo 1772087 22722383 := bstep (se 1 (by rfl) ⟨17041787, by rfl⟩ : syracuseStep 22722383 = 34083575) B34083575
theorem B5986169 : Blo 1772087 5986169 := bstep (se 2 (by rfl) ⟨2244813, by rfl⟩ : syracuseStep 5986169 = 4489627) B4489627
theorem B2840555 : Blo 1772087 2840555 := bstep (se 1 (by rfl) ⟨2130416, by rfl⟩ : syracuseStep 2840555 = 4260833) B4260833
theorem B2660351 : Blo 1772087 2660351 := bstep (se 1 (by rfl) ⟨1995263, by rfl⟩ : syracuseStep 2660351 = 3990527) B3990527
theorem B3987503 : Blo 1772087 3987503 := bstep (se 1 (by rfl) ⟨2990627, by rfl⟩ : syracuseStep 3987503 = 5981255) B5981255
theorem B28743947 : Blo 1772087 28743947 := bstep (se 1 (by rfl) ⟨21557960, by rfl⟩ : syracuseStep 28743947 = 43115921) B43115921
theorem B7575905 : Blo 1772087 7575905 := bstep (se 2 (by rfl) ⟨2840964, by rfl⟩ : syracuseStep 7575905 = 5681929) B5681929
theorem B2660843 : Blo 1772087 2660843 := bstep (se 1 (by rfl) ⟨1995632, by rfl⟩ : syracuseStep 2660843 = 3991265) B3991265
theorem B2841323 : Blo 1772087 2841323 := bstep (se 1 (by rfl) ⟨2130992, by rfl⟩ : syracuseStep 2841323 = 4261985) B4261985
theorem B5987195 : Blo 1772087 5987195 := bstep (se 1 (by rfl) ⟨4490396, by rfl⟩ : syracuseStep 5987195 = 8980793) B8980793
theorem B6388769 : Blo 1772087 6388769 := bstep (se 2 (by rfl) ⟨2395788, by rfl⟩ : syracuseStep 6388769 = 4791577) B4791577
theorem B8519033 : Blo 1772087 8519033 := bstep (se 2 (by rfl) ⟨3194637, by rfl⟩ : syracuseStep 8519033 = 6389275) B6389275
theorem B65559935 : Blo 1772087 65559935 := bstep (se 1 (by rfl) ⟨49169951, by rfl⟩ : syracuseStep 65559935 = 98339903) B98339903
theorem B3988943 : Blo 1772087 3988943 := bstep (se 1 (by rfl) ⟨2991707, by rfl⟩ : syracuseStep 3988943 = 5983415) B5983415
theorem B98377253 : Blo 1772087 98377253 := bstep (se 4 (by rfl) ⟨9222867, by rfl⟩ : syracuseStep 98377253 = 18445735) B18445735
theorem B4489415 : Blo 1772087 4489415 := bstep (se 1 (by rfl) ⟨3367061, by rfl⟩ : syracuseStep 4489415 = 6734123) B6734123
theorem B2244935 : Blo 1772087 2244935 := bstep (se 1 (by rfl) ⟨1683701, by rfl⟩ : syracuseStep 2244935 = 3367403) B3367403
theorem B2990567 : Blo 1772087 2990567 := bstep (se 1 (by rfl) ⟨2242925, by rfl⟩ : syracuseStep 2990567 = 4485851) B4485851
theorem B4489769 : Blo 1772087 4489769 := bstep (se 2 (by rfl) ⟨1683663, by rfl⟩ : syracuseStep 4489769 = 3367327) B3367327
theorem B3990311 : Blo 1772087 3990311 := bstep (se 1 (by rfl) ⟨2992733, by rfl⟩ : syracuseStep 3990311 = 5985467) B5985467
theorem B17048555 : Blo 1772087 17048555 := bstep (se 1 (by rfl) ⟨12786416, by rfl⟩ : syracuseStep 17048555 = 25572833) B25572833
theorem B8979497 : Blo 1772087 8979497 := bstep (se 2 (by rfl) ⟨3367311, by rfl⟩ : syracuseStep 8979497 = 6734623) B6734623
theorem B18195563 : Blo 1772087 18195563 := bstep (se 1 (by rfl) ⟨13646672, by rfl⟩ : syracuseStep 18195563 = 27293345) B27293345
theorem B3990635 : Blo 1772087 3990635 := bstep (se 1 (by rfl) ⟨2992976, by rfl⟩ : syracuseStep 3990635 = 5985953) B5985953
theorem B15148255 : Blo 1772087 15148255 := bstep (se 1 (by rfl) ⟨11361191, by rfl⟩ : syracuseStep 15148255 = 22722383) B22722383
theorem B3990779 : Blo 1772087 3990779 := bstep (se 1 (by rfl) ⟨2993084, by rfl⟩ : syracuseStep 3990779 = 5986169) B5986169
theorem B1893703 : Blo 1772087 1893703 := bstep (se 1 (by rfl) ⟨1420277, by rfl⟩ : syracuseStep 1893703 = 2840555) B2840555
theorem B19162631 : Blo 1772087 19162631 := bstep (se 1 (by rfl) ⟨14371973, by rfl⟩ : syracuseStep 19162631 = 28743947) B28743947
theorem B3991463 : Blo 1772087 3991463 := bstep (se 1 (by rfl) ⟨2993597, by rfl⟩ : syracuseStep 3991463 = 5987195) B5987195
theorem B7571515 : Blo 1772087 7571515 := bstep (se 1 (by rfl) ⟨5678636, by rfl⟩ : syracuseStep 7571515 = 11357273) B11357273
theorem B5679355 : Blo 1772087 5679355 := bstep (se 1 (by rfl) ⟨4259516, by rfl⟩ : syracuseStep 5679355 = 8519033) B8519033
theorem B43706623 : Blo 1772087 43706623 := bstep (se 1 (by rfl) ⟨32779967, by rfl⟩ : syracuseStep 43706623 = 65559935) B65559935
theorem B1772283 : Blo 1772087 1772283 := bstep (se 1 (by rfl) ⟨1329212, by rfl⟩ : syracuseStep 1772283 = 2658425) B2658425
theorem B1772351 : Blo 1772087 1772351 := bstep (se 1 (by rfl) ⟨1329263, by rfl⟩ : syracuseStep 1772351 = 2658527) B2658527
theorem B1772479 : Blo 1772087 1772479 := bstep (se 1 (by rfl) ⟨1329359, by rfl⟩ : syracuseStep 1772479 = 2658719) B2658719
theorem B1772671 : Blo 1772087 1772671 := bstep (se 1 (by rfl) ⟨1329503, by rfl⟩ : syracuseStep 1772671 = 2659007) B2659007
theorem B17042561 : Blo 1772087 17042561 := bstep (se 2 (by rfl) ⟨6390960, by rfl⟩ : syracuseStep 17042561 = 12781921) B12781921
theorem B1772735 : Blo 1772087 1772735 := bstep (se 1 (by rfl) ⟨1329551, by rfl⟩ : syracuseStep 1772735 = 2659103) B2659103
theorem B1772871 : Blo 1772087 1772871 := bstep (se 1 (by rfl) ⟨1329653, by rfl⟩ : syracuseStep 1772871 = 2659307) B2659307
theorem B1797535 : Blo 1772087 1797535 := bstep (se 1 (by rfl) ⟨1348151, by rfl⟩ : syracuseStep 1797535 = 2696303) B2696303
theorem B1773039 : Blo 1772087 1773039 := bstep (se 1 (by rfl) ⟨1329779, by rfl⟩ : syracuseStep 1773039 = 2659559) B2659559
theorem B1773055 : Blo 1772087 1773055 := bstep (se 1 (by rfl) ⟨1329791, by rfl⟩ : syracuseStep 1773055 = 2659583) B2659583
theorem B14577175 : Blo 1772087 14577175 := bstep (se 1 (by rfl) ⟨10932881, by rfl⟩ : syracuseStep 14577175 = 21865763) B21865763
theorem B1994287 : Blo 1772087 1994287 := bstep (se 1 (by rfl) ⟨1495715, by rfl⟩ : syracuseStep 1994287 = 2991431) B2991431
theorem B2993719 : Blo 1772087 2993719 := bstep (se 1 (by rfl) ⟨2245289, by rfl⟩ : syracuseStep 2993719 = 4490579) B4490579
theorem B5115727 : Blo 1772087 5115727 := bstep (se 1 (by rfl) ⟨3836795, by rfl⟩ : syracuseStep 5115727 = 7673591) B7673591
theorem B1773567 : Blo 1772087 1773567 := bstep (se 1 (by rfl) ⟨1330175, by rfl⟩ : syracuseStep 1773567 = 2660351) B2660351
theorem B2658335 : Blo 1772087 2658335 := bstep (se 1 (by rfl) ⟨1993751, by rfl⟩ : syracuseStep 2658335 = 3987503) B3987503
theorem B5050603 : Blo 1772087 5050603 := bstep (se 1 (by rfl) ⟨3787952, by rfl⟩ : syracuseStep 5050603 = 7575905) B7575905
theorem B1773895 : Blo 1772087 1773895 := bstep (se 1 (by rfl) ⟨1330421, by rfl⟩ : syracuseStep 1773895 = 2660843) B2660843
theorem B8974799 : Blo 1772087 8974799 := bstep (se 1 (by rfl) ⟨6731099, by rfl⟩ : syracuseStep 8974799 = 13462199) B13462199
theorem B8090279 : Blo 1772087 8090279 := bstep (se 1 (by rfl) ⟨6067709, by rfl⟩ : syracuseStep 8090279 = 12135419) B12135419
theorem B7574249 : Blo 1772087 7574249 := bstep (se 2 (by rfl) ⟨2840343, by rfl⟩ : syracuseStep 7574249 = 5680687) B5680687
theorem B2659295 : Blo 1772087 2659295 := bstep (se 1 (by rfl) ⟨1994471, by rfl⟩ : syracuseStep 2659295 = 3988943) B3988943
theorem B30307445 : Blo 1772087 30307445 := bstep (se 5 (by rfl) ⟨1420661, by rfl⟩ : syracuseStep 30307445 = 2841323) B2841323
theorem B4486367 : Blo 1772087 4486367 := bstep (se 1 (by rfl) ⟨3364775, by rfl⟩ : syracuseStep 4486367 = 6729551) B6729551
theorem B2659871 : Blo 1772087 2659871 := bstep (se 1 (by rfl) ⟨1994903, by rfl⟩ : syracuseStep 2659871 = 3989807) B3989807
theorem B51132059 : Blo 1772087 51132059 := bstep (se 1 (by rfl) ⟨38349044, by rfl⟩ : syracuseStep 51132059 = 76698089) B76698089
theorem B8517743 : Blo 1772087 8517743 := bstep (se 1 (by rfl) ⟨6388307, by rfl⟩ : syracuseStep 8517743 = 12776615) B12776615
theorem B13466087 : Blo 1772087 13466087 := bstep (se 1 (by rfl) ⟨10099565, by rfl⟩ : syracuseStep 13466087 = 20199131) B20199131
theorem B5986817 : Blo 1772087 5986817 := bstep (se 2 (by rfl) ⟨2245056, by rfl⟩ : syracuseStep 5986817 = 4490113) B4490113
theorem B2661071 : Blo 1772087 2661071 := bstep (se 1 (by rfl) ⟨1995803, by rfl⟩ : syracuseStep 2661071 = 3991607) B3991607
theorem B2661095 : Blo 1772087 2661095 := bstep (se 1 (by rfl) ⟨1995821, by rfl⟩ : syracuseStep 2661095 = 3991643) B3991643
theorem B3988223 : Blo 1772087 3988223 := bstep (se 1 (by rfl) ⟨2991167, by rfl⟩ : syracuseStep 3988223 = 5982335) B5982335
theorem B2661119 : Blo 1772087 2661119 := bstep (se 1 (by rfl) ⟨1995839, by rfl⟩ : syracuseStep 2661119 = 3991679) B3991679
theorem B3988457 : Blo 1772087 3988457 := bstep (se 2 (by rfl) ⟨1495671, by rfl⟩ : syracuseStep 3988457 = 2991343) B2991343
theorem B3988583 : Blo 1772087 3988583 := bstep (se 1 (by rfl) ⟨2991437, by rfl⟩ : syracuseStep 3988583 = 5982875) B5982875
theorem B3988691 : Blo 1772087 3988691 := bstep (se 1 (by rfl) ⟨2991518, by rfl⟩ : syracuseStep 3988691 = 5983037) B5983037
theorem B3366127 : Blo 1772087 3366127 := bstep (se 1 (by rfl) ⟨2524595, by rfl⟩ : syracuseStep 3366127 = 5049191) B5049191
theorem B3988763 : Blo 1772087 3988763 := bstep (se 1 (by rfl) ⟨2991572, by rfl⟩ : syracuseStep 3988763 = 5983145) B5983145
theorem B2694455 : Blo 1772087 2694455 := bstep (se 1 (by rfl) ⟨2020841, by rfl⟩ : syracuseStep 2694455 = 4041683) B4041683
theorem B4259179 : Blo 1772087 4259179 := bstep (se 1 (by rfl) ⟨3194384, by rfl⟩ : syracuseStep 4259179 = 6388769) B6388769
theorem B3988907 : Blo 1772087 3988907 := bstep (se 1 (by rfl) ⟨2991680, by rfl⟩ : syracuseStep 3988907 = 5983361) B5983361
theorem B65584835 : Blo 1772087 65584835 := bstep (se 1 (by rfl) ⟨49188626, by rfl⟩ : syracuseStep 65584835 = 98377253) B98377253
theorem B48521501 : Blo 1772087 48521501 := bstep (se 3 (by rfl) ⟨9097781, by rfl⟩ : syracuseStep 48521501 = 18195563) B18195563
theorem B6734137 : Blo 1772087 6734137 := bstep (se 2 (by rfl) ⟨2525301, by rfl⟩ : syracuseStep 6734137 = 5050603) B5050603
theorem B2990911 : Blo 1772087 2990911 := bstep (se 1 (by rfl) ⟨2243183, by rfl⟩ : syracuseStep 2990911 = 4486367) B4486367
theorem B34088039 : Blo 1772087 34088039 := bstep (se 1 (by rfl) ⟨25566029, by rfl⟩ : syracuseStep 34088039 = 51132059) B51132059
theorem B5678495 : Blo 1772087 5678495 := bstep (se 1 (by rfl) ⟨4258871, by rfl⟩ : syracuseStep 5678495 = 8517743) B8517743
theorem B3991211 : Blo 1772087 3991211 := bstep (se 1 (by rfl) ⟨2993408, by rfl⟩ : syracuseStep 3991211 = 5986817) B5986817
theorem B2524937 : Blo 1772087 2524937 := bstep (se 2 (by rfl) ⟨946851, by rfl⟩ : syracuseStep 2524937 = 1893703) B1893703
theorem B5678905 : Blo 1772087 5678905 := bstep (se 2 (by rfl) ⟨2129589, by rfl⟩ : syracuseStep 5678905 = 4259179) B4259179
theorem B3991625 : Blo 1772087 3991625 := bstep (se 2 (by rfl) ⟨1496859, by rfl⟩ : syracuseStep 3991625 = 2993719) B2993719
theorem B1796303 : Blo 1772087 1796303 := bstep (se 1 (by rfl) ⟨1347227, by rfl⟩ : syracuseStep 1796303 = 2694455) B2694455
theorem B43723223 : Blo 1772087 43723223 := bstep (se 1 (by rfl) ⟨32792417, by rfl⟩ : syracuseStep 43723223 = 65584835) B65584835
theorem B1772223 : Blo 1772087 1772223 := bstep (se 1 (by rfl) ⟨1329167, by rfl⟩ : syracuseStep 1772223 = 2658335) B2658335
theorem B10095353 : Blo 1772087 10095353 := bstep (se 2 (by rfl) ⟨3785757, by rfl⟩ : syracuseStep 10095353 = 7571515) B7571515
theorem B77744933 : Blo 1772087 77744933 := bstep (se 4 (by rfl) ⟨7288587, by rfl⟩ : syracuseStep 77744933 = 14577175) B14577175
theorem B2992943 : Blo 1772087 2992943 := bstep (se 1 (by rfl) ⟨2244707, by rfl⟩ : syracuseStep 2992943 = 4489415) B4489415
theorem B5983199 : Blo 1772087 5983199 := bstep (se 1 (by rfl) ⟨4487399, by rfl⟩ : syracuseStep 5983199 = 8974799) B8974799
theorem B1993711 : Blo 1772087 1993711 := bstep (se 1 (by rfl) ⟨1495283, by rfl⟩ : syracuseStep 1993711 = 2990567) B2990567
theorem B7572473 : Blo 1772087 7572473 := bstep (se 2 (by rfl) ⟨2839677, by rfl⟩ : syracuseStep 7572473 = 5679355) B5679355
theorem B2993179 : Blo 1772087 2993179 := bstep (se 1 (by rfl) ⟨2244884, by rfl⟩ : syracuseStep 2993179 = 4489769) B4489769
theorem B5393519 : Blo 1772087 5393519 := bstep (se 1 (by rfl) ⟨4045139, by rfl⟩ : syracuseStep 5393519 = 8090279) B8090279
theorem B5049499 : Blo 1772087 5049499 := bstep (se 1 (by rfl) ⟨3787124, by rfl⟩ : syracuseStep 5049499 = 7574249) B7574249
theorem B1772863 : Blo 1772087 1772863 := bstep (se 1 (by rfl) ⟨1329647, by rfl⟩ : syracuseStep 1772863 = 2659295) B2659295
theorem B11365703 : Blo 1772087 11365703 := bstep (se 1 (by rfl) ⟨8524277, by rfl⟩ : syracuseStep 11365703 = 17048555) B17048555
theorem B20204963 : Blo 1772087 20204963 := bstep (se 1 (by rfl) ⟨15153722, by rfl⟩ : syracuseStep 20204963 = 30307445) B30307445
theorem B12775087 : Blo 1772087 12775087 := bstep (se 1 (by rfl) ⟨9581315, by rfl⟩ : syracuseStep 12775087 = 19162631) B19162631
theorem B1773247 : Blo 1772087 1773247 := bstep (se 1 (by rfl) ⟨1329935, by rfl⟩ : syracuseStep 1773247 = 2659871) B2659871
theorem B20197673 : Blo 1772087 20197673 := bstep (se 2 (by rfl) ⟨7574127, by rfl⟩ : syracuseStep 20197673 = 15148255) B15148255
theorem B1774047 : Blo 1772087 1774047 := bstep (se 1 (by rfl) ⟨1330535, by rfl⟩ : syracuseStep 1774047 = 2661071) B2661071
theorem B1774063 : Blo 1772087 1774063 := bstep (se 1 (by rfl) ⟨1330547, by rfl⟩ : syracuseStep 1774063 = 2661095) B2661095
theorem B2658815 : Blo 1772087 2658815 := bstep (se 1 (by rfl) ⟨1994111, by rfl⟩ : syracuseStep 2658815 = 3988223) B3988223
theorem B1774079 : Blo 1772087 1774079 := bstep (se 1 (by rfl) ⟨1330559, by rfl⟩ : syracuseStep 1774079 = 2661119) B2661119
theorem B2396713 : Blo 1772087 2396713 := bstep (se 2 (by rfl) ⟨898767, by rfl⟩ : syracuseStep 2396713 = 1797535) B1797535
theorem B2658971 : Blo 1772087 2658971 := bstep (se 1 (by rfl) ⟨1994228, by rfl⟩ : syracuseStep 2658971 = 3988457) B3988457
theorem B2659049 : Blo 1772087 2659049 := bstep (se 2 (by rfl) ⟨997143, by rfl⟩ : syracuseStep 2659049 = 1994287) B1994287
theorem B2659055 : Blo 1772087 2659055 := bstep (se 1 (by rfl) ⟨1994291, by rfl⟩ : syracuseStep 2659055 = 3988583) B3988583
theorem B2659127 : Blo 1772087 2659127 := bstep (se 1 (by rfl) ⟨1994345, by rfl⟩ : syracuseStep 2659127 = 3988691) B3988691
theorem B2659175 : Blo 1772087 2659175 := bstep (se 1 (by rfl) ⟨1994381, by rfl⟩ : syracuseStep 2659175 = 3988763) B3988763
theorem B2659271 : Blo 1772087 2659271 := bstep (se 1 (by rfl) ⟨1994453, by rfl⟩ : syracuseStep 2659271 = 3988907) B3988907
theorem B6820969 : Blo 1772087 6820969 := bstep (se 2 (by rfl) ⟨2557863, by rfl⟩ : syracuseStep 6820969 = 5115727) B5115727
theorem B58275497 : Blo 1772087 58275497 := bstep (se 2 (by rfl) ⟨21853311, by rfl⟩ : syracuseStep 58275497 = 43706623) B43706623
theorem B2660207 : Blo 1772087 2660207 := bstep (se 1 (by rfl) ⟨1995155, by rfl⟩ : syracuseStep 2660207 = 3990311) B3990311
theorem B5986331 : Blo 1772087 5986331 := bstep (se 1 (by rfl) ⟨4489748, by rfl⟩ : syracuseStep 5986331 = 8979497) B8979497
theorem B2660423 : Blo 1772087 2660423 := bstep (se 1 (by rfl) ⟨1995317, by rfl⟩ : syracuseStep 2660423 = 3990635) B3990635
theorem B2660519 : Blo 1772087 2660519 := bstep (se 1 (by rfl) ⟨1995389, by rfl⟩ : syracuseStep 2660519 = 3990779) B3990779
theorem B5986493 : Blo 1772087 5986493 := bstep (se 3 (by rfl) ⟨1122467, by rfl⟩ : syracuseStep 5986493 = 2244935) B2244935
theorem B2660975 : Blo 1772087 2660975 := bstep (se 1 (by rfl) ⟨1995731, by rfl⟩ : syracuseStep 2660975 = 3991463) B3991463
theorem B4488169 : Blo 1772087 4488169 := bstep (se 2 (by rfl) ⟨1683063, by rfl⟩ : syracuseStep 4488169 = 3366127) B3366127
theorem B8977391 : Blo 1772087 8977391 := bstep (se 1 (by rfl) ⟨6733043, by rfl⟩ : syracuseStep 8977391 = 13466087) B13466087
theorem B11361707 : Blo 1772087 11361707 := bstep (se 1 (by rfl) ⟨8521280, by rfl⟩ : syracuseStep 11361707 = 17042561) B17042561
theorem B8978849 : Blo 1772087 8978849 := bstep (se 2 (by rfl) ⟨3367068, by rfl⟩ : syracuseStep 8978849 = 6734137) B6734137
theorem B3195617 : Blo 1772087 3195617 := bstep (se 2 (by rfl) ⟨1198356, by rfl⟩ : syracuseStep 3195617 = 2396713) B2396713
theorem B22725359 : Blo 1772087 22725359 := bstep (se 1 (by rfl) ⟨17044019, by rfl⟩ : syracuseStep 22725359 = 34088039) B34088039
theorem B3785663 : Blo 1772087 3785663 := bstep (se 1 (by rfl) ⟨2839247, by rfl⟩ : syracuseStep 3785663 = 5678495) B5678495
theorem B3990887 : Blo 1772087 3990887 := bstep (se 1 (by rfl) ⟨2993165, by rfl⟩ : syracuseStep 3990887 = 5986331) B5986331
theorem B3990905 : Blo 1772087 3990905 := bstep (se 2 (by rfl) ⟨1496589, by rfl⟩ : syracuseStep 3990905 = 2993179) B2993179
theorem B3990995 : Blo 1772087 3990995 := bstep (se 1 (by rfl) ⟨2993246, by rfl⟩ : syracuseStep 3990995 = 5986493) B5986493
theorem B9094625 : Blo 1772087 9094625 := bstep (se 2 (by rfl) ⟨3410484, by rfl⟩ : syracuseStep 9094625 = 6820969) B6820969
theorem B29148815 : Blo 1772087 29148815 := bstep (se 1 (by rfl) ⟨21861611, by rfl⟩ : syracuseStep 29148815 = 43723223) B43723223
theorem B5048315 : Blo 1772087 5048315 := bstep (se 1 (by rfl) ⟨3786236, by rfl⟩ : syracuseStep 5048315 = 7572473) B7572473
theorem B17033449 : Blo 1772087 17033449 := bstep (se 2 (by rfl) ⟨6387543, by rfl⟩ : syracuseStep 17033449 = 12775087) B12775087
theorem B13469975 : Blo 1772087 13469975 := bstep (se 1 (by rfl) ⟨10102481, by rfl⟩ : syracuseStep 13469975 = 20204963) B20204963
theorem B7571873 : Blo 1772087 7571873 := bstep (se 2 (by rfl) ⟨2839452, by rfl⟩ : syracuseStep 7571873 = 5678905) B5678905
theorem B1772543 : Blo 1772087 1772543 := bstep (se 1 (by rfl) ⟨1329407, by rfl⟩ : syracuseStep 1772543 = 2658815) B2658815
theorem B1772647 : Blo 1772087 1772647 := bstep (se 1 (by rfl) ⟨1329485, by rfl⟩ : syracuseStep 1772647 = 2658971) B2658971
theorem B1772699 : Blo 1772087 1772699 := bstep (se 1 (by rfl) ⟨1329524, by rfl⟩ : syracuseStep 1772699 = 2659049) B2659049
theorem B1772703 : Blo 1772087 1772703 := bstep (se 1 (by rfl) ⟨1329527, by rfl⟩ : syracuseStep 1772703 = 2659055) B2659055
theorem B1772751 : Blo 1772087 1772751 := bstep (se 1 (by rfl) ⟨1329563, by rfl⟩ : syracuseStep 1772751 = 2659127) B2659127
theorem B1772783 : Blo 1772087 1772783 := bstep (se 1 (by rfl) ⟨1329587, by rfl⟩ : syracuseStep 1772783 = 2659175) B2659175
theorem B1772847 : Blo 1772087 1772847 := bstep (se 1 (by rfl) ⟨1329635, by rfl⟩ : syracuseStep 1772847 = 2659271) B2659271
theorem B1773471 : Blo 1772087 1773471 := bstep (se 1 (by rfl) ⟨1330103, by rfl⟩ : syracuseStep 1773471 = 2660207) B2660207
theorem B5984225 : Blo 1772087 5984225 := bstep (se 2 (by rfl) ⟨2244084, by rfl⟩ : syracuseStep 5984225 = 4488169) B4488169
theorem B2658281 : Blo 1772087 2658281 := bstep (se 2 (by rfl) ⟨996855, by rfl⟩ : syracuseStep 2658281 = 1993711) B1993711
theorem B1773615 : Blo 1772087 1773615 := bstep (se 1 (by rfl) ⟨1330211, by rfl⟩ : syracuseStep 1773615 = 2660423) B2660423
theorem B1773679 : Blo 1772087 1773679 := bstep (se 1 (by rfl) ⟨1330259, by rfl⟩ : syracuseStep 1773679 = 2660519) B2660519
theorem B1773983 : Blo 1772087 1773983 := bstep (se 1 (by rfl) ⟨1330487, by rfl⟩ : syracuseStep 1773983 = 2660975) B2660975
theorem B6730235 : Blo 1772087 6730235 := bstep (se 1 (by rfl) ⟨5047676, by rfl⟩ : syracuseStep 6730235 = 10095353) B10095353
theorem B1995295 : Blo 1772087 1995295 := bstep (se 1 (by rfl) ⟨1496471, by rfl⟩ : syracuseStep 1995295 = 2992943) B2992943
theorem B5984927 : Blo 1772087 5984927 := bstep (se 1 (by rfl) ⟨4488695, by rfl⟩ : syracuseStep 5984927 = 8977391) B8977391
theorem B7574471 : Blo 1772087 7574471 := bstep (se 1 (by rfl) ⟨5680853, by rfl⟩ : syracuseStep 7574471 = 11361707) B11361707
theorem B32347667 : Blo 1772087 32347667 := bstep (se 1 (by rfl) ⟨24260750, by rfl⟩ : syracuseStep 32347667 = 48521501) B48521501
theorem B13465115 : Blo 1772087 13465115 := bstep (se 1 (by rfl) ⟨10098836, by rfl⟩ : syracuseStep 13465115 = 20197673) B20197673
theorem B4790141 : Blo 1772087 4790141 := bstep (se 3 (by rfl) ⟨898151, by rfl⟩ : syracuseStep 4790141 = 1796303) B1796303
theorem B3987881 : Blo 1772087 3987881 := bstep (se 2 (by rfl) ⟨1495455, by rfl⟩ : syracuseStep 3987881 = 2990911) B2990911
theorem B2660807 : Blo 1772087 2660807 := bstep (se 1 (by rfl) ⟨1995605, by rfl⟩ : syracuseStep 2660807 = 3991211) B3991211
theorem B2661083 : Blo 1772087 2661083 := bstep (se 1 (by rfl) ⟨1995812, by rfl⟩ : syracuseStep 2661083 = 3991625) B3991625
theorem B6732665 : Blo 1772087 6732665 := bstep (se 2 (by rfl) ⟨2524749, by rfl⟩ : syracuseStep 6732665 = 5049499) B5049499
theorem B155401325 : Blo 1772087 155401325 := bstep (se 3 (by rfl) ⟨29137748, by rfl⟩ : syracuseStep 155401325 = 58275497) B58275497
theorem B51829955 : Blo 1772087 51829955 := bstep (se 1 (by rfl) ⟨38872466, by rfl⟩ : syracuseStep 51829955 = 77744933) B77744933
theorem B3988799 : Blo 1772087 3988799 := bstep (se 1 (by rfl) ⟨2991599, by rfl⟩ : syracuseStep 3988799 = 5983199) B5983199
theorem B6733165 : Blo 1772087 6733165 := bstep (se 3 (by rfl) ⟨1262468, by rfl⟩ : syracuseStep 6733165 = 2524937) B2524937
theorem B3595679 : Blo 1772087 3595679 := bstep (se 1 (by rfl) ⟨2696759, by rfl⟩ : syracuseStep 3595679 = 5393519) B5393519
theorem B7577135 : Blo 1772087 7577135 := bstep (se 1 (by rfl) ⟨5682851, by rfl⟩ : syracuseStep 7577135 = 11365703) B11365703
theorem B3989951 : Blo 1772087 3989951 := bstep (se 1 (by rfl) ⟨2992463, by rfl⟩ : syracuseStep 3989951 = 5984927) B5984927
theorem B6063083 : Blo 1772087 6063083 := bstep (se 1 (by rfl) ⟨4547312, by rfl⟩ : syracuseStep 6063083 = 9094625) B9094625
theorem B19432543 : Blo 1772087 19432543 := bstep (se 1 (by rfl) ⟨14574407, by rfl⟩ : syracuseStep 19432543 = 29148815) B29148815
theorem B8979983 : Blo 1772087 8979983 := bstep (se 1 (by rfl) ⟨6734987, by rfl⟩ : syracuseStep 8979983 = 13469975) B13469975
theorem B5047915 : Blo 1772087 5047915 := bstep (se 1 (by rfl) ⟨3785936, by rfl⟩ : syracuseStep 5047915 = 7571873) B7571873
theorem B10095101 : Blo 1772087 10095101 := bstep (se 3 (by rfl) ⟨1892831, by rfl⟩ : syracuseStep 10095101 = 3785663) B3785663
theorem B1772187 : Blo 1772087 1772187 := bstep (se 1 (by rfl) ⟨1329140, by rfl⟩ : syracuseStep 1772187 = 2658281) B2658281
theorem B22711265 : Blo 1772087 22711265 := bstep (se 2 (by rfl) ⟨8516724, by rfl⟩ : syracuseStep 22711265 = 17033449) B17033449
theorem B15150239 : Blo 1772087 15150239 := bstep (se 1 (by rfl) ⟨11362679, by rfl⟩ : syracuseStep 15150239 = 22725359) B22725359
theorem B5049647 : Blo 1772087 5049647 := bstep (se 1 (by rfl) ⟨3787235, by rfl⟩ : syracuseStep 5049647 = 7574471) B7574471
theorem B21565111 : Blo 1772087 21565111 := bstep (se 1 (by rfl) ⟨16173833, by rfl⟩ : syracuseStep 21565111 = 32347667) B32347667
theorem B2658587 : Blo 1772087 2658587 := bstep (se 1 (by rfl) ⟨1993940, by rfl⟩ : syracuseStep 2658587 = 3987881) B3987881
theorem B1773871 : Blo 1772087 1773871 := bstep (se 1 (by rfl) ⟨1330403, by rfl⟩ : syracuseStep 1773871 = 2660807) B2660807
theorem B1774055 : Blo 1772087 1774055 := bstep (se 1 (by rfl) ⟨1330541, by rfl⟩ : syracuseStep 1774055 = 2661083) B2661083
theorem B103600883 : Blo 1772087 103600883 := bstep (se 1 (by rfl) ⟨77700662, by rfl⟩ : syracuseStep 103600883 = 155401325) B155401325
theorem B2659199 : Blo 1772087 2659199 := bstep (se 1 (by rfl) ⟨1994399, by rfl⟩ : syracuseStep 2659199 = 3988799) B3988799
theorem B2397119 : Blo 1772087 2397119 := bstep (se 1 (by rfl) ⟨1797839, by rfl⟩ : syracuseStep 2397119 = 3595679) B3595679
theorem B5051423 : Blo 1772087 5051423 := bstep (se 1 (by rfl) ⟨3788567, by rfl⟩ : syracuseStep 5051423 = 7577135) B7577135
theorem B5985899 : Blo 1772087 5985899 := bstep (se 1 (by rfl) ⟨4489424, by rfl⟩ : syracuseStep 5985899 = 8978849) B8978849
theorem B4486823 : Blo 1772087 4486823 := bstep (se 1 (by rfl) ⟨3365117, by rfl⟩ : syracuseStep 4486823 = 6730235) B6730235
theorem B2660393 : Blo 1772087 2660393 := bstep (se 2 (by rfl) ⟨997647, by rfl⟩ : syracuseStep 2660393 = 1995295) B1995295
theorem B2660591 : Blo 1772087 2660591 := bstep (se 1 (by rfl) ⟨1995443, by rfl⟩ : syracuseStep 2660591 = 3990887) B3990887
theorem B2660603 : Blo 1772087 2660603 := bstep (se 1 (by rfl) ⟨1995452, by rfl⟩ : syracuseStep 2660603 = 3990905) B3990905
theorem B2660663 : Blo 1772087 2660663 := bstep (se 1 (by rfl) ⟨1995497, by rfl⟩ : syracuseStep 2660663 = 3990995) B3990995
theorem B8976743 : Blo 1772087 8976743 := bstep (se 1 (by rfl) ⟨6732557, by rfl⟩ : syracuseStep 8976743 = 13465115) B13465115
theorem B3193427 : Blo 1772087 3193427 := bstep (se 1 (by rfl) ⟨2395070, by rfl⟩ : syracuseStep 3193427 = 4790141) B4790141
theorem B3365543 : Blo 1772087 3365543 := bstep (se 1 (by rfl) ⟨2524157, by rfl⟩ : syracuseStep 3365543 = 5048315) B5048315
theorem B8977553 : Blo 1772087 8977553 := bstep (se 2 (by rfl) ⟨3366582, by rfl⟩ : syracuseStep 8977553 = 6733165) B6733165
theorem B4488443 : Blo 1772087 4488443 := bstep (se 1 (by rfl) ⟨3366332, by rfl⟩ : syracuseStep 4488443 = 6732665) B6732665
theorem B34553303 : Blo 1772087 34553303 := bstep (se 1 (by rfl) ⟨25914977, by rfl⟩ : syracuseStep 34553303 = 51829955) B51829955
theorem B34086581 : Blo 1772087 34086581 := bstep (se 5 (by rfl) ⟨1597808, by rfl⟩ : syracuseStep 34086581 = 3195617) B3195617
theorem B3989483 : Blo 1772087 3989483 := bstep (se 1 (by rfl) ⟨2992112, by rfl⟩ : syracuseStep 3989483 = 5984225) B5984225
theorem B69067255 : Blo 1772087 69067255 := bstep (se 1 (by rfl) ⟨51800441, by rfl⟩ : syracuseStep 69067255 = 103600883) B103600883
theorem B3990599 : Blo 1772087 3990599 := bstep (se 1 (by rfl) ⟨2992949, by rfl⟩ : syracuseStep 3990599 = 5985899) B5985899
theorem B2991215 : Blo 1772087 2991215 := bstep (se 1 (by rfl) ⟨2243411, by rfl⟩ : syracuseStep 2991215 = 4486823) B4486823
theorem B15140843 : Blo 1772087 15140843 := bstep (se 1 (by rfl) ⟨11355632, by rfl⟩ : syracuseStep 15140843 = 22711265) B22711265
theorem B2992295 : Blo 1772087 2992295 := bstep (se 1 (by rfl) ⟨2244221, by rfl⟩ : syracuseStep 2992295 = 4488443) B4488443
theorem B6392317 : Blo 1772087 6392317 := bstep (se 3 (by rfl) ⟨1198559, by rfl⟩ : syracuseStep 6392317 = 2397119) B2397119
theorem B13470461 : Blo 1772087 13470461 := bstep (se 3 (by rfl) ⟨2525711, by rfl⟩ : syracuseStep 13470461 = 5051423) B5051423
theorem B1772391 : Blo 1772087 1772391 := bstep (se 1 (by rfl) ⟨1329293, by rfl⟩ : syracuseStep 1772391 = 2658587) B2658587
theorem B1772799 : Blo 1772087 1772799 := bstep (se 1 (by rfl) ⟨1329599, by rfl⟩ : syracuseStep 1772799 = 2659199) B2659199
theorem B4042055 : Blo 1772087 4042055 := bstep (se 1 (by rfl) ⟨3031541, by rfl⟩ : syracuseStep 4042055 = 6063083) B6063083
theorem B1773595 : Blo 1772087 1773595 := bstep (se 1 (by rfl) ⟨1330196, by rfl⟩ : syracuseStep 1773595 = 2660393) B2660393
theorem B1773727 : Blo 1772087 1773727 := bstep (se 1 (by rfl) ⟨1330295, by rfl⟩ : syracuseStep 1773727 = 2660591) B2660591
theorem B1773735 : Blo 1772087 1773735 := bstep (se 1 (by rfl) ⟨1330301, by rfl⟩ : syracuseStep 1773735 = 2660603) B2660603
theorem B1773775 : Blo 1772087 1773775 := bstep (se 1 (by rfl) ⟨1330331, by rfl⟩ : syracuseStep 1773775 = 2660663) B2660663
theorem B5984495 : Blo 1772087 5984495 := bstep (se 1 (by rfl) ⟨4488371, by rfl⟩ : syracuseStep 5984495 = 8976743) B8976743
theorem B6730067 : Blo 1772087 6730067 := bstep (se 1 (by rfl) ⟨5047550, by rfl⟩ : syracuseStep 6730067 = 10095101) B10095101
theorem B5985035 : Blo 1772087 5985035 := bstep (se 1 (by rfl) ⟨4488776, by rfl⟩ : syracuseStep 5985035 = 8977553) B8977553
theorem B6730553 : Blo 1772087 6730553 := bstep (se 2 (by rfl) ⟨2523957, by rfl⟩ : syracuseStep 6730553 = 5047915) B5047915
theorem B2659655 : Blo 1772087 2659655 := bstep (se 1 (by rfl) ⟨1994741, by rfl⟩ : syracuseStep 2659655 = 3989483) B3989483
theorem B2659967 : Blo 1772087 2659967 := bstep (se 1 (by rfl) ⟨1994975, by rfl⟩ : syracuseStep 2659967 = 3989951) B3989951
theorem B5986655 : Blo 1772087 5986655 := bstep (se 1 (by rfl) ⟨4489991, by rfl⟩ : syracuseStep 5986655 = 8979983) B8979983
theorem B25910057 : Blo 1772087 25910057 := bstep (se 2 (by rfl) ⟨9716271, by rfl⟩ : syracuseStep 25910057 = 19432543) B19432543
theorem B2128951 : Blo 1772087 2128951 := bstep (se 1 (by rfl) ⟨1596713, by rfl⟩ : syracuseStep 2128951 = 3193427) B3193427
theorem B2243695 : Blo 1772087 2243695 := bstep (se 1 (by rfl) ⟨1682771, by rfl⟩ : syracuseStep 2243695 = 3365543) B3365543
theorem B10100159 : Blo 1772087 10100159 := bstep (se 1 (by rfl) ⟨7575119, by rfl⟩ : syracuseStep 10100159 = 15150239) B15150239
theorem B3366431 : Blo 1772087 3366431 := bstep (se 1 (by rfl) ⟨2524823, by rfl⟩ : syracuseStep 3366431 = 5049647) B5049647
theorem B28753481 : Blo 1772087 28753481 := bstep (se 2 (by rfl) ⟨10782555, by rfl⟩ : syracuseStep 28753481 = 21565111) B21565111
theorem B23035535 : Blo 1772087 23035535 := bstep (se 1 (by rfl) ⟨17276651, by rfl⟩ : syracuseStep 23035535 = 34553303) B34553303
theorem B22724387 : Blo 1772087 22724387 := bstep (se 1 (by rfl) ⟨17043290, by rfl⟩ : syracuseStep 22724387 = 34086581) B34086581
theorem B3989663 : Blo 1772087 3989663 := bstep (se 1 (by rfl) ⟨2992247, by rfl⟩ : syracuseStep 3989663 = 5984495) B5984495
theorem B3990023 : Blo 1772087 3990023 := bstep (se 1 (by rfl) ⟨2992517, by rfl⟩ : syracuseStep 3990023 = 5985035) B5985035
theorem B10093895 : Blo 1772087 10093895 := bstep (se 1 (by rfl) ⟨7570421, by rfl⟩ : syracuseStep 10093895 = 15140843) B15140843
theorem B2991593 : Blo 1772087 2991593 := bstep (se 2 (by rfl) ⟨1121847, by rfl⟩ : syracuseStep 2991593 = 2243695) B2243695
theorem B3991103 : Blo 1772087 3991103 := bstep (se 1 (by rfl) ⟨2993327, by rfl⟩ : syracuseStep 3991103 = 5986655) B5986655
theorem B8980307 : Blo 1772087 8980307 := bstep (se 1 (by rfl) ⟨6735230, by rfl⟩ : syracuseStep 8980307 = 13470461) B13470461
theorem B15149591 : Blo 1772087 15149591 := bstep (se 1 (by rfl) ⟨11362193, by rfl⟩ : syracuseStep 15149591 = 22724387) B22724387
theorem B92089673 : Blo 1772087 92089673 := bstep (se 2 (by rfl) ⟨34533627, by rfl⟩ : syracuseStep 92089673 = 69067255) B69067255
theorem B8523089 : Blo 1772087 8523089 := bstep (se 2 (by rfl) ⟨3196158, by rfl⟩ : syracuseStep 8523089 = 6392317) B6392317
theorem B1994143 : Blo 1772087 1994143 := bstep (se 1 (by rfl) ⟨1495607, by rfl⟩ : syracuseStep 1994143 = 2991215) B2991215
theorem B1773103 : Blo 1772087 1773103 := bstep (se 1 (by rfl) ⟨1329827, by rfl⟩ : syracuseStep 1773103 = 2659655) B2659655
theorem B1773311 : Blo 1772087 1773311 := bstep (se 1 (by rfl) ⟨1329983, by rfl⟩ : syracuseStep 1773311 = 2659967) B2659967
theorem B2838601 : Blo 1772087 2838601 := bstep (se 2 (by rfl) ⟨1064475, by rfl⟩ : syracuseStep 2838601 = 2128951) B2128951
theorem B1994863 : Blo 1772087 1994863 := bstep (se 1 (by rfl) ⟨1496147, by rfl⟩ : syracuseStep 1994863 = 2992295) B2992295
theorem B17273371 : Blo 1772087 17273371 := bstep (se 1 (by rfl) ⟨12955028, by rfl⟩ : syracuseStep 17273371 = 25910057) B25910057
theorem B15357023 : Blo 1772087 15357023 := bstep (se 1 (by rfl) ⟨11517767, by rfl⟩ : syracuseStep 15357023 = 23035535) B23035535
theorem B4486711 : Blo 1772087 4486711 := bstep (se 1 (by rfl) ⟨3365033, by rfl⟩ : syracuseStep 4486711 = 6730067) B6730067
theorem B4487035 : Blo 1772087 4487035 := bstep (se 1 (by rfl) ⟨3365276, by rfl⟩ : syracuseStep 4487035 = 6730553) B6730553
theorem B2660399 : Blo 1772087 2660399 := bstep (se 1 (by rfl) ⟨1995299, by rfl⟩ : syracuseStep 2660399 = 3990599) B3990599
theorem B2694703 : Blo 1772087 2694703 := bstep (se 1 (by rfl) ⟨2021027, by rfl⟩ : syracuseStep 2694703 = 4042055) B4042055
theorem B6733439 : Blo 1772087 6733439 := bstep (se 1 (by rfl) ⟨5050079, by rfl⟩ : syracuseStep 6733439 = 10100159) B10100159
theorem B2244287 : Blo 1772087 2244287 := bstep (se 1 (by rfl) ⟨1683215, by rfl⟩ : syracuseStep 2244287 = 3366431) B3366431
theorem B19168987 : Blo 1772087 19168987 := bstep (se 1 (by rfl) ⟨14376740, by rfl⟩ : syracuseStep 19168987 = 28753481) B28753481
theorem B3784801 : Blo 1772087 3784801 := bstep (se 2 (by rfl) ⟨1419300, by rfl⟩ : syracuseStep 3784801 = 2838601) B2838601
theorem B5982281 : Blo 1772087 5982281 := bstep (se 2 (by rfl) ⟨2243355, by rfl⟩ : syracuseStep 5982281 = 4486711) B4486711
theorem B61393115 : Blo 1772087 61393115 := bstep (se 1 (by rfl) ⟨46044836, by rfl⟩ : syracuseStep 61393115 = 92089673) B92089673
theorem B5982713 : Blo 1772087 5982713 := bstep (se 2 (by rfl) ⟨2243517, by rfl⟩ : syracuseStep 5982713 = 4487035) B4487035
theorem B23031161 : Blo 1772087 23031161 := bstep (se 2 (by rfl) ⟨8636685, by rfl⟩ : syracuseStep 23031161 = 17273371) B17273371
theorem B6729263 : Blo 1772087 6729263 := bstep (se 1 (by rfl) ⟨5046947, by rfl⟩ : syracuseStep 6729263 = 10093895) B10093895
theorem B1994395 : Blo 1772087 1994395 := bstep (se 1 (by rfl) ⟨1495796, by rfl⟩ : syracuseStep 1994395 = 2991593) B2991593
theorem B1773599 : Blo 1772087 1773599 := bstep (se 1 (by rfl) ⟨1330199, by rfl⟩ : syracuseStep 1773599 = 2660399) B2660399
theorem B5984765 : Blo 1772087 5984765 := bstep (se 3 (by rfl) ⟨1122143, by rfl⟩ : syracuseStep 5984765 = 2244287) B2244287
theorem B2658857 : Blo 1772087 2658857 := bstep (se 2 (by rfl) ⟨997071, by rfl⟩ : syracuseStep 2658857 = 1994143) B1994143
theorem B3592937 : Blo 1772087 3592937 := bstep (se 2 (by rfl) ⟨1347351, by rfl⟩ : syracuseStep 3592937 = 2694703) B2694703
theorem B5682059 : Blo 1772087 5682059 := bstep (se 1 (by rfl) ⟨4261544, by rfl⟩ : syracuseStep 5682059 = 8523089) B8523089
theorem B2659775 : Blo 1772087 2659775 := bstep (se 1 (by rfl) ⟨1994831, by rfl⟩ : syracuseStep 2659775 = 3989663) B3989663
theorem B2659817 : Blo 1772087 2659817 := bstep (se 2 (by rfl) ⟨997431, by rfl⟩ : syracuseStep 2659817 = 1994863) B1994863
theorem B2660015 : Blo 1772087 2660015 := bstep (se 1 (by rfl) ⟨1995011, by rfl⟩ : syracuseStep 2660015 = 3990023) B3990023
theorem B10238015 : Blo 1772087 10238015 := bstep (se 1 (by rfl) ⟨7678511, by rfl⟩ : syracuseStep 10238015 = 15357023) B15357023
theorem B2660735 : Blo 1772087 2660735 := bstep (se 1 (by rfl) ⟨1995551, by rfl⟩ : syracuseStep 2660735 = 3991103) B3991103
theorem B5986871 : Blo 1772087 5986871 := bstep (se 1 (by rfl) ⟨4490153, by rfl⟩ : syracuseStep 5986871 = 8980307) B8980307
theorem B10099727 : Blo 1772087 10099727 := bstep (se 1 (by rfl) ⟨7574795, by rfl⟩ : syracuseStep 10099727 = 15149591) B15149591
theorem B25558649 : Blo 1772087 25558649 := bstep (se 2 (by rfl) ⟨9584493, by rfl⟩ : syracuseStep 25558649 = 19168987) B19168987
theorem B4488959 : Blo 1772087 4488959 := bstep (se 1 (by rfl) ⟨3366719, by rfl⟩ : syracuseStep 4488959 = 6733439) B6733439
theorem B5046401 : Blo 1772087 5046401 := bstep (se 2 (by rfl) ⟨1892400, by rfl⟩ : syracuseStep 5046401 = 3784801) B3784801
theorem B3989843 : Blo 1772087 3989843 := bstep (se 1 (by rfl) ⟨2992382, by rfl⟩ : syracuseStep 3989843 = 5984765) B5984765
theorem B6825343 : Blo 1772087 6825343 := bstep (se 1 (by rfl) ⟨5119007, by rfl⟩ : syracuseStep 6825343 = 10238015) B10238015
theorem B40928743 : Blo 1772087 40928743 := bstep (se 1 (by rfl) ⟨30696557, by rfl⟩ : syracuseStep 40928743 = 61393115) B61393115
theorem B3991247 : Blo 1772087 3991247 := bstep (se 1 (by rfl) ⟨2993435, by rfl⟩ : syracuseStep 3991247 = 5986871) B5986871
theorem B15354107 : Blo 1772087 15354107 := bstep (se 1 (by rfl) ⟨11515580, by rfl⟩ : syracuseStep 15354107 = 23031161) B23031161
theorem B2992639 : Blo 1772087 2992639 := bstep (se 1 (by rfl) ⟨2244479, by rfl⟩ : syracuseStep 2992639 = 4488959) B4488959
theorem B1772571 : Blo 1772087 1772571 := bstep (se 1 (by rfl) ⟨1329428, by rfl⟩ : syracuseStep 1772571 = 2658857) B2658857
theorem B2395291 : Blo 1772087 2395291 := bstep (se 1 (by rfl) ⟨1796468, by rfl⟩ : syracuseStep 2395291 = 3592937) B3592937
theorem B3788039 : Blo 1772087 3788039 := bstep (se 1 (by rfl) ⟨2841029, by rfl⟩ : syracuseStep 3788039 = 5682059) B5682059
theorem B1773183 : Blo 1772087 1773183 := bstep (se 1 (by rfl) ⟨1329887, by rfl⟩ : syracuseStep 1773183 = 2659775) B2659775
theorem B1773211 : Blo 1772087 1773211 := bstep (se 1 (by rfl) ⟨1329908, by rfl⟩ : syracuseStep 1773211 = 2659817) B2659817
theorem B1773343 : Blo 1772087 1773343 := bstep (se 1 (by rfl) ⟨1330007, by rfl⟩ : syracuseStep 1773343 = 2660015) B2660015
theorem B1773823 : Blo 1772087 1773823 := bstep (se 1 (by rfl) ⟨1330367, by rfl⟩ : syracuseStep 1773823 = 2660735) B2660735
theorem B2659193 : Blo 1772087 2659193 := bstep (se 2 (by rfl) ⟨997197, by rfl⟩ : syracuseStep 2659193 = 1994395) B1994395
theorem B4486175 : Blo 1772087 4486175 := bstep (se 1 (by rfl) ⟨3364631, by rfl⟩ : syracuseStep 4486175 = 6729263) B6729263
theorem B3988187 : Blo 1772087 3988187 := bstep (se 1 (by rfl) ⟨2991140, by rfl⟩ : syracuseStep 3988187 = 5982281) B5982281
theorem B3988475 : Blo 1772087 3988475 := bstep (se 1 (by rfl) ⟨2991356, by rfl⟩ : syracuseStep 3988475 = 5982713) B5982713
theorem B6733151 : Blo 1772087 6733151 := bstep (se 1 (by rfl) ⟨5049863, by rfl⟩ : syracuseStep 6733151 = 10099727) B10099727
theorem B17039099 : Blo 1772087 17039099 := bstep (se 1 (by rfl) ⟨12779324, by rfl⟩ : syracuseStep 17039099 = 25558649) B25558649
theorem B3990185 : Blo 1772087 3990185 := bstep (se 2 (by rfl) ⟨1496319, by rfl⟩ : syracuseStep 3990185 = 2992639) B2992639
theorem B2990783 : Blo 1772087 2990783 := bstep (se 1 (by rfl) ⟨2243087, by rfl⟩ : syracuseStep 2990783 = 4486175) B4486175
theorem B2525359 : Blo 1772087 2525359 := bstep (se 1 (by rfl) ⟨1894019, by rfl⟩ : syracuseStep 2525359 = 3788039) B3788039
theorem B1772795 : Blo 1772087 1772795 := bstep (se 1 (by rfl) ⟨1329596, by rfl⟩ : syracuseStep 1772795 = 2659193) B2659193
theorem B10236071 : Blo 1772087 10236071 := bstep (se 1 (by rfl) ⟨7677053, by rfl⟩ : syracuseStep 10236071 = 15354107) B15354107
theorem B2658791 : Blo 1772087 2658791 := bstep (se 1 (by rfl) ⟨1994093, by rfl⟩ : syracuseStep 2658791 = 3988187) B3988187
theorem B54571657 : Blo 1772087 54571657 := bstep (se 2 (by rfl) ⟨20464371, by rfl⟩ : syracuseStep 54571657 = 40928743) B40928743
theorem B2658983 : Blo 1772087 2658983 := bstep (se 1 (by rfl) ⟨1994237, by rfl⟩ : syracuseStep 2658983 = 3988475) B3988475
theorem B11359399 : Blo 1772087 11359399 := bstep (se 1 (by rfl) ⟨8519549, by rfl⟩ : syracuseStep 11359399 = 17039099) B17039099
theorem B3364267 : Blo 1772087 3364267 := bstep (se 1 (by rfl) ⟨2523200, by rfl⟩ : syracuseStep 3364267 = 5046401) B5046401
theorem B2659895 : Blo 1772087 2659895 := bstep (se 1 (by rfl) ⟨1994921, by rfl⟩ : syracuseStep 2659895 = 3989843) B3989843
theorem B2660831 : Blo 1772087 2660831 := bstep (se 1 (by rfl) ⟨1995623, by rfl⟩ : syracuseStep 2660831 = 3991247) B3991247
theorem B3193721 : Blo 1772087 3193721 := bstep (se 2 (by rfl) ⟨1197645, by rfl⟩ : syracuseStep 3193721 = 2395291) B2395291
theorem B9100457 : Blo 1772087 9100457 := bstep (se 2 (by rfl) ⟨3412671, by rfl⟩ : syracuseStep 9100457 = 6825343) B6825343
theorem B4488767 : Blo 1772087 4488767 := bstep (se 1 (by rfl) ⟨3366575, by rfl⟩ : syracuseStep 4488767 = 6733151) B6733151
theorem B3367145 : Blo 1772087 3367145 := bstep (se 2 (by rfl) ⟨1262679, by rfl⟩ : syracuseStep 3367145 = 2525359) B2525359
theorem B27296189 : Blo 1772087 27296189 := bstep (se 3 (by rfl) ⟨5118035, by rfl⟩ : syracuseStep 27296189 = 10236071) B10236071
theorem B72762209 : Blo 1772087 72762209 := bstep (se 2 (by rfl) ⟨27285828, by rfl⟩ : syracuseStep 72762209 = 54571657) B54571657
theorem B2992511 : Blo 1772087 2992511 := bstep (se 1 (by rfl) ⟨2244383, by rfl⟩ : syracuseStep 2992511 = 4488767) B4488767
theorem B1772527 : Blo 1772087 1772527 := bstep (se 1 (by rfl) ⟨1329395, by rfl⟩ : syracuseStep 1772527 = 2658791) B2658791
theorem B1772655 : Blo 1772087 1772655 := bstep (se 1 (by rfl) ⟨1329491, by rfl⟩ : syracuseStep 1772655 = 2658983) B2658983
theorem B1993855 : Blo 1772087 1993855 := bstep (se 1 (by rfl) ⟨1495391, by rfl⟩ : syracuseStep 1993855 = 2990783) B2990783
theorem B1773263 : Blo 1772087 1773263 := bstep (se 1 (by rfl) ⟨1329947, by rfl⟩ : syracuseStep 1773263 = 2659895) B2659895
theorem B1773887 : Blo 1772087 1773887 := bstep (se 1 (by rfl) ⟨1330415, by rfl⟩ : syracuseStep 1773887 = 2660831) B2660831
theorem B4485689 : Blo 1772087 4485689 := bstep (se 2 (by rfl) ⟨1682133, by rfl⟩ : syracuseStep 4485689 = 3364267) B3364267
theorem B6066971 : Blo 1772087 6066971 := bstep (se 1 (by rfl) ⟨4550228, by rfl⟩ : syracuseStep 6066971 = 9100457) B9100457
theorem B2660123 : Blo 1772087 2660123 := bstep (se 1 (by rfl) ⟨1995092, by rfl⟩ : syracuseStep 2660123 = 3990185) B3990185
theorem B15145865 : Blo 1772087 15145865 := bstep (se 2 (by rfl) ⟨5679699, by rfl⟩ : syracuseStep 15145865 = 11359399) B11359399
theorem B2129147 : Blo 1772087 2129147 := bstep (se 1 (by rfl) ⟨1596860, by rfl⟩ : syracuseStep 2129147 = 3193721) B3193721
theorem B2244763 : Blo 1772087 2244763 := bstep (se 1 (by rfl) ⟨1683572, by rfl⟩ : syracuseStep 2244763 = 3367145) B3367145
theorem B2990459 : Blo 1772087 2990459 := bstep (se 1 (by rfl) ⟨2242844, by rfl⟩ : syracuseStep 2990459 = 4485689) B4485689
theorem B22710901 : Blo 1772087 22710901 := bstep (se 5 (by rfl) ⟨1064573, by rfl⟩ : syracuseStep 22710901 = 2129147) B2129147
theorem B18197459 : Blo 1772087 18197459 := bstep (se 1 (by rfl) ⟨13648094, by rfl⟩ : syracuseStep 18197459 = 27296189) B27296189
theorem B48508139 : Blo 1772087 48508139 := bstep (se 1 (by rfl) ⟨36381104, by rfl⟩ : syracuseStep 48508139 = 72762209) B72762209
theorem B1773415 : Blo 1772087 1773415 := bstep (se 1 (by rfl) ⟨1330061, by rfl⟩ : syracuseStep 1773415 = 2660123) B2660123
theorem B2658473 : Blo 1772087 2658473 := bstep (se 2 (by rfl) ⟨996927, by rfl⟩ : syracuseStep 2658473 = 1993855) B1993855
theorem B1995007 : Blo 1772087 1995007 := bstep (se 1 (by rfl) ⟨1496255, by rfl⟩ : syracuseStep 1995007 = 2992511) B2992511
theorem B10097243 : Blo 1772087 10097243 := bstep (se 1 (by rfl) ⟨7572932, by rfl⟩ : syracuseStep 10097243 = 15145865) B15145865
theorem B4044647 : Blo 1772087 4044647 := bstep (se 1 (by rfl) ⟨3033485, by rfl⟩ : syracuseStep 4044647 = 6066971) B6066971
theorem B2696431 : Blo 1772087 2696431 := bstep (se 1 (by rfl) ⟨2022323, by rfl⟩ : syracuseStep 2696431 = 4044647) B4044647
theorem B1772315 : Blo 1772087 1772315 := bstep (se 1 (by rfl) ⟨1329236, by rfl⟩ : syracuseStep 1772315 = 2658473) B2658473
theorem B2993017 : Blo 1772087 2993017 := bstep (se 2 (by rfl) ⟨1122381, by rfl⟩ : syracuseStep 2993017 = 2244763) B2244763
theorem B1993639 : Blo 1772087 1993639 := bstep (se 1 (by rfl) ⟨1495229, by rfl⟩ : syracuseStep 1993639 = 2990459) B2990459
theorem B30281201 : Blo 1772087 30281201 := bstep (se 2 (by rfl) ⟨11355450, by rfl⟩ : syracuseStep 30281201 = 22710901) B22710901
theorem B32338759 : Blo 1772087 32338759 := bstep (se 1 (by rfl) ⟨24254069, by rfl⟩ : syracuseStep 32338759 = 48508139) B48508139
theorem B2660009 : Blo 1772087 2660009 := bstep (se 2 (by rfl) ⟨997503, by rfl⟩ : syracuseStep 2660009 = 1995007) B1995007
theorem B6731495 : Blo 1772087 6731495 := bstep (se 1 (by rfl) ⟨5048621, by rfl⟩ : syracuseStep 6731495 = 10097243) B10097243
theorem B12131639 : Blo 1772087 12131639 := bstep (se 1 (by rfl) ⟨9098729, by rfl⟩ : syracuseStep 12131639 = 18197459) B18197459
theorem B3990689 : Blo 1772087 3990689 := bstep (se 2 (by rfl) ⟨1496508, by rfl⟩ : syracuseStep 3990689 = 2993017) B2993017
theorem B8087759 : Blo 1772087 8087759 := bstep (se 1 (by rfl) ⟨6065819, by rfl⟩ : syracuseStep 8087759 = 12131639) B12131639
theorem B20187467 : Blo 1772087 20187467 := bstep (se 1 (by rfl) ⟨15140600, by rfl⟩ : syracuseStep 20187467 = 30281201) B30281201
theorem B43118345 : Blo 1772087 43118345 := bstep (se 2 (by rfl) ⟨16169379, by rfl⟩ : syracuseStep 43118345 = 32338759) B32338759
theorem B1773339 : Blo 1772087 1773339 := bstep (se 1 (by rfl) ⟨1330004, by rfl⟩ : syracuseStep 1773339 = 2660009) B2660009
theorem B2658185 : Blo 1772087 2658185 := bstep (se 2 (by rfl) ⟨996819, by rfl⟩ : syracuseStep 2658185 = 1993639) B1993639
theorem B4487663 : Blo 1772087 4487663 := bstep (se 1 (by rfl) ⟨3365747, by rfl⟩ : syracuseStep 4487663 = 6731495) B6731495
theorem B3595241 : Blo 1772087 3595241 := bstep (se 2 (by rfl) ⟨1348215, by rfl⟩ : syracuseStep 3595241 = 2696431) B2696431
theorem B5391839 : Blo 1772087 5391839 := bstep (se 1 (by rfl) ⟨4043879, by rfl⟩ : syracuseStep 5391839 = 8087759) B8087759
theorem B2991775 : Blo 1772087 2991775 := bstep (se 1 (by rfl) ⟨2243831, by rfl⟩ : syracuseStep 2991775 = 4487663) B4487663
theorem B1772123 : Blo 1772087 1772123 := bstep (se 1 (by rfl) ⟨1329092, by rfl⟩ : syracuseStep 1772123 = 2658185) B2658185
theorem B2396827 : Blo 1772087 2396827 := bstep (se 1 (by rfl) ⟨1797620, by rfl⟩ : syracuseStep 2396827 = 3595241) B3595241
theorem B2660459 : Blo 1772087 2660459 := bstep (se 1 (by rfl) ⟨1995344, by rfl⟩ : syracuseStep 2660459 = 3990689) B3990689
theorem B13458311 : Blo 1772087 13458311 := bstep (se 1 (by rfl) ⟨10093733, by rfl⟩ : syracuseStep 13458311 = 20187467) B20187467
theorem B28745563 : Blo 1772087 28745563 := bstep (se 1 (by rfl) ⟨21559172, by rfl⟩ : syracuseStep 28745563 = 43118345) B43118345
theorem B3195769 : Blo 1772087 3195769 := bstep (se 2 (by rfl) ⟨1198413, by rfl⟩ : syracuseStep 3195769 = 2396827) B2396827
theorem B8972207 : Blo 1772087 8972207 := bstep (se 1 (by rfl) ⟨6729155, by rfl⟩ : syracuseStep 8972207 = 13458311) B13458311
theorem B1773639 : Blo 1772087 1773639 := bstep (se 1 (by rfl) ⟨1330229, by rfl⟩ : syracuseStep 1773639 = 2660459) B2660459
theorem B38327417 : Blo 1772087 38327417 := bstep (se 2 (by rfl) ⟨14372781, by rfl⟩ : syracuseStep 38327417 = 28745563) B28745563
theorem B3594559 : Blo 1772087 3594559 := bstep (se 1 (by rfl) ⟨2695919, by rfl⟩ : syracuseStep 3594559 = 5391839) B5391839
theorem B3989033 : Blo 1772087 3989033 := bstep (se 2 (by rfl) ⟨1495887, by rfl⟩ : syracuseStep 3989033 = 2991775) B2991775
theorem B4792745 : Blo 1772087 4792745 := bstep (se 2 (by rfl) ⟨1797279, by rfl⟩ : syracuseStep 4792745 = 3594559) B3594559
theorem B25551611 : Blo 1772087 25551611 := bstep (se 1 (by rfl) ⟨19163708, by rfl⟩ : syracuseStep 25551611 = 38327417) B38327417
theorem B4261025 : Blo 1772087 4261025 := bstep (se 2 (by rfl) ⟨1597884, by rfl⟩ : syracuseStep 4261025 = 3195769) B3195769
theorem B5981471 : Blo 1772087 5981471 := bstep (se 1 (by rfl) ⟨4486103, by rfl⟩ : syracuseStep 5981471 = 8972207) B8972207
theorem B2659355 : Blo 1772087 2659355 := bstep (se 1 (by rfl) ⟨1994516, by rfl⟩ : syracuseStep 2659355 = 3989033) B3989033
theorem B3195163 : Blo 1772087 3195163 := bstep (se 1 (by rfl) ⟨2396372, by rfl⟩ : syracuseStep 3195163 = 4792745) B4792745
theorem B17034407 : Blo 1772087 17034407 := bstep (se 1 (by rfl) ⟨12775805, by rfl⟩ : syracuseStep 17034407 = 25551611) B25551611
theorem B1772903 : Blo 1772087 1772903 := bstep (se 1 (by rfl) ⟨1329677, by rfl⟩ : syracuseStep 1772903 = 2659355) B2659355
theorem B2840683 : Blo 1772087 2840683 := bstep (se 1 (by rfl) ⟨2130512, by rfl⟩ : syracuseStep 2840683 = 4261025) B4261025
theorem B3987647 : Blo 1772087 3987647 := bstep (se 1 (by rfl) ⟨2990735, by rfl⟩ : syracuseStep 3987647 = 5981471) B5981471
theorem B4260217 : Blo 1772087 4260217 := bstep (se 2 (by rfl) ⟨1597581, by rfl⟩ : syracuseStep 4260217 = 3195163) B3195163
theorem B11356271 : Blo 1772087 11356271 := bstep (se 1 (by rfl) ⟨8517203, by rfl⟩ : syracuseStep 11356271 = 17034407) B17034407
theorem B3787577 : Blo 1772087 3787577 := bstep (se 2 (by rfl) ⟨1420341, by rfl⟩ : syracuseStep 3787577 = 2840683) B2840683
theorem B2658431 : Blo 1772087 2658431 := bstep (se 1 (by rfl) ⟨1993823, by rfl⟩ : syracuseStep 2658431 = 3987647) B3987647
theorem B7570847 : Blo 1772087 7570847 := bstep (se 1 (by rfl) ⟨5678135, by rfl⟩ : syracuseStep 7570847 = 11356271) B11356271
theorem B2525051 : Blo 1772087 2525051 := bstep (se 1 (by rfl) ⟨1893788, by rfl⟩ : syracuseStep 2525051 = 3787577) B3787577
theorem B1772287 : Blo 1772087 1772287 := bstep (se 1 (by rfl) ⟨1329215, by rfl⟩ : syracuseStep 1772287 = 2658431) B2658431
theorem B5680289 : Blo 1772087 5680289 := bstep (se 2 (by rfl) ⟨2130108, by rfl⟩ : syracuseStep 5680289 = 4260217) B4260217
theorem B3786859 : Blo 1772087 3786859 := bstep (se 1 (by rfl) ⟨2840144, by rfl⟩ : syracuseStep 3786859 = 5680289) B5680289
theorem B20188925 : Blo 1772087 20188925 := bstep (se 3 (by rfl) ⟨3785423, by rfl⟩ : syracuseStep 20188925 = 7570847) B7570847
theorem B6733469 : Blo 1772087 6733469 := bstep (se 3 (by rfl) ⟨1262525, by rfl⟩ : syracuseStep 6733469 = 2525051) B2525051
theorem B5049145 : Blo 1772087 5049145 := bstep (se 2 (by rfl) ⟨1893429, by rfl⟩ : syracuseStep 5049145 = 3786859) B3786859
theorem B4488979 : Blo 1772087 4488979 := bstep (se 1 (by rfl) ⟨3366734, by rfl⟩ : syracuseStep 4488979 = 6733469) B6733469
theorem B13459283 : Blo 1772087 13459283 := bstep (se 1 (by rfl) ⟨10094462, by rfl⟩ : syracuseStep 13459283 = 20188925) B20188925
theorem B8972855 : Blo 1772087 8972855 := bstep (se 1 (by rfl) ⟨6729641, by rfl⟩ : syracuseStep 8972855 = 13459283) B13459283
theorem B5985305 : Blo 1772087 5985305 := bstep (se 2 (by rfl) ⟨2244489, by rfl⟩ : syracuseStep 5985305 = 4488979) B4488979
theorem B6732193 : Blo 1772087 6732193 := bstep (se 2 (by rfl) ⟨2524572, by rfl⟩ : syracuseStep 6732193 = 5049145) B5049145
theorem B3990203 : Blo 1772087 3990203 := bstep (se 1 (by rfl) ⟨2992652, by rfl⟩ : syracuseStep 3990203 = 5985305) B5985305
theorem B5981903 : Blo 1772087 5981903 := bstep (se 1 (by rfl) ⟨4486427, by rfl⟩ : syracuseStep 5981903 = 8972855) B8972855
theorem B8976257 : Blo 1772087 8976257 := bstep (se 2 (by rfl) ⟨3366096, by rfl⟩ : syracuseStep 8976257 = 6732193) B6732193
theorem B5984171 : Blo 1772087 5984171 := bstep (se 1 (by rfl) ⟨4488128, by rfl⟩ : syracuseStep 5984171 = 8976257) B8976257
theorem B2660135 : Blo 1772087 2660135 := bstep (se 1 (by rfl) ⟨1995101, by rfl⟩ : syracuseStep 2660135 = 3990203) B3990203
theorem B3987935 : Blo 1772087 3987935 := bstep (se 1 (by rfl) ⟨2990951, by rfl⟩ : syracuseStep 3987935 = 5981903) B5981903
theorem B1773423 : Blo 1772087 1773423 := bstep (se 1 (by rfl) ⟨1330067, by rfl⟩ : syracuseStep 1773423 = 2660135) B2660135
theorem B2658623 : Blo 1772087 2658623 := bstep (se 1 (by rfl) ⟨1993967, by rfl⟩ : syracuseStep 2658623 = 3987935) B3987935
theorem B3989447 : Blo 1772087 3989447 := bstep (se 1 (by rfl) ⟨2992085, by rfl⟩ : syracuseStep 3989447 = 5984171) B5984171
theorem B1772415 : Blo 1772087 1772415 := bstep (se 1 (by rfl) ⟨1329311, by rfl⟩ : syracuseStep 1772415 = 2658623) B2658623
theorem B2659631 : Blo 1772087 2659631 := bstep (se 1 (by rfl) ⟨1994723, by rfl⟩ : syracuseStep 2659631 = 3989447) B3989447
theorem B1773087 : Blo 1772087 1773087 := bstep (se 1 (by rfl) ⟨1329815, by rfl⟩ : syracuseStep 1773087 = 2659631) B2659631

theorem C0 (j : ℕ) (h1 : 443021 ≤ j) (h2 : j ≤ 443521) : Blo 1772087 (4 * j + 3) := by
  interval_cases j
  · exact B1772087
  · exact B1772091
  · exact B1772095
  · exact B1772099
  · exact B1772103
  · exact B1772107
  · exact B1772111
  · exact B1772115
  · exact B1772119
  · exact B1772123
  · exact B1772127
  · exact B1772131
  · exact B1772135
  · exact B1772139
  · exact B1772143
  · exact B1772147
  · exact B1772151
  · exact B1772155
  · exact B1772159
  · exact B1772163
  · exact B1772167
  · exact B1772171
  · exact B1772175
  · exact B1772179
  · exact B1772183
  · exact B1772187
  · exact B1772191
  · exact B1772195
  · exact B1772199
  · exact B1772203
  · exact B1772207
  · exact B1772211
  · exact B1772215
  · exact B1772219
  · exact B1772223
  · exact B1772227
  · exact B1772231
  · exact B1772235
  · exact B1772239
  · exact B1772243
  · exact B1772247
  · exact B1772251
  · exact B1772255
  · exact B1772259
  · exact B1772263
  · exact B1772267
  · exact B1772271
  · exact B1772275
  · exact B1772279
  · exact B1772283
  · exact B1772287
  · exact B1772291
  · exact B1772295
  · exact B1772299
  · exact B1772303
  · exact B1772307
  · exact B1772311
  · exact B1772315
  · exact B1772319
  · exact B1772323
  · exact B1772327
  · exact B1772331
  · exact B1772335
  · exact B1772339
  · exact B1772343
  · exact B1772347
  · exact B1772351
  · exact B1772355
  · exact B1772359
  · exact B1772363
  · exact B1772367
  · exact B1772371
  · exact B1772375
  · exact B1772379
  · exact B1772383
  · exact B1772387
  · exact B1772391
  · exact B1772395
  · exact B1772399
  · exact B1772403
  · exact B1772407
  · exact B1772411
  · exact B1772415
  · exact B1772419
  · exact B1772423
  · exact B1772427
  · exact B1772431
  · exact B1772435
  · exact B1772439
  · exact B1772443
  · exact B1772447
  · exact B1772451
  · exact B1772455
  · exact B1772459
  · exact B1772463
  · exact B1772467
  · exact B1772471
  · exact B1772475
  · exact B1772479
  · exact B1772483
  · exact B1772487
  · exact B1772491
  · exact B1772495
  · exact B1772499
  · exact B1772503
  · exact B1772507
  · exact B1772511
  · exact B1772515
  · exact B1772519
  · exact B1772523
  · exact B1772527
  · exact B1772531
  · exact B1772535
  · exact B1772539
  · exact B1772543
  · exact B1772547
  · exact B1772551
  · exact B1772555
  · exact B1772559
  · exact B1772563
  · exact B1772567
  · exact B1772571
  · exact B1772575
  · exact B1772579
  · exact B1772583
  · exact B1772587
  · exact B1772591
  · exact B1772595
  · exact B1772599
  · exact B1772603
  · exact B1772607
  · exact B1772611
  · exact B1772615
  · exact B1772619
  · exact B1772623
  · exact B1772627
  · exact B1772631
  · exact B1772635
  · exact B1772639
  · exact B1772643
  · exact B1772647
  · exact B1772651
  · exact B1772655
  · exact B1772659
  · exact B1772663
  · exact B1772667
  · exact B1772671
  · exact B1772675
  · exact B1772679
  · exact B1772683
  · exact B1772687
  · exact B1772691
  · exact B1772695
  · exact B1772699
  · exact B1772703
  · exact B1772707
  · exact B1772711
  · exact B1772715
  · exact B1772719
  · exact B1772723
  · exact B1772727
  · exact B1772731
  · exact B1772735
  · exact B1772739
  · exact B1772743
  · exact B1772747
  · exact B1772751
  · exact B1772755
  · exact B1772759
  · exact B1772763
  · exact B1772767
  · exact B1772771
  · exact B1772775
  · exact B1772779
  · exact B1772783
  · exact B1772787
  · exact B1772791
  · exact B1772795
  · exact B1772799
  · exact B1772803
  · exact B1772807
  · exact B1772811
  · exact B1772815
  · exact B1772819
  · exact B1772823
  · exact B1772827
  · exact B1772831
  · exact B1772835
  · exact B1772839
  · exact B1772843
  · exact B1772847
  · exact B1772851
  · exact B1772855
  · exact B1772859
  · exact B1772863
  · exact B1772867
  · exact B1772871
  · exact B1772875
  · exact B1772879
  · exact B1772883
  · exact B1772887
  · exact B1772891
  · exact B1772895
  · exact B1772899
  · exact B1772903
  · exact B1772907
  · exact B1772911
  · exact B1772915
  · exact B1772919
  · exact B1772923
  · exact B1772927
  · exact B1772931
  · exact B1772935
  · exact B1772939
  · exact B1772943
  · exact B1772947
  · exact B1772951
  · exact B1772955
  · exact B1772959
  · exact B1772963
  · exact B1772967
  · exact B1772971
  · exact B1772975
  · exact B1772979
  · exact B1772983
  · exact B1772987
  · exact B1772991
  · exact B1772995
  · exact B1772999
  · exact B1773003
  · exact B1773007
  · exact B1773011
  · exact B1773015
  · exact B1773019
  · exact B1773023
  · exact B1773027
  · exact B1773031
  · exact B1773035
  · exact B1773039
  · exact B1773043
  · exact B1773047
  · exact B1773051
  · exact B1773055
  · exact B1773059
  · exact B1773063
  · exact B1773067
  · exact B1773071
  · exact B1773075
  · exact B1773079
  · exact B1773083
  · exact B1773087
  · exact B1773091
  · exact B1773095
  · exact B1773099
  · exact B1773103
  · exact B1773107
  · exact B1773111
  · exact B1773115
  · exact B1773119
  · exact B1773123
  · exact B1773127
  · exact B1773131
  · exact B1773135
  · exact B1773139
  · exact B1773143
  · exact B1773147
  · exact B1773151
  · exact B1773155
  · exact B1773159
  · exact B1773163
  · exact B1773167
  · exact B1773171
  · exact B1773175
  · exact B1773179
  · exact B1773183
  · exact B1773187
  · exact B1773191
  · exact B1773195
  · exact B1773199
  · exact B1773203
  · exact B1773207
  · exact B1773211
  · exact B1773215
  · exact B1773219
  · exact B1773223
  · exact B1773227
  · exact B1773231
  · exact B1773235
  · exact B1773239
  · exact B1773243
  · exact B1773247
  · exact B1773251
  · exact B1773255
  · exact B1773259
  · exact B1773263
  · exact B1773267
  · exact B1773271
  · exact B1773275
  · exact B1773279
  · exact B1773283
  · exact B1773287
  · exact B1773291
  · exact B1773295
  · exact B1773299
  · exact B1773303
  · exact B1773307
  · exact B1773311
  · exact B1773315
  · exact B1773319
  · exact B1773323
  · exact B1773327
  · exact B1773331
  · exact B1773335
  · exact B1773339
  · exact B1773343
  · exact B1773347
  · exact B1773351
  · exact B1773355
  · exact B1773359
  · exact B1773363
  · exact B1773367
  · exact B1773371
  · exact B1773375
  · exact B1773379
  · exact B1773383
  · exact B1773387
  · exact B1773391
  · exact B1773395
  · exact B1773399
  · exact B1773403
  · exact B1773407
  · exact B1773411
  · exact B1773415
  · exact B1773419
  · exact B1773423
  · exact B1773427
  · exact B1773431
  · exact B1773435
  · exact B1773439
  · exact B1773443
  · exact B1773447
  · exact B1773451
  · exact B1773455
  · exact B1773459
  · exact B1773463
  · exact B1773467
  · exact B1773471
  · exact B1773475
  · exact B1773479
  · exact B1773483
  · exact B1773487
  · exact B1773491
  · exact B1773495
  · exact B1773499
  · exact B1773503
  · exact B1773507
  · exact B1773511
  · exact B1773515
  · exact B1773519
  · exact B1773523
  · exact B1773527
  · exact B1773531
  · exact B1773535
  · exact B1773539
  · exact B1773543
  · exact B1773547
  · exact B1773551
  · exact B1773555
  · exact B1773559
  · exact B1773563
  · exact B1773567
  · exact B1773571
  · exact B1773575
  · exact B1773579
  · exact B1773583
  · exact B1773587
  · exact B1773591
  · exact B1773595
  · exact B1773599
  · exact B1773603
  · exact B1773607
  · exact B1773611
  · exact B1773615
  · exact B1773619
  · exact B1773623
  · exact B1773627
  · exact B1773631
  · exact B1773635
  · exact B1773639
  · exact B1773643
  · exact B1773647
  · exact B1773651
  · exact B1773655
  · exact B1773659
  · exact B1773663
  · exact B1773667
  · exact B1773671
  · exact B1773675
  · exact B1773679
  · exact B1773683
  · exact B1773687
  · exact B1773691
  · exact B1773695
  · exact B1773699
  · exact B1773703
  · exact B1773707
  · exact B1773711
  · exact B1773715
  · exact B1773719
  · exact B1773723
  · exact B1773727
  · exact B1773731
  · exact B1773735
  · exact B1773739
  · exact B1773743
  · exact B1773747
  · exact B1773751
  · exact B1773755
  · exact B1773759
  · exact B1773763
  · exact B1773767
  · exact B1773771
  · exact B1773775
  · exact B1773779
  · exact B1773783
  · exact B1773787
  · exact B1773791
  · exact B1773795
  · exact B1773799
  · exact B1773803
  · exact B1773807
  · exact B1773811
  · exact B1773815
  · exact B1773819
  · exact B1773823
  · exact B1773827
  · exact B1773831
  · exact B1773835
  · exact B1773839
  · exact B1773843
  · exact B1773847
  · exact B1773851
  · exact B1773855
  · exact B1773859
  · exact B1773863
  · exact B1773867
  · exact B1773871
  · exact B1773875
  · exact B1773879
  · exact B1773883
  · exact B1773887
  · exact B1773891
  · exact B1773895
  · exact B1773899
  · exact B1773903
  · exact B1773907
  · exact B1773911
  · exact B1773915
  · exact B1773919
  · exact B1773923
  · exact B1773927
  · exact B1773931
  · exact B1773935
  · exact B1773939
  · exact B1773943
  · exact B1773947
  · exact B1773951
  · exact B1773955
  · exact B1773959
  · exact B1773963
  · exact B1773967
  · exact B1773971
  · exact B1773975
  · exact B1773979
  · exact B1773983
  · exact B1773987
  · exact B1773991
  · exact B1773995
  · exact B1773999
  · exact B1774003
  · exact B1774007
  · exact B1774011
  · exact B1774015
  · exact B1774019
  · exact B1774023
  · exact B1774027
  · exact B1774031
  · exact B1774035
  · exact B1774039
  · exact B1774043
  · exact B1774047
  · exact B1774051
  · exact B1774055
  · exact B1774059
  · exact B1774063
  · exact B1774067
  · exact B1774071
  · exact B1774075
  · exact B1774079
  · exact B1774083
  · exact B1774087

theorem solution (m : ℕ) (hlo : 1772087 ≤ m) (hhi : m ≤ 1774087) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 443021 ≤ j := by omega
    have hj2 : j ≤ 443521 := by omega
    have hb : Blo 1772087 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
