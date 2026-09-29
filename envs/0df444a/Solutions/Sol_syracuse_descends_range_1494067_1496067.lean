-- Prove2me | solution 1 for syracuse_descends_range_1494067_1496067
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:47:10.494+00:00
-- url     : https://prove2.me/submissions/04f828e8-3e8c-4dc2-80a3-dbd6d8fd6323

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


theorem B2129933 : Blo 1494067 2129933 := bbase (se 3 (by rfl) ⟨399362, by rfl⟩ : syracuseStep 2129933 = 798725) (by norm_num)
theorem B3784765 : Blo 1494067 3784765 := bbase (se 3 (by rfl) ⟨709643, by rfl⟩ : syracuseStep 3784765 = 1419287) (by norm_num)
theorem B2523197 : Blo 1494067 2523197 := bbase (se 3 (by rfl) ⟨473099, by rfl⟩ : syracuseStep 2523197 = 946199) (by norm_num)
theorem B1892413 : Blo 1494067 1892413 := bbase (se 3 (by rfl) ⟨354827, by rfl⟩ : syracuseStep 1892413 = 709655) (by norm_num)
theorem B1597501 : Blo 1494067 1597501 := bbase (se 3 (by rfl) ⟨299531, by rfl⟩ : syracuseStep 1597501 = 599063) (by norm_num)
theorem B16162901 : Blo 1494067 16162901 := bbase (se 8 (by rfl) ⟨94704, by rfl⟩ : syracuseStep 16162901 = 189409) (by norm_num)
theorem B2130013 : Blo 1494067 2130013 := bbase (se 3 (by rfl) ⟨399377, by rfl⟩ : syracuseStep 2130013 = 798755) (by norm_num)
theorem B3833981 : Blo 1494067 3833981 := bbase (se 3 (by rfl) ⟨718871, by rfl⟩ : syracuseStep 3833981 = 1437743) (by norm_num)
theorem B6815893 : Blo 1494067 6815893 := bbase (se 6 (by rfl) ⟨159747, by rfl⟩ : syracuseStep 6815893 = 319495) (by norm_num)
theorem B3784877 : Blo 1494067 3784877 := bbase (se 3 (by rfl) ⟨709664, by rfl⟩ : syracuseStep 3784877 = 1419329) (by norm_num)
theorem B2523325 : Blo 1494067 2523325 := bbase (se 3 (by rfl) ⟨473123, by rfl⟩ : syracuseStep 2523325 = 946247) (by norm_num)
theorem B2130133 : Blo 1494067 2130133 := bbase (se 7 (by rfl) ⟨24962, by rfl⟩ : syracuseStep 2130133 = 49925) (by norm_num)
theorem B1892585 : Blo 1494067 1892585 := bbase (se 2 (by rfl) ⟨709719, by rfl⟩ : syracuseStep 1892585 = 1419439) (by norm_num)
theorem B7184645 : Blo 1494067 7184645 := bbase (se 4 (by rfl) ⟨673560, by rfl⟩ : syracuseStep 7184645 = 1347121) (by norm_num)
theorem B2523413 : Blo 1494067 2523413 := bbase (se 6 (by rfl) ⟨59142, by rfl⟩ : syracuseStep 2523413 = 118285) (by norm_num)
theorem B1892641 : Blo 1494067 1892641 := bbase (se 2 (by rfl) ⟨709740, by rfl⟩ : syracuseStep 1892641 = 1419481) (by norm_num)
theorem B3195173 : Blo 1494067 3195173 := bbase (se 4 (by rfl) ⟨299547, by rfl⟩ : syracuseStep 3195173 = 599095) (by norm_num)
theorem B3785069 : Blo 1494067 3785069 := bbase (se 3 (by rfl) ⟨709700, by rfl⟩ : syracuseStep 3785069 = 1419401) (by norm_num)
theorem B1892737 : Blo 1494067 1892737 := bbase (se 2 (by rfl) ⟨709776, by rfl⟩ : syracuseStep 1892737 = 1419553) (by norm_num)
theorem B4792709 : Blo 1494067 4792709 := bbase (se 4 (by rfl) ⟨449316, by rfl⟩ : syracuseStep 4792709 = 898633) (by norm_num)
theorem B5046677 : Blo 1494067 5046677 := bbase (se 6 (by rfl) ⟨118281, by rfl⟩ : syracuseStep 5046677 = 236563) (by norm_num)
theorem B2523541 : Blo 1494067 2523541 := bbase (se 6 (by rfl) ⟨59145, by rfl⟩ : syracuseStep 2523541 = 118291) (by norm_num)
theorem B1917361 : Blo 1494067 1917361 := bbase (se 2 (by rfl) ⟨719010, by rfl⟩ : syracuseStep 1917361 = 1438021) (by norm_num)
theorem B2523629 : Blo 1494067 2523629 := bbase (se 3 (by rfl) ⟨473180, by rfl⟩ : syracuseStep 2523629 = 946361) (by norm_num)
theorem B6062597 : Blo 1494067 6062597 := bbase (se 4 (by rfl) ⟨568368, by rfl⟩ : syracuseStep 6062597 = 1136737) (by norm_num)
theorem B5677573 : Blo 1494067 5677573 := bbase (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) (by norm_num)
theorem B3408421 : Blo 1494067 3408421 := bbase (se 4 (by rfl) ⟨319539, by rfl⟩ : syracuseStep 3408421 = 639079) (by norm_num)
theorem B1892909 : Blo 1494067 1892909 := bbase (se 3 (by rfl) ⟨354920, by rfl⟩ : syracuseStep 1892909 = 709841) (by norm_num)
theorem B1892965 : Blo 1494067 1892965 := bbase (se 4 (by rfl) ⟨177465, by rfl⟩ : syracuseStep 1892965 = 354931) (by norm_num)
theorem B2523757 : Blo 1494067 2523757 := bbase (se 3 (by rfl) ⟨473204, by rfl⟩ : syracuseStep 2523757 = 946409) (by norm_num)
theorem B1704613 : Blo 1494067 1704613 := bbase (se 4 (by rfl) ⟨159807, by rfl⟩ : syracuseStep 1704613 = 319615) (by norm_num)
theorem B6062789 : Blo 1494067 6062789 := bbase (se 4 (by rfl) ⟨568386, by rfl⟩ : syracuseStep 6062789 = 1136773) (by norm_num)
theorem B3785413 : Blo 1494067 3785413 := bbase (se 4 (by rfl) ⟨354882, by rfl⟩ : syracuseStep 3785413 = 709765) (by norm_num)
theorem B2523845 : Blo 1494067 2523845 := bbase (se 4 (by rfl) ⟨236610, by rfl⟩ : syracuseStep 2523845 = 473221) (by norm_num)
theorem B1893061 : Blo 1494067 1893061 := bbase (se 4 (by rfl) ⟨177474, by rfl⟩ : syracuseStep 1893061 = 354949) (by norm_num)
theorem B5186261 : Blo 1494067 5186261 := bbase (se 7 (by rfl) ⟨60776, by rfl⟩ : syracuseStep 5186261 = 121553) (by norm_num)
theorem B8086229 : Blo 1494067 8086229 := bbase (se 7 (by rfl) ⟨94760, by rfl⟩ : syracuseStep 8086229 = 189521) (by norm_num)
theorem B1516249 : Blo 1494067 1516249 := bbase (se 2 (by rfl) ⟨568593, by rfl⟩ : syracuseStep 1516249 = 1137187) (by norm_num)
theorem B5677877 : Blo 1494067 5677877 := bbase (se 5 (by rfl) ⟨266150, by rfl⟩ : syracuseStep 5677877 = 532301) (by norm_num)
theorem B3785525 : Blo 1494067 3785525 := bbase (se 5 (by rfl) ⟨177446, by rfl⟩ : syracuseStep 3785525 = 354893) (by norm_num)
theorem B5047109 : Blo 1494067 5047109 := bbase (se 4 (by rfl) ⟨473166, by rfl⟩ : syracuseStep 5047109 = 946333) (by norm_num)
theorem B2523973 : Blo 1494067 2523973 := bbase (se 4 (by rfl) ⟨236622, by rfl⟩ : syracuseStep 2523973 = 473245) (by norm_num)
theorem B34530133 : Blo 1494067 34530133 := bbase (se 9 (by rfl) ⟨101162, by rfl⟩ : syracuseStep 34530133 = 202325) (by norm_num)
theorem B3457885 : Blo 1494067 3457885 := bbase (se 3 (by rfl) ⟨648353, by rfl⟩ : syracuseStep 3457885 = 1296707) (by norm_num)
theorem B1893233 : Blo 1494067 1893233 := bbase (se 2 (by rfl) ⟨709962, by rfl⟩ : syracuseStep 1893233 = 1419925) (by norm_num)
theorem B2524061 : Blo 1494067 2524061 := bbase (se 3 (by rfl) ⟨473261, by rfl⟩ : syracuseStep 2524061 = 946523) (by norm_num)
theorem B1893289 : Blo 1494067 1893289 := bbase (se 2 (by rfl) ⟨709983, by rfl⟩ : syracuseStep 1893289 = 1419967) (by norm_num)
theorem B7570421 : Blo 1494067 7570421 := bbase (se 5 (by rfl) ⟨354863, by rfl⟩ : syracuseStep 7570421 = 709727) (by norm_num)
theorem B3785717 : Blo 1494067 3785717 := bbase (se 5 (by rfl) ⟨177455, by rfl⟩ : syracuseStep 3785717 = 354911) (by norm_num)
theorem B5391365 : Blo 1494067 5391365 := bbase (se 4 (by rfl) ⟨505440, by rfl⟩ : syracuseStep 5391365 = 1010881) (by norm_num)
theorem B1893385 : Blo 1494067 1893385 := bbase (se 2 (by rfl) ⟨710019, by rfl⟩ : syracuseStep 1893385 = 1420039) (by norm_num)
theorem B2524189 : Blo 1494067 2524189 := bbase (se 3 (by rfl) ⟨473285, by rfl⟩ : syracuseStep 2524189 = 946571) (by norm_num)
theorem B3032101 : Blo 1494067 3032101 := bbase (se 4 (by rfl) ⟨284259, by rfl⟩ : syracuseStep 3032101 = 568519) (by norm_num)
theorem B2524277 : Blo 1494067 2524277 := bbase (se 5 (by rfl) ⟨118325, by rfl⟩ : syracuseStep 2524277 = 236651) (by norm_num)
theorem B5047541 : Blo 1494067 5047541 := bbase (se 5 (by rfl) ⟨236603, by rfl⟩ : syracuseStep 5047541 = 473207) (by norm_num)
theorem B2524405 : Blo 1494067 2524405 := bbase (se 5 (by rfl) ⟨118331, by rfl⟩ : syracuseStep 2524405 = 236663) (by norm_num)
theorem B3835133 : Blo 1494067 3835133 := bbase (se 3 (by rfl) ⟨719087, by rfl⟩ : syracuseStep 3835133 = 1438175) (by norm_num)
theorem B3786061 : Blo 1494067 3786061 := bbase (se 3 (by rfl) ⟨709886, by rfl⟩ : syracuseStep 3786061 = 1419773) (by norm_num)
theorem B2524493 : Blo 1494067 2524493 := bbase (se 3 (by rfl) ⟨473342, by rfl⟩ : syracuseStep 2524493 = 946685) (by norm_num)
theorem B10225045 : Blo 1494067 10225045 := bbase (se 6 (by rfl) ⟨239649, by rfl⟩ : syracuseStep 10225045 = 479299) (by norm_num)
theorem B1795493 : Blo 1494067 1795493 := bbase (se 4 (by rfl) ⟨168327, by rfl⟩ : syracuseStep 1795493 = 336655) (by norm_num)
theorem B3786173 : Blo 1494067 3786173 := bbase (se 3 (by rfl) ⟨709907, by rfl⟩ : syracuseStep 3786173 = 1419815) (by norm_num)
theorem B1680853 : Blo 1494067 1680853 := bbase (se 7 (by rfl) ⟨19697, by rfl⟩ : syracuseStep 1680853 = 39395) (by norm_num)
theorem B36349397 : Blo 1494067 36349397 := bbase (se 7 (by rfl) ⟨425969, by rfl⟩ : syracuseStep 36349397 = 851939) (by norm_num)
theorem B1680889 : Blo 1494067 1680889 := bbase (se 2 (by rfl) ⟨630333, by rfl⟩ : syracuseStep 1680889 = 1260667) (by norm_num)
theorem B1680925 : Blo 1494067 1680925 := bbase (se 3 (by rfl) ⟨315173, by rfl⟩ : syracuseStep 1680925 = 630347) (by norm_num)
theorem B1820209 : Blo 1494067 1820209 := bbase (se 2 (by rfl) ⟨682578, by rfl⟩ : syracuseStep 1820209 = 1365157) (by norm_num)
theorem B1680961 : Blo 1494067 1680961 := bbase (se 2 (by rfl) ⟨630360, by rfl⟩ : syracuseStep 1680961 = 1260721) (by norm_num)
theorem B1680997 : Blo 1494067 1680997 := bbase (se 4 (by rfl) ⟨157593, by rfl⟩ : syracuseStep 1680997 = 315187) (by norm_num)
theorem B3786365 : Blo 1494067 3786365 := bbase (se 3 (by rfl) ⟨709943, by rfl⟩ : syracuseStep 3786365 = 1419887) (by norm_num)
theorem B1681033 : Blo 1494067 1681033 := bbase (se 2 (by rfl) ⟨630387, by rfl⟩ : syracuseStep 1681033 = 1260775) (by norm_num)
theorem B2557589 : Blo 1494067 2557589 := bbase (se 6 (by rfl) ⟨59943, by rfl⟩ : syracuseStep 2557589 = 119887) (by norm_num)
theorem B5047973 : Blo 1494067 5047973 := bbase (se 4 (by rfl) ⟨473247, by rfl⟩ : syracuseStep 5047973 = 946495) (by norm_num)
theorem B1681069 : Blo 1494067 1681069 := bbase (se 3 (by rfl) ⟨315200, by rfl⟩ : syracuseStep 1681069 = 630401) (by norm_num)
theorem B1681105 : Blo 1494067 1681105 := bbase (se 2 (by rfl) ⟨630414, by rfl⟩ : syracuseStep 1681105 = 1260829) (by norm_num)
theorem B1681141 : Blo 1494067 1681141 := bbase (se 5 (by rfl) ⟨78803, by rfl⟩ : syracuseStep 1681141 = 157607) (by norm_num)
theorem B3032821 : Blo 1494067 3032821 := bbase (se 5 (by rfl) ⟨142163, by rfl⟩ : syracuseStep 3032821 = 284327) (by norm_num)
theorem B3639053 : Blo 1494067 3639053 := bbase (se 3 (by rfl) ⟨682322, by rfl⟩ : syracuseStep 3639053 = 1364645) (by norm_num)
theorem B2393869 : Blo 1494067 2393869 := bbase (se 3 (by rfl) ⟨448850, by rfl⟩ : syracuseStep 2393869 = 897701) (by norm_num)
theorem B7669525 : Blo 1494067 7669525 := bbase (se 6 (by rfl) ⟨179754, by rfl⟩ : syracuseStep 7669525 = 359509) (by norm_num)
theorem B1681177 : Blo 1494067 1681177 := bbase (se 2 (by rfl) ⟨630441, by rfl⟩ : syracuseStep 1681177 = 1260883) (by norm_num)
theorem B12773173 : Blo 1494067 12773173 := bbase (se 5 (by rfl) ⟨598742, by rfl⟩ : syracuseStep 12773173 = 1197485) (by norm_num)
theorem B1681213 : Blo 1494067 1681213 := bbase (se 3 (by rfl) ⟨315227, by rfl⟩ : syracuseStep 1681213 = 630455) (by norm_num)
theorem B3589957 : Blo 1494067 3589957 := bbase (se 4 (by rfl) ⟨336558, by rfl⟩ : syracuseStep 3589957 = 673117) (by norm_num)
theorem B1681249 : Blo 1494067 1681249 := bbase (se 2 (by rfl) ⟨630468, by rfl⟩ : syracuseStep 1681249 = 1260937) (by norm_num)
theorem B1795969 : Blo 1494067 1795969 := bbase (se 2 (by rfl) ⟨673488, by rfl⟩ : syracuseStep 1795969 = 1346977) (by norm_num)
theorem B2590597 : Blo 1494067 2590597 := bbase (se 4 (by rfl) ⟨242868, by rfl⟩ : syracuseStep 2590597 = 485737) (by norm_num)
theorem B1681285 : Blo 1494067 1681285 := bbase (se 4 (by rfl) ⟨157620, by rfl⟩ : syracuseStep 1681285 = 315241) (by norm_num)
theorem B1795997 : Blo 1494067 1795997 := bbase (se 3 (by rfl) ⟨336749, by rfl⟩ : syracuseStep 1795997 = 673499) (by norm_num)
theorem B1681321 : Blo 1494067 1681321 := bbase (se 2 (by rfl) ⟨630495, by rfl⟩ : syracuseStep 1681321 = 1260991) (by norm_num)
theorem B1681357 : Blo 1494067 1681357 := bbase (se 3 (by rfl) ⟨315254, by rfl⟩ : syracuseStep 1681357 = 630509) (by norm_num)
theorem B3786709 : Blo 1494067 3786709 := bbase (se 7 (by rfl) ⟨44375, by rfl⟩ : syracuseStep 3786709 = 88751) (by norm_num)
theorem B1681393 : Blo 1494067 1681393 := bbase (se 2 (by rfl) ⟨630522, by rfl⟩ : syracuseStep 1681393 = 1261045) (by norm_num)
theorem B3590149 : Blo 1494067 3590149 := bbase (se 4 (by rfl) ⟨336576, by rfl⟩ : syracuseStep 3590149 = 673153) (by norm_num)
theorem B2394125 : Blo 1494067 2394125 := bbase (se 3 (by rfl) ⟨448898, by rfl⟩ : syracuseStep 2394125 = 897797) (by norm_num)
theorem B1681429 : Blo 1494067 1681429 := bbase (se 6 (by rfl) ⟨39408, by rfl⟩ : syracuseStep 1681429 = 78817) (by norm_num)
theorem B3590189 : Blo 1494067 3590189 := bbase (se 3 (by rfl) ⟨673160, by rfl⟩ : syracuseStep 3590189 = 1346321) (by norm_num)
theorem B1681465 : Blo 1494067 1681465 := bbase (se 2 (by rfl) ⟨630549, by rfl⟩ : syracuseStep 1681465 = 1261099) (by norm_num)
theorem B3786821 : Blo 1494067 3786821 := bbase (se 4 (by rfl) ⟨355014, by rfl⟩ : syracuseStep 3786821 = 710029) (by norm_num)
theorem B4098133 : Blo 1494067 4098133 := bbase (se 8 (by rfl) ⟨24012, by rfl⟩ : syracuseStep 4098133 = 48025) (by norm_num)
theorem B5048405 : Blo 1494067 5048405 := bbase (se 8 (by rfl) ⟨29580, by rfl⟩ : syracuseStep 5048405 = 59161) (by norm_num)
theorem B1796185 : Blo 1494067 1796185 := bbase (se 2 (by rfl) ⟨673569, by rfl⟩ : syracuseStep 1796185 = 1347139) (by norm_num)
theorem B1681501 : Blo 1494067 1681501 := bbase (se 3 (by rfl) ⟨315281, by rfl⟩ : syracuseStep 1681501 = 630563) (by norm_num)
theorem B6383717 : Blo 1494067 6383717 := bbase (se 4 (by rfl) ⟨598473, by rfl⟩ : syracuseStep 6383717 = 1196947) (by norm_num)
theorem B1681537 : Blo 1494067 1681537 := bbase (se 2 (by rfl) ⟨630576, by rfl⟩ : syracuseStep 1681537 = 1261153) (by norm_num)
theorem B6473861 : Blo 1494067 6473861 := bbase (se 4 (by rfl) ⟨606924, by rfl⟩ : syracuseStep 6473861 = 1213849) (by norm_num)
theorem B1681573 : Blo 1494067 1681573 := bbase (se 4 (by rfl) ⟨157647, by rfl⟩ : syracuseStep 1681573 = 315295) (by norm_num)
theorem B1681609 : Blo 1494067 1681609 := bbase (se 2 (by rfl) ⟨630603, by rfl⟩ : syracuseStep 1681609 = 1261207) (by norm_num)
theorem B2394317 : Blo 1494067 2394317 := bbase (se 3 (by rfl) ⟨448934, by rfl⟩ : syracuseStep 2394317 = 897869) (by norm_num)
theorem B1796305 : Blo 1494067 1796305 := bbase (se 2 (by rfl) ⟨673614, by rfl⟩ : syracuseStep 1796305 = 1347229) (by norm_num)
theorem B1681645 : Blo 1494067 1681645 := bbase (se 3 (by rfl) ⟨315308, by rfl⟩ : syracuseStep 1681645 = 630617) (by norm_num)
theorem B7571717 : Blo 1494067 7571717 := bbase (se 4 (by rfl) ⟨709848, by rfl⟩ : syracuseStep 7571717 = 1419697) (by norm_num)
theorem B1681681 : Blo 1494067 1681681 := bbase (se 2 (by rfl) ⟨630630, by rfl⟩ : syracuseStep 1681681 = 1261261) (by norm_num)
theorem B1681717 : Blo 1494067 1681717 := bbase (se 5 (by rfl) ⟨78830, by rfl⟩ : syracuseStep 1681717 = 157661) (by norm_num)
theorem B3590477 : Blo 1494067 3590477 := bbase (se 3 (by rfl) ⟨673214, by rfl⟩ : syracuseStep 3590477 = 1346429) (by norm_num)
theorem B1681753 : Blo 1494067 1681753 := bbase (se 2 (by rfl) ⟨630657, by rfl⟩ : syracuseStep 1681753 = 1261315) (by norm_num)
theorem B1681789 : Blo 1494067 1681789 := bbase (se 3 (by rfl) ⟨315335, by rfl⟩ : syracuseStep 1681789 = 630671) (by norm_num)
theorem B1681825 : Blo 1494067 1681825 := bbase (se 2 (by rfl) ⟨630684, by rfl⟩ : syracuseStep 1681825 = 1261369) (by norm_num)
theorem B1681861 : Blo 1494067 1681861 := bbase (se 4 (by rfl) ⟨157674, by rfl⟩ : syracuseStep 1681861 = 315349) (by norm_num)
theorem B2836957 : Blo 1494067 2836957 := bbase (se 3 (by rfl) ⟨531929, by rfl⟩ : syracuseStep 2836957 = 1063859) (by norm_num)
theorem B1681897 : Blo 1494067 1681897 := bbase (se 2 (by rfl) ⟨630711, by rfl⟩ : syracuseStep 1681897 = 1261423) (by norm_num)
theorem B5048837 : Blo 1494067 5048837 := bbase (se 4 (by rfl) ⟨473328, by rfl⟩ : syracuseStep 5048837 = 946657) (by norm_num)
theorem B1681933 : Blo 1494067 1681933 := bbase (se 3 (by rfl) ⟨315362, by rfl⟩ : syracuseStep 1681933 = 630725) (by norm_num)
theorem B1681969 : Blo 1494067 1681969 := bbase (se 2 (by rfl) ⟨630738, by rfl⟩ : syracuseStep 1681969 = 1261477) (by norm_num)
theorem B1682005 : Blo 1494067 1682005 := bbase (se 8 (by rfl) ⟨9855, by rfl⟩ : syracuseStep 1682005 = 19711) (by norm_num)
theorem B17033813 : Blo 1494067 17033813 := bbase (se 8 (by rfl) ⟨99807, by rfl⟩ : syracuseStep 17033813 = 199615) (by norm_num)
theorem B4786789 : Blo 1494067 4786789 := bbase (se 4 (by rfl) ⟨448761, by rfl⟩ : syracuseStep 4786789 = 897523) (by norm_num)
theorem B2837101 : Blo 1494067 2837101 := bbase (se 3 (by rfl) ⟨531956, by rfl⟩ : syracuseStep 2837101 = 1063913) (by norm_num)
theorem B1682041 : Blo 1494067 1682041 := bbase (se 2 (by rfl) ⟨630765, by rfl⟩ : syracuseStep 1682041 = 1261531) (by norm_num)
theorem B1682077 : Blo 1494067 1682077 := bbase (se 3 (by rfl) ⟨315389, by rfl⟩ : syracuseStep 1682077 = 630779) (by norm_num)
theorem B7563941 : Blo 1494067 7563941 := bbase (se 4 (by rfl) ⟨709119, by rfl⟩ : syracuseStep 7563941 = 1418239) (by norm_num)
theorem B1682113 : Blo 1494067 1682113 := bbase (se 2 (by rfl) ⟨630792, by rfl⟩ : syracuseStep 1682113 = 1261585) (by norm_num)
theorem B19163861 : Blo 1494067 19163861 := bbase (se 7 (by rfl) ⟨224576, by rfl⟩ : syracuseStep 19163861 = 449153) (by norm_num)
theorem B1682149 : Blo 1494067 1682149 := bbase (se 4 (by rfl) ⟨157701, by rfl⟩ : syracuseStep 1682149 = 315403) (by norm_num)
theorem B1682185 : Blo 1494067 1682185 := bbase (se 2 (by rfl) ⟨630819, by rfl⟩ : syracuseStep 1682185 = 1261639) (by norm_num)
theorem B2837261 : Blo 1494067 2837261 := bbase (se 3 (by rfl) ⟨531986, by rfl⟩ : syracuseStep 2837261 = 1063973) (by norm_num)
theorem B1682221 : Blo 1494067 1682221 := bbase (se 3 (by rfl) ⟨315416, by rfl⟩ : syracuseStep 1682221 = 630833) (by norm_num)
theorem B1682257 : Blo 1494067 1682257 := bbase (se 2 (by rfl) ⟨630846, by rfl⟩ : syracuseStep 1682257 = 1261693) (by norm_num)
theorem B1682293 : Blo 1494067 1682293 := bbase (se 5 (by rfl) ⟨78857, by rfl⟩ : syracuseStep 1682293 = 157715) (by norm_num)
theorem B5679989 : Blo 1494067 5679989 := bbase (se 5 (by rfl) ⟨266249, by rfl⟩ : syracuseStep 5679989 = 532499) (by norm_num)
theorem B3361661 : Blo 1494067 3361661 := bbase (se 3 (by rfl) ⟨630311, by rfl⟩ : syracuseStep 3361661 = 1260623) (by norm_num)
theorem B1682329 : Blo 1494067 1682329 := bbase (se 2 (by rfl) ⟨630873, by rfl⟩ : syracuseStep 1682329 = 1261747) (by norm_num)
theorem B2837405 : Blo 1494067 2837405 := bbase (se 3 (by rfl) ⟨532013, by rfl⟩ : syracuseStep 2837405 = 1064027) (by norm_num)
theorem B1682365 : Blo 1494067 1682365 := bbase (se 3 (by rfl) ⟨315443, by rfl⟩ : syracuseStep 1682365 = 630887) (by norm_num)
theorem B3361733 : Blo 1494067 3361733 := bbase (se 4 (by rfl) ⟨315162, by rfl⟩ : syracuseStep 3361733 = 630325) (by norm_num)
theorem B1682401 : Blo 1494067 1682401 := bbase (se 2 (by rfl) ⟨630900, by rfl⟩ : syracuseStep 1682401 = 1261801) (by norm_num)
theorem B1682437 : Blo 1494067 1682437 := bbase (se 4 (by rfl) ⟨157728, by rfl⟩ : syracuseStep 1682437 = 315457) (by norm_num)
theorem B3361805 : Blo 1494067 3361805 := bbase (se 3 (by rfl) ⟨630338, by rfl⟩ : syracuseStep 3361805 = 1260677) (by norm_num)
theorem B14363669 : Blo 1494067 14363669 := bbase (se 6 (by rfl) ⟨336648, by rfl⟩ : syracuseStep 14363669 = 673297) (by norm_num)
theorem B1682473 : Blo 1494067 1682473 := bbase (se 2 (by rfl) ⟨630927, by rfl⟩ : syracuseStep 1682473 = 1261855) (by norm_num)
theorem B7187525 : Blo 1494067 7187525 := bbase (se 4 (by rfl) ⟨673830, by rfl⟩ : syracuseStep 7187525 = 1347661) (by norm_num)
theorem B1682509 : Blo 1494067 1682509 := bbase (se 3 (by rfl) ⟨315470, by rfl⟩ : syracuseStep 1682509 = 630941) (by norm_num)
theorem B3361877 : Blo 1494067 3361877 := bbase (se 8 (by rfl) ⟨19698, by rfl⟩ : syracuseStep 3361877 = 39397) (by norm_num)
theorem B1682545 : Blo 1494067 1682545 := bbase (se 2 (by rfl) ⟨630954, by rfl⟩ : syracuseStep 1682545 = 1261909) (by norm_num)
theorem B2395253 : Blo 1494067 2395253 := bbase (se 5 (by rfl) ⟨112277, by rfl⟩ : syracuseStep 2395253 = 224555) (by norm_num)
theorem B11357333 : Blo 1494067 11357333 := bbase (se 6 (by rfl) ⟨266187, by rfl⟩ : syracuseStep 11357333 = 532375) (by norm_num)
theorem B1682581 : Blo 1494067 1682581 := bbase (se 6 (by rfl) ⟨39435, by rfl⟩ : syracuseStep 1682581 = 78871) (by norm_num)
theorem B5680277 : Blo 1494067 5680277 := bbase (se 6 (by rfl) ⟨133131, by rfl⟩ : syracuseStep 5680277 = 266263) (by norm_num)
theorem B3361949 : Blo 1494067 3361949 := bbase (se 3 (by rfl) ⟨630365, by rfl⟩ : syracuseStep 3361949 = 1260731) (by norm_num)
theorem B1682617 : Blo 1494067 1682617 := bbase (se 2 (by rfl) ⟨630981, by rfl⟩ : syracuseStep 1682617 = 1261963) (by norm_num)
theorem B2837693 : Blo 1494067 2837693 := bbase (se 3 (by rfl) ⟨532067, by rfl⟩ : syracuseStep 2837693 = 1064135) (by norm_num)
theorem B1682653 : Blo 1494067 1682653 := bbase (se 3 (by rfl) ⟨315497, by rfl⟩ : syracuseStep 1682653 = 630995) (by norm_num)
theorem B3362021 : Blo 1494067 3362021 := bbase (se 4 (by rfl) ⟨315189, by rfl⟩ : syracuseStep 3362021 = 630379) (by norm_num)
theorem B1682689 : Blo 1494067 1682689 := bbase (se 2 (by rfl) ⟨631008, by rfl⟩ : syracuseStep 1682689 = 1262017) (by norm_num)
theorem B1682725 : Blo 1494067 1682725 := bbase (se 4 (by rfl) ⟨157755, by rfl⟩ : syracuseStep 1682725 = 315511) (by norm_num)
theorem B3362093 : Blo 1494067 3362093 := bbase (se 3 (by rfl) ⟨630392, by rfl⟩ : syracuseStep 3362093 = 1260785) (by norm_num)
theorem B1682761 : Blo 1494067 1682761 := bbase (se 2 (by rfl) ⟨631035, by rfl⟩ : syracuseStep 1682761 = 1262071) (by norm_num)
theorem B2837845 : Blo 1494067 2837845 := bbase (se 11 (by rfl) ⟨2078, by rfl⟩ : syracuseStep 2837845 = 4157) (by norm_num)
theorem B1682797 : Blo 1494067 1682797 := bbase (se 3 (by rfl) ⟨315524, by rfl⟩ : syracuseStep 1682797 = 631049) (by norm_num)
theorem B3362165 : Blo 1494067 3362165 := bbase (se 5 (by rfl) ⟨157601, by rfl⟩ : syracuseStep 3362165 = 315203) (by norm_num)
theorem B1682833 : Blo 1494067 1682833 := bbase (se 2 (by rfl) ⟨631062, by rfl⟩ : syracuseStep 1682833 = 1262125) (by norm_num)
theorem B1682869 : Blo 1494067 1682869 := bbase (se 5 (by rfl) ⟨78884, by rfl⟩ : syracuseStep 1682869 = 157769) (by norm_num)
theorem B3362237 : Blo 1494067 3362237 := bbase (se 3 (by rfl) ⟨630419, by rfl⟩ : syracuseStep 3362237 = 1260839) (by norm_num)
theorem B5385685 : Blo 1494067 5385685 := bbase (se 7 (by rfl) ⟨63113, by rfl⟩ : syracuseStep 5385685 = 126227) (by norm_num)
theorem B1682905 : Blo 1494067 1682905 := bbase (se 2 (by rfl) ⟨631089, by rfl⟩ : syracuseStep 1682905 = 1262179) (by norm_num)
theorem B2395637 : Blo 1494067 2395637 := bbase (se 5 (by rfl) ⟨112295, by rfl⟩ : syracuseStep 2395637 = 224591) (by norm_num)
theorem B1682941 : Blo 1494067 1682941 := bbase (se 3 (by rfl) ⟨315551, by rfl⟩ : syracuseStep 1682941 = 631103) (by norm_num)
theorem B3362309 : Blo 1494067 3362309 := bbase (se 4 (by rfl) ⟨315216, by rfl⟩ : syracuseStep 3362309 = 630433) (by norm_num)
theorem B15543829 : Blo 1494067 15543829 := bbase (se 6 (by rfl) ⟨364308, by rfl⟩ : syracuseStep 15543829 = 728617) (by norm_num)
theorem B7573013 : Blo 1494067 7573013 := bbase (se 6 (by rfl) ⟨177492, by rfl⟩ : syracuseStep 7573013 = 354985) (by norm_num)
theorem B1682977 : Blo 1494067 1682977 := bbase (se 2 (by rfl) ⟨631116, by rfl⟩ : syracuseStep 1682977 = 1262233) (by norm_num)
theorem B11349557 : Blo 1494067 11349557 := bbase (se 5 (by rfl) ⟨532010, by rfl⟩ : syracuseStep 11349557 = 1064021) (by norm_num)
theorem B1683013 : Blo 1494067 1683013 := bbase (se 4 (by rfl) ⟨157782, by rfl⟩ : syracuseStep 1683013 = 315565) (by norm_num)
theorem B3362381 : Blo 1494067 3362381 := bbase (se 3 (by rfl) ⟨630446, by rfl⟩ : syracuseStep 3362381 = 1260893) (by norm_num)
theorem B1683049 : Blo 1494067 1683049 := bbase (se 2 (by rfl) ⟨631143, by rfl⟩ : syracuseStep 1683049 = 1262287) (by norm_num)
theorem B2395765 : Blo 1494067 2395765 := bbase (se 5 (by rfl) ⟨112301, by rfl⟩ : syracuseStep 2395765 = 224603) (by norm_num)
theorem B2838149 : Blo 1494067 2838149 := bbase (se 4 (by rfl) ⟨266076, by rfl⟩ : syracuseStep 2838149 = 532153) (by norm_num)
theorem B3362453 : Blo 1494067 3362453 := bbase (se 6 (by rfl) ⟨78807, by rfl⟩ : syracuseStep 3362453 = 157615) (by norm_num)
theorem B3362525 : Blo 1494067 3362525 := bbase (se 3 (by rfl) ⟨630473, by rfl⟩ : syracuseStep 3362525 = 1260947) (by norm_num)
theorem B12775157 : Blo 1494067 12775157 := bbase (se 5 (by rfl) ⟨598835, by rfl⟩ : syracuseStep 12775157 = 1197671) (by norm_num)
theorem B1535761 : Blo 1494067 1535761 := bbase (se 2 (by rfl) ⟨575910, by rfl⟩ : syracuseStep 1535761 = 1151821) (by norm_num)
theorem B3362597 : Blo 1494067 3362597 := bbase (se 4 (by rfl) ⟨315243, by rfl⟩ : syracuseStep 3362597 = 630487) (by norm_num)
theorem B6385493 : Blo 1494067 6385493 := bbase (se 9 (by rfl) ⟨18707, by rfl⟩ : syracuseStep 6385493 = 37415) (by norm_num)
theorem B2158429 : Blo 1494067 2158429 := bbase (se 3 (by rfl) ⟨404705, by rfl⟩ : syracuseStep 2158429 = 809411) (by norm_num)
theorem B3362669 : Blo 1494067 3362669 := bbase (se 3 (by rfl) ⟨630500, by rfl⟩ : syracuseStep 3362669 = 1261001) (by norm_num)
theorem B7565237 : Blo 1494067 7565237 := bbase (se 5 (by rfl) ⟨354620, by rfl⟩ : syracuseStep 7565237 = 709241) (by norm_num)
theorem B3362741 : Blo 1494067 3362741 := bbase (se 5 (by rfl) ⟨157628, by rfl⟩ : syracuseStep 3362741 = 315257) (by norm_num)
theorem B3362813 : Blo 1494067 3362813 := bbase (se 3 (by rfl) ⟨630527, by rfl⟩ : syracuseStep 3362813 = 1261055) (by norm_num)
theorem B2019325 : Blo 1494067 2019325 := bbase (se 3 (by rfl) ⟨378623, by rfl⟩ : syracuseStep 2019325 = 757247) (by norm_num)
theorem B5754901 : Blo 1494067 5754901 := bbase (se 6 (by rfl) ⟨134880, by rfl⟩ : syracuseStep 5754901 = 269761) (by norm_num)
theorem B3362885 : Blo 1494067 3362885 := bbase (se 4 (by rfl) ⟨315270, by rfl⟩ : syracuseStep 3362885 = 630541) (by norm_num)
theorem B3362957 : Blo 1494067 3362957 := bbase (se 3 (by rfl) ⟨630554, by rfl⟩ : syracuseStep 3362957 = 1261109) (by norm_num)
theorem B2019541 : Blo 1494067 2019541 := bbase (se 7 (by rfl) ⟨23666, by rfl⟩ : syracuseStep 2019541 = 47333) (by norm_num)
theorem B3363029 : Blo 1494067 3363029 := bbase (se 7 (by rfl) ⟨39410, by rfl⟩ : syracuseStep 3363029 = 78821) (by norm_num)
theorem B10367189 : Blo 1494067 10367189 := bbase (se 7 (by rfl) ⟨121490, by rfl⟩ : syracuseStep 10367189 = 242981) (by norm_num)
theorem B3363101 : Blo 1494067 3363101 := bbase (se 3 (by rfl) ⟨630581, by rfl⟩ : syracuseStep 3363101 = 1261163) (by norm_num)
theorem B6476117 : Blo 1494067 6476117 := bbase (se 10 (by rfl) ⟨9486, by rfl⟩ : syracuseStep 6476117 = 18973) (by norm_num)
theorem B3363173 : Blo 1494067 3363173 := bbase (se 4 (by rfl) ⟨315297, by rfl⟩ : syracuseStep 3363173 = 630595) (by norm_num)
theorem B2838901 : Blo 1494067 2838901 := bbase (se 5 (by rfl) ⟨133073, by rfl⟩ : syracuseStep 2838901 = 266147) (by norm_num)
theorem B4256165 : Blo 1494067 4256165 := bbase (se 4 (by rfl) ⟨399015, by rfl⟩ : syracuseStep 4256165 = 798031) (by norm_num)
theorem B3363245 : Blo 1494067 3363245 := bbase (se 3 (by rfl) ⟨630608, by rfl⟩ : syracuseStep 3363245 = 1261217) (by norm_num)
theorem B7180741 : Blo 1494067 7180741 := bbase (se 4 (by rfl) ⟨673194, by rfl⟩ : syracuseStep 7180741 = 1346389) (by norm_num)
theorem B11514325 : Blo 1494067 11514325 := bbase (se 7 (by rfl) ⟨134933, by rfl⟩ : syracuseStep 11514325 = 269867) (by norm_num)
theorem B3363317 : Blo 1494067 3363317 := bbase (se 5 (by rfl) ⟨157655, by rfl⟩ : syracuseStep 3363317 = 315311) (by norm_num)
theorem B2273789 : Blo 1494067 2273789 := bbase (se 3 (by rfl) ⟨426335, by rfl⟩ : syracuseStep 2273789 = 852671) (by norm_num)
theorem B2839045 : Blo 1494067 2839045 := bbase (se 4 (by rfl) ⟨266160, by rfl⟩ : syracuseStep 2839045 = 532321) (by norm_num)
theorem B3363389 : Blo 1494067 3363389 := bbase (se 3 (by rfl) ⟨630635, by rfl⟩ : syracuseStep 3363389 = 1261271) (by norm_num)
theorem B2241101 : Blo 1494067 2241101 := bbase (se 3 (by rfl) ⟨420206, by rfl⟩ : syracuseStep 2241101 = 840413) (by norm_num)
theorem B2241125 : Blo 1494067 2241125 := bbase (se 4 (by rfl) ⟨210105, by rfl⟩ : syracuseStep 2241125 = 420211) (by norm_num)
theorem B5042789 : Blo 1494067 5042789 := bbase (se 4 (by rfl) ⟨472761, by rfl⟩ : syracuseStep 5042789 = 945523) (by norm_num)
theorem B2241149 : Blo 1494067 2241149 := bbase (se 3 (by rfl) ⟨420215, by rfl⟩ : syracuseStep 2241149 = 840431) (by norm_num)
theorem B3363461 : Blo 1494067 3363461 := bbase (se 4 (by rfl) ⟨315324, by rfl⟩ : syracuseStep 3363461 = 630649) (by norm_num)
theorem B2241173 : Blo 1494067 2241173 := bbase (se 6 (by rfl) ⟨52527, by rfl⟩ : syracuseStep 2241173 = 105055) (by norm_num)
theorem B2839205 : Blo 1494067 2839205 := bbase (se 4 (by rfl) ⟨266175, by rfl⟩ : syracuseStep 2839205 = 532351) (by norm_num)
theorem B2241197 : Blo 1494067 2241197 := bbase (se 3 (by rfl) ⟨420224, by rfl⟩ : syracuseStep 2241197 = 840449) (by norm_num)
theorem B2241221 : Blo 1494067 2241221 := bbase (se 4 (by rfl) ⟨210114, by rfl⟩ : syracuseStep 2241221 = 420229) (by norm_num)
theorem B3363533 : Blo 1494067 3363533 := bbase (se 3 (by rfl) ⟨630662, by rfl⟩ : syracuseStep 3363533 = 1261325) (by norm_num)
theorem B5673685 : Blo 1494067 5673685 := bbase (se 7 (by rfl) ⟨66488, by rfl⟩ : syracuseStep 5673685 = 132977) (by norm_num)
theorem B2241245 : Blo 1494067 2241245 := bbase (se 3 (by rfl) ⟨420233, by rfl⟩ : syracuseStep 2241245 = 840467) (by norm_num)
theorem B2241269 : Blo 1494067 2241269 := bbase (se 5 (by rfl) ⟨105059, by rfl⟩ : syracuseStep 2241269 = 210119) (by norm_num)
theorem B2241293 : Blo 1494067 2241293 := bbase (se 3 (by rfl) ⟨420242, by rfl⟩ : syracuseStep 2241293 = 840485) (by norm_num)
theorem B3363605 : Blo 1494067 3363605 := bbase (se 6 (by rfl) ⟨78834, by rfl⟩ : syracuseStep 3363605 = 157669) (by norm_num)
theorem B2241317 : Blo 1494067 2241317 := bbase (se 4 (by rfl) ⟨210123, by rfl⟩ : syracuseStep 2241317 = 420247) (by norm_num)
theorem B6386485 : Blo 1494067 6386485 := bbase (se 5 (by rfl) ⟨299366, by rfl⟩ : syracuseStep 6386485 = 598733) (by norm_num)
theorem B2839349 : Blo 1494067 2839349 := bbase (se 5 (by rfl) ⟨133094, by rfl⟩ : syracuseStep 2839349 = 266189) (by norm_num)
theorem B2241341 : Blo 1494067 2241341 := bbase (se 3 (by rfl) ⟨420251, by rfl⟩ : syracuseStep 2241341 = 840503) (by norm_num)
theorem B2241365 : Blo 1494067 2241365 := bbase (se 9 (by rfl) ⟨6566, by rfl⟩ : syracuseStep 2241365 = 13133) (by norm_num)
theorem B3363677 : Blo 1494067 3363677 := bbase (se 3 (by rfl) ⟨630689, by rfl⟩ : syracuseStep 3363677 = 1261379) (by norm_num)
theorem B3191653 : Blo 1494067 3191653 := bbase (se 4 (by rfl) ⟨299217, by rfl⟩ : syracuseStep 3191653 = 598435) (by norm_num)
theorem B2241389 : Blo 1494067 2241389 := bbase (se 3 (by rfl) ⟨420260, by rfl⟩ : syracuseStep 2241389 = 840521) (by norm_num)
theorem B1618813 : Blo 1494067 1618813 := bbase (se 3 (by rfl) ⟨303527, by rfl⟩ : syracuseStep 1618813 = 607055) (by norm_num)
theorem B2241413 : Blo 1494067 2241413 := bbase (se 4 (by rfl) ⟨210132, by rfl⟩ : syracuseStep 2241413 = 420265) (by norm_num)
theorem B2020237 : Blo 1494067 2020237 := bbase (se 3 (by rfl) ⟨378794, by rfl⟩ : syracuseStep 2020237 = 757589) (by norm_num)
theorem B2241437 : Blo 1494067 2241437 := bbase (se 3 (by rfl) ⟨420269, by rfl⟩ : syracuseStep 2241437 = 840539) (by norm_num)
theorem B3363749 : Blo 1494067 3363749 := bbase (se 4 (by rfl) ⟨315351, by rfl⟩ : syracuseStep 3363749 = 630703) (by norm_num)
theorem B2241461 : Blo 1494067 2241461 := bbase (se 5 (by rfl) ⟨105068, by rfl⟩ : syracuseStep 2241461 = 210137) (by norm_num)
theorem B2241485 : Blo 1494067 2241485 := bbase (se 3 (by rfl) ⟨420278, by rfl⟩ : syracuseStep 2241485 = 840557) (by norm_num)
theorem B2241509 : Blo 1494067 2241509 := bbase (se 4 (by rfl) ⟨210141, by rfl⟩ : syracuseStep 2241509 = 420283) (by norm_num)
theorem B3363821 : Blo 1494067 3363821 := bbase (se 3 (by rfl) ⟨630716, by rfl⟩ : syracuseStep 3363821 = 1261433) (by norm_num)
theorem B2241533 : Blo 1494067 2241533 := bbase (se 3 (by rfl) ⟨420287, by rfl⟩ : syracuseStep 2241533 = 840575) (by norm_num)
theorem B5673989 : Blo 1494067 5673989 := bbase (se 4 (by rfl) ⟨531936, by rfl⟩ : syracuseStep 5673989 = 1063873) (by norm_num)
theorem B5043221 : Blo 1494067 5043221 := bbase (se 6 (by rfl) ⟨118200, by rfl⟩ : syracuseStep 5043221 = 236401) (by norm_num)
theorem B2241557 : Blo 1494067 2241557 := bbase (se 6 (by rfl) ⟨52536, by rfl⟩ : syracuseStep 2241557 = 105073) (by norm_num)
theorem B2241581 : Blo 1494067 2241581 := bbase (se 3 (by rfl) ⟨420296, by rfl⟩ : syracuseStep 2241581 = 840593) (by norm_num)
theorem B3363893 : Blo 1494067 3363893 := bbase (se 5 (by rfl) ⟨157682, by rfl⟩ : syracuseStep 3363893 = 315365) (by norm_num)
theorem B2241605 : Blo 1494067 2241605 := bbase (se 4 (by rfl) ⟨210150, by rfl⟩ : syracuseStep 2241605 = 420301) (by norm_num)
theorem B4256837 : Blo 1494067 4256837 := bbase (se 4 (by rfl) ⟨399078, by rfl⟩ : syracuseStep 4256837 = 798157) (by norm_num)
theorem B2839637 : Blo 1494067 2839637 := bbase (se 8 (by rfl) ⟨16638, by rfl⟩ : syracuseStep 2839637 = 33277) (by norm_num)
theorem B2241629 : Blo 1494067 2241629 := bbase (se 3 (by rfl) ⟨420305, by rfl⟩ : syracuseStep 2241629 = 840611) (by norm_num)
theorem B2241653 : Blo 1494067 2241653 := bbase (se 5 (by rfl) ⟨105077, by rfl⟩ : syracuseStep 2241653 = 210155) (by norm_num)
theorem B5534837 : Blo 1494067 5534837 := bbase (se 5 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 5534837 = 518891) (by norm_num)
theorem B3363965 : Blo 1494067 3363965 := bbase (se 3 (by rfl) ⟨630743, by rfl⟩ : syracuseStep 3363965 = 1261487) (by norm_num)
theorem B3552389 : Blo 1494067 3552389 := bbase (se 4 (by rfl) ⟨333036, by rfl⟩ : syracuseStep 3552389 = 666073) (by norm_num)
theorem B2241677 : Blo 1494067 2241677 := bbase (se 3 (by rfl) ⟨420314, by rfl⟩ : syracuseStep 2241677 = 840629) (by norm_num)
theorem B3740813 : Blo 1494067 3740813 := bbase (se 3 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 3740813 = 1402805) (by norm_num)
theorem B1537165 : Blo 1494067 1537165 := bbase (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) (by norm_num)
theorem B2241701 : Blo 1494067 2241701 := bbase (se 4 (by rfl) ⟨210159, by rfl⟩ : syracuseStep 2241701 = 420319) (by norm_num)
theorem B2241725 : Blo 1494067 2241725 := bbase (se 3 (by rfl) ⟨420323, by rfl⟩ : syracuseStep 2241725 = 840647) (by norm_num)
theorem B7566533 : Blo 1494067 7566533 := bbase (se 4 (by rfl) ⟨709362, by rfl⟩ : syracuseStep 7566533 = 1418725) (by norm_num)
theorem B3364037 : Blo 1494067 3364037 := bbase (se 4 (by rfl) ⟨315378, by rfl⟩ : syracuseStep 3364037 = 630757) (by norm_num)
theorem B2241749 : Blo 1494067 2241749 := bbase (se 7 (by rfl) ⟨26270, by rfl⟩ : syracuseStep 2241749 = 52541) (by norm_num)
theorem B2241773 : Blo 1494067 2241773 := bbase (se 3 (by rfl) ⟨420332, by rfl⟩ : syracuseStep 2241773 = 840665) (by norm_num)
theorem B2839789 : Blo 1494067 2839789 := bbase (se 3 (by rfl) ⟨532460, by rfl⟩ : syracuseStep 2839789 = 1064921) (by norm_num)
theorem B2241797 : Blo 1494067 2241797 := bbase (se 4 (by rfl) ⟨210168, by rfl⟩ : syracuseStep 2241797 = 420337) (by norm_num)
theorem B3364109 : Blo 1494067 3364109 := bbase (se 3 (by rfl) ⟨630770, by rfl⟩ : syracuseStep 3364109 = 1261541) (by norm_num)
theorem B2241821 : Blo 1494067 2241821 := bbase (se 3 (by rfl) ⟨420341, by rfl⟩ : syracuseStep 2241821 = 840683) (by norm_num)
theorem B2241845 : Blo 1494067 2241845 := bbase (se 5 (by rfl) ⟨105086, by rfl⟩ : syracuseStep 2241845 = 210173) (by norm_num)
theorem B2241869 : Blo 1494067 2241869 := bbase (se 3 (by rfl) ⟨420350, by rfl⟩ : syracuseStep 2241869 = 840701) (by norm_num)
theorem B3192149 : Blo 1494067 3192149 := bbase (se 13 (by rfl) ⟨584, by rfl⟩ : syracuseStep 3192149 = 1169) (by norm_num)
theorem B3364181 : Blo 1494067 3364181 := bbase (se 17 (by rfl) ⟨38, by rfl⟩ : syracuseStep 3364181 = 77) (by norm_num)
theorem B2241893 : Blo 1494067 2241893 := bbase (se 4 (by rfl) ⟨210177, by rfl⟩ : syracuseStep 2241893 = 420355) (by norm_num)
theorem B4789621 : Blo 1494067 4789621 := bbase (se 5 (by rfl) ⟨224513, by rfl⟩ : syracuseStep 4789621 = 449027) (by norm_num)
theorem B2241917 : Blo 1494067 2241917 := bbase (se 3 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 2241917 = 840719) (by norm_num)
theorem B2241941 : Blo 1494067 2241941 := bbase (se 6 (by rfl) ⟨52545, by rfl⟩ : syracuseStep 2241941 = 105091) (by norm_num)
theorem B3364253 : Blo 1494067 3364253 := bbase (se 3 (by rfl) ⟨630797, by rfl⟩ : syracuseStep 3364253 = 1261595) (by norm_num)
theorem B2241965 : Blo 1494067 2241965 := bbase (se 3 (by rfl) ⟨420368, by rfl⟩ : syracuseStep 2241965 = 840737) (by norm_num)
theorem B4789685 : Blo 1494067 4789685 := bbase (se 5 (by rfl) ⟨224516, by rfl⟩ : syracuseStep 4789685 = 449033) (by norm_num)
theorem B5043653 : Blo 1494067 5043653 := bbase (se 4 (by rfl) ⟨472842, by rfl⟩ : syracuseStep 5043653 = 945685) (by norm_num)
theorem B2241989 : Blo 1494067 2241989 := bbase (se 4 (by rfl) ⟨210186, by rfl⟩ : syracuseStep 2241989 = 420373) (by norm_num)
theorem B2127325 : Blo 1494067 2127325 := bbase (se 3 (by rfl) ⟨398873, by rfl⟩ : syracuseStep 2127325 = 797747) (by norm_num)
theorem B2242013 : Blo 1494067 2242013 := bbase (se 3 (by rfl) ⟨420377, by rfl⟩ : syracuseStep 2242013 = 840755) (by norm_num)
theorem B3364325 : Blo 1494067 3364325 := bbase (se 4 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 3364325 = 630811) (by norm_num)
theorem B2242037 : Blo 1494067 2242037 := bbase (se 5 (by rfl) ⟨105095, by rfl⟩ : syracuseStep 2242037 = 210191) (by norm_num)
theorem B4257269 : Blo 1494067 4257269 := bbase (se 5 (by rfl) ⟨199559, by rfl⟩ : syracuseStep 4257269 = 399119) (by norm_num)
theorem B2242061 : Blo 1494067 2242061 := bbase (se 3 (by rfl) ⟨420386, by rfl⟩ : syracuseStep 2242061 = 840773) (by norm_num)
theorem B3782173 : Blo 1494067 3782173 := bbase (se 3 (by rfl) ⟨709157, by rfl⟩ : syracuseStep 3782173 = 1418315) (by norm_num)
theorem B2840093 : Blo 1494067 2840093 := bbase (se 3 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 2840093 = 1065035) (by norm_num)
theorem B2242085 : Blo 1494067 2242085 := bbase (se 4 (by rfl) ⟨210195, by rfl⟩ : syracuseStep 2242085 = 420391) (by norm_num)
theorem B3364397 : Blo 1494067 3364397 := bbase (se 3 (by rfl) ⟨630824, by rfl⟩ : syracuseStep 3364397 = 1261649) (by norm_num)
theorem B2242109 : Blo 1494067 2242109 := bbase (se 3 (by rfl) ⟨420395, by rfl⟩ : syracuseStep 2242109 = 840791) (by norm_num)
theorem B2692685 : Blo 1494067 2692685 := bbase (se 3 (by rfl) ⟨504878, by rfl⟩ : syracuseStep 2692685 = 1009757) (by norm_num)
theorem B2242133 : Blo 1494067 2242133 := bbase (se 8 (by rfl) ⟨13137, by rfl⟩ : syracuseStep 2242133 = 26275) (by norm_num)
theorem B2242157 : Blo 1494067 2242157 := bbase (se 3 (by rfl) ⟨420404, by rfl⟩ : syracuseStep 2242157 = 840809) (by norm_num)
theorem B3642989 : Blo 1494067 3642989 := bbase (se 3 (by rfl) ⟨683060, by rfl⟩ : syracuseStep 3642989 = 1366121) (by norm_num)
theorem B3364469 : Blo 1494067 3364469 := bbase (se 5 (by rfl) ⟨157709, by rfl⟩ : syracuseStep 3364469 = 315419) (by norm_num)
theorem B12949109 : Blo 1494067 12949109 := bbase (se 5 (by rfl) ⟨606989, by rfl⟩ : syracuseStep 12949109 = 1213979) (by norm_num)
theorem B2242181 : Blo 1494067 2242181 := bbase (se 4 (by rfl) ⟨210204, by rfl⟩ : syracuseStep 2242181 = 420409) (by norm_num)
theorem B3782285 : Blo 1494067 3782285 := bbase (se 3 (by rfl) ⟨709178, by rfl⟩ : syracuseStep 3782285 = 1418357) (by norm_num)
theorem B2242205 : Blo 1494067 2242205 := bbase (se 3 (by rfl) ⟨420413, by rfl⟩ : syracuseStep 2242205 = 840827) (by norm_num)
theorem B2127541 : Blo 1494067 2127541 := bbase (se 5 (by rfl) ⟨99728, by rfl⟩ : syracuseStep 2127541 = 199457) (by norm_num)
theorem B2242229 : Blo 1494067 2242229 := bbase (se 5 (by rfl) ⟨105104, by rfl⟩ : syracuseStep 2242229 = 210209) (by norm_num)
theorem B3364541 : Blo 1494067 3364541 := bbase (se 3 (by rfl) ⟨630851, by rfl⟩ : syracuseStep 3364541 = 1261703) (by norm_num)
theorem B2242253 : Blo 1494067 2242253 := bbase (se 3 (by rfl) ⟨420422, by rfl⟩ : syracuseStep 2242253 = 840845) (by norm_num)
theorem B2242277 : Blo 1494067 2242277 := bbase (se 4 (by rfl) ⟨210213, by rfl⟩ : syracuseStep 2242277 = 420427) (by norm_num)
theorem B2242301 : Blo 1494067 2242301 := bbase (se 3 (by rfl) ⟨420431, by rfl⟩ : syracuseStep 2242301 = 840863) (by norm_num)
theorem B3364613 : Blo 1494067 3364613 := bbase (se 4 (by rfl) ⟨315432, by rfl⟩ : syracuseStep 3364613 = 630865) (by norm_num)
theorem B2242325 : Blo 1494067 2242325 := bbase (se 6 (by rfl) ⟨52554, by rfl⟩ : syracuseStep 2242325 = 105109) (by norm_num)
theorem B2242349 : Blo 1494067 2242349 := bbase (se 3 (by rfl) ⟨420440, by rfl⟩ : syracuseStep 2242349 = 840881) (by norm_num)
theorem B2242373 : Blo 1494067 2242373 := bbase (se 4 (by rfl) ⟨210222, by rfl⟩ : syracuseStep 2242373 = 420445) (by norm_num)
theorem B3782477 : Blo 1494067 3782477 := bbase (se 3 (by rfl) ⟨709214, by rfl⟩ : syracuseStep 3782477 = 1418429) (by norm_num)
theorem B3364685 : Blo 1494067 3364685 := bbase (se 3 (by rfl) ⟨630878, by rfl⟩ : syracuseStep 3364685 = 1261757) (by norm_num)
theorem B3594061 : Blo 1494067 3594061 := bbase (se 3 (by rfl) ⟨673886, by rfl⟩ : syracuseStep 3594061 = 1347773) (by norm_num)
theorem B14374741 : Blo 1494067 14374741 := bbase (se 9 (by rfl) ⟨42113, by rfl⟩ : syracuseStep 14374741 = 84227) (by norm_num)
theorem B2242397 : Blo 1494067 2242397 := bbase (se 3 (by rfl) ⟨420449, by rfl⟩ : syracuseStep 2242397 = 840899) (by norm_num)
theorem B5044085 : Blo 1494067 5044085 := bbase (se 5 (by rfl) ⟨236441, by rfl⟩ : syracuseStep 5044085 = 472883) (by norm_num)
theorem B2242421 : Blo 1494067 2242421 := bbase (se 5 (by rfl) ⟨105113, by rfl⟩ : syracuseStep 2242421 = 210227) (by norm_num)
theorem B2242445 : Blo 1494067 2242445 := bbase (se 3 (by rfl) ⟨420458, by rfl⟩ : syracuseStep 2242445 = 840917) (by norm_num)
theorem B18184085 : Blo 1494067 18184085 := bbase (se 6 (by rfl) ⟨426189, by rfl⟩ : syracuseStep 18184085 = 852379) (by norm_num)
theorem B3364757 : Blo 1494067 3364757 := bbase (se 6 (by rfl) ⟨78861, by rfl⟩ : syracuseStep 3364757 = 157723) (by norm_num)
theorem B2242469 : Blo 1494067 2242469 := bbase (se 4 (by rfl) ⟨210231, by rfl⟩ : syracuseStep 2242469 = 420463) (by norm_num)
theorem B2242493 : Blo 1494067 2242493 := bbase (se 3 (by rfl) ⟨420467, by rfl⟩ : syracuseStep 2242493 = 840935) (by norm_num)
theorem B2242517 : Blo 1494067 2242517 := bbase (se 7 (by rfl) ⟨26279, by rfl⟩ : syracuseStep 2242517 = 52559) (by norm_num)
theorem B59062229 : Blo 1494067 59062229 := bbase (se 7 (by rfl) ⟨692135, by rfl⟩ : syracuseStep 59062229 = 1384271) (by norm_num)
theorem B3364829 : Blo 1494067 3364829 := bbase (se 3 (by rfl) ⟨630905, by rfl⟩ : syracuseStep 3364829 = 1261811) (by norm_num)
theorem B2021341 : Blo 1494067 2021341 := bbase (se 3 (by rfl) ⟨379001, by rfl⟩ : syracuseStep 2021341 = 758003) (by norm_num)
theorem B2242541 : Blo 1494067 2242541 := bbase (se 3 (by rfl) ⟨420476, by rfl⟩ : syracuseStep 2242541 = 840953) (by norm_num)
theorem B2242565 : Blo 1494067 2242565 := bbase (se 4 (by rfl) ⟨210240, by rfl⟩ : syracuseStep 2242565 = 420481) (by norm_num)
theorem B2242589 : Blo 1494067 2242589 := bbase (se 3 (by rfl) ⟨420485, by rfl⟩ : syracuseStep 2242589 = 840971) (by norm_num)
theorem B3364901 : Blo 1494067 3364901 := bbase (se 4 (by rfl) ⟨315459, by rfl⟩ : syracuseStep 3364901 = 630919) (by norm_num)
theorem B2127917 : Blo 1494067 2127917 := bbase (se 3 (by rfl) ⟨398984, by rfl⟩ : syracuseStep 2127917 = 797969) (by norm_num)
theorem B2242613 : Blo 1494067 2242613 := bbase (se 5 (by rfl) ⟨105122, by rfl⟩ : syracuseStep 2242613 = 210245) (by norm_num)
theorem B2242637 : Blo 1494067 2242637 := bbase (se 3 (by rfl) ⟨420494, by rfl⟩ : syracuseStep 2242637 = 840989) (by norm_num)
theorem B1595485 : Blo 1494067 1595485 := bbase (se 3 (by rfl) ⟨299153, by rfl⟩ : syracuseStep 1595485 = 598307) (by norm_num)
theorem B2242661 : Blo 1494067 2242661 := bbase (se 4 (by rfl) ⟨210249, by rfl⟩ : syracuseStep 2242661 = 420499) (by norm_num)
theorem B3364973 : Blo 1494067 3364973 := bbase (se 3 (by rfl) ⟨630932, by rfl⟩ : syracuseStep 3364973 = 1261865) (by norm_num)
theorem B2242685 : Blo 1494067 2242685 := bbase (se 3 (by rfl) ⟨420503, by rfl⟩ : syracuseStep 2242685 = 841007) (by norm_num)
theorem B5462149 : Blo 1494067 5462149 := bbase (se 4 (by rfl) ⟨512076, by rfl⟩ : syracuseStep 5462149 = 1024153) (by norm_num)
theorem B2242709 : Blo 1494067 2242709 := bbase (se 6 (by rfl) ⟨52563, by rfl⟩ : syracuseStep 2242709 = 105127) (by norm_num)
theorem B2521253 : Blo 1494067 2521253 := bbase (se 4 (by rfl) ⟨236367, by rfl⟩ : syracuseStep 2521253 = 472735) (by norm_num)
theorem B3782821 : Blo 1494067 3782821 := bbase (se 4 (by rfl) ⟨354639, by rfl⟩ : syracuseStep 3782821 = 709279) (by norm_num)
theorem B2242733 : Blo 1494067 2242733 := bbase (se 3 (by rfl) ⟨420512, by rfl⟩ : syracuseStep 2242733 = 841025) (by norm_num)
theorem B3193013 : Blo 1494067 3193013 := bbase (se 5 (by rfl) ⟨149672, by rfl⟩ : syracuseStep 3193013 = 299345) (by norm_num)
theorem B3365045 : Blo 1494067 3365045 := bbase (se 5 (by rfl) ⟨157736, by rfl⟩ : syracuseStep 3365045 = 315473) (by norm_num)
theorem B2242757 : Blo 1494067 2242757 := bbase (se 4 (by rfl) ⟨210258, by rfl⟩ : syracuseStep 2242757 = 420517) (by norm_num)
theorem B2242781 : Blo 1494067 2242781 := bbase (se 3 (by rfl) ⟨420521, by rfl⟩ : syracuseStep 2242781 = 841043) (by norm_num)
theorem B4258021 : Blo 1494067 4258021 := bbase (se 4 (by rfl) ⟨399189, by rfl⟩ : syracuseStep 4258021 = 798379) (by norm_num)
theorem B2242805 : Blo 1494067 2242805 := bbase (se 5 (by rfl) ⟨105131, by rfl⟩ : syracuseStep 2242805 = 210263) (by norm_num)
theorem B2021621 : Blo 1494067 2021621 := bbase (se 5 (by rfl) ⟨94763, by rfl⟩ : syracuseStep 2021621 = 189527) (by norm_num)
theorem B3365117 : Blo 1494067 3365117 := bbase (se 3 (by rfl) ⟨630959, by rfl⟩ : syracuseStep 3365117 = 1261919) (by norm_num)
theorem B2242829 : Blo 1494067 2242829 := bbase (se 3 (by rfl) ⟨420530, by rfl⟩ : syracuseStep 2242829 = 841061) (by norm_num)
theorem B3782933 : Blo 1494067 3782933 := bbase (se 6 (by rfl) ⟨88662, by rfl⟩ : syracuseStep 3782933 = 177325) (by norm_num)
theorem B2521381 : Blo 1494067 2521381 := bbase (se 4 (by rfl) ⟨236379, by rfl⟩ : syracuseStep 2521381 = 472759) (by norm_num)
theorem B5044517 : Blo 1494067 5044517 := bbase (se 4 (by rfl) ⟨472923, by rfl⟩ : syracuseStep 5044517 = 945847) (by norm_num)
theorem B2242853 : Blo 1494067 2242853 := bbase (se 4 (by rfl) ⟨210267, by rfl⟩ : syracuseStep 2242853 = 420535) (by norm_num)
theorem B2242877 : Blo 1494067 2242877 := bbase (se 3 (by rfl) ⟨420539, by rfl⟩ : syracuseStep 2242877 = 841079) (by norm_num)
theorem B3193157 : Blo 1494067 3193157 := bbase (se 4 (by rfl) ⟨299358, by rfl⟩ : syracuseStep 3193157 = 598717) (by norm_num)
theorem B3365189 : Blo 1494067 3365189 := bbase (se 4 (by rfl) ⟨315486, by rfl⟩ : syracuseStep 3365189 = 630973) (by norm_num)
theorem B2242901 : Blo 1494067 2242901 := bbase (se 10 (by rfl) ⟨3285, by rfl⟩ : syracuseStep 2242901 = 6571) (by norm_num)
theorem B2693477 : Blo 1494067 2693477 := bbase (se 4 (by rfl) ⟨252513, by rfl⟩ : syracuseStep 2693477 = 505027) (by norm_num)
theorem B2242925 : Blo 1494067 2242925 := bbase (se 3 (by rfl) ⟨420548, by rfl⟩ : syracuseStep 2242925 = 841097) (by norm_num)
theorem B2521469 : Blo 1494067 2521469 := bbase (se 3 (by rfl) ⟨472775, by rfl⟩ : syracuseStep 2521469 = 945551) (by norm_num)
theorem B2242949 : Blo 1494067 2242949 := bbase (se 4 (by rfl) ⟨210276, by rfl⟩ : syracuseStep 2242949 = 420553) (by norm_num)
theorem B3365261 : Blo 1494067 3365261 := bbase (se 3 (by rfl) ⟨630986, by rfl⟩ : syracuseStep 3365261 = 1261973) (by norm_num)
theorem B21543317 : Blo 1494067 21543317 := bbase (se 6 (by rfl) ⟨504921, by rfl⟩ : syracuseStep 21543317 = 1009843) (by norm_num)
theorem B2242973 : Blo 1494067 2242973 := bbase (se 3 (by rfl) ⟨420557, by rfl⟩ : syracuseStep 2242973 = 841115) (by norm_num)
theorem B2242997 : Blo 1494067 2242997 := bbase (se 5 (by rfl) ⟨105140, by rfl⟩ : syracuseStep 2242997 = 210281) (by norm_num)
theorem B2243021 : Blo 1494067 2243021 := bbase (se 3 (by rfl) ⟨420566, by rfl⟩ : syracuseStep 2243021 = 841133) (by norm_num)
theorem B1595857 : Blo 1494067 1595857 := bbase (se 2 (by rfl) ⟨598446, by rfl⟩ : syracuseStep 1595857 = 1196893) (by norm_num)
theorem B3783125 : Blo 1494067 3783125 := bbase (se 7 (by rfl) ⟨44333, by rfl⟩ : syracuseStep 3783125 = 88667) (by norm_num)
theorem B7567829 : Blo 1494067 7567829 := bbase (se 7 (by rfl) ⟨88685, by rfl⟩ : syracuseStep 7567829 = 177371) (by norm_num)
theorem B3365333 : Blo 1494067 3365333 := bbase (se 7 (by rfl) ⟨39437, by rfl⟩ : syracuseStep 3365333 = 78875) (by norm_num)
theorem B3791333 : Blo 1494067 3791333 := bbase (se 4 (by rfl) ⟨355437, by rfl⟩ : syracuseStep 3791333 = 710875) (by norm_num)
theorem B2243045 : Blo 1494067 2243045 := bbase (se 4 (by rfl) ⟨210285, by rfl⟩ : syracuseStep 2243045 = 420571) (by norm_num)
theorem B2693621 : Blo 1494067 2693621 := bbase (se 5 (by rfl) ⟨126263, by rfl⟩ : syracuseStep 2693621 = 252527) (by norm_num)
theorem B2521597 : Blo 1494067 2521597 := bbase (se 3 (by rfl) ⟨472799, by rfl⟩ : syracuseStep 2521597 = 945599) (by norm_num)
theorem B2243069 : Blo 1494067 2243069 := bbase (se 3 (by rfl) ⟨420575, by rfl⟩ : syracuseStep 2243069 = 841151) (by norm_num)
theorem B2243093 : Blo 1494067 2243093 := bbase (se 6 (by rfl) ⟨52572, by rfl⟩ : syracuseStep 2243093 = 105145) (by norm_num)
theorem B3365405 : Blo 1494067 3365405 := bbase (se 3 (by rfl) ⟨631013, by rfl⟩ : syracuseStep 3365405 = 1262027) (by norm_num)
theorem B1497637 : Blo 1494067 1497637 := bbase (se 4 (by rfl) ⟨140403, by rfl⟩ : syracuseStep 1497637 = 280807) (by norm_num)
theorem B2243117 : Blo 1494067 2243117 := bbase (se 3 (by rfl) ⟨420584, by rfl⟩ : syracuseStep 2243117 = 841169) (by norm_num)
theorem B2243141 : Blo 1494067 2243141 := bbase (se 4 (by rfl) ⟨210294, by rfl⟩ : syracuseStep 2243141 = 420589) (by norm_num)
theorem B2521685 : Blo 1494067 2521685 := bbase (se 8 (by rfl) ⟨14775, by rfl⟩ : syracuseStep 2521685 = 29551) (by norm_num)
theorem B8518229 : Blo 1494067 8518229 := bbase (se 8 (by rfl) ⟨49911, by rfl⟩ : syracuseStep 8518229 = 99823) (by norm_num)
theorem B2243165 : Blo 1494067 2243165 := bbase (se 3 (by rfl) ⟨420593, by rfl⟩ : syracuseStep 2243165 = 841187) (by norm_num)
theorem B3365477 : Blo 1494067 3365477 := bbase (se 4 (by rfl) ⟨315513, by rfl⟩ : syracuseStep 3365477 = 631027) (by norm_num)
theorem B2243189 : Blo 1494067 2243189 := bbase (se 5 (by rfl) ⟨105149, by rfl⟩ : syracuseStep 2243189 = 210299) (by norm_num)
theorem B2243213 : Blo 1494067 2243213 := bbase (se 3 (by rfl) ⟨420602, by rfl⟩ : syracuseStep 2243213 = 841205) (by norm_num)
theorem B1890965 : Blo 1494067 1890965 := bbase (se 6 (by rfl) ⟨44319, by rfl⟩ : syracuseStep 1890965 = 88639) (by norm_num)
theorem B2243237 : Blo 1494067 2243237 := bbase (se 4 (by rfl) ⟨210303, by rfl⟩ : syracuseStep 2243237 = 420607) (by norm_num)
theorem B7674533 : Blo 1494067 7674533 := bbase (se 4 (by rfl) ⟨719487, by rfl⟩ : syracuseStep 7674533 = 1438975) (by norm_num)
theorem B3365549 : Blo 1494067 3365549 := bbase (se 3 (by rfl) ⟨631040, by rfl⟩ : syracuseStep 3365549 = 1262081) (by norm_num)
theorem B2243261 : Blo 1494067 2243261 := bbase (se 3 (by rfl) ⟨420611, by rfl⟩ : syracuseStep 2243261 = 841223) (by norm_num)
theorem B1891021 : Blo 1494067 1891021 := bbase (se 3 (by rfl) ⟨354566, by rfl⟩ : syracuseStep 1891021 = 709133) (by norm_num)
theorem B2521813 : Blo 1494067 2521813 := bbase (se 7 (by rfl) ⟨29552, by rfl⟩ : syracuseStep 2521813 = 59105) (by norm_num)
theorem B5044949 : Blo 1494067 5044949 := bbase (se 7 (by rfl) ⟨59120, by rfl⟩ : syracuseStep 5044949 = 118241) (by norm_num)
theorem B2243285 : Blo 1494067 2243285 := bbase (se 7 (by rfl) ⟨26288, by rfl⟩ : syracuseStep 2243285 = 52577) (by norm_num)
theorem B2243309 : Blo 1494067 2243309 := bbase (se 3 (by rfl) ⟨420620, by rfl⟩ : syracuseStep 2243309 = 841241) (by norm_num)
theorem B3365621 : Blo 1494067 3365621 := bbase (se 5 (by rfl) ⟨157763, by rfl⟩ : syracuseStep 3365621 = 315527) (by norm_num)
theorem B2243333 : Blo 1494067 2243333 := bbase (se 4 (by rfl) ⟨210312, by rfl⟩ : syracuseStep 2243333 = 420625) (by norm_num)
theorem B2243357 : Blo 1494067 2243357 := bbase (se 3 (by rfl) ⟨420629, by rfl⟩ : syracuseStep 2243357 = 841259) (by norm_num)
theorem B1891117 : Blo 1494067 1891117 := bbase (se 3 (by rfl) ⟨354584, by rfl⟩ : syracuseStep 1891117 = 709169) (by norm_num)
theorem B2521901 : Blo 1494067 2521901 := bbase (se 3 (by rfl) ⟨472856, by rfl⟩ : syracuseStep 2521901 = 945713) (by norm_num)
theorem B3783469 : Blo 1494067 3783469 := bbase (se 3 (by rfl) ⟨709400, by rfl⟩ : syracuseStep 3783469 = 1418801) (by norm_num)
theorem B2243381 : Blo 1494067 2243381 := bbase (se 5 (by rfl) ⟨105158, by rfl⟩ : syracuseStep 2243381 = 210317) (by norm_num)
theorem B3365693 : Blo 1494067 3365693 := bbase (se 3 (by rfl) ⟨631067, by rfl⟩ : syracuseStep 3365693 = 1262135) (by norm_num)
theorem B1596233 : Blo 1494067 1596233 := bbase (se 2 (by rfl) ⟨598587, by rfl⟩ : syracuseStep 1596233 = 1197175) (by norm_num)
theorem B2243405 : Blo 1494067 2243405 := bbase (se 3 (by rfl) ⟨420638, by rfl⟩ : syracuseStep 2243405 = 841277) (by norm_num)
theorem B2243429 : Blo 1494067 2243429 := bbase (se 4 (by rfl) ⟨210321, by rfl⟩ : syracuseStep 2243429 = 420643) (by norm_num)
theorem B2243453 : Blo 1494067 2243453 := bbase (se 3 (by rfl) ⟨420647, by rfl⟩ : syracuseStep 2243453 = 841295) (by norm_num)
theorem B3365765 : Blo 1494067 3365765 := bbase (se 4 (by rfl) ⟨315540, by rfl⟩ : syracuseStep 3365765 = 631081) (by norm_num)
theorem B1596305 : Blo 1494067 1596305 := bbase (se 2 (by rfl) ⟨598614, by rfl⟩ : syracuseStep 1596305 = 1197229) (by norm_num)
theorem B2243477 : Blo 1494067 2243477 := bbase (se 6 (by rfl) ⟨52581, by rfl⟩ : syracuseStep 2243477 = 105163) (by norm_num)
theorem B3783581 : Blo 1494067 3783581 := bbase (se 3 (by rfl) ⟨709421, by rfl⟩ : syracuseStep 3783581 = 1418843) (by norm_num)
theorem B2522029 : Blo 1494067 2522029 := bbase (se 3 (by rfl) ⟨472880, by rfl⟩ : syracuseStep 2522029 = 945761) (by norm_num)
theorem B2243501 : Blo 1494067 2243501 := bbase (se 3 (by rfl) ⟨420656, by rfl⟩ : syracuseStep 2243501 = 841313) (by norm_num)
theorem B2243525 : Blo 1494067 2243525 := bbase (se 4 (by rfl) ⟨210330, by rfl⟩ : syracuseStep 2243525 = 420661) (by norm_num)
theorem B3365837 : Blo 1494067 3365837 := bbase (se 3 (by rfl) ⟨631094, by rfl⟩ : syracuseStep 3365837 = 1262189) (by norm_num)
theorem B1891289 : Blo 1494067 1891289 := bbase (se 2 (by rfl) ⟨709233, by rfl⟩ : syracuseStep 1891289 = 1418467) (by norm_num)
theorem B2243549 : Blo 1494067 2243549 := bbase (se 3 (by rfl) ⟨420665, by rfl⟩ : syracuseStep 2243549 = 841331) (by norm_num)
theorem B2243573 : Blo 1494067 2243573 := bbase (se 5 (by rfl) ⟨105167, by rfl⟩ : syracuseStep 2243573 = 210335) (by norm_num)
theorem B2522117 : Blo 1494067 2522117 := bbase (se 4 (by rfl) ⟨236448, by rfl⟩ : syracuseStep 2522117 = 472897) (by norm_num)
theorem B2243597 : Blo 1494067 2243597 := bbase (se 3 (by rfl) ⟨420674, by rfl⟩ : syracuseStep 2243597 = 841349) (by norm_num)
theorem B1891345 : Blo 1494067 1891345 := bbase (se 2 (by rfl) ⟨709254, by rfl⟩ : syracuseStep 1891345 = 1418509) (by norm_num)
theorem B3365909 : Blo 1494067 3365909 := bbase (se 6 (by rfl) ⟨78888, by rfl⟩ : syracuseStep 3365909 = 157777) (by norm_num)
theorem B2243621 : Blo 1494067 2243621 := bbase (se 4 (by rfl) ⟨210339, by rfl⟩ : syracuseStep 2243621 = 420679) (by norm_num)
theorem B3193901 : Blo 1494067 3193901 := bbase (se 3 (by rfl) ⟨598856, by rfl⟩ : syracuseStep 3193901 = 1197713) (by norm_num)
theorem B2243645 : Blo 1494067 2243645 := bbase (se 3 (by rfl) ⟨420683, by rfl⟩ : syracuseStep 2243645 = 841367) (by norm_num)
theorem B5676101 : Blo 1494067 5676101 := bbase (se 4 (by rfl) ⟨532134, by rfl⟩ : syracuseStep 5676101 = 1064269) (by norm_num)
theorem B1596493 : Blo 1494067 1596493 := bbase (se 3 (by rfl) ⟨299342, by rfl⟩ : syracuseStep 1596493 = 598685) (by norm_num)
theorem B2243669 : Blo 1494067 2243669 := bbase (se 8 (by rfl) ⟨13146, by rfl⟩ : syracuseStep 2243669 = 26293) (by norm_num)
theorem B3783773 : Blo 1494067 3783773 := bbase (se 3 (by rfl) ⟨709457, by rfl⟩ : syracuseStep 3783773 = 1418915) (by norm_num)
theorem B3365981 : Blo 1494067 3365981 := bbase (se 3 (by rfl) ⟨631121, by rfl⟩ : syracuseStep 3365981 = 1262243) (by norm_num)
theorem B2104421 : Blo 1494067 2104421 := bbase (se 4 (by rfl) ⟨197289, by rfl⟩ : syracuseStep 2104421 = 394579) (by norm_num)
theorem B2243693 : Blo 1494067 2243693 := bbase (se 3 (by rfl) ⟨420692, by rfl⟩ : syracuseStep 2243693 = 841385) (by norm_num)
theorem B1891441 : Blo 1494067 1891441 := bbase (se 2 (by rfl) ⟨709290, by rfl⟩ : syracuseStep 1891441 = 1418581) (by norm_num)
theorem B3939445 : Blo 1494067 3939445 := bbase (se 5 (by rfl) ⟨184661, by rfl⟩ : syracuseStep 3939445 = 369323) (by norm_num)
theorem B2522245 : Blo 1494067 2522245 := bbase (se 4 (by rfl) ⟨236460, by rfl⟩ : syracuseStep 2522245 = 472921) (by norm_num)
theorem B5045381 : Blo 1494067 5045381 := bbase (se 4 (by rfl) ⟨473004, by rfl⟩ : syracuseStep 5045381 = 946009) (by norm_num)
theorem B2243717 : Blo 1494067 2243717 := bbase (se 4 (by rfl) ⟨210348, by rfl⟩ : syracuseStep 2243717 = 420697) (by norm_num)
theorem B2243741 : Blo 1494067 2243741 := bbase (se 3 (by rfl) ⟨420701, by rfl⟩ : syracuseStep 2243741 = 841403) (by norm_num)
theorem B3366053 : Blo 1494067 3366053 := bbase (se 4 (by rfl) ⟨315567, by rfl⟩ : syracuseStep 3366053 = 631135) (by norm_num)
theorem B2243765 : Blo 1494067 2243765 := bbase (se 5 (by rfl) ⟨105176, by rfl⟩ : syracuseStep 2243765 = 210353) (by norm_num)
theorem B2243789 : Blo 1494067 2243789 := bbase (se 3 (by rfl) ⟨420710, by rfl⟩ : syracuseStep 2243789 = 841421) (by norm_num)
theorem B9583829 : Blo 1494067 9583829 := bbase (se 7 (by rfl) ⟨112310, by rfl⟩ : syracuseStep 9583829 = 224621) (by norm_num)
theorem B2522333 : Blo 1494067 2522333 := bbase (se 3 (by rfl) ⟨472937, by rfl⟩ : syracuseStep 2522333 = 945875) (by norm_num)
theorem B2243813 : Blo 1494067 2243813 := bbase (se 4 (by rfl) ⟨210357, by rfl⟩ : syracuseStep 2243813 = 420715) (by norm_num)
theorem B3366125 : Blo 1494067 3366125 := bbase (se 3 (by rfl) ⟨631148, by rfl⟩ : syracuseStep 3366125 = 1262297) (by norm_num)
theorem B2243837 : Blo 1494067 2243837 := bbase (se 3 (by rfl) ⟨420719, by rfl⟩ : syracuseStep 2243837 = 841439) (by norm_num)
theorem B1596677 : Blo 1494067 1596677 := bbase (se 4 (by rfl) ⟨149688, by rfl⟩ : syracuseStep 1596677 = 299377) (by norm_num)
theorem B2243861 : Blo 1494067 2243861 := bbase (se 6 (by rfl) ⟨52590, by rfl⟩ : syracuseStep 2243861 = 105181) (by norm_num)
theorem B1891613 : Blo 1494067 1891613 := bbase (se 3 (by rfl) ⟨354677, by rfl⟩ : syracuseStep 1891613 = 709355) (by norm_num)
theorem B2243885 : Blo 1494067 2243885 := bbase (se 3 (by rfl) ⟨420728, by rfl⟩ : syracuseStep 2243885 = 841457) (by norm_num)
theorem B2243909 : Blo 1494067 2243909 := bbase (se 4 (by rfl) ⟨210366, by rfl⟩ : syracuseStep 2243909 = 420733) (by norm_num)
theorem B1891669 : Blo 1494067 1891669 := bbase (se 11 (by rfl) ⟨1385, by rfl⟩ : syracuseStep 1891669 = 2771) (by norm_num)
theorem B4545877 : Blo 1494067 4545877 := bbase (se 11 (by rfl) ⟨3329, by rfl⟩ : syracuseStep 4545877 = 6659) (by norm_num)
theorem B2522461 : Blo 1494067 2522461 := bbase (se 3 (by rfl) ⟨472961, by rfl⟩ : syracuseStep 2522461 = 945923) (by norm_num)
theorem B2243933 : Blo 1494067 2243933 := bbase (se 3 (by rfl) ⟨420737, by rfl⟩ : syracuseStep 2243933 = 841475) (by norm_num)
theorem B5676389 : Blo 1494067 5676389 := bbase (se 4 (by rfl) ⟨532161, by rfl⟩ : syracuseStep 5676389 = 1064323) (by norm_num)
theorem B2243957 : Blo 1494067 2243957 := bbase (se 5 (by rfl) ⟨105185, by rfl⟩ : syracuseStep 2243957 = 210371) (by norm_num)
theorem B2243981 : Blo 1494067 2243981 := bbase (se 3 (by rfl) ⟨420746, by rfl⟩ : syracuseStep 2243981 = 841493) (by norm_num)
theorem B2244005 : Blo 1494067 2244005 := bbase (se 4 (by rfl) ⟨210375, by rfl⟩ : syracuseStep 2244005 = 420751) (by norm_num)
theorem B1891765 : Blo 1494067 1891765 := bbase (se 5 (by rfl) ⟨88676, by rfl⟩ : syracuseStep 1891765 = 177353) (by norm_num)
theorem B2522549 : Blo 1494067 2522549 := bbase (se 5 (by rfl) ⟨118244, by rfl⟩ : syracuseStep 2522549 = 236489) (by norm_num)
theorem B3784117 : Blo 1494067 3784117 := bbase (se 5 (by rfl) ⟨177380, by rfl⟩ : syracuseStep 3784117 = 354761) (by norm_num)
theorem B2129341 : Blo 1494067 2129341 := bbase (se 3 (by rfl) ⟨399251, by rfl⟩ : syracuseStep 2129341 = 798503) (by norm_num)
theorem B2244029 : Blo 1494067 2244029 := bbase (se 3 (by rfl) ⟨420755, by rfl⟩ : syracuseStep 2244029 = 841511) (by norm_num)
theorem B2244053 : Blo 1494067 2244053 := bbase (se 7 (by rfl) ⟨26297, by rfl⟩ : syracuseStep 2244053 = 52595) (by norm_num)
theorem B2244077 : Blo 1494067 2244077 := bbase (se 3 (by rfl) ⟨420764, by rfl⟩ : syracuseStep 2244077 = 841529) (by norm_num)
theorem B2244101 : Blo 1494067 2244101 := bbase (se 4 (by rfl) ⟨210384, by rfl⟩ : syracuseStep 2244101 = 420769) (by norm_num)
theorem B3784229 : Blo 1494067 3784229 := bbase (se 4 (by rfl) ⟨354771, by rfl⟩ : syracuseStep 3784229 = 709543) (by norm_num)
theorem B2522677 : Blo 1494067 2522677 := bbase (se 5 (by rfl) ⟨118250, by rfl⟩ : syracuseStep 2522677 = 236501) (by norm_num)
theorem B5045813 : Blo 1494067 5045813 := bbase (se 5 (by rfl) ⟨236522, by rfl⟩ : syracuseStep 5045813 = 473045) (by norm_num)
theorem B6913621 : Blo 1494067 6913621 := bbase (se 8 (by rfl) ⟨40509, by rfl⟩ : syracuseStep 6913621 = 81019) (by norm_num)
theorem B1891937 : Blo 1494067 1891937 := bbase (se 2 (by rfl) ⟨709476, by rfl⟩ : syracuseStep 1891937 = 1418953) (by norm_num)
theorem B2522765 : Blo 1494067 2522765 := bbase (se 3 (by rfl) ⟨473018, by rfl⟩ : syracuseStep 2522765 = 946037) (by norm_num)
theorem B1891993 : Blo 1494067 1891993 := bbase (se 2 (by rfl) ⟨709497, by rfl⟩ : syracuseStep 1891993 = 1418995) (by norm_num)
theorem B3784421 : Blo 1494067 3784421 := bbase (se 4 (by rfl) ⟨354789, by rfl⟩ : syracuseStep 3784421 = 709579) (by norm_num)
theorem B7569125 : Blo 1494067 7569125 := bbase (se 4 (by rfl) ⟨709605, by rfl⟩ : syracuseStep 7569125 = 1419211) (by norm_num)
theorem B1892089 : Blo 1494067 1892089 := bbase (se 2 (by rfl) ⟨709533, by rfl⟩ : syracuseStep 1892089 = 1419067) (by norm_num)
theorem B2522893 : Blo 1494067 2522893 := bbase (se 3 (by rfl) ⟨473042, by rfl⟩ : syracuseStep 2522893 = 946085) (by norm_num)
theorem B3194653 : Blo 1494067 3194653 := bbase (se 3 (by rfl) ⟨598997, by rfl⟩ : syracuseStep 3194653 = 1197995) (by norm_num)
theorem B2522981 : Blo 1494067 2522981 := bbase (se 4 (by rfl) ⟨236529, by rfl⟩ : syracuseStep 2522981 = 473059) (by norm_num)
theorem B9715573 : Blo 1494067 9715573 := bbase (se 5 (by rfl) ⟨455417, by rfl⟩ : syracuseStep 9715573 = 910835) (by norm_num)
theorem B3030941 : Blo 1494067 3030941 := bbase (se 3 (by rfl) ⟨568301, by rfl⟩ : syracuseStep 3030941 = 1136603) (by norm_num)
theorem B1892261 : Blo 1494067 1892261 := bbase (se 4 (by rfl) ⟨177399, by rfl⟩ : syracuseStep 1892261 = 354799) (by norm_num)
theorem B3194797 : Blo 1494067 3194797 := bbase (se 3 (by rfl) ⟨599024, by rfl⟩ : syracuseStep 3194797 = 1198049) (by norm_num)
theorem B20742101 : Blo 1494067 20742101 := bbase (se 7 (by rfl) ⟨243071, by rfl⟩ : syracuseStep 20742101 = 486143) (by norm_num)
theorem B1892317 : Blo 1494067 1892317 := bbase (se 3 (by rfl) ⟨354809, by rfl⟩ : syracuseStep 1892317 = 709619) (by norm_num)
theorem B2523109 : Blo 1494067 2523109 := bbase (se 4 (by rfl) ⟨236541, by rfl⟩ : syracuseStep 2523109 = 473083) (by norm_num)
theorem B5046245 : Blo 1494067 5046245 := bbase (se 4 (by rfl) ⟨473085, by rfl⟩ : syracuseStep 5046245 = 946171) (by norm_num)
theorem B1597429 : Blo 1494067 1597429 := bbase (se 5 (by rfl) ⟨74879, by rfl⟩ : syracuseStep 1597429 = 149759) (by norm_num)
theorem B14376973 : Blo 1494067 14376973 := bstep (se 3 (by rfl) ⟨2695682, by rfl⟩ : syracuseStep 14376973 = 5391365) B5391365
theorem B5046353 : Blo 1494067 5046353 := bstep (se 2 (by rfl) ⟨1892382, by rfl⟩ : syracuseStep 5046353 = 3784765) B3784765
theorem B2523217 : Blo 1494067 2523217 := bstep (se 2 (by rfl) ⟨946206, by rfl⟩ : syracuseStep 2523217 = 1892413) B1892413
theorem B2555987 : Blo 1494067 2555987 := bstep (se 1 (by rfl) ⟨1916990, by rfl⟩ : syracuseStep 2555987 = 3833981) B3833981
theorem B2523251 : Blo 1494067 2523251 := bstep (se 1 (by rfl) ⟨1892438, by rfl⟩ : syracuseStep 2523251 = 3784877) B3784877
theorem B7282865 : Blo 1494067 7282865 := bstep (se 2 (by rfl) ⟨2731074, by rfl⟩ : syracuseStep 7282865 = 5462149) B5462149
theorem B7987397 : Blo 1494067 7987397 := bstep (se 4 (by rfl) ⟨748818, by rfl⟩ : syracuseStep 7987397 = 1497637) B1497637
theorem B2523379 : Blo 1494067 2523379 := bstep (se 1 (by rfl) ⟨1892534, by rfl⟩ : syracuseStep 2523379 = 3785069) B3785069
theorem B3195139 : Blo 1494067 3195139 := bstep (se 1 (by rfl) ⟨2396354, by rfl⟩ : syracuseStep 3195139 = 4792709) B4792709
theorem B5611789 : Blo 1494067 5611789 := bstep (se 3 (by rfl) ⟨1052210, by rfl⟩ : syracuseStep 5611789 = 2104421) B2104421
theorem B43098389 : Blo 1494067 43098389 := bstep (se 6 (by rfl) ⟨1010118, by rfl⟩ : syracuseStep 43098389 = 2020237) B2020237
theorem B5677361 : Blo 1494067 5677361 := bstep (se 2 (by rfl) ⟨2129010, by rfl⟩ : syracuseStep 5677361 = 4258021) B4258021
theorem B8520005 : Blo 1494067 8520005 := bstep (se 4 (by rfl) ⟨798750, by rfl⟩ : syracuseStep 8520005 = 1597501) B1597501
theorem B2523521 : Blo 1494067 2523521 := bstep (se 2 (by rfl) ⟨946320, by rfl⟩ : syracuseStep 2523521 = 1892641) B1892641
theorem B1892803 : Blo 1494067 1892803 := bstep (se 1 (by rfl) ⟨1419602, by rfl⟩ : syracuseStep 1892803 = 2839205) B2839205
theorem B21856709 : Blo 1494067 21856709 := bstep (se 4 (by rfl) ⟨2049066, by rfl⟩ : syracuseStep 21856709 = 4098133) B4098133
theorem B3457507 : Blo 1494067 3457507 := bstep (se 1 (by rfl) ⟨2593130, by rfl⟩ : syracuseStep 3457507 = 5186261) B5186261
theorem B5390819 : Blo 1494067 5390819 := bstep (se 1 (by rfl) ⟨4043114, by rfl⟩ : syracuseStep 5390819 = 8086229) B8086229
theorem B3785201 : Blo 1494067 3785201 := bstep (se 2 (by rfl) ⟨1419450, by rfl⟩ : syracuseStep 3785201 = 2838901) B2838901
theorem B2523649 : Blo 1494067 2523649 := bstep (se 2 (by rfl) ⟨946368, by rfl⟩ : syracuseStep 2523649 = 1892737) B1892737
theorem B3785251 : Blo 1494067 3785251 := bstep (se 1 (by rfl) ⟨2838938, by rfl⟩ : syracuseStep 3785251 = 5677877) B5677877
theorem B2523683 : Blo 1494067 2523683 := bstep (se 1 (by rfl) ⟨1892762, by rfl⟩ : syracuseStep 2523683 = 3785525) B3785525
theorem B1892899 : Blo 1494067 1892899 := bstep (se 1 (by rfl) ⟨1419674, by rfl⟩ : syracuseStep 1892899 = 2839349) B2839349
theorem B5046893 : Blo 1494067 5046893 := bstep (se 3 (by rfl) ⟨946292, by rfl⟩ : syracuseStep 5046893 = 1892585) B1892585
theorem B15352433 : Blo 1494067 15352433 := bstep (se 2 (by rfl) ⟨5757162, by rfl⟩ : syracuseStep 15352433 = 11514325) B11514325
theorem B5046947 : Blo 1494067 5046947 := bstep (se 1 (by rfl) ⟨3785210, by rfl⟩ : syracuseStep 5046947 = 7570421) B7570421
theorem B2523811 : Blo 1494067 2523811 := bstep (se 1 (by rfl) ⟨1892858, by rfl⟩ : syracuseStep 2523811 = 3785717) B3785717
theorem B7570097 : Blo 1494067 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B3785393 : Blo 1494067 3785393 := bstep (se 2 (by rfl) ⟨1419522, by rfl⟩ : syracuseStep 3785393 = 2839045) B2839045
theorem B2368259 : Blo 1494067 2368259 := bstep (se 1 (by rfl) ⟨1776194, by rfl⟩ : syracuseStep 2368259 = 3552389) B3552389
theorem B8520461 : Blo 1494067 8520461 := bstep (se 3 (by rfl) ⟨1597586, by rfl⟩ : syracuseStep 8520461 = 3195173) B3195173
theorem B6382385 : Blo 1494067 6382385 := bstep (se 2 (by rfl) ⟨2393394, by rfl⟩ : syracuseStep 6382385 = 4786789) B4786789
theorem B2523953 : Blo 1494067 2523953 := bstep (se 2 (by rfl) ⟨946482, by rfl⟩ : syracuseStep 2523953 = 1892965) B1892965
theorem B2556755 : Blo 1494067 2556755 := bstep (se 1 (by rfl) ⟨1917566, by rfl⟩ : syracuseStep 2556755 = 3835133) B3835133
theorem B8512397 : Blo 1494067 8512397 := bstep (se 3 (by rfl) ⟨1596074, by rfl⟩ : syracuseStep 8512397 = 3192149) B3192149
theorem B17269645 : Blo 1494067 17269645 := bstep (se 3 (by rfl) ⟨3238058, by rfl⟩ : syracuseStep 17269645 = 6476117) B6476117
theorem B5047217 : Blo 1494067 5047217 := bstep (se 2 (by rfl) ⟨1892706, by rfl⟩ : syracuseStep 5047217 = 3785413) B3785413
theorem B2524081 : Blo 1494067 2524081 := bstep (se 2 (by rfl) ⟨946530, by rfl⟩ : syracuseStep 2524081 = 1893061) B1893061
theorem B2524115 : Blo 1494067 2524115 := bstep (se 1 (by rfl) ⟨1893086, by rfl⟩ : syracuseStep 2524115 = 3786173) B3786173
theorem B24232931 : Blo 1494067 24232931 := bstep (se 1 (by rfl) ⟨18174698, by rfl⟩ : syracuseStep 24232931 = 36349397) B36349397
theorem B1893395 : Blo 1494067 1893395 := bstep (se 1 (by rfl) ⟨1420046, by rfl⟩ : syracuseStep 1893395 = 2840093) B2840093
theorem B1795123 : Blo 1494067 1795123 := bstep (se 1 (by rfl) ⟨1346342, by rfl⟩ : syracuseStep 1795123 = 2692685) B2692685
theorem B2524243 : Blo 1494067 2524243 := bstep (se 1 (by rfl) ⟨1893182, by rfl⟩ : syracuseStep 2524243 = 3786365) B3786365
theorem B46040177 : Blo 1494067 46040177 := bstep (se 2 (by rfl) ⟨17265066, by rfl⟩ : syracuseStep 46040177 = 34530133) B34530133
theorem B8086661 : Blo 1494067 8086661 := bstep (se 4 (by rfl) ⟨758124, by rfl⟩ : syracuseStep 8086661 = 1516249) B1516249
theorem B2524385 : Blo 1494067 2524385 := bstep (se 2 (by rfl) ⟨946644, by rfl⟩ : syracuseStep 2524385 = 1893289) B1893289
theorem B10110221 : Blo 1494067 10110221 := bstep (se 3 (by rfl) ⟨1895666, by rfl⟩ : syracuseStep 10110221 = 3791333) B3791333
theorem B6063437 : Blo 1494067 6063437 := bstep (se 3 (by rfl) ⟨1136894, by rfl⟩ : syracuseStep 6063437 = 2273789) B2273789
theorem B2524513 : Blo 1494067 2524513 := bstep (se 2 (by rfl) ⟨946692, by rfl⟩ : syracuseStep 2524513 = 1893385) B1893385
theorem B2393459 : Blo 1494067 2393459 := bstep (se 1 (by rfl) ⟨1795094, by rfl⟩ : syracuseStep 2393459 = 3590189) B3590189
theorem B2524547 : Blo 1494067 2524547 := bstep (se 1 (by rfl) ⟨1893410, by rfl⟩ : syracuseStep 2524547 = 3786821) B3786821
theorem B1680835 : Blo 1494067 1680835 := bstep (se 1 (by rfl) ⟨1260626, by rfl⟩ : syracuseStep 1680835 = 2521253) B2521253
theorem B5047757 : Blo 1494067 5047757 := bstep (se 3 (by rfl) ⟨946454, by rfl⟩ : syracuseStep 5047757 = 1892909) B1892909
theorem B5047811 : Blo 1494067 5047811 := bstep (se 1 (by rfl) ⟨3785858, by rfl⟩ : syracuseStep 5047811 = 7571717) B7571717
theorem B2393651 : Blo 1494067 2393651 := bstep (se 1 (by rfl) ⟨1795238, by rfl⟩ : syracuseStep 2393651 = 3590477) B3590477
theorem B1795651 : Blo 1494067 1795651 := bstep (se 1 (by rfl) ⟨1346738, by rfl⟩ : syracuseStep 1795651 = 2693477) B2693477
theorem B1680979 : Blo 1494067 1680979 := bstep (se 1 (by rfl) ⟨1260734, by rfl⟩ : syracuseStep 1680979 = 2521469) B2521469
theorem B14362211 : Blo 1494067 14362211 := bstep (se 1 (by rfl) ⟨10771658, by rfl⟩ : syracuseStep 14362211 = 21543317) B21543317
theorem B3786385 : Blo 1494067 3786385 := bstep (se 2 (by rfl) ⟨1419894, by rfl⟩ : syracuseStep 3786385 = 2839789) B2839789
theorem B1681123 : Blo 1494067 1681123 := bstep (se 1 (by rfl) ⟨1260842, by rfl⟩ : syracuseStep 1681123 = 2521685) B2521685
theorem B11355875 : Blo 1494067 11355875 := bstep (se 1 (by rfl) ⟨8516906, by rfl⟩ : syracuseStep 11355875 = 17033813) B17033813
theorem B5678819 : Blo 1494067 5678819 := bstep (se 1 (by rfl) ⟨4259114, by rfl⟩ : syracuseStep 5678819 = 8518229) B8518229
theorem B5048081 : Blo 1494067 5048081 := bstep (se 2 (by rfl) ⟨1893030, by rfl⟩ : syracuseStep 5048081 = 3786061) B3786061
theorem B13633393 : Blo 1494067 13633393 := bstep (se 2 (by rfl) ⟨5112522, by rfl⟩ : syracuseStep 13633393 = 10225045) B10225045
theorem B1681267 : Blo 1494067 1681267 := bstep (se 1 (by rfl) ⟨1260950, by rfl⟩ : syracuseStep 1681267 = 2521901) B2521901
theorem B3786659 : Blo 1494067 3786659 := bstep (se 1 (by rfl) ⟨2839994, by rfl⟩ : syracuseStep 3786659 = 5679989) B5679989
theorem B2836433 : Blo 1494067 2836433 := bstep (se 2 (by rfl) ⟨1063662, by rfl⟩ : syracuseStep 2836433 = 2127325) B2127325
theorem B1681411 : Blo 1494067 1681411 := bstep (se 1 (by rfl) ⟨1261058, by rfl⟩ : syracuseStep 1681411 = 2522117) B2522117
theorem B2426945 : Blo 1494067 2426945 := bstep (se 2 (by rfl) ⟨910104, by rfl⟩ : syracuseStep 2426945 = 1820209) B1820209
theorem B7571555 : Blo 1494067 7571555 := bstep (se 1 (by rfl) ⟨5678666, by rfl⟩ : syracuseStep 7571555 = 11357333) B11357333
theorem B3786851 : Blo 1494067 3786851 := bstep (se 1 (by rfl) ⟨2840138, by rfl⟩ : syracuseStep 3786851 = 5680277) B5680277
theorem B9218161 : Blo 1494067 9218161 := bstep (se 2 (by rfl) ⟨3456810, by rfl⟩ : syracuseStep 9218161 = 6913621) B6913621
theorem B1681555 : Blo 1494067 1681555 := bstep (se 1 (by rfl) ⟨1261166, by rfl⟩ : syracuseStep 1681555 = 2522333) B2522333
theorem B2836721 : Blo 1494067 2836721 := bstep (se 2 (by rfl) ⟨1063770, by rfl⟩ : syracuseStep 2836721 = 2127541) B2127541
theorem B10225925 : Blo 1494067 10225925 := bstep (se 4 (by rfl) ⟨958680, by rfl⟩ : syracuseStep 10225925 = 1917361) B1917361
theorem B1681699 : Blo 1494067 1681699 := bstep (se 1 (by rfl) ⟨1261274, by rfl⟩ : syracuseStep 1681699 = 2522549) B2522549
theorem B5048621 : Blo 1494067 5048621 := bstep (se 3 (by rfl) ⟨946616, by rfl⟩ : syracuseStep 5048621 = 1893233) B1893233
theorem B5048675 : Blo 1494067 5048675 := bstep (se 1 (by rfl) ⟨3786506, by rfl⟩ : syracuseStep 5048675 = 7573013) B7573013
theorem B10226033 : Blo 1494067 10226033 := bstep (se 2 (by rfl) ⟨3834762, by rfl⟩ : syracuseStep 10226033 = 7669525) B7669525
theorem B4786609 : Blo 1494067 4786609 := bstep (se 2 (by rfl) ⟨1794978, by rfl⟩ : syracuseStep 4786609 = 3589957) B3589957
theorem B1681843 : Blo 1494067 1681843 := bstep (se 1 (by rfl) ⟨1261382, by rfl⟩ : syracuseStep 1681843 = 2522765) B2522765
theorem B2877905 : Blo 1494067 2877905 := bstep (se 2 (by rfl) ⟨1079214, by rfl⟩ : syracuseStep 2877905 = 2158429) B2158429
theorem B12954097 : Blo 1494067 12954097 := bstep (se 2 (by rfl) ⟨4857786, by rfl⟩ : syracuseStep 12954097 = 9715573) B9715573
theorem B2394625 : Blo 1494067 2394625 := bstep (se 2 (by rfl) ⟨897984, by rfl⟩ : syracuseStep 2394625 = 1795969) B1795969
theorem B21563957 : Blo 1494067 21563957 := bstep (se 5 (by rfl) ⟨1010810, by rfl⟩ : syracuseStep 21563957 = 2021621) B2021621
theorem B1681987 : Blo 1494067 1681987 := bstep (se 1 (by rfl) ⟨1261490, by rfl⟩ : syracuseStep 1681987 = 2522981) B2522981
theorem B5048945 : Blo 1494067 5048945 := bstep (se 2 (by rfl) ⟨1893354, by rfl⟩ : syracuseStep 5048945 = 3786709) B3786709
theorem B4786865 : Blo 1494067 4786865 := bstep (se 2 (by rfl) ⟨1795074, by rfl⟩ : syracuseStep 4786865 = 3590149) B3590149
theorem B5679821 : Blo 1494067 5679821 := bstep (se 3 (by rfl) ⟨1064966, by rfl⟩ : syracuseStep 5679821 = 2129933) B2129933
theorem B1682131 : Blo 1494067 1682131 := bstep (se 1 (by rfl) ⟨1261598, by rfl⟩ : syracuseStep 1682131 = 2523197) B2523197
theorem B10775267 : Blo 1494067 10775267 := bstep (se 1 (by rfl) ⟨8081450, by rfl⟩ : syracuseStep 10775267 = 16162901) B16162901
theorem B1682275 : Blo 1494067 1682275 := bstep (se 1 (by rfl) ⟨1261706, by rfl⟩ : syracuseStep 1682275 = 2523413) B2523413
theorem B9087857 : Blo 1494067 9087857 := bstep (se 2 (by rfl) ⟨3407946, by rfl⟩ : syracuseStep 9087857 = 6815893) B6815893
theorem B7572365 : Blo 1494067 7572365 := bstep (se 3 (by rfl) ⟨1419818, by rfl⟩ : syracuseStep 7572365 = 2839637) B2839637
theorem B2395073 : Blo 1494067 2395073 := bstep (se 2 (by rfl) ⟨898152, by rfl⟩ : syracuseStep 2395073 = 1796305) B1796305
theorem B2837443 : Blo 1494067 2837443 := bstep (se 1 (by rfl) ⟨2128082, by rfl⟩ : syracuseStep 2837443 = 4256165) B4256165
theorem B1682419 : Blo 1494067 1682419 := bstep (se 1 (by rfl) ⟨1261814, by rfl⟩ : syracuseStep 1682419 = 2523629) B2523629
theorem B4041731 : Blo 1494067 4041731 := bstep (se 1 (by rfl) ⟨3031298, by rfl⟩ : syracuseStep 4041731 = 6062597) B6062597
theorem B3361841 : Blo 1494067 3361841 := bstep (se 2 (by rfl) ⟨1260690, by rfl⟩ : syracuseStep 3361841 = 2521381) B2521381
theorem B1494067 : Blo 1494067 1494067 := bstep (se 1 (by rfl) ⟨1120550, by rfl⟩ : syracuseStep 1494067 = 2241101) B2241101
theorem B1494083 : Blo 1494067 1494083 := bstep (se 1 (by rfl) ⟨1120562, by rfl⟩ : syracuseStep 1494083 = 2241125) B2241125
theorem B3361859 : Blo 1494067 3361859 := bstep (se 1 (by rfl) ⟨2521394, by rfl⟩ : syracuseStep 3361859 = 5042789) B5042789
theorem B8514629 : Blo 1494067 8514629 := bstep (se 4 (by rfl) ⟨798246, by rfl⟩ : syracuseStep 8514629 = 1596493) B1596493
theorem B1494099 : Blo 1494067 1494099 := bstep (se 1 (by rfl) ⟨1120574, by rfl⟩ : syracuseStep 1494099 = 2241149) B2241149
theorem B1494115 : Blo 1494067 1494115 := bstep (se 1 (by rfl) ⟨1120586, by rfl⟩ : syracuseStep 1494115 = 2241173) B2241173
theorem B1494131 : Blo 1494067 1494131 := bstep (se 1 (by rfl) ⟨1120598, by rfl⟩ : syracuseStep 1494131 = 2241197) B2241197
theorem B1494147 : Blo 1494067 1494147 := bstep (se 1 (by rfl) ⟨1120610, by rfl⟩ : syracuseStep 1494147 = 2241221) B2241221
theorem B4041859 : Blo 1494067 4041859 := bstep (se 1 (by rfl) ⟨3031394, by rfl⟩ : syracuseStep 4041859 = 6062789) B6062789
theorem B9579653 : Blo 1494067 9579653 := bstep (se 4 (by rfl) ⟨898092, by rfl⟩ : syracuseStep 9579653 = 1796185) B1796185
theorem B1682563 : Blo 1494067 1682563 := bstep (se 1 (by rfl) ⟨1261922, by rfl⟩ : syracuseStep 1682563 = 2523845) B2523845
theorem B1494163 : Blo 1494067 1494163 := bstep (se 1 (by rfl) ⟨1120622, by rfl⟩ : syracuseStep 1494163 = 2241245) B2241245
theorem B1494179 : Blo 1494067 1494179 := bstep (se 1 (by rfl) ⟨1120634, by rfl⟩ : syracuseStep 1494179 = 2241269) B2241269
theorem B1494195 : Blo 1494067 1494195 := bstep (se 1 (by rfl) ⟨1120646, by rfl⟩ : syracuseStep 1494195 = 2241293) B2241293
theorem B1494211 : Blo 1494067 1494211 := bstep (se 1 (by rfl) ⟨1120658, by rfl⟩ : syracuseStep 1494211 = 2241317) B2241317
theorem B6384845 : Blo 1494067 6384845 := bstep (se 3 (by rfl) ⟨1197158, by rfl⟩ : syracuseStep 6384845 = 2394317) B2394317
theorem B1494227 : Blo 1494067 1494227 := bstep (se 1 (by rfl) ⟨1120670, by rfl⟩ : syracuseStep 1494227 = 2241341) B2241341
theorem B1494243 : Blo 1494067 1494243 := bstep (se 1 (by rfl) ⟨1120682, by rfl⟩ : syracuseStep 1494243 = 2241365) B2241365
theorem B1494259 : Blo 1494067 1494259 := bstep (se 1 (by rfl) ⟨1120694, by rfl⟩ : syracuseStep 1494259 = 2241389) B2241389
theorem B1494275 : Blo 1494067 1494275 := bstep (se 1 (by rfl) ⟨1120706, by rfl⟩ : syracuseStep 1494275 = 2241413) B2241413
theorem B1494291 : Blo 1494067 1494291 := bstep (se 1 (by rfl) ⟨1120718, by rfl⟩ : syracuseStep 1494291 = 2241437) B2241437
theorem B1682707 : Blo 1494067 1682707 := bstep (se 1 (by rfl) ⟨1262030, by rfl⟩ : syracuseStep 1682707 = 2524061) B2524061
theorem B1494307 : Blo 1494067 1494307 := bstep (se 1 (by rfl) ⟨1120730, by rfl⟩ : syracuseStep 1494307 = 2241461) B2241461
theorem B1494323 : Blo 1494067 1494323 := bstep (se 1 (by rfl) ⟨1120742, by rfl⟩ : syracuseStep 1494323 = 2241485) B2241485
theorem B1494339 : Blo 1494067 1494339 := bstep (se 1 (by rfl) ⟨1120754, by rfl⟩ : syracuseStep 1494339 = 2241509) B2241509
theorem B3362129 : Blo 1494067 3362129 := bstep (se 2 (by rfl) ⟨1260798, by rfl⟩ : syracuseStep 3362129 = 2521597) B2521597
theorem B1494355 : Blo 1494067 1494355 := bstep (se 1 (by rfl) ⟨1120766, by rfl⟩ : syracuseStep 1494355 = 2241533) B2241533
theorem B3362147 : Blo 1494067 3362147 := bstep (se 1 (by rfl) ⟨2521610, by rfl⟩ : syracuseStep 3362147 = 5043221) B5043221
theorem B1494371 : Blo 1494067 1494371 := bstep (se 1 (by rfl) ⟨1120778, by rfl⟩ : syracuseStep 1494371 = 2241557) B2241557
theorem B1494387 : Blo 1494067 1494387 := bstep (se 1 (by rfl) ⟨1120790, by rfl⟩ : syracuseStep 1494387 = 2241581) B2241581
theorem B1494403 : Blo 1494067 1494403 := bstep (se 1 (by rfl) ⟨1120802, by rfl⟩ : syracuseStep 1494403 = 2241605) B2241605
theorem B2837891 : Blo 1494067 2837891 := bstep (se 1 (by rfl) ⟨2128418, by rfl⟩ : syracuseStep 2837891 = 4256837) B4256837
theorem B1494419 : Blo 1494067 1494419 := bstep (se 1 (by rfl) ⟨1120814, by rfl⟩ : syracuseStep 1494419 = 2241629) B2241629
theorem B1494435 : Blo 1494067 1494435 := bstep (se 1 (by rfl) ⟨1120826, by rfl⟩ : syracuseStep 1494435 = 2241653) B2241653
theorem B3689891 : Blo 1494067 3689891 := bstep (se 1 (by rfl) ⟨2767418, by rfl⟩ : syracuseStep 3689891 = 5534837) B5534837
theorem B1682851 : Blo 1494067 1682851 := bstep (se 1 (by rfl) ⟨1262138, by rfl⟩ : syracuseStep 1682851 = 2524277) B2524277
theorem B1494451 : Blo 1494067 1494451 := bstep (se 1 (by rfl) ⟨1120838, by rfl⟩ : syracuseStep 1494451 = 2241677) B2241677
theorem B2493875 : Blo 1494067 2493875 := bstep (se 1 (by rfl) ⟨1870406, by rfl⟩ : syracuseStep 2493875 = 3740813) B3740813
theorem B1494467 : Blo 1494067 1494467 := bstep (se 1 (by rfl) ⟨1120850, by rfl⟩ : syracuseStep 1494467 = 2241701) B2241701
theorem B1494483 : Blo 1494067 1494483 := bstep (se 1 (by rfl) ⟨1120862, by rfl⟩ : syracuseStep 1494483 = 2241725) B2241725
theorem B1494499 : Blo 1494067 1494499 := bstep (se 1 (by rfl) ⟨1120874, by rfl⟩ : syracuseStep 1494499 = 2241749) B2241749
theorem B1494515 : Blo 1494067 1494515 := bstep (se 1 (by rfl) ⟨1120886, by rfl⟩ : syracuseStep 1494515 = 2241773) B2241773
theorem B1494531 : Blo 1494067 1494531 := bstep (se 1 (by rfl) ⟨1120898, by rfl⟩ : syracuseStep 1494531 = 2241797) B2241797
theorem B1494547 : Blo 1494067 1494547 := bstep (se 1 (by rfl) ⟨1120910, by rfl⟩ : syracuseStep 1494547 = 2241821) B2241821
theorem B1494563 : Blo 1494067 1494563 := bstep (se 1 (by rfl) ⟨1120922, by rfl⟩ : syracuseStep 1494563 = 2241845) B2241845
theorem B2272817 : Blo 1494067 2272817 := bstep (se 2 (by rfl) ⟨852306, by rfl⟩ : syracuseStep 2272817 = 1704613) B1704613
theorem B1494579 : Blo 1494067 1494579 := bstep (se 1 (by rfl) ⟨1120934, by rfl⟩ : syracuseStep 1494579 = 2241869) B2241869
theorem B1682995 : Blo 1494067 1682995 := bstep (se 1 (by rfl) ⟨1262246, by rfl⟩ : syracuseStep 1682995 = 2524493) B2524493
theorem B1494595 : Blo 1494067 1494595 := bstep (se 1 (by rfl) ⟨1120946, by rfl⟩ : syracuseStep 1494595 = 2241893) B2241893
theorem B1494611 : Blo 1494067 1494611 := bstep (se 1 (by rfl) ⟨1120958, by rfl⟩ : syracuseStep 1494611 = 2241917) B2241917
theorem B1494627 : Blo 1494067 1494627 := bstep (se 1 (by rfl) ⟨1120970, by rfl⟩ : syracuseStep 1494627 = 2241941) B2241941
theorem B7564913 : Blo 1494067 7564913 := bstep (se 2 (by rfl) ⟨2836842, by rfl⟩ : syracuseStep 7564913 = 5673685) B5673685
theorem B3362417 : Blo 1494067 3362417 := bstep (se 2 (by rfl) ⟨1260906, by rfl⟩ : syracuseStep 3362417 = 2521813) B2521813
theorem B1494643 : Blo 1494067 1494643 := bstep (se 1 (by rfl) ⟨1120982, by rfl⟩ : syracuseStep 1494643 = 2241965) B2241965
theorem B3362435 : Blo 1494067 3362435 := bstep (se 1 (by rfl) ⟨2521826, by rfl⟩ : syracuseStep 3362435 = 5043653) B5043653
theorem B1494659 : Blo 1494067 1494659 := bstep (se 1 (by rfl) ⟨1120994, by rfl⟩ : syracuseStep 1494659 = 2241989) B2241989
theorem B1494675 : Blo 1494067 1494675 := bstep (se 1 (by rfl) ⟨1121006, by rfl⟩ : syracuseStep 1494675 = 2242013) B2242013
theorem B1494691 : Blo 1494067 1494691 := bstep (se 1 (by rfl) ⟨1121018, by rfl⟩ : syracuseStep 1494691 = 2242037) B2242037
theorem B2838179 : Blo 1494067 2838179 := bstep (se 1 (by rfl) ⟨2128634, by rfl⟩ : syracuseStep 2838179 = 4257269) B4257269
theorem B1494707 : Blo 1494067 1494707 := bstep (se 1 (by rfl) ⟨1121030, by rfl⟩ : syracuseStep 1494707 = 2242061) B2242061
theorem B1494723 : Blo 1494067 1494723 := bstep (se 1 (by rfl) ⟨1121042, by rfl⟩ : syracuseStep 1494723 = 2242085) B2242085
theorem B1494739 : Blo 1494067 1494739 := bstep (se 1 (by rfl) ⟨1121054, by rfl⟩ : syracuseStep 1494739 = 2242109) B2242109
theorem B1494755 : Blo 1494067 1494755 := bstep (se 1 (by rfl) ⟨1121066, by rfl⟩ : syracuseStep 1494755 = 2242133) B2242133
theorem B8515313 : Blo 1494067 8515313 := bstep (se 2 (by rfl) ⟨3193242, by rfl⟩ : syracuseStep 8515313 = 6386485) B6386485
theorem B1494771 : Blo 1494067 1494771 := bstep (se 1 (by rfl) ⟨1121078, by rfl⟩ : syracuseStep 1494771 = 2242157) B2242157
theorem B1494787 : Blo 1494067 1494787 := bstep (se 1 (by rfl) ⟨1121090, by rfl⟩ : syracuseStep 1494787 = 2242181) B2242181
theorem B4787981 : Blo 1494067 4787981 := bstep (se 3 (by rfl) ⟨897746, by rfl⟩ : syracuseStep 4787981 = 1795493) B1795493
theorem B1494803 : Blo 1494067 1494803 := bstep (se 1 (by rfl) ⟨1121102, by rfl⟩ : syracuseStep 1494803 = 2242205) B2242205
theorem B1494819 : Blo 1494067 1494819 := bstep (se 1 (by rfl) ⟨1121114, by rfl⟩ : syracuseStep 1494819 = 2242229) B2242229
theorem B1494835 : Blo 1494067 1494835 := bstep (se 1 (by rfl) ⟨1121126, by rfl⟩ : syracuseStep 1494835 = 2242253) B2242253
theorem B1494851 : Blo 1494067 1494851 := bstep (se 1 (by rfl) ⟨1121138, by rfl⟩ : syracuseStep 1494851 = 2242277) B2242277
theorem B2158417 : Blo 1494067 2158417 := bstep (se 2 (by rfl) ⟨809406, by rfl⟩ : syracuseStep 2158417 = 1618813) B1618813
theorem B1494867 : Blo 1494067 1494867 := bstep (se 1 (by rfl) ⟨1121150, by rfl⟩ : syracuseStep 1494867 = 2242301) B2242301
theorem B1494883 : Blo 1494067 1494883 := bstep (se 1 (by rfl) ⟨1121162, by rfl⟩ : syracuseStep 1494883 = 2242325) B2242325
theorem B1494899 : Blo 1494067 1494899 := bstep (se 1 (by rfl) ⟨1121174, by rfl⟩ : syracuseStep 1494899 = 2242349) B2242349
theorem B1494915 : Blo 1494067 1494915 := bstep (se 1 (by rfl) ⟨1121186, by rfl⟩ : syracuseStep 1494915 = 2242373) B2242373
theorem B3362705 : Blo 1494067 3362705 := bstep (se 2 (by rfl) ⟨1261014, by rfl⟩ : syracuseStep 3362705 = 2522029) B2522029
theorem B1494931 : Blo 1494067 1494931 := bstep (se 1 (by rfl) ⟨1121198, by rfl⟩ : syracuseStep 1494931 = 2242397) B2242397
theorem B3362723 : Blo 1494067 3362723 := bstep (se 1 (by rfl) ⟨2522042, by rfl⟩ : syracuseStep 3362723 = 5044085) B5044085
theorem B1494947 : Blo 1494067 1494947 := bstep (se 1 (by rfl) ⟨1121210, by rfl⟩ : syracuseStep 1494947 = 2242421) B2242421
theorem B1494963 : Blo 1494067 1494963 := bstep (se 1 (by rfl) ⟨1121222, by rfl⟩ : syracuseStep 1494963 = 2242445) B2242445
theorem B1494979 : Blo 1494067 1494979 := bstep (se 1 (by rfl) ⟨1121234, by rfl⟩ : syracuseStep 1494979 = 2242469) B2242469
theorem B16175045 : Blo 1494067 16175045 := bstep (se 4 (by rfl) ⟨1516410, by rfl⟩ : syracuseStep 16175045 = 3032821) B3032821
theorem B1494995 : Blo 1494067 1494995 := bstep (se 1 (by rfl) ⟨1121246, by rfl⟩ : syracuseStep 1494995 = 2242493) B2242493
theorem B1495011 : Blo 1494067 1495011 := bstep (se 1 (by rfl) ⟨1121258, by rfl⟩ : syracuseStep 1495011 = 2242517) B2242517
theorem B39374819 : Blo 1494067 39374819 := bstep (se 1 (by rfl) ⟨29531114, by rfl⟩ : syracuseStep 39374819 = 59062229) B59062229
theorem B1495027 : Blo 1494067 1495027 := bstep (se 1 (by rfl) ⟨1121270, by rfl⟩ : syracuseStep 1495027 = 2242541) B2242541
theorem B1495043 : Blo 1494067 1495043 := bstep (se 1 (by rfl) ⟨1121282, by rfl⟩ : syracuseStep 1495043 = 2242565) B2242565
theorem B1495059 : Blo 1494067 1495059 := bstep (se 1 (by rfl) ⟨1121294, by rfl⟩ : syracuseStep 1495059 = 2242589) B2242589
theorem B1495075 : Blo 1494067 1495075 := bstep (se 1 (by rfl) ⟨1121306, by rfl⟩ : syracuseStep 1495075 = 2242613) B2242613
theorem B4042801 : Blo 1494067 4042801 := bstep (se 2 (by rfl) ⟨1516050, by rfl⟩ : syracuseStep 4042801 = 3032101) B3032101
theorem B1495091 : Blo 1494067 1495091 := bstep (se 1 (by rfl) ⟨1121318, by rfl⟩ : syracuseStep 1495091 = 2242637) B2242637
theorem B4255811 : Blo 1494067 4255811 := bstep (se 1 (by rfl) ⟨3191858, by rfl⟩ : syracuseStep 4255811 = 6383717) B6383717
theorem B1495107 : Blo 1494067 1495107 := bstep (se 1 (by rfl) ⟨1121330, by rfl⟩ : syracuseStep 1495107 = 2242661) B2242661
theorem B1495123 : Blo 1494067 1495123 := bstep (se 1 (by rfl) ⟨1121342, by rfl⟩ : syracuseStep 1495123 = 2242685) B2242685
theorem B1495139 : Blo 1494067 1495139 := bstep (se 1 (by rfl) ⟨1121354, by rfl⟩ : syracuseStep 1495139 = 2242709) B2242709
theorem B1495155 : Blo 1494067 1495155 := bstep (se 1 (by rfl) ⟨1121366, by rfl⟩ : syracuseStep 1495155 = 2242733) B2242733
theorem B1495171 : Blo 1494067 1495171 := bstep (se 1 (by rfl) ⟨1121378, by rfl⟩ : syracuseStep 1495171 = 2242757) B2242757
theorem B1495187 : Blo 1494067 1495187 := bstep (se 1 (by rfl) ⟨1121390, by rfl⟩ : syracuseStep 1495187 = 2242781) B2242781
theorem B1495203 : Blo 1494067 1495203 := bstep (se 1 (by rfl) ⟨1121402, by rfl⟩ : syracuseStep 1495203 = 2242805) B2242805
theorem B3362993 : Blo 1494067 3362993 := bstep (se 2 (by rfl) ⟨1261122, by rfl⟩ : syracuseStep 3362993 = 2522245) B2522245
theorem B1495219 : Blo 1494067 1495219 := bstep (se 1 (by rfl) ⟨1121414, by rfl⟩ : syracuseStep 1495219 = 2242829) B2242829
theorem B3363011 : Blo 1494067 3363011 := bstep (se 1 (by rfl) ⟨2522258, by rfl⟩ : syracuseStep 3363011 = 5044517) B5044517
theorem B1495235 : Blo 1494067 1495235 := bstep (se 1 (by rfl) ⟨1121426, by rfl⟩ : syracuseStep 1495235 = 2242853) B2242853
theorem B1495251 : Blo 1494067 1495251 := bstep (se 1 (by rfl) ⟨1121438, by rfl⟩ : syracuseStep 1495251 = 2242877) B2242877
theorem B1495267 : Blo 1494067 1495267 := bstep (se 1 (by rfl) ⟨1121450, by rfl⟩ : syracuseStep 1495267 = 2242901) B2242901
theorem B1495283 : Blo 1494067 1495283 := bstep (se 1 (by rfl) ⟨1121462, by rfl⟩ : syracuseStep 1495283 = 2242925) B2242925
theorem B1495299 : Blo 1494067 1495299 := bstep (se 1 (by rfl) ⟨1121474, by rfl⟩ : syracuseStep 1495299 = 2242949) B2242949
theorem B1495315 : Blo 1494067 1495315 := bstep (se 1 (by rfl) ⟨1121486, by rfl⟩ : syracuseStep 1495315 = 2242973) B2242973
theorem B1495331 : Blo 1494067 1495331 := bstep (se 1 (by rfl) ⟨1121498, by rfl⟩ : syracuseStep 1495331 = 2242997) B2242997
theorem B1495347 : Blo 1494067 1495347 := bstep (se 1 (by rfl) ⟨1121510, by rfl⟩ : syracuseStep 1495347 = 2243021) B2243021
theorem B1495363 : Blo 1494067 1495363 := bstep (se 1 (by rfl) ⟨1121522, by rfl⟩ : syracuseStep 1495363 = 2243045) B2243045
theorem B1495379 : Blo 1494067 1495379 := bstep (se 1 (by rfl) ⟨1121534, by rfl⟩ : syracuseStep 1495379 = 2243069) B2243069
theorem B1495395 : Blo 1494067 1495395 := bstep (se 1 (by rfl) ⟨1121546, by rfl⟩ : syracuseStep 1495395 = 2243093) B2243093
theorem B1495411 : Blo 1494067 1495411 := bstep (se 1 (by rfl) ⟨1121558, by rfl⟩ : syracuseStep 1495411 = 2243117) B2243117
theorem B1495427 : Blo 1494067 1495427 := bstep (se 1 (by rfl) ⟨1121570, by rfl⟩ : syracuseStep 1495427 = 2243141) B2243141
theorem B5042573 : Blo 1494067 5042573 := bstep (se 3 (by rfl) ⟨945482, by rfl⟩ : syracuseStep 5042573 = 1890965) B1890965
theorem B6820237 : Blo 1494067 6820237 := bstep (se 3 (by rfl) ⟨1278794, by rfl⟩ : syracuseStep 6820237 = 2557589) B2557589
theorem B1495443 : Blo 1494067 1495443 := bstep (se 1 (by rfl) ⟨1121582, by rfl⟩ : syracuseStep 1495443 = 2243165) B2243165
theorem B1495459 : Blo 1494067 1495459 := bstep (se 1 (by rfl) ⟨1121594, by rfl⟩ : syracuseStep 1495459 = 2243189) B2243189
theorem B1495475 : Blo 1494067 1495475 := bstep (se 1 (by rfl) ⟨1121606, by rfl⟩ : syracuseStep 1495475 = 2243213) B2243213
theorem B5042627 : Blo 1494067 5042627 := bstep (se 1 (by rfl) ⟨3781970, by rfl⟩ : syracuseStep 5042627 = 7563941) B7563941
theorem B1495491 : Blo 1494067 1495491 := bstep (se 1 (by rfl) ⟨1121618, by rfl⟩ : syracuseStep 1495491 = 2243237) B2243237
theorem B5116355 : Blo 1494067 5116355 := bstep (se 1 (by rfl) ⟨3837266, by rfl⟩ : syracuseStep 5116355 = 7674533) B7674533
theorem B3363281 : Blo 1494067 3363281 := bstep (se 2 (by rfl) ⟨1261230, by rfl⟩ : syracuseStep 3363281 = 2522461) B2522461
theorem B1495507 : Blo 1494067 1495507 := bstep (se 1 (by rfl) ⟨1121630, by rfl⟩ : syracuseStep 1495507 = 2243261) B2243261
theorem B3363299 : Blo 1494067 3363299 := bstep (se 1 (by rfl) ⟨2522474, by rfl⟩ : syracuseStep 3363299 = 5044949) B5044949
theorem B12775907 : Blo 1494067 12775907 := bstep (se 1 (by rfl) ⟨9581930, by rfl⟩ : syracuseStep 12775907 = 19163861) B19163861
theorem B1495523 : Blo 1494067 1495523 := bstep (se 1 (by rfl) ⟨1121642, by rfl⟩ : syracuseStep 1495523 = 2243285) B2243285
theorem B6386161 : Blo 1494067 6386161 := bstep (se 2 (by rfl) ⟨2394810, by rfl⟩ : syracuseStep 6386161 = 4789621) B4789621
theorem B1495539 : Blo 1494067 1495539 := bstep (se 1 (by rfl) ⟨1121654, by rfl⟩ : syracuseStep 1495539 = 2243309) B2243309
theorem B1495555 : Blo 1494067 1495555 := bstep (se 1 (by rfl) ⟨1121666, by rfl⟩ : syracuseStep 1495555 = 2243333) B2243333
theorem B1495571 : Blo 1494067 1495571 := bstep (se 1 (by rfl) ⟨1121678, by rfl⟩ : syracuseStep 1495571 = 2243357) B2243357
theorem B1495587 : Blo 1494067 1495587 := bstep (se 1 (by rfl) ⟨1121690, by rfl⟩ : syracuseStep 1495587 = 2243381) B2243381
theorem B1495603 : Blo 1494067 1495603 := bstep (se 1 (by rfl) ⟨1121702, by rfl⟩ : syracuseStep 1495603 = 2243405) B2243405
theorem B1495619 : Blo 1494067 1495619 := bstep (se 1 (by rfl) ⟨1121714, by rfl⟩ : syracuseStep 1495619 = 2243429) B2243429
theorem B2839121 : Blo 1494067 2839121 := bstep (se 2 (by rfl) ⟨1064670, by rfl⟩ : syracuseStep 2839121 = 2129341) B2129341
theorem B2241107 : Blo 1494067 2241107 := bstep (se 1 (by rfl) ⟨1680830, by rfl⟩ : syracuseStep 2241107 = 3361661) B3361661
theorem B1495635 : Blo 1494067 1495635 := bstep (se 1 (by rfl) ⟨1121726, by rfl⟩ : syracuseStep 1495635 = 2243453) B2243453
theorem B1495651 : Blo 1494067 1495651 := bstep (se 1 (by rfl) ⟨1121738, by rfl⟩ : syracuseStep 1495651 = 2243477) B2243477
theorem B2241137 : Blo 1494067 2241137 := bstep (se 2 (by rfl) ⟨840426, by rfl⟩ : syracuseStep 2241137 = 1680853) B1680853
theorem B7180913 : Blo 1494067 7180913 := bstep (se 2 (by rfl) ⟨2692842, by rfl⟩ : syracuseStep 7180913 = 5385685) B5385685
theorem B1495667 : Blo 1494067 1495667 := bstep (se 1 (by rfl) ⟨1121750, by rfl⟩ : syracuseStep 1495667 = 2243501) B2243501
theorem B2241155 : Blo 1494067 2241155 := bstep (se 1 (by rfl) ⟨1680866, by rfl⟩ : syracuseStep 2241155 = 3361733) B3361733
theorem B1495683 : Blo 1494067 1495683 := bstep (se 1 (by rfl) ⟨1121762, by rfl⟩ : syracuseStep 1495683 = 2243525) B2243525
theorem B1495699 : Blo 1494067 1495699 := bstep (se 1 (by rfl) ⟨1121774, by rfl⟩ : syracuseStep 1495699 = 2243549) B2243549
theorem B2241185 : Blo 1494067 2241185 := bstep (se 2 (by rfl) ⟨840444, by rfl⟩ : syracuseStep 2241185 = 1680889) B1680889
theorem B1495715 : Blo 1494067 1495715 := bstep (se 1 (by rfl) ⟨1121786, by rfl⟩ : syracuseStep 1495715 = 2243573) B2243573
theorem B2241203 : Blo 1494067 2241203 := bstep (se 1 (by rfl) ⟨1680902, by rfl⟩ : syracuseStep 2241203 = 3361805) B3361805
theorem B1495731 : Blo 1494067 1495731 := bstep (se 1 (by rfl) ⟨1121798, by rfl⟩ : syracuseStep 1495731 = 2243597) B2243597
theorem B1495747 : Blo 1494067 1495747 := bstep (se 1 (by rfl) ⟨1121810, by rfl⟩ : syracuseStep 1495747 = 2243621) B2243621
theorem B9704141 : Blo 1494067 9704141 := bstep (se 3 (by rfl) ⟨1819526, by rfl⟩ : syracuseStep 9704141 = 3639053) B3639053
theorem B2241233 : Blo 1494067 2241233 := bstep (se 2 (by rfl) ⟨840462, by rfl⟩ : syracuseStep 2241233 = 1680925) B1680925
theorem B5042897 : Blo 1494067 5042897 := bstep (se 2 (by rfl) ⟨1891086, by rfl⟩ : syracuseStep 5042897 = 3782173) B3782173
theorem B1495763 : Blo 1494067 1495763 := bstep (se 1 (by rfl) ⟨1121822, by rfl⟩ : syracuseStep 1495763 = 2243645) B2243645
theorem B2241251 : Blo 1494067 2241251 := bstep (se 1 (by rfl) ⟨1680938, by rfl⟩ : syracuseStep 2241251 = 3361877) B3361877
theorem B1495779 : Blo 1494067 1495779 := bstep (se 1 (by rfl) ⟨1121834, by rfl⟩ : syracuseStep 1495779 = 2243669) B2243669
theorem B3363569 : Blo 1494067 3363569 := bstep (se 2 (by rfl) ⟨1261338, by rfl⟩ : syracuseStep 3363569 = 2522677) B2522677
theorem B1495795 : Blo 1494067 1495795 := bstep (se 1 (by rfl) ⟨1121846, by rfl⟩ : syracuseStep 1495795 = 2243693) B2243693
theorem B2241281 : Blo 1494067 2241281 := bstep (se 2 (by rfl) ⟨840480, by rfl⟩ : syracuseStep 2241281 = 1680961) B1680961
theorem B3363587 : Blo 1494067 3363587 := bstep (se 1 (by rfl) ⟨2522690, by rfl⟩ : syracuseStep 3363587 = 5045381) B5045381
theorem B1495811 : Blo 1494067 1495811 := bstep (se 1 (by rfl) ⟨1121858, by rfl⟩ : syracuseStep 1495811 = 2243717) B2243717
theorem B2241299 : Blo 1494067 2241299 := bstep (se 1 (by rfl) ⟨1680974, by rfl⟩ : syracuseStep 2241299 = 3361949) B3361949
theorem B1495827 : Blo 1494067 1495827 := bstep (se 1 (by rfl) ⟨1121870, by rfl⟩ : syracuseStep 1495827 = 2243741) B2243741
theorem B1495843 : Blo 1494067 1495843 := bstep (se 1 (by rfl) ⟨1121882, by rfl⟩ : syracuseStep 1495843 = 2243765) B2243765
theorem B2241329 : Blo 1494067 2241329 := bstep (se 2 (by rfl) ⟨840498, by rfl⟩ : syracuseStep 2241329 = 1680997) B1680997
theorem B1495859 : Blo 1494067 1495859 := bstep (se 1 (by rfl) ⟨1121894, by rfl⟩ : syracuseStep 1495859 = 2243789) B2243789
theorem B2241347 : Blo 1494067 2241347 := bstep (se 1 (by rfl) ⟨1681010, by rfl⟩ : syracuseStep 2241347 = 3362021) B3362021
theorem B1495875 : Blo 1494067 1495875 := bstep (se 1 (by rfl) ⟨1121906, by rfl⟩ : syracuseStep 1495875 = 2243813) B2243813
theorem B1495891 : Blo 1494067 1495891 := bstep (se 1 (by rfl) ⟨1121918, by rfl⟩ : syracuseStep 1495891 = 2243837) B2243837
theorem B2241377 : Blo 1494067 2241377 := bstep (se 2 (by rfl) ⟨840516, by rfl⟩ : syracuseStep 2241377 = 1681033) B1681033
theorem B1495907 : Blo 1494067 1495907 := bstep (se 1 (by rfl) ⟨1121930, by rfl⟩ : syracuseStep 1495907 = 2243861) B2243861
theorem B4256621 : Blo 1494067 4256621 := bstep (se 3 (by rfl) ⟨798116, by rfl⟩ : syracuseStep 4256621 = 1596233) B1596233
theorem B2241395 : Blo 1494067 2241395 := bstep (se 1 (by rfl) ⟨1681046, by rfl⟩ : syracuseStep 2241395 = 3362093) B3362093
theorem B1495923 : Blo 1494067 1495923 := bstep (se 1 (by rfl) ⟨1121942, by rfl⟩ : syracuseStep 1495923 = 2243885) B2243885
theorem B1495939 : Blo 1494067 1495939 := bstep (se 1 (by rfl) ⟨1121954, by rfl⟩ : syracuseStep 1495939 = 2243909) B2243909
theorem B17027981 : Blo 1494067 17027981 := bstep (se 3 (by rfl) ⟨3192746, by rfl⟩ : syracuseStep 17027981 = 6385493) B6385493
theorem B2241425 : Blo 1494067 2241425 := bstep (se 2 (by rfl) ⟨840534, by rfl⟩ : syracuseStep 2241425 = 1681069) B1681069
theorem B1495955 : Blo 1494067 1495955 := bstep (se 1 (by rfl) ⟨1121966, by rfl⟩ : syracuseStep 1495955 = 2243933) B2243933
theorem B2241443 : Blo 1494067 2241443 := bstep (se 1 (by rfl) ⟨1681082, by rfl⟩ : syracuseStep 2241443 = 3362165) B3362165
theorem B1495971 : Blo 1494067 1495971 := bstep (se 1 (by rfl) ⟨1121978, by rfl⟩ : syracuseStep 1495971 = 2243957) B2243957
theorem B1495987 : Blo 1494067 1495987 := bstep (se 1 (by rfl) ⟨1121990, by rfl⟩ : syracuseStep 1495987 = 2243981) B2243981
theorem B2241473 : Blo 1494067 2241473 := bstep (se 2 (by rfl) ⟨840552, by rfl⟩ : syracuseStep 2241473 = 1681105) B1681105
theorem B1496003 : Blo 1494067 1496003 := bstep (se 1 (by rfl) ⟨1122002, by rfl⟩ : syracuseStep 1496003 = 2244005) B2244005
theorem B2241491 : Blo 1494067 2241491 := bstep (se 1 (by rfl) ⟨1681118, by rfl⟩ : syracuseStep 2241491 = 3362237) B3362237
theorem B1496019 : Blo 1494067 1496019 := bstep (se 1 (by rfl) ⟨1122014, by rfl⟩ : syracuseStep 1496019 = 2244029) B2244029
theorem B1496035 : Blo 1494067 1496035 := bstep (se 1 (by rfl) ⟨1122026, by rfl⟩ : syracuseStep 1496035 = 2244053) B2244053
theorem B2241521 : Blo 1494067 2241521 := bstep (se 2 (by rfl) ⟨840570, by rfl⟩ : syracuseStep 2241521 = 1681141) B1681141
theorem B1496051 : Blo 1494067 1496051 := bstep (se 1 (by rfl) ⟨1122038, by rfl⟩ : syracuseStep 1496051 = 2244077) B2244077
theorem B2241539 : Blo 1494067 2241539 := bstep (se 1 (by rfl) ⟨1681154, by rfl⟩ : syracuseStep 2241539 = 3362309) B3362309
theorem B1496067 : Blo 1494067 1496067 := bstep (se 1 (by rfl) ⟨1122050, by rfl⟩ : syracuseStep 1496067 = 2244101) B2244101
theorem B3191825 : Blo 1494067 3191825 := bstep (se 2 (by rfl) ⟨1196934, by rfl⟩ : syracuseStep 3191825 = 2393869) B2393869
theorem B3363857 : Blo 1494067 3363857 := bstep (se 2 (by rfl) ⟨1261446, by rfl⟩ : syracuseStep 3363857 = 2522893) B2522893
theorem B2241569 : Blo 1494067 2241569 := bstep (se 2 (by rfl) ⟨840588, by rfl⟩ : syracuseStep 2241569 = 1681177) B1681177
theorem B7566371 : Blo 1494067 7566371 := bstep (se 1 (by rfl) ⟨5674778, by rfl⟩ : syracuseStep 7566371 = 11349557) B11349557
theorem B3363875 : Blo 1494067 3363875 := bstep (se 1 (by rfl) ⟨2522906, by rfl⟩ : syracuseStep 3363875 = 5045813) B5045813
theorem B4256813 : Blo 1494067 4256813 := bstep (se 3 (by rfl) ⟨798152, by rfl⟩ : syracuseStep 4256813 = 1596305) B1596305
theorem B2241587 : Blo 1494067 2241587 := bstep (se 1 (by rfl) ⟨1681190, by rfl⟩ : syracuseStep 2241587 = 3362381) B3362381
theorem B4789325 : Blo 1494067 4789325 := bstep (se 3 (by rfl) ⟨897998, by rfl⟩ : syracuseStep 4789325 = 1795997) B1795997
theorem B2241617 : Blo 1494067 2241617 := bstep (se 2 (by rfl) ⟨840606, by rfl⟩ : syracuseStep 2241617 = 1681213) B1681213
theorem B2241635 : Blo 1494067 2241635 := bstep (se 1 (by rfl) ⟨1681226, by rfl⟩ : syracuseStep 2241635 = 3362453) B3362453
theorem B19166321 : Blo 1494067 19166321 := bstep (se 2 (by rfl) ⟨7187370, by rfl⟩ : syracuseStep 19166321 = 14374741) B14374741
theorem B2241665 : Blo 1494067 2241665 := bstep (se 2 (by rfl) ⟨840624, by rfl⟩ : syracuseStep 2241665 = 1681249) B1681249
theorem B2241683 : Blo 1494067 2241683 := bstep (se 1 (by rfl) ⟨1681262, by rfl⟩ : syracuseStep 2241683 = 3362525) B3362525
theorem B8516771 : Blo 1494067 8516771 := bstep (se 1 (by rfl) ⟨6387578, by rfl⟩ : syracuseStep 8516771 = 12775157) B12775157
theorem B3454129 : Blo 1494067 3454129 := bstep (se 2 (by rfl) ⟨1295298, by rfl⟩ : syracuseStep 3454129 = 2590597) B2590597
theorem B2241713 : Blo 1494067 2241713 := bstep (se 2 (by rfl) ⟨840642, by rfl⟩ : syracuseStep 2241713 = 1681285) B1681285
theorem B2241731 : Blo 1494067 2241731 := bstep (se 1 (by rfl) ⟨1681298, by rfl⟩ : syracuseStep 2241731 = 3362597) B3362597
theorem B2241761 : Blo 1494067 2241761 := bstep (se 2 (by rfl) ⟨840660, by rfl⟩ : syracuseStep 2241761 = 1681321) B1681321
theorem B5043437 : Blo 1494067 5043437 := bstep (se 3 (by rfl) ⟨945644, by rfl⟩ : syracuseStep 5043437 = 1891289) B1891289
theorem B2241779 : Blo 1494067 2241779 := bstep (se 1 (by rfl) ⟨1681334, by rfl⟩ : syracuseStep 2241779 = 3362669) B3362669
theorem B2241809 : Blo 1494067 2241809 := bstep (se 2 (by rfl) ⟨840678, by rfl⟩ : syracuseStep 2241809 = 1681357) B1681357
theorem B2020627 : Blo 1494067 2020627 := bstep (se 1 (by rfl) ⟨1515470, by rfl⟩ : syracuseStep 2020627 = 3030941) B3030941
theorem B5043491 : Blo 1494067 5043491 := bstep (se 1 (by rfl) ⟨3782618, by rfl⟩ : syracuseStep 5043491 = 7565237) B7565237
theorem B2241827 : Blo 1494067 2241827 := bstep (se 1 (by rfl) ⟨1681370, by rfl⟩ : syracuseStep 2241827 = 3362741) B3362741
theorem B3364145 : Blo 1494067 3364145 := bstep (se 2 (by rfl) ⟨1261554, by rfl⟩ : syracuseStep 3364145 = 2523109) B2523109
theorem B2241857 : Blo 1494067 2241857 := bstep (se 2 (by rfl) ⟨840696, by rfl⟩ : syracuseStep 2241857 = 1681393) B1681393
theorem B3364163 : Blo 1494067 3364163 := bstep (se 1 (by rfl) ⟨2523122, by rfl⟩ : syracuseStep 3364163 = 5046245) B5046245
theorem B2692433 : Blo 1494067 2692433 := bstep (se 2 (by rfl) ⟨1009662, by rfl⟩ : syracuseStep 2692433 = 2019325) B2019325
theorem B2241875 : Blo 1494067 2241875 := bstep (se 1 (by rfl) ⟨1681406, by rfl⟩ : syracuseStep 2241875 = 3362813) B3362813
theorem B2241905 : Blo 1494067 2241905 := bstep (se 2 (by rfl) ⟨840714, by rfl⟩ : syracuseStep 2241905 = 1681429) B1681429
theorem B7673201 : Blo 1494067 7673201 := bstep (se 2 (by rfl) ⟨2877450, by rfl⟩ : syracuseStep 7673201 = 5754901) B5754901
theorem B2241923 : Blo 1494067 2241923 := bstep (se 1 (by rfl) ⟨1681442, by rfl⟩ : syracuseStep 2241923 = 3362885) B3362885
theorem B38303117 : Blo 1494067 38303117 := bstep (se 3 (by rfl) ⟨7181834, by rfl⟩ : syracuseStep 38303117 = 14363669) B14363669
theorem B2241953 : Blo 1494067 2241953 := bstep (se 2 (by rfl) ⟨840732, by rfl⟩ : syracuseStep 2241953 = 1681465) B1681465
theorem B2241971 : Blo 1494067 2241971 := bstep (se 1 (by rfl) ⟨1681478, by rfl⟩ : syracuseStep 2241971 = 3362957) B3362957
theorem B82900421 : Blo 1494067 82900421 := bstep (se 4 (by rfl) ⟨7771914, by rfl⟩ : syracuseStep 82900421 = 15543829) B15543829
theorem B5674445 : Blo 1494067 5674445 := bstep (se 3 (by rfl) ⟨1063958, by rfl⟩ : syracuseStep 5674445 = 2127917) B2127917
theorem B2127313 : Blo 1494067 2127313 := bstep (se 2 (by rfl) ⟨797742, by rfl⟩ : syracuseStep 2127313 = 1595485) B1595485
theorem B2242001 : Blo 1494067 2242001 := bstep (se 2 (by rfl) ⟨840750, by rfl⟩ : syracuseStep 2242001 = 1681501) B1681501
theorem B2840017 : Blo 1494067 2840017 := bstep (se 2 (by rfl) ⟨1065006, by rfl⟩ : syracuseStep 2840017 = 2130013) B2130013
theorem B2242019 : Blo 1494067 2242019 := bstep (se 1 (by rfl) ⟨1681514, by rfl⟩ : syracuseStep 2242019 = 3363029) B3363029
theorem B6911459 : Blo 1494067 6911459 := bstep (se 1 (by rfl) ⟨5183594, by rfl⟩ : syracuseStep 6911459 = 10367189) B10367189
theorem B2242049 : Blo 1494067 2242049 := bstep (se 2 (by rfl) ⟨840768, by rfl⟩ : syracuseStep 2242049 = 1681537) B1681537
theorem B4789763 : Blo 1494067 4789763 := bstep (se 1 (by rfl) ⟨3592322, by rfl⟩ : syracuseStep 4789763 = 7184645) B7184645
theorem B2242067 : Blo 1494067 2242067 := bstep (se 1 (by rfl) ⟨1681550, by rfl⟩ : syracuseStep 2242067 = 3363101) B3363101
theorem B5043761 : Blo 1494067 5043761 := bstep (se 2 (by rfl) ⟨1891410, by rfl⟩ : syracuseStep 5043761 = 3782821) B3782821
theorem B2242097 : Blo 1494067 2242097 := bstep (se 2 (by rfl) ⟨840786, by rfl⟩ : syracuseStep 2242097 = 1681573) B1681573
theorem B2242115 : Blo 1494067 2242115 := bstep (se 1 (by rfl) ⟨1681586, by rfl⟩ : syracuseStep 2242115 = 3363173) B3363173
theorem B3364433 : Blo 1494067 3364433 := bstep (se 2 (by rfl) ⟨1261662, by rfl⟩ : syracuseStep 3364433 = 2523325) B2523325
theorem B2242145 : Blo 1494067 2242145 := bstep (se 2 (by rfl) ⟨840804, by rfl⟩ : syracuseStep 2242145 = 1681609) B1681609
theorem B3364451 : Blo 1494067 3364451 := bstep (se 1 (by rfl) ⟨2523338, by rfl⟩ : syracuseStep 3364451 = 5046677) B5046677
theorem B2692721 : Blo 1494067 2692721 := bstep (se 2 (by rfl) ⟨1009770, by rfl⟩ : syracuseStep 2692721 = 2019541) B2019541
theorem B2840177 : Blo 1494067 2840177 := bstep (se 2 (by rfl) ⟨1065066, by rfl⟩ : syracuseStep 2840177 = 2130133) B2130133
theorem B2242163 : Blo 1494067 2242163 := bstep (se 1 (by rfl) ⟨1681622, by rfl⟩ : syracuseStep 2242163 = 3363245) B3363245
theorem B2242193 : Blo 1494067 2242193 := bstep (se 2 (by rfl) ⟨840822, by rfl⟩ : syracuseStep 2242193 = 1681645) B1681645
theorem B2242211 : Blo 1494067 2242211 := bstep (se 1 (by rfl) ⟨1681658, by rfl⟩ : syracuseStep 2242211 = 3363317) B3363317
theorem B2242241 : Blo 1494067 2242241 := bstep (se 2 (by rfl) ⟨840840, by rfl⟩ : syracuseStep 2242241 = 1681681) B1681681
theorem B2242259 : Blo 1494067 2242259 := bstep (se 1 (by rfl) ⟨1681694, by rfl⟩ : syracuseStep 2242259 = 3363389) B3363389
theorem B2242289 : Blo 1494067 2242289 := bstep (se 2 (by rfl) ⟨840858, by rfl⟩ : syracuseStep 2242289 = 1681717) B1681717
theorem B2242307 : Blo 1494067 2242307 := bstep (se 1 (by rfl) ⟨1681730, by rfl⟩ : syracuseStep 2242307 = 3363461) B3363461
theorem B2242337 : Blo 1494067 2242337 := bstep (se 2 (by rfl) ⟨840876, by rfl⟩ : syracuseStep 2242337 = 1681753) B1681753
theorem B2242355 : Blo 1494067 2242355 := bstep (se 1 (by rfl) ⟨1681766, by rfl⟩ : syracuseStep 2242355 = 3363533) B3363533
theorem B7567181 : Blo 1494067 7567181 := bstep (se 3 (by rfl) ⟨1418846, by rfl⟩ : syracuseStep 7567181 = 2837693) B2837693
theorem B2242385 : Blo 1494067 2242385 := bstep (se 2 (by rfl) ⟨840894, by rfl⟩ : syracuseStep 2242385 = 1681789) B1681789
theorem B2242403 : Blo 1494067 2242403 := bstep (se 1 (by rfl) ⟨1681802, by rfl⟩ : syracuseStep 2242403 = 3363605) B3363605
theorem B3364721 : Blo 1494067 3364721 := bstep (se 2 (by rfl) ⟨1261770, by rfl⟩ : syracuseStep 3364721 = 2523541) B2523541
theorem B2242433 : Blo 1494067 2242433 := bstep (se 2 (by rfl) ⟨840912, by rfl⟩ : syracuseStep 2242433 = 1681825) B1681825
theorem B3364739 : Blo 1494067 3364739 := bstep (se 1 (by rfl) ⟨2523554, by rfl⟩ : syracuseStep 3364739 = 5047109) B5047109
theorem B2242451 : Blo 1494067 2242451 := bstep (se 1 (by rfl) ⟨1681838, by rfl⟩ : syracuseStep 2242451 = 3363677) B3363677
theorem B9574321 : Blo 1494067 9574321 := bstep (se 2 (by rfl) ⟨3590370, by rfl⟩ : syracuseStep 9574321 = 7180741) B7180741
theorem B2242481 : Blo 1494067 2242481 := bstep (se 2 (by rfl) ⟨840930, by rfl⟩ : syracuseStep 2242481 = 1681861) B1681861
theorem B2127809 : Blo 1494067 2127809 := bstep (se 2 (by rfl) ⟨797928, by rfl⟩ : syracuseStep 2127809 = 1595857) B1595857
theorem B2242499 : Blo 1494067 2242499 := bstep (se 1 (by rfl) ⟨1681874, by rfl⟩ : syracuseStep 2242499 = 3363749) B3363749
theorem B21010373 : Blo 1494067 21010373 := bstep (se 4 (by rfl) ⟨1969722, by rfl⟩ : syracuseStep 21010373 = 3939445) B3939445
theorem B3782609 : Blo 1494067 3782609 := bstep (se 2 (by rfl) ⟨1418478, by rfl⟩ : syracuseStep 3782609 = 2836957) B2836957
theorem B2242529 : Blo 1494067 2242529 := bstep (se 2 (by rfl) ⟨840948, by rfl⟩ : syracuseStep 2242529 = 1681897) B1681897
theorem B2242547 : Blo 1494067 2242547 := bstep (se 1 (by rfl) ⟨1681910, by rfl⟩ : syracuseStep 2242547 = 3363821) B3363821
theorem B3782659 : Blo 1494067 3782659 := bstep (se 1 (by rfl) ⟨2836994, by rfl⟩ : syracuseStep 3782659 = 5673989) B5673989
theorem B4257805 : Blo 1494067 4257805 := bstep (se 3 (by rfl) ⟨798338, by rfl⟩ : syracuseStep 4257805 = 1596677) B1596677
theorem B2242577 : Blo 1494067 2242577 := bstep (se 2 (by rfl) ⟨840966, by rfl⟩ : syracuseStep 2242577 = 1681933) B1681933
theorem B2242595 : Blo 1494067 2242595 := bstep (se 1 (by rfl) ⟨1681946, by rfl⟩ : syracuseStep 2242595 = 3363893) B3363893
theorem B4544561 : Blo 1494067 4544561 := bstep (se 2 (by rfl) ⟨1704210, by rfl⟩ : syracuseStep 4544561 = 3408421) B3408421
theorem B2242625 : Blo 1494067 2242625 := bstep (se 2 (by rfl) ⟨840984, by rfl⟩ : syracuseStep 2242625 = 1681969) B1681969
theorem B8198213 : Blo 1494067 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B5044301 : Blo 1494067 5044301 := bstep (se 3 (by rfl) ⟨945806, by rfl⟩ : syracuseStep 5044301 = 1891613) B1891613
theorem B2242643 : Blo 1494067 2242643 := bstep (se 1 (by rfl) ⟨1681982, by rfl⟩ : syracuseStep 2242643 = 3363965) B3363965
theorem B2242673 : Blo 1494067 2242673 := bstep (se 2 (by rfl) ⟨841002, by rfl⟩ : syracuseStep 2242673 = 1682005) B1682005
theorem B5044355 : Blo 1494067 5044355 := bstep (se 1 (by rfl) ⟨3783266, by rfl⟩ : syracuseStep 5044355 = 7566533) B7566533
theorem B2242691 : Blo 1494067 2242691 := bstep (se 1 (by rfl) ⟨1682018, by rfl⟩ : syracuseStep 2242691 = 3364037) B3364037
theorem B3782801 : Blo 1494067 3782801 := bstep (se 2 (by rfl) ⟨1418550, by rfl⟩ : syracuseStep 3782801 = 2837101) B2837101
theorem B3365009 : Blo 1494067 3365009 := bstep (se 2 (by rfl) ⟨1261878, by rfl⟩ : syracuseStep 3365009 = 2523757) B2523757
theorem B2242721 : Blo 1494067 2242721 := bstep (se 2 (by rfl) ⟨841020, by rfl⟩ : syracuseStep 2242721 = 1682041) B1682041
theorem B3365027 : Blo 1494067 3365027 := bstep (se 1 (by rfl) ⟨2523770, by rfl⟩ : syracuseStep 3365027 = 5047541) B5047541
theorem B2242739 : Blo 1494067 2242739 := bstep (se 1 (by rfl) ⟨1682054, by rfl⟩ : syracuseStep 2242739 = 3364109) B3364109
theorem B2242769 : Blo 1494067 2242769 := bstep (se 2 (by rfl) ⟨841038, by rfl⟩ : syracuseStep 2242769 = 1682077) B1682077
theorem B2242787 : Blo 1494067 2242787 := bstep (se 1 (by rfl) ⟨1682090, by rfl⟩ : syracuseStep 2242787 = 3364181) B3364181
theorem B2242817 : Blo 1494067 2242817 := bstep (se 2 (by rfl) ⟨841056, by rfl⟩ : syracuseStep 2242817 = 1682113) B1682113
theorem B2521361 : Blo 1494067 2521361 := bstep (se 2 (by rfl) ⟨945510, by rfl⟩ : syracuseStep 2521361 = 1891021) B1891021
theorem B2242835 : Blo 1494067 2242835 := bstep (se 1 (by rfl) ⟨1682126, by rfl⟩ : syracuseStep 2242835 = 3364253) B3364253
theorem B3193123 : Blo 1494067 3193123 := bstep (se 1 (by rfl) ⟨2394842, by rfl⟩ : syracuseStep 3193123 = 4789685) B4789685
theorem B2242865 : Blo 1494067 2242865 := bstep (se 2 (by rfl) ⟨841074, by rfl⟩ : syracuseStep 2242865 = 1682149) B1682149
theorem B2242883 : Blo 1494067 2242883 := bstep (se 1 (by rfl) ⟨1682162, by rfl⟩ : syracuseStep 2242883 = 3364325) B3364325
theorem B2242913 : Blo 1494067 2242913 := bstep (se 2 (by rfl) ⟨841092, by rfl⟩ : syracuseStep 2242913 = 1682185) B1682185
theorem B2242931 : Blo 1494067 2242931 := bstep (se 1 (by rfl) ⟨1682198, by rfl⟩ : syracuseStep 2242931 = 3364397) B3364397
theorem B2521489 : Blo 1494067 2521489 := bstep (se 2 (by rfl) ⟨945558, by rfl⟩ : syracuseStep 2521489 = 1891117) B1891117
theorem B5044625 : Blo 1494067 5044625 := bstep (se 2 (by rfl) ⟨1891734, by rfl⟩ : syracuseStep 5044625 = 3783469) B3783469
theorem B2242961 : Blo 1494067 2242961 := bstep (se 2 (by rfl) ⟨841110, by rfl⟩ : syracuseStep 2242961 = 1682221) B1682221
theorem B2242979 : Blo 1494067 2242979 := bstep (se 1 (by rfl) ⟨1682234, by rfl⟩ : syracuseStep 2242979 = 3364469) B3364469
theorem B8632739 : Blo 1494067 8632739 := bstep (se 1 (by rfl) ⟨6474554, by rfl⟩ : syracuseStep 8632739 = 12949109) B12949109
theorem B3365297 : Blo 1494067 3365297 := bstep (se 2 (by rfl) ⟨1261986, by rfl⟩ : syracuseStep 3365297 = 2523973) B2523973
theorem B2521523 : Blo 1494067 2521523 := bstep (se 1 (by rfl) ⟨1891142, by rfl⟩ : syracuseStep 2521523 = 3782285) B3782285
theorem B2243009 : Blo 1494067 2243009 := bstep (se 2 (by rfl) ⟨841128, by rfl⟩ : syracuseStep 2243009 = 1682257) B1682257
theorem B3365315 : Blo 1494067 3365315 := bstep (se 1 (by rfl) ⟨2523986, by rfl⟩ : syracuseStep 3365315 = 5047973) B5047973
theorem B4610513 : Blo 1494067 4610513 := bstep (se 2 (by rfl) ⟨1728942, by rfl⟩ : syracuseStep 4610513 = 3457885) B3457885
theorem B2243027 : Blo 1494067 2243027 := bstep (se 1 (by rfl) ⟨1682270, by rfl⟩ : syracuseStep 2243027 = 3364541) B3364541
theorem B2243057 : Blo 1494067 2243057 := bstep (se 2 (by rfl) ⟨841146, by rfl⟩ : syracuseStep 2243057 = 1682293) B1682293
theorem B2243075 : Blo 1494067 2243075 := bstep (se 1 (by rfl) ⟨1682306, by rfl⟩ : syracuseStep 2243075 = 3364613) B3364613
theorem B2243105 : Blo 1494067 2243105 := bstep (se 2 (by rfl) ⟨841164, by rfl⟩ : syracuseStep 2243105 = 1682329) B1682329
theorem B2521651 : Blo 1494067 2521651 := bstep (se 1 (by rfl) ⟨1891238, by rfl⟩ : syracuseStep 2521651 = 3782477) B3782477
theorem B2243123 : Blo 1494067 2243123 := bstep (se 1 (by rfl) ⟨1682342, by rfl⟩ : syracuseStep 2243123 = 3364685) B3364685
theorem B2243153 : Blo 1494067 2243153 := bstep (se 2 (by rfl) ⟨841182, by rfl⟩ : syracuseStep 2243153 = 1682365) B1682365
theorem B12122723 : Blo 1494067 12122723 := bstep (se 1 (by rfl) ⟨9092042, by rfl⟩ : syracuseStep 12122723 = 18184085) B18184085
theorem B2243171 : Blo 1494067 2243171 := bstep (se 1 (by rfl) ⟨1682378, by rfl⟩ : syracuseStep 2243171 = 3364757) B3364757
theorem B2243201 : Blo 1494067 2243201 := bstep (se 2 (by rfl) ⟨841200, by rfl⟩ : syracuseStep 2243201 = 1682401) B1682401
theorem B7182989 : Blo 1494067 7182989 := bstep (se 3 (by rfl) ⟨1346810, by rfl⟩ : syracuseStep 7182989 = 2693621) B2693621
theorem B2243219 : Blo 1494067 2243219 := bstep (se 1 (by rfl) ⟨1682414, by rfl⟩ : syracuseStep 2243219 = 3364829) B3364829
theorem B2243249 : Blo 1494067 2243249 := bstep (se 2 (by rfl) ⟨841218, by rfl⟩ : syracuseStep 2243249 = 1682437) B1682437
theorem B1596083 : Blo 1494067 1596083 := bstep (se 1 (by rfl) ⟨1197062, by rfl⟩ : syracuseStep 1596083 = 2394125) B2394125
theorem B2521793 : Blo 1494067 2521793 := bstep (se 2 (by rfl) ⟨945672, by rfl⟩ : syracuseStep 2521793 = 1891345) B1891345
theorem B2243267 : Blo 1494067 2243267 := bstep (se 1 (by rfl) ⟨1682450, by rfl⟩ : syracuseStep 2243267 = 3364901) B3364901
theorem B3365585 : Blo 1494067 3365585 := bstep (se 2 (by rfl) ⟨1262094, by rfl⟩ : syracuseStep 3365585 = 2524189) B2524189
theorem B2243297 : Blo 1494067 2243297 := bstep (se 2 (by rfl) ⟨841236, by rfl⟩ : syracuseStep 2243297 = 1682473) B1682473
theorem B3365603 : Blo 1494067 3365603 := bstep (se 1 (by rfl) ⟨2524202, by rfl⟩ : syracuseStep 3365603 = 5048405) B5048405
theorem B2243315 : Blo 1494067 2243315 := bstep (se 1 (by rfl) ⟨1682486, by rfl⟩ : syracuseStep 2243315 = 3364973) B3364973
theorem B4315907 : Blo 1494067 4315907 := bstep (se 1 (by rfl) ⟨3236930, by rfl⟩ : syracuseStep 4315907 = 6473861) B6473861
theorem B8190725 : Blo 1494067 8190725 := bstep (se 4 (by rfl) ⟨767880, by rfl⟩ : syracuseStep 8190725 = 1535761) B1535761
theorem B2243345 : Blo 1494067 2243345 := bstep (se 2 (by rfl) ⟨841254, by rfl⟩ : syracuseStep 2243345 = 1682509) B1682509
theorem B2128675 : Blo 1494067 2128675 := bstep (se 1 (by rfl) ⟨1596506, by rfl⟩ : syracuseStep 2128675 = 3193013) B3193013
theorem B2243363 : Blo 1494067 2243363 := bstep (se 1 (by rfl) ⟨1682522, by rfl⟩ : syracuseStep 2243363 = 3365045) B3365045
theorem B2521921 : Blo 1494067 2521921 := bstep (se 2 (by rfl) ⟨945720, by rfl⟩ : syracuseStep 2521921 = 1891441) B1891441
theorem B2243393 : Blo 1494067 2243393 := bstep (se 2 (by rfl) ⟨841272, by rfl⟩ : syracuseStep 2243393 = 1682545) B1682545
theorem B2243411 : Blo 1494067 2243411 := bstep (se 1 (by rfl) ⟨1682558, by rfl⟩ : syracuseStep 2243411 = 3365117) B3365117
theorem B2521955 : Blo 1494067 2521955 := bstep (se 1 (by rfl) ⟨1891466, by rfl⟩ : syracuseStep 2521955 = 3782933) B3782933
theorem B2243441 : Blo 1494067 2243441 := bstep (se 2 (by rfl) ⟨841290, by rfl⟩ : syracuseStep 2243441 = 1682581) B1682581
theorem B2128771 : Blo 1494067 2128771 := bstep (se 1 (by rfl) ⟨1596578, by rfl⟩ : syracuseStep 2128771 = 3193157) B3193157
theorem B2243459 : Blo 1494067 2243459 := bstep (se 1 (by rfl) ⟨1682594, by rfl⟩ : syracuseStep 2243459 = 3365189) B3365189
theorem B2243489 : Blo 1494067 2243489 := bstep (se 2 (by rfl) ⟨841308, by rfl⟩ : syracuseStep 2243489 = 1682617) B1682617
theorem B5045165 : Blo 1494067 5045165 := bstep (se 3 (by rfl) ⟨945968, by rfl⟩ : syracuseStep 5045165 = 1891937) B1891937
theorem B2243507 : Blo 1494067 2243507 := bstep (se 1 (by rfl) ⟨1682630, by rfl⟩ : syracuseStep 2243507 = 3365261) B3365261
theorem B9714637 : Blo 1494067 9714637 := bstep (se 3 (by rfl) ⟨1821494, by rfl⟩ : syracuseStep 9714637 = 3642989) B3642989
theorem B2243537 : Blo 1494067 2243537 := bstep (se 2 (by rfl) ⟨841326, by rfl⟩ : syracuseStep 2243537 = 1682653) B1682653
theorem B2522083 : Blo 1494067 2522083 := bstep (se 1 (by rfl) ⟨1891562, by rfl⟩ : syracuseStep 2522083 = 3783125) B3783125
theorem B5045219 : Blo 1494067 5045219 := bstep (se 1 (by rfl) ⟨3783914, by rfl⟩ : syracuseStep 5045219 = 7567829) B7567829
theorem B2243555 : Blo 1494067 2243555 := bstep (se 1 (by rfl) ⟨1682666, by rfl⟩ : syracuseStep 2243555 = 3365333) B3365333
theorem B3365873 : Blo 1494067 3365873 := bstep (se 2 (by rfl) ⟨1262202, by rfl⟩ : syracuseStep 3365873 = 2524405) B2524405
theorem B2243585 : Blo 1494067 2243585 := bstep (se 2 (by rfl) ⟨841344, by rfl⟩ : syracuseStep 2243585 = 1682689) B1682689
theorem B3365891 : Blo 1494067 3365891 := bstep (se 1 (by rfl) ⟨2524418, by rfl⟩ : syracuseStep 3365891 = 5048837) B5048837
theorem B2243603 : Blo 1494067 2243603 := bstep (se 1 (by rfl) ⟨1682702, by rfl⟩ : syracuseStep 2243603 = 3365405) B3365405
theorem B2243633 : Blo 1494067 2243633 := bstep (se 2 (by rfl) ⟨841362, by rfl⟩ : syracuseStep 2243633 = 1682725) B1682725
theorem B2243651 : Blo 1494067 2243651 := bstep (se 1 (by rfl) ⟨1682738, by rfl⟩ : syracuseStep 2243651 = 3365477) B3365477
theorem B19168325 : Blo 1494067 19168325 := bstep (se 4 (by rfl) ⟨1797030, by rfl⟩ : syracuseStep 19168325 = 3594061) B3594061
theorem B2243681 : Blo 1494067 2243681 := bstep (se 2 (by rfl) ⟨841380, by rfl⟩ : syracuseStep 2243681 = 1682761) B1682761
theorem B2522225 : Blo 1494067 2522225 := bstep (se 2 (by rfl) ⟨945834, by rfl⟩ : syracuseStep 2522225 = 1891669) B1891669
theorem B3783793 : Blo 1494067 3783793 := bstep (se 2 (by rfl) ⟨1418922, by rfl⟩ : syracuseStep 3783793 = 2837845) B2837845
theorem B6061169 : Blo 1494067 6061169 := bstep (se 2 (by rfl) ⟨2272938, by rfl⟩ : syracuseStep 6061169 = 4545877) B4545877
theorem B2243699 : Blo 1494067 2243699 := bstep (se 1 (by rfl) ⟨1682774, by rfl⟩ : syracuseStep 2243699 = 3365549) B3365549
theorem B2243729 : Blo 1494067 2243729 := bstep (se 2 (by rfl) ⟨841398, by rfl⟩ : syracuseStep 2243729 = 1682797) B1682797
theorem B2243747 : Blo 1494067 2243747 := bstep (se 1 (by rfl) ⟨1682810, by rfl⟩ : syracuseStep 2243747 = 3365621) B3365621
theorem B1891507 : Blo 1494067 1891507 := bstep (se 1 (by rfl) ⟨1418630, by rfl⟩ : syracuseStep 1891507 = 2837261) B2837261
theorem B2243777 : Blo 1494067 2243777 := bstep (se 2 (by rfl) ⟨841416, by rfl⟩ : syracuseStep 2243777 = 1682833) B1682833
theorem B17022149 : Blo 1494067 17022149 := bstep (se 4 (by rfl) ⟨1595826, by rfl⟩ : syracuseStep 17022149 = 3191653) B3191653
theorem B2243795 : Blo 1494067 2243795 := bstep (se 1 (by rfl) ⟨1682846, by rfl⟩ : syracuseStep 2243795 = 3365693) B3365693
theorem B2522353 : Blo 1494067 2522353 := bstep (se 2 (by rfl) ⟨945882, by rfl⟩ : syracuseStep 2522353 = 1891765) B1891765
theorem B5045489 : Blo 1494067 5045489 := bstep (se 2 (by rfl) ⟨1892058, by rfl⟩ : syracuseStep 5045489 = 3784117) B3784117
theorem B2243825 : Blo 1494067 2243825 := bstep (se 2 (by rfl) ⟨841434, by rfl⟩ : syracuseStep 2243825 = 1682869) B1682869
theorem B2243843 : Blo 1494067 2243843 := bstep (se 1 (by rfl) ⟨1682882, by rfl⟩ : syracuseStep 2243843 = 3365765) B3365765
theorem B1891603 : Blo 1494067 1891603 := bstep (se 1 (by rfl) ⟨1418702, by rfl⟩ : syracuseStep 1891603 = 2837405) B2837405
theorem B2522387 : Blo 1494067 2522387 := bstep (se 1 (by rfl) ⟨1891790, by rfl⟩ : syracuseStep 2522387 = 3783581) B3783581
theorem B2243873 : Blo 1494067 2243873 := bstep (se 2 (by rfl) ⟨841452, by rfl⟩ : syracuseStep 2243873 = 1682905) B1682905
theorem B2243891 : Blo 1494067 2243891 := bstep (se 1 (by rfl) ⟨1682918, by rfl⟩ : syracuseStep 2243891 = 3365837) B3365837
theorem B2243921 : Blo 1494067 2243921 := bstep (se 2 (by rfl) ⟨841470, by rfl⟩ : syracuseStep 2243921 = 1682941) B1682941
theorem B2243939 : Blo 1494067 2243939 := bstep (se 1 (by rfl) ⟨1682954, by rfl⟩ : syracuseStep 2243939 = 3365909) B3365909
theorem B2129267 : Blo 1494067 2129267 := bstep (se 1 (by rfl) ⟨1596950, by rfl⟩ : syracuseStep 2129267 = 3193901) B3193901
theorem B2243969 : Blo 1494067 2243969 := bstep (se 2 (by rfl) ⟨841488, by rfl⟩ : syracuseStep 2243969 = 1682977) B1682977
theorem B3784067 : Blo 1494067 3784067 := bstep (se 1 (by rfl) ⟨2838050, by rfl⟩ : syracuseStep 3784067 = 5676101) B5676101
theorem B4791683 : Blo 1494067 4791683 := bstep (se 1 (by rfl) ⟨3593762, by rfl⟩ : syracuseStep 4791683 = 7187525) B7187525
theorem B2522515 : Blo 1494067 2522515 := bstep (se 1 (by rfl) ⟨1891886, by rfl⟩ : syracuseStep 2522515 = 3783773) B3783773
theorem B2243987 : Blo 1494067 2243987 := bstep (se 1 (by rfl) ⟨1682990, by rfl⟩ : syracuseStep 2243987 = 3365981) B3365981
theorem B1596835 : Blo 1494067 1596835 := bstep (se 1 (by rfl) ⟨1197626, by rfl⟩ : syracuseStep 1596835 = 2395253) B2395253
theorem B2244017 : Blo 1494067 2244017 := bstep (se 2 (by rfl) ⟨841506, by rfl⟩ : syracuseStep 2244017 = 1683013) B1683013
theorem B2244035 : Blo 1494067 2244035 := bstep (se 1 (by rfl) ⟨1683026, by rfl⟩ : syracuseStep 2244035 = 3366053) B3366053
theorem B2244065 : Blo 1494067 2244065 := bstep (se 2 (by rfl) ⟨841524, by rfl⟩ : syracuseStep 2244065 = 1683049) B1683049
theorem B6389219 : Blo 1494067 6389219 := bstep (se 1 (by rfl) ⟨4791914, by rfl⟩ : syracuseStep 6389219 = 9583829) B9583829
theorem B3194353 : Blo 1494067 3194353 := bstep (se 2 (by rfl) ⟨1197882, by rfl⟩ : syracuseStep 3194353 = 2395765) B2395765
theorem B2244083 : Blo 1494067 2244083 := bstep (se 1 (by rfl) ⟨1683062, by rfl⟩ : syracuseStep 2244083 = 3366125) B3366125
theorem B2522657 : Blo 1494067 2522657 := bstep (se 2 (by rfl) ⟨945996, by rfl⟩ : syracuseStep 2522657 = 1891993) B1891993
theorem B3784259 : Blo 1494067 3784259 := bstep (se 1 (by rfl) ⟨2838194, by rfl⟩ : syracuseStep 3784259 = 5676389) B5676389
theorem B2522785 : Blo 1494067 2522785 := bstep (se 2 (by rfl) ⟨946044, by rfl⟩ : syracuseStep 2522785 = 1892089) B1892089
theorem B1597091 : Blo 1494067 1597091 := bstep (se 1 (by rfl) ⟨1197818, by rfl⟩ : syracuseStep 1597091 = 2395637) B2395637
theorem B2522819 : Blo 1494067 2522819 := bstep (se 1 (by rfl) ⟨1892114, by rfl⟩ : syracuseStep 2522819 = 3784229) B3784229
theorem B4259537 : Blo 1494067 4259537 := bstep (se 2 (by rfl) ⟨1597326, by rfl⟩ : syracuseStep 4259537 = 3194653) B3194653
theorem B17030897 : Blo 1494067 17030897 := bstep (se 2 (by rfl) ⟨6386586, by rfl⟩ : syracuseStep 17030897 = 12773173) B12773173
theorem B1892099 : Blo 1494067 1892099 := bstep (se 1 (by rfl) ⟨1419074, by rfl⟩ : syracuseStep 1892099 = 2838149) B2838149
theorem B5046029 : Blo 1494067 5046029 := bstep (se 3 (by rfl) ⟨946130, by rfl⟩ : syracuseStep 5046029 = 1892261) B1892261
theorem B2522947 : Blo 1494067 2522947 := bstep (se 1 (by rfl) ⟨1892210, by rfl⟩ : syracuseStep 2522947 = 3784421) B3784421
theorem B5046083 : Blo 1494067 5046083 := bstep (se 1 (by rfl) ⟨3784562, by rfl⟩ : syracuseStep 5046083 = 7569125) B7569125
theorem B4259729 : Blo 1494067 4259729 := bstep (se 2 (by rfl) ⟨1597398, by rfl⟩ : syracuseStep 4259729 = 3194797) B3194797
theorem B2523089 : Blo 1494067 2523089 := bstep (se 2 (by rfl) ⟨946158, by rfl⟩ : syracuseStep 2523089 = 1892317) B1892317
theorem B2695121 : Blo 1494067 2695121 := bstep (se 2 (by rfl) ⟨1010670, by rfl⟩ : syracuseStep 2695121 = 2021341) B2021341
theorem B13828067 : Blo 1494067 13828067 := bstep (se 1 (by rfl) ⟨10371050, by rfl⟩ : syracuseStep 13828067 = 20742101) B20742101
theorem B2129905 : Blo 1494067 2129905 := bstep (se 2 (by rfl) ⟨798714, by rfl⟩ : syracuseStep 2129905 = 1597429) B1597429
theorem B5677073 : Blo 1494067 5677073 := bstep (se 2 (by rfl) ⟨2128902, by rfl⟩ : syracuseStep 5677073 = 4257805) B4257805
theorem B19169297 : Blo 1494067 19169297 := bstep (se 2 (by rfl) ⟨7188486, by rfl⟩ : syracuseStep 19169297 = 14376973) B14376973
theorem B87367733 : Blo 1494067 87367733 := bstep (se 5 (by rfl) ⟨4095362, by rfl⟩ : syracuseStep 87367733 = 8190725) B8190725
theorem B5390401 : Blo 1494067 5390401 := bstep (se 2 (by rfl) ⟨2021400, by rfl⟩ : syracuseStep 5390401 = 4042801) B4042801
theorem B12771533 : Blo 1494067 12771533 := bstep (se 3 (by rfl) ⟨2394662, by rfl⟩ : syracuseStep 12771533 = 4789325) B4789325
theorem B3784907 : Blo 1494067 3784907 := bstep (se 1 (by rfl) ⟨2838680, by rfl⟩ : syracuseStep 3784907 = 5677361) B5677361
theorem B2523467 : Blo 1494067 2523467 := bstep (se 1 (by rfl) ⟨1892600, by rfl⟩ : syracuseStep 2523467 = 3785201) B3785201
theorem B4260185 : Blo 1494067 4260185 := bstep (se 2 (by rfl) ⟨1597569, by rfl⟩ : syracuseStep 4260185 = 3195139) B3195139
theorem B9576805 : Blo 1494067 9576805 := bstep (se 4 (by rfl) ⟨897825, by rfl⟩ : syracuseStep 9576805 = 1795651) B1795651
theorem B1892747 : Blo 1494067 1892747 := bstep (se 1 (by rfl) ⟨1419560, by rfl⟩ : syracuseStep 1892747 = 2839121) B2839121
theorem B5046731 : Blo 1494067 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B2523595 : Blo 1494067 2523595 := bstep (se 1 (by rfl) ⟨1892696, by rfl⟩ : syracuseStep 2523595 = 3785393) B3785393
theorem B21299725 : Blo 1494067 21299725 := bstep (se 3 (by rfl) ⟨3993698, by rfl⟩ : syracuseStep 21299725 = 7987397) B7987397
theorem B9093649 : Blo 1494067 9093649 := bstep (se 2 (by rfl) ⟨3410118, by rfl⟩ : syracuseStep 9093649 = 6820237) B6820237
theorem B1704503 : Blo 1494067 1704503 := bstep (se 1 (by rfl) ⟨1278377, by rfl⟩ : syracuseStep 1704503 = 2556755) B2556755
theorem B6382145 : Blo 1494067 6382145 := bstep (se 2 (by rfl) ⟨2393304, by rfl⟩ : syracuseStep 6382145 = 4786609) B4786609
theorem B2523737 : Blo 1494067 2523737 := bstep (se 2 (by rfl) ⟨946401, by rfl⟩ : syracuseStep 2523737 = 1892803) B1892803
theorem B16155287 : Blo 1494067 16155287 := bstep (se 1 (by rfl) ⟨12116465, by rfl⟩ : syracuseStep 16155287 = 24232931) B24232931
theorem B25887413 : Blo 1494067 25887413 := bstep (se 5 (by rfl) ⟨1213472, by rfl⟩ : syracuseStep 25887413 = 2426945) B2426945
theorem B5047001 : Blo 1494067 5047001 := bstep (se 2 (by rfl) ⟨1892625, by rfl⟩ : syracuseStep 5047001 = 3785251) B3785251
theorem B2523865 : Blo 1494067 2523865 := bstep (se 2 (by rfl) ⟨946449, by rfl⟩ : syracuseStep 2523865 = 1892899) B1892899
theorem B5391107 : Blo 1494067 5391107 := bstep (se 1 (by rfl) ⟨4043330, by rfl⟩ : syracuseStep 5391107 = 8086661) B8086661
theorem B5677847 : Blo 1494067 5677847 := bstep (se 1 (by rfl) ⟨4258385, by rfl⟩ : syracuseStep 5677847 = 8516771) B8516771
theorem B27263861 : Blo 1494067 27263861 := bstep (se 5 (by rfl) ⟨1277993, by rfl⟩ : syracuseStep 27263861 = 2555987) B2555987
theorem B1794955 : Blo 1494067 1794955 := bstep (se 1 (by rfl) ⟨1346216, by rfl⟩ : syracuseStep 1794955 = 2692433) B2692433
theorem B25535411 : Blo 1494067 25535411 := bstep (se 1 (by rfl) ⟨19151558, by rfl⟩ : syracuseStep 25535411 = 38303117) B38303117
theorem B5678045 : Blo 1494067 5678045 := bstep (se 3 (by rfl) ⟨1064633, by rfl⟩ : syracuseStep 5678045 = 2129267) B2129267
theorem B1893451 : Blo 1494067 1893451 := bstep (se 1 (by rfl) ⟨1420088, by rfl⟩ : syracuseStep 1893451 = 2840177) B2840177
theorem B7570583 : Blo 1494067 7570583 := bstep (se 1 (by rfl) ⟨5677937, by rfl⟩ : syracuseStep 7570583 = 11355875) B11355875
theorem B3785879 : Blo 1494067 3785879 := bstep (se 1 (by rfl) ⟨2839409, by rfl⟩ : syracuseStep 3785879 = 5678819) B5678819
theorem B2524439 : Blo 1494067 2524439 := bstep (se 1 (by rfl) ⟨1893329, by rfl⟩ : syracuseStep 2524439 = 3786659) B3786659
theorem B5047703 : Blo 1494067 5047703 := bstep (se 1 (by rfl) ⟨3785777, by rfl⟩ : syracuseStep 5047703 = 7571555) B7571555
theorem B2524567 : Blo 1494067 2524567 := bstep (se 1 (by rfl) ⟨1893425, by rfl⟩ : syracuseStep 2524567 = 3786851) B3786851
theorem B2393497 : Blo 1494067 2393497 := bstep (se 2 (by rfl) ⟨897561, by rfl⟩ : syracuseStep 2393497 = 1795123) B1795123
theorem B6383069 : Blo 1494067 6383069 := bstep (se 3 (by rfl) ⟨1196825, by rfl⟩ : syracuseStep 6383069 = 2393651) B2393651
theorem B6817283 : Blo 1494067 6817283 := bstep (se 1 (by rfl) ⟨5112962, by rfl⟩ : syracuseStep 6817283 = 10225925) B10225925
theorem B1680907 : Blo 1494067 1680907 := bstep (se 1 (by rfl) ⟨1260680, by rfl⟩ : syracuseStep 1680907 = 2521361) B2521361
theorem B4605505 : Blo 1494067 4605505 := bstep (se 2 (by rfl) ⟨1727064, by rfl⟩ : syracuseStep 4605505 = 3454129) B3454129
theorem B6817355 : Blo 1494067 6817355 := bstep (se 1 (by rfl) ⟨5113016, by rfl⟩ : syracuseStep 6817355 = 10226033) B10226033
theorem B1681015 : Blo 1494067 1681015 := bstep (se 1 (by rfl) ⟨1260761, by rfl⟩ : syracuseStep 1681015 = 2521523) B2521523
theorem B1918603 : Blo 1494067 1918603 := bstep (se 1 (by rfl) ⟨1438952, by rfl⟩ : syracuseStep 1918603 = 2877905) B2877905
theorem B3073675 : Blo 1494067 3073675 := bstep (se 1 (by rfl) ⟨2305256, by rfl⟩ : syracuseStep 3073675 = 4610513) B4610513
theorem B1681195 : Blo 1494067 1681195 := bstep (se 1 (by rfl) ⟨1260896, by rfl⟩ : syracuseStep 1681195 = 2521793) B2521793
theorem B3786547 : Blo 1494067 3786547 := bstep (se 1 (by rfl) ⟨2839910, by rfl⟩ : syracuseStep 3786547 = 5679821) B5679821
theorem B1681303 : Blo 1494067 1681303 := bstep (se 1 (by rfl) ⟨1260977, by rfl⟩ : syracuseStep 1681303 = 2521955) B2521955
theorem B5048243 : Blo 1494067 5048243 := bstep (se 1 (by rfl) ⟨3786182, by rfl⟩ : syracuseStep 5048243 = 7572365) B7572365
theorem B3786689 : Blo 1494067 3786689 := bstep (se 2 (by rfl) ⟨1420008, by rfl⟩ : syracuseStep 3786689 = 2840017) B2840017
theorem B1681483 : Blo 1494067 1681483 := bstep (se 1 (by rfl) ⟨1261112, by rfl⟩ : syracuseStep 1681483 = 2522225) B2522225
theorem B4040779 : Blo 1494067 4040779 := bstep (se 1 (by rfl) ⟨3030584, by rfl⟩ : syracuseStep 4040779 = 6061169) B6061169
theorem B11348099 : Blo 1494067 11348099 := bstep (se 1 (by rfl) ⟨8511074, by rfl⟩ : syracuseStep 11348099 = 17022149) B17022149
theorem B1681591 : Blo 1494067 1681591 := bstep (se 1 (by rfl) ⟨1261193, by rfl⟩ : syracuseStep 1681591 = 2522387) B2522387
theorem B5048513 : Blo 1494067 5048513 := bstep (se 2 (by rfl) ⟨1893192, by rfl⟩ : syracuseStep 5048513 = 3786385) B3786385
theorem B2459927 : Blo 1494067 2459927 := bstep (se 1 (by rfl) ⟨1844945, by rfl⟩ : syracuseStep 2459927 = 3689891) B3689891
theorem B1681771 : Blo 1494067 1681771 := bstep (se 1 (by rfl) ⟨1261328, by rfl⟩ : syracuseStep 1681771 = 2522657) B2522657
theorem B2877889 : Blo 1494067 2877889 := bstep (se 2 (by rfl) ⟨1079208, by rfl⟩ : syracuseStep 2877889 = 2158417) B2158417
theorem B1681879 : Blo 1494067 1681879 := bstep (se 1 (by rfl) ⟨1261409, by rfl⟩ : syracuseStep 1681879 = 2522819) B2522819
theorem B12765761 : Blo 1494067 12765761 := bstep (se 2 (by rfl) ⟨4787160, by rfl⟩ : syracuseStep 12765761 = 9574321) B9574321
theorem B10783363 : Blo 1494067 10783363 := bstep (se 1 (by rfl) ⟨8087522, by rfl⟩ : syracuseStep 10783363 = 16175045) B16175045
theorem B1682059 : Blo 1494067 1682059 := bstep (se 1 (by rfl) ⟨1261544, by rfl⟩ : syracuseStep 1682059 = 2523089) B2523089
theorem B1796747 : Blo 1494067 1796747 := bstep (se 1 (by rfl) ⟨1347560, by rfl⟩ : syracuseStep 1796747 = 2695121) B2695121
theorem B26249879 : Blo 1494067 26249879 := bstep (se 1 (by rfl) ⟨19687409, by rfl⟩ : syracuseStep 26249879 = 39374819) B39374819
theorem B9218711 : Blo 1494067 9218711 := bstep (se 1 (by rfl) ⟨6914033, by rfl⟩ : syracuseStep 9218711 = 13828067) B13828067
theorem B2837207 : Blo 1494067 2837207 := bstep (se 1 (by rfl) ⟨2127905, by rfl⟩ : syracuseStep 2837207 = 4255811) B4255811
theorem B5049053 : Blo 1494067 5049053 := bstep (se 3 (by rfl) ⟨946697, by rfl⟩ : syracuseStep 5049053 = 1893395) B1893395
theorem B1682167 : Blo 1494067 1682167 := bstep (se 1 (by rfl) ⟨1261625, by rfl⟩ : syracuseStep 1682167 = 2523251) B2523251
theorem B12290881 : Blo 1494067 12290881 := bstep (se 2 (by rfl) ⟨4609080, by rfl⟩ : syracuseStep 12290881 = 9218161) B9218161
theorem B28732259 : Blo 1494067 28732259 := bstep (se 1 (by rfl) ⟨21549194, by rfl⟩ : syracuseStep 28732259 = 43098389) B43098389
theorem B5680003 : Blo 1494067 5680003 := bstep (se 1 (by rfl) ⟨4260002, by rfl⟩ : syracuseStep 5680003 = 8520005) B8520005
theorem B1682347 : Blo 1494067 1682347 := bstep (se 1 (by rfl) ⟨1261760, by rfl⟩ : syracuseStep 1682347 = 2523521) B2523521
theorem B3361715 : Blo 1494067 3361715 := bstep (se 1 (by rfl) ⟨2521286, by rfl⟩ : syracuseStep 3361715 = 5042573) B5042573
theorem B3361751 : Blo 1494067 3361751 := bstep (se 1 (by rfl) ⟨2521313, by rfl⟩ : syracuseStep 3361751 = 5042627) B5042627
theorem B3410903 : Blo 1494067 3410903 := bstep (se 1 (by rfl) ⟨2558177, by rfl⟩ : syracuseStep 3410903 = 5116355) B5116355
theorem B7482385 : Blo 1494067 7482385 := bstep (se 2 (by rfl) ⟨2805894, by rfl⟩ : syracuseStep 7482385 = 5611789) B5611789
theorem B1682455 : Blo 1494067 1682455 := bstep (se 1 (by rfl) ⟨1261841, by rfl⟩ : syracuseStep 1682455 = 2523683) B2523683
theorem B1494071 : Blo 1494067 1494071 := bstep (se 1 (by rfl) ⟨1120553, by rfl⟩ : syracuseStep 1494071 = 2241107) B2241107
theorem B1494091 : Blo 1494067 1494091 := bstep (se 1 (by rfl) ⟨1120568, by rfl⟩ : syracuseStep 1494091 = 2241137) B2241137
theorem B4787275 : Blo 1494067 4787275 := bstep (se 1 (by rfl) ⟨3590456, by rfl⟩ : syracuseStep 4787275 = 7180913) B7180913
theorem B10234955 : Blo 1494067 10234955 := bstep (se 1 (by rfl) ⟨7676216, by rfl⟩ : syracuseStep 10234955 = 15352433) B15352433
theorem B1494103 : Blo 1494067 1494103 := bstep (se 1 (by rfl) ⟨1120577, by rfl⟩ : syracuseStep 1494103 = 2241155) B2241155
theorem B1494123 : Blo 1494067 1494123 := bstep (se 1 (by rfl) ⟨1120592, by rfl⟩ : syracuseStep 1494123 = 2241185) B2241185
theorem B1494135 : Blo 1494067 1494135 := bstep (se 1 (by rfl) ⟨1120601, by rfl⟩ : syracuseStep 1494135 = 2241203) B2241203
theorem B1494155 : Blo 1494067 1494155 := bstep (se 1 (by rfl) ⟨1120616, by rfl⟩ : syracuseStep 1494155 = 2241233) B2241233
theorem B3361931 : Blo 1494067 3361931 := bstep (se 1 (by rfl) ⟨2521448, by rfl⟩ : syracuseStep 3361931 = 5042897) B5042897
theorem B1494167 : Blo 1494067 1494167 := bstep (se 1 (by rfl) ⟨1120625, by rfl⟩ : syracuseStep 1494167 = 2241251) B2241251
theorem B1494187 : Blo 1494067 1494187 := bstep (se 1 (by rfl) ⟨1120640, by rfl⟩ : syracuseStep 1494187 = 2241281) B2241281
theorem B5680307 : Blo 1494067 5680307 := bstep (se 1 (by rfl) ⟨4260230, by rfl⟩ : syracuseStep 5680307 = 8520461) B8520461
theorem B1494199 : Blo 1494067 1494199 := bstep (se 1 (by rfl) ⟨1120649, by rfl⟩ : syracuseStep 1494199 = 2241299) B2241299
theorem B3361985 : Blo 1494067 3361985 := bstep (se 2 (by rfl) ⟨1260744, by rfl⟩ : syracuseStep 3361985 = 2521489) B2521489
theorem B4254923 : Blo 1494067 4254923 := bstep (se 1 (by rfl) ⟨3191192, by rfl⟩ : syracuseStep 4254923 = 6382385) B6382385
theorem B1494219 : Blo 1494067 1494219 := bstep (se 1 (by rfl) ⟨1120664, by rfl⟩ : syracuseStep 1494219 = 2241329) B2241329
theorem B1682635 : Blo 1494067 1682635 := bstep (se 1 (by rfl) ⟨1261976, by rfl⟩ : syracuseStep 1682635 = 2523953) B2523953
theorem B1494231 : Blo 1494067 1494231 := bstep (se 1 (by rfl) ⟨1120673, by rfl⟩ : syracuseStep 1494231 = 2241347) B2241347
theorem B1494251 : Blo 1494067 1494251 := bstep (se 1 (by rfl) ⟨1120688, by rfl⟩ : syracuseStep 1494251 = 2241377) B2241377
theorem B2837747 : Blo 1494067 2837747 := bstep (se 1 (by rfl) ⟨2128310, by rfl⟩ : syracuseStep 2837747 = 4256621) B4256621
theorem B1494263 : Blo 1494067 1494263 := bstep (se 1 (by rfl) ⟨1120697, by rfl⟩ : syracuseStep 1494263 = 2241395) B2241395
theorem B1494283 : Blo 1494067 1494283 := bstep (se 1 (by rfl) ⟨1120712, by rfl⟩ : syracuseStep 1494283 = 2241425) B2241425
theorem B1494295 : Blo 1494067 1494295 := bstep (se 1 (by rfl) ⟨1120721, by rfl⟩ : syracuseStep 1494295 = 2241443) B2241443
theorem B1494315 : Blo 1494067 1494315 := bstep (se 1 (by rfl) ⟨1120736, by rfl⟩ : syracuseStep 1494315 = 2241473) B2241473
theorem B7564589 : Blo 1494067 7564589 := bstep (se 3 (by rfl) ⟨1418360, by rfl⟩ : syracuseStep 7564589 = 2836721) B2836721
theorem B1494327 : Blo 1494067 1494327 := bstep (se 1 (by rfl) ⟨1120745, by rfl⟩ : syracuseStep 1494327 = 2241491) B2241491
theorem B1682743 : Blo 1494067 1682743 := bstep (se 1 (by rfl) ⟨1262057, by rfl⟩ : syracuseStep 1682743 = 2524115) B2524115
theorem B8514881 : Blo 1494067 8514881 := bstep (se 2 (by rfl) ⟨3193080, by rfl⟩ : syracuseStep 8514881 = 6386161) B6386161
theorem B17272129 : Blo 1494067 17272129 := bstep (se 2 (by rfl) ⟨6477048, by rfl⟩ : syracuseStep 17272129 = 12954097) B12954097
theorem B1494347 : Blo 1494067 1494347 := bstep (se 1 (by rfl) ⟨1120760, by rfl⟩ : syracuseStep 1494347 = 2241521) B2241521
theorem B1494359 : Blo 1494067 1494359 := bstep (se 1 (by rfl) ⟨1120769, by rfl⟩ : syracuseStep 1494359 = 2241539) B2241539
theorem B1494379 : Blo 1494067 1494379 := bstep (se 1 (by rfl) ⟨1120784, by rfl⟩ : syracuseStep 1494379 = 2241569) B2241569
theorem B1494391 : Blo 1494067 1494391 := bstep (se 1 (by rfl) ⟨1120793, by rfl⟩ : syracuseStep 1494391 = 2241587) B2241587
theorem B1494411 : Blo 1494067 1494411 := bstep (se 1 (by rfl) ⟨1120808, by rfl⟩ : syracuseStep 1494411 = 2241617) B2241617
theorem B1494423 : Blo 1494067 1494423 := bstep (se 1 (by rfl) ⟨1120817, by rfl⟩ : syracuseStep 1494423 = 2241635) B2241635
theorem B3362201 : Blo 1494067 3362201 := bstep (se 2 (by rfl) ⟨1260825, by rfl⟩ : syracuseStep 3362201 = 2521651) B2521651
theorem B1494443 : Blo 1494067 1494443 := bstep (se 1 (by rfl) ⟨1120832, by rfl⟩ : syracuseStep 1494443 = 2241665) B2241665
theorem B1494455 : Blo 1494067 1494455 := bstep (se 1 (by rfl) ⟨1120841, by rfl⟩ : syracuseStep 1494455 = 2241683) B2241683
theorem B1494475 : Blo 1494067 1494475 := bstep (se 1 (by rfl) ⟨1120856, by rfl⟩ : syracuseStep 1494475 = 2241713) B2241713
theorem B1494487 : Blo 1494067 1494487 := bstep (se 1 (by rfl) ⟨1120865, by rfl⟩ : syracuseStep 1494487 = 2241731) B2241731
theorem B1494507 : Blo 1494067 1494507 := bstep (se 1 (by rfl) ⟨1120880, by rfl⟩ : syracuseStep 1494507 = 2241761) B2241761
theorem B1682923 : Blo 1494067 1682923 := bstep (se 1 (by rfl) ⟨1262192, by rfl⟩ : syracuseStep 1682923 = 2524385) B2524385
theorem B3362291 : Blo 1494067 3362291 := bstep (se 1 (by rfl) ⟨2521718, by rfl⟩ : syracuseStep 3362291 = 5043437) B5043437
theorem B1494519 : Blo 1494067 1494519 := bstep (se 1 (by rfl) ⟨1120889, by rfl⟩ : syracuseStep 1494519 = 2241779) B2241779
theorem B1494539 : Blo 1494067 1494539 := bstep (se 1 (by rfl) ⟨1120904, by rfl⟩ : syracuseStep 1494539 = 2241809) B2241809
theorem B3362327 : Blo 1494067 3362327 := bstep (se 1 (by rfl) ⟨2521745, by rfl⟩ : syracuseStep 3362327 = 5043491) B5043491
theorem B1494551 : Blo 1494067 1494551 := bstep (se 1 (by rfl) ⟨1120913, by rfl⟩ : syracuseStep 1494551 = 2241827) B2241827
theorem B1494571 : Blo 1494067 1494571 := bstep (se 1 (by rfl) ⟨1120928, by rfl⟩ : syracuseStep 1494571 = 2241857) B2241857
theorem B1494583 : Blo 1494067 1494583 := bstep (se 1 (by rfl) ⟨1120937, by rfl⟩ : syracuseStep 1494583 = 2241875) B2241875
theorem B1494603 : Blo 1494067 1494603 := bstep (se 1 (by rfl) ⟨1120952, by rfl⟩ : syracuseStep 1494603 = 2241905) B2241905
theorem B5115467 : Blo 1494067 5115467 := bstep (se 1 (by rfl) ⟨3836600, by rfl⟩ : syracuseStep 5115467 = 7673201) B7673201
theorem B1494615 : Blo 1494067 1494615 := bstep (se 1 (by rfl) ⟨1120961, by rfl⟩ : syracuseStep 1494615 = 2241923) B2241923
theorem B1683031 : Blo 1494067 1683031 := bstep (se 1 (by rfl) ⟨1262273, by rfl⟩ : syracuseStep 1683031 = 2524547) B2524547
theorem B1494635 : Blo 1494067 1494635 := bstep (se 1 (by rfl) ⟨1120976, by rfl⟩ : syracuseStep 1494635 = 2241953) B2241953
theorem B1494647 : Blo 1494067 1494647 := bstep (se 1 (by rfl) ⟨1120985, by rfl⟩ : syracuseStep 1494647 = 2241971) B2241971
theorem B55266947 : Blo 1494067 55266947 := bstep (se 1 (by rfl) ⟨41450210, by rfl⟩ : syracuseStep 55266947 = 82900421) B82900421
theorem B1494667 : Blo 1494067 1494667 := bstep (se 1 (by rfl) ⟨1121000, by rfl⟩ : syracuseStep 1494667 = 2242001) B2242001
theorem B4607639 : Blo 1494067 4607639 := bstep (se 1 (by rfl) ⟨3455729, by rfl⟩ : syracuseStep 4607639 = 6911459) B6911459
theorem B1494679 : Blo 1494067 1494679 := bstep (se 1 (by rfl) ⟨1121009, by rfl⟩ : syracuseStep 1494679 = 2242019) B2242019
theorem B1494699 : Blo 1494067 1494699 := bstep (se 1 (by rfl) ⟨1121024, by rfl⟩ : syracuseStep 1494699 = 2242049) B2242049
theorem B1494711 : Blo 1494067 1494711 := bstep (se 1 (by rfl) ⟨1121033, by rfl⟩ : syracuseStep 1494711 = 2242067) B2242067
theorem B3362507 : Blo 1494067 3362507 := bstep (se 1 (by rfl) ⟨2521880, by rfl⟩ : syracuseStep 3362507 = 5043761) B5043761
theorem B1494731 : Blo 1494067 1494731 := bstep (se 1 (by rfl) ⟨1121048, by rfl⟩ : syracuseStep 1494731 = 2242097) B2242097
theorem B1494743 : Blo 1494067 1494743 := bstep (se 1 (by rfl) ⟨1121057, by rfl⟩ : syracuseStep 1494743 = 2242115) B2242115
theorem B2838233 : Blo 1494067 2838233 := bstep (se 2 (by rfl) ⟨1064337, by rfl⟩ : syracuseStep 2838233 = 2128675) B2128675
theorem B1494763 : Blo 1494067 1494763 := bstep (se 1 (by rfl) ⟨1121072, by rfl⟩ : syracuseStep 1494763 = 2242145) B2242145
theorem B1494775 : Blo 1494067 1494775 := bstep (se 1 (by rfl) ⟨1121081, by rfl⟩ : syracuseStep 1494775 = 2242163) B2242163
theorem B3362561 : Blo 1494067 3362561 := bstep (se 2 (by rfl) ⟨1260960, by rfl⟩ : syracuseStep 3362561 = 2521921) B2521921
theorem B1494795 : Blo 1494067 1494795 := bstep (se 1 (by rfl) ⟨1121096, by rfl⟩ : syracuseStep 1494795 = 2242193) B2242193
theorem B1494807 : Blo 1494067 1494807 := bstep (se 1 (by rfl) ⟨1121105, by rfl⟩ : syracuseStep 1494807 = 2242211) B2242211
theorem B1494827 : Blo 1494067 1494827 := bstep (se 1 (by rfl) ⟨1121120, by rfl⟩ : syracuseStep 1494827 = 2242241) B2242241
theorem B1494839 : Blo 1494067 1494839 := bstep (se 1 (by rfl) ⟨1121129, by rfl⟩ : syracuseStep 1494839 = 2242259) B2242259
theorem B1494859 : Blo 1494067 1494859 := bstep (se 1 (by rfl) ⟨1121144, by rfl⟩ : syracuseStep 1494859 = 2242289) B2242289
theorem B1494871 : Blo 1494067 1494871 := bstep (se 1 (by rfl) ⟨1121153, by rfl⟩ : syracuseStep 1494871 = 2242307) B2242307
theorem B1494891 : Blo 1494067 1494891 := bstep (se 1 (by rfl) ⟨1121168, by rfl⟩ : syracuseStep 1494891 = 2242337) B2242337
theorem B1494903 : Blo 1494067 1494903 := bstep (se 1 (by rfl) ⟨1121177, by rfl⟩ : syracuseStep 1494903 = 2242355) B2242355
theorem B1494923 : Blo 1494067 1494923 := bstep (se 1 (by rfl) ⟨1121192, by rfl⟩ : syracuseStep 1494923 = 2242385) B2242385
theorem B1494935 : Blo 1494067 1494935 := bstep (se 1 (by rfl) ⟨1121201, by rfl⟩ : syracuseStep 1494935 = 2242403) B2242403
theorem B1494955 : Blo 1494067 1494955 := bstep (se 1 (by rfl) ⟨1121216, by rfl⟩ : syracuseStep 1494955 = 2242433) B2242433
theorem B1494967 : Blo 1494067 1494967 := bstep (se 1 (by rfl) ⟨1121225, by rfl⟩ : syracuseStep 1494967 = 2242451) B2242451
theorem B1494987 : Blo 1494067 1494987 := bstep (se 1 (by rfl) ⟨1121240, by rfl⟩ : syracuseStep 1494987 = 2242481) B2242481
theorem B1494999 : Blo 1494067 1494999 := bstep (se 1 (by rfl) ⟨1121249, by rfl⟩ : syracuseStep 1494999 = 2242499) B2242499
theorem B3362777 : Blo 1494067 3362777 := bstep (se 2 (by rfl) ⟨1261041, by rfl⟩ : syracuseStep 3362777 = 2522083) B2522083
theorem B1495019 : Blo 1494067 1495019 := bstep (se 1 (by rfl) ⟨1121264, by rfl⟩ : syracuseStep 1495019 = 2242529) B2242529
theorem B1495031 : Blo 1494067 1495031 := bstep (se 1 (by rfl) ⟨1121273, by rfl⟩ : syracuseStep 1495031 = 2242547) B2242547
theorem B1495051 : Blo 1494067 1495051 := bstep (se 1 (by rfl) ⟨1121288, by rfl⟩ : syracuseStep 1495051 = 2242577) B2242577
theorem B1495063 : Blo 1494067 1495063 := bstep (se 1 (by rfl) ⟨1121297, by rfl⟩ : syracuseStep 1495063 = 2242595) B2242595
theorem B1495083 : Blo 1494067 1495083 := bstep (se 1 (by rfl) ⟨1121312, by rfl⟩ : syracuseStep 1495083 = 2242625) B2242625
theorem B3362867 : Blo 1494067 3362867 := bstep (se 1 (by rfl) ⟨2522150, by rfl⟩ : syracuseStep 3362867 = 5044301) B5044301
theorem B1495095 : Blo 1494067 1495095 := bstep (se 1 (by rfl) ⟨1121321, by rfl⟩ : syracuseStep 1495095 = 2242643) B2242643
theorem B1495115 : Blo 1494067 1495115 := bstep (se 1 (by rfl) ⟨1121336, by rfl⟩ : syracuseStep 1495115 = 2242673) B2242673
theorem B3362903 : Blo 1494067 3362903 := bstep (se 1 (by rfl) ⟨2522177, by rfl⟩ : syracuseStep 3362903 = 5044355) B5044355
theorem B1495127 : Blo 1494067 1495127 := bstep (se 1 (by rfl) ⟨1121345, by rfl⟩ : syracuseStep 1495127 = 2242691) B2242691
theorem B1495147 : Blo 1494067 1495147 := bstep (se 1 (by rfl) ⟨1121360, by rfl⟩ : syracuseStep 1495147 = 2242721) B2242721
theorem B1495159 : Blo 1494067 1495159 := bstep (se 1 (by rfl) ⟨1121369, by rfl⟩ : syracuseStep 1495159 = 2242739) B2242739
theorem B1495179 : Blo 1494067 1495179 := bstep (se 1 (by rfl) ⟨1121384, by rfl⟩ : syracuseStep 1495179 = 2242769) B2242769
theorem B1495191 : Blo 1494067 1495191 := bstep (se 1 (by rfl) ⟨1121393, by rfl⟩ : syracuseStep 1495191 = 2242787) B2242787
theorem B1495211 : Blo 1494067 1495211 := bstep (se 1 (by rfl) ⟨1121408, by rfl⟩ : syracuseStep 1495211 = 2242817) B2242817
theorem B1495223 : Blo 1494067 1495223 := bstep (se 1 (by rfl) ⟨1121417, by rfl⟩ : syracuseStep 1495223 = 2242835) B2242835
theorem B1495243 : Blo 1494067 1495243 := bstep (se 1 (by rfl) ⟨1121432, by rfl⟩ : syracuseStep 1495243 = 2242865) B2242865
theorem B1495255 : Blo 1494067 1495255 := bstep (se 1 (by rfl) ⟨1121441, by rfl⟩ : syracuseStep 1495255 = 2242883) B2242883
theorem B1495275 : Blo 1494067 1495275 := bstep (se 1 (by rfl) ⟨1121456, by rfl⟩ : syracuseStep 1495275 = 2242913) B2242913
theorem B1495287 : Blo 1494067 1495287 := bstep (se 1 (by rfl) ⟨1121465, by rfl⟩ : syracuseStep 1495287 = 2242931) B2242931
theorem B3363083 : Blo 1494067 3363083 := bstep (se 1 (by rfl) ⟨2522312, by rfl⟩ : syracuseStep 3363083 = 5044625) B5044625
theorem B1495307 : Blo 1494067 1495307 := bstep (se 1 (by rfl) ⟨1121480, by rfl⟩ : syracuseStep 1495307 = 2242961) B2242961
theorem B1495319 : Blo 1494067 1495319 := bstep (se 1 (by rfl) ⟨1121489, by rfl⟩ : syracuseStep 1495319 = 2242979) B2242979
theorem B5755159 : Blo 1494067 5755159 := bstep (se 1 (by rfl) ⟨4316369, by rfl⟩ : syracuseStep 5755159 = 8632739) B8632739
theorem B1495339 : Blo 1494067 1495339 := bstep (se 1 (by rfl) ⟨1121504, by rfl⟩ : syracuseStep 1495339 = 2243009) B2243009
theorem B7180589 : Blo 1494067 7180589 := bstep (se 3 (by rfl) ⟨1346360, by rfl⟩ : syracuseStep 7180589 = 2692721) B2692721
theorem B1495351 : Blo 1494067 1495351 := bstep (se 1 (by rfl) ⟨1121513, by rfl⟩ : syracuseStep 1495351 = 2243027) B2243027
theorem B3363137 : Blo 1494067 3363137 := bstep (se 2 (by rfl) ⟨1261176, by rfl⟩ : syracuseStep 3363137 = 2522353) B2522353
theorem B1495371 : Blo 1494067 1495371 := bstep (se 1 (by rfl) ⟨1121528, by rfl⟩ : syracuseStep 1495371 = 2243057) B2243057
theorem B1495383 : Blo 1494067 1495383 := bstep (se 1 (by rfl) ⟨1121537, by rfl⟩ : syracuseStep 1495383 = 2243075) B2243075
theorem B1495403 : Blo 1494067 1495403 := bstep (se 1 (by rfl) ⟨1121552, by rfl⟩ : syracuseStep 1495403 = 2243105) B2243105
theorem B1495415 : Blo 1494067 1495415 := bstep (se 1 (by rfl) ⟨1121561, by rfl⟩ : syracuseStep 1495415 = 2243123) B2243123
theorem B1495435 : Blo 1494067 1495435 := bstep (se 1 (by rfl) ⟨1121576, by rfl⟩ : syracuseStep 1495435 = 2243153) B2243153
theorem B8081815 : Blo 1494067 8081815 := bstep (se 1 (by rfl) ⟨6061361, by rfl⟩ : syracuseStep 8081815 = 12122723) B12122723
theorem B1495447 : Blo 1494067 1495447 := bstep (se 1 (by rfl) ⟨1121585, by rfl⟩ : syracuseStep 1495447 = 2243171) B2243171
theorem B1495467 : Blo 1494067 1495467 := bstep (se 1 (by rfl) ⟨1121600, by rfl⟩ : syracuseStep 1495467 = 2243201) B2243201
theorem B4788659 : Blo 1494067 4788659 := bstep (se 1 (by rfl) ⟨3591494, by rfl⟩ : syracuseStep 4788659 = 7182989) B7182989
theorem B1495479 : Blo 1494067 1495479 := bstep (se 1 (by rfl) ⟨1121609, by rfl⟩ : syracuseStep 1495479 = 2243219) B2243219
theorem B3191243 : Blo 1494067 3191243 := bstep (se 1 (by rfl) ⟨2393432, by rfl⟩ : syracuseStep 3191243 = 4786865) B4786865
theorem B1495499 : Blo 1494067 1495499 := bstep (se 1 (by rfl) ⟨1121624, by rfl⟩ : syracuseStep 1495499 = 2243249) B2243249
theorem B1495511 : Blo 1494067 1495511 := bstep (se 1 (by rfl) ⟨1121633, by rfl⟩ : syracuseStep 1495511 = 2243267) B2243267
theorem B4256221 : Blo 1494067 4256221 := bstep (se 3 (by rfl) ⟨798041, by rfl⟩ : syracuseStep 4256221 = 1596083) B1596083
theorem B1495531 : Blo 1494067 1495531 := bstep (se 1 (by rfl) ⟨1121648, by rfl⟩ : syracuseStep 1495531 = 2243297) B2243297
theorem B1495543 : Blo 1494067 1495543 := bstep (se 1 (by rfl) ⟨1121657, by rfl⟩ : syracuseStep 1495543 = 2243315) B2243315
theorem B1495563 : Blo 1494067 1495563 := bstep (se 1 (by rfl) ⟨1121672, by rfl⟩ : syracuseStep 1495563 = 2243345) B2243345
theorem B1495575 : Blo 1494067 1495575 := bstep (se 1 (by rfl) ⟨1121681, by rfl⟩ : syracuseStep 1495575 = 2243363) B2243363
theorem B3363353 : Blo 1494067 3363353 := bstep (se 2 (by rfl) ⟨1261257, by rfl⟩ : syracuseStep 3363353 = 2522515) B2522515
theorem B1495595 : Blo 1494067 1495595 := bstep (se 1 (by rfl) ⟨1121696, by rfl⟩ : syracuseStep 1495595 = 2243393) B2243393
theorem B1495607 : Blo 1494067 1495607 := bstep (se 1 (by rfl) ⟨1121705, by rfl⟩ : syracuseStep 1495607 = 2243411) B2243411
theorem B6058571 : Blo 1494067 6058571 := bstep (se 1 (by rfl) ⟨4543928, by rfl⟩ : syracuseStep 6058571 = 9087857) B9087857
theorem B1495627 : Blo 1494067 1495627 := bstep (se 1 (by rfl) ⟨1121720, by rfl⟩ : syracuseStep 1495627 = 2243441) B2243441
theorem B1495639 : Blo 1494067 1495639 := bstep (se 1 (by rfl) ⟨1121729, by rfl⟩ : syracuseStep 1495639 = 2243459) B2243459
theorem B2241113 : Blo 1494067 2241113 := bstep (se 2 (by rfl) ⟨840417, by rfl⟩ : syracuseStep 2241113 = 1680835) B1680835
theorem B1495659 : Blo 1494067 1495659 := bstep (se 1 (by rfl) ⟨1121744, by rfl⟩ : syracuseStep 1495659 = 2243489) B2243489
theorem B3363443 : Blo 1494067 3363443 := bstep (se 1 (by rfl) ⟨2522582, by rfl⟩ : syracuseStep 3363443 = 5045165) B5045165
theorem B1495671 : Blo 1494067 1495671 := bstep (se 1 (by rfl) ⟨1121753, by rfl⟩ : syracuseStep 1495671 = 2243507) B2243507
theorem B1495691 : Blo 1494067 1495691 := bstep (se 1 (by rfl) ⟨1121768, by rfl⟩ : syracuseStep 1495691 = 2243537) B2243537
theorem B3363479 : Blo 1494067 3363479 := bstep (se 1 (by rfl) ⟨2522609, by rfl⟩ : syracuseStep 3363479 = 5045219) B5045219
theorem B1495703 : Blo 1494067 1495703 := bstep (se 1 (by rfl) ⟨1121777, by rfl⟩ : syracuseStep 1495703 = 2243555) B2243555
theorem B1495723 : Blo 1494067 1495723 := bstep (se 1 (by rfl) ⟨1121792, by rfl⟩ : syracuseStep 1495723 = 2243585) B2243585
theorem B1495735 : Blo 1494067 1495735 := bstep (se 1 (by rfl) ⟨1121801, by rfl⟩ : syracuseStep 1495735 = 2243603) B2243603
theorem B2241227 : Blo 1494067 2241227 := bstep (se 1 (by rfl) ⟨1680920, by rfl⟩ : syracuseStep 2241227 = 3361841) B3361841
theorem B1495755 : Blo 1494067 1495755 := bstep (se 1 (by rfl) ⟨1121816, by rfl⟩ : syracuseStep 1495755 = 2243633) B2243633
theorem B2241239 : Blo 1494067 2241239 := bstep (se 1 (by rfl) ⟨1680929, by rfl⟩ : syracuseStep 2241239 = 3361859) B3361859
theorem B1495767 : Blo 1494067 1495767 := bstep (se 1 (by rfl) ⟨1121825, by rfl⟩ : syracuseStep 1495767 = 2243651) B2243651
theorem B1495787 : Blo 1494067 1495787 := bstep (se 1 (by rfl) ⟨1121840, by rfl⟩ : syracuseStep 1495787 = 2243681) B2243681
theorem B1495799 : Blo 1494067 1495799 := bstep (se 1 (by rfl) ⟨1121849, by rfl⟩ : syracuseStep 1495799 = 2243699) B2243699
theorem B6386435 : Blo 1494067 6386435 := bstep (se 1 (by rfl) ⟨4789826, by rfl⟩ : syracuseStep 6386435 = 9579653) B9579653
theorem B1495819 : Blo 1494067 1495819 := bstep (se 1 (by rfl) ⟨1121864, by rfl⟩ : syracuseStep 1495819 = 2243729) B2243729
theorem B1495831 : Blo 1494067 1495831 := bstep (se 1 (by rfl) ⟨1121873, by rfl⟩ : syracuseStep 1495831 = 2243747) B2243747
theorem B2241305 : Blo 1494067 2241305 := bstep (se 2 (by rfl) ⟨840489, by rfl⟩ : syracuseStep 2241305 = 1680979) B1680979
theorem B1495851 : Blo 1494067 1495851 := bstep (se 1 (by rfl) ⟨1121888, by rfl⟩ : syracuseStep 1495851 = 2243777) B2243777
theorem B4256563 : Blo 1494067 4256563 := bstep (se 1 (by rfl) ⟨3192422, by rfl⟩ : syracuseStep 4256563 = 6384845) B6384845
theorem B1495863 : Blo 1494067 1495863 := bstep (se 1 (by rfl) ⟨1121897, by rfl⟩ : syracuseStep 1495863 = 2243795) B2243795
theorem B3363659 : Blo 1494067 3363659 := bstep (se 1 (by rfl) ⟨2522744, by rfl⟩ : syracuseStep 3363659 = 5045489) B5045489
theorem B1495883 : Blo 1494067 1495883 := bstep (se 1 (by rfl) ⟨1121912, by rfl⟩ : syracuseStep 1495883 = 2243825) B2243825
theorem B1495895 : Blo 1494067 1495895 := bstep (se 1 (by rfl) ⟨1121921, by rfl⟩ : syracuseStep 1495895 = 2243843) B2243843
theorem B1495915 : Blo 1494067 1495915 := bstep (se 1 (by rfl) ⟨1121936, by rfl⟩ : syracuseStep 1495915 = 2243873) B2243873
theorem B1495927 : Blo 1494067 1495927 := bstep (se 1 (by rfl) ⟨1121945, by rfl⟩ : syracuseStep 1495927 = 2243891) B2243891
theorem B3363713 : Blo 1494067 3363713 := bstep (se 2 (by rfl) ⟨1261392, by rfl⟩ : syracuseStep 3363713 = 2522785) B2522785
theorem B2241419 : Blo 1494067 2241419 := bstep (se 1 (by rfl) ⟨1681064, by rfl⟩ : syracuseStep 2241419 = 3362129) B3362129
theorem B1495947 : Blo 1494067 1495947 := bstep (se 1 (by rfl) ⟨1121960, by rfl⟩ : syracuseStep 1495947 = 2243921) B2243921
theorem B2241431 : Blo 1494067 2241431 := bstep (se 1 (by rfl) ⟨1681073, by rfl⟩ : syracuseStep 2241431 = 3362147) B3362147
theorem B1495959 : Blo 1494067 1495959 := bstep (se 1 (by rfl) ⟨1121969, by rfl⟩ : syracuseStep 1495959 = 2243939) B2243939
theorem B1495979 : Blo 1494067 1495979 := bstep (se 1 (by rfl) ⟨1121984, by rfl⟩ : syracuseStep 1495979 = 2243969) B2243969
theorem B1495991 : Blo 1494067 1495991 := bstep (se 1 (by rfl) ⟨1121993, by rfl⟩ : syracuseStep 1495991 = 2243987) B2243987
theorem B1496011 : Blo 1494067 1496011 := bstep (se 1 (by rfl) ⟨1122008, by rfl⟩ : syracuseStep 1496011 = 2244017) B2244017
theorem B1496023 : Blo 1494067 1496023 := bstep (se 1 (by rfl) ⟨1122017, by rfl⟩ : syracuseStep 1496023 = 2244035) B2244035
theorem B2241497 : Blo 1494067 2241497 := bstep (se 2 (by rfl) ⟨840561, by rfl⟩ : syracuseStep 2241497 = 1681123) B1681123
theorem B1496043 : Blo 1494067 1496043 := bstep (se 1 (by rfl) ⟨1122032, by rfl⟩ : syracuseStep 1496043 = 2244065) B2244065
theorem B1496055 : Blo 1494067 1496055 := bstep (se 1 (by rfl) ⟨1122041, by rfl⟩ : syracuseStep 1496055 = 2244083) B2244083
theorem B11359277 : Blo 1494067 11359277 := bstep (se 3 (by rfl) ⟨2129864, by rfl⟩ : syracuseStep 11359277 = 4259729) B4259729
theorem B51811397 : Blo 1494067 51811397 := bstep (se 4 (by rfl) ⟨4857318, by rfl⟩ : syracuseStep 51811397 = 9714637) B9714637
theorem B5043275 : Blo 1494067 5043275 := bstep (se 1 (by rfl) ⟨3782456, by rfl⟩ : syracuseStep 5043275 = 7564913) B7564913
theorem B2241611 : Blo 1494067 2241611 := bstep (se 1 (by rfl) ⟨1681208, by rfl⟩ : syracuseStep 2241611 = 3362417) B3362417
theorem B2241623 : Blo 1494067 2241623 := bstep (se 1 (by rfl) ⟨1681217, by rfl⟩ : syracuseStep 2241623 = 3362435) B3362435
theorem B3363929 : Blo 1494067 3363929 := bstep (se 2 (by rfl) ⟨1261473, by rfl⟩ : syracuseStep 3363929 = 2522947) B2522947
theorem B2839691 : Blo 1494067 2839691 := bstep (se 1 (by rfl) ⟨2129768, by rfl⟩ : syracuseStep 2839691 = 4259537) B4259537
theorem B2241689 : Blo 1494067 2241689 := bstep (se 2 (by rfl) ⟨840633, by rfl⟩ : syracuseStep 2241689 = 1681267) B1681267
theorem B5674157 : Blo 1494067 5674157 := bstep (se 3 (by rfl) ⟨1063904, by rfl⟩ : syracuseStep 5674157 = 2127809) B2127809
theorem B3191987 : Blo 1494067 3191987 := bstep (se 1 (by rfl) ⟨2393990, by rfl⟩ : syracuseStep 3191987 = 4787981) B4787981
theorem B3364019 : Blo 1494067 3364019 := bstep (se 1 (by rfl) ⟨2523014, by rfl⟩ : syracuseStep 3364019 = 5046029) B5046029
theorem B3364055 : Blo 1494067 3364055 := bstep (se 1 (by rfl) ⟨2523041, by rfl⟩ : syracuseStep 3364055 = 5046083) B5046083
theorem B2241803 : Blo 1494067 2241803 := bstep (se 1 (by rfl) ⟨1681352, by rfl⟩ : syracuseStep 2241803 = 3362705) B3362705
theorem B2241815 : Blo 1494067 2241815 := bstep (se 1 (by rfl) ⟨1681361, by rfl⟩ : syracuseStep 2241815 = 3362723) B3362723
theorem B2839873 : Blo 1494067 2839873 := bstep (se 2 (by rfl) ⟨1064952, by rfl⟩ : syracuseStep 2839873 = 2129905) B2129905
theorem B5043545 : Blo 1494067 5043545 := bstep (se 2 (by rfl) ⟨1891329, by rfl⟩ : syracuseStep 5043545 = 3782659) B3782659
theorem B2241881 : Blo 1494067 2241881 := bstep (se 2 (by rfl) ⟨840705, by rfl⟩ : syracuseStep 2241881 = 1681411) B1681411
theorem B3364235 : Blo 1494067 3364235 := bstep (se 1 (by rfl) ⟨2523176, by rfl⟩ : syracuseStep 3364235 = 5046353) B5046353
theorem B3364289 : Blo 1494067 3364289 := bstep (se 2 (by rfl) ⟨1261608, by rfl⟩ : syracuseStep 3364289 = 2523217) B2523217
theorem B2241995 : Blo 1494067 2241995 := bstep (se 1 (by rfl) ⟨1681496, by rfl⟩ : syracuseStep 2241995 = 3362993) B3362993
theorem B4855243 : Blo 1494067 4855243 := bstep (se 1 (by rfl) ⟨3641432, by rfl⟩ : syracuseStep 4855243 = 7282865) B7282865
theorem B11351501 : Blo 1494067 11351501 := bstep (se 3 (by rfl) ⟨2128406, by rfl⟩ : syracuseStep 11351501 = 4256813) B4256813
theorem B2242007 : Blo 1494067 2242007 := bstep (se 1 (by rfl) ⟨1681505, by rfl⟩ : syracuseStep 2242007 = 3363011) B3363011
theorem B2242073 : Blo 1494067 2242073 := bstep (se 2 (by rfl) ⟨840777, by rfl⟩ : syracuseStep 2242073 = 1681555) B1681555
theorem B14571139 : Blo 1494067 14571139 := bstep (se 1 (by rfl) ⟨10928354, by rfl⟩ : syracuseStep 14571139 = 21856709) B21856709
theorem B2242187 : Blo 1494067 2242187 := bstep (se 1 (by rfl) ⟨1681640, by rfl⟩ : syracuseStep 2242187 = 3363281) B3363281
theorem B2242199 : Blo 1494067 2242199 := bstep (se 1 (by rfl) ⟨1681649, by rfl⟩ : syracuseStep 2242199 = 3363299) B3363299
theorem B8517271 : Blo 1494067 8517271 := bstep (se 1 (by rfl) ⟨6387953, by rfl⟩ : syracuseStep 8517271 = 12775907) B12775907
theorem B3364505 : Blo 1494067 3364505 := bstep (se 2 (by rfl) ⟨1261689, by rfl⟩ : syracuseStep 3364505 = 2523379) B2523379
theorem B3593879 : Blo 1494067 3593879 := bstep (se 1 (by rfl) ⟨2695409, by rfl⟩ : syracuseStep 3593879 = 5390819) B5390819
theorem B2242265 : Blo 1494067 2242265 := bstep (se 2 (by rfl) ⟨840849, by rfl⟩ : syracuseStep 2242265 = 1681699) B1681699
theorem B4257497 : Blo 1494067 4257497 := bstep (se 2 (by rfl) ⟨1596561, by rfl⟩ : syracuseStep 4257497 = 3193123) B3193123
theorem B3364595 : Blo 1494067 3364595 := bstep (se 1 (by rfl) ⟨2523446, by rfl⟩ : syracuseStep 3364595 = 5046893) B5046893
theorem B3364631 : Blo 1494067 3364631 := bstep (se 1 (by rfl) ⟨2523473, by rfl⟩ : syracuseStep 3364631 = 5046947) B5046947
theorem B6469427 : Blo 1494067 6469427 := bstep (se 1 (by rfl) ⟨4852070, by rfl⟩ : syracuseStep 6469427 = 9704141) B9704141
theorem B2242379 : Blo 1494067 2242379 := bstep (se 1 (by rfl) ⟨1681784, by rfl⟩ : syracuseStep 2242379 = 3363569) B3363569
theorem B2242391 : Blo 1494067 2242391 := bstep (se 1 (by rfl) ⟨1681793, by rfl⟩ : syracuseStep 2242391 = 3363587) B3363587
theorem B1578839 : Blo 1494067 1578839 := bstep (se 1 (by rfl) ⟨1184129, by rfl⟩ : syracuseStep 1578839 = 2368259) B2368259
theorem B2242457 : Blo 1494067 2242457 := bstep (se 2 (by rfl) ⟨840921, by rfl⟩ : syracuseStep 2242457 = 1681843) B1681843
theorem B5674931 : Blo 1494067 5674931 := bstep (se 1 (by rfl) ⟨4256198, by rfl⟩ : syracuseStep 5674931 = 8512397) B8512397
theorem B11351987 : Blo 1494067 11351987 := bstep (se 1 (by rfl) ⟨8513990, by rfl⟩ : syracuseStep 11351987 = 17027981) B17027981
theorem B3364811 : Blo 1494067 3364811 := bstep (se 1 (by rfl) ⟨2523608, by rfl⟩ : syracuseStep 3364811 = 5047217) B5047217
theorem B4610009 : Blo 1494067 4610009 := bstep (se 2 (by rfl) ⟨1728753, by rfl⟩ : syracuseStep 4610009 = 3457507) B3457507
theorem B3192833 : Blo 1494067 3192833 := bstep (se 2 (by rfl) ⟨1197312, by rfl⟩ : syracuseStep 3192833 = 2394625) B2394625
theorem B3364865 : Blo 1494067 3364865 := bstep (se 2 (by rfl) ⟨1261824, by rfl⟩ : syracuseStep 3364865 = 2523649) B2523649
theorem B2127883 : Blo 1494067 2127883 := bstep (se 1 (by rfl) ⟨1595912, by rfl⟩ : syracuseStep 2127883 = 3191825) B3191825
theorem B2242571 : Blo 1494067 2242571 := bstep (se 1 (by rfl) ⟨1681928, by rfl⟩ : syracuseStep 2242571 = 3363857) B3363857
theorem B5044247 : Blo 1494067 5044247 := bstep (se 1 (by rfl) ⟨3783185, by rfl⟩ : syracuseStep 5044247 = 7566371) B7566371
theorem B2242583 : Blo 1494067 2242583 := bstep (se 1 (by rfl) ⟨1681937, by rfl⟩ : syracuseStep 2242583 = 3363875) B3363875
theorem B87447605 : Blo 1494067 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B30693451 : Blo 1494067 30693451 := bstep (se 1 (by rfl) ⟨23020088, by rfl⟩ : syracuseStep 30693451 = 46040177) B46040177
theorem B12777547 : Blo 1494067 12777547 := bstep (se 1 (by rfl) ⟨9583160, by rfl⟩ : syracuseStep 12777547 = 19166321) B19166321
theorem B2242649 : Blo 1494067 2242649 := bstep (se 2 (by rfl) ⟨840993, by rfl⟩ : syracuseStep 2242649 = 1681987) B1681987
theorem B6740147 : Blo 1494067 6740147 := bstep (se 1 (by rfl) ⟨5055110, by rfl⟩ : syracuseStep 6740147 = 10110221) B10110221
theorem B2242763 : Blo 1494067 2242763 := bstep (se 1 (by rfl) ⟨1682072, by rfl⟩ : syracuseStep 2242763 = 3364145) B3364145
theorem B16169165 : Blo 1494067 16169165 := bstep (se 3 (by rfl) ⟨3031718, by rfl⟩ : syracuseStep 16169165 = 6063437) B6063437
theorem B2242775 : Blo 1494067 2242775 := bstep (se 1 (by rfl) ⟨1682081, by rfl⟩ : syracuseStep 2242775 = 3364163) B3364163
theorem B3365081 : Blo 1494067 3365081 := bstep (se 2 (by rfl) ⟨1261905, by rfl⟩ : syracuseStep 3365081 = 2523811) B2523811
theorem B1595639 : Blo 1494067 1595639 := bstep (se 1 (by rfl) ⟨1196729, by rfl⟩ : syracuseStep 1595639 = 2393459) B2393459
theorem B2242841 : Blo 1494067 2242841 := bstep (se 2 (by rfl) ⟨841065, by rfl⟩ : syracuseStep 2242841 = 1682131) B1682131
theorem B3782963 : Blo 1494067 3782963 := bstep (se 1 (by rfl) ⟨2837222, by rfl⟩ : syracuseStep 3782963 = 5674445) B5674445
theorem B3365171 : Blo 1494067 3365171 := bstep (se 1 (by rfl) ⟨2523878, by rfl⟩ : syracuseStep 3365171 = 5047757) B5047757
theorem B3193175 : Blo 1494067 3193175 := bstep (se 1 (by rfl) ⟨2394881, by rfl⟩ : syracuseStep 3193175 = 4789763) B4789763
theorem B3365207 : Blo 1494067 3365207 := bstep (se 1 (by rfl) ⟨2523905, by rfl⟩ : syracuseStep 3365207 = 5047811) B5047811
theorem B12777821 : Blo 1494067 12777821 := bstep (se 3 (by rfl) ⟨2395841, by rfl⟩ : syracuseStep 12777821 = 4791683) B4791683
theorem B2242955 : Blo 1494067 2242955 := bstep (se 1 (by rfl) ⟨1682216, by rfl⟩ : syracuseStep 2242955 = 3364433) B3364433
theorem B9574807 : Blo 1494067 9574807 := bstep (se 1 (by rfl) ⟨7181105, by rfl⟩ : syracuseStep 9574807 = 14362211) B14362211
theorem B2242967 : Blo 1494067 2242967 := bstep (se 1 (by rfl) ⟨1682225, by rfl⟩ : syracuseStep 2242967 = 3364451) B3364451
theorem B2243033 : Blo 1494067 2243033 := bstep (se 2 (by rfl) ⟨841137, by rfl⟩ : syracuseStep 2243033 = 1682275) B1682275
theorem B6650333 : Blo 1494067 6650333 := bstep (se 3 (by rfl) ⟨1246937, by rfl⟩ : syracuseStep 6650333 = 2493875) B2493875
theorem B3365387 : Blo 1494067 3365387 := bstep (se 1 (by rfl) ⟨2524040, by rfl⟩ : syracuseStep 3365387 = 5048081) B5048081
theorem B23026193 : Blo 1494067 23026193 := bstep (se 2 (by rfl) ⟨8634822, by rfl⟩ : syracuseStep 23026193 = 17269645) B17269645
theorem B5044787 : Blo 1494067 5044787 := bstep (se 1 (by rfl) ⟨3783590, by rfl⟩ : syracuseStep 5044787 = 7567181) B7567181
theorem B3365441 : Blo 1494067 3365441 := bstep (se 2 (by rfl) ⟨1262040, by rfl⟩ : syracuseStep 3365441 = 2524081) B2524081
theorem B2243147 : Blo 1494067 2243147 := bstep (se 1 (by rfl) ⟨1682360, by rfl⟩ : syracuseStep 2243147 = 3364721) B3364721
theorem B2243159 : Blo 1494067 2243159 := bstep (se 1 (by rfl) ⟨1682369, by rfl⟩ : syracuseStep 2243159 = 3364739) B3364739
theorem B3783257 : Blo 1494067 3783257 := bstep (se 2 (by rfl) ⟨1418721, by rfl⟩ : syracuseStep 3783257 = 2837443) B2837443
theorem B14006915 : Blo 1494067 14006915 := bstep (se 1 (by rfl) ⟨10505186, by rfl⟩ : syracuseStep 14006915 = 21010373) B21010373
theorem B1890955 : Blo 1494067 1890955 := bstep (se 1 (by rfl) ⟨1418216, by rfl⟩ : syracuseStep 1890955 = 2836433) B2836433
theorem B2521739 : Blo 1494067 2521739 := bstep (se 1 (by rfl) ⟨1891304, by rfl⟩ : syracuseStep 2521739 = 3782609) B3782609
theorem B2243225 : Blo 1494067 2243225 := bstep (se 2 (by rfl) ⟨841209, by rfl⟩ : syracuseStep 2243225 = 1682419) B1682419
theorem B3029707 : Blo 1494067 3029707 := bstep (se 1 (by rfl) ⟨2272280, by rfl⟩ : syracuseStep 3029707 = 4544561) B4544561
theorem B2521867 : Blo 1494067 2521867 := bstep (se 1 (by rfl) ⟨1891400, by rfl⟩ : syracuseStep 2521867 = 3782801) B3782801
theorem B2243339 : Blo 1494067 2243339 := bstep (se 1 (by rfl) ⟨1682504, by rfl⟩ : syracuseStep 2243339 = 3365009) B3365009
theorem B2243351 : Blo 1494067 2243351 := bstep (se 1 (by rfl) ⟨1682513, by rfl⟩ : syracuseStep 2243351 = 3365027) B3365027
theorem B3365657 : Blo 1494067 3365657 := bstep (se 2 (by rfl) ⟨1262121, by rfl⟩ : syracuseStep 3365657 = 2524243) B2524243
theorem B6060845 : Blo 1494067 6060845 := bstep (se 3 (by rfl) ⟨1136408, by rfl⟩ : syracuseStep 6060845 = 2272817) B2272817
theorem B5045057 : Blo 1494067 5045057 := bstep (se 2 (by rfl) ⟨1891896, by rfl⟩ : syracuseStep 5045057 = 3783793) B3783793
theorem B5389145 : Blo 1494067 5389145 := bstep (se 2 (by rfl) ⟨2020929, by rfl⟩ : syracuseStep 5389145 = 4041859) B4041859
theorem B2243417 : Blo 1494067 2243417 := bstep (se 2 (by rfl) ⟨841281, by rfl⟩ : syracuseStep 2243417 = 1682563) B1682563
theorem B3365747 : Blo 1494067 3365747 := bstep (se 1 (by rfl) ⟨2524310, by rfl⟩ : syracuseStep 3365747 = 5048621) B5048621
theorem B3365783 : Blo 1494067 3365783 := bstep (se 1 (by rfl) ⟨2524337, by rfl⟩ : syracuseStep 3365783 = 5048675) B5048675
theorem B2522009 : Blo 1494067 2522009 := bstep (se 2 (by rfl) ⟨945753, by rfl⟩ : syracuseStep 2522009 = 1891507) B1891507
theorem B2243531 : Blo 1494067 2243531 := bstep (se 1 (by rfl) ⟨1682648, by rfl⟩ : syracuseStep 2243531 = 3365297) B3365297
theorem B2243543 : Blo 1494067 2243543 := bstep (se 1 (by rfl) ⟨1682657, by rfl⟩ : syracuseStep 2243543 = 3365315) B3365315
theorem B2522137 : Blo 1494067 2522137 := bstep (se 2 (by rfl) ⟨945801, by rfl⟩ : syracuseStep 2522137 = 1891603) B1891603
theorem B2694169 : Blo 1494067 2694169 := bstep (se 2 (by rfl) ⟨1010313, by rfl⟩ : syracuseStep 2694169 = 2020627) B2020627
theorem B2243609 : Blo 1494067 2243609 := bstep (se 2 (by rfl) ⟨841353, by rfl⟩ : syracuseStep 2243609 = 1682707) B1682707
theorem B14375971 : Blo 1494067 14375971 := bstep (se 1 (by rfl) ⟨10781978, by rfl⟩ : syracuseStep 14375971 = 21563957) B21563957
theorem B3365963 : Blo 1494067 3365963 := bstep (se 1 (by rfl) ⟨2524472, by rfl⟩ : syracuseStep 3365963 = 5048945) B5048945
theorem B7568477 : Blo 1494067 7568477 := bstep (se 3 (by rfl) ⟨1419089, by rfl⟩ : syracuseStep 7568477 = 2838179) B2838179
theorem B4258909 : Blo 1494067 4258909 := bstep (se 3 (by rfl) ⟨798545, by rfl⟩ : syracuseStep 4258909 = 1597091) B1597091
theorem B3366017 : Blo 1494067 3366017 := bstep (se 2 (by rfl) ⟨1262256, by rfl⟩ : syracuseStep 3366017 = 2524513) B2524513
theorem B2243723 : Blo 1494067 2243723 := bstep (se 1 (by rfl) ⟨1682792, by rfl⟩ : syracuseStep 2243723 = 3365585) B3365585
theorem B7183511 : Blo 1494067 7183511 := bstep (se 1 (by rfl) ⟨5387633, by rfl⟩ : syracuseStep 7183511 = 10775267) B10775267
theorem B2243735 : Blo 1494067 2243735 := bstep (se 1 (by rfl) ⟨1682801, by rfl⟩ : syracuseStep 2243735 = 3365603) B3365603
theorem B2129113 : Blo 1494067 2129113 := bstep (se 2 (by rfl) ⟨798417, by rfl⟩ : syracuseStep 2129113 = 1596835) B1596835
theorem B2243801 : Blo 1494067 2243801 := bstep (se 2 (by rfl) ⟨841425, by rfl⟩ : syracuseStep 2243801 = 1682851) B1682851
theorem B1596715 : Blo 1494067 1596715 := bstep (se 1 (by rfl) ⟨1197536, by rfl⟩ : syracuseStep 1596715 = 2395073) B2395073
theorem B4259137 : Blo 1494067 4259137 := bstep (se 2 (by rfl) ⟨1597176, by rfl⟩ : syracuseStep 4259137 = 3194353) B3194353
theorem B2243915 : Blo 1494067 2243915 := bstep (se 1 (by rfl) ⟨1682936, by rfl⟩ : syracuseStep 2243915 = 3365873) B3365873
theorem B2694487 : Blo 1494067 2694487 := bstep (se 1 (by rfl) ⟨2020865, by rfl⟩ : syracuseStep 2694487 = 4041731) B4041731
theorem B2243927 : Blo 1494067 2243927 := bstep (se 1 (by rfl) ⟨1682945, by rfl⟩ : syracuseStep 2243927 = 3365891) B3365891
theorem B5045597 : Blo 1494067 5045597 := bstep (se 3 (by rfl) ⟨946049, by rfl⟩ : syracuseStep 5045597 = 1892099) B1892099
theorem B11509085 : Blo 1494067 11509085 := bstep (se 3 (by rfl) ⟨2157953, by rfl⟩ : syracuseStep 11509085 = 4315907) B4315907
theorem B11353445 : Blo 1494067 11353445 := bstep (se 4 (by rfl) ⟨1064385, by rfl⟩ : syracuseStep 11353445 = 2128771) B2128771
theorem B5676419 : Blo 1494067 5676419 := bstep (se 1 (by rfl) ⟨4257314, by rfl⟩ : syracuseStep 5676419 = 8514629) B8514629
theorem B12778883 : Blo 1494067 12778883 := bstep (se 1 (by rfl) ⟨9584162, by rfl⟩ : syracuseStep 12778883 = 19168325) B19168325
theorem B2243993 : Blo 1494067 2243993 := bstep (se 2 (by rfl) ⟨841497, by rfl⟩ : syracuseStep 2243993 = 1682995) B1682995
theorem B1891927 : Blo 1494067 1891927 := bstep (se 1 (by rfl) ⟨1418945, by rfl⟩ : syracuseStep 1891927 = 2837891) B2837891
theorem B2522711 : Blo 1494067 2522711 := bstep (se 1 (by rfl) ⟨1892033, by rfl⟩ : syracuseStep 2522711 = 3784067) B3784067
theorem B4259479 : Blo 1494067 4259479 := bstep (se 1 (by rfl) ⟨3194609, by rfl⟩ : syracuseStep 4259479 = 6389219) B6389219
theorem B2522839 : Blo 1494067 2522839 := bstep (se 1 (by rfl) ⟨1892129, by rfl⟩ : syracuseStep 2522839 = 3784259) B3784259
theorem B11345669 : Blo 1494067 11345669 := bstep (se 4 (by rfl) ⟨1063656, by rfl⟩ : syracuseStep 11345669 = 2127313) B2127313
theorem B18177857 : Blo 1494067 18177857 := bstep (se 2 (by rfl) ⟨6816696, by rfl⟩ : syracuseStep 18177857 = 13633393) B13633393
theorem B5676875 : Blo 1494067 5676875 := bstep (se 1 (by rfl) ⟨4257656, by rfl⟩ : syracuseStep 5676875 = 8515313) B8515313
theorem B11353931 : Blo 1494067 11353931 := bstep (se 1 (by rfl) ⟨8515448, by rfl⟩ : syracuseStep 11353931 = 17030897) B17030897
theorem B3784715 : Blo 1494067 3784715 := bstep (se 1 (by rfl) ⟨2838536, by rfl⟩ : syracuseStep 3784715 = 5677073) B5677073
theorem B12779531 : Blo 1494067 12779531 := bstep (se 1 (by rfl) ⟨9584648, by rfl⟩ : syracuseStep 12779531 = 19169297) B19169297
theorem B58245155 : Blo 1494067 58245155 := bstep (se 1 (by rfl) ⟨43683866, by rfl⟩ : syracuseStep 58245155 = 87367733) B87367733
theorem B113598533 : Blo 1494067 113598533 := bstep (se 4 (by rfl) ⟨10649862, by rfl⟩ : syracuseStep 113598533 = 21299725) B21299725
theorem B2523271 : Blo 1494067 2523271 := bstep (se 1 (by rfl) ⟨1892453, by rfl⟩ : syracuseStep 2523271 = 3784907) B3784907
theorem B8511965 : Blo 1494067 8511965 := bstep (se 3 (by rfl) ⟨1595993, by rfl⟩ : syracuseStep 8511965 = 3191987) B3191987
theorem B3785231 : Blo 1494067 3785231 := bstep (se 1 (by rfl) ⟨2838923, by rfl⟩ : syracuseStep 3785231 = 5677847) B5677847
theorem B932774453 : Blo 1494067 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B17023607 : Blo 1494067 17023607 := bstep (se 1 (by rfl) ⟨12767705, by rfl⟩ : syracuseStep 17023607 = 25535411) B25535411
theorem B3785363 : Blo 1494067 3785363 := bstep (se 1 (by rfl) ⟨2839022, by rfl⟩ : syracuseStep 3785363 = 5678045) B5678045
theorem B12124865 : Blo 1494067 12124865 := bstep (se 2 (by rfl) ⟨4546824, by rfl⟩ : syracuseStep 12124865 = 9093649) B9093649
theorem B1893127 : Blo 1494067 1893127 := bstep (se 1 (by rfl) ⟨1419845, by rfl⟩ : syracuseStep 1893127 = 2839691) B2839691
theorem B5047055 : Blo 1494067 5047055 := bstep (se 1 (by rfl) ⟨3785291, by rfl⟩ : syracuseStep 5047055 = 7570583) B7570583
theorem B2523919 : Blo 1494067 2523919 := bstep (se 1 (by rfl) ⟨1892939, by rfl⟩ : syracuseStep 2523919 = 3785879) B3785879
theorem B14377817 : Blo 1494067 14377817 := bstep (se 2 (by rfl) ⟨5391681, by rfl⟩ : syracuseStep 14377817 = 10783363) B10783363
theorem B5047325 : Blo 1494067 5047325 := bstep (se 3 (by rfl) ⟨946373, by rfl⟩ : syracuseStep 5047325 = 1892747) B1892747
theorem B2393273 : Blo 1494067 2393273 := bstep (se 2 (by rfl) ⟨897477, by rfl⟩ : syracuseStep 2393273 = 1794955) B1794955
theorem B2524459 : Blo 1494067 2524459 := bstep (se 1 (by rfl) ⟨1893344, by rfl⟩ : syracuseStep 2524459 = 3786689) B3786689
theorem B3073339 : Blo 1494067 3073339 := bstep (se 1 (by rfl) ⟨2305004, by rfl⟩ : syracuseStep 3073339 = 4610009) B4610009
theorem B6383033 : Blo 1494067 6383033 := bstep (se 2 (by rfl) ⟨2393637, by rfl⟩ : syracuseStep 6383033 = 4787275) B4787275
theorem B2524601 : Blo 1494067 2524601 := bstep (se 2 (by rfl) ⟨946725, by rfl⟩ : syracuseStep 2524601 = 1893451) B1893451
theorem B5678545 : Blo 1494067 5678545 := bstep (se 2 (by rfl) ⟨2129454, by rfl⟩ : syracuseStep 5678545 = 4258909) B4258909
theorem B16156189 : Blo 1494067 16156189 := bstep (se 3 (by rfl) ⟨3029285, by rfl⟩ : syracuseStep 16156189 = 6058571) B6058571
theorem B4433555 : Blo 1494067 4433555 := bstep (se 1 (by rfl) ⟨3325166, by rfl⟩ : syracuseStep 4433555 = 6650333) B6650333
theorem B5678849 : Blo 1494067 5678849 := bstep (se 2 (by rfl) ⟨2129568, by rfl⟩ : syracuseStep 5678849 = 4259137) B4259137
theorem B3786497 : Blo 1494067 3786497 := bstep (se 2 (by rfl) ⟨1419936, by rfl⟩ : syracuseStep 3786497 = 2839873) B2839873
theorem B23029505 : Blo 1494067 23029505 := bstep (se 2 (by rfl) ⟨8636064, by rfl⟩ : syracuseStep 23029505 = 17272129) B17272129
theorem B1681159 : Blo 1494067 1681159 := bstep (se 1 (by rfl) ⟨1260869, by rfl⟩ : syracuseStep 1681159 = 2521739) B2521739
theorem B17499919 : Blo 1494067 17499919 := bstep (se 1 (by rfl) ⟨13124939, by rfl⟩ : syracuseStep 17499919 = 26249879) B26249879
theorem B6145807 : Blo 1494067 6145807 := bstep (se 1 (by rfl) ⟨4609355, by rfl⟩ : syracuseStep 6145807 = 9218711) B9218711
theorem B4040563 : Blo 1494067 4040563 := bstep (se 1 (by rfl) ⟨3030422, by rfl⟩ : syracuseStep 4040563 = 6060845) B6060845
theorem B19154839 : Blo 1494067 19154839 := bstep (se 1 (by rfl) ⟨14366129, by rfl⟩ : syracuseStep 19154839 = 28732259) B28732259
theorem B6473657 : Blo 1494067 6473657 := bstep (se 2 (by rfl) ⟨2427621, by rfl⟩ : syracuseStep 6473657 = 4855243) B4855243
theorem B1681339 : Blo 1494067 1681339 := bstep (se 1 (by rfl) ⟨1261004, by rfl⟩ : syracuseStep 1681339 = 2522009) B2522009
theorem B3786871 : Blo 1494067 3786871 := bstep (se 1 (by rfl) ⟨2840153, by rfl⟩ : syracuseStep 3786871 = 5680307) B5680307
theorem B2836615 : Blo 1494067 2836615 := bstep (se 1 (by rfl) ⟨2127461, by rfl⟩ : syracuseStep 2836615 = 4254923) B4254923
theorem B2558137 : Blo 1494067 2558137 := bstep (se 2 (by rfl) ⟨959301, by rfl⟩ : syracuseStep 2558137 = 1918603) B1918603
theorem B4098233 : Blo 1494067 4098233 := bstep (se 2 (by rfl) ⟨1536837, by rfl⟩ : syracuseStep 4098233 = 3073675) B3073675
theorem B11356361 : Blo 1494067 11356361 := bstep (se 2 (by rfl) ⟨4258635, by rfl⟩ : syracuseStep 11356361 = 8517271) B8517271
theorem B5679305 : Blo 1494067 5679305 := bstep (se 2 (by rfl) ⟨2129739, by rfl⟩ : syracuseStep 5679305 = 4259479) B4259479
theorem B3410311 : Blo 1494067 3410311 := bstep (se 1 (by rfl) ⟨2557733, by rfl⟩ : syracuseStep 3410311 = 5115467) B5115467
theorem B1681807 : Blo 1494067 1681807 := bstep (se 1 (by rfl) ⟨1261355, by rfl⟩ : syracuseStep 1681807 = 2522711) B2522711
theorem B5048729 : Blo 1494067 5048729 := bstep (se 2 (by rfl) ⟨1893273, by rfl⟩ : syracuseStep 5048729 = 3786547) B3786547
theorem B7563779 : Blo 1494067 7563779 := bstep (se 1 (by rfl) ⟨5672834, by rfl⟩ : syracuseStep 7563779 = 11345669) B11345669
theorem B12118571 : Blo 1494067 12118571 := bstep (se 1 (by rfl) ⟨9088928, by rfl⟩ : syracuseStep 12118571 = 18177857) B18177857
theorem B2837177 : Blo 1494067 2837177 := bstep (se 2 (by rfl) ⟨1063941, by rfl⟩ : syracuseStep 2837177 = 2127883) B2127883
theorem B7187201 : Blo 1494067 7187201 := bstep (se 2 (by rfl) ⟨2695200, by rfl⟩ : syracuseStep 7187201 = 5390401) B5390401
theorem B39906053 : Blo 1494067 39906053 := bstep (se 4 (by rfl) ⟨3741192, by rfl⟩ : syracuseStep 39906053 = 7482385) B7482385
theorem B8514355 : Blo 1494067 8514355 := bstep (se 1 (by rfl) ⟨6385766, by rfl⟩ : syracuseStep 8514355 = 12771533) B12771533
theorem B4787059 : Blo 1494067 4787059 := bstep (se 1 (by rfl) ⟨3590294, by rfl⟩ : syracuseStep 4787059 = 7180589) B7180589
theorem B1682311 : Blo 1494067 1682311 := bstep (se 1 (by rfl) ⟨1261733, by rfl⟩ : syracuseStep 1682311 = 2523467) B2523467
theorem B24562693 : Blo 1494067 24562693 := bstep (se 4 (by rfl) ⟨2302752, by rfl⟩ : syracuseStep 24562693 = 4605505) B4605505
theorem B4254763 : Blo 1494067 4254763 := bstep (se 1 (by rfl) ⟨3191072, by rfl⟩ : syracuseStep 4254763 = 6382145) B6382145
theorem B1494075 : Blo 1494067 1494075 := bstep (se 1 (by rfl) ⟨1120556, by rfl⟩ : syracuseStep 1494075 = 2241113) B2241113
theorem B1682491 : Blo 1494067 1682491 := bstep (se 1 (by rfl) ⟨1261868, by rfl⟩ : syracuseStep 1682491 = 2523737) B2523737
theorem B1494151 : Blo 1494067 1494151 := bstep (se 1 (by rfl) ⟨1120613, by rfl⟩ : syracuseStep 1494151 = 2241227) B2241227
theorem B1494159 : Blo 1494067 1494159 := bstep (se 1 (by rfl) ⟨1120619, by rfl⟩ : syracuseStep 1494159 = 2241239) B2241239
theorem B1494203 : Blo 1494067 1494203 := bstep (se 1 (by rfl) ⟨1120652, by rfl⟩ : syracuseStep 1494203 = 2241305) B2241305
theorem B12766409 : Blo 1494067 12766409 := bstep (se 2 (by rfl) ⟨4787403, by rfl⟩ : syracuseStep 12766409 = 9574807) B9574807
theorem B10775753 : Blo 1494067 10775753 := bstep (se 2 (by rfl) ⟨4040907, by rfl⟩ : syracuseStep 10775753 = 8081815) B8081815
theorem B3837185 : Blo 1494067 3837185 := bstep (se 2 (by rfl) ⟨1438944, by rfl⟩ : syracuseStep 3837185 = 2877889) B2877889
theorem B1494279 : Blo 1494067 1494279 := bstep (se 1 (by rfl) ⟨1120709, by rfl⟩ : syracuseStep 1494279 = 2241419) B2241419
theorem B1494287 : Blo 1494067 1494287 := bstep (se 1 (by rfl) ⟨1120715, by rfl⟩ : syracuseStep 1494287 = 2241431) B2241431
theorem B1494331 : Blo 1494067 1494331 := bstep (se 1 (by rfl) ⟨1120748, by rfl⟩ : syracuseStep 1494331 = 2241497) B2241497
theorem B4255037 : Blo 1494067 4255037 := bstep (se 3 (by rfl) ⟨797819, by rfl⟩ : syracuseStep 4255037 = 1595639) B1595639
theorem B7572851 : Blo 1494067 7572851 := bstep (se 1 (by rfl) ⟨5679638, by rfl⟩ : syracuseStep 7572851 = 11359277) B11359277
theorem B34540931 : Blo 1494067 34540931 := bstep (se 1 (by rfl) ⟨25905698, by rfl⟩ : syracuseStep 34540931 = 51811397) B51811397
theorem B3362183 : Blo 1494067 3362183 := bstep (se 1 (by rfl) ⟨2521637, by rfl⟩ : syracuseStep 3362183 = 5043275) B5043275
theorem B1494407 : Blo 1494067 1494407 := bstep (se 1 (by rfl) ⟨1120805, by rfl⟩ : syracuseStep 1494407 = 2241611) B2241611
theorem B1494415 : Blo 1494067 1494415 := bstep (se 1 (by rfl) ⟨1120811, by rfl⟩ : syracuseStep 1494415 = 2241623) B2241623
theorem B1494459 : Blo 1494067 1494459 := bstep (se 1 (by rfl) ⟨1120844, by rfl⟩ : syracuseStep 1494459 = 2241689) B2241689
theorem B1494535 : Blo 1494067 1494535 := bstep (se 1 (by rfl) ⟨1120901, by rfl⟩ : syracuseStep 1494535 = 2241803) B2241803
theorem B1494543 : Blo 1494067 1494543 := bstep (se 1 (by rfl) ⟨1120907, by rfl⟩ : syracuseStep 1494543 = 2241815) B2241815
theorem B1682959 : Blo 1494067 1682959 := bstep (se 1 (by rfl) ⟨1262219, by rfl⟩ : syracuseStep 1682959 = 2524439) B2524439
theorem B3362363 : Blo 1494067 3362363 := bstep (se 1 (by rfl) ⟨2521772, by rfl⟩ : syracuseStep 3362363 = 5043545) B5043545
theorem B1494587 : Blo 1494067 1494587 := bstep (se 1 (by rfl) ⟨1120940, by rfl⟩ : syracuseStep 1494587 = 2241881) B2241881
theorem B30690893 : Blo 1494067 30690893 := bstep (se 3 (by rfl) ⟨5754542, by rfl⟩ : syracuseStep 30690893 = 11509085) B11509085
theorem B1494663 : Blo 1494067 1494663 := bstep (se 1 (by rfl) ⟨1120997, by rfl⟩ : syracuseStep 1494663 = 2241995) B2241995
theorem B1494671 : Blo 1494067 1494671 := bstep (se 1 (by rfl) ⟨1121003, by rfl⟩ : syracuseStep 1494671 = 2242007) B2242007
theorem B4255379 : Blo 1494067 4255379 := bstep (se 1 (by rfl) ⟨3191534, by rfl⟩ : syracuseStep 4255379 = 6383069) B6383069
theorem B3362489 : Blo 1494067 3362489 := bstep (se 2 (by rfl) ⟨1260933, by rfl⟩ : syracuseStep 3362489 = 2521867) B2521867
theorem B1494715 : Blo 1494067 1494715 := bstep (se 1 (by rfl) ⟨1121036, by rfl⟩ : syracuseStep 1494715 = 2242073) B2242073
theorem B16158437 : Blo 1494067 16158437 := bstep (se 4 (by rfl) ⟨1514853, by rfl⟩ : syracuseStep 16158437 = 3029707) B3029707
theorem B16387841 : Blo 1494067 16387841 := bstep (se 2 (by rfl) ⟨6145440, by rfl⟩ : syracuseStep 16387841 = 12290881) B12290881
theorem B1494791 : Blo 1494067 1494791 := bstep (se 1 (by rfl) ⟨1121093, by rfl⟩ : syracuseStep 1494791 = 2242187) B2242187
theorem B1494799 : Blo 1494067 1494799 := bstep (se 1 (by rfl) ⟨1121099, by rfl⟩ : syracuseStep 1494799 = 2242199) B2242199
theorem B2395919 : Blo 1494067 2395919 := bstep (se 1 (by rfl) ⟨1796939, by rfl⟩ : syracuseStep 2395919 = 3593879) B3593879
theorem B1494843 : Blo 1494067 1494843 := bstep (se 1 (by rfl) ⟨1121132, by rfl⟩ : syracuseStep 1494843 = 2242265) B2242265
theorem B2838331 : Blo 1494067 2838331 := bstep (se 1 (by rfl) ⟨2128748, by rfl⟩ : syracuseStep 2838331 = 4257497) B4257497
theorem B7573337 : Blo 1494067 7573337 := bstep (se 2 (by rfl) ⟨2840001, by rfl⟩ : syracuseStep 7573337 = 5680003) B5680003
theorem B1494919 : Blo 1494067 1494919 := bstep (se 1 (by rfl) ⟨1121189, by rfl⟩ : syracuseStep 1494919 = 2242379) B2242379
theorem B1494927 : Blo 1494067 1494927 := bstep (se 1 (by rfl) ⟨1121195, by rfl⟩ : syracuseStep 1494927 = 2242391) B2242391
theorem B1494971 : Blo 1494067 1494971 := bstep (se 1 (by rfl) ⟨1121228, by rfl⟩ : syracuseStep 1494971 = 2242457) B2242457
theorem B1495047 : Blo 1494067 1495047 := bstep (se 1 (by rfl) ⟨1121285, by rfl⟩ : syracuseStep 1495047 = 2242571) B2242571
theorem B3362831 : Blo 1494067 3362831 := bstep (se 1 (by rfl) ⟨2522123, by rfl⟩ : syracuseStep 3362831 = 5044247) B5044247
theorem B1495055 : Blo 1494067 1495055 := bstep (se 1 (by rfl) ⟨1121291, by rfl⟩ : syracuseStep 1495055 = 2242583) B2242583
theorem B3362849 : Blo 1494067 3362849 := bstep (se 2 (by rfl) ⟨1261068, by rfl⟩ : syracuseStep 3362849 = 2522137) B2522137
theorem B3592225 : Blo 1494067 3592225 := bstep (se 2 (by rfl) ⟨1347084, by rfl⟩ : syracuseStep 3592225 = 2694169) B2694169
theorem B1495099 : Blo 1494067 1495099 := bstep (se 1 (by rfl) ⟨1121324, by rfl⟩ : syracuseStep 1495099 = 2242649) B2242649
theorem B7565399 : Blo 1494067 7565399 := bstep (se 1 (by rfl) ⟨5674049, by rfl⟩ : syracuseStep 7565399 = 11348099) B11348099
theorem B4493431 : Blo 1494067 4493431 := bstep (se 1 (by rfl) ⟨3370073, by rfl⟩ : syracuseStep 4493431 = 6740147) B6740147
theorem B1495175 : Blo 1494067 1495175 := bstep (se 1 (by rfl) ⟨1121381, by rfl⟩ : syracuseStep 1495175 = 2242763) B2242763
theorem B1495183 : Blo 1494067 1495183 := bstep (se 1 (by rfl) ⟨1121387, by rfl⟩ : syracuseStep 1495183 = 2242775) B2242775
theorem B1495227 : Blo 1494067 1495227 := bstep (se 1 (by rfl) ⟨1121420, by rfl⟩ : syracuseStep 1495227 = 2242841) B2242841
theorem B8515813 : Blo 1494067 8515813 := bstep (se 4 (by rfl) ⟨798357, by rfl⟩ : syracuseStep 8515813 = 1596715) B1596715
theorem B1495303 : Blo 1494067 1495303 := bstep (se 1 (by rfl) ⟨1121477, by rfl⟩ : syracuseStep 1495303 = 2242955) B2242955
theorem B1495311 : Blo 1494067 1495311 := bstep (se 1 (by rfl) ⟨1121483, by rfl⟩ : syracuseStep 1495311 = 2242967) B2242967
theorem B2838817 : Blo 1494067 2838817 := bstep (se 2 (by rfl) ⟨1064556, by rfl⟩ : syracuseStep 2838817 = 2129113) B2129113
theorem B1495355 : Blo 1494067 1495355 := bstep (se 1 (by rfl) ⟨1121516, by rfl⟩ : syracuseStep 1495355 = 2243033) B2243033
theorem B3363191 : Blo 1494067 3363191 := bstep (se 1 (by rfl) ⟨2522393, by rfl⟩ : syracuseStep 3363191 = 5044787) B5044787
theorem B1495431 : Blo 1494067 1495431 := bstep (se 1 (by rfl) ⟨1121573, by rfl⟩ : syracuseStep 1495431 = 2243147) B2243147
theorem B1495439 : Blo 1494067 1495439 := bstep (se 1 (by rfl) ⟨1121579, by rfl⟩ : syracuseStep 1495439 = 2243159) B2243159
theorem B1495483 : Blo 1494067 1495483 := bstep (se 1 (by rfl) ⟨1121612, by rfl⟩ : syracuseStep 1495483 = 2243225) B2243225
theorem B3592649 : Blo 1494067 3592649 := bstep (se 2 (by rfl) ⟨1347243, by rfl⟩ : syracuseStep 3592649 = 2694487) B2694487
theorem B1495559 : Blo 1494067 1495559 := bstep (se 1 (by rfl) ⟨1121669, by rfl⟩ : syracuseStep 1495559 = 2243339) B2243339
theorem B1495567 : Blo 1494067 1495567 := bstep (se 1 (by rfl) ⟨1121675, by rfl⟩ : syracuseStep 1495567 = 2243351) B2243351
theorem B3191329 : Blo 1494067 3191329 := bstep (se 2 (by rfl) ⟨1196748, by rfl⟩ : syracuseStep 3191329 = 2393497) B2393497
theorem B3363371 : Blo 1494067 3363371 := bstep (se 1 (by rfl) ⟨2522528, by rfl⟩ : syracuseStep 3363371 = 5045057) B5045057
theorem B3592763 : Blo 1494067 3592763 := bstep (se 1 (by rfl) ⟨2694572, by rfl⟩ : syracuseStep 3592763 = 5389145) B5389145
theorem B1495611 : Blo 1494067 1495611 := bstep (se 1 (by rfl) ⟨1121708, by rfl⟩ : syracuseStep 1495611 = 2243417) B2243417
theorem B7565885 : Blo 1494067 7565885 := bstep (se 3 (by rfl) ⟨1418603, by rfl⟩ : syracuseStep 7565885 = 2837207) B2837207
theorem B2241143 : Blo 1494067 2241143 := bstep (se 1 (by rfl) ⟨1680857, by rfl⟩ : syracuseStep 2241143 = 3361715) B3361715
theorem B1495687 : Blo 1494067 1495687 := bstep (se 1 (by rfl) ⟨1121765, by rfl⟩ : syracuseStep 1495687 = 2243531) B2243531
theorem B2241167 : Blo 1494067 2241167 := bstep (se 1 (by rfl) ⟨1680875, by rfl⟩ : syracuseStep 2241167 = 3361751) B3361751
theorem B2273935 : Blo 1494067 2273935 := bstep (se 1 (by rfl) ⟨1705451, by rfl⟩ : syracuseStep 2273935 = 3410903) B3410903
theorem B1495695 : Blo 1494067 1495695 := bstep (se 1 (by rfl) ⟨1121771, by rfl⟩ : syracuseStep 1495695 = 2243543) B2243543
theorem B2241209 : Blo 1494067 2241209 := bstep (se 2 (by rfl) ⟨840453, by rfl⟩ : syracuseStep 2241209 = 1680907) B1680907
theorem B1495739 : Blo 1494067 1495739 := bstep (se 1 (by rfl) ⟨1121804, by rfl⟩ : syracuseStep 1495739 = 2243609) B2243609
theorem B2241287 : Blo 1494067 2241287 := bstep (se 1 (by rfl) ⟨1680965, by rfl⟩ : syracuseStep 2241287 = 3361931) B3361931
theorem B1495815 : Blo 1494067 1495815 := bstep (se 1 (by rfl) ⟨1121861, by rfl⟩ : syracuseStep 1495815 = 2243723) B2243723
theorem B4789007 : Blo 1494067 4789007 := bstep (se 1 (by rfl) ⟨3591755, by rfl⟩ : syracuseStep 4789007 = 7183511) B7183511
theorem B1495823 : Blo 1494067 1495823 := bstep (se 1 (by rfl) ⟨1121867, by rfl⟩ : syracuseStep 1495823 = 2243735) B2243735
theorem B2241323 : Blo 1494067 2241323 := bstep (se 1 (by rfl) ⟨1680992, by rfl⟩ : syracuseStep 2241323 = 3361985) B3361985
theorem B1495867 : Blo 1494067 1495867 := bstep (se 1 (by rfl) ⟨1121900, by rfl⟩ : syracuseStep 1495867 = 2243801) B2243801
theorem B2241353 : Blo 1494067 2241353 := bstep (se 2 (by rfl) ⟨840507, by rfl⟩ : syracuseStep 2241353 = 1681015) B1681015
theorem B19428185 : Blo 1494067 19428185 := bstep (se 2 (by rfl) ⟨7285569, by rfl⟩ : syracuseStep 19428185 = 14571139) B14571139
theorem B5043059 : Blo 1494067 5043059 := bstep (se 1 (by rfl) ⟨3782294, by rfl⟩ : syracuseStep 5043059 = 7564589) B7564589
theorem B1495943 : Blo 1494067 1495943 := bstep (se 1 (by rfl) ⟨1121957, by rfl⟩ : syracuseStep 1495943 = 2243915) B2243915
theorem B1495951 : Blo 1494067 1495951 := bstep (se 1 (by rfl) ⟨1121963, by rfl⟩ : syracuseStep 1495951 = 2243927) B2243927
theorem B3363731 : Blo 1494067 3363731 := bstep (se 1 (by rfl) ⟨2522798, by rfl⟩ : syracuseStep 3363731 = 5045597) B5045597
theorem B2241467 : Blo 1494067 2241467 := bstep (se 1 (by rfl) ⟨1681100, by rfl⟩ : syracuseStep 2241467 = 3362201) B3362201
theorem B1495995 : Blo 1494067 1495995 := bstep (se 1 (by rfl) ⟨1121996, by rfl⟩ : syracuseStep 1495995 = 2243993) B2243993
theorem B3363785 : Blo 1494067 3363785 := bstep (se 2 (by rfl) ⟨1261419, by rfl⟩ : syracuseStep 3363785 = 2522839) B2522839
theorem B2241527 : Blo 1494067 2241527 := bstep (se 1 (by rfl) ⟨1681145, by rfl⟩ : syracuseStep 2241527 = 3362291) B3362291
theorem B2241551 : Blo 1494067 2241551 := bstep (se 1 (by rfl) ⟨1681163, by rfl⟩ : syracuseStep 2241551 = 3362327) B3362327
theorem B2241593 : Blo 1494067 2241593 := bstep (se 2 (by rfl) ⟨840597, by rfl⟩ : syracuseStep 2241593 = 1681195) B1681195
theorem B36844631 : Blo 1494067 36844631 := bstep (se 1 (by rfl) ⟨27633473, by rfl⟩ : syracuseStep 36844631 = 55266947) B55266947
theorem B2241671 : Blo 1494067 2241671 := bstep (se 1 (by rfl) ⟨1681253, by rfl⟩ : syracuseStep 2241671 = 3362507) B3362507
theorem B2241707 : Blo 1494067 2241707 := bstep (se 1 (by rfl) ⟨1681280, by rfl⟩ : syracuseStep 2241707 = 3362561) B3362561
theorem B2241737 : Blo 1494067 2241737 := bstep (se 2 (by rfl) ⟨840651, by rfl⟩ : syracuseStep 2241737 = 1681303) B1681303
theorem B2241851 : Blo 1494067 2241851 := bstep (se 1 (by rfl) ⟨1681388, by rfl⟩ : syracuseStep 2241851 = 3362777) B3362777
theorem B2241911 : Blo 1494067 2241911 := bstep (se 1 (by rfl) ⟨1681433, by rfl⟩ : syracuseStep 2241911 = 3362867) B3362867
theorem B2241935 : Blo 1494067 2241935 := bstep (se 1 (by rfl) ⟨1681451, by rfl⟩ : syracuseStep 2241935 = 3362903) B3362903
theorem B2241977 : Blo 1494067 2241977 := bstep (se 2 (by rfl) ⟨840741, by rfl⟩ : syracuseStep 2241977 = 1681483) B1681483
theorem B5387705 : Blo 1494067 5387705 := bstep (se 2 (by rfl) ⟨2020389, by rfl⟩ : syracuseStep 5387705 = 4040779) B4040779
theorem B40924601 : Blo 1494067 40924601 := bstep (se 2 (by rfl) ⟨15346725, by rfl⟩ : syracuseStep 40924601 = 30693451) B30693451
theorem B17036729 : Blo 1494067 17036729 := bstep (se 2 (by rfl) ⟨6388773, by rfl⟩ : syracuseStep 17036729 = 12777547) B12777547
theorem B2242055 : Blo 1494067 2242055 := bstep (se 1 (by rfl) ⟨1681541, by rfl⟩ : syracuseStep 2242055 = 3363083) B3363083
theorem B27293213 : Blo 1494067 27293213 := bstep (se 3 (by rfl) ⟨5117477, by rfl⟩ : syracuseStep 27293213 = 10234955) B10234955
theorem B2242091 : Blo 1494067 2242091 := bstep (se 1 (by rfl) ⟨1681568, by rfl⟩ : syracuseStep 2242091 = 3363137) B3363137
theorem B2840123 : Blo 1494067 2840123 := bstep (se 1 (by rfl) ⟨2130092, by rfl⟩ : syracuseStep 2840123 = 4260185) B4260185
theorem B2242121 : Blo 1494067 2242121 := bstep (se 2 (by rfl) ⟨840795, by rfl⟩ : syracuseStep 2242121 = 1681591) B1681591
theorem B3364487 : Blo 1494067 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B2242235 : Blo 1494067 2242235 := bstep (se 1 (by rfl) ⟨1681676, by rfl⟩ : syracuseStep 2242235 = 3363353) B3363353
theorem B7673545 : Blo 1494067 7673545 := bstep (se 2 (by rfl) ⟨2877579, by rfl⟩ : syracuseStep 7673545 = 5755159) B5755159
theorem B2242295 : Blo 1494067 2242295 := bstep (se 1 (by rfl) ⟨1681721, by rfl⟩ : syracuseStep 2242295 = 3363443) B3363443
theorem B10770191 : Blo 1494067 10770191 := bstep (se 1 (by rfl) ⟨8077643, by rfl⟩ : syracuseStep 10770191 = 16155287) B16155287
theorem B2242319 : Blo 1494067 2242319 := bstep (se 1 (by rfl) ⟨1681739, by rfl⟩ : syracuseStep 2242319 = 3363479) B3363479
theorem B17258275 : Blo 1494067 17258275 := bstep (se 1 (by rfl) ⟨12943706, by rfl⟩ : syracuseStep 17258275 = 25887413) B25887413
theorem B12769073 : Blo 1494067 12769073 := bstep (se 2 (by rfl) ⟨4788402, by rfl⟩ : syracuseStep 12769073 = 9576805) B9576805
theorem B2242361 : Blo 1494067 2242361 := bstep (se 2 (by rfl) ⟨840885, by rfl⟩ : syracuseStep 2242361 = 1681771) B1681771
theorem B3364667 : Blo 1494067 3364667 := bstep (se 1 (by rfl) ⟨2523500, by rfl⟩ : syracuseStep 3364667 = 5047001) B5047001
theorem B4257623 : Blo 1494067 4257623 := bstep (se 1 (by rfl) ⟨3193217, by rfl⟩ : syracuseStep 4257623 = 6386435) B6386435
theorem B3594071 : Blo 1494067 3594071 := bstep (se 1 (by rfl) ⟨2695553, by rfl⟩ : syracuseStep 3594071 = 5391107) B5391107
theorem B2242439 : Blo 1494067 2242439 := bstep (se 1 (by rfl) ⟨1681829, by rfl⟩ : syracuseStep 2242439 = 3363659) B3363659
theorem B18175907 : Blo 1494067 18175907 := bstep (se 1 (by rfl) ⟨13631930, by rfl⟩ : syracuseStep 18175907 = 27263861) B27263861
theorem B2242475 : Blo 1494067 2242475 := bstep (se 1 (by rfl) ⟨1681856, by rfl⟩ : syracuseStep 2242475 = 3363713) B3363713
theorem B3364793 : Blo 1494067 3364793 := bstep (se 2 (by rfl) ⟨1261797, by rfl⟩ : syracuseStep 3364793 = 2523595) B2523595
theorem B2242505 : Blo 1494067 2242505 := bstep (se 2 (by rfl) ⟨840939, by rfl⟩ : syracuseStep 2242505 = 1681879) B1681879
theorem B5674961 : Blo 1494067 5674961 := bstep (se 2 (by rfl) ⟨2128110, by rfl⟩ : syracuseStep 5674961 = 4256221) B4256221
theorem B2242619 : Blo 1494067 2242619 := bstep (se 1 (by rfl) ⟨1681964, by rfl⟩ : syracuseStep 2242619 = 3363929) B3363929
theorem B6559805 : Blo 1494067 6559805 := bstep (se 3 (by rfl) ⟨1229963, by rfl⟩ : syracuseStep 6559805 = 2459927) B2459927
theorem B3782771 : Blo 1494067 3782771 := bstep (se 1 (by rfl) ⟨2837078, by rfl⟩ : syracuseStep 3782771 = 5674157) B5674157
theorem B2242679 : Blo 1494067 2242679 := bstep (se 1 (by rfl) ⟨1682009, by rfl⟩ : syracuseStep 2242679 = 3364019) B3364019
theorem B2242703 : Blo 1494067 2242703 := bstep (se 1 (by rfl) ⟨1682027, by rfl⟩ : syracuseStep 2242703 = 3364055) B3364055
theorem B2521273 : Blo 1494067 2521273 := bstep (se 2 (by rfl) ⟨945477, by rfl⟩ : syracuseStep 2521273 = 1890955) B1890955
theorem B2242745 : Blo 1494067 2242745 := bstep (se 2 (by rfl) ⟨841029, by rfl⟩ : syracuseStep 2242745 = 1682059) B1682059
theorem B2242823 : Blo 1494067 2242823 := bstep (se 1 (by rfl) ⟨1682117, by rfl⟩ : syracuseStep 2242823 = 3364235) B3364235
theorem B3365135 : Blo 1494067 3365135 := bstep (se 1 (by rfl) ⟨2523851, by rfl⟩ : syracuseStep 3365135 = 5047703) B5047703
theorem B3365153 : Blo 1494067 3365153 := bstep (se 2 (by rfl) ⟨1261932, by rfl⟩ : syracuseStep 3365153 = 2523865) B2523865
theorem B2242859 : Blo 1494067 2242859 := bstep (se 1 (by rfl) ⟨1682144, by rfl⟩ : syracuseStep 2242859 = 3364289) B3364289
theorem B7567667 : Blo 1494067 7567667 := bstep (se 1 (by rfl) ⟨5675750, by rfl⟩ : syracuseStep 7567667 = 11351501) B11351501
theorem B2242889 : Blo 1494067 2242889 := bstep (se 2 (by rfl) ⟨841083, by rfl⟩ : syracuseStep 2242889 = 1682167) B1682167
theorem B4544855 : Blo 1494067 4544855 := bstep (se 1 (by rfl) ⟨3408641, by rfl⟩ : syracuseStep 4544855 = 6817283) B6817283
theorem B4544903 : Blo 1494067 4544903 := bstep (se 1 (by rfl) ⟨3408677, by rfl⟩ : syracuseStep 4544903 = 6817355) B6817355
theorem B5675417 : Blo 1494067 5675417 := bstep (se 2 (by rfl) ⟨2128281, by rfl⟩ : syracuseStep 5675417 = 4256563) B4256563
theorem B2243003 : Blo 1494067 2243003 := bstep (se 1 (by rfl) ⟨1682252, by rfl⟩ : syracuseStep 2243003 = 3364505) B3364505
theorem B12769757 : Blo 1494067 12769757 := bstep (se 3 (by rfl) ⟨2394329, by rfl⟩ : syracuseStep 12769757 = 4788659) B4788659
theorem B2243063 : Blo 1494067 2243063 := bstep (se 1 (by rfl) ⟨1682297, by rfl⟩ : syracuseStep 2243063 = 3364595) B3364595
theorem B2243087 : Blo 1494067 2243087 := bstep (se 1 (by rfl) ⟨1682315, by rfl⟩ : syracuseStep 2243087 = 3364631) B3364631
theorem B8509981 : Blo 1494067 8509981 := bstep (se 3 (by rfl) ⟨1595621, by rfl⟩ : syracuseStep 8509981 = 3191243) B3191243
theorem B2243129 : Blo 1494067 2243129 := bstep (se 2 (by rfl) ⟨841173, by rfl⟩ : syracuseStep 2243129 = 1682347) B1682347
theorem B3783287 : Blo 1494067 3783287 := bstep (se 1 (by rfl) ⟨2837465, by rfl⟩ : syracuseStep 3783287 = 5674931) B5674931
theorem B7567991 : Blo 1494067 7567991 := bstep (se 1 (by rfl) ⟨5675993, by rfl⟩ : syracuseStep 7567991 = 11351987) B11351987
theorem B3365495 : Blo 1494067 3365495 := bstep (se 1 (by rfl) ⟨2524121, by rfl⟩ : syracuseStep 3365495 = 5048243) B5048243
theorem B2243207 : Blo 1494067 2243207 := bstep (se 1 (by rfl) ⟨1682405, by rfl⟩ : syracuseStep 2243207 = 3364811) B3364811
theorem B2128555 : Blo 1494067 2128555 := bstep (se 1 (by rfl) ⟨1596416, by rfl⟩ : syracuseStep 2128555 = 3192833) B3192833
theorem B2243243 : Blo 1494067 2243243 := bstep (se 1 (by rfl) ⟨1682432, by rfl⟩ : syracuseStep 2243243 = 3364865) B3364865
theorem B2243273 : Blo 1494067 2243273 := bstep (se 2 (by rfl) ⟨841227, by rfl⟩ : syracuseStep 2243273 = 1682455) B1682455
theorem B19167961 : Blo 1494067 19167961 := bstep (se 2 (by rfl) ⟨7187985, by rfl⟩ : syracuseStep 19167961 = 14375971) B14375971
theorem B3365675 : Blo 1494067 3365675 := bstep (se 1 (by rfl) ⟨2524256, by rfl⟩ : syracuseStep 3365675 = 5048513) B5048513
theorem B10779443 : Blo 1494067 10779443 := bstep (se 1 (by rfl) ⟨8084582, by rfl⟩ : syracuseStep 10779443 = 16169165) B16169165
theorem B2243387 : Blo 1494067 2243387 := bstep (se 1 (by rfl) ⟨1682540, by rfl⟩ : syracuseStep 2243387 = 3365081) B3365081
theorem B4545341 : Blo 1494067 4545341 := bstep (se 3 (by rfl) ⟨852251, by rfl⟩ : syracuseStep 4545341 = 1704503) B1704503
theorem B2521975 : Blo 1494067 2521975 := bstep (se 1 (by rfl) ⟨1891481, by rfl⟩ : syracuseStep 2521975 = 3782963) B3782963
theorem B2243447 : Blo 1494067 2243447 := bstep (se 1 (by rfl) ⟨1682585, by rfl⟩ : syracuseStep 2243447 = 3365171) B3365171
theorem B2128783 : Blo 1494067 2128783 := bstep (se 1 (by rfl) ⟨1596587, by rfl⟩ : syracuseStep 2128783 = 3193175) B3193175
theorem B2243471 : Blo 1494067 2243471 := bstep (se 1 (by rfl) ⟨1682603, by rfl⟩ : syracuseStep 2243471 = 3365207) B3365207
theorem B8518547 : Blo 1494067 8518547 := bstep (se 1 (by rfl) ⟨6388910, by rfl⟩ : syracuseStep 8518547 = 12777821) B12777821
theorem B2243513 : Blo 1494067 2243513 := bstep (se 2 (by rfl) ⟨841317, by rfl⟩ : syracuseStep 2243513 = 1682635) B1682635
theorem B2243591 : Blo 1494067 2243591 := bstep (se 1 (by rfl) ⟨1682693, by rfl⟩ : syracuseStep 2243591 = 3365387) B3365387
theorem B15350795 : Blo 1494067 15350795 := bstep (se 1 (by rfl) ⟨11513096, by rfl⟩ : syracuseStep 15350795 = 23026193) B23026193
theorem B4791325 : Blo 1494067 4791325 := bstep (se 3 (by rfl) ⟨898373, by rfl⟩ : syracuseStep 4791325 = 1796747) B1796747
theorem B8510507 : Blo 1494067 8510507 := bstep (se 1 (by rfl) ⟨6382880, by rfl⟩ : syracuseStep 8510507 = 12765761) B12765761
theorem B2243627 : Blo 1494067 2243627 := bstep (se 1 (by rfl) ⟨1682720, by rfl⟩ : syracuseStep 2243627 = 3365441) B3365441
theorem B2522171 : Blo 1494067 2522171 := bstep (se 1 (by rfl) ⟨1891628, by rfl⟩ : syracuseStep 2522171 = 3783257) B3783257
theorem B2243657 : Blo 1494067 2243657 := bstep (se 2 (by rfl) ⟨841371, by rfl⟩ : syracuseStep 2243657 = 1682743) B1682743
theorem B9337943 : Blo 1494067 9337943 := bstep (se 1 (by rfl) ⟨7003457, by rfl⟩ : syracuseStep 9337943 = 14006915) B14006915
theorem B3366035 : Blo 1494067 3366035 := bstep (se 1 (by rfl) ⟨2524526, by rfl⟩ : syracuseStep 3366035 = 5049053) B5049053
theorem B2243771 : Blo 1494067 2243771 := bstep (se 1 (by rfl) ⟨1682828, by rfl⟩ : syracuseStep 2243771 = 3365657) B3365657
theorem B3366089 : Blo 1494067 3366089 := bstep (se 2 (by rfl) ⟨1262283, by rfl⟩ : syracuseStep 3366089 = 2524567) B2524567
theorem B2243831 : Blo 1494067 2243831 := bstep (se 1 (by rfl) ⟨1682873, by rfl⟩ : syracuseStep 2243831 = 3365747) B3365747
theorem B2243855 : Blo 1494067 2243855 := bstep (se 1 (by rfl) ⟨1682891, by rfl⟩ : syracuseStep 2243855 = 3365783) B3365783
theorem B2243897 : Blo 1494067 2243897 := bstep (se 2 (by rfl) ⟨841461, by rfl⟩ : syracuseStep 2243897 = 1682923) B1682923
theorem B2243975 : Blo 1494067 2243975 := bstep (se 1 (by rfl) ⟨1682981, by rfl⟩ : syracuseStep 2243975 = 3365963) B3365963
theorem B5045651 : Blo 1494067 5045651 := bstep (se 1 (by rfl) ⟨3784238, by rfl⟩ : syracuseStep 5045651 = 7568477) B7568477
theorem B2244011 : Blo 1494067 2244011 := bstep (se 1 (by rfl) ⟨1683008, by rfl⟩ : syracuseStep 2244011 = 3366017) B3366017
theorem B2522569 : Blo 1494067 2522569 := bstep (se 2 (by rfl) ⟨945963, by rfl⟩ : syracuseStep 2522569 = 1891927) B1891927
theorem B2244041 : Blo 1494067 2244041 := bstep (se 2 (by rfl) ⟨841515, by rfl⟩ : syracuseStep 2244041 = 1683031) B1683031
theorem B17251805 : Blo 1494067 17251805 := bstep (se 3 (by rfl) ⟨3234713, by rfl⟩ : syracuseStep 17251805 = 6469427) B6469427
theorem B1891831 : Blo 1494067 1891831 := bstep (se 1 (by rfl) ⟨1418873, by rfl⟩ : syracuseStep 1891831 = 2837747) B2837747
theorem B5676587 : Blo 1494067 5676587 := bstep (se 1 (by rfl) ⟨4257440, by rfl⟩ : syracuseStep 5676587 = 8514881) B8514881
theorem B4210237 : Blo 1494067 4210237 := bstep (se 3 (by rfl) ⟨789419, by rfl⟩ : syracuseStep 4210237 = 1578839) B1578839
theorem B7568963 : Blo 1494067 7568963 := bstep (se 1 (by rfl) ⟨5676722, by rfl⟩ : syracuseStep 7568963 = 11353445) B11353445
theorem B3784279 : Blo 1494067 3784279 := bstep (se 1 (by rfl) ⟨2838209, by rfl⟩ : syracuseStep 3784279 = 5676419) B5676419
theorem B8519255 : Blo 1494067 8519255 := bstep (se 1 (by rfl) ⟨6389441, by rfl⟩ : syracuseStep 8519255 = 12778883) B12778883
theorem B3071759 : Blo 1494067 3071759 := bstep (se 1 (by rfl) ⟨2303819, by rfl⟩ : syracuseStep 3071759 = 4607639) B4607639
theorem B1892155 : Blo 1494067 1892155 := bstep (se 1 (by rfl) ⟨1419116, by rfl⟩ : syracuseStep 1892155 = 2838233) B2838233
theorem B3784583 : Blo 1494067 3784583 := bstep (se 1 (by rfl) ⟨2838437, by rfl⟩ : syracuseStep 3784583 = 5676875) B5676875
theorem B7569287 : Blo 1494067 7569287 := bstep (se 1 (by rfl) ⟨5676965, by rfl⟩ : syracuseStep 7569287 = 11353931) B11353931
theorem B2523143 : Blo 1494067 2523143 := bstep (se 1 (by rfl) ⟨1892357, by rfl⟩ : syracuseStep 2523143 = 3784715) B3784715
theorem B8519687 : Blo 1494067 8519687 := bstep (se 1 (by rfl) ⟨6389765, by rfl⟩ : syracuseStep 8519687 = 12779531) B12779531
theorem B38830103 : Blo 1494067 38830103 := bstep (se 1 (by rfl) ⟨29122577, by rfl⟩ : syracuseStep 38830103 = 58245155) B58245155
theorem B11354417 : Blo 1494067 11354417 := bstep (se 2 (by rfl) ⟨4257906, by rfl⟩ : syracuseStep 11354417 = 8515813) B8515813
theorem B22454597 : Blo 1494067 22454597 := bstep (se 4 (by rfl) ⟨2105118, by rfl⟩ : syracuseStep 22454597 = 4210237) B4210237
theorem B2523487 : Blo 1494067 2523487 := bstep (se 1 (by rfl) ⟨1892615, by rfl⟩ : syracuseStep 2523487 = 3785231) B3785231
theorem B3785089 : Blo 1494067 3785089 := bstep (se 2 (by rfl) ⟨1419408, by rfl⟩ : syracuseStep 3785089 = 2838817) B2838817
theorem B2523575 : Blo 1494067 2523575 := bstep (se 1 (by rfl) ⟨1892681, by rfl⟩ : syracuseStep 2523575 = 3785363) B3785363
theorem B6382061 : Blo 1494067 6382061 := bstep (se 3 (by rfl) ⟨1196636, by rfl⟩ : syracuseStep 6382061 = 2393273) B2393273
theorem B10928621 : Blo 1494067 10928621 := bstep (se 3 (by rfl) ⟨2049116, by rfl⟩ : syracuseStep 10928621 = 4098233) B4098233
theorem B4547081 : Blo 1494067 4547081 := bstep (se 2 (by rfl) ⟨1705155, by rfl⟩ : syracuseStep 4547081 = 3410311) B3410311
theorem B9585211 : Blo 1494067 9585211 := bstep (se 1 (by rfl) ⟨7188908, by rfl⟩ : syracuseStep 9585211 = 14377817) B14377817
theorem B11346641 : Blo 1494067 11346641 := bstep (se 2 (by rfl) ⟨4254990, by rfl⟩ : syracuseStep 11346641 = 8509981) B8509981
theorem B3031913 : Blo 1494067 3031913 := bstep (se 2 (by rfl) ⟨1136967, by rfl⟩ : syracuseStep 3031913 = 2273935) B2273935
theorem B2524169 : Blo 1494067 2524169 := bstep (se 2 (by rfl) ⟨946563, by rfl⟩ : syracuseStep 2524169 = 1893127) B1893127
theorem B18195475 : Blo 1494067 18195475 := bstep (se 1 (by rfl) ⟨13646606, by rfl⟩ : syracuseStep 18195475 = 27293213) B27293213
theorem B6382745 : Blo 1494067 6382745 := bstep (se 2 (by rfl) ⟨2393529, by rfl⟩ : syracuseStep 6382745 = 4787059) B4787059
theorem B3785899 : Blo 1494067 3785899 := bstep (se 1 (by rfl) ⟨2839424, by rfl⟩ : syracuseStep 3785899 = 5678849) B5678849
theorem B2524331 : Blo 1494067 2524331 := bstep (se 1 (by rfl) ⟨1893248, by rfl⟩ : syracuseStep 2524331 = 3786497) B3786497
theorem B15353003 : Blo 1494067 15353003 := bstep (se 1 (by rfl) ⟨11514752, by rfl⟩ : syracuseStep 15353003 = 23029505) B23029505
theorem B8512715 : Blo 1494067 8512715 := bstep (se 1 (by rfl) ⟨6384536, by rfl⟩ : syracuseStep 8512715 = 12769073) B12769073
theorem B12117271 : Blo 1494067 12117271 := bstep (se 1 (by rfl) ⟨9087953, by rfl⟩ : syracuseStep 12117271 = 18175907) B18175907
theorem B7570907 : Blo 1494067 7570907 := bstep (se 1 (by rfl) ⟨5678180, by rfl⟩ : syracuseStep 7570907 = 11356361) B11356361
theorem B3786203 : Blo 1494067 3786203 := bstep (se 1 (by rfl) ⟨2839652, by rfl⟩ : syracuseStep 3786203 = 5679305) B5679305
theorem B8513171 : Blo 1494067 8513171 := bstep (se 1 (by rfl) ⟨6384878, by rfl⟩ : syracuseStep 8513171 = 12769757) B12769757
theorem B8079047 : Blo 1494067 8079047 := bstep (se 1 (by rfl) ⟨6059285, by rfl⟩ : syracuseStep 8079047 = 12118571) B12118571
theorem B4097785 : Blo 1494067 4097785 := bstep (se 2 (by rfl) ⟨1536669, by rfl⟩ : syracuseStep 4097785 = 3073339) B3073339
theorem B7186295 : Blo 1494067 7186295 := bstep (se 1 (by rfl) ⟨5389721, by rfl⟩ : syracuseStep 7186295 = 10779443) B10779443
theorem B5679031 : Blo 1494067 5679031 := bstep (se 1 (by rfl) ⟨4259273, by rfl⟩ : syracuseStep 5679031 = 8518547) B8518547
theorem B7571393 : Blo 1494067 7571393 := bstep (se 2 (by rfl) ⟨2839272, by rfl⟩ : syracuseStep 7571393 = 5678545) B5678545
theorem B10233863 : Blo 1494067 10233863 := bstep (se 1 (by rfl) ⟨7675397, by rfl⟩ : syracuseStep 10233863 = 15350795) B15350795
theorem B1681447 : Blo 1494067 1681447 := bstep (se 1 (by rfl) ⟨1261085, by rfl⟩ : syracuseStep 1681447 = 2522171) B2522171
theorem B2558123 : Blo 1494067 2558123 := bstep (se 1 (by rfl) ⟨1918592, by rfl⟩ : syracuseStep 2558123 = 3837185) B3837185
theorem B2836691 : Blo 1494067 2836691 := bstep (se 1 (by rfl) ⟨2127518, by rfl⟩ : syracuseStep 2836691 = 4255037) B4255037
theorem B51808493 : Blo 1494067 51808493 := bstep (se 3 (by rfl) ⟨9714092, by rfl⟩ : syracuseStep 51808493 = 19428185) B19428185
theorem B5048567 : Blo 1494067 5048567 := bstep (se 1 (by rfl) ⟨3786425, by rfl⟩ : syracuseStep 5048567 = 7572851) B7572851
theorem B23333225 : Blo 1494067 23333225 := bstep (se 2 (by rfl) ⟨8749959, by rfl⟩ : syracuseStep 23333225 = 17499919) B17499919
theorem B8194409 : Blo 1494067 8194409 := bstep (se 2 (by rfl) ⟨3072903, by rfl⟩ : syracuseStep 8194409 = 6145807) B6145807
theorem B5679503 : Blo 1494067 5679503 := bstep (se 1 (by rfl) ⟨4259627, by rfl⟩ : syracuseStep 5679503 = 8519255) B8519255
theorem B2836919 : Blo 1494067 2836919 := bstep (se 1 (by rfl) ⟨2127689, by rfl⟩ : syracuseStep 2836919 = 4255379) B4255379
theorem B5048891 : Blo 1494067 5048891 := bstep (se 1 (by rfl) ⟨3786668, by rfl⟩ : syracuseStep 5048891 = 7573337) B7573337
theorem B5991241 : Blo 1494067 5991241 := bstep (se 2 (by rfl) ⟨2246715, by rfl⟩ : syracuseStep 5991241 = 4493431) B4493431
theorem B5049161 : Blo 1494067 5049161 := bstep (se 2 (by rfl) ⟨1893435, by rfl⟩ : syracuseStep 5049161 = 3786871) B3786871
theorem B3361697 : Blo 1494067 3361697 := bstep (se 2 (by rfl) ⟨1260636, by rfl⟩ : syracuseStep 3361697 = 2521273) B2521273
theorem B3410849 : Blo 1494067 3410849 := bstep (se 2 (by rfl) ⟨1279068, by rfl⟩ : syracuseStep 3410849 = 2558137) B2558137
theorem B2395099 : Blo 1494067 2395099 := bstep (se 1 (by rfl) ⟨1796324, by rfl⟩ : syracuseStep 2395099 = 3592649) B3592649
theorem B621849635 : Blo 1494067 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B2395175 : Blo 1494067 2395175 := bstep (se 1 (by rfl) ⟨1796381, by rfl⟩ : syracuseStep 2395175 = 3592763) B3592763
theorem B1494095 : Blo 1494067 1494095 := bstep (se 1 (by rfl) ⟨1120571, by rfl⟩ : syracuseStep 1494095 = 2241143) B2241143
theorem B11349071 : Blo 1494067 11349071 := bstep (se 1 (by rfl) ⟨8511803, by rfl⟩ : syracuseStep 11349071 = 17023607) B17023607
theorem B1494111 : Blo 1494067 1494111 := bstep (se 1 (by rfl) ⟨1120583, by rfl⟩ : syracuseStep 1494111 = 2241167) B2241167
theorem B1494139 : Blo 1494067 1494139 := bstep (se 1 (by rfl) ⟨1120604, by rfl⟩ : syracuseStep 1494139 = 2241209) B2241209
theorem B1494191 : Blo 1494067 1494191 := bstep (se 1 (by rfl) ⟨1120643, by rfl⟩ : syracuseStep 1494191 = 2241287) B2241287
theorem B1494215 : Blo 1494067 1494215 := bstep (se 1 (by rfl) ⟨1120661, by rfl⟩ : syracuseStep 1494215 = 2241323) B2241323
theorem B1494235 : Blo 1494067 1494235 := bstep (se 1 (by rfl) ⟨1120676, by rfl⟩ : syracuseStep 1494235 = 2241353) B2241353
theorem B3362039 : Blo 1494067 3362039 := bstep (se 1 (by rfl) ⟨2521529, by rfl⟩ : syracuseStep 3362039 = 5043059) B5043059
theorem B1494311 : Blo 1494067 1494311 := bstep (se 1 (by rfl) ⟨1120733, by rfl⟩ : syracuseStep 1494311 = 2241467) B2241467
theorem B1494351 : Blo 1494067 1494351 := bstep (se 1 (by rfl) ⟨1120763, by rfl⟩ : syracuseStep 1494351 = 2241527) B2241527
theorem B1494367 : Blo 1494067 1494367 := bstep (se 1 (by rfl) ⟨1120775, by rfl⟩ : syracuseStep 1494367 = 2241551) B2241551
theorem B1494395 : Blo 1494067 1494395 := bstep (se 1 (by rfl) ⟨1120796, by rfl⟩ : syracuseStep 1494395 = 2241593) B2241593
theorem B4255105 : Blo 1494067 4255105 := bstep (se 2 (by rfl) ⟨1595664, by rfl⟩ : syracuseStep 4255105 = 3191329) B3191329
theorem B24563087 : Blo 1494067 24563087 := bstep (se 1 (by rfl) ⟨18422315, by rfl⟩ : syracuseStep 24563087 = 36844631) B36844631
theorem B1494447 : Blo 1494067 1494447 := bstep (se 1 (by rfl) ⟨1120835, by rfl⟩ : syracuseStep 1494447 = 2241671) B2241671
theorem B1494471 : Blo 1494067 1494471 := bstep (se 1 (by rfl) ⟨1120853, by rfl⟩ : syracuseStep 1494471 = 2241707) B2241707
theorem B1494491 : Blo 1494067 1494491 := bstep (se 1 (by rfl) ⟨1120868, by rfl⟩ : syracuseStep 1494491 = 2241737) B2241737
theorem B1494567 : Blo 1494067 1494567 := bstep (se 1 (by rfl) ⟨1120925, by rfl⟩ : syracuseStep 1494567 = 2241851) B2241851
theorem B2838073 : Blo 1494067 2838073 := bstep (se 2 (by rfl) ⟨1064277, by rfl⟩ : syracuseStep 2838073 = 2128555) B2128555
theorem B1494607 : Blo 1494067 1494607 := bstep (se 1 (by rfl) ⟨1120955, by rfl⟩ : syracuseStep 1494607 = 2241911) B2241911
theorem B1494623 : Blo 1494067 1494623 := bstep (se 1 (by rfl) ⟨1120967, by rfl⟩ : syracuseStep 1494623 = 2241935) B2241935
theorem B4255355 : Blo 1494067 4255355 := bstep (se 1 (by rfl) ⟨3191516, by rfl⟩ : syracuseStep 4255355 = 6383033) B6383033
theorem B1494651 : Blo 1494067 1494651 := bstep (se 1 (by rfl) ⟨1120988, by rfl⟩ : syracuseStep 1494651 = 2241977) B2241977
theorem B3591803 : Blo 1494067 3591803 := bstep (se 1 (by rfl) ⟨2693852, by rfl⟩ : syracuseStep 3591803 = 5387705) B5387705
theorem B27283067 : Blo 1494067 27283067 := bstep (se 1 (by rfl) ⟨20462300, by rfl⟩ : syracuseStep 27283067 = 40924601) B40924601
theorem B11357819 : Blo 1494067 11357819 := bstep (se 1 (by rfl) ⟨8518364, by rfl⟩ : syracuseStep 11357819 = 17036729) B17036729
theorem B1494703 : Blo 1494067 1494703 := bstep (se 1 (by rfl) ⟨1121027, by rfl⟩ : syracuseStep 1494703 = 2242055) B2242055
theorem B1494727 : Blo 1494067 1494727 := bstep (se 1 (by rfl) ⟨1121045, by rfl⟩ : syracuseStep 1494727 = 2242091) B2242091
theorem B1494747 : Blo 1494067 1494747 := bstep (se 1 (by rfl) ⟨1121060, by rfl⟩ : syracuseStep 1494747 = 2242121) B2242121
theorem B1494823 : Blo 1494067 1494823 := bstep (se 1 (by rfl) ⟨1121117, by rfl⟩ : syracuseStep 1494823 = 2242235) B2242235
theorem B3362633 : Blo 1494067 3362633 := bstep (se 2 (by rfl) ⟨1260987, by rfl⟩ : syracuseStep 3362633 = 2521975) B2521975
theorem B1494863 : Blo 1494067 1494863 := bstep (se 1 (by rfl) ⟨1121147, by rfl⟩ : syracuseStep 1494863 = 2242295) B2242295
theorem B7180127 : Blo 1494067 7180127 := bstep (se 1 (by rfl) ⟨5385095, by rfl⟩ : syracuseStep 7180127 = 10770191) B10770191
theorem B1494879 : Blo 1494067 1494879 := bstep (se 1 (by rfl) ⟨1121159, by rfl⟩ : syracuseStep 1494879 = 2242319) B2242319
theorem B2838377 : Blo 1494067 2838377 := bstep (se 2 (by rfl) ⟨1064391, by rfl⟩ : syracuseStep 2838377 = 2128783) B2128783
theorem B1494907 : Blo 1494067 1494907 := bstep (se 1 (by rfl) ⟨1121180, by rfl⟩ : syracuseStep 1494907 = 2242361) B2242361
theorem B2838415 : Blo 1494067 2838415 := bstep (se 1 (by rfl) ⟨2128811, by rfl⟩ : syracuseStep 2838415 = 4257623) B4257623
theorem B2396047 : Blo 1494067 2396047 := bstep (se 1 (by rfl) ⟨1797035, by rfl⟩ : syracuseStep 2396047 = 3594071) B3594071
theorem B1494959 : Blo 1494067 1494959 := bstep (se 1 (by rfl) ⟨1121219, by rfl⟩ : syracuseStep 1494959 = 2242439) B2242439
theorem B1494983 : Blo 1494067 1494983 := bstep (se 1 (by rfl) ⟨1121237, by rfl⟩ : syracuseStep 1494983 = 2242475) B2242475
theorem B1495003 : Blo 1494067 1495003 := bstep (se 1 (by rfl) ⟨1121252, by rfl⟩ : syracuseStep 1495003 = 2242505) B2242505
theorem B1495079 : Blo 1494067 1495079 := bstep (se 1 (by rfl) ⟨1121309, by rfl⟩ : syracuseStep 1495079 = 2242619) B2242619
theorem B5673017 : Blo 1494067 5673017 := bstep (se 2 (by rfl) ⟨2127381, by rfl⟩ : syracuseStep 5673017 = 4254763) B4254763
theorem B1495119 : Blo 1494067 1495119 := bstep (se 1 (by rfl) ⟨1121339, by rfl⟩ : syracuseStep 1495119 = 2242679) B2242679
theorem B1495135 : Blo 1494067 1495135 := bstep (se 1 (by rfl) ⟨1121351, by rfl⟩ : syracuseStep 1495135 = 2242703) B2242703
theorem B1495163 : Blo 1494067 1495163 := bstep (se 1 (by rfl) ⟨1121372, by rfl⟩ : syracuseStep 1495163 = 2242745) B2242745
theorem B7573661 : Blo 1494067 7573661 := bstep (se 3 (by rfl) ⟨1420061, by rfl⟩ : syracuseStep 7573661 = 2840123) B2840123
theorem B1495215 : Blo 1494067 1495215 := bstep (se 1 (by rfl) ⟨1121411, by rfl⟩ : syracuseStep 1495215 = 2242823) B2242823
theorem B1495239 : Blo 1494067 1495239 := bstep (se 1 (by rfl) ⟨1121429, by rfl⟩ : syracuseStep 1495239 = 2242859) B2242859
theorem B1495259 : Blo 1494067 1495259 := bstep (se 1 (by rfl) ⟨1121444, by rfl⟩ : syracuseStep 1495259 = 2242889) B2242889
theorem B1495335 : Blo 1494067 1495335 := bstep (se 1 (by rfl) ⟨1121501, by rfl⟩ : syracuseStep 1495335 = 2243003) B2243003
theorem B1495375 : Blo 1494067 1495375 := bstep (se 1 (by rfl) ⟨1121531, by rfl⟩ : syracuseStep 1495375 = 2243063) B2243063
theorem B5042519 : Blo 1494067 5042519 := bstep (se 1 (by rfl) ⟨3781889, by rfl⟩ : syracuseStep 5042519 = 7563779) B7563779
theorem B1495391 : Blo 1494067 1495391 := bstep (se 1 (by rfl) ⟨1121543, by rfl⟩ : syracuseStep 1495391 = 2243087) B2243087
theorem B1495419 : Blo 1494067 1495419 := bstep (se 1 (by rfl) ⟨1121564, by rfl⟩ : syracuseStep 1495419 = 2243129) B2243129
theorem B1495471 : Blo 1494067 1495471 := bstep (se 1 (by rfl) ⟨1121603, by rfl⟩ : syracuseStep 1495471 = 2243207) B2243207
theorem B1495495 : Blo 1494067 1495495 := bstep (se 1 (by rfl) ⟨1121621, by rfl⟩ : syracuseStep 1495495 = 2243243) B2243243
theorem B1495515 : Blo 1494067 1495515 := bstep (se 1 (by rfl) ⟨1121636, by rfl⟩ : syracuseStep 1495515 = 2243273) B2243273
theorem B26604035 : Blo 1494067 26604035 := bstep (se 1 (by rfl) ⟨19953026, by rfl⟩ : syracuseStep 26604035 = 39906053) B39906053
theorem B1495591 : Blo 1494067 1495591 := bstep (se 1 (by rfl) ⟨1121693, by rfl⟩ : syracuseStep 1495591 = 2243387) B2243387
theorem B1495631 : Blo 1494067 1495631 := bstep (se 1 (by rfl) ⟨1121723, by rfl⟩ : syracuseStep 1495631 = 2243447) B2243447
theorem B3363425 : Blo 1494067 3363425 := bstep (se 2 (by rfl) ⟨1261284, by rfl⟩ : syracuseStep 3363425 = 2522569) B2522569
theorem B1495647 : Blo 1494067 1495647 := bstep (se 1 (by rfl) ⟨1121735, by rfl⟩ : syracuseStep 1495647 = 2243471) B2243471
theorem B1495675 : Blo 1494067 1495675 := bstep (se 1 (by rfl) ⟨1121756, by rfl⟩ : syracuseStep 1495675 = 2243513) B2243513
theorem B1495727 : Blo 1494067 1495727 := bstep (se 1 (by rfl) ⟨1121795, by rfl⟩ : syracuseStep 1495727 = 2243591) B2243591
theorem B5673671 : Blo 1494067 5673671 := bstep (se 1 (by rfl) ⟨4255253, by rfl⟩ : syracuseStep 5673671 = 8510507) B8510507
theorem B1495751 : Blo 1494067 1495751 := bstep (se 1 (by rfl) ⟨1121813, by rfl⟩ : syracuseStep 1495751 = 2243627) B2243627
theorem B21541585 : Blo 1494067 21541585 := bstep (se 2 (by rfl) ⟨8078094, by rfl⟩ : syracuseStep 21541585 = 16156189) B16156189
theorem B1495771 : Blo 1494067 1495771 := bstep (se 1 (by rfl) ⟨1121828, by rfl⟩ : syracuseStep 1495771 = 2243657) B2243657
theorem B1495847 : Blo 1494067 1495847 := bstep (se 1 (by rfl) ⟨1121885, by rfl⟩ : syracuseStep 1495847 = 2243771) B2243771
theorem B1495887 : Blo 1494067 1495887 := bstep (se 1 (by rfl) ⟨1121915, by rfl⟩ : syracuseStep 1495887 = 2243831) B2243831
theorem B1495903 : Blo 1494067 1495903 := bstep (se 1 (by rfl) ⟨1121927, by rfl⟩ : syracuseStep 1495903 = 2243855) B2243855
theorem B1495931 : Blo 1494067 1495931 := bstep (se 1 (by rfl) ⟨1121948, by rfl⟩ : syracuseStep 1495931 = 2243897) B2243897
theorem B2241455 : Blo 1494067 2241455 := bstep (se 1 (by rfl) ⟨1681091, by rfl⟩ : syracuseStep 2241455 = 3362183) B3362183
theorem B1495983 : Blo 1494067 1495983 := bstep (se 1 (by rfl) ⟨1121987, by rfl⟩ : syracuseStep 1495983 = 2243975) B2243975
theorem B3363767 : Blo 1494067 3363767 := bstep (se 1 (by rfl) ⟨2522825, by rfl⟩ : syracuseStep 3363767 = 5045651) B5045651
theorem B1496007 : Blo 1494067 1496007 := bstep (se 1 (by rfl) ⟨1122005, by rfl⟩ : syracuseStep 1496007 = 2244011) B2244011
theorem B1496027 : Blo 1494067 1496027 := bstep (se 1 (by rfl) ⟨1122020, by rfl⟩ : syracuseStep 1496027 = 2244041) B2244041
theorem B2241545 : Blo 1494067 2241545 := bstep (se 2 (by rfl) ⟨840579, by rfl⟩ : syracuseStep 2241545 = 1681159) B1681159
theorem B2241575 : Blo 1494067 2241575 := bstep (se 1 (by rfl) ⟨1681181, by rfl⟩ : syracuseStep 2241575 = 3362363) B3362363
theorem B20460595 : Blo 1494067 20460595 := bstep (se 1 (by rfl) ⟨15345446, by rfl⟩ : syracuseStep 20460595 = 30690893) B30690893
theorem B2241659 : Blo 1494067 2241659 := bstep (se 1 (by rfl) ⟨1681244, by rfl⟩ : syracuseStep 2241659 = 3362489) B3362489
theorem B5387417 : Blo 1494067 5387417 := bstep (se 2 (by rfl) ⟨2020281, by rfl⟩ : syracuseStep 5387417 = 4040563) B4040563
theorem B10925227 : Blo 1494067 10925227 := bstep (se 1 (by rfl) ⟨8193920, by rfl⟩ : syracuseStep 10925227 = 16387841) B16387841
theorem B25539785 : Blo 1494067 25539785 := bstep (se 2 (by rfl) ⟨9577419, by rfl⟩ : syracuseStep 25539785 = 19154839) B19154839
theorem B2241785 : Blo 1494067 2241785 := bstep (se 2 (by rfl) ⟨840669, by rfl⟩ : syracuseStep 2241785 = 1681339) B1681339
theorem B2241887 : Blo 1494067 2241887 := bstep (se 1 (by rfl) ⟨1681415, by rfl⟩ : syracuseStep 2241887 = 3362831) B3362831
theorem B2241899 : Blo 1494067 2241899 := bstep (se 1 (by rfl) ⟨1681424, by rfl⟩ : syracuseStep 2241899 = 3362849) B3362849
theorem B4789633 : Blo 1494067 4789633 := bstep (se 2 (by rfl) ⟨1796112, by rfl⟩ : syracuseStep 4789633 = 3592225) B3592225
theorem B75732355 : Blo 1494067 75732355 := bstep (se 1 (by rfl) ⟨56799266, by rfl⟩ : syracuseStep 75732355 = 113598533) B113598533
theorem B5043599 : Blo 1494067 5043599 := bstep (se 1 (by rfl) ⟨3782699, by rfl⟩ : syracuseStep 5043599 = 7565399) B7565399
theorem B1683067 : Blo 1494067 1683067 := bstep (se 1 (by rfl) ⟨1262300, by rfl⟩ : syracuseStep 1683067 = 2524601) B2524601
theorem B32765429 : Blo 1494067 32765429 := bstep (se 5 (by rfl) ⟨1535879, by rfl⟩ : syracuseStep 32765429 = 3071759) B3071759
theorem B3782153 : Blo 1494067 3782153 := bstep (se 2 (by rfl) ⟨1418307, by rfl⟩ : syracuseStep 3782153 = 2836615) B2836615
theorem B3364361 : Blo 1494067 3364361 := bstep (se 2 (by rfl) ⟨1261635, by rfl⟩ : syracuseStep 3364361 = 2523271) B2523271
theorem B2242127 : Blo 1494067 2242127 := bstep (se 1 (by rfl) ⟨1681595, by rfl⟩ : syracuseStep 2242127 = 3363191) B3363191
theorem B5674643 : Blo 1494067 5674643 := bstep (se 1 (by rfl) ⟨4255982, by rfl⟩ : syracuseStep 5674643 = 8511965) B8511965
theorem B2242247 : Blo 1494067 2242247 := bstep (se 1 (by rfl) ⟨1681685, by rfl⟩ : syracuseStep 2242247 = 3363371) B3363371
theorem B5043923 : Blo 1494067 5043923 := bstep (se 1 (by rfl) ⟨3782942, by rfl⟩ : syracuseStep 5043923 = 7565885) B7565885
theorem B8083243 : Blo 1494067 8083243 := bstep (se 1 (by rfl) ⟨6062432, by rfl⟩ : syracuseStep 8083243 = 12124865) B12124865
theorem B3192671 : Blo 1494067 3192671 := bstep (se 1 (by rfl) ⟨2394503, by rfl⟩ : syracuseStep 3192671 = 4789007) B4789007
theorem B3364703 : Blo 1494067 3364703 := bstep (se 1 (by rfl) ⟨2523527, by rfl⟩ : syracuseStep 3364703 = 5047055) B5047055
theorem B2242409 : Blo 1494067 2242409 := bstep (se 2 (by rfl) ⟨840903, by rfl⟩ : syracuseStep 2242409 = 1681807) B1681807
theorem B2242487 : Blo 1494067 2242487 := bstep (se 1 (by rfl) ⟨1681865, by rfl⟩ : syracuseStep 2242487 = 3363731) B3363731
theorem B2242523 : Blo 1494067 2242523 := bstep (se 1 (by rfl) ⟨1681892, by rfl⟩ : syracuseStep 2242523 = 3363785) B3363785
theorem B3364883 : Blo 1494067 3364883 := bstep (se 1 (by rfl) ⟨2523662, by rfl⟩ : syracuseStep 3364883 = 5047325) B5047325
theorem B25557281 : Blo 1494067 25557281 := bstep (se 2 (by rfl) ⟨9583980, by rfl⟩ : syracuseStep 25557281 = 19167961) B19167961
theorem B3365225 : Blo 1494067 3365225 := bstep (se 2 (by rfl) ⟨1261959, by rfl⟩ : syracuseStep 3365225 = 2523919) B2523919
theorem B40925573 : Blo 1494067 40925573 := bstep (se 4 (by rfl) ⟨3836772, by rfl⟩ : syracuseStep 40925573 = 7673545) B7673545
theorem B11352473 : Blo 1494067 11352473 := bstep (se 2 (by rfl) ⟨4257177, by rfl⟩ : syracuseStep 11352473 = 8514355) B8514355
theorem B2242991 : Blo 1494067 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B2955703 : Blo 1494067 2955703 := bstep (se 1 (by rfl) ⟨2216777, by rfl⟩ : syracuseStep 2955703 = 4433555) B4433555
theorem B2243081 : Blo 1494067 2243081 := bstep (se 2 (by rfl) ⟨841155, by rfl⟩ : syracuseStep 2243081 = 1682311) B1682311
theorem B2243111 : Blo 1494067 2243111 := bstep (se 1 (by rfl) ⟨1682333, by rfl⟩ : syracuseStep 2243111 = 3364667) B3364667
theorem B4315771 : Blo 1494067 4315771 := bstep (se 1 (by rfl) ⟨3236828, by rfl⟩ : syracuseStep 4315771 = 6473657) B6473657
theorem B2243195 : Blo 1494067 2243195 := bstep (se 1 (by rfl) ⟨1682396, by rfl⟩ : syracuseStep 2243195 = 3364793) B3364793
theorem B3783307 : Blo 1494067 3783307 := bstep (se 1 (by rfl) ⟨2837480, by rfl⟩ : syracuseStep 3783307 = 5674961) B5674961
theorem B32750257 : Blo 1494067 32750257 := bstep (se 2 (by rfl) ⟨12281346, by rfl⟩ : syracuseStep 32750257 = 24562693) B24562693
theorem B6388433 : Blo 1494067 6388433 := bstep (se 2 (by rfl) ⟨2395662, by rfl⟩ : syracuseStep 6388433 = 4791325) B4791325
theorem B4373203 : Blo 1494067 4373203 := bstep (se 1 (by rfl) ⟨3279902, by rfl⟩ : syracuseStep 4373203 = 6559805) B6559805
theorem B2521847 : Blo 1494067 2521847 := bstep (se 1 (by rfl) ⟨1891385, by rfl⟩ : syracuseStep 2521847 = 3782771) B3782771
theorem B2243321 : Blo 1494067 2243321 := bstep (se 2 (by rfl) ⟨841245, by rfl⟩ : syracuseStep 2243321 = 1682491) B1682491
theorem B2243423 : Blo 1494067 2243423 := bstep (se 1 (by rfl) ⟨1682567, by rfl⟩ : syracuseStep 2243423 = 3365135) B3365135
theorem B92044133 : Blo 1494067 92044133 := bstep (se 4 (by rfl) ⟨8629137, by rfl⟩ : syracuseStep 92044133 = 17258275) B17258275
theorem B2243435 : Blo 1494067 2243435 := bstep (se 1 (by rfl) ⟨1682576, by rfl⟩ : syracuseStep 2243435 = 3365153) B3365153
theorem B5045111 : Blo 1494067 5045111 := bstep (se 1 (by rfl) ⟨3783833, by rfl⟩ : syracuseStep 5045111 = 7567667) B7567667
theorem B3029903 : Blo 1494067 3029903 := bstep (se 1 (by rfl) ⟨2272427, by rfl⟩ : syracuseStep 3029903 = 4544855) B4544855
theorem B3029935 : Blo 1494067 3029935 := bstep (se 1 (by rfl) ⟨2272451, by rfl⟩ : syracuseStep 3029935 = 4544903) B4544903
theorem B3783611 : Blo 1494067 3783611 := bstep (se 1 (by rfl) ⟨2837708, by rfl⟩ : syracuseStep 3783611 = 5675417) B5675417
theorem B3365819 : Blo 1494067 3365819 := bstep (se 1 (by rfl) ⟨2524364, by rfl⟩ : syracuseStep 3365819 = 5048729) B5048729
theorem B3365945 : Blo 1494067 3365945 := bstep (se 2 (by rfl) ⟨1262229, by rfl⟩ : syracuseStep 3365945 = 2524459) B2524459
theorem B2522191 : Blo 1494067 2522191 := bstep (se 1 (by rfl) ⟨1891643, by rfl⟩ : syracuseStep 2522191 = 3783287) B3783287
theorem B5045327 : Blo 1494067 5045327 := bstep (se 1 (by rfl) ⟨3783995, by rfl⟩ : syracuseStep 5045327 = 7567991) B7567991
theorem B2243663 : Blo 1494067 2243663 := bstep (se 1 (by rfl) ⟨1682747, by rfl⟩ : syracuseStep 2243663 = 3365495) B3365495
theorem B1891451 : Blo 1494067 1891451 := bstep (se 1 (by rfl) ⟨1418588, by rfl⟩ : syracuseStep 1891451 = 2837177) B2837177
theorem B4791467 : Blo 1494067 4791467 := bstep (se 1 (by rfl) ⟨3593600, by rfl⟩ : syracuseStep 4791467 = 7187201) B7187201
theorem B2243783 : Blo 1494067 2243783 := bstep (se 1 (by rfl) ⟨1682837, by rfl⟩ : syracuseStep 2243783 = 3365675) B3365675
theorem B3030227 : Blo 1494067 3030227 := bstep (se 1 (by rfl) ⟨2272670, by rfl⟩ : syracuseStep 3030227 = 4545341) B4545341
theorem B2522441 : Blo 1494067 2522441 := bstep (se 2 (by rfl) ⟨945915, by rfl⟩ : syracuseStep 2522441 = 1891831) B1891831
theorem B2243945 : Blo 1494067 2243945 := bstep (se 2 (by rfl) ⟨841479, by rfl⟩ : syracuseStep 2243945 = 1682959) B1682959
theorem B6389117 : Blo 1494067 6389117 := bstep (se 3 (by rfl) ⟨1197959, by rfl⟩ : syracuseStep 6389117 = 2395919) B2395919
theorem B6225295 : Blo 1494067 6225295 := bstep (se 1 (by rfl) ⟨4668971, by rfl⟩ : syracuseStep 6225295 = 9337943) B9337943
theorem B2244023 : Blo 1494067 2244023 := bstep (se 1 (by rfl) ⟨1683017, by rfl⟩ : syracuseStep 2244023 = 3366035) B3366035
theorem B5045705 : Blo 1494067 5045705 := bstep (se 2 (by rfl) ⟨1892139, by rfl⟩ : syracuseStep 5045705 = 3784279) B3784279
theorem B8510939 : Blo 1494067 8510939 := bstep (se 1 (by rfl) ⟨6383204, by rfl⟩ : syracuseStep 8510939 = 12766409) B12766409
theorem B7183835 : Blo 1494067 7183835 := bstep (se 1 (by rfl) ⟨5387876, by rfl⟩ : syracuseStep 7183835 = 10775753) B10775753
theorem B2244059 : Blo 1494067 2244059 := bstep (se 1 (by rfl) ⟨1683044, by rfl⟩ : syracuseStep 2244059 = 3366089) B3366089
theorem B23027287 : Blo 1494067 23027287 := bstep (se 1 (by rfl) ⟨17270465, by rfl⟩ : syracuseStep 23027287 = 34540931) B34540931
theorem B11501203 : Blo 1494067 11501203 := bstep (se 1 (by rfl) ⟨8625902, by rfl⟩ : syracuseStep 11501203 = 17251805) B17251805
theorem B3784391 : Blo 1494067 3784391 := bstep (se 1 (by rfl) ⟨2838293, by rfl⟩ : syracuseStep 3784391 = 5676587) B5676587
theorem B5045975 : Blo 1494067 5045975 := bstep (se 1 (by rfl) ⟨3784481, by rfl⟩ : syracuseStep 5045975 = 7568963) B7568963
theorem B2522873 : Blo 1494067 2522873 := bstep (se 2 (by rfl) ⟨946077, by rfl⟩ : syracuseStep 2522873 = 1892155) B1892155
theorem B3784441 : Blo 1494067 3784441 := bstep (se 2 (by rfl) ⟨1419165, by rfl⟩ : syracuseStep 3784441 = 2838331) B2838331
theorem B10772291 : Blo 1494067 10772291 := bstep (se 1 (by rfl) ⟨8079218, by rfl⟩ : syracuseStep 10772291 = 16158437) B16158437
theorem B2523055 : Blo 1494067 2523055 := bstep (se 1 (by rfl) ⟨1892291, by rfl⟩ : syracuseStep 2523055 = 3784583) B3784583
theorem B5046191 : Blo 1494067 5046191 := bstep (se 1 (by rfl) ⟨3784643, by rfl⟩ : syracuseStep 5046191 = 7569287) B7569287
theorem B25886735 : Blo 1494067 25886735 := bstep (se 1 (by rfl) ⟨19415051, by rfl⟩ : syracuseStep 25886735 = 38830103) B38830103
theorem B7569611 : Blo 1494067 7569611 := bstep (se 1 (by rfl) ⟨5677208, by rfl⟩ : syracuseStep 7569611 = 11354417) B11354417
theorem B17736023 : Blo 1494067 17736023 := bstep (se 1 (by rfl) ⟨13302017, by rfl⟩ : syracuseStep 17736023 = 26604035) B26604035
theorem B3031387 : Blo 1494067 3031387 := bstep (se 1 (by rfl) ⟨2273540, by rfl⟩ : syracuseStep 3031387 = 4547081) B4547081
theorem B5046785 : Blo 1494067 5046785 := bstep (se 2 (by rfl) ⟨1892544, by rfl⟩ : syracuseStep 5046785 = 3785089) B3785089
theorem B3940937 : Blo 1494067 3940937 := bstep (se 2 (by rfl) ⟨1477851, by rfl⟩ : syracuseStep 3940937 = 2955703) B2955703
theorem B12780281 : Blo 1494067 12780281 := bstep (se 2 (by rfl) ⟨4792605, by rfl⟩ : syracuseStep 12780281 = 9585211) B9585211
theorem B28722113 : Blo 1494067 28722113 := bstep (se 2 (by rfl) ⟨10770792, by rfl⟩ : syracuseStep 28722113 = 21541585) B21541585
theorem B5047271 : Blo 1494067 5047271 := bstep (se 1 (by rfl) ⟨3785453, by rfl⟩ : syracuseStep 5047271 = 7570907) B7570907
theorem B2524135 : Blo 1494067 2524135 := bstep (se 1 (by rfl) ⟨1893101, by rfl⟩ : syracuseStep 2524135 = 3786203) B3786203
theorem B7988321 : Blo 1494067 7988321 := bstep (se 2 (by rfl) ⟨2995620, by rfl⟩ : syracuseStep 7988321 = 5991241) B5991241
theorem B4039913 : Blo 1494067 4039913 := bstep (se 2 (by rfl) ⟨1514967, by rfl⟩ : syracuseStep 4039913 = 3029935) B3029935
theorem B5047595 : Blo 1494067 5047595 := bstep (se 1 (by rfl) ⟨3785696, by rfl⟩ : syracuseStep 5047595 = 7571393) B7571393
theorem B27280793 : Blo 1494067 27280793 := bstep (se 2 (by rfl) ⟨10230297, by rfl⟩ : syracuseStep 27280793 = 20460595) B20460595
theorem B1705415 : Blo 1494067 1705415 := bstep (se 1 (by rfl) ⟨1279061, by rfl⟩ : syracuseStep 1705415 = 2558123) B2558123
theorem B34538995 : Blo 1494067 34538995 := bstep (se 1 (by rfl) ⟨25904246, by rfl⟩ : syracuseStep 34538995 = 51808493) B51808493
theorem B14566969 : Blo 1494067 14566969 := bstep (se 2 (by rfl) ⟨5462613, by rfl⟩ : syracuseStep 14566969 = 10925227) B10925227
theorem B5047865 : Blo 1494067 5047865 := bstep (se 2 (by rfl) ⟨1892949, by rfl⟩ : syracuseStep 5047865 = 3785899) B3785899
theorem B3786335 : Blo 1494067 3786335 := bstep (se 1 (by rfl) ⟨2839751, by rfl⟩ : syracuseStep 3786335 = 5679503) B5679503
theorem B11347613 : Blo 1494067 11347613 := bstep (se 3 (by rfl) ⟨2127677, by rfl⟩ : syracuseStep 11347613 = 4255355) B4255355
theorem B16156361 : Blo 1494067 16156361 := bstep (se 2 (by rfl) ⟨6058635, by rfl⟩ : syracuseStep 16156361 = 12117271) B12117271
theorem B1681231 : Blo 1494067 1681231 := bstep (se 1 (by rfl) ⟨1260923, by rfl⟩ : syracuseStep 1681231 = 2521847) B2521847
theorem B100976473 : Blo 1494067 100976473 := bstep (se 2 (by rfl) ⟨37866177, by rfl⟩ : syracuseStep 100976473 = 75732355) B75732355
theorem B8300393 : Blo 1494067 8300393 := bstep (se 2 (by rfl) ⟨3112647, by rfl⟩ : syracuseStep 8300393 = 6225295) B6225295
theorem B414566423 : Blo 1494067 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B1681627 : Blo 1494067 1681627 := bstep (se 1 (by rfl) ⟨1261220, by rfl⟩ : syracuseStep 1681627 = 2522441) B2522441
theorem B2394535 : Blo 1494067 2394535 := bstep (se 1 (by rfl) ⟨1795901, by rfl⟩ : syracuseStep 2394535 = 3591803) B3591803
theorem B18188711 : Blo 1494067 18188711 := bstep (se 1 (by rfl) ⟨13641533, by rfl⟩ : syracuseStep 18188711 = 27283067) B27283067
theorem B7571879 : Blo 1494067 7571879 := bstep (se 1 (by rfl) ⟨5678909, by rfl⟩ : syracuseStep 7571879 = 11357819) B11357819
theorem B9095597 : Blo 1494067 9095597 := bstep (se 3 (by rfl) ⟨1705424, by rfl⟩ : syracuseStep 9095597 = 3410849) B3410849
theorem B1681915 : Blo 1494067 1681915 := bstep (se 1 (by rfl) ⟨1261436, by rfl⟩ : syracuseStep 1681915 = 2522873) B2522873
theorem B4786751 : Blo 1494067 4786751 := bstep (se 1 (by rfl) ⟨3590063, by rfl⟩ : syracuseStep 4786751 = 7180127) B7180127
theorem B7572041 : Blo 1494067 7572041 := bstep (se 2 (by rfl) ⟨2839515, by rfl⟩ : syracuseStep 7572041 = 5679031) B5679031
theorem B1682095 : Blo 1494067 1682095 := bstep (se 1 (by rfl) ⟨1261571, by rfl⟩ : syracuseStep 1682095 = 2523143) B2523143
theorem B5679791 : Blo 1494067 5679791 := bstep (se 1 (by rfl) ⟨4259843, by rfl⟩ : syracuseStep 5679791 = 8519687) B8519687
theorem B5049107 : Blo 1494067 5049107 := bstep (se 1 (by rfl) ⟨3786830, by rfl⟩ : syracuseStep 5049107 = 7573661) B7573661
theorem B14969731 : Blo 1494067 14969731 := bstep (se 1 (by rfl) ⟨11227298, by rfl⟩ : syracuseStep 14969731 = 22454597) B22454597
theorem B3361679 : Blo 1494067 3361679 := bstep (se 1 (by rfl) ⟨2521259, by rfl⟩ : syracuseStep 3361679 = 5042519) B5042519
theorem B1682383 : Blo 1494067 1682383 := bstep (se 1 (by rfl) ⟨1261787, by rfl⟩ : syracuseStep 1682383 = 2523575) B2523575
theorem B4254707 : Blo 1494067 4254707 := bstep (se 1 (by rfl) ⟨3191030, by rfl⟩ : syracuseStep 4254707 = 6382061) B6382061
theorem B7285747 : Blo 1494067 7285747 := bstep (se 1 (by rfl) ⟨5464310, by rfl⟩ : syracuseStep 7285747 = 10928621) B10928621
theorem B7564427 : Blo 1494067 7564427 := bstep (se 1 (by rfl) ⟨5673320, by rfl⟩ : syracuseStep 7564427 = 11346641) B11346641
theorem B1494303 : Blo 1494067 1494303 := bstep (se 1 (by rfl) ⟨1120727, by rfl⟩ : syracuseStep 1494303 = 2241455) B2241455
theorem B1494363 : Blo 1494067 1494363 := bstep (se 1 (by rfl) ⟨1120772, by rfl⟩ : syracuseStep 1494363 = 2241545) B2241545
theorem B1682779 : Blo 1494067 1682779 := bstep (se 1 (by rfl) ⟨1262084, by rfl⟩ : syracuseStep 1682779 = 2524169) B2524169
theorem B1494383 : Blo 1494067 1494383 := bstep (se 1 (by rfl) ⟨1120787, by rfl⟩ : syracuseStep 1494383 = 2241575) B2241575
theorem B1494439 : Blo 1494067 1494439 := bstep (se 1 (by rfl) ⟨1120829, by rfl⟩ : syracuseStep 1494439 = 2241659) B2241659
theorem B4255163 : Blo 1494067 4255163 := bstep (se 1 (by rfl) ⟨3191372, by rfl⟩ : syracuseStep 4255163 = 6382745) B6382745
theorem B3591611 : Blo 1494067 3591611 := bstep (se 1 (by rfl) ⟨2693708, by rfl⟩ : syracuseStep 3591611 = 5387417) B5387417
theorem B1682887 : Blo 1494067 1682887 := bstep (se 1 (by rfl) ⟨1262165, by rfl⟩ : syracuseStep 1682887 = 2524331) B2524331
theorem B10235335 : Blo 1494067 10235335 := bstep (se 1 (by rfl) ⟨7676501, by rfl⟩ : syracuseStep 10235335 = 15353003) B15353003
theorem B17026523 : Blo 1494067 17026523 := bstep (se 1 (by rfl) ⟨12769892, by rfl⟩ : syracuseStep 17026523 = 25539785) B25539785
theorem B1494523 : Blo 1494067 1494523 := bstep (se 1 (by rfl) ⟨1120892, by rfl⟩ : syracuseStep 1494523 = 2241785) B2241785
theorem B1494591 : Blo 1494067 1494591 := bstep (se 1 (by rfl) ⟨1120943, by rfl⟩ : syracuseStep 1494591 = 2241887) B2241887
theorem B43667009 : Blo 1494067 43667009 := bstep (se 2 (by rfl) ⟨16375128, by rfl⟩ : syracuseStep 43667009 = 32750257) B32750257
theorem B1494599 : Blo 1494067 1494599 := bstep (se 1 (by rfl) ⟨1120949, by rfl⟩ : syracuseStep 1494599 = 2241899) B2241899
theorem B3362399 : Blo 1494067 3362399 := bstep (se 1 (by rfl) ⟨2521799, by rfl⟩ : syracuseStep 3362399 = 5043599) B5043599
theorem B62221933 : Blo 1494067 62221933 := bstep (se 3 (by rfl) ⟨11666612, by rfl⟩ : syracuseStep 62221933 = 23333225) B23333225
theorem B1494751 : Blo 1494067 1494751 := bstep (se 1 (by rfl) ⟨1121063, by rfl⟩ : syracuseStep 1494751 = 2242127) B2242127
theorem B5386031 : Blo 1494067 5386031 := bstep (se 1 (by rfl) ⟨4039523, by rfl⟩ : syracuseStep 5386031 = 8079047) B8079047
theorem B1494831 : Blo 1494067 1494831 := bstep (se 1 (by rfl) ⟨1121123, by rfl⟩ : syracuseStep 1494831 = 2242247) B2242247
theorem B3362615 : Blo 1494067 3362615 := bstep (se 1 (by rfl) ⟨2521961, by rfl⟩ : syracuseStep 3362615 = 5043923) B5043923
theorem B1494939 : Blo 1494067 1494939 := bstep (se 1 (by rfl) ⟨1121204, by rfl⟩ : syracuseStep 1494939 = 2242409) B2242409
theorem B1494991 : Blo 1494067 1494991 := bstep (se 1 (by rfl) ⟨1121243, by rfl⟩ : syracuseStep 1494991 = 2242487) B2242487
theorem B1495015 : Blo 1494067 1495015 := bstep (se 1 (by rfl) ⟨1121261, by rfl⟩ : syracuseStep 1495015 = 2242523) B2242523
theorem B24260633 : Blo 1494067 24260633 := bstep (se 2 (by rfl) ⟨9097737, by rfl⟩ : syracuseStep 24260633 = 18195475) B18195475
theorem B3362921 : Blo 1494067 3362921 := bstep (se 2 (by rfl) ⟨1261095, by rfl⟩ : syracuseStep 3362921 = 2522191) B2522191
theorem B27283715 : Blo 1494067 27283715 := bstep (se 1 (by rfl) ⟨20462786, by rfl⟩ : syracuseStep 27283715 = 40925573) B40925573
theorem B1495327 : Blo 1494067 1495327 := bstep (se 1 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 1495327 = 2242991) B2242991
theorem B1495387 : Blo 1494067 1495387 := bstep (se 1 (by rfl) ⟨1121540, by rfl⟩ : syracuseStep 1495387 = 2243081) B2243081
theorem B1495407 : Blo 1494067 1495407 := bstep (se 1 (by rfl) ⟨1121555, by rfl⟩ : syracuseStep 1495407 = 2243111) B2243111
theorem B1495463 : Blo 1494067 1495463 := bstep (se 1 (by rfl) ⟨1121597, by rfl⟩ : syracuseStep 1495463 = 2243195) B2243195
theorem B1495547 : Blo 1494067 1495547 := bstep (se 1 (by rfl) ⟨1121660, by rfl⟩ : syracuseStep 1495547 = 2243321) B2243321
theorem B5673473 : Blo 1494067 5673473 := bstep (se 2 (by rfl) ⟨2127552, by rfl⟩ : syracuseStep 5673473 = 4255105) B4255105
theorem B6386177 : Blo 1494067 6386177 := bstep (se 2 (by rfl) ⟨2394816, by rfl⟩ : syracuseStep 6386177 = 4789633) B4789633
theorem B1495615 : Blo 1494067 1495615 := bstep (se 1 (by rfl) ⟨1121711, by rfl⟩ : syracuseStep 1495615 = 2243423) B2243423
theorem B61362755 : Blo 1494067 61362755 := bstep (se 1 (by rfl) ⟨46022066, by rfl⟩ : syracuseStep 61362755 = 92044133) B92044133
theorem B1495623 : Blo 1494067 1495623 := bstep (se 1 (by rfl) ⟨1121717, by rfl⟩ : syracuseStep 1495623 = 2243435) B2243435
theorem B3363407 : Blo 1494067 3363407 := bstep (se 1 (by rfl) ⟨2522555, by rfl⟩ : syracuseStep 3363407 = 5045111) B5045111
theorem B2019935 : Blo 1494067 2019935 := bstep (se 1 (by rfl) ⟨1514951, by rfl⟩ : syracuseStep 2019935 = 3029903) B3029903
theorem B2241131 : Blo 1494067 2241131 := bstep (se 1 (by rfl) ⟨1680848, by rfl⟩ : syracuseStep 2241131 = 3361697) B3361697
theorem B7566047 : Blo 1494067 7566047 := bstep (se 1 (by rfl) ⟨5674535, by rfl⟩ : syracuseStep 7566047 = 11349071) B11349071
theorem B3363551 : Blo 1494067 3363551 := bstep (se 1 (by rfl) ⟨2522663, by rfl⟩ : syracuseStep 3363551 = 5045327) B5045327
theorem B1495775 : Blo 1494067 1495775 := bstep (se 1 (by rfl) ⟨1121831, by rfl⟩ : syracuseStep 1495775 = 2243663) B2243663
theorem B1495855 : Blo 1494067 1495855 := bstep (se 1 (by rfl) ⟨1121891, by rfl⟩ : syracuseStep 1495855 = 2243783) B2243783
theorem B2020151 : Blo 1494067 2020151 := bstep (se 1 (by rfl) ⟨1515113, by rfl⟩ : syracuseStep 2020151 = 3030227) B3030227
theorem B2241359 : Blo 1494067 2241359 := bstep (se 1 (by rfl) ⟨1681019, by rfl⟩ : syracuseStep 2241359 = 3362039) B3362039
theorem B28726109 : Blo 1494067 28726109 := bstep (se 3 (by rfl) ⟨5386145, by rfl⟩ : syracuseStep 28726109 = 10772291) B10772291
theorem B1495963 : Blo 1494067 1495963 := bstep (se 1 (by rfl) ⟨1121972, by rfl⟩ : syracuseStep 1495963 = 2243945) B2243945
theorem B1496015 : Blo 1494067 1496015 := bstep (se 1 (by rfl) ⟨1122011, by rfl⟩ : syracuseStep 1496015 = 2244023) B2244023
theorem B3363803 : Blo 1494067 3363803 := bstep (se 1 (by rfl) ⟨2522852, by rfl⟩ : syracuseStep 3363803 = 5045705) B5045705
theorem B5673959 : Blo 1494067 5673959 := bstep (se 1 (by rfl) ⟨4255469, by rfl⟩ : syracuseStep 5673959 = 8510939) B8510939
theorem B4789223 : Blo 1494067 4789223 := bstep (se 1 (by rfl) ⟨3591917, by rfl⟩ : syracuseStep 4789223 = 7183835) B7183835
theorem B1496039 : Blo 1494067 1496039 := bstep (se 1 (by rfl) ⟨1122029, by rfl⟩ : syracuseStep 1496039 = 2244059) B2244059
theorem B10777657 : Blo 1494067 10777657 := bstep (se 2 (by rfl) ⟨4041621, by rfl⟩ : syracuseStep 10777657 = 8083243) B8083243
theorem B3363983 : Blo 1494067 3363983 := bstep (se 1 (by rfl) ⟨2522987, by rfl⟩ : syracuseStep 3363983 = 5045975) B5045975
theorem B2241755 : Blo 1494067 2241755 := bstep (se 1 (by rfl) ⟨1681316, by rfl⟩ : syracuseStep 2241755 = 3362633) B3362633
theorem B3364073 : Blo 1494067 3364073 := bstep (se 2 (by rfl) ⟨1261527, by rfl⟩ : syracuseStep 3364073 = 2523055) B2523055
theorem B3364127 : Blo 1494067 3364127 := bstep (se 1 (by rfl) ⟨2523095, by rfl⟩ : syracuseStep 3364127 = 5046191) B5046191
theorem B3782011 : Blo 1494067 3782011 := bstep (se 1 (by rfl) ⟨2836508, by rfl⟩ : syracuseStep 3782011 = 5673017) B5673017
theorem B2241929 : Blo 1494067 2241929 := bstep (se 2 (by rfl) ⟨840723, by rfl⟩ : syracuseStep 2241929 = 1681447) B1681447
theorem B5043869 : Blo 1494067 5043869 := bstep (se 3 (by rfl) ⟨945725, by rfl⟩ : syracuseStep 5043869 = 1891451) B1891451
theorem B2242283 : Blo 1494067 2242283 := bstep (se 1 (by rfl) ⟨1681712, by rfl⟩ : syracuseStep 2242283 = 3363425) B3363425
theorem B25548533 : Blo 1494067 25548533 := bstep (se 5 (by rfl) ⟨1197587, by rfl⟩ : syracuseStep 25548533 = 2395175) B2395175
theorem B3364649 : Blo 1494067 3364649 := bstep (se 2 (by rfl) ⟨1261743, by rfl⟩ : syracuseStep 3364649 = 2523487) B2523487
theorem B3782447 : Blo 1494067 3782447 := bstep (se 1 (by rfl) ⟨2836835, by rfl⟩ : syracuseStep 3782447 = 5673671) B5673671
theorem B2021275 : Blo 1494067 2021275 := bstep (se 1 (by rfl) ⟨1515956, by rfl⟩ : syracuseStep 2021275 = 3031913) B3031913
theorem B2242511 : Blo 1494067 2242511 := bstep (se 1 (by rfl) ⟨1681883, by rfl⟩ : syracuseStep 2242511 = 3363767) B3363767
theorem B23017445 : Blo 1494067 23017445 := bstep (se 4 (by rfl) ⟨2157885, by rfl⟩ : syracuseStep 23017445 = 4315771) B4315771
theorem B5675143 : Blo 1494067 5675143 := bstep (se 1 (by rfl) ⟨4256357, by rfl⟩ : syracuseStep 5675143 = 8512715) B8512715
theorem B5044409 : Blo 1494067 5044409 := bstep (se 2 (by rfl) ⟨1891653, by rfl⟩ : syracuseStep 5044409 = 3783307) B3783307
theorem B5830937 : Blo 1494067 5830937 := bstep (se 2 (by rfl) ⟨2186601, by rfl⟩ : syracuseStep 5830937 = 4373203) B4373203
theorem B2521435 : Blo 1494067 2521435 := bstep (se 1 (by rfl) ⟨1891076, by rfl⟩ : syracuseStep 2521435 = 3782153) B3782153
theorem B2242907 : Blo 1494067 2242907 := bstep (se 1 (by rfl) ⟨1682180, by rfl⟩ : syracuseStep 2242907 = 3364361) B3364361
theorem B3783095 : Blo 1494067 3783095 := bstep (se 1 (by rfl) ⟨2837321, by rfl⟩ : syracuseStep 3783095 = 5674643) B5674643
theorem B5675447 : Blo 1494067 5675447 := bstep (se 1 (by rfl) ⟨4256585, by rfl⟩ : syracuseStep 5675447 = 8513171) B8513171
theorem B2128447 : Blo 1494067 2128447 := bstep (se 1 (by rfl) ⟨1596335, by rfl⟩ : syracuseStep 2128447 = 3192671) B3192671
theorem B2243135 : Blo 1494067 2243135 := bstep (se 1 (by rfl) ⟨1682351, by rfl⟩ : syracuseStep 2243135 = 3364703) B3364703
theorem B4790863 : Blo 1494067 4790863 := bstep (se 1 (by rfl) ⟨3593147, by rfl⟩ : syracuseStep 4790863 = 7186295) B7186295
theorem B3193465 : Blo 1494067 3193465 := bstep (se 2 (by rfl) ⟨1197549, by rfl⟩ : syracuseStep 3193465 = 2395099) B2395099
theorem B87374477 : Blo 1494067 87374477 := bstep (se 3 (by rfl) ⟨16382714, by rfl⟩ : syracuseStep 87374477 = 32765429) B32765429
theorem B6822575 : Blo 1494067 6822575 := bstep (se 1 (by rfl) ⟨5116931, by rfl⟩ : syracuseStep 6822575 = 10233863) B10233863
theorem B2243255 : Blo 1494067 2243255 := bstep (se 1 (by rfl) ⟨1682441, by rfl⟩ : syracuseStep 2243255 = 3364883) B3364883
theorem B1891127 : Blo 1494067 1891127 := bstep (se 1 (by rfl) ⟨1418345, by rfl⟩ : syracuseStep 1891127 = 2836691) B2836691
theorem B3365711 : Blo 1494067 3365711 := bstep (se 1 (by rfl) ⟨2524283, by rfl⟩ : syracuseStep 3365711 = 5048567) B5048567
theorem B17038187 : Blo 1494067 17038187 := bstep (se 1 (by rfl) ⟨12778640, by rfl⟩ : syracuseStep 17038187 = 25557281) B25557281
theorem B5462939 : Blo 1494067 5462939 := bstep (se 1 (by rfl) ⟨4097204, by rfl⟩ : syracuseStep 5462939 = 8194409) B8194409
theorem B2243483 : Blo 1494067 2243483 := bstep (se 1 (by rfl) ⟨1682612, by rfl⟩ : syracuseStep 2243483 = 3365225) B3365225
theorem B7568315 : Blo 1494067 7568315 := bstep (se 1 (by rfl) ⟨5676236, by rfl⟩ : syracuseStep 7568315 = 11352473) B11352473
theorem B1891279 : Blo 1494067 1891279 := bstep (se 1 (by rfl) ⟨1418459, by rfl⟩ : syracuseStep 1891279 = 2836919) B2836919
theorem B3365927 : Blo 1494067 3365927 := bstep (se 1 (by rfl) ⟨2524445, by rfl⟩ : syracuseStep 3365927 = 5048891) B5048891
theorem B4258955 : Blo 1494067 4258955 := bstep (se 1 (by rfl) ⟨3194216, by rfl⟩ : syracuseStep 4258955 = 6388433) B6388433
theorem B3366107 : Blo 1494067 3366107 := bstep (se 1 (by rfl) ⟨2524580, by rfl⟩ : syracuseStep 3366107 = 5049161) B5049161
theorem B2522407 : Blo 1494067 2522407 := bstep (se 1 (by rfl) ⟨1891805, by rfl⟩ : syracuseStep 2522407 = 3783611) B3783611
theorem B2243879 : Blo 1494067 2243879 := bstep (se 1 (by rfl) ⟨1682909, by rfl⟩ : syracuseStep 2243879 = 3365819) B3365819
theorem B2243963 : Blo 1494067 2243963 := bstep (se 1 (by rfl) ⟨1682972, by rfl⟩ : syracuseStep 2243963 = 3365945) B3365945
theorem B3784097 : Blo 1494067 3784097 := bstep (se 2 (by rfl) ⟨1419036, by rfl⟩ : syracuseStep 3784097 = 2838073) B2838073
theorem B3194311 : Blo 1494067 3194311 := bstep (se 1 (by rfl) ⟨2395733, by rfl⟩ : syracuseStep 3194311 = 4791467) B4791467
theorem B30703049 : Blo 1494067 30703049 := bstep (se 2 (by rfl) ⟨11513643, by rfl⟩ : syracuseStep 30703049 = 23027287) B23027287
theorem B2244089 : Blo 1494067 2244089 := bstep (se 2 (by rfl) ⟨841533, by rfl⟩ : syracuseStep 2244089 = 1683067) B1683067
theorem B15334937 : Blo 1494067 15334937 := bstep (se 2 (by rfl) ⟨5750601, by rfl⟩ : syracuseStep 15334937 = 11501203) B11501203
theorem B4259411 : Blo 1494067 4259411 := bstep (se 1 (by rfl) ⟨3194558, by rfl⟩ : syracuseStep 4259411 = 6389117) B6389117
theorem B16375391 : Blo 1494067 16375391 := bstep (se 1 (by rfl) ⟨12281543, by rfl⟩ : syracuseStep 16375391 = 24563087) B24563087
theorem B5045921 : Blo 1494067 5045921 := bstep (se 2 (by rfl) ⟨1892220, by rfl⟩ : syracuseStep 5045921 = 3784441) B3784441
theorem B5463713 : Blo 1494067 5463713 := bstep (se 2 (by rfl) ⟨2048892, by rfl⟩ : syracuseStep 5463713 = 4097785) B4097785
theorem B2522927 : Blo 1494067 2522927 := bstep (se 1 (by rfl) ⟨1892195, by rfl⟩ : syracuseStep 2522927 = 3784391) B3784391
theorem B3784553 : Blo 1494067 3784553 := bstep (se 2 (by rfl) ⟨1419207, by rfl⟩ : syracuseStep 3784553 = 2838415) B2838415
theorem B3194729 : Blo 1494067 3194729 := bstep (se 2 (by rfl) ⟨1198023, by rfl⟩ : syracuseStep 3194729 = 2396047) B2396047
theorem B1892251 : Blo 1494067 1892251 := bstep (se 1 (by rfl) ⟨1419188, by rfl⟩ : syracuseStep 1892251 = 2838377) B2838377
theorem B5046407 : Blo 1494067 5046407 := bstep (se 1 (by rfl) ⟨3784805, by rfl⟩ : syracuseStep 5046407 = 7569611) B7569611
theorem B8520187 : Blo 1494067 8520187 := bstep (se 1 (by rfl) ⟨6390140, by rfl⟩ : syracuseStep 8520187 = 12780281) B12780281
theorem B10773101 : Blo 1494067 10773101 := bstep (se 3 (by rfl) ⟨2019956, by rfl⟩ : syracuseStep 10773101 = 4039913) B4039913
theorem B5325547 : Blo 1494067 5325547 := bstep (se 1 (by rfl) ⟨3994160, by rfl⟩ : syracuseStep 5325547 = 7988321) B7988321
theorem B18187195 : Blo 1494067 18187195 := bstep (se 1 (by rfl) ⟨13640396, by rfl⟩ : syracuseStep 18187195 = 27280793) B27280793
theorem B2524223 : Blo 1494067 2524223 := bstep (se 1 (by rfl) ⟨1893167, by rfl⟩ : syracuseStep 2524223 = 3786335) B3786335
theorem B17032355 : Blo 1494067 17032355 := bstep (se 1 (by rfl) ⟨12774266, by rfl⟩ : syracuseStep 17032355 = 25548533) B25548533
theorem B4547773 : Blo 1494067 4547773 := bstep (se 3 (by rfl) ⟨852707, by rfl⟩ : syracuseStep 4547773 = 1705415) B1705415
theorem B15344963 : Blo 1494067 15344963 := bstep (se 1 (by rfl) ⟨11508722, by rfl⟩ : syracuseStep 15344963 = 23017445) B23017445
theorem B14370209 : Blo 1494067 14370209 := bstep (se 2 (by rfl) ⟨5388828, by rfl⟩ : syracuseStep 14370209 = 10777657) B10777657
theorem B12125807 : Blo 1494067 12125807 := bstep (se 1 (by rfl) ⟨9094355, by rfl⟩ : syracuseStep 12125807 = 18188711) B18188711
theorem B5047919 : Blo 1494067 5047919 := bstep (se 1 (by rfl) ⟨3785939, by rfl⟩ : syracuseStep 5047919 = 7571879) B7571879
theorem B6063731 : Blo 1494067 6063731 := bstep (se 1 (by rfl) ⟨4547798, by rfl⟩ : syracuseStep 6063731 = 9095597) B9095597
theorem B5048027 : Blo 1494067 5048027 := bstep (se 1 (by rfl) ⟨3786020, by rfl⟩ : syracuseStep 5048027 = 7572041) B7572041
theorem B4548383 : Blo 1494067 4548383 := bstep (se 1 (by rfl) ⟨3411287, by rfl⟩ : syracuseStep 4548383 = 6822575) B6822575
theorem B3786527 : Blo 1494067 3786527 := bstep (se 1 (by rfl) ⟨2839895, by rfl⟩ : syracuseStep 3786527 = 5679791) B5679791
theorem B2836471 : Blo 1494067 2836471 := bstep (se 1 (by rfl) ⟨2127353, by rfl⟩ : syracuseStep 2836471 = 4254707) B4254707
theorem B82962577 : Blo 1494067 82962577 := bstep (se 2 (by rfl) ⟨31110966, by rfl⟩ : syracuseStep 82962577 = 62221933) B62221933
theorem B2836775 : Blo 1494067 2836775 := bstep (se 1 (by rfl) ⟨2127581, by rfl⟩ : syracuseStep 2836775 = 4255163) B4255163
theorem B2394407 : Blo 1494067 2394407 := bstep (se 1 (by rfl) ⟨1795805, by rfl⟩ : syracuseStep 2394407 = 3591611) B3591611
theorem B3590687 : Blo 1494067 3590687 := bstep (se 1 (by rfl) ⟨2693015, by rfl⟩ : syracuseStep 3590687 = 5386031) B5386031
theorem B1681951 : Blo 1494067 1681951 := bstep (se 1 (by rfl) ⟨1261463, by rfl⟩ : syracuseStep 1681951 = 2522927) B2522927
theorem B16173755 : Blo 1494067 16173755 := bstep (se 1 (by rfl) ⟨12130316, by rfl⟩ : syracuseStep 16173755 = 24260633) B24260633
theorem B18189143 : Blo 1494067 18189143 := bstep (se 1 (by rfl) ⟨13641857, by rfl⟩ : syracuseStep 18189143 = 27283715) B27283715
theorem B11824015 : Blo 1494067 11824015 := bstep (se 1 (by rfl) ⟨8868011, by rfl⟩ : syracuseStep 11824015 = 17736023) B17736023
theorem B1494087 : Blo 1494067 1494087 := bstep (se 1 (by rfl) ⟨1120565, by rfl⟩ : syracuseStep 1494087 = 2241131) B2241131
theorem B3361913 : Blo 1494067 3361913 := bstep (se 2 (by rfl) ⟨1260717, by rfl⟩ : syracuseStep 3361913 = 2521435) B2521435
theorem B1494239 : Blo 1494067 1494239 := bstep (se 1 (by rfl) ⟨1120679, by rfl⟩ : syracuseStep 1494239 = 2241359) B2241359
theorem B19148075 : Blo 1494067 19148075 := bstep (se 1 (by rfl) ⟨14361056, by rfl⟩ : syracuseStep 19148075 = 28722113) B28722113
theorem B2837929 : Blo 1494067 2837929 := bstep (se 2 (by rfl) ⟨1064223, by rfl⟩ : syracuseStep 2837929 = 2128447) B2128447
theorem B42036661 : Blo 1494067 42036661 := bstep (se 5 (by rfl) ⟨1970468, by rfl⟩ : syracuseStep 42036661 = 3940937) B3940937
theorem B1494503 : Blo 1494067 1494503 := bstep (se 1 (by rfl) ⟨1120877, by rfl⟩ : syracuseStep 1494503 = 2241755) B2241755
theorem B1494619 : Blo 1494067 1494619 := bstep (se 1 (by rfl) ⟨1120964, by rfl⟩ : syracuseStep 1494619 = 2241929) B2241929
theorem B7565075 : Blo 1494067 7565075 := bstep (se 1 (by rfl) ⟨5673806, by rfl⟩ : syracuseStep 7565075 = 11347613) B11347613
theorem B3362579 : Blo 1494067 3362579 := bstep (se 1 (by rfl) ⟨2521934, by rfl⟩ : syracuseStep 3362579 = 5043869) B5043869
theorem B1494855 : Blo 1494067 1494855 := bstep (se 1 (by rfl) ⟨1121141, by rfl⟩ : syracuseStep 1494855 = 2242283) B2242283
theorem B19959641 : Blo 1494067 19959641 := bstep (se 2 (by rfl) ⟨7484865, by rfl⟩ : syracuseStep 19959641 = 14969731) B14969731
theorem B5533595 : Blo 1494067 5533595 := bstep (se 1 (by rfl) ⟨4150196, by rfl⟩ : syracuseStep 5533595 = 8300393) B8300393
theorem B1495007 : Blo 1494067 1495007 := bstep (se 1 (by rfl) ⟨1121255, by rfl⟩ : syracuseStep 1495007 = 2242511) B2242511
theorem B276377615 : Blo 1494067 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B3362939 : Blo 1494067 3362939 := bstep (se 1 (by rfl) ⟨2522204, by rfl⟩ : syracuseStep 3362939 = 5044409) B5044409
theorem B3887291 : Blo 1494067 3887291 := bstep (se 1 (by rfl) ⟨2915468, by rfl⟩ : syracuseStep 3887291 = 5830937) B5830937
theorem B1495271 : Blo 1494067 1495271 := bstep (se 1 (by rfl) ⟨1121453, by rfl⟩ : syracuseStep 1495271 = 2242907) B2242907
theorem B5386493 : Blo 1494067 5386493 := bstep (se 3 (by rfl) ⟨1009967, by rfl⟩ : syracuseStep 5386493 = 2019935) B2019935
theorem B3191167 : Blo 1494067 3191167 := bstep (se 1 (by rfl) ⟨2393375, by rfl⟩ : syracuseStep 3191167 = 4786751) B4786751
theorem B1495423 : Blo 1494067 1495423 := bstep (se 1 (by rfl) ⟨1121567, by rfl⟩ : syracuseStep 1495423 = 2243135) B2243135
theorem B3363209 : Blo 1494067 3363209 := bstep (se 2 (by rfl) ⟨1261203, by rfl⟩ : syracuseStep 3363209 = 2522407) B2522407
theorem B14569901 : Blo 1494067 14569901 := bstep (se 3 (by rfl) ⟨2731856, by rfl⟩ : syracuseStep 14569901 = 5463713) B5463713
theorem B58249651 : Blo 1494067 58249651 := bstep (se 1 (by rfl) ⟨43687238, by rfl⟩ : syracuseStep 58249651 = 87374477) B87374477
theorem B1495503 : Blo 1494067 1495503 := bstep (se 1 (by rfl) ⟨1121627, by rfl⟩ : syracuseStep 1495503 = 2243255) B2243255
theorem B16167397 : Blo 1494067 16167397 := bstep (se 4 (by rfl) ⟨1515693, by rfl⟩ : syracuseStep 16167397 = 3031387) B3031387
theorem B5042681 : Blo 1494067 5042681 := bstep (se 2 (by rfl) ⟨1891005, by rfl⟩ : syracuseStep 5042681 = 3782011) B3782011
theorem B11358791 : Blo 1494067 11358791 := bstep (se 1 (by rfl) ⟨8519093, by rfl⟩ : syracuseStep 11358791 = 17038187) B17038187
theorem B2241119 : Blo 1494067 2241119 := bstep (se 1 (by rfl) ⟨1680839, by rfl⟩ : syracuseStep 2241119 = 3361679) B3361679
theorem B3641959 : Blo 1494067 3641959 := bstep (se 1 (by rfl) ⟨2731469, by rfl⟩ : syracuseStep 3641959 = 5462939) B5462939
theorem B1495655 : Blo 1494067 1495655 := bstep (se 1 (by rfl) ⟨1121741, by rfl⟩ : syracuseStep 1495655 = 2243483) B2243483
theorem B46051993 : Blo 1494067 46051993 := bstep (se 2 (by rfl) ⟨17269497, by rfl⟩ : syracuseStep 46051993 = 34538995) B34538995
theorem B5042951 : Blo 1494067 5042951 := bstep (se 1 (by rfl) ⟨3782213, by rfl⟩ : syracuseStep 5042951 = 7564427) B7564427
theorem B2839303 : Blo 1494067 2839303 := bstep (se 1 (by rfl) ⟨2129477, by rfl⟩ : syracuseStep 2839303 = 4258955) B4258955
theorem B5043005 : Blo 1494067 5043005 := bstep (se 3 (by rfl) ⟨945563, by rfl⟩ : syracuseStep 5043005 = 1891127) B1891127
theorem B5387069 : Blo 1494067 5387069 := bstep (se 3 (by rfl) ⟨1010075, by rfl⟩ : syracuseStep 5387069 = 2020151) B2020151
theorem B1495919 : Blo 1494067 1495919 := bstep (se 1 (by rfl) ⟨1121939, by rfl⟩ : syracuseStep 1495919 = 2243879) B2243879
theorem B1495975 : Blo 1494067 1495975 := bstep (se 1 (by rfl) ⟨1121981, by rfl⟩ : syracuseStep 1495975 = 2243963) B2243963
theorem B20468699 : Blo 1494067 20468699 := bstep (se 1 (by rfl) ⟨15351524, by rfl⟩ : syracuseStep 20468699 = 30703049) B30703049
theorem B11351015 : Blo 1494067 11351015 := bstep (se 1 (by rfl) ⟨8513261, by rfl⟩ : syracuseStep 11351015 = 17026523) B17026523
theorem B1496059 : Blo 1494067 1496059 := bstep (se 1 (by rfl) ⟨1122044, by rfl⟩ : syracuseStep 1496059 = 2244089) B2244089
theorem B29111339 : Blo 1494067 29111339 := bstep (se 1 (by rfl) ⟨21833504, by rfl⟩ : syracuseStep 29111339 = 43667009) B43667009
theorem B2839607 : Blo 1494067 2839607 := bstep (se 1 (by rfl) ⟨2129705, by rfl⟩ : syracuseStep 2839607 = 4259411) B4259411
theorem B10916927 : Blo 1494067 10916927 := bstep (se 1 (by rfl) ⟨8187695, by rfl⟩ : syracuseStep 10916927 = 16375391) B16375391
theorem B2241599 : Blo 1494067 2241599 := bstep (se 1 (by rfl) ⟨1681199, by rfl⟩ : syracuseStep 2241599 = 3362399) B3362399
theorem B2241641 : Blo 1494067 2241641 := bstep (se 2 (by rfl) ⟨840615, by rfl⟩ : syracuseStep 2241641 = 1681231) B1681231
theorem B3363947 : Blo 1494067 3363947 := bstep (se 1 (by rfl) ⟨2522960, by rfl⟩ : syracuseStep 3363947 = 5045921) B5045921
theorem B2241743 : Blo 1494067 2241743 := bstep (se 1 (by rfl) ⟨1681307, by rfl⟩ : syracuseStep 2241743 = 3362615) B3362615
theorem B17257823 : Blo 1494067 17257823 := bstep (se 1 (by rfl) ⟨12943367, by rfl⟩ : syracuseStep 17257823 = 25886735) B25886735
theorem B2241947 : Blo 1494067 2241947 := bstep (se 1 (by rfl) ⟨1681460, by rfl⟩ : syracuseStep 2241947 = 3362921) B3362921
theorem B7566857 : Blo 1494067 7566857 := bstep (se 2 (by rfl) ⟨2837571, by rfl⟩ : syracuseStep 7566857 = 5675143) B5675143
theorem B2242169 : Blo 1494067 2242169 := bstep (se 2 (by rfl) ⟨840813, by rfl⟩ : syracuseStep 2242169 = 1681627) B1681627
theorem B3782315 : Blo 1494067 3782315 := bstep (se 1 (by rfl) ⟨2836736, by rfl⟩ : syracuseStep 3782315 = 5673473) B5673473
theorem B4257451 : Blo 1494067 4257451 := bstep (se 1 (by rfl) ⟨3193088, by rfl⟩ : syracuseStep 4257451 = 6386177) B6386177
theorem B3364523 : Blo 1494067 3364523 := bstep (se 1 (by rfl) ⟨2523392, by rfl⟩ : syracuseStep 3364523 = 5046785) B5046785
theorem B40908503 : Blo 1494067 40908503 := bstep (se 1 (by rfl) ⟨30681377, by rfl⟩ : syracuseStep 40908503 = 61362755) B61362755
theorem B2242271 : Blo 1494067 2242271 := bstep (se 1 (by rfl) ⟨1681703, by rfl⟩ : syracuseStep 2242271 = 3363407) B3363407
theorem B5044031 : Blo 1494067 5044031 := bstep (se 1 (by rfl) ⟨3783023, by rfl⟩ : syracuseStep 5044031 = 7566047) B7566047
theorem B2242367 : Blo 1494067 2242367 := bstep (se 1 (by rfl) ⟨1681775, by rfl⟩ : syracuseStep 2242367 = 3363551) B3363551
theorem B3192713 : Blo 1494067 3192713 := bstep (se 2 (by rfl) ⟨1197267, by rfl⟩ : syracuseStep 3192713 = 2394535) B2394535
theorem B19150739 : Blo 1494067 19150739 := bstep (se 1 (by rfl) ⟨14363054, by rfl⟩ : syracuseStep 19150739 = 28726109) B28726109
theorem B2242535 : Blo 1494067 2242535 := bstep (se 1 (by rfl) ⟨1681901, by rfl⟩ : syracuseStep 2242535 = 3363803) B3363803
theorem B3782639 : Blo 1494067 3782639 := bstep (se 1 (by rfl) ⟨2836979, by rfl⟩ : syracuseStep 3782639 = 5673959) B5673959
theorem B3192815 : Blo 1494067 3192815 := bstep (se 1 (by rfl) ⟨2394611, by rfl⟩ : syracuseStep 3192815 = 4789223) B4789223
theorem B3364847 : Blo 1494067 3364847 := bstep (se 1 (by rfl) ⟨2523635, by rfl⟩ : syracuseStep 3364847 = 5047271) B5047271
theorem B2242553 : Blo 1494067 2242553 := bstep (se 2 (by rfl) ⟨840957, by rfl⟩ : syracuseStep 2242553 = 1681915) B1681915
theorem B2242655 : Blo 1494067 2242655 := bstep (se 1 (by rfl) ⟨1681991, by rfl⟩ : syracuseStep 2242655 = 3363983) B3363983
theorem B6387817 : Blo 1494067 6387817 := bstep (se 2 (by rfl) ⟨2395431, by rfl⟩ : syracuseStep 6387817 = 4790863) B4790863
theorem B2242715 : Blo 1494067 2242715 := bstep (se 1 (by rfl) ⟨1682036, by rfl⟩ : syracuseStep 2242715 = 3364073) B3364073
theorem B4257953 : Blo 1494067 4257953 := bstep (se 2 (by rfl) ⟨1596732, by rfl⟩ : syracuseStep 4257953 = 3193465) B3193465
theorem B2242751 : Blo 1494067 2242751 := bstep (se 1 (by rfl) ⟨1682063, by rfl⟩ : syracuseStep 2242751 = 3364127) B3364127
theorem B3365063 : Blo 1494067 3365063 := bstep (se 1 (by rfl) ⟨2523797, by rfl⟩ : syracuseStep 3365063 = 5047595) B5047595
theorem B2242793 : Blo 1494067 2242793 := bstep (se 2 (by rfl) ⟨841047, by rfl⟩ : syracuseStep 2242793 = 1682095) B1682095
theorem B3365243 : Blo 1494067 3365243 := bstep (se 1 (by rfl) ⟨2523932, by rfl⟩ : syracuseStep 3365243 = 5047865) B5047865
theorem B10770907 : Blo 1494067 10770907 := bstep (se 1 (by rfl) ⟨8078180, by rfl⟩ : syracuseStep 10770907 = 16156361) B16156361
theorem B2243099 : Blo 1494067 2243099 := bstep (se 1 (by rfl) ⟨1682324, by rfl⟩ : syracuseStep 2243099 = 3364649) B3364649
theorem B2521631 : Blo 1494067 2521631 := bstep (se 1 (by rfl) ⟨1891223, by rfl⟩ : syracuseStep 2521631 = 3782447) B3782447
theorem B2521705 : Blo 1494067 2521705 := bstep (se 2 (by rfl) ⟨945639, by rfl⟩ : syracuseStep 2521705 = 1891279) B1891279
theorem B2243177 : Blo 1494067 2243177 := bstep (se 2 (by rfl) ⟨841191, by rfl⟩ : syracuseStep 2243177 = 1682383) B1682383
theorem B3365513 : Blo 1494067 3365513 := bstep (se 2 (by rfl) ⟨1262067, by rfl⟩ : syracuseStep 3365513 = 2524135) B2524135
theorem B9714329 : Blo 1494067 9714329 := bstep (se 2 (by rfl) ⟨3642873, by rfl⟩ : syracuseStep 9714329 = 7285747) B7285747
theorem B2522063 : Blo 1494067 2522063 := bstep (se 1 (by rfl) ⟨1891547, by rfl⟩ : syracuseStep 2522063 = 3783095) B3783095
theorem B3783631 : Blo 1494067 3783631 := bstep (se 1 (by rfl) ⟨2837723, by rfl⟩ : syracuseStep 3783631 = 5675447) B5675447
theorem B2243705 : Blo 1494067 2243705 := bstep (se 2 (by rfl) ⟨841389, by rfl⟩ : syracuseStep 2243705 = 1682779) B1682779
theorem B3366071 : Blo 1494067 3366071 := bstep (se 1 (by rfl) ⟨2524553, by rfl⟩ : syracuseStep 3366071 = 5049107) B5049107
theorem B2243807 : Blo 1494067 2243807 := bstep (se 1 (by rfl) ⟨1682855, by rfl⟩ : syracuseStep 2243807 = 3365711) B3365711
theorem B4259081 : Blo 1494067 4259081 := bstep (se 2 (by rfl) ⟨1597155, by rfl⟩ : syracuseStep 4259081 = 3194311) B3194311
theorem B2243849 : Blo 1494067 2243849 := bstep (se 2 (by rfl) ⟨841443, by rfl⟩ : syracuseStep 2243849 = 1682887) B1682887
theorem B13647113 : Blo 1494067 13647113 := bstep (se 2 (by rfl) ⟨5117667, by rfl⟩ : syracuseStep 13647113 = 10235335) B10235335
theorem B5045543 : Blo 1494067 5045543 := bstep (se 1 (by rfl) ⟨3784157, by rfl⟩ : syracuseStep 5045543 = 7568315) B7568315
theorem B2243951 : Blo 1494067 2243951 := bstep (se 1 (by rfl) ⟨1682963, by rfl⟩ : syracuseStep 2243951 = 3365927) B3365927
theorem B19422625 : Blo 1494067 19422625 := bstep (se 2 (by rfl) ⟨7283484, by rfl⟩ : syracuseStep 19422625 = 14566969) B14566969
theorem B10780133 : Blo 1494067 10780133 := bstep (se 4 (by rfl) ⟨1010637, by rfl⟩ : syracuseStep 10780133 = 2021275) B2021275
theorem B2244071 : Blo 1494067 2244071 := bstep (se 1 (by rfl) ⟨1683053, by rfl⟩ : syracuseStep 2244071 = 3366107) B3366107
theorem B2522731 : Blo 1494067 2522731 := bstep (se 1 (by rfl) ⟨1892048, by rfl⟩ : syracuseStep 2522731 = 3784097) B3784097
theorem B10223291 : Blo 1494067 10223291 := bstep (se 1 (by rfl) ⟨7667468, by rfl⟩ : syracuseStep 10223291 = 15334937) B15334937
theorem B134635297 : Blo 1494067 134635297 := bstep (se 2 (by rfl) ⟨50488236, by rfl⟩ : syracuseStep 134635297 = 100976473) B100976473
theorem B2523001 : Blo 1494067 2523001 := bstep (se 2 (by rfl) ⟨946125, by rfl⟩ : syracuseStep 2523001 = 1892251) B1892251
theorem B2523035 : Blo 1494067 2523035 := bstep (se 1 (by rfl) ⟨1892276, by rfl⟩ : syracuseStep 2523035 = 3784553) B3784553
theorem B2129819 : Blo 1494067 2129819 := bstep (se 1 (by rfl) ⟨1597364, by rfl⟩ : syracuseStep 2129819 = 3194729) B3194729
theorem B110616769 : Blo 1494067 110616769 := bstep (se 2 (by rfl) ⟨41481288, by rfl⟩ : syracuseStep 110616769 = 82962577) B82962577
theorem B14361209 : Blo 1494067 14361209 := bstep (se 2 (by rfl) ⟨5385453, by rfl⟩ : syracuseStep 14361209 = 10770907) B10770907
theorem B19407559 : Blo 1494067 19407559 := bstep (se 1 (by rfl) ⟨14555669, by rfl⟩ : syracuseStep 19407559 = 29111339) B29111339
theorem B1893071 : Blo 1494067 1893071 := bstep (se 1 (by rfl) ⟨1419803, by rfl⟩ : syracuseStep 1893071 = 2839607) B2839607
theorem B11354903 : Blo 1494067 11354903 := bstep (se 1 (by rfl) ⟨8516177, by rfl⟩ : syracuseStep 11354903 = 17032355) B17032355
theorem B3785737 : Blo 1494067 3785737 := bstep (se 2 (by rfl) ⟨1419651, by rfl⟩ : syracuseStep 3785737 = 2839303) B2839303
theorem B27272335 : Blo 1494067 27272335 := bstep (se 1 (by rfl) ⟨20454251, by rfl⟩ : syracuseStep 27272335 = 40908503) B40908503
theorem B3032255 : Blo 1494067 3032255 := bstep (se 1 (by rfl) ⟨2274191, by rfl⟩ : syracuseStep 3032255 = 4548383) B4548383
theorem B2524351 : Blo 1494067 2524351 := bstep (se 1 (by rfl) ⟨1893263, by rfl⟩ : syracuseStep 2524351 = 3786527) B3786527
theorem B24249593 : Blo 1494067 24249593 := bstep (se 2 (by rfl) ⟨9093597, by rfl⟩ : syracuseStep 24249593 = 18187195) B18187195
theorem B28747021 : Blo 1494067 28747021 := bstep (se 3 (by rfl) ⟨5390066, by rfl⟩ : syracuseStep 28747021 = 10780133) B10780133
theorem B6063697 : Blo 1494067 6063697 := bstep (se 2 (by rfl) ⟨2273886, by rfl⟩ : syracuseStep 6063697 = 4547773) B4547773
theorem B1681087 : Blo 1494067 1681087 := bstep (se 1 (by rfl) ⟨1260815, by rfl⟩ : syracuseStep 1681087 = 2521631) B2521631
theorem B10782503 : Blo 1494067 10782503 := bstep (se 1 (by rfl) ⟨8086877, by rfl⟩ : syracuseStep 10782503 = 16173755) B16173755
theorem B25896833 : Blo 1494067 25896833 := bstep (se 2 (by rfl) ⟨9711312, by rfl⟩ : syracuseStep 25896833 = 19422625) B19422625
theorem B12126095 : Blo 1494067 12126095 := bstep (se 1 (by rfl) ⟨9094571, by rfl⟩ : syracuseStep 12126095 = 18189143) B18189143
theorem B1681375 : Blo 1494067 1681375 := bstep (se 1 (by rfl) ⟨1261031, by rfl⟩ : syracuseStep 1681375 = 2522063) B2522063
theorem B12765383 : Blo 1494067 12765383 := bstep (se 1 (by rfl) ⟨9574037, by rfl⟩ : syracuseStep 12765383 = 19148075) B19148075
theorem B179513729 : Blo 1494067 179513729 := bstep (se 2 (by rfl) ⟨67317648, by rfl⟩ : syracuseStep 179513729 = 134635297) B134635297
theorem B5679517 : Blo 1494067 5679517 := bstep (se 3 (by rfl) ⟨1064909, by rfl⟩ : syracuseStep 5679517 = 2129819) B2129819
theorem B13306427 : Blo 1494067 13306427 := bstep (se 1 (by rfl) ⟨9979820, by rfl⟩ : syracuseStep 13306427 = 19959641) B19959641
theorem B3689063 : Blo 1494067 3689063 := bstep (se 1 (by rfl) ⟨2766797, by rfl⟩ : syracuseStep 3689063 = 5533595) B5533595
theorem B1682023 : Blo 1494067 1682023 := bstep (se 1 (by rfl) ⟨1261517, by rfl⟩ : syracuseStep 1682023 = 2523035) B2523035
theorem B8514173 : Blo 1494067 8514173 := bstep (se 3 (by rfl) ⟨1596407, by rfl⟩ : syracuseStep 8514173 = 3192815) B3192815
theorem B2591527 : Blo 1494067 2591527 := bstep (se 1 (by rfl) ⟨1943645, by rfl⟩ : syracuseStep 2591527 = 3887291) B3887291
theorem B3590995 : Blo 1494067 3590995 := bstep (se 1 (by rfl) ⟨2693246, by rfl⟩ : syracuseStep 3590995 = 5386493) B5386493
theorem B3361787 : Blo 1494067 3361787 := bstep (se 1 (by rfl) ⟨2521340, by rfl⟩ : syracuseStep 3361787 = 5042681) B5042681
theorem B7572527 : Blo 1494067 7572527 := bstep (se 1 (by rfl) ⟨5679395, by rfl⟩ : syracuseStep 7572527 = 11358791) B11358791
theorem B1494079 : Blo 1494067 1494079 := bstep (se 1 (by rfl) ⟨1120559, by rfl⟩ : syracuseStep 1494079 = 2241119) B2241119
theorem B4254889 : Blo 1494067 4254889 := bstep (se 2 (by rfl) ⟨1595583, by rfl⟩ : syracuseStep 4254889 = 3191167) B3191167
theorem B3361967 : Blo 1494067 3361967 := bstep (se 1 (by rfl) ⟨2521475, by rfl⟩ : syracuseStep 3361967 = 5042951) B5042951
theorem B3362003 : Blo 1494067 3362003 := bstep (se 1 (by rfl) ⟨2521502, by rfl⟩ : syracuseStep 3362003 = 5043005) B5043005
theorem B3591379 : Blo 1494067 3591379 := bstep (se 1 (by rfl) ⟨2693534, by rfl⟩ : syracuseStep 3591379 = 5387069) B5387069
theorem B21556529 : Blo 1494067 21556529 := bstep (se 2 (by rfl) ⟨8083698, by rfl⟩ : syracuseStep 21556529 = 16167397) B16167397
theorem B7277951 : Blo 1494067 7277951 := bstep (se 1 (by rfl) ⟨5458463, by rfl⟩ : syracuseStep 7277951 = 10916927) B10916927
theorem B1494399 : Blo 1494067 1494399 := bstep (se 1 (by rfl) ⟨1120799, by rfl⟩ : syracuseStep 1494399 = 2241599) B2241599
theorem B1682815 : Blo 1494067 1682815 := bstep (se 1 (by rfl) ⟨1262111, by rfl⟩ : syracuseStep 1682815 = 2524223) B2524223
theorem B1494427 : Blo 1494067 1494427 := bstep (se 1 (by rfl) ⟨1120820, by rfl⟩ : syracuseStep 1494427 = 2241641) B2241641
theorem B1494495 : Blo 1494067 1494495 := bstep (se 1 (by rfl) ⟨1120871, by rfl⟩ : syracuseStep 1494495 = 2241743) B2241743
theorem B3362273 : Blo 1494067 3362273 := bstep (se 2 (by rfl) ⟨1260852, by rfl⟩ : syracuseStep 3362273 = 2521705) B2521705
theorem B61402657 : Blo 1494067 61402657 := bstep (se 2 (by rfl) ⟨23025996, by rfl⟩ : syracuseStep 61402657 = 46051993) B46051993
theorem B11505215 : Blo 1494067 11505215 := bstep (se 1 (by rfl) ⟨8628911, by rfl⟩ : syracuseStep 11505215 = 17257823) B17257823
theorem B1494631 : Blo 1494067 1494631 := bstep (se 1 (by rfl) ⟨1120973, by rfl⟩ : syracuseStep 1494631 = 2241947) B2241947
theorem B9580139 : Blo 1494067 9580139 := bstep (se 1 (by rfl) ⟨7185104, by rfl⟩ : syracuseStep 9580139 = 14370209) B14370209
theorem B4042487 : Blo 1494067 4042487 := bstep (se 1 (by rfl) ⟨3031865, by rfl⟩ : syracuseStep 4042487 = 6063731) B6063731
theorem B1494779 : Blo 1494067 1494779 := bstep (se 1 (by rfl) ⟨1121084, by rfl⟩ : syracuseStep 1494779 = 2242169) B2242169
theorem B1494847 : Blo 1494067 1494847 := bstep (se 1 (by rfl) ⟨1121135, by rfl⟩ : syracuseStep 1494847 = 2242271) B2242271
theorem B15765353 : Blo 1494067 15765353 := bstep (se 2 (by rfl) ⟨5912007, by rfl⟩ : syracuseStep 15765353 = 11824015) B11824015
theorem B3362687 : Blo 1494067 3362687 := bstep (se 1 (by rfl) ⟨2522015, by rfl⟩ : syracuseStep 3362687 = 5044031) B5044031
theorem B1494911 : Blo 1494067 1494911 := bstep (se 1 (by rfl) ⟨1121183, by rfl⟩ : syracuseStep 1494911 = 2242367) B2242367
theorem B12767159 : Blo 1494067 12767159 := bstep (se 1 (by rfl) ⟨9575369, by rfl⟩ : syracuseStep 12767159 = 19150739) B19150739
theorem B1495023 : Blo 1494067 1495023 := bstep (se 1 (by rfl) ⟨1121267, by rfl⟩ : syracuseStep 1495023 = 2242535) B2242535
theorem B1495035 : Blo 1494067 1495035 := bstep (se 1 (by rfl) ⟨1121276, by rfl⟩ : syracuseStep 1495035 = 2242553) B2242553
theorem B1495103 : Blo 1494067 1495103 := bstep (se 1 (by rfl) ⟨1121327, by rfl⟩ : syracuseStep 1495103 = 2242655) B2242655
theorem B1495143 : Blo 1494067 1495143 := bstep (se 1 (by rfl) ⟨1121357, by rfl⟩ : syracuseStep 1495143 = 2242715) B2242715
theorem B2838635 : Blo 1494067 2838635 := bstep (se 1 (by rfl) ⟨2128976, by rfl⟩ : syracuseStep 2838635 = 4257953) B4257953
theorem B1495167 : Blo 1494067 1495167 := bstep (se 1 (by rfl) ⟨1121375, by rfl⟩ : syracuseStep 1495167 = 2242751) B2242751
theorem B1495195 : Blo 1494067 1495195 := bstep (se 1 (by rfl) ⟨1121396, by rfl⟩ : syracuseStep 1495195 = 2242793) B2242793
theorem B1495399 : Blo 1494067 1495399 := bstep (se 1 (by rfl) ⟨1121549, by rfl⟩ : syracuseStep 1495399 = 2243099) B2243099
theorem B1495451 : Blo 1494067 1495451 := bstep (se 1 (by rfl) ⟨1121588, by rfl⟩ : syracuseStep 1495451 = 2243177) B2243177
theorem B6476219 : Blo 1494067 6476219 := bstep (se 1 (by rfl) ⟨4857164, by rfl⟩ : syracuseStep 6476219 = 9714329) B9714329
theorem B2241275 : Blo 1494067 2241275 := bstep (se 1 (by rfl) ⟨1680956, by rfl⟩ : syracuseStep 2241275 = 3361913) B3361913
theorem B1495803 : Blo 1494067 1495803 := bstep (se 1 (by rfl) ⟨1121852, by rfl⟩ : syracuseStep 1495803 = 2243705) B2243705
theorem B3363641 : Blo 1494067 3363641 := bstep (se 2 (by rfl) ⟨1261365, by rfl⟩ : syracuseStep 3363641 = 2522731) B2522731
theorem B1495871 : Blo 1494067 1495871 := bstep (se 1 (by rfl) ⟨1121903, by rfl⟩ : syracuseStep 1495871 = 2243807) B2243807
theorem B2839387 : Blo 1494067 2839387 := bstep (se 1 (by rfl) ⟨2129540, by rfl⟩ : syracuseStep 2839387 = 4259081) B4259081
theorem B1495899 : Blo 1494067 1495899 := bstep (se 1 (by rfl) ⟨1121924, by rfl⟩ : syracuseStep 1495899 = 2243849) B2243849
theorem B9098075 : Blo 1494067 9098075 := bstep (se 1 (by rfl) ⟨6823556, by rfl⟩ : syracuseStep 9098075 = 13647113) B13647113
theorem B3363695 : Blo 1494067 3363695 := bstep (se 1 (by rfl) ⟨2522771, by rfl⟩ : syracuseStep 3363695 = 5045543) B5045543
theorem B1495967 : Blo 1494067 1495967 := bstep (se 1 (by rfl) ⟨1121975, by rfl⟩ : syracuseStep 1495967 = 2243951) B2243951
theorem B1496047 : Blo 1494067 1496047 := bstep (se 1 (by rfl) ⟨1122035, by rfl⟩ : syracuseStep 1496047 = 2244071) B2244071
theorem B3364001 : Blo 1494067 3364001 := bstep (se 2 (by rfl) ⟨1261500, by rfl⟩ : syracuseStep 3364001 = 2523001) B2523001
theorem B5043383 : Blo 1494067 5043383 := bstep (se 1 (by rfl) ⟨3782537, by rfl⟩ : syracuseStep 5043383 = 7565075) B7565075
theorem B2241719 : Blo 1494067 2241719 := bstep (se 1 (by rfl) ⟨1681289, by rfl⟩ : syracuseStep 2241719 = 3362579) B3362579
theorem B3781961 : Blo 1494067 3781961 := bstep (se 2 (by rfl) ⟨1418235, by rfl⟩ : syracuseStep 3781961 = 2836471) B2836471
theorem B184251743 : Blo 1494067 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B2241959 : Blo 1494067 2241959 := bstep (se 1 (by rfl) ⟨1681469, by rfl⟩ : syracuseStep 2241959 = 3362939) B3362939
theorem B3364271 : Blo 1494067 3364271 := bstep (se 1 (by rfl) ⟨2523203, by rfl⟩ : syracuseStep 3364271 = 5046407) B5046407
theorem B8517089 : Blo 1494067 8517089 := bstep (se 2 (by rfl) ⟨3193908, by rfl⟩ : syracuseStep 8517089 = 6387817) B6387817
theorem B2242139 : Blo 1494067 2242139 := bstep (se 1 (by rfl) ⟨1681604, by rfl⟩ : syracuseStep 2242139 = 3363209) B3363209
theorem B9713267 : Blo 1494067 9713267 := bstep (se 1 (by rfl) ⟨7284950, by rfl⟩ : syracuseStep 9713267 = 14569901) B14569901
theorem B7182067 : Blo 1494067 7182067 := bstep (se 1 (by rfl) ⟨5386550, by rfl⟩ : syracuseStep 7182067 = 10773101) B10773101
theorem B77666201 : Blo 1494067 77666201 := bstep (se 2 (by rfl) ⟨29124825, by rfl⟩ : syracuseStep 77666201 = 58249651) B58249651
theorem B13645799 : Blo 1494067 13645799 := bstep (se 1 (by rfl) ⟨10234349, by rfl⟩ : syracuseStep 13645799 = 20468699) B20468699
theorem B7567343 : Blo 1494067 7567343 := bstep (se 1 (by rfl) ⟨5675507, by rfl⟩ : syracuseStep 7567343 = 11351015) B11351015
theorem B11360249 : Blo 1494067 11360249 := bstep (se 2 (by rfl) ⟨4260093, by rfl⟩ : syracuseStep 11360249 = 8520187) B8520187
theorem B2242601 : Blo 1494067 2242601 := bstep (se 2 (by rfl) ⟨840975, by rfl⟩ : syracuseStep 2242601 = 1681951) B1681951
theorem B2242631 : Blo 1494067 2242631 := bstep (se 1 (by rfl) ⟨1681973, by rfl⟩ : syracuseStep 2242631 = 3363947) B3363947
theorem B4855945 : Blo 1494067 4855945 := bstep (se 2 (by rfl) ⟨1820979, by rfl⟩ : syracuseStep 4855945 = 3641959) B3641959
theorem B10229975 : Blo 1494067 10229975 := bstep (se 1 (by rfl) ⟨7672481, by rfl⟩ : syracuseStep 10229975 = 15344963) B15344963
theorem B7100729 : Blo 1494067 7100729 := bstep (se 2 (by rfl) ⟨2662773, by rfl⟩ : syracuseStep 7100729 = 5325547) B5325547
theorem B5044571 : Blo 1494067 5044571 := bstep (se 1 (by rfl) ⟨3783428, by rfl⟩ : syracuseStep 5044571 = 7566857) B7566857
theorem B8083871 : Blo 1494067 8083871 := bstep (se 1 (by rfl) ⟨6062903, by rfl⟩ : syracuseStep 8083871 = 12125807) B12125807
theorem B3365279 : Blo 1494067 3365279 := bstep (se 1 (by rfl) ⟨2523959, by rfl⟩ : syracuseStep 3365279 = 5047919) B5047919
theorem B2521543 : Blo 1494067 2521543 := bstep (se 1 (by rfl) ⟨1891157, by rfl⟩ : syracuseStep 2521543 = 3782315) B3782315
theorem B2243015 : Blo 1494067 2243015 := bstep (se 1 (by rfl) ⟨1682261, by rfl⟩ : syracuseStep 2243015 = 3364523) B3364523
theorem B3365351 : Blo 1494067 3365351 := bstep (se 1 (by rfl) ⟨2524013, by rfl⟩ : syracuseStep 3365351 = 5048027) B5048027
theorem B2128475 : Blo 1494067 2128475 := bstep (se 1 (by rfl) ⟨1596356, by rfl⟩ : syracuseStep 2128475 = 3192713) B3192713
theorem B5044841 : Blo 1494067 5044841 := bstep (se 2 (by rfl) ⟨1891815, by rfl⟩ : syracuseStep 5044841 = 3783631) B3783631
theorem B2521759 : Blo 1494067 2521759 := bstep (se 1 (by rfl) ⟨1891319, by rfl⟩ : syracuseStep 2521759 = 3782639) B3782639
theorem B2243231 : Blo 1494067 2243231 := bstep (se 1 (by rfl) ⟨1682423, by rfl⟩ : syracuseStep 2243231 = 3364847) B3364847
theorem B9575165 : Blo 1494067 9575165 := bstep (se 3 (by rfl) ⟨1795343, by rfl⟩ : syracuseStep 9575165 = 3590687) B3590687
theorem B2243375 : Blo 1494067 2243375 := bstep (se 1 (by rfl) ⟨1682531, by rfl⟩ : syracuseStep 2243375 = 3365063) B3365063
theorem B1891183 : Blo 1494067 1891183 := bstep (se 1 (by rfl) ⟨1418387, by rfl⟩ : syracuseStep 1891183 = 2836775) B2836775
theorem B1596271 : Blo 1494067 1596271 := bstep (se 1 (by rfl) ⟨1197203, by rfl⟩ : syracuseStep 1596271 = 2394407) B2394407
theorem B2243495 : Blo 1494067 2243495 := bstep (se 1 (by rfl) ⟨1682621, by rfl⟩ : syracuseStep 2243495 = 3365243) B3365243
theorem B2243675 : Blo 1494067 2243675 := bstep (se 1 (by rfl) ⟨1682756, by rfl⟩ : syracuseStep 2243675 = 3365513) B3365513
theorem B27262109 : Blo 1494067 27262109 := bstep (se 3 (by rfl) ⟨5111645, by rfl⟩ : syracuseStep 27262109 = 10223291) B10223291
theorem B3783905 : Blo 1494067 3783905 := bstep (se 2 (by rfl) ⟨1418964, by rfl⟩ : syracuseStep 3783905 = 2837929) B2837929
theorem B56048881 : Blo 1494067 56048881 := bstep (se 2 (by rfl) ⟨21018330, by rfl⟩ : syracuseStep 56048881 = 42036661) B42036661
theorem B2244047 : Blo 1494067 2244047 := bstep (se 1 (by rfl) ⟨1683035, by rfl⟩ : syracuseStep 2244047 = 3366071) B3366071
theorem B5676601 : Blo 1494067 5676601 := bstep (se 2 (by rfl) ⟨2128725, by rfl⟩ : syracuseStep 5676601 = 4257451) B4257451
theorem B1892423 : Blo 1494067 1892423 := bstep (se 1 (by rfl) ⟨1419317, by rfl⟩ : syracuseStep 1892423 = 2838635) B2838635
theorem B147489025 : Blo 1494067 147489025 := bstep (se 2 (by rfl) ⟨55308384, by rfl⟩ : syracuseStep 147489025 = 110616769) B110616769
theorem B4317479 : Blo 1494067 4317479 := bstep (se 1 (by rfl) ⟨3238109, by rfl⟩ : syracuseStep 4317479 = 6476219) B6476219
theorem B8086013 : Blo 1494067 8086013 := bstep (se 3 (by rfl) ⟨1516127, by rfl⟩ : syracuseStep 8086013 = 3032255) B3032255
theorem B7569935 : Blo 1494067 7569935 := bstep (se 1 (by rfl) ⟨5677451, by rfl⟩ : syracuseStep 7569935 = 11354903) B11354903
theorem B5678059 : Blo 1494067 5678059 := bstep (se 1 (by rfl) ⟨4258544, by rfl⟩ : syracuseStep 5678059 = 8517089) B8517089
theorem B3785849 : Blo 1494067 3785849 := bstep (se 2 (by rfl) ⟨1419693, by rfl⟩ : syracuseStep 3785849 = 2839387) B2839387
theorem B5047649 : Blo 1494067 5047649 := bstep (se 2 (by rfl) ⟨1892868, by rfl⟩ : syracuseStep 5047649 = 3785737) B3785737
theorem B2459375 : Blo 1494067 2459375 := bstep (se 1 (by rfl) ⟨1844531, by rfl⟩ : syracuseStep 2459375 = 3689063) B3689063
theorem B6383443 : Blo 1494067 6383443 := bstep (se 1 (by rfl) ⟨4787582, by rfl⟩ : syracuseStep 6383443 = 9575165) B9575165
theorem B5048189 : Blo 1494067 5048189 := bstep (se 3 (by rfl) ⟨946535, by rfl⟩ : syracuseStep 5048189 = 1893071) B1893071
theorem B5048351 : Blo 1494067 5048351 := bstep (se 1 (by rfl) ⟨3786263, by rfl⟩ : syracuseStep 5048351 = 7572527) B7572527
theorem B14371019 : Blo 1494067 14371019 := bstep (se 1 (by rfl) ⟨10778264, by rfl⟩ : syracuseStep 14371019 = 21556529) B21556529
theorem B4851967 : Blo 1494067 4851967 := bstep (se 1 (by rfl) ⟨3638975, by rfl⟩ : syracuseStep 4851967 = 7277951) B7277951
theorem B7670143 : Blo 1494067 7670143 := bstep (se 1 (by rfl) ⟨5752607, by rfl⟩ : syracuseStep 7670143 = 11505215) B11505215
theorem B6474593 : Blo 1494067 6474593 := bstep (se 2 (by rfl) ⟨2427972, by rfl⟩ : syracuseStep 6474593 = 4855945) B4855945
theorem B72698957 : Blo 1494067 72698957 := bstep (se 3 (by rfl) ⟨13631054, by rfl⟩ : syracuseStep 72698957 = 27262109) B27262109
theorem B1494183 : Blo 1494067 1494183 := bstep (se 1 (by rfl) ⟨1120637, by rfl⟩ : syracuseStep 1494183 = 2241275) B2241275
theorem B7572689 : Blo 1494067 7572689 := bstep (se 2 (by rfl) ⟨2839758, by rfl⟩ : syracuseStep 7572689 = 5679517) B5679517
theorem B6065383 : Blo 1494067 6065383 := bstep (se 1 (by rfl) ⟨4549037, by rfl⟩ : syracuseStep 6065383 = 9098075) B9098075
theorem B3362057 : Blo 1494067 3362057 := bstep (se 2 (by rfl) ⟨1260771, by rfl⟩ : syracuseStep 3362057 = 2521543) B2521543
theorem B3362255 : Blo 1494067 3362255 := bstep (se 1 (by rfl) ⟨2521691, by rfl⟩ : syracuseStep 3362255 = 5043383) B5043383
theorem B1494479 : Blo 1494067 1494479 := bstep (se 1 (by rfl) ⟨1120859, by rfl⟩ : syracuseStep 1494479 = 2241719) B2241719
theorem B16166395 : Blo 1494067 16166395 := bstep (se 1 (by rfl) ⟨12124796, by rfl⟩ : syracuseStep 16166395 = 24249593) B24249593
theorem B3362345 : Blo 1494067 3362345 := bstep (se 2 (by rfl) ⟨1260879, by rfl⟩ : syracuseStep 3362345 = 2521759) B2521759
theorem B122834495 : Blo 1494067 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B1494639 : Blo 1494067 1494639 := bstep (se 1 (by rfl) ⟨1120979, by rfl⟩ : syracuseStep 1494639 = 2241959) B2241959
theorem B1494759 : Blo 1494067 1494759 := bstep (se 1 (by rfl) ⟨1121069, by rfl⟩ : syracuseStep 1494759 = 2242139) B2242139
theorem B6475511 : Blo 1494067 6475511 := bstep (se 1 (by rfl) ⟨4856633, by rfl⟩ : syracuseStep 6475511 = 9713267) B9713267
theorem B4787993 : Blo 1494067 4787993 := bstep (se 2 (by rfl) ⟨1795497, by rfl⟩ : syracuseStep 4787993 = 3590995) B3590995
theorem B7188335 : Blo 1494067 7188335 := bstep (se 1 (by rfl) ⟨5391251, by rfl⟩ : syracuseStep 7188335 = 10782503) B10782503
theorem B17264555 : Blo 1494067 17264555 := bstep (se 1 (by rfl) ⟨12948416, by rfl⟩ : syracuseStep 17264555 = 25896833) B25896833
theorem B51777467 : Blo 1494067 51777467 := bstep (se 1 (by rfl) ⟨38833100, by rfl⟩ : syracuseStep 51777467 = 77666201) B77666201
theorem B9097199 : Blo 1494067 9097199 := bstep (se 1 (by rfl) ⟨6822899, by rfl⟩ : syracuseStep 9097199 = 13645799) B13645799
theorem B7573499 : Blo 1494067 7573499 := bstep (se 1 (by rfl) ⟨5680124, by rfl⟩ : syracuseStep 7573499 = 11360249) B11360249
theorem B1495067 : Blo 1494067 1495067 := bstep (se 1 (by rfl) ⟨1121300, by rfl⟩ : syracuseStep 1495067 = 2242601) B2242601
theorem B1495087 : Blo 1494067 1495087 := bstep (se 1 (by rfl) ⟨1121315, by rfl⟩ : syracuseStep 1495087 = 2242631) B2242631
theorem B6819983 : Blo 1494067 6819983 := bstep (se 1 (by rfl) ⟨5114987, by rfl⟩ : syracuseStep 6819983 = 10229975) B10229975
theorem B5673185 : Blo 1494067 5673185 := bstep (se 2 (by rfl) ⟨2127444, by rfl⟩ : syracuseStep 5673185 = 4254889) B4254889
theorem B3363047 : Blo 1494067 3363047 := bstep (se 1 (by rfl) ⟨2522285, by rfl⟩ : syracuseStep 3363047 = 5044571) B5044571
theorem B4788505 : Blo 1494067 4788505 := bstep (se 2 (by rfl) ⟨1795689, by rfl⟩ : syracuseStep 4788505 = 3591379) B3591379
theorem B1495343 : Blo 1494067 1495343 := bstep (se 1 (by rfl) ⟨1121507, by rfl⟩ : syracuseStep 1495343 = 2243015) B2243015
theorem B74731841 : Blo 1494067 74731841 := bstep (se 2 (by rfl) ⟨28024440, by rfl⟩ : syracuseStep 74731841 = 56048881) B56048881
theorem B3363227 : Blo 1494067 3363227 := bstep (se 1 (by rfl) ⟨2522420, by rfl⟩ : syracuseStep 3363227 = 5044841) B5044841
theorem B1495487 : Blo 1494067 1495487 := bstep (se 1 (by rfl) ⟨1121615, by rfl⟩ : syracuseStep 1495487 = 2243231) B2243231
theorem B1495583 : Blo 1494067 1495583 := bstep (se 1 (by rfl) ⟨1121687, by rfl⟩ : syracuseStep 1495583 = 2243375) B2243375
theorem B1495663 : Blo 1494067 1495663 := bstep (se 1 (by rfl) ⟨1121747, by rfl⟩ : syracuseStep 1495663 = 2243495) B2243495
theorem B2241191 : Blo 1494067 2241191 := bstep (se 1 (by rfl) ⟨1680893, by rfl⟩ : syracuseStep 2241191 = 3361787) B3361787
theorem B1495783 : Blo 1494067 1495783 := bstep (se 1 (by rfl) ⟨1121837, by rfl⟩ : syracuseStep 1495783 = 2243675) B2243675
theorem B2241311 : Blo 1494067 2241311 := bstep (se 1 (by rfl) ⟨1680983, by rfl⟩ : syracuseStep 2241311 = 3361967) B3361967
theorem B2241335 : Blo 1494067 2241335 := bstep (se 1 (by rfl) ⟨1681001, by rfl⟩ : syracuseStep 2241335 = 3362003) B3362003
theorem B2241449 : Blo 1494067 2241449 := bstep (se 2 (by rfl) ⟨840543, by rfl⟩ : syracuseStep 2241449 = 1681087) B1681087
theorem B1496031 : Blo 1494067 1496031 := bstep (se 1 (by rfl) ⟨1122023, by rfl⟩ : syracuseStep 1496031 = 2244047) B2244047
theorem B2241515 : Blo 1494067 2241515 := bstep (se 1 (by rfl) ⟨1681136, by rfl⟩ : syracuseStep 2241515 = 3362273) B3362273
theorem B6386759 : Blo 1494067 6386759 := bstep (se 1 (by rfl) ⟨4790069, by rfl⟩ : syracuseStep 6386759 = 9580139) B9580139
theorem B2241791 : Blo 1494067 2241791 := bstep (se 1 (by rfl) ⟨1681343, by rfl⟩ : syracuseStep 2241791 = 3362687) B3362687
theorem B2241833 : Blo 1494067 2241833 := bstep (se 2 (by rfl) ⟨840687, by rfl⟩ : syracuseStep 2241833 = 1681375) B1681375
theorem B9574139 : Blo 1494067 9574139 := bstep (se 1 (by rfl) ⟨7180604, by rfl⟩ : syracuseStep 9574139 = 14361209) B14361209
theorem B2242427 : Blo 1494067 2242427 := bstep (se 1 (by rfl) ⟨1681820, by rfl⟩ : syracuseStep 2242427 = 3363641) B3363641
theorem B2242463 : Blo 1494067 2242463 := bstep (se 1 (by rfl) ⟨1681847, by rfl⟩ : syracuseStep 2242463 = 3363695) B3363695
theorem B2242667 : Blo 1494067 2242667 := bstep (se 1 (by rfl) ⟨1682000, by rfl⟩ : syracuseStep 2242667 = 3364001) B3364001
theorem B2242697 : Blo 1494067 2242697 := bstep (se 2 (by rfl) ⟨841011, by rfl⟩ : syracuseStep 2242697 = 1682023) B1682023
theorem B2521307 : Blo 1494067 2521307 := bstep (se 1 (by rfl) ⟨1890980, by rfl⟩ : syracuseStep 2521307 = 3781961) B3781961
theorem B25876745 : Blo 1494067 25876745 := bstep (se 2 (by rfl) ⟨9703779, by rfl⟩ : syracuseStep 25876745 = 19407559) B19407559
theorem B2242847 : Blo 1494067 2242847 := bstep (se 1 (by rfl) ⟨1682135, by rfl⟩ : syracuseStep 2242847 = 3364271) B3364271
theorem B3455369 : Blo 1494067 3455369 := bstep (se 2 (by rfl) ⟨1295763, by rfl⟩ : syracuseStep 3455369 = 2591527) B2591527
theorem B2521577 : Blo 1494067 2521577 := bstep (se 2 (by rfl) ⟨945591, by rfl⟩ : syracuseStep 2521577 = 1891183) B1891183
theorem B2128361 : Blo 1494067 2128361 := bstep (se 2 (by rfl) ⟨798135, by rfl⟩ : syracuseStep 2128361 = 1596271) B1596271
theorem B8084063 : Blo 1494067 8084063 := bstep (se 1 (by rfl) ⟨6063047, by rfl⟩ : syracuseStep 8084063 = 12126095) B12126095
theorem B5044895 : Blo 1494067 5044895 := bstep (se 1 (by rfl) ⟨3783671, by rfl⟩ : syracuseStep 5044895 = 7567343) B7567343
theorem B8510255 : Blo 1494067 8510255 := bstep (se 1 (by rfl) ⟨6382691, by rfl⟩ : syracuseStep 8510255 = 12765383) B12765383
theorem B36363113 : Blo 1494067 36363113 := bstep (se 2 (by rfl) ⟨13636167, by rfl⟩ : syracuseStep 36363113 = 27272335) B27272335
theorem B4733819 : Blo 1494067 4733819 := bstep (se 1 (by rfl) ⟨3550364, by rfl⟩ : syracuseStep 4733819 = 7100729) B7100729
theorem B5675933 : Blo 1494067 5675933 := bstep (se 3 (by rfl) ⟨1064237, by rfl⟩ : syracuseStep 5675933 = 2128475) B2128475
theorem B3365801 : Blo 1494067 3365801 := bstep (se 2 (by rfl) ⟨1262175, by rfl⟩ : syracuseStep 3365801 = 2524351) B2524351
theorem B119675819 : Blo 1494067 119675819 := bstep (se 1 (by rfl) ⟨89756864, by rfl⟩ : syracuseStep 119675819 = 179513729) B179513729
theorem B5389247 : Blo 1494067 5389247 := bstep (se 1 (by rfl) ⟨4041935, by rfl⟩ : syracuseStep 5389247 = 8083871) B8083871
theorem B2243519 : Blo 1494067 2243519 := bstep (se 1 (by rfl) ⟨1682639, by rfl⟩ : syracuseStep 2243519 = 3365279) B3365279
theorem B2243567 : Blo 1494067 2243567 := bstep (se 1 (by rfl) ⟨1682675, by rfl⟩ : syracuseStep 2243567 = 3365351) B3365351
theorem B38329361 : Blo 1494067 38329361 := bstep (se 2 (by rfl) ⟨14373510, by rfl⟩ : syracuseStep 38329361 = 28747021) B28747021
theorem B8870951 : Blo 1494067 8870951 := bstep (se 1 (by rfl) ⟨6653213, by rfl⟩ : syracuseStep 8870951 = 13306427) B13306427
theorem B5676115 : Blo 1494067 5676115 := bstep (se 1 (by rfl) ⟨4257086, by rfl⟩ : syracuseStep 5676115 = 8514173) B8514173
theorem B2243753 : Blo 1494067 2243753 := bstep (se 2 (by rfl) ⟨841407, by rfl⟩ : syracuseStep 2243753 = 1682815) B1682815
theorem B10779965 : Blo 1494067 10779965 := bstep (se 3 (by rfl) ⟨2021243, by rfl⟩ : syracuseStep 10779965 = 4042487) B4042487
theorem B81870209 : Blo 1494067 81870209 := bstep (se 2 (by rfl) ⟨30701328, by rfl⟩ : syracuseStep 81870209 = 61402657) B61402657
theorem B7568801 : Blo 1494067 7568801 := bstep (se 2 (by rfl) ⟨2838300, by rfl⟩ : syracuseStep 7568801 = 5676601) B5676601
theorem B8084929 : Blo 1494067 8084929 := bstep (se 2 (by rfl) ⟨3031848, by rfl⟩ : syracuseStep 8084929 = 6063697) B6063697
theorem B2522603 : Blo 1494067 2522603 := bstep (se 1 (by rfl) ⟨1891952, by rfl⟩ : syracuseStep 2522603 = 3783905) B3783905
theorem B9576089 : Blo 1494067 9576089 := bstep (se 2 (by rfl) ⟨3591033, by rfl⟩ : syracuseStep 9576089 = 7182067) B7182067
theorem B10510235 : Blo 1494067 10510235 := bstep (se 1 (by rfl) ⟨7882676, by rfl⟩ : syracuseStep 10510235 = 15765353) B15765353
theorem B8511439 : Blo 1494067 8511439 := bstep (se 1 (by rfl) ⟨6383579, by rfl⟩ : syracuseStep 8511439 = 12767159) B12767159
theorem B4546655 : Blo 1494067 4546655 := bstep (se 1 (by rfl) ⟨3409991, by rfl⟩ : syracuseStep 4546655 = 6819983) B6819983
theorem B5046461 : Blo 1494067 5046461 := bstep (se 3 (by rfl) ⟨946211, by rfl⟩ : syracuseStep 5046461 = 1892423) B1892423
theorem B5390675 : Blo 1494067 5390675 := bstep (se 1 (by rfl) ⟨4043006, by rfl⟩ : syracuseStep 5390675 = 8086013) B8086013
theorem B5046623 : Blo 1494067 5046623 := bstep (se 1 (by rfl) ⟨3784967, by rfl⟩ : syracuseStep 5046623 = 7569935) B7569935
theorem B2523899 : Blo 1494067 2523899 := bstep (se 1 (by rfl) ⟨1892924, by rfl⟩ : syracuseStep 2523899 = 3785849) B3785849
theorem B1639583 : Blo 1494067 1639583 := bstep (se 1 (by rfl) ⟨1229687, by rfl⟩ : syracuseStep 1639583 = 2459375) B2459375
theorem B7570745 : Blo 1494067 7570745 := bstep (se 2 (by rfl) ⟨2839029, by rfl⟩ : syracuseStep 7570745 = 5678059) B5678059
theorem B1680871 : Blo 1494067 1680871 := bstep (se 1 (by rfl) ⟨1260653, by rfl⟩ : syracuseStep 1680871 = 2521307) B2521307
theorem B2303579 : Blo 1494067 2303579 := bstep (se 1 (by rfl) ⟨1727684, by rfl⟩ : syracuseStep 2303579 = 3455369) B3455369
theorem B8087177 : Blo 1494067 8087177 := bstep (se 2 (by rfl) ⟨3032691, by rfl⟩ : syracuseStep 8087177 = 6065383) B6065383
theorem B1681051 : Blo 1494067 1681051 := bstep (se 1 (by rfl) ⟨1260788, by rfl⟩ : syracuseStep 1681051 = 2521577) B2521577
theorem B24242075 : Blo 1494067 24242075 := bstep (se 1 (by rfl) ⟨18181556, by rfl⟩ : syracuseStep 24242075 = 36363113) B36363113
theorem B3155879 : Blo 1494067 3155879 := bstep (se 1 (by rfl) ⟨2366909, by rfl⟩ : syracuseStep 3155879 = 4733819) B4733819
theorem B79783879 : Blo 1494067 79783879 := bstep (se 1 (by rfl) ⟨59837909, by rfl⟩ : syracuseStep 79783879 = 119675819) B119675819
theorem B21555193 : Blo 1494067 21555193 := bstep (se 2 (by rfl) ⟨8083197, by rfl⟩ : syracuseStep 21555193 = 16166395) B16166395
theorem B25552907 : Blo 1494067 25552907 := bstep (se 1 (by rfl) ⟨19164680, by rfl⟩ : syracuseStep 25552907 = 38329361) B38329361
theorem B48465971 : Blo 1494067 48465971 := bstep (se 1 (by rfl) ⟨36349478, by rfl⟩ : syracuseStep 48465971 = 72698957) B72698957
theorem B5048459 : Blo 1494067 5048459 := bstep (se 1 (by rfl) ⟨3786344, by rfl⟩ : syracuseStep 5048459 = 7572689) B7572689
theorem B7186643 : Blo 1494067 7186643 := bstep (se 1 (by rfl) ⟨5389982, by rfl⟩ : syracuseStep 7186643 = 10779965) B10779965
theorem B1681735 : Blo 1494067 1681735 := bstep (se 1 (by rfl) ⟨1261301, by rfl⟩ : syracuseStep 1681735 = 2522603) B2522603
theorem B81889663 : Blo 1494067 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B6384059 : Blo 1494067 6384059 := bstep (se 1 (by rfl) ⟨4788044, by rfl⟩ : syracuseStep 6384059 = 9576089) B9576089
theorem B7006823 : Blo 1494067 7006823 := bstep (se 1 (by rfl) ⟨5255117, by rfl⟩ : syracuseStep 7006823 = 10510235) B10510235
theorem B11348585 : Blo 1494067 11348585 := bstep (se 2 (by rfl) ⟨4255719, by rfl⟩ : syracuseStep 11348585 = 8511439) B8511439
theorem B6064799 : Blo 1494067 6064799 := bstep (se 1 (by rfl) ⟨4548599, by rfl⟩ : syracuseStep 6064799 = 9097199) B9097199
theorem B5048999 : Blo 1494067 5048999 := bstep (se 1 (by rfl) ⟨3786749, by rfl⟩ : syracuseStep 5048999 = 7573499) B7573499
theorem B2878319 : Blo 1494067 2878319 := bstep (se 1 (by rfl) ⟨2158739, by rfl⟩ : syracuseStep 2878319 = 4317479) B4317479
theorem B196652033 : Blo 1494067 196652033 := bstep (se 2 (by rfl) ⟨73744512, by rfl⟩ : syracuseStep 196652033 = 147489025) B147489025
theorem B6384673 : Blo 1494067 6384673 := bstep (se 2 (by rfl) ⟨2394252, by rfl⟩ : syracuseStep 6384673 = 4788505) B4788505
theorem B1494127 : Blo 1494067 1494127 := bstep (se 1 (by rfl) ⟨1120595, by rfl⟩ : syracuseStep 1494127 = 2241191) B2241191
theorem B10226857 : Blo 1494067 10226857 := bstep (se 2 (by rfl) ⟨3835071, by rfl⟩ : syracuseStep 10226857 = 7670143) B7670143
theorem B1494207 : Blo 1494067 1494207 := bstep (se 1 (by rfl) ⟨1120655, by rfl⟩ : syracuseStep 1494207 = 2241311) B2241311
theorem B1494223 : Blo 1494067 1494223 := bstep (se 1 (by rfl) ⟨1120667, by rfl⟩ : syracuseStep 1494223 = 2241335) B2241335
theorem B1494299 : Blo 1494067 1494299 := bstep (se 1 (by rfl) ⟨1120724, by rfl⟩ : syracuseStep 1494299 = 2241449) B2241449
theorem B1494343 : Blo 1494067 1494343 := bstep (se 1 (by rfl) ⟨1120757, by rfl⟩ : syracuseStep 1494343 = 2241515) B2241515
theorem B1494527 : Blo 1494067 1494527 := bstep (se 1 (by rfl) ⟨1120895, by rfl⟩ : syracuseStep 1494527 = 2241791) B2241791
theorem B1494555 : Blo 1494067 1494555 := bstep (se 1 (by rfl) ⟨1120916, by rfl⟩ : syracuseStep 1494555 = 2241833) B2241833
theorem B1494951 : Blo 1494067 1494951 := bstep (se 1 (by rfl) ⟨1121213, by rfl⟩ : syracuseStep 1494951 = 2242427) B2242427
theorem B1494975 : Blo 1494067 1494975 := bstep (se 1 (by rfl) ⟨1121231, by rfl⟩ : syracuseStep 1494975 = 2242463) B2242463
theorem B1495111 : Blo 1494067 1495111 := bstep (se 1 (by rfl) ⟨1121333, by rfl⟩ : syracuseStep 1495111 = 2242667) B2242667
theorem B1495131 : Blo 1494067 1495131 := bstep (se 1 (by rfl) ⟨1121348, by rfl⟩ : syracuseStep 1495131 = 2242697) B2242697
theorem B9580679 : Blo 1494067 9580679 := bstep (se 1 (by rfl) ⟨7185509, by rfl⟩ : syracuseStep 9580679 = 14371019) B14371019
theorem B1495231 : Blo 1494067 1495231 := bstep (se 1 (by rfl) ⟨1121423, by rfl⟩ : syracuseStep 1495231 = 2242847) B2242847
theorem B21557501 : Blo 1494067 21557501 := bstep (se 3 (by rfl) ⟨4042031, by rfl⟩ : syracuseStep 21557501 = 8084063) B8084063
theorem B3363263 : Blo 1494067 3363263 := bstep (se 1 (by rfl) ⟨2522447, by rfl⟩ : syracuseStep 3363263 = 5044895) B5044895
theorem B5673503 : Blo 1494067 5673503 := bstep (se 1 (by rfl) ⟨4255127, by rfl⟩ : syracuseStep 5673503 = 8510255) B8510255
theorem B3592831 : Blo 1494067 3592831 := bstep (se 1 (by rfl) ⟨2694623, by rfl⟩ : syracuseStep 3592831 = 5389247) B5389247
theorem B1495679 : Blo 1494067 1495679 := bstep (se 1 (by rfl) ⟨1121759, by rfl⟩ : syracuseStep 1495679 = 2243519) B2243519
theorem B25531037 : Blo 1494067 25531037 := bstep (se 3 (by rfl) ⟨4787069, by rfl⟩ : syracuseStep 25531037 = 9574139) B9574139
theorem B1495711 : Blo 1494067 1495711 := bstep (se 1 (by rfl) ⟨1121783, by rfl⟩ : syracuseStep 1495711 = 2243567) B2243567
theorem B1495835 : Blo 1494067 1495835 := bstep (se 1 (by rfl) ⟨1121876, by rfl⟩ : syracuseStep 1495835 = 2243753) B2243753
theorem B2241371 : Blo 1494067 2241371 := bstep (se 1 (by rfl) ⟨1681028, by rfl⟩ : syracuseStep 2241371 = 3362057) B3362057
theorem B54580139 : Blo 1494067 54580139 := bstep (se 1 (by rfl) ⟨40935104, by rfl⟩ : syracuseStep 54580139 = 81870209) B81870209
theorem B17265581 : Blo 1494067 17265581 := bstep (se 3 (by rfl) ⟨3237296, by rfl⟩ : syracuseStep 17265581 = 6474593) B6474593
theorem B2241503 : Blo 1494067 2241503 := bstep (se 1 (by rfl) ⟨1681127, by rfl⟩ : syracuseStep 2241503 = 3362255) B3362255
theorem B2241563 : Blo 1494067 2241563 := bstep (se 1 (by rfl) ⟨1681172, by rfl⟩ : syracuseStep 2241563 = 3362345) B3362345
theorem B3191995 : Blo 1494067 3191995 := bstep (se 1 (by rfl) ⟨2393996, by rfl⟩ : syracuseStep 3191995 = 4787993) B4787993
theorem B34518311 : Blo 1494067 34518311 := bstep (se 1 (by rfl) ⟨25888733, by rfl⟩ : syracuseStep 34518311 = 51777467) B51777467
theorem B3782123 : Blo 1494067 3782123 := bstep (se 1 (by rfl) ⟨2836592, by rfl⟩ : syracuseStep 3782123 = 5673185) B5673185
theorem B2242031 : Blo 1494067 2242031 := bstep (se 1 (by rfl) ⟨1681523, by rfl⟩ : syracuseStep 2242031 = 3363047) B3363047
theorem B49821227 : Blo 1494067 49821227 := bstep (se 1 (by rfl) ⟨37365920, by rfl⟩ : syracuseStep 49821227 = 74731841) B74731841
theorem B2242151 : Blo 1494067 2242151 := bstep (se 1 (by rfl) ⟨1681613, by rfl⟩ : syracuseStep 2242151 = 3363227) B3363227
theorem B6469289 : Blo 1494067 6469289 := bstep (se 2 (by rfl) ⟨2425983, by rfl⟩ : syracuseStep 6469289 = 4851967) B4851967
theorem B4257839 : Blo 1494067 4257839 := bstep (se 1 (by rfl) ⟨3193379, by rfl⟩ : syracuseStep 4257839 = 6386759) B6386759
theorem B3365099 : Blo 1494067 3365099 := bstep (se 1 (by rfl) ⟨2523824, by rfl⟩ : syracuseStep 3365099 = 5047649) B5047649
theorem B3365459 : Blo 1494067 3365459 := bstep (se 1 (by rfl) ⟨2524094, by rfl⟩ : syracuseStep 3365459 = 5048189) B5048189
theorem B5675629 : Blo 1494067 5675629 := bstep (se 3 (by rfl) ⟨1064180, by rfl⟩ : syracuseStep 5675629 = 2128361) B2128361
theorem B3365567 : Blo 1494067 3365567 := bstep (se 1 (by rfl) ⟨2524175, by rfl⟩ : syracuseStep 3365567 = 5048351) B5048351
theorem B7568153 : Blo 1494067 7568153 := bstep (se 2 (by rfl) ⟨2838057, by rfl⟩ : syracuseStep 7568153 = 5676115) B5676115
theorem B17251163 : Blo 1494067 17251163 := bstep (se 1 (by rfl) ⟨12938372, by rfl⟩ : syracuseStep 17251163 = 25876745) B25876745
theorem B10779905 : Blo 1494067 10779905 := bstep (se 2 (by rfl) ⟨4042464, by rfl⟩ : syracuseStep 10779905 = 8084929) B8084929
theorem B3783955 : Blo 1494067 3783955 := bstep (se 1 (by rfl) ⟨2837966, by rfl⟩ : syracuseStep 3783955 = 5675933) B5675933
theorem B2243867 : Blo 1494067 2243867 := bstep (se 1 (by rfl) ⟨1682900, by rfl⟩ : syracuseStep 2243867 = 3365801) B3365801
theorem B17268029 : Blo 1494067 17268029 := bstep (se 3 (by rfl) ⟨3237755, by rfl⟩ : syracuseStep 17268029 = 6475511) B6475511
theorem B5913967 : Blo 1494067 5913967 := bstep (se 1 (by rfl) ⟨4435475, by rfl⟩ : syracuseStep 5913967 = 8870951) B8870951
theorem B5045867 : Blo 1494067 5045867 := bstep (se 1 (by rfl) ⟨3784400, by rfl⟩ : syracuseStep 5045867 = 7568801) B7568801
theorem B8511257 : Blo 1494067 8511257 := bstep (se 2 (by rfl) ⟨3191721, by rfl⟩ : syracuseStep 8511257 = 6383443) B6383443
theorem B4792223 : Blo 1494067 4792223 := bstep (se 1 (by rfl) ⟨3594167, by rfl⟩ : syracuseStep 4792223 = 7188335) B7188335
theorem B11509703 : Blo 1494067 11509703 := bstep (se 1 (by rfl) ⟨8632277, by rfl⟩ : syracuseStep 11509703 = 17264555) B17264555
theorem B3031103 : Blo 1494067 3031103 := bstep (se 1 (by rfl) ⟨2273327, by rfl⟩ : syracuseStep 3031103 = 4546655) B4546655
theorem B11510387 : Blo 1494067 11510387 := bstep (se 1 (by rfl) ⟨8632790, by rfl⟩ : syracuseStep 11510387 = 17265581) B17265581
theorem B23012207 : Blo 1494067 23012207 := bstep (se 1 (by rfl) ⟨17259155, by rfl⟩ : syracuseStep 23012207 = 34518311) B34518311
theorem B5047163 : Blo 1494067 5047163 := bstep (se 1 (by rfl) ⟨3785372, by rfl⟩ : syracuseStep 5047163 = 7570745) B7570745
theorem B5391451 : Blo 1494067 5391451 := bstep (se 1 (by rfl) ⟨4043588, by rfl⟩ : syracuseStep 5391451 = 8087177) B8087177
theorem B32310647 : Blo 1494067 32310647 := bstep (se 1 (by rfl) ⟨24232985, by rfl⟩ : syracuseStep 32310647 = 48465971) B48465971
theorem B8512897 : Blo 1494067 8512897 := bstep (se 2 (by rfl) ⟨3192336, by rfl⟩ : syracuseStep 8512897 = 6384673) B6384673
theorem B4671215 : Blo 1494067 4671215 := bstep (se 1 (by rfl) ⟨3503411, by rfl⟩ : syracuseStep 4671215 = 7006823) B7006823
theorem B16172797 : Blo 1494067 16172797 := bstep (se 3 (by rfl) ⟨3032399, by rfl⟩ : syracuseStep 16172797 = 6064799) B6064799
theorem B1918879 : Blo 1494067 1918879 := bstep (se 1 (by rfl) ⟨1439159, by rfl⟩ : syracuseStep 1918879 = 2878319) B2878319
theorem B7186603 : Blo 1494067 7186603 := bstep (se 1 (by rfl) ⟨5389952, by rfl⟩ : syracuseStep 7186603 = 10779905) B10779905
theorem B11512019 : Blo 1494067 11512019 := bstep (se 1 (by rfl) ⟨8634014, by rfl⟩ : syracuseStep 11512019 = 17268029) B17268029
theorem B8415677 : Blo 1494067 8415677 := bstep (se 3 (by rfl) ⟨1577939, by rfl⟩ : syracuseStep 8415677 = 3155879) B3155879
theorem B28740257 : Blo 1494067 28740257 := bstep (se 2 (by rfl) ⟨10777596, by rfl⟩ : syracuseStep 28740257 = 21555193) B21555193
theorem B14371667 : Blo 1494067 14371667 := bstep (se 1 (by rfl) ⟨10778750, by rfl⟩ : syracuseStep 14371667 = 21557501) B21557501
theorem B1682599 : Blo 1494067 1682599 := bstep (se 1 (by rfl) ⟨1261949, by rfl⟩ : syracuseStep 1682599 = 2523899) B2523899
theorem B109186217 : Blo 1494067 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B1494247 : Blo 1494067 1494247 := bstep (se 1 (by rfl) ⟨1120685, by rfl⟩ : syracuseStep 1494247 = 2241371) B2241371
theorem B1494335 : Blo 1494067 1494335 := bstep (se 1 (by rfl) ⟨1120751, by rfl⟩ : syracuseStep 1494335 = 2241503) B2241503
theorem B1494375 : Blo 1494067 1494375 := bstep (se 1 (by rfl) ⟨1120781, by rfl⟩ : syracuseStep 1494375 = 2241563) B2241563
theorem B1494687 : Blo 1494067 1494687 := bstep (se 1 (by rfl) ⟨1121015, by rfl⟩ : syracuseStep 1494687 = 2242031) B2242031
theorem B33214151 : Blo 1494067 33214151 := bstep (se 1 (by rfl) ⟨24910613, by rfl⟩ : syracuseStep 33214151 = 49821227) B49821227
theorem B1494767 : Blo 1494067 1494767 := bstep (se 1 (by rfl) ⟨1121075, by rfl⟩ : syracuseStep 1494767 = 2242151) B2242151
theorem B4312859 : Blo 1494067 4312859 := bstep (se 1 (by rfl) ⟨3234644, by rfl⟩ : syracuseStep 4312859 = 6469289) B6469289
theorem B17035271 : Blo 1494067 17035271 := bstep (se 1 (by rfl) ⟨12776453, by rfl⟩ : syracuseStep 17035271 = 25552907) B25552907
theorem B2838559 : Blo 1494067 2838559 := bstep (se 1 (by rfl) ⟨2128919, by rfl⟩ : syracuseStep 2838559 = 4257839) B4257839
theorem B13635809 : Blo 1494067 13635809 := bstep (se 2 (by rfl) ⟨5113428, by rfl⟩ : syracuseStep 13635809 = 10226857) B10226857
theorem B4255993 : Blo 1494067 4255993 := bstep (se 2 (by rfl) ⟨1595997, by rfl⟩ : syracuseStep 4255993 = 3191995) B3191995
theorem B4256039 : Blo 1494067 4256039 := bstep (se 1 (by rfl) ⟨3192029, by rfl⟩ : syracuseStep 4256039 = 6384059) B6384059
theorem B7565723 : Blo 1494067 7565723 := bstep (se 1 (by rfl) ⟨5674292, by rfl⟩ : syracuseStep 7565723 = 11348585) B11348585
theorem B7885289 : Blo 1494067 7885289 := bstep (se 2 (by rfl) ⟨2956983, by rfl⟩ : syracuseStep 7885289 = 5913967) B5913967
theorem B2241161 : Blo 1494067 2241161 := bstep (se 2 (by rfl) ⟨840435, by rfl⟩ : syracuseStep 2241161 = 1680871) B1680871
theorem B131101355 : Blo 1494067 131101355 := bstep (se 1 (by rfl) ⟨98326016, by rfl⟩ : syracuseStep 131101355 = 196652033) B196652033
theorem B1495911 : Blo 1494067 1495911 := bstep (se 1 (by rfl) ⟨1121933, by rfl⟩ : syracuseStep 1495911 = 2243867) B2243867
theorem B2241401 : Blo 1494067 2241401 := bstep (se 2 (by rfl) ⟨840525, by rfl⟩ : syracuseStep 2241401 = 1681051) B1681051
theorem B3363911 : Blo 1494067 3363911 := bstep (se 1 (by rfl) ⟨2522933, by rfl⟩ : syracuseStep 3363911 = 5045867) B5045867
theorem B5674171 : Blo 1494067 5674171 := bstep (se 1 (by rfl) ⟨4255628, by rfl⟩ : syracuseStep 5674171 = 8511257) B8511257
theorem B106378505 : Blo 1494067 106378505 := bstep (se 2 (by rfl) ⟨39891939, by rfl⟩ : syracuseStep 106378505 = 79783879) B79783879
theorem B7673135 : Blo 1494067 7673135 := bstep (se 1 (by rfl) ⟨5754851, by rfl⟩ : syracuseStep 7673135 = 11509703) B11509703
theorem B6387119 : Blo 1494067 6387119 := bstep (se 1 (by rfl) ⟨4790339, by rfl⟩ : syracuseStep 6387119 = 9580679) B9580679
theorem B3364307 : Blo 1494067 3364307 := bstep (se 1 (by rfl) ⟨2523230, by rfl⟩ : syracuseStep 3364307 = 5046461) B5046461
theorem B3593783 : Blo 1494067 3593783 := bstep (se 1 (by rfl) ⟨2695337, by rfl⟩ : syracuseStep 3593783 = 5390675) B5390675
theorem B3364415 : Blo 1494067 3364415 := bstep (se 1 (by rfl) ⟨2523311, by rfl⟩ : syracuseStep 3364415 = 5046623) B5046623
theorem B2242175 : Blo 1494067 2242175 := bstep (se 1 (by rfl) ⟨1681631, by rfl⟩ : syracuseStep 2242175 = 3363263) B3363263
theorem B3782335 : Blo 1494067 3782335 := bstep (se 1 (by rfl) ⟨2836751, by rfl⟩ : syracuseStep 3782335 = 5673503) B5673503
theorem B2242313 : Blo 1494067 2242313 := bstep (se 2 (by rfl) ⟨840867, by rfl⟩ : syracuseStep 2242313 = 1681735) B1681735
theorem B17020691 : Blo 1494067 17020691 := bstep (se 1 (by rfl) ⟨12765518, by rfl⟩ : syracuseStep 17020691 = 25531037) B25531037
theorem B36386759 : Blo 1494067 36386759 := bstep (se 1 (by rfl) ⟨27290069, by rfl⟩ : syracuseStep 36386759 = 54580139) B54580139
theorem B7567505 : Blo 1494067 7567505 := bstep (se 2 (by rfl) ⟨2837814, by rfl⟩ : syracuseStep 7567505 = 5675629) B5675629
theorem B4790441 : Blo 1494067 4790441 := bstep (se 2 (by rfl) ⟨1796415, by rfl⟩ : syracuseStep 4790441 = 3592831) B3592831
theorem B2521415 : Blo 1494067 2521415 := bstep (se 1 (by rfl) ⟨1891061, by rfl⟩ : syracuseStep 2521415 = 3782123) B3782123
theorem B16161383 : Blo 1494067 16161383 := bstep (se 1 (by rfl) ⟨12121037, by rfl⟩ : syracuseStep 16161383 = 24242075) B24242075
theorem B3365639 : Blo 1494067 3365639 := bstep (se 1 (by rfl) ⟨2524229, by rfl⟩ : syracuseStep 3365639 = 5048459) B5048459
theorem B4791095 : Blo 1494067 4791095 := bstep (se 1 (by rfl) ⟨3593321, by rfl⟩ : syracuseStep 4791095 = 7186643) B7186643
theorem B2243399 : Blo 1494067 2243399 := bstep (se 1 (by rfl) ⟨1682549, by rfl⟩ : syracuseStep 2243399 = 3365099) B3365099
theorem B6142877 : Blo 1494067 6142877 := bstep (se 3 (by rfl) ⟨1151789, by rfl⟩ : syracuseStep 6142877 = 2303579) B2303579
theorem B17488885 : Blo 1494067 17488885 := bstep (se 5 (by rfl) ⟨819791, by rfl⟩ : syracuseStep 17488885 = 1639583) B1639583
theorem B5045273 : Blo 1494067 5045273 := bstep (se 2 (by rfl) ⟨1891977, by rfl⟩ : syracuseStep 5045273 = 3783955) B3783955
theorem B2243639 : Blo 1494067 2243639 := bstep (se 1 (by rfl) ⟨1682729, by rfl⟩ : syracuseStep 2243639 = 3365459) B3365459
theorem B3365999 : Blo 1494067 3365999 := bstep (se 1 (by rfl) ⟨2524499, by rfl⟩ : syracuseStep 3365999 = 5048999) B5048999
theorem B2243711 : Blo 1494067 2243711 := bstep (se 1 (by rfl) ⟨1682783, by rfl⟩ : syracuseStep 2243711 = 3365567) B3365567
theorem B5045435 : Blo 1494067 5045435 := bstep (se 1 (by rfl) ⟨3784076, by rfl⟩ : syracuseStep 5045435 = 7568153) B7568153
theorem B11500775 : Blo 1494067 11500775 := bstep (se 1 (by rfl) ⟨8625581, by rfl⟩ : syracuseStep 11500775 = 17251163) B17251163
theorem B3194815 : Blo 1494067 3194815 := bstep (se 1 (by rfl) ⟨2396111, by rfl⟩ : syracuseStep 3194815 = 4792223) B4792223
theorem B3784745 : Blo 1494067 3784745 := bstep (se 2 (by rfl) ⟨1419279, by rfl⟩ : syracuseStep 3784745 = 2838559) B2838559
theorem B87400903 : Blo 1494067 87400903 := bstep (se 1 (by rfl) ⟨65550677, by rfl⟩ : syracuseStep 87400903 = 131101355) B131101355
theorem B70919003 : Blo 1494067 70919003 := bstep (se 1 (by rfl) ⟨53189252, by rfl⟩ : syracuseStep 70919003 = 106378505) B106378505
theorem B3114143 : Blo 1494067 3114143 := bstep (se 1 (by rfl) ⟨2335607, by rfl⟩ : syracuseStep 3114143 = 4671215) B4671215
theorem B11347127 : Blo 1494067 11347127 := bstep (se 1 (by rfl) ⟨8510345, by rfl⟩ : syracuseStep 11347127 = 17020691) B17020691
theorem B24257839 : Blo 1494067 24257839 := bstep (se 1 (by rfl) ⟨18193379, by rfl⟩ : syracuseStep 24257839 = 36386759) B36386759
theorem B1680943 : Blo 1494067 1680943 := bstep (se 1 (by rfl) ⟨1260707, by rfl⟩ : syracuseStep 1680943 = 2521415) B2521415
theorem B10774255 : Blo 1494067 10774255 := bstep (se 1 (by rfl) ⟨8080691, by rfl⟩ : syracuseStep 10774255 = 16161383) B16161383
theorem B10234021 : Blo 1494067 10234021 := bstep (se 4 (by rfl) ⟨959439, by rfl⟩ : syracuseStep 10234021 = 1918879) B1918879
theorem B21563729 : Blo 1494067 21563729 := bstep (se 2 (by rfl) ⟨8086398, by rfl⟩ : syracuseStep 21563729 = 16172797) B16172797
theorem B11356847 : Blo 1494067 11356847 := bstep (se 1 (by rfl) ⟨8517635, by rfl⟩ : syracuseStep 11356847 = 17035271) B17035271
theorem B2837359 : Blo 1494067 2837359 := bstep (se 1 (by rfl) ⟨2128019, by rfl⟩ : syracuseStep 2837359 = 4256039) B4256039
theorem B1494107 : Blo 1494067 1494107 := bstep (se 1 (by rfl) ⟨1120580, by rfl⟩ : syracuseStep 1494107 = 2241161) B2241161
theorem B12774509 : Blo 1494067 12774509 := bstep (se 3 (by rfl) ⟨2395220, by rfl⟩ : syracuseStep 12774509 = 4790441) B4790441
theorem B1494267 : Blo 1494067 1494267 := bstep (se 1 (by rfl) ⟨1120700, by rfl⟩ : syracuseStep 1494267 = 2241401) B2241401
theorem B21540431 : Blo 1494067 21540431 := bstep (se 1 (by rfl) ⟨16155323, by rfl⟩ : syracuseStep 21540431 = 32310647) B32310647
theorem B2395855 : Blo 1494067 2395855 := bstep (se 1 (by rfl) ⟨1796891, by rfl⟩ : syracuseStep 2395855 = 3593783) B3593783
theorem B1494783 : Blo 1494067 1494783 := bstep (se 1 (by rfl) ⟨1121087, by rfl⟩ : syracuseStep 1494783 = 2242175) B2242175
theorem B1494875 : Blo 1494067 1494875 := bstep (se 1 (by rfl) ⟨1121156, by rfl⟩ : syracuseStep 1494875 = 2242313) B2242313
theorem B23318513 : Blo 1494067 23318513 := bstep (se 2 (by rfl) ⟨8744442, by rfl⟩ : syracuseStep 23318513 = 17488885) B17488885
theorem B7188601 : Blo 1494067 7188601 := bstep (se 2 (by rfl) ⟨2695725, by rfl⟩ : syracuseStep 7188601 = 5391451) B5391451
theorem B7565561 : Blo 1494067 7565561 := bstep (se 2 (by rfl) ⟨2837085, by rfl⟩ : syracuseStep 7565561 = 5674171) B5674171
theorem B11350529 : Blo 1494067 11350529 := bstep (se 2 (by rfl) ⟨4256448, by rfl⟩ : syracuseStep 11350529 = 8512897) B8512897
theorem B1495599 : Blo 1494067 1495599 := bstep (se 1 (by rfl) ⟨1121699, by rfl⟩ : syracuseStep 1495599 = 2243399) B2243399
theorem B9581111 : Blo 1494067 9581111 := bstep (se 1 (by rfl) ⟨7185833, by rfl⟩ : syracuseStep 9581111 = 14371667) B14371667
theorem B3363515 : Blo 1494067 3363515 := bstep (se 1 (by rfl) ⟨2522636, by rfl⟩ : syracuseStep 3363515 = 5045273) B5045273
theorem B1495759 : Blo 1494067 1495759 := bstep (se 1 (by rfl) ⟨1121819, by rfl⟩ : syracuseStep 1495759 = 2243639) B2243639
theorem B1495807 : Blo 1494067 1495807 := bstep (se 1 (by rfl) ⟨1121855, by rfl⟩ : syracuseStep 1495807 = 2243711) B2243711
theorem B72790811 : Blo 1494067 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B3363623 : Blo 1494067 3363623 := bstep (se 1 (by rfl) ⟨2522717, by rfl⟩ : syracuseStep 3363623 = 5045435) B5045435
theorem B5043113 : Blo 1494067 5043113 := bstep (se 2 (by rfl) ⟨1891167, by rfl⟩ : syracuseStep 5043113 = 3782335) B3782335
theorem B2020735 : Blo 1494067 2020735 := bstep (se 1 (by rfl) ⟨1515551, by rfl⟩ : syracuseStep 2020735 = 3031103) B3031103
theorem B9090539 : Blo 1494067 9090539 := bstep (se 1 (by rfl) ⟨6817904, by rfl⟩ : syracuseStep 9090539 = 13635809) B13635809
theorem B9582137 : Blo 1494067 9582137 := bstep (se 2 (by rfl) ⟨3593301, by rfl⟩ : syracuseStep 9582137 = 7186603) B7186603
theorem B5043815 : Blo 1494067 5043815 := bstep (se 1 (by rfl) ⟨3782861, by rfl⟩ : syracuseStep 5043815 = 7565723) B7565723
theorem B5674657 : Blo 1494067 5674657 := bstep (se 2 (by rfl) ⟨2127996, by rfl⟩ : syracuseStep 5674657 = 4255993) B4255993
theorem B7673591 : Blo 1494067 7673591 := bstep (se 1 (by rfl) ⟨5755193, by rfl⟩ : syracuseStep 7673591 = 11510387) B11510387
theorem B15341471 : Blo 1494067 15341471 := bstep (se 1 (by rfl) ⟨11506103, by rfl⟩ : syracuseStep 15341471 = 23012207) B23012207
theorem B3364775 : Blo 1494067 3364775 := bstep (se 1 (by rfl) ⟨2523581, by rfl⟩ : syracuseStep 3364775 = 5047163) B5047163
theorem B2242607 : Blo 1494067 2242607 := bstep (se 1 (by rfl) ⟨1681955, by rfl⟩ : syracuseStep 2242607 = 3363911) B3363911
theorem B20461693 : Blo 1494067 20461693 := bstep (se 3 (by rfl) ⟨3836567, by rfl⟩ : syracuseStep 20461693 = 7673135) B7673135
theorem B4258079 : Blo 1494067 4258079 := bstep (se 1 (by rfl) ⟨3193559, by rfl⟩ : syracuseStep 4258079 = 6387119) B6387119
theorem B2242871 : Blo 1494067 2242871 := bstep (se 1 (by rfl) ⟨1682153, by rfl⟩ : syracuseStep 2242871 = 3364307) B3364307
theorem B2242943 : Blo 1494067 2242943 := bstep (se 1 (by rfl) ⟨1682207, by rfl⟩ : syracuseStep 2242943 = 3364415) B3364415
theorem B21027437 : Blo 1494067 21027437 := bstep (se 3 (by rfl) ⟨3942644, by rfl⟩ : syracuseStep 21027437 = 7885289) B7885289
theorem B5045003 : Blo 1494067 5045003 := bstep (se 1 (by rfl) ⟨3783752, by rfl⟩ : syracuseStep 5045003 = 7567505) B7567505
theorem B7674679 : Blo 1494067 7674679 := bstep (se 1 (by rfl) ⟨5756009, by rfl⟩ : syracuseStep 7674679 = 11512019) B11512019
theorem B2243465 : Blo 1494067 2243465 := bstep (se 2 (by rfl) ⟨841299, by rfl⟩ : syracuseStep 2243465 = 1682599) B1682599
theorem B5610451 : Blo 1494067 5610451 := bstep (se 1 (by rfl) ⟨4207838, by rfl⟩ : syracuseStep 5610451 = 8415677) B8415677
theorem B19160171 : Blo 1494067 19160171 := bstep (se 1 (by rfl) ⟨14370128, by rfl⟩ : syracuseStep 19160171 = 28740257) B28740257
theorem B2243759 : Blo 1494067 2243759 := bstep (se 1 (by rfl) ⟨1682819, by rfl⟩ : syracuseStep 2243759 = 3365639) B3365639
theorem B3194063 : Blo 1494067 3194063 := bstep (se 1 (by rfl) ⟨2395547, by rfl⟩ : syracuseStep 3194063 = 4791095) B4791095
theorem B4095251 : Blo 1494067 4095251 := bstep (se 1 (by rfl) ⟨3071438, by rfl⟩ : syracuseStep 4095251 = 6142877) B6142877
theorem B11500957 : Blo 1494067 11500957 := bstep (se 3 (by rfl) ⟨2156429, by rfl⟩ : syracuseStep 11500957 = 4312859) B4312859
theorem B2243999 : Blo 1494067 2243999 := bstep (se 1 (by rfl) ⟨1682999, by rfl⟩ : syracuseStep 2243999 = 3365999) B3365999
theorem B7667183 : Blo 1494067 7667183 := bstep (se 1 (by rfl) ⟨5750387, by rfl⟩ : syracuseStep 7667183 = 11500775) B11500775
theorem B22142767 : Blo 1494067 22142767 := bstep (se 1 (by rfl) ⟨16607075, by rfl⟩ : syracuseStep 22142767 = 33214151) B33214151
theorem B4259753 : Blo 1494067 4259753 := bstep (se 2 (by rfl) ⟨1597407, by rfl⟩ : syracuseStep 4259753 = 3194815) B3194815
theorem B2523163 : Blo 1494067 2523163 := bstep (se 1 (by rfl) ⟨1892372, by rfl⟩ : syracuseStep 2523163 = 3784745) B3784745
theorem B9584801 : Blo 1494067 9584801 := bstep (se 2 (by rfl) ⟨3594300, by rfl⟩ : syracuseStep 9584801 = 7188601) B7188601
theorem B10232905 : Blo 1494067 10232905 := bstep (se 2 (by rfl) ⟨3837339, by rfl⟩ : syracuseStep 10232905 = 7674679) B7674679
theorem B7480601 : Blo 1494067 7480601 := bstep (se 2 (by rfl) ⟨2805225, by rfl⟩ : syracuseStep 7480601 = 5610451) B5610451
theorem B32343785 : Blo 1494067 32343785 := bstep (se 2 (by rfl) ⟨12128919, by rfl⟩ : syracuseStep 32343785 = 24257839) B24257839
theorem B14018291 : Blo 1494067 14018291 := bstep (se 1 (by rfl) ⟨10513718, by rfl⟩ : syracuseStep 14018291 = 21027437) B21027437
theorem B7571231 : Blo 1494067 7571231 := bstep (se 1 (by rfl) ⟨5678423, by rfl⟩ : syracuseStep 7571231 = 11356847) B11356847
theorem B12773447 : Blo 1494067 12773447 := bstep (se 1 (by rfl) ⟨9580085, by rfl⟩ : syracuseStep 12773447 = 19160171) B19160171
theorem B2730167 : Blo 1494067 2730167 := bstep (se 1 (by rfl) ⟨2047625, by rfl⟩ : syracuseStep 2730167 = 4095251) B4095251
theorem B27282257 : Blo 1494067 27282257 := bstep (se 2 (by rfl) ⟨10230846, by rfl⟩ : syracuseStep 27282257 = 20461693) B20461693
theorem B116534537 : Blo 1494067 116534537 := bstep (se 2 (by rfl) ⟨43700451, by rfl⟩ : syracuseStep 116534537 = 87400903) B87400903
theorem B3362075 : Blo 1494067 3362075 := bstep (se 1 (by rfl) ⟨2521556, by rfl⟩ : syracuseStep 3362075 = 5043113) B5043113
theorem B2076095 : Blo 1494067 2076095 := bstep (se 1 (by rfl) ⟨1557071, by rfl⟩ : syracuseStep 2076095 = 3114143) B3114143
theorem B7564751 : Blo 1494067 7564751 := bstep (se 1 (by rfl) ⟨5673563, by rfl⟩ : syracuseStep 7564751 = 11347127) B11347127
theorem B3362543 : Blo 1494067 3362543 := bstep (se 1 (by rfl) ⟨2521907, by rfl⟩ : syracuseStep 3362543 = 5043815) B5043815
theorem B5115727 : Blo 1494067 5115727 := bstep (se 1 (by rfl) ⟨3836795, by rfl⟩ : syracuseStep 5115727 = 7673591) B7673591
theorem B10227647 : Blo 1494067 10227647 := bstep (se 1 (by rfl) ⟨7670735, by rfl⟩ : syracuseStep 10227647 = 15341471) B15341471
theorem B1495071 : Blo 1494067 1495071 := bstep (se 1 (by rfl) ⟨1121303, by rfl⟩ : syracuseStep 1495071 = 2242607) B2242607
theorem B2838719 : Blo 1494067 2838719 := bstep (se 1 (by rfl) ⟨2129039, by rfl⟩ : syracuseStep 2838719 = 4258079) B4258079
theorem B1495247 : Blo 1494067 1495247 := bstep (se 1 (by rfl) ⟨1121435, by rfl⟩ : syracuseStep 1495247 = 2242871) B2242871
theorem B1495295 : Blo 1494067 1495295 := bstep (se 1 (by rfl) ⟨1121471, by rfl⟩ : syracuseStep 1495295 = 2242943) B2242943
theorem B3363335 : Blo 1494067 3363335 := bstep (se 1 (by rfl) ⟨2522501, by rfl⟩ : syracuseStep 3363335 = 5045003) B5045003
theorem B1495643 : Blo 1494067 1495643 := bstep (se 1 (by rfl) ⟨1121732, by rfl⟩ : syracuseStep 1495643 = 2243465) B2243465
theorem B2241257 : Blo 1494067 2241257 := bstep (se 2 (by rfl) ⟨840471, by rfl⟩ : syracuseStep 2241257 = 1680943) B1680943
theorem B8516339 : Blo 1494067 8516339 := bstep (se 1 (by rfl) ⟨6387254, by rfl⟩ : syracuseStep 8516339 = 12774509) B12774509
theorem B1495839 : Blo 1494067 1495839 := bstep (se 1 (by rfl) ⟨1121879, by rfl⟩ : syracuseStep 1495839 = 2243759) B2243759
theorem B7566209 : Blo 1494067 7566209 := bstep (se 2 (by rfl) ⟨2837328, by rfl⟩ : syracuseStep 7566209 = 5674657) B5674657
theorem B189117341 : Blo 1494067 189117341 := bstep (se 3 (by rfl) ⟨35459501, by rfl⟩ : syracuseStep 189117341 = 70919003) B70919003
theorem B1495999 : Blo 1494067 1495999 := bstep (se 1 (by rfl) ⟨1121999, by rfl⟩ : syracuseStep 1495999 = 2243999) B2243999
theorem B14365673 : Blo 1494067 14365673 := bstep (se 2 (by rfl) ⟨5387127, by rfl⟩ : syracuseStep 14365673 = 10774255) B10774255
theorem B2839835 : Blo 1494067 2839835 := bstep (se 1 (by rfl) ⟨2129876, by rfl⟩ : syracuseStep 2839835 = 4259753) B4259753
theorem B15545675 : Blo 1494067 15545675 := bstep (se 1 (by rfl) ⟨11659256, by rfl⟩ : syracuseStep 15545675 = 23318513) B23318513
theorem B5043707 : Blo 1494067 5043707 := bstep (se 1 (by rfl) ⟨3782780, by rfl⟩ : syracuseStep 5043707 = 7565561) B7565561
theorem B13645361 : Blo 1494067 13645361 := bstep (se 2 (by rfl) ⟨5117010, by rfl⟩ : syracuseStep 13645361 = 10234021) B10234021
theorem B7567019 : Blo 1494067 7567019 := bstep (se 1 (by rfl) ⟨5675264, by rfl⟩ : syracuseStep 7567019 = 11350529) B11350529
theorem B6387407 : Blo 1494067 6387407 := bstep (se 1 (by rfl) ⟨4790555, by rfl⟩ : syracuseStep 6387407 = 9581111) B9581111
theorem B2242343 : Blo 1494067 2242343 := bstep (se 1 (by rfl) ⟨1681757, by rfl⟩ : syracuseStep 2242343 = 3363515) B3363515
theorem B48527207 : Blo 1494067 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B2242415 : Blo 1494067 2242415 := bstep (se 1 (by rfl) ⟨1681811, by rfl⟩ : syracuseStep 2242415 = 3363623) B3363623
theorem B6060359 : Blo 1494067 6060359 := bstep (se 1 (by rfl) ⟨4545269, by rfl⟩ : syracuseStep 6060359 = 9090539) B9090539
theorem B6388091 : Blo 1494067 6388091 := bstep (se 1 (by rfl) ⟨4791068, by rfl⟩ : syracuseStep 6388091 = 9582137) B9582137
theorem B3783145 : Blo 1494067 3783145 := bstep (se 2 (by rfl) ⟨1418679, by rfl⟩ : syracuseStep 3783145 = 2837359) B2837359
theorem B2243183 : Blo 1494067 2243183 := bstep (se 1 (by rfl) ⟨1682387, by rfl⟩ : syracuseStep 2243183 = 3364775) B3364775
theorem B14375819 : Blo 1494067 14375819 := bstep (se 1 (by rfl) ⟨10781864, by rfl⟩ : syracuseStep 14375819 = 21563729) B21563729
theorem B2694313 : Blo 1494067 2694313 := bstep (se 2 (by rfl) ⟨1010367, by rfl⟩ : syracuseStep 2694313 = 2020735) B2020735
theorem B15334609 : Blo 1494067 15334609 := bstep (se 2 (by rfl) ⟨5750478, by rfl⟩ : syracuseStep 15334609 = 11500957) B11500957
theorem B2129375 : Blo 1494067 2129375 := bstep (se 1 (by rfl) ⟨1597031, by rfl⟩ : syracuseStep 2129375 = 3194063) B3194063
theorem B3194473 : Blo 1494067 3194473 := bstep (se 2 (by rfl) ⟨1197927, by rfl⟩ : syracuseStep 3194473 = 2395855) B2395855
theorem B5111455 : Blo 1494067 5111455 := bstep (se 1 (by rfl) ⟨3833591, by rfl⟩ : syracuseStep 5111455 = 7667183) B7667183
theorem B14360287 : Blo 1494067 14360287 := bstep (se 1 (by rfl) ⟨10770215, by rfl⟩ : syracuseStep 14360287 = 21540431) B21540431
theorem B29523689 : Blo 1494067 29523689 := bstep (se 2 (by rfl) ⟨11071383, by rfl⟩ : syracuseStep 29523689 = 22142767) B22142767
theorem B6389867 : Blo 1494067 6389867 := bstep (se 1 (by rfl) ⟨4792400, by rfl⟩ : syracuseStep 6389867 = 9584801) B9584801
theorem B1892479 : Blo 1494067 1892479 := bstep (se 1 (by rfl) ⟨1419359, by rfl⟩ : syracuseStep 1892479 = 2838719) B2838719
theorem B5677559 : Blo 1494067 5677559 := bstep (se 1 (by rfl) ⟨4258169, by rfl⟩ : syracuseStep 5677559 = 8516339) B8516339
theorem B9577115 : Blo 1494067 9577115 := bstep (se 1 (by rfl) ⟨7182836, by rfl⟩ : syracuseStep 9577115 = 14365673) B14365673
theorem B1893223 : Blo 1494067 1893223 := bstep (se 1 (by rfl) ⟨1419917, by rfl⟩ : syracuseStep 1893223 = 2839835) B2839835
theorem B14369669 : Blo 1494067 14369669 := bstep (se 4 (by rfl) ⟨1347156, by rfl⟩ : syracuseStep 14369669 = 2694313) B2694313
theorem B10363783 : Blo 1494067 10363783 := bstep (se 1 (by rfl) ⟨7772837, by rfl⟩ : syracuseStep 10363783 = 15545675) B15545675
theorem B21562523 : Blo 1494067 21562523 := bstep (se 1 (by rfl) ⟨16171892, by rfl⟩ : syracuseStep 21562523 = 32343785) B32343785
theorem B5047487 : Blo 1494067 5047487 := bstep (se 1 (by rfl) ⟨3785615, by rfl⟩ : syracuseStep 5047487 = 7571231) B7571231
theorem B32351471 : Blo 1494067 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B5678333 : Blo 1494067 5678333 := bstep (se 3 (by rfl) ⟨1064687, by rfl⟩ : syracuseStep 5678333 = 2129375) B2129375
theorem B1820111 : Blo 1494067 1820111 := bstep (se 1 (by rfl) ⟨1365083, by rfl⟩ : syracuseStep 1820111 = 2730167) B2730167
theorem B4040239 : Blo 1494067 4040239 := bstep (se 1 (by rfl) ⟨3030179, by rfl⟩ : syracuseStep 4040239 = 6060359) B6060359
theorem B18188171 : Blo 1494067 18188171 := bstep (se 1 (by rfl) ⟨13641128, by rfl⟩ : syracuseStep 18188171 = 27282257) B27282257
theorem B19147049 : Blo 1494067 19147049 := bstep (se 2 (by rfl) ⟨7180143, by rfl⟩ : syracuseStep 19147049 = 14360287) B14360287
theorem B6818431 : Blo 1494067 6818431 := bstep (se 1 (by rfl) ⟨5113823, by rfl⟩ : syracuseStep 6818431 = 10227647) B10227647
theorem B1494171 : Blo 1494067 1494171 := bstep (se 1 (by rfl) ⟨1120628, by rfl⟩ : syracuseStep 1494171 = 2241257) B2241257
theorem B126078227 : Blo 1494067 126078227 := bstep (se 1 (by rfl) ⟨94558670, by rfl⟩ : syracuseStep 126078227 = 189117341) B189117341
theorem B3362471 : Blo 1494067 3362471 := bstep (se 1 (by rfl) ⟨2521853, by rfl⟩ : syracuseStep 3362471 = 5043707) B5043707
theorem B9096907 : Blo 1494067 9096907 := bstep (se 1 (by rfl) ⟨6822680, by rfl⟩ : syracuseStep 9096907 = 13645361) B13645361
theorem B1494895 : Blo 1494067 1494895 := bstep (se 1 (by rfl) ⟨1121171, by rfl⟩ : syracuseStep 1494895 = 2242343) B2242343
theorem B1494943 : Blo 1494067 1494943 := bstep (se 1 (by rfl) ⟨1121207, by rfl⟩ : syracuseStep 1494943 = 2242415) B2242415
theorem B8515631 : Blo 1494067 8515631 := bstep (se 1 (by rfl) ⟨6386723, by rfl⟩ : syracuseStep 8515631 = 12773447) B12773447
theorem B13643873 : Blo 1494067 13643873 := bstep (se 2 (by rfl) ⟨5116452, by rfl⟩ : syracuseStep 13643873 = 10232905) B10232905
theorem B1495455 : Blo 1494067 1495455 := bstep (se 1 (by rfl) ⟨1121591, by rfl⟩ : syracuseStep 1495455 = 2243183) B2243183
theorem B77689691 : Blo 1494067 77689691 := bstep (se 1 (by rfl) ⟨58267268, by rfl⟩ : syracuseStep 77689691 = 116534537) B116534537
theorem B2241383 : Blo 1494067 2241383 := bstep (se 1 (by rfl) ⟨1681037, by rfl⟩ : syracuseStep 2241383 = 3362075) B3362075
theorem B5043167 : Blo 1494067 5043167 := bstep (se 1 (by rfl) ⟨3782375, by rfl⟩ : syracuseStep 5043167 = 7564751) B7564751
theorem B6820969 : Blo 1494067 6820969 := bstep (se 2 (by rfl) ⟨2557863, by rfl⟩ : syracuseStep 6820969 = 5115727) B5115727
theorem B19682459 : Blo 1494067 19682459 := bstep (se 1 (by rfl) ⟨14761844, by rfl⟩ : syracuseStep 19682459 = 29523689) B29523689
theorem B2241695 : Blo 1494067 2241695 := bstep (se 1 (by rfl) ⟨1681271, by rfl⟩ : syracuseStep 2241695 = 3362543) B3362543
theorem B3364217 : Blo 1494067 3364217 := bstep (se 2 (by rfl) ⟨1261581, by rfl⟩ : syracuseStep 3364217 = 2523163) B2523163
theorem B2242223 : Blo 1494067 2242223 := bstep (se 1 (by rfl) ⟨1681667, by rfl⟩ : syracuseStep 2242223 = 3363335) B3363335
theorem B5044139 : Blo 1494067 5044139 := bstep (se 1 (by rfl) ⟨3783104, by rfl⟩ : syracuseStep 5044139 = 7566209) B7566209
theorem B5044193 : Blo 1494067 5044193 := bstep (se 2 (by rfl) ⟨1891572, by rfl⟩ : syracuseStep 5044193 = 3783145) B3783145
theorem B4987067 : Blo 1494067 4987067 := bstep (se 1 (by rfl) ⟨3740300, by rfl⟩ : syracuseStep 4987067 = 7480601) B7480601
theorem B5044679 : Blo 1494067 5044679 := bstep (se 1 (by rfl) ⟨3783509, by rfl⟩ : syracuseStep 5044679 = 7567019) B7567019
theorem B4258271 : Blo 1494067 4258271 := bstep (se 1 (by rfl) ⟨3193703, by rfl⟩ : syracuseStep 4258271 = 6387407) B6387407
theorem B9345527 : Blo 1494067 9345527 := bstep (se 1 (by rfl) ⟨7009145, by rfl⟩ : syracuseStep 9345527 = 14018291) B14018291
theorem B5536253 : Blo 1494067 5536253 := bstep (se 3 (by rfl) ⟨1038047, by rfl⟩ : syracuseStep 5536253 = 2076095) B2076095
theorem B4258727 : Blo 1494067 4258727 := bstep (se 1 (by rfl) ⟨3194045, by rfl⟩ : syracuseStep 4258727 = 6388091) B6388091
theorem B20446145 : Blo 1494067 20446145 := bstep (se 2 (by rfl) ⟨7667304, by rfl⟩ : syracuseStep 20446145 = 15334609) B15334609
theorem B9583879 : Blo 1494067 9583879 := bstep (se 1 (by rfl) ⟨7187909, by rfl⟩ : syracuseStep 9583879 = 14375819) B14375819
theorem B4259297 : Blo 1494067 4259297 := bstep (se 2 (by rfl) ⟨1597236, by rfl⟩ : syracuseStep 4259297 = 3194473) B3194473
theorem B6815273 : Blo 1494067 6815273 := bstep (se 2 (by rfl) ⟨2555727, by rfl⟩ : syracuseStep 6815273 = 5111455) B5111455
theorem B5677087 : Blo 1494067 5677087 := bstep (se 1 (by rfl) ⟨4257815, by rfl⟩ : syracuseStep 5677087 = 8515631) B8515631
theorem B2523305 : Blo 1494067 2523305 := bstep (se 2 (by rfl) ⟨946239, by rfl⟩ : syracuseStep 2523305 = 1892479) B1892479
theorem B17039645 : Blo 1494067 17039645 := bstep (se 3 (by rfl) ⟨3194933, by rfl⟩ : syracuseStep 17039645 = 6389867) B6389867
theorem B3785039 : Blo 1494067 3785039 := bstep (se 1 (by rfl) ⟨2838779, by rfl⟩ : syracuseStep 3785039 = 5677559) B5677559
theorem B3785555 : Blo 1494067 3785555 := bstep (se 1 (by rfl) ⟨2839166, by rfl⟩ : syracuseStep 3785555 = 5678333) B5678333
theorem B2524297 : Blo 1494067 2524297 := bstep (se 2 (by rfl) ⟨946611, by rfl⟩ : syracuseStep 2524297 = 1893223) B1893223
theorem B11355389 : Blo 1494067 11355389 := bstep (se 3 (by rfl) ⟨2129135, by rfl⟩ : syracuseStep 11355389 = 4258271) B4258271
theorem B12125447 : Blo 1494067 12125447 := bstep (se 1 (by rfl) ⟨9094085, by rfl⟩ : syracuseStep 12125447 = 18188171) B18188171
theorem B9094625 : Blo 1494067 9094625 := bstep (se 2 (by rfl) ⟨3410484, by rfl⟩ : syracuseStep 9094625 = 6820969) B6820969
theorem B12764699 : Blo 1494067 12764699 := bstep (se 1 (by rfl) ⟨9573524, by rfl⟩ : syracuseStep 12764699 = 19147049) B19147049
theorem B84052151 : Blo 1494067 84052151 := bstep (se 1 (by rfl) ⟨63039113, by rfl⟩ : syracuseStep 84052151 = 126078227) B126078227
theorem B9095915 : Blo 1494067 9095915 := bstep (se 1 (by rfl) ⟨6821936, by rfl⟩ : syracuseStep 9095915 = 13643873) B13643873
theorem B6384743 : Blo 1494067 6384743 := bstep (se 1 (by rfl) ⟨4788557, by rfl⟩ : syracuseStep 6384743 = 9577115) B9577115
theorem B51793127 : Blo 1494067 51793127 := bstep (se 1 (by rfl) ⟨38844845, by rfl⟩ : syracuseStep 51793127 = 77689691) B77689691
theorem B1494255 : Blo 1494067 1494255 := bstep (se 1 (by rfl) ⟨1120691, by rfl⟩ : syracuseStep 1494255 = 2241383) B2241383
theorem B9579779 : Blo 1494067 9579779 := bstep (se 1 (by rfl) ⟨7184834, by rfl⟩ : syracuseStep 9579779 = 14369669) B14369669
theorem B3362111 : Blo 1494067 3362111 := bstep (se 1 (by rfl) ⟨2521583, by rfl⟩ : syracuseStep 3362111 = 5043167) B5043167
theorem B1494463 : Blo 1494067 1494463 := bstep (se 1 (by rfl) ⟨1120847, by rfl⟩ : syracuseStep 1494463 = 2241695) B2241695
theorem B1494815 : Blo 1494067 1494815 := bstep (se 1 (by rfl) ⟨1121111, by rfl⟩ : syracuseStep 1494815 = 2242223) B2242223
theorem B4853629 : Blo 1494067 4853629 := bstep (se 3 (by rfl) ⟨910055, by rfl⟩ : syracuseStep 4853629 = 1820111) B1820111
theorem B3362759 : Blo 1494067 3362759 := bstep (se 1 (by rfl) ⟨2522069, by rfl⟩ : syracuseStep 3362759 = 5044139) B5044139
theorem B3362795 : Blo 1494067 3362795 := bstep (se 1 (by rfl) ⟨2522096, by rfl⟩ : syracuseStep 3362795 = 5044193) B5044193
theorem B18174061 : Blo 1494067 18174061 := bstep (se 3 (by rfl) ⟨3407636, by rfl⟩ : syracuseStep 18174061 = 6815273) B6815273
theorem B3363119 : Blo 1494067 3363119 := bstep (se 1 (by rfl) ⟨2522339, by rfl⟩ : syracuseStep 3363119 = 5044679) B5044679
theorem B6230351 : Blo 1494067 6230351 := bstep (se 1 (by rfl) ⟨4672763, by rfl⟩ : syracuseStep 6230351 = 9345527) B9345527
theorem B3690835 : Blo 1494067 3690835 := bstep (se 1 (by rfl) ⟨2768126, by rfl⟩ : syracuseStep 3690835 = 5536253) B5536253
theorem B2839151 : Blo 1494067 2839151 := bstep (se 1 (by rfl) ⟨2129363, by rfl⟩ : syracuseStep 2839151 = 4258727) B4258727
theorem B53195381 : Blo 1494067 53195381 := bstep (se 5 (by rfl) ⟨2493533, by rfl⟩ : syracuseStep 53195381 = 4987067) B4987067
theorem B5386985 : Blo 1494067 5386985 := bstep (se 2 (by rfl) ⟨2020119, by rfl⟩ : syracuseStep 5386985 = 4040239) B4040239
theorem B12129209 : Blo 1494067 12129209 := bstep (se 2 (by rfl) ⟨4548453, by rfl⟩ : syracuseStep 12129209 = 9096907) B9096907
theorem B2839531 : Blo 1494067 2839531 := bstep (se 1 (by rfl) ⟨2129648, by rfl⟩ : syracuseStep 2839531 = 4259297) B4259297
theorem B2241647 : Blo 1494067 2241647 := bstep (se 1 (by rfl) ⟨1681235, by rfl⟩ : syracuseStep 2241647 = 3362471) B3362471
theorem B13121639 : Blo 1494067 13121639 := bstep (se 1 (by rfl) ⟨9841229, by rfl⟩ : syracuseStep 13121639 = 19682459) B19682459
theorem B14375015 : Blo 1494067 14375015 := bstep (se 1 (by rfl) ⟨10781261, by rfl⟩ : syracuseStep 14375015 = 21562523) B21562523
theorem B3364991 : Blo 1494067 3364991 := bstep (se 1 (by rfl) ⟨2523743, by rfl⟩ : syracuseStep 3364991 = 5047487) B5047487
theorem B21567647 : Blo 1494067 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B9091241 : Blo 1494067 9091241 := bstep (se 2 (by rfl) ⟨3409215, by rfl⟩ : syracuseStep 9091241 = 6818431) B6818431
theorem B2242811 : Blo 1494067 2242811 := bstep (se 1 (by rfl) ⟨1682108, by rfl⟩ : syracuseStep 2242811 = 3364217) B3364217
theorem B13818377 : Blo 1494067 13818377 := bstep (se 2 (by rfl) ⟨5181891, by rfl⟩ : syracuseStep 13818377 = 10363783) B10363783
theorem B12778505 : Blo 1494067 12778505 := bstep (se 2 (by rfl) ⟨4791939, by rfl⟩ : syracuseStep 12778505 = 9583879) B9583879
theorem B13630763 : Blo 1494067 13630763 := bstep (se 1 (by rfl) ⟨10223072, by rfl⟩ : syracuseStep 13630763 = 20446145) B20446145
theorem B7569449 : Blo 1494067 7569449 := bstep (se 2 (by rfl) ⟨2838543, by rfl⟩ : syracuseStep 7569449 = 5677087) B5677087
theorem B24232081 : Blo 1494067 24232081 := bstep (se 2 (by rfl) ⟨9087030, by rfl⟩ : syracuseStep 24232081 = 18174061) B18174061
theorem B2523359 : Blo 1494067 2523359 := bstep (se 1 (by rfl) ⟨1892519, by rfl⟩ : syracuseStep 2523359 = 3785039) B3785039
theorem B4153567 : Blo 1494067 4153567 := bstep (se 1 (by rfl) ⟨3115175, by rfl⟩ : syracuseStep 4153567 = 6230351) B6230351
theorem B35463587 : Blo 1494067 35463587 := bstep (se 1 (by rfl) ⟨26597690, by rfl⟩ : syracuseStep 35463587 = 53195381) B53195381
theorem B2523703 : Blo 1494067 2523703 := bstep (se 1 (by rfl) ⟨1892777, by rfl⟩ : syracuseStep 2523703 = 3785555) B3785555
theorem B8086139 : Blo 1494067 8086139 := bstep (se 1 (by rfl) ⟨6064604, by rfl⟩ : syracuseStep 8086139 = 12129209) B12129209
theorem B7570259 : Blo 1494067 7570259 := bstep (se 1 (by rfl) ⟨5677694, by rfl⟩ : syracuseStep 7570259 = 11355389) B11355389
theorem B6063083 : Blo 1494067 6063083 := bstep (se 1 (by rfl) ⟨4547312, by rfl⟩ : syracuseStep 6063083 = 9094625) B9094625
theorem B3786041 : Blo 1494067 3786041 := bstep (se 2 (by rfl) ⟨1419765, by rfl⟩ : syracuseStep 3786041 = 2839531) B2839531
theorem B36849005 : Blo 1494067 36849005 := bstep (se 3 (by rfl) ⟨6909188, by rfl⟩ : syracuseStep 36849005 = 13818377) B13818377
theorem B56034767 : Blo 1494067 56034767 := bstep (se 1 (by rfl) ⟨42026075, by rfl⟩ : syracuseStep 56034767 = 84052151) B84052151
theorem B7571069 : Blo 1494067 7571069 := bstep (se 3 (by rfl) ⟨1419575, by rfl⟩ : syracuseStep 7571069 = 2839151) B2839151
theorem B6063943 : Blo 1494067 6063943 := bstep (se 1 (by rfl) ⟨4547957, by rfl⟩ : syracuseStep 6063943 = 9095915) B9095915
theorem B9087175 : Blo 1494067 9087175 := bstep (se 1 (by rfl) ⟨6815381, by rfl⟩ : syracuseStep 9087175 = 13630763) B13630763
theorem B1682203 : Blo 1494067 1682203 := bstep (se 1 (by rfl) ⟨1261652, by rfl⟩ : syracuseStep 1682203 = 2523305) B2523305
theorem B3591323 : Blo 1494067 3591323 := bstep (se 1 (by rfl) ⟨2693492, by rfl⟩ : syracuseStep 3591323 = 5386985) B5386985
theorem B1494431 : Blo 1494067 1494431 := bstep (se 1 (by rfl) ⟨1120823, by rfl⟩ : syracuseStep 1494431 = 2241647) B2241647
theorem B1495207 : Blo 1494067 1495207 := bstep (se 1 (by rfl) ⟨1121405, by rfl⟩ : syracuseStep 1495207 = 2242811) B2242811
theorem B4256495 : Blo 1494067 4256495 := bstep (se 1 (by rfl) ⟨3192371, by rfl⟩ : syracuseStep 4256495 = 6384743) B6384743
theorem B6386519 : Blo 1494067 6386519 := bstep (se 1 (by rfl) ⟨4789889, by rfl⟩ : syracuseStep 6386519 = 9579779) B9579779
theorem B2241407 : Blo 1494067 2241407 := bstep (se 1 (by rfl) ⟨1681055, by rfl⟩ : syracuseStep 2241407 = 3362111) B3362111
theorem B2241839 : Blo 1494067 2241839 := bstep (se 1 (by rfl) ⟨1681379, by rfl⟩ : syracuseStep 2241839 = 3362759) B3362759
theorem B2241863 : Blo 1494067 2241863 := bstep (se 1 (by rfl) ⟨1681397, by rfl⟩ : syracuseStep 2241863 = 3362795) B3362795
theorem B11359763 : Blo 1494067 11359763 := bstep (se 1 (by rfl) ⟨8519822, by rfl⟩ : syracuseStep 11359763 = 17039645) B17039645
theorem B2242079 : Blo 1494067 2242079 := bstep (se 1 (by rfl) ⟨1681559, by rfl⟩ : syracuseStep 2242079 = 3363119) B3363119
theorem B57513725 : Blo 1494067 57513725 := bstep (se 3 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 57513725 = 21567647) B21567647
theorem B8083631 : Blo 1494067 8083631 := bstep (se 1 (by rfl) ⟨6062723, by rfl⟩ : syracuseStep 8083631 = 12125447) B12125447
theorem B8509799 : Blo 1494067 8509799 := bstep (se 1 (by rfl) ⟨6382349, by rfl⟩ : syracuseStep 8509799 = 12764699) B12764699
theorem B8747759 : Blo 1494067 8747759 := bstep (se 1 (by rfl) ⟨6560819, by rfl⟩ : syracuseStep 8747759 = 13121639) B13121639
theorem B9583343 : Blo 1494067 9583343 := bstep (se 1 (by rfl) ⟨7187507, by rfl⟩ : syracuseStep 9583343 = 14375015) B14375015
theorem B2243327 : Blo 1494067 2243327 := bstep (se 1 (by rfl) ⟨1682495, by rfl⟩ : syracuseStep 2243327 = 3364991) B3364991
theorem B6060827 : Blo 1494067 6060827 := bstep (se 1 (by rfl) ⟨4545620, by rfl⟩ : syracuseStep 6060827 = 9091241) B9091241
theorem B3365729 : Blo 1494067 3365729 := bstep (se 2 (by rfl) ⟨1262148, by rfl⟩ : syracuseStep 3365729 = 2524297) B2524297
theorem B19684453 : Blo 1494067 19684453 := bstep (se 4 (by rfl) ⟨1845417, by rfl⟩ : syracuseStep 19684453 = 3690835) B3690835
theorem B8519003 : Blo 1494067 8519003 := bstep (se 1 (by rfl) ⟨6389252, by rfl⟩ : syracuseStep 8519003 = 12778505) B12778505
theorem B34528751 : Blo 1494067 34528751 := bstep (se 1 (by rfl) ⟨25896563, by rfl⟩ : syracuseStep 34528751 = 51793127) B51793127
theorem B6471505 : Blo 1494067 6471505 := bstep (se 2 (by rfl) ⟨2426814, by rfl⟩ : syracuseStep 6471505 = 4853629) B4853629
theorem B5046299 : Blo 1494067 5046299 := bstep (se 1 (by rfl) ⟨3784724, by rfl⟩ : syracuseStep 5046299 = 7569449) B7569449
theorem B32309441 : Blo 1494067 32309441 := bstep (se 2 (by rfl) ⟨12116040, by rfl⟩ : syracuseStep 32309441 = 24232081) B24232081
theorem B12116233 : Blo 1494067 12116233 := bstep (se 2 (by rfl) ⟨4543587, by rfl⟩ : syracuseStep 12116233 = 9087175) B9087175
theorem B5538089 : Blo 1494067 5538089 := bstep (se 2 (by rfl) ⟨2076783, by rfl⟩ : syracuseStep 5538089 = 4153567) B4153567
theorem B5390759 : Blo 1494067 5390759 := bstep (se 1 (by rfl) ⟨4043069, by rfl⟩ : syracuseStep 5390759 = 8086139) B8086139
theorem B5046839 : Blo 1494067 5046839 := bstep (se 1 (by rfl) ⟨3785129, by rfl⟩ : syracuseStep 5046839 = 7570259) B7570259
theorem B2524027 : Blo 1494067 2524027 := bstep (se 1 (by rfl) ⟨1893020, by rfl⟩ : syracuseStep 2524027 = 3786041) B3786041
theorem B37356511 : Blo 1494067 37356511 := bstep (se 1 (by rfl) ⟨28017383, by rfl⟩ : syracuseStep 37356511 = 56034767) B56034767
theorem B5047379 : Blo 1494067 5047379 := bstep (se 1 (by rfl) ⟨3785534, by rfl⟩ : syracuseStep 5047379 = 7571069) B7571069
theorem B4040551 : Blo 1494067 4040551 := bstep (se 1 (by rfl) ⟨3030413, by rfl⟩ : syracuseStep 4040551 = 6060827) B6060827
theorem B2394215 : Blo 1494067 2394215 := bstep (se 1 (by rfl) ⟨1795661, by rfl⟩ : syracuseStep 2394215 = 3591323) B3591323
theorem B5679335 : Blo 1494067 5679335 := bstep (se 1 (by rfl) ⟨4259501, by rfl⟩ : syracuseStep 5679335 = 8519003) B8519003
theorem B8628673 : Blo 1494067 8628673 := bstep (se 2 (by rfl) ⟨3235752, by rfl⟩ : syracuseStep 8628673 = 6471505) B6471505
theorem B1682239 : Blo 1494067 1682239 := bstep (se 1 (by rfl) ⟨1261679, by rfl⟩ : syracuseStep 1682239 = 2523359) B2523359
theorem B2837663 : Blo 1494067 2837663 := bstep (se 1 (by rfl) ⟨2128247, by rfl⟩ : syracuseStep 2837663 = 4256495) B4256495
theorem B1494271 : Blo 1494067 1494271 := bstep (se 1 (by rfl) ⟨1120703, by rfl⟩ : syracuseStep 1494271 = 2241407) B2241407
theorem B4042055 : Blo 1494067 4042055 := bstep (se 1 (by rfl) ⟨3031541, by rfl⟩ : syracuseStep 4042055 = 6063083) B6063083
theorem B1494559 : Blo 1494067 1494559 := bstep (se 1 (by rfl) ⟨1120919, by rfl⟩ : syracuseStep 1494559 = 2241839) B2241839
theorem B1494575 : Blo 1494067 1494575 := bstep (se 1 (by rfl) ⟨1120931, by rfl⟩ : syracuseStep 1494575 = 2241863) B2241863
theorem B7573175 : Blo 1494067 7573175 := bstep (se 1 (by rfl) ⟨5679881, by rfl⟩ : syracuseStep 7573175 = 11359763) B11359763
theorem B1494719 : Blo 1494067 1494719 := bstep (se 1 (by rfl) ⟨1121039, by rfl⟩ : syracuseStep 1494719 = 2242079) B2242079
theorem B38342483 : Blo 1494067 38342483 := bstep (se 1 (by rfl) ⟨28756862, by rfl⟩ : syracuseStep 38342483 = 57513725) B57513725
theorem B5673199 : Blo 1494067 5673199 := bstep (se 1 (by rfl) ⟨4254899, by rfl⟩ : syracuseStep 5673199 = 8509799) B8509799
theorem B378278261 : Blo 1494067 378278261 := bstep (se 5 (by rfl) ⟨17731793, by rfl⟩ : syracuseStep 378278261 = 35463587) B35463587
theorem B1495551 : Blo 1494067 1495551 := bstep (se 1 (by rfl) ⟨1121663, by rfl⟩ : syracuseStep 1495551 = 2243327) B2243327
theorem B4257679 : Blo 1494067 4257679 := bstep (se 1 (by rfl) ⟨3193259, by rfl⟩ : syracuseStep 4257679 = 6386519) B6386519
theorem B3364937 : Blo 1494067 3364937 := bstep (se 2 (by rfl) ⟨1261851, by rfl⟩ : syracuseStep 3364937 = 2523703) B2523703
theorem B24566003 : Blo 1494067 24566003 := bstep (se 1 (by rfl) ⟨18424502, by rfl⟩ : syracuseStep 24566003 = 36849005) B36849005
theorem B2242937 : Blo 1494067 2242937 := bstep (se 2 (by rfl) ⟨841101, by rfl⟩ : syracuseStep 2242937 = 1682203) B1682203
theorem B5389087 : Blo 1494067 5389087 := bstep (se 1 (by rfl) ⟨4041815, by rfl⟩ : syracuseStep 5389087 = 8083631) B8083631
theorem B26245937 : Blo 1494067 26245937 := bstep (se 2 (by rfl) ⟨9842226, by rfl⟩ : syracuseStep 26245937 = 19684453) B19684453
theorem B5831839 : Blo 1494067 5831839 := bstep (se 1 (by rfl) ⟨4373879, by rfl⟩ : syracuseStep 5831839 = 8747759) B8747759
theorem B6388895 : Blo 1494067 6388895 := bstep (se 1 (by rfl) ⟨4791671, by rfl⟩ : syracuseStep 6388895 = 9583343) B9583343
theorem B2243819 : Blo 1494067 2243819 := bstep (se 1 (by rfl) ⟨1682864, by rfl⟩ : syracuseStep 2243819 = 3365729) B3365729
theorem B23019167 : Blo 1494067 23019167 := bstep (se 1 (by rfl) ⟨17264375, by rfl⟩ : syracuseStep 23019167 = 34528751) B34528751
theorem B8085257 : Blo 1494067 8085257 := bstep (se 2 (by rfl) ⟨3031971, by rfl⟩ : syracuseStep 8085257 = 6063943) B6063943
theorem B16154977 : Blo 1494067 16154977 := bstep (se 2 (by rfl) ⟨6058116, by rfl⟩ : syracuseStep 16154977 = 12116233) B12116233
theorem B7185449 : Blo 1494067 7185449 := bstep (se 2 (by rfl) ⟨2694543, by rfl⟩ : syracuseStep 7185449 = 5389087) B5389087
theorem B49808681 : Blo 1494067 49808681 := bstep (se 2 (by rfl) ⟨18678255, by rfl⟩ : syracuseStep 49808681 = 37356511) B37356511
theorem B3786223 : Blo 1494067 3786223 := bstep (se 1 (by rfl) ⟨2839667, by rfl⟩ : syracuseStep 3786223 = 5679335) B5679335
theorem B16377335 : Blo 1494067 16377335 := bstep (se 1 (by rfl) ⟨12283001, by rfl⟩ : syracuseStep 16377335 = 24566003) B24566003
theorem B7775785 : Blo 1494067 7775785 := bstep (se 2 (by rfl) ⟨2915919, by rfl⟩ : syracuseStep 7775785 = 5831839) B5831839
theorem B15346111 : Blo 1494067 15346111 := bstep (se 1 (by rfl) ⟨11509583, by rfl⟩ : syracuseStep 15346111 = 23019167) B23019167
theorem B5048783 : Blo 1494067 5048783 := bstep (se 1 (by rfl) ⟨3786587, by rfl⟩ : syracuseStep 5048783 = 7573175) B7573175
theorem B25561655 : Blo 1494067 25561655 := bstep (se 1 (by rfl) ⟨19171241, by rfl⟩ : syracuseStep 25561655 = 38342483) B38342483
theorem B21539627 : Blo 1494067 21539627 := bstep (se 1 (by rfl) ⟨16154720, by rfl⟩ : syracuseStep 21539627 = 32309441) B32309441
theorem B252185507 : Blo 1494067 252185507 := bstep (se 1 (by rfl) ⟨189139130, by rfl⟩ : syracuseStep 252185507 = 378278261) B378278261
theorem B7564265 : Blo 1494067 7564265 := bstep (se 2 (by rfl) ⟨2836599, by rfl⟩ : syracuseStep 7564265 = 5673199) B5673199
theorem B11504897 : Blo 1494067 11504897 := bstep (se 2 (by rfl) ⟨4314336, by rfl⟩ : syracuseStep 11504897 = 8628673) B8628673
theorem B1495291 : Blo 1494067 1495291 := bstep (se 1 (by rfl) ⟨1121468, by rfl⟩ : syracuseStep 1495291 = 2242937) B2242937
theorem B1495879 : Blo 1494067 1495879 := bstep (se 1 (by rfl) ⟨1121909, by rfl⟩ : syracuseStep 1495879 = 2243819) B2243819
theorem B5387401 : Blo 1494067 5387401 := bstep (se 2 (by rfl) ⟨2020275, by rfl⟩ : syracuseStep 5387401 = 4040551) B4040551
theorem B3364199 : Blo 1494067 3364199 := bstep (se 1 (by rfl) ⟨2523149, by rfl⟩ : syracuseStep 3364199 = 5046299) B5046299
theorem B3364559 : Blo 1494067 3364559 := bstep (se 1 (by rfl) ⟨2523419, by rfl⟩ : syracuseStep 3364559 = 5046839) B5046839
theorem B3364919 : Blo 1494067 3364919 := bstep (se 1 (by rfl) ⟨2523689, by rfl⟩ : syracuseStep 3364919 = 5047379) B5047379
theorem B14768237 : Blo 1494067 14768237 := bstep (se 3 (by rfl) ⟨2769044, by rfl⟩ : syracuseStep 14768237 = 5538089) B5538089
theorem B2242985 : Blo 1494067 2242985 := bstep (se 2 (by rfl) ⟨841119, by rfl⟩ : syracuseStep 2242985 = 1682239) B1682239
theorem B14375357 : Blo 1494067 14375357 := bstep (se 3 (by rfl) ⟨2695379, by rfl⟩ : syracuseStep 14375357 = 5390759) B5390759
theorem B3365369 : Blo 1494067 3365369 := bstep (se 2 (by rfl) ⟨1262013, by rfl⟩ : syracuseStep 3365369 = 2524027) B2524027
theorem B2243291 : Blo 1494067 2243291 := bstep (se 1 (by rfl) ⟨1682468, by rfl⟩ : syracuseStep 2243291 = 3364937) B3364937
theorem B1596143 : Blo 1494067 1596143 := bstep (se 1 (by rfl) ⟨1197107, by rfl⟩ : syracuseStep 1596143 = 2394215) B2394215
theorem B17497291 : Blo 1494067 17497291 := bstep (se 1 (by rfl) ⟨13122968, by rfl⟩ : syracuseStep 17497291 = 26245937) B26245937
theorem B1891775 : Blo 1494067 1891775 := bstep (se 1 (by rfl) ⟨1418831, by rfl⟩ : syracuseStep 1891775 = 2837663) B2837663
theorem B4259263 : Blo 1494067 4259263 := bstep (se 1 (by rfl) ⟨3194447, by rfl⟩ : syracuseStep 4259263 = 6388895) B6388895
theorem B2694703 : Blo 1494067 2694703 := bstep (se 1 (by rfl) ⟨2021027, by rfl⟩ : syracuseStep 2694703 = 4042055) B4042055
theorem B5390171 : Blo 1494067 5390171 := bstep (se 1 (by rfl) ⟨4042628, by rfl⟩ : syracuseStep 5390171 = 8085257) B8085257
theorem B5676905 : Blo 1494067 5676905 := bstep (se 2 (by rfl) ⟨2128839, by rfl⟩ : syracuseStep 5676905 = 4257679) B4257679
theorem B19161197 : Blo 1494067 19161197 := bstep (se 3 (by rfl) ⟨3592724, by rfl⟩ : syracuseStep 19161197 = 7185449) B7185449
theorem B17041103 : Blo 1494067 17041103 := bstep (se 1 (by rfl) ⟨12780827, by rfl⟩ : syracuseStep 17041103 = 25561655) B25561655
theorem B5679017 : Blo 1494067 5679017 := bstep (se 2 (by rfl) ⟨2129631, by rfl⟩ : syracuseStep 5679017 = 4259263) B4259263
theorem B5048297 : Blo 1494067 5048297 := bstep (se 2 (by rfl) ⟨1893111, by rfl⟩ : syracuseStep 5048297 = 3786223) B3786223
theorem B7669931 : Blo 1494067 7669931 := bstep (se 1 (by rfl) ⟨5752448, by rfl⟩ : syracuseStep 7669931 = 11504897) B11504897
theorem B21539969 : Blo 1494067 21539969 := bstep (se 2 (by rfl) ⟨8077488, by rfl⟩ : syracuseStep 21539969 = 16154977) B16154977
theorem B28732805 : Blo 1494067 28732805 := bstep (se 4 (by rfl) ⟨2693700, by rfl⟩ : syracuseStep 28732805 = 5387401) B5387401
theorem B33205787 : Blo 1494067 33205787 := bstep (se 1 (by rfl) ⟨24904340, by rfl⟩ : syracuseStep 33205787 = 49808681) B49808681
theorem B1495323 : Blo 1494067 1495323 := bstep (se 1 (by rfl) ⟨1121492, by rfl⟩ : syracuseStep 1495323 = 2242985) B2242985
theorem B1495527 : Blo 1494067 1495527 := bstep (se 1 (by rfl) ⟨1121645, by rfl⟩ : syracuseStep 1495527 = 2243291) B2243291
theorem B4256381 : Blo 1494067 4256381 := bstep (se 3 (by rfl) ⟨798071, by rfl⟩ : syracuseStep 4256381 = 1596143) B1596143
theorem B5042843 : Blo 1494067 5042843 := bstep (se 1 (by rfl) ⟨3782132, by rfl⟩ : syracuseStep 5042843 = 7564265) B7564265
theorem B10367713 : Blo 1494067 10367713 := bstep (se 2 (by rfl) ⟨3887892, by rfl⟩ : syracuseStep 10367713 = 7775785) B7775785
theorem B3592937 : Blo 1494067 3592937 := bstep (se 2 (by rfl) ⟨1347351, by rfl⟩ : syracuseStep 3592937 = 2694703) B2694703
theorem B3593447 : Blo 1494067 3593447 := bstep (se 1 (by rfl) ⟨2695085, by rfl⟩ : syracuseStep 3593447 = 5390171) B5390171
theorem B20461481 : Blo 1494067 20461481 := bstep (se 2 (by rfl) ⟨7673055, by rfl⟩ : syracuseStep 20461481 = 15346111) B15346111
theorem B2242799 : Blo 1494067 2242799 := bstep (se 1 (by rfl) ⟨1682099, by rfl⟩ : syracuseStep 2242799 = 3364199) B3364199
theorem B10918223 : Blo 1494067 10918223 := bstep (se 1 (by rfl) ⟨8188667, by rfl⟩ : syracuseStep 10918223 = 16377335) B16377335
theorem B2243039 : Blo 1494067 2243039 := bstep (se 1 (by rfl) ⟨1682279, by rfl⟩ : syracuseStep 2243039 = 3364559) B3364559
theorem B5044733 : Blo 1494067 5044733 := bstep (se 3 (by rfl) ⟨945887, by rfl⟩ : syracuseStep 5044733 = 1891775) B1891775
theorem B2243279 : Blo 1494067 2243279 := bstep (se 1 (by rfl) ⟨1682459, by rfl⟩ : syracuseStep 2243279 = 3364919) B3364919
theorem B9845491 : Blo 1494067 9845491 := bstep (se 1 (by rfl) ⟨7384118, by rfl⟩ : syracuseStep 9845491 = 14768237) B14768237
theorem B23329721 : Blo 1494067 23329721 := bstep (se 2 (by rfl) ⟨8748645, by rfl⟩ : syracuseStep 23329721 = 17497291) B17497291
theorem B9583571 : Blo 1494067 9583571 := bstep (se 1 (by rfl) ⟨7187678, by rfl⟩ : syracuseStep 9583571 = 14375357) B14375357
theorem B3365855 : Blo 1494067 3365855 := bstep (se 1 (by rfl) ⟨2524391, by rfl⟩ : syracuseStep 3365855 = 5048783) B5048783
theorem B2243579 : Blo 1494067 2243579 := bstep (se 1 (by rfl) ⟨1682684, by rfl⟩ : syracuseStep 2243579 = 3365369) B3365369
theorem B14359751 : Blo 1494067 14359751 := bstep (se 1 (by rfl) ⟨10769813, by rfl⟩ : syracuseStep 14359751 = 21539627) B21539627
theorem B168123671 : Blo 1494067 168123671 := bstep (se 1 (by rfl) ⟨126092753, by rfl⟩ : syracuseStep 168123671 = 252185507) B252185507
theorem B3784603 : Blo 1494067 3784603 := bstep (se 1 (by rfl) ⟨2838452, by rfl⟩ : syracuseStep 3784603 = 5676905) B5676905
theorem B13640987 : Blo 1494067 13640987 := bstep (se 1 (by rfl) ⟨10230740, by rfl⟩ : syracuseStep 13640987 = 20461481) B20461481
theorem B3786011 : Blo 1494067 3786011 := bstep (se 1 (by rfl) ⟨2839508, by rfl⟩ : syracuseStep 3786011 = 5679017) B5679017
theorem B19155203 : Blo 1494067 19155203 := bstep (se 1 (by rfl) ⟨14366402, by rfl⟩ : syracuseStep 19155203 = 28732805) B28732805
theorem B22137191 : Blo 1494067 22137191 := bstep (se 1 (by rfl) ⟨16602893, by rfl⟩ : syracuseStep 22137191 = 33205787) B33205787
theorem B12774131 : Blo 1494067 12774131 := bstep (se 1 (by rfl) ⟨9580598, by rfl⟩ : syracuseStep 12774131 = 19161197) B19161197
theorem B2837587 : Blo 1494067 2837587 := bstep (se 1 (by rfl) ⟨2128190, by rfl⟩ : syracuseStep 2837587 = 4256381) B4256381
theorem B3361895 : Blo 1494067 3361895 := bstep (se 1 (by rfl) ⟨2521421, by rfl⟩ : syracuseStep 3361895 = 5042843) B5042843
theorem B2395631 : Blo 1494067 2395631 := bstep (se 1 (by rfl) ⟨1796723, by rfl⟩ : syracuseStep 2395631 = 3593447) B3593447
theorem B13823617 : Blo 1494067 13823617 := bstep (se 2 (by rfl) ⟨5183856, by rfl⟩ : syracuseStep 13823617 = 10367713) B10367713
theorem B13127321 : Blo 1494067 13127321 := bstep (se 2 (by rfl) ⟨4922745, by rfl⟩ : syracuseStep 13127321 = 9845491) B9845491
theorem B1495199 : Blo 1494067 1495199 := bstep (se 1 (by rfl) ⟨1121399, by rfl⟩ : syracuseStep 1495199 = 2242799) B2242799
theorem B7278815 : Blo 1494067 7278815 := bstep (se 1 (by rfl) ⟨5459111, by rfl⟩ : syracuseStep 7278815 = 10918223) B10918223
theorem B1495359 : Blo 1494067 1495359 := bstep (se 1 (by rfl) ⟨1121519, by rfl⟩ : syracuseStep 1495359 = 2243039) B2243039
theorem B3363155 : Blo 1494067 3363155 := bstep (se 1 (by rfl) ⟨2522366, by rfl⟩ : syracuseStep 3363155 = 5044733) B5044733
theorem B1495519 : Blo 1494067 1495519 := bstep (se 1 (by rfl) ⟨1121639, by rfl⟩ : syracuseStep 1495519 = 2243279) B2243279
theorem B9581165 : Blo 1494067 9581165 := bstep (se 3 (by rfl) ⟨1796468, by rfl⟩ : syracuseStep 9581165 = 3592937) B3592937
theorem B15553147 : Blo 1494067 15553147 := bstep (se 1 (by rfl) ⟨11664860, by rfl⟩ : syracuseStep 15553147 = 23329721) B23329721
theorem B1495719 : Blo 1494067 1495719 := bstep (se 1 (by rfl) ⟨1121789, by rfl⟩ : syracuseStep 1495719 = 2243579) B2243579
theorem B9573167 : Blo 1494067 9573167 := bstep (se 1 (by rfl) ⟨7179875, by rfl⟩ : syracuseStep 9573167 = 14359751) B14359751
theorem B20453149 : Blo 1494067 20453149 := bstep (se 3 (by rfl) ⟨3834965, by rfl⟩ : syracuseStep 20453149 = 7669931) B7669931
theorem B11360735 : Blo 1494067 11360735 := bstep (se 1 (by rfl) ⟨8520551, by rfl⟩ : syracuseStep 11360735 = 17041103) B17041103
theorem B3365531 : Blo 1494067 3365531 := bstep (se 1 (by rfl) ⟨2524148, by rfl⟩ : syracuseStep 3365531 = 5048297) B5048297
theorem B6389047 : Blo 1494067 6389047 := bstep (se 1 (by rfl) ⟨4791785, by rfl⟩ : syracuseStep 6389047 = 9583571) B9583571
theorem B2243903 : Blo 1494067 2243903 := bstep (se 1 (by rfl) ⟨1682927, by rfl⟩ : syracuseStep 2243903 = 3365855) B3365855
theorem B14359979 : Blo 1494067 14359979 := bstep (se 1 (by rfl) ⟨10769984, by rfl⟩ : syracuseStep 14359979 = 21539969) B21539969
theorem B112082447 : Blo 1494067 112082447 := bstep (se 1 (by rfl) ⟨84061835, by rfl⟩ : syracuseStep 112082447 = 168123671) B168123671
theorem B5046137 : Blo 1494067 5046137 := bstep (se 2 (by rfl) ⟨1892301, by rfl⟩ : syracuseStep 5046137 = 3784603) B3784603
theorem B6382111 : Blo 1494067 6382111 := bstep (se 1 (by rfl) ⟨4786583, by rfl⟩ : syracuseStep 6382111 = 9573167) B9573167
theorem B9093991 : Blo 1494067 9093991 := bstep (se 1 (by rfl) ⟨6820493, by rfl⟩ : syracuseStep 9093991 = 13640987) B13640987
theorem B2524007 : Blo 1494067 2524007 := bstep (se 1 (by rfl) ⟨1893005, by rfl⟩ : syracuseStep 2524007 = 3786011) B3786011
theorem B74721631 : Blo 1494067 74721631 := bstep (se 1 (by rfl) ⟨56041223, by rfl⟩ : syracuseStep 74721631 = 112082447) B112082447
theorem B8751547 : Blo 1494067 8751547 := bstep (se 1 (by rfl) ⟨6563660, by rfl⟩ : syracuseStep 8751547 = 13127321) B13127321
theorem B4852543 : Blo 1494067 4852543 := bstep (se 1 (by rfl) ⟨3639407, by rfl⟩ : syracuseStep 4852543 = 7278815) B7278815
theorem B20737529 : Blo 1494067 20737529 := bstep (se 2 (by rfl) ⟨7776573, by rfl⟩ : syracuseStep 20737529 = 15553147) B15553147
theorem B14758127 : Blo 1494067 14758127 := bstep (se 1 (by rfl) ⟨11068595, by rfl⟩ : syracuseStep 14758127 = 22137191) B22137191
theorem B7573823 : Blo 1494067 7573823 := bstep (se 1 (by rfl) ⟨5680367, by rfl⟩ : syracuseStep 7573823 = 11360735) B11360735
theorem B8516087 : Blo 1494067 8516087 := bstep (se 1 (by rfl) ⟨6387065, by rfl⟩ : syracuseStep 8516087 = 12774131) B12774131
theorem B2241263 : Blo 1494067 2241263 := bstep (se 1 (by rfl) ⟨1680947, by rfl⟩ : syracuseStep 2241263 = 3361895) B3361895
theorem B1495935 : Blo 1494067 1495935 := bstep (se 1 (by rfl) ⟨1121951, by rfl⟩ : syracuseStep 1495935 = 2243903) B2243903
theorem B9573319 : Blo 1494067 9573319 := bstep (se 1 (by rfl) ⟨7179989, by rfl⟩ : syracuseStep 9573319 = 14359979) B14359979
theorem B3364091 : Blo 1494067 3364091 := bstep (se 1 (by rfl) ⟨2523068, by rfl⟩ : syracuseStep 3364091 = 5046137) B5046137
theorem B2242103 : Blo 1494067 2242103 := bstep (se 1 (by rfl) ⟨1681577, by rfl⟩ : syracuseStep 2242103 = 3363155) B3363155
theorem B6387443 : Blo 1494067 6387443 := bstep (se 1 (by rfl) ⟨4790582, by rfl⟩ : syracuseStep 6387443 = 9581165) B9581165
theorem B3783449 : Blo 1494067 3783449 := bstep (se 2 (by rfl) ⟨1418793, by rfl⟩ : syracuseStep 3783449 = 2837587) B2837587
theorem B12770135 : Blo 1494067 12770135 := bstep (se 1 (by rfl) ⟨9577601, by rfl⟩ : syracuseStep 12770135 = 19155203) B19155203
theorem B8518729 : Blo 1494067 8518729 := bstep (se 2 (by rfl) ⟨3194523, by rfl⟩ : syracuseStep 8518729 = 6389047) B6389047
theorem B2243687 : Blo 1494067 2243687 := bstep (se 1 (by rfl) ⟨1682765, by rfl⟩ : syracuseStep 2243687 = 3365531) B3365531
theorem B18431489 : Blo 1494067 18431489 := bstep (se 2 (by rfl) ⟨6911808, by rfl⟩ : syracuseStep 18431489 = 13823617) B13823617
theorem B1597087 : Blo 1494067 1597087 := bstep (se 1 (by rfl) ⟨1197815, by rfl⟩ : syracuseStep 1597087 = 2395631) B2395631
theorem B27270865 : Blo 1494067 27270865 := bstep (se 2 (by rfl) ⟨10226574, by rfl⟩ : syracuseStep 27270865 = 20453149) B20453149
theorem B9838751 : Blo 1494067 9838751 := bstep (se 1 (by rfl) ⟨7379063, by rfl⟩ : syracuseStep 9838751 = 14758127) B14758127
theorem B5677391 : Blo 1494067 5677391 := bstep (se 1 (by rfl) ⟨4258043, by rfl⟩ : syracuseStep 5677391 = 8516087) B8516087
theorem B12125321 : Blo 1494067 12125321 := bstep (se 2 (by rfl) ⟨4546995, by rfl⟩ : syracuseStep 12125321 = 9093991) B9093991
theorem B12764425 : Blo 1494067 12764425 := bstep (se 2 (by rfl) ⟨4786659, by rfl⟩ : syracuseStep 12764425 = 9573319) B9573319
theorem B8513423 : Blo 1494067 8513423 := bstep (se 1 (by rfl) ⟨6385067, by rfl⟩ : syracuseStep 8513423 = 12770135) B12770135
theorem B5049215 : Blo 1494067 5049215 := bstep (se 1 (by rfl) ⟨3786911, by rfl⟩ : syracuseStep 5049215 = 7573823) B7573823
theorem B1494175 : Blo 1494067 1494175 := bstep (se 1 (by rfl) ⟨1120631, by rfl⟩ : syracuseStep 1494175 = 2241263) B2241263
theorem B1682671 : Blo 1494067 1682671 := bstep (se 1 (by rfl) ⟨1262003, by rfl⟩ : syracuseStep 1682671 = 2524007) B2524007
theorem B1494735 : Blo 1494067 1494735 := bstep (se 1 (by rfl) ⟨1121051, by rfl⟩ : syracuseStep 1494735 = 2242103) B2242103
theorem B11358305 : Blo 1494067 11358305 := bstep (se 2 (by rfl) ⟨4259364, by rfl⟩ : syracuseStep 11358305 = 8518729) B8518729
theorem B1495791 : Blo 1494067 1495791 := bstep (se 1 (by rfl) ⟨1121843, by rfl⟩ : syracuseStep 1495791 = 2243687) B2243687
theorem B36361153 : Blo 1494067 36361153 := bstep (se 2 (by rfl) ⟨13635432, by rfl⟩ : syracuseStep 36361153 = 27270865) B27270865
theorem B46674917 : Blo 1494067 46674917 := bstep (se 4 (by rfl) ⟨4375773, by rfl⟩ : syracuseStep 46674917 = 8751547) B8751547
theorem B13825019 : Blo 1494067 13825019 := bstep (se 1 (by rfl) ⟨10368764, by rfl⟩ : syracuseStep 13825019 = 20737529) B20737529
theorem B99628841 : Blo 1494067 99628841 := bstep (se 2 (by rfl) ⟨37360815, by rfl⟩ : syracuseStep 99628841 = 74721631) B74721631
theorem B8509481 : Blo 1494067 8509481 := bstep (se 2 (by rfl) ⟨3191055, by rfl⟩ : syracuseStep 8509481 = 6382111) B6382111
theorem B2242727 : Blo 1494067 2242727 := bstep (se 1 (by rfl) ⟨1682045, by rfl⟩ : syracuseStep 2242727 = 3364091) B3364091
theorem B8517797 : Blo 1494067 8517797 := bstep (se 4 (by rfl) ⟨798543, by rfl⟩ : syracuseStep 8517797 = 1597087) B1597087
theorem B6470057 : Blo 1494067 6470057 := bstep (se 2 (by rfl) ⟨2426271, by rfl⟩ : syracuseStep 6470057 = 4852543) B4852543
theorem B4258295 : Blo 1494067 4258295 := bstep (se 1 (by rfl) ⟨3193721, by rfl⟩ : syracuseStep 4258295 = 6387443) B6387443
theorem B2522299 : Blo 1494067 2522299 := bstep (se 1 (by rfl) ⟨1891724, by rfl⟩ : syracuseStep 2522299 = 3783449) B3783449
theorem B12287659 : Blo 1494067 12287659 := bstep (se 1 (by rfl) ⟨9215744, by rfl⟩ : syracuseStep 12287659 = 18431489) B18431489
theorem B3784927 : Blo 1494067 3784927 := bstep (se 1 (by rfl) ⟨2838695, by rfl⟩ : syracuseStep 3784927 = 5677391) B5677391
theorem B9216679 : Blo 1494067 9216679 := bstep (se 1 (by rfl) ⟨6912509, by rfl⟩ : syracuseStep 9216679 = 13825019) B13825019
theorem B17253485 : Blo 1494067 17253485 := bstep (se 3 (by rfl) ⟨3235028, by rfl⟩ : syracuseStep 17253485 = 6470057) B6470057
theorem B48481537 : Blo 1494067 48481537 := bstep (se 2 (by rfl) ⟨18180576, by rfl⟩ : syracuseStep 48481537 = 36361153) B36361153
theorem B5678531 : Blo 1494067 5678531 := bstep (se 1 (by rfl) ⟨4258898, by rfl⟩ : syracuseStep 5678531 = 8517797) B8517797
theorem B7572203 : Blo 1494067 7572203 := bstep (se 1 (by rfl) ⟨5679152, by rfl⟩ : syracuseStep 7572203 = 11358305) B11358305
theorem B31116611 : Blo 1494067 31116611 := bstep (se 1 (by rfl) ⟨23337458, by rfl⟩ : syracuseStep 31116611 = 46674917) B46674917
theorem B5672987 : Blo 1494067 5672987 := bstep (se 1 (by rfl) ⟨4254740, by rfl⟩ : syracuseStep 5672987 = 8509481) B8509481
theorem B1495151 : Blo 1494067 1495151 := bstep (se 1 (by rfl) ⟨1121363, by rfl⟩ : syracuseStep 1495151 = 2242727) B2242727
theorem B3363065 : Blo 1494067 3363065 := bstep (se 2 (by rfl) ⟨1261149, by rfl⟩ : syracuseStep 3363065 = 2522299) B2522299
theorem B2838863 : Blo 1494067 2838863 := bstep (se 1 (by rfl) ⟨2129147, by rfl⟩ : syracuseStep 2838863 = 4258295) B4258295
theorem B17019233 : Blo 1494067 17019233 := bstep (se 2 (by rfl) ⟨6382212, by rfl⟩ : syracuseStep 17019233 = 12764425) B12764425
theorem B26236669 : Blo 1494067 26236669 := bstep (se 3 (by rfl) ⟨4919375, by rfl⟩ : syracuseStep 26236669 = 9838751) B9838751
theorem B8083547 : Blo 1494067 8083547 := bstep (se 1 (by rfl) ⟨6062660, by rfl⟩ : syracuseStep 8083547 = 12125321) B12125321
theorem B66419227 : Blo 1494067 66419227 := bstep (se 1 (by rfl) ⟨49814420, by rfl⟩ : syracuseStep 66419227 = 99628841) B99628841
theorem B5675615 : Blo 1494067 5675615 := bstep (se 1 (by rfl) ⟨4256711, by rfl⟩ : syracuseStep 5675615 = 8513423) B8513423
theorem B2243561 : Blo 1494067 2243561 := bstep (se 2 (by rfl) ⟨841335, by rfl⟩ : syracuseStep 2243561 = 1682671) B1682671
theorem B3366143 : Blo 1494067 3366143 := bstep (se 1 (by rfl) ⟨2524607, by rfl⟩ : syracuseStep 3366143 = 5049215) B5049215
theorem B16383545 : Blo 1494067 16383545 := bstep (se 2 (by rfl) ⟨6143829, by rfl⟩ : syracuseStep 16383545 = 12287659) B12287659
theorem B1892575 : Blo 1494067 1892575 := bstep (se 1 (by rfl) ⟨1419431, by rfl⟩ : syracuseStep 1892575 = 2838863) B2838863
theorem B11346155 : Blo 1494067 11346155 := bstep (se 1 (by rfl) ⟨8509616, by rfl⟩ : syracuseStep 11346155 = 17019233) B17019233
theorem B5046569 : Blo 1494067 5046569 := bstep (se 2 (by rfl) ⟨1892463, by rfl⟩ : syracuseStep 5046569 = 3784927) B3784927
theorem B11502323 : Blo 1494067 11502323 := bstep (se 1 (by rfl) ⟨8626742, by rfl⟩ : syracuseStep 11502323 = 17253485) B17253485
theorem B12288905 : Blo 1494067 12288905 := bstep (se 2 (by rfl) ⟨4608339, by rfl⟩ : syracuseStep 12288905 = 9216679) B9216679
theorem B3785687 : Blo 1494067 3785687 := bstep (se 1 (by rfl) ⟨2839265, by rfl⟩ : syracuseStep 3785687 = 5678531) B5678531
theorem B5048135 : Blo 1494067 5048135 := bstep (se 1 (by rfl) ⟨3786101, by rfl⟩ : syracuseStep 5048135 = 7572203) B7572203
theorem B20744407 : Blo 1494067 20744407 := bstep (se 1 (by rfl) ⟨15558305, by rfl⟩ : syracuseStep 20744407 = 31116611) B31116611
theorem B34982225 : Blo 1494067 34982225 := bstep (se 2 (by rfl) ⟨13118334, by rfl⟩ : syracuseStep 34982225 = 26236669) B26236669
theorem B10922363 : Blo 1494067 10922363 := bstep (se 1 (by rfl) ⟨8191772, by rfl⟩ : syracuseStep 10922363 = 16383545) B16383545
theorem B88558969 : Blo 1494067 88558969 := bstep (se 2 (by rfl) ⟨33209613, by rfl⟩ : syracuseStep 88558969 = 66419227) B66419227
theorem B1495707 : Blo 1494067 1495707 := bstep (se 1 (by rfl) ⟨1121780, by rfl⟩ : syracuseStep 1495707 = 2243561) B2243561
theorem B3781991 : Blo 1494067 3781991 := bstep (se 1 (by rfl) ⟨2836493, by rfl⟩ : syracuseStep 3781991 = 5672987) B5672987
theorem B2242043 : Blo 1494067 2242043 := bstep (se 1 (by rfl) ⟨1681532, by rfl⟩ : syracuseStep 2242043 = 3363065) B3363065
theorem B5389031 : Blo 1494067 5389031 := bstep (se 1 (by rfl) ⟨4041773, by rfl⟩ : syracuseStep 5389031 = 8083547) B8083547
theorem B64642049 : Blo 1494067 64642049 := bstep (se 2 (by rfl) ⟨24240768, by rfl⟩ : syracuseStep 64642049 = 48481537) B48481537
theorem B3783743 : Blo 1494067 3783743 := bstep (se 1 (by rfl) ⟨2837807, by rfl⟩ : syracuseStep 3783743 = 5675615) B5675615
theorem B2244095 : Blo 1494067 2244095 := bstep (se 1 (by rfl) ⟨1683071, by rfl⟩ : syracuseStep 2244095 = 3366143) B3366143
theorem B2523433 : Blo 1494067 2523433 := bstep (se 2 (by rfl) ⟨946287, by rfl⟩ : syracuseStep 2523433 = 1892575) B1892575
theorem B7668215 : Blo 1494067 7668215 := bstep (se 1 (by rfl) ⟨5751161, by rfl⟩ : syracuseStep 7668215 = 11502323) B11502323
theorem B8192603 : Blo 1494067 8192603 := bstep (se 1 (by rfl) ⟨6144452, by rfl⟩ : syracuseStep 8192603 = 12288905) B12288905
theorem B2523791 : Blo 1494067 2523791 := bstep (se 1 (by rfl) ⟨1892843, by rfl⟩ : syracuseStep 2523791 = 3785687) B3785687
theorem B7564103 : Blo 1494067 7564103 := bstep (se 1 (by rfl) ⟨5673077, by rfl⟩ : syracuseStep 7564103 = 11346155) B11346155
theorem B27659209 : Blo 1494067 27659209 := bstep (se 2 (by rfl) ⟨10372203, by rfl⟩ : syracuseStep 27659209 = 20744407) B20744407
theorem B1494695 : Blo 1494067 1494695 := bstep (se 1 (by rfl) ⟨1121021, by rfl⟩ : syracuseStep 1494695 = 2242043) B2242043
theorem B3592687 : Blo 1494067 3592687 := bstep (se 1 (by rfl) ⟨2694515, by rfl⟩ : syracuseStep 3592687 = 5389031) B5389031
theorem B43094699 : Blo 1494067 43094699 := bstep (se 1 (by rfl) ⟨32321024, by rfl⟩ : syracuseStep 43094699 = 64642049) B64642049
theorem B1496063 : Blo 1494067 1496063 := bstep (se 1 (by rfl) ⟨1122047, by rfl⟩ : syracuseStep 1496063 = 2244095) B2244095
theorem B3364379 : Blo 1494067 3364379 := bstep (se 1 (by rfl) ⟨2523284, by rfl⟩ : syracuseStep 3364379 = 5046569) B5046569
theorem B2521327 : Blo 1494067 2521327 := bstep (se 1 (by rfl) ⟨1890995, by rfl⟩ : syracuseStep 2521327 = 3781991) B3781991
theorem B3365423 : Blo 1494067 3365423 := bstep (se 1 (by rfl) ⟨2524067, by rfl⟩ : syracuseStep 3365423 = 5048135) B5048135
theorem B23321483 : Blo 1494067 23321483 := bstep (se 1 (by rfl) ⟨17491112, by rfl⟩ : syracuseStep 23321483 = 34982225) B34982225
theorem B7281575 : Blo 1494067 7281575 := bstep (se 1 (by rfl) ⟨5461181, by rfl⟩ : syracuseStep 7281575 = 10922363) B10922363
theorem B118078625 : Blo 1494067 118078625 := bstep (se 2 (by rfl) ⟨44279484, by rfl⟩ : syracuseStep 118078625 = 88558969) B88558969
theorem B2522495 : Blo 1494067 2522495 := bstep (se 1 (by rfl) ⟨1891871, by rfl⟩ : syracuseStep 2522495 = 3783743) B3783743
theorem B5112143 : Blo 1494067 5112143 := bstep (se 1 (by rfl) ⟨3834107, by rfl⟩ : syracuseStep 5112143 = 7668215) B7668215
theorem B28729799 : Blo 1494067 28729799 := bstep (se 1 (by rfl) ⟨21547349, by rfl⟩ : syracuseStep 28729799 = 43094699) B43094699
theorem B590063125 : Blo 1494067 590063125 := bstep (se 6 (by rfl) ⟨13829604, by rfl⟩ : syracuseStep 590063125 = 27659209) B27659209
theorem B78719083 : Blo 1494067 78719083 := bstep (se 1 (by rfl) ⟨59039312, by rfl⟩ : syracuseStep 78719083 = 118078625) B118078625
theorem B1681663 : Blo 1494067 1681663 := bstep (se 1 (by rfl) ⟨1261247, by rfl⟩ : syracuseStep 1681663 = 2522495) B2522495
theorem B3361769 : Blo 1494067 3361769 := bstep (se 2 (by rfl) ⟨1260663, by rfl⟩ : syracuseStep 3361769 = 2521327) B2521327
theorem B1682527 : Blo 1494067 1682527 := bstep (se 1 (by rfl) ⟨1261895, by rfl⟩ : syracuseStep 1682527 = 2523791) B2523791
theorem B5042735 : Blo 1494067 5042735 := bstep (se 1 (by rfl) ⟨3782051, by rfl⟩ : syracuseStep 5042735 = 7564103) B7564103
theorem B4854383 : Blo 1494067 4854383 := bstep (se 1 (by rfl) ⟨3640787, by rfl⟩ : syracuseStep 4854383 = 7281575) B7281575
theorem B3364577 : Blo 1494067 3364577 := bstep (se 2 (by rfl) ⟨1261716, by rfl⟩ : syracuseStep 3364577 = 2523433) B2523433
theorem B5461735 : Blo 1494067 5461735 := bstep (se 1 (by rfl) ⟨4096301, by rfl⟩ : syracuseStep 5461735 = 8192603) B8192603
theorem B4790249 : Blo 1494067 4790249 := bstep (se 2 (by rfl) ⟨1796343, by rfl⟩ : syracuseStep 4790249 = 3592687) B3592687
theorem B2242919 : Blo 1494067 2242919 := bstep (se 1 (by rfl) ⟨1682189, by rfl⟩ : syracuseStep 2242919 = 3364379) B3364379
theorem B2243615 : Blo 1494067 2243615 := bstep (se 1 (by rfl) ⟨1682711, by rfl⟩ : syracuseStep 2243615 = 3365423) B3365423
theorem B15547655 : Blo 1494067 15547655 := bstep (se 1 (by rfl) ⟨11660741, by rfl⟩ : syracuseStep 15547655 = 23321483) B23321483
theorem B3408095 : Blo 1494067 3408095 := bstep (se 1 (by rfl) ⟨2556071, by rfl⟩ : syracuseStep 3408095 = 5112143) B5112143
theorem B19153199 : Blo 1494067 19153199 := bstep (se 1 (by rfl) ⟨14364899, by rfl⟩ : syracuseStep 19153199 = 28729799) B28729799
theorem B3236255 : Blo 1494067 3236255 := bstep (se 1 (by rfl) ⟨2427191, by rfl⟩ : syracuseStep 3236255 = 4854383) B4854383
theorem B10365103 : Blo 1494067 10365103 := bstep (se 1 (by rfl) ⟨7773827, by rfl⟩ : syracuseStep 10365103 = 15547655) B15547655
theorem B3361823 : Blo 1494067 3361823 := bstep (se 1 (by rfl) ⟨2521367, by rfl⟩ : syracuseStep 3361823 = 5042735) B5042735
theorem B419835109 : Blo 1494067 419835109 := bstep (se 4 (by rfl) ⟨39359541, by rfl⟩ : syracuseStep 419835109 = 78719083) B78719083
theorem B1495279 : Blo 1494067 1495279 := bstep (se 1 (by rfl) ⟨1121459, by rfl⟩ : syracuseStep 1495279 = 2242919) B2242919
theorem B2241179 : Blo 1494067 2241179 := bstep (se 1 (by rfl) ⟨1680884, by rfl⟩ : syracuseStep 2241179 = 3361769) B3361769
theorem B1495743 : Blo 1494067 1495743 := bstep (se 1 (by rfl) ⟨1121807, by rfl⟩ : syracuseStep 1495743 = 2243615) B2243615
theorem B2242217 : Blo 1494067 2242217 := bstep (se 2 (by rfl) ⟨840831, by rfl⟩ : syracuseStep 2242217 = 1681663) B1681663
theorem B2243051 : Blo 1494067 2243051 := bstep (se 1 (by rfl) ⟨1682288, by rfl⟩ : syracuseStep 2243051 = 3364577) B3364577
theorem B3193499 : Blo 1494067 3193499 := bstep (se 1 (by rfl) ⟨2395124, by rfl⟩ : syracuseStep 3193499 = 4790249) B4790249
theorem B2243369 : Blo 1494067 2243369 := bstep (se 2 (by rfl) ⟨841263, by rfl⟩ : syracuseStep 2243369 = 1682527) B1682527
theorem B786750833 : Blo 1494067 786750833 := bstep (se 2 (by rfl) ⟨295031562, by rfl⟩ : syracuseStep 786750833 = 590063125) B590063125
theorem B7282313 : Blo 1494067 7282313 := bstep (se 2 (by rfl) ⟨2730867, by rfl⟩ : syracuseStep 7282313 = 5461735) B5461735
theorem B55280549 : Blo 1494067 55280549 := bstep (se 4 (by rfl) ⟨5182551, by rfl⟩ : syracuseStep 55280549 = 10365103) B10365103
theorem B2272063 : Blo 1494067 2272063 := bstep (se 1 (by rfl) ⟨1704047, by rfl⟩ : syracuseStep 2272063 = 3408095) B3408095
theorem B1494119 : Blo 1494067 1494119 := bstep (se 1 (by rfl) ⟨1120589, by rfl⟩ : syracuseStep 1494119 = 2241179) B2241179
theorem B1494811 : Blo 1494067 1494811 := bstep (se 1 (by rfl) ⟨1121108, by rfl⟩ : syracuseStep 1494811 = 2242217) B2242217
theorem B559780145 : Blo 1494067 559780145 := bstep (se 2 (by rfl) ⟨209917554, by rfl⟩ : syracuseStep 559780145 = 419835109) B419835109
theorem B1495367 : Blo 1494067 1495367 := bstep (se 1 (by rfl) ⟨1121525, by rfl⟩ : syracuseStep 1495367 = 2243051) B2243051
theorem B1495579 : Blo 1494067 1495579 := bstep (se 1 (by rfl) ⟨1121684, by rfl⟩ : syracuseStep 1495579 = 2243369) B2243369
theorem B2241215 : Blo 1494067 2241215 := bstep (se 1 (by rfl) ⟨1680911, by rfl⟩ : syracuseStep 2241215 = 3361823) B3361823
theorem B4854875 : Blo 1494067 4854875 := bstep (se 1 (by rfl) ⟨3641156, by rfl⟩ : syracuseStep 4854875 = 7282313) B7282313
theorem B12768799 : Blo 1494067 12768799 := bstep (se 1 (by rfl) ⟨9576599, by rfl⟩ : syracuseStep 12768799 = 19153199) B19153199
theorem B34520053 : Blo 1494067 34520053 := bstep (se 5 (by rfl) ⟨1618127, by rfl⟩ : syracuseStep 34520053 = 3236255) B3236255
theorem B2128999 : Blo 1494067 2128999 := bstep (se 1 (by rfl) ⟨1596749, by rfl⟩ : syracuseStep 2128999 = 3193499) B3193499
theorem B524500555 : Blo 1494067 524500555 := bstep (se 1 (by rfl) ⟨393375416, by rfl⟩ : syracuseStep 524500555 = 786750833) B786750833
theorem B373186763 : Blo 1494067 373186763 := bstep (se 1 (by rfl) ⟨279890072, by rfl⟩ : syracuseStep 373186763 = 559780145) B559780145
theorem B17025065 : Blo 1494067 17025065 := bstep (se 2 (by rfl) ⟨6384399, by rfl⟩ : syracuseStep 17025065 = 12768799) B12768799
theorem B1494143 : Blo 1494067 1494143 := bstep (se 1 (by rfl) ⟨1120607, by rfl⟩ : syracuseStep 1494143 = 2241215) B2241215
theorem B51785333 : Blo 1494067 51785333 := bstep (se 5 (by rfl) ⟨2427437, by rfl⟩ : syracuseStep 51785333 = 4854875) B4854875
theorem B46026737 : Blo 1494067 46026737 := bstep (se 2 (by rfl) ⟨17260026, by rfl⟩ : syracuseStep 46026737 = 34520053) B34520053
theorem B2838665 : Blo 1494067 2838665 := bstep (se 2 (by rfl) ⟨1064499, by rfl⟩ : syracuseStep 2838665 = 2128999) B2128999
theorem B36853699 : Blo 1494067 36853699 := bstep (se 1 (by rfl) ⟨27640274, by rfl⟩ : syracuseStep 36853699 = 55280549) B55280549
theorem B3029417 : Blo 1494067 3029417 := bstep (se 2 (by rfl) ⟨1136031, by rfl⟩ : syracuseStep 3029417 = 2272063) B2272063
theorem B699334073 : Blo 1494067 699334073 := bstep (se 2 (by rfl) ⟨262250277, by rfl⟩ : syracuseStep 699334073 = 524500555) B524500555
theorem B248791175 : Blo 1494067 248791175 := bstep (se 1 (by rfl) ⟨186593381, by rfl⟩ : syracuseStep 248791175 = 373186763) B373186763
theorem B7569773 : Blo 1494067 7569773 := bstep (se 3 (by rfl) ⟨1419332, by rfl⟩ : syracuseStep 7569773 = 2838665) B2838665
theorem B34523555 : Blo 1494067 34523555 := bstep (se 1 (by rfl) ⟨25892666, by rfl⟩ : syracuseStep 34523555 = 51785333) B51785333
theorem B49138265 : Blo 1494067 49138265 := bstep (se 2 (by rfl) ⟨18426849, by rfl⟩ : syracuseStep 49138265 = 36853699) B36853699
theorem B11350043 : Blo 1494067 11350043 := bstep (se 1 (by rfl) ⟨8512532, by rfl⟩ : syracuseStep 11350043 = 17025065) B17025065
theorem B2019611 : Blo 1494067 2019611 := bstep (se 1 (by rfl) ⟨1514708, by rfl⟩ : syracuseStep 2019611 = 3029417) B3029417
theorem B30684491 : Blo 1494067 30684491 := bstep (se 1 (by rfl) ⟨23013368, by rfl⟩ : syracuseStep 30684491 = 46026737) B46026737
theorem B466222715 : Blo 1494067 466222715 := bstep (se 1 (by rfl) ⟨349667036, by rfl⟩ : syracuseStep 466222715 = 699334073) B699334073
theorem B5046515 : Blo 1494067 5046515 := bstep (se 1 (by rfl) ⟨3784886, by rfl⟩ : syracuseStep 5046515 = 7569773) B7569773
theorem B20456327 : Blo 1494067 20456327 := bstep (se 1 (by rfl) ⟨15342245, by rfl⟩ : syracuseStep 20456327 = 30684491) B30684491
theorem B92062813 : Blo 1494067 92062813 := bstep (se 3 (by rfl) ⟨17261777, by rfl⟩ : syracuseStep 92062813 = 34523555) B34523555
theorem B310815143 : Blo 1494067 310815143 := bstep (se 1 (by rfl) ⟨233111357, by rfl⟩ : syracuseStep 310815143 = 466222715) B466222715
theorem B5385629 : Blo 1494067 5385629 := bstep (se 3 (by rfl) ⟨1009805, by rfl⟩ : syracuseStep 5385629 = 2019611) B2019611
theorem B7566695 : Blo 1494067 7566695 := bstep (se 1 (by rfl) ⟨5675021, by rfl⟩ : syracuseStep 7566695 = 11350043) B11350043
theorem B165860783 : Blo 1494067 165860783 := bstep (se 1 (by rfl) ⟨124395587, by rfl⟩ : syracuseStep 165860783 = 248791175) B248791175
theorem B32758843 : Blo 1494067 32758843 := bstep (se 1 (by rfl) ⟨24569132, by rfl⟩ : syracuseStep 32758843 = 49138265) B49138265
theorem B122750417 : Blo 1494067 122750417 := bstep (se 2 (by rfl) ⟨46031406, by rfl⟩ : syracuseStep 122750417 = 92062813) B92062813
theorem B207210095 : Blo 1494067 207210095 := bstep (se 1 (by rfl) ⟨155407571, by rfl⟩ : syracuseStep 207210095 = 310815143) B310815143
theorem B3590419 : Blo 1494067 3590419 := bstep (se 1 (by rfl) ⟨2692814, by rfl⟩ : syracuseStep 3590419 = 5385629) B5385629
theorem B3364343 : Blo 1494067 3364343 := bstep (se 1 (by rfl) ⟨2523257, by rfl⟩ : syracuseStep 3364343 = 5046515) B5046515
theorem B5044463 : Blo 1494067 5044463 := bstep (se 1 (by rfl) ⟨3783347, by rfl⟩ : syracuseStep 5044463 = 7566695) B7566695
theorem B110573855 : Blo 1494067 110573855 := bstep (se 1 (by rfl) ⟨82930391, by rfl⟩ : syracuseStep 110573855 = 165860783) B165860783
theorem B43678457 : Blo 1494067 43678457 := bstep (se 2 (by rfl) ⟨16379421, by rfl⟩ : syracuseStep 43678457 = 32758843) B32758843
theorem B54550205 : Blo 1494067 54550205 := bstep (se 3 (by rfl) ⟨10228163, by rfl⟩ : syracuseStep 54550205 = 20456327) B20456327
theorem B36366803 : Blo 1494067 36366803 := bstep (se 1 (by rfl) ⟨27275102, by rfl⟩ : syracuseStep 36366803 = 54550205) B54550205
theorem B4787225 : Blo 1494067 4787225 := bstep (se 2 (by rfl) ⟨1795209, by rfl⟩ : syracuseStep 4787225 = 3590419) B3590419
theorem B81833611 : Blo 1494067 81833611 := bstep (se 1 (by rfl) ⟨61375208, by rfl⟩ : syracuseStep 81833611 = 122750417) B122750417
theorem B3362975 : Blo 1494067 3362975 := bstep (se 1 (by rfl) ⟨2522231, by rfl⟩ : syracuseStep 3362975 = 5044463) B5044463
theorem B73715903 : Blo 1494067 73715903 := bstep (se 1 (by rfl) ⟨55286927, by rfl⟩ : syracuseStep 73715903 = 110573855) B110573855
theorem B29118971 : Blo 1494067 29118971 := bstep (se 1 (by rfl) ⟨21839228, by rfl⟩ : syracuseStep 29118971 = 43678457) B43678457
theorem B2242895 : Blo 1494067 2242895 := bstep (se 1 (by rfl) ⟨1682171, by rfl⟩ : syracuseStep 2242895 = 3364343) B3364343
theorem B138140063 : Blo 1494067 138140063 := bstep (se 1 (by rfl) ⟨103605047, by rfl⟩ : syracuseStep 138140063 = 207210095) B207210095
theorem B49143935 : Blo 1494067 49143935 := bstep (se 1 (by rfl) ⟨36857951, by rfl⟩ : syracuseStep 49143935 = 73715903) B73715903
theorem B109111481 : Blo 1494067 109111481 := bstep (se 2 (by rfl) ⟨40916805, by rfl⟩ : syracuseStep 109111481 = 81833611) B81833611
theorem B1495263 : Blo 1494067 1495263 := bstep (se 1 (by rfl) ⟨1121447, by rfl⟩ : syracuseStep 1495263 = 2242895) B2242895
theorem B24244535 : Blo 1494067 24244535 := bstep (se 1 (by rfl) ⟨18183401, by rfl⟩ : syracuseStep 24244535 = 36366803) B36366803
theorem B3191483 : Blo 1494067 3191483 := bstep (se 1 (by rfl) ⟨2393612, by rfl⟩ : syracuseStep 3191483 = 4787225) B4787225
theorem B2241983 : Blo 1494067 2241983 := bstep (se 1 (by rfl) ⟨1681487, by rfl⟩ : syracuseStep 2241983 = 3362975) B3362975
theorem B77650589 : Blo 1494067 77650589 := bstep (se 3 (by rfl) ⟨14559485, by rfl⟩ : syracuseStep 77650589 = 29118971) B29118971
theorem B92093375 : Blo 1494067 92093375 := bstep (se 1 (by rfl) ⟨69070031, by rfl⟩ : syracuseStep 92093375 = 138140063) B138140063
theorem B64652093 : Blo 1494067 64652093 := bstep (se 3 (by rfl) ⟨12122267, by rfl⟩ : syracuseStep 64652093 = 24244535) B24244535
theorem B131050493 : Blo 1494067 131050493 := bstep (se 3 (by rfl) ⟨24571967, by rfl⟩ : syracuseStep 131050493 = 49143935) B49143935
theorem B1494655 : Blo 1494067 1494655 := bstep (se 1 (by rfl) ⟨1120991, by rfl⟩ : syracuseStep 1494655 = 2241983) B2241983
theorem B72740987 : Blo 1494067 72740987 := bstep (se 1 (by rfl) ⟨54555740, by rfl⟩ : syracuseStep 72740987 = 109111481) B109111481
theorem B61395583 : Blo 1494067 61395583 := bstep (se 1 (by rfl) ⟨46046687, by rfl⟩ : syracuseStep 61395583 = 92093375) B92093375
theorem B2127655 : Blo 1494067 2127655 := bstep (se 1 (by rfl) ⟨1595741, by rfl⟩ : syracuseStep 2127655 = 3191483) B3191483
theorem B207068237 : Blo 1494067 207068237 := bstep (se 3 (by rfl) ⟨38825294, by rfl⟩ : syracuseStep 207068237 = 77650589) B77650589
theorem B138045491 : Blo 1494067 138045491 := bstep (se 1 (by rfl) ⟨103534118, by rfl⟩ : syracuseStep 138045491 = 207068237) B207068237
theorem B2836873 : Blo 1494067 2836873 := bstep (se 2 (by rfl) ⟨1063827, by rfl⟩ : syracuseStep 2836873 = 2127655) B2127655
theorem B43101395 : Blo 1494067 43101395 := bstep (se 1 (by rfl) ⟨32326046, by rfl⟩ : syracuseStep 43101395 = 64652093) B64652093
theorem B48493991 : Blo 1494067 48493991 := bstep (se 1 (by rfl) ⟨36370493, by rfl⟩ : syracuseStep 48493991 = 72740987) B72740987
theorem B81860777 : Blo 1494067 81860777 := bstep (se 2 (by rfl) ⟨30697791, by rfl⟩ : syracuseStep 81860777 = 61395583) B61395583
theorem B87366995 : Blo 1494067 87366995 := bstep (se 1 (by rfl) ⟨65525246, by rfl⟩ : syracuseStep 87366995 = 131050493) B131050493
theorem B92030327 : Blo 1494067 92030327 := bstep (se 1 (by rfl) ⟨69022745, by rfl⟩ : syracuseStep 92030327 = 138045491) B138045491
theorem B28734263 : Blo 1494067 28734263 := bstep (se 1 (by rfl) ⟨21550697, by rfl⟩ : syracuseStep 28734263 = 43101395) B43101395
theorem B3782497 : Blo 1494067 3782497 := bstep (se 2 (by rfl) ⟨1418436, by rfl⟩ : syracuseStep 3782497 = 2836873) B2836873
theorem B129317309 : Blo 1494067 129317309 := bstep (se 3 (by rfl) ⟨24246995, by rfl⟩ : syracuseStep 129317309 = 48493991) B48493991
theorem B54573851 : Blo 1494067 54573851 := bstep (se 1 (by rfl) ⟨40930388, by rfl⟩ : syracuseStep 54573851 = 81860777) B81860777
theorem B58244663 : Blo 1494067 58244663 := bstep (se 1 (by rfl) ⟨43683497, by rfl⟩ : syracuseStep 58244663 = 87366995) B87366995
theorem B36382567 : Blo 1494067 36382567 := bstep (se 1 (by rfl) ⟨27286925, by rfl⟩ : syracuseStep 36382567 = 54573851) B54573851
theorem B19156175 : Blo 1494067 19156175 := bstep (se 1 (by rfl) ⟨14367131, by rfl⟩ : syracuseStep 19156175 = 28734263) B28734263
theorem B61353551 : Blo 1494067 61353551 := bstep (se 1 (by rfl) ⟨46015163, by rfl⟩ : syracuseStep 61353551 = 92030327) B92030327
theorem B5043329 : Blo 1494067 5043329 := bstep (se 2 (by rfl) ⟨1891248, by rfl⟩ : syracuseStep 5043329 = 3782497) B3782497
theorem B86211539 : Blo 1494067 86211539 := bstep (se 1 (by rfl) ⟨64658654, by rfl⟩ : syracuseStep 86211539 = 129317309) B129317309
theorem B38829775 : Blo 1494067 38829775 := bstep (se 1 (by rfl) ⟨29122331, by rfl⟩ : syracuseStep 38829775 = 58244663) B58244663
theorem B3362219 : Blo 1494067 3362219 := bstep (se 1 (by rfl) ⟨2521664, by rfl⟩ : syracuseStep 3362219 = 5043329) B5043329
theorem B48510089 : Blo 1494067 48510089 := bstep (se 2 (by rfl) ⟨18191283, by rfl⟩ : syracuseStep 48510089 = 36382567) B36382567
theorem B57474359 : Blo 1494067 57474359 := bstep (se 1 (by rfl) ⟨43105769, by rfl⟩ : syracuseStep 57474359 = 86211539) B86211539
theorem B12770783 : Blo 1494067 12770783 := bstep (se 1 (by rfl) ⟨9578087, by rfl⟩ : syracuseStep 12770783 = 19156175) B19156175
theorem B51773033 : Blo 1494067 51773033 := bstep (se 2 (by rfl) ⟨19414887, by rfl⟩ : syracuseStep 51773033 = 38829775) B38829775
theorem B40902367 : Blo 1494067 40902367 := bstep (se 1 (by rfl) ⟨30676775, by rfl⟩ : syracuseStep 40902367 = 61353551) B61353551
theorem B38316239 : Blo 1494067 38316239 := bstep (se 1 (by rfl) ⟨28737179, by rfl⟩ : syracuseStep 38316239 = 57474359) B57474359
theorem B54536489 : Blo 1494067 54536489 := bstep (se 2 (by rfl) ⟨20451183, by rfl⟩ : syracuseStep 54536489 = 40902367) B40902367
theorem B8513855 : Blo 1494067 8513855 := bstep (se 1 (by rfl) ⟨6385391, by rfl⟩ : syracuseStep 8513855 = 12770783) B12770783
theorem B34515355 : Blo 1494067 34515355 := bstep (se 1 (by rfl) ⟨25886516, by rfl⟩ : syracuseStep 34515355 = 51773033) B51773033
theorem B2241479 : Blo 1494067 2241479 := bstep (se 1 (by rfl) ⟨1681109, by rfl⟩ : syracuseStep 2241479 = 3362219) B3362219
theorem B32340059 : Blo 1494067 32340059 := bstep (se 1 (by rfl) ⟨24255044, by rfl⟩ : syracuseStep 32340059 = 48510089) B48510089
theorem B25544159 : Blo 1494067 25544159 := bstep (se 1 (by rfl) ⟨19158119, by rfl⟩ : syracuseStep 25544159 = 38316239) B38316239
theorem B36357659 : Blo 1494067 36357659 := bstep (se 1 (by rfl) ⟨27268244, by rfl⟩ : syracuseStep 36357659 = 54536489) B54536489
theorem B1494319 : Blo 1494067 1494319 := bstep (se 1 (by rfl) ⟨1120739, by rfl⟩ : syracuseStep 1494319 = 2241479) B2241479
theorem B46020473 : Blo 1494067 46020473 := bstep (se 2 (by rfl) ⟨17257677, by rfl⟩ : syracuseStep 46020473 = 34515355) B34515355
theorem B21560039 : Blo 1494067 21560039 := bstep (se 1 (by rfl) ⟨16170029, by rfl⟩ : syracuseStep 21560039 = 32340059) B32340059
theorem B5675903 : Blo 1494067 5675903 := bstep (se 1 (by rfl) ⟨4256927, by rfl⟩ : syracuseStep 5675903 = 8513855) B8513855
theorem B30680315 : Blo 1494067 30680315 := bstep (se 1 (by rfl) ⟨23010236, by rfl⟩ : syracuseStep 30680315 = 46020473) B46020473
theorem B14373359 : Blo 1494067 14373359 := bstep (se 1 (by rfl) ⟨10780019, by rfl⟩ : syracuseStep 14373359 = 21560039) B21560039
theorem B17029439 : Blo 1494067 17029439 := bstep (se 1 (by rfl) ⟨12772079, by rfl⟩ : syracuseStep 17029439 = 25544159) B25544159
theorem B24238439 : Blo 1494067 24238439 := bstep (se 1 (by rfl) ⟨18178829, by rfl⟩ : syracuseStep 24238439 = 36357659) B36357659
theorem B3783935 : Blo 1494067 3783935 := bstep (se 1 (by rfl) ⟨2837951, by rfl⟩ : syracuseStep 3783935 = 5675903) B5675903
theorem B16158959 : Blo 1494067 16158959 := bstep (se 1 (by rfl) ⟨12119219, by rfl⟩ : syracuseStep 16158959 = 24238439) B24238439
theorem B9582239 : Blo 1494067 9582239 := bstep (se 1 (by rfl) ⟨7186679, by rfl⟩ : syracuseStep 9582239 = 14373359) B14373359
theorem B20453543 : Blo 1494067 20453543 := bstep (se 1 (by rfl) ⟨15340157, by rfl⟩ : syracuseStep 20453543 = 30680315) B30680315
theorem B11352959 : Blo 1494067 11352959 := bstep (se 1 (by rfl) ⟨8514719, by rfl⟩ : syracuseStep 11352959 = 17029439) B17029439
theorem B2522623 : Blo 1494067 2522623 := bstep (se 1 (by rfl) ⟨1891967, by rfl⟩ : syracuseStep 2522623 = 3783935) B3783935
theorem B10772639 : Blo 1494067 10772639 := bstep (se 1 (by rfl) ⟨8079479, by rfl⟩ : syracuseStep 10772639 = 16158959) B16158959
theorem B13635695 : Blo 1494067 13635695 := bstep (se 1 (by rfl) ⟨10226771, by rfl⟩ : syracuseStep 13635695 = 20453543) B20453543
theorem B3363497 : Blo 1494067 3363497 := bstep (se 2 (by rfl) ⟨1261311, by rfl⟩ : syracuseStep 3363497 = 2522623) B2522623
theorem B6388159 : Blo 1494067 6388159 := bstep (se 1 (by rfl) ⟨4791119, by rfl⟩ : syracuseStep 6388159 = 9582239) B9582239
theorem B7568639 : Blo 1494067 7568639 := bstep (se 1 (by rfl) ⟨5676479, by rfl⟩ : syracuseStep 7568639 = 11352959) B11352959
theorem B9090463 : Blo 1494067 9090463 := bstep (se 1 (by rfl) ⟨6817847, by rfl⟩ : syracuseStep 9090463 = 13635695) B13635695
theorem B7181759 : Blo 1494067 7181759 := bstep (se 1 (by rfl) ⟨5386319, by rfl⟩ : syracuseStep 7181759 = 10772639) B10772639
theorem B2242331 : Blo 1494067 2242331 := bstep (se 1 (by rfl) ⟨1681748, by rfl⟩ : syracuseStep 2242331 = 3363497) B3363497
theorem B8517545 : Blo 1494067 8517545 := bstep (se 2 (by rfl) ⟨3194079, by rfl⟩ : syracuseStep 8517545 = 6388159) B6388159
theorem B5045759 : Blo 1494067 5045759 := bstep (se 1 (by rfl) ⟨3784319, by rfl⟩ : syracuseStep 5045759 = 7568639) B7568639
theorem B5678363 : Blo 1494067 5678363 := bstep (se 1 (by rfl) ⟨4258772, by rfl⟩ : syracuseStep 5678363 = 8517545) B8517545
theorem B4787839 : Blo 1494067 4787839 := bstep (se 1 (by rfl) ⟨3590879, by rfl⟩ : syracuseStep 4787839 = 7181759) B7181759
theorem B1494887 : Blo 1494067 1494887 := bstep (se 1 (by rfl) ⟨1121165, by rfl⟩ : syracuseStep 1494887 = 2242331) B2242331
theorem B12120617 : Blo 1494067 12120617 := bstep (se 2 (by rfl) ⟨4545231, by rfl⟩ : syracuseStep 12120617 = 9090463) B9090463
theorem B3363839 : Blo 1494067 3363839 := bstep (se 1 (by rfl) ⟨2522879, by rfl⟩ : syracuseStep 3363839 = 5045759) B5045759
theorem B3785575 : Blo 1494067 3785575 := bstep (se 1 (by rfl) ⟨2839181, by rfl⟩ : syracuseStep 3785575 = 5678363) B5678363
theorem B6383785 : Blo 1494067 6383785 := bstep (se 2 (by rfl) ⟨2393919, by rfl⟩ : syracuseStep 6383785 = 4787839) B4787839
theorem B8080411 : Blo 1494067 8080411 := bstep (se 1 (by rfl) ⟨6060308, by rfl⟩ : syracuseStep 8080411 = 12120617) B12120617
theorem B2242559 : Blo 1494067 2242559 := bstep (se 1 (by rfl) ⟨1681919, by rfl⟩ : syracuseStep 2242559 = 3363839) B3363839
theorem B8511713 : Blo 1494067 8511713 := bstep (se 2 (by rfl) ⟨3191892, by rfl⟩ : syracuseStep 8511713 = 6383785) B6383785
theorem B5047433 : Blo 1494067 5047433 := bstep (se 2 (by rfl) ⟨1892787, by rfl⟩ : syracuseStep 5047433 = 3785575) B3785575
theorem B10773881 : Blo 1494067 10773881 := bstep (se 2 (by rfl) ⟨4040205, by rfl⟩ : syracuseStep 10773881 = 8080411) B8080411
theorem B1495039 : Blo 1494067 1495039 := bstep (se 1 (by rfl) ⟨1121279, by rfl⟩ : syracuseStep 1495039 = 2242559) B2242559
theorem B5674475 : Blo 1494067 5674475 := bstep (se 1 (by rfl) ⟨4255856, by rfl⟩ : syracuseStep 5674475 = 8511713) B8511713
theorem B3364955 : Blo 1494067 3364955 := bstep (se 1 (by rfl) ⟨2523716, by rfl⟩ : syracuseStep 3364955 = 5047433) B5047433
theorem B7182587 : Blo 1494067 7182587 := bstep (se 1 (by rfl) ⟨5386940, by rfl⟩ : syracuseStep 7182587 = 10773881) B10773881
theorem B4788391 : Blo 1494067 4788391 := bstep (se 1 (by rfl) ⟨3591293, by rfl⟩ : syracuseStep 4788391 = 7182587) B7182587
theorem B3782983 : Blo 1494067 3782983 := bstep (se 1 (by rfl) ⟨2837237, by rfl⟩ : syracuseStep 3782983 = 5674475) B5674475
theorem B2243303 : Blo 1494067 2243303 := bstep (se 1 (by rfl) ⟨1682477, by rfl⟩ : syracuseStep 2243303 = 3364955) B3364955
theorem B6384521 : Blo 1494067 6384521 := bstep (se 2 (by rfl) ⟨2394195, by rfl⟩ : syracuseStep 6384521 = 4788391) B4788391
theorem B1495535 : Blo 1494067 1495535 := bstep (se 1 (by rfl) ⟨1121651, by rfl⟩ : syracuseStep 1495535 = 2243303) B2243303
theorem B5043977 : Blo 1494067 5043977 := bstep (se 2 (by rfl) ⟨1891491, by rfl⟩ : syracuseStep 5043977 = 3782983) B3782983
theorem B3362651 : Blo 1494067 3362651 := bstep (se 1 (by rfl) ⟨2521988, by rfl⟩ : syracuseStep 3362651 = 5043977) B5043977
theorem B4256347 : Blo 1494067 4256347 := bstep (se 1 (by rfl) ⟨3192260, by rfl⟩ : syracuseStep 4256347 = 6384521) B6384521
theorem B2241767 : Blo 1494067 2241767 := bstep (se 1 (by rfl) ⟨1681325, by rfl⟩ : syracuseStep 2241767 = 3362651) B3362651
theorem B5675129 : Blo 1494067 5675129 := bstep (se 2 (by rfl) ⟨2128173, by rfl⟩ : syracuseStep 5675129 = 4256347) B4256347
theorem B1494511 : Blo 1494067 1494511 := bstep (se 1 (by rfl) ⟨1120883, by rfl⟩ : syracuseStep 1494511 = 2241767) B2241767
theorem B3783419 : Blo 1494067 3783419 := bstep (se 1 (by rfl) ⟨2837564, by rfl⟩ : syracuseStep 3783419 = 5675129) B5675129
theorem B2522279 : Blo 1494067 2522279 := bstep (se 1 (by rfl) ⟨1891709, by rfl⟩ : syracuseStep 2522279 = 3783419) B3783419
theorem B1681519 : Blo 1494067 1681519 := bstep (se 1 (by rfl) ⟨1261139, by rfl⟩ : syracuseStep 1681519 = 2522279) B2522279
theorem B2242025 : Blo 1494067 2242025 := bstep (se 2 (by rfl) ⟨840759, by rfl⟩ : syracuseStep 2242025 = 1681519) B1681519
theorem B1494683 : Blo 1494067 1494683 := bstep (se 1 (by rfl) ⟨1121012, by rfl⟩ : syracuseStep 1494683 = 2242025) B2242025

theorem C0 (j : ℕ) (h1 : 373516 ≤ j) (h2 : j ≤ 374016) : Blo 1494067 (4 * j + 3) := by
  interval_cases j
  · exact B1494067
  · exact B1494071
  · exact B1494075
  · exact B1494079
  · exact B1494083
  · exact B1494087
  · exact B1494091
  · exact B1494095
  · exact B1494099
  · exact B1494103
  · exact B1494107
  · exact B1494111
  · exact B1494115
  · exact B1494119
  · exact B1494123
  · exact B1494127
  · exact B1494131
  · exact B1494135
  · exact B1494139
  · exact B1494143
  · exact B1494147
  · exact B1494151
  · exact B1494155
  · exact B1494159
  · exact B1494163
  · exact B1494167
  · exact B1494171
  · exact B1494175
  · exact B1494179
  · exact B1494183
  · exact B1494187
  · exact B1494191
  · exact B1494195
  · exact B1494199
  · exact B1494203
  · exact B1494207
  · exact B1494211
  · exact B1494215
  · exact B1494219
  · exact B1494223
  · exact B1494227
  · exact B1494231
  · exact B1494235
  · exact B1494239
  · exact B1494243
  · exact B1494247
  · exact B1494251
  · exact B1494255
  · exact B1494259
  · exact B1494263
  · exact B1494267
  · exact B1494271
  · exact B1494275
  · exact B1494279
  · exact B1494283
  · exact B1494287
  · exact B1494291
  · exact B1494295
  · exact B1494299
  · exact B1494303
  · exact B1494307
  · exact B1494311
  · exact B1494315
  · exact B1494319
  · exact B1494323
  · exact B1494327
  · exact B1494331
  · exact B1494335
  · exact B1494339
  · exact B1494343
  · exact B1494347
  · exact B1494351
  · exact B1494355
  · exact B1494359
  · exact B1494363
  · exact B1494367
  · exact B1494371
  · exact B1494375
  · exact B1494379
  · exact B1494383
  · exact B1494387
  · exact B1494391
  · exact B1494395
  · exact B1494399
  · exact B1494403
  · exact B1494407
  · exact B1494411
  · exact B1494415
  · exact B1494419
  · exact B1494423
  · exact B1494427
  · exact B1494431
  · exact B1494435
  · exact B1494439
  · exact B1494443
  · exact B1494447
  · exact B1494451
  · exact B1494455
  · exact B1494459
  · exact B1494463
  · exact B1494467
  · exact B1494471
  · exact B1494475
  · exact B1494479
  · exact B1494483
  · exact B1494487
  · exact B1494491
  · exact B1494495
  · exact B1494499
  · exact B1494503
  · exact B1494507
  · exact B1494511
  · exact B1494515
  · exact B1494519
  · exact B1494523
  · exact B1494527
  · exact B1494531
  · exact B1494535
  · exact B1494539
  · exact B1494543
  · exact B1494547
  · exact B1494551
  · exact B1494555
  · exact B1494559
  · exact B1494563
  · exact B1494567
  · exact B1494571
  · exact B1494575
  · exact B1494579
  · exact B1494583
  · exact B1494587
  · exact B1494591
  · exact B1494595
  · exact B1494599
  · exact B1494603
  · exact B1494607
  · exact B1494611
  · exact B1494615
  · exact B1494619
  · exact B1494623
  · exact B1494627
  · exact B1494631
  · exact B1494635
  · exact B1494639
  · exact B1494643
  · exact B1494647
  · exact B1494651
  · exact B1494655
  · exact B1494659
  · exact B1494663
  · exact B1494667
  · exact B1494671
  · exact B1494675
  · exact B1494679
  · exact B1494683
  · exact B1494687
  · exact B1494691
  · exact B1494695
  · exact B1494699
  · exact B1494703
  · exact B1494707
  · exact B1494711
  · exact B1494715
  · exact B1494719
  · exact B1494723
  · exact B1494727
  · exact B1494731
  · exact B1494735
  · exact B1494739
  · exact B1494743
  · exact B1494747
  · exact B1494751
  · exact B1494755
  · exact B1494759
  · exact B1494763
  · exact B1494767
  · exact B1494771
  · exact B1494775
  · exact B1494779
  · exact B1494783
  · exact B1494787
  · exact B1494791
  · exact B1494795
  · exact B1494799
  · exact B1494803
  · exact B1494807
  · exact B1494811
  · exact B1494815
  · exact B1494819
  · exact B1494823
  · exact B1494827
  · exact B1494831
  · exact B1494835
  · exact B1494839
  · exact B1494843
  · exact B1494847
  · exact B1494851
  · exact B1494855
  · exact B1494859
  · exact B1494863
  · exact B1494867
  · exact B1494871
  · exact B1494875
  · exact B1494879
  · exact B1494883
  · exact B1494887
  · exact B1494891
  · exact B1494895
  · exact B1494899
  · exact B1494903
  · exact B1494907
  · exact B1494911
  · exact B1494915
  · exact B1494919
  · exact B1494923
  · exact B1494927
  · exact B1494931
  · exact B1494935
  · exact B1494939
  · exact B1494943
  · exact B1494947
  · exact B1494951
  · exact B1494955
  · exact B1494959
  · exact B1494963
  · exact B1494967
  · exact B1494971
  · exact B1494975
  · exact B1494979
  · exact B1494983
  · exact B1494987
  · exact B1494991
  · exact B1494995
  · exact B1494999
  · exact B1495003
  · exact B1495007
  · exact B1495011
  · exact B1495015
  · exact B1495019
  · exact B1495023
  · exact B1495027
  · exact B1495031
  · exact B1495035
  · exact B1495039
  · exact B1495043
  · exact B1495047
  · exact B1495051
  · exact B1495055
  · exact B1495059
  · exact B1495063
  · exact B1495067
  · exact B1495071
  · exact B1495075
  · exact B1495079
  · exact B1495083
  · exact B1495087
  · exact B1495091
  · exact B1495095
  · exact B1495099
  · exact B1495103
  · exact B1495107
  · exact B1495111
  · exact B1495115
  · exact B1495119
  · exact B1495123
  · exact B1495127
  · exact B1495131
  · exact B1495135
  · exact B1495139
  · exact B1495143
  · exact B1495147
  · exact B1495151
  · exact B1495155
  · exact B1495159
  · exact B1495163
  · exact B1495167
  · exact B1495171
  · exact B1495175
  · exact B1495179
  · exact B1495183
  · exact B1495187
  · exact B1495191
  · exact B1495195
  · exact B1495199
  · exact B1495203
  · exact B1495207
  · exact B1495211
  · exact B1495215
  · exact B1495219
  · exact B1495223
  · exact B1495227
  · exact B1495231
  · exact B1495235
  · exact B1495239
  · exact B1495243
  · exact B1495247
  · exact B1495251
  · exact B1495255
  · exact B1495259
  · exact B1495263
  · exact B1495267
  · exact B1495271
  · exact B1495275
  · exact B1495279
  · exact B1495283
  · exact B1495287
  · exact B1495291
  · exact B1495295
  · exact B1495299
  · exact B1495303
  · exact B1495307
  · exact B1495311
  · exact B1495315
  · exact B1495319
  · exact B1495323
  · exact B1495327
  · exact B1495331
  · exact B1495335
  · exact B1495339
  · exact B1495343
  · exact B1495347
  · exact B1495351
  · exact B1495355
  · exact B1495359
  · exact B1495363
  · exact B1495367
  · exact B1495371
  · exact B1495375
  · exact B1495379
  · exact B1495383
  · exact B1495387
  · exact B1495391
  · exact B1495395
  · exact B1495399
  · exact B1495403
  · exact B1495407
  · exact B1495411
  · exact B1495415
  · exact B1495419
  · exact B1495423
  · exact B1495427
  · exact B1495431
  · exact B1495435
  · exact B1495439
  · exact B1495443
  · exact B1495447
  · exact B1495451
  · exact B1495455
  · exact B1495459
  · exact B1495463
  · exact B1495467
  · exact B1495471
  · exact B1495475
  · exact B1495479
  · exact B1495483
  · exact B1495487
  · exact B1495491
  · exact B1495495
  · exact B1495499
  · exact B1495503
  · exact B1495507
  · exact B1495511
  · exact B1495515
  · exact B1495519
  · exact B1495523
  · exact B1495527
  · exact B1495531
  · exact B1495535
  · exact B1495539
  · exact B1495543
  · exact B1495547
  · exact B1495551
  · exact B1495555
  · exact B1495559
  · exact B1495563
  · exact B1495567
  · exact B1495571
  · exact B1495575
  · exact B1495579
  · exact B1495583
  · exact B1495587
  · exact B1495591
  · exact B1495595
  · exact B1495599
  · exact B1495603
  · exact B1495607
  · exact B1495611
  · exact B1495615
  · exact B1495619
  · exact B1495623
  · exact B1495627
  · exact B1495631
  · exact B1495635
  · exact B1495639
  · exact B1495643
  · exact B1495647
  · exact B1495651
  · exact B1495655
  · exact B1495659
  · exact B1495663
  · exact B1495667
  · exact B1495671
  · exact B1495675
  · exact B1495679
  · exact B1495683
  · exact B1495687
  · exact B1495691
  · exact B1495695
  · exact B1495699
  · exact B1495703
  · exact B1495707
  · exact B1495711
  · exact B1495715
  · exact B1495719
  · exact B1495723
  · exact B1495727
  · exact B1495731
  · exact B1495735
  · exact B1495739
  · exact B1495743
  · exact B1495747
  · exact B1495751
  · exact B1495755
  · exact B1495759
  · exact B1495763
  · exact B1495767
  · exact B1495771
  · exact B1495775
  · exact B1495779
  · exact B1495783
  · exact B1495787
  · exact B1495791
  · exact B1495795
  · exact B1495799
  · exact B1495803
  · exact B1495807
  · exact B1495811
  · exact B1495815
  · exact B1495819
  · exact B1495823
  · exact B1495827
  · exact B1495831
  · exact B1495835
  · exact B1495839
  · exact B1495843
  · exact B1495847
  · exact B1495851
  · exact B1495855
  · exact B1495859
  · exact B1495863
  · exact B1495867
  · exact B1495871
  · exact B1495875
  · exact B1495879
  · exact B1495883
  · exact B1495887
  · exact B1495891
  · exact B1495895
  · exact B1495899
  · exact B1495903
  · exact B1495907
  · exact B1495911
  · exact B1495915
  · exact B1495919
  · exact B1495923
  · exact B1495927
  · exact B1495931
  · exact B1495935
  · exact B1495939
  · exact B1495943
  · exact B1495947
  · exact B1495951
  · exact B1495955
  · exact B1495959
  · exact B1495963
  · exact B1495967
  · exact B1495971
  · exact B1495975
  · exact B1495979
  · exact B1495983
  · exact B1495987
  · exact B1495991
  · exact B1495995
  · exact B1495999
  · exact B1496003
  · exact B1496007
  · exact B1496011
  · exact B1496015
  · exact B1496019
  · exact B1496023
  · exact B1496027
  · exact B1496031
  · exact B1496035
  · exact B1496039
  · exact B1496043
  · exact B1496047
  · exact B1496051
  · exact B1496055
  · exact B1496059
  · exact B1496063
  · exact B1496067

theorem solution (m : ℕ) (hlo : 1494067 ≤ m) (hhi : m ≤ 1496067) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 373516 ≤ j := by omega
    have hj2 : j ≤ 374016 := by omega
    have hb : Blo 1494067 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
