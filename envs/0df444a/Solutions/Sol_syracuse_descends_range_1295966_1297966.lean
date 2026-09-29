-- Prove2me | solution 1 for syracuse_descends_range_1295966_1297966
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:25.453198+00:00
-- url     : https://prove2.me/submissions/45502b7b-f329-4e63-90e5-d8a61b1b0daa

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


theorem B1458193 : Blo 1295966 1458193 := bbase (se 2 (by rfl) ⟨546822, by rfl⟩ : syracuseStep 1458193 = 1093645) (by norm_num)
theorem B2187317 : Blo 1295966 2187317 := bbase (se 5 (by rfl) ⟨102530, by rfl⟩ : syracuseStep 2187317 = 205061) (by norm_num)
theorem B1458229 : Blo 1295966 1458229 := bbase (se 5 (by rfl) ⟨68354, by rfl⟩ : syracuseStep 1458229 = 136709) (by norm_num)
theorem B2916413 : Blo 1295966 2916413 := bbase (se 3 (by rfl) ⟨546827, by rfl⟩ : syracuseStep 2916413 = 1093655) (by norm_num)
theorem B2629693 : Blo 1295966 2629693 := bbase (se 3 (by rfl) ⟨493067, by rfl⟩ : syracuseStep 2629693 = 986135) (by norm_num)
theorem B1458265 : Blo 1295966 1458265 := bbase (se 2 (by rfl) ⟨546849, by rfl⟩ : syracuseStep 1458265 = 1093699) (by norm_num)
theorem B3694709 : Blo 1295966 3694709 := bbase (se 5 (by rfl) ⟨173189, by rfl⟩ : syracuseStep 3694709 = 346379) (by norm_num)
theorem B1458301 : Blo 1295966 1458301 := bbase (se 3 (by rfl) ⟨273431, by rfl⟩ : syracuseStep 1458301 = 546863) (by norm_num)
theorem B2629757 : Blo 1295966 2629757 := bbase (se 3 (by rfl) ⟨493079, by rfl⟩ : syracuseStep 2629757 = 986159) (by norm_num)
theorem B2916485 : Blo 1295966 2916485 := bbase (se 4 (by rfl) ⟨273420, by rfl⟩ : syracuseStep 2916485 = 546841) (by norm_num)
theorem B1458337 : Blo 1295966 1458337 := bbase (se 2 (by rfl) ⟨546876, by rfl⟩ : syracuseStep 1458337 = 1093753) (by norm_num)
theorem B3285157 : Blo 1295966 3285157 := bbase (se 4 (by rfl) ⟨307983, by rfl⟩ : syracuseStep 3285157 = 615967) (by norm_num)
theorem B2187445 : Blo 1295966 2187445 := bbase (se 5 (by rfl) ⟨102536, by rfl⟩ : syracuseStep 2187445 = 205073) (by norm_num)
theorem B1458373 : Blo 1295966 1458373 := bbase (se 4 (by rfl) ⟨136722, by rfl⟩ : syracuseStep 1458373 = 273445) (by norm_num)
theorem B2916557 : Blo 1295966 2916557 := bbase (se 3 (by rfl) ⟨546854, by rfl⟩ : syracuseStep 2916557 = 1093709) (by norm_num)
theorem B14016725 : Blo 1295966 14016725 := bbase (se 7 (by rfl) ⟨164258, by rfl⟩ : syracuseStep 14016725 = 328517) (by norm_num)
theorem B4923605 : Blo 1295966 4923605 := bbase (se 7 (by rfl) ⟨57698, by rfl⟩ : syracuseStep 4923605 = 115397) (by norm_num)
theorem B1458409 : Blo 1295966 1458409 := bbase (se 2 (by rfl) ⟨546903, by rfl⟩ : syracuseStep 1458409 = 1093807) (by norm_num)
theorem B2187533 : Blo 1295966 2187533 := bbase (se 3 (by rfl) ⟨410162, by rfl⟩ : syracuseStep 2187533 = 820325) (by norm_num)
theorem B1458445 : Blo 1295966 1458445 := bbase (se 3 (by rfl) ⟨273458, by rfl⟩ : syracuseStep 1458445 = 546917) (by norm_num)
theorem B2916629 : Blo 1295966 2916629 := bbase (se 6 (by rfl) ⟨68358, by rfl⟩ : syracuseStep 2916629 = 136717) (by norm_num)
theorem B3285269 : Blo 1295966 3285269 := bbase (se 6 (by rfl) ⟨76998, by rfl⟩ : syracuseStep 3285269 = 153997) (by norm_num)
theorem B1458481 : Blo 1295966 1458481 := bbase (se 2 (by rfl) ⟨546930, by rfl⟩ : syracuseStep 1458481 = 1093861) (by norm_num)
theorem B2769221 : Blo 1295966 2769221 := bbase (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) (by norm_num)
theorem B1384781 : Blo 1295966 1384781 := bbase (se 3 (by rfl) ⟨259646, by rfl⟩ : syracuseStep 1384781 = 519293) (by norm_num)
theorem B6562133 : Blo 1295966 6562133 := bbase (se 10 (by rfl) ⟨9612, by rfl⟩ : syracuseStep 6562133 = 19225) (by norm_num)
theorem B1458517 : Blo 1295966 1458517 := bbase (se 10 (by rfl) ⟨2136, by rfl⟩ : syracuseStep 1458517 = 4273) (by norm_num)
theorem B2916701 : Blo 1295966 2916701 := bbase (se 3 (by rfl) ⟨546881, by rfl⟩ : syracuseStep 2916701 = 1093763) (by norm_num)
theorem B1458553 : Blo 1295966 1458553 := bbase (se 2 (by rfl) ⟨546957, by rfl⟩ : syracuseStep 1458553 = 1093915) (by norm_num)
theorem B4374917 : Blo 1295966 4374917 := bbase (se 4 (by rfl) ⟨410148, by rfl⟩ : syracuseStep 4374917 = 820297) (by norm_num)
theorem B2187661 : Blo 1295966 2187661 := bbase (se 3 (by rfl) ⟨410186, by rfl⟩ : syracuseStep 2187661 = 820373) (by norm_num)
theorem B1458589 : Blo 1295966 1458589 := bbase (se 3 (by rfl) ⟨273485, by rfl⟩ : syracuseStep 1458589 = 546971) (by norm_num)
theorem B2916773 : Blo 1295966 2916773 := bbase (se 4 (by rfl) ⟨273447, by rfl⟩ : syracuseStep 2916773 = 546895) (by norm_num)
theorem B4153781 : Blo 1295966 4153781 := bbase (se 5 (by rfl) ⟨194708, by rfl⟩ : syracuseStep 4153781 = 389417) (by norm_num)
theorem B1458625 : Blo 1295966 1458625 := bbase (se 2 (by rfl) ⟨546984, by rfl⟩ : syracuseStep 1458625 = 1093969) (by norm_num)
theorem B3285461 : Blo 1295966 3285461 := bbase (se 7 (by rfl) ⟨38501, by rfl⟩ : syracuseStep 3285461 = 77003) (by norm_num)
theorem B2187749 : Blo 1295966 2187749 := bbase (se 4 (by rfl) ⟨205101, by rfl⟩ : syracuseStep 2187749 = 410203) (by norm_num)
theorem B1458661 : Blo 1295966 1458661 := bbase (se 4 (by rfl) ⟨136749, by rfl⟩ : syracuseStep 1458661 = 273499) (by norm_num)
theorem B2916845 : Blo 1295966 2916845 := bbase (se 3 (by rfl) ⟨546908, by rfl⟩ : syracuseStep 2916845 = 1093817) (by norm_num)
theorem B1458697 : Blo 1295966 1458697 := bbase (se 2 (by rfl) ⟨547011, by rfl⟩ : syracuseStep 1458697 = 1094023) (by norm_num)
theorem B1458733 : Blo 1295966 1458733 := bbase (se 3 (by rfl) ⟨273512, by rfl⟩ : syracuseStep 1458733 = 547025) (by norm_num)
theorem B2916917 : Blo 1295966 2916917 := bbase (se 5 (by rfl) ⟨136730, by rfl⟩ : syracuseStep 2916917 = 273461) (by norm_num)
theorem B1385029 : Blo 1295966 1385029 := bbase (se 4 (by rfl) ⟨129846, by rfl⟩ : syracuseStep 1385029 = 259693) (by norm_num)
theorem B1458769 : Blo 1295966 1458769 := bbase (se 2 (by rfl) ⟨547038, by rfl⟩ : syracuseStep 1458769 = 1094077) (by norm_num)
theorem B2187877 : Blo 1295966 2187877 := bbase (se 4 (by rfl) ⟨205113, by rfl⟩ : syracuseStep 2187877 = 410227) (by norm_num)
theorem B1458805 : Blo 1295966 1458805 := bbase (se 5 (by rfl) ⟨68381, by rfl⟩ : syracuseStep 1458805 = 136763) (by norm_num)
theorem B2916989 : Blo 1295966 2916989 := bbase (se 3 (by rfl) ⟨546935, by rfl⟩ : syracuseStep 2916989 = 1093871) (by norm_num)
theorem B1458841 : Blo 1295966 1458841 := bbase (se 2 (by rfl) ⟨547065, by rfl⟩ : syracuseStep 1458841 = 1094131) (by norm_num)
theorem B2187965 : Blo 1295966 2187965 := bbase (se 3 (by rfl) ⟨410243, by rfl⟩ : syracuseStep 2187965 = 820487) (by norm_num)
theorem B1458877 : Blo 1295966 1458877 := bbase (se 3 (by rfl) ⟨273539, by rfl⟩ : syracuseStep 1458877 = 547079) (by norm_num)
theorem B4735685 : Blo 1295966 4735685 := bbase (se 4 (by rfl) ⟨443970, by rfl⟩ : syracuseStep 4735685 = 887941) (by norm_num)
theorem B2917061 : Blo 1295966 2917061 := bbase (se 4 (by rfl) ⟨273474, by rfl⟩ : syracuseStep 2917061 = 546949) (by norm_num)
theorem B16622293 : Blo 1295966 16622293 := bbase (se 7 (by rfl) ⟨194792, by rfl⟩ : syracuseStep 16622293 = 389585) (by norm_num)
theorem B1458913 : Blo 1295966 1458913 := bbase (se 2 (by rfl) ⟨547092, by rfl⟩ : syracuseStep 1458913 = 1094185) (by norm_num)
theorem B1557245 : Blo 1295966 1557245 := bbase (se 3 (by rfl) ⟨291983, by rfl⟩ : syracuseStep 1557245 = 583967) (by norm_num)
theorem B1458949 : Blo 1295966 1458949 := bbase (se 4 (by rfl) ⟨136776, by rfl⟩ : syracuseStep 1458949 = 273553) (by norm_num)
theorem B2917133 : Blo 1295966 2917133 := bbase (se 3 (by rfl) ⟨546962, by rfl⟩ : syracuseStep 2917133 = 1093925) (by norm_num)
theorem B7013141 : Blo 1295966 7013141 := bbase (se 6 (by rfl) ⟨164370, by rfl⟩ : syracuseStep 7013141 = 328741) (by norm_num)
theorem B1458985 : Blo 1295966 1458985 := bbase (se 2 (by rfl) ⟨547119, by rfl⟩ : syracuseStep 1458985 = 1094239) (by norm_num)
theorem B4375349 : Blo 1295966 4375349 := bbase (se 5 (by rfl) ⟨205094, by rfl⟩ : syracuseStep 4375349 = 410189) (by norm_num)
theorem B5260085 : Blo 1295966 5260085 := bbase (se 5 (by rfl) ⟨246566, by rfl⟩ : syracuseStep 5260085 = 493133) (by norm_num)
theorem B2188093 : Blo 1295966 2188093 := bbase (se 3 (by rfl) ⟨410267, by rfl⟩ : syracuseStep 2188093 = 820535) (by norm_num)
theorem B1459021 : Blo 1295966 1459021 := bbase (se 3 (by rfl) ⟨273566, by rfl⟩ : syracuseStep 1459021 = 547133) (by norm_num)
theorem B2917205 : Blo 1295966 2917205 := bbase (se 9 (by rfl) ⟨8546, by rfl⟩ : syracuseStep 2917205 = 17093) (by norm_num)
theorem B1459057 : Blo 1295966 1459057 := bbase (se 2 (by rfl) ⟨547146, by rfl⟩ : syracuseStep 1459057 = 1094293) (by norm_num)
theorem B2335637 : Blo 1295966 2335637 := bbase (se 6 (by rfl) ⟨54741, by rfl⟩ : syracuseStep 2335637 = 109483) (by norm_num)
theorem B2188181 : Blo 1295966 2188181 := bbase (se 6 (by rfl) ⟨51285, by rfl⟩ : syracuseStep 2188181 = 102571) (by norm_num)
theorem B1459093 : Blo 1295966 1459093 := bbase (se 6 (by rfl) ⟨34197, by rfl⟩ : syracuseStep 1459093 = 68395) (by norm_num)
theorem B2917277 : Blo 1295966 2917277 := bbase (se 3 (by rfl) ⟨546989, by rfl⟩ : syracuseStep 2917277 = 1093979) (by norm_num)
theorem B1459129 : Blo 1295966 1459129 := bbase (se 2 (by rfl) ⟨547173, by rfl⟩ : syracuseStep 1459129 = 1094347) (by norm_num)
theorem B1459165 : Blo 1295966 1459165 := bbase (se 3 (by rfl) ⟨273593, by rfl⟩ : syracuseStep 1459165 = 547187) (by norm_num)
theorem B2917349 : Blo 1295966 2917349 := bbase (se 4 (by rfl) ⟨273501, by rfl⟩ : syracuseStep 2917349 = 547003) (by norm_num)
theorem B1385461 : Blo 1295966 1385461 := bbase (se 5 (by rfl) ⟨64943, by rfl⟩ : syracuseStep 1385461 = 129887) (by norm_num)
theorem B3113981 : Blo 1295966 3113981 := bbase (se 3 (by rfl) ⟨583871, by rfl⟩ : syracuseStep 3113981 = 1167743) (by norm_num)
theorem B1557505 : Blo 1295966 1557505 := bbase (se 2 (by rfl) ⟨584064, by rfl⟩ : syracuseStep 1557505 = 1168129) (by norm_num)
theorem B1459201 : Blo 1295966 1459201 := bbase (se 2 (by rfl) ⟨547200, by rfl⟩ : syracuseStep 1459201 = 1094401) (by norm_num)
theorem B2188309 : Blo 1295966 2188309 := bbase (se 6 (by rfl) ⟨51288, by rfl⟩ : syracuseStep 2188309 = 102577) (by norm_num)
theorem B1459237 : Blo 1295966 1459237 := bbase (se 4 (by rfl) ⟨136803, by rfl⟩ : syracuseStep 1459237 = 273607) (by norm_num)
theorem B2917421 : Blo 1295966 2917421 := bbase (se 3 (by rfl) ⟨547016, by rfl⟩ : syracuseStep 2917421 = 1094033) (by norm_num)
theorem B1385533 : Blo 1295966 1385533 := bbase (se 3 (by rfl) ⟨259787, by rfl⟩ : syracuseStep 1385533 = 519575) (by norm_num)
theorem B1459273 : Blo 1295966 1459273 := bbase (se 2 (by rfl) ⟨547227, by rfl⟩ : syracuseStep 1459273 = 1094455) (by norm_num)
theorem B1664077 : Blo 1295966 1664077 := bbase (se 3 (by rfl) ⟨312014, by rfl⟩ : syracuseStep 1664077 = 624029) (by norm_num)
theorem B1999949 : Blo 1295966 1999949 := bbase (se 3 (by rfl) ⟨374990, by rfl⟩ : syracuseStep 1999949 = 749981) (by norm_num)
theorem B5260373 : Blo 1295966 5260373 := bbase (se 8 (by rfl) ⟨30822, by rfl⟩ : syracuseStep 5260373 = 61645) (by norm_num)
theorem B2188397 : Blo 1295966 2188397 := bbase (se 3 (by rfl) ⟨410324, by rfl⟩ : syracuseStep 2188397 = 820649) (by norm_num)
theorem B1459309 : Blo 1295966 1459309 := bbase (se 3 (by rfl) ⟨273620, by rfl⟩ : syracuseStep 1459309 = 547241) (by norm_num)
theorem B2917493 : Blo 1295966 2917493 := bbase (se 5 (by rfl) ⟨136757, by rfl⟩ : syracuseStep 2917493 = 273515) (by norm_num)
theorem B1459345 : Blo 1295966 1459345 := bbase (se 2 (by rfl) ⟨547254, by rfl⟩ : syracuseStep 1459345 = 1094509) (by norm_num)
theorem B1459381 : Blo 1295966 1459381 := bbase (se 5 (by rfl) ⟨68408, by rfl⟩ : syracuseStep 1459381 = 136817) (by norm_num)
theorem B2917565 : Blo 1295966 2917565 := bbase (se 3 (by rfl) ⟨547043, by rfl⟩ : syracuseStep 2917565 = 1094087) (by norm_num)
theorem B1557697 : Blo 1295966 1557697 := bbase (se 2 (by rfl) ⟨584136, by rfl⟩ : syracuseStep 1557697 = 1168273) (by norm_num)
theorem B1557721 : Blo 1295966 1557721 := bbase (se 2 (by rfl) ⟨584145, by rfl⟩ : syracuseStep 1557721 = 1168291) (by norm_num)
theorem B1459417 : Blo 1295966 1459417 := bbase (se 2 (by rfl) ⟨547281, by rfl⟩ : syracuseStep 1459417 = 1094563) (by norm_num)
theorem B1557725 : Blo 1295966 1557725 := bbase (se 3 (by rfl) ⟨292073, by rfl⟩ : syracuseStep 1557725 = 584147) (by norm_num)
theorem B4375781 : Blo 1295966 4375781 := bbase (se 4 (by rfl) ⟨410229, by rfl⟩ : syracuseStep 4375781 = 820459) (by norm_num)
theorem B2188525 : Blo 1295966 2188525 := bbase (se 3 (by rfl) ⟨410348, by rfl⟩ : syracuseStep 2188525 = 820697) (by norm_num)
theorem B1443065 : Blo 1295966 1443065 := bbase (se 2 (by rfl) ⟨541149, by rfl⟩ : syracuseStep 1443065 = 1082299) (by norm_num)
theorem B1459453 : Blo 1295966 1459453 := bbase (se 3 (by rfl) ⟨273647, by rfl⟩ : syracuseStep 1459453 = 547295) (by norm_num)
theorem B2917637 : Blo 1295966 2917637 := bbase (se 4 (by rfl) ⟨273528, by rfl⟩ : syracuseStep 2917637 = 547057) (by norm_num)
theorem B1459489 : Blo 1295966 1459489 := bbase (se 2 (by rfl) ⟨547308, by rfl⟩ : syracuseStep 1459489 = 1094617) (by norm_num)
theorem B2188613 : Blo 1295966 2188613 := bbase (se 4 (by rfl) ⟨205182, by rfl⟩ : syracuseStep 2188613 = 410365) (by norm_num)
theorem B1459525 : Blo 1295966 1459525 := bbase (se 4 (by rfl) ⟨136830, by rfl⟩ : syracuseStep 1459525 = 273661) (by norm_num)
theorem B2917709 : Blo 1295966 2917709 := bbase (se 3 (by rfl) ⟨547070, by rfl⟩ : syracuseStep 2917709 = 1094141) (by norm_num)
theorem B1459561 : Blo 1295966 1459561 := bbase (se 2 (by rfl) ⟨547335, by rfl⟩ : syracuseStep 1459561 = 1094671) (by norm_num)
theorem B1459597 : Blo 1295966 1459597 := bbase (se 3 (by rfl) ⟨273674, by rfl⟩ : syracuseStep 1459597 = 547349) (by norm_num)
theorem B2917781 : Blo 1295966 2917781 := bbase (se 6 (by rfl) ⟨68385, by rfl⟩ : syracuseStep 2917781 = 136771) (by norm_num)
theorem B1459633 : Blo 1295966 1459633 := bbase (se 2 (by rfl) ⟨547362, by rfl⟩ : syracuseStep 1459633 = 1094725) (by norm_num)
theorem B1385905 : Blo 1295966 1385905 := bbase (se 2 (by rfl) ⟨519714, by rfl⟩ : syracuseStep 1385905 = 1039429) (by norm_num)
theorem B2188741 : Blo 1295966 2188741 := bbase (se 4 (by rfl) ⟨205194, by rfl⟩ : syracuseStep 2188741 = 410389) (by norm_num)
theorem B1459669 : Blo 1295966 1459669 := bbase (se 7 (by rfl) ⟨17105, by rfl⟩ : syracuseStep 1459669 = 34211) (by norm_num)
theorem B2917853 : Blo 1295966 2917853 := bbase (se 3 (by rfl) ⟨547097, by rfl⟩ : syracuseStep 2917853 = 1094195) (by norm_num)
theorem B1459705 : Blo 1295966 1459705 := bbase (se 2 (by rfl) ⟨547389, by rfl⟩ : syracuseStep 1459705 = 1094779) (by norm_num)
theorem B3327517 : Blo 1295966 3327517 := bbase (se 3 (by rfl) ⟨623909, by rfl⟩ : syracuseStep 3327517 = 1247819) (by norm_num)
theorem B2188829 : Blo 1295966 2188829 := bbase (se 3 (by rfl) ⟨410405, by rfl⟩ : syracuseStep 2188829 = 820811) (by norm_num)
theorem B1459741 : Blo 1295966 1459741 := bbase (se 3 (by rfl) ⟨273701, by rfl⟩ : syracuseStep 1459741 = 547403) (by norm_num)
theorem B2336293 : Blo 1295966 2336293 := bbase (se 4 (by rfl) ⟨219027, by rfl⟩ : syracuseStep 2336293 = 438055) (by norm_num)
theorem B2917925 : Blo 1295966 2917925 := bbase (se 4 (by rfl) ⟨273555, by rfl⟩ : syracuseStep 2917925 = 547111) (by norm_num)
theorem B8308277 : Blo 1295966 8308277 := bbase (se 5 (by rfl) ⟨389450, by rfl⟩ : syracuseStep 8308277 = 778901) (by norm_num)
theorem B1459777 : Blo 1295966 1459777 := bbase (se 2 (by rfl) ⟨547416, by rfl⟩ : syracuseStep 1459777 = 1094833) (by norm_num)
theorem B3507781 : Blo 1295966 3507781 := bbase (se 4 (by rfl) ⟨328854, by rfl⟩ : syracuseStep 3507781 = 657709) (by norm_num)
theorem B6563429 : Blo 1295966 6563429 := bbase (se 4 (by rfl) ⟨615321, by rfl⟩ : syracuseStep 6563429 = 1230643) (by norm_num)
theorem B2336357 : Blo 1295966 2336357 := bbase (se 4 (by rfl) ⟨219033, by rfl⟩ : syracuseStep 2336357 = 438067) (by norm_num)
theorem B3114605 : Blo 1295966 3114605 := bbase (se 3 (by rfl) ⟨583988, by rfl⟩ : syracuseStep 3114605 = 1167977) (by norm_num)
theorem B2917997 : Blo 1295966 2917997 := bbase (se 3 (by rfl) ⟨547124, by rfl⟩ : syracuseStep 2917997 = 1094249) (by norm_num)
theorem B1459849 : Blo 1295966 1459849 := bbase (se 2 (by rfl) ⟨547443, by rfl⟩ : syracuseStep 1459849 = 1094887) (by norm_num)
theorem B4376213 : Blo 1295966 4376213 := bbase (se 6 (by rfl) ⟨102567, by rfl⟩ : syracuseStep 4376213 = 205135) (by norm_num)
theorem B2188957 : Blo 1295966 2188957 := bbase (se 3 (by rfl) ⟨410429, by rfl⟩ : syracuseStep 2188957 = 820859) (by norm_num)
theorem B1459885 : Blo 1295966 1459885 := bbase (se 3 (by rfl) ⟨273728, by rfl⟩ : syracuseStep 1459885 = 547457) (by norm_num)
theorem B2918069 : Blo 1295966 2918069 := bbase (se 5 (by rfl) ⟨136784, by rfl⟩ : syracuseStep 2918069 = 273569) (by norm_num)
theorem B1558225 : Blo 1295966 1558225 := bbase (se 2 (by rfl) ⟨584334, by rfl⟩ : syracuseStep 1558225 = 1168669) (by norm_num)
theorem B1459921 : Blo 1295966 1459921 := bbase (se 2 (by rfl) ⟨547470, by rfl⟩ : syracuseStep 1459921 = 1094941) (by norm_num)
theorem B2189045 : Blo 1295966 2189045 := bbase (se 5 (by rfl) ⟨102611, by rfl⟩ : syracuseStep 2189045 = 205223) (by norm_num)
theorem B1459957 : Blo 1295966 1459957 := bbase (se 5 (by rfl) ⟨68435, by rfl⟩ : syracuseStep 1459957 = 136871) (by norm_num)
theorem B2918141 : Blo 1295966 2918141 := bbase (se 3 (by rfl) ⟨547151, by rfl⟩ : syracuseStep 2918141 = 1094303) (by norm_num)
theorem B11077397 : Blo 1295966 11077397 := bbase (se 6 (by rfl) ⟨259626, by rfl⟩ : syracuseStep 11077397 = 519253) (by norm_num)
theorem B1459993 : Blo 1295966 1459993 := bbase (se 2 (by rfl) ⟨547497, by rfl⟩ : syracuseStep 1459993 = 1094995) (by norm_num)
theorem B1558321 : Blo 1295966 1558321 := bbase (se 2 (by rfl) ⟨584370, by rfl⟩ : syracuseStep 1558321 = 1168741) (by norm_num)
theorem B1640245 : Blo 1295966 1640245 := bbase (se 5 (by rfl) ⟨76886, by rfl⟩ : syracuseStep 1640245 = 153773) (by norm_num)
theorem B6235957 : Blo 1295966 6235957 := bbase (se 5 (by rfl) ⟨292310, by rfl⟩ : syracuseStep 6235957 = 584621) (by norm_num)
theorem B1460029 : Blo 1295966 1460029 := bbase (se 3 (by rfl) ⟨273755, by rfl⟩ : syracuseStep 1460029 = 547511) (by norm_num)
theorem B2918213 : Blo 1295966 2918213 := bbase (se 4 (by rfl) ⟨273582, by rfl⟩ : syracuseStep 2918213 = 547165) (by norm_num)
theorem B1460065 : Blo 1295966 1460065 := bbase (se 2 (by rfl) ⟨547524, by rfl⟩ : syracuseStep 1460065 = 1095049) (by norm_num)
theorem B2189173 : Blo 1295966 2189173 := bbase (se 5 (by rfl) ⟨102617, by rfl⟩ : syracuseStep 2189173 = 205235) (by norm_num)
theorem B1460101 : Blo 1295966 1460101 := bbase (se 4 (by rfl) ⟨136884, by rfl⟩ : syracuseStep 1460101 = 273769) (by norm_num)
theorem B2918285 : Blo 1295966 2918285 := bbase (se 3 (by rfl) ⟨547178, by rfl⟩ : syracuseStep 2918285 = 1094357) (by norm_num)
theorem B1640341 : Blo 1295966 1640341 := bbase (se 6 (by rfl) ⟨38445, by rfl⟩ : syracuseStep 1640341 = 76891) (by norm_num)
theorem B1460137 : Blo 1295966 1460137 := bbase (se 2 (by rfl) ⟨547551, by rfl⟩ : syracuseStep 1460137 = 1095103) (by norm_num)
theorem B2770861 : Blo 1295966 2770861 := bbase (se 3 (by rfl) ⟨519536, by rfl⟩ : syracuseStep 2770861 = 1039073) (by norm_num)
theorem B2189261 : Blo 1295966 2189261 := bbase (se 3 (by rfl) ⟨410486, by rfl⟩ : syracuseStep 2189261 = 820973) (by norm_num)
theorem B1460173 : Blo 1295966 1460173 := bbase (se 3 (by rfl) ⟨273782, by rfl⟩ : syracuseStep 1460173 = 547565) (by norm_num)
theorem B9848789 : Blo 1295966 9848789 := bbase (se 7 (by rfl) ⟨115415, by rfl⟩ : syracuseStep 9848789 = 230831) (by norm_num)
theorem B2918357 : Blo 1295966 2918357 := bbase (se 7 (by rfl) ⟨34199, by rfl⟩ : syracuseStep 2918357 = 68399) (by norm_num)
theorem B1460209 : Blo 1295966 1460209 := bbase (se 2 (by rfl) ⟨547578, by rfl⟩ : syracuseStep 1460209 = 1095157) (by norm_num)
theorem B2918429 : Blo 1295966 2918429 := bbase (se 3 (by rfl) ⟨547205, by rfl⟩ : syracuseStep 2918429 = 1094411) (by norm_num)
theorem B5539877 : Blo 1295966 5539877 := bbase (se 4 (by rfl) ⟨519363, by rfl⟩ : syracuseStep 5539877 = 1038727) (by norm_num)
theorem B1640513 : Blo 1295966 1640513 := bbase (se 2 (by rfl) ⟨615192, by rfl⟩ : syracuseStep 1640513 = 1230385) (by norm_num)
theorem B4376645 : Blo 1295966 4376645 := bbase (se 4 (by rfl) ⟨410310, by rfl⟩ : syracuseStep 4376645 = 820621) (by norm_num)
theorem B5261381 : Blo 1295966 5261381 := bbase (se 4 (by rfl) ⟨493254, by rfl⟩ : syracuseStep 5261381 = 986509) (by norm_num)
theorem B2189389 : Blo 1295966 2189389 := bbase (se 3 (by rfl) ⟨410510, by rfl⟩ : syracuseStep 2189389 = 821021) (by norm_num)
theorem B2918501 : Blo 1295966 2918501 := bbase (se 4 (by rfl) ⟨273609, by rfl⟩ : syracuseStep 2918501 = 547219) (by norm_num)
theorem B1640569 : Blo 1295966 1640569 := bbase (se 2 (by rfl) ⟨615213, by rfl⟩ : syracuseStep 1640569 = 1230427) (by norm_num)
theorem B2435221 : Blo 1295966 2435221 := bbase (se 6 (by rfl) ⟨57075, by rfl⟩ : syracuseStep 2435221 = 114151) (by norm_num)
theorem B2189477 : Blo 1295966 2189477 := bbase (se 4 (by rfl) ⟨205263, by rfl⟩ : syracuseStep 2189477 = 410527) (by norm_num)
theorem B2918573 : Blo 1295966 2918573 := bbase (se 3 (by rfl) ⟨547232, by rfl⟩ : syracuseStep 2918573 = 1094465) (by norm_num)
theorem B7383221 : Blo 1295966 7383221 := bbase (se 5 (by rfl) ⟨346088, by rfl⟩ : syracuseStep 7383221 = 692177) (by norm_num)
theorem B2959573 : Blo 1295966 2959573 := bbase (se 7 (by rfl) ⟨34682, by rfl⟩ : syracuseStep 2959573 = 69365) (by norm_num)
theorem B1640665 : Blo 1295966 1640665 := bbase (se 2 (by rfl) ⟨615249, by rfl⟩ : syracuseStep 1640665 = 1230499) (by norm_num)
theorem B2664677 : Blo 1295966 2664677 := bbase (se 4 (by rfl) ⟨249813, by rfl⟩ : syracuseStep 2664677 = 499627) (by norm_num)
theorem B2918645 : Blo 1295966 2918645 := bbase (se 5 (by rfl) ⟨136811, by rfl⟩ : syracuseStep 2918645 = 273623) (by norm_num)
theorem B1845509 : Blo 1295966 1845509 := bbase (se 4 (by rfl) ⟨173016, by rfl⟩ : syracuseStep 1845509 = 346033) (by norm_num)
theorem B4925717 : Blo 1295966 4925717 := bbase (se 6 (by rfl) ⟨115446, by rfl⟩ : syracuseStep 4925717 = 230893) (by norm_num)
theorem B2189605 : Blo 1295966 2189605 := bbase (se 4 (by rfl) ⟨205275, by rfl⟩ : syracuseStep 2189605 = 410551) (by norm_num)
theorem B2918717 : Blo 1295966 2918717 := bbase (se 3 (by rfl) ⟨547259, by rfl⟩ : syracuseStep 2918717 = 1094519) (by norm_num)
theorem B2189693 : Blo 1295966 2189693 := bbase (se 3 (by rfl) ⟨410567, by rfl⟩ : syracuseStep 2189693 = 821135) (by norm_num)
theorem B1640837 : Blo 1295966 1640837 := bbase (se 4 (by rfl) ⟨153828, by rfl⟩ : syracuseStep 1640837 = 307657) (by norm_num)
theorem B2918789 : Blo 1295966 2918789 := bbase (se 4 (by rfl) ⟨273636, by rfl⟩ : syracuseStep 2918789 = 547273) (by norm_num)
theorem B1943957 : Blo 1295966 1943957 := bbase (se 6 (by rfl) ⟨45561, by rfl⟩ : syracuseStep 1943957 = 91123) (by norm_num)
theorem B1943981 : Blo 1295966 1943981 := bbase (se 3 (by rfl) ⟨364496, by rfl⟩ : syracuseStep 1943981 = 728993) (by norm_num)
theorem B1599925 : Blo 1295966 1599925 := bbase (se 5 (by rfl) ⟨74996, by rfl⟩ : syracuseStep 1599925 = 149993) (by norm_num)
theorem B1640893 : Blo 1295966 1640893 := bbase (se 3 (by rfl) ⟨307667, by rfl⟩ : syracuseStep 1640893 = 615335) (by norm_num)
theorem B1403329 : Blo 1295966 1403329 := bbase (se 2 (by rfl) ⟨526248, by rfl⟩ : syracuseStep 1403329 = 1052497) (by norm_num)
theorem B1944005 : Blo 1295966 1944005 := bbase (se 4 (by rfl) ⟨182250, by rfl⟩ : syracuseStep 1944005 = 364501) (by norm_num)
theorem B2918861 : Blo 1295966 2918861 := bbase (se 3 (by rfl) ⟨547286, by rfl⟩ : syracuseStep 2918861 = 1094573) (by norm_num)
theorem B1944029 : Blo 1295966 1944029 := bbase (se 3 (by rfl) ⟨364505, by rfl⟩ : syracuseStep 1944029 = 729011) (by norm_num)
theorem B5917157 : Blo 1295966 5917157 := bbase (se 4 (by rfl) ⟨554733, by rfl⟩ : syracuseStep 5917157 = 1109467) (by norm_num)
theorem B1944053 : Blo 1295966 1944053 := bbase (se 5 (by rfl) ⟨91127, by rfl⟩ : syracuseStep 1944053 = 182255) (by norm_num)
theorem B4377077 : Blo 1295966 4377077 := bbase (se 5 (by rfl) ⟨205175, by rfl⟩ : syracuseStep 4377077 = 410351) (by norm_num)
theorem B2189821 : Blo 1295966 2189821 := bbase (se 3 (by rfl) ⟨410591, by rfl⟩ : syracuseStep 2189821 = 821183) (by norm_num)
theorem B1944077 : Blo 1295966 1944077 := bbase (se 3 (by rfl) ⟨364514, by rfl⟩ : syracuseStep 1944077 = 729029) (by norm_num)
theorem B2918933 : Blo 1295966 2918933 := bbase (se 6 (by rfl) ⟨68412, by rfl⟩ : syracuseStep 2918933 = 136825) (by norm_num)
theorem B1640989 : Blo 1295966 1640989 := bbase (se 3 (by rfl) ⟨307685, by rfl⟩ : syracuseStep 1640989 = 615371) (by norm_num)
theorem B1944101 : Blo 1295966 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B4926005 : Blo 1295966 4926005 := bbase (se 5 (by rfl) ⟨230906, by rfl⟩ : syracuseStep 4926005 = 461813) (by norm_num)
theorem B1944125 : Blo 1295966 1944125 := bbase (se 3 (by rfl) ⟨364523, by rfl⟩ : syracuseStep 1944125 = 729047) (by norm_num)
theorem B1944149 : Blo 1295966 1944149 := bbase (se 8 (by rfl) ⟨11391, by rfl⟩ : syracuseStep 1944149 = 22783) (by norm_num)
theorem B2189909 : Blo 1295966 2189909 := bbase (se 8 (by rfl) ⟨12831, by rfl⟩ : syracuseStep 2189909 = 25663) (by norm_num)
theorem B2919005 : Blo 1295966 2919005 := bbase (se 3 (by rfl) ⟨547313, by rfl⟩ : syracuseStep 2919005 = 1094627) (by norm_num)
theorem B1944173 : Blo 1295966 1944173 := bbase (se 3 (by rfl) ⟨364532, by rfl⟩ : syracuseStep 1944173 = 729065) (by norm_num)
theorem B1944197 : Blo 1295966 1944197 := bbase (se 4 (by rfl) ⟨182268, by rfl⟩ : syracuseStep 1944197 = 364537) (by norm_num)
theorem B1944221 : Blo 1295966 1944221 := bbase (se 3 (by rfl) ⟨364541, by rfl⟩ : syracuseStep 1944221 = 729083) (by norm_num)
theorem B2919077 : Blo 1295966 2919077 := bbase (se 4 (by rfl) ⟨273663, by rfl⟩ : syracuseStep 2919077 = 547327) (by norm_num)
theorem B1944245 : Blo 1295966 1944245 := bbase (se 5 (by rfl) ⟨91136, by rfl⟩ : syracuseStep 1944245 = 182273) (by norm_num)
theorem B1641161 : Blo 1295966 1641161 := bbase (se 2 (by rfl) ⟨615435, by rfl⟩ : syracuseStep 1641161 = 1230871) (by norm_num)
theorem B1944269 : Blo 1295966 1944269 := bbase (se 3 (by rfl) ⟨364550, by rfl⟩ : syracuseStep 1944269 = 729101) (by norm_num)
theorem B17984213 : Blo 1295966 17984213 := bbase (se 7 (by rfl) ⟨210752, by rfl⟩ : syracuseStep 17984213 = 421505) (by norm_num)
theorem B2190037 : Blo 1295966 2190037 := bbase (se 7 (by rfl) ⟨25664, by rfl⟩ : syracuseStep 2190037 = 51329) (by norm_num)
theorem B1944293 : Blo 1295966 1944293 := bbase (se 4 (by rfl) ⟨182277, by rfl⟩ : syracuseStep 1944293 = 364555) (by norm_num)
theorem B2919149 : Blo 1295966 2919149 := bbase (se 3 (by rfl) ⟨547340, by rfl⟩ : syracuseStep 2919149 = 1094681) (by norm_num)
theorem B1944317 : Blo 1295966 1944317 := bbase (se 3 (by rfl) ⟨364559, by rfl⟩ : syracuseStep 1944317 = 729119) (by norm_num)
theorem B1641217 : Blo 1295966 1641217 := bbase (se 2 (by rfl) ⟨615456, by rfl⟩ : syracuseStep 1641217 = 1230913) (by norm_num)
theorem B1559297 : Blo 1295966 1559297 := bbase (se 2 (by rfl) ⟨584736, by rfl⟩ : syracuseStep 1559297 = 1169473) (by norm_num)
theorem B1944341 : Blo 1295966 1944341 := bbase (se 6 (by rfl) ⟨45570, by rfl⟩ : syracuseStep 1944341 = 91141) (by norm_num)
theorem B2771749 : Blo 1295966 2771749 := bbase (se 4 (by rfl) ⟨259851, by rfl⟩ : syracuseStep 2771749 = 519703) (by norm_num)
theorem B1944365 : Blo 1295966 1944365 := bbase (se 3 (by rfl) ⟨364568, by rfl⟩ : syracuseStep 1944365 = 729137) (by norm_num)
theorem B2190125 : Blo 1295966 2190125 := bbase (se 3 (by rfl) ⟨410648, by rfl⟩ : syracuseStep 2190125 = 821297) (by norm_num)
theorem B2919221 : Blo 1295966 2919221 := bbase (se 5 (by rfl) ⟨136838, by rfl⟩ : syracuseStep 2919221 = 273677) (by norm_num)
theorem B1944389 : Blo 1295966 1944389 := bbase (se 4 (by rfl) ⟨182286, by rfl⟩ : syracuseStep 1944389 = 364573) (by norm_num)
theorem B1944413 : Blo 1295966 1944413 := bbase (se 3 (by rfl) ⟨364577, by rfl⟩ : syracuseStep 1944413 = 729155) (by norm_num)
theorem B1641313 : Blo 1295966 1641313 := bbase (se 2 (by rfl) ⟨615492, by rfl⟩ : syracuseStep 1641313 = 1230985) (by norm_num)
theorem B1944437 : Blo 1295966 1944437 := bbase (se 5 (by rfl) ⟨91145, by rfl⟩ : syracuseStep 1944437 = 182291) (by norm_num)
theorem B6564725 : Blo 1295966 6564725 := bbase (se 5 (by rfl) ⟨307721, by rfl⟩ : syracuseStep 6564725 = 615443) (by norm_num)
theorem B2919293 : Blo 1295966 2919293 := bbase (se 3 (by rfl) ⟨547367, by rfl⟩ : syracuseStep 2919293 = 1094735) (by norm_num)
theorem B2460557 : Blo 1295966 2460557 := bbase (se 3 (by rfl) ⟨461354, by rfl⟩ : syracuseStep 2460557 = 922709) (by norm_num)
theorem B1944461 : Blo 1295966 1944461 := bbase (se 3 (by rfl) ⟨364586, by rfl⟩ : syracuseStep 1944461 = 729173) (by norm_num)
theorem B1944485 : Blo 1295966 1944485 := bbase (se 4 (by rfl) ⟨182295, by rfl⟩ : syracuseStep 1944485 = 364591) (by norm_num)
theorem B4377509 : Blo 1295966 4377509 := bbase (se 4 (by rfl) ⟨410391, by rfl⟩ : syracuseStep 4377509 = 820783) (by norm_num)
theorem B2190253 : Blo 1295966 2190253 := bbase (se 3 (by rfl) ⟨410672, by rfl⟩ : syracuseStep 2190253 = 821345) (by norm_num)
theorem B1944509 : Blo 1295966 1944509 := bbase (se 3 (by rfl) ⟨364595, by rfl⟩ : syracuseStep 1944509 = 729191) (by norm_num)
theorem B2919365 : Blo 1295966 2919365 := bbase (se 4 (by rfl) ⟨273690, by rfl⟩ : syracuseStep 2919365 = 547381) (by norm_num)
theorem B1944533 : Blo 1295966 1944533 := bbase (se 7 (by rfl) ⟨22787, by rfl⟩ : syracuseStep 1944533 = 45575) (by norm_num)
theorem B9989077 : Blo 1295966 9989077 := bbase (se 7 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 9989077 = 234119) (by norm_num)
theorem B1944557 : Blo 1295966 1944557 := bbase (se 3 (by rfl) ⟨364604, by rfl⟩ : syracuseStep 1944557 = 729209) (by norm_num)
theorem B1846261 : Blo 1295966 1846261 := bbase (se 5 (by rfl) ⟨86543, by rfl⟩ : syracuseStep 1846261 = 173087) (by norm_num)
theorem B1944581 : Blo 1295966 1944581 := bbase (se 4 (by rfl) ⟨182304, by rfl⟩ : syracuseStep 1944581 = 364609) (by norm_num)
theorem B1641485 : Blo 1295966 1641485 := bbase (se 3 (by rfl) ⟨307778, by rfl⟩ : syracuseStep 1641485 = 615557) (by norm_num)
theorem B2919437 : Blo 1295966 2919437 := bbase (se 3 (by rfl) ⟨547394, by rfl⟩ : syracuseStep 2919437 = 1094789) (by norm_num)
theorem B1944605 : Blo 1295966 1944605 := bbase (se 3 (by rfl) ⟨364613, by rfl⟩ : syracuseStep 1944605 = 729227) (by norm_num)
theorem B2460709 : Blo 1295966 2460709 := bbase (se 4 (by rfl) ⟨230691, by rfl⟩ : syracuseStep 2460709 = 461383) (by norm_num)
theorem B1944629 : Blo 1295966 1944629 := bbase (se 5 (by rfl) ⟨91154, by rfl⟩ : syracuseStep 1944629 = 182309) (by norm_num)
theorem B1641541 : Blo 1295966 1641541 := bbase (se 4 (by rfl) ⟨153894, by rfl⟩ : syracuseStep 1641541 = 307789) (by norm_num)
theorem B1944653 : Blo 1295966 1944653 := bbase (se 3 (by rfl) ⟨364622, by rfl⟩ : syracuseStep 1944653 = 729245) (by norm_num)
theorem B2919509 : Blo 1295966 2919509 := bbase (se 8 (by rfl) ⟨17106, by rfl⟩ : syracuseStep 2919509 = 34213) (by norm_num)
theorem B1944677 : Blo 1295966 1944677 := bbase (se 4 (by rfl) ⟨182313, by rfl⟩ : syracuseStep 1944677 = 364627) (by norm_num)
theorem B1944701 : Blo 1295966 1944701 := bbase (se 3 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 1944701 = 729263) (by norm_num)
theorem B1944725 : Blo 1295966 1944725 := bbase (se 6 (by rfl) ⟨45579, by rfl⟩ : syracuseStep 1944725 = 91159) (by norm_num)
theorem B2919581 : Blo 1295966 2919581 := bbase (se 3 (by rfl) ⟨547421, by rfl⟩ : syracuseStep 2919581 = 1094843) (by norm_num)
theorem B1641637 : Blo 1295966 1641637 := bbase (se 4 (by rfl) ⟨153903, by rfl⟩ : syracuseStep 1641637 = 307807) (by norm_num)
theorem B1944749 : Blo 1295966 1944749 := bbase (se 3 (by rfl) ⟨364640, by rfl⟩ : syracuseStep 1944749 = 729281) (by norm_num)
theorem B1944773 : Blo 1295966 1944773 := bbase (se 4 (by rfl) ⟨182322, by rfl⟩ : syracuseStep 1944773 = 364645) (by norm_num)
theorem B1944797 : Blo 1295966 1944797 := bbase (se 3 (by rfl) ⟨364649, by rfl⟩ : syracuseStep 1944797 = 729299) (by norm_num)
theorem B2919653 : Blo 1295966 2919653 := bbase (se 4 (by rfl) ⟨273717, by rfl⟩ : syracuseStep 2919653 = 547435) (by norm_num)
theorem B1944821 : Blo 1295966 1944821 := bbase (se 5 (by rfl) ⟨91163, by rfl⟩ : syracuseStep 1944821 = 182327) (by norm_num)
theorem B1944845 : Blo 1295966 1944845 := bbase (se 3 (by rfl) ⟨364658, by rfl⟩ : syracuseStep 1944845 = 729317) (by norm_num)
theorem B1944869 : Blo 1295966 1944869 := bbase (se 4 (by rfl) ⟨182331, by rfl⟩ : syracuseStep 1944869 = 364663) (by norm_num)
theorem B2919725 : Blo 1295966 2919725 := bbase (se 3 (by rfl) ⟨547448, by rfl⟩ : syracuseStep 2919725 = 1094897) (by norm_num)
theorem B1944893 : Blo 1295966 1944893 := bbase (se 3 (by rfl) ⟨364667, by rfl⟩ : syracuseStep 1944893 = 729335) (by norm_num)
theorem B1641809 : Blo 1295966 1641809 := bbase (se 2 (by rfl) ⟨615678, by rfl⟩ : syracuseStep 1641809 = 1231357) (by norm_num)
theorem B2461013 : Blo 1295966 2461013 := bbase (se 11 (by rfl) ⟨1802, by rfl⟩ : syracuseStep 2461013 = 3605) (by norm_num)
theorem B7384405 : Blo 1295966 7384405 := bbase (se 11 (by rfl) ⟨5408, by rfl⟩ : syracuseStep 7384405 = 10817) (by norm_num)
theorem B1944917 : Blo 1295966 1944917 := bbase (se 11 (by rfl) ⟨1424, by rfl⟩ : syracuseStep 1944917 = 2849) (by norm_num)
theorem B4377941 : Blo 1295966 4377941 := bbase (se 11 (by rfl) ⟨3206, by rfl⟩ : syracuseStep 4377941 = 6413) (by norm_num)
theorem B1944941 : Blo 1295966 1944941 := bbase (se 3 (by rfl) ⟨364676, by rfl⟩ : syracuseStep 1944941 = 729353) (by norm_num)
theorem B2919797 : Blo 1295966 2919797 := bbase (se 5 (by rfl) ⟨136865, by rfl⟩ : syracuseStep 2919797 = 273731) (by norm_num)
theorem B1944965 : Blo 1295966 1944965 := bbase (se 4 (by rfl) ⟨182340, by rfl⟩ : syracuseStep 1944965 = 364681) (by norm_num)
theorem B1314185 : Blo 1295966 1314185 := bbase (se 2 (by rfl) ⟨492819, by rfl⟩ : syracuseStep 1314185 = 985639) (by norm_num)
theorem B1641865 : Blo 1295966 1641865 := bbase (se 2 (by rfl) ⟨615699, by rfl⟩ : syracuseStep 1641865 = 1231399) (by norm_num)
theorem B1944989 : Blo 1295966 1944989 := bbase (se 3 (by rfl) ⟨364685, by rfl⟩ : syracuseStep 1944989 = 729371) (by norm_num)
theorem B1945013 : Blo 1295966 1945013 := bbase (se 5 (by rfl) ⟨91172, by rfl⟩ : syracuseStep 1945013 = 182345) (by norm_num)
theorem B2919869 : Blo 1295966 2919869 := bbase (se 3 (by rfl) ⟨547475, by rfl⟩ : syracuseStep 2919869 = 1094951) (by norm_num)
theorem B1945037 : Blo 1295966 1945037 := bbase (se 3 (by rfl) ⟨364694, by rfl⟩ : syracuseStep 1945037 = 729389) (by norm_num)
theorem B1945061 : Blo 1295966 1945061 := bbase (se 4 (by rfl) ⟨182349, by rfl⟩ : syracuseStep 1945061 = 364699) (by norm_num)
theorem B1641961 : Blo 1295966 1641961 := bbase (se 2 (by rfl) ⟨615735, by rfl⟩ : syracuseStep 1641961 = 1231471) (by norm_num)
theorem B1945085 : Blo 1295966 1945085 := bbase (se 3 (by rfl) ⟨364703, by rfl⟩ : syracuseStep 1945085 = 729407) (by norm_num)
theorem B4156933 : Blo 1295966 4156933 := bbase (se 4 (by rfl) ⟨389712, by rfl⟩ : syracuseStep 4156933 = 779425) (by norm_num)
theorem B2919941 : Blo 1295966 2919941 := bbase (se 4 (by rfl) ⟨273744, by rfl⟩ : syracuseStep 2919941 = 547489) (by norm_num)
theorem B1945109 : Blo 1295966 1945109 := bbase (se 6 (by rfl) ⟨45588, by rfl⟩ : syracuseStep 1945109 = 91177) (by norm_num)
theorem B1945133 : Blo 1295966 1945133 := bbase (se 3 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 1945133 = 729425) (by norm_num)
theorem B1404469 : Blo 1295966 1404469 := bbase (se 5 (by rfl) ⟨65834, by rfl⟩ : syracuseStep 1404469 = 131669) (by norm_num)
theorem B1945157 : Blo 1295966 1945157 := bbase (se 4 (by rfl) ⟨182358, by rfl⟩ : syracuseStep 1945157 = 364717) (by norm_num)
theorem B2920013 : Blo 1295966 2920013 := bbase (se 3 (by rfl) ⟨547502, by rfl⟩ : syracuseStep 2920013 = 1095005) (by norm_num)
theorem B1945181 : Blo 1295966 1945181 := bbase (se 3 (by rfl) ⟨364721, by rfl⟩ : syracuseStep 1945181 = 729443) (by norm_num)
theorem B1945205 : Blo 1295966 1945205 := bbase (se 5 (by rfl) ⟨91181, by rfl⟩ : syracuseStep 1945205 = 182363) (by norm_num)
theorem B1945229 : Blo 1295966 1945229 := bbase (se 3 (by rfl) ⟨364730, by rfl⟩ : syracuseStep 1945229 = 729461) (by norm_num)
theorem B1642133 : Blo 1295966 1642133 := bbase (se 6 (by rfl) ⟨38487, by rfl⟩ : syracuseStep 1642133 = 76975) (by norm_num)
theorem B2920085 : Blo 1295966 2920085 := bbase (se 6 (by rfl) ⟨68439, by rfl⟩ : syracuseStep 2920085 = 136879) (by norm_num)
theorem B1945253 : Blo 1295966 1945253 := bbase (se 4 (by rfl) ⟨182367, by rfl⟩ : syracuseStep 1945253 = 364735) (by norm_num)
theorem B1945277 : Blo 1295966 1945277 := bbase (se 3 (by rfl) ⟨364739, by rfl⟩ : syracuseStep 1945277 = 729479) (by norm_num)
theorem B1642189 : Blo 1295966 1642189 := bbase (se 3 (by rfl) ⟨307910, by rfl⟩ : syracuseStep 1642189 = 615821) (by norm_num)
theorem B1945301 : Blo 1295966 1945301 := bbase (se 7 (by rfl) ⟨22796, by rfl⟩ : syracuseStep 1945301 = 45593) (by norm_num)
theorem B4927189 : Blo 1295966 4927189 := bbase (se 7 (by rfl) ⟨57740, by rfl⟩ : syracuseStep 4927189 = 115481) (by norm_num)
theorem B2920157 : Blo 1295966 2920157 := bbase (se 3 (by rfl) ⟨547529, by rfl⟩ : syracuseStep 2920157 = 1095059) (by norm_num)
theorem B3550949 : Blo 1295966 3550949 := bbase (se 4 (by rfl) ⟨332901, by rfl⟩ : syracuseStep 3550949 = 665803) (by norm_num)
theorem B3280621 : Blo 1295966 3280621 := bbase (se 3 (by rfl) ⟨615116, by rfl⟩ : syracuseStep 3280621 = 1230233) (by norm_num)
theorem B1945325 : Blo 1295966 1945325 := bbase (se 3 (by rfl) ⟨364748, by rfl⟩ : syracuseStep 1945325 = 729497) (by norm_num)
theorem B1945349 : Blo 1295966 1945349 := bbase (se 4 (by rfl) ⟨182376, by rfl⟩ : syracuseStep 1945349 = 364753) (by norm_num)
theorem B4378373 : Blo 1295966 4378373 := bbase (se 4 (by rfl) ⟨410472, by rfl⟩ : syracuseStep 4378373 = 820945) (by norm_num)
theorem B1847053 : Blo 1295966 1847053 := bbase (se 3 (by rfl) ⟨346322, by rfl⟩ : syracuseStep 1847053 = 692645) (by norm_num)
theorem B1945373 : Blo 1295966 1945373 := bbase (se 3 (by rfl) ⟨364757, by rfl⟩ : syracuseStep 1945373 = 729515) (by norm_num)
theorem B2920229 : Blo 1295966 2920229 := bbase (se 4 (by rfl) ⟨273771, by rfl⟩ : syracuseStep 2920229 = 547543) (by norm_num)
theorem B1642285 : Blo 1295966 1642285 := bbase (se 3 (by rfl) ⟨307928, by rfl⟩ : syracuseStep 1642285 = 615857) (by norm_num)
theorem B1945397 : Blo 1295966 1945397 := bbase (se 5 (by rfl) ⟨91190, by rfl⟩ : syracuseStep 1945397 = 182381) (by norm_num)
theorem B1945421 : Blo 1295966 1945421 := bbase (se 3 (by rfl) ⟨364766, by rfl⟩ : syracuseStep 1945421 = 729533) (by norm_num)
theorem B3280733 : Blo 1295966 3280733 := bbase (se 3 (by rfl) ⟨615137, by rfl⟩ : syracuseStep 3280733 = 1230275) (by norm_num)
theorem B1945445 : Blo 1295966 1945445 := bbase (se 4 (by rfl) ⟨182385, by rfl⟩ : syracuseStep 1945445 = 364771) (by norm_num)
theorem B2920301 : Blo 1295966 2920301 := bbase (se 3 (by rfl) ⟨547556, by rfl⟩ : syracuseStep 2920301 = 1095113) (by norm_num)
theorem B1945469 : Blo 1295966 1945469 := bbase (se 3 (by rfl) ⟨364775, by rfl⟩ : syracuseStep 1945469 = 729551) (by norm_num)
theorem B1945493 : Blo 1295966 1945493 := bbase (se 6 (by rfl) ⟨45597, by rfl⟩ : syracuseStep 1945493 = 91195) (by norm_num)
theorem B1945517 : Blo 1295966 1945517 := bbase (se 3 (by rfl) ⟨364784, by rfl⟩ : syracuseStep 1945517 = 729569) (by norm_num)
theorem B2920373 : Blo 1295966 2920373 := bbase (se 5 (by rfl) ⟨136892, by rfl⟩ : syracuseStep 2920373 = 273785) (by norm_num)
theorem B1314749 : Blo 1295966 1314749 := bbase (se 3 (by rfl) ⟨246515, by rfl⟩ : syracuseStep 1314749 = 493031) (by norm_num)
theorem B1945541 : Blo 1295966 1945541 := bbase (se 4 (by rfl) ⟨182394, by rfl⟩ : syracuseStep 1945541 = 364789) (by norm_num)
theorem B17756117 : Blo 1295966 17756117 := bbase (se 7 (by rfl) ⟨208079, by rfl⟩ : syracuseStep 17756117 = 416159) (by norm_num)
theorem B1642457 : Blo 1295966 1642457 := bbase (se 2 (by rfl) ⟨615921, by rfl⟩ : syracuseStep 1642457 = 1231843) (by norm_num)
theorem B1945565 : Blo 1295966 1945565 := bbase (se 3 (by rfl) ⟨364793, by rfl⟩ : syracuseStep 1945565 = 729587) (by norm_num)
theorem B1314785 : Blo 1295966 1314785 := bbase (se 2 (by rfl) ⟨493044, by rfl⟩ : syracuseStep 1314785 = 986089) (by norm_num)
theorem B1945589 : Blo 1295966 1945589 := bbase (se 5 (by rfl) ⟨91199, by rfl⟩ : syracuseStep 1945589 = 182399) (by norm_num)
theorem B4927493 : Blo 1295966 4927493 := bbase (se 4 (by rfl) ⟨461952, by rfl⟩ : syracuseStep 4927493 = 923905) (by norm_num)
theorem B1945613 : Blo 1295966 1945613 := bbase (se 3 (by rfl) ⟨364802, by rfl⟩ : syracuseStep 1945613 = 729605) (by norm_num)
theorem B1642513 : Blo 1295966 1642513 := bbase (se 2 (by rfl) ⟨615942, by rfl⟩ : syracuseStep 1642513 = 1231885) (by norm_num)
theorem B3690517 : Blo 1295966 3690517 := bbase (se 6 (by rfl) ⟨86496, by rfl⟩ : syracuseStep 3690517 = 172993) (by norm_num)
theorem B12455957 : Blo 1295966 12455957 := bbase (se 6 (by rfl) ⟨291936, by rfl⟩ : syracuseStep 12455957 = 583873) (by norm_num)
theorem B3280925 : Blo 1295966 3280925 := bbase (se 3 (by rfl) ⟨615173, by rfl⟩ : syracuseStep 3280925 = 1230347) (by norm_num)
theorem B1945637 : Blo 1295966 1945637 := bbase (se 4 (by rfl) ⟨182403, by rfl⟩ : syracuseStep 1945637 = 364807) (by norm_num)
theorem B1945661 : Blo 1295966 1945661 := bbase (se 3 (by rfl) ⟨364811, by rfl⟩ : syracuseStep 1945661 = 729623) (by norm_num)
theorem B2461765 : Blo 1295966 2461765 := bbase (se 4 (by rfl) ⟨230790, by rfl⟩ : syracuseStep 2461765 = 461581) (by norm_num)
theorem B1478741 : Blo 1295966 1478741 := bbase (se 8 (by rfl) ⟨8664, by rfl⟩ : syracuseStep 1478741 = 17329) (by norm_num)
theorem B1945685 : Blo 1295966 1945685 := bbase (se 8 (by rfl) ⟨11400, by rfl⟩ : syracuseStep 1945685 = 22801) (by norm_num)
theorem B1847389 : Blo 1295966 1847389 := bbase (se 3 (by rfl) ⟨346385, by rfl⟩ : syracuseStep 1847389 = 692771) (by norm_num)
theorem B1945709 : Blo 1295966 1945709 := bbase (se 3 (by rfl) ⟨364820, by rfl⟩ : syracuseStep 1945709 = 729641) (by norm_num)
theorem B1642609 : Blo 1295966 1642609 := bbase (se 2 (by rfl) ⟨615978, by rfl⟩ : syracuseStep 1642609 = 1231957) (by norm_num)
theorem B6566021 : Blo 1295966 6566021 := bbase (se 4 (by rfl) ⟨615564, by rfl⟩ : syracuseStep 6566021 = 1231129) (by norm_num)
theorem B1945733 : Blo 1295966 1945733 := bbase (se 4 (by rfl) ⟨182412, by rfl⟩ : syracuseStep 1945733 = 364825) (by norm_num)
theorem B1945757 : Blo 1295966 1945757 := bbase (se 3 (by rfl) ⟨364829, by rfl⟩ : syracuseStep 1945757 = 729659) (by norm_num)
theorem B3690677 : Blo 1295966 3690677 := bbase (se 5 (by rfl) ⟨173000, by rfl⟩ : syracuseStep 3690677 = 346001) (by norm_num)
theorem B1945781 : Blo 1295966 1945781 := bbase (se 5 (by rfl) ⟨91208, by rfl⟩ : syracuseStep 1945781 = 182417) (by norm_num)
theorem B4378805 : Blo 1295966 4378805 := bbase (se 5 (by rfl) ⟨205256, by rfl⟩ : syracuseStep 4378805 = 410513) (by norm_num)
theorem B1945805 : Blo 1295966 1945805 := bbase (se 3 (by rfl) ⟨364838, by rfl⟩ : syracuseStep 1945805 = 729677) (by norm_num)
theorem B2461909 : Blo 1295966 2461909 := bbase (se 7 (by rfl) ⟨28850, by rfl⟩ : syracuseStep 2461909 = 57701) (by norm_num)
theorem B1945829 : Blo 1295966 1945829 := bbase (se 4 (by rfl) ⟨182421, by rfl⟩ : syracuseStep 1945829 = 364843) (by norm_num)
theorem B1945853 : Blo 1295966 1945853 := bbase (se 3 (by rfl) ⟨364847, by rfl⟩ : syracuseStep 1945853 = 729695) (by norm_num)
theorem B1945877 : Blo 1295966 1945877 := bbase (se 6 (by rfl) ⟨45606, by rfl⟩ : syracuseStep 1945877 = 91213) (by norm_num)
theorem B1315109 : Blo 1295966 1315109 := bbase (se 4 (by rfl) ⟨123291, by rfl⟩ : syracuseStep 1315109 = 246583) (by norm_num)
theorem B1945901 : Blo 1295966 1945901 := bbase (se 3 (by rfl) ⟨364856, by rfl⟩ : syracuseStep 1945901 = 729713) (by norm_num)
theorem B1847605 : Blo 1295966 1847605 := bbase (se 5 (by rfl) ⟨86606, by rfl⟩ : syracuseStep 1847605 = 173213) (by norm_num)
theorem B1945925 : Blo 1295966 1945925 := bbase (se 4 (by rfl) ⟨182430, by rfl⟩ : syracuseStep 1945925 = 364861) (by norm_num)
theorem B1945949 : Blo 1295966 1945949 := bbase (se 3 (by rfl) ⟨364865, by rfl⟩ : syracuseStep 1945949 = 729731) (by norm_num)
theorem B3281269 : Blo 1295966 3281269 := bbase (se 5 (by rfl) ⟨153809, by rfl⟩ : syracuseStep 3281269 = 307619) (by norm_num)
theorem B2462069 : Blo 1295966 2462069 := bbase (se 5 (by rfl) ⟨115409, by rfl⟩ : syracuseStep 2462069 = 230819) (by norm_num)
theorem B1732981 : Blo 1295966 1732981 := bbase (se 5 (by rfl) ⟨81233, by rfl⟩ : syracuseStep 1732981 = 162467) (by norm_num)
theorem B1945973 : Blo 1295966 1945973 := bbase (se 5 (by rfl) ⟨91217, by rfl⟩ : syracuseStep 1945973 = 182435) (by norm_num)
theorem B1331581 : Blo 1295966 1331581 := bbase (se 3 (by rfl) ⟨249671, by rfl⟩ : syracuseStep 1331581 = 499343) (by norm_num)
theorem B1945997 : Blo 1295966 1945997 := bbase (se 3 (by rfl) ⟨364874, by rfl⟩ : syracuseStep 1945997 = 729749) (by norm_num)
theorem B3690917 : Blo 1295966 3690917 := bbase (se 4 (by rfl) ⟨346023, by rfl⟩ : syracuseStep 3690917 = 692047) (by norm_num)
theorem B1946021 : Blo 1295966 1946021 := bbase (se 4 (by rfl) ⟨182439, by rfl⟩ : syracuseStep 1946021 = 364879) (by norm_num)
theorem B1946045 : Blo 1295966 1946045 := bbase (se 3 (by rfl) ⟨364883, by rfl⟩ : syracuseStep 1946045 = 729767) (by norm_num)
theorem B1946069 : Blo 1295966 1946069 := bbase (se 7 (by rfl) ⟨22805, by rfl⟩ : syracuseStep 1946069 = 45611) (by norm_num)
theorem B3281381 : Blo 1295966 3281381 := bbase (se 4 (by rfl) ⟨307629, by rfl⟩ : syracuseStep 3281381 = 615259) (by norm_num)
theorem B1946093 : Blo 1295966 1946093 := bbase (se 3 (by rfl) ⟨364892, by rfl⟩ : syracuseStep 1946093 = 729785) (by norm_num)
theorem B5255669 : Blo 1295966 5255669 := bbase (se 5 (by rfl) ⟨246359, by rfl⟩ : syracuseStep 5255669 = 492719) (by norm_num)
theorem B3117565 : Blo 1295966 3117565 := bbase (se 3 (by rfl) ⟨584543, by rfl⟩ : syracuseStep 3117565 = 1169087) (by norm_num)
theorem B2462213 : Blo 1295966 2462213 := bbase (se 4 (by rfl) ⟨230832, by rfl⟩ : syracuseStep 2462213 = 461665) (by norm_num)
theorem B1946117 : Blo 1295966 1946117 := bbase (se 4 (by rfl) ⟨182448, by rfl⟩ : syracuseStep 1946117 = 364897) (by norm_num)
theorem B1946141 : Blo 1295966 1946141 := bbase (se 3 (by rfl) ⟨364901, by rfl⟩ : syracuseStep 1946141 = 729803) (by norm_num)
theorem B1459813 : Blo 1295966 1459813 := bbase (se 4 (by rfl) ⟨136857, by rfl⟩ : syracuseStep 1459813 = 273715) (by norm_num)
theorem B1946165 : Blo 1295966 1946165 := bbase (se 5 (by rfl) ⟨91226, by rfl⟩ : syracuseStep 1946165 = 182453) (by norm_num)
theorem B1946189 : Blo 1295966 1946189 := bbase (se 3 (by rfl) ⟨364910, by rfl⟩ : syracuseStep 1946189 = 729821) (by norm_num)
theorem B3691109 : Blo 1295966 3691109 := bbase (se 4 (by rfl) ⟨346041, by rfl⟩ : syracuseStep 3691109 = 692083) (by norm_num)
theorem B1331813 : Blo 1295966 1331813 := bbase (se 4 (by rfl) ⟨124857, by rfl⟩ : syracuseStep 1331813 = 249715) (by norm_num)
theorem B1946213 : Blo 1295966 1946213 := bbase (se 4 (by rfl) ⟨182457, by rfl⟩ : syracuseStep 1946213 = 364915) (by norm_num)
theorem B4379237 : Blo 1295966 4379237 := bbase (se 4 (by rfl) ⟨410553, by rfl⟩ : syracuseStep 4379237 = 821107) (by norm_num)
theorem B2077301 : Blo 1295966 2077301 := bbase (se 5 (by rfl) ⟨97373, by rfl⟩ : syracuseStep 2077301 = 194747) (by norm_num)
theorem B1946237 : Blo 1295966 1946237 := bbase (se 3 (by rfl) ⟨364919, by rfl⟩ : syracuseStep 1946237 = 729839) (by norm_num)
theorem B1946261 : Blo 1295966 1946261 := bbase (se 6 (by rfl) ⟨45615, by rfl⟩ : syracuseStep 1946261 = 91231) (by norm_num)
theorem B3281573 : Blo 1295966 3281573 := bbase (se 4 (by rfl) ⟨307647, by rfl⟩ : syracuseStep 3281573 = 615295) (by norm_num)
theorem B1946285 : Blo 1295966 1946285 := bbase (se 3 (by rfl) ⟨364928, by rfl⟩ : syracuseStep 1946285 = 729857) (by norm_num)
theorem B1847981 : Blo 1295966 1847981 := bbase (se 3 (by rfl) ⟨346496, by rfl⟩ : syracuseStep 1847981 = 692993) (by norm_num)
theorem B3117757 : Blo 1295966 3117757 := bbase (se 3 (by rfl) ⟨584579, by rfl⟩ : syracuseStep 3117757 = 1169159) (by norm_num)
theorem B1946309 : Blo 1295966 1946309 := bbase (se 4 (by rfl) ⟨182466, by rfl⟩ : syracuseStep 1946309 = 364933) (by norm_num)
theorem B1946333 : Blo 1295966 1946333 := bbase (se 3 (by rfl) ⟨364937, by rfl⟩ : syracuseStep 1946333 = 729875) (by norm_num)
theorem B3117797 : Blo 1295966 3117797 := bbase (se 4 (by rfl) ⟨292293, by rfl⟩ : syracuseStep 3117797 = 584587) (by norm_num)
theorem B1946357 : Blo 1295966 1946357 := bbase (se 5 (by rfl) ⟨91235, by rfl⟩ : syracuseStep 1946357 = 182471) (by norm_num)
theorem B1479425 : Blo 1295966 1479425 := bbase (se 2 (by rfl) ⟨554784, by rfl⟩ : syracuseStep 1479425 = 1109569) (by norm_num)
theorem B1946381 : Blo 1295966 1946381 := bbase (se 3 (by rfl) ⟨364946, by rfl⟩ : syracuseStep 1946381 = 729893) (by norm_num)
theorem B2462501 : Blo 1295966 2462501 := bbase (se 4 (by rfl) ⟨230859, by rfl⟩ : syracuseStep 2462501 = 461719) (by norm_num)
theorem B1946405 : Blo 1295966 1946405 := bbase (se 4 (by rfl) ⟨182475, by rfl⟩ : syracuseStep 1946405 = 364951) (by norm_num)
theorem B1946429 : Blo 1295966 1946429 := bbase (se 3 (by rfl) ⟨364955, by rfl⟩ : syracuseStep 1946429 = 729911) (by norm_num)
theorem B1315661 : Blo 1295966 1315661 := bbase (se 3 (by rfl) ⟨246686, by rfl⟩ : syracuseStep 1315661 = 493373) (by norm_num)
theorem B2077525 : Blo 1295966 2077525 := bbase (se 9 (by rfl) ⟨6086, by rfl⟩ : syracuseStep 2077525 = 12173) (by norm_num)
theorem B1946453 : Blo 1295966 1946453 := bbase (se 9 (by rfl) ⟨5702, by rfl⟩ : syracuseStep 1946453 = 11405) (by norm_num)
theorem B1946477 : Blo 1295966 1946477 := bbase (se 3 (by rfl) ⟨364964, by rfl⟩ : syracuseStep 1946477 = 729929) (by norm_num)
theorem B1946501 : Blo 1295966 1946501 := bbase (se 4 (by rfl) ⟨182484, by rfl⟩ : syracuseStep 1946501 = 364969) (by norm_num)
theorem B8426389 : Blo 1295966 8426389 := bbase (se 6 (by rfl) ⟨197493, by rfl⟩ : syracuseStep 8426389 = 394987) (by norm_num)
theorem B1946525 : Blo 1295966 1946525 := bbase (se 3 (by rfl) ⟨364973, by rfl⟩ : syracuseStep 1946525 = 729947) (by norm_num)
theorem B1946549 : Blo 1295966 1946549 := bbase (se 5 (by rfl) ⟨91244, by rfl⟩ : syracuseStep 1946549 = 182489) (by norm_num)
theorem B2462653 : Blo 1295966 2462653 := bbase (se 3 (by rfl) ⟨461747, by rfl⟩ : syracuseStep 2462653 = 923495) (by norm_num)
theorem B1946573 : Blo 1295966 1946573 := bbase (se 3 (by rfl) ⟨364982, by rfl⟩ : syracuseStep 1946573 = 729965) (by norm_num)
theorem B1946597 : Blo 1295966 1946597 := bbase (se 4 (by rfl) ⟨182493, by rfl⟩ : syracuseStep 1946597 = 364987) (by norm_num)
theorem B11228149 : Blo 1295966 11228149 := bbase (se 5 (by rfl) ⟨526319, by rfl⟩ : syracuseStep 11228149 = 1052639) (by norm_num)
theorem B3281917 : Blo 1295966 3281917 := bbase (se 3 (by rfl) ⟨615359, by rfl⟩ : syracuseStep 3281917 = 1230719) (by norm_num)
theorem B1946621 : Blo 1295966 1946621 := bbase (se 3 (by rfl) ⟨364991, by rfl⟩ : syracuseStep 1946621 = 729983) (by norm_num)
theorem B3118085 : Blo 1295966 3118085 := bbase (se 4 (by rfl) ⟨292320, by rfl⟩ : syracuseStep 3118085 = 584641) (by norm_num)
theorem B4379669 : Blo 1295966 4379669 := bbase (se 6 (by rfl) ⟨102648, by rfl⟩ : syracuseStep 4379669 = 205297) (by norm_num)
theorem B1946645 : Blo 1295966 1946645 := bbase (se 6 (by rfl) ⟨45624, by rfl⟩ : syracuseStep 1946645 = 91249) (by norm_num)
theorem B1946669 : Blo 1295966 1946669 := bbase (se 3 (by rfl) ⟨365000, by rfl⟩ : syracuseStep 1946669 = 730001) (by norm_num)
theorem B1946693 : Blo 1295966 1946693 := bbase (se 4 (by rfl) ⟨182502, by rfl⟩ : syracuseStep 1946693 = 365005) (by norm_num)
theorem B1946717 : Blo 1295966 1946717 := bbase (se 3 (by rfl) ⟨365009, by rfl⟩ : syracuseStep 1946717 = 730019) (by norm_num)
theorem B3282029 : Blo 1295966 3282029 := bbase (se 3 (by rfl) ⟨615380, by rfl⟩ : syracuseStep 3282029 = 1230761) (by norm_num)
theorem B1946741 : Blo 1295966 1946741 := bbase (se 5 (by rfl) ⟨91253, by rfl⟩ : syracuseStep 1946741 = 182507) (by norm_num)
theorem B1946765 : Blo 1295966 1946765 := bbase (se 3 (by rfl) ⟨365018, by rfl⟩ : syracuseStep 1946765 = 730037) (by norm_num)
theorem B4052117 : Blo 1295966 4052117 := bbase (se 6 (by rfl) ⟨94971, by rfl⟩ : syracuseStep 4052117 = 189943) (by norm_num)
theorem B1946789 : Blo 1295966 1946789 := bbase (se 4 (by rfl) ⟨182511, by rfl⟩ : syracuseStep 1946789 = 365023) (by norm_num)
theorem B1946813 : Blo 1295966 1946813 := bbase (se 3 (by rfl) ⟨365027, by rfl⟩ : syracuseStep 1946813 = 730055) (by norm_num)
theorem B1946837 : Blo 1295966 1946837 := bbase (se 7 (by rfl) ⟨22814, by rfl⟩ : syracuseStep 1946837 = 45629) (by norm_num)
theorem B2462957 : Blo 1295966 2462957 := bbase (se 3 (by rfl) ⟨461804, by rfl⟩ : syracuseStep 2462957 = 923609) (by norm_num)
theorem B1946861 : Blo 1295966 1946861 := bbase (se 3 (by rfl) ⟨365036, by rfl⟩ : syracuseStep 1946861 = 730073) (by norm_num)
theorem B1946885 : Blo 1295966 1946885 := bbase (se 4 (by rfl) ⟨182520, by rfl⟩ : syracuseStep 1946885 = 365041) (by norm_num)
theorem B7386389 : Blo 1295966 7386389 := bbase (se 6 (by rfl) ⟨173118, by rfl⟩ : syracuseStep 7386389 = 346237) (by norm_num)
theorem B1946909 : Blo 1295966 1946909 := bbase (se 3 (by rfl) ⟨365045, by rfl⟩ : syracuseStep 1946909 = 730091) (by norm_num)
theorem B1479973 : Blo 1295966 1479973 := bbase (se 4 (by rfl) ⟨138747, by rfl⟩ : syracuseStep 1479973 = 277495) (by norm_num)
theorem B3282221 : Blo 1295966 3282221 := bbase (se 3 (by rfl) ⟨615416, by rfl⟩ : syracuseStep 3282221 = 1230833) (by norm_num)
theorem B1946933 : Blo 1295966 1946933 := bbase (se 5 (by rfl) ⟨91262, by rfl⟩ : syracuseStep 1946933 = 182525) (by norm_num)
theorem B6567317 : Blo 1295966 6567317 := bbase (se 6 (by rfl) ⟨153921, by rfl⟩ : syracuseStep 6567317 = 307843) (by norm_num)
theorem B4380101 : Blo 1295966 4380101 := bbase (se 4 (by rfl) ⟨410634, by rfl⟩ : syracuseStep 4380101 = 821269) (by norm_num)
theorem B3692101 : Blo 1295966 3692101 := bbase (se 4 (by rfl) ⟨346134, by rfl⟩ : syracuseStep 3692101 = 692269) (by norm_num)
theorem B6231653 : Blo 1295966 6231653 := bbase (se 4 (by rfl) ⟨584217, by rfl⟩ : syracuseStep 6231653 = 1168435) (by norm_num)
theorem B4806245 : Blo 1295966 4806245 := bbase (se 4 (by rfl) ⟨450585, by rfl⟩ : syracuseStep 4806245 = 901171) (by norm_num)
theorem B3503749 : Blo 1295966 3503749 := bbase (se 4 (by rfl) ⟨328476, by rfl⟩ : syracuseStep 3503749 = 656953) (by norm_num)
theorem B3282565 : Blo 1295966 3282565 := bbase (se 4 (by rfl) ⟨307740, by rfl⟩ : syracuseStep 3282565 = 615481) (by norm_num)
theorem B4994693 : Blo 1295966 4994693 := bbase (se 4 (by rfl) ⟨468252, by rfl⟩ : syracuseStep 4994693 = 936505) (by norm_num)
theorem B3282677 : Blo 1295966 3282677 := bbase (se 5 (by rfl) ⟨153875, by rfl⟩ : syracuseStep 3282677 = 307751) (by norm_num)
theorem B12474101 : Blo 1295966 12474101 := bbase (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) (by norm_num)
theorem B2807557 : Blo 1295966 2807557 := bbase (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) (by norm_num)
theorem B4380533 : Blo 1295966 4380533 := bbase (se 5 (by rfl) ⟨205337, by rfl⟩ : syracuseStep 4380533 = 410675) (by norm_num)
theorem B11384725 : Blo 1295966 11384725 := bbase (se 6 (by rfl) ⟨266829, by rfl⟩ : syracuseStep 11384725 = 533659) (by norm_num)
theorem B3282869 : Blo 1295966 3282869 := bbase (se 5 (by rfl) ⟨153884, by rfl⟩ : syracuseStep 3282869 = 307769) (by norm_num)
theorem B2463709 : Blo 1295966 2463709 := bbase (se 3 (by rfl) ⟨461945, by rfl⟩ : syracuseStep 2463709 = 923891) (by norm_num)
theorem B5543909 : Blo 1295966 5543909 := bbase (se 4 (by rfl) ⟨519741, by rfl⟩ : syracuseStep 5543909 = 1039483) (by norm_num)
theorem B1972325 : Blo 1295966 1972325 := bbase (se 4 (by rfl) ⟨184905, by rfl⟩ : syracuseStep 1972325 = 369811) (by norm_num)
theorem B2463853 : Blo 1295966 2463853 := bbase (se 3 (by rfl) ⟨461972, by rfl⟩ : syracuseStep 2463853 = 923945) (by norm_num)
theorem B2078941 : Blo 1295966 2078941 := bbase (se 3 (by rfl) ⟨389801, by rfl⟩ : syracuseStep 2078941 = 779603) (by norm_num)
theorem B3283213 : Blo 1295966 3283213 := bbase (se 3 (by rfl) ⟨615602, by rfl⟩ : syracuseStep 3283213 = 1231205) (by norm_num)
theorem B2464013 : Blo 1295966 2464013 := bbase (se 3 (by rfl) ⟨462002, by rfl⟩ : syracuseStep 2464013 = 924005) (by norm_num)
theorem B16202069 : Blo 1295966 16202069 := bbase (se 10 (by rfl) ⟨23733, by rfl⟩ : syracuseStep 16202069 = 47467) (by norm_num)
theorem B5536117 : Blo 1295966 5536117 := bbase (se 5 (by rfl) ⟨259505, by rfl⟩ : syracuseStep 5536117 = 519011) (by norm_num)
theorem B3283325 : Blo 1295966 3283325 := bbase (se 3 (by rfl) ⟨615623, by rfl⟩ : syracuseStep 3283325 = 1231247) (by norm_num)
theorem B4921829 : Blo 1295966 4921829 := bbase (se 4 (by rfl) ⟨461421, by rfl⟩ : syracuseStep 4921829 = 922843) (by norm_num)
theorem B3283517 : Blo 1295966 3283517 := bbase (se 3 (by rfl) ⟨615659, by rfl⟩ : syracuseStep 3283517 = 1231319) (by norm_num)
theorem B3742325 : Blo 1295966 3742325 := bbase (se 5 (by rfl) ⟨175421, by rfl⟩ : syracuseStep 3742325 = 350843) (by norm_num)
theorem B3693205 : Blo 1295966 3693205 := bbase (se 6 (by rfl) ⟨86559, by rfl⟩ : syracuseStep 3693205 = 173119) (by norm_num)
theorem B1751717 : Blo 1295966 1751717 := bbase (se 4 (by rfl) ⟨164223, by rfl⟩ : syracuseStep 1751717 = 328447) (by norm_num)
theorem B2218661 : Blo 1295966 2218661 := bbase (se 4 (by rfl) ⟨207999, by rfl⟩ : syracuseStep 2218661 = 415999) (by norm_num)
theorem B6568613 : Blo 1295966 6568613 := bbase (se 4 (by rfl) ⟨615807, by rfl⟩ : syracuseStep 6568613 = 1231615) (by norm_num)
theorem B5257973 : Blo 1295966 5257973 := bbase (se 5 (by rfl) ⟨246467, by rfl⟩ : syracuseStep 5257973 = 492935) (by norm_num)
theorem B4922117 : Blo 1295966 4922117 := bbase (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) (by norm_num)
theorem B1973053 : Blo 1295966 1973053 := bbase (se 3 (by rfl) ⟨369947, by rfl⟩ : syracuseStep 1973053 = 739895) (by norm_num)
theorem B11074421 : Blo 1295966 11074421 := bbase (se 5 (by rfl) ⟨519113, by rfl⟩ : syracuseStep 11074421 = 1038227) (by norm_num)
theorem B5258101 : Blo 1295966 5258101 := bbase (se 5 (by rfl) ⟨246473, by rfl⟩ : syracuseStep 5258101 = 492947) (by norm_num)
theorem B11836277 : Blo 1295966 11836277 := bbase (se 5 (by rfl) ⟨554825, by rfl⟩ : syracuseStep 11836277 = 1109651) (by norm_num)
theorem B3283861 : Blo 1295966 3283861 := bbase (se 6 (by rfl) ⟨76965, by rfl⟩ : syracuseStep 3283861 = 153931) (by norm_num)
theorem B3283973 : Blo 1295966 3283973 := bbase (se 4 (by rfl) ⟨307872, by rfl⟩ : syracuseStep 3283973 = 615745) (by norm_num)
theorem B6560837 : Blo 1295966 6560837 := bbase (se 4 (by rfl) ⟨615078, by rfl⟩ : syracuseStep 6560837 = 1230157) (by norm_num)
theorem B2104397 : Blo 1295966 2104397 := bbase (se 3 (by rfl) ⟨394574, by rfl⟩ : syracuseStep 2104397 = 789149) (by norm_num)
theorem B3284165 : Blo 1295966 3284165 := bbase (se 4 (by rfl) ⟨307890, by rfl⟩ : syracuseStep 3284165 = 615781) (by norm_num)
theorem B6651173 : Blo 1295966 6651173 := bbase (se 4 (by rfl) ⟨623547, by rfl⟩ : syracuseStep 6651173 = 1247095) (by norm_num)
theorem B3603749 : Blo 1295966 3603749 := bbase (se 4 (by rfl) ⟨337851, by rfl⟩ : syracuseStep 3603749 = 675703) (by norm_num)
theorem B7388597 : Blo 1295966 7388597 := bbase (se 5 (by rfl) ⟨346340, by rfl⟩ : syracuseStep 7388597 = 692681) (by norm_num)
theorem B1686977 : Blo 1295966 1686977 := bbase (se 2 (by rfl) ⟨632616, by rfl⟩ : syracuseStep 1686977 = 1265233) (by norm_num)
theorem B3284509 : Blo 1295966 3284509 := bbase (se 3 (by rfl) ⟨615845, by rfl⟩ : syracuseStep 3284509 = 1231691) (by norm_num)
theorem B4374053 : Blo 1295966 4374053 := bbase (se 4 (by rfl) ⟨410067, by rfl⟩ : syracuseStep 4374053 = 820135) (by norm_num)
theorem B6233669 : Blo 1295966 6233669 := bbase (se 4 (by rfl) ⟨584406, by rfl⟩ : syracuseStep 6233669 = 1168813) (by norm_num)
theorem B2915981 : Blo 1295966 2915981 := bbase (se 3 (by rfl) ⟨546746, by rfl⟩ : syracuseStep 2915981 = 1093493) (by norm_num)
theorem B3284621 : Blo 1295966 3284621 := bbase (se 3 (by rfl) ⟨615866, by rfl⟩ : syracuseStep 3284621 = 1231733) (by norm_num)
theorem B4210325 : Blo 1295966 4210325 := bbase (se 6 (by rfl) ⟨98679, by rfl⟩ : syracuseStep 4210325 = 197359) (by norm_num)
theorem B2916053 : Blo 1295966 2916053 := bbase (se 7 (by rfl) ⟨34172, by rfl⟩ : syracuseStep 2916053 = 68345) (by norm_num)
theorem B5996261 : Blo 1295966 5996261 := bbase (se 4 (by rfl) ⟨562149, by rfl⟩ : syracuseStep 5996261 = 1124299) (by norm_num)
theorem B2187013 : Blo 1295966 2187013 := bbase (se 4 (by rfl) ⟨205032, by rfl⟩ : syracuseStep 2187013 = 410065) (by norm_num)
theorem B6233861 : Blo 1295966 6233861 := bbase (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) (by norm_num)
theorem B2916125 : Blo 1295966 2916125 := bbase (se 3 (by rfl) ⟨546773, by rfl⟩ : syracuseStep 2916125 = 1093547) (by norm_num)
theorem B1457977 : Blo 1295966 1457977 := bbase (se 2 (by rfl) ⟨546741, by rfl⟩ : syracuseStep 1457977 = 1093483) (by norm_num)
theorem B5537605 : Blo 1295966 5537605 := bbase (se 4 (by rfl) ⟨519150, by rfl⟩ : syracuseStep 5537605 = 1038301) (by norm_num)
theorem B3284813 : Blo 1295966 3284813 := bbase (se 3 (by rfl) ⟨615902, by rfl⟩ : syracuseStep 3284813 = 1231805) (by norm_num)
theorem B5537621 : Blo 1295966 5537621 := bbase (se 9 (by rfl) ⟨16223, by rfl⟩ : syracuseStep 5537621 = 32447) (by norm_num)
theorem B1458013 : Blo 1295966 1458013 := bbase (se 3 (by rfl) ⟨273377, by rfl⟩ : syracuseStep 1458013 = 546755) (by norm_num)
theorem B2187101 : Blo 1295966 2187101 := bbase (se 3 (by rfl) ⟨410081, by rfl⟩ : syracuseStep 2187101 = 820163) (by norm_num)
theorem B2916197 : Blo 1295966 2916197 := bbase (se 4 (by rfl) ⟨273393, by rfl⟩ : syracuseStep 2916197 = 546787) (by norm_num)
theorem B1458049 : Blo 1295966 1458049 := bbase (se 2 (by rfl) ⟨546768, by rfl⟩ : syracuseStep 1458049 = 1093537) (by norm_num)
theorem B1384337 : Blo 1295966 1384337 := bbase (se 2 (by rfl) ⟨519126, by rfl⟩ : syracuseStep 1384337 = 1038253) (by norm_num)
theorem B1458085 : Blo 1295966 1458085 := bbase (se 4 (by rfl) ⟨136695, by rfl⟩ : syracuseStep 1458085 = 273391) (by norm_num)
theorem B4923301 : Blo 1295966 4923301 := bbase (se 4 (by rfl) ⟨461559, by rfl⟩ : syracuseStep 4923301 = 923119) (by norm_num)
theorem B2916269 : Blo 1295966 2916269 := bbase (se 3 (by rfl) ⟨546800, by rfl⟩ : syracuseStep 2916269 = 1093601) (by norm_num)
theorem B6651829 : Blo 1295966 6651829 := bbase (se 5 (by rfl) ⟨311804, by rfl⟩ : syracuseStep 6651829 = 623609) (by norm_num)
theorem B6569909 : Blo 1295966 6569909 := bbase (se 5 (by rfl) ⟨307964, by rfl⟩ : syracuseStep 6569909 = 615929) (by norm_num)
theorem B1458121 : Blo 1295966 1458121 := bbase (se 2 (by rfl) ⟨546795, by rfl⟩ : syracuseStep 1458121 = 1093591) (by norm_num)
theorem B2768845 : Blo 1295966 2768845 := bbase (se 3 (by rfl) ⟨519158, by rfl⟩ : syracuseStep 2768845 = 1038317) (by norm_num)
theorem B4374485 : Blo 1295966 4374485 := bbase (se 7 (by rfl) ⟨51263, by rfl⟩ : syracuseStep 4374485 = 102527) (by norm_num)
theorem B2187229 : Blo 1295966 2187229 := bbase (se 3 (by rfl) ⟨410105, by rfl⟩ : syracuseStep 2187229 = 820211) (by norm_num)
theorem B1458157 : Blo 1295966 1458157 := bbase (se 3 (by rfl) ⟨273404, by rfl⟩ : syracuseStep 1458157 = 546809) (by norm_num)
theorem B1753069 : Blo 1295966 1753069 := bbase (se 3 (by rfl) ⟨328700, by rfl⟩ : syracuseStep 1753069 = 657401) (by norm_num)
theorem B2220013 : Blo 1295966 2220013 := bbase (se 3 (by rfl) ⟨416252, by rfl⟩ : syracuseStep 2220013 = 832505) (by norm_num)
theorem B2916341 : Blo 1295966 2916341 := bbase (se 5 (by rfl) ⟨136703, by rfl⟩ : syracuseStep 2916341 = 273407) (by norm_num)
theorem B3284995 : Blo 1295966 3284995 := bstep (se 1 (by rfl) ⟨2463746, by rfl⟩ : syracuseStep 3284995 = 4927493) B4927493
theorem B2187283 : Blo 1295966 2187283 := bstep (se 1 (by rfl) ⟨1640462, by rfl⟩ : syracuseStep 2187283 = 3280925) B3280925
theorem B1458211 : Blo 1295966 1458211 := bstep (se 1 (by rfl) ⟨1093658, by rfl⟩ : syracuseStep 1458211 = 2187317) B2187317
theorem B3506257 : Blo 1295966 3506257 := bstep (se 2 (by rfl) ⟨1314846, by rfl⟩ : syracuseStep 3506257 = 2629693) B2629693
theorem B1753171 : Blo 1295966 1753171 := bstep (se 1 (by rfl) ⟨1314878, by rfl⟩ : syracuseStep 1753171 = 2629757) B2629757
theorem B3285137 : Blo 1295966 3285137 := bstep (se 2 (by rfl) ⟨1231926, by rfl⟩ : syracuseStep 3285137 = 2463853) B2463853
theorem B2187425 : Blo 1295966 2187425 := bstep (se 2 (by rfl) ⟨820284, by rfl⟩ : syracuseStep 2187425 = 1640569) B1640569
theorem B4374701 : Blo 1295966 4374701 := bstep (se 3 (by rfl) ⟨820256, by rfl⟩ : syracuseStep 4374701 = 1640513) B1640513
theorem B1458355 : Blo 1295966 1458355 := bstep (se 1 (by rfl) ⟨1093766, by rfl⟩ : syracuseStep 1458355 = 2187533) B2187533
theorem B12460229 : Blo 1295966 12460229 := bstep (se 4 (by rfl) ⟨1168146, by rfl⟩ : syracuseStep 12460229 = 2336293) B2336293
theorem B5333197 : Blo 1295966 5333197 := bstep (se 3 (by rfl) ⟨999974, by rfl⟩ : syracuseStep 5333197 = 1999949) B1999949
theorem B4374755 : Blo 1295966 4374755 := bstep (se 1 (by rfl) ⟨3281066, by rfl⟩ : syracuseStep 4374755 = 6562133) B6562133
theorem B2916593 : Blo 1295966 2916593 := bstep (se 2 (by rfl) ⟨1093722, by rfl⟩ : syracuseStep 2916593 = 2187445) B2187445
theorem B2916611 : Blo 1295966 2916611 := bstep (se 1 (by rfl) ⟨2187458, by rfl⟩ : syracuseStep 2916611 = 4374917) B4374917
theorem B2187553 : Blo 1295966 2187553 := bstep (se 2 (by rfl) ⟨820332, by rfl⟩ : syracuseStep 2187553 = 1640665) B1640665
theorem B2769187 : Blo 1295966 2769187 := bstep (se 1 (by rfl) ⟨2076890, by rfl⟩ : syracuseStep 2769187 = 4153781) B4153781
theorem B2187587 : Blo 1295966 2187587 := bstep (se 1 (by rfl) ⟨1640690, by rfl⟩ : syracuseStep 2187587 = 3281381) B3281381
theorem B1458499 : Blo 1295966 1458499 := bstep (se 1 (by rfl) ⟨1093874, by rfl⟩ : syracuseStep 1458499 = 2187749) B2187749
theorem B10805645 : Blo 1295966 10805645 := bstep (se 3 (by rfl) ⟨2026058, by rfl⟩ : syracuseStep 10805645 = 4052117) B4052117
theorem B1384867 : Blo 1295966 1384867 := bstep (se 1 (by rfl) ⟨1038650, by rfl⟩ : syracuseStep 1384867 = 2077301) B2077301
theorem B2187715 : Blo 1295966 2187715 := bstep (se 1 (by rfl) ⟨1640786, by rfl⟩ : syracuseStep 2187715 = 3281573) B3281573
theorem B1458643 : Blo 1295966 1458643 := bstep (se 1 (by rfl) ⟨1093982, by rfl⟩ : syracuseStep 1458643 = 2187965) B2187965
theorem B7381489 : Blo 1295966 7381489 := bstep (se 2 (by rfl) ⟨2768058, by rfl⟩ : syracuseStep 7381489 = 5536117) B5536117
theorem B4375025 : Blo 1295966 4375025 := bstep (se 2 (by rfl) ⟨1640634, by rfl⟩ : syracuseStep 4375025 = 3281269) B3281269
theorem B2916881 : Blo 1295966 2916881 := bstep (se 2 (by rfl) ⟨1093830, by rfl⟩ : syracuseStep 2916881 = 2187661) B2187661
theorem B2916899 : Blo 1295966 2916899 := bstep (se 1 (by rfl) ⟨2187674, by rfl⟩ : syracuseStep 2916899 = 4375349) B4375349
theorem B3506723 : Blo 1295966 3506723 := bstep (se 1 (by rfl) ⟨2630042, by rfl⟩ : syracuseStep 3506723 = 5260085) B5260085
theorem B4153933 : Blo 1295966 4153933 := bstep (se 3 (by rfl) ⟨778862, by rfl⟩ : syracuseStep 4153933 = 1557725) B1557725
theorem B2187857 : Blo 1295966 2187857 := bstep (se 2 (by rfl) ⟨820446, by rfl⟩ : syracuseStep 2187857 = 1640893) B1640893
theorem B1557091 : Blo 1295966 1557091 := bstep (se 1 (by rfl) ⟨1167818, by rfl⟩ : syracuseStep 1557091 = 2335637) B2335637
theorem B1458787 : Blo 1295966 1458787 := bstep (se 1 (by rfl) ⟨1094090, by rfl⟩ : syracuseStep 1458787 = 2188181) B2188181
theorem B2187985 : Blo 1295966 2187985 := bstep (se 2 (by rfl) ⟨820494, by rfl⟩ : syracuseStep 2187985 = 1640989) B1640989
theorem B3506915 : Blo 1295966 3506915 := bstep (se 1 (by rfl) ⟨2630186, by rfl⟩ : syracuseStep 3506915 = 5260373) B5260373
theorem B2188019 : Blo 1295966 2188019 := bstep (se 1 (by rfl) ⟨1641014, by rfl⟩ : syracuseStep 2188019 = 3282029) B3282029
theorem B1458931 : Blo 1295966 1458931 := bstep (se 1 (by rfl) ⟨1094198, by rfl⟩ : syracuseStep 1458931 = 2188397) B2188397
theorem B3506957 : Blo 1295966 3506957 := bstep (se 3 (by rfl) ⟨657554, by rfl⟩ : syracuseStep 3506957 = 1315109) B1315109
theorem B9609997 : Blo 1295966 9609997 := bstep (se 3 (by rfl) ⟨1801874, by rfl⟩ : syracuseStep 9609997 = 3603749) B3603749
theorem B2917169 : Blo 1295966 2917169 := bstep (se 2 (by rfl) ⟨1093938, by rfl⟩ : syracuseStep 2917169 = 2187877) B2187877
theorem B14770997 : Blo 1295966 14770997 := bstep (se 5 (by rfl) ⟨692390, by rfl⟩ : syracuseStep 14770997 = 1384781) B1384781
theorem B2917187 : Blo 1295966 2917187 := bstep (se 1 (by rfl) ⟨2187890, by rfl⟩ : syracuseStep 2917187 = 4375781) B4375781
theorem B4924259 : Blo 1295966 4924259 := bstep (se 1 (by rfl) ⟨3693194, by rfl⟩ : syracuseStep 4924259 = 7386389) B7386389
theorem B4924273 : Blo 1295966 4924273 := bstep (se 2 (by rfl) ⟨1846602, by rfl⟩ : syracuseStep 4924273 = 3693205) B3693205
theorem B2188147 : Blo 1295966 2188147 := bstep (se 1 (by rfl) ⟨1641110, by rfl⟩ : syracuseStep 2188147 = 3282221) B3282221
theorem B1459075 : Blo 1295966 1459075 := bstep (se 1 (by rfl) ⟨1094306, by rfl⟩ : syracuseStep 1459075 = 2188613) B2188613
theorem B2188289 : Blo 1295966 2188289 := bstep (se 2 (by rfl) ⟨820608, by rfl⟩ : syracuseStep 2188289 = 1641217) B1641217
theorem B4375565 : Blo 1295966 4375565 := bstep (se 3 (by rfl) ⟨820418, by rfl⟩ : syracuseStep 4375565 = 1640837) B1640837
theorem B1459219 : Blo 1295966 1459219 := bstep (se 1 (by rfl) ⟨1094414, by rfl⟩ : syracuseStep 1459219 = 2188829) B2188829
theorem B5538851 : Blo 1295966 5538851 := bstep (se 1 (by rfl) ⟨4154138, by rfl⟩ : syracuseStep 5538851 = 8308277) B8308277
theorem B4375619 : Blo 1295966 4375619 := bstep (se 1 (by rfl) ⟨3281714, by rfl⟩ : syracuseStep 4375619 = 6563429) B6563429
theorem B4154435 : Blo 1295966 4154435 := bstep (se 1 (by rfl) ⟨3115826, by rfl⟩ : syracuseStep 4154435 = 6231653) B6231653
theorem B3204163 : Blo 1295966 3204163 := bstep (se 1 (by rfl) ⟨2403122, by rfl⟩ : syracuseStep 3204163 = 4806245) B4806245
theorem B2917457 : Blo 1295966 2917457 := bstep (se 2 (by rfl) ⟨1094046, by rfl⟩ : syracuseStep 2917457 = 2188093) B2188093
theorem B2630737 : Blo 1295966 2630737 := bstep (se 2 (by rfl) ⟨986526, by rfl⟩ : syracuseStep 2630737 = 1973053) B1973053
theorem B2917475 : Blo 1295966 2917475 := bstep (se 1 (by rfl) ⟨2188106, by rfl⟩ : syracuseStep 2917475 = 4376213) B4376213
theorem B2770033 : Blo 1295966 2770033 := bstep (se 2 (by rfl) ⟨1038762, by rfl⟩ : syracuseStep 2770033 = 2077525) B2077525
theorem B2188417 : Blo 1295966 2188417 := bstep (se 2 (by rfl) ⟨820656, by rfl⟩ : syracuseStep 2188417 = 1641313) B1641313
theorem B8307845 : Blo 1295966 8307845 := bstep (se 4 (by rfl) ⟨778860, by rfl⟩ : syracuseStep 8307845 = 1557721) B1557721
theorem B2188451 : Blo 1295966 2188451 := bstep (se 1 (by rfl) ⟨1641338, by rfl⟩ : syracuseStep 2188451 = 3282677) B3282677
theorem B1459363 : Blo 1295966 1459363 := bstep (se 1 (by rfl) ⟨1094522, by rfl⟩ : syracuseStep 1459363 = 2189045) B2189045
theorem B2188579 : Blo 1295966 2188579 := bstep (se 1 (by rfl) ⟨1641434, by rfl⟩ : syracuseStep 2188579 = 3282869) B3282869
theorem B1459507 : Blo 1295966 1459507 := bstep (se 1 (by rfl) ⟨1094630, by rfl⟩ : syracuseStep 1459507 = 2189261) B2189261
theorem B3695939 : Blo 1295966 3695939 := bstep (se 1 (by rfl) ⟨2771954, by rfl⟩ : syracuseStep 3695939 = 5543909) B5543909
theorem B4375889 : Blo 1295966 4375889 := bstep (se 2 (by rfl) ⟨1640958, by rfl⟩ : syracuseStep 4375889 = 3281917) B3281917
theorem B2917745 : Blo 1295966 2917745 := bstep (se 2 (by rfl) ⟨1094154, by rfl⟩ : syracuseStep 2917745 = 2188309) B2188309
theorem B2917763 : Blo 1295966 2917763 := bstep (se 1 (by rfl) ⟨2188322, by rfl⟩ : syracuseStep 2917763 = 4376645) B4376645
theorem B3507587 : Blo 1295966 3507587 := bstep (se 1 (by rfl) ⟨2630690, by rfl⟩ : syracuseStep 3507587 = 5261381) B5261381
theorem B2188721 : Blo 1295966 2188721 := bstep (se 2 (by rfl) ⟨820770, by rfl⟩ : syracuseStep 2188721 = 1641541) B1641541
theorem B1459651 : Blo 1295966 1459651 := bstep (se 1 (by rfl) ⟨1094738, by rfl⟩ : syracuseStep 1459651 = 2189477) B2189477
theorem B2188849 : Blo 1295966 2188849 := bstep (se 2 (by rfl) ⟨820818, by rfl⟩ : syracuseStep 2188849 = 1641637) B1641637
theorem B2188883 : Blo 1295966 2188883 := bstep (se 1 (by rfl) ⟨1641662, by rfl⟩ : syracuseStep 2188883 = 3283325) B3283325
theorem B1459795 : Blo 1295966 1459795 := bstep (se 1 (by rfl) ⟨1094846, by rfl⟩ : syracuseStep 1459795 = 2189693) B2189693
theorem B1295971 : Blo 1295966 1295971 := bstep (se 1 (by rfl) ⟨971978, by rfl⟩ : syracuseStep 1295971 = 1943957) B1943957
theorem B1295987 : Blo 1295966 1295987 := bstep (se 1 (by rfl) ⟨971990, by rfl⟩ : syracuseStep 1295987 = 1943981) B1943981
theorem B1296003 : Blo 1295966 1296003 := bstep (se 1 (by rfl) ⟨972002, by rfl⟩ : syracuseStep 1296003 = 1944005) B1944005
theorem B2918033 : Blo 1295966 2918033 := bstep (se 2 (by rfl) ⟨1094262, by rfl⟩ : syracuseStep 2918033 = 2188525) B2188525
theorem B1296019 : Blo 1295966 1296019 := bstep (se 1 (by rfl) ⟨972014, by rfl⟩ : syracuseStep 1296019 = 1944029) B1944029
theorem B1296035 : Blo 1295966 1296035 := bstep (se 1 (by rfl) ⟨972026, by rfl⟩ : syracuseStep 1296035 = 1944053) B1944053
theorem B2918051 : Blo 1295966 2918051 := bstep (se 1 (by rfl) ⟨2188538, by rfl⟩ : syracuseStep 2918051 = 4377077) B4377077
theorem B1296051 : Blo 1295966 1296051 := bstep (se 1 (by rfl) ⟨972038, by rfl⟩ : syracuseStep 1296051 = 1944077) B1944077
theorem B1296067 : Blo 1295966 1296067 := bstep (se 1 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 1296067 = 1944101) B1944101
theorem B1296083 : Blo 1295966 1296083 := bstep (se 1 (by rfl) ⟨972062, by rfl⟩ : syracuseStep 1296083 = 1944125) B1944125
theorem B2189011 : Blo 1295966 2189011 := bstep (se 1 (by rfl) ⟨1641758, by rfl⟩ : syracuseStep 2189011 = 3283517) B3283517
theorem B1296099 : Blo 1295966 1296099 := bstep (se 1 (by rfl) ⟨972074, by rfl⟩ : syracuseStep 1296099 = 1944149) B1944149
theorem B1459939 : Blo 1295966 1459939 := bstep (se 1 (by rfl) ⟨1094954, by rfl⟩ : syracuseStep 1459939 = 2189909) B2189909
theorem B1296115 : Blo 1295966 1296115 := bstep (se 1 (by rfl) ⟨972086, by rfl⟩ : syracuseStep 1296115 = 1944173) B1944173
theorem B1296131 : Blo 1295966 1296131 := bstep (se 1 (by rfl) ⟨972098, by rfl⟩ : syracuseStep 1296131 = 1944197) B1944197
theorem B4671245 : Blo 1295966 4671245 := bstep (se 3 (by rfl) ⟨875858, by rfl⟩ : syracuseStep 4671245 = 1751717) B1751717
theorem B1296147 : Blo 1295966 1296147 := bstep (se 1 (by rfl) ⟨972110, by rfl⟩ : syracuseStep 1296147 = 1944221) B1944221
theorem B1296163 : Blo 1295966 1296163 := bstep (se 1 (by rfl) ⟨972122, by rfl⟩ : syracuseStep 1296163 = 1944245) B1944245
theorem B1296179 : Blo 1295966 1296179 := bstep (se 1 (by rfl) ⟨972134, by rfl⟩ : syracuseStep 1296179 = 1944269) B1944269
theorem B1296195 : Blo 1295966 1296195 := bstep (se 1 (by rfl) ⟨972146, by rfl⟩ : syracuseStep 1296195 = 1944293) B1944293
theorem B1296211 : Blo 1295966 1296211 := bstep (se 1 (by rfl) ⟨972158, by rfl⟩ : syracuseStep 1296211 = 1944317) B1944317
theorem B2189153 : Blo 1295966 2189153 := bstep (se 2 (by rfl) ⟨820932, by rfl⟩ : syracuseStep 2189153 = 1641865) B1641865
theorem B1296227 : Blo 1295966 1296227 := bstep (se 1 (by rfl) ⟨972170, by rfl⟩ : syracuseStep 1296227 = 1944341) B1944341
theorem B4376429 : Blo 1295966 4376429 := bstep (se 3 (by rfl) ⟨820580, by rfl⟩ : syracuseStep 4376429 = 1641161) B1641161
theorem B1296243 : Blo 1295966 1296243 := bstep (se 1 (by rfl) ⟨972182, by rfl⟩ : syracuseStep 1296243 = 1944365) B1944365
theorem B1460083 : Blo 1295966 1460083 := bstep (se 1 (by rfl) ⟨1095062, by rfl⟩ : syracuseStep 1460083 = 2190125) B2190125
theorem B1296259 : Blo 1295966 1296259 := bstep (se 1 (by rfl) ⟨972194, by rfl⟩ : syracuseStep 1296259 = 1944389) B1944389
theorem B1296275 : Blo 1295966 1296275 := bstep (se 1 (by rfl) ⟨972206, by rfl⟩ : syracuseStep 1296275 = 1944413) B1944413
theorem B4376483 : Blo 1295966 4376483 := bstep (se 1 (by rfl) ⟨3282362, by rfl⟩ : syracuseStep 4376483 = 6564725) B6564725
theorem B1296291 : Blo 1295966 1296291 := bstep (se 1 (by rfl) ⟨972218, by rfl⟩ : syracuseStep 1296291 = 1944437) B1944437
theorem B7382947 : Blo 1295966 7382947 := bstep (se 1 (by rfl) ⟨5537210, by rfl⟩ : syracuseStep 7382947 = 11074421) B11074421
theorem B7890851 : Blo 1295966 7890851 := bstep (se 1 (by rfl) ⟨5918138, by rfl⟩ : syracuseStep 7890851 = 11836277) B11836277
theorem B2918321 : Blo 1295966 2918321 := bstep (se 2 (by rfl) ⟨1094370, by rfl⟩ : syracuseStep 2918321 = 2188741) B2188741
theorem B1296307 : Blo 1295966 1296307 := bstep (se 1 (by rfl) ⟨972230, by rfl⟩ : syracuseStep 1296307 = 1944461) B1944461
theorem B1296323 : Blo 1295966 1296323 := bstep (se 1 (by rfl) ⟨972242, by rfl⟩ : syracuseStep 1296323 = 1944485) B1944485
theorem B2918339 : Blo 1295966 2918339 := bstep (se 1 (by rfl) ⟨2188754, by rfl⟩ : syracuseStep 2918339 = 4377509) B4377509
theorem B1296339 : Blo 1295966 1296339 := bstep (se 1 (by rfl) ⟨972254, by rfl⟩ : syracuseStep 1296339 = 1944509) B1944509
theorem B2189281 : Blo 1295966 2189281 := bstep (se 2 (by rfl) ⟨820980, by rfl⟩ : syracuseStep 2189281 = 1641961) B1641961
theorem B1296355 : Blo 1295966 1296355 := bstep (se 1 (by rfl) ⟨972266, by rfl⟩ : syracuseStep 1296355 = 1944533) B1944533
theorem B1296371 : Blo 1295966 1296371 := bstep (se 1 (by rfl) ⟨972278, by rfl⟩ : syracuseStep 1296371 = 1944557) B1944557
theorem B1296387 : Blo 1295966 1296387 := bstep (se 1 (by rfl) ⟨972290, by rfl⟩ : syracuseStep 1296387 = 1944581) B1944581
theorem B2189315 : Blo 1295966 2189315 := bstep (se 1 (by rfl) ⟨1641986, by rfl⟩ : syracuseStep 2189315 = 3283973) B3283973
theorem B16623629 : Blo 1295966 16623629 := bstep (se 3 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 16623629 = 6233861) B6233861
theorem B1296403 : Blo 1295966 1296403 := bstep (se 1 (by rfl) ⟨972302, by rfl⟩ : syracuseStep 1296403 = 1944605) B1944605
theorem B1296419 : Blo 1295966 1296419 := bstep (se 1 (by rfl) ⟨972314, by rfl⟩ : syracuseStep 1296419 = 1944629) B1944629
theorem B1402931 : Blo 1295966 1402931 := bstep (se 1 (by rfl) ⟨1052198, by rfl⟩ : syracuseStep 1402931 = 2104397) B2104397
theorem B1296435 : Blo 1295966 1296435 := bstep (se 1 (by rfl) ⟨972326, by rfl⟩ : syracuseStep 1296435 = 1944653) B1944653
theorem B1296451 : Blo 1295966 1296451 := bstep (se 1 (by rfl) ⟨972338, by rfl⟩ : syracuseStep 1296451 = 1944677) B1944677
theorem B1296467 : Blo 1295966 1296467 := bstep (se 1 (by rfl) ⟨972350, by rfl⟩ : syracuseStep 1296467 = 1944701) B1944701
theorem B1296483 : Blo 1295966 1296483 := bstep (se 1 (by rfl) ⟨972362, by rfl⟩ : syracuseStep 1296483 = 1944725) B1944725
theorem B1296499 : Blo 1295966 1296499 := bstep (se 1 (by rfl) ⟨972374, by rfl⟩ : syracuseStep 1296499 = 1944749) B1944749
theorem B1296515 : Blo 1295966 1296515 := bstep (se 1 (by rfl) ⟨972386, by rfl⟩ : syracuseStep 1296515 = 1944773) B1944773
theorem B2189443 : Blo 1295966 2189443 := bstep (se 1 (by rfl) ⟨1642082, by rfl⟩ : syracuseStep 2189443 = 3284165) B3284165
theorem B1296531 : Blo 1295966 1296531 := bstep (se 1 (by rfl) ⟨972398, by rfl⟩ : syracuseStep 1296531 = 1944797) B1944797
theorem B1296547 : Blo 1295966 1296547 := bstep (se 1 (by rfl) ⟨972410, by rfl⟩ : syracuseStep 1296547 = 1944821) B1944821
theorem B4671665 : Blo 1295966 4671665 := bstep (se 2 (by rfl) ⟨1751874, by rfl⟩ : syracuseStep 4671665 = 3503749) B3503749
theorem B4376753 : Blo 1295966 4376753 := bstep (se 2 (by rfl) ⟨1641282, by rfl⟩ : syracuseStep 4376753 = 3282565) B3282565
theorem B1296563 : Blo 1295966 1296563 := bstep (se 1 (by rfl) ⟨972422, by rfl⟩ : syracuseStep 1296563 = 1944845) B1944845
theorem B4434115 : Blo 1295966 4434115 := bstep (se 1 (by rfl) ⟨3325586, by rfl⟩ : syracuseStep 4434115 = 6651173) B6651173
theorem B1296579 : Blo 1295966 1296579 := bstep (se 1 (by rfl) ⟨972434, by rfl⟩ : syracuseStep 1296579 = 1944869) B1944869
theorem B3508429 : Blo 1295966 3508429 := bstep (se 3 (by rfl) ⟨657830, by rfl⟩ : syracuseStep 3508429 = 1315661) B1315661
theorem B2918609 : Blo 1295966 2918609 := bstep (se 2 (by rfl) ⟨1094478, by rfl⟩ : syracuseStep 2918609 = 2188957) B2188957
theorem B1296595 : Blo 1295966 1296595 := bstep (se 1 (by rfl) ⟨972446, by rfl⟩ : syracuseStep 1296595 = 1944893) B1944893
theorem B1640675 : Blo 1295966 1640675 := bstep (se 1 (by rfl) ⟨1230506, by rfl⟩ : syracuseStep 1640675 = 2461013) B2461013
theorem B1296611 : Blo 1295966 1296611 := bstep (se 1 (by rfl) ⟨972458, by rfl⟩ : syracuseStep 1296611 = 1944917) B1944917
theorem B2918627 : Blo 1295966 2918627 := bstep (se 1 (by rfl) ⟨2188970, by rfl⟩ : syracuseStep 2918627 = 4377941) B4377941
theorem B1296627 : Blo 1295966 1296627 := bstep (se 1 (by rfl) ⟨972470, by rfl⟩ : syracuseStep 1296627 = 1944941) B1944941
theorem B1296643 : Blo 1295966 1296643 := bstep (se 1 (by rfl) ⟨972482, by rfl⟩ : syracuseStep 1296643 = 1944965) B1944965
theorem B2189585 : Blo 1295966 2189585 := bstep (se 2 (by rfl) ⟨821094, by rfl⟩ : syracuseStep 2189585 = 1642189) B1642189
theorem B1296659 : Blo 1295966 1296659 := bstep (se 1 (by rfl) ⟨972494, by rfl⟩ : syracuseStep 1296659 = 1944989) B1944989
theorem B1296675 : Blo 1295966 1296675 := bstep (se 1 (by rfl) ⟨972506, by rfl⟩ : syracuseStep 1296675 = 1945013) B1945013
theorem B4925731 : Blo 1295966 4925731 := bstep (se 1 (by rfl) ⟨3694298, by rfl⟩ : syracuseStep 4925731 = 7388597) B7388597
theorem B1296691 : Blo 1295966 1296691 := bstep (se 1 (by rfl) ⟨972518, by rfl⟩ : syracuseStep 1296691 = 1945037) B1945037
theorem B1296707 : Blo 1295966 1296707 := bstep (se 1 (by rfl) ⟨972530, by rfl⟩ : syracuseStep 1296707 = 1945061) B1945061
theorem B1296723 : Blo 1295966 1296723 := bstep (se 1 (by rfl) ⟨972542, by rfl⟩ : syracuseStep 1296723 = 1945085) B1945085
theorem B1296739 : Blo 1295966 1296739 := bstep (se 1 (by rfl) ⟨972554, by rfl⟩ : syracuseStep 1296739 = 1945109) B1945109
theorem B1296755 : Blo 1295966 1296755 := bstep (se 1 (by rfl) ⟨972566, by rfl⟩ : syracuseStep 1296755 = 1945133) B1945133
theorem B1296771 : Blo 1295966 1296771 := bstep (se 1 (by rfl) ⟨972578, by rfl⟩ : syracuseStep 1296771 = 1945157) B1945157
theorem B4155779 : Blo 1295966 4155779 := bstep (se 1 (by rfl) ⟨3116834, by rfl⟩ : syracuseStep 4155779 = 6233669) B6233669
theorem B2189713 : Blo 1295966 2189713 := bstep (se 2 (by rfl) ⟨821142, by rfl⟩ : syracuseStep 2189713 = 1642285) B1642285
theorem B1296787 : Blo 1295966 1296787 := bstep (se 1 (by rfl) ⟨972590, by rfl⟩ : syracuseStep 1296787 = 1945181) B1945181
theorem B1943969 : Blo 1295966 1943969 := bstep (se 2 (by rfl) ⟨728988, by rfl⟩ : syracuseStep 1943969 = 1457977) B1457977
theorem B1296803 : Blo 1295966 1296803 := bstep (se 1 (by rfl) ⟨972602, by rfl⟩ : syracuseStep 1296803 = 1945205) B1945205
theorem B7383473 : Blo 1295966 7383473 := bstep (se 2 (by rfl) ⟨2768802, by rfl⟩ : syracuseStep 7383473 = 5537605) B5537605
theorem B1943987 : Blo 1295966 1943987 := bstep (se 1 (by rfl) ⟨1457990, by rfl⟩ : syracuseStep 1943987 = 2915981) B2915981
theorem B1296819 : Blo 1295966 1296819 := bstep (se 1 (by rfl) ⟨972614, by rfl⟩ : syracuseStep 1296819 = 1945229) B1945229
theorem B2189747 : Blo 1295966 2189747 := bstep (se 1 (by rfl) ⟨1642310, by rfl⟩ : syracuseStep 2189747 = 3284621) B3284621
theorem B1296835 : Blo 1295966 1296835 := bstep (se 1 (by rfl) ⟨972626, by rfl⟩ : syracuseStep 1296835 = 1945253) B1945253
theorem B1944017 : Blo 1295966 1944017 := bstep (se 2 (by rfl) ⟨729006, by rfl⟩ : syracuseStep 1944017 = 1458013) B1458013
theorem B1296851 : Blo 1295966 1296851 := bstep (se 1 (by rfl) ⟨972638, by rfl⟩ : syracuseStep 1296851 = 1945277) B1945277
theorem B1944035 : Blo 1295966 1944035 := bstep (se 1 (by rfl) ⟨1458026, by rfl⟩ : syracuseStep 1944035 = 2916053) B2916053
theorem B1296867 : Blo 1295966 1296867 := bstep (se 1 (by rfl) ⟨972650, by rfl⟩ : syracuseStep 1296867 = 1945301) B1945301
theorem B2918897 : Blo 1295966 2918897 := bstep (se 2 (by rfl) ⟨1094586, by rfl⟩ : syracuseStep 2918897 = 2189173) B2189173
theorem B1296883 : Blo 1295966 1296883 := bstep (se 1 (by rfl) ⟨972662, by rfl⟩ : syracuseStep 1296883 = 1945325) B1945325
theorem B1944065 : Blo 1295966 1944065 := bstep (se 2 (by rfl) ⟨729024, by rfl⟩ : syracuseStep 1944065 = 1458049) B1458049
theorem B1296899 : Blo 1295966 1296899 := bstep (se 1 (by rfl) ⟨972674, by rfl⟩ : syracuseStep 1296899 = 1945349) B1945349
theorem B2918915 : Blo 1295966 2918915 := bstep (se 1 (by rfl) ⟨2189186, by rfl⟩ : syracuseStep 2918915 = 4378373) B4378373
theorem B1944083 : Blo 1295966 1944083 := bstep (se 1 (by rfl) ⟨1458062, by rfl⟩ : syracuseStep 1944083 = 2916125) B2916125
theorem B1296915 : Blo 1295966 1296915 := bstep (se 1 (by rfl) ⟨972686, by rfl⟩ : syracuseStep 1296915 = 1945373) B1945373
theorem B1296931 : Blo 1295966 1296931 := bstep (se 1 (by rfl) ⟨972698, by rfl⟩ : syracuseStep 1296931 = 1945397) B1945397
theorem B1944113 : Blo 1295966 1944113 := bstep (se 2 (by rfl) ⟨729042, by rfl⟩ : syracuseStep 1944113 = 1458085) B1458085
theorem B6564401 : Blo 1295966 6564401 := bstep (se 2 (by rfl) ⟨2461650, by rfl⟩ : syracuseStep 6564401 = 4923301) B4923301
theorem B1296947 : Blo 1295966 1296947 := bstep (se 1 (by rfl) ⟨972710, by rfl⟩ : syracuseStep 1296947 = 1945421) B1945421
theorem B2189875 : Blo 1295966 2189875 := bstep (se 1 (by rfl) ⟨1642406, by rfl⟩ : syracuseStep 2189875 = 3284813) B3284813
theorem B1944131 : Blo 1295966 1944131 := bstep (se 1 (by rfl) ⟨1458098, by rfl⟩ : syracuseStep 1944131 = 2916197) B2916197
theorem B1296963 : Blo 1295966 1296963 := bstep (se 1 (by rfl) ⟨972722, by rfl⟩ : syracuseStep 1296963 = 1945445) B1945445
theorem B11840069 : Blo 1295966 11840069 := bstep (se 4 (by rfl) ⟨1110006, by rfl⟩ : syracuseStep 11840069 = 2220013) B2220013
theorem B1296979 : Blo 1295966 1296979 := bstep (se 1 (by rfl) ⟨972734, by rfl⟩ : syracuseStep 1296979 = 1945469) B1945469
theorem B1944161 : Blo 1295966 1944161 := bstep (se 2 (by rfl) ⟨729060, by rfl⟩ : syracuseStep 1944161 = 1458121) B1458121
theorem B1296995 : Blo 1295966 1296995 := bstep (se 1 (by rfl) ⟨972746, by rfl⟩ : syracuseStep 1296995 = 1945493) B1945493
theorem B1944179 : Blo 1295966 1944179 := bstep (se 1 (by rfl) ⟨1458134, by rfl⟩ : syracuseStep 1944179 = 2916269) B2916269
theorem B1297011 : Blo 1295966 1297011 := bstep (se 1 (by rfl) ⟨972758, by rfl⟩ : syracuseStep 1297011 = 1945517) B1945517
theorem B1297027 : Blo 1295966 1297027 := bstep (se 1 (by rfl) ⟨972770, by rfl⟩ : syracuseStep 1297027 = 1945541) B1945541
theorem B1944209 : Blo 1295966 1944209 := bstep (se 2 (by rfl) ⟨729078, by rfl⟩ : syracuseStep 1944209 = 1458157) B1458157
theorem B2337425 : Blo 1295966 2337425 := bstep (se 2 (by rfl) ⟨876534, by rfl⟩ : syracuseStep 2337425 = 1753069) B1753069
theorem B1297043 : Blo 1295966 1297043 := bstep (se 1 (by rfl) ⟨972782, by rfl⟩ : syracuseStep 1297043 = 1945565) B1945565
theorem B1944227 : Blo 1295966 1944227 := bstep (se 1 (by rfl) ⟨1458170, by rfl⟩ : syracuseStep 1944227 = 2916341) B2916341
theorem B1297059 : Blo 1295966 1297059 := bstep (se 1 (by rfl) ⟨972794, by rfl⟩ : syracuseStep 1297059 = 1945589) B1945589
theorem B1297075 : Blo 1295966 1297075 := bstep (se 1 (by rfl) ⟨972806, by rfl⟩ : syracuseStep 1297075 = 1945613) B1945613
theorem B1944257 : Blo 1295966 1944257 := bstep (se 2 (by rfl) ⟨729096, by rfl⟩ : syracuseStep 1944257 = 1458193) B1458193
theorem B2190017 : Blo 1295966 2190017 := bstep (se 2 (by rfl) ⟨821256, by rfl⟩ : syracuseStep 2190017 = 1642513) B1642513
theorem B1297091 : Blo 1295966 1297091 := bstep (se 1 (by rfl) ⟨972818, by rfl⟩ : syracuseStep 1297091 = 1945637) B1945637
theorem B4377293 : Blo 1295966 4377293 := bstep (se 3 (by rfl) ⟨820742, by rfl⟩ : syracuseStep 4377293 = 1641485) B1641485
theorem B1944275 : Blo 1295966 1944275 := bstep (se 1 (by rfl) ⟨1458206, by rfl⟩ : syracuseStep 1944275 = 2916413) B2916413
theorem B1297107 : Blo 1295966 1297107 := bstep (se 1 (by rfl) ⟨972830, by rfl⟩ : syracuseStep 1297107 = 1945661) B1945661
theorem B1297123 : Blo 1295966 1297123 := bstep (se 1 (by rfl) ⟨972842, by rfl⟩ : syracuseStep 1297123 = 1945685) B1945685
theorem B1944305 : Blo 1295966 1944305 := bstep (se 2 (by rfl) ⟨729114, by rfl⟩ : syracuseStep 1944305 = 1458229) B1458229
theorem B1297139 : Blo 1295966 1297139 := bstep (se 1 (by rfl) ⟨972854, by rfl⟩ : syracuseStep 1297139 = 1945709) B1945709
theorem B1944323 : Blo 1295966 1944323 := bstep (se 1 (by rfl) ⟨1458242, by rfl⟩ : syracuseStep 1944323 = 2916485) B2916485
theorem B4377347 : Blo 1295966 4377347 := bstep (se 1 (by rfl) ⟨3283010, by rfl⟩ : syracuseStep 4377347 = 6566021) B6566021
theorem B1297155 : Blo 1295966 1297155 := bstep (se 1 (by rfl) ⟨972866, by rfl⟩ : syracuseStep 1297155 = 1945733) B1945733
theorem B2919185 : Blo 1295966 2919185 := bstep (se 2 (by rfl) ⟨1094694, by rfl⟩ : syracuseStep 2919185 = 2189389) B2189389
theorem B1297171 : Blo 1295966 1297171 := bstep (se 1 (by rfl) ⟨972878, by rfl⟩ : syracuseStep 1297171 = 1945757) B1945757
theorem B59894549 : Blo 1295966 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B1944353 : Blo 1295966 1944353 := bstep (se 2 (by rfl) ⟨729132, by rfl⟩ : syracuseStep 1944353 = 1458265) B1458265
theorem B2460451 : Blo 1295966 2460451 := bstep (se 1 (by rfl) ⟨1845338, by rfl⟩ : syracuseStep 2460451 = 3690677) B3690677
theorem B1297187 : Blo 1295966 1297187 := bstep (se 1 (by rfl) ⟨972890, by rfl⟩ : syracuseStep 1297187 = 1945781) B1945781
theorem B2919203 : Blo 1295966 2919203 := bstep (se 1 (by rfl) ⟨2189402, by rfl⟩ : syracuseStep 2919203 = 4378805) B4378805
theorem B1944371 : Blo 1295966 1944371 := bstep (se 1 (by rfl) ⟨1458278, by rfl⟩ : syracuseStep 1944371 = 2916557) B2916557
theorem B1297203 : Blo 1295966 1297203 := bstep (se 1 (by rfl) ⟨972902, by rfl⟩ : syracuseStep 1297203 = 1945805) B1945805
theorem B2190145 : Blo 1295966 2190145 := bstep (se 2 (by rfl) ⟨821304, by rfl⟩ : syracuseStep 2190145 = 1642609) B1642609
theorem B1297219 : Blo 1295966 1297219 := bstep (se 1 (by rfl) ⟨972914, by rfl⟩ : syracuseStep 1297219 = 1945829) B1945829
theorem B1944401 : Blo 1295966 1944401 := bstep (se 2 (by rfl) ⟨729150, by rfl⟩ : syracuseStep 1944401 = 1458301) B1458301
theorem B1297235 : Blo 1295966 1297235 := bstep (se 1 (by rfl) ⟨972926, by rfl⟩ : syracuseStep 1297235 = 1945853) B1945853
theorem B1944419 : Blo 1295966 1944419 := bstep (se 1 (by rfl) ⟨1458314, by rfl⟩ : syracuseStep 1944419 = 2916629) B2916629
theorem B1297251 : Blo 1295966 1297251 := bstep (se 1 (by rfl) ⟨972938, by rfl⟩ : syracuseStep 1297251 = 1945877) B1945877
theorem B2190179 : Blo 1295966 2190179 := bstep (se 1 (by rfl) ⟨1642634, by rfl⟩ : syracuseStep 2190179 = 3285269) B3285269
theorem B1297267 : Blo 1295966 1297267 := bstep (se 1 (by rfl) ⟨972950, by rfl⟩ : syracuseStep 1297267 = 1945901) B1945901
theorem B3246961 : Blo 1295966 3246961 := bstep (se 2 (by rfl) ⟨1217610, by rfl⟩ : syracuseStep 3246961 = 2435221) B2435221
theorem B1944449 : Blo 1295966 1944449 := bstep (se 2 (by rfl) ⟨729168, by rfl⟩ : syracuseStep 1944449 = 1458337) B1458337
theorem B1846147 : Blo 1295966 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B1297283 : Blo 1295966 1297283 := bstep (se 1 (by rfl) ⟨972962, by rfl⟩ : syracuseStep 1297283 = 1945925) B1945925
theorem B1944467 : Blo 1295966 1944467 := bstep (se 1 (by rfl) ⟨1458350, by rfl⟩ : syracuseStep 1944467 = 2916701) B2916701
theorem B1297299 : Blo 1295966 1297299 := bstep (se 1 (by rfl) ⟨972974, by rfl⟩ : syracuseStep 1297299 = 1945949) B1945949
theorem B1641379 : Blo 1295966 1641379 := bstep (se 1 (by rfl) ⟨1231034, by rfl⟩ : syracuseStep 1641379 = 2462069) B2462069
theorem B1297315 : Blo 1295966 1297315 := bstep (se 1 (by rfl) ⟨972986, by rfl⟩ : syracuseStep 1297315 = 1945973) B1945973
theorem B1944497 : Blo 1295966 1944497 := bstep (se 2 (by rfl) ⟨729186, by rfl⟩ : syracuseStep 1944497 = 1458373) B1458373
theorem B1297331 : Blo 1295966 1297331 := bstep (se 1 (by rfl) ⟨972998, by rfl⟩ : syracuseStep 1297331 = 1945997) B1945997
theorem B2460611 : Blo 1295966 2460611 := bstep (se 1 (by rfl) ⟨1845458, by rfl⟩ : syracuseStep 2460611 = 3690917) B3690917
theorem B1944515 : Blo 1295966 1944515 := bstep (se 1 (by rfl) ⟨1458386, by rfl⟩ : syracuseStep 1944515 = 2916773) B2916773
theorem B1297347 : Blo 1295966 1297347 := bstep (se 1 (by rfl) ⟨973010, by rfl⟩ : syracuseStep 1297347 = 1946021) B1946021
theorem B2771921 : Blo 1295966 2771921 := bstep (se 2 (by rfl) ⟨1039470, by rfl⟩ : syracuseStep 2771921 = 2078941) B2078941
theorem B1297363 : Blo 1295966 1297363 := bstep (se 1 (by rfl) ⟨973022, by rfl⟩ : syracuseStep 1297363 = 1946045) B1946045
theorem B1944545 : Blo 1295966 1944545 := bstep (se 2 (by rfl) ⟨729204, by rfl⟩ : syracuseStep 1944545 = 1458409) B1458409
theorem B1297379 : Blo 1295966 1297379 := bstep (se 1 (by rfl) ⟨973034, by rfl⟩ : syracuseStep 1297379 = 1946069) B1946069
theorem B2190307 : Blo 1295966 2190307 := bstep (se 1 (by rfl) ⟨1642730, by rfl⟩ : syracuseStep 2190307 = 3285461) B3285461
theorem B1944563 : Blo 1295966 1944563 := bstep (se 1 (by rfl) ⟨1458422, by rfl⟩ : syracuseStep 1944563 = 2916845) B2916845
theorem B1297395 : Blo 1295966 1297395 := bstep (se 1 (by rfl) ⟨973046, by rfl⟩ : syracuseStep 1297395 = 1946093) B1946093
theorem B1641475 : Blo 1295966 1641475 := bstep (se 1 (by rfl) ⟨1231106, by rfl⟩ : syracuseStep 1641475 = 2462213) B2462213
theorem B1297411 : Blo 1295966 1297411 := bstep (se 1 (by rfl) ⟨973058, by rfl⟩ : syracuseStep 1297411 = 1946117) B1946117
theorem B1944593 : Blo 1295966 1944593 := bstep (se 2 (by rfl) ⟨729222, by rfl⟩ : syracuseStep 1944593 = 1458445) B1458445
theorem B4377617 : Blo 1295966 4377617 := bstep (se 2 (by rfl) ⟨1641606, by rfl⟩ : syracuseStep 4377617 = 3283213) B3283213
theorem B1297427 : Blo 1295966 1297427 := bstep (se 1 (by rfl) ⟨973070, by rfl⟩ : syracuseStep 1297427 = 1946141) B1946141
theorem B1944611 : Blo 1295966 1944611 := bstep (se 1 (by rfl) ⟨1458458, by rfl⟩ : syracuseStep 1944611 = 2916917) B2916917
theorem B1297443 : Blo 1295966 1297443 := bstep (se 1 (by rfl) ⟨973082, by rfl⟩ : syracuseStep 1297443 = 1946165) B1946165
theorem B2919473 : Blo 1295966 2919473 := bstep (se 2 (by rfl) ⟨1094802, by rfl⟩ : syracuseStep 2919473 = 2189605) B2189605
theorem B1297459 : Blo 1295966 1297459 := bstep (se 1 (by rfl) ⟨973094, by rfl⟩ : syracuseStep 1297459 = 1946189) B1946189
theorem B1944641 : Blo 1295966 1944641 := bstep (se 2 (by rfl) ⟨729240, by rfl⟩ : syracuseStep 1944641 = 1458481) B1458481
theorem B1297475 : Blo 1295966 1297475 := bstep (se 1 (by rfl) ⟨973106, by rfl⟩ : syracuseStep 1297475 = 1946213) B1946213
theorem B2919491 : Blo 1295966 2919491 := bstep (se 1 (by rfl) ⟨2189618, by rfl⟩ : syracuseStep 2919491 = 4379237) B4379237
theorem B1944659 : Blo 1295966 1944659 := bstep (se 1 (by rfl) ⟨1458494, by rfl⟩ : syracuseStep 1944659 = 2916989) B2916989
theorem B1297491 : Blo 1295966 1297491 := bstep (se 1 (by rfl) ⟨973118, by rfl⟩ : syracuseStep 1297491 = 1946237) B1946237
theorem B1297507 : Blo 1295966 1297507 := bstep (se 1 (by rfl) ⟨973130, by rfl⟩ : syracuseStep 1297507 = 1946261) B1946261
theorem B1944689 : Blo 1295966 1944689 := bstep (se 2 (by rfl) ⟨729258, by rfl⟩ : syracuseStep 1944689 = 1458517) B1458517
theorem B1297523 : Blo 1295966 1297523 := bstep (se 1 (by rfl) ⟨973142, by rfl⟩ : syracuseStep 1297523 = 1946285) B1946285
theorem B3157123 : Blo 1295966 3157123 := bstep (se 1 (by rfl) ⟨2367842, by rfl⟩ : syracuseStep 3157123 = 4735685) B4735685
theorem B1944707 : Blo 1295966 1944707 := bstep (se 1 (by rfl) ⟨1458530, by rfl⟩ : syracuseStep 1944707 = 2917061) B2917061
theorem B1297539 : Blo 1295966 1297539 := bstep (se 1 (by rfl) ⟨973154, by rfl⟩ : syracuseStep 1297539 = 1946309) B1946309
theorem B1297555 : Blo 1295966 1297555 := bstep (se 1 (by rfl) ⟨973166, by rfl⟩ : syracuseStep 1297555 = 1946333) B1946333
theorem B1944737 : Blo 1295966 1944737 := bstep (se 2 (by rfl) ⟨729276, by rfl⟩ : syracuseStep 1944737 = 1458553) B1458553
theorem B1297571 : Blo 1295966 1297571 := bstep (se 1 (by rfl) ⟨973178, by rfl⟩ : syracuseStep 1297571 = 1946357) B1946357
theorem B1944755 : Blo 1295966 1944755 := bstep (se 1 (by rfl) ⟨1458566, by rfl⟩ : syracuseStep 1944755 = 2917133) B2917133
theorem B1297587 : Blo 1295966 1297587 := bstep (se 1 (by rfl) ⟨973190, by rfl⟩ : syracuseStep 1297587 = 1946381) B1946381
theorem B1297603 : Blo 1295966 1297603 := bstep (se 1 (by rfl) ⟨973202, by rfl⟩ : syracuseStep 1297603 = 1946405) B1946405
theorem B1944785 : Blo 1295966 1944785 := bstep (se 2 (by rfl) ⟨729294, by rfl⟩ : syracuseStep 1944785 = 1458589) B1458589
theorem B1297619 : Blo 1295966 1297619 := bstep (se 1 (by rfl) ⟨973214, by rfl⟩ : syracuseStep 1297619 = 1946429) B1946429
theorem B1944803 : Blo 1295966 1944803 := bstep (se 1 (by rfl) ⟨1458602, by rfl⟩ : syracuseStep 1944803 = 2917205) B2917205
theorem B1297635 : Blo 1295966 1297635 := bstep (se 1 (by rfl) ⟨973226, by rfl⟩ : syracuseStep 1297635 = 1946453) B1946453
theorem B2133233 : Blo 1295966 2133233 := bstep (se 2 (by rfl) ⟨799962, by rfl⟩ : syracuseStep 2133233 = 1599925) B1599925
theorem B1297651 : Blo 1295966 1297651 := bstep (se 1 (by rfl) ⟨973238, by rfl⟩ : syracuseStep 1297651 = 1946477) B1946477
theorem B1871105 : Blo 1295966 1871105 := bstep (se 2 (by rfl) ⟨701664, by rfl⟩ : syracuseStep 1871105 = 1403329) B1403329
theorem B1944833 : Blo 1295966 1944833 := bstep (se 2 (by rfl) ⟨729312, by rfl⟩ : syracuseStep 1944833 = 1458625) B1458625
theorem B1297667 : Blo 1295966 1297667 := bstep (se 1 (by rfl) ⟨973250, by rfl⟩ : syracuseStep 1297667 = 1946501) B1946501
theorem B7105805 : Blo 1295966 7105805 := bstep (se 3 (by rfl) ⟨1332338, by rfl⟩ : syracuseStep 7105805 = 2664677) B2664677
theorem B1944851 : Blo 1295966 1944851 := bstep (se 1 (by rfl) ⟨1458638, by rfl⟩ : syracuseStep 1944851 = 2917277) B2917277
theorem B1297683 : Blo 1295966 1297683 := bstep (se 1 (by rfl) ⟨973262, by rfl⟩ : syracuseStep 1297683 = 1946525) B1946525
theorem B1297699 : Blo 1295966 1297699 := bstep (se 1 (by rfl) ⟨973274, by rfl⟩ : syracuseStep 1297699 = 1946549) B1946549
theorem B1944881 : Blo 1295966 1944881 := bstep (se 2 (by rfl) ⟨729330, by rfl⟩ : syracuseStep 1944881 = 1458661) B1458661
theorem B1297715 : Blo 1295966 1297715 := bstep (se 1 (by rfl) ⟨973286, by rfl⟩ : syracuseStep 1297715 = 1946573) B1946573
theorem B1944899 : Blo 1295966 1944899 := bstep (se 1 (by rfl) ⟨1458674, by rfl⟩ : syracuseStep 1944899 = 2917349) B2917349
theorem B1297731 : Blo 1295966 1297731 := bstep (se 1 (by rfl) ⟨973298, by rfl⟩ : syracuseStep 1297731 = 1946597) B1946597
theorem B4156753 : Blo 1295966 4156753 := bstep (se 2 (by rfl) ⟨1558782, by rfl⟩ : syracuseStep 4156753 = 3117565) B3117565
theorem B2075987 : Blo 1295966 2075987 := bstep (se 1 (by rfl) ⟨1556990, by rfl⟩ : syracuseStep 2075987 = 3113981) B3113981
theorem B2919761 : Blo 1295966 2919761 := bstep (se 2 (by rfl) ⟨1094910, by rfl⟩ : syracuseStep 2919761 = 2189821) B2189821
theorem B1297747 : Blo 1295966 1297747 := bstep (se 1 (by rfl) ⟨973310, by rfl⟩ : syracuseStep 1297747 = 1946621) B1946621
theorem B1944929 : Blo 1295966 1944929 := bstep (se 2 (by rfl) ⟨729348, by rfl⟩ : syracuseStep 1944929 = 1458697) B1458697
theorem B2919779 : Blo 1295966 2919779 := bstep (se 1 (by rfl) ⟨2189834, by rfl⟩ : syracuseStep 2919779 = 4379669) B4379669
theorem B1297763 : Blo 1295966 1297763 := bstep (se 1 (by rfl) ⟨973322, by rfl⟩ : syracuseStep 1297763 = 1946645) B1946645
theorem B1944947 : Blo 1295966 1944947 := bstep (se 1 (by rfl) ⟨1458710, by rfl⟩ : syracuseStep 1944947 = 2917421) B2917421
theorem B1297779 : Blo 1295966 1297779 := bstep (se 1 (by rfl) ⟨973334, by rfl⟩ : syracuseStep 1297779 = 1946669) B1946669
theorem B1297795 : Blo 1295966 1297795 := bstep (se 1 (by rfl) ⟨973346, by rfl⟩ : syracuseStep 1297795 = 1946693) B1946693
theorem B1944977 : Blo 1295966 1944977 := bstep (se 2 (by rfl) ⟨729366, by rfl⟩ : syracuseStep 1944977 = 1458733) B1458733
theorem B1297811 : Blo 1295966 1297811 := bstep (se 1 (by rfl) ⟨973358, by rfl⟩ : syracuseStep 1297811 = 1946717) B1946717
theorem B1944995 : Blo 1295966 1944995 := bstep (se 1 (by rfl) ⟨1458746, by rfl⟩ : syracuseStep 1944995 = 2917493) B2917493
theorem B1297827 : Blo 1295966 1297827 := bstep (se 1 (by rfl) ⟨973370, by rfl⟩ : syracuseStep 1297827 = 1946741) B1946741
theorem B1297843 : Blo 1295966 1297843 := bstep (se 1 (by rfl) ⟨973382, by rfl⟩ : syracuseStep 1297843 = 1946765) B1946765
theorem B1945025 : Blo 1295966 1945025 := bstep (se 2 (by rfl) ⟨729384, by rfl⟩ : syracuseStep 1945025 = 1458769) B1458769
theorem B1297859 : Blo 1295966 1297859 := bstep (se 1 (by rfl) ⟨973394, by rfl⟩ : syracuseStep 1297859 = 1946789) B1946789
theorem B1945043 : Blo 1295966 1945043 := bstep (se 1 (by rfl) ⟨1458782, by rfl⟩ : syracuseStep 1945043 = 2917565) B2917565
theorem B1297875 : Blo 1295966 1297875 := bstep (se 1 (by rfl) ⟨973406, by rfl⟩ : syracuseStep 1297875 = 1946813) B1946813
theorem B1297891 : Blo 1295966 1297891 := bstep (se 1 (by rfl) ⟨973418, by rfl⟩ : syracuseStep 1297891 = 1946837) B1946837
theorem B1945073 : Blo 1295966 1945073 := bstep (se 2 (by rfl) ⟨729402, by rfl⟩ : syracuseStep 1945073 = 1458805) B1458805
theorem B1641971 : Blo 1295966 1641971 := bstep (se 1 (by rfl) ⟨1231478, by rfl⟩ : syracuseStep 1641971 = 2462957) B2462957
theorem B1297907 : Blo 1295966 1297907 := bstep (se 1 (by rfl) ⟨973430, by rfl⟩ : syracuseStep 1297907 = 1946861) B1946861
theorem B1945091 : Blo 1295966 1945091 := bstep (se 1 (by rfl) ⟨1458818, by rfl⟩ : syracuseStep 1945091 = 2917637) B2917637
theorem B1297923 : Blo 1295966 1297923 := bstep (se 1 (by rfl) ⟨973442, by rfl⟩ : syracuseStep 1297923 = 1946885) B1946885
theorem B1297939 : Blo 1295966 1297939 := bstep (se 1 (by rfl) ⟨973454, by rfl⟩ : syracuseStep 1297939 = 1946909) B1946909
theorem B1945121 : Blo 1295966 1945121 := bstep (se 2 (by rfl) ⟨729420, by rfl⟩ : syracuseStep 1945121 = 1458841) B1458841
theorem B1297955 : Blo 1295966 1297955 := bstep (se 1 (by rfl) ⟨973466, by rfl⟩ : syracuseStep 1297955 = 1946933) B1946933
theorem B4378157 : Blo 1295966 4378157 := bstep (se 3 (by rfl) ⟨820904, by rfl⟩ : syracuseStep 4378157 = 1641809) B1641809
theorem B1945139 : Blo 1295966 1945139 := bstep (se 1 (by rfl) ⟨1458854, by rfl⟩ : syracuseStep 1945139 = 2917709) B2917709
theorem B15773237 : Blo 1295966 15773237 := bstep (se 5 (by rfl) ⟨739370, by rfl⟩ : syracuseStep 15773237 = 1478741) B1478741
theorem B1945169 : Blo 1295966 1945169 := bstep (se 2 (by rfl) ⟨729438, by rfl⟩ : syracuseStep 1945169 = 1458877) B1458877
theorem B4157009 : Blo 1295966 4157009 := bstep (se 2 (by rfl) ⟨1558878, by rfl⟩ : syracuseStep 4157009 = 3117757) B3117757
theorem B1945187 : Blo 1295966 1945187 := bstep (se 1 (by rfl) ⟨1458890, by rfl⟩ : syracuseStep 1945187 = 2917781) B2917781
theorem B4378211 : Blo 1295966 4378211 := bstep (se 1 (by rfl) ⟨3283658, by rfl⟩ : syracuseStep 4378211 = 6567317) B6567317
theorem B22163057 : Blo 1295966 22163057 := bstep (se 2 (by rfl) ⟨8311146, by rfl⟩ : syracuseStep 22163057 = 16622293) B16622293
theorem B2920049 : Blo 1295966 2920049 := bstep (se 2 (by rfl) ⟨1095018, by rfl⟩ : syracuseStep 2920049 = 2190037) B2190037
theorem B1945217 : Blo 1295966 1945217 := bstep (se 2 (by rfl) ⟨729456, by rfl⟩ : syracuseStep 1945217 = 1458913) B1458913
theorem B2920067 : Blo 1295966 2920067 := bstep (se 1 (by rfl) ⟨2190050, by rfl⟩ : syracuseStep 2920067 = 4380101) B4380101
theorem B1945235 : Blo 1295966 1945235 := bstep (se 1 (by rfl) ⟨1458926, by rfl⟩ : syracuseStep 1945235 = 2917853) B2917853
theorem B1945265 : Blo 1295966 1945265 := bstep (se 2 (by rfl) ⟨729474, by rfl⟩ : syracuseStep 1945265 = 1458949) B1458949
theorem B1945283 : Blo 1295966 1945283 := bstep (se 1 (by rfl) ⟨1458962, by rfl⟩ : syracuseStep 1945283 = 2917925) B2917925
theorem B1945313 : Blo 1295966 1945313 := bstep (se 2 (by rfl) ⟨729492, by rfl⟩ : syracuseStep 1945313 = 1458985) B1458985
theorem B2076403 : Blo 1295966 2076403 := bstep (se 1 (by rfl) ⟨1557302, by rfl⟩ : syracuseStep 2076403 = 3114605) B3114605
theorem B1945331 : Blo 1295966 1945331 := bstep (se 1 (by rfl) ⟨1458998, by rfl⟩ : syracuseStep 1945331 = 2917997) B2917997
theorem B3329795 : Blo 1295966 3329795 := bstep (se 1 (by rfl) ⟨2497346, by rfl⟩ : syracuseStep 3329795 = 4994693) B4994693
theorem B1945361 : Blo 1295966 1945361 := bstep (se 2 (by rfl) ⟨729510, by rfl⟩ : syracuseStep 1945361 = 1459021) B1459021
theorem B1945379 : Blo 1295966 1945379 := bstep (se 1 (by rfl) ⟨1459034, by rfl⟩ : syracuseStep 1945379 = 2918069) B2918069
theorem B1945409 : Blo 1295966 1945409 := bstep (se 2 (by rfl) ⟨729528, by rfl⟩ : syracuseStep 1945409 = 1459057) B1459057
theorem B1945427 : Blo 1295966 1945427 := bstep (se 1 (by rfl) ⟨1459070, by rfl⟩ : syracuseStep 1945427 = 2918141) B2918141
theorem B7384931 : Blo 1295966 7384931 := bstep (se 1 (by rfl) ⟨5538698, by rfl⟩ : syracuseStep 7384931 = 11077397) B11077397
theorem B1945457 : Blo 1295966 1945457 := bstep (se 2 (by rfl) ⟨729546, by rfl⟩ : syracuseStep 1945457 = 1459093) B1459093
theorem B4378481 : Blo 1295966 4378481 := bstep (se 2 (by rfl) ⟨1641930, by rfl⟩ : syracuseStep 4378481 = 3283861) B3283861
theorem B11235185 : Blo 1295966 11235185 := bstep (se 2 (by rfl) ⟨4213194, by rfl⟩ : syracuseStep 11235185 = 8426389) B8426389
theorem B1945475 : Blo 1295966 1945475 := bstep (se 1 (by rfl) ⟨1459106, by rfl⟩ : syracuseStep 1945475 = 2918213) B2918213
theorem B2920337 : Blo 1295966 2920337 := bstep (se 2 (by rfl) ⟨1095126, by rfl⟩ : syracuseStep 2920337 = 2190253) B2190253
theorem B1945505 : Blo 1295966 1945505 := bstep (se 2 (by rfl) ⟨729564, by rfl⟩ : syracuseStep 1945505 = 1459129) B1459129
theorem B2920355 : Blo 1295966 2920355 := bstep (se 1 (by rfl) ⟨2190266, by rfl⟩ : syracuseStep 2920355 = 4380533) B4380533
theorem B1945523 : Blo 1295966 1945523 := bstep (se 1 (by rfl) ⟨1459142, by rfl⟩ : syracuseStep 1945523 = 2918285) B2918285
theorem B1945553 : Blo 1295966 1945553 := bstep (se 2 (by rfl) ⟨729582, by rfl⟩ : syracuseStep 1945553 = 1459165) B1459165
theorem B6565859 : Blo 1295966 6565859 := bstep (se 1 (by rfl) ⟨4924394, by rfl⟩ : syracuseStep 6565859 = 9848789) B9848789
theorem B1945571 : Blo 1295966 1945571 := bstep (se 1 (by rfl) ⟨1459178, by rfl⟩ : syracuseStep 1945571 = 2918357) B2918357
theorem B14970865 : Blo 1295966 14970865 := bstep (se 2 (by rfl) ⟨5614074, by rfl⟩ : syracuseStep 14970865 = 11228149) B11228149
theorem B2461681 : Blo 1295966 2461681 := bstep (se 2 (by rfl) ⟨923130, by rfl⟩ : syracuseStep 2461681 = 1846261) B1846261
theorem B1847281 : Blo 1295966 1847281 := bstep (se 2 (by rfl) ⟨692730, by rfl⟩ : syracuseStep 1847281 = 1385461) B1385461
theorem B2076673 : Blo 1295966 2076673 := bstep (se 2 (by rfl) ⟨778752, by rfl⟩ : syracuseStep 2076673 = 1557505) B1557505
theorem B1945601 : Blo 1295966 1945601 := bstep (se 2 (by rfl) ⟨729600, by rfl⟩ : syracuseStep 1945601 = 1459201) B1459201
theorem B1945619 : Blo 1295966 1945619 := bstep (se 1 (by rfl) ⟨1459214, by rfl⟩ : syracuseStep 1945619 = 2918429) B2918429
theorem B3280945 : Blo 1295966 3280945 := bstep (se 2 (by rfl) ⟨1230354, by rfl⟩ : syracuseStep 3280945 = 2460709) B2460709
theorem B1945649 : Blo 1295966 1945649 := bstep (se 2 (by rfl) ⟨729618, by rfl⟩ : syracuseStep 1945649 = 1459237) B1459237
theorem B1945667 : Blo 1295966 1945667 := bstep (se 1 (by rfl) ⟨1459250, by rfl⟩ : syracuseStep 1945667 = 2918501) B2918501
theorem B1314883 : Blo 1295966 1314883 := bstep (se 1 (by rfl) ⟨986162, by rfl⟩ : syracuseStep 1314883 = 1972325) B1972325
theorem B1847377 : Blo 1295966 1847377 := bstep (se 2 (by rfl) ⟨692766, by rfl⟩ : syracuseStep 1847377 = 1385533) B1385533
theorem B1945697 : Blo 1295966 1945697 := bstep (se 2 (by rfl) ⟨729636, by rfl⟩ : syracuseStep 1945697 = 1459273) B1459273
theorem B1945715 : Blo 1295966 1945715 := bstep (se 1 (by rfl) ⟨1459286, by rfl⟩ : syracuseStep 1945715 = 2918573) B2918573
theorem B1945745 : Blo 1295966 1945745 := bstep (se 2 (by rfl) ⟨729654, by rfl⟩ : syracuseStep 1945745 = 1459309) B1459309
theorem B1945763 : Blo 1295966 1945763 := bstep (se 1 (by rfl) ⟨1459322, by rfl⟩ : syracuseStep 1945763 = 2918645) B2918645
theorem B1642675 : Blo 1295966 1642675 := bstep (se 1 (by rfl) ⟨1232006, by rfl⟩ : syracuseStep 1642675 = 2464013) B2464013
theorem B1945793 : Blo 1295966 1945793 := bstep (se 2 (by rfl) ⟨729672, by rfl⟩ : syracuseStep 1945793 = 1459345) B1459345
theorem B14782661 : Blo 1295966 14782661 := bstep (se 4 (by rfl) ⟨1385874, by rfl⟩ : syracuseStep 14782661 = 2771749) B2771749
theorem B1945811 : Blo 1295966 1945811 := bstep (se 1 (by rfl) ⟨1459358, by rfl⟩ : syracuseStep 1945811 = 2918717) B2918717
theorem B10801379 : Blo 1295966 10801379 := bstep (se 1 (by rfl) ⟨8101034, by rfl⟩ : syracuseStep 10801379 = 16202069) B16202069
theorem B1945841 : Blo 1295966 1945841 := bstep (se 2 (by rfl) ⟨729690, by rfl⟩ : syracuseStep 1945841 = 1459381) B1459381
theorem B2076929 : Blo 1295966 2076929 := bstep (se 2 (by rfl) ⟨778848, by rfl⟩ : syracuseStep 2076929 = 1557697) B1557697
theorem B1945859 : Blo 1295966 1945859 := bstep (se 1 (by rfl) ⟨1459394, by rfl⟩ : syracuseStep 1945859 = 2918789) B2918789
theorem B8311045 : Blo 1295966 8311045 := bstep (se 4 (by rfl) ⟨779160, by rfl⟩ : syracuseStep 8311045 = 1558321) B1558321
theorem B9842957 : Blo 1295966 9842957 := bstep (se 3 (by rfl) ⟨1845554, by rfl⟩ : syracuseStep 9842957 = 3691109) B3691109
theorem B3551501 : Blo 1295966 3551501 := bstep (se 3 (by rfl) ⟨665906, by rfl⟩ : syracuseStep 3551501 = 1331813) B1331813
theorem B6230285 : Blo 1295966 6230285 := bstep (se 3 (by rfl) ⟨1168178, by rfl⟩ : syracuseStep 6230285 = 2336357) B2336357
theorem B1945889 : Blo 1295966 1945889 := bstep (se 2 (by rfl) ⟨729708, by rfl⟩ : syracuseStep 1945889 = 1459417) B1459417
theorem B1945907 : Blo 1295966 1945907 := bstep (se 1 (by rfl) ⟨1459430, by rfl⟩ : syracuseStep 1945907 = 2918861) B2918861
theorem B3281219 : Blo 1295966 3281219 := bstep (se 1 (by rfl) ⟨2460914, by rfl⟩ : syracuseStep 3281219 = 4921829) B4921829
theorem B3944771 : Blo 1295966 3944771 := bstep (se 1 (by rfl) ⟨2958578, by rfl⟩ : syracuseStep 3944771 = 5917157) B5917157
theorem B1945937 : Blo 1295966 1945937 := bstep (se 2 (by rfl) ⟨729726, by rfl⟩ : syracuseStep 1945937 = 1459453) B1459453
theorem B1945955 : Blo 1295966 1945955 := bstep (se 1 (by rfl) ⟨1459466, by rfl⟩ : syracuseStep 1945955 = 2918933) B2918933
theorem B1945985 : Blo 1295966 1945985 := bstep (se 2 (by rfl) ⟨729744, by rfl⟩ : syracuseStep 1945985 = 1459489) B1459489
theorem B4379021 : Blo 1295966 4379021 := bstep (se 3 (by rfl) ⟨821066, by rfl⟩ : syracuseStep 4379021 = 1642133) B1642133
theorem B1946003 : Blo 1295966 1946003 := bstep (se 1 (by rfl) ⟨1459502, by rfl⟩ : syracuseStep 1946003 = 2919005) B2919005
theorem B2494883 : Blo 1295966 2494883 := bstep (se 1 (by rfl) ⟨1871162, by rfl⟩ : syracuseStep 2494883 = 3742325) B3742325
theorem B1946033 : Blo 1295966 1946033 := bstep (se 2 (by rfl) ⟨729762, by rfl⟩ : syracuseStep 1946033 = 1459525) B1459525
theorem B1479107 : Blo 1295966 1479107 := bstep (se 1 (by rfl) ⟨1109330, by rfl⟩ : syracuseStep 1479107 = 2218661) B2218661
theorem B1946051 : Blo 1295966 1946051 := bstep (se 1 (by rfl) ⟨1459538, by rfl⟩ : syracuseStep 1946051 = 2919077) B2919077
theorem B4379075 : Blo 1295966 4379075 := bstep (se 1 (by rfl) ⟨3284306, by rfl⟩ : syracuseStep 4379075 = 6568613) B6568613
theorem B4927949 : Blo 1295966 4927949 := bstep (se 3 (by rfl) ⟨923990, by rfl⟩ : syracuseStep 4927949 = 1847981) B1847981
theorem B1946081 : Blo 1295966 1946081 := bstep (se 2 (by rfl) ⟨729780, by rfl⟩ : syracuseStep 1946081 = 1459561) B1459561
theorem B11989475 : Blo 1295966 11989475 := bstep (se 1 (by rfl) ⟨8992106, by rfl⟩ : syracuseStep 11989475 = 17984213) B17984213
theorem B1946099 : Blo 1295966 1946099 := bstep (se 1 (by rfl) ⟨1459574, by rfl⟩ : syracuseStep 1946099 = 2919149) B2919149
theorem B3281411 : Blo 1295966 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B1946129 : Blo 1295966 1946129 := bstep (se 2 (by rfl) ⟨729798, by rfl⟩ : syracuseStep 1946129 = 1459597) B1459597
theorem B1946147 : Blo 1295966 1946147 := bstep (se 1 (by rfl) ⟨1459610, by rfl⟩ : syracuseStep 1946147 = 2919221) B2919221
theorem B1946177 : Blo 1295966 1946177 := bstep (se 2 (by rfl) ⟨729816, by rfl⟩ : syracuseStep 1946177 = 1459633) B1459633
theorem B1847873 : Blo 1295966 1847873 := bstep (se 2 (by rfl) ⟨692952, by rfl⟩ : syracuseStep 1847873 = 1385905) B1385905
theorem B1946195 : Blo 1295966 1946195 := bstep (se 1 (by rfl) ⟨1459646, by rfl⟩ : syracuseStep 1946195 = 2919293) B2919293
theorem B1946225 : Blo 1295966 1946225 := bstep (se 2 (by rfl) ⟨729834, by rfl⟩ : syracuseStep 1946225 = 1459669) B1459669
theorem B1946243 : Blo 1295966 1946243 := bstep (se 1 (by rfl) ⟨1459682, by rfl⟩ : syracuseStep 1946243 = 2919365) B2919365
theorem B33264269 : Blo 1295966 33264269 := bstep (se 3 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 33264269 = 12474101) B12474101
theorem B1946273 : Blo 1295966 1946273 := bstep (se 2 (by rfl) ⟨729852, by rfl⟩ : syracuseStep 1946273 = 1459705) B1459705
theorem B3945133 : Blo 1295966 3945133 := bstep (se 3 (by rfl) ⟨739712, by rfl⟩ : syracuseStep 3945133 = 1479425) B1479425
theorem B5542577 : Blo 1295966 5542577 := bstep (se 2 (by rfl) ⟨2078466, by rfl⟩ : syracuseStep 5542577 = 4156933) B4156933
theorem B4158125 : Blo 1295966 4158125 := bstep (se 3 (by rfl) ⟨779648, by rfl⟩ : syracuseStep 4158125 = 1559297) B1559297
theorem B1946291 : Blo 1295966 1946291 := bstep (se 1 (by rfl) ⟨1459718, by rfl⟩ : syracuseStep 1946291 = 2919437) B2919437
theorem B17994421 : Blo 1295966 17994421 := bstep (se 5 (by rfl) ⟨843488, by rfl⟩ : syracuseStep 17994421 = 1686977) B1686977
theorem B4436689 : Blo 1295966 4436689 := bstep (se 2 (by rfl) ⟨1663758, by rfl⟩ : syracuseStep 4436689 = 3327517) B3327517
theorem B1946321 : Blo 1295966 1946321 := bstep (se 2 (by rfl) ⟨729870, by rfl⟩ : syracuseStep 1946321 = 1459741) B1459741
theorem B4379345 : Blo 1295966 4379345 := bstep (se 2 (by rfl) ⟨1642254, by rfl⟩ : syracuseStep 4379345 = 3284509) B3284509
theorem B1946339 : Blo 1295966 1946339 := bstep (se 1 (by rfl) ⟨1459754, by rfl⟩ : syracuseStep 1946339 = 2919509) B2919509
theorem B1872625 : Blo 1295966 1872625 := bstep (se 2 (by rfl) ⟨702234, by rfl⟩ : syracuseStep 1872625 = 1404469) B1404469
theorem B1946369 : Blo 1295966 1946369 := bstep (se 2 (by rfl) ⟨729888, by rfl⟩ : syracuseStep 1946369 = 1459777) B1459777
theorem B6566669 : Blo 1295966 6566669 := bstep (se 3 (by rfl) ⟨1231250, by rfl⟩ : syracuseStep 6566669 = 2462501) B2462501
theorem B1946387 : Blo 1295966 1946387 := bstep (se 1 (by rfl) ⟨1459790, by rfl⟩ : syracuseStep 1946387 = 2919581) B2919581
theorem B1946417 : Blo 1295966 1946417 := bstep (se 2 (by rfl) ⟨729906, by rfl⟩ : syracuseStep 1946417 = 1459813) B1459813
theorem B1946435 : Blo 1295966 1946435 := bstep (se 1 (by rfl) ⟨1459826, by rfl⟩ : syracuseStep 1946435 = 2919653) B2919653
theorem B1946465 : Blo 1295966 1946465 := bstep (se 2 (by rfl) ⟨729924, by rfl⟩ : syracuseStep 1946465 = 1459849) B1459849
theorem B1946483 : Blo 1295966 1946483 := bstep (se 1 (by rfl) ⟨1459862, by rfl⟩ : syracuseStep 1946483 = 2919725) B2919725
theorem B1946513 : Blo 1295966 1946513 := bstep (se 2 (by rfl) ⟨729942, by rfl⟩ : syracuseStep 1946513 = 1459885) B1459885
theorem B1946531 : Blo 1295966 1946531 := bstep (se 1 (by rfl) ⟨1459898, by rfl⟩ : syracuseStep 1946531 = 2919797) B2919797
theorem B2077633 : Blo 1295966 2077633 := bstep (se 2 (by rfl) ⟨779112, by rfl⟩ : syracuseStep 2077633 = 1558225) B1558225
theorem B1946561 : Blo 1295966 1946561 := bstep (se 2 (by rfl) ⟨729960, by rfl⟩ : syracuseStep 1946561 = 1459921) B1459921
theorem B1946579 : Blo 1295966 1946579 := bstep (se 1 (by rfl) ⟨1459934, by rfl⟩ : syracuseStep 1946579 = 2919869) B2919869
theorem B1946609 : Blo 1295966 1946609 := bstep (se 2 (by rfl) ⟨729978, by rfl⟩ : syracuseStep 1946609 = 1459957) B1459957
theorem B1946627 : Blo 1295966 1946627 := bstep (se 1 (by rfl) ⟨1459970, by rfl⟩ : syracuseStep 1946627 = 2919941) B2919941
theorem B2462737 : Blo 1295966 2462737 := bstep (se 2 (by rfl) ⟨923526, by rfl⟩ : syracuseStep 2462737 = 1847053) B1847053
theorem B1946657 : Blo 1295966 1946657 := bstep (se 2 (by rfl) ⟨729996, by rfl⟩ : syracuseStep 1946657 = 1459993) B1459993
theorem B3691565 : Blo 1295966 3691565 := bstep (se 3 (by rfl) ⟨692168, by rfl⟩ : syracuseStep 3691565 = 1384337) B1384337
theorem B1946675 : Blo 1295966 1946675 := bstep (se 1 (by rfl) ⟨1460006, by rfl⟩ : syracuseStep 1946675 = 2920013) B2920013
theorem B1946705 : Blo 1295966 1946705 := bstep (se 2 (by rfl) ⟨730014, by rfl⟩ : syracuseStep 1946705 = 1460029) B1460029
theorem B2806883 : Blo 1295966 2806883 := bstep (se 1 (by rfl) ⟨2105162, by rfl⟩ : syracuseStep 2806883 = 4210325) B4210325
theorem B1946723 : Blo 1295966 1946723 := bstep (se 1 (by rfl) ⟨1460042, by rfl⟩ : syracuseStep 1946723 = 2920085) B2920085
theorem B1946753 : Blo 1295966 1946753 := bstep (se 2 (by rfl) ⟨730032, by rfl⟩ : syracuseStep 1946753 = 1460065) B1460065
theorem B1946771 : Blo 1295966 1946771 := bstep (se 1 (by rfl) ⟨1460078, by rfl⟩ : syracuseStep 1946771 = 2920157) B2920157
theorem B1946801 : Blo 1295966 1946801 := bstep (se 2 (by rfl) ⟨730050, by rfl⟩ : syracuseStep 1946801 = 1460101) B1460101
theorem B1946819 : Blo 1295966 1946819 := bstep (se 1 (by rfl) ⟨1460114, by rfl⟩ : syracuseStep 1946819 = 2920229) B2920229
theorem B1946849 : Blo 1295966 1946849 := bstep (se 2 (by rfl) ⟨730068, by rfl⟩ : syracuseStep 1946849 = 1460137) B1460137
theorem B3691747 : Blo 1295966 3691747 := bstep (se 1 (by rfl) ⟨2768810, by rfl⟩ : syracuseStep 3691747 = 5537621) B5537621
theorem B4379885 : Blo 1295966 4379885 := bstep (se 3 (by rfl) ⟨821228, by rfl⟩ : syracuseStep 4379885 = 1642457) B1642457
theorem B8869105 : Blo 1295966 8869105 := bstep (se 2 (by rfl) ⟨3325914, by rfl⟩ : syracuseStep 8869105 = 6651829) B6651829
theorem B1946867 : Blo 1295966 1946867 := bstep (se 1 (by rfl) ⟨1460150, by rfl⟩ : syracuseStep 1946867 = 2920301) B2920301
theorem B3691793 : Blo 1295966 3691793 := bstep (se 2 (by rfl) ⟨1384422, by rfl⟩ : syracuseStep 3691793 = 2768845) B2768845
theorem B1946897 : Blo 1295966 1946897 := bstep (se 2 (by rfl) ⟨730086, by rfl⟩ : syracuseStep 1946897 = 1460173) B1460173
theorem B4379939 : Blo 1295966 4379939 := bstep (se 1 (by rfl) ⟨3284954, by rfl⟩ : syracuseStep 4379939 = 6569909) B6569909
theorem B1946915 : Blo 1295966 1946915 := bstep (se 1 (by rfl) ⟨1460186, by rfl⟩ : syracuseStep 1946915 = 2920373) B2920373
theorem B1946945 : Blo 1295966 1946945 := bstep (se 2 (by rfl) ⟨730104, by rfl⟩ : syracuseStep 1946945 = 1460209) B1460209
theorem B8303971 : Blo 1295966 8303971 := bstep (se 1 (by rfl) ⟨6227978, by rfl⟩ : syracuseStep 8303971 = 12455957) B12455957
theorem B4920689 : Blo 1295966 4920689 := bstep (se 2 (by rfl) ⟨1845258, by rfl⟩ : syracuseStep 4920689 = 3690517) B3690517
theorem B2463139 : Blo 1295966 2463139 := bstep (se 1 (by rfl) ⟨1847354, by rfl⟩ : syracuseStep 2463139 = 3694709) B3694709
theorem B3282353 : Blo 1295966 3282353 := bstep (se 2 (by rfl) ⟨1230882, by rfl⟩ : syracuseStep 3282353 = 2461765) B2461765
theorem B2463185 : Blo 1295966 2463185 := bstep (se 2 (by rfl) ⟨923694, by rfl⟩ : syracuseStep 2463185 = 1847389) B1847389
theorem B9344483 : Blo 1295966 9344483 := bstep (se 1 (by rfl) ⟨7008362, by rfl⟩ : syracuseStep 9344483 = 14016725) B14016725
theorem B3282403 : Blo 1295966 3282403 := bstep (se 1 (by rfl) ⟨2461802, by rfl⟩ : syracuseStep 3282403 = 4923605) B4923605
theorem B4380209 : Blo 1295966 4380209 := bstep (se 2 (by rfl) ⟨1642578, by rfl⟩ : syracuseStep 4380209 = 3285157) B3285157
theorem B3282545 : Blo 1295966 3282545 := bstep (se 2 (by rfl) ⟨1230954, by rfl⟩ : syracuseStep 3282545 = 2461909) B2461909
theorem B3946097 : Blo 1295966 3946097 := bstep (se 2 (by rfl) ⟨1479786, by rfl⟩ : syracuseStep 3946097 = 2959573) B2959573
theorem B3503779 : Blo 1295966 3503779 := bstep (se 1 (by rfl) ⟨2627834, by rfl⟩ : syracuseStep 3503779 = 5255669) B5255669
theorem B7386821 : Blo 1295966 7386821 := bstep (se 4 (by rfl) ⟨692514, by rfl⟩ : syracuseStep 7386821 = 1385029) B1385029
theorem B2463473 : Blo 1295966 2463473 := bstep (se 2 (by rfl) ⟨923802, by rfl⟩ : syracuseStep 2463473 = 1847605) B1847605
theorem B2078531 : Blo 1295966 2078531 := bstep (se 1 (by rfl) ⟨1558898, by rfl⟩ : syracuseStep 2078531 = 3117797) B3117797
theorem B1775441 : Blo 1295966 1775441 := bstep (se 2 (by rfl) ⟨665790, by rfl⟩ : syracuseStep 1775441 = 1331581) B1331581
theorem B4675427 : Blo 1295966 4675427 := bstep (se 1 (by rfl) ⟨3506570, by rfl⟩ : syracuseStep 4675427 = 7013141) B7013141
theorem B2078723 : Blo 1295966 2078723 := bstep (se 1 (by rfl) ⟨1559042, by rfl⟩ : syracuseStep 2078723 = 3118085) B3118085
theorem B4921357 : Blo 1295966 4921357 := bstep (se 3 (by rfl) ⟨922754, by rfl⟩ : syracuseStep 4921357 = 1845509) B1845509
theorem B3504493 : Blo 1295966 3504493 := bstep (se 3 (by rfl) ⟨657092, by rfl⟩ : syracuseStep 3504493 = 1314185) B1314185
theorem B7010801 : Blo 1295966 7010801 := bstep (se 2 (by rfl) ⟨2629050, by rfl⟩ : syracuseStep 7010801 = 5258101) B5258101
theorem B3283537 : Blo 1295966 3283537 := bstep (se 2 (by rfl) ⟨1231326, by rfl⟩ : syracuseStep 3283537 = 2462653) B2462653
theorem B13318769 : Blo 1295966 13318769 := bstep (se 2 (by rfl) ⟨4994538, by rfl⟩ : syracuseStep 13318769 = 9989077) B9989077
theorem B3693251 : Blo 1295966 3693251 := bstep (se 1 (by rfl) ⟨2769938, by rfl⟩ : syracuseStep 3693251 = 5539877) B5539877
theorem B2218769 : Blo 1295966 2218769 := bstep (se 2 (by rfl) ⟨832038, by rfl⟩ : syracuseStep 2218769 = 1664077) B1664077
theorem B4922147 : Blo 1295966 4922147 := bstep (se 1 (by rfl) ⟨3691610, by rfl⟩ : syracuseStep 4922147 = 7383221) B7383221
theorem B3283811 : Blo 1295966 3283811 := bstep (se 1 (by rfl) ⟨2462858, by rfl⟩ : syracuseStep 3283811 = 4925717) B4925717
theorem B3284003 : Blo 1295966 3284003 := bstep (se 1 (by rfl) ⟨2463002, by rfl⟩ : syracuseStep 3284003 = 4926005) B4926005
theorem B1973297 : Blo 1295966 1973297 := bstep (se 2 (by rfl) ⟨739986, by rfl⟩ : syracuseStep 1973297 = 1479973) B1479973
theorem B147881045 : Blo 1295966 147881045 := bstep (se 8 (by rfl) ⟨866490, by rfl⟩ : syracuseStep 147881045 = 1732981) B1732981
theorem B9845873 : Blo 1295966 9845873 := bstep (se 2 (by rfl) ⟨3692202, by rfl⟩ : syracuseStep 9845873 = 7384405) B7384405
theorem B3505315 : Blo 1295966 3505315 := bstep (se 1 (by rfl) ⟨2628986, by rfl⟩ : syracuseStep 3505315 = 5257973) B5257973
theorem B4152653 : Blo 1295966 4152653 := bstep (se 3 (by rfl) ⟨778622, by rfl⟩ : syracuseStep 4152653 = 1557245) B1557245
theorem B4373891 : Blo 1295966 4373891 := bstep (se 1 (by rfl) ⟨3280418, by rfl⟩ : syracuseStep 4373891 = 6560837) B6560837
theorem B4922801 : Blo 1295966 4922801 := bstep (se 2 (by rfl) ⟨1846050, by rfl⟩ : syracuseStep 4922801 = 3692101) B3692101
theorem B4677041 : Blo 1295966 4677041 := bstep (se 2 (by rfl) ⟨1753890, by rfl⟩ : syracuseStep 4677041 = 3507781) B3507781
theorem B6569585 : Blo 1295966 6569585 := bstep (se 2 (by rfl) ⟨2463594, by rfl⟩ : syracuseStep 6569585 = 4927189) B4927189
theorem B4374161 : Blo 1295966 4374161 := bstep (se 2 (by rfl) ⟨1640310, by rfl⟩ : syracuseStep 4374161 = 3280621) B3280621
theorem B2916017 : Blo 1295966 2916017 := bstep (se 2 (by rfl) ⟨1093506, by rfl⟩ : syracuseStep 2916017 = 2187013) B2187013
theorem B2916035 : Blo 1295966 2916035 := bstep (se 1 (by rfl) ⟨2187026, by rfl⟩ : syracuseStep 2916035 = 4374053) B4374053
theorem B6561485 : Blo 1295966 6561485 := bstep (se 3 (by rfl) ⟨1230278, by rfl⟩ : syracuseStep 6561485 = 2460557) B2460557
theorem B2186993 : Blo 1295966 2186993 := bstep (se 2 (by rfl) ⟨820122, by rfl⟩ : syracuseStep 2186993 = 1640245) B1640245
theorem B8314609 : Blo 1295966 8314609 := bstep (se 2 (by rfl) ⟨3117978, by rfl⟩ : syracuseStep 8314609 = 6235957) B6235957
theorem B2367299 : Blo 1295966 2367299 := bstep (se 1 (by rfl) ⟨1775474, by rfl⟩ : syracuseStep 2367299 = 3550949) B3550949
theorem B3997507 : Blo 1295966 3997507 := bstep (se 1 (by rfl) ⟨2998130, by rfl⟩ : syracuseStep 3997507 = 5996261) B5996261
theorem B3505997 : Blo 1295966 3505997 := bstep (se 3 (by rfl) ⟨657374, by rfl⟩ : syracuseStep 3505997 = 1314749) B1314749
theorem B2187121 : Blo 1295966 2187121 := bstep (se 2 (by rfl) ⟨820170, by rfl⟩ : syracuseStep 2187121 = 1640341) B1640341
theorem B15179633 : Blo 1295966 15179633 := bstep (se 2 (by rfl) ⟨5692362, by rfl⟩ : syracuseStep 15179633 = 11384725) B11384725
theorem B3694481 : Blo 1295966 3694481 := bstep (se 2 (by rfl) ⟨1385430, by rfl⟩ : syracuseStep 3694481 = 2770861) B2770861
theorem B1458067 : Blo 1295966 1458067 := bstep (se 1 (by rfl) ⟨1093550, by rfl⟩ : syracuseStep 1458067 = 2187101) B2187101
theorem B2187155 : Blo 1295966 2187155 := bstep (se 1 (by rfl) ⟨1640366, by rfl⟩ : syracuseStep 2187155 = 3280733) B3280733
theorem B3506093 : Blo 1295966 3506093 := bstep (se 3 (by rfl) ⟨657392, by rfl⟩ : syracuseStep 3506093 = 1314785) B1314785
theorem B15392693 : Blo 1295966 15392693 := bstep (se 5 (by rfl) ⟨721532, by rfl⟩ : syracuseStep 15392693 = 1443065) B1443065
theorem B2916305 : Blo 1295966 2916305 := bstep (se 2 (by rfl) ⟨1093614, by rfl⟩ : syracuseStep 2916305 = 2187229) B2187229
theorem B3284945 : Blo 1295966 3284945 := bstep (se 2 (by rfl) ⟨1231854, by rfl⟩ : syracuseStep 3284945 = 2463709) B2463709
theorem B2916323 : Blo 1295966 2916323 := bstep (se 1 (by rfl) ⟨2187242, by rfl⟩ : syracuseStep 2916323 = 4374485) B4374485
theorem B11837411 : Blo 1295966 11837411 := bstep (se 1 (by rfl) ⟨8878058, by rfl⟩ : syracuseStep 11837411 = 17756117) B17756117
theorem B2768897 : Blo 1295966 2768897 := bstep (se 2 (by rfl) ⟨1038336, by rfl⟩ : syracuseStep 2768897 = 2076673) B2076673
theorem B6561809 : Blo 1295966 6561809 := bstep (se 2 (by rfl) ⟨2460678, by rfl⟩ : syracuseStep 6561809 = 4921357) B4921357
theorem B2916377 : Blo 1295966 2916377 := bstep (se 2 (by rfl) ⟨1093641, by rfl⟩ : syracuseStep 2916377 = 2187283) B2187283
theorem B4374593 : Blo 1295966 4374593 := bstep (se 2 (by rfl) ⟨1640472, by rfl⟩ : syracuseStep 4374593 = 3280945) B3280945
theorem B1753177 : Blo 1295966 1753177 := bstep (se 2 (by rfl) ⟨657441, by rfl⟩ : syracuseStep 1753177 = 1314883) B1314883
theorem B1458283 : Blo 1295966 1458283 := bstep (se 1 (by rfl) ⟨1093712, by rfl⟩ : syracuseStep 1458283 = 2187425) B2187425
theorem B2916467 : Blo 1295966 2916467 := bstep (se 1 (by rfl) ⟨2187350, by rfl⟩ : syracuseStep 2916467 = 4374701) B4374701
theorem B8306819 : Blo 1295966 8306819 := bstep (se 1 (by rfl) ⟨6230114, by rfl⟩ : syracuseStep 8306819 = 12460229) B12460229
theorem B9855107 : Blo 1295966 9855107 := bstep (se 1 (by rfl) ⟨7391330, by rfl⟩ : syracuseStep 9855107 = 14782661) B14782661
theorem B2916503 : Blo 1295966 2916503 := bstep (se 1 (by rfl) ⟨2187377, by rfl⟩ : syracuseStep 2916503 = 4374755) B4374755
theorem B7200919 : Blo 1295966 7200919 := bstep (se 1 (by rfl) ⟨5400689, by rfl⟩ : syracuseStep 7200919 = 10801379) B10801379
theorem B1384619 : Blo 1295966 1384619 := bstep (se 1 (by rfl) ⟨1038464, by rfl⟩ : syracuseStep 1384619 = 2076929) B2076929
theorem B6561971 : Blo 1295966 6561971 := bstep (se 1 (by rfl) ⟨4921478, by rfl⟩ : syracuseStep 6561971 = 9842957) B9842957
theorem B2367667 : Blo 1295966 2367667 := bstep (se 1 (by rfl) ⟨1775750, by rfl⟩ : syracuseStep 2367667 = 3551501) B3551501
theorem B4153523 : Blo 1295966 4153523 := bstep (se 1 (by rfl) ⟨3115142, by rfl⟩ : syracuseStep 4153523 = 6230285) B6230285
theorem B2187479 : Blo 1295966 2187479 := bstep (se 1 (by rfl) ⟨1640609, by rfl⟩ : syracuseStep 2187479 = 3281219) B3281219
theorem B1458391 : Blo 1295966 1458391 := bstep (se 1 (by rfl) ⟨1093793, by rfl⟩ : syracuseStep 1458391 = 2187587) B2187587
theorem B2629847 : Blo 1295966 2629847 := bstep (se 1 (by rfl) ⟨1972385, by rfl⟩ : syracuseStep 2629847 = 3944771) B3944771
theorem B7110929 : Blo 1295966 7110929 := bstep (se 2 (by rfl) ⟨2666598, by rfl⟩ : syracuseStep 7110929 = 5333197) B5333197
theorem B4677905 : Blo 1295966 4677905 := bstep (se 2 (by rfl) ⟨1754214, by rfl⟩ : syracuseStep 4677905 = 3508429) B3508429
theorem B3285299 : Blo 1295966 3285299 := bstep (se 1 (by rfl) ⟨2463974, by rfl⟩ : syracuseStep 3285299 = 4927949) B4927949
theorem B2916683 : Blo 1295966 2916683 := bstep (se 1 (by rfl) ⟨2187512, by rfl⟩ : syracuseStep 2916683 = 4375025) B4375025
theorem B2187607 : Blo 1295966 2187607 := bstep (se 1 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 2187607 = 3281411) B3281411
theorem B17088869 : Blo 1295966 17088869 := bstep (se 4 (by rfl) ⟨1602081, by rfl⟩ : syracuseStep 17088869 = 3204163) B3204163
theorem B2916737 : Blo 1295966 2916737 := bstep (se 2 (by rfl) ⟨1093776, by rfl⟩ : syracuseStep 2916737 = 2187553) B2187553
theorem B1458571 : Blo 1295966 1458571 := bstep (se 1 (by rfl) ⟨1093928, by rfl⟩ : syracuseStep 1458571 = 2187857) B2187857
theorem B22176179 : Blo 1295966 22176179 := bstep (se 1 (by rfl) ⟨16632134, by rfl⟩ : syracuseStep 22176179 = 33264269) B33264269
theorem B3695051 : Blo 1295966 3695051 := bstep (se 1 (by rfl) ⟨2771288, by rfl⟩ : syracuseStep 3695051 = 5542577) B5542577
theorem B1458679 : Blo 1295966 1458679 := bstep (se 1 (by rfl) ⟨1094009, by rfl⟩ : syracuseStep 1458679 = 2188019) B2188019
theorem B9847331 : Blo 1295966 9847331 := bstep (se 1 (by rfl) ⟨7385498, by rfl⟩ : syracuseStep 9847331 = 14770997) B14770997
theorem B2916953 : Blo 1295966 2916953 := bstep (se 2 (by rfl) ⟨1093857, by rfl⟩ : syracuseStep 2916953 = 2187715) B2187715
theorem B4375133 : Blo 1295966 4375133 := bstep (se 3 (by rfl) ⟨820337, by rfl⟩ : syracuseStep 4375133 = 1640675) B1640675
theorem B1458859 : Blo 1295966 1458859 := bstep (se 1 (by rfl) ⟨1094144, by rfl⟩ : syracuseStep 1458859 = 2188289) B2188289
theorem B4989613 : Blo 1295966 4989613 := bstep (se 3 (by rfl) ⟨935552, by rfl⟩ : syracuseStep 4989613 = 1871105) B1871105
theorem B2917043 : Blo 1295966 2917043 := bstep (se 1 (by rfl) ⟨2187782, by rfl⟩ : syracuseStep 2917043 = 4375565) B4375565
theorem B2917079 : Blo 1295966 2917079 := bstep (se 1 (by rfl) ⟨2187809, by rfl⟩ : syracuseStep 2917079 = 4375619) B4375619
theorem B2769623 : Blo 1295966 2769623 := bstep (se 1 (by rfl) ⟨2077217, by rfl⟩ : syracuseStep 2769623 = 4154435) B4154435
theorem B5538563 : Blo 1295966 5538563 := bstep (se 1 (by rfl) ⟨4153922, by rfl⟩ : syracuseStep 5538563 = 8307845) B8307845
theorem B1458967 : Blo 1295966 1458967 := bstep (se 1 (by rfl) ⟨1094225, by rfl⟩ : syracuseStep 1458967 = 2188451) B2188451
theorem B18686821 : Blo 1295966 18686821 := bstep (se 4 (by rfl) ⟨1751889, by rfl⟩ : syracuseStep 18686821 = 3503779) B3503779
theorem B2917259 : Blo 1295966 2917259 := bstep (se 1 (by rfl) ⟨2187944, by rfl⟩ : syracuseStep 2917259 = 4375889) B4375889
theorem B5260177 : Blo 1295966 5260177 := bstep (se 2 (by rfl) ⟨1972566, by rfl⟩ : syracuseStep 5260177 = 3945133) B3945133
theorem B2917313 : Blo 1295966 2917313 := bstep (se 2 (by rfl) ⟨1093992, by rfl⟩ : syracuseStep 2917313 = 2187985) B2187985
theorem B5915585 : Blo 1295966 5915585 := bstep (se 2 (by rfl) ⟨2218344, by rfl⟩ : syracuseStep 5915585 = 4436689) B4436689
theorem B2188235 : Blo 1295966 2188235 := bstep (se 1 (by rfl) ⟨1641176, by rfl⟩ : syracuseStep 2188235 = 3282353) B3282353
theorem B1459147 : Blo 1295966 1459147 := bstep (se 1 (by rfl) ⟨1094360, by rfl⟩ : syracuseStep 1459147 = 2188721) B2188721
theorem B12813329 : Blo 1295966 12813329 := bstep (se 2 (by rfl) ⟨4804998, by rfl⟩ : syracuseStep 12813329 = 9609997) B9609997
theorem B1459255 : Blo 1295966 1459255 := bstep (se 1 (by rfl) ⟨1094441, by rfl⟩ : syracuseStep 1459255 = 2188883) B2188883
theorem B2188363 : Blo 1295966 2188363 := bstep (se 1 (by rfl) ⟨1641272, by rfl⟩ : syracuseStep 2188363 = 3282545) B3282545
theorem B2630731 : Blo 1295966 2630731 := bstep (se 1 (by rfl) ⟨1973048, by rfl⟩ : syracuseStep 2630731 = 3946097) B3946097
theorem B6653021 : Blo 1295966 6653021 := bstep (se 3 (by rfl) ⟨1247441, by rfl⟩ : syracuseStep 6653021 = 2494883) B2494883
theorem B4924547 : Blo 1295966 4924547 := bstep (se 1 (by rfl) ⟨3693410, by rfl⟩ : syracuseStep 4924547 = 7386821) B7386821
theorem B2917529 : Blo 1295966 2917529 := bstep (se 2 (by rfl) ⟨1094073, by rfl⟩ : syracuseStep 2917529 = 2188147) B2188147
theorem B3114163 : Blo 1295966 3114163 := bstep (se 1 (by rfl) ⟨2335622, by rfl⟩ : syracuseStep 3114163 = 4671245) B4671245
theorem B1385687 : Blo 1295966 1385687 := bstep (se 1 (by rfl) ⟨1039265, by rfl⟩ : syracuseStep 1385687 = 2078531) B2078531
theorem B2188505 : Blo 1295966 2188505 := bstep (se 2 (by rfl) ⟨820689, by rfl⟩ : syracuseStep 2188505 = 1641379) B1641379
theorem B1459435 : Blo 1295966 1459435 := bstep (se 1 (by rfl) ⟨1094576, by rfl⟩ : syracuseStep 1459435 = 2189153) B2189153
theorem B2917619 : Blo 1295966 2917619 := bstep (se 1 (by rfl) ⟨2188214, by rfl⟩ : syracuseStep 2917619 = 4376429) B4376429
theorem B47301893 : Blo 1295966 47301893 := bstep (se 4 (by rfl) ⟨4434552, by rfl⟩ : syracuseStep 47301893 = 8869105) B8869105
theorem B2917655 : Blo 1295966 2917655 := bstep (se 1 (by rfl) ⟨2188241, by rfl⟩ : syracuseStep 2917655 = 4376483) B4376483
theorem B5260567 : Blo 1295966 5260567 := bstep (se 1 (by rfl) ⟨3945425, by rfl⟩ : syracuseStep 5260567 = 7890851) B7890851
theorem B1459543 : Blo 1295966 1459543 := bstep (se 1 (by rfl) ⟨1094657, by rfl⟩ : syracuseStep 1459543 = 2189315) B2189315
theorem B2188633 : Blo 1295966 2188633 := bstep (se 2 (by rfl) ⟨820737, by rfl⟩ : syracuseStep 2188633 = 1641475) B1641475
theorem B3114443 : Blo 1295966 3114443 := bstep (se 1 (by rfl) ⟨2335832, by rfl⟩ : syracuseStep 3114443 = 4671665) B4671665
theorem B2917835 : Blo 1295966 2917835 := bstep (se 1 (by rfl) ⟨2188376, by rfl⟩ : syracuseStep 2917835 = 4376753) B4376753
theorem B2917889 : Blo 1295966 2917889 := bstep (se 2 (by rfl) ⟨1094208, by rfl⟩ : syracuseStep 2917889 = 2188417) B2188417
theorem B1459723 : Blo 1295966 1459723 := bstep (se 1 (by rfl) ⟨1094792, by rfl⟩ : syracuseStep 1459723 = 2189585) B2189585
theorem B2770519 : Blo 1295966 2770519 := bstep (se 1 (by rfl) ⟨2077889, by rfl⟩ : syracuseStep 2770519 = 4155779) B4155779
theorem B1295979 : Blo 1295966 1295979 := bstep (se 1 (by rfl) ⟨971984, by rfl⟩ : syracuseStep 1295979 = 1943969) B1943969
theorem B1295991 : Blo 1295966 1295991 := bstep (se 1 (by rfl) ⟨971993, by rfl⟩ : syracuseStep 1295991 = 1943987) B1943987
theorem B1459831 : Blo 1295966 1459831 := bstep (se 1 (by rfl) ⟨1094873, by rfl⟩ : syracuseStep 1459831 = 2189747) B2189747
theorem B1296011 : Blo 1295966 1296011 := bstep (se 1 (by rfl) ⟨972008, by rfl⟩ : syracuseStep 1296011 = 1944017) B1944017
theorem B1296023 : Blo 1295966 1296023 := bstep (se 1 (by rfl) ⟨972017, by rfl⟩ : syracuseStep 1296023 = 1944035) B1944035
theorem B1296043 : Blo 1295966 1296043 := bstep (se 1 (by rfl) ⟨972032, by rfl⟩ : syracuseStep 1296043 = 1944065) B1944065
theorem B1296055 : Blo 1295966 1296055 := bstep (se 1 (by rfl) ⟨972041, by rfl⟩ : syracuseStep 1296055 = 1944083) B1944083
theorem B1296075 : Blo 1295966 1296075 := bstep (se 1 (by rfl) ⟨972056, by rfl⟩ : syracuseStep 1296075 = 1944113) B1944113
theorem B4376267 : Blo 1295966 4376267 := bstep (se 1 (by rfl) ⟨3282200, by rfl⟩ : syracuseStep 4376267 = 6564401) B6564401
theorem B1296087 : Blo 1295966 1296087 := bstep (se 1 (by rfl) ⟨972065, by rfl⟩ : syracuseStep 1296087 = 1944131) B1944131
theorem B2918105 : Blo 1295966 2918105 := bstep (se 2 (by rfl) ⟨1094289, by rfl⟩ : syracuseStep 2918105 = 2188579) B2188579
theorem B1296107 : Blo 1295966 1296107 := bstep (se 1 (by rfl) ⟨972080, by rfl⟩ : syracuseStep 1296107 = 1944161) B1944161
theorem B1296119 : Blo 1295966 1296119 := bstep (se 1 (by rfl) ⟨972089, by rfl⟩ : syracuseStep 1296119 = 1944179) B1944179
theorem B1296139 : Blo 1295966 1296139 := bstep (se 1 (by rfl) ⟨972104, by rfl⟩ : syracuseStep 1296139 = 1944209) B1944209
theorem B1558283 : Blo 1295966 1558283 := bstep (se 1 (by rfl) ⟨1168712, by rfl⟩ : syracuseStep 1558283 = 2337425) B2337425
theorem B1296151 : Blo 1295966 1296151 := bstep (se 1 (by rfl) ⟨972113, by rfl⟩ : syracuseStep 1296151 = 1944227) B1944227
theorem B1296171 : Blo 1295966 1296171 := bstep (se 1 (by rfl) ⟨972128, by rfl⟩ : syracuseStep 1296171 = 1944257) B1944257
theorem B1460011 : Blo 1295966 1460011 := bstep (se 1 (by rfl) ⟨1095008, by rfl⟩ : syracuseStep 1460011 = 2190017) B2190017
theorem B2918195 : Blo 1295966 2918195 := bstep (se 1 (by rfl) ⟨2188646, by rfl⟩ : syracuseStep 2918195 = 4377293) B4377293
theorem B1296183 : Blo 1295966 1296183 := bstep (se 1 (by rfl) ⟨972137, by rfl⟩ : syracuseStep 1296183 = 1944275) B1944275
theorem B1296203 : Blo 1295966 1296203 := bstep (se 1 (by rfl) ⟨972152, by rfl⟩ : syracuseStep 1296203 = 1944305) B1944305
theorem B1296215 : Blo 1295966 1296215 := bstep (se 1 (by rfl) ⟨972161, by rfl⟩ : syracuseStep 1296215 = 1944323) B1944323
theorem B2918231 : Blo 1295966 2918231 := bstep (se 1 (by rfl) ⟨2188673, by rfl⟩ : syracuseStep 2918231 = 4377347) B4377347
theorem B39929699 : Blo 1295966 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B1296235 : Blo 1295966 1296235 := bstep (se 1 (by rfl) ⟨972176, by rfl⟩ : syracuseStep 1296235 = 1944353) B1944353
theorem B1296247 : Blo 1295966 1296247 := bstep (se 1 (by rfl) ⟨972185, by rfl⟩ : syracuseStep 1296247 = 1944371) B1944371
theorem B1296267 : Blo 1295966 1296267 := bstep (se 1 (by rfl) ⟨972200, by rfl⟩ : syracuseStep 1296267 = 1944401) B1944401
theorem B1296279 : Blo 1295966 1296279 := bstep (se 1 (by rfl) ⟨972209, by rfl⟩ : syracuseStep 1296279 = 1944419) B1944419
theorem B2189207 : Blo 1295966 2189207 := bstep (se 1 (by rfl) ⟨1641905, by rfl⟩ : syracuseStep 2189207 = 3283811) B3283811
theorem B1460119 : Blo 1295966 1460119 := bstep (se 1 (by rfl) ⟨1095089, by rfl⟩ : syracuseStep 1460119 = 2190179) B2190179
theorem B1296299 : Blo 1295966 1296299 := bstep (se 1 (by rfl) ⟨972224, by rfl⟩ : syracuseStep 1296299 = 1944449) B1944449
theorem B1296311 : Blo 1295966 1296311 := bstep (se 1 (by rfl) ⟨972233, by rfl⟩ : syracuseStep 1296311 = 1944467) B1944467
theorem B1296331 : Blo 1295966 1296331 := bstep (se 1 (by rfl) ⟨972248, by rfl⟩ : syracuseStep 1296331 = 1944497) B1944497
theorem B1640407 : Blo 1295966 1640407 := bstep (se 1 (by rfl) ⟨1230305, by rfl⟩ : syracuseStep 1640407 = 2460611) B2460611
theorem B1296343 : Blo 1295966 1296343 := bstep (se 1 (by rfl) ⟨972257, by rfl⟩ : syracuseStep 1296343 = 1944515) B1944515
theorem B4376537 : Blo 1295966 4376537 := bstep (se 2 (by rfl) ⟨1641201, by rfl⟩ : syracuseStep 4376537 = 3282403) B3282403
theorem B1296363 : Blo 1295966 1296363 := bstep (se 1 (by rfl) ⟨972272, by rfl⟩ : syracuseStep 1296363 = 1944545) B1944545
theorem B1296375 : Blo 1295966 1296375 := bstep (se 1 (by rfl) ⟨972281, by rfl⟩ : syracuseStep 1296375 = 1944563) B1944563
theorem B1296395 : Blo 1295966 1296395 := bstep (se 1 (by rfl) ⟨972296, by rfl⟩ : syracuseStep 1296395 = 1944593) B1944593
theorem B2918411 : Blo 1295966 2918411 := bstep (se 1 (by rfl) ⟨2188808, by rfl⟩ : syracuseStep 2918411 = 4377617) B4377617
theorem B1296407 : Blo 1295966 1296407 := bstep (se 1 (by rfl) ⟨972305, by rfl⟩ : syracuseStep 1296407 = 1944611) B1944611
theorem B2189335 : Blo 1295966 2189335 := bstep (se 1 (by rfl) ⟨1642001, by rfl⟩ : syracuseStep 2189335 = 3284003) B3284003
theorem B1296427 : Blo 1295966 1296427 := bstep (se 1 (by rfl) ⟨972320, by rfl⟩ : syracuseStep 1296427 = 1944641) B1944641
theorem B1296439 : Blo 1295966 1296439 := bstep (se 1 (by rfl) ⟨972329, by rfl⟩ : syracuseStep 1296439 = 1944659) B1944659
theorem B2918465 : Blo 1295966 2918465 := bstep (se 2 (by rfl) ⟨1094424, by rfl⟩ : syracuseStep 2918465 = 2188849) B2188849
theorem B1296459 : Blo 1295966 1296459 := bstep (se 1 (by rfl) ⟨972344, by rfl⟩ : syracuseStep 1296459 = 1944689) B1944689
theorem B6563915 : Blo 1295966 6563915 := bstep (se 1 (by rfl) ⟨4922936, by rfl⟩ : syracuseStep 6563915 = 9845873) B9845873
theorem B1296471 : Blo 1295966 1296471 := bstep (se 1 (by rfl) ⟨972353, by rfl⟩ : syracuseStep 1296471 = 1944707) B1944707
theorem B1296491 : Blo 1295966 1296491 := bstep (se 1 (by rfl) ⟨972368, by rfl⟩ : syracuseStep 1296491 = 1944737) B1944737
theorem B1296503 : Blo 1295966 1296503 := bstep (se 1 (by rfl) ⟨972377, by rfl⟩ : syracuseStep 1296503 = 1944755) B1944755
theorem B1296523 : Blo 1295966 1296523 := bstep (se 1 (by rfl) ⟨972392, by rfl⟩ : syracuseStep 1296523 = 1944785) B1944785
theorem B1296535 : Blo 1295966 1296535 := bstep (se 1 (by rfl) ⟨972401, by rfl⟩ : syracuseStep 1296535 = 1944803) B1944803
theorem B1296555 : Blo 1295966 1296555 := bstep (se 1 (by rfl) ⟨972416, by rfl⟩ : syracuseStep 1296555 = 1944833) B1944833
theorem B4737203 : Blo 1295966 4737203 := bstep (se 1 (by rfl) ⟨3552902, by rfl⟩ : syracuseStep 4737203 = 7105805) B7105805
theorem B1296567 : Blo 1295966 1296567 := bstep (se 1 (by rfl) ⟨972425, by rfl⟩ : syracuseStep 1296567 = 1944851) B1944851
theorem B1296587 : Blo 1295966 1296587 := bstep (se 1 (by rfl) ⟨972440, by rfl⟩ : syracuseStep 1296587 = 1944881) B1944881
theorem B1296599 : Blo 1295966 1296599 := bstep (se 1 (by rfl) ⟨972449, by rfl⟩ : syracuseStep 1296599 = 1944899) B1944899
theorem B1296619 : Blo 1295966 1296619 := bstep (se 1 (by rfl) ⟨972464, by rfl⟩ : syracuseStep 1296619 = 1944929) B1944929
theorem B1296631 : Blo 1295966 1296631 := bstep (se 1 (by rfl) ⟨972473, by rfl⟩ : syracuseStep 1296631 = 1944947) B1944947
theorem B1296651 : Blo 1295966 1296651 := bstep (se 1 (by rfl) ⟨972488, by rfl⟩ : syracuseStep 1296651 = 1944977) B1944977
theorem B1296663 : Blo 1295966 1296663 := bstep (se 1 (by rfl) ⟨972497, by rfl⟩ : syracuseStep 1296663 = 1944995) B1944995
theorem B2918681 : Blo 1295966 2918681 := bstep (se 2 (by rfl) ⟨1094505, by rfl⟩ : syracuseStep 2918681 = 2189011) B2189011
theorem B1296683 : Blo 1295966 1296683 := bstep (se 1 (by rfl) ⟨972512, by rfl⟩ : syracuseStep 1296683 = 1945025) B1945025
theorem B1296695 : Blo 1295966 1296695 := bstep (se 1 (by rfl) ⟨972521, by rfl⟩ : syracuseStep 1296695 = 1945043) B1945043
theorem B11086145 : Blo 1295966 11086145 := bstep (se 2 (by rfl) ⟨4157304, by rfl⟩ : syracuseStep 11086145 = 8314609) B8314609
theorem B1296715 : Blo 1295966 1296715 := bstep (se 1 (by rfl) ⟨972536, by rfl⟩ : syracuseStep 1296715 = 1945073) B1945073
theorem B1296727 : Blo 1295966 1296727 := bstep (se 1 (by rfl) ⟨972545, by rfl⟩ : syracuseStep 1296727 = 1945091) B1945091
theorem B1296747 : Blo 1295966 1296747 := bstep (se 1 (by rfl) ⟨972560, by rfl⟩ : syracuseStep 1296747 = 1945121) B1945121
theorem B2918771 : Blo 1295966 2918771 := bstep (se 1 (by rfl) ⟨2189078, by rfl⟩ : syracuseStep 2918771 = 4378157) B4378157
theorem B1296759 : Blo 1295966 1296759 := bstep (se 1 (by rfl) ⟨972569, by rfl⟩ : syracuseStep 1296759 = 1945139) B1945139
theorem B1296779 : Blo 1295966 1296779 := bstep (se 1 (by rfl) ⟨972584, by rfl⟩ : syracuseStep 1296779 = 1945169) B1945169
theorem B2771339 : Blo 1295966 2771339 := bstep (se 1 (by rfl) ⟨2078504, by rfl⟩ : syracuseStep 2771339 = 4157009) B4157009
theorem B1296791 : Blo 1295966 1296791 := bstep (se 1 (by rfl) ⟨972593, by rfl⟩ : syracuseStep 1296791 = 1945187) B1945187
theorem B2918807 : Blo 1295966 2918807 := bstep (se 1 (by rfl) ⟨2189105, by rfl⟩ : syracuseStep 2918807 = 4378211) B4378211
theorem B1296811 : Blo 1295966 1296811 := bstep (se 1 (by rfl) ⟨972608, by rfl⟩ : syracuseStep 1296811 = 1945217) B1945217
theorem B1296823 : Blo 1295966 1296823 := bstep (se 1 (by rfl) ⟨972617, by rfl⟩ : syracuseStep 1296823 = 1945235) B1945235
theorem B1944011 : Blo 1295966 1944011 := bstep (se 1 (by rfl) ⟨1458008, by rfl⟩ : syracuseStep 1944011 = 2916017) B2916017
theorem B1296843 : Blo 1295966 1296843 := bstep (se 1 (by rfl) ⟨972632, by rfl⟩ : syracuseStep 1296843 = 1945265) B1945265
theorem B1944023 : Blo 1295966 1944023 := bstep (se 1 (by rfl) ⟨1458017, by rfl⟩ : syracuseStep 1944023 = 2916035) B2916035
theorem B1296855 : Blo 1295966 1296855 := bstep (se 1 (by rfl) ⟨972641, by rfl⟩ : syracuseStep 1296855 = 1945283) B1945283
theorem B1296875 : Blo 1295966 1296875 := bstep (se 1 (by rfl) ⟨972656, by rfl⟩ : syracuseStep 1296875 = 1945313) B1945313
theorem B1296887 : Blo 1295966 1296887 := bstep (se 1 (by rfl) ⟨972665, by rfl⟩ : syracuseStep 1296887 = 1945331) B1945331
theorem B1296907 : Blo 1295966 1296907 := bstep (se 1 (by rfl) ⟨972680, by rfl⟩ : syracuseStep 1296907 = 1945361) B1945361
theorem B1296919 : Blo 1295966 1296919 := bstep (se 1 (by rfl) ⟨972689, by rfl⟩ : syracuseStep 1296919 = 1945379) B1945379
theorem B1944089 : Blo 1295966 1944089 := bstep (se 2 (by rfl) ⟨729033, by rfl⟩ : syracuseStep 1944089 = 1458067) B1458067
theorem B1296939 : Blo 1295966 1296939 := bstep (se 1 (by rfl) ⟨972704, by rfl⟩ : syracuseStep 1296939 = 1945409) B1945409
theorem B2337331 : Blo 1295966 2337331 := bstep (se 1 (by rfl) ⟨1752998, by rfl⟩ : syracuseStep 2337331 = 3505997) B3505997
theorem B1296951 : Blo 1295966 1296951 := bstep (se 1 (by rfl) ⟨972713, by rfl⟩ : syracuseStep 1296951 = 1945427) B1945427
theorem B1296971 : Blo 1295966 1296971 := bstep (se 1 (by rfl) ⟨972728, by rfl⟩ : syracuseStep 1296971 = 1945457) B1945457
theorem B10119755 : Blo 1295966 10119755 := bstep (se 1 (by rfl) ⟨7589816, by rfl⟩ : syracuseStep 10119755 = 15179633) B15179633
theorem B2918987 : Blo 1295966 2918987 := bstep (se 1 (by rfl) ⟨2189240, by rfl⟩ : syracuseStep 2918987 = 4378481) B4378481
theorem B7490123 : Blo 1295966 7490123 := bstep (se 1 (by rfl) ⟨5617592, by rfl⟩ : syracuseStep 7490123 = 11235185) B11235185
theorem B1296983 : Blo 1295966 1296983 := bstep (se 1 (by rfl) ⟨972737, by rfl⟩ : syracuseStep 1296983 = 1945475) B1945475
theorem B1297003 : Blo 1295966 1297003 := bstep (se 1 (by rfl) ⟨972752, by rfl⟩ : syracuseStep 1297003 = 1945505) B1945505
theorem B2337395 : Blo 1295966 2337395 := bstep (se 1 (by rfl) ⟨1753046, by rfl⟩ : syracuseStep 2337395 = 3506093) B3506093
theorem B1297015 : Blo 1295966 1297015 := bstep (se 1 (by rfl) ⟨972761, by rfl⟩ : syracuseStep 1297015 = 1945523) B1945523
theorem B2919041 : Blo 1295966 2919041 := bstep (se 2 (by rfl) ⟨1094640, by rfl⟩ : syracuseStep 2919041 = 2189281) B2189281
theorem B1944203 : Blo 1295966 1944203 := bstep (se 1 (by rfl) ⟨1458152, by rfl⟩ : syracuseStep 1944203 = 2916305) B2916305
theorem B1297035 : Blo 1295966 1297035 := bstep (se 1 (by rfl) ⟨972776, by rfl⟩ : syracuseStep 1297035 = 1945553) B1945553
theorem B2189963 : Blo 1295966 2189963 := bstep (se 1 (by rfl) ⟨1642472, by rfl⟩ : syracuseStep 2189963 = 3284945) B3284945
theorem B1944215 : Blo 1295966 1944215 := bstep (se 1 (by rfl) ⟨1458161, by rfl⟩ : syracuseStep 1944215 = 2916323) B2916323
theorem B4377239 : Blo 1295966 4377239 := bstep (se 1 (by rfl) ⟨3282929, by rfl⟩ : syracuseStep 4377239 = 6565859) B6565859
theorem B1297047 : Blo 1295966 1297047 := bstep (se 1 (by rfl) ⟨972785, by rfl⟩ : syracuseStep 1297047 = 1945571) B1945571
theorem B7891607 : Blo 1295966 7891607 := bstep (se 1 (by rfl) ⟨5918705, by rfl⟩ : syracuseStep 7891607 = 11837411) B11837411
theorem B1297067 : Blo 1295966 1297067 := bstep (se 1 (by rfl) ⟨972800, by rfl⟩ : syracuseStep 1297067 = 1945601) B1945601
theorem B1297079 : Blo 1295966 1297079 := bstep (se 1 (by rfl) ⟨972809, by rfl⟩ : syracuseStep 1297079 = 1945619) B1945619
theorem B1297099 : Blo 1295966 1297099 := bstep (se 1 (by rfl) ⟨972824, by rfl⟩ : syracuseStep 1297099 = 1945649) B1945649
theorem B1297111 : Blo 1295966 1297111 := bstep (se 1 (by rfl) ⟨972833, by rfl⟩ : syracuseStep 1297111 = 1945667) B1945667
theorem B1944281 : Blo 1295966 1944281 := bstep (se 2 (by rfl) ⟨729105, by rfl⟩ : syracuseStep 1944281 = 1458211) B1458211
theorem B1297131 : Blo 1295966 1297131 := bstep (se 1 (by rfl) ⟨972848, by rfl⟩ : syracuseStep 1297131 = 1945697) B1945697
theorem B1297143 : Blo 1295966 1297143 := bstep (se 1 (by rfl) ⟨972857, by rfl⟩ : syracuseStep 1297143 = 1945715) B1945715
theorem B1297163 : Blo 1295966 1297163 := bstep (se 1 (by rfl) ⟨972872, by rfl⟩ : syracuseStep 1297163 = 1945745) B1945745
theorem B2190091 : Blo 1295966 2190091 := bstep (se 1 (by rfl) ⟨1642568, by rfl⟩ : syracuseStep 2190091 = 3285137) B3285137
theorem B1297175 : Blo 1295966 1297175 := bstep (se 1 (by rfl) ⟨972881, by rfl⟩ : syracuseStep 1297175 = 1945763) B1945763
theorem B1297195 : Blo 1295966 1297195 := bstep (se 1 (by rfl) ⟨972896, by rfl⟩ : syracuseStep 1297195 = 1945793) B1945793
theorem B37407541 : Blo 1295966 37407541 := bstep (se 5 (by rfl) ⟨1753478, by rfl⟩ : syracuseStep 37407541 = 3506957) B3506957
theorem B1297207 : Blo 1295966 1297207 := bstep (se 1 (by rfl) ⟨972905, by rfl⟩ : syracuseStep 1297207 = 1945811) B1945811
theorem B1944395 : Blo 1295966 1944395 := bstep (se 1 (by rfl) ⟨1458296, by rfl⟩ : syracuseStep 1944395 = 2916593) B2916593
theorem B1297227 : Blo 1295966 1297227 := bstep (se 1 (by rfl) ⟨972920, by rfl⟩ : syracuseStep 1297227 = 1945841) B1945841
theorem B1944407 : Blo 1295966 1944407 := bstep (se 1 (by rfl) ⟨1458305, by rfl⟩ : syracuseStep 1944407 = 2916611) B2916611
theorem B1297239 : Blo 1295966 1297239 := bstep (se 1 (by rfl) ⟨972929, by rfl⟩ : syracuseStep 1297239 = 1945859) B1945859
theorem B2919257 : Blo 1295966 2919257 := bstep (se 2 (by rfl) ⟨1094721, by rfl⟩ : syracuseStep 2919257 = 2189443) B2189443
theorem B1297259 : Blo 1295966 1297259 := bstep (se 1 (by rfl) ⟨972944, by rfl⟩ : syracuseStep 1297259 = 1945889) B1945889
theorem B1297271 : Blo 1295966 1297271 := bstep (se 1 (by rfl) ⟨972953, by rfl⟩ : syracuseStep 1297271 = 1945907) B1945907
theorem B1297291 : Blo 1295966 1297291 := bstep (se 1 (by rfl) ⟨972968, by rfl⟩ : syracuseStep 1297291 = 1945937) B1945937
theorem B1297303 : Blo 1295966 1297303 := bstep (se 1 (by rfl) ⟨972977, by rfl⟩ : syracuseStep 1297303 = 1945955) B1945955
theorem B1944473 : Blo 1295966 1944473 := bstep (se 2 (by rfl) ⟨729177, by rfl⟩ : syracuseStep 1944473 = 1458355) B1458355
theorem B2190233 : Blo 1295966 2190233 := bstep (se 2 (by rfl) ⟨821337, by rfl⟩ : syracuseStep 2190233 = 1642675) B1642675
theorem B1297323 : Blo 1295966 1297323 := bstep (se 1 (by rfl) ⟨972992, by rfl⟩ : syracuseStep 1297323 = 1945985) B1945985
theorem B7203763 : Blo 1295966 7203763 := bstep (se 1 (by rfl) ⟨5402822, by rfl⟩ : syracuseStep 7203763 = 10805645) B10805645
theorem B2919347 : Blo 1295966 2919347 := bstep (se 1 (by rfl) ⟨2189510, by rfl⟩ : syracuseStep 2919347 = 4379021) B4379021
theorem B1297335 : Blo 1295966 1297335 := bstep (se 1 (by rfl) ⟨973001, by rfl⟩ : syracuseStep 1297335 = 1946003) B1946003
theorem B1297355 : Blo 1295966 1297355 := bstep (se 1 (by rfl) ⟨973016, by rfl⟩ : syracuseStep 1297355 = 1946033) B1946033
theorem B1297367 : Blo 1295966 1297367 := bstep (se 1 (by rfl) ⟨973025, by rfl⟩ : syracuseStep 1297367 = 1946051) B1946051
theorem B2919383 : Blo 1295966 2919383 := bstep (se 1 (by rfl) ⟨2189537, by rfl⟩ : syracuseStep 2919383 = 4379075) B4379075
theorem B1297387 : Blo 1295966 1297387 := bstep (se 1 (by rfl) ⟨973040, by rfl⟩ : syracuseStep 1297387 = 1946081) B1946081
theorem B1297399 : Blo 1295966 1297399 := bstep (se 1 (by rfl) ⟨973049, by rfl⟩ : syracuseStep 1297399 = 1946099) B1946099
theorem B1944587 : Blo 1295966 1944587 := bstep (se 1 (by rfl) ⟨1458440, by rfl⟩ : syracuseStep 1944587 = 2916881) B2916881
theorem B1297419 : Blo 1295966 1297419 := bstep (se 1 (by rfl) ⟨973064, by rfl⟩ : syracuseStep 1297419 = 1946129) B1946129
theorem B1944599 : Blo 1295966 1944599 := bstep (se 1 (by rfl) ⟨1458449, by rfl⟩ : syracuseStep 1944599 = 2916899) B2916899
theorem B2337815 : Blo 1295966 2337815 := bstep (se 1 (by rfl) ⟨1753361, by rfl⟩ : syracuseStep 2337815 = 3506723) B3506723
theorem B1297431 : Blo 1295966 1297431 := bstep (se 1 (by rfl) ⟨973073, by rfl⟩ : syracuseStep 1297431 = 1946147) B1946147
theorem B1297451 : Blo 1295966 1297451 := bstep (se 1 (by rfl) ⟨973088, by rfl⟩ : syracuseStep 1297451 = 1946177) B1946177
theorem B1297463 : Blo 1295966 1297463 := bstep (se 1 (by rfl) ⟨973097, by rfl⟩ : syracuseStep 1297463 = 1946195) B1946195
theorem B22154309 : Blo 1295966 22154309 := bstep (se 4 (by rfl) ⟨2076966, by rfl⟩ : syracuseStep 22154309 = 4153933) B4153933
theorem B1297483 : Blo 1295966 1297483 := bstep (se 1 (by rfl) ⟨973112, by rfl⟩ : syracuseStep 1297483 = 1946225) B1946225
theorem B1297495 : Blo 1295966 1297495 := bstep (se 1 (by rfl) ⟨973121, by rfl⟩ : syracuseStep 1297495 = 1946243) B1946243
theorem B1944665 : Blo 1295966 1944665 := bstep (se 2 (by rfl) ⟨729249, by rfl⟩ : syracuseStep 1944665 = 1458499) B1458499
theorem B9350245 : Blo 1295966 9350245 := bstep (se 4 (by rfl) ⟨876585, by rfl⟩ : syracuseStep 9350245 = 1753171) B1753171
theorem B1297515 : Blo 1295966 1297515 := bstep (se 1 (by rfl) ⟨973136, by rfl⟩ : syracuseStep 1297515 = 1946273) B1946273
theorem B2772083 : Blo 1295966 2772083 := bstep (se 1 (by rfl) ⟨2079062, by rfl⟩ : syracuseStep 2772083 = 4158125) B4158125
theorem B1297527 : Blo 1295966 1297527 := bstep (se 1 (by rfl) ⟨973145, by rfl⟩ : syracuseStep 1297527 = 1946291) B1946291
theorem B1297547 : Blo 1295966 1297547 := bstep (se 1 (by rfl) ⟨973160, by rfl⟩ : syracuseStep 1297547 = 1946321) B1946321
theorem B2919563 : Blo 1295966 2919563 := bstep (se 1 (by rfl) ⟨2189672, by rfl⟩ : syracuseStep 2919563 = 4379345) B4379345
theorem B4672657 : Blo 1295966 4672657 := bstep (se 2 (by rfl) ⟨1752246, by rfl⟩ : syracuseStep 4672657 = 3504493) B3504493
theorem B1297559 : Blo 1295966 1297559 := bstep (se 1 (by rfl) ⟨973169, by rfl⟩ : syracuseStep 1297559 = 1946339) B1946339
theorem B1297579 : Blo 1295966 1297579 := bstep (se 1 (by rfl) ⟨973184, by rfl⟩ : syracuseStep 1297579 = 1946369) B1946369
theorem B4377779 : Blo 1295966 4377779 := bstep (se 1 (by rfl) ⟨3283334, by rfl⟩ : syracuseStep 4377779 = 6566669) B6566669
theorem B1297591 : Blo 1295966 1297591 := bstep (se 1 (by rfl) ⟨973193, by rfl⟩ : syracuseStep 1297591 = 1946387) B1946387
theorem B2919617 : Blo 1295966 2919617 := bstep (se 2 (by rfl) ⟨1094856, by rfl⟩ : syracuseStep 2919617 = 2189713) B2189713
theorem B1944779 : Blo 1295966 1944779 := bstep (se 1 (by rfl) ⟨1458584, by rfl⟩ : syracuseStep 1944779 = 2917169) B2917169
theorem B1297611 : Blo 1295966 1297611 := bstep (se 1 (by rfl) ⟨973208, by rfl⟩ : syracuseStep 1297611 = 1946417) B1946417
theorem B1944791 : Blo 1295966 1944791 := bstep (se 1 (by rfl) ⟨1458593, by rfl⟩ : syracuseStep 1944791 = 2917187) B2917187
theorem B1297623 : Blo 1295966 1297623 := bstep (se 1 (by rfl) ⟨973217, by rfl⟩ : syracuseStep 1297623 = 1946435) B1946435
theorem B1846489 : Blo 1295966 1846489 := bstep (se 2 (by rfl) ⟨692433, by rfl⟩ : syracuseStep 1846489 = 1384867) B1384867
theorem B1297643 : Blo 1295966 1297643 := bstep (se 1 (by rfl) ⟨973232, by rfl⟩ : syracuseStep 1297643 = 1946465) B1946465
theorem B1297655 : Blo 1295966 1297655 := bstep (se 1 (by rfl) ⟨973241, by rfl⟩ : syracuseStep 1297655 = 1946483) B1946483
theorem B1297675 : Blo 1295966 1297675 := bstep (se 1 (by rfl) ⟨973256, by rfl⟩ : syracuseStep 1297675 = 1946513) B1946513
theorem B1297687 : Blo 1295966 1297687 := bstep (se 1 (by rfl) ⟨973265, by rfl⟩ : syracuseStep 1297687 = 1946531) B1946531
theorem B1944857 : Blo 1295966 1944857 := bstep (se 2 (by rfl) ⟨729321, by rfl⟩ : syracuseStep 1944857 = 1458643) B1458643
theorem B1297707 : Blo 1295966 1297707 := bstep (se 1 (by rfl) ⟨973280, by rfl⟩ : syracuseStep 1297707 = 1946561) B1946561
theorem B1297719 : Blo 1295966 1297719 := bstep (se 1 (by rfl) ⟨973289, by rfl⟩ : syracuseStep 1297719 = 1946579) B1946579
theorem B9841985 : Blo 1295966 9841985 := bstep (se 2 (by rfl) ⟨3690744, by rfl⟩ : syracuseStep 9841985 = 7381489) B7381489
theorem B1297739 : Blo 1295966 1297739 := bstep (se 1 (by rfl) ⟨973304, by rfl⟩ : syracuseStep 1297739 = 1946609) B1946609
theorem B1297751 : Blo 1295966 1297751 := bstep (se 1 (by rfl) ⟨973313, by rfl⟩ : syracuseStep 1297751 = 1946627) B1946627
theorem B1297771 : Blo 1295966 1297771 := bstep (se 1 (by rfl) ⟨973328, by rfl⟩ : syracuseStep 1297771 = 1946657) B1946657
theorem B2461043 : Blo 1295966 2461043 := bstep (se 1 (by rfl) ⟨1845782, by rfl⟩ : syracuseStep 2461043 = 3691565) B3691565
theorem B1297783 : Blo 1295966 1297783 := bstep (se 1 (by rfl) ⟨973337, by rfl⟩ : syracuseStep 1297783 = 1946675) B1946675
theorem B1944971 : Blo 1295966 1944971 := bstep (se 1 (by rfl) ⟨1458728, by rfl⟩ : syracuseStep 1944971 = 2917457) B2917457
theorem B1297803 : Blo 1295966 1297803 := bstep (se 1 (by rfl) ⟨973352, by rfl⟩ : syracuseStep 1297803 = 1946705) B1946705
theorem B1871255 : Blo 1295966 1871255 := bstep (se 1 (by rfl) ⟨1403441, by rfl⟩ : syracuseStep 1871255 = 2806883) B2806883
theorem B1944983 : Blo 1295966 1944983 := bstep (se 1 (by rfl) ⟨1458737, by rfl⟩ : syracuseStep 1944983 = 2917475) B2917475
theorem B2919833 : Blo 1295966 2919833 := bstep (se 2 (by rfl) ⟨1094937, by rfl⟩ : syracuseStep 2919833 = 2189875) B2189875
theorem B1297815 : Blo 1295966 1297815 := bstep (se 1 (by rfl) ⟨973361, by rfl⟩ : syracuseStep 1297815 = 1946723) B1946723
theorem B1297835 : Blo 1295966 1297835 := bstep (se 1 (by rfl) ⟨973376, by rfl⟩ : syracuseStep 1297835 = 1946753) B1946753
theorem B1297847 : Blo 1295966 1297847 := bstep (se 1 (by rfl) ⟨973385, by rfl⟩ : syracuseStep 1297847 = 1946771) B1946771
theorem B4378049 : Blo 1295966 4378049 := bstep (se 2 (by rfl) ⟨1641768, by rfl⟩ : syracuseStep 4378049 = 3283537) B3283537
theorem B1297867 : Blo 1295966 1297867 := bstep (se 1 (by rfl) ⟨973400, by rfl⟩ : syracuseStep 1297867 = 1946801) B1946801
theorem B1297879 : Blo 1295966 1297879 := bstep (se 1 (by rfl) ⟨973409, by rfl⟩ : syracuseStep 1297879 = 1946819) B1946819
theorem B2076121 : Blo 1295966 2076121 := bstep (se 2 (by rfl) ⟨778545, by rfl⟩ : syracuseStep 2076121 = 1557091) B1557091
theorem B1945049 : Blo 1295966 1945049 := bstep (se 2 (by rfl) ⟨729393, by rfl⟩ : syracuseStep 1945049 = 1458787) B1458787
theorem B1297899 : Blo 1295966 1297899 := bstep (se 1 (by rfl) ⟨973424, by rfl⟩ : syracuseStep 1297899 = 1946849) B1946849
theorem B2919923 : Blo 1295966 2919923 := bstep (se 1 (by rfl) ⟨2189942, by rfl⟩ : syracuseStep 2919923 = 4379885) B4379885
theorem B1297911 : Blo 1295966 1297911 := bstep (se 1 (by rfl) ⟨973433, by rfl⟩ : syracuseStep 1297911 = 1946867) B1946867
theorem B2461195 : Blo 1295966 2461195 := bstep (se 1 (by rfl) ⟨1845896, by rfl⟩ : syracuseStep 2461195 = 3691793) B3691793
theorem B1297931 : Blo 1295966 1297931 := bstep (se 1 (by rfl) ⟨973448, by rfl⟩ : syracuseStep 1297931 = 1946897) B1946897
theorem B2919959 : Blo 1295966 2919959 := bstep (se 1 (by rfl) ⟨2189969, by rfl⟩ : syracuseStep 2919959 = 4379939) B4379939
theorem B1297943 : Blo 1295966 1297943 := bstep (se 1 (by rfl) ⟨973457, by rfl⟩ : syracuseStep 1297943 = 1946915) B1946915
theorem B1297963 : Blo 1295966 1297963 := bstep (se 1 (by rfl) ⟨973472, by rfl⟩ : syracuseStep 1297963 = 1946945) B1946945
theorem B3280459 : Blo 1295966 3280459 := bstep (se 1 (by rfl) ⟨2460344, by rfl⟩ : syracuseStep 3280459 = 4920689) B4920689
theorem B1945163 : Blo 1295966 1945163 := bstep (se 1 (by rfl) ⟨1458872, by rfl⟩ : syracuseStep 1945163 = 2917745) B2917745
theorem B1945175 : Blo 1295966 1945175 := bstep (se 1 (by rfl) ⟨1458881, by rfl⟩ : syracuseStep 1945175 = 2917763) B2917763
theorem B2338391 : Blo 1295966 2338391 := bstep (se 1 (by rfl) ⟨1753793, by rfl⟩ : syracuseStep 2338391 = 3507587) B3507587
theorem B1642123 : Blo 1295966 1642123 := bstep (se 1 (by rfl) ⟨1231592, by rfl⟩ : syracuseStep 1642123 = 2463185) B2463185
theorem B6229655 : Blo 1295966 6229655 := bstep (se 1 (by rfl) ⟨4672241, by rfl⟩ : syracuseStep 6229655 = 9344483) B9344483
theorem B1945241 : Blo 1295966 1945241 := bstep (se 2 (by rfl) ⟨729465, by rfl⟩ : syracuseStep 1945241 = 1458931) B1458931
theorem B2920139 : Blo 1295966 2920139 := bstep (se 1 (by rfl) ⟨2190104, by rfl⟩ : syracuseStep 2920139 = 4380209) B4380209
theorem B3280601 : Blo 1295966 3280601 := bstep (se 2 (by rfl) ⟨1230225, by rfl⟩ : syracuseStep 3280601 = 2460451) B2460451
theorem B2920193 : Blo 1295966 2920193 := bstep (se 2 (by rfl) ⟨1095072, by rfl⟩ : syracuseStep 2920193 = 2190145) B2190145
theorem B1945355 : Blo 1295966 1945355 := bstep (se 1 (by rfl) ⟨1459016, by rfl⟩ : syracuseStep 1945355 = 2918033) B2918033
theorem B1945367 : Blo 1295966 1945367 := bstep (se 1 (by rfl) ⟨1459025, by rfl⟩ : syracuseStep 1945367 = 2918051) B2918051
theorem B6565697 : Blo 1295966 6565697 := bstep (se 2 (by rfl) ⟨2462136, by rfl⟩ : syracuseStep 6565697 = 4924273) B4924273
theorem B4329281 : Blo 1295966 4329281 := bstep (se 2 (by rfl) ⟨1623480, by rfl⟩ : syracuseStep 4329281 = 3246961) B3246961
theorem B2461529 : Blo 1295966 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B1945433 : Blo 1295966 1945433 := bstep (se 2 (by rfl) ⟨729537, by rfl⟩ : syracuseStep 1945433 = 1459075) B1459075
theorem B3944285 : Blo 1295966 3944285 := bstep (se 3 (by rfl) ⟨739553, by rfl⟩ : syracuseStep 3944285 = 1479107) B1479107
theorem B3116951 : Blo 1295966 3116951 := bstep (se 1 (by rfl) ⟨2337713, by rfl⟩ : syracuseStep 3116951 = 4675427) B4675427
theorem B1945547 : Blo 1295966 1945547 := bstep (se 1 (by rfl) ⟨1459160, by rfl⟩ : syracuseStep 1945547 = 2918321) B2918321
theorem B1945559 : Blo 1295966 1945559 := bstep (se 1 (by rfl) ⟨1459169, by rfl⟩ : syracuseStep 1945559 = 2918339) B2918339
theorem B2920409 : Blo 1295966 2920409 := bstep (se 2 (by rfl) ⟨1095153, by rfl⟩ : syracuseStep 2920409 = 2190307) B2190307
theorem B4378589 : Blo 1295966 4378589 := bstep (se 3 (by rfl) ⟨820985, by rfl⟩ : syracuseStep 4378589 = 1641971) B1641971
theorem B1945625 : Blo 1295966 1945625 := bstep (se 2 (by rfl) ⟨729609, by rfl⟩ : syracuseStep 1945625 = 1459219) B1459219
theorem B1945739 : Blo 1295966 1945739 := bstep (se 1 (by rfl) ⟨1459304, by rfl⟩ : syracuseStep 1945739 = 2918609) B2918609
theorem B1945751 : Blo 1295966 1945751 := bstep (se 1 (by rfl) ⟨1459313, by rfl⟩ : syracuseStep 1945751 = 2918627) B2918627
theorem B4927661 : Blo 1295966 4927661 := bstep (se 3 (by rfl) ⟨923936, by rfl⟩ : syracuseStep 4927661 = 1847873) B1847873
theorem B4673753 : Blo 1295966 4673753 := bstep (se 2 (by rfl) ⟨1752657, by rfl⟩ : syracuseStep 4673753 = 3505315) B3505315
theorem B1945817 : Blo 1295966 1945817 := bstep (se 2 (by rfl) ⟨729681, by rfl⟩ : syracuseStep 1945817 = 1459363) B1459363
theorem B4673867 : Blo 1295966 4673867 := bstep (se 1 (by rfl) ⟨3505400, by rfl⟩ : syracuseStep 4673867 = 7010801) B7010801
theorem B1945931 : Blo 1295966 1945931 := bstep (se 1 (by rfl) ⟨1459448, by rfl⟩ : syracuseStep 1945931 = 2918897) B2918897
theorem B1945943 : Blo 1295966 1945943 := bstep (se 1 (by rfl) ⟨1459457, by rfl⟩ : syracuseStep 1945943 = 2918915) B2918915
theorem B7893379 : Blo 1295966 7893379 := bstep (se 1 (by rfl) ⟨5920034, by rfl⟩ : syracuseStep 7893379 = 11840069) B11840069
theorem B1946009 : Blo 1295966 1946009 := bstep (se 2 (by rfl) ⟨729753, by rfl⟩ : syracuseStep 1946009 = 1459507) B1459507
theorem B5542337 : Blo 1295966 5542337 := bstep (se 2 (by rfl) ⟨2078376, by rfl⟩ : syracuseStep 5542337 = 4156753) B4156753
theorem B2462167 : Blo 1295966 2462167 := bstep (se 1 (by rfl) ⟨1846625, by rfl⟩ : syracuseStep 2462167 = 3693251) B3693251
theorem B11071961 : Blo 1295966 11071961 := bstep (se 2 (by rfl) ⟨4151985, by rfl⟩ : syracuseStep 11071961 = 8303971) B8303971
theorem B1479179 : Blo 1295966 1479179 := bstep (se 1 (by rfl) ⟨1109384, by rfl⟩ : syracuseStep 1479179 = 2218769) B2218769
theorem B1946123 : Blo 1295966 1946123 := bstep (se 1 (by rfl) ⟨1459592, by rfl⟩ : syracuseStep 1946123 = 2919185) B2919185
theorem B3281431 : Blo 1295966 3281431 := bstep (se 1 (by rfl) ⟨2461073, by rfl⟩ : syracuseStep 3281431 = 4922147) B4922147
theorem B1946135 : Blo 1295966 1946135 := bstep (se 1 (by rfl) ⟨1459601, by rfl⟩ : syracuseStep 1946135 = 2919203) B2919203
theorem B1946201 : Blo 1295966 1946201 := bstep (se 2 (by rfl) ⟨729825, by rfl⟩ : syracuseStep 1946201 = 1459651) B1459651
theorem B9351773 : Blo 1295966 9351773 := bstep (se 3 (by rfl) ⟨1753457, by rfl⟩ : syracuseStep 9351773 = 3506915) B3506915
theorem B1847947 : Blo 1295966 1847947 := bstep (se 1 (by rfl) ⟨1385960, by rfl⟩ : syracuseStep 1847947 = 2771921) B2771921
theorem B1946315 : Blo 1295966 1946315 := bstep (se 1 (by rfl) ⟨1459736, by rfl⟩ : syracuseStep 1946315 = 2919473) B2919473
theorem B1315531 : Blo 1295966 1315531 := bstep (se 1 (by rfl) ⟨986648, by rfl⟩ : syracuseStep 1315531 = 1973297) B1973297
theorem B1946327 : Blo 1295966 1946327 := bstep (se 1 (by rfl) ⟨1459745, by rfl⟩ : syracuseStep 1946327 = 2919491) B2919491
theorem B98587363 : Blo 1295966 98587363 := bstep (se 1 (by rfl) ⟨73940522, by rfl⟩ : syracuseStep 98587363 = 147881045) B147881045
theorem B1946393 : Blo 1295966 1946393 := bstep (se 2 (by rfl) ⟨729897, by rfl⟩ : syracuseStep 1946393 = 1459795) B1459795
theorem B1422155 : Blo 1295966 1422155 := bstep (se 1 (by rfl) ⟨1066616, by rfl⟩ : syracuseStep 1422155 = 2133233) B2133233
theorem B1946507 : Blo 1295966 1946507 := bstep (se 1 (by rfl) ⟨1459880, by rfl⟩ : syracuseStep 1946507 = 2919761) B2919761
theorem B1946519 : Blo 1295966 1946519 := bstep (se 1 (by rfl) ⟨1459889, by rfl⟩ : syracuseStep 1946519 = 2919779) B2919779
theorem B3281867 : Blo 1295966 3281867 := bstep (se 1 (by rfl) ⟨2461400, by rfl⟩ : syracuseStep 3281867 = 4922801) B4922801
theorem B3118027 : Blo 1295966 3118027 := bstep (se 1 (by rfl) ⟨2338520, by rfl⟩ : syracuseStep 3118027 = 4677041) B4677041
theorem B1946585 : Blo 1295966 1946585 := bstep (se 2 (by rfl) ⟨729969, by rfl⟩ : syracuseStep 1946585 = 1459939) B1459939
theorem B11080709 : Blo 1295966 11080709 := bstep (se 4 (by rfl) ⟨1038816, by rfl⟩ : syracuseStep 11080709 = 2077633) B2077633
theorem B10515491 : Blo 1295966 10515491 := bstep (se 1 (by rfl) ⟨7886618, by rfl⟩ : syracuseStep 10515491 = 15773237) B15773237
theorem B14775371 : Blo 1295966 14775371 := bstep (se 1 (by rfl) ⟨11081528, by rfl⟩ : syracuseStep 14775371 = 22163057) B22163057
theorem B4379723 : Blo 1295966 4379723 := bstep (se 1 (by rfl) ⟨3284792, by rfl⟩ : syracuseStep 4379723 = 6569585) B6569585
theorem B1946699 : Blo 1295966 1946699 := bstep (se 1 (by rfl) ⟨1460024, by rfl⟩ : syracuseStep 1946699 = 2920049) B2920049
theorem B1946711 : Blo 1295966 1946711 := bstep (se 1 (by rfl) ⟨1460033, by rfl⟩ : syracuseStep 1946711 = 2920067) B2920067
theorem B5330009 : Blo 1295966 5330009 := bstep (se 2 (by rfl) ⟨1998753, by rfl⟩ : syracuseStep 5330009 = 3997507) B3997507
theorem B41047181 : Blo 1295966 41047181 := bstep (se 3 (by rfl) ⟨7696346, by rfl⟩ : syracuseStep 41047181 = 15392693) B15392693
theorem B1946777 : Blo 1295966 1946777 := bstep (se 2 (by rfl) ⟨730041, by rfl⟩ : syracuseStep 1946777 = 1460083) B1460083
theorem B1578199 : Blo 1295966 1578199 := bstep (se 1 (by rfl) ⟨1183649, by rfl⟩ : syracuseStep 1578199 = 2367299) B2367299
theorem B9843929 : Blo 1295966 9843929 := bstep (se 2 (by rfl) ⟨3691473, by rfl⟩ : syracuseStep 9843929 = 7382947) B7382947
theorem B2462987 : Blo 1295966 2462987 := bstep (se 1 (by rfl) ⟨1847240, by rfl⟩ : syracuseStep 2462987 = 3694481) B3694481
theorem B1946891 : Blo 1295966 1946891 := bstep (se 1 (by rfl) ⟨1460168, by rfl⟩ : syracuseStep 1946891 = 2920337) B2920337
theorem B1946903 : Blo 1295966 1946903 := bstep (se 1 (by rfl) ⟨1460177, by rfl⟩ : syracuseStep 1946903 = 2920355) B2920355
theorem B19961153 : Blo 1295966 19961153 := bstep (se 2 (by rfl) ⟨7485432, by rfl⟩ : syracuseStep 19961153 = 14970865) B14970865
theorem B3282241 : Blo 1295966 3282241 := bstep (se 2 (by rfl) ⟨1230840, by rfl⟩ : syracuseStep 3282241 = 2461681) B2461681
theorem B2463041 : Blo 1295966 2463041 := bstep (se 2 (by rfl) ⟨923640, by rfl⟩ : syracuseStep 2463041 = 1847281) B1847281
theorem B4379993 : Blo 1295966 4379993 := bstep (se 2 (by rfl) ⟨1642497, by rfl⟩ : syracuseStep 4379993 = 3284995) B3284995
theorem B5543261 : Blo 1295966 5543261 := bstep (se 3 (by rfl) ⟨1039361, by rfl⟩ : syracuseStep 5543261 = 2078723) B2078723
theorem B4675009 : Blo 1295966 4675009 := bstep (se 2 (by rfl) ⟨1753128, by rfl⟩ : syracuseStep 4675009 = 3506257) B3506257
theorem B3741149 : Blo 1295966 3741149 := bstep (se 3 (by rfl) ⟨701465, by rfl⟩ : syracuseStep 3741149 = 1402931) B1402931
theorem B5912153 : Blo 1295966 5912153 := bstep (se 2 (by rfl) ⟨2217057, by rfl⟩ : syracuseStep 5912153 = 4434115) B4434115
theorem B7992983 : Blo 1295966 7992983 := bstep (se 1 (by rfl) ⟨5994737, by rfl⟩ : syracuseStep 7992983 = 11989475) B11989475
theorem B11081393 : Blo 1295966 11081393 := bstep (se 2 (by rfl) ⟨4155522, by rfl⟩ : syracuseStep 11081393 = 8311045) B8311045
theorem B3692249 : Blo 1295966 3692249 := bstep (se 2 (by rfl) ⟨1384593, by rfl⟩ : syracuseStep 3692249 = 2769187) B2769187
theorem B6567641 : Blo 1295966 6567641 := bstep (se 2 (by rfl) ⟨2462865, by rfl⟩ : syracuseStep 6567641 = 4925731) B4925731
theorem B9852677 : Blo 1295966 9852677 := bstep (se 4 (by rfl) ⟨923688, by rfl⟩ : syracuseStep 9852677 = 1847377) B1847377
theorem B14030597 : Blo 1295966 14030597 := bstep (se 4 (by rfl) ⟨1315368, by rfl⟩ : syracuseStep 14030597 = 2630737) B2630737
theorem B3282839 : Blo 1295966 3282839 := bstep (se 1 (by rfl) ⟨2462129, by rfl⟩ : syracuseStep 3282839 = 4924259) B4924259
theorem B3692567 : Blo 1295966 3692567 := bstep (se 1 (by rfl) ⟨2769425, by rfl⟩ : syracuseStep 3692567 = 5538851) B5538851
theorem B2463959 : Blo 1295966 2463959 := bstep (se 1 (by rfl) ⟨1847969, by rfl⟩ : syracuseStep 2463959 = 3695939) B3695939
theorem B5535965 : Blo 1295966 5535965 := bstep (se 3 (by rfl) ⟨1037993, by rfl⟩ : syracuseStep 5535965 = 2075987) B2075987
theorem B23992561 : Blo 1295966 23992561 := bstep (se 2 (by rfl) ⟨8997210, by rfl⟩ : syracuseStep 23992561 = 17994421) B17994421
theorem B2496833 : Blo 1295966 2496833 := bstep (se 2 (by rfl) ⟨936312, by rfl⟩ : syracuseStep 2496833 = 1872625) B1872625
theorem B11082419 : Blo 1295966 11082419 := bstep (se 1 (by rfl) ⟨8311814, by rfl⟩ : syracuseStep 11082419 = 16623629) B16623629
theorem B3283649 : Blo 1295966 3283649 := bstep (se 2 (by rfl) ⟨1231368, by rfl⟩ : syracuseStep 3283649 = 2462737) B2462737
theorem B3693377 : Blo 1295966 3693377 := bstep (se 2 (by rfl) ⟨1385016, by rfl⟩ : syracuseStep 3693377 = 2770033) B2770033
theorem B4209497 : Blo 1295966 4209497 := bstep (se 2 (by rfl) ⟨1578561, by rfl⟩ : syracuseStep 4209497 = 3157123) B3157123
theorem B4922315 : Blo 1295966 4922315 := bstep (se 1 (by rfl) ⟨3691736, by rfl⟩ : syracuseStep 4922315 = 7383473) B7383473
theorem B4922329 : Blo 1295966 4922329 := bstep (se 2 (by rfl) ⟨1845873, by rfl⟩ : syracuseStep 4922329 = 3691747) B3691747
theorem B8879179 : Blo 1295966 8879179 := bstep (se 1 (by rfl) ⟨6659384, by rfl⟩ : syracuseStep 8879179 = 13318769) B13318769
theorem B3284185 : Blo 1295966 3284185 := bstep (se 2 (by rfl) ⟨1231569, by rfl⟩ : syracuseStep 3284185 = 2463139) B2463139
theorem B6569261 : Blo 1295966 6569261 := bstep (se 3 (by rfl) ⟨1231736, by rfl⟩ : syracuseStep 6569261 = 2463473) B2463473
theorem B8879453 : Blo 1295966 8879453 := bstep (se 3 (by rfl) ⟨1664897, by rfl⟩ : syracuseStep 8879453 = 3329795) B3329795
theorem B4734509 : Blo 1295966 4734509 := bstep (se 3 (by rfl) ⟨887720, by rfl⟩ : syracuseStep 4734509 = 1775441) B1775441
theorem B2768435 : Blo 1295966 2768435 := bstep (se 1 (by rfl) ⟨2076326, by rfl⟩ : syracuseStep 2768435 = 4152653) B4152653
theorem B2915927 : Blo 1295966 2915927 := bstep (se 1 (by rfl) ⟨2186945, by rfl⟩ : syracuseStep 2915927 = 4373891) B4373891
theorem B2768537 : Blo 1295966 2768537 := bstep (se 2 (by rfl) ⟨1038201, by rfl⟩ : syracuseStep 2768537 = 2076403) B2076403
theorem B2916107 : Blo 1295966 2916107 := bstep (se 1 (by rfl) ⟨2187080, by rfl⟩ : syracuseStep 2916107 = 4374161) B4374161
theorem B4374323 : Blo 1295966 4374323 := bstep (se 1 (by rfl) ⟨3280742, by rfl⟩ : syracuseStep 4374323 = 6561485) B6561485
theorem B2916161 : Blo 1295966 2916161 := bstep (se 2 (by rfl) ⟨1093560, by rfl⟩ : syracuseStep 2916161 = 2187121) B2187121
theorem B1457995 : Blo 1295966 1457995 := bstep (se 1 (by rfl) ⟨1093496, by rfl⟩ : syracuseStep 1457995 = 2186993) B2186993
theorem B4923287 : Blo 1295966 4923287 := bstep (se 1 (by rfl) ⟨3692465, by rfl⟩ : syracuseStep 4923287 = 7384931) B7384931
theorem B1458103 : Blo 1295966 1458103 := bstep (se 1 (by rfl) ⟨1093577, by rfl⟩ : syracuseStep 1458103 = 2187155) B2187155
theorem B4374539 : Blo 1295966 4374539 := bstep (se 1 (by rfl) ⟨3280904, by rfl⟩ : syracuseStep 4374539 = 6561809) B6561809
theorem B2916395 : Blo 1295966 2916395 := bstep (se 1 (by rfl) ⟨2187296, by rfl⟩ : syracuseStep 2916395 = 4374593) B4374593
theorem B34168877 : Blo 1295966 34168877 := bstep (se 3 (by rfl) ⟨6406664, by rfl⟩ : syracuseStep 34168877 = 12813329) B12813329
theorem B9846845 : Blo 1295966 9846845 := bstep (se 3 (by rfl) ⟨1846283, by rfl⟩ : syracuseStep 9846845 = 3692567) B3692567
theorem B5537879 : Blo 1295966 5537879 := bstep (se 1 (by rfl) ⟨4153409, by rfl⟩ : syracuseStep 5537879 = 8306819) B8306819
theorem B6570071 : Blo 1295966 6570071 := bstep (se 1 (by rfl) ⟨4927553, by rfl⟩ : syracuseStep 6570071 = 9855107) B9855107
theorem B3285107 : Blo 1295966 3285107 := bstep (se 1 (by rfl) ⟨2463830, by rfl⟩ : syracuseStep 3285107 = 4927661) B4927661
theorem B4374647 : Blo 1295966 4374647 := bstep (se 1 (by rfl) ⟨3280985, by rfl⟩ : syracuseStep 4374647 = 6561971) B6561971
theorem B1458319 : Blo 1295966 1458319 := bstep (se 1 (by rfl) ⟨1093739, by rfl⟩ : syracuseStep 1458319 = 2187479) B2187479
theorem B14213357 : Blo 1295966 14213357 := bstep (se 3 (by rfl) ⟨2665004, by rfl⟩ : syracuseStep 14213357 = 5330009) B5330009
theorem B3694891 : Blo 1295966 3694891 := bstep (se 1 (by rfl) ⟨2771168, by rfl⟩ : syracuseStep 3694891 = 5542337) B5542337
theorem B7381307 : Blo 1295966 7381307 := bstep (se 1 (by rfl) ⟨5535980, by rfl⟩ : syracuseStep 7381307 = 11071961) B11071961
theorem B31990081 : Blo 1295966 31990081 := bstep (se 2 (by rfl) ⟨11996280, by rfl⟩ : syracuseStep 31990081 = 23992561) B23992561
theorem B2916755 : Blo 1295966 2916755 := bstep (se 1 (by rfl) ⟨2187566, by rfl⟩ : syracuseStep 2916755 = 4375133) B4375133
theorem B6234515 : Blo 1295966 6234515 := bstep (se 1 (by rfl) ⟨4675886, by rfl⟩ : syracuseStep 6234515 = 9351773) B9351773
theorem B2916809 : Blo 1295966 2916809 := bstep (se 2 (by rfl) ⟨1093803, by rfl⟩ : syracuseStep 2916809 = 2187607) B2187607
theorem B11076061 : Blo 1295966 11076061 := bstep (se 3 (by rfl) ⟨2076761, by rfl⟩ : syracuseStep 11076061 = 4153523) B4153523
theorem B7012925 : Blo 1295966 7012925 := bstep (se 3 (by rfl) ⟨1314923, by rfl⟩ : syracuseStep 7012925 = 2629847) B2629847
theorem B3695165 : Blo 1295966 3695165 := bstep (se 3 (by rfl) ⟨692843, by rfl⟩ : syracuseStep 3695165 = 1385687) B1385687
theorem B6570557 : Blo 1295966 6570557 := bstep (se 3 (by rfl) ⟨1231979, by rfl⟩ : syracuseStep 6570557 = 2463959) B2463959
theorem B2187911 : Blo 1295966 2187911 := bstep (se 1 (by rfl) ⟨1640933, by rfl⟩ : syracuseStep 2187911 = 3281867) B3281867
theorem B1458823 : Blo 1295966 1458823 := bstep (se 1 (by rfl) ⟨1094117, by rfl⟩ : syracuseStep 1458823 = 2188235) B2188235
theorem B4375241 : Blo 1295966 4375241 := bstep (se 2 (by rfl) ⟨1640715, by rfl⟩ : syracuseStep 4375241 = 3281431) B3281431
theorem B38404901 : Blo 1295966 38404901 := bstep (se 4 (by rfl) ⟨3600459, by rfl⟩ : syracuseStep 38404901 = 7200919) B7200919
theorem B6562619 : Blo 1295966 6562619 := bstep (se 1 (by rfl) ⟨4921964, by rfl⟩ : syracuseStep 6562619 = 9843929) B9843929
theorem B1459003 : Blo 1295966 1459003 := bstep (se 1 (by rfl) ⟨1094252, by rfl⟩ : syracuseStep 1459003 = 2188505) B2188505
theorem B6652817 : Blo 1295966 6652817 := bstep (se 2 (by rfl) ⟨2494806, by rfl⟩ : syracuseStep 6652817 = 4989613) B4989613
theorem B3695507 : Blo 1295966 3695507 := bstep (se 1 (by rfl) ⟨2771630, by rfl⟩ : syracuseStep 3695507 = 5543261) B5543261
theorem B131449817 : Blo 1295966 131449817 := bstep (se 2 (by rfl) ⟨49293681, by rfl⟩ : syracuseStep 131449817 = 98587363) B98587363
theorem B6562781 : Blo 1295966 6562781 := bstep (se 3 (by rfl) ⟨1230521, by rfl⟩ : syracuseStep 6562781 = 2461043) B2461043
theorem B7390237 : Blo 1295966 7390237 := bstep (se 3 (by rfl) ⟨1385669, by rfl⟩ : syracuseStep 7390237 = 2771339) B2771339
theorem B3941435 : Blo 1295966 3941435 := bstep (se 1 (by rfl) ⟨2956076, by rfl⟩ : syracuseStep 3941435 = 5912153) B5912153
theorem B4990013 : Blo 1295966 4990013 := bstep (se 3 (by rfl) ⟨935627, by rfl⟩ : syracuseStep 4990013 = 1871255) B1871255
theorem B2917511 : Blo 1295966 2917511 := bstep (se 1 (by rfl) ⟨2188133, by rfl⟩ : syracuseStep 2917511 = 4376267) B4376267
theorem B7013569 : Blo 1295966 7013569 := bstep (se 2 (by rfl) ⟨2630088, by rfl⟩ : syracuseStep 7013569 = 5260177) B5260177
theorem B2188559 : Blo 1295966 2188559 := bstep (se 1 (by rfl) ⟨1641419, by rfl⟩ : syracuseStep 2188559 = 3282839) B3282839
theorem B1459471 : Blo 1295966 1459471 := bstep (se 1 (by rfl) ⟨1094603, by rfl⟩ : syracuseStep 1459471 = 2189207) B2189207
theorem B6563105 : Blo 1295966 6563105 := bstep (se 2 (by rfl) ⟨2461164, by rfl⟩ : syracuseStep 6563105 = 4922329) B4922329
theorem B2917691 : Blo 1295966 2917691 := bstep (se 1 (by rfl) ⟨2188268, by rfl⟩ : syracuseStep 2917691 = 4376537) B4376537
theorem B4375943 : Blo 1295966 4375943 := bstep (se 1 (by rfl) ⟨3281957, by rfl⟩ : syracuseStep 4375943 = 6563915) B6563915
theorem B2917817 : Blo 1295966 2917817 := bstep (se 2 (by rfl) ⟨1094181, by rfl⟩ : syracuseStep 2917817 = 2188363) B2188363
theorem B3507641 : Blo 1295966 3507641 := bstep (se 2 (by rfl) ⟨1315365, by rfl⟩ : syracuseStep 3507641 = 2630731) B2630731
theorem B11838905 : Blo 1295966 11838905 := bstep (se 2 (by rfl) ⟨4439589, by rfl⟩ : syracuseStep 11838905 = 8879179) B8879179
theorem B12625357 : Blo 1295966 12625357 := bstep (se 3 (by rfl) ⟨2367254, by rfl⟩ : syracuseStep 12625357 = 4734509) B4734509
theorem B1664555 : Blo 1295966 1664555 := bstep (se 1 (by rfl) ⟨1248416, by rfl⟩ : syracuseStep 1664555 = 2496833) B2496833
theorem B7390763 : Blo 1295966 7390763 := bstep (se 1 (by rfl) ⟨5543072, by rfl⟩ : syracuseStep 7390763 = 11086145) B11086145
theorem B1296007 : Blo 1295966 1296007 := bstep (se 1 (by rfl) ⟨972005, by rfl⟩ : syracuseStep 1296007 = 1944011) B1944011
theorem B1296015 : Blo 1295966 1296015 := bstep (se 1 (by rfl) ⟨972011, by rfl⟩ : syracuseStep 1296015 = 1944023) B1944023
theorem B1296059 : Blo 1295966 1296059 := bstep (se 1 (by rfl) ⟨972044, by rfl⟩ : syracuseStep 1296059 = 1944089) B1944089
theorem B7014089 : Blo 1295966 7014089 := bstep (se 2 (by rfl) ⟨2630283, by rfl⟩ : syracuseStep 7014089 = 5260567) B5260567
theorem B7382765 : Blo 1295966 7382765 := bstep (se 3 (by rfl) ⟨1384268, by rfl⟩ : syracuseStep 7382765 = 2768537) B2768537
theorem B4376321 : Blo 1295966 4376321 := bstep (se 2 (by rfl) ⟨1641120, by rfl⟩ : syracuseStep 4376321 = 3282241) B3282241
theorem B1296135 : Blo 1295966 1296135 := bstep (se 1 (by rfl) ⟨972101, by rfl⟩ : syracuseStep 1296135 = 1944203) B1944203
theorem B1459975 : Blo 1295966 1459975 := bstep (se 1 (by rfl) ⟨1094981, by rfl⟩ : syracuseStep 1459975 = 2189963) B2189963
theorem B1296143 : Blo 1295966 1296143 := bstep (se 1 (by rfl) ⟨972107, by rfl⟩ : syracuseStep 1296143 = 1944215) B1944215
theorem B2918159 : Blo 1295966 2918159 := bstep (se 1 (by rfl) ⟨2188619, by rfl⟩ : syracuseStep 2918159 = 4377239) B4377239
theorem B2918177 : Blo 1295966 2918177 := bstep (se 2 (by rfl) ⟨1094316, by rfl⟩ : syracuseStep 2918177 = 2188633) B2188633
theorem B2189099 : Blo 1295966 2189099 := bstep (se 1 (by rfl) ⟨1641824, by rfl⟩ : syracuseStep 2189099 = 3283649) B3283649
theorem B1296187 : Blo 1295966 1296187 := bstep (se 1 (by rfl) ⟨972140, by rfl⟩ : syracuseStep 1296187 = 1944281) B1944281
theorem B1296263 : Blo 1295966 1296263 := bstep (se 1 (by rfl) ⟨972197, by rfl⟩ : syracuseStep 1296263 = 1944395) B1944395
theorem B1296271 : Blo 1295966 1296271 := bstep (se 1 (by rfl) ⟨972203, by rfl⟩ : syracuseStep 1296271 = 1944407) B1944407
theorem B1296315 : Blo 1295966 1296315 := bstep (se 1 (by rfl) ⟨972236, by rfl⟩ : syracuseStep 1296315 = 1944473) B1944473
theorem B1460155 : Blo 1295966 1460155 := bstep (se 1 (by rfl) ⟨1095116, by rfl⟩ : syracuseStep 1460155 = 2190233) B2190233
theorem B1296391 : Blo 1295966 1296391 := bstep (se 1 (by rfl) ⟨972293, by rfl⟩ : syracuseStep 1296391 = 1944587) B1944587
theorem B1296399 : Blo 1295966 1296399 := bstep (se 1 (by rfl) ⟨972299, by rfl⟩ : syracuseStep 1296399 = 1944599) B1944599
theorem B1558543 : Blo 1295966 1558543 := bstep (se 1 (by rfl) ⟨1168907, by rfl⟩ : syracuseStep 1558543 = 2337815) B2337815
theorem B4155421 : Blo 1295966 4155421 := bstep (se 3 (by rfl) ⟨779141, by rfl⟩ : syracuseStep 4155421 = 1558283) B1558283
theorem B1296443 : Blo 1295966 1296443 := bstep (se 1 (by rfl) ⟨972332, by rfl⟩ : syracuseStep 1296443 = 1944665) B1944665
theorem B2918519 : Blo 1295966 2918519 := bstep (se 1 (by rfl) ⟨2188889, by rfl⟩ : syracuseStep 2918519 = 4377779) B4377779
theorem B1296519 : Blo 1295966 1296519 := bstep (se 1 (by rfl) ⟨972389, by rfl⟩ : syracuseStep 1296519 = 1944779) B1944779
theorem B1296527 : Blo 1295966 1296527 := bstep (se 1 (by rfl) ⟨972395, by rfl⟩ : syracuseStep 1296527 = 1944791) B1944791
theorem B2189497 : Blo 1295966 2189497 := bstep (se 2 (by rfl) ⟨821061, by rfl⟩ : syracuseStep 2189497 = 1642123) B1642123
theorem B1296571 : Blo 1295966 1296571 := bstep (se 1 (by rfl) ⟨972428, by rfl⟩ : syracuseStep 1296571 = 1944857) B1944857
theorem B6564077 : Blo 1295966 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B1296647 : Blo 1295966 1296647 := bstep (se 1 (by rfl) ⟨972485, by rfl⟩ : syracuseStep 1296647 = 1944971) B1944971
theorem B1296655 : Blo 1295966 1296655 := bstep (se 1 (by rfl) ⟨972491, by rfl⟩ : syracuseStep 1296655 = 1944983) B1944983
theorem B2918699 : Blo 1295966 2918699 := bstep (se 1 (by rfl) ⟨2189024, by rfl⟩ : syracuseStep 2918699 = 4378049) B4378049
theorem B1296699 : Blo 1295966 1296699 := bstep (se 1 (by rfl) ⟨972524, by rfl⟩ : syracuseStep 1296699 = 1945049) B1945049
theorem B1845623 : Blo 1295966 1845623 := bstep (se 1 (by rfl) ⟨1384217, by rfl⟩ : syracuseStep 1845623 = 2768435) B2768435
theorem B1296775 : Blo 1295966 1296775 := bstep (se 1 (by rfl) ⟨972581, by rfl⟩ : syracuseStep 1296775 = 1945163) B1945163
theorem B1943951 : Blo 1295966 1943951 := bstep (se 1 (by rfl) ⟨1457963, by rfl⟩ : syracuseStep 1943951 = 2915927) B2915927
theorem B1296783 : Blo 1295966 1296783 := bstep (se 1 (by rfl) ⟨972587, by rfl⟩ : syracuseStep 1296783 = 1945175) B1945175
theorem B1558927 : Blo 1295966 1558927 := bstep (se 1 (by rfl) ⟨1169195, by rfl⟩ : syracuseStep 1558927 = 2338391) B2338391
theorem B1943993 : Blo 1295966 1943993 := bstep (se 2 (by rfl) ⟨728997, by rfl⟩ : syracuseStep 1943993 = 1457995) B1457995
theorem B1296827 : Blo 1295966 1296827 := bstep (se 1 (by rfl) ⟨972620, by rfl⟩ : syracuseStep 1296827 = 1945241) B1945241
theorem B1944071 : Blo 1295966 1944071 := bstep (se 1 (by rfl) ⟨1458053, by rfl⟩ : syracuseStep 1944071 = 2916107) B2916107
theorem B1296903 : Blo 1295966 1296903 := bstep (se 1 (by rfl) ⟨972677, by rfl⟩ : syracuseStep 1296903 = 1945355) B1945355
theorem B1296911 : Blo 1295966 1296911 := bstep (se 1 (by rfl) ⟨972683, by rfl⟩ : syracuseStep 1296911 = 1945367) B1945367
theorem B1944107 : Blo 1295966 1944107 := bstep (se 1 (by rfl) ⟨1458080, by rfl⟩ : syracuseStep 1944107 = 2916161) B2916161
theorem B4377131 : Blo 1295966 4377131 := bstep (se 1 (by rfl) ⟨3282848, by rfl⟩ : syracuseStep 4377131 = 6565697) B6565697
theorem B2886187 : Blo 1295966 2886187 := bstep (se 1 (by rfl) ⟨2164640, by rfl⟩ : syracuseStep 2886187 = 4329281) B4329281
theorem B1296955 : Blo 1295966 1296955 := bstep (se 1 (by rfl) ⟨972716, by rfl⟩ : syracuseStep 1296955 = 1945433) B1945433
theorem B1944137 : Blo 1295966 1944137 := bstep (se 2 (by rfl) ⟨729051, by rfl⟩ : syracuseStep 1944137 = 1458103) B1458103
theorem B1297031 : Blo 1295966 1297031 := bstep (se 1 (by rfl) ⟨972773, by rfl⟩ : syracuseStep 1297031 = 1945547) B1945547
theorem B1297039 : Blo 1295966 1297039 := bstep (se 1 (by rfl) ⟨972779, by rfl⟩ : syracuseStep 1297039 = 1945559) B1945559
theorem B2919059 : Blo 1295966 2919059 := bstep (se 1 (by rfl) ⟨2189294, by rfl⟩ : syracuseStep 2919059 = 4378589) B4378589
theorem B1845931 : Blo 1295966 1845931 := bstep (se 1 (by rfl) ⟨1384448, by rfl⟩ : syracuseStep 1845931 = 2768897) B2768897
theorem B1944251 : Blo 1295966 1944251 := bstep (se 1 (by rfl) ⟨1458188, by rfl⟩ : syracuseStep 1944251 = 2916377) B2916377
theorem B1297083 : Blo 1295966 1297083 := bstep (se 1 (by rfl) ⟨972812, by rfl⟩ : syracuseStep 1297083 = 1945625) B1945625
theorem B2919113 : Blo 1295966 2919113 := bstep (se 2 (by rfl) ⟨1094667, by rfl⟩ : syracuseStep 2919113 = 2189335) B2189335
theorem B1944311 : Blo 1295966 1944311 := bstep (se 1 (by rfl) ⟨1458233, by rfl⟩ : syracuseStep 1944311 = 2916467) B2916467
theorem B1297159 : Blo 1295966 1297159 := bstep (se 1 (by rfl) ⟨972869, by rfl⟩ : syracuseStep 1297159 = 1945739) B1945739
theorem B1944335 : Blo 1295966 1944335 := bstep (se 1 (by rfl) ⟨1458251, by rfl⟩ : syracuseStep 1944335 = 2916503) B2916503
theorem B1297167 : Blo 1295966 1297167 := bstep (se 1 (by rfl) ⟨972875, by rfl⟩ : syracuseStep 1297167 = 1945751) B1945751
theorem B2337569 : Blo 1295966 2337569 := bstep (se 2 (by rfl) ⟨876588, by rfl⟩ : syracuseStep 2337569 = 1753177) B1753177
theorem B1944377 : Blo 1295966 1944377 := bstep (se 2 (by rfl) ⟨729141, by rfl⟩ : syracuseStep 1944377 = 1458283) B1458283
theorem B3115835 : Blo 1295966 3115835 := bstep (se 1 (by rfl) ⟨2336876, by rfl⟩ : syracuseStep 3115835 = 4673753) B4673753
theorem B1297211 : Blo 1295966 1297211 := bstep (se 1 (by rfl) ⟨972908, by rfl⟩ : syracuseStep 1297211 = 1945817) B1945817
theorem B2190199 : Blo 1295966 2190199 := bstep (se 1 (by rfl) ⟨1642649, by rfl⟩ : syracuseStep 2190199 = 3285299) B3285299
theorem B1944455 : Blo 1295966 1944455 := bstep (se 1 (by rfl) ⟨1458341, by rfl⟩ : syracuseStep 1944455 = 2916683) B2916683
theorem B1297287 : Blo 1295966 1297287 := bstep (se 1 (by rfl) ⟨972965, by rfl⟩ : syracuseStep 1297287 = 1945931) B1945931
theorem B1297295 : Blo 1295966 1297295 := bstep (se 1 (by rfl) ⟨972971, by rfl⟩ : syracuseStep 1297295 = 1945943) B1945943
theorem B3156889 : Blo 1295966 3156889 := bstep (se 2 (by rfl) ⟨1183833, by rfl⟩ : syracuseStep 3156889 = 2367667) B2367667
theorem B1944491 : Blo 1295966 1944491 := bstep (se 1 (by rfl) ⟨1458368, by rfl⟩ : syracuseStep 1944491 = 2916737) B2916737
theorem B1297339 : Blo 1295966 1297339 := bstep (se 1 (by rfl) ⟨973004, by rfl⟩ : syracuseStep 1297339 = 1946009) B1946009
theorem B1944521 : Blo 1295966 1944521 := bstep (se 2 (by rfl) ⟨729195, by rfl⟩ : syracuseStep 1944521 = 1458391) B1458391
theorem B7392221 : Blo 1295966 7392221 := bstep (se 3 (by rfl) ⟨1386041, by rfl⟩ : syracuseStep 7392221 = 2772083) B2772083
theorem B1297415 : Blo 1295966 1297415 := bstep (se 1 (by rfl) ⟨973061, by rfl⟩ : syracuseStep 1297415 = 1946123) B1946123
theorem B1297423 : Blo 1295966 1297423 := bstep (se 1 (by rfl) ⟨973067, by rfl⟩ : syracuseStep 1297423 = 1946135) B1946135
theorem B6564887 : Blo 1295966 6564887 := bstep (se 1 (by rfl) ⟨4923665, by rfl⟩ : syracuseStep 6564887 = 9847331) B9847331
theorem B1944635 : Blo 1295966 1944635 := bstep (se 1 (by rfl) ⟨1458476, by rfl⟩ : syracuseStep 1944635 = 2916953) B2916953
theorem B1297467 : Blo 1295966 1297467 := bstep (se 1 (by rfl) ⟨973100, by rfl⟩ : syracuseStep 1297467 = 1946201) B1946201
theorem B1944695 : Blo 1295966 1944695 := bstep (se 1 (by rfl) ⟨1458521, by rfl⟩ : syracuseStep 1944695 = 2917043) B2917043
theorem B1297543 : Blo 1295966 1297543 := bstep (se 1 (by rfl) ⟨973157, by rfl⟩ : syracuseStep 1297543 = 1946315) B1946315
theorem B1944719 : Blo 1295966 1944719 := bstep (se 1 (by rfl) ⟨1458539, by rfl⟩ : syracuseStep 1944719 = 2917079) B2917079
theorem B1846415 : Blo 1295966 1846415 := bstep (se 1 (by rfl) ⟨1384811, by rfl⟩ : syracuseStep 1846415 = 2769623) B2769623
theorem B1297551 : Blo 1295966 1297551 := bstep (se 1 (by rfl) ⟨973163, by rfl⟩ : syracuseStep 1297551 = 1946327) B1946327
theorem B1944761 : Blo 1295966 1944761 := bstep (se 2 (by rfl) ⟨729285, by rfl⟩ : syracuseStep 1944761 = 1458571) B1458571
theorem B1297595 : Blo 1295966 1297595 := bstep (se 1 (by rfl) ⟨973196, by rfl⟩ : syracuseStep 1297595 = 1946393) B1946393
theorem B1944839 : Blo 1295966 1944839 := bstep (se 1 (by rfl) ⟨1458629, by rfl⟩ : syracuseStep 1944839 = 2917259) B2917259
theorem B1297671 : Blo 1295966 1297671 := bstep (se 1 (by rfl) ⟨973253, by rfl⟩ : syracuseStep 1297671 = 1946507) B1946507
theorem B1297679 : Blo 1295966 1297679 := bstep (se 1 (by rfl) ⟨973259, by rfl⟩ : syracuseStep 1297679 = 1946519) B1946519
theorem B1944875 : Blo 1295966 1944875 := bstep (se 1 (by rfl) ⟨1458656, by rfl⟩ : syracuseStep 1944875 = 2917313) B2917313
theorem B3943723 : Blo 1295966 3943723 := bstep (se 1 (by rfl) ⟨2957792, by rfl⟩ : syracuseStep 3943723 = 5915585) B5915585
theorem B1297723 : Blo 1295966 1297723 := bstep (se 1 (by rfl) ⟨973292, by rfl⟩ : syracuseStep 1297723 = 1946585) B1946585
theorem B1944905 : Blo 1295966 1944905 := bstep (se 2 (by rfl) ⟨729339, by rfl⟩ : syracuseStep 1944905 = 1458679) B1458679
theorem B9850247 : Blo 1295966 9850247 := bstep (se 1 (by rfl) ⟨7387685, by rfl⟩ : syracuseStep 9850247 = 14775371) B14775371
theorem B2919815 : Blo 1295966 2919815 := bstep (se 1 (by rfl) ⟨2189861, by rfl⟩ : syracuseStep 2919815 = 4379723) B4379723
theorem B1297799 : Blo 1295966 1297799 := bstep (se 1 (by rfl) ⟨973349, by rfl⟩ : syracuseStep 1297799 = 1946699) B1946699
theorem B1297807 : Blo 1295966 1297807 := bstep (se 1 (by rfl) ⟨973355, by rfl⟩ : syracuseStep 1297807 = 1946711) B1946711
theorem B3116441 : Blo 1295966 3116441 := bstep (se 2 (by rfl) ⟨1168665, by rfl⟩ : syracuseStep 3116441 = 2337331) B2337331
theorem B27364787 : Blo 1295966 27364787 := bstep (se 1 (by rfl) ⟨20523590, by rfl⟩ : syracuseStep 27364787 = 41047181) B41047181
theorem B1945019 : Blo 1295966 1945019 := bstep (se 1 (by rfl) ⟨1458764, by rfl⟩ : syracuseStep 1945019 = 2917529) B2917529
theorem B1297851 : Blo 1295966 1297851 := bstep (se 1 (by rfl) ⟨973388, by rfl⟩ : syracuseStep 1297851 = 1946777) B1946777
theorem B1945079 : Blo 1295966 1945079 := bstep (se 1 (by rfl) ⟨1458809, by rfl⟩ : syracuseStep 1945079 = 2917619) B2917619
theorem B31534595 : Blo 1295966 31534595 := bstep (se 1 (by rfl) ⟨23650946, by rfl⟩ : syracuseStep 31534595 = 47301893) B47301893
theorem B1297927 : Blo 1295966 1297927 := bstep (se 1 (by rfl) ⟨973445, by rfl⟩ : syracuseStep 1297927 = 1946891) B1946891
theorem B1945103 : Blo 1295966 1945103 := bstep (se 1 (by rfl) ⟨1458827, by rfl⟩ : syracuseStep 1945103 = 2917655) B2917655
theorem B1297935 : Blo 1295966 1297935 := bstep (se 1 (by rfl) ⟨973451, by rfl⟩ : syracuseStep 1297935 = 1946903) B1946903
theorem B12463645 : Blo 1295966 12463645 := bstep (se 3 (by rfl) ⟨2336933, by rfl⟩ : syracuseStep 12463645 = 4673867) B4673867
theorem B13307435 : Blo 1295966 13307435 := bstep (se 1 (by rfl) ⟨9980576, by rfl⟩ : syracuseStep 13307435 = 19961153) B19961153
theorem B1642027 : Blo 1295966 1642027 := bstep (se 1 (by rfl) ⟨1231520, by rfl⟩ : syracuseStep 1642027 = 2463041) B2463041
theorem B1945145 : Blo 1295966 1945145 := bstep (se 2 (by rfl) ⟨729429, by rfl⟩ : syracuseStep 1945145 = 1458859) B1458859
theorem B2919995 : Blo 1295966 2919995 := bstep (se 1 (by rfl) ⟨2189996, by rfl⟩ : syracuseStep 2919995 = 4379993) B4379993
theorem B2076295 : Blo 1295966 2076295 := bstep (se 1 (by rfl) ⟨1557221, by rfl⟩ : syracuseStep 2076295 = 3114443) B3114443
theorem B1945223 : Blo 1295966 1945223 := bstep (se 1 (by rfl) ⟨1458917, by rfl⟩ : syracuseStep 1945223 = 2917835) B2917835
theorem B2494099 : Blo 1295966 2494099 := bstep (se 1 (by rfl) ⟨1870574, by rfl⟩ : syracuseStep 2494099 = 3741149) B3741149
theorem B1945259 : Blo 1295966 1945259 := bstep (se 1 (by rfl) ⟨1458944, by rfl⟩ : syracuseStep 1945259 = 2917889) B2917889
theorem B2920121 : Blo 1295966 2920121 := bstep (se 2 (by rfl) ⟨1095045, by rfl⟩ : syracuseStep 2920121 = 2190091) B2190091
theorem B1945289 : Blo 1295966 1945289 := bstep (se 2 (by rfl) ⟨729483, by rfl⟩ : syracuseStep 1945289 = 1458967) B1458967
theorem B7016165 : Blo 1295966 7016165 := bstep (se 4 (by rfl) ⟨657765, by rfl⟩ : syracuseStep 7016165 = 1315531) B1315531
theorem B49876721 : Blo 1295966 49876721 := bstep (se 2 (by rfl) ⟨18703770, by rfl⟩ : syracuseStep 49876721 = 37407541) B37407541
theorem B5328655 : Blo 1295966 5328655 := bstep (se 1 (by rfl) ⟨3996491, by rfl⟩ : syracuseStep 5328655 = 7992983) B7992983
theorem B24915761 : Blo 1295966 24915761 := bstep (se 2 (by rfl) ⟨9343410, by rfl⟩ : syracuseStep 24915761 = 18686821) B18686821
theorem B2461499 : Blo 1295966 2461499 := bstep (se 1 (by rfl) ⟨1846124, by rfl⟩ : syracuseStep 2461499 = 3692249) B3692249
theorem B1945403 : Blo 1295966 1945403 := bstep (se 1 (by rfl) ⟨1459052, by rfl⟩ : syracuseStep 1945403 = 2918105) B2918105
theorem B4378427 : Blo 1295966 4378427 := bstep (se 1 (by rfl) ⟨3283820, by rfl⟩ : syracuseStep 4378427 = 6567641) B6567641
theorem B1945463 : Blo 1295966 1945463 := bstep (se 1 (by rfl) ⟨1459097, by rfl⟩ : syracuseStep 1945463 = 2918195) B2918195
theorem B1945487 : Blo 1295966 1945487 := bstep (se 1 (by rfl) ⟨1459115, by rfl⟩ : syracuseStep 1945487 = 2918231) B2918231
theorem B26619799 : Blo 1295966 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B9605017 : Blo 1295966 9605017 := bstep (se 2 (by rfl) ⟨3601881, by rfl⟩ : syracuseStep 9605017 = 7203763) B7203763
theorem B1945529 : Blo 1295966 1945529 := bstep (se 2 (by rfl) ⟨729573, by rfl⟩ : syracuseStep 1945529 = 1459147) B1459147
theorem B4157369 : Blo 1295966 4157369 := bstep (se 2 (by rfl) ⟨1559013, by rfl⟩ : syracuseStep 4157369 = 3118027) B3118027
theorem B1945607 : Blo 1295966 1945607 := bstep (se 1 (by rfl) ⟨1459205, by rfl⟩ : syracuseStep 1945607 = 2918411) B2918411
theorem B3944477 : Blo 1295966 3944477 := bstep (se 3 (by rfl) ⟨739589, by rfl⟩ : syracuseStep 3944477 = 1479179) B1479179
theorem B1945643 : Blo 1295966 1945643 := bstep (se 1 (by rfl) ⟨1459232, by rfl⟩ : syracuseStep 1945643 = 2918465) B2918465
theorem B1945673 : Blo 1295966 1945673 := bstep (se 2 (by rfl) ⟨729627, by rfl⟩ : syracuseStep 1945673 = 1459255) B1459255
theorem B3158135 : Blo 1295966 3158135 := bstep (se 1 (by rfl) ⟨2368601, by rfl⟩ : syracuseStep 3158135 = 4737203) B4737203
theorem B3690643 : Blo 1295966 3690643 := bstep (se 1 (by rfl) ⟨2767982, by rfl⟩ : syracuseStep 3690643 = 5535965) B5535965
theorem B1945787 : Blo 1295966 1945787 := bstep (se 1 (by rfl) ⟨1459340, by rfl⟩ : syracuseStep 1945787 = 2918681) B2918681
theorem B6230209 : Blo 1295966 6230209 := bstep (se 2 (by rfl) ⟨2336328, by rfl⟩ : syracuseStep 6230209 = 4672657) B4672657
theorem B1945847 : Blo 1295966 1945847 := bstep (se 1 (by rfl) ⟨1459385, by rfl⟩ : syracuseStep 1945847 = 2918771) B2918771
theorem B1945871 : Blo 1295966 1945871 := bstep (se 1 (by rfl) ⟨1459403, by rfl⟩ : syracuseStep 1945871 = 2918807) B2918807
theorem B2461985 : Blo 1295966 2461985 := bstep (se 2 (by rfl) ⟨923244, by rfl⟩ : syracuseStep 2461985 = 1846489) B1846489
theorem B4378913 : Blo 1295966 4378913 := bstep (se 2 (by rfl) ⟨1642092, by rfl⟩ : syracuseStep 4378913 = 3284185) B3284185
theorem B1945913 : Blo 1295966 1945913 := bstep (se 2 (by rfl) ⟨729717, by rfl⟩ : syracuseStep 1945913 = 1459435) B1459435
theorem B6746503 : Blo 1295966 6746503 := bstep (se 1 (by rfl) ⟨5059877, by rfl⟩ : syracuseStep 6746503 = 10119755) B10119755
theorem B1945991 : Blo 1295966 1945991 := bstep (se 1 (by rfl) ⟨1459493, by rfl⟩ : syracuseStep 1945991 = 2918987) B2918987
theorem B4993415 : Blo 1295966 4993415 := bstep (se 1 (by rfl) ⟨3745061, by rfl⟩ : syracuseStep 4993415 = 7490123) B7490123
theorem B1946027 : Blo 1295966 1946027 := bstep (se 1 (by rfl) ⟨1459520, by rfl⟩ : syracuseStep 1946027 = 2919041) B2919041
theorem B1946057 : Blo 1295966 1946057 := bstep (se 2 (by rfl) ⟨729771, by rfl⟩ : syracuseStep 1946057 = 1459543) B1459543
theorem B2462251 : Blo 1295966 2462251 := bstep (se 1 (by rfl) ⟨1846688, by rfl⟩ : syracuseStep 2462251 = 3693377) B3693377
theorem B2806331 : Blo 1295966 2806331 := bstep (se 1 (by rfl) ⟨2104748, by rfl⟩ : syracuseStep 2806331 = 4209497) B4209497
theorem B1946171 : Blo 1295966 1946171 := bstep (se 1 (by rfl) ⟨1459628, by rfl⟩ : syracuseStep 1946171 = 2919257) B2919257
theorem B1946231 : Blo 1295966 1946231 := bstep (se 1 (by rfl) ⟨1459673, by rfl⟩ : syracuseStep 1946231 = 2919347) B2919347
theorem B3281543 : Blo 1295966 3281543 := bstep (se 1 (by rfl) ⟨2461157, by rfl⟩ : syracuseStep 3281543 = 4922315) B4922315
theorem B1946255 : Blo 1295966 1946255 := bstep (se 1 (by rfl) ⟨1459691, by rfl⟩ : syracuseStep 1946255 = 2919383) B2919383
theorem B3281593 : Blo 1295966 3281593 := bstep (se 2 (by rfl) ⟨1230597, by rfl⟩ : syracuseStep 3281593 = 2461195) B2461195
theorem B1946297 : Blo 1295966 1946297 := bstep (se 2 (by rfl) ⟨729861, by rfl⟩ : syracuseStep 1946297 = 1459723) B1459723
theorem B1946375 : Blo 1295966 1946375 := bstep (se 1 (by rfl) ⟨1459781, by rfl⟩ : syracuseStep 1946375 = 2919563) B2919563
theorem B1946411 : Blo 1295966 1946411 := bstep (se 1 (by rfl) ⟨1459808, by rfl⟩ : syracuseStep 1946411 = 2919617) B2919617
theorem B1946441 : Blo 1295966 1946441 := bstep (se 2 (by rfl) ⟨729915, by rfl⟩ : syracuseStep 1946441 = 1459831) B1459831
theorem B4379507 : Blo 1295966 4379507 := bstep (se 1 (by rfl) ⟨3284630, by rfl⟩ : syracuseStep 4379507 = 6569261) B6569261
theorem B5919635 : Blo 1295966 5919635 := bstep (se 1 (by rfl) ⟨4439726, by rfl⟩ : syracuseStep 5919635 = 8879453) B8879453
theorem B1946555 : Blo 1295966 1946555 := bstep (se 1 (by rfl) ⟨1459916, by rfl⟩ : syracuseStep 1946555 = 2919833) B2919833
theorem B1946615 : Blo 1295966 1946615 := bstep (se 1 (by rfl) ⟨1459961, by rfl⟩ : syracuseStep 1946615 = 2919923) B2919923
theorem B1946639 : Blo 1295966 1946639 := bstep (se 1 (by rfl) ⟨1459979, by rfl⟩ : syracuseStep 1946639 = 2919959) B2919959
theorem B1946681 : Blo 1295966 1946681 := bstep (se 2 (by rfl) ⟨730005, by rfl⟩ : syracuseStep 1946681 = 1460011) B1460011
theorem B11072645 : Blo 1295966 11072645 := bstep (se 4 (by rfl) ⟨1038060, by rfl⟩ : syracuseStep 11072645 = 2076121) B2076121
theorem B1946759 : Blo 1295966 1946759 := bstep (se 1 (by rfl) ⟨1460069, by rfl⟩ : syracuseStep 1946759 = 2920139) B2920139
theorem B1946795 : Blo 1295966 1946795 := bstep (se 1 (by rfl) ⟨1460096, by rfl⟩ : syracuseStep 1946795 = 2920193) B2920193
theorem B1946825 : Blo 1295966 1946825 := bstep (se 2 (by rfl) ⟨730059, by rfl⟩ : syracuseStep 1946825 = 1460119) B1460119
theorem B3282191 : Blo 1295966 3282191 := bstep (se 1 (by rfl) ⟨2461643, by rfl⟩ : syracuseStep 3282191 = 4923287) B4923287
theorem B2077967 : Blo 1295966 2077967 := bstep (se 1 (by rfl) ⟨1558475, by rfl⟩ : syracuseStep 2077967 = 3116951) B3116951
theorem B1946939 : Blo 1295966 1946939 := bstep (se 1 (by rfl) ⟨1460204, by rfl⟩ : syracuseStep 1946939 = 2920409) B2920409
theorem B4740619 : Blo 1295966 4740619 := bstep (se 1 (by rfl) ⟨3555464, by rfl⟩ : syracuseStep 4740619 = 7110929) B7110929
theorem B3118603 : Blo 1295966 3118603 := bstep (se 1 (by rfl) ⟨2338952, by rfl⟩ : syracuseStep 3118603 = 4677905) B4677905
theorem B11392579 : Blo 1295966 11392579 := bstep (se 1 (by rfl) ⟨8544434, by rfl⟩ : syracuseStep 11392579 = 17088869) B17088869
theorem B17741389 : Blo 1295966 17741389 := bstep (se 3 (by rfl) ⟨3326510, by rfl⟩ : syracuseStep 17741389 = 6653021) B6653021
theorem B14784119 : Blo 1295966 14784119 := bstep (se 1 (by rfl) ⟨11088089, by rfl⟩ : syracuseStep 14784119 = 22176179) B22176179
theorem B2463367 : Blo 1295966 2463367 := bstep (se 1 (by rfl) ⟨1847525, by rfl⟩ : syracuseStep 2463367 = 3695051) B3695051
theorem B3692317 : Blo 1295966 3692317 := bstep (se 3 (by rfl) ⟨692309, by rfl⟩ : syracuseStep 3692317 = 1384619) B1384619
theorem B3692375 : Blo 1295966 3692375 := bstep (se 1 (by rfl) ⟨2769281, by rfl⟩ : syracuseStep 3692375 = 5538563) B5538563
theorem B10524505 : Blo 1295966 10524505 := bstep (se 2 (by rfl) ⟨3946689, by rfl⟩ : syracuseStep 10524505 = 7893379) B7893379
theorem B3282889 : Blo 1295966 3282889 := bstep (se 2 (by rfl) ⟨1231083, by rfl⟩ : syracuseStep 3282889 = 2462167) B2462167
theorem B7387139 : Blo 1295966 7387139 := bstep (se 1 (by rfl) ⟨5540354, by rfl⟩ : syracuseStep 7387139 = 11080709) B11080709
theorem B7010327 : Blo 1295966 7010327 := bstep (se 1 (by rfl) ⟨5257745, by rfl⟩ : syracuseStep 7010327 = 10515491) B10515491
theorem B6567965 : Blo 1295966 6567965 := bstep (se 3 (by rfl) ⟨1231493, by rfl⟩ : syracuseStep 6567965 = 2462987) B2462987
theorem B3283031 : Blo 1295966 3283031 := bstep (se 1 (by rfl) ⟨2462273, by rfl⟩ : syracuseStep 3283031 = 4924547) B4924547
theorem B2463929 : Blo 1295966 2463929 := bstep (se 2 (by rfl) ⟨923973, by rfl⟩ : syracuseStep 2463929 = 1847947) B1847947
theorem B7387595 : Blo 1295966 7387595 := bstep (se 1 (by rfl) ⟨5540696, by rfl⟩ : syracuseStep 7387595 = 11081393) B11081393
theorem B6568451 : Blo 1295966 6568451 := bstep (se 1 (by rfl) ⟨4926338, by rfl⟩ : syracuseStep 6568451 = 9852677) B9852677
theorem B9353731 : Blo 1295966 9353731 := bstep (se 1 (by rfl) ⟨7015298, by rfl⟩ : syracuseStep 9353731 = 14030597) B14030597
theorem B12466993 : Blo 1295966 12466993 := bstep (se 2 (by rfl) ⟨4675122, by rfl⟩ : syracuseStep 12466993 = 9350245) B9350245
theorem B4152217 : Blo 1295966 4152217 := bstep (se 2 (by rfl) ⟨1557081, by rfl⟩ : syracuseStep 4152217 = 3114163) B3114163
theorem B2104265 : Blo 1295966 2104265 := bstep (se 2 (by rfl) ⟨789099, by rfl⟩ : syracuseStep 2104265 = 1578199) B1578199
theorem B6233053 : Blo 1295966 6233053 := bstep (se 3 (by rfl) ⟨1168697, by rfl⟩ : syracuseStep 6233053 = 2337395) B2337395
theorem B21044285 : Blo 1295966 21044285 := bstep (se 3 (by rfl) ⟨3945803, by rfl⟩ : syracuseStep 21044285 = 7891607) B7891607
theorem B7388279 : Blo 1295966 7388279 := bstep (se 1 (by rfl) ⟨5541209, by rfl⟩ : syracuseStep 7388279 = 11082419) B11082419
theorem B6233345 : Blo 1295966 6233345 := bstep (se 2 (by rfl) ⟨2337504, by rfl⟩ : syracuseStep 6233345 = 4675009) B4675009
theorem B14769539 : Blo 1295966 14769539 := bstep (se 1 (by rfl) ⟨11077154, by rfl⟩ : syracuseStep 14769539 = 22154309) B22154309
theorem B4373945 : Blo 1295966 4373945 := bstep (se 2 (by rfl) ⟨1640229, by rfl⟩ : syracuseStep 4373945 = 3280459) B3280459
theorem B3694025 : Blo 1295966 3694025 := bstep (se 2 (by rfl) ⟨1385259, by rfl⟩ : syracuseStep 3694025 = 2770519) B2770519
theorem B3792413 : Blo 1295966 3792413 := bstep (se 3 (by rfl) ⟨711077, by rfl⟩ : syracuseStep 3792413 = 1422155) B1422155
theorem B6561323 : Blo 1295966 6561323 := bstep (se 1 (by rfl) ⟨4920992, by rfl⟩ : syracuseStep 6561323 = 9841985) B9841985
theorem B4153103 : Blo 1295966 4153103 := bstep (se 1 (by rfl) ⟨3114827, by rfl⟩ : syracuseStep 4153103 = 6229655) B6229655
theorem B2187067 : Blo 1295966 2187067 := bstep (se 1 (by rfl) ⟨1640300, by rfl⟩ : syracuseStep 2187067 = 3280601) B3280601
theorem B2916215 : Blo 1295966 2916215 := bstep (se 1 (by rfl) ⟨2187161, by rfl⟩ : syracuseStep 2916215 = 4374323) B4374323
theorem B2629523 : Blo 1295966 2629523 := bstep (se 1 (by rfl) ⟨1972142, by rfl⟩ : syracuseStep 2629523 = 3944285) B3944285
theorem B2187209 : Blo 1295966 2187209 := bstep (se 2 (by rfl) ⟨820203, by rfl⟩ : syracuseStep 2187209 = 1640407) B1640407
theorem B2916359 : Blo 1295966 2916359 := bstep (se 1 (by rfl) ⟨2187269, by rfl⟩ : syracuseStep 2916359 = 4374539) B4374539
theorem B10518605 : Blo 1295966 10518605 := bstep (se 3 (by rfl) ⟨1972238, by rfl⟩ : syracuseStep 10518605 = 3944477) B3944477
theorem B2916431 : Blo 1295966 2916431 := bstep (se 1 (by rfl) ⟨2187323, by rfl⟩ : syracuseStep 2916431 = 4374647) B4374647
theorem B2105423 : Blo 1295966 2105423 := bstep (se 1 (by rfl) ⟨1579067, by rfl⟩ : syracuseStep 2105423 = 3158135) B3158135
theorem B8306945 : Blo 1295966 8306945 := bstep (se 2 (by rfl) ⟨3115104, by rfl⟩ : syracuseStep 8306945 = 6230209) B6230209
theorem B4923773 : Blo 1295966 4923773 := bstep (se 3 (by rfl) ⟨923207, by rfl⟩ : syracuseStep 4923773 = 1846415) B1846415
theorem B2187695 : Blo 1295966 2187695 := bstep (se 1 (by rfl) ⟨1640771, by rfl⟩ : syracuseStep 2187695 = 3281543) B3281543
theorem B1458607 : Blo 1295966 1458607 := bstep (se 1 (by rfl) ⟨1093955, by rfl⟩ : syracuseStep 1458607 = 2187911) B2187911
theorem B2916827 : Blo 1295966 2916827 := bstep (se 1 (by rfl) ⟨2187620, by rfl⟩ : syracuseStep 2916827 = 4375241) B4375241
theorem B8995337 : Blo 1295966 8995337 := bstep (se 2 (by rfl) ⟨3373251, by rfl⟩ : syracuseStep 8995337 = 6746503) B6746503
theorem B4375079 : Blo 1295966 4375079 := bstep (se 1 (by rfl) ⟨3281309, by rfl⟩ : syracuseStep 4375079 = 6562619) B6562619
theorem B4375187 : Blo 1295966 4375187 := bstep (se 1 (by rfl) ⟨3281390, by rfl⟩ : syracuseStep 4375187 = 6562781) B6562781
theorem B3326675 : Blo 1295966 3326675 := bstep (se 1 (by rfl) ⟨2495006, by rfl⟩ : syracuseStep 3326675 = 4990013) B4990013
theorem B7381763 : Blo 1295966 7381763 := bstep (se 1 (by rfl) ⟨5536322, by rfl⟩ : syracuseStep 7381763 = 11072645) B11072645
theorem B2188127 : Blo 1295966 2188127 := bstep (se 1 (by rfl) ⟨1641095, by rfl⟩ : syracuseStep 2188127 = 3282191) B3282191
theorem B1459039 : Blo 1295966 1459039 := bstep (se 1 (by rfl) ⟨1094279, by rfl⟩ : syracuseStep 1459039 = 2188559) B2188559
theorem B1385311 : Blo 1295966 1385311 := bstep (se 1 (by rfl) ⟨1038983, by rfl⟩ : syracuseStep 1385311 = 2077967) B2077967
theorem B4375403 : Blo 1295966 4375403 := bstep (se 1 (by rfl) ⟨3281552, by rfl⟩ : syracuseStep 4375403 = 6563105) B6563105
theorem B4375457 : Blo 1295966 4375457 := bstep (se 2 (by rfl) ⟨1640796, by rfl⟩ : syracuseStep 4375457 = 3281593) B3281593
theorem B2917295 : Blo 1295966 2917295 := bstep (se 1 (by rfl) ⟨2187971, by rfl⟩ : syracuseStep 2917295 = 4375943) B4375943
theorem B16622657 : Blo 1295966 16622657 := bstep (se 2 (by rfl) ⟨6233496, by rfl⟩ : syracuseStep 16622657 = 12466993) B12466993
theorem B9856079 : Blo 1295966 9856079 := bstep (se 1 (by rfl) ⟨7392059, by rfl⟩ : syracuseStep 9856079 = 14784119) B14784119
theorem B2917547 : Blo 1295966 2917547 := bstep (se 1 (by rfl) ⟨2188160, by rfl⟩ : syracuseStep 2917547 = 4376321) B4376321
theorem B1459399 : Blo 1295966 1459399 := bstep (se 1 (by rfl) ⟨1094549, by rfl⟩ : syracuseStep 1459399 = 2189099) B2189099
theorem B4924759 : Blo 1295966 4924759 := bstep (se 1 (by rfl) ⟨3693569, by rfl⟩ : syracuseStep 4924759 = 7387139) B7387139
theorem B2188687 : Blo 1295966 2188687 := bstep (se 1 (by rfl) ⟨1641515, by rfl⟩ : syracuseStep 2188687 = 3283031) B3283031
theorem B28419493 : Blo 1295966 28419493 := bstep (se 4 (by rfl) ⟨2664327, by rfl⟩ : syracuseStep 28419493 = 5328655) B5328655
theorem B4376051 : Blo 1295966 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B1295967 : Blo 1295966 1295967 := bstep (se 1 (by rfl) ⟨971975, by rfl⟩ : syracuseStep 1295967 = 1943951) B1943951
theorem B1295995 : Blo 1295966 1295995 := bstep (se 1 (by rfl) ⟨971996, by rfl⟩ : syracuseStep 1295995 = 1943993) B1943993
theorem B4925063 : Blo 1295966 4925063 := bstep (se 1 (by rfl) ⟨3693797, by rfl⟩ : syracuseStep 4925063 = 7387595) B7387595
theorem B1296047 : Blo 1295966 1296047 := bstep (se 1 (by rfl) ⟨972035, by rfl⟩ : syracuseStep 1296047 = 1944071) B1944071
theorem B1296071 : Blo 1295966 1296071 := bstep (se 1 (by rfl) ⟨972053, by rfl⟩ : syracuseStep 1296071 = 1944107) B1944107
theorem B2918087 : Blo 1295966 2918087 := bstep (se 1 (by rfl) ⟨2188565, by rfl⟩ : syracuseStep 2918087 = 4377131) B4377131
theorem B1296091 : Blo 1295966 1296091 := bstep (se 1 (by rfl) ⟨972068, by rfl⟩ : syracuseStep 1296091 = 1944137) B1944137
theorem B1296167 : Blo 1295966 1296167 := bstep (se 1 (by rfl) ⟨972125, by rfl⟩ : syracuseStep 1296167 = 1944251) B1944251
theorem B1296207 : Blo 1295966 1296207 := bstep (se 1 (by rfl) ⟨972155, by rfl⟩ : syracuseStep 1296207 = 1944311) B1944311
theorem B1296223 : Blo 1295966 1296223 := bstep (se 1 (by rfl) ⟨972167, by rfl⟩ : syracuseStep 1296223 = 1944335) B1944335
theorem B1558379 : Blo 1295966 1558379 := bstep (se 1 (by rfl) ⟨1168784, by rfl⟩ : syracuseStep 1558379 = 2337569) B2337569
theorem B1296251 : Blo 1295966 1296251 := bstep (se 1 (by rfl) ⟨972188, by rfl⟩ : syracuseStep 1296251 = 1944377) B1944377
theorem B1296303 : Blo 1295966 1296303 := bstep (se 1 (by rfl) ⟨972227, by rfl⟩ : syracuseStep 1296303 = 1944455) B1944455
theorem B1296327 : Blo 1295966 1296327 := bstep (se 1 (by rfl) ⟨972245, by rfl⟩ : syracuseStep 1296327 = 1944491) B1944491
theorem B1296347 : Blo 1295966 1296347 := bstep (se 1 (by rfl) ⟨972260, by rfl⟩ : syracuseStep 1296347 = 1944521) B1944521
theorem B4376591 : Blo 1295966 4376591 := bstep (se 1 (by rfl) ⟨3282443, by rfl⟩ : syracuseStep 4376591 = 6564887) B6564887
theorem B1296423 : Blo 1295966 1296423 := bstep (se 1 (by rfl) ⟨972317, by rfl⟩ : syracuseStep 1296423 = 1944635) B1944635
theorem B2189369 : Blo 1295966 2189369 := bstep (se 2 (by rfl) ⟨821013, by rfl⟩ : syracuseStep 2189369 = 1642027) B1642027
theorem B1296463 : Blo 1295966 1296463 := bstep (se 1 (by rfl) ⟨972347, by rfl⟩ : syracuseStep 1296463 = 1944695) B1944695
theorem B4925519 : Blo 1295966 4925519 := bstep (se 1 (by rfl) ⟨3694139, by rfl⟩ : syracuseStep 4925519 = 7388279) B7388279
theorem B15190105 : Blo 1295966 15190105 := bstep (se 2 (by rfl) ⟨5696289, by rfl⟩ : syracuseStep 15190105 = 11392579) B11392579
theorem B1296479 : Blo 1295966 1296479 := bstep (se 1 (by rfl) ⟨972359, by rfl⟩ : syracuseStep 1296479 = 1944719) B1944719
theorem B1296507 : Blo 1295966 1296507 := bstep (se 1 (by rfl) ⟨972380, by rfl⟩ : syracuseStep 1296507 = 1944761) B1944761
theorem B4155563 : Blo 1295966 4155563 := bstep (se 1 (by rfl) ⟨3116672, by rfl⟩ : syracuseStep 4155563 = 6233345) B6233345
theorem B1296559 : Blo 1295966 1296559 := bstep (se 1 (by rfl) ⟨972419, by rfl⟩ : syracuseStep 1296559 = 1944839) B1944839
theorem B1296583 : Blo 1295966 1296583 := bstep (se 1 (by rfl) ⟨972437, by rfl⟩ : syracuseStep 1296583 = 1944875) B1944875
theorem B1296603 : Blo 1295966 1296603 := bstep (se 1 (by rfl) ⟨972452, by rfl⟩ : syracuseStep 1296603 = 1944905) B1944905
theorem B1296679 : Blo 1295966 1296679 := bstep (se 1 (by rfl) ⟨972509, by rfl⟩ : syracuseStep 1296679 = 1945019) B1945019
theorem B1296719 : Blo 1295966 1296719 := bstep (se 1 (by rfl) ⟨972539, by rfl⟩ : syracuseStep 1296719 = 1945079) B1945079
theorem B21023063 : Blo 1295966 21023063 := bstep (se 1 (by rfl) ⟨15767297, by rfl⟩ : syracuseStep 21023063 = 31534595) B31534595
theorem B1296735 : Blo 1295966 1296735 := bstep (se 1 (by rfl) ⟨972551, by rfl⟩ : syracuseStep 1296735 = 1945103) B1945103
theorem B1296763 : Blo 1295966 1296763 := bstep (se 1 (by rfl) ⟨972572, by rfl⟩ : syracuseStep 1296763 = 1945145) B1945145
theorem B1296815 : Blo 1295966 1296815 := bstep (se 1 (by rfl) ⟨972611, by rfl⟩ : syracuseStep 1296815 = 1945223) B1945223
theorem B1296839 : Blo 1295966 1296839 := bstep (se 1 (by rfl) ⟨972629, by rfl⟩ : syracuseStep 1296839 = 1945259) B1945259
theorem B1296859 : Blo 1295966 1296859 := bstep (se 1 (by rfl) ⟨972644, by rfl⟩ : syracuseStep 1296859 = 1945289) B1945289
theorem B12806689 : Blo 1295966 12806689 := bstep (se 2 (by rfl) ⟨4802508, by rfl⟩ : syracuseStep 12806689 = 9605017) B9605017
theorem B1640999 : Blo 1295966 1640999 := bstep (se 1 (by rfl) ⟨1230749, by rfl⟩ : syracuseStep 1640999 = 2461499) B2461499
theorem B1296935 : Blo 1295966 1296935 := bstep (se 1 (by rfl) ⟨972701, by rfl⟩ : syracuseStep 1296935 = 1945403) B1945403
theorem B2918951 : Blo 1295966 2918951 := bstep (se 1 (by rfl) ⟨2189213, by rfl⟩ : syracuseStep 2918951 = 4378427) B4378427
theorem B1944143 : Blo 1295966 1944143 := bstep (se 1 (by rfl) ⟨1458107, by rfl⟩ : syracuseStep 1944143 = 2916215) B2916215
theorem B1296975 : Blo 1295966 1296975 := bstep (se 1 (by rfl) ⟨972731, by rfl⟩ : syracuseStep 1296975 = 1945463) B1945463
theorem B1296991 : Blo 1295966 1296991 := bstep (se 1 (by rfl) ⟨972743, by rfl⟩ : syracuseStep 1296991 = 1945487) B1945487
theorem B4377185 : Blo 1295966 4377185 := bstep (se 2 (by rfl) ⟨1641444, by rfl⟩ : syracuseStep 4377185 = 3282889) B3282889
theorem B1297019 : Blo 1295966 1297019 := bstep (se 1 (by rfl) ⟨972764, by rfl⟩ : syracuseStep 1297019 = 1945529) B1945529
theorem B2771579 : Blo 1295966 2771579 := bstep (se 1 (by rfl) ⟨2078684, by rfl⟩ : syracuseStep 2771579 = 4157369) B4157369
theorem B1297071 : Blo 1295966 1297071 := bstep (se 1 (by rfl) ⟨972803, by rfl⟩ : syracuseStep 1297071 = 1945607) B1945607
theorem B1944263 : Blo 1295966 1944263 := bstep (se 1 (by rfl) ⟨1458197, by rfl⟩ : syracuseStep 1944263 = 2916395) B2916395
theorem B1297095 : Blo 1295966 1297095 := bstep (se 1 (by rfl) ⟨972821, by rfl⟩ : syracuseStep 1297095 = 1945643) B1945643
theorem B5540561 : Blo 1295966 5540561 := bstep (se 2 (by rfl) ⟨2077710, by rfl⟩ : syracuseStep 5540561 = 4155421) B4155421
theorem B6564563 : Blo 1295966 6564563 := bstep (se 1 (by rfl) ⟨4923422, by rfl⟩ : syracuseStep 6564563 = 9846845) B9846845
theorem B1297115 : Blo 1295966 1297115 := bstep (se 1 (by rfl) ⟨972836, by rfl⟩ : syracuseStep 1297115 = 1945673) B1945673
theorem B2190071 : Blo 1295966 2190071 := bstep (se 1 (by rfl) ⟨1642553, by rfl⟩ : syracuseStep 2190071 = 3285107) B3285107
theorem B1297191 : Blo 1295966 1297191 := bstep (se 1 (by rfl) ⟨972893, by rfl⟩ : syracuseStep 1297191 = 1945787) B1945787
theorem B1297231 : Blo 1295966 1297231 := bstep (se 1 (by rfl) ⟨972923, by rfl⟩ : syracuseStep 1297231 = 1945847) B1945847
theorem B1297247 : Blo 1295966 1297247 := bstep (se 1 (by rfl) ⟨972935, by rfl⟩ : syracuseStep 1297247 = 1945871) B1945871
theorem B1944425 : Blo 1295966 1944425 := bstep (se 2 (by rfl) ⟨729159, by rfl⟩ : syracuseStep 1944425 = 1458319) B1458319
theorem B1641323 : Blo 1295966 1641323 := bstep (se 1 (by rfl) ⟨1230992, by rfl⟩ : syracuseStep 1641323 = 2461985) B2461985
theorem B2919275 : Blo 1295966 2919275 := bstep (se 1 (by rfl) ⟨2189456, by rfl⟩ : syracuseStep 2919275 = 4378913) B4378913
theorem B1297275 : Blo 1295966 1297275 := bstep (se 1 (by rfl) ⟨972956, by rfl⟩ : syracuseStep 1297275 = 1945913) B1945913
theorem B2919329 : Blo 1295966 2919329 := bstep (se 2 (by rfl) ⟨1094748, by rfl⟩ : syracuseStep 2919329 = 2189497) B2189497
theorem B1297327 : Blo 1295966 1297327 := bstep (se 1 (by rfl) ⟨972995, by rfl⟩ : syracuseStep 1297327 = 1945991) B1945991
theorem B3328943 : Blo 1295966 3328943 := bstep (se 1 (by rfl) ⟨2496707, by rfl⟩ : syracuseStep 3328943 = 4993415) B4993415
theorem B1944503 : Blo 1295966 1944503 := bstep (se 1 (by rfl) ⟨1458377, by rfl⟩ : syracuseStep 1944503 = 2916755) B2916755
theorem B4156343 : Blo 1295966 4156343 := bstep (se 1 (by rfl) ⟨3117257, by rfl⟩ : syracuseStep 4156343 = 6234515) B6234515
theorem B1297351 : Blo 1295966 1297351 := bstep (se 1 (by rfl) ⟨973013, by rfl⟩ : syracuseStep 1297351 = 1946027) B1946027
theorem B1944539 : Blo 1295966 1944539 := bstep (se 1 (by rfl) ⟨1458404, by rfl⟩ : syracuseStep 1944539 = 2916809) B2916809
theorem B1297371 : Blo 1295966 1297371 := bstep (se 1 (by rfl) ⟨973028, by rfl⟩ : syracuseStep 1297371 = 1946057) B1946057
theorem B1297447 : Blo 1295966 1297447 := bstep (se 1 (by rfl) ⟨973085, by rfl⟩ : syracuseStep 1297447 = 1946171) B1946171
theorem B4926521 : Blo 1295966 4926521 := bstep (se 2 (by rfl) ⟨1847445, by rfl⟩ : syracuseStep 4926521 = 3694891) B3694891
theorem B1297487 : Blo 1295966 1297487 := bstep (se 1 (by rfl) ⟨973115, by rfl⟩ : syracuseStep 1297487 = 1946231) B1946231
theorem B1297503 : Blo 1295966 1297503 := bstep (se 1 (by rfl) ⟨973127, by rfl⟩ : syracuseStep 1297503 = 1946255) B1946255
theorem B1297531 : Blo 1295966 1297531 := bstep (se 1 (by rfl) ⟨973148, by rfl⟩ : syracuseStep 1297531 = 1946297) B1946297
theorem B1297583 : Blo 1295966 1297583 := bstep (se 1 (by rfl) ⟨973187, by rfl⟩ : syracuseStep 1297583 = 1946375) B1946375
theorem B1297607 : Blo 1295966 1297607 := bstep (se 1 (by rfl) ⟨973205, by rfl⟩ : syracuseStep 1297607 = 1946411) B1946411
theorem B1297627 : Blo 1295966 1297627 := bstep (se 1 (by rfl) ⟨973220, by rfl⟩ : syracuseStep 1297627 = 1946441) B1946441
theorem B2919671 : Blo 1295966 2919671 := bstep (se 1 (by rfl) ⟨2189753, by rfl⟩ : syracuseStep 2919671 = 4379507) B4379507
theorem B4435211 : Blo 1295966 4435211 := bstep (se 1 (by rfl) ⟨3326408, by rfl⟩ : syracuseStep 4435211 = 6652817) B6652817
theorem B1297703 : Blo 1295966 1297703 := bstep (se 1 (by rfl) ⟨973277, by rfl⟩ : syracuseStep 1297703 = 1946555) B1946555
theorem B87633211 : Blo 1295966 87633211 := bstep (se 1 (by rfl) ⟨65724908, by rfl⟩ : syracuseStep 87633211 = 131449817) B131449817
theorem B1297743 : Blo 1295966 1297743 := bstep (se 1 (by rfl) ⟨973307, by rfl⟩ : syracuseStep 1297743 = 1946615) B1946615
theorem B12471641 : Blo 1295966 12471641 := bstep (se 2 (by rfl) ⟨4676865, by rfl⟩ : syracuseStep 12471641 = 9353731) B9353731
theorem B1297759 : Blo 1295966 1297759 := bstep (se 1 (by rfl) ⟨973319, by rfl⟩ : syracuseStep 1297759 = 1946639) B1946639
theorem B1297787 : Blo 1295966 1297787 := bstep (se 1 (by rfl) ⟨973340, by rfl⟩ : syracuseStep 1297787 = 1946681) B1946681
theorem B1945007 : Blo 1295966 1945007 := bstep (se 1 (by rfl) ⟨1458755, by rfl⟩ : syracuseStep 1945007 = 2917511) B2917511
theorem B1297839 : Blo 1295966 1297839 := bstep (se 1 (by rfl) ⟨973379, by rfl⟩ : syracuseStep 1297839 = 1946759) B1946759
theorem B1297863 : Blo 1295966 1297863 := bstep (se 1 (by rfl) ⟨973397, by rfl⟩ : syracuseStep 1297863 = 1946795) B1946795
theorem B1297883 : Blo 1295966 1297883 := bstep (se 1 (by rfl) ⟨973412, by rfl⟩ : syracuseStep 1297883 = 1946825) B1946825
theorem B1945097 : Blo 1295966 1945097 := bstep (se 2 (by rfl) ⟨729411, by rfl⟩ : syracuseStep 1945097 = 1458823) B1458823
theorem B1945127 : Blo 1295966 1945127 := bstep (se 1 (by rfl) ⟨1458845, by rfl⟩ : syracuseStep 1945127 = 2917691) B2917691
theorem B1297959 : Blo 1295966 1297959 := bstep (se 1 (by rfl) ⟨973469, by rfl⟩ : syracuseStep 1297959 = 1946939) B1946939
theorem B2461241 : Blo 1295966 2461241 := bstep (se 2 (by rfl) ⟨922965, by rfl⟩ : syracuseStep 2461241 = 1845931) B1845931
theorem B1945211 : Blo 1295966 1945211 := bstep (se 1 (by rfl) ⟨1458908, by rfl⟩ : syracuseStep 1945211 = 2917817) B2917817
theorem B2338427 : Blo 1295966 2338427 := bstep (se 1 (by rfl) ⟨1753820, by rfl⟩ : syracuseStep 2338427 = 3507641) B3507641
theorem B7892603 : Blo 1295966 7892603 := bstep (se 1 (by rfl) ⟨5919452, by rfl⟩ : syracuseStep 7892603 = 11838905) B11838905
theorem B4927175 : Blo 1295966 4927175 := bstep (se 1 (by rfl) ⟨3695381, by rfl⟩ : syracuseStep 4927175 = 7390763) B7390763
theorem B8310509 : Blo 1295966 8310509 := bstep (se 3 (by rfl) ⟨1558220, by rfl⟩ : syracuseStep 8310509 = 3116441) B3116441
theorem B1945337 : Blo 1295966 1945337 := bstep (se 2 (by rfl) ⟨729501, by rfl⟩ : syracuseStep 1945337 = 1459003) B1459003
theorem B2920265 : Blo 1295966 2920265 := bstep (se 2 (by rfl) ⟨1095099, by rfl⟩ : syracuseStep 2920265 = 2190199) B2190199
theorem B1945439 : Blo 1295966 1945439 := bstep (se 1 (by rfl) ⟨1459079, by rfl⟩ : syracuseStep 1945439 = 2918159) B2918159
theorem B1945451 : Blo 1295966 1945451 := bstep (se 1 (by rfl) ⟨1459088, by rfl⟩ : syracuseStep 1945451 = 2918177) B2918177
theorem B9850733 : Blo 1295966 9850733 := bstep (se 3 (by rfl) ⟨1847012, by rfl⟩ : syracuseStep 9850733 = 3694025) B3694025
theorem B2461583 : Blo 1295966 2461583 := bstep (se 1 (by rfl) ⟨1846187, by rfl⟩ : syracuseStep 2461583 = 3692375) B3692375
theorem B8310737 : Blo 1295966 8310737 := bstep (se 2 (by rfl) ⟨3116526, by rfl⟩ : syracuseStep 8310737 = 6233053) B6233053
theorem B4673551 : Blo 1295966 4673551 := bstep (se 1 (by rfl) ⟨3505163, by rfl⟩ : syracuseStep 4673551 = 7010327) B7010327
theorem B4378643 : Blo 1295966 4378643 := bstep (se 1 (by rfl) ⟨3283982, by rfl⟩ : syracuseStep 4378643 = 6567965) B6567965
theorem B1945679 : Blo 1295966 1945679 := bstep (se 1 (by rfl) ⟨1459259, by rfl⟩ : syracuseStep 1945679 = 2918519) B2918519
theorem B1642619 : Blo 1295966 1642619 := bstep (se 1 (by rfl) ⟨1231964, by rfl⟩ : syracuseStep 1642619 = 2463929) B2463929
theorem B7483549 : Blo 1295966 7483549 := bstep (se 3 (by rfl) ⟨1403165, by rfl⟩ : syracuseStep 7483549 = 2806331) B2806331
theorem B1945799 : Blo 1295966 1945799 := bstep (se 1 (by rfl) ⟨1459349, by rfl⟩ : syracuseStep 1945799 = 2918699) B2918699
theorem B9351425 : Blo 1295966 9351425 := bstep (se 2 (by rfl) ⟨3506784, by rfl⟩ : syracuseStep 9351425 = 7013569) B7013569
theorem B4378967 : Blo 1295966 4378967 := bstep (se 1 (by rfl) ⟨3284225, by rfl⟩ : syracuseStep 4378967 = 6568451) B6568451
theorem B1945961 : Blo 1295966 1945961 := bstep (se 2 (by rfl) ⟨729735, by rfl⟩ : syracuseStep 1945961 = 1459471) B1459471
theorem B1946039 : Blo 1295966 1946039 := bstep (se 1 (by rfl) ⟨1459529, by rfl⟩ : syracuseStep 1946039 = 2919059) B2919059
theorem B1946075 : Blo 1295966 1946075 := bstep (se 1 (by rfl) ⟨1459556, by rfl⟩ : syracuseStep 1946075 = 2919113) B2919113
theorem B2077223 : Blo 1295966 2077223 := bstep (se 1 (by rfl) ⟨1557917, by rfl⟩ : syracuseStep 2077223 = 3115835) B3115835
theorem B4928147 : Blo 1295966 4928147 := bstep (se 1 (by rfl) ⟨3696110, by rfl⟩ : syracuseStep 4928147 = 7392221) B7392221
theorem B6320825 : Blo 1295966 6320825 := bstep (se 2 (by rfl) ⟨2370309, by rfl⟩ : syracuseStep 6320825 = 4740619) B4740619
theorem B4158137 : Blo 1295966 4158137 := bstep (se 2 (by rfl) ⟨1559301, by rfl⟩ : syracuseStep 4158137 = 3118603) B3118603
theorem B16618193 : Blo 1295966 16618193 := bstep (se 2 (by rfl) ⟨6231822, by rfl⟩ : syracuseStep 16618193 = 12463645) B12463645
theorem B14029523 : Blo 1295966 14029523 := bstep (se 1 (by rfl) ⟨10522142, by rfl⟩ : syracuseStep 14029523 = 21044285) B21044285
theorem B102413069 : Blo 1295966 102413069 := bstep (se 3 (by rfl) ⟨19202450, by rfl⟩ : syracuseStep 102413069 = 38404901) B38404901
theorem B23655185 : Blo 1295966 23655185 := bstep (se 2 (by rfl) ⟨8870694, by rfl⟩ : syracuseStep 23655185 = 17741389) B17741389
theorem B6566831 : Blo 1295966 6566831 := bstep (se 1 (by rfl) ⟨4925123, by rfl⟩ : syracuseStep 6566831 = 9850247) B9850247
theorem B1946543 : Blo 1295966 1946543 := bstep (se 1 (by rfl) ⟨1459907, by rfl⟩ : syracuseStep 1946543 = 2919815) B2919815
theorem B1946633 : Blo 1295966 1946633 := bstep (se 2 (by rfl) ⟨729987, by rfl⟩ : syracuseStep 1946633 = 1459975) B1459975
theorem B2528275 : Blo 1295966 2528275 := bstep (se 1 (by rfl) ⟨1896206, by rfl⟩ : syracuseStep 2528275 = 3792413) B3792413
theorem B1946663 : Blo 1295966 1946663 := bstep (se 1 (by rfl) ⟨1459997, by rfl⟩ : syracuseStep 1946663 = 2919995) B2919995
theorem B1946747 : Blo 1295966 1946747 := bstep (se 1 (by rfl) ⟨1460060, by rfl⟩ : syracuseStep 1946747 = 2920121) B2920121
theorem B35493065 : Blo 1295966 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B16610507 : Blo 1295966 16610507 := bstep (se 1 (by rfl) ⟨12457880, by rfl⟩ : syracuseStep 16610507 = 24915761) B24915761
theorem B1946873 : Blo 1295966 1946873 := bstep (se 2 (by rfl) ⟨730077, by rfl⟩ : syracuseStep 1946873 = 1460155) B1460155
theorem B2078057 : Blo 1295966 2078057 := bstep (se 2 (by rfl) ⟨779271, by rfl⟩ : syracuseStep 2078057 = 1558543) B1558543
theorem B22779251 : Blo 1295966 22779251 := bstep (se 1 (by rfl) ⟨17084438, by rfl⟩ : syracuseStep 22779251 = 34168877) B34168877
theorem B3691919 : Blo 1295966 3691919 := bstep (se 1 (by rfl) ⟨2768939, by rfl⟩ : syracuseStep 3691919 = 5537879) B5537879
theorem B4380047 : Blo 1295966 4380047 := bstep (se 1 (by rfl) ⟨3285035, by rfl⟩ : syracuseStep 4380047 = 6570071) B6570071
theorem B9475571 : Blo 1295966 9475571 := bstep (se 1 (by rfl) ⟨7106678, by rfl⟩ : syracuseStep 9475571 = 14213357) B14213357
theorem B4920857 : Blo 1295966 4920857 := bstep (se 2 (by rfl) ⟨1845321, by rfl⟩ : syracuseStep 4920857 = 3690643) B3690643
theorem B4920871 : Blo 1295966 4920871 := bstep (se 1 (by rfl) ⟨3690653, by rfl⟩ : syracuseStep 4920871 = 7381307) B7381307
theorem B4675283 : Blo 1295966 4675283 := bstep (se 1 (by rfl) ⟨3506462, by rfl⟩ : syracuseStep 4675283 = 7012925) B7012925
theorem B2463443 : Blo 1295966 2463443 := bstep (se 1 (by rfl) ⟨1847582, by rfl⟩ : syracuseStep 2463443 = 3695165) B3695165
theorem B4380371 : Blo 1295966 4380371 := bstep (se 1 (by rfl) ⟨3285278, by rfl⟩ : syracuseStep 4380371 = 6570557) B6570557
theorem B42653441 : Blo 1295966 42653441 := bstep (se 2 (by rfl) ⟨15995040, by rfl⟩ : syracuseStep 42653441 = 31990081) B31990081
theorem B2078569 : Blo 1295966 2078569 := bstep (se 2 (by rfl) ⟨779463, by rfl⟩ : syracuseStep 2078569 = 1558927) B1558927
theorem B2463671 : Blo 1295966 2463671 := bstep (se 1 (by rfl) ⟨1847753, by rfl⟩ : syracuseStep 2463671 = 3695507) B3695507
theorem B3946423 : Blo 1295966 3946423 := bstep (se 1 (by rfl) ⟨2959817, by rfl⟩ : syracuseStep 3946423 = 5919635) B5919635
theorem B14768081 : Blo 1295966 14768081 := bstep (se 2 (by rfl) ⟨5538030, by rfl⟩ : syracuseStep 14768081 = 11076061) B11076061
theorem B2627623 : Blo 1295966 2627623 := bstep (se 1 (by rfl) ⟨1970717, by rfl⟩ : syracuseStep 2627623 = 3941435) B3941435
theorem B3283001 : Blo 1295966 3283001 := bstep (se 2 (by rfl) ⟨1231125, by rfl⟩ : syracuseStep 3283001 = 2462251) B2462251
theorem B3848249 : Blo 1295966 3848249 := bstep (se 2 (by rfl) ⟨1443093, by rfl⟩ : syracuseStep 3848249 = 2886187) B2886187
theorem B4921661 : Blo 1295966 4921661 := bstep (se 3 (by rfl) ⟨922811, by rfl⟩ : syracuseStep 4921661 = 1845623) B1845623
theorem B4676059 : Blo 1295966 4676059 := bstep (se 1 (by rfl) ⟨3507044, by rfl⟩ : syracuseStep 4676059 = 7014089) B7014089
theorem B4921843 : Blo 1295966 4921843 := bstep (se 1 (by rfl) ⟨3691382, by rfl⟩ : syracuseStep 4921843 = 7382765) B7382765
theorem B5536289 : Blo 1295966 5536289 := bstep (se 2 (by rfl) ⟨2076108, by rfl⟩ : syracuseStep 5536289 = 4152217) B4152217
theorem B4209185 : Blo 1295966 4209185 := bstep (se 2 (by rfl) ⟨1578444, by rfl⟩ : syracuseStep 4209185 = 3156889) B3156889
theorem B9853649 : Blo 1295966 9853649 := bstep (se 2 (by rfl) ⟨3695118, by rfl⟩ : syracuseStep 9853649 = 7390237) B7390237
theorem B4438813 : Blo 1295966 4438813 := bstep (se 3 (by rfl) ⟨832277, by rfl⟩ : syracuseStep 4438813 = 1664555) B1664555
theorem B5258297 : Blo 1295966 5258297 := bstep (se 2 (by rfl) ⟨1971861, by rfl⟩ : syracuseStep 5258297 = 3943723) B3943723
theorem B16833809 : Blo 1295966 16833809 := bstep (se 2 (by rfl) ⟨6312678, by rfl⟩ : syracuseStep 16833809 = 12625357) B12625357
theorem B2768393 : Blo 1295966 2768393 := bstep (se 2 (by rfl) ⟨1038147, by rfl⟩ : syracuseStep 2768393 = 2076295) B2076295
theorem B3284489 : Blo 1295966 3284489 := bstep (se 2 (by rfl) ⟨1231683, by rfl⟩ : syracuseStep 3284489 = 2463367) B2463367
theorem B3325465 : Blo 1295966 3325465 := bstep (se 2 (by rfl) ⟨1247049, by rfl⟩ : syracuseStep 3325465 = 2494099) B2494099
theorem B9846359 : Blo 1295966 9846359 := bstep (se 1 (by rfl) ⟨7384769, by rfl⟩ : syracuseStep 9846359 = 14769539) B14769539
theorem B18243191 : Blo 1295966 18243191 := bstep (se 1 (by rfl) ⟨13682393, by rfl⟩ : syracuseStep 18243191 = 27364787) B27364787
theorem B2915963 : Blo 1295966 2915963 := bstep (se 1 (by rfl) ⟨2186972, by rfl⟩ : syracuseStep 2915963 = 4373945) B4373945
theorem B4374215 : Blo 1295966 4374215 := bstep (se 1 (by rfl) ⟨3280661, by rfl⟩ : syracuseStep 4374215 = 6561323) B6561323
theorem B8871623 : Blo 1295966 8871623 := bstep (se 1 (by rfl) ⟨6653717, by rfl⟩ : syracuseStep 8871623 = 13307435) B13307435
theorem B4923089 : Blo 1295966 4923089 := bstep (se 2 (by rfl) ⟨1846158, by rfl⟩ : syracuseStep 4923089 = 3692317) B3692317
theorem B2916089 : Blo 1295966 2916089 := bstep (se 2 (by rfl) ⟨1093533, by rfl⟩ : syracuseStep 2916089 = 2187067) B2187067
theorem B14032673 : Blo 1295966 14032673 := bstep (se 2 (by rfl) ⟨5262252, by rfl⟩ : syracuseStep 14032673 = 10524505) B10524505
theorem B4677443 : Blo 1295966 4677443 := bstep (se 1 (by rfl) ⟨3508082, by rfl⟩ : syracuseStep 4677443 = 7016165) B7016165
theorem B33251147 : Blo 1295966 33251147 := bstep (se 1 (by rfl) ⟨24938360, by rfl⟩ : syracuseStep 33251147 = 49876721) B49876721
theorem B2768735 : Blo 1295966 2768735 := bstep (se 1 (by rfl) ⟨2076551, by rfl⟩ : syracuseStep 2768735 = 4153103) B4153103
theorem B5611373 : Blo 1295966 5611373 := bstep (se 3 (by rfl) ⟨1052132, by rfl⟩ : syracuseStep 5611373 = 2104265) B2104265
theorem B1753015 : Blo 1295966 1753015 := bstep (se 1 (by rfl) ⟨1314761, by rfl⟩ : syracuseStep 1753015 = 2629523) B2629523
theorem B1458139 : Blo 1295966 1458139 := bstep (se 1 (by rfl) ⟨1093604, by rfl⟩ : syracuseStep 1458139 = 2187209) B2187209
theorem B7012403 : Blo 1295966 7012403 := bstep (se 1 (by rfl) ⟨5259302, by rfl⟩ : syracuseStep 7012403 = 10518605) B10518605
theorem B5537963 : Blo 1295966 5537963 := bstep (se 1 (by rfl) ⟨4153472, by rfl⟩ : syracuseStep 5537963 = 8306945) B8306945
theorem B6234283 : Blo 1295966 6234283 := bstep (se 1 (by rfl) ⟨4675712, by rfl⟩ : syracuseStep 6234283 = 9351425) B9351425
theorem B9978065 : Blo 1295966 9978065 := bstep (se 2 (by rfl) ⟨3741774, by rfl⟩ : syracuseStep 9978065 = 7483549) B7483549
theorem B1458463 : Blo 1295966 1458463 := bstep (se 1 (by rfl) ⟨1093847, by rfl⟩ : syracuseStep 1458463 = 2187695) B2187695
theorem B5996891 : Blo 1295966 5996891 := bstep (se 1 (by rfl) ⟨4497668, by rfl⟩ : syracuseStep 5996891 = 8995337) B8995337
theorem B2916719 : Blo 1295966 2916719 := bstep (se 1 (by rfl) ⟨2187539, by rfl⟩ : syracuseStep 2916719 = 4375079) B4375079
theorem B2916791 : Blo 1295966 2916791 := bstep (se 1 (by rfl) ⟨2187593, by rfl⟩ : syracuseStep 2916791 = 4375187) B4375187
theorem B3285431 : Blo 1295966 3285431 := bstep (se 1 (by rfl) ⟨2464073, by rfl⟩ : syracuseStep 3285431 = 4928147) B4928147
theorem B15770123 : Blo 1295966 15770123 := bstep (se 1 (by rfl) ⟨11827592, by rfl⟩ : syracuseStep 15770123 = 23655185) B23655185
theorem B1458751 : Blo 1295966 1458751 := bstep (se 1 (by rfl) ⟨1094063, by rfl⟩ : syracuseStep 1458751 = 2188127) B2188127
theorem B2916935 : Blo 1295966 2916935 := bstep (se 1 (by rfl) ⟨2187701, by rfl⟩ : syracuseStep 2916935 = 4375403) B4375403
theorem B2916971 : Blo 1295966 2916971 := bstep (se 1 (by rfl) ⟨2187728, by rfl⟩ : syracuseStep 2916971 = 4375457) B4375457
theorem B6234745 : Blo 1295966 6234745 := bstep (se 2 (by rfl) ⟨2338029, by rfl⟩ : syracuseStep 6234745 = 4676059) B4676059
theorem B6562457 : Blo 1295966 6562457 := bstep (se 2 (by rfl) ⟨2460921, by rfl⟩ : syracuseStep 6562457 = 4921843) B4921843
theorem B6570719 : Blo 1295966 6570719 := bstep (se 1 (by rfl) ⟨4928039, by rfl⟩ : syracuseStep 6570719 = 9856079) B9856079
theorem B1385371 : Blo 1295966 1385371 := bstep (se 1 (by rfl) ⟨1039028, by rfl⟩ : syracuseStep 1385371 = 2078057) B2078057
theorem B2917367 : Blo 1295966 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B6317047 : Blo 1295966 6317047 := bstep (se 1 (by rfl) ⟨4737785, by rfl⟩ : syracuseStep 6317047 = 9475571) B9475571
theorem B28435627 : Blo 1295966 28435627 := bstep (se 1 (by rfl) ⟨21326720, by rfl⟩ : syracuseStep 28435627 = 42653441) B42653441
theorem B2917727 : Blo 1295966 2917727 := bstep (se 1 (by rfl) ⟨2188295, by rfl⟩ : syracuseStep 2917727 = 4376591) B4376591
theorem B2188667 : Blo 1295966 2188667 := bstep (se 1 (by rfl) ⟨1641500, by rfl⟩ : syracuseStep 2188667 = 3283001) B3283001
theorem B1459579 : Blo 1295966 1459579 := bstep (se 1 (by rfl) ⟨1094684, by rfl⟩ : syracuseStep 1459579 = 2189369) B2189369
theorem B4375997 : Blo 1295966 4375997 := bstep (se 3 (by rfl) ⟨820499, by rfl⟩ : syracuseStep 4375997 = 1640999) B1640999
theorem B5539261 : Blo 1295966 5539261 := bstep (se 3 (by rfl) ⟨1038611, by rfl⟩ : syracuseStep 5539261 = 2077223) B2077223
theorem B2770375 : Blo 1295966 2770375 := bstep (se 1 (by rfl) ⟨2077781, by rfl⟩ : syracuseStep 2770375 = 4155563) B4155563
theorem B6235805 : Blo 1295966 6235805 := bstep (se 3 (by rfl) ⟨1169213, by rfl⟩ : syracuseStep 6235805 = 2338427) B2338427
theorem B1296095 : Blo 1295966 1296095 := bstep (se 1 (by rfl) ⟨972071, by rfl⟩ : syracuseStep 1296095 = 1944143) B1944143
theorem B2918123 : Blo 1295966 2918123 := bstep (se 1 (by rfl) ⟨2188592, by rfl⟩ : syracuseStep 2918123 = 4377185) B4377185
theorem B116844281 : Blo 1295966 116844281 := bstep (se 2 (by rfl) ⟨43816605, by rfl⟩ : syracuseStep 116844281 = 87633211) B87633211
theorem B1296175 : Blo 1295966 1296175 := bstep (se 1 (by rfl) ⟨972131, by rfl⟩ : syracuseStep 1296175 = 1944263) B1944263
theorem B4376375 : Blo 1295966 4376375 := bstep (se 1 (by rfl) ⟨3282281, by rfl⟩ : syracuseStep 4376375 = 6564563) B6564563
theorem B1460047 : Blo 1295966 1460047 := bstep (se 1 (by rfl) ⟨1095035, by rfl⟩ : syracuseStep 1460047 = 2190071) B2190071
theorem B2918249 : Blo 1295966 2918249 := bstep (se 2 (by rfl) ⟨1094343, by rfl⟩ : syracuseStep 2918249 = 2188687) B2188687
theorem B1296283 : Blo 1295966 1296283 := bstep (se 1 (by rfl) ⟨972212, by rfl⟩ : syracuseStep 1296283 = 1944425) B1944425
theorem B1296335 : Blo 1295966 1296335 := bstep (se 1 (by rfl) ⟨972251, by rfl⟩ : syracuseStep 1296335 = 1944503) B1944503
theorem B2770895 : Blo 1295966 2770895 := bstep (se 1 (by rfl) ⟨2078171, by rfl⟩ : syracuseStep 2770895 = 4156343) B4156343
theorem B1296359 : Blo 1295966 1296359 := bstep (se 1 (by rfl) ⟨972269, by rfl⟩ : syracuseStep 1296359 = 1944539) B1944539
theorem B4433953 : Blo 1295966 4433953 := bstep (se 2 (by rfl) ⟨1662732, by rfl⟩ : syracuseStep 4433953 = 3325465) B3325465
theorem B4376861 : Blo 1295966 4376861 := bstep (se 3 (by rfl) ⟨820661, by rfl⟩ : syracuseStep 4376861 = 1641323) B1641323
theorem B4155677 : Blo 1295966 4155677 := bstep (se 3 (by rfl) ⟨779189, by rfl⟩ : syracuseStep 4155677 = 1558379) B1558379
theorem B1296671 : Blo 1295966 1296671 := bstep (se 1 (by rfl) ⟨972503, by rfl⟩ : syracuseStep 1296671 = 1945007) B1945007
theorem B1845595 : Blo 1295966 1845595 := bstep (se 1 (by rfl) ⟨1384196, by rfl⟩ : syracuseStep 1845595 = 2768393) B2768393
theorem B1296731 : Blo 1295966 1296731 := bstep (se 1 (by rfl) ⟨972548, by rfl⟩ : syracuseStep 1296731 = 1945097) B1945097
theorem B2189659 : Blo 1295966 2189659 := bstep (se 1 (by rfl) ⟨1642244, by rfl⟩ : syracuseStep 2189659 = 3284489) B3284489
theorem B1296751 : Blo 1295966 1296751 := bstep (se 1 (by rfl) ⟨972563, by rfl⟩ : syracuseStep 1296751 = 1945127) B1945127
theorem B1640827 : Blo 1295966 1640827 := bstep (se 1 (by rfl) ⟨1230620, by rfl⟩ : syracuseStep 1640827 = 2461241) B2461241
theorem B6564239 : Blo 1295966 6564239 := bstep (se 1 (by rfl) ⟨4923179, by rfl⟩ : syracuseStep 6564239 = 9846359) B9846359
theorem B1943975 : Blo 1295966 1943975 := bstep (se 1 (by rfl) ⟨1457981, by rfl⟩ : syracuseStep 1943975 = 2915963) B2915963
theorem B1296807 : Blo 1295966 1296807 := bstep (se 1 (by rfl) ⟨972605, by rfl⟩ : syracuseStep 1296807 = 1945211) B1945211
theorem B5261735 : Blo 1295966 5261735 := bstep (se 1 (by rfl) ⟨3946301, by rfl⟩ : syracuseStep 5261735 = 7892603) B7892603
theorem B2771425 : Blo 1295966 2771425 := bstep (se 2 (by rfl) ⟨1039284, by rfl⟩ : syracuseStep 2771425 = 2078569) B2078569
theorem B5540339 : Blo 1295966 5540339 := bstep (se 1 (by rfl) ⟨4155254, by rfl⟩ : syracuseStep 5540339 = 8310509) B8310509
theorem B1944059 : Blo 1295966 1944059 := bstep (se 1 (by rfl) ⟨1458044, by rfl⟩ : syracuseStep 1944059 = 2916089) B2916089
theorem B1296891 : Blo 1295966 1296891 := bstep (se 1 (by rfl) ⟨972668, by rfl⟩ : syracuseStep 1296891 = 1945337) B1945337
theorem B1845823 : Blo 1295966 1845823 := bstep (se 1 (by rfl) ⟨1384367, by rfl⟩ : syracuseStep 1845823 = 2768735) B2768735
theorem B1296959 : Blo 1295966 1296959 := bstep (se 1 (by rfl) ⟨972719, by rfl⟩ : syracuseStep 1296959 = 1945439) B1945439
theorem B1296967 : Blo 1295966 1296967 := bstep (se 1 (by rfl) ⟨972725, by rfl⟩ : syracuseStep 1296967 = 1945451) B1945451
theorem B2337353 : Blo 1295966 2337353 := bstep (se 2 (by rfl) ⟨876507, by rfl⟩ : syracuseStep 2337353 = 1753015) B1753015
theorem B5261897 : Blo 1295966 5261897 := bstep (se 2 (by rfl) ⟨1973211, by rfl⟩ : syracuseStep 5261897 = 3946423) B3946423
theorem B1641055 : Blo 1295966 1641055 := bstep (se 1 (by rfl) ⟨1230791, by rfl⟩ : syracuseStep 1641055 = 2461583) B2461583
theorem B1944185 : Blo 1295966 1944185 := bstep (se 2 (by rfl) ⟨729069, by rfl⟩ : syracuseStep 1944185 = 1458139) B1458139
theorem B5540491 : Blo 1295966 5540491 := bstep (se 1 (by rfl) ⟨4155368, by rfl⟩ : syracuseStep 5540491 = 8310737) B8310737
theorem B1944239 : Blo 1295966 1944239 := bstep (se 1 (by rfl) ⟨1458179, by rfl⟩ : syracuseStep 1944239 = 2916359) B2916359
theorem B2919095 : Blo 1295966 2919095 := bstep (se 1 (by rfl) ⟨2189321, by rfl⟩ : syracuseStep 2919095 = 4378643) B4378643
theorem B1944287 : Blo 1295966 1944287 := bstep (se 1 (by rfl) ⟨1458215, by rfl⟩ : syracuseStep 1944287 = 2916431) B2916431
theorem B1403615 : Blo 1295966 1403615 := bstep (se 1 (by rfl) ⟨1052711, by rfl⟩ : syracuseStep 1403615 = 2105423) B2105423
theorem B1297119 : Blo 1295966 1297119 := bstep (se 1 (by rfl) ⟨972839, by rfl⟩ : syracuseStep 1297119 = 1945679) B1945679
theorem B20253473 : Blo 1295966 20253473 := bstep (se 2 (by rfl) ⟨7595052, by rfl⟩ : syracuseStep 20253473 = 15190105) B15190105
theorem B1297199 : Blo 1295966 1297199 := bstep (se 1 (by rfl) ⟨972899, by rfl⟩ : syracuseStep 1297199 = 1945799) B1945799
theorem B2919311 : Blo 1295966 2919311 := bstep (se 1 (by rfl) ⟨2189483, by rfl⟩ : syracuseStep 2919311 = 4378967) B4378967
theorem B1297307 : Blo 1295966 1297307 := bstep (se 1 (by rfl) ⟨972980, by rfl⟩ : syracuseStep 1297307 = 1945961) B1945961
theorem B1297359 : Blo 1295966 1297359 := bstep (se 1 (by rfl) ⟨973019, by rfl⟩ : syracuseStep 1297359 = 1946039) B1946039
theorem B1944551 : Blo 1295966 1944551 := bstep (se 1 (by rfl) ⟨1458413, by rfl⟩ : syracuseStep 1944551 = 2916827) B2916827
theorem B1297383 : Blo 1295966 1297383 := bstep (se 1 (by rfl) ⟨973037, by rfl⟩ : syracuseStep 1297383 = 1946075) B1946075
theorem B4213883 : Blo 1295966 4213883 := bstep (se 1 (by rfl) ⟨3160412, by rfl⟩ : syracuseStep 4213883 = 6320825) B6320825
theorem B2772091 : Blo 1295966 2772091 := bstep (se 1 (by rfl) ⟨2079068, by rfl⟩ : syracuseStep 2772091 = 4158137) B4158137
theorem B11078795 : Blo 1295966 11078795 := bstep (se 1 (by rfl) ⟨8309096, by rfl⟩ : syracuseStep 11078795 = 16618193) B16618193
theorem B68275379 : Blo 1295966 68275379 := bstep (se 1 (by rfl) ⟨51206534, by rfl⟩ : syracuseStep 68275379 = 102413069) B102413069
theorem B1944809 : Blo 1295966 1944809 := bstep (se 2 (by rfl) ⟨729303, by rfl⟩ : syracuseStep 1944809 = 1458607) B1458607
theorem B1944863 : Blo 1295966 1944863 := bstep (se 1 (by rfl) ⟨1458647, by rfl⟩ : syracuseStep 1944863 = 2917295) B2917295
theorem B4377887 : Blo 1295966 4377887 := bstep (se 1 (by rfl) ⟨3283415, by rfl⟩ : syracuseStep 4377887 = 6566831) B6566831
theorem B1297695 : Blo 1295966 1297695 := bstep (se 1 (by rfl) ⟨973271, by rfl⟩ : syracuseStep 1297695 = 1946543) B1946543
theorem B1297755 : Blo 1295966 1297755 := bstep (se 1 (by rfl) ⟨973316, by rfl⟩ : syracuseStep 1297755 = 1946633) B1946633
theorem B1297775 : Blo 1295966 1297775 := bstep (se 1 (by rfl) ⟨973331, by rfl⟩ : syracuseStep 1297775 = 1946663) B1946663
theorem B17075585 : Blo 1295966 17075585 := bstep (se 2 (by rfl) ⟨6403344, by rfl⟩ : syracuseStep 17075585 = 12806689) B12806689
theorem B1297831 : Blo 1295966 1297831 := bstep (se 1 (by rfl) ⟨973373, by rfl⟩ : syracuseStep 1297831 = 1946747) B1946747
theorem B1945031 : Blo 1295966 1945031 := bstep (se 1 (by rfl) ⟨1458773, by rfl⟩ : syracuseStep 1945031 = 2917547) B2917547
theorem B23662043 : Blo 1295966 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B1297915 : Blo 1295966 1297915 := bstep (se 1 (by rfl) ⟨973436, by rfl⟩ : syracuseStep 1297915 = 1946873) B1946873
theorem B2461279 : Blo 1295966 2461279 := bstep (se 1 (by rfl) ⟨1845959, by rfl⟩ : syracuseStep 2461279 = 3691919) B3691919
theorem B2920031 : Blo 1295966 2920031 := bstep (se 1 (by rfl) ⟨2190023, by rfl⟩ : syracuseStep 2920031 = 4380047) B4380047
theorem B3280571 : Blo 1295966 3280571 := bstep (se 1 (by rfl) ⟨2460428, by rfl⟩ : syracuseStep 3280571 = 4920857) B4920857
theorem B5918417 : Blo 1295966 5918417 := bstep (se 2 (by rfl) ⟨2219406, by rfl⟩ : syracuseStep 5918417 = 4438813) B4438813
theorem B1945385 : Blo 1295966 1945385 := bstep (se 2 (by rfl) ⟨729519, by rfl⟩ : syracuseStep 1945385 = 1459039) B1459039
theorem B1847081 : Blo 1295966 1847081 := bstep (se 2 (by rfl) ⟨692655, by rfl⟩ : syracuseStep 1847081 = 1385311) B1385311
theorem B1945391 : Blo 1295966 1945391 := bstep (se 1 (by rfl) ⟨1459043, by rfl⟩ : syracuseStep 1945391 = 2918087) B2918087
theorem B3116855 : Blo 1295966 3116855 := bstep (se 1 (by rfl) ⟨2337641, by rfl⟩ : syracuseStep 3116855 = 4675283) B4675283
theorem B1642295 : Blo 1295966 1642295 := bstep (se 1 (by rfl) ⟨1231721, by rfl⟩ : syracuseStep 1642295 = 2463443) B2463443
theorem B2920247 : Blo 1295966 2920247 := bstep (se 1 (by rfl) ⟨2190185, by rfl⟩ : syracuseStep 2920247 = 4380371) B4380371
theorem B1642447 : Blo 1295966 1642447 := bstep (se 1 (by rfl) ⟨1231835, by rfl⟩ : syracuseStep 1642447 = 2463671) B2463671
theorem B3371033 : Blo 1295966 3371033 := bstep (se 2 (by rfl) ⟨1264137, by rfl⟩ : syracuseStep 3371033 = 2528275) B2528275
theorem B3281107 : Blo 1295966 3281107 := bstep (se 1 (by rfl) ⟨2460830, by rfl⟩ : syracuseStep 3281107 = 4921661) B4921661
theorem B1945865 : Blo 1295966 1945865 := bstep (se 2 (by rfl) ⟨729699, by rfl⟩ : syracuseStep 1945865 = 1459399) B1459399
theorem B48648509 : Blo 1295966 48648509 := bstep (se 3 (by rfl) ⟨9121595, by rfl⟩ : syracuseStep 48648509 = 18243191) B18243191
theorem B3690859 : Blo 1295966 3690859 := bstep (se 1 (by rfl) ⟨2768144, by rfl⟩ : syracuseStep 3690859 = 5536289) B5536289
theorem B2806123 : Blo 1295966 2806123 := bstep (se 1 (by rfl) ⟨2104592, by rfl⟩ : syracuseStep 2806123 = 4209185) B4209185
theorem B1945967 : Blo 1295966 1945967 := bstep (se 1 (by rfl) ⟨1459475, by rfl⟩ : syracuseStep 1945967 = 2918951) B2918951
theorem B1847719 : Blo 1295966 1847719 := bstep (se 1 (by rfl) ⟨1385789, by rfl⟩ : syracuseStep 1847719 = 2771579) B2771579
theorem B6566345 : Blo 1295966 6566345 := bstep (se 2 (by rfl) ⟨2462379, by rfl⟩ : syracuseStep 6566345 = 4924759) B4924759
theorem B35508725 : Blo 1295966 35508725 := bstep (se 5 (by rfl) ⟨1664471, by rfl⟩ : syracuseStep 35508725 = 3328943) B3328943
theorem B37892657 : Blo 1295966 37892657 := bstep (se 2 (by rfl) ⟨14209746, by rfl⟩ : syracuseStep 37892657 = 28419493) B28419493
theorem B1946183 : Blo 1295966 1946183 := bstep (se 1 (by rfl) ⟨1459637, by rfl⟩ : syracuseStep 1946183 = 2919275) B2919275
theorem B1946219 : Blo 1295966 1946219 := bstep (se 1 (by rfl) ⟨1459664, by rfl⟩ : syracuseStep 1946219 = 2919329) B2919329
theorem B1946447 : Blo 1295966 1946447 := bstep (se 1 (by rfl) ⟨1459835, by rfl⟩ : syracuseStep 1946447 = 2919671) B2919671
theorem B3282059 : Blo 1295966 3282059 := bstep (se 1 (by rfl) ⟨2461544, by rfl⟩ : syracuseStep 3282059 = 4923089) B4923089
theorem B3118295 : Blo 1295966 3118295 := bstep (se 1 (by rfl) ⟨2338721, by rfl⟩ : syracuseStep 3118295 = 4677443) B4677443
theorem B1946843 : Blo 1295966 1946843 := bstep (se 1 (by rfl) ⟨1460132, by rfl⟩ : syracuseStep 1946843 = 2920265) B2920265
theorem B3740915 : Blo 1295966 3740915 := bstep (se 1 (by rfl) ⟨2805686, by rfl⟩ : syracuseStep 3740915 = 5611373) B5611373
theorem B6567155 : Blo 1295966 6567155 := bstep (se 1 (by rfl) ⟨4925366, by rfl⟩ : syracuseStep 6567155 = 9850733) B9850733
theorem B6231401 : Blo 1295966 6231401 := bstep (se 2 (by rfl) ⟨2336775, by rfl⟩ : syracuseStep 6231401 = 4673551) B4673551
theorem B10261997 : Blo 1295966 10261997 := bstep (se 3 (by rfl) ⟨1924124, by rfl⟩ : syracuseStep 10261997 = 3848249) B3848249
theorem B14013989 : Blo 1295966 14013989 := bstep (se 4 (by rfl) ⟨1313811, by rfl⟩ : syracuseStep 14013989 = 2627623) B2627623
theorem B3282515 : Blo 1295966 3282515 := bstep (se 1 (by rfl) ⟨2461886, by rfl⟩ : syracuseStep 3282515 = 4923773) B4923773
theorem B4380317 : Blo 1295966 4380317 := bstep (se 3 (by rfl) ⟨821309, by rfl⟩ : syracuseStep 4380317 = 1642619) B1642619
theorem B9353015 : Blo 1295966 9353015 := bstep (se 1 (by rfl) ⟨7014761, by rfl⟩ : syracuseStep 9353015 = 14029523) B14029523
theorem B4921175 : Blo 1295966 4921175 := bstep (se 1 (by rfl) ⟨3690881, by rfl⟩ : syracuseStep 4921175 = 7381763) B7381763
theorem B11081771 : Blo 1295966 11081771 := bstep (se 1 (by rfl) ⟨8311328, by rfl⟩ : syracuseStep 11081771 = 16622657) B16622657
theorem B44890157 : Blo 1295966 44890157 := bstep (se 3 (by rfl) ⟨8416904, by rfl⟩ : syracuseStep 44890157 = 16833809) B16833809
theorem B11073671 : Blo 1295966 11073671 := bstep (se 1 (by rfl) ⟨8305253, by rfl⟩ : syracuseStep 11073671 = 16610507) B16610507
theorem B15186167 : Blo 1295966 15186167 := bstep (se 1 (by rfl) ⟨11389625, by rfl⟩ : syracuseStep 15186167 = 22779251) B22779251
theorem B3283375 : Blo 1295966 3283375 := bstep (se 1 (by rfl) ⟨2462531, by rfl⟩ : syracuseStep 3283375 = 4925063) B4925063
theorem B9845387 : Blo 1295966 9845387 := bstep (se 1 (by rfl) ⟨7384040, by rfl⟩ : syracuseStep 9845387 = 14768081) B14768081
theorem B3283679 : Blo 1295966 3283679 := bstep (se 1 (by rfl) ⟨2462759, by rfl⟩ : syracuseStep 3283679 = 4925519) B4925519
theorem B14015375 : Blo 1295966 14015375 := bstep (se 1 (by rfl) ⟨10511531, by rfl⟩ : syracuseStep 14015375 = 21023063) B21023063
theorem B3693707 : Blo 1295966 3693707 := bstep (se 1 (by rfl) ⟨2770280, by rfl⟩ : syracuseStep 3693707 = 5540561) B5540561
theorem B6569099 : Blo 1295966 6569099 := bstep (se 1 (by rfl) ⟨4926824, by rfl⟩ : syracuseStep 6569099 = 9853649) B9853649
theorem B8871133 : Blo 1295966 8871133 := bstep (se 3 (by rfl) ⟨1663337, by rfl⟩ : syracuseStep 8871133 = 3326675) B3326675
theorem B3505531 : Blo 1295966 3505531 := bstep (se 1 (by rfl) ⟨2629148, by rfl⟩ : syracuseStep 3505531 = 5258297) B5258297
theorem B3284347 : Blo 1295966 3284347 := bstep (se 1 (by rfl) ⟨2463260, by rfl⟩ : syracuseStep 3284347 = 4926521) B4926521
theorem B6561161 : Blo 1295966 6561161 := bstep (se 2 (by rfl) ⟨2460435, by rfl⟩ : syracuseStep 6561161 = 4920871) B4920871
theorem B2956807 : Blo 1295966 2956807 := bstep (se 1 (by rfl) ⟨2217605, by rfl⟩ : syracuseStep 2956807 = 4435211) B4435211
theorem B8314427 : Blo 1295966 8314427 := bstep (se 1 (by rfl) ⟨6235820, by rfl⟩ : syracuseStep 8314427 = 12471641) B12471641
theorem B2916143 : Blo 1295966 2916143 := bstep (se 1 (by rfl) ⟨2187107, by rfl⟩ : syracuseStep 2916143 = 4374215) B4374215
theorem B5914415 : Blo 1295966 5914415 := bstep (se 1 (by rfl) ⟨4435811, by rfl⟩ : syracuseStep 5914415 = 8871623) B8871623
theorem B3284783 : Blo 1295966 3284783 := bstep (se 1 (by rfl) ⟨2463587, by rfl⟩ : syracuseStep 3284783 = 4927175) B4927175
theorem B9355115 : Blo 1295966 9355115 := bstep (se 1 (by rfl) ⟨7016336, by rfl⟩ : syracuseStep 9355115 = 14032673) B14032673
theorem B22167431 : Blo 1295966 22167431 := bstep (se 1 (by rfl) ⟨16625573, by rfl⟩ : syracuseStep 22167431 = 33251147) B33251147
theorem B15769637 : Blo 1295966 15769637 := bstep (se 4 (by rfl) ⟨1478403, by rfl⟩ : syracuseStep 15769637 = 2956807) B2956807
theorem B6652043 : Blo 1295966 6652043 := bstep (se 1 (by rfl) ⟨4989032, by rfl⟩ : syracuseStep 6652043 = 9978065) B9978065
theorem B32432339 : Blo 1295966 32432339 := bstep (se 1 (by rfl) ⟨24324254, by rfl⟩ : syracuseStep 32432339 = 48648509) B48648509
theorem B3997927 : Blo 1295966 3997927 := bstep (se 1 (by rfl) ⟨2998445, by rfl⟩ : syracuseStep 3997927 = 5996891) B5996891
theorem B4374809 : Blo 1295966 4374809 := bstep (se 2 (by rfl) ⟨1640553, by rfl⟩ : syracuseStep 4374809 = 3281107) B3281107
theorem B4374971 : Blo 1295966 4374971 := bstep (se 1 (by rfl) ⟨3281228, by rfl⟩ : syracuseStep 4374971 = 6562457) B6562457
theorem B2187769 : Blo 1295966 2187769 := bstep (se 2 (by rfl) ⟨820413, by rfl⟩ : syracuseStep 2187769 = 1640827) B1640827
theorem B8315453 : Blo 1295966 8315453 := bstep (se 3 (by rfl) ⟨1559147, by rfl⟩ : syracuseStep 8315453 = 3118295) B3118295
theorem B3695233 : Blo 1295966 3695233 := bstep (se 2 (by rfl) ⟨1385712, by rfl⟩ : syracuseStep 3695233 = 2771425) B2771425
theorem B2188039 : Blo 1295966 2188039 := bstep (se 1 (by rfl) ⟨1641029, by rfl⟩ : syracuseStep 2188039 = 3282059) B3282059
theorem B2188073 : Blo 1295966 2188073 := bstep (se 2 (by rfl) ⟨820527, by rfl⟩ : syracuseStep 2188073 = 1641055) B1641055
theorem B4154267 : Blo 1295966 4154267 := bstep (se 1 (by rfl) ⟨3115700, by rfl⟩ : syracuseStep 4154267 = 6231401) B6231401
theorem B1459111 : Blo 1295966 1459111 := bstep (se 1 (by rfl) ⟨1094333, by rfl⟩ : syracuseStep 1459111 = 2188667) B2188667
theorem B2917331 : Blo 1295966 2917331 := bstep (se 1 (by rfl) ⟨2187998, by rfl⟩ : syracuseStep 2917331 = 4375997) B4375997
theorem B6841331 : Blo 1295966 6841331 := bstep (se 1 (by rfl) ⟨5130998, by rfl⟩ : syracuseStep 6841331 = 10261997) B10261997
theorem B2188343 : Blo 1295966 2188343 := bstep (se 1 (by rfl) ⟨1641257, by rfl⟩ : syracuseStep 2188343 = 3282515) B3282515
theorem B2917583 : Blo 1295966 2917583 := bstep (se 1 (by rfl) ⟨2188187, by rfl⟩ : syracuseStep 2917583 = 4376375) B4376375
theorem B6235343 : Blo 1295966 6235343 := bstep (se 1 (by rfl) ⟨4676507, by rfl⟩ : syracuseStep 6235343 = 9353015) B9353015
theorem B7382447 : Blo 1295966 7382447 := bstep (se 1 (by rfl) ⟨5536835, by rfl⟩ : syracuseStep 7382447 = 11073671) B11073671
theorem B3696121 : Blo 1295966 3696121 := bstep (se 2 (by rfl) ⟨1386045, by rfl⟩ : syracuseStep 3696121 = 2772091) B2772091
theorem B2917907 : Blo 1295966 2917907 := bstep (se 1 (by rfl) ⟨2188430, by rfl⟩ : syracuseStep 2917907 = 4376861) B4376861
theorem B2770451 : Blo 1295966 2770451 := bstep (se 1 (by rfl) ⟨2077838, by rfl⟩ : syracuseStep 2770451 = 4155677) B4155677
theorem B37914169 : Blo 1295966 37914169 := bstep (se 2 (by rfl) ⟨14217813, by rfl⟩ : syracuseStep 37914169 = 28435627) B28435627
theorem B4376159 : Blo 1295966 4376159 := bstep (se 1 (by rfl) ⟨3282119, by rfl⟩ : syracuseStep 4376159 = 6564239) B6564239
theorem B1295983 : Blo 1295966 1295983 := bstep (se 1 (by rfl) ⟨971987, by rfl⟩ : syracuseStep 1295983 = 1943975) B1943975
theorem B3507823 : Blo 1295966 3507823 := bstep (se 1 (by rfl) ⟨2630867, by rfl⟩ : syracuseStep 3507823 = 5261735) B5261735
theorem B1296039 : Blo 1295966 1296039 := bstep (se 1 (by rfl) ⟨972029, by rfl⟩ : syracuseStep 1296039 = 1944059) B1944059
theorem B1558235 : Blo 1295966 1558235 := bstep (se 1 (by rfl) ⟨1168676, by rfl⟩ : syracuseStep 1558235 = 2337353) B2337353
theorem B3507931 : Blo 1295966 3507931 := bstep (se 1 (by rfl) ⟨2630948, by rfl⟩ : syracuseStep 3507931 = 5261897) B5261897
theorem B1296123 : Blo 1295966 1296123 := bstep (se 1 (by rfl) ⟨972092, by rfl⟩ : syracuseStep 1296123 = 1944185) B1944185
theorem B6563591 : Blo 1295966 6563591 := bstep (se 1 (by rfl) ⟨4922693, by rfl⟩ : syracuseStep 6563591 = 9845387) B9845387
theorem B1296159 : Blo 1295966 1296159 := bstep (se 1 (by rfl) ⟨972119, by rfl⟩ : syracuseStep 1296159 = 1944239) B1944239
theorem B1296191 : Blo 1295966 1296191 := bstep (se 1 (by rfl) ⟨972143, by rfl⟩ : syracuseStep 1296191 = 1944287) B1944287
theorem B2189119 : Blo 1295966 2189119 := bstep (se 1 (by rfl) ⟨1641839, by rfl⟩ : syracuseStep 2189119 = 3283679) B3283679
theorem B13502315 : Blo 1295966 13502315 := bstep (se 1 (by rfl) ⟨10126736, by rfl⟩ : syracuseStep 13502315 = 20253473) B20253473
theorem B1296367 : Blo 1295966 1296367 := bstep (se 1 (by rfl) ⟨972275, by rfl⟩ : syracuseStep 1296367 = 1944551) B1944551
theorem B4925549 : Blo 1295966 4925549 := bstep (se 3 (by rfl) ⟨923540, by rfl⟩ : syracuseStep 4925549 = 1847081) B1847081
theorem B45516919 : Blo 1295966 45516919 := bstep (se 1 (by rfl) ⟨34137689, by rfl⟩ : syracuseStep 45516919 = 68275379) B68275379
theorem B15771773 : Blo 1295966 15771773 := bstep (se 3 (by rfl) ⟨2957207, by rfl⟩ : syracuseStep 15771773 = 5914415) B5914415
theorem B1296539 : Blo 1295966 1296539 := bstep (se 1 (by rfl) ⟨972404, by rfl⟩ : syracuseStep 1296539 = 1944809) B1944809
theorem B1296575 : Blo 1295966 1296575 := bstep (se 1 (by rfl) ⟨972431, by rfl⟩ : syracuseStep 1296575 = 1944863) B1944863
theorem B2918591 : Blo 1295966 2918591 := bstep (se 1 (by rfl) ⟨2188943, by rfl⟩ : syracuseStep 2918591 = 4377887) B4377887
theorem B24946973 : Blo 1295966 24946973 := bstep (se 3 (by rfl) ⟨4677557, by rfl⟩ : syracuseStep 24946973 = 9355115) B9355115
theorem B1296687 : Blo 1295966 1296687 := bstep (se 1 (by rfl) ⟨972515, by rfl⟩ : syracuseStep 1296687 = 1945031) B1945031
theorem B1296923 : Blo 1295966 1296923 := bstep (se 1 (by rfl) ⟨972692, by rfl⟩ : syracuseStep 1296923 = 1945385) B1945385
theorem B1944095 : Blo 1295966 1944095 := bstep (se 1 (by rfl) ⟨1458071, by rfl⟩ : syracuseStep 1944095 = 2916143) B2916143
theorem B1296927 : Blo 1295966 1296927 := bstep (se 1 (by rfl) ⟨972695, by rfl⟩ : syracuseStep 1296927 = 1945391) B1945391
theorem B2189855 : Blo 1295966 2189855 := bstep (se 1 (by rfl) ⟨1642391, by rfl⟩ : syracuseStep 2189855 = 3284783) B3284783
theorem B2189929 : Blo 1295966 2189929 := bstep (se 2 (by rfl) ⟨821223, by rfl⟩ : syracuseStep 2189929 = 1642447) B1642447
theorem B2247355 : Blo 1295966 2247355 := bstep (se 1 (by rfl) ⟨1685516, by rfl⟩ : syracuseStep 2247355 = 3371033) B3371033
theorem B1297243 : Blo 1295966 1297243 := bstep (se 1 (by rfl) ⟨972932, by rfl⟩ : syracuseStep 1297243 = 1945865) B1945865
theorem B1944479 : Blo 1295966 1944479 := bstep (se 1 (by rfl) ⟨1458359, by rfl⟩ : syracuseStep 1944479 = 2916719) B2916719
theorem B1297311 : Blo 1295966 1297311 := bstep (se 1 (by rfl) ⟨972983, by rfl⟩ : syracuseStep 1297311 = 1945967) B1945967
theorem B1944527 : Blo 1295966 1944527 := bstep (se 1 (by rfl) ⟨1458395, by rfl⟩ : syracuseStep 1944527 = 2916791) B2916791
theorem B2190287 : Blo 1295966 2190287 := bstep (se 1 (by rfl) ⟨1642715, by rfl⟩ : syracuseStep 2190287 = 3285431) B3285431
theorem B4377563 : Blo 1295966 4377563 := bstep (se 1 (by rfl) ⟨3283172, by rfl⟩ : syracuseStep 4377563 = 6566345) B6566345
theorem B10513415 : Blo 1295966 10513415 := bstep (se 1 (by rfl) ⟨7885061, by rfl⟩ : syracuseStep 10513415 = 15770123) B15770123
theorem B1944617 : Blo 1295966 1944617 := bstep (se 2 (by rfl) ⟨729231, by rfl⟩ : syracuseStep 1944617 = 1458463) B1458463
theorem B1944623 : Blo 1295966 1944623 := bstep (se 1 (by rfl) ⟨1458467, by rfl⟩ : syracuseStep 1944623 = 2916935) B2916935
theorem B1297455 : Blo 1295966 1297455 := bstep (se 1 (by rfl) ⟨973091, by rfl⟩ : syracuseStep 1297455 = 1946183) B1946183
theorem B1944647 : Blo 1295966 1944647 := bstep (se 1 (by rfl) ⟨1458485, by rfl⟩ : syracuseStep 1944647 = 2916971) B2916971
theorem B1297479 : Blo 1295966 1297479 := bstep (se 1 (by rfl) ⟨973109, by rfl⟩ : syracuseStep 1297479 = 1946219) B1946219
theorem B2460793 : Blo 1295966 2460793 := bstep (se 2 (by rfl) ⟨922797, by rfl⟩ : syracuseStep 2460793 = 1845595) B1845595
theorem B2919545 : Blo 1295966 2919545 := bstep (se 2 (by rfl) ⟨1094829, by rfl⟩ : syracuseStep 2919545 = 2189659) B2189659
theorem B1297631 : Blo 1295966 1297631 := bstep (se 1 (by rfl) ⟨973223, by rfl⟩ : syracuseStep 1297631 = 1946447) B1946447
theorem B4377833 : Blo 1295966 4377833 := bstep (se 2 (by rfl) ⟨1641687, by rfl⟩ : syracuseStep 4377833 = 3283375) B3283375
theorem B1944911 : Blo 1295966 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B2461097 : Blo 1295966 2461097 := bstep (se 2 (by rfl) ⟨922911, by rfl⟩ : syracuseStep 2461097 = 1845823) B1845823
theorem B1945001 : Blo 1295966 1945001 := bstep (se 2 (by rfl) ⟨729375, by rfl⟩ : syracuseStep 1945001 = 1458751) B1458751
theorem B1297895 : Blo 1295966 1297895 := bstep (se 1 (by rfl) ⟨973421, by rfl⟩ : syracuseStep 1297895 = 1946843) B1946843
theorem B4378103 : Blo 1295966 4378103 := bstep (se 1 (by rfl) ⟨3283577, by rfl⟩ : syracuseStep 4378103 = 6567155) B6567155
theorem B1945151 : Blo 1295966 1945151 := bstep (se 1 (by rfl) ⟨1458863, by rfl⟩ : syracuseStep 1945151 = 2917727) B2917727
theorem B9342659 : Blo 1295966 9342659 := bstep (se 1 (by rfl) ⟨7006994, by rfl⟩ : syracuseStep 9342659 = 14013989) B14013989
theorem B4157203 : Blo 1295966 4157203 := bstep (se 1 (by rfl) ⟨3117902, by rfl⟩ : syracuseStep 4157203 = 6235805) B6235805
theorem B2920211 : Blo 1295966 2920211 := bstep (se 1 (by rfl) ⟨2190158, by rfl⟩ : syracuseStep 2920211 = 4380317) B4380317
theorem B1945415 : Blo 1295966 1945415 := bstep (se 1 (by rfl) ⟨1459061, by rfl⟩ : syracuseStep 1945415 = 2918123) B2918123
theorem B1847161 : Blo 1295966 1847161 := bstep (se 2 (by rfl) ⟨692685, by rfl⟩ : syracuseStep 1847161 = 1385371) B1385371
theorem B3280783 : Blo 1295966 3280783 := bstep (se 1 (by rfl) ⟨2460587, by rfl⟩ : syracuseStep 3280783 = 4921175) B4921175
theorem B1945499 : Blo 1295966 1945499 := bstep (se 1 (by rfl) ⟨1459124, by rfl⟩ : syracuseStep 1945499 = 2918249) B2918249
theorem B22171805 : Blo 1295966 22171805 := bstep (se 3 (by rfl) ⟨4157213, by rfl⟩ : syracuseStep 22171805 = 8314427) B8314427
theorem B1946063 : Blo 1295966 1946063 := bstep (se 1 (by rfl) ⟨1459547, by rfl⟩ : syracuseStep 1946063 = 2919095) B2919095
theorem B4674041 : Blo 1295966 4674041 := bstep (se 2 (by rfl) ⟨1752765, by rfl⟩ : syracuseStep 4674041 = 3505531) B3505531
theorem B1946105 : Blo 1295966 1946105 := bstep (se 2 (by rfl) ⟨729789, by rfl⟩ : syracuseStep 1946105 = 1459579) B1459579
theorem B4379129 : Blo 1295966 4379129 := bstep (se 2 (by rfl) ⟨1642173, by rfl⟩ : syracuseStep 4379129 = 3284347) B3284347
theorem B7385681 : Blo 1295966 7385681 := bstep (se 2 (by rfl) ⟨2769630, by rfl⟩ : syracuseStep 7385681 = 5539261) B5539261
theorem B9343583 : Blo 1295966 9343583 := bstep (se 1 (by rfl) ⟨7007687, by rfl⟩ : syracuseStep 9343583 = 14015375) B14015375
theorem B1946207 : Blo 1295966 1946207 := bstep (se 1 (by rfl) ⟨1459655, by rfl⟩ : syracuseStep 1946207 = 2919311) B2919311
theorem B7385863 : Blo 1295966 7385863 := bstep (se 1 (by rfl) ⟨5539397, by rfl⟩ : syracuseStep 7385863 = 11078795) B11078795
theorem B2462471 : Blo 1295966 2462471 := bstep (se 1 (by rfl) ⟨1846853, by rfl⟩ : syracuseStep 2462471 = 3693707) B3693707
theorem B4379399 : Blo 1295966 4379399 := bstep (se 1 (by rfl) ⟨3284549, by rfl⟩ : syracuseStep 4379399 = 6569099) B6569099
theorem B3281705 : Blo 1295966 3281705 := bstep (se 2 (by rfl) ⟨1230639, by rfl⟩ : syracuseStep 3281705 = 2461279) B2461279
theorem B4379453 : Blo 1295966 4379453 := bstep (se 3 (by rfl) ⟨821147, by rfl⟩ : syracuseStep 4379453 = 1642295) B1642295
theorem B11383723 : Blo 1295966 11383723 := bstep (se 1 (by rfl) ⟨8537792, by rfl⟩ : syracuseStep 11383723 = 17075585) B17075585
theorem B15774695 : Blo 1295966 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B1946687 : Blo 1295966 1946687 := bstep (se 1 (by rfl) ⟨1460015, by rfl⟩ : syracuseStep 1946687 = 2920031) B2920031
theorem B1946729 : Blo 1295966 1946729 := bstep (se 2 (by rfl) ⟨730023, by rfl⟩ : syracuseStep 1946729 = 1460047) B1460047
theorem B3945611 : Blo 1295966 3945611 := bstep (se 1 (by rfl) ⟨2959208, by rfl⟩ : syracuseStep 3945611 = 5918417) B5918417
theorem B2077903 : Blo 1295966 2077903 := bstep (se 1 (by rfl) ⟨1558427, by rfl⟩ : syracuseStep 2077903 = 3116855) B3116855
theorem B1946831 : Blo 1295966 1946831 := bstep (se 1 (by rfl) ⟨1460123, by rfl⟩ : syracuseStep 1946831 = 2920247) B2920247
theorem B33690917 : Blo 1295966 33690917 := bstep (se 4 (by rfl) ⟨3158523, by rfl⟩ : syracuseStep 33690917 = 6317047) B6317047
theorem B4674935 : Blo 1295966 4674935 := bstep (se 1 (by rfl) ⟨3506201, by rfl⟩ : syracuseStep 4674935 = 7012403) B7012403
theorem B5911937 : Blo 1295966 5911937 := bstep (se 2 (by rfl) ⟨2216976, by rfl⟩ : syracuseStep 5911937 = 4433953) B4433953
theorem B3691975 : Blo 1295966 3691975 := bstep (se 1 (by rfl) ⟨2768981, by rfl⟩ : syracuseStep 3691975 = 5537963) B5537963
theorem B119707085 : Blo 1295966 119707085 := bstep (se 3 (by rfl) ⟨22445078, by rfl⟩ : syracuseStep 119707085 = 44890157) B44890157
theorem B8312377 : Blo 1295966 8312377 := bstep (se 2 (by rfl) ⟨3117141, by rfl⟩ : syracuseStep 8312377 = 6234283) B6234283
theorem B23672483 : Blo 1295966 23672483 := bstep (se 1 (by rfl) ⟨17754362, by rfl⟩ : syracuseStep 23672483 = 35508725) B35508725
theorem B4921145 : Blo 1295966 4921145 := bstep (se 2 (by rfl) ⟨1845429, by rfl⟩ : syracuseStep 4921145 = 3690859) B3690859
theorem B3741497 : Blo 1295966 3741497 := bstep (se 2 (by rfl) ⟨1403061, by rfl⟩ : syracuseStep 3741497 = 2806123) B2806123
theorem B4380479 : Blo 1295966 4380479 := bstep (se 1 (by rfl) ⟨3285359, by rfl⟩ : syracuseStep 4380479 = 6570719) B6570719
theorem B2463625 : Blo 1295966 2463625 := bstep (se 2 (by rfl) ⟨923859, by rfl⟩ : syracuseStep 2463625 = 1847719) B1847719
theorem B9975773 : Blo 1295966 9975773 := bstep (se 3 (by rfl) ⟨1870457, by rfl⟩ : syracuseStep 9975773 = 3740915) B3740915
theorem B8312993 : Blo 1295966 8312993 := bstep (se 2 (by rfl) ⟨3117372, by rfl⟩ : syracuseStep 8312993 = 6234745) B6234745
theorem B7387321 : Blo 1295966 7387321 := bstep (se 2 (by rfl) ⟨2770245, by rfl⟩ : syracuseStep 7387321 = 5540491) B5540491
theorem B77896187 : Blo 1295966 77896187 := bstep (se 1 (by rfl) ⟨58422140, by rfl⟩ : syracuseStep 77896187 = 116844281) B116844281
theorem B7387847 : Blo 1295966 7387847 := bstep (se 1 (by rfl) ⟨5540885, by rfl⟩ : syracuseStep 7387847 = 11081771) B11081771
theorem B101047085 : Blo 1295966 101047085 := bstep (se 3 (by rfl) ⟨18946328, by rfl⟩ : syracuseStep 101047085 = 37892657) B37892657
theorem B10124111 : Blo 1295966 10124111 := bstep (se 1 (by rfl) ⟨7593083, by rfl⟩ : syracuseStep 10124111 = 15186167) B15186167
theorem B11828177 : Blo 1295966 11828177 := bstep (se 2 (by rfl) ⟨4435566, by rfl⟩ : syracuseStep 11828177 = 8871133) B8871133
theorem B3693559 : Blo 1295966 3693559 := bstep (se 1 (by rfl) ⟨2770169, by rfl⟩ : syracuseStep 3693559 = 5540339) B5540339
theorem B3742973 : Blo 1295966 3742973 := bstep (se 3 (by rfl) ⟨701807, by rfl⟩ : syracuseStep 3742973 = 1403615) B1403615
theorem B3693833 : Blo 1295966 3693833 := bstep (se 2 (by rfl) ⟨1385187, by rfl⟩ : syracuseStep 3693833 = 2770375) B2770375
theorem B2809255 : Blo 1295966 2809255 := bstep (se 1 (by rfl) ⟨2106941, by rfl⟩ : syracuseStep 2809255 = 4213883) B4213883
theorem B4374107 : Blo 1295966 4374107 := bstep (se 1 (by rfl) ⟨3280580, by rfl⟩ : syracuseStep 4374107 = 6561161) B6561161
theorem B2187047 : Blo 1295966 2187047 := bstep (se 1 (by rfl) ⟨1640285, by rfl⟩ : syracuseStep 2187047 = 3280571) B3280571
theorem B7389053 : Blo 1295966 7389053 := bstep (se 3 (by rfl) ⟨1385447, by rfl⟩ : syracuseStep 7389053 = 2770895) B2770895
theorem B14778287 : Blo 1295966 14778287 := bstep (se 1 (by rfl) ⟨11083715, by rfl⟩ : syracuseStep 14778287 = 22167431) B22167431
theorem B2916539 : Blo 1295966 2916539 := bstep (se 1 (by rfl) ⟨2187404, by rfl⟩ : syracuseStep 2916539 = 4374809) B4374809
theorem B2916647 : Blo 1295966 2916647 := bstep (se 1 (by rfl) ⟨2187485, by rfl⟩ : syracuseStep 2916647 = 4374971) B4374971
theorem B42058061 : Blo 1295966 42058061 := bstep (se 3 (by rfl) ⟨7885886, by rfl⟩ : syracuseStep 42058061 = 15771773) B15771773
theorem B4923787 : Blo 1295966 4923787 := bstep (se 1 (by rfl) ⟨3692840, by rfl⟩ : syracuseStep 4923787 = 7385681) B7385681
theorem B2187803 : Blo 1295966 2187803 := bstep (se 1 (by rfl) ⟨1640852, by rfl⟩ : syracuseStep 2187803 = 3281705) B3281705
theorem B1458715 : Blo 1295966 1458715 := bstep (se 1 (by rfl) ⟨1094036, by rfl⟩ : syracuseStep 1458715 = 2188073) B2188073
theorem B2917025 : Blo 1295966 2917025 := bstep (se 2 (by rfl) ⟨1093884, by rfl⟩ : syracuseStep 2917025 = 2187769) B2187769
theorem B1458895 : Blo 1295966 1458895 := bstep (se 1 (by rfl) ⟨1094171, by rfl⟩ : syracuseStep 1458895 = 2188343) B2188343
theorem B2630407 : Blo 1295966 2630407 := bstep (se 1 (by rfl) ⟨1972805, by rfl⟩ : syracuseStep 2630407 = 3945611) B3945611
theorem B3941291 : Blo 1295966 3941291 := bstep (se 1 (by rfl) ⟨2955968, by rfl⟩ : syracuseStep 3941291 = 5911937) B5911937
theorem B11985893 : Blo 1295966 11985893 := bstep (se 4 (by rfl) ⟨1123677, by rfl⟩ : syracuseStep 11985893 = 2247355) B2247355
theorem B2917385 : Blo 1295966 2917385 := bstep (se 2 (by rfl) ⟨1094019, by rfl⟩ : syracuseStep 2917385 = 2188039) B2188039
theorem B9847817 : Blo 1295966 9847817 := bstep (se 2 (by rfl) ⟨3692931, by rfl⟩ : syracuseStep 9847817 = 7385863) B7385863
theorem B2917439 : Blo 1295966 2917439 := bstep (se 1 (by rfl) ⟨2188079, by rfl⟩ : syracuseStep 2917439 = 4376159) B4376159
theorem B4375727 : Blo 1295966 4375727 := bstep (se 1 (by rfl) ⟨3281795, by rfl⟩ : syracuseStep 4375727 = 6563591) B6563591
theorem B4924745 : Blo 1295966 4924745 := bstep (se 2 (by rfl) ⟨1846779, by rfl⟩ : syracuseStep 4924745 = 3693559) B3693559
theorem B16631315 : Blo 1295966 16631315 := bstep (se 1 (by rfl) ⟨12473486, by rfl⟩ : syracuseStep 16631315 = 24946973) B24946973
theorem B2770537 : Blo 1295966 2770537 := bstep (se 2 (by rfl) ⟨1038951, by rfl⟩ : syracuseStep 2770537 = 2077903) B2077903
theorem B51930791 : Blo 1295966 51930791 := bstep (se 1 (by rfl) ⟨38948093, by rfl⟩ : syracuseStep 51930791 = 77896187) B77896187
theorem B1296063 : Blo 1295966 1296063 := bstep (se 1 (by rfl) ⟨972047, by rfl⟩ : syracuseStep 1296063 = 1944095) B1944095
theorem B1459903 : Blo 1295966 1459903 := bstep (se 1 (by rfl) ⟨1094927, by rfl⟩ : syracuseStep 1459903 = 2189855) B2189855
theorem B4925231 : Blo 1295966 4925231 := bstep (se 1 (by rfl) ⟨3693923, by rfl⟩ : syracuseStep 4925231 = 7387847) B7387847
theorem B24913757 : Blo 1295966 24913757 := bstep (se 3 (by rfl) ⟨4671329, by rfl⟩ : syracuseStep 24913757 = 9342659) B9342659
theorem B67364723 : Blo 1295966 67364723 := bstep (se 1 (by rfl) ⟨50523542, by rfl⟩ : syracuseStep 67364723 = 101047085) B101047085
theorem B3745673 : Blo 1295966 3745673 := bstep (se 2 (by rfl) ⟨1404627, by rfl⟩ : syracuseStep 3745673 = 2809255) B2809255
theorem B4155293 : Blo 1295966 4155293 := bstep (se 3 (by rfl) ⟨779117, by rfl⟩ : syracuseStep 4155293 = 1558235) B1558235
theorem B1296319 : Blo 1295966 1296319 := bstep (se 1 (by rfl) ⟨972239, by rfl⟩ : syracuseStep 1296319 = 1944479) B1944479
theorem B1296351 : Blo 1295966 1296351 := bstep (se 1 (by rfl) ⟨972263, by rfl⟩ : syracuseStep 1296351 = 1944527) B1944527
theorem B1460191 : Blo 1295966 1460191 := bstep (se 1 (by rfl) ⟨1095143, by rfl⟩ : syracuseStep 1460191 = 2190287) B2190287
theorem B2918375 : Blo 1295966 2918375 := bstep (se 1 (by rfl) ⟨2188781, by rfl⟩ : syracuseStep 2918375 = 4377563) B4377563
theorem B1296411 : Blo 1295966 1296411 := bstep (se 1 (by rfl) ⟨972308, by rfl⟩ : syracuseStep 1296411 = 1944617) B1944617
theorem B1296415 : Blo 1295966 1296415 := bstep (se 1 (by rfl) ⟨972311, by rfl⟩ : syracuseStep 1296415 = 1944623) B1944623
theorem B1296431 : Blo 1295966 1296431 := bstep (se 1 (by rfl) ⟨972323, by rfl⟩ : syracuseStep 1296431 = 1944647) B1944647
theorem B2918555 : Blo 1295966 2918555 := bstep (se 1 (by rfl) ⟨2188916, by rfl⟩ : syracuseStep 2918555 = 4377833) B4377833
theorem B1296607 : Blo 1295966 1296607 := bstep (se 1 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 1296607 = 1944911) B1944911
theorem B60713189 : Blo 1295966 60713189 := bstep (se 4 (by rfl) ⟨5691861, by rfl⟩ : syracuseStep 60713189 = 11383723) B11383723
theorem B1640731 : Blo 1295966 1640731 := bstep (se 1 (by rfl) ⟨1230548, by rfl⟩ : syracuseStep 1640731 = 2461097) B2461097
theorem B1296667 : Blo 1295966 1296667 := bstep (se 1 (by rfl) ⟨972500, by rfl⟩ : syracuseStep 1296667 = 1945001) B1945001
theorem B2918735 : Blo 1295966 2918735 := bstep (se 1 (by rfl) ⟨2189051, by rfl⟩ : syracuseStep 2918735 = 4378103) B4378103
theorem B1296767 : Blo 1295966 1296767 := bstep (se 1 (by rfl) ⟨972575, by rfl⟩ : syracuseStep 1296767 = 1945151) B1945151
theorem B11078045 : Blo 1295966 11078045 := bstep (se 3 (by rfl) ⟨2077133, by rfl⟩ : syracuseStep 11078045 = 4154267) B4154267
theorem B2918825 : Blo 1295966 2918825 := bstep (se 2 (by rfl) ⟨1094559, by rfl⟩ : syracuseStep 2918825 = 2189119) B2189119
theorem B1296943 : Blo 1295966 1296943 := bstep (se 1 (by rfl) ⟨972707, by rfl⟩ : syracuseStep 1296943 = 1945415) B1945415
theorem B4926035 : Blo 1295966 4926035 := bstep (se 1 (by rfl) ⟨3694526, by rfl⟩ : syracuseStep 4926035 = 7389053) B7389053
theorem B1296999 : Blo 1295966 1296999 := bstep (se 1 (by rfl) ⟨972749, by rfl⟩ : syracuseStep 1296999 = 1945499) B1945499
theorem B10513091 : Blo 1295966 10513091 := bstep (se 1 (by rfl) ⟨7884818, by rfl⟩ : syracuseStep 10513091 = 15769637) B15769637
theorem B4434695 : Blo 1295966 4434695 := bstep (se 1 (by rfl) ⟨3326021, by rfl⟩ : syracuseStep 4434695 = 6652043) B6652043
theorem B14781203 : Blo 1295966 14781203 := bstep (se 1 (by rfl) ⟨11085902, by rfl⟩ : syracuseStep 14781203 = 22171805) B22171805
theorem B60689225 : Blo 1295966 60689225 := bstep (se 2 (by rfl) ⟨22758459, by rfl⟩ : syracuseStep 60689225 = 45516919) B45516919
theorem B9849761 : Blo 1295966 9849761 := bstep (se 2 (by rfl) ⟨3693660, by rfl⟩ : syracuseStep 9849761 = 7387321) B7387321
theorem B1297375 : Blo 1295966 1297375 := bstep (se 1 (by rfl) ⟨973031, by rfl⟩ : syracuseStep 1297375 = 1946063) B1946063
theorem B3116027 : Blo 1295966 3116027 := bstep (se 1 (by rfl) ⟨2337020, by rfl⟩ : syracuseStep 3116027 = 4674041) B4674041
theorem B1297403 : Blo 1295966 1297403 := bstep (se 1 (by rfl) ⟨973052, by rfl⟩ : syracuseStep 1297403 = 1946105) B1946105
theorem B2919419 : Blo 1295966 2919419 := bstep (se 1 (by rfl) ⟨2189564, by rfl⟩ : syracuseStep 2919419 = 4379129) B4379129
theorem B6229055 : Blo 1295966 6229055 := bstep (se 1 (by rfl) ⟨4671791, by rfl⟩ : syracuseStep 6229055 = 9343583) B9343583
theorem B1297471 : Blo 1295966 1297471 := bstep (se 1 (by rfl) ⟨973103, by rfl⟩ : syracuseStep 1297471 = 1946207) B1946207
theorem B1641647 : Blo 1295966 1641647 := bstep (se 1 (by rfl) ⟨1231235, by rfl⟩ : syracuseStep 1641647 = 2462471) B2462471
theorem B2919599 : Blo 1295966 2919599 := bstep (se 1 (by rfl) ⟨2189699, by rfl⟩ : syracuseStep 2919599 = 4379399) B4379399
theorem B2919635 : Blo 1295966 2919635 := bstep (se 1 (by rfl) ⟨2189726, by rfl⟩ : syracuseStep 2919635 = 4379453) B4379453
theorem B86486237 : Blo 1295966 86486237 := bstep (se 3 (by rfl) ⟨16216169, by rfl⟩ : syracuseStep 86486237 = 32432339) B32432339
theorem B1944887 : Blo 1295966 1944887 := bstep (se 1 (by rfl) ⟨1458665, by rfl⟩ : syracuseStep 1944887 = 2917331) B2917331
theorem B1297791 : Blo 1295966 1297791 := bstep (se 1 (by rfl) ⟨973343, by rfl⟩ : syracuseStep 1297791 = 1946687) B1946687
theorem B1297819 : Blo 1295966 1297819 := bstep (se 1 (by rfl) ⟨973364, by rfl⟩ : syracuseStep 1297819 = 1946729) B1946729
theorem B1945055 : Blo 1295966 1945055 := bstep (se 1 (by rfl) ⟨1458791, by rfl⟩ : syracuseStep 1945055 = 2917583) B2917583
theorem B4156895 : Blo 1295966 4156895 := bstep (se 1 (by rfl) ⟨3117671, by rfl⟩ : syracuseStep 4156895 = 6235343) B6235343
theorem B2919905 : Blo 1295966 2919905 := bstep (se 2 (by rfl) ⟨1094964, by rfl⟩ : syracuseStep 2919905 = 2189929) B2189929
theorem B1297887 : Blo 1295966 1297887 := bstep (se 1 (by rfl) ⟨973415, by rfl⟩ : syracuseStep 1297887 = 1946831) B1946831
theorem B4926977 : Blo 1295966 4926977 := bstep (se 2 (by rfl) ⟨1847616, by rfl⟩ : syracuseStep 4926977 = 3695233) B3695233
theorem B1945271 : Blo 1295966 1945271 := bstep (se 1 (by rfl) ⟨1458953, by rfl⟩ : syracuseStep 1945271 = 2917907) B2917907
theorem B1846967 : Blo 1295966 1846967 := bstep (se 1 (by rfl) ⟨1385225, by rfl⟩ : syracuseStep 1846967 = 2770451) B2770451
theorem B15781655 : Blo 1295966 15781655 := bstep (se 1 (by rfl) ⟨11836241, by rfl⟩ : syracuseStep 15781655 = 23672483) B23672483
theorem B3280763 : Blo 1295966 3280763 := bstep (se 1 (by rfl) ⟨2460572, by rfl⟩ : syracuseStep 3280763 = 4921145) B4921145
theorem B2494331 : Blo 1295966 2494331 := bstep (se 1 (by rfl) ⟨1870748, by rfl⟩ : syracuseStep 2494331 = 3741497) B3741497
theorem B2920319 : Blo 1295966 2920319 := bstep (se 1 (by rfl) ⟨2190239, by rfl⟩ : syracuseStep 2920319 = 4380479) B4380479
theorem B1945481 : Blo 1295966 1945481 := bstep (se 2 (by rfl) ⟨729555, by rfl⟩ : syracuseStep 1945481 = 1459111) B1459111
theorem B5541995 : Blo 1295966 5541995 := bstep (se 1 (by rfl) ⟨4156496, by rfl⟩ : syracuseStep 5541995 = 8312993) B8312993
theorem B1945727 : Blo 1295966 1945727 := bstep (se 1 (by rfl) ⟨1459295, by rfl⟩ : syracuseStep 1945727 = 2918591) B2918591
theorem B3281057 : Blo 1295966 3281057 := bstep (se 2 (by rfl) ⟨1230396, by rfl⟩ : syracuseStep 3281057 = 2460793) B2460793
theorem B7885451 : Blo 1295966 7885451 := bstep (se 1 (by rfl) ⟨5914088, by rfl⟩ : syracuseStep 7885451 = 11828177) B11828177
theorem B4928161 : Blo 1295966 4928161 := bstep (se 2 (by rfl) ⟨1848060, by rfl⟩ : syracuseStep 4928161 = 3696121) B3696121
theorem B7008943 : Blo 1295966 7008943 := bstep (se 1 (by rfl) ⟨5256707, by rfl⟩ : syracuseStep 7008943 = 10513415) B10513415
theorem B1946363 : Blo 1295966 1946363 := bstep (se 1 (by rfl) ⟨1459772, by rfl⟩ : syracuseStep 1946363 = 2919545) B2919545
theorem B2495315 : Blo 1295966 2495315 := bstep (se 1 (by rfl) ⟨1871486, by rfl⟩ : syracuseStep 2495315 = 3742973) B3742973
theorem B2462555 : Blo 1295966 2462555 := bstep (se 1 (by rfl) ⟨1846916, by rfl⟩ : syracuseStep 2462555 = 3693833) B3693833
theorem B5542937 : Blo 1295966 5542937 := bstep (se 2 (by rfl) ⟨2078601, by rfl⟩ : syracuseStep 5542937 = 4157203) B4157203
theorem B2462881 : Blo 1295966 2462881 := bstep (se 2 (by rfl) ⟨923580, by rfl⟩ : syracuseStep 2462881 = 1847161) B1847161
theorem B1946807 : Blo 1295966 1946807 := bstep (se 1 (by rfl) ⟨1460105, by rfl⟩ : syracuseStep 1946807 = 2920211) B2920211
theorem B9852191 : Blo 1295966 9852191 := bstep (se 1 (by rfl) ⟨7389143, by rfl⟩ : syracuseStep 9852191 = 14778287) B14778287
theorem B5330569 : Blo 1295966 5330569 := bstep (se 2 (by rfl) ⟨1998963, by rfl⟩ : syracuseStep 5330569 = 3997927) B3997927
theorem B5543635 : Blo 1295966 5543635 := bstep (se 1 (by rfl) ⟨4157726, by rfl⟩ : syracuseStep 5543635 = 8315453) B8315453
theorem B10516463 : Blo 1295966 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B4560887 : Blo 1295966 4560887 := bstep (se 1 (by rfl) ⟨3420665, by rfl⟩ : syracuseStep 4560887 = 6841331) B6841331
theorem B22460611 : Blo 1295966 22460611 := bstep (se 1 (by rfl) ⟨16845458, by rfl⟩ : syracuseStep 22460611 = 33690917) B33690917
theorem B4921631 : Blo 1295966 4921631 := bstep (se 1 (by rfl) ⟨3691223, by rfl⟩ : syracuseStep 4921631 = 7382447) B7382447
theorem B79804723 : Blo 1295966 79804723 := bstep (se 1 (by rfl) ⟨59853542, by rfl⟩ : syracuseStep 79804723 = 119707085) B119707085
theorem B12466493 : Blo 1295966 12466493 := bstep (se 3 (by rfl) ⟨2337467, by rfl⟩ : syracuseStep 12466493 = 4674935) B4674935
theorem B18708965 : Blo 1295966 18708965 := bstep (se 4 (by rfl) ⟨1753965, by rfl⟩ : syracuseStep 18708965 = 3507931) B3507931
theorem B9001543 : Blo 1295966 9001543 := bstep (se 1 (by rfl) ⟨6751157, by rfl⟩ : syracuseStep 9001543 = 13502315) B13502315
theorem B6650515 : Blo 1295966 6650515 := bstep (se 1 (by rfl) ⟨4987886, by rfl⟩ : syracuseStep 6650515 = 9975773) B9975773
theorem B3283699 : Blo 1295966 3283699 := bstep (se 1 (by rfl) ⟨2462774, by rfl⟩ : syracuseStep 3283699 = 4925549) B4925549
theorem B6749407 : Blo 1295966 6749407 := bstep (se 1 (by rfl) ⟨5062055, by rfl⟩ : syracuseStep 6749407 = 10124111) B10124111
theorem B4922633 : Blo 1295966 4922633 := bstep (se 2 (by rfl) ⟨1845987, by rfl⟩ : syracuseStep 4922633 = 3691975) B3691975
theorem B50552225 : Blo 1295966 50552225 := bstep (se 2 (by rfl) ⟨18957084, by rfl⟩ : syracuseStep 50552225 = 37914169) B37914169
theorem B11083169 : Blo 1295966 11083169 := bstep (se 2 (by rfl) ⟨4156188, by rfl⟩ : syracuseStep 11083169 = 8312377) B8312377
theorem B4677097 : Blo 1295966 4677097 := bstep (se 2 (by rfl) ⟨1753911, by rfl⟩ : syracuseStep 4677097 = 3507823) B3507823
theorem B2916071 : Blo 1295966 2916071 := bstep (se 1 (by rfl) ⟨2187053, by rfl⟩ : syracuseStep 2916071 = 4374107) B4374107
theorem B3284833 : Blo 1295966 3284833 := bstep (se 2 (by rfl) ⟨1231812, by rfl⟩ : syracuseStep 3284833 = 2463625) B2463625
theorem B4374377 : Blo 1295966 4374377 := bstep (se 2 (by rfl) ⟨1640391, by rfl⟩ : syracuseStep 4374377 = 3280783) B3280783
theorem B1458031 : Blo 1295966 1458031 := bstep (se 1 (by rfl) ⟨1093523, by rfl⟩ : syracuseStep 1458031 = 2187047) B2187047
theorem B3694663 : Blo 1295966 3694663 := bstep (se 1 (by rfl) ⟨2770997, by rfl⟩ : syracuseStep 3694663 = 5541995) B5541995
theorem B2187371 : Blo 1295966 2187371 := bstep (se 1 (by rfl) ⟨1640528, by rfl⟩ : syracuseStep 2187371 = 3281057) B3281057
theorem B1458535 : Blo 1295966 1458535 := bstep (se 1 (by rfl) ⟨1093901, by rfl⟩ : syracuseStep 1458535 = 2187803) B2187803
theorem B2187641 : Blo 1295966 2187641 := bstep (se 2 (by rfl) ⟨820365, by rfl⟩ : syracuseStep 2187641 = 1640731) B1640731
theorem B106406297 : Blo 1295966 106406297 := bstep (se 2 (by rfl) ⟨39902361, by rfl⟩ : syracuseStep 106406297 = 79804723) B79804723
theorem B1663543 : Blo 1295966 1663543 := bstep (se 1 (by rfl) ⟨1247657, by rfl⟩ : syracuseStep 1663543 = 2495315) B2495315
theorem B3695291 : Blo 1295966 3695291 := bstep (se 1 (by rfl) ⟨2771468, by rfl⟩ : syracuseStep 3695291 = 5542937) B5542937
theorem B12002057 : Blo 1295966 12002057 := bstep (se 2 (by rfl) ⟨4500771, by rfl⟩ : syracuseStep 12002057 = 9001543) B9001543
theorem B2917151 : Blo 1295966 2917151 := bstep (se 1 (by rfl) ⟨2187863, by rfl⟩ : syracuseStep 2917151 = 4375727) B4375727
theorem B6570881 : Blo 1295966 6570881 := bstep (se 2 (by rfl) ⟨2464080, by rfl⟩ : syracuseStep 6570881 = 4928161) B4928161
theorem B3507209 : Blo 1295966 3507209 := bstep (se 2 (by rfl) ⟨1315203, by rfl⟩ : syracuseStep 3507209 = 2630407) B2630407
theorem B34620527 : Blo 1295966 34620527 := bstep (se 1 (by rfl) ⟨25965395, by rfl⟩ : syracuseStep 34620527 = 51930791) B51930791
theorem B44909815 : Blo 1295966 44909815 := bstep (se 1 (by rfl) ⟨33682361, by rfl⟩ : syracuseStep 44909815 = 67364723) B67364723
theorem B2770195 : Blo 1295966 2770195 := bstep (se 1 (by rfl) ⟨2077646, by rfl⟩ : syracuseStep 2770195 = 4155293) B4155293
theorem B3040591 : Blo 1295966 3040591 := bstep (se 1 (by rfl) ⟨2280443, by rfl⟩ : syracuseStep 3040591 = 4560887) B4560887
theorem B4925245 : Blo 1295966 4925245 := bstep (se 3 (by rfl) ⟨923483, by rfl⟩ : syracuseStep 4925245 = 1846967) B1846967
theorem B6236129 : Blo 1295966 6236129 := bstep (se 2 (by rfl) ⟨2338548, by rfl⟩ : syracuseStep 6236129 = 4677097) B4677097
theorem B57657491 : Blo 1295966 57657491 := bstep (se 1 (by rfl) ⟨43243118, by rfl⟩ : syracuseStep 57657491 = 86486237) B86486237
theorem B1296591 : Blo 1295966 1296591 := bstep (se 1 (by rfl) ⟨972443, by rfl⟩ : syracuseStep 1296591 = 1944887) B1944887
theorem B7391513 : Blo 1295966 7391513 := bstep (se 2 (by rfl) ⟨2771817, by rfl⟩ : syracuseStep 7391513 = 5543635) B5543635
theorem B1296703 : Blo 1295966 1296703 := bstep (se 1 (by rfl) ⟨972527, by rfl⟩ : syracuseStep 1296703 = 1945055) B1945055
theorem B2771263 : Blo 1295966 2771263 := bstep (se 1 (by rfl) ⟨2078447, by rfl⟩ : syracuseStep 2771263 = 4156895) B4156895
theorem B1296847 : Blo 1295966 1296847 := bstep (se 1 (by rfl) ⟨972635, by rfl⟩ : syracuseStep 1296847 = 1945271) B1945271
theorem B1944041 : Blo 1295966 1944041 := bstep (se 2 (by rfl) ⟨729015, by rfl⟩ : syracuseStep 1944041 = 1458031) B1458031
theorem B1944047 : Blo 1295966 1944047 := bstep (se 1 (by rfl) ⟨1458035, by rfl⟩ : syracuseStep 1944047 = 2916071) B2916071
theorem B10521103 : Blo 1295966 10521103 := bstep (se 1 (by rfl) ⟨7890827, by rfl⟩ : syracuseStep 10521103 = 15781655) B15781655
theorem B1296987 : Blo 1295966 1296987 := bstep (se 1 (by rfl) ⟨972740, by rfl⟩ : syracuseStep 1296987 = 1945481) B1945481
theorem B8309405 : Blo 1295966 8309405 := bstep (se 3 (by rfl) ⟨1558013, by rfl⟩ : syracuseStep 8309405 = 3116027) B3116027
theorem B1297151 : Blo 1295966 1297151 := bstep (se 1 (by rfl) ⟨972863, by rfl⟩ : syracuseStep 1297151 = 1945727) B1945727
theorem B1944359 : Blo 1295966 1944359 := bstep (se 1 (by rfl) ⟨1458269, by rfl⟩ : syracuseStep 1944359 = 2916539) B2916539
theorem B1944431 : Blo 1295966 1944431 := bstep (se 1 (by rfl) ⟨1458323, by rfl⟩ : syracuseStep 1944431 = 2916647) B2916647
theorem B1944683 : Blo 1295966 1944683 := bstep (se 1 (by rfl) ⟨1458512, by rfl⟩ : syracuseStep 1944683 = 2917025) B2917025
theorem B4377725 : Blo 1295966 4377725 := bstep (se 3 (by rfl) ⟨820823, by rfl⟩ : syracuseStep 4377725 = 1641647) B1641647
theorem B1297575 : Blo 1295966 1297575 := bstep (se 1 (by rfl) ⟨973181, by rfl⟩ : syracuseStep 1297575 = 1946363) B1946363
theorem B6565049 : Blo 1295966 6565049 := bstep (se 2 (by rfl) ⟨2461893, by rfl⟩ : syracuseStep 6565049 = 4923787) B4923787
theorem B1641703 : Blo 1295966 1641703 := bstep (se 1 (by rfl) ⟨1231277, by rfl⟩ : syracuseStep 1641703 = 2462555) B2462555
theorem B7990595 : Blo 1295966 7990595 := bstep (se 1 (by rfl) ⟨5992946, by rfl⟩ : syracuseStep 7990595 = 11985893) B11985893
theorem B1944923 : Blo 1295966 1944923 := bstep (se 1 (by rfl) ⟨1458692, by rfl⟩ : syracuseStep 1944923 = 2917385) B2917385
theorem B6565211 : Blo 1295966 6565211 := bstep (se 1 (by rfl) ⟨4923908, by rfl⟩ : syracuseStep 6565211 = 9847817) B9847817
theorem B1944953 : Blo 1295966 1944953 := bstep (se 2 (by rfl) ⟨729357, by rfl⟩ : syracuseStep 1944953 = 1458715) B1458715
theorem B1944959 : Blo 1295966 1944959 := bstep (se 1 (by rfl) ⟨1458719, by rfl⟩ : syracuseStep 1944959 = 2917439) B2917439
theorem B1297871 : Blo 1295966 1297871 := bstep (se 1 (by rfl) ⟨973403, by rfl⟩ : syracuseStep 1297871 = 1946807) B1946807
theorem B8867353 : Blo 1295966 8867353 := bstep (se 2 (by rfl) ⟨3325257, by rfl⟩ : syracuseStep 8867353 = 6650515) B6650515
theorem B1945193 : Blo 1295966 1945193 := bstep (se 2 (by rfl) ⟨729447, by rfl⟩ : syracuseStep 1945193 = 1458895) B1458895
theorem B4378265 : Blo 1295966 4378265 := bstep (se 2 (by rfl) ⟨1641849, by rfl⟩ : syracuseStep 4378265 = 3283699) B3283699
theorem B11087543 : Blo 1295966 11087543 := bstep (se 1 (by rfl) ⟨8315657, by rfl⟩ : syracuseStep 11087543 = 16631315) B16631315
theorem B16609171 : Blo 1295966 16609171 := bstep (se 1 (by rfl) ⟨12456878, by rfl⟩ : syracuseStep 16609171 = 24913757) B24913757
theorem B1945583 : Blo 1295966 1945583 := bstep (se 1 (by rfl) ⟨1459187, by rfl⟩ : syracuseStep 1945583 = 2918375) B2918375
theorem B1945703 : Blo 1295966 1945703 := bstep (se 1 (by rfl) ⟨1459277, by rfl⟩ : syracuseStep 1945703 = 2918555) B2918555
theorem B3281087 : Blo 1295966 3281087 := bstep (se 1 (by rfl) ⟨2460815, by rfl⟩ : syracuseStep 3281087 = 4921631) B4921631
theorem B8310995 : Blo 1295966 8310995 := bstep (se 1 (by rfl) ⟨6233246, by rfl⟩ : syracuseStep 8310995 = 12466493) B12466493
theorem B1945823 : Blo 1295966 1945823 := bstep (se 1 (by rfl) ⟨1459367, by rfl⟩ : syracuseStep 1945823 = 2918735) B2918735
theorem B7385363 : Blo 1295966 7385363 := bstep (se 1 (by rfl) ⟨5539022, by rfl⟩ : syracuseStep 7385363 = 11078045) B11078045
theorem B1945883 : Blo 1295966 1945883 := bstep (se 1 (by rfl) ⟨1459412, by rfl⟩ : syracuseStep 1945883 = 2918825) B2918825
theorem B8999209 : Blo 1295966 8999209 := bstep (se 2 (by rfl) ⟨3374703, by rfl⟩ : syracuseStep 8999209 = 6749407) B6749407
theorem B12472643 : Blo 1295966 12472643 := bstep (se 1 (by rfl) ⟨9354482, by rfl⟩ : syracuseStep 12472643 = 18708965) B18708965
theorem B7008727 : Blo 1295966 7008727 := bstep (se 1 (by rfl) ⟨5256545, by rfl⟩ : syracuseStep 7008727 = 10513091) B10513091
theorem B6566507 : Blo 1295966 6566507 := bstep (se 1 (by rfl) ⟨4924880, by rfl⟩ : syracuseStep 6566507 = 9849761) B9849761
theorem B1946279 : Blo 1295966 1946279 := bstep (se 1 (by rfl) ⟨1459709, by rfl⟩ : syracuseStep 1946279 = 2919419) B2919419
theorem B1946399 : Blo 1295966 1946399 := bstep (se 1 (by rfl) ⟨1459799, by rfl⟩ : syracuseStep 1946399 = 2919599) B2919599
theorem B1946423 : Blo 1295966 1946423 := bstep (se 1 (by rfl) ⟨1459817, by rfl⟩ : syracuseStep 1946423 = 2919635) B2919635
theorem B3281755 : Blo 1295966 3281755 := bstep (se 1 (by rfl) ⟨2461316, by rfl⟩ : syracuseStep 3281755 = 4922633) B4922633
theorem B7107425 : Blo 1295966 7107425 := bstep (se 2 (by rfl) ⟨2665284, by rfl⟩ : syracuseStep 7107425 = 5330569) B5330569
theorem B1946537 : Blo 1295966 1946537 := bstep (se 2 (by rfl) ⟨729951, by rfl⟩ : syracuseStep 1946537 = 1459903) B1459903
theorem B1946603 : Blo 1295966 1946603 := bstep (se 1 (by rfl) ⟨1459952, by rfl⟩ : syracuseStep 1946603 = 2919905) B2919905
theorem B4379777 : Blo 1295966 4379777 := bstep (se 2 (by rfl) ⟨1642416, by rfl⟩ : syracuseStep 4379777 = 3284833) B3284833
theorem B1946879 : Blo 1295966 1946879 := bstep (se 1 (by rfl) ⟨1460159, by rfl⟩ : syracuseStep 1946879 = 2920319) B2920319
theorem B1946921 : Blo 1295966 1946921 := bstep (se 2 (by rfl) ⟨730095, by rfl⟩ : syracuseStep 1946921 = 1460191) B1460191
theorem B28038707 : Blo 1295966 28038707 := bstep (se 1 (by rfl) ⟨21029030, by rfl⟩ : syracuseStep 28038707 = 42058061) B42058061
theorem B29947481 : Blo 1295966 29947481 := bstep (se 2 (by rfl) ⟨11230305, by rfl⟩ : syracuseStep 29947481 = 22460611) B22460611
theorem B2627527 : Blo 1295966 2627527 := bstep (se 1 (by rfl) ⟨1970645, by rfl⟩ : syracuseStep 2627527 = 3941291) B3941291
theorem B6568127 : Blo 1295966 6568127 := bstep (se 1 (by rfl) ⟨4926095, by rfl⟩ : syracuseStep 6568127 = 9852191) B9852191
theorem B3283163 : Blo 1295966 3283163 := bstep (se 1 (by rfl) ⟨2462372, by rfl⟩ : syracuseStep 3283163 = 4924745) B4924745
theorem B9345257 : Blo 1295966 9345257 := bstep (se 2 (by rfl) ⟨3504471, by rfl⟩ : syracuseStep 9345257 = 7008943) B7008943
theorem B3283487 : Blo 1295966 3283487 := bstep (se 1 (by rfl) ⟨2462615, by rfl⟩ : syracuseStep 3283487 = 4925231) B4925231
theorem B2497115 : Blo 1295966 2497115 := bstep (se 1 (by rfl) ⟨1872836, by rfl⟩ : syracuseStep 2497115 = 3745673) B3745673
theorem B7010975 : Blo 1295966 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B40475459 : Blo 1295966 40475459 := bstep (se 1 (by rfl) ⟨30356594, by rfl⟩ : syracuseStep 40475459 = 60713189) B60713189
theorem B3283841 : Blo 1295966 3283841 := bstep (se 2 (by rfl) ⟨1231440, by rfl⟩ : syracuseStep 3283841 = 2462881) B2462881
theorem B21027869 : Blo 1295966 21027869 := bstep (se 3 (by rfl) ⟨3942725, by rfl⟩ : syracuseStep 21027869 = 7885451) B7885451
theorem B3284023 : Blo 1295966 3284023 := bstep (se 1 (by rfl) ⟨2463017, by rfl⟩ : syracuseStep 3284023 = 4926035) B4926035
theorem B2956463 : Blo 1295966 2956463 := bstep (se 1 (by rfl) ⟨2217347, by rfl⟩ : syracuseStep 2956463 = 4434695) B4434695
theorem B9854135 : Blo 1295966 9854135 := bstep (se 1 (by rfl) ⟨7390601, by rfl⟩ : syracuseStep 9854135 = 14781203) B14781203
theorem B40459483 : Blo 1295966 40459483 := bstep (se 1 (by rfl) ⟨30344612, by rfl⟩ : syracuseStep 40459483 = 60689225) B60689225
theorem B4152703 : Blo 1295966 4152703 := bstep (se 1 (by rfl) ⟨3114527, by rfl⟩ : syracuseStep 4152703 = 6229055) B6229055
theorem B3694049 : Blo 1295966 3694049 := bstep (se 2 (by rfl) ⟨1385268, by rfl⟩ : syracuseStep 3694049 = 2770537) B2770537
theorem B33701483 : Blo 1295966 33701483 := bstep (se 1 (by rfl) ⟨25276112, by rfl⟩ : syracuseStep 33701483 = 50552225) B50552225
theorem B7388779 : Blo 1295966 7388779 := bstep (se 1 (by rfl) ⟨5541584, by rfl⟩ : syracuseStep 7388779 = 11083169) B11083169
theorem B3284651 : Blo 1295966 3284651 := bstep (se 1 (by rfl) ⟨2463488, by rfl⟩ : syracuseStep 3284651 = 4926977) B4926977
theorem B2916251 : Blo 1295966 2916251 := bstep (se 1 (by rfl) ⟨2187188, by rfl⟩ : syracuseStep 2916251 = 4374377) B4374377
theorem B2187175 : Blo 1295966 2187175 := bstep (se 1 (by rfl) ⟨1640381, by rfl⟩ : syracuseStep 2187175 = 3280763) B3280763
theorem B1662887 : Blo 1295966 1662887 := bstep (se 1 (by rfl) ⟨1247165, by rfl⟩ : syracuseStep 1662887 = 2494331) B2494331
theorem B1458247 : Blo 1295966 1458247 := bstep (se 1 (by rfl) ⟨1093685, by rfl⟩ : syracuseStep 1458247 = 2187371) B2187371
theorem B2187391 : Blo 1295966 2187391 := bstep (se 1 (by rfl) ⟨1640543, by rfl⟩ : syracuseStep 2187391 = 3281087) B3281087
theorem B4923575 : Blo 1295966 4923575 := bstep (se 1 (by rfl) ⟨3692681, by rfl⟩ : syracuseStep 4923575 = 7385363) B7385363
theorem B8315095 : Blo 1295966 8315095 := bstep (se 1 (by rfl) ⟨6236321, by rfl⟩ : syracuseStep 8315095 = 12472643) B12472643
theorem B1458427 : Blo 1295966 1458427 := bstep (se 1 (by rfl) ⟨1093820, by rfl⟩ : syracuseStep 1458427 = 2187641) B2187641
theorem B8872229 : Blo 1295966 8872229 := bstep (se 4 (by rfl) ⟨831771, by rfl⟩ : syracuseStep 8872229 = 1663543) B1663543
theorem B3695017 : Blo 1295966 3695017 := bstep (se 2 (by rfl) ⟨1385631, by rfl⟩ : syracuseStep 3695017 = 2771263) B2771263
theorem B19964987 : Blo 1295966 19964987 := bstep (se 1 (by rfl) ⟨14973740, by rfl⟩ : syracuseStep 19964987 = 29947481) B29947481
theorem B4375673 : Blo 1295966 4375673 := bstep (se 2 (by rfl) ⟨1640877, by rfl⟩ : syracuseStep 4375673 = 3281755) B3281755
theorem B38438327 : Blo 1295966 38438327 := bstep (se 1 (by rfl) ⟨28828745, by rfl⟩ : syracuseStep 38438327 = 57657491) B57657491
theorem B2188775 : Blo 1295966 2188775 := bstep (se 1 (by rfl) ⟨1641581, by rfl⟩ : syracuseStep 2188775 = 3283163) B3283163
theorem B2188937 : Blo 1295966 2188937 := bstep (se 2 (by rfl) ⟨820851, by rfl⟩ : syracuseStep 2188937 = 1641703) B1641703
theorem B1296027 : Blo 1295966 1296027 := bstep (se 1 (by rfl) ⟨972020, by rfl⟩ : syracuseStep 1296027 = 1944041) B1944041
theorem B1296031 : Blo 1295966 1296031 := bstep (se 1 (by rfl) ⟨972023, by rfl⟩ : syracuseStep 1296031 = 1944047) B1944047
theorem B2188991 : Blo 1295966 2188991 := bstep (se 1 (by rfl) ⟨1641743, by rfl⟩ : syracuseStep 2188991 = 3283487) B3283487
theorem B18695933 : Blo 1295966 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B5539603 : Blo 1295966 5539603 := bstep (se 1 (by rfl) ⟨4154702, by rfl⟩ : syracuseStep 5539603 = 8309405) B8309405
theorem B1296239 : Blo 1295966 1296239 := bstep (se 1 (by rfl) ⟨972179, by rfl⟩ : syracuseStep 1296239 = 1944359) B1944359
theorem B1296287 : Blo 1295966 1296287 := bstep (se 1 (by rfl) ⟨972215, by rfl⟩ : syracuseStep 1296287 = 1944431) B1944431
theorem B2189227 : Blo 1295966 2189227 := bstep (se 1 (by rfl) ⟨1641920, by rfl⟩ : syracuseStep 2189227 = 3283841) B3283841
theorem B14018579 : Blo 1295966 14018579 := bstep (se 1 (by rfl) ⟨10513934, by rfl⟩ : syracuseStep 14018579 = 21027869) B21027869
theorem B11823137 : Blo 1295966 11823137 := bstep (se 2 (by rfl) ⟨4433676, by rfl⟩ : syracuseStep 11823137 = 8867353) B8867353
theorem B1296455 : Blo 1295966 1296455 := bstep (se 1 (by rfl) ⟨972341, by rfl⟩ : syracuseStep 1296455 = 1944683) B1944683
theorem B2918483 : Blo 1295966 2918483 := bstep (se 1 (by rfl) ⟨2188862, by rfl⟩ : syracuseStep 2918483 = 4377725) B4377725
theorem B4376699 : Blo 1295966 4376699 := bstep (se 1 (by rfl) ⟨3282524, by rfl⟩ : syracuseStep 4376699 = 6565049) B6565049
theorem B5327063 : Blo 1295966 5327063 := bstep (se 1 (by rfl) ⟨3995297, by rfl⟩ : syracuseStep 5327063 = 7990595) B7990595
theorem B1296615 : Blo 1295966 1296615 := bstep (se 1 (by rfl) ⟨972461, by rfl⟩ : syracuseStep 1296615 = 1944923) B1944923
theorem B4376807 : Blo 1295966 4376807 := bstep (se 1 (by rfl) ⟨3282605, by rfl⟩ : syracuseStep 4376807 = 6565211) B6565211
theorem B1296635 : Blo 1295966 1296635 := bstep (se 1 (by rfl) ⟨972476, by rfl⟩ : syracuseStep 1296635 = 1944953) B1944953
theorem B1296639 : Blo 1295966 1296639 := bstep (se 1 (by rfl) ⟨972479, by rfl⟩ : syracuseStep 1296639 = 1944959) B1944959
theorem B1296795 : Blo 1295966 1296795 := bstep (se 1 (by rfl) ⟨972596, by rfl⟩ : syracuseStep 1296795 = 1945193) B1945193
theorem B4434365 : Blo 1295966 4434365 := bstep (se 3 (by rfl) ⟨831443, by rfl⟩ : syracuseStep 4434365 = 1662887) B1662887
theorem B2189767 : Blo 1295966 2189767 := bstep (se 1 (by rfl) ⟨1642325, by rfl⟩ : syracuseStep 2189767 = 3284651) B3284651
theorem B7391695 : Blo 1295966 7391695 := bstep (se 1 (by rfl) ⟨5543771, by rfl⟩ : syracuseStep 7391695 = 11087543) B11087543
theorem B22145561 : Blo 1295966 22145561 := bstep (se 2 (by rfl) ⟨8304585, by rfl⟩ : syracuseStep 22145561 = 16609171) B16609171
theorem B1944167 : Blo 1295966 1944167 := bstep (se 1 (by rfl) ⟨1458125, by rfl⟩ : syracuseStep 1944167 = 2916251) B2916251
theorem B1297055 : Blo 1295966 1297055 := bstep (se 1 (by rfl) ⟨972791, by rfl⟩ : syracuseStep 1297055 = 1945583) B1945583
theorem B1297135 : Blo 1295966 1297135 := bstep (se 1 (by rfl) ⟨972851, by rfl⟩ : syracuseStep 1297135 = 1945703) B1945703
theorem B4926217 : Blo 1295966 4926217 := bstep (se 2 (by rfl) ⟨1847331, by rfl⟩ : syracuseStep 4926217 = 3694663) B3694663
theorem B5540663 : Blo 1295966 5540663 := bstep (se 1 (by rfl) ⟨4155497, by rfl⟩ : syracuseStep 5540663 = 8310995) B8310995
theorem B1297215 : Blo 1295966 1297215 := bstep (se 1 (by rfl) ⟨972911, by rfl⟩ : syracuseStep 1297215 = 1945823) B1945823
theorem B1297255 : Blo 1295966 1297255 := bstep (se 1 (by rfl) ⟨972941, by rfl⟩ : syracuseStep 1297255 = 1945883) B1945883
theorem B70937531 : Blo 1295966 70937531 := bstep (se 1 (by rfl) ⟨53203148, by rfl⟩ : syracuseStep 70937531 = 106406297) B106406297
theorem B4377671 : Blo 1295966 4377671 := bstep (se 1 (by rfl) ⟨3283253, by rfl⟩ : syracuseStep 4377671 = 6566507) B6566507
theorem B1297519 : Blo 1295966 1297519 := bstep (se 1 (by rfl) ⟨973139, by rfl⟩ : syracuseStep 1297519 = 1946279) B1946279
theorem B1944713 : Blo 1295966 1944713 := bstep (se 2 (by rfl) ⟨729267, by rfl⟩ : syracuseStep 1944713 = 1458535) B1458535
theorem B1944767 : Blo 1295966 1944767 := bstep (se 1 (by rfl) ⟨1458575, by rfl⟩ : syracuseStep 1944767 = 2917151) B2917151
theorem B1297599 : Blo 1295966 1297599 := bstep (se 1 (by rfl) ⟨973199, by rfl⟩ : syracuseStep 1297599 = 1946399) B1946399
theorem B1297615 : Blo 1295966 1297615 := bstep (se 1 (by rfl) ⟨973211, by rfl⟩ : syracuseStep 1297615 = 1946423) B1946423
theorem B4738283 : Blo 1295966 4738283 := bstep (se 1 (by rfl) ⟨3553712, by rfl⟩ : syracuseStep 4738283 = 7107425) B7107425
theorem B1297691 : Blo 1295966 1297691 := bstep (se 1 (by rfl) ⟨973268, by rfl⟩ : syracuseStep 1297691 = 1946537) B1946537
theorem B1297735 : Blo 1295966 1297735 := bstep (se 1 (by rfl) ⟨973301, by rfl⟩ : syracuseStep 1297735 = 1946603) B1946603
theorem B2338139 : Blo 1295966 2338139 := bstep (se 1 (by rfl) ⟨1753604, by rfl⟩ : syracuseStep 2338139 = 3507209) B3507209
theorem B14028137 : Blo 1295966 14028137 := bstep (se 2 (by rfl) ⟨5260551, by rfl⟩ : syracuseStep 14028137 = 10521103) B10521103
theorem B23080351 : Blo 1295966 23080351 := bstep (se 1 (by rfl) ⟨17310263, by rfl⟩ : syracuseStep 23080351 = 34620527) B34620527
theorem B2919851 : Blo 1295966 2919851 := bstep (se 1 (by rfl) ⟨2189888, by rfl⟩ : syracuseStep 2919851 = 4379777) B4379777
theorem B1297919 : Blo 1295966 1297919 := bstep (se 1 (by rfl) ⟨973439, by rfl⟩ : syracuseStep 1297919 = 1946879) B1946879
theorem B1297947 : Blo 1295966 1297947 := bstep (se 1 (by rfl) ⟨973460, by rfl⟩ : syracuseStep 1297947 = 1946921) B1946921
theorem B4157419 : Blo 1295966 4157419 := bstep (se 1 (by rfl) ⟨3118064, by rfl⟩ : syracuseStep 4157419 = 6236129) B6236129
theorem B4378697 : Blo 1295966 4378697 := bstep (se 2 (by rfl) ⟨1642011, by rfl⟩ : syracuseStep 4378697 = 3284023) B3284023
theorem B4378751 : Blo 1295966 4378751 := bstep (se 1 (by rfl) ⟨3284063, by rfl⟩ : syracuseStep 4378751 = 6568127) B6568127
theorem B6230171 : Blo 1295966 6230171 := bstep (se 1 (by rfl) ⟨4672628, by rfl⟩ : syracuseStep 6230171 = 9345257) B9345257
theorem B4927675 : Blo 1295966 4927675 := bstep (se 1 (by rfl) ⟨3695756, by rfl⟩ : syracuseStep 4927675 = 7391513) B7391513
theorem B59879753 : Blo 1295966 59879753 := bstep (se 2 (by rfl) ⟨22454907, by rfl⟩ : syracuseStep 59879753 = 44909815) B44909815
theorem B1970975 : Blo 1295966 1970975 := bstep (se 1 (by rfl) ⟨1478231, by rfl⟩ : syracuseStep 1970975 = 2956463) B2956463
theorem B9851705 : Blo 1295966 9851705 := bstep (se 2 (by rfl) ⟨3694389, by rfl⟩ : syracuseStep 9851705 = 7388779) B7388779
theorem B2462699 : Blo 1295966 2462699 := bstep (se 1 (by rfl) ⟨1847024, by rfl⟩ : syracuseStep 2462699 = 3694049) B3694049
theorem B22467655 : Blo 1295966 22467655 := bstep (se 1 (by rfl) ⟨16850741, by rfl⟩ : syracuseStep 22467655 = 33701483) B33701483
theorem B6566993 : Blo 1295966 6566993 := bstep (se 2 (by rfl) ⟨2462622, by rfl⟩ : syracuseStep 6566993 = 4925245) B4925245
theorem B2918843 : Blo 1295966 2918843 := bstep (se 1 (by rfl) ⟨2189132, by rfl⟩ : syracuseStep 2918843 = 4378265) B4378265
theorem B3503369 : Blo 1295966 3503369 := bstep (se 2 (by rfl) ⟨1313763, by rfl⟩ : syracuseStep 3503369 = 2627527) B2627527
theorem B11998945 : Blo 1295966 11998945 := bstep (se 2 (by rfl) ⟨4499604, by rfl⟩ : syracuseStep 11998945 = 8999209) B8999209
theorem B2463527 : Blo 1295966 2463527 := bstep (se 1 (by rfl) ⟨1847645, by rfl⟩ : syracuseStep 2463527 = 3695291) B3695291
theorem B8001371 : Blo 1295966 8001371 := bstep (se 1 (by rfl) ⟨6001028, by rfl⟩ : syracuseStep 8001371 = 12002057) B12002057
theorem B4380587 : Blo 1295966 4380587 := bstep (se 1 (by rfl) ⟨3285440, by rfl⟩ : syracuseStep 4380587 = 6570881) B6570881
theorem B9344969 : Blo 1295966 9344969 := bstep (se 2 (by rfl) ⟨3504363, by rfl⟩ : syracuseStep 9344969 = 7008727) B7008727
theorem B18692471 : Blo 1295966 18692471 := bstep (se 1 (by rfl) ⟨14019353, by rfl⟩ : syracuseStep 18692471 = 28038707) B28038707
theorem B215783909 : Blo 1295966 215783909 := bstep (se 4 (by rfl) ⟨20229741, by rfl⟩ : syracuseStep 215783909 = 40459483) B40459483
theorem B6658973 : Blo 1295966 6658973 := bstep (se 3 (by rfl) ⟨1248557, by rfl⟩ : syracuseStep 6658973 = 2497115) B2497115
theorem B3693593 : Blo 1295966 3693593 := bstep (se 2 (by rfl) ⟨1385097, by rfl⟩ : syracuseStep 3693593 = 2770195) B2770195
theorem B4054121 : Blo 1295966 4054121 := bstep (se 2 (by rfl) ⟨1520295, by rfl⟩ : syracuseStep 4054121 = 3040591) B3040591
theorem B5536937 : Blo 1295966 5536937 := bstep (se 2 (by rfl) ⟨2076351, by rfl⟩ : syracuseStep 5536937 = 4152703) B4152703
theorem B26983639 : Blo 1295966 26983639 := bstep (se 1 (by rfl) ⟨20237729, by rfl⟩ : syracuseStep 26983639 = 40475459) B40475459
theorem B6569423 : Blo 1295966 6569423 := bstep (se 1 (by rfl) ⟨4927067, by rfl⟩ : syracuseStep 6569423 = 9854135) B9854135
theorem B2916233 : Blo 1295966 2916233 := bstep (se 2 (by rfl) ⟨1093587, by rfl⟩ : syracuseStep 2916233 = 2187175) B2187175
theorem B4153447 : Blo 1295966 4153447 := bstep (se 1 (by rfl) ⟨3115085, by rfl⟩ : syracuseStep 4153447 = 6230171) B6230171
theorem B2916521 : Blo 1295966 2916521 := bstep (se 2 (by rfl) ⟨1093695, by rfl⟩ : syracuseStep 2916521 = 2187391) B2187391
theorem B5914819 : Blo 1295966 5914819 := bstep (se 1 (by rfl) ⟨4436114, by rfl⟩ : syracuseStep 5914819 = 8872229) B8872229
theorem B39919835 : Blo 1295966 39919835 := bstep (se 1 (by rfl) ⟨29939876, by rfl⟩ : syracuseStep 39919835 = 59879753) B59879753
theorem B6570233 : Blo 1295966 6570233 := bstep (se 2 (by rfl) ⟨2463837, by rfl⟩ : syracuseStep 6570233 = 4927675) B4927675
theorem B9855593 : Blo 1295966 9855593 := bstep (se 2 (by rfl) ⟨3695847, by rfl⟩ : syracuseStep 9855593 = 7391695) B7391695
theorem B2917115 : Blo 1295966 2917115 := bstep (se 1 (by rfl) ⟨2187836, by rfl⟩ : syracuseStep 2917115 = 4375673) B4375673
theorem B1459183 : Blo 1295966 1459183 := bstep (se 1 (by rfl) ⟨1094387, by rfl⟩ : syracuseStep 1459183 = 2188775) B2188775
theorem B1459291 : Blo 1295966 1459291 := bstep (se 1 (by rfl) ⟨1094468, by rfl⟩ : syracuseStep 1459291 = 2188937) B2188937
theorem B1459327 : Blo 1295966 1459327 := bstep (se 1 (by rfl) ⟨1094495, by rfl⟩ : syracuseStep 1459327 = 2188991) B2188991
theorem B5334247 : Blo 1295966 5334247 := bstep (se 1 (by rfl) ⟨4000685, by rfl⟩ : syracuseStep 5334247 = 8001371) B8001371
theorem B7882091 : Blo 1295966 7882091 := bstep (se 1 (by rfl) ⟨5911568, by rfl⟩ : syracuseStep 7882091 = 11823137) B11823137
theorem B2917799 : Blo 1295966 2917799 := bstep (se 1 (by rfl) ⟨2188349, by rfl⟩ : syracuseStep 2917799 = 4376699) B4376699
theorem B2917871 : Blo 1295966 2917871 := bstep (se 1 (by rfl) ⟨2188403, by rfl⟩ : syracuseStep 2917871 = 4376807) B4376807
theorem B12461647 : Blo 1295966 12461647 := bstep (se 1 (by rfl) ⟨9346235, by rfl⟩ : syracuseStep 12461647 = 18692471) B18692471
theorem B14763707 : Blo 1295966 14763707 := bstep (se 1 (by rfl) ⟨11072780, by rfl⟩ : syracuseStep 14763707 = 22145561) B22145561
theorem B1296111 : Blo 1295966 1296111 := bstep (se 1 (by rfl) ⟨972083, by rfl⟩ : syracuseStep 1296111 = 1944167) B1944167
theorem B2918447 : Blo 1295966 2918447 := bstep (se 1 (by rfl) ⟨2188835, by rfl⟩ : syracuseStep 2918447 = 4377671) B4377671
theorem B1296475 : Blo 1295966 1296475 := bstep (se 1 (by rfl) ⟨972356, by rfl⟩ : syracuseStep 1296475 = 1944713) B1944713
theorem B1296511 : Blo 1295966 1296511 := bstep (se 1 (by rfl) ⟨972383, by rfl⟩ : syracuseStep 1296511 = 1944767) B1944767
theorem B1558759 : Blo 1295966 1558759 := bstep (se 1 (by rfl) ⟨1169069, by rfl⟩ : syracuseStep 1558759 = 2338139) B2338139
theorem B2918969 : Blo 1295966 2918969 := bstep (se 2 (by rfl) ⟨1094613, by rfl⟩ : syracuseStep 2918969 = 2189227) B2189227
theorem B1944155 : Blo 1295966 1944155 := bstep (se 1 (by rfl) ⟨1458116, by rfl⟩ : syracuseStep 1944155 = 2916233) B2916233
theorem B2919131 : Blo 1295966 2919131 := bstep (se 1 (by rfl) ⟨2189348, by rfl⟩ : syracuseStep 2919131 = 4378697) B4378697
theorem B2919167 : Blo 1295966 2919167 := bstep (se 1 (by rfl) ⟨2189375, by rfl⟩ : syracuseStep 2919167 = 4378751) B4378751
theorem B1944329 : Blo 1295966 1944329 := bstep (se 2 (by rfl) ⟨729123, by rfl⟩ : syracuseStep 1944329 = 1458247) B1458247
theorem B11086793 : Blo 1295966 11086793 := bstep (se 2 (by rfl) ⟨4157547, by rfl⟩ : syracuseStep 11086793 = 8315095) B8315095
theorem B1944569 : Blo 1295966 1944569 := bstep (se 2 (by rfl) ⟨729213, by rfl⟩ : syracuseStep 1944569 = 1458427) B1458427
theorem B14765165 : Blo 1295966 14765165 := bstep (se 3 (by rfl) ⟨2768468, by rfl⟩ : syracuseStep 14765165 = 5536937) B5536937
theorem B1313983 : Blo 1295966 1313983 := bstep (se 1 (by rfl) ⟨985487, by rfl⟩ : syracuseStep 1313983 = 1970975) B1970975
theorem B4926689 : Blo 1295966 4926689 := bstep (se 2 (by rfl) ⟨1847508, by rfl⟩ : syracuseStep 4926689 = 3695017) B3695017
theorem B2919689 : Blo 1295966 2919689 := bstep (se 2 (by rfl) ⟨1094883, by rfl⟩ : syracuseStep 2919689 = 2189767) B2189767
theorem B1641799 : Blo 1295966 1641799 := bstep (se 1 (by rfl) ⟨1231349, by rfl⟩ : syracuseStep 1641799 = 2462699) B2462699
theorem B9342317 : Blo 1295966 9342317 := bstep (se 3 (by rfl) ⟨1751684, by rfl⟩ : syracuseStep 9342317 = 3503369) B3503369
theorem B4377995 : Blo 1295966 4377995 := bstep (se 1 (by rfl) ⟨3283496, by rfl⟩ : syracuseStep 4377995 = 6566993) B6566993
theorem B102502205 : Blo 1295966 102502205 := bstep (se 3 (by rfl) ⟨19219163, by rfl⟩ : syracuseStep 102502205 = 38438327) B38438327
theorem B11824973 : Blo 1295966 11824973 := bstep (se 3 (by rfl) ⟨2217182, by rfl⟩ : syracuseStep 11824973 = 4434365) B4434365
theorem B12463955 : Blo 1295966 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B1642351 : Blo 1295966 1642351 := bstep (se 1 (by rfl) ⟨1231763, by rfl⟩ : syracuseStep 1642351 = 2463527) B2463527
theorem B2920391 : Blo 1295966 2920391 := bstep (se 1 (by rfl) ⟨2190293, by rfl⟩ : syracuseStep 2920391 = 4380587) B4380587
theorem B6229979 : Blo 1295966 6229979 := bstep (se 1 (by rfl) ⟨4672484, by rfl⟩ : syracuseStep 6229979 = 9344969) B9344969
theorem B1945655 : Blo 1295966 1945655 := bstep (se 1 (by rfl) ⟨1459241, by rfl⟩ : syracuseStep 1945655 = 2918483) B2918483
theorem B3551375 : Blo 1295966 3551375 := bstep (se 1 (by rfl) ⟨2663531, by rfl⟩ : syracuseStep 3551375 = 5327063) B5327063
theorem B1945895 : Blo 1295966 1945895 := bstep (se 1 (by rfl) ⟨1459421, by rfl⟩ : syracuseStep 1945895 = 2918843) B2918843
theorem B143855939 : Blo 1295966 143855939 := bstep (se 1 (by rfl) ⟨107891954, by rfl⟩ : syracuseStep 143855939 = 215783909) B215783909
theorem B30773801 : Blo 1295966 30773801 := bstep (se 2 (by rfl) ⟨11540175, by rfl⟩ : syracuseStep 30773801 = 23080351) B23080351
theorem B2462395 : Blo 1295966 2462395 := bstep (se 1 (by rfl) ⟨1846796, by rfl⟩ : syracuseStep 2462395 = 3693593) B3693593
theorem B3158855 : Blo 1295966 3158855 := bstep (se 1 (by rfl) ⟨2369141, by rfl⟩ : syracuseStep 3158855 = 4738283) B4738283
theorem B9352091 : Blo 1295966 9352091 := bstep (se 1 (by rfl) ⟨7014068, by rfl⟩ : syracuseStep 9352091 = 14028137) B14028137
theorem B1946567 : Blo 1295966 1946567 := bstep (se 1 (by rfl) ⟨1459925, by rfl⟩ : syracuseStep 1946567 = 2919851) B2919851
theorem B4379615 : Blo 1295966 4379615 := bstep (se 1 (by rfl) ⟨3284711, by rfl⟩ : syracuseStep 4379615 = 6569423) B6569423
theorem B7386137 : Blo 1295966 7386137 := bstep (se 2 (by rfl) ⟨2769801, by rfl⟩ : syracuseStep 7386137 = 5539603) B5539603
theorem B5543225 : Blo 1295966 5543225 := bstep (se 2 (by rfl) ⟨2078709, by rfl⟩ : syracuseStep 5543225 = 4157419) B4157419
theorem B3282383 : Blo 1295966 3282383 := bstep (se 1 (by rfl) ⟨2461787, by rfl⟩ : syracuseStep 3282383 = 4923575) B4923575
theorem B6567803 : Blo 1295966 6567803 := bstep (se 1 (by rfl) ⟨4925852, by rfl⟩ : syracuseStep 6567803 = 9851705) B9851705
theorem B13309991 : Blo 1295966 13309991 := bstep (se 1 (by rfl) ⟨9982493, by rfl⟩ : syracuseStep 13309991 = 19964987) B19964987
theorem B6568289 : Blo 1295966 6568289 := bstep (se 2 (by rfl) ⟨2463108, by rfl⟩ : syracuseStep 6568289 = 4926217) B4926217
theorem B9345719 : Blo 1295966 9345719 := bstep (se 1 (by rfl) ⟨7009289, by rfl⟩ : syracuseStep 9345719 = 14018579) B14018579
theorem B29956873 : Blo 1295966 29956873 := bstep (se 2 (by rfl) ⟨11233827, by rfl⟩ : syracuseStep 29956873 = 22467655) B22467655
theorem B35978185 : Blo 1295966 35978185 := bstep (se 2 (by rfl) ⟨13491819, by rfl⟩ : syracuseStep 35978185 = 26983639) B26983639
theorem B3693775 : Blo 1295966 3693775 := bstep (se 1 (by rfl) ⟨2770331, by rfl⟩ : syracuseStep 3693775 = 5540663) B5540663
theorem B4439315 : Blo 1295966 4439315 := bstep (se 1 (by rfl) ⟨3329486, by rfl⟩ : syracuseStep 4439315 = 6658973) B6658973
theorem B47291687 : Blo 1295966 47291687 := bstep (se 1 (by rfl) ⟨35468765, by rfl⟩ : syracuseStep 47291687 = 70937531) B70937531
theorem B2702747 : Blo 1295966 2702747 := bstep (se 1 (by rfl) ⟨2027060, by rfl⟩ : syracuseStep 2702747 = 4054121) B4054121
theorem B15998593 : Blo 1295966 15998593 := bstep (se 2 (by rfl) ⟨5999472, by rfl⟩ : syracuseStep 15998593 = 11998945) B11998945
theorem B5537929 : Blo 1295966 5537929 := bstep (se 2 (by rfl) ⟨2076723, by rfl⟩ : syracuseStep 5537929 = 4153447) B4153447
theorem B95903959 : Blo 1295966 95903959 := bstep (se 1 (by rfl) ⟨71927969, by rfl⟩ : syracuseStep 95903959 = 143855939) B143855939
theorem B9470333 : Blo 1295966 9470333 := bstep (se 3 (by rfl) ⟨1775687, by rfl⟩ : syracuseStep 9470333 = 3551375) B3551375
theorem B6570395 : Blo 1295966 6570395 := bstep (se 1 (by rfl) ⟨4927796, by rfl⟩ : syracuseStep 6570395 = 9855593) B9855593
theorem B2105903 : Blo 1295966 2105903 := bstep (se 1 (by rfl) ⟨1579427, by rfl⟩ : syracuseStep 2105903 = 3158855) B3158855
theorem B6234727 : Blo 1295966 6234727 := bstep (se 1 (by rfl) ⟨4676045, by rfl⟩ : syracuseStep 6234727 = 9352091) B9352091
theorem B4924091 : Blo 1295966 4924091 := bstep (se 1 (by rfl) ⟨3693068, by rfl⟩ : syracuseStep 4924091 = 7386137) B7386137
theorem B3695483 : Blo 1295966 3695483 := bstep (se 1 (by rfl) ⟨2771612, by rfl⟩ : syracuseStep 3695483 = 5543225) B5543225
theorem B2188255 : Blo 1295966 2188255 := bstep (se 1 (by rfl) ⟨1641191, by rfl⟩ : syracuseStep 2188255 = 3282383) B3282383
theorem B8873327 : Blo 1295966 8873327 := bstep (se 1 (by rfl) ⟨6654995, by rfl⟩ : syracuseStep 8873327 = 13309991) B13309991
theorem B4925033 : Blo 1295966 4925033 := bstep (se 2 (by rfl) ⟨1846887, by rfl⟩ : syracuseStep 4925033 = 3693775) B3693775
theorem B7112329 : Blo 1295966 7112329 := bstep (se 2 (by rfl) ⟨2667123, by rfl⟩ : syracuseStep 7112329 = 5334247) B5334247
theorem B1296103 : Blo 1295966 1296103 := bstep (se 1 (by rfl) ⟨972077, by rfl⟩ : syracuseStep 1296103 = 1944155) B1944155
theorem B2189065 : Blo 1295966 2189065 := bstep (se 2 (by rfl) ⟨820899, by rfl⟩ : syracuseStep 2189065 = 1641799) B1641799
theorem B1296219 : Blo 1295966 1296219 := bstep (se 1 (by rfl) ⟨972164, by rfl⟩ : syracuseStep 1296219 = 1944329) B1944329
theorem B7391195 : Blo 1295966 7391195 := bstep (se 1 (by rfl) ⟨5543396, by rfl⟩ : syracuseStep 7391195 = 11086793) B11086793
theorem B1296379 : Blo 1295966 1296379 := bstep (se 1 (by rfl) ⟨972284, by rfl⟩ : syracuseStep 1296379 = 1944569) B1944569
theorem B16615529 : Blo 1295966 16615529 := bstep (se 2 (by rfl) ⟨6230823, by rfl⟩ : syracuseStep 16615529 = 12461647) B12461647
theorem B2959543 : Blo 1295966 2959543 := bstep (se 1 (by rfl) ⟨2219657, by rfl⟩ : syracuseStep 2959543 = 4439315) B4439315
theorem B6228211 : Blo 1295966 6228211 := bstep (se 1 (by rfl) ⟨4671158, by rfl⟩ : syracuseStep 6228211 = 9342317) B9342317
theorem B2918663 : Blo 1295966 2918663 := bstep (se 1 (by rfl) ⟨2188997, by rfl⟩ : syracuseStep 2918663 = 4377995) B4377995
theorem B2189801 : Blo 1295966 2189801 := bstep (se 2 (by rfl) ⟨821175, by rfl⟩ : syracuseStep 2189801 = 1642351) B1642351
theorem B7883315 : Blo 1295966 7883315 := bstep (se 1 (by rfl) ⟨5912486, by rfl⟩ : syracuseStep 7883315 = 11824973) B11824973
theorem B8309303 : Blo 1295966 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B1297103 : Blo 1295966 1297103 := bstep (se 1 (by rfl) ⟨972827, by rfl⟩ : syracuseStep 1297103 = 1945655) B1945655
theorem B1944347 : Blo 1295966 1944347 := bstep (se 1 (by rfl) ⟨1458260, by rfl⟩ : syracuseStep 1944347 = 2916521) B2916521
theorem B1297263 : Blo 1295966 1297263 := bstep (se 1 (by rfl) ⟨972947, by rfl⟩ : syracuseStep 1297263 = 1945895) B1945895
theorem B1944743 : Blo 1295966 1944743 := bstep (se 1 (by rfl) ⟨1458557, by rfl⟩ : syracuseStep 1944743 = 2917115) B2917115
theorem B1297711 : Blo 1295966 1297711 := bstep (se 1 (by rfl) ⟨973283, by rfl⟩ : syracuseStep 1297711 = 1946567) B1946567
theorem B2919743 : Blo 1295966 2919743 := bstep (se 1 (by rfl) ⟨2189807, by rfl⟩ : syracuseStep 2919743 = 4379615) B4379615
theorem B5254727 : Blo 1295966 5254727 := bstep (se 1 (by rfl) ⟨3941045, by rfl⟩ : syracuseStep 5254727 = 7882091) B7882091
theorem B1945199 : Blo 1295966 1945199 := bstep (se 1 (by rfl) ⟨1458899, by rfl⟩ : syracuseStep 1945199 = 2917799) B2917799
theorem B1945247 : Blo 1295966 1945247 := bstep (se 1 (by rfl) ⟨1458935, by rfl⟩ : syracuseStep 1945247 = 2917871) B2917871
theorem B9842471 : Blo 1295966 9842471 := bstep (se 1 (by rfl) ⟨7381853, by rfl⟩ : syracuseStep 9842471 = 14763707) B14763707
theorem B4378535 : Blo 1295966 4378535 := bstep (se 1 (by rfl) ⟨3283901, by rfl⟩ : syracuseStep 4378535 = 6567803) B6567803
theorem B1945577 : Blo 1295966 1945577 := bstep (se 2 (by rfl) ⟨729591, by rfl⟩ : syracuseStep 1945577 = 1459183) B1459183
theorem B1945631 : Blo 1295966 1945631 := bstep (se 1 (by rfl) ⟨1459223, by rfl⟩ : syracuseStep 1945631 = 2918447) B2918447
theorem B82063469 : Blo 1295966 82063469 := bstep (se 3 (by rfl) ⟨15386900, by rfl⟩ : syracuseStep 82063469 = 30773801) B30773801
theorem B1945721 : Blo 1295966 1945721 := bstep (se 2 (by rfl) ⟨729645, by rfl⟩ : syracuseStep 1945721 = 1459291) B1459291
theorem B1945769 : Blo 1295966 1945769 := bstep (se 2 (by rfl) ⟨729663, by rfl⟩ : syracuseStep 1945769 = 1459327) B1459327
theorem B4378859 : Blo 1295966 4378859 := bstep (se 1 (by rfl) ⟨3284144, by rfl⟩ : syracuseStep 4378859 = 6568289) B6568289
theorem B1945979 : Blo 1295966 1945979 := bstep (se 1 (by rfl) ⟨1459484, by rfl⟩ : syracuseStep 1945979 = 2918969) B2918969
theorem B6230479 : Blo 1295966 6230479 := bstep (se 1 (by rfl) ⟨4672859, by rfl⟩ : syracuseStep 6230479 = 9345719) B9345719
theorem B1946087 : Blo 1295966 1946087 := bstep (se 1 (by rfl) ⟨1459565, by rfl⟩ : syracuseStep 1946087 = 2919131) B2919131
theorem B1946111 : Blo 1295966 1946111 := bstep (se 1 (by rfl) ⟨1459583, by rfl⟩ : syracuseStep 1946111 = 2919167) B2919167
theorem B9843443 : Blo 1295966 9843443 := bstep (se 1 (by rfl) ⟨7382582, by rfl⟩ : syracuseStep 9843443 = 14765165) B14765165
theorem B1946459 : Blo 1295966 1946459 := bstep (se 1 (by rfl) ⟨1459844, by rfl⟩ : syracuseStep 1946459 = 2919689) B2919689
theorem B31527791 : Blo 1295966 31527791 := bstep (se 1 (by rfl) ⟨23645843, by rfl⟩ : syracuseStep 31527791 = 47291687) B47291687
theorem B68334803 : Blo 1295966 68334803 := bstep (se 1 (by rfl) ⟨51251102, by rfl⟩ : syracuseStep 68334803 = 102502205) B102502205
theorem B1946927 : Blo 1295966 1946927 := bstep (se 1 (by rfl) ⟨1460195, by rfl⟩ : syracuseStep 1946927 = 2920391) B2920391
theorem B4380155 : Blo 1295966 4380155 := bstep (se 1 (by rfl) ⟨3285116, by rfl⟩ : syracuseStep 4380155 = 6570233) B6570233
theorem B7886425 : Blo 1295966 7886425 := bstep (se 2 (by rfl) ⟨2957409, by rfl⟩ : syracuseStep 7886425 = 5914819) B5914819
theorem B2078345 : Blo 1295966 2078345 := bstep (se 2 (by rfl) ⟨779379, by rfl⟩ : syracuseStep 2078345 = 1558759) B1558759
theorem B106452893 : Blo 1295966 106452893 := bstep (se 3 (by rfl) ⟨19959917, by rfl⟩ : syracuseStep 106452893 = 39919835) B39919835
theorem B3283193 : Blo 1295966 3283193 := bstep (se 2 (by rfl) ⟨1231197, by rfl⟩ : syracuseStep 3283193 = 2462395) B2462395
theorem B39942497 : Blo 1295966 39942497 := bstep (se 2 (by rfl) ⟨14978436, by rfl⟩ : syracuseStep 39942497 = 29956873) B29956873
theorem B47970913 : Blo 1295966 47970913 := bstep (se 2 (by rfl) ⟨17989092, by rfl⟩ : syracuseStep 47970913 = 35978185) B35978185
theorem B1751977 : Blo 1295966 1751977 := bstep (se 2 (by rfl) ⟨656991, by rfl⟩ : syracuseStep 1751977 = 1313983) B1313983
theorem B3284459 : Blo 1295966 3284459 := bstep (se 1 (by rfl) ⟨2463344, by rfl⟩ : syracuseStep 3284459 = 4926689) B4926689
theorem B21331457 : Blo 1295966 21331457 := bstep (se 2 (by rfl) ⟨7999296, by rfl⟩ : syracuseStep 21331457 = 15998593) B15998593
theorem B1801831 : Blo 1295966 1801831 := bstep (se 1 (by rfl) ⟨1351373, by rfl⟩ : syracuseStep 1801831 = 2702747) B2702747
theorem B4153319 : Blo 1295966 4153319 := bstep (se 1 (by rfl) ⟨3114989, by rfl⟩ : syracuseStep 4153319 = 6229979) B6229979
theorem B6562295 : Blo 1295966 6562295 := bstep (se 1 (by rfl) ⟨4921721, by rfl⟩ : syracuseStep 6562295 = 9843443) B9843443
theorem B8307305 : Blo 1295966 8307305 := bstep (se 2 (by rfl) ⟨3115239, by rfl⟩ : syracuseStep 8307305 = 6230479) B6230479
theorem B45556535 : Blo 1295966 45556535 := bstep (se 1 (by rfl) ⟨34167401, by rfl⟩ : syracuseStep 45556535 = 68334803) B68334803
theorem B5915551 : Blo 1295966 5915551 := bstep (se 1 (by rfl) ⟨4436663, by rfl⟩ : syracuseStep 5915551 = 8873327) B8873327
theorem B106513325 : Blo 1295966 106513325 := bstep (se 3 (by rfl) ⟨19971248, by rfl⟩ : syracuseStep 106513325 = 39942497) B39942497
theorem B2335969 : Blo 1295966 2335969 := bstep (se 2 (by rfl) ⟨875988, by rfl⟩ : syracuseStep 2335969 = 1751977) B1751977
theorem B70968595 : Blo 1295966 70968595 := bstep (se 1 (by rfl) ⟨53226446, by rfl⟩ : syracuseStep 70968595 = 106452893) B106452893
theorem B2917673 : Blo 1295966 2917673 := bstep (se 2 (by rfl) ⟨1094127, by rfl⟩ : syracuseStep 2917673 = 2188255) B2188255
theorem B11077019 : Blo 1295966 11077019 := bstep (se 1 (by rfl) ⟨8307764, by rfl⟩ : syracuseStep 11077019 = 16615529) B16615529
theorem B2188795 : Blo 1295966 2188795 := bstep (se 1 (by rfl) ⟨1641596, by rfl⟩ : syracuseStep 2188795 = 3283193) B3283193
theorem B1459867 : Blo 1295966 1459867 := bstep (se 1 (by rfl) ⟨1094900, by rfl⟩ : syracuseStep 1459867 = 2189801) B2189801
theorem B5539535 : Blo 1295966 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B1296231 : Blo 1295966 1296231 := bstep (se 1 (by rfl) ⟨972173, by rfl⟩ : syracuseStep 1296231 = 1944347) B1944347
theorem B1296495 : Blo 1295966 1296495 := bstep (se 1 (by rfl) ⟨972371, by rfl⟩ : syracuseStep 1296495 = 1944743) B1944743
theorem B2402441 : Blo 1295966 2402441 := bstep (se 2 (by rfl) ⟨900915, by rfl⟩ : syracuseStep 2402441 = 1801831) B1801831
theorem B2189639 : Blo 1295966 2189639 := bstep (se 1 (by rfl) ⟨1642229, by rfl⟩ : syracuseStep 2189639 = 3284459) B3284459
theorem B2918753 : Blo 1295966 2918753 := bstep (se 2 (by rfl) ⟨1094532, by rfl⟩ : syracuseStep 2918753 = 2189065) B2189065
theorem B1296799 : Blo 1295966 1296799 := bstep (se 1 (by rfl) ⟨972599, by rfl⟩ : syracuseStep 1296799 = 1945199) B1945199
theorem B1296831 : Blo 1295966 1296831 := bstep (se 1 (by rfl) ⟨972623, by rfl⟩ : syracuseStep 1296831 = 1945247) B1945247
theorem B2919023 : Blo 1295966 2919023 := bstep (se 1 (by rfl) ⟨2189267, by rfl⟩ : syracuseStep 2919023 = 4378535) B4378535
theorem B1297051 : Blo 1295966 1297051 := bstep (se 1 (by rfl) ⟨972788, by rfl⟩ : syracuseStep 1297051 = 1945577) B1945577
theorem B1297087 : Blo 1295966 1297087 := bstep (se 1 (by rfl) ⟨972815, by rfl⟩ : syracuseStep 1297087 = 1945631) B1945631
theorem B54708979 : Blo 1295966 54708979 := bstep (se 1 (by rfl) ⟨41031734, by rfl⟩ : syracuseStep 54708979 = 82063469) B82063469
theorem B1297147 : Blo 1295966 1297147 := bstep (se 1 (by rfl) ⟨972860, by rfl⟩ : syracuseStep 1297147 = 1945721) B1945721
theorem B1297179 : Blo 1295966 1297179 := bstep (se 1 (by rfl) ⟨972884, by rfl⟩ : syracuseStep 1297179 = 1945769) B1945769
theorem B2919239 : Blo 1295966 2919239 := bstep (se 1 (by rfl) ⟨2189429, by rfl⟩ : syracuseStep 2919239 = 4378859) B4378859
theorem B7383905 : Blo 1295966 7383905 := bstep (se 2 (by rfl) ⟨2768964, by rfl⟩ : syracuseStep 7383905 = 5537929) B5537929
theorem B1297319 : Blo 1295966 1297319 := bstep (se 1 (by rfl) ⟨972989, by rfl⟩ : syracuseStep 1297319 = 1945979) B1945979
theorem B127871945 : Blo 1295966 127871945 := bstep (se 2 (by rfl) ⟨47951979, by rfl⟩ : syracuseStep 127871945 = 95903959) B95903959
theorem B1297391 : Blo 1295966 1297391 := bstep (se 1 (by rfl) ⟨973043, by rfl⟩ : syracuseStep 1297391 = 1946087) B1946087
theorem B1297407 : Blo 1295966 1297407 := bstep (se 1 (by rfl) ⟨973055, by rfl⟩ : syracuseStep 1297407 = 1946111) B1946111
theorem B1403935 : Blo 1295966 1403935 := bstep (se 1 (by rfl) ⟨1052951, by rfl⟩ : syracuseStep 1403935 = 2105903) B2105903
theorem B1297639 : Blo 1295966 1297639 := bstep (se 1 (by rfl) ⟨973229, by rfl⟩ : syracuseStep 1297639 = 1946459) B1946459
theorem B37932421 : Blo 1295966 37932421 := bstep (se 4 (by rfl) ⟨3556164, by rfl⟩ : syracuseStep 37932421 = 7112329) B7112329
theorem B1297951 : Blo 1295966 1297951 := bstep (se 1 (by rfl) ⟨973463, by rfl⟩ : syracuseStep 1297951 = 1946927) B1946927
theorem B2920103 : Blo 1295966 2920103 := bstep (se 1 (by rfl) ⟨2190077, by rfl⟩ : syracuseStep 2920103 = 4380155) B4380155
theorem B4927463 : Blo 1295966 4927463 := bstep (se 1 (by rfl) ⟨3695597, by rfl⟩ : syracuseStep 4927463 = 7391195) B7391195
theorem B1945775 : Blo 1295966 1945775 := bstep (se 1 (by rfl) ⟨1459331, by rfl⟩ : syracuseStep 1945775 = 2918663) B2918663
theorem B14012605 : Blo 1295966 14012605 := bstep (se 3 (by rfl) ⟨2627363, by rfl⟩ : syracuseStep 14012605 = 5254727) B5254727
theorem B5542253 : Blo 1295966 5542253 := bstep (se 3 (by rfl) ⟨1039172, by rfl⟩ : syracuseStep 5542253 = 2078345) B2078345
theorem B5255543 : Blo 1295966 5255543 := bstep (se 1 (by rfl) ⟨3941657, by rfl⟩ : syracuseStep 5255543 = 7883315) B7883315
theorem B10515233 : Blo 1295966 10515233 := bstep (se 2 (by rfl) ⟨3943212, by rfl⟩ : syracuseStep 10515233 = 7886425) B7886425
theorem B1946495 : Blo 1295966 1946495 := bstep (se 1 (by rfl) ⟨1459871, by rfl⟩ : syracuseStep 1946495 = 2919743) B2919743
theorem B6313555 : Blo 1295966 6313555 := bstep (se 1 (by rfl) ⟨4735166, by rfl⟩ : syracuseStep 6313555 = 9470333) B9470333
theorem B4380263 : Blo 1295966 4380263 := bstep (se 1 (by rfl) ⟨3285197, by rfl⟩ : syracuseStep 4380263 = 6570395) B6570395
theorem B8304281 : Blo 1295966 8304281 := bstep (se 2 (by rfl) ⟨3114105, by rfl⟩ : syracuseStep 8304281 = 6228211) B6228211
theorem B3282727 : Blo 1295966 3282727 := bstep (se 1 (by rfl) ⟨2462045, by rfl⟩ : syracuseStep 3282727 = 4924091) B4924091
theorem B21018527 : Blo 1295966 21018527 := bstep (se 1 (by rfl) ⟨15763895, by rfl⟩ : syracuseStep 21018527 = 31527791) B31527791
theorem B63961217 : Blo 1295966 63961217 := bstep (se 2 (by rfl) ⟨23985456, by rfl⟩ : syracuseStep 63961217 = 47970913) B47970913
theorem B8312969 : Blo 1295966 8312969 := bstep (se 2 (by rfl) ⟨3117363, by rfl⟩ : syracuseStep 8312969 = 6234727) B6234727
theorem B15784229 : Blo 1295966 15784229 := bstep (se 4 (by rfl) ⟨1479771, by rfl⟩ : syracuseStep 15784229 = 2959543) B2959543
theorem B3283355 : Blo 1295966 3283355 := bstep (se 1 (by rfl) ⟨2462516, by rfl⟩ : syracuseStep 3283355 = 4925033) B4925033
theorem B9854621 : Blo 1295966 9854621 := bstep (se 3 (by rfl) ⟨1847741, by rfl⟩ : syracuseStep 9854621 = 3695483) B3695483
theorem B14220971 : Blo 1295966 14220971 := bstep (se 1 (by rfl) ⟨10665728, by rfl⟩ : syracuseStep 14220971 = 21331457) B21331457
theorem B6561647 : Blo 1295966 6561647 := bstep (se 1 (by rfl) ⟨4921235, by rfl⟩ : syracuseStep 6561647 = 9842471) B9842471
theorem B2768879 : Blo 1295966 2768879 := bstep (se 1 (by rfl) ⟨2076659, by rfl⟩ : syracuseStep 2768879 = 4153319) B4153319
theorem B7487653 : Blo 1295966 7487653 := bstep (se 4 (by rfl) ⟨701967, by rfl⟩ : syracuseStep 7487653 = 1403935) B1403935
theorem B3694835 : Blo 1295966 3694835 := bstep (se 1 (by rfl) ⟨2771126, by rfl⟩ : syracuseStep 3694835 = 5542253) B5542253
theorem B4374863 : Blo 1295966 4374863 := bstep (se 1 (by rfl) ⟨3281147, by rfl⟩ : syracuseStep 4374863 = 6562295) B6562295
theorem B5538203 : Blo 1295966 5538203 := bstep (se 1 (by rfl) ⟨4153652, by rfl⟩ : syracuseStep 5538203 = 8307305) B8307305
theorem B71008883 : Blo 1295966 71008883 := bstep (se 1 (by rfl) ⟨53256662, by rfl⟩ : syracuseStep 71008883 = 106513325) B106513325
theorem B42640811 : Blo 1295966 42640811 := bstep (se 1 (by rfl) ⟨31980608, by rfl⟩ : syracuseStep 42640811 = 63961217) B63961217
theorem B1459759 : Blo 1295966 1459759 := bstep (se 1 (by rfl) ⟨1094819, by rfl⟩ : syracuseStep 1459759 = 2189639) B2189639
theorem B2188903 : Blo 1295966 2188903 := bstep (se 1 (by rfl) ⟨1641677, by rfl⟩ : syracuseStep 2188903 = 3283355) B3283355
theorem B3114625 : Blo 1295966 3114625 := bstep (se 2 (by rfl) ⟨1167984, by rfl⟩ : syracuseStep 3114625 = 2335969) B2335969
theorem B85247963 : Blo 1295966 85247963 := bstep (se 1 (by rfl) ⟨63935972, by rfl⟩ : syracuseStep 85247963 = 127871945) B127871945
theorem B2918393 : Blo 1295966 2918393 := bstep (se 2 (by rfl) ⟨1094397, by rfl⟩ : syracuseStep 2918393 = 2188795) B2188795
theorem B4376969 : Blo 1295966 4376969 := bstep (se 2 (by rfl) ⟨1641363, by rfl⟩ : syracuseStep 4376969 = 3282727) B3282727
theorem B9480647 : Blo 1295966 9480647 := bstep (se 1 (by rfl) ⟨7110485, by rfl⟩ : syracuseStep 9480647 = 14220971) B14220971
theorem B1845919 : Blo 1295966 1845919 := bstep (se 1 (by rfl) ⟨1384439, by rfl⟩ : syracuseStep 1845919 = 2768879) B2768879
theorem B1297183 : Blo 1295966 1297183 := bstep (se 1 (by rfl) ⟨972887, by rfl⟩ : syracuseStep 1297183 = 1945775) B1945775
theorem B30371023 : Blo 1295966 30371023 := bstep (se 1 (by rfl) ⟨22778267, by rfl⟩ : syracuseStep 30371023 = 45556535) B45556535
theorem B1297663 : Blo 1295966 1297663 := bstep (se 1 (by rfl) ⟨973247, by rfl⟩ : syracuseStep 1297663 = 1946495) B1946495
theorem B1945115 : Blo 1295966 1945115 := bstep (se 1 (by rfl) ⟨1458836, by rfl⟩ : syracuseStep 1945115 = 2917673) B2917673
theorem B7384679 : Blo 1295966 7384679 := bstep (se 1 (by rfl) ⟨5538509, by rfl⟩ : syracuseStep 7384679 = 11077019) B11077019
theorem B72945305 : Blo 1295966 72945305 := bstep (se 2 (by rfl) ⟨27354489, by rfl⟩ : syracuseStep 72945305 = 54708979) B54708979
theorem B2920175 : Blo 1295966 2920175 := bstep (se 1 (by rfl) ⟨2190131, by rfl⟩ : syracuseStep 2920175 = 4380263) B4380263
theorem B14012351 : Blo 1295966 14012351 := bstep (se 1 (by rfl) ⟨10509263, by rfl⟩ : syracuseStep 14012351 = 21018527) B21018527
theorem B5541979 : Blo 1295966 5541979 := bstep (se 1 (by rfl) ⟨4156484, by rfl⟩ : syracuseStep 5541979 = 8312969) B8312969
theorem B1601627 : Blo 1295966 1601627 := bstep (se 1 (by rfl) ⟨1201220, by rfl⟩ : syracuseStep 1601627 = 2402441) B2402441
theorem B10522819 : Blo 1295966 10522819 := bstep (se 1 (by rfl) ⟨7892114, by rfl⟩ : syracuseStep 10522819 = 15784229) B15784229
theorem B1945835 : Blo 1295966 1945835 := bstep (se 1 (by rfl) ⟨1459376, by rfl⟩ : syracuseStep 1945835 = 2918753) B2918753
theorem B1946015 : Blo 1295966 1946015 := bstep (se 1 (by rfl) ⟨1459511, by rfl⟩ : syracuseStep 1946015 = 2919023) B2919023
theorem B1946159 : Blo 1295966 1946159 := bstep (se 1 (by rfl) ⟨1459619, by rfl⟩ : syracuseStep 1946159 = 2919239) B2919239
theorem B8418073 : Blo 1295966 8418073 := bstep (se 2 (by rfl) ⟨3156777, by rfl⟩ : syracuseStep 8418073 = 6313555) B6313555
theorem B1946489 : Blo 1295966 1946489 := bstep (se 2 (by rfl) ⟨729933, by rfl⟩ : syracuseStep 1946489 = 1459867) B1459867
theorem B1946735 : Blo 1295966 1946735 := bstep (se 1 (by rfl) ⟨1460051, by rfl⟩ : syracuseStep 1946735 = 2920103) B2920103
theorem B3503695 : Blo 1295966 3503695 := bstep (se 1 (by rfl) ⟨2627771, by rfl⟩ : syracuseStep 3503695 = 5255543) B5255543
theorem B18683473 : Blo 1295966 18683473 := bstep (se 2 (by rfl) ⟨7006302, by rfl⟩ : syracuseStep 18683473 = 14012605) B14012605
theorem B7010155 : Blo 1295966 7010155 := bstep (se 1 (by rfl) ⟨5257616, by rfl⟩ : syracuseStep 7010155 = 10515233) B10515233
theorem B5536187 : Blo 1295966 5536187 := bstep (se 1 (by rfl) ⟨4152140, by rfl⟩ : syracuseStep 5536187 = 8304281) B8304281
theorem B3693023 : Blo 1295966 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B7887401 : Blo 1295966 7887401 := bstep (se 2 (by rfl) ⟨2957775, by rfl⟩ : syracuseStep 7887401 = 5915551) B5915551
theorem B94624793 : Blo 1295966 94624793 := bstep (se 2 (by rfl) ⟨35484297, by rfl⟩ : syracuseStep 94624793 = 70968595) B70968595
theorem B50576561 : Blo 1295966 50576561 := bstep (se 2 (by rfl) ⟨18966210, by rfl⟩ : syracuseStep 50576561 = 37932421) B37932421
theorem B4922603 : Blo 1295966 4922603 := bstep (se 1 (by rfl) ⟨3691952, by rfl⟩ : syracuseStep 4922603 = 7383905) B7383905
theorem B6569747 : Blo 1295966 6569747 := bstep (se 1 (by rfl) ⟨4927310, by rfl⟩ : syracuseStep 6569747 = 9854621) B9854621
theorem B4374431 : Blo 1295966 4374431 := bstep (se 1 (by rfl) ⟨3280823, by rfl⟩ : syracuseStep 4374431 = 6561647) B6561647
theorem B3284975 : Blo 1295966 3284975 := bstep (se 1 (by rfl) ⟨2463731, by rfl⟩ : syracuseStep 3284975 = 4927463) B4927463
theorem B7389305 : Blo 1295966 7389305 := bstep (se 2 (by rfl) ⟨2770989, by rfl⟩ : syracuseStep 7389305 = 5541979) B5541979
theorem B2916575 : Blo 1295966 2916575 := bstep (se 1 (by rfl) ⟨2187431, by rfl⟩ : syracuseStep 2916575 = 4374863) B4374863
theorem B28427207 : Blo 1295966 28427207 := bstep (se 1 (by rfl) ⟨21320405, by rfl⟩ : syracuseStep 28427207 = 42640811) B42640811
theorem B11224097 : Blo 1295966 11224097 := bstep (se 2 (by rfl) ⟨4209036, by rfl⟩ : syracuseStep 11224097 = 8418073) B8418073
theorem B2917979 : Blo 1295966 2917979 := bstep (se 1 (by rfl) ⟨2188484, by rfl⟩ : syracuseStep 2917979 = 4376969) B4376969
theorem B40494697 : Blo 1295966 40494697 := bstep (se 2 (by rfl) ⟨15185511, by rfl⟩ : syracuseStep 40494697 = 30371023) B30371023
theorem B4671593 : Blo 1295966 4671593 := bstep (se 2 (by rfl) ⟨1751847, by rfl⟩ : syracuseStep 4671593 = 3503695) B3503695
theorem B2918537 : Blo 1295966 2918537 := bstep (se 2 (by rfl) ⟨1094451, by rfl⟩ : syracuseStep 2918537 = 2188903) B2188903
theorem B1296743 : Blo 1295966 1296743 := bstep (se 1 (by rfl) ⟨972557, by rfl⟩ : syracuseStep 1296743 = 1945115) B1945115
theorem B48630203 : Blo 1295966 48630203 := bstep (se 1 (by rfl) ⟨36472652, by rfl⟩ : syracuseStep 48630203 = 72945305) B72945305
theorem B9341567 : Blo 1295966 9341567 := bstep (se 1 (by rfl) ⟨7006175, by rfl⟩ : syracuseStep 9341567 = 14012351) B14012351
theorem B2189983 : Blo 1295966 2189983 := bstep (se 1 (by rfl) ⟨1642487, by rfl⟩ : syracuseStep 2189983 = 3284975) B3284975
theorem B1297223 : Blo 1295966 1297223 := bstep (se 1 (by rfl) ⟨972917, by rfl⟩ : syracuseStep 1297223 = 1945835) B1945835
theorem B4271005 : Blo 1295966 4271005 := bstep (se 3 (by rfl) ⟨800813, by rfl⟩ : syracuseStep 4271005 = 1601627) B1601627
theorem B1297343 : Blo 1295966 1297343 := bstep (se 1 (by rfl) ⟨973007, by rfl⟩ : syracuseStep 1297343 = 1946015) B1946015
theorem B1297439 : Blo 1295966 1297439 := bstep (se 1 (by rfl) ⟨973079, by rfl⟩ : syracuseStep 1297439 = 1946159) B1946159
theorem B1297659 : Blo 1295966 1297659 := bstep (se 1 (by rfl) ⟨973244, by rfl⟩ : syracuseStep 1297659 = 1946489) B1946489
theorem B1297823 : Blo 1295966 1297823 := bstep (se 1 (by rfl) ⟨973367, by rfl⟩ : syracuseStep 1297823 = 1946735) B1946735
theorem B56831975 : Blo 1295966 56831975 := bstep (se 1 (by rfl) ⟨42623981, by rfl⟩ : syracuseStep 56831975 = 85247963) B85247963
theorem B1945595 : Blo 1295966 1945595 := bstep (se 1 (by rfl) ⟨1459196, by rfl⟩ : syracuseStep 1945595 = 2918393) B2918393
theorem B3690791 : Blo 1295966 3690791 := bstep (se 1 (by rfl) ⟨2768093, by rfl⟩ : syracuseStep 3690791 = 5536187) B5536187
theorem B6320431 : Blo 1295966 6320431 := bstep (se 1 (by rfl) ⟨4740323, by rfl⟩ : syracuseStep 6320431 = 9480647) B9480647
theorem B2462015 : Blo 1295966 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B63083195 : Blo 1295966 63083195 := bstep (se 1 (by rfl) ⟨47312396, by rfl⟩ : syracuseStep 63083195 = 94624793) B94624793
theorem B1946345 : Blo 1295966 1946345 := bstep (se 2 (by rfl) ⟨729879, by rfl⟩ : syracuseStep 1946345 = 1459759) B1459759
theorem B3281735 : Blo 1295966 3281735 := bstep (se 1 (by rfl) ⟨2461301, by rfl⟩ : syracuseStep 3281735 = 4922603) B4922603
theorem B1946783 : Blo 1295966 1946783 := bstep (se 1 (by rfl) ⟨1460087, by rfl⟩ : syracuseStep 1946783 = 2920175) B2920175
theorem B4379831 : Blo 1295966 4379831 := bstep (se 1 (by rfl) ⟨3284873, by rfl⟩ : syracuseStep 4379831 = 6569747) B6569747
theorem B2463223 : Blo 1295966 2463223 := bstep (se 1 (by rfl) ⟨1847417, by rfl⟩ : syracuseStep 2463223 = 3694835) B3694835
theorem B9983537 : Blo 1295966 9983537 := bstep (se 2 (by rfl) ⟨3743826, by rfl⟩ : syracuseStep 9983537 = 7487653) B7487653
theorem B14030425 : Blo 1295966 14030425 := bstep (se 2 (by rfl) ⟨5261409, by rfl⟩ : syracuseStep 14030425 = 10522819) B10522819
theorem B3692135 : Blo 1295966 3692135 := bstep (se 1 (by rfl) ⟨2769101, by rfl⟩ : syracuseStep 3692135 = 5538203) B5538203
theorem B47339255 : Blo 1295966 47339255 := bstep (se 1 (by rfl) ⟨35504441, by rfl⟩ : syracuseStep 47339255 = 71008883) B71008883
theorem B9844901 : Blo 1295966 9844901 := bstep (se 4 (by rfl) ⟨922959, by rfl⟩ : syracuseStep 9844901 = 1845919) B1845919
theorem B5258267 : Blo 1295966 5258267 := bstep (se 1 (by rfl) ⟨3943700, by rfl⟩ : syracuseStep 5258267 = 7887401) B7887401
theorem B24911297 : Blo 1295966 24911297 := bstep (se 2 (by rfl) ⟨9341736, by rfl⟩ : syracuseStep 24911297 = 18683473) B18683473
theorem B33717707 : Blo 1295966 33717707 := bstep (se 1 (by rfl) ⟨25288280, by rfl⟩ : syracuseStep 33717707 = 50576561) B50576561
theorem B4152833 : Blo 1295966 4152833 := bstep (se 2 (by rfl) ⟨1557312, by rfl⟩ : syracuseStep 4152833 = 3114625) B3114625
theorem B4923119 : Blo 1295966 4923119 := bstep (se 1 (by rfl) ⟨3692339, by rfl⟩ : syracuseStep 4923119 = 7384679) B7384679
theorem B9346873 : Blo 1295966 9346873 := bstep (se 2 (by rfl) ⟨3505077, by rfl⟩ : syracuseStep 9346873 = 7010155) B7010155
theorem B2916287 : Blo 1295966 2916287 := bstep (se 1 (by rfl) ⟨2187215, by rfl⟩ : syracuseStep 2916287 = 4374431) B4374431
theorem B2187823 : Blo 1295966 2187823 := bstep (se 1 (by rfl) ⟨1640867, by rfl⟩ : syracuseStep 2187823 = 3281735) B3281735
theorem B5694673 : Blo 1295966 5694673 := bstep (se 2 (by rfl) ⟨2135502, by rfl⟩ : syracuseStep 5694673 = 4271005) B4271005
theorem B3114395 : Blo 1295966 3114395 := bstep (se 1 (by rfl) ⟨2335796, by rfl⟩ : syracuseStep 3114395 = 4671593) B4671593
theorem B6563267 : Blo 1295966 6563267 := bstep (se 1 (by rfl) ⟨4922450, by rfl⟩ : syracuseStep 6563267 = 9844901) B9844901
theorem B6227711 : Blo 1295966 6227711 := bstep (se 1 (by rfl) ⟨4670783, by rfl⟩ : syracuseStep 6227711 = 9341567) B9341567
theorem B16607531 : Blo 1295966 16607531 := bstep (se 1 (by rfl) ⟨12455648, by rfl⟩ : syracuseStep 16607531 = 24911297) B24911297
theorem B12462497 : Blo 1295966 12462497 := bstep (se 2 (by rfl) ⟨4673436, by rfl⟩ : syracuseStep 12462497 = 9346873) B9346873
theorem B1944191 : Blo 1295966 1944191 := bstep (se 1 (by rfl) ⟨1458143, by rfl⟩ : syracuseStep 1944191 = 2916287) B2916287
theorem B1297063 : Blo 1295966 1297063 := bstep (se 1 (by rfl) ⟨972797, by rfl⟩ : syracuseStep 1297063 = 1945595) B1945595
theorem B4926203 : Blo 1295966 4926203 := bstep (se 1 (by rfl) ⟨3694652, by rfl⟩ : syracuseStep 4926203 = 7389305) B7389305
theorem B1944383 : Blo 1295966 1944383 := bstep (se 1 (by rfl) ⟨1458287, by rfl⟩ : syracuseStep 1944383 = 2916575) B2916575
theorem B2460527 : Blo 1295966 2460527 := bstep (se 1 (by rfl) ⟨1845395, by rfl⟩ : syracuseStep 2460527 = 3690791) B3690791
theorem B1297563 : Blo 1295966 1297563 := bstep (se 1 (by rfl) ⟨973172, by rfl⟩ : syracuseStep 1297563 = 1946345) B1946345
theorem B7482731 : Blo 1295966 7482731 := bstep (se 1 (by rfl) ⟨5612048, by rfl⟩ : syracuseStep 7482731 = 11224097) B11224097
theorem B1297855 : Blo 1295966 1297855 := bstep (se 1 (by rfl) ⟨973391, by rfl⟩ : syracuseStep 1297855 = 1946783) B1946783
theorem B2919887 : Blo 1295966 2919887 := bstep (se 1 (by rfl) ⟨2189915, by rfl⟩ : syracuseStep 2919887 = 4379831) B4379831
theorem B6565373 : Blo 1295966 6565373 := bstep (se 3 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 6565373 = 2462015) B2462015
theorem B2919977 : Blo 1295966 2919977 := bstep (se 2 (by rfl) ⟨1094991, by rfl⟩ : syracuseStep 2919977 = 2189983) B2189983
theorem B6655691 : Blo 1295966 6655691 := bstep (se 1 (by rfl) ⟨4991768, by rfl⟩ : syracuseStep 6655691 = 9983537) B9983537
theorem B1945319 : Blo 1295966 1945319 := bstep (se 1 (by rfl) ⟨1458989, by rfl⟩ : syracuseStep 1945319 = 2917979) B2917979
theorem B2461423 : Blo 1295966 2461423 := bstep (se 1 (by rfl) ⟨1846067, by rfl⟩ : syracuseStep 2461423 = 3692135) B3692135
theorem B31559503 : Blo 1295966 31559503 := bstep (se 1 (by rfl) ⟨23669627, by rfl⟩ : syracuseStep 31559503 = 47339255) B47339255
theorem B1945691 : Blo 1295966 1945691 := bstep (se 1 (by rfl) ⟨1459268, by rfl⟩ : syracuseStep 1945691 = 2918537) B2918537
theorem B32420135 : Blo 1295966 32420135 := bstep (se 1 (by rfl) ⟨24315101, by rfl⟩ : syracuseStep 32420135 = 48630203) B48630203
theorem B18707233 : Blo 1295966 18707233 := bstep (se 2 (by rfl) ⟨7015212, by rfl⟩ : syracuseStep 18707233 = 14030425) B14030425
theorem B3282079 : Blo 1295966 3282079 := bstep (se 1 (by rfl) ⟨2461559, by rfl⟩ : syracuseStep 3282079 = 4923119) B4923119
theorem B75805885 : Blo 1295966 75805885 := bstep (se 3 (by rfl) ⟨14213603, by rfl⟩ : syracuseStep 75805885 = 28427207) B28427207
theorem B8427241 : Blo 1295966 8427241 := bstep (se 2 (by rfl) ⟨3160215, by rfl⟩ : syracuseStep 8427241 = 6320431) B6320431
theorem B42055463 : Blo 1295966 42055463 := bstep (se 1 (by rfl) ⟨31541597, by rfl⟩ : syracuseStep 42055463 = 63083195) B63083195
theorem B215971717 : Blo 1295966 215971717 := bstep (se 4 (by rfl) ⟨20247348, by rfl⟩ : syracuseStep 215971717 = 40494697) B40494697
theorem B3284297 : Blo 1295966 3284297 := bstep (se 2 (by rfl) ⟨1231611, by rfl⟩ : syracuseStep 3284297 = 2463223) B2463223
theorem B3505511 : Blo 1295966 3505511 := bstep (se 1 (by rfl) ⟨2629133, by rfl⟩ : syracuseStep 3505511 = 5258267) B5258267
theorem B22478471 : Blo 1295966 22478471 := bstep (se 1 (by rfl) ⟨16858853, by rfl⟩ : syracuseStep 22478471 = 33717707) B33717707
theorem B2768555 : Blo 1295966 2768555 := bstep (se 1 (by rfl) ⟨2076416, by rfl⟩ : syracuseStep 2768555 = 4152833) B4152833
theorem B37887983 : Blo 1295966 37887983 := bstep (se 1 (by rfl) ⟨28415987, by rfl⟩ : syracuseStep 37887983 = 56831975) B56831975
theorem B2917097 : Blo 1295966 2917097 := bstep (se 2 (by rfl) ⟨1093911, by rfl⟩ : syracuseStep 2917097 = 2187823) B2187823
theorem B4375511 : Blo 1295966 4375511 := bstep (se 1 (by rfl) ⟨3281633, by rfl⟩ : syracuseStep 4375511 = 6563267) B6563267
theorem B4376105 : Blo 1295966 4376105 := bstep (se 2 (by rfl) ⟨1641039, by rfl⟩ : syracuseStep 4376105 = 3282079) B3282079
theorem B101074513 : Blo 1295966 101074513 := bstep (se 2 (by rfl) ⟨37902942, by rfl⟩ : syracuseStep 101074513 = 75805885) B75805885
theorem B8308331 : Blo 1295966 8308331 := bstep (se 1 (by rfl) ⟨6231248, by rfl⟩ : syracuseStep 8308331 = 12462497) B12462497
theorem B1296127 : Blo 1295966 1296127 := bstep (se 1 (by rfl) ⟨972095, by rfl⟩ : syracuseStep 1296127 = 1944191) B1944191
theorem B1296255 : Blo 1295966 1296255 := bstep (se 1 (by rfl) ⟨972191, by rfl⟩ : syracuseStep 1296255 = 1944383) B1944383
theorem B1640351 : Blo 1295966 1640351 := bstep (se 1 (by rfl) ⟨1230263, by rfl⟩ : syracuseStep 1640351 = 2460527) B2460527
theorem B2189531 : Blo 1295966 2189531 := bstep (se 1 (by rfl) ⟨1642148, by rfl⟩ : syracuseStep 2189531 = 3284297) B3284297
theorem B2337007 : Blo 1295966 2337007 := bstep (se 1 (by rfl) ⟨1752755, by rfl⟩ : syracuseStep 2337007 = 3505511) B3505511
theorem B4376915 : Blo 1295966 4376915 := bstep (se 1 (by rfl) ⟨3282686, by rfl⟩ : syracuseStep 4376915 = 6565373) B6565373
theorem B14985647 : Blo 1295966 14985647 := bstep (se 1 (by rfl) ⟨11239235, by rfl⟩ : syracuseStep 14985647 = 22478471) B22478471
theorem B1845703 : Blo 1295966 1845703 := bstep (se 1 (by rfl) ⟨1384277, by rfl⟩ : syracuseStep 1845703 = 2768555) B2768555
theorem B1296879 : Blo 1295966 1296879 := bstep (se 1 (by rfl) ⟨972659, by rfl⟩ : syracuseStep 1296879 = 1945319) B1945319
theorem B25258655 : Blo 1295966 25258655 := bstep (se 1 (by rfl) ⟨18943991, by rfl⟩ : syracuseStep 25258655 = 37887983) B37887983
theorem B1297127 : Blo 1295966 1297127 := bstep (se 1 (by rfl) ⟨972845, by rfl⟩ : syracuseStep 1297127 = 1945691) B1945691
theorem B21613423 : Blo 1295966 21613423 := bstep (se 1 (by rfl) ⟨16210067, by rfl⟩ : syracuseStep 21613423 = 32420135) B32420135
theorem B2076263 : Blo 1295966 2076263 := bstep (se 1 (by rfl) ⟨1557197, by rfl⟩ : syracuseStep 2076263 = 3114395) B3114395
theorem B28036975 : Blo 1295966 28036975 := bstep (se 1 (by rfl) ⟨21027731, by rfl⟩ : syracuseStep 28036975 = 42055463) B42055463
theorem B44945285 : Blo 1295966 44945285 := bstep (se 4 (by rfl) ⟨4213620, by rfl⟩ : syracuseStep 44945285 = 8427241) B8427241
theorem B11071687 : Blo 1295966 11071687 := bstep (se 1 (by rfl) ⟨8303765, by rfl⟩ : syracuseStep 11071687 = 16607531) B16607531
theorem B1946591 : Blo 1295966 1946591 := bstep (se 1 (by rfl) ⟨1459943, by rfl⟩ : syracuseStep 1946591 = 2919887) B2919887
theorem B3281897 : Blo 1295966 3281897 := bstep (se 2 (by rfl) ⟨1230711, by rfl⟩ : syracuseStep 3281897 = 2461423) B2461423
theorem B1946651 : Blo 1295966 1946651 := bstep (se 1 (by rfl) ⟨1459988, by rfl⟩ : syracuseStep 1946651 = 2919977) B2919977
theorem B42079337 : Blo 1295966 42079337 := bstep (se 2 (by rfl) ⟨15779751, by rfl⟩ : syracuseStep 42079337 = 31559503) B31559503
theorem B4437127 : Blo 1295966 4437127 := bstep (se 1 (by rfl) ⟨3327845, by rfl⟩ : syracuseStep 4437127 = 6655691) B6655691
theorem B287962289 : Blo 1295966 287962289 := bstep (se 2 (by rfl) ⟨107985858, by rfl⟩ : syracuseStep 287962289 = 215971717) B215971717
theorem B19953949 : Blo 1295966 19953949 := bstep (se 3 (by rfl) ⟨3741365, by rfl⟩ : syracuseStep 19953949 = 7482731) B7482731
theorem B24942977 : Blo 1295966 24942977 := bstep (se 2 (by rfl) ⟨9353616, by rfl⟩ : syracuseStep 24942977 = 18707233) B18707233
theorem B4151807 : Blo 1295966 4151807 := bstep (se 1 (by rfl) ⟨3113855, by rfl⟩ : syracuseStep 4151807 = 6227711) B6227711
theorem B7592897 : Blo 1295966 7592897 := bstep (se 2 (by rfl) ⟨2847336, by rfl⟩ : syracuseStep 7592897 = 5694673) B5694673
theorem B3284135 : Blo 1295966 3284135 := bstep (se 1 (by rfl) ⟨2463101, by rfl⟩ : syracuseStep 3284135 = 4926203) B4926203
theorem B14762249 : Blo 1295966 14762249 := bstep (se 2 (by rfl) ⟨5535843, by rfl⟩ : syracuseStep 14762249 = 11071687) B11071687
theorem B2917007 : Blo 1295966 2917007 := bstep (se 1 (by rfl) ⟨2187755, by rfl⟩ : syracuseStep 2917007 = 4375511) B4375511
theorem B2187931 : Blo 1295966 2187931 := bstep (se 1 (by rfl) ⟨1640948, by rfl⟩ : syracuseStep 2187931 = 3281897) B3281897
theorem B2917403 : Blo 1295966 2917403 := bstep (se 1 (by rfl) ⟨2188052, by rfl⟩ : syracuseStep 2917403 = 4376105) B4376105
theorem B5538887 : Blo 1295966 5538887 := bstep (se 1 (by rfl) ⟨4154165, by rfl⟩ : syracuseStep 5538887 = 8308331) B8308331
theorem B1459687 : Blo 1295966 1459687 := bstep (se 1 (by rfl) ⟨1094765, by rfl⟩ : syracuseStep 1459687 = 2189531) B2189531
theorem B5916169 : Blo 1295966 5916169 := bstep (se 2 (by rfl) ⟨2218563, by rfl⟩ : syracuseStep 5916169 = 4437127) B4437127
theorem B2917943 : Blo 1295966 2917943 := bstep (se 1 (by rfl) ⟨2188457, by rfl⟩ : syracuseStep 2917943 = 4376915) B4376915
theorem B2189423 : Blo 1295966 2189423 := bstep (se 1 (by rfl) ⟨1642067, by rfl⟩ : syracuseStep 2189423 = 3284135) B3284135
theorem B37382633 : Blo 1295966 37382633 := bstep (se 2 (by rfl) ⟨14018487, by rfl⟩ : syracuseStep 37382633 = 28036975) B28036975
theorem B3116009 : Blo 1295966 3116009 := bstep (se 2 (by rfl) ⟨1168503, by rfl⟩ : syracuseStep 3116009 = 2337007) B2337007
theorem B1944731 : Blo 1295966 1944731 := bstep (se 1 (by rfl) ⟨1458548, by rfl⟩ : syracuseStep 1944731 = 2917097) B2917097
theorem B2460937 : Blo 1295966 2460937 := bstep (se 2 (by rfl) ⟨922851, by rfl⟩ : syracuseStep 2460937 = 1845703) B1845703
theorem B1297727 : Blo 1295966 1297727 := bstep (se 1 (by rfl) ⟨973295, by rfl⟩ : syracuseStep 1297727 = 1946591) B1946591
theorem B1297767 : Blo 1295966 1297767 := bstep (se 1 (by rfl) ⟨973325, by rfl⟩ : syracuseStep 1297767 = 1946651) B1946651
theorem B28052891 : Blo 1295966 28052891 := bstep (se 1 (by rfl) ⟨21039668, by rfl⟩ : syracuseStep 28052891 = 42079337) B42079337
theorem B191974859 : Blo 1295966 191974859 := bstep (se 1 (by rfl) ⟨143981144, by rfl⟩ : syracuseStep 191974859 = 287962289) B287962289
theorem B9990431 : Blo 1295966 9990431 := bstep (se 1 (by rfl) ⟨7492823, by rfl⟩ : syracuseStep 9990431 = 14985647) B14985647
theorem B16839103 : Blo 1295966 16839103 := bstep (se 1 (by rfl) ⟨12629327, by rfl⟩ : syracuseStep 16839103 = 25258655) B25258655
theorem B119854093 : Blo 1295966 119854093 := bstep (se 3 (by rfl) ⟨22472642, by rfl⟩ : syracuseStep 119854093 = 44945285) B44945285
theorem B20247725 : Blo 1295966 20247725 := bstep (se 3 (by rfl) ⟨3796448, by rfl⟩ : syracuseStep 20247725 = 7592897) B7592897
theorem B26605265 : Blo 1295966 26605265 := bstep (se 2 (by rfl) ⟨9976974, by rfl⟩ : syracuseStep 26605265 = 19953949) B19953949
theorem B28817897 : Blo 1295966 28817897 := bstep (se 2 (by rfl) ⟨10806711, by rfl⟩ : syracuseStep 28817897 = 21613423) B21613423
theorem B16628651 : Blo 1295966 16628651 := bstep (se 1 (by rfl) ⟨12471488, by rfl⟩ : syracuseStep 16628651 = 24942977) B24942977
theorem B2767871 : Blo 1295966 2767871 := bstep (se 1 (by rfl) ⟨2075903, by rfl⟩ : syracuseStep 2767871 = 4151807) B4151807
theorem B134766017 : Blo 1295966 134766017 := bstep (se 2 (by rfl) ⟨50537256, by rfl⟩ : syracuseStep 134766017 = 101074513) B101074513
theorem B1384175 : Blo 1295966 1384175 := bstep (se 1 (by rfl) ⟨1038131, by rfl⟩ : syracuseStep 1384175 = 2076263) B2076263
theorem B4374269 : Blo 1295966 4374269 := bstep (se 3 (by rfl) ⟨820175, by rfl⟩ : syracuseStep 4374269 = 1640351) B1640351
theorem B6660287 : Blo 1295966 6660287 := bstep (se 1 (by rfl) ⟨4995215, by rfl⟩ : syracuseStep 6660287 = 9990431) B9990431
theorem B2917241 : Blo 1295966 2917241 := bstep (se 2 (by rfl) ⟨1093965, by rfl⟩ : syracuseStep 2917241 = 2187931) B2187931
theorem B1459615 : Blo 1295966 1459615 := bstep (se 1 (by rfl) ⟨1094711, by rfl⟩ : syracuseStep 1459615 = 2189423) B2189423
theorem B24921755 : Blo 1295966 24921755 := bstep (se 1 (by rfl) ⟨18691316, by rfl⟩ : syracuseStep 24921755 = 37382633) B37382633
theorem B11085767 : Blo 1295966 11085767 := bstep (se 1 (by rfl) ⟨8314325, by rfl⟩ : syracuseStep 11085767 = 16628651) B16628651
theorem B1296487 : Blo 1295966 1296487 := bstep (se 1 (by rfl) ⟨972365, by rfl⟩ : syracuseStep 1296487 = 1944731) B1944731
theorem B283789493 : Blo 1295966 283789493 := bstep (se 5 (by rfl) ⟨13302632, by rfl⟩ : syracuseStep 283789493 = 26605265) B26605265
theorem B89844011 : Blo 1295966 89844011 := bstep (se 1 (by rfl) ⟨67383008, by rfl⟩ : syracuseStep 89844011 = 134766017) B134766017
theorem B9841499 : Blo 1295966 9841499 := bstep (se 1 (by rfl) ⟨7381124, by rfl⟩ : syracuseStep 9841499 = 14762249) B14762249
theorem B1944671 : Blo 1295966 1944671 := bstep (se 1 (by rfl) ⟨1458503, by rfl⟩ : syracuseStep 1944671 = 2917007) B2917007
theorem B1944935 : Blo 1295966 1944935 := bstep (se 1 (by rfl) ⟨1458701, by rfl⟩ : syracuseStep 1944935 = 2917403) B2917403
theorem B1945295 : Blo 1295966 1945295 := bstep (se 1 (by rfl) ⟨1458971, by rfl⟩ : syracuseStep 1945295 = 2917943) B2917943
theorem B159805457 : Blo 1295966 159805457 := bstep (se 2 (by rfl) ⟨59927046, by rfl⟩ : syracuseStep 159805457 = 119854093) B119854093
theorem B3281249 : Blo 1295966 3281249 := bstep (se 2 (by rfl) ⟨1230468, by rfl⟩ : syracuseStep 3281249 = 2460937) B2460937
theorem B3691133 : Blo 1295966 3691133 := bstep (se 3 (by rfl) ⟨692087, by rfl⟩ : syracuseStep 3691133 = 1384175) B1384175
theorem B1946249 : Blo 1295966 1946249 := bstep (se 2 (by rfl) ⟨729843, by rfl⟩ : syracuseStep 1946249 = 1459687) B1459687
theorem B2077339 : Blo 1295966 2077339 := bstep (se 1 (by rfl) ⟨1558004, by rfl⟩ : syracuseStep 2077339 = 3116009) B3116009
theorem B22452137 : Blo 1295966 22452137 := bstep (se 2 (by rfl) ⟨8419551, by rfl⟩ : syracuseStep 22452137 = 16839103) B16839103
theorem B3692591 : Blo 1295966 3692591 := bstep (se 1 (by rfl) ⟨2769443, by rfl⟩ : syracuseStep 3692591 = 5538887) B5538887
theorem B13498483 : Blo 1295966 13498483 := bstep (se 1 (by rfl) ⟨10123862, by rfl⟩ : syracuseStep 13498483 = 20247725) B20247725
theorem B76847725 : Blo 1295966 76847725 := bstep (se 3 (by rfl) ⟨14408948, by rfl⟩ : syracuseStep 76847725 = 28817897) B28817897
theorem B7888225 : Blo 1295966 7888225 := bstep (se 2 (by rfl) ⟨2958084, by rfl⟩ : syracuseStep 7888225 = 5916169) B5916169
theorem B18701927 : Blo 1295966 18701927 := bstep (se 1 (by rfl) ⟨14026445, by rfl⟩ : syracuseStep 18701927 = 28052891) B28052891
theorem B127983239 : Blo 1295966 127983239 := bstep (se 1 (by rfl) ⟨95987429, by rfl⟩ : syracuseStep 127983239 = 191974859) B191974859
theorem B2916179 : Blo 1295966 2916179 := bstep (se 1 (by rfl) ⟨2187134, by rfl⟩ : syracuseStep 2916179 = 4374269) B4374269
theorem B7380989 : Blo 1295966 7380989 := bstep (se 3 (by rfl) ⟨1383935, by rfl⟩ : syracuseStep 7380989 = 2767871) B2767871
theorem B106536971 : Blo 1295966 106536971 := bstep (se 1 (by rfl) ⟨79902728, by rfl⟩ : syracuseStep 106536971 = 159805457) B159805457
theorem B4440191 : Blo 1295966 4440191 := bstep (se 1 (by rfl) ⟨3330143, by rfl⟩ : syracuseStep 4440191 = 6660287) B6660287
theorem B17997977 : Blo 1295966 17997977 := bstep (se 2 (by rfl) ⟨6749241, by rfl⟩ : syracuseStep 17997977 = 13498483) B13498483
theorem B2187499 : Blo 1295966 2187499 := bstep (se 1 (by rfl) ⟨1640624, by rfl⟩ : syracuseStep 2187499 = 3281249) B3281249
theorem B2769785 : Blo 1295966 2769785 := bstep (se 2 (by rfl) ⟨1038669, by rfl⟩ : syracuseStep 2769785 = 2077339) B2077339
theorem B16614503 : Blo 1295966 16614503 := bstep (se 1 (by rfl) ⟨12460877, by rfl⟩ : syracuseStep 16614503 = 24921755) B24921755
theorem B14968091 : Blo 1295966 14968091 := bstep (se 1 (by rfl) ⟨11226068, by rfl⟩ : syracuseStep 14968091 = 22452137) B22452137
theorem B7390511 : Blo 1295966 7390511 := bstep (se 1 (by rfl) ⟨5542883, by rfl⟩ : syracuseStep 7390511 = 11085767) B11085767
theorem B1296447 : Blo 1295966 1296447 := bstep (se 1 (by rfl) ⟨972335, by rfl⟩ : syracuseStep 1296447 = 1944671) B1944671
theorem B1296623 : Blo 1295966 1296623 := bstep (se 1 (by rfl) ⟨972467, by rfl⟩ : syracuseStep 1296623 = 1944935) B1944935
theorem B85322159 : Blo 1295966 85322159 := bstep (se 1 (by rfl) ⟨63991619, by rfl⟩ : syracuseStep 85322159 = 127983239) B127983239
theorem B1296863 : Blo 1295966 1296863 := bstep (se 1 (by rfl) ⟨972647, by rfl⟩ : syracuseStep 1296863 = 1945295) B1945295
theorem B1944119 : Blo 1295966 1944119 := bstep (se 1 (by rfl) ⟨1458089, by rfl⟩ : syracuseStep 1944119 = 2916179) B2916179
theorem B2460755 : Blo 1295966 2460755 := bstep (se 1 (by rfl) ⟨1845566, by rfl⟩ : syracuseStep 2460755 = 3691133) B3691133
theorem B1297499 : Blo 1295966 1297499 := bstep (se 1 (by rfl) ⟨973124, by rfl⟩ : syracuseStep 1297499 = 1946249) B1946249
theorem B1944827 : Blo 1295966 1944827 := bstep (se 1 (by rfl) ⟨1458620, by rfl⟩ : syracuseStep 1944827 = 2917241) B2917241
theorem B2461727 : Blo 1295966 2461727 := bstep (se 1 (by rfl) ⟨1846295, by rfl⟩ : syracuseStep 2461727 = 3692591) B3692591
theorem B59896007 : Blo 1295966 59896007 := bstep (se 1 (by rfl) ⟨44922005, by rfl⟩ : syracuseStep 59896007 = 89844011) B89844011
theorem B1946153 : Blo 1295966 1946153 := bstep (se 2 (by rfl) ⟨729807, by rfl⟩ : syracuseStep 1946153 = 1459615) B1459615
theorem B4920659 : Blo 1295966 4920659 := bstep (se 1 (by rfl) ⟨3690494, by rfl⟩ : syracuseStep 4920659 = 7380989) B7380989
theorem B102463633 : Blo 1295966 102463633 := bstep (se 2 (by rfl) ⟨38423862, by rfl⟩ : syracuseStep 102463633 = 76847725) B76847725
theorem B189192995 : Blo 1295966 189192995 := bstep (se 1 (by rfl) ⟨141894746, by rfl⟩ : syracuseStep 189192995 = 283789493) B283789493
theorem B10517633 : Blo 1295966 10517633 := bstep (se 2 (by rfl) ⟨3944112, by rfl⟩ : syracuseStep 10517633 = 7888225) B7888225
theorem B6560999 : Blo 1295966 6560999 := bstep (se 1 (by rfl) ⟨4920749, by rfl⟩ : syracuseStep 6560999 = 9841499) B9841499
theorem B12467951 : Blo 1295966 12467951 := bstep (se 1 (by rfl) ⟨9350963, by rfl⟩ : syracuseStep 12467951 = 18701927) B18701927
theorem B71024647 : Blo 1295966 71024647 := bstep (se 1 (by rfl) ⟨53268485, by rfl⟩ : syracuseStep 71024647 = 106536971) B106536971
theorem B136618177 : Blo 1295966 136618177 := bstep (se 2 (by rfl) ⟨51231816, by rfl⟩ : syracuseStep 136618177 = 102463633) B102463633
theorem B2916665 : Blo 1295966 2916665 := bstep (se 2 (by rfl) ⟨1093749, by rfl⟩ : syracuseStep 2916665 = 2187499) B2187499
theorem B11076335 : Blo 1295966 11076335 := bstep (se 1 (by rfl) ⟨8307251, by rfl⟩ : syracuseStep 11076335 = 16614503) B16614503
theorem B9978727 : Blo 1295966 9978727 := bstep (se 1 (by rfl) ⟨7484045, by rfl⟩ : syracuseStep 9978727 = 14968091) B14968091
theorem B1296079 : Blo 1295966 1296079 := bstep (se 1 (by rfl) ⟨972059, by rfl⟩ : syracuseStep 1296079 = 1944119) B1944119
theorem B1640503 : Blo 1295966 1640503 := bstep (se 1 (by rfl) ⟨1230377, by rfl⟩ : syracuseStep 1640503 = 2460755) B2460755
theorem B1296551 : Blo 1295966 1296551 := bstep (se 1 (by rfl) ⟨972413, by rfl⟩ : syracuseStep 1296551 = 1944827) B1944827
theorem B1641151 : Blo 1295966 1641151 := bstep (se 1 (by rfl) ⟨1230863, by rfl⟩ : syracuseStep 1641151 = 2461727) B2461727
theorem B39930671 : Blo 1295966 39930671 := bstep (se 1 (by rfl) ⟨29948003, by rfl⟩ : syracuseStep 39930671 = 59896007) B59896007
theorem B11840509 : Blo 1295966 11840509 := bstep (se 3 (by rfl) ⟨2220095, by rfl⟩ : syracuseStep 11840509 = 4440191) B4440191
theorem B1297435 : Blo 1295966 1297435 := bstep (se 1 (by rfl) ⟨973076, by rfl⟩ : syracuseStep 1297435 = 1946153) B1946153
theorem B1846523 : Blo 1295966 1846523 := bstep (se 1 (by rfl) ⟨1384892, by rfl⟩ : syracuseStep 1846523 = 2769785) B2769785
theorem B4927007 : Blo 1295966 4927007 := bstep (se 1 (by rfl) ⟨3695255, by rfl⟩ : syracuseStep 4927007 = 7390511) B7390511
theorem B3280439 : Blo 1295966 3280439 := bstep (se 1 (by rfl) ⟨2460329, by rfl⟩ : syracuseStep 3280439 = 4920659) B4920659
theorem B56881439 : Blo 1295966 56881439 := bstep (se 1 (by rfl) ⟨42661079, by rfl⟩ : syracuseStep 56881439 = 85322159) B85322159
theorem B126128663 : Blo 1295966 126128663 := bstep (se 1 (by rfl) ⟨94596497, by rfl⟩ : syracuseStep 126128663 = 189192995) B189192995
theorem B8311967 : Blo 1295966 8311967 := bstep (se 1 (by rfl) ⟨6233975, by rfl⟩ : syracuseStep 8311967 = 12467951) B12467951
theorem B47994605 : Blo 1295966 47994605 := bstep (se 3 (by rfl) ⟨8998988, by rfl⟩ : syracuseStep 47994605 = 17997977) B17997977
theorem B7011755 : Blo 1295966 7011755 := bstep (se 1 (by rfl) ⟨5258816, by rfl⟩ : syracuseStep 7011755 = 10517633) B10517633
theorem B4373999 : Blo 1295966 4373999 := bstep (se 1 (by rfl) ⟨3280499, by rfl⟩ : syracuseStep 4373999 = 6560999) B6560999
theorem B94699529 : Blo 1295966 94699529 := bstep (se 2 (by rfl) ⟨35512323, by rfl⟩ : syracuseStep 94699529 = 71024647) B71024647
theorem B2187337 : Blo 1295966 2187337 := bstep (se 2 (by rfl) ⟨820251, by rfl⟩ : syracuseStep 2187337 = 1640503) B1640503
theorem B37920959 : Blo 1295966 37920959 := bstep (se 1 (by rfl) ⟨28440719, by rfl⟩ : syracuseStep 37920959 = 56881439) B56881439
theorem B182157569 : Blo 1295966 182157569 := bstep (se 2 (by rfl) ⟨68309088, by rfl⟩ : syracuseStep 182157569 = 136618177) B136618177
theorem B4924061 : Blo 1295966 4924061 := bstep (se 3 (by rfl) ⟨923261, by rfl⟩ : syracuseStep 4924061 = 1846523) B1846523
theorem B2188201 : Blo 1295966 2188201 := bstep (se 2 (by rfl) ⟨820575, by rfl⟩ : syracuseStep 2188201 = 1641151) B1641151
theorem B13304969 : Blo 1295966 13304969 := bstep (se 2 (by rfl) ⟨4989363, by rfl⟩ : syracuseStep 13304969 = 9978727) B9978727
theorem B15787345 : Blo 1295966 15787345 := bstep (se 2 (by rfl) ⟨5920254, by rfl⟩ : syracuseStep 15787345 = 11840509) B11840509
theorem B1944443 : Blo 1295966 1944443 := bstep (se 1 (by rfl) ⟨1458332, by rfl⟩ : syracuseStep 1944443 = 2916665) B2916665
theorem B84085775 : Blo 1295966 84085775 := bstep (se 1 (by rfl) ⟨63064331, by rfl⟩ : syracuseStep 84085775 = 126128663) B126128663
theorem B7384223 : Blo 1295966 7384223 := bstep (se 1 (by rfl) ⟨5538167, by rfl⟩ : syracuseStep 7384223 = 11076335) B11076335
theorem B5541311 : Blo 1295966 5541311 := bstep (se 1 (by rfl) ⟨4155983, by rfl⟩ : syracuseStep 5541311 = 8311967) B8311967
theorem B26620447 : Blo 1295966 26620447 := bstep (se 1 (by rfl) ⟨19965335, by rfl⟩ : syracuseStep 26620447 = 39930671) B39930671
theorem B4674503 : Blo 1295966 4674503 := bstep (se 1 (by rfl) ⟨3505877, by rfl⟩ : syracuseStep 4674503 = 7011755) B7011755
theorem B31996403 : Blo 1295966 31996403 := bstep (se 1 (by rfl) ⟨23997302, by rfl⟩ : syracuseStep 31996403 = 47994605) B47994605
theorem B2915999 : Blo 1295966 2915999 := bstep (se 1 (by rfl) ⟨2186999, by rfl⟩ : syracuseStep 2915999 = 4373999) B4373999
theorem B3284671 : Blo 1295966 3284671 := bstep (se 1 (by rfl) ⟨2463503, by rfl⟩ : syracuseStep 3284671 = 4927007) B4927007
theorem B2186959 : Blo 1295966 2186959 := bstep (se 1 (by rfl) ⟨1640219, by rfl⟩ : syracuseStep 2186959 = 3280439) B3280439
theorem B2916449 : Blo 1295966 2916449 := bstep (se 2 (by rfl) ⟨1093668, by rfl⟩ : syracuseStep 2916449 = 2187337) B2187337
theorem B25280639 : Blo 1295966 25280639 := bstep (se 1 (by rfl) ⟨18960479, by rfl⟩ : syracuseStep 25280639 = 37920959) B37920959
theorem B121438379 : Blo 1295966 121438379 := bstep (se 1 (by rfl) ⟨91078784, by rfl⟩ : syracuseStep 121438379 = 182157569) B182157569
theorem B2917601 : Blo 1295966 2917601 := bstep (se 2 (by rfl) ⟨1094100, by rfl⟩ : syracuseStep 2917601 = 2188201) B2188201
theorem B1296295 : Blo 1295966 1296295 := bstep (se 1 (by rfl) ⟨972221, by rfl⟩ : syracuseStep 1296295 = 1944443) B1944443
theorem B1943999 : Blo 1295966 1943999 := bstep (se 1 (by rfl) ⟨1457999, by rfl⟩ : syracuseStep 1943999 = 2915999) B2915999
theorem B3116335 : Blo 1295966 3116335 := bstep (se 1 (by rfl) ⟨2337251, by rfl⟩ : syracuseStep 3116335 = 4674503) B4674503
theorem B21049793 : Blo 1295966 21049793 := bstep (se 2 (by rfl) ⟨7893672, by rfl⟩ : syracuseStep 21049793 = 15787345) B15787345
theorem B4379561 : Blo 1295966 4379561 := bstep (se 2 (by rfl) ⟨1642335, by rfl⟩ : syracuseStep 4379561 = 3284671) B3284671
theorem B63133019 : Blo 1295966 63133019 := bstep (se 1 (by rfl) ⟨47349764, by rfl⟩ : syracuseStep 63133019 = 94699529) B94699529
theorem B3282707 : Blo 1295966 3282707 := bstep (se 1 (by rfl) ⟨2462030, by rfl⟩ : syracuseStep 3282707 = 4924061) B4924061
theorem B35493929 : Blo 1295966 35493929 := bstep (se 2 (by rfl) ⟨13310223, by rfl⟩ : syracuseStep 35493929 = 26620447) B26620447
theorem B8869979 : Blo 1295966 8869979 := bstep (se 1 (by rfl) ⟨6652484, by rfl⟩ : syracuseStep 8869979 = 13304969) B13304969
theorem B14776829 : Blo 1295966 14776829 := bstep (se 3 (by rfl) ⟨2770655, by rfl⟩ : syracuseStep 14776829 = 5541311) B5541311
theorem B21330935 : Blo 1295966 21330935 := bstep (se 1 (by rfl) ⟨15998201, by rfl⟩ : syracuseStep 21330935 = 31996403) B31996403
theorem B56057183 : Blo 1295966 56057183 := bstep (se 1 (by rfl) ⟨42042887, by rfl⟩ : syracuseStep 56057183 = 84085775) B84085775
theorem B4922815 : Blo 1295966 4922815 := bstep (se 1 (by rfl) ⟨3692111, by rfl⟩ : syracuseStep 4922815 = 7384223) B7384223
theorem B2915945 : Blo 1295966 2915945 := bstep (se 2 (by rfl) ⟨1093479, by rfl⟩ : syracuseStep 2915945 = 2186959) B2186959
theorem B14033195 : Blo 1295966 14033195 := bstep (se 1 (by rfl) ⟨10524896, by rfl⟩ : syracuseStep 14033195 = 21049793) B21049793
theorem B2188471 : Blo 1295966 2188471 := bstep (se 1 (by rfl) ⟨1641353, by rfl⟩ : syracuseStep 2188471 = 3282707) B3282707
theorem B1295999 : Blo 1295966 1295999 := bstep (se 1 (by rfl) ⟨971999, by rfl⟩ : syracuseStep 1295999 = 1943999) B1943999
theorem B4155113 : Blo 1295966 4155113 := bstep (se 2 (by rfl) ⟨1558167, by rfl⟩ : syracuseStep 4155113 = 3116335) B3116335
theorem B6563753 : Blo 1295966 6563753 := bstep (se 2 (by rfl) ⟨2461407, by rfl⟩ : syracuseStep 6563753 = 4922815) B4922815
theorem B1943963 : Blo 1295966 1943963 := bstep (se 1 (by rfl) ⟨1457972, by rfl⟩ : syracuseStep 1943963 = 2915945) B2915945
theorem B1944299 : Blo 1295966 1944299 := bstep (se 1 (by rfl) ⟨1458224, by rfl⟩ : syracuseStep 1944299 = 2916449) B2916449
theorem B16853759 : Blo 1295966 16853759 := bstep (se 1 (by rfl) ⟨12640319, by rfl⟩ : syracuseStep 16853759 = 25280639) B25280639
theorem B23653277 : Blo 1295966 23653277 := bstep (se 3 (by rfl) ⟨4434989, by rfl⟩ : syracuseStep 23653277 = 8869979) B8869979
theorem B2919707 : Blo 1295966 2919707 := bstep (se 1 (by rfl) ⟨2189780, by rfl⟩ : syracuseStep 2919707 = 4379561) B4379561
theorem B1945067 : Blo 1295966 1945067 := bstep (se 1 (by rfl) ⟨1458800, by rfl⟩ : syracuseStep 1945067 = 2917601) B2917601
theorem B23662619 : Blo 1295966 23662619 := bstep (se 1 (by rfl) ⟨17746964, by rfl⟩ : syracuseStep 23662619 = 35493929) B35493929
theorem B9851219 : Blo 1295966 9851219 := bstep (se 1 (by rfl) ⟨7388414, by rfl⟩ : syracuseStep 9851219 = 14776829) B14776829
theorem B80958919 : Blo 1295966 80958919 := bstep (se 1 (by rfl) ⟨60719189, by rfl⟩ : syracuseStep 80958919 = 121438379) B121438379
theorem B42088679 : Blo 1295966 42088679 := bstep (se 1 (by rfl) ⟨31566509, by rfl⟩ : syracuseStep 42088679 = 63133019) B63133019
theorem B14220623 : Blo 1295966 14220623 := bstep (se 1 (by rfl) ⟨10665467, by rfl⟩ : syracuseStep 14220623 = 21330935) B21330935
theorem B37371455 : Blo 1295966 37371455 := bstep (se 1 (by rfl) ⟨28028591, by rfl⟩ : syracuseStep 37371455 = 56057183) B56057183
theorem B9355463 : Blo 1295966 9355463 := bstep (se 1 (by rfl) ⟨7016597, by rfl⟩ : syracuseStep 9355463 = 14033195) B14033195
theorem B2770075 : Blo 1295966 2770075 := bstep (se 1 (by rfl) ⟨2077556, by rfl⟩ : syracuseStep 2770075 = 4155113) B4155113
theorem B4375835 : Blo 1295966 4375835 := bstep (se 1 (by rfl) ⟨3281876, by rfl⟩ : syracuseStep 4375835 = 6563753) B6563753
theorem B28059119 : Blo 1295966 28059119 := bstep (se 1 (by rfl) ⟨21044339, by rfl⟩ : syracuseStep 28059119 = 42088679) B42088679
theorem B2917961 : Blo 1295966 2917961 := bstep (se 2 (by rfl) ⟨1094235, by rfl⟩ : syracuseStep 2917961 = 2188471) B2188471
theorem B1295975 : Blo 1295966 1295975 := bstep (se 1 (by rfl) ⟨971981, by rfl⟩ : syracuseStep 1295975 = 1943963) B1943963
theorem B1296199 : Blo 1295966 1296199 := bstep (se 1 (by rfl) ⟨972149, by rfl⟩ : syracuseStep 1296199 = 1944299) B1944299
theorem B9480415 : Blo 1295966 9480415 := bstep (se 1 (by rfl) ⟨7110311, by rfl⟩ : syracuseStep 9480415 = 14220623) B14220623
theorem B1296711 : Blo 1295966 1296711 := bstep (se 1 (by rfl) ⟨972533, by rfl⟩ : syracuseStep 1296711 = 1945067) B1945067
theorem B24914303 : Blo 1295966 24914303 := bstep (se 1 (by rfl) ⟨18685727, by rfl⟩ : syracuseStep 24914303 = 37371455) B37371455
theorem B11235839 : Blo 1295966 11235839 := bstep (se 1 (by rfl) ⟨8426879, by rfl⟩ : syracuseStep 11235839 = 16853759) B16853759
theorem B1946471 : Blo 1295966 1946471 := bstep (se 1 (by rfl) ⟨1459853, by rfl⟩ : syracuseStep 1946471 = 2919707) B2919707
theorem B15775079 : Blo 1295966 15775079 := bstep (se 1 (by rfl) ⟨11831309, by rfl⟩ : syracuseStep 15775079 = 23662619) B23662619
theorem B6567479 : Blo 1295966 6567479 := bstep (se 1 (by rfl) ⟨4925609, by rfl⟩ : syracuseStep 6567479 = 9851219) B9851219
theorem B107945225 : Blo 1295966 107945225 := bstep (se 2 (by rfl) ⟨40479459, by rfl⟩ : syracuseStep 107945225 = 80958919) B80958919
theorem B15768851 : Blo 1295966 15768851 := bstep (se 1 (by rfl) ⟨11826638, by rfl⟩ : syracuseStep 15768851 = 23653277) B23653277
theorem B12640553 : Blo 1295966 12640553 := bstep (se 2 (by rfl) ⟨4740207, by rfl⟩ : syracuseStep 12640553 = 9480415) B9480415
theorem B42050269 : Blo 1295966 42050269 := bstep (se 3 (by rfl) ⟨7884425, by rfl⟩ : syracuseStep 42050269 = 15768851) B15768851
theorem B2917223 : Blo 1295966 2917223 := bstep (se 1 (by rfl) ⟨2187917, by rfl⟩ : syracuseStep 2917223 = 4375835) B4375835
theorem B42066877 : Blo 1295966 42066877 := bstep (se 3 (by rfl) ⟨7887539, by rfl⟩ : syracuseStep 42066877 = 15775079) B15775079
theorem B6236975 : Blo 1295966 6236975 := bstep (se 1 (by rfl) ⟨4677731, by rfl⟩ : syracuseStep 6236975 = 9355463) B9355463
theorem B1297647 : Blo 1295966 1297647 := bstep (se 1 (by rfl) ⟨973235, by rfl⟩ : syracuseStep 1297647 = 1946471) B1946471
theorem B18706079 : Blo 1295966 18706079 := bstep (se 1 (by rfl) ⟨14029559, by rfl⟩ : syracuseStep 18706079 = 28059119) B28059119
theorem B4378319 : Blo 1295966 4378319 := bstep (se 1 (by rfl) ⟨3283739, by rfl⟩ : syracuseStep 4378319 = 6567479) B6567479
theorem B1945307 : Blo 1295966 1945307 := bstep (se 1 (by rfl) ⟨1458980, by rfl⟩ : syracuseStep 1945307 = 2917961) B2917961
theorem B29962237 : Blo 1295966 29962237 := bstep (se 3 (by rfl) ⟨5617919, by rfl⟩ : syracuseStep 29962237 = 11235839) B11235839
theorem B16609535 : Blo 1295966 16609535 := bstep (se 1 (by rfl) ⟨12457151, by rfl⟩ : syracuseStep 16609535 = 24914303) B24914303
theorem B71963483 : Blo 1295966 71963483 := bstep (se 1 (by rfl) ⟨53972612, by rfl⟩ : syracuseStep 71963483 = 107945225) B107945225
theorem B3693433 : Blo 1295966 3693433 := bstep (se 2 (by rfl) ⟨1385037, by rfl⟩ : syracuseStep 3693433 = 2770075) B2770075
theorem B56067025 : Blo 1295966 56067025 := bstep (se 2 (by rfl) ⟨21025134, by rfl⟩ : syracuseStep 56067025 = 42050269) B42050269
theorem B4924577 : Blo 1295966 4924577 := bstep (se 2 (by rfl) ⟨1846716, by rfl⟩ : syracuseStep 4924577 = 3693433) B3693433
theorem B12470719 : Blo 1295966 12470719 := bstep (se 1 (by rfl) ⟨9353039, by rfl⟩ : syracuseStep 12470719 = 18706079) B18706079
theorem B2918879 : Blo 1295966 2918879 := bstep (se 1 (by rfl) ⟨2189159, by rfl⟩ : syracuseStep 2918879 = 4378319) B4378319
theorem B1296871 : Blo 1295966 1296871 := bstep (se 1 (by rfl) ⟨972653, by rfl⟩ : syracuseStep 1296871 = 1945307) B1945307
theorem B1944815 : Blo 1295966 1944815 := bstep (se 1 (by rfl) ⟨1458611, by rfl⟩ : syracuseStep 1944815 = 2917223) B2917223
theorem B4157983 : Blo 1295966 4157983 := bstep (se 1 (by rfl) ⟨3118487, by rfl⟩ : syracuseStep 4157983 = 6236975) B6236975
theorem B191902621 : Blo 1295966 191902621 := bstep (se 3 (by rfl) ⟨35981741, by rfl⟩ : syracuseStep 191902621 = 71963483) B71963483
theorem B39949649 : Blo 1295966 39949649 := bstep (se 2 (by rfl) ⟨14981118, by rfl⟩ : syracuseStep 39949649 = 29962237) B29962237
theorem B11073023 : Blo 1295966 11073023 := bstep (se 1 (by rfl) ⟨8304767, by rfl⟩ : syracuseStep 11073023 = 16609535) B16609535
theorem B8427035 : Blo 1295966 8427035 := bstep (se 1 (by rfl) ⟨6320276, by rfl⟩ : syracuseStep 8427035 = 12640553) B12640553
theorem B56089169 : Blo 1295966 56089169 := bstep (se 2 (by rfl) ⟨21033438, by rfl⟩ : syracuseStep 56089169 = 42066877) B42066877
theorem B26633099 : Blo 1295966 26633099 := bstep (se 1 (by rfl) ⟨19974824, by rfl⟩ : syracuseStep 26633099 = 39949649) B39949649
theorem B7382015 : Blo 1295966 7382015 := bstep (se 1 (by rfl) ⟨5536511, by rfl⟩ : syracuseStep 7382015 = 11073023) B11073023
theorem B255870161 : Blo 1295966 255870161 := bstep (se 2 (by rfl) ⟨95951310, by rfl⟩ : syracuseStep 255870161 = 191902621) B191902621
theorem B22472093 : Blo 1295966 22472093 := bstep (se 3 (by rfl) ⟨4213517, by rfl⟩ : syracuseStep 22472093 = 8427035) B8427035
theorem B1296543 : Blo 1295966 1296543 := bstep (se 1 (by rfl) ⟨972407, by rfl⟩ : syracuseStep 1296543 = 1944815) B1944815
theorem B74756033 : Blo 1295966 74756033 := bstep (se 2 (by rfl) ⟨28033512, by rfl⟩ : syracuseStep 74756033 = 56067025) B56067025
theorem B1945919 : Blo 1295966 1945919 := bstep (se 1 (by rfl) ⟨1459439, by rfl⟩ : syracuseStep 1945919 = 2918879) B2918879
theorem B37392779 : Blo 1295966 37392779 := bstep (se 1 (by rfl) ⟨28044584, by rfl⟩ : syracuseStep 37392779 = 56089169) B56089169
theorem B16627625 : Blo 1295966 16627625 := bstep (se 2 (by rfl) ⟨6235359, by rfl⟩ : syracuseStep 16627625 = 12470719) B12470719
theorem B5543977 : Blo 1295966 5543977 := bstep (se 2 (by rfl) ⟨2078991, by rfl⟩ : syracuseStep 5543977 = 4157983) B4157983
theorem B3283051 : Blo 1295966 3283051 := bstep (se 1 (by rfl) ⟨2462288, by rfl⟩ : syracuseStep 3283051 = 4924577) B4924577
theorem B24928519 : Blo 1295966 24928519 := bstep (se 1 (by rfl) ⟨18696389, by rfl⟩ : syracuseStep 24928519 = 37392779) B37392779
theorem B11085083 : Blo 1295966 11085083 := bstep (se 1 (by rfl) ⟨8313812, by rfl⟩ : syracuseStep 11085083 = 16627625) B16627625
theorem B7391969 : Blo 1295966 7391969 := bstep (se 2 (by rfl) ⟨2771988, by rfl⟩ : syracuseStep 7391969 = 5543977) B5543977
theorem B4377401 : Blo 1295966 4377401 := bstep (se 2 (by rfl) ⟨1641525, by rfl⟩ : syracuseStep 4377401 = 3283051) B3283051
theorem B1297279 : Blo 1295966 1297279 := bstep (se 1 (by rfl) ⟨972959, by rfl⟩ : syracuseStep 1297279 = 1945919) B1945919
theorem B17755399 : Blo 1295966 17755399 := bstep (se 1 (by rfl) ⟨13316549, by rfl⟩ : syracuseStep 17755399 = 26633099) B26633099
theorem B49837355 : Blo 1295966 49837355 := bstep (se 1 (by rfl) ⟨37378016, by rfl⟩ : syracuseStep 49837355 = 74756033) B74756033
theorem B4921343 : Blo 1295966 4921343 := bstep (se 1 (by rfl) ⟨3691007, by rfl⟩ : syracuseStep 4921343 = 7382015) B7382015
theorem B170580107 : Blo 1295966 170580107 := bstep (se 1 (by rfl) ⟨127935080, by rfl⟩ : syracuseStep 170580107 = 255870161) B255870161
theorem B14981395 : Blo 1295966 14981395 := bstep (se 1 (by rfl) ⟨11236046, by rfl⟩ : syracuseStep 14981395 = 22472093) B22472093
theorem B7390055 : Blo 1295966 7390055 := bstep (se 1 (by rfl) ⟨5542541, by rfl⟩ : syracuseStep 7390055 = 11085083) B11085083
theorem B2918267 : Blo 1295966 2918267 := bstep (se 1 (by rfl) ⟨2188700, by rfl⟩ : syracuseStep 2918267 = 4377401) B4377401
theorem B33238025 : Blo 1295966 33238025 := bstep (se 2 (by rfl) ⟨12464259, by rfl⟩ : syracuseStep 33238025 = 24928519) B24928519
theorem B19975193 : Blo 1295966 19975193 := bstep (se 2 (by rfl) ⟨7490697, by rfl⟩ : syracuseStep 19975193 = 14981395) B14981395
theorem B3280895 : Blo 1295966 3280895 := bstep (se 1 (by rfl) ⟨2460671, by rfl⟩ : syracuseStep 3280895 = 4921343) B4921343
theorem B4927979 : Blo 1295966 4927979 := bstep (se 1 (by rfl) ⟨3695984, by rfl⟩ : syracuseStep 4927979 = 7391969) B7391969
theorem B33224903 : Blo 1295966 33224903 := bstep (se 1 (by rfl) ⟨24918677, by rfl⟩ : syracuseStep 33224903 = 49837355) B49837355
theorem B113720071 : Blo 1295966 113720071 := bstep (se 1 (by rfl) ⟨85290053, by rfl⟩ : syracuseStep 113720071 = 170580107) B170580107
theorem B23673865 : Blo 1295966 23673865 := bstep (se 2 (by rfl) ⟨8877699, by rfl⟩ : syracuseStep 23673865 = 17755399) B17755399
theorem B3285319 : Blo 1295966 3285319 := bstep (se 1 (by rfl) ⟨2463989, by rfl⟩ : syracuseStep 3285319 = 4927979) B4927979
theorem B151626761 : Blo 1295966 151626761 := bstep (se 2 (by rfl) ⟨56860035, by rfl⟩ : syracuseStep 151626761 = 113720071) B113720071
theorem B31565153 : Blo 1295966 31565153 := bstep (se 2 (by rfl) ⟨11836932, by rfl⟩ : syracuseStep 31565153 = 23673865) B23673865
theorem B2187263 : Blo 1295966 2187263 := bstep (se 1 (by rfl) ⟨1640447, by rfl⟩ : syracuseStep 2187263 = 3280895) B3280895
theorem B4926703 : Blo 1295966 4926703 := bstep (se 1 (by rfl) ⟨3695027, by rfl⟩ : syracuseStep 4926703 = 7390055) B7390055
theorem B1945511 : Blo 1295966 1945511 := bstep (se 1 (by rfl) ⟨1459133, by rfl⟩ : syracuseStep 1945511 = 2918267) B2918267
theorem B13316795 : Blo 1295966 13316795 := bstep (se 1 (by rfl) ⟨9987596, by rfl⟩ : syracuseStep 13316795 = 19975193) B19975193
theorem B22149935 : Blo 1295966 22149935 := bstep (se 1 (by rfl) ⟨16612451, by rfl⟩ : syracuseStep 22149935 = 33224903) B33224903
theorem B22158683 : Blo 1295966 22158683 := bstep (se 1 (by rfl) ⟨16619012, by rfl⟩ : syracuseStep 22158683 = 33238025) B33238025
theorem B14772455 : Blo 1295966 14772455 := bstep (se 1 (by rfl) ⟨11079341, by rfl⟩ : syracuseStep 14772455 = 22158683) B22158683
theorem B1297007 : Blo 1295966 1297007 := bstep (se 1 (by rfl) ⟨972755, by rfl⟩ : syracuseStep 1297007 = 1945511) B1945511
theorem B101084507 : Blo 1295966 101084507 := bstep (se 1 (by rfl) ⟨75813380, by rfl⟩ : syracuseStep 101084507 = 151626761) B151626761
theorem B14766623 : Blo 1295966 14766623 := bstep (se 1 (by rfl) ⟨11074967, by rfl⟩ : syracuseStep 14766623 = 22149935) B22149935
theorem B4380425 : Blo 1295966 4380425 := bstep (se 2 (by rfl) ⟨1642659, by rfl⟩ : syracuseStep 4380425 = 3285319) B3285319
theorem B8877863 : Blo 1295966 8877863 := bstep (se 1 (by rfl) ⟨6658397, by rfl⟩ : syracuseStep 8877863 = 13316795) B13316795
theorem B21043435 : Blo 1295966 21043435 := bstep (se 1 (by rfl) ⟨15782576, by rfl⟩ : syracuseStep 21043435 = 31565153) B31565153
theorem B6568937 : Blo 1295966 6568937 := bstep (se 2 (by rfl) ⟨2463351, by rfl⟩ : syracuseStep 6568937 = 4926703) B4926703
theorem B1458175 : Blo 1295966 1458175 := bstep (se 1 (by rfl) ⟨1093631, by rfl⟩ : syracuseStep 1458175 = 2187263) B2187263
theorem B28057913 : Blo 1295966 28057913 := bstep (se 2 (by rfl) ⟨10521717, by rfl⟩ : syracuseStep 28057913 = 21043435) B21043435
theorem B9848303 : Blo 1295966 9848303 := bstep (se 1 (by rfl) ⟨7386227, by rfl⟩ : syracuseStep 9848303 = 14772455) B14772455
theorem B67389671 : Blo 1295966 67389671 := bstep (se 1 (by rfl) ⟨50542253, by rfl⟩ : syracuseStep 67389671 = 101084507) B101084507
theorem B1944233 : Blo 1295966 1944233 := bstep (se 2 (by rfl) ⟨729087, by rfl⟩ : syracuseStep 1944233 = 1458175) B1458175
theorem B2920283 : Blo 1295966 2920283 := bstep (se 1 (by rfl) ⟨2190212, by rfl⟩ : syracuseStep 2920283 = 4380425) B4380425
theorem B5918575 : Blo 1295966 5918575 := bstep (se 1 (by rfl) ⟨4438931, by rfl⟩ : syracuseStep 5918575 = 8877863) B8877863
theorem B4379291 : Blo 1295966 4379291 := bstep (se 1 (by rfl) ⟨3284468, by rfl⟩ : syracuseStep 4379291 = 6568937) B6568937
theorem B9844415 : Blo 1295966 9844415 := bstep (se 1 (by rfl) ⟨7383311, by rfl⟩ : syracuseStep 9844415 = 14766623) B14766623
theorem B6562943 : Blo 1295966 6562943 := bstep (se 1 (by rfl) ⟨4922207, by rfl⟩ : syracuseStep 6562943 = 9844415) B9844415
theorem B1296155 : Blo 1295966 1296155 := bstep (se 1 (by rfl) ⟨972116, by rfl⟩ : syracuseStep 1296155 = 1944233) B1944233
theorem B7891433 : Blo 1295966 7891433 := bstep (se 2 (by rfl) ⟨2959287, by rfl⟩ : syracuseStep 7891433 = 5918575) B5918575
theorem B18705275 : Blo 1295966 18705275 := bstep (se 1 (by rfl) ⟨14028956, by rfl⟩ : syracuseStep 18705275 = 28057913) B28057913
theorem B2919527 : Blo 1295966 2919527 := bstep (se 1 (by rfl) ⟨2189645, by rfl⟩ : syracuseStep 2919527 = 4379291) B4379291
theorem B6565535 : Blo 1295966 6565535 := bstep (se 1 (by rfl) ⟨4924151, by rfl⟩ : syracuseStep 6565535 = 9848303) B9848303
theorem B1946855 : Blo 1295966 1946855 := bstep (se 1 (by rfl) ⟨1460141, by rfl⟩ : syracuseStep 1946855 = 2920283) B2920283
theorem B179705789 : Blo 1295966 179705789 := bstep (se 3 (by rfl) ⟨33694835, by rfl⟩ : syracuseStep 179705789 = 67389671) B67389671
theorem B4375295 : Blo 1295966 4375295 := bstep (se 1 (by rfl) ⟨3281471, by rfl⟩ : syracuseStep 4375295 = 6562943) B6562943
theorem B5260955 : Blo 1295966 5260955 := bstep (se 1 (by rfl) ⟨3945716, by rfl⟩ : syracuseStep 5260955 = 7891433) B7891433
theorem B12470183 : Blo 1295966 12470183 := bstep (se 1 (by rfl) ⟨9352637, by rfl⟩ : syracuseStep 12470183 = 18705275) B18705275
theorem B4377023 : Blo 1295966 4377023 := bstep (se 1 (by rfl) ⟨3282767, by rfl⟩ : syracuseStep 4377023 = 6565535) B6565535
theorem B1297903 : Blo 1295966 1297903 := bstep (se 1 (by rfl) ⟨973427, by rfl⟩ : syracuseStep 1297903 = 1946855) B1946855
theorem B119803859 : Blo 1295966 119803859 := bstep (se 1 (by rfl) ⟨89852894, by rfl⟩ : syracuseStep 119803859 = 179705789) B179705789
theorem B1946351 : Blo 1295966 1946351 := bstep (se 1 (by rfl) ⟨1459763, by rfl⟩ : syracuseStep 1946351 = 2919527) B2919527
theorem B2916863 : Blo 1295966 2916863 := bstep (se 1 (by rfl) ⟨2187647, by rfl⟩ : syracuseStep 2916863 = 4375295) B4375295
theorem B2918015 : Blo 1295966 2918015 := bstep (se 1 (by rfl) ⟨2188511, by rfl⟩ : syracuseStep 2918015 = 4377023) B4377023
theorem B1297567 : Blo 1295966 1297567 := bstep (se 1 (by rfl) ⟨973175, by rfl⟩ : syracuseStep 1297567 = 1946351) B1946351
theorem B14029213 : Blo 1295966 14029213 := bstep (se 3 (by rfl) ⟨2630477, by rfl⟩ : syracuseStep 14029213 = 5260955) B5260955
theorem B79869239 : Blo 1295966 79869239 := bstep (se 1 (by rfl) ⟨59901929, by rfl⟩ : syracuseStep 79869239 = 119803859) B119803859
theorem B8313455 : Blo 1295966 8313455 := bstep (se 1 (by rfl) ⟨6235091, by rfl⟩ : syracuseStep 8313455 = 12470183) B12470183
theorem B1944575 : Blo 1295966 1944575 := bstep (se 1 (by rfl) ⟨1458431, by rfl⟩ : syracuseStep 1944575 = 2916863) B2916863
theorem B18705617 : Blo 1295966 18705617 := bstep (se 2 (by rfl) ⟨7014606, by rfl⟩ : syracuseStep 18705617 = 14029213) B14029213
theorem B1945343 : Blo 1295966 1945343 := bstep (se 1 (by rfl) ⟨1459007, by rfl⟩ : syracuseStep 1945343 = 2918015) B2918015
theorem B5542303 : Blo 1295966 5542303 := bstep (se 1 (by rfl) ⟨4156727, by rfl⟩ : syracuseStep 5542303 = 8313455) B8313455
theorem B53246159 : Blo 1295966 53246159 := bstep (se 1 (by rfl) ⟨39934619, by rfl⟩ : syracuseStep 53246159 = 79869239) B79869239
theorem B7389737 : Blo 1295966 7389737 := bstep (se 2 (by rfl) ⟨2771151, by rfl⟩ : syracuseStep 7389737 = 5542303) B5542303
theorem B35497439 : Blo 1295966 35497439 := bstep (se 1 (by rfl) ⟨26623079, by rfl⟩ : syracuseStep 35497439 = 53246159) B53246159
theorem B1296383 : Blo 1295966 1296383 := bstep (se 1 (by rfl) ⟨972287, by rfl⟩ : syracuseStep 1296383 = 1944575) B1944575
theorem B12470411 : Blo 1295966 12470411 := bstep (se 1 (by rfl) ⟨9352808, by rfl⟩ : syracuseStep 12470411 = 18705617) B18705617
theorem B1296895 : Blo 1295966 1296895 := bstep (se 1 (by rfl) ⟨972671, by rfl⟩ : syracuseStep 1296895 = 1945343) B1945343
theorem B4926491 : Blo 1295966 4926491 := bstep (se 1 (by rfl) ⟨3694868, by rfl⟩ : syracuseStep 4926491 = 7389737) B7389737
theorem B23664959 : Blo 1295966 23664959 := bstep (se 1 (by rfl) ⟨17748719, by rfl⟩ : syracuseStep 23664959 = 35497439) B35497439
theorem B8313607 : Blo 1295966 8313607 := bstep (se 1 (by rfl) ⟨6235205, by rfl⟩ : syracuseStep 8313607 = 12470411) B12470411
theorem B11084809 : Blo 1295966 11084809 := bstep (se 2 (by rfl) ⟨4156803, by rfl⟩ : syracuseStep 11084809 = 8313607) B8313607
theorem B15776639 : Blo 1295966 15776639 := bstep (se 1 (by rfl) ⟨11832479, by rfl⟩ : syracuseStep 15776639 = 23664959) B23664959
theorem B3284327 : Blo 1295966 3284327 := bstep (se 1 (by rfl) ⟨2463245, by rfl⟩ : syracuseStep 3284327 = 4926491) B4926491
theorem B14779745 : Blo 1295966 14779745 := bstep (se 2 (by rfl) ⟨5542404, by rfl⟩ : syracuseStep 14779745 = 11084809) B11084809
theorem B2189551 : Blo 1295966 2189551 := bstep (se 1 (by rfl) ⟨1642163, by rfl⟩ : syracuseStep 2189551 = 3284327) B3284327
theorem B10517759 : Blo 1295966 10517759 := bstep (se 1 (by rfl) ⟨7888319, by rfl⟩ : syracuseStep 10517759 = 15776639) B15776639
theorem B2919401 : Blo 1295966 2919401 := bstep (se 2 (by rfl) ⟨1094775, by rfl⟩ : syracuseStep 2919401 = 2189551) B2189551
theorem B9853163 : Blo 1295966 9853163 := bstep (se 1 (by rfl) ⟨7389872, by rfl⟩ : syracuseStep 9853163 = 14779745) B14779745
theorem B7011839 : Blo 1295966 7011839 := bstep (se 1 (by rfl) ⟨5258879, by rfl⟩ : syracuseStep 7011839 = 10517759) B10517759
theorem B1946267 : Blo 1295966 1946267 := bstep (se 1 (by rfl) ⟨1459700, by rfl⟩ : syracuseStep 1946267 = 2919401) B2919401
theorem B4674559 : Blo 1295966 4674559 := bstep (se 1 (by rfl) ⟨3505919, by rfl⟩ : syracuseStep 4674559 = 7011839) B7011839
theorem B6568775 : Blo 1295966 6568775 := bstep (se 1 (by rfl) ⟨4926581, by rfl⟩ : syracuseStep 6568775 = 9853163) B9853163
theorem B1297511 : Blo 1295966 1297511 := bstep (se 1 (by rfl) ⟨973133, by rfl⟩ : syracuseStep 1297511 = 1946267) B1946267
theorem B4379183 : Blo 1295966 4379183 := bstep (se 1 (by rfl) ⟨3284387, by rfl⟩ : syracuseStep 4379183 = 6568775) B6568775
theorem B6232745 : Blo 1295966 6232745 := bstep (se 2 (by rfl) ⟨2337279, by rfl⟩ : syracuseStep 6232745 = 4674559) B4674559
theorem B2919455 : Blo 1295966 2919455 := bstep (se 1 (by rfl) ⟨2189591, by rfl⟩ : syracuseStep 2919455 = 4379183) B4379183
theorem B16620653 : Blo 1295966 16620653 := bstep (se 3 (by rfl) ⟨3116372, by rfl⟩ : syracuseStep 16620653 = 6232745) B6232745
theorem B1946303 : Blo 1295966 1946303 := bstep (se 1 (by rfl) ⟨1459727, by rfl⟩ : syracuseStep 1946303 = 2919455) B2919455
theorem B11080435 : Blo 1295966 11080435 := bstep (se 1 (by rfl) ⟨8310326, by rfl⟩ : syracuseStep 11080435 = 16620653) B16620653
theorem B1297535 : Blo 1295966 1297535 := bstep (se 1 (by rfl) ⟨973151, by rfl⟩ : syracuseStep 1297535 = 1946303) B1946303
theorem B14773913 : Blo 1295966 14773913 := bstep (se 2 (by rfl) ⟨5540217, by rfl⟩ : syracuseStep 14773913 = 11080435) B11080435
theorem B9849275 : Blo 1295966 9849275 := bstep (se 1 (by rfl) ⟨7386956, by rfl⟩ : syracuseStep 9849275 = 14773913) B14773913
theorem B6566183 : Blo 1295966 6566183 := bstep (se 1 (by rfl) ⟨4924637, by rfl⟩ : syracuseStep 6566183 = 9849275) B9849275
theorem B4377455 : Blo 1295966 4377455 := bstep (se 1 (by rfl) ⟨3283091, by rfl⟩ : syracuseStep 4377455 = 6566183) B6566183
theorem B2918303 : Blo 1295966 2918303 := bstep (se 1 (by rfl) ⟨2188727, by rfl⟩ : syracuseStep 2918303 = 4377455) B4377455
theorem B1945535 : Blo 1295966 1945535 := bstep (se 1 (by rfl) ⟨1459151, by rfl⟩ : syracuseStep 1945535 = 2918303) B2918303
theorem B1297023 : Blo 1295966 1297023 := bstep (se 1 (by rfl) ⟨972767, by rfl⟩ : syracuseStep 1297023 = 1945535) B1945535

theorem C0 (j : ℕ) (h1 : 323991 ≤ j) (h2 : j ≤ 324490) : Blo 1295966 (4 * j + 3) := by
  interval_cases j
  · exact B1295967
  · exact B1295971
  · exact B1295975
  · exact B1295979
  · exact B1295983
  · exact B1295987
  · exact B1295991
  · exact B1295995
  · exact B1295999
  · exact B1296003
  · exact B1296007
  · exact B1296011
  · exact B1296015
  · exact B1296019
  · exact B1296023
  · exact B1296027
  · exact B1296031
  · exact B1296035
  · exact B1296039
  · exact B1296043
  · exact B1296047
  · exact B1296051
  · exact B1296055
  · exact B1296059
  · exact B1296063
  · exact B1296067
  · exact B1296071
  · exact B1296075
  · exact B1296079
  · exact B1296083
  · exact B1296087
  · exact B1296091
  · exact B1296095
  · exact B1296099
  · exact B1296103
  · exact B1296107
  · exact B1296111
  · exact B1296115
  · exact B1296119
  · exact B1296123
  · exact B1296127
  · exact B1296131
  · exact B1296135
  · exact B1296139
  · exact B1296143
  · exact B1296147
  · exact B1296151
  · exact B1296155
  · exact B1296159
  · exact B1296163
  · exact B1296167
  · exact B1296171
  · exact B1296175
  · exact B1296179
  · exact B1296183
  · exact B1296187
  · exact B1296191
  · exact B1296195
  · exact B1296199
  · exact B1296203
  · exact B1296207
  · exact B1296211
  · exact B1296215
  · exact B1296219
  · exact B1296223
  · exact B1296227
  · exact B1296231
  · exact B1296235
  · exact B1296239
  · exact B1296243
  · exact B1296247
  · exact B1296251
  · exact B1296255
  · exact B1296259
  · exact B1296263
  · exact B1296267
  · exact B1296271
  · exact B1296275
  · exact B1296279
  · exact B1296283
  · exact B1296287
  · exact B1296291
  · exact B1296295
  · exact B1296299
  · exact B1296303
  · exact B1296307
  · exact B1296311
  · exact B1296315
  · exact B1296319
  · exact B1296323
  · exact B1296327
  · exact B1296331
  · exact B1296335
  · exact B1296339
  · exact B1296343
  · exact B1296347
  · exact B1296351
  · exact B1296355
  · exact B1296359
  · exact B1296363
  · exact B1296367
  · exact B1296371
  · exact B1296375
  · exact B1296379
  · exact B1296383
  · exact B1296387
  · exact B1296391
  · exact B1296395
  · exact B1296399
  · exact B1296403
  · exact B1296407
  · exact B1296411
  · exact B1296415
  · exact B1296419
  · exact B1296423
  · exact B1296427
  · exact B1296431
  · exact B1296435
  · exact B1296439
  · exact B1296443
  · exact B1296447
  · exact B1296451
  · exact B1296455
  · exact B1296459
  · exact B1296463
  · exact B1296467
  · exact B1296471
  · exact B1296475
  · exact B1296479
  · exact B1296483
  · exact B1296487
  · exact B1296491
  · exact B1296495
  · exact B1296499
  · exact B1296503
  · exact B1296507
  · exact B1296511
  · exact B1296515
  · exact B1296519
  · exact B1296523
  · exact B1296527
  · exact B1296531
  · exact B1296535
  · exact B1296539
  · exact B1296543
  · exact B1296547
  · exact B1296551
  · exact B1296555
  · exact B1296559
  · exact B1296563
  · exact B1296567
  · exact B1296571
  · exact B1296575
  · exact B1296579
  · exact B1296583
  · exact B1296587
  · exact B1296591
  · exact B1296595
  · exact B1296599
  · exact B1296603
  · exact B1296607
  · exact B1296611
  · exact B1296615
  · exact B1296619
  · exact B1296623
  · exact B1296627
  · exact B1296631
  · exact B1296635
  · exact B1296639
  · exact B1296643
  · exact B1296647
  · exact B1296651
  · exact B1296655
  · exact B1296659
  · exact B1296663
  · exact B1296667
  · exact B1296671
  · exact B1296675
  · exact B1296679
  · exact B1296683
  · exact B1296687
  · exact B1296691
  · exact B1296695
  · exact B1296699
  · exact B1296703
  · exact B1296707
  · exact B1296711
  · exact B1296715
  · exact B1296719
  · exact B1296723
  · exact B1296727
  · exact B1296731
  · exact B1296735
  · exact B1296739
  · exact B1296743
  · exact B1296747
  · exact B1296751
  · exact B1296755
  · exact B1296759
  · exact B1296763
  · exact B1296767
  · exact B1296771
  · exact B1296775
  · exact B1296779
  · exact B1296783
  · exact B1296787
  · exact B1296791
  · exact B1296795
  · exact B1296799
  · exact B1296803
  · exact B1296807
  · exact B1296811
  · exact B1296815
  · exact B1296819
  · exact B1296823
  · exact B1296827
  · exact B1296831
  · exact B1296835
  · exact B1296839
  · exact B1296843
  · exact B1296847
  · exact B1296851
  · exact B1296855
  · exact B1296859
  · exact B1296863
  · exact B1296867
  · exact B1296871
  · exact B1296875
  · exact B1296879
  · exact B1296883
  · exact B1296887
  · exact B1296891
  · exact B1296895
  · exact B1296899
  · exact B1296903
  · exact B1296907
  · exact B1296911
  · exact B1296915
  · exact B1296919
  · exact B1296923
  · exact B1296927
  · exact B1296931
  · exact B1296935
  · exact B1296939
  · exact B1296943
  · exact B1296947
  · exact B1296951
  · exact B1296955
  · exact B1296959
  · exact B1296963
  · exact B1296967
  · exact B1296971
  · exact B1296975
  · exact B1296979
  · exact B1296983
  · exact B1296987
  · exact B1296991
  · exact B1296995
  · exact B1296999
  · exact B1297003
  · exact B1297007
  · exact B1297011
  · exact B1297015
  · exact B1297019
  · exact B1297023
  · exact B1297027
  · exact B1297031
  · exact B1297035
  · exact B1297039
  · exact B1297043
  · exact B1297047
  · exact B1297051
  · exact B1297055
  · exact B1297059
  · exact B1297063
  · exact B1297067
  · exact B1297071
  · exact B1297075
  · exact B1297079
  · exact B1297083
  · exact B1297087
  · exact B1297091
  · exact B1297095
  · exact B1297099
  · exact B1297103
  · exact B1297107
  · exact B1297111
  · exact B1297115
  · exact B1297119
  · exact B1297123
  · exact B1297127
  · exact B1297131
  · exact B1297135
  · exact B1297139
  · exact B1297143
  · exact B1297147
  · exact B1297151
  · exact B1297155
  · exact B1297159
  · exact B1297163
  · exact B1297167
  · exact B1297171
  · exact B1297175
  · exact B1297179
  · exact B1297183
  · exact B1297187
  · exact B1297191
  · exact B1297195
  · exact B1297199
  · exact B1297203
  · exact B1297207
  · exact B1297211
  · exact B1297215
  · exact B1297219
  · exact B1297223
  · exact B1297227
  · exact B1297231
  · exact B1297235
  · exact B1297239
  · exact B1297243
  · exact B1297247
  · exact B1297251
  · exact B1297255
  · exact B1297259
  · exact B1297263
  · exact B1297267
  · exact B1297271
  · exact B1297275
  · exact B1297279
  · exact B1297283
  · exact B1297287
  · exact B1297291
  · exact B1297295
  · exact B1297299
  · exact B1297303
  · exact B1297307
  · exact B1297311
  · exact B1297315
  · exact B1297319
  · exact B1297323
  · exact B1297327
  · exact B1297331
  · exact B1297335
  · exact B1297339
  · exact B1297343
  · exact B1297347
  · exact B1297351
  · exact B1297355
  · exact B1297359
  · exact B1297363
  · exact B1297367
  · exact B1297371
  · exact B1297375
  · exact B1297379
  · exact B1297383
  · exact B1297387
  · exact B1297391
  · exact B1297395
  · exact B1297399
  · exact B1297403
  · exact B1297407
  · exact B1297411
  · exact B1297415
  · exact B1297419
  · exact B1297423
  · exact B1297427
  · exact B1297431
  · exact B1297435
  · exact B1297439
  · exact B1297443
  · exact B1297447
  · exact B1297451
  · exact B1297455
  · exact B1297459
  · exact B1297463
  · exact B1297467
  · exact B1297471
  · exact B1297475
  · exact B1297479
  · exact B1297483
  · exact B1297487
  · exact B1297491
  · exact B1297495
  · exact B1297499
  · exact B1297503
  · exact B1297507
  · exact B1297511
  · exact B1297515
  · exact B1297519
  · exact B1297523
  · exact B1297527
  · exact B1297531
  · exact B1297535
  · exact B1297539
  · exact B1297543
  · exact B1297547
  · exact B1297551
  · exact B1297555
  · exact B1297559
  · exact B1297563
  · exact B1297567
  · exact B1297571
  · exact B1297575
  · exact B1297579
  · exact B1297583
  · exact B1297587
  · exact B1297591
  · exact B1297595
  · exact B1297599
  · exact B1297603
  · exact B1297607
  · exact B1297611
  · exact B1297615
  · exact B1297619
  · exact B1297623
  · exact B1297627
  · exact B1297631
  · exact B1297635
  · exact B1297639
  · exact B1297643
  · exact B1297647
  · exact B1297651
  · exact B1297655
  · exact B1297659
  · exact B1297663
  · exact B1297667
  · exact B1297671
  · exact B1297675
  · exact B1297679
  · exact B1297683
  · exact B1297687
  · exact B1297691
  · exact B1297695
  · exact B1297699
  · exact B1297703
  · exact B1297707
  · exact B1297711
  · exact B1297715
  · exact B1297719
  · exact B1297723
  · exact B1297727
  · exact B1297731
  · exact B1297735
  · exact B1297739
  · exact B1297743
  · exact B1297747
  · exact B1297751
  · exact B1297755
  · exact B1297759
  · exact B1297763
  · exact B1297767
  · exact B1297771
  · exact B1297775
  · exact B1297779
  · exact B1297783
  · exact B1297787
  · exact B1297791
  · exact B1297795
  · exact B1297799
  · exact B1297803
  · exact B1297807
  · exact B1297811
  · exact B1297815
  · exact B1297819
  · exact B1297823
  · exact B1297827
  · exact B1297831
  · exact B1297835
  · exact B1297839
  · exact B1297843
  · exact B1297847
  · exact B1297851
  · exact B1297855
  · exact B1297859
  · exact B1297863
  · exact B1297867
  · exact B1297871
  · exact B1297875
  · exact B1297879
  · exact B1297883
  · exact B1297887
  · exact B1297891
  · exact B1297895
  · exact B1297899
  · exact B1297903
  · exact B1297907
  · exact B1297911
  · exact B1297915
  · exact B1297919
  · exact B1297923
  · exact B1297927
  · exact B1297931
  · exact B1297935
  · exact B1297939
  · exact B1297943
  · exact B1297947
  · exact B1297951
  · exact B1297955
  · exact B1297959
  · exact B1297963

theorem solution (m : ℕ) (hlo : 1295966 ≤ m) (hhi : m ≤ 1297966) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 323991 ≤ j := by omega
    have hj2 : j ≤ 324490 := by omega
    have hb : Blo 1295966 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
