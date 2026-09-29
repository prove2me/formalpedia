-- Prove2me | solution 1 for syracuse_descends_range_323837_327837
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:25.469557+00:00
-- url     : https://prove2.me/submissions/74a4530f-aa69-4c31-8033-8ab5406ae032

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


theorem B491525 : Blo 323837 491525 := bbase (se 4 (by rfl) ⟨46080, by rfl⟩ : syracuseStep 491525 = 92161) (by norm_num)
theorem B393233 : Blo 323837 393233 := bbase (se 2 (by rfl) ⟨147462, by rfl⟩ : syracuseStep 393233 = 294925) (by norm_num)
theorem B491549 : Blo 323837 491549 := bbase (se 3 (by rfl) ⟨92165, by rfl⟩ : syracuseStep 491549 = 184331) (by norm_num)
theorem B491573 : Blo 323837 491573 := bbase (se 5 (by rfl) ⟨23042, by rfl⟩ : syracuseStep 491573 = 46085) (by norm_num)
theorem B491597 : Blo 323837 491597 := bbase (se 3 (by rfl) ⟨92174, by rfl⟩ : syracuseStep 491597 = 184349) (by norm_num)
theorem B1572949 : Blo 323837 1572949 := bbase (se 8 (by rfl) ⟨9216, by rfl⟩ : syracuseStep 1572949 = 18433) (by norm_num)
theorem B491621 : Blo 323837 491621 := bbase (se 4 (by rfl) ⟨46089, by rfl⟩ : syracuseStep 491621 = 92179) (by norm_num)
theorem B491645 : Blo 323837 491645 := bbase (se 3 (by rfl) ⟨92183, by rfl⟩ : syracuseStep 491645 = 184367) (by norm_num)
theorem B393349 : Blo 323837 393349 := bbase (se 4 (by rfl) ⟨36876, by rfl⟩ : syracuseStep 393349 = 73753) (by norm_num)
theorem B491669 : Blo 323837 491669 := bbase (se 6 (by rfl) ⟨11523, by rfl⟩ : syracuseStep 491669 = 23047) (by norm_num)
theorem B491693 : Blo 323837 491693 := bbase (se 3 (by rfl) ⟨92192, by rfl⟩ : syracuseStep 491693 = 184385) (by norm_num)
theorem B491717 : Blo 323837 491717 := bbase (se 4 (by rfl) ⟨46098, by rfl⟩ : syracuseStep 491717 = 92197) (by norm_num)
theorem B491741 : Blo 323837 491741 := bbase (se 3 (by rfl) ⟨92201, by rfl⟩ : syracuseStep 491741 = 184403) (by norm_num)
theorem B524573 : Blo 323837 524573 := bbase (se 3 (by rfl) ⟨98357, by rfl⟩ : syracuseStep 524573 = 196715) (by norm_num)
theorem B393545 : Blo 323837 393545 := bbase (se 2 (by rfl) ⟨147579, by rfl⟩ : syracuseStep 393545 = 295159) (by norm_num)
theorem B787013 : Blo 323837 787013 := bbase (se 4 (by rfl) ⟨73782, by rfl⟩ : syracuseStep 787013 = 147565) (by norm_num)
theorem B819821 : Blo 323837 819821 := bbase (se 3 (by rfl) ⟨153716, by rfl⟩ : syracuseStep 819821 = 307433) (by norm_num)
theorem B1049237 : Blo 323837 1049237 := bbase (se 6 (by rfl) ⟨24591, by rfl⟩ : syracuseStep 1049237 = 49183) (by norm_num)
theorem B590485 : Blo 323837 590485 := bbase (se 6 (by rfl) ⟨13839, by rfl⟩ : syracuseStep 590485 = 27679) (by norm_num)
theorem B3572437 : Blo 323837 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B328421 : Blo 323837 328421 := bbase (se 4 (by rfl) ⟨30789, by rfl⟩ : syracuseStep 328421 = 61579) (by norm_num)
theorem B525085 : Blo 323837 525085 := bbase (se 3 (by rfl) ⟨98453, by rfl⟩ : syracuseStep 525085 = 196907) (by norm_num)
theorem B492389 : Blo 323837 492389 := bbase (se 4 (by rfl) ⟨46161, by rfl⟩ : syracuseStep 492389 = 92323) (by norm_num)
theorem B590773 : Blo 323837 590773 := bbase (se 5 (by rfl) ⟨27692, by rfl⟩ : syracuseStep 590773 = 55385) (by norm_num)
theorem B820165 : Blo 323837 820165 := bbase (se 4 (by rfl) ⟨76890, by rfl⟩ : syracuseStep 820165 = 153781) (by norm_num)
theorem B820277 : Blo 323837 820277 := bbase (se 5 (by rfl) ⟨38450, by rfl⟩ : syracuseStep 820277 = 76901) (by norm_num)
theorem B394433 : Blo 323837 394433 := bbase (se 2 (by rfl) ⟨147912, by rfl⟩ : syracuseStep 394433 = 295825) (by norm_num)
theorem B820469 : Blo 323837 820469 := bbase (se 5 (by rfl) ⟨38459, by rfl⟩ : syracuseStep 820469 = 76919) (by norm_num)
theorem B918821 : Blo 323837 918821 := bbase (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) (by norm_num)
theorem B329005 : Blo 323837 329005 := bbase (se 3 (by rfl) ⟨61688, by rfl⟩ : syracuseStep 329005 = 123377) (by norm_num)
theorem B1639925 : Blo 323837 1639925 := bbase (se 5 (by rfl) ⟨76871, by rfl⟩ : syracuseStep 1639925 = 153743) (by norm_num)
theorem B820813 : Blo 323837 820813 := bbase (se 3 (by rfl) ⟨153902, by rfl⟩ : syracuseStep 820813 = 307805) (by norm_num)
theorem B820925 : Blo 323837 820925 := bbase (se 3 (by rfl) ⟨153923, by rfl⟩ : syracuseStep 820925 = 307847) (by norm_num)
theorem B493325 : Blo 323837 493325 := bbase (se 3 (by rfl) ⟨92498, by rfl⟩ : syracuseStep 493325 = 184997) (by norm_num)
theorem B5965589 : Blo 323837 5965589 := bbase (se 6 (by rfl) ⟨139818, by rfl⟩ : syracuseStep 5965589 = 279637) (by norm_num)
theorem B821117 : Blo 323837 821117 := bbase (se 3 (by rfl) ⟨153959, by rfl⟩ : syracuseStep 821117 = 307919) (by norm_num)
theorem B821461 : Blo 323837 821461 := bbase (se 7 (by rfl) ⟨9626, by rfl⟩ : syracuseStep 821461 = 19253) (by norm_num)
theorem B1771733 : Blo 323837 1771733 := bbase (se 7 (by rfl) ⟨20762, by rfl⟩ : syracuseStep 1771733 = 41525) (by norm_num)
theorem B2787605 : Blo 323837 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B821573 : Blo 323837 821573 := bbase (se 4 (by rfl) ⟨77022, by rfl⟩ : syracuseStep 821573 = 154045) (by norm_num)
theorem B330205 : Blo 323837 330205 := bbase (se 3 (by rfl) ⟨61913, by rfl⟩ : syracuseStep 330205 = 123827) (by norm_num)
theorem B821765 : Blo 323837 821765 := bbase (se 4 (by rfl) ⟨77040, by rfl⟩ : syracuseStep 821765 = 154081) (by norm_num)
theorem B461389 : Blo 323837 461389 := bbase (se 3 (by rfl) ⟨86510, by rfl⟩ : syracuseStep 461389 = 173021) (by norm_num)
theorem B1641221 : Blo 323837 1641221 := bbase (se 4 (by rfl) ⟨153864, by rfl⟩ : syracuseStep 1641221 = 307729) (by norm_num)
theorem B822109 : Blo 323837 822109 := bbase (se 3 (by rfl) ⟨154145, by rfl⟩ : syracuseStep 822109 = 308291) (by norm_num)
theorem B822221 : Blo 323837 822221 := bbase (se 3 (by rfl) ⟨154166, by rfl⟩ : syracuseStep 822221 = 308333) (by norm_num)
theorem B1313813 : Blo 323837 1313813 := bbase (se 6 (by rfl) ⟨30792, by rfl⟩ : syracuseStep 1313813 = 61585) (by norm_num)
theorem B756797 : Blo 323837 756797 := bbase (se 3 (by rfl) ⟨141899, by rfl⟩ : syracuseStep 756797 = 283799) (by norm_num)
theorem B822413 : Blo 323837 822413 := bbase (se 3 (by rfl) ⟨154202, by rfl⟩ : syracuseStep 822413 = 308405) (by norm_num)
theorem B461981 : Blo 323837 461981 := bbase (se 3 (by rfl) ⟨86621, by rfl⟩ : syracuseStep 461981 = 173243) (by norm_num)
theorem B462061 : Blo 323837 462061 := bbase (se 3 (by rfl) ⟨86636, by rfl⟩ : syracuseStep 462061 = 173273) (by norm_num)
theorem B593173 : Blo 323837 593173 := bbase (se 6 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 593173 = 27805) (by norm_num)
theorem B462181 : Blo 323837 462181 := bbase (se 4 (by rfl) ⟨43329, by rfl⟩ : syracuseStep 462181 = 86659) (by norm_num)
theorem B462277 : Blo 323837 462277 := bbase (se 4 (by rfl) ⟨43338, by rfl⟩ : syracuseStep 462277 = 86677) (by norm_num)
theorem B822757 : Blo 323837 822757 := bbase (se 4 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 822757 = 154267) (by norm_num)
theorem B1248821 : Blo 323837 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B822869 : Blo 323837 822869 := bbase (se 8 (by rfl) ⟨4821, by rfl⟩ : syracuseStep 822869 = 9643) (by norm_num)
theorem B495253 : Blo 323837 495253 := bbase (se 6 (by rfl) ⟨11607, by rfl⟩ : syracuseStep 495253 = 23215) (by norm_num)
theorem B691973 : Blo 323837 691973 := bbase (se 4 (by rfl) ⟨64872, by rfl⟩ : syracuseStep 691973 = 129745) (by norm_num)
theorem B823061 : Blo 323837 823061 := bbase (se 6 (by rfl) ⟨19290, by rfl⟩ : syracuseStep 823061 = 38581) (by norm_num)
theorem B986917 : Blo 323837 986917 := bbase (se 4 (by rfl) ⟨92523, by rfl⟩ : syracuseStep 986917 = 185047) (by norm_num)
theorem B364333 : Blo 323837 364333 := bbase (se 3 (by rfl) ⟨68312, by rfl⟩ : syracuseStep 364333 = 136625) (by norm_num)
theorem B364369 : Blo 323837 364369 := bbase (se 2 (by rfl) ⟨136638, by rfl⟩ : syracuseStep 364369 = 273277) (by norm_num)
theorem B15109973 : Blo 323837 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B364405 : Blo 323837 364405 := bbase (se 5 (by rfl) ⟨17081, by rfl⟩ : syracuseStep 364405 = 34163) (by norm_num)
theorem B331661 : Blo 323837 331661 := bbase (se 3 (by rfl) ⟨62186, by rfl⟩ : syracuseStep 331661 = 124373) (by norm_num)
theorem B2461589 : Blo 323837 2461589 := bbase (se 6 (by rfl) ⟨57693, by rfl⟩ : syracuseStep 2461589 = 115387) (by norm_num)
theorem B364441 : Blo 323837 364441 := bbase (se 2 (by rfl) ⟨136665, by rfl⟩ : syracuseStep 364441 = 273331) (by norm_num)
theorem B462773 : Blo 323837 462773 := bbase (se 5 (by rfl) ⟨21692, by rfl⟩ : syracuseStep 462773 = 43385) (by norm_num)
theorem B364477 : Blo 323837 364477 := bbase (se 3 (by rfl) ⟨68339, by rfl⟩ : syracuseStep 364477 = 136679) (by norm_num)
theorem B364513 : Blo 323837 364513 := bbase (se 2 (by rfl) ⟨136692, by rfl⟩ : syracuseStep 364513 = 273385) (by norm_num)
theorem B364549 : Blo 323837 364549 := bbase (se 4 (by rfl) ⟨34176, by rfl⟩ : syracuseStep 364549 = 68353) (by norm_num)
theorem B1642517 : Blo 323837 1642517 := bbase (se 6 (by rfl) ⟨38496, by rfl⟩ : syracuseStep 1642517 = 76993) (by norm_num)
theorem B364585 : Blo 323837 364585 := bbase (se 2 (by rfl) ⟨136719, by rfl⟩ : syracuseStep 364585 = 273439) (by norm_num)
theorem B495661 : Blo 323837 495661 := bbase (se 3 (by rfl) ⟨92936, by rfl⟩ : syracuseStep 495661 = 185873) (by norm_num)
theorem B364621 : Blo 323837 364621 := bbase (se 3 (by rfl) ⟨68366, by rfl⟩ : syracuseStep 364621 = 136733) (by norm_num)
theorem B823405 : Blo 323837 823405 := bbase (se 3 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 823405 = 308777) (by norm_num)
theorem B364657 : Blo 323837 364657 := bbase (se 2 (by rfl) ⟨136746, by rfl⟩ : syracuseStep 364657 = 273493) (by norm_num)
theorem B790661 : Blo 323837 790661 := bbase (se 4 (by rfl) ⟨74124, by rfl⟩ : syracuseStep 790661 = 148249) (by norm_num)
theorem B364693 : Blo 323837 364693 := bbase (se 6 (by rfl) ⟨8547, by rfl⟩ : syracuseStep 364693 = 17095) (by norm_num)
theorem B364729 : Blo 323837 364729 := bbase (se 2 (by rfl) ⟨136773, by rfl⟩ : syracuseStep 364729 = 273547) (by norm_num)
theorem B364765 : Blo 323837 364765 := bbase (se 3 (by rfl) ⟨68393, by rfl⟩ : syracuseStep 364765 = 136787) (by norm_num)
theorem B823517 : Blo 323837 823517 := bbase (se 3 (by rfl) ⟨154409, by rfl⟩ : syracuseStep 823517 = 308819) (by norm_num)
theorem B1315045 : Blo 323837 1315045 := bbase (se 4 (by rfl) ⟨123285, by rfl⟩ : syracuseStep 1315045 = 246571) (by norm_num)
theorem B364801 : Blo 323837 364801 := bbase (se 2 (by rfl) ⟨136800, by rfl⟩ : syracuseStep 364801 = 273601) (by norm_num)
theorem B364837 : Blo 323837 364837 := bbase (se 4 (by rfl) ⟨34203, by rfl⟩ : syracuseStep 364837 = 68407) (by norm_num)
theorem B364873 : Blo 323837 364873 := bbase (se 2 (by rfl) ⟨136827, by rfl⟩ : syracuseStep 364873 = 273655) (by norm_num)
theorem B627029 : Blo 323837 627029 := bbase (se 10 (by rfl) ⟨918, by rfl⟩ : syracuseStep 627029 = 1837) (by norm_num)
theorem B364909 : Blo 323837 364909 := bbase (se 3 (by rfl) ⟨68420, by rfl⟩ : syracuseStep 364909 = 136841) (by norm_num)
theorem B364945 : Blo 323837 364945 := bbase (se 2 (by rfl) ⟨136854, by rfl⟩ : syracuseStep 364945 = 273709) (by norm_num)
theorem B823709 : Blo 323837 823709 := bbase (se 3 (by rfl) ⟨154445, by rfl⟩ : syracuseStep 823709 = 308891) (by norm_num)
theorem B364981 : Blo 323837 364981 := bbase (se 5 (by rfl) ⟨17108, by rfl⟩ : syracuseStep 364981 = 34217) (by norm_num)
theorem B332245 : Blo 323837 332245 := bbase (se 7 (by rfl) ⟨3893, by rfl⟩ : syracuseStep 332245 = 7787) (by norm_num)
theorem B365017 : Blo 323837 365017 := bbase (se 2 (by rfl) ⟨136881, by rfl⟩ : syracuseStep 365017 = 273763) (by norm_num)
theorem B463325 : Blo 323837 463325 := bbase (se 3 (by rfl) ⟨86873, by rfl⟩ : syracuseStep 463325 = 173747) (by norm_num)
theorem B332257 : Blo 323837 332257 := bbase (se 2 (by rfl) ⟨124596, by rfl⟩ : syracuseStep 332257 = 249193) (by norm_num)
theorem B692725 : Blo 323837 692725 := bbase (se 5 (by rfl) ⟨32471, by rfl⟩ : syracuseStep 692725 = 64943) (by norm_num)
theorem B365053 : Blo 323837 365053 := bbase (se 3 (by rfl) ⟨68447, by rfl⟩ : syracuseStep 365053 = 136895) (by norm_num)
theorem B365089 : Blo 323837 365089 := bbase (se 2 (by rfl) ⟨136908, by rfl⟩ : syracuseStep 365089 = 273817) (by norm_num)
theorem B365125 : Blo 323837 365125 := bbase (se 4 (by rfl) ⟨34230, by rfl⟩ : syracuseStep 365125 = 68461) (by norm_num)
theorem B1184341 : Blo 323837 1184341 := bbase (se 8 (by rfl) ⟨6939, by rfl⟩ : syracuseStep 1184341 = 13879) (by norm_num)
theorem B365161 : Blo 323837 365161 := bbase (se 2 (by rfl) ⟨136935, by rfl⟩ : syracuseStep 365161 = 273871) (by norm_num)
theorem B692869 : Blo 323837 692869 := bbase (se 4 (by rfl) ⟨64956, by rfl⟩ : syracuseStep 692869 = 129913) (by norm_num)
theorem B365197 : Blo 323837 365197 := bbase (se 3 (by rfl) ⟨68474, by rfl⟩ : syracuseStep 365197 = 136949) (by norm_num)
theorem B365233 : Blo 323837 365233 := bbase (se 2 (by rfl) ⟨136962, by rfl⟩ : syracuseStep 365233 = 273925) (by norm_num)
theorem B365269 : Blo 323837 365269 := bbase (se 7 (by rfl) ⟨4280, by rfl⟩ : syracuseStep 365269 = 8561) (by norm_num)
theorem B824053 : Blo 323837 824053 := bbase (se 5 (by rfl) ⟨38627, by rfl⟩ : syracuseStep 824053 = 77255) (by norm_num)
theorem B365305 : Blo 323837 365305 := bbase (se 2 (by rfl) ⟨136989, by rfl⟩ : syracuseStep 365305 = 273979) (by norm_num)
theorem B365341 : Blo 323837 365341 := bbase (se 3 (by rfl) ⟨68501, by rfl⟩ : syracuseStep 365341 = 137003) (by norm_num)
theorem B365377 : Blo 323837 365377 := bbase (se 2 (by rfl) ⟨137016, by rfl⟩ : syracuseStep 365377 = 274033) (by norm_num)
theorem B529237 : Blo 323837 529237 := bbase (se 9 (by rfl) ⟨1550, by rfl⟩ : syracuseStep 529237 = 3101) (by norm_num)
theorem B365413 : Blo 323837 365413 := bbase (se 4 (by rfl) ⟨34257, by rfl⟩ : syracuseStep 365413 = 68515) (by norm_num)
theorem B824165 : Blo 323837 824165 := bbase (se 4 (by rfl) ⟨77265, by rfl⟩ : syracuseStep 824165 = 154531) (by norm_num)
theorem B365449 : Blo 323837 365449 := bbase (se 2 (by rfl) ⟨137043, by rfl⟩ : syracuseStep 365449 = 274087) (by norm_num)
theorem B365485 : Blo 323837 365485 := bbase (se 3 (by rfl) ⟨68528, by rfl⟩ : syracuseStep 365485 = 137057) (by norm_num)
theorem B365521 : Blo 323837 365521 := bbase (se 2 (by rfl) ⟨137070, by rfl⟩ : syracuseStep 365521 = 274141) (by norm_num)
theorem B365557 : Blo 323837 365557 := bbase (se 5 (by rfl) ⟨17135, by rfl⟩ : syracuseStep 365557 = 34271) (by norm_num)
theorem B693245 : Blo 323837 693245 := bbase (se 3 (by rfl) ⟨129983, by rfl⟩ : syracuseStep 693245 = 259967) (by norm_num)
theorem B365593 : Blo 323837 365593 := bbase (se 2 (by rfl) ⟨137097, by rfl⟩ : syracuseStep 365593 = 274195) (by norm_num)
theorem B496669 : Blo 323837 496669 := bbase (se 3 (by rfl) ⟨93125, by rfl⟩ : syracuseStep 496669 = 186251) (by norm_num)
theorem B824357 : Blo 323837 824357 := bbase (se 4 (by rfl) ⟨77283, by rfl⟩ : syracuseStep 824357 = 154567) (by norm_num)
theorem B365629 : Blo 323837 365629 := bbase (se 3 (by rfl) ⟨68555, by rfl⟩ : syracuseStep 365629 = 137111) (by norm_num)
theorem B365665 : Blo 323837 365665 := bbase (se 2 (by rfl) ⟨137124, by rfl⟩ : syracuseStep 365665 = 274249) (by norm_num)
theorem B365701 : Blo 323837 365701 := bbase (se 4 (by rfl) ⟨34284, by rfl⟩ : syracuseStep 365701 = 68569) (by norm_num)
theorem B365737 : Blo 323837 365737 := bbase (se 2 (by rfl) ⟨137151, by rfl⟩ : syracuseStep 365737 = 274303) (by norm_num)
theorem B365773 : Blo 323837 365773 := bbase (se 3 (by rfl) ⟨68582, by rfl⟩ : syracuseStep 365773 = 137165) (by norm_num)
theorem B464077 : Blo 323837 464077 := bbase (se 3 (by rfl) ⟨87014, by rfl⟩ : syracuseStep 464077 = 174029) (by norm_num)
theorem B365809 : Blo 323837 365809 := bbase (se 2 (by rfl) ⟨137178, by rfl⟩ : syracuseStep 365809 = 274357) (by norm_num)
theorem B365845 : Blo 323837 365845 := bbase (se 6 (by rfl) ⟨8574, by rfl⟩ : syracuseStep 365845 = 17149) (by norm_num)
theorem B1643813 : Blo 323837 1643813 := bbase (se 4 (by rfl) ⟨154107, by rfl⟩ : syracuseStep 1643813 = 308215) (by norm_num)
theorem B365881 : Blo 323837 365881 := bbase (se 2 (by rfl) ⟨137205, by rfl⟩ : syracuseStep 365881 = 274411) (by norm_num)
theorem B365917 : Blo 323837 365917 := bbase (se 3 (by rfl) ⟨68609, by rfl⟩ : syracuseStep 365917 = 137219) (by norm_num)
theorem B693613 : Blo 323837 693613 := bbase (se 3 (by rfl) ⟨130052, by rfl⟩ : syracuseStep 693613 = 260105) (by norm_num)
theorem B824701 : Blo 323837 824701 := bbase (se 3 (by rfl) ⟨154631, by rfl⟩ : syracuseStep 824701 = 309263) (by norm_num)
theorem B365953 : Blo 323837 365953 := bbase (se 2 (by rfl) ⟨137232, by rfl⟩ : syracuseStep 365953 = 274465) (by norm_num)
theorem B365989 : Blo 323837 365989 := bbase (se 4 (by rfl) ⟨34311, by rfl⟩ : syracuseStep 365989 = 68623) (by norm_num)
theorem B366025 : Blo 323837 366025 := bbase (se 2 (by rfl) ⟨137259, by rfl⟩ : syracuseStep 366025 = 274519) (by norm_num)
theorem B366061 : Blo 323837 366061 := bbase (se 3 (by rfl) ⟨68636, by rfl⟩ : syracuseStep 366061 = 137273) (by norm_num)
theorem B824813 : Blo 323837 824813 := bbase (se 3 (by rfl) ⟨154652, by rfl⟩ : syracuseStep 824813 = 309305) (by norm_num)
theorem B366097 : Blo 323837 366097 := bbase (se 2 (by rfl) ⟨137286, by rfl⟩ : syracuseStep 366097 = 274573) (by norm_num)
theorem B1676837 : Blo 323837 1676837 := bbase (se 4 (by rfl) ⟨157203, by rfl⟩ : syracuseStep 1676837 = 314407) (by norm_num)
theorem B366133 : Blo 323837 366133 := bbase (se 5 (by rfl) ⟨17162, by rfl⟩ : syracuseStep 366133 = 34325) (by norm_num)
theorem B988757 : Blo 323837 988757 := bbase (se 8 (by rfl) ⟨5793, by rfl⟩ : syracuseStep 988757 = 11587) (by norm_num)
theorem B366169 : Blo 323837 366169 := bbase (se 2 (by rfl) ⟨137313, by rfl⟩ : syracuseStep 366169 = 274627) (by norm_num)
theorem B366205 : Blo 323837 366205 := bbase (se 3 (by rfl) ⟨68663, by rfl⟩ : syracuseStep 366205 = 137327) (by norm_num)
theorem B366241 : Blo 323837 366241 := bbase (se 2 (by rfl) ⟨137340, by rfl⟩ : syracuseStep 366241 = 274681) (by norm_num)
theorem B825005 : Blo 323837 825005 := bbase (se 3 (by rfl) ⟨154688, by rfl⟩ : syracuseStep 825005 = 309377) (by norm_num)
theorem B562877 : Blo 323837 562877 := bbase (se 3 (by rfl) ⟨105539, by rfl⟩ : syracuseStep 562877 = 211079) (by norm_num)
theorem B366277 : Blo 323837 366277 := bbase (se 4 (by rfl) ⟨34338, by rfl⟩ : syracuseStep 366277 = 68677) (by norm_num)
theorem B366313 : Blo 323837 366313 := bbase (se 2 (by rfl) ⟨137367, by rfl⟩ : syracuseStep 366313 = 274735) (by norm_num)
theorem B366349 : Blo 323837 366349 := bbase (se 3 (by rfl) ⟨68690, by rfl⟩ : syracuseStep 366349 = 137381) (by norm_num)
theorem B595741 : Blo 323837 595741 := bbase (se 3 (by rfl) ⟨111701, by rfl⟩ : syracuseStep 595741 = 223403) (by norm_num)
theorem B366385 : Blo 323837 366385 := bbase (se 2 (by rfl) ⟨137394, by rfl⟩ : syracuseStep 366385 = 274789) (by norm_num)
theorem B890677 : Blo 323837 890677 := bbase (se 5 (by rfl) ⟨41750, by rfl⟩ : syracuseStep 890677 = 83501) (by norm_num)
theorem B1677125 : Blo 323837 1677125 := bbase (se 4 (by rfl) ⟨157230, by rfl⟩ : syracuseStep 1677125 = 314461) (by norm_num)
theorem B366421 : Blo 323837 366421 := bbase (se 9 (by rfl) ⟨1073, by rfl⟩ : syracuseStep 366421 = 2147) (by norm_num)
theorem B366457 : Blo 323837 366457 := bbase (se 2 (by rfl) ⟨137421, by rfl⟩ : syracuseStep 366457 = 274843) (by norm_num)
theorem B1120133 : Blo 323837 1120133 := bbase (se 4 (by rfl) ⟨105012, by rfl⟩ : syracuseStep 1120133 = 210025) (by norm_num)
theorem B366493 : Blo 323837 366493 := bbase (se 3 (by rfl) ⟨68717, by rfl⟩ : syracuseStep 366493 = 137435) (by norm_num)
theorem B366529 : Blo 323837 366529 := bbase (se 2 (by rfl) ⟨137448, by rfl⟩ : syracuseStep 366529 = 274897) (by norm_num)
theorem B366565 : Blo 323837 366565 := bbase (se 4 (by rfl) ⟨34365, by rfl⟩ : syracuseStep 366565 = 68731) (by norm_num)
theorem B464869 : Blo 323837 464869 := bbase (se 4 (by rfl) ⟨43581, by rfl⟩ : syracuseStep 464869 = 87163) (by norm_num)
theorem B825349 : Blo 323837 825349 := bbase (se 4 (by rfl) ⟨77376, by rfl⟩ : syracuseStep 825349 = 154753) (by norm_num)
theorem B366601 : Blo 323837 366601 := bbase (se 2 (by rfl) ⟨137475, by rfl⟩ : syracuseStep 366601 = 274951) (by norm_num)
theorem B366637 : Blo 323837 366637 := bbase (se 3 (by rfl) ⟨68744, by rfl⟩ : syracuseStep 366637 = 137489) (by norm_num)
theorem B366673 : Blo 323837 366673 := bbase (se 2 (by rfl) ⟨137502, by rfl⟩ : syracuseStep 366673 = 275005) (by norm_num)
theorem B366709 : Blo 323837 366709 := bbase (se 5 (by rfl) ⟨17189, by rfl⟩ : syracuseStep 366709 = 34379) (by norm_num)
theorem B825461 : Blo 323837 825461 := bbase (se 5 (by rfl) ⟨38693, by rfl⟩ : syracuseStep 825461 = 77387) (by norm_num)
theorem B366745 : Blo 323837 366745 := bbase (se 2 (by rfl) ⟨137529, by rfl⟩ : syracuseStep 366745 = 275059) (by norm_num)
theorem B366781 : Blo 323837 366781 := bbase (se 3 (by rfl) ⟨68771, by rfl⟩ : syracuseStep 366781 = 137543) (by norm_num)
theorem B366817 : Blo 323837 366817 := bbase (se 2 (by rfl) ⟨137556, by rfl⟩ : syracuseStep 366817 = 275113) (by norm_num)
theorem B366853 : Blo 323837 366853 := bbase (se 4 (by rfl) ⟨34392, by rfl⟩ : syracuseStep 366853 = 68785) (by norm_num)
theorem B366889 : Blo 323837 366889 := bbase (se 2 (by rfl) ⟨137583, by rfl⟩ : syracuseStep 366889 = 275167) (by norm_num)
theorem B2005301 : Blo 323837 2005301 := bbase (se 5 (by rfl) ⟨93998, by rfl⟩ : syracuseStep 2005301 = 187997) (by norm_num)
theorem B825653 : Blo 323837 825653 := bbase (se 5 (by rfl) ⟨38702, by rfl⟩ : syracuseStep 825653 = 77405) (by norm_num)
theorem B465205 : Blo 323837 465205 := bbase (se 5 (by rfl) ⟨21806, by rfl⟩ : syracuseStep 465205 = 43613) (by norm_num)
theorem B366925 : Blo 323837 366925 := bbase (se 3 (by rfl) ⟨68798, by rfl⟩ : syracuseStep 366925 = 137597) (by norm_num)
theorem B366961 : Blo 323837 366961 := bbase (se 2 (by rfl) ⟨137610, by rfl⟩ : syracuseStep 366961 = 275221) (by norm_num)
theorem B366997 : Blo 323837 366997 := bbase (se 6 (by rfl) ⟨8601, by rfl⟩ : syracuseStep 366997 = 17203) (by norm_num)
theorem B367033 : Blo 323837 367033 := bbase (se 2 (by rfl) ⟨137637, by rfl⟩ : syracuseStep 367033 = 275275) (by norm_num)
theorem B367069 : Blo 323837 367069 := bbase (se 3 (by rfl) ⟨68825, by rfl⟩ : syracuseStep 367069 = 137651) (by norm_num)
theorem B367105 : Blo 323837 367105 := bbase (se 2 (by rfl) ⟨137664, by rfl⟩ : syracuseStep 367105 = 275329) (by norm_num)
theorem B465421 : Blo 323837 465421 := bbase (se 3 (by rfl) ⟨87266, by rfl⟩ : syracuseStep 465421 = 174533) (by norm_num)
theorem B367141 : Blo 323837 367141 := bbase (se 4 (by rfl) ⟨34419, by rfl⟩ : syracuseStep 367141 = 68839) (by norm_num)
theorem B1645109 : Blo 323837 1645109 := bbase (se 5 (by rfl) ⟨77114, by rfl⟩ : syracuseStep 1645109 = 154229) (by norm_num)
theorem B891445 : Blo 323837 891445 := bbase (se 5 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 891445 = 83573) (by norm_num)
theorem B367177 : Blo 323837 367177 := bbase (se 2 (by rfl) ⟨137691, by rfl⟩ : syracuseStep 367177 = 275383) (by norm_num)
theorem B367213 : Blo 323837 367213 := bbase (se 3 (by rfl) ⟨68852, by rfl⟩ : syracuseStep 367213 = 137705) (by norm_num)
theorem B825997 : Blo 323837 825997 := bbase (se 3 (by rfl) ⟨154874, by rfl⟩ : syracuseStep 825997 = 309749) (by norm_num)
theorem B367249 : Blo 323837 367249 := bbase (se 2 (by rfl) ⟨137718, by rfl⟩ : syracuseStep 367249 = 275437) (by norm_num)
theorem B498325 : Blo 323837 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B367285 : Blo 323837 367285 := bbase (se 5 (by rfl) ⟨17216, by rfl⟩ : syracuseStep 367285 = 34433) (by norm_num)
theorem B367321 : Blo 323837 367321 := bbase (se 2 (by rfl) ⟨137745, by rfl⟩ : syracuseStep 367321 = 275491) (by norm_num)
theorem B498397 : Blo 323837 498397 := bbase (se 3 (by rfl) ⟨93449, by rfl⟩ : syracuseStep 498397 = 186899) (by norm_num)
theorem B826109 : Blo 323837 826109 := bbase (se 3 (by rfl) ⟨154895, by rfl⟩ : syracuseStep 826109 = 309791) (by norm_num)
theorem B367357 : Blo 323837 367357 := bbase (se 3 (by rfl) ⟨68879, by rfl⟩ : syracuseStep 367357 = 137759) (by norm_num)
theorem B367393 : Blo 323837 367393 := bbase (se 2 (by rfl) ⟨137772, by rfl⟩ : syracuseStep 367393 = 275545) (by norm_num)
theorem B367429 : Blo 323837 367429 := bbase (se 4 (by rfl) ⟨34446, by rfl⟩ : syracuseStep 367429 = 68893) (by norm_num)
theorem B695117 : Blo 323837 695117 := bbase (se 3 (by rfl) ⟨130334, by rfl⟩ : syracuseStep 695117 = 260669) (by norm_num)
theorem B662357 : Blo 323837 662357 := bbase (se 9 (by rfl) ⟨1940, by rfl⟩ : syracuseStep 662357 = 3881) (by norm_num)
theorem B367465 : Blo 323837 367465 := bbase (se 2 (by rfl) ⟨137799, by rfl⟩ : syracuseStep 367465 = 275599) (by norm_num)
theorem B465797 : Blo 323837 465797 := bbase (se 4 (by rfl) ⟨43668, by rfl⟩ : syracuseStep 465797 = 87337) (by norm_num)
theorem B367501 : Blo 323837 367501 := bbase (se 3 (by rfl) ⟨68906, by rfl⟩ : syracuseStep 367501 = 137813) (by norm_num)
theorem B662437 : Blo 323837 662437 := bbase (se 4 (by rfl) ⟨62103, by rfl⟩ : syracuseStep 662437 = 124207) (by norm_num)
theorem B367537 : Blo 323837 367537 := bbase (se 2 (by rfl) ⟨137826, by rfl⟩ : syracuseStep 367537 = 275653) (by norm_num)
theorem B826301 : Blo 323837 826301 := bbase (se 3 (by rfl) ⟨154931, by rfl⟩ : syracuseStep 826301 = 309863) (by norm_num)
theorem B367573 : Blo 323837 367573 := bbase (se 7 (by rfl) ⟨4307, by rfl⟩ : syracuseStep 367573 = 8615) (by norm_num)
theorem B695261 : Blo 323837 695261 := bbase (se 3 (by rfl) ⟨130361, by rfl⟩ : syracuseStep 695261 = 260723) (by norm_num)
theorem B367609 : Blo 323837 367609 := bbase (se 2 (by rfl) ⟨137853, by rfl⟩ : syracuseStep 367609 = 275707) (by norm_num)
theorem B367645 : Blo 323837 367645 := bbase (se 3 (by rfl) ⟨68933, by rfl⟩ : syracuseStep 367645 = 137867) (by norm_num)
theorem B367681 : Blo 323837 367681 := bbase (se 2 (by rfl) ⟨137880, by rfl⟩ : syracuseStep 367681 = 275761) (by norm_num)
theorem B367717 : Blo 323837 367717 := bbase (se 4 (by rfl) ⟨34473, by rfl⟩ : syracuseStep 367717 = 68947) (by norm_num)
theorem B367753 : Blo 323837 367753 := bbase (se 2 (by rfl) ⟨137907, by rfl⟩ : syracuseStep 367753 = 275815) (by norm_num)
theorem B367789 : Blo 323837 367789 := bbase (se 3 (by rfl) ⟨68960, by rfl⟩ : syracuseStep 367789 = 137921) (by norm_num)
theorem B367825 : Blo 323837 367825 := bbase (se 2 (by rfl) ⟨137934, by rfl⟩ : syracuseStep 367825 = 275869) (by norm_num)
theorem B367861 : Blo 323837 367861 := bbase (se 5 (by rfl) ⟨17243, by rfl⟩ : syracuseStep 367861 = 34487) (by norm_num)
theorem B826645 : Blo 323837 826645 := bbase (se 6 (by rfl) ⟨19374, by rfl⟩ : syracuseStep 826645 = 38749) (by norm_num)
theorem B367897 : Blo 323837 367897 := bbase (se 2 (by rfl) ⟨137961, by rfl⟩ : syracuseStep 367897 = 275923) (by norm_num)
theorem B924965 : Blo 323837 924965 := bbase (se 4 (by rfl) ⟨86715, by rfl⟩ : syracuseStep 924965 = 173431) (by norm_num)
theorem B367933 : Blo 323837 367933 := bbase (se 3 (by rfl) ⟨68987, by rfl⟩ : syracuseStep 367933 = 137975) (by norm_num)
theorem B695621 : Blo 323837 695621 := bbase (se 4 (by rfl) ⟨65214, by rfl⟩ : syracuseStep 695621 = 130429) (by norm_num)
theorem B367969 : Blo 323837 367969 := bbase (se 2 (by rfl) ⟨137988, by rfl⟩ : syracuseStep 367969 = 275977) (by norm_num)
theorem B826757 : Blo 323837 826757 := bbase (se 4 (by rfl) ⟨77508, by rfl⟩ : syracuseStep 826757 = 155017) (by norm_num)
theorem B368005 : Blo 323837 368005 := bbase (se 4 (by rfl) ⟨34500, by rfl⟩ : syracuseStep 368005 = 69001) (by norm_num)
theorem B368041 : Blo 323837 368041 := bbase (se 2 (by rfl) ⟨138015, by rfl⟩ : syracuseStep 368041 = 276031) (by norm_num)
theorem B368077 : Blo 323837 368077 := bbase (se 3 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 368077 = 138029) (by norm_num)
theorem B663005 : Blo 323837 663005 := bbase (se 3 (by rfl) ⟨124313, by rfl⟩ : syracuseStep 663005 = 248627) (by norm_num)
theorem B368113 : Blo 323837 368113 := bbase (se 2 (by rfl) ⟨138042, by rfl⟩ : syracuseStep 368113 = 276085) (by norm_num)
theorem B368149 : Blo 323837 368149 := bbase (se 6 (by rfl) ⟨8628, by rfl⟩ : syracuseStep 368149 = 17257) (by norm_num)
theorem B368185 : Blo 323837 368185 := bbase (se 2 (by rfl) ⟨138069, by rfl⟩ : syracuseStep 368185 = 276139) (by norm_num)
theorem B826949 : Blo 323837 826949 := bbase (se 4 (by rfl) ⟨77526, by rfl⟩ : syracuseStep 826949 = 155053) (by norm_num)
theorem B368221 : Blo 323837 368221 := bbase (se 3 (by rfl) ⟨69041, by rfl⟩ : syracuseStep 368221 = 138083) (by norm_num)
theorem B728693 : Blo 323837 728693 := bbase (se 5 (by rfl) ⟨34157, by rfl⟩ : syracuseStep 728693 = 68315) (by norm_num)
theorem B368257 : Blo 323837 368257 := bbase (se 2 (by rfl) ⟨138096, by rfl⟩ : syracuseStep 368257 = 276193) (by norm_num)
theorem B368293 : Blo 323837 368293 := bbase (se 4 (by rfl) ⟨34527, by rfl⟩ : syracuseStep 368293 = 69055) (by norm_num)
theorem B1482421 : Blo 323837 1482421 := bbase (se 5 (by rfl) ⟨69488, by rfl⟩ : syracuseStep 1482421 = 138977) (by norm_num)
theorem B728765 : Blo 323837 728765 := bbase (se 3 (by rfl) ⟨136643, by rfl⟩ : syracuseStep 728765 = 273287) (by norm_num)
theorem B368329 : Blo 323837 368329 := bbase (se 2 (by rfl) ⟨138123, by rfl⟩ : syracuseStep 368329 = 276247) (by norm_num)
theorem B368365 : Blo 323837 368365 := bbase (se 3 (by rfl) ⟨69068, by rfl⟩ : syracuseStep 368365 = 138137) (by norm_num)
theorem B728837 : Blo 323837 728837 := bbase (se 4 (by rfl) ⟨68328, by rfl⟩ : syracuseStep 728837 = 136657) (by norm_num)
theorem B368401 : Blo 323837 368401 := bbase (se 2 (by rfl) ⟨138150, by rfl⟩ : syracuseStep 368401 = 276301) (by norm_num)
theorem B368437 : Blo 323837 368437 := bbase (se 5 (by rfl) ⟨17270, by rfl⟩ : syracuseStep 368437 = 34541) (by norm_num)
theorem B1646405 : Blo 323837 1646405 := bbase (se 4 (by rfl) ⟨154350, by rfl⟩ : syracuseStep 1646405 = 308701) (by norm_num)
theorem B728909 : Blo 323837 728909 := bbase (se 3 (by rfl) ⟨136670, by rfl⟩ : syracuseStep 728909 = 273341) (by norm_num)
theorem B368473 : Blo 323837 368473 := bbase (se 2 (by rfl) ⟨138177, by rfl⟩ : syracuseStep 368473 = 276355) (by norm_num)
theorem B368509 : Blo 323837 368509 := bbase (se 3 (by rfl) ⟨69095, by rfl⟩ : syracuseStep 368509 = 138191) (by norm_num)
theorem B728981 : Blo 323837 728981 := bbase (se 6 (by rfl) ⟨17085, by rfl⟩ : syracuseStep 728981 = 34171) (by norm_num)
theorem B827293 : Blo 323837 827293 := bbase (se 3 (by rfl) ⟨155117, by rfl⟩ : syracuseStep 827293 = 310235) (by norm_num)
theorem B368545 : Blo 323837 368545 := bbase (se 2 (by rfl) ⟨138204, by rfl⟩ : syracuseStep 368545 = 276409) (by norm_num)
theorem B368581 : Blo 323837 368581 := bbase (se 4 (by rfl) ⟨34554, by rfl⟩ : syracuseStep 368581 = 69109) (by norm_num)
theorem B729053 : Blo 323837 729053 := bbase (se 3 (by rfl) ⟨136697, by rfl⟩ : syracuseStep 729053 = 273395) (by norm_num)
theorem B368617 : Blo 323837 368617 := bbase (se 2 (by rfl) ⟨138231, by rfl⟩ : syracuseStep 368617 = 276463) (by norm_num)
theorem B827405 : Blo 323837 827405 := bbase (se 3 (by rfl) ⟨155138, by rfl⟩ : syracuseStep 827405 = 310277) (by norm_num)
theorem B368653 : Blo 323837 368653 := bbase (se 3 (by rfl) ⟨69122, by rfl⟩ : syracuseStep 368653 = 138245) (by norm_num)
theorem B729125 : Blo 323837 729125 := bbase (se 4 (by rfl) ⟨68355, by rfl⟩ : syracuseStep 729125 = 136711) (by norm_num)
theorem B368689 : Blo 323837 368689 := bbase (se 2 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 368689 = 276517) (by norm_num)
theorem B368725 : Blo 323837 368725 := bbase (se 8 (by rfl) ⟨2160, by rfl⟩ : syracuseStep 368725 = 4321) (by norm_num)
theorem B729197 : Blo 323837 729197 := bbase (se 3 (by rfl) ⟨136724, by rfl⟩ : syracuseStep 729197 = 273449) (by norm_num)
theorem B368761 : Blo 323837 368761 := bbase (se 2 (by rfl) ⟨138285, by rfl⟩ : syracuseStep 368761 = 276571) (by norm_num)
theorem B368797 : Blo 323837 368797 := bbase (se 3 (by rfl) ⟨69149, by rfl⟩ : syracuseStep 368797 = 138299) (by norm_num)
theorem B729269 : Blo 323837 729269 := bbase (se 5 (by rfl) ⟨34184, by rfl⟩ : syracuseStep 729269 = 68369) (by norm_num)
theorem B696509 : Blo 323837 696509 := bbase (se 3 (by rfl) ⟨130595, by rfl⟩ : syracuseStep 696509 = 261191) (by norm_num)
theorem B827597 : Blo 323837 827597 := bbase (se 3 (by rfl) ⟨155174, by rfl⟩ : syracuseStep 827597 = 310349) (by norm_num)
theorem B729341 : Blo 323837 729341 := bbase (se 3 (by rfl) ⟨136751, by rfl⟩ : syracuseStep 729341 = 273503) (by norm_num)
theorem B729413 : Blo 323837 729413 := bbase (se 4 (by rfl) ⟨68382, by rfl⟩ : syracuseStep 729413 = 136765) (by norm_num)
theorem B729485 : Blo 323837 729485 := bbase (se 3 (by rfl) ⟨136778, by rfl⟩ : syracuseStep 729485 = 273557) (by norm_num)
theorem B696757 : Blo 323837 696757 := bbase (se 5 (by rfl) ⟨32660, by rfl⟩ : syracuseStep 696757 = 65321) (by norm_num)
theorem B926149 : Blo 323837 926149 := bbase (se 4 (by rfl) ⟨86826, by rfl⟩ : syracuseStep 926149 = 173653) (by norm_num)
theorem B729557 : Blo 323837 729557 := bbase (se 7 (by rfl) ⟨8549, by rfl⟩ : syracuseStep 729557 = 17099) (by norm_num)
theorem B729629 : Blo 323837 729629 := bbase (se 3 (by rfl) ⟨136805, by rfl⟩ : syracuseStep 729629 = 273611) (by norm_num)
theorem B827941 : Blo 323837 827941 := bbase (se 4 (by rfl) ⟨77619, by rfl⟩ : syracuseStep 827941 = 155239) (by norm_num)
theorem B1679957 : Blo 323837 1679957 := bbase (se 8 (by rfl) ⟨9843, by rfl⟩ : syracuseStep 1679957 = 19687) (by norm_num)
theorem B729701 : Blo 323837 729701 := bbase (se 4 (by rfl) ⟨68409, by rfl⟩ : syracuseStep 729701 = 136819) (by norm_num)
theorem B926309 : Blo 323837 926309 := bbase (se 4 (by rfl) ⟨86841, by rfl⟩ : syracuseStep 926309 = 173683) (by norm_num)
theorem B828053 : Blo 323837 828053 := bbase (se 6 (by rfl) ⟨19407, by rfl⟩ : syracuseStep 828053 = 38815) (by norm_num)
theorem B729773 : Blo 323837 729773 := bbase (se 3 (by rfl) ⟨136832, by rfl⟩ : syracuseStep 729773 = 273665) (by norm_num)
theorem B729845 : Blo 323837 729845 := bbase (se 5 (by rfl) ⟨34211, by rfl⟩ : syracuseStep 729845 = 68423) (by norm_num)
theorem B729917 : Blo 323837 729917 := bbase (se 3 (by rfl) ⟨136859, by rfl⟩ : syracuseStep 729917 = 273719) (by norm_num)
theorem B926549 : Blo 323837 926549 := bbase (se 9 (by rfl) ⟨2714, by rfl⟩ : syracuseStep 926549 = 5429) (by norm_num)
theorem B828245 : Blo 323837 828245 := bbase (se 9 (by rfl) ⟨2426, by rfl⟩ : syracuseStep 828245 = 4853) (by norm_num)
theorem B992101 : Blo 323837 992101 := bbase (se 4 (by rfl) ⟨93009, by rfl⟩ : syracuseStep 992101 = 186019) (by norm_num)
theorem B729989 : Blo 323837 729989 := bbase (se 4 (by rfl) ⟨68436, by rfl⟩ : syracuseStep 729989 = 136873) (by norm_num)
theorem B697261 : Blo 323837 697261 := bbase (se 3 (by rfl) ⟨130736, by rfl⟩ : syracuseStep 697261 = 261473) (by norm_num)
theorem B730061 : Blo 323837 730061 := bbase (se 3 (by rfl) ⟨136886, by rfl⟩ : syracuseStep 730061 = 273773) (by norm_num)
theorem B730133 : Blo 323837 730133 := bbase (se 6 (by rfl) ⟨17112, by rfl⟩ : syracuseStep 730133 = 34225) (by norm_num)
theorem B926741 : Blo 323837 926741 := bbase (se 6 (by rfl) ⟨21720, by rfl⟩ : syracuseStep 926741 = 43441) (by norm_num)
theorem B1647701 : Blo 323837 1647701 := bbase (se 8 (by rfl) ⟨9654, by rfl⟩ : syracuseStep 1647701 = 19309) (by norm_num)
theorem B730205 : Blo 323837 730205 := bbase (se 3 (by rfl) ⟨136913, by rfl⟩ : syracuseStep 730205 = 273827) (by norm_num)
theorem B730277 : Blo 323837 730277 := bbase (se 4 (by rfl) ⟨68463, by rfl⟩ : syracuseStep 730277 = 136927) (by norm_num)
theorem B828589 : Blo 323837 828589 := bbase (se 3 (by rfl) ⟨155360, by rfl⟩ : syracuseStep 828589 = 310721) (by norm_num)
theorem B730349 : Blo 323837 730349 := bbase (se 3 (by rfl) ⟨136940, by rfl⟩ : syracuseStep 730349 = 273881) (by norm_num)
theorem B828701 : Blo 323837 828701 := bbase (se 3 (by rfl) ⟨155381, by rfl⟩ : syracuseStep 828701 = 310763) (by norm_num)
theorem B730421 : Blo 323837 730421 := bbase (se 5 (by rfl) ⟨34238, by rfl⟩ : syracuseStep 730421 = 68477) (by norm_num)
theorem B730493 : Blo 323837 730493 := bbase (se 3 (by rfl) ⟨136967, by rfl⟩ : syracuseStep 730493 = 273935) (by norm_num)
theorem B730565 : Blo 323837 730565 := bbase (se 4 (by rfl) ⟨68490, by rfl⟩ : syracuseStep 730565 = 136981) (by norm_num)
theorem B828893 : Blo 323837 828893 := bbase (se 3 (by rfl) ⟨155417, by rfl⟩ : syracuseStep 828893 = 310835) (by norm_num)
theorem B730637 : Blo 323837 730637 := bbase (se 3 (by rfl) ⟨136994, by rfl⟩ : syracuseStep 730637 = 273989) (by norm_num)
theorem B1123877 : Blo 323837 1123877 := bbase (se 4 (by rfl) ⟨105363, by rfl⟩ : syracuseStep 1123877 = 210727) (by norm_num)
theorem B730709 : Blo 323837 730709 := bbase (se 8 (by rfl) ⟨4281, by rfl⟩ : syracuseStep 730709 = 8563) (by norm_num)
theorem B370273 : Blo 323837 370273 := bbase (se 2 (by rfl) ⟨138852, by rfl⟩ : syracuseStep 370273 = 277705) (by norm_num)
theorem B730781 : Blo 323837 730781 := bbase (se 3 (by rfl) ⟨137021, by rfl⟩ : syracuseStep 730781 = 274043) (by norm_num)
theorem B730853 : Blo 323837 730853 := bbase (se 4 (by rfl) ⟨68517, by rfl⟩ : syracuseStep 730853 = 137035) (by norm_num)
theorem B698149 : Blo 323837 698149 := bbase (se 4 (by rfl) ⟨65451, by rfl⟩ : syracuseStep 698149 = 130903) (by norm_num)
theorem B730925 : Blo 323837 730925 := bbase (se 3 (by rfl) ⟨137048, by rfl⟩ : syracuseStep 730925 = 274097) (by norm_num)
theorem B829237 : Blo 323837 829237 := bbase (se 5 (by rfl) ⟨38870, by rfl⟩ : syracuseStep 829237 = 77741) (by norm_num)
theorem B730997 : Blo 323837 730997 := bbase (se 5 (by rfl) ⟨34265, by rfl⟩ : syracuseStep 730997 = 68531) (by norm_num)
theorem B829349 : Blo 323837 829349 := bbase (se 4 (by rfl) ⟨77751, by rfl⟩ : syracuseStep 829349 = 155503) (by norm_num)
theorem B731069 : Blo 323837 731069 := bbase (se 3 (by rfl) ⟨137075, by rfl⟩ : syracuseStep 731069 = 274151) (by norm_num)
theorem B927733 : Blo 323837 927733 := bbase (se 5 (by rfl) ⟨43487, by rfl⟩ : syracuseStep 927733 = 86975) (by norm_num)
theorem B731141 : Blo 323837 731141 := bbase (se 4 (by rfl) ⟨68544, by rfl⟩ : syracuseStep 731141 = 137089) (by norm_num)
theorem B731213 : Blo 323837 731213 := bbase (se 3 (by rfl) ⟨137102, by rfl⟩ : syracuseStep 731213 = 274205) (by norm_num)
theorem B829541 : Blo 323837 829541 := bbase (se 4 (by rfl) ⟨77769, by rfl⟩ : syracuseStep 829541 = 155539) (by norm_num)
theorem B731285 : Blo 323837 731285 := bbase (se 6 (by rfl) ⟨17139, by rfl⟩ : syracuseStep 731285 = 34279) (by norm_num)
theorem B731357 : Blo 323837 731357 := bbase (se 3 (by rfl) ⟨137129, by rfl⟩ : syracuseStep 731357 = 274259) (by norm_num)
theorem B3352853 : Blo 323837 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B698645 : Blo 323837 698645 := bbase (se 6 (by rfl) ⟨16374, by rfl⟩ : syracuseStep 698645 = 32749) (by norm_num)
theorem B731429 : Blo 323837 731429 := bbase (se 4 (by rfl) ⟨68571, by rfl⟩ : syracuseStep 731429 = 137143) (by norm_num)
theorem B9382229 : Blo 323837 9382229 := bbase (se 10 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 9382229 = 27487) (by norm_num)
theorem B1648997 : Blo 323837 1648997 := bbase (se 4 (by rfl) ⟨154593, by rfl⟩ : syracuseStep 1648997 = 309187) (by norm_num)
theorem B731501 : Blo 323837 731501 := bbase (se 3 (by rfl) ⟨137156, by rfl⟩ : syracuseStep 731501 = 274313) (by norm_num)
theorem B731573 : Blo 323837 731573 := bbase (se 5 (by rfl) ⟨34292, by rfl⟩ : syracuseStep 731573 = 68585) (by norm_num)
theorem B731645 : Blo 323837 731645 := bbase (se 3 (by rfl) ⟨137183, by rfl⟩ : syracuseStep 731645 = 274367) (by norm_num)
theorem B731717 : Blo 323837 731717 := bbase (se 4 (by rfl) ⟨68598, by rfl⟩ : syracuseStep 731717 = 137197) (by norm_num)
theorem B2894453 : Blo 323837 2894453 := bbase (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) (by norm_num)
theorem B731789 : Blo 323837 731789 := bbase (se 3 (by rfl) ⟨137210, by rfl⟩ : syracuseStep 731789 = 274421) (by norm_num)
theorem B731861 : Blo 323837 731861 := bbase (se 7 (by rfl) ⟨8576, by rfl⟩ : syracuseStep 731861 = 17153) (by norm_num)
theorem B2075381 : Blo 323837 2075381 := bbase (se 5 (by rfl) ⟨97283, by rfl⟩ : syracuseStep 2075381 = 194567) (by norm_num)
theorem B994069 : Blo 323837 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B731933 : Blo 323837 731933 := bbase (se 3 (by rfl) ⟨137237, by rfl⟩ : syracuseStep 731933 = 274475) (by norm_num)
theorem B994117 : Blo 323837 994117 := bbase (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) (by norm_num)
theorem B732005 : Blo 323837 732005 := bbase (se 4 (by rfl) ⟨68625, by rfl⟩ : syracuseStep 732005 = 137251) (by norm_num)
theorem B732077 : Blo 323837 732077 := bbase (se 3 (by rfl) ⟨137264, by rfl⟩ : syracuseStep 732077 = 274529) (by norm_num)
theorem B732149 : Blo 323837 732149 := bbase (se 5 (by rfl) ⟨34319, by rfl⟩ : syracuseStep 732149 = 68639) (by norm_num)
theorem B732221 : Blo 323837 732221 := bbase (se 3 (by rfl) ⟨137291, by rfl⟩ : syracuseStep 732221 = 274583) (by norm_num)
theorem B371773 : Blo 323837 371773 := bbase (se 3 (by rfl) ⟨69707, by rfl⟩ : syracuseStep 371773 = 139415) (by norm_num)
theorem B928837 : Blo 323837 928837 := bbase (se 4 (by rfl) ⟨87078, by rfl⟩ : syracuseStep 928837 = 174157) (by norm_num)
theorem B1387637 : Blo 323837 1387637 := bbase (se 5 (by rfl) ⟨65045, by rfl⟩ : syracuseStep 1387637 = 130091) (by norm_num)
theorem B732293 : Blo 323837 732293 := bbase (se 4 (by rfl) ⟨68652, by rfl⟩ : syracuseStep 732293 = 137305) (by norm_num)
theorem B699533 : Blo 323837 699533 := bbase (se 3 (by rfl) ⟨131162, by rfl⟩ : syracuseStep 699533 = 262325) (by norm_num)
theorem B1846421 : Blo 323837 1846421 := bbase (se 6 (by rfl) ⟨43275, by rfl⟩ : syracuseStep 1846421 = 86551) (by norm_num)
theorem B732365 : Blo 323837 732365 := bbase (se 3 (by rfl) ⟨137318, by rfl⟩ : syracuseStep 732365 = 274637) (by norm_num)
theorem B699653 : Blo 323837 699653 := bbase (se 4 (by rfl) ⟨65592, by rfl⟩ : syracuseStep 699653 = 131185) (by norm_num)
theorem B732437 : Blo 323837 732437 := bbase (se 6 (by rfl) ⟨17166, by rfl⟩ : syracuseStep 732437 = 34333) (by norm_num)
theorem B732509 : Blo 323837 732509 := bbase (se 3 (by rfl) ⟨137345, by rfl⟩ : syracuseStep 732509 = 274691) (by norm_num)
theorem B372097 : Blo 323837 372097 := bbase (se 2 (by rfl) ⟨139536, by rfl⟩ : syracuseStep 372097 = 279073) (by norm_num)
theorem B1093013 : Blo 323837 1093013 := bbase (se 6 (by rfl) ⟨25617, by rfl⟩ : syracuseStep 1093013 = 51235) (by norm_num)
theorem B1387925 : Blo 323837 1387925 := bbase (se 6 (by rfl) ⟨32529, by rfl⟩ : syracuseStep 1387925 = 65059) (by norm_num)
theorem B732581 : Blo 323837 732581 := bbase (se 4 (by rfl) ⟨68679, by rfl⟩ : syracuseStep 732581 = 137359) (by norm_num)
theorem B2633141 : Blo 323837 2633141 := bbase (se 5 (by rfl) ⟨123428, by rfl⟩ : syracuseStep 2633141 = 246857) (by norm_num)
theorem B732653 : Blo 323837 732653 := bbase (se 3 (by rfl) ⟨137372, by rfl⟩ : syracuseStep 732653 = 274745) (by norm_num)
theorem B2469365 : Blo 323837 2469365 := bbase (se 5 (by rfl) ⟨115751, by rfl⟩ : syracuseStep 2469365 = 231503) (by norm_num)
theorem B732725 : Blo 323837 732725 := bbase (se 5 (by rfl) ⟨34346, by rfl⟩ : syracuseStep 732725 = 68693) (by norm_num)
theorem B1650293 : Blo 323837 1650293 := bbase (se 5 (by rfl) ⟨77357, by rfl⟩ : syracuseStep 1650293 = 154715) (by norm_num)
theorem B732797 : Blo 323837 732797 := bbase (se 3 (by rfl) ⟨137399, by rfl⟩ : syracuseStep 732797 = 274799) (by norm_num)
theorem B732869 : Blo 323837 732869 := bbase (se 4 (by rfl) ⟨68706, by rfl⟩ : syracuseStep 732869 = 137413) (by norm_num)
theorem B437981 : Blo 323837 437981 := bbase (se 3 (by rfl) ⟨82121, by rfl⟩ : syracuseStep 437981 = 164243) (by norm_num)
theorem B372485 : Blo 323837 372485 := bbase (se 4 (by rfl) ⟨34920, by rfl⟩ : syracuseStep 372485 = 69841) (by norm_num)
theorem B732941 : Blo 323837 732941 := bbase (se 3 (by rfl) ⟨137426, by rfl⟩ : syracuseStep 732941 = 274853) (by norm_num)
theorem B6893333 : Blo 323837 6893333 := bbase (se 6 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 6893333 = 323125) (by norm_num)
theorem B1093445 : Blo 323837 1093445 := bbase (se 4 (by rfl) ⟨102510, by rfl⟩ : syracuseStep 1093445 = 205021) (by norm_num)
theorem B733013 : Blo 323837 733013 := bbase (se 9 (by rfl) ⟨2147, by rfl⟩ : syracuseStep 733013 = 4295) (by norm_num)
theorem B3125141 : Blo 323837 3125141 := bbase (se 6 (by rfl) ⟨73245, by rfl⟩ : syracuseStep 3125141 = 146491) (by norm_num)
theorem B733085 : Blo 323837 733085 := bbase (se 3 (by rfl) ⟨137453, by rfl⟩ : syracuseStep 733085 = 274907) (by norm_num)
theorem B733157 : Blo 323837 733157 := bbase (se 4 (by rfl) ⟨68733, by rfl⟩ : syracuseStep 733157 = 137467) (by norm_num)
theorem B733229 : Blo 323837 733229 := bbase (se 3 (by rfl) ⟨137480, by rfl⟩ : syracuseStep 733229 = 274961) (by norm_num)
theorem B733301 : Blo 323837 733301 := bbase (se 5 (by rfl) ⟨34373, by rfl⟩ : syracuseStep 733301 = 68747) (by norm_num)
theorem B1388677 : Blo 323837 1388677 := bbase (se 4 (by rfl) ⟨130188, by rfl⟩ : syracuseStep 1388677 = 260377) (by norm_num)
theorem B733373 : Blo 323837 733373 := bbase (se 3 (by rfl) ⟨137507, by rfl⟩ : syracuseStep 733373 = 275015) (by norm_num)
theorem B1093877 : Blo 323837 1093877 := bbase (se 5 (by rfl) ⟨51275, by rfl⟩ : syracuseStep 1093877 = 102551) (by norm_num)
theorem B733445 : Blo 323837 733445 := bbase (se 4 (by rfl) ⟨68760, by rfl⟩ : syracuseStep 733445 = 137521) (by norm_num)
theorem B733517 : Blo 323837 733517 := bbase (se 3 (by rfl) ⟨137534, by rfl⟩ : syracuseStep 733517 = 275069) (by norm_num)
theorem B733589 : Blo 323837 733589 := bbase (se 6 (by rfl) ⟨17193, by rfl⟩ : syracuseStep 733589 = 34387) (by norm_num)
theorem B733661 : Blo 323837 733661 := bbase (se 3 (by rfl) ⟨137561, by rfl⟩ : syracuseStep 733661 = 275123) (by norm_num)
theorem B831973 : Blo 323837 831973 := bbase (se 4 (by rfl) ⟨77997, by rfl⟩ : syracuseStep 831973 = 155995) (by norm_num)
theorem B1192421 : Blo 323837 1192421 := bbase (se 4 (by rfl) ⟨111789, by rfl⟩ : syracuseStep 1192421 = 223579) (by norm_num)
theorem B733733 : Blo 323837 733733 := bbase (se 4 (by rfl) ⟨68787, by rfl⟩ : syracuseStep 733733 = 137575) (by norm_num)
theorem B930341 : Blo 323837 930341 := bbase (se 4 (by rfl) ⟨87219, by rfl⟩ : syracuseStep 930341 = 174439) (by norm_num)
theorem B733805 : Blo 323837 733805 := bbase (se 3 (by rfl) ⟨137588, by rfl⟩ : syracuseStep 733805 = 275177) (by norm_num)
theorem B1094309 : Blo 323837 1094309 := bbase (se 4 (by rfl) ⟨102591, by rfl⟩ : syracuseStep 1094309 = 205183) (by norm_num)
theorem B733877 : Blo 323837 733877 := bbase (se 5 (by rfl) ⟨34400, by rfl⟩ : syracuseStep 733877 = 68801) (by norm_num)
theorem B733949 : Blo 323837 733949 := bbase (se 3 (by rfl) ⟨137615, by rfl⟩ : syracuseStep 733949 = 275231) (by norm_num)
theorem B734021 : Blo 323837 734021 := bbase (se 4 (by rfl) ⟨68814, by rfl⟩ : syracuseStep 734021 = 137629) (by norm_num)
theorem B1389413 : Blo 323837 1389413 := bbase (se 4 (by rfl) ⟨130257, by rfl⟩ : syracuseStep 1389413 = 260515) (by norm_num)
theorem B1651589 : Blo 323837 1651589 := bbase (se 4 (by rfl) ⟨154836, by rfl⟩ : syracuseStep 1651589 = 309673) (by norm_num)
theorem B734093 : Blo 323837 734093 := bbase (se 3 (by rfl) ⟨137642, by rfl⟩ : syracuseStep 734093 = 275285) (by norm_num)
theorem B734165 : Blo 323837 734165 := bbase (se 7 (by rfl) ⟨8603, by rfl⟩ : syracuseStep 734165 = 17207) (by norm_num)
theorem B373753 : Blo 323837 373753 := bbase (se 2 (by rfl) ⟨140157, by rfl⟩ : syracuseStep 373753 = 280315) (by norm_num)
theorem B734237 : Blo 323837 734237 := bbase (se 3 (by rfl) ⟨137669, by rfl⟩ : syracuseStep 734237 = 275339) (by norm_num)
theorem B1094741 : Blo 323837 1094741 := bbase (se 8 (by rfl) ⟨6414, by rfl⟩ : syracuseStep 1094741 = 12829) (by norm_num)
theorem B734309 : Blo 323837 734309 := bbase (se 4 (by rfl) ⟨68841, by rfl⟩ : syracuseStep 734309 = 137683) (by norm_num)
theorem B701581 : Blo 323837 701581 := bbase (se 3 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 701581 = 263093) (by norm_num)
theorem B701597 : Blo 323837 701597 := bbase (se 3 (by rfl) ⟨131549, by rfl⟩ : syracuseStep 701597 = 263099) (by norm_num)
theorem B734381 : Blo 323837 734381 := bbase (se 3 (by rfl) ⟨137696, by rfl⟩ : syracuseStep 734381 = 275393) (by norm_num)
theorem B1881269 : Blo 323837 1881269 := bbase (se 5 (by rfl) ⟨88184, by rfl⟩ : syracuseStep 1881269 = 176369) (by norm_num)
theorem B734453 : Blo 323837 734453 := bbase (se 5 (by rfl) ⟨34427, by rfl⟩ : syracuseStep 734453 = 68855) (by norm_num)
theorem B734525 : Blo 323837 734525 := bbase (se 3 (by rfl) ⟨137723, by rfl⟩ : syracuseStep 734525 = 275447) (by norm_num)
theorem B734597 : Blo 323837 734597 := bbase (se 4 (by rfl) ⟨68868, by rfl⟩ : syracuseStep 734597 = 137737) (by norm_num)
theorem B734669 : Blo 323837 734669 := bbase (se 3 (by rfl) ⟨137750, by rfl⟩ : syracuseStep 734669 = 275501) (by norm_num)
theorem B1095173 : Blo 323837 1095173 := bbase (se 4 (by rfl) ⟨102672, by rfl⟩ : syracuseStep 1095173 = 205345) (by norm_num)
theorem B734741 : Blo 323837 734741 := bbase (se 6 (by rfl) ⟨17220, by rfl⟩ : syracuseStep 734741 = 34441) (by norm_num)
theorem B734813 : Blo 323837 734813 := bbase (se 3 (by rfl) ⟨137777, by rfl⟩ : syracuseStep 734813 = 275555) (by norm_num)
theorem B734885 : Blo 323837 734885 := bbase (se 4 (by rfl) ⟨68895, by rfl⟩ : syracuseStep 734885 = 137791) (by norm_num)
theorem B3192533 : Blo 323837 3192533 := bbase (se 7 (by rfl) ⟨37412, by rfl⟩ : syracuseStep 3192533 = 74825) (by norm_num)
theorem B734957 : Blo 323837 734957 := bbase (se 3 (by rfl) ⟨137804, by rfl⟩ : syracuseStep 734957 = 275609) (by norm_num)
theorem B735029 : Blo 323837 735029 := bbase (se 5 (by rfl) ⟨34454, by rfl⟩ : syracuseStep 735029 = 68909) (by norm_num)
theorem B1718101 : Blo 323837 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B735101 : Blo 323837 735101 := bbase (se 3 (by rfl) ⟨137831, by rfl⟩ : syracuseStep 735101 = 275663) (by norm_num)
theorem B472973 : Blo 323837 472973 := bbase (se 3 (by rfl) ⟨88682, by rfl⟩ : syracuseStep 472973 = 177365) (by norm_num)
theorem B2635669 : Blo 323837 2635669 := bbase (se 6 (by rfl) ⟨61773, by rfl⟩ : syracuseStep 2635669 = 123547) (by norm_num)
theorem B1095605 : Blo 323837 1095605 := bbase (se 5 (by rfl) ⟨51356, by rfl⟩ : syracuseStep 1095605 = 102713) (by norm_num)
theorem B735173 : Blo 323837 735173 := bbase (se 4 (by rfl) ⟨68922, by rfl⟩ : syracuseStep 735173 = 137845) (by norm_num)
theorem B1718261 : Blo 323837 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B735245 : Blo 323837 735245 := bbase (se 3 (by rfl) ⟨137858, by rfl⟩ : syracuseStep 735245 = 275717) (by norm_num)
theorem B735317 : Blo 323837 735317 := bbase (se 8 (by rfl) ⟨4308, by rfl⟩ : syracuseStep 735317 = 8617) (by norm_num)
theorem B931925 : Blo 323837 931925 := bbase (se 8 (by rfl) ⟨5460, by rfl⟩ : syracuseStep 931925 = 10921) (by norm_num)
theorem B1652885 : Blo 323837 1652885 := bbase (se 6 (by rfl) ⟨38739, by rfl⟩ : syracuseStep 1652885 = 77479) (by norm_num)
theorem B735389 : Blo 323837 735389 := bbase (se 3 (by rfl) ⟨137885, by rfl⟩ : syracuseStep 735389 = 275771) (by norm_num)
theorem B735461 : Blo 323837 735461 := bbase (se 4 (by rfl) ⟨68949, by rfl⟩ : syracuseStep 735461 = 137899) (by norm_num)
theorem B735533 : Blo 323837 735533 := bbase (se 3 (by rfl) ⟨137912, by rfl⟩ : syracuseStep 735533 = 275825) (by norm_num)
theorem B1096037 : Blo 323837 1096037 := bbase (se 4 (by rfl) ⟨102753, by rfl⟩ : syracuseStep 1096037 = 205507) (by norm_num)
theorem B735605 : Blo 323837 735605 := bbase (se 5 (by rfl) ⟨34481, by rfl⟩ : syracuseStep 735605 = 68963) (by norm_num)
theorem B1325477 : Blo 323837 1325477 := bbase (se 4 (by rfl) ⟨124263, by rfl⟩ : syracuseStep 1325477 = 248527) (by norm_num)
theorem B440749 : Blo 323837 440749 := bbase (se 3 (by rfl) ⟨82640, by rfl⟩ : syracuseStep 440749 = 165281) (by norm_num)
theorem B735677 : Blo 323837 735677 := bbase (se 3 (by rfl) ⟨137939, by rfl⟩ : syracuseStep 735677 = 275879) (by norm_num)
theorem B735749 : Blo 323837 735749 := bbase (se 4 (by rfl) ⟨68976, by rfl⟩ : syracuseStep 735749 = 137953) (by norm_num)
theorem B6404629 : Blo 323837 6404629 := bbase (se 6 (by rfl) ⟨150108, by rfl⟩ : syracuseStep 6404629 = 300217) (by norm_num)
theorem B1325605 : Blo 323837 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B735821 : Blo 323837 735821 := bbase (se 3 (by rfl) ⟨137966, by rfl⟩ : syracuseStep 735821 = 275933) (by norm_num)
theorem B2767445 : Blo 323837 2767445 := bbase (se 8 (by rfl) ⟨16215, by rfl⟩ : syracuseStep 2767445 = 32431) (by norm_num)
theorem B703085 : Blo 323837 703085 := bbase (se 3 (by rfl) ⟨131828, by rfl⟩ : syracuseStep 703085 = 263657) (by norm_num)
theorem B2341493 : Blo 323837 2341493 := bbase (se 5 (by rfl) ⟨109757, by rfl⟩ : syracuseStep 2341493 = 219515) (by norm_num)
theorem B440965 : Blo 323837 440965 := bbase (se 4 (by rfl) ⟨41340, by rfl⟩ : syracuseStep 440965 = 82681) (by norm_num)
theorem B735893 : Blo 323837 735893 := bbase (se 6 (by rfl) ⟨17247, by rfl⟩ : syracuseStep 735893 = 34495) (by norm_num)
theorem B735965 : Blo 323837 735965 := bbase (se 3 (by rfl) ⟨137993, by rfl⟩ : syracuseStep 735965 = 275987) (by norm_num)
theorem B932597 : Blo 323837 932597 := bbase (se 5 (by rfl) ⟨43715, by rfl⟩ : syracuseStep 932597 = 87431) (by norm_num)
theorem B1096469 : Blo 323837 1096469 := bbase (se 6 (by rfl) ⟨25698, by rfl⟩ : syracuseStep 1096469 = 51397) (by norm_num)
theorem B736037 : Blo 323837 736037 := bbase (se 4 (by rfl) ⟨69003, by rfl⟩ : syracuseStep 736037 = 138007) (by norm_num)
theorem B736109 : Blo 323837 736109 := bbase (se 3 (by rfl) ⟨138020, by rfl⟩ : syracuseStep 736109 = 276041) (by norm_num)
theorem B736181 : Blo 323837 736181 := bbase (se 5 (by rfl) ⟨34508, by rfl⟩ : syracuseStep 736181 = 69017) (by norm_num)
theorem B736253 : Blo 323837 736253 := bbase (se 3 (by rfl) ⟨138047, by rfl⟩ : syracuseStep 736253 = 276095) (by norm_num)
theorem B736325 : Blo 323837 736325 := bbase (se 4 (by rfl) ⟨69030, by rfl⟩ : syracuseStep 736325 = 138061) (by norm_num)
theorem B736397 : Blo 323837 736397 := bbase (se 3 (by rfl) ⟨138074, by rfl⟩ : syracuseStep 736397 = 276149) (by norm_num)
theorem B933029 : Blo 323837 933029 := bbase (se 4 (by rfl) ⟨87471, by rfl⟩ : syracuseStep 933029 = 174943) (by norm_num)
theorem B1096901 : Blo 323837 1096901 := bbase (se 4 (by rfl) ⟨102834, by rfl⟩ : syracuseStep 1096901 = 205669) (by norm_num)
theorem B736469 : Blo 323837 736469 := bbase (se 7 (by rfl) ⟨8630, by rfl⟩ : syracuseStep 736469 = 17261) (by norm_num)
theorem B638237 : Blo 323837 638237 := bbase (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) (by norm_num)
theorem B736541 : Blo 323837 736541 := bbase (se 3 (by rfl) ⟨138101, by rfl⟩ : syracuseStep 736541 = 276203) (by norm_num)
theorem B736613 : Blo 323837 736613 := bbase (se 4 (by rfl) ⟨69057, by rfl⟩ : syracuseStep 736613 = 138115) (by norm_num)
theorem B1654181 : Blo 323837 1654181 := bbase (se 4 (by rfl) ⟨155079, by rfl⟩ : syracuseStep 1654181 = 310159) (by norm_num)
theorem B736685 : Blo 323837 736685 := bbase (se 3 (by rfl) ⟨138128, by rfl⟩ : syracuseStep 736685 = 276257) (by norm_num)
theorem B736757 : Blo 323837 736757 := bbase (se 5 (by rfl) ⟨34535, by rfl⟩ : syracuseStep 736757 = 69071) (by norm_num)
theorem B736829 : Blo 323837 736829 := bbase (se 3 (by rfl) ⟨138155, by rfl⟩ : syracuseStep 736829 = 276311) (by norm_num)
theorem B1097333 : Blo 323837 1097333 := bbase (se 5 (by rfl) ⟨51437, by rfl⟩ : syracuseStep 1097333 = 102875) (by norm_num)
theorem B1326725 : Blo 323837 1326725 := bbase (se 4 (by rfl) ⟨124380, by rfl⟩ : syracuseStep 1326725 = 248761) (by norm_num)
theorem B736901 : Blo 323837 736901 := bbase (se 4 (by rfl) ⟨69084, by rfl⟩ : syracuseStep 736901 = 138169) (by norm_num)
theorem B736973 : Blo 323837 736973 := bbase (se 3 (by rfl) ⟨138182, by rfl⟩ : syracuseStep 736973 = 276365) (by norm_num)
theorem B737045 : Blo 323837 737045 := bbase (se 6 (by rfl) ⟨17274, by rfl⟩ : syracuseStep 737045 = 34549) (by norm_num)
theorem B737117 : Blo 323837 737117 := bbase (se 3 (by rfl) ⟨138209, by rfl⟩ : syracuseStep 737117 = 276419) (by norm_num)
theorem B737189 : Blo 323837 737189 := bbase (se 4 (by rfl) ⟨69111, by rfl⟩ : syracuseStep 737189 = 138223) (by norm_num)
theorem B737261 : Blo 323837 737261 := bbase (se 3 (by rfl) ⟨138236, by rfl⟩ : syracuseStep 737261 = 276473) (by norm_num)
theorem B1097765 : Blo 323837 1097765 := bbase (se 4 (by rfl) ⟨102915, by rfl⟩ : syracuseStep 1097765 = 205831) (by norm_num)
theorem B737333 : Blo 323837 737333 := bbase (se 5 (by rfl) ⟨34562, by rfl⟩ : syracuseStep 737333 = 69125) (by norm_num)
theorem B1392709 : Blo 323837 1392709 := bbase (se 4 (by rfl) ⟨130566, by rfl⟩ : syracuseStep 1392709 = 261133) (by norm_num)
theorem B409709 : Blo 323837 409709 := bbase (se 3 (by rfl) ⟨76820, by rfl⟩ : syracuseStep 409709 = 153641) (by norm_num)
theorem B737405 : Blo 323837 737405 := bbase (se 3 (by rfl) ⟨138263, by rfl⟩ : syracuseStep 737405 = 276527) (by norm_num)
theorem B737477 : Blo 323837 737477 := bbase (se 4 (by rfl) ⟨69138, by rfl⟩ : syracuseStep 737477 = 138277) (by norm_num)
theorem B737549 : Blo 323837 737549 := bbase (se 3 (by rfl) ⟨138290, by rfl⟩ : syracuseStep 737549 = 276581) (by norm_num)
theorem B737621 : Blo 323837 737621 := bbase (se 10 (by rfl) ⟨1080, by rfl⟩ : syracuseStep 737621 = 2161) (by norm_num)
theorem B409961 : Blo 323837 409961 := bbase (se 2 (by rfl) ⟨153735, by rfl⟩ : syracuseStep 409961 = 307471) (by norm_num)
theorem B410017 : Blo 323837 410017 := bbase (se 2 (by rfl) ⟨153756, by rfl⟩ : syracuseStep 410017 = 307513) (by norm_num)
theorem B1098197 : Blo 323837 1098197 := bbase (se 7 (by rfl) ⟨12869, by rfl⟩ : syracuseStep 1098197 = 25739) (by norm_num)
theorem B410113 : Blo 323837 410113 := bbase (se 2 (by rfl) ⟨153792, by rfl⟩ : syracuseStep 410113 = 307585) (by norm_num)
theorem B410285 : Blo 323837 410285 := bbase (se 3 (by rfl) ⟨76928, by rfl⟩ : syracuseStep 410285 = 153857) (by norm_num)
theorem B1655477 : Blo 323837 1655477 := bbase (se 5 (by rfl) ⟨77600, by rfl⟩ : syracuseStep 1655477 = 155201) (by norm_num)
theorem B410341 : Blo 323837 410341 := bbase (se 4 (by rfl) ⟨38469, by rfl⟩ : syracuseStep 410341 = 76939) (by norm_num)
theorem B1884917 : Blo 323837 1884917 := bbase (se 5 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 1884917 = 176711) (by norm_num)
theorem B508717 : Blo 323837 508717 := bbase (se 3 (by rfl) ⟨95384, by rfl⟩ : syracuseStep 508717 = 190769) (by norm_num)
theorem B410437 : Blo 323837 410437 := bbase (se 4 (by rfl) ⟨38478, by rfl⟩ : syracuseStep 410437 = 76957) (by norm_num)
theorem B1229701 : Blo 323837 1229701 := bbase (se 4 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 1229701 = 230569) (by norm_num)
theorem B1098629 : Blo 323837 1098629 := bbase (se 4 (by rfl) ⟨102996, by rfl⟩ : syracuseStep 1098629 = 205993) (by norm_num)
theorem B410609 : Blo 323837 410609 := bbase (se 2 (by rfl) ⟨153978, by rfl⟩ : syracuseStep 410609 = 307957) (by norm_num)
theorem B410665 : Blo 323837 410665 := bbase (se 2 (by rfl) ⟨153999, by rfl⟩ : syracuseStep 410665 = 307999) (by norm_num)
theorem B410761 : Blo 323837 410761 := bbase (se 2 (by rfl) ⟨154035, by rfl⟩ : syracuseStep 410761 = 308071) (by norm_num)
theorem B1230005 : Blo 323837 1230005 := bbase (se 5 (by rfl) ⟨57656, by rfl⟩ : syracuseStep 1230005 = 115313) (by norm_num)
theorem B410933 : Blo 323837 410933 := bbase (se 5 (by rfl) ⟨19262, by rfl⟩ : syracuseStep 410933 = 38525) (by norm_num)
theorem B1099061 : Blo 323837 1099061 := bbase (se 5 (by rfl) ⟨51518, by rfl⟩ : syracuseStep 1099061 = 103037) (by norm_num)
theorem B410989 : Blo 323837 410989 := bbase (se 3 (by rfl) ⟨77060, by rfl⟩ : syracuseStep 410989 = 154121) (by norm_num)
theorem B705925 : Blo 323837 705925 := bbase (se 4 (by rfl) ⟨66180, by rfl⟩ : syracuseStep 705925 = 132361) (by norm_num)
theorem B411085 : Blo 323837 411085 := bbase (se 3 (by rfl) ⟨77078, by rfl⟩ : syracuseStep 411085 = 154157) (by norm_num)
theorem B411257 : Blo 323837 411257 := bbase (se 2 (by rfl) ⟨154221, by rfl⟩ : syracuseStep 411257 = 308443) (by norm_num)
theorem B411313 : Blo 323837 411313 := bbase (se 2 (by rfl) ⟨154242, by rfl⟩ : syracuseStep 411313 = 308485) (by norm_num)
theorem B1099493 : Blo 323837 1099493 := bbase (se 4 (by rfl) ⟨103077, by rfl⟩ : syracuseStep 1099493 = 206155) (by norm_num)
theorem B411409 : Blo 323837 411409 := bbase (se 2 (by rfl) ⟨154278, by rfl⟩ : syracuseStep 411409 = 308557) (by norm_num)
theorem B411581 : Blo 323837 411581 := bbase (se 3 (by rfl) ⟨77171, by rfl⟩ : syracuseStep 411581 = 154343) (by norm_num)
theorem B1656773 : Blo 323837 1656773 := bbase (se 4 (by rfl) ⟨155322, by rfl⟩ : syracuseStep 1656773 = 310645) (by norm_num)
theorem B739277 : Blo 323837 739277 := bbase (se 3 (by rfl) ⟨138614, by rfl⟩ : syracuseStep 739277 = 277229) (by norm_num)
theorem B411637 : Blo 323837 411637 := bbase (se 5 (by rfl) ⟨19295, by rfl⟩ : syracuseStep 411637 = 38591) (by norm_num)
theorem B804917 : Blo 323837 804917 := bbase (se 5 (by rfl) ⟨37730, by rfl⟩ : syracuseStep 804917 = 75461) (by norm_num)
theorem B411733 : Blo 323837 411733 := bbase (se 8 (by rfl) ⟨2412, by rfl⟩ : syracuseStep 411733 = 4825) (by norm_num)
theorem B1099925 : Blo 323837 1099925 := bbase (se 6 (by rfl) ⟨25779, by rfl⟩ : syracuseStep 1099925 = 51559) (by norm_num)
theorem B411905 : Blo 323837 411905 := bbase (se 2 (by rfl) ⟨154464, by rfl⟩ : syracuseStep 411905 = 308929) (by norm_num)
theorem B411961 : Blo 323837 411961 := bbase (se 2 (by rfl) ⟨154485, by rfl⟩ : syracuseStep 411961 = 308971) (by norm_num)
theorem B346465 : Blo 323837 346465 := bbase (se 2 (by rfl) ⟨129924, by rfl⟩ : syracuseStep 346465 = 259849) (by norm_num)
theorem B412057 : Blo 323837 412057 := bbase (se 2 (by rfl) ⟨154521, by rfl⟩ : syracuseStep 412057 = 309043) (by norm_num)
theorem B346537 : Blo 323837 346537 := bbase (se 2 (by rfl) ⟨129951, by rfl⟩ : syracuseStep 346537 = 259903) (by norm_num)
theorem B1558997 : Blo 323837 1558997 := bbase (se 7 (by rfl) ⟨18269, by rfl⟩ : syracuseStep 1558997 = 36539) (by norm_num)
theorem B412229 : Blo 323837 412229 := bbase (se 4 (by rfl) ⟨38646, by rfl⟩ : syracuseStep 412229 = 77293) (by norm_num)
theorem B1100357 : Blo 323837 1100357 := bbase (se 4 (by rfl) ⟨103158, by rfl⟩ : syracuseStep 1100357 = 206317) (by norm_num)
theorem B346717 : Blo 323837 346717 := bbase (se 3 (by rfl) ⟨65009, by rfl⟩ : syracuseStep 346717 = 130019) (by norm_num)
theorem B412285 : Blo 323837 412285 := bbase (se 3 (by rfl) ⟨77303, by rfl⟩ : syracuseStep 412285 = 154607) (by norm_num)
theorem B412381 : Blo 323837 412381 := bbase (se 3 (by rfl) ⟨77321, by rfl⟩ : syracuseStep 412381 = 154643) (by norm_num)
theorem B412553 : Blo 323837 412553 := bbase (se 2 (by rfl) ⟨154707, by rfl⟩ : syracuseStep 412553 = 309415) (by norm_num)
theorem B2837429 : Blo 323837 2837429 := bbase (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) (by norm_num)
theorem B412609 : Blo 323837 412609 := bbase (se 2 (by rfl) ⟨154728, by rfl⟩ : syracuseStep 412609 = 309457) (by norm_num)
theorem B740333 : Blo 323837 740333 := bbase (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) (by norm_num)
theorem B1100789 : Blo 323837 1100789 := bbase (se 5 (by rfl) ⟨51599, by rfl⟩ : syracuseStep 1100789 = 103199) (by norm_num)
theorem B1395701 : Blo 323837 1395701 := bbase (se 5 (by rfl) ⟨65423, by rfl⟩ : syracuseStep 1395701 = 130847) (by norm_num)
theorem B1854485 : Blo 323837 1854485 := bbase (se 6 (by rfl) ⟨43464, by rfl⟩ : syracuseStep 1854485 = 86929) (by norm_num)
theorem B347161 : Blo 323837 347161 := bbase (se 2 (by rfl) ⟨130185, by rfl⟩ : syracuseStep 347161 = 260371) (by norm_num)
theorem B412705 : Blo 323837 412705 := bbase (se 2 (by rfl) ⟨154764, by rfl⟩ : syracuseStep 412705 = 309529) (by norm_num)
theorem B2477141 : Blo 323837 2477141 := bbase (se 8 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 2477141 = 29029) (by norm_num)
theorem B347285 : Blo 323837 347285 := bbase (se 6 (by rfl) ⟨8139, by rfl⟩ : syracuseStep 347285 = 16279) (by norm_num)
theorem B412877 : Blo 323837 412877 := bbase (se 3 (by rfl) ⟨77414, by rfl⟩ : syracuseStep 412877 = 154829) (by norm_num)
theorem B1658069 : Blo 323837 1658069 := bbase (se 7 (by rfl) ⟨19430, by rfl⟩ : syracuseStep 1658069 = 38861) (by norm_num)
theorem B1232117 : Blo 323837 1232117 := bbase (se 5 (by rfl) ⟨57755, by rfl⟩ : syracuseStep 1232117 = 115511) (by norm_num)
theorem B412933 : Blo 323837 412933 := bbase (se 4 (by rfl) ⟨38712, by rfl⟩ : syracuseStep 412933 = 77425) (by norm_num)
theorem B413029 : Blo 323837 413029 := bbase (se 4 (by rfl) ⟨38721, by rfl⟩ : syracuseStep 413029 = 77443) (by norm_num)
theorem B1494389 : Blo 323837 1494389 := bbase (se 5 (by rfl) ⟨70049, by rfl⟩ : syracuseStep 1494389 = 140099) (by norm_num)
theorem B347537 : Blo 323837 347537 := bbase (se 2 (by rfl) ⟨130326, by rfl⟩ : syracuseStep 347537 = 260653) (by norm_num)
theorem B1101221 : Blo 323837 1101221 := bbase (se 4 (by rfl) ⟨103239, by rfl⟩ : syracuseStep 1101221 = 206479) (by norm_num)
theorem B413201 : Blo 323837 413201 := bbase (se 2 (by rfl) ⟨154950, by rfl⟩ : syracuseStep 413201 = 309901) (by norm_num)
theorem B1232405 : Blo 323837 1232405 := bbase (se 6 (by rfl) ⟨28884, by rfl⟩ : syracuseStep 1232405 = 57769) (by norm_num)
theorem B413257 : Blo 323837 413257 := bbase (se 2 (by rfl) ⟨154971, by rfl⟩ : syracuseStep 413257 = 309943) (by norm_num)
theorem B4705877 : Blo 323837 4705877 := bbase (se 8 (by rfl) ⟨27573, by rfl⟩ : syracuseStep 4705877 = 55147) (by norm_num)
theorem B413353 : Blo 323837 413353 := bbase (se 2 (by rfl) ⟨155007, by rfl⟩ : syracuseStep 413353 = 310015) (by norm_num)
theorem B3690197 : Blo 323837 3690197 := bbase (se 7 (by rfl) ⟨43244, by rfl⟩ : syracuseStep 3690197 = 86489) (by norm_num)
theorem B347981 : Blo 323837 347981 := bbase (se 3 (by rfl) ⟨65246, by rfl⟩ : syracuseStep 347981 = 130493) (by norm_num)
theorem B1101653 : Blo 323837 1101653 := bbase (se 9 (by rfl) ⟨3227, by rfl⟩ : syracuseStep 1101653 = 6455) (by norm_num)
theorem B413525 : Blo 323837 413525 := bbase (se 9 (by rfl) ⟨1211, by rfl⟩ : syracuseStep 413525 = 2423) (by norm_num)
theorem B413581 : Blo 323837 413581 := bbase (se 3 (by rfl) ⟨77546, by rfl⟩ : syracuseStep 413581 = 155093) (by norm_num)
theorem B1167317 : Blo 323837 1167317 := bbase (se 7 (by rfl) ⟨13679, by rfl⟩ : syracuseStep 1167317 = 27359) (by norm_num)
theorem B1396709 : Blo 323837 1396709 := bbase (se 4 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 1396709 = 261883) (by norm_num)
theorem B413677 : Blo 323837 413677 := bbase (se 3 (by rfl) ⟨77564, by rfl⟩ : syracuseStep 413677 = 155129) (by norm_num)
theorem B348229 : Blo 323837 348229 := bbase (se 4 (by rfl) ⟨32646, by rfl⟩ : syracuseStep 348229 = 65293) (by norm_num)
theorem B413849 : Blo 323837 413849 := bbase (se 2 (by rfl) ⟨155193, by rfl⟩ : syracuseStep 413849 = 310387) (by norm_num)
theorem B1855669 : Blo 323837 1855669 := bbase (se 5 (by rfl) ⟨86984, by rfl⟩ : syracuseStep 1855669 = 173969) (by norm_num)
theorem B413905 : Blo 323837 413905 := bbase (se 2 (by rfl) ⟨155214, by rfl⟩ : syracuseStep 413905 = 310429) (by norm_num)
theorem B1102085 : Blo 323837 1102085 := bbase (se 4 (by rfl) ⟨103320, by rfl⟩ : syracuseStep 1102085 = 206641) (by norm_num)
theorem B3232021 : Blo 323837 3232021 := bbase (se 6 (by rfl) ⟨75750, by rfl⟩ : syracuseStep 3232021 = 151501) (by norm_num)
theorem B414001 : Blo 323837 414001 := bbase (se 2 (by rfl) ⟨155250, by rfl⟩ : syracuseStep 414001 = 310501) (by norm_num)
theorem B840061 : Blo 323837 840061 := bbase (se 3 (by rfl) ⟨157511, by rfl⟩ : syracuseStep 840061 = 315023) (by norm_num)
theorem B414173 : Blo 323837 414173 := bbase (se 3 (by rfl) ⟨77657, by rfl⟩ : syracuseStep 414173 = 155315) (by norm_num)
theorem B1659365 : Blo 323837 1659365 := bbase (se 4 (by rfl) ⟨155565, by rfl⟩ : syracuseStep 1659365 = 311131) (by norm_num)
theorem B348673 : Blo 323837 348673 := bbase (se 2 (by rfl) ⟨130752, by rfl⟩ : syracuseStep 348673 = 261505) (by norm_num)
theorem B414229 : Blo 323837 414229 := bbase (se 6 (by rfl) ⟨9708, by rfl⟩ : syracuseStep 414229 = 19417) (by norm_num)
theorem B348733 : Blo 323837 348733 := bbase (se 3 (by rfl) ⟨65387, by rfl⟩ : syracuseStep 348733 = 130775) (by norm_num)
theorem B414325 : Blo 323837 414325 := bbase (se 5 (by rfl) ⟨19421, by rfl⟩ : syracuseStep 414325 = 38843) (by norm_num)
theorem B1233589 : Blo 323837 1233589 := bbase (se 5 (by rfl) ⟨57824, by rfl⟩ : syracuseStep 1233589 = 115649) (by norm_num)
theorem B1102517 : Blo 323837 1102517 := bbase (se 5 (by rfl) ⟨51680, by rfl⟩ : syracuseStep 1102517 = 103361) (by norm_num)
theorem B742085 : Blo 323837 742085 := bbase (se 4 (by rfl) ⟨69570, by rfl⟩ : syracuseStep 742085 = 139141) (by norm_num)
theorem B414497 : Blo 323837 414497 := bbase (se 2 (by rfl) ⟨155436, by rfl⟩ : syracuseStep 414497 = 310873) (by norm_num)
theorem B1168181 : Blo 323837 1168181 := bbase (se 5 (by rfl) ⟨54758, by rfl⟩ : syracuseStep 1168181 = 109517) (by norm_num)
theorem B414553 : Blo 323837 414553 := bbase (se 2 (by rfl) ⟨155457, by rfl⟩ : syracuseStep 414553 = 310915) (by norm_num)
theorem B349049 : Blo 323837 349049 := bbase (se 2 (by rfl) ⟨130893, by rfl⟩ : syracuseStep 349049 = 261787) (by norm_num)
theorem B4445077 : Blo 323837 4445077 := bbase (se 6 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 4445077 = 208363) (by norm_num)
theorem B414649 : Blo 323837 414649 := bbase (se 2 (by rfl) ⟨155493, by rfl⟩ : syracuseStep 414649 = 310987) (by norm_num)
theorem B1233893 : Blo 323837 1233893 := bbase (se 4 (by rfl) ⟨115677, by rfl⟩ : syracuseStep 1233893 = 231355) (by norm_num)
theorem B1168469 : Blo 323837 1168469 := bbase (se 8 (by rfl) ⟨6846, by rfl⟩ : syracuseStep 1168469 = 13693) (by norm_num)
theorem B1102949 : Blo 323837 1102949 := bbase (se 4 (by rfl) ⟨103401, by rfl⟩ : syracuseStep 1102949 = 206803) (by norm_num)
theorem B414821 : Blo 323837 414821 := bbase (se 4 (by rfl) ⟨38889, by rfl⟩ : syracuseStep 414821 = 77779) (by norm_num)
theorem B414877 : Blo 323837 414877 := bbase (se 3 (by rfl) ⟨77789, by rfl⟩ : syracuseStep 414877 = 155579) (by norm_num)
theorem B349493 : Blo 323837 349493 := bbase (se 5 (by rfl) ⟨16382, by rfl⟩ : syracuseStep 349493 = 32765) (by norm_num)
theorem B349553 : Blo 323837 349553 := bbase (se 2 (by rfl) ⟨131082, by rfl⟩ : syracuseStep 349553 = 262165) (by norm_num)
theorem B349681 : Blo 323837 349681 := bbase (se 2 (by rfl) ⟨131130, by rfl⟩ : syracuseStep 349681 = 262261) (by norm_num)
theorem B1168901 : Blo 323837 1168901 := bbase (se 4 (by rfl) ⟨109584, by rfl⟩ : syracuseStep 1168901 = 219169) (by norm_num)
theorem B1103381 : Blo 323837 1103381 := bbase (se 6 (by rfl) ⟨25860, by rfl⟩ : syracuseStep 1103381 = 51721) (by norm_num)
theorem B546493 : Blo 323837 546493 := bbase (se 3 (by rfl) ⟨102467, by rfl⟩ : syracuseStep 546493 = 204935) (by norm_num)
theorem B1398485 : Blo 323837 1398485 := bbase (se 7 (by rfl) ⟨16388, by rfl⟩ : syracuseStep 1398485 = 32777) (by norm_num)
theorem B546581 : Blo 323837 546581 := bbase (se 6 (by rfl) ⟨12810, by rfl⟩ : syracuseStep 546581 = 25621) (by norm_num)
theorem B2119445 : Blo 323837 2119445 := bbase (se 6 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 2119445 = 99349) (by norm_num)
theorem B546709 : Blo 323837 546709 := bbase (se 6 (by rfl) ⟨12813, by rfl⟩ : syracuseStep 546709 = 25627) (by norm_num)
theorem B1103813 : Blo 323837 1103813 := bbase (se 4 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 1103813 = 206965) (by norm_num)
theorem B546797 : Blo 323837 546797 := bbase (se 3 (by rfl) ⟨102524, by rfl⟩ : syracuseStep 546797 = 205049) (by norm_num)
theorem B546925 : Blo 323837 546925 := bbase (se 3 (by rfl) ⟨102548, by rfl⟩ : syracuseStep 546925 = 205097) (by norm_num)
theorem B1857653 : Blo 323837 1857653 := bbase (se 5 (by rfl) ⟨87077, by rfl⟩ : syracuseStep 1857653 = 174155) (by norm_num)
theorem B547013 : Blo 323837 547013 := bbase (se 4 (by rfl) ⟨51282, by rfl⟩ : syracuseStep 547013 = 102565) (by norm_num)
theorem B415945 : Blo 323837 415945 := bbase (se 2 (by rfl) ⟨155979, by rfl⟩ : syracuseStep 415945 = 311959) (by norm_num)
theorem B547141 : Blo 323837 547141 := bbase (se 4 (by rfl) ⟨51294, by rfl⟩ : syracuseStep 547141 = 102589) (by norm_num)
theorem B1431893 : Blo 323837 1431893 := bbase (se 10 (by rfl) ⟨2097, by rfl⟩ : syracuseStep 1431893 = 4195) (by norm_num)
theorem B1104245 : Blo 323837 1104245 := bbase (se 5 (by rfl) ⟨51761, by rfl⟩ : syracuseStep 1104245 = 103523) (by norm_num)
theorem B547229 : Blo 323837 547229 := bbase (se 3 (by rfl) ⟨102605, by rfl⟩ : syracuseStep 547229 = 205211) (by norm_num)
theorem B547357 : Blo 323837 547357 := bbase (se 3 (by rfl) ⟨102629, by rfl⟩ : syracuseStep 547357 = 205259) (by norm_num)
theorem B2087477 : Blo 323837 2087477 := bbase (se 5 (by rfl) ⟨97850, by rfl⟩ : syracuseStep 2087477 = 195701) (by norm_num)
theorem B547445 : Blo 323837 547445 := bbase (se 5 (by rfl) ⟨25661, by rfl⟩ : syracuseStep 547445 = 51323) (by norm_num)
theorem B547573 : Blo 323837 547573 := bbase (se 5 (by rfl) ⟨25667, by rfl⟩ : syracuseStep 547573 = 51335) (by norm_num)
theorem B1104677 : Blo 323837 1104677 := bbase (se 4 (by rfl) ⟨103563, by rfl⟩ : syracuseStep 1104677 = 207127) (by norm_num)
theorem B547661 : Blo 323837 547661 := bbase (se 3 (by rfl) ⟨102686, by rfl⟩ : syracuseStep 547661 = 205373) (by norm_num)
theorem B547789 : Blo 323837 547789 := bbase (se 3 (by rfl) ⟨102710, by rfl⟩ : syracuseStep 547789 = 205421) (by norm_num)
theorem B547877 : Blo 323837 547877 := bbase (se 4 (by rfl) ⟨51363, by rfl⟩ : syracuseStep 547877 = 102727) (by norm_num)
theorem B1236005 : Blo 323837 1236005 := bbase (se 4 (by rfl) ⟨115875, by rfl⟩ : syracuseStep 1236005 = 231751) (by norm_num)
theorem B548005 : Blo 323837 548005 := bbase (se 4 (by rfl) ⟨51375, by rfl⟩ : syracuseStep 548005 = 102751) (by norm_num)
theorem B1105109 : Blo 323837 1105109 := bbase (se 7 (by rfl) ⟨12950, by rfl⟩ : syracuseStep 1105109 = 25901) (by norm_num)
theorem B548093 : Blo 323837 548093 := bbase (se 3 (by rfl) ⟨102767, by rfl⟩ : syracuseStep 548093 = 205535) (by norm_num)
theorem B1236293 : Blo 323837 1236293 := bbase (se 4 (by rfl) ⟨115902, by rfl⟩ : syracuseStep 1236293 = 231805) (by norm_num)
theorem B13557077 : Blo 323837 13557077 := bbase (se 11 (by rfl) ⟨9929, by rfl⟩ : syracuseStep 13557077 = 19859) (by norm_num)
theorem B548221 : Blo 323837 548221 := bbase (se 3 (by rfl) ⟨102791, by rfl⟩ : syracuseStep 548221 = 205583) (by norm_num)
theorem B548309 : Blo 323837 548309 := bbase (se 7 (by rfl) ⟨6425, by rfl⟩ : syracuseStep 548309 = 12851) (by norm_num)
theorem B548437 : Blo 323837 548437 := bbase (se 8 (by rfl) ⟨3213, by rfl⟩ : syracuseStep 548437 = 6427) (by norm_num)
theorem B1105541 : Blo 323837 1105541 := bbase (se 4 (by rfl) ⟨103644, by rfl⟩ : syracuseStep 1105541 = 207289) (by norm_num)
theorem B1171093 : Blo 323837 1171093 := bbase (se 6 (by rfl) ⟨27447, by rfl⟩ : syracuseStep 1171093 = 54895) (by norm_num)
theorem B548525 : Blo 323837 548525 := bbase (se 3 (by rfl) ⟨102848, by rfl⟩ : syracuseStep 548525 = 205697) (by norm_num)
theorem B548653 : Blo 323837 548653 := bbase (se 3 (by rfl) ⟨102872, by rfl⟩ : syracuseStep 548653 = 205745) (by norm_num)
theorem B548741 : Blo 323837 548741 := bbase (se 4 (by rfl) ⟨51444, by rfl⟩ : syracuseStep 548741 = 102889) (by norm_num)
theorem B548869 : Blo 323837 548869 := bbase (se 4 (by rfl) ⟨51456, by rfl⟩ : syracuseStep 548869 = 102913) (by norm_num)
theorem B1105973 : Blo 323837 1105973 := bbase (se 5 (by rfl) ⟨51842, by rfl⟩ : syracuseStep 1105973 = 103685) (by norm_num)
theorem B548957 : Blo 323837 548957 := bbase (se 3 (by rfl) ⟨102929, by rfl⟩ : syracuseStep 548957 = 205859) (by norm_num)
theorem B549085 : Blo 323837 549085 := bbase (se 3 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 549085 = 205907) (by norm_num)
theorem B1859861 : Blo 323837 1859861 := bbase (se 6 (by rfl) ⟨43590, by rfl⟩ : syracuseStep 1859861 = 87181) (by norm_num)
theorem B549173 : Blo 323837 549173 := bbase (se 5 (by rfl) ⟨25742, by rfl⟩ : syracuseStep 549173 = 51485) (by norm_num)
theorem B418117 : Blo 323837 418117 := bbase (se 4 (by rfl) ⟨39198, by rfl⟩ : syracuseStep 418117 = 78397) (by norm_num)
theorem B549301 : Blo 323837 549301 := bbase (se 5 (by rfl) ⟨25748, by rfl⟩ : syracuseStep 549301 = 51497) (by norm_num)
theorem B1237477 : Blo 323837 1237477 := bbase (se 4 (by rfl) ⟨116013, by rfl⟩ : syracuseStep 1237477 = 232027) (by norm_num)
theorem B1106405 : Blo 323837 1106405 := bbase (se 4 (by rfl) ⟨103725, by rfl⟩ : syracuseStep 1106405 = 207451) (by norm_num)
theorem B549389 : Blo 323837 549389 := bbase (se 3 (by rfl) ⟨103010, by rfl⟩ : syracuseStep 549389 = 206021) (by norm_num)
theorem B614965 : Blo 323837 614965 := bbase (se 5 (by rfl) ⟨28826, by rfl⟩ : syracuseStep 614965 = 57653) (by norm_num)
theorem B451165 : Blo 323837 451165 := bbase (se 3 (by rfl) ⟨84593, by rfl⟩ : syracuseStep 451165 = 169187) (by norm_num)
theorem B746101 : Blo 323837 746101 := bbase (se 5 (by rfl) ⟨34973, by rfl⟩ : syracuseStep 746101 = 69947) (by norm_num)
theorem B811661 : Blo 323837 811661 := bbase (se 3 (by rfl) ⟨152186, by rfl⟩ : syracuseStep 811661 = 304373) (by norm_num)
theorem B549517 : Blo 323837 549517 := bbase (se 3 (by rfl) ⟨103034, by rfl⟩ : syracuseStep 549517 = 206069) (by norm_num)
theorem B615109 : Blo 323837 615109 := bbase (se 4 (by rfl) ⟨57666, by rfl⟩ : syracuseStep 615109 = 115333) (by norm_num)
theorem B549605 : Blo 323837 549605 := bbase (se 4 (by rfl) ⟨51525, by rfl⟩ : syracuseStep 549605 = 103051) (by norm_num)
theorem B1237781 : Blo 323837 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B615269 : Blo 323837 615269 := bbase (se 4 (by rfl) ⟨57681, by rfl⟩ : syracuseStep 615269 = 115363) (by norm_num)
theorem B549733 : Blo 323837 549733 := bbase (se 4 (by rfl) ⟨51537, by rfl⟩ : syracuseStep 549733 = 103075) (by norm_num)
theorem B418717 : Blo 323837 418717 := bbase (se 3 (by rfl) ⟨78509, by rfl⟩ : syracuseStep 418717 = 157019) (by norm_num)
theorem B549821 : Blo 323837 549821 := bbase (se 3 (by rfl) ⟨103091, by rfl⟩ : syracuseStep 549821 = 206183) (by norm_num)
theorem B615413 : Blo 323837 615413 := bbase (se 5 (by rfl) ⟨28847, by rfl⟩ : syracuseStep 615413 = 57695) (by norm_num)
theorem B549949 : Blo 323837 549949 := bbase (se 3 (by rfl) ⟨103115, by rfl⟩ : syracuseStep 549949 = 206231) (by norm_num)
theorem B550037 : Blo 323837 550037 := bbase (se 6 (by rfl) ⟨12891, by rfl⟩ : syracuseStep 550037 = 25783) (by norm_num)
theorem B615701 : Blo 323837 615701 := bbase (se 6 (by rfl) ⟨14430, by rfl⟩ : syracuseStep 615701 = 28861) (by norm_num)
theorem B550165 : Blo 323837 550165 := bbase (se 6 (by rfl) ⟨12894, by rfl⟩ : syracuseStep 550165 = 25789) (by norm_num)
theorem B2647349 : Blo 323837 2647349 := bbase (se 5 (by rfl) ⟨124094, by rfl⟩ : syracuseStep 2647349 = 248189) (by norm_num)
theorem B550253 : Blo 323837 550253 := bbase (se 3 (by rfl) ⟨103172, by rfl⟩ : syracuseStep 550253 = 206345) (by norm_num)
theorem B615853 : Blo 323837 615853 := bbase (se 3 (by rfl) ⟨115472, by rfl⟩ : syracuseStep 615853 = 230945) (by norm_num)
theorem B1041893 : Blo 323837 1041893 := bbase (se 4 (by rfl) ⟨97677, by rfl⟩ : syracuseStep 1041893 = 195355) (by norm_num)
theorem B550381 : Blo 323837 550381 := bbase (se 3 (by rfl) ⟨103196, by rfl⟩ : syracuseStep 550381 = 206393) (by norm_num)
theorem B550469 : Blo 323837 550469 := bbase (se 4 (by rfl) ⟨51606, by rfl⟩ : syracuseStep 550469 = 103213) (by norm_num)
theorem B550597 : Blo 323837 550597 := bbase (se 4 (by rfl) ⟨51618, by rfl⟩ : syracuseStep 550597 = 103237) (by norm_num)
theorem B616157 : Blo 323837 616157 := bbase (se 3 (by rfl) ⟨115529, by rfl⟩ : syracuseStep 616157 = 231059) (by norm_num)
theorem B550685 : Blo 323837 550685 := bbase (se 3 (by rfl) ⟨103253, by rfl⟩ : syracuseStep 550685 = 206507) (by norm_num)
theorem B550813 : Blo 323837 550813 := bbase (se 3 (by rfl) ⟨103277, by rfl⟩ : syracuseStep 550813 = 206555) (by norm_num)
theorem B550901 : Blo 323837 550901 := bbase (se 5 (by rfl) ⟨25823, by rfl⟩ : syracuseStep 550901 = 51647) (by norm_num)
theorem B845909 : Blo 323837 845909 := bbase (se 8 (by rfl) ⟨4956, by rfl⟩ : syracuseStep 845909 = 9913) (by norm_num)
theorem B551029 : Blo 323837 551029 := bbase (se 5 (by rfl) ⟨25829, by rfl⟩ : syracuseStep 551029 = 51659) (by norm_num)
theorem B551117 : Blo 323837 551117 := bbase (se 3 (by rfl) ⟨103334, by rfl⟩ : syracuseStep 551117 = 206669) (by norm_num)
theorem B551245 : Blo 323837 551245 := bbase (se 3 (by rfl) ⟨103358, by rfl⟩ : syracuseStep 551245 = 206717) (by norm_num)
theorem B1042789 : Blo 323837 1042789 := bbase (se 4 (by rfl) ⟨97761, by rfl⟩ : syracuseStep 1042789 = 195523) (by norm_num)
theorem B485765 : Blo 323837 485765 := bbase (se 4 (by rfl) ⟨45540, by rfl⟩ : syracuseStep 485765 = 91081) (by norm_num)
theorem B2779541 : Blo 323837 2779541 := bbase (se 6 (by rfl) ⟨65145, by rfl⟩ : syracuseStep 2779541 = 130291) (by norm_num)
theorem B485789 : Blo 323837 485789 := bbase (se 3 (by rfl) ⟨91085, by rfl⟩ : syracuseStep 485789 = 182171) (by norm_num)
theorem B551333 : Blo 323837 551333 := bbase (se 4 (by rfl) ⟨51687, by rfl⟩ : syracuseStep 551333 = 103375) (by norm_num)
theorem B485813 : Blo 323837 485813 := bbase (se 5 (by rfl) ⟨22772, by rfl⟩ : syracuseStep 485813 = 45545) (by norm_num)
theorem B485837 : Blo 323837 485837 := bbase (se 3 (by rfl) ⟨91094, by rfl⟩ : syracuseStep 485837 = 182189) (by norm_num)
theorem B616909 : Blo 323837 616909 := bbase (se 3 (by rfl) ⟨115670, by rfl⟩ : syracuseStep 616909 = 231341) (by norm_num)
theorem B485861 : Blo 323837 485861 := bbase (se 4 (by rfl) ⟨45549, by rfl⟩ : syracuseStep 485861 = 91099) (by norm_num)
theorem B1272293 : Blo 323837 1272293 := bbase (se 4 (by rfl) ⟨119277, by rfl⟩ : syracuseStep 1272293 = 238555) (by norm_num)
theorem B485885 : Blo 323837 485885 := bbase (se 3 (by rfl) ⟨91103, by rfl⟩ : syracuseStep 485885 = 182207) (by norm_num)
theorem B485909 : Blo 323837 485909 := bbase (se 6 (by rfl) ⟨11388, by rfl⟩ : syracuseStep 485909 = 22777) (by norm_num)
theorem B551461 : Blo 323837 551461 := bbase (se 4 (by rfl) ⟨51699, by rfl⟩ : syracuseStep 551461 = 103399) (by norm_num)
theorem B485933 : Blo 323837 485933 := bbase (se 3 (by rfl) ⟨91112, by rfl⟩ : syracuseStep 485933 = 182225) (by norm_num)
theorem B485957 : Blo 323837 485957 := bbase (se 4 (by rfl) ⟨45558, by rfl⟩ : syracuseStep 485957 = 91117) (by norm_num)
theorem B485981 : Blo 323837 485981 := bbase (se 3 (by rfl) ⟨91121, by rfl⟩ : syracuseStep 485981 = 182243) (by norm_num)
theorem B617053 : Blo 323837 617053 := bbase (se 3 (by rfl) ⟨115697, by rfl⟩ : syracuseStep 617053 = 231395) (by norm_num)
theorem B486005 : Blo 323837 486005 := bbase (se 5 (by rfl) ⟨22781, by rfl⟩ : syracuseStep 486005 = 45563) (by norm_num)
theorem B551549 : Blo 323837 551549 := bbase (se 3 (by rfl) ⟨103415, by rfl⟩ : syracuseStep 551549 = 206831) (by norm_num)
theorem B486029 : Blo 323837 486029 := bbase (se 3 (by rfl) ⟨91130, by rfl⟩ : syracuseStep 486029 = 182261) (by norm_num)
theorem B486053 : Blo 323837 486053 := bbase (se 4 (by rfl) ⟨45567, by rfl⟩ : syracuseStep 486053 = 91135) (by norm_num)
theorem B2484917 : Blo 323837 2484917 := bbase (se 5 (by rfl) ⟨116480, by rfl⟩ : syracuseStep 2484917 = 232961) (by norm_num)
theorem B486077 : Blo 323837 486077 := bbase (se 3 (by rfl) ⟨91139, by rfl⟩ : syracuseStep 486077 = 182279) (by norm_num)
theorem B486101 : Blo 323837 486101 := bbase (se 7 (by rfl) ⟨5696, by rfl⟩ : syracuseStep 486101 = 11393) (by norm_num)
theorem B486125 : Blo 323837 486125 := bbase (se 3 (by rfl) ⟨91148, by rfl⟩ : syracuseStep 486125 = 182297) (by norm_num)
theorem B1043189 : Blo 323837 1043189 := bbase (se 5 (by rfl) ⟨48899, by rfl⟩ : syracuseStep 1043189 = 97799) (by norm_num)
theorem B617213 : Blo 323837 617213 := bbase (se 3 (by rfl) ⟨115727, by rfl⟩ : syracuseStep 617213 = 231455) (by norm_num)
theorem B551677 : Blo 323837 551677 := bbase (se 3 (by rfl) ⟨103439, by rfl⟩ : syracuseStep 551677 = 206879) (by norm_num)
theorem B486149 : Blo 323837 486149 := bbase (se 4 (by rfl) ⟨45576, by rfl⟩ : syracuseStep 486149 = 91153) (by norm_num)
theorem B486173 : Blo 323837 486173 := bbase (se 3 (by rfl) ⟨91157, by rfl⟩ : syracuseStep 486173 = 182315) (by norm_num)
theorem B781093 : Blo 323837 781093 := bbase (se 4 (by rfl) ⟨73227, by rfl⟩ : syracuseStep 781093 = 146455) (by norm_num)
theorem B486197 : Blo 323837 486197 := bbase (se 5 (by rfl) ⟨22790, by rfl⟩ : syracuseStep 486197 = 45581) (by norm_num)
theorem B486221 : Blo 323837 486221 := bbase (se 3 (by rfl) ⟨91166, by rfl⟩ : syracuseStep 486221 = 182333) (by norm_num)
theorem B846677 : Blo 323837 846677 := bbase (se 9 (by rfl) ⟨2480, by rfl⟩ : syracuseStep 846677 = 4961) (by norm_num)
theorem B1239893 : Blo 323837 1239893 := bbase (se 9 (by rfl) ⟨3632, by rfl⟩ : syracuseStep 1239893 = 7265) (by norm_num)
theorem B551765 : Blo 323837 551765 := bbase (se 9 (by rfl) ⟨1616, by rfl⟩ : syracuseStep 551765 = 3233) (by norm_num)
theorem B486245 : Blo 323837 486245 := bbase (se 4 (by rfl) ⟨45585, by rfl⟩ : syracuseStep 486245 = 91171) (by norm_num)
theorem B486269 : Blo 323837 486269 := bbase (se 3 (by rfl) ⟨91175, by rfl⟩ : syracuseStep 486269 = 182351) (by norm_num)
theorem B617357 : Blo 323837 617357 := bbase (se 3 (by rfl) ⟨115754, by rfl⟩ : syracuseStep 617357 = 231509) (by norm_num)
theorem B486293 : Blo 323837 486293 := bbase (se 6 (by rfl) ⟨11397, by rfl⟩ : syracuseStep 486293 = 22795) (by norm_num)
theorem B486317 : Blo 323837 486317 := bbase (se 3 (by rfl) ⟨91184, by rfl⟩ : syracuseStep 486317 = 182369) (by norm_num)
theorem B486341 : Blo 323837 486341 := bbase (se 4 (by rfl) ⟨45594, by rfl⟩ : syracuseStep 486341 = 91189) (by norm_num)
theorem B551893 : Blo 323837 551893 := bbase (se 7 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 551893 = 12935) (by norm_num)
theorem B486365 : Blo 323837 486365 := bbase (se 3 (by rfl) ⟨91193, by rfl⟩ : syracuseStep 486365 = 182387) (by norm_num)
theorem B486389 : Blo 323837 486389 := bbase (se 5 (by rfl) ⟨22799, by rfl⟩ : syracuseStep 486389 = 45599) (by norm_num)
theorem B486413 : Blo 323837 486413 := bbase (se 3 (by rfl) ⟨91202, by rfl⟩ : syracuseStep 486413 = 182405) (by norm_num)
theorem B486437 : Blo 323837 486437 := bbase (se 4 (by rfl) ⟨45603, by rfl⟩ : syracuseStep 486437 = 91207) (by norm_num)
theorem B551981 : Blo 323837 551981 := bbase (se 3 (by rfl) ⟨103496, by rfl⟩ : syracuseStep 551981 = 206993) (by norm_num)
theorem B486461 : Blo 323837 486461 := bbase (se 3 (by rfl) ⟨91211, by rfl⟩ : syracuseStep 486461 = 182423) (by norm_num)
theorem B486485 : Blo 323837 486485 := bbase (se 8 (by rfl) ⟨2850, by rfl⟩ : syracuseStep 486485 = 5701) (by norm_num)
theorem B486509 : Blo 323837 486509 := bbase (se 3 (by rfl) ⟨91220, by rfl⟩ : syracuseStep 486509 = 182441) (by norm_num)
theorem B1240181 : Blo 323837 1240181 := bbase (se 5 (by rfl) ⟨58133, by rfl⟩ : syracuseStep 1240181 = 116267) (by norm_num)
theorem B486533 : Blo 323837 486533 := bbase (se 4 (by rfl) ⟨45612, by rfl⟩ : syracuseStep 486533 = 91225) (by norm_num)
theorem B486557 : Blo 323837 486557 := bbase (se 3 (by rfl) ⟨91229, by rfl⟩ : syracuseStep 486557 = 182459) (by norm_num)
theorem B617645 : Blo 323837 617645 := bbase (se 3 (by rfl) ⟨115808, by rfl⟩ : syracuseStep 617645 = 231617) (by norm_num)
theorem B552109 : Blo 323837 552109 := bbase (se 3 (by rfl) ⟨103520, by rfl⟩ : syracuseStep 552109 = 207041) (by norm_num)
theorem B486581 : Blo 323837 486581 := bbase (se 5 (by rfl) ⟨22808, by rfl⟩ : syracuseStep 486581 = 45617) (by norm_num)
theorem B486605 : Blo 323837 486605 := bbase (se 3 (by rfl) ⟨91238, by rfl⟩ : syracuseStep 486605 = 182477) (by norm_num)
theorem B486629 : Blo 323837 486629 := bbase (se 4 (by rfl) ⟨45621, by rfl⟩ : syracuseStep 486629 = 91243) (by norm_num)
theorem B486653 : Blo 323837 486653 := bbase (se 3 (by rfl) ⟨91247, by rfl⟩ : syracuseStep 486653 = 182495) (by norm_num)
theorem B552197 : Blo 323837 552197 := bbase (se 4 (by rfl) ⟨51768, by rfl⟩ : syracuseStep 552197 = 103537) (by norm_num)
theorem B945413 : Blo 323837 945413 := bbase (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) (by norm_num)
theorem B486677 : Blo 323837 486677 := bbase (se 6 (by rfl) ⟨11406, by rfl⟩ : syracuseStep 486677 = 22813) (by norm_num)
theorem B1109285 : Blo 323837 1109285 := bbase (se 4 (by rfl) ⟨103995, by rfl⟩ : syracuseStep 1109285 = 207991) (by norm_num)
theorem B486701 : Blo 323837 486701 := bbase (se 3 (by rfl) ⟨91256, by rfl⟩ : syracuseStep 486701 = 182513) (by norm_num)
theorem B486725 : Blo 323837 486725 := bbase (se 4 (by rfl) ⟨45630, by rfl⟩ : syracuseStep 486725 = 91261) (by norm_num)
theorem B617797 : Blo 323837 617797 := bbase (se 4 (by rfl) ⟨57918, by rfl⟩ : syracuseStep 617797 = 115837) (by norm_num)
theorem B1568069 : Blo 323837 1568069 := bbase (se 4 (by rfl) ⟨147006, by rfl⟩ : syracuseStep 1568069 = 294013) (by norm_num)
theorem B4156757 : Blo 323837 4156757 := bbase (se 11 (by rfl) ⟨3044, by rfl⟩ : syracuseStep 4156757 = 6089) (by norm_num)
theorem B486749 : Blo 323837 486749 := bbase (se 3 (by rfl) ⟨91265, by rfl⟩ : syracuseStep 486749 = 182531) (by norm_num)
theorem B486773 : Blo 323837 486773 := bbase (se 5 (by rfl) ⟨22817, by rfl⟩ : syracuseStep 486773 = 45635) (by norm_num)
theorem B552325 : Blo 323837 552325 := bbase (se 4 (by rfl) ⟨51780, by rfl⟩ : syracuseStep 552325 = 103561) (by norm_num)
theorem B486797 : Blo 323837 486797 := bbase (se 3 (by rfl) ⟨91274, by rfl⟩ : syracuseStep 486797 = 182549) (by norm_num)
theorem B486821 : Blo 323837 486821 := bbase (se 4 (by rfl) ⟨45639, by rfl⟩ : syracuseStep 486821 = 91279) (by norm_num)
theorem B486845 : Blo 323837 486845 := bbase (se 3 (by rfl) ⟨91283, by rfl⟩ : syracuseStep 486845 = 182567) (by norm_num)
theorem B585157 : Blo 323837 585157 := bbase (se 4 (by rfl) ⟨54858, by rfl⟩ : syracuseStep 585157 = 109717) (by norm_num)
theorem B486869 : Blo 323837 486869 := bbase (se 7 (by rfl) ⟨5705, by rfl⟩ : syracuseStep 486869 = 11411) (by norm_num)
theorem B552413 : Blo 323837 552413 := bbase (se 3 (by rfl) ⟨103577, by rfl⟩ : syracuseStep 552413 = 207155) (by norm_num)
theorem B486893 : Blo 323837 486893 := bbase (se 3 (by rfl) ⟨91292, by rfl⟩ : syracuseStep 486893 = 182585) (by norm_num)
theorem B486917 : Blo 323837 486917 := bbase (se 4 (by rfl) ⟨45648, by rfl⟩ : syracuseStep 486917 = 91297) (by norm_num)
theorem B1568261 : Blo 323837 1568261 := bbase (se 4 (by rfl) ⟨147024, by rfl⟩ : syracuseStep 1568261 = 294049) (by norm_num)
theorem B486941 : Blo 323837 486941 := bbase (se 3 (by rfl) ⟨91301, by rfl⟩ : syracuseStep 486941 = 182603) (by norm_num)
theorem B486965 : Blo 323837 486965 := bbase (se 5 (by rfl) ⟨22826, by rfl⟩ : syracuseStep 486965 = 45653) (by norm_num)
theorem B486989 : Blo 323837 486989 := bbase (se 3 (by rfl) ⟨91310, by rfl⟩ : syracuseStep 486989 = 182621) (by norm_num)
theorem B585301 : Blo 323837 585301 := bbase (se 8 (by rfl) ⟨3429, by rfl⟩ : syracuseStep 585301 = 6859) (by norm_num)
theorem B552541 : Blo 323837 552541 := bbase (se 3 (by rfl) ⟨103601, by rfl⟩ : syracuseStep 552541 = 207203) (by norm_num)
theorem B487013 : Blo 323837 487013 := bbase (se 4 (by rfl) ⟨45657, by rfl⟩ : syracuseStep 487013 = 91315) (by norm_num)
theorem B618101 : Blo 323837 618101 := bbase (se 5 (by rfl) ⟨28973, by rfl⟩ : syracuseStep 618101 = 57947) (by norm_num)
theorem B487037 : Blo 323837 487037 := bbase (se 3 (by rfl) ⟨91319, by rfl⟩ : syracuseStep 487037 = 182639) (by norm_num)
theorem B487061 : Blo 323837 487061 := bbase (se 6 (by rfl) ⟨11415, by rfl⟩ : syracuseStep 487061 = 22831) (by norm_num)
theorem B487085 : Blo 323837 487085 := bbase (se 3 (by rfl) ⟨91328, by rfl⟩ : syracuseStep 487085 = 182657) (by norm_num)
theorem B552629 : Blo 323837 552629 := bbase (se 5 (by rfl) ⟨25904, by rfl⟩ : syracuseStep 552629 = 51809) (by norm_num)
theorem B487109 : Blo 323837 487109 := bbase (se 4 (by rfl) ⟨45666, by rfl⟩ : syracuseStep 487109 = 91333) (by norm_num)
theorem B487133 : Blo 323837 487133 := bbase (se 3 (by rfl) ⟨91337, by rfl⟩ : syracuseStep 487133 = 182675) (by norm_num)
theorem B487157 : Blo 323837 487157 := bbase (se 5 (by rfl) ⟨22835, by rfl⟩ : syracuseStep 487157 = 45671) (by norm_num)
theorem B487181 : Blo 323837 487181 := bbase (se 3 (by rfl) ⟨91346, by rfl⟩ : syracuseStep 487181 = 182693) (by norm_num)
theorem B487205 : Blo 323837 487205 := bbase (se 4 (by rfl) ⟨45675, by rfl⟩ : syracuseStep 487205 = 91351) (by norm_num)
theorem B552757 : Blo 323837 552757 := bbase (se 5 (by rfl) ⟨25910, by rfl⟩ : syracuseStep 552757 = 51821) (by norm_num)
theorem B487229 : Blo 323837 487229 := bbase (se 3 (by rfl) ⟨91355, by rfl⟩ : syracuseStep 487229 = 182711) (by norm_num)
theorem B487253 : Blo 323837 487253 := bbase (se 9 (by rfl) ⟨1427, by rfl⟩ : syracuseStep 487253 = 2855) (by norm_num)
theorem B2649941 : Blo 323837 2649941 := bbase (se 9 (by rfl) ⟨7763, by rfl⟩ : syracuseStep 2649941 = 15527) (by norm_num)
theorem B520037 : Blo 323837 520037 := bbase (se 4 (by rfl) ⟨48753, by rfl⟩ : syracuseStep 520037 = 97507) (by norm_num)
theorem B487277 : Blo 323837 487277 := bbase (se 3 (by rfl) ⟨91364, by rfl⟩ : syracuseStep 487277 = 182729) (by norm_num)
theorem B487301 : Blo 323837 487301 := bbase (se 4 (by rfl) ⟨45684, by rfl⟩ : syracuseStep 487301 = 91369) (by norm_num)
theorem B1568645 : Blo 323837 1568645 := bbase (se 4 (by rfl) ⟨147060, by rfl⟩ : syracuseStep 1568645 = 294121) (by norm_num)
theorem B552845 : Blo 323837 552845 := bbase (se 3 (by rfl) ⟨103658, by rfl⟩ : syracuseStep 552845 = 207317) (by norm_num)
theorem B487325 : Blo 323837 487325 := bbase (se 3 (by rfl) ⟨91373, by rfl⟩ : syracuseStep 487325 = 182747) (by norm_num)
theorem B1666981 : Blo 323837 1666981 := bbase (se 4 (by rfl) ⟨156279, by rfl⟩ : syracuseStep 1666981 = 312559) (by norm_num)
theorem B487349 : Blo 323837 487349 := bbase (se 5 (by rfl) ⟨22844, by rfl⟩ : syracuseStep 487349 = 45689) (by norm_num)
theorem B487373 : Blo 323837 487373 := bbase (se 3 (by rfl) ⟨91382, by rfl⟩ : syracuseStep 487373 = 182765) (by norm_num)
theorem B389081 : Blo 323837 389081 := bbase (se 2 (by rfl) ⟨145905, by rfl⟩ : syracuseStep 389081 = 291811) (by norm_num)
theorem B487397 : Blo 323837 487397 := bbase (se 4 (by rfl) ⟨45693, by rfl⟩ : syracuseStep 487397 = 91387) (by norm_num)
theorem B487421 : Blo 323837 487421 := bbase (se 3 (by rfl) ⟨91391, by rfl⟩ : syracuseStep 487421 = 182783) (by norm_num)
theorem B552973 : Blo 323837 552973 := bbase (se 3 (by rfl) ⟨103682, by rfl⟩ : syracuseStep 552973 = 207365) (by norm_num)
theorem B487445 : Blo 323837 487445 := bbase (se 6 (by rfl) ⟨11424, by rfl⟩ : syracuseStep 487445 = 22849) (by norm_num)
theorem B520229 : Blo 323837 520229 := bbase (se 4 (by rfl) ⟨48771, by rfl⟩ : syracuseStep 520229 = 97543) (by norm_num)
theorem B487469 : Blo 323837 487469 := bbase (se 3 (by rfl) ⟨91400, by rfl⟩ : syracuseStep 487469 = 182801) (by norm_num)
theorem B487493 : Blo 323837 487493 := bbase (se 4 (by rfl) ⟨45702, by rfl⟩ : syracuseStep 487493 = 91405) (by norm_num)
theorem B2093141 : Blo 323837 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B487517 : Blo 323837 487517 := bbase (se 3 (by rfl) ⟨91409, by rfl⟩ : syracuseStep 487517 = 182819) (by norm_num)
theorem B553061 : Blo 323837 553061 := bbase (se 4 (by rfl) ⟨51849, by rfl⟩ : syracuseStep 553061 = 103699) (by norm_num)
theorem B487541 : Blo 323837 487541 := bbase (se 5 (by rfl) ⟨22853, by rfl⟩ : syracuseStep 487541 = 45707) (by norm_num)
theorem B487565 : Blo 323837 487565 := bbase (se 3 (by rfl) ⟨91418, by rfl⟩ : syracuseStep 487565 = 182837) (by norm_num)
theorem B782477 : Blo 323837 782477 := bbase (se 3 (by rfl) ⟨146714, by rfl⟩ : syracuseStep 782477 = 293429) (by norm_num)
theorem B585877 : Blo 323837 585877 := bbase (se 6 (by rfl) ⟨13731, by rfl⟩ : syracuseStep 585877 = 27463) (by norm_num)
theorem B487589 : Blo 323837 487589 := bbase (se 4 (by rfl) ⟨45711, by rfl⟩ : syracuseStep 487589 = 91423) (by norm_num)
theorem B487613 : Blo 323837 487613 := bbase (se 3 (by rfl) ⟨91427, by rfl⟩ : syracuseStep 487613 = 182855) (by norm_num)
theorem B487637 : Blo 323837 487637 := bbase (se 7 (by rfl) ⟨5714, by rfl⟩ : syracuseStep 487637 = 11429) (by norm_num)
theorem B553189 : Blo 323837 553189 := bbase (se 4 (by rfl) ⟨51861, by rfl⟩ : syracuseStep 553189 = 103723) (by norm_num)
theorem B487661 : Blo 323837 487661 := bbase (se 3 (by rfl) ⟨91436, by rfl⟩ : syracuseStep 487661 = 182873) (by norm_num)
theorem B487685 : Blo 323837 487685 := bbase (se 4 (by rfl) ⟨45720, by rfl⟩ : syracuseStep 487685 = 91441) (by norm_num)
theorem B389389 : Blo 323837 389389 := bbase (se 3 (by rfl) ⟨73010, by rfl⟩ : syracuseStep 389389 = 146021) (by norm_num)
theorem B1241365 : Blo 323837 1241365 := bbase (se 6 (by rfl) ⟨29094, by rfl⟩ : syracuseStep 1241365 = 58189) (by norm_num)
theorem B487709 : Blo 323837 487709 := bbase (se 3 (by rfl) ⟨91445, by rfl⟩ : syracuseStep 487709 = 182891) (by norm_num)
theorem B487733 : Blo 323837 487733 := bbase (se 5 (by rfl) ⟨22862, by rfl⟩ : syracuseStep 487733 = 45725) (by norm_num)
theorem B487757 : Blo 323837 487757 := bbase (se 3 (by rfl) ⟨91454, by rfl⟩ : syracuseStep 487757 = 182909) (by norm_num)
theorem B782669 : Blo 323837 782669 := bbase (se 3 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 782669 = 293501) (by norm_num)
theorem B487781 : Blo 323837 487781 := bbase (se 4 (by rfl) ⟨45729, by rfl⟩ : syracuseStep 487781 = 91459) (by norm_num)
theorem B618853 : Blo 323837 618853 := bbase (se 4 (by rfl) ⟨58017, by rfl⟩ : syracuseStep 618853 = 116035) (by norm_num)
theorem B487805 : Blo 323837 487805 := bbase (se 3 (by rfl) ⟨91463, by rfl⟩ : syracuseStep 487805 = 182927) (by norm_num)
theorem B487829 : Blo 323837 487829 := bbase (se 6 (by rfl) ⟨11433, by rfl⟩ : syracuseStep 487829 = 22867) (by norm_num)
theorem B487853 : Blo 323837 487853 := bbase (se 3 (by rfl) ⟨91472, by rfl⟩ : syracuseStep 487853 = 182945) (by norm_num)
theorem B389557 : Blo 323837 389557 := bbase (se 5 (by rfl) ⟨18260, by rfl⟩ : syracuseStep 389557 = 36521) (by norm_num)
theorem B487877 : Blo 323837 487877 := bbase (se 4 (by rfl) ⟨45738, by rfl⟩ : syracuseStep 487877 = 91477) (by norm_num)
theorem B487901 : Blo 323837 487901 := bbase (se 3 (by rfl) ⟨91481, by rfl⟩ : syracuseStep 487901 = 182963) (by norm_num)
theorem B389605 : Blo 323837 389605 := bbase (se 4 (by rfl) ⟨36525, by rfl⟩ : syracuseStep 389605 = 73051) (by norm_num)
theorem B487925 : Blo 323837 487925 := bbase (se 5 (by rfl) ⟨22871, by rfl⟩ : syracuseStep 487925 = 45743) (by norm_num)
theorem B618997 : Blo 323837 618997 := bbase (se 5 (by rfl) ⟨29015, by rfl⟩ : syracuseStep 618997 = 58031) (by norm_num)
theorem B487949 : Blo 323837 487949 := bbase (se 3 (by rfl) ⟨91490, by rfl⟩ : syracuseStep 487949 = 182981) (by norm_num)
theorem B586253 : Blo 323837 586253 := bbase (se 3 (by rfl) ⟨109922, by rfl⟩ : syracuseStep 586253 = 219845) (by norm_num)
theorem B2355733 : Blo 323837 2355733 := bbase (se 6 (by rfl) ⟨55212, by rfl⟩ : syracuseStep 2355733 = 110425) (by norm_num)
theorem B487973 : Blo 323837 487973 := bbase (se 4 (by rfl) ⟨45747, by rfl⟩ : syracuseStep 487973 = 91495) (by norm_num)
theorem B487997 : Blo 323837 487997 := bbase (se 3 (by rfl) ⟨91499, by rfl⟩ : syracuseStep 487997 = 182999) (by norm_num)
theorem B389701 : Blo 323837 389701 := bbase (se 4 (by rfl) ⟨36534, by rfl⟩ : syracuseStep 389701 = 73069) (by norm_num)
theorem B1241669 : Blo 323837 1241669 := bbase (se 4 (by rfl) ⟨116406, by rfl⟩ : syracuseStep 1241669 = 232813) (by norm_num)
theorem B488021 : Blo 323837 488021 := bbase (se 8 (by rfl) ⟨2859, by rfl⟩ : syracuseStep 488021 = 5719) (by norm_num)
theorem B488045 : Blo 323837 488045 := bbase (se 3 (by rfl) ⟨91508, by rfl⟩ : syracuseStep 488045 = 183017) (by norm_num)
theorem B488069 : Blo 323837 488069 := bbase (se 4 (by rfl) ⟨45756, by rfl⟩ : syracuseStep 488069 = 91513) (by norm_num)
theorem B619157 : Blo 323837 619157 := bbase (se 6 (by rfl) ⟨14511, by rfl⟩ : syracuseStep 619157 = 29023) (by norm_num)
theorem B488093 : Blo 323837 488093 := bbase (se 3 (by rfl) ⟨91517, by rfl⟩ : syracuseStep 488093 = 183035) (by norm_num)
theorem B488117 : Blo 323837 488117 := bbase (se 5 (by rfl) ⟨22880, by rfl⟩ : syracuseStep 488117 = 45761) (by norm_num)
theorem B488141 : Blo 323837 488141 := bbase (se 3 (by rfl) ⟨91526, by rfl⟩ : syracuseStep 488141 = 183053) (by norm_num)
theorem B488165 : Blo 323837 488165 := bbase (se 4 (by rfl) ⟨45765, by rfl⟩ : syracuseStep 488165 = 91531) (by norm_num)
theorem B488189 : Blo 323837 488189 := bbase (se 3 (by rfl) ⟨91535, by rfl⟩ : syracuseStep 488189 = 183071) (by norm_num)
theorem B488213 : Blo 323837 488213 := bbase (se 6 (by rfl) ⟨11442, by rfl⟩ : syracuseStep 488213 = 22885) (by norm_num)
theorem B619301 : Blo 323837 619301 := bbase (se 4 (by rfl) ⟨58059, by rfl⟩ : syracuseStep 619301 = 116119) (by norm_num)
theorem B586541 : Blo 323837 586541 := bbase (se 3 (by rfl) ⟨109976, by rfl⟩ : syracuseStep 586541 = 219953) (by norm_num)
theorem B488237 : Blo 323837 488237 := bbase (se 3 (by rfl) ⟨91544, by rfl⟩ : syracuseStep 488237 = 183089) (by norm_num)
theorem B488261 : Blo 323837 488261 := bbase (se 4 (by rfl) ⟨45774, by rfl⟩ : syracuseStep 488261 = 91549) (by norm_num)
theorem B488285 : Blo 323837 488285 := bbase (se 3 (by rfl) ⟨91553, by rfl⟩ : syracuseStep 488285 = 183107) (by norm_num)
theorem B488309 : Blo 323837 488309 := bbase (se 5 (by rfl) ⟨22889, by rfl⟩ : syracuseStep 488309 = 45779) (by norm_num)
theorem B488333 : Blo 323837 488333 := bbase (se 3 (by rfl) ⟨91562, by rfl⟩ : syracuseStep 488333 = 183125) (by norm_num)
theorem B488357 : Blo 323837 488357 := bbase (se 4 (by rfl) ⟨45783, by rfl⟩ : syracuseStep 488357 = 91567) (by norm_num)
theorem B586685 : Blo 323837 586685 := bbase (se 3 (by rfl) ⟨110003, by rfl⟩ : syracuseStep 586685 = 220007) (by norm_num)
theorem B488381 : Blo 323837 488381 := bbase (se 3 (by rfl) ⟨91571, by rfl⟩ : syracuseStep 488381 = 183143) (by norm_num)
theorem B488405 : Blo 323837 488405 := bbase (se 7 (by rfl) ⟨5723, by rfl⟩ : syracuseStep 488405 = 11447) (by norm_num)
theorem B488429 : Blo 323837 488429 := bbase (se 3 (by rfl) ⟨91580, by rfl⟩ : syracuseStep 488429 = 183161) (by norm_num)
theorem B488453 : Blo 323837 488453 := bbase (se 4 (by rfl) ⟨45792, by rfl⟩ : syracuseStep 488453 = 91585) (by norm_num)
theorem B488477 : Blo 323837 488477 := bbase (se 3 (by rfl) ⟨91589, by rfl⟩ : syracuseStep 488477 = 183179) (by norm_num)
theorem B488501 : Blo 323837 488501 := bbase (se 5 (by rfl) ⟨22898, by rfl⟩ : syracuseStep 488501 = 45797) (by norm_num)
theorem B619589 : Blo 323837 619589 := bbase (se 4 (by rfl) ⟨58086, by rfl⟩ : syracuseStep 619589 = 116173) (by norm_num)
theorem B488525 : Blo 323837 488525 := bbase (se 3 (by rfl) ⟨91598, by rfl⟩ : syracuseStep 488525 = 183197) (by norm_num)
theorem B488549 : Blo 323837 488549 := bbase (se 4 (by rfl) ⟨45801, by rfl⟩ : syracuseStep 488549 = 91603) (by norm_num)
theorem B488573 : Blo 323837 488573 := bbase (se 3 (by rfl) ⟨91607, by rfl⟩ : syracuseStep 488573 = 183215) (by norm_num)
theorem B390277 : Blo 323837 390277 := bbase (se 4 (by rfl) ⟨36588, by rfl⟩ : syracuseStep 390277 = 73177) (by norm_num)
theorem B488597 : Blo 323837 488597 := bbase (se 6 (by rfl) ⟨11451, by rfl⟩ : syracuseStep 488597 = 22903) (by norm_num)
theorem B488621 : Blo 323837 488621 := bbase (se 3 (by rfl) ⟨91616, by rfl⟩ : syracuseStep 488621 = 183233) (by norm_num)
theorem B488645 : Blo 323837 488645 := bbase (se 4 (by rfl) ⟨45810, by rfl⟩ : syracuseStep 488645 = 91621) (by norm_num)
theorem B488669 : Blo 323837 488669 := bbase (se 3 (by rfl) ⟨91625, by rfl⟩ : syracuseStep 488669 = 183251) (by norm_num)
theorem B619741 : Blo 323837 619741 := bbase (se 3 (by rfl) ⟨116201, by rfl⟩ : syracuseStep 619741 = 232403) (by norm_num)
theorem B488693 : Blo 323837 488693 := bbase (se 5 (by rfl) ⟨22907, by rfl⟩ : syracuseStep 488693 = 45815) (by norm_num)
theorem B3142901 : Blo 323837 3142901 := bbase (se 5 (by rfl) ⟨147323, by rfl⟩ : syracuseStep 3142901 = 294647) (by norm_num)
theorem B488717 : Blo 323837 488717 := bbase (se 3 (by rfl) ⟨91634, by rfl⟩ : syracuseStep 488717 = 183269) (by norm_num)
theorem B488741 : Blo 323837 488741 := bbase (se 4 (by rfl) ⟨45819, by rfl⟩ : syracuseStep 488741 = 91639) (by norm_num)
theorem B488765 : Blo 323837 488765 := bbase (se 3 (by rfl) ⟨91643, by rfl⟩ : syracuseStep 488765 = 183287) (by norm_num)
theorem B521549 : Blo 323837 521549 := bbase (se 3 (by rfl) ⟨97790, by rfl⟩ : syracuseStep 521549 = 195581) (by norm_num)
theorem B488789 : Blo 323837 488789 := bbase (se 13 (by rfl) ⟨89, by rfl⟩ : syracuseStep 488789 = 179) (by norm_num)
theorem B488813 : Blo 323837 488813 := bbase (se 3 (by rfl) ⟨91652, by rfl⟩ : syracuseStep 488813 = 183305) (by norm_num)
theorem B488837 : Blo 323837 488837 := bbase (se 4 (by rfl) ⟨45828, by rfl⟩ : syracuseStep 488837 = 91657) (by norm_num)
theorem B488861 : Blo 323837 488861 := bbase (se 3 (by rfl) ⟨91661, by rfl⟩ : syracuseStep 488861 = 183323) (by norm_num)
theorem B521645 : Blo 323837 521645 := bbase (se 3 (by rfl) ⟨97808, by rfl⟩ : syracuseStep 521645 = 195617) (by norm_num)
theorem B488885 : Blo 323837 488885 := bbase (se 5 (by rfl) ⟨22916, by rfl⟩ : syracuseStep 488885 = 45833) (by norm_num)
theorem B521677 : Blo 323837 521677 := bbase (se 3 (by rfl) ⟨97814, by rfl⟩ : syracuseStep 521677 = 195629) (by norm_num)
theorem B488909 : Blo 323837 488909 := bbase (se 3 (by rfl) ⟨91670, by rfl⟩ : syracuseStep 488909 = 183341) (by norm_num)
theorem B488933 : Blo 323837 488933 := bbase (se 4 (by rfl) ⟨45837, by rfl⟩ : syracuseStep 488933 = 91675) (by norm_num)
theorem B587261 : Blo 323837 587261 := bbase (se 3 (by rfl) ⟨110111, by rfl⟩ : syracuseStep 587261 = 220223) (by norm_num)
theorem B488957 : Blo 323837 488957 := bbase (se 3 (by rfl) ⟨91679, by rfl⟩ : syracuseStep 488957 = 183359) (by norm_num)
theorem B620045 : Blo 323837 620045 := bbase (se 3 (by rfl) ⟨116258, by rfl⟩ : syracuseStep 620045 = 232517) (by norm_num)
theorem B488981 : Blo 323837 488981 := bbase (se 6 (by rfl) ⟨11460, by rfl⟩ : syracuseStep 488981 = 22921) (by norm_num)
theorem B751141 : Blo 323837 751141 := bbase (se 4 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 751141 = 140839) (by norm_num)
theorem B489005 : Blo 323837 489005 := bbase (se 3 (by rfl) ⟨91688, by rfl⟩ : syracuseStep 489005 = 183377) (by norm_num)
theorem B489029 : Blo 323837 489029 := bbase (se 4 (by rfl) ⟨45846, by rfl⟩ : syracuseStep 489029 = 91693) (by norm_num)
theorem B489053 : Blo 323837 489053 := bbase (se 3 (by rfl) ⟨91697, by rfl⟩ : syracuseStep 489053 = 183395) (by norm_num)
theorem B489077 : Blo 323837 489077 := bbase (se 5 (by rfl) ⟨22925, by rfl⟩ : syracuseStep 489077 = 45851) (by norm_num)
theorem B489101 : Blo 323837 489101 := bbase (se 3 (by rfl) ⟨91706, by rfl⟩ : syracuseStep 489101 = 183413) (by norm_num)
theorem B6256277 : Blo 323837 6256277 := bbase (se 6 (by rfl) ⟨146631, by rfl⟩ : syracuseStep 6256277 = 293263) (by norm_num)
theorem B489125 : Blo 323837 489125 := bbase (se 4 (by rfl) ⟨45855, by rfl⟩ : syracuseStep 489125 = 91711) (by norm_num)
theorem B1111733 : Blo 323837 1111733 := bbase (se 5 (by rfl) ⟨52112, by rfl⟩ : syracuseStep 1111733 = 104225) (by norm_num)
theorem B2815669 : Blo 323837 2815669 := bbase (se 5 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 2815669 = 263969) (by norm_num)
theorem B489149 : Blo 323837 489149 := bbase (se 3 (by rfl) ⟨91715, by rfl⟩ : syracuseStep 489149 = 183431) (by norm_num)
theorem B489173 : Blo 323837 489173 := bbase (se 7 (by rfl) ⟨5732, by rfl⟩ : syracuseStep 489173 = 11465) (by norm_num)
theorem B489197 : Blo 323837 489197 := bbase (se 3 (by rfl) ⟨91724, by rfl⟩ : syracuseStep 489197 = 183449) (by norm_num)
theorem B489221 : Blo 323837 489221 := bbase (se 4 (by rfl) ⟨45864, by rfl⟩ : syracuseStep 489221 = 91729) (by norm_num)
theorem B489245 : Blo 323837 489245 := bbase (se 3 (by rfl) ⟨91733, by rfl⟩ : syracuseStep 489245 = 183467) (by norm_num)
theorem B489269 : Blo 323837 489269 := bbase (se 5 (by rfl) ⟨22934, by rfl⟩ : syracuseStep 489269 = 45869) (by norm_num)
theorem B489293 : Blo 323837 489293 := bbase (se 3 (by rfl) ⟨91742, by rfl⟩ : syracuseStep 489293 = 183485) (by norm_num)
theorem B489317 : Blo 323837 489317 := bbase (se 4 (by rfl) ⟨45873, by rfl⟩ : syracuseStep 489317 = 91747) (by norm_num)
theorem B784237 : Blo 323837 784237 := bbase (se 3 (by rfl) ⟨147044, by rfl⟩ : syracuseStep 784237 = 294089) (by norm_num)
theorem B489341 : Blo 323837 489341 := bbase (se 3 (by rfl) ⟨91751, by rfl⟩ : syracuseStep 489341 = 183503) (by norm_num)
theorem B489365 : Blo 323837 489365 := bbase (se 6 (by rfl) ⟨11469, by rfl⟩ : syracuseStep 489365 = 22939) (by norm_num)
theorem B489389 : Blo 323837 489389 := bbase (se 3 (by rfl) ⟨91760, by rfl⟩ : syracuseStep 489389 = 183521) (by norm_num)
theorem B489413 : Blo 323837 489413 := bbase (se 4 (by rfl) ⟨45882, by rfl⟩ : syracuseStep 489413 = 91765) (by norm_num)
theorem B489437 : Blo 323837 489437 := bbase (se 3 (by rfl) ⟨91769, by rfl⟩ : syracuseStep 489437 = 183539) (by norm_num)
theorem B489461 : Blo 323837 489461 := bbase (se 5 (by rfl) ⟨22943, by rfl⟩ : syracuseStep 489461 = 45887) (by norm_num)
theorem B489485 : Blo 323837 489485 := bbase (se 3 (by rfl) ⟨91778, by rfl⟩ : syracuseStep 489485 = 183557) (by norm_num)
theorem B489509 : Blo 323837 489509 := bbase (se 4 (by rfl) ⟨45891, by rfl⟩ : syracuseStep 489509 = 91783) (by norm_num)
theorem B489533 : Blo 323837 489533 := bbase (se 3 (by rfl) ⟨91787, by rfl⟩ : syracuseStep 489533 = 183575) (by norm_num)
theorem B489557 : Blo 323837 489557 := bbase (se 8 (by rfl) ⟨2868, by rfl⟩ : syracuseStep 489557 = 5737) (by norm_num)
theorem B391277 : Blo 323837 391277 := bbase (se 3 (by rfl) ⟨73364, by rfl⟩ : syracuseStep 391277 = 146729) (by norm_num)
theorem B489581 : Blo 323837 489581 := bbase (se 3 (by rfl) ⟨91796, by rfl⟩ : syracuseStep 489581 = 183593) (by norm_num)
theorem B2652277 : Blo 323837 2652277 := bbase (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) (by norm_num)
theorem B489605 : Blo 323837 489605 := bbase (se 4 (by rfl) ⟨45900, by rfl⟩ : syracuseStep 489605 = 91801) (by norm_num)
theorem B391325 : Blo 323837 391325 := bbase (se 3 (by rfl) ⟨73373, by rfl⟩ : syracuseStep 391325 = 146747) (by norm_num)
theorem B489629 : Blo 323837 489629 := bbase (se 3 (by rfl) ⟨91805, by rfl⟩ : syracuseStep 489629 = 183611) (by norm_num)
theorem B489653 : Blo 323837 489653 := bbase (se 5 (by rfl) ⟨22952, by rfl⟩ : syracuseStep 489653 = 45905) (by norm_num)
theorem B489677 : Blo 323837 489677 := bbase (se 3 (by rfl) ⟨91814, by rfl⟩ : syracuseStep 489677 = 183629) (by norm_num)
theorem B489701 : Blo 323837 489701 := bbase (se 4 (by rfl) ⟨45909, by rfl⟩ : syracuseStep 489701 = 91819) (by norm_num)
theorem B489725 : Blo 323837 489725 := bbase (se 3 (by rfl) ⟨91823, by rfl⟩ : syracuseStep 489725 = 183647) (by norm_num)
theorem B620797 : Blo 323837 620797 := bbase (se 3 (by rfl) ⟨116399, by rfl⟩ : syracuseStep 620797 = 232799) (by norm_num)
theorem B489749 : Blo 323837 489749 := bbase (se 6 (by rfl) ⟨11478, by rfl⟩ : syracuseStep 489749 = 22957) (by norm_num)
theorem B489773 : Blo 323837 489773 := bbase (se 3 (by rfl) ⟨91832, by rfl⟩ : syracuseStep 489773 = 183665) (by norm_num)
theorem B489797 : Blo 323837 489797 := bbase (se 4 (by rfl) ⟨45918, by rfl⟩ : syracuseStep 489797 = 91837) (by norm_num)
theorem B489821 : Blo 323837 489821 := bbase (se 3 (by rfl) ⟨91841, by rfl⟩ : syracuseStep 489821 = 183683) (by norm_num)
theorem B489845 : Blo 323837 489845 := bbase (se 5 (by rfl) ⟨22961, by rfl⟩ : syracuseStep 489845 = 45923) (by norm_num)
theorem B489869 : Blo 323837 489869 := bbase (se 3 (by rfl) ⟨91850, by rfl⟩ : syracuseStep 489869 = 183701) (by norm_num)
theorem B620941 : Blo 323837 620941 := bbase (se 3 (by rfl) ⟨116426, by rfl⟩ : syracuseStep 620941 = 232853) (by norm_num)
theorem B489893 : Blo 323837 489893 := bbase (se 4 (by rfl) ⟨45927, by rfl⟩ : syracuseStep 489893 = 91855) (by norm_num)
theorem B489917 : Blo 323837 489917 := bbase (se 3 (by rfl) ⟨91859, by rfl⟩ : syracuseStep 489917 = 183719) (by norm_num)
theorem B1046981 : Blo 323837 1046981 := bbase (se 4 (by rfl) ⟨98154, by rfl⟩ : syracuseStep 1046981 = 196309) (by norm_num)
theorem B784853 : Blo 323837 784853 := bbase (se 7 (by rfl) ⟨9197, by rfl⟩ : syracuseStep 784853 = 18395) (by norm_num)
theorem B489941 : Blo 323837 489941 := bbase (se 7 (by rfl) ⟨5741, by rfl⟩ : syracuseStep 489941 = 11483) (by norm_num)
theorem B489965 : Blo 323837 489965 := bbase (se 3 (by rfl) ⟨91868, by rfl⟩ : syracuseStep 489965 = 183737) (by norm_num)
theorem B489989 : Blo 323837 489989 := bbase (se 4 (by rfl) ⟨45936, by rfl⟩ : syracuseStep 489989 = 91873) (by norm_num)
theorem B490013 : Blo 323837 490013 := bbase (se 3 (by rfl) ⟨91877, by rfl⟩ : syracuseStep 490013 = 183755) (by norm_num)
theorem B621101 : Blo 323837 621101 := bbase (se 3 (by rfl) ⟨116456, by rfl⟩ : syracuseStep 621101 = 232913) (by norm_num)
theorem B490037 : Blo 323837 490037 := bbase (se 5 (by rfl) ⟨22970, by rfl⟩ : syracuseStep 490037 = 45941) (by norm_num)
theorem B490061 : Blo 323837 490061 := bbase (se 3 (by rfl) ⟨91886, by rfl⟩ : syracuseStep 490061 = 183773) (by norm_num)
theorem B490085 : Blo 323837 490085 := bbase (se 4 (by rfl) ⟨45945, by rfl⟩ : syracuseStep 490085 = 91891) (by norm_num)
theorem B490109 : Blo 323837 490109 := bbase (se 3 (by rfl) ⟨91895, by rfl⟩ : syracuseStep 490109 = 183791) (by norm_num)
theorem B1243781 : Blo 323837 1243781 := bbase (se 4 (by rfl) ⟨116604, by rfl⟩ : syracuseStep 1243781 = 233209) (by norm_num)
theorem B490133 : Blo 323837 490133 := bbase (se 6 (by rfl) ⟨11487, by rfl⟩ : syracuseStep 490133 = 22975) (by norm_num)
theorem B490157 : Blo 323837 490157 := bbase (se 3 (by rfl) ⟨91904, by rfl⟩ : syracuseStep 490157 = 183809) (by norm_num)
theorem B621245 : Blo 323837 621245 := bbase (se 3 (by rfl) ⟨116483, by rfl⟩ : syracuseStep 621245 = 232967) (by norm_num)
theorem B391873 : Blo 323837 391873 := bbase (se 2 (by rfl) ⟨146952, by rfl⟩ : syracuseStep 391873 = 293905) (by norm_num)
theorem B490181 : Blo 323837 490181 := bbase (se 4 (by rfl) ⟨45954, by rfl⟩ : syracuseStep 490181 = 91909) (by norm_num)
theorem B490205 : Blo 323837 490205 := bbase (se 3 (by rfl) ⟨91913, by rfl⟩ : syracuseStep 490205 = 183827) (by norm_num)
theorem B490229 : Blo 323837 490229 := bbase (se 5 (by rfl) ⟨22979, by rfl⟩ : syracuseStep 490229 = 45959) (by norm_num)
theorem B490253 : Blo 323837 490253 := bbase (se 3 (by rfl) ⟨91922, by rfl⟩ : syracuseStep 490253 = 183845) (by norm_num)
theorem B4193045 : Blo 323837 4193045 := bbase (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) (by norm_num)
theorem B490277 : Blo 323837 490277 := bbase (se 4 (by rfl) ⟨45963, by rfl⟩ : syracuseStep 490277 = 91927) (by norm_num)
theorem B850733 : Blo 323837 850733 := bbase (se 3 (by rfl) ⟨159512, by rfl⟩ : syracuseStep 850733 = 319025) (by norm_num)
theorem B490301 : Blo 323837 490301 := bbase (se 3 (by rfl) ⟨91931, by rfl⟩ : syracuseStep 490301 = 183863) (by norm_num)
theorem B490325 : Blo 323837 490325 := bbase (se 9 (by rfl) ⟨1436, by rfl⟩ : syracuseStep 490325 = 2873) (by norm_num)
theorem B490349 : Blo 323837 490349 := bbase (se 3 (by rfl) ⟨91940, by rfl⟩ : syracuseStep 490349 = 183881) (by norm_num)
theorem B490373 : Blo 323837 490373 := bbase (se 4 (by rfl) ⟨45972, by rfl⟩ : syracuseStep 490373 = 91945) (by norm_num)
theorem B490397 : Blo 323837 490397 := bbase (se 3 (by rfl) ⟨91949, by rfl⟩ : syracuseStep 490397 = 183899) (by norm_num)
theorem B1244069 : Blo 323837 1244069 := bbase (se 4 (by rfl) ⟨116631, by rfl⟩ : syracuseStep 1244069 = 233263) (by norm_num)
theorem B523189 : Blo 323837 523189 := bbase (se 5 (by rfl) ⟨24524, by rfl⟩ : syracuseStep 523189 = 49049) (by norm_num)
theorem B490421 : Blo 323837 490421 := bbase (se 5 (by rfl) ⟨22988, by rfl⟩ : syracuseStep 490421 = 45977) (by norm_num)
theorem B490445 : Blo 323837 490445 := bbase (se 3 (by rfl) ⟨91958, by rfl⟩ : syracuseStep 490445 = 183917) (by norm_num)
theorem B621533 : Blo 323837 621533 := bbase (se 3 (by rfl) ⟨116537, by rfl⟩ : syracuseStep 621533 = 233075) (by norm_num)
theorem B490469 : Blo 323837 490469 := bbase (se 4 (by rfl) ⟨45981, by rfl⟩ : syracuseStep 490469 = 91963) (by norm_num)
theorem B490493 : Blo 323837 490493 := bbase (se 3 (by rfl) ⟨91967, by rfl⟩ : syracuseStep 490493 = 183935) (by norm_num)
theorem B490517 : Blo 323837 490517 := bbase (se 6 (by rfl) ⟨11496, by rfl⟩ : syracuseStep 490517 = 22993) (by norm_num)
theorem B490541 : Blo 323837 490541 := bbase (se 3 (by rfl) ⟨91976, by rfl⟩ : syracuseStep 490541 = 183953) (by norm_num)
theorem B490565 : Blo 323837 490565 := bbase (se 4 (by rfl) ⟨45990, by rfl⟩ : syracuseStep 490565 = 91981) (by norm_num)
theorem B490589 : Blo 323837 490589 := bbase (se 3 (by rfl) ⟨91985, by rfl⟩ : syracuseStep 490589 = 183971) (by norm_num)
theorem B490613 : Blo 323837 490613 := bbase (se 5 (by rfl) ⟨22997, by rfl⟩ : syracuseStep 490613 = 45995) (by norm_num)
theorem B621685 : Blo 323837 621685 := bbase (se 5 (by rfl) ⟨29141, by rfl⟩ : syracuseStep 621685 = 58283) (by norm_num)
theorem B490637 : Blo 323837 490637 := bbase (se 3 (by rfl) ⟨91994, by rfl⟩ : syracuseStep 490637 = 183989) (by norm_num)
theorem B392353 : Blo 323837 392353 := bbase (se 2 (by rfl) ⟨147132, by rfl⟩ : syracuseStep 392353 = 294265) (by norm_num)
theorem B490661 : Blo 323837 490661 := bbase (se 4 (by rfl) ⟨45999, by rfl⟩ : syracuseStep 490661 = 91999) (by norm_num)
theorem B490685 : Blo 323837 490685 := bbase (se 3 (by rfl) ⟨92003, by rfl⟩ : syracuseStep 490685 = 184007) (by norm_num)
theorem B490709 : Blo 323837 490709 := bbase (se 7 (by rfl) ⟨5750, by rfl⟩ : syracuseStep 490709 = 11501) (by norm_num)
theorem B785629 : Blo 323837 785629 := bbase (se 3 (by rfl) ⟨147305, by rfl⟩ : syracuseStep 785629 = 294611) (by norm_num)
theorem B490733 : Blo 323837 490733 := bbase (se 3 (by rfl) ⟨92012, by rfl⟩ : syracuseStep 490733 = 184025) (by norm_num)
theorem B490757 : Blo 323837 490757 := bbase (se 4 (by rfl) ⟨46008, by rfl⟩ : syracuseStep 490757 = 92017) (by norm_num)
theorem B490781 : Blo 323837 490781 := bbase (se 3 (by rfl) ⟨92021, by rfl⟩ : syracuseStep 490781 = 184043) (by norm_num)
theorem B490805 : Blo 323837 490805 := bbase (se 5 (by rfl) ⟨23006, by rfl⟩ : syracuseStep 490805 = 46013) (by norm_num)
theorem B490829 : Blo 323837 490829 := bbase (se 3 (by rfl) ⟨92030, by rfl⟩ : syracuseStep 490829 = 184061) (by norm_num)
theorem B490853 : Blo 323837 490853 := bbase (se 4 (by rfl) ⟨46017, by rfl⟩ : syracuseStep 490853 = 92035) (by norm_num)
theorem B490877 : Blo 323837 490877 := bbase (se 3 (by rfl) ⟨92039, by rfl⟩ : syracuseStep 490877 = 184079) (by norm_num)
theorem B490901 : Blo 323837 490901 := bbase (se 6 (by rfl) ⟨11505, by rfl⟩ : syracuseStep 490901 = 23011) (by norm_num)
theorem B621989 : Blo 323837 621989 := bbase (se 4 (by rfl) ⟨58311, by rfl⟩ : syracuseStep 621989 = 116623) (by norm_num)
theorem B490925 : Blo 323837 490925 := bbase (se 3 (by rfl) ⟨92048, by rfl⟩ : syracuseStep 490925 = 184097) (by norm_num)
theorem B490949 : Blo 323837 490949 := bbase (se 4 (by rfl) ⟨46026, by rfl⟩ : syracuseStep 490949 = 92053) (by norm_num)
theorem B490973 : Blo 323837 490973 := bbase (se 3 (by rfl) ⟨92057, by rfl⟩ : syracuseStep 490973 = 184115) (by norm_num)
theorem B490997 : Blo 323837 490997 := bbase (se 5 (by rfl) ⟨23015, by rfl⟩ : syracuseStep 490997 = 46031) (by norm_num)
theorem B1048069 : Blo 323837 1048069 := bbase (se 4 (by rfl) ⟨98256, by rfl⟩ : syracuseStep 1048069 = 196513) (by norm_num)
theorem B491021 : Blo 323837 491021 := bbase (se 3 (by rfl) ⟨92066, by rfl⟩ : syracuseStep 491021 = 184133) (by norm_num)
theorem B491045 : Blo 323837 491045 := bbase (se 4 (by rfl) ⟨46035, by rfl⟩ : syracuseStep 491045 = 92071) (by norm_num)
theorem B491069 : Blo 323837 491069 := bbase (se 3 (by rfl) ⟨92075, by rfl⟩ : syracuseStep 491069 = 184151) (by norm_num)
theorem B491093 : Blo 323837 491093 := bbase (se 8 (by rfl) ⟨2877, by rfl⟩ : syracuseStep 491093 = 5755) (by norm_num)
theorem B491117 : Blo 323837 491117 := bbase (se 3 (by rfl) ⟨92084, by rfl⟩ : syracuseStep 491117 = 184169) (by norm_num)
theorem B523901 : Blo 323837 523901 := bbase (se 3 (by rfl) ⟨98231, by rfl⟩ : syracuseStep 523901 = 196463) (by norm_num)
theorem B491141 : Blo 323837 491141 := bbase (se 4 (by rfl) ⟨46044, by rfl⟩ : syracuseStep 491141 = 92089) (by norm_num)
theorem B491165 : Blo 323837 491165 := bbase (se 3 (by rfl) ⟨92093, by rfl⟩ : syracuseStep 491165 = 184187) (by norm_num)
theorem B491189 : Blo 323837 491189 := bbase (se 5 (by rfl) ⟨23024, by rfl⟩ : syracuseStep 491189 = 46049) (by norm_num)
theorem B491213 : Blo 323837 491213 := bbase (se 3 (by rfl) ⟨92102, by rfl⟩ : syracuseStep 491213 = 184205) (by norm_num)
theorem B491237 : Blo 323837 491237 := bbase (se 4 (by rfl) ⟨46053, by rfl⟩ : syracuseStep 491237 = 92107) (by norm_num)
theorem B491261 : Blo 323837 491261 := bbase (se 3 (by rfl) ⟨92111, by rfl⟩ : syracuseStep 491261 = 184223) (by norm_num)
theorem B491285 : Blo 323837 491285 := bbase (se 6 (by rfl) ⟨11514, by rfl⟩ : syracuseStep 491285 = 23029) (by norm_num)
theorem B491309 : Blo 323837 491309 := bbase (se 3 (by rfl) ⟨92120, by rfl⟩ : syracuseStep 491309 = 184241) (by norm_num)
theorem B491333 : Blo 323837 491333 := bbase (se 4 (by rfl) ⟨46062, by rfl⟩ : syracuseStep 491333 = 92125) (by norm_num)
theorem B5930837 : Blo 323837 5930837 := bbase (se 9 (by rfl) ⟨17375, by rfl⟩ : syracuseStep 5930837 = 34751) (by norm_num)
theorem B491357 : Blo 323837 491357 := bbase (se 3 (by rfl) ⟨92129, by rfl⟩ : syracuseStep 491357 = 184259) (by norm_num)
theorem B491381 : Blo 323837 491381 := bbase (se 5 (by rfl) ⟨23033, by rfl⟩ : syracuseStep 491381 = 46067) (by norm_num)
theorem B491405 : Blo 323837 491405 := bbase (se 3 (by rfl) ⟨92138, by rfl⟩ : syracuseStep 491405 = 184277) (by norm_num)
theorem B786341 : Blo 323837 786341 := bbase (se 4 (by rfl) ⟨73719, by rfl⟩ : syracuseStep 786341 = 147439) (by norm_num)
theorem B491429 : Blo 323837 491429 := bbase (se 4 (by rfl) ⟨46071, by rfl⟩ : syracuseStep 491429 = 92143) (by norm_num)
theorem B491453 : Blo 323837 491453 := bbase (se 3 (by rfl) ⟨92147, by rfl⟩ : syracuseStep 491453 = 184295) (by norm_num)
theorem B491477 : Blo 323837 491477 := bbase (se 7 (by rfl) ⟨5759, by rfl⟩ : syracuseStep 491477 = 11519) (by norm_num)
theorem B491501 : Blo 323837 491501 := bbase (se 3 (by rfl) ⟨92156, by rfl⟩ : syracuseStep 491501 = 184313) (by norm_num)
theorem B327683 : Blo 323837 327683 := bstep (se 1 (by rfl) ⟨245762, by rfl⟩ : syracuseStep 327683 = 491525) B491525
theorem B491537 : Blo 323837 491537 := bstep (se 2 (by rfl) ⟨184326, by rfl⟩ : syracuseStep 491537 = 368653) B368653
theorem B327699 : Blo 323837 327699 := bstep (se 1 (by rfl) ⟨245774, by rfl⟩ : syracuseStep 327699 = 491549) B491549
theorem B491555 : Blo 323837 491555 := bstep (se 1 (by rfl) ⟨368666, by rfl⟩ : syracuseStep 491555 = 737333) B737333
theorem B327715 : Blo 323837 327715 := bstep (se 1 (by rfl) ⟨245786, by rfl⟩ : syracuseStep 327715 = 491573) B491573
theorem B1048621 : Blo 323837 1048621 := bstep (se 3 (by rfl) ⟨196616, by rfl⟩ : syracuseStep 1048621 = 393233) B393233
theorem B327731 : Blo 323837 327731 := bstep (se 1 (by rfl) ⟨245798, by rfl⟩ : syracuseStep 327731 = 491597) B491597
theorem B491585 : Blo 323837 491585 := bstep (se 2 (by rfl) ⟨184344, by rfl⟩ : syracuseStep 491585 = 368689) B368689
theorem B327747 : Blo 323837 327747 := bstep (se 1 (by rfl) ⟨245810, by rfl⟩ : syracuseStep 327747 = 491621) B491621
theorem B491603 : Blo 323837 491603 := bstep (se 1 (by rfl) ⟨368702, by rfl⟩ : syracuseStep 491603 = 737405) B737405
theorem B327763 : Blo 323837 327763 := bstep (se 1 (by rfl) ⟨245822, by rfl⟩ : syracuseStep 327763 = 491645) B491645
theorem B327779 : Blo 323837 327779 := bstep (se 1 (by rfl) ⟨245834, by rfl⟩ : syracuseStep 327779 = 491669) B491669
theorem B2097265 : Blo 323837 2097265 := bstep (se 2 (by rfl) ⟨786474, by rfl⟩ : syracuseStep 2097265 = 1572949) B1572949
theorem B491633 : Blo 323837 491633 := bstep (se 2 (by rfl) ⟨184362, by rfl⟩ : syracuseStep 491633 = 368725) B368725
theorem B327795 : Blo 323837 327795 := bstep (se 1 (by rfl) ⟨245846, by rfl⟩ : syracuseStep 327795 = 491693) B491693
theorem B491651 : Blo 323837 491651 := bstep (se 1 (by rfl) ⟨368738, by rfl⟩ : syracuseStep 491651 = 737477) B737477
theorem B327811 : Blo 323837 327811 := bstep (se 1 (by rfl) ⟨245858, by rfl⟩ : syracuseStep 327811 = 491717) B491717
theorem B327827 : Blo 323837 327827 := bstep (se 1 (by rfl) ⟨245870, by rfl⟩ : syracuseStep 327827 = 491741) B491741
theorem B491681 : Blo 323837 491681 := bstep (se 2 (by rfl) ⟨184380, by rfl⟩ : syracuseStep 491681 = 368761) B368761
theorem B524465 : Blo 323837 524465 := bstep (se 2 (by rfl) ⟨196674, by rfl⟩ : syracuseStep 524465 = 393349) B393349
theorem B491699 : Blo 323837 491699 := bstep (se 1 (by rfl) ⟨368774, by rfl⟩ : syracuseStep 491699 = 737549) B737549
theorem B491729 : Blo 323837 491729 := bstep (se 2 (by rfl) ⟨184398, by rfl⟩ : syracuseStep 491729 = 368797) B368797
theorem B40337621 : Blo 323837 40337621 := bstep (se 7 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 40337621 = 945413) B945413
theorem B491747 : Blo 323837 491747 := bstep (se 1 (by rfl) ⟨368810, by rfl⟩ : syracuseStep 491747 = 737621) B737621
theorem B524675 : Blo 323837 524675 := bstep (se 1 (by rfl) ⟨393506, by rfl⟩ : syracuseStep 524675 = 787013) B787013
theorem B557489 : Blo 323837 557489 := bstep (se 2 (by rfl) ⟨209058, by rfl⟩ : syracuseStep 557489 = 418117) B418117
theorem B328259 : Blo 323837 328259 := bstep (se 1 (by rfl) ⟨246194, by rfl⟩ : syracuseStep 328259 = 492389) B492389
theorem B819953 : Blo 323837 819953 := bstep (se 2 (by rfl) ⟨307482, by rfl⟩ : syracuseStep 819953 = 614965) B614965
theorem B820003 : Blo 323837 820003 := bstep (se 1 (by rfl) ⟨615002, by rfl⟩ : syracuseStep 820003 = 1230005) B1230005
theorem B1049453 : Blo 323837 1049453 := bstep (se 3 (by rfl) ⟨196772, by rfl⟩ : syracuseStep 1049453 = 393545) B393545
theorem B787313 : Blo 323837 787313 := bstep (se 2 (by rfl) ⟨295242, by rfl⟩ : syracuseStep 787313 = 590485) B590485
theorem B820145 : Blo 323837 820145 := bstep (se 2 (by rfl) ⟨307554, by rfl⟩ : syracuseStep 820145 = 615109) B615109
theorem B1639601 : Blo 323837 1639601 := bstep (se 2 (by rfl) ⟨614850, by rfl⟩ : syracuseStep 1639601 = 1229701) B1229701
theorem B328883 : Blo 323837 328883 := bstep (se 1 (by rfl) ⟨246662, by rfl⟩ : syracuseStep 328883 = 493325) B493325
theorem B7013573 : Blo 323837 7013573 := bstep (se 4 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 7013573 = 1315045) B1315045
theorem B558289 : Blo 323837 558289 := bstep (se 2 (by rfl) ⟨209358, by rfl⟩ : syracuseStep 558289 = 418717) B418717
theorem B787697 : Blo 323837 787697 := bstep (se 2 (by rfl) ⟨295386, by rfl⟩ : syracuseStep 787697 = 590773) B590773
theorem B492851 : Blo 323837 492851 := bstep (se 1 (by rfl) ⟨369638, by rfl⟩ : syracuseStep 492851 = 739277) B739277
theorem B1181155 : Blo 323837 1181155 := bstep (se 1 (by rfl) ⟨885866, by rfl⟩ : syracuseStep 1181155 = 1771733) B1771733
theorem B2164429 : Blo 323837 2164429 := bstep (se 3 (by rfl) ⟨405830, by rfl⟩ : syracuseStep 2164429 = 811661) B811661
theorem B821137 : Blo 323837 821137 := bstep (se 2 (by rfl) ⟨307926, by rfl⟩ : syracuseStep 821137 = 615853) B615853
theorem B493697 : Blo 323837 493697 := bstep (se 2 (by rfl) ⟨185136, by rfl⟩ : syracuseStep 493697 = 370273) B370273
theorem B821411 : Blo 323837 821411 := bstep (se 1 (by rfl) ⟨616058, by rfl⟩ : syracuseStep 821411 = 1232117) B1232117
theorem B821603 : Blo 323837 821603 := bstep (se 1 (by rfl) ⟨616202, by rfl⟩ : syracuseStep 821603 = 1232405) B1232405
theorem B2460131 : Blo 323837 2460131 := bstep (se 1 (by rfl) ⟨1845098, by rfl⟩ : syracuseStep 2460131 = 3690197) B3690197
theorem B461315 : Blo 323837 461315 := bstep (se 1 (by rfl) ⟨345986, by rfl⟩ : syracuseStep 461315 = 691973) B691973
theorem B1641059 : Blo 323837 1641059 := bstep (se 1 (by rfl) ⟨1230794, by rfl⟩ : syracuseStep 1641059 = 2461589) B2461589
theorem B461953 : Blo 323837 461953 := bstep (se 2 (by rfl) ⟨173232, by rfl⟩ : syracuseStep 461953 = 346465) B346465
theorem B494723 : Blo 323837 494723 := bstep (se 1 (by rfl) ⟨371042, by rfl⟩ : syracuseStep 494723 = 742085) B742085
theorem B822545 : Blo 323837 822545 := bstep (se 2 (by rfl) ⟨308454, by rfl⟩ : syracuseStep 822545 = 616909) B616909
theorem B822595 : Blo 323837 822595 := bstep (se 1 (by rfl) ⟨616946, by rfl⟩ : syracuseStep 822595 = 1233893) B1233893
theorem B1641869 : Blo 323837 1641869 := bstep (se 3 (by rfl) ⟨307850, by rfl⟩ : syracuseStep 1641869 = 615701) B615701
theorem B462289 : Blo 323837 462289 := bstep (se 2 (by rfl) ⟨173358, by rfl⟩ : syracuseStep 462289 = 346717) B346717
theorem B822737 : Blo 323837 822737 := bstep (se 2 (by rfl) ⟨308526, by rfl⟩ : syracuseStep 822737 = 617053) B617053
theorem B1117891 : Blo 323837 1117891 := bstep (se 1 (by rfl) ⟨838418, by rfl⟩ : syracuseStep 1117891 = 1676837) B1676837
theorem B659171 : Blo 323837 659171 := bstep (se 1 (by rfl) ⟨494378, by rfl⟩ : syracuseStep 659171 = 988757) B988757
theorem B364387 : Blo 323837 364387 := bstep (se 1 (by rfl) ⟨273290, by rfl⟩ : syracuseStep 364387 = 546581) B546581
theorem B1412963 : Blo 323837 1412963 := bstep (se 1 (by rfl) ⟨1059722, by rfl⟩ : syracuseStep 1412963 = 2119445) B2119445
theorem B364531 : Blo 323837 364531 := bstep (se 1 (by rfl) ⟨273398, by rfl⟩ : syracuseStep 364531 = 546797) B546797
theorem B462881 : Blo 323837 462881 := bstep (se 2 (by rfl) ⟨173580, by rfl⟩ : syracuseStep 462881 = 347161) B347161
theorem B364675 : Blo 323837 364675 := bstep (se 1 (by rfl) ⟨273506, by rfl⟩ : syracuseStep 364675 = 547013) B547013
theorem B954595 : Blo 323837 954595 := bstep (se 1 (by rfl) ⟨715946, by rfl⟩ : syracuseStep 954595 = 1431893) B1431893
theorem B364819 : Blo 323837 364819 := bstep (se 1 (by rfl) ⟨273614, by rfl⟩ : syracuseStep 364819 = 547229) B547229
theorem B790897 : Blo 323837 790897 := bstep (se 2 (by rfl) ⟨296586, by rfl⟩ : syracuseStep 790897 = 593173) B593173
theorem B364963 : Blo 323837 364963 := bstep (se 1 (by rfl) ⟨273722, by rfl⟩ : syracuseStep 364963 = 547445) B547445
theorem B823729 : Blo 323837 823729 := bstep (se 2 (by rfl) ⟨308898, by rfl⟩ : syracuseStep 823729 = 617797) B617797
theorem B2822597 : Blo 323837 2822597 := bstep (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) B529237
theorem B496129 : Blo 323837 496129 := bstep (se 2 (by rfl) ⟨186048, by rfl⟩ : syracuseStep 496129 = 372097) B372097
theorem B365107 : Blo 323837 365107 := bstep (se 1 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 365107 = 547661) B547661
theorem B463411 : Blo 323837 463411 := bstep (se 1 (by rfl) ⟨347558, by rfl⟩ : syracuseStep 463411 = 695117) B695117
theorem B365251 : Blo 323837 365251 := bstep (se 1 (by rfl) ⟨273938, by rfl⟩ : syracuseStep 365251 = 547877) B547877
theorem B824003 : Blo 323837 824003 := bstep (se 1 (by rfl) ⟨618002, by rfl⟩ : syracuseStep 824003 = 1236005) B1236005
theorem B365395 : Blo 323837 365395 := bstep (se 1 (by rfl) ⟨274046, by rfl⟩ : syracuseStep 365395 = 548093) B548093
theorem B824195 : Blo 323837 824195 := bstep (se 1 (by rfl) ⟨618146, by rfl⟩ : syracuseStep 824195 = 1236293) B1236293
theorem B463747 : Blo 323837 463747 := bstep (se 1 (by rfl) ⟨347810, by rfl⟩ : syracuseStep 463747 = 695621) B695621
theorem B365539 : Blo 323837 365539 := bstep (se 1 (by rfl) ⟨274154, by rfl⟩ : syracuseStep 365539 = 548309) B548309
theorem B2987021 : Blo 323837 2987021 := bstep (se 3 (by rfl) ⟨560066, by rfl⟩ : syracuseStep 2987021 = 1120133) B1120133
theorem B1315889 : Blo 323837 1315889 := bstep (se 2 (by rfl) ⟨493458, by rfl⟩ : syracuseStep 1315889 = 986917) B986917
theorem B365683 : Blo 323837 365683 := bstep (se 1 (by rfl) ⟨274262, by rfl⟩ : syracuseStep 365683 = 548525) B548525
theorem B365827 : Blo 323837 365827 := bstep (se 1 (by rfl) ⟨274370, by rfl⟩ : syracuseStep 365827 = 548741) B548741
theorem B660881 : Blo 323837 660881 := bstep (se 2 (by rfl) ⟨247830, by rfl⟩ : syracuseStep 660881 = 495661) B495661
theorem B365971 : Blo 323837 365971 := bstep (se 1 (by rfl) ⟨274478, by rfl⟩ : syracuseStep 365971 = 548957) B548957
theorem B464305 : Blo 323837 464305 := bstep (se 2 (by rfl) ⟨174114, by rfl⟩ : syracuseStep 464305 = 348229) B348229
theorem B464339 : Blo 323837 464339 := bstep (se 1 (by rfl) ⟨348254, by rfl⟩ : syracuseStep 464339 = 696509) B696509
theorem B366115 : Blo 323837 366115 := bstep (se 1 (by rfl) ⟨274586, by rfl⟩ : syracuseStep 366115 = 549173) B549173
theorem B366259 : Blo 323837 366259 := bstep (se 1 (by rfl) ⟨274694, by rfl⟩ : syracuseStep 366259 = 549389) B549389
theorem B1119971 : Blo 323837 1119971 := bstep (se 1 (by rfl) ⟨839978, by rfl⟩ : syracuseStep 1119971 = 1679957) B1679957
theorem B825137 : Blo 323837 825137 := bstep (se 2 (by rfl) ⟨309426, by rfl⟩ : syracuseStep 825137 = 618853) B618853
theorem B366403 : Blo 323837 366403 := bstep (se 1 (by rfl) ⟨274802, by rfl⟩ : syracuseStep 366403 = 549605) B549605
theorem B1120081 : Blo 323837 1120081 := bstep (se 2 (by rfl) ⟨420030, by rfl⟩ : syracuseStep 1120081 = 840061) B840061
theorem B825187 : Blo 323837 825187 := bstep (se 1 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 825187 = 1237781) B1237781
theorem B366547 : Blo 323837 366547 := bstep (se 1 (by rfl) ⟨274910, by rfl⟩ : syracuseStep 366547 = 549821) B549821
theorem B923633 : Blo 323837 923633 := bstep (se 2 (by rfl) ⟨346362, by rfl⟩ : syracuseStep 923633 = 692725) B692725
theorem B825329 : Blo 323837 825329 := bstep (se 2 (by rfl) ⟨309498, by rfl⟩ : syracuseStep 825329 = 618997) B618997
theorem B464897 : Blo 323837 464897 := bstep (se 2 (by rfl) ⟨174336, by rfl⟩ : syracuseStep 464897 = 348673) B348673
theorem B464977 : Blo 323837 464977 := bstep (se 2 (by rfl) ⟨174366, by rfl⟩ : syracuseStep 464977 = 348733) B348733
theorem B366691 : Blo 323837 366691 := bstep (se 1 (by rfl) ⟨275018, by rfl⟩ : syracuseStep 366691 = 550037) B550037
theorem B1579121 : Blo 323837 1579121 := bstep (se 2 (by rfl) ⟨592170, by rfl⟩ : syracuseStep 1579121 = 1184341) B1184341
theorem B923825 : Blo 323837 923825 := bstep (se 2 (by rfl) ⟨346434, by rfl⟩ : syracuseStep 923825 = 692869) B692869
theorem B1644785 : Blo 323837 1644785 := bstep (se 2 (by rfl) ⟨616794, by rfl⟩ : syracuseStep 1644785 = 1233589) B1233589
theorem B366835 : Blo 323837 366835 := bstep (se 1 (by rfl) ⟨275126, by rfl⟩ : syracuseStep 366835 = 550253) B550253
theorem B694595 : Blo 323837 694595 := bstep (se 1 (by rfl) ⟨520946, by rfl⟩ : syracuseStep 694595 = 1041893) B1041893
theorem B366979 : Blo 323837 366979 := bstep (se 1 (by rfl) ⟨275234, by rfl⟩ : syracuseStep 366979 = 550469) B550469
theorem B367123 : Blo 323837 367123 := bstep (se 1 (by rfl) ⟨275342, by rfl⟩ : syracuseStep 367123 = 550685) B550685
theorem B367267 : Blo 323837 367267 := bstep (se 1 (by rfl) ⟨275450, by rfl⟩ : syracuseStep 367267 = 550901) B550901
theorem B563939 : Blo 323837 563939 := bstep (se 1 (by rfl) ⟨422954, by rfl⟩ : syracuseStep 563939 = 845909) B845909
theorem B367411 : Blo 323837 367411 := bstep (se 1 (by rfl) ⟨275558, by rfl⟩ : syracuseStep 367411 = 551117) B551117
theorem B2235235 : Blo 323837 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B465763 : Blo 323837 465763 := bstep (se 1 (by rfl) ⟨349322, by rfl⟩ : syracuseStep 465763 = 698645) B698645
theorem B367555 : Blo 323837 367555 := bstep (se 1 (by rfl) ⟨275666, by rfl⟩ : syracuseStep 367555 = 551333) B551333
theorem B826321 : Blo 323837 826321 := bstep (se 2 (by rfl) ⟨309870, by rfl⟩ : syracuseStep 826321 = 619741) B619741
theorem B367699 : Blo 323837 367699 := bstep (se 1 (by rfl) ⟨275774, by rfl⟩ : syracuseStep 367699 = 551549) B551549
theorem B924817 : Blo 323837 924817 := bstep (se 2 (by rfl) ⟨346806, by rfl⟩ : syracuseStep 924817 = 693613) B693613
theorem B1383587 : Blo 323837 1383587 := bstep (se 1 (by rfl) ⟨1037690, by rfl⟩ : syracuseStep 1383587 = 2075381) B2075381
theorem B695459 : Blo 323837 695459 := bstep (se 1 (by rfl) ⟨521594, by rfl⟩ : syracuseStep 695459 = 1043189) B1043189
theorem B564451 : Blo 323837 564451 := bstep (se 1 (by rfl) ⟨423338, by rfl⟩ : syracuseStep 564451 = 846677) B846677
theorem B826595 : Blo 323837 826595 := bstep (se 1 (by rfl) ⟨619946, by rfl⟩ : syracuseStep 826595 = 1239893) B1239893
theorem B367843 : Blo 323837 367843 := bstep (se 1 (by rfl) ⟨275882, by rfl⟩ : syracuseStep 367843 = 551765) B551765
theorem B695569 : Blo 323837 695569 := bstep (se 2 (by rfl) ⟨260838, by rfl⟩ : syracuseStep 695569 = 521677) B521677
theorem B466241 : Blo 323837 466241 := bstep (se 2 (by rfl) ⟨174840, by rfl⟩ : syracuseStep 466241 = 349681) B349681
theorem B367987 : Blo 323837 367987 := bstep (se 1 (by rfl) ⟨275990, by rfl⟩ : syracuseStep 367987 = 551981) B551981
theorem B925091 : Blo 323837 925091 := bstep (se 1 (by rfl) ⟨693818, by rfl⟩ : syracuseStep 925091 = 1387637) B1387637
theorem B826787 : Blo 323837 826787 := bstep (se 1 (by rfl) ⟨620090, by rfl⟩ : syracuseStep 826787 = 1240181) B1240181
theorem B466355 : Blo 323837 466355 := bstep (se 1 (by rfl) ⟨349766, by rfl⟩ : syracuseStep 466355 = 699533) B699533
theorem B368131 : Blo 323837 368131 := bstep (se 1 (by rfl) ⟨276098, by rfl⟩ : syracuseStep 368131 = 552197) B552197
theorem B466435 : Blo 323837 466435 := bstep (se 1 (by rfl) ⟨349826, by rfl⟩ : syracuseStep 466435 = 699653) B699653
theorem B728657 : Blo 323837 728657 := bstep (se 2 (by rfl) ⟨273246, by rfl⟩ : syracuseStep 728657 = 546493) B546493
theorem B728675 : Blo 323837 728675 := bstep (se 1 (by rfl) ⟨546506, by rfl⟩ : syracuseStep 728675 = 1093013) B1093013
theorem B925283 : Blo 323837 925283 := bstep (se 1 (by rfl) ⟨693962, by rfl⟩ : syracuseStep 925283 = 1387925) B1387925
theorem B368275 : Blo 323837 368275 := bstep (se 1 (by rfl) ⟨276206, by rfl⟩ : syracuseStep 368275 = 552413) B552413
theorem B1646243 : Blo 323837 1646243 := bstep (se 1 (by rfl) ⟨1234682, by rfl⟩ : syracuseStep 1646243 = 2469365) B2469365
theorem B2465477 : Blo 323837 2465477 := bstep (se 4 (by rfl) ⟨231138, by rfl⟩ : syracuseStep 2465477 = 462277) B462277
theorem B794321 : Blo 323837 794321 := bstep (se 2 (by rfl) ⟨297870, by rfl⟩ : syracuseStep 794321 = 595741) B595741
theorem B1187569 : Blo 323837 1187569 := bstep (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) B890677
theorem B368419 : Blo 323837 368419 := bstep (se 1 (by rfl) ⟨276314, by rfl⟩ : syracuseStep 368419 = 552629) B552629
theorem B4595555 : Blo 323837 4595555 := bstep (se 1 (by rfl) ⟨3446666, by rfl⟩ : syracuseStep 4595555 = 6893333) B6893333
theorem B728945 : Blo 323837 728945 := bstep (se 2 (by rfl) ⟨273354, by rfl⟩ : syracuseStep 728945 = 546709) B546709
theorem B3514225 : Blo 323837 3514225 := bstep (se 2 (by rfl) ⟨1317834, by rfl⟩ : syracuseStep 3514225 = 2635669) B2635669
theorem B728963 : Blo 323837 728963 := bstep (se 1 (by rfl) ⟨546722, by rfl⟩ : syracuseStep 728963 = 1093445) B1093445
theorem B368563 : Blo 323837 368563 := bstep (se 1 (by rfl) ⟨276422, by rfl⟩ : syracuseStep 368563 = 552845) B552845
theorem B1974221 : Blo 323837 1974221 := bstep (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) B740333
theorem B368707 : Blo 323837 368707 := bstep (se 1 (by rfl) ⟨276530, by rfl⟩ : syracuseStep 368707 = 553061) B553061
theorem B729233 : Blo 323837 729233 := bstep (se 2 (by rfl) ⟨273462, by rfl⟩ : syracuseStep 729233 = 546925) B546925
theorem B729251 : Blo 323837 729251 := bstep (se 1 (by rfl) ⟨546938, by rfl⟩ : syracuseStep 729251 = 1093877) B1093877
theorem B794947 : Blo 323837 794947 := bstep (se 1 (by rfl) ⟨596210, by rfl⟩ : syracuseStep 794947 = 1192421) B1192421
theorem B827729 : Blo 323837 827729 := bstep (se 2 (by rfl) ⟨310398, by rfl⟩ : syracuseStep 827729 = 620797) B620797
theorem B827779 : Blo 323837 827779 := bstep (se 1 (by rfl) ⟨620834, by rfl⟩ : syracuseStep 827779 = 1241669) B1241669
theorem B926093 : Blo 323837 926093 := bstep (se 3 (by rfl) ⟨173642, by rfl⟩ : syracuseStep 926093 = 347285) B347285
theorem B729521 : Blo 323837 729521 := bstep (se 2 (by rfl) ⟨273570, by rfl⟩ : syracuseStep 729521 = 547141) B547141
theorem B729539 : Blo 323837 729539 := bstep (se 1 (by rfl) ⟨547154, by rfl⟩ : syracuseStep 729539 = 1094309) B1094309
theorem B1647053 : Blo 323837 1647053 := bstep (se 3 (by rfl) ⟨308822, by rfl⟩ : syracuseStep 1647053 = 617645) B617645
theorem B827921 : Blo 323837 827921 := bstep (se 2 (by rfl) ⟨310470, by rfl⟩ : syracuseStep 827921 = 620941) B620941
theorem B926275 : Blo 323837 926275 := bstep (se 1 (by rfl) ⟨694706, by rfl⟩ : syracuseStep 926275 = 1389413) B1389413
theorem B729809 : Blo 323837 729809 := bstep (se 2 (by rfl) ⟨273678, by rfl⟩ : syracuseStep 729809 = 547357) B547357
theorem B729827 : Blo 323837 729827 := bstep (se 1 (by rfl) ⟨547370, by rfl⟩ : syracuseStep 729827 = 1094741) B1094741
theorem B1188593 : Blo 323837 1188593 := bstep (se 2 (by rfl) ⟨445722, by rfl⟩ : syracuseStep 1188593 = 891445) B891445
theorem B467731 : Blo 323837 467731 := bstep (se 1 (by rfl) ⟨350798, by rfl⟩ : syracuseStep 467731 = 701597) B701597
theorem B1254179 : Blo 323837 1254179 := bstep (se 1 (by rfl) ⟨940634, by rfl⟩ : syracuseStep 1254179 = 1881269) B1881269
theorem B664433 : Blo 323837 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B664529 : Blo 323837 664529 := bstep (se 2 (by rfl) ⟨249198, by rfl⟩ : syracuseStep 664529 = 498397) B498397
theorem B730097 : Blo 323837 730097 := bstep (se 2 (by rfl) ⟨273786, by rfl⟩ : syracuseStep 730097 = 547573) B547573
theorem B730115 : Blo 323837 730115 := bstep (se 1 (by rfl) ⟨547586, by rfl⟩ : syracuseStep 730115 = 1095173) B1095173
theorem B926765 : Blo 323837 926765 := bstep (se 3 (by rfl) ⟨173768, by rfl⟩ : syracuseStep 926765 = 347537) B347537
theorem B4170851 : Blo 323837 4170851 := bstep (se 1 (by rfl) ⟨3128138, by rfl⟩ : syracuseStep 4170851 = 6256277) B6256277
theorem B697585 : Blo 323837 697585 := bstep (se 2 (by rfl) ⟨261594, by rfl⟩ : syracuseStep 697585 = 523189) B523189
theorem B730385 : Blo 323837 730385 := bstep (se 2 (by rfl) ⟨273894, by rfl⟩ : syracuseStep 730385 = 547789) B547789
theorem B730403 : Blo 323837 730403 := bstep (se 1 (by rfl) ⟨547802, by rfl⟩ : syracuseStep 730403 = 1095605) B1095605
theorem B828913 : Blo 323837 828913 := bstep (se 2 (by rfl) ⟨310842, by rfl⟩ : syracuseStep 828913 = 621685) B621685
theorem B730673 : Blo 323837 730673 := bstep (se 2 (by rfl) ⟨274002, by rfl⟩ : syracuseStep 730673 = 548005) B548005
theorem B730691 : Blo 323837 730691 := bstep (se 1 (by rfl) ⟨548018, by rfl⟩ : syracuseStep 730691 = 1096037) B1096037
theorem B697987 : Blo 323837 697987 := bstep (se 1 (by rfl) ⟨523490, by rfl⟩ : syracuseStep 697987 = 1046981) B1046981
theorem B1844963 : Blo 323837 1844963 := bstep (se 1 (by rfl) ⟨1383722, by rfl⟩ : syracuseStep 1844963 = 2767445) B2767445
theorem B829187 : Blo 323837 829187 := bstep (se 1 (by rfl) ⟨621890, by rfl⟩ : syracuseStep 829187 = 1243781) B1243781
theorem B730961 : Blo 323837 730961 := bstep (se 2 (by rfl) ⟨274110, by rfl⟩ : syracuseStep 730961 = 548221) B548221
theorem B730979 : Blo 323837 730979 := bstep (se 1 (by rfl) ⟨548234, by rfl⟩ : syracuseStep 730979 = 1096469) B1096469
theorem B2795363 : Blo 323837 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B567155 : Blo 323837 567155 := bstep (se 1 (by rfl) ⟨425366, by rfl⟩ : syracuseStep 567155 = 850733) B850733
theorem B829379 : Blo 323837 829379 := bstep (se 1 (by rfl) ⟨622034, by rfl⟩ : syracuseStep 829379 = 1244069) B1244069
theorem B993293 : Blo 323837 993293 := bstep (se 3 (by rfl) ⟨186242, by rfl⟩ : syracuseStep 993293 = 372485) B372485
theorem B731249 : Blo 323837 731249 := bstep (se 2 (by rfl) ⟨274218, by rfl⟩ : syracuseStep 731249 = 548437) B548437
theorem B731267 : Blo 323837 731267 := bstep (se 1 (by rfl) ⟨548450, by rfl⟩ : syracuseStep 731267 = 1096901) B1096901
theorem B8890565 : Blo 323837 8890565 := bstep (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) B1666981
theorem B927949 : Blo 323837 927949 := bstep (se 3 (by rfl) ⟨173990, by rfl⟩ : syracuseStep 927949 = 347981) B347981
theorem B1976561 : Blo 323837 1976561 := bstep (se 2 (by rfl) ⟨741210, by rfl⟩ : syracuseStep 1976561 = 1482421) B1482421
theorem B731537 : Blo 323837 731537 := bstep (se 2 (by rfl) ⟨274326, by rfl⟩ : syracuseStep 731537 = 548653) B548653
theorem B731555 : Blo 323837 731555 := bstep (se 1 (by rfl) ⟨548666, by rfl⟩ : syracuseStep 731555 = 1097333) B1097333
theorem B731825 : Blo 323837 731825 := bstep (se 2 (by rfl) ⟨274434, by rfl⟩ : syracuseStep 731825 = 548869) B548869
theorem B731843 : Blo 323837 731843 := bstep (se 1 (by rfl) ⟨548882, by rfl⟩ : syracuseStep 731843 = 1097765) B1097765
theorem B1387277 : Blo 323837 1387277 := bstep (se 3 (by rfl) ⟨260114, by rfl⟩ : syracuseStep 1387277 = 520229) B520229
theorem B1092557 : Blo 323837 1092557 := bstep (se 3 (by rfl) ⟨204854, by rfl⟩ : syracuseStep 1092557 = 409709) B409709
theorem B732113 : Blo 323837 732113 := bstep (se 2 (by rfl) ⟨274542, by rfl⟩ : syracuseStep 732113 = 549085) B549085
theorem B732131 : Blo 323837 732131 := bstep (se 1 (by rfl) ⟨549098, by rfl⟩ : syracuseStep 732131 = 1098197) B1098197
theorem B2108429 : Blo 323837 2108429 := bstep (se 3 (by rfl) ⟨395330, by rfl⟩ : syracuseStep 2108429 = 790661) B790661
theorem B699491 : Blo 323837 699491 := bstep (se 1 (by rfl) ⟨524618, by rfl⟩ : syracuseStep 699491 = 1049237) B1049237
theorem B732401 : Blo 323837 732401 := bstep (se 2 (by rfl) ⟨274650, by rfl⟩ : syracuseStep 732401 = 549301) B549301
theorem B929009 : Blo 323837 929009 := bstep (se 2 (by rfl) ⟨348378, by rfl⟩ : syracuseStep 929009 = 696757) B696757
theorem B732419 : Blo 323837 732419 := bstep (se 1 (by rfl) ⟨549314, by rfl⟩ : syracuseStep 732419 = 1098629) B1098629
theorem B10595605 : Blo 323837 10595605 := bstep (se 6 (by rfl) ⟨248334, by rfl⟩ : syracuseStep 10595605 = 496669) B496669
theorem B1649969 : Blo 323837 1649969 := bstep (se 2 (by rfl) ⟨618738, by rfl⟩ : syracuseStep 1649969 = 1237477) B1237477
theorem B601553 : Blo 323837 601553 := bstep (se 2 (by rfl) ⟨225582, by rfl⟩ : syracuseStep 601553 = 451165) B451165
theorem B994801 : Blo 323837 994801 := bstep (se 2 (by rfl) ⟨373050, by rfl⟩ : syracuseStep 994801 = 746101) B746101
theorem B732689 : Blo 323837 732689 := bstep (se 2 (by rfl) ⟨274758, by rfl⟩ : syracuseStep 732689 = 549517) B549517
theorem B732707 : Blo 323837 732707 := bstep (se 1 (by rfl) ⟨549530, by rfl⟩ : syracuseStep 732707 = 1099061) B1099061
theorem B1093229 : Blo 323837 1093229 := bstep (se 3 (by rfl) ⟨204980, by rfl⟩ : syracuseStep 1093229 = 409961) B409961
theorem B4763249 : Blo 323837 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B1093283 : Blo 323837 1093283 := bstep (se 1 (by rfl) ⟨819962, by rfl⟩ : syracuseStep 1093283 = 1639925) B1639925
theorem B732977 : Blo 323837 732977 := bstep (se 2 (by rfl) ⟨274866, by rfl⟩ : syracuseStep 732977 = 549733) B549733
theorem B1322801 : Blo 323837 1322801 := bstep (se 2 (by rfl) ⟨496050, by rfl⟩ : syracuseStep 1322801 = 992101) B992101
theorem B732995 : Blo 323837 732995 := bstep (se 1 (by rfl) ⟨549746, by rfl⟩ : syracuseStep 732995 = 1099493) B1099493
theorem B3977059 : Blo 323837 3977059 := bstep (se 1 (by rfl) ⟨2982794, by rfl⟩ : syracuseStep 3977059 = 5965589) B5965589
theorem B929681 : Blo 323837 929681 := bstep (se 2 (by rfl) ⟨348630, by rfl⟩ : syracuseStep 929681 = 697261) B697261
theorem B1093553 : Blo 323837 1093553 := bstep (se 2 (by rfl) ⟨410082, by rfl⟩ : syracuseStep 1093553 = 820165) B820165
theorem B536611 : Blo 323837 536611 := bstep (se 1 (by rfl) ⟨402458, by rfl⟩ : syracuseStep 536611 = 804917) B804917
theorem B733265 : Blo 323837 733265 := bstep (se 2 (by rfl) ⟨274974, by rfl⟩ : syracuseStep 733265 = 549949) B549949
theorem B733283 : Blo 323837 733283 := bstep (se 1 (by rfl) ⟨549962, by rfl⟩ : syracuseStep 733283 = 1099925) B1099925
theorem B733553 : Blo 323837 733553 := bstep (se 2 (by rfl) ⟨275082, by rfl⟩ : syracuseStep 733553 = 550165) B550165
theorem B733571 : Blo 323837 733571 := bstep (se 1 (by rfl) ⟨550178, by rfl⟩ : syracuseStep 733571 = 1100357) B1100357
theorem B1094093 : Blo 323837 1094093 := bstep (se 3 (by rfl) ⟨205142, by rfl⟩ : syracuseStep 1094093 = 410285) B410285
theorem B1094147 : Blo 323837 1094147 := bstep (se 1 (by rfl) ⟨820610, by rfl⟩ : syracuseStep 1094147 = 1641221) B1641221
theorem B5026445 : Blo 323837 5026445 := bstep (se 3 (by rfl) ⟨942458, by rfl⟩ : syracuseStep 5026445 = 1884917) B1884917
theorem B733841 : Blo 323837 733841 := bstep (se 2 (by rfl) ⟨275190, by rfl⟩ : syracuseStep 733841 = 550381) B550381
theorem B733859 : Blo 323837 733859 := bstep (se 1 (by rfl) ⟨550394, by rfl⟩ : syracuseStep 733859 = 1100789) B1100789
theorem B930467 : Blo 323837 930467 := bstep (se 1 (by rfl) ⟨697850, by rfl⟩ : syracuseStep 930467 = 1395701) B1395701
theorem B4207285 : Blo 323837 4207285 := bstep (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) B394433
theorem B1651427 : Blo 323837 1651427 := bstep (se 1 (by rfl) ⟨1238570, by rfl⟩ : syracuseStep 1651427 = 2477141) B2477141
theorem B1094417 : Blo 323837 1094417 := bstep (se 2 (by rfl) ⟨410406, by rfl⟩ : syracuseStep 1094417 = 820813) B820813
theorem B1848197 : Blo 323837 1848197 := bstep (se 4 (by rfl) ⟨173268, by rfl⟩ : syracuseStep 1848197 = 346537) B346537
theorem B996259 : Blo 323837 996259 := bstep (se 1 (by rfl) ⟨747194, by rfl⟩ : syracuseStep 996259 = 1494389) B1494389
theorem B734129 : Blo 323837 734129 := bstep (se 2 (by rfl) ⟨275298, by rfl⟩ : syracuseStep 734129 = 550597) B550597
theorem B734147 : Blo 323837 734147 := bstep (se 1 (by rfl) ⟨550610, by rfl⟩ : syracuseStep 734147 = 1101221) B1101221
theorem B930797 : Blo 323837 930797 := bstep (se 3 (by rfl) ⟨174524, by rfl⟩ : syracuseStep 930797 = 349049) B349049
theorem B832547 : Blo 323837 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B930865 : Blo 323837 930865 := bstep (se 2 (by rfl) ⟨349074, by rfl⟩ : syracuseStep 930865 = 698149) B698149
theorem B734417 : Blo 323837 734417 := bstep (se 2 (by rfl) ⟨275406, by rfl⟩ : syracuseStep 734417 = 550813) B550813
theorem B734435 : Blo 323837 734435 := bstep (se 1 (by rfl) ⟨550826, by rfl⟩ : syracuseStep 734435 = 1101653) B1101653
theorem B10073315 : Blo 323837 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B1094957 : Blo 323837 1094957 := bstep (se 3 (by rfl) ⟨205304, by rfl⟩ : syracuseStep 1094957 = 410609) B410609
theorem B931139 : Blo 323837 931139 := bstep (se 1 (by rfl) ⟨698354, by rfl⟩ : syracuseStep 931139 = 1396709) B1396709
theorem B1848653 : Blo 323837 1848653 := bstep (se 3 (by rfl) ⟨346622, by rfl⟩ : syracuseStep 1848653 = 693245) B693245
theorem B1095011 : Blo 323837 1095011 := bstep (se 1 (by rfl) ⟨821258, by rfl⟩ : syracuseStep 1095011 = 1642517) B1642517
theorem B2471309 : Blo 323837 2471309 := bstep (se 3 (by rfl) ⟨463370, by rfl⟩ : syracuseStep 2471309 = 926741) B926741
theorem B734705 : Blo 323837 734705 := bstep (se 2 (by rfl) ⟨275514, by rfl⟩ : syracuseStep 734705 = 551029) B551029
theorem B734723 : Blo 323837 734723 := bstep (se 1 (by rfl) ⟨551042, by rfl⟩ : syracuseStep 734723 = 1102085) B1102085
theorem B1652237 : Blo 323837 1652237 := bstep (se 3 (by rfl) ⟨309794, by rfl⟩ : syracuseStep 1652237 = 619589) B619589
theorem B1095281 : Blo 323837 1095281 := bstep (se 2 (by rfl) ⟨410730, by rfl⟩ : syracuseStep 1095281 = 821461) B821461
theorem B734993 : Blo 323837 734993 := bstep (se 2 (by rfl) ⟨275622, by rfl⟩ : syracuseStep 734993 = 551245) B551245
theorem B735011 : Blo 323837 735011 := bstep (se 1 (by rfl) ⟨551258, by rfl⟩ : syracuseStep 735011 = 1102517) B1102517
theorem B1390385 : Blo 323837 1390385 := bstep (se 2 (by rfl) ⟨521394, by rfl⟩ : syracuseStep 1390385 = 1042789) B1042789
theorem B440273 : Blo 323837 440273 := bstep (se 2 (by rfl) ⟨165102, by rfl⟩ : syracuseStep 440273 = 330205) B330205
theorem B735281 : Blo 323837 735281 := bstep (se 2 (by rfl) ⟨275730, by rfl⟩ : syracuseStep 735281 = 551461) B551461
theorem B735299 : Blo 323837 735299 := bstep (se 1 (by rfl) ⟨551474, by rfl⟩ : syracuseStep 735299 = 1102949) B1102949
theorem B1095821 : Blo 323837 1095821 := bstep (se 3 (by rfl) ⟨205466, by rfl⟩ : syracuseStep 1095821 = 410933) B410933
theorem B931981 : Blo 323837 931981 := bstep (se 3 (by rfl) ⟨174746, by rfl⟩ : syracuseStep 931981 = 349493) B349493
theorem B1095875 : Blo 323837 1095875 := bstep (se 1 (by rfl) ⟨821906, by rfl⟩ : syracuseStep 1095875 = 1643813) B1643813
theorem B932141 : Blo 323837 932141 := bstep (se 3 (by rfl) ⟨174776, by rfl⟩ : syracuseStep 932141 = 349553) B349553
theorem B735569 : Blo 323837 735569 := bstep (se 2 (by rfl) ⟨275838, by rfl⟩ : syracuseStep 735569 = 551677) B551677
theorem B735587 : Blo 323837 735587 := bstep (se 1 (by rfl) ⟨551690, by rfl⟩ : syracuseStep 735587 = 1103381) B1103381
theorem B1325425 : Blo 323837 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B1325489 : Blo 323837 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B1391053 : Blo 323837 1391053 := bstep (se 3 (by rfl) ⟨260822, by rfl⟩ : syracuseStep 1391053 = 521645) B521645
theorem B1096145 : Blo 323837 1096145 := bstep (se 2 (by rfl) ⟨411054, by rfl⟩ : syracuseStep 1096145 = 822109) B822109
theorem B375251 : Blo 323837 375251 := bstep (se 1 (by rfl) ⟨281438, by rfl⟩ : syracuseStep 375251 = 562877) B562877
theorem B932323 : Blo 323837 932323 := bstep (se 1 (by rfl) ⟨699242, by rfl⟩ : syracuseStep 932323 = 1398485) B1398485
theorem B735857 : Blo 323837 735857 := bstep (se 2 (by rfl) ⟨275946, by rfl⟩ : syracuseStep 735857 = 551893) B551893
theorem B735875 : Blo 323837 735875 := bstep (se 1 (by rfl) ⟨551906, by rfl⟩ : syracuseStep 735875 = 1103813) B1103813
theorem B2800453 : Blo 323837 2800453 := bstep (se 4 (by rfl) ⟨262542, by rfl⟩ : syracuseStep 2800453 = 525085) B525085
theorem B736145 : Blo 323837 736145 := bstep (se 2 (by rfl) ⟨276054, by rfl⟩ : syracuseStep 736145 = 552109) B552109
theorem B736163 : Blo 323837 736163 := bstep (se 1 (by rfl) ⟨552122, by rfl⟩ : syracuseStep 736163 = 1104245) B1104245
theorem B1096685 : Blo 323837 1096685 := bstep (se 3 (by rfl) ⟨205628, by rfl⟩ : syracuseStep 1096685 = 411257) B411257
theorem B1096739 : Blo 323837 1096739 := bstep (se 1 (by rfl) ⟨822554, by rfl⟩ : syracuseStep 1096739 = 1645109) B1645109
theorem B1391651 : Blo 323837 1391651 := bstep (se 1 (by rfl) ⟨1043738, by rfl⟩ : syracuseStep 1391651 = 2087477) B2087477
theorem B736433 : Blo 323837 736433 := bstep (se 2 (by rfl) ⟨276162, by rfl⟩ : syracuseStep 736433 = 552325) B552325
theorem B736451 : Blo 323837 736451 := bstep (se 1 (by rfl) ⟨552338, by rfl⟩ : syracuseStep 736451 = 1104677) B1104677
theorem B1097009 : Blo 323837 1097009 := bstep (se 2 (by rfl) ⟨411378, by rfl⟩ : syracuseStep 1097009 = 822757) B822757
theorem B736721 : Blo 323837 736721 := bstep (se 2 (by rfl) ⟨276270, by rfl⟩ : syracuseStep 736721 = 552541) B552541
theorem B736739 : Blo 323837 736739 := bstep (se 1 (by rfl) ⟨552554, by rfl⟩ : syracuseStep 736739 = 1105109) B1105109
theorem B4472333 : Blo 323837 4472333 := bstep (se 3 (by rfl) ⟨838562, by rfl⟩ : syracuseStep 4472333 = 1677125) B1677125
theorem B1261261 : Blo 323837 1261261 := bstep (se 3 (by rfl) ⟨236486, by rfl⟩ : syracuseStep 1261261 = 472973) B472973
theorem B737009 : Blo 323837 737009 := bstep (se 2 (by rfl) ⟨276378, by rfl⟩ : syracuseStep 737009 = 552757) B552757
theorem B737027 : Blo 323837 737027 := bstep (se 1 (by rfl) ⟨552770, by rfl⟩ : syracuseStep 737027 = 1105541) B1105541
theorem B1097549 : Blo 323837 1097549 := bstep (se 3 (by rfl) ⟨205790, by rfl⟩ : syracuseStep 1097549 = 411581) B411581
theorem B1097603 : Blo 323837 1097603 := bstep (se 1 (by rfl) ⟨823202, by rfl⟩ : syracuseStep 1097603 = 1646405) B1646405
theorem B737297 : Blo 323837 737297 := bstep (se 2 (by rfl) ⟨276486, by rfl⟩ : syracuseStep 737297 = 552973) B552973
theorem B737315 : Blo 323837 737315 := bstep (se 1 (by rfl) ⟨552986, by rfl⟩ : syracuseStep 737315 = 1105973) B1105973
theorem B1097873 : Blo 323837 1097873 := bstep (se 2 (by rfl) ⟨411702, by rfl⟩ : syracuseStep 1097873 = 823405) B823405
theorem B1851569 : Blo 323837 1851569 := bstep (se 2 (by rfl) ⟨694338, by rfl⟩ : syracuseStep 1851569 = 1388677) B1388677
theorem B2474225 : Blo 323837 2474225 := bstep (se 2 (by rfl) ⟨927834, by rfl⟩ : syracuseStep 2474225 = 1855669) B1855669
theorem B737585 : Blo 323837 737585 := bstep (se 2 (by rfl) ⟨276594, by rfl⟩ : syracuseStep 737585 = 553189) B553189
theorem B737603 : Blo 323837 737603 := bstep (se 1 (by rfl) ⟨553202, by rfl⟩ : syracuseStep 737603 = 1106405) B1106405
theorem B1982789 : Blo 323837 1982789 := bstep (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) B371773
theorem B1655153 : Blo 323837 1655153 := bstep (se 2 (by rfl) ⟨620682, by rfl⟩ : syracuseStep 1655153 = 1241365) B1241365
theorem B4309361 : Blo 323837 4309361 := bstep (se 2 (by rfl) ⟨1616010, by rfl⟩ : syracuseStep 4309361 = 3232021) B3232021
theorem B410179 : Blo 323837 410179 := bstep (se 1 (by rfl) ⟨307634, by rfl⟩ : syracuseStep 410179 = 615269) B615269
theorem B442993 : Blo 323837 442993 := bstep (se 2 (by rfl) ⟨166122, by rfl⟩ : syracuseStep 442993 = 332245) B332245
theorem B443009 : Blo 323837 443009 := bstep (se 2 (by rfl) ⟨166128, by rfl⟩ : syracuseStep 443009 = 332257) B332257
theorem B410275 : Blo 323837 410275 := bstep (se 1 (by rfl) ⟨307706, by rfl⟩ : syracuseStep 410275 = 615413) B615413
theorem B1098413 : Blo 323837 1098413 := bstep (se 3 (by rfl) ⟨205952, by rfl⟩ : syracuseStep 1098413 = 411905) B411905
theorem B2081477 : Blo 323837 2081477 := bstep (se 4 (by rfl) ⟨195138, by rfl⟩ : syracuseStep 2081477 = 390277) B390277
theorem B1098467 : Blo 323837 1098467 := bstep (se 1 (by rfl) ⟨823850, by rfl⟩ : syracuseStep 1098467 = 1647701) B1647701
theorem B1098737 : Blo 323837 1098737 := bstep (se 2 (by rfl) ⟨412026, by rfl⟩ : syracuseStep 1098737 = 824053) B824053
theorem B410771 : Blo 323837 410771 := bstep (se 1 (by rfl) ⟨308078, by rfl⟩ : syracuseStep 410771 = 616157) B616157
theorem B1099277 : Blo 323837 1099277 := bstep (se 3 (by rfl) ⟨206114, by rfl⟩ : syracuseStep 1099277 = 412229) B412229
theorem B935441 : Blo 323837 935441 := bstep (se 2 (by rfl) ⟨350790, by rfl⟩ : syracuseStep 935441 = 701581) B701581
theorem B1099331 : Blo 323837 1099331 := bstep (se 1 (by rfl) ⟨824498, by rfl⟩ : syracuseStep 1099331 = 1648997) B1648997
theorem B1754693 : Blo 323837 1754693 := bstep (se 4 (by rfl) ⟨164502, by rfl⟩ : syracuseStep 1754693 = 329005) B329005
theorem B1853027 : Blo 323837 1853027 := bstep (se 1 (by rfl) ⟨1389770, by rfl⟩ : syracuseStep 1853027 = 2779541) B2779541
theorem B1656611 : Blo 323837 1656611 := bstep (se 1 (by rfl) ⟨1242458, by rfl⟩ : syracuseStep 1656611 = 2484917) B2484917
theorem B1099601 : Blo 323837 1099601 := bstep (se 2 (by rfl) ⟨412350, by rfl⟩ : syracuseStep 1099601 = 824701) B824701
theorem B411475 : Blo 323837 411475 := bstep (se 1 (by rfl) ⟨308606, by rfl⟩ : syracuseStep 411475 = 617213) B617213
theorem B411571 : Blo 323837 411571 := bstep (se 1 (by rfl) ⟨308678, by rfl⟩ : syracuseStep 411571 = 617357) B617357
theorem B1001521 : Blo 323837 1001521 := bstep (se 2 (by rfl) ⟨375570, by rfl⟩ : syracuseStep 1001521 = 751141) B751141
theorem B1230947 : Blo 323837 1230947 := bstep (se 1 (by rfl) ⟨923210, by rfl⟩ : syracuseStep 1230947 = 1846421) B1846421
theorem B739523 : Blo 323837 739523 := bstep (se 1 (by rfl) ⟨554642, by rfl⟩ : syracuseStep 739523 = 1109285) B1109285
theorem B2771171 : Blo 323837 2771171 := bstep (se 1 (by rfl) ⟨2078378, by rfl⟩ : syracuseStep 2771171 = 4156757) B4156757
theorem B3754225 : Blo 323837 3754225 := bstep (se 2 (by rfl) ⟨1407834, by rfl⟩ : syracuseStep 3754225 = 2815669) B2815669
theorem B1755427 : Blo 323837 1755427 := bstep (se 1 (by rfl) ⟨1316570, by rfl⟩ : syracuseStep 1755427 = 2633141) B2633141
theorem B1100141 : Blo 323837 1100141 := bstep (se 3 (by rfl) ⟨206276, by rfl⟩ : syracuseStep 1100141 = 412553) B412553
theorem B412067 : Blo 323837 412067 := bstep (se 1 (by rfl) ⟨309050, by rfl⟩ : syracuseStep 412067 = 618101) B618101
theorem B1100195 : Blo 323837 1100195 := bstep (se 1 (by rfl) ⟨825146, by rfl⟩ : syracuseStep 1100195 = 1650293) B1650293
theorem B346691 : Blo 323837 346691 := bstep (se 1 (by rfl) ⟨260018, by rfl⟩ : syracuseStep 346691 = 520037) B520037
theorem B1854029 : Blo 323837 1854029 := bstep (se 3 (by rfl) ⟨347630, by rfl⟩ : syracuseStep 1854029 = 695261) B695261
theorem B1657421 : Blo 323837 1657421 := bstep (se 3 (by rfl) ⟨310766, by rfl⟩ : syracuseStep 1657421 = 621533) B621533
theorem B2083427 : Blo 323837 2083427 := bstep (se 1 (by rfl) ⟨1562570, by rfl⟩ : syracuseStep 2083427 = 3125141) B3125141
theorem B1100465 : Blo 323837 1100465 := bstep (se 2 (by rfl) ⟨412674, by rfl⟩ : syracuseStep 1100465 = 825349) B825349
theorem B1395427 : Blo 323837 1395427 := bstep (se 1 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 1395427 = 2093141) B2093141
theorem B2018125 : Blo 323837 2018125 := bstep (se 3 (by rfl) ⟨378398, by rfl⟩ : syracuseStep 2018125 = 756797) B756797
theorem B1231949 : Blo 323837 1231949 := bstep (se 3 (by rfl) ⟨230990, by rfl⟩ : syracuseStep 1231949 = 461981) B461981
theorem B412771 : Blo 323837 412771 := bstep (se 1 (by rfl) ⟨309578, by rfl⟩ : syracuseStep 412771 = 619157) B619157
theorem B412867 : Blo 323837 412867 := bstep (se 1 (by rfl) ⟨309650, by rfl⟩ : syracuseStep 412867 = 619301) B619301
theorem B1101005 : Blo 323837 1101005 := bstep (se 3 (by rfl) ⟨206438, by rfl⟩ : syracuseStep 1101005 = 412877) B412877
theorem B1101059 : Blo 323837 1101059 := bstep (se 1 (by rfl) ⟨825794, by rfl⟩ : syracuseStep 1101059 = 1651589) B1651589
theorem B8539505 : Blo 323837 8539505 := bstep (se 2 (by rfl) ⟨3202314, by rfl⟩ : syracuseStep 8539505 = 6404629) B6404629
theorem B2641349 : Blo 323837 2641349 := bstep (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) B495253
theorem B1101329 : Blo 323837 1101329 := bstep (se 2 (by rfl) ⟨412998, by rfl⟩ : syracuseStep 1101329 = 825997) B825997
theorem B347699 : Blo 323837 347699 := bstep (se 1 (by rfl) ⟨260774, by rfl⟩ : syracuseStep 347699 = 521549) B521549
theorem B413363 : Blo 323837 413363 := bstep (se 1 (by rfl) ⟨310022, by rfl⟩ : syracuseStep 413363 = 620045) B620045
theorem B741155 : Blo 323837 741155 := bstep (se 1 (by rfl) ⟨555866, by rfl⟩ : syracuseStep 741155 = 1111733) B1111733
theorem B1101869 : Blo 323837 1101869 := bstep (se 3 (by rfl) ⟨206600, by rfl⟩ : syracuseStep 1101869 = 413201) B413201
theorem B1101923 : Blo 323837 1101923 := bstep (se 1 (by rfl) ⟨826442, by rfl⟩ : syracuseStep 1101923 = 1652885) B1652885
theorem B1102193 : Blo 323837 1102193 := bstep (se 2 (by rfl) ⟨413322, by rfl⟩ : syracuseStep 1102193 = 826645) B826645
theorem B414067 : Blo 323837 414067 := bstep (se 1 (by rfl) ⟨310550, by rfl⟩ : syracuseStep 414067 = 621101) B621101
theorem B1560995 : Blo 323837 1560995 := bstep (se 1 (by rfl) ⟨1170746, by rfl⟩ : syracuseStep 1560995 = 2341493) B2341493
theorem B414163 : Blo 323837 414163 := bstep (se 1 (by rfl) ⟨310622, by rfl⟩ : syracuseStep 414163 = 621245) B621245
theorem B1167949 : Blo 323837 1167949 := bstep (se 3 (by rfl) ⟨218990, by rfl⟩ : syracuseStep 1167949 = 437981) B437981
theorem B1397425 : Blo 323837 1397425 := bstep (se 2 (by rfl) ⟨524034, by rfl⟩ : syracuseStep 1397425 = 1048069) B1048069
theorem B1561457 : Blo 323837 1561457 := bstep (se 2 (by rfl) ⟨585546, by rfl⟩ : syracuseStep 1561457 = 1171093) B1171093
theorem B1102733 : Blo 323837 1102733 := bstep (se 3 (by rfl) ⟨206762, by rfl⟩ : syracuseStep 1102733 = 413525) B413525
theorem B1102787 : Blo 323837 1102787 := bstep (se 1 (by rfl) ⟨827090, by rfl⟩ : syracuseStep 1102787 = 1654181) B1654181
theorem B414659 : Blo 323837 414659 := bstep (se 1 (by rfl) ⟨310994, by rfl⟩ : syracuseStep 414659 = 621989) B621989
theorem B349267 : Blo 323837 349267 := bstep (se 1 (by rfl) ⟨261950, by rfl⟩ : syracuseStep 349267 = 523901) B523901
theorem B1234061 : Blo 323837 1234061 := bstep (se 3 (by rfl) ⟨231386, by rfl⟩ : syracuseStep 1234061 = 462773) B462773
theorem B1103057 : Blo 323837 1103057 := bstep (se 2 (by rfl) ⟨413646, by rfl⟩ : syracuseStep 1103057 = 827293) B827293
theorem B3953891 : Blo 323837 3953891 := bstep (se 1 (by rfl) ⟨2965418, by rfl⟩ : syracuseStep 3953891 = 5930837) B5930837
theorem B1037549 : Blo 323837 1037549 := bstep (se 3 (by rfl) ⟨194540, by rfl⟩ : syracuseStep 1037549 = 389081) B389081
theorem B1856945 : Blo 323837 1856945 := bstep (se 2 (by rfl) ⟨696354, by rfl⟩ : syracuseStep 1856945 = 1392709) B1392709
theorem B349715 : Blo 323837 349715 := bstep (se 1 (by rfl) ⟨262286, by rfl⟩ : syracuseStep 349715 = 524573) B524573
theorem B1103597 : Blo 323837 1103597 := bstep (se 3 (by rfl) ⟨206924, by rfl⟩ : syracuseStep 1103597 = 413849) B413849
theorem B546547 : Blo 323837 546547 := bstep (se 1 (by rfl) ⟨409910, by rfl⟩ : syracuseStep 546547 = 819821) B819821
theorem B1103651 : Blo 323837 1103651 := bstep (se 1 (by rfl) ⟨827738, by rfl⟩ : syracuseStep 1103651 = 1655477) B1655477
theorem B546689 : Blo 323837 546689 := bstep (se 2 (by rfl) ⟨205008, by rfl⟩ : syracuseStep 546689 = 410017) B410017
theorem B1234865 : Blo 323837 1234865 := bstep (se 2 (by rfl) ⟨463074, by rfl⟩ : syracuseStep 1234865 = 926149) B926149
theorem B546817 : Blo 323837 546817 := bstep (se 2 (by rfl) ⟨205056, by rfl⟩ : syracuseStep 546817 = 410113) B410113
theorem B546851 : Blo 323837 546851 := bstep (se 1 (by rfl) ⟨410138, by rfl⟩ : syracuseStep 546851 = 820277) B820277
theorem B1103921 : Blo 323837 1103921 := bstep (se 2 (by rfl) ⟨413970, by rfl⟩ : syracuseStep 1103921 = 827941) B827941
theorem B546979 : Blo 323837 546979 := bstep (se 1 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 546979 = 820469) B820469
theorem B2087117 : Blo 323837 2087117 := bstep (se 3 (by rfl) ⟨391334, by rfl⟩ : syracuseStep 2087117 = 782669) B782669
theorem B547121 : Blo 323837 547121 := bstep (se 2 (by rfl) ⟨205170, by rfl⟩ : syracuseStep 547121 = 410341) B410341
theorem B2218373 : Blo 323837 2218373 := bstep (se 4 (by rfl) ⟨207972, by rfl⟩ : syracuseStep 2218373 = 415945) B415945
theorem B678289 : Blo 323837 678289 := bstep (se 2 (by rfl) ⟨254358, by rfl⟩ : syracuseStep 678289 = 508717) B508717
theorem B547249 : Blo 323837 547249 := bstep (se 2 (by rfl) ⟨205218, by rfl⟩ : syracuseStep 547249 = 410437) B410437
theorem B547283 : Blo 323837 547283 := bstep (se 1 (by rfl) ⟨410462, by rfl⟩ : syracuseStep 547283 = 820925) B820925
theorem B1235533 : Blo 323837 1235533 := bstep (se 3 (by rfl) ⟨231662, by rfl⟩ : syracuseStep 1235533 = 463325) B463325
theorem B1104461 : Blo 323837 1104461 := bstep (se 3 (by rfl) ⟨207086, by rfl⟩ : syracuseStep 1104461 = 414173) B414173
theorem B547411 : Blo 323837 547411 := bstep (se 1 (by rfl) ⟨410558, by rfl⟩ : syracuseStep 547411 = 821117) B821117
theorem B1104515 : Blo 323837 1104515 := bstep (se 1 (by rfl) ⟨828386, by rfl⟩ : syracuseStep 1104515 = 1656773) B1656773
theorem B547553 : Blo 323837 547553 := bstep (se 2 (by rfl) ⟨205332, by rfl⟩ : syracuseStep 547553 = 410665) B410665
theorem B547681 : Blo 323837 547681 := bstep (se 2 (by rfl) ⟨205380, by rfl⟩ : syracuseStep 547681 = 410761) B410761
theorem B1858403 : Blo 323837 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B547715 : Blo 323837 547715 := bstep (se 1 (by rfl) ⟨410786, by rfl⟩ : syracuseStep 547715 = 821573) B821573
theorem B1104785 : Blo 323837 1104785 := bstep (se 2 (by rfl) ⟨414294, by rfl⟩ : syracuseStep 1104785 = 828589) B828589
theorem B1039331 : Blo 323837 1039331 := bstep (se 1 (by rfl) ⟨779498, by rfl⟩ : syracuseStep 1039331 = 1558997) B1558997
theorem B547843 : Blo 323837 547843 := bstep (se 1 (by rfl) ⟨410882, by rfl⟩ : syracuseStep 547843 = 821765) B821765
theorem B547985 : Blo 323837 547985 := bstep (se 2 (by rfl) ⟨205494, by rfl⟩ : syracuseStep 547985 = 410989) B410989
theorem B875789 : Blo 323837 875789 := bstep (se 3 (by rfl) ⟨164210, by rfl⟩ : syracuseStep 875789 = 328421) B328421
theorem B548113 : Blo 323837 548113 := bstep (se 2 (by rfl) ⟨205542, by rfl⟩ : syracuseStep 548113 = 411085) B411085
theorem B1891619 : Blo 323837 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B548147 : Blo 323837 548147 := bstep (se 1 (by rfl) ⟨411110, by rfl⟩ : syracuseStep 548147 = 822221) B822221
theorem B875875 : Blo 323837 875875 := bstep (se 1 (by rfl) ⟨656906, by rfl⟩ : syracuseStep 875875 = 1313813) B1313813
theorem B1236323 : Blo 323837 1236323 := bstep (se 1 (by rfl) ⟨927242, by rfl⟩ : syracuseStep 1236323 = 1854485) B1854485
theorem B1105325 : Blo 323837 1105325 := bstep (se 3 (by rfl) ⟨207248, by rfl⟩ : syracuseStep 1105325 = 414497) B414497
theorem B548275 : Blo 323837 548275 := bstep (se 1 (by rfl) ⟨411206, by rfl⟩ : syracuseStep 548275 = 822413) B822413
theorem B1564109 : Blo 323837 1564109 := bstep (se 3 (by rfl) ⟨293270, by rfl⟩ : syracuseStep 1564109 = 586541) B586541
theorem B1105379 : Blo 323837 1105379 := bstep (se 1 (by rfl) ⟨829034, by rfl⟩ : syracuseStep 1105379 = 1658069) B1658069
theorem B548417 : Blo 323837 548417 := bstep (se 2 (by rfl) ⟨205656, by rfl⟩ : syracuseStep 548417 = 411313) B411313
theorem B548545 : Blo 323837 548545 := bstep (se 2 (by rfl) ⟨205704, by rfl⟩ : syracuseStep 548545 = 411409) B411409
theorem B548579 : Blo 323837 548579 := bstep (se 1 (by rfl) ⟨411434, by rfl⟩ : syracuseStep 548579 = 822869) B822869
theorem B3137251 : Blo 323837 3137251 := bstep (se 1 (by rfl) ⟨2352938, by rfl⟩ : syracuseStep 3137251 = 4705877) B4705877
theorem B1105649 : Blo 323837 1105649 := bstep (se 2 (by rfl) ⟨414618, by rfl⟩ : syracuseStep 1105649 = 829237) B829237
theorem B548707 : Blo 323837 548707 := bstep (se 1 (by rfl) ⟨411530, by rfl⟩ : syracuseStep 548707 = 823061) B823061
theorem B778211 : Blo 323837 778211 := bstep (se 1 (by rfl) ⟨583658, by rfl⟩ : syracuseStep 778211 = 1167317) B1167317
theorem B548849 : Blo 323837 548849 := bstep (se 2 (by rfl) ⟨205818, by rfl⟩ : syracuseStep 548849 = 411637) B411637
theorem B1236977 : Blo 323837 1236977 := bstep (se 2 (by rfl) ⟨463866, by rfl⟩ : syracuseStep 1236977 = 927733) B927733
theorem B548977 : Blo 323837 548977 := bstep (se 2 (by rfl) ⟨205866, by rfl⟩ : syracuseStep 548977 = 411733) B411733
theorem B549011 : Blo 323837 549011 := bstep (se 1 (by rfl) ⟨411758, by rfl⟩ : syracuseStep 549011 = 823517) B823517
theorem B418019 : Blo 323837 418019 := bstep (se 1 (by rfl) ⟨313514, by rfl⟩ : syracuseStep 418019 = 627029) B627029
theorem B1106189 : Blo 323837 1106189 := bstep (se 3 (by rfl) ⟨207410, by rfl⟩ : syracuseStep 1106189 = 414821) B414821
theorem B549139 : Blo 323837 549139 := bstep (se 1 (by rfl) ⟨411854, by rfl⟩ : syracuseStep 549139 = 823709) B823709
theorem B1106243 : Blo 323837 1106243 := bstep (se 1 (by rfl) ⟨829682, by rfl⟩ : syracuseStep 1106243 = 1659365) B1659365
theorem B549281 : Blo 323837 549281 := bstep (se 2 (by rfl) ⟨205980, by rfl⟩ : syracuseStep 549281 = 411961) B411961
theorem B549409 : Blo 323837 549409 := bstep (se 2 (by rfl) ⟨206028, by rfl⟩ : syracuseStep 549409 = 412057) B412057
theorem B778787 : Blo 323837 778787 := bstep (se 1 (by rfl) ⟨584090, by rfl⟩ : syracuseStep 778787 = 1168181) B1168181
theorem B549443 : Blo 323837 549443 := bstep (se 1 (by rfl) ⟨412082, by rfl⟩ : syracuseStep 549443 = 824165) B824165
theorem B549571 : Blo 323837 549571 := bstep (se 1 (by rfl) ⟨412178, by rfl⟩ : syracuseStep 549571 = 824357) B824357
theorem B778979 : Blo 323837 778979 := bstep (se 1 (by rfl) ⟨584234, by rfl⟩ : syracuseStep 778979 = 1168469) B1168469
theorem B2450189 : Blo 323837 2450189 := bstep (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) B918821
theorem B615185 : Blo 323837 615185 := bstep (se 2 (by rfl) ⟨230694, by rfl⟩ : syracuseStep 615185 = 461389) B461389
theorem B549713 : Blo 323837 549713 := bstep (se 2 (by rfl) ⟨206142, by rfl⟩ : syracuseStep 549713 = 412285) B412285
theorem B549841 : Blo 323837 549841 := bstep (se 2 (by rfl) ⟨206190, by rfl⟩ : syracuseStep 549841 = 412381) B412381
theorem B549875 : Blo 323837 549875 := bstep (se 1 (by rfl) ⟨412406, by rfl⟩ : syracuseStep 549875 = 824813) B824813
theorem B779267 : Blo 323837 779267 := bstep (se 1 (by rfl) ⟨584450, by rfl⟩ : syracuseStep 779267 = 1168901) B1168901
theorem B1041457 : Blo 323837 1041457 := bstep (se 2 (by rfl) ⟨390546, by rfl⟩ : syracuseStep 1041457 = 781093) B781093
theorem B550003 : Blo 323837 550003 := bstep (se 1 (by rfl) ⟨412502, by rfl⟩ : syracuseStep 550003 = 825005) B825005
theorem B550145 : Blo 323837 550145 := bstep (se 2 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 550145 = 412609) B412609
theorem B1566029 : Blo 323837 1566029 := bstep (se 3 (by rfl) ⟨293630, by rfl⟩ : syracuseStep 1566029 = 587261) B587261
theorem B550273 : Blo 323837 550273 := bstep (se 2 (by rfl) ⟨206352, by rfl⟩ : syracuseStep 550273 = 412705) B412705
theorem B550307 : Blo 323837 550307 := bstep (se 1 (by rfl) ⟨412730, by rfl⟩ : syracuseStep 550307 = 825461) B825461
theorem B1238435 : Blo 323837 1238435 := bstep (se 1 (by rfl) ⟨928826, by rfl⟩ : syracuseStep 1238435 = 1857653) B1857653
theorem B1238449 : Blo 323837 1238449 := bstep (se 2 (by rfl) ⟨464418, by rfl⟩ : syracuseStep 1238449 = 928837) B928837
theorem B1336867 : Blo 323837 1336867 := bstep (se 1 (by rfl) ⟨1002650, by rfl⟩ : syracuseStep 1336867 = 2005301) B2005301
theorem B550435 : Blo 323837 550435 := bstep (se 1 (by rfl) ⟨412826, by rfl⟩ : syracuseStep 550435 = 825653) B825653
theorem B616081 : Blo 323837 616081 := bstep (se 2 (by rfl) ⟨231030, by rfl⟩ : syracuseStep 616081 = 462061) B462061
theorem B550577 : Blo 323837 550577 := bstep (se 2 (by rfl) ⟨206466, by rfl⟩ : syracuseStep 550577 = 412933) B412933
theorem B616241 : Blo 323837 616241 := bstep (se 2 (by rfl) ⟨231090, by rfl⟩ : syracuseStep 616241 = 462181) B462181
theorem B550705 : Blo 323837 550705 := bstep (se 2 (by rfl) ⟨206514, by rfl⟩ : syracuseStep 550705 = 413029) B413029
theorem B550739 : Blo 323837 550739 := bstep (se 1 (by rfl) ⟨413054, by rfl⟩ : syracuseStep 550739 = 826109) B826109
theorem B780209 : Blo 323837 780209 := bstep (se 2 (by rfl) ⟨292578, by rfl⟩ : syracuseStep 780209 = 585157) B585157
theorem B550867 : Blo 323837 550867 := bstep (se 1 (by rfl) ⟨413150, by rfl⟩ : syracuseStep 550867 = 826301) B826301
theorem B551009 : Blo 323837 551009 := bstep (se 2 (by rfl) ⟨206628, by rfl⟩ : syracuseStep 551009 = 413257) B413257
theorem B780401 : Blo 323837 780401 := bstep (se 2 (by rfl) ⟨292650, by rfl⟩ : syracuseStep 780401 = 585301) B585301
theorem B616643 : Blo 323837 616643 := bstep (se 1 (by rfl) ⟨462482, by rfl⟩ : syracuseStep 616643 = 924965) B924965
theorem B3532997 : Blo 323837 3532997 := bstep (se 4 (by rfl) ⟨331218, by rfl⟩ : syracuseStep 3532997 = 662437) B662437
theorem B551137 : Blo 323837 551137 := bstep (se 2 (by rfl) ⟨206676, by rfl⟩ : syracuseStep 551137 = 413353) B413353
theorem B9038051 : Blo 323837 9038051 := bstep (se 1 (by rfl) ⟨6778538, by rfl⟩ : syracuseStep 9038051 = 13557077) B13557077
theorem B551171 : Blo 323837 551171 := bstep (se 1 (by rfl) ⟨413378, by rfl⟩ : syracuseStep 551171 = 826757) B826757
theorem B551299 : Blo 323837 551299 := bstep (se 1 (by rfl) ⟨413474, by rfl⟩ : syracuseStep 551299 = 826949) B826949
theorem B485777 : Blo 323837 485777 := bstep (se 2 (by rfl) ⟨182166, by rfl⟩ : syracuseStep 485777 = 364333) B364333
theorem B485795 : Blo 323837 485795 := bstep (se 1 (by rfl) ⟨364346, by rfl⟩ : syracuseStep 485795 = 728693) B728693
theorem B485825 : Blo 323837 485825 := bstep (se 2 (by rfl) ⟨182184, by rfl⟩ : syracuseStep 485825 = 364369) B364369
theorem B485843 : Blo 323837 485843 := bstep (se 1 (by rfl) ⟨364382, by rfl⟩ : syracuseStep 485843 = 728765) B728765
theorem B485873 : Blo 323837 485873 := bstep (se 2 (by rfl) ⟨182202, by rfl⟩ : syracuseStep 485873 = 364405) B364405
theorem B485891 : Blo 323837 485891 := bstep (se 1 (by rfl) ⟨364418, by rfl⟩ : syracuseStep 485891 = 728837) B728837
theorem B551441 : Blo 323837 551441 := bstep (se 2 (by rfl) ⟨206790, by rfl⟩ : syracuseStep 551441 = 413581) B413581
theorem B485921 : Blo 323837 485921 := bstep (se 2 (by rfl) ⟨182220, by rfl⟩ : syracuseStep 485921 = 364441) B364441
theorem B485939 : Blo 323837 485939 := bstep (se 1 (by rfl) ⟨364454, by rfl⟩ : syracuseStep 485939 = 728909) B728909
theorem B485969 : Blo 323837 485969 := bstep (se 2 (by rfl) ⟨182238, by rfl⟩ : syracuseStep 485969 = 364477) B364477
theorem B485987 : Blo 323837 485987 := bstep (se 1 (by rfl) ⟨364490, by rfl⟩ : syracuseStep 485987 = 728981) B728981
theorem B486017 : Blo 323837 486017 := bstep (se 2 (by rfl) ⟨182256, by rfl⟩ : syracuseStep 486017 = 364513) B364513
theorem B1993349 : Blo 323837 1993349 := bstep (se 4 (by rfl) ⟨186876, by rfl⟩ : syracuseStep 1993349 = 373753) B373753
theorem B551569 : Blo 323837 551569 := bstep (se 2 (by rfl) ⟨206838, by rfl⟩ : syracuseStep 551569 = 413677) B413677
theorem B486035 : Blo 323837 486035 := bstep (se 1 (by rfl) ⟨364526, by rfl⟩ : syracuseStep 486035 = 729053) B729053
theorem B486065 : Blo 323837 486065 := bstep (se 2 (by rfl) ⟨182274, by rfl⟩ : syracuseStep 486065 = 364549) B364549
theorem B551603 : Blo 323837 551603 := bstep (se 1 (by rfl) ⟨413702, by rfl⟩ : syracuseStep 551603 = 827405) B827405
theorem B486083 : Blo 323837 486083 := bstep (se 1 (by rfl) ⟨364562, by rfl⟩ : syracuseStep 486083 = 729125) B729125
theorem B486113 : Blo 323837 486113 := bstep (se 2 (by rfl) ⟨182292, by rfl⟩ : syracuseStep 486113 = 364585) B364585
theorem B486131 : Blo 323837 486131 := bstep (se 1 (by rfl) ⟨364598, by rfl⟩ : syracuseStep 486131 = 729197) B729197
theorem B486161 : Blo 323837 486161 := bstep (se 2 (by rfl) ⟨182310, by rfl⟩ : syracuseStep 486161 = 364621) B364621
theorem B486179 : Blo 323837 486179 := bstep (se 1 (by rfl) ⟨364634, by rfl⟩ : syracuseStep 486179 = 729269) B729269
theorem B551731 : Blo 323837 551731 := bstep (se 1 (by rfl) ⟨413798, by rfl⟩ : syracuseStep 551731 = 827597) B827597
theorem B486209 : Blo 323837 486209 := bstep (se 2 (by rfl) ⟨182328, by rfl⟩ : syracuseStep 486209 = 364657) B364657
theorem B486227 : Blo 323837 486227 := bstep (se 1 (by rfl) ⟨364670, by rfl⟩ : syracuseStep 486227 = 729341) B729341
theorem B1239907 : Blo 323837 1239907 := bstep (se 1 (by rfl) ⟨929930, by rfl⟩ : syracuseStep 1239907 = 1859861) B1859861
theorem B486257 : Blo 323837 486257 := bstep (se 2 (by rfl) ⟨182346, by rfl⟩ : syracuseStep 486257 = 364693) B364693
theorem B781169 : Blo 323837 781169 := bstep (se 2 (by rfl) ⟨292938, by rfl⟩ : syracuseStep 781169 = 585877) B585877
theorem B486275 : Blo 323837 486275 := bstep (se 1 (by rfl) ⟨364706, by rfl⟩ : syracuseStep 486275 = 729413) B729413
theorem B486305 : Blo 323837 486305 := bstep (se 2 (by rfl) ⟨182364, by rfl⟩ : syracuseStep 486305 = 364729) B364729
theorem B486323 : Blo 323837 486323 := bstep (se 1 (by rfl) ⟨364742, by rfl⟩ : syracuseStep 486323 = 729485) B729485
theorem B551873 : Blo 323837 551873 := bstep (se 2 (by rfl) ⟨206952, by rfl⟩ : syracuseStep 551873 = 413905) B413905
theorem B1043405 : Blo 323837 1043405 := bstep (se 3 (by rfl) ⟨195638, by rfl⟩ : syracuseStep 1043405 = 391277) B391277
theorem B486353 : Blo 323837 486353 := bstep (se 2 (by rfl) ⟨182382, by rfl⟩ : syracuseStep 486353 = 364765) B364765
theorem B486371 : Blo 323837 486371 := bstep (se 1 (by rfl) ⟨364778, by rfl⟩ : syracuseStep 486371 = 729557) B729557
theorem B486401 : Blo 323837 486401 := bstep (se 2 (by rfl) ⟨182400, by rfl⟩ : syracuseStep 486401 = 364801) B364801
theorem B519185 : Blo 323837 519185 := bstep (se 2 (by rfl) ⟨194694, by rfl⟩ : syracuseStep 519185 = 389389) B389389
theorem B486419 : Blo 323837 486419 := bstep (se 1 (by rfl) ⟨364814, by rfl⟩ : syracuseStep 486419 = 729629) B729629
theorem B486449 : Blo 323837 486449 := bstep (se 2 (by rfl) ⟨182418, by rfl⟩ : syracuseStep 486449 = 364837) B364837
theorem B552001 : Blo 323837 552001 := bstep (se 2 (by rfl) ⟨207000, by rfl⟩ : syracuseStep 552001 = 414001) B414001
theorem B486467 : Blo 323837 486467 := bstep (se 1 (by rfl) ⟨364850, by rfl⟩ : syracuseStep 486467 = 729701) B729701
theorem B617539 : Blo 323837 617539 := bstep (se 1 (by rfl) ⟨463154, by rfl⟩ : syracuseStep 617539 = 926309) B926309
theorem B1043533 : Blo 323837 1043533 := bstep (se 3 (by rfl) ⟨195662, by rfl⟩ : syracuseStep 1043533 = 391325) B391325
theorem B486497 : Blo 323837 486497 := bstep (se 2 (by rfl) ⟨182436, by rfl⟩ : syracuseStep 486497 = 364873) B364873
theorem B552035 : Blo 323837 552035 := bstep (se 1 (by rfl) ⟨414026, by rfl⟩ : syracuseStep 552035 = 828053) B828053
theorem B486515 : Blo 323837 486515 := bstep (se 1 (by rfl) ⟨364886, by rfl⟩ : syracuseStep 486515 = 729773) B729773
theorem B486545 : Blo 323837 486545 := bstep (se 2 (by rfl) ⟨182454, by rfl⟩ : syracuseStep 486545 = 364909) B364909
theorem B486563 : Blo 323837 486563 := bstep (se 1 (by rfl) ⟨364922, by rfl⟩ : syracuseStep 486563 = 729845) B729845
theorem B486593 : Blo 323837 486593 := bstep (se 2 (by rfl) ⟨182472, by rfl⟩ : syracuseStep 486593 = 364945) B364945
theorem B486611 : Blo 323837 486611 := bstep (se 1 (by rfl) ⟨364958, by rfl⟩ : syracuseStep 486611 = 729917) B729917
theorem B617699 : Blo 323837 617699 := bstep (se 1 (by rfl) ⟨463274, by rfl⟩ : syracuseStep 617699 = 926549) B926549
theorem B552163 : Blo 323837 552163 := bstep (se 1 (by rfl) ⟨414122, by rfl⟩ : syracuseStep 552163 = 828245) B828245
theorem B519409 : Blo 323837 519409 := bstep (se 2 (by rfl) ⟨194778, by rfl⟩ : syracuseStep 519409 = 389557) B389557
theorem B486641 : Blo 323837 486641 := bstep (se 2 (by rfl) ⟨182490, by rfl⟩ : syracuseStep 486641 = 364981) B364981
theorem B486659 : Blo 323837 486659 := bstep (se 1 (by rfl) ⟨364994, by rfl⟩ : syracuseStep 486659 = 729989) B729989
theorem B486689 : Blo 323837 486689 := bstep (se 2 (by rfl) ⟨182508, by rfl⟩ : syracuseStep 486689 = 365017) B365017
theorem B1109297 : Blo 323837 1109297 := bstep (se 2 (by rfl) ⟨415986, by rfl⟩ : syracuseStep 1109297 = 831973) B831973
theorem B519473 : Blo 323837 519473 := bstep (se 2 (by rfl) ⟨194802, by rfl⟩ : syracuseStep 519473 = 389605) B389605
theorem B486707 : Blo 323837 486707 := bstep (se 1 (by rfl) ⟨365030, by rfl⟩ : syracuseStep 486707 = 730061) B730061
theorem B486737 : Blo 323837 486737 := bstep (se 2 (by rfl) ⟨182526, by rfl⟩ : syracuseStep 486737 = 365053) B365053
theorem B486755 : Blo 323837 486755 := bstep (se 1 (by rfl) ⟨365066, by rfl⟩ : syracuseStep 486755 = 730133) B730133
theorem B3140977 : Blo 323837 3140977 := bstep (se 2 (by rfl) ⟨1177866, by rfl⟩ : syracuseStep 3140977 = 2355733) B2355733
theorem B552305 : Blo 323837 552305 := bstep (se 2 (by rfl) ⟨207114, by rfl⟩ : syracuseStep 552305 = 414229) B414229
theorem B486785 : Blo 323837 486785 := bstep (se 2 (by rfl) ⟨182544, by rfl⟩ : syracuseStep 486785 = 365089) B365089
theorem B486803 : Blo 323837 486803 := bstep (se 1 (by rfl) ⟨365102, by rfl⟩ : syracuseStep 486803 = 730205) B730205
theorem B519601 : Blo 323837 519601 := bstep (se 2 (by rfl) ⟨194850, by rfl⟩ : syracuseStep 519601 = 389701) B389701
theorem B486833 : Blo 323837 486833 := bstep (se 2 (by rfl) ⟨182562, by rfl⟩ : syracuseStep 486833 = 365125) B365125
theorem B486851 : Blo 323837 486851 := bstep (se 1 (by rfl) ⟨365138, by rfl⟩ : syracuseStep 486851 = 730277) B730277
theorem B486881 : Blo 323837 486881 := bstep (se 2 (by rfl) ⟨182580, by rfl⟩ : syracuseStep 486881 = 365161) B365161
theorem B552433 : Blo 323837 552433 := bstep (se 2 (by rfl) ⟨207162, by rfl⟩ : syracuseStep 552433 = 414325) B414325
theorem B486899 : Blo 323837 486899 := bstep (se 1 (by rfl) ⟨365174, by rfl⟩ : syracuseStep 486899 = 730349) B730349
theorem B2092549 : Blo 323837 2092549 := bstep (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) B392353
theorem B486929 : Blo 323837 486929 := bstep (se 2 (by rfl) ⟨182598, by rfl⟩ : syracuseStep 486929 = 365197) B365197
theorem B552467 : Blo 323837 552467 := bstep (se 1 (by rfl) ⟨414350, by rfl⟩ : syracuseStep 552467 = 828701) B828701
theorem B486947 : Blo 323837 486947 := bstep (se 1 (by rfl) ⟨365210, by rfl⟩ : syracuseStep 486947 = 730421) B730421
theorem B1764899 : Blo 323837 1764899 := bstep (se 1 (by rfl) ⟨1323674, by rfl⟩ : syracuseStep 1764899 = 2647349) B2647349
theorem B486977 : Blo 323837 486977 := bstep (se 2 (by rfl) ⟨182616, by rfl⟩ : syracuseStep 486977 = 365233) B365233
theorem B486995 : Blo 323837 486995 := bstep (se 1 (by rfl) ⟨365246, by rfl⟩ : syracuseStep 486995 = 730493) B730493
theorem B487025 : Blo 323837 487025 := bstep (se 2 (by rfl) ⟨182634, by rfl⟩ : syracuseStep 487025 = 365269) B365269
theorem B487043 : Blo 323837 487043 := bstep (se 1 (by rfl) ⟨365282, by rfl⟩ : syracuseStep 487043 = 730565) B730565
theorem B552595 : Blo 323837 552595 := bstep (se 1 (by rfl) ⟨414446, by rfl⟩ : syracuseStep 552595 = 828893) B828893
theorem B487073 : Blo 323837 487073 := bstep (se 2 (by rfl) ⟨182652, by rfl⟩ : syracuseStep 487073 = 365305) B365305
theorem B487091 : Blo 323837 487091 := bstep (se 1 (by rfl) ⟨365318, by rfl⟩ : syracuseStep 487091 = 730637) B730637
theorem B749251 : Blo 323837 749251 := bstep (se 1 (by rfl) ⟨561938, by rfl⟩ : syracuseStep 749251 = 1123877) B1123877
theorem B487121 : Blo 323837 487121 := bstep (se 2 (by rfl) ⟨182670, by rfl⟩ : syracuseStep 487121 = 365341) B365341
theorem B487139 : Blo 323837 487139 := bstep (se 1 (by rfl) ⟨365354, by rfl⟩ : syracuseStep 487139 = 730709) B730709
theorem B487169 : Blo 323837 487169 := bstep (se 2 (by rfl) ⟨182688, by rfl⟩ : syracuseStep 487169 = 365377) B365377
theorem B487187 : Blo 323837 487187 := bstep (se 1 (by rfl) ⟨365390, by rfl⟩ : syracuseStep 487187 = 730781) B730781
theorem B552737 : Blo 323837 552737 := bstep (se 2 (by rfl) ⟨207276, by rfl⟩ : syracuseStep 552737 = 414553) B414553
theorem B487217 : Blo 323837 487217 := bstep (se 2 (by rfl) ⟨182706, by rfl⟩ : syracuseStep 487217 = 365413) B365413
theorem B7499573 : Blo 323837 7499573 := bstep (se 5 (by rfl) ⟨351542, by rfl⟩ : syracuseStep 7499573 = 703085) B703085
theorem B487235 : Blo 323837 487235 := bstep (se 1 (by rfl) ⟨365426, by rfl⟩ : syracuseStep 487235 = 730853) B730853
theorem B487265 : Blo 323837 487265 := bstep (se 2 (by rfl) ⟨182724, by rfl⟩ : syracuseStep 487265 = 365449) B365449
theorem B5926769 : Blo 323837 5926769 := bstep (se 2 (by rfl) ⟨2222538, by rfl⟩ : syracuseStep 5926769 = 4445077) B4445077
theorem B487283 : Blo 323837 487283 := bstep (se 1 (by rfl) ⟨365462, by rfl⟩ : syracuseStep 487283 = 730925) B730925
theorem B487313 : Blo 323837 487313 := bstep (se 2 (by rfl) ⟨182742, by rfl⟩ : syracuseStep 487313 = 365485) B365485
theorem B552865 : Blo 323837 552865 := bstep (se 2 (by rfl) ⟨207324, by rfl⟩ : syracuseStep 552865 = 414649) B414649
theorem B487331 : Blo 323837 487331 := bstep (se 1 (by rfl) ⟨365498, by rfl⟩ : syracuseStep 487331 = 730997) B730997
theorem B487361 : Blo 323837 487361 := bstep (se 2 (by rfl) ⟨182760, by rfl⟩ : syracuseStep 487361 = 365521) B365521
theorem B552899 : Blo 323837 552899 := bstep (se 1 (by rfl) ⟨414674, by rfl⟩ : syracuseStep 552899 = 829349) B829349
theorem B487379 : Blo 323837 487379 := bstep (se 1 (by rfl) ⟨365534, by rfl⟩ : syracuseStep 487379 = 731069) B731069
theorem B487409 : Blo 323837 487409 := bstep (se 2 (by rfl) ⟨182778, by rfl⟩ : syracuseStep 487409 = 365557) B365557
theorem B487427 : Blo 323837 487427 := bstep (se 1 (by rfl) ⟨365570, by rfl⟩ : syracuseStep 487427 = 731141) B731141
theorem B487457 : Blo 323837 487457 := bstep (se 2 (by rfl) ⟨182796, by rfl⟩ : syracuseStep 487457 = 365593) B365593
theorem B487475 : Blo 323837 487475 := bstep (se 1 (by rfl) ⟨365606, by rfl⟩ : syracuseStep 487475 = 731213) B731213
theorem B553027 : Blo 323837 553027 := bstep (se 1 (by rfl) ⟨414770, by rfl⟩ : syracuseStep 553027 = 829541) B829541
theorem B487505 : Blo 323837 487505 := bstep (se 2 (by rfl) ⟨182814, by rfl⟩ : syracuseStep 487505 = 365629) B365629
theorem B487523 : Blo 323837 487523 := bstep (se 1 (by rfl) ⟨365642, by rfl⟩ : syracuseStep 487523 = 731285) B731285
theorem B487553 : Blo 323837 487553 := bstep (se 2 (by rfl) ⟨182832, by rfl⟩ : syracuseStep 487553 = 365665) B365665
theorem B487571 : Blo 323837 487571 := bstep (se 1 (by rfl) ⟨365678, by rfl⟩ : syracuseStep 487571 = 731357) B731357
theorem B487601 : Blo 323837 487601 := bstep (se 2 (by rfl) ⟨182850, by rfl⟩ : syracuseStep 487601 = 365701) B365701
theorem B487619 : Blo 323837 487619 := bstep (se 1 (by rfl) ⟨365714, by rfl⟩ : syracuseStep 487619 = 731429) B731429
theorem B553169 : Blo 323837 553169 := bstep (se 2 (by rfl) ⟨207438, by rfl⟩ : syracuseStep 553169 = 414877) B414877
theorem B487649 : Blo 323837 487649 := bstep (se 2 (by rfl) ⟨182868, by rfl⟩ : syracuseStep 487649 = 365737) B365737
theorem B6254819 : Blo 323837 6254819 := bstep (se 1 (by rfl) ⟨4691114, by rfl⟩ : syracuseStep 6254819 = 9382229) B9382229
theorem B487667 : Blo 323837 487667 := bstep (se 1 (by rfl) ⟨365750, by rfl⟩ : syracuseStep 487667 = 731501) B731501
theorem B323843 : Blo 323837 323843 := bstep (se 1 (by rfl) ⟨242882, by rfl⟩ : syracuseStep 323843 = 485765) B485765
theorem B487697 : Blo 323837 487697 := bstep (se 2 (by rfl) ⟨182886, by rfl⟩ : syracuseStep 487697 = 365773) B365773
theorem B618769 : Blo 323837 618769 := bstep (se 2 (by rfl) ⟨232038, by rfl⟩ : syracuseStep 618769 = 464077) B464077
theorem B323859 : Blo 323837 323859 := bstep (se 1 (by rfl) ⟨242894, by rfl⟩ : syracuseStep 323859 = 485789) B485789
theorem B323875 : Blo 323837 323875 := bstep (se 1 (by rfl) ⟨242906, by rfl⟩ : syracuseStep 323875 = 485813) B485813
theorem B487715 : Blo 323837 487715 := bstep (se 1 (by rfl) ⟨365786, by rfl⟩ : syracuseStep 487715 = 731573) B731573
theorem B323891 : Blo 323837 323891 := bstep (se 1 (by rfl) ⟨242918, by rfl⟩ : syracuseStep 323891 = 485837) B485837
theorem B487745 : Blo 323837 487745 := bstep (se 2 (by rfl) ⟨182904, by rfl⟩ : syracuseStep 487745 = 365809) B365809
theorem B323907 : Blo 323837 323907 := bstep (se 1 (by rfl) ⟨242930, by rfl⟩ : syracuseStep 323907 = 485861) B485861
theorem B848195 : Blo 323837 848195 := bstep (se 1 (by rfl) ⟨636146, by rfl⟩ : syracuseStep 848195 = 1272293) B1272293
theorem B323923 : Blo 323837 323923 := bstep (se 1 (by rfl) ⟨242942, by rfl⟩ : syracuseStep 323923 = 485885) B485885
theorem B487763 : Blo 323837 487763 := bstep (se 1 (by rfl) ⟨365822, by rfl⟩ : syracuseStep 487763 = 731645) B731645
theorem B323939 : Blo 323837 323939 := bstep (se 1 (by rfl) ⟨242954, by rfl⟩ : syracuseStep 323939 = 485909) B485909
theorem B487793 : Blo 323837 487793 := bstep (se 2 (by rfl) ⟨182922, by rfl⟩ : syracuseStep 487793 = 365845) B365845
theorem B323955 : Blo 323837 323955 := bstep (se 1 (by rfl) ⟨242966, by rfl⟩ : syracuseStep 323955 = 485933) B485933
theorem B323971 : Blo 323837 323971 := bstep (se 1 (by rfl) ⟨242978, by rfl⟩ : syracuseStep 323971 = 485957) B485957
theorem B487811 : Blo 323837 487811 := bstep (se 1 (by rfl) ⟨365858, by rfl⟩ : syracuseStep 487811 = 731717) B731717
theorem B323987 : Blo 323837 323987 := bstep (se 1 (by rfl) ⟨242990, by rfl⟩ : syracuseStep 323987 = 485981) B485981
theorem B487841 : Blo 323837 487841 := bstep (se 2 (by rfl) ⟨182940, by rfl⟩ : syracuseStep 487841 = 365881) B365881
theorem B324003 : Blo 323837 324003 := bstep (se 1 (by rfl) ⟨243002, by rfl⟩ : syracuseStep 324003 = 486005) B486005
theorem B1929635 : Blo 323837 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B324019 : Blo 323837 324019 := bstep (se 1 (by rfl) ⟨243014, by rfl⟩ : syracuseStep 324019 = 486029) B486029
theorem B487859 : Blo 323837 487859 := bstep (se 1 (by rfl) ⟨365894, by rfl⟩ : syracuseStep 487859 = 731789) B731789
theorem B324035 : Blo 323837 324035 := bstep (se 1 (by rfl) ⟨243026, by rfl⟩ : syracuseStep 324035 = 486053) B486053
theorem B487889 : Blo 323837 487889 := bstep (se 2 (by rfl) ⟨182958, by rfl⟩ : syracuseStep 487889 = 365917) B365917
theorem B324051 : Blo 323837 324051 := bstep (se 1 (by rfl) ⟨243038, by rfl⟩ : syracuseStep 324051 = 486077) B486077
theorem B324067 : Blo 323837 324067 := bstep (se 1 (by rfl) ⟨243050, by rfl⟩ : syracuseStep 324067 = 486101) B486101
theorem B487907 : Blo 323837 487907 := bstep (se 1 (by rfl) ⟨365930, by rfl⟩ : syracuseStep 487907 = 731861) B731861
theorem B324083 : Blo 323837 324083 := bstep (se 1 (by rfl) ⟨243062, by rfl⟩ : syracuseStep 324083 = 486125) B486125
theorem B487937 : Blo 323837 487937 := bstep (se 2 (by rfl) ⟨182976, by rfl⟩ : syracuseStep 487937 = 365953) B365953
theorem B324099 : Blo 323837 324099 := bstep (se 1 (by rfl) ⟨243074, by rfl⟩ : syracuseStep 324099 = 486149) B486149
theorem B324115 : Blo 323837 324115 := bstep (se 1 (by rfl) ⟨243086, by rfl⟩ : syracuseStep 324115 = 486173) B486173
theorem B487955 : Blo 323837 487955 := bstep (se 1 (by rfl) ⟨365966, by rfl⟩ : syracuseStep 487955 = 731933) B731933
theorem B324131 : Blo 323837 324131 := bstep (se 1 (by rfl) ⟨243098, by rfl⟩ : syracuseStep 324131 = 486197) B486197
theorem B487985 : Blo 323837 487985 := bstep (se 2 (by rfl) ⟨182994, by rfl⟩ : syracuseStep 487985 = 365989) B365989
theorem B324147 : Blo 323837 324147 := bstep (se 1 (by rfl) ⟨243110, by rfl⟩ : syracuseStep 324147 = 486221) B486221
theorem B324163 : Blo 323837 324163 := bstep (se 1 (by rfl) ⟨243122, by rfl⟩ : syracuseStep 324163 = 486245) B486245
theorem B488003 : Blo 323837 488003 := bstep (se 1 (by rfl) ⟨366002, by rfl⟩ : syracuseStep 488003 = 732005) B732005
theorem B324179 : Blo 323837 324179 := bstep (se 1 (by rfl) ⟨243134, by rfl⟩ : syracuseStep 324179 = 486269) B486269
theorem B488033 : Blo 323837 488033 := bstep (se 2 (by rfl) ⟨183012, by rfl⟩ : syracuseStep 488033 = 366025) B366025
theorem B324195 : Blo 323837 324195 := bstep (se 1 (by rfl) ⟨243146, by rfl⟩ : syracuseStep 324195 = 486293) B486293
theorem B324211 : Blo 323837 324211 := bstep (se 1 (by rfl) ⟨243158, by rfl⟩ : syracuseStep 324211 = 486317) B486317
theorem B488051 : Blo 323837 488051 := bstep (se 1 (by rfl) ⟨366038, by rfl⟩ : syracuseStep 488051 = 732077) B732077
theorem B324227 : Blo 323837 324227 := bstep (se 1 (by rfl) ⟨243170, by rfl⟩ : syracuseStep 324227 = 486341) B486341
theorem B488081 : Blo 323837 488081 := bstep (se 2 (by rfl) ⟨183030, by rfl⟩ : syracuseStep 488081 = 366061) B366061
theorem B324243 : Blo 323837 324243 := bstep (se 1 (by rfl) ⟨243182, by rfl⟩ : syracuseStep 324243 = 486365) B486365
theorem B324259 : Blo 323837 324259 := bstep (se 1 (by rfl) ⟨243194, by rfl⟩ : syracuseStep 324259 = 486389) B486389
theorem B488099 : Blo 323837 488099 := bstep (se 1 (by rfl) ⟨366074, by rfl⟩ : syracuseStep 488099 = 732149) B732149
theorem B324275 : Blo 323837 324275 := bstep (se 1 (by rfl) ⟨243206, by rfl⟩ : syracuseStep 324275 = 486413) B486413
theorem B488129 : Blo 323837 488129 := bstep (se 2 (by rfl) ⟨183048, by rfl⟩ : syracuseStep 488129 = 366097) B366097
theorem B324291 : Blo 323837 324291 := bstep (se 1 (by rfl) ⟨243218, by rfl⟩ : syracuseStep 324291 = 486437) B486437
theorem B3764933 : Blo 323837 3764933 := bstep (se 4 (by rfl) ⟨352962, by rfl⟩ : syracuseStep 3764933 = 705925) B705925
theorem B324307 : Blo 323837 324307 := bstep (se 1 (by rfl) ⟨243230, by rfl⟩ : syracuseStep 324307 = 486461) B486461
theorem B488147 : Blo 323837 488147 := bstep (se 1 (by rfl) ⟨366110, by rfl⟩ : syracuseStep 488147 = 732221) B732221
theorem B324323 : Blo 323837 324323 := bstep (se 1 (by rfl) ⟨243242, by rfl⟩ : syracuseStep 324323 = 486485) B486485
theorem B488177 : Blo 323837 488177 := bstep (se 2 (by rfl) ⟨183066, by rfl⟩ : syracuseStep 488177 = 366133) B366133
theorem B324339 : Blo 323837 324339 := bstep (se 1 (by rfl) ⟨243254, by rfl⟩ : syracuseStep 324339 = 486509) B486509
theorem B324355 : Blo 323837 324355 := bstep (se 1 (by rfl) ⟨243266, by rfl⟩ : syracuseStep 324355 = 486533) B486533
theorem B488195 : Blo 323837 488195 := bstep (se 1 (by rfl) ⟨366146, by rfl⟩ : syracuseStep 488195 = 732293) B732293
theorem B324371 : Blo 323837 324371 := bstep (se 1 (by rfl) ⟨243278, by rfl⟩ : syracuseStep 324371 = 486557) B486557
theorem B488225 : Blo 323837 488225 := bstep (se 2 (by rfl) ⟨183084, by rfl⟩ : syracuseStep 488225 = 366169) B366169
theorem B324387 : Blo 323837 324387 := bstep (se 1 (by rfl) ⟨243290, by rfl⟩ : syracuseStep 324387 = 486581) B486581
theorem B324403 : Blo 323837 324403 := bstep (se 1 (by rfl) ⟨243302, by rfl⟩ : syracuseStep 324403 = 486605) B486605
theorem B488243 : Blo 323837 488243 := bstep (se 1 (by rfl) ⟨366182, by rfl⟩ : syracuseStep 488243 = 732365) B732365
theorem B324419 : Blo 323837 324419 := bstep (se 1 (by rfl) ⟨243314, by rfl⟩ : syracuseStep 324419 = 486629) B486629
theorem B488273 : Blo 323837 488273 := bstep (se 2 (by rfl) ⟨183102, by rfl⟩ : syracuseStep 488273 = 366205) B366205
theorem B324435 : Blo 323837 324435 := bstep (se 1 (by rfl) ⟨243326, by rfl⟩ : syracuseStep 324435 = 486653) B486653
theorem B324451 : Blo 323837 324451 := bstep (se 1 (by rfl) ⟨243338, by rfl⟩ : syracuseStep 324451 = 486677) B486677
theorem B488291 : Blo 323837 488291 := bstep (se 1 (by rfl) ⟨366218, by rfl⟩ : syracuseStep 488291 = 732437) B732437
theorem B324467 : Blo 323837 324467 := bstep (se 1 (by rfl) ⟨243350, by rfl⟩ : syracuseStep 324467 = 486701) B486701
theorem B488321 : Blo 323837 488321 := bstep (se 2 (by rfl) ⟨183120, by rfl⟩ : syracuseStep 488321 = 366241) B366241
theorem B1045379 : Blo 323837 1045379 := bstep (se 1 (by rfl) ⟨784034, by rfl⟩ : syracuseStep 1045379 = 1568069) B1568069
theorem B324483 : Blo 323837 324483 := bstep (se 1 (by rfl) ⟨243362, by rfl⟩ : syracuseStep 324483 = 486725) B486725
theorem B1766285 : Blo 323837 1766285 := bstep (se 3 (by rfl) ⟨331178, by rfl⟩ : syracuseStep 1766285 = 662357) B662357
theorem B324499 : Blo 323837 324499 := bstep (se 1 (by rfl) ⟨243374, by rfl⟩ : syracuseStep 324499 = 486749) B486749
theorem B488339 : Blo 323837 488339 := bstep (se 1 (by rfl) ⟨366254, by rfl⟩ : syracuseStep 488339 = 732509) B732509
theorem B324515 : Blo 323837 324515 := bstep (se 1 (by rfl) ⟨243386, by rfl⟩ : syracuseStep 324515 = 486773) B486773
theorem B488369 : Blo 323837 488369 := bstep (se 2 (by rfl) ⟨183138, by rfl⟩ : syracuseStep 488369 = 366277) B366277
theorem B324531 : Blo 323837 324531 := bstep (se 1 (by rfl) ⟨243398, by rfl⟩ : syracuseStep 324531 = 486797) B486797
theorem B324547 : Blo 323837 324547 := bstep (se 1 (by rfl) ⟨243410, by rfl⟩ : syracuseStep 324547 = 486821) B486821
theorem B488387 : Blo 323837 488387 := bstep (se 1 (by rfl) ⟨366290, by rfl⟩ : syracuseStep 488387 = 732581) B732581
theorem B324563 : Blo 323837 324563 := bstep (se 1 (by rfl) ⟨243422, by rfl⟩ : syracuseStep 324563 = 486845) B486845
theorem B488417 : Blo 323837 488417 := bstep (se 2 (by rfl) ⟨183156, by rfl⟩ : syracuseStep 488417 = 366313) B366313
theorem B324579 : Blo 323837 324579 := bstep (se 1 (by rfl) ⟨243434, by rfl⟩ : syracuseStep 324579 = 486869) B486869
theorem B324595 : Blo 323837 324595 := bstep (se 1 (by rfl) ⟨243446, by rfl⟩ : syracuseStep 324595 = 486893) B486893
theorem B488435 : Blo 323837 488435 := bstep (se 1 (by rfl) ⟨366326, by rfl⟩ : syracuseStep 488435 = 732653) B732653
theorem B324611 : Blo 323837 324611 := bstep (se 1 (by rfl) ⟨243458, by rfl⟩ : syracuseStep 324611 = 486917) B486917
theorem B1045507 : Blo 323837 1045507 := bstep (se 1 (by rfl) ⟨784130, by rfl⟩ : syracuseStep 1045507 = 1568261) B1568261
theorem B1242125 : Blo 323837 1242125 := bstep (se 3 (by rfl) ⟨232898, by rfl⟩ : syracuseStep 1242125 = 465797) B465797
theorem B488465 : Blo 323837 488465 := bstep (se 2 (by rfl) ⟨183174, by rfl⟩ : syracuseStep 488465 = 366349) B366349
theorem B324627 : Blo 323837 324627 := bstep (se 1 (by rfl) ⟨243470, by rfl⟩ : syracuseStep 324627 = 486941) B486941
theorem B324643 : Blo 323837 324643 := bstep (se 1 (by rfl) ⟨243482, by rfl⟩ : syracuseStep 324643 = 486965) B486965
theorem B488483 : Blo 323837 488483 := bstep (se 1 (by rfl) ⟨366362, by rfl⟩ : syracuseStep 488483 = 732725) B732725
theorem B324659 : Blo 323837 324659 := bstep (se 1 (by rfl) ⟨243494, by rfl⟩ : syracuseStep 324659 = 486989) B486989
theorem B488513 : Blo 323837 488513 := bstep (se 2 (by rfl) ⟨183192, by rfl⟩ : syracuseStep 488513 = 366385) B366385
theorem B324675 : Blo 323837 324675 := bstep (se 1 (by rfl) ⟨243506, by rfl⟩ : syracuseStep 324675 = 487013) B487013
theorem B324691 : Blo 323837 324691 := bstep (se 1 (by rfl) ⟨243518, by rfl⟩ : syracuseStep 324691 = 487037) B487037
theorem B488531 : Blo 323837 488531 := bstep (se 1 (by rfl) ⟨366398, by rfl⟩ : syracuseStep 488531 = 732797) B732797
theorem B324707 : Blo 323837 324707 := bstep (se 1 (by rfl) ⟨243530, by rfl⟩ : syracuseStep 324707 = 487061) B487061
theorem B488561 : Blo 323837 488561 := bstep (se 2 (by rfl) ⟨183210, by rfl⟩ : syracuseStep 488561 = 366421) B366421
theorem B2290801 : Blo 323837 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B324723 : Blo 323837 324723 := bstep (se 1 (by rfl) ⟨243542, by rfl⟩ : syracuseStep 324723 = 487085) B487085
theorem B324739 : Blo 323837 324739 := bstep (se 1 (by rfl) ⟨243554, by rfl⟩ : syracuseStep 324739 = 487109) B487109
theorem B488579 : Blo 323837 488579 := bstep (se 1 (by rfl) ⟨366434, by rfl⟩ : syracuseStep 488579 = 732869) B732869
theorem B1045649 : Blo 323837 1045649 := bstep (se 2 (by rfl) ⟨392118, by rfl⟩ : syracuseStep 1045649 = 784237) B784237
theorem B324755 : Blo 323837 324755 := bstep (se 1 (by rfl) ⟨243566, by rfl⟩ : syracuseStep 324755 = 487133) B487133
theorem B488609 : Blo 323837 488609 := bstep (se 2 (by rfl) ⟨183228, by rfl⟩ : syracuseStep 488609 = 366457) B366457
theorem B324771 : Blo 323837 324771 := bstep (se 1 (by rfl) ⟨243578, by rfl⟩ : syracuseStep 324771 = 487157) B487157
theorem B324787 : Blo 323837 324787 := bstep (se 1 (by rfl) ⟨243590, by rfl⟩ : syracuseStep 324787 = 487181) B487181
theorem B488627 : Blo 323837 488627 := bstep (se 1 (by rfl) ⟨366470, by rfl⟩ : syracuseStep 488627 = 732941) B732941
theorem B324803 : Blo 323837 324803 := bstep (se 1 (by rfl) ⟨243602, by rfl⟩ : syracuseStep 324803 = 487205) B487205
theorem B488657 : Blo 323837 488657 := bstep (se 2 (by rfl) ⟨183246, by rfl⟩ : syracuseStep 488657 = 366493) B366493
theorem B324819 : Blo 323837 324819 := bstep (se 1 (by rfl) ⟨243614, by rfl⟩ : syracuseStep 324819 = 487229) B487229
theorem B324835 : Blo 323837 324835 := bstep (se 1 (by rfl) ⟨243626, by rfl⟩ : syracuseStep 324835 = 487253) B487253
theorem B488675 : Blo 323837 488675 := bstep (se 1 (by rfl) ⟨366506, by rfl⟩ : syracuseStep 488675 = 733013) B733013
theorem B1766627 : Blo 323837 1766627 := bstep (se 1 (by rfl) ⟨1324970, by rfl⟩ : syracuseStep 1766627 = 2649941) B2649941
theorem B324851 : Blo 323837 324851 := bstep (se 1 (by rfl) ⟨243638, by rfl⟩ : syracuseStep 324851 = 487277) B487277
theorem B488705 : Blo 323837 488705 := bstep (se 2 (by rfl) ⟨183264, by rfl⟩ : syracuseStep 488705 = 366529) B366529
theorem B324867 : Blo 323837 324867 := bstep (se 1 (by rfl) ⟨243650, by rfl⟩ : syracuseStep 324867 = 487301) B487301
theorem B1045763 : Blo 323837 1045763 := bstep (se 1 (by rfl) ⟨784322, by rfl⟩ : syracuseStep 1045763 = 1568645) B1568645
theorem B324883 : Blo 323837 324883 := bstep (se 1 (by rfl) ⟨243662, by rfl⟩ : syracuseStep 324883 = 487325) B487325
theorem B488723 : Blo 323837 488723 := bstep (se 1 (by rfl) ⟨366542, by rfl⟩ : syracuseStep 488723 = 733085) B733085
theorem B324899 : Blo 323837 324899 := bstep (se 1 (by rfl) ⟨243674, by rfl⟩ : syracuseStep 324899 = 487349) B487349
theorem B488753 : Blo 323837 488753 := bstep (se 2 (by rfl) ⟨183282, by rfl⟩ : syracuseStep 488753 = 366565) B366565
theorem B619825 : Blo 323837 619825 := bstep (se 2 (by rfl) ⟨232434, by rfl⟩ : syracuseStep 619825 = 464869) B464869
theorem B324915 : Blo 323837 324915 := bstep (se 1 (by rfl) ⟨243686, by rfl⟩ : syracuseStep 324915 = 487373) B487373
theorem B324931 : Blo 323837 324931 := bstep (se 1 (by rfl) ⟨243698, by rfl⟩ : syracuseStep 324931 = 487397) B487397
theorem B488771 : Blo 323837 488771 := bstep (se 1 (by rfl) ⟨366578, by rfl⟩ : syracuseStep 488771 = 733157) B733157
theorem B324947 : Blo 323837 324947 := bstep (se 1 (by rfl) ⟨243710, by rfl⟩ : syracuseStep 324947 = 487421) B487421
theorem B488801 : Blo 323837 488801 := bstep (se 2 (by rfl) ⟨183300, by rfl⟩ : syracuseStep 488801 = 366601) B366601
theorem B324963 : Blo 323837 324963 := bstep (se 1 (by rfl) ⟨243722, by rfl⟩ : syracuseStep 324963 = 487445) B487445
theorem B324979 : Blo 323837 324979 := bstep (se 1 (by rfl) ⟨243734, by rfl⟩ : syracuseStep 324979 = 487469) B487469
theorem B488819 : Blo 323837 488819 := bstep (se 1 (by rfl) ⟨366614, by rfl⟩ : syracuseStep 488819 = 733229) B733229
theorem B324995 : Blo 323837 324995 := bstep (se 1 (by rfl) ⟨243746, by rfl⟩ : syracuseStep 324995 = 487493) B487493
theorem B488849 : Blo 323837 488849 := bstep (se 2 (by rfl) ⟨183318, by rfl⟩ : syracuseStep 488849 = 366637) B366637
theorem B325011 : Blo 323837 325011 := bstep (se 1 (by rfl) ⟨243758, by rfl⟩ : syracuseStep 325011 = 487517) B487517
theorem B325027 : Blo 323837 325027 := bstep (se 1 (by rfl) ⟨243770, by rfl⟩ : syracuseStep 325027 = 487541) B487541
theorem B488867 : Blo 323837 488867 := bstep (se 1 (by rfl) ⟨366650, by rfl⟩ : syracuseStep 488867 = 733301) B733301
theorem B325043 : Blo 323837 325043 := bstep (se 1 (by rfl) ⟨243782, by rfl⟩ : syracuseStep 325043 = 487565) B487565
theorem B521651 : Blo 323837 521651 := bstep (se 1 (by rfl) ⟨391238, by rfl⟩ : syracuseStep 521651 = 782477) B782477
theorem B488897 : Blo 323837 488897 := bstep (se 2 (by rfl) ⟨183336, by rfl⟩ : syracuseStep 488897 = 366673) B366673
theorem B325059 : Blo 323837 325059 := bstep (se 1 (by rfl) ⟨243794, by rfl⟩ : syracuseStep 325059 = 487589) B487589
theorem B325075 : Blo 323837 325075 := bstep (se 1 (by rfl) ⟨243806, by rfl⟩ : syracuseStep 325075 = 487613) B487613
theorem B488915 : Blo 323837 488915 := bstep (se 1 (by rfl) ⟨366686, by rfl⟩ : syracuseStep 488915 = 733373) B733373
theorem B325091 : Blo 323837 325091 := bstep (se 1 (by rfl) ⟨243818, by rfl⟩ : syracuseStep 325091 = 487637) B487637
theorem B488945 : Blo 323837 488945 := bstep (se 2 (by rfl) ⟨183354, by rfl⟩ : syracuseStep 488945 = 366709) B366709
theorem B3536369 : Blo 323837 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B325107 : Blo 323837 325107 := bstep (se 1 (by rfl) ⟨243830, by rfl⟩ : syracuseStep 325107 = 487661) B487661
theorem B325123 : Blo 323837 325123 := bstep (se 1 (by rfl) ⟨243842, by rfl⟩ : syracuseStep 325123 = 487685) B487685
theorem B488963 : Blo 323837 488963 := bstep (se 1 (by rfl) ⟨366722, by rfl⟩ : syracuseStep 488963 = 733445) B733445
theorem B325139 : Blo 323837 325139 := bstep (se 1 (by rfl) ⟨243854, by rfl⟩ : syracuseStep 325139 = 487709) B487709
theorem B488993 : Blo 323837 488993 := bstep (se 2 (by rfl) ⟨183372, by rfl⟩ : syracuseStep 488993 = 366745) B366745
theorem B325155 : Blo 323837 325155 := bstep (se 1 (by rfl) ⟨243866, by rfl⟩ : syracuseStep 325155 = 487733) B487733
theorem B325171 : Blo 323837 325171 := bstep (se 1 (by rfl) ⟨243878, by rfl⟩ : syracuseStep 325171 = 487757) B487757
theorem B489011 : Blo 323837 489011 := bstep (se 1 (by rfl) ⟨366758, by rfl⟩ : syracuseStep 489011 = 733517) B733517
theorem B325187 : Blo 323837 325187 := bstep (se 1 (by rfl) ⟨243890, by rfl⟩ : syracuseStep 325187 = 487781) B487781
theorem B489041 : Blo 323837 489041 := bstep (se 2 (by rfl) ⟨183390, by rfl⟩ : syracuseStep 489041 = 366781) B366781
theorem B325203 : Blo 323837 325203 := bstep (se 1 (by rfl) ⟨243902, by rfl⟩ : syracuseStep 325203 = 487805) B487805
theorem B325219 : Blo 323837 325219 := bstep (se 1 (by rfl) ⟨243914, by rfl⟩ : syracuseStep 325219 = 487829) B487829
theorem B489059 : Blo 323837 489059 := bstep (se 1 (by rfl) ⟨366794, by rfl⟩ : syracuseStep 489059 = 733589) B733589
theorem B325235 : Blo 323837 325235 := bstep (se 1 (by rfl) ⟨243926, by rfl⟩ : syracuseStep 325235 = 487853) B487853
theorem B489089 : Blo 323837 489089 := bstep (se 2 (by rfl) ⟨183408, by rfl⟩ : syracuseStep 489089 = 366817) B366817
theorem B325251 : Blo 323837 325251 := bstep (se 1 (by rfl) ⟨243938, by rfl⟩ : syracuseStep 325251 = 487877) B487877
theorem B325267 : Blo 323837 325267 := bstep (se 1 (by rfl) ⟨243950, by rfl⟩ : syracuseStep 325267 = 487901) B487901
theorem B489107 : Blo 323837 489107 := bstep (se 1 (by rfl) ⟨366830, by rfl⟩ : syracuseStep 489107 = 733661) B733661
theorem B325283 : Blo 323837 325283 := bstep (se 1 (by rfl) ⟨243962, by rfl⟩ : syracuseStep 325283 = 487925) B487925
theorem B489137 : Blo 323837 489137 := bstep (se 2 (by rfl) ⟨183426, by rfl⟩ : syracuseStep 489137 = 366853) B366853
theorem B325299 : Blo 323837 325299 := bstep (se 1 (by rfl) ⟨243974, by rfl⟩ : syracuseStep 325299 = 487949) B487949
theorem B390835 : Blo 323837 390835 := bstep (se 1 (by rfl) ⟨293126, by rfl⟩ : syracuseStep 390835 = 586253) B586253
theorem B325315 : Blo 323837 325315 := bstep (se 1 (by rfl) ⟨243986, by rfl⟩ : syracuseStep 325315 = 487973) B487973
theorem B489155 : Blo 323837 489155 := bstep (se 1 (by rfl) ⟨366866, by rfl⟩ : syracuseStep 489155 = 733733) B733733
theorem B620227 : Blo 323837 620227 := bstep (se 1 (by rfl) ⟨465170, by rfl⟩ : syracuseStep 620227 = 930341) B930341
theorem B325331 : Blo 323837 325331 := bstep (se 1 (by rfl) ⟨243998, by rfl⟩ : syracuseStep 325331 = 487997) B487997
theorem B489185 : Blo 323837 489185 := bstep (se 2 (by rfl) ⟨183444, by rfl⟩ : syracuseStep 489185 = 366889) B366889
theorem B325347 : Blo 323837 325347 := bstep (se 1 (by rfl) ⟨244010, by rfl⟩ : syracuseStep 325347 = 488021) B488021
theorem B620273 : Blo 323837 620273 := bstep (se 2 (by rfl) ⟨232602, by rfl⟩ : syracuseStep 620273 = 465205) B465205
theorem B325363 : Blo 323837 325363 := bstep (se 1 (by rfl) ⟨244022, by rfl⟩ : syracuseStep 325363 = 488045) B488045
theorem B489203 : Blo 323837 489203 := bstep (se 1 (by rfl) ⟨366902, by rfl⟩ : syracuseStep 489203 = 733805) B733805
theorem B325379 : Blo 323837 325379 := bstep (se 1 (by rfl) ⟨244034, by rfl⟩ : syracuseStep 325379 = 488069) B488069
theorem B489233 : Blo 323837 489233 := bstep (se 2 (by rfl) ⟨183462, by rfl⟩ : syracuseStep 489233 = 366925) B366925
theorem B325395 : Blo 323837 325395 := bstep (se 1 (by rfl) ⟨244046, by rfl⟩ : syracuseStep 325395 = 488093) B488093
theorem B325411 : Blo 323837 325411 := bstep (se 1 (by rfl) ⟨244058, by rfl⟩ : syracuseStep 325411 = 488117) B488117
theorem B489251 : Blo 323837 489251 := bstep (se 1 (by rfl) ⟨366938, by rfl⟩ : syracuseStep 489251 = 733877) B733877
theorem B325427 : Blo 323837 325427 := bstep (se 1 (by rfl) ⟨244070, by rfl⟩ : syracuseStep 325427 = 488141) B488141
theorem B489281 : Blo 323837 489281 := bstep (se 2 (by rfl) ⟨183480, by rfl⟩ : syracuseStep 489281 = 366961) B366961
theorem B325443 : Blo 323837 325443 := bstep (se 1 (by rfl) ⟨244082, by rfl⟩ : syracuseStep 325443 = 488165) B488165
theorem B325459 : Blo 323837 325459 := bstep (se 1 (by rfl) ⟨244094, by rfl⟩ : syracuseStep 325459 = 488189) B488189
theorem B489299 : Blo 323837 489299 := bstep (se 1 (by rfl) ⟨366974, by rfl⟩ : syracuseStep 489299 = 733949) B733949
theorem B325475 : Blo 323837 325475 := bstep (se 1 (by rfl) ⟨244106, by rfl⟩ : syracuseStep 325475 = 488213) B488213
theorem B489329 : Blo 323837 489329 := bstep (se 2 (by rfl) ⟨183498, by rfl⟩ : syracuseStep 489329 = 366997) B366997
theorem B325491 : Blo 323837 325491 := bstep (se 1 (by rfl) ⟨244118, by rfl⟩ : syracuseStep 325491 = 488237) B488237
theorem B325507 : Blo 323837 325507 := bstep (se 1 (by rfl) ⟨244130, by rfl⟩ : syracuseStep 325507 = 488261) B488261
theorem B489347 : Blo 323837 489347 := bstep (se 1 (by rfl) ⟨367010, by rfl⟩ : syracuseStep 489347 = 734021) B734021
theorem B587665 : Blo 323837 587665 := bstep (se 2 (by rfl) ⟨220374, by rfl⟩ : syracuseStep 587665 = 440749) B440749
theorem B325523 : Blo 323837 325523 := bstep (se 1 (by rfl) ⟨244142, by rfl⟩ : syracuseStep 325523 = 488285) B488285
theorem B489377 : Blo 323837 489377 := bstep (se 2 (by rfl) ⟨183516, by rfl⟩ : syracuseStep 489377 = 367033) B367033
theorem B325539 : Blo 323837 325539 := bstep (se 1 (by rfl) ⟨244154, by rfl⟩ : syracuseStep 325539 = 488309) B488309
theorem B325555 : Blo 323837 325555 := bstep (se 1 (by rfl) ⟨244166, by rfl⟩ : syracuseStep 325555 = 488333) B488333
theorem B489395 : Blo 323837 489395 := bstep (se 1 (by rfl) ⟨367046, by rfl⟩ : syracuseStep 489395 = 734093) B734093
theorem B325571 : Blo 323837 325571 := bstep (se 1 (by rfl) ⟨244178, by rfl⟩ : syracuseStep 325571 = 488357) B488357
theorem B489425 : Blo 323837 489425 := bstep (se 2 (by rfl) ⟨183534, by rfl⟩ : syracuseStep 489425 = 367069) B367069
theorem B391123 : Blo 323837 391123 := bstep (se 1 (by rfl) ⟨293342, by rfl⟩ : syracuseStep 391123 = 586685) B586685
theorem B325587 : Blo 323837 325587 := bstep (se 1 (by rfl) ⟨244190, by rfl⟩ : syracuseStep 325587 = 488381) B488381
theorem B325603 : Blo 323837 325603 := bstep (se 1 (by rfl) ⟨244202, by rfl⟩ : syracuseStep 325603 = 488405) B488405
theorem B489443 : Blo 323837 489443 := bstep (se 1 (by rfl) ⟨367082, by rfl⟩ : syracuseStep 489443 = 734165) B734165
theorem B325619 : Blo 323837 325619 := bstep (se 1 (by rfl) ⟨244214, by rfl⟩ : syracuseStep 325619 = 488429) B488429
theorem B489473 : Blo 323837 489473 := bstep (se 2 (by rfl) ⟨183552, by rfl⟩ : syracuseStep 489473 = 367105) B367105
theorem B325635 : Blo 323837 325635 := bstep (se 1 (by rfl) ⟨244226, by rfl⟩ : syracuseStep 325635 = 488453) B488453
theorem B620561 : Blo 323837 620561 := bstep (se 2 (by rfl) ⟨232710, by rfl⟩ : syracuseStep 620561 = 465421) B465421
theorem B325651 : Blo 323837 325651 := bstep (se 1 (by rfl) ⟨244238, by rfl⟩ : syracuseStep 325651 = 488477) B488477
theorem B489491 : Blo 323837 489491 := bstep (se 1 (by rfl) ⟨367118, by rfl⟩ : syracuseStep 489491 = 734237) B734237
theorem B325667 : Blo 323837 325667 := bstep (se 1 (by rfl) ⟨244250, by rfl⟩ : syracuseStep 325667 = 488501) B488501
theorem B489521 : Blo 323837 489521 := bstep (se 2 (by rfl) ⟨183570, by rfl⟩ : syracuseStep 489521 = 367141) B367141
theorem B1767473 : Blo 323837 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B325683 : Blo 323837 325683 := bstep (se 1 (by rfl) ⟨244262, by rfl⟩ : syracuseStep 325683 = 488525) B488525
theorem B325699 : Blo 323837 325699 := bstep (se 1 (by rfl) ⟨244274, by rfl⟩ : syracuseStep 325699 = 488549) B488549
theorem B489539 : Blo 323837 489539 := bstep (se 1 (by rfl) ⟨367154, by rfl⟩ : syracuseStep 489539 = 734309) B734309
theorem B1701965 : Blo 323837 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B325715 : Blo 323837 325715 := bstep (se 1 (by rfl) ⟨244286, by rfl⟩ : syracuseStep 325715 = 488573) B488573
theorem B489569 : Blo 323837 489569 := bstep (se 2 (by rfl) ⟨183588, by rfl⟩ : syracuseStep 489569 = 367177) B367177
theorem B325731 : Blo 323837 325731 := bstep (se 1 (by rfl) ⟨244298, by rfl⟩ : syracuseStep 325731 = 488597) B488597
theorem B325747 : Blo 323837 325747 := bstep (se 1 (by rfl) ⟨244310, by rfl⟩ : syracuseStep 325747 = 488621) B488621
theorem B489587 : Blo 323837 489587 := bstep (se 1 (by rfl) ⟨367190, by rfl⟩ : syracuseStep 489587 = 734381) B734381
theorem B325763 : Blo 323837 325763 := bstep (se 1 (by rfl) ⟨244322, by rfl⟩ : syracuseStep 325763 = 488645) B488645
theorem B489617 : Blo 323837 489617 := bstep (se 2 (by rfl) ⟨183606, by rfl⟩ : syracuseStep 489617 = 367213) B367213
theorem B325779 : Blo 323837 325779 := bstep (se 1 (by rfl) ⟨244334, by rfl⟩ : syracuseStep 325779 = 488669) B488669
theorem B325795 : Blo 323837 325795 := bstep (se 1 (by rfl) ⟨244346, by rfl⟩ : syracuseStep 325795 = 488693) B488693
theorem B489635 : Blo 323837 489635 := bstep (se 1 (by rfl) ⟨367226, by rfl⟩ : syracuseStep 489635 = 734453) B734453
theorem B2095267 : Blo 323837 2095267 := bstep (se 1 (by rfl) ⟨1571450, by rfl⟩ : syracuseStep 2095267 = 3142901) B3142901
theorem B587953 : Blo 323837 587953 := bstep (se 2 (by rfl) ⟨220482, by rfl⟩ : syracuseStep 587953 = 440965) B440965
theorem B325811 : Blo 323837 325811 := bstep (se 1 (by rfl) ⟨244358, by rfl⟩ : syracuseStep 325811 = 488717) B488717
theorem B489665 : Blo 323837 489665 := bstep (se 2 (by rfl) ⟨183624, by rfl⟩ : syracuseStep 489665 = 367249) B367249
theorem B325827 : Blo 323837 325827 := bstep (se 1 (by rfl) ⟨244370, by rfl⟩ : syracuseStep 325827 = 488741) B488741
theorem B325843 : Blo 323837 325843 := bstep (se 1 (by rfl) ⟨244382, by rfl⟩ : syracuseStep 325843 = 488765) B488765
theorem B489683 : Blo 323837 489683 := bstep (se 1 (by rfl) ⟨367262, by rfl⟩ : syracuseStep 489683 = 734525) B734525
theorem B325859 : Blo 323837 325859 := bstep (se 1 (by rfl) ⟨244394, by rfl⟩ : syracuseStep 325859 = 488789) B488789
theorem B489713 : Blo 323837 489713 := bstep (se 2 (by rfl) ⟨183642, by rfl⟩ : syracuseStep 489713 = 367285) B367285
theorem B325875 : Blo 323837 325875 := bstep (se 1 (by rfl) ⟨244406, by rfl⟩ : syracuseStep 325875 = 488813) B488813
theorem B522497 : Blo 323837 522497 := bstep (se 2 (by rfl) ⟨195936, by rfl⟩ : syracuseStep 522497 = 391873) B391873
theorem B325891 : Blo 323837 325891 := bstep (se 1 (by rfl) ⟨244418, by rfl⟩ : syracuseStep 325891 = 488837) B488837
theorem B489731 : Blo 323837 489731 := bstep (se 1 (by rfl) ⟨367298, by rfl⟩ : syracuseStep 489731 = 734597) B734597
theorem B325907 : Blo 323837 325907 := bstep (se 1 (by rfl) ⟨244430, by rfl⟩ : syracuseStep 325907 = 488861) B488861
theorem B489761 : Blo 323837 489761 := bstep (se 2 (by rfl) ⟨183660, by rfl⟩ : syracuseStep 489761 = 367321) B367321
theorem B325923 : Blo 323837 325923 := bstep (se 1 (by rfl) ⟨244442, by rfl⟩ : syracuseStep 325923 = 488885) B488885
theorem B325939 : Blo 323837 325939 := bstep (se 1 (by rfl) ⟨244454, by rfl⟩ : syracuseStep 325939 = 488909) B488909
theorem B489779 : Blo 323837 489779 := bstep (se 1 (by rfl) ⟨367334, by rfl⟩ : syracuseStep 489779 = 734669) B734669
theorem B325955 : Blo 323837 325955 := bstep (se 1 (by rfl) ⟨244466, by rfl⟩ : syracuseStep 325955 = 488933) B488933
theorem B489809 : Blo 323837 489809 := bstep (se 2 (by rfl) ⟨183678, by rfl⟩ : syracuseStep 489809 = 367357) B367357
theorem B325971 : Blo 323837 325971 := bstep (se 1 (by rfl) ⟨244478, by rfl⟩ : syracuseStep 325971 = 488957) B488957
theorem B325987 : Blo 323837 325987 := bstep (se 1 (by rfl) ⟨244490, by rfl⟩ : syracuseStep 325987 = 488981) B488981
theorem B489827 : Blo 323837 489827 := bstep (se 1 (by rfl) ⟨367370, by rfl⟩ : syracuseStep 489827 = 734741) B734741
theorem B326003 : Blo 323837 326003 := bstep (se 1 (by rfl) ⟨244502, by rfl⟩ : syracuseStep 326003 = 489005) B489005
theorem B489857 : Blo 323837 489857 := bstep (se 2 (by rfl) ⟨183696, by rfl⟩ : syracuseStep 489857 = 367393) B367393
theorem B326019 : Blo 323837 326019 := bstep (se 1 (by rfl) ⟨244514, by rfl⟩ : syracuseStep 326019 = 489029) B489029
theorem B326035 : Blo 323837 326035 := bstep (se 1 (by rfl) ⟨244526, by rfl⟩ : syracuseStep 326035 = 489053) B489053
theorem B489875 : Blo 323837 489875 := bstep (se 1 (by rfl) ⟨367406, by rfl⟩ : syracuseStep 489875 = 734813) B734813
theorem B326051 : Blo 323837 326051 := bstep (se 1 (by rfl) ⟨244538, by rfl⟩ : syracuseStep 326051 = 489077) B489077
theorem B489905 : Blo 323837 489905 := bstep (se 2 (by rfl) ⟨183714, by rfl⟩ : syracuseStep 489905 = 367429) B367429
theorem B326067 : Blo 323837 326067 := bstep (se 1 (by rfl) ⟨244550, by rfl⟩ : syracuseStep 326067 = 489101) B489101
theorem B326083 : Blo 323837 326083 := bstep (se 1 (by rfl) ⟨244562, by rfl⟩ : syracuseStep 326083 = 489125) B489125
theorem B489923 : Blo 323837 489923 := bstep (se 1 (by rfl) ⟨367442, by rfl⟩ : syracuseStep 489923 = 734885) B734885
theorem B326099 : Blo 323837 326099 := bstep (se 1 (by rfl) ⟨244574, by rfl⟩ : syracuseStep 326099 = 489149) B489149
theorem B489953 : Blo 323837 489953 := bstep (se 2 (by rfl) ⟨183732, by rfl⟩ : syracuseStep 489953 = 367465) B367465
theorem B326115 : Blo 323837 326115 := bstep (se 1 (by rfl) ⟨244586, by rfl⟩ : syracuseStep 326115 = 489173) B489173
theorem B2128355 : Blo 323837 2128355 := bstep (se 1 (by rfl) ⟨1596266, by rfl⟩ : syracuseStep 2128355 = 3192533) B3192533
theorem B326131 : Blo 323837 326131 := bstep (se 1 (by rfl) ⟨244598, by rfl⟩ : syracuseStep 326131 = 489197) B489197
theorem B489971 : Blo 323837 489971 := bstep (se 1 (by rfl) ⟨367478, by rfl⟩ : syracuseStep 489971 = 734957) B734957
theorem B326147 : Blo 323837 326147 := bstep (se 1 (by rfl) ⟨244610, by rfl⟩ : syracuseStep 326147 = 489221) B489221
theorem B490001 : Blo 323837 490001 := bstep (se 2 (by rfl) ⟨183750, by rfl⟩ : syracuseStep 490001 = 367501) B367501
theorem B326163 : Blo 323837 326163 := bstep (se 1 (by rfl) ⟨244622, by rfl⟩ : syracuseStep 326163 = 489245) B489245
theorem B326179 : Blo 323837 326179 := bstep (se 1 (by rfl) ⟨244634, by rfl⟩ : syracuseStep 326179 = 489269) B489269
theorem B490019 : Blo 323837 490019 := bstep (se 1 (by rfl) ⟨367514, by rfl⟩ : syracuseStep 490019 = 735029) B735029
theorem B326195 : Blo 323837 326195 := bstep (se 1 (by rfl) ⟨244646, by rfl⟩ : syracuseStep 326195 = 489293) B489293
theorem B490049 : Blo 323837 490049 := bstep (se 2 (by rfl) ⟨183768, by rfl⟩ : syracuseStep 490049 = 367537) B367537
theorem B326211 : Blo 323837 326211 := bstep (se 1 (by rfl) ⟨244658, by rfl⟩ : syracuseStep 326211 = 489317) B489317
theorem B1768013 : Blo 323837 1768013 := bstep (se 3 (by rfl) ⟨331502, by rfl⟩ : syracuseStep 1768013 = 663005) B663005
theorem B326227 : Blo 323837 326227 := bstep (se 1 (by rfl) ⟨244670, by rfl⟩ : syracuseStep 326227 = 489341) B489341
theorem B490067 : Blo 323837 490067 := bstep (se 1 (by rfl) ⟨367550, by rfl⟩ : syracuseStep 490067 = 735101) B735101
theorem B326243 : Blo 323837 326243 := bstep (se 1 (by rfl) ⟨244682, by rfl⟩ : syracuseStep 326243 = 489365) B489365
theorem B490097 : Blo 323837 490097 := bstep (se 2 (by rfl) ⟨183786, by rfl⟩ : syracuseStep 490097 = 367573) B367573
theorem B326259 : Blo 323837 326259 := bstep (se 1 (by rfl) ⟨244694, by rfl⟩ : syracuseStep 326259 = 489389) B489389
theorem B326275 : Blo 323837 326275 := bstep (se 1 (by rfl) ⟨244706, by rfl⟩ : syracuseStep 326275 = 489413) B489413
theorem B490115 : Blo 323837 490115 := bstep (se 1 (by rfl) ⟨367586, by rfl⟩ : syracuseStep 490115 = 735173) B735173
theorem B326291 : Blo 323837 326291 := bstep (se 1 (by rfl) ⟨244718, by rfl⟩ : syracuseStep 326291 = 489437) B489437
theorem B490145 : Blo 323837 490145 := bstep (se 2 (by rfl) ⟨183804, by rfl⟩ : syracuseStep 490145 = 367609) B367609
theorem B1145507 : Blo 323837 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B326307 : Blo 323837 326307 := bstep (se 1 (by rfl) ⟨244730, by rfl⟩ : syracuseStep 326307 = 489461) B489461
theorem B326323 : Blo 323837 326323 := bstep (se 1 (by rfl) ⟨244742, by rfl⟩ : syracuseStep 326323 = 489485) B489485
theorem B490163 : Blo 323837 490163 := bstep (se 1 (by rfl) ⟨367622, by rfl⟩ : syracuseStep 490163 = 735245) B735245
theorem B326339 : Blo 323837 326339 := bstep (se 1 (by rfl) ⟨244754, by rfl⟩ : syracuseStep 326339 = 489509) B489509
theorem B490193 : Blo 323837 490193 := bstep (se 2 (by rfl) ⟨183822, by rfl⟩ : syracuseStep 490193 = 367645) B367645
theorem B326355 : Blo 323837 326355 := bstep (se 1 (by rfl) ⟨244766, by rfl⟩ : syracuseStep 326355 = 489533) B489533
theorem B326371 : Blo 323837 326371 := bstep (se 1 (by rfl) ⟨244778, by rfl⟩ : syracuseStep 326371 = 489557) B489557
theorem B490211 : Blo 323837 490211 := bstep (se 1 (by rfl) ⟨367658, by rfl⟩ : syracuseStep 490211 = 735317) B735317
theorem B621283 : Blo 323837 621283 := bstep (se 1 (by rfl) ⟨465962, by rfl⟩ : syracuseStep 621283 = 931925) B931925
theorem B326387 : Blo 323837 326387 := bstep (se 1 (by rfl) ⟨244790, by rfl⟩ : syracuseStep 326387 = 489581) B489581
theorem B490241 : Blo 323837 490241 := bstep (se 2 (by rfl) ⟨183840, by rfl⟩ : syracuseStep 490241 = 367681) B367681
theorem B326403 : Blo 323837 326403 := bstep (se 1 (by rfl) ⟨244802, by rfl⟩ : syracuseStep 326403 = 489605) B489605
theorem B326419 : Blo 323837 326419 := bstep (se 1 (by rfl) ⟨244814, by rfl⟩ : syracuseStep 326419 = 489629) B489629
theorem B490259 : Blo 323837 490259 := bstep (se 1 (by rfl) ⟨367694, by rfl⟩ : syracuseStep 490259 = 735389) B735389
theorem B326435 : Blo 323837 326435 := bstep (se 1 (by rfl) ⟨244826, by rfl⟩ : syracuseStep 326435 = 489653) B489653
theorem B490289 : Blo 323837 490289 := bstep (se 2 (by rfl) ⟨183858, by rfl⟩ : syracuseStep 490289 = 367717) B367717
theorem B326451 : Blo 323837 326451 := bstep (se 1 (by rfl) ⟨244838, by rfl⟩ : syracuseStep 326451 = 489677) B489677
theorem B326467 : Blo 323837 326467 := bstep (se 1 (by rfl) ⟨244850, by rfl⟩ : syracuseStep 326467 = 489701) B489701
theorem B490307 : Blo 323837 490307 := bstep (se 1 (by rfl) ⟨367730, by rfl⟩ : syracuseStep 490307 = 735461) B735461
theorem B326483 : Blo 323837 326483 := bstep (se 1 (by rfl) ⟨244862, by rfl⟩ : syracuseStep 326483 = 489725) B489725
theorem B490337 : Blo 323837 490337 := bstep (se 2 (by rfl) ⟨183876, by rfl⟩ : syracuseStep 490337 = 367753) B367753
theorem B326499 : Blo 323837 326499 := bstep (se 1 (by rfl) ⟨244874, by rfl⟩ : syracuseStep 326499 = 489749) B489749
theorem B326515 : Blo 323837 326515 := bstep (se 1 (by rfl) ⟨244886, by rfl⟩ : syracuseStep 326515 = 489773) B489773
theorem B490355 : Blo 323837 490355 := bstep (se 1 (by rfl) ⟨367766, by rfl⟩ : syracuseStep 490355 = 735533) B735533
theorem B326531 : Blo 323837 326531 := bstep (se 1 (by rfl) ⟨244898, by rfl⟩ : syracuseStep 326531 = 489797) B489797
theorem B490385 : Blo 323837 490385 := bstep (se 2 (by rfl) ⟨183894, by rfl⟩ : syracuseStep 490385 = 367789) B367789
theorem B326547 : Blo 323837 326547 := bstep (se 1 (by rfl) ⟨244910, by rfl⟩ : syracuseStep 326547 = 489821) B489821
theorem B326563 : Blo 323837 326563 := bstep (se 1 (by rfl) ⟨244922, by rfl⟩ : syracuseStep 326563 = 489845) B489845
theorem B490403 : Blo 323837 490403 := bstep (se 1 (by rfl) ⟨367802, by rfl⟩ : syracuseStep 490403 = 735605) B735605
theorem B326579 : Blo 323837 326579 := bstep (se 1 (by rfl) ⟨244934, by rfl⟩ : syracuseStep 326579 = 489869) B489869
theorem B490433 : Blo 323837 490433 := bstep (se 2 (by rfl) ⟨183912, by rfl⟩ : syracuseStep 490433 = 367825) B367825
theorem B326595 : Blo 323837 326595 := bstep (se 1 (by rfl) ⟨244946, by rfl⟩ : syracuseStep 326595 = 489893) B489893
theorem B883651 : Blo 323837 883651 := bstep (se 1 (by rfl) ⟨662738, by rfl⟩ : syracuseStep 883651 = 1325477) B1325477
theorem B1047505 : Blo 323837 1047505 := bstep (se 2 (by rfl) ⟨392814, by rfl⟩ : syracuseStep 1047505 = 785629) B785629
theorem B326611 : Blo 323837 326611 := bstep (se 1 (by rfl) ⟨244958, by rfl⟩ : syracuseStep 326611 = 489917) B489917
theorem B490451 : Blo 323837 490451 := bstep (se 1 (by rfl) ⟨367838, by rfl⟩ : syracuseStep 490451 = 735677) B735677
theorem B326627 : Blo 323837 326627 := bstep (se 1 (by rfl) ⟨244970, by rfl⟩ : syracuseStep 326627 = 489941) B489941
theorem B523235 : Blo 323837 523235 := bstep (se 1 (by rfl) ⟨392426, by rfl⟩ : syracuseStep 523235 = 784853) B784853
theorem B490481 : Blo 323837 490481 := bstep (se 2 (by rfl) ⟨183930, by rfl⟩ : syracuseStep 490481 = 367861) B367861
theorem B326643 : Blo 323837 326643 := bstep (se 1 (by rfl) ⟨244982, by rfl⟩ : syracuseStep 326643 = 489965) B489965
theorem B326659 : Blo 323837 326659 := bstep (se 1 (by rfl) ⟨244994, by rfl⟩ : syracuseStep 326659 = 489989) B489989
theorem B490499 : Blo 323837 490499 := bstep (se 1 (by rfl) ⟨367874, by rfl⟩ : syracuseStep 490499 = 735749) B735749
theorem B326675 : Blo 323837 326675 := bstep (se 1 (by rfl) ⟨245006, by rfl⟩ : syracuseStep 326675 = 490013) B490013
theorem B490529 : Blo 323837 490529 := bstep (se 2 (by rfl) ⟨183948, by rfl⟩ : syracuseStep 490529 = 367897) B367897
theorem B326691 : Blo 323837 326691 := bstep (se 1 (by rfl) ⟨245018, by rfl⟩ : syracuseStep 326691 = 490037) B490037
theorem B326707 : Blo 323837 326707 := bstep (se 1 (by rfl) ⟨245030, by rfl⟩ : syracuseStep 326707 = 490061) B490061
theorem B490547 : Blo 323837 490547 := bstep (se 1 (by rfl) ⟨367910, by rfl⟩ : syracuseStep 490547 = 735821) B735821
theorem B326723 : Blo 323837 326723 := bstep (se 1 (by rfl) ⟨245042, by rfl⟩ : syracuseStep 326723 = 490085) B490085
theorem B490577 : Blo 323837 490577 := bstep (se 2 (by rfl) ⟨183966, by rfl⟩ : syracuseStep 490577 = 367933) B367933
theorem B326739 : Blo 323837 326739 := bstep (se 1 (by rfl) ⟨245054, by rfl⟩ : syracuseStep 326739 = 490109) B490109
theorem B326755 : Blo 323837 326755 := bstep (se 1 (by rfl) ⟨245066, by rfl⟩ : syracuseStep 326755 = 490133) B490133
theorem B490595 : Blo 323837 490595 := bstep (se 1 (by rfl) ⟨367946, by rfl⟩ : syracuseStep 490595 = 735893) B735893
theorem B326771 : Blo 323837 326771 := bstep (se 1 (by rfl) ⟨245078, by rfl⟩ : syracuseStep 326771 = 490157) B490157
theorem B490625 : Blo 323837 490625 := bstep (se 2 (by rfl) ⟨183984, by rfl⟩ : syracuseStep 490625 = 367969) B367969
theorem B326787 : Blo 323837 326787 := bstep (se 1 (by rfl) ⟨245090, by rfl⟩ : syracuseStep 326787 = 490181) B490181
theorem B326803 : Blo 323837 326803 := bstep (se 1 (by rfl) ⟨245102, by rfl⟩ : syracuseStep 326803 = 490205) B490205
theorem B490643 : Blo 323837 490643 := bstep (se 1 (by rfl) ⟨367982, by rfl⟩ : syracuseStep 490643 = 735965) B735965
theorem B326819 : Blo 323837 326819 := bstep (se 1 (by rfl) ⟨245114, by rfl⟩ : syracuseStep 326819 = 490229) B490229
theorem B621731 : Blo 323837 621731 := bstep (se 1 (by rfl) ⟨466298, by rfl⟩ : syracuseStep 621731 = 932597) B932597
theorem B490673 : Blo 323837 490673 := bstep (se 2 (by rfl) ⟨184002, by rfl⟩ : syracuseStep 490673 = 368005) B368005
theorem B326835 : Blo 323837 326835 := bstep (se 1 (by rfl) ⟨245126, by rfl⟩ : syracuseStep 326835 = 490253) B490253
theorem B326851 : Blo 323837 326851 := bstep (se 1 (by rfl) ⟨245138, by rfl⟩ : syracuseStep 326851 = 490277) B490277
theorem B490691 : Blo 323837 490691 := bstep (se 1 (by rfl) ⟨368018, by rfl⟩ : syracuseStep 490691 = 736037) B736037
theorem B326867 : Blo 323837 326867 := bstep (se 1 (by rfl) ⟨245150, by rfl⟩ : syracuseStep 326867 = 490301) B490301
theorem B490721 : Blo 323837 490721 := bstep (se 2 (by rfl) ⟨184020, by rfl⟩ : syracuseStep 490721 = 368041) B368041
theorem B326883 : Blo 323837 326883 := bstep (se 1 (by rfl) ⟨245162, by rfl⟩ : syracuseStep 326883 = 490325) B490325
theorem B326899 : Blo 323837 326899 := bstep (se 1 (by rfl) ⟨245174, by rfl⟩ : syracuseStep 326899 = 490349) B490349
theorem B490739 : Blo 323837 490739 := bstep (se 1 (by rfl) ⟨368054, by rfl⟩ : syracuseStep 490739 = 736109) B736109
theorem B326915 : Blo 323837 326915 := bstep (se 1 (by rfl) ⟨245186, by rfl⟩ : syracuseStep 326915 = 490373) B490373
theorem B490769 : Blo 323837 490769 := bstep (se 2 (by rfl) ⟨184038, by rfl⟩ : syracuseStep 490769 = 368077) B368077
theorem B326931 : Blo 323837 326931 := bstep (se 1 (by rfl) ⟨245198, by rfl⟩ : syracuseStep 326931 = 490397) B490397
theorem B326947 : Blo 323837 326947 := bstep (se 1 (by rfl) ⟨245210, by rfl⟩ : syracuseStep 326947 = 490421) B490421
theorem B490787 : Blo 323837 490787 := bstep (se 1 (by rfl) ⟨368090, by rfl⟩ : syracuseStep 490787 = 736181) B736181
theorem B326963 : Blo 323837 326963 := bstep (se 1 (by rfl) ⟨245222, by rfl⟩ : syracuseStep 326963 = 490445) B490445
theorem B490817 : Blo 323837 490817 := bstep (se 2 (by rfl) ⟨184056, by rfl⟩ : syracuseStep 490817 = 368113) B368113
theorem B326979 : Blo 323837 326979 := bstep (se 1 (by rfl) ⟨245234, by rfl⟩ : syracuseStep 326979 = 490469) B490469
theorem B326995 : Blo 323837 326995 := bstep (se 1 (by rfl) ⟨245246, by rfl⟩ : syracuseStep 326995 = 490493) B490493
theorem B490835 : Blo 323837 490835 := bstep (se 1 (by rfl) ⟨368126, by rfl⟩ : syracuseStep 490835 = 736253) B736253
theorem B327011 : Blo 323837 327011 := bstep (se 1 (by rfl) ⟨245258, by rfl⟩ : syracuseStep 327011 = 490517) B490517
theorem B490865 : Blo 323837 490865 := bstep (se 2 (by rfl) ⟨184074, by rfl⟩ : syracuseStep 490865 = 368149) B368149
theorem B327027 : Blo 323837 327027 := bstep (se 1 (by rfl) ⟨245270, by rfl⟩ : syracuseStep 327027 = 490541) B490541
theorem B327043 : Blo 323837 327043 := bstep (se 1 (by rfl) ⟨245282, by rfl⟩ : syracuseStep 327043 = 490565) B490565
theorem B490883 : Blo 323837 490883 := bstep (se 1 (by rfl) ⟨368162, by rfl⟩ : syracuseStep 490883 = 736325) B736325
theorem B327059 : Blo 323837 327059 := bstep (se 1 (by rfl) ⟨245294, by rfl⟩ : syracuseStep 327059 = 490589) B490589
theorem B490913 : Blo 323837 490913 := bstep (se 2 (by rfl) ⟨184092, by rfl⟩ : syracuseStep 490913 = 368185) B368185
theorem B327075 : Blo 323837 327075 := bstep (se 1 (by rfl) ⟨245306, by rfl⟩ : syracuseStep 327075 = 490613) B490613
theorem B327091 : Blo 323837 327091 := bstep (se 1 (by rfl) ⟨245318, by rfl⟩ : syracuseStep 327091 = 490637) B490637
theorem B490931 : Blo 323837 490931 := bstep (se 1 (by rfl) ⟨368198, by rfl⟩ : syracuseStep 490931 = 736397) B736397
theorem B327107 : Blo 323837 327107 := bstep (se 1 (by rfl) ⟨245330, by rfl⟩ : syracuseStep 327107 = 490661) B490661
theorem B622019 : Blo 323837 622019 := bstep (se 1 (by rfl) ⟨466514, by rfl⟩ : syracuseStep 622019 = 933029) B933029
theorem B490961 : Blo 323837 490961 := bstep (se 2 (by rfl) ⟨184110, by rfl⟩ : syracuseStep 490961 = 368221) B368221
theorem B327123 : Blo 323837 327123 := bstep (se 1 (by rfl) ⟨245342, by rfl⟩ : syracuseStep 327123 = 490685) B490685
theorem B327139 : Blo 323837 327139 := bstep (se 1 (by rfl) ⟨245354, by rfl⟩ : syracuseStep 327139 = 490709) B490709
theorem B490979 : Blo 323837 490979 := bstep (se 1 (by rfl) ⟨368234, by rfl⟩ : syracuseStep 490979 = 736469) B736469
theorem B327155 : Blo 323837 327155 := bstep (se 1 (by rfl) ⟨245366, by rfl⟩ : syracuseStep 327155 = 490733) B490733
theorem B491009 : Blo 323837 491009 := bstep (se 2 (by rfl) ⟨184128, by rfl⟩ : syracuseStep 491009 = 368257) B368257
theorem B327171 : Blo 323837 327171 := bstep (se 1 (by rfl) ⟨245378, by rfl⟩ : syracuseStep 327171 = 490757) B490757
theorem B327187 : Blo 323837 327187 := bstep (se 1 (by rfl) ⟨245390, by rfl⟩ : syracuseStep 327187 = 490781) B490781
theorem B491027 : Blo 323837 491027 := bstep (se 1 (by rfl) ⟨368270, by rfl⟩ : syracuseStep 491027 = 736541) B736541
theorem B327203 : Blo 323837 327203 := bstep (se 1 (by rfl) ⟨245402, by rfl⟩ : syracuseStep 327203 = 490805) B490805
theorem B491057 : Blo 323837 491057 := bstep (se 2 (by rfl) ⟨184146, by rfl⟩ : syracuseStep 491057 = 368293) B368293
theorem B327219 : Blo 323837 327219 := bstep (se 1 (by rfl) ⟨245414, by rfl⟩ : syracuseStep 327219 = 490829) B490829
theorem B327235 : Blo 323837 327235 := bstep (se 1 (by rfl) ⟨245426, by rfl⟩ : syracuseStep 327235 = 490853) B490853
theorem B491075 : Blo 323837 491075 := bstep (se 1 (by rfl) ⟨368306, by rfl⟩ : syracuseStep 491075 = 736613) B736613
theorem B327251 : Blo 323837 327251 := bstep (se 1 (by rfl) ⟨245438, by rfl⟩ : syracuseStep 327251 = 490877) B490877
theorem B491105 : Blo 323837 491105 := bstep (se 2 (by rfl) ⟨184164, by rfl⟩ : syracuseStep 491105 = 368329) B368329
theorem B327267 : Blo 323837 327267 := bstep (se 1 (by rfl) ⟨245450, by rfl⟩ : syracuseStep 327267 = 490901) B490901
theorem B327283 : Blo 323837 327283 := bstep (se 1 (by rfl) ⟨245462, by rfl⟩ : syracuseStep 327283 = 490925) B490925
theorem B491123 : Blo 323837 491123 := bstep (se 1 (by rfl) ⟨368342, by rfl⟩ : syracuseStep 491123 = 736685) B736685
theorem B327299 : Blo 323837 327299 := bstep (se 1 (by rfl) ⟨245474, by rfl⟩ : syracuseStep 327299 = 490949) B490949
theorem B491153 : Blo 323837 491153 := bstep (se 2 (by rfl) ⟨184182, by rfl⟩ : syracuseStep 491153 = 368365) B368365
theorem B327315 : Blo 323837 327315 := bstep (se 1 (by rfl) ⟨245486, by rfl⟩ : syracuseStep 327315 = 490973) B490973
theorem B327331 : Blo 323837 327331 := bstep (se 1 (by rfl) ⟨245498, by rfl⟩ : syracuseStep 327331 = 490997) B490997
theorem B491171 : Blo 323837 491171 := bstep (se 1 (by rfl) ⟨368378, by rfl⟩ : syracuseStep 491171 = 736757) B736757
theorem B327347 : Blo 323837 327347 := bstep (se 1 (by rfl) ⟨245510, by rfl⟩ : syracuseStep 327347 = 491021) B491021
theorem B491201 : Blo 323837 491201 := bstep (se 2 (by rfl) ⟨184200, by rfl⟩ : syracuseStep 491201 = 368401) B368401
theorem B327363 : Blo 323837 327363 := bstep (se 1 (by rfl) ⟨245522, by rfl⟩ : syracuseStep 327363 = 491045) B491045
theorem B884429 : Blo 323837 884429 := bstep (se 3 (by rfl) ⟨165830, by rfl⟩ : syracuseStep 884429 = 331661) B331661
theorem B327379 : Blo 323837 327379 := bstep (se 1 (by rfl) ⟨245534, by rfl⟩ : syracuseStep 327379 = 491069) B491069
theorem B491219 : Blo 323837 491219 := bstep (se 1 (by rfl) ⟨368414, by rfl⟩ : syracuseStep 491219 = 736829) B736829
theorem B327395 : Blo 323837 327395 := bstep (se 1 (by rfl) ⟨245546, by rfl⟩ : syracuseStep 327395 = 491093) B491093
theorem B491249 : Blo 323837 491249 := bstep (se 2 (by rfl) ⟨184218, by rfl⟩ : syracuseStep 491249 = 368437) B368437
theorem B327411 : Blo 323837 327411 := bstep (se 1 (by rfl) ⟨245558, by rfl⟩ : syracuseStep 327411 = 491117) B491117
theorem B884483 : Blo 323837 884483 := bstep (se 1 (by rfl) ⟨663362, by rfl⟩ : syracuseStep 884483 = 1326725) B1326725
theorem B327427 : Blo 323837 327427 := bstep (se 1 (by rfl) ⟨245570, by rfl⟩ : syracuseStep 327427 = 491141) B491141
theorem B491267 : Blo 323837 491267 := bstep (se 1 (by rfl) ⟨368450, by rfl⟩ : syracuseStep 491267 = 736901) B736901
theorem B327443 : Blo 323837 327443 := bstep (se 1 (by rfl) ⟨245582, by rfl⟩ : syracuseStep 327443 = 491165) B491165
theorem B491297 : Blo 323837 491297 := bstep (se 2 (by rfl) ⟨184236, by rfl⟩ : syracuseStep 491297 = 368473) B368473
theorem B327459 : Blo 323837 327459 := bstep (se 1 (by rfl) ⟨245594, by rfl⟩ : syracuseStep 327459 = 491189) B491189
theorem B327475 : Blo 323837 327475 := bstep (se 1 (by rfl) ⟨245606, by rfl⟩ : syracuseStep 327475 = 491213) B491213
theorem B491315 : Blo 323837 491315 := bstep (se 1 (by rfl) ⟨368486, by rfl⟩ : syracuseStep 491315 = 736973) B736973
theorem B327491 : Blo 323837 327491 := bstep (se 1 (by rfl) ⟨245618, by rfl⟩ : syracuseStep 327491 = 491237) B491237
theorem B491345 : Blo 323837 491345 := bstep (se 2 (by rfl) ⟨184254, by rfl⟩ : syracuseStep 491345 = 368509) B368509
theorem B327507 : Blo 323837 327507 := bstep (se 1 (by rfl) ⟨245630, by rfl⟩ : syracuseStep 327507 = 491261) B491261
theorem B327523 : Blo 323837 327523 := bstep (se 1 (by rfl) ⟨245642, by rfl⟩ : syracuseStep 327523 = 491285) B491285
theorem B491363 : Blo 323837 491363 := bstep (se 1 (by rfl) ⟨368522, by rfl⟩ : syracuseStep 491363 = 737045) B737045
theorem B327539 : Blo 323837 327539 := bstep (se 1 (by rfl) ⟨245654, by rfl⟩ : syracuseStep 327539 = 491309) B491309
theorem B491393 : Blo 323837 491393 := bstep (se 2 (by rfl) ⟨184272, by rfl⟩ : syracuseStep 491393 = 368545) B368545
theorem B327555 : Blo 323837 327555 := bstep (se 1 (by rfl) ⟨245666, by rfl⟩ : syracuseStep 327555 = 491333) B491333
theorem B327571 : Blo 323837 327571 := bstep (se 1 (by rfl) ⟨245678, by rfl⟩ : syracuseStep 327571 = 491357) B491357
theorem B491411 : Blo 323837 491411 := bstep (se 1 (by rfl) ⟨368558, by rfl⟩ : syracuseStep 491411 = 737117) B737117
theorem B327587 : Blo 323837 327587 := bstep (se 1 (by rfl) ⟨245690, by rfl⟩ : syracuseStep 327587 = 491381) B491381
theorem B491441 : Blo 323837 491441 := bstep (se 2 (by rfl) ⟨184290, by rfl⟩ : syracuseStep 491441 = 368581) B368581
theorem B327603 : Blo 323837 327603 := bstep (se 1 (by rfl) ⟨245702, by rfl⟩ : syracuseStep 327603 = 491405) B491405
theorem B524227 : Blo 323837 524227 := bstep (se 1 (by rfl) ⟨393170, by rfl⟩ : syracuseStep 524227 = 786341) B786341
theorem B327619 : Blo 323837 327619 := bstep (se 1 (by rfl) ⟨245714, by rfl⟩ : syracuseStep 327619 = 491429) B491429
theorem B491459 : Blo 323837 491459 := bstep (se 1 (by rfl) ⟨368594, by rfl⟩ : syracuseStep 491459 = 737189) B737189
theorem B327635 : Blo 323837 327635 := bstep (se 1 (by rfl) ⟨245726, by rfl⟩ : syracuseStep 327635 = 491453) B491453
theorem B491489 : Blo 323837 491489 := bstep (se 2 (by rfl) ⟨184308, by rfl⟩ : syracuseStep 491489 = 368617) B368617
theorem B327651 : Blo 323837 327651 := bstep (se 1 (by rfl) ⟨245738, by rfl⟩ : syracuseStep 327651 = 491477) B491477
theorem B327667 : Blo 323837 327667 := bstep (se 1 (by rfl) ⟨245750, by rfl⟩ : syracuseStep 327667 = 491501) B491501
theorem B491507 : Blo 323837 491507 := bstep (se 1 (by rfl) ⟨368630, by rfl⟩ : syracuseStep 491507 = 737261) B737261
theorem B491531 : Blo 323837 491531 := bstep (se 1 (by rfl) ⟨368648, by rfl⟩ : syracuseStep 491531 = 737297) B737297
theorem B327691 : Blo 323837 327691 := bstep (se 1 (by rfl) ⟨245768, by rfl⟩ : syracuseStep 327691 = 491537) B491537
theorem B491543 : Blo 323837 491543 := bstep (se 1 (by rfl) ⟨368657, by rfl⟩ : syracuseStep 491543 = 737315) B737315
theorem B327703 : Blo 323837 327703 := bstep (se 1 (by rfl) ⟨245777, by rfl⟩ : syracuseStep 327703 = 491555) B491555
theorem B327723 : Blo 323837 327723 := bstep (se 1 (by rfl) ⟨245792, by rfl⟩ : syracuseStep 327723 = 491585) B491585
theorem B327735 : Blo 323837 327735 := bstep (se 1 (by rfl) ⟨245801, by rfl⟩ : syracuseStep 327735 = 491603) B491603
theorem B327755 : Blo 323837 327755 := bstep (se 1 (by rfl) ⟨245816, by rfl⟩ : syracuseStep 327755 = 491633) B491633
theorem B327767 : Blo 323837 327767 := bstep (se 1 (by rfl) ⟨245825, by rfl⟩ : syracuseStep 327767 = 491651) B491651
theorem B491609 : Blo 323837 491609 := bstep (se 2 (by rfl) ⟨184353, by rfl⟩ : syracuseStep 491609 = 368707) B368707
theorem B327787 : Blo 323837 327787 := bstep (se 1 (by rfl) ⟨245840, by rfl⟩ : syracuseStep 327787 = 491681) B491681
theorem B327799 : Blo 323837 327799 := bstep (se 1 (by rfl) ⟨245849, by rfl⟩ : syracuseStep 327799 = 491699) B491699
theorem B327819 : Blo 323837 327819 := bstep (se 1 (by rfl) ⟨245864, by rfl⟩ : syracuseStep 327819 = 491729) B491729
theorem B327831 : Blo 323837 327831 := bstep (se 1 (by rfl) ⟨245873, by rfl⟩ : syracuseStep 327831 = 491747) B491747
theorem B491723 : Blo 323837 491723 := bstep (se 1 (by rfl) ⟨368792, by rfl⟩ : syracuseStep 491723 = 737585) B737585
theorem B491735 : Blo 323837 491735 := bstep (se 1 (by rfl) ⟨368801, by rfl⟩ : syracuseStep 491735 = 737603) B737603
theorem B524875 : Blo 323837 524875 := bstep (se 1 (by rfl) ⟨393656, by rfl⟩ : syracuseStep 524875 = 787313) B787313
theorem B1114717 : Blo 323837 1114717 := bstep (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) B418019
theorem B590657 : Blo 323837 590657 := bstep (se 2 (by rfl) ⟨221496, by rfl⟩ : syracuseStep 590657 = 442993) B442993
theorem B525131 : Blo 323837 525131 := bstep (se 1 (by rfl) ⟨393848, by rfl⟩ : syracuseStep 525131 = 787697) B787697
theorem B623627 : Blo 323837 623627 := bstep (se 1 (by rfl) ⟨467720, by rfl⟩ : syracuseStep 623627 = 935441) B935441
theorem B623641 : Blo 323837 623641 := bstep (se 2 (by rfl) ⟨233865, by rfl⟩ : syracuseStep 623641 = 467731) B467731
theorem B820631 : Blo 323837 820631 := bstep (se 1 (by rfl) ⟨615473, by rfl⟩ : syracuseStep 820631 = 1230947) B1230947
theorem B329131 : Blo 323837 329131 := bstep (se 1 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 329131 = 493697) B493697
theorem B493015 : Blo 323837 493015 := bstep (se 1 (by rfl) ⟨369761, by rfl⟩ : syracuseStep 493015 = 739523) B739523
theorem B1640087 : Blo 323837 1640087 := bstep (se 1 (by rfl) ⟨1230065, by rfl⟩ : syracuseStep 1640087 = 2460131) B2460131
theorem B1181357 : Blo 323837 1181357 := bstep (se 3 (by rfl) ⟨221504, by rfl⟩ : syracuseStep 1181357 = 443009) B443009
theorem B3508085 : Blo 323837 3508085 := bstep (se 5 (by rfl) ⟨164441, by rfl⟩ : syracuseStep 3508085 = 328883) B328883
theorem B1574873 : Blo 323837 1574873 := bstep (se 2 (by rfl) ⟨590577, by rfl⟩ : syracuseStep 1574873 = 1181155) B1181155
theorem B821299 : Blo 323837 821299 := bstep (se 1 (by rfl) ⟨615974, by rfl⟩ : syracuseStep 821299 = 1231949) B1231949
theorem B821441 : Blo 323837 821441 := bstep (se 2 (by rfl) ⟨308040, by rfl⟩ : syracuseStep 821441 = 616081) B616081
theorem B2885905 : Blo 323837 2885905 := bstep (se 2 (by rfl) ⟨1082214, by rfl⟩ : syracuseStep 2885905 = 2164429) B2164429
theorem B822707 : Blo 323837 822707 := bstep (se 1 (by rfl) ⟨617030, by rfl⟩ : syracuseStep 822707 = 1234061) B1234061
theorem B1314269 : Blo 323837 1314269 := bstep (se 3 (by rfl) ⟨246425, by rfl⟩ : syracuseStep 1314269 = 492851) B492851
theorem B2690833 : Blo 323837 2690833 := bstep (se 2 (by rfl) ⟨1009062, by rfl⟩ : syracuseStep 2690833 = 2018125) B2018125
theorem B364459 : Blo 323837 364459 := bstep (se 1 (by rfl) ⟨273344, by rfl⟩ : syracuseStep 364459 = 546689) B546689
theorem B823243 : Blo 323837 823243 := bstep (se 1 (by rfl) ⟨617432, by rfl⟩ : syracuseStep 823243 = 1234865) B1234865
theorem B364567 : Blo 323837 364567 := bstep (se 1 (by rfl) ⟨273425, by rfl⟩ : syracuseStep 364567 = 546851) B546851
theorem B1052747 : Blo 323837 1052747 := bstep (se 1 (by rfl) ⟨789560, by rfl⟩ : syracuseStep 1052747 = 1579121) B1579121
theorem B823385 : Blo 323837 823385 := bstep (se 2 (by rfl) ⟨308769, by rfl⟩ : syracuseStep 823385 = 617539) B617539
theorem B364747 : Blo 323837 364747 := bstep (se 1 (by rfl) ⟨273560, by rfl⟩ : syracuseStep 364747 = 547121) B547121
theorem B1478915 : Blo 323837 1478915 := bstep (se 1 (by rfl) ⟨1109186, by rfl⟩ : syracuseStep 1478915 = 2218373) B2218373
theorem B364855 : Blo 323837 364855 := bstep (se 1 (by rfl) ⟨273641, by rfl⟩ : syracuseStep 364855 = 547283) B547283
theorem B692545 : Blo 323837 692545 := bstep (se 2 (by rfl) ⟨259704, by rfl⟩ : syracuseStep 692545 = 519409) B519409
theorem B14127473 : Blo 323837 14127473 := bstep (se 2 (by rfl) ⟨5297802, by rfl⟩ : syracuseStep 14127473 = 10595605) B10595605
theorem B365035 : Blo 323837 365035 := bstep (se 1 (by rfl) ⟨273776, by rfl⟩ : syracuseStep 365035 = 547553) B547553
theorem B692801 : Blo 323837 692801 := bstep (se 2 (by rfl) ⟨259800, by rfl⟩ : syracuseStep 692801 = 519601) B519601
theorem B365143 : Blo 323837 365143 := bstep (se 1 (by rfl) ⟨273857, by rfl⟩ : syracuseStep 365143 = 547715) B547715
theorem B692887 : Blo 323837 692887 := bstep (se 1 (by rfl) ⟨519665, by rfl⟩ : syracuseStep 692887 = 1039331) B1039331
theorem B2790065 : Blo 323837 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B365323 : Blo 323837 365323 := bstep (se 1 (by rfl) ⟨273992, by rfl⟩ : syracuseStep 365323 = 547985) B547985
theorem B922391 : Blo 323837 922391 := bstep (se 1 (by rfl) ⟨691793, by rfl⟩ : syracuseStep 922391 = 1383587) B1383587
theorem B463639 : Blo 323837 463639 := bstep (se 1 (by rfl) ⟨347729, by rfl⟩ : syracuseStep 463639 = 695459) B695459
theorem B3707693 : Blo 323837 3707693 := bstep (se 3 (by rfl) ⟨695192, by rfl⟩ : syracuseStep 3707693 = 1390385) B1390385
theorem B365431 : Blo 323837 365431 := bstep (se 1 (by rfl) ⟨274073, by rfl⟩ : syracuseStep 365431 = 548147) B548147
theorem B824215 : Blo 323837 824215 := bstep (se 1 (by rfl) ⟨618161, by rfl⟩ : syracuseStep 824215 = 1236323) B1236323
theorem B365611 : Blo 323837 365611 := bstep (se 1 (by rfl) ⟨274208, by rfl⟩ : syracuseStep 365611 = 548417) B548417
theorem B1643651 : Blo 323837 1643651 := bstep (se 1 (by rfl) ⟨1232738, by rfl⟩ : syracuseStep 1643651 = 2465477) B2465477
theorem B365719 : Blo 323837 365719 := bstep (se 1 (by rfl) ⟨274289, by rfl⟩ : syracuseStep 365719 = 548579) B548579
theorem B1316147 : Blo 323837 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B365899 : Blo 323837 365899 := bstep (se 1 (by rfl) ⟨274424, by rfl⟩ : syracuseStep 365899 = 548849) B548849
theorem B824651 : Blo 323837 824651 := bstep (se 1 (by rfl) ⟨618488, by rfl⟩ : syracuseStep 824651 = 1236977) B1236977
theorem B366007 : Blo 323837 366007 := bstep (se 1 (by rfl) ⟨274505, by rfl⟩ : syracuseStep 366007 = 549011) B549011
theorem B366187 : Blo 323837 366187 := bstep (se 1 (by rfl) ⟨274640, by rfl⟩ : syracuseStep 366187 = 549281) B549281
theorem B825025 : Blo 323837 825025 := bstep (se 2 (by rfl) ⟨309384, by rfl⟩ : syracuseStep 825025 = 618769) B618769
theorem B366295 : Blo 323837 366295 := bstep (se 1 (by rfl) ⟨274721, by rfl⟩ : syracuseStep 366295 = 549443) B549443
theorem B2463533 : Blo 323837 2463533 := bstep (se 3 (by rfl) ⟨461912, by rfl⟩ : syracuseStep 2463533 = 923825) B923825
theorem B1054529 : Blo 323837 1054529 := bstep (se 2 (by rfl) ⟨395448, by rfl⟩ : syracuseStep 1054529 = 790897) B790897
theorem B792395 : Blo 323837 792395 := bstep (se 1 (by rfl) ⟨594296, by rfl⟩ : syracuseStep 792395 = 1188593) B1188593
theorem B366475 : Blo 323837 366475 := bstep (se 1 (by rfl) ⟨274856, by rfl⟩ : syracuseStep 366475 = 549713) B549713
theorem B366583 : Blo 323837 366583 := bstep (se 1 (by rfl) ⟨274937, by rfl⟩ : syracuseStep 366583 = 549875) B549875
theorem B661505 : Blo 323837 661505 := bstep (se 2 (by rfl) ⟨248064, by rfl⟩ : syracuseStep 661505 = 496129) B496129
theorem B366763 : Blo 323837 366763 := bstep (se 1 (by rfl) ⟨275072, by rfl⟩ : syracuseStep 366763 = 550145) B550145
theorem B366871 : Blo 323837 366871 := bstep (se 1 (by rfl) ⟨275153, by rfl⟩ : syracuseStep 366871 = 550307) B550307
theorem B825623 : Blo 323837 825623 := bstep (se 1 (by rfl) ⟨619217, by rfl⟩ : syracuseStep 825623 = 1238435) B1238435
theorem B367051 : Blo 323837 367051 := bstep (se 1 (by rfl) ⟨275288, by rfl⟩ : syracuseStep 367051 = 550577) B550577
theorem B367159 : Blo 323837 367159 := bstep (se 1 (by rfl) ⟨275369, by rfl⟩ : syracuseStep 367159 = 550739) B550739
theorem B662195 : Blo 323837 662195 := bstep (se 1 (by rfl) ⟨496646, by rfl⟩ : syracuseStep 662195 = 993293) B993293
theorem B367339 : Blo 323837 367339 := bstep (se 1 (by rfl) ⟨275504, by rfl⟩ : syracuseStep 367339 = 551009) B551009
theorem B465689 : Blo 323837 465689 := bstep (se 2 (by rfl) ⟨174633, by rfl⟩ : syracuseStep 465689 = 349267) B349267
theorem B3054401 : Blo 323837 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B1317707 : Blo 323837 1317707 := bstep (se 1 (by rfl) ⟨988280, by rfl⟩ : syracuseStep 1317707 = 1976561) B1976561
theorem B367447 : Blo 323837 367447 := bstep (se 1 (by rfl) ⟨275585, by rfl⟩ : syracuseStep 367447 = 551171) B551171
theorem B924509 : Blo 323837 924509 := bstep (se 3 (by rfl) ⟨173345, by rfl⟩ : syracuseStep 924509 = 346691) B346691
theorem B367627 : Blo 323837 367627 := bstep (se 1 (by rfl) ⟨275720, by rfl⟩ : syracuseStep 367627 = 551441) B551441
theorem B826433 : Blo 323837 826433 := bstep (se 2 (by rfl) ⟨309912, by rfl⟩ : syracuseStep 826433 = 619825) B619825
theorem B3054685 : Blo 323837 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B367735 : Blo 323837 367735 := bstep (se 1 (by rfl) ⟨275801, by rfl⟩ : syracuseStep 367735 = 551603) B551603
theorem B924851 : Blo 323837 924851 := bstep (se 1 (by rfl) ⟨693638, by rfl⟩ : syracuseStep 924851 = 1387277) B1387277
theorem B367915 : Blo 323837 367915 := bstep (se 1 (by rfl) ⟨275936, by rfl⟩ : syracuseStep 367915 = 551873) B551873
theorem B695603 : Blo 323837 695603 := bstep (se 1 (by rfl) ⟨521702, by rfl⟩ : syracuseStep 695603 = 1043405) B1043405
theorem B728371 : Blo 323837 728371 := bstep (se 1 (by rfl) ⟨546278, by rfl⟩ : syracuseStep 728371 = 1092557) B1092557
theorem B368023 : Blo 323837 368023 := bstep (se 1 (by rfl) ⟨276017, by rfl⟩ : syracuseStep 368023 = 552035) B552035
theorem B466327 : Blo 323837 466327 := bstep (se 1 (by rfl) ⟨349745, by rfl⟩ : syracuseStep 466327 = 699491) B699491
theorem B368203 : Blo 323837 368203 := bstep (se 1 (by rfl) ⟨276152, by rfl⟩ : syracuseStep 368203 = 552305) B552305
theorem B826969 : Blo 323837 826969 := bstep (se 2 (by rfl) ⟨310113, by rfl⟩ : syracuseStep 826969 = 620227) B620227
theorem B728729 : Blo 323837 728729 := bstep (se 2 (by rfl) ⟨273273, by rfl⟩ : syracuseStep 728729 = 546547) B546547
theorem B368311 : Blo 323837 368311 := bstep (se 1 (by rfl) ⟨276233, by rfl⟩ : syracuseStep 368311 = 552467) B552467
theorem B728819 : Blo 323837 728819 := bstep (se 1 (by rfl) ⟨546614, by rfl⟩ : syracuseStep 728819 = 1093229) B1093229
theorem B728855 : Blo 323837 728855 := bstep (se 1 (by rfl) ⟨546641, by rfl⟩ : syracuseStep 728855 = 1093283) B1093283
theorem B368491 : Blo 323837 368491 := bstep (se 1 (by rfl) ⟨276368, by rfl⟩ : syracuseStep 368491 = 552737) B552737
theorem B729035 : Blo 323837 729035 := bstep (se 1 (by rfl) ⟨546776, by rfl⟩ : syracuseStep 729035 = 1093553) B1093553
theorem B368599 : Blo 323837 368599 := bstep (se 1 (by rfl) ⟨276449, by rfl⟩ : syracuseStep 368599 = 552899) B552899
theorem B729089 : Blo 323837 729089 := bstep (se 2 (by rfl) ⟨273408, by rfl⟩ : syracuseStep 729089 = 546817) B546817
theorem B368779 : Blo 323837 368779 := bstep (se 1 (by rfl) ⟨276584, by rfl⟩ : syracuseStep 368779 = 553169) B553169
theorem B4169879 : Blo 323837 4169879 := bstep (se 1 (by rfl) ⟨3127409, by rfl⟩ : syracuseStep 4169879 = 6254819) B6254819
theorem B565463 : Blo 323837 565463 := bstep (se 1 (by rfl) ⟨424097, by rfl⟩ : syracuseStep 565463 = 848195) B848195
theorem B729305 : Blo 323837 729305 := bstep (se 2 (by rfl) ⟨273489, by rfl⟩ : syracuseStep 729305 = 546979) B546979
theorem B2793689 : Blo 323837 2793689 := bstep (se 2 (by rfl) ⟨1047633, by rfl⟩ : syracuseStep 2793689 = 2095267) B2095267
theorem B1286423 : Blo 323837 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B729395 : Blo 323837 729395 := bstep (se 1 (by rfl) ⟨547046, by rfl⟩ : syracuseStep 729395 = 1094093) B1094093
theorem B729431 : Blo 323837 729431 := bstep (se 1 (by rfl) ⟨547073, by rfl⟩ : syracuseStep 729431 = 1094147) B1094147
theorem B1319261 : Blo 323837 1319261 := bstep (se 3 (by rfl) ⟨247361, by rfl⟩ : syracuseStep 1319261 = 494723) B494723
theorem B3350963 : Blo 323837 3350963 := bstep (se 1 (by rfl) ⟨2513222, by rfl⟩ : syracuseStep 3350963 = 5026445) B5026445
theorem B729611 : Blo 323837 729611 := bstep (se 1 (by rfl) ⟨547208, by rfl⟩ : syracuseStep 729611 = 1094417) B1094417
theorem B729665 : Blo 323837 729665 := bstep (se 2 (by rfl) ⟨273624, by rfl⟩ : syracuseStep 729665 = 547249) B547249
theorem B696919 : Blo 323837 696919 := bstep (se 1 (by rfl) ⟨522689, by rfl⟩ : syracuseStep 696919 = 1045379) B1045379
theorem B828083 : Blo 323837 828083 := bstep (se 1 (by rfl) ⟨621062, by rfl⟩ : syracuseStep 828083 = 1242125) B1242125
theorem B697099 : Blo 323837 697099 := bstep (se 1 (by rfl) ⟨522824, by rfl⟩ : syracuseStep 697099 = 1045649) B1045649
theorem B1647377 : Blo 323837 1647377 := bstep (se 2 (by rfl) ⟨617766, by rfl⟩ : syracuseStep 1647377 = 1235533) B1235533
theorem B729881 : Blo 323837 729881 := bstep (se 2 (by rfl) ⟨273705, by rfl⟩ : syracuseStep 729881 = 547411) B547411
theorem B1385261 : Blo 323837 1385261 := bstep (se 3 (by rfl) ⟨259736, by rfl⟩ : syracuseStep 1385261 = 519473) B519473
theorem B697175 : Blo 323837 697175 := bstep (se 1 (by rfl) ⟨522881, by rfl⟩ : syracuseStep 697175 = 1045763) B1045763
theorem B729971 : Blo 323837 729971 := bstep (se 1 (by rfl) ⟨547478, by rfl⟩ : syracuseStep 729971 = 1094957) B1094957
theorem B730007 : Blo 323837 730007 := bstep (se 1 (by rfl) ⟨547505, by rfl⟩ : syracuseStep 730007 = 1095011) B1095011
theorem B1647539 : Blo 323837 1647539 := bstep (se 1 (by rfl) ⟨1235654, by rfl⟩ : syracuseStep 1647539 = 2471309) B2471309
theorem B828377 : Blo 323837 828377 := bstep (se 2 (by rfl) ⟨310641, by rfl⟩ : syracuseStep 828377 = 621283) B621283
theorem B730187 : Blo 323837 730187 := bstep (se 1 (by rfl) ⟨547640, by rfl⟩ : syracuseStep 730187 = 1095281) B1095281
theorem B730241 : Blo 323837 730241 := bstep (se 2 (by rfl) ⟨273840, by rfl⟩ : syracuseStep 730241 = 547681) B547681
theorem B8332469 : Blo 323837 8332469 := bstep (se 5 (by rfl) ⟨390584, by rfl⟩ : syracuseStep 8332469 = 781169) B781169
theorem B730457 : Blo 323837 730457 := bstep (se 2 (by rfl) ⟨273921, by rfl⟩ : syracuseStep 730457 = 547843) B547843
theorem B730547 : Blo 323837 730547 := bstep (se 1 (by rfl) ⟨547910, by rfl⟩ : syracuseStep 730547 = 1095821) B1095821
theorem B730583 : Blo 323837 730583 := bstep (se 1 (by rfl) ⟨547937, by rfl⟩ : syracuseStep 730583 = 1095875) B1095875
theorem B927197 : Blo 323837 927197 := bstep (se 3 (by rfl) ⟨173849, by rfl⟩ : syracuseStep 927197 = 347699) B347699
theorem B2467421 : Blo 323837 2467421 := bstep (se 3 (by rfl) ⟨462641, by rfl⟩ : syracuseStep 2467421 = 925283) B925283
theorem B730763 : Blo 323837 730763 := bstep (se 1 (by rfl) ⟨548072, by rfl⟩ : syracuseStep 730763 = 1096145) B1096145
theorem B1418903 : Blo 323837 1418903 := bstep (se 1 (by rfl) ⟨1064177, by rfl⟩ : syracuseStep 1418903 = 2128355) B2128355
theorem B730817 : Blo 323837 730817 := bstep (se 2 (by rfl) ⟨274056, by rfl⟩ : syracuseStep 730817 = 548113) B548113
theorem B927425 : Blo 323837 927425 := bstep (se 2 (by rfl) ⟨347784, by rfl⟩ : syracuseStep 927425 = 695569) B695569
theorem B731033 : Blo 323837 731033 := bstep (se 2 (by rfl) ⟨274137, by rfl⟩ : syracuseStep 731033 = 548275) B548275
theorem B731123 : Blo 323837 731123 := bstep (se 1 (by rfl) ⟨548342, by rfl⟩ : syracuseStep 731123 = 1096685) B1096685
theorem B731159 : Blo 323837 731159 := bstep (se 1 (by rfl) ⟨548369, by rfl⟩ : syracuseStep 731159 = 1096739) B1096739
theorem B927767 : Blo 323837 927767 := bstep (se 1 (by rfl) ⟨695825, by rfl⟩ : syracuseStep 927767 = 1391651) B1391651
theorem B1976413 : Blo 323837 1976413 := bstep (se 3 (by rfl) ⟨370577, by rfl⟩ : syracuseStep 1976413 = 741155) B741155
theorem B7088309 : Blo 323837 7088309 := bstep (se 5 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 7088309 = 664529) B664529
theorem B731339 : Blo 323837 731339 := bstep (se 1 (by rfl) ⟨548504, by rfl⟩ : syracuseStep 731339 = 1097009) B1097009
theorem B731393 : Blo 323837 731393 := bstep (se 2 (by rfl) ⟨274272, by rfl⟩ : syracuseStep 731393 = 548545) B548545
theorem B1681681 : Blo 323837 1681681 := bstep (se 2 (by rfl) ⟨630630, by rfl⟩ : syracuseStep 1681681 = 1261261) B1261261
theorem B1583425 : Blo 323837 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B731609 : Blo 323837 731609 := bstep (se 2 (by rfl) ⟨274353, by rfl⟩ : syracuseStep 731609 = 548707) B548707
theorem B731699 : Blo 323837 731699 := bstep (se 1 (by rfl) ⟨548774, by rfl⟩ : syracuseStep 731699 = 1097549) B1097549
theorem B731735 : Blo 323837 731735 := bstep (se 1 (by rfl) ⟨548801, by rfl⟩ : syracuseStep 731735 = 1097603) B1097603
theorem B698969 : Blo 323837 698969 := bstep (se 2 (by rfl) ⟨262113, by rfl⟩ : syracuseStep 698969 = 524227) B524227
theorem B731915 : Blo 323837 731915 := bstep (se 1 (by rfl) ⟨548936, by rfl⟩ : syracuseStep 731915 = 1097873) B1097873
theorem B731969 : Blo 323837 731969 := bstep (se 2 (by rfl) ⟨274488, by rfl⟩ : syracuseStep 731969 = 548977) B548977
theorem B2796353 : Blo 323837 2796353 := bstep (se 2 (by rfl) ⟨1048632, by rfl⟩ : syracuseStep 2796353 = 2097265) B2097265
theorem B1649483 : Blo 323837 1649483 := bstep (se 1 (by rfl) ⟨1237112, by rfl⟩ : syracuseStep 1649483 = 2474225) B2474225
theorem B1321859 : Blo 323837 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B732185 : Blo 323837 732185 := bstep (se 2 (by rfl) ⟨274569, by rfl⟩ : syracuseStep 732185 = 549139) B549139
theorem B1059929 : Blo 323837 1059929 := bstep (se 2 (by rfl) ⟨397473, by rfl⟩ : syracuseStep 1059929 = 794947) B794947
theorem B732275 : Blo 323837 732275 := bstep (se 1 (by rfl) ⟨549206, by rfl⟩ : syracuseStep 732275 = 1098413) B1098413
theorem B732311 : Blo 323837 732311 := bstep (se 1 (by rfl) ⟨549233, by rfl⟩ : syracuseStep 732311 = 1098467) B1098467
theorem B699635 : Blo 323837 699635 := bstep (se 1 (by rfl) ⟨524726, by rfl⟩ : syracuseStep 699635 = 1049453) B1049453
theorem B732491 : Blo 323837 732491 := bstep (se 1 (by rfl) ⟨549368, by rfl⟩ : syracuseStep 732491 = 1098737) B1098737
theorem B732545 : Blo 323837 732545 := bstep (se 2 (by rfl) ⟨274704, by rfl⟩ : syracuseStep 732545 = 549409) B549409
theorem B1093067 : Blo 323837 1093067 := bstep (se 1 (by rfl) ⟨819800, by rfl⟩ : syracuseStep 1093067 = 1639601) B1639601
theorem B732761 : Blo 323837 732761 := bstep (se 2 (by rfl) ⟨274785, by rfl⟩ : syracuseStep 732761 = 549571) B549571
theorem B732851 : Blo 323837 732851 := bstep (se 1 (by rfl) ⟨549638, by rfl⟩ : syracuseStep 732851 = 1099277) B1099277
theorem B732887 : Blo 323837 732887 := bstep (se 1 (by rfl) ⟨549665, by rfl⟩ : syracuseStep 732887 = 1099331) B1099331
theorem B1093337 : Blo 323837 1093337 := bstep (se 2 (by rfl) ⟨410001, by rfl⟩ : syracuseStep 1093337 = 820003) B820003
theorem B1486637 : Blo 323837 1486637 := bstep (se 3 (by rfl) ⟨278744, by rfl⟩ : syracuseStep 1486637 = 557489) B557489
theorem B733067 : Blo 323837 733067 := bstep (se 1 (by rfl) ⟨549800, by rfl⟩ : syracuseStep 733067 = 1099601) B1099601
theorem B733121 : Blo 323837 733121 := bstep (se 2 (by rfl) ⟨274920, by rfl⟩ : syracuseStep 733121 = 549841) B549841
theorem B1388609 : Blo 323837 1388609 := bstep (se 2 (by rfl) ⟨520728, by rfl⟩ : syracuseStep 1388609 = 1041457) B1041457
theorem B1847447 : Blo 323837 1847447 := bstep (se 1 (by rfl) ⟨1385585, by rfl⟩ : syracuseStep 1847447 = 2771171) B2771171
theorem B733337 : Blo 323837 733337 := bstep (se 2 (by rfl) ⟨275001, by rfl⟩ : syracuseStep 733337 = 550003) B550003
theorem B733427 : Blo 323837 733427 := bstep (se 1 (by rfl) ⟨550070, by rfl⟩ : syracuseStep 733427 = 1100141) B1100141
theorem B733463 : Blo 323837 733463 := bstep (se 1 (by rfl) ⟨550097, by rfl⟩ : syracuseStep 733463 = 1100195) B1100195
theorem B930113 : Blo 323837 930113 := bstep (se 2 (by rfl) ⟨348792, by rfl⟩ : syracuseStep 930113 = 697585) B697585
theorem B1094039 : Blo 323837 1094039 := bstep (se 1 (by rfl) ⟨820529, by rfl⟩ : syracuseStep 1094039 = 1641059) B1641059
theorem B1388951 : Blo 323837 1388951 := bstep (se 1 (by rfl) ⟨1041713, by rfl⟩ : syracuseStep 1388951 = 2083427) B2083427
theorem B733643 : Blo 323837 733643 := bstep (se 1 (by rfl) ⟨550232, by rfl⟩ : syracuseStep 733643 = 1100465) B1100465
theorem B733697 : Blo 323837 733697 := bstep (se 2 (by rfl) ⟨275136, by rfl⟩ : syracuseStep 733697 = 550273) B550273
theorem B5550605 : Blo 323837 5550605 := bstep (se 3 (by rfl) ⟨1040738, by rfl⟩ : syracuseStep 5550605 = 2081477) B2081477
theorem B1651265 : Blo 323837 1651265 := bstep (se 2 (by rfl) ⟨619224, by rfl⟩ : syracuseStep 1651265 = 1238449) B1238449
theorem B733913 : Blo 323837 733913 := bstep (se 2 (by rfl) ⟨275217, by rfl⟩ : syracuseStep 733913 = 550435) B550435
theorem B734003 : Blo 323837 734003 := bstep (se 1 (by rfl) ⟨550502, by rfl⟩ : syracuseStep 734003 = 1101005) B1101005
theorem B734039 : Blo 323837 734039 := bstep (se 1 (by rfl) ⟨550529, by rfl⟩ : syracuseStep 734039 = 1101059) B1101059
theorem B930649 : Blo 323837 930649 := bstep (se 2 (by rfl) ⟨348993, by rfl⟩ : syracuseStep 930649 = 697987) B697987
theorem B1094579 : Blo 323837 1094579 := bstep (se 1 (by rfl) ⟨820934, by rfl⟩ : syracuseStep 1094579 = 1641869) B1641869
theorem B734219 : Blo 323837 734219 := bstep (se 1 (by rfl) ⟨550664, by rfl⟩ : syracuseStep 734219 = 1101329) B1101329
theorem B734273 : Blo 323837 734273 := bstep (se 2 (by rfl) ⟨275352, by rfl⟩ : syracuseStep 734273 = 550705) B550705
theorem B439447 : Blo 323837 439447 := bstep (se 1 (by rfl) ⟨329585, by rfl⟩ : syracuseStep 439447 = 659171) B659171
theorem B1094849 : Blo 323837 1094849 := bstep (se 2 (by rfl) ⟨410568, by rfl⟩ : syracuseStep 1094849 = 821137) B821137
theorem B734489 : Blo 323837 734489 := bstep (se 2 (by rfl) ⟨275433, by rfl⟩ : syracuseStep 734489 = 550867) B550867
theorem B2078045 : Blo 323837 2078045 := bstep (se 3 (by rfl) ⟨389633, by rfl⟩ : syracuseStep 2078045 = 779267) B779267
theorem B734579 : Blo 323837 734579 := bstep (se 1 (by rfl) ⟨550934, by rfl⟩ : syracuseStep 734579 = 1101869) B1101869
theorem B734615 : Blo 323837 734615 := bstep (se 1 (by rfl) ⟨550961, by rfl⟩ : syracuseStep 734615 = 1101923) B1101923
theorem B734795 : Blo 323837 734795 := bstep (se 1 (by rfl) ⟨551096, by rfl⟩ : syracuseStep 734795 = 1102193) B1102193
theorem B734849 : Blo 323837 734849 := bstep (se 2 (by rfl) ⟨275568, by rfl⟩ : syracuseStep 734849 = 551137) B551137
theorem B1881731 : Blo 323837 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B2340569 : Blo 323837 2340569 := bstep (se 2 (by rfl) ⟨877713, by rfl⟩ : syracuseStep 2340569 = 1755427) B1755427
theorem B1095389 : Blo 323837 1095389 := bstep (se 3 (by rfl) ⟨205385, by rfl⟩ : syracuseStep 1095389 = 410771) B410771
theorem B735065 : Blo 323837 735065 := bstep (se 2 (by rfl) ⟨275649, by rfl⟩ : syracuseStep 735065 = 551299) B551299
theorem B735155 : Blo 323837 735155 := bstep (se 1 (by rfl) ⟨551366, by rfl⟩ : syracuseStep 735155 = 1102733) B1102733
theorem B2766797 : Blo 323837 2766797 := bstep (se 3 (by rfl) ⟨518774, by rfl⟩ : syracuseStep 2766797 = 1037549) B1037549
theorem B735191 : Blo 323837 735191 := bstep (se 1 (by rfl) ⟨551393, by rfl⟩ : syracuseStep 735191 = 1102787) B1102787
theorem B735371 : Blo 323837 735371 := bstep (se 1 (by rfl) ⟨551528, by rfl⟩ : syracuseStep 735371 = 1103057) B1103057
theorem B735425 : Blo 323837 735425 := bstep (se 2 (by rfl) ⟨275784, by rfl⟩ : syracuseStep 735425 = 551569) B551569
theorem B440587 : Blo 323837 440587 := bstep (se 1 (by rfl) ⟨330440, by rfl⟩ : syracuseStep 440587 = 660881) B660881
theorem B735641 : Blo 323837 735641 := bstep (se 2 (by rfl) ⟨275865, by rfl⟩ : syracuseStep 735641 = 551731) B551731
theorem B1653209 : Blo 323837 1653209 := bstep (se 2 (by rfl) ⟨619953, by rfl⟩ : syracuseStep 1653209 = 1239907) B1239907
theorem B1391069 : Blo 323837 1391069 := bstep (se 3 (by rfl) ⟨260825, by rfl⟩ : syracuseStep 1391069 = 521651) B521651
theorem B735731 : Blo 323837 735731 := bstep (se 1 (by rfl) ⟨551798, by rfl⟩ : syracuseStep 735731 = 1103597) B1103597
theorem B735767 : Blo 323837 735767 := bstep (se 1 (by rfl) ⟨551825, by rfl⟩ : syracuseStep 735767 = 1103651) B1103651
theorem B735947 : Blo 323837 735947 := bstep (se 1 (by rfl) ⟨551960, by rfl⟩ : syracuseStep 735947 = 1103921) B1103921
theorem B932573 : Blo 323837 932573 := bstep (se 3 (by rfl) ⟨174857, by rfl⟩ : syracuseStep 932573 = 349715) B349715
theorem B736001 : Blo 323837 736001 := bstep (se 2 (by rfl) ⟨276000, by rfl⟩ : syracuseStep 736001 = 552001) B552001
theorem B1391377 : Blo 323837 1391377 := bstep (se 2 (by rfl) ⟨521766, by rfl⟩ : syracuseStep 1391377 = 1043533) B1043533
theorem B1391411 : Blo 323837 1391411 := bstep (se 1 (by rfl) ⟨1043558, by rfl⟩ : syracuseStep 1391411 = 2087117) B2087117
theorem B1096523 : Blo 323837 1096523 := bstep (se 1 (by rfl) ⟨822392, by rfl⟩ : syracuseStep 1096523 = 1644785) B1644785
theorem B736217 : Blo 323837 736217 := bstep (se 2 (by rfl) ⟨276081, by rfl⟩ : syracuseStep 736217 = 552163) B552163
theorem B736307 : Blo 323837 736307 := bstep (se 1 (by rfl) ⟨552230, by rfl⟩ : syracuseStep 736307 = 1104461) B1104461
theorem B736343 : Blo 323837 736343 := bstep (se 1 (by rfl) ⟨552257, by rfl⟩ : syracuseStep 736343 = 1104515) B1104515
theorem B1096793 : Blo 323837 1096793 := bstep (se 2 (by rfl) ⟨411297, by rfl⟩ : syracuseStep 1096793 = 822595) B822595
theorem B375959 : Blo 323837 375959 := bstep (se 1 (by rfl) ⟨281969, by rfl⟩ : syracuseStep 375959 = 563939) B563939
theorem B736523 : Blo 323837 736523 := bstep (se 1 (by rfl) ⟨552392, by rfl⟩ : syracuseStep 736523 = 1104785) B1104785
theorem B1326401 : Blo 323837 1326401 := bstep (se 2 (by rfl) ⟨497400, by rfl⟩ : syracuseStep 1326401 = 994801) B994801
theorem B736577 : Blo 323837 736577 := bstep (se 2 (by rfl) ⟨276216, by rfl⟩ : syracuseStep 736577 = 552433) B552433
theorem B12041621 : Blo 323837 12041621 := bstep (se 6 (by rfl) ⟨282225, by rfl⟩ : syracuseStep 12041621 = 564451) B564451
theorem B1261079 : Blo 323837 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B736793 : Blo 323837 736793 := bstep (se 2 (by rfl) ⟨276297, by rfl⟩ : syracuseStep 736793 = 552595) B552595
theorem B999001 : Blo 323837 999001 := bstep (se 2 (by rfl) ⟨374625, by rfl⟩ : syracuseStep 999001 = 749251) B749251
theorem B1490521 : Blo 323837 1490521 := bstep (se 2 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 1490521 = 1117891) B1117891
theorem B736883 : Blo 323837 736883 := bstep (se 1 (by rfl) ⟨552662, by rfl⟩ : syracuseStep 736883 = 1105325) B1105325
theorem B736919 : Blo 323837 736919 := bstep (se 1 (by rfl) ⟨552689, by rfl⟩ : syracuseStep 736919 = 1105379) B1105379
theorem B1097495 : Blo 323837 1097495 := bstep (se 1 (by rfl) ⟨823121, by rfl⟩ : syracuseStep 1097495 = 1646243) B1646243
theorem B737099 : Blo 323837 737099 := bstep (se 1 (by rfl) ⟨552824, by rfl⟩ : syracuseStep 737099 = 1105649) B1105649
theorem B737153 : Blo 323837 737153 := bstep (se 2 (by rfl) ⟨276432, by rfl⟩ : syracuseStep 737153 = 552865) B552865
theorem B3063703 : Blo 323837 3063703 := bstep (se 1 (by rfl) ⟨2297777, by rfl⟩ : syracuseStep 3063703 = 4595555) B4595555
theorem B1654829 : Blo 323837 1654829 := bstep (se 3 (by rfl) ⟨310280, by rfl⟩ : syracuseStep 1654829 = 620561) B620561
theorem B737369 : Blo 323837 737369 := bstep (se 2 (by rfl) ⟨276513, by rfl⟩ : syracuseStep 737369 = 553027) B553027
theorem B737459 : Blo 323837 737459 := bstep (se 1 (by rfl) ⟨553094, by rfl⟩ : syracuseStep 737459 = 1106189) B1106189
theorem B737495 : Blo 323837 737495 := bstep (se 1 (by rfl) ⟨553121, by rfl⟩ : syracuseStep 737495 = 1106243) B1106243
theorem B1098035 : Blo 323837 1098035 := bstep (se 1 (by rfl) ⟨823526, by rfl⟩ : syracuseStep 1098035 = 1647053) B1647053
theorem B410123 : Blo 323837 410123 := bstep (se 1 (by rfl) ⟨307592, by rfl⟩ : syracuseStep 410123 = 615185) B615185
theorem B23708173 : Blo 323837 23708173 := bstep (se 3 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 23708173 = 8890565) B8890565
theorem B836119 : Blo 323837 836119 := bstep (se 1 (by rfl) ⟨627089, by rfl⟩ : syracuseStep 836119 = 1254179) B1254179
theorem B1098305 : Blo 323837 1098305 := bstep (se 2 (by rfl) ⟨411864, by rfl⟩ : syracuseStep 1098305 = 823729) B823729
theorem B442955 : Blo 323837 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B1393325 : Blo 323837 1393325 := bstep (se 3 (by rfl) ⟨261248, by rfl⟩ : syracuseStep 1393325 = 522497) B522497
theorem B1557265 : Blo 323837 1557265 := bstep (se 2 (by rfl) ⟨583974, by rfl⟩ : syracuseStep 1557265 = 1167949) B1167949
theorem B1852253 : Blo 323837 1852253 := bstep (se 3 (by rfl) ⟨347297, by rfl⟩ : syracuseStep 1852253 = 694595) B694595
theorem B1098845 : Blo 323837 1098845 := bstep (se 3 (by rfl) ⟨206033, by rfl⟩ : syracuseStep 1098845 = 412067) B412067
theorem B1229975 : Blo 323837 1229975 := bstep (se 1 (by rfl) ⟨922481, by rfl⟩ : syracuseStep 1229975 = 1844963) B1844963
theorem B410827 : Blo 323837 410827 := bstep (se 1 (by rfl) ⟨308120, by rfl⟩ : syracuseStep 410827 = 616241) B616241
theorem B1328345 : Blo 323837 1328345 := bstep (se 2 (by rfl) ⟨498129, by rfl⟩ : syracuseStep 1328345 = 996259) B996259
theorem B1000669 : Blo 323837 1000669 := bstep (se 3 (by rfl) ⟨187625, by rfl⟩ : syracuseStep 1000669 = 375251) B375251
theorem B378103 : Blo 323837 378103 := bstep (se 1 (by rfl) ⟨283577, by rfl⟩ : syracuseStep 378103 = 567155) B567155
theorem B1394009 : Blo 323837 1394009 := bstep (se 2 (by rfl) ⟨522753, by rfl⟩ : syracuseStep 1394009 = 1045507) B1045507
theorem B1230173 : Blo 323837 1230173 := bstep (se 3 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 1230173 = 461315) B461315
theorem B411095 : Blo 323837 411095 := bstep (se 1 (by rfl) ⟨308321, by rfl⟩ : syracuseStep 411095 = 616643) B616643
theorem B1328899 : Blo 323837 1328899 := bstep (se 1 (by rfl) ⟨996674, by rfl⟩ : syracuseStep 1328899 = 1993349) B1993349
theorem B346123 : Blo 323837 346123 := bstep (se 1 (by rfl) ⟨259592, by rfl⟩ : syracuseStep 346123 = 519185) B519185
theorem B411799 : Blo 323837 411799 := bstep (se 1 (by rfl) ⟨308849, by rfl⟩ : syracuseStep 411799 = 617699) B617699
theorem B8472757 : Blo 323837 8472757 := bstep (se 5 (by rfl) ⟨397160, by rfl⟩ : syracuseStep 8472757 = 794321) B794321
theorem B739531 : Blo 323837 739531 := bstep (se 1 (by rfl) ⟨554648, by rfl⟩ : syracuseStep 739531 = 1109297) B1109297
theorem B1099979 : Blo 323837 1099979 := bstep (se 1 (by rfl) ⟨824984, by rfl⟩ : syracuseStep 1099979 = 1649969) B1649969
theorem B1493441 : Blo 323837 1493441 := bstep (se 2 (by rfl) ⟨560040, by rfl⟩ : syracuseStep 1493441 = 1120081) B1120081
theorem B1100249 : Blo 323837 1100249 := bstep (se 2 (by rfl) ⟨412593, by rfl⟩ : syracuseStep 1100249 = 825187) B825187
theorem B4999715 : Blo 323837 4999715 := bstep (se 1 (by rfl) ⟨3749786, by rfl⟩ : syracuseStep 4999715 = 7499573) B7499573
theorem B3951179 : Blo 323837 3951179 := bstep (se 1 (by rfl) ⟨2963384, by rfl⟩ : syracuseStep 3951179 = 5926769) B5926769
theorem B7129957 : Blo 323837 7129957 := bstep (se 4 (by rfl) ⟨668433, by rfl⟩ : syracuseStep 7129957 = 1336867) B1336867
theorem B2509955 : Blo 323837 2509955 := bstep (se 1 (by rfl) ⟨1882466, by rfl⟩ : syracuseStep 2509955 = 3764933) B3764933
theorem B1100951 : Blo 323837 1100951 := bstep (se 1 (by rfl) ⟨825713, by rfl⟩ : syracuseStep 1100951 = 1651427) B1651427
theorem B904385 : Blo 323837 904385 := bstep (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) B678289
theorem B1232131 : Blo 323837 1232131 := bstep (se 1 (by rfl) ⟨924098, by rfl⟩ : syracuseStep 1232131 = 1848197) B1848197
theorem B1854737 : Blo 323837 1854737 := bstep (se 2 (by rfl) ⟨695526, by rfl⟩ : syracuseStep 1854737 = 1391053) B1391053
theorem B1232435 : Blo 323837 1232435 := bstep (se 1 (by rfl) ⟨924326, by rfl⟩ : syracuseStep 1232435 = 1848653) B1848653
theorem B2084453 : Blo 323837 2084453 := bstep (se 4 (by rfl) ⟨195417, by rfl⟩ : syracuseStep 2084453 = 390835) B390835
theorem B1101491 : Blo 323837 1101491 := bstep (se 1 (by rfl) ⟨826118, by rfl⟩ : syracuseStep 1101491 = 1652237) B1652237
theorem B413515 : Blo 323837 413515 := bstep (se 1 (by rfl) ⟨310136, by rfl⟩ : syracuseStep 413515 = 620273) B620273
theorem B1658717 : Blo 323837 1658717 := bstep (se 3 (by rfl) ⟨311009, by rfl⟩ : syracuseStep 1658717 = 622019) B622019
theorem B1101761 : Blo 323837 1101761 := bstep (se 2 (by rfl) ⟨413160, by rfl⟩ : syracuseStep 1101761 = 826321) B826321
theorem B1396673 : Blo 323837 1396673 := bstep (se 2 (by rfl) ⟨523752, by rfl⟩ : syracuseStep 1396673 = 1047505) B1047505
theorem B1134643 : Blo 323837 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B1233089 : Blo 323837 1233089 := bstep (se 2 (by rfl) ⟨462408, by rfl⟩ : syracuseStep 1233089 = 924817) B924817
theorem B1167833 : Blo 323837 1167833 := bstep (se 2 (by rfl) ⟨437937, by rfl⟩ : syracuseStep 1167833 = 875875) B875875
theorem B1102301 : Blo 323837 1102301 := bstep (se 3 (by rfl) ⟨206681, by rfl⟩ : syracuseStep 1102301 = 413363) B413363
theorem B348823 : Blo 323837 348823 := bstep (se 1 (by rfl) ⟨261617, by rfl⟩ : syracuseStep 348823 = 523235) B523235
theorem B3134213 : Blo 323837 3134213 := bstep (se 4 (by rfl) ⟨293832, by rfl⟩ : syracuseStep 3134213 = 587665) B587665
theorem B414487 : Blo 323837 414487 := bstep (se 1 (by rfl) ⟨310865, by rfl⟩ : syracuseStep 414487 = 621731) B621731
theorem B4183001 : Blo 323837 4183001 := bstep (se 2 (by rfl) ⟨1568625, by rfl⟩ : syracuseStep 4183001 = 3137251) B3137251
theorem B1398161 : Blo 323837 1398161 := bstep (se 2 (by rfl) ⟨524310, by rfl⟩ : syracuseStep 1398161 = 1048621) B1048621
theorem B1234349 : Blo 323837 1234349 := bstep (se 3 (by rfl) ⟨231440, by rfl⟩ : syracuseStep 1234349 = 462881) B462881
theorem B1234379 : Blo 323837 1234379 := bstep (se 1 (by rfl) ⟨925784, by rfl⟩ : syracuseStep 1234379 = 1851569) B1851569
theorem B349643 : Blo 323837 349643 := bstep (se 1 (by rfl) ⟨262232, by rfl⟩ : syracuseStep 349643 = 524465) B524465
theorem B26891747 : Blo 323837 26891747 := bstep (se 1 (by rfl) ⟨20168810, by rfl⟩ : syracuseStep 26891747 = 40337621) B40337621
theorem B1103435 : Blo 323837 1103435 := bstep (se 1 (by rfl) ⟨827576, by rfl⟩ : syracuseStep 1103435 = 1655153) B1655153
theorem B2872907 : Blo 323837 2872907 := bstep (se 1 (by rfl) ⟨2154680, by rfl⟩ : syracuseStep 2872907 = 4309361) B4309361
theorem B546635 : Blo 323837 546635 := bstep (se 1 (by rfl) ⟨409976, by rfl⟩ : syracuseStep 546635 = 819953) B819953
theorem B1103705 : Blo 323837 1103705 := bstep (se 2 (by rfl) ⟨413889, by rfl⟩ : syracuseStep 1103705 = 827779) B827779
theorem B546763 : Blo 323837 546763 := bstep (se 1 (by rfl) ⟨410072, by rfl⟩ : syracuseStep 546763 = 820145) B820145
theorem B546905 : Blo 323837 546905 := bstep (se 2 (by rfl) ⟨205089, by rfl⟩ : syracuseStep 546905 = 410179) B410179
theorem B1235033 : Blo 323837 1235033 := bstep (se 2 (by rfl) ⟨463137, by rfl⟩ : syracuseStep 1235033 = 926275) B926275
theorem B4675715 : Blo 323837 4675715 := bstep (se 1 (by rfl) ⟨3506786, by rfl⟩ : syracuseStep 4675715 = 7013573) B7013573
theorem B547033 : Blo 323837 547033 := bstep (se 2 (by rfl) ⟨205137, by rfl⟩ : syracuseStep 547033 = 410275) B410275
theorem B1399133 : Blo 323837 1399133 := bstep (se 3 (by rfl) ⟨262337, by rfl⟩ : syracuseStep 1399133 = 524675) B524675
theorem B1169795 : Blo 323837 1169795 := bstep (se 1 (by rfl) ⟨877346, by rfl⟩ : syracuseStep 1169795 = 1754693) B1754693
theorem B1235351 : Blo 323837 1235351 := bstep (se 1 (by rfl) ⟨926513, by rfl⟩ : syracuseStep 1235351 = 1853027) B1853027
theorem B1104407 : Blo 323837 1104407 := bstep (se 1 (by rfl) ⟨828305, by rfl⟩ : syracuseStep 1104407 = 1656611) B1656611
theorem B547607 : Blo 323837 547607 := bstep (se 1 (by rfl) ⟨410705, by rfl⟩ : syracuseStep 547607 = 821411) B821411
theorem B875357 : Blo 323837 875357 := bstep (se 3 (by rfl) ⟨164129, by rfl⟩ : syracuseStep 875357 = 328259) B328259
theorem B547735 : Blo 323837 547735 := bstep (se 1 (by rfl) ⟨410801, by rfl⟩ : syracuseStep 547735 = 821603) B821603
theorem B744385 : Blo 323837 744385 := bstep (se 2 (by rfl) ⟨279144, by rfl⟩ : syracuseStep 744385 = 558289) B558289
theorem B1236019 : Blo 323837 1236019 := bstep (se 1 (by rfl) ⟨927014, by rfl⟩ : syracuseStep 1236019 = 1854029) B1854029
theorem B1104947 : Blo 323837 1104947 := bstep (se 1 (by rfl) ⟨828710, by rfl⟩ : syracuseStep 1104947 = 1657421) B1657421
theorem B1105217 : Blo 323837 1105217 := bstep (se 2 (by rfl) ⟨414456, by rfl⟩ : syracuseStep 1105217 = 828913) B828913
theorem B548363 : Blo 323837 548363 := bstep (se 1 (by rfl) ⟨411272, by rfl⟩ : syracuseStep 548363 = 822545) B822545
theorem B5693003 : Blo 323837 5693003 := bstep (se 1 (by rfl) ⟨4269752, by rfl⟩ : syracuseStep 5693003 = 8539505) B8539505
theorem B548491 : Blo 323837 548491 := bstep (se 1 (by rfl) ⟨411368, by rfl⟩ : syracuseStep 548491 = 822737) B822737
theorem B548633 : Blo 323837 548633 := bstep (se 2 (by rfl) ⟨205737, by rfl⟩ : syracuseStep 548633 = 411475) B411475
theorem B1105757 : Blo 323837 1105757 := bstep (se 3 (by rfl) ⟨207329, by rfl⟩ : syracuseStep 1105757 = 414659) B414659
theorem B941975 : Blo 323837 941975 := bstep (se 1 (by rfl) ⟨706481, by rfl⟩ : syracuseStep 941975 = 1412963) B1412963
theorem B548761 : Blo 323837 548761 := bstep (se 2 (by rfl) ⟨205785, by rfl⟩ : syracuseStep 548761 = 411571) B411571
theorem B1335361 : Blo 323837 1335361 := bstep (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) B1001521
theorem B1237265 : Blo 323837 1237265 := bstep (se 2 (by rfl) ⟨463974, by rfl⟩ : syracuseStep 1237265 = 927949) B927949
theorem B1040663 : Blo 323837 1040663 := bstep (se 1 (by rfl) ⟨780497, by rfl⟩ : syracuseStep 1040663 = 1560995) B1560995
theorem B5005633 : Blo 323837 5005633 := bstep (se 2 (by rfl) ⟨1877112, by rfl⟩ : syracuseStep 5005633 = 3754225) B3754225
theorem B549335 : Blo 323837 549335 := bstep (se 1 (by rfl) ⟨412001, by rfl⟩ : syracuseStep 549335 = 824003) B824003
theorem B1040971 : Blo 323837 1040971 := bstep (se 1 (by rfl) ⟨780728, by rfl⟩ : syracuseStep 1040971 = 1561457) B1561457
theorem B549463 : Blo 323837 549463 := bstep (se 1 (by rfl) ⟨412097, by rfl⟩ : syracuseStep 549463 = 824195) B824195
theorem B10543709 : Blo 323837 10543709 := bstep (se 3 (by rfl) ⟨1976945, by rfl⟩ : syracuseStep 10543709 = 3953891) B3953891
theorem B1991347 : Blo 323837 1991347 := bstep (se 1 (by rfl) ⟨1493510, by rfl⟩ : syracuseStep 1991347 = 2987021) B2987021
theorem B877259 : Blo 323837 877259 := bstep (se 1 (by rfl) ⟨657944, by rfl⟩ : syracuseStep 877259 = 1315889) B1315889
theorem B22438853 : Blo 323837 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B1237963 : Blo 323837 1237963 := bstep (se 1 (by rfl) ⟨928472, by rfl⟩ : syracuseStep 1237963 = 1856945) B1856945
theorem B1860569 : Blo 323837 1860569 := bstep (se 2 (by rfl) ⟨697713, by rfl⟩ : syracuseStep 1860569 = 1395427) B1395427
theorem B746647 : Blo 323837 746647 := bstep (se 1 (by rfl) ⟨559985, by rfl⟩ : syracuseStep 746647 = 1119971) B1119971
theorem B550091 : Blo 323837 550091 := bstep (se 1 (by rfl) ⟨412568, by rfl⟩ : syracuseStep 550091 = 825137) B825137
theorem B1238237 : Blo 323837 1238237 := bstep (se 3 (by rfl) ⟨232169, by rfl⟩ : syracuseStep 1238237 = 464339) B464339
theorem B615755 : Blo 323837 615755 := bstep (se 1 (by rfl) ⟨461816, by rfl⟩ : syracuseStep 615755 = 923633) B923633
theorem B550219 : Blo 323837 550219 := bstep (se 1 (by rfl) ⟨412664, by rfl⟩ : syracuseStep 550219 = 825329) B825329
theorem B550361 : Blo 323837 550361 := bstep (se 2 (by rfl) ⟨206385, by rfl⟩ : syracuseStep 550361 = 412771) B412771
theorem B615937 : Blo 323837 615937 := bstep (se 2 (by rfl) ⟨230976, by rfl⟩ : syracuseStep 615937 = 461953) B461953
theorem B550489 : Blo 323837 550489 := bstep (se 2 (by rfl) ⟨206433, by rfl⟩ : syracuseStep 550489 = 412867) B412867
theorem B4187969 : Blo 323837 4187969 := bstep (se 2 (by rfl) ⟨1570488, by rfl⟩ : syracuseStep 4187969 = 3140977) B3140977
theorem B1238935 : Blo 323837 1238935 := bstep (se 1 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 1238935 = 1858403) B1858403
theorem B616385 : Blo 323837 616385 := bstep (se 2 (by rfl) ⟨231144, by rfl⟩ : syracuseStep 616385 = 462289) B462289
theorem B551063 : Blo 323837 551063 := bstep (se 1 (by rfl) ⟨413297, by rfl⟩ : syracuseStep 551063 = 826595) B826595
theorem B583859 : Blo 323837 583859 := bstep (se 1 (by rfl) ⟨437894, by rfl⟩ : syracuseStep 583859 = 875789) B875789
theorem B616727 : Blo 323837 616727 := bstep (se 1 (by rfl) ⟨462545, by rfl⟩ : syracuseStep 616727 = 925091) B925091
theorem B551191 : Blo 323837 551191 := bstep (se 1 (by rfl) ⟨413393, by rfl⟩ : syracuseStep 551191 = 826787) B826787
theorem B1042739 : Blo 323837 1042739 := bstep (se 1 (by rfl) ⟨782054, by rfl⟩ : syracuseStep 1042739 = 1564109) B1564109
theorem B485771 : Blo 323837 485771 := bstep (se 1 (by rfl) ⟨364328, by rfl⟩ : syracuseStep 485771 = 728657) B728657
theorem B485783 : Blo 323837 485783 := bstep (se 1 (by rfl) ⟨364337, by rfl⟩ : syracuseStep 485783 = 728675) B728675
theorem B485849 : Blo 323837 485849 := bstep (se 2 (by rfl) ⟨182193, by rfl⟩ : syracuseStep 485849 = 364387) B364387
theorem B5302745 : Blo 323837 5302745 := bstep (se 2 (by rfl) ⟨1988529, by rfl⟩ : syracuseStep 5302745 = 3977059) B3977059
theorem B1174061 : Blo 323837 1174061 := bstep (se 3 (by rfl) ⟨220136, by rfl⟩ : syracuseStep 1174061 = 440273) B440273
theorem B485963 : Blo 323837 485963 := bstep (se 1 (by rfl) ⟨364472, by rfl⟩ : syracuseStep 485963 = 728945) B728945
theorem B485975 : Blo 323837 485975 := bstep (se 1 (by rfl) ⟨364481, by rfl⟩ : syracuseStep 485975 = 728963) B728963
theorem B518807 : Blo 323837 518807 := bstep (se 1 (by rfl) ⟨389105, by rfl⟩ : syracuseStep 518807 = 778211) B778211
theorem B486041 : Blo 323837 486041 := bstep (se 2 (by rfl) ⟨182265, by rfl⟩ : syracuseStep 486041 = 364531) B364531
theorem B1239725 : Blo 323837 1239725 := bstep (se 3 (by rfl) ⟨232448, by rfl⟩ : syracuseStep 1239725 = 464897) B464897
theorem B715481 : Blo 323837 715481 := bstep (se 2 (by rfl) ⟨268305, by rfl⟩ : syracuseStep 715481 = 536611) B536611
theorem B486155 : Blo 323837 486155 := bstep (se 1 (by rfl) ⟨364616, by rfl⟩ : syracuseStep 486155 = 729233) B729233
theorem B486167 : Blo 323837 486167 := bstep (se 1 (by rfl) ⟨364625, by rfl⟩ : syracuseStep 486167 = 729251) B729251
theorem B486233 : Blo 323837 486233 := bstep (se 2 (by rfl) ⟨182337, by rfl⟩ : syracuseStep 486233 = 364675) B364675
theorem B551819 : Blo 323837 551819 := bstep (se 1 (by rfl) ⟨413864, by rfl⟩ : syracuseStep 551819 = 827729) B827729
theorem B617395 : Blo 323837 617395 := bstep (se 1 (by rfl) ⟨463046, by rfl⟩ : syracuseStep 617395 = 926093) B926093
theorem B486347 : Blo 323837 486347 := bstep (se 1 (by rfl) ⟨364760, by rfl⟩ : syracuseStep 486347 = 729521) B729521
theorem B486359 : Blo 323837 486359 := bstep (se 1 (by rfl) ⟨364769, by rfl⟩ : syracuseStep 486359 = 729539) B729539
theorem B1272793 : Blo 323837 1272793 := bstep (se 2 (by rfl) ⟨477297, by rfl⟩ : syracuseStep 1272793 = 954595) B954595
theorem B551947 : Blo 323837 551947 := bstep (se 1 (by rfl) ⟨413960, by rfl⟩ : syracuseStep 551947 = 827921) B827921
theorem B519191 : Blo 323837 519191 := bstep (se 1 (by rfl) ⟨389393, by rfl⟩ : syracuseStep 519191 = 778787) B778787
theorem B486425 : Blo 323837 486425 := bstep (se 2 (by rfl) ⟨182409, by rfl⟩ : syracuseStep 486425 = 364819) B364819
theorem B486539 : Blo 323837 486539 := bstep (se 1 (by rfl) ⟨364904, by rfl⟩ : syracuseStep 486539 = 729809) B729809
theorem B519319 : Blo 323837 519319 := bstep (se 1 (by rfl) ⟨389489, by rfl⟩ : syracuseStep 519319 = 778979) B778979
theorem B486551 : Blo 323837 486551 := bstep (se 1 (by rfl) ⟨364913, by rfl⟩ : syracuseStep 486551 = 729827) B729827
theorem B552089 : Blo 323837 552089 := bstep (se 2 (by rfl) ⟨207033, by rfl⟩ : syracuseStep 552089 = 414067) B414067
theorem B1633459 : Blo 323837 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B486617 : Blo 323837 486617 := bstep (se 2 (by rfl) ⟨182481, by rfl⟩ : syracuseStep 486617 = 364963) B364963
theorem B552217 : Blo 323837 552217 := bstep (se 2 (by rfl) ⟨207081, by rfl⟩ : syracuseStep 552217 = 414163) B414163
theorem B486731 : Blo 323837 486731 := bstep (se 1 (by rfl) ⟨365048, by rfl⟩ : syracuseStep 486731 = 730097) B730097
theorem B486743 : Blo 323837 486743 := bstep (se 1 (by rfl) ⟨365057, by rfl⟩ : syracuseStep 486743 = 730115) B730115
theorem B617843 : Blo 323837 617843 := bstep (se 1 (by rfl) ⟨463382, by rfl⟩ : syracuseStep 617843 = 926765) B926765
theorem B2780567 : Blo 323837 2780567 := bstep (se 1 (by rfl) ⟨2085425, by rfl⟩ : syracuseStep 2780567 = 4170851) B4170851
theorem B486809 : Blo 323837 486809 := bstep (se 2 (by rfl) ⟨182553, by rfl⟩ : syracuseStep 486809 = 365107) B365107
theorem B617881 : Blo 323837 617881 := bstep (se 2 (by rfl) ⟨231705, by rfl⟩ : syracuseStep 617881 = 463411) B463411
theorem B486923 : Blo 323837 486923 := bstep (se 1 (by rfl) ⟨365192, by rfl⟩ : syracuseStep 486923 = 730385) B730385
theorem B486935 : Blo 323837 486935 := bstep (se 1 (by rfl) ⟨365201, by rfl⟩ : syracuseStep 486935 = 730403) B730403
theorem B1044019 : Blo 323837 1044019 := bstep (se 1 (by rfl) ⟨783014, by rfl⟩ : syracuseStep 1044019 = 1566029) B1566029
theorem B1863233 : Blo 323837 1863233 := bstep (se 2 (by rfl) ⟨698712, by rfl⟩ : syracuseStep 1863233 = 1397425) B1397425
theorem B487001 : Blo 323837 487001 := bstep (se 2 (by rfl) ⟨182625, by rfl⟩ : syracuseStep 487001 = 365251) B365251
theorem B487115 : Blo 323837 487115 := bstep (se 1 (by rfl) ⟨365336, by rfl⟩ : syracuseStep 487115 = 730673) B730673
theorem B487127 : Blo 323837 487127 := bstep (se 1 (by rfl) ⟨365345, by rfl⟩ : syracuseStep 487127 = 730691) B730691
theorem B487193 : Blo 323837 487193 := bstep (se 2 (by rfl) ⟨182697, by rfl⟩ : syracuseStep 487193 = 365395) B365395
theorem B3534637 : Blo 323837 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B552791 : Blo 323837 552791 := bstep (se 1 (by rfl) ⟨414593, by rfl⟩ : syracuseStep 552791 = 829187) B829187
theorem B618329 : Blo 323837 618329 := bstep (se 2 (by rfl) ⟨231873, by rfl⟩ : syracuseStep 618329 = 463747) B463747
theorem B487307 : Blo 323837 487307 := bstep (se 1 (by rfl) ⟨365480, by rfl⟩ : syracuseStep 487307 = 730961) B730961
theorem B487319 : Blo 323837 487319 := bstep (se 1 (by rfl) ⟨365489, by rfl⟩ : syracuseStep 487319 = 730979) B730979
theorem B1863575 : Blo 323837 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B520139 : Blo 323837 520139 := bstep (se 1 (by rfl) ⟨390104, by rfl⟩ : syracuseStep 520139 = 780209) B780209
theorem B552919 : Blo 323837 552919 := bstep (se 1 (by rfl) ⟨414689, by rfl⟩ : syracuseStep 552919 = 829379) B829379
theorem B487385 : Blo 323837 487385 := bstep (se 2 (by rfl) ⟨182769, by rfl⟩ : syracuseStep 487385 = 365539) B365539
theorem B1241153 : Blo 323837 1241153 := bstep (se 2 (by rfl) ⟨465432, by rfl⟩ : syracuseStep 1241153 = 930865) B930865
theorem B520267 : Blo 323837 520267 := bstep (se 1 (by rfl) ⟨390200, by rfl⟩ : syracuseStep 520267 = 780401) B780401
theorem B487499 : Blo 323837 487499 := bstep (se 1 (by rfl) ⟨365624, by rfl⟩ : syracuseStep 487499 = 731249) B731249
theorem B487511 : Blo 323837 487511 := bstep (se 1 (by rfl) ⟨365633, by rfl⟩ : syracuseStep 487511 = 731267) B731267
theorem B2355331 : Blo 323837 2355331 := bstep (se 1 (by rfl) ⟨1766498, by rfl⟩ : syracuseStep 2355331 = 3532997) B3532997
theorem B6025367 : Blo 323837 6025367 := bstep (se 1 (by rfl) ⟨4519025, by rfl⟩ : syracuseStep 6025367 = 9038051) B9038051
theorem B487577 : Blo 323837 487577 := bstep (se 2 (by rfl) ⟨182841, by rfl⟩ : syracuseStep 487577 = 365683) B365683
theorem B323851 : Blo 323837 323851 := bstep (se 1 (by rfl) ⟨242888, by rfl⟩ : syracuseStep 323851 = 485777) B485777
theorem B487691 : Blo 323837 487691 := bstep (se 1 (by rfl) ⟨365768, by rfl⟩ : syracuseStep 487691 = 731537) B731537
theorem B323863 : Blo 323837 323863 := bstep (se 1 (by rfl) ⟨242897, by rfl⟩ : syracuseStep 323863 = 485795) B485795
theorem B487703 : Blo 323837 487703 := bstep (se 1 (by rfl) ⟨365777, by rfl⟩ : syracuseStep 487703 = 731555) B731555
theorem B323883 : Blo 323837 323883 := bstep (se 1 (by rfl) ⟨242912, by rfl⟩ : syracuseStep 323883 = 485825) B485825
theorem B323895 : Blo 323837 323895 := bstep (se 1 (by rfl) ⟨242921, by rfl⟩ : syracuseStep 323895 = 485843) B485843
theorem B323915 : Blo 323837 323915 := bstep (se 1 (by rfl) ⟨242936, by rfl⟩ : syracuseStep 323915 = 485873) B485873
theorem B323927 : Blo 323837 323927 := bstep (se 1 (by rfl) ⟨242945, by rfl⟩ : syracuseStep 323927 = 485891) B485891
theorem B487769 : Blo 323837 487769 := bstep (se 2 (by rfl) ⟨182913, by rfl⟩ : syracuseStep 487769 = 365827) B365827
theorem B323947 : Blo 323837 323947 := bstep (se 1 (by rfl) ⟨242960, by rfl⟩ : syracuseStep 323947 = 485921) B485921
theorem B323959 : Blo 323837 323959 := bstep (se 1 (by rfl) ⟨242969, by rfl⟩ : syracuseStep 323959 = 485939) B485939
theorem B323979 : Blo 323837 323979 := bstep (se 1 (by rfl) ⟨242984, by rfl⟩ : syracuseStep 323979 = 485969) B485969
theorem B323991 : Blo 323837 323991 := bstep (se 1 (by rfl) ⟨242993, by rfl⟩ : syracuseStep 323991 = 485987) B485987
theorem B324011 : Blo 323837 324011 := bstep (se 1 (by rfl) ⟨243008, by rfl⟩ : syracuseStep 324011 = 486017) B486017
theorem B324023 : Blo 323837 324023 := bstep (se 1 (by rfl) ⟨243017, by rfl⟩ : syracuseStep 324023 = 486035) B486035
theorem B324043 : Blo 323837 324043 := bstep (se 1 (by rfl) ⟨243032, by rfl⟩ : syracuseStep 324043 = 486065) B486065
theorem B487883 : Blo 323837 487883 := bstep (se 1 (by rfl) ⟨365912, by rfl⟩ : syracuseStep 487883 = 731825) B731825
theorem B324055 : Blo 323837 324055 := bstep (se 1 (by rfl) ⟨243041, by rfl⟩ : syracuseStep 324055 = 486083) B486083
theorem B487895 : Blo 323837 487895 := bstep (se 1 (by rfl) ⟨365921, by rfl⟩ : syracuseStep 487895 = 731843) B731843
theorem B324075 : Blo 323837 324075 := bstep (se 1 (by rfl) ⟨243056, by rfl⟩ : syracuseStep 324075 = 486113) B486113
theorem B324087 : Blo 323837 324087 := bstep (se 1 (by rfl) ⟨243065, by rfl⟩ : syracuseStep 324087 = 486131) B486131
theorem B324107 : Blo 323837 324107 := bstep (se 1 (by rfl) ⟨243080, by rfl⟩ : syracuseStep 324107 = 486161) B486161
theorem B324119 : Blo 323837 324119 := bstep (se 1 (by rfl) ⟨243089, by rfl⟩ : syracuseStep 324119 = 486179) B486179
theorem B487961 : Blo 323837 487961 := bstep (se 2 (by rfl) ⟨182985, by rfl⟩ : syracuseStep 487961 = 365971) B365971
theorem B324139 : Blo 323837 324139 := bstep (se 1 (by rfl) ⟨243104, by rfl⟩ : syracuseStep 324139 = 486209) B486209
theorem B324151 : Blo 323837 324151 := bstep (se 1 (by rfl) ⟨243113, by rfl⟩ : syracuseStep 324151 = 486227) B486227
theorem B619073 : Blo 323837 619073 := bstep (se 2 (by rfl) ⟨232152, by rfl⟩ : syracuseStep 619073 = 464305) B464305
theorem B324171 : Blo 323837 324171 := bstep (se 1 (by rfl) ⟨243128, by rfl⟩ : syracuseStep 324171 = 486257) B486257
theorem B324183 : Blo 323837 324183 := bstep (se 1 (by rfl) ⟨243137, by rfl⟩ : syracuseStep 324183 = 486275) B486275
theorem B324203 : Blo 323837 324203 := bstep (se 1 (by rfl) ⟨243152, by rfl⟩ : syracuseStep 324203 = 486305) B486305
theorem B324215 : Blo 323837 324215 := bstep (se 1 (by rfl) ⟨243161, by rfl⟩ : syracuseStep 324215 = 486323) B486323
theorem B324235 : Blo 323837 324235 := bstep (se 1 (by rfl) ⟨243176, by rfl⟩ : syracuseStep 324235 = 486353) B486353
theorem B488075 : Blo 323837 488075 := bstep (se 1 (by rfl) ⟨366056, by rfl⟩ : syracuseStep 488075 = 732113) B732113
theorem B324247 : Blo 323837 324247 := bstep (se 1 (by rfl) ⟨243185, by rfl⟩ : syracuseStep 324247 = 486371) B486371
theorem B488087 : Blo 323837 488087 := bstep (se 1 (by rfl) ⟨366065, by rfl⟩ : syracuseStep 488087 = 732131) B732131
theorem B324267 : Blo 323837 324267 := bstep (se 1 (by rfl) ⟨243200, by rfl⟩ : syracuseStep 324267 = 486401) B486401
theorem B1405619 : Blo 323837 1405619 := bstep (se 1 (by rfl) ⟨1054214, by rfl⟩ : syracuseStep 1405619 = 2108429) B2108429
theorem B324279 : Blo 323837 324279 := bstep (se 1 (by rfl) ⟨243209, by rfl⟩ : syracuseStep 324279 = 486419) B486419
theorem B324299 : Blo 323837 324299 := bstep (se 1 (by rfl) ⟨243224, by rfl⟩ : syracuseStep 324299 = 486449) B486449
theorem B324311 : Blo 323837 324311 := bstep (se 1 (by rfl) ⟨243233, by rfl⟩ : syracuseStep 324311 = 486467) B486467
theorem B488153 : Blo 323837 488153 := bstep (se 2 (by rfl) ⟨183057, by rfl⟩ : syracuseStep 488153 = 366115) B366115
theorem B324331 : Blo 323837 324331 := bstep (se 1 (by rfl) ⟨243248, by rfl⟩ : syracuseStep 324331 = 486497) B486497
theorem B324343 : Blo 323837 324343 := bstep (se 1 (by rfl) ⟨243257, by rfl⟩ : syracuseStep 324343 = 486515) B486515
theorem B324363 : Blo 323837 324363 := bstep (se 1 (by rfl) ⟨243272, by rfl⟩ : syracuseStep 324363 = 486545) B486545
theorem B324375 : Blo 323837 324375 := bstep (se 1 (by rfl) ⟨243281, by rfl⟩ : syracuseStep 324375 = 486563) B486563
theorem B324395 : Blo 323837 324395 := bstep (se 1 (by rfl) ⟨243296, by rfl⟩ : syracuseStep 324395 = 486593) B486593
theorem B324407 : Blo 323837 324407 := bstep (se 1 (by rfl) ⟨243305, by rfl⟩ : syracuseStep 324407 = 486611) B486611
theorem B324427 : Blo 323837 324427 := bstep (se 1 (by rfl) ⟨243320, by rfl⟩ : syracuseStep 324427 = 486641) B486641
theorem B488267 : Blo 323837 488267 := bstep (se 1 (by rfl) ⟨366200, by rfl⟩ : syracuseStep 488267 = 732401) B732401
theorem B619339 : Blo 323837 619339 := bstep (se 1 (by rfl) ⟨464504, by rfl⟩ : syracuseStep 619339 = 929009) B929009
theorem B324439 : Blo 323837 324439 := bstep (se 1 (by rfl) ⟨243329, by rfl⟩ : syracuseStep 324439 = 486659) B486659
theorem B488279 : Blo 323837 488279 := bstep (se 1 (by rfl) ⟨366209, by rfl⟩ : syracuseStep 488279 = 732419) B732419
theorem B324459 : Blo 323837 324459 := bstep (se 1 (by rfl) ⟨243344, by rfl⟩ : syracuseStep 324459 = 486689) B486689
theorem B324471 : Blo 323837 324471 := bstep (se 1 (by rfl) ⟨243353, by rfl⟩ : syracuseStep 324471 = 486707) B486707
theorem B324491 : Blo 323837 324491 := bstep (se 1 (by rfl) ⟨243368, by rfl⟩ : syracuseStep 324491 = 486737) B486737
theorem B324503 : Blo 323837 324503 := bstep (se 1 (by rfl) ⟨243377, by rfl⟩ : syracuseStep 324503 = 486755) B486755
theorem B488345 : Blo 323837 488345 := bstep (se 2 (by rfl) ⟨183129, by rfl⟩ : syracuseStep 488345 = 366259) B366259
theorem B324523 : Blo 323837 324523 := bstep (se 1 (by rfl) ⟨243392, by rfl⟩ : syracuseStep 324523 = 486785) B486785
theorem B324535 : Blo 323837 324535 := bstep (se 1 (by rfl) ⟨243401, by rfl⟩ : syracuseStep 324535 = 486803) B486803
theorem B324555 : Blo 323837 324555 := bstep (se 1 (by rfl) ⟨243416, by rfl⟩ : syracuseStep 324555 = 486833) B486833
theorem B324567 : Blo 323837 324567 := bstep (se 1 (by rfl) ⟨243425, by rfl⟩ : syracuseStep 324567 = 486851) B486851
theorem B324587 : Blo 323837 324587 := bstep (se 1 (by rfl) ⟨243440, by rfl⟩ : syracuseStep 324587 = 486881) B486881
theorem B324599 : Blo 323837 324599 := bstep (se 1 (by rfl) ⟨243449, by rfl⟩ : syracuseStep 324599 = 486899) B486899
theorem B324619 : Blo 323837 324619 := bstep (se 1 (by rfl) ⟨243464, by rfl⟩ : syracuseStep 324619 = 486929) B486929
theorem B488459 : Blo 323837 488459 := bstep (se 1 (by rfl) ⟨366344, by rfl⟩ : syracuseStep 488459 = 732689) B732689
theorem B324631 : Blo 323837 324631 := bstep (se 1 (by rfl) ⟨243473, by rfl⟩ : syracuseStep 324631 = 486947) B486947
theorem B488471 : Blo 323837 488471 := bstep (se 1 (by rfl) ⟨366353, by rfl⟩ : syracuseStep 488471 = 732707) B732707
theorem B1176599 : Blo 323837 1176599 := bstep (se 1 (by rfl) ⟨882449, by rfl⟩ : syracuseStep 1176599 = 1764899) B1764899
theorem B324651 : Blo 323837 324651 := bstep (se 1 (by rfl) ⟨243488, by rfl⟩ : syracuseStep 324651 = 486977) B486977
theorem B324663 : Blo 323837 324663 := bstep (se 1 (by rfl) ⟨243497, by rfl⟩ : syracuseStep 324663 = 486995) B486995
theorem B324683 : Blo 323837 324683 := bstep (se 1 (by rfl) ⟨243512, by rfl⟩ : syracuseStep 324683 = 487025) B487025
theorem B3175499 : Blo 323837 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B324695 : Blo 323837 324695 := bstep (se 1 (by rfl) ⟨243521, by rfl⟩ : syracuseStep 324695 = 487043) B487043
theorem B488537 : Blo 323837 488537 := bstep (se 2 (by rfl) ⟨183201, by rfl⟩ : syracuseStep 488537 = 366403) B366403
theorem B324715 : Blo 323837 324715 := bstep (se 1 (by rfl) ⟨243536, by rfl⟩ : syracuseStep 324715 = 487073) B487073
theorem B324727 : Blo 323837 324727 := bstep (se 1 (by rfl) ⟨243545, by rfl⟩ : syracuseStep 324727 = 487091) B487091
theorem B324747 : Blo 323837 324747 := bstep (se 1 (by rfl) ⟨243560, by rfl⟩ : syracuseStep 324747 = 487121) B487121
theorem B324759 : Blo 323837 324759 := bstep (se 1 (by rfl) ⟨243569, by rfl⟩ : syracuseStep 324759 = 487139) B487139
theorem B324779 : Blo 323837 324779 := bstep (se 1 (by rfl) ⟨243584, by rfl⟩ : syracuseStep 324779 = 487169) B487169
theorem B324791 : Blo 323837 324791 := bstep (se 1 (by rfl) ⟨243593, by rfl⟩ : syracuseStep 324791 = 487187) B487187
theorem B324811 : Blo 323837 324811 := bstep (se 1 (by rfl) ⟨243608, by rfl⟩ : syracuseStep 324811 = 487217) B487217
theorem B488651 : Blo 323837 488651 := bstep (se 1 (by rfl) ⟨366488, by rfl⟩ : syracuseStep 488651 = 732977) B732977
theorem B881867 : Blo 323837 881867 := bstep (se 1 (by rfl) ⟨661400, by rfl⟩ : syracuseStep 881867 = 1322801) B1322801
theorem B324823 : Blo 323837 324823 := bstep (se 1 (by rfl) ⟨243617, by rfl⟩ : syracuseStep 324823 = 487235) B487235
theorem B488663 : Blo 323837 488663 := bstep (se 1 (by rfl) ⟨366497, by rfl⟩ : syracuseStep 488663 = 732995) B732995
theorem B324843 : Blo 323837 324843 := bstep (se 1 (by rfl) ⟨243632, by rfl⟩ : syracuseStep 324843 = 487265) B487265
theorem B324855 : Blo 323837 324855 := bstep (se 1 (by rfl) ⟨243641, by rfl⟩ : syracuseStep 324855 = 487283) B487283
theorem B324875 : Blo 323837 324875 := bstep (se 1 (by rfl) ⟨243656, by rfl⟩ : syracuseStep 324875 = 487313) B487313
theorem B619787 : Blo 323837 619787 := bstep (se 1 (by rfl) ⟨464840, by rfl⟩ : syracuseStep 619787 = 929681) B929681
theorem B324887 : Blo 323837 324887 := bstep (se 1 (by rfl) ⟨243665, by rfl⟩ : syracuseStep 324887 = 487331) B487331
theorem B521497 : Blo 323837 521497 := bstep (se 2 (by rfl) ⟨195561, by rfl⟩ : syracuseStep 521497 = 391123) B391123
theorem B488729 : Blo 323837 488729 := bstep (se 2 (by rfl) ⟨183273, by rfl⟩ : syracuseStep 488729 = 366547) B366547
theorem B324907 : Blo 323837 324907 := bstep (se 1 (by rfl) ⟨243680, by rfl⟩ : syracuseStep 324907 = 487361) B487361
theorem B324919 : Blo 323837 324919 := bstep (se 1 (by rfl) ⟨243689, by rfl⟩ : syracuseStep 324919 = 487379) B487379
theorem B324939 : Blo 323837 324939 := bstep (se 1 (by rfl) ⟨243704, by rfl⟩ : syracuseStep 324939 = 487409) B487409
theorem B324951 : Blo 323837 324951 := bstep (se 1 (by rfl) ⟨243713, by rfl⟩ : syracuseStep 324951 = 487427) B487427
theorem B324971 : Blo 323837 324971 := bstep (se 1 (by rfl) ⟨243728, by rfl⟩ : syracuseStep 324971 = 487457) B487457
theorem B324983 : Blo 323837 324983 := bstep (se 1 (by rfl) ⟨243737, by rfl⟩ : syracuseStep 324983 = 487475) B487475
theorem B325003 : Blo 323837 325003 := bstep (se 1 (by rfl) ⟨243752, by rfl⟩ : syracuseStep 325003 = 487505) B487505
theorem B488843 : Blo 323837 488843 := bstep (se 1 (by rfl) ⟨366632, by rfl⟩ : syracuseStep 488843 = 733265) B733265
theorem B325015 : Blo 323837 325015 := bstep (se 1 (by rfl) ⟨243761, by rfl⟩ : syracuseStep 325015 = 487523) B487523
theorem B488855 : Blo 323837 488855 := bstep (se 1 (by rfl) ⟨366641, by rfl⟩ : syracuseStep 488855 = 733283) B733283
theorem B325035 : Blo 323837 325035 := bstep (se 1 (by rfl) ⟨243776, by rfl⟩ : syracuseStep 325035 = 487553) B487553
theorem B325047 : Blo 323837 325047 := bstep (se 1 (by rfl) ⟨243785, by rfl⟩ : syracuseStep 325047 = 487571) B487571
theorem B619969 : Blo 323837 619969 := bstep (se 2 (by rfl) ⟨232488, by rfl⟩ : syracuseStep 619969 = 464977) B464977
theorem B325067 : Blo 323837 325067 := bstep (se 1 (by rfl) ⟨243800, by rfl⟩ : syracuseStep 325067 = 487601) B487601
theorem B325079 : Blo 323837 325079 := bstep (se 1 (by rfl) ⟨243809, by rfl⟩ : syracuseStep 325079 = 487619) B487619
theorem B488921 : Blo 323837 488921 := bstep (se 2 (by rfl) ⟨183345, by rfl⟩ : syracuseStep 488921 = 366691) B366691
theorem B325099 : Blo 323837 325099 := bstep (se 1 (by rfl) ⟨243824, by rfl⟩ : syracuseStep 325099 = 487649) B487649
theorem B325111 : Blo 323837 325111 := bstep (se 1 (by rfl) ⟨243833, by rfl⟩ : syracuseStep 325111 = 487667) B487667
theorem B325131 : Blo 323837 325131 := bstep (se 1 (by rfl) ⟨243848, by rfl⟩ : syracuseStep 325131 = 487697) B487697
theorem B1242641 : Blo 323837 1242641 := bstep (se 2 (by rfl) ⟨465990, by rfl⟩ : syracuseStep 1242641 = 931981) B931981
theorem B325143 : Blo 323837 325143 := bstep (se 1 (by rfl) ⟨243857, by rfl⟩ : syracuseStep 325143 = 487715) B487715
theorem B325163 : Blo 323837 325163 := bstep (se 1 (by rfl) ⟨243872, by rfl⟩ : syracuseStep 325163 = 487745) B487745
theorem B325175 : Blo 323837 325175 := bstep (se 1 (by rfl) ⟨243881, by rfl⟩ : syracuseStep 325175 = 487763) B487763
theorem B783937 : Blo 323837 783937 := bstep (se 2 (by rfl) ⟨293976, by rfl⟩ : syracuseStep 783937 = 587953) B587953
theorem B325195 : Blo 323837 325195 := bstep (se 1 (by rfl) ⟨243896, by rfl⟩ : syracuseStep 325195 = 487793) B487793
theorem B489035 : Blo 323837 489035 := bstep (se 1 (by rfl) ⟨366776, by rfl⟩ : syracuseStep 489035 = 733553) B733553
theorem B325207 : Blo 323837 325207 := bstep (se 1 (by rfl) ⟨243905, by rfl⟩ : syracuseStep 325207 = 487811) B487811
theorem B489047 : Blo 323837 489047 := bstep (se 1 (by rfl) ⟨366785, by rfl⟩ : syracuseStep 489047 = 733571) B733571
theorem B325227 : Blo 323837 325227 := bstep (se 1 (by rfl) ⟨243920, by rfl⟩ : syracuseStep 325227 = 487841) B487841
theorem B325239 : Blo 323837 325239 := bstep (se 1 (by rfl) ⟨243929, by rfl⟩ : syracuseStep 325239 = 487859) B487859
theorem B325259 : Blo 323837 325259 := bstep (se 1 (by rfl) ⟨243944, by rfl⟩ : syracuseStep 325259 = 487889) B487889
theorem B325271 : Blo 323837 325271 := bstep (se 1 (by rfl) ⟨243953, by rfl⟩ : syracuseStep 325271 = 487907) B487907
theorem B489113 : Blo 323837 489113 := bstep (se 2 (by rfl) ⟨183417, by rfl⟩ : syracuseStep 489113 = 366835) B366835
theorem B325291 : Blo 323837 325291 := bstep (se 1 (by rfl) ⟨243968, by rfl⟩ : syracuseStep 325291 = 487937) B487937
theorem B325303 : Blo 323837 325303 := bstep (se 1 (by rfl) ⟨243977, by rfl⟩ : syracuseStep 325303 = 487955) B487955
theorem B325323 : Blo 323837 325323 := bstep (se 1 (by rfl) ⟨243992, by rfl⟩ : syracuseStep 325323 = 487985) B487985
theorem B325335 : Blo 323837 325335 := bstep (se 1 (by rfl) ⟨244001, by rfl⟩ : syracuseStep 325335 = 488003) B488003
theorem B325355 : Blo 323837 325355 := bstep (se 1 (by rfl) ⟨244016, by rfl⟩ : syracuseStep 325355 = 488033) B488033
theorem B325367 : Blo 323837 325367 := bstep (se 1 (by rfl) ⟨244025, by rfl⟩ : syracuseStep 325367 = 488051) B488051
theorem B325387 : Blo 323837 325387 := bstep (se 1 (by rfl) ⟨244040, by rfl⟩ : syracuseStep 325387 = 488081) B488081
theorem B489227 : Blo 323837 489227 := bstep (se 1 (by rfl) ⟨366920, by rfl⟩ : syracuseStep 489227 = 733841) B733841
theorem B325399 : Blo 323837 325399 := bstep (se 1 (by rfl) ⟨244049, by rfl⟩ : syracuseStep 325399 = 488099) B488099
theorem B489239 : Blo 323837 489239 := bstep (se 1 (by rfl) ⟨366929, by rfl⟩ : syracuseStep 489239 = 733859) B733859
theorem B620311 : Blo 323837 620311 := bstep (se 1 (by rfl) ⟨465233, by rfl⟩ : syracuseStep 620311 = 930467) B930467
theorem B325419 : Blo 323837 325419 := bstep (se 1 (by rfl) ⟨244064, by rfl⟩ : syracuseStep 325419 = 488129) B488129
theorem B325431 : Blo 323837 325431 := bstep (se 1 (by rfl) ⟨244073, by rfl⟩ : syracuseStep 325431 = 488147) B488147
theorem B1767233 : Blo 323837 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B325451 : Blo 323837 325451 := bstep (se 1 (by rfl) ⟨244088, by rfl⟩ : syracuseStep 325451 = 488177) B488177
theorem B325463 : Blo 323837 325463 := bstep (se 1 (by rfl) ⟨244097, by rfl⟩ : syracuseStep 325463 = 488195) B488195
theorem B489305 : Blo 323837 489305 := bstep (se 2 (by rfl) ⟨183489, by rfl⟩ : syracuseStep 489305 = 366979) B366979
theorem B325483 : Blo 323837 325483 := bstep (se 1 (by rfl) ⟨244112, by rfl⟩ : syracuseStep 325483 = 488225) B488225
theorem B325495 : Blo 323837 325495 := bstep (se 1 (by rfl) ⟨244121, by rfl⟩ : syracuseStep 325495 = 488243) B488243
theorem B325515 : Blo 323837 325515 := bstep (se 1 (by rfl) ⟨244136, by rfl⟩ : syracuseStep 325515 = 488273) B488273
theorem B325527 : Blo 323837 325527 := bstep (se 1 (by rfl) ⟨244145, by rfl⟩ : syracuseStep 325527 = 488291) B488291
theorem B325547 : Blo 323837 325547 := bstep (se 1 (by rfl) ⟨244160, by rfl⟩ : syracuseStep 325547 = 488321) B488321
theorem B1177523 : Blo 323837 1177523 := bstep (se 1 (by rfl) ⟨883142, by rfl⟩ : syracuseStep 1177523 = 1766285) B1766285
theorem B325559 : Blo 323837 325559 := bstep (se 1 (by rfl) ⟨244169, by rfl⟩ : syracuseStep 325559 = 488339) B488339
theorem B325579 : Blo 323837 325579 := bstep (se 1 (by rfl) ⟨244184, by rfl⟩ : syracuseStep 325579 = 488369) B488369
theorem B489419 : Blo 323837 489419 := bstep (se 1 (by rfl) ⟨367064, by rfl⟩ : syracuseStep 489419 = 734129) B734129
theorem B325591 : Blo 323837 325591 := bstep (se 1 (by rfl) ⟨244193, by rfl⟩ : syracuseStep 325591 = 488387) B488387
theorem B489431 : Blo 323837 489431 := bstep (se 1 (by rfl) ⟨367073, by rfl⟩ : syracuseStep 489431 = 734147) B734147
theorem B1243097 : Blo 323837 1243097 := bstep (se 2 (by rfl) ⟨466161, by rfl⟩ : syracuseStep 1243097 = 932323) B932323
theorem B325611 : Blo 323837 325611 := bstep (se 1 (by rfl) ⟨244208, by rfl⟩ : syracuseStep 325611 = 488417) B488417
theorem B620531 : Blo 323837 620531 := bstep (se 1 (by rfl) ⟨465398, by rfl⟩ : syracuseStep 620531 = 930797) B930797
theorem B325623 : Blo 323837 325623 := bstep (se 1 (by rfl) ⟨244217, by rfl⟩ : syracuseStep 325623 = 488435) B488435
theorem B325643 : Blo 323837 325643 := bstep (se 1 (by rfl) ⟨244232, by rfl⟩ : syracuseStep 325643 = 488465) B488465
theorem B555031 : Blo 323837 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B325655 : Blo 323837 325655 := bstep (se 1 (by rfl) ⟨244241, by rfl⟩ : syracuseStep 325655 = 488483) B488483
theorem B489497 : Blo 323837 489497 := bstep (se 2 (by rfl) ⟨183561, by rfl⟩ : syracuseStep 489497 = 367123) B367123
theorem B325675 : Blo 323837 325675 := bstep (se 1 (by rfl) ⟨244256, by rfl⟩ : syracuseStep 325675 = 488513) B488513
theorem B325687 : Blo 323837 325687 := bstep (se 1 (by rfl) ⟨244265, by rfl⟩ : syracuseStep 325687 = 488531) B488531
theorem B325707 : Blo 323837 325707 := bstep (se 1 (by rfl) ⟨244280, by rfl⟩ : syracuseStep 325707 = 488561) B488561
theorem B325719 : Blo 323837 325719 := bstep (se 1 (by rfl) ⟨244289, by rfl⟩ : syracuseStep 325719 = 488579) B488579
theorem B325739 : Blo 323837 325739 := bstep (se 1 (by rfl) ⟨244304, by rfl⟩ : syracuseStep 325739 = 488609) B488609
theorem B325751 : Blo 323837 325751 := bstep (se 1 (by rfl) ⟨244313, by rfl⟩ : syracuseStep 325751 = 488627) B488627
theorem B325771 : Blo 323837 325771 := bstep (se 1 (by rfl) ⟨244328, by rfl⟩ : syracuseStep 325771 = 488657) B488657
theorem B489611 : Blo 323837 489611 := bstep (se 1 (by rfl) ⟨367208, by rfl⟩ : syracuseStep 489611 = 734417) B734417
theorem B325783 : Blo 323837 325783 := bstep (se 1 (by rfl) ⟨244337, by rfl⟩ : syracuseStep 325783 = 488675) B488675
theorem B489623 : Blo 323837 489623 := bstep (se 1 (by rfl) ⟨367217, by rfl⟩ : syracuseStep 489623 = 734435) B734435
theorem B1177751 : Blo 323837 1177751 := bstep (se 1 (by rfl) ⟨883313, by rfl⟩ : syracuseStep 1177751 = 1766627) B1766627
theorem B6715543 : Blo 323837 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B325803 : Blo 323837 325803 := bstep (se 1 (by rfl) ⟨244352, by rfl⟩ : syracuseStep 325803 = 488705) B488705
theorem B1243309 : Blo 323837 1243309 := bstep (se 3 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 1243309 = 466241) B466241
theorem B325815 : Blo 323837 325815 := bstep (se 1 (by rfl) ⟨244361, by rfl⟩ : syracuseStep 325815 = 488723) B488723
theorem B325835 : Blo 323837 325835 := bstep (se 1 (by rfl) ⟨244376, by rfl⟩ : syracuseStep 325835 = 488753) B488753
theorem B325847 : Blo 323837 325847 := bstep (se 1 (by rfl) ⟨244385, by rfl⟩ : syracuseStep 325847 = 488771) B488771
theorem B620759 : Blo 323837 620759 := bstep (se 1 (by rfl) ⟨465569, by rfl⟩ : syracuseStep 620759 = 931139) B931139
theorem B489689 : Blo 323837 489689 := bstep (se 2 (by rfl) ⟨183633, by rfl⟩ : syracuseStep 489689 = 367267) B367267
theorem B325867 : Blo 323837 325867 := bstep (se 1 (by rfl) ⟨244400, by rfl⟩ : syracuseStep 325867 = 488801) B488801
theorem B325879 : Blo 323837 325879 := bstep (se 1 (by rfl) ⟨244409, by rfl⟩ : syracuseStep 325879 = 488819) B488819
theorem B325899 : Blo 323837 325899 := bstep (se 1 (by rfl) ⟨244424, by rfl⟩ : syracuseStep 325899 = 488849) B488849
theorem B325911 : Blo 323837 325911 := bstep (se 1 (by rfl) ⟨244433, by rfl⟩ : syracuseStep 325911 = 488867) B488867
theorem B325931 : Blo 323837 325931 := bstep (se 1 (by rfl) ⟨244448, by rfl⟩ : syracuseStep 325931 = 488897) B488897
theorem B325943 : Blo 323837 325943 := bstep (se 1 (by rfl) ⟨244457, by rfl⟩ : syracuseStep 325943 = 488915) B488915
theorem B325963 : Blo 323837 325963 := bstep (se 1 (by rfl) ⟨244472, by rfl⟩ : syracuseStep 325963 = 488945) B488945
theorem B489803 : Blo 323837 489803 := bstep (se 1 (by rfl) ⟨367352, by rfl⟩ : syracuseStep 489803 = 734705) B734705
theorem B2357579 : Blo 323837 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B325975 : Blo 323837 325975 := bstep (se 1 (by rfl) ⟨244481, by rfl⟩ : syracuseStep 325975 = 488963) B488963
theorem B489815 : Blo 323837 489815 := bstep (se 1 (by rfl) ⟨367361, by rfl⟩ : syracuseStep 489815 = 734723) B734723
theorem B325995 : Blo 323837 325995 := bstep (se 1 (by rfl) ⟨244496, by rfl⟩ : syracuseStep 325995 = 488993) B488993
theorem B326007 : Blo 323837 326007 := bstep (se 1 (by rfl) ⟨244505, by rfl⟩ : syracuseStep 326007 = 489011) B489011
theorem B326027 : Blo 323837 326027 := bstep (se 1 (by rfl) ⟨244520, by rfl⟩ : syracuseStep 326027 = 489041) B489041
theorem B326039 : Blo 323837 326039 := bstep (se 1 (by rfl) ⟨244529, by rfl⟩ : syracuseStep 326039 = 489059) B489059
theorem B489881 : Blo 323837 489881 := bstep (se 2 (by rfl) ⟨183705, by rfl⟩ : syracuseStep 489881 = 367411) B367411
theorem B326059 : Blo 323837 326059 := bstep (se 1 (by rfl) ⟨244544, by rfl⟩ : syracuseStep 326059 = 489089) B489089
theorem B3733937 : Blo 323837 3733937 := bstep (se 2 (by rfl) ⟨1400226, by rfl⟩ : syracuseStep 3733937 = 2800453) B2800453
theorem B326071 : Blo 323837 326071 := bstep (se 1 (by rfl) ⟨244553, by rfl⟩ : syracuseStep 326071 = 489107) B489107
theorem B326091 : Blo 323837 326091 := bstep (se 1 (by rfl) ⟨244568, by rfl⟩ : syracuseStep 326091 = 489137) B489137
theorem B326103 : Blo 323837 326103 := bstep (se 1 (by rfl) ⟨244577, by rfl⟩ : syracuseStep 326103 = 489155) B489155
theorem B2980313 : Blo 323837 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B621017 : Blo 323837 621017 := bstep (se 2 (by rfl) ⟨232881, by rfl⟩ : syracuseStep 621017 = 465763) B465763
theorem B1243613 : Blo 323837 1243613 := bstep (se 3 (by rfl) ⟨233177, by rfl⟩ : syracuseStep 1243613 = 466355) B466355
theorem B326123 : Blo 323837 326123 := bstep (se 1 (by rfl) ⟨244592, by rfl⟩ : syracuseStep 326123 = 489185) B489185
theorem B326135 : Blo 323837 326135 := bstep (se 1 (by rfl) ⟨244601, by rfl⟩ : syracuseStep 326135 = 489203) B489203
theorem B326155 : Blo 323837 326155 := bstep (se 1 (by rfl) ⟨244616, by rfl⟩ : syracuseStep 326155 = 489233) B489233
theorem B489995 : Blo 323837 489995 := bstep (se 1 (by rfl) ⟨367496, by rfl⟩ : syracuseStep 489995 = 734993) B734993
theorem B7043597 : Blo 323837 7043597 := bstep (se 3 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 7043597 = 2641349) B2641349
theorem B326167 : Blo 323837 326167 := bstep (se 1 (by rfl) ⟨244625, by rfl⟩ : syracuseStep 326167 = 489251) B489251
theorem B490007 : Blo 323837 490007 := bstep (se 1 (by rfl) ⟨367505, by rfl⟩ : syracuseStep 490007 = 735011) B735011
theorem B326187 : Blo 323837 326187 := bstep (se 1 (by rfl) ⟨244640, by rfl⟩ : syracuseStep 326187 = 489281) B489281
theorem B1604141 : Blo 323837 1604141 := bstep (se 3 (by rfl) ⟨300776, by rfl⟩ : syracuseStep 1604141 = 601553) B601553
theorem B326199 : Blo 323837 326199 := bstep (se 1 (by rfl) ⟨244649, by rfl⟩ : syracuseStep 326199 = 489299) B489299
theorem B326219 : Blo 323837 326219 := bstep (se 1 (by rfl) ⟨244664, by rfl⟩ : syracuseStep 326219 = 489329) B489329
theorem B326231 : Blo 323837 326231 := bstep (se 1 (by rfl) ⟨244673, by rfl⟩ : syracuseStep 326231 = 489347) B489347
theorem B490073 : Blo 323837 490073 := bstep (se 2 (by rfl) ⟨183777, by rfl⟩ : syracuseStep 490073 = 367555) B367555
theorem B1178201 : Blo 323837 1178201 := bstep (se 2 (by rfl) ⟨441825, by rfl⟩ : syracuseStep 1178201 = 883651) B883651
theorem B326251 : Blo 323837 326251 := bstep (se 1 (by rfl) ⟨244688, by rfl⟩ : syracuseStep 326251 = 489377) B489377
theorem B326263 : Blo 323837 326263 := bstep (se 1 (by rfl) ⟨244697, by rfl⟩ : syracuseStep 326263 = 489395) B489395
theorem B326283 : Blo 323837 326283 := bstep (se 1 (by rfl) ⟨244712, by rfl⟩ : syracuseStep 326283 = 489425) B489425
theorem B326295 : Blo 323837 326295 := bstep (se 1 (by rfl) ⟨244721, by rfl⟩ : syracuseStep 326295 = 489443) B489443
theorem B326315 : Blo 323837 326315 := bstep (se 1 (by rfl) ⟨244736, by rfl⟩ : syracuseStep 326315 = 489473) B489473
theorem B326327 : Blo 323837 326327 := bstep (se 1 (by rfl) ⟨244745, by rfl⟩ : syracuseStep 326327 = 489491) B489491
theorem B326347 : Blo 323837 326347 := bstep (se 1 (by rfl) ⟨244760, by rfl⟩ : syracuseStep 326347 = 489521) B489521
theorem B490187 : Blo 323837 490187 := bstep (se 1 (by rfl) ⟨367640, by rfl⟩ : syracuseStep 490187 = 735281) B735281
theorem B1178315 : Blo 323837 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B326359 : Blo 323837 326359 := bstep (se 1 (by rfl) ⟨244769, by rfl⟩ : syracuseStep 326359 = 489539) B489539
theorem B490199 : Blo 323837 490199 := bstep (se 1 (by rfl) ⟨367649, by rfl⟩ : syracuseStep 490199 = 735299) B735299
theorem B326379 : Blo 323837 326379 := bstep (se 1 (by rfl) ⟨244784, by rfl⟩ : syracuseStep 326379 = 489569) B489569
theorem B326391 : Blo 323837 326391 := bstep (se 1 (by rfl) ⟨244793, by rfl⟩ : syracuseStep 326391 = 489587) B489587
theorem B326411 : Blo 323837 326411 := bstep (se 1 (by rfl) ⟨244808, by rfl⟩ : syracuseStep 326411 = 489617) B489617
theorem B326423 : Blo 323837 326423 := bstep (se 1 (by rfl) ⟨244817, by rfl⟩ : syracuseStep 326423 = 489635) B489635
theorem B490265 : Blo 323837 490265 := bstep (se 2 (by rfl) ⟨183849, by rfl⟩ : syracuseStep 490265 = 367699) B367699
theorem B326443 : Blo 323837 326443 := bstep (se 1 (by rfl) ⟨244832, by rfl⟩ : syracuseStep 326443 = 489665) B489665
theorem B326455 : Blo 323837 326455 := bstep (se 1 (by rfl) ⟨244841, by rfl⟩ : syracuseStep 326455 = 489683) B489683
theorem B326475 : Blo 323837 326475 := bstep (se 1 (by rfl) ⟨244856, by rfl⟩ : syracuseStep 326475 = 489713) B489713
theorem B326487 : Blo 323837 326487 := bstep (se 1 (by rfl) ⟨244865, by rfl⟩ : syracuseStep 326487 = 489731) B489731
theorem B326507 : Blo 323837 326507 := bstep (se 1 (by rfl) ⟨244880, by rfl⟩ : syracuseStep 326507 = 489761) B489761
theorem B621427 : Blo 323837 621427 := bstep (se 1 (by rfl) ⟨466070, by rfl⟩ : syracuseStep 621427 = 932141) B932141
theorem B326519 : Blo 323837 326519 := bstep (se 1 (by rfl) ⟨244889, by rfl⟩ : syracuseStep 326519 = 489779) B489779
theorem B326539 : Blo 323837 326539 := bstep (se 1 (by rfl) ⟨244904, by rfl⟩ : syracuseStep 326539 = 489809) B489809
theorem B490379 : Blo 323837 490379 := bstep (se 1 (by rfl) ⟨367784, by rfl⟩ : syracuseStep 490379 = 735569) B735569
theorem B326551 : Blo 323837 326551 := bstep (se 1 (by rfl) ⟨244913, by rfl⟩ : syracuseStep 326551 = 489827) B489827
theorem B490391 : Blo 323837 490391 := bstep (se 1 (by rfl) ⟨367793, by rfl⟩ : syracuseStep 490391 = 735587) B735587
theorem B326571 : Blo 323837 326571 := bstep (se 1 (by rfl) ⟨244928, by rfl⟩ : syracuseStep 326571 = 489857) B489857
theorem B326583 : Blo 323837 326583 := bstep (se 1 (by rfl) ⟨244937, by rfl⟩ : syracuseStep 326583 = 489875) B489875
theorem B326603 : Blo 323837 326603 := bstep (se 1 (by rfl) ⟨244952, by rfl⟩ : syracuseStep 326603 = 489905) B489905
theorem B326615 : Blo 323837 326615 := bstep (se 1 (by rfl) ⟨244961, by rfl⟩ : syracuseStep 326615 = 489923) B489923
theorem B490457 : Blo 323837 490457 := bstep (se 2 (by rfl) ⟨183921, by rfl⟩ : syracuseStep 490457 = 367843) B367843
theorem B326635 : Blo 323837 326635 := bstep (se 1 (by rfl) ⟨244976, by rfl⟩ : syracuseStep 326635 = 489953) B489953
theorem B326647 : Blo 323837 326647 := bstep (se 1 (by rfl) ⟨244985, by rfl⟩ : syracuseStep 326647 = 489971) B489971
theorem B326667 : Blo 323837 326667 := bstep (se 1 (by rfl) ⟨245000, by rfl⟩ : syracuseStep 326667 = 490001) B490001
theorem B326679 : Blo 323837 326679 := bstep (se 1 (by rfl) ⟨245009, by rfl⟩ : syracuseStep 326679 = 490019) B490019
theorem B326699 : Blo 323837 326699 := bstep (se 1 (by rfl) ⟨245024, by rfl⟩ : syracuseStep 326699 = 490049) B490049
theorem B1178675 : Blo 323837 1178675 := bstep (se 1 (by rfl) ⟨884006, by rfl⟩ : syracuseStep 1178675 = 1768013) B1768013
theorem B326711 : Blo 323837 326711 := bstep (se 1 (by rfl) ⟨245033, by rfl⟩ : syracuseStep 326711 = 490067) B490067
theorem B326731 : Blo 323837 326731 := bstep (se 1 (by rfl) ⟨245048, by rfl⟩ : syracuseStep 326731 = 490097) B490097
theorem B490571 : Blo 323837 490571 := bstep (se 1 (by rfl) ⟨367928, by rfl⟩ : syracuseStep 490571 = 735857) B735857
theorem B326743 : Blo 323837 326743 := bstep (se 1 (by rfl) ⟨245057, by rfl⟩ : syracuseStep 326743 = 490115) B490115
theorem B490583 : Blo 323837 490583 := bstep (se 1 (by rfl) ⟨367937, by rfl⟩ : syracuseStep 490583 = 735875) B735875
theorem B326763 : Blo 323837 326763 := bstep (se 1 (by rfl) ⟨245072, by rfl⟩ : syracuseStep 326763 = 490145) B490145
theorem B326775 : Blo 323837 326775 := bstep (se 1 (by rfl) ⟨245081, by rfl⟩ : syracuseStep 326775 = 490163) B490163
theorem B326795 : Blo 323837 326795 := bstep (se 1 (by rfl) ⟨245096, by rfl⟩ : syracuseStep 326795 = 490193) B490193
theorem B326807 : Blo 323837 326807 := bstep (se 1 (by rfl) ⟨245105, by rfl⟩ : syracuseStep 326807 = 490211) B490211
theorem B490649 : Blo 323837 490649 := bstep (se 2 (by rfl) ⟨183993, by rfl⟩ : syracuseStep 490649 = 367987) B367987
theorem B326827 : Blo 323837 326827 := bstep (se 1 (by rfl) ⟨245120, by rfl⟩ : syracuseStep 326827 = 490241) B490241
theorem B326839 : Blo 323837 326839 := bstep (se 1 (by rfl) ⟨245129, by rfl⟩ : syracuseStep 326839 = 490259) B490259
theorem B326859 : Blo 323837 326859 := bstep (se 1 (by rfl) ⟨245144, by rfl⟩ : syracuseStep 326859 = 490289) B490289
theorem B326871 : Blo 323837 326871 := bstep (se 1 (by rfl) ⟨245153, by rfl⟩ : syracuseStep 326871 = 490307) B490307
theorem B326891 : Blo 323837 326891 := bstep (se 1 (by rfl) ⟨245168, by rfl⟩ : syracuseStep 326891 = 490337) B490337
theorem B326903 : Blo 323837 326903 := bstep (se 1 (by rfl) ⟨245177, by rfl⟩ : syracuseStep 326903 = 490355) B490355
theorem B326923 : Blo 323837 326923 := bstep (se 1 (by rfl) ⟨245192, by rfl⟩ : syracuseStep 326923 = 490385) B490385
theorem B490763 : Blo 323837 490763 := bstep (se 1 (by rfl) ⟨368072, by rfl⟩ : syracuseStep 490763 = 736145) B736145
theorem B326935 : Blo 323837 326935 := bstep (se 1 (by rfl) ⟨245201, by rfl⟩ : syracuseStep 326935 = 490403) B490403
theorem B490775 : Blo 323837 490775 := bstep (se 1 (by rfl) ⟨368081, by rfl⟩ : syracuseStep 490775 = 736163) B736163
theorem B326955 : Blo 323837 326955 := bstep (se 1 (by rfl) ⟨245216, by rfl⟩ : syracuseStep 326955 = 490433) B490433
theorem B326967 : Blo 323837 326967 := bstep (se 1 (by rfl) ⟨245225, by rfl⟩ : syracuseStep 326967 = 490451) B490451
theorem B326987 : Blo 323837 326987 := bstep (se 1 (by rfl) ⟨245240, by rfl⟩ : syracuseStep 326987 = 490481) B490481
theorem B326999 : Blo 323837 326999 := bstep (se 1 (by rfl) ⟨245249, by rfl⟩ : syracuseStep 326999 = 490499) B490499
theorem B490841 : Blo 323837 490841 := bstep (se 2 (by rfl) ⟨184065, by rfl⟩ : syracuseStep 490841 = 368131) B368131
theorem B621913 : Blo 323837 621913 := bstep (se 2 (by rfl) ⟨233217, by rfl⟩ : syracuseStep 621913 = 466435) B466435
theorem B327019 : Blo 323837 327019 := bstep (se 1 (by rfl) ⟨245264, by rfl⟩ : syracuseStep 327019 = 490529) B490529
theorem B327031 : Blo 323837 327031 := bstep (se 1 (by rfl) ⟨245273, by rfl⟩ : syracuseStep 327031 = 490547) B490547
theorem B327051 : Blo 323837 327051 := bstep (se 1 (by rfl) ⟨245288, by rfl⟩ : syracuseStep 327051 = 490577) B490577
theorem B327063 : Blo 323837 327063 := bstep (se 1 (by rfl) ⟨245297, by rfl⟩ : syracuseStep 327063 = 490595) B490595
theorem B327083 : Blo 323837 327083 := bstep (se 1 (by rfl) ⟨245312, by rfl⟩ : syracuseStep 327083 = 490625) B490625
theorem B327095 : Blo 323837 327095 := bstep (se 1 (by rfl) ⟨245321, by rfl⟩ : syracuseStep 327095 = 490643) B490643
theorem B327115 : Blo 323837 327115 := bstep (se 1 (by rfl) ⟨245336, by rfl⟩ : syracuseStep 327115 = 490673) B490673
theorem B490955 : Blo 323837 490955 := bstep (se 1 (by rfl) ⟨368216, by rfl⟩ : syracuseStep 490955 = 736433) B736433
theorem B327127 : Blo 323837 327127 := bstep (se 1 (by rfl) ⟨245345, by rfl⟩ : syracuseStep 327127 = 490691) B490691
theorem B490967 : Blo 323837 490967 := bstep (se 1 (by rfl) ⟨368225, by rfl⟩ : syracuseStep 490967 = 736451) B736451
theorem B327147 : Blo 323837 327147 := bstep (se 1 (by rfl) ⟨245360, by rfl⟩ : syracuseStep 327147 = 490721) B490721
theorem B327159 : Blo 323837 327159 := bstep (se 1 (by rfl) ⟨245369, by rfl⟩ : syracuseStep 327159 = 490739) B490739
theorem B327179 : Blo 323837 327179 := bstep (se 1 (by rfl) ⟨245384, by rfl⟩ : syracuseStep 327179 = 490769) B490769
theorem B327191 : Blo 323837 327191 := bstep (se 1 (by rfl) ⟨245393, by rfl⟩ : syracuseStep 327191 = 490787) B490787
theorem B491033 : Blo 323837 491033 := bstep (se 2 (by rfl) ⟨184137, by rfl⟩ : syracuseStep 491033 = 368275) B368275
theorem B327211 : Blo 323837 327211 := bstep (se 1 (by rfl) ⟨245408, by rfl⟩ : syracuseStep 327211 = 490817) B490817
theorem B327223 : Blo 323837 327223 := bstep (se 1 (by rfl) ⟨245417, by rfl⟩ : syracuseStep 327223 = 490835) B490835
theorem B327243 : Blo 323837 327243 := bstep (se 1 (by rfl) ⟨245432, by rfl⟩ : syracuseStep 327243 = 490865) B490865
theorem B327255 : Blo 323837 327255 := bstep (se 1 (by rfl) ⟨245441, by rfl⟩ : syracuseStep 327255 = 490883) B490883
theorem B327275 : Blo 323837 327275 := bstep (se 1 (by rfl) ⟨245456, by rfl⟩ : syracuseStep 327275 = 490913) B490913
theorem B327287 : Blo 323837 327287 := bstep (se 1 (by rfl) ⟨245465, by rfl⟩ : syracuseStep 327287 = 490931) B490931
theorem B327307 : Blo 323837 327307 := bstep (se 1 (by rfl) ⟨245480, by rfl⟩ : syracuseStep 327307 = 490961) B490961
theorem B491147 : Blo 323837 491147 := bstep (se 1 (by rfl) ⟨368360, by rfl⟩ : syracuseStep 491147 = 736721) B736721
theorem B327319 : Blo 323837 327319 := bstep (se 1 (by rfl) ⟨245489, by rfl⟩ : syracuseStep 327319 = 490979) B490979
theorem B491159 : Blo 323837 491159 := bstep (se 1 (by rfl) ⟨368369, by rfl⟩ : syracuseStep 491159 = 736739) B736739
theorem B327339 : Blo 323837 327339 := bstep (se 1 (by rfl) ⟨245504, by rfl⟩ : syracuseStep 327339 = 491009) B491009
theorem B2981555 : Blo 323837 2981555 := bstep (se 1 (by rfl) ⟨2236166, by rfl⟩ : syracuseStep 2981555 = 4472333) B4472333
theorem B327351 : Blo 323837 327351 := bstep (se 1 (by rfl) ⟨245513, by rfl⟩ : syracuseStep 327351 = 491027) B491027
theorem B327371 : Blo 323837 327371 := bstep (se 1 (by rfl) ⟨245528, by rfl⟩ : syracuseStep 327371 = 491057) B491057
theorem B327383 : Blo 323837 327383 := bstep (se 1 (by rfl) ⟨245537, by rfl⟩ : syracuseStep 327383 = 491075) B491075
theorem B491225 : Blo 323837 491225 := bstep (se 2 (by rfl) ⟨184209, by rfl⟩ : syracuseStep 491225 = 368419) B368419
theorem B327403 : Blo 323837 327403 := bstep (se 1 (by rfl) ⟨245552, by rfl⟩ : syracuseStep 327403 = 491105) B491105
theorem B327415 : Blo 323837 327415 := bstep (se 1 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 327415 = 491123) B491123
theorem B327435 : Blo 323837 327435 := bstep (se 1 (by rfl) ⟨245576, by rfl⟩ : syracuseStep 327435 = 491153) B491153
theorem B327447 : Blo 323837 327447 := bstep (se 1 (by rfl) ⟨245585, by rfl⟩ : syracuseStep 327447 = 491171) B491171
theorem B327467 : Blo 323837 327467 := bstep (se 1 (by rfl) ⟨245600, by rfl⟩ : syracuseStep 327467 = 491201) B491201
theorem B589619 : Blo 323837 589619 := bstep (se 1 (by rfl) ⟨442214, by rfl⟩ : syracuseStep 589619 = 884429) B884429
theorem B327479 : Blo 323837 327479 := bstep (se 1 (by rfl) ⟨245609, by rfl⟩ : syracuseStep 327479 = 491219) B491219
theorem B4685633 : Blo 323837 4685633 := bstep (se 2 (by rfl) ⟨1757112, by rfl⟩ : syracuseStep 4685633 = 3514225) B3514225
theorem B327499 : Blo 323837 327499 := bstep (se 1 (by rfl) ⟨245624, by rfl⟩ : syracuseStep 327499 = 491249) B491249
theorem B491339 : Blo 323837 491339 := bstep (se 1 (by rfl) ⟨368504, by rfl⟩ : syracuseStep 491339 = 737009) B737009
theorem B589655 : Blo 323837 589655 := bstep (se 1 (by rfl) ⟨442241, by rfl⟩ : syracuseStep 589655 = 884483) B884483
theorem B327511 : Blo 323837 327511 := bstep (se 1 (by rfl) ⟨245633, by rfl⟩ : syracuseStep 327511 = 491267) B491267
theorem B491351 : Blo 323837 491351 := bstep (se 1 (by rfl) ⟨368513, by rfl⟩ : syracuseStep 491351 = 737027) B737027
theorem B327531 : Blo 323837 327531 := bstep (se 1 (by rfl) ⟨245648, by rfl⟩ : syracuseStep 327531 = 491297) B491297
theorem B327543 : Blo 323837 327543 := bstep (se 1 (by rfl) ⟨245657, by rfl⟩ : syracuseStep 327543 = 491315) B491315
theorem B327563 : Blo 323837 327563 := bstep (se 1 (by rfl) ⟨245672, by rfl⟩ : syracuseStep 327563 = 491345) B491345
theorem B327575 : Blo 323837 327575 := bstep (se 1 (by rfl) ⟨245681, by rfl⟩ : syracuseStep 327575 = 491363) B491363
theorem B491417 : Blo 323837 491417 := bstep (se 2 (by rfl) ⟨184281, by rfl⟩ : syracuseStep 491417 = 368563) B368563
theorem B327595 : Blo 323837 327595 := bstep (se 1 (by rfl) ⟨245696, by rfl⟩ : syracuseStep 327595 = 491393) B491393
theorem B327607 : Blo 323837 327607 := bstep (se 1 (by rfl) ⟨245705, by rfl⟩ : syracuseStep 327607 = 491411) B491411
theorem B327627 : Blo 323837 327627 := bstep (se 1 (by rfl) ⟨245720, by rfl⟩ : syracuseStep 327627 = 491441) B491441
theorem B327639 : Blo 323837 327639 := bstep (se 1 (by rfl) ⟨245729, by rfl⟩ : syracuseStep 327639 = 491459) B491459
theorem B327659 : Blo 323837 327659 := bstep (se 1 (by rfl) ⟨245744, by rfl⟩ : syracuseStep 327659 = 491489) B491489
theorem B327671 : Blo 323837 327671 := bstep (se 1 (by rfl) ⟨245753, by rfl⟩ : syracuseStep 327671 = 491507) B491507
theorem B327687 : Blo 323837 327687 := bstep (se 1 (by rfl) ⟨245765, by rfl⟩ : syracuseStep 327687 = 491531) B491531
theorem B327695 : Blo 323837 327695 := bstep (se 1 (by rfl) ⟨245771, by rfl⟩ : syracuseStep 327695 = 491543) B491543
theorem B491579 : Blo 323837 491579 := bstep (se 1 (by rfl) ⟨368684, by rfl⟩ : syracuseStep 491579 = 737369) B737369
theorem B327739 : Blo 323837 327739 := bstep (se 1 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 327739 = 491609) B491609
theorem B491639 : Blo 323837 491639 := bstep (se 1 (by rfl) ⟨368729, by rfl⟩ : syracuseStep 491639 = 737459) B737459
theorem B327815 : Blo 323837 327815 := bstep (se 1 (by rfl) ⟨245861, by rfl⟩ : syracuseStep 327815 = 491723) B491723
theorem B491663 : Blo 323837 491663 := bstep (se 1 (by rfl) ⟨368747, by rfl⟩ : syracuseStep 491663 = 737495) B737495
theorem B327823 : Blo 323837 327823 := bstep (se 1 (by rfl) ⟨245867, by rfl⟩ : syracuseStep 327823 = 491735) B491735
theorem B491705 : Blo 323837 491705 := bstep (se 2 (by rfl) ⟨184389, by rfl⟩ : syracuseStep 491705 = 368779) B368779
theorem B1114825 : Blo 323837 1114825 := bstep (se 2 (by rfl) ⟨418059, by rfl⟩ : syracuseStep 1114825 = 836119) B836119
theorem B819983 : Blo 323837 819983 := bstep (se 1 (by rfl) ⟨614987, by rfl⟩ : syracuseStep 819983 = 1229975) B1229975
theorem B885563 : Blo 323837 885563 := bstep (se 1 (by rfl) ⟨664172, by rfl⟩ : syracuseStep 885563 = 1328345) B1328345
theorem B820115 : Blo 323837 820115 := bstep (se 1 (by rfl) ⟨615086, by rfl⟩ : syracuseStep 820115 = 1230173) B1230173
theorem B54887381 : Blo 323837 54887381 := bstep (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) B1286423
theorem B787571 : Blo 323837 787571 := bstep (se 1 (by rfl) ⟨590678, by rfl⟩ : syracuseStep 787571 = 1181357) B1181357
theorem B1049915 : Blo 323837 1049915 := bstep (se 1 (by rfl) ⟨787436, by rfl⟩ : syracuseStep 1049915 = 1574873) B1574873
theorem B1181213 : Blo 323837 1181213 := bstep (se 3 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 1181213 = 442955) B442955
theorem B657353 : Blo 323837 657353 := bstep (se 2 (by rfl) ⟨246507, by rfl⟩ : syracuseStep 657353 = 493015) B493015
theorem B821249 : Blo 323837 821249 := bstep (se 2 (by rfl) ⟨307968, by rfl⟩ : syracuseStep 821249 = 615937) B615937
theorem B1673303 : Blo 323837 1673303 := bstep (se 1 (by rfl) ⟨1254977, by rfl⟩ : syracuseStep 1673303 = 2509955) B2509955
theorem B1575085 : Blo 323837 1575085 := bstep (se 3 (by rfl) ⟨295328, by rfl⟩ : syracuseStep 1575085 = 590657) B590657
theorem B1771865 : Blo 323837 1771865 := bstep (se 2 (by rfl) ⟨664449, by rfl⟩ : syracuseStep 1771865 = 1328899) B1328899
theorem B821623 : Blo 323837 821623 := bstep (se 1 (by rfl) ⟨616217, by rfl⟩ : syracuseStep 821623 = 1232435) B1232435
theorem B822059 : Blo 323837 822059 := bstep (se 1 (by rfl) ⟨616544, by rfl⟩ : syracuseStep 822059 = 1233089) B1233089
theorem B985943 : Blo 323837 985943 := bstep (se 1 (by rfl) ⟨739457, by rfl⟩ : syracuseStep 985943 = 1478915) B1478915
theorem B986041 : Blo 323837 986041 := bstep (se 2 (by rfl) ⟨369765, by rfl⟩ : syracuseStep 986041 = 739531) B739531
theorem B461867 : Blo 323837 461867 := bstep (se 1 (by rfl) ⟨346400, by rfl⟩ : syracuseStep 461867 = 692801) B692801
theorem B2788667 : Blo 323837 2788667 := bstep (se 1 (by rfl) ⟨2091500, by rfl⟩ : syracuseStep 2788667 = 4183001) B4183001
theorem B3509725 : Blo 323837 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B10620517 : Blo 323837 10620517 := bstep (se 4 (by rfl) ⟨995673, by rfl⟩ : syracuseStep 10620517 = 1991347) B1991347
theorem B822899 : Blo 323837 822899 := bstep (se 1 (by rfl) ⟨617174, by rfl⟩ : syracuseStep 822899 = 1234349) B1234349
theorem B822919 : Blo 323837 822919 := bstep (se 1 (by rfl) ⟨617189, by rfl⟩ : syracuseStep 822919 = 1234379) B1234379
theorem B17927831 : Blo 323837 17927831 := bstep (se 1 (by rfl) ⟨13445873, by rfl⟩ : syracuseStep 17927831 = 26891747) B26891747
theorem B9506609 : Blo 323837 9506609 := bstep (se 2 (by rfl) ⟨3564978, by rfl⟩ : syracuseStep 9506609 = 7129957) B7129957
theorem B1642355 : Blo 323837 1642355 := bstep (se 1 (by rfl) ⟨1231766, by rfl⟩ : syracuseStep 1642355 = 2463533) B2463533
theorem B364423 : Blo 323837 364423 := bstep (se 1 (by rfl) ⟨273317, by rfl⟩ : syracuseStep 364423 = 546635) B546635
theorem B528263 : Blo 323837 528263 := bstep (se 1 (by rfl) ⟨396197, by rfl⟩ : syracuseStep 528263 = 792395) B792395
theorem B823193 : Blo 323837 823193 := bstep (se 2 (by rfl) ⟨308697, by rfl⟩ : syracuseStep 823193 = 617395) B617395
theorem B364603 : Blo 323837 364603 := bstep (se 1 (by rfl) ⟨273452, by rfl⟩ : syracuseStep 364603 = 546905) B546905
theorem B823355 : Blo 323837 823355 := bstep (se 1 (by rfl) ⟨617516, by rfl⟩ : syracuseStep 823355 = 1235033) B1235033
theorem B3117143 : Blo 323837 3117143 := bstep (se 1 (by rfl) ⟨2337857, by rfl⟩ : syracuseStep 3117143 = 4675715) B4675715
theorem B692425 : Blo 323837 692425 := bstep (se 2 (by rfl) ⟨259659, by rfl⟩ : syracuseStep 692425 = 519319) B519319
theorem B823567 : Blo 323837 823567 := bstep (se 1 (by rfl) ⟨617675, by rfl⟩ : syracuseStep 823567 = 1235351) B1235351
theorem B1642841 : Blo 323837 1642841 := bstep (se 2 (by rfl) ⟨616065, by rfl⟩ : syracuseStep 1642841 = 1232131) B1232131
theorem B5017949 : Blo 323837 5017949 := bstep (se 3 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 5017949 = 1881731) B1881731
theorem B365071 : Blo 323837 365071 := bstep (se 1 (by rfl) ⟨273803, by rfl⟩ : syracuseStep 365071 = 547607) B547607
theorem B823841 : Blo 323837 823841 := bstep (se 2 (by rfl) ⟨308940, by rfl⟩ : syracuseStep 823841 = 617881) B617881
theorem B2036267 : Blo 323837 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B463735 : Blo 323837 463735 := bstep (se 1 (by rfl) ⟨347801, by rfl⟩ : syracuseStep 463735 = 695603) B695603
theorem B365575 : Blo 323837 365575 := bstep (se 1 (by rfl) ⟨274181, by rfl⟩ : syracuseStep 365575 = 548363) B548363
theorem B365755 : Blo 323837 365755 := bstep (se 1 (by rfl) ⟨274316, by rfl⟩ : syracuseStep 365755 = 548633) B548633
theorem B627983 : Blo 323837 627983 := bstep (se 1 (by rfl) ⟨470987, by rfl⟩ : syracuseStep 627983 = 941975) B941975
theorem B1512857 : Blo 323837 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B693689 : Blo 323837 693689 := bstep (se 2 (by rfl) ⟨260133, by rfl⟩ : syracuseStep 693689 = 520267) B520267
theorem B824843 : Blo 323837 824843 := bstep (se 1 (by rfl) ⟨618632, by rfl⟩ : syracuseStep 824843 = 1237265) B1237265
theorem B693775 : Blo 323837 693775 := bstep (se 1 (by rfl) ⟨520331, by rfl⟩ : syracuseStep 693775 = 1040663) B1040663
theorem B2233975 : Blo 323837 2233975 := bstep (se 1 (by rfl) ⟨1675481, by rfl⟩ : syracuseStep 2233975 = 3350963) B3350963
theorem B366223 : Blo 323837 366223 := bstep (se 1 (by rfl) ⟨274667, by rfl⟩ : syracuseStep 366223 = 549335) B549335
theorem B923393 : Blo 323837 923393 := bstep (se 2 (by rfl) ⟨346272, by rfl⟩ : syracuseStep 923393 = 692545) B692545
theorem B431929 : Blo 323837 431929 := bstep (se 2 (by rfl) ⟨161973, by rfl⟩ : syracuseStep 431929 = 323947) B323947
theorem B923507 : Blo 323837 923507 := bstep (se 1 (by rfl) ⟨692630, by rfl⟩ : syracuseStep 923507 = 1385261) B1385261
theorem B464783 : Blo 323837 464783 := bstep (se 1 (by rfl) ⟨348587, by rfl⟩ : syracuseStep 464783 = 697175) B697175
theorem B366727 : Blo 323837 366727 := bstep (se 1 (by rfl) ⟨275045, by rfl⟩ : syracuseStep 366727 = 550091) B550091
theorem B825491 : Blo 323837 825491 := bstep (se 1 (by rfl) ⟨619118, by rfl⟩ : syracuseStep 825491 = 1238237) B1238237
theorem B923849 : Blo 323837 923849 := bstep (se 2 (by rfl) ⟨346443, by rfl⟩ : syracuseStep 923849 = 692887) B692887
theorem B465097 : Blo 323837 465097 := bstep (se 2 (by rfl) ⟨174411, by rfl⟩ : syracuseStep 465097 = 348823) B348823
theorem B366907 : Blo 323837 366907 := bstep (se 1 (by rfl) ⟨275180, by rfl⟩ : syracuseStep 366907 = 550361) B550361
theorem B1644947 : Blo 323837 1644947 := bstep (se 1 (by rfl) ⟨1233710, by rfl⟩ : syracuseStep 1644947 = 2467421) B2467421
theorem B825785 : Blo 323837 825785 := bstep (se 2 (by rfl) ⟨309669, by rfl⟩ : syracuseStep 825785 = 619339) B619339
theorem B2791979 : Blo 323837 2791979 := bstep (se 1 (by rfl) ⟨2093984, by rfl⟩ : syracuseStep 2791979 = 4187969) B4187969
theorem B367375 : Blo 323837 367375 := bstep (se 1 (by rfl) ⟨275531, by rfl⟩ : syracuseStep 367375 = 551063) B551063
theorem B4725539 : Blo 323837 4725539 := bstep (se 1 (by rfl) ⟨3544154, by rfl⟩ : syracuseStep 4725539 = 7088309) B7088309
theorem B695159 : Blo 323837 695159 := bstep (se 1 (by rfl) ⟨521369, by rfl⟩ : syracuseStep 695159 = 1042739) B1042739
theorem B826483 : Blo 323837 826483 := bstep (se 1 (by rfl) ⟨619862, by rfl⟩ : syracuseStep 826483 = 1239725) B1239725
theorem B826625 : Blo 323837 826625 := bstep (se 2 (by rfl) ⟨309984, by rfl⟩ : syracuseStep 826625 = 619969) B619969
theorem B367879 : Blo 323837 367879 := bstep (se 1 (by rfl) ⟨275909, by rfl⟩ : syracuseStep 367879 = 551819) B551819
theorem B368059 : Blo 323837 368059 := bstep (se 1 (by rfl) ⟨276044, by rfl⟩ : syracuseStep 368059 = 552089) B552089
theorem B728711 : Blo 323837 728711 := bstep (se 1 (by rfl) ⟨546533, by rfl⟩ : syracuseStep 728711 = 1093067) B1093067
theorem B827081 : Blo 323837 827081 := bstep (se 2 (by rfl) ⟨310155, by rfl⟩ : syracuseStep 827081 = 620311) B620311
theorem B728891 : Blo 323837 728891 := bstep (se 1 (by rfl) ⟨546668, by rfl⟩ : syracuseStep 728891 = 1093337) B1093337
theorem B991091 : Blo 323837 991091 := bstep (se 1 (by rfl) ⟨743318, by rfl⟩ : syracuseStep 991091 = 1486637) B1486637
theorem B368527 : Blo 323837 368527 := bstep (se 1 (by rfl) ⟨276395, by rfl⟩ : syracuseStep 368527 = 552791) B552791
theorem B729017 : Blo 323837 729017 := bstep (se 2 (by rfl) ⟨273381, by rfl⟩ : syracuseStep 729017 = 546763) B546763
theorem B925739 : Blo 323837 925739 := bstep (se 1 (by rfl) ⟨694304, by rfl⟩ : syracuseStep 925739 = 1388609) B1388609
theorem B827435 : Blo 323837 827435 := bstep (se 1 (by rfl) ⟨620576, by rfl⟩ : syracuseStep 827435 = 1241153) B1241153
theorem B8954057 : Blo 323837 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B729359 : Blo 323837 729359 := bstep (se 1 (by rfl) ⟨547019, by rfl⟩ : syracuseStep 729359 = 1094039) B1094039
theorem B925967 : Blo 323837 925967 := bstep (se 1 (by rfl) ⟨694475, by rfl⟩ : syracuseStep 925967 = 1388951) B1388951
theorem B729377 : Blo 323837 729377 := bstep (se 2 (by rfl) ⟨273516, by rfl⟩ : syracuseStep 729377 = 547033) B547033
theorem B729719 : Blo 323837 729719 := bstep (se 1 (by rfl) ⟨547289, by rfl⟩ : syracuseStep 729719 = 1094579) B1094579
theorem B729899 : Blo 323837 729899 := bstep (se 1 (by rfl) ⟨547424, by rfl⟩ : syracuseStep 729899 = 1094849) B1094849
theorem B1385363 : Blo 323837 1385363 := bstep (se 1 (by rfl) ⟨1039022, by rfl⟩ : syracuseStep 1385363 = 2078045) B2078045
theorem B828427 : Blo 323837 828427 := bstep (se 1 (by rfl) ⟨621320, by rfl⟩ : syracuseStep 828427 = 1242641) B1242641
theorem B730259 : Blo 323837 730259 := bstep (se 1 (by rfl) ⟨547694, by rfl⟩ : syracuseStep 730259 = 1095389) B1095389
theorem B828569 : Blo 323837 828569 := bstep (se 2 (by rfl) ⟨310713, by rfl⟩ : syracuseStep 828569 = 621427) B621427
theorem B730313 : Blo 323837 730313 := bstep (se 2 (by rfl) ⟨273867, by rfl⟩ : syracuseStep 730313 = 547735) B547735
theorem B992513 : Blo 323837 992513 := bstep (se 2 (by rfl) ⟨372192, by rfl⟩ : syracuseStep 992513 = 744385) B744385
theorem B1844531 : Blo 323837 1844531 := bstep (se 1 (by rfl) ⟨1383398, by rfl⟩ : syracuseStep 1844531 = 2766797) B2766797
theorem B828731 : Blo 323837 828731 := bstep (se 1 (by rfl) ⟨621548, by rfl⟩ : syracuseStep 828731 = 1243097) B1243097
theorem B1648025 : Blo 323837 1648025 := bstep (se 2 (by rfl) ⟨618009, by rfl⟩ : syracuseStep 1648025 = 1236019) B1236019
theorem B4072913 : Blo 323837 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B927379 : Blo 323837 927379 := bstep (se 1 (by rfl) ⟨695534, by rfl⟩ : syracuseStep 927379 = 1391069) B1391069
theorem B829075 : Blo 323837 829075 := bstep (se 1 (by rfl) ⟨621806, by rfl⟩ : syracuseStep 829075 = 1243613) B1243613
theorem B4695731 : Blo 323837 4695731 := bstep (se 1 (by rfl) ⟨3521798, by rfl⟩ : syracuseStep 4695731 = 7043597) B7043597
theorem B829217 : Blo 323837 829217 := bstep (se 2 (by rfl) ⟨310956, by rfl⟩ : syracuseStep 829217 = 621913) B621913
theorem B927607 : Blo 323837 927607 := bstep (se 1 (by rfl) ⟨695705, by rfl⟩ : syracuseStep 927607 = 1391411) B1391411
theorem B731015 : Blo 323837 731015 := bstep (se 1 (by rfl) ⟨548261, by rfl⟩ : syracuseStep 731015 = 1096523) B1096523
theorem B731195 : Blo 323837 731195 := bstep (se 1 (by rfl) ⟨548396, by rfl⟩ : syracuseStep 731195 = 1096793) B1096793
theorem B731321 : Blo 323837 731321 := bstep (se 2 (by rfl) ⟨274245, by rfl⟩ : syracuseStep 731321 = 548491) B548491
theorem B731663 : Blo 323837 731663 := bstep (se 1 (by rfl) ⟨548747, by rfl⟩ : syracuseStep 731663 = 1097495) B1097495
theorem B1387037 : Blo 323837 1387037 := bstep (se 3 (by rfl) ⟨260069, by rfl⟩ : syracuseStep 1387037 = 520139) B520139
theorem B731681 : Blo 323837 731681 := bstep (se 2 (by rfl) ⟨274380, by rfl⟩ : syracuseStep 731681 = 548761) B548761
theorem B3123755 : Blo 323837 3123755 := bstep (se 1 (by rfl) ⟨2342816, by rfl⟩ : syracuseStep 3123755 = 4685633) B4685633
theorem B1845989 : Blo 323837 1845989 := bstep (se 4 (by rfl) ⟨173061, by rfl⟩ : syracuseStep 1845989 = 346123) B346123
theorem B1780481 : Blo 323837 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B2960165 : Blo 323837 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B732023 : Blo 323837 732023 := bstep (se 1 (by rfl) ⟨549017, by rfl⟩ : syracuseStep 732023 = 1098035) B1098035
theorem B732203 : Blo 323837 732203 := bstep (se 1 (by rfl) ⟨549152, by rfl⟩ : syracuseStep 732203 = 1098305) B1098305
theorem B16067645 : Blo 323837 16067645 := bstep (se 3 (by rfl) ⟨3012683, by rfl⟩ : syracuseStep 16067645 = 6025367) B6025367
theorem B928883 : Blo 323837 928883 := bstep (se 1 (by rfl) ⟨696662, by rfl⟩ : syracuseStep 928883 = 1393325) B1393325
theorem B732563 : Blo 323837 732563 := bstep (se 1 (by rfl) ⟨549422, by rfl⟩ : syracuseStep 732563 = 1098845) B1098845
theorem B1387961 : Blo 323837 1387961 := bstep (se 2 (by rfl) ⟨520485, by rfl⟩ : syracuseStep 1387961 = 1040971) B1040971
theorem B699833 : Blo 323837 699833 := bstep (se 2 (by rfl) ⟨262437, by rfl⟩ : syracuseStep 699833 = 524875) B524875
theorem B732617 : Blo 323837 732617 := bstep (se 2 (by rfl) ⟨274731, by rfl⟩ : syracuseStep 732617 = 549463) B549463
theorem B929225 : Blo 323837 929225 := bstep (se 2 (by rfl) ⟨348459, by rfl⟩ : syracuseStep 929225 = 696919) B696919
theorem B1486289 : Blo 323837 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B929339 : Blo 323837 929339 := bstep (se 1 (by rfl) ⟨697004, by rfl⟩ : syracuseStep 929339 = 1394009) B1394009
theorem B3518029 : Blo 323837 3518029 := bstep (se 3 (by rfl) ⟨659630, by rfl⟩ : syracuseStep 3518029 = 1319261) B1319261
theorem B929465 : Blo 323837 929465 := bstep (se 2 (by rfl) ⟨348549, by rfl⟩ : syracuseStep 929465 = 697099) B697099
theorem B2076353 : Blo 323837 2076353 := bstep (se 2 (by rfl) ⟨778632, by rfl⟩ : syracuseStep 2076353 = 1557265) B1557265
theorem B1093391 : Blo 323837 1093391 := bstep (se 1 (by rfl) ⟨820043, by rfl⟩ : syracuseStep 1093391 = 1640087) B1640087
theorem B2338723 : Blo 323837 2338723 := bstep (se 1 (by rfl) ⟨1754042, by rfl⟩ : syracuseStep 2338723 = 3508085) B3508085
theorem B1650617 : Blo 323837 1650617 := bstep (se 2 (by rfl) ⟨618981, by rfl⟩ : syracuseStep 1650617 = 1237963) B1237963
theorem B1093661 : Blo 323837 1093661 := bstep (se 3 (by rfl) ⟨205061, by rfl⟩ : syracuseStep 1093661 = 410123) B410123
theorem B831521 : Blo 323837 831521 := bstep (se 2 (by rfl) ⟨311820, by rfl⟩ : syracuseStep 831521 = 623641) B623641
theorem B733319 : Blo 323837 733319 := bstep (se 1 (by rfl) ⟨549989, by rfl⟩ : syracuseStep 733319 = 1099979) B1099979
theorem B995627 : Blo 323837 995627 := bstep (se 1 (by rfl) ⟨746720, by rfl⟩ : syracuseStep 995627 = 1493441) B1493441
theorem B733499 : Blo 323837 733499 := bstep (se 1 (by rfl) ⟨550124, by rfl⟩ : syracuseStep 733499 = 1100249) B1100249
theorem B504137 : Blo 323837 504137 := bstep (se 2 (by rfl) ⟨189051, by rfl⟩ : syracuseStep 504137 = 378103) B378103
theorem B2634119 : Blo 323837 2634119 := bstep (se 1 (by rfl) ⟨1975589, by rfl⟩ : syracuseStep 2634119 = 3951179) B3951179
theorem B733625 : Blo 323837 733625 := bstep (se 2 (by rfl) ⟨275109, by rfl⟩ : syracuseStep 733625 = 550219) B550219
theorem B438841 : Blo 323837 438841 := bstep (se 2 (by rfl) ⟨164565, by rfl⟩ : syracuseStep 438841 = 329131) B329131
theorem B733967 : Blo 323837 733967 := bstep (se 1 (by rfl) ⟨550475, by rfl⟩ : syracuseStep 733967 = 1100951) B1100951
theorem B733985 : Blo 323837 733985 := bstep (se 2 (by rfl) ⟨275244, by rfl⟩ : syracuseStep 733985 = 550489) B550489
theorem B1389635 : Blo 323837 1389635 := bstep (se 1 (by rfl) ⟨1042226, by rfl⟩ : syracuseStep 1389635 = 2084453) B2084453
theorem B734327 : Blo 323837 734327 := bstep (se 1 (by rfl) ⟨550745, by rfl⟩ : syracuseStep 734327 = 1101491) B1101491
theorem B1651913 : Blo 323837 1651913 := bstep (se 2 (by rfl) ⟨619467, by rfl⟩ : syracuseStep 1651913 = 1238935) B1238935
theorem B734507 : Blo 323837 734507 := bstep (se 1 (by rfl) ⟨550880, by rfl⟩ : syracuseStep 734507 = 1101761) B1101761
theorem B931115 : Blo 323837 931115 := bstep (se 1 (by rfl) ⟨698336, by rfl⟩ : syracuseStep 931115 = 1396673) B1396673
theorem B701831 : Blo 323837 701831 := bstep (se 1 (by rfl) ⟨526373, by rfl⟩ : syracuseStep 701831 = 1052747) B1052747
theorem B1095065 : Blo 323837 1095065 := bstep (se 2 (by rfl) ⟨410649, by rfl⟩ : syracuseStep 1095065 = 821299) B821299
theorem B2635217 : Blo 323837 2635217 := bstep (se 2 (by rfl) ⟨988206, by rfl⟩ : syracuseStep 2635217 = 1976413) B1976413
theorem B9418315 : Blo 323837 9418315 := bstep (se 1 (by rfl) ⟨7063736, by rfl⟩ : syracuseStep 9418315 = 14127473) B14127473
theorem B734867 : Blo 323837 734867 := bstep (se 1 (by rfl) ⟨551150, by rfl⟩ : syracuseStep 734867 = 1102301) B1102301
theorem B3847873 : Blo 323837 3847873 := bstep (se 2 (by rfl) ⟨1442952, by rfl⟩ : syracuseStep 3847873 = 2885905) B2885905
theorem B2242241 : Blo 323837 2242241 := bstep (se 2 (by rfl) ⟨840840, by rfl⟩ : syracuseStep 2242241 = 1681681) B1681681
theorem B734921 : Blo 323837 734921 := bstep (se 2 (by rfl) ⟨275595, by rfl⟩ : syracuseStep 734921 = 551191) B551191
theorem B2111233 : Blo 323837 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B2471795 : Blo 323837 2471795 := bstep (se 1 (by rfl) ⟨1853846, by rfl⟩ : syracuseStep 2471795 = 3707693) B3707693
theorem B1095767 : Blo 323837 1095767 := bstep (se 1 (by rfl) ⟨821825, by rfl⟩ : syracuseStep 1095767 = 1643651) B1643651
theorem B932107 : Blo 323837 932107 := bstep (se 1 (by rfl) ⟨699080, by rfl⟩ : syracuseStep 932107 = 1398161) B1398161
theorem B735623 : Blo 323837 735623 := bstep (se 1 (by rfl) ⟨551717, by rfl⟩ : syracuseStep 735623 = 1103435) B1103435
theorem B1915271 : Blo 323837 1915271 := bstep (se 1 (by rfl) ⟨1436453, by rfl⟩ : syracuseStep 1915271 = 2872907) B2872907
theorem B932381 : Blo 323837 932381 := bstep (se 3 (by rfl) ⟨174821, by rfl⟩ : syracuseStep 932381 = 349643) B349643
theorem B703019 : Blo 323837 703019 := bstep (se 1 (by rfl) ⟨527264, by rfl⟩ : syracuseStep 703019 = 1054529) B1054529
theorem B735803 : Blo 323837 735803 := bstep (se 1 (by rfl) ⟨551852, by rfl⟩ : syracuseStep 735803 = 1103705) B1103705
theorem B1096253 : Blo 323837 1096253 := bstep (se 3 (by rfl) ⟨205547, by rfl⟩ : syracuseStep 1096253 = 411095) B411095
theorem B735929 : Blo 323837 735929 := bstep (se 2 (by rfl) ⟨275973, by rfl⟩ : syracuseStep 735929 = 551947) B551947
theorem B2177945 : Blo 323837 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B736271 : Blo 323837 736271 := bstep (se 1 (by rfl) ⟨552203, by rfl⟩ : syracuseStep 736271 = 1104407) B1104407
theorem B736289 : Blo 323837 736289 := bstep (se 2 (by rfl) ⟨276108, by rfl⟩ : syracuseStep 736289 = 552217) B552217
theorem B441463 : Blo 323837 441463 := bstep (se 1 (by rfl) ⟨331097, by rfl⟩ : syracuseStep 441463 = 662195) B662195
theorem B736631 : Blo 323837 736631 := bstep (se 1 (by rfl) ⟨552473, by rfl⟩ : syracuseStep 736631 = 1104947) B1104947
theorem B736811 : Blo 323837 736811 := bstep (se 1 (by rfl) ⟨552608, by rfl⟩ : syracuseStep 736811 = 1105217) B1105217
theorem B3587777 : Blo 323837 3587777 := bstep (se 2 (by rfl) ⟨1345416, by rfl⟩ : syracuseStep 3587777 = 2690833) B2690833
theorem B737171 : Blo 323837 737171 := bstep (se 1 (by rfl) ⟨552878, by rfl⟩ : syracuseStep 737171 = 1105757) B1105757
theorem B1097657 : Blo 323837 1097657 := bstep (se 2 (by rfl) ⟨411621, by rfl⟩ : syracuseStep 1097657 = 823243) B823243
theorem B737225 : Blo 323837 737225 := bstep (se 2 (by rfl) ⟨276459, by rfl⟩ : syracuseStep 737225 = 552919) B552919
theorem B376975 : Blo 323837 376975 := bstep (se 1 (by rfl) ⟨282731, by rfl⟩ : syracuseStep 376975 = 565463) B565463
theorem B7029139 : Blo 323837 7029139 := bstep (se 1 (by rfl) ⟨5271854, by rfl⟩ : syracuseStep 7029139 = 10543709) B10543709
theorem B1556957 : Blo 323837 1556957 := bstep (se 3 (by rfl) ⟨291929, by rfl⟩ : syracuseStep 1556957 = 583859) B583859
theorem B1098251 : Blo 323837 1098251 := bstep (se 1 (by rfl) ⟨823688, by rfl⟩ : syracuseStep 1098251 = 1647377) B1647377
theorem B1098359 : Blo 323837 1098359 := bstep (se 1 (by rfl) ⟨823769, by rfl⟩ : syracuseStep 1098359 = 1647539) B1647539
theorem B14959235 : Blo 323837 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B5554979 : Blo 323837 5554979 := bstep (se 1 (by rfl) ⟨4166234, by rfl⟩ : syracuseStep 5554979 = 8332469) B8332469
theorem B3982117 : Blo 323837 3982117 := bstep (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) B746647
theorem B410503 : Blo 323837 410503 := bstep (se 1 (by rfl) ⟨307877, by rfl⟩ : syracuseStep 410503 = 615755) B615755
theorem B1098953 : Blo 323837 1098953 := bstep (se 2 (by rfl) ⟨412107, by rfl⟩ : syracuseStep 1098953 = 824215) B824215
theorem B410923 : Blo 323837 410923 := bstep (se 1 (by rfl) ⟨308192, by rfl⟩ : syracuseStep 410923 = 616385) B616385
theorem B411151 : Blo 323837 411151 := bstep (se 1 (by rfl) ⟨308363, by rfl⟩ : syracuseStep 411151 = 616727) B616727
theorem B3884645 : Blo 323837 3884645 := bstep (se 4 (by rfl) ⟨364185, by rfl⟩ : syracuseStep 3884645 = 728371) B728371
theorem B345871 : Blo 323837 345871 := bstep (se 1 (by rfl) ⟨259403, by rfl⟩ : syracuseStep 345871 = 518807) B518807
theorem B476987 : Blo 323837 476987 := bstep (se 1 (by rfl) ⟨357740, by rfl⟩ : syracuseStep 476987 = 715481) B715481
theorem B1099655 : Blo 323837 1099655 := bstep (se 1 (by rfl) ⟨824741, by rfl⟩ : syracuseStep 1099655 = 1649483) B1649483
theorem B346127 : Blo 323837 346127 := bstep (se 1 (by rfl) ⟨259595, by rfl⟩ : syracuseStep 346127 = 519191) B519191
theorem B706619 : Blo 323837 706619 := bstep (se 1 (by rfl) ⟨529964, by rfl⟩ : syracuseStep 706619 = 1059929) B1059929
theorem B411895 : Blo 323837 411895 := bstep (se 1 (by rfl) ⟨308921, by rfl⟩ : syracuseStep 411895 = 617843) B617843
theorem B1100033 : Blo 323837 1100033 := bstep (se 2 (by rfl) ⟨412512, by rfl⟩ : syracuseStep 1100033 = 825025) B825025
theorem B1853711 : Blo 323837 1853711 := bstep (se 1 (by rfl) ⟨1390283, by rfl⟩ : syracuseStep 1853711 = 2780567) B2780567
theorem B412219 : Blo 323837 412219 := bstep (se 1 (by rfl) ⟨309164, by rfl⟩ : syracuseStep 412219 = 618329) B618329
theorem B1231631 : Blo 323837 1231631 := bstep (se 1 (by rfl) ⟨923723, by rfl⟩ : syracuseStep 1231631 = 1847447) B1847447
theorem B1657745 : Blo 323837 1657745 := bstep (se 2 (by rfl) ⟨621654, by rfl⟩ : syracuseStep 1657745 = 1243309) B1243309
theorem B4180997 : Blo 323837 4180997 := bstep (se 4 (by rfl) ⟨391968, by rfl⟩ : syracuseStep 4180997 = 783937) B783937
theorem B412715 : Blo 323837 412715 := bstep (se 1 (by rfl) ⟨309536, by rfl⟩ : syracuseStep 412715 = 619073) B619073
theorem B1100843 : Blo 323837 1100843 := bstep (se 1 (by rfl) ⟨825632, by rfl⟩ : syracuseStep 1100843 = 1651265) B1651265
theorem B1002557 : Blo 323837 1002557 := bstep (se 3 (by rfl) ⟨187979, by rfl⟩ : syracuseStep 1002557 = 375959) B375959
theorem B937079 : Blo 323837 937079 := bstep (se 1 (by rfl) ⟨702809, by rfl⟩ : syracuseStep 937079 = 1405619) B1405619
theorem B2411693 : Blo 323837 2411693 := bstep (se 3 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 2411693 = 904385) B904385
theorem B2116999 : Blo 323837 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B413191 : Blo 323837 413191 := bstep (se 1 (by rfl) ⟨309893, by rfl⟩ : syracuseStep 413191 = 619787) B619787
theorem B1855169 : Blo 323837 1855169 := bstep (se 2 (by rfl) ⟨695688, by rfl⟩ : syracuseStep 1855169 = 1391377) B1391377
theorem B1560379 : Blo 323837 1560379 := bstep (se 1 (by rfl) ⟨1170284, by rfl⟩ : syracuseStep 1560379 = 2340569) B2340569
theorem B413687 : Blo 323837 413687 := bstep (se 1 (by rfl) ⟨310265, by rfl⟩ : syracuseStep 413687 = 620531) B620531
theorem B413839 : Blo 323837 413839 := bstep (se 1 (by rfl) ⟨310379, by rfl⟩ : syracuseStep 413839 = 620759) B620759
theorem B1986875 : Blo 323837 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B414011 : Blo 323837 414011 := bstep (se 1 (by rfl) ⟨310508, by rfl⟩ : syracuseStep 414011 = 621017) B621017
theorem B1102139 : Blo 323837 1102139 := bstep (se 1 (by rfl) ⟨826604, by rfl⟩ : syracuseStep 1102139 = 1653209) B1653209
theorem B1069427 : Blo 323837 1069427 := bstep (se 1 (by rfl) ⟨802070, by rfl⟩ : syracuseStep 1069427 = 1604141) B1604141
theorem B1332001 : Blo 323837 1332001 := bstep (se 2 (by rfl) ⟨499500, by rfl⟩ : syracuseStep 1332001 = 999001) B999001
theorem B1102625 : Blo 323837 1102625 := bstep (se 2 (by rfl) ⟨413484, by rfl⟩ : syracuseStep 1102625 = 826969) B826969
theorem B1987361 : Blo 323837 1987361 := bstep (se 2 (by rfl) ⟨745260, by rfl⟩ : syracuseStep 1987361 = 1490521) B1490521
theorem B840719 : Blo 323837 840719 := bstep (se 1 (by rfl) ⟨630539, by rfl⟩ : syracuseStep 840719 = 1261079) B1261079
theorem B1987703 : Blo 323837 1987703 := bstep (se 1 (by rfl) ⟨1490777, by rfl⟩ : syracuseStep 1987703 = 2981555) B2981555
theorem B4084937 : Blo 323837 4084937 := bstep (se 2 (by rfl) ⟨1531851, by rfl⟩ : syracuseStep 4084937 = 3063703) B3063703
theorem B1103219 : Blo 323837 1103219 := bstep (se 1 (by rfl) ⟨827414, by rfl⟩ : syracuseStep 1103219 = 1654829) B1654829
theorem B6674177 : Blo 323837 6674177 := bstep (se 2 (by rfl) ⟨2502816, by rfl⟩ : syracuseStep 6674177 = 5005633) B5005633
theorem B350087 : Blo 323837 350087 := bstep (se 1 (by rfl) ⟨262565, by rfl⟩ : syracuseStep 350087 = 525131) B525131
theorem B1234835 : Blo 323837 1234835 := bstep (se 1 (by rfl) ⟨926126, by rfl⟩ : syracuseStep 1234835 = 1852253) B1852253
theorem B415751 : Blo 323837 415751 := bstep (se 1 (by rfl) ⟨311813, by rfl⟩ : syracuseStep 415751 = 623627) B623627
theorem B31610897 : Blo 323837 31610897 := bstep (se 2 (by rfl) ⟨11854086, by rfl⟩ : syracuseStep 31610897 = 23708173) B23708173
theorem B547087 : Blo 323837 547087 := bstep (se 1 (by rfl) ⟨410315, by rfl⟩ : syracuseStep 547087 = 820631) B820631
theorem B547627 : Blo 323837 547627 := bstep (se 1 (by rfl) ⟨410720, by rfl⟩ : syracuseStep 547627 = 821441) B821441
theorem B547769 : Blo 323837 547769 := bstep (se 2 (by rfl) ⟨205413, by rfl⟩ : syracuseStep 547769 = 410827) B410827
theorem B1334225 : Blo 323837 1334225 := bstep (se 2 (by rfl) ⟨500334, by rfl⟩ : syracuseStep 1334225 = 1000669) B1000669
theorem B3333143 : Blo 323837 3333143 := bstep (se 1 (by rfl) ⟨2499857, by rfl⟩ : syracuseStep 3333143 = 4999715) B4999715
theorem B1236491 : Blo 323837 1236491 := bstep (se 1 (by rfl) ⟨927368, by rfl⟩ : syracuseStep 1236491 = 1854737) B1854737
theorem B548471 : Blo 323837 548471 := bstep (se 1 (by rfl) ⟨411353, by rfl⟩ : syracuseStep 548471 = 822707) B822707
theorem B876179 : Blo 323837 876179 := bstep (se 1 (by rfl) ⟨657134, by rfl⟩ : syracuseStep 876179 = 1314269) B1314269
theorem B1105811 : Blo 323837 1105811 := bstep (se 1 (by rfl) ⟨829358, by rfl⟩ : syracuseStep 1105811 = 1658717) B1658717
theorem B548923 : Blo 323837 548923 := bstep (se 1 (by rfl) ⟨411692, by rfl⟩ : syracuseStep 548923 = 823385) B823385
theorem B549065 : Blo 323837 549065 := bstep (se 2 (by rfl) ⟨205899, by rfl⟩ : syracuseStep 549065 = 411799) B411799
theorem B11297009 : Blo 323837 11297009 := bstep (se 2 (by rfl) ⟨4236378, by rfl⟩ : syracuseStep 11297009 = 8472757) B8472757
theorem B778555 : Blo 323837 778555 := bstep (se 1 (by rfl) ⟨583916, by rfl⟩ : syracuseStep 778555 = 1167833) B1167833
theorem B1860043 : Blo 323837 1860043 := bstep (se 1 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 1860043 = 2790065) B2790065
theorem B2089475 : Blo 323837 2089475 := bstep (se 1 (by rfl) ⟨1567106, by rfl⟩ : syracuseStep 2089475 = 3134213) B3134213
theorem B614927 : Blo 323837 614927 := bstep (se 1 (by rfl) ⟨461195, by rfl⟩ : syracuseStep 614927 = 922391) B922391
theorem B549767 : Blo 323837 549767 := bstep (se 1 (by rfl) ⟨412325, by rfl⟩ : syracuseStep 549767 = 824651) B824651
theorem B1697057 : Blo 323837 1697057 := bstep (se 2 (by rfl) ⟨636396, by rfl⟩ : syracuseStep 1697057 = 1272793) B1272793
theorem B550415 : Blo 323837 550415 := bstep (se 1 (by rfl) ⟨412811, by rfl⟩ : syracuseStep 550415 = 825623) B825623
theorem B779863 : Blo 323837 779863 := bstep (se 1 (by rfl) ⟨584897, by rfl⟩ : syracuseStep 779863 = 1169795) B1169795
theorem B878471 : Blo 323837 878471 := bstep (se 1 (by rfl) ⟨658853, by rfl⟩ : syracuseStep 878471 = 1317707) B1317707
theorem B583571 : Blo 323837 583571 := bstep (se 1 (by rfl) ⟨437678, by rfl⟩ : syracuseStep 583571 = 875357) B875357
theorem B616339 : Blo 323837 616339 := bstep (se 1 (by rfl) ⟨462254, by rfl⟩ : syracuseStep 616339 = 924509) B924509
theorem B550955 : Blo 323837 550955 := bstep (se 1 (by rfl) ⟨413216, by rfl⟩ : syracuseStep 550955 = 826433) B826433
theorem B616567 : Blo 323837 616567 := bstep (se 1 (by rfl) ⟨462425, by rfl⟩ : syracuseStep 616567 = 924851) B924851
theorem B3795335 : Blo 323837 3795335 := bstep (se 1 (by rfl) ⟨2846501, by rfl⟩ : syracuseStep 3795335 = 5693003) B5693003
theorem B4712849 : Blo 323837 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B551353 : Blo 323837 551353 := bstep (se 2 (by rfl) ⟨206757, by rfl⟩ : syracuseStep 551353 = 413515) B413515
theorem B485819 : Blo 323837 485819 := bstep (se 1 (by rfl) ⟨364364, by rfl⟩ : syracuseStep 485819 = 728729) B728729
theorem B485879 : Blo 323837 485879 := bstep (se 1 (by rfl) ⟨364409, by rfl⟩ : syracuseStep 485879 = 728819) B728819
theorem B485903 : Blo 323837 485903 := bstep (se 1 (by rfl) ⟨364427, by rfl⟩ : syracuseStep 485903 = 728855) B728855
theorem B485945 : Blo 323837 485945 := bstep (se 2 (by rfl) ⟨182229, by rfl⟩ : syracuseStep 485945 = 364459) B364459
theorem B486023 : Blo 323837 486023 := bstep (se 1 (by rfl) ⟨364517, by rfl⟩ : syracuseStep 486023 = 729035) B729035
theorem B486059 : Blo 323837 486059 := bstep (se 1 (by rfl) ⟨364544, by rfl⟩ : syracuseStep 486059 = 729089) B729089
theorem B1764013 : Blo 323837 1764013 := bstep (se 3 (by rfl) ⟨330752, by rfl⟩ : syracuseStep 1764013 = 661505) B661505
theorem B486089 : Blo 323837 486089 := bstep (se 2 (by rfl) ⟨182283, by rfl⟩ : syracuseStep 486089 = 364567) B364567
theorem B2779919 : Blo 323837 2779919 := bstep (se 1 (by rfl) ⟨2084939, by rfl⟩ : syracuseStep 2779919 = 4169879) B4169879
theorem B486203 : Blo 323837 486203 := bstep (se 1 (by rfl) ⟨364652, by rfl⟩ : syracuseStep 486203 = 729305) B729305
theorem B1862459 : Blo 323837 1862459 := bstep (se 1 (by rfl) ⟨1396844, by rfl⟩ : syracuseStep 1862459 = 2793689) B2793689
theorem B3140441 : Blo 323837 3140441 := bstep (se 2 (by rfl) ⟨1177665, by rfl⟩ : syracuseStep 3140441 = 2355331) B2355331
theorem B486263 : Blo 323837 486263 := bstep (se 1 (by rfl) ⟨364697, by rfl⟩ : syracuseStep 486263 = 729395) B729395
theorem B486287 : Blo 323837 486287 := bstep (se 1 (by rfl) ⟨364715, by rfl⟩ : syracuseStep 486287 = 729431) B729431
theorem B486329 : Blo 323837 486329 := bstep (se 2 (by rfl) ⟨182373, by rfl⟩ : syracuseStep 486329 = 364747) B364747
theorem B486407 : Blo 323837 486407 := bstep (se 1 (by rfl) ⟨364805, by rfl⟩ : syracuseStep 486407 = 729611) B729611
theorem B486443 : Blo 323837 486443 := bstep (se 1 (by rfl) ⟨364832, by rfl⟩ : syracuseStep 486443 = 729665) B729665
theorem B3140669 : Blo 323837 3140669 := bstep (se 3 (by rfl) ⟨588875, by rfl⟩ : syracuseStep 3140669 = 1177751) B1177751
theorem B486473 : Blo 323837 486473 := bstep (se 2 (by rfl) ⟨182427, by rfl⟩ : syracuseStep 486473 = 364855) B364855
theorem B552055 : Blo 323837 552055 := bstep (se 1 (by rfl) ⟨414041, by rfl⟩ : syracuseStep 552055 = 828083) B828083
theorem B584839 : Blo 323837 584839 := bstep (se 1 (by rfl) ⟨438629, by rfl⟩ : syracuseStep 584839 = 877259) B877259
theorem B486587 : Blo 323837 486587 := bstep (se 1 (by rfl) ⟨364940, by rfl⟩ : syracuseStep 486587 = 729881) B729881
theorem B486647 : Blo 323837 486647 := bstep (se 1 (by rfl) ⟨364985, by rfl⟩ : syracuseStep 486647 = 729971) B729971
theorem B486671 : Blo 323837 486671 := bstep (se 1 (by rfl) ⟨365003, by rfl⟩ : syracuseStep 486671 = 730007) B730007
theorem B486713 : Blo 323837 486713 := bstep (se 2 (by rfl) ⟨182517, by rfl⟩ : syracuseStep 486713 = 365035) B365035
theorem B1240379 : Blo 323837 1240379 := bstep (se 1 (by rfl) ⟨930284, by rfl⟩ : syracuseStep 1240379 = 1860569) B1860569
theorem B552251 : Blo 323837 552251 := bstep (se 1 (by rfl) ⟨414188, by rfl⟩ : syracuseStep 552251 = 828377) B828377
theorem B486791 : Blo 323837 486791 := bstep (se 1 (by rfl) ⟨365093, by rfl⟩ : syracuseStep 486791 = 730187) B730187
theorem B486827 : Blo 323837 486827 := bstep (se 1 (by rfl) ⟨365120, by rfl⟩ : syracuseStep 486827 = 730241) B730241
theorem B486857 : Blo 323837 486857 := bstep (se 2 (by rfl) ⟨182571, by rfl⟩ : syracuseStep 486857 = 365143) B365143
theorem B486971 : Blo 323837 486971 := bstep (se 1 (by rfl) ⟨365228, by rfl⟩ : syracuseStep 486971 = 730457) B730457
theorem B3731021 : Blo 323837 3731021 := bstep (se 3 (by rfl) ⟨699566, by rfl⟩ : syracuseStep 3731021 = 1399133) B1399133
theorem B487031 : Blo 323837 487031 := bstep (se 1 (by rfl) ⟨365273, by rfl⟩ : syracuseStep 487031 = 730547) B730547
theorem B487055 : Blo 323837 487055 := bstep (se 1 (by rfl) ⟨365291, by rfl⟩ : syracuseStep 487055 = 730583) B730583
theorem B618131 : Blo 323837 618131 := bstep (se 1 (by rfl) ⟨463598, by rfl⟩ : syracuseStep 618131 = 927197) B927197
theorem B487097 : Blo 323837 487097 := bstep (se 2 (by rfl) ⟨182661, by rfl⟩ : syracuseStep 487097 = 365323) B365323
theorem B618185 : Blo 323837 618185 := bstep (se 2 (by rfl) ⟨231819, by rfl⟩ : syracuseStep 618185 = 463639) B463639
theorem B552649 : Blo 323837 552649 := bstep (se 2 (by rfl) ⟨207243, by rfl⟩ : syracuseStep 552649 = 414487) B414487
theorem B487175 : Blo 323837 487175 := bstep (se 1 (by rfl) ⟨365381, by rfl⟩ : syracuseStep 487175 = 730763) B730763
theorem B945935 : Blo 323837 945935 := bstep (se 1 (by rfl) ⟨709451, by rfl⟩ : syracuseStep 945935 = 1418903) B1418903
theorem B1240865 : Blo 323837 1240865 := bstep (se 2 (by rfl) ⟨465324, by rfl⟩ : syracuseStep 1240865 = 930649) B930649
theorem B487211 : Blo 323837 487211 := bstep (se 1 (by rfl) ⟨365408, by rfl⟩ : syracuseStep 487211 = 730817) B730817
theorem B618283 : Blo 323837 618283 := bstep (se 1 (by rfl) ⟨463712, by rfl⟩ : syracuseStep 618283 = 927425) B927425
theorem B487241 : Blo 323837 487241 := bstep (se 2 (by rfl) ⟨182715, by rfl⟩ : syracuseStep 487241 = 365431) B365431
theorem B487355 : Blo 323837 487355 := bstep (se 1 (by rfl) ⟨365516, by rfl⟩ : syracuseStep 487355 = 731033) B731033
theorem B487415 : Blo 323837 487415 := bstep (se 1 (by rfl) ⟨365561, by rfl⟩ : syracuseStep 487415 = 731123) B731123
theorem B487439 : Blo 323837 487439 := bstep (se 1 (by rfl) ⟨365579, by rfl⟩ : syracuseStep 487439 = 731159) B731159
theorem B618511 : Blo 323837 618511 := bstep (se 1 (by rfl) ⟨463883, by rfl⟩ : syracuseStep 618511 = 927767) B927767
theorem B487481 : Blo 323837 487481 := bstep (se 2 (by rfl) ⟨182805, by rfl⟩ : syracuseStep 487481 = 365611) B365611
theorem B2781317 : Blo 323837 2781317 := bstep (se 4 (by rfl) ⟨260748, by rfl⟩ : syracuseStep 2781317 = 521497) B521497
theorem B487559 : Blo 323837 487559 := bstep (se 1 (by rfl) ⟨365669, by rfl⟩ : syracuseStep 487559 = 731339) B731339
theorem B487595 : Blo 323837 487595 := bstep (se 1 (by rfl) ⟨365696, by rfl⟩ : syracuseStep 487595 = 731393) B731393
theorem B487625 : Blo 323837 487625 := bstep (se 2 (by rfl) ⟨182859, by rfl⟩ : syracuseStep 487625 = 365719) B365719
theorem B585929 : Blo 323837 585929 := bstep (se 2 (by rfl) ⟨219723, by rfl⟩ : syracuseStep 585929 = 439447) B439447
theorem B1863917 : Blo 323837 1863917 := bstep (se 3 (by rfl) ⟨349484, by rfl⟩ : syracuseStep 1863917 = 698969) B698969
theorem B323847 : Blo 323837 323847 := bstep (se 1 (by rfl) ⟨242885, by rfl⟩ : syracuseStep 323847 = 485771) B485771
theorem B323855 : Blo 323837 323855 := bstep (se 1 (by rfl) ⟨242891, by rfl⟩ : syracuseStep 323855 = 485783) B485783
theorem B3535163 : Blo 323837 3535163 := bstep (se 1 (by rfl) ⟨2651372, by rfl⟩ : syracuseStep 3535163 = 5302745) B5302745
theorem B323899 : Blo 323837 323899 := bstep (se 1 (by rfl) ⟨242924, by rfl⟩ : syracuseStep 323899 = 485849) B485849
theorem B487739 : Blo 323837 487739 := bstep (se 1 (by rfl) ⟨365804, by rfl⟩ : syracuseStep 487739 = 731609) B731609
theorem B782707 : Blo 323837 782707 := bstep (se 1 (by rfl) ⟨587030, by rfl⟩ : syracuseStep 782707 = 1174061) B1174061
theorem B487799 : Blo 323837 487799 := bstep (se 1 (by rfl) ⟨365849, by rfl⟩ : syracuseStep 487799 = 731699) B731699
theorem B323975 : Blo 323837 323975 := bstep (se 1 (by rfl) ⟨242981, by rfl⟩ : syracuseStep 323975 = 485963) B485963
theorem B323983 : Blo 323837 323983 := bstep (se 1 (by rfl) ⟨242987, by rfl⟩ : syracuseStep 323983 = 485975) B485975
theorem B487823 : Blo 323837 487823 := bstep (se 1 (by rfl) ⟨365867, by rfl⟩ : syracuseStep 487823 = 731735) B731735
theorem B487865 : Blo 323837 487865 := bstep (se 2 (by rfl) ⟨182949, by rfl⟩ : syracuseStep 487865 = 365899) B365899
theorem B324027 : Blo 323837 324027 := bstep (se 1 (by rfl) ⟨243020, by rfl⟩ : syracuseStep 324027 = 486041) B486041
theorem B324103 : Blo 323837 324103 := bstep (se 1 (by rfl) ⟨243077, by rfl⟩ : syracuseStep 324103 = 486155) B486155
theorem B487943 : Blo 323837 487943 := bstep (se 1 (by rfl) ⟨365957, by rfl⟩ : syracuseStep 487943 = 731915) B731915
theorem B324111 : Blo 323837 324111 := bstep (se 1 (by rfl) ⟨243083, by rfl⟩ : syracuseStep 324111 = 486167) B486167
theorem B487979 : Blo 323837 487979 := bstep (se 1 (by rfl) ⟨365984, by rfl⟩ : syracuseStep 487979 = 731969) B731969
theorem B1864235 : Blo 323837 1864235 := bstep (se 1 (by rfl) ⟨1398176, by rfl⟩ : syracuseStep 1864235 = 2796353) B2796353
theorem B324155 : Blo 323837 324155 := bstep (se 1 (by rfl) ⟨243116, by rfl⟩ : syracuseStep 324155 = 486233) B486233
theorem B488009 : Blo 323837 488009 := bstep (se 2 (by rfl) ⟨183003, by rfl⟩ : syracuseStep 488009 = 366007) B366007
theorem B2486861 : Blo 323837 2486861 := bstep (se 3 (by rfl) ⟨466286, by rfl⟩ : syracuseStep 2486861 = 932573) B932573
theorem B881239 : Blo 323837 881239 := bstep (se 1 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 881239 = 1321859) B1321859
theorem B324231 : Blo 323837 324231 := bstep (se 1 (by rfl) ⟨243173, by rfl⟩ : syracuseStep 324231 = 486347) B486347
theorem B324239 : Blo 323837 324239 := bstep (se 1 (by rfl) ⟨243179, by rfl⟩ : syracuseStep 324239 = 486359) B486359
theorem B324283 : Blo 323837 324283 := bstep (se 1 (by rfl) ⟨243212, by rfl⟩ : syracuseStep 324283 = 486425) B486425
theorem B488123 : Blo 323837 488123 := bstep (se 1 (by rfl) ⟨366092, by rfl⟩ : syracuseStep 488123 = 732185) B732185
theorem B1241837 : Blo 323837 1241837 := bstep (se 3 (by rfl) ⟨232844, by rfl⟩ : syracuseStep 1241837 = 465689) B465689
theorem B488183 : Blo 323837 488183 := bstep (se 1 (by rfl) ⟨366137, by rfl⟩ : syracuseStep 488183 = 732275) B732275
theorem B324359 : Blo 323837 324359 := bstep (se 1 (by rfl) ⟨243269, by rfl⟩ : syracuseStep 324359 = 486539) B486539
theorem B324367 : Blo 323837 324367 := bstep (se 1 (by rfl) ⟨243275, by rfl⟩ : syracuseStep 324367 = 486551) B486551
theorem B488207 : Blo 323837 488207 := bstep (se 1 (by rfl) ⟨366155, by rfl⟩ : syracuseStep 488207 = 732311) B732311
theorem B488249 : Blo 323837 488249 := bstep (se 2 (by rfl) ⟨183093, by rfl⟩ : syracuseStep 488249 = 366187) B366187
theorem B324411 : Blo 323837 324411 := bstep (se 1 (by rfl) ⟨243308, by rfl⟩ : syracuseStep 324411 = 486617) B486617
theorem B324487 : Blo 323837 324487 := bstep (se 1 (by rfl) ⟨243365, by rfl⟩ : syracuseStep 324487 = 486731) B486731
theorem B488327 : Blo 323837 488327 := bstep (se 1 (by rfl) ⟨366245, by rfl⟩ : syracuseStep 488327 = 732491) B732491
theorem B324495 : Blo 323837 324495 := bstep (se 1 (by rfl) ⟨243371, by rfl⟩ : syracuseStep 324495 = 486743) B486743
theorem B488363 : Blo 323837 488363 := bstep (se 1 (by rfl) ⟨366272, by rfl⟩ : syracuseStep 488363 = 732545) B732545
theorem B324539 : Blo 323837 324539 := bstep (se 1 (by rfl) ⟨243404, by rfl⟩ : syracuseStep 324539 = 486809) B486809
theorem B488393 : Blo 323837 488393 := bstep (se 2 (by rfl) ⟨183147, by rfl⟩ : syracuseStep 488393 = 366295) B366295
theorem B324615 : Blo 323837 324615 := bstep (se 1 (by rfl) ⟨243461, by rfl⟩ : syracuseStep 324615 = 486923) B486923
theorem B324623 : Blo 323837 324623 := bstep (se 1 (by rfl) ⟨243467, by rfl⟩ : syracuseStep 324623 = 486935) B486935
theorem B1242155 : Blo 323837 1242155 := bstep (se 1 (by rfl) ⟨931616, by rfl⟩ : syracuseStep 1242155 = 1863233) B1863233
theorem B324667 : Blo 323837 324667 := bstep (se 1 (by rfl) ⟨243500, by rfl⟩ : syracuseStep 324667 = 487001) B487001
theorem B488507 : Blo 323837 488507 := bstep (se 1 (by rfl) ⟨366380, by rfl⟩ : syracuseStep 488507 = 732761) B732761
theorem B488567 : Blo 323837 488567 := bstep (se 1 (by rfl) ⟨366425, by rfl⟩ : syracuseStep 488567 = 732851) B732851
theorem B324743 : Blo 323837 324743 := bstep (se 1 (by rfl) ⟨243557, by rfl⟩ : syracuseStep 324743 = 487115) B487115
theorem B324751 : Blo 323837 324751 := bstep (se 1 (by rfl) ⟨243563, by rfl⟩ : syracuseStep 324751 = 487127) B487127
theorem B488591 : Blo 323837 488591 := bstep (se 1 (by rfl) ⟨366443, by rfl⟩ : syracuseStep 488591 = 732887) B732887
theorem B488633 : Blo 323837 488633 := bstep (se 2 (by rfl) ⟨183237, by rfl⟩ : syracuseStep 488633 = 366475) B366475
theorem B324795 : Blo 323837 324795 := bstep (se 1 (by rfl) ⟨243596, by rfl⟩ : syracuseStep 324795 = 487193) B487193
theorem B324871 : Blo 323837 324871 := bstep (se 1 (by rfl) ⟨243653, by rfl⟩ : syracuseStep 324871 = 487307) B487307
theorem B488711 : Blo 323837 488711 := bstep (se 1 (by rfl) ⟨366533, by rfl⟩ : syracuseStep 488711 = 733067) B733067
theorem B324879 : Blo 323837 324879 := bstep (se 1 (by rfl) ⟨243659, by rfl⟩ : syracuseStep 324879 = 487319) B487319
theorem B1242383 : Blo 323837 1242383 := bstep (se 1 (by rfl) ⟨931787, by rfl⟩ : syracuseStep 1242383 = 1863575) B1863575
theorem B488747 : Blo 323837 488747 := bstep (se 1 (by rfl) ⟨366560, by rfl⟩ : syracuseStep 488747 = 733121) B733121
theorem B324923 : Blo 323837 324923 := bstep (se 1 (by rfl) ⟨243692, by rfl⟩ : syracuseStep 324923 = 487385) B487385
theorem B488777 : Blo 323837 488777 := bstep (se 2 (by rfl) ⟨183291, by rfl⟩ : syracuseStep 488777 = 366583) B366583
theorem B324999 : Blo 323837 324999 := bstep (se 1 (by rfl) ⟨243749, by rfl⟩ : syracuseStep 324999 = 487499) B487499
theorem B325007 : Blo 323837 325007 := bstep (se 1 (by rfl) ⟨243755, by rfl⟩ : syracuseStep 325007 = 487511) B487511
theorem B325051 : Blo 323837 325051 := bstep (se 1 (by rfl) ⟨243788, by rfl⟩ : syracuseStep 325051 = 487577) B487577
theorem B488891 : Blo 323837 488891 := bstep (se 1 (by rfl) ⟨366668, by rfl⟩ : syracuseStep 488891 = 733337) B733337
theorem B488951 : Blo 323837 488951 := bstep (se 1 (by rfl) ⟨366713, by rfl⟩ : syracuseStep 488951 = 733427) B733427
theorem B325127 : Blo 323837 325127 := bstep (se 1 (by rfl) ⟨243845, by rfl⟩ : syracuseStep 325127 = 487691) B487691
theorem B325135 : Blo 323837 325135 := bstep (se 1 (by rfl) ⟨243851, by rfl⟩ : syracuseStep 325135 = 487703) B487703
theorem B488975 : Blo 323837 488975 := bstep (se 1 (by rfl) ⟨366731, by rfl⟩ : syracuseStep 488975 = 733463) B733463
theorem B620075 : Blo 323837 620075 := bstep (se 1 (by rfl) ⟨465056, by rfl⟩ : syracuseStep 620075 = 930113) B930113
theorem B489017 : Blo 323837 489017 := bstep (se 2 (by rfl) ⟨183381, by rfl⟩ : syracuseStep 489017 = 366763) B366763
theorem B325179 : Blo 323837 325179 := bstep (se 1 (by rfl) ⟨243884, by rfl⟩ : syracuseStep 325179 = 487769) B487769
theorem B5568101 : Blo 323837 5568101 := bstep (se 4 (by rfl) ⟨522009, by rfl⟩ : syracuseStep 5568101 = 1044019) B1044019
theorem B325255 : Blo 323837 325255 := bstep (se 1 (by rfl) ⟨243941, by rfl⟩ : syracuseStep 325255 = 487883) B487883
theorem B489095 : Blo 323837 489095 := bstep (se 1 (by rfl) ⟨366821, by rfl⟩ : syracuseStep 489095 = 733643) B733643
theorem B325263 : Blo 323837 325263 := bstep (se 1 (by rfl) ⟨243947, by rfl⟩ : syracuseStep 325263 = 487895) B487895
theorem B489131 : Blo 323837 489131 := bstep (se 1 (by rfl) ⟨366848, by rfl⟩ : syracuseStep 489131 = 733697) B733697
theorem B3700403 : Blo 323837 3700403 := bstep (se 1 (by rfl) ⟨2775302, by rfl⟩ : syracuseStep 3700403 = 5550605) B5550605
theorem B587449 : Blo 323837 587449 := bstep (se 2 (by rfl) ⟨220293, by rfl⟩ : syracuseStep 587449 = 440587) B440587
theorem B325307 : Blo 323837 325307 := bstep (se 1 (by rfl) ⟨243980, by rfl⟩ : syracuseStep 325307 = 487961) B487961
theorem B489161 : Blo 323837 489161 := bstep (se 2 (by rfl) ⟨183435, by rfl⟩ : syracuseStep 489161 = 366871) B366871
theorem B325383 : Blo 323837 325383 := bstep (se 1 (by rfl) ⟨244037, by rfl⟩ : syracuseStep 325383 = 488075) B488075
theorem B325391 : Blo 323837 325391 := bstep (se 1 (by rfl) ⟨244043, by rfl⟩ : syracuseStep 325391 = 488087) B488087
theorem B325435 : Blo 323837 325435 := bstep (se 1 (by rfl) ⟨244076, by rfl⟩ : syracuseStep 325435 = 488153) B488153
theorem B489275 : Blo 323837 489275 := bstep (se 1 (by rfl) ⟨366956, by rfl⟩ : syracuseStep 489275 = 733913) B733913
theorem B489335 : Blo 323837 489335 := bstep (se 1 (by rfl) ⟨367001, by rfl⟩ : syracuseStep 489335 = 734003) B734003
theorem B325511 : Blo 323837 325511 := bstep (se 1 (by rfl) ⟨244133, by rfl⟩ : syracuseStep 325511 = 488267) B488267
theorem B325519 : Blo 323837 325519 := bstep (se 1 (by rfl) ⟨244139, by rfl⟩ : syracuseStep 325519 = 488279) B488279
theorem B489359 : Blo 323837 489359 := bstep (se 1 (by rfl) ⟨367019, by rfl⟩ : syracuseStep 489359 = 734039) B734039
theorem B489401 : Blo 323837 489401 := bstep (se 2 (by rfl) ⟨183525, by rfl⟩ : syracuseStep 489401 = 367051) B367051
theorem B325563 : Blo 323837 325563 := bstep (se 1 (by rfl) ⟨244172, by rfl⟩ : syracuseStep 325563 = 488345) B488345
theorem B1865693 : Blo 323837 1865693 := bstep (se 3 (by rfl) ⟨349817, by rfl⟩ : syracuseStep 1865693 = 699635) B699635
theorem B325639 : Blo 323837 325639 := bstep (se 1 (by rfl) ⟨244229, by rfl⟩ : syracuseStep 325639 = 488459) B488459
theorem B489479 : Blo 323837 489479 := bstep (se 1 (by rfl) ⟨367109, by rfl⟩ : syracuseStep 489479 = 734219) B734219
theorem B325647 : Blo 323837 325647 := bstep (se 1 (by rfl) ⟨244235, by rfl⟩ : syracuseStep 325647 = 488471) B488471
theorem B784399 : Blo 323837 784399 := bstep (se 1 (by rfl) ⟨588299, by rfl⟩ : syracuseStep 784399 = 1176599) B1176599
theorem B489515 : Blo 323837 489515 := bstep (se 1 (by rfl) ⟨367136, by rfl⟩ : syracuseStep 489515 = 734273) B734273
theorem B325691 : Blo 323837 325691 := bstep (se 1 (by rfl) ⟨244268, by rfl⟩ : syracuseStep 325691 = 488537) B488537
theorem B489545 : Blo 323837 489545 := bstep (se 2 (by rfl) ⟨183579, by rfl⟩ : syracuseStep 489545 = 367159) B367159
theorem B325767 : Blo 323837 325767 := bstep (se 1 (by rfl) ⟨244325, by rfl⟩ : syracuseStep 325767 = 488651) B488651
theorem B587911 : Blo 323837 587911 := bstep (se 1 (by rfl) ⟨440933, by rfl⟩ : syracuseStep 587911 = 881867) B881867
theorem B325775 : Blo 323837 325775 := bstep (se 1 (by rfl) ⟨244331, by rfl⟩ : syracuseStep 325775 = 488663) B488663
theorem B325819 : Blo 323837 325819 := bstep (se 1 (by rfl) ⟨244364, by rfl⟩ : syracuseStep 325819 = 488729) B488729
theorem B489659 : Blo 323837 489659 := bstep (se 1 (by rfl) ⟨367244, by rfl⟩ : syracuseStep 489659 = 734489) B734489
theorem B489719 : Blo 323837 489719 := bstep (se 1 (by rfl) ⟨367289, by rfl⟩ : syracuseStep 489719 = 734579) B734579
theorem B325895 : Blo 323837 325895 := bstep (se 1 (by rfl) ⟨244421, by rfl⟩ : syracuseStep 325895 = 488843) B488843
theorem B325903 : Blo 323837 325903 := bstep (se 1 (by rfl) ⟨244427, by rfl⟩ : syracuseStep 325903 = 488855) B488855
theorem B489743 : Blo 323837 489743 := bstep (se 1 (by rfl) ⟨367307, by rfl⟩ : syracuseStep 489743 = 734615) B734615
theorem B489785 : Blo 323837 489785 := bstep (se 2 (by rfl) ⟨183669, by rfl⟩ : syracuseStep 489785 = 367339) B367339
theorem B325947 : Blo 323837 325947 := bstep (se 1 (by rfl) ⟨244460, by rfl⟩ : syracuseStep 325947 = 488921) B488921
theorem B326023 : Blo 323837 326023 := bstep (se 1 (by rfl) ⟨244517, by rfl⟩ : syracuseStep 326023 = 489035) B489035
theorem B489863 : Blo 323837 489863 := bstep (se 1 (by rfl) ⟨367397, by rfl⟩ : syracuseStep 489863 = 734795) B734795
theorem B326031 : Blo 323837 326031 := bstep (se 1 (by rfl) ⟨244523, by rfl⟩ : syracuseStep 326031 = 489047) B489047
theorem B489899 : Blo 323837 489899 := bstep (se 1 (by rfl) ⟨367424, by rfl⟩ : syracuseStep 489899 = 734849) B734849
theorem B326075 : Blo 323837 326075 := bstep (se 1 (by rfl) ⟨244556, by rfl⟩ : syracuseStep 326075 = 489113) B489113
theorem B489929 : Blo 323837 489929 := bstep (se 2 (by rfl) ⟨183723, by rfl⟩ : syracuseStep 489929 = 367447) B367447
theorem B326151 : Blo 323837 326151 := bstep (se 1 (by rfl) ⟨244613, by rfl⟩ : syracuseStep 326151 = 489227) B489227
theorem B326159 : Blo 323837 326159 := bstep (se 1 (by rfl) ⟨244619, by rfl⟩ : syracuseStep 326159 = 489239) B489239
theorem B1178155 : Blo 323837 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B326203 : Blo 323837 326203 := bstep (se 1 (by rfl) ⟨244652, by rfl⟩ : syracuseStep 326203 = 489305) B489305
theorem B490043 : Blo 323837 490043 := bstep (se 1 (by rfl) ⟨367532, by rfl⟩ : syracuseStep 490043 = 735065) B735065
theorem B785015 : Blo 323837 785015 := bstep (se 1 (by rfl) ⟨588761, by rfl⟩ : syracuseStep 785015 = 1177523) B1177523
theorem B490103 : Blo 323837 490103 := bstep (se 1 (by rfl) ⟨367577, by rfl⟩ : syracuseStep 490103 = 735155) B735155
theorem B326279 : Blo 323837 326279 := bstep (se 1 (by rfl) ⟨244709, by rfl⟩ : syracuseStep 326279 = 489419) B489419
theorem B326287 : Blo 323837 326287 := bstep (se 1 (by rfl) ⟨244715, by rfl⟩ : syracuseStep 326287 = 489431) B489431
theorem B490127 : Blo 323837 490127 := bstep (se 1 (by rfl) ⟨367595, by rfl⟩ : syracuseStep 490127 = 735191) B735191
theorem B490169 : Blo 323837 490169 := bstep (se 2 (by rfl) ⟨183813, by rfl⟩ : syracuseStep 490169 = 367627) B367627
theorem B326331 : Blo 323837 326331 := bstep (se 1 (by rfl) ⟨244748, by rfl⟩ : syracuseStep 326331 = 489497) B489497
theorem B326407 : Blo 323837 326407 := bstep (se 1 (by rfl) ⟨244805, by rfl⟩ : syracuseStep 326407 = 489611) B489611
theorem B490247 : Blo 323837 490247 := bstep (se 1 (by rfl) ⟨367685, by rfl⟩ : syracuseStep 490247 = 735371) B735371
theorem B326415 : Blo 323837 326415 := bstep (se 1 (by rfl) ⟨244811, by rfl⟩ : syracuseStep 326415 = 489623) B489623
theorem B490283 : Blo 323837 490283 := bstep (se 1 (by rfl) ⟨367712, by rfl⟩ : syracuseStep 490283 = 735425) B735425
theorem B326459 : Blo 323837 326459 := bstep (se 1 (by rfl) ⟨244844, by rfl⟩ : syracuseStep 326459 = 489689) B489689
theorem B490313 : Blo 323837 490313 := bstep (se 2 (by rfl) ⟨183867, by rfl⟩ : syracuseStep 490313 = 367735) B367735
theorem B326535 : Blo 323837 326535 := bstep (se 1 (by rfl) ⟨244901, by rfl⟩ : syracuseStep 326535 = 489803) B489803
theorem B1571719 : Blo 323837 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B326543 : Blo 323837 326543 := bstep (se 1 (by rfl) ⟨244907, by rfl⟩ : syracuseStep 326543 = 489815) B489815
theorem B326587 : Blo 323837 326587 := bstep (se 1 (by rfl) ⟨244940, by rfl⟩ : syracuseStep 326587 = 489881) B489881
theorem B490427 : Blo 323837 490427 := bstep (se 1 (by rfl) ⟨367820, by rfl⟩ : syracuseStep 490427 = 735641) B735641
theorem B2489291 : Blo 323837 2489291 := bstep (se 1 (by rfl) ⟨1866968, by rfl⟩ : syracuseStep 2489291 = 3733937) B3733937
theorem B490487 : Blo 323837 490487 := bstep (se 1 (by rfl) ⟨367865, by rfl⟩ : syracuseStep 490487 = 735731) B735731
theorem B326663 : Blo 323837 326663 := bstep (se 1 (by rfl) ⟨244997, by rfl⟩ : syracuseStep 326663 = 489995) B489995
theorem B326671 : Blo 323837 326671 := bstep (se 1 (by rfl) ⟨245003, by rfl⟩ : syracuseStep 326671 = 490007) B490007
theorem B490511 : Blo 323837 490511 := bstep (se 1 (by rfl) ⟨367883, by rfl⟩ : syracuseStep 490511 = 735767) B735767
theorem B490553 : Blo 323837 490553 := bstep (se 2 (by rfl) ⟨183957, by rfl⟩ : syracuseStep 490553 = 367915) B367915
theorem B326715 : Blo 323837 326715 := bstep (se 1 (by rfl) ⟨245036, by rfl⟩ : syracuseStep 326715 = 490073) B490073
theorem B785467 : Blo 323837 785467 := bstep (se 1 (by rfl) ⟨589100, by rfl⟩ : syracuseStep 785467 = 1178201) B1178201
theorem B326791 : Blo 323837 326791 := bstep (se 1 (by rfl) ⟨245093, by rfl⟩ : syracuseStep 326791 = 490187) B490187
theorem B785543 : Blo 323837 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B490631 : Blo 323837 490631 := bstep (se 1 (by rfl) ⟨367973, by rfl⟩ : syracuseStep 490631 = 735947) B735947
theorem B326799 : Blo 323837 326799 := bstep (se 1 (by rfl) ⟨245099, by rfl⟩ : syracuseStep 326799 = 490199) B490199
theorem B490667 : Blo 323837 490667 := bstep (se 1 (by rfl) ⟨368000, by rfl⟩ : syracuseStep 490667 = 736001) B736001
theorem B326843 : Blo 323837 326843 := bstep (se 1 (by rfl) ⟨245132, by rfl⟩ : syracuseStep 326843 = 490265) B490265
theorem B490697 : Blo 323837 490697 := bstep (se 2 (by rfl) ⟨184011, by rfl⟩ : syracuseStep 490697 = 368023) B368023
theorem B621769 : Blo 323837 621769 := bstep (se 2 (by rfl) ⟨233163, by rfl⟩ : syracuseStep 621769 = 466327) B466327
theorem B326919 : Blo 323837 326919 := bstep (se 1 (by rfl) ⟨245189, by rfl⟩ : syracuseStep 326919 = 490379) B490379
theorem B326927 : Blo 323837 326927 := bstep (se 1 (by rfl) ⟨245195, by rfl⟩ : syracuseStep 326927 = 490391) B490391
theorem B326971 : Blo 323837 326971 := bstep (se 1 (by rfl) ⟨245228, by rfl⟩ : syracuseStep 326971 = 490457) B490457
theorem B490811 : Blo 323837 490811 := bstep (se 1 (by rfl) ⟨368108, by rfl⟩ : syracuseStep 490811 = 736217) B736217
theorem B785783 : Blo 323837 785783 := bstep (se 1 (by rfl) ⟨589337, by rfl⟩ : syracuseStep 785783 = 1178675) B1178675
theorem B490871 : Blo 323837 490871 := bstep (se 1 (by rfl) ⟨368153, by rfl⟩ : syracuseStep 490871 = 736307) B736307
theorem B327047 : Blo 323837 327047 := bstep (se 1 (by rfl) ⟨245285, by rfl⟩ : syracuseStep 327047 = 490571) B490571
theorem B327055 : Blo 323837 327055 := bstep (se 1 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 327055 = 490583) B490583
theorem B490895 : Blo 323837 490895 := bstep (se 1 (by rfl) ⟨368171, by rfl⟩ : syracuseStep 490895 = 736343) B736343
theorem B490937 : Blo 323837 490937 := bstep (se 2 (by rfl) ⟨184101, by rfl⟩ : syracuseStep 490937 = 368203) B368203
theorem B327099 : Blo 323837 327099 := bstep (se 1 (by rfl) ⟨245324, by rfl⟩ : syracuseStep 327099 = 490649) B490649
theorem B1572317 : Blo 323837 1572317 := bstep (se 3 (by rfl) ⟨294809, by rfl⟩ : syracuseStep 1572317 = 589619) B589619
theorem B327175 : Blo 323837 327175 := bstep (se 1 (by rfl) ⟨245381, by rfl⟩ : syracuseStep 327175 = 490763) B490763
theorem B491015 : Blo 323837 491015 := bstep (se 1 (by rfl) ⟨368261, by rfl⟩ : syracuseStep 491015 = 736523) B736523
theorem B327183 : Blo 323837 327183 := bstep (se 1 (by rfl) ⟨245387, by rfl⟩ : syracuseStep 327183 = 490775) B490775
theorem B884267 : Blo 323837 884267 := bstep (se 1 (by rfl) ⟨663200, by rfl⟩ : syracuseStep 884267 = 1326401) B1326401
theorem B491051 : Blo 323837 491051 := bstep (se 1 (by rfl) ⟨368288, by rfl⟩ : syracuseStep 491051 = 736577) B736577
theorem B327227 : Blo 323837 327227 := bstep (se 1 (by rfl) ⟨245420, by rfl⟩ : syracuseStep 327227 = 490841) B490841
theorem B491081 : Blo 323837 491081 := bstep (se 2 (by rfl) ⟨184155, by rfl⟩ : syracuseStep 491081 = 368311) B368311
theorem B8027747 : Blo 323837 8027747 := bstep (se 1 (by rfl) ⟨6020810, by rfl⟩ : syracuseStep 8027747 = 12041621) B12041621
theorem B327303 : Blo 323837 327303 := bstep (se 1 (by rfl) ⟨245477, by rfl⟩ : syracuseStep 327303 = 490955) B490955
theorem B327311 : Blo 323837 327311 := bstep (se 1 (by rfl) ⟨245483, by rfl⟩ : syracuseStep 327311 = 490967) B490967
theorem B327355 : Blo 323837 327355 := bstep (se 1 (by rfl) ⟨245516, by rfl⟩ : syracuseStep 327355 = 491033) B491033
theorem B491195 : Blo 323837 491195 := bstep (se 1 (by rfl) ⟨368396, by rfl⟩ : syracuseStep 491195 = 736793) B736793
theorem B491255 : Blo 323837 491255 := bstep (se 1 (by rfl) ⟨368441, by rfl⟩ : syracuseStep 491255 = 736883) B736883
theorem B327431 : Blo 323837 327431 := bstep (se 1 (by rfl) ⟨245573, by rfl⟩ : syracuseStep 327431 = 491147) B491147
theorem B327439 : Blo 323837 327439 := bstep (se 1 (by rfl) ⟨245579, by rfl⟩ : syracuseStep 327439 = 491159) B491159
theorem B491279 : Blo 323837 491279 := bstep (se 1 (by rfl) ⟨368459, by rfl⟩ : syracuseStep 491279 = 736919) B736919
theorem B491321 : Blo 323837 491321 := bstep (se 2 (by rfl) ⟨184245, by rfl⟩ : syracuseStep 491321 = 368491) B368491
theorem B327483 : Blo 323837 327483 := bstep (se 1 (by rfl) ⟨245612, by rfl⟩ : syracuseStep 327483 = 491225) B491225
theorem B327559 : Blo 323837 327559 := bstep (se 1 (by rfl) ⟨245669, by rfl⟩ : syracuseStep 327559 = 491339) B491339
theorem B491399 : Blo 323837 491399 := bstep (se 1 (by rfl) ⟨368549, by rfl⟩ : syracuseStep 491399 = 737099) B737099
theorem B393103 : Blo 323837 393103 := bstep (se 1 (by rfl) ⟨294827, by rfl⟩ : syracuseStep 393103 = 589655) B589655
theorem B327567 : Blo 323837 327567 := bstep (se 1 (by rfl) ⟨245675, by rfl⟩ : syracuseStep 327567 = 491351) B491351
theorem B491435 : Blo 323837 491435 := bstep (se 1 (by rfl) ⟨368576, by rfl⟩ : syracuseStep 491435 = 737153) B737153
theorem B327611 : Blo 323837 327611 := bstep (se 1 (by rfl) ⟨245708, by rfl⟩ : syracuseStep 327611 = 491417) B491417
theorem B491465 : Blo 323837 491465 := bstep (se 2 (by rfl) ⟨184299, by rfl⟩ : syracuseStep 491465 = 368599) B368599
theorem B327719 : Blo 323837 327719 := bstep (se 1 (by rfl) ⟨245789, by rfl⟩ : syracuseStep 327719 = 491579) B491579
theorem B327759 : Blo 323837 327759 := bstep (se 1 (by rfl) ⟨245819, by rfl⟩ : syracuseStep 327759 = 491639) B491639
theorem B327775 : Blo 323837 327775 := bstep (se 1 (by rfl) ⟨245831, by rfl⟩ : syracuseStep 327775 = 491663) B491663
theorem B327803 : Blo 323837 327803 := bstep (se 1 (by rfl) ⟨245852, by rfl⟩ : syracuseStep 327803 = 491705) B491705
theorem B3703319 : Blo 323837 3703319 := bstep (se 1 (by rfl) ⟨2777489, by rfl⟩ : syracuseStep 3703319 = 5554979) B5554979
theorem B9372185 : Blo 323837 9372185 := bstep (se 2 (by rfl) ⟨3514569, by rfl⟩ : syracuseStep 9372185 = 7029139) B7029139
theorem B590375 : Blo 323837 590375 := bstep (se 1 (by rfl) ⟨442781, by rfl⟩ : syracuseStep 590375 = 885563) B885563
theorem B525047 : Blo 323837 525047 := bstep (se 1 (by rfl) ⟨393785, by rfl⟩ : syracuseStep 525047 = 787571) B787571
theorem B1344365 : Blo 323837 1344365 := bstep (se 3 (by rfl) ⟨252068, by rfl⟩ : syracuseStep 1344365 = 504137) B504137
theorem B787475 : Blo 323837 787475 := bstep (se 1 (by rfl) ⟨590606, by rfl⟩ : syracuseStep 787475 = 1181213) B1181213
theorem B5309489 : Blo 323837 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B2589763 : Blo 323837 2589763 := bstep (se 1 (by rfl) ⟨1942322, by rfl⟩ : syracuseStep 2589763 = 3884645) B3884645
theorem B1181243 : Blo 323837 1181243 := bstep (se 1 (by rfl) ⟨885932, by rfl⟩ : syracuseStep 1181243 = 1771865) B1771865
theorem B821087 : Blo 323837 821087 := bstep (se 1 (by rfl) ⟨615815, by rfl⟩ : syracuseStep 821087 = 1231631) B1231631
theorem B2787331 : Blo 323837 2787331 := bstep (se 1 (by rfl) ⟨2090498, by rfl⟩ : syracuseStep 2787331 = 4180997) B4180997
theorem B624719 : Blo 323837 624719 := bstep (se 1 (by rfl) ⟨468539, by rfl⟩ : syracuseStep 624719 = 937079) B937079
theorem B1607795 : Blo 323837 1607795 := bstep (se 1 (by rfl) ⟨1205846, by rfl⟩ : syracuseStep 1607795 = 2411693) B2411693
theorem B461161 : Blo 323837 461161 := bstep (se 2 (by rfl) ⟨172935, by rfl⟩ : syracuseStep 461161 = 345871) B345871
theorem B821785 : Blo 323837 821785 := bstep (se 2 (by rfl) ⟨308169, by rfl⟩ : syracuseStep 821785 = 616339) B616339
theorem B822089 : Blo 323837 822089 := bstep (se 2 (by rfl) ⟨308283, by rfl⟩ : syracuseStep 822089 = 616567) B616567
theorem B2100113 : Blo 323837 2100113 := bstep (se 2 (by rfl) ⟨787542, by rfl⟩ : syracuseStep 2100113 = 1575085) B1575085
theorem B3345299 : Blo 323837 3345299 := bstep (se 1 (by rfl) ⟨2508974, by rfl⟩ : syracuseStep 3345299 = 5017949) B5017949
theorem B3313021 : Blo 323837 3313021 := bstep (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) B1242383
theorem B2723291 : Blo 323837 2723291 := bstep (se 1 (by rfl) ⟨2042468, by rfl⟩ : syracuseStep 2723291 = 4084937) B4084937
theorem B4034285 : Blo 323837 4034285 := bstep (se 3 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 4034285 = 1512857) B1512857
theorem B1314721 : Blo 323837 1314721 := bstep (se 2 (by rfl) ⟨493020, by rfl⟩ : syracuseStep 1314721 = 986041) B986041
theorem B823223 : Blo 323837 823223 := bstep (se 1 (by rfl) ⟨617417, by rfl⟩ : syracuseStep 823223 = 1234835) B1234835
theorem B21073931 : Blo 323837 21073931 := bstep (se 1 (by rfl) ⟨15805448, by rfl⟩ : syracuseStep 21073931 = 31610897) B31610897
theorem B3150359 : Blo 323837 3150359 := bstep (se 1 (by rfl) ⟨2362769, by rfl⟩ : syracuseStep 3150359 = 4725539) B4725539
theorem B463439 : Blo 323837 463439 := bstep (se 1 (by rfl) ⟨347579, by rfl⟩ : syracuseStep 463439 = 695159) B695159
theorem B365179 : Blo 323837 365179 := bstep (se 1 (by rfl) ⟨273884, by rfl⟩ : syracuseStep 365179 = 547769) B547769
theorem B889483 : Blo 323837 889483 := bstep (se 1 (by rfl) ⟨667112, by rfl⟩ : syracuseStep 889483 = 1334225) B1334225
theorem B4690705 : Blo 323837 4690705 := bstep (se 2 (by rfl) ⟨1759014, by rfl⟩ : syracuseStep 4690705 = 3518029) B3518029
theorem B14160689 : Blo 323837 14160689 := bstep (se 2 (by rfl) ⟨5310258, by rfl⟩ : syracuseStep 14160689 = 10620517) B10620517
theorem B824327 : Blo 323837 824327 := bstep (se 1 (by rfl) ⟨618245, by rfl⟩ : syracuseStep 824327 = 1236491) B1236491
theorem B824377 : Blo 323837 824377 := bstep (se 2 (by rfl) ⟨309141, by rfl⟩ : syracuseStep 824377 = 618283) B618283
theorem B365647 : Blo 323837 365647 := bstep (se 1 (by rfl) ⟨274235, by rfl⟩ : syracuseStep 365647 = 548471) B548471
theorem B3118297 : Blo 323837 3118297 := bstep (se 2 (by rfl) ⟨1169361, by rfl⟩ : syracuseStep 3118297 = 2338723) B2338723
theorem B660727 : Blo 323837 660727 := bstep (se 1 (by rfl) ⟨495545, by rfl⟩ : syracuseStep 660727 = 991091) B991091
theorem B824681 : Blo 323837 824681 := bstep (se 2 (by rfl) ⟨309255, by rfl⟩ : syracuseStep 824681 = 618511) B618511
theorem B923005 : Blo 323837 923005 := bstep (se 3 (by rfl) ⟨173063, by rfl⟩ : syracuseStep 923005 = 346127) B346127
theorem B366043 : Blo 323837 366043 := bstep (se 1 (by rfl) ⟨274532, by rfl⟩ : syracuseStep 366043 = 549065) B549065
theorem B5969371 : Blo 323837 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B4462141 : Blo 323837 4462141 := bstep (se 3 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 4462141 = 1673303) B1673303
theorem B923233 : Blo 323837 923233 := bstep (se 2 (by rfl) ⟨346212, by rfl⟩ : syracuseStep 923233 = 692425) B692425
theorem B366511 : Blo 323837 366511 := bstep (se 1 (by rfl) ⟨274883, by rfl⟩ : syracuseStep 366511 = 549767) B549767
theorem B923575 : Blo 323837 923575 := bstep (se 1 (by rfl) ⟨692681, by rfl⟩ : syracuseStep 923575 = 1385363) B1385363
theorem B3119141 : Blo 323837 3119141 := bstep (se 4 (by rfl) ⟨292419, by rfl⟩ : syracuseStep 3119141 = 584839) B584839
theorem B661675 : Blo 323837 661675 := bstep (se 1 (by rfl) ⟨496256, by rfl⟩ : syracuseStep 661675 = 992513) B992513
theorem B366943 : Blo 323837 366943 := bstep (se 1 (by rfl) ⟨275207, by rfl⟩ : syracuseStep 366943 = 550415) B550415
theorem B1776001 : Blo 323837 1776001 := bstep (se 2 (by rfl) ⟨666000, by rfl⟩ : syracuseStep 1776001 = 1332001) B1332001
theorem B367303 : Blo 323837 367303 := bstep (se 1 (by rfl) ⟨275477, by rfl⟩ : syracuseStep 367303 = 550955) B550955
theorem B2530223 : Blo 323837 2530223 := bstep (se 1 (by rfl) ⟨1897667, by rfl⟩ : syracuseStep 2530223 = 3795335) B3795335
theorem B924691 : Blo 323837 924691 := bstep (se 1 (by rfl) ⟨693518, by rfl⟩ : syracuseStep 924691 = 1387037) B1387037
theorem B1186987 : Blo 323837 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B925033 : Blo 323837 925033 := bstep (se 2 (by rfl) ⟨346887, by rfl⟩ : syracuseStep 925033 = 693775) B693775
theorem B12557753 : Blo 323837 12557753 := bstep (se 2 (by rfl) ⟨4709157, by rfl⟩ : syracuseStep 12557753 = 9418315) B9418315
theorem B826919 : Blo 323837 826919 := bstep (se 1 (by rfl) ⟨620189, by rfl⟩ : syracuseStep 826919 = 1240379) B1240379
theorem B368167 : Blo 323837 368167 := bstep (se 1 (by rfl) ⟨276125, by rfl⟩ : syracuseStep 368167 = 552251) B552251
theorem B2629181 : Blo 323837 2629181 := bstep (se 3 (by rfl) ⟨492971, by rfl⟩ : syracuseStep 2629181 = 985943) B985943
theorem B925307 : Blo 323837 925307 := bstep (se 1 (by rfl) ⟨693980, by rfl⟩ : syracuseStep 925307 = 1387961) B1387961
theorem B466555 : Blo 323837 466555 := bstep (se 1 (by rfl) ⟨349916, by rfl⟩ : syracuseStep 466555 = 699833) B699833
theorem B1384235 : Blo 323837 1384235 := bstep (se 1 (by rfl) ⟨1038176, by rfl⟩ : syracuseStep 1384235 = 2076353) B2076353
theorem B728927 : Blo 323837 728927 := bstep (se 1 (by rfl) ⟨546695, by rfl⟩ : syracuseStep 728927 = 1093391) B1093391
theorem B630623 : Blo 323837 630623 := bstep (se 1 (by rfl) ⟨472967, by rfl⟩ : syracuseStep 630623 = 945935) B945935
theorem B827243 : Blo 323837 827243 := bstep (se 1 (by rfl) ⟨620432, by rfl⟩ : syracuseStep 827243 = 1240865) B1240865
theorem B729107 : Blo 323837 729107 := bstep (se 1 (by rfl) ⟨546830, by rfl⟩ : syracuseStep 729107 = 1093661) B1093661
theorem B663751 : Blo 323837 663751 := bstep (se 1 (by rfl) ⟨497813, by rfl⟩ : syracuseStep 663751 = 995627) B995627
theorem B729449 : Blo 323837 729449 := bstep (se 2 (by rfl) ⟨273543, by rfl⟩ : syracuseStep 729449 = 547087) B547087
theorem B827891 : Blo 323837 827891 := bstep (se 1 (by rfl) ⟨620918, by rfl⟩ : syracuseStep 827891 = 1241837) B1241837
theorem B828103 : Blo 323837 828103 := bstep (se 1 (by rfl) ⟨621077, by rfl⟩ : syracuseStep 828103 = 1242155) B1242155
theorem B926423 : Blo 323837 926423 := bstep (se 1 (by rfl) ⟨694817, by rfl⟩ : syracuseStep 926423 = 1389635) B1389635
theorem B467887 : Blo 323837 467887 := bstep (se 1 (by rfl) ⟨350915, by rfl⟩ : syracuseStep 467887 = 701831) B701831
theorem B730043 : Blo 323837 730043 := bstep (se 1 (by rfl) ⟨547532, by rfl⟩ : syracuseStep 730043 = 1095065) B1095065
theorem B730169 : Blo 323837 730169 := bstep (se 2 (by rfl) ⟨273813, by rfl⟩ : syracuseStep 730169 = 547627) B547627
theorem B3712067 : Blo 323837 3712067 := bstep (se 1 (by rfl) ⟨2784050, by rfl⟩ : syracuseStep 3712067 = 5568101) B5568101
theorem B2466935 : Blo 323837 2466935 := bstep (se 1 (by rfl) ⟨1850201, by rfl⟩ : syracuseStep 2466935 = 3700403) B3700403
theorem B1647863 : Blo 323837 1647863 := bstep (se 1 (by rfl) ⟨1235897, by rfl⟩ : syracuseStep 1647863 = 2471795) B2471795
theorem B730511 : Blo 323837 730511 := bstep (se 1 (by rfl) ⟨547883, by rfl⟩ : syracuseStep 730511 = 1095767) B1095767
theorem B829025 : Blo 323837 829025 := bstep (se 2 (by rfl) ⟨310884, by rfl⟩ : syracuseStep 829025 = 621769) B621769
theorem B468679 : Blo 323837 468679 := bstep (se 1 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 468679 = 703019) B703019
theorem B730835 : Blo 323837 730835 := bstep (se 1 (by rfl) ⟨548126, by rfl⟩ : syracuseStep 730835 = 1096253) B1096253
theorem B1648349 : Blo 323837 1648349 := bstep (se 3 (by rfl) ⟨309065, by rfl⟩ : syracuseStep 1648349 = 618131) B618131
theorem B1451963 : Blo 323837 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B5351831 : Blo 323837 5351831 := bstep (se 1 (by rfl) ⟨4013873, by rfl⟩ : syracuseStep 5351831 = 8027747) B8027747
theorem B731771 : Blo 323837 731771 := bstep (se 1 (by rfl) ⟨548828, by rfl⟩ : syracuseStep 731771 = 1097657) B1097657
theorem B731897 : Blo 323837 731897 := bstep (se 2 (by rfl) ⟨274461, by rfl⟩ : syracuseStep 731897 = 548923) B548923
theorem B502633 : Blo 323837 502633 := bstep (se 2 (by rfl) ⟨188487, by rfl⟩ : syracuseStep 502633 = 376975) B376975
theorem B732167 : Blo 323837 732167 := bstep (se 1 (by rfl) ⟨549125, by rfl⟩ : syracuseStep 732167 = 1098251) B1098251
theorem B732239 : Blo 323837 732239 := bstep (se 1 (by rfl) ⟨549179, by rfl⟩ : syracuseStep 732239 = 1098359) B1098359
theorem B9972823 : Blo 323837 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B30125357 : Blo 323837 30125357 := bstep (se 3 (by rfl) ⟨5648504, by rfl⟩ : syracuseStep 30125357 = 11297009) B11297009
theorem B732635 : Blo 323837 732635 := bstep (se 1 (by rfl) ⟨549476, by rfl⟩ : syracuseStep 732635 = 1098953) B1098953
theorem B699943 : Blo 323837 699943 := bstep (se 1 (by rfl) ⟨524957, by rfl⟩ : syracuseStep 699943 = 1049915) B1049915
theorem B1486433 : Blo 323837 1486433 := bstep (se 2 (by rfl) ⟨557412, by rfl⟩ : syracuseStep 1486433 = 1114825) B1114825
theorem B733103 : Blo 323837 733103 := bstep (se 1 (by rfl) ⟨549827, by rfl⟩ : syracuseStep 733103 = 1099655) B1099655
theorem B471079 : Blo 323837 471079 := bstep (se 1 (by rfl) ⟨353309, by rfl⟩ : syracuseStep 471079 = 706619) B706619
theorem B733355 : Blo 323837 733355 := bstep (se 1 (by rfl) ⟨550016, by rfl⟩ : syracuseStep 733355 = 1100033) B1100033
theorem B733895 : Blo 323837 733895 := bstep (se 1 (by rfl) ⟨550421, by rfl⟩ : syracuseStep 733895 = 1100843) B1100843
theorem B6337739 : Blo 323837 6337739 := bstep (se 1 (by rfl) ⟨4753304, by rfl⟩ : syracuseStep 6337739 = 9506609) B9506609
theorem B1094903 : Blo 323837 1094903 := bstep (se 1 (by rfl) ⟨821177, by rfl⟩ : syracuseStep 1094903 = 1642355) B1642355
theorem B2241917 : Blo 323837 2241917 := bstep (se 3 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 2241917 = 840719) B840719
theorem B2078095 : Blo 323837 2078095 := bstep (se 1 (by rfl) ⟨1558571, by rfl⟩ : syracuseStep 2078095 = 3117143) B3117143
theorem B734759 : Blo 323837 734759 := bstep (se 1 (by rfl) ⟨551069, by rfl⟩ : syracuseStep 734759 = 1102139) B1102139
theorem B1324583 : Blo 323837 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B1095227 : Blo 323837 1095227 := bstep (se 1 (by rfl) ⟨821420, by rfl⟩ : syracuseStep 1095227 = 1642841) B1642841
theorem B2340485 : Blo 323837 2340485 := bstep (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) B438841
theorem B1357511 : Blo 323837 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B1095497 : Blo 323837 1095497 := bstep (se 2 (by rfl) ⟨410811, by rfl⟩ : syracuseStep 1095497 = 821623) B821623
theorem B735083 : Blo 323837 735083 := bstep (se 1 (by rfl) ⟨551312, by rfl⟩ : syracuseStep 735083 = 1102625) B1102625
theorem B1324907 : Blo 323837 1324907 := bstep (se 1 (by rfl) ⟨993680, by rfl⟩ : syracuseStep 1324907 = 1987361) B1987361
theorem B735137 : Blo 323837 735137 := bstep (se 2 (by rfl) ⟨275676, by rfl⟩ : syracuseStep 735137 = 551353) B551353
theorem B1325135 : Blo 323837 1325135 := bstep (se 1 (by rfl) ⟨993851, by rfl⟩ : syracuseStep 1325135 = 1987703) B1987703
theorem B735479 : Blo 323837 735479 := bstep (se 1 (by rfl) ⟨551609, by rfl⟩ : syracuseStep 735479 = 1103219) B1103219
theorem B1849837 : Blo 323837 1849837 := bstep (se 3 (by rfl) ⟨346844, by rfl⟩ : syracuseStep 1849837 = 693689) B693689
theorem B1653533 : Blo 323837 1653533 := bstep (se 3 (by rfl) ⟨310037, by rfl⟩ : syracuseStep 1653533 = 620075) B620075
theorem B736073 : Blo 323837 736073 := bstep (se 2 (by rfl) ⟨276027, by rfl⟩ : syracuseStep 736073 = 552055) B552055
theorem B1096631 : Blo 323837 1096631 := bstep (se 1 (by rfl) ⟨822473, by rfl⟩ : syracuseStep 1096631 = 1644947) B1644947
theorem B2473253 : Blo 323837 2473253 := bstep (se 4 (by rfl) ⟨231867, by rfl⟩ : syracuseStep 2473253 = 463735) B463735
theorem B1097225 : Blo 323837 1097225 := bstep (se 2 (by rfl) ⟨411459, by rfl⟩ : syracuseStep 1097225 = 822919) B822919
theorem B736865 : Blo 323837 736865 := bstep (se 2 (by rfl) ⟨276324, by rfl⟩ : syracuseStep 736865 = 552649) B552649
theorem B933565 : Blo 323837 933565 := bstep (se 3 (by rfl) ⟨175043, by rfl⟩ : syracuseStep 933565 = 350087) B350087
theorem B2080505 : Blo 323837 2080505 := bstep (se 2 (by rfl) ⟨780189, by rfl⟩ : syracuseStep 2080505 = 1560379) B1560379
theorem B1752941 : Blo 323837 1752941 := bstep (se 3 (by rfl) ⟨328676, by rfl⟩ : syracuseStep 1752941 = 657353) B657353
theorem B737207 : Blo 323837 737207 := bstep (se 1 (by rfl) ⟨552905, by rfl⟩ : syracuseStep 737207 = 1105811) B1105811
theorem B1392983 : Blo 323837 1392983 := bstep (se 1 (by rfl) ⟨1044737, by rfl⟩ : syracuseStep 1392983 = 2089475) B2089475
theorem B409951 : Blo 323837 409951 := bstep (se 1 (by rfl) ⟨307463, by rfl⟩ : syracuseStep 409951 = 614927) B614927
theorem B1098089 : Blo 323837 1098089 := bstep (se 2 (by rfl) ⟨411783, by rfl⟩ : syracuseStep 1098089 = 823567) B823567
theorem B1131371 : Blo 323837 1131371 := bstep (se 1 (by rfl) ⟨848528, by rfl⟩ : syracuseStep 1131371 = 1697057) B1697057
theorem B1229687 : Blo 323837 1229687 := bstep (se 1 (by rfl) ⟨922265, by rfl⟩ : syracuseStep 1229687 = 1844531) B1844531
theorem B1098683 : Blo 323837 1098683 := bstep (se 1 (by rfl) ⟨824012, by rfl⟩ : syracuseStep 1098683 = 1648025) B1648025
theorem B3130487 : Blo 323837 3130487 := bstep (se 1 (by rfl) ⟨2347865, by rfl⟩ : syracuseStep 3130487 = 4695731) B4695731
theorem B2082503 : Blo 323837 2082503 := bstep (se 1 (by rfl) ⟨1561877, by rfl⟩ : syracuseStep 2082503 = 3123755) B3123755
theorem B1230659 : Blo 323837 1230659 := bstep (se 1 (by rfl) ⟨922994, by rfl⟩ : syracuseStep 1230659 = 1845989) B1845989
theorem B1853279 : Blo 323837 1853279 := bstep (se 1 (by rfl) ⟨1389959, by rfl⟩ : syracuseStep 1853279 = 2779919) B2779919
theorem B11290661 : Blo 323837 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B5130497 : Blo 323837 5130497 := bstep (se 2 (by rfl) ⟨1923936, by rfl⟩ : syracuseStep 5130497 = 3847873) B3847873
theorem B575905 : Blo 323837 575905 := bstep (se 2 (by rfl) ⟨215964, by rfl⟩ : syracuseStep 575905 = 431929) B431929
theorem B412123 : Blo 323837 412123 := bstep (se 1 (by rfl) ⟨309092, by rfl⟩ : syracuseStep 412123 = 618185) B618185
theorem B1100411 : Blo 323837 1100411 := bstep (se 1 (by rfl) ⟨825308, by rfl⟩ : syracuseStep 1100411 = 1650617) B1650617
theorem B1854211 : Blo 323837 1854211 := bstep (se 1 (by rfl) ⟨1390658, by rfl⟩ : syracuseStep 1854211 = 2781317) B2781317
theorem B1231645 : Blo 323837 1231645 := bstep (se 3 (by rfl) ⟨230933, by rfl⟩ : syracuseStep 1231645 = 461867) B461867
theorem B1100573 : Blo 323837 1100573 := bstep (se 3 (by rfl) ⟨206357, by rfl⟩ : syracuseStep 1100573 = 412715) B412715
theorem B2673485 : Blo 323837 2673485 := bstep (se 3 (by rfl) ⟨501278, by rfl⟩ : syracuseStep 2673485 = 1002557) B1002557
theorem B1756079 : Blo 323837 1756079 := bstep (se 1 (by rfl) ⟨1317059, by rfl⟩ : syracuseStep 1756079 = 2634119) B2634119
theorem B1657907 : Blo 323837 1657907 := bstep (se 1 (by rfl) ⟨1243430, by rfl⟩ : syracuseStep 1657907 = 2486861) B2486861
theorem B1101275 : Blo 323837 1101275 := bstep (se 1 (by rfl) ⟨825956, by rfl⟩ : syracuseStep 1101275 = 1651913) B1651913
theorem B1756811 : Blo 323837 1756811 := bstep (se 1 (by rfl) ⟨1317608, by rfl⟩ : syracuseStep 1756811 = 2635217) B2635217
theorem B1494827 : Blo 323837 1494827 := bstep (se 1 (by rfl) ⟨1121120, by rfl⟩ : syracuseStep 1494827 = 2242241) B2242241
theorem B1101977 : Blo 323837 1101977 := bstep (se 2 (by rfl) ⟨413241, by rfl⟩ : syracuseStep 1101977 = 826483) B826483
theorem B1659527 : Blo 323837 1659527 := bstep (se 1 (by rfl) ⟨1244645, by rfl⟩ : syracuseStep 1659527 = 2489291) B2489291
theorem B1103165 : Blo 323837 1103165 := bstep (se 3 (by rfl) ⟨206843, by rfl⟩ : syracuseStep 1103165 = 413687) B413687
theorem B1037971 : Blo 323837 1037971 := bstep (se 1 (by rfl) ⟨778478, by rfl⟩ : syracuseStep 1037971 = 1556957) B1556957
theorem B546655 : Blo 323837 546655 := bstep (se 1 (by rfl) ⟨409991, by rfl⟩ : syracuseStep 546655 = 819983) B819983
theorem B546743 : Blo 323837 546743 := bstep (se 1 (by rfl) ⟨410057, by rfl⟩ : syracuseStep 546743 = 820115) B820115
theorem B2480057 : Blo 323837 2480057 := bstep (se 2 (by rfl) ⟨930021, by rfl⟩ : syracuseStep 2480057 = 1860043) B1860043
theorem B36591587 : Blo 323837 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B1104029 : Blo 323837 1104029 := bstep (se 3 (by rfl) ⟨207005, by rfl⟩ : syracuseStep 1104029 = 414011) B414011
theorem B547337 : Blo 323837 547337 := bstep (se 2 (by rfl) ⟨205251, by rfl⟩ : syracuseStep 547337 = 410503) B410503
theorem B547499 : Blo 323837 547499 := bstep (se 1 (by rfl) ⟨410624, by rfl⟩ : syracuseStep 547499 = 821249) B821249
theorem B1104569 : Blo 323837 1104569 := bstep (se 2 (by rfl) ⟨414213, by rfl⟩ : syracuseStep 1104569 = 828427) B828427
theorem B1235807 : Blo 323837 1235807 := bstep (se 1 (by rfl) ⟨926855, by rfl⟩ : syracuseStep 1235807 = 1853711) B1853711
theorem B4152293 : Blo 323837 4152293 := bstep (se 4 (by rfl) ⟨389277, by rfl⟩ : syracuseStep 4152293 = 778555) B778555
theorem B547897 : Blo 323837 547897 := bstep (se 2 (by rfl) ⟨205461, by rfl⟩ : syracuseStep 547897 = 410923) B410923
theorem B548039 : Blo 323837 548039 := bstep (se 1 (by rfl) ⟨411029, by rfl⟩ : syracuseStep 548039 = 822059) B822059
theorem B1105163 : Blo 323837 1105163 := bstep (se 1 (by rfl) ⟨828872, by rfl⟩ : syracuseStep 1105163 = 1657745) B1657745
theorem B548201 : Blo 323837 548201 := bstep (se 2 (by rfl) ⟨205575, by rfl⟩ : syracuseStep 548201 = 411151) B411151
theorem B1039817 : Blo 323837 1039817 := bstep (se 2 (by rfl) ⟨389931, by rfl⟩ : syracuseStep 1039817 = 779863) B779863
theorem B1236505 : Blo 323837 1236505 := bstep (se 2 (by rfl) ⟨463689, by rfl⟩ : syracuseStep 1236505 = 927379) B927379
theorem B1105433 : Blo 323837 1105433 := bstep (se 2 (by rfl) ⟨414537, by rfl⟩ : syracuseStep 1105433 = 829075) B829075
theorem B1859111 : Blo 323837 1859111 := bstep (se 1 (by rfl) ⟨1394333, by rfl⟩ : syracuseStep 1859111 = 2788667) B2788667
theorem B548599 : Blo 323837 548599 := bstep (se 1 (by rfl) ⟨411449, by rfl⟩ : syracuseStep 548599 = 822899) B822899
theorem B11951887 : Blo 323837 11951887 := bstep (se 1 (by rfl) ⟨8963915, by rfl⟩ : syracuseStep 11951887 = 17927831) B17927831
theorem B1236779 : Blo 323837 1236779 := bstep (se 1 (by rfl) ⟨927584, by rfl⟩ : syracuseStep 1236779 = 1855169) B1855169
theorem B1236809 : Blo 323837 1236809 := bstep (se 2 (by rfl) ⟨463803, by rfl⟩ : syracuseStep 1236809 = 927607) B927607
theorem B352175 : Blo 323837 352175 := bstep (se 1 (by rfl) ⟨264131, by rfl⟩ : syracuseStep 352175 = 528263) B528263
theorem B548795 : Blo 323837 548795 := bstep (se 1 (by rfl) ⟨411596, by rfl⟩ : syracuseStep 548795 = 823193) B823193
theorem B548903 : Blo 323837 548903 := bstep (se 1 (by rfl) ⟨411677, by rfl⟩ : syracuseStep 548903 = 823355) B823355
theorem B6283493 : Blo 323837 6283493 := bstep (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) B1178155
theorem B712951 : Blo 323837 712951 := bstep (se 1 (by rfl) ⟨534713, by rfl⟩ : syracuseStep 712951 = 1069427) B1069427
theorem B549193 : Blo 323837 549193 := bstep (se 2 (by rfl) ⟨205947, by rfl⟩ : syracuseStep 549193 = 411895) B411895
theorem B549227 : Blo 323837 549227 := bstep (se 1 (by rfl) ⟨411920, by rfl⟩ : syracuseStep 549227 = 823841) B823841
theorem B549625 : Blo 323837 549625 := bstep (se 2 (by rfl) ⟨206109, by rfl⟩ : syracuseStep 549625 = 412219) B412219
theorem B2482973 : Blo 323837 2482973 := bstep (se 3 (by rfl) ⟨465557, by rfl⟩ : syracuseStep 2482973 = 931115) B931115
theorem B418655 : Blo 323837 418655 := bstep (se 1 (by rfl) ⟨313991, by rfl⟩ : syracuseStep 418655 = 627983) B627983
theorem B2352017 : Blo 323837 2352017 := bstep (se 2 (by rfl) ⟨882006, by rfl⟩ : syracuseStep 2352017 = 1764013) B1764013
theorem B549895 : Blo 323837 549895 := bstep (se 1 (by rfl) ⟨412421, by rfl⟩ : syracuseStep 549895 = 824843) B824843
theorem B615595 : Blo 323837 615595 := bstep (se 1 (by rfl) ⟨461696, by rfl⟩ : syracuseStep 615595 = 923393) B923393
theorem B4449451 : Blo 323837 4449451 := bstep (se 1 (by rfl) ⟨3337088, by rfl⟩ : syracuseStep 4449451 = 6674177) B6674177
theorem B615671 : Blo 323837 615671 := bstep (se 1 (by rfl) ⟨461753, by rfl⟩ : syracuseStep 615671 = 923507) B923507
theorem B550327 : Blo 323837 550327 := bstep (se 1 (by rfl) ⟨412745, by rfl⟩ : syracuseStep 550327 = 825491) B825491
theorem B615899 : Blo 323837 615899 := bstep (se 1 (by rfl) ⟨461924, by rfl⟩ : syracuseStep 615899 = 923849) B923849
theorem B550523 : Blo 323837 550523 := bstep (se 1 (by rfl) ⟨412892, by rfl⟩ : syracuseStep 550523 = 825785) B825785
theorem B1861319 : Blo 323837 1861319 := bstep (se 1 (by rfl) ⟨1395989, by rfl⟩ : syracuseStep 1861319 = 2791979) B2791979
theorem B4679633 : Blo 323837 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B550921 : Blo 323837 550921 := bstep (se 2 (by rfl) ⟨206595, by rfl⟩ : syracuseStep 550921 = 413191) B413191
theorem B2222095 : Blo 323837 2222095 := bstep (se 1 (by rfl) ⟨1666571, by rfl⟩ : syracuseStep 2222095 = 3333143) B3333143
theorem B1271965 : Blo 323837 1271965 := bstep (se 3 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 1271965 = 476987) B476987
theorem B551083 : Blo 323837 551083 := bstep (se 1 (by rfl) ⟨413312, by rfl⟩ : syracuseStep 551083 = 826625) B826625
theorem B1239421 : Blo 323837 1239421 := bstep (se 3 (by rfl) ⟨232391, by rfl⟩ : syracuseStep 1239421 = 464783) B464783
theorem B485807 : Blo 323837 485807 := bstep (se 1 (by rfl) ⟨364355, by rfl⟩ : syracuseStep 485807 = 728711) B728711
theorem B584119 : Blo 323837 584119 := bstep (se 1 (by rfl) ⟨438089, by rfl⟩ : syracuseStep 584119 = 876179) B876179
theorem B551387 : Blo 323837 551387 := bstep (se 1 (by rfl) ⟨413540, by rfl⟩ : syracuseStep 551387 = 827081) B827081
theorem B485897 : Blo 323837 485897 := bstep (se 2 (by rfl) ⟨182211, by rfl⟩ : syracuseStep 485897 = 364423) B364423
theorem B485927 : Blo 323837 485927 := bstep (se 1 (by rfl) ⟨364445, by rfl⟩ : syracuseStep 485927 = 728891) B728891
theorem B486011 : Blo 323837 486011 := bstep (se 1 (by rfl) ⟨364508, by rfl⟩ : syracuseStep 486011 = 729017) B729017
theorem B1108669 : Blo 323837 1108669 := bstep (se 3 (by rfl) ⟨207875, by rfl⟩ : syracuseStep 1108669 = 415751) B415751
theorem B617159 : Blo 323837 617159 := bstep (se 1 (by rfl) ⟨462869, by rfl⟩ : syracuseStep 617159 = 925739) B925739
theorem B551623 : Blo 323837 551623 := bstep (se 1 (by rfl) ⟨413717, by rfl⟩ : syracuseStep 551623 = 827435) B827435
theorem B486137 : Blo 323837 486137 := bstep (se 2 (by rfl) ⟨182301, by rfl⟩ : syracuseStep 486137 = 364603) B364603
theorem B486239 : Blo 323837 486239 := bstep (se 1 (by rfl) ⟨364679, by rfl⟩ : syracuseStep 486239 = 729359) B729359
theorem B617311 : Blo 323837 617311 := bstep (se 1 (by rfl) ⟨462983, by rfl⟩ : syracuseStep 617311 = 925967) B925967
theorem B551785 : Blo 323837 551785 := bstep (se 2 (by rfl) ⟨206919, by rfl⟩ : syracuseStep 551785 = 413839) B413839
theorem B486251 : Blo 323837 486251 := bstep (se 1 (by rfl) ⟨364688, by rfl⟩ : syracuseStep 486251 = 729377) B729377
theorem B486479 : Blo 323837 486479 := bstep (se 1 (by rfl) ⟨364859, by rfl⟩ : syracuseStep 486479 = 729719) B729719
theorem B1043609 : Blo 323837 1043609 := bstep (se 2 (by rfl) ⟨391353, by rfl⟩ : syracuseStep 1043609 = 782707) B782707
theorem B486599 : Blo 323837 486599 := bstep (se 1 (by rfl) ⟨364949, by rfl⟩ : syracuseStep 486599 = 729899) B729899
theorem B486761 : Blo 323837 486761 := bstep (se 2 (by rfl) ⟨182535, by rfl⟩ : syracuseStep 486761 = 365071) B365071
theorem B486839 : Blo 323837 486839 := bstep (se 1 (by rfl) ⟨365129, by rfl⟩ : syracuseStep 486839 = 730259) B730259
theorem B552379 : Blo 323837 552379 := bstep (se 1 (by rfl) ⟨414284, by rfl⟩ : syracuseStep 552379 = 828569) B828569
theorem B1174985 : Blo 323837 1174985 := bstep (se 2 (by rfl) ⟨440619, by rfl⟩ : syracuseStep 1174985 = 881239) B881239
theorem B486875 : Blo 323837 486875 := bstep (se 1 (by rfl) ⟨365156, by rfl⟩ : syracuseStep 486875 = 730313) B730313
theorem B552487 : Blo 323837 552487 := bstep (se 1 (by rfl) ⟨414365, by rfl⟩ : syracuseStep 552487 = 828731) B828731
theorem B2715275 : Blo 323837 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B552811 : Blo 323837 552811 := bstep (se 1 (by rfl) ⟨414608, by rfl⟩ : syracuseStep 552811 = 829217) B829217
theorem B487343 : Blo 323837 487343 := bstep (se 1 (by rfl) ⟨365507, by rfl⟩ : syracuseStep 487343 = 731015) B731015
theorem B585647 : Blo 323837 585647 := bstep (se 1 (by rfl) ⟨439235, by rfl⟩ : syracuseStep 585647 = 878471) B878471
theorem B389047 : Blo 323837 389047 := bstep (se 1 (by rfl) ⟨291785, by rfl⟩ : syracuseStep 389047 = 583571) B583571
theorem B487433 : Blo 323837 487433 := bstep (se 2 (by rfl) ⟨182787, by rfl⟩ : syracuseStep 487433 = 365575) B365575
theorem B487463 : Blo 323837 487463 := bstep (se 1 (by rfl) ⟨365597, by rfl⟩ : syracuseStep 487463 = 731195) B731195
theorem B487547 : Blo 323837 487547 := bstep (se 1 (by rfl) ⟨365660, by rfl⟩ : syracuseStep 487547 = 731321) B731321
theorem B487673 : Blo 323837 487673 := bstep (se 2 (by rfl) ⟨182877, by rfl⟩ : syracuseStep 487673 = 365755) B365755
theorem B3141899 : Blo 323837 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B323879 : Blo 323837 323879 := bstep (se 1 (by rfl) ⟨242909, by rfl⟩ : syracuseStep 323879 = 485819) B485819
theorem B323919 : Blo 323837 323919 := bstep (se 1 (by rfl) ⟨242939, by rfl⟩ : syracuseStep 323919 = 485879) B485879
theorem B323935 : Blo 323837 323935 := bstep (se 1 (by rfl) ⟨242951, by rfl⟩ : syracuseStep 323935 = 485903) B485903
theorem B487775 : Blo 323837 487775 := bstep (se 1 (by rfl) ⟨365831, by rfl⟩ : syracuseStep 487775 = 731663) B731663
theorem B487787 : Blo 323837 487787 := bstep (se 1 (by rfl) ⟨365840, by rfl⟩ : syracuseStep 487787 = 731681) B731681
theorem B323963 : Blo 323837 323963 := bstep (se 1 (by rfl) ⟨242972, by rfl⟩ : syracuseStep 323963 = 485945) B485945
theorem B324015 : Blo 323837 324015 := bstep (se 1 (by rfl) ⟨243011, by rfl⟩ : syracuseStep 324015 = 486023) B486023
theorem B324039 : Blo 323837 324039 := bstep (se 1 (by rfl) ⟨243029, by rfl⟩ : syracuseStep 324039 = 486059) B486059
theorem B324059 : Blo 323837 324059 := bstep (se 1 (by rfl) ⟨243044, by rfl⟩ : syracuseStep 324059 = 486089) B486089
theorem B324135 : Blo 323837 324135 := bstep (se 1 (by rfl) ⟨243101, by rfl⟩ : syracuseStep 324135 = 486203) B486203
theorem B1241639 : Blo 323837 1241639 := bstep (se 1 (by rfl) ⟨931229, by rfl⟩ : syracuseStep 1241639 = 1862459) B1862459
theorem B2093627 : Blo 323837 2093627 := bstep (se 1 (by rfl) ⟨1570220, by rfl⟩ : syracuseStep 2093627 = 3140441) B3140441
theorem B324175 : Blo 323837 324175 := bstep (se 1 (by rfl) ⟨243131, by rfl⟩ : syracuseStep 324175 = 486263) B486263
theorem B488015 : Blo 323837 488015 := bstep (se 1 (by rfl) ⟨366011, by rfl⟩ : syracuseStep 488015 = 732023) B732023
theorem B324191 : Blo 323837 324191 := bstep (se 1 (by rfl) ⟨243143, by rfl⟩ : syracuseStep 324191 = 486287) B486287
theorem B324219 : Blo 323837 324219 := bstep (se 1 (by rfl) ⟨243164, by rfl⟩ : syracuseStep 324219 = 486329) B486329
theorem B324271 : Blo 323837 324271 := bstep (se 1 (by rfl) ⟨243203, by rfl⟩ : syracuseStep 324271 = 486407) B486407
theorem B324295 : Blo 323837 324295 := bstep (se 1 (by rfl) ⟨243221, by rfl⟩ : syracuseStep 324295 = 486443) B486443
theorem B488135 : Blo 323837 488135 := bstep (se 1 (by rfl) ⟨366101, by rfl⟩ : syracuseStep 488135 = 732203) B732203
theorem B10711763 : Blo 323837 10711763 := bstep (se 1 (by rfl) ⟨8033822, by rfl⟩ : syracuseStep 10711763 = 16067645) B16067645
theorem B2093779 : Blo 323837 2093779 := bstep (se 1 (by rfl) ⟨1570334, by rfl⟩ : syracuseStep 2093779 = 3140669) B3140669
theorem B324315 : Blo 323837 324315 := bstep (se 1 (by rfl) ⟨243236, by rfl⟩ : syracuseStep 324315 = 486473) B486473
theorem B619255 : Blo 323837 619255 := bstep (se 1 (by rfl) ⟨464441, by rfl⟩ : syracuseStep 619255 = 928883) B928883
theorem B7893773 : Blo 323837 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B324391 : Blo 323837 324391 := bstep (se 1 (by rfl) ⟨243293, by rfl⟩ : syracuseStep 324391 = 486587) B486587
theorem B2978633 : Blo 323837 2978633 := bstep (se 2 (by rfl) ⟨1116987, by rfl⟩ : syracuseStep 2978633 = 2233975) B2233975
theorem B324431 : Blo 323837 324431 := bstep (se 1 (by rfl) ⟨243323, by rfl⟩ : syracuseStep 324431 = 486647) B486647
theorem B324447 : Blo 323837 324447 := bstep (se 1 (by rfl) ⟨243335, by rfl⟩ : syracuseStep 324447 = 486671) B486671
theorem B488297 : Blo 323837 488297 := bstep (se 2 (by rfl) ⟨183111, by rfl⟩ : syracuseStep 488297 = 366223) B366223
theorem B324475 : Blo 323837 324475 := bstep (se 1 (by rfl) ⟨243356, by rfl⟩ : syracuseStep 324475 = 486713) B486713
theorem B783265 : Blo 323837 783265 := bstep (se 2 (by rfl) ⟨293724, by rfl⟩ : syracuseStep 783265 = 587449) B587449
theorem B324527 : Blo 323837 324527 := bstep (se 1 (by rfl) ⟨243395, by rfl⟩ : syracuseStep 324527 = 486791) B486791
theorem B488375 : Blo 323837 488375 := bstep (se 1 (by rfl) ⟨366281, by rfl⟩ : syracuseStep 488375 = 732563) B732563
theorem B324551 : Blo 323837 324551 := bstep (se 1 (by rfl) ⟨243413, by rfl⟩ : syracuseStep 324551 = 486827) B486827
theorem B324571 : Blo 323837 324571 := bstep (se 1 (by rfl) ⟨243428, by rfl⟩ : syracuseStep 324571 = 486857) B486857
theorem B488411 : Blo 323837 488411 := bstep (se 1 (by rfl) ⟨366308, by rfl⟩ : syracuseStep 488411 = 732617) B732617
theorem B619483 : Blo 323837 619483 := bstep (se 1 (by rfl) ⟨464612, by rfl⟩ : syracuseStep 619483 = 929225) B929225
theorem B2814977 : Blo 323837 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B324647 : Blo 323837 324647 := bstep (se 1 (by rfl) ⟨243485, by rfl⟩ : syracuseStep 324647 = 486971) B486971
theorem B619559 : Blo 323837 619559 := bstep (se 1 (by rfl) ⟨464669, by rfl⟩ : syracuseStep 619559 = 929339) B929339
theorem B2487347 : Blo 323837 2487347 := bstep (se 1 (by rfl) ⟨1865510, by rfl⟩ : syracuseStep 2487347 = 3731021) B3731021
theorem B324687 : Blo 323837 324687 := bstep (se 1 (by rfl) ⟨243515, by rfl⟩ : syracuseStep 324687 = 487031) B487031
theorem B324703 : Blo 323837 324703 := bstep (se 1 (by rfl) ⟨243527, by rfl⟩ : syracuseStep 324703 = 487055) B487055
theorem B324731 : Blo 323837 324731 := bstep (se 1 (by rfl) ⟨243548, by rfl⟩ : syracuseStep 324731 = 487097) B487097
theorem B619643 : Blo 323837 619643 := bstep (se 1 (by rfl) ⟨464732, by rfl⟩ : syracuseStep 619643 = 929465) B929465
theorem B324783 : Blo 323837 324783 := bstep (se 1 (by rfl) ⟨243587, by rfl⟩ : syracuseStep 324783 = 487175) B487175
theorem B324807 : Blo 323837 324807 := bstep (se 1 (by rfl) ⟨243605, by rfl⟩ : syracuseStep 324807 = 487211) B487211
theorem B324827 : Blo 323837 324827 := bstep (se 1 (by rfl) ⟨243620, by rfl⟩ : syracuseStep 324827 = 487241) B487241
theorem B324903 : Blo 323837 324903 := bstep (se 1 (by rfl) ⟨243677, by rfl⟩ : syracuseStep 324903 = 487355) B487355
theorem B324943 : Blo 323837 324943 := bstep (se 1 (by rfl) ⟨243707, by rfl⟩ : syracuseStep 324943 = 487415) B487415
theorem B324959 : Blo 323837 324959 := bstep (se 1 (by rfl) ⟨243719, by rfl⟩ : syracuseStep 324959 = 487439) B487439
theorem B1045865 : Blo 323837 1045865 := bstep (se 2 (by rfl) ⟨392199, by rfl⟩ : syracuseStep 1045865 = 784399) B784399
theorem B554347 : Blo 323837 554347 := bstep (se 1 (by rfl) ⟨415760, by rfl⟩ : syracuseStep 554347 = 831521) B831521
theorem B324987 : Blo 323837 324987 := bstep (se 1 (by rfl) ⟨243740, by rfl⟩ : syracuseStep 324987 = 487481) B487481
theorem B325039 : Blo 323837 325039 := bstep (se 1 (by rfl) ⟨243779, by rfl⟩ : syracuseStep 325039 = 487559) B487559
theorem B488879 : Blo 323837 488879 := bstep (se 1 (by rfl) ⟨366659, by rfl⟩ : syracuseStep 488879 = 733319) B733319
theorem B325063 : Blo 323837 325063 := bstep (se 1 (by rfl) ⟨243797, by rfl⟩ : syracuseStep 325063 = 487595) B487595
theorem B325083 : Blo 323837 325083 := bstep (se 1 (by rfl) ⟨243812, by rfl⟩ : syracuseStep 325083 = 487625) B487625
theorem B390619 : Blo 323837 390619 := bstep (se 1 (by rfl) ⟨292964, by rfl⟩ : syracuseStep 390619 = 585929) B585929
theorem B1242611 : Blo 323837 1242611 := bstep (se 1 (by rfl) ⟨931958, by rfl⟩ : syracuseStep 1242611 = 1863917) B1863917
theorem B488969 : Blo 323837 488969 := bstep (se 2 (by rfl) ⟨183363, by rfl⟩ : syracuseStep 488969 = 366727) B366727
theorem B783881 : Blo 323837 783881 := bstep (se 2 (by rfl) ⟨293955, by rfl⟩ : syracuseStep 783881 = 587911) B587911
theorem B325159 : Blo 323837 325159 := bstep (se 1 (by rfl) ⟨243869, by rfl⟩ : syracuseStep 325159 = 487739) B487739
theorem B488999 : Blo 323837 488999 := bstep (se 1 (by rfl) ⟨366749, by rfl⟩ : syracuseStep 488999 = 733499) B733499
theorem B2356775 : Blo 323837 2356775 := bstep (se 1 (by rfl) ⟨1767581, by rfl⟩ : syracuseStep 2356775 = 3535163) B3535163
theorem B325199 : Blo 323837 325199 := bstep (se 1 (by rfl) ⟨243899, by rfl⟩ : syracuseStep 325199 = 487799) B487799
theorem B325215 : Blo 323837 325215 := bstep (se 1 (by rfl) ⟨243911, by rfl⟩ : syracuseStep 325215 = 487823) B487823
theorem B620129 : Blo 323837 620129 := bstep (se 2 (by rfl) ⟨232548, by rfl⟩ : syracuseStep 620129 = 465097) B465097
theorem B325243 : Blo 323837 325243 := bstep (se 1 (by rfl) ⟨243932, by rfl⟩ : syracuseStep 325243 = 487865) B487865
theorem B489083 : Blo 323837 489083 := bstep (se 1 (by rfl) ⟨366812, by rfl⟩ : syracuseStep 489083 = 733625) B733625
theorem B325295 : Blo 323837 325295 := bstep (se 1 (by rfl) ⟨243971, by rfl⟩ : syracuseStep 325295 = 487943) B487943
theorem B1242809 : Blo 323837 1242809 := bstep (se 2 (by rfl) ⟨466053, by rfl⟩ : syracuseStep 1242809 = 932107) B932107
theorem B2094781 : Blo 323837 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B325319 : Blo 323837 325319 := bstep (se 1 (by rfl) ⟨243989, by rfl⟩ : syracuseStep 325319 = 487979) B487979
theorem B1242823 : Blo 323837 1242823 := bstep (se 1 (by rfl) ⟨932117, by rfl⟩ : syracuseStep 1242823 = 1864235) B1864235
theorem B325339 : Blo 323837 325339 := bstep (se 1 (by rfl) ⟨244004, by rfl⟩ : syracuseStep 325339 = 488009) B488009
theorem B489209 : Blo 323837 489209 := bstep (se 2 (by rfl) ⟨183453, by rfl⟩ : syracuseStep 489209 = 366907) B366907
theorem B325415 : Blo 323837 325415 := bstep (se 1 (by rfl) ⟨244061, by rfl⟩ : syracuseStep 325415 = 488123) B488123
theorem B325455 : Blo 323837 325455 := bstep (se 1 (by rfl) ⟨244091, by rfl⟩ : syracuseStep 325455 = 488183) B488183
theorem B325471 : Blo 323837 325471 := bstep (se 1 (by rfl) ⟨244103, by rfl⟩ : syracuseStep 325471 = 488207) B488207
theorem B489311 : Blo 323837 489311 := bstep (se 1 (by rfl) ⟨366983, by rfl⟩ : syracuseStep 489311 = 733967) B733967
theorem B489323 : Blo 323837 489323 := bstep (se 1 (by rfl) ⟨366992, by rfl⟩ : syracuseStep 489323 = 733985) B733985
theorem B325499 : Blo 323837 325499 := bstep (se 1 (by rfl) ⟨244124, by rfl⟩ : syracuseStep 325499 = 488249) B488249
theorem B325551 : Blo 323837 325551 := bstep (se 1 (by rfl) ⟨244163, by rfl⟩ : syracuseStep 325551 = 488327) B488327
theorem B325575 : Blo 323837 325575 := bstep (se 1 (by rfl) ⟨244181, by rfl⟩ : syracuseStep 325575 = 488363) B488363
theorem B325595 : Blo 323837 325595 := bstep (se 1 (by rfl) ⟨244196, by rfl⟩ : syracuseStep 325595 = 488393) B488393
theorem B325671 : Blo 323837 325671 := bstep (se 1 (by rfl) ⟨244253, by rfl⟩ : syracuseStep 325671 = 488507) B488507
theorem B325711 : Blo 323837 325711 := bstep (se 1 (by rfl) ⟨244283, by rfl⟩ : syracuseStep 325711 = 488567) B488567
theorem B489551 : Blo 323837 489551 := bstep (se 1 (by rfl) ⟨367163, by rfl⟩ : syracuseStep 489551 = 734327) B734327
theorem B325727 : Blo 323837 325727 := bstep (se 1 (by rfl) ⟨244295, by rfl⟩ : syracuseStep 325727 = 488591) B488591
theorem B325755 : Blo 323837 325755 := bstep (se 1 (by rfl) ⟨244316, by rfl⟩ : syracuseStep 325755 = 488633) B488633
theorem B325807 : Blo 323837 325807 := bstep (se 1 (by rfl) ⟨244355, by rfl⟩ : syracuseStep 325807 = 488711) B488711
theorem B325831 : Blo 323837 325831 := bstep (se 1 (by rfl) ⟨244373, by rfl⟩ : syracuseStep 325831 = 488747) B488747
theorem B489671 : Blo 323837 489671 := bstep (se 1 (by rfl) ⟨367253, by rfl⟩ : syracuseStep 489671 = 734507) B734507
theorem B325851 : Blo 323837 325851 := bstep (se 1 (by rfl) ⟨244388, by rfl⟩ : syracuseStep 325851 = 488777) B488777
theorem B325927 : Blo 323837 325927 := bstep (se 1 (by rfl) ⟨244445, by rfl⟩ : syracuseStep 325927 = 488891) B488891
theorem B325967 : Blo 323837 325967 := bstep (se 1 (by rfl) ⟨244475, by rfl⟩ : syracuseStep 325967 = 488951) B488951
theorem B325983 : Blo 323837 325983 := bstep (se 1 (by rfl) ⟨244487, by rfl⟩ : syracuseStep 325983 = 488975) B488975
theorem B489833 : Blo 323837 489833 := bstep (se 2 (by rfl) ⟨183687, by rfl⟩ : syracuseStep 489833 = 367375) B367375
theorem B326011 : Blo 323837 326011 := bstep (se 1 (by rfl) ⟨244508, by rfl⟩ : syracuseStep 326011 = 489017) B489017
theorem B326063 : Blo 323837 326063 := bstep (se 1 (by rfl) ⟨244547, by rfl⟩ : syracuseStep 326063 = 489095) B489095
theorem B489911 : Blo 323837 489911 := bstep (se 1 (by rfl) ⟨367433, by rfl⟩ : syracuseStep 489911 = 734867) B734867
theorem B326087 : Blo 323837 326087 := bstep (se 1 (by rfl) ⟨244565, by rfl⟩ : syracuseStep 326087 = 489131) B489131
theorem B326107 : Blo 323837 326107 := bstep (se 1 (by rfl) ⟨244580, by rfl⟩ : syracuseStep 326107 = 489161) B489161
theorem B489947 : Blo 323837 489947 := bstep (se 1 (by rfl) ⟨367460, by rfl⟩ : syracuseStep 489947 = 734921) B734921
theorem B2095625 : Blo 323837 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B326183 : Blo 323837 326183 := bstep (se 1 (by rfl) ⟨244637, by rfl⟩ : syracuseStep 326183 = 489275) B489275
theorem B3963437 : Blo 323837 3963437 := bstep (se 3 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 3963437 = 1486289) B1486289
theorem B326223 : Blo 323837 326223 := bstep (se 1 (by rfl) ⟨244667, by rfl⟩ : syracuseStep 326223 = 489335) B489335
theorem B326239 : Blo 323837 326239 := bstep (se 1 (by rfl) ⟨244679, by rfl⟩ : syracuseStep 326239 = 489359) B489359
theorem B326267 : Blo 323837 326267 := bstep (se 1 (by rfl) ⟨244700, by rfl⟩ : syracuseStep 326267 = 489401) B489401
theorem B1243795 : Blo 323837 1243795 := bstep (se 1 (by rfl) ⟨932846, by rfl⟩ : syracuseStep 1243795 = 1865693) B1865693
theorem B326319 : Blo 323837 326319 := bstep (se 1 (by rfl) ⟨244739, by rfl⟩ : syracuseStep 326319 = 489479) B489479
theorem B326343 : Blo 323837 326343 := bstep (se 1 (by rfl) ⟨244757, by rfl⟩ : syracuseStep 326343 = 489515) B489515
theorem B326363 : Blo 323837 326363 := bstep (se 1 (by rfl) ⟨244772, by rfl⟩ : syracuseStep 326363 = 489545) B489545
theorem B1047289 : Blo 323837 1047289 := bstep (se 2 (by rfl) ⟨392733, by rfl⟩ : syracuseStep 1047289 = 785467) B785467
theorem B326439 : Blo 323837 326439 := bstep (se 1 (by rfl) ⟨244829, by rfl⟩ : syracuseStep 326439 = 489659) B489659
theorem B588617 : Blo 323837 588617 := bstep (se 2 (by rfl) ⟨220731, by rfl⟩ : syracuseStep 588617 = 441463) B441463
theorem B326479 : Blo 323837 326479 := bstep (se 1 (by rfl) ⟨244859, by rfl⟩ : syracuseStep 326479 = 489719) B489719
theorem B326495 : Blo 323837 326495 := bstep (se 1 (by rfl) ⟨244871, by rfl⟩ : syracuseStep 326495 = 489743) B489743
theorem B326523 : Blo 323837 326523 := bstep (se 1 (by rfl) ⟨244892, by rfl⟩ : syracuseStep 326523 = 489785) B489785
theorem B326575 : Blo 323837 326575 := bstep (se 1 (by rfl) ⟨244931, by rfl⟩ : syracuseStep 326575 = 489863) B489863
theorem B490415 : Blo 323837 490415 := bstep (se 1 (by rfl) ⟨367811, by rfl⟩ : syracuseStep 490415 = 735623) B735623
theorem B1276847 : Blo 323837 1276847 := bstep (se 1 (by rfl) ⟨957635, by rfl⟩ : syracuseStep 1276847 = 1915271) B1915271
theorem B326599 : Blo 323837 326599 := bstep (se 1 (by rfl) ⟨244949, by rfl⟩ : syracuseStep 326599 = 489899) B489899
theorem B326619 : Blo 323837 326619 := bstep (se 1 (by rfl) ⟨244964, by rfl⟩ : syracuseStep 326619 = 489929) B489929
theorem B490505 : Blo 323837 490505 := bstep (se 2 (by rfl) ⟨183939, by rfl⟩ : syracuseStep 490505 = 367879) B367879
theorem B621587 : Blo 323837 621587 := bstep (se 1 (by rfl) ⟨466190, by rfl⟩ : syracuseStep 621587 = 932381) B932381
theorem B326695 : Blo 323837 326695 := bstep (se 1 (by rfl) ⟨245021, by rfl⟩ : syracuseStep 326695 = 490043) B490043
theorem B490535 : Blo 323837 490535 := bstep (se 1 (by rfl) ⟨367901, by rfl⟩ : syracuseStep 490535 = 735803) B735803
theorem B523343 : Blo 323837 523343 := bstep (se 1 (by rfl) ⟨392507, by rfl⟩ : syracuseStep 523343 = 785015) B785015
theorem B326735 : Blo 323837 326735 := bstep (se 1 (by rfl) ⟨245051, by rfl⟩ : syracuseStep 326735 = 490103) B490103
theorem B326751 : Blo 323837 326751 := bstep (se 1 (by rfl) ⟨245063, by rfl⟩ : syracuseStep 326751 = 490127) B490127
theorem B326779 : Blo 323837 326779 := bstep (se 1 (by rfl) ⟨245084, by rfl⟩ : syracuseStep 326779 = 490169) B490169
theorem B490619 : Blo 323837 490619 := bstep (se 1 (by rfl) ⟨367964, by rfl⟩ : syracuseStep 490619 = 735929) B735929
theorem B326831 : Blo 323837 326831 := bstep (se 1 (by rfl) ⟨245123, by rfl⟩ : syracuseStep 326831 = 490247) B490247
theorem B326855 : Blo 323837 326855 := bstep (se 1 (by rfl) ⟨245141, by rfl⟩ : syracuseStep 326855 = 490283) B490283
theorem B326875 : Blo 323837 326875 := bstep (se 1 (by rfl) ⟨245156, by rfl⟩ : syracuseStep 326875 = 490313) B490313
theorem B490745 : Blo 323837 490745 := bstep (se 2 (by rfl) ⟨184029, by rfl⟩ : syracuseStep 490745 = 368059) B368059
theorem B326951 : Blo 323837 326951 := bstep (se 1 (by rfl) ⟨245213, by rfl⟩ : syracuseStep 326951 = 490427) B490427
theorem B326991 : Blo 323837 326991 := bstep (se 1 (by rfl) ⟨245243, by rfl⟩ : syracuseStep 326991 = 490487) B490487
theorem B327007 : Blo 323837 327007 := bstep (se 1 (by rfl) ⟨245255, by rfl⟩ : syracuseStep 327007 = 490511) B490511
theorem B490847 : Blo 323837 490847 := bstep (se 1 (by rfl) ⟨368135, by rfl⟩ : syracuseStep 490847 = 736271) B736271
theorem B490859 : Blo 323837 490859 := bstep (se 1 (by rfl) ⟨368144, by rfl⟩ : syracuseStep 490859 = 736289) B736289
theorem B327035 : Blo 323837 327035 := bstep (se 1 (by rfl) ⟨245276, by rfl⟩ : syracuseStep 327035 = 490553) B490553
theorem B2096549 : Blo 323837 2096549 := bstep (se 4 (by rfl) ⟨196551, by rfl⟩ : syracuseStep 2096549 = 393103) B393103
theorem B327087 : Blo 323837 327087 := bstep (se 1 (by rfl) ⟨245315, by rfl⟩ : syracuseStep 327087 = 490631) B490631
theorem B327111 : Blo 323837 327111 := bstep (se 1 (by rfl) ⟨245333, by rfl⟩ : syracuseStep 327111 = 490667) B490667
theorem B327131 : Blo 323837 327131 := bstep (se 1 (by rfl) ⟨245348, by rfl⟩ : syracuseStep 327131 = 490697) B490697
theorem B327207 : Blo 323837 327207 := bstep (se 1 (by rfl) ⟨245405, by rfl⟩ : syracuseStep 327207 = 490811) B490811
theorem B523855 : Blo 323837 523855 := bstep (se 1 (by rfl) ⟨392891, by rfl⟩ : syracuseStep 523855 = 785783) B785783
theorem B327247 : Blo 323837 327247 := bstep (se 1 (by rfl) ⟨245435, by rfl⟩ : syracuseStep 327247 = 490871) B490871
theorem B491087 : Blo 323837 491087 := bstep (se 1 (by rfl) ⟨368315, by rfl⟩ : syracuseStep 491087 = 736631) B736631
theorem B327263 : Blo 323837 327263 := bstep (se 1 (by rfl) ⟨245447, by rfl⟩ : syracuseStep 327263 = 490895) B490895
theorem B327291 : Blo 323837 327291 := bstep (se 1 (by rfl) ⟨245468, by rfl⟩ : syracuseStep 327291 = 490937) B490937
theorem B1048211 : Blo 323837 1048211 := bstep (se 1 (by rfl) ⟨786158, by rfl⟩ : syracuseStep 1048211 = 1572317) B1572317
theorem B327343 : Blo 323837 327343 := bstep (se 1 (by rfl) ⟨245507, by rfl⟩ : syracuseStep 327343 = 491015) B491015
theorem B589511 : Blo 323837 589511 := bstep (se 1 (by rfl) ⟨442133, by rfl⟩ : syracuseStep 589511 = 884267) B884267
theorem B327367 : Blo 323837 327367 := bstep (se 1 (by rfl) ⟨245525, by rfl⟩ : syracuseStep 327367 = 491051) B491051
theorem B491207 : Blo 323837 491207 := bstep (se 1 (by rfl) ⟨368405, by rfl⟩ : syracuseStep 491207 = 736811) B736811
theorem B327387 : Blo 323837 327387 := bstep (se 1 (by rfl) ⟨245540, by rfl⟩ : syracuseStep 327387 = 491081) B491081
theorem B327463 : Blo 323837 327463 := bstep (se 1 (by rfl) ⟨245597, by rfl⟩ : syracuseStep 327463 = 491195) B491195
theorem B2391851 : Blo 323837 2391851 := bstep (se 1 (by rfl) ⟨1793888, by rfl⟩ : syracuseStep 2391851 = 3587777) B3587777
theorem B327503 : Blo 323837 327503 := bstep (se 1 (by rfl) ⟨245627, by rfl⟩ : syracuseStep 327503 = 491255) B491255
theorem B327519 : Blo 323837 327519 := bstep (se 1 (by rfl) ⟨245639, by rfl⟩ : syracuseStep 327519 = 491279) B491279
theorem B491369 : Blo 323837 491369 := bstep (se 2 (by rfl) ⟨184263, by rfl⟩ : syracuseStep 491369 = 368527) B368527
theorem B327547 : Blo 323837 327547 := bstep (se 1 (by rfl) ⟨245660, by rfl⟩ : syracuseStep 327547 = 491321) B491321
theorem B327599 : Blo 323837 327599 := bstep (se 1 (by rfl) ⟨245699, by rfl⟩ : syracuseStep 327599 = 491399) B491399
theorem B491447 : Blo 323837 491447 := bstep (se 1 (by rfl) ⟨368585, by rfl⟩ : syracuseStep 491447 = 737171) B737171
theorem B327623 : Blo 323837 327623 := bstep (se 1 (by rfl) ⟨245717, by rfl⟩ : syracuseStep 327623 = 491435) B491435
theorem B327643 : Blo 323837 327643 := bstep (se 1 (by rfl) ⟨245732, by rfl⟩ : syracuseStep 327643 = 491465) B491465
theorem B491483 : Blo 323837 491483 := bstep (se 1 (by rfl) ⟨368612, by rfl⟩ : syracuseStep 491483 = 737225) B737225
theorem B885001 : Blo 323837 885001 := bstep (se 2 (by rfl) ⟨331875, by rfl⟩ : syracuseStep 885001 = 663751) B663751
theorem B754247 : Blo 323837 754247 := bstep (se 1 (by rfl) ⟨565685, by rfl⟩ : syracuseStep 754247 = 1131371) B1131371
theorem B819791 : Blo 323837 819791 := bstep (se 1 (by rfl) ⟨614843, by rfl⟩ : syracuseStep 819791 = 1229687) B1229687
theorem B524983 : Blo 323837 524983 := bstep (se 1 (by rfl) ⟨393737, by rfl⟩ : syracuseStep 524983 = 787475) B787475
theorem B3539659 : Blo 323837 3539659 := bstep (se 1 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 3539659 = 5309489) B5309489
theorem B787495 : Blo 323837 787495 := bstep (se 1 (by rfl) ⟨590621, by rfl⟩ : syracuseStep 787495 = 1181243) B1181243
theorem B820439 : Blo 323837 820439 := bstep (se 1 (by rfl) ⟨615329, by rfl⟩ : syracuseStep 820439 = 1230659) B1230659
theorem B3802405 : Blo 323837 3802405 := bstep (se 4 (by rfl) ⟨356475, by rfl⟩ : syracuseStep 3802405 = 712951) B712951
theorem B55248277 : Blo 323837 55248277 := bstep (se 6 (by rfl) ⟨1294881, by rfl⟩ : syracuseStep 55248277 = 2589763) B2589763
theorem B1574333 : Blo 323837 1574333 := bstep (se 3 (by rfl) ⟨295187, by rfl⟩ : syracuseStep 1574333 = 590375) B590375
theorem B820793 : Blo 323837 820793 := bstep (se 2 (by rfl) ⟨307797, by rfl⟩ : syracuseStep 820793 = 615595) B615595
theorem B5932601 : Blo 323837 5932601 := bstep (se 2 (by rfl) ⟨2224725, by rfl⟩ : syracuseStep 5932601 = 4449451) B4449451
theorem B2230199 : Blo 323837 2230199 := bstep (se 1 (by rfl) ⟨1672649, by rfl⟩ : syracuseStep 2230199 = 3345299) B3345299
theorem B1116413 : Blo 323837 1116413 := bstep (se 3 (by rfl) ⟨209327, by rfl⟩ : syracuseStep 1116413 = 418655) B418655
theorem B624905 : Blo 323837 624905 := bstep (se 2 (by rfl) ⟨234339, by rfl⟩ : syracuseStep 624905 = 468679) B468679
theorem B2689523 : Blo 323837 2689523 := bstep (se 1 (by rfl) ⟨2017142, by rfl⟩ : syracuseStep 2689523 = 4034285) B4034285
theorem B2100239 : Blo 323837 2100239 := bstep (se 1 (by rfl) ⟨1575179, by rfl⟩ : syracuseStep 2100239 = 3150359) B3150359
theorem B9440459 : Blo 323837 9440459 := bstep (se 1 (by rfl) ⟨7080344, by rfl⟩ : syracuseStep 9440459 = 14160689) B14160689
theorem B1478225 : Blo 323837 1478225 := bstep (se 2 (by rfl) ⟨554334, by rfl⟩ : syracuseStep 1478225 = 1108669) B1108669
theorem B1642193 : Blo 323837 1642193 := bstep (se 2 (by rfl) ⟨615822, by rfl⟩ : syracuseStep 1642193 = 1231645) B1231645
theorem B823081 : Blo 323837 823081 := bstep (se 2 (by rfl) ⟨308655, by rfl⟩ : syracuseStep 823081 = 617311) B617311
theorem B364495 : Blo 323837 364495 := bstep (se 1 (by rfl) ⟨273371, by rfl⟩ : syracuseStep 364495 = 546743) B546743
theorem B364891 : Blo 323837 364891 := bstep (se 1 (by rfl) ⟨273668, by rfl⟩ : syracuseStep 364891 = 547337) B547337
theorem B364999 : Blo 323837 364999 := bstep (se 1 (by rfl) ⟨273749, by rfl⟩ : syracuseStep 364999 = 547499) B547499
theorem B823871 : Blo 323837 823871 := bstep (se 1 (by rfl) ⟨617903, by rfl⟩ : syracuseStep 823871 = 1235807) B1235807
theorem B365359 : Blo 323837 365359 := bstep (se 1 (by rfl) ⟨274019, by rfl⟩ : syracuseStep 365359 = 548039) B548039
theorem B365467 : Blo 323837 365467 := bstep (se 1 (by rfl) ⟨274100, by rfl⟩ : syracuseStep 365467 = 548201) B548201
theorem B693211 : Blo 323837 693211 := bstep (se 1 (by rfl) ⟨519908, by rfl⟩ : syracuseStep 693211 = 1039817) B1039817
theorem B3871901 : Blo 323837 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B922823 : Blo 323837 922823 := bstep (se 1 (by rfl) ⟨692117, by rfl⟩ : syracuseStep 922823 = 1384235) B1384235
theorem B824519 : Blo 323837 824519 := bstep (se 1 (by rfl) ⟨618389, by rfl⟩ : syracuseStep 824519 = 1236779) B1236779
theorem B824539 : Blo 323837 824539 := bstep (se 1 (by rfl) ⟨618404, by rfl⟩ : syracuseStep 824539 = 1236809) B1236809
theorem B365863 : Blo 323837 365863 := bstep (se 1 (by rfl) ⟨274397, by rfl⟩ : syracuseStep 365863 = 548795) B548795
theorem B365935 : Blo 323837 365935 := bstep (se 1 (by rfl) ⟨274451, by rfl⟩ : syracuseStep 365935 = 548903) B548903
theorem B628105 : Blo 323837 628105 := bstep (se 2 (by rfl) ⟨235539, by rfl⟩ : syracuseStep 628105 = 471079) B471079
theorem B366151 : Blo 323837 366151 := bstep (se 1 (by rfl) ⟨274613, by rfl⟩ : syracuseStep 366151 = 549227) B549227
theorem B1644623 : Blo 323837 1644623 := bstep (se 1 (by rfl) ⟨1233467, by rfl⟩ : syracuseStep 1644623 = 2466935) B2466935
theorem B1185977 : Blo 323837 1185977 := bstep (se 2 (by rfl) ⟨444741, by rfl⟩ : syracuseStep 1185977 = 889483) B889483
theorem B2791705 : Blo 323837 2791705 := bstep (se 2 (by rfl) ⟨1046889, by rfl⟩ : syracuseStep 2791705 = 2093779) B2093779
theorem B825673 : Blo 323837 825673 := bstep (se 2 (by rfl) ⟨309627, by rfl⟩ : syracuseStep 825673 = 619255) B619255
theorem B367015 : Blo 323837 367015 := bstep (se 1 (by rfl) ⟨275261, by rfl⟩ : syracuseStep 367015 = 550523) B550523
theorem B825977 : Blo 323837 825977 := bstep (se 2 (by rfl) ⟨309741, by rfl⟩ : syracuseStep 825977 = 619483) B619483
theorem B367591 : Blo 323837 367591 := bstep (se 1 (by rfl) ⟨275693, by rfl⟩ : syracuseStep 367591 = 551387) B551387
theorem B1645757 : Blo 323837 1645757 := bstep (se 3 (by rfl) ⟨308579, by rfl⟩ : syracuseStep 1645757 = 617159) B617159
theorem B2956517 : Blo 323837 2956517 := bstep (se 4 (by rfl) ⟨277173, by rfl⟩ : syracuseStep 2956517 = 554347) B554347
theorem B1383961 : Blo 323837 1383961 := bstep (se 2 (by rfl) ⟨518985, by rfl⟩ : syracuseStep 1383961 = 1037971) B1037971
theorem B2793041 : Blo 323837 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B990955 : Blo 323837 990955 := bstep (se 1 (by rfl) ⟨743216, by rfl⟩ : syracuseStep 990955 = 1486433) B1486433
theorem B1810183 : Blo 323837 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B728873 : Blo 323837 728873 := bstep (se 2 (by rfl) ⟨273327, by rfl⟩ : syracuseStep 728873 = 546655) B546655
theorem B827759 : Blo 323837 827759 := bstep (se 1 (by rfl) ⟨620819, by rfl⟩ : syracuseStep 827759 = 1241639) B1241639
theorem B2368001 : Blo 323837 2368001 := bstep (se 2 (by rfl) ⟨888000, by rfl⟩ : syracuseStep 2368001 = 1776001) B1776001
theorem B2466449 : Blo 323837 2466449 := bstep (se 2 (by rfl) ⟨924918, by rfl⟩ : syracuseStep 2466449 = 1849837) B1849837
theorem B1876651 : Blo 323837 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B729935 : Blo 323837 729935 := bstep (se 1 (by rfl) ⟨547451, by rfl⟩ : syracuseStep 729935 = 1094903) B1094903
theorem B697243 : Blo 323837 697243 := bstep (se 1 (by rfl) ⟨522932, by rfl⟩ : syracuseStep 697243 = 1045865) B1045865
theorem B828407 : Blo 323837 828407 := bstep (se 1 (by rfl) ⟨621305, by rfl⟩ : syracuseStep 828407 = 1242611) B1242611
theorem B730151 : Blo 323837 730151 := bstep (se 1 (by rfl) ⟨547613, by rfl⟩ : syracuseStep 730151 = 1095227) B1095227
theorem B828539 : Blo 323837 828539 := bstep (se 1 (by rfl) ⟨621404, by rfl⟩ : syracuseStep 828539 = 1242809) B1242809
theorem B730331 : Blo 323837 730331 := bstep (se 1 (by rfl) ⟨547748, by rfl⟩ : syracuseStep 730331 = 1095497) B1095497
theorem B730529 : Blo 323837 730529 := bstep (se 2 (by rfl) ⟨273948, by rfl⟩ : syracuseStep 730529 = 547897) B547897
theorem B1582649 : Blo 323837 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B731087 : Blo 323837 731087 := bstep (se 1 (by rfl) ⟨548315, by rfl⟩ : syracuseStep 731087 = 1096631) B1096631
theorem B1648673 : Blo 323837 1648673 := bstep (se 2 (by rfl) ⟨618252, by rfl⟩ : syracuseStep 1648673 = 1236505) B1236505
theorem B698473 : Blo 323837 698473 := bstep (se 2 (by rfl) ⟨261927, by rfl⟩ : syracuseStep 698473 = 523855) B523855
theorem B1648835 : Blo 323837 1648835 := bstep (se 1 (by rfl) ⟨1236626, by rfl⟩ : syracuseStep 1648835 = 2473253) B2473253
theorem B1681661 : Blo 323837 1681661 := bstep (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) B630623
theorem B731465 : Blo 323837 731465 := bstep (se 2 (by rfl) ⟨274299, by rfl⟩ : syracuseStep 731465 = 548599) B548599
theorem B731483 : Blo 323837 731483 := bstep (se 1 (by rfl) ⟨548612, by rfl⟩ : syracuseStep 731483 = 1097225) B1097225
theorem B15935849 : Blo 323837 15935849 := bstep (se 2 (by rfl) ⟨5975943, by rfl⟩ : syracuseStep 15935849 = 11951887) B11951887
theorem B698807 : Blo 323837 698807 := bstep (se 1 (by rfl) ⟨524105, by rfl⟩ : syracuseStep 698807 = 1048211) B1048211
theorem B1387003 : Blo 323837 1387003 := bstep (se 1 (by rfl) ⟨1040252, by rfl⟩ : syracuseStep 1387003 = 2080505) B2080505
theorem B928655 : Blo 323837 928655 := bstep (se 1 (by rfl) ⟨696491, by rfl⟩ : syracuseStep 928655 = 1392983) B1392983
theorem B732059 : Blo 323837 732059 := bstep (se 1 (by rfl) ⟨549044, by rfl⟩ : syracuseStep 732059 = 1098089) B1098089
theorem B2468879 : Blo 323837 2468879 := bstep (se 1 (by rfl) ⟨1851659, by rfl⟩ : syracuseStep 2468879 = 3703319) B3703319
theorem B732257 : Blo 323837 732257 := bstep (se 2 (by rfl) ⟨274596, by rfl⟩ : syracuseStep 732257 = 549193) B549193
theorem B896243 : Blo 323837 896243 := bstep (se 1 (by rfl) ⟨672182, by rfl⟩ : syracuseStep 896243 = 1344365) B1344365
theorem B732455 : Blo 323837 732455 := bstep (se 1 (by rfl) ⟨549341, by rfl⟩ : syracuseStep 732455 = 1098683) B1098683
theorem B732833 : Blo 323837 732833 := bstep (se 2 (by rfl) ⟨274812, by rfl⟩ : syracuseStep 732833 = 549625) B549625
theorem B1388335 : Blo 323837 1388335 := bstep (se 1 (by rfl) ⟨1041251, by rfl⟩ : syracuseStep 1388335 = 2082503) B2082503
theorem B733193 : Blo 323837 733193 := bstep (se 2 (by rfl) ⟨274947, by rfl⟩ : syracuseStep 733193 = 549895) B549895
theorem B733607 : Blo 323837 733607 := bstep (se 1 (by rfl) ⟨550205, by rfl⟩ : syracuseStep 733607 = 1100411) B1100411
theorem B733715 : Blo 323837 733715 := bstep (se 1 (by rfl) ⟨550286, by rfl⟩ : syracuseStep 733715 = 1100573) B1100573
theorem B1782323 : Blo 323837 1782323 := bstep (se 1 (by rfl) ⟨1336742, by rfl⟩ : syracuseStep 1782323 = 2673485) B2673485
theorem B733769 : Blo 323837 733769 := bstep (se 2 (by rfl) ⟨275163, by rfl⟩ : syracuseStep 733769 = 550327) B550327
theorem B734183 : Blo 323837 734183 := bstep (se 1 (by rfl) ⟨550637, by rfl⟩ : syracuseStep 734183 = 1101275) B1101275
theorem B1815527 : Blo 323837 1815527 := bstep (se 1 (by rfl) ⟨1361645, by rfl⟩ : syracuseStep 1815527 = 2723291) B2723291
theorem B996551 : Blo 323837 996551 := bstep (se 1 (by rfl) ⟨747413, by rfl⟩ : syracuseStep 996551 = 1494827) B1494827
theorem B3716441 : Blo 323837 3716441 := bstep (se 2 (by rfl) ⟨1393665, by rfl⟩ : syracuseStep 3716441 = 2787331) B2787331
theorem B734561 : Blo 323837 734561 := bstep (se 2 (by rfl) ⟨275460, by rfl⟩ : syracuseStep 734561 = 550921) B550921
theorem B2962793 : Blo 323837 2962793 := bstep (se 2 (by rfl) ⟨1111047, by rfl⟩ : syracuseStep 2962793 = 2222095) B2222095
theorem B734651 : Blo 323837 734651 := bstep (se 1 (by rfl) ⟨550988, by rfl⟩ : syracuseStep 734651 = 1101977) B1101977
theorem B734777 : Blo 323837 734777 := bstep (se 2 (by rfl) ⟨275541, by rfl⟩ : syracuseStep 734777 = 551083) B551083
theorem B1652561 : Blo 323837 1652561 := bstep (se 2 (by rfl) ⟨619710, by rfl⟩ : syracuseStep 1652561 = 1239421) B1239421
theorem B767873 : Blo 323837 767873 := bstep (se 2 (by rfl) ⟨287952, by rfl⟩ : syracuseStep 767873 = 575905) B575905
theorem B1095713 : Blo 323837 1095713 := bstep (se 2 (by rfl) ⟨410892, by rfl⟩ : syracuseStep 1095713 = 821785) B821785
theorem B735443 : Blo 323837 735443 := bstep (se 1 (by rfl) ⟨551582, by rfl⟩ : syracuseStep 735443 = 1103165) B1103165
theorem B735497 : Blo 323837 735497 := bstep (se 2 (by rfl) ⟨275811, by rfl⟩ : syracuseStep 735497 = 551623) B551623
theorem B2472281 : Blo 323837 2472281 := bstep (se 2 (by rfl) ⟨927105, by rfl⟩ : syracuseStep 2472281 = 1854211) B1854211
theorem B670177 : Blo 323837 670177 := bstep (se 2 (by rfl) ⟨251316, by rfl⟩ : syracuseStep 670177 = 502633) B502633
theorem B735713 : Blo 323837 735713 := bstep (se 2 (by rfl) ⟨275892, by rfl⟩ : syracuseStep 735713 = 551785) B551785
theorem B1653371 : Blo 323837 1653371 := bstep (se 1 (by rfl) ⟨1240028, by rfl⟩ : syracuseStep 1653371 = 2480057) B2480057
theorem B24394391 : Blo 323837 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B2079427 : Blo 323837 2079427 := bstep (se 1 (by rfl) ⟨1559570, by rfl⟩ : syracuseStep 2079427 = 3119141) B3119141
theorem B736019 : Blo 323837 736019 := bstep (se 1 (by rfl) ⟨552014, by rfl⟩ : syracuseStep 736019 = 1104029) B1104029
theorem B736379 : Blo 323837 736379 := bstep (se 1 (by rfl) ⟨552284, by rfl⟩ : syracuseStep 736379 = 1104569) B1104569
theorem B736505 : Blo 323837 736505 := bstep (se 2 (by rfl) ⟨276189, by rfl⟩ : syracuseStep 736505 = 552379) B552379
theorem B1686815 : Blo 323837 1686815 := bstep (se 1 (by rfl) ⟨1265111, by rfl⟩ : syracuseStep 1686815 = 2530223) B2530223
theorem B2768195 : Blo 323837 2768195 := bstep (se 1 (by rfl) ⟨2076146, by rfl⟩ : syracuseStep 2768195 = 4152293) B4152293
theorem B736649 : Blo 323837 736649 := bstep (se 2 (by rfl) ⟨276243, by rfl⟩ : syracuseStep 736649 = 552487) B552487
theorem B933257 : Blo 323837 933257 := bstep (se 2 (by rfl) ⟨349971, by rfl⟩ : syracuseStep 933257 = 699943) B699943
theorem B736775 : Blo 323837 736775 := bstep (se 1 (by rfl) ⟨552581, by rfl⟩ : syracuseStep 736775 = 1105163) B1105163
theorem B8371835 : Blo 323837 8371835 := bstep (se 1 (by rfl) ⟨6278876, by rfl⟩ : syracuseStep 8371835 = 12557753) B12557753
theorem B736955 : Blo 323837 736955 := bstep (se 1 (by rfl) ⟨552716, by rfl⟩ : syracuseStep 736955 = 1105433) B1105433
theorem B1752787 : Blo 323837 1752787 := bstep (se 1 (by rfl) ⟨1314590, by rfl⟩ : syracuseStep 1752787 = 2629181) B2629181
theorem B737081 : Blo 323837 737081 := bstep (se 2 (by rfl) ⟨276405, by rfl⟩ : syracuseStep 737081 = 552811) B552811
theorem B1752961 : Blo 323837 1752961 := bstep (se 2 (by rfl) ⟨657360, by rfl⟩ : syracuseStep 1752961 = 1314721) B1314721
theorem B1655315 : Blo 323837 1655315 := bstep (se 1 (by rfl) ⟨1241486, by rfl⟩ : syracuseStep 1655315 = 2482973) B2482973
theorem B13681325 : Blo 323837 13681325 := bstep (se 3 (by rfl) ⟨2565248, by rfl⟩ : syracuseStep 13681325 = 5130497) B5130497
theorem B2474711 : Blo 323837 2474711 := bstep (se 1 (by rfl) ⟨1856033, by rfl⟩ : syracuseStep 2474711 = 3712067) B3712067
theorem B410447 : Blo 323837 410447 := bstep (se 1 (by rfl) ⟨307835, by rfl⟩ : syracuseStep 410447 = 615671) B615671
theorem B1098575 : Blo 323837 1098575 := bstep (se 1 (by rfl) ⟨823931, by rfl⟩ : syracuseStep 1098575 = 1647863) B1647863
theorem B410599 : Blo 323837 410599 := bstep (se 1 (by rfl) ⟨307949, by rfl⟩ : syracuseStep 410599 = 615899) B615899
theorem B1098899 : Blo 323837 1098899 := bstep (se 1 (by rfl) ⟨824174, by rfl⟩ : syracuseStep 1098899 = 1648349) B1648349
theorem B1099169 : Blo 323837 1099169 := bstep (se 2 (by rfl) ⟨412188, by rfl⟩ : syracuseStep 1099169 = 824377) B824377
theorem B1230673 : Blo 323837 1230673 := bstep (se 2 (by rfl) ⟨461502, by rfl⟩ : syracuseStep 1230673 = 923005) B923005
theorem B2770793 : Blo 323837 2770793 := bstep (se 2 (by rfl) ⟨1039047, by rfl⟩ : syracuseStep 2770793 = 2078095) B2078095
theorem B5949521 : Blo 323837 5949521 := bstep (se 2 (by rfl) ⟨2231070, by rfl⟩ : syracuseStep 5949521 = 4462141) B4462141
theorem B1230977 : Blo 323837 1230977 := bstep (se 2 (by rfl) ⟨461616, by rfl⟩ : syracuseStep 1230977 = 923233) B923233
theorem B1657097 : Blo 323837 1657097 := bstep (se 2 (by rfl) ⟨621411, by rfl⟩ : syracuseStep 1657097 = 1242823) B1242823
theorem B1231433 : Blo 323837 1231433 := bstep (se 2 (by rfl) ⟨461787, by rfl⟩ : syracuseStep 1231433 = 923575) B923575
theorem B1395751 : Blo 323837 1395751 := bstep (se 1 (by rfl) ⟨1046813, by rfl⟩ : syracuseStep 1395751 = 2093627) B2093627
theorem B5262515 : Blo 323837 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B1985755 : Blo 323837 1985755 := bstep (se 1 (by rfl) ⟨1489316, by rfl⟩ : syracuseStep 1985755 = 2978633) B2978633
theorem B413039 : Blo 323837 413039 := bstep (se 1 (by rfl) ⟨309779, by rfl⟩ : syracuseStep 413039 = 619559) B619559
theorem B1658231 : Blo 323837 1658231 := bstep (se 1 (by rfl) ⟨1243673, by rfl⟩ : syracuseStep 1658231 = 2487347) B2487347
theorem B413095 : Blo 323837 413095 := bstep (se 1 (by rfl) ⟨309821, by rfl⟩ : syracuseStep 413095 = 619643) B619643
theorem B1658393 : Blo 323837 1658393 := bstep (se 2 (by rfl) ⟨621897, by rfl⟩ : syracuseStep 1658393 = 1243795) B1243795
theorem B1494611 : Blo 323837 1494611 := bstep (se 1 (by rfl) ⟨1120958, by rfl⟩ : syracuseStep 1494611 = 2241917) B2241917
theorem B9981589 : Blo 323837 9981589 := bstep (se 6 (by rfl) ⟨233943, by rfl⟩ : syracuseStep 9981589 = 467887) B467887
theorem B1396385 : Blo 323837 1396385 := bstep (se 2 (by rfl) ⟨523644, by rfl⟩ : syracuseStep 1396385 = 1047289) B1047289
theorem B413419 : Blo 323837 413419 := bstep (se 1 (by rfl) ⟨310064, by rfl⟩ : syracuseStep 413419 = 620129) B620129
theorem B1560323 : Blo 323837 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B1232921 : Blo 323837 1232921 := bstep (se 2 (by rfl) ⟨462345, by rfl⟩ : syracuseStep 1232921 = 924691) B924691
theorem B1397083 : Blo 323837 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B2642291 : Blo 323837 2642291 := bstep (se 1 (by rfl) ⟨1981718, by rfl⟩ : syracuseStep 2642291 = 3963437) B3963437
theorem B1233377 : Blo 323837 1233377 := bstep (se 2 (by rfl) ⟨462516, by rfl⟩ : syracuseStep 1233377 = 925033) B925033
theorem B1102355 : Blo 323837 1102355 := bstep (se 1 (by rfl) ⟨826766, by rfl⟩ : syracuseStep 1102355 = 1653533) B1653533
theorem B414391 : Blo 323837 414391 := bstep (se 1 (by rfl) ⟨310793, by rfl⟩ : syracuseStep 414391 = 621587) B621587
theorem B348895 : Blo 323837 348895 := bstep (se 1 (by rfl) ⟨261671, by rfl⟩ : syracuseStep 348895 = 523343) B523343
theorem B1397699 : Blo 323837 1397699 := bstep (se 1 (by rfl) ⟨1048274, by rfl⟩ : syracuseStep 1397699 = 2096549) B2096549
theorem B4674509 : Blo 323837 4674509 := bstep (se 3 (by rfl) ⟨876470, by rfl⟩ : syracuseStep 4674509 = 1752941) B1752941
theorem B939133 : Blo 323837 939133 := bstep (se 3 (by rfl) ⟨176087, by rfl⟩ : syracuseStep 939133 = 352175) B352175
theorem B1594567 : Blo 323837 1594567 := bstep (se 1 (by rfl) ⟨1195925, by rfl⟩ : syracuseStep 1594567 = 2391851) B2391851
theorem B6248123 : Blo 323837 6248123 := bstep (se 1 (by rfl) ⟨4686092, by rfl⟩ : syracuseStep 6248123 = 9372185) B9372185
theorem B546601 : Blo 323837 546601 := bstep (se 2 (by rfl) ⟨204975, by rfl⟩ : syracuseStep 546601 = 409951) B409951
theorem B2086991 : Blo 323837 2086991 := bstep (se 1 (by rfl) ⟨1565243, by rfl⟩ : syracuseStep 2086991 = 3130487) B3130487
theorem B1104137 : Blo 323837 1104137 := bstep (se 2 (by rfl) ⟨414051, by rfl⟩ : syracuseStep 1104137 = 828103) B828103
theorem B547391 : Blo 323837 547391 := bstep (se 1 (by rfl) ⟨410543, by rfl⟩ : syracuseStep 547391 = 821087) B821087
theorem B1235519 : Blo 323837 1235519 := bstep (se 1 (by rfl) ⟨926639, by rfl⟩ : syracuseStep 1235519 = 1853279) B1853279
theorem B7527107 : Blo 323837 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B1071863 : Blo 323837 1071863 := bstep (se 1 (by rfl) ⟨803897, by rfl⟩ : syracuseStep 1071863 = 1607795) B1607795
theorem B1235837 : Blo 323837 1235837 := bstep (se 3 (by rfl) ⟨231719, by rfl⟩ : syracuseStep 1235837 = 463439) B463439
theorem B548059 : Blo 323837 548059 := bstep (se 1 (by rfl) ⟨411044, by rfl⟩ : syracuseStep 548059 = 822089) B822089
theorem B1400075 : Blo 323837 1400075 := bstep (se 1 (by rfl) ⟨1050056, by rfl⟩ : syracuseStep 1400075 = 2100113) B2100113
theorem B1170719 : Blo 323837 1170719 := bstep (se 1 (by rfl) ⟨878039, by rfl⟩ : syracuseStep 1170719 = 1756079) B1756079
theorem B1400125 : Blo 323837 1400125 := bstep (se 3 (by rfl) ⟨262523, by rfl⟩ : syracuseStep 1400125 = 525047) B525047
theorem B1105271 : Blo 323837 1105271 := bstep (se 1 (by rfl) ⟨828953, by rfl⟩ : syracuseStep 1105271 = 1657907) B1657907
theorem B1171207 : Blo 323837 1171207 := bstep (se 1 (by rfl) ⟨878405, by rfl⟩ : syracuseStep 1171207 = 1756811) B1756811
theorem B548815 : Blo 323837 548815 := bstep (se 1 (by rfl) ⟨411611, by rfl⟩ : syracuseStep 548815 = 823223) B823223
theorem B14049287 : Blo 323837 14049287 := bstep (se 1 (by rfl) ⟨10536965, by rfl⟩ : syracuseStep 14049287 = 21073931) B21073931
theorem B1695953 : Blo 323837 1695953 := bstep (se 2 (by rfl) ⟨635982, by rfl⟩ : syracuseStep 1695953 = 1271965) B1271965
theorem B1106351 : Blo 323837 1106351 := bstep (se 1 (by rfl) ⟨829763, by rfl⟩ : syracuseStep 1106351 = 1659527) B1659527
theorem B614881 : Blo 323837 614881 := bstep (se 2 (by rfl) ⟨230580, by rfl⟩ : syracuseStep 614881 = 461161) B461161
theorem B778825 : Blo 323837 778825 := bstep (se 2 (by rfl) ⟨292059, by rfl⟩ : syracuseStep 778825 = 584119) B584119
theorem B549497 : Blo 323837 549497 := bstep (se 2 (by rfl) ⟨206061, by rfl⟩ : syracuseStep 549497 = 412123) B412123
theorem B549551 : Blo 323837 549551 := bstep (se 1 (by rfl) ⟨412163, by rfl⟩ : syracuseStep 549551 = 824327) B824327
theorem B549787 : Blo 323837 549787 := bstep (se 1 (by rfl) ⟨412340, by rfl⟩ : syracuseStep 549787 = 824681) B824681
theorem B13297097 : Blo 323837 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B4417361 : Blo 323837 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B1239407 : Blo 323837 1239407 := bstep (se 1 (by rfl) ⟨929555, by rfl⟩ : syracuseStep 1239407 = 1859111) B1859111
theorem B551279 : Blo 323837 551279 := bstep (se 1 (by rfl) ⟨413459, by rfl⟩ : syracuseStep 551279 = 826919) B826919
theorem B616871 : Blo 323837 616871 := bstep (se 1 (by rfl) ⟨462653, by rfl⟩ : syracuseStep 616871 = 925307) B925307
theorem B12479021 : Blo 323837 12479021 := bstep (se 3 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 12479021 = 4679633) B4679633
theorem B485951 : Blo 323837 485951 := bstep (se 1 (by rfl) ⟨364463, by rfl⟩ : syracuseStep 485951 = 728927) B728927
theorem B551495 : Blo 323837 551495 := bstep (se 1 (by rfl) ⟨413621, by rfl⟩ : syracuseStep 551495 = 827243) B827243
theorem B518729 : Blo 323837 518729 := bstep (se 2 (by rfl) ⟨194523, by rfl⟩ : syracuseStep 518729 = 389047) B389047
theorem B486071 : Blo 323837 486071 := bstep (se 1 (by rfl) ⟨364553, by rfl⟩ : syracuseStep 486071 = 729107) B729107
theorem B4188995 : Blo 323837 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B1665917 : Blo 323837 1665917 := bstep (se 3 (by rfl) ⟨312359, by rfl⟩ : syracuseStep 1665917 = 624719) B624719
theorem B486299 : Blo 323837 486299 := bstep (se 1 (by rfl) ⟨364724, by rfl⟩ : syracuseStep 486299 = 729449) B729449
theorem B551927 : Blo 323837 551927 := bstep (se 1 (by rfl) ⟨413945, by rfl⟩ : syracuseStep 551927 = 827891) B827891
theorem B617615 : Blo 323837 617615 := bstep (se 1 (by rfl) ⟨463211, by rfl⟩ : syracuseStep 617615 = 926423) B926423
theorem B1568011 : Blo 323837 1568011 := bstep (se 1 (by rfl) ⟨1176008, by rfl⟩ : syracuseStep 1568011 = 2352017) B2352017
theorem B486695 : Blo 323837 486695 := bstep (se 1 (by rfl) ⟨365021, by rfl⟩ : syracuseStep 486695 = 730043) B730043
theorem B486779 : Blo 323837 486779 := bstep (se 1 (by rfl) ⟨365084, by rfl⟩ : syracuseStep 486779 = 730169) B730169
theorem B486905 : Blo 323837 486905 := bstep (se 2 (by rfl) ⟨182589, by rfl⟩ : syracuseStep 486905 = 365179) B365179
theorem B487007 : Blo 323837 487007 := bstep (se 1 (by rfl) ⟨365255, by rfl⟩ : syracuseStep 487007 = 730511) B730511
theorem B6254273 : Blo 323837 6254273 := bstep (se 2 (by rfl) ⟨2345352, by rfl⟩ : syracuseStep 6254273 = 4690705) B4690705
theorem B552683 : Blo 323837 552683 := bstep (se 1 (by rfl) ⟨414512, by rfl⟩ : syracuseStep 552683 = 829025) B829025
theorem B1240879 : Blo 323837 1240879 := bstep (se 1 (by rfl) ⟨930659, by rfl⟩ : syracuseStep 1240879 = 1861319) B1861319
theorem B487223 : Blo 323837 487223 := bstep (se 1 (by rfl) ⟨365417, by rfl⟩ : syracuseStep 487223 = 730835) B730835
theorem B1044353 : Blo 323837 1044353 := bstep (se 2 (by rfl) ⟨391632, by rfl⟩ : syracuseStep 1044353 = 783265) B783265
theorem B487529 : Blo 323837 487529 := bstep (se 2 (by rfl) ⟨182823, by rfl⟩ : syracuseStep 487529 = 365647) B365647
theorem B3567887 : Blo 323837 3567887 := bstep (se 1 (by rfl) ⟨2675915, by rfl⟩ : syracuseStep 3567887 = 5351831) B5351831
theorem B323871 : Blo 323837 323871 := bstep (se 1 (by rfl) ⟨242903, by rfl⟩ : syracuseStep 323871 = 485807) B485807
theorem B4157729 : Blo 323837 4157729 := bstep (se 2 (by rfl) ⟨1559148, by rfl⟩ : syracuseStep 4157729 = 3118297) B3118297
theorem B880969 : Blo 323837 880969 := bstep (se 2 (by rfl) ⟨330363, by rfl⟩ : syracuseStep 880969 = 660727) B660727
theorem B323931 : Blo 323837 323931 := bstep (se 1 (by rfl) ⟨242948, by rfl⟩ : syracuseStep 323931 = 485897) B485897
theorem B323951 : Blo 323837 323951 := bstep (se 1 (by rfl) ⟨242963, by rfl⟩ : syracuseStep 323951 = 485927) B485927
theorem B324007 : Blo 323837 324007 := bstep (se 1 (by rfl) ⟨243005, by rfl⟩ : syracuseStep 324007 = 486011) B486011
theorem B487847 : Blo 323837 487847 := bstep (se 1 (by rfl) ⟨365885, by rfl⟩ : syracuseStep 487847 = 731771) B731771
theorem B324091 : Blo 323837 324091 := bstep (se 1 (by rfl) ⟨243068, by rfl⟩ : syracuseStep 324091 = 486137) B486137
theorem B487931 : Blo 323837 487931 := bstep (se 1 (by rfl) ⟨365948, by rfl⟩ : syracuseStep 487931 = 731897) B731897
theorem B324159 : Blo 323837 324159 := bstep (se 1 (by rfl) ⟨243119, by rfl⟩ : syracuseStep 324159 = 486239) B486239
theorem B324167 : Blo 323837 324167 := bstep (se 1 (by rfl) ⟨243125, by rfl⟩ : syracuseStep 324167 = 486251) B486251
theorem B520825 : Blo 323837 520825 := bstep (se 2 (by rfl) ⟨195309, by rfl⟩ : syracuseStep 520825 = 390619) B390619
theorem B488057 : Blo 323837 488057 := bstep (se 2 (by rfl) ⟨183021, by rfl⟩ : syracuseStep 488057 = 366043) B366043
theorem B7959161 : Blo 323837 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B488111 : Blo 323837 488111 := bstep (se 1 (by rfl) ⟨366083, by rfl⟩ : syracuseStep 488111 = 732167) B732167
theorem B324319 : Blo 323837 324319 := bstep (se 1 (by rfl) ⟨243239, by rfl⟩ : syracuseStep 324319 = 486479) B486479
theorem B488159 : Blo 323837 488159 := bstep (se 1 (by rfl) ⟨366119, by rfl⟩ : syracuseStep 488159 = 732239) B732239
theorem B14480117 : Blo 323837 14480117 := bstep (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) B1357511
theorem B324399 : Blo 323837 324399 := bstep (se 1 (by rfl) ⟨243299, by rfl⟩ : syracuseStep 324399 = 486599) B486599
theorem B20083571 : Blo 323837 20083571 := bstep (se 1 (by rfl) ⟨15062678, by rfl⟩ : syracuseStep 20083571 = 30125357) B30125357
theorem B324507 : Blo 323837 324507 := bstep (se 1 (by rfl) ⟨243380, by rfl⟩ : syracuseStep 324507 = 486761) B486761
theorem B324559 : Blo 323837 324559 := bstep (se 1 (by rfl) ⟨243419, by rfl⟩ : syracuseStep 324559 = 486839) B486839
theorem B783323 : Blo 323837 783323 := bstep (se 1 (by rfl) ⟨587492, by rfl⟩ : syracuseStep 783323 = 1174985) B1174985
theorem B324583 : Blo 323837 324583 := bstep (se 1 (by rfl) ⟨243437, by rfl⟩ : syracuseStep 324583 = 486875) B486875
theorem B488423 : Blo 323837 488423 := bstep (se 1 (by rfl) ⟨366317, by rfl⟩ : syracuseStep 488423 = 732635) B732635
theorem B488681 : Blo 323837 488681 := bstep (se 2 (by rfl) ⟨183255, by rfl⟩ : syracuseStep 488681 = 366511) B366511
theorem B324895 : Blo 323837 324895 := bstep (se 1 (by rfl) ⟨243671, by rfl⟩ : syracuseStep 324895 = 487343) B487343
theorem B390431 : Blo 323837 390431 := bstep (se 1 (by rfl) ⟨292823, by rfl⟩ : syracuseStep 390431 = 585647) B585647
theorem B488735 : Blo 323837 488735 := bstep (se 1 (by rfl) ⟨366551, by rfl⟩ : syracuseStep 488735 = 733103) B733103
theorem B324955 : Blo 323837 324955 := bstep (se 1 (by rfl) ⟨243716, by rfl⟩ : syracuseStep 324955 = 487433) B487433
theorem B324975 : Blo 323837 324975 := bstep (se 1 (by rfl) ⟨243731, by rfl⟩ : syracuseStep 324975 = 487463) B487463
theorem B325031 : Blo 323837 325031 := bstep (se 1 (by rfl) ⟨243773, by rfl⟩ : syracuseStep 325031 = 487547) B487547
theorem B488903 : Blo 323837 488903 := bstep (se 1 (by rfl) ⟨366677, by rfl⟩ : syracuseStep 488903 = 733355) B733355
theorem B325115 : Blo 323837 325115 := bstep (se 1 (by rfl) ⟨243836, by rfl⟩ : syracuseStep 325115 = 487673) B487673
theorem B2094599 : Blo 323837 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B882233 : Blo 323837 882233 := bstep (se 2 (by rfl) ⟨330837, by rfl⟩ : syracuseStep 882233 = 661675) B661675
theorem B325183 : Blo 323837 325183 := bstep (se 1 (by rfl) ⟨243887, by rfl⟩ : syracuseStep 325183 = 487775) B487775
theorem B325191 : Blo 323837 325191 := bstep (se 1 (by rfl) ⟨243893, by rfl⟩ : syracuseStep 325191 = 487787) B487787
theorem B325343 : Blo 323837 325343 := bstep (se 1 (by rfl) ⟨244007, by rfl⟩ : syracuseStep 325343 = 488015) B488015
theorem B2782957 : Blo 323837 2782957 := bstep (se 3 (by rfl) ⟨521804, by rfl⟩ : syracuseStep 2782957 = 1043609) B1043609
theorem B489257 : Blo 323837 489257 := bstep (se 2 (by rfl) ⟨183471, by rfl⟩ : syracuseStep 489257 = 366943) B366943
theorem B325423 : Blo 323837 325423 := bstep (se 1 (by rfl) ⟨244067, by rfl⟩ : syracuseStep 325423 = 488135) B488135
theorem B489263 : Blo 323837 489263 := bstep (se 1 (by rfl) ⟨366947, by rfl⟩ : syracuseStep 489263 = 733895) B733895
theorem B7141175 : Blo 323837 7141175 := bstep (se 1 (by rfl) ⟨5355881, by rfl⟩ : syracuseStep 7141175 = 10711763) B10711763
theorem B325531 : Blo 323837 325531 := bstep (se 1 (by rfl) ⟨244148, by rfl⟩ : syracuseStep 325531 = 488297) B488297
theorem B325583 : Blo 323837 325583 := bstep (se 1 (by rfl) ⟨244187, by rfl⟩ : syracuseStep 325583 = 488375) B488375
theorem B325607 : Blo 323837 325607 := bstep (se 1 (by rfl) ⟨244205, by rfl⟩ : syracuseStep 325607 = 488411) B488411
theorem B4225159 : Blo 323837 4225159 := bstep (se 1 (by rfl) ⟨3168869, by rfl⟩ : syracuseStep 4225159 = 6337739) B6337739
theorem B489737 : Blo 323837 489737 := bstep (se 2 (by rfl) ⟨183651, by rfl⟩ : syracuseStep 489737 = 367303) B367303
theorem B325919 : Blo 323837 325919 := bstep (se 1 (by rfl) ⟨244439, by rfl⟩ : syracuseStep 325919 = 488879) B488879
theorem B325979 : Blo 323837 325979 := bstep (se 1 (by rfl) ⟨244484, by rfl⟩ : syracuseStep 325979 = 488969) B488969
theorem B522587 : Blo 323837 522587 := bstep (se 1 (by rfl) ⟨391940, by rfl⟩ : syracuseStep 522587 = 783881) B783881
theorem B325999 : Blo 323837 325999 := bstep (se 1 (by rfl) ⟨244499, by rfl⟩ : syracuseStep 325999 = 488999) B488999
theorem B489839 : Blo 323837 489839 := bstep (se 1 (by rfl) ⟨367379, by rfl⟩ : syracuseStep 489839 = 734759) B734759
theorem B883055 : Blo 323837 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B1571183 : Blo 323837 1571183 := bstep (se 1 (by rfl) ⟨1178387, by rfl⟩ : syracuseStep 1571183 = 2356775) B2356775
theorem B326055 : Blo 323837 326055 := bstep (se 1 (by rfl) ⟨244541, by rfl⟩ : syracuseStep 326055 = 489083) B489083
theorem B326139 : Blo 323837 326139 := bstep (se 1 (by rfl) ⟨244604, by rfl⟩ : syracuseStep 326139 = 489209) B489209
theorem B326207 : Blo 323837 326207 := bstep (se 1 (by rfl) ⟨244655, by rfl⟩ : syracuseStep 326207 = 489311) B489311
theorem B326215 : Blo 323837 326215 := bstep (se 1 (by rfl) ⟨244661, by rfl⟩ : syracuseStep 326215 = 489323) B489323
theorem B490055 : Blo 323837 490055 := bstep (se 1 (by rfl) ⟨367541, by rfl⟩ : syracuseStep 490055 = 735083) B735083
theorem B883271 : Blo 323837 883271 := bstep (se 1 (by rfl) ⟨662453, by rfl⟩ : syracuseStep 883271 = 1324907) B1324907
theorem B490091 : Blo 323837 490091 := bstep (se 1 (by rfl) ⟨367568, by rfl⟩ : syracuseStep 490091 = 735137) B735137
theorem B883423 : Blo 323837 883423 := bstep (se 1 (by rfl) ⟨662567, by rfl⟩ : syracuseStep 883423 = 1325135) B1325135
theorem B326367 : Blo 323837 326367 := bstep (se 1 (by rfl) ⟨244775, by rfl⟩ : syracuseStep 326367 = 489551) B489551
theorem B326447 : Blo 323837 326447 := bstep (se 1 (by rfl) ⟨244835, by rfl⟩ : syracuseStep 326447 = 489671) B489671
theorem B490319 : Blo 323837 490319 := bstep (se 1 (by rfl) ⟨367739, by rfl⟩ : syracuseStep 490319 = 735479) B735479
theorem B326555 : Blo 323837 326555 := bstep (se 1 (by rfl) ⟨244916, by rfl⟩ : syracuseStep 326555 = 489833) B489833
theorem B326607 : Blo 323837 326607 := bstep (se 1 (by rfl) ⟨244955, by rfl⟩ : syracuseStep 326607 = 489911) B489911
theorem B326631 : Blo 323837 326631 := bstep (se 1 (by rfl) ⟨244973, by rfl⟩ : syracuseStep 326631 = 489947) B489947
theorem B392411 : Blo 323837 392411 := bstep (se 1 (by rfl) ⟨294308, by rfl⟩ : syracuseStep 392411 = 588617) B588617
theorem B490715 : Blo 323837 490715 := bstep (se 1 (by rfl) ⟨368036, by rfl⟩ : syracuseStep 490715 = 736073) B736073
theorem B326943 : Blo 323837 326943 := bstep (se 1 (by rfl) ⟨245207, by rfl⟩ : syracuseStep 326943 = 490415) B490415
theorem B851231 : Blo 323837 851231 := bstep (se 1 (by rfl) ⟨638423, by rfl⟩ : syracuseStep 851231 = 1276847) B1276847
theorem B327003 : Blo 323837 327003 := bstep (se 1 (by rfl) ⟨245252, by rfl⟩ : syracuseStep 327003 = 490505) B490505
theorem B327023 : Blo 323837 327023 := bstep (se 1 (by rfl) ⟨245267, by rfl⟩ : syracuseStep 327023 = 490535) B490535
theorem B490889 : Blo 323837 490889 := bstep (se 2 (by rfl) ⟨184083, by rfl⟩ : syracuseStep 490889 = 368167) B368167
theorem B327079 : Blo 323837 327079 := bstep (se 1 (by rfl) ⟨245309, by rfl⟩ : syracuseStep 327079 = 490619) B490619
theorem B622073 : Blo 323837 622073 := bstep (se 2 (by rfl) ⟨233277, by rfl⟩ : syracuseStep 622073 = 466555) B466555
theorem B327163 : Blo 323837 327163 := bstep (se 1 (by rfl) ⟨245372, by rfl⟩ : syracuseStep 327163 = 490745) B490745
theorem B327231 : Blo 323837 327231 := bstep (se 1 (by rfl) ⟨245423, by rfl⟩ : syracuseStep 327231 = 490847) B490847
theorem B327239 : Blo 323837 327239 := bstep (se 1 (by rfl) ⟨245429, by rfl⟩ : syracuseStep 327239 = 490859) B490859
theorem B1244753 : Blo 323837 1244753 := bstep (se 2 (by rfl) ⟨466782, by rfl⟩ : syracuseStep 1244753 = 933565) B933565
theorem B327391 : Blo 323837 327391 := bstep (se 1 (by rfl) ⟨245543, by rfl⟩ : syracuseStep 327391 = 491087) B491087
theorem B491243 : Blo 323837 491243 := bstep (se 1 (by rfl) ⟨368432, by rfl⟩ : syracuseStep 491243 = 736865) B736865
theorem B393007 : Blo 323837 393007 := bstep (se 1 (by rfl) ⟨294755, by rfl⟩ : syracuseStep 393007 = 589511) B589511
theorem B327471 : Blo 323837 327471 := bstep (se 1 (by rfl) ⟨245603, by rfl⟩ : syracuseStep 327471 = 491207) B491207
theorem B327579 : Blo 323837 327579 := bstep (se 1 (by rfl) ⟨245684, by rfl⟩ : syracuseStep 327579 = 491369) B491369
theorem B327631 : Blo 323837 327631 := bstep (se 1 (by rfl) ⟨245723, by rfl⟩ : syracuseStep 327631 = 491447) B491447
theorem B491471 : Blo 323837 491471 := bstep (se 1 (by rfl) ⟨368603, by rfl⟩ : syracuseStep 491471 = 737207) B737207
theorem B327655 : Blo 323837 327655 := bstep (se 1 (by rfl) ⟨245741, by rfl⟩ : syracuseStep 327655 = 491483) B491483
theorem B1180001 : Blo 323837 1180001 := bstep (se 2 (by rfl) ⟨442500, by rfl⟩ : syracuseStep 1180001 = 885001) B885001
theorem B819841 : Blo 323837 819841 := bstep (se 2 (by rfl) ⟨307440, by rfl⟩ : syracuseStep 819841 = 614881) B614881
theorem B4719545 : Blo 323837 4719545 := bstep (se 2 (by rfl) ⟨1769829, by rfl⟩ : syracuseStep 4719545 = 3539659) B3539659
theorem B1049555 : Blo 323837 1049555 := bstep (se 1 (by rfl) ⟨787166, by rfl⟩ : syracuseStep 1049555 = 1574333) B1574333
theorem B1049993 : Blo 323837 1049993 := bstep (se 2 (by rfl) ⟨393747, by rfl⟩ : syracuseStep 1049993 = 787495) B787495
theorem B3966347 : Blo 323837 3966347 := bstep (se 1 (by rfl) ⟨2974760, by rfl⟩ : syracuseStep 3966347 = 5949521) B5949521
theorem B820651 : Blo 323837 820651 := bstep (se 1 (by rfl) ⟨615488, by rfl⟩ : syracuseStep 820651 = 1230977) B1230977
theorem B820955 : Blo 323837 820955 := bstep (se 1 (by rfl) ⟨615716, by rfl⟩ : syracuseStep 820955 = 1231433) B1231433
theorem B73664369 : Blo 323837 73664369 := bstep (se 2 (by rfl) ⟨27624138, by rfl⟩ : syracuseStep 73664369 = 55248277) B55248277
theorem B3508343 : Blo 323837 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B6293639 : Blo 323837 6293639 := bstep (se 1 (by rfl) ⟨4720229, by rfl⟩ : syracuseStep 6293639 = 9440459) B9440459
theorem B985483 : Blo 323837 985483 := bstep (se 1 (by rfl) ⟨739112, by rfl⟩ : syracuseStep 985483 = 1478225) B1478225
theorem B1640897 : Blo 323837 1640897 := bstep (se 2 (by rfl) ⟨615336, by rfl⟩ : syracuseStep 1640897 = 1230673) B1230673
theorem B3574277 : Blo 323837 3574277 := bstep (se 4 (by rfl) ⟨335088, by rfl⟩ : syracuseStep 3574277 = 670177) B670177
theorem B821947 : Blo 323837 821947 := bstep (se 1 (by rfl) ⟨616460, by rfl⟩ : syracuseStep 821947 = 1232921) B1232921
theorem B822251 : Blo 323837 822251 := bstep (se 1 (by rfl) ⟨616688, by rfl⟩ : syracuseStep 822251 = 1233377) B1233377
theorem B10325069 : Blo 323837 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B3116339 : Blo 323837 3116339 := bstep (se 1 (by rfl) ⟨2337254, by rfl⟩ : syracuseStep 3116339 = 4674509) B4674509
theorem B4165415 : Blo 323837 4165415 := bstep (se 1 (by rfl) ⟨3124061, by rfl⟩ : syracuseStep 4165415 = 6248123) B6248123
theorem B790651 : Blo 323837 790651 := bstep (se 1 (by rfl) ⟨592988, by rfl⟩ : syracuseStep 790651 = 1185977) B1185977
theorem B364927 : Blo 323837 364927 := bstep (se 1 (by rfl) ⟨273695, by rfl⟩ : syracuseStep 364927 = 547391) B547391
theorem B823679 : Blo 323837 823679 := bstep (se 1 (by rfl) ⟨617759, by rfl⟩ : syracuseStep 823679 = 1235519) B1235519
theorem B823891 : Blo 323837 823891 := bstep (se 1 (by rfl) ⟨617918, by rfl⟩ : syracuseStep 823891 = 1235837) B1235837
theorem B1971011 : Blo 323837 1971011 := bstep (se 1 (by rfl) ⟨1478258, by rfl⟩ : syracuseStep 1971011 = 2956517) B2956517
theorem B13308785 : Blo 323837 13308785 := bstep (se 2 (by rfl) ⟨4990794, by rfl⟩ : syracuseStep 13308785 = 9981589) B9981589
theorem B366331 : Blo 323837 366331 := bstep (se 1 (by rfl) ⟨274748, by rfl⟩ : syracuseStep 366331 = 549497) B549497
theorem B1644299 : Blo 323837 1644299 := bstep (se 1 (by rfl) ⟨1233224, by rfl⟩ : syracuseStep 1644299 = 2466449) B2466449
theorem B366367 : Blo 323837 366367 := bstep (se 1 (by rfl) ⟨274775, by rfl⟩ : syracuseStep 366367 = 549551) B549551
theorem B694433 : Blo 323837 694433 := bstep (se 2 (by rfl) ⟨260412, by rfl⟩ : syracuseStep 694433 = 520825) B520825
theorem B465193 : Blo 323837 465193 := bstep (se 2 (by rfl) ⟨174447, by rfl⟩ : syracuseStep 465193 = 348895) B348895
theorem B1055099 : Blo 323837 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B924281 : Blo 323837 924281 := bstep (se 2 (by rfl) ⟨346605, by rfl⟩ : syracuseStep 924281 = 693211) B693211
theorem B10623899 : Blo 323837 10623899 := bstep (se 1 (by rfl) ⟨7967924, by rfl⟩ : syracuseStep 10623899 = 15935849) B15935849
theorem B826271 : Blo 323837 826271 := bstep (se 1 (by rfl) ⟨619703, by rfl⟩ : syracuseStep 826271 = 1239407) B1239407
theorem B367519 : Blo 323837 367519 := bstep (se 1 (by rfl) ⟨275639, by rfl⟩ : syracuseStep 367519 = 551279) B551279
theorem B367663 : Blo 323837 367663 := bstep (se 1 (by rfl) ⟨275747, by rfl⟩ : syracuseStep 367663 = 551495) B551495
theorem B2792663 : Blo 323837 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B367951 : Blo 323837 367951 := bstep (se 1 (by rfl) ⟨275963, by rfl⟩ : syracuseStep 367951 = 551927) B551927
theorem B1645919 : Blo 323837 1645919 := bstep (se 1 (by rfl) ⟨1234439, by rfl⟩ : syracuseStep 1645919 = 2468879) B2468879
theorem B3710609 : Blo 323837 3710609 := bstep (se 2 (by rfl) ⟨1391478, by rfl⟩ : syracuseStep 3710609 = 2782957) B2782957
theorem B728801 : Blo 323837 728801 := bstep (se 2 (by rfl) ⟨273300, by rfl⟩ : syracuseStep 728801 = 546601) B546601
theorem B4169515 : Blo 323837 4169515 := bstep (se 1 (by rfl) ⟨3127136, by rfl⟩ : syracuseStep 4169515 = 6254273) B6254273
theorem B368455 : Blo 323837 368455 := bstep (se 1 (by rfl) ⟨276341, by rfl⟩ : syracuseStep 368455 = 552683) B552683
theorem B1188215 : Blo 323837 1188215 := bstep (se 1 (by rfl) ⟨891161, by rfl⟩ : syracuseStep 1188215 = 1782323) B1782323
theorem B664367 : Blo 323837 664367 := bstep (se 1 (by rfl) ⟨498275, by rfl⟩ : syracuseStep 664367 = 996551) B996551
theorem B1975195 : Blo 323837 1975195 := bstep (se 1 (by rfl) ⟨1481396, by rfl⟩ : syracuseStep 1975195 = 2962793) B2962793
theorem B4760783 : Blo 323837 4760783 := bstep (se 1 (by rfl) ⟨3570587, by rfl⟩ : syracuseStep 4760783 = 7141175) B7141175
theorem B730475 : Blo 323837 730475 := bstep (se 1 (by rfl) ⟨547856, by rfl⟩ : syracuseStep 730475 = 1095713) B1095713
theorem B1648187 : Blo 323837 1648187 := bstep (se 1 (by rfl) ⟨1236140, by rfl⟩ : syracuseStep 1648187 = 2472281) B2472281
theorem B730745 : Blo 323837 730745 := bstep (se 2 (by rfl) ⟨274029, by rfl⟩ : syracuseStep 730745 = 548059) B548059
theorem B16262927 : Blo 323837 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B1845281 : Blo 323837 1845281 := bstep (se 2 (by rfl) ⟨691980, by rfl⟩ : syracuseStep 1845281 = 1383961) B1383961
theorem B1124543 : Blo 323837 1124543 := bstep (se 1 (by rfl) ⟨843407, by rfl⟩ : syracuseStep 1124543 = 1686815) B1686815
theorem B567487 : Blo 323837 567487 := bstep (se 1 (by rfl) ⟨425615, by rfl⟩ : syracuseStep 567487 = 851231) B851231
theorem B1845463 : Blo 323837 1845463 := bstep (se 1 (by rfl) ⟨1384097, by rfl⟩ : syracuseStep 1845463 = 2768195) B2768195
theorem B2337049 : Blo 323837 2337049 := bstep (se 2 (by rfl) ⟨876393, by rfl⟩ : syracuseStep 2337049 = 1752787) B1752787
theorem B1321273 : Blo 323837 1321273 := bstep (se 2 (by rfl) ⟨495477, by rfl⟩ : syracuseStep 1321273 = 990955) B990955
theorem B829835 : Blo 323837 829835 := bstep (se 1 (by rfl) ⟨622376, by rfl⟩ : syracuseStep 829835 = 1244753) B1244753
theorem B5581223 : Blo 323837 5581223 := bstep (se 1 (by rfl) ⟨4185917, by rfl⟩ : syracuseStep 5581223 = 8371835) B8371835
theorem B2337281 : Blo 323837 2337281 := bstep (se 2 (by rfl) ⟨876480, by rfl⟩ : syracuseStep 2337281 = 1752961) B1752961
theorem B731753 : Blo 323837 731753 := bstep (se 2 (by rfl) ⟨274407, by rfl⟩ : syracuseStep 731753 = 548815) B548815
theorem B502831 : Blo 323837 502831 := bstep (se 1 (by rfl) ⟨377123, by rfl⟩ : syracuseStep 502831 = 754247) B754247
theorem B9120883 : Blo 323837 9120883 := bstep (se 1 (by rfl) ⟨6840662, by rfl⟩ : syracuseStep 9120883 = 13681325) B13681325
theorem B1649807 : Blo 323837 1649807 := bstep (se 1 (by rfl) ⟨1237355, by rfl⟩ : syracuseStep 1649807 = 2474711) B2474711
theorem B732383 : Blo 323837 732383 := bstep (se 1 (by rfl) ⟨549287, by rfl⟩ : syracuseStep 732383 = 1098575) B1098575
theorem B732599 : Blo 323837 732599 := bstep (se 1 (by rfl) ⟨549449, by rfl⟩ : syracuseStep 732599 = 1098899) B1098899
theorem B699977 : Blo 323837 699977 := bstep (se 2 (by rfl) ⟨262491, by rfl⟩ : syracuseStep 699977 = 524983) B524983
theorem B732779 : Blo 323837 732779 := bstep (se 1 (by rfl) ⟨549584, by rfl⟩ : syracuseStep 732779 = 1099169) B1099169
theorem B733049 : Blo 323837 733049 := bstep (se 2 (by rfl) ⟨274893, by rfl⟩ : syracuseStep 733049 = 549787) B549787
theorem B929657 : Blo 323837 929657 := bstep (se 2 (by rfl) ⟨348621, by rfl⟩ : syracuseStep 929657 = 697243) B697243
theorem B1847195 : Blo 323837 1847195 := bstep (se 1 (by rfl) ⟨1385396, by rfl⟩ : syracuseStep 1847195 = 2770793) B2770793
theorem B1486799 : Blo 323837 1486799 := bstep (se 1 (by rfl) ⟨1115099, by rfl⟩ : syracuseStep 1486799 = 2230199) B2230199
theorem B1094525 : Blo 323837 1094525 := bstep (se 3 (by rfl) ⟨205223, by rfl⟩ : syracuseStep 1094525 = 410447) B410447
theorem B996407 : Blo 323837 996407 := bstep (se 1 (by rfl) ⟨747305, by rfl⟩ : syracuseStep 996407 = 1494611) B1494611
theorem B930923 : Blo 323837 930923 := bstep (se 1 (by rfl) ⟨698192, by rfl⟩ : syracuseStep 930923 = 1396385) B1396385
theorem B1094795 : Blo 323837 1094795 := bstep (se 1 (by rfl) ⟨821096, by rfl⟩ : syracuseStep 1094795 = 1642193) B1642193
theorem B734903 : Blo 323837 734903 := bstep (se 1 (by rfl) ⟨551177, by rfl⟩ : syracuseStep 734903 = 1102355) B1102355
theorem B931799 : Blo 323837 931799 := bstep (se 1 (by rfl) ⟨698849, by rfl⟩ : syracuseStep 931799 = 1397699) B1397699
theorem B1849337 : Blo 323837 1849337 := bstep (se 2 (by rfl) ⟨693501, by rfl⟩ : syracuseStep 1849337 = 1387003) B1387003
theorem B5585597 : Blo 323837 5585597 := bstep (se 3 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 5585597 = 2094599) B2094599
theorem B1096415 : Blo 323837 1096415 := bstep (se 1 (by rfl) ⟨822311, by rfl⟩ : syracuseStep 1096415 = 1644623) B1644623
theorem B1391327 : Blo 323837 1391327 := bstep (se 1 (by rfl) ⟨1043495, by rfl⟩ : syracuseStep 1391327 = 2086991) B2086991
theorem B736091 : Blo 323837 736091 := bstep (se 1 (by rfl) ⟨552068, by rfl⟩ : syracuseStep 736091 = 1104137) B1104137
theorem B1097171 : Blo 323837 1097171 := bstep (se 1 (by rfl) ⟨822878, by rfl⟩ : syracuseStep 1097171 = 1645757) B1645757
theorem B933383 : Blo 323837 933383 := bstep (se 1 (by rfl) ⟨700037, by rfl⟩ : syracuseStep 933383 = 1400075) B1400075
theorem B736847 : Blo 323837 736847 := bstep (se 1 (by rfl) ⟨552635, by rfl⟩ : syracuseStep 736847 = 1105271) B1105271
theorem B1097441 : Blo 323837 1097441 := bstep (se 2 (by rfl) ⟨411540, by rfl⟩ : syracuseStep 1097441 = 823081) B823081
theorem B1851113 : Blo 323837 1851113 := bstep (se 2 (by rfl) ⟨694167, by rfl⟩ : syracuseStep 1851113 = 1388335) B1388335
theorem B1654505 : Blo 323837 1654505 := bstep (se 2 (by rfl) ⟨620439, by rfl⟩ : syracuseStep 1654505 = 1240879) B1240879
theorem B1130635 : Blo 323837 1130635 := bstep (se 1 (by rfl) ⟨847976, by rfl⟩ : syracuseStep 1130635 = 1695953) B1695953
theorem B737567 : Blo 323837 737567 := bstep (se 1 (by rfl) ⟨553175, by rfl⟩ : syracuseStep 737567 = 1106351) B1106351
theorem B8864731 : Blo 323837 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B1099115 : Blo 323837 1099115 := bstep (se 1 (by rfl) ⟨824336, by rfl⟩ : syracuseStep 1099115 = 1648673) B1648673
theorem B1099223 : Blo 323837 1099223 := bstep (se 1 (by rfl) ⟨824417, by rfl⟩ : syracuseStep 1099223 = 1648835) B1648835
theorem B411247 : Blo 323837 411247 := bstep (se 1 (by rfl) ⟨308435, by rfl⟩ : syracuseStep 411247 = 616871) B616871
theorem B1099385 : Blo 323837 1099385 := bstep (se 2 (by rfl) ⟨412269, by rfl⟩ : syracuseStep 1099385 = 824539) B824539
theorem B20072285 : Blo 323837 20072285 := bstep (se 3 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 20072285 = 7527107) B7527107
theorem B837473 : Blo 323837 837473 := bstep (se 2 (by rfl) ⟨314052, by rfl⟩ : syracuseStep 837473 = 628105) B628105
theorem B411743 : Blo 323837 411743 := bstep (se 1 (by rfl) ⟨308807, by rfl⟩ : syracuseStep 411743 = 617615) B617615
theorem B2378591 : Blo 323837 2378591 := bstep (se 1 (by rfl) ⟨1783943, by rfl⟩ : syracuseStep 2378591 = 3567887) B3567887
theorem B2771819 : Blo 323837 2771819 := bstep (se 1 (by rfl) ⟨2078864, by rfl⟩ : syracuseStep 2771819 = 4157729) B4157729
theorem B3722273 : Blo 323837 3722273 := bstep (se 2 (by rfl) ⟨1395852, by rfl⟩ : syracuseStep 3722273 = 2791705) B2791705
theorem B1100897 : Blo 323837 1100897 := bstep (se 2 (by rfl) ⟨412836, by rfl⟩ : syracuseStep 1100897 = 825673) B825673
theorem B9653411 : Blo 323837 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B13389047 : Blo 323837 13389047 := bstep (se 1 (by rfl) ⟨10041785, by rfl⟩ : syracuseStep 13389047 = 20083571) B20083571
theorem B2477627 : Blo 323837 2477627 := bstep (se 1 (by rfl) ⟨1858220, by rfl⟩ : syracuseStep 2477627 = 3716441) B3716441
theorem B2772569 : Blo 323837 2772569 := bstep (se 2 (by rfl) ⟨1039713, by rfl⟩ : syracuseStep 2772569 = 2079427) B2079427
theorem B1101437 : Blo 323837 1101437 := bstep (se 3 (by rfl) ⟨206519, by rfl⟩ : syracuseStep 1101437 = 413039) B413039
theorem B1101707 : Blo 323837 1101707 := bstep (se 1 (by rfl) ⟨826280, by rfl⟩ : syracuseStep 1101707 = 1652561) B1652561
theorem B511915 : Blo 323837 511915 := bstep (se 1 (by rfl) ⟨383936, by rfl⟩ : syracuseStep 511915 = 767873) B767873
theorem B348391 : Blo 323837 348391 := bstep (se 1 (by rfl) ⟨261293, by rfl⟩ : syracuseStep 348391 = 522587) B522587
theorem B1102247 : Blo 323837 1102247 := bstep (se 1 (by rfl) ⟨826685, by rfl⟩ : syracuseStep 1102247 = 1653371) B1653371
theorem B414715 : Blo 323837 414715 := bstep (se 1 (by rfl) ⟨311036, by rfl⟩ : syracuseStep 414715 = 622073) B622073
theorem B1561609 : Blo 323837 1561609 := bstep (se 2 (by rfl) ⟨585603, by rfl⟩ : syracuseStep 1561609 = 1171207) B1171207
theorem B2413577 : Blo 323837 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B1103543 : Blo 323837 1103543 := bstep (se 1 (by rfl) ⟨827657, by rfl⟩ : syracuseStep 1103543 = 1655315) B1655315
theorem B546527 : Blo 323837 546527 := bstep (se 1 (by rfl) ⟨409895, by rfl⟩ : syracuseStep 546527 = 819791) B819791
theorem B3725189 : Blo 323837 3725189 := bstep (se 4 (by rfl) ⟨349236, by rfl⟩ : syracuseStep 3725189 = 698473) B698473
theorem B1038433 : Blo 323837 1038433 := bstep (se 2 (by rfl) ⟨389412, by rfl⟩ : syracuseStep 1038433 = 778825) B778825
theorem B546959 : Blo 323837 546959 := bstep (se 1 (by rfl) ⟨410219, by rfl⟩ : syracuseStep 546959 = 820439) B820439
theorem B547195 : Blo 323837 547195 := bstep (se 1 (by rfl) ⟨410396, by rfl⟩ : syracuseStep 547195 = 820793) B820793
theorem B3955067 : Blo 323837 3955067 := bstep (se 1 (by rfl) ⟨2966300, by rfl⟩ : syracuseStep 3955067 = 5932601) B5932601
theorem B547465 : Blo 323837 547465 := bstep (se 2 (by rfl) ⟨205299, by rfl⟩ : syracuseStep 547465 = 410599) B410599
theorem B6314669 : Blo 323837 6314669 := bstep (se 3 (by rfl) ⟨1184000, by rfl⟩ : syracuseStep 6314669 = 2368001) B2368001
theorem B744275 : Blo 323837 744275 := bstep (se 1 (by rfl) ⟨558206, by rfl⟩ : syracuseStep 744275 = 1116413) B1116413
theorem B416603 : Blo 323837 416603 := bstep (se 1 (by rfl) ⟨312452, by rfl⟩ : syracuseStep 416603 = 624905) B624905
theorem B1104731 : Blo 323837 1104731 := bstep (se 1 (by rfl) ⟨828548, by rfl⟩ : syracuseStep 1104731 = 1657097) B1657097
theorem B1793015 : Blo 323837 1793015 := bstep (se 1 (by rfl) ⟨1344761, by rfl⟩ : syracuseStep 1793015 = 2689523) B2689523
theorem B5069873 : Blo 323837 5069873 := bstep (se 2 (by rfl) ⟨1901202, by rfl⟩ : syracuseStep 5069873 = 3802405) B3802405
theorem B1400159 : Blo 323837 1400159 := bstep (se 1 (by rfl) ⟨1050119, by rfl⟩ : syracuseStep 1400159 = 2100239) B2100239
theorem B1105487 : Blo 323837 1105487 := bstep (se 1 (by rfl) ⟨829115, by rfl⟩ : syracuseStep 1105487 = 1658231) B1658231
theorem B1105595 : Blo 323837 1105595 := bstep (se 1 (by rfl) ⟨829196, by rfl⟩ : syracuseStep 1105595 = 1658393) B1658393
theorem B1040215 : Blo 323837 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B1761527 : Blo 323837 1761527 := bstep (se 1 (by rfl) ⟨1321145, by rfl⟩ : syracuseStep 1761527 = 2642291) B2642291
theorem B549247 : Blo 323837 549247 := bstep (se 1 (by rfl) ⟨411935, by rfl⟩ : syracuseStep 549247 = 823871) B823871
theorem B1041149 : Blo 323837 1041149 := bstep (se 3 (by rfl) ⟨195215, by rfl⟩ : syracuseStep 1041149 = 390431) B390431
theorem B615215 : Blo 323837 615215 := bstep (se 1 (by rfl) ⟨461411, by rfl⟩ : syracuseStep 615215 = 922823) B922823
theorem B549679 : Blo 323837 549679 := bstep (se 1 (by rfl) ⟨412259, by rfl⟩ : syracuseStep 549679 = 824519) B824519
theorem B40035221 : Blo 323837 40035221 := bstep (se 6 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 40035221 = 1876651) B1876651
theorem B1861001 : Blo 323837 1861001 := bstep (se 2 (by rfl) ⟨697875, by rfl⟩ : syracuseStep 1861001 = 1395751) B1395751
theorem B2647673 : Blo 323837 2647673 := bstep (se 2 (by rfl) ⟨992877, by rfl⟩ : syracuseStep 2647673 = 1985755) B1985755
theorem B2090681 : Blo 323837 2090681 := bstep (se 2 (by rfl) ⟨784005, by rfl⟩ : syracuseStep 2090681 = 1568011) B1568011
theorem B550651 : Blo 323837 550651 := bstep (se 1 (by rfl) ⟨412988, by rfl⟩ : syracuseStep 550651 = 825977) B825977
theorem B714575 : Blo 323837 714575 := bstep (se 1 (by rfl) ⟨535931, by rfl⟩ : syracuseStep 714575 = 1071863) B1071863
theorem B550793 : Blo 323837 550793 := bstep (se 2 (by rfl) ⟨206547, by rfl⟩ : syracuseStep 550793 = 413095) B413095
theorem B780479 : Blo 323837 780479 := bstep (se 1 (by rfl) ⟨585359, by rfl⟩ : syracuseStep 780479 = 1170719) B1170719
theorem B551225 : Blo 323837 551225 := bstep (se 2 (by rfl) ⟨206709, by rfl⟩ : syracuseStep 551225 = 413419) B413419
theorem B1862027 : Blo 323837 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B485915 : Blo 323837 485915 := bstep (se 1 (by rfl) ⟨364436, by rfl⟩ : syracuseStep 485915 = 728873) B728873
theorem B485993 : Blo 323837 485993 := bstep (se 2 (by rfl) ⟨182247, by rfl⟩ : syracuseStep 485993 = 364495) B364495
theorem B9366191 : Blo 323837 9366191 := bstep (se 1 (by rfl) ⟨7024643, by rfl⟩ : syracuseStep 9366191 = 14049287) B14049287
theorem B551839 : Blo 323837 551839 := bstep (se 1 (by rfl) ⟨413879, by rfl⟩ : syracuseStep 551839 = 827759) B827759
theorem B1174625 : Blo 323837 1174625 := bstep (se 2 (by rfl) ⟨440484, by rfl⟩ : syracuseStep 1174625 = 880969) B880969
theorem B486521 : Blo 323837 486521 := bstep (se 2 (by rfl) ⟨182445, by rfl⟩ : syracuseStep 486521 = 364891) B364891
theorem B1862777 : Blo 323837 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B486623 : Blo 323837 486623 := bstep (se 1 (by rfl) ⟨364967, by rfl⟩ : syracuseStep 486623 = 729935) B729935
theorem B486665 : Blo 323837 486665 := bstep (se 2 (by rfl) ⟨182499, by rfl⟩ : syracuseStep 486665 = 364999) B364999
theorem B5008709 : Blo 323837 5008709 := bstep (se 4 (by rfl) ⟨469566, by rfl⟩ : syracuseStep 5008709 = 939133) B939133
theorem B4484429 : Blo 323837 4484429 := bstep (se 3 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 4484429 = 1681661) B1681661
theorem B552271 : Blo 323837 552271 := bstep (se 1 (by rfl) ⟨414203, by rfl⟩ : syracuseStep 552271 = 828407) B828407
theorem B486767 : Blo 323837 486767 := bstep (se 1 (by rfl) ⟨365075, by rfl⟩ : syracuseStep 486767 = 730151) B730151
theorem B552359 : Blo 323837 552359 := bstep (se 1 (by rfl) ⟨414269, by rfl⟩ : syracuseStep 552359 = 828539) B828539
theorem B5533109 : Blo 323837 5533109 := bstep (se 5 (by rfl) ⟨259364, by rfl⟩ : syracuseStep 5533109 = 518729) B518729
theorem B486887 : Blo 323837 486887 := bstep (se 1 (by rfl) ⟨365165, by rfl⟩ : syracuseStep 486887 = 730331) B730331
theorem B552521 : Blo 323837 552521 := bstep (se 2 (by rfl) ⟨207195, by rfl⟩ : syracuseStep 552521 = 414391) B414391
theorem B487019 : Blo 323837 487019 := bstep (se 1 (by rfl) ⟨365264, by rfl⟩ : syracuseStep 487019 = 730529) B730529
theorem B487145 : Blo 323837 487145 := bstep (se 2 (by rfl) ⟨182679, by rfl⟩ : syracuseStep 487145 = 365359) B365359
theorem B1863485 : Blo 323837 1863485 := bstep (se 3 (by rfl) ⟨349403, by rfl⟩ : syracuseStep 1863485 = 698807) B698807
theorem B487289 : Blo 323837 487289 := bstep (se 2 (by rfl) ⟨182733, by rfl⟩ : syracuseStep 487289 = 365467) B365467
theorem B2944907 : Blo 323837 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B487391 : Blo 323837 487391 := bstep (se 1 (by rfl) ⟨365543, by rfl⟩ : syracuseStep 487391 = 731087) B731087
theorem B2355389 : Blo 323837 2355389 := bstep (se 3 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 2355389 = 883271) B883271
theorem B487643 : Blo 323837 487643 := bstep (se 1 (by rfl) ⟨365732, by rfl⟩ : syracuseStep 487643 = 731465) B731465
theorem B487655 : Blo 323837 487655 := bstep (se 1 (by rfl) ⟨365741, by rfl⟩ : syracuseStep 487655 = 731483) B731483
theorem B2126089 : Blo 323837 2126089 := bstep (se 2 (by rfl) ⟨797283, by rfl⟩ : syracuseStep 2126089 = 1594567) B1594567
theorem B8319347 : Blo 323837 8319347 := bstep (se 1 (by rfl) ⟨6239510, by rfl⟩ : syracuseStep 8319347 = 12479021) B12479021
theorem B323967 : Blo 323837 323967 := bstep (se 1 (by rfl) ⟨242975, by rfl⟩ : syracuseStep 323967 = 485951) B485951
theorem B487817 : Blo 323837 487817 := bstep (se 2 (by rfl) ⟨182931, by rfl⟩ : syracuseStep 487817 = 365863) B365863
theorem B324047 : Blo 323837 324047 := bstep (se 1 (by rfl) ⟨243035, by rfl⟩ : syracuseStep 324047 = 486071) B486071
theorem B487913 : Blo 323837 487913 := bstep (se 2 (by rfl) ⟨182967, by rfl⟩ : syracuseStep 487913 = 365935) B365935
theorem B1110611 : Blo 323837 1110611 := bstep (se 1 (by rfl) ⟨832958, by rfl⟩ : syracuseStep 1110611 = 1665917) B1665917
theorem B619103 : Blo 323837 619103 := bstep (se 1 (by rfl) ⟨464327, by rfl⟩ : syracuseStep 619103 = 928655) B928655
theorem B324199 : Blo 323837 324199 := bstep (se 1 (by rfl) ⟨243149, by rfl⟩ : syracuseStep 324199 = 486299) B486299
theorem B488039 : Blo 323837 488039 := bstep (se 1 (by rfl) ⟨366029, by rfl⟩ : syracuseStep 488039 = 732059) B732059
theorem B488171 : Blo 323837 488171 := bstep (se 1 (by rfl) ⟨366128, by rfl⟩ : syracuseStep 488171 = 732257) B732257
theorem B488201 : Blo 323837 488201 := bstep (se 2 (by rfl) ⟨183075, by rfl⟩ : syracuseStep 488201 = 366151) B366151
theorem B324463 : Blo 323837 324463 := bstep (se 1 (by rfl) ⟨243347, by rfl⟩ : syracuseStep 324463 = 486695) B486695
theorem B488303 : Blo 323837 488303 := bstep (se 1 (by rfl) ⟨366227, by rfl⟩ : syracuseStep 488303 = 732455) B732455
theorem B324519 : Blo 323837 324519 := bstep (se 1 (by rfl) ⟨243389, by rfl⟩ : syracuseStep 324519 = 486779) B486779
theorem B324603 : Blo 323837 324603 := bstep (se 1 (by rfl) ⟨243452, by rfl⟩ : syracuseStep 324603 = 486905) B486905
theorem B324671 : Blo 323837 324671 := bstep (se 1 (by rfl) ⟨243503, by rfl⟩ : syracuseStep 324671 = 487007) B487007
theorem B488555 : Blo 323837 488555 := bstep (se 1 (by rfl) ⟨366416, by rfl⟩ : syracuseStep 488555 = 732833) B732833
theorem B324815 : Blo 323837 324815 := bstep (se 1 (by rfl) ⟨243611, by rfl⟩ : syracuseStep 324815 = 487223) B487223
theorem B488795 : Blo 323837 488795 := bstep (se 1 (by rfl) ⟨366596, by rfl⟩ : syracuseStep 488795 = 733193) B733193
theorem B325019 : Blo 323837 325019 := bstep (se 1 (by rfl) ⟨243764, by rfl⟩ : syracuseStep 325019 = 487529) B487529
theorem B5633545 : Blo 323837 5633545 := bstep (se 2 (by rfl) ⟨2112579, by rfl⟩ : syracuseStep 5633545 = 4225159) B4225159
theorem B325231 : Blo 323837 325231 := bstep (se 1 (by rfl) ⟨243923, by rfl⟩ : syracuseStep 325231 = 487847) B487847
theorem B489071 : Blo 323837 489071 := bstep (se 1 (by rfl) ⟨366803, by rfl⟩ : syracuseStep 489071 = 733607) B733607
theorem B325287 : Blo 323837 325287 := bstep (se 1 (by rfl) ⟨243965, by rfl⟩ : syracuseStep 325287 = 487931) B487931
theorem B489143 : Blo 323837 489143 := bstep (se 1 (by rfl) ⟨366857, by rfl⟩ : syracuseStep 489143 = 733715) B733715
theorem B489179 : Blo 323837 489179 := bstep (se 1 (by rfl) ⟨366884, by rfl⟩ : syracuseStep 489179 = 733769) B733769
theorem B325371 : Blo 323837 325371 := bstep (se 1 (by rfl) ⟨244028, by rfl⟩ : syracuseStep 325371 = 488057) B488057
theorem B5306107 : Blo 323837 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B325407 : Blo 323837 325407 := bstep (se 1 (by rfl) ⟨244055, by rfl⟩ : syracuseStep 325407 = 488111) B488111
theorem B325439 : Blo 323837 325439 := bstep (se 1 (by rfl) ⟨244079, by rfl⟩ : syracuseStep 325439 = 488159) B488159
theorem B489353 : Blo 323837 489353 := bstep (se 2 (by rfl) ⟨183507, by rfl⟩ : syracuseStep 489353 = 367015) B367015
theorem B1046429 : Blo 323837 1046429 := bstep (se 3 (by rfl) ⟨196205, by rfl⟩ : syracuseStep 1046429 = 392411) B392411
theorem B2389981 : Blo 323837 2389981 := bstep (se 3 (by rfl) ⟨448121, by rfl⟩ : syracuseStep 2389981 = 896243) B896243
theorem B522215 : Blo 323837 522215 := bstep (se 1 (by rfl) ⟨391661, by rfl⟩ : syracuseStep 522215 = 783323) B783323
theorem B1210351 : Blo 323837 1210351 := bstep (se 1 (by rfl) ⟨907763, by rfl⟩ : syracuseStep 1210351 = 1815527) B1815527
theorem B325615 : Blo 323837 325615 := bstep (se 1 (by rfl) ⟨244211, by rfl⟩ : syracuseStep 325615 = 488423) B488423
theorem B489455 : Blo 323837 489455 := bstep (se 1 (by rfl) ⟨367091, by rfl⟩ : syracuseStep 489455 = 734183) B734183
theorem B325787 : Blo 323837 325787 := bstep (se 1 (by rfl) ⟨244340, by rfl⟩ : syracuseStep 325787 = 488681) B488681
theorem B325823 : Blo 323837 325823 := bstep (se 1 (by rfl) ⟨244367, by rfl⟩ : syracuseStep 325823 = 488735) B488735
theorem B489707 : Blo 323837 489707 := bstep (se 1 (by rfl) ⟨367280, by rfl⟩ : syracuseStep 489707 = 734561) B734561
theorem B489767 : Blo 323837 489767 := bstep (se 1 (by rfl) ⟨367325, by rfl⟩ : syracuseStep 489767 = 734651) B734651
theorem B1177897 : Blo 323837 1177897 := bstep (se 2 (by rfl) ⟨441711, by rfl⟩ : syracuseStep 1177897 = 883423) B883423
theorem B325935 : Blo 323837 325935 := bstep (se 1 (by rfl) ⟨244451, by rfl⟩ : syracuseStep 325935 = 488903) B488903
theorem B588155 : Blo 323837 588155 := bstep (se 1 (by rfl) ⟨441116, by rfl⟩ : syracuseStep 588155 = 882233) B882233
theorem B489851 : Blo 323837 489851 := bstep (se 1 (by rfl) ⟨367388, by rfl⟩ : syracuseStep 489851 = 734777) B734777
theorem B326171 : Blo 323837 326171 := bstep (se 1 (by rfl) ⟨244628, by rfl⟩ : syracuseStep 326171 = 489257) B489257
theorem B326175 : Blo 323837 326175 := bstep (se 1 (by rfl) ⟨244631, by rfl⟩ : syracuseStep 326175 = 489263) B489263
theorem B490121 : Blo 323837 490121 := bstep (se 2 (by rfl) ⟨183795, by rfl⟩ : syracuseStep 490121 = 367591) B367591
theorem B490295 : Blo 323837 490295 := bstep (se 1 (by rfl) ⟨367721, by rfl⟩ : syracuseStep 490295 = 735443) B735443
theorem B490331 : Blo 323837 490331 := bstep (se 1 (by rfl) ⟨367748, by rfl⟩ : syracuseStep 490331 = 735497) B735497
theorem B326491 : Blo 323837 326491 := bstep (se 1 (by rfl) ⟨244868, by rfl⟩ : syracuseStep 326491 = 489737) B489737
theorem B1047455 : Blo 323837 1047455 := bstep (se 1 (by rfl) ⟨785591, by rfl⟩ : syracuseStep 1047455 = 1571183) B1571183
theorem B326559 : Blo 323837 326559 := bstep (se 1 (by rfl) ⟨244919, by rfl⟩ : syracuseStep 326559 = 489839) B489839
theorem B588703 : Blo 323837 588703 := bstep (se 1 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 588703 = 883055) B883055
theorem B490475 : Blo 323837 490475 := bstep (se 1 (by rfl) ⟨367856, by rfl⟩ : syracuseStep 490475 = 735713) B735713
theorem B326703 : Blo 323837 326703 := bstep (se 1 (by rfl) ⟨245027, by rfl⟩ : syracuseStep 326703 = 490055) B490055
theorem B326727 : Blo 323837 326727 := bstep (se 1 (by rfl) ⟨245045, by rfl⟩ : syracuseStep 326727 = 490091) B490091
theorem B1866833 : Blo 323837 1866833 := bstep (se 2 (by rfl) ⟨700062, by rfl⟩ : syracuseStep 1866833 = 1400125) B1400125
theorem B490679 : Blo 323837 490679 := bstep (se 1 (by rfl) ⟨368009, by rfl⟩ : syracuseStep 490679 = 736019) B736019
theorem B326879 : Blo 323837 326879 := bstep (se 1 (by rfl) ⟨245159, by rfl⟩ : syracuseStep 326879 = 490319) B490319
theorem B490919 : Blo 323837 490919 := bstep (se 1 (by rfl) ⟨368189, by rfl⟩ : syracuseStep 490919 = 736379) B736379
theorem B327143 : Blo 323837 327143 := bstep (se 1 (by rfl) ⟨245357, by rfl⟩ : syracuseStep 327143 = 490715) B490715
theorem B491003 : Blo 323837 491003 := bstep (se 1 (by rfl) ⟨368252, by rfl⟩ : syracuseStep 491003 = 736505) B736505
theorem B327259 : Blo 323837 327259 := bstep (se 1 (by rfl) ⟨245444, by rfl⟩ : syracuseStep 327259 = 490889) B490889
theorem B491099 : Blo 323837 491099 := bstep (se 1 (by rfl) ⟨368324, by rfl⟩ : syracuseStep 491099 = 736649) B736649
theorem B622171 : Blo 323837 622171 := bstep (se 1 (by rfl) ⟨466628, by rfl⟩ : syracuseStep 622171 = 933257) B933257
theorem B2784941 : Blo 323837 2784941 := bstep (se 3 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 2784941 = 1044353) B1044353
theorem B491183 : Blo 323837 491183 := bstep (se 1 (by rfl) ⟨368387, by rfl⟩ : syracuseStep 491183 = 736775) B736775
theorem B524009 : Blo 323837 524009 := bstep (se 2 (by rfl) ⟨196503, by rfl⟩ : syracuseStep 524009 = 393007) B393007
theorem B491303 : Blo 323837 491303 := bstep (se 1 (by rfl) ⟨368477, by rfl⟩ : syracuseStep 491303 = 736955) B736955
theorem B327495 : Blo 323837 327495 := bstep (se 1 (by rfl) ⟨245621, by rfl⟩ : syracuseStep 327495 = 491243) B491243
theorem B491387 : Blo 323837 491387 := bstep (se 1 (by rfl) ⟨368540, by rfl⟩ : syracuseStep 491387 = 737081) B737081
theorem B327647 : Blo 323837 327647 := bstep (se 1 (by rfl) ⟨245735, by rfl⟩ : syracuseStep 327647 = 491471) B491471
theorem B1507513 : Blo 323837 1507513 := bstep (se 2 (by rfl) ⟨565317, by rfl⟩ : syracuseStep 1507513 = 1130635) B1130635
theorem B491711 : Blo 323837 491711 := bstep (se 1 (by rfl) ⟨368783, by rfl⟩ : syracuseStep 491711 = 737567) B737567
theorem B786667 : Blo 323837 786667 := bstep (se 1 (by rfl) ⟨590000, by rfl⟩ : syracuseStep 786667 = 1180001) B1180001
theorem B3146363 : Blo 323837 3146363 := bstep (se 1 (by rfl) ⟨2359772, by rfl⟩ : syracuseStep 3146363 = 4719545) B4719545
theorem B4195759 : Blo 323837 4195759 := bstep (se 1 (by rfl) ⟨3146819, by rfl⟩ : syracuseStep 4195759 = 6293639) B6293639
theorem B6883379 : Blo 323837 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B1640573 : Blo 323837 1640573 := bstep (se 3 (by rfl) ⟨307607, by rfl⟩ : syracuseStep 1640573 = 615215) B615215
theorem B1771645 : Blo 323837 1771645 := bstep (se 3 (by rfl) ⟨332183, by rfl⟩ : syracuseStep 1771645 = 664367) B664367
theorem B756649 : Blo 323837 756649 := bstep (se 2 (by rfl) ⟨283743, by rfl⟩ : syracuseStep 756649 = 567487) B567487
theorem B2460617 : Blo 323837 2460617 := bstep (se 2 (by rfl) ⟨922731, by rfl⟩ : syracuseStep 2460617 = 1845463) B1845463
theorem B3116065 : Blo 323837 3116065 := bstep (se 2 (by rfl) ⟨1168524, by rfl⟩ : syracuseStep 3116065 = 2337049) B2337049
theorem B1313977 : Blo 323837 1313977 := bstep (se 2 (by rfl) ⟨492741, by rfl⟩ : syracuseStep 1313977 = 985483) B985483
theorem B364351 : Blo 323837 364351 := bstep (se 1 (by rfl) ⟨273263, by rfl⟩ : syracuseStep 364351 = 546527) B546527
theorem B364639 : Blo 323837 364639 := bstep (se 1 (by rfl) ⟨273479, by rfl⟩ : syracuseStep 364639 = 546959) B546959
theorem B12161177 : Blo 323837 12161177 := bstep (se 2 (by rfl) ⟨4560441, by rfl⟩ : syracuseStep 12161177 = 9120883) B9120883
theorem B7082599 : Blo 323837 7082599 := bstep (se 1 (by rfl) ⟨5311949, by rfl⟩ : syracuseStep 7082599 = 10623899) B10623899
theorem B3379915 : Blo 323837 3379915 := bstep (se 1 (by rfl) ⟨2534936, by rfl⟩ : syracuseStep 3379915 = 5069873) B5069873
theorem B2233261 : Blo 323837 2233261 := bstep (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) B837473
theorem B1054201 : Blo 323837 1054201 := bstep (se 2 (by rfl) ⟨395325, by rfl⟩ : syracuseStep 1054201 = 790651) B790651
theorem B792143 : Blo 323837 792143 := bstep (se 1 (by rfl) ⟨594107, by rfl⟩ : syracuseStep 792143 = 1188215) B1188215
theorem B694099 : Blo 323837 694099 := bstep (se 1 (by rfl) ⟨520574, by rfl⟩ : syracuseStep 694099 = 1041149) B1041149
theorem B367195 : Blo 323837 367195 := bstep (se 1 (by rfl) ⟨275396, by rfl⟩ : syracuseStep 367195 = 550793) B550793
theorem B367483 : Blo 323837 367483 := bstep (se 1 (by rfl) ⟨275612, by rfl⟩ : syracuseStep 367483 = 551225) B551225
theorem B7511393 : Blo 323837 7511393 := bstep (se 2 (by rfl) ⟨2816772, by rfl⟩ : syracuseStep 7511393 = 5633545) B5633545
theorem B2989619 : Blo 323837 2989619 := bstep (se 1 (by rfl) ⟨2242214, by rfl⟩ : syracuseStep 2989619 = 4484429) B4484429
theorem B368239 : Blo 323837 368239 := bstep (se 1 (by rfl) ⟨276179, by rfl⟩ : syracuseStep 368239 = 552359) B552359
theorem B368347 : Blo 323837 368347 := bstep (se 1 (by rfl) ⟨276260, by rfl⟩ : syracuseStep 368347 = 552521) B552521
theorem B466651 : Blo 323837 466651 := bstep (se 1 (by rfl) ⟨349988, by rfl⟩ : syracuseStep 466651 = 699977) B699977
theorem B3186641 : Blo 323837 3186641 := bstep (se 2 (by rfl) ⟨1194990, by rfl⟩ : syracuseStep 3186641 = 2389981) B2389981
theorem B991199 : Blo 323837 991199 := bstep (se 1 (by rfl) ⟨743399, by rfl⟩ : syracuseStep 991199 = 1486799) B1486799
theorem B1613801 : Blo 323837 1613801 := bstep (se 2 (by rfl) ⟨605175, by rfl⟩ : syracuseStep 1613801 = 1210351) B1210351
theorem B1384577 : Blo 323837 1384577 := bstep (se 2 (by rfl) ⟨519216, by rfl⟩ : syracuseStep 1384577 = 1038433) B1038433
theorem B5546231 : Blo 323837 5546231 := bstep (se 1 (by rfl) ⟨4159673, by rfl⟩ : syracuseStep 5546231 = 8319347) B8319347
theorem B729593 : Blo 323837 729593 := bstep (se 2 (by rfl) ⟨273597, by rfl⟩ : syracuseStep 729593 = 547195) B547195
theorem B729683 : Blo 323837 729683 := bstep (se 1 (by rfl) ⟨547262, by rfl⟩ : syracuseStep 729683 = 1094525) B1094525
theorem B664271 : Blo 323837 664271 := bstep (se 1 (by rfl) ⟨498203, by rfl⟩ : syracuseStep 664271 = 996407) B996407
theorem B729863 : Blo 323837 729863 := bstep (se 1 (by rfl) ⟨547397, by rfl⟩ : syracuseStep 729863 = 1094795) B1094795
theorem B729953 : Blo 323837 729953 := bstep (se 2 (by rfl) ⟨273732, by rfl⟩ : syracuseStep 729953 = 547465) B547465
theorem B697619 : Blo 323837 697619 := bstep (se 1 (by rfl) ⟨523214, by rfl⟩ : syracuseStep 697619 = 1046429) B1046429
theorem B730943 : Blo 323837 730943 := bstep (se 1 (by rfl) ⟨548207, by rfl⟩ : syracuseStep 730943 = 1096415) B1096415
theorem B927551 : Blo 323837 927551 := bstep (se 1 (by rfl) ⟨695663, by rfl⟩ : syracuseStep 927551 = 1391327) B1391327
theorem B698303 : Blo 323837 698303 := bstep (se 1 (by rfl) ⟨523727, by rfl⟩ : syracuseStep 698303 = 1047455) B1047455
theorem B829561 : Blo 323837 829561 := bstep (se 2 (by rfl) ⟨311085, by rfl⟩ : syracuseStep 829561 = 622171) B622171
theorem B731447 : Blo 323837 731447 := bstep (se 1 (by rfl) ⟨548585, by rfl⟩ : syracuseStep 731447 = 1097171) B1097171
theorem B1386953 : Blo 323837 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B731627 : Blo 323837 731627 := bstep (se 1 (by rfl) ⟨548720, by rfl⟩ : syracuseStep 731627 = 1097441) B1097441
theorem B732329 : Blo 323837 732329 := bstep (se 2 (by rfl) ⟨274623, by rfl⟩ : syracuseStep 732329 = 549247) B549247
theorem B1093121 : Blo 323837 1093121 := bstep (se 2 (by rfl) ⟨409920, by rfl⟩ : syracuseStep 1093121 = 819841) B819841
theorem B732743 : Blo 323837 732743 := bstep (se 1 (by rfl) ⟨549557, by rfl⟩ : syracuseStep 732743 = 1099115) B1099115
theorem B699995 : Blo 323837 699995 := bstep (se 1 (by rfl) ⟨524996, by rfl⟩ : syracuseStep 699995 = 1049993) B1049993
theorem B732815 : Blo 323837 732815 := bstep (se 1 (by rfl) ⟨549611, by rfl⟩ : syracuseStep 732815 = 1099223) B1099223
theorem B732905 : Blo 323837 732905 := bstep (se 2 (by rfl) ⟨274839, by rfl⟩ : syracuseStep 732905 = 549679) B549679
theorem B732923 : Blo 323837 732923 := bstep (se 1 (by rfl) ⟨549692, by rfl⟩ : syracuseStep 732923 = 1099385) B1099385
theorem B2633593 : Blo 323837 2633593 := bstep (se 2 (by rfl) ⟨987597, by rfl⟩ : syracuseStep 2633593 = 1975195) B1975195
theorem B13381523 : Blo 323837 13381523 := bstep (se 1 (by rfl) ⟨10036142, by rfl⟩ : syracuseStep 13381523 = 20072285) B20072285
theorem B2338895 : Blo 323837 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B1650941 : Blo 323837 1650941 := bstep (se 3 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 1650941 = 619103) B619103
theorem B1093931 : Blo 323837 1093931 := bstep (se 1 (by rfl) ⟨820448, by rfl⟩ : syracuseStep 1093931 = 1640897) B1640897
theorem B1094201 : Blo 323837 1094201 := bstep (se 2 (by rfl) ⟨410325, by rfl⟩ : syracuseStep 1094201 = 820651) B820651
theorem B1585727 : Blo 323837 1585727 := bstep (se 1 (by rfl) ⟨1189295, by rfl⟩ : syracuseStep 1585727 = 2378591) B2378591
theorem B1847879 : Blo 323837 1847879 := bstep (se 1 (by rfl) ⟨1385909, by rfl⟩ : syracuseStep 1847879 = 2771819) B2771819
theorem B733931 : Blo 323837 733931 := bstep (se 1 (by rfl) ⟨550448, by rfl⟩ : syracuseStep 733931 = 1100897) B1100897
theorem B6435607 : Blo 323837 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B8926031 : Blo 323837 8926031 := bstep (se 1 (by rfl) ⟨6694523, by rfl⟩ : syracuseStep 8926031 = 13389047) B13389047
theorem B5256029 : Blo 323837 5256029 := bstep (se 3 (by rfl) ⟨985505, by rfl⟩ : syracuseStep 5256029 = 1971011) B1971011
theorem B2077559 : Blo 323837 2077559 := bstep (se 1 (by rfl) ⟨1558169, by rfl⟩ : syracuseStep 2077559 = 3116339) B3116339
theorem B734201 : Blo 323837 734201 := bstep (se 2 (by rfl) ⟨275325, by rfl⟩ : syracuseStep 734201 = 550651) B550651
theorem B1651751 : Blo 323837 1651751 := bstep (se 1 (by rfl) ⟨1238813, by rfl⟩ : syracuseStep 1651751 = 2477627) B2477627
theorem B1848379 : Blo 323837 1848379 := bstep (se 1 (by rfl) ⟨1386284, by rfl⟩ : syracuseStep 1848379 = 2772569) B2772569
theorem B734291 : Blo 323837 734291 := bstep (se 1 (by rfl) ⟨550718, by rfl⟩ : syracuseStep 734291 = 1101437) B1101437
theorem B2798813 : Blo 323837 2798813 := bstep (se 3 (by rfl) ⟨524777, by rfl⟩ : syracuseStep 2798813 = 1049555) B1049555
theorem B734471 : Blo 323837 734471 := bstep (se 1 (by rfl) ⟨550853, by rfl⟩ : syracuseStep 734471 = 1101707) B1101707
theorem B6436205 : Blo 323837 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B734831 : Blo 323837 734831 := bstep (se 1 (by rfl) ⟨551123, by rfl⟩ : syracuseStep 734831 = 1102247) B1102247
theorem B1095929 : Blo 323837 1095929 := bstep (se 2 (by rfl) ⟨410973, by rfl⟩ : syracuseStep 1095929 = 821947) B821947
theorem B735695 : Blo 323837 735695 := bstep (se 1 (by rfl) ⟨551771, by rfl⟩ : syracuseStep 735695 = 1103543) B1103543
theorem B1096199 : Blo 323837 1096199 := bstep (se 1 (by rfl) ⟨822149, by rfl⟩ : syracuseStep 1096199 = 1644299) B1644299
theorem B735785 : Blo 323837 735785 := bstep (se 2 (by rfl) ⟨275919, by rfl⟩ : syracuseStep 735785 = 551839) B551839
theorem B670441 : Blo 323837 670441 := bstep (se 2 (by rfl) ⟨251415, by rfl⟩ : syracuseStep 670441 = 502831) B502831
theorem B703399 : Blo 323837 703399 := bstep (se 1 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 703399 = 1055099) B1055099
theorem B2636711 : Blo 323837 2636711 := bstep (se 1 (by rfl) ⟨1977533, by rfl⟩ : syracuseStep 2636711 = 3955067) B3955067
theorem B736361 : Blo 323837 736361 := bstep (se 2 (by rfl) ⟨276135, by rfl⟩ : syracuseStep 736361 = 552271) B552271
theorem B4209779 : Blo 323837 4209779 := bstep (se 1 (by rfl) ⟨3157334, by rfl⟩ : syracuseStep 4209779 = 6314669) B6314669
theorem B736487 : Blo 323837 736487 := bstep (se 1 (by rfl) ⟨552365, by rfl⟩ : syracuseStep 736487 = 1104731) B1104731
theorem B1195343 : Blo 323837 1195343 := bstep (se 1 (by rfl) ⟨896507, by rfl⟩ : syracuseStep 1195343 = 1793015) B1793015
theorem B1097279 : Blo 323837 1097279 := bstep (se 1 (by rfl) ⟨822959, by rfl⟩ : syracuseStep 1097279 = 1645919) B1645919
theorem B933439 : Blo 323837 933439 := bstep (se 1 (by rfl) ⟨700079, by rfl⟩ : syracuseStep 933439 = 1400159) B1400159
theorem B736991 : Blo 323837 736991 := bstep (se 1 (by rfl) ⟨552743, by rfl⟩ : syracuseStep 736991 = 1105487) B1105487
theorem B2473739 : Blo 323837 2473739 := bstep (se 1 (by rfl) ⟨1855304, by rfl⟩ : syracuseStep 2473739 = 3710609) B3710609
theorem B737063 : Blo 323837 737063 := bstep (se 1 (by rfl) ⟨552797, by rfl⟩ : syracuseStep 737063 = 1105595) B1105595
theorem B1097981 : Blo 323837 1097981 := bstep (se 3 (by rfl) ⟨205871, by rfl⟩ : syracuseStep 1097981 = 411743) B411743
theorem B2834785 : Blo 323837 2834785 := bstep (se 2 (by rfl) ⟨1063044, by rfl⟩ : syracuseStep 2834785 = 2126089) B2126089
theorem B1851821 : Blo 323837 1851821 := bstep (se 3 (by rfl) ⟨347216, by rfl⟩ : syracuseStep 1851821 = 694433) B694433
theorem B2998781 : Blo 323837 2998781 := bstep (se 3 (by rfl) ⟨562271, by rfl⟩ : syracuseStep 2998781 = 1124543) B1124543
theorem B26690147 : Blo 323837 26690147 := bstep (se 1 (by rfl) ⟨20017610, by rfl⟩ : syracuseStep 26690147 = 40035221) B40035221
theorem B1098521 : Blo 323837 1098521 := bstep (se 2 (by rfl) ⟨411945, by rfl⟩ : syracuseStep 1098521 = 823891) B823891
theorem B1098791 : Blo 323837 1098791 := bstep (se 1 (by rfl) ⟨824093, by rfl⟩ : syracuseStep 1098791 = 1648187) B1648187
theorem B1393787 : Blo 323837 1393787 := bstep (se 1 (by rfl) ⟨1045340, by rfl⟩ : syracuseStep 1393787 = 2090681) B2090681
theorem B476383 : Blo 323837 476383 := bstep (se 1 (by rfl) ⟨357287, by rfl⟩ : syracuseStep 476383 = 714575) B714575
theorem B2082145 : Blo 323837 2082145 := bstep (se 2 (by rfl) ⟨780804, by rfl⟩ : syracuseStep 2082145 = 1561609) B1561609
theorem B1230187 : Blo 323837 1230187 := bstep (se 1 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 1230187 = 1845281) B1845281
theorem B3720815 : Blo 323837 3720815 := bstep (se 1 (by rfl) ⟨2790611, by rfl⟩ : syracuseStep 3720815 = 5581223) B5581223
theorem B1558187 : Blo 323837 1558187 := bstep (se 1 (by rfl) ⟨1168640, by rfl⟩ : syracuseStep 1558187 = 2337281) B2337281
theorem B6244127 : Blo 323837 6244127 := bstep (se 1 (by rfl) ⟨4683095, by rfl⟩ : syracuseStep 6244127 = 9366191) B9366191
theorem B1099871 : Blo 323837 1099871 := bstep (se 1 (by rfl) ⟨824903, by rfl⟩ : syracuseStep 1099871 = 1649807) B1649807
theorem B1984733 : Blo 323837 1984733 := bstep (se 3 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 1984733 = 744275) B744275
theorem B3688739 : Blo 323837 3688739 := bstep (se 1 (by rfl) ⟨2766554, by rfl⟩ : syracuseStep 3688739 = 5533109) B5533109
theorem B1231463 : Blo 323837 1231463 := bstep (se 1 (by rfl) ⟨923597, by rfl⟩ : syracuseStep 1231463 = 1847195) B1847195
theorem B740407 : Blo 323837 740407 := bstep (se 1 (by rfl) ⟨555305, by rfl⟩ : syracuseStep 740407 = 1110611) B1110611
theorem B348143 : Blo 323837 348143 := bstep (se 1 (by rfl) ⟨261107, by rfl⟩ : syracuseStep 348143 = 522215) B522215
theorem B1232891 : Blo 323837 1232891 := bstep (se 1 (by rfl) ⟨924668, by rfl⟩ : syracuseStep 1232891 = 1849337) B1849337
theorem B3723731 : Blo 323837 3723731 := bstep (se 1 (by rfl) ⟨2792798, by rfl⟩ : syracuseStep 3723731 = 5585597) B5585597
theorem B1397357 : Blo 323837 1397357 := bstep (se 3 (by rfl) ⟨262004, by rfl⟩ : syracuseStep 1397357 = 524009) B524009
theorem B2479085 : Blo 323837 2479085 := bstep (se 3 (by rfl) ⟨464828, by rfl⟩ : syracuseStep 2479085 = 929657) B929657
theorem B5559353 : Blo 323837 5559353 := bstep (se 2 (by rfl) ⟨2084757, by rfl⟩ : syracuseStep 5559353 = 4169515) B4169515
theorem B1856627 : Blo 323837 1856627 := bstep (se 1 (by rfl) ⟨1392470, by rfl⟩ : syracuseStep 1856627 = 2784941) B2784941
theorem B1103003 : Blo 323837 1103003 := bstep (se 1 (by rfl) ⟨827252, by rfl⟩ : syracuseStep 1103003 = 1654505) B1654505
theorem B1234075 : Blo 323837 1234075 := bstep (se 1 (by rfl) ⟨925556, by rfl⟩ : syracuseStep 1234075 = 1851113) B1851113
theorem B547303 : Blo 323837 547303 := bstep (se 1 (by rfl) ⟨410477, by rfl⟩ : syracuseStep 547303 = 820955) B820955
theorem B1858085 : Blo 323837 1858085 := bstep (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) B348391
theorem B49109579 : Blo 323837 49109579 := bstep (se 1 (by rfl) ⟨36832184, by rfl⟩ : syracuseStep 49109579 = 73664369) B73664369
theorem B11819641 : Blo 323837 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B2481029 : Blo 323837 2481029 := bstep (se 4 (by rfl) ⟨232596, by rfl⟩ : syracuseStep 2481029 = 465193) B465193
theorem B2382851 : Blo 323837 2382851 := bstep (se 1 (by rfl) ⟨1787138, by rfl⟩ : syracuseStep 2382851 = 3574277) B3574277
theorem B548167 : Blo 323837 548167 := bstep (se 1 (by rfl) ⟨411125, by rfl⟩ : syracuseStep 548167 = 822251) B822251
theorem B2481515 : Blo 323837 2481515 := bstep (se 1 (by rfl) ⟨1861136, by rfl⟩ : syracuseStep 2481515 = 3722273) B3722273
theorem B548329 : Blo 323837 548329 := bstep (se 2 (by rfl) ⟨205623, by rfl⟩ : syracuseStep 548329 = 411247) B411247
theorem B2776943 : Blo 323837 2776943 := bstep (se 1 (by rfl) ⟨2082707, by rfl⟩ : syracuseStep 2776943 = 4165415) B4165415
theorem B549119 : Blo 323837 549119 := bstep (se 1 (by rfl) ⟨411839, by rfl⟩ : syracuseStep 549119 = 823679) B823679
theorem B1761697 : Blo 323837 1761697 := bstep (se 2 (by rfl) ⟨660636, by rfl⟩ : syracuseStep 1761697 = 1321273) B1321273
theorem B8872523 : Blo 323837 8872523 := bstep (se 1 (by rfl) ⟨6654392, by rfl⟩ : syracuseStep 8872523 = 13308785) B13308785
theorem B10576925 : Blo 323837 10576925 := bstep (se 3 (by rfl) ⟨1983173, by rfl⟩ : syracuseStep 10576925 = 3966347) B3966347
theorem B2483459 : Blo 323837 2483459 := bstep (se 1 (by rfl) ⟨1862594, by rfl⟩ : syracuseStep 2483459 = 3725189) B3725189
theorem B616187 : Blo 323837 616187 := bstep (se 1 (by rfl) ⟨462140, by rfl⟩ : syracuseStep 616187 = 924281) B924281
theorem B550847 : Blo 323837 550847 := bstep (se 1 (by rfl) ⟨413135, by rfl⟩ : syracuseStep 550847 = 826271) B826271
theorem B1861775 : Blo 323837 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B485867 : Blo 323837 485867 := bstep (se 1 (by rfl) ⟨364400, by rfl⟩ : syracuseStep 485867 = 728801) B728801
theorem B682553 : Blo 323837 682553 := bstep (se 2 (by rfl) ⟨255957, by rfl⟩ : syracuseStep 682553 = 511915) B511915
theorem B1174351 : Blo 323837 1174351 := bstep (se 1 (by rfl) ⟨880763, by rfl⟩ : syracuseStep 1174351 = 1761527) B1761527
theorem B486569 : Blo 323837 486569 := bstep (se 2 (by rfl) ⟨182463, by rfl⟩ : syracuseStep 486569 = 364927) B364927
theorem B3173855 : Blo 323837 3173855 := bstep (se 1 (by rfl) ⟨2380391, by rfl⟩ : syracuseStep 3173855 = 4760783) B4760783
theorem B486983 : Blo 323837 486983 := bstep (se 1 (by rfl) ⟨365237, by rfl⟩ : syracuseStep 486983 = 730475) B730475
theorem B1240667 : Blo 323837 1240667 := bstep (se 1 (by rfl) ⟨930500, by rfl⟩ : syracuseStep 1240667 = 1861001) B1861001
theorem B1568413 : Blo 323837 1568413 := bstep (se 3 (by rfl) ⟨294077, by rfl⟩ : syracuseStep 1568413 = 588155) B588155
theorem B487163 : Blo 323837 487163 := bstep (se 1 (by rfl) ⟨365372, by rfl⟩ : syracuseStep 487163 = 730745) B730745
theorem B1765115 : Blo 323837 1765115 := bstep (se 1 (by rfl) ⟨1323836, by rfl⟩ : syracuseStep 1765115 = 2647673) B2647673
theorem B10841951 : Blo 323837 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B552953 : Blo 323837 552953 := bstep (se 2 (by rfl) ⟨207357, by rfl⟩ : syracuseStep 552953 = 414715) B414715
theorem B520319 : Blo 323837 520319 := bstep (se 1 (by rfl) ⟨390239, by rfl⟩ : syracuseStep 520319 = 780479) B780479
theorem B1241351 : Blo 323837 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B553223 : Blo 323837 553223 := bstep (se 1 (by rfl) ⟨414917, by rfl⟩ : syracuseStep 553223 = 829835) B829835
theorem B323943 : Blo 323837 323943 := bstep (se 1 (by rfl) ⟨242957, by rfl⟩ : syracuseStep 323943 = 485915) B485915
theorem B323995 : Blo 323837 323995 := bstep (se 1 (by rfl) ⟨242996, by rfl⟩ : syracuseStep 323995 = 485993) B485993
theorem B487835 : Blo 323837 487835 := bstep (se 1 (by rfl) ⟨365876, by rfl⟩ : syracuseStep 487835 = 731753) B731753
theorem B783083 : Blo 323837 783083 := bstep (se 1 (by rfl) ⟨587312, by rfl⟩ : syracuseStep 783083 = 1174625) B1174625
theorem B324347 : Blo 323837 324347 := bstep (se 1 (by rfl) ⟨243260, by rfl⟩ : syracuseStep 324347 = 486521) B486521
theorem B1241851 : Blo 323837 1241851 := bstep (se 1 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 1241851 = 1862777) B1862777
theorem B324415 : Blo 323837 324415 := bstep (se 1 (by rfl) ⟨243311, by rfl⟩ : syracuseStep 324415 = 486623) B486623
theorem B488255 : Blo 323837 488255 := bstep (se 1 (by rfl) ⟨366191, by rfl⟩ : syracuseStep 488255 = 732383) B732383
theorem B324443 : Blo 323837 324443 := bstep (se 1 (by rfl) ⟨243332, by rfl⟩ : syracuseStep 324443 = 486665) B486665
theorem B3339139 : Blo 323837 3339139 := bstep (se 1 (by rfl) ⟨2504354, by rfl⟩ : syracuseStep 3339139 = 5008709) B5008709
theorem B1110941 : Blo 323837 1110941 := bstep (se 3 (by rfl) ⟨208301, by rfl⟩ : syracuseStep 1110941 = 416603) B416603
theorem B324511 : Blo 323837 324511 := bstep (se 1 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 324511 = 486767) B486767
theorem B488399 : Blo 323837 488399 := bstep (se 1 (by rfl) ⟨366299, by rfl⟩ : syracuseStep 488399 = 732599) B732599
theorem B324591 : Blo 323837 324591 := bstep (se 1 (by rfl) ⟨243443, by rfl⟩ : syracuseStep 324591 = 486887) B486887
theorem B488441 : Blo 323837 488441 := bstep (se 2 (by rfl) ⟨183165, by rfl⟩ : syracuseStep 488441 = 366331) B366331
theorem B7074809 : Blo 323837 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B488489 : Blo 323837 488489 := bstep (se 2 (by rfl) ⟨183183, by rfl⟩ : syracuseStep 488489 = 366367) B366367
theorem B324679 : Blo 323837 324679 := bstep (se 1 (by rfl) ⟨243509, by rfl⟩ : syracuseStep 324679 = 487019) B487019
theorem B488519 : Blo 323837 488519 := bstep (se 1 (by rfl) ⟨366389, by rfl⟩ : syracuseStep 488519 = 732779) B732779
theorem B324763 : Blo 323837 324763 := bstep (se 1 (by rfl) ⟨243572, by rfl⟩ : syracuseStep 324763 = 487145) B487145
theorem B1242323 : Blo 323837 1242323 := bstep (se 1 (by rfl) ⟨931742, by rfl⟩ : syracuseStep 1242323 = 1863485) B1863485
theorem B324859 : Blo 323837 324859 := bstep (se 1 (by rfl) ⟨243644, by rfl⟩ : syracuseStep 324859 = 487289) B487289
theorem B488699 : Blo 323837 488699 := bstep (se 1 (by rfl) ⟨366524, by rfl⟩ : syracuseStep 488699 = 733049) B733049
theorem B1963271 : Blo 323837 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B324927 : Blo 323837 324927 := bstep (se 1 (by rfl) ⟨243695, by rfl⟩ : syracuseStep 324927 = 487391) B487391
theorem B1570259 : Blo 323837 1570259 := bstep (se 1 (by rfl) ⟨1177694, by rfl⟩ : syracuseStep 1570259 = 2355389) B2355389
theorem B325095 : Blo 323837 325095 := bstep (se 1 (by rfl) ⟨243821, by rfl⟩ : syracuseStep 325095 = 487643) B487643
theorem B325103 : Blo 323837 325103 := bstep (se 1 (by rfl) ⟨243827, by rfl⟩ : syracuseStep 325103 = 487655) B487655
theorem B325211 : Blo 323837 325211 := bstep (se 1 (by rfl) ⟨243908, by rfl⟩ : syracuseStep 325211 = 487817) B487817
theorem B325275 : Blo 323837 325275 := bstep (se 1 (by rfl) ⟨243956, by rfl⟩ : syracuseStep 325275 = 487913) B487913
theorem B1570529 : Blo 323837 1570529 := bstep (se 2 (by rfl) ⟨588948, by rfl⟩ : syracuseStep 1570529 = 1177897) B1177897
theorem B325359 : Blo 323837 325359 := bstep (se 1 (by rfl) ⟨244019, by rfl⟩ : syracuseStep 325359 = 488039) B488039
theorem B325447 : Blo 323837 325447 := bstep (se 1 (by rfl) ⟨244085, by rfl⟩ : syracuseStep 325447 = 488171) B488171
theorem B325467 : Blo 323837 325467 := bstep (se 1 (by rfl) ⟨244100, by rfl⟩ : syracuseStep 325467 = 488201) B488201
theorem B325535 : Blo 323837 325535 := bstep (se 1 (by rfl) ⟨244151, by rfl⟩ : syracuseStep 325535 = 488303) B488303
theorem B325703 : Blo 323837 325703 := bstep (se 1 (by rfl) ⟨244277, by rfl⟩ : syracuseStep 325703 = 488555) B488555
theorem B620615 : Blo 323837 620615 := bstep (se 1 (by rfl) ⟨465461, by rfl⟩ : syracuseStep 620615 = 930923) B930923
theorem B325863 : Blo 323837 325863 := bstep (se 1 (by rfl) ⟨244397, by rfl⟩ : syracuseStep 325863 = 488795) B488795
theorem B326047 : Blo 323837 326047 := bstep (se 1 (by rfl) ⟨244535, by rfl⟩ : syracuseStep 326047 = 489071) B489071
theorem B326095 : Blo 323837 326095 := bstep (se 1 (by rfl) ⟨244571, by rfl⟩ : syracuseStep 326095 = 489143) B489143
theorem B489935 : Blo 323837 489935 := bstep (se 1 (by rfl) ⟨367451, by rfl⟩ : syracuseStep 489935 = 734903) B734903
theorem B326119 : Blo 323837 326119 := bstep (se 1 (by rfl) ⟨244589, by rfl⟩ : syracuseStep 326119 = 489179) B489179
theorem B490025 : Blo 323837 490025 := bstep (se 2 (by rfl) ⟨183759, by rfl⟩ : syracuseStep 490025 = 367519) B367519
theorem B784937 : Blo 323837 784937 := bstep (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) B588703
theorem B326235 : Blo 323837 326235 := bstep (se 1 (by rfl) ⟨244676, by rfl⟩ : syracuseStep 326235 = 489353) B489353
theorem B621199 : Blo 323837 621199 := bstep (se 1 (by rfl) ⟨465899, by rfl⟩ : syracuseStep 621199 = 931799) B931799
theorem B326303 : Blo 323837 326303 := bstep (se 1 (by rfl) ⟨244727, by rfl⟩ : syracuseStep 326303 = 489455) B489455
theorem B490217 : Blo 323837 490217 := bstep (se 2 (by rfl) ⟨183831, by rfl⟩ : syracuseStep 490217 = 367663) B367663
theorem B326471 : Blo 323837 326471 := bstep (se 1 (by rfl) ⟨244853, by rfl⟩ : syracuseStep 326471 = 489707) B489707
theorem B326511 : Blo 323837 326511 := bstep (se 1 (by rfl) ⟨244883, by rfl⟩ : syracuseStep 326511 = 489767) B489767
theorem B326567 : Blo 323837 326567 := bstep (se 1 (by rfl) ⟨244925, by rfl⟩ : syracuseStep 326567 = 489851) B489851
theorem B326747 : Blo 323837 326747 := bstep (se 1 (by rfl) ⟨245060, by rfl⟩ : syracuseStep 326747 = 490121) B490121
theorem B490601 : Blo 323837 490601 := bstep (se 2 (by rfl) ⟨183975, by rfl⟩ : syracuseStep 490601 = 367951) B367951
theorem B326863 : Blo 323837 326863 := bstep (se 1 (by rfl) ⟨245147, by rfl⟩ : syracuseStep 326863 = 490295) B490295
theorem B326887 : Blo 323837 326887 := bstep (se 1 (by rfl) ⟨245165, by rfl⟩ : syracuseStep 326887 = 490331) B490331
theorem B490727 : Blo 323837 490727 := bstep (se 1 (by rfl) ⟨368045, by rfl⟩ : syracuseStep 490727 = 736091) B736091
theorem B326983 : Blo 323837 326983 := bstep (se 1 (by rfl) ⟨245237, by rfl⟩ : syracuseStep 326983 = 490475) B490475
theorem B1244555 : Blo 323837 1244555 := bstep (se 1 (by rfl) ⟨933416, by rfl⟩ : syracuseStep 1244555 = 1866833) B1866833
theorem B327119 : Blo 323837 327119 := bstep (se 1 (by rfl) ⟨245339, by rfl⟩ : syracuseStep 327119 = 490679) B490679
theorem B327279 : Blo 323837 327279 := bstep (se 1 (by rfl) ⟨245459, by rfl⟩ : syracuseStep 327279 = 490919) B490919
theorem B327335 : Blo 323837 327335 := bstep (se 1 (by rfl) ⟨245501, by rfl⟩ : syracuseStep 327335 = 491003) B491003
theorem B622255 : Blo 323837 622255 := bstep (se 1 (by rfl) ⟨466691, by rfl⟩ : syracuseStep 622255 = 933383) B933383
theorem B491231 : Blo 323837 491231 := bstep (se 1 (by rfl) ⟨368423, by rfl⟩ : syracuseStep 491231 = 736847) B736847
theorem B327399 : Blo 323837 327399 := bstep (se 1 (by rfl) ⟨245549, by rfl⟩ : syracuseStep 327399 = 491099) B491099
theorem B491273 : Blo 323837 491273 := bstep (se 2 (by rfl) ⟨184227, by rfl⟩ : syracuseStep 491273 = 368455) B368455
theorem B327455 : Blo 323837 327455 := bstep (se 1 (by rfl) ⟨245591, by rfl⟩ : syracuseStep 327455 = 491183) B491183
theorem B327535 : Blo 323837 327535 := bstep (se 1 (by rfl) ⟨245651, by rfl⟩ : syracuseStep 327535 = 491303) B491303
theorem B327591 : Blo 323837 327591 := bstep (se 1 (by rfl) ⟨245693, by rfl⟩ : syracuseStep 327591 = 491387) B491387
theorem B327807 : Blo 323837 327807 := bstep (se 1 (by rfl) ⟨245855, by rfl⟩ : syracuseStep 327807 = 491711) B491711
theorem B1048889 : Blo 323837 1048889 := bstep (se 2 (by rfl) ⟨393333, by rfl⟩ : syracuseStep 1048889 = 786667) B786667
theorem B1999187 : Blo 323837 1999187 := bstep (se 1 (by rfl) ⟨1499390, by rfl⟩ : syracuseStep 1999187 = 2998781) B2998781
theorem B17793431 : Blo 323837 17793431 := bstep (se 1 (by rfl) ⟨13345073, by rfl⟩ : syracuseStep 17793431 = 26690147) B26690147
theorem B2097575 : Blo 323837 2097575 := bstep (se 1 (by rfl) ⟨1573181, by rfl⟩ : syracuseStep 2097575 = 3146363) B3146363
theorem B4162751 : Blo 323837 4162751 := bstep (se 1 (by rfl) ⟨3122063, by rfl⟩ : syracuseStep 4162751 = 6244127) B6244127
theorem B4588919 : Blo 323837 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B2459159 : Blo 323837 2459159 := bstep (se 1 (by rfl) ⟨1844369, by rfl⟩ : syracuseStep 2459159 = 3688739) B3688739
theorem B820975 : Blo 323837 820975 := bstep (se 1 (by rfl) ⟨615731, by rfl⟩ : syracuseStep 820975 = 1231463) B1231463
theorem B1640249 : Blo 323837 1640249 := bstep (se 2 (by rfl) ⟨615093, by rfl⟩ : syracuseStep 1640249 = 1230187) B1230187
theorem B1640411 : Blo 323837 1640411 := bstep (se 1 (by rfl) ⟨1230308, by rfl⟩ : syracuseStep 1640411 = 2460617) B2460617
theorem B821927 : Blo 323837 821927 := bstep (se 1 (by rfl) ⟨616445, by rfl⟩ : syracuseStep 821927 = 1232891) B1232891
theorem B2362193 : Blo 323837 2362193 := bstep (se 2 (by rfl) ⟨885822, by rfl⟩ : syracuseStep 2362193 = 1771645) B1771645
theorem B3706235 : Blo 323837 3706235 := bstep (se 1 (by rfl) ⟨2779676, by rfl⟩ : syracuseStep 3706235 = 5559353) B5559353
theorem B528095 : Blo 323837 528095 := bstep (se 1 (by rfl) ⟨396071, by rfl⟩ : syracuseStep 528095 = 792143) B792143
theorem B987209 : Blo 323837 987209 := bstep (se 2 (by rfl) ⟨370203, by rfl⟩ : syracuseStep 987209 = 740407) B740407
theorem B32739719 : Blo 323837 32739719 := bstep (se 1 (by rfl) ⟨24554789, by rfl⟩ : syracuseStep 32739719 = 49109579) B49109579
theorem B1643165 : Blo 323837 1643165 := bstep (se 3 (by rfl) ⟨308093, by rfl⟩ : syracuseStep 1643165 = 616187) B616187
theorem B33854453 : Blo 323837 33854453 := bstep (se 5 (by rfl) ⟨1586927, by rfl⟩ : syracuseStep 33854453 = 3173855) B3173855
theorem B3511457 : Blo 323837 3511457 := bstep (se 2 (by rfl) ⟨1316796, by rfl⟩ : syracuseStep 3511457 = 2633593) B2633593
theorem B660799 : Blo 323837 660799 := bstep (se 1 (by rfl) ⟨495599, by rfl⟩ : syracuseStep 660799 = 991199) B991199
theorem B923051 : Blo 323837 923051 := bstep (se 1 (by rfl) ⟨692288, by rfl⟩ : syracuseStep 923051 = 1384577) B1384577
theorem B366079 : Blo 323837 366079 := bstep (se 1 (by rfl) ⟨274559, by rfl⟩ : syracuseStep 366079 = 549119) B549119
theorem B7051283 : Blo 323837 7051283 := bstep (se 1 (by rfl) ⟨5288462, by rfl⟩ : syracuseStep 7051283 = 10576925) B10576925
theorem B9443465 : Blo 323837 9443465 := bstep (se 2 (by rfl) ⟨3541299, by rfl⟩ : syracuseStep 9443465 = 7082599) B7082599
theorem B367231 : Blo 323837 367231 := bstep (se 1 (by rfl) ⟨275423, by rfl⟩ : syracuseStep 367231 = 550847) B550847
theorem B465535 : Blo 323837 465535 := bstep (se 1 (by rfl) ⟨349151, by rfl⟩ : syracuseStep 465535 = 698303) B698303
theorem B2464505 : Blo 323837 2464505 := bstep (se 2 (by rfl) ⟨924189, by rfl⟩ : syracuseStep 2464505 = 1848379) B1848379
theorem B1645433 : Blo 323837 1645433 := bstep (se 2 (by rfl) ⟨617037, by rfl⟩ : syracuseStep 1645433 = 1234075) B1234075
theorem B924635 : Blo 323837 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B728747 : Blo 323837 728747 := bstep (se 1 (by rfl) ⟨546560, by rfl⟩ : syracuseStep 728747 = 1093121) B1093121
theorem B827111 : Blo 323837 827111 := bstep (se 1 (by rfl) ⟨620333, by rfl⟩ : syracuseStep 827111 = 1240667) B1240667
theorem B466663 : Blo 323837 466663 := bstep (se 1 (by rfl) ⟨349997, by rfl⟩ : syracuseStep 466663 = 699995) B699995
theorem B8921015 : Blo 323837 8921015 := bstep (se 1 (by rfl) ⟨6690761, by rfl⟩ : syracuseStep 8921015 = 13381523) B13381523
theorem B368635 : Blo 323837 368635 := bstep (se 1 (by rfl) ⟨276476, by rfl⟩ : syracuseStep 368635 = 552953) B552953
theorem B827567 : Blo 323837 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B368815 : Blo 323837 368815 := bstep (se 1 (by rfl) ⟨276611, by rfl⟩ : syracuseStep 368815 = 553223) B553223
theorem B729287 : Blo 323837 729287 := bstep (se 1 (by rfl) ⟨546965, by rfl⟩ : syracuseStep 729287 = 1093931) B1093931
theorem B729467 : Blo 323837 729467 := bstep (se 1 (by rfl) ⟨547100, by rfl⟩ : syracuseStep 729467 = 1094201) B1094201
theorem B1057151 : Blo 323837 1057151 := bstep (se 1 (by rfl) ⟨792863, by rfl⟩ : syracuseStep 1057151 = 1585727) B1585727
theorem B1385039 : Blo 323837 1385039 := bstep (se 1 (by rfl) ⟨1038779, by rfl⟩ : syracuseStep 1385039 = 2077559) B2077559
theorem B729737 : Blo 323837 729737 := bstep (se 2 (by rfl) ⟨273651, by rfl⟩ : syracuseStep 729737 = 547303) B547303
theorem B828215 : Blo 323837 828215 := bstep (se 1 (by rfl) ⟨621161, by rfl⟩ : syracuseStep 828215 = 1242323) B1242323
theorem B828265 : Blo 323837 828265 := bstep (se 2 (by rfl) ⟨310599, by rfl⟩ : syracuseStep 828265 = 621199) B621199
theorem B893921 : Blo 323837 893921 := bstep (se 2 (by rfl) ⟨335220, by rfl⟩ : syracuseStep 893921 = 670441) B670441
theorem B730619 : Blo 323837 730619 := bstep (se 1 (by rfl) ⟨547964, by rfl⟩ : syracuseStep 730619 = 1095929) B1095929
theorem B730799 : Blo 323837 730799 := bstep (se 1 (by rfl) ⟨548099, by rfl⟩ : syracuseStep 730799 = 1096199) B1096199
theorem B730889 : Blo 323837 730889 := bstep (se 2 (by rfl) ⟨274083, by rfl⟩ : syracuseStep 730889 = 548167) B548167
theorem B731105 : Blo 323837 731105 := bstep (se 2 (by rfl) ⟨274164, by rfl⟩ : syracuseStep 731105 = 548329) B548329
theorem B796895 : Blo 323837 796895 := bstep (se 1 (by rfl) ⟨597671, by rfl⟩ : syracuseStep 796895 = 1195343) B1195343
theorem B829673 : Blo 323837 829673 := bstep (se 2 (by rfl) ⟨311127, by rfl⟩ : syracuseStep 829673 = 622255) B622255
theorem B829703 : Blo 323837 829703 := bstep (se 1 (by rfl) ⟨622277, by rfl⟩ : syracuseStep 829703 = 1244555) B1244555
theorem B731519 : Blo 323837 731519 := bstep (se 1 (by rfl) ⟨548639, by rfl⟩ : syracuseStep 731519 = 1097279) B1097279
theorem B3713525 : Blo 323837 3713525 := bstep (se 5 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 3713525 = 348143) B348143
theorem B1649159 : Blo 323837 1649159 := bstep (se 1 (by rfl) ⟨1236869, by rfl⟩ : syracuseStep 1649159 = 2473739) B2473739
theorem B4303469 : Blo 323837 4303469 := bstep (se 3 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 4303469 = 1613801) B1613801
theorem B731987 : Blo 323837 731987 := bstep (se 1 (by rfl) ⟨548990, by rfl⟩ : syracuseStep 731987 = 1097981) B1097981
theorem B2010017 : Blo 323837 2010017 := bstep (se 2 (by rfl) ⟨753756, by rfl⟩ : syracuseStep 2010017 = 1507513) B1507513
theorem B3779713 : Blo 323837 3779713 := bstep (se 2 (by rfl) ⟨1417392, by rfl⟩ : syracuseStep 3779713 = 2834785) B2834785
theorem B732347 : Blo 323837 732347 := bstep (se 1 (by rfl) ⟨549260, by rfl⟩ : syracuseStep 732347 = 1098521) B1098521
theorem B732527 : Blo 323837 732527 := bstep (se 1 (by rfl) ⟨549395, by rfl⟩ : syracuseStep 732527 = 1098791) B1098791
theorem B929191 : Blo 323837 929191 := bstep (se 1 (by rfl) ⟨696893, by rfl⟩ : syracuseStep 929191 = 1393787) B1393787
theorem B733247 : Blo 323837 733247 := bstep (se 1 (by rfl) ⟨549935, by rfl⟩ : syracuseStep 733247 = 1099871) B1099871
theorem B1093715 : Blo 323837 1093715 := bstep (se 1 (by rfl) ⟨820286, by rfl⟩ : syracuseStep 1093715 = 1640573) B1640573
theorem B1323155 : Blo 323837 1323155 := bstep (se 1 (by rfl) ⟨992366, by rfl⟩ : syracuseStep 1323155 = 1984733) B1984733
theorem B635177 : Blo 323837 635177 := bstep (se 2 (by rfl) ⟨238191, by rfl⟩ : syracuseStep 635177 = 476383) B476383
theorem B8107451 : Blo 323837 8107451 := bstep (se 1 (by rfl) ⟨6080588, by rfl⟩ : syracuseStep 8107451 = 12161177) B12161177
theorem B931571 : Blo 323837 931571 := bstep (se 1 (by rfl) ⟨698678, by rfl⟩ : syracuseStep 931571 = 1397357) B1397357
theorem B1652723 : Blo 323837 1652723 := bstep (se 1 (by rfl) ⟨1239542, by rfl⟩ : syracuseStep 1652723 = 2479085) B2479085
theorem B735335 : Blo 323837 735335 := bstep (se 1 (by rfl) ⟨551501, by rfl⟩ : syracuseStep 735335 = 1103003) B1103003
theorem B1751969 : Blo 323837 1751969 := bstep (se 2 (by rfl) ⟨656988, by rfl⟩ : syracuseStep 1751969 = 1313977) B1313977
theorem B1654019 : Blo 323837 1654019 := bstep (se 1 (by rfl) ⟨1240514, by rfl⟩ : syracuseStep 1654019 = 2481029) B2481029
theorem B1588567 : Blo 323837 1588567 := bstep (se 1 (by rfl) ⟨1191425, by rfl⟩ : syracuseStep 1588567 = 2382851) B2382851
theorem B1654343 : Blo 323837 1654343 := bstep (se 1 (by rfl) ⟨1240757, by rfl⟩ : syracuseStep 1654343 = 2481515) B2481515
theorem B1851295 : Blo 323837 1851295 := bstep (se 1 (by rfl) ⟨1388471, by rfl⟩ : syracuseStep 1851295 = 2776943) B2776943
theorem B5915015 : Blo 323837 5915015 := bstep (se 1 (by rfl) ⟨4436261, by rfl⟩ : syracuseStep 5915015 = 8872523) B8872523
theorem B442847 : Blo 323837 442847 := bstep (se 1 (by rfl) ⟨332135, by rfl⟩ : syracuseStep 442847 = 664271) B664271
theorem B1655639 : Blo 323837 1655639 := bstep (se 1 (by rfl) ⟨1241729, by rfl⟩ : syracuseStep 1655639 = 2483459) B2483459
theorem B4506553 : Blo 323837 4506553 := bstep (se 2 (by rfl) ⟨1689957, by rfl⟩ : syracuseStep 4506553 = 3379915) B3379915
theorem B1655801 : Blo 323837 1655801 := bstep (se 2 (by rfl) ⟨620925, by rfl⟩ : syracuseStep 1655801 = 1241851) B1241851
theorem B1820141 : Blo 323837 1820141 := bstep (se 3 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 1820141 = 682553) B682553
theorem B7227967 : Blo 323837 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B1559263 : Blo 323837 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B346879 : Blo 323837 346879 := bstep (se 1 (by rfl) ⟨260159, by rfl⟩ : syracuseStep 346879 = 520319) B520319
theorem B1100627 : Blo 323837 1100627 := bstep (se 1 (by rfl) ⟨825470, by rfl⟩ : syracuseStep 1100627 = 1650941) B1650941
theorem B11226077 : Blo 323837 11226077 := bstep (se 3 (by rfl) ⟨2104889, by rfl⟩ : syracuseStep 11226077 = 4209779) B4209779
theorem B1231919 : Blo 323837 1231919 := bstep (se 1 (by rfl) ⟨923939, by rfl⟩ : syracuseStep 1231919 = 1847879) B1847879
theorem B5950687 : Blo 323837 5950687 := bstep (se 1 (by rfl) ⟨4463015, by rfl⟩ : syracuseStep 5950687 = 8926031) B8926031
theorem B740627 : Blo 323837 740627 := bstep (se 1 (by rfl) ⟨555470, by rfl⟩ : syracuseStep 740627 = 1110941) B1110941
theorem B1101167 : Blo 323837 1101167 := bstep (se 1 (by rfl) ⟨825875, by rfl⟩ : syracuseStep 1101167 = 1651751) B1651751
theorem B937865 : Blo 323837 937865 := bstep (se 2 (by rfl) ⟨351699, by rfl⟩ : syracuseStep 937865 = 703399) B703399
theorem B413743 : Blo 323837 413743 := bstep (se 1 (by rfl) ⟨310307, by rfl⟩ : syracuseStep 413743 = 620615) B620615
theorem B1757807 : Blo 323837 1757807 := bstep (se 1 (by rfl) ⟨1318355, by rfl⟩ : syracuseStep 1757807 = 2636711) B2636711
theorem B1234547 : Blo 323837 1234547 := bstep (se 1 (by rfl) ⟨925910, by rfl⟩ : syracuseStep 1234547 = 1851821) B1851821
theorem B2348929 : Blo 323837 2348929 := bstep (se 2 (by rfl) ⟨880848, by rfl⟩ : syracuseStep 2348929 = 1761697) B1761697
theorem B2480543 : Blo 323837 2480543 := bstep (se 1 (by rfl) ⟨1860407, by rfl⟩ : syracuseStep 2480543 = 3720815) B3720815
theorem B1038791 : Blo 323837 1038791 := bstep (se 1 (by rfl) ⟨779093, by rfl⟩ : syracuseStep 1038791 = 1558187) B1558187
theorem B2776193 : Blo 323837 2776193 := bstep (se 2 (by rfl) ⟨1041072, by rfl⟩ : syracuseStep 2776193 = 2082145) B2082145
theorem B5594345 : Blo 323837 5594345 := bstep (se 2 (by rfl) ⟨2097879, by rfl⟩ : syracuseStep 5594345 = 4195759) B4195759
theorem B1106081 : Blo 323837 1106081 := bstep (se 2 (by rfl) ⟨414780, by rfl⟩ : syracuseStep 1106081 = 829561) B829561
theorem B2482487 : Blo 323837 2482487 := bstep (se 1 (by rfl) ⟨1861865, by rfl⟩ : syracuseStep 2482487 = 3723731) B3723731
theorem B1860317 : Blo 323837 1860317 := bstep (se 3 (by rfl) ⟨348809, by rfl⟩ : syracuseStep 1860317 = 697619) B697619
theorem B1237751 : Blo 323837 1237751 := bstep (se 1 (by rfl) ⟨928313, by rfl⟩ : syracuseStep 1237751 = 1856627) B1856627
theorem B1565801 : Blo 323837 1565801 := bstep (se 2 (by rfl) ⟨587175, by rfl⟩ : syracuseStep 1565801 = 1174351) B1174351
theorem B1008865 : Blo 323837 1008865 := bstep (se 2 (by rfl) ⟨378324, by rfl⟩ : syracuseStep 1008865 = 756649) B756649
theorem B4154753 : Blo 323837 4154753 := bstep (se 2 (by rfl) ⟨1558032, by rfl⟩ : syracuseStep 4154753 = 3116065) B3116065
theorem B1238723 : Blo 323837 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B2091217 : Blo 323837 2091217 := bstep (se 2 (by rfl) ⟨784206, by rfl⟩ : syracuseStep 2091217 = 1568413) B1568413
theorem B5007595 : Blo 323837 5007595 := bstep (se 1 (by rfl) ⟨3755696, by rfl⟩ : syracuseStep 5007595 = 7511393) B7511393
theorem B1993079 : Blo 323837 1993079 := bstep (se 1 (by rfl) ⟨1494809, by rfl⟩ : syracuseStep 1993079 = 2989619) B2989619
theorem B485801 : Blo 323837 485801 := bstep (se 2 (by rfl) ⟨182175, by rfl⟩ : syracuseStep 485801 = 364351) B364351
theorem B2124427 : Blo 323837 2124427 := bstep (se 1 (by rfl) ⟨1593320, by rfl⟩ : syracuseStep 2124427 = 3186641) B3186641
theorem B486185 : Blo 323837 486185 := bstep (se 2 (by rfl) ⟨182319, by rfl⟩ : syracuseStep 486185 = 364639) B364639
theorem B3697487 : Blo 323837 3697487 := bstep (se 1 (by rfl) ⟨2773115, by rfl⟩ : syracuseStep 3697487 = 5546231) B5546231
theorem B486395 : Blo 323837 486395 := bstep (se 1 (by rfl) ⟨364796, by rfl⟩ : syracuseStep 486395 = 729593) B729593
theorem B486455 : Blo 323837 486455 := bstep (se 1 (by rfl) ⟨364841, by rfl⟩ : syracuseStep 486455 = 729683) B729683
theorem B486575 : Blo 323837 486575 := bstep (se 1 (by rfl) ⟨364931, by rfl⟩ : syracuseStep 486575 = 729863) B729863
theorem B486635 : Blo 323837 486635 := bstep (se 1 (by rfl) ⟨364976, by rfl⟩ : syracuseStep 486635 = 729953) B729953
theorem B8580809 : Blo 323837 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B4452185 : Blo 323837 4452185 := bstep (se 2 (by rfl) ⟨1669569, by rfl⟩ : syracuseStep 4452185 = 3339139) B3339139
theorem B487295 : Blo 323837 487295 := bstep (se 1 (by rfl) ⟨365471, by rfl⟩ : syracuseStep 487295 = 730943) B730943
theorem B618367 : Blo 323837 618367 := bstep (se 1 (by rfl) ⟨463775, by rfl⟩ : syracuseStep 618367 = 927551) B927551
theorem B2977681 : Blo 323837 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B1241183 : Blo 323837 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B2093165 : Blo 323837 2093165 := bstep (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) B784937
theorem B487631 : Blo 323837 487631 := bstep (se 1 (by rfl) ⟨365723, by rfl⟩ : syracuseStep 487631 = 731447) B731447
theorem B323911 : Blo 323837 323911 := bstep (se 1 (by rfl) ⟨242933, by rfl⟩ : syracuseStep 323911 = 485867) B485867
theorem B487751 : Blo 323837 487751 := bstep (se 1 (by rfl) ⟨365813, by rfl⟩ : syracuseStep 487751 = 731627) B731627
theorem B1405601 : Blo 323837 1405601 := bstep (se 2 (by rfl) ⟨527100, by rfl⟩ : syracuseStep 1405601 = 1054201) B1054201
theorem B324379 : Blo 323837 324379 := bstep (se 1 (by rfl) ⟨243284, by rfl⟩ : syracuseStep 324379 = 486569) B486569
theorem B488219 : Blo 323837 488219 := bstep (se 1 (by rfl) ⟨366164, by rfl⟩ : syracuseStep 488219 = 732329) B732329
theorem B324655 : Blo 323837 324655 := bstep (se 1 (by rfl) ⟨243491, by rfl⟩ : syracuseStep 324655 = 486983) B486983
theorem B488495 : Blo 323837 488495 := bstep (se 1 (by rfl) ⟨366371, by rfl⟩ : syracuseStep 488495 = 732743) B732743
theorem B488543 : Blo 323837 488543 := bstep (se 1 (by rfl) ⟨366407, by rfl⟩ : syracuseStep 488543 = 732815) B732815
theorem B488603 : Blo 323837 488603 := bstep (se 1 (by rfl) ⟨366452, by rfl⟩ : syracuseStep 488603 = 732905) B732905
theorem B324775 : Blo 323837 324775 := bstep (se 1 (by rfl) ⟨243581, by rfl⟩ : syracuseStep 324775 = 487163) B487163
theorem B488615 : Blo 323837 488615 := bstep (se 1 (by rfl) ⟨366461, by rfl⟩ : syracuseStep 488615 = 732923) B732923
theorem B1176743 : Blo 323837 1176743 := bstep (se 1 (by rfl) ⟨882557, by rfl⟩ : syracuseStep 1176743 = 1765115) B1765115
theorem B325223 : Blo 323837 325223 := bstep (se 1 (by rfl) ⟨243917, by rfl⟩ : syracuseStep 325223 = 487835) B487835
theorem B522055 : Blo 323837 522055 := bstep (se 1 (by rfl) ⟨391541, by rfl⟩ : syracuseStep 522055 = 783083) B783083
theorem B489287 : Blo 323837 489287 := bstep (se 1 (by rfl) ⟨366965, by rfl⟩ : syracuseStep 489287 = 733931) B733931
theorem B325503 : Blo 323837 325503 := bstep (se 1 (by rfl) ⟨244127, by rfl⟩ : syracuseStep 325503 = 488255) B488255
theorem B3504019 : Blo 323837 3504019 := bstep (se 1 (by rfl) ⟨2628014, by rfl⟩ : syracuseStep 3504019 = 5256029) B5256029
theorem B325599 : Blo 323837 325599 := bstep (se 1 (by rfl) ⟨244199, by rfl⟩ : syracuseStep 325599 = 488399) B488399
theorem B325627 : Blo 323837 325627 := bstep (se 1 (by rfl) ⟨244220, by rfl⟩ : syracuseStep 325627 = 488441) B488441
theorem B489467 : Blo 323837 489467 := bstep (se 1 (by rfl) ⟨367100, by rfl⟩ : syracuseStep 489467 = 734201) B734201
theorem B4716539 : Blo 323837 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B325659 : Blo 323837 325659 := bstep (se 1 (by rfl) ⟨244244, by rfl⟩ : syracuseStep 325659 = 488489) B488489
theorem B325679 : Blo 323837 325679 := bstep (se 1 (by rfl) ⟨244259, by rfl⟩ : syracuseStep 325679 = 488519) B488519
theorem B489527 : Blo 323837 489527 := bstep (se 1 (by rfl) ⟨367145, by rfl⟩ : syracuseStep 489527 = 734291) B734291
theorem B489593 : Blo 323837 489593 := bstep (se 2 (by rfl) ⟨183597, by rfl⟩ : syracuseStep 489593 = 367195) B367195
theorem B1865875 : Blo 323837 1865875 := bstep (se 1 (by rfl) ⟨1399406, by rfl⟩ : syracuseStep 1865875 = 2798813) B2798813
theorem B15759521 : Blo 323837 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B325799 : Blo 323837 325799 := bstep (se 1 (by rfl) ⟨244349, by rfl⟩ : syracuseStep 325799 = 488699) B488699
theorem B489647 : Blo 323837 489647 := bstep (se 1 (by rfl) ⟨367235, by rfl⟩ : syracuseStep 489647 = 734471) B734471
theorem B1308847 : Blo 323837 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B4290803 : Blo 323837 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B1046839 : Blo 323837 1046839 := bstep (se 1 (by rfl) ⟨785129, by rfl⟩ : syracuseStep 1046839 = 1570259) B1570259
theorem B489887 : Blo 323837 489887 := bstep (se 1 (by rfl) ⟨367415, by rfl⟩ : syracuseStep 489887 = 734831) B734831
theorem B2488805 : Blo 323837 2488805 := bstep (se 4 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 2488805 = 466651) B466651
theorem B1047019 : Blo 323837 1047019 := bstep (se 1 (by rfl) ⟨785264, by rfl⟩ : syracuseStep 1047019 = 1570529) B1570529
theorem B489977 : Blo 323837 489977 := bstep (se 2 (by rfl) ⟨183741, by rfl⟩ : syracuseStep 489977 = 367483) B367483
theorem B326623 : Blo 323837 326623 := bstep (se 1 (by rfl) ⟨244967, by rfl⟩ : syracuseStep 326623 = 489935) B489935
theorem B490463 : Blo 323837 490463 := bstep (se 1 (by rfl) ⟨367847, by rfl⟩ : syracuseStep 490463 = 735695) B735695
theorem B326683 : Blo 323837 326683 := bstep (se 1 (by rfl) ⟨245012, by rfl⟩ : syracuseStep 326683 = 490025) B490025
theorem B490523 : Blo 323837 490523 := bstep (se 1 (by rfl) ⟨367892, by rfl⟩ : syracuseStep 490523 = 735785) B735785
theorem B3701861 : Blo 323837 3701861 := bstep (se 4 (by rfl) ⟨347049, by rfl⟩ : syracuseStep 3701861 = 694099) B694099
theorem B326811 : Blo 323837 326811 := bstep (se 1 (by rfl) ⟨245108, by rfl⟩ : syracuseStep 326811 = 490217) B490217
theorem B327067 : Blo 323837 327067 := bstep (se 1 (by rfl) ⟨245300, by rfl⟩ : syracuseStep 327067 = 490601) B490601
theorem B490907 : Blo 323837 490907 := bstep (se 1 (by rfl) ⟨368180, by rfl⟩ : syracuseStep 490907 = 736361) B736361
theorem B1244585 : Blo 323837 1244585 := bstep (se 2 (by rfl) ⟨466719, by rfl⟩ : syracuseStep 1244585 = 933439) B933439
theorem B490985 : Blo 323837 490985 := bstep (se 2 (by rfl) ⟨184119, by rfl⟩ : syracuseStep 490985 = 368239) B368239
theorem B327151 : Blo 323837 327151 := bstep (se 1 (by rfl) ⟨245363, by rfl⟩ : syracuseStep 327151 = 490727) B490727
theorem B490991 : Blo 323837 490991 := bstep (se 1 (by rfl) ⟨368243, by rfl⟩ : syracuseStep 490991 = 736487) B736487
theorem B491129 : Blo 323837 491129 := bstep (se 2 (by rfl) ⟨184173, by rfl⟩ : syracuseStep 491129 = 368347) B368347
theorem B327487 : Blo 323837 327487 := bstep (se 1 (by rfl) ⟨245615, by rfl⟩ : syracuseStep 327487 = 491231) B491231
theorem B491327 : Blo 323837 491327 := bstep (se 1 (by rfl) ⟨368495, by rfl⟩ : syracuseStep 491327 = 736991) B736991
theorem B327515 : Blo 323837 327515 := bstep (se 1 (by rfl) ⟨245636, by rfl⟩ : syracuseStep 327515 = 491273) B491273
theorem B491375 : Blo 323837 491375 := bstep (se 1 (by rfl) ⟨368531, by rfl⟩ : syracuseStep 491375 = 737063) B737063
theorem B491753 : Blo 323837 491753 := bstep (se 2 (by rfl) ⟨184407, by rfl⟩ : syracuseStep 491753 = 368815) B368815
theorem B11862287 : Blo 323837 11862287 := bstep (se 1 (by rfl) ⟨8896715, by rfl⟩ : syracuseStep 11862287 = 17793431) B17793431
theorem B1213427 : Blo 323837 1213427 := bstep (se 1 (by rfl) ⟨910070, by rfl⟩ : syracuseStep 1213427 = 1820141) B1820141
theorem B1639439 : Blo 323837 1639439 := bstep (se 1 (by rfl) ⟨1229579, by rfl⟩ : syracuseStep 1639439 = 2459159) B2459159
theorem B1180925 : Blo 323837 1180925 := bstep (se 3 (by rfl) ⟨221423, by rfl⟩ : syracuseStep 1180925 = 442847) B442847
theorem B1574795 : Blo 323837 1574795 := bstep (se 1 (by rfl) ⟨1181096, by rfl⟩ : syracuseStep 1574795 = 2362193) B2362193
theorem B821279 : Blo 323837 821279 := bstep (se 1 (by rfl) ⟨615959, by rfl⟩ : syracuseStep 821279 = 1231919) B1231919
theorem B493751 : Blo 323837 493751 := bstep (se 1 (by rfl) ⟨370313, by rfl⟩ : syracuseStep 493751 = 740627) B740627
theorem B625243 : Blo 323837 625243 := bstep (se 1 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 625243 = 937865) B937865
theorem B658139 : Blo 323837 658139 := bstep (se 1 (by rfl) ⟨493604, by rfl⟩ : syracuseStep 658139 = 987209) B987209
theorem B2788289 : Blo 323837 2788289 := bstep (se 2 (by rfl) ⟨1045608, by rfl⟩ : syracuseStep 2788289 = 2091217) B2091217
theorem B9637289 : Blo 323837 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B462505 : Blo 323837 462505 := bstep (se 2 (by rfl) ⟨173439, by rfl⟩ : syracuseStep 462505 = 346879) B346879
theorem B823031 : Blo 323837 823031 := bstep (se 1 (by rfl) ⟨617273, by rfl⟩ : syracuseStep 823031 = 1234547) B1234547
theorem B6295643 : Blo 323837 6295643 := bstep (se 1 (by rfl) ⟨4721732, by rfl⟩ : syracuseStep 6295643 = 9443465) B9443465
theorem B7934249 : Blo 323837 7934249 := bstep (se 2 (by rfl) ⟨2975343, by rfl⟩ : syracuseStep 7934249 = 5950687) B5950687
theorem B1643003 : Blo 323837 1643003 := bstep (se 1 (by rfl) ⟨1232252, by rfl⟩ : syracuseStep 1643003 = 2464505) B2464505
theorem B824489 : Blo 323837 824489 := bstep (se 2 (by rfl) ⟨309183, by rfl⟩ : syracuseStep 824489 = 618367) B618367
theorem B3970241 : Blo 323837 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B923359 : Blo 323837 923359 := bstep (se 1 (by rfl) ⟨692519, by rfl⟩ : syracuseStep 923359 = 1385039) B1385039
theorem B825167 : Blo 323837 825167 := bstep (se 1 (by rfl) ⟨618875, by rfl⟩ : syracuseStep 825167 = 1237751) B1237751
theorem B20158469 : Blo 323837 20158469 := bstep (se 4 (by rfl) ⟨1889856, by rfl⟩ : syracuseStep 20158469 = 3779713) B3779713
theorem B825815 : Blo 323837 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B5380613 : Blo 323837 5380613 := bstep (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) B1008865
theorem B531263 : Blo 323837 531263 := bstep (se 1 (by rfl) ⟨398447, by rfl⟩ : syracuseStep 531263 = 796895) B796895
theorem B2464991 : Blo 323837 2464991 := bstep (se 1 (by rfl) ⟨1848743, by rfl⟩ : syracuseStep 2464991 = 3697487) B3697487
theorem B729143 : Blo 323837 729143 := bstep (se 1 (by rfl) ⟨546857, by rfl⟩ : syracuseStep 729143 = 1093715) B1093715
theorem B827455 : Blo 323837 827455 := bstep (se 1 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 827455 = 1241183) B1241183
theorem B1745129 : Blo 323837 1745129 := bstep (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) B1308847
theorem B2860535 : Blo 323837 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B2467907 : Blo 323837 2467907 := bstep (se 1 (by rfl) ⟨1850930, by rfl⟩ : syracuseStep 2467907 = 3701861) B3701861
theorem B11872493 : Blo 323837 11872493 := bstep (se 3 (by rfl) ⟨2226092, by rfl⟩ : syracuseStep 11872493 = 4452185) B4452185
theorem B829723 : Blo 323837 829723 := bstep (se 1 (by rfl) ⟨622292, by rfl⟩ : syracuseStep 829723 = 1244585) B1244585
theorem B2468393 : Blo 323837 2468393 := bstep (se 2 (by rfl) ⟨925647, by rfl⟩ : syracuseStep 2468393 = 1851295) B1851295
theorem B3943343 : Blo 323837 3943343 := bstep (se 1 (by rfl) ⟨2957507, by rfl⟩ : syracuseStep 3943343 = 5915015) B5915015
theorem B2797037 : Blo 323837 2797037 := bstep (se 3 (by rfl) ⟨524444, by rfl⟩ : syracuseStep 2797037 = 1048889) B1048889
theorem B3059279 : Blo 323837 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B1093499 : Blo 323837 1093499 := bstep (se 1 (by rfl) ⟨820124, by rfl⟩ : syracuseStep 1093499 = 1640249) B1640249
theorem B6008737 : Blo 323837 6008737 := bstep (se 2 (by rfl) ⟨2253276, by rfl⟩ : syracuseStep 6008737 = 4506553) B4506553
theorem B1093607 : Blo 323837 1093607 := bstep (se 1 (by rfl) ⟨820205, by rfl⟩ : syracuseStep 1093607 = 1640411) B1640411
theorem B733751 : Blo 323837 733751 := bstep (se 1 (by rfl) ⟨550313, by rfl⟩ : syracuseStep 733751 = 1100627) B1100627
theorem B7484051 : Blo 323837 7484051 := bstep (se 1 (by rfl) ⟨5613038, by rfl⟩ : syracuseStep 7484051 = 11226077) B11226077
theorem B734111 : Blo 323837 734111 := bstep (se 1 (by rfl) ⟨550583, by rfl⟩ : syracuseStep 734111 = 1101167) B1101167
theorem B2470823 : Blo 323837 2470823 := bstep (se 1 (by rfl) ⟨1853117, by rfl⟩ : syracuseStep 2470823 = 3706235) B3706235
theorem B1094633 : Blo 323837 1094633 := bstep (se 2 (by rfl) ⟨410487, by rfl⟩ : syracuseStep 1094633 = 820975) B820975
theorem B1095443 : Blo 323837 1095443 := bstep (se 1 (by rfl) ⟨821582, by rfl⟩ : syracuseStep 1095443 = 1643165) B1643165
theorem B2340971 : Blo 323837 2340971 := bstep (se 1 (by rfl) ⟨1755728, by rfl⟩ : syracuseStep 2340971 = 3511457) B3511457
theorem B2832569 : Blo 323837 2832569 := bstep (se 2 (by rfl) ⟨1062213, by rfl⟩ : syracuseStep 2832569 = 2124427) B2124427
theorem B2079017 : Blo 323837 2079017 := bstep (se 2 (by rfl) ⟨779631, by rfl⟩ : syracuseStep 2079017 = 1559263) B1559263
theorem B4700855 : Blo 323837 4700855 := bstep (se 1 (by rfl) ⟨3525641, by rfl⟩ : syracuseStep 4700855 = 7051283) B7051283
theorem B349223669 : Blo 323837 349223669 := bstep (se 5 (by rfl) ⟨16369859, by rfl⟩ : syracuseStep 349223669 = 32739719) B32739719
theorem B1653695 : Blo 323837 1653695 := bstep (se 1 (by rfl) ⟨1240271, by rfl⟩ : syracuseStep 1653695 = 2480543) B2480543
theorem B1096955 : Blo 323837 1096955 := bstep (se 1 (by rfl) ⟨822716, by rfl⟩ : syracuseStep 1096955 = 1645433) B1645433
theorem B1850795 : Blo 323837 1850795 := bstep (se 1 (by rfl) ⟨1388096, by rfl⟩ : syracuseStep 1850795 = 2776193) B2776193
theorem B5947343 : Blo 323837 5947343 := bstep (se 1 (by rfl) ⟨4460507, by rfl⟩ : syracuseStep 5947343 = 8921015) B8921015
theorem B737387 : Blo 323837 737387 := bstep (se 1 (by rfl) ⟨553040, by rfl⟩ : syracuseStep 737387 = 1106081) B1106081
theorem B1654991 : Blo 323837 1654991 := bstep (se 1 (by rfl) ⟨1241243, by rfl⟩ : syracuseStep 1654991 = 2482487) B2482487
theorem B704767 : Blo 323837 704767 := bstep (se 1 (by rfl) ⟨528575, by rfl⟩ : syracuseStep 704767 = 1057151) B1057151
theorem B2769835 : Blo 323837 2769835 := bstep (se 1 (by rfl) ⟨2077376, by rfl⟩ : syracuseStep 2769835 = 4154753) B4154753
theorem B2770109 : Blo 323837 2770109 := bstep (se 3 (by rfl) ⟨519395, by rfl⟩ : syracuseStep 2770109 = 1038791) B1038791
theorem B1328719 : Blo 323837 1328719 := bstep (se 1 (by rfl) ⟨996539, by rfl⟩ : syracuseStep 1328719 = 1993079) B1993079
theorem B2475683 : Blo 323837 2475683 := bstep (se 1 (by rfl) ⟨1856762, by rfl⟩ : syracuseStep 2475683 = 3713525) B3713525
theorem B1099439 : Blo 323837 1099439 := bstep (se 1 (by rfl) ⟨824579, by rfl⟩ : syracuseStep 1099439 = 1649159) B1649159
theorem B2868979 : Blo 323837 2868979 := bstep (se 1 (by rfl) ⟨2151734, by rfl⟩ : syracuseStep 2868979 = 4303469) B4303469
theorem B5720539 : Blo 323837 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B3131905 : Blo 323837 3131905 := bstep (se 2 (by rfl) ⟨1174464, by rfl⟩ : syracuseStep 3131905 = 2348929) B2348929
theorem B4672025 : Blo 323837 4672025 := bstep (se 2 (by rfl) ⟨1752009, by rfl⟩ : syracuseStep 4672025 = 3504019) B3504019
theorem B1395443 : Blo 323837 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B1395785 : Blo 323837 1395785 := bstep (se 2 (by rfl) ⟨523419, by rfl⟩ : syracuseStep 1395785 = 1046839) B1046839
theorem B937067 : Blo 323837 937067 := bstep (se 1 (by rfl) ⟨702800, by rfl⟩ : syracuseStep 937067 = 1405601) B1405601
theorem B1396025 : Blo 323837 1396025 := bstep (se 2 (by rfl) ⟨523509, by rfl⟩ : syracuseStep 1396025 = 1047019) B1047019
theorem B1101815 : Blo 323837 1101815 := bstep (se 1 (by rfl) ⟨826361, by rfl⟩ : syracuseStep 1101815 = 1652723) B1652723
theorem B10506347 : Blo 323837 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B1659203 : Blo 323837 1659203 := bstep (se 1 (by rfl) ⟨1244402, by rfl⟩ : syracuseStep 1659203 = 2488805) B2488805
theorem B2118089 : Blo 323837 2118089 := bstep (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) B1588567
theorem B1167979 : Blo 323837 1167979 := bstep (se 1 (by rfl) ⟨875984, by rfl⟩ : syracuseStep 1167979 = 1751969) B1751969
theorem B1102679 : Blo 323837 1102679 := bstep (se 1 (by rfl) ⟨827009, by rfl⟩ : syracuseStep 1102679 = 1654019) B1654019
theorem B1102895 : Blo 323837 1102895 := bstep (se 1 (by rfl) ⟨827171, by rfl⟩ : syracuseStep 1102895 = 1654343) B1654343
theorem B1332791 : Blo 323837 1332791 := bstep (se 1 (by rfl) ⟨999593, by rfl⟩ : syracuseStep 1332791 = 1999187) B1999187
theorem B1398383 : Blo 323837 1398383 := bstep (se 1 (by rfl) ⟨1048787, by rfl⟩ : syracuseStep 1398383 = 2097575) B2097575
theorem B1103759 : Blo 323837 1103759 := bstep (se 1 (by rfl) ⟨827819, by rfl⟩ : syracuseStep 1103759 = 1655639) B1655639
theorem B1103867 : Blo 323837 1103867 := bstep (se 1 (by rfl) ⟨827900, by rfl⟩ : syracuseStep 1103867 = 1655801) B1655801
theorem B2775167 : Blo 323837 2775167 := bstep (se 1 (by rfl) ⟨2081375, by rfl⟩ : syracuseStep 2775167 = 4162751) B4162751
theorem B1104353 : Blo 323837 1104353 := bstep (se 2 (by rfl) ⟨414132, by rfl⟩ : syracuseStep 1104353 = 828265) B828265
theorem B547951 : Blo 323837 547951 := bstep (se 1 (by rfl) ⟨410963, by rfl⟩ : syracuseStep 547951 = 821927) B821927
theorem B352063 : Blo 323837 352063 := bstep (se 1 (by rfl) ⟨264047, by rfl⟩ : syracuseStep 352063 = 528095) B528095
theorem B2383789 : Blo 323837 2383789 := bstep (se 3 (by rfl) ⟨446960, by rfl⟩ : syracuseStep 2383789 = 893921) B893921
theorem B6676793 : Blo 323837 6676793 := bstep (se 2 (by rfl) ⟨2503797, by rfl⟩ : syracuseStep 6676793 = 5007595) B5007595
theorem B1171871 : Blo 323837 1171871 := bstep (se 1 (by rfl) ⟨878903, by rfl⟩ : syracuseStep 1171871 = 1757807) B1757807
theorem B22569635 : Blo 323837 22569635 := bstep (se 1 (by rfl) ⟨16927226, by rfl⟩ : syracuseStep 22569635 = 33854453) B33854453
theorem B615367 : Blo 323837 615367 := bstep (se 1 (by rfl) ⟨461525, by rfl⟩ : syracuseStep 615367 = 923051) B923051
theorem B1238921 : Blo 323837 1238921 := bstep (se 2 (by rfl) ⟨464595, by rfl⟩ : syracuseStep 1238921 = 929191) B929191
theorem B616423 : Blo 323837 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B3729563 : Blo 323837 3729563 := bstep (se 1 (by rfl) ⟨2797172, by rfl⟩ : syracuseStep 3729563 = 5594345) B5594345
theorem B485831 : Blo 323837 485831 := bstep (se 1 (by rfl) ⟨364373, by rfl⟩ : syracuseStep 485831 = 728747) B728747
theorem B551407 : Blo 323837 551407 := bstep (se 1 (by rfl) ⟨413555, by rfl⟩ : syracuseStep 551407 = 827111) B827111
theorem B551657 : Blo 323837 551657 := bstep (se 2 (by rfl) ⟨206871, by rfl⟩ : syracuseStep 551657 = 413743) B413743
theorem B551711 : Blo 323837 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B486191 : Blo 323837 486191 := bstep (se 1 (by rfl) ⟨364643, by rfl⟩ : syracuseStep 486191 = 729287) B729287
theorem B486311 : Blo 323837 486311 := bstep (se 1 (by rfl) ⟨364733, by rfl⟩ : syracuseStep 486311 = 729467) B729467
theorem B486491 : Blo 323837 486491 := bstep (se 1 (by rfl) ⟨364868, by rfl⟩ : syracuseStep 486491 = 729737) B729737
theorem B1240211 : Blo 323837 1240211 := bstep (se 1 (by rfl) ⟨930158, by rfl⟩ : syracuseStep 1240211 = 1860317) B1860317
theorem B552143 : Blo 323837 552143 := bstep (se 1 (by rfl) ⟨414107, by rfl⟩ : syracuseStep 552143 = 828215) B828215
theorem B1043867 : Blo 323837 1043867 := bstep (se 1 (by rfl) ⟨782900, by rfl⟩ : syracuseStep 1043867 = 1565801) B1565801
theorem B487079 : Blo 323837 487079 := bstep (se 1 (by rfl) ⟨365309, by rfl⟩ : syracuseStep 487079 = 730619) B730619
theorem B487199 : Blo 323837 487199 := bstep (se 1 (by rfl) ⟨365399, by rfl⟩ : syracuseStep 487199 = 730799) B730799
theorem B487259 : Blo 323837 487259 := bstep (se 1 (by rfl) ⟨365444, by rfl⟩ : syracuseStep 487259 = 730889) B730889
theorem B487403 : Blo 323837 487403 := bstep (se 1 (by rfl) ⟨365552, by rfl⟩ : syracuseStep 487403 = 731105) B731105
theorem B553115 : Blo 323837 553115 := bstep (se 1 (by rfl) ⟨414836, by rfl⟩ : syracuseStep 553115 = 829673) B829673
theorem B553135 : Blo 323837 553135 := bstep (se 1 (by rfl) ⟨414851, by rfl⟩ : syracuseStep 553135 = 829703) B829703
theorem B487679 : Blo 323837 487679 := bstep (se 1 (by rfl) ⟨365759, by rfl⟩ : syracuseStep 487679 = 731519) B731519
theorem B323867 : Blo 323837 323867 := bstep (se 1 (by rfl) ⟨242900, by rfl⟩ : syracuseStep 323867 = 485801) B485801
theorem B881065 : Blo 323837 881065 := bstep (se 2 (by rfl) ⟨330399, by rfl⟩ : syracuseStep 881065 = 660799) B660799
theorem B324123 : Blo 323837 324123 := bstep (se 1 (by rfl) ⟨243092, by rfl⟩ : syracuseStep 324123 = 486185) B486185
theorem B487991 : Blo 323837 487991 := bstep (se 1 (by rfl) ⟨365993, by rfl⟩ : syracuseStep 487991 = 731987) B731987
theorem B1340011 : Blo 323837 1340011 := bstep (se 1 (by rfl) ⟨1005008, by rfl⟩ : syracuseStep 1340011 = 2010017) B2010017
theorem B324263 : Blo 323837 324263 := bstep (se 1 (by rfl) ⟨243197, by rfl⟩ : syracuseStep 324263 = 486395) B486395
theorem B488105 : Blo 323837 488105 := bstep (se 2 (by rfl) ⟨183039, by rfl⟩ : syracuseStep 488105 = 366079) B366079
theorem B324303 : Blo 323837 324303 := bstep (se 1 (by rfl) ⟨243227, by rfl⟩ : syracuseStep 324303 = 486455) B486455
theorem B324383 : Blo 323837 324383 := bstep (se 1 (by rfl) ⟨243287, by rfl⟩ : syracuseStep 324383 = 486575) B486575
theorem B488231 : Blo 323837 488231 := bstep (se 1 (by rfl) ⟨366173, by rfl⟩ : syracuseStep 488231 = 732347) B732347
theorem B324423 : Blo 323837 324423 := bstep (se 1 (by rfl) ⟨243317, by rfl⟩ : syracuseStep 324423 = 486635) B486635
theorem B488351 : Blo 323837 488351 := bstep (se 1 (by rfl) ⟨366263, by rfl⟩ : syracuseStep 488351 = 732527) B732527
theorem B324863 : Blo 323837 324863 := bstep (se 1 (by rfl) ⟨243647, by rfl⟩ : syracuseStep 324863 = 487295) B487295
theorem B488831 : Blo 323837 488831 := bstep (se 1 (by rfl) ⟨366623, by rfl⟩ : syracuseStep 488831 = 733247) B733247
theorem B882103 : Blo 323837 882103 := bstep (se 1 (by rfl) ⟨661577, by rfl⟩ : syracuseStep 882103 = 1323155) B1323155
theorem B325087 : Blo 323837 325087 := bstep (se 1 (by rfl) ⟨243815, by rfl⟩ : syracuseStep 325087 = 487631) B487631
theorem B2487833 : Blo 323837 2487833 := bstep (se 2 (by rfl) ⟨932937, by rfl⟩ : syracuseStep 2487833 = 1865875) B1865875
theorem B423451 : Blo 323837 423451 := bstep (se 1 (by rfl) ⟨317588, by rfl⟩ : syracuseStep 423451 = 635177) B635177
theorem B325167 : Blo 323837 325167 := bstep (se 1 (by rfl) ⟨243875, by rfl⟩ : syracuseStep 325167 = 487751) B487751
theorem B325479 : Blo 323837 325479 := bstep (se 1 (by rfl) ⟨244109, by rfl⟩ : syracuseStep 325479 = 488219) B488219
theorem B325663 : Blo 323837 325663 := bstep (se 1 (by rfl) ⟨244247, by rfl⟩ : syracuseStep 325663 = 488495) B488495
theorem B325695 : Blo 323837 325695 := bstep (se 1 (by rfl) ⟨244271, by rfl⟩ : syracuseStep 325695 = 488543) B488543
theorem B325735 : Blo 323837 325735 := bstep (se 1 (by rfl) ⟨244301, by rfl⟩ : syracuseStep 325735 = 488603) B488603
theorem B325743 : Blo 323837 325743 := bstep (se 1 (by rfl) ⟨244307, by rfl⟩ : syracuseStep 325743 = 488615) B488615
theorem B784495 : Blo 323837 784495 := bstep (se 1 (by rfl) ⟨588371, by rfl⟩ : syracuseStep 784495 = 1176743) B1176743
theorem B489641 : Blo 323837 489641 := bstep (se 2 (by rfl) ⟨183615, by rfl⟩ : syracuseStep 489641 = 367231) B367231
theorem B620713 : Blo 323837 620713 := bstep (se 2 (by rfl) ⟨232767, by rfl⟩ : syracuseStep 620713 = 465535) B465535
theorem B5404967 : Blo 323837 5404967 := bstep (se 1 (by rfl) ⟨4053725, by rfl⟩ : syracuseStep 5404967 = 8107451) B8107451
theorem B621047 : Blo 323837 621047 := bstep (se 1 (by rfl) ⟨465785, by rfl⟩ : syracuseStep 621047 = 931571) B931571
theorem B326191 : Blo 323837 326191 := bstep (se 1 (by rfl) ⟨244643, by rfl⟩ : syracuseStep 326191 = 489287) B489287
theorem B326311 : Blo 323837 326311 := bstep (se 1 (by rfl) ⟨244733, by rfl⟩ : syracuseStep 326311 = 489467) B489467
theorem B3144359 : Blo 323837 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B326351 : Blo 323837 326351 := bstep (se 1 (by rfl) ⟨244763, by rfl⟩ : syracuseStep 326351 = 489527) B489527
theorem B490223 : Blo 323837 490223 := bstep (se 1 (by rfl) ⟨367667, by rfl⟩ : syracuseStep 490223 = 735335) B735335
theorem B326395 : Blo 323837 326395 := bstep (se 1 (by rfl) ⟨244796, by rfl⟩ : syracuseStep 326395 = 489593) B489593
theorem B326431 : Blo 323837 326431 := bstep (se 1 (by rfl) ⟨244823, by rfl⟩ : syracuseStep 326431 = 489647) B489647
theorem B326591 : Blo 323837 326591 := bstep (se 1 (by rfl) ⟨244943, by rfl⟩ : syracuseStep 326591 = 489887) B489887
theorem B326651 : Blo 323837 326651 := bstep (se 1 (by rfl) ⟨244988, by rfl⟩ : syracuseStep 326651 = 489977) B489977
theorem B2784293 : Blo 323837 2784293 := bstep (se 4 (by rfl) ⟨261027, by rfl⟩ : syracuseStep 2784293 = 522055) B522055
theorem B326975 : Blo 323837 326975 := bstep (se 1 (by rfl) ⟨245231, by rfl⟩ : syracuseStep 326975 = 490463) B490463
theorem B327015 : Blo 323837 327015 := bstep (se 1 (by rfl) ⟨245261, by rfl⟩ : syracuseStep 327015 = 490523) B490523
theorem B327271 : Blo 323837 327271 := bstep (se 1 (by rfl) ⟨245453, by rfl⟩ : syracuseStep 327271 = 490907) B490907
theorem B622217 : Blo 323837 622217 := bstep (se 2 (by rfl) ⟨233331, by rfl⟩ : syracuseStep 622217 = 466663) B466663
theorem B327323 : Blo 323837 327323 := bstep (se 1 (by rfl) ⟨245492, by rfl⟩ : syracuseStep 327323 = 490985) B490985
theorem B327327 : Blo 323837 327327 := bstep (se 1 (by rfl) ⟨245495, by rfl⟩ : syracuseStep 327327 = 490991) B490991
theorem B327419 : Blo 323837 327419 := bstep (se 1 (by rfl) ⟨245564, by rfl⟩ : syracuseStep 327419 = 491129) B491129
theorem B327551 : Blo 323837 327551 := bstep (se 1 (by rfl) ⟨245663, by rfl⟩ : syracuseStep 327551 = 491327) B491327
theorem B327583 : Blo 323837 327583 := bstep (se 1 (by rfl) ⟨245687, by rfl⟩ : syracuseStep 327583 = 491375) B491375
theorem B491513 : Blo 323837 491513 := bstep (se 2 (by rfl) ⟨184317, by rfl⟩ : syracuseStep 491513 = 368635) B368635
theorem B491591 : Blo 323837 491591 := bstep (se 1 (by rfl) ⟨368693, by rfl⟩ : syracuseStep 491591 = 737387) B737387
theorem B327835 : Blo 323837 327835 := bstep (se 1 (by rfl) ⟨245876, by rfl⟩ : syracuseStep 327835 = 491753) B491753
theorem B4653677 : Blo 323837 4653677 := bstep (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) B1745129
theorem B787283 : Blo 323837 787283 := bstep (se 1 (by rfl) ⟨590462, by rfl⟩ : syracuseStep 787283 = 1180925) B1180925
theorem B1049863 : Blo 323837 1049863 := bstep (se 1 (by rfl) ⟨787397, by rfl⟩ : syracuseStep 1049863 = 1574795) B1574795
theorem B820489 : Blo 323837 820489 := bstep (se 2 (by rfl) ⟨307683, by rfl⟩ : syracuseStep 820489 = 615367) B615367
theorem B329167 : Blo 323837 329167 := bstep (se 1 (by rfl) ⟨246875, by rfl⟩ : syracuseStep 329167 = 493751) B493751
theorem B3114683 : Blo 323837 3114683 := bstep (se 1 (by rfl) ⟨2336012, by rfl⟩ : syracuseStep 3114683 = 4672025) B4672025
theorem B1771625 : Blo 323837 1771625 := bstep (se 2 (by rfl) ⟨664359, by rfl⟩ : syracuseStep 1771625 = 1328719) B1328719
theorem B6424859 : Blo 323837 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B821897 : Blo 323837 821897 := bstep (se 2 (by rfl) ⟨308211, by rfl⟩ : syracuseStep 821897 = 616423) B616423
theorem B4197095 : Blo 323837 4197095 := bstep (se 1 (by rfl) ⟨3147821, by rfl⟩ : syracuseStep 4197095 = 6295643) B6295643
theorem B888527 : Blo 323837 888527 := bstep (se 1 (by rfl) ⟨666395, by rfl⟩ : syracuseStep 888527 = 1332791) B1332791
theorem B13438979 : Blo 323837 13438979 := bstep (se 1 (by rfl) ⟨10079234, by rfl⟩ : syracuseStep 13438979 = 20158469) B20158469
theorem B1643327 : Blo 323837 1643327 := bstep (se 1 (by rfl) ⟨1232495, by rfl⟩ : syracuseStep 1643327 = 2464991) B2464991
theorem B1907023 : Blo 323837 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B825947 : Blo 323837 825947 := bstep (se 1 (by rfl) ⟨619460, by rfl⟩ : syracuseStep 825947 = 1238921) B1238921
theorem B1645271 : Blo 323837 1645271 := bstep (se 1 (by rfl) ⟨1233953, by rfl⟩ : syracuseStep 1645271 = 2467907) B2467907
theorem B1645595 : Blo 323837 1645595 := bstep (se 1 (by rfl) ⟨1234196, by rfl⟩ : syracuseStep 1645595 = 2468393) B2468393
theorem B367771 : Blo 323837 367771 := bstep (se 1 (by rfl) ⟨275828, by rfl⟩ : syracuseStep 367771 = 551657) B551657
theorem B367807 : Blo 323837 367807 := bstep (se 1 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 367807 = 551711) B551711
theorem B2628895 : Blo 323837 2628895 := bstep (se 1 (by rfl) ⟨1971671, by rfl⟩ : syracuseStep 2628895 = 3943343) B3943343
theorem B826807 : Blo 323837 826807 := bstep (se 1 (by rfl) ⟨620105, by rfl⟩ : syracuseStep 826807 = 1240211) B1240211
theorem B368095 : Blo 323837 368095 := bstep (se 1 (by rfl) ⟨276071, by rfl⟩ : syracuseStep 368095 = 552143) B552143
theorem B1416701 : Blo 323837 1416701 := bstep (se 3 (by rfl) ⟨265631, by rfl⟩ : syracuseStep 1416701 = 531263) B531263
theorem B695911 : Blo 323837 695911 := bstep (se 1 (by rfl) ⟨521933, by rfl⟩ : syracuseStep 695911 = 1043867) B1043867
theorem B2039519 : Blo 323837 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B728999 : Blo 323837 728999 := bstep (se 1 (by rfl) ⟨546749, by rfl⟩ : syracuseStep 728999 = 1093499) B1093499
theorem B729071 : Blo 323837 729071 := bstep (se 1 (by rfl) ⟨546803, by rfl⟩ : syracuseStep 729071 = 1093607) B1093607
theorem B368743 : Blo 323837 368743 := bstep (se 1 (by rfl) ⟨276557, by rfl⟩ : syracuseStep 368743 = 553115) B553115
theorem B827617 : Blo 323837 827617 := bstep (se 2 (by rfl) ⟨310356, by rfl⟩ : syracuseStep 827617 = 620713) B620713
theorem B2498845 : Blo 323837 2498845 := bstep (se 3 (by rfl) ⟨468533, by rfl⟩ : syracuseStep 2498845 = 937067) B937067
theorem B4989367 : Blo 323837 4989367 := bstep (se 1 (by rfl) ⟨3742025, by rfl⟩ : syracuseStep 4989367 = 7484051) B7484051
theorem B1647215 : Blo 323837 1647215 := bstep (se 1 (by rfl) ⟨1235411, by rfl⟩ : syracuseStep 1647215 = 2470823) B2470823
theorem B729755 : Blo 323837 729755 := bstep (se 1 (by rfl) ⟨547316, by rfl⟩ : syracuseStep 729755 = 1094633) B1094633
theorem B730295 : Blo 323837 730295 := bstep (se 1 (by rfl) ⟨547721, by rfl⟩ : syracuseStep 730295 = 1095443) B1095443
theorem B730601 : Blo 323837 730601 := bstep (se 2 (by rfl) ⟨273975, by rfl⟩ : syracuseStep 730601 = 547951) B547951
theorem B1386011 : Blo 323837 1386011 := bstep (se 1 (by rfl) ⟨1039508, by rfl⟩ : syracuseStep 1386011 = 2079017) B2079017
theorem B731303 : Blo 323837 731303 := bstep (se 1 (by rfl) ⟨548477, by rfl⟩ : syracuseStep 731303 = 1096955) B1096955
theorem B469417 : Blo 323837 469417 := bstep (se 2 (by rfl) ⟨176031, by rfl⟩ : syracuseStep 469417 = 352063) B352063
theorem B7908191 : Blo 323837 7908191 := bstep (se 1 (by rfl) ⟨5931143, by rfl⟩ : syracuseStep 7908191 = 11862287) B11862287
theorem B1092959 : Blo 323837 1092959 := bstep (se 1 (by rfl) ⟨819719, by rfl⟩ : syracuseStep 1092959 = 1639439) B1639439
theorem B1846739 : Blo 323837 1846739 := bstep (se 1 (by rfl) ⟨1385054, by rfl⟩ : syracuseStep 1846739 = 2770109) B2770109
theorem B1650455 : Blo 323837 1650455 := bstep (se 1 (by rfl) ⟨1237841, by rfl⟩ : syracuseStep 1650455 = 2475683) B2475683
theorem B732959 : Blo 323837 732959 := bstep (se 1 (by rfl) ⟨549719, by rfl⟩ : syracuseStep 732959 = 1099439) B1099439
theorem B5648237 : Blo 323837 5648237 := bstep (se 3 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 5648237 = 2118089) B2118089
theorem B930295 : Blo 323837 930295 := bstep (se 1 (by rfl) ⟨697721, by rfl⟩ : syracuseStep 930295 = 1395443) B1395443
theorem B930523 : Blo 323837 930523 := bstep (se 1 (by rfl) ⟨697892, by rfl⟩ : syracuseStep 930523 = 1395785) B1395785
theorem B930683 : Blo 323837 930683 := bstep (se 1 (by rfl) ⟨698012, by rfl⟩ : syracuseStep 930683 = 1396025) B1396025
theorem B734543 : Blo 323837 734543 := bstep (se 1 (by rfl) ⟨550907, by rfl⟩ : syracuseStep 734543 = 1101815) B1101815
theorem B5289499 : Blo 323837 5289499 := bstep (se 1 (by rfl) ⟨3967124, by rfl⟩ : syracuseStep 5289499 = 7934249) B7934249
theorem B1095335 : Blo 323837 1095335 := bstep (se 1 (by rfl) ⟨821501, by rfl⟩ : syracuseStep 1095335 = 1643003) B1643003
theorem B735119 : Blo 323837 735119 := bstep (se 1 (by rfl) ⟨551339, by rfl⟩ : syracuseStep 735119 = 1102679) B1102679
theorem B735209 : Blo 323837 735209 := bstep (se 2 (by rfl) ⟨275703, by rfl⟩ : syracuseStep 735209 = 551407) B551407
theorem B4175873 : Blo 323837 4175873 := bstep (se 2 (by rfl) ⟨1565952, by rfl⟩ : syracuseStep 4175873 = 3131905) B3131905
theorem B735263 : Blo 323837 735263 := bstep (se 1 (by rfl) ⟨551447, by rfl⟩ : syracuseStep 735263 = 1102895) B1102895
theorem B833657 : Blo 323837 833657 := bstep (se 2 (by rfl) ⟨312621, by rfl⟩ : syracuseStep 833657 = 625243) B625243
theorem B932255 : Blo 323837 932255 := bstep (se 1 (by rfl) ⟨699191, by rfl⟩ : syracuseStep 932255 = 1398383) B1398383
theorem B735839 : Blo 323837 735839 := bstep (se 1 (by rfl) ⟨551879, by rfl⟩ : syracuseStep 735839 = 1103759) B1103759
theorem B735911 : Blo 323837 735911 := bstep (se 1 (by rfl) ⟨551933, by rfl⟩ : syracuseStep 735911 = 1103867) B1103867
theorem B1850111 : Blo 323837 1850111 := bstep (se 1 (by rfl) ⟨1387583, by rfl⟩ : syracuseStep 1850111 = 2775167) B2775167
theorem B736235 : Blo 323837 736235 := bstep (se 1 (by rfl) ⟨552176, by rfl⟩ : syracuseStep 736235 = 1104353) B1104353
theorem B3587075 : Blo 323837 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B8011649 : Blo 323837 8011649 := bstep (se 2 (by rfl) ⟨3004368, by rfl⟩ : syracuseStep 8011649 = 6008737) B6008737
theorem B737513 : Blo 323837 737513 := bstep (se 2 (by rfl) ⟨276567, by rfl⟩ : syracuseStep 737513 = 553135) B553135
theorem B1557305 : Blo 323837 1557305 := bstep (se 2 (by rfl) ⟨583989, by rfl⟩ : syracuseStep 1557305 = 1167979) B1167979
theorem B1786681 : Blo 323837 1786681 := bstep (se 2 (by rfl) ⟨670005, by rfl⟩ : syracuseStep 1786681 = 1340011) B1340011
theorem B1656125 : Blo 323837 1656125 := bstep (se 3 (by rfl) ⟨310523, by rfl⟩ : syracuseStep 1656125 = 621047) B621047
theorem B7914995 : Blo 323837 7914995 := bstep (se 1 (by rfl) ⟨5936246, by rfl⟩ : syracuseStep 7914995 = 11872493) B11872493
theorem B1755037 : Blo 323837 1755037 := bstep (se 3 (by rfl) ⟨329069, by rfl⟩ : syracuseStep 1755037 = 658139) B658139
theorem B1231145 : Blo 323837 1231145 := bstep (se 2 (by rfl) ⟨461679, by rfl⟩ : syracuseStep 1231145 = 923359) B923359
theorem B1658555 : Blo 323837 1658555 := bstep (se 1 (by rfl) ⟨1243916, by rfl⟩ : syracuseStep 1658555 = 2487833) B2487833
theorem B1560647 : Blo 323837 1560647 := bstep (se 1 (by rfl) ⟨1170485, by rfl⟩ : syracuseStep 1560647 = 2340971) B2340971
theorem B1888379 : Blo 323837 1888379 := bstep (se 1 (by rfl) ⟨1416284, by rfl⟩ : syracuseStep 1888379 = 2832569) B2832569
theorem B3133903 : Blo 323837 3133903 := bstep (se 1 (by rfl) ⟨2350427, by rfl⟩ : syracuseStep 3133903 = 4700855) B4700855
theorem B1102463 : Blo 323837 1102463 := bstep (se 1 (by rfl) ⟨826847, by rfl⟩ : syracuseStep 1102463 = 1653695) B1653695
theorem B1856195 : Blo 323837 1856195 := bstep (se 1 (by rfl) ⟨1392146, by rfl⟩ : syracuseStep 1856195 = 2784293) B2784293
theorem B1233863 : Blo 323837 1233863 := bstep (se 1 (by rfl) ⟨925397, by rfl⟩ : syracuseStep 1233863 = 1850795) B1850795
theorem B414811 : Blo 323837 414811 := bstep (se 1 (by rfl) ⟨311108, by rfl⟩ : syracuseStep 414811 = 622217) B622217
theorem B1103273 : Blo 323837 1103273 := bstep (se 2 (by rfl) ⟨413727, by rfl⟩ : syracuseStep 1103273 = 827455) B827455
theorem B1103327 : Blo 323837 1103327 := bstep (se 1 (by rfl) ⟨827495, by rfl⟩ : syracuseStep 1103327 = 1654991) B1654991
theorem B939689 : Blo 323837 939689 := bstep (se 2 (by rfl) ⟨352383, by rfl⟩ : syracuseStep 939689 = 704767) B704767
theorem B4183973 : Blo 323837 4183973 := bstep (se 4 (by rfl) ⟨392247, by rfl⟩ : syracuseStep 4183973 = 784495) B784495
theorem B808951 : Blo 323837 808951 := bstep (se 1 (by rfl) ⟨606713, by rfl⟩ : syracuseStep 808951 = 1213427) B1213427
theorem B3693113 : Blo 323837 3693113 := bstep (se 2 (by rfl) ⟨1384917, by rfl⟩ : syracuseStep 3693113 = 2769835) B2769835
theorem B547519 : Blo 323837 547519 := bstep (se 1 (by rfl) ⟨410639, by rfl⟩ : syracuseStep 547519 = 821279) B821279
theorem B60185693 : Blo 323837 60185693 := bstep (se 3 (by rfl) ⟨11284817, by rfl⟩ : syracuseStep 60185693 = 22569635) B22569635
theorem B1858859 : Blo 323837 1858859 := bstep (se 1 (by rfl) ⟨1394144, by rfl⟩ : syracuseStep 1858859 = 2788289) B2788289
theorem B3825305 : Blo 323837 3825305 := bstep (se 2 (by rfl) ⟨1434489, by rfl⟩ : syracuseStep 3825305 = 2868979) B2868979
theorem B548687 : Blo 323837 548687 := bstep (se 1 (by rfl) ⟨411515, by rfl⟩ : syracuseStep 548687 = 823031) B823031
theorem B7004231 : Blo 323837 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B1106135 : Blo 323837 1106135 := bstep (se 1 (by rfl) ⟨829601, by rfl⟩ : syracuseStep 1106135 = 1659203) B1659203
theorem B1106297 : Blo 323837 1106297 := bstep (se 2 (by rfl) ⟨414861, by rfl⟩ : syracuseStep 1106297 = 829723) B829723
theorem B7627385 : Blo 323837 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B549659 : Blo 323837 549659 := bstep (se 1 (by rfl) ⟨412244, by rfl⟩ : syracuseStep 549659 = 824489) B824489
theorem B2646827 : Blo 323837 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B550111 : Blo 323837 550111 := bstep (se 1 (by rfl) ⟨412583, by rfl⟩ : syracuseStep 550111 = 825167) B825167
theorem B550543 : Blo 323837 550543 := bstep (se 1 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 550543 = 825815) B825815
theorem B616673 : Blo 323837 616673 := bstep (se 2 (by rfl) ⟨231252, by rfl⟩ : syracuseStep 616673 = 462505) B462505
theorem B486095 : Blo 323837 486095 := bstep (se 1 (by rfl) ⟨364571, by rfl⟩ : syracuseStep 486095 = 729143) B729143
theorem B4451195 : Blo 323837 4451195 := bstep (se 1 (by rfl) ⟨3338396, by rfl⟩ : syracuseStep 4451195 = 6676793) B6676793
theorem B781247 : Blo 323837 781247 := bstep (se 1 (by rfl) ⟨585935, by rfl⟩ : syracuseStep 781247 = 1171871) B1171871
theorem B1174753 : Blo 323837 1174753 := bstep (se 2 (by rfl) ⟨440532, by rfl⟩ : syracuseStep 1174753 = 881065) B881065
theorem B2486375 : Blo 323837 2486375 := bstep (se 1 (by rfl) ⟨1864781, by rfl⟩ : syracuseStep 2486375 = 3729563) B3729563
theorem B323887 : Blo 323837 323887 := bstep (se 1 (by rfl) ⟨242915, by rfl⟩ : syracuseStep 323887 = 485831) B485831
theorem B8384957 : Blo 323837 8384957 := bstep (se 3 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 8384957 = 3144359) B3144359
theorem B324127 : Blo 323837 324127 := bstep (se 1 (by rfl) ⟨243095, by rfl⟩ : syracuseStep 324127 = 486191) B486191
theorem B1176137 : Blo 323837 1176137 := bstep (se 2 (by rfl) ⟨441051, by rfl⟩ : syracuseStep 1176137 = 882103) B882103
theorem B324207 : Blo 323837 324207 := bstep (se 1 (by rfl) ⟨243155, by rfl⟩ : syracuseStep 324207 = 486311) B486311
theorem B324327 : Blo 323837 324327 := bstep (se 1 (by rfl) ⟨243245, by rfl⟩ : syracuseStep 324327 = 486491) B486491
theorem B1864691 : Blo 323837 1864691 := bstep (se 1 (by rfl) ⟨1398518, by rfl⟩ : syracuseStep 1864691 = 2797037) B2797037
theorem B324719 : Blo 323837 324719 := bstep (se 1 (by rfl) ⟨243539, by rfl⟩ : syracuseStep 324719 = 487079) B487079
theorem B324799 : Blo 323837 324799 := bstep (se 1 (by rfl) ⟨243599, by rfl⟩ : syracuseStep 324799 = 487199) B487199
theorem B324839 : Blo 323837 324839 := bstep (se 1 (by rfl) ⟨243629, by rfl⟩ : syracuseStep 324839 = 487259) B487259
theorem B324935 : Blo 323837 324935 := bstep (se 1 (by rfl) ⟨243701, by rfl⟩ : syracuseStep 324935 = 487403) B487403
theorem B2258405 : Blo 323837 2258405 := bstep (se 4 (by rfl) ⟨211725, by rfl⟩ : syracuseStep 2258405 = 423451) B423451
theorem B325119 : Blo 323837 325119 := bstep (se 1 (by rfl) ⟨243839, by rfl⟩ : syracuseStep 325119 = 487679) B487679
theorem B325327 : Blo 323837 325327 := bstep (se 1 (by rfl) ⟨243995, by rfl⟩ : syracuseStep 325327 = 487991) B487991
theorem B489167 : Blo 323837 489167 := bstep (se 1 (by rfl) ⟨366875, by rfl⟩ : syracuseStep 489167 = 733751) B733751
theorem B325403 : Blo 323837 325403 := bstep (se 1 (by rfl) ⟨244052, by rfl⟩ : syracuseStep 325403 = 488105) B488105
theorem B325487 : Blo 323837 325487 := bstep (se 1 (by rfl) ⟨244115, by rfl⟩ : syracuseStep 325487 = 488231) B488231
theorem B325567 : Blo 323837 325567 := bstep (se 1 (by rfl) ⟨244175, by rfl⟩ : syracuseStep 325567 = 488351) B488351
theorem B489407 : Blo 323837 489407 := bstep (se 1 (by rfl) ⟨367055, by rfl⟩ : syracuseStep 489407 = 734111) B734111
theorem B325887 : Blo 323837 325887 := bstep (se 1 (by rfl) ⟨244415, by rfl⟩ : syracuseStep 325887 = 488831) B488831
theorem B326427 : Blo 323837 326427 := bstep (se 1 (by rfl) ⟨244820, by rfl⟩ : syracuseStep 326427 = 489641) B489641
theorem B3603311 : Blo 323837 3603311 := bstep (se 1 (by rfl) ⟨2702483, by rfl⟩ : syracuseStep 3603311 = 5404967) B5404967
theorem B326815 : Blo 323837 326815 := bstep (se 1 (by rfl) ⟨245111, by rfl⟩ : syracuseStep 326815 = 490223) B490223
theorem B232815779 : Blo 323837 232815779 := bstep (se 1 (by rfl) ⟨174611834, by rfl⟩ : syracuseStep 232815779 = 349223669) B349223669
theorem B3178385 : Blo 323837 3178385 := bstep (se 2 (by rfl) ⟨1191894, by rfl⟩ : syracuseStep 3178385 = 2383789) B2383789
theorem B3964895 : Blo 323837 3964895 := bstep (se 1 (by rfl) ⟨2973671, by rfl⟩ : syracuseStep 3964895 = 5947343) B5947343
theorem B327675 : Blo 323837 327675 := bstep (se 1 (by rfl) ⟨245756, by rfl⟩ : syracuseStep 327675 = 491513) B491513
theorem B327727 : Blo 323837 327727 := bstep (se 1 (by rfl) ⟨245795, by rfl⟩ : syracuseStep 327727 = 491591) B491591
theorem B491657 : Blo 323837 491657 := bstep (se 2 (by rfl) ⟨184371, by rfl⟩ : syracuseStep 491657 = 368743) B368743
theorem B491675 : Blo 323837 491675 := bstep (se 1 (by rfl) ⟨368756, by rfl⟩ : syracuseStep 491675 = 737513) B737513
theorem B4161725 : Blo 323837 4161725 := bstep (se 3 (by rfl) ⟨780323, by rfl⟩ : syracuseStep 4161725 = 1560647) B1560647
theorem B524855 : Blo 323837 524855 := bstep (se 1 (by rfl) ⟨393641, by rfl⟩ : syracuseStep 524855 = 787283) B787283
theorem B6652489 : Blo 323837 6652489 := bstep (se 2 (by rfl) ⟨2494683, by rfl⟩ : syracuseStep 6652489 = 4989367) B4989367
theorem B5276663 : Blo 323837 5276663 := bstep (se 1 (by rfl) ⟨3957497, by rfl⟩ : syracuseStep 5276663 = 7914995) B7914995
theorem B1181083 : Blo 323837 1181083 := bstep (se 1 (by rfl) ⟨885812, by rfl⟩ : syracuseStep 1181083 = 1771625) B1771625
theorem B820763 : Blo 323837 820763 := bstep (se 1 (by rfl) ⟨615572, by rfl⟩ : syracuseStep 820763 = 1231145) B1231145
theorem B592351 : Blo 323837 592351 := bstep (se 1 (by rfl) ⟨444263, by rfl⟩ : syracuseStep 592351 = 888527) B888527
theorem B625889 : Blo 323837 625889 := bstep (se 2 (by rfl) ⟨234708, by rfl⟩ : syracuseStep 625889 = 469417) B469417
theorem B822575 : Blo 323837 822575 := bstep (se 1 (by rfl) ⟨616931, by rfl⟩ : syracuseStep 822575 = 1233863) B1233863
theorem B626459 : Blo 323837 626459 := bstep (se 1 (by rfl) ⟨469844, by rfl⟩ : syracuseStep 626459 = 939689) B939689
theorem B2789315 : Blo 323837 2789315 := bstep (se 1 (by rfl) ⟨2091986, by rfl⟩ : syracuseStep 2789315 = 4183973) B4183973
theorem B2462075 : Blo 323837 2462075 := bstep (se 1 (by rfl) ⟨1846556, by rfl⟩ : syracuseStep 2462075 = 3693113) B3693113
theorem B365791 : Blo 323837 365791 := bstep (se 1 (by rfl) ⟨274343, by rfl⟩ : syracuseStep 365791 = 548687) B548687
theorem B366439 : Blo 323837 366439 := bstep (se 1 (by rfl) ⟨274829, by rfl⟩ : syracuseStep 366439 = 549659) B549659
theorem B1644461 : Blo 323837 1644461 := bstep (se 3 (by rfl) ⟨308336, by rfl⟩ : syracuseStep 1644461 = 616673) B616673
theorem B7052665 : Blo 323837 7052665 := bstep (se 2 (by rfl) ⟨2644749, by rfl⟩ : syracuseStep 7052665 = 5289499) B5289499
theorem B728639 : Blo 323837 728639 := bstep (se 1 (by rfl) ⟨546479, by rfl⟩ : syracuseStep 728639 = 1092959) B1092959
theorem B730025 : Blo 323837 730025 := bstep (se 2 (by rfl) ⟨273759, by rfl⟩ : syracuseStep 730025 = 547519) B547519
theorem B730223 : Blo 323837 730223 := bstep (se 1 (by rfl) ⟨547667, by rfl⟩ : syracuseStep 730223 = 1095335) B1095335
theorem B2402207 : Blo 323837 2402207 := bstep (se 1 (by rfl) ⟨1801655, by rfl⟩ : syracuseStep 2402207 = 3603311) B3603311
theorem B927881 : Blo 323837 927881 := bstep (se 2 (by rfl) ⟨347955, by rfl⟩ : syracuseStep 927881 = 695911) B695911
theorem B2076455 : Blo 323837 2076455 := bstep (se 1 (by rfl) ⟨1557341, by rfl⟩ : syracuseStep 2076455 = 3114683) B3114683
theorem B8892341 : Blo 323837 8892341 := bstep (se 5 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 8892341 = 833657) B833657
theorem B733481 : Blo 323837 733481 := bstep (se 2 (by rfl) ⟨275055, by rfl⟩ : syracuseStep 733481 = 550111) B550111
theorem B1093985 : Blo 323837 1093985 := bstep (se 2 (by rfl) ⟨410244, by rfl⟩ : syracuseStep 1093985 = 820489) B820489
theorem B2798063 : Blo 323837 2798063 := bstep (se 1 (by rfl) ⟨2098547, by rfl⟩ : syracuseStep 2798063 = 4197095) B4197095
theorem B438889 : Blo 323837 438889 := bstep (se 2 (by rfl) ⟨164583, by rfl⟩ : syracuseStep 438889 = 329167) B329167
theorem B734057 : Blo 323837 734057 := bstep (se 2 (by rfl) ⟨275271, by rfl⟩ : syracuseStep 734057 = 550543) B550543
theorem B2340049 : Blo 323837 2340049 := bstep (se 2 (by rfl) ⟨877518, by rfl⟩ : syracuseStep 2340049 = 1755037) B1755037
theorem B8959319 : Blo 323837 8959319 := bstep (se 1 (by rfl) ⟨6719489, by rfl⟩ : syracuseStep 8959319 = 13438979) B13438979
theorem B1258919 : Blo 323837 1258919 := bstep (se 1 (by rfl) ⟨944189, by rfl⟩ : syracuseStep 1258919 = 1888379) B1888379
theorem B734975 : Blo 323837 734975 := bstep (se 1 (by rfl) ⟨551231, by rfl⟩ : syracuseStep 734975 = 1102463) B1102463
theorem B1095551 : Blo 323837 1095551 := bstep (se 1 (by rfl) ⟨821663, by rfl⟩ : syracuseStep 1095551 = 1643327) B1643327
theorem B735515 : Blo 323837 735515 := bstep (se 1 (by rfl) ⟨551636, by rfl⟩ : syracuseStep 735515 = 1103273) B1103273
theorem B735551 : Blo 323837 735551 := bstep (se 1 (by rfl) ⟨551663, by rfl⟩ : syracuseStep 735551 = 1103327) B1103327
theorem B1096847 : Blo 323837 1096847 := bstep (se 1 (by rfl) ⟨822635, by rfl⟩ : syracuseStep 1096847 = 1645271) B1645271
theorem B1097063 : Blo 323837 1097063 := bstep (se 1 (by rfl) ⟨822797, by rfl⟩ : syracuseStep 1097063 = 1645595) B1645595
theorem B1359679 : Blo 323837 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B4669487 : Blo 323837 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B737423 : Blo 323837 737423 := bstep (se 1 (by rfl) ⟨553067, by rfl⟩ : syracuseStep 737423 = 1106135) B1106135
theorem B737531 : Blo 323837 737531 := bstep (se 1 (by rfl) ⟨553148, by rfl⟩ : syracuseStep 737531 = 1106297) B1106297
theorem B1098143 : Blo 323837 1098143 := bstep (se 1 (by rfl) ⟨823607, by rfl⟩ : syracuseStep 1098143 = 1647215) B1647215
theorem B4178537 : Blo 323837 4178537 := bstep (se 2 (by rfl) ⟨1566951, by rfl⟩ : syracuseStep 4178537 = 3133903) B3133903
theorem B2967463 : Blo 323837 2967463 := bstep (se 1 (by rfl) ⟨2225597, by rfl⟩ : syracuseStep 2967463 = 4451195) B4451195
theorem B1231159 : Blo 323837 1231159 := bstep (se 1 (by rfl) ⟨923369, by rfl⟩ : syracuseStep 1231159 = 1846739) B1846739
theorem B1100303 : Blo 323837 1100303 := bstep (se 1 (by rfl) ⟨825227, by rfl⟩ : syracuseStep 1100303 = 1650455) B1650455
theorem B1657583 : Blo 323837 1657583 := bstep (se 1 (by rfl) ⟨1243187, by rfl⟩ : syracuseStep 1657583 = 2486375) B2486375
theorem B5589971 : Blo 323837 5589971 := bstep (se 1 (by rfl) ⟨4192478, by rfl⟩ : syracuseStep 5589971 = 8384957) B8384957
theorem B2542697 : Blo 323837 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B1233407 : Blo 323837 1233407 := bstep (se 1 (by rfl) ⟨925055, by rfl⟩ : syracuseStep 1233407 = 1850111) B1850111
theorem B1102409 : Blo 323837 1102409 := bstep (se 2 (by rfl) ⟨413403, by rfl⟩ : syracuseStep 1102409 = 826807) B826807
theorem B155210519 : Blo 323837 155210519 := bstep (se 1 (by rfl) ⟨116407889, by rfl⟩ : syracuseStep 155210519 = 232815779) B232815779
theorem B2118923 : Blo 323837 2118923 := bstep (se 1 (by rfl) ⟨1589192, by rfl⟩ : syracuseStep 2118923 = 3178385) B3178385
theorem B2643263 : Blo 323837 2643263 := bstep (se 1 (by rfl) ⟨1982447, by rfl⟩ : syracuseStep 2643263 = 3964895) B3964895
theorem B1103489 : Blo 323837 1103489 := bstep (se 2 (by rfl) ⟨413808, by rfl⟩ : syracuseStep 1103489 = 827617) B827617
theorem B3331793 : Blo 323837 3331793 := bstep (se 2 (by rfl) ⟨1249422, by rfl⟩ : syracuseStep 3331793 = 2498845) B2498845
theorem B1038203 : Blo 323837 1038203 := bstep (se 1 (by rfl) ⟨778652, by rfl⟩ : syracuseStep 1038203 = 1557305) B1557305
theorem B1104083 : Blo 323837 1104083 := bstep (se 1 (by rfl) ⟨828062, by rfl⟩ : syracuseStep 1104083 = 1656125) B1656125
theorem B4283239 : Blo 323837 4283239 := bstep (se 1 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 4283239 = 6424859) B6424859
theorem B12409805 : Blo 323837 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B20339693 : Blo 323837 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B1399817 : Blo 323837 1399817 := bstep (se 2 (by rfl) ⟨524931, by rfl⟩ : syracuseStep 1399817 = 1049863) B1049863
theorem B547931 : Blo 323837 547931 := bstep (se 1 (by rfl) ⟨410948, by rfl⟩ : syracuseStep 547931 = 821897) B821897
theorem B1105703 : Blo 323837 1105703 := bstep (se 1 (by rfl) ⟨829277, by rfl⟩ : syracuseStep 1105703 = 1658555) B1658555
theorem B1237463 : Blo 323837 1237463 := bstep (se 1 (by rfl) ⟨928097, by rfl⟩ : syracuseStep 1237463 = 1856195) B1856195
theorem B3696029 : Blo 323837 3696029 := bstep (se 3 (by rfl) ⟨693005, by rfl⟩ : syracuseStep 3696029 = 1386011) B1386011
theorem B1566337 : Blo 323837 1566337 := bstep (se 2 (by rfl) ⟨587376, by rfl⟩ : syracuseStep 1566337 = 1174753) B1174753
theorem B9528965 : Blo 323837 9528965 := bstep (se 4 (by rfl) ⟨893340, by rfl⟩ : syracuseStep 9528965 = 1786681) B1786681
theorem B550631 : Blo 323837 550631 := bstep (se 1 (by rfl) ⟨412973, by rfl⟩ : syracuseStep 550631 = 825947) B825947
theorem B1239239 : Blo 323837 1239239 := bstep (se 1 (by rfl) ⟨929429, by rfl⟩ : syracuseStep 1239239 = 1858859) B1858859
theorem B944467 : Blo 323837 944467 := bstep (se 1 (by rfl) ⟨708350, by rfl⟩ : syracuseStep 944467 = 1416701) B1416701
theorem B2550203 : Blo 323837 2550203 := bstep (se 1 (by rfl) ⟨1912652, by rfl⟩ : syracuseStep 2550203 = 3825305) B3825305
theorem B485999 : Blo 323837 485999 := bstep (se 1 (by rfl) ⟨364499, by rfl⟩ : syracuseStep 485999 = 728999) B728999
theorem B486047 : Blo 323837 486047 := bstep (se 1 (by rfl) ⟨364535, by rfl⟩ : syracuseStep 486047 = 729071) B729071
theorem B486503 : Blo 323837 486503 := bstep (se 1 (by rfl) ⟨364877, by rfl⟩ : syracuseStep 486503 = 729755) B729755
theorem B1764551 : Blo 323837 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B1240393 : Blo 323837 1240393 := bstep (se 2 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 1240393 = 930295) B930295
theorem B486863 : Blo 323837 486863 := bstep (se 1 (by rfl) ⟨365147, by rfl⟩ : syracuseStep 486863 = 730295) B730295
theorem B1240697 : Blo 323837 1240697 := bstep (se 2 (by rfl) ⟨465261, by rfl⟩ : syracuseStep 1240697 = 930523) B930523
theorem B487067 : Blo 323837 487067 := bstep (se 1 (by rfl) ⟨365300, by rfl⟩ : syracuseStep 487067 = 730601) B730601
theorem B487535 : Blo 323837 487535 := bstep (se 1 (by rfl) ⟨365651, by rfl⟩ : syracuseStep 487535 = 731303) B731303
theorem B553081 : Blo 323837 553081 := bstep (se 2 (by rfl) ⟨207405, by rfl⟩ : syracuseStep 553081 = 414811) B414811
theorem B324063 : Blo 323837 324063 := bstep (se 1 (by rfl) ⟨243047, by rfl⟩ : syracuseStep 324063 = 486095) B486095
theorem B5272127 : Blo 323837 5272127 := bstep (se 1 (by rfl) ⟨3954095, by rfl⟩ : syracuseStep 5272127 = 7908191) B7908191
theorem B520831 : Blo 323837 520831 := bstep (se 1 (by rfl) ⟨390623, by rfl⟩ : syracuseStep 520831 = 781247) B781247
theorem B488639 : Blo 323837 488639 := bstep (se 1 (by rfl) ⟨366479, by rfl⟩ : syracuseStep 488639 = 732959) B732959
theorem B3765491 : Blo 323837 3765491 := bstep (se 1 (by rfl) ⟨2824118, by rfl⟩ : syracuseStep 3765491 = 5648237) B5648237
theorem B1078601 : Blo 323837 1078601 := bstep (se 2 (by rfl) ⟨404475, by rfl⟩ : syracuseStep 1078601 = 808951) B808951
theorem B160495181 : Blo 323837 160495181 := bstep (se 3 (by rfl) ⟨30092846, by rfl⟩ : syracuseStep 160495181 = 60185693) B60185693
theorem B784091 : Blo 323837 784091 := bstep (se 1 (by rfl) ⟨588068, by rfl⟩ : syracuseStep 784091 = 1176137) B1176137
theorem B620455 : Blo 323837 620455 := bstep (se 1 (by rfl) ⟨465341, by rfl⟩ : syracuseStep 620455 = 930683) B930683
theorem B1243127 : Blo 323837 1243127 := bstep (se 1 (by rfl) ⟨932345, by rfl⟩ : syracuseStep 1243127 = 1864691) B1864691
theorem B489695 : Blo 323837 489695 := bstep (se 1 (by rfl) ⟨367271, by rfl⟩ : syracuseStep 489695 = 734543) B734543
theorem B1505603 : Blo 323837 1505603 := bstep (se 1 (by rfl) ⟨1129202, by rfl⟩ : syracuseStep 1505603 = 2258405) B2258405
theorem B326111 : Blo 323837 326111 := bstep (se 1 (by rfl) ⟨244583, by rfl⟩ : syracuseStep 326111 = 489167) B489167
theorem B490079 : Blo 323837 490079 := bstep (se 1 (by rfl) ⟨367559, by rfl⟩ : syracuseStep 490079 = 735119) B735119
theorem B326271 : Blo 323837 326271 := bstep (se 1 (by rfl) ⟨244703, by rfl⟩ : syracuseStep 326271 = 489407) B489407
theorem B490139 : Blo 323837 490139 := bstep (se 1 (by rfl) ⟨367604, by rfl⟩ : syracuseStep 490139 = 735209) B735209
theorem B2783915 : Blo 323837 2783915 := bstep (se 1 (by rfl) ⟨2087936, by rfl⟩ : syracuseStep 2783915 = 4175873) B4175873
theorem B490175 : Blo 323837 490175 := bstep (se 1 (by rfl) ⟨367631, by rfl⟩ : syracuseStep 490175 = 735263) B735263
theorem B490361 : Blo 323837 490361 := bstep (se 2 (by rfl) ⟨183885, by rfl⟩ : syracuseStep 490361 = 367771) B367771
theorem B490409 : Blo 323837 490409 := bstep (se 2 (by rfl) ⟨183903, by rfl⟩ : syracuseStep 490409 = 367807) B367807
theorem B621503 : Blo 323837 621503 := bstep (se 1 (by rfl) ⟨466127, by rfl⟩ : syracuseStep 621503 = 932255) B932255
theorem B3505193 : Blo 323837 3505193 := bstep (se 2 (by rfl) ⟨1314447, by rfl⟩ : syracuseStep 3505193 = 2628895) B2628895
theorem B490559 : Blo 323837 490559 := bstep (se 1 (by rfl) ⟨367919, by rfl⟩ : syracuseStep 490559 = 735839) B735839
theorem B490607 : Blo 323837 490607 := bstep (se 1 (by rfl) ⟨367955, by rfl⟩ : syracuseStep 490607 = 735911) B735911
theorem B490793 : Blo 323837 490793 := bstep (se 2 (by rfl) ⟨184047, by rfl⟩ : syracuseStep 490793 = 368095) B368095
theorem B490823 : Blo 323837 490823 := bstep (se 1 (by rfl) ⟨368117, by rfl⟩ : syracuseStep 490823 = 736235) B736235
theorem B2391383 : Blo 323837 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B5341099 : Blo 323837 5341099 := bstep (se 1 (by rfl) ⟨4005824, by rfl⟩ : syracuseStep 5341099 = 8011649) B8011649
theorem B3112991 : Blo 323837 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B327771 : Blo 323837 327771 := bstep (se 1 (by rfl) ⟨245828, by rfl⟩ : syracuseStep 327771 = 491657) B491657
theorem B491615 : Blo 323837 491615 := bstep (se 1 (by rfl) ⟨368711, by rfl⟩ : syracuseStep 491615 = 737423) B737423
theorem B327783 : Blo 323837 327783 := bstep (se 1 (by rfl) ⟨245837, by rfl⟩ : syracuseStep 327783 = 491675) B491675
theorem B491687 : Blo 323837 491687 := bstep (se 1 (by rfl) ⟨368765, by rfl⟩ : syracuseStep 491687 = 737531) B737531
theorem B2785691 : Blo 323837 2785691 := bstep (se 1 (by rfl) ⟨2089268, by rfl⟩ : syracuseStep 2785691 = 4178537) B4178537
theorem B1574777 : Blo 323837 1574777 := bstep (se 2 (by rfl) ⟨590541, by rfl⟩ : syracuseStep 1574777 = 1181083) B1181083
theorem B413894717 : Blo 323837 413894717 := bstep (se 3 (by rfl) ⟨77605259, by rfl⟩ : syracuseStep 413894717 = 155210519) B155210519
theorem B1641383 : Blo 323837 1641383 := bstep (se 1 (by rfl) ⟨1231037, by rfl⟩ : syracuseStep 1641383 = 2462075) B2462075
theorem B822271 : Blo 323837 822271 := bstep (se 1 (by rfl) ⟨616703, by rfl⟩ : syracuseStep 822271 = 1233407) B1233407
theorem B1641545 : Blo 323837 1641545 := bstep (se 2 (by rfl) ⟨615579, by rfl⟩ : syracuseStep 1641545 = 1231159) B1231159
theorem B11505077 : Blo 323837 11505077 := bstep (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) B1078601
theorem B1412615 : Blo 323837 1412615 := bstep (se 1 (by rfl) ⟨1059461, by rfl⟩ : syracuseStep 1412615 = 2118923) B2118923
theorem B692135 : Blo 323837 692135 := bstep (se 1 (by rfl) ⟨519101, by rfl⟩ : syracuseStep 692135 = 1038203) B1038203
theorem B365287 : Blo 323837 365287 := bstep (se 1 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 365287 = 547931) B547931
theorem B824975 : Blo 323837 824975 := bstep (se 1 (by rfl) ⟨618731, by rfl⟩ : syracuseStep 824975 = 1237463) B1237463
theorem B694441 : Blo 323837 694441 := bstep (se 2 (by rfl) ⟨260415, by rfl⟩ : syracuseStep 694441 = 520831) B520831
theorem B2464019 : Blo 323837 2464019 := bstep (se 1 (by rfl) ⟨1848014, by rfl⟩ : syracuseStep 2464019 = 3696029) B3696029
theorem B367087 : Blo 323837 367087 := bstep (se 1 (by rfl) ⟨275315, by rfl⟩ : syracuseStep 367087 = 550631) B550631
theorem B826159 : Blo 323837 826159 := bstep (se 1 (by rfl) ⟨619619, by rfl⟩ : syracuseStep 826159 = 1239239) B1239239
theorem B3120065 : Blo 323837 3120065 := bstep (se 2 (by rfl) ⟨1170024, by rfl⟩ : syracuseStep 3120065 = 2340049) B2340049
theorem B827131 : Blo 323837 827131 := bstep (se 1 (by rfl) ⟨620348, by rfl⟩ : syracuseStep 827131 = 1240697) B1240697
theorem B1384303 : Blo 323837 1384303 := bstep (se 1 (by rfl) ⟨1038227, by rfl⟩ : syracuseStep 1384303 = 2076455) B2076455
theorem B827273 : Blo 323837 827273 := bstep (se 2 (by rfl) ⟨310227, by rfl⟩ : syracuseStep 827273 = 620455) B620455
theorem B729323 : Blo 323837 729323 := bstep (se 1 (by rfl) ⟨546992, by rfl⟩ : syracuseStep 729323 = 1093985) B1093985
theorem B3514751 : Blo 323837 3514751 := bstep (se 1 (by rfl) ⟨2636063, by rfl⟩ : syracuseStep 3514751 = 5272127) B5272127
theorem B5972879 : Blo 323837 5972879 := bstep (se 1 (by rfl) ⟨4479659, by rfl⟩ : syracuseStep 5972879 = 8959319) B8959319
theorem B106996787 : Blo 323837 106996787 := bstep (se 1 (by rfl) ⟨80247590, by rfl⟩ : syracuseStep 106996787 = 160495181) B160495181
theorem B5710985 : Blo 323837 5710985 := bstep (se 2 (by rfl) ⟨2141619, by rfl⟩ : syracuseStep 5710985 = 4283239) B4283239
theorem B730367 : Blo 323837 730367 := bstep (se 1 (by rfl) ⟨547775, by rfl⟩ : syracuseStep 730367 = 1095551) B1095551
theorem B828751 : Blo 323837 828751 := bstep (se 1 (by rfl) ⟨621563, by rfl⟩ : syracuseStep 828751 = 1243127) B1243127
theorem B2336795 : Blo 323837 2336795 := bstep (se 1 (by rfl) ⟨1752596, by rfl⟩ : syracuseStep 2336795 = 3505193) B3505193
theorem B731231 : Blo 323837 731231 := bstep (se 1 (by rfl) ⟨548423, by rfl⟩ : syracuseStep 731231 = 1096847) B1096847
theorem B731375 : Blo 323837 731375 := bstep (se 1 (by rfl) ⟨548531, by rfl⟩ : syracuseStep 731375 = 1097063) B1097063
theorem B1812905 : Blo 323837 1812905 := bstep (se 2 (by rfl) ⟨679839, by rfl⟩ : syracuseStep 1812905 = 1359679) B1359679
theorem B7121465 : Blo 323837 7121465 := bstep (se 2 (by rfl) ⟨2670549, by rfl⟩ : syracuseStep 7121465 = 5341099) B5341099
theorem B732095 : Blo 323837 732095 := bstep (se 1 (by rfl) ⟨549071, by rfl⟩ : syracuseStep 732095 = 1098143) B1098143
theorem B3517775 : Blo 323837 3517775 := bstep (se 1 (by rfl) ⟨2638331, by rfl⟩ : syracuseStep 3517775 = 5276663) B5276663
theorem B733535 : Blo 323837 733535 := bstep (se 1 (by rfl) ⟨550151, by rfl⟩ : syracuseStep 733535 = 1100303) B1100303
theorem B3159205 : Blo 323837 3159205 := bstep (se 4 (by rfl) ⟨296175, by rfl⟩ : syracuseStep 3159205 = 592351) B592351
theorem B734939 : Blo 323837 734939 := bstep (se 1 (by rfl) ⟨551204, by rfl⟩ : syracuseStep 734939 = 1102409) B1102409
theorem B735659 : Blo 323837 735659 := bstep (se 1 (by rfl) ⟨551744, by rfl⟩ : syracuseStep 735659 = 1103489) B1103489
theorem B1096307 : Blo 323837 1096307 := bstep (se 1 (by rfl) ⟨822230, by rfl⟩ : syracuseStep 1096307 = 1644461) B1644461
theorem B736055 : Blo 323837 736055 := bstep (se 1 (by rfl) ⟨552041, by rfl⟩ : syracuseStep 736055 = 1104083) B1104083
theorem B1653857 : Blo 323837 1653857 := bstep (se 2 (by rfl) ⟨620196, by rfl⟩ : syracuseStep 1653857 = 1240393) B1240393
theorem B933211 : Blo 323837 933211 := bstep (se 1 (by rfl) ⟨699908, by rfl⟩ : syracuseStep 933211 = 1399817) B1399817
theorem B737135 : Blo 323837 737135 := bstep (se 1 (by rfl) ⟨552851, by rfl⟩ : syracuseStep 737135 = 1105703) B1105703
theorem B737441 : Blo 323837 737441 := bstep (se 2 (by rfl) ⟨276540, by rfl⟩ : syracuseStep 737441 = 553081) B553081
theorem B2510327 : Blo 323837 2510327 := bstep (se 1 (by rfl) ⟨1882745, by rfl⟩ : syracuseStep 2510327 = 3765491) B3765491
theorem B839279 : Blo 323837 839279 := bstep (se 1 (by rfl) ⟨629459, by rfl⟩ : syracuseStep 839279 = 1258919) B1258919
theorem B1003735 : Blo 323837 1003735 := bstep (se 1 (by rfl) ⟨752801, by rfl⟩ : syracuseStep 1003735 = 1505603) B1505603
theorem B1855943 : Blo 323837 1855943 := bstep (se 1 (by rfl) ⟨1391957, by rfl⟩ : syracuseStep 1855943 = 2783915) B2783915
theorem B414335 : Blo 323837 414335 := bstep (se 1 (by rfl) ⟨310751, by rfl⟩ : syracuseStep 414335 = 621503) B621503
theorem B1594255 : Blo 323837 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B2774483 : Blo 323837 2774483 := bstep (se 1 (by rfl) ⟨2080862, by rfl⟩ : syracuseStep 2774483 = 4161725) B4161725
theorem B349903 : Blo 323837 349903 := bstep (se 1 (by rfl) ⟨262427, by rfl⟩ : syracuseStep 349903 = 524855) B524855
theorem B8869985 : Blo 323837 8869985 := bstep (se 2 (by rfl) ⟨3326244, by rfl⟩ : syracuseStep 8869985 = 6652489) B6652489
theorem B547175 : Blo 323837 547175 := bstep (se 1 (by rfl) ⟨410381, by rfl⟩ : syracuseStep 547175 = 820763) B820763
theorem B5037157 : Blo 323837 5037157 := bstep (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) B944467
theorem B1105055 : Blo 323837 1105055 := bstep (se 1 (by rfl) ⟨828791, by rfl⟩ : syracuseStep 1105055 = 1657583) B1657583
theorem B3726647 : Blo 323837 3726647 := bstep (se 1 (by rfl) ⟨2794985, by rfl⟩ : syracuseStep 3726647 = 5589971) B5589971
theorem B1695131 : Blo 323837 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B417259 : Blo 323837 417259 := bstep (se 1 (by rfl) ⟨312944, by rfl⟩ : syracuseStep 417259 = 625889) B625889
theorem B2088449 : Blo 323837 2088449 := bstep (se 2 (by rfl) ⟨783168, by rfl⟩ : syracuseStep 2088449 = 1566337) B1566337
theorem B548383 : Blo 323837 548383 := bstep (se 1 (by rfl) ⟨411287, by rfl⟩ : syracuseStep 548383 = 822575) B822575
theorem B3956617 : Blo 323837 3956617 := bstep (se 2 (by rfl) ⟨1483731, by rfl⟩ : syracuseStep 3956617 = 2967463) B2967463
theorem B1859543 : Blo 323837 1859543 := bstep (se 1 (by rfl) ⟨1394657, by rfl⟩ : syracuseStep 1859543 = 2789315) B2789315
theorem B1762175 : Blo 323837 1762175 := bstep (se 1 (by rfl) ⟨1321631, by rfl⟩ : syracuseStep 1762175 = 2643263) B2643263
theorem B2221195 : Blo 323837 2221195 := bstep (se 1 (by rfl) ⟨1665896, by rfl⟩ : syracuseStep 2221195 = 3331793) B3331793
theorem B2090909 : Blo 323837 2090909 := bstep (se 3 (by rfl) ⟨392045, by rfl⟩ : syracuseStep 2090909 = 784091) B784091
theorem B13559795 : Blo 323837 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B485759 : Blo 323837 485759 := bstep (se 1 (by rfl) ⟨364319, by rfl⟩ : syracuseStep 485759 = 728639) B728639
theorem B486683 : Blo 323837 486683 := bstep (se 1 (by rfl) ⟨365012, by rfl⟩ : syracuseStep 486683 = 730025) B730025
theorem B486815 : Blo 323837 486815 := bstep (se 1 (by rfl) ⟨365111, by rfl⟩ : syracuseStep 486815 = 730223) B730223
theorem B585185 : Blo 323837 585185 := bstep (se 2 (by rfl) ⟨219444, by rfl⟩ : syracuseStep 585185 = 438889) B438889
theorem B6352643 : Blo 323837 6352643 := bstep (se 1 (by rfl) ⟨4764482, by rfl⟩ : syracuseStep 6352643 = 9528965) B9528965
theorem B1601471 : Blo 323837 1601471 := bstep (se 1 (by rfl) ⟨1201103, by rfl⟩ : syracuseStep 1601471 = 2402207) B2402207
theorem B618587 : Blo 323837 618587 := bstep (se 1 (by rfl) ⟨463940, by rfl⟩ : syracuseStep 618587 = 927881) B927881
theorem B1700135 : Blo 323837 1700135 := bstep (se 1 (by rfl) ⟨1275101, by rfl⟩ : syracuseStep 1700135 = 2550203) B2550203
theorem B487721 : Blo 323837 487721 := bstep (se 2 (by rfl) ⟨182895, by rfl⟩ : syracuseStep 487721 = 365791) B365791
theorem B323999 : Blo 323837 323999 := bstep (se 1 (by rfl) ⟨242999, by rfl⟩ : syracuseStep 323999 = 485999) B485999
theorem B324031 : Blo 323837 324031 := bstep (se 1 (by rfl) ⟨243023, by rfl⟩ : syracuseStep 324031 = 486047) B486047
theorem B324335 : Blo 323837 324335 := bstep (se 1 (by rfl) ⟨243251, by rfl⟩ : syracuseStep 324335 = 486503) B486503
theorem B1176367 : Blo 323837 1176367 := bstep (se 1 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 1176367 = 1764551) B1764551
theorem B324575 : Blo 323837 324575 := bstep (se 1 (by rfl) ⟨243431, by rfl⟩ : syracuseStep 324575 = 486863) B486863
theorem B324711 : Blo 323837 324711 := bstep (se 1 (by rfl) ⟨243533, by rfl⟩ : syracuseStep 324711 = 487067) B487067
theorem B488585 : Blo 323837 488585 := bstep (se 2 (by rfl) ⟨183219, by rfl⟩ : syracuseStep 488585 = 366439) B366439
theorem B33092813 : Blo 323837 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B5928227 : Blo 323837 5928227 := bstep (se 1 (by rfl) ⟨4446170, by rfl⟩ : syracuseStep 5928227 = 8892341) B8892341
theorem B325023 : Blo 323837 325023 := bstep (se 1 (by rfl) ⟨243767, by rfl⟩ : syracuseStep 325023 = 487535) B487535
theorem B488987 : Blo 323837 488987 := bstep (se 1 (by rfl) ⟨366740, by rfl⟩ : syracuseStep 488987 = 733481) B733481
theorem B1865375 : Blo 323837 1865375 := bstep (se 1 (by rfl) ⟨1399031, by rfl⟩ : syracuseStep 1865375 = 2798063) B2798063
theorem B489371 : Blo 323837 489371 := bstep (se 1 (by rfl) ⟨367028, by rfl⟩ : syracuseStep 489371 = 734057) B734057
theorem B325759 : Blo 323837 325759 := bstep (se 1 (by rfl) ⟨244319, by rfl⟩ : syracuseStep 325759 = 488639) B488639
theorem B489983 : Blo 323837 489983 := bstep (se 1 (by rfl) ⟨367487, by rfl⟩ : syracuseStep 489983 = 734975) B734975
theorem B326463 : Blo 323837 326463 := bstep (se 1 (by rfl) ⟨244847, by rfl⟩ : syracuseStep 326463 = 489695) B489695
theorem B490343 : Blo 323837 490343 := bstep (se 1 (by rfl) ⟨367757, by rfl⟩ : syracuseStep 490343 = 735515) B735515
theorem B490367 : Blo 323837 490367 := bstep (se 1 (by rfl) ⟨367775, by rfl⟩ : syracuseStep 490367 = 735551) B735551
theorem B326719 : Blo 323837 326719 := bstep (se 1 (by rfl) ⟨245039, by rfl⟩ : syracuseStep 326719 = 490079) B490079
theorem B326759 : Blo 323837 326759 := bstep (se 1 (by rfl) ⟨245069, by rfl⟩ : syracuseStep 326759 = 490139) B490139
theorem B326783 : Blo 323837 326783 := bstep (se 1 (by rfl) ⟨245087, by rfl⟩ : syracuseStep 326783 = 490175) B490175
theorem B9403553 : Blo 323837 9403553 := bstep (se 2 (by rfl) ⟨3526332, by rfl⟩ : syracuseStep 9403553 = 7052665) B7052665
theorem B326907 : Blo 323837 326907 := bstep (se 1 (by rfl) ⟨245180, by rfl⟩ : syracuseStep 326907 = 490361) B490361
theorem B326939 : Blo 323837 326939 := bstep (se 1 (by rfl) ⟨245204, by rfl⟩ : syracuseStep 326939 = 490409) B490409
theorem B327039 : Blo 323837 327039 := bstep (se 1 (by rfl) ⟨245279, by rfl⟩ : syracuseStep 327039 = 490559) B490559
theorem B1670557 : Blo 323837 1670557 := bstep (se 3 (by rfl) ⟨313229, by rfl⟩ : syracuseStep 1670557 = 626459) B626459
theorem B327071 : Blo 323837 327071 := bstep (se 1 (by rfl) ⟨245303, by rfl⟩ : syracuseStep 327071 = 490607) B490607
theorem B327195 : Blo 323837 327195 := bstep (se 1 (by rfl) ⟨245396, by rfl⟩ : syracuseStep 327195 = 490793) B490793
theorem B327215 : Blo 323837 327215 := bstep (se 1 (by rfl) ⟨245411, by rfl⟩ : syracuseStep 327215 = 490823) B490823
theorem B327743 : Blo 323837 327743 := bstep (se 1 (by rfl) ⟨245807, by rfl⟩ : syracuseStep 327743 = 491615) B491615
theorem B491627 : Blo 323837 491627 := bstep (se 1 (by rfl) ⟨368720, by rfl⟩ : syracuseStep 491627 = 737441) B737441
theorem B327791 : Blo 323837 327791 := bstep (se 1 (by rfl) ⟨245843, by rfl⟩ : syracuseStep 327791 = 491687) B491687
theorem B1049851 : Blo 323837 1049851 := bstep (se 1 (by rfl) ⟨787388, by rfl⟩ : syracuseStep 1049851 = 1574777) B1574777
theorem B7670051 : Blo 323837 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B1673551 : Blo 323837 1673551 := bstep (se 1 (by rfl) ⟨1255163, by rfl⟩ : syracuseStep 1673551 = 2510327) B2510327
theorem B461423 : Blo 323837 461423 := bstep (se 1 (by rfl) ⟨346067, by rfl⟩ : syracuseStep 461423 = 692135) B692135
theorem B88247501 : Blo 323837 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B1642679 : Blo 323837 1642679 := bstep (se 1 (by rfl) ⟨1232009, by rfl⟩ : syracuseStep 1642679 = 2464019) B2464019
theorem B364783 : Blo 323837 364783 := bstep (se 1 (by rfl) ⟨273587, by rfl⟩ : syracuseStep 364783 = 547175) B547175
theorem B3807323 : Blo 323837 3807323 := bstep (se 1 (by rfl) ⟨2855492, by rfl⟩ : syracuseStep 3807323 = 5710985) B5710985
theorem B16849093 : Blo 323837 16849093 := bstep (se 4 (by rfl) ⟨1579602, by rfl⟩ : syracuseStep 16849093 = 3159205) B3159205
theorem B4235095 : Blo 323837 4235095 := bstep (se 1 (by rfl) ⟨3176321, by rfl⟩ : syracuseStep 4235095 = 6352643) B6352643
theorem B925921 : Blo 323837 925921 := bstep (se 2 (by rfl) ⟨347220, by rfl⟩ : syracuseStep 925921 = 694441) B694441
theorem B2238077 : Blo 323837 2238077 := bstep (se 3 (by rfl) ⟨419639, by rfl⟩ : syracuseStep 2238077 = 839279) B839279
theorem B730871 : Blo 323837 730871 := bstep (se 1 (by rfl) ⟨548153, by rfl⟩ : syracuseStep 730871 = 1096307) B1096307
theorem B731177 : Blo 323837 731177 := bstep (se 2 (by rfl) ⟨274191, by rfl⟩ : syracuseStep 731177 = 548383) B548383
theorem B6269035 : Blo 323837 6269035 := bstep (se 1 (by rfl) ⟨4701776, by rfl⟩ : syracuseStep 6269035 = 9403553) B9403553
theorem B1845737 : Blo 323837 1845737 := bstep (se 2 (by rfl) ⟨692151, by rfl⟩ : syracuseStep 1845737 = 1384303) B1384303
theorem B4270589 : Blo 323837 4270589 := bstep (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) B1601471
theorem B2075327 : Blo 323837 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B5353253 : Blo 323837 5353253 := bstep (se 4 (by rfl) ⟨501867, by rfl⟩ : syracuseStep 5353253 = 1003735) B1003735
theorem B2961593 : Blo 323837 2961593 := bstep (se 2 (by rfl) ⟨1110597, by rfl⟩ : syracuseStep 2961593 = 2221195) B2221195
theorem B1094255 : Blo 323837 1094255 := bstep (se 1 (by rfl) ⟨820691, by rfl⟩ : syracuseStep 1094255 = 1641383) B1641383
theorem B1094363 : Blo 323837 1094363 := bstep (se 1 (by rfl) ⟨820772, by rfl⟩ : syracuseStep 1094363 = 1641545) B1641545
theorem B4699133 : Blo 323837 4699133 := bstep (se 3 (by rfl) ⟨881087, by rfl⟩ : syracuseStep 4699133 = 1762175) B1762175
theorem B1849655 : Blo 323837 1849655 := bstep (se 1 (by rfl) ⟨1387241, by rfl⟩ : syracuseStep 1849655 = 2774483) B2774483
theorem B1096361 : Blo 323837 1096361 := bstep (se 2 (by rfl) ⟨411135, by rfl⟩ : syracuseStep 1096361 = 822271) B822271
theorem B5913323 : Blo 323837 5913323 := bstep (se 1 (by rfl) ⟨4434992, by rfl⟩ : syracuseStep 5913323 = 8869985) B8869985
theorem B2080043 : Blo 323837 2080043 := bstep (se 1 (by rfl) ⟨1560032, by rfl⟩ : syracuseStep 2080043 = 3120065) B3120065
theorem B736703 : Blo 323837 736703 := bstep (se 1 (by rfl) ⟨552527, by rfl⟩ : syracuseStep 736703 = 1105055) B1105055
theorem B1130087 : Blo 323837 1130087 := bstep (se 1 (by rfl) ⟨847565, by rfl⟩ : syracuseStep 1130087 = 1695131) B1695131
theorem B1392299 : Blo 323837 1392299 := bstep (se 1 (by rfl) ⟨1044224, by rfl⟩ : syracuseStep 1392299 = 2088449) B2088449
theorem B2343167 : Blo 323837 2343167 := bstep (se 1 (by rfl) ⟨1757375, by rfl⟩ : syracuseStep 2343167 = 3514751) B3514751
theorem B3981919 : Blo 323837 3981919 := bstep (se 1 (by rfl) ⟨2986439, by rfl⟩ : syracuseStep 3981919 = 5972879) B5972879
theorem B1393939 : Blo 323837 1393939 := bstep (se 1 (by rfl) ⟨1045454, by rfl⟩ : syracuseStep 1393939 = 2090909) B2090909
theorem B1557863 : Blo 323837 1557863 := bstep (se 1 (by rfl) ⟨1168397, by rfl⟩ : syracuseStep 1557863 = 2336795) B2336795
theorem B2345183 : Blo 323837 2345183 := bstep (se 1 (by rfl) ⟨1758887, by rfl⟩ : syracuseStep 2345183 = 3517775) B3517775
theorem B412391 : Blo 323837 412391 := bstep (se 1 (by rfl) ⟨309293, by rfl⟩ : syracuseStep 412391 = 618587) B618587
theorem B1133423 : Blo 323837 1133423 := bstep (se 1 (by rfl) ⟨850067, by rfl⟩ : syracuseStep 1133423 = 1700135) B1700135
theorem B3952151 : Blo 323837 3952151 := bstep (se 1 (by rfl) ⟨2964113, by rfl⟩ : syracuseStep 3952151 = 5928227) B5928227
theorem B1101545 : Blo 323837 1101545 := bstep (se 2 (by rfl) ⟨413079, by rfl⟩ : syracuseStep 1101545 = 826159) B826159
theorem B1560493 : Blo 323837 1560493 := bstep (se 3 (by rfl) ⟨292592, by rfl⟩ : syracuseStep 1560493 = 585185) B585185
theorem B1102571 : Blo 323837 1102571 := bstep (se 1 (by rfl) ⟨826928, by rfl⟩ : syracuseStep 1102571 = 1653857) B1653857
theorem B1102841 : Blo 323837 1102841 := bstep (se 2 (by rfl) ⟨413565, by rfl⟩ : syracuseStep 1102841 = 827131) B827131
theorem B1857127 : Blo 323837 1857127 := bstep (se 1 (by rfl) ⟨1392845, by rfl⟩ : syracuseStep 1857127 = 2785691) B2785691
theorem B275929811 : Blo 323837 275929811 := bstep (se 1 (by rfl) ⟨206947358, by rfl⟩ : syracuseStep 275929811 = 413894717) B413894717
theorem B1104893 : Blo 323837 1104893 := bstep (se 3 (by rfl) ⟨207167, by rfl⟩ : syracuseStep 1104893 = 414335) B414335
theorem B1105001 : Blo 323837 1105001 := bstep (se 2 (by rfl) ⟨414375, by rfl⟩ : syracuseStep 1105001 = 828751) B828751
theorem B941743 : Blo 323837 941743 := bstep (se 1 (by rfl) ⟨706307, by rfl⟩ : syracuseStep 941743 = 1412615) B1412615
theorem B1237295 : Blo 323837 1237295 := bstep (se 1 (by rfl) ⟨927971, by rfl⟩ : syracuseStep 1237295 = 1855943) B1855943
theorem B549983 : Blo 323837 549983 := bstep (se 1 (by rfl) ⟨412487, by rfl⟩ : syracuseStep 549983 = 824975) B824975
theorem B2484431 : Blo 323837 2484431 := bstep (se 1 (by rfl) ⟨1863323, by rfl⟩ : syracuseStep 2484431 = 3726647) B3726647
theorem B551515 : Blo 323837 551515 := bstep (se 1 (by rfl) ⟨413636, by rfl⟩ : syracuseStep 551515 = 827273) B827273
theorem B1239695 : Blo 323837 1239695 := bstep (se 1 (by rfl) ⟨929771, by rfl⟩ : syracuseStep 1239695 = 1859543) B1859543
theorem B486215 : Blo 323837 486215 := bstep (se 1 (by rfl) ⟨364661, by rfl⟩ : syracuseStep 486215 = 729323) B729323
theorem B71331191 : Blo 323837 71331191 := bstep (se 1 (by rfl) ⟨53498393, by rfl⟩ : syracuseStep 71331191 = 106996787) B106996787
theorem B486911 : Blo 323837 486911 := bstep (se 1 (by rfl) ⟨365183, by rfl⟩ : syracuseStep 486911 = 730367) B730367
theorem B487049 : Blo 323837 487049 := bstep (se 2 (by rfl) ⟨182643, by rfl⟩ : syracuseStep 487049 = 365287) B365287
theorem B1568489 : Blo 323837 1568489 := bstep (se 2 (by rfl) ⟨588183, by rfl⟩ : syracuseStep 1568489 = 1176367) B1176367
theorem B2125673 : Blo 323837 2125673 := bstep (se 2 (by rfl) ⟨797127, by rfl⟩ : syracuseStep 2125673 = 1594255) B1594255
theorem B9039863 : Blo 323837 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B487487 : Blo 323837 487487 := bstep (se 1 (by rfl) ⟨365615, by rfl⟩ : syracuseStep 487487 = 731231) B731231
theorem B487583 : Blo 323837 487583 := bstep (se 1 (by rfl) ⟨365687, by rfl⟩ : syracuseStep 487583 = 731375) B731375
theorem B323839 : Blo 323837 323839 := bstep (se 1 (by rfl) ⟨242879, by rfl⟩ : syracuseStep 323839 = 485759) B485759
theorem B1208603 : Blo 323837 1208603 := bstep (se 1 (by rfl) ⟨906452, by rfl⟩ : syracuseStep 1208603 = 1812905) B1812905
theorem B4747643 : Blo 323837 4747643 := bstep (se 1 (by rfl) ⟨3560732, by rfl⟩ : syracuseStep 4747643 = 7121465) B7121465
theorem B488063 : Blo 323837 488063 := bstep (se 1 (by rfl) ⟨366047, by rfl⟩ : syracuseStep 488063 = 732095) B732095
theorem B324455 : Blo 323837 324455 := bstep (se 1 (by rfl) ⟨243341, by rfl⟩ : syracuseStep 324455 = 486683) B486683
theorem B324543 : Blo 323837 324543 := bstep (se 1 (by rfl) ⟨243407, by rfl⟩ : syracuseStep 324543 = 486815) B486815
theorem B325147 : Blo 323837 325147 := bstep (se 1 (by rfl) ⟨243860, by rfl⟩ : syracuseStep 325147 = 487721) B487721
theorem B489023 : Blo 323837 489023 := bstep (se 1 (by rfl) ⟨366767, by rfl⟩ : syracuseStep 489023 = 733535) B733535
theorem B489449 : Blo 323837 489449 := bstep (se 2 (by rfl) ⟨183543, by rfl⟩ : syracuseStep 489449 = 367087) B367087
theorem B325723 : Blo 323837 325723 := bstep (se 1 (by rfl) ⟨244292, by rfl⟩ : syracuseStep 325723 = 488585) B488585
theorem B325991 : Blo 323837 325991 := bstep (se 1 (by rfl) ⟨244493, by rfl⟩ : syracuseStep 325991 = 488987) B488987
theorem B1866149 : Blo 323837 1866149 := bstep (se 4 (by rfl) ⟨174951, by rfl⟩ : syracuseStep 1866149 = 349903) B349903
theorem B1243583 : Blo 323837 1243583 := bstep (se 1 (by rfl) ⟨932687, by rfl⟩ : syracuseStep 1243583 = 1865375) B1865375
theorem B489959 : Blo 323837 489959 := bstep (se 1 (by rfl) ⟨367469, by rfl⟩ : syracuseStep 489959 = 734939) B734939
theorem B326247 : Blo 323837 326247 := bstep (se 1 (by rfl) ⟨244685, by rfl⟩ : syracuseStep 326247 = 489371) B489371
theorem B6716209 : Blo 323837 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B490439 : Blo 323837 490439 := bstep (se 1 (by rfl) ⟨367829, by rfl⟩ : syracuseStep 490439 = 735659) B735659
theorem B326655 : Blo 323837 326655 := bstep (se 1 (by rfl) ⟨244991, by rfl⟩ : syracuseStep 326655 = 489983) B489983
theorem B1244281 : Blo 323837 1244281 := bstep (se 2 (by rfl) ⟨466605, by rfl⟩ : syracuseStep 1244281 = 933211) B933211
theorem B490703 : Blo 323837 490703 := bstep (se 1 (by rfl) ⟨368027, by rfl⟩ : syracuseStep 490703 = 736055) B736055
theorem B2227409 : Blo 323837 2227409 := bstep (se 2 (by rfl) ⟨835278, by rfl⟩ : syracuseStep 2227409 = 1670557) B1670557
theorem B326895 : Blo 323837 326895 := bstep (se 1 (by rfl) ⟨245171, by rfl⟩ : syracuseStep 326895 = 490343) B490343
theorem B326911 : Blo 323837 326911 := bstep (se 1 (by rfl) ⟨245183, by rfl⟩ : syracuseStep 326911 = 490367) B490367
theorem B556345 : Blo 323837 556345 := bstep (se 2 (by rfl) ⟨208629, by rfl⟩ : syracuseStep 556345 = 417259) B417259
theorem B5275489 : Blo 323837 5275489 := bstep (se 2 (by rfl) ⟨1978308, by rfl⟩ : syracuseStep 5275489 = 3956617) B3956617
theorem B491423 : Blo 323837 491423 := bstep (se 1 (by rfl) ⟨368567, by rfl⟩ : syracuseStep 491423 = 737135) B737135
theorem B327751 : Blo 323837 327751 := bstep (se 1 (by rfl) ⟨245813, by rfl⟩ : syracuseStep 327751 = 491627) B491627
theorem B5309225 : Blo 323837 5309225 := bstep (se 2 (by rfl) ⟨1990959, by rfl⟩ : syracuseStep 5309225 = 3981919) B3981919
theorem B5113367 : Blo 323837 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B755615 : Blo 323837 755615 := bstep (se 1 (by rfl) ⟨566711, by rfl⟩ : syracuseStep 755615 = 1133423) B1133423
theorem B8358713 : Blo 323837 8358713 := bstep (se 2 (by rfl) ⟨3134517, by rfl⟩ : syracuseStep 8358713 = 6269035) B6269035
theorem B2231401 : Blo 323837 2231401 := bstep (se 2 (by rfl) ⟨836775, by rfl⟩ : syracuseStep 2231401 = 1673551) B1673551
theorem B5968205 : Blo 323837 5968205 := bstep (se 3 (by rfl) ⟨1119038, by rfl⟩ : syracuseStep 5968205 = 2238077) B2238077
theorem B824863 : Blo 323837 824863 := bstep (se 1 (by rfl) ⟨618647, by rfl⟩ : syracuseStep 824863 = 1237295) B1237295
theorem B366655 : Blo 323837 366655 := bstep (se 1 (by rfl) ⟨274991, by rfl⟩ : syracuseStep 366655 = 549983) B549983
theorem B826463 : Blo 323837 826463 := bstep (se 1 (by rfl) ⟨619847, by rfl⟩ : syracuseStep 826463 = 1239695) B1239695
theorem B1383551 : Blo 323837 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B47554127 : Blo 323837 47554127 := bstep (se 1 (by rfl) ⟨35665595, by rfl⟩ : syracuseStep 47554127 = 71331191) B71331191
theorem B1417115 : Blo 323837 1417115 := bstep (se 1 (by rfl) ⟨1062836, by rfl⟩ : syracuseStep 1417115 = 2125673) B2125673
theorem B1974395 : Blo 323837 1974395 := bstep (se 1 (by rfl) ⟨1480796, by rfl⟩ : syracuseStep 1974395 = 2961593) B2961593
theorem B729503 : Blo 323837 729503 := bstep (se 1 (by rfl) ⟨547127, by rfl⟩ : syracuseStep 729503 = 1094255) B1094255
theorem B729575 : Blo 323837 729575 := bstep (se 1 (by rfl) ⟨547181, by rfl⟩ : syracuseStep 729575 = 1094363) B1094363
theorem B8954945 : Blo 323837 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B829055 : Blo 323837 829055 := bstep (se 1 (by rfl) ⟨621791, by rfl⟩ : syracuseStep 829055 = 1243583) B1243583
theorem B730907 : Blo 323837 730907 := bstep (se 1 (by rfl) ⟨548180, by rfl⟩ : syracuseStep 730907 = 1096361) B1096361
theorem B3942215 : Blo 323837 3942215 := bstep (se 1 (by rfl) ⟨2956661, by rfl⟩ : syracuseStep 3942215 = 5913323) B5913323
theorem B1484939 : Blo 323837 1484939 := bstep (se 1 (by rfl) ⟨1113704, by rfl⟩ : syracuseStep 1484939 = 2227409) B2227409
theorem B1386695 : Blo 323837 1386695 := bstep (se 1 (by rfl) ⟨1040021, by rfl⟩ : syracuseStep 1386695 = 2080043) B2080043
theorem B1255657 : Blo 323837 1255657 := bstep (se 2 (by rfl) ⟨470871, by rfl⟩ : syracuseStep 1255657 = 941743) B941743
theorem B928199 : Blo 323837 928199 := bstep (se 1 (by rfl) ⟨696149, by rfl⟩ : syracuseStep 928199 = 1392299) B1392299
theorem B5646793 : Blo 323837 5646793 := bstep (se 2 (by rfl) ⟨2117547, by rfl⟩ : syracuseStep 5646793 = 4235095) B4235095
theorem B58831667 : Blo 323837 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B2634767 : Blo 323837 2634767 := bstep (se 1 (by rfl) ⟨1976075, by rfl⟩ : syracuseStep 2634767 = 3952151) B3952151
theorem B734363 : Blo 323837 734363 := bstep (se 1 (by rfl) ⟨550772, by rfl⟩ : syracuseStep 734363 = 1101545) B1101545
theorem B1095119 : Blo 323837 1095119 := bstep (se 1 (by rfl) ⟨821339, by rfl⟩ : syracuseStep 1095119 = 1642679) B1642679
theorem B735047 : Blo 323837 735047 := bstep (se 1 (by rfl) ⟨551285, by rfl⟩ : syracuseStep 735047 = 1102571) B1102571
theorem B735227 : Blo 323837 735227 := bstep (se 1 (by rfl) ⟨551420, by rfl⟩ : syracuseStep 735227 = 1102841) B1102841
theorem B735353 : Blo 323837 735353 := bstep (se 2 (by rfl) ⟨275757, by rfl⟩ : syracuseStep 735353 = 551515) B551515
theorem B2538215 : Blo 323837 2538215 := bstep (se 1 (by rfl) ⟨1903661, by rfl⟩ : syracuseStep 2538215 = 3807323) B3807323
theorem B736595 : Blo 323837 736595 := bstep (se 1 (by rfl) ⟨552446, by rfl⟩ : syracuseStep 736595 = 1104893) B1104893
theorem B736667 : Blo 323837 736667 := bstep (se 1 (by rfl) ⟨552500, by rfl⟩ : syracuseStep 736667 = 1105001) B1105001
theorem B2080657 : Blo 323837 2080657 := bstep (se 2 (by rfl) ⟨780246, by rfl⟩ : syracuseStep 2080657 = 1560493) B1560493
theorem B1656287 : Blo 323837 1656287 := bstep (se 1 (by rfl) ⟨1242215, by rfl⟩ : syracuseStep 1656287 = 2484431) B2484431
theorem B1230461 : Blo 323837 1230461 := bstep (se 3 (by rfl) ⟨230711, by rfl⟩ : syracuseStep 1230461 = 461423) B461423
theorem B1230491 : Blo 323837 1230491 := bstep (se 1 (by rfl) ⟨922868, by rfl⟩ : syracuseStep 1230491 = 1845737) B1845737
theorem B1099709 : Blo 323837 1099709 := bstep (se 3 (by rfl) ⟨206195, by rfl⟩ : syracuseStep 1099709 = 412391) B412391
theorem B2476169 : Blo 323837 2476169 := bstep (se 2 (by rfl) ⟨928563, by rfl⟩ : syracuseStep 2476169 = 1857127) B1857127
theorem B805735 : Blo 323837 805735 := bstep (se 1 (by rfl) ⟨604301, by rfl⟩ : syracuseStep 805735 = 1208603) B1208603
theorem B3165095 : Blo 323837 3165095 := bstep (se 1 (by rfl) ⟨2373821, by rfl⟩ : syracuseStep 3165095 = 4747643) B4747643
theorem B22465457 : Blo 323837 22465457 := bstep (se 2 (by rfl) ⟨8424546, by rfl⟩ : syracuseStep 22465457 = 16849093) B16849093
theorem B3132755 : Blo 323837 3132755 := bstep (se 1 (by rfl) ⟨2349566, by rfl⟩ : syracuseStep 3132755 = 4699133) B4699133
theorem B1659041 : Blo 323837 1659041 := bstep (se 2 (by rfl) ⟨622140, by rfl⟩ : syracuseStep 1659041 = 1244281) B1244281
theorem B1233103 : Blo 323837 1233103 := bstep (se 1 (by rfl) ⟨924827, by rfl⟩ : syracuseStep 1233103 = 1849655) B1849655
theorem B741793 : Blo 323837 741793 := bstep (se 2 (by rfl) ⟨278172, by rfl⟩ : syracuseStep 741793 = 556345) B556345
theorem B4182637 : Blo 323837 4182637 := bstep (se 3 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 4182637 = 1568489) B1568489
theorem B7033985 : Blo 323837 7033985 := bstep (se 2 (by rfl) ⟨2637744, by rfl⟩ : syracuseStep 7033985 = 5275489) B5275489
theorem B1562111 : Blo 323837 1562111 := bstep (se 1 (by rfl) ⟨1171583, by rfl⟩ : syracuseStep 1562111 = 2343167) B2343167
theorem B1234561 : Blo 323837 1234561 := bstep (se 2 (by rfl) ⟨462960, by rfl⟩ : syracuseStep 1234561 = 925921) B925921
theorem B1038575 : Blo 323837 1038575 := bstep (se 1 (by rfl) ⟨778931, by rfl⟩ : syracuseStep 1038575 = 1557863) B1557863
theorem B1563455 : Blo 323837 1563455 := bstep (se 1 (by rfl) ⟨1172591, by rfl⟩ : syracuseStep 1563455 = 2345183) B2345183
theorem B1399801 : Blo 323837 1399801 := bstep (se 2 (by rfl) ⟨524925, by rfl⟩ : syracuseStep 1399801 = 1049851) B1049851
theorem B1858585 : Blo 323837 1858585 := bstep (se 2 (by rfl) ⟨696969, by rfl⟩ : syracuseStep 1858585 = 1393939) B1393939
theorem B183953207 : Blo 323837 183953207 := bstep (se 1 (by rfl) ⟨137964905, by rfl⟩ : syracuseStep 183953207 = 275929811) B275929811
theorem B486377 : Blo 323837 486377 := bstep (se 2 (by rfl) ⟨182391, by rfl⟩ : syracuseStep 486377 = 364783) B364783
theorem B487247 : Blo 323837 487247 := bstep (se 1 (by rfl) ⟨365435, by rfl⟩ : syracuseStep 487247 = 730871) B730871
theorem B487451 : Blo 323837 487451 := bstep (se 1 (by rfl) ⟨365588, by rfl⟩ : syracuseStep 487451 = 731177) B731177
theorem B2847059 : Blo 323837 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B324143 : Blo 323837 324143 := bstep (se 1 (by rfl) ⟨243107, by rfl⟩ : syracuseStep 324143 = 486215) B486215
theorem B324607 : Blo 323837 324607 := bstep (se 1 (by rfl) ⟨243455, by rfl⟩ : syracuseStep 324607 = 486911) B486911
theorem B324699 : Blo 323837 324699 := bstep (se 1 (by rfl) ⟨243524, by rfl⟩ : syracuseStep 324699 = 487049) B487049
theorem B3568835 : Blo 323837 3568835 := bstep (se 1 (by rfl) ⟨2676626, by rfl⟩ : syracuseStep 3568835 = 5353253) B5353253
theorem B6026575 : Blo 323837 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B324991 : Blo 323837 324991 := bstep (se 1 (by rfl) ⟨243743, by rfl⟩ : syracuseStep 324991 = 487487) B487487
theorem B325055 : Blo 323837 325055 := bstep (se 1 (by rfl) ⟨243791, by rfl⟩ : syracuseStep 325055 = 487583) B487583
theorem B325375 : Blo 323837 325375 := bstep (se 1 (by rfl) ⟨244031, by rfl⟩ : syracuseStep 325375 = 488063) B488063
theorem B326015 : Blo 323837 326015 := bstep (se 1 (by rfl) ⟨244511, by rfl⟩ : syracuseStep 326015 = 489023) B489023
theorem B326299 : Blo 323837 326299 := bstep (se 1 (by rfl) ⟨244724, by rfl⟩ : syracuseStep 326299 = 489449) B489449
theorem B1244099 : Blo 323837 1244099 := bstep (se 1 (by rfl) ⟨933074, by rfl⟩ : syracuseStep 1244099 = 1866149) B1866149
theorem B326639 : Blo 323837 326639 := bstep (se 1 (by rfl) ⟨244979, by rfl⟩ : syracuseStep 326639 = 489959) B489959
theorem B326959 : Blo 323837 326959 := bstep (se 1 (by rfl) ⟨245219, by rfl⟩ : syracuseStep 326959 = 490439) B490439
theorem B327135 : Blo 323837 327135 := bstep (se 1 (by rfl) ⟨245351, by rfl⟩ : syracuseStep 327135 = 490703) B490703
theorem B491135 : Blo 323837 491135 := bstep (se 1 (by rfl) ⟨368351, by rfl⟩ : syracuseStep 491135 = 736703) B736703
theorem B753391 : Blo 323837 753391 := bstep (se 1 (by rfl) ⟨565043, by rfl⟩ : syracuseStep 753391 = 1130087) B1130087
theorem B327615 : Blo 323837 327615 := bstep (se 1 (by rfl) ⟨245711, by rfl⟩ : syracuseStep 327615 = 491423) B491423
theorem B3539483 : Blo 323837 3539483 := bstep (se 1 (by rfl) ⟨2654612, by rfl⟩ : syracuseStep 3539483 = 5309225) B5309225
theorem B3408911 : Blo 323837 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B820307 : Blo 323837 820307 := bstep (se 1 (by rfl) ⟨615230, by rfl⟩ : syracuseStep 820307 = 1230461) B1230461
theorem B820327 : Blo 323837 820327 := bstep (se 1 (by rfl) ⟨615245, by rfl⟩ : syracuseStep 820327 = 1230491) B1230491
theorem B5572475 : Blo 323837 5572475 := bstep (se 1 (by rfl) ⟨4179356, by rfl⟩ : syracuseStep 5572475 = 8358713) B8358713
theorem B14976971 : Blo 323837 14976971 := bstep (se 1 (by rfl) ⟨11232728, by rfl⟩ : syracuseStep 14976971 = 22465457) B22465457
theorem B1674209 : Blo 323837 1674209 := bstep (se 2 (by rfl) ⟨627828, by rfl⟩ : syracuseStep 1674209 = 1255657) B1255657
theorem B4689323 : Blo 323837 4689323 := bstep (se 1 (by rfl) ⟨3516992, by rfl⟩ : syracuseStep 4689323 = 7033985) B7033985
theorem B692383 : Blo 323837 692383 := bstep (se 1 (by rfl) ⟨519287, by rfl⟩ : syracuseStep 692383 = 1038575) B1038575
theorem B922367 : Blo 323837 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B1316263 : Blo 323837 1316263 := bstep (se 1 (by rfl) ⟨987197, by rfl⟩ : syracuseStep 1316263 = 1974395) B1974395
theorem B1644137 : Blo 323837 1644137 := bstep (se 2 (by rfl) ⟨616551, by rfl⟩ : syracuseStep 1644137 = 1233103) B1233103
theorem B989057 : Blo 323837 989057 := bstep (se 2 (by rfl) ⟨370896, by rfl⟩ : syracuseStep 989057 = 741793) B741793
theorem B5969963 : Blo 323837 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B5576849 : Blo 323837 5576849 := bstep (se 2 (by rfl) ⟨2091318, by rfl⟩ : syracuseStep 5576849 = 4182637) B4182637
theorem B2628143 : Blo 323837 2628143 := bstep (se 1 (by rfl) ⟨1971107, by rfl⟩ : syracuseStep 2628143 = 3942215) B3942215
theorem B924463 : Blo 323837 924463 := bstep (se 1 (by rfl) ⟨693347, by rfl⟩ : syracuseStep 924463 = 1386695) B1386695
theorem B8035433 : Blo 323837 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B1646081 : Blo 323837 1646081 := bstep (se 2 (by rfl) ⟨617280, by rfl⟩ : syracuseStep 1646081 = 1234561) B1234561
theorem B730079 : Blo 323837 730079 := bstep (se 1 (by rfl) ⟨547559, by rfl⟩ : syracuseStep 730079 = 1095119) B1095119
theorem B829399 : Blo 323837 829399 := bstep (se 1 (by rfl) ⟨622049, by rfl⟩ : syracuseStep 829399 = 1244099) B1244099
theorem B3778973 : Blo 323837 3778973 := bstep (se 3 (by rfl) ⟨708557, by rfl⟩ : syracuseStep 3778973 = 1417115) B1417115
theorem B503743 : Blo 323837 503743 := bstep (se 1 (by rfl) ⟨377807, by rfl⟩ : syracuseStep 503743 = 755615) B755615
theorem B733139 : Blo 323837 733139 := bstep (se 1 (by rfl) ⟨549854, by rfl⟩ : syracuseStep 733139 = 1099709) B1099709
theorem B1650779 : Blo 323837 1650779 := bstep (se 1 (by rfl) ⟨1238084, by rfl⟩ : syracuseStep 1650779 = 2476169) B2476169
theorem B2110063 : Blo 323837 2110063 := bstep (se 1 (by rfl) ⟨1582547, by rfl⟩ : syracuseStep 2110063 = 3165095) B3165095
theorem B3978803 : Blo 323837 3978803 := bstep (se 1 (by rfl) ⟨2984102, by rfl⟩ : syracuseStep 3978803 = 5968205) B5968205
theorem B31702751 : Blo 323837 31702751 := bstep (se 1 (by rfl) ⟨23777063, by rfl⟩ : syracuseStep 31702751 = 47554127) B47554127
theorem B2475197 : Blo 323837 2475197 := bstep (se 3 (by rfl) ⟨464099, by rfl⟩ : syracuseStep 2475197 = 928199) B928199
theorem B122635471 : Blo 323837 122635471 := bstep (se 1 (by rfl) ⟨91976603, by rfl⟩ : syracuseStep 122635471 = 183953207) B183953207
theorem B1099817 : Blo 323837 1099817 := bstep (se 2 (by rfl) ⟨412431, by rfl⟩ : syracuseStep 1099817 = 824863) B824863
theorem B1756511 : Blo 323837 1756511 := bstep (se 1 (by rfl) ⟨1317383, by rfl⟩ : syracuseStep 1756511 = 2634767) B2634767
theorem B2379223 : Blo 323837 2379223 := bstep (se 1 (by rfl) ⟨1784417, by rfl⟩ : syracuseStep 2379223 = 3568835) B3568835
theorem B2478113 : Blo 323837 2478113 := bstep (se 2 (by rfl) ⟨929292, by rfl⟩ : syracuseStep 2478113 = 1858585) B1858585
theorem B1692143 : Blo 323837 1692143 := bstep (se 1 (by rfl) ⟨1269107, by rfl⟩ : syracuseStep 1692143 = 2538215) B2538215
theorem B1004521 : Blo 323837 1004521 := bstep (se 2 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 1004521 = 753391) B753391
theorem B2774209 : Blo 323837 2774209 := bstep (se 2 (by rfl) ⟨1040328, by rfl⟩ : syracuseStep 2774209 = 2080657) B2080657
theorem B1104191 : Blo 323837 1104191 := bstep (se 1 (by rfl) ⟨828143, by rfl⟩ : syracuseStep 1104191 = 1656287) B1656287
theorem B2088503 : Blo 323837 2088503 := bstep (se 1 (by rfl) ⟨1566377, by rfl⟩ : syracuseStep 2088503 = 3132755) B3132755
theorem B1106027 : Blo 323837 1106027 := bstep (se 1 (by rfl) ⟨829520, by rfl⟩ : syracuseStep 1106027 = 1659041) B1659041
theorem B7529057 : Blo 323837 7529057 := bstep (se 2 (by rfl) ⟨2823396, by rfl⟩ : syracuseStep 7529057 = 5646793) B5646793
theorem B1041407 : Blo 323837 1041407 := bstep (se 1 (by rfl) ⟨781055, by rfl⟩ : syracuseStep 1041407 = 1562111) B1562111
theorem B1074313 : Blo 323837 1074313 := bstep (se 2 (by rfl) ⟨402867, by rfl⟩ : syracuseStep 1074313 = 805735) B805735
theorem B2975201 : Blo 323837 2975201 := bstep (se 2 (by rfl) ⟨1115700, by rfl⟩ : syracuseStep 2975201 = 2231401) B2231401
theorem B1042303 : Blo 323837 1042303 := bstep (se 1 (by rfl) ⟨781727, by rfl⟩ : syracuseStep 1042303 = 1563455) B1563455
theorem B550975 : Blo 323837 550975 := bstep (se 1 (by rfl) ⟨413231, by rfl⟩ : syracuseStep 550975 = 826463) B826463
theorem B486335 : Blo 323837 486335 := bstep (se 1 (by rfl) ⟨364751, by rfl⟩ : syracuseStep 486335 = 729503) B729503
theorem B486383 : Blo 323837 486383 := bstep (se 1 (by rfl) ⟨364787, by rfl⟩ : syracuseStep 486383 = 729575) B729575
theorem B3959837 : Blo 323837 3959837 := bstep (se 3 (by rfl) ⟨742469, by rfl⟩ : syracuseStep 3959837 = 1484939) B1484939
theorem B552703 : Blo 323837 552703 := bstep (se 1 (by rfl) ⟨414527, by rfl⟩ : syracuseStep 552703 = 829055) B829055
theorem B487271 : Blo 323837 487271 := bstep (se 1 (by rfl) ⟨365453, by rfl⟩ : syracuseStep 487271 = 730907) B730907
theorem B324251 : Blo 323837 324251 := bstep (se 1 (by rfl) ⟨243188, by rfl⟩ : syracuseStep 324251 = 486377) B486377
theorem B324831 : Blo 323837 324831 := bstep (se 1 (by rfl) ⟨243623, by rfl⟩ : syracuseStep 324831 = 487247) B487247
theorem B324967 : Blo 323837 324967 := bstep (se 1 (by rfl) ⟨243725, by rfl⟩ : syracuseStep 324967 = 487451) B487451
theorem B488873 : Blo 323837 488873 := bstep (se 2 (by rfl) ⟨183327, by rfl⟩ : syracuseStep 488873 = 366655) B366655
theorem B1898039 : Blo 323837 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B39221111 : Blo 323837 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B489575 : Blo 323837 489575 := bstep (se 1 (by rfl) ⟨367181, by rfl⟩ : syracuseStep 489575 = 734363) B734363
theorem B490031 : Blo 323837 490031 := bstep (se 1 (by rfl) ⟨367523, by rfl⟩ : syracuseStep 490031 = 735047) B735047
theorem B1866401 : Blo 323837 1866401 := bstep (se 2 (by rfl) ⟨699900, by rfl⟩ : syracuseStep 1866401 = 1399801) B1399801
theorem B490151 : Blo 323837 490151 := bstep (se 1 (by rfl) ⟨367613, by rfl⟩ : syracuseStep 490151 = 735227) B735227
theorem B490235 : Blo 323837 490235 := bstep (se 1 (by rfl) ⟨367676, by rfl⟩ : syracuseStep 490235 = 735353) B735353
theorem B491063 : Blo 323837 491063 := bstep (se 1 (by rfl) ⟨368297, by rfl⟩ : syracuseStep 491063 = 736595) B736595
theorem B491111 : Blo 323837 491111 := bstep (se 1 (by rfl) ⟨368333, by rfl⟩ : syracuseStep 491111 = 736667) B736667
theorem B327423 : Blo 323837 327423 := bstep (se 1 (by rfl) ⟨245567, by rfl⟩ : syracuseStep 327423 = 491135) B491135
theorem B2359655 : Blo 323837 2359655 := bstep (se 1 (by rfl) ⟨1769741, by rfl⟩ : syracuseStep 2359655 = 3539483) B3539483
theorem B163513961 : Blo 323837 163513961 := bstep (se 2 (by rfl) ⟨61317735, by rfl⟩ : syracuseStep 163513961 = 122635471) B122635471
theorem B2459645 : Blo 323837 2459645 := bstep (se 3 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 2459645 = 922367) B922367
theorem B923177 : Blo 323837 923177 := bstep (se 2 (by rfl) ⟨346191, by rfl⟩ : syracuseStep 923177 = 692383) B692383
theorem B5019371 : Blo 323837 5019371 := bstep (se 1 (by rfl) ⟨3764528, by rfl⟩ : syracuseStep 5019371 = 7529057) B7529057
theorem B694271 : Blo 323837 694271 := bstep (se 1 (by rfl) ⟨520703, by rfl⟩ : syracuseStep 694271 = 1041407) B1041407
theorem B4464557 : Blo 323837 4464557 := bstep (se 3 (by rfl) ⟨837104, by rfl⟩ : syracuseStep 4464557 = 1674209) B1674209
theorem B2272607 : Blo 323837 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B1650131 : Blo 323837 1650131 := bstep (se 1 (by rfl) ⟨1237598, by rfl⟩ : syracuseStep 1650131 = 2475197) B2475197
theorem B3714983 : Blo 323837 3714983 := bstep (se 1 (by rfl) ⟨2786237, by rfl⟩ : syracuseStep 3714983 = 5572475) B5572475
theorem B733211 : Blo 323837 733211 := bstep (se 1 (by rfl) ⟨549908, by rfl⟩ : syracuseStep 733211 = 1099817) B1099817
theorem B1093769 : Blo 323837 1093769 := bstep (se 2 (by rfl) ⟨410163, by rfl⟩ : syracuseStep 1093769 = 820327) B820327
theorem B3126215 : Blo 323837 3126215 := bstep (se 1 (by rfl) ⟨2344661, by rfl⟩ : syracuseStep 3126215 = 4689323) B4689323
theorem B1389737 : Blo 323837 1389737 := bstep (se 2 (by rfl) ⟨521151, by rfl⟩ : syracuseStep 1389737 = 1042303) B1042303
theorem B1652075 : Blo 323837 1652075 := bstep (se 1 (by rfl) ⟨1239056, by rfl⟩ : syracuseStep 1652075 = 2478113) B2478113
theorem B734633 : Blo 323837 734633 := bstep (se 2 (by rfl) ⟨275487, by rfl⟩ : syracuseStep 734633 = 550975) B550975
theorem B1128095 : Blo 323837 1128095 := bstep (se 1 (by rfl) ⟨846071, by rfl⟩ : syracuseStep 1128095 = 1692143) B1692143
theorem B1096091 : Blo 323837 1096091 := bstep (se 1 (by rfl) ⟨822068, by rfl⟩ : syracuseStep 1096091 = 1644137) B1644137
theorem B3979975 : Blo 323837 3979975 := bstep (se 1 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 3979975 = 5969963) B5969963
theorem B3717899 : Blo 323837 3717899 := bstep (se 1 (by rfl) ⟨2788424, by rfl⟩ : syracuseStep 3717899 = 5576849) B5576849
theorem B5061437 : Blo 323837 5061437 := bstep (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) B1898039
theorem B736127 : Blo 323837 736127 := bstep (se 1 (by rfl) ⟨552095, by rfl⟩ : syracuseStep 736127 = 1104191) B1104191
theorem B1752095 : Blo 323837 1752095 := bstep (se 1 (by rfl) ⟨1314071, by rfl⟩ : syracuseStep 1752095 = 2628143) B2628143
theorem B5356955 : Blo 323837 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B736937 : Blo 323837 736937 := bstep (se 2 (by rfl) ⟨276351, by rfl⟩ : syracuseStep 736937 = 552703) B552703
theorem B1097387 : Blo 323837 1097387 := bstep (se 1 (by rfl) ⟨823040, by rfl⟩ : syracuseStep 1097387 = 1646081) B1646081
theorem B2637485 : Blo 323837 2637485 := bstep (se 3 (by rfl) ⟨494528, by rfl⟩ : syracuseStep 2637485 = 989057) B989057
theorem B1392335 : Blo 323837 1392335 := bstep (se 1 (by rfl) ⟨1044251, by rfl⟩ : syracuseStep 1392335 = 2088503) B2088503
theorem B671657 : Blo 323837 671657 := bstep (se 2 (by rfl) ⟨251871, by rfl⟩ : syracuseStep 671657 = 503743) B503743
theorem B737351 : Blo 323837 737351 := bstep (se 1 (by rfl) ⟨553013, by rfl⟩ : syracuseStep 737351 = 1106027) B1106027
theorem B1983467 : Blo 323837 1983467 := bstep (se 1 (by rfl) ⟨1487600, by rfl⟩ : syracuseStep 1983467 = 2975201) B2975201
theorem B1755017 : Blo 323837 1755017 := bstep (se 2 (by rfl) ⟨658131, by rfl⟩ : syracuseStep 1755017 = 1316263) B1316263
theorem B2639891 : Blo 323837 2639891 := bstep (se 1 (by rfl) ⟨1979918, by rfl⟩ : syracuseStep 2639891 = 3959837) B3959837
theorem B1100519 : Blo 323837 1100519 := bstep (se 1 (by rfl) ⟨825389, by rfl⟩ : syracuseStep 1100519 = 1650779) B1650779
theorem B1232617 : Blo 323837 1232617 := bstep (se 2 (by rfl) ⟨462231, by rfl⟩ : syracuseStep 1232617 = 924463) B924463
theorem B546871 : Blo 323837 546871 := bstep (se 1 (by rfl) ⟨410153, by rfl⟩ : syracuseStep 546871 = 820307) B820307
theorem B9984647 : Blo 323837 9984647 := bstep (se 1 (by rfl) ⟨7488485, by rfl⟩ : syracuseStep 9984647 = 14976971) B14976971
theorem B1432417 : Blo 323837 1432417 := bstep (se 2 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 1432417 = 1074313) B1074313
theorem B1171007 : Blo 323837 1171007 := bstep (se 1 (by rfl) ⟨878255, by rfl⟩ : syracuseStep 1171007 = 1756511) B1756511
theorem B1105865 : Blo 323837 1105865 := bstep (se 2 (by rfl) ⟨414699, by rfl⟩ : syracuseStep 1105865 = 829399) B829399
theorem B3172297 : Blo 323837 3172297 := bstep (se 2 (by rfl) ⟨1189611, by rfl⟩ : syracuseStep 3172297 = 2379223) B2379223
theorem B486719 : Blo 323837 486719 := bstep (se 1 (by rfl) ⟨365039, by rfl⟩ : syracuseStep 486719 = 730079) B730079
theorem B2813417 : Blo 323837 2813417 := bstep (se 2 (by rfl) ⟨1055031, by rfl⟩ : syracuseStep 2813417 = 2110063) B2110063
theorem B1339361 : Blo 323837 1339361 := bstep (se 2 (by rfl) ⟨502260, by rfl⟩ : syracuseStep 1339361 = 1004521) B1004521
theorem B3698945 : Blo 323837 3698945 := bstep (se 2 (by rfl) ⟨1387104, by rfl⟩ : syracuseStep 3698945 = 2774209) B2774209
theorem B2519315 : Blo 323837 2519315 := bstep (se 1 (by rfl) ⟨1889486, by rfl⟩ : syracuseStep 2519315 = 3778973) B3778973
theorem B324223 : Blo 323837 324223 := bstep (se 1 (by rfl) ⟨243167, by rfl⟩ : syracuseStep 324223 = 486335) B486335
theorem B324255 : Blo 323837 324255 := bstep (se 1 (by rfl) ⟨243191, by rfl⟩ : syracuseStep 324255 = 486383) B486383
theorem B324847 : Blo 323837 324847 := bstep (se 1 (by rfl) ⟨243635, by rfl⟩ : syracuseStep 324847 = 487271) B487271
theorem B488759 : Blo 323837 488759 := bstep (se 1 (by rfl) ⟨366569, by rfl⟩ : syracuseStep 488759 = 733139) B733139
theorem B325915 : Blo 323837 325915 := bstep (se 1 (by rfl) ⟨244436, by rfl⟩ : syracuseStep 325915 = 488873) B488873
theorem B2652535 : Blo 323837 2652535 := bstep (se 1 (by rfl) ⟨1989401, by rfl⟩ : syracuseStep 2652535 = 3978803) B3978803
theorem B26147407 : Blo 323837 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B326383 : Blo 323837 326383 := bstep (se 1 (by rfl) ⟨244787, by rfl⟩ : syracuseStep 326383 = 489575) B489575
theorem B326687 : Blo 323837 326687 := bstep (se 1 (by rfl) ⟨245015, by rfl⟩ : syracuseStep 326687 = 490031) B490031
theorem B1244267 : Blo 323837 1244267 := bstep (se 1 (by rfl) ⟨933200, by rfl⟩ : syracuseStep 1244267 = 1866401) B1866401
theorem B326767 : Blo 323837 326767 := bstep (se 1 (by rfl) ⟨245075, by rfl⟩ : syracuseStep 326767 = 490151) B490151
theorem B326823 : Blo 323837 326823 := bstep (se 1 (by rfl) ⟨245117, by rfl⟩ : syracuseStep 326823 = 490235) B490235
theorem B327375 : Blo 323837 327375 := bstep (se 1 (by rfl) ⟨245531, by rfl⟩ : syracuseStep 327375 = 491063) B491063
theorem B327407 : Blo 323837 327407 := bstep (se 1 (by rfl) ⟨245555, by rfl⟩ : syracuseStep 327407 = 491111) B491111
theorem B21135167 : Blo 323837 21135167 := bstep (se 1 (by rfl) ⟨15851375, by rfl⟩ : syracuseStep 21135167 = 31702751) B31702751
theorem B491567 : Blo 323837 491567 := bstep (se 1 (by rfl) ⟨368675, by rfl⟩ : syracuseStep 491567 = 737351) B737351
theorem B1573103 : Blo 323837 1573103 := bstep (se 1 (by rfl) ⟨1179827, by rfl⟩ : syracuseStep 1573103 = 2359655) B2359655
theorem B1639763 : Blo 323837 1639763 := bstep (se 1 (by rfl) ⟨1229822, by rfl⟩ : syracuseStep 1639763 = 2459645) B2459645
theorem B4229729 : Blo 323837 4229729 := bstep (se 2 (by rfl) ⟨1586148, by rfl⟩ : syracuseStep 4229729 = 3172297) B3172297
theorem B3346247 : Blo 323837 3346247 := bstep (se 1 (by rfl) ⟨2509685, by rfl⟩ : syracuseStep 3346247 = 5019371) B5019371
theorem B462847 : Blo 323837 462847 := bstep (se 1 (by rfl) ⟨347135, by rfl⟩ : syracuseStep 462847 = 694271) B694271
theorem B6656431 : Blo 323837 6656431 := bstep (se 1 (by rfl) ⟨4992323, by rfl⟩ : syracuseStep 6656431 = 9984647) B9984647
theorem B1643489 : Blo 323837 1643489 := bstep (se 2 (by rfl) ⟨616308, by rfl⟩ : syracuseStep 1643489 = 1232617) B1232617
theorem B1515071 : Blo 323837 1515071 := bstep (se 1 (by rfl) ⟨1136303, by rfl⟩ : syracuseStep 1515071 = 2272607) B2272607
theorem B1875611 : Blo 323837 1875611 := bstep (se 1 (by rfl) ⟨1406708, by rfl⟩ : syracuseStep 1875611 = 2813417) B2813417
theorem B892907 : Blo 323837 892907 := bstep (se 1 (by rfl) ⟨669680, by rfl⟩ : syracuseStep 892907 = 1339361) B1339361
theorem B729161 : Blo 323837 729161 := bstep (se 2 (by rfl) ⟨273435, by rfl⟩ : syracuseStep 729161 = 546871) B546871
theorem B729179 : Blo 323837 729179 := bstep (se 1 (by rfl) ⟨546884, by rfl⟩ : syracuseStep 729179 = 1093769) B1093769
theorem B2465963 : Blo 323837 2465963 := bstep (se 1 (by rfl) ⟨1849472, by rfl⟩ : syracuseStep 2465963 = 3698945) B3698945
theorem B1679543 : Blo 323837 1679543 := bstep (se 1 (by rfl) ⟨1259657, by rfl⟩ : syracuseStep 1679543 = 2519315) B2519315
theorem B926491 : Blo 323837 926491 := bstep (se 1 (by rfl) ⟨694868, by rfl⟩ : syracuseStep 926491 = 1389737) B1389737
theorem B1909889 : Blo 323837 1909889 := bstep (se 2 (by rfl) ⟨716208, by rfl⟩ : syracuseStep 1909889 = 1432417) B1432417
theorem B730727 : Blo 323837 730727 := bstep (se 1 (by rfl) ⟨548045, by rfl⟩ : syracuseStep 730727 = 1096091) B1096091
theorem B829511 : Blo 323837 829511 := bstep (se 1 (by rfl) ⟨622133, by rfl⟩ : syracuseStep 829511 = 1244267) B1244267
theorem B731591 : Blo 323837 731591 := bstep (se 1 (by rfl) ⟨548693, by rfl⟩ : syracuseStep 731591 = 1097387) B1097387
theorem B928223 : Blo 323837 928223 := bstep (se 1 (by rfl) ⟨696167, by rfl⟩ : syracuseStep 928223 = 1392335) B1392335
theorem B733679 : Blo 323837 733679 := bstep (se 1 (by rfl) ⟨550259, by rfl⟩ : syracuseStep 733679 = 1100519) B1100519
theorem B5289245 : Blo 323837 5289245 := bstep (se 3 (by rfl) ⟨991733, by rfl⟩ : syracuseStep 5289245 = 1983467) B1983467
theorem B737243 : Blo 323837 737243 := bstep (se 1 (by rfl) ⟨552932, by rfl⟩ : syracuseStep 737243 = 1105865) B1105865
theorem B1100087 : Blo 323837 1100087 := bstep (se 1 (by rfl) ⟨825065, by rfl⟩ : syracuseStep 1100087 = 1650131) B1650131
theorem B2476655 : Blo 323837 2476655 := bstep (se 1 (by rfl) ⟨1857491, by rfl⟩ : syracuseStep 2476655 = 3714983) B3714983
theorem B2084143 : Blo 323837 2084143 := bstep (se 1 (by rfl) ⟨1563107, by rfl⟩ : syracuseStep 2084143 = 3126215) B3126215
theorem B1101383 : Blo 323837 1101383 := bstep (se 1 (by rfl) ⟨826037, by rfl⟩ : syracuseStep 1101383 = 1652075) B1652075
theorem B2478599 : Blo 323837 2478599 := bstep (se 1 (by rfl) ⟨1858949, by rfl⟩ : syracuseStep 2478599 = 3717899) B3717899
theorem B1168063 : Blo 323837 1168063 := bstep (se 1 (by rfl) ⟨876047, by rfl⟩ : syracuseStep 1168063 = 1752095) B1752095
theorem B1791085 : Blo 323837 1791085 := bstep (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) B671657
theorem B1758323 : Blo 323837 1758323 := bstep (se 1 (by rfl) ⟨1318742, by rfl⟩ : syracuseStep 1758323 = 2637485) B2637485
theorem B109009307 : Blo 323837 109009307 := bstep (se 1 (by rfl) ⟨81756980, by rfl⟩ : syracuseStep 109009307 = 163513961) B163513961
theorem B1170011 : Blo 323837 1170011 := bstep (se 1 (by rfl) ⟨877508, by rfl⟩ : syracuseStep 1170011 = 1755017) B1755017
theorem B1759927 : Blo 323837 1759927 := bstep (se 1 (by rfl) ⟨1319945, by rfl⟩ : syracuseStep 1759927 = 2639891) B2639891
theorem B615451 : Blo 323837 615451 := bstep (se 1 (by rfl) ⟨461588, by rfl⟩ : syracuseStep 615451 = 923177) B923177
theorem B780671 : Blo 323837 780671 := bstep (se 1 (by rfl) ⟨585503, by rfl⟩ : syracuseStep 780671 = 1171007) B1171007
theorem B2976371 : Blo 323837 2976371 := bstep (se 1 (by rfl) ⟨2232278, by rfl⟩ : syracuseStep 2976371 = 4464557) B4464557
theorem B324479 : Blo 323837 324479 := bstep (se 1 (by rfl) ⟨243359, by rfl⟩ : syracuseStep 324479 = 486719) B486719
theorem B488807 : Blo 323837 488807 := bstep (se 1 (by rfl) ⟨366605, by rfl⟩ : syracuseStep 488807 = 733211) B733211
theorem B3536713 : Blo 323837 3536713 := bstep (se 2 (by rfl) ⟨1326267, by rfl⟩ : syracuseStep 3536713 = 2652535) B2652535
theorem B34863209 : Blo 323837 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B325839 : Blo 323837 325839 := bstep (se 1 (by rfl) ⟨244379, by rfl⟩ : syracuseStep 325839 = 488759) B488759
theorem B5306633 : Blo 323837 5306633 := bstep (se 2 (by rfl) ⟨1989987, by rfl⟩ : syracuseStep 5306633 = 3979975) B3979975
theorem B489755 : Blo 323837 489755 := bstep (se 1 (by rfl) ⟨367316, by rfl⟩ : syracuseStep 489755 = 734633) B734633
theorem B752063 : Blo 323837 752063 := bstep (se 1 (by rfl) ⟨564047, by rfl⟩ : syracuseStep 752063 = 1128095) B1128095
theorem B3374291 : Blo 323837 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B490751 : Blo 323837 490751 := bstep (se 1 (by rfl) ⟨368063, by rfl⟩ : syracuseStep 490751 = 736127) B736127
theorem B3571303 : Blo 323837 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B491291 : Blo 323837 491291 := bstep (se 1 (by rfl) ⟨368468, by rfl⟩ : syracuseStep 491291 = 736937) B736937
theorem B14090111 : Blo 323837 14090111 := bstep (se 1 (by rfl) ⟨10567583, by rfl⟩ : syracuseStep 14090111 = 21135167) B21135167
theorem B327711 : Blo 323837 327711 := bstep (se 1 (by rfl) ⟨245783, by rfl⟩ : syracuseStep 327711 = 491567) B491567
theorem B1048735 : Blo 323837 1048735 := bstep (se 1 (by rfl) ⟨786551, by rfl⟩ : syracuseStep 1048735 = 1573103) B1573103
theorem B820601 : Blo 323837 820601 := bstep (se 2 (by rfl) ⟨307725, by rfl⟩ : syracuseStep 820601 = 615451) B615451
theorem B2819819 : Blo 323837 2819819 := bstep (se 1 (by rfl) ⟨2114864, by rfl⟩ : syracuseStep 2819819 = 4229729) B4229729
theorem B2230831 : Blo 323837 2230831 := bstep (se 1 (by rfl) ⟨1673123, by rfl⟩ : syracuseStep 2230831 = 3346247) B3346247
theorem B6229669 : Blo 323837 6229669 := bstep (se 4 (by rfl) ⟨584031, by rfl⟩ : syracuseStep 6229669 = 1168063) B1168063
theorem B1250407 : Blo 323837 1250407 := bstep (se 1 (by rfl) ⟨937805, by rfl⟩ : syracuseStep 1250407 = 1875611) B1875611
theorem B595271 : Blo 323837 595271 := bstep (se 1 (by rfl) ⟨446453, by rfl⟩ : syracuseStep 595271 = 892907) B892907
theorem B1643975 : Blo 323837 1643975 := bstep (se 1 (by rfl) ⟨1232981, by rfl⟩ : syracuseStep 1643975 = 2465963) B2465963
theorem B1119695 : Blo 323837 1119695 := bstep (se 1 (by rfl) ⟨839771, by rfl⟩ : syracuseStep 1119695 = 1679543) B1679543
theorem B2005501 : Blo 323837 2005501 := bstep (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) B752063
theorem B3120029 : Blo 323837 3120029 := bstep (se 3 (by rfl) ⟨585005, by rfl⟩ : syracuseStep 3120029 = 1170011) B1170011
theorem B23242139 : Blo 323837 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B4040189 : Blo 323837 4040189 := bstep (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) B1515071
theorem B4761737 : Blo 323837 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B1093175 : Blo 323837 1093175 := bstep (se 1 (by rfl) ⟨819881, by rfl⟩ : syracuseStep 1093175 = 1639763) B1639763
theorem B733391 : Blo 323837 733391 := bstep (se 1 (by rfl) ⟨550043, by rfl⟩ : syracuseStep 733391 = 1100087) B1100087
theorem B1651103 : Blo 323837 1651103 := bstep (se 1 (by rfl) ⟨1238327, by rfl⟩ : syracuseStep 1651103 = 2476655) B2476655
theorem B734255 : Blo 323837 734255 := bstep (se 1 (by rfl) ⟨550691, by rfl⟩ : syracuseStep 734255 = 1101383) B1101383
theorem B1652399 : Blo 323837 1652399 := bstep (se 1 (by rfl) ⟨1239299, by rfl⟩ : syracuseStep 1652399 = 2478599) B2478599
theorem B1095659 : Blo 323837 1095659 := bstep (se 1 (by rfl) ⟨821744, by rfl⟩ : syracuseStep 1095659 = 1643489) B1643489
theorem B1984247 : Blo 323837 1984247 := bstep (se 1 (by rfl) ⟨1488185, by rfl⟩ : syracuseStep 1984247 = 2976371) B2976371
theorem B3526163 : Blo 323837 3526163 := bstep (se 1 (by rfl) ⟨2644622, by rfl⟩ : syracuseStep 3526163 = 5289245) B5289245
theorem B2346569 : Blo 323837 2346569 := bstep (se 2 (by rfl) ⟨879963, by rfl⟩ : syracuseStep 2346569 = 1759927) B1759927
theorem B2249527 : Blo 323837 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B9393407 : Blo 323837 9393407 := bstep (se 1 (by rfl) ⟨7045055, by rfl⟩ : syracuseStep 9393407 = 14090111) B14090111
theorem B1235321 : Blo 323837 1235321 := bstep (se 2 (by rfl) ⟨463245, by rfl⟩ : syracuseStep 1235321 = 926491) B926491
theorem B1172215 : Blo 323837 1172215 := bstep (se 1 (by rfl) ⟨879161, by rfl⟩ : syracuseStep 1172215 = 1758323) B1758323
theorem B72672871 : Blo 323837 72672871 := bstep (se 1 (by rfl) ⟨54504653, by rfl⟩ : syracuseStep 72672871 = 109009307) B109009307
theorem B2778857 : Blo 323837 2778857 := bstep (se 2 (by rfl) ⟨1042071, by rfl⟩ : syracuseStep 2778857 = 2084143) B2084143
theorem B617129 : Blo 323837 617129 := bstep (se 2 (by rfl) ⟨231423, by rfl⟩ : syracuseStep 617129 = 462847) B462847
theorem B486107 : Blo 323837 486107 := bstep (se 1 (by rfl) ⟨364580, by rfl⟩ : syracuseStep 486107 = 729161) B729161
theorem B486119 : Blo 323837 486119 := bstep (se 1 (by rfl) ⟨364589, by rfl⟩ : syracuseStep 486119 = 729179) B729179
theorem B8875241 : Blo 323837 8875241 := bstep (se 2 (by rfl) ⟨3328215, by rfl⟩ : syracuseStep 8875241 = 6656431) B6656431
theorem B1273259 : Blo 323837 1273259 := bstep (se 1 (by rfl) ⟨954944, by rfl⟩ : syracuseStep 1273259 = 1909889) B1909889
theorem B487151 : Blo 323837 487151 := bstep (se 1 (by rfl) ⟨365363, by rfl⟩ : syracuseStep 487151 = 730727) B730727
theorem B553007 : Blo 323837 553007 := bstep (se 1 (by rfl) ⟨414755, by rfl⟩ : syracuseStep 553007 = 829511) B829511
theorem B2388113 : Blo 323837 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B520447 : Blo 323837 520447 := bstep (se 1 (by rfl) ⟨390335, by rfl⟩ : syracuseStep 520447 = 780671) B780671
theorem B487727 : Blo 323837 487727 := bstep (se 1 (by rfl) ⟨365795, by rfl⟩ : syracuseStep 487727 = 731591) B731591
theorem B618815 : Blo 323837 618815 := bstep (se 1 (by rfl) ⟨464111, by rfl⟩ : syracuseStep 618815 = 928223) B928223
theorem B4715617 : Blo 323837 4715617 := bstep (se 2 (by rfl) ⟨1768356, by rfl⟩ : syracuseStep 4715617 = 3536713) B3536713
theorem B489119 : Blo 323837 489119 := bstep (se 1 (by rfl) ⟨366839, by rfl⟩ : syracuseStep 489119 = 733679) B733679
theorem B325871 : Blo 323837 325871 := bstep (se 1 (by rfl) ⟨244403, by rfl⟩ : syracuseStep 325871 = 488807) B488807
theorem B3537755 : Blo 323837 3537755 := bstep (se 1 (by rfl) ⟨2653316, by rfl⟩ : syracuseStep 3537755 = 5306633) B5306633
theorem B326503 : Blo 323837 326503 := bstep (se 1 (by rfl) ⟨244877, by rfl⟩ : syracuseStep 326503 = 489755) B489755
theorem B327167 : Blo 323837 327167 := bstep (se 1 (by rfl) ⟨245375, by rfl⟩ : syracuseStep 327167 = 490751) B490751
theorem B327527 : Blo 323837 327527 := bstep (se 1 (by rfl) ⟨245645, by rfl⟩ : syracuseStep 327527 = 491291) B491291
theorem B491495 : Blo 323837 491495 := bstep (se 1 (by rfl) ⟨368621, by rfl⟩ : syracuseStep 491495 = 737243) B737243
theorem B96897161 : Blo 323837 96897161 := bstep (se 2 (by rfl) ⟨36336435, by rfl⟩ : syracuseStep 96897161 = 72672871) B72672871
theorem B6262271 : Blo 323837 6262271 := bstep (se 1 (by rfl) ⟨4696703, by rfl⟩ : syracuseStep 6262271 = 9393407) B9393407
theorem B396847 : Blo 323837 396847 := bstep (se 1 (by rfl) ⟨297635, by rfl⟩ : syracuseStep 396847 = 595271) B595271
theorem B823547 : Blo 323837 823547 := bstep (se 1 (by rfl) ⟨617660, by rfl⟩ : syracuseStep 823547 = 1235321) B1235321
theorem B693929 : Blo 323837 693929 := bstep (se 2 (by rfl) ⟨260223, by rfl⟩ : syracuseStep 693929 = 520447) B520447
theorem B2693459 : Blo 323837 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B728783 : Blo 323837 728783 := bstep (se 1 (by rfl) ⟨546587, by rfl⟩ : syracuseStep 728783 = 1093175) B1093175
theorem B368671 : Blo 323837 368671 := bstep (se 1 (by rfl) ⟨276503, by rfl⟩ : syracuseStep 368671 = 553007) B553007
theorem B730439 : Blo 323837 730439 := bstep (se 1 (by rfl) ⟨547829, by rfl⟩ : syracuseStep 730439 = 1095659) B1095659
theorem B1322831 : Blo 323837 1322831 := bstep (se 1 (by rfl) ⟨992123, by rfl⟩ : syracuseStep 1322831 = 1984247) B1984247
theorem B1095983 : Blo 323837 1095983 := bstep (se 1 (by rfl) ⟨821987, by rfl⟩ : syracuseStep 1095983 = 1643975) B1643975
theorem B2080019 : Blo 323837 2080019 := bstep (se 1 (by rfl) ⟨1560014, by rfl⟩ : syracuseStep 2080019 = 3120029) B3120029
theorem B7519517 : Blo 323837 7519517 := bstep (se 3 (by rfl) ⟨1409909, by rfl⟩ : syracuseStep 7519517 = 2819819) B2819819
theorem B11943413 : Blo 323837 11943413 := bstep (se 5 (by rfl) ⟨559847, by rfl⟩ : syracuseStep 11943413 = 1119695) B1119695
theorem B8306225 : Blo 323837 8306225 := bstep (se 2 (by rfl) ⟨3114834, by rfl⟩ : syracuseStep 8306225 = 6229669) B6229669
theorem B6668837 : Blo 323837 6668837 := bstep (se 4 (by rfl) ⟨625203, by rfl⟩ : syracuseStep 6668837 = 1250407) B1250407
theorem B2999369 : Blo 323837 2999369 := bstep (se 2 (by rfl) ⟨1124763, by rfl⟩ : syracuseStep 2999369 = 2249527) B2249527
theorem B1852571 : Blo 323837 1852571 := bstep (se 1 (by rfl) ⟨1389428, by rfl⟩ : syracuseStep 1852571 = 2778857) B2778857
theorem B411419 : Blo 323837 411419 := bstep (se 1 (by rfl) ⟨308564, by rfl⟩ : syracuseStep 411419 = 617129) B617129
theorem B5916827 : Blo 323837 5916827 := bstep (se 1 (by rfl) ⟨4437620, by rfl⟩ : syracuseStep 5916827 = 8875241) B8875241
theorem B1592075 : Blo 323837 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B412543 : Blo 323837 412543 := bstep (se 1 (by rfl) ⟨309407, by rfl⟩ : syracuseStep 412543 = 618815) B618815
theorem B1100735 : Blo 323837 1100735 := bstep (se 1 (by rfl) ⟨825551, by rfl⟩ : syracuseStep 1100735 = 1651103) B1651103
theorem B2674001 : Blo 323837 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B1101599 : Blo 323837 1101599 := bstep (se 1 (by rfl) ⟨826199, by rfl⟩ : syracuseStep 1101599 = 1652399) B1652399
theorem B1398313 : Blo 323837 1398313 := bstep (se 2 (by rfl) ⟨524367, by rfl⟩ : syracuseStep 1398313 = 1048735) B1048735
theorem B547067 : Blo 323837 547067 := bstep (se 1 (by rfl) ⟨410300, by rfl⟩ : syracuseStep 547067 = 820601) B820601
theorem B2350775 : Blo 323837 2350775 := bstep (se 1 (by rfl) ⟨1763081, by rfl⟩ : syracuseStep 2350775 = 3526163) B3526163
theorem B1564379 : Blo 323837 1564379 := bstep (se 1 (by rfl) ⟨1173284, by rfl⟩ : syracuseStep 1564379 = 2346569) B2346569
theorem B2974441 : Blo 323837 2974441 := bstep (se 2 (by rfl) ⟨1115415, by rfl⟩ : syracuseStep 2974441 = 2230831) B2230831
theorem B6251813 : Blo 323837 6251813 := bstep (se 4 (by rfl) ⟨586107, by rfl⟩ : syracuseStep 6251813 = 1172215) B1172215
theorem B15494759 : Blo 323837 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B3174491 : Blo 323837 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B6287489 : Blo 323837 6287489 := bstep (se 2 (by rfl) ⟨2357808, by rfl⟩ : syracuseStep 6287489 = 4715617) B4715617
theorem B324071 : Blo 323837 324071 := bstep (se 1 (by rfl) ⟨243053, by rfl⟩ : syracuseStep 324071 = 486107) B486107
theorem B324079 : Blo 323837 324079 := bstep (se 1 (by rfl) ⟨243059, by rfl⟩ : syracuseStep 324079 = 486119) B486119
theorem B848839 : Blo 323837 848839 := bstep (se 1 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 848839 = 1273259) B1273259
theorem B324767 : Blo 323837 324767 := bstep (se 1 (by rfl) ⟨243575, by rfl⟩ : syracuseStep 324767 = 487151) B487151
theorem B488927 : Blo 323837 488927 := bstep (se 1 (by rfl) ⟨366695, by rfl⟩ : syracuseStep 488927 = 733391) B733391
theorem B325151 : Blo 323837 325151 := bstep (se 1 (by rfl) ⟨243863, by rfl⟩ : syracuseStep 325151 = 487727) B487727
theorem B489503 : Blo 323837 489503 := bstep (se 1 (by rfl) ⟨367127, by rfl⟩ : syracuseStep 489503 = 734255) B734255
theorem B326079 : Blo 323837 326079 := bstep (se 1 (by rfl) ⟨244559, by rfl⟩ : syracuseStep 326079 = 489119) B489119
theorem B2358503 : Blo 323837 2358503 := bstep (se 1 (by rfl) ⟨1768877, by rfl⟩ : syracuseStep 2358503 = 3537755) B3537755
theorem B327663 : Blo 323837 327663 := bstep (se 1 (by rfl) ⟨245747, by rfl⟩ : syracuseStep 327663 = 491495) B491495
theorem B491561 : Blo 323837 491561 := bstep (se 2 (by rfl) ⟨184335, by rfl⟩ : syracuseStep 491561 = 368671) B368671
theorem B1999579 : Blo 323837 1999579 := bstep (se 1 (by rfl) ⟨1499684, by rfl⟩ : syracuseStep 1999579 = 2999369) B2999369
theorem B3965921 : Blo 323837 3965921 := bstep (se 2 (by rfl) ⟨1487220, by rfl⟩ : syracuseStep 3965921 = 2974441) B2974441
theorem B462619 : Blo 323837 462619 := bstep (se 1 (by rfl) ⟨346964, by rfl⟩ : syracuseStep 462619 = 693929) B693929
theorem B364711 : Blo 323837 364711 := bstep (se 1 (by rfl) ⟨273533, by rfl⟩ : syracuseStep 364711 = 547067) B547067
theorem B529129 : Blo 323837 529129 := bstep (se 2 (by rfl) ⟨198423, by rfl⟩ : syracuseStep 529129 = 396847) B396847
theorem B4167875 : Blo 323837 4167875 := bstep (se 1 (by rfl) ⟨3125906, by rfl⟩ : syracuseStep 4167875 = 6251813) B6251813
theorem B7182557 : Blo 323837 7182557 := bstep (se 3 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 7182557 = 2693459) B2693459
theorem B10329839 : Blo 323837 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B730655 : Blo 323837 730655 := bstep (se 1 (by rfl) ⟨547991, by rfl⟩ : syracuseStep 730655 = 1095983) B1095983
theorem B1386679 : Blo 323837 1386679 := bstep (se 1 (by rfl) ⟨1040009, by rfl⟩ : syracuseStep 1386679 = 2080019) B2080019
theorem B8465309 : Blo 323837 8465309 := bstep (se 3 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 8465309 = 3174491) B3174491
theorem B3944551 : Blo 323837 3944551 := bstep (se 1 (by rfl) ⟨2958413, by rfl⟩ : syracuseStep 3944551 = 5916827) B5916827
theorem B733823 : Blo 323837 733823 := bstep (se 1 (by rfl) ⟨550367, by rfl⟩ : syracuseStep 733823 = 1100735) B1100735
theorem B1782667 : Blo 323837 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B4174847 : Blo 323837 4174847 := bstep (se 1 (by rfl) ⟨3131135, by rfl⟩ : syracuseStep 4174847 = 6262271) B6262271
theorem B734399 : Blo 323837 734399 := bstep (se 1 (by rfl) ⟨550799, by rfl⟩ : syracuseStep 734399 = 1101599) B1101599
theorem B1097117 : Blo 323837 1097117 := bstep (se 3 (by rfl) ⟨205709, by rfl⟩ : syracuseStep 1097117 = 411419) B411419
theorem B258392429 : Blo 323837 258392429 := bstep (se 3 (by rfl) ⟨48448580, by rfl⟩ : syracuseStep 258392429 = 96897161) B96897161
theorem B1131785 : Blo 323837 1131785 := bstep (se 2 (by rfl) ⟨424419, by rfl⟩ : syracuseStep 1131785 = 848839) B848839
theorem B4245533 : Blo 323837 4245533 := bstep (se 3 (by rfl) ⟨796037, by rfl⟩ : syracuseStep 4245533 = 1592075) B1592075
theorem B3527549 : Blo 323837 3527549 := bstep (se 3 (by rfl) ⟨661415, by rfl⟩ : syracuseStep 3527549 = 1322831) B1322831
theorem B4445891 : Blo 323837 4445891 := bstep (se 1 (by rfl) ⟨3334418, by rfl⟩ : syracuseStep 4445891 = 6668837) B6668837
theorem B1235047 : Blo 323837 1235047 := bstep (se 1 (by rfl) ⟨926285, by rfl⟩ : syracuseStep 1235047 = 1852571) B1852571
theorem B549031 : Blo 323837 549031 := bstep (se 1 (by rfl) ⟨411773, by rfl⟩ : syracuseStep 549031 = 823547) B823547
theorem B550057 : Blo 323837 550057 := bstep (se 2 (by rfl) ⟨206271, by rfl⟩ : syracuseStep 550057 = 412543) B412543
theorem B1567183 : Blo 323837 1567183 := bstep (se 1 (by rfl) ⟨1175387, by rfl⟩ : syracuseStep 1567183 = 2350775) B2350775
theorem B485855 : Blo 323837 485855 := bstep (se 1 (by rfl) ⟨364391, by rfl⟩ : syracuseStep 485855 = 728783) B728783
theorem B1042919 : Blo 323837 1042919 := bstep (se 1 (by rfl) ⟨782189, by rfl⟩ : syracuseStep 1042919 = 1564379) B1564379
theorem B486959 : Blo 323837 486959 := bstep (se 1 (by rfl) ⟨365219, by rfl⟩ : syracuseStep 486959 = 730439) B730439
theorem B1864417 : Blo 323837 1864417 := bstep (se 2 (by rfl) ⟨699156, by rfl⟩ : syracuseStep 1864417 = 1398313) B1398313
theorem B4191659 : Blo 323837 4191659 := bstep (se 1 (by rfl) ⟨3143744, by rfl⟩ : syracuseStep 4191659 = 6287489) B6287489
theorem B325951 : Blo 323837 325951 := bstep (se 1 (by rfl) ⟨244463, by rfl⟩ : syracuseStep 325951 = 488927) B488927
theorem B326335 : Blo 323837 326335 := bstep (se 1 (by rfl) ⟨244751, by rfl⟩ : syracuseStep 326335 = 489503) B489503
theorem B1572335 : Blo 323837 1572335 := bstep (se 1 (by rfl) ⟨1179251, by rfl⟩ : syracuseStep 1572335 = 2358503) B2358503
theorem B5013011 : Blo 323837 5013011 := bstep (se 1 (by rfl) ⟨3759758, by rfl⟩ : syracuseStep 5013011 = 7519517) B7519517
theorem B7962275 : Blo 323837 7962275 := bstep (se 1 (by rfl) ⟨5971706, by rfl⟩ : syracuseStep 7962275 = 11943413) B11943413
theorem B5537483 : Blo 323837 5537483 := bstep (se 1 (by rfl) ⟨4153112, by rfl⟩ : syracuseStep 5537483 = 8306225) B8306225
theorem B327707 : Blo 323837 327707 := bstep (se 1 (by rfl) ⟨245780, by rfl⟩ : syracuseStep 327707 = 491561) B491561
theorem B172261619 : Blo 323837 172261619 := bstep (se 1 (by rfl) ⟨129196214, by rfl⟩ : syracuseStep 172261619 = 258392429) B258392429
theorem B754523 : Blo 323837 754523 := bstep (se 1 (by rfl) ⟨565892, by rfl⟩ : syracuseStep 754523 = 1131785) B1131785
theorem B4788371 : Blo 323837 4788371 := bstep (se 1 (by rfl) ⟨3591278, by rfl⟩ : syracuseStep 4788371 = 7182557) B7182557
theorem B9507557 : Blo 323837 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B6886559 : Blo 323837 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B695279 : Blo 323837 695279 := bstep (se 1 (by rfl) ⟨521459, by rfl⟩ : syracuseStep 695279 = 1042919) B1042919
theorem B5643539 : Blo 323837 5643539 := bstep (se 1 (by rfl) ⟨4232654, by rfl⟩ : syracuseStep 5643539 = 8465309) B8465309
theorem B1646729 : Blo 323837 1646729 := bstep (se 2 (by rfl) ⟨617523, by rfl⟩ : syracuseStep 1646729 = 1235047) B1235047
theorem B2794439 : Blo 323837 2794439 := bstep (se 1 (by rfl) ⟨2095829, by rfl⟩ : syracuseStep 2794439 = 4191659) B4191659
theorem B731411 : Blo 323837 731411 := bstep (se 1 (by rfl) ⟨548558, by rfl⟩ : syracuseStep 731411 = 1097117) B1097117
theorem B732041 : Blo 323837 732041 := bstep (se 2 (by rfl) ⟨274515, by rfl⟩ : syracuseStep 732041 = 549031) B549031
theorem B2666105 : Blo 323837 2666105 := bstep (se 2 (by rfl) ⟨999789, by rfl⟩ : syracuseStep 2666105 = 1999579) B1999579
theorem B2830355 : Blo 323837 2830355 := bstep (se 1 (by rfl) ⟨2122766, by rfl⟩ : syracuseStep 2830355 = 4245533) B4245533
theorem B733409 : Blo 323837 733409 := bstep (se 2 (by rfl) ⟨275028, by rfl⟩ : syracuseStep 733409 = 550057) B550057
theorem B1848905 : Blo 323837 1848905 := bstep (se 2 (by rfl) ⟨693339, by rfl⟩ : syracuseStep 1848905 = 1386679) B1386679
theorem B2963927 : Blo 323837 2963927 := bstep (se 1 (by rfl) ⟨2222945, by rfl⟩ : syracuseStep 2963927 = 4445891) B4445891
theorem B5259401 : Blo 323837 5259401 := bstep (se 2 (by rfl) ⟨1972275, by rfl⟩ : syracuseStep 5259401 = 3944551) B3944551
theorem B705505 : Blo 323837 705505 := bstep (se 2 (by rfl) ⟨264564, by rfl⟩ : syracuseStep 705505 = 529129) B529129
theorem B3691655 : Blo 323837 3691655 := bstep (se 1 (by rfl) ⟨2768741, by rfl⟩ : syracuseStep 3691655 = 5537483) B5537483
theorem B2643947 : Blo 323837 2643947 := bstep (se 1 (by rfl) ⟨1982960, by rfl⟩ : syracuseStep 2643947 = 3965921) B3965921
theorem B2351699 : Blo 323837 2351699 := bstep (se 1 (by rfl) ⟨1763774, by rfl⟩ : syracuseStep 2351699 = 3527549) B3527549
theorem B2089577 : Blo 323837 2089577 := bstep (se 2 (by rfl) ⟨783591, by rfl⟩ : syracuseStep 2089577 = 1567183) B1567183
theorem B2778583 : Blo 323837 2778583 := bstep (se 1 (by rfl) ⟨2083937, by rfl⟩ : syracuseStep 2778583 = 4167875) B4167875
theorem B616825 : Blo 323837 616825 := bstep (se 2 (by rfl) ⟨231309, by rfl⟩ : syracuseStep 616825 = 462619) B462619
theorem B486281 : Blo 323837 486281 := bstep (se 2 (by rfl) ⟨182355, by rfl⟩ : syracuseStep 486281 = 364711) B364711
theorem B2485889 : Blo 323837 2485889 := bstep (se 2 (by rfl) ⟨932208, by rfl⟩ : syracuseStep 2485889 = 1864417) B1864417
theorem B487103 : Blo 323837 487103 := bstep (se 1 (by rfl) ⟨365327, by rfl⟩ : syracuseStep 487103 = 730655) B730655
theorem B323903 : Blo 323837 323903 := bstep (se 1 (by rfl) ⟨242927, by rfl⟩ : syracuseStep 323903 = 485855) B485855
theorem B324639 : Blo 323837 324639 := bstep (se 1 (by rfl) ⟨243479, by rfl⟩ : syracuseStep 324639 = 486959) B486959
theorem B489215 : Blo 323837 489215 := bstep (se 1 (by rfl) ⟨366911, by rfl⟩ : syracuseStep 489215 = 733823) B733823
theorem B2783231 : Blo 323837 2783231 := bstep (se 1 (by rfl) ⟨2087423, by rfl⟩ : syracuseStep 2783231 = 4174847) B4174847
theorem B489599 : Blo 323837 489599 := bstep (se 1 (by rfl) ⟨367199, by rfl⟩ : syracuseStep 489599 = 734399) B734399
theorem B1048223 : Blo 323837 1048223 := bstep (se 1 (by rfl) ⟨786167, by rfl⟩ : syracuseStep 1048223 = 1572335) B1572335
theorem B3342007 : Blo 323837 3342007 := bstep (se 1 (by rfl) ⟨2506505, by rfl⟩ : syracuseStep 3342007 = 5013011) B5013011
theorem B5308183 : Blo 323837 5308183 := bstep (se 1 (by rfl) ⟨3981137, by rfl⟩ : syracuseStep 5308183 = 7962275) B7962275
theorem B3506267 : Blo 323837 3506267 := bstep (se 1 (by rfl) ⟨2629700, by rfl⟩ : syracuseStep 3506267 = 5259401) B5259401
theorem B3704777 : Blo 323837 3704777 := bstep (se 2 (by rfl) ⟨1389291, by rfl⟩ : syracuseStep 3704777 = 2778583) B2778583
theorem B822433 : Blo 323837 822433 := bstep (se 2 (by rfl) ⟨308412, by rfl⟩ : syracuseStep 822433 = 616825) B616825
theorem B2461103 : Blo 323837 2461103 := bstep (se 1 (by rfl) ⟨1845827, by rfl⟩ : syracuseStep 2461103 = 3691655) B3691655
theorem B463519 : Blo 323837 463519 := bstep (se 1 (by rfl) ⟨347639, by rfl⟩ : syracuseStep 463519 = 695279) B695279
theorem B1777403 : Blo 323837 1777403 := bstep (se 1 (by rfl) ⟨1333052, by rfl⟩ : syracuseStep 1777403 = 2666105) B2666105
theorem B1975951 : Blo 323837 1975951 := bstep (se 1 (by rfl) ⟨1481963, by rfl⟩ : syracuseStep 1975951 = 2963927) B2963927
theorem B698815 : Blo 323837 698815 := bstep (se 1 (by rfl) ⟨524111, by rfl⟩ : syracuseStep 698815 = 1048223) B1048223
theorem B503015 : Blo 323837 503015 := bstep (se 1 (by rfl) ⟨377261, by rfl⟩ : syracuseStep 503015 = 754523) B754523
theorem B3192247 : Blo 323837 3192247 := bstep (se 1 (by rfl) ⟨2394185, by rfl⟩ : syracuseStep 3192247 = 4788371) B4788371
theorem B18364157 : Blo 323837 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B6338371 : Blo 323837 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B1097819 : Blo 323837 1097819 := bstep (se 1 (by rfl) ⟨823364, by rfl⟩ : syracuseStep 1097819 = 1646729) B1646729
theorem B1393051 : Blo 323837 1393051 := bstep (se 1 (by rfl) ⟨1044788, by rfl⟩ : syracuseStep 1393051 = 2089577) B2089577
theorem B1657259 : Blo 323837 1657259 := bstep (se 1 (by rfl) ⟨1242944, by rfl⟩ : syracuseStep 1657259 = 2485889) B2485889
theorem B1886903 : Blo 323837 1886903 := bstep (se 1 (by rfl) ⟨1415177, by rfl⟩ : syracuseStep 1886903 = 2830355) B2830355
theorem B1232603 : Blo 323837 1232603 := bstep (se 1 (by rfl) ⟨924452, by rfl⟩ : syracuseStep 1232603 = 1848905) B1848905
theorem B1855487 : Blo 323837 1855487 := bstep (se 1 (by rfl) ⟨1391615, by rfl⟩ : syracuseStep 1855487 = 2783231) B2783231
theorem B114841079 : Blo 323837 114841079 := bstep (se 1 (by rfl) ⟨86130809, by rfl⟩ : syracuseStep 114841079 = 172261619) B172261619
theorem B940673 : Blo 323837 940673 := bstep (se 2 (by rfl) ⟨352752, by rfl⟩ : syracuseStep 940673 = 705505) B705505
theorem B1762631 : Blo 323837 1762631 := bstep (se 1 (by rfl) ⟨1321973, by rfl⟩ : syracuseStep 1762631 = 2643947) B2643947
theorem B3762359 : Blo 323837 3762359 := bstep (se 1 (by rfl) ⟨2821769, by rfl⟩ : syracuseStep 3762359 = 5643539) B5643539
theorem B1567799 : Blo 323837 1567799 := bstep (se 1 (by rfl) ⟨1175849, by rfl⟩ : syracuseStep 1567799 = 2351699) B2351699
theorem B1862959 : Blo 323837 1862959 := bstep (se 1 (by rfl) ⟨1397219, by rfl⟩ : syracuseStep 1862959 = 2794439) B2794439
theorem B487607 : Blo 323837 487607 := bstep (se 1 (by rfl) ⟨365705, by rfl⟩ : syracuseStep 487607 = 731411) B731411
theorem B324187 : Blo 323837 324187 := bstep (se 1 (by rfl) ⟨243140, by rfl⟩ : syracuseStep 324187 = 486281) B486281
theorem B488027 : Blo 323837 488027 := bstep (se 1 (by rfl) ⟨366020, by rfl⟩ : syracuseStep 488027 = 732041) B732041
theorem B324735 : Blo 323837 324735 := bstep (se 1 (by rfl) ⟨243551, by rfl⟩ : syracuseStep 324735 = 487103) B487103
theorem B488939 : Blo 323837 488939 := bstep (se 1 (by rfl) ⟨366704, by rfl⟩ : syracuseStep 488939 = 733409) B733409
theorem B326143 : Blo 323837 326143 := bstep (se 1 (by rfl) ⟨244607, by rfl⟩ : syracuseStep 326143 = 489215) B489215
theorem B326399 : Blo 323837 326399 := bstep (se 1 (by rfl) ⟨244799, by rfl⟩ : syracuseStep 326399 = 489599) B489599
theorem B4456009 : Blo 323837 4456009 := bstep (se 2 (by rfl) ⟨1671003, by rfl⟩ : syracuseStep 4456009 = 3342007) B3342007
theorem B7077577 : Blo 323837 7077577 := bstep (se 2 (by rfl) ⟨2654091, by rfl⟩ : syracuseStep 7077577 = 5308183) B5308183
theorem B1640735 : Blo 323837 1640735 := bstep (se 1 (by rfl) ⟨1230551, by rfl⟩ : syracuseStep 1640735 = 2461103) B2461103
theorem B821735 : Blo 323837 821735 := bstep (se 1 (by rfl) ⟨616301, by rfl⟩ : syracuseStep 821735 = 1232603) B1232603
theorem B627115 : Blo 323837 627115 := bstep (se 1 (by rfl) ⟨470336, by rfl⟩ : syracuseStep 627115 = 940673) B940673
theorem B5941345 : Blo 323837 5941345 := bstep (se 2 (by rfl) ⟨2228004, by rfl⟩ : syracuseStep 5941345 = 4456009) B4456009
theorem B2337511 : Blo 323837 2337511 := bstep (se 1 (by rfl) ⟨1753133, by rfl⟩ : syracuseStep 2337511 = 3506267) B3506267
theorem B731879 : Blo 323837 731879 := bstep (se 1 (by rfl) ⟨548909, by rfl⟩ : syracuseStep 731879 = 1097819) B1097819
theorem B2469851 : Blo 323837 2469851 := bstep (se 1 (by rfl) ⟨1852388, by rfl⟩ : syracuseStep 2469851 = 3704777) B3704777
theorem B1257935 : Blo 323837 1257935 := bstep (se 1 (by rfl) ⟨943451, by rfl⟩ : syracuseStep 1257935 = 1886903) B1886903
theorem B2634601 : Blo 323837 2634601 := bstep (se 2 (by rfl) ⟨987975, by rfl⟩ : syracuseStep 2634601 = 1975951) B1975951
theorem B931753 : Blo 323837 931753 := bstep (se 2 (by rfl) ⟨349407, by rfl⟩ : syracuseStep 931753 = 698815) B698815
theorem B76560719 : Blo 323837 76560719 := bstep (se 1 (by rfl) ⟨57420539, by rfl⟩ : syracuseStep 76560719 = 114841079) B114841079
theorem B1096577 : Blo 323837 1096577 := bstep (se 2 (by rfl) ⟨411216, by rfl⟩ : syracuseStep 1096577 = 822433) B822433
theorem B2508239 : Blo 323837 2508239 := bstep (se 1 (by rfl) ⟨1881179, by rfl⟩ : syracuseStep 2508239 = 3762359) B3762359
theorem B12242771 : Blo 323837 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B4739741 : Blo 323837 4739741 := bstep (se 3 (by rfl) ⟨888701, by rfl⟩ : syracuseStep 4739741 = 1777403) B1777403
theorem B1857401 : Blo 323837 1857401 := bstep (se 2 (by rfl) ⟨696525, by rfl⟩ : syracuseStep 1857401 = 1393051) B1393051
theorem B1104839 : Blo 323837 1104839 := bstep (se 1 (by rfl) ⟨828629, by rfl⟩ : syracuseStep 1104839 = 1657259) B1657259
theorem B1236991 : Blo 323837 1236991 := bstep (se 1 (by rfl) ⟨927743, by rfl⟩ : syracuseStep 1236991 = 1855487) B1855487
theorem B2483945 : Blo 323837 2483945 := bstep (se 2 (by rfl) ⟨931479, by rfl⟩ : syracuseStep 2483945 = 1862959) B1862959
theorem B618025 : Blo 323837 618025 := bstep (se 2 (by rfl) ⟨231759, by rfl⟩ : syracuseStep 618025 = 463519) B463519
theorem B1175087 : Blo 323837 1175087 := bstep (se 1 (by rfl) ⟨881315, by rfl⟩ : syracuseStep 1175087 = 1762631) B1762631
theorem B4256329 : Blo 323837 4256329 := bstep (se 2 (by rfl) ⟨1596123, by rfl⟩ : syracuseStep 4256329 = 3192247) B3192247
theorem B1045199 : Blo 323837 1045199 := bstep (se 1 (by rfl) ⟨783899, by rfl⟩ : syracuseStep 1045199 = 1567799) B1567799
theorem B8451161 : Blo 323837 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B325071 : Blo 323837 325071 := bstep (se 1 (by rfl) ⟨243803, by rfl⟩ : syracuseStep 325071 = 487607) B487607
theorem B325351 : Blo 323837 325351 := bstep (se 1 (by rfl) ⟨244013, by rfl⟩ : syracuseStep 325351 = 488027) B488027
theorem B1341373 : Blo 323837 1341373 := bstep (se 3 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 1341373 = 503015) B503015
theorem B325959 : Blo 323837 325959 := bstep (se 1 (by rfl) ⟨244469, by rfl⟩ : syracuseStep 325959 = 488939) B488939
theorem B9436769 : Blo 323837 9436769 := bstep (se 2 (by rfl) ⟨3538788, by rfl⟩ : syracuseStep 9436769 = 7077577) B7077577
theorem B1672159 : Blo 323837 1672159 := bstep (se 1 (by rfl) ⟨1254119, by rfl⟩ : syracuseStep 1672159 = 2508239) B2508239
theorem B8161847 : Blo 323837 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B3116681 : Blo 323837 3116681 := bstep (se 2 (by rfl) ⟨1168755, by rfl⟩ : syracuseStep 3116681 = 2337511) B2337511
theorem B824033 : Blo 323837 824033 := bstep (se 2 (by rfl) ⟨309012, by rfl⟩ : syracuseStep 824033 = 618025) B618025
theorem B5675105 : Blo 323837 5675105 := bstep (se 2 (by rfl) ⟨2128164, by rfl⟩ : syracuseStep 5675105 = 4256329) B4256329
theorem B3512801 : Blo 323837 3512801 := bstep (se 2 (by rfl) ⟨1317300, by rfl⟩ : syracuseStep 3512801 = 2634601) B2634601
theorem B1646567 : Blo 323837 1646567 := bstep (se 1 (by rfl) ⟨1234925, by rfl⟩ : syracuseStep 1646567 = 2469851) B2469851
theorem B696799 : Blo 323837 696799 := bstep (se 1 (by rfl) ⟨522599, by rfl⟩ : syracuseStep 696799 = 1045199) B1045199
theorem B731051 : Blo 323837 731051 := bstep (se 1 (by rfl) ⟨548288, by rfl⟩ : syracuseStep 731051 = 1096577) B1096577
theorem B1649321 : Blo 323837 1649321 := bstep (se 2 (by rfl) ⟨618495, by rfl⟩ : syracuseStep 1649321 = 1236991) B1236991
theorem B3354493 : Blo 323837 3354493 := bstep (se 3 (by rfl) ⟨628967, by rfl⟩ : syracuseStep 3354493 = 1257935) B1257935
theorem B1093823 : Blo 323837 1093823 := bstep (se 1 (by rfl) ⟨820367, by rfl⟩ : syracuseStep 1093823 = 1640735) B1640735
theorem B3159827 : Blo 323837 3159827 := bstep (se 1 (by rfl) ⟨2369870, by rfl⟩ : syracuseStep 3159827 = 4739741) B4739741
theorem B736559 : Blo 323837 736559 := bstep (se 1 (by rfl) ⟨552419, by rfl⟩ : syracuseStep 736559 = 1104839) B1104839
theorem B836153 : Blo 323837 836153 := bstep (se 2 (by rfl) ⟨313557, by rfl⟩ : syracuseStep 836153 = 627115) B627115
theorem B204161917 : Blo 323837 204161917 := bstep (se 3 (by rfl) ⟨38280359, by rfl⟩ : syracuseStep 204161917 = 76560719) B76560719
theorem B1655963 : Blo 323837 1655963 := bstep (se 1 (by rfl) ⟨1241972, by rfl⟩ : syracuseStep 1655963 = 2483945) B2483945
theorem B1788497 : Blo 323837 1788497 := bstep (se 2 (by rfl) ⟨670686, by rfl⟩ : syracuseStep 1788497 = 1341373) B1341373
theorem B547823 : Blo 323837 547823 := bstep (se 1 (by rfl) ⟨410867, by rfl⟩ : syracuseStep 547823 = 821735) B821735
theorem B7921793 : Blo 323837 7921793 := bstep (se 2 (by rfl) ⟨2970672, by rfl⟩ : syracuseStep 7921793 = 5941345) B5941345
theorem B1238267 : Blo 323837 1238267 := bstep (se 1 (by rfl) ⟨928700, by rfl⟩ : syracuseStep 1238267 = 1857401) B1857401
theorem B487919 : Blo 323837 487919 := bstep (se 1 (by rfl) ⟨365939, by rfl⟩ : syracuseStep 487919 = 731879) B731879
theorem B783391 : Blo 323837 783391 := bstep (se 1 (by rfl) ⟨587543, by rfl⟩ : syracuseStep 783391 = 1175087) B1175087
theorem B1242337 : Blo 323837 1242337 := bstep (se 2 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 1242337 = 931753) B931753
theorem B5634107 : Blo 323837 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B6291179 : Blo 323837 6291179 := bstep (se 1 (by rfl) ⟨4718384, by rfl⟩ : syracuseStep 6291179 = 9436769) B9436769
theorem B557435 : Blo 323837 557435 := bstep (se 1 (by rfl) ⟨418076, by rfl⟩ : syracuseStep 557435 = 836153) B836153
theorem B2229545 : Blo 323837 2229545 := bstep (se 2 (by rfl) ⟨836079, by rfl⟩ : syracuseStep 2229545 = 1672159) B1672159
theorem B5441231 : Blo 323837 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B365215 : Blo 323837 365215 := bstep (se 1 (by rfl) ⟨273911, by rfl⟩ : syracuseStep 365215 = 547823) B547823
theorem B5281195 : Blo 323837 5281195 := bstep (se 1 (by rfl) ⟨3960896, by rfl⟩ : syracuseStep 5281195 = 7921793) B7921793
theorem B825511 : Blo 323837 825511 := bstep (se 1 (by rfl) ⟨619133, by rfl⟩ : syracuseStep 825511 = 1238267) B1238267
theorem B729215 : Blo 323837 729215 := bstep (se 1 (by rfl) ⟨546911, by rfl⟩ : syracuseStep 729215 = 1093823) B1093823
theorem B2106551 : Blo 323837 2106551 := bstep (se 1 (by rfl) ⟨1579913, by rfl⟩ : syracuseStep 2106551 = 3159827) B3159827
theorem B929065 : Blo 323837 929065 := bstep (se 2 (by rfl) ⟨348399, by rfl⟩ : syracuseStep 929065 = 696799) B696799
theorem B272215889 : Blo 323837 272215889 := bstep (se 2 (by rfl) ⟨102080958, by rfl⟩ : syracuseStep 272215889 = 204161917) B204161917
theorem B1192331 : Blo 323837 1192331 := bstep (se 1 (by rfl) ⟨894248, by rfl⟩ : syracuseStep 1192331 = 1788497) B1788497
theorem B2077787 : Blo 323837 2077787 := bstep (se 1 (by rfl) ⟨1558340, by rfl⟩ : syracuseStep 2077787 = 3116681) B3116681
theorem B2341867 : Blo 323837 2341867 := bstep (se 1 (by rfl) ⟨1756400, by rfl⟩ : syracuseStep 2341867 = 3512801) B3512801
theorem B4472657 : Blo 323837 4472657 := bstep (se 2 (by rfl) ⟨1677246, by rfl⟩ : syracuseStep 4472657 = 3354493) B3354493
theorem B1097711 : Blo 323837 1097711 := bstep (se 1 (by rfl) ⟨823283, by rfl⟩ : syracuseStep 1097711 = 1646567) B1646567
theorem B1656449 : Blo 323837 1656449 := bstep (se 2 (by rfl) ⟨621168, by rfl⟩ : syracuseStep 1656449 = 1242337) B1242337
theorem B1099547 : Blo 323837 1099547 := bstep (se 1 (by rfl) ⟨824660, by rfl⟩ : syracuseStep 1099547 = 1649321) B1649321
theorem B3756071 : Blo 323837 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B1103975 : Blo 323837 1103975 := bstep (se 1 (by rfl) ⟨827981, by rfl⟩ : syracuseStep 1103975 = 1655963) B1655963
theorem B549355 : Blo 323837 549355 := bstep (se 1 (by rfl) ⟨412016, by rfl⟩ : syracuseStep 549355 = 824033) B824033
theorem B15133613 : Blo 323837 15133613 := bstep (se 3 (by rfl) ⟨2837552, by rfl⟩ : syracuseStep 15133613 = 5675105) B5675105
theorem B487367 : Blo 323837 487367 := bstep (se 1 (by rfl) ⟨365525, by rfl⟩ : syracuseStep 487367 = 731051) B731051
theorem B1044521 : Blo 323837 1044521 := bstep (se 2 (by rfl) ⟨391695, by rfl⟩ : syracuseStep 1044521 = 783391) B783391
theorem B325279 : Blo 323837 325279 := bstep (se 1 (by rfl) ⟨243959, by rfl⟩ : syracuseStep 325279 = 487919) B487919
theorem B491039 : Blo 323837 491039 := bstep (se 1 (by rfl) ⟨368279, by rfl⟩ : syracuseStep 491039 = 736559) B736559
theorem B4194119 : Blo 323837 4194119 := bstep (se 1 (by rfl) ⟨3145589, by rfl⟩ : syracuseStep 4194119 = 6291179) B6291179
theorem B181477259 : Blo 323837 181477259 := bstep (se 1 (by rfl) ⟨136107944, by rfl⟩ : syracuseStep 181477259 = 272215889) B272215889
theorem B696347 : Blo 323837 696347 := bstep (se 1 (by rfl) ⟨522260, by rfl⟩ : syracuseStep 696347 = 1044521) B1044521
theorem B794887 : Blo 323837 794887 := bstep (se 1 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 794887 = 1192331) B1192331
theorem B1385191 : Blo 323837 1385191 := bstep (se 1 (by rfl) ⟨1038893, by rfl⟩ : syracuseStep 1385191 = 2077787) B2077787
theorem B3122489 : Blo 323837 3122489 := bstep (se 2 (by rfl) ⟨1170933, by rfl⟩ : syracuseStep 3122489 = 2341867) B2341867
theorem B2796079 : Blo 323837 2796079 := bstep (se 1 (by rfl) ⟨2097059, by rfl⟩ : syracuseStep 2796079 = 4194119) B4194119
theorem B731807 : Blo 323837 731807 := bstep (se 1 (by rfl) ⟨548855, by rfl⟩ : syracuseStep 731807 = 1097711) B1097711
theorem B371623 : Blo 323837 371623 := bstep (se 1 (by rfl) ⟨278717, by rfl⟩ : syracuseStep 371623 = 557435) B557435
theorem B732473 : Blo 323837 732473 := bstep (se 2 (by rfl) ⟨274677, by rfl⟩ : syracuseStep 732473 = 549355) B549355
theorem B1486363 : Blo 323837 1486363 := bstep (se 1 (by rfl) ⟨1114772, by rfl⟩ : syracuseStep 1486363 = 2229545) B2229545
theorem B733031 : Blo 323837 733031 := bstep (se 1 (by rfl) ⟨549773, by rfl⟩ : syracuseStep 733031 = 1099547) B1099547
theorem B2504047 : Blo 323837 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B5617469 : Blo 323837 5617469 := bstep (se 3 (by rfl) ⟨1053275, by rfl⟩ : syracuseStep 5617469 = 2106551) B2106551
theorem B735983 : Blo 323837 735983 := bstep (se 1 (by rfl) ⟨551987, by rfl⟩ : syracuseStep 735983 = 1103975) B1103975
theorem B40356301 : Blo 323837 40356301 := bstep (se 3 (by rfl) ⟨7566806, by rfl⟩ : syracuseStep 40356301 = 15133613) B15133613
theorem B1100681 : Blo 323837 1100681 := bstep (se 2 (by rfl) ⟨412755, by rfl⟩ : syracuseStep 1100681 = 825511) B825511
theorem B1104299 : Blo 323837 1104299 := bstep (se 1 (by rfl) ⟨828224, by rfl⟩ : syracuseStep 1104299 = 1656449) B1656449
theorem B3627487 : Blo 323837 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B1238753 : Blo 323837 1238753 := bstep (se 2 (by rfl) ⟨464532, by rfl⟩ : syracuseStep 1238753 = 929065) B929065
theorem B486143 : Blo 323837 486143 := bstep (se 1 (by rfl) ⟨364607, by rfl⟩ : syracuseStep 486143 = 729215) B729215
theorem B486953 : Blo 323837 486953 := bstep (se 2 (by rfl) ⟨182607, by rfl⟩ : syracuseStep 486953 = 365215) B365215
theorem B7041593 : Blo 323837 7041593 := bstep (se 2 (by rfl) ⟨2640597, by rfl⟩ : syracuseStep 7041593 = 5281195) B5281195
theorem B324911 : Blo 323837 324911 := bstep (se 1 (by rfl) ⟨243683, by rfl⟩ : syracuseStep 324911 = 487367) B487367
theorem B327359 : Blo 323837 327359 := bstep (se 1 (by rfl) ⟨245519, by rfl⟩ : syracuseStep 327359 = 491039) B491039
theorem B2981771 : Blo 323837 2981771 := bstep (se 1 (by rfl) ⟨2236328, by rfl⟩ : syracuseStep 2981771 = 4472657) B4472657
theorem B18777581 : Blo 323837 18777581 := bstep (se 3 (by rfl) ⟨3520796, by rfl⟩ : syracuseStep 18777581 = 7041593) B7041593
theorem B53808401 : Blo 323837 53808401 := bstep (se 2 (by rfl) ⟨20178150, by rfl⟩ : syracuseStep 53808401 = 40356301) B40356301
theorem B495497 : Blo 323837 495497 := bstep (se 2 (by rfl) ⟨185811, by rfl⟩ : syracuseStep 495497 = 371623) B371623
theorem B14979917 : Blo 323837 14979917 := bstep (se 3 (by rfl) ⟨2808734, by rfl⟩ : syracuseStep 14979917 = 5617469) B5617469
theorem B120984839 : Blo 323837 120984839 := bstep (se 1 (by rfl) ⟨90738629, by rfl⟩ : syracuseStep 120984839 = 181477259) B181477259
theorem B464231 : Blo 323837 464231 := bstep (se 1 (by rfl) ⟨348173, by rfl⟩ : syracuseStep 464231 = 696347) B696347
theorem B825835 : Blo 323837 825835 := bstep (se 1 (by rfl) ⟨619376, by rfl⟩ : syracuseStep 825835 = 1238753) B1238753
theorem B1846921 : Blo 323837 1846921 := bstep (se 2 (by rfl) ⟨692595, by rfl⟩ : syracuseStep 1846921 = 1385191) B1385191
theorem B4239397 : Blo 323837 4239397 := bstep (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) B794887
theorem B733787 : Blo 323837 733787 := bstep (se 1 (by rfl) ⟨550340, by rfl⟩ : syracuseStep 733787 = 1100681) B1100681
theorem B19346597 : Blo 323837 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B736199 : Blo 323837 736199 := bstep (se 1 (by rfl) ⟨552149, by rfl⟩ : syracuseStep 736199 = 1104299) B1104299
theorem B1981817 : Blo 323837 1981817 := bstep (se 2 (by rfl) ⟨743181, by rfl⟩ : syracuseStep 1981817 = 1486363) B1486363
theorem B2081659 : Blo 323837 2081659 := bstep (se 1 (by rfl) ⟨1561244, by rfl⟩ : syracuseStep 2081659 = 3122489) B3122489
theorem B1987847 : Blo 323837 1987847 := bstep (se 1 (by rfl) ⟨1490885, by rfl⟩ : syracuseStep 1987847 = 2981771) B2981771
theorem B3728105 : Blo 323837 3728105 := bstep (se 2 (by rfl) ⟨1398039, by rfl⟩ : syracuseStep 3728105 = 2796079) B2796079
theorem B487871 : Blo 323837 487871 := bstep (se 1 (by rfl) ⟨365903, by rfl⟩ : syracuseStep 487871 = 731807) B731807
theorem B3338729 : Blo 323837 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B324095 : Blo 323837 324095 := bstep (se 1 (by rfl) ⟨243071, by rfl⟩ : syracuseStep 324095 = 486143) B486143
theorem B488315 : Blo 323837 488315 := bstep (se 1 (by rfl) ⟨366236, by rfl⟩ : syracuseStep 488315 = 732473) B732473
theorem B324635 : Blo 323837 324635 := bstep (se 1 (by rfl) ⟨243476, by rfl⟩ : syracuseStep 324635 = 486953) B486953
theorem B488687 : Blo 323837 488687 := bstep (se 1 (by rfl) ⟨366515, by rfl⟩ : syracuseStep 488687 = 733031) B733031
theorem B490655 : Blo 323837 490655 := bstep (se 1 (by rfl) ⟨367991, by rfl⟩ : syracuseStep 490655 = 735983) B735983
theorem B22610117 : Blo 323837 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B12518387 : Blo 323837 12518387 := bstep (se 1 (by rfl) ⟨9388790, by rfl⟩ : syracuseStep 12518387 = 18777581) B18777581
theorem B39946445 : Blo 323837 39946445 := bstep (se 3 (by rfl) ⟨7489958, by rfl⟩ : syracuseStep 39946445 = 14979917) B14979917
theorem B2462561 : Blo 323837 2462561 := bstep (se 2 (by rfl) ⟨923460, by rfl⟩ : syracuseStep 2462561 = 1846921) B1846921
theorem B1321211 : Blo 323837 1321211 := bstep (se 1 (by rfl) ⟨990908, by rfl⟩ : syracuseStep 1321211 = 1981817) B1981817
theorem B1321325 : Blo 323837 1321325 := bstep (se 3 (by rfl) ⟨247748, by rfl⟩ : syracuseStep 1321325 = 495497) B495497
theorem B1325231 : Blo 323837 1325231 := bstep (se 1 (by rfl) ⟨993923, by rfl⟩ : syracuseStep 1325231 = 1987847) B1987847
theorem B80656559 : Blo 323837 80656559 := bstep (se 1 (by rfl) ⟨60492419, by rfl⟩ : syracuseStep 80656559 = 120984839) B120984839
theorem B1101113 : Blo 323837 1101113 := bstep (se 2 (by rfl) ⟨412917, by rfl⟩ : syracuseStep 1101113 = 825835) B825835
theorem B12897731 : Blo 323837 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B2775545 : Blo 323837 2775545 := bstep (se 2 (by rfl) ⟨1040829, by rfl⟩ : syracuseStep 2775545 = 2081659) B2081659
theorem B1237949 : Blo 323837 1237949 := bstep (se 3 (by rfl) ⟨232115, by rfl⟩ : syracuseStep 1237949 = 464231) B464231
theorem B2485403 : Blo 323837 2485403 := bstep (se 1 (by rfl) ⟨1864052, by rfl⟩ : syracuseStep 2485403 = 3728105) B3728105
theorem B325247 : Blo 323837 325247 := bstep (se 1 (by rfl) ⟨243935, by rfl⟩ : syracuseStep 325247 = 487871) B487871
theorem B2225819 : Blo 323837 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B489191 : Blo 323837 489191 := bstep (se 1 (by rfl) ⟨366893, by rfl⟩ : syracuseStep 489191 = 733787) B733787
theorem B325543 : Blo 323837 325543 := bstep (se 1 (by rfl) ⟨244157, by rfl⟩ : syracuseStep 325543 = 488315) B488315
theorem B143489069 : Blo 323837 143489069 := bstep (se 3 (by rfl) ⟨26904200, by rfl⟩ : syracuseStep 143489069 = 53808401) B53808401
theorem B325791 : Blo 323837 325791 := bstep (se 1 (by rfl) ⟨244343, by rfl⟩ : syracuseStep 325791 = 488687) B488687
theorem B490799 : Blo 323837 490799 := bstep (se 1 (by rfl) ⟨368099, by rfl⟩ : syracuseStep 490799 = 736199) B736199
theorem B327103 : Blo 323837 327103 := bstep (se 1 (by rfl) ⟨245327, by rfl⟩ : syracuseStep 327103 = 490655) B490655
theorem B60293645 : Blo 323837 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B1641707 : Blo 323837 1641707 := bstep (se 1 (by rfl) ⟨1231280, by rfl⟩ : syracuseStep 1641707 = 2462561) B2462561
theorem B5935517 : Blo 323837 5935517 := bstep (se 3 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 5935517 = 2225819) B2225819
theorem B825299 : Blo 323837 825299 := bstep (se 1 (by rfl) ⟨618974, by rfl⟩ : syracuseStep 825299 = 1237949) B1237949
theorem B95659379 : Blo 323837 95659379 := bstep (se 1 (by rfl) ⟨71744534, by rfl⟩ : syracuseStep 95659379 = 143489069) B143489069
theorem B734075 : Blo 323837 734075 := bstep (se 1 (by rfl) ⟨550556, by rfl⟩ : syracuseStep 734075 = 1101113) B1101113
theorem B8598487 : Blo 323837 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B1850363 : Blo 323837 1850363 := bstep (se 1 (by rfl) ⟨1387772, by rfl⟩ : syracuseStep 1850363 = 2775545) B2775545
theorem B1656935 : Blo 323837 1656935 := bstep (se 1 (by rfl) ⟨1242701, by rfl⟩ : syracuseStep 1656935 = 2485403) B2485403
theorem B8345591 : Blo 323837 8345591 := bstep (se 1 (by rfl) ⟨6259193, by rfl⟩ : syracuseStep 8345591 = 12518387) B12518387
theorem B26630963 : Blo 323837 26630963 := bstep (se 1 (by rfl) ⟨19973222, by rfl⟩ : syracuseStep 26630963 = 39946445) B39946445
theorem B880807 : Blo 323837 880807 := bstep (se 1 (by rfl) ⟨660605, by rfl⟩ : syracuseStep 880807 = 1321211) B1321211
theorem B880883 : Blo 323837 880883 := bstep (se 1 (by rfl) ⟨660662, by rfl⟩ : syracuseStep 880883 = 1321325) B1321325
theorem B326127 : Blo 323837 326127 := bstep (se 1 (by rfl) ⟨244595, by rfl⟩ : syracuseStep 326127 = 489191) B489191
theorem B883487 : Blo 323837 883487 := bstep (se 1 (by rfl) ⟨662615, by rfl⟩ : syracuseStep 883487 = 1325231) B1325231
theorem B53771039 : Blo 323837 53771039 := bstep (se 1 (by rfl) ⟨40328279, by rfl⟩ : syracuseStep 53771039 = 80656559) B80656559
theorem B327199 : Blo 323837 327199 := bstep (se 1 (by rfl) ⟨245399, by rfl⟩ : syracuseStep 327199 = 490799) B490799
theorem B63772919 : Blo 323837 63772919 := bstep (se 1 (by rfl) ⟨47829689, by rfl⟩ : syracuseStep 63772919 = 95659379) B95659379
theorem B1094471 : Blo 323837 1094471 := bstep (se 1 (by rfl) ⟨820853, by rfl⟩ : syracuseStep 1094471 = 1641707) B1641707
theorem B1233575 : Blo 323837 1233575 := bstep (se 1 (by rfl) ⟨925181, by rfl⟩ : syracuseStep 1233575 = 1850363) B1850363
theorem B40195763 : Blo 323837 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B1104623 : Blo 323837 1104623 := bstep (se 1 (by rfl) ⟨828467, by rfl⟩ : syracuseStep 1104623 = 1656935) B1656935
theorem B3957011 : Blo 323837 3957011 := bstep (se 1 (by rfl) ⟨2967758, by rfl⟩ : syracuseStep 3957011 = 5935517) B5935517
theorem B550199 : Blo 323837 550199 := bstep (se 1 (by rfl) ⟨412649, by rfl⟩ : syracuseStep 550199 = 825299) B825299
theorem B5563727 : Blo 323837 5563727 := bstep (se 1 (by rfl) ⟨4172795, by rfl⟩ : syracuseStep 5563727 = 8345591) B8345591
theorem B17753975 : Blo 323837 17753975 := bstep (se 1 (by rfl) ⟨13315481, by rfl⟩ : syracuseStep 17753975 = 26630963) B26630963
theorem B1174409 : Blo 323837 1174409 := bstep (se 2 (by rfl) ⟨440403, by rfl⟩ : syracuseStep 1174409 = 880807) B880807
theorem B11464649 : Blo 323837 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B2355965 : Blo 323837 2355965 := bstep (se 3 (by rfl) ⟨441743, by rfl⟩ : syracuseStep 2355965 = 883487) B883487
theorem B587255 : Blo 323837 587255 := bstep (se 1 (by rfl) ⟨440441, by rfl⟩ : syracuseStep 587255 = 880883) B880883
theorem B489383 : Blo 323837 489383 := bstep (se 1 (by rfl) ⟨367037, by rfl⟩ : syracuseStep 489383 = 734075) B734075
theorem B35847359 : Blo 323837 35847359 := bstep (se 1 (by rfl) ⟨26885519, by rfl⟩ : syracuseStep 35847359 = 53771039) B53771039
theorem B822383 : Blo 323837 822383 := bstep (se 1 (by rfl) ⟨616787, by rfl⟩ : syracuseStep 822383 = 1233575) B1233575
theorem B366799 : Blo 323837 366799 := bstep (se 1 (by rfl) ⟨275099, by rfl⟩ : syracuseStep 366799 = 550199) B550199
theorem B3709151 : Blo 323837 3709151 := bstep (se 1 (by rfl) ⟨2781863, by rfl⟩ : syracuseStep 3709151 = 5563727) B5563727
theorem B11835983 : Blo 323837 11835983 := bstep (se 1 (by rfl) ⟨8876987, by rfl⟩ : syracuseStep 11835983 = 17753975) B17753975
theorem B7643099 : Blo 323837 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B729647 : Blo 323837 729647 := bstep (se 1 (by rfl) ⟨547235, by rfl⟩ : syracuseStep 729647 = 1094471) B1094471
theorem B23898239 : Blo 323837 23898239 := bstep (se 1 (by rfl) ⟨17923679, by rfl⟩ : syracuseStep 23898239 = 35847359) B35847359
theorem B42515279 : Blo 323837 42515279 := bstep (se 1 (by rfl) ⟨31886459, by rfl⟩ : syracuseStep 42515279 = 63772919) B63772919
theorem B736415 : Blo 323837 736415 := bstep (se 1 (by rfl) ⟨552311, by rfl⟩ : syracuseStep 736415 = 1104623) B1104623
theorem B2638007 : Blo 323837 2638007 := bstep (se 1 (by rfl) ⟨1978505, by rfl⟩ : syracuseStep 2638007 = 3957011) B3957011
theorem B26797175 : Blo 323837 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B1566013 : Blo 323837 1566013 := bstep (se 3 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 1566013 = 587255) B587255
theorem B782939 : Blo 323837 782939 := bstep (se 1 (by rfl) ⟨587204, by rfl⟩ : syracuseStep 782939 = 1174409) B1174409
theorem B1570643 : Blo 323837 1570643 := bstep (se 1 (by rfl) ⟨1177982, by rfl⟩ : syracuseStep 1570643 = 2355965) B2355965
theorem B326255 : Blo 323837 326255 := bstep (se 1 (by rfl) ⟨244691, by rfl⟩ : syracuseStep 326255 = 489383) B489383
theorem B17864783 : Blo 323837 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B15932159 : Blo 323837 15932159 := bstep (se 1 (by rfl) ⟨11949119, by rfl⟩ : syracuseStep 15932159 = 23898239) B23898239
theorem B2472767 : Blo 323837 2472767 := bstep (se 1 (by rfl) ⟨1854575, by rfl⟩ : syracuseStep 2472767 = 3709151) B3709151
theorem B5095399 : Blo 323837 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B1758671 : Blo 323837 1758671 := bstep (se 1 (by rfl) ⟨1319003, by rfl⟩ : syracuseStep 1758671 = 2638007) B2638007
theorem B2088017 : Blo 323837 2088017 := bstep (se 2 (by rfl) ⟨783006, by rfl⟩ : syracuseStep 2088017 = 1566013) B1566013
theorem B548255 : Blo 323837 548255 := bstep (se 1 (by rfl) ⟨411191, by rfl⟩ : syracuseStep 548255 = 822383) B822383
theorem B7890655 : Blo 323837 7890655 := bstep (se 1 (by rfl) ⟨5917991, by rfl⟩ : syracuseStep 7890655 = 11835983) B11835983
theorem B486431 : Blo 323837 486431 := bstep (se 1 (by rfl) ⟨364823, by rfl⟩ : syracuseStep 486431 = 729647) B729647
theorem B489065 : Blo 323837 489065 := bstep (se 2 (by rfl) ⟨183399, by rfl⟩ : syracuseStep 489065 = 366799) B366799
theorem B521959 : Blo 323837 521959 := bstep (se 1 (by rfl) ⟨391469, by rfl⟩ : syracuseStep 521959 = 782939) B782939
theorem B1047095 : Blo 323837 1047095 := bstep (se 1 (by rfl) ⟨785321, by rfl⟩ : syracuseStep 1047095 = 1570643) B1570643
theorem B28343519 : Blo 323837 28343519 := bstep (se 1 (by rfl) ⟨21257639, by rfl⟩ : syracuseStep 28343519 = 42515279) B42515279
theorem B490943 : Blo 323837 490943 := bstep (se 1 (by rfl) ⟨368207, by rfl⟩ : syracuseStep 490943 = 736415) B736415
theorem B10520873 : Blo 323837 10520873 := bstep (se 2 (by rfl) ⟨3945327, by rfl⟩ : syracuseStep 10520873 = 7890655) B7890655
theorem B10621439 : Blo 323837 10621439 := bstep (se 1 (by rfl) ⟨7966079, by rfl⟩ : syracuseStep 10621439 = 15932159) B15932159
theorem B365503 : Blo 323837 365503 := bstep (se 1 (by rfl) ⟨274127, by rfl⟩ : syracuseStep 365503 = 548255) B548255
theorem B695945 : Blo 323837 695945 := bstep (se 2 (by rfl) ⟨260979, by rfl⟩ : syracuseStep 695945 = 521959) B521959
theorem B698063 : Blo 323837 698063 := bstep (se 1 (by rfl) ⟨523547, by rfl⟩ : syracuseStep 698063 = 1047095) B1047095
theorem B1648511 : Blo 323837 1648511 := bstep (se 1 (by rfl) ⟨1236383, by rfl⟩ : syracuseStep 1648511 = 2472767) B2472767
theorem B6793865 : Blo 323837 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B11909855 : Blo 323837 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B1392011 : Blo 323837 1392011 := bstep (se 1 (by rfl) ⟨1044008, by rfl⟩ : syracuseStep 1392011 = 2088017) B2088017
theorem B18895679 : Blo 323837 18895679 := bstep (se 1 (by rfl) ⟨14171759, by rfl⟩ : syracuseStep 18895679 = 28343519) B28343519
theorem B1172447 : Blo 323837 1172447 := bstep (se 1 (by rfl) ⟨879335, by rfl⟩ : syracuseStep 1172447 = 1758671) B1758671
theorem B324287 : Blo 323837 324287 := bstep (se 1 (by rfl) ⟨243215, by rfl⟩ : syracuseStep 324287 = 486431) B486431
theorem B326043 : Blo 323837 326043 := bstep (se 1 (by rfl) ⟨244532, by rfl⟩ : syracuseStep 326043 = 489065) B489065
theorem B327295 : Blo 323837 327295 := bstep (se 1 (by rfl) ⟨245471, by rfl⟩ : syracuseStep 327295 = 490943) B490943
theorem B7013915 : Blo 323837 7013915 := bstep (se 1 (by rfl) ⟨5260436, by rfl⟩ : syracuseStep 7013915 = 10520873) B10520873
theorem B7080959 : Blo 323837 7080959 := bstep (se 1 (by rfl) ⟨5310719, by rfl⟩ : syracuseStep 7080959 = 10621439) B10621439
theorem B463963 : Blo 323837 463963 := bstep (se 1 (by rfl) ⟨347972, by rfl⟩ : syracuseStep 463963 = 695945) B695945
theorem B4529243 : Blo 323837 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B7939903 : Blo 323837 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B928007 : Blo 323837 928007 := bstep (se 1 (by rfl) ⟨696005, by rfl⟩ : syracuseStep 928007 = 1392011) B1392011
theorem B12597119 : Blo 323837 12597119 := bstep (se 1 (by rfl) ⟨9447839, by rfl⟩ : syracuseStep 12597119 = 18895679) B18895679
theorem B1099007 : Blo 323837 1099007 := bstep (se 1 (by rfl) ⟨824255, by rfl⟩ : syracuseStep 1099007 = 1648511) B1648511
theorem B1861501 : Blo 323837 1861501 := bstep (se 3 (by rfl) ⟨349031, by rfl⟩ : syracuseStep 1861501 = 698063) B698063
theorem B781631 : Blo 323837 781631 := bstep (se 1 (by rfl) ⟨586223, by rfl⟩ : syracuseStep 781631 = 1172447) B1172447
theorem B487337 : Blo 323837 487337 := bstep (se 2 (by rfl) ⟨182751, by rfl⟩ : syracuseStep 487337 = 365503) B365503
theorem B4720639 : Blo 323837 4720639 := bstep (se 1 (by rfl) ⟨3540479, by rfl⟩ : syracuseStep 4720639 = 7080959) B7080959
theorem B10586537 : Blo 323837 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B8398079 : Blo 323837 8398079 := bstep (se 1 (by rfl) ⟨6298559, by rfl⟩ : syracuseStep 8398079 = 12597119) B12597119
theorem B732671 : Blo 323837 732671 := bstep (se 1 (by rfl) ⟨549503, by rfl⟩ : syracuseStep 732671 = 1099007) B1099007
theorem B12077981 : Blo 323837 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B4675943 : Blo 323837 4675943 := bstep (se 1 (by rfl) ⟨3506957, by rfl⟩ : syracuseStep 4675943 = 7013915) B7013915
theorem B2482001 : Blo 323837 2482001 := bstep (se 2 (by rfl) ⟨930750, by rfl⟩ : syracuseStep 2482001 = 1861501) B1861501
theorem B618617 : Blo 323837 618617 := bstep (se 2 (by rfl) ⟨231981, by rfl⟩ : syracuseStep 618617 = 463963) B463963
theorem B618671 : Blo 323837 618671 := bstep (se 1 (by rfl) ⟨464003, by rfl⟩ : syracuseStep 618671 = 928007) B928007
theorem B521087 : Blo 323837 521087 := bstep (se 1 (by rfl) ⟨390815, by rfl⟩ : syracuseStep 521087 = 781631) B781631
theorem B324891 : Blo 323837 324891 := bstep (se 1 (by rfl) ⟨243668, by rfl⟩ : syracuseStep 324891 = 487337) B487337
theorem B6294185 : Blo 323837 6294185 := bstep (se 2 (by rfl) ⟨2360319, by rfl⟩ : syracuseStep 6294185 = 4720639) B4720639
theorem B3117295 : Blo 323837 3117295 := bstep (se 1 (by rfl) ⟨2337971, by rfl⟩ : syracuseStep 3117295 = 4675943) B4675943
theorem B1649645 : Blo 323837 1649645 := bstep (se 3 (by rfl) ⟨309308, by rfl⟩ : syracuseStep 1649645 = 618617) B618617
theorem B7057691 : Blo 323837 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B1389565 : Blo 323837 1389565 := bstep (se 3 (by rfl) ⟨260543, by rfl⟩ : syracuseStep 1389565 = 521087) B521087
theorem B1654667 : Blo 323837 1654667 := bstep (se 1 (by rfl) ⟨1241000, by rfl⟩ : syracuseStep 1654667 = 2482001) B2482001
theorem B412447 : Blo 323837 412447 := bstep (se 1 (by rfl) ⟨309335, by rfl⟩ : syracuseStep 412447 = 618671) B618671
theorem B8051987 : Blo 323837 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B5598719 : Blo 323837 5598719 := bstep (se 1 (by rfl) ⟨4199039, by rfl⟩ : syracuseStep 5598719 = 8398079) B8398079
theorem B488447 : Blo 323837 488447 := bstep (se 1 (by rfl) ⟨366335, by rfl⟩ : syracuseStep 488447 = 732671) B732671
theorem B4196123 : Blo 323837 4196123 := bstep (se 1 (by rfl) ⟨3147092, by rfl⟩ : syracuseStep 4196123 = 6294185) B6294185
theorem B1852753 : Blo 323837 1852753 := bstep (se 2 (by rfl) ⟨694782, by rfl⟩ : syracuseStep 1852753 = 1389565) B1389565
theorem B1099763 : Blo 323837 1099763 := bstep (se 1 (by rfl) ⟨824822, by rfl⟩ : syracuseStep 1099763 = 1649645) B1649645
theorem B4705127 : Blo 323837 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B1103111 : Blo 323837 1103111 := bstep (se 1 (by rfl) ⟨827333, by rfl⟩ : syracuseStep 1103111 = 1654667) B1654667
theorem B549929 : Blo 323837 549929 := bstep (se 2 (by rfl) ⟨206223, by rfl⟩ : syracuseStep 549929 = 412447) B412447
theorem B5367991 : Blo 323837 5367991 := bstep (se 1 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 5367991 = 8051987) B8051987
theorem B4156393 : Blo 323837 4156393 := bstep (se 2 (by rfl) ⟨1558647, by rfl⟩ : syracuseStep 4156393 = 3117295) B3117295
theorem B3732479 : Blo 323837 3732479 := bstep (se 1 (by rfl) ⟨2799359, by rfl⟩ : syracuseStep 3732479 = 5598719) B5598719
theorem B325631 : Blo 323837 325631 := bstep (se 1 (by rfl) ⟨244223, by rfl⟩ : syracuseStep 325631 = 488447) B488447
theorem B5541857 : Blo 323837 5541857 := bstep (se 2 (by rfl) ⟨2078196, by rfl⟩ : syracuseStep 5541857 = 4156393) B4156393
theorem B366619 : Blo 323837 366619 := bstep (se 1 (by rfl) ⟨274964, by rfl⟩ : syracuseStep 366619 = 549929) B549929
theorem B2797415 : Blo 323837 2797415 := bstep (se 1 (by rfl) ⟨2098061, by rfl⟩ : syracuseStep 2797415 = 4196123) B4196123
theorem B733175 : Blo 323837 733175 := bstep (se 1 (by rfl) ⟨549881, by rfl⟩ : syracuseStep 733175 = 1099763) B1099763
theorem B2470337 : Blo 323837 2470337 := bstep (se 2 (by rfl) ⟨926376, by rfl⟩ : syracuseStep 2470337 = 1852753) B1852753
theorem B7157321 : Blo 323837 7157321 := bstep (se 2 (by rfl) ⟨2683995, by rfl⟩ : syracuseStep 7157321 = 5367991) B5367991
theorem B735407 : Blo 323837 735407 := bstep (se 1 (by rfl) ⟨551555, by rfl⟩ : syracuseStep 735407 = 1103111) B1103111
theorem B3136751 : Blo 323837 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B2488319 : Blo 323837 2488319 := bstep (se 1 (by rfl) ⟨1866239, by rfl⟩ : syracuseStep 2488319 = 3732479) B3732479
theorem B1646891 : Blo 323837 1646891 := bstep (se 1 (by rfl) ⟨1235168, by rfl⟩ : syracuseStep 1646891 = 2470337) B2470337
theorem B4771547 : Blo 323837 4771547 := bstep (se 1 (by rfl) ⟨3578660, by rfl⟩ : syracuseStep 4771547 = 7157321) B7157321
theorem B1658879 : Blo 323837 1658879 := bstep (se 1 (by rfl) ⟨1244159, by rfl⟩ : syracuseStep 1658879 = 2488319) B2488319
theorem B3694571 : Blo 323837 3694571 := bstep (se 1 (by rfl) ⟨2770928, by rfl⟩ : syracuseStep 3694571 = 5541857) B5541857
theorem B2091167 : Blo 323837 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B1864943 : Blo 323837 1864943 := bstep (se 1 (by rfl) ⟨1398707, by rfl⟩ : syracuseStep 1864943 = 2797415) B2797415
theorem B488783 : Blo 323837 488783 := bstep (se 1 (by rfl) ⟨366587, by rfl⟩ : syracuseStep 488783 = 733175) B733175
theorem B488825 : Blo 323837 488825 := bstep (se 2 (by rfl) ⟨183309, by rfl⟩ : syracuseStep 488825 = 366619) B366619
theorem B490271 : Blo 323837 490271 := bstep (se 1 (by rfl) ⟨367703, by rfl⟩ : syracuseStep 490271 = 735407) B735407
theorem B3181031 : Blo 323837 3181031 := bstep (se 1 (by rfl) ⟨2385773, by rfl⟩ : syracuseStep 3181031 = 4771547) B4771547
theorem B2463047 : Blo 323837 2463047 := bstep (se 1 (by rfl) ⟨1847285, by rfl⟩ : syracuseStep 2463047 = 3694571) B3694571
theorem B1097927 : Blo 323837 1097927 := bstep (se 1 (by rfl) ⟨823445, by rfl⟩ : syracuseStep 1097927 = 1646891) B1646891
theorem B1394111 : Blo 323837 1394111 := bstep (se 1 (by rfl) ⟨1045583, by rfl⟩ : syracuseStep 1394111 = 2091167) B2091167
theorem B1105919 : Blo 323837 1105919 := bstep (se 1 (by rfl) ⟨829439, by rfl⟩ : syracuseStep 1105919 = 1658879) B1658879
theorem B1243295 : Blo 323837 1243295 := bstep (se 1 (by rfl) ⟨932471, by rfl⟩ : syracuseStep 1243295 = 1864943) B1864943
theorem B325855 : Blo 323837 325855 := bstep (se 1 (by rfl) ⟨244391, by rfl⟩ : syracuseStep 325855 = 488783) B488783
theorem B325883 : Blo 323837 325883 := bstep (se 1 (by rfl) ⟨244412, by rfl⟩ : syracuseStep 325883 = 488825) B488825
theorem B326847 : Blo 323837 326847 := bstep (se 1 (by rfl) ⟨245135, by rfl⟩ : syracuseStep 326847 = 490271) B490271
theorem B1642031 : Blo 323837 1642031 := bstep (se 1 (by rfl) ⟨1231523, by rfl⟩ : syracuseStep 1642031 = 2463047) B2463047
theorem B828863 : Blo 323837 828863 := bstep (se 1 (by rfl) ⟨621647, by rfl⟩ : syracuseStep 828863 = 1243295) B1243295
theorem B731951 : Blo 323837 731951 := bstep (se 1 (by rfl) ⟨548963, by rfl⟩ : syracuseStep 731951 = 1097927) B1097927
theorem B929407 : Blo 323837 929407 := bstep (se 1 (by rfl) ⟨697055, by rfl⟩ : syracuseStep 929407 = 1394111) B1394111
theorem B737279 : Blo 323837 737279 := bstep (se 1 (by rfl) ⟨552959, by rfl⟩ : syracuseStep 737279 = 1105919) B1105919
theorem B2120687 : Blo 323837 2120687 := bstep (se 1 (by rfl) ⟨1590515, by rfl⟩ : syracuseStep 2120687 = 3181031) B3181031
theorem B1413791 : Blo 323837 1413791 := bstep (se 1 (by rfl) ⟨1060343, by rfl⟩ : syracuseStep 1413791 = 2120687) B2120687
theorem B1094687 : Blo 323837 1094687 := bstep (se 1 (by rfl) ⟨821015, by rfl⟩ : syracuseStep 1094687 = 1642031) B1642031
theorem B491519 : Blo 323837 491519 := bstep (se 1 (by rfl) ⟨368639, by rfl⟩ : syracuseStep 491519 = 737279) B737279
theorem B1239209 : Blo 323837 1239209 := bstep (se 2 (by rfl) ⟨464703, by rfl⟩ : syracuseStep 1239209 = 929407) B929407
theorem B552575 : Blo 323837 552575 := bstep (se 1 (by rfl) ⟨414431, by rfl⟩ : syracuseStep 552575 = 828863) B828863
theorem B487967 : Blo 323837 487967 := bstep (se 1 (by rfl) ⟨365975, by rfl⟩ : syracuseStep 487967 = 731951) B731951
theorem B826139 : Blo 323837 826139 := bstep (se 1 (by rfl) ⟨619604, by rfl⟩ : syracuseStep 826139 = 1239209) B1239209
theorem B368383 : Blo 323837 368383 := bstep (se 1 (by rfl) ⟨276287, by rfl⟩ : syracuseStep 368383 = 552575) B552575
theorem B729791 : Blo 323837 729791 := bstep (se 1 (by rfl) ⟨547343, by rfl⟩ : syracuseStep 729791 = 1094687) B1094687
theorem B942527 : Blo 323837 942527 := bstep (se 1 (by rfl) ⟨706895, by rfl⟩ : syracuseStep 942527 = 1413791) B1413791
theorem B325311 : Blo 323837 325311 := bstep (se 1 (by rfl) ⟨243983, by rfl⟩ : syracuseStep 325311 = 487967) B487967
theorem B327679 : Blo 323837 327679 := bstep (se 1 (by rfl) ⟨245759, by rfl⟩ : syracuseStep 327679 = 491519) B491519
theorem B2513405 : Blo 323837 2513405 := bstep (se 3 (by rfl) ⟨471263, by rfl⟩ : syracuseStep 2513405 = 942527) B942527
theorem B550759 : Blo 323837 550759 := bstep (se 1 (by rfl) ⟨413069, by rfl⟩ : syracuseStep 550759 = 826139) B826139
theorem B486527 : Blo 323837 486527 := bstep (se 1 (by rfl) ⟨364895, by rfl⟩ : syracuseStep 486527 = 729791) B729791
theorem B491177 : Blo 323837 491177 := bstep (se 2 (by rfl) ⟨184191, by rfl⟩ : syracuseStep 491177 = 368383) B368383
theorem B1675603 : Blo 323837 1675603 := bstep (se 1 (by rfl) ⟨1256702, by rfl⟩ : syracuseStep 1675603 = 2513405) B2513405
theorem B734345 : Blo 323837 734345 := bstep (se 2 (by rfl) ⟨275379, by rfl⟩ : syracuseStep 734345 = 550759) B550759
theorem B324351 : Blo 323837 324351 := bstep (se 1 (by rfl) ⟨243263, by rfl⟩ : syracuseStep 324351 = 486527) B486527
theorem B327451 : Blo 323837 327451 := bstep (se 1 (by rfl) ⟨245588, by rfl⟩ : syracuseStep 327451 = 491177) B491177
theorem B2234137 : Blo 323837 2234137 := bstep (se 2 (by rfl) ⟨837801, by rfl⟩ : syracuseStep 2234137 = 1675603) B1675603
theorem B489563 : Blo 323837 489563 := bstep (se 1 (by rfl) ⟨367172, by rfl⟩ : syracuseStep 489563 = 734345) B734345
theorem B2978849 : Blo 323837 2978849 := bstep (se 2 (by rfl) ⟨1117068, by rfl⟩ : syracuseStep 2978849 = 2234137) B2234137
theorem B326375 : Blo 323837 326375 := bstep (se 1 (by rfl) ⟨244781, by rfl⟩ : syracuseStep 326375 = 489563) B489563
theorem B1985899 : Blo 323837 1985899 := bstep (se 1 (by rfl) ⟨1489424, by rfl⟩ : syracuseStep 1985899 = 2978849) B2978849
theorem B2647865 : Blo 323837 2647865 := bstep (se 2 (by rfl) ⟨992949, by rfl⟩ : syracuseStep 2647865 = 1985899) B1985899
theorem B1765243 : Blo 323837 1765243 := bstep (se 1 (by rfl) ⟨1323932, by rfl⟩ : syracuseStep 1765243 = 2647865) B2647865
theorem B2353657 : Blo 323837 2353657 := bstep (se 2 (by rfl) ⟨882621, by rfl⟩ : syracuseStep 2353657 = 1765243) B1765243
theorem B3138209 : Blo 323837 3138209 := bstep (se 2 (by rfl) ⟨1176828, by rfl⟩ : syracuseStep 3138209 = 2353657) B2353657
theorem B2092139 : Blo 323837 2092139 := bstep (se 1 (by rfl) ⟨1569104, by rfl⟩ : syracuseStep 2092139 = 3138209) B3138209
theorem B1394759 : Blo 323837 1394759 := bstep (se 1 (by rfl) ⟨1046069, by rfl⟩ : syracuseStep 1394759 = 2092139) B2092139
theorem B3719357 : Blo 323837 3719357 := bstep (se 3 (by rfl) ⟨697379, by rfl⟩ : syracuseStep 3719357 = 1394759) B1394759
theorem B2479571 : Blo 323837 2479571 := bstep (se 1 (by rfl) ⟨1859678, by rfl⟩ : syracuseStep 2479571 = 3719357) B3719357
theorem B1653047 : Blo 323837 1653047 := bstep (se 1 (by rfl) ⟨1239785, by rfl⟩ : syracuseStep 1653047 = 2479571) B2479571
theorem B1102031 : Blo 323837 1102031 := bstep (se 1 (by rfl) ⟨826523, by rfl⟩ : syracuseStep 1102031 = 1653047) B1653047
theorem B734687 : Blo 323837 734687 := bstep (se 1 (by rfl) ⟨551015, by rfl⟩ : syracuseStep 734687 = 1102031) B1102031
theorem B489791 : Blo 323837 489791 := bstep (se 1 (by rfl) ⟨367343, by rfl⟩ : syracuseStep 489791 = 734687) B734687
theorem B326527 : Blo 323837 326527 := bstep (se 1 (by rfl) ⟨244895, by rfl⟩ : syracuseStep 326527 = 489791) B489791

theorem C0 (j : ℕ) (h1 : 80959 ≤ j) (h2 : j ≤ 81658) : Blo 323837 (4 * j + 3) := by
  interval_cases j
  · exact B323839
  · exact B323843
  · exact B323847
  · exact B323851
  · exact B323855
  · exact B323859
  · exact B323863
  · exact B323867
  · exact B323871
  · exact B323875
  · exact B323879
  · exact B323883
  · exact B323887
  · exact B323891
  · exact B323895
  · exact B323899
  · exact B323903
  · exact B323907
  · exact B323911
  · exact B323915
  · exact B323919
  · exact B323923
  · exact B323927
  · exact B323931
  · exact B323935
  · exact B323939
  · exact B323943
  · exact B323947
  · exact B323951
  · exact B323955
  · exact B323959
  · exact B323963
  · exact B323967
  · exact B323971
  · exact B323975
  · exact B323979
  · exact B323983
  · exact B323987
  · exact B323991
  · exact B323995
  · exact B323999
  · exact B324003
  · exact B324007
  · exact B324011
  · exact B324015
  · exact B324019
  · exact B324023
  · exact B324027
  · exact B324031
  · exact B324035
  · exact B324039
  · exact B324043
  · exact B324047
  · exact B324051
  · exact B324055
  · exact B324059
  · exact B324063
  · exact B324067
  · exact B324071
  · exact B324075
  · exact B324079
  · exact B324083
  · exact B324087
  · exact B324091
  · exact B324095
  · exact B324099
  · exact B324103
  · exact B324107
  · exact B324111
  · exact B324115
  · exact B324119
  · exact B324123
  · exact B324127
  · exact B324131
  · exact B324135
  · exact B324139
  · exact B324143
  · exact B324147
  · exact B324151
  · exact B324155
  · exact B324159
  · exact B324163
  · exact B324167
  · exact B324171
  · exact B324175
  · exact B324179
  · exact B324183
  · exact B324187
  · exact B324191
  · exact B324195
  · exact B324199
  · exact B324203
  · exact B324207
  · exact B324211
  · exact B324215
  · exact B324219
  · exact B324223
  · exact B324227
  · exact B324231
  · exact B324235
  · exact B324239
  · exact B324243
  · exact B324247
  · exact B324251
  · exact B324255
  · exact B324259
  · exact B324263
  · exact B324267
  · exact B324271
  · exact B324275
  · exact B324279
  · exact B324283
  · exact B324287
  · exact B324291
  · exact B324295
  · exact B324299
  · exact B324303
  · exact B324307
  · exact B324311
  · exact B324315
  · exact B324319
  · exact B324323
  · exact B324327
  · exact B324331
  · exact B324335
  · exact B324339
  · exact B324343
  · exact B324347
  · exact B324351
  · exact B324355
  · exact B324359
  · exact B324363
  · exact B324367
  · exact B324371
  · exact B324375
  · exact B324379
  · exact B324383
  · exact B324387
  · exact B324391
  · exact B324395
  · exact B324399
  · exact B324403
  · exact B324407
  · exact B324411
  · exact B324415
  · exact B324419
  · exact B324423
  · exact B324427
  · exact B324431
  · exact B324435
  · exact B324439
  · exact B324443
  · exact B324447
  · exact B324451
  · exact B324455
  · exact B324459
  · exact B324463
  · exact B324467
  · exact B324471
  · exact B324475
  · exact B324479
  · exact B324483
  · exact B324487
  · exact B324491
  · exact B324495
  · exact B324499
  · exact B324503
  · exact B324507
  · exact B324511
  · exact B324515
  · exact B324519
  · exact B324523
  · exact B324527
  · exact B324531
  · exact B324535
  · exact B324539
  · exact B324543
  · exact B324547
  · exact B324551
  · exact B324555
  · exact B324559
  · exact B324563
  · exact B324567
  · exact B324571
  · exact B324575
  · exact B324579
  · exact B324583
  · exact B324587
  · exact B324591
  · exact B324595
  · exact B324599
  · exact B324603
  · exact B324607
  · exact B324611
  · exact B324615
  · exact B324619
  · exact B324623
  · exact B324627
  · exact B324631
  · exact B324635
  · exact B324639
  · exact B324643
  · exact B324647
  · exact B324651
  · exact B324655
  · exact B324659
  · exact B324663
  · exact B324667
  · exact B324671
  · exact B324675
  · exact B324679
  · exact B324683
  · exact B324687
  · exact B324691
  · exact B324695
  · exact B324699
  · exact B324703
  · exact B324707
  · exact B324711
  · exact B324715
  · exact B324719
  · exact B324723
  · exact B324727
  · exact B324731
  · exact B324735
  · exact B324739
  · exact B324743
  · exact B324747
  · exact B324751
  · exact B324755
  · exact B324759
  · exact B324763
  · exact B324767
  · exact B324771
  · exact B324775
  · exact B324779
  · exact B324783
  · exact B324787
  · exact B324791
  · exact B324795
  · exact B324799
  · exact B324803
  · exact B324807
  · exact B324811
  · exact B324815
  · exact B324819
  · exact B324823
  · exact B324827
  · exact B324831
  · exact B324835
  · exact B324839
  · exact B324843
  · exact B324847
  · exact B324851
  · exact B324855
  · exact B324859
  · exact B324863
  · exact B324867
  · exact B324871
  · exact B324875
  · exact B324879
  · exact B324883
  · exact B324887
  · exact B324891
  · exact B324895
  · exact B324899
  · exact B324903
  · exact B324907
  · exact B324911
  · exact B324915
  · exact B324919
  · exact B324923
  · exact B324927
  · exact B324931
  · exact B324935
  · exact B324939
  · exact B324943
  · exact B324947
  · exact B324951
  · exact B324955
  · exact B324959
  · exact B324963
  · exact B324967
  · exact B324971
  · exact B324975
  · exact B324979
  · exact B324983
  · exact B324987
  · exact B324991
  · exact B324995
  · exact B324999
  · exact B325003
  · exact B325007
  · exact B325011
  · exact B325015
  · exact B325019
  · exact B325023
  · exact B325027
  · exact B325031
  · exact B325035
  · exact B325039
  · exact B325043
  · exact B325047
  · exact B325051
  · exact B325055
  · exact B325059
  · exact B325063
  · exact B325067
  · exact B325071
  · exact B325075
  · exact B325079
  · exact B325083
  · exact B325087
  · exact B325091
  · exact B325095
  · exact B325099
  · exact B325103
  · exact B325107
  · exact B325111
  · exact B325115
  · exact B325119
  · exact B325123
  · exact B325127
  · exact B325131
  · exact B325135
  · exact B325139
  · exact B325143
  · exact B325147
  · exact B325151
  · exact B325155
  · exact B325159
  · exact B325163
  · exact B325167
  · exact B325171
  · exact B325175
  · exact B325179
  · exact B325183
  · exact B325187
  · exact B325191
  · exact B325195
  · exact B325199
  · exact B325203
  · exact B325207
  · exact B325211
  · exact B325215
  · exact B325219
  · exact B325223
  · exact B325227
  · exact B325231
  · exact B325235
  · exact B325239
  · exact B325243
  · exact B325247
  · exact B325251
  · exact B325255
  · exact B325259
  · exact B325263
  · exact B325267
  · exact B325271
  · exact B325275
  · exact B325279
  · exact B325283
  · exact B325287
  · exact B325291
  · exact B325295
  · exact B325299
  · exact B325303
  · exact B325307
  · exact B325311
  · exact B325315
  · exact B325319
  · exact B325323
  · exact B325327
  · exact B325331
  · exact B325335
  · exact B325339
  · exact B325343
  · exact B325347
  · exact B325351
  · exact B325355
  · exact B325359
  · exact B325363
  · exact B325367
  · exact B325371
  · exact B325375
  · exact B325379
  · exact B325383
  · exact B325387
  · exact B325391
  · exact B325395
  · exact B325399
  · exact B325403
  · exact B325407
  · exact B325411
  · exact B325415
  · exact B325419
  · exact B325423
  · exact B325427
  · exact B325431
  · exact B325435
  · exact B325439
  · exact B325443
  · exact B325447
  · exact B325451
  · exact B325455
  · exact B325459
  · exact B325463
  · exact B325467
  · exact B325471
  · exact B325475
  · exact B325479
  · exact B325483
  · exact B325487
  · exact B325491
  · exact B325495
  · exact B325499
  · exact B325503
  · exact B325507
  · exact B325511
  · exact B325515
  · exact B325519
  · exact B325523
  · exact B325527
  · exact B325531
  · exact B325535
  · exact B325539
  · exact B325543
  · exact B325547
  · exact B325551
  · exact B325555
  · exact B325559
  · exact B325563
  · exact B325567
  · exact B325571
  · exact B325575
  · exact B325579
  · exact B325583
  · exact B325587
  · exact B325591
  · exact B325595
  · exact B325599
  · exact B325603
  · exact B325607
  · exact B325611
  · exact B325615
  · exact B325619
  · exact B325623
  · exact B325627
  · exact B325631
  · exact B325635
  · exact B325639
  · exact B325643
  · exact B325647
  · exact B325651
  · exact B325655
  · exact B325659
  · exact B325663
  · exact B325667
  · exact B325671
  · exact B325675
  · exact B325679
  · exact B325683
  · exact B325687
  · exact B325691
  · exact B325695
  · exact B325699
  · exact B325703
  · exact B325707
  · exact B325711
  · exact B325715
  · exact B325719
  · exact B325723
  · exact B325727
  · exact B325731
  · exact B325735
  · exact B325739
  · exact B325743
  · exact B325747
  · exact B325751
  · exact B325755
  · exact B325759
  · exact B325763
  · exact B325767
  · exact B325771
  · exact B325775
  · exact B325779
  · exact B325783
  · exact B325787
  · exact B325791
  · exact B325795
  · exact B325799
  · exact B325803
  · exact B325807
  · exact B325811
  · exact B325815
  · exact B325819
  · exact B325823
  · exact B325827
  · exact B325831
  · exact B325835
  · exact B325839
  · exact B325843
  · exact B325847
  · exact B325851
  · exact B325855
  · exact B325859
  · exact B325863
  · exact B325867
  · exact B325871
  · exact B325875
  · exact B325879
  · exact B325883
  · exact B325887
  · exact B325891
  · exact B325895
  · exact B325899
  · exact B325903
  · exact B325907
  · exact B325911
  · exact B325915
  · exact B325919
  · exact B325923
  · exact B325927
  · exact B325931
  · exact B325935
  · exact B325939
  · exact B325943
  · exact B325947
  · exact B325951
  · exact B325955
  · exact B325959
  · exact B325963
  · exact B325967
  · exact B325971
  · exact B325975
  · exact B325979
  · exact B325983
  · exact B325987
  · exact B325991
  · exact B325995
  · exact B325999
  · exact B326003
  · exact B326007
  · exact B326011
  · exact B326015
  · exact B326019
  · exact B326023
  · exact B326027
  · exact B326031
  · exact B326035
  · exact B326039
  · exact B326043
  · exact B326047
  · exact B326051
  · exact B326055
  · exact B326059
  · exact B326063
  · exact B326067
  · exact B326071
  · exact B326075
  · exact B326079
  · exact B326083
  · exact B326087
  · exact B326091
  · exact B326095
  · exact B326099
  · exact B326103
  · exact B326107
  · exact B326111
  · exact B326115
  · exact B326119
  · exact B326123
  · exact B326127
  · exact B326131
  · exact B326135
  · exact B326139
  · exact B326143
  · exact B326147
  · exact B326151
  · exact B326155
  · exact B326159
  · exact B326163
  · exact B326167
  · exact B326171
  · exact B326175
  · exact B326179
  · exact B326183
  · exact B326187
  · exact B326191
  · exact B326195
  · exact B326199
  · exact B326203
  · exact B326207
  · exact B326211
  · exact B326215
  · exact B326219
  · exact B326223
  · exact B326227
  · exact B326231
  · exact B326235
  · exact B326239
  · exact B326243
  · exact B326247
  · exact B326251
  · exact B326255
  · exact B326259
  · exact B326263
  · exact B326267
  · exact B326271
  · exact B326275
  · exact B326279
  · exact B326283
  · exact B326287
  · exact B326291
  · exact B326295
  · exact B326299
  · exact B326303
  · exact B326307
  · exact B326311
  · exact B326315
  · exact B326319
  · exact B326323
  · exact B326327
  · exact B326331
  · exact B326335
  · exact B326339
  · exact B326343
  · exact B326347
  · exact B326351
  · exact B326355
  · exact B326359
  · exact B326363
  · exact B326367
  · exact B326371
  · exact B326375
  · exact B326379
  · exact B326383
  · exact B326387
  · exact B326391
  · exact B326395
  · exact B326399
  · exact B326403
  · exact B326407
  · exact B326411
  · exact B326415
  · exact B326419
  · exact B326423
  · exact B326427
  · exact B326431
  · exact B326435
  · exact B326439
  · exact B326443
  · exact B326447
  · exact B326451
  · exact B326455
  · exact B326459
  · exact B326463
  · exact B326467
  · exact B326471
  · exact B326475
  · exact B326479
  · exact B326483
  · exact B326487
  · exact B326491
  · exact B326495
  · exact B326499
  · exact B326503
  · exact B326507
  · exact B326511
  · exact B326515
  · exact B326519
  · exact B326523
  · exact B326527
  · exact B326531
  · exact B326535
  · exact B326539
  · exact B326543
  · exact B326547
  · exact B326551
  · exact B326555
  · exact B326559
  · exact B326563
  · exact B326567
  · exact B326571
  · exact B326575
  · exact B326579
  · exact B326583
  · exact B326587
  · exact B326591
  · exact B326595
  · exact B326599
  · exact B326603
  · exact B326607
  · exact B326611
  · exact B326615
  · exact B326619
  · exact B326623
  · exact B326627
  · exact B326631
  · exact B326635

theorem C1 (j : ℕ) (h1 : 81659 ≤ j) (h2 : j ≤ 81958) : Blo 323837 (4 * j + 3) := by
  interval_cases j
  · exact B326639
  · exact B326643
  · exact B326647
  · exact B326651
  · exact B326655
  · exact B326659
  · exact B326663
  · exact B326667
  · exact B326671
  · exact B326675
  · exact B326679
  · exact B326683
  · exact B326687
  · exact B326691
  · exact B326695
  · exact B326699
  · exact B326703
  · exact B326707
  · exact B326711
  · exact B326715
  · exact B326719
  · exact B326723
  · exact B326727
  · exact B326731
  · exact B326735
  · exact B326739
  · exact B326743
  · exact B326747
  · exact B326751
  · exact B326755
  · exact B326759
  · exact B326763
  · exact B326767
  · exact B326771
  · exact B326775
  · exact B326779
  · exact B326783
  · exact B326787
  · exact B326791
  · exact B326795
  · exact B326799
  · exact B326803
  · exact B326807
  · exact B326811
  · exact B326815
  · exact B326819
  · exact B326823
  · exact B326827
  · exact B326831
  · exact B326835
  · exact B326839
  · exact B326843
  · exact B326847
  · exact B326851
  · exact B326855
  · exact B326859
  · exact B326863
  · exact B326867
  · exact B326871
  · exact B326875
  · exact B326879
  · exact B326883
  · exact B326887
  · exact B326891
  · exact B326895
  · exact B326899
  · exact B326903
  · exact B326907
  · exact B326911
  · exact B326915
  · exact B326919
  · exact B326923
  · exact B326927
  · exact B326931
  · exact B326935
  · exact B326939
  · exact B326943
  · exact B326947
  · exact B326951
  · exact B326955
  · exact B326959
  · exact B326963
  · exact B326967
  · exact B326971
  · exact B326975
  · exact B326979
  · exact B326983
  · exact B326987
  · exact B326991
  · exact B326995
  · exact B326999
  · exact B327003
  · exact B327007
  · exact B327011
  · exact B327015
  · exact B327019
  · exact B327023
  · exact B327027
  · exact B327031
  · exact B327035
  · exact B327039
  · exact B327043
  · exact B327047
  · exact B327051
  · exact B327055
  · exact B327059
  · exact B327063
  · exact B327067
  · exact B327071
  · exact B327075
  · exact B327079
  · exact B327083
  · exact B327087
  · exact B327091
  · exact B327095
  · exact B327099
  · exact B327103
  · exact B327107
  · exact B327111
  · exact B327115
  · exact B327119
  · exact B327123
  · exact B327127
  · exact B327131
  · exact B327135
  · exact B327139
  · exact B327143
  · exact B327147
  · exact B327151
  · exact B327155
  · exact B327159
  · exact B327163
  · exact B327167
  · exact B327171
  · exact B327175
  · exact B327179
  · exact B327183
  · exact B327187
  · exact B327191
  · exact B327195
  · exact B327199
  · exact B327203
  · exact B327207
  · exact B327211
  · exact B327215
  · exact B327219
  · exact B327223
  · exact B327227
  · exact B327231
  · exact B327235
  · exact B327239
  · exact B327243
  · exact B327247
  · exact B327251
  · exact B327255
  · exact B327259
  · exact B327263
  · exact B327267
  · exact B327271
  · exact B327275
  · exact B327279
  · exact B327283
  · exact B327287
  · exact B327291
  · exact B327295
  · exact B327299
  · exact B327303
  · exact B327307
  · exact B327311
  · exact B327315
  · exact B327319
  · exact B327323
  · exact B327327
  · exact B327331
  · exact B327335
  · exact B327339
  · exact B327343
  · exact B327347
  · exact B327351
  · exact B327355
  · exact B327359
  · exact B327363
  · exact B327367
  · exact B327371
  · exact B327375
  · exact B327379
  · exact B327383
  · exact B327387
  · exact B327391
  · exact B327395
  · exact B327399
  · exact B327403
  · exact B327407
  · exact B327411
  · exact B327415
  · exact B327419
  · exact B327423
  · exact B327427
  · exact B327431
  · exact B327435
  · exact B327439
  · exact B327443
  · exact B327447
  · exact B327451
  · exact B327455
  · exact B327459
  · exact B327463
  · exact B327467
  · exact B327471
  · exact B327475
  · exact B327479
  · exact B327483
  · exact B327487
  · exact B327491
  · exact B327495
  · exact B327499
  · exact B327503
  · exact B327507
  · exact B327511
  · exact B327515
  · exact B327519
  · exact B327523
  · exact B327527
  · exact B327531
  · exact B327535
  · exact B327539
  · exact B327543
  · exact B327547
  · exact B327551
  · exact B327555
  · exact B327559
  · exact B327563
  · exact B327567
  · exact B327571
  · exact B327575
  · exact B327579
  · exact B327583
  · exact B327587
  · exact B327591
  · exact B327595
  · exact B327599
  · exact B327603
  · exact B327607
  · exact B327611
  · exact B327615
  · exact B327619
  · exact B327623
  · exact B327627
  · exact B327631
  · exact B327635
  · exact B327639
  · exact B327643
  · exact B327647
  · exact B327651
  · exact B327655
  · exact B327659
  · exact B327663
  · exact B327667
  · exact B327671
  · exact B327675
  · exact B327679
  · exact B327683
  · exact B327687
  · exact B327691
  · exact B327695
  · exact B327699
  · exact B327703
  · exact B327707
  · exact B327711
  · exact B327715
  · exact B327719
  · exact B327723
  · exact B327727
  · exact B327731
  · exact B327735
  · exact B327739
  · exact B327743
  · exact B327747
  · exact B327751
  · exact B327755
  · exact B327759
  · exact B327763
  · exact B327767
  · exact B327771
  · exact B327775
  · exact B327779
  · exact B327783
  · exact B327787
  · exact B327791
  · exact B327795
  · exact B327799
  · exact B327803
  · exact B327807
  · exact B327811
  · exact B327815
  · exact B327819
  · exact B327823
  · exact B327827
  · exact B327831
  · exact B327835

theorem solution (m : ℕ) (hlo : 323837 ≤ m) (hhi : m ≤ 327837) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 80959 ≤ j := by omega
    have hj2 : j ≤ 81958 := by omega
    have hb : Blo 323837 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 81659 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
