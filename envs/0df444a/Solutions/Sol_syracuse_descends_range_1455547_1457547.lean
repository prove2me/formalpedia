-- Prove2me | solution 1 for syracuse_descends_range_1455547_1457547
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:43:52.257141+00:00
-- url     : https://prove2.me/submissions/a427e818-7af0-4ed6-a846-18725cfd0595

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


theorem B1638409 : Blo 1455547 1638409 := bbase (se 2 (by rfl) ⟨614403, by rfl⟩ : syracuseStep 1638409 = 1228807) (by norm_num)
theorem B3276845 : Blo 1455547 3276845 := bbase (se 3 (by rfl) ⟨614408, by rfl⟩ : syracuseStep 3276845 = 1228817) (by norm_num)
theorem B1638445 : Blo 1455547 1638445 := bbase (se 3 (by rfl) ⟨307208, by rfl⟩ : syracuseStep 1638445 = 614417) (by norm_num)
theorem B3547189 : Blo 1455547 3547189 := bbase (se 5 (by rfl) ⟨166274, by rfl⟩ : syracuseStep 3547189 = 332549) (by norm_num)
theorem B2457661 : Blo 1455547 2457661 := bbase (se 3 (by rfl) ⟨460811, by rfl⟩ : syracuseStep 2457661 = 921623) (by norm_num)
theorem B1638481 : Blo 1455547 1638481 := bbase (se 2 (by rfl) ⟨614430, by rfl⟩ : syracuseStep 1638481 = 1228861) (by norm_num)
theorem B3276917 : Blo 1455547 3276917 := bbase (se 5 (by rfl) ⟨153605, by rfl⟩ : syracuseStep 3276917 = 307211) (by norm_num)
theorem B1638517 : Blo 1455547 1638517 := bbase (se 5 (by rfl) ⟨76805, by rfl⟩ : syracuseStep 1638517 = 153611) (by norm_num)
theorem B1843337 : Blo 1455547 1843337 := bbase (se 2 (by rfl) ⟨691251, by rfl⟩ : syracuseStep 1843337 = 1382503) (by norm_num)
theorem B4915349 : Blo 1455547 4915349 := bbase (se 6 (by rfl) ⟨115203, by rfl⟩ : syracuseStep 4915349 = 230407) (by norm_num)
theorem B2457749 : Blo 1455547 2457749 := bbase (se 6 (by rfl) ⟨57603, by rfl⟩ : syracuseStep 2457749 = 115207) (by norm_num)
theorem B1638553 : Blo 1455547 1638553 := bbase (se 2 (by rfl) ⟨614457, by rfl⟩ : syracuseStep 1638553 = 1228915) (by norm_num)
theorem B3686573 : Blo 1455547 3686573 := bbase (se 3 (by rfl) ⟨691232, by rfl⟩ : syracuseStep 3686573 = 1382465) (by norm_num)
theorem B3276989 : Blo 1455547 3276989 := bbase (se 3 (by rfl) ⟨614435, by rfl⟩ : syracuseStep 3276989 = 1228871) (by norm_num)
theorem B1638589 : Blo 1455547 1638589 := bbase (se 3 (by rfl) ⟨307235, by rfl⟩ : syracuseStep 1638589 = 614471) (by norm_num)
theorem B1843393 : Blo 1455547 1843393 := bbase (se 2 (by rfl) ⟨691272, by rfl⟩ : syracuseStep 1843393 = 1382545) (by norm_num)
theorem B3367133 : Blo 1455547 3367133 := bbase (se 3 (by rfl) ⟨631337, by rfl⟩ : syracuseStep 3367133 = 1262675) (by norm_num)
theorem B1638625 : Blo 1455547 1638625 := bbase (se 2 (by rfl) ⟨614484, by rfl⟩ : syracuseStep 1638625 = 1228969) (by norm_num)
theorem B5529829 : Blo 1455547 5529829 := bbase (se 4 (by rfl) ⟨518421, by rfl⟩ : syracuseStep 5529829 = 1036843) (by norm_num)
theorem B4145413 : Blo 1455547 4145413 := bbase (se 4 (by rfl) ⟨388632, by rfl⟩ : syracuseStep 4145413 = 777265) (by norm_num)
theorem B3277061 : Blo 1455547 3277061 := bbase (se 4 (by rfl) ⟨307224, by rfl⟩ : syracuseStep 3277061 = 614449) (by norm_num)
theorem B1638661 : Blo 1455547 1638661 := bbase (se 4 (by rfl) ⟨153624, by rfl⟩ : syracuseStep 1638661 = 307249) (by norm_num)
theorem B2457877 : Blo 1455547 2457877 := bbase (se 6 (by rfl) ⟨57606, by rfl⟩ : syracuseStep 2457877 = 115213) (by norm_num)
theorem B1843489 : Blo 1455547 1843489 := bbase (se 2 (by rfl) ⟨691308, by rfl⟩ : syracuseStep 1843489 = 1382617) (by norm_num)
theorem B1638697 : Blo 1455547 1638697 := bbase (se 2 (by rfl) ⟨614511, by rfl⟩ : syracuseStep 1638697 = 1229023) (by norm_num)
theorem B3277133 : Blo 1455547 3277133 := bbase (se 3 (by rfl) ⟨614462, by rfl⟩ : syracuseStep 3277133 = 1228925) (by norm_num)
theorem B1638733 : Blo 1455547 1638733 := bbase (se 3 (by rfl) ⟨307262, by rfl⟩ : syracuseStep 1638733 = 614525) (by norm_num)
theorem B2457965 : Blo 1455547 2457965 := bbase (se 3 (by rfl) ⟨460868, by rfl⟩ : syracuseStep 2457965 = 921737) (by norm_num)
theorem B1638769 : Blo 1455547 1638769 := bbase (se 2 (by rfl) ⟨614538, by rfl⟩ : syracuseStep 1638769 = 1229077) (by norm_num)
theorem B2072957 : Blo 1455547 2072957 := bbase (se 3 (by rfl) ⟨388679, by rfl⟩ : syracuseStep 2072957 = 777359) (by norm_num)
theorem B3277205 : Blo 1455547 3277205 := bbase (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) (by norm_num)
theorem B1638805 : Blo 1455547 1638805 := bbase (se 6 (by rfl) ⟨38409, by rfl⟩ : syracuseStep 1638805 = 76819) (by norm_num)
theorem B4145573 : Blo 1455547 4145573 := bbase (se 4 (by rfl) ⟨388647, by rfl⟩ : syracuseStep 4145573 = 777295) (by norm_num)
theorem B2490797 : Blo 1455547 2490797 := bbase (se 3 (by rfl) ⟨467024, by rfl⟩ : syracuseStep 2490797 = 934049) (by norm_num)
theorem B1638841 : Blo 1455547 1638841 := bbase (se 2 (by rfl) ⟨614565, by rfl⟩ : syracuseStep 1638841 = 1229131) (by norm_num)
theorem B1843661 : Blo 1455547 1843661 := bbase (se 3 (by rfl) ⟨345686, by rfl⟩ : syracuseStep 1843661 = 691373) (by norm_num)
theorem B3277277 : Blo 1455547 3277277 := bbase (se 3 (by rfl) ⟨614489, by rfl⟩ : syracuseStep 3277277 = 1228979) (by norm_num)
theorem B1638877 : Blo 1455547 1638877 := bbase (se 3 (by rfl) ⟨307289, by rfl⟩ : syracuseStep 1638877 = 614579) (by norm_num)
theorem B2458093 : Blo 1455547 2458093 := bbase (se 3 (by rfl) ⟨460892, by rfl⟩ : syracuseStep 2458093 = 921785) (by norm_num)
theorem B1638913 : Blo 1455547 1638913 := bbase (se 2 (by rfl) ⟨614592, by rfl⟩ : syracuseStep 1638913 = 1229185) (by norm_num)
theorem B3686917 : Blo 1455547 3686917 := bbase (se 4 (by rfl) ⟨345648, by rfl⟩ : syracuseStep 3686917 = 691297) (by norm_num)
theorem B1843717 : Blo 1455547 1843717 := bbase (se 4 (by rfl) ⟨172848, by rfl⟩ : syracuseStep 1843717 = 345697) (by norm_num)
theorem B5530133 : Blo 1455547 5530133 := bbase (se 6 (by rfl) ⟨129612, by rfl⟩ : syracuseStep 5530133 = 259225) (by norm_num)
theorem B3277349 : Blo 1455547 3277349 := bbase (se 4 (by rfl) ⟨307251, by rfl⟩ : syracuseStep 3277349 = 614503) (by norm_num)
theorem B1638949 : Blo 1455547 1638949 := bbase (se 4 (by rfl) ⟨153651, by rfl⟩ : syracuseStep 1638949 = 307303) (by norm_num)
theorem B6218309 : Blo 1455547 6218309 := bbase (se 4 (by rfl) ⟨582966, by rfl⟩ : syracuseStep 6218309 = 1165933) (by norm_num)
theorem B4915781 : Blo 1455547 4915781 := bbase (se 4 (by rfl) ⟨460854, by rfl⟩ : syracuseStep 4915781 = 921709) (by norm_num)
theorem B2458181 : Blo 1455547 2458181 := bbase (se 4 (by rfl) ⟨230454, by rfl⟩ : syracuseStep 2458181 = 460909) (by norm_num)
theorem B1638985 : Blo 1455547 1638985 := bbase (se 2 (by rfl) ⟨614619, by rfl⟩ : syracuseStep 1638985 = 1229239) (by norm_num)
theorem B1843813 : Blo 1455547 1843813 := bbase (se 4 (by rfl) ⟨172857, by rfl⟩ : syracuseStep 1843813 = 345715) (by norm_num)
theorem B3277421 : Blo 1455547 3277421 := bbase (se 3 (by rfl) ⟨614516, by rfl⟩ : syracuseStep 3277421 = 1229033) (by norm_num)
theorem B1639021 : Blo 1455547 1639021 := bbase (se 3 (by rfl) ⟨307316, by rfl⟩ : syracuseStep 1639021 = 614633) (by norm_num)
theorem B7373429 : Blo 1455547 7373429 := bbase (se 5 (by rfl) ⟨345629, by rfl⟩ : syracuseStep 7373429 = 691259) (by norm_num)
theorem B3687029 : Blo 1455547 3687029 := bbase (se 5 (by rfl) ⟨172829, by rfl⟩ : syracuseStep 3687029 = 345659) (by norm_num)
theorem B1639057 : Blo 1455547 1639057 := bbase (se 2 (by rfl) ⟨614646, by rfl⟩ : syracuseStep 1639057 = 1229293) (by norm_num)
theorem B4145813 : Blo 1455547 4145813 := bbase (se 6 (by rfl) ⟨97167, by rfl⟩ : syracuseStep 4145813 = 194335) (by norm_num)
theorem B3277493 : Blo 1455547 3277493 := bbase (se 5 (by rfl) ⟨153632, by rfl⟩ : syracuseStep 3277493 = 307265) (by norm_num)
theorem B1639093 : Blo 1455547 1639093 := bbase (se 5 (by rfl) ⟨76832, by rfl⟩ : syracuseStep 1639093 = 153665) (by norm_num)
theorem B2458309 : Blo 1455547 2458309 := bbase (se 4 (by rfl) ⟨230466, by rfl⟩ : syracuseStep 2458309 = 460933) (by norm_num)
theorem B1639129 : Blo 1455547 1639129 := bbase (se 2 (by rfl) ⟨614673, by rfl⟩ : syracuseStep 1639129 = 1229347) (by norm_num)
theorem B3277565 : Blo 1455547 3277565 := bbase (se 3 (by rfl) ⟨614543, by rfl⟩ : syracuseStep 3277565 = 1229087) (by norm_num)
theorem B1639165 : Blo 1455547 1639165 := bbase (se 3 (by rfl) ⟨307343, by rfl⟩ : syracuseStep 1639165 = 614687) (by norm_num)
theorem B1843985 : Blo 1455547 1843985 := bbase (se 2 (by rfl) ⟨691494, by rfl⟩ : syracuseStep 1843985 = 1382989) (by norm_num)
theorem B2458397 : Blo 1455547 2458397 := bbase (se 3 (by rfl) ⟨460949, by rfl⟩ : syracuseStep 2458397 = 921899) (by norm_num)
theorem B1639201 : Blo 1455547 1639201 := bbase (se 2 (by rfl) ⟨614700, by rfl⟩ : syracuseStep 1639201 = 1229401) (by norm_num)
theorem B3687221 : Blo 1455547 3687221 := bbase (se 5 (by rfl) ⟨172838, by rfl⟩ : syracuseStep 3687221 = 345677) (by norm_num)
theorem B3277637 : Blo 1455547 3277637 := bbase (se 4 (by rfl) ⟨307278, by rfl⟩ : syracuseStep 3277637 = 614557) (by norm_num)
theorem B1639237 : Blo 1455547 1639237 := bbase (se 4 (by rfl) ⟨153678, by rfl⟩ : syracuseStep 1639237 = 307357) (by norm_num)
theorem B1844041 : Blo 1455547 1844041 := bbase (se 2 (by rfl) ⟨691515, by rfl⟩ : syracuseStep 1844041 = 1383031) (by norm_num)
theorem B4146005 : Blo 1455547 4146005 := bbase (se 9 (by rfl) ⟨12146, by rfl⟩ : syracuseStep 4146005 = 24293) (by norm_num)
theorem B2491229 : Blo 1455547 2491229 := bbase (se 3 (by rfl) ⟨467105, by rfl⟩ : syracuseStep 2491229 = 934211) (by norm_num)
theorem B1639273 : Blo 1455547 1639273 := bbase (se 2 (by rfl) ⟨614727, by rfl⟩ : syracuseStep 1639273 = 1229455) (by norm_num)
theorem B3154805 : Blo 1455547 3154805 := bbase (se 5 (by rfl) ⟨147881, by rfl⟩ : syracuseStep 3154805 = 295763) (by norm_num)
theorem B3277709 : Blo 1455547 3277709 := bbase (se 3 (by rfl) ⟨614570, by rfl⟩ : syracuseStep 3277709 = 1229141) (by norm_num)
theorem B1639309 : Blo 1455547 1639309 := bbase (se 3 (by rfl) ⟨307370, by rfl⟩ : syracuseStep 1639309 = 614741) (by norm_num)
theorem B2458525 : Blo 1455547 2458525 := bbase (se 3 (by rfl) ⟨460973, by rfl⟩ : syracuseStep 2458525 = 921947) (by norm_num)
theorem B1844137 : Blo 1455547 1844137 := bbase (se 2 (by rfl) ⟨691551, by rfl⟩ : syracuseStep 1844137 = 1383103) (by norm_num)
theorem B1639345 : Blo 1455547 1639345 := bbase (se 2 (by rfl) ⟨614754, by rfl⟩ : syracuseStep 1639345 = 1229509) (by norm_num)
theorem B3277781 : Blo 1455547 3277781 := bbase (se 7 (by rfl) ⟨38411, by rfl⟩ : syracuseStep 3277781 = 76823) (by norm_num)
theorem B1639381 : Blo 1455547 1639381 := bbase (se 7 (by rfl) ⟨19211, by rfl⟩ : syracuseStep 1639381 = 38423) (by norm_num)
theorem B7095269 : Blo 1455547 7095269 := bbase (se 4 (by rfl) ⟨665181, by rfl⟩ : syracuseStep 7095269 = 1330363) (by norm_num)
theorem B4916213 : Blo 1455547 4916213 := bbase (se 5 (by rfl) ⟨230447, by rfl⟩ : syracuseStep 4916213 = 460895) (by norm_num)
theorem B2458613 : Blo 1455547 2458613 := bbase (se 5 (by rfl) ⟨115247, by rfl⟩ : syracuseStep 2458613 = 230495) (by norm_num)
theorem B1639417 : Blo 1455547 1639417 := bbase (se 2 (by rfl) ⟨614781, by rfl⟩ : syracuseStep 1639417 = 1229563) (by norm_num)
theorem B2802701 : Blo 1455547 2802701 := bbase (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) (by norm_num)
theorem B3277853 : Blo 1455547 3277853 := bbase (se 3 (by rfl) ⟨614597, by rfl⟩ : syracuseStep 3277853 = 1229195) (by norm_num)
theorem B1639453 : Blo 1455547 1639453 := bbase (se 3 (by rfl) ⟨307397, by rfl⟩ : syracuseStep 1639453 = 614795) (by norm_num)
theorem B1639489 : Blo 1455547 1639489 := bbase (se 2 (by rfl) ⟨614808, by rfl⟩ : syracuseStep 1639489 = 1229617) (by norm_num)
theorem B1844309 : Blo 1455547 1844309 := bbase (se 8 (by rfl) ⟨10806, by rfl⟩ : syracuseStep 1844309 = 21613) (by norm_num)
theorem B3277925 : Blo 1455547 3277925 := bbase (se 4 (by rfl) ⟨307305, by rfl⟩ : syracuseStep 3277925 = 614611) (by norm_num)
theorem B1639525 : Blo 1455547 1639525 := bbase (se 4 (by rfl) ⟨153705, by rfl⟩ : syracuseStep 1639525 = 307411) (by norm_num)
theorem B2073709 : Blo 1455547 2073709 := bbase (se 3 (by rfl) ⟨388820, by rfl⟩ : syracuseStep 2073709 = 777641) (by norm_num)
theorem B2458741 : Blo 1455547 2458741 := bbase (se 5 (by rfl) ⟨115253, by rfl⟩ : syracuseStep 2458741 = 230507) (by norm_num)
theorem B1639561 : Blo 1455547 1639561 := bbase (se 2 (by rfl) ⟨614835, by rfl⟩ : syracuseStep 1639561 = 1229671) (by norm_num)
theorem B3687565 : Blo 1455547 3687565 := bbase (se 3 (by rfl) ⟨691418, by rfl⟩ : syracuseStep 3687565 = 1382837) (by norm_num)
theorem B1844365 : Blo 1455547 1844365 := bbase (se 3 (by rfl) ⟨345818, by rfl⟩ : syracuseStep 1844365 = 691637) (by norm_num)
theorem B3277997 : Blo 1455547 3277997 := bbase (se 3 (by rfl) ⟨614624, by rfl⟩ : syracuseStep 3277997 = 1229249) (by norm_num)
theorem B1639597 : Blo 1455547 1639597 := bbase (se 3 (by rfl) ⟨307424, by rfl⟩ : syracuseStep 1639597 = 614849) (by norm_num)
theorem B2458829 : Blo 1455547 2458829 := bbase (se 3 (by rfl) ⟨461030, by rfl⟩ : syracuseStep 2458829 = 922061) (by norm_num)
theorem B1639633 : Blo 1455547 1639633 := bbase (se 2 (by rfl) ⟨614862, by rfl⟩ : syracuseStep 1639633 = 1229725) (by norm_num)
theorem B1844461 : Blo 1455547 1844461 := bbase (se 3 (by rfl) ⟨345836, by rfl⟩ : syracuseStep 1844461 = 691673) (by norm_num)
theorem B3278069 : Blo 1455547 3278069 := bbase (se 5 (by rfl) ⟨153659, by rfl⟩ : syracuseStep 3278069 = 307319) (by norm_num)
theorem B1639669 : Blo 1455547 1639669 := bbase (se 5 (by rfl) ⟨76859, by rfl⟩ : syracuseStep 1639669 = 153719) (by norm_num)
theorem B3687677 : Blo 1455547 3687677 := bbase (se 3 (by rfl) ⟨691439, by rfl⟩ : syracuseStep 3687677 = 1382879) (by norm_num)
theorem B1639705 : Blo 1455547 1639705 := bbase (se 2 (by rfl) ⟨614889, by rfl⟩ : syracuseStep 1639705 = 1229779) (by norm_num)
theorem B3278141 : Blo 1455547 3278141 := bbase (se 3 (by rfl) ⟨614651, by rfl⟩ : syracuseStep 3278141 = 1229303) (by norm_num)
theorem B1639741 : Blo 1455547 1639741 := bbase (se 3 (by rfl) ⟨307451, by rfl⟩ : syracuseStep 1639741 = 614903) (by norm_num)
theorem B2458957 : Blo 1455547 2458957 := bbase (se 3 (by rfl) ⟨461054, by rfl⟩ : syracuseStep 2458957 = 922109) (by norm_num)
theorem B3278213 : Blo 1455547 3278213 := bbase (se 4 (by rfl) ⟨307332, by rfl⟩ : syracuseStep 3278213 = 614665) (by norm_num)
theorem B1844633 : Blo 1455547 1844633 := bbase (se 2 (by rfl) ⟨691737, by rfl⟩ : syracuseStep 1844633 = 1383475) (by norm_num)
theorem B4916645 : Blo 1455547 4916645 := bbase (se 4 (by rfl) ⟨460935, by rfl⟩ : syracuseStep 4916645 = 921871) (by norm_num)
theorem B2459045 : Blo 1455547 2459045 := bbase (se 4 (by rfl) ⟨230535, by rfl⟩ : syracuseStep 2459045 = 461071) (by norm_num)
theorem B3687869 : Blo 1455547 3687869 := bbase (se 3 (by rfl) ⟨691475, by rfl⟩ : syracuseStep 3687869 = 1382951) (by norm_num)
theorem B3278285 : Blo 1455547 3278285 := bbase (se 3 (by rfl) ⟨614678, by rfl⟩ : syracuseStep 3278285 = 1229357) (by norm_num)
theorem B1844689 : Blo 1455547 1844689 := bbase (se 2 (by rfl) ⟨691758, by rfl⟩ : syracuseStep 1844689 = 1383517) (by norm_num)
theorem B3278357 : Blo 1455547 3278357 := bbase (se 6 (by rfl) ⟨76836, by rfl⟩ : syracuseStep 3278357 = 153673) (by norm_num)
theorem B2459173 : Blo 1455547 2459173 := bbase (se 4 (by rfl) ⟨230547, by rfl⟩ : syracuseStep 2459173 = 461095) (by norm_num)
theorem B3278429 : Blo 1455547 3278429 := bbase (se 3 (by rfl) ⟨614705, by rfl⟩ : syracuseStep 3278429 = 1229411) (by norm_num)
theorem B3499645 : Blo 1455547 3499645 := bbase (se 3 (by rfl) ⟨656183, by rfl⟩ : syracuseStep 3499645 = 1312367) (by norm_num)
theorem B2459261 : Blo 1455547 2459261 := bbase (se 3 (by rfl) ⟨461111, by rfl⟩ : syracuseStep 2459261 = 922223) (by norm_num)
theorem B3278501 : Blo 1455547 3278501 := bbase (se 4 (by rfl) ⟨307359, by rfl⟩ : syracuseStep 3278501 = 614719) (by norm_num)
theorem B12445397 : Blo 1455547 12445397 := bbase (se 7 (by rfl) ⟨145844, by rfl⟩ : syracuseStep 12445397 = 291689) (by norm_num)
theorem B3278573 : Blo 1455547 3278573 := bbase (se 3 (by rfl) ⟨614732, by rfl⟩ : syracuseStep 3278573 = 1229465) (by norm_num)
theorem B2459389 : Blo 1455547 2459389 := bbase (se 3 (by rfl) ⟨461135, by rfl⟩ : syracuseStep 2459389 = 922271) (by norm_num)
theorem B5605141 : Blo 1455547 5605141 := bbase (se 6 (by rfl) ⟨131370, by rfl⟩ : syracuseStep 5605141 = 262741) (by norm_num)
theorem B3688213 : Blo 1455547 3688213 := bbase (se 6 (by rfl) ⟨86442, by rfl⟩ : syracuseStep 3688213 = 172885) (by norm_num)
theorem B5908261 : Blo 1455547 5908261 := bbase (se 4 (by rfl) ⟨553899, by rfl⟩ : syracuseStep 5908261 = 1107799) (by norm_num)
theorem B4146997 : Blo 1455547 4146997 := bbase (se 5 (by rfl) ⟨194390, by rfl⟩ : syracuseStep 4146997 = 388781) (by norm_num)
theorem B3278645 : Blo 1455547 3278645 := bbase (se 5 (by rfl) ⟨153686, by rfl⟩ : syracuseStep 3278645 = 307373) (by norm_num)
theorem B12437333 : Blo 1455547 12437333 := bbase (se 9 (by rfl) ⟨36437, by rfl⟩ : syracuseStep 12437333 = 72875) (by norm_num)
theorem B4917077 : Blo 1455547 4917077 := bbase (se 9 (by rfl) ⟨14405, by rfl⟩ : syracuseStep 4917077 = 28811) (by norm_num)
theorem B2459477 : Blo 1455547 2459477 := bbase (se 9 (by rfl) ⟨7205, by rfl⟩ : syracuseStep 2459477 = 14411) (by norm_num)
theorem B1967989 : Blo 1455547 1967989 := bbase (se 5 (by rfl) ⟨92249, by rfl⟩ : syracuseStep 1967989 = 184499) (by norm_num)
theorem B3278717 : Blo 1455547 3278717 := bbase (se 3 (by rfl) ⟨614759, by rfl⟩ : syracuseStep 3278717 = 1229519) (by norm_num)
theorem B7374725 : Blo 1455547 7374725 := bbase (se 4 (by rfl) ⟨691380, by rfl⟩ : syracuseStep 7374725 = 1382761) (by norm_num)
theorem B2074501 : Blo 1455547 2074501 := bbase (se 4 (by rfl) ⟨194484, by rfl⟩ : syracuseStep 2074501 = 388969) (by norm_num)
theorem B3688325 : Blo 1455547 3688325 := bbase (se 4 (by rfl) ⟨345780, by rfl⟩ : syracuseStep 3688325 = 691561) (by norm_num)
theorem B8857525 : Blo 1455547 8857525 := bbase (se 5 (by rfl) ⟨415196, by rfl⟩ : syracuseStep 8857525 = 830393) (by norm_num)
theorem B3278789 : Blo 1455547 3278789 := bbase (se 4 (by rfl) ⟨307386, by rfl⟩ : syracuseStep 3278789 = 614773) (by norm_num)
theorem B2459605 : Blo 1455547 2459605 := bbase (se 7 (by rfl) ⟨28823, by rfl⟩ : syracuseStep 2459605 = 57647) (by norm_num)
theorem B3278861 : Blo 1455547 3278861 := bbase (se 3 (by rfl) ⟨614786, by rfl⟩ : syracuseStep 3278861 = 1229573) (by norm_num)
theorem B3688517 : Blo 1455547 3688517 := bbase (se 4 (by rfl) ⟨345798, by rfl⟩ : syracuseStep 3688517 = 691597) (by norm_num)
theorem B3278933 : Blo 1455547 3278933 := bbase (se 8 (by rfl) ⟨19212, by rfl⟩ : syracuseStep 3278933 = 38425) (by norm_num)
theorem B1476725 : Blo 1455547 1476725 := bbase (se 5 (by rfl) ⟨69221, by rfl⟩ : syracuseStep 1476725 = 138443) (by norm_num)
theorem B1476757 : Blo 1455547 1476757 := bbase (se 6 (by rfl) ⟨34611, by rfl⟩ : syracuseStep 1476757 = 69223) (by norm_num)
theorem B3279005 : Blo 1455547 3279005 := bbase (se 3 (by rfl) ⟨614813, by rfl⟩ : syracuseStep 3279005 = 1229627) (by norm_num)
theorem B2074837 : Blo 1455547 2074837 := bbase (se 7 (by rfl) ⟨24314, by rfl⟩ : syracuseStep 2074837 = 48629) (by norm_num)
theorem B3279077 : Blo 1455547 3279077 := bbase (se 4 (by rfl) ⟨307413, by rfl⟩ : syracuseStep 3279077 = 614827) (by norm_num)
theorem B4917509 : Blo 1455547 4917509 := bbase (se 4 (by rfl) ⟨461016, by rfl⟩ : syracuseStep 4917509 = 922033) (by norm_num)
theorem B6998309 : Blo 1455547 6998309 := bbase (se 4 (by rfl) ⟨656091, by rfl⟩ : syracuseStep 6998309 = 1312183) (by norm_num)
theorem B3279149 : Blo 1455547 3279149 := bbase (se 3 (by rfl) ⟨614840, by rfl⟩ : syracuseStep 3279149 = 1229681) (by norm_num)
theorem B4983125 : Blo 1455547 4983125 := bbase (se 10 (by rfl) ⟨7299, by rfl⟩ : syracuseStep 4983125 = 14599) (by norm_num)
theorem B3279221 : Blo 1455547 3279221 := bbase (se 5 (by rfl) ⟨153713, by rfl⟩ : syracuseStep 3279221 = 307427) (by norm_num)
theorem B1477001 : Blo 1455547 1477001 := bbase (se 2 (by rfl) ⟨553875, by rfl⟩ : syracuseStep 1477001 = 1107751) (by norm_num)
theorem B3688861 : Blo 1455547 3688861 := bbase (se 3 (by rfl) ⟨691661, by rfl⟩ : syracuseStep 3688861 = 1383323) (by norm_num)
theorem B2075053 : Blo 1455547 2075053 := bbase (se 3 (by rfl) ⟨389072, by rfl⟩ : syracuseStep 2075053 = 778145) (by norm_num)
theorem B3279293 : Blo 1455547 3279293 := bbase (se 3 (by rfl) ⟨614867, by rfl⟩ : syracuseStep 3279293 = 1229735) (by norm_num)
theorem B3279365 : Blo 1455547 3279365 := bbase (se 4 (by rfl) ⟨307440, by rfl⟩ : syracuseStep 3279365 = 614881) (by norm_num)
theorem B3688973 : Blo 1455547 3688973 := bbase (se 3 (by rfl) ⟨691682, by rfl⟩ : syracuseStep 3688973 = 1383365) (by norm_num)
theorem B3279437 : Blo 1455547 3279437 := bbase (se 3 (by rfl) ⟨614894, by rfl⟩ : syracuseStep 3279437 = 1229789) (by norm_num)
theorem B3320405 : Blo 1455547 3320405 := bbase (se 8 (by rfl) ⟨19455, by rfl⟩ : syracuseStep 3320405 = 38911) (by norm_num)
theorem B11061845 : Blo 1455547 11061845 := bbase (se 8 (by rfl) ⟨64815, by rfl⟩ : syracuseStep 11061845 = 129631) (by norm_num)
theorem B5532245 : Blo 1455547 5532245 := bbase (se 8 (by rfl) ⟨32415, by rfl⟩ : syracuseStep 5532245 = 64831) (by norm_num)
theorem B3500653 : Blo 1455547 3500653 := bbase (se 3 (by rfl) ⟨656372, by rfl⟩ : syracuseStep 3500653 = 1312745) (by norm_num)
theorem B2763389 : Blo 1455547 2763389 := bbase (se 3 (by rfl) ⟨518135, by rfl⟩ : syracuseStep 2763389 = 1036271) (by norm_num)
theorem B8293013 : Blo 1455547 8293013 := bbase (se 6 (by rfl) ⟨194367, by rfl⟩ : syracuseStep 8293013 = 388735) (by norm_num)
theorem B1477289 : Blo 1455547 1477289 := bbase (se 2 (by rfl) ⟨553983, by rfl⟩ : syracuseStep 1477289 = 1107967) (by norm_num)
theorem B4917941 : Blo 1455547 4917941 := bbase (se 5 (by rfl) ⟨230528, by rfl⟩ : syracuseStep 4917941 = 461057) (by norm_num)
theorem B2493109 : Blo 1455547 2493109 := bbase (se 5 (by rfl) ⟨116864, by rfl⟩ : syracuseStep 2493109 = 233729) (by norm_num)
theorem B3500749 : Blo 1455547 3500749 := bbase (se 3 (by rfl) ⟨656390, by rfl⟩ : syracuseStep 3500749 = 1312781) (by norm_num)
theorem B3689165 : Blo 1455547 3689165 := bbase (se 3 (by rfl) ⟨691718, by rfl⟩ : syracuseStep 3689165 = 1383437) (by norm_num)
theorem B2624221 : Blo 1455547 2624221 := bbase (se 3 (by rfl) ⟨492041, by rfl⟩ : syracuseStep 2624221 = 984083) (by norm_num)
theorem B2763533 : Blo 1455547 2763533 := bbase (se 3 (by rfl) ⟨518162, by rfl⟩ : syracuseStep 2763533 = 1036325) (by norm_num)
theorem B5532533 : Blo 1455547 5532533 := bbase (se 5 (by rfl) ⟨259337, by rfl⟩ : syracuseStep 5532533 = 518675) (by norm_num)
theorem B5909365 : Blo 1455547 5909365 := bbase (se 5 (by rfl) ⟨277001, by rfl⟩ : syracuseStep 5909365 = 554003) (by norm_num)
theorem B4148101 : Blo 1455547 4148101 := bbase (se 4 (by rfl) ⟨388884, by rfl⟩ : syracuseStep 4148101 = 777769) (by norm_num)
theorem B5909429 : Blo 1455547 5909429 := bbase (se 5 (by rfl) ⟨277004, by rfl⟩ : syracuseStep 5909429 = 554009) (by norm_num)
theorem B3787709 : Blo 1455547 3787709 := bbase (se 3 (by rfl) ⟨710195, by rfl⟩ : syracuseStep 3787709 = 1420391) (by norm_num)
theorem B11054069 : Blo 1455547 11054069 := bbase (se 5 (by rfl) ⟨518159, by rfl⟩ : syracuseStep 11054069 = 1036319) (by norm_num)
theorem B2763821 : Blo 1455547 2763821 := bbase (se 3 (by rfl) ⟨518216, by rfl⟩ : syracuseStep 2763821 = 1036433) (by norm_num)
theorem B5246021 : Blo 1455547 5246021 := bbase (se 4 (by rfl) ⟨491814, by rfl⟩ : syracuseStep 5246021 = 983629) (by norm_num)
theorem B4983893 : Blo 1455547 4983893 := bbase (se 8 (by rfl) ⟨29202, by rfl⟩ : syracuseStep 4983893 = 58405) (by norm_num)
theorem B4918373 : Blo 1455547 4918373 := bbase (se 4 (by rfl) ⟨461097, by rfl⟩ : syracuseStep 4918373 = 922195) (by norm_num)
theorem B7376021 : Blo 1455547 7376021 := bbase (se 6 (by rfl) ⟨172875, by rfl⟩ : syracuseStep 7376021 = 345751) (by norm_num)
theorem B2763973 : Blo 1455547 2763973 := bbase (se 4 (by rfl) ⟨259122, by rfl⟩ : syracuseStep 2763973 = 518245) (by norm_num)
theorem B3501269 : Blo 1455547 3501269 := bbase (se 7 (by rfl) ⟨41030, by rfl⟩ : syracuseStep 3501269 = 82061) (by norm_num)
theorem B1969373 : Blo 1455547 1969373 := bbase (se 3 (by rfl) ⟨369257, by rfl⟩ : syracuseStep 1969373 = 738515) (by norm_num)
theorem B2952445 : Blo 1455547 2952445 := bbase (se 3 (by rfl) ⟨553583, by rfl⟩ : syracuseStep 2952445 = 1107167) (by norm_num)
theorem B5606741 : Blo 1455547 5606741 := bbase (se 11 (by rfl) ⟨4106, by rfl⟩ : syracuseStep 5606741 = 8213) (by norm_num)
theorem B5246309 : Blo 1455547 5246309 := bbase (se 4 (by rfl) ⟨491841, by rfl⟩ : syracuseStep 5246309 = 983683) (by norm_num)
theorem B3321245 : Blo 1455547 3321245 := bbase (se 3 (by rfl) ⟨622733, by rfl⟩ : syracuseStep 3321245 = 1245467) (by norm_num)
theorem B5320165 : Blo 1455547 5320165 := bbase (se 4 (by rfl) ⟨498765, by rfl⟩ : syracuseStep 5320165 = 997531) (by norm_num)
theorem B2764277 : Blo 1455547 2764277 := bbase (se 5 (by rfl) ⟨129575, by rfl⟩ : syracuseStep 2764277 = 259151) (by norm_num)
theorem B4918805 : Blo 1455547 4918805 := bbase (se 6 (by rfl) ⟨115284, by rfl⟩ : syracuseStep 4918805 = 230569) (by norm_num)
theorem B1683149 : Blo 1455547 1683149 := bbase (se 3 (by rfl) ⟨315590, by rfl⟩ : syracuseStep 1683149 = 631181) (by norm_num)
theorem B1576657 : Blo 1455547 1576657 := bbase (se 2 (by rfl) ⟨591246, by rfl⟩ : syracuseStep 1576657 = 1182493) (by norm_num)
theorem B3501797 : Blo 1455547 3501797 := bbase (se 4 (by rfl) ⟨328293, by rfl⟩ : syracuseStep 3501797 = 656587) (by norm_num)
theorem B4665077 : Blo 1455547 4665077 := bbase (se 5 (by rfl) ⟨218675, by rfl⟩ : syracuseStep 4665077 = 437351) (by norm_num)
theorem B6221605 : Blo 1455547 6221605 := bbase (se 4 (by rfl) ⟨583275, by rfl⟩ : syracuseStep 6221605 = 1166551) (by norm_num)
theorem B8294197 : Blo 1455547 8294197 := bbase (se 5 (by rfl) ⟨388790, by rfl⟩ : syracuseStep 8294197 = 777581) (by norm_num)
theorem B1748837 : Blo 1455547 1748837 := bbase (se 4 (by rfl) ⟨163953, by rfl⟩ : syracuseStep 1748837 = 327907) (by norm_num)
theorem B4665205 : Blo 1455547 4665205 := bbase (se 5 (by rfl) ⟨218681, by rfl⟩ : syracuseStep 4665205 = 437363) (by norm_num)
theorem B3502037 : Blo 1455547 3502037 := bbase (se 7 (by rfl) ⟨41039, by rfl⟩ : syracuseStep 3502037 = 82079) (by norm_num)
theorem B5533717 : Blo 1455547 5533717 := bbase (se 6 (by rfl) ⟨129696, by rfl⟩ : syracuseStep 5533717 = 259393) (by norm_num)
theorem B2183333 : Blo 1455547 2183333 := bbase (se 4 (by rfl) ⟨204687, by rfl⟩ : syracuseStep 2183333 = 409375) (by norm_num)
theorem B1749173 : Blo 1455547 1749173 := bbase (se 5 (by rfl) ⟨81992, by rfl⟩ : syracuseStep 1749173 = 163985) (by norm_num)
theorem B2183357 : Blo 1455547 2183357 := bbase (se 3 (by rfl) ⟨409379, by rfl⟩ : syracuseStep 2183357 = 818759) (by norm_num)
theorem B2183381 : Blo 1455547 2183381 := bbase (se 7 (by rfl) ⟨25586, by rfl⟩ : syracuseStep 2183381 = 51173) (by norm_num)
theorem B2765029 : Blo 1455547 2765029 := bbase (se 4 (by rfl) ⟨259221, by rfl⟩ : syracuseStep 2765029 = 518443) (by norm_num)
theorem B7475429 : Blo 1455547 7475429 := bbase (se 4 (by rfl) ⟨700821, by rfl⟩ : syracuseStep 7475429 = 1401643) (by norm_num)
theorem B2183405 : Blo 1455547 2183405 := bbase (se 3 (by rfl) ⟨409388, by rfl⟩ : syracuseStep 2183405 = 818777) (by norm_num)
theorem B2183429 : Blo 1455547 2183429 := bbase (se 4 (by rfl) ⟨204696, by rfl⟩ : syracuseStep 2183429 = 409393) (by norm_num)
theorem B2183453 : Blo 1455547 2183453 := bbase (se 3 (by rfl) ⟨409397, by rfl⟩ : syracuseStep 2183453 = 818795) (by norm_num)
theorem B1749289 : Blo 1455547 1749289 := bbase (se 2 (by rfl) ⟨655983, by rfl⟩ : syracuseStep 1749289 = 1311967) (by norm_num)
theorem B2183477 : Blo 1455547 2183477 := bbase (se 5 (by rfl) ⟨102350, by rfl⟩ : syracuseStep 2183477 = 204701) (by norm_num)
theorem B1577281 : Blo 1455547 1577281 := bbase (se 2 (by rfl) ⟨591480, by rfl⟩ : syracuseStep 1577281 = 1182961) (by norm_num)
theorem B5534021 : Blo 1455547 5534021 := bbase (se 4 (by rfl) ⟨518814, by rfl⟩ : syracuseStep 5534021 = 1037629) (by norm_num)
theorem B2183501 : Blo 1455547 2183501 := bbase (se 3 (by rfl) ⟨409406, by rfl⟩ : syracuseStep 2183501 = 818813) (by norm_num)
theorem B2183525 : Blo 1455547 2183525 := bbase (se 4 (by rfl) ⟨204705, by rfl⟩ : syracuseStep 2183525 = 409411) (by norm_num)
theorem B4149605 : Blo 1455547 4149605 := bbase (se 4 (by rfl) ⟨389025, by rfl⟩ : syracuseStep 4149605 = 778051) (by norm_num)
theorem B1749361 : Blo 1455547 1749361 := bbase (se 2 (by rfl) ⟨656010, by rfl⟩ : syracuseStep 1749361 = 1312021) (by norm_num)
theorem B2765173 : Blo 1455547 2765173 := bbase (se 5 (by rfl) ⟨129617, by rfl⟩ : syracuseStep 2765173 = 259235) (by norm_num)
theorem B2183549 : Blo 1455547 2183549 := bbase (se 3 (by rfl) ⟨409415, by rfl⟩ : syracuseStep 2183549 = 818831) (by norm_num)
theorem B1749385 : Blo 1455547 1749385 := bbase (se 2 (by rfl) ⟨656019, by rfl⟩ : syracuseStep 1749385 = 1312039) (by norm_num)
theorem B2183573 : Blo 1455547 2183573 := bbase (se 6 (by rfl) ⟨51177, by rfl⟩ : syracuseStep 2183573 = 102355) (by norm_num)
theorem B7377317 : Blo 1455547 7377317 := bbase (se 4 (by rfl) ⟨691623, by rfl⟩ : syracuseStep 7377317 = 1383247) (by norm_num)
theorem B2183597 : Blo 1455547 2183597 := bbase (se 3 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 2183597 = 818849) (by norm_num)
theorem B2183621 : Blo 1455547 2183621 := bbase (se 4 (by rfl) ⟨204714, by rfl⟩ : syracuseStep 2183621 = 409429) (by norm_num)
theorem B2183645 : Blo 1455547 2183645 := bbase (se 3 (by rfl) ⟨409433, by rfl⟩ : syracuseStep 2183645 = 818867) (by norm_num)
theorem B2183669 : Blo 1455547 2183669 := bbase (se 5 (by rfl) ⟨102359, by rfl⟩ : syracuseStep 2183669 = 204719) (by norm_num)
theorem B2183693 : Blo 1455547 2183693 := bbase (se 3 (by rfl) ⟨409442, by rfl⟩ : syracuseStep 2183693 = 818885) (by norm_num)
theorem B2765333 : Blo 1455547 2765333 := bbase (se 6 (by rfl) ⟨64812, by rfl⟩ : syracuseStep 2765333 = 129625) (by norm_num)
theorem B1749529 : Blo 1455547 1749529 := bbase (se 2 (by rfl) ⟨656073, by rfl⟩ : syracuseStep 1749529 = 1312147) (by norm_num)
theorem B2183717 : Blo 1455547 2183717 := bbase (se 4 (by rfl) ⟨204723, by rfl⟩ : syracuseStep 2183717 = 409447) (by norm_num)
theorem B1684009 : Blo 1455547 1684009 := bbase (se 2 (by rfl) ⟨631503, by rfl⟩ : syracuseStep 1684009 = 1263007) (by norm_num)
theorem B2183741 : Blo 1455547 2183741 := bbase (se 3 (by rfl) ⟨409451, by rfl⟩ : syracuseStep 2183741 = 818903) (by norm_num)
theorem B2183765 : Blo 1455547 2183765 := bbase (se 8 (by rfl) ⟨12795, by rfl⟩ : syracuseStep 2183765 = 25591) (by norm_num)
theorem B1684069 : Blo 1455547 1684069 := bbase (se 4 (by rfl) ⟨157881, by rfl⟩ : syracuseStep 1684069 = 315763) (by norm_num)
theorem B2183789 : Blo 1455547 2183789 := bbase (se 3 (by rfl) ⟨409460, by rfl⟩ : syracuseStep 2183789 = 818921) (by norm_num)
theorem B2183813 : Blo 1455547 2183813 := bbase (se 4 (by rfl) ⟨204732, by rfl⟩ : syracuseStep 2183813 = 409465) (by norm_num)
theorem B2183837 : Blo 1455547 2183837 := bbase (se 3 (by rfl) ⟨409469, by rfl⟩ : syracuseStep 2183837 = 818939) (by norm_num)
theorem B2765477 : Blo 1455547 2765477 := bbase (se 4 (by rfl) ⟨259263, by rfl⟩ : syracuseStep 2765477 = 518527) (by norm_num)
theorem B3322541 : Blo 1455547 3322541 := bbase (se 3 (by rfl) ⟨622976, by rfl⟩ : syracuseStep 3322541 = 1245953) (by norm_num)
theorem B2183861 : Blo 1455547 2183861 := bbase (se 5 (by rfl) ⟨102368, by rfl⟩ : syracuseStep 2183861 = 204737) (by norm_num)
theorem B3109565 : Blo 1455547 3109565 := bbase (se 3 (by rfl) ⟨583043, by rfl⟩ : syracuseStep 3109565 = 1166087) (by norm_num)
theorem B2183885 : Blo 1455547 2183885 := bbase (se 3 (by rfl) ⟨409478, by rfl⟩ : syracuseStep 2183885 = 818957) (by norm_num)
theorem B1774285 : Blo 1455547 1774285 := bbase (se 3 (by rfl) ⟨332678, by rfl⟩ : syracuseStep 1774285 = 665357) (by norm_num)
theorem B2183909 : Blo 1455547 2183909 := bbase (se 4 (by rfl) ⟨204741, by rfl⟩ : syracuseStep 2183909 = 409483) (by norm_num)
theorem B2183933 : Blo 1455547 2183933 := bbase (se 3 (by rfl) ⟨409487, by rfl⟩ : syracuseStep 2183933 = 818975) (by norm_num)
theorem B2183957 : Blo 1455547 2183957 := bbase (se 6 (by rfl) ⟨51186, by rfl⟩ : syracuseStep 2183957 = 102373) (by norm_num)
theorem B2183981 : Blo 1455547 2183981 := bbase (se 3 (by rfl) ⟨409496, by rfl⟩ : syracuseStep 2183981 = 818993) (by norm_num)
theorem B7369541 : Blo 1455547 7369541 := bbase (se 4 (by rfl) ⟨690894, by rfl⟩ : syracuseStep 7369541 = 1381789) (by norm_num)
theorem B2184005 : Blo 1455547 2184005 := bbase (se 4 (by rfl) ⟨204750, by rfl⟩ : syracuseStep 2184005 = 409501) (by norm_num)
theorem B3109709 : Blo 1455547 3109709 := bbase (se 3 (by rfl) ⟨583070, by rfl⟩ : syracuseStep 3109709 = 1166141) (by norm_num)
theorem B28365653 : Blo 1455547 28365653 := bbase (se 9 (by rfl) ⟨83102, by rfl⟩ : syracuseStep 28365653 = 166205) (by norm_num)
theorem B2184029 : Blo 1455547 2184029 := bbase (se 3 (by rfl) ⟨409505, by rfl⟩ : syracuseStep 2184029 = 819011) (by norm_num)
theorem B2184053 : Blo 1455547 2184053 := bbase (se 5 (by rfl) ⟨102377, by rfl⟩ : syracuseStep 2184053 = 204755) (by norm_num)
theorem B2184077 : Blo 1455547 2184077 := bbase (se 3 (by rfl) ⟨409514, by rfl⟩ : syracuseStep 2184077 = 819029) (by norm_num)
theorem B2184101 : Blo 1455547 2184101 := bbase (se 4 (by rfl) ⟨204759, by rfl⟩ : syracuseStep 2184101 = 409519) (by norm_num)
theorem B7000997 : Blo 1455547 7000997 := bbase (se 4 (by rfl) ⟨656343, by rfl⟩ : syracuseStep 7000997 = 1312687) (by norm_num)
theorem B1495985 : Blo 1455547 1495985 := bbase (se 2 (by rfl) ⟨560994, by rfl⟩ : syracuseStep 1495985 = 1121989) (by norm_num)
theorem B2184125 : Blo 1455547 2184125 := bbase (se 3 (by rfl) ⟨409523, by rfl⟩ : syracuseStep 2184125 = 819047) (by norm_num)
theorem B2765765 : Blo 1455547 2765765 := bbase (se 4 (by rfl) ⟨259290, by rfl⟩ : syracuseStep 2765765 = 518581) (by norm_num)
theorem B2184149 : Blo 1455547 2184149 := bbase (se 7 (by rfl) ⟨25595, by rfl⟩ : syracuseStep 2184149 = 51191) (by norm_num)
theorem B28013525 : Blo 1455547 28013525 := bbase (se 7 (by rfl) ⟨328283, by rfl⟩ : syracuseStep 28013525 = 656567) (by norm_num)
theorem B2184173 : Blo 1455547 2184173 := bbase (se 3 (by rfl) ⟨409532, by rfl⟩ : syracuseStep 2184173 = 819065) (by norm_num)
theorem B2184197 : Blo 1455547 2184197 := bbase (se 4 (by rfl) ⟨204768, by rfl⟩ : syracuseStep 2184197 = 409537) (by norm_num)
theorem B2331661 : Blo 1455547 2331661 := bbase (se 3 (by rfl) ⟨437186, by rfl⟩ : syracuseStep 2331661 = 874373) (by norm_num)
theorem B2184221 : Blo 1455547 2184221 := bbase (se 3 (by rfl) ⟨409541, by rfl⟩ : syracuseStep 2184221 = 819083) (by norm_num)
theorem B2184245 : Blo 1455547 2184245 := bbase (se 5 (by rfl) ⟨102386, by rfl⟩ : syracuseStep 2184245 = 204773) (by norm_num)
theorem B2184269 : Blo 1455547 2184269 := bbase (se 3 (by rfl) ⟨409550, by rfl⟩ : syracuseStep 2184269 = 819101) (by norm_num)
theorem B9335893 : Blo 1455547 9335893 := bbase (se 8 (by rfl) ⟨54702, by rfl⟩ : syracuseStep 9335893 = 109405) (by norm_num)
theorem B2765917 : Blo 1455547 2765917 := bbase (se 3 (by rfl) ⟨518609, by rfl⟩ : syracuseStep 2765917 = 1037219) (by norm_num)
theorem B2184293 : Blo 1455547 2184293 := bbase (se 4 (by rfl) ⟨204777, by rfl⟩ : syracuseStep 2184293 = 409555) (by norm_num)
theorem B2184317 : Blo 1455547 2184317 := bbase (se 3 (by rfl) ⟨409559, by rfl⟩ : syracuseStep 2184317 = 819119) (by norm_num)
theorem B2184341 : Blo 1455547 2184341 := bbase (se 6 (by rfl) ⟨51195, by rfl⟩ : syracuseStep 2184341 = 102391) (by norm_num)
theorem B2184365 : Blo 1455547 2184365 := bbase (se 3 (by rfl) ⟨409568, by rfl⟩ : syracuseStep 2184365 = 819137) (by norm_num)
theorem B9327797 : Blo 1455547 9327797 := bbase (se 5 (by rfl) ⟨437240, by rfl⟩ : syracuseStep 9327797 = 874481) (by norm_num)
theorem B3110069 : Blo 1455547 3110069 := bbase (se 5 (by rfl) ⟨145784, by rfl⟩ : syracuseStep 3110069 = 291569) (by norm_num)
theorem B2184389 : Blo 1455547 2184389 := bbase (se 4 (by rfl) ⟨204786, by rfl⟩ : syracuseStep 2184389 = 409573) (by norm_num)
theorem B2184413 : Blo 1455547 2184413 := bbase (se 3 (by rfl) ⟨409577, by rfl⟩ : syracuseStep 2184413 = 819155) (by norm_num)
theorem B2184437 : Blo 1455547 2184437 := bbase (se 5 (by rfl) ⟨102395, by rfl⟩ : syracuseStep 2184437 = 204791) (by norm_num)
theorem B2184461 : Blo 1455547 2184461 := bbase (se 3 (by rfl) ⟨409586, by rfl⟩ : syracuseStep 2184461 = 819173) (by norm_num)
theorem B2184485 : Blo 1455547 2184485 := bbase (se 4 (by rfl) ⟨204795, by rfl⟩ : syracuseStep 2184485 = 409591) (by norm_num)
theorem B2184509 : Blo 1455547 2184509 := bbase (se 3 (by rfl) ⟨409595, by rfl⟩ : syracuseStep 2184509 = 819191) (by norm_num)
theorem B2184533 : Blo 1455547 2184533 := bbase (se 18 (by rfl) ⟨12, by rfl⟩ : syracuseStep 2184533 = 25) (by norm_num)
theorem B2184557 : Blo 1455547 2184557 := bbase (se 3 (by rfl) ⟨409604, by rfl⟩ : syracuseStep 2184557 = 819209) (by norm_num)
theorem B3790189 : Blo 1455547 3790189 := bbase (se 3 (by rfl) ⟨710660, by rfl⟩ : syracuseStep 3790189 = 1421321) (by norm_num)
theorem B3151237 : Blo 1455547 3151237 := bbase (se 4 (by rfl) ⟨295428, by rfl⟩ : syracuseStep 3151237 = 590857) (by norm_num)
theorem B2184581 : Blo 1455547 2184581 := bbase (se 4 (by rfl) ⟨204804, by rfl⟩ : syracuseStep 2184581 = 409609) (by norm_num)
theorem B2766221 : Blo 1455547 2766221 := bbase (se 3 (by rfl) ⟨518666, by rfl⟩ : syracuseStep 2766221 = 1037333) (by norm_num)
theorem B2184605 : Blo 1455547 2184605 := bbase (se 3 (by rfl) ⟨409613, by rfl⟩ : syracuseStep 2184605 = 819227) (by norm_num)
theorem B1660321 : Blo 1455547 1660321 := bbase (se 2 (by rfl) ⟨622620, by rfl⟩ : syracuseStep 1660321 = 1245241) (by norm_num)
theorem B2184629 : Blo 1455547 2184629 := bbase (se 5 (by rfl) ⟨102404, by rfl⟩ : syracuseStep 2184629 = 204809) (by norm_num)
theorem B14005685 : Blo 1455547 14005685 := bbase (se 5 (by rfl) ⟨656516, by rfl⟩ : syracuseStep 14005685 = 1313033) (by norm_num)
theorem B2184653 : Blo 1455547 2184653 := bbase (se 3 (by rfl) ⟨409622, by rfl⟩ : syracuseStep 2184653 = 819245) (by norm_num)
theorem B2184677 : Blo 1455547 2184677 := bbase (se 4 (by rfl) ⟨204813, by rfl⟩ : syracuseStep 2184677 = 409627) (by norm_num)
theorem B2184701 : Blo 1455547 2184701 := bbase (se 3 (by rfl) ⟨409631, by rfl⟩ : syracuseStep 2184701 = 819263) (by norm_num)
theorem B2184725 : Blo 1455547 2184725 := bbase (se 6 (by rfl) ⟨51204, by rfl⟩ : syracuseStep 2184725 = 102409) (by norm_num)
theorem B2184749 : Blo 1455547 2184749 := bbase (se 3 (by rfl) ⟨409640, by rfl⟩ : syracuseStep 2184749 = 819281) (by norm_num)
theorem B2184773 : Blo 1455547 2184773 := bbase (se 4 (by rfl) ⟨204822, by rfl⟩ : syracuseStep 2184773 = 409645) (by norm_num)
theorem B2184797 : Blo 1455547 2184797 := bbase (se 3 (by rfl) ⟨409649, by rfl⟩ : syracuseStep 2184797 = 819299) (by norm_num)
theorem B4912757 : Blo 1455547 4912757 := bbase (se 5 (by rfl) ⟨230285, by rfl⟩ : syracuseStep 4912757 = 460571) (by norm_num)
theorem B2184821 : Blo 1455547 2184821 := bbase (se 5 (by rfl) ⟨102413, by rfl⟩ : syracuseStep 2184821 = 204827) (by norm_num)
theorem B2184845 : Blo 1455547 2184845 := bbase (se 3 (by rfl) ⟨409658, by rfl⟩ : syracuseStep 2184845 = 819317) (by norm_num)
theorem B2184869 : Blo 1455547 2184869 := bbase (se 4 (by rfl) ⟨204831, by rfl⟩ : syracuseStep 2184869 = 409663) (by norm_num)
theorem B2332333 : Blo 1455547 2332333 := bbase (se 3 (by rfl) ⟨437312, by rfl⟩ : syracuseStep 2332333 = 874625) (by norm_num)
theorem B4429493 : Blo 1455547 4429493 := bbase (se 5 (by rfl) ⟨207632, by rfl⟩ : syracuseStep 4429493 = 415265) (by norm_num)
theorem B7378613 : Blo 1455547 7378613 := bbase (se 5 (by rfl) ⟨345872, by rfl⟩ : syracuseStep 7378613 = 691745) (by norm_num)
theorem B2184893 : Blo 1455547 2184893 := bbase (se 3 (by rfl) ⟨409667, by rfl⟩ : syracuseStep 2184893 = 819335) (by norm_num)
theorem B2184917 : Blo 1455547 2184917 := bbase (se 7 (by rfl) ⟨25604, by rfl⟩ : syracuseStep 2184917 = 51209) (by norm_num)
theorem B1750745 : Blo 1455547 1750745 := bbase (se 2 (by rfl) ⟨656529, by rfl⟩ : syracuseStep 1750745 = 1313059) (by norm_num)
theorem B2184941 : Blo 1455547 2184941 := bbase (se 3 (by rfl) ⟨409676, by rfl⟩ : syracuseStep 2184941 = 819353) (by norm_num)
theorem B8296181 : Blo 1455547 8296181 := bbase (se 5 (by rfl) ⟨388883, by rfl⟩ : syracuseStep 8296181 = 777767) (by norm_num)
theorem B2184965 : Blo 1455547 2184965 := bbase (se 4 (by rfl) ⟨204840, by rfl⟩ : syracuseStep 2184965 = 409681) (by norm_num)
theorem B3938053 : Blo 1455547 3938053 := bbase (se 4 (by rfl) ⟨369192, by rfl⟩ : syracuseStep 3938053 = 738385) (by norm_num)
theorem B2184989 : Blo 1455547 2184989 := bbase (se 3 (by rfl) ⟨409685, by rfl⟩ : syracuseStep 2184989 = 819371) (by norm_num)
theorem B2185013 : Blo 1455547 2185013 := bbase (se 5 (by rfl) ⟨102422, by rfl⟩ : syracuseStep 2185013 = 204845) (by norm_num)
theorem B2185037 : Blo 1455547 2185037 := bbase (se 3 (by rfl) ⟨409694, by rfl⟩ : syracuseStep 2185037 = 819389) (by norm_num)
theorem B2185061 : Blo 1455547 2185061 := bbase (se 4 (by rfl) ⟨204849, by rfl⟩ : syracuseStep 2185061 = 409699) (by norm_num)
theorem B3938149 : Blo 1455547 3938149 := bbase (se 4 (by rfl) ⟨369201, by rfl⟩ : syracuseStep 3938149 = 738403) (by norm_num)
theorem B1537913 : Blo 1455547 1537913 := bbase (se 2 (by rfl) ⟨576717, by rfl⟩ : syracuseStep 1537913 = 1153435) (by norm_num)
theorem B2185085 : Blo 1455547 2185085 := bbase (se 3 (by rfl) ⟨409703, by rfl⟩ : syracuseStep 2185085 = 819407) (by norm_num)
theorem B2185109 : Blo 1455547 2185109 := bbase (se 6 (by rfl) ⟨51213, by rfl⟩ : syracuseStep 2185109 = 102427) (by norm_num)
theorem B2185133 : Blo 1455547 2185133 := bbase (se 3 (by rfl) ⟨409712, by rfl⟩ : syracuseStep 2185133 = 819425) (by norm_num)
theorem B2185157 : Blo 1455547 2185157 := bbase (se 4 (by rfl) ⟨204858, by rfl⟩ : syracuseStep 2185157 = 409717) (by norm_num)
theorem B1554385 : Blo 1455547 1554385 := bbase (se 2 (by rfl) ⟨582894, by rfl⟩ : syracuseStep 1554385 = 1165789) (by norm_num)
theorem B2185181 : Blo 1455547 2185181 := bbase (se 3 (by rfl) ⟨409721, by rfl⟩ : syracuseStep 2185181 = 819443) (by norm_num)
theorem B2185205 : Blo 1455547 2185205 := bbase (se 5 (by rfl) ⟨102431, by rfl⟩ : syracuseStep 2185205 = 204863) (by norm_num)
theorem B13293557 : Blo 1455547 13293557 := bbase (se 5 (by rfl) ⟨623135, by rfl⟩ : syracuseStep 13293557 = 1246271) (by norm_num)
theorem B1660933 : Blo 1455547 1660933 := bbase (se 4 (by rfl) ⟨155712, by rfl⟩ : syracuseStep 1660933 = 311425) (by norm_num)
theorem B2185229 : Blo 1455547 2185229 := bbase (se 3 (by rfl) ⟨409730, by rfl⟩ : syracuseStep 2185229 = 819461) (by norm_num)
theorem B27981845 : Blo 1455547 27981845 := bbase (se 6 (by rfl) ⟨655824, by rfl⟩ : syracuseStep 27981845 = 1311649) (by norm_num)
theorem B15742997 : Blo 1455547 15742997 := bbase (se 6 (by rfl) ⟨368976, by rfl⟩ : syracuseStep 15742997 = 737953) (by norm_num)
theorem B4913189 : Blo 1455547 4913189 := bbase (se 4 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 4913189 = 921223) (by norm_num)
theorem B2185253 : Blo 1455547 2185253 := bbase (se 4 (by rfl) ⟨204867, by rfl⟩ : syracuseStep 2185253 = 409735) (by norm_num)
theorem B3110957 : Blo 1455547 3110957 := bbase (se 3 (by rfl) ⟨583304, by rfl⟩ : syracuseStep 3110957 = 1166609) (by norm_num)
theorem B14956597 : Blo 1455547 14956597 := bbase (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) (by norm_num)
theorem B2185277 : Blo 1455547 2185277 := bbase (se 3 (by rfl) ⟨409739, by rfl⟩ : syracuseStep 2185277 = 819479) (by norm_num)
theorem B1554509 : Blo 1455547 1554509 := bbase (se 3 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 1554509 = 582941) (by norm_num)
theorem B3684437 : Blo 1455547 3684437 := bbase (se 8 (by rfl) ⟨21588, by rfl⟩ : syracuseStep 3684437 = 43177) (by norm_num)
theorem B7370837 : Blo 1455547 7370837 := bbase (se 8 (by rfl) ⟨43188, by rfl⟩ : syracuseStep 7370837 = 86377) (by norm_num)
theorem B2185301 : Blo 1455547 2185301 := bbase (se 8 (by rfl) ⟨12804, by rfl⟩ : syracuseStep 2185301 = 25609) (by norm_num)
theorem B2185325 : Blo 1455547 2185325 := bbase (se 3 (by rfl) ⟨409748, by rfl⟩ : syracuseStep 2185325 = 819497) (by norm_num)
theorem B2766973 : Blo 1455547 2766973 := bbase (se 3 (by rfl) ⟨518807, by rfl⟩ : syracuseStep 2766973 = 1037615) (by norm_num)
theorem B2185349 : Blo 1455547 2185349 := bbase (se 4 (by rfl) ⟨204876, by rfl⟩ : syracuseStep 2185349 = 409753) (by norm_num)
theorem B2185373 : Blo 1455547 2185373 := bbase (se 3 (by rfl) ⟨409757, by rfl⟩ : syracuseStep 2185373 = 819515) (by norm_num)
theorem B2185397 : Blo 1455547 2185397 := bbase (se 5 (by rfl) ⟨102440, by rfl⟩ : syracuseStep 2185397 = 204881) (by norm_num)
theorem B2185421 : Blo 1455547 2185421 := bbase (se 3 (by rfl) ⟨409766, by rfl⟩ : syracuseStep 2185421 = 819533) (by norm_num)
theorem B1579225 : Blo 1455547 1579225 := bbase (se 2 (by rfl) ⟨592209, by rfl⟩ : syracuseStep 1579225 = 1184419) (by norm_num)
theorem B2185445 : Blo 1455547 2185445 := bbase (se 4 (by rfl) ⟨204885, by rfl⟩ : syracuseStep 2185445 = 409771) (by norm_num)
theorem B2185469 : Blo 1455547 2185469 := bbase (se 3 (by rfl) ⟨409775, by rfl⟩ : syracuseStep 2185469 = 819551) (by norm_num)
theorem B3684629 : Blo 1455547 3684629 := bbase (se 6 (by rfl) ⟨86358, by rfl⟩ : syracuseStep 3684629 = 172717) (by norm_num)
theorem B2185493 : Blo 1455547 2185493 := bbase (se 6 (by rfl) ⟨51222, by rfl⟩ : syracuseStep 2185493 = 102445) (by norm_num)
theorem B3275045 : Blo 1455547 3275045 := bbase (se 4 (by rfl) ⟨307035, by rfl⟩ : syracuseStep 3275045 = 614071) (by norm_num)
theorem B3111205 : Blo 1455547 3111205 := bbase (se 4 (by rfl) ⟨291675, by rfl⟩ : syracuseStep 3111205 = 583351) (by norm_num)
theorem B2185517 : Blo 1455547 2185517 := bbase (se 3 (by rfl) ⟨409784, by rfl⟩ : syracuseStep 2185517 = 819569) (by norm_num)
theorem B2185541 : Blo 1455547 2185541 := bbase (se 4 (by rfl) ⟨204894, by rfl⟩ : syracuseStep 2185541 = 409789) (by norm_num)
theorem B1554761 : Blo 1455547 1554761 := bbase (se 2 (by rfl) ⟨583035, by rfl⟩ : syracuseStep 1554761 = 1166071) (by norm_num)
theorem B2185565 : Blo 1455547 2185565 := bbase (se 3 (by rfl) ⟨409793, by rfl⟩ : syracuseStep 2185565 = 819587) (by norm_num)
theorem B3275117 : Blo 1455547 3275117 := bbase (se 3 (by rfl) ⟨614084, by rfl⟩ : syracuseStep 3275117 = 1228169) (by norm_num)
theorem B2185589 : Blo 1455547 2185589 := bbase (se 5 (by rfl) ⟨102449, by rfl⟩ : syracuseStep 2185589 = 204899) (by norm_num)
theorem B2185613 : Blo 1455547 2185613 := bbase (se 3 (by rfl) ⟨409802, by rfl⟩ : syracuseStep 2185613 = 819605) (by norm_num)
theorem B7985557 : Blo 1455547 7985557 := bbase (se 6 (by rfl) ⟨187161, by rfl⟩ : syracuseStep 7985557 = 374323) (by norm_num)
theorem B2185637 : Blo 1455547 2185637 := bbase (se 4 (by rfl) ⟨204903, by rfl⟩ : syracuseStep 2185637 = 409807) (by norm_num)
theorem B3275189 : Blo 1455547 3275189 := bbase (se 5 (by rfl) ⟨153524, by rfl⟩ : syracuseStep 3275189 = 307049) (by norm_num)
theorem B2185661 : Blo 1455547 2185661 := bbase (se 3 (by rfl) ⟨409811, by rfl⟩ : syracuseStep 2185661 = 819623) (by norm_num)
theorem B2275781 : Blo 1455547 2275781 := bbase (se 4 (by rfl) ⟨213354, by rfl⟩ : syracuseStep 2275781 = 426709) (by norm_num)
theorem B4913621 : Blo 1455547 4913621 := bbase (se 7 (by rfl) ⟨57581, by rfl⟩ : syracuseStep 4913621 = 115163) (by norm_num)
theorem B2185685 : Blo 1455547 2185685 := bbase (se 7 (by rfl) ⟨25613, by rfl⟩ : syracuseStep 2185685 = 51227) (by norm_num)
theorem B2185709 : Blo 1455547 2185709 := bbase (se 3 (by rfl) ⟨409820, by rfl⟩ : syracuseStep 2185709 = 819641) (by norm_num)
theorem B3275261 : Blo 1455547 3275261 := bbase (se 3 (by rfl) ⟨614111, by rfl⟩ : syracuseStep 3275261 = 1228223) (by norm_num)
theorem B2185733 : Blo 1455547 2185733 := bbase (se 4 (by rfl) ⟨204912, by rfl⟩ : syracuseStep 2185733 = 409825) (by norm_num)
theorem B2185757 : Blo 1455547 2185757 := bbase (se 3 (by rfl) ⟨409829, by rfl⟩ : syracuseStep 2185757 = 819659) (by norm_num)
theorem B2185781 : Blo 1455547 2185781 := bbase (se 5 (by rfl) ⟨102458, by rfl⟩ : syracuseStep 2185781 = 204917) (by norm_num)
theorem B3275333 : Blo 1455547 3275333 := bbase (se 4 (by rfl) ⟨307062, by rfl⟩ : syracuseStep 3275333 = 614125) (by norm_num)
theorem B2185805 : Blo 1455547 2185805 := bbase (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) (by norm_num)
theorem B2185829 : Blo 1455547 2185829 := bbase (se 4 (by rfl) ⟨204921, by rfl⟩ : syracuseStep 2185829 = 409843) (by norm_num)
theorem B3684973 : Blo 1455547 3684973 := bbase (se 3 (by rfl) ⟨690932, by rfl⟩ : syracuseStep 3684973 = 1381865) (by norm_num)
theorem B2185853 : Blo 1455547 2185853 := bbase (se 3 (by rfl) ⟨409847, by rfl⟩ : syracuseStep 2185853 = 819695) (by norm_num)
theorem B3275405 : Blo 1455547 3275405 := bbase (se 3 (by rfl) ⟨614138, by rfl⟩ : syracuseStep 3275405 = 1228277) (by norm_num)
theorem B2333333 : Blo 1455547 2333333 := bbase (se 6 (by rfl) ⟨54687, by rfl⟩ : syracuseStep 2333333 = 109375) (by norm_num)
theorem B2185877 : Blo 1455547 2185877 := bbase (se 6 (by rfl) ⟨51231, by rfl⟩ : syracuseStep 2185877 = 102463) (by norm_num)
theorem B2456237 : Blo 1455547 2456237 := bbase (se 3 (by rfl) ⟨460544, by rfl⟩ : syracuseStep 2456237 = 921089) (by norm_num)
theorem B2185901 : Blo 1455547 2185901 := bbase (se 3 (by rfl) ⟨409856, by rfl⟩ : syracuseStep 2185901 = 819713) (by norm_num)
theorem B4668101 : Blo 1455547 4668101 := bbase (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) (by norm_num)
theorem B2185925 : Blo 1455547 2185925 := bbase (se 4 (by rfl) ⟨204930, by rfl⟩ : syracuseStep 2185925 = 409861) (by norm_num)
theorem B3275477 : Blo 1455547 3275477 := bbase (se 7 (by rfl) ⟨38384, by rfl⟩ : syracuseStep 3275477 = 76769) (by norm_num)
theorem B6224597 : Blo 1455547 6224597 := bbase (se 7 (by rfl) ⟨72944, by rfl⟩ : syracuseStep 6224597 = 145889) (by norm_num)
theorem B3685085 : Blo 1455547 3685085 := bbase (se 3 (by rfl) ⟨690953, by rfl⟩ : syracuseStep 3685085 = 1381907) (by norm_num)
theorem B2185949 : Blo 1455547 2185949 := bbase (se 3 (by rfl) ⟨409865, by rfl⟩ : syracuseStep 2185949 = 819731) (by norm_num)
theorem B2185973 : Blo 1455547 2185973 := bbase (se 5 (by rfl) ⟨102467, by rfl⟩ : syracuseStep 2185973 = 204935) (by norm_num)
theorem B1555205 : Blo 1455547 1555205 := bbase (se 4 (by rfl) ⟨145800, by rfl⟩ : syracuseStep 1555205 = 291601) (by norm_num)
theorem B2185997 : Blo 1455547 2185997 := bbase (se 3 (by rfl) ⟨409874, by rfl⟩ : syracuseStep 2185997 = 819749) (by norm_num)
theorem B3275549 : Blo 1455547 3275549 := bbase (se 3 (by rfl) ⟨614165, by rfl⟩ : syracuseStep 3275549 = 1228331) (by norm_num)
theorem B3111709 : Blo 1455547 3111709 := bbase (se 3 (by rfl) ⟨583445, by rfl⟩ : syracuseStep 3111709 = 1166891) (by norm_num)
theorem B5528357 : Blo 1455547 5528357 := bbase (se 4 (by rfl) ⟨518283, by rfl⟩ : syracuseStep 5528357 = 1036567) (by norm_num)
theorem B2186021 : Blo 1455547 2186021 := bbase (se 4 (by rfl) ⟨204939, by rfl⟩ : syracuseStep 2186021 = 409879) (by norm_num)
theorem B2456365 : Blo 1455547 2456365 := bbase (se 3 (by rfl) ⟨460568, by rfl⟩ : syracuseStep 2456365 = 921137) (by norm_num)
theorem B2186045 : Blo 1455547 2186045 := bbase (se 3 (by rfl) ⟨409883, by rfl⟩ : syracuseStep 2186045 = 819767) (by norm_num)
theorem B2186069 : Blo 1455547 2186069 := bbase (se 9 (by rfl) ⟨6404, by rfl⟩ : syracuseStep 2186069 = 12809) (by norm_num)
theorem B3275621 : Blo 1455547 3275621 := bbase (se 4 (by rfl) ⟨307089, by rfl⟩ : syracuseStep 3275621 = 614179) (by norm_num)
theorem B2186093 : Blo 1455547 2186093 := bbase (se 3 (by rfl) ⟨409892, by rfl⟩ : syracuseStep 2186093 = 819785) (by norm_num)
theorem B2456453 : Blo 1455547 2456453 := bbase (se 4 (by rfl) ⟨230292, by rfl⟩ : syracuseStep 2456453 = 460585) (by norm_num)
theorem B4914053 : Blo 1455547 4914053 := bbase (se 4 (by rfl) ⟨460692, by rfl⟩ : syracuseStep 4914053 = 921385) (by norm_num)
theorem B2186117 : Blo 1455547 2186117 := bbase (se 4 (by rfl) ⟨204948, by rfl⟩ : syracuseStep 2186117 = 409897) (by norm_num)
theorem B3685277 : Blo 1455547 3685277 := bbase (se 3 (by rfl) ⟨690989, by rfl⟩ : syracuseStep 3685277 = 1381979) (by norm_num)
theorem B2186141 : Blo 1455547 2186141 := bbase (se 3 (by rfl) ⟨409901, by rfl⟩ : syracuseStep 2186141 = 819803) (by norm_num)
theorem B3275693 : Blo 1455547 3275693 := bbase (se 3 (by rfl) ⟨614192, by rfl⟩ : syracuseStep 3275693 = 1228385) (by norm_num)
theorem B2186165 : Blo 1455547 2186165 := bbase (se 5 (by rfl) ⟨102476, by rfl⟩ : syracuseStep 2186165 = 204953) (by norm_num)
theorem B1661881 : Blo 1455547 1661881 := bbase (se 2 (by rfl) ⟨623205, by rfl⟩ : syracuseStep 1661881 = 1246411) (by norm_num)
theorem B2186189 : Blo 1455547 2186189 := bbase (se 3 (by rfl) ⟨409910, by rfl⟩ : syracuseStep 2186189 = 819821) (by norm_num)
theorem B2186213 : Blo 1455547 2186213 := bbase (se 4 (by rfl) ⟨204957, by rfl⟩ : syracuseStep 2186213 = 409915) (by norm_num)
theorem B3275765 : Blo 1455547 3275765 := bbase (se 5 (by rfl) ⟨153551, by rfl⟩ : syracuseStep 3275765 = 307103) (by norm_num)
theorem B1555453 : Blo 1455547 1555453 := bbase (se 3 (by rfl) ⟨291647, by rfl⟩ : syracuseStep 1555453 = 583295) (by norm_num)
theorem B2186237 : Blo 1455547 2186237 := bbase (se 3 (by rfl) ⟨409919, by rfl⟩ : syracuseStep 2186237 = 819839) (by norm_num)
theorem B2456581 : Blo 1455547 2456581 := bbase (se 4 (by rfl) ⟨230304, by rfl⟩ : syracuseStep 2456581 = 460609) (by norm_num)
theorem B1842193 : Blo 1455547 1842193 := bbase (se 2 (by rfl) ⟨690822, by rfl⟩ : syracuseStep 1842193 = 1381645) (by norm_num)
theorem B2186261 : Blo 1455547 2186261 := bbase (se 6 (by rfl) ⟨51240, by rfl⟩ : syracuseStep 2186261 = 102481) (by norm_num)
theorem B2186285 : Blo 1455547 2186285 := bbase (se 3 (by rfl) ⟨409928, by rfl⟩ : syracuseStep 2186285 = 819857) (by norm_num)
theorem B3275837 : Blo 1455547 3275837 := bbase (se 3 (by rfl) ⟨614219, by rfl⟩ : syracuseStep 3275837 = 1228439) (by norm_num)
theorem B5528645 : Blo 1455547 5528645 := bbase (se 4 (by rfl) ⟨518310, by rfl⟩ : syracuseStep 5528645 = 1036621) (by norm_num)
theorem B2186309 : Blo 1455547 2186309 := bbase (se 4 (by rfl) ⟨204966, by rfl⟩ : syracuseStep 2186309 = 409933) (by norm_num)
theorem B2456669 : Blo 1455547 2456669 := bbase (se 3 (by rfl) ⟨460625, by rfl⟩ : syracuseStep 2456669 = 921251) (by norm_num)
theorem B3939445 : Blo 1455547 3939445 := bbase (se 5 (by rfl) ⟨184661, by rfl⟩ : syracuseStep 3939445 = 369323) (by norm_num)
theorem B1637509 : Blo 1455547 1637509 := bbase (se 4 (by rfl) ⟨153516, by rfl⟩ : syracuseStep 1637509 = 307033) (by norm_num)
theorem B3275909 : Blo 1455547 3275909 := bbase (se 4 (by rfl) ⟨307116, by rfl⟩ : syracuseStep 3275909 = 614233) (by norm_num)
theorem B3734677 : Blo 1455547 3734677 := bbase (se 6 (by rfl) ⟨87531, by rfl⟩ : syracuseStep 3734677 = 175063) (by norm_num)
theorem B1637545 : Blo 1455547 1637545 := bbase (se 2 (by rfl) ⟨614079, by rfl⟩ : syracuseStep 1637545 = 1228159) (by norm_num)
theorem B1842365 : Blo 1455547 1842365 := bbase (se 3 (by rfl) ⟨345443, by rfl⟩ : syracuseStep 1842365 = 690887) (by norm_num)
theorem B1637581 : Blo 1455547 1637581 := bbase (se 3 (by rfl) ⟨307046, by rfl⟩ : syracuseStep 1637581 = 614093) (by norm_num)
theorem B3275981 : Blo 1455547 3275981 := bbase (se 3 (by rfl) ⟨614246, by rfl⟩ : syracuseStep 3275981 = 1228493) (by norm_num)
theorem B2456797 : Blo 1455547 2456797 := bbase (se 3 (by rfl) ⟨460649, by rfl⟩ : syracuseStep 2456797 = 921299) (by norm_num)
theorem B1637617 : Blo 1455547 1637617 := bbase (se 2 (by rfl) ⟨614106, by rfl⟩ : syracuseStep 1637617 = 1228213) (by norm_num)
theorem B1842421 : Blo 1455547 1842421 := bbase (se 5 (by rfl) ⟨86363, by rfl⟩ : syracuseStep 1842421 = 172727) (by norm_num)
theorem B3685621 : Blo 1455547 3685621 := bbase (se 5 (by rfl) ⟨172763, by rfl⟩ : syracuseStep 3685621 = 345527) (by norm_num)
theorem B1637653 : Blo 1455547 1637653 := bbase (se 6 (by rfl) ⟨38382, by rfl⟩ : syracuseStep 1637653 = 76765) (by norm_num)
theorem B3276053 : Blo 1455547 3276053 := bbase (se 6 (by rfl) ⟨76782, by rfl⟩ : syracuseStep 3276053 = 153565) (by norm_num)
theorem B2456885 : Blo 1455547 2456885 := bbase (se 5 (by rfl) ⟨115166, by rfl⟩ : syracuseStep 2456885 = 230333) (by norm_num)
theorem B4914485 : Blo 1455547 4914485 := bbase (se 5 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 4914485 = 460733) (by norm_num)
theorem B1637689 : Blo 1455547 1637689 := bbase (se 2 (by rfl) ⟨614133, by rfl⟩ : syracuseStep 1637689 = 1228267) (by norm_num)
theorem B1842517 : Blo 1455547 1842517 := bbase (se 11 (by rfl) ⟨1349, by rfl⟩ : syracuseStep 1842517 = 2699) (by norm_num)
theorem B1637725 : Blo 1455547 1637725 := bbase (se 3 (by rfl) ⟨307073, by rfl⟩ : syracuseStep 1637725 = 614147) (by norm_num)
theorem B3276125 : Blo 1455547 3276125 := bbase (se 3 (by rfl) ⟨614273, by rfl⟩ : syracuseStep 3276125 = 1228547) (by norm_num)
theorem B3685733 : Blo 1455547 3685733 := bbase (se 4 (by rfl) ⟨345537, by rfl⟩ : syracuseStep 3685733 = 691075) (by norm_num)
theorem B7372133 : Blo 1455547 7372133 := bbase (se 4 (by rfl) ⟨691137, by rfl⟩ : syracuseStep 7372133 = 1382275) (by norm_num)
theorem B1637761 : Blo 1455547 1637761 := bbase (se 2 (by rfl) ⟨614160, by rfl⟩ : syracuseStep 1637761 = 1228321) (by norm_num)
theorem B1637797 : Blo 1455547 1637797 := bbase (se 4 (by rfl) ⟨153543, by rfl⟩ : syracuseStep 1637797 = 307087) (by norm_num)
theorem B3276197 : Blo 1455547 3276197 := bbase (se 4 (by rfl) ⟨307143, by rfl⟩ : syracuseStep 3276197 = 614287) (by norm_num)
theorem B2457013 : Blo 1455547 2457013 := bbase (se 5 (by rfl) ⟨115172, by rfl⟩ : syracuseStep 2457013 = 230345) (by norm_num)
theorem B1555897 : Blo 1455547 1555897 := bbase (se 2 (by rfl) ⟨583461, by rfl⟩ : syracuseStep 1555897 = 1166923) (by norm_num)
theorem B1637833 : Blo 1455547 1637833 := bbase (se 2 (by rfl) ⟨614187, by rfl⟩ : syracuseStep 1637833 = 1228375) (by norm_num)
theorem B18906581 : Blo 1455547 18906581 := bbase (se 7 (by rfl) ⟨221561, by rfl⟩ : syracuseStep 18906581 = 443123) (by norm_num)
theorem B1637869 : Blo 1455547 1637869 := bbase (se 3 (by rfl) ⟨307100, by rfl⟩ : syracuseStep 1637869 = 614201) (by norm_num)
theorem B3276269 : Blo 1455547 3276269 := bbase (se 3 (by rfl) ⟨614300, by rfl⟩ : syracuseStep 3276269 = 1228601) (by norm_num)
theorem B1555957 : Blo 1455547 1555957 := bbase (se 5 (by rfl) ⟨72935, by rfl⟩ : syracuseStep 1555957 = 145871) (by norm_num)
theorem B1842689 : Blo 1455547 1842689 := bbase (se 2 (by rfl) ⟨691008, by rfl⟩ : syracuseStep 1842689 = 1382017) (by norm_num)
theorem B2457101 : Blo 1455547 2457101 := bbase (se 3 (by rfl) ⟨460706, by rfl⟩ : syracuseStep 2457101 = 921413) (by norm_num)
theorem B1637905 : Blo 1455547 1637905 := bbase (se 2 (by rfl) ⟨614214, by rfl⟩ : syracuseStep 1637905 = 1228429) (by norm_num)
theorem B3497501 : Blo 1455547 3497501 := bbase (se 3 (by rfl) ⟨655781, by rfl⟩ : syracuseStep 3497501 = 1311563) (by norm_num)
theorem B3685925 : Blo 1455547 3685925 := bbase (se 4 (by rfl) ⟨345555, by rfl⟩ : syracuseStep 3685925 = 691111) (by norm_num)
theorem B1637941 : Blo 1455547 1637941 := bbase (se 5 (by rfl) ⟨76778, by rfl⟩ : syracuseStep 1637941 = 153557) (by norm_num)
theorem B3276341 : Blo 1455547 3276341 := bbase (se 5 (by rfl) ⟨153578, by rfl⟩ : syracuseStep 3276341 = 307157) (by norm_num)
theorem B1842745 : Blo 1455547 1842745 := bbase (se 2 (by rfl) ⟨691029, by rfl⟩ : syracuseStep 1842745 = 1382059) (by norm_num)
theorem B1637977 : Blo 1455547 1637977 := bbase (se 2 (by rfl) ⟨614241, by rfl⟩ : syracuseStep 1637977 = 1228483) (by norm_num)
theorem B1638013 : Blo 1455547 1638013 := bbase (se 3 (by rfl) ⟨307127, by rfl⟩ : syracuseStep 1638013 = 614255) (by norm_num)
theorem B3276413 : Blo 1455547 3276413 := bbase (se 3 (by rfl) ⟨614327, by rfl⟩ : syracuseStep 3276413 = 1228655) (by norm_num)
theorem B2457229 : Blo 1455547 2457229 := bbase (se 3 (by rfl) ⟨460730, by rfl⟩ : syracuseStep 2457229 = 921461) (by norm_num)
theorem B3112597 : Blo 1455547 3112597 := bbase (se 6 (by rfl) ⟨72951, by rfl⟩ : syracuseStep 3112597 = 145903) (by norm_num)
theorem B1842841 : Blo 1455547 1842841 := bbase (se 2 (by rfl) ⟨691065, by rfl⟩ : syracuseStep 1842841 = 1382131) (by norm_num)
theorem B1638049 : Blo 1455547 1638049 := bbase (se 2 (by rfl) ⟨614268, by rfl⟩ : syracuseStep 1638049 = 1228537) (by norm_num)
theorem B1638085 : Blo 1455547 1638085 := bbase (se 4 (by rfl) ⟨153570, by rfl⟩ : syracuseStep 1638085 = 307141) (by norm_num)
theorem B3276485 : Blo 1455547 3276485 := bbase (se 4 (by rfl) ⟨307170, by rfl⟩ : syracuseStep 3276485 = 614341) (by norm_num)
theorem B6225605 : Blo 1455547 6225605 := bbase (se 4 (by rfl) ⟨583650, by rfl⟩ : syracuseStep 6225605 = 1167301) (by norm_num)
theorem B3194581 : Blo 1455547 3194581 := bbase (se 7 (by rfl) ⟨37436, by rfl⟩ : syracuseStep 3194581 = 74873) (by norm_num)
theorem B2457317 : Blo 1455547 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B4914917 : Blo 1455547 4914917 := bbase (se 4 (by rfl) ⟨460773, by rfl⟩ : syracuseStep 4914917 = 921547) (by norm_num)
theorem B1638121 : Blo 1455547 1638121 := bbase (se 2 (by rfl) ⟨614295, by rfl⟩ : syracuseStep 1638121 = 1228591) (by norm_num)
theorem B2244341 : Blo 1455547 2244341 := bbase (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) (by norm_num)
theorem B1638157 : Blo 1455547 1638157 := bbase (se 3 (by rfl) ⟨307154, by rfl⟩ : syracuseStep 1638157 = 614309) (by norm_num)
theorem B3276557 : Blo 1455547 3276557 := bbase (se 3 (by rfl) ⟨614354, by rfl⟩ : syracuseStep 3276557 = 1228709) (by norm_num)
theorem B1638193 : Blo 1455547 1638193 := bbase (se 2 (by rfl) ⟨614322, by rfl⟩ : syracuseStep 1638193 = 1228645) (by norm_num)
theorem B1556273 : Blo 1455547 1556273 := bbase (se 2 (by rfl) ⟨583602, by rfl⟩ : syracuseStep 1556273 = 1167205) (by norm_num)
theorem B1843013 : Blo 1455547 1843013 := bbase (se 4 (by rfl) ⟨172782, by rfl⟩ : syracuseStep 1843013 = 345565) (by norm_num)
theorem B1638229 : Blo 1455547 1638229 := bbase (se 9 (by rfl) ⟨4799, by rfl⟩ : syracuseStep 1638229 = 9599) (by norm_num)
theorem B3276629 : Blo 1455547 3276629 := bbase (se 9 (by rfl) ⟨9599, by rfl⟩ : syracuseStep 3276629 = 19199) (by norm_num)
theorem B6217573 : Blo 1455547 6217573 := bbase (se 4 (by rfl) ⟨582897, by rfl⟩ : syracuseStep 6217573 = 1165795) (by norm_num)
theorem B2457445 : Blo 1455547 2457445 := bbase (se 4 (by rfl) ⟨230385, by rfl⟩ : syracuseStep 2457445 = 460771) (by norm_num)
theorem B1638265 : Blo 1455547 1638265 := bbase (se 2 (by rfl) ⟨614349, by rfl⟩ : syracuseStep 1638265 = 1228699) (by norm_num)
theorem B1843069 : Blo 1455547 1843069 := bbase (se 3 (by rfl) ⟨345575, by rfl⟩ : syracuseStep 1843069 = 691151) (by norm_num)
theorem B3686269 : Blo 1455547 3686269 := bbase (se 3 (by rfl) ⟨691175, by rfl⟩ : syracuseStep 3686269 = 1382351) (by norm_num)
theorem B8298389 : Blo 1455547 8298389 := bbase (se 6 (by rfl) ⟨194493, by rfl⟩ : syracuseStep 8298389 = 388987) (by norm_num)
theorem B3497885 : Blo 1455547 3497885 := bbase (se 3 (by rfl) ⟨655853, by rfl⟩ : syracuseStep 3497885 = 1311707) (by norm_num)
theorem B1638301 : Blo 1455547 1638301 := bbase (se 3 (by rfl) ⟨307181, by rfl⟩ : syracuseStep 1638301 = 614363) (by norm_num)
theorem B3276701 : Blo 1455547 3276701 := bbase (se 3 (by rfl) ⟨614381, by rfl⟩ : syracuseStep 3276701 = 1228763) (by norm_num)
theorem B2457533 : Blo 1455547 2457533 := bbase (se 3 (by rfl) ⟨460787, by rfl⟩ : syracuseStep 2457533 = 921575) (by norm_num)
theorem B1638337 : Blo 1455547 1638337 := bbase (se 2 (by rfl) ⟨614376, by rfl⟩ : syracuseStep 1638337 = 1228753) (by norm_num)
theorem B1843165 : Blo 1455547 1843165 := bbase (se 3 (by rfl) ⟨345593, by rfl⟩ : syracuseStep 1843165 = 691187) (by norm_num)
theorem B1638373 : Blo 1455547 1638373 := bbase (se 4 (by rfl) ⟨153597, by rfl⟩ : syracuseStep 1638373 = 307195) (by norm_num)
theorem B3276773 : Blo 1455547 3276773 := bbase (se 4 (by rfl) ⟨307197, by rfl⟩ : syracuseStep 3276773 = 614395) (by norm_num)
theorem B3686381 : Blo 1455547 3686381 := bbase (se 3 (by rfl) ⟨691196, by rfl⟩ : syracuseStep 3686381 = 1382393) (by norm_num)
theorem B3276881 : Blo 1455547 3276881 := bstep (se 2 (by rfl) ⟨1228830, by rfl⟩ : syracuseStep 3276881 = 2457661) B2457661
theorem B3276899 : Blo 1455547 3276899 := bstep (se 1 (by rfl) ⟨2457674, by rfl⟩ : syracuseStep 3276899 = 4915349) B4915349
theorem B1638499 : Blo 1455547 1638499 := bstep (se 1 (by rfl) ⟨1228874, by rfl⟩ : syracuseStep 1638499 = 2457749) B2457749
theorem B2457715 : Blo 1455547 2457715 := bstep (se 1 (by rfl) ⟨1843286, by rfl⟩ : syracuseStep 2457715 = 3686573) B3686573
theorem B9330821 : Blo 1455547 9330821 := bstep (se 4 (by rfl) ⟨874764, by rfl⟩ : syracuseStep 9330821 = 1749529) B1749529
theorem B2244755 : Blo 1455547 2244755 := bstep (se 1 (by rfl) ⟨1683566, by rfl⟩ : syracuseStep 2244755 = 3367133) B3367133
theorem B4145357 : Blo 1455547 4145357 := bstep (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) B1554509
theorem B1638643 : Blo 1455547 1638643 := bstep (se 1 (by rfl) ⟨1228982, by rfl⟩ : syracuseStep 1638643 = 2457965) B2457965
theorem B2457857 : Blo 1455547 2457857 := bstep (se 2 (by rfl) ⟨921696, by rfl⟩ : syracuseStep 2457857 = 1843393) B1843393
theorem B2105633 : Blo 1455547 2105633 := bstep (se 2 (by rfl) ⟨789612, by rfl⟩ : syracuseStep 2105633 = 1579225) B1579225
theorem B7373105 : Blo 1455547 7373105 := bstep (se 2 (by rfl) ⟨2764914, by rfl⟩ : syracuseStep 7373105 = 5529829) B5529829
theorem B3686705 : Blo 1455547 3686705 := bstep (se 2 (by rfl) ⟨1382514, by rfl⟩ : syracuseStep 3686705 = 2765029) B2765029
theorem B3686755 : Blo 1455547 3686755 := bstep (se 1 (by rfl) ⟨2765066, by rfl⟩ : syracuseStep 3686755 = 5530133) B5530133
theorem B1843555 : Blo 1455547 1843555 := bstep (se 1 (by rfl) ⟨1382666, by rfl⟩ : syracuseStep 1843555 = 2765333) B2765333
theorem B4915565 : Blo 1455547 4915565 := bstep (se 3 (by rfl) ⟨921668, by rfl⟩ : syracuseStep 4915565 = 1843337) B1843337
theorem B3277169 : Blo 1455547 3277169 := bstep (se 2 (by rfl) ⟨1228938, by rfl⟩ : syracuseStep 3277169 = 2457877) B2457877
theorem B2457985 : Blo 1455547 2457985 := bstep (se 2 (by rfl) ⟨921744, by rfl⟩ : syracuseStep 2457985 = 1843489) B1843489
theorem B4145539 : Blo 1455547 4145539 := bstep (se 1 (by rfl) ⟨3109154, by rfl⟩ : syracuseStep 4145539 = 6218309) B6218309
theorem B3277187 : Blo 1455547 3277187 := bstep (se 1 (by rfl) ⟨2457890, by rfl⟩ : syracuseStep 3277187 = 4915781) B4915781
theorem B1638787 : Blo 1455547 1638787 := bstep (se 1 (by rfl) ⟨1229090, by rfl⟩ : syracuseStep 1638787 = 2458181) B2458181
theorem B4915619 : Blo 1455547 4915619 := bstep (se 1 (by rfl) ⟨3686714, by rfl⟩ : syracuseStep 4915619 = 7373429) B7373429
theorem B2458019 : Blo 1455547 2458019 := bstep (se 1 (by rfl) ⟨1843514, by rfl⟩ : syracuseStep 2458019 = 3687029) B3687029
theorem B1843651 : Blo 1455547 1843651 := bstep (se 1 (by rfl) ⟨1382738, by rfl⟩ : syracuseStep 1843651 = 2765477) B2765477
theorem B2073043 : Blo 1455547 2073043 := bstep (se 1 (by rfl) ⟨1554782, by rfl⟩ : syracuseStep 2073043 = 3109565) B3109565
theorem B3686897 : Blo 1455547 3686897 := bstep (se 2 (by rfl) ⟨1382586, by rfl⟩ : syracuseStep 3686897 = 2765173) B2765173
theorem B1638931 : Blo 1455547 1638931 := bstep (se 1 (by rfl) ⟨1229198, by rfl⟩ : syracuseStep 1638931 = 2458397) B2458397
theorem B2458147 : Blo 1455547 2458147 := bstep (se 1 (by rfl) ⟨1843610, by rfl⟩ : syracuseStep 2458147 = 3687221) B3687221
theorem B5251661 : Blo 1455547 5251661 := bstep (se 3 (by rfl) ⟨984686, by rfl⟩ : syracuseStep 5251661 = 1969373) B1969373
theorem B3277457 : Blo 1455547 3277457 := bstep (se 2 (by rfl) ⟨1229046, by rfl⟩ : syracuseStep 3277457 = 2458093) B2458093
theorem B3277475 : Blo 1455547 3277475 := bstep (se 1 (by rfl) ⟨2458106, by rfl⟩ : syracuseStep 3277475 = 4916213) B4916213
theorem B1639075 : Blo 1455547 1639075 := bstep (se 1 (by rfl) ⟨1229306, by rfl⟩ : syracuseStep 1639075 = 2458613) B2458613
theorem B4915889 : Blo 1455547 4915889 := bstep (se 2 (by rfl) ⟨1843458, by rfl⟩ : syracuseStep 4915889 = 3686917) B3686917
theorem B2458289 : Blo 1455547 2458289 := bstep (se 2 (by rfl) ⟨921858, by rfl⟩ : syracuseStep 2458289 = 1843717) B1843717
theorem B6218531 : Blo 1455547 6218531 := bstep (se 1 (by rfl) ⟨4663898, by rfl⟩ : syracuseStep 6218531 = 9327797) B9327797
theorem B2073379 : Blo 1455547 2073379 := bstep (se 1 (by rfl) ⟨1555034, by rfl⟩ : syracuseStep 2073379 = 3110069) B3110069
theorem B2458417 : Blo 1455547 2458417 := bstep (se 2 (by rfl) ⟨921906, by rfl⟩ : syracuseStep 2458417 = 1843813) B1843813
theorem B1639219 : Blo 1455547 1639219 := bstep (se 1 (by rfl) ⟨1229414, by rfl⟩ : syracuseStep 1639219 = 2458829) B2458829
theorem B2458451 : Blo 1455547 2458451 := bstep (se 1 (by rfl) ⟨1843838, by rfl⟩ : syracuseStep 2458451 = 3687677) B3687677
theorem B4146029 : Blo 1455547 4146029 := bstep (se 3 (by rfl) ⟨777380, by rfl⟩ : syracuseStep 4146029 = 1554761) B1554761
theorem B13288333 : Blo 1455547 13288333 := bstep (se 3 (by rfl) ⟨2491562, by rfl⟩ : syracuseStep 13288333 = 4983125) B4983125
theorem B3277745 : Blo 1455547 3277745 := bstep (se 2 (by rfl) ⟨1229154, by rfl⟩ : syracuseStep 3277745 = 2458309) B2458309
theorem B1844147 : Blo 1455547 1844147 := bstep (se 1 (by rfl) ⟨1383110, by rfl⟩ : syracuseStep 1844147 = 2766221) B2766221
theorem B3277763 : Blo 1455547 3277763 := bstep (se 1 (by rfl) ⟨2458322, by rfl⟩ : syracuseStep 3277763 = 4916645) B4916645
theorem B1639363 : Blo 1455547 1639363 := bstep (se 1 (by rfl) ⟨1229522, by rfl⟩ : syracuseStep 1639363 = 2459045) B2459045
theorem B13296581 : Blo 1455547 13296581 := bstep (se 4 (by rfl) ⟨1246554, by rfl⟩ : syracuseStep 13296581 = 2493109) B2493109
theorem B3498961 : Blo 1455547 3498961 := bstep (se 2 (by rfl) ⟨1312110, by rfl⟩ : syracuseStep 3498961 = 2624221) B2624221
theorem B2458579 : Blo 1455547 2458579 := bstep (se 1 (by rfl) ⟨1843934, by rfl⟩ : syracuseStep 2458579 = 3687869) B3687869
theorem B18670661 : Blo 1455547 18670661 := bstep (se 4 (by rfl) ⟨1750374, by rfl⟩ : syracuseStep 18670661 = 3500749) B3500749
theorem B9462853 : Blo 1455547 9462853 := bstep (se 4 (by rfl) ⟨887142, by rfl⟩ : syracuseStep 9462853 = 1774285) B1774285
theorem B1639507 : Blo 1455547 1639507 := bstep (se 1 (by rfl) ⟨1229630, by rfl⟩ : syracuseStep 1639507 = 2459261) B2459261
theorem B2458721 : Blo 1455547 2458721 := bstep (se 2 (by rfl) ⟨922020, by rfl⟩ : syracuseStep 2458721 = 1844041) B1844041
theorem B5530787 : Blo 1455547 5530787 := bstep (se 1 (by rfl) ⟨4148090, by rfl⟩ : syracuseStep 5530787 = 8296181) B8296181
theorem B5530801 : Blo 1455547 5530801 := bstep (se 2 (by rfl) ⟨2074050, by rfl⟩ : syracuseStep 5530801 = 4148101) B4148101
theorem B4916429 : Blo 1455547 4916429 := bstep (se 3 (by rfl) ⟨921830, by rfl⟩ : syracuseStep 4916429 = 1843661) B1843661
theorem B3278033 : Blo 1455547 3278033 := bstep (se 2 (by rfl) ⟨1229262, by rfl⟩ : syracuseStep 3278033 = 2458525) B2458525
theorem B2458849 : Blo 1455547 2458849 := bstep (se 2 (by rfl) ⟨922068, by rfl⟩ : syracuseStep 2458849 = 1844137) B1844137
theorem B8291555 : Blo 1455547 8291555 := bstep (se 1 (by rfl) ⟨6218666, by rfl⟩ : syracuseStep 8291555 = 12437333) B12437333
theorem B3278051 : Blo 1455547 3278051 := bstep (se 1 (by rfl) ⟨2458538, by rfl⟩ : syracuseStep 3278051 = 4917077) B4917077
theorem B1639651 : Blo 1455547 1639651 := bstep (se 1 (by rfl) ⟨1229738, by rfl⟩ : syracuseStep 1639651 = 2459477) B2459477
theorem B4916483 : Blo 1455547 4916483 := bstep (se 1 (by rfl) ⟨3687362, by rfl⟩ : syracuseStep 4916483 = 7374725) B7374725
theorem B2458883 : Blo 1455547 2458883 := bstep (se 1 (by rfl) ⟨1844162, by rfl⟩ : syracuseStep 2458883 = 3688325) B3688325
theorem B2073937 : Blo 1455547 2073937 := bstep (se 2 (by rfl) ⟨777726, by rfl⟩ : syracuseStep 2073937 = 1555453) B1555453
theorem B18654563 : Blo 1455547 18654563 := bstep (se 1 (by rfl) ⟨13990922, by rfl⟩ : syracuseStep 18654563 = 27981845) B27981845
theorem B10495331 : Blo 1455547 10495331 := bstep (se 1 (by rfl) ⟨7871498, by rfl⟩ : syracuseStep 10495331 = 15742997) B15742997
theorem B2073971 : Blo 1455547 2073971 := bstep (se 1 (by rfl) ⟨1555478, by rfl⟩ : syracuseStep 2073971 = 3110957) B3110957
theorem B2459011 : Blo 1455547 2459011 := bstep (se 1 (by rfl) ⟨1844258, by rfl⟩ : syracuseStep 2459011 = 3688517) B3688517
theorem B3687889 : Blo 1455547 3687889 := bstep (se 2 (by rfl) ⟨1382958, by rfl⟩ : syracuseStep 3687889 = 2765917) B2765917
theorem B3278321 : Blo 1455547 3278321 := bstep (se 2 (by rfl) ⟨1229370, by rfl⟩ : syracuseStep 3278321 = 2458741) B2458741
theorem B3278339 : Blo 1455547 3278339 := bstep (se 1 (by rfl) ⟨2458754, by rfl⟩ : syracuseStep 3278339 = 4917509) B4917509
theorem B4916753 : Blo 1455547 4916753 := bstep (se 2 (by rfl) ⟨1843782, by rfl⟩ : syracuseStep 4916753 = 3687565) B3687565
theorem B2459153 : Blo 1455547 2459153 := bstep (se 2 (by rfl) ⟨922182, by rfl⟩ : syracuseStep 2459153 = 1844365) B1844365
theorem B2459281 : Blo 1455547 2459281 := bstep (se 2 (by rfl) ⟨922230, by rfl⟩ : syracuseStep 2459281 = 1844461) B1844461
theorem B2459315 : Blo 1455547 2459315 := bstep (se 1 (by rfl) ⟨1844486, by rfl⟩ : syracuseStep 2459315 = 3688973) B3688973
theorem B2213603 : Blo 1455547 2213603 := bstep (se 1 (by rfl) ⟨1660202, by rfl⟩ : syracuseStep 2213603 = 3320405) B3320405
theorem B7374563 : Blo 1455547 7374563 := bstep (se 1 (by rfl) ⟨5530922, by rfl⟩ : syracuseStep 7374563 = 11061845) B11061845
theorem B3688163 : Blo 1455547 3688163 := bstep (se 1 (by rfl) ⟨2766122, by rfl⟩ : syracuseStep 3688163 = 5532245) B5532245
theorem B3278609 : Blo 1455547 3278609 := bstep (se 2 (by rfl) ⟨1229478, by rfl⟩ : syracuseStep 3278609 = 2458957) B2458957
theorem B3278627 : Blo 1455547 3278627 := bstep (se 1 (by rfl) ⟨2458970, by rfl⟩ : syracuseStep 3278627 = 4917941) B4917941
theorem B2459443 : Blo 1455547 2459443 := bstep (se 1 (by rfl) ⟨1844582, by rfl⟩ : syracuseStep 2459443 = 3689165) B3689165
theorem B2074529 : Blo 1455547 2074529 := bstep (se 2 (by rfl) ⟨777948, by rfl⟩ : syracuseStep 2074529 = 1555897) B1555897
theorem B3688355 : Blo 1455547 3688355 := bstep (se 1 (by rfl) ⟨2766266, by rfl⟩ : syracuseStep 3688355 = 5532533) B5532533
theorem B2459585 : Blo 1455547 2459585 := bstep (se 2 (by rfl) ⟨922344, by rfl⟩ : syracuseStep 2459585 = 1844689) B1844689
theorem B2074609 : Blo 1455547 2074609 := bstep (se 2 (by rfl) ⟨777978, by rfl⟩ : syracuseStep 2074609 = 1555957) B1555957
theorem B4147213 : Blo 1455547 4147213 := bstep (se 3 (by rfl) ⟨777602, by rfl⟩ : syracuseStep 4147213 = 1555205) B1555205
theorem B4917293 : Blo 1455547 4917293 := bstep (se 3 (by rfl) ⟨921992, by rfl⟩ : syracuseStep 4917293 = 1843985) B1843985
theorem B3278897 : Blo 1455547 3278897 := bstep (se 2 (by rfl) ⟨1229586, by rfl⟩ : syracuseStep 3278897 = 2459173) B2459173
theorem B3278915 : Blo 1455547 3278915 := bstep (se 1 (by rfl) ⟨2459186, by rfl⟩ : syracuseStep 3278915 = 4918373) B4918373
theorem B4917347 : Blo 1455547 4917347 := bstep (se 1 (by rfl) ⟨3688010, by rfl⟩ : syracuseStep 4917347 = 7376021) B7376021
theorem B8292557 : Blo 1455547 8292557 := bstep (se 3 (by rfl) ⟨1554854, by rfl⟩ : syracuseStep 8292557 = 3109709) B3109709
theorem B3737827 : Blo 1455547 3737827 := bstep (se 1 (by rfl) ⟨2803370, by rfl⟩ : syracuseStep 3737827 = 5606741) B5606741
theorem B4663565 : Blo 1455547 4663565 := bstep (se 3 (by rfl) ⟨874418, by rfl⟩ : syracuseStep 4663565 = 1748837) B1748837
theorem B2214163 : Blo 1455547 2214163 := bstep (se 1 (by rfl) ⟨1660622, by rfl⟩ : syracuseStep 2214163 = 3321245) B3321245
theorem B3279185 : Blo 1455547 3279185 := bstep (se 2 (by rfl) ⟨1229694, by rfl⟩ : syracuseStep 3279185 = 2459389) B2459389
theorem B3279203 : Blo 1455547 3279203 := bstep (se 1 (by rfl) ⟨2459402, by rfl⟩ : syracuseStep 3279203 = 4918805) B4918805
theorem B7473521 : Blo 1455547 7473521 := bstep (se 2 (by rfl) ⟨2802570, by rfl⟩ : syracuseStep 7473521 = 5605141) B5605141
theorem B4917617 : Blo 1455547 4917617 := bstep (se 2 (by rfl) ⟨1844106, by rfl⟩ : syracuseStep 4917617 = 3688213) B3688213
theorem B2623985 : Blo 1455547 2623985 := bstep (se 2 (by rfl) ⟨983994, by rfl⟩ : syracuseStep 2623985 = 1967989) B1967989
theorem B6220273 : Blo 1455547 6220273 := bstep (se 2 (by rfl) ⟨2332602, by rfl⟩ : syracuseStep 6220273 = 4665205) B4665205
theorem B7375373 : Blo 1455547 7375373 := bstep (se 3 (by rfl) ⟨1382882, by rfl⟩ : syracuseStep 7375373 = 2765765) B2765765
theorem B5532259 : Blo 1455547 5532259 := bstep (se 1 (by rfl) ⟨4149194, by rfl⟩ : syracuseStep 5532259 = 8298389) B8298389
theorem B3279473 : Blo 1455547 3279473 := bstep (se 2 (by rfl) ⟨1229802, by rfl⟩ : syracuseStep 3279473 = 2459605) B2459605
theorem B2214577 : Blo 1455547 2214577 := bstep (se 2 (by rfl) ⟨830466, by rfl⟩ : syracuseStep 2214577 = 1660933) B1660933
theorem B7473869 : Blo 1455547 7473869 := bstep (se 3 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 7473869 = 2802701) B2802701
theorem B4729585 : Blo 1455547 4729585 := bstep (se 2 (by rfl) ⟨1773594, by rfl⟩ : syracuseStep 4729585 = 3547189) B3547189
theorem B19942129 : Blo 1455547 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B4983619 : Blo 1455547 4983619 := bstep (se 1 (by rfl) ⟨3737714, by rfl⟩ : syracuseStep 4983619 = 7475429) B7475429
theorem B3689297 : Blo 1455547 3689297 := bstep (se 2 (by rfl) ⟨1383486, by rfl⟩ : syracuseStep 3689297 = 2766973) B2766973
theorem B3689347 : Blo 1455547 3689347 := bstep (se 1 (by rfl) ⟨2767010, by rfl⟩ : syracuseStep 3689347 = 5534021) B5534021
theorem B8981381 : Blo 1455547 8981381 := bstep (se 4 (by rfl) ⟨842004, by rfl⟩ : syracuseStep 8981381 = 1684009) B1684009
theorem B4918157 : Blo 1455547 4918157 := bstep (se 3 (by rfl) ⟨922154, by rfl⟩ : syracuseStep 4918157 = 1844309) B1844309
theorem B2763715 : Blo 1455547 2763715 := bstep (se 1 (by rfl) ⟨2072786, by rfl⟩ : syracuseStep 2763715 = 4145573) B4145573
theorem B4918211 : Blo 1455547 4918211 := bstep (se 1 (by rfl) ⟨3688658, by rfl⟩ : syracuseStep 4918211 = 7377317) B7377317
theorem B4148273 : Blo 1455547 4148273 := bstep (se 2 (by rfl) ⟨1555602, by rfl⟩ : syracuseStep 4148273 = 3111205) B3111205
theorem B2763875 : Blo 1455547 2763875 := bstep (se 1 (by rfl) ⟨2072906, by rfl⟩ : syracuseStep 2763875 = 4145813) B4145813
theorem B2215027 : Blo 1455547 2215027 := bstep (se 1 (by rfl) ⟨1661270, by rfl⟩ : syracuseStep 2215027 = 3322541) B3322541
theorem B4664461 : Blo 1455547 4664461 := bstep (se 3 (by rfl) ⟨874586, by rfl⟩ : syracuseStep 4664461 = 1749173) B1749173
theorem B4918481 : Blo 1455547 4918481 := bstep (se 2 (by rfl) ⟨1844430, by rfl⟩ : syracuseStep 4918481 = 3688861) B3688861
theorem B18910435 : Blo 1455547 18910435 := bstep (se 1 (by rfl) ⟨14182826, by rfl⟩ : syracuseStep 18910435 = 28365653) B28365653
theorem B4730179 : Blo 1455547 4730179 := bstep (se 1 (by rfl) ⟨3547634, by rfl⟩ : syracuseStep 4730179 = 7095269) B7095269
theorem B7876037 : Blo 1455547 7876037 := bstep (se 4 (by rfl) ⟨738378, by rfl⟩ : syracuseStep 7876037 = 1476757) B1476757
theorem B12439109 : Blo 1455547 12439109 := bstep (se 4 (by rfl) ⟨1166166, by rfl⟩ : syracuseStep 12439109 = 2332333) B2332333
theorem B4148945 : Blo 1455547 4148945 := bstep (se 2 (by rfl) ⟨1555854, by rfl⟩ : syracuseStep 4148945 = 3111709) B3111709
theorem B4919021 : Blo 1455547 4919021 := bstep (se 3 (by rfl) ⟨922316, by rfl⟩ : syracuseStep 4919021 = 1844633) B1844633
theorem B8408837 : Blo 1455547 8408837 := bstep (se 4 (by rfl) ⟨788328, by rfl⟩ : syracuseStep 8408837 = 1576657) B1576657
theorem B2952995 : Blo 1455547 2952995 := bstep (se 1 (by rfl) ⟨2214746, by rfl⟩ : syracuseStep 2952995 = 4429493) B4429493
theorem B4919075 : Blo 1455547 4919075 := bstep (se 1 (by rfl) ⟨3689306, by rfl⟩ : syracuseStep 4919075 = 7378613) B7378613
theorem B50417549 : Blo 1455547 50417549 := bstep (se 3 (by rfl) ⟨9453290, by rfl⟩ : syracuseStep 50417549 = 18906581) B18906581
theorem B2215841 : Blo 1455547 2215841 := bstep (se 2 (by rfl) ⟨830940, by rfl⟩ : syracuseStep 2215841 = 1661881) B1661881
theorem B3108881 : Blo 1455547 3108881 := bstep (se 2 (by rfl) ⟨1165830, by rfl⟩ : syracuseStep 3108881 = 2331661) B2331661
theorem B12447857 : Blo 1455547 12447857 := bstep (se 2 (by rfl) ⟨4667946, by rfl⟩ : syracuseStep 12447857 = 9335893) B9335893
theorem B2764945 : Blo 1455547 2764945 := bstep (se 2 (by rfl) ⟨1036854, by rfl⟩ : syracuseStep 2764945 = 2073709) B2073709
theorem B2183345 : Blo 1455547 2183345 := bstep (se 2 (by rfl) ⟨818754, by rfl⟩ : syracuseStep 2183345 = 1637509) B1637509
theorem B2183363 : Blo 1455547 2183363 := bstep (se 1 (by rfl) ⟨1637522, by rfl⟩ : syracuseStep 2183363 = 3275045) B3275045
theorem B4665539 : Blo 1455547 4665539 := bstep (se 1 (by rfl) ⟨3499154, by rfl⟩ : syracuseStep 4665539 = 6998309) B6998309
theorem B2183393 : Blo 1455547 2183393 := bstep (se 2 (by rfl) ⟨818772, by rfl⟩ : syracuseStep 2183393 = 1637545) B1637545
theorem B2183411 : Blo 1455547 2183411 := bstep (se 1 (by rfl) ⟨1637558, by rfl⟩ : syracuseStep 2183411 = 3275117) B3275117
theorem B2183441 : Blo 1455547 2183441 := bstep (se 2 (by rfl) ⟨818790, by rfl⟩ : syracuseStep 2183441 = 1637581) B1637581
theorem B2183459 : Blo 1455547 2183459 := bstep (se 1 (by rfl) ⟨1637594, by rfl⟩ : syracuseStep 2183459 = 3275189) B3275189
theorem B2183489 : Blo 1455547 2183489 := bstep (se 2 (by rfl) ⟨818808, by rfl⟩ : syracuseStep 2183489 = 1637617) B1637617
theorem B3936593 : Blo 1455547 3936593 := bstep (se 2 (by rfl) ⟨1476222, by rfl⟩ : syracuseStep 3936593 = 2952445) B2952445
theorem B2183507 : Blo 1455547 2183507 := bstep (se 1 (by rfl) ⟨1637630, by rfl⟩ : syracuseStep 2183507 = 3275261) B3275261
theorem B2183537 : Blo 1455547 2183537 := bstep (se 2 (by rfl) ⟨818826, by rfl⟩ : syracuseStep 2183537 = 1637653) B1637653
theorem B2183555 : Blo 1455547 2183555 := bstep (se 1 (by rfl) ⟨1637666, by rfl⟩ : syracuseStep 2183555 = 3275333) B3275333
theorem B6222221 : Blo 1455547 6222221 := bstep (se 3 (by rfl) ⟨1166666, by rfl⟩ : syracuseStep 6222221 = 2333333) B2333333
theorem B2183585 : Blo 1455547 2183585 := bstep (se 2 (by rfl) ⟨818844, by rfl⟩ : syracuseStep 2183585 = 1637689) B1637689
theorem B2183603 : Blo 1455547 2183603 := bstep (se 1 (by rfl) ⟨1637702, by rfl⟩ : syracuseStep 2183603 = 3275405) B3275405
theorem B2183633 : Blo 1455547 2183633 := bstep (se 2 (by rfl) ⟨818862, by rfl⟩ : syracuseStep 2183633 = 1637725) B1637725
theorem B2183651 : Blo 1455547 2183651 := bstep (se 1 (by rfl) ⟨1637738, by rfl⟩ : syracuseStep 2183651 = 3275477) B3275477
theorem B4149731 : Blo 1455547 4149731 := bstep (se 1 (by rfl) ⟨3112298, by rfl⟩ : syracuseStep 4149731 = 6224597) B6224597
theorem B2183681 : Blo 1455547 2183681 := bstep (se 2 (by rfl) ⟨818880, by rfl⟩ : syracuseStep 2183681 = 1637761) B1637761
theorem B2183699 : Blo 1455547 2183699 := bstep (se 1 (by rfl) ⟨1637774, by rfl⟩ : syracuseStep 2183699 = 3275549) B3275549
theorem B2183729 : Blo 1455547 2183729 := bstep (se 2 (by rfl) ⟨818898, by rfl⟩ : syracuseStep 2183729 = 1637797) B1637797
theorem B2183747 : Blo 1455547 2183747 := bstep (se 1 (by rfl) ⟨1637810, by rfl⟩ : syracuseStep 2183747 = 3275621) B3275621
theorem B2183777 : Blo 1455547 2183777 := bstep (se 2 (by rfl) ⟨818916, by rfl⟩ : syracuseStep 2183777 = 1637833) B1637833
theorem B2183795 : Blo 1455547 2183795 := bstep (se 1 (by rfl) ⟨1637846, by rfl⟩ : syracuseStep 2183795 = 3275693) B3275693
theorem B5984909 : Blo 1455547 5984909 := bstep (se 3 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 5984909 = 2244341) B2244341
theorem B2183825 : Blo 1455547 2183825 := bstep (se 2 (by rfl) ⟨818934, by rfl⟩ : syracuseStep 2183825 = 1637869) B1637869
theorem B7369379 : Blo 1455547 7369379 := bstep (se 1 (by rfl) ⟨5527034, by rfl⟩ : syracuseStep 7369379 = 11054069) B11054069
theorem B2183843 : Blo 1455547 2183843 := bstep (se 1 (by rfl) ⟨1637882, by rfl⟩ : syracuseStep 2183843 = 3275765) B3275765
theorem B2183873 : Blo 1455547 2183873 := bstep (se 2 (by rfl) ⟨818952, by rfl⟩ : syracuseStep 2183873 = 1637905) B1637905
theorem B2183891 : Blo 1455547 2183891 := bstep (se 1 (by rfl) ⟨1637918, by rfl⟩ : syracuseStep 2183891 = 3275837) B3275837
theorem B3322595 : Blo 1455547 3322595 := bstep (se 1 (by rfl) ⟨2491946, by rfl⟩ : syracuseStep 3322595 = 4983893) B4983893
theorem B2183921 : Blo 1455547 2183921 := bstep (se 2 (by rfl) ⟨818970, by rfl⟩ : syracuseStep 2183921 = 1637941) B1637941
theorem B2183939 : Blo 1455547 2183939 := bstep (se 1 (by rfl) ⟨1637954, by rfl⟩ : syracuseStep 2183939 = 3275909) B3275909
theorem B35926805 : Blo 1455547 35926805 := bstep (se 6 (by rfl) ⟨842034, by rfl⟩ : syracuseStep 35926805 = 1684069) B1684069
theorem B2183969 : Blo 1455547 2183969 := bstep (se 2 (by rfl) ⟨818988, by rfl⟩ : syracuseStep 2183969 = 1637977) B1637977
theorem B4150061 : Blo 1455547 4150061 := bstep (se 3 (by rfl) ⟨778136, by rfl⟩ : syracuseStep 4150061 = 1556273) B1556273
theorem B2183987 : Blo 1455547 2183987 := bstep (se 1 (by rfl) ⟨1637990, by rfl⟩ : syracuseStep 2183987 = 3275981) B3275981
theorem B17953589 : Blo 1455547 17953589 := bstep (se 5 (by rfl) ⟨841574, by rfl⟩ : syracuseStep 17953589 = 1683149) B1683149
theorem B2184017 : Blo 1455547 2184017 := bstep (se 2 (by rfl) ⟨819006, by rfl⟩ : syracuseStep 2184017 = 1638013) B1638013
theorem B4666193 : Blo 1455547 4666193 := bstep (se 2 (by rfl) ⟨1749822, by rfl⟩ : syracuseStep 4666193 = 3499645) B3499645
theorem B2184035 : Blo 1455547 2184035 := bstep (se 1 (by rfl) ⟨1638026, by rfl⟩ : syracuseStep 2184035 = 3276053) B3276053
theorem B4150129 : Blo 1455547 4150129 := bstep (se 2 (by rfl) ⟨1556298, by rfl⟩ : syracuseStep 4150129 = 3112597) B3112597
theorem B2184065 : Blo 1455547 2184065 := bstep (se 2 (by rfl) ⟨819024, by rfl⟩ : syracuseStep 2184065 = 1638049) B1638049
theorem B11056013 : Blo 1455547 11056013 := bstep (se 3 (by rfl) ⟨2073002, by rfl⟩ : syracuseStep 11056013 = 4146005) B4146005
theorem B2184083 : Blo 1455547 2184083 := bstep (se 1 (by rfl) ⟨1638062, by rfl⟩ : syracuseStep 2184083 = 3276125) B3276125
theorem B2184113 : Blo 1455547 2184113 := bstep (se 2 (by rfl) ⟨819042, by rfl⟩ : syracuseStep 2184113 = 1638085) B1638085
theorem B2184131 : Blo 1455547 2184131 := bstep (se 1 (by rfl) ⟨1638098, by rfl⟩ : syracuseStep 2184131 = 3276197) B3276197
theorem B2184161 : Blo 1455547 2184161 := bstep (se 2 (by rfl) ⟨819060, by rfl⟩ : syracuseStep 2184161 = 1638121) B1638121
theorem B4101101 : Blo 1455547 4101101 := bstep (se 3 (by rfl) ⟨768956, by rfl⟩ : syracuseStep 4101101 = 1537913) B1537913
theorem B2184179 : Blo 1455547 2184179 := bstep (se 1 (by rfl) ⟨1638134, by rfl⟩ : syracuseStep 2184179 = 3276269) B3276269
theorem B2184209 : Blo 1455547 2184209 := bstep (se 2 (by rfl) ⟨819078, by rfl⟩ : syracuseStep 2184209 = 1638157) B1638157
theorem B2331667 : Blo 1455547 2331667 := bstep (se 1 (by rfl) ⟨1748750, by rfl⟩ : syracuseStep 2331667 = 3497501) B3497501
theorem B2184227 : Blo 1455547 2184227 := bstep (se 1 (by rfl) ⟨1638170, by rfl⟩ : syracuseStep 2184227 = 3276341) B3276341
theorem B8295473 : Blo 1455547 8295473 := bstep (se 2 (by rfl) ⟨3110802, by rfl⟩ : syracuseStep 8295473 = 6221605) B6221605
theorem B7877681 : Blo 1455547 7877681 := bstep (se 2 (by rfl) ⟨2954130, by rfl⟩ : syracuseStep 7877681 = 5908261) B5908261
theorem B2184257 : Blo 1455547 2184257 := bstep (se 2 (by rfl) ⟨819096, by rfl⟩ : syracuseStep 2184257 = 1638193) B1638193
theorem B2184275 : Blo 1455547 2184275 := bstep (se 1 (by rfl) ⟨1638206, by rfl⟩ : syracuseStep 2184275 = 3276413) B3276413
theorem B2184305 : Blo 1455547 2184305 := bstep (se 2 (by rfl) ⟨819114, by rfl⟩ : syracuseStep 2184305 = 1638229) B1638229
theorem B2184323 : Blo 1455547 2184323 := bstep (se 1 (by rfl) ⟨1638242, by rfl⟩ : syracuseStep 2184323 = 3276485) B3276485
theorem B4150403 : Blo 1455547 4150403 := bstep (se 1 (by rfl) ⟨3112802, by rfl⟩ : syracuseStep 4150403 = 6225605) B6225605
theorem B2184353 : Blo 1455547 2184353 := bstep (se 2 (by rfl) ⟨819132, by rfl⟩ : syracuseStep 2184353 = 1638265) B1638265
theorem B3110051 : Blo 1455547 3110051 := bstep (se 1 (by rfl) ⟨2332538, by rfl⟩ : syracuseStep 3110051 = 4665077) B4665077
theorem B2766001 : Blo 1455547 2766001 := bstep (se 2 (by rfl) ⟨1037250, by rfl⟩ : syracuseStep 2766001 = 2074501) B2074501
theorem B2184371 : Blo 1455547 2184371 := bstep (se 1 (by rfl) ⟨1638278, by rfl⟩ : syracuseStep 2184371 = 3276557) B3276557
theorem B2184401 : Blo 1455547 2184401 := bstep (se 2 (by rfl) ⟨819150, by rfl⟩ : syracuseStep 2184401 = 1638301) B1638301
theorem B2184419 : Blo 1455547 2184419 := bstep (se 1 (by rfl) ⟨1638314, by rfl⟩ : syracuseStep 2184419 = 3276629) B3276629
theorem B11810033 : Blo 1455547 11810033 := bstep (se 2 (by rfl) ⟨4428762, by rfl⟩ : syracuseStep 11810033 = 8857525) B8857525
theorem B2184449 : Blo 1455547 2184449 := bstep (se 2 (by rfl) ⟨819168, by rfl⟩ : syracuseStep 2184449 = 1638337) B1638337
theorem B2331923 : Blo 1455547 2331923 := bstep (se 1 (by rfl) ⟨1748942, by rfl⟩ : syracuseStep 2331923 = 3497885) B3497885
theorem B2184467 : Blo 1455547 2184467 := bstep (se 1 (by rfl) ⟨1638350, by rfl⟩ : syracuseStep 2184467 = 3276701) B3276701
theorem B2184497 : Blo 1455547 2184497 := bstep (se 2 (by rfl) ⟨819186, by rfl⟩ : syracuseStep 2184497 = 1638373) B1638373
theorem B2184515 : Blo 1455547 2184515 := bstep (se 1 (by rfl) ⟨1638386, by rfl⟩ : syracuseStep 2184515 = 3276773) B3276773
theorem B2184545 : Blo 1455547 2184545 := bstep (se 2 (by rfl) ⟨819204, by rfl⟩ : syracuseStep 2184545 = 1638409) B1638409
theorem B7378289 : Blo 1455547 7378289 := bstep (se 2 (by rfl) ⟨2766858, by rfl⟩ : syracuseStep 7378289 = 5533717) B5533717
theorem B2184563 : Blo 1455547 2184563 := bstep (se 1 (by rfl) ⟨1638422, by rfl⟩ : syracuseStep 2184563 = 3276845) B3276845
theorem B2184593 : Blo 1455547 2184593 := bstep (se 2 (by rfl) ⟨819222, by rfl⟩ : syracuseStep 2184593 = 1638445) B1638445
theorem B2184611 : Blo 1455547 2184611 := bstep (se 1 (by rfl) ⟨1638458, by rfl⟩ : syracuseStep 2184611 = 3276917) B3276917
theorem B2184641 : Blo 1455547 2184641 := bstep (se 2 (by rfl) ⟨819240, by rfl⟩ : syracuseStep 2184641 = 1638481) B1638481
theorem B1455555 : Blo 1455547 1455555 := bstep (se 1 (by rfl) ⟨1091666, by rfl⟩ : syracuseStep 1455555 = 2183333) B2183333
theorem B7370189 : Blo 1455547 7370189 := bstep (se 3 (by rfl) ⟨1381910, by rfl⟩ : syracuseStep 7370189 = 2763821) B2763821
theorem B1455571 : Blo 1455547 1455571 := bstep (se 1 (by rfl) ⟨1091678, by rfl⟩ : syracuseStep 1455571 = 2183357) B2183357
theorem B2184659 : Blo 1455547 2184659 := bstep (se 1 (by rfl) ⟨1638494, by rfl⟩ : syracuseStep 2184659 = 3276989) B3276989
theorem B1455587 : Blo 1455547 1455587 := bstep (se 1 (by rfl) ⟨1091690, by rfl⟩ : syracuseStep 1455587 = 2183381) B2183381
theorem B2184689 : Blo 1455547 2184689 := bstep (se 2 (by rfl) ⟨819258, by rfl⟩ : syracuseStep 2184689 = 1638517) B1638517
theorem B1455603 : Blo 1455547 1455603 := bstep (se 1 (by rfl) ⟨1091702, by rfl⟩ : syracuseStep 1455603 = 2183405) B2183405
theorem B1455619 : Blo 1455547 1455619 := bstep (se 1 (by rfl) ⟨1091714, by rfl⟩ : syracuseStep 1455619 = 2183429) B2183429
theorem B2184707 : Blo 1455547 2184707 := bstep (se 1 (by rfl) ⟨1638530, by rfl⟩ : syracuseStep 2184707 = 3277061) B3277061
theorem B1455635 : Blo 1455547 1455635 := bstep (se 1 (by rfl) ⟨1091726, by rfl⟩ : syracuseStep 1455635 = 2183453) B2183453
theorem B2184737 : Blo 1455547 2184737 := bstep (se 2 (by rfl) ⟨819276, by rfl⟩ : syracuseStep 2184737 = 1638553) B1638553
theorem B1455651 : Blo 1455547 1455651 := bstep (se 1 (by rfl) ⟨1091738, by rfl⟩ : syracuseStep 1455651 = 2183477) B2183477
theorem B1455667 : Blo 1455547 1455667 := bstep (se 1 (by rfl) ⟨1091750, by rfl⟩ : syracuseStep 1455667 = 2183501) B2183501
theorem B2184755 : Blo 1455547 2184755 := bstep (se 1 (by rfl) ⟨1638566, by rfl⟩ : syracuseStep 2184755 = 3277133) B3277133
theorem B1455683 : Blo 1455547 1455683 := bstep (se 1 (by rfl) ⟨1091762, by rfl⟩ : syracuseStep 1455683 = 2183525) B2183525
theorem B2766403 : Blo 1455547 2766403 := bstep (se 1 (by rfl) ⟨2074802, by rfl⟩ : syracuseStep 2766403 = 4149605) B4149605
theorem B2184785 : Blo 1455547 2184785 := bstep (se 2 (by rfl) ⟨819294, by rfl⟩ : syracuseStep 2184785 = 1638589) B1638589
theorem B1455699 : Blo 1455547 1455699 := bstep (se 1 (by rfl) ⟨1091774, by rfl⟩ : syracuseStep 1455699 = 2183549) B2183549
theorem B1455715 : Blo 1455547 1455715 := bstep (se 1 (by rfl) ⟨1091786, by rfl⟩ : syracuseStep 1455715 = 2183573) B2183573
theorem B2184803 : Blo 1455547 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B2766449 : Blo 1455547 2766449 := bstep (se 2 (by rfl) ⟨1037418, by rfl⟩ : syracuseStep 2766449 = 2074837) B2074837
theorem B1455731 : Blo 1455547 1455731 := bstep (se 1 (by rfl) ⟨1091798, by rfl⟩ : syracuseStep 1455731 = 2183597) B2183597
theorem B2184833 : Blo 1455547 2184833 := bstep (se 2 (by rfl) ⟨819312, by rfl⟩ : syracuseStep 2184833 = 1638625) B1638625
theorem B1455747 : Blo 1455547 1455747 := bstep (se 1 (by rfl) ⟨1091810, by rfl⟩ : syracuseStep 1455747 = 2183621) B2183621
theorem B3937933 : Blo 1455547 3937933 := bstep (se 3 (by rfl) ⟨738362, by rfl⟩ : syracuseStep 3937933 = 1476725) B1476725
theorem B1455763 : Blo 1455547 1455763 := bstep (se 1 (by rfl) ⟨1091822, by rfl⟩ : syracuseStep 1455763 = 2183645) B2183645
theorem B2184851 : Blo 1455547 2184851 := bstep (se 1 (by rfl) ⟨1638638, by rfl⟩ : syracuseStep 2184851 = 3277277) B3277277
theorem B1455779 : Blo 1455547 1455779 := bstep (se 1 (by rfl) ⟨1091834, by rfl⟩ : syracuseStep 1455779 = 2183669) B2183669
theorem B5527217 : Blo 1455547 5527217 := bstep (se 2 (by rfl) ⟨2072706, by rfl⟩ : syracuseStep 5527217 = 4145413) B4145413
theorem B2184881 : Blo 1455547 2184881 := bstep (se 2 (by rfl) ⟨819330, by rfl⟩ : syracuseStep 2184881 = 1638661) B1638661
theorem B1455795 : Blo 1455547 1455795 := bstep (se 1 (by rfl) ⟨1091846, by rfl⟩ : syracuseStep 1455795 = 2183693) B2183693
theorem B1455811 : Blo 1455547 1455811 := bstep (se 1 (by rfl) ⟨1091858, by rfl⟩ : syracuseStep 1455811 = 2183717) B2183717
theorem B2184899 : Blo 1455547 2184899 := bstep (se 1 (by rfl) ⟨1638674, by rfl⟩ : syracuseStep 2184899 = 3277349) B3277349
theorem B1455827 : Blo 1455547 1455827 := bstep (se 1 (by rfl) ⟨1091870, by rfl⟩ : syracuseStep 1455827 = 2183741) B2183741
theorem B2332385 : Blo 1455547 2332385 := bstep (se 2 (by rfl) ⟨874644, by rfl⟩ : syracuseStep 2332385 = 1749289) B1749289
theorem B1455843 : Blo 1455547 1455843 := bstep (se 1 (by rfl) ⟨1091882, by rfl⟩ : syracuseStep 1455843 = 2183765) B2183765
theorem B2184929 : Blo 1455547 2184929 := bstep (se 2 (by rfl) ⟨819348, by rfl⟩ : syracuseStep 2184929 = 1638697) B1638697
theorem B1455859 : Blo 1455547 1455859 := bstep (se 1 (by rfl) ⟨1091894, by rfl⟩ : syracuseStep 1455859 = 2183789) B2183789
theorem B2184947 : Blo 1455547 2184947 := bstep (se 1 (by rfl) ⟨1638710, by rfl⟩ : syracuseStep 2184947 = 3277421) B3277421
theorem B2103041 : Blo 1455547 2103041 := bstep (se 2 (by rfl) ⟨788640, by rfl⟩ : syracuseStep 2103041 = 1577281) B1577281
theorem B1455875 : Blo 1455547 1455875 := bstep (se 1 (by rfl) ⟨1091906, by rfl⟩ : syracuseStep 1455875 = 2183813) B2183813
theorem B2184977 : Blo 1455547 2184977 := bstep (se 2 (by rfl) ⟨819366, by rfl⟩ : syracuseStep 2184977 = 1638733) B1638733
theorem B1455891 : Blo 1455547 1455891 := bstep (se 1 (by rfl) ⟨1091918, by rfl⟩ : syracuseStep 1455891 = 2183837) B2183837
theorem B1455907 : Blo 1455547 1455907 := bstep (se 1 (by rfl) ⟨1091930, by rfl⟩ : syracuseStep 1455907 = 2183861) B2183861
theorem B2184995 : Blo 1455547 2184995 := bstep (se 1 (by rfl) ⟨1638746, by rfl⟩ : syracuseStep 2184995 = 3277493) B3277493
theorem B1455923 : Blo 1455547 1455923 := bstep (se 1 (by rfl) ⟨1091942, by rfl⟩ : syracuseStep 1455923 = 2183885) B2183885
theorem B2332481 : Blo 1455547 2332481 := bstep (se 2 (by rfl) ⟨874680, by rfl⟩ : syracuseStep 2332481 = 1749361) B1749361
theorem B2185025 : Blo 1455547 2185025 := bstep (se 2 (by rfl) ⟨819384, by rfl⟩ : syracuseStep 2185025 = 1638769) B1638769
theorem B1455939 : Blo 1455547 1455939 := bstep (se 1 (by rfl) ⟨1091954, by rfl⟩ : syracuseStep 1455939 = 2183909) B2183909
theorem B4912973 : Blo 1455547 4912973 := bstep (se 3 (by rfl) ⟨921182, by rfl⟩ : syracuseStep 4912973 = 1842365) B1842365
theorem B1455955 : Blo 1455547 1455955 := bstep (se 1 (by rfl) ⟨1091966, by rfl⟩ : syracuseStep 1455955 = 2183933) B2183933
theorem B2185043 : Blo 1455547 2185043 := bstep (se 1 (by rfl) ⟨1638782, by rfl⟩ : syracuseStep 2185043 = 3277565) B3277565
theorem B2332513 : Blo 1455547 2332513 := bstep (se 2 (by rfl) ⟨874692, by rfl⟩ : syracuseStep 2332513 = 1749385) B1749385
theorem B1455971 : Blo 1455547 1455971 := bstep (se 1 (by rfl) ⟨1091978, by rfl⟩ : syracuseStep 1455971 = 2183957) B2183957
theorem B2185073 : Blo 1455547 2185073 := bstep (se 2 (by rfl) ⟨819402, by rfl⟩ : syracuseStep 2185073 = 1638805) B1638805
theorem B1455987 : Blo 1455547 1455987 := bstep (se 1 (by rfl) ⟨1091990, by rfl⟩ : syracuseStep 1455987 = 2183981) B2183981
theorem B4913027 : Blo 1455547 4913027 := bstep (se 1 (by rfl) ⟨3684770, by rfl⟩ : syracuseStep 4913027 = 7369541) B7369541
theorem B1456003 : Blo 1455547 1456003 := bstep (se 1 (by rfl) ⟨1092002, by rfl⟩ : syracuseStep 1456003 = 2184005) B2184005
theorem B2185091 : Blo 1455547 2185091 := bstep (se 1 (by rfl) ⟨1638818, by rfl⟩ : syracuseStep 2185091 = 3277637) B3277637
theorem B2766737 : Blo 1455547 2766737 := bstep (se 2 (by rfl) ⟨1037526, by rfl⟩ : syracuseStep 2766737 = 2075053) B2075053
theorem B1456019 : Blo 1455547 1456019 := bstep (se 1 (by rfl) ⟨1092014, by rfl⟩ : syracuseStep 1456019 = 2184029) B2184029
theorem B1660819 : Blo 1455547 1660819 := bstep (se 1 (by rfl) ⟨1245614, by rfl⟩ : syracuseStep 1660819 = 2491229) B2491229
theorem B2185121 : Blo 1455547 2185121 := bstep (se 2 (by rfl) ⟨819420, by rfl⟩ : syracuseStep 2185121 = 1638841) B1638841
theorem B1456035 : Blo 1455547 1456035 := bstep (se 1 (by rfl) ⟨1092026, by rfl⟩ : syracuseStep 1456035 = 2184053) B2184053
theorem B2103203 : Blo 1455547 2103203 := bstep (se 1 (by rfl) ⟨1577402, by rfl⟩ : syracuseStep 2103203 = 3154805) B3154805
theorem B1456051 : Blo 1455547 1456051 := bstep (se 1 (by rfl) ⟨1092038, by rfl⟩ : syracuseStep 1456051 = 2184077) B2184077
theorem B2185139 : Blo 1455547 2185139 := bstep (se 1 (by rfl) ⟨1638854, by rfl⟩ : syracuseStep 2185139 = 3277709) B3277709
theorem B1456067 : Blo 1455547 1456067 := bstep (se 1 (by rfl) ⟨1092050, by rfl⟩ : syracuseStep 1456067 = 2184101) B2184101
theorem B21010373 : Blo 1455547 21010373 := bstep (se 4 (by rfl) ⟨1969722, by rfl⟩ : syracuseStep 21010373 = 3939445) B3939445
theorem B1456083 : Blo 1455547 1456083 := bstep (se 1 (by rfl) ⟨1092062, by rfl⟩ : syracuseStep 1456083 = 2184125) B2184125
theorem B2185169 : Blo 1455547 2185169 := bstep (se 2 (by rfl) ⟨819438, by rfl⟩ : syracuseStep 2185169 = 1638877) B1638877
theorem B1456099 : Blo 1455547 1456099 := bstep (se 1 (by rfl) ⟨1092074, by rfl⟩ : syracuseStep 1456099 = 2184149) B2184149
theorem B2185187 : Blo 1455547 2185187 := bstep (se 1 (by rfl) ⟨1638890, by rfl⟩ : syracuseStep 2185187 = 3277781) B3277781
theorem B18675683 : Blo 1455547 18675683 := bstep (se 1 (by rfl) ⟨14006762, by rfl⟩ : syracuseStep 18675683 = 28013525) B28013525
theorem B1456115 : Blo 1455547 1456115 := bstep (se 1 (by rfl) ⟨1092086, by rfl⟩ : syracuseStep 1456115 = 2184173) B2184173
theorem B2185217 : Blo 1455547 2185217 := bstep (se 2 (by rfl) ⟨819456, by rfl⟩ : syracuseStep 2185217 = 1638913) B1638913
theorem B1456131 : Blo 1455547 1456131 := bstep (se 1 (by rfl) ⟨1092098, by rfl⟩ : syracuseStep 1456131 = 2184197) B2184197
theorem B1456147 : Blo 1455547 1456147 := bstep (se 1 (by rfl) ⟨1092110, by rfl⟩ : syracuseStep 1456147 = 2184221) B2184221
theorem B2185235 : Blo 1455547 2185235 := bstep (se 1 (by rfl) ⟨1638926, by rfl⟩ : syracuseStep 2185235 = 3277853) B3277853
theorem B1456163 : Blo 1455547 1456163 := bstep (se 1 (by rfl) ⟨1092122, by rfl⟩ : syracuseStep 1456163 = 2184245) B2184245
theorem B2185265 : Blo 1455547 2185265 := bstep (se 2 (by rfl) ⟨819474, by rfl⟩ : syracuseStep 2185265 = 1638949) B1638949
theorem B1456179 : Blo 1455547 1456179 := bstep (se 1 (by rfl) ⟨1092134, by rfl⟩ : syracuseStep 1456179 = 2184269) B2184269
theorem B1456195 : Blo 1455547 1456195 := bstep (se 1 (by rfl) ⟨1092146, by rfl⟩ : syracuseStep 1456195 = 2184293) B2184293
theorem B2185283 : Blo 1455547 2185283 := bstep (se 1 (by rfl) ⟨1638962, by rfl⟩ : syracuseStep 2185283 = 3277925) B3277925
theorem B1456211 : Blo 1455547 1456211 := bstep (se 1 (by rfl) ⟨1092158, by rfl⟩ : syracuseStep 1456211 = 2184317) B2184317
theorem B2185313 : Blo 1455547 2185313 := bstep (se 2 (by rfl) ⟨819492, by rfl⟩ : syracuseStep 2185313 = 1638985) B1638985
theorem B1456227 : Blo 1455547 1456227 := bstep (se 1 (by rfl) ⟨1092170, by rfl⟩ : syracuseStep 1456227 = 2184341) B2184341
theorem B1456243 : Blo 1455547 1456243 := bstep (se 1 (by rfl) ⟨1092182, by rfl⟩ : syracuseStep 1456243 = 2184365) B2184365
theorem B2185331 : Blo 1455547 2185331 := bstep (se 1 (by rfl) ⟨1638998, by rfl⟩ : syracuseStep 2185331 = 3277997) B3277997
theorem B1456259 : Blo 1455547 1456259 := bstep (se 1 (by rfl) ⟨1092194, by rfl⟩ : syracuseStep 1456259 = 2184389) B2184389
theorem B4913297 : Blo 1455547 4913297 := bstep (se 2 (by rfl) ⟨1842486, by rfl⟩ : syracuseStep 4913297 = 3684973) B3684973
theorem B2185361 : Blo 1455547 2185361 := bstep (se 2 (by rfl) ⟨819510, by rfl⟩ : syracuseStep 2185361 = 1639021) B1639021
theorem B1456275 : Blo 1455547 1456275 := bstep (se 1 (by rfl) ⟨1092206, by rfl⟩ : syracuseStep 1456275 = 2184413) B2184413
theorem B4667537 : Blo 1455547 4667537 := bstep (se 2 (by rfl) ⟨1750326, by rfl⟩ : syracuseStep 4667537 = 3500653) B3500653
theorem B1456291 : Blo 1455547 1456291 := bstep (se 1 (by rfl) ⟨1092218, by rfl⟩ : syracuseStep 1456291 = 2184437) B2184437
theorem B2185379 : Blo 1455547 2185379 := bstep (se 1 (by rfl) ⟨1639034, by rfl⟩ : syracuseStep 2185379 = 3278069) B3278069
theorem B1456307 : Blo 1455547 1456307 := bstep (se 1 (by rfl) ⟨1092230, by rfl⟩ : syracuseStep 1456307 = 2184461) B2184461
theorem B2185409 : Blo 1455547 2185409 := bstep (se 2 (by rfl) ⟨819528, by rfl⟩ : syracuseStep 2185409 = 1639057) B1639057
theorem B1456323 : Blo 1455547 1456323 := bstep (se 1 (by rfl) ⟨1092242, by rfl⟩ : syracuseStep 1456323 = 2184485) B2184485
theorem B1456339 : Blo 1455547 1456339 := bstep (se 1 (by rfl) ⟨1092254, by rfl⟩ : syracuseStep 1456339 = 2184509) B2184509
theorem B2185427 : Blo 1455547 2185427 := bstep (se 1 (by rfl) ⟨1639070, by rfl⟩ : syracuseStep 2185427 = 3278141) B3278141
theorem B1456355 : Blo 1455547 1456355 := bstep (se 1 (by rfl) ⟨1092266, by rfl⟩ : syracuseStep 1456355 = 2184533) B2184533
theorem B2185457 : Blo 1455547 2185457 := bstep (se 2 (by rfl) ⟨819546, by rfl⟩ : syracuseStep 2185457 = 1639093) B1639093
theorem B1456371 : Blo 1455547 1456371 := bstep (se 1 (by rfl) ⟨1092278, by rfl⟩ : syracuseStep 1456371 = 2184557) B2184557
theorem B1456387 : Blo 1455547 1456387 := bstep (se 1 (by rfl) ⟨1092290, by rfl⟩ : syracuseStep 1456387 = 2184581) B2184581
theorem B2185475 : Blo 1455547 2185475 := bstep (se 1 (by rfl) ⟨1639106, by rfl⟩ : syracuseStep 2185475 = 3278213) B3278213
theorem B13990157 : Blo 1455547 13990157 := bstep (se 3 (by rfl) ⟨2623154, by rfl⟩ : syracuseStep 13990157 = 5246309) B5246309
theorem B1456403 : Blo 1455547 1456403 := bstep (se 1 (by rfl) ⟨1092302, by rfl⟩ : syracuseStep 1456403 = 2184605) B2184605
theorem B2185505 : Blo 1455547 2185505 := bstep (se 2 (by rfl) ⟨819564, by rfl⟩ : syracuseStep 2185505 = 1639129) B1639129
theorem B1456419 : Blo 1455547 1456419 := bstep (se 1 (by rfl) ⟨1092314, by rfl⟩ : syracuseStep 1456419 = 2184629) B2184629
theorem B9337123 : Blo 1455547 9337123 := bstep (se 1 (by rfl) ⟨7002842, by rfl⟩ : syracuseStep 9337123 = 14005685) B14005685
theorem B1456435 : Blo 1455547 1456435 := bstep (se 1 (by rfl) ⟨1092326, by rfl⟩ : syracuseStep 1456435 = 2184653) B2184653
theorem B2185523 : Blo 1455547 2185523 := bstep (se 1 (by rfl) ⟨1639142, by rfl⟩ : syracuseStep 2185523 = 3278285) B3278285
theorem B1456451 : Blo 1455547 1456451 := bstep (se 1 (by rfl) ⟨1092338, by rfl⟩ : syracuseStep 1456451 = 2184677) B2184677
theorem B5527885 : Blo 1455547 5527885 := bstep (se 3 (by rfl) ⟨1036478, by rfl⟩ : syracuseStep 5527885 = 2072957) B2072957
theorem B2185553 : Blo 1455547 2185553 := bstep (se 2 (by rfl) ⟨819582, by rfl⟩ : syracuseStep 2185553 = 1639165) B1639165
theorem B1456467 : Blo 1455547 1456467 := bstep (se 1 (by rfl) ⟨1092350, by rfl⟩ : syracuseStep 1456467 = 2184701) B2184701
theorem B1456483 : Blo 1455547 1456483 := bstep (se 1 (by rfl) ⟨1092362, by rfl⟩ : syracuseStep 1456483 = 2184725) B2184725
theorem B2185571 : Blo 1455547 2185571 := bstep (se 1 (by rfl) ⟨1639178, by rfl⟩ : syracuseStep 2185571 = 3278357) B3278357
theorem B3938669 : Blo 1455547 3938669 := bstep (se 3 (by rfl) ⟨738500, by rfl⟩ : syracuseStep 3938669 = 1477001) B1477001
theorem B1456499 : Blo 1455547 1456499 := bstep (se 1 (by rfl) ⟨1092374, by rfl⟩ : syracuseStep 1456499 = 2184749) B2184749
theorem B2185601 : Blo 1455547 2185601 := bstep (se 2 (by rfl) ⟨819600, by rfl⟩ : syracuseStep 2185601 = 1639201) B1639201
theorem B1456515 : Blo 1455547 1456515 := bstep (se 1 (by rfl) ⟨1092386, by rfl⟩ : syracuseStep 1456515 = 2184773) B2184773
theorem B3275153 : Blo 1455547 3275153 := bstep (se 2 (by rfl) ⟨1228182, by rfl⟩ : syracuseStep 3275153 = 2456365) B2456365
theorem B1456531 : Blo 1455547 1456531 := bstep (se 1 (by rfl) ⟨1092398, by rfl⟩ : syracuseStep 1456531 = 2184797) B2184797
theorem B2185619 : Blo 1455547 2185619 := bstep (se 1 (by rfl) ⟨1639214, by rfl⟩ : syracuseStep 2185619 = 3278429) B3278429
theorem B3275171 : Blo 1455547 3275171 := bstep (se 1 (by rfl) ⟨2456378, by rfl⟩ : syracuseStep 3275171 = 4912757) B4912757
theorem B1456547 : Blo 1455547 1456547 := bstep (se 1 (by rfl) ⟨1092410, by rfl⟩ : syracuseStep 1456547 = 2184821) B2184821
theorem B2185649 : Blo 1455547 2185649 := bstep (se 2 (by rfl) ⟨819618, by rfl⟩ : syracuseStep 2185649 = 1639237) B1639237
theorem B1456563 : Blo 1455547 1456563 := bstep (se 1 (by rfl) ⟨1092422, by rfl⟩ : syracuseStep 1456563 = 2184845) B2184845
theorem B1456579 : Blo 1455547 1456579 := bstep (se 1 (by rfl) ⟨1092434, by rfl⟩ : syracuseStep 1456579 = 2184869) B2184869
theorem B2185667 : Blo 1455547 2185667 := bstep (se 1 (by rfl) ⟨1639250, by rfl⟩ : syracuseStep 2185667 = 3278501) B3278501
theorem B6642125 : Blo 1455547 6642125 := bstep (se 3 (by rfl) ⟨1245398, by rfl⟩ : syracuseStep 6642125 = 2490797) B2490797
theorem B1456595 : Blo 1455547 1456595 := bstep (se 1 (by rfl) ⟨1092446, by rfl⟩ : syracuseStep 1456595 = 2184893) B2184893
theorem B2185697 : Blo 1455547 2185697 := bstep (se 2 (by rfl) ⟨819636, by rfl⟩ : syracuseStep 2185697 = 1639273) B1639273
theorem B1456611 : Blo 1455547 1456611 := bstep (se 1 (by rfl) ⟨1092458, by rfl⟩ : syracuseStep 1456611 = 2184917) B2184917
theorem B8296931 : Blo 1455547 8296931 := bstep (se 1 (by rfl) ⟨6222698, by rfl⟩ : syracuseStep 8296931 = 12445397) B12445397
theorem B7879153 : Blo 1455547 7879153 := bstep (se 2 (by rfl) ⟨2954682, by rfl⟩ : syracuseStep 7879153 = 5909365) B5909365
theorem B1456627 : Blo 1455547 1456627 := bstep (se 1 (by rfl) ⟨1092470, by rfl⟩ : syracuseStep 1456627 = 2184941) B2184941
theorem B2185715 : Blo 1455547 2185715 := bstep (se 1 (by rfl) ⟨1639286, by rfl⟩ : syracuseStep 2185715 = 3278573) B3278573
theorem B1456643 : Blo 1455547 1456643 := bstep (se 1 (by rfl) ⟨1092482, by rfl⟩ : syracuseStep 1456643 = 2184965) B2184965
theorem B6068749 : Blo 1455547 6068749 := bstep (se 3 (by rfl) ⟨1137890, by rfl⟩ : syracuseStep 6068749 = 2275781) B2275781
theorem B2185745 : Blo 1455547 2185745 := bstep (se 2 (by rfl) ⟨819654, by rfl⟩ : syracuseStep 2185745 = 1639309) B1639309
theorem B1456659 : Blo 1455547 1456659 := bstep (se 1 (by rfl) ⟨1092494, by rfl⟩ : syracuseStep 1456659 = 2184989) B2184989
theorem B1456675 : Blo 1455547 1456675 := bstep (se 1 (by rfl) ⟨1092506, by rfl⟩ : syracuseStep 1456675 = 2185013) B2185013
theorem B2185763 : Blo 1455547 2185763 := bstep (se 1 (by rfl) ⟨1639322, by rfl⟩ : syracuseStep 2185763 = 3278645) B3278645
theorem B1456691 : Blo 1455547 1456691 := bstep (se 1 (by rfl) ⟨1092518, by rfl⟩ : syracuseStep 1456691 = 2185037) B2185037
theorem B2185793 : Blo 1455547 2185793 := bstep (se 2 (by rfl) ⟨819672, by rfl⟩ : syracuseStep 2185793 = 1639345) B1639345
theorem B1456707 : Blo 1455547 1456707 := bstep (se 1 (by rfl) ⟨1092530, by rfl⟩ : syracuseStep 1456707 = 2185061) B2185061
theorem B1456723 : Blo 1455547 1456723 := bstep (se 1 (by rfl) ⟨1092542, by rfl⟩ : syracuseStep 1456723 = 2185085) B2185085
theorem B2185811 : Blo 1455547 2185811 := bstep (se 1 (by rfl) ⟨1639358, by rfl⟩ : syracuseStep 2185811 = 3278717) B3278717
theorem B1456739 : Blo 1455547 1456739 := bstep (se 1 (by rfl) ⟨1092554, by rfl⟩ : syracuseStep 1456739 = 2185109) B2185109
theorem B2185841 : Blo 1455547 2185841 := bstep (se 2 (by rfl) ⟨819690, by rfl⟩ : syracuseStep 2185841 = 1639381) B1639381
theorem B1456755 : Blo 1455547 1456755 := bstep (se 1 (by rfl) ⟨1092566, by rfl⟩ : syracuseStep 1456755 = 2185133) B2185133
theorem B1456771 : Blo 1455547 1456771 := bstep (se 1 (by rfl) ⟨1092578, by rfl⟩ : syracuseStep 1456771 = 2185157) B2185157
theorem B2185859 : Blo 1455547 2185859 := bstep (se 1 (by rfl) ⟨1639394, by rfl⟩ : syracuseStep 2185859 = 3278789) B3278789
theorem B1456787 : Blo 1455547 1456787 := bstep (se 1 (by rfl) ⟨1092590, by rfl⟩ : syracuseStep 1456787 = 2185181) B2185181
theorem B2185889 : Blo 1455547 2185889 := bstep (se 2 (by rfl) ⟨819708, by rfl⟩ : syracuseStep 2185889 = 1639417) B1639417
theorem B1456803 : Blo 1455547 1456803 := bstep (se 1 (by rfl) ⟨1092602, by rfl⟩ : syracuseStep 1456803 = 2185205) B2185205
theorem B8862371 : Blo 1455547 8862371 := bstep (se 1 (by rfl) ⟨6646778, by rfl⟩ : syracuseStep 8862371 = 13293557) B13293557
theorem B4913837 : Blo 1455547 4913837 := bstep (se 3 (by rfl) ⟨921344, by rfl⟩ : syracuseStep 4913837 = 1842689) B1842689
theorem B3275441 : Blo 1455547 3275441 := bstep (se 2 (by rfl) ⟨1228290, by rfl⟩ : syracuseStep 3275441 = 2456581) B2456581
theorem B1456819 : Blo 1455547 1456819 := bstep (se 1 (by rfl) ⟨1092614, by rfl⟩ : syracuseStep 1456819 = 2185229) B2185229
theorem B2185907 : Blo 1455547 2185907 := bstep (se 1 (by rfl) ⟨1639430, by rfl⟩ : syracuseStep 2185907 = 3278861) B3278861
theorem B2456257 : Blo 1455547 2456257 := bstep (se 2 (by rfl) ⟨921096, by rfl⟩ : syracuseStep 2456257 = 1842193) B1842193
theorem B3275459 : Blo 1455547 3275459 := bstep (se 1 (by rfl) ⟨2456594, by rfl⟩ : syracuseStep 3275459 = 4913189) B4913189
theorem B1456835 : Blo 1455547 1456835 := bstep (se 1 (by rfl) ⟨1092626, by rfl⟩ : syracuseStep 1456835 = 2185253) B2185253
theorem B2185937 : Blo 1455547 2185937 := bstep (se 2 (by rfl) ⟨819726, by rfl⟩ : syracuseStep 2185937 = 1639453) B1639453
theorem B1456851 : Blo 1455547 1456851 := bstep (se 1 (by rfl) ⟨1092638, by rfl⟩ : syracuseStep 1456851 = 2185277) B2185277
theorem B2456291 : Blo 1455547 2456291 := bstep (se 1 (by rfl) ⟨1842218, by rfl⟩ : syracuseStep 2456291 = 3684437) B3684437
theorem B4913891 : Blo 1455547 4913891 := bstep (se 1 (by rfl) ⟨3685418, by rfl⟩ : syracuseStep 4913891 = 7370837) B7370837
theorem B1456867 : Blo 1455547 1456867 := bstep (se 1 (by rfl) ⟨1092650, by rfl⟩ : syracuseStep 1456867 = 2185301) B2185301
theorem B2185955 : Blo 1455547 2185955 := bstep (se 1 (by rfl) ⟨1639466, by rfl⟩ : syracuseStep 2185955 = 3278933) B3278933
theorem B1456883 : Blo 1455547 1456883 := bstep (se 1 (by rfl) ⟨1092662, by rfl⟩ : syracuseStep 1456883 = 2185325) B2185325
theorem B2185985 : Blo 1455547 2185985 := bstep (se 2 (by rfl) ⟨819744, by rfl⟩ : syracuseStep 2185985 = 1639489) B1639489
theorem B1456899 : Blo 1455547 1456899 := bstep (se 1 (by rfl) ⟨1092674, by rfl⟩ : syracuseStep 1456899 = 2185349) B2185349
theorem B1456915 : Blo 1455547 1456915 := bstep (se 1 (by rfl) ⟨1092686, by rfl⟩ : syracuseStep 1456915 = 2185373) B2185373
theorem B2186003 : Blo 1455547 2186003 := bstep (se 1 (by rfl) ⟨1639502, by rfl⟩ : syracuseStep 2186003 = 3279005) B3279005
theorem B1456931 : Blo 1455547 1456931 := bstep (se 1 (by rfl) ⟨1092698, by rfl⟩ : syracuseStep 1456931 = 2185397) B2185397
theorem B2186033 : Blo 1455547 2186033 := bstep (se 2 (by rfl) ⟨819762, by rfl⟩ : syracuseStep 2186033 = 1639525) B1639525
theorem B1456947 : Blo 1455547 1456947 := bstep (se 1 (by rfl) ⟨1092710, by rfl⟩ : syracuseStep 1456947 = 2185421) B2185421
theorem B1456963 : Blo 1455547 1456963 := bstep (se 1 (by rfl) ⟨1092722, by rfl⟩ : syracuseStep 1456963 = 2185445) B2185445
theorem B2186051 : Blo 1455547 2186051 := bstep (se 1 (by rfl) ⟨1639538, by rfl⟩ : syracuseStep 2186051 = 3279077) B3279077
theorem B1456979 : Blo 1455547 1456979 := bstep (se 1 (by rfl) ⟨1092734, by rfl⟩ : syracuseStep 1456979 = 2185469) B2185469
theorem B2186081 : Blo 1455547 2186081 := bstep (se 2 (by rfl) ⟨819780, by rfl⟩ : syracuseStep 2186081 = 1639561) B1639561
theorem B2456419 : Blo 1455547 2456419 := bstep (se 1 (by rfl) ⟨1842314, by rfl⟩ : syracuseStep 2456419 = 3684629) B3684629
theorem B1456995 : Blo 1455547 1456995 := bstep (se 1 (by rfl) ⟨1092746, by rfl⟩ : syracuseStep 1456995 = 2185493) B2185493
theorem B4979569 : Blo 1455547 4979569 := bstep (se 2 (by rfl) ⟨1867338, by rfl⟩ : syracuseStep 4979569 = 3734677) B3734677
theorem B1457011 : Blo 1455547 1457011 := bstep (se 1 (by rfl) ⟨1092758, by rfl⟩ : syracuseStep 1457011 = 2185517) B2185517
theorem B2186099 : Blo 1455547 2186099 := bstep (se 1 (by rfl) ⟨1639574, by rfl⟩ : syracuseStep 2186099 = 3279149) B3279149
theorem B1457027 : Blo 1455547 1457027 := bstep (se 1 (by rfl) ⟨1092770, by rfl⟩ : syracuseStep 1457027 = 2185541) B2185541
theorem B2186129 : Blo 1455547 2186129 := bstep (se 2 (by rfl) ⟨819798, by rfl⟩ : syracuseStep 2186129 = 1639597) B1639597
theorem B1457043 : Blo 1455547 1457043 := bstep (se 1 (by rfl) ⟨1092782, by rfl⟩ : syracuseStep 1457043 = 2185565) B2185565
theorem B1457059 : Blo 1455547 1457059 := bstep (se 1 (by rfl) ⟨1092794, by rfl⟩ : syracuseStep 1457059 = 2185589) B2185589
theorem B2186147 : Blo 1455547 2186147 := bstep (se 1 (by rfl) ⟨1639610, by rfl⟩ : syracuseStep 2186147 = 3279221) B3279221
theorem B3685297 : Blo 1455547 3685297 := bstep (se 2 (by rfl) ⟨1381986, by rfl⟩ : syracuseStep 3685297 = 2763973) B2763973
theorem B1457075 : Blo 1455547 1457075 := bstep (se 1 (by rfl) ⟨1092806, by rfl⟩ : syracuseStep 1457075 = 2185613) B2185613
theorem B2186177 : Blo 1455547 2186177 := bstep (se 2 (by rfl) ⟨819816, by rfl⟩ : syracuseStep 2186177 = 1639633) B1639633
theorem B1457091 : Blo 1455547 1457091 := bstep (se 1 (by rfl) ⟨1092818, by rfl⟩ : syracuseStep 1457091 = 2185637) B2185637
theorem B3275729 : Blo 1455547 3275729 := bstep (se 2 (by rfl) ⟨1228398, by rfl⟩ : syracuseStep 3275729 = 2456797) B2456797
theorem B1457107 : Blo 1455547 1457107 := bstep (se 1 (by rfl) ⟨1092830, by rfl⟩ : syracuseStep 1457107 = 2185661) B2185661
theorem B2186195 : Blo 1455547 2186195 := bstep (se 1 (by rfl) ⟨1639646, by rfl⟩ : syracuseStep 2186195 = 3279293) B3279293
theorem B3275747 : Blo 1455547 3275747 := bstep (se 1 (by rfl) ⟨2456810, by rfl⟩ : syracuseStep 3275747 = 4913621) B4913621
theorem B1457123 : Blo 1455547 1457123 := bstep (se 1 (by rfl) ⟨1092842, by rfl⟩ : syracuseStep 1457123 = 2185685) B2185685
theorem B2456561 : Blo 1455547 2456561 := bstep (se 2 (by rfl) ⟨921210, by rfl⟩ : syracuseStep 2456561 = 1842421) B1842421
theorem B4914161 : Blo 1455547 4914161 := bstep (se 2 (by rfl) ⟨1842810, by rfl⟩ : syracuseStep 4914161 = 3685621) B3685621
theorem B1457139 : Blo 1455547 1457139 := bstep (se 1 (by rfl) ⟨1092854, by rfl⟩ : syracuseStep 1457139 = 2185709) B2185709
theorem B2186225 : Blo 1455547 2186225 := bstep (se 2 (by rfl) ⟨819834, by rfl⟩ : syracuseStep 2186225 = 1639669) B1639669
theorem B1457155 : Blo 1455547 1457155 := bstep (se 1 (by rfl) ⟨1092866, by rfl⟩ : syracuseStep 1457155 = 2185733) B2185733
theorem B2186243 : Blo 1455547 2186243 := bstep (se 1 (by rfl) ⟨1639682, by rfl⟩ : syracuseStep 2186243 = 3279365) B3279365
theorem B1457171 : Blo 1455547 1457171 := bstep (se 1 (by rfl) ⟨1092878, by rfl⟩ : syracuseStep 1457171 = 2185757) B2185757
theorem B1457187 : Blo 1455547 1457187 := bstep (se 1 (by rfl) ⟨1092890, by rfl⟩ : syracuseStep 1457187 = 2185781) B2185781
theorem B2186273 : Blo 1455547 2186273 := bstep (se 2 (by rfl) ⟨819852, by rfl⟩ : syracuseStep 2186273 = 1639705) B1639705
theorem B1457203 : Blo 1455547 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B2186291 : Blo 1455547 2186291 := bstep (se 1 (by rfl) ⟨1639718, by rfl⟩ : syracuseStep 2186291 = 3279437) B3279437
theorem B1457219 : Blo 1455547 1457219 := bstep (se 1 (by rfl) ⟨1092914, by rfl⟩ : syracuseStep 1457219 = 2185829) B2185829
theorem B2186321 : Blo 1455547 2186321 := bstep (se 2 (by rfl) ⟨819870, by rfl⟩ : syracuseStep 2186321 = 1639741) B1639741
theorem B1842259 : Blo 1455547 1842259 := bstep (se 1 (by rfl) ⟨1381694, by rfl⟩ : syracuseStep 1842259 = 2763389) B2763389
theorem B1457235 : Blo 1455547 1457235 := bstep (se 1 (by rfl) ⟨1092926, by rfl⟩ : syracuseStep 1457235 = 2185853) B2185853
theorem B5528675 : Blo 1455547 5528675 := bstep (se 1 (by rfl) ⟨4146506, by rfl⟩ : syracuseStep 5528675 = 8293013) B8293013
theorem B1457251 : Blo 1455547 1457251 := bstep (se 1 (by rfl) ⟨1092938, by rfl⟩ : syracuseStep 1457251 = 2185877) B2185877
theorem B3939437 : Blo 1455547 3939437 := bstep (se 3 (by rfl) ⟨738644, by rfl⟩ : syracuseStep 3939437 = 1477289) B1477289
theorem B2456689 : Blo 1455547 2456689 := bstep (se 2 (by rfl) ⟨921258, by rfl⟩ : syracuseStep 2456689 = 1842517) B1842517
theorem B1637491 : Blo 1455547 1637491 := bstep (se 1 (by rfl) ⟨1228118, by rfl⟩ : syracuseStep 1637491 = 2456237) B2456237
theorem B1457267 : Blo 1455547 1457267 := bstep (se 1 (by rfl) ⟨1092950, by rfl⟩ : syracuseStep 1457267 = 2185901) B2185901
theorem B3112067 : Blo 1455547 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B1457283 : Blo 1455547 1457283 := bstep (se 1 (by rfl) ⟨1092962, by rfl⟩ : syracuseStep 1457283 = 2185925) B2185925
theorem B5053585 : Blo 1455547 5053585 := bstep (se 2 (by rfl) ⟨1895094, by rfl⟩ : syracuseStep 5053585 = 3790189) B3790189
theorem B2456723 : Blo 1455547 2456723 := bstep (se 1 (by rfl) ⟨1842542, by rfl⟩ : syracuseStep 2456723 = 3685085) B3685085
theorem B1457299 : Blo 1455547 1457299 := bstep (se 1 (by rfl) ⟨1092974, by rfl⟩ : syracuseStep 1457299 = 2185949) B2185949
theorem B1457315 : Blo 1455547 1457315 := bstep (se 1 (by rfl) ⟨1092986, by rfl⟩ : syracuseStep 1457315 = 2185973) B2185973
theorem B4201649 : Blo 1455547 4201649 := bstep (se 2 (by rfl) ⟨1575618, by rfl⟩ : syracuseStep 4201649 = 3151237) B3151237
theorem B1842355 : Blo 1455547 1842355 := bstep (se 1 (by rfl) ⟨1381766, by rfl⟩ : syracuseStep 1842355 = 2763533) B2763533
theorem B1457331 : Blo 1455547 1457331 := bstep (se 1 (by rfl) ⟨1092998, by rfl⟩ : syracuseStep 1457331 = 2185997) B2185997
theorem B3685571 : Blo 1455547 3685571 := bstep (se 1 (by rfl) ⟨2764178, by rfl⟩ : syracuseStep 3685571 = 5528357) B5528357
theorem B1457347 : Blo 1455547 1457347 := bstep (se 1 (by rfl) ⟨1093010, by rfl⟩ : syracuseStep 1457347 = 2186021) B2186021
theorem B1457363 : Blo 1455547 1457363 := bstep (se 1 (by rfl) ⟨1093022, by rfl⟩ : syracuseStep 1457363 = 2186045) B2186045
theorem B1457379 : Blo 1455547 1457379 := bstep (se 1 (by rfl) ⟨1093034, by rfl⟩ : syracuseStep 1457379 = 2186069) B2186069
theorem B4668653 : Blo 1455547 4668653 := bstep (se 3 (by rfl) ⟨875372, by rfl⟩ : syracuseStep 4668653 = 1750745) B1750745
theorem B3276017 : Blo 1455547 3276017 := bstep (se 2 (by rfl) ⟨1228506, by rfl⟩ : syracuseStep 3276017 = 2457013) B2457013
theorem B1457395 : Blo 1455547 1457395 := bstep (se 1 (by rfl) ⟨1093046, by rfl⟩ : syracuseStep 1457395 = 2186093) B2186093
theorem B1637635 : Blo 1455547 1637635 := bstep (se 1 (by rfl) ⟨1228226, by rfl⟩ : syracuseStep 1637635 = 2456453) B2456453
theorem B3276035 : Blo 1455547 3276035 := bstep (se 1 (by rfl) ⟨2457026, by rfl⟩ : syracuseStep 3276035 = 4914053) B4914053
theorem B1457411 : Blo 1455547 1457411 := bstep (se 1 (by rfl) ⟨1093058, by rfl⟩ : syracuseStep 1457411 = 2186117) B2186117
theorem B9338125 : Blo 1455547 9338125 := bstep (se 3 (by rfl) ⟨1750898, by rfl⟩ : syracuseStep 9338125 = 3501797) B3501797
theorem B2456851 : Blo 1455547 2456851 := bstep (se 1 (by rfl) ⟨1842638, by rfl⟩ : syracuseStep 2456851 = 3685277) B3685277
theorem B1457427 : Blo 1455547 1457427 := bstep (se 1 (by rfl) ⟨1093070, by rfl⟩ : syracuseStep 1457427 = 2186141) B2186141
theorem B1457443 : Blo 1455547 1457443 := bstep (se 1 (by rfl) ⟨1093082, by rfl⟩ : syracuseStep 1457443 = 2186165) B2186165
theorem B3939619 : Blo 1455547 3939619 := bstep (se 1 (by rfl) ⟨2954714, by rfl⟩ : syracuseStep 3939619 = 5909429) B5909429
theorem B7093553 : Blo 1455547 7093553 := bstep (se 2 (by rfl) ⟨2660082, by rfl⟩ : syracuseStep 7093553 = 5320165) B5320165
theorem B1457459 : Blo 1455547 1457459 := bstep (se 1 (by rfl) ⟨1093094, by rfl⟩ : syracuseStep 1457459 = 2186189) B2186189
theorem B1457475 : Blo 1455547 1457475 := bstep (se 1 (by rfl) ⟨1093106, by rfl⟩ : syracuseStep 1457475 = 2186213) B2186213
theorem B1457491 : Blo 1455547 1457491 := bstep (se 1 (by rfl) ⟨1093118, by rfl⟩ : syracuseStep 1457491 = 2186237) B2186237
theorem B1457507 : Blo 1455547 1457507 := bstep (se 1 (by rfl) ⟨1093130, by rfl⟩ : syracuseStep 1457507 = 2186261) B2186261
theorem B1457523 : Blo 1455547 1457523 := bstep (se 1 (by rfl) ⟨1093142, by rfl⟩ : syracuseStep 1457523 = 2186285) B2186285
theorem B3497347 : Blo 1455547 3497347 := bstep (se 1 (by rfl) ⟨2623010, by rfl⟩ : syracuseStep 3497347 = 5246021) B5246021
theorem B3685763 : Blo 1455547 3685763 := bstep (se 1 (by rfl) ⟨2764322, by rfl⟩ : syracuseStep 3685763 = 5528645) B5528645
theorem B1457539 : Blo 1455547 1457539 := bstep (se 1 (by rfl) ⟨1093154, by rfl⟩ : syracuseStep 1457539 = 2186309) B2186309
theorem B1637779 : Blo 1455547 1637779 := bstep (se 1 (by rfl) ⟨1228334, by rfl⟩ : syracuseStep 1637779 = 2456669) B2456669
theorem B2456993 : Blo 1455547 2456993 := bstep (se 2 (by rfl) ⟨921372, by rfl⟩ : syracuseStep 2456993 = 1842745) B1842745
theorem B42589637 : Blo 1455547 42589637 := bstep (se 4 (by rfl) ⟨3992778, by rfl⟩ : syracuseStep 42589637 = 7985557) B7985557
theorem B2334179 : Blo 1455547 2334179 := bstep (se 1 (by rfl) ⟨1750634, by rfl⟩ : syracuseStep 2334179 = 3501269) B3501269
theorem B8855045 : Blo 1455547 8855045 := bstep (se 4 (by rfl) ⟨830160, by rfl⟩ : syracuseStep 8855045 = 1660321) B1660321
theorem B4914701 : Blo 1455547 4914701 := bstep (se 3 (by rfl) ⟨921506, by rfl⟩ : syracuseStep 4914701 = 1843013) B1843013
theorem B3276305 : Blo 1455547 3276305 := bstep (se 2 (by rfl) ⟨1228614, by rfl⟩ : syracuseStep 3276305 = 2457229) B2457229
theorem B2457121 : Blo 1455547 2457121 := bstep (se 2 (by rfl) ⟨921420, by rfl⟩ : syracuseStep 2457121 = 1842841) B1842841
theorem B1637923 : Blo 1455547 1637923 := bstep (se 1 (by rfl) ⟨1228442, by rfl⟩ : syracuseStep 1637923 = 2456885) B2456885
theorem B3276323 : Blo 1455547 3276323 := bstep (se 1 (by rfl) ⟨2457242, by rfl⟩ : syracuseStep 3276323 = 4914485) B4914485
theorem B2457155 : Blo 1455547 2457155 := bstep (se 1 (by rfl) ⟨1842866, by rfl⟩ : syracuseStep 2457155 = 3685733) B3685733
theorem B4914755 : Blo 1455547 4914755 := bstep (se 1 (by rfl) ⟨3686066, by rfl⟩ : syracuseStep 4914755 = 7372133) B7372133
theorem B4259441 : Blo 1455547 4259441 := bstep (se 2 (by rfl) ⟨1597290, by rfl⟩ : syracuseStep 4259441 = 3194581) B3194581
theorem B1842851 : Blo 1455547 1842851 := bstep (se 1 (by rfl) ⟨1382138, by rfl⟩ : syracuseStep 1842851 = 2764277) B2764277
theorem B5250737 : Blo 1455547 5250737 := bstep (se 2 (by rfl) ⟨1969026, by rfl⟩ : syracuseStep 5250737 = 3938053) B3938053
theorem B1638067 : Blo 1455547 1638067 := bstep (se 1 (by rfl) ⟨1228550, by rfl⟩ : syracuseStep 1638067 = 2457101) B2457101
theorem B2457283 : Blo 1455547 2457283 := bstep (se 1 (by rfl) ⟨1842962, by rfl⟩ : syracuseStep 2457283 = 3685925) B3685925
theorem B5529329 : Blo 1455547 5529329 := bstep (se 2 (by rfl) ⟨2073498, by rfl⟩ : syracuseStep 5529329 = 4146997) B4146997
theorem B11058929 : Blo 1455547 11058929 := bstep (se 2 (by rfl) ⟨4147098, by rfl⟩ : syracuseStep 11058929 = 8294197) B8294197
theorem B18669325 : Blo 1455547 18669325 := bstep (se 3 (by rfl) ⟨3500498, by rfl⟩ : syracuseStep 18669325 = 7000997) B7000997
theorem B3989293 : Blo 1455547 3989293 := bstep (se 3 (by rfl) ⟨747992, by rfl⟩ : syracuseStep 3989293 = 1495985) B1495985
theorem B8290097 : Blo 1455547 8290097 := bstep (se 2 (by rfl) ⟨3108786, by rfl⟩ : syracuseStep 8290097 = 6217573) B6217573
theorem B3276593 : Blo 1455547 3276593 := bstep (se 2 (by rfl) ⟨1228722, by rfl⟩ : syracuseStep 3276593 = 2457445) B2457445
theorem B5250865 : Blo 1455547 5250865 := bstep (se 2 (by rfl) ⟨1969074, by rfl⟩ : syracuseStep 5250865 = 3938149) B3938149
theorem B1638211 : Blo 1455547 1638211 := bstep (se 1 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 1638211 = 2457317) B2457317
theorem B3276611 : Blo 1455547 3276611 := bstep (se 1 (by rfl) ⟨2457458, by rfl⟩ : syracuseStep 3276611 = 4914917) B4914917
theorem B10100557 : Blo 1455547 10100557 := bstep (se 3 (by rfl) ⟨1893854, by rfl⟩ : syracuseStep 10100557 = 3787709) B3787709
theorem B2457425 : Blo 1455547 2457425 := bstep (se 2 (by rfl) ⟨921534, by rfl⟩ : syracuseStep 2457425 = 1843069) B1843069
theorem B4915025 : Blo 1455547 4915025 := bstep (se 2 (by rfl) ⟨1843134, by rfl⟩ : syracuseStep 4915025 = 3686269) B3686269
theorem B2072513 : Blo 1455547 2072513 := bstep (se 2 (by rfl) ⟨777192, by rfl⟩ : syracuseStep 2072513 = 1554385) B1554385
theorem B2457553 : Blo 1455547 2457553 := bstep (se 2 (by rfl) ⟨921582, by rfl⟩ : syracuseStep 2457553 = 1843165) B1843165
theorem B1638355 : Blo 1455547 1638355 := bstep (se 1 (by rfl) ⟨1228766, by rfl⟩ : syracuseStep 1638355 = 2457533) B2457533
theorem B2334691 : Blo 1455547 2334691 := bstep (se 1 (by rfl) ⟨1751018, by rfl⟩ : syracuseStep 2334691 = 3502037) B3502037
theorem B2457587 : Blo 1455547 2457587 := bstep (se 1 (by rfl) ⟨1843190, by rfl⟩ : syracuseStep 2457587 = 3686381) B3686381
theorem B5529617 : Blo 1455547 5529617 := bstep (se 2 (by rfl) ⟨2073606, by rfl⟩ : syracuseStep 5529617 = 4147213) B4147213
theorem B8290349 : Blo 1455547 8290349 := bstep (se 3 (by rfl) ⟨1554440, by rfl⟩ : syracuseStep 8290349 = 3108881) B3108881
theorem B8298571 : Blo 1455547 8298571 := bstep (se 1 (by rfl) ⟨6223928, by rfl⟩ : syracuseStep 8298571 = 12447857) B12447857
theorem B3276953 : Blo 1455547 3276953 := bstep (se 2 (by rfl) ⟨1228857, by rfl⟩ : syracuseStep 3276953 = 2457715) B2457715
theorem B1638571 : Blo 1455547 1638571 := bstep (se 1 (by rfl) ⟨1228928, by rfl⟩ : syracuseStep 1638571 = 2457857) B2457857
theorem B3686593 : Blo 1455547 3686593 := bstep (se 2 (by rfl) ⟨1382472, by rfl⟩ : syracuseStep 3686593 = 2764945) B2764945
theorem B4915403 : Blo 1455547 4915403 := bstep (se 1 (by rfl) ⟨3686552, by rfl⟩ : syracuseStep 4915403 = 7373105) B7373105
theorem B2457803 : Blo 1455547 2457803 := bstep (se 1 (by rfl) ⟨1843352, by rfl⟩ : syracuseStep 2457803 = 3686705) B3686705
theorem B3277043 : Blo 1455547 3277043 := bstep (se 1 (by rfl) ⟨2457782, by rfl⟩ : syracuseStep 3277043 = 4915565) B4915565
theorem B3277079 : Blo 1455547 3277079 := bstep (se 1 (by rfl) ⟨2457809, by rfl⟩ : syracuseStep 3277079 = 4915619) B4915619
theorem B1638679 : Blo 1455547 1638679 := bstep (se 1 (by rfl) ⟨1229009, by rfl⟩ : syracuseStep 1638679 = 2458019) B2458019
theorem B2457931 : Blo 1455547 2457931 := bstep (se 1 (by rfl) ⟨1843448, by rfl⟩ : syracuseStep 2457931 = 3686897) B3686897
theorem B8298845 : Blo 1455547 8298845 := bstep (se 3 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 8298845 = 3112067) B3112067
theorem B3989939 : Blo 1455547 3989939 := bstep (se 1 (by rfl) ⟨2992454, by rfl⟩ : syracuseStep 3989939 = 5984909) B5984909
theorem B3277259 : Blo 1455547 3277259 := bstep (se 1 (by rfl) ⟨2457944, by rfl⟩ : syracuseStep 3277259 = 4915889) B4915889
theorem B1638859 : Blo 1455547 1638859 := bstep (se 1 (by rfl) ⟨1229144, by rfl⟩ : syracuseStep 1638859 = 2458289) B2458289
theorem B4915673 : Blo 1455547 4915673 := bstep (se 2 (by rfl) ⟨1843377, by rfl⟩ : syracuseStep 4915673 = 3686755) B3686755
theorem B2458073 : Blo 1455547 2458073 := bstep (se 2 (by rfl) ⟨921777, by rfl⟩ : syracuseStep 2458073 = 1843555) B1843555
theorem B3277313 : Blo 1455547 3277313 := bstep (se 2 (by rfl) ⟨1228992, by rfl⟩ : syracuseStep 3277313 = 2457985) B2457985
theorem B4145687 : Blo 1455547 4145687 := bstep (se 1 (by rfl) ⟨3109265, by rfl⟩ : syracuseStep 4145687 = 6218531) B6218531
theorem B11969059 : Blo 1455547 11969059 := bstep (se 1 (by rfl) ⟨8976794, by rfl⟩ : syracuseStep 11969059 = 17953589) B17953589
theorem B1638967 : Blo 1455547 1638967 := bstep (se 1 (by rfl) ⟨1229225, by rfl⟩ : syracuseStep 1638967 = 2458451) B2458451
theorem B2458201 : Blo 1455547 2458201 := bstep (se 2 (by rfl) ⟨921825, by rfl⟩ : syracuseStep 2458201 = 1843651) B1843651
theorem B8864387 : Blo 1455547 8864387 := bstep (se 1 (by rfl) ⟨6648290, by rfl⟩ : syracuseStep 8864387 = 13296581) B13296581
theorem B5530315 : Blo 1455547 5530315 := bstep (se 1 (by rfl) ⟨4147736, by rfl⟩ : syracuseStep 5530315 = 8295473) B8295473
theorem B5251787 : Blo 1455547 5251787 := bstep (se 1 (by rfl) ⟨3938840, by rfl⟩ : syracuseStep 5251787 = 7877681) B7877681
theorem B3277529 : Blo 1455547 3277529 := bstep (se 2 (by rfl) ⟨1229073, by rfl⟩ : syracuseStep 3277529 = 2458147) B2458147
theorem B6218461 : Blo 1455547 6218461 := bstep (se 3 (by rfl) ⟨1165961, by rfl⟩ : syracuseStep 6218461 = 2331923) B2331923
theorem B1639147 : Blo 1455547 1639147 := bstep (se 1 (by rfl) ⟨1229360, by rfl⟩ : syracuseStep 1639147 = 2458721) B2458721
theorem B2073367 : Blo 1455547 2073367 := bstep (se 1 (by rfl) ⟨1555025, by rfl⟩ : syracuseStep 2073367 = 3110051) B3110051
theorem B3687191 : Blo 1455547 3687191 := bstep (se 1 (by rfl) ⟨2765393, by rfl⟩ : syracuseStep 3687191 = 5530787) B5530787
theorem B18916141 : Blo 1455547 18916141 := bstep (se 3 (by rfl) ⟨3546776, by rfl⟩ : syracuseStep 18916141 = 7093553) B7093553
theorem B3277619 : Blo 1455547 3277619 := bstep (se 1 (by rfl) ⟨2458214, by rfl⟩ : syracuseStep 3277619 = 4916429) B4916429
theorem B7873355 : Blo 1455547 7873355 := bstep (se 1 (by rfl) ⟨5905016, by rfl⟩ : syracuseStep 7873355 = 11810033) B11810033
theorem B3277655 : Blo 1455547 3277655 := bstep (se 1 (by rfl) ⟨2458241, by rfl⟩ : syracuseStep 3277655 = 4916483) B4916483
theorem B1639255 : Blo 1455547 1639255 := bstep (se 1 (by rfl) ⟨1229441, by rfl⟩ : syracuseStep 1639255 = 2458883) B2458883
theorem B12436375 : Blo 1455547 12436375 := bstep (se 1 (by rfl) ⟨9327281, by rfl⟩ : syracuseStep 12436375 = 18654563) B18654563
theorem B6996887 : Blo 1455547 6996887 := bstep (se 1 (by rfl) ⟨5247665, by rfl⟩ : syracuseStep 6996887 = 10495331) B10495331
theorem B5530589 : Blo 1455547 5530589 := bstep (se 3 (by rfl) ⟨1036985, by rfl⟩ : syracuseStep 5530589 = 2073971) B2073971
theorem B3277835 : Blo 1455547 3277835 := bstep (se 1 (by rfl) ⟨2458376, by rfl⟩ : syracuseStep 3277835 = 4916753) B4916753
theorem B1639435 : Blo 1455547 1639435 := bstep (se 1 (by rfl) ⟨1229576, by rfl⟩ : syracuseStep 1639435 = 2459153) B2459153
theorem B3277889 : Blo 1455547 3277889 := bstep (se 2 (by rfl) ⟨1229208, by rfl⟩ : syracuseStep 3277889 = 2458417) B2458417
theorem B1844299 : Blo 1455547 1844299 := bstep (se 1 (by rfl) ⟨1383224, by rfl⟩ : syracuseStep 1844299 = 2766449) B2766449
theorem B6644825 : Blo 1455547 6644825 := bstep (se 2 (by rfl) ⟨2491809, by rfl⟩ : syracuseStep 6644825 = 4983619) B4983619
theorem B1639543 : Blo 1455547 1639543 := bstep (se 1 (by rfl) ⟨1229657, by rfl⟩ : syracuseStep 1639543 = 2459315) B2459315
theorem B1475735 : Blo 1455547 1475735 := bstep (se 1 (by rfl) ⟨1106801, by rfl⟩ : syracuseStep 1475735 = 2213603) B2213603
theorem B4916375 : Blo 1455547 4916375 := bstep (se 1 (by rfl) ⟨3687281, by rfl⟩ : syracuseStep 4916375 = 7374563) B7374563
theorem B2458775 : Blo 1455547 2458775 := bstep (se 1 (by rfl) ⟨1844081, by rfl⟩ : syracuseStep 2458775 = 3688163) B3688163
theorem B2458903 : Blo 1455547 2458903 := bstep (se 1 (by rfl) ⟨1844177, by rfl⟩ : syracuseStep 2458903 = 3688355) B3688355
theorem B3278105 : Blo 1455547 3278105 := bstep (se 2 (by rfl) ⟨1229289, by rfl⟩ : syracuseStep 3278105 = 2458579) B2458579
theorem B1639723 : Blo 1455547 1639723 := bstep (se 1 (by rfl) ⟨1229792, by rfl⟩ : syracuseStep 1639723 = 2459585) B2459585
theorem B3278195 : Blo 1455547 3278195 := bstep (se 1 (by rfl) ⟨2458646, by rfl⟩ : syracuseStep 3278195 = 4917293) B4917293
theorem B3278231 : Blo 1455547 3278231 := bstep (se 1 (by rfl) ⟨2458673, by rfl⟩ : syracuseStep 3278231 = 4917347) B4917347
theorem B12617137 : Blo 1455547 12617137 := bstep (se 2 (by rfl) ⟨4731426, by rfl⟩ : syracuseStep 12617137 = 9462853) B9462853
theorem B6219281 : Blo 1455547 6219281 := bstep (se 2 (by rfl) ⟨2332230, by rfl⟩ : syracuseStep 6219281 = 4664461) B4664461
theorem B7374401 : Blo 1455547 7374401 := bstep (se 2 (by rfl) ⟨2765400, by rfl⟩ : syracuseStep 7374401 = 5530801) B5530801
theorem B3688001 : Blo 1455547 3688001 := bstep (se 2 (by rfl) ⟨1383000, by rfl⟩ : syracuseStep 3688001 = 2766001) B2766001
theorem B4982347 : Blo 1455547 4982347 := bstep (se 1 (by rfl) ⟨3736760, by rfl⟩ : syracuseStep 4982347 = 7473521) B7473521
theorem B3278411 : Blo 1455547 3278411 := bstep (se 1 (by rfl) ⟨2458808, by rfl⟩ : syracuseStep 3278411 = 4917617) B4917617
theorem B3278465 : Blo 1455547 3278465 := bstep (se 2 (by rfl) ⟨1229424, by rfl⟩ : syracuseStep 3278465 = 2458849) B2458849
theorem B5531287 : Blo 1455547 5531287 := bstep (se 1 (by rfl) ⟨4148465, by rfl⟩ : syracuseStep 5531287 = 8296931) B8296931
theorem B4916915 : Blo 1455547 4916915 := bstep (se 1 (by rfl) ⟨3687686, by rfl⟩ : syracuseStep 4916915 = 7375373) B7375373
theorem B23635637 : Blo 1455547 23635637 := bstep (se 5 (by rfl) ⟨1107920, by rfl⟩ : syracuseStep 23635637 = 2215841) B2215841
theorem B5252825 : Blo 1455547 5252825 := bstep (se 2 (by rfl) ⟨1969809, by rfl⟩ : syracuseStep 5252825 = 3939619) B3939619
theorem B5908247 : Blo 1455547 5908247 := bstep (se 1 (by rfl) ⟨4431185, by rfl⟩ : syracuseStep 5908247 = 8862371) B8862371
theorem B4982579 : Blo 1455547 4982579 := bstep (se 1 (by rfl) ⟨3736934, by rfl⟩ : syracuseStep 4982579 = 7473869) B7473869
theorem B4663129 : Blo 1455547 4663129 := bstep (se 2 (by rfl) ⟨1748673, by rfl⟩ : syracuseStep 4663129 = 3497347) B3497347
theorem B3278681 : Blo 1455547 3278681 := bstep (se 2 (by rfl) ⟨1229505, by rfl⟩ : syracuseStep 3278681 = 2459011) B2459011
theorem B2459531 : Blo 1455547 2459531 := bstep (se 1 (by rfl) ⟨1844648, by rfl⟩ : syracuseStep 2459531 = 3689297) B3689297
theorem B3278771 : Blo 1455547 3278771 := bstep (se 1 (by rfl) ⟨2459078, by rfl⟩ : syracuseStep 3278771 = 4918157) B4918157
theorem B4917185 : Blo 1455547 4917185 := bstep (se 2 (by rfl) ⟨1843944, by rfl⟩ : syracuseStep 4917185 = 3687889) B3687889
theorem B3278807 : Blo 1455547 3278807 := bstep (se 1 (by rfl) ⟨2459105, by rfl⟩ : syracuseStep 3278807 = 4918211) B4918211
theorem B3688537 : Blo 1455547 3688537 := bstep (se 2 (by rfl) ⟨1383201, by rfl⟩ : syracuseStep 3688537 = 2766403) B2766403
theorem B7874653 : Blo 1455547 7874653 := bstep (se 3 (by rfl) ⟨1476497, by rfl⟩ : syracuseStep 7874653 = 2952995) B2952995
theorem B3278987 : Blo 1455547 3278987 := bstep (se 1 (by rfl) ⟨2459240, by rfl⟩ : syracuseStep 3278987 = 4918481) B4918481
theorem B6219949 : Blo 1455547 6219949 := bstep (se 3 (by rfl) ⟨1166240, by rfl⟩ : syracuseStep 6219949 = 2332481) B2332481
theorem B3279041 : Blo 1455547 3279041 := bstep (se 2 (by rfl) ⟨1229640, by rfl⟩ : syracuseStep 3279041 = 2459281) B2459281
theorem B8292739 : Blo 1455547 8292739 := bstep (se 1 (by rfl) ⟨6219554, by rfl⟩ : syracuseStep 8292739 = 12439109) B12439109
theorem B3279257 : Blo 1455547 3279257 := bstep (se 2 (by rfl) ⟨1229721, by rfl⟩ : syracuseStep 3279257 = 2459443) B2459443
theorem B5532077 : Blo 1455547 5532077 := bstep (se 3 (by rfl) ⟨1037264, by rfl⟩ : syracuseStep 5532077 = 2074529) B2074529
theorem B3500491 : Blo 1455547 3500491 := bstep (se 1 (by rfl) ⟨2625368, by rfl⟩ : syracuseStep 3500491 = 5250737) B5250737
theorem B4917725 : Blo 1455547 4917725 := bstep (se 3 (by rfl) ⟨922073, by rfl⟩ : syracuseStep 4917725 = 1844147) B1844147
theorem B3279347 : Blo 1455547 3279347 := bstep (se 1 (by rfl) ⟨2459510, by rfl⟩ : syracuseStep 3279347 = 4919021) B4919021
theorem B5605891 : Blo 1455547 5605891 := bstep (se 1 (by rfl) ⟨4204418, by rfl⟩ : syracuseStep 5605891 = 8408837) B8408837
theorem B3279383 : Blo 1455547 3279383 := bstep (se 1 (by rfl) ⟨2459537, by rfl⟩ : syracuseStep 3279383 = 4919075) B4919075
theorem B2214425 : Blo 1455547 2214425 := bstep (se 2 (by rfl) ⟨830409, by rfl⟩ : syracuseStep 2214425 = 1660819) B1660819
theorem B6220547 : Blo 1455547 6220547 := bstep (se 1 (by rfl) ⟨4665410, by rfl⟩ : syracuseStep 6220547 = 9330821) B9330821
theorem B2763571 : Blo 1455547 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B2624395 : Blo 1455547 2624395 := bstep (se 1 (by rfl) ⟨1968296, by rfl⟩ : syracuseStep 2624395 = 3936593) B3936593
theorem B4148147 : Blo 1455547 4148147 := bstep (se 1 (by rfl) ⟨3111110, by rfl⟩ : syracuseStep 4148147 = 6222221) B6222221
theorem B4983769 : Blo 1455547 4983769 := bstep (se 2 (by rfl) ⟨1868913, by rfl⟩ : syracuseStep 4983769 = 3737827) B3737827
theorem B2952217 : Blo 1455547 2952217 := bstep (se 2 (by rfl) ⟨1107081, by rfl⟩ : syracuseStep 2952217 = 2214163) B2214163
theorem B3501107 : Blo 1455547 3501107 := bstep (se 1 (by rfl) ⟨2625830, by rfl⟩ : syracuseStep 3501107 = 5251661) B5251661
theorem B2215063 : Blo 1455547 2215063 := bstep (se 1 (by rfl) ⟨1661297, by rfl⟩ : syracuseStep 2215063 = 3322595) B3322595
theorem B2764019 : Blo 1455547 2764019 := bstep (se 1 (by rfl) ⟨2073014, by rfl⟩ : syracuseStep 2764019 = 4146029) B4146029
theorem B2764057 : Blo 1455547 2764057 := bstep (se 2 (by rfl) ⟨1036521, by rfl⟩ : syracuseStep 2764057 = 2073043) B2073043
theorem B8293697 : Blo 1455547 8293697 := bstep (se 2 (by rfl) ⟨3110136, by rfl⟩ : syracuseStep 8293697 = 6220273) B6220273
theorem B10505537 : Blo 1455547 10505537 := bstep (se 2 (by rfl) ⟨3939576, by rfl⟩ : syracuseStep 10505537 = 7879153) B7879153
theorem B12447107 : Blo 1455547 12447107 := bstep (se 1 (by rfl) ⟨9335330, by rfl⟩ : syracuseStep 12447107 = 18670661) B18670661
theorem B5615021 : Blo 1455547 5615021 := bstep (se 3 (by rfl) ⟨1052816, by rfl⟩ : syracuseStep 5615021 = 2105633) B2105633
theorem B7376345 : Blo 1455547 7376345 := bstep (se 2 (by rfl) ⟨2766129, by rfl⟩ : syracuseStep 7376345 = 5532259) B5532259
theorem B2952769 : Blo 1455547 2952769 := bstep (se 2 (by rfl) ⟨1107288, by rfl⟩ : syracuseStep 2952769 = 2214577) B2214577
theorem B4918859 : Blo 1455547 4918859 := bstep (se 1 (by rfl) ⟨3689144, by rfl⟩ : syracuseStep 4918859 = 7378289) B7378289
theorem B2764505 : Blo 1455547 2764505 := bstep (se 2 (by rfl) ⟨1036689, by rfl⟩ : syracuseStep 2764505 = 2073379) B2073379
theorem B6639425 : Blo 1455547 6639425 := bstep (se 2 (by rfl) ⟨2489784, by rfl⟩ : syracuseStep 6639425 = 4979569) B4979569
theorem B5533505 : Blo 1455547 5533505 := bstep (se 2 (by rfl) ⟨2075064, by rfl⟩ : syracuseStep 5533505 = 4150129) B4150129
theorem B4919129 : Blo 1455547 4919129 := bstep (se 2 (by rfl) ⟨1844673, by rfl⟩ : syracuseStep 4919129 = 3689347) B3689347
theorem B4665281 : Blo 1455547 4665281 := bstep (se 2 (by rfl) ⟨1749480, by rfl⟩ : syracuseStep 4665281 = 3498961) B3498961
theorem B3108889 : Blo 1455547 3108889 := bstep (se 2 (by rfl) ⟨1165833, by rfl⟩ : syracuseStep 3108889 = 2331667) B2331667
theorem B2183321 : Blo 1455547 2183321 := bstep (se 2 (by rfl) ⟨818745, by rfl⟩ : syracuseStep 2183321 = 1637491) B1637491
theorem B2953369 : Blo 1455547 2953369 := bstep (se 2 (by rfl) ⟨1107513, by rfl⟩ : syracuseStep 2953369 = 2215027) B2215027
theorem B9326771 : Blo 1455547 9326771 := bstep (se 1 (by rfl) ⟨6995078, by rfl⟩ : syracuseStep 9326771 = 13990157) B13990157
theorem B3109043 : Blo 1455547 3109043 := bstep (se 1 (by rfl) ⟨2331782, by rfl⟩ : syracuseStep 3109043 = 4663565) B4663565
theorem B6738113 : Blo 1455547 6738113 := bstep (se 2 (by rfl) ⟨2526792, by rfl⟩ : syracuseStep 6738113 = 5053585) B5053585
theorem B2625779 : Blo 1455547 2625779 := bstep (se 1 (by rfl) ⟨1969334, by rfl⟩ : syracuseStep 2625779 = 3938669) B3938669
theorem B2183435 : Blo 1455547 2183435 := bstep (se 1 (by rfl) ⟨1637576, by rfl⟩ : syracuseStep 2183435 = 3275153) B3275153
theorem B2183447 : Blo 1455547 2183447 := bstep (se 1 (by rfl) ⟨1637585, by rfl⟩ : syracuseStep 2183447 = 3275171) B3275171
theorem B4428083 : Blo 1455547 4428083 := bstep (se 1 (by rfl) ⟨3321062, by rfl⟩ : syracuseStep 4428083 = 6642125) B6642125
theorem B1749323 : Blo 1455547 1749323 := bstep (se 1 (by rfl) ⟨1311992, by rfl⟩ : syracuseStep 1749323 = 2623985) B2623985
theorem B2183513 : Blo 1455547 2183513 := bstep (se 2 (by rfl) ⟨818817, by rfl⟩ : syracuseStep 2183513 = 1637635) B1637635
theorem B2765249 : Blo 1455547 2765249 := bstep (se 2 (by rfl) ⟨1036968, by rfl⟩ : syracuseStep 2765249 = 2073937) B2073937
theorem B2183627 : Blo 1455547 2183627 := bstep (se 1 (by rfl) ⟨1637720, by rfl⟩ : syracuseStep 2183627 = 3275441) B3275441
theorem B2183639 : Blo 1455547 2183639 := bstep (se 1 (by rfl) ⟨1637729, by rfl⟩ : syracuseStep 2183639 = 3275459) B3275459
theorem B2183705 : Blo 1455547 2183705 := bstep (se 2 (by rfl) ⟨818889, by rfl⟩ : syracuseStep 2183705 = 1637779) B1637779
theorem B2183819 : Blo 1455547 2183819 := bstep (se 1 (by rfl) ⟨1637864, by rfl⟩ : syracuseStep 2183819 = 3275729) B3275729
theorem B2183831 : Blo 1455547 2183831 := bstep (se 1 (by rfl) ⟨1637873, by rfl⟩ : syracuseStep 2183831 = 3275747) B3275747
theorem B5608109 : Blo 1455547 5608109 := bstep (se 3 (by rfl) ⟨1051520, by rfl⟩ : syracuseStep 5608109 = 2103041) B2103041
theorem B2765515 : Blo 1455547 2765515 := bstep (se 1 (by rfl) ⟨2074136, by rfl⟩ : syracuseStep 2765515 = 4148273) B4148273
theorem B2183897 : Blo 1455547 2183897 := bstep (se 2 (by rfl) ⟨818961, by rfl⟩ : syracuseStep 2183897 = 1637923) B1637923
theorem B2626291 : Blo 1455547 2626291 := bstep (se 1 (by rfl) ⟨1969718, by rfl⟩ : syracuseStep 2626291 = 3939437) B3939437
theorem B2184011 : Blo 1455547 2184011 := bstep (se 1 (by rfl) ⟨1638008, by rfl⟩ : syracuseStep 2184011 = 3276017) B3276017
theorem B2184023 : Blo 1455547 2184023 := bstep (se 1 (by rfl) ⟨1638017, by rfl⟩ : syracuseStep 2184023 = 3276035) B3276035
theorem B2184089 : Blo 1455547 2184089 := bstep (se 2 (by rfl) ⟨819033, by rfl⟩ : syracuseStep 2184089 = 1638067) B1638067
theorem B5903363 : Blo 1455547 5903363 := bstep (se 1 (by rfl) ⟨4427522, by rfl⟩ : syracuseStep 5903363 = 8855045) B8855045
theorem B2184203 : Blo 1455547 2184203 := bstep (se 1 (by rfl) ⟨1638152, by rfl⟩ : syracuseStep 2184203 = 3276305) B3276305
theorem B23950349 : Blo 1455547 23950349 := bstep (se 3 (by rfl) ⟨4490690, by rfl⟩ : syracuseStep 23950349 = 8981381) B8981381
theorem B24892433 : Blo 1455547 24892433 := bstep (se 2 (by rfl) ⟨9334662, by rfl⟩ : syracuseStep 24892433 = 18669325) B18669325
theorem B2184215 : Blo 1455547 2184215 := bstep (se 1 (by rfl) ⟨1638161, by rfl⟩ : syracuseStep 2184215 = 3276323) B3276323
theorem B7377965 : Blo 1455547 7377965 := bstep (se 3 (by rfl) ⟨1383368, by rfl⟩ : syracuseStep 7377965 = 2766737) B2766737
theorem B7001153 : Blo 1455547 7001153 := bstep (se 2 (by rfl) ⟨2625432, by rfl⟩ : syracuseStep 7001153 = 5250865) B5250865
theorem B2839627 : Blo 1455547 2839627 := bstep (se 1 (by rfl) ⟨2129720, by rfl⟩ : syracuseStep 2839627 = 4259441) B4259441
theorem B2184281 : Blo 1455547 2184281 := bstep (se 2 (by rfl) ⟨819105, by rfl⟩ : syracuseStep 2184281 = 1638211) B1638211
theorem B5608541 : Blo 1455547 5608541 := bstep (se 3 (by rfl) ⟨1051601, by rfl⟩ : syracuseStep 5608541 = 2103203) B2103203
theorem B3110017 : Blo 1455547 3110017 := bstep (se 2 (by rfl) ⟨1166256, by rfl⟩ : syracuseStep 3110017 = 2332513) B2332513
theorem B2765963 : Blo 1455547 2765963 := bstep (se 1 (by rfl) ⟨2074472, by rfl⟩ : syracuseStep 2765963 = 4148945) B4148945
theorem B5526701 : Blo 1455547 5526701 := bstep (se 3 (by rfl) ⟨1036256, by rfl⟩ : syracuseStep 5526701 = 2072513) B2072513
theorem B5526731 : Blo 1455547 5526731 := bstep (se 1 (by rfl) ⟨4145048, by rfl⟩ : syracuseStep 5526731 = 8290097) B8290097
theorem B2184395 : Blo 1455547 2184395 := bstep (se 1 (by rfl) ⟨1638296, by rfl⟩ : syracuseStep 2184395 = 3276593) B3276593
theorem B2184407 : Blo 1455547 2184407 := bstep (se 1 (by rfl) ⟨1638305, by rfl⟩ : syracuseStep 2184407 = 3276611) B3276611
theorem B2184473 : Blo 1455547 2184473 := bstep (se 2 (by rfl) ⟨819177, by rfl⟩ : syracuseStep 2184473 = 1638355) B1638355
theorem B2766145 : Blo 1455547 2766145 := bstep (se 2 (by rfl) ⟨1037304, by rfl⟩ : syracuseStep 2766145 = 2074609) B2074609
theorem B2184587 : Blo 1455547 2184587 := bstep (se 1 (by rfl) ⟨1638440, by rfl⟩ : syracuseStep 2184587 = 3276881) B3276881
theorem B2184599 : Blo 1455547 2184599 := bstep (se 1 (by rfl) ⟨1638449, by rfl⟩ : syracuseStep 2184599 = 3276899) B3276899
theorem B1496503 : Blo 1455547 1496503 := bstep (se 1 (by rfl) ⟨1122377, by rfl⟩ : syracuseStep 1496503 = 2244755) B2244755
theorem B1455563 : Blo 1455547 1455563 := bstep (se 1 (by rfl) ⟨1091672, by rfl⟩ : syracuseStep 1455563 = 2183345) B2183345
theorem B1455575 : Blo 1455547 1455575 := bstep (se 1 (by rfl) ⟨1091681, by rfl⟩ : syracuseStep 1455575 = 2183363) B2183363
theorem B3110359 : Blo 1455547 3110359 := bstep (se 1 (by rfl) ⟨2332769, by rfl⟩ : syracuseStep 3110359 = 4665539) B4665539
theorem B2184665 : Blo 1455547 2184665 := bstep (se 2 (by rfl) ⟨819249, by rfl⟩ : syracuseStep 2184665 = 1638499) B1638499
theorem B1455595 : Blo 1455547 1455595 := bstep (se 1 (by rfl) ⟨1091696, by rfl⟩ : syracuseStep 1455595 = 2183393) B2183393
theorem B1455607 : Blo 1455547 1455607 := bstep (se 1 (by rfl) ⟨1091705, by rfl⟩ : syracuseStep 1455607 = 2183411) B2183411
theorem B1455627 : Blo 1455547 1455627 := bstep (se 1 (by rfl) ⟨1091720, by rfl⟩ : syracuseStep 1455627 = 2183441) B2183441
theorem B1455639 : Blo 1455547 1455639 := bstep (se 1 (by rfl) ⟨1091729, by rfl⟩ : syracuseStep 1455639 = 2183459) B2183459
theorem B1455659 : Blo 1455547 1455659 := bstep (se 1 (by rfl) ⟨1091744, by rfl⟩ : syracuseStep 1455659 = 2183489) B2183489
theorem B1455671 : Blo 1455547 1455671 := bstep (se 1 (by rfl) ⟨1091753, by rfl⟩ : syracuseStep 1455671 = 2183507) B2183507
theorem B1455691 : Blo 1455547 1455691 := bstep (se 1 (by rfl) ⟨1091768, by rfl⟩ : syracuseStep 1455691 = 2183537) B2183537
theorem B2184779 : Blo 1455547 2184779 := bstep (se 1 (by rfl) ⟨1638584, by rfl⟩ : syracuseStep 2184779 = 3277169) B3277169
theorem B1455703 : Blo 1455547 1455703 := bstep (se 1 (by rfl) ⟨1091777, by rfl⟩ : syracuseStep 1455703 = 2183555) B2183555
theorem B2184791 : Blo 1455547 2184791 := bstep (se 1 (by rfl) ⟨1638593, by rfl⟩ : syracuseStep 2184791 = 3277187) B3277187
theorem B1455723 : Blo 1455547 1455723 := bstep (se 1 (by rfl) ⟨1091792, by rfl⟩ : syracuseStep 1455723 = 2183585) B2183585
theorem B1455735 : Blo 1455547 1455735 := bstep (se 1 (by rfl) ⟨1091801, by rfl⟩ : syracuseStep 1455735 = 2183603) B2183603
theorem B1455755 : Blo 1455547 1455755 := bstep (se 1 (by rfl) ⟨1091816, by rfl⟩ : syracuseStep 1455755 = 2183633) B2183633
theorem B1455767 : Blo 1455547 1455767 := bstep (se 1 (by rfl) ⟨1091825, by rfl⟩ : syracuseStep 1455767 = 2183651) B2183651
theorem B2184857 : Blo 1455547 2184857 := bstep (se 2 (by rfl) ⟨819321, by rfl⟩ : syracuseStep 2184857 = 1638643) B1638643
theorem B2766487 : Blo 1455547 2766487 := bstep (se 1 (by rfl) ⟨2074865, by rfl⟩ : syracuseStep 2766487 = 4149731) B4149731
theorem B1455787 : Blo 1455547 1455787 := bstep (se 1 (by rfl) ⟨1091840, by rfl⟩ : syracuseStep 1455787 = 2183681) B2183681
theorem B1455799 : Blo 1455547 1455799 := bstep (se 1 (by rfl) ⟨1091849, by rfl⟩ : syracuseStep 1455799 = 2183699) B2183699
theorem B1455819 : Blo 1455547 1455819 := bstep (se 1 (by rfl) ⟨1091864, by rfl⟩ : syracuseStep 1455819 = 2183729) B2183729
theorem B1455831 : Blo 1455547 1455831 := bstep (se 1 (by rfl) ⟨1091873, by rfl⟩ : syracuseStep 1455831 = 2183747) B2183747
theorem B12449497 : Blo 1455547 12449497 := bstep (se 2 (by rfl) ⟨4668561, by rfl⟩ : syracuseStep 12449497 = 9337123) B9337123
theorem B1455851 : Blo 1455547 1455851 := bstep (se 1 (by rfl) ⟨1091888, by rfl⟩ : syracuseStep 1455851 = 2183777) B2183777
theorem B1455863 : Blo 1455547 1455863 := bstep (se 1 (by rfl) ⟨1091897, by rfl⟩ : syracuseStep 1455863 = 2183795) B2183795
theorem B1455883 : Blo 1455547 1455883 := bstep (se 1 (by rfl) ⟨1091912, by rfl⟩ : syracuseStep 1455883 = 2183825) B2183825
theorem B2184971 : Blo 1455547 2184971 := bstep (se 1 (by rfl) ⟨1638728, by rfl⟩ : syracuseStep 2184971 = 3277457) B3277457
theorem B7370513 : Blo 1455547 7370513 := bstep (se 2 (by rfl) ⟨2763942, by rfl⟩ : syracuseStep 7370513 = 5527885) B5527885
theorem B4912919 : Blo 1455547 4912919 := bstep (se 1 (by rfl) ⟨3684689, by rfl⟩ : syracuseStep 4912919 = 7369379) B7369379
theorem B1455895 : Blo 1455547 1455895 := bstep (se 1 (by rfl) ⟨1091921, by rfl⟩ : syracuseStep 1455895 = 2183843) B2183843
theorem B2184983 : Blo 1455547 2184983 := bstep (se 1 (by rfl) ⟨1638737, by rfl⟩ : syracuseStep 2184983 = 3277475) B3277475
theorem B1455915 : Blo 1455547 1455915 := bstep (se 1 (by rfl) ⟨1091936, by rfl⟩ : syracuseStep 1455915 = 2183873) B2183873
theorem B1455927 : Blo 1455547 1455927 := bstep (se 1 (by rfl) ⟨1091945, by rfl⟩ : syracuseStep 1455927 = 2183891) B2183891
theorem B1455947 : Blo 1455547 1455947 := bstep (se 1 (by rfl) ⟨1091960, by rfl⟩ : syracuseStep 1455947 = 2183921) B2183921
theorem B1455959 : Blo 1455547 1455959 := bstep (se 1 (by rfl) ⟨1091969, by rfl⟩ : syracuseStep 1455959 = 2183939) B2183939
theorem B5527385 : Blo 1455547 5527385 := bstep (se 2 (by rfl) ⟨2072769, by rfl⟩ : syracuseStep 5527385 = 4145539) B4145539
theorem B2185049 : Blo 1455547 2185049 := bstep (se 2 (by rfl) ⟨819393, by rfl⟩ : syracuseStep 2185049 = 1638787) B1638787
theorem B23951203 : Blo 1455547 23951203 := bstep (se 1 (by rfl) ⟨17963402, by rfl⟩ : syracuseStep 23951203 = 35926805) B35926805
theorem B1455979 : Blo 1455547 1455979 := bstep (se 1 (by rfl) ⟨1091984, by rfl⟩ : syracuseStep 1455979 = 2183969) B2183969
theorem B2766707 : Blo 1455547 2766707 := bstep (se 1 (by rfl) ⟨2075030, by rfl⟩ : syracuseStep 2766707 = 4150061) B4150061
theorem B1455991 : Blo 1455547 1455991 := bstep (se 1 (by rfl) ⟨1091993, by rfl⟩ : syracuseStep 1455991 = 2183987) B2183987
theorem B1456011 : Blo 1455547 1456011 := bstep (se 1 (by rfl) ⟨1092008, by rfl⟩ : syracuseStep 1456011 = 2184017) B2184017
theorem B3110795 : Blo 1455547 3110795 := bstep (se 1 (by rfl) ⟨2333096, by rfl⟩ : syracuseStep 3110795 = 4666193) B4666193
theorem B1456023 : Blo 1455547 1456023 := bstep (se 1 (by rfl) ⟨1092017, by rfl⟩ : syracuseStep 1456023 = 2184035) B2184035
theorem B1456043 : Blo 1455547 1456043 := bstep (se 1 (by rfl) ⟨1092032, by rfl⟩ : syracuseStep 1456043 = 2184065) B2184065
theorem B7370675 : Blo 1455547 7370675 := bstep (se 1 (by rfl) ⟨5528006, by rfl⟩ : syracuseStep 7370675 = 11056013) B11056013
theorem B1456055 : Blo 1455547 1456055 := bstep (se 1 (by rfl) ⟨1092041, by rfl⟩ : syracuseStep 1456055 = 2184083) B2184083
theorem B1456075 : Blo 1455547 1456075 := bstep (se 1 (by rfl) ⟨1092056, by rfl⟩ : syracuseStep 1456075 = 2184113) B2184113
theorem B2185163 : Blo 1455547 2185163 := bstep (se 1 (by rfl) ⟨1638872, by rfl⟩ : syracuseStep 2185163 = 3277745) B3277745
theorem B1456087 : Blo 1455547 1456087 := bstep (se 1 (by rfl) ⟨1092065, by rfl⟩ : syracuseStep 1456087 = 2184131) B2184131
theorem B2185175 : Blo 1455547 2185175 := bstep (se 1 (by rfl) ⟨1638881, by rfl⟩ : syracuseStep 2185175 = 3277763) B3277763
theorem B1456107 : Blo 1455547 1456107 := bstep (se 1 (by rfl) ⟨1092080, by rfl⟩ : syracuseStep 1456107 = 2184161) B2184161
theorem B2734067 : Blo 1455547 2734067 := bstep (se 1 (by rfl) ⟨2050550, by rfl⟩ : syracuseStep 2734067 = 4101101) B4101101
theorem B1456119 : Blo 1455547 1456119 := bstep (se 1 (by rfl) ⟨1092089, by rfl⟩ : syracuseStep 1456119 = 2184179) B2184179
theorem B1456139 : Blo 1455547 1456139 := bstep (se 1 (by rfl) ⟨1092104, by rfl⟩ : syracuseStep 1456139 = 2184209) B2184209
theorem B8091665 : Blo 1455547 8091665 := bstep (se 2 (by rfl) ⟨3034374, by rfl⟩ : syracuseStep 8091665 = 6068749) B6068749
theorem B1456151 : Blo 1455547 1456151 := bstep (se 1 (by rfl) ⟨1092113, by rfl⟩ : syracuseStep 1456151 = 2184227) B2184227
theorem B2185241 : Blo 1455547 2185241 := bstep (se 2 (by rfl) ⟨819465, by rfl⟩ : syracuseStep 2185241 = 1638931) B1638931
theorem B1456171 : Blo 1455547 1456171 := bstep (se 1 (by rfl) ⟨1092128, by rfl⟩ : syracuseStep 1456171 = 2184257) B2184257
theorem B1456183 : Blo 1455547 1456183 := bstep (se 1 (by rfl) ⟨1092137, by rfl⟩ : syracuseStep 1456183 = 2184275) B2184275
theorem B1456203 : Blo 1455547 1456203 := bstep (se 1 (by rfl) ⟨1092152, by rfl⟩ : syracuseStep 1456203 = 2184305) B2184305
theorem B1456215 : Blo 1455547 1456215 := bstep (se 1 (by rfl) ⟨1092161, by rfl⟩ : syracuseStep 1456215 = 2184323) B2184323
theorem B2766935 : Blo 1455547 2766935 := bstep (se 1 (by rfl) ⟨2075201, by rfl⟩ : syracuseStep 2766935 = 4150403) B4150403
theorem B1456235 : Blo 1455547 1456235 := bstep (se 1 (by rfl) ⟨1092176, by rfl⟩ : syracuseStep 1456235 = 2184353) B2184353
theorem B1456247 : Blo 1455547 1456247 := bstep (se 1 (by rfl) ⟨1092185, by rfl⟩ : syracuseStep 1456247 = 2184371) B2184371
theorem B1456267 : Blo 1455547 1456267 := bstep (se 1 (by rfl) ⟨1092200, by rfl⟩ : syracuseStep 1456267 = 2184401) B2184401
theorem B2185355 : Blo 1455547 2185355 := bstep (se 1 (by rfl) ⟨1639016, by rfl⟩ : syracuseStep 2185355 = 3278033) B3278033
theorem B5527703 : Blo 1455547 5527703 := bstep (se 1 (by rfl) ⟨4145777, by rfl⟩ : syracuseStep 5527703 = 8291555) B8291555
theorem B1456279 : Blo 1455547 1456279 := bstep (se 1 (by rfl) ⟨1092209, by rfl⟩ : syracuseStep 1456279 = 2184419) B2184419
theorem B2185367 : Blo 1455547 2185367 := bstep (se 1 (by rfl) ⟨1639025, by rfl⟩ : syracuseStep 2185367 = 3278051) B3278051
theorem B1456299 : Blo 1455547 1456299 := bstep (se 1 (by rfl) ⟨1092224, by rfl⟩ : syracuseStep 1456299 = 2184449) B2184449
theorem B1456311 : Blo 1455547 1456311 := bstep (se 1 (by rfl) ⟨1092233, by rfl⟩ : syracuseStep 1456311 = 2184467) B2184467
theorem B1456331 : Blo 1455547 1456331 := bstep (se 1 (by rfl) ⟨1092248, by rfl⟩ : syracuseStep 1456331 = 2184497) B2184497
theorem B1456343 : Blo 1455547 1456343 := bstep (se 1 (by rfl) ⟨1092257, by rfl⟩ : syracuseStep 1456343 = 2184515) B2184515
theorem B2185433 : Blo 1455547 2185433 := bstep (se 2 (by rfl) ⟨819537, by rfl⟩ : syracuseStep 2185433 = 1639075) B1639075
theorem B1456363 : Blo 1455547 1456363 := bstep (se 1 (by rfl) ⟨1092272, by rfl⟩ : syracuseStep 1456363 = 2184545) B2184545
theorem B1456375 : Blo 1455547 1456375 := bstep (se 1 (by rfl) ⟨1092281, by rfl⟩ : syracuseStep 1456375 = 2184563) B2184563
theorem B3275009 : Blo 1455547 3275009 := bstep (se 2 (by rfl) ⟨1228128, by rfl⟩ : syracuseStep 3275009 = 2456257) B2456257
theorem B1456395 : Blo 1455547 1456395 := bstep (se 1 (by rfl) ⟨1092296, by rfl⟩ : syracuseStep 1456395 = 2184593) B2184593
theorem B85104917 : Blo 1455547 85104917 := bstep (se 6 (by rfl) ⟨1994646, by rfl⟩ : syracuseStep 85104917 = 3989293) B3989293
theorem B1456407 : Blo 1455547 1456407 := bstep (se 1 (by rfl) ⟨1092305, by rfl⟩ : syracuseStep 1456407 = 2184611) B2184611
theorem B1456427 : Blo 1455547 1456427 := bstep (se 1 (by rfl) ⟨1092320, by rfl⟩ : syracuseStep 1456427 = 2184641) B2184641
theorem B4913459 : Blo 1455547 4913459 := bstep (se 1 (by rfl) ⟨3685094, by rfl⟩ : syracuseStep 4913459 = 7370189) B7370189
theorem B1456439 : Blo 1455547 1456439 := bstep (se 1 (by rfl) ⟨1092329, by rfl⟩ : syracuseStep 1456439 = 2184659) B2184659
theorem B6306113 : Blo 1455547 6306113 := bstep (se 2 (by rfl) ⟨2364792, by rfl⟩ : syracuseStep 6306113 = 4729585) B4729585
theorem B26589505 : Blo 1455547 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B1456459 : Blo 1455547 1456459 := bstep (se 1 (by rfl) ⟨1092344, by rfl⟩ : syracuseStep 1456459 = 2184689) B2184689
theorem B2185547 : Blo 1455547 2185547 := bstep (se 1 (by rfl) ⟨1639160, by rfl⟩ : syracuseStep 2185547 = 3278321) B3278321
theorem B1456471 : Blo 1455547 1456471 := bstep (se 1 (by rfl) ⟨1092353, by rfl⟩ : syracuseStep 1456471 = 2184707) B2184707
theorem B2185559 : Blo 1455547 2185559 := bstep (se 1 (by rfl) ⟨1639169, by rfl⟩ : syracuseStep 2185559 = 3278339) B3278339
theorem B1456491 : Blo 1455547 1456491 := bstep (se 1 (by rfl) ⟨1092368, by rfl⟩ : syracuseStep 1456491 = 2184737) B2184737
theorem B1456503 : Blo 1455547 1456503 := bstep (se 1 (by rfl) ⟨1092377, by rfl⟩ : syracuseStep 1456503 = 2184755) B2184755
theorem B1456523 : Blo 1455547 1456523 := bstep (se 1 (by rfl) ⟨1092392, by rfl⟩ : syracuseStep 1456523 = 2184785) B2184785
theorem B1456535 : Blo 1455547 1456535 := bstep (se 1 (by rfl) ⟨1092401, by rfl⟩ : syracuseStep 1456535 = 2184803) B2184803
theorem B2185625 : Blo 1455547 2185625 := bstep (se 2 (by rfl) ⟨819609, by rfl⟩ : syracuseStep 2185625 = 1639219) B1639219
theorem B1456555 : Blo 1455547 1456555 := bstep (se 1 (by rfl) ⟨1092416, by rfl⟩ : syracuseStep 1456555 = 2184833) B2184833
theorem B1456567 : Blo 1455547 1456567 := bstep (se 1 (by rfl) ⟨1092425, by rfl⟩ : syracuseStep 1456567 = 2184851) B2184851
theorem B3684811 : Blo 1455547 3684811 := bstep (se 1 (by rfl) ⟨2763608, by rfl⟩ : syracuseStep 3684811 = 5527217) B5527217
theorem B1456587 : Blo 1455547 1456587 := bstep (se 1 (by rfl) ⟨1092440, by rfl⟩ : syracuseStep 1456587 = 2184881) B2184881
theorem B1456599 : Blo 1455547 1456599 := bstep (se 1 (by rfl) ⟨1092449, by rfl⟩ : syracuseStep 1456599 = 2184899) B2184899
theorem B3275225 : Blo 1455547 3275225 := bstep (se 2 (by rfl) ⟨1228209, by rfl⟩ : syracuseStep 3275225 = 2456419) B2456419
theorem B1554923 : Blo 1455547 1554923 := bstep (se 1 (by rfl) ⟨1166192, by rfl⟩ : syracuseStep 1554923 = 2332385) B2332385
theorem B1456619 : Blo 1455547 1456619 := bstep (se 1 (by rfl) ⟨1092464, by rfl⟩ : syracuseStep 1456619 = 2184929) B2184929
theorem B1456631 : Blo 1455547 1456631 := bstep (se 1 (by rfl) ⟨1092473, by rfl⟩ : syracuseStep 1456631 = 2184947) B2184947
theorem B1456651 : Blo 1455547 1456651 := bstep (se 1 (by rfl) ⟨1092488, by rfl⟩ : syracuseStep 1456651 = 2184977) B2184977
theorem B2185739 : Blo 1455547 2185739 := bstep (se 1 (by rfl) ⟨1639304, by rfl⟩ : syracuseStep 2185739 = 3278609) B3278609
theorem B17717777 : Blo 1455547 17717777 := bstep (se 2 (by rfl) ⟨6644166, by rfl⟩ : syracuseStep 17717777 = 13288333) B13288333
theorem B1456663 : Blo 1455547 1456663 := bstep (se 1 (by rfl) ⟨1092497, by rfl⟩ : syracuseStep 1456663 = 2184995) B2184995
theorem B2185751 : Blo 1455547 2185751 := bstep (se 1 (by rfl) ⟨1639313, by rfl⟩ : syracuseStep 2185751 = 3278627) B3278627
theorem B1456683 : Blo 1455547 1456683 := bstep (se 1 (by rfl) ⟨1092512, by rfl⟩ : syracuseStep 1456683 = 2185025) B2185025
theorem B3275315 : Blo 1455547 3275315 := bstep (se 1 (by rfl) ⟨2456486, by rfl⟩ : syracuseStep 3275315 = 4912973) B4912973
theorem B1456695 : Blo 1455547 1456695 := bstep (se 1 (by rfl) ⟨1092521, by rfl⟩ : syracuseStep 1456695 = 2185043) B2185043
theorem B4913729 : Blo 1455547 4913729 := bstep (se 2 (by rfl) ⟨1842648, by rfl⟩ : syracuseStep 4913729 = 3685297) B3685297
theorem B1456715 : Blo 1455547 1456715 := bstep (se 1 (by rfl) ⟨1092536, by rfl⟩ : syracuseStep 1456715 = 2185073) B2185073
theorem B3275351 : Blo 1455547 3275351 := bstep (se 1 (by rfl) ⟨2456513, by rfl⟩ : syracuseStep 3275351 = 4913027) B4913027
theorem B1456727 : Blo 1455547 1456727 := bstep (se 1 (by rfl) ⟨1092545, by rfl⟩ : syracuseStep 1456727 = 2185091) B2185091
theorem B3684953 : Blo 1455547 3684953 := bstep (se 2 (by rfl) ⟨1381857, by rfl⟩ : syracuseStep 3684953 = 2763715) B2763715
theorem B2185817 : Blo 1455547 2185817 := bstep (se 2 (by rfl) ⟨819681, by rfl⟩ : syracuseStep 2185817 = 1639363) B1639363
theorem B1456747 : Blo 1455547 1456747 := bstep (se 1 (by rfl) ⟨1092560, by rfl⟩ : syracuseStep 1456747 = 2185121) B2185121
theorem B1456759 : Blo 1455547 1456759 := bstep (se 1 (by rfl) ⟨1092569, by rfl⟩ : syracuseStep 1456759 = 2185139) B2185139
theorem B14006915 : Blo 1455547 14006915 := bstep (se 1 (by rfl) ⟨10505186, by rfl⟩ : syracuseStep 14006915 = 21010373) B21010373
theorem B1456779 : Blo 1455547 1456779 := bstep (se 1 (by rfl) ⟨1092584, by rfl⟩ : syracuseStep 1456779 = 2185169) B2185169
theorem B1456791 : Blo 1455547 1456791 := bstep (se 1 (by rfl) ⟨1092593, by rfl⟩ : syracuseStep 1456791 = 2185187) B2185187
theorem B12450455 : Blo 1455547 12450455 := bstep (se 1 (by rfl) ⟨9337841, by rfl⟩ : syracuseStep 12450455 = 18675683) B18675683
theorem B1456811 : Blo 1455547 1456811 := bstep (se 1 (by rfl) ⟨1092608, by rfl⟩ : syracuseStep 1456811 = 2185217) B2185217
theorem B1456823 : Blo 1455547 1456823 := bstep (se 1 (by rfl) ⟨1092617, by rfl⟩ : syracuseStep 1456823 = 2185235) B2185235
theorem B1456843 : Blo 1455547 1456843 := bstep (se 1 (by rfl) ⟨1092632, by rfl⟩ : syracuseStep 1456843 = 2185265) B2185265
theorem B2185931 : Blo 1455547 2185931 := bstep (se 1 (by rfl) ⟨1639448, by rfl⟩ : syracuseStep 2185931 = 3278897) B3278897
theorem B1456855 : Blo 1455547 1456855 := bstep (se 1 (by rfl) ⟨1092641, by rfl⟩ : syracuseStep 1456855 = 2185283) B2185283
theorem B2185943 : Blo 1455547 2185943 := bstep (se 1 (by rfl) ⟨1639457, by rfl⟩ : syracuseStep 2185943 = 3278915) B3278915
theorem B1456875 : Blo 1455547 1456875 := bstep (se 1 (by rfl) ⟨1092656, by rfl⟩ : syracuseStep 1456875 = 2185313) B2185313
theorem B1456887 : Blo 1455547 1456887 := bstep (se 1 (by rfl) ⟨1092665, by rfl⟩ : syracuseStep 1456887 = 2185331) B2185331
theorem B3275531 : Blo 1455547 3275531 := bstep (se 1 (by rfl) ⟨2456648, by rfl⟩ : syracuseStep 3275531 = 4913297) B4913297
theorem B1456907 : Blo 1455547 1456907 := bstep (se 1 (by rfl) ⟨1092680, by rfl⟩ : syracuseStep 1456907 = 2185361) B2185361
theorem B3111691 : Blo 1455547 3111691 := bstep (se 1 (by rfl) ⟨2333768, by rfl⟩ : syracuseStep 3111691 = 4667537) B4667537
theorem B1456919 : Blo 1455547 1456919 := bstep (se 1 (by rfl) ⟨1092689, by rfl⟩ : syracuseStep 1456919 = 2185379) B2185379
theorem B2456345 : Blo 1455547 2456345 := bstep (se 2 (by rfl) ⟨921129, by rfl⟩ : syracuseStep 2456345 = 1842259) B1842259
theorem B2186009 : Blo 1455547 2186009 := bstep (se 2 (by rfl) ⟨819753, by rfl⟩ : syracuseStep 2186009 = 1639507) B1639507
theorem B1456939 : Blo 1455547 1456939 := bstep (se 1 (by rfl) ⟨1092704, by rfl⟩ : syracuseStep 1456939 = 2185409) B2185409
theorem B5528371 : Blo 1455547 5528371 := bstep (se 1 (by rfl) ⟨4146278, by rfl⟩ : syracuseStep 5528371 = 8292557) B8292557
theorem B1456951 : Blo 1455547 1456951 := bstep (se 1 (by rfl) ⟨1092713, by rfl⟩ : syracuseStep 1456951 = 2185427) B2185427
theorem B3275585 : Blo 1455547 3275585 := bstep (se 2 (by rfl) ⟨1228344, by rfl⟩ : syracuseStep 3275585 = 2456689) B2456689
theorem B1456971 : Blo 1455547 1456971 := bstep (se 1 (by rfl) ⟨1092728, by rfl⟩ : syracuseStep 1456971 = 2185457) B2185457
theorem B1456983 : Blo 1455547 1456983 := bstep (se 1 (by rfl) ⟨1092737, by rfl⟩ : syracuseStep 1456983 = 2185475) B2185475
theorem B1457003 : Blo 1455547 1457003 := bstep (se 1 (by rfl) ⟨1092752, by rfl⟩ : syracuseStep 1457003 = 2185505) B2185505
theorem B1457015 : Blo 1455547 1457015 := bstep (se 1 (by rfl) ⟨1092761, by rfl⟩ : syracuseStep 1457015 = 2185523) B2185523
theorem B1457035 : Blo 1455547 1457035 := bstep (se 1 (by rfl) ⟨1092776, by rfl⟩ : syracuseStep 1457035 = 2185553) B2185553
theorem B2186123 : Blo 1455547 2186123 := bstep (se 1 (by rfl) ⟨1639592, by rfl⟩ : syracuseStep 2186123 = 3279185) B3279185
theorem B1457047 : Blo 1455547 1457047 := bstep (se 1 (by rfl) ⟨1092785, by rfl⟩ : syracuseStep 1457047 = 2185571) B2185571
theorem B2186135 : Blo 1455547 2186135 := bstep (se 1 (by rfl) ⟨1639601, by rfl⟩ : syracuseStep 2186135 = 3279203) B3279203
theorem B2456473 : Blo 1455547 2456473 := bstep (se 2 (by rfl) ⟨921177, by rfl⟩ : syracuseStep 2456473 = 1842355) B1842355
theorem B1457067 : Blo 1455547 1457067 := bstep (se 1 (by rfl) ⟨1092800, by rfl⟩ : syracuseStep 1457067 = 2185601) B2185601
theorem B1457079 : Blo 1455547 1457079 := bstep (se 1 (by rfl) ⟨1092809, by rfl⟩ : syracuseStep 1457079 = 2185619) B2185619
theorem B1457099 : Blo 1455547 1457099 := bstep (se 1 (by rfl) ⟨1092824, by rfl⟩ : syracuseStep 1457099 = 2185649) B2185649
theorem B1457111 : Blo 1455547 1457111 := bstep (se 1 (by rfl) ⟨1092833, by rfl⟩ : syracuseStep 1457111 = 2185667) B2185667
theorem B25213913 : Blo 1455547 25213913 := bstep (se 2 (by rfl) ⟨9455217, by rfl⟩ : syracuseStep 25213913 = 18910435) B18910435
theorem B2186201 : Blo 1455547 2186201 := bstep (se 2 (by rfl) ⟨819825, by rfl⟩ : syracuseStep 2186201 = 1639651) B1639651
theorem B1457131 : Blo 1455547 1457131 := bstep (se 1 (by rfl) ⟨1092848, by rfl⟩ : syracuseStep 1457131 = 2185697) B2185697
theorem B1457143 : Blo 1455547 1457143 := bstep (se 1 (by rfl) ⟨1092857, by rfl⟩ : syracuseStep 1457143 = 2185715) B2185715
theorem B1457163 : Blo 1455547 1457163 := bstep (se 1 (by rfl) ⟨1092872, by rfl⟩ : syracuseStep 1457163 = 2185745) B2185745
theorem B12450833 : Blo 1455547 12450833 := bstep (se 2 (by rfl) ⟨4669062, by rfl⟩ : syracuseStep 12450833 = 9338125) B9338125
theorem B1457175 : Blo 1455547 1457175 := bstep (se 1 (by rfl) ⟨1092881, by rfl⟩ : syracuseStep 1457175 = 2185763) B2185763
theorem B3275801 : Blo 1455547 3275801 := bstep (se 2 (by rfl) ⟨1228425, by rfl⟩ : syracuseStep 3275801 = 2456851) B2456851
theorem B1457195 : Blo 1455547 1457195 := bstep (se 1 (by rfl) ⟨1092896, by rfl⟩ : syracuseStep 1457195 = 2185793) B2185793
theorem B1457207 : Blo 1455547 1457207 := bstep (se 1 (by rfl) ⟨1092905, by rfl⟩ : syracuseStep 1457207 = 2185811) B2185811
theorem B53869637 : Blo 1455547 53869637 := bstep (se 4 (by rfl) ⟨5050278, by rfl⟩ : syracuseStep 53869637 = 10100557) B10100557
theorem B1457227 : Blo 1455547 1457227 := bstep (se 1 (by rfl) ⟨1092920, by rfl⟩ : syracuseStep 1457227 = 2185841) B2185841
theorem B2186315 : Blo 1455547 2186315 := bstep (se 1 (by rfl) ⟨1639736, by rfl⟩ : syracuseStep 2186315 = 3279473) B3279473
theorem B1457239 : Blo 1455547 1457239 := bstep (se 1 (by rfl) ⟨1092929, by rfl⟩ : syracuseStep 1457239 = 2185859) B2185859
theorem B6306905 : Blo 1455547 6306905 := bstep (se 2 (by rfl) ⟨2365089, by rfl⟩ : syracuseStep 6306905 = 4730179) B4730179
theorem B4914269 : Blo 1455547 4914269 := bstep (se 3 (by rfl) ⟨921425, by rfl⟩ : syracuseStep 4914269 = 1842851) B1842851
theorem B1457259 : Blo 1455547 1457259 := bstep (se 1 (by rfl) ⟨1092944, by rfl⟩ : syracuseStep 1457259 = 2185889) B2185889
theorem B3275891 : Blo 1455547 3275891 := bstep (se 1 (by rfl) ⟨2456918, by rfl⟩ : syracuseStep 3275891 = 4913837) B4913837
theorem B1457271 : Blo 1455547 1457271 := bstep (se 1 (by rfl) ⟨1092953, by rfl⟩ : syracuseStep 1457271 = 2185907) B2185907
theorem B1457291 : Blo 1455547 1457291 := bstep (se 1 (by rfl) ⟨1092968, by rfl⟩ : syracuseStep 1457291 = 2185937) B2185937
theorem B1637527 : Blo 1455547 1637527 := bstep (se 1 (by rfl) ⟨1228145, by rfl⟩ : syracuseStep 1637527 = 2456291) B2456291
theorem B3275927 : Blo 1455547 3275927 := bstep (se 1 (by rfl) ⟨2456945, by rfl⟩ : syracuseStep 3275927 = 4913891) B4913891
theorem B1457303 : Blo 1455547 1457303 := bstep (se 1 (by rfl) ⟨1092977, by rfl⟩ : syracuseStep 1457303 = 2185955) B2185955
theorem B1457323 : Blo 1455547 1457323 := bstep (se 1 (by rfl) ⟨1092992, by rfl⟩ : syracuseStep 1457323 = 2185985) B2185985
theorem B1457335 : Blo 1455547 1457335 := bstep (se 1 (by rfl) ⟨1093001, by rfl⟩ : syracuseStep 1457335 = 2186003) B2186003
theorem B1457355 : Blo 1455547 1457355 := bstep (se 1 (by rfl) ⟨1093016, by rfl⟩ : syracuseStep 1457355 = 2186033) B2186033
theorem B1457367 : Blo 1455547 1457367 := bstep (se 1 (by rfl) ⟨1093025, by rfl⟩ : syracuseStep 1457367 = 2186051) B2186051
theorem B1457387 : Blo 1455547 1457387 := bstep (se 1 (by rfl) ⟨1093040, by rfl⟩ : syracuseStep 1457387 = 2186081) B2186081
theorem B1457399 : Blo 1455547 1457399 := bstep (se 1 (by rfl) ⟨1093049, by rfl⟩ : syracuseStep 1457399 = 2186099) B2186099
theorem B1457419 : Blo 1455547 1457419 := bstep (se 1 (by rfl) ⟨1093064, by rfl⟩ : syracuseStep 1457419 = 2186129) B2186129
theorem B1457431 : Blo 1455547 1457431 := bstep (se 1 (by rfl) ⟨1093073, by rfl⟩ : syracuseStep 1457431 = 2186147) B2186147
theorem B1457451 : Blo 1455547 1457451 := bstep (se 1 (by rfl) ⟨1093088, by rfl⟩ : syracuseStep 1457451 = 2186177) B2186177
theorem B1457463 : Blo 1455547 1457463 := bstep (se 1 (by rfl) ⟨1093097, by rfl⟩ : syracuseStep 1457463 = 2186195) B2186195
theorem B1637707 : Blo 1455547 1637707 := bstep (se 1 (by rfl) ⟨1228280, by rfl⟩ : syracuseStep 1637707 = 2456561) B2456561
theorem B3276107 : Blo 1455547 3276107 := bstep (se 1 (by rfl) ⟨2457080, by rfl⟩ : syracuseStep 3276107 = 4914161) B4914161
theorem B1457483 : Blo 1455547 1457483 := bstep (se 1 (by rfl) ⟨1093112, by rfl⟩ : syracuseStep 1457483 = 2186225) B2186225
theorem B1457495 : Blo 1455547 1457495 := bstep (se 1 (by rfl) ⟨1093121, by rfl⟩ : syracuseStep 1457495 = 2186243) B2186243
theorem B1457515 : Blo 1455547 1457515 := bstep (se 1 (by rfl) ⟨1093136, by rfl⟩ : syracuseStep 1457515 = 2186273) B2186273
theorem B1457527 : Blo 1455547 1457527 := bstep (se 1 (by rfl) ⟨1093145, by rfl⟩ : syracuseStep 1457527 = 2186291) B2186291
theorem B3276161 : Blo 1455547 3276161 := bstep (se 2 (by rfl) ⟨1228560, by rfl⟩ : syracuseStep 3276161 = 2457121) B2457121
theorem B1457547 : Blo 1455547 1457547 := bstep (se 1 (by rfl) ⟨1093160, by rfl⟩ : syracuseStep 1457547 = 2186321) B2186321
theorem B1842583 : Blo 1455547 1842583 := bstep (se 1 (by rfl) ⟨1381937, by rfl⟩ : syracuseStep 1842583 = 2763875) B2763875
theorem B3685783 : Blo 1455547 3685783 := bstep (se 1 (by rfl) ⟨2764337, by rfl⟩ : syracuseStep 3685783 = 5528675) B5528675
theorem B1637815 : Blo 1455547 1637815 := bstep (se 1 (by rfl) ⟨1228361, by rfl⟩ : syracuseStep 1637815 = 2456723) B2456723
theorem B2801099 : Blo 1455547 2801099 := bstep (se 1 (by rfl) ⟨2100824, by rfl⟩ : syracuseStep 2801099 = 4201649) B4201649
theorem B2457047 : Blo 1455547 2457047 := bstep (se 1 (by rfl) ⟨1842785, by rfl⟩ : syracuseStep 2457047 = 3685571) B3685571
theorem B3112435 : Blo 1455547 3112435 := bstep (se 1 (by rfl) ⟨2334326, by rfl⟩ : syracuseStep 3112435 = 4668653) B4668653
theorem B5250577 : Blo 1455547 5250577 := bstep (se 2 (by rfl) ⟨1968966, by rfl⟩ : syracuseStep 5250577 = 3937933) B3937933
theorem B2457175 : Blo 1455547 2457175 := bstep (se 1 (by rfl) ⟨1842881, by rfl⟩ : syracuseStep 2457175 = 3685763) B3685763
theorem B3276377 : Blo 1455547 3276377 := bstep (se 2 (by rfl) ⟨1228641, by rfl⟩ : syracuseStep 3276377 = 2457283) B2457283
theorem B1637995 : Blo 1455547 1637995 := bstep (se 1 (by rfl) ⟨1228496, by rfl⟩ : syracuseStep 1637995 = 2456993) B2456993
theorem B5250691 : Blo 1455547 5250691 := bstep (se 1 (by rfl) ⟨3938018, by rfl⟩ : syracuseStep 5250691 = 7876037) B7876037
theorem B28393091 : Blo 1455547 28393091 := bstep (se 1 (by rfl) ⟨21294818, by rfl⟩ : syracuseStep 28393091 = 42589637) B42589637
theorem B1556119 : Blo 1455547 1556119 := bstep (se 1 (by rfl) ⟨1167089, by rfl⟩ : syracuseStep 1556119 = 2334179) B2334179
theorem B3276467 : Blo 1455547 3276467 := bstep (se 1 (by rfl) ⟨2457350, by rfl⟩ : syracuseStep 3276467 = 4914701) B4914701
theorem B1638103 : Blo 1455547 1638103 := bstep (se 1 (by rfl) ⟨1228577, by rfl⟩ : syracuseStep 1638103 = 2457155) B2457155
theorem B3276503 : Blo 1455547 3276503 := bstep (se 1 (by rfl) ⟨2457377, by rfl⟩ : syracuseStep 3276503 = 4914755) B4914755
theorem B3686219 : Blo 1455547 3686219 := bstep (se 1 (by rfl) ⟨2764664, by rfl⟩ : syracuseStep 3686219 = 5529329) B5529329
theorem B7372619 : Blo 1455547 7372619 := bstep (se 1 (by rfl) ⟨5529464, by rfl⟩ : syracuseStep 7372619 = 11058929) B11058929
theorem B1638283 : Blo 1455547 1638283 := bstep (se 1 (by rfl) ⟨1228712, by rfl⟩ : syracuseStep 1638283 = 2457425) B2457425
theorem B3276683 : Blo 1455547 3276683 := bstep (se 1 (by rfl) ⟨2457512, by rfl⟩ : syracuseStep 3276683 = 4915025) B4915025
theorem B33611699 : Blo 1455547 33611699 := bstep (se 1 (by rfl) ⟨25208774, by rfl⟩ : syracuseStep 33611699 = 50417549) B50417549
theorem B3276737 : Blo 1455547 3276737 := bstep (se 2 (by rfl) ⟨1228776, by rfl⟩ : syracuseStep 3276737 = 2457553) B2457553
theorem B3112921 : Blo 1455547 3112921 := bstep (se 2 (by rfl) ⟨1167345, by rfl⟩ : syracuseStep 3112921 = 2334691) B2334691
theorem B1638391 : Blo 1455547 1638391 := bstep (se 1 (by rfl) ⟨1228793, by rfl⟩ : syracuseStep 1638391 = 2457587) B2457587
theorem B3686411 : Blo 1455547 3686411 := bstep (se 1 (by rfl) ⟨2764808, by rfl⟩ : syracuseStep 3686411 = 5529617) B5529617
theorem B4145185 : Blo 1455547 4145185 := bstep (se 2 (by rfl) ⟨1554444, by rfl⟩ : syracuseStep 4145185 = 3108889) B3108889
theorem B6217847 : Blo 1455547 6217847 := bstep (se 1 (by rfl) ⟨4663385, by rfl⟩ : syracuseStep 6217847 = 9326771) B9326771
theorem B3276935 : Blo 1455547 3276935 := bstep (se 1 (by rfl) ⟨2457701, by rfl⟩ : syracuseStep 3276935 = 4915403) B4915403
theorem B1638535 : Blo 1455547 1638535 := bstep (se 1 (by rfl) ⟨1228901, by rfl⟩ : syracuseStep 1638535 = 2457803) B2457803
theorem B4915457 : Blo 1455547 4915457 := bstep (se 2 (by rfl) ⟨1843296, by rfl⟩ : syracuseStep 4915457 = 3686593) B3686593
theorem B1843499 : Blo 1455547 1843499 := bstep (se 1 (by rfl) ⟨1382624, by rfl⟩ : syracuseStep 1843499 = 2765249) B2765249
theorem B3277115 : Blo 1455547 3277115 := bstep (se 1 (by rfl) ⟨2457836, by rfl⟩ : syracuseStep 3277115 = 4915673) B4915673
theorem B1638715 : Blo 1455547 1638715 := bstep (se 1 (by rfl) ⟨1229036, by rfl⟩ : syracuseStep 1638715 = 2458073) B2458073
theorem B3277241 : Blo 1455547 3277241 := bstep (se 2 (by rfl) ⟨1228965, by rfl⟩ : syracuseStep 3277241 = 2457931) B2457931
theorem B8290781 : Blo 1455547 8290781 := bstep (se 3 (by rfl) ⟨1554521, by rfl⟩ : syracuseStep 8290781 = 3109043) B3109043
theorem B2458127 : Blo 1455547 2458127 := bstep (se 1 (by rfl) ⟨1843595, by rfl⟩ : syracuseStep 2458127 = 3687191) B3687191
theorem B3687059 : Blo 1455547 3687059 := bstep (se 1 (by rfl) ⟨2765294, by rfl⟩ : syracuseStep 3687059 = 5530589) B5530589
theorem B15966899 : Blo 1455547 15966899 := bstep (se 1 (by rfl) ⟨11975174, by rfl⟩ : syracuseStep 15966899 = 23950349) B23950349
theorem B15958745 : Blo 1455547 15958745 := bstep (se 2 (by rfl) ⟨5984529, by rfl⟩ : syracuseStep 15958745 = 11969059) B11969059
theorem B1843975 : Blo 1455547 1843975 := bstep (se 1 (by rfl) ⟨1382981, by rfl⟩ : syracuseStep 1843975 = 2765963) B2765963
theorem B3277583 : Blo 1455547 3277583 := bstep (se 1 (by rfl) ⟨2458187, by rfl⟩ : syracuseStep 3277583 = 4916375) B4916375
theorem B1639183 : Blo 1455547 1639183 := bstep (se 1 (by rfl) ⟨1229387, by rfl⟩ : syracuseStep 1639183 = 2458775) B2458775
theorem B3277601 : Blo 1455547 3277601 := bstep (se 2 (by rfl) ⟨1229100, by rfl⟩ : syracuseStep 3277601 = 2458201) B2458201
theorem B7373753 : Blo 1455547 7373753 := bstep (se 2 (by rfl) ⟨2765157, by rfl⟩ : syracuseStep 7373753 = 5530315) B5530315
theorem B3687353 : Blo 1455547 3687353 := bstep (se 2 (by rfl) ⟨1382757, by rfl⟩ : syracuseStep 3687353 = 2765515) B2765515
theorem B8291281 : Blo 1455547 8291281 := bstep (se 2 (by rfl) ⟨3109230, by rfl⟩ : syracuseStep 8291281 = 6218461) B6218461
theorem B4916267 : Blo 1455547 4916267 := bstep (se 1 (by rfl) ⟨3687200, by rfl⟩ : syracuseStep 4916267 = 7374401) B7374401
theorem B2458667 : Blo 1455547 2458667 := bstep (se 1 (by rfl) ⟨1844000, by rfl⟩ : syracuseStep 2458667 = 3688001) B3688001
theorem B3277943 : Blo 1455547 3277943 := bstep (se 1 (by rfl) ⟨2458457, by rfl⟩ : syracuseStep 3277943 = 4916915) B4916915
theorem B3499193 : Blo 1455547 3499193 := bstep (se 2 (by rfl) ⟨1312197, by rfl⟩ : syracuseStep 3499193 = 2624395) B2624395
theorem B16581833 : Blo 1455547 16581833 := bstep (se 2 (by rfl) ⟨6218187, by rfl⟩ : syracuseStep 16581833 = 12436375) B12436375
theorem B1844471 : Blo 1455547 1844471 := bstep (se 1 (by rfl) ⟨1383353, by rfl⟩ : syracuseStep 1844471 = 2766707) B2766707
theorem B2073863 : Blo 1455547 2073863 := bstep (se 1 (by rfl) ⟨1555397, by rfl⟩ : syracuseStep 2073863 = 3110795) B3110795
theorem B1639687 : Blo 1455547 1639687 := bstep (se 1 (by rfl) ⟨1229765, by rfl⟩ : syracuseStep 1639687 = 2459531) B2459531
theorem B4146461 : Blo 1455547 4146461 := bstep (se 3 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 4146461 = 1554923) B1554923
theorem B6645025 : Blo 1455547 6645025 := bstep (se 2 (by rfl) ⟨2491884, by rfl⟩ : syracuseStep 6645025 = 4983769) B4983769
theorem B3278123 : Blo 1455547 3278123 := bstep (se 1 (by rfl) ⟨2458592, by rfl⟩ : syracuseStep 3278123 = 4917185) B4917185
theorem B1844623 : Blo 1455547 1844623 := bstep (se 1 (by rfl) ⟨1383467, by rfl⟩ : syracuseStep 1844623 = 2766935) B2766935
theorem B3786169 : Blo 1455547 3786169 := bstep (se 2 (by rfl) ⟨1419813, by rfl⟩ : syracuseStep 3786169 = 2839627) B2839627
theorem B2459065 : Blo 1455547 2459065 := bstep (se 2 (by rfl) ⟨922149, by rfl⟩ : syracuseStep 2459065 = 1844299) B1844299
theorem B4146689 : Blo 1455547 4146689 := bstep (se 2 (by rfl) ⟨1555008, by rfl⟩ : syracuseStep 4146689 = 3110017) B3110017
theorem B4204075 : Blo 1455547 4204075 := bstep (se 1 (by rfl) ⟨3153056, by rfl⟩ : syracuseStep 4204075 = 6306113) B6306113
theorem B3688051 : Blo 1455547 3688051 := bstep (se 1 (by rfl) ⟨2766038, by rfl⟩ : syracuseStep 3688051 = 5532077) B5532077
theorem B3278483 : Blo 1455547 3278483 := bstep (se 1 (by rfl) ⟨2458862, by rfl⟩ : syracuseStep 3278483 = 4917725) B4917725
theorem B3278537 : Blo 1455547 3278537 := bstep (se 2 (by rfl) ⟨1229451, by rfl⟩ : syracuseStep 3278537 = 2458903) B2458903
theorem B3688193 : Blo 1455547 3688193 := bstep (se 2 (by rfl) ⟨1383072, by rfl⟩ : syracuseStep 3688193 = 2766145) B2766145
theorem B8300303 : Blo 1455547 8300303 := bstep (se 1 (by rfl) ⟨6225227, by rfl⟩ : syracuseStep 8300303 = 12450455) B12450455
theorem B4147031 : Blo 1455547 4147031 := bstep (se 1 (by rfl) ⟨3110273, by rfl⟩ : syracuseStep 4147031 = 6220547) B6220547
theorem B127739749 : Blo 1455547 127739749 := bstep (se 4 (by rfl) ⟨11975601, by rfl⟩ : syracuseStep 127739749 = 23951203) B23951203
theorem B4147145 : Blo 1455547 4147145 := bstep (se 2 (by rfl) ⟨1555179, by rfl⟩ : syracuseStep 4147145 = 3110359) B3110359
theorem B8300555 : Blo 1455547 8300555 := bstep (se 1 (by rfl) ⟨6225416, by rfl⟩ : syracuseStep 8300555 = 12450833) B12450833
theorem B4204603 : Blo 1455547 4204603 := bstep (se 1 (by rfl) ⟨3153452, by rfl⟩ : syracuseStep 4204603 = 6306905) B6306905
theorem B7375049 : Blo 1455547 7375049 := bstep (se 2 (by rfl) ⟨2765643, by rfl⟩ : syracuseStep 7375049 = 5531287) B5531287
theorem B2074825 : Blo 1455547 2074825 := bstep (se 2 (by rfl) ⟨778059, by rfl⟩ : syracuseStep 2074825 = 1556119) B1556119
theorem B3688649 : Blo 1455547 3688649 := bstep (se 2 (by rfl) ⟨1383243, by rfl⟩ : syracuseStep 3688649 = 2766487) B2766487
theorem B16599329 : Blo 1455547 16599329 := bstep (se 2 (by rfl) ⟨6224748, by rfl⟩ : syracuseStep 16599329 = 12449497) B12449497
theorem B4917563 : Blo 1455547 4917563 := bstep (se 1 (by rfl) ⟨3688172, by rfl⟩ : syracuseStep 4917563 = 7376345) B7376345
theorem B3279239 : Blo 1455547 3279239 := bstep (se 1 (by rfl) ⟨2459429, by rfl⟩ : syracuseStep 3279239 = 4918859) B4918859
theorem B89631197 : Blo 1455547 89631197 := bstep (se 3 (by rfl) ⟨16805849, by rfl⟩ : syracuseStep 89631197 = 33611699) B33611699
theorem B4426283 : Blo 1455547 4426283 := bstep (se 1 (by rfl) ⟨3319712, by rfl⟩ : syracuseStep 4426283 = 6639425) B6639425
theorem B3689003 : Blo 1455547 3689003 := bstep (se 1 (by rfl) ⟨2766752, by rfl⟩ : syracuseStep 3689003 = 5533505) B5533505
theorem B3279419 : Blo 1455547 3279419 := bstep (se 1 (by rfl) ⟨2459564, by rfl⟩ : syracuseStep 3279419 = 4919129) B4919129
theorem B4918049 : Blo 1455547 4918049 := bstep (se 2 (by rfl) ⟨1844268, by rfl⟩ : syracuseStep 4918049 = 3688537) B3688537
theorem B2952055 : Blo 1455547 2952055 := bstep (se 1 (by rfl) ⟨2214041, by rfl⟩ : syracuseStep 2952055 = 4428083) B4428083
theorem B8293265 : Blo 1455547 8293265 := bstep (se 2 (by rfl) ⟨3109974, by rfl⟩ : syracuseStep 8293265 = 6219949) B6219949
theorem B5532563 : Blo 1455547 5532563 := bstep (se 1 (by rfl) ⟨4149422, by rfl⟩ : syracuseStep 5532563 = 8298845) B8298845
theorem B2763791 : Blo 1455547 2763791 := bstep (se 1 (by rfl) ⟨2072843, by rfl⟩ : syracuseStep 2763791 = 4145687) B4145687
theorem B3935293 : Blo 1455547 3935293 := bstep (se 3 (by rfl) ⟨737867, by rfl⟩ : syracuseStep 3935293 = 1475735) B1475735
theorem B5909591 : Blo 1455547 5909591 := bstep (se 1 (by rfl) ⟨4432193, by rfl⟩ : syracuseStep 5909591 = 8864387) B8864387
theorem B3738739 : Blo 1455547 3738739 := bstep (se 1 (by rfl) ⟨2804054, by rfl⟩ : syracuseStep 3738739 = 5608109) B5608109
theorem B3501191 : Blo 1455547 3501191 := bstep (se 1 (by rfl) ⟨2625893, by rfl⟩ : syracuseStep 3501191 = 5251787) B5251787
theorem B17968301 : Blo 1455547 17968301 := bstep (se 3 (by rfl) ⟨3369056, by rfl⟩ : syracuseStep 17968301 = 6738113) B6738113
theorem B4664591 : Blo 1455547 4664591 := bstep (se 1 (by rfl) ⟨3498443, by rfl⟩ : syracuseStep 4664591 = 6996887) B6996887
theorem B3935575 : Blo 1455547 3935575 := bstep (se 1 (by rfl) ⟨2951681, by rfl⟩ : syracuseStep 3935575 = 5903363) B5903363
theorem B4918643 : Blo 1455547 4918643 := bstep (se 1 (by rfl) ⟨3688982, by rfl⟩ : syracuseStep 4918643 = 7377965) B7377965
theorem B4664861 : Blo 1455547 4664861 := bstep (se 3 (by rfl) ⟨874661, by rfl⟩ : syracuseStep 4664861 = 1749323) B1749323
theorem B3501721 : Blo 1455547 3501721 := bstep (se 2 (by rfl) ⟨1313145, by rfl⟩ : syracuseStep 3501721 = 2626291) B2626291
theorem B4148921 : Blo 1455547 4148921 := bstep (se 2 (by rfl) ⟨1555845, by rfl⟩ : syracuseStep 4148921 = 3111691) B3111691
theorem B15757091 : Blo 1455547 15757091 := bstep (se 1 (by rfl) ⟨11817818, by rfl⟩ : syracuseStep 15757091 = 23635637) B23635637
theorem B3501883 : Blo 1455547 3501883 := bstep (se 1 (by rfl) ⟨2626412, by rfl⟩ : syracuseStep 3501883 = 5252825) B5252825
theorem B3321719 : Blo 1455547 3321719 := bstep (se 1 (by rfl) ⟨2491289, by rfl⟩ : syracuseStep 3321719 = 4982579) B4982579
theorem B1822711 : Blo 1455547 1822711 := bstep (se 1 (by rfl) ⟨1367033, by rfl⟩ : syracuseStep 1822711 = 2734067) B2734067
theorem B5394443 : Blo 1455547 5394443 := bstep (se 1 (by rfl) ⟨4045832, by rfl⟩ : syracuseStep 5394443 = 8091665) B8091665
theorem B3936289 : Blo 1455547 3936289 := bstep (se 2 (by rfl) ⟨1476108, by rfl⟩ : syracuseStep 3936289 = 2952217) B2952217
theorem B16584749 : Blo 1455547 16584749 := bstep (se 3 (by rfl) ⟨3109640, by rfl⟩ : syracuseStep 16584749 = 6219281) B6219281
theorem B2183339 : Blo 1455547 2183339 := bstep (se 1 (by rfl) ⟨1637504, by rfl⟩ : syracuseStep 2183339 = 3275009) B3275009
theorem B2183369 : Blo 1455547 2183369 := bstep (se 2 (by rfl) ⟨818763, by rfl⟩ : syracuseStep 2183369 = 1637527) B1637527
theorem B2953417 : Blo 1455547 2953417 := bstep (se 2 (by rfl) ⟨1107531, by rfl⟩ : syracuseStep 2953417 = 2215063) B2215063
theorem B2183483 : Blo 1455547 2183483 := bstep (se 1 (by rfl) ⟨1637612, by rfl⟩ : syracuseStep 2183483 = 3275225) B3275225
theorem B2183543 : Blo 1455547 2183543 := bstep (se 1 (by rfl) ⟨1637657, by rfl⟩ : syracuseStep 2183543 = 3275315) B3275315
theorem B2183567 : Blo 1455547 2183567 := bstep (se 1 (by rfl) ⟨1637675, by rfl⟩ : syracuseStep 2183567 = 3275351) B3275351
theorem B2183609 : Blo 1455547 2183609 := bstep (se 2 (by rfl) ⟨818853, by rfl⟩ : syracuseStep 2183609 = 1637707) B1637707
theorem B2183687 : Blo 1455547 2183687 := bstep (se 1 (by rfl) ⟨1637765, by rfl⟩ : syracuseStep 2183687 = 3275531) B3275531
theorem B2183723 : Blo 1455547 2183723 := bstep (se 1 (by rfl) ⟨1637792, by rfl⟩ : syracuseStep 2183723 = 3275585) B3275585
theorem B16822849 : Blo 1455547 16822849 := bstep (se 2 (by rfl) ⟨6308568, by rfl⟩ : syracuseStep 16822849 = 12617137) B12617137
theorem B2183753 : Blo 1455547 2183753 := bstep (se 2 (by rfl) ⟨818907, by rfl⟩ : syracuseStep 2183753 = 1637815) B1637815
theorem B1995337 : Blo 1455547 1995337 := bstep (se 2 (by rfl) ⟨748251, by rfl⟩ : syracuseStep 1995337 = 1496503) B1496503
theorem B2765431 : Blo 1455547 2765431 := bstep (se 1 (by rfl) ⟨2074073, by rfl⟩ : syracuseStep 2765431 = 4148147) B4148147
theorem B4149913 : Blo 1455547 4149913 := bstep (se 2 (by rfl) ⟨1556217, by rfl⟩ : syracuseStep 4149913 = 3112435) B3112435
theorem B2183867 : Blo 1455547 2183867 := bstep (se 1 (by rfl) ⟨1637900, by rfl⟩ : syracuseStep 2183867 = 3275801) B3275801
theorem B7000769 : Blo 1455547 7000769 := bstep (se 2 (by rfl) ⟨2625288, by rfl⟩ : syracuseStep 7000769 = 5250577) B5250577
theorem B2183927 : Blo 1455547 2183927 := bstep (se 1 (by rfl) ⟨1637945, by rfl⟩ : syracuseStep 2183927 = 3275891) B3275891
theorem B3937025 : Blo 1455547 3937025 := bstep (se 2 (by rfl) ⟨1476384, by rfl⟩ : syracuseStep 3937025 = 2952769) B2952769
theorem B2183951 : Blo 1455547 2183951 := bstep (se 1 (by rfl) ⟨1637963, by rfl⟩ : syracuseStep 2183951 = 3275927) B3275927
theorem B2183993 : Blo 1455547 2183993 := bstep (se 2 (by rfl) ⟨818997, by rfl⟩ : syracuseStep 2183993 = 1637995) B1637995
theorem B7000921 : Blo 1455547 7000921 := bstep (se 2 (by rfl) ⟨2625345, by rfl⟩ : syracuseStep 7000921 = 5250691) B5250691
theorem B2184071 : Blo 1455547 2184071 := bstep (se 1 (by rfl) ⟨1638053, by rfl⟩ : syracuseStep 2184071 = 3276107) B3276107
theorem B2184107 : Blo 1455547 2184107 := bstep (se 1 (by rfl) ⟨1638080, by rfl⟩ : syracuseStep 2184107 = 3276161) B3276161
theorem B2184137 : Blo 1455547 2184137 := bstep (se 2 (by rfl) ⟨819051, by rfl⟩ : syracuseStep 2184137 = 1638103) B1638103
theorem B2184251 : Blo 1455547 2184251 := bstep (se 1 (by rfl) ⟨1638188, by rfl⟩ : syracuseStep 2184251 = 3276377) B3276377
theorem B18928727 : Blo 1455547 18928727 := bstep (se 1 (by rfl) ⟨14196545, by rfl⟩ : syracuseStep 18928727 = 28393091) B28393091
theorem B2184311 : Blo 1455547 2184311 := bstep (se 1 (by rfl) ⟨1638233, by rfl⟩ : syracuseStep 2184311 = 3276467) B3276467
theorem B16602245 : Blo 1455547 16602245 := bstep (se 4 (by rfl) ⟨1556460, by rfl⟩ : syracuseStep 16602245 = 3112921) B3112921
theorem B2184335 : Blo 1455547 2184335 := bstep (se 1 (by rfl) ⟨1638251, by rfl⟩ : syracuseStep 2184335 = 3276503) B3276503
theorem B12440749 : Blo 1455547 12440749 := bstep (se 3 (by rfl) ⟨2332640, by rfl⟩ : syracuseStep 12440749 = 4665281) B4665281
theorem B2184377 : Blo 1455547 2184377 := bstep (se 2 (by rfl) ⟨819141, by rfl⟩ : syracuseStep 2184377 = 1638283) B1638283
theorem B2184455 : Blo 1455547 2184455 := bstep (se 1 (by rfl) ⟨1638341, by rfl⟩ : syracuseStep 2184455 = 3276683) B3276683
theorem B2184491 : Blo 1455547 2184491 := bstep (se 1 (by rfl) ⟨1638368, by rfl⟩ : syracuseStep 2184491 = 3276737) B3276737
theorem B2184521 : Blo 1455547 2184521 := bstep (se 2 (by rfl) ⟨819195, by rfl⟩ : syracuseStep 2184521 = 1638391) B1638391
theorem B29898085 : Blo 1455547 29898085 := bstep (se 4 (by rfl) ⟨2802945, by rfl⟩ : syracuseStep 29898085 = 5605891) B5605891
theorem B5526899 : Blo 1455547 5526899 := bstep (se 1 (by rfl) ⟨4145174, by rfl⟩ : syracuseStep 5526899 = 8290349) B8290349
theorem B11064761 : Blo 1455547 11064761 := bstep (se 2 (by rfl) ⟨4149285, by rfl⟩ : syracuseStep 11064761 = 8298571) B8298571
theorem B1455547 : Blo 1455547 1455547 := bstep (se 1 (by rfl) ⟨1091660, by rfl⟩ : syracuseStep 1455547 = 2183321) B2183321
theorem B2184635 : Blo 1455547 2184635 := bstep (se 1 (by rfl) ⟨1638476, by rfl⟩ : syracuseStep 2184635 = 3276953) B3276953
theorem B10499537 : Blo 1455547 10499537 := bstep (se 2 (by rfl) ⟨3937326, by rfl⟩ : syracuseStep 10499537 = 7874653) B7874653
theorem B2184695 : Blo 1455547 2184695 := bstep (se 1 (by rfl) ⟨1638521, by rfl⟩ : syracuseStep 2184695 = 3277043) B3277043
theorem B1750519 : Blo 1455547 1750519 := bstep (se 1 (by rfl) ⟨1312889, by rfl⟩ : syracuseStep 1750519 = 2625779) B2625779
theorem B1455623 : Blo 1455547 1455623 := bstep (se 1 (by rfl) ⟨1091717, by rfl⟩ : syracuseStep 1455623 = 2183435) B2183435
theorem B143652365 : Blo 1455547 143652365 := bstep (se 3 (by rfl) ⟨26934818, by rfl⟩ : syracuseStep 143652365 = 53869637) B53869637
theorem B1455631 : Blo 1455547 1455631 := bstep (se 1 (by rfl) ⟨1091723, by rfl⟩ : syracuseStep 1455631 = 2183447) B2183447
theorem B2184719 : Blo 1455547 2184719 := bstep (se 1 (by rfl) ⟨1638539, by rfl⟩ : syracuseStep 2184719 = 3277079) B3277079
theorem B3937825 : Blo 1455547 3937825 := bstep (se 2 (by rfl) ⟨1476684, by rfl⟩ : syracuseStep 3937825 = 2953369) B2953369
theorem B2184761 : Blo 1455547 2184761 := bstep (se 2 (by rfl) ⟨819285, by rfl⟩ : syracuseStep 2184761 = 1638571) B1638571
theorem B1455675 : Blo 1455547 1455675 := bstep (se 1 (by rfl) ⟨1091756, by rfl⟩ : syracuseStep 1455675 = 2183513) B2183513
theorem B14956109 : Blo 1455547 14956109 := bstep (se 3 (by rfl) ⟨2804270, by rfl⟩ : syracuseStep 14956109 = 5608541) B5608541
theorem B1455751 : Blo 1455547 1455751 := bstep (se 1 (by rfl) ⟨1091813, by rfl⟩ : syracuseStep 1455751 = 2183627) B2183627
theorem B2184839 : Blo 1455547 2184839 := bstep (se 1 (by rfl) ⟨1638629, by rfl⟩ : syracuseStep 2184839 = 3277259) B3277259
theorem B1455759 : Blo 1455547 1455759 := bstep (se 1 (by rfl) ⟨1091819, by rfl⟩ : syracuseStep 1455759 = 2183639) B2183639
theorem B2184875 : Blo 1455547 2184875 := bstep (se 1 (by rfl) ⟨1638656, by rfl⟩ : syracuseStep 2184875 = 3277313) B3277313
theorem B1455803 : Blo 1455547 1455803 := bstep (se 1 (by rfl) ⟨1091852, by rfl⟩ : syracuseStep 1455803 = 2183705) B2183705
theorem B2184905 : Blo 1455547 2184905 := bstep (se 2 (by rfl) ⟨819339, by rfl⟩ : syracuseStep 2184905 = 1638679) B1638679
theorem B35452673 : Blo 1455547 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B1455879 : Blo 1455547 1455879 := bstep (se 1 (by rfl) ⟨1091909, by rfl⟩ : syracuseStep 1455879 = 2183819) B2183819
theorem B1455887 : Blo 1455547 1455887 := bstep (se 1 (by rfl) ⟨1091915, by rfl⟩ : syracuseStep 1455887 = 2183831) B2183831
theorem B1455931 : Blo 1455547 1455931 := bstep (se 1 (by rfl) ⟨1091948, by rfl⟩ : syracuseStep 1455931 = 2183897) B2183897
theorem B2185019 : Blo 1455547 2185019 := bstep (se 1 (by rfl) ⟨1638764, by rfl⟩ : syracuseStep 2185019 = 3277529) B3277529
theorem B11056985 : Blo 1455547 11056985 := bstep (se 2 (by rfl) ⟨4146369, by rfl⟩ : syracuseStep 11056985 = 8292739) B8292739
theorem B2185079 : Blo 1455547 2185079 := bstep (se 1 (by rfl) ⟨1638809, by rfl⟩ : syracuseStep 2185079 = 3277619) B3277619
theorem B1456007 : Blo 1455547 1456007 := bstep (se 1 (by rfl) ⟨1092005, by rfl⟩ : syracuseStep 1456007 = 2184011) B2184011
theorem B5248903 : Blo 1455547 5248903 := bstep (se 1 (by rfl) ⟨3936677, by rfl⟩ : syracuseStep 5248903 = 7873355) B7873355
theorem B1456015 : Blo 1455547 1456015 := bstep (se 1 (by rfl) ⟨1092011, by rfl⟩ : syracuseStep 1456015 = 2184023) B2184023
theorem B2185103 : Blo 1455547 2185103 := bstep (se 1 (by rfl) ⟨1638827, by rfl⟩ : syracuseStep 2185103 = 3277655) B3277655
theorem B4913081 : Blo 1455547 4913081 := bstep (se 2 (by rfl) ⟨1842405, by rfl⟩ : syracuseStep 4913081 = 3684811) B3684811
theorem B2185145 : Blo 1455547 2185145 := bstep (se 2 (by rfl) ⟨819429, by rfl⟩ : syracuseStep 2185145 = 1638859) B1638859
theorem B1456059 : Blo 1455547 1456059 := bstep (se 1 (by rfl) ⟨1092044, by rfl⟩ : syracuseStep 1456059 = 2184089) B2184089
theorem B4667321 : Blo 1455547 4667321 := bstep (se 2 (by rfl) ⟨1750245, by rfl⟩ : syracuseStep 4667321 = 3500491) B3500491
theorem B1456135 : Blo 1455547 1456135 := bstep (se 1 (by rfl) ⟨1092101, by rfl⟩ : syracuseStep 1456135 = 2184203) B2184203
theorem B2185223 : Blo 1455547 2185223 := bstep (se 1 (by rfl) ⟨1638917, by rfl⟩ : syracuseStep 2185223 = 3277835) B3277835
theorem B16594955 : Blo 1455547 16594955 := bstep (se 1 (by rfl) ⟨12446216, by rfl⟩ : syracuseStep 16594955 = 24892433) B24892433
theorem B1456143 : Blo 1455547 1456143 := bstep (se 1 (by rfl) ⟨1092107, by rfl⟩ : syracuseStep 1456143 = 2184215) B2184215
theorem B2185259 : Blo 1455547 2185259 := bstep (se 1 (by rfl) ⟨1638944, by rfl⟩ : syracuseStep 2185259 = 3277889) B3277889
theorem B4667435 : Blo 1455547 4667435 := bstep (se 1 (by rfl) ⟨3500576, by rfl⟩ : syracuseStep 4667435 = 7001153) B7001153
theorem B1456187 : Blo 1455547 1456187 := bstep (se 1 (by rfl) ⟨1092140, by rfl⟩ : syracuseStep 1456187 = 2184281) B2184281
theorem B4429883 : Blo 1455547 4429883 := bstep (se 1 (by rfl) ⟨3322412, by rfl⟩ : syracuseStep 4429883 = 6644825) B6644825
theorem B2185289 : Blo 1455547 2185289 := bstep (se 2 (by rfl) ⟨819483, by rfl⟩ : syracuseStep 2185289 = 1638967) B1638967
theorem B3684467 : Blo 1455547 3684467 := bstep (se 1 (by rfl) ⟨2763350, by rfl⟩ : syracuseStep 3684467 = 5526701) B5526701
theorem B3684487 : Blo 1455547 3684487 := bstep (se 1 (by rfl) ⟨2763365, by rfl⟩ : syracuseStep 3684487 = 5526731) B5526731
theorem B1456263 : Blo 1455547 1456263 := bstep (se 1 (by rfl) ⟨1092197, by rfl⟩ : syracuseStep 1456263 = 2184395) B2184395
theorem B1456271 : Blo 1455547 1456271 := bstep (se 1 (by rfl) ⟨1092203, by rfl⟩ : syracuseStep 1456271 = 2184407) B2184407
theorem B1456315 : Blo 1455547 1456315 := bstep (se 1 (by rfl) ⟨1092236, by rfl⟩ : syracuseStep 1456315 = 2184473) B2184473
theorem B2185403 : Blo 1455547 2185403 := bstep (se 1 (by rfl) ⟨1639052, by rfl⟩ : syracuseStep 2185403 = 3278105) B3278105
theorem B2185463 : Blo 1455547 2185463 := bstep (se 1 (by rfl) ⟨1639097, by rfl⟩ : syracuseStep 2185463 = 3278195) B3278195
theorem B1456391 : Blo 1455547 1456391 := bstep (se 1 (by rfl) ⟨1092293, by rfl⟩ : syracuseStep 1456391 = 2184587) B2184587
theorem B1456399 : Blo 1455547 1456399 := bstep (se 1 (by rfl) ⟨1092299, by rfl⟩ : syracuseStep 1456399 = 2184599) B2184599
theorem B2185487 : Blo 1455547 2185487 := bstep (se 1 (by rfl) ⟨1639115, by rfl⟩ : syracuseStep 2185487 = 3278231) B3278231
theorem B2185529 : Blo 1455547 2185529 := bstep (se 2 (by rfl) ⟨819573, by rfl⟩ : syracuseStep 2185529 = 1639147) B1639147
theorem B1456443 : Blo 1455547 1456443 := bstep (se 1 (by rfl) ⟨1092332, by rfl⟩ : syracuseStep 1456443 = 2184665) B2184665
theorem B1456519 : Blo 1455547 1456519 := bstep (se 1 (by rfl) ⟨1092389, by rfl⟩ : syracuseStep 1456519 = 2184779) B2184779
theorem B2185607 : Blo 1455547 2185607 := bstep (se 1 (by rfl) ⟨1639205, by rfl⟩ : syracuseStep 2185607 = 3278411) B3278411
theorem B1456527 : Blo 1455547 1456527 := bstep (se 1 (by rfl) ⟨1092395, by rfl⟩ : syracuseStep 1456527 = 2184791) B2184791
theorem B25221521 : Blo 1455547 25221521 := bstep (se 2 (by rfl) ⟨9458070, by rfl⟩ : syracuseStep 25221521 = 18916141) B18916141
theorem B3684761 : Blo 1455547 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B7371161 : Blo 1455547 7371161 := bstep (se 2 (by rfl) ⟨2764185, by rfl⟩ : syracuseStep 7371161 = 5528371) B5528371
theorem B2185643 : Blo 1455547 2185643 := bstep (se 1 (by rfl) ⟨1639232, by rfl⟩ : syracuseStep 2185643 = 3278465) B3278465
theorem B1456571 : Blo 1455547 1456571 := bstep (se 1 (by rfl) ⟨1092428, by rfl⟩ : syracuseStep 1456571 = 2184857) B2184857
theorem B2185673 : Blo 1455547 2185673 := bstep (se 2 (by rfl) ⟨819627, by rfl⟩ : syracuseStep 2185673 = 1639255) B1639255
theorem B10639837 : Blo 1455547 10639837 := bstep (se 3 (by rfl) ⟨1994969, by rfl⟩ : syracuseStep 10639837 = 3989939) B3989939
theorem B1456647 : Blo 1455547 1456647 := bstep (se 1 (by rfl) ⟨1092485, by rfl⟩ : syracuseStep 1456647 = 2184971) B2184971
theorem B4913675 : Blo 1455547 4913675 := bstep (se 1 (by rfl) ⟨3685256, by rfl⟩ : syracuseStep 4913675 = 7370513) B7370513
theorem B3275279 : Blo 1455547 3275279 := bstep (se 1 (by rfl) ⟨2456459, by rfl⟩ : syracuseStep 3275279 = 4912919) B4912919
theorem B1456655 : Blo 1455547 1456655 := bstep (se 1 (by rfl) ⟨1092491, by rfl⟩ : syracuseStep 1456655 = 2184983) B2184983
theorem B3938831 : Blo 1455547 3938831 := bstep (se 1 (by rfl) ⟨2954123, by rfl⟩ : syracuseStep 3938831 = 5908247) B5908247
theorem B7469597 : Blo 1455547 7469597 := bstep (se 3 (by rfl) ⟨1400549, by rfl⟩ : syracuseStep 7469597 = 2801099) B2801099
theorem B3275297 : Blo 1455547 3275297 := bstep (se 2 (by rfl) ⟨1228236, by rfl⟩ : syracuseStep 3275297 = 2456473) B2456473
theorem B3684923 : Blo 1455547 3684923 := bstep (se 1 (by rfl) ⟨2763692, by rfl⟩ : syracuseStep 3684923 = 5527385) B5527385
theorem B1456699 : Blo 1455547 1456699 := bstep (se 1 (by rfl) ⟨1092524, by rfl⟩ : syracuseStep 1456699 = 2185049) B2185049
theorem B2185787 : Blo 1455547 2185787 := bstep (se 1 (by rfl) ⟨1639340, by rfl⟩ : syracuseStep 2185787 = 3278681) B3278681
theorem B4913783 : Blo 1455547 4913783 := bstep (se 1 (by rfl) ⟨3685337, by rfl⟩ : syracuseStep 4913783 = 7370675) B7370675
theorem B2185847 : Blo 1455547 2185847 := bstep (se 1 (by rfl) ⟨1639385, by rfl⟩ : syracuseStep 2185847 = 3278771) B3278771
theorem B1456775 : Blo 1455547 1456775 := bstep (se 1 (by rfl) ⟨1092581, by rfl⟩ : syracuseStep 1456775 = 2185163) B2185163
theorem B1456783 : Blo 1455547 1456783 := bstep (se 1 (by rfl) ⟨1092587, by rfl⟩ : syracuseStep 1456783 = 2185175) B2185175
theorem B2185871 : Blo 1455547 2185871 := bstep (se 1 (by rfl) ⟨1639403, by rfl⟩ : syracuseStep 2185871 = 3278807) B3278807
theorem B2185913 : Blo 1455547 2185913 := bstep (se 2 (by rfl) ⟨819717, by rfl⟩ : syracuseStep 2185913 = 1639435) B1639435
theorem B1456827 : Blo 1455547 1456827 := bstep (se 1 (by rfl) ⟨1092620, by rfl⟩ : syracuseStep 1456827 = 2185241) B2185241
theorem B5905133 : Blo 1455547 5905133 := bstep (se 3 (by rfl) ⟨1107212, by rfl⟩ : syracuseStep 5905133 = 2214425) B2214425
theorem B1456903 : Blo 1455547 1456903 := bstep (se 1 (by rfl) ⟨1092677, by rfl⟩ : syracuseStep 1456903 = 2185355) B2185355
theorem B2185991 : Blo 1455547 2185991 := bstep (se 1 (by rfl) ⟨1639493, by rfl⟩ : syracuseStep 2185991 = 3278987) B3278987
theorem B3685135 : Blo 1455547 3685135 := bstep (se 1 (by rfl) ⟨2763851, by rfl⟩ : syracuseStep 3685135 = 5527703) B5527703
theorem B1456911 : Blo 1455547 1456911 := bstep (se 1 (by rfl) ⟨1092683, by rfl⟩ : syracuseStep 1456911 = 2185367) B2185367
theorem B11057957 : Blo 1455547 11057957 := bstep (se 4 (by rfl) ⟨1036683, by rfl⟩ : syracuseStep 11057957 = 2073367) B2073367
theorem B2186027 : Blo 1455547 2186027 := bstep (se 1 (by rfl) ⟨1639520, by rfl⟩ : syracuseStep 2186027 = 3279041) B3279041
theorem B1456955 : Blo 1455547 1456955 := bstep (se 1 (by rfl) ⟨1092716, by rfl⟩ : syracuseStep 1456955 = 2185433) B2185433
theorem B2186057 : Blo 1455547 2186057 := bstep (se 2 (by rfl) ⟨819771, by rfl⟩ : syracuseStep 2186057 = 1639543) B1639543
theorem B56736611 : Blo 1455547 56736611 := bstep (se 1 (by rfl) ⟨42552458, by rfl⟩ : syracuseStep 56736611 = 85104917) B85104917
theorem B3275639 : Blo 1455547 3275639 := bstep (se 1 (by rfl) ⟨2456729, by rfl⟩ : syracuseStep 3275639 = 4913459) B4913459
theorem B1457031 : Blo 1455547 1457031 := bstep (se 1 (by rfl) ⟨1092773, by rfl⟩ : syracuseStep 1457031 = 2185547) B2185547
theorem B1457039 : Blo 1455547 1457039 := bstep (se 1 (by rfl) ⟨1092779, by rfl⟩ : syracuseStep 1457039 = 2185559) B2185559
theorem B1457083 : Blo 1455547 1457083 := bstep (se 1 (by rfl) ⟨1092812, by rfl⟩ : syracuseStep 1457083 = 2185625) B2185625
theorem B2186171 : Blo 1455547 2186171 := bstep (se 1 (by rfl) ⟨1639628, by rfl⟩ : syracuseStep 2186171 = 3279257) B3279257
theorem B2186231 : Blo 1455547 2186231 := bstep (se 1 (by rfl) ⟨1639673, by rfl⟩ : syracuseStep 2186231 = 3279347) B3279347
theorem B1457159 : Blo 1455547 1457159 := bstep (se 1 (by rfl) ⟨1092869, by rfl⟩ : syracuseStep 1457159 = 2185739) B2185739
theorem B11811851 : Blo 1455547 11811851 := bstep (se 1 (by rfl) ⟨8858888, by rfl⟩ : syracuseStep 11811851 = 17717777) B17717777
theorem B1457167 : Blo 1455547 1457167 := bstep (se 1 (by rfl) ⟨1092875, by rfl⟩ : syracuseStep 1457167 = 2185751) B2185751
theorem B2186255 : Blo 1455547 2186255 := bstep (se 1 (by rfl) ⟨1639691, by rfl⟩ : syracuseStep 2186255 = 3279383) B3279383
theorem B3685409 : Blo 1455547 3685409 := bstep (se 2 (by rfl) ⟨1382028, by rfl⟩ : syracuseStep 3685409 = 2764057) B2764057
theorem B3275819 : Blo 1455547 3275819 := bstep (se 1 (by rfl) ⟨2456864, by rfl⟩ : syracuseStep 3275819 = 4913729) B4913729
theorem B2186297 : Blo 1455547 2186297 := bstep (se 2 (by rfl) ⟨819861, by rfl⟩ : syracuseStep 2186297 = 1639723) B1639723
theorem B2456635 : Blo 1455547 2456635 := bstep (se 1 (by rfl) ⟨1842476, by rfl⟩ : syracuseStep 2456635 = 3684953) B3684953
theorem B1457211 : Blo 1455547 1457211 := bstep (se 1 (by rfl) ⟨1092908, by rfl⟩ : syracuseStep 1457211 = 2185817) B2185817
theorem B9337943 : Blo 1455547 9337943 := bstep (se 1 (by rfl) ⟨7003457, by rfl⟩ : syracuseStep 9337943 = 14006915) B14006915
theorem B1457287 : Blo 1455547 1457287 := bstep (se 1 (by rfl) ⟨1092965, by rfl⟩ : syracuseStep 1457287 = 2185931) B2185931
theorem B1457295 : Blo 1455547 1457295 := bstep (se 1 (by rfl) ⟨1092971, by rfl⟩ : syracuseStep 1457295 = 2185943) B2185943
theorem B1637563 : Blo 1455547 1637563 := bstep (se 1 (by rfl) ⟨1228172, by rfl⟩ : syracuseStep 1637563 = 2456345) B2456345
theorem B1457339 : Blo 1455547 1457339 := bstep (se 1 (by rfl) ⟨1093004, by rfl⟩ : syracuseStep 1457339 = 2186009) B2186009
theorem B2456777 : Blo 1455547 2456777 := bstep (se 2 (by rfl) ⟨921291, by rfl⟩ : syracuseStep 2456777 = 1842583) B1842583
theorem B4914377 : Blo 1455547 4914377 := bstep (se 2 (by rfl) ⟨1842891, by rfl⟩ : syracuseStep 4914377 = 3685783) B3685783
theorem B1457415 : Blo 1455547 1457415 := bstep (se 1 (by rfl) ⟨1093061, by rfl⟩ : syracuseStep 1457415 = 2186123) B2186123
theorem B1457423 : Blo 1455547 1457423 := bstep (se 1 (by rfl) ⟨1093067, by rfl⟩ : syracuseStep 1457423 = 2186135) B2186135
theorem B16809275 : Blo 1455547 16809275 := bstep (se 1 (by rfl) ⟨12606956, by rfl⟩ : syracuseStep 16809275 = 25213913) B25213913
theorem B1457467 : Blo 1455547 1457467 := bstep (se 1 (by rfl) ⟨1093100, by rfl⟩ : syracuseStep 1457467 = 2186201) B2186201
theorem B2334071 : Blo 1455547 2334071 := bstep (se 1 (by rfl) ⟨1750553, by rfl⟩ : syracuseStep 2334071 = 3501107) B3501107
theorem B1457543 : Blo 1455547 1457543 := bstep (se 1 (by rfl) ⟨1093157, by rfl⟩ : syracuseStep 1457543 = 2186315) B2186315
theorem B3276179 : Blo 1455547 3276179 := bstep (se 1 (by rfl) ⟨2457134, by rfl⟩ : syracuseStep 3276179 = 4914269) B4914269
theorem B6643129 : Blo 1455547 6643129 := bstep (se 2 (by rfl) ⟨2491173, by rfl⟩ : syracuseStep 6643129 = 4982347) B4982347
theorem B3276233 : Blo 1455547 3276233 := bstep (se 2 (by rfl) ⟨1228587, by rfl⟩ : syracuseStep 3276233 = 2457175) B2457175
theorem B1842679 : Blo 1455547 1842679 := bstep (se 1 (by rfl) ⟨1382009, by rfl⟩ : syracuseStep 1842679 = 2764019) B2764019
theorem B5529131 : Blo 1455547 5529131 := bstep (se 1 (by rfl) ⟨4146848, by rfl⟩ : syracuseStep 5529131 = 8293697) B8293697
theorem B7003691 : Blo 1455547 7003691 := bstep (se 1 (by rfl) ⟨5252768, by rfl⟩ : syracuseStep 7003691 = 10505537) B10505537
theorem B8298071 : Blo 1455547 8298071 := bstep (se 1 (by rfl) ⟨6223553, by rfl⟩ : syracuseStep 8298071 = 12447107) B12447107
theorem B3743347 : Blo 1455547 3743347 := bstep (se 1 (by rfl) ⟨2807510, by rfl⟩ : syracuseStep 3743347 = 5615021) B5615021
theorem B1638031 : Blo 1455547 1638031 := bstep (se 1 (by rfl) ⟨1228523, by rfl⟩ : syracuseStep 1638031 = 2457047) B2457047
theorem B6217505 : Blo 1455547 6217505 := bstep (se 2 (by rfl) ⟨2331564, by rfl⟩ : syracuseStep 6217505 = 4663129) B4663129
theorem B1843003 : Blo 1455547 1843003 := bstep (se 1 (by rfl) ⟨1382252, by rfl⟩ : syracuseStep 1843003 = 2764505) B2764505
theorem B2457479 : Blo 1455547 2457479 := bstep (se 1 (by rfl) ⟨1843109, by rfl⟩ : syracuseStep 2457479 = 3686219) B3686219
theorem B4915079 : Blo 1455547 4915079 := bstep (se 1 (by rfl) ⟨3686309, by rfl⟩ : syracuseStep 4915079 = 7372619) B7372619
theorem B2457607 : Blo 1455547 2457607 := bstep (se 1 (by rfl) ⟨1843205, by rfl⟩ : syracuseStep 2457607 = 3686411) B3686411
theorem B14385181 : Blo 1455547 14385181 := bstep (se 3 (by rfl) ⟨2697221, by rfl⟩ : syracuseStep 14385181 = 5394443) B5394443
theorem B4145231 : Blo 1455547 4145231 := bstep (se 1 (by rfl) ⟨3108923, by rfl⟩ : syracuseStep 4145231 = 6217847) B6217847
theorem B3276971 : Blo 1455547 3276971 := bstep (se 1 (by rfl) ⟨2457728, by rfl⟩ : syracuseStep 3276971 = 4915457) B4915457
theorem B20988229 : Blo 1455547 20988229 := bstep (se 4 (by rfl) ⟨1967646, by rfl⟩ : syracuseStep 20988229 = 3935293) B3935293
theorem B1638751 : Blo 1455547 1638751 := bstep (se 1 (by rfl) ⟨1229063, by rfl⟩ : syracuseStep 1638751 = 2458127) B2458127
theorem B2458039 : Blo 1455547 2458039 := bstep (se 1 (by rfl) ⟨1843529, by rfl⟩ : syracuseStep 2458039 = 3687059) B3687059
theorem B4915835 : Blo 1455547 4915835 := bstep (se 1 (by rfl) ⟨3686876, by rfl⟩ : syracuseStep 4915835 = 7373753) B7373753
theorem B2458235 : Blo 1455547 2458235 := bstep (se 1 (by rfl) ⟨1843676, by rfl⟩ : syracuseStep 2458235 = 3687353) B3687353
theorem B5530301 : Blo 1455547 5530301 := bstep (se 3 (by rfl) ⟨1036931, by rfl⟩ : syracuseStep 5530301 = 2073863) B2073863
theorem B3277511 : Blo 1455547 3277511 := bstep (se 1 (by rfl) ⟨2458133, by rfl⟩ : syracuseStep 3277511 = 4916267) B4916267
theorem B1639111 : Blo 1455547 1639111 := bstep (se 1 (by rfl) ⟨1229333, by rfl⟩ : syracuseStep 1639111 = 2458667) B2458667
theorem B22430465 : Blo 1455547 22430465 := bstep (se 2 (by rfl) ⟨8411424, by rfl⟩ : syracuseStep 22430465 = 16822849) B16822849
theorem B11068163 : Blo 1455547 11068163 := bstep (se 1 (by rfl) ⟨8301122, by rfl⟩ : syracuseStep 11068163 = 16602245) B16602245
theorem B4915997 : Blo 1455547 4915997 := bstep (se 3 (by rfl) ⟨921749, by rfl⟩ : syracuseStep 4915997 = 1843499) B1843499
theorem B3687241 : Blo 1455547 3687241 := bstep (se 2 (by rfl) ⟨1382715, by rfl⟩ : syracuseStep 3687241 = 2765431) B2765431
theorem B2458633 : Blo 1455547 2458633 := bstep (se 2 (by rfl) ⟨921987, by rfl⟩ : syracuseStep 2458633 = 1843975) B1843975
theorem B9970739 : Blo 1455547 9970739 := bstep (se 1 (by rfl) ⟨7478054, by rfl⟩ : syracuseStep 9970739 = 14956109) B14956109
theorem B2458795 : Blo 1455547 2458795 := bstep (se 1 (by rfl) ⟨1844096, by rfl⟩ : syracuseStep 2458795 = 3688193) B3688193
theorem B23635115 : Blo 1455547 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B4916699 : Blo 1455547 4916699 := bstep (se 1 (by rfl) ⟨3687524, by rfl⟩ : syracuseStep 4916699 = 7375049) B7375049
theorem B2459099 : Blo 1455547 2459099 := bstep (se 1 (by rfl) ⟨1844324, by rfl⟩ : syracuseStep 2459099 = 3688649) B3688649
theorem B3278375 : Blo 1455547 3278375 := bstep (se 1 (by rfl) ⟨2458781, by rfl⟩ : syracuseStep 3278375 = 4917563) B4917563
theorem B59754131 : Blo 1455547 59754131 := bstep (se 1 (by rfl) ⟨44815598, by rfl⟩ : syracuseStep 59754131 = 89631197) B89631197
theorem B2459335 : Blo 1455547 2459335 := bstep (se 1 (by rfl) ⟨1844501, by rfl⟩ : syracuseStep 2459335 = 3689003) B3689003
theorem B39864113 : Blo 1455547 39864113 := bstep (se 2 (by rfl) ⟨14949042, by rfl⟩ : syracuseStep 39864113 = 29898085) B29898085
theorem B2459497 : Blo 1455547 2459497 := bstep (se 2 (by rfl) ⟨922311, by rfl⟩ : syracuseStep 2459497 = 1844623) B1844623
theorem B3278699 : Blo 1455547 3278699 := bstep (se 1 (by rfl) ⟨2459024, by rfl⟩ : syracuseStep 3278699 = 4918049) B4918049
theorem B37824407 : Blo 1455547 37824407 := bstep (se 1 (by rfl) ⟨28368305, by rfl⟩ : syracuseStep 37824407 = 56736611) B56736611
theorem B5048225 : Blo 1455547 5048225 := bstep (se 2 (by rfl) ⟨1893084, by rfl⟩ : syracuseStep 5048225 = 3786169) B3786169
theorem B8857505 : Blo 1455547 8857505 := bstep (se 2 (by rfl) ⟨3321564, by rfl⟩ : syracuseStep 8857505 = 6643129) B6643129
theorem B3278753 : Blo 1455547 3278753 := bstep (se 2 (by rfl) ⟨1229532, by rfl⟩ : syracuseStep 3278753 = 2459065) B2459065
theorem B3688375 : Blo 1455547 3688375 := bstep (se 1 (by rfl) ⟨2766281, by rfl⟩ : syracuseStep 3688375 = 5532563) B5532563
theorem B7874567 : Blo 1455547 7874567 := bstep (se 1 (by rfl) ⟨5905925, by rfl⟩ : syracuseStep 7874567 = 11811851) B11811851
theorem B5605433 : Blo 1455547 5605433 := bstep (se 2 (by rfl) ⟨2102037, by rfl⟩ : syracuseStep 5605433 = 4204075) B4204075
theorem B11978867 : Blo 1455547 11978867 := bstep (se 1 (by rfl) ⟨8984150, by rfl⟩ : syracuseStep 11978867 = 17968301) B17968301
theorem B4991129 : Blo 1455547 4991129 := bstep (se 2 (by rfl) ⟨1871673, by rfl⟩ : syracuseStep 4991129 = 3743347) B3743347
theorem B4917401 : Blo 1455547 4917401 := bstep (se 2 (by rfl) ⟨1844025, by rfl⟩ : syracuseStep 4917401 = 3688051) B3688051
theorem B3279095 : Blo 1455547 3279095 := bstep (se 1 (by rfl) ⟨2459321, by rfl⟩ : syracuseStep 3279095 = 4918643) B4918643
theorem B5532047 : Blo 1455547 5532047 := bstep (se 1 (by rfl) ⟨4149035, by rfl⟩ : syracuseStep 5532047 = 8298071) B8298071
theorem B6998537 : Blo 1455547 6998537 := bstep (se 2 (by rfl) ⟨2624451, by rfl⟩ : syracuseStep 6998537 = 5248903) B5248903
theorem B10504727 : Blo 1455547 10504727 := bstep (se 1 (by rfl) ⟨7878545, by rfl⟩ : syracuseStep 10504727 = 15757091) B15757091
theorem B2214479 : Blo 1455547 2214479 := bstep (se 1 (by rfl) ⟨1660859, by rfl⟩ : syracuseStep 2214479 = 3321719) B3321719
theorem B5606137 : Blo 1455547 5606137 := bstep (se 2 (by rfl) ⟨2102301, by rfl⟩ : syracuseStep 5606137 = 4204603) B4204603
theorem B10644599 : Blo 1455547 10644599 := bstep (se 1 (by rfl) ⟨7983449, by rfl⟩ : syracuseStep 10644599 = 15966899) B15966899
theorem B2624683 : Blo 1455547 2624683 := bstep (se 1 (by rfl) ⟨1968512, by rfl⟩ : syracuseStep 2624683 = 3937025) B3937025
theorem B4918589 : Blo 1455547 4918589 := bstep (se 3 (by rfl) ⟨922235, by rfl⟩ : syracuseStep 4918589 = 1844471) B1844471
theorem B12619151 : Blo 1455547 12619151 := bstep (se 1 (by rfl) ⟨9464363, by rfl⟩ : syracuseStep 12619151 = 18928727) B18928727
theorem B11054555 : Blo 1455547 11054555 := bstep (se 1 (by rfl) ⟨8290916, by rfl⟩ : syracuseStep 11054555 = 16581833) B16581833
theorem B2764307 : Blo 1455547 2764307 := bstep (se 1 (by rfl) ⟨2073230, by rfl⟩ : syracuseStep 2764307 = 4146461) B4146461
theorem B5533217 : Blo 1455547 5533217 := bstep (se 2 (by rfl) ⟨2074956, by rfl⟩ : syracuseStep 5533217 = 4149913) B4149913
theorem B7376507 : Blo 1455547 7376507 := bstep (se 1 (by rfl) ⟨5532380, by rfl⟩ : syracuseStep 7376507 = 11064761) B11064761
theorem B6999691 : Blo 1455547 6999691 := bstep (se 1 (by rfl) ⟨5249768, by rfl⟩ : syracuseStep 6999691 = 10499537) B10499537
theorem B2764459 : Blo 1455547 2764459 := bstep (se 1 (by rfl) ⟨2073344, by rfl⟩ : syracuseStep 2764459 = 4146689) B4146689
theorem B95768243 : Blo 1455547 95768243 := bstep (se 1 (by rfl) ⟨71826182, by rfl⟩ : syracuseStep 95768243 = 143652365) B143652365
theorem B9334561 : Blo 1455547 9334561 := bstep (se 2 (by rfl) ⟨3500460, by rfl⟩ : syracuseStep 9334561 = 7000921) B7000921
theorem B3936073 : Blo 1455547 3936073 := bstep (se 2 (by rfl) ⟨1476027, by rfl⟩ : syracuseStep 3936073 = 2952055) B2952055
theorem B5533535 : Blo 1455547 5533535 := bstep (se 1 (by rfl) ⟨4150151, by rfl⟩ : syracuseStep 5533535 = 8300303) B8300303
theorem B2764687 : Blo 1455547 2764687 := bstep (se 1 (by rfl) ⟨2073515, by rfl⟩ : syracuseStep 2764687 = 4147031) B4147031
theorem B11055041 : Blo 1455547 11055041 := bstep (se 2 (by rfl) ⟨4145640, by rfl⟩ : syracuseStep 11055041 = 8291281) B8291281
theorem B2764763 : Blo 1455547 2764763 := bstep (se 1 (by rfl) ⟨2073572, by rfl⟩ : syracuseStep 2764763 = 4147145) B4147145
theorem B11063303 : Blo 1455547 11063303 := bstep (se 1 (by rfl) ⟨8297477, by rfl⟩ : syracuseStep 11063303 = 16594955) B16594955
theorem B5533703 : Blo 1455547 5533703 := bstep (se 1 (by rfl) ⟨4150277, by rfl⟩ : syracuseStep 5533703 = 8300555) B8300555
theorem B2953255 : Blo 1455547 2953255 := bstep (se 1 (by rfl) ⟨2214941, by rfl⟩ : syracuseStep 2953255 = 4429883) B4429883
theorem B4984985 : Blo 1455547 4984985 := bstep (se 2 (by rfl) ⟨1869369, by rfl⟩ : syracuseStep 4984985 = 3738739) B3738739
theorem B2183417 : Blo 1455547 2183417 := bstep (se 2 (by rfl) ⟨818781, by rfl⟩ : syracuseStep 2183417 = 1637563) B1637563
theorem B16814347 : Blo 1455547 16814347 := bstep (se 1 (by rfl) ⟨12610760, by rfl⟩ : syracuseStep 16814347 = 25221521) B25221521
theorem B2183519 : Blo 1455547 2183519 := bstep (se 1 (by rfl) ⟨1637639, by rfl⟩ : syracuseStep 2183519 = 3275279) B3275279
theorem B2625887 : Blo 1455547 2625887 := bstep (se 1 (by rfl) ⟨1969415, by rfl⟩ : syracuseStep 2625887 = 3938831) B3938831
theorem B2183531 : Blo 1455547 2183531 := bstep (se 1 (by rfl) ⟨1637648, by rfl⟩ : syracuseStep 2183531 = 3275297) B3275297
theorem B8860033 : Blo 1455547 8860033 := bstep (se 2 (by rfl) ⟨3322512, by rfl⟩ : syracuseStep 8860033 = 6645025) B6645025
theorem B5247433 : Blo 1455547 5247433 := bstep (se 2 (by rfl) ⟨1967787, by rfl⟩ : syracuseStep 5247433 = 3935575) B3935575
theorem B11063789 : Blo 1455547 11063789 := bstep (se 3 (by rfl) ⟨2074460, by rfl⟩ : syracuseStep 11063789 = 4148921) B4148921
theorem B3936755 : Blo 1455547 3936755 := bstep (se 1 (by rfl) ⟨2952566, by rfl⟩ : syracuseStep 3936755 = 5905133) B5905133
theorem B2183759 : Blo 1455547 2183759 := bstep (se 1 (by rfl) ⟨1637819, by rfl⟩ : syracuseStep 2183759 = 3275639) B3275639
theorem B2183879 : Blo 1455547 2183879 := bstep (se 1 (by rfl) ⟨1637909, by rfl⟩ : syracuseStep 2183879 = 3275819) B3275819
theorem B3109727 : Blo 1455547 3109727 := bstep (se 1 (by rfl) ⟨2332295, by rfl⟩ : syracuseStep 3109727 = 4664591) B4664591
theorem B2184041 : Blo 1455547 2184041 := bstep (se 2 (by rfl) ⟨819015, by rfl⟩ : syracuseStep 2184041 = 1638031) B1638031
theorem B2184119 : Blo 1455547 2184119 := bstep (se 1 (by rfl) ⟨1638089, by rfl⟩ : syracuseStep 2184119 = 3276179) B3276179
theorem B2184155 : Blo 1455547 2184155 := bstep (se 1 (by rfl) ⟨1638116, by rfl⟩ : syracuseStep 2184155 = 3276233) B3276233
theorem B3109907 : Blo 1455547 3109907 := bstep (se 1 (by rfl) ⟨2332430, by rfl⟩ : syracuseStep 3109907 = 4664861) B4664861
theorem B2430281 : Blo 1455547 2430281 := bstep (se 2 (by rfl) ⟨911355, by rfl⟩ : syracuseStep 2430281 = 1822711) B1822711
theorem B11056499 : Blo 1455547 11056499 := bstep (se 1 (by rfl) ⟨8292374, by rfl⟩ : syracuseStep 11056499 = 16584749) B16584749
theorem B5526913 : Blo 1455547 5526913 := bstep (se 2 (by rfl) ⟨2072592, by rfl⟩ : syracuseStep 5526913 = 4145185) B4145185
theorem B5248385 : Blo 1455547 5248385 := bstep (se 2 (by rfl) ⟨1968144, by rfl⟩ : syracuseStep 5248385 = 3936289) B3936289
theorem B2184623 : Blo 1455547 2184623 := bstep (se 1 (by rfl) ⟨1638467, by rfl⟩ : syracuseStep 2184623 = 3276935) B3276935
theorem B1455559 : Blo 1455547 1455559 := bstep (se 1 (by rfl) ⟨1091669, by rfl⟩ : syracuseStep 1455559 = 2183339) B2183339
theorem B1455579 : Blo 1455547 1455579 := bstep (se 1 (by rfl) ⟨1091684, by rfl⟩ : syracuseStep 1455579 = 2183369) B2183369
theorem B4912649 : Blo 1455547 4912649 := bstep (se 2 (by rfl) ⟨1842243, by rfl⟩ : syracuseStep 4912649 = 3684487) B3684487
theorem B2184713 : Blo 1455547 2184713 := bstep (se 2 (by rfl) ⟨819267, by rfl⟩ : syracuseStep 2184713 = 1638535) B1638535
theorem B1455655 : Blo 1455547 1455655 := bstep (se 1 (by rfl) ⟨1091741, by rfl⟩ : syracuseStep 1455655 = 2183483) B2183483
theorem B2184743 : Blo 1455547 2184743 := bstep (se 1 (by rfl) ⟨1638557, by rfl⟩ : syracuseStep 2184743 = 3277115) B3277115
theorem B24901181 : Blo 1455547 24901181 := bstep (se 3 (by rfl) ⟨4668971, by rfl⟩ : syracuseStep 24901181 = 9337943) B9337943
theorem B1455695 : Blo 1455547 1455695 := bstep (se 1 (by rfl) ⟨1091771, by rfl⟩ : syracuseStep 1455695 = 2183543) B2183543
theorem B1455711 : Blo 1455547 1455711 := bstep (se 1 (by rfl) ⟨1091783, by rfl⟩ : syracuseStep 1455711 = 2183567) B2183567
theorem B3937889 : Blo 1455547 3937889 := bstep (se 2 (by rfl) ⟨1476708, by rfl⟩ : syracuseStep 3937889 = 2953417) B2953417
theorem B1455739 : Blo 1455547 1455739 := bstep (se 1 (by rfl) ⟨1091804, by rfl⟩ : syracuseStep 1455739 = 2183609) B2183609
theorem B2184827 : Blo 1455547 2184827 := bstep (se 1 (by rfl) ⟨1638620, by rfl⟩ : syracuseStep 2184827 = 3277241) B3277241
theorem B5527187 : Blo 1455547 5527187 := bstep (se 1 (by rfl) ⟨4145390, by rfl⟩ : syracuseStep 5527187 = 8290781) B8290781
theorem B1455791 : Blo 1455547 1455791 := bstep (se 1 (by rfl) ⟨1091843, by rfl⟩ : syracuseStep 1455791 = 2183687) B2183687
theorem B9336509 : Blo 1455547 9336509 := bstep (se 3 (by rfl) ⟨1750595, by rfl⟩ : syracuseStep 9336509 = 3501191) B3501191
theorem B1455815 : Blo 1455547 1455815 := bstep (se 1 (by rfl) ⟨1091861, by rfl⟩ : syracuseStep 1455815 = 2183723) B2183723
theorem B1455835 : Blo 1455547 1455835 := bstep (se 1 (by rfl) ⟨1091876, by rfl⟩ : syracuseStep 1455835 = 2183753) B2183753
theorem B2184953 : Blo 1455547 2184953 := bstep (se 2 (by rfl) ⟨819357, by rfl⟩ : syracuseStep 2184953 = 1638715) B1638715
theorem B1455911 : Blo 1455547 1455911 := bstep (se 1 (by rfl) ⟨1091933, by rfl⟩ : syracuseStep 1455911 = 2183867) B2183867
theorem B4667179 : Blo 1455547 4667179 := bstep (se 1 (by rfl) ⟨3500384, by rfl⟩ : syracuseStep 4667179 = 7000769) B7000769
theorem B10639163 : Blo 1455547 10639163 := bstep (se 1 (by rfl) ⟨7979372, by rfl⟩ : syracuseStep 10639163 = 15958745) B15958745
theorem B1455951 : Blo 1455547 1455951 := bstep (se 1 (by rfl) ⟨1091963, by rfl⟩ : syracuseStep 1455951 = 2183927) B2183927
theorem B1455967 : Blo 1455547 1455967 := bstep (se 1 (by rfl) ⟨1091975, by rfl⟩ : syracuseStep 1455967 = 2183951) B2183951
theorem B2185055 : Blo 1455547 2185055 := bstep (se 1 (by rfl) ⟨1638791, by rfl⟩ : syracuseStep 2185055 = 3277583) B3277583
theorem B2185067 : Blo 1455547 2185067 := bstep (se 1 (by rfl) ⟨1638800, by rfl⟩ : syracuseStep 2185067 = 3277601) B3277601
theorem B1455995 : Blo 1455547 1455995 := bstep (se 1 (by rfl) ⟨1091996, by rfl⟩ : syracuseStep 1455995 = 2183993) B2183993
theorem B1456047 : Blo 1455547 1456047 := bstep (se 1 (by rfl) ⟨1092035, by rfl⟩ : syracuseStep 1456047 = 2184071) B2184071
theorem B1456071 : Blo 1455547 1456071 := bstep (se 1 (by rfl) ⟨1092053, by rfl⟩ : syracuseStep 1456071 = 2184107) B2184107
theorem B14186449 : Blo 1455547 14186449 := bstep (se 2 (by rfl) ⟨5319918, by rfl⟩ : syracuseStep 14186449 = 10639837) B10639837
theorem B1456091 : Blo 1455547 1456091 := bstep (se 1 (by rfl) ⟨1092068, by rfl⟩ : syracuseStep 1456091 = 2184137) B2184137
theorem B1456167 : Blo 1455547 1456167 := bstep (se 1 (by rfl) ⟨1092125, by rfl⟩ : syracuseStep 1456167 = 2184251) B2184251
theorem B1456207 : Blo 1455547 1456207 := bstep (se 1 (by rfl) ⟨1092155, by rfl⟩ : syracuseStep 1456207 = 2184311) B2184311
theorem B2185295 : Blo 1455547 2185295 := bstep (se 1 (by rfl) ⟨1638971, by rfl⟩ : syracuseStep 2185295 = 3277943) B3277943
theorem B1456223 : Blo 1455547 1456223 := bstep (se 1 (by rfl) ⟨1092167, by rfl⟩ : syracuseStep 1456223 = 2184335) B2184335
theorem B2660449 : Blo 1455547 2660449 := bstep (se 2 (by rfl) ⟨997668, by rfl⟩ : syracuseStep 2660449 = 1995337) B1995337
theorem B1456251 : Blo 1455547 1456251 := bstep (se 1 (by rfl) ⟨1092188, by rfl⟩ : syracuseStep 1456251 = 2184377) B2184377
theorem B2332795 : Blo 1455547 2332795 := bstep (se 1 (by rfl) ⟨1749596, by rfl⟩ : syracuseStep 2332795 = 3499193) B3499193
theorem B1456303 : Blo 1455547 1456303 := bstep (se 1 (by rfl) ⟨1092227, by rfl⟩ : syracuseStep 1456303 = 2184455) B2184455
theorem B1456327 : Blo 1455547 1456327 := bstep (se 1 (by rfl) ⟨1092245, by rfl⟩ : syracuseStep 1456327 = 2184491) B2184491
theorem B2185415 : Blo 1455547 2185415 := bstep (se 1 (by rfl) ⟨1639061, by rfl⟩ : syracuseStep 2185415 = 3278123) B3278123
theorem B1456347 : Blo 1455547 1456347 := bstep (se 1 (by rfl) ⟨1092260, by rfl⟩ : syracuseStep 1456347 = 2184521) B2184521
theorem B3684599 : Blo 1455547 3684599 := bstep (se 1 (by rfl) ⟨2763449, by rfl⟩ : syracuseStep 3684599 = 5526899) B5526899
theorem B1456423 : Blo 1455547 1456423 := bstep (se 1 (by rfl) ⟨1092317, by rfl⟩ : syracuseStep 1456423 = 2184635) B2184635
theorem B1456463 : Blo 1455547 1456463 := bstep (se 1 (by rfl) ⟨1092347, by rfl⟩ : syracuseStep 1456463 = 2184695) B2184695
theorem B1456479 : Blo 1455547 1456479 := bstep (se 1 (by rfl) ⟨1092359, by rfl⟩ : syracuseStep 1456479 = 2184719) B2184719
theorem B4913513 : Blo 1455547 4913513 := bstep (se 2 (by rfl) ⟨1842567, by rfl⟩ : syracuseStep 4913513 = 3685135) B3685135
theorem B2185577 : Blo 1455547 2185577 := bstep (se 2 (by rfl) ⟨819591, by rfl⟩ : syracuseStep 2185577 = 1639183) B1639183
theorem B1456507 : Blo 1455547 1456507 := bstep (se 1 (by rfl) ⟨1092380, by rfl⟩ : syracuseStep 1456507 = 2184761) B2184761
theorem B11065733 : Blo 1455547 11065733 := bstep (se 4 (by rfl) ⟨1037412, by rfl⟩ : syracuseStep 11065733 = 2074825) B2074825
theorem B1456559 : Blo 1455547 1456559 := bstep (se 1 (by rfl) ⟨1092419, by rfl⟩ : syracuseStep 1456559 = 2184839) B2184839
theorem B2185655 : Blo 1455547 2185655 := bstep (se 1 (by rfl) ⟨1639241, by rfl⟩ : syracuseStep 2185655 = 3278483) B3278483
theorem B1456583 : Blo 1455547 1456583 := bstep (se 1 (by rfl) ⟨1092437, by rfl⟩ : syracuseStep 1456583 = 2184875) B2184875
theorem B1456603 : Blo 1455547 1456603 := bstep (se 1 (by rfl) ⟨1092452, by rfl⟩ : syracuseStep 1456603 = 2184905) B2184905
theorem B2185691 : Blo 1455547 2185691 := bstep (se 1 (by rfl) ⟨1639268, by rfl⟩ : syracuseStep 2185691 = 3278537) B3278537
theorem B1456679 : Blo 1455547 1456679 := bstep (se 1 (by rfl) ⟨1092509, by rfl⟩ : syracuseStep 1456679 = 2185019) B2185019
theorem B7371323 : Blo 1455547 7371323 := bstep (se 1 (by rfl) ⟨5528492, by rfl⟩ : syracuseStep 7371323 = 11056985) B11056985
theorem B1456719 : Blo 1455547 1456719 := bstep (se 1 (by rfl) ⟨1092539, by rfl⟩ : syracuseStep 1456719 = 2185079) B2185079
theorem B1456735 : Blo 1455547 1456735 := bstep (se 1 (by rfl) ⟨1092551, by rfl⟩ : syracuseStep 1456735 = 2185103) B2185103
theorem B3275387 : Blo 1455547 3275387 := bstep (se 1 (by rfl) ⟨2456540, by rfl⟩ : syracuseStep 3275387 = 4913081) B4913081
theorem B1456763 : Blo 1455547 1456763 := bstep (se 1 (by rfl) ⟨1092572, by rfl⟩ : syracuseStep 1456763 = 2185145) B2185145
theorem B3111547 : Blo 1455547 3111547 := bstep (se 1 (by rfl) ⟨2333660, by rfl⟩ : syracuseStep 3111547 = 4667321) B4667321
theorem B1456815 : Blo 1455547 1456815 := bstep (se 1 (by rfl) ⟨1092611, by rfl⟩ : syracuseStep 1456815 = 2185223) B2185223
theorem B1456839 : Blo 1455547 1456839 := bstep (se 1 (by rfl) ⟨1092629, by rfl⟩ : syracuseStep 1456839 = 2185259) B2185259
theorem B3111623 : Blo 1455547 3111623 := bstep (se 1 (by rfl) ⟨2333717, by rfl⟩ : syracuseStep 3111623 = 4667435) B4667435
theorem B1456859 : Blo 1455547 1456859 := bstep (se 1 (by rfl) ⟨1092644, by rfl⟩ : syracuseStep 1456859 = 2185289) B2185289
theorem B2456311 : Blo 1455547 2456311 := bstep (se 1 (by rfl) ⟨1842233, by rfl⟩ : syracuseStep 2456311 = 3684467) B3684467
theorem B3275513 : Blo 1455547 3275513 := bstep (se 2 (by rfl) ⟨1228317, by rfl⟩ : syracuseStep 3275513 = 2456635) B2456635
theorem B11803421 : Blo 1455547 11803421 := bstep (se 3 (by rfl) ⟨2213141, by rfl⟩ : syracuseStep 11803421 = 4426283) B4426283
theorem B1456935 : Blo 1455547 1456935 := bstep (se 1 (by rfl) ⟨1092701, by rfl⟩ : syracuseStep 1456935 = 2185403) B2185403
theorem B1456975 : Blo 1455547 1456975 := bstep (se 1 (by rfl) ⟨1092731, by rfl⟩ : syracuseStep 1456975 = 2185463) B2185463
theorem B1456991 : Blo 1455547 1456991 := bstep (se 1 (by rfl) ⟨1092743, by rfl⟩ : syracuseStep 1456991 = 2185487) B2185487
theorem B11066219 : Blo 1455547 11066219 := bstep (se 1 (by rfl) ⟨8299664, by rfl⟩ : syracuseStep 11066219 = 16599329) B16599329
theorem B1457019 : Blo 1455547 1457019 := bstep (se 1 (by rfl) ⟨1092764, by rfl⟩ : syracuseStep 1457019 = 2185529) B2185529
theorem B16587665 : Blo 1455547 16587665 := bstep (se 2 (by rfl) ⟨6220374, by rfl⟩ : syracuseStep 16587665 = 12440749) B12440749
theorem B1457071 : Blo 1455547 1457071 := bstep (se 1 (by rfl) ⟨1092803, by rfl⟩ : syracuseStep 1457071 = 2185607) B2185607
theorem B2186159 : Blo 1455547 2186159 := bstep (se 1 (by rfl) ⟨1639619, by rfl⟩ : syracuseStep 2186159 = 3279239) B3279239
theorem B2456507 : Blo 1455547 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B4914107 : Blo 1455547 4914107 := bstep (se 1 (by rfl) ⟨3685580, by rfl⟩ : syracuseStep 4914107 = 7371161) B7371161
theorem B1457095 : Blo 1455547 1457095 := bstep (se 1 (by rfl) ⟨1092821, by rfl⟩ : syracuseStep 1457095 = 2185643) B2185643
theorem B1457115 : Blo 1455547 1457115 := bstep (se 1 (by rfl) ⟨1092836, by rfl⟩ : syracuseStep 1457115 = 2185673) B2185673
theorem B3275783 : Blo 1455547 3275783 := bstep (se 1 (by rfl) ⟨2456837, by rfl⟩ : syracuseStep 3275783 = 4913675) B4913675
theorem B2186249 : Blo 1455547 2186249 := bstep (se 2 (by rfl) ⟨819843, by rfl⟩ : syracuseStep 2186249 = 1639687) B1639687
theorem B4979731 : Blo 1455547 4979731 := bstep (se 1 (by rfl) ⟨3734798, by rfl⟩ : syracuseStep 4979731 = 7469597) B7469597
theorem B2456615 : Blo 1455547 2456615 := bstep (se 1 (by rfl) ⟨1842461, by rfl⟩ : syracuseStep 2456615 = 3684923) B3684923
theorem B1457191 : Blo 1455547 1457191 := bstep (se 1 (by rfl) ⟨1092893, by rfl⟩ : syracuseStep 1457191 = 2185787) B2185787
theorem B2186279 : Blo 1455547 2186279 := bstep (se 1 (by rfl) ⟨1639709, by rfl⟩ : syracuseStep 2186279 = 3279419) B3279419
theorem B3275855 : Blo 1455547 3275855 := bstep (se 1 (by rfl) ⟨2456891, by rfl⟩ : syracuseStep 3275855 = 4913783) B4913783
theorem B1457231 : Blo 1455547 1457231 := bstep (se 1 (by rfl) ⟨1092923, by rfl⟩ : syracuseStep 1457231 = 2185847) B2185847
theorem B1457247 : Blo 1455547 1457247 := bstep (se 1 (by rfl) ⟨1092935, by rfl⟩ : syracuseStep 1457247 = 2185871) B2185871
theorem B1457275 : Blo 1455547 1457275 := bstep (se 1 (by rfl) ⟨1092956, by rfl⟩ : syracuseStep 1457275 = 2185913) B2185913
theorem B1457327 : Blo 1455547 1457327 := bstep (se 1 (by rfl) ⟨1092995, by rfl⟩ : syracuseStep 1457327 = 2185991) B2185991
theorem B7371971 : Blo 1455547 7371971 := bstep (se 1 (by rfl) ⟨5528978, by rfl⟩ : syracuseStep 7371971 = 11057957) B11057957
theorem B1457351 : Blo 1455547 1457351 := bstep (se 1 (by rfl) ⟨1093013, by rfl⟩ : syracuseStep 1457351 = 2186027) B2186027
theorem B1457371 : Blo 1455547 1457371 := bstep (se 1 (by rfl) ⟨1093028, by rfl⟩ : syracuseStep 1457371 = 2186057) B2186057
theorem B5528843 : Blo 1455547 5528843 := bstep (se 1 (by rfl) ⟨4146632, by rfl⟩ : syracuseStep 5528843 = 8293265) B8293265
theorem B1457447 : Blo 1455547 1457447 := bstep (se 1 (by rfl) ⟨1093085, by rfl⟩ : syracuseStep 1457447 = 2186171) B2186171
theorem B2456905 : Blo 1455547 2456905 := bstep (se 2 (by rfl) ⟨921339, by rfl⟩ : syracuseStep 2456905 = 1842679) B1842679
theorem B2334025 : Blo 1455547 2334025 := bstep (se 2 (by rfl) ⟨875259, by rfl⟩ : syracuseStep 2334025 = 1750519) B1750519
theorem B1457487 : Blo 1455547 1457487 := bstep (se 1 (by rfl) ⟨1093115, by rfl⟩ : syracuseStep 1457487 = 2186231) B2186231
theorem B1842527 : Blo 1455547 1842527 := bstep (se 1 (by rfl) ⟨1381895, by rfl⟩ : syracuseStep 1842527 = 2763791) B2763791
theorem B1457503 : Blo 1455547 1457503 := bstep (se 1 (by rfl) ⟨1093127, by rfl⟩ : syracuseStep 1457503 = 2186255) B2186255
theorem B2456939 : Blo 1455547 2456939 := bstep (se 1 (by rfl) ⟨1842704, by rfl⟩ : syracuseStep 2456939 = 3685409) B3685409
theorem B1457531 : Blo 1455547 1457531 := bstep (se 1 (by rfl) ⟨1093148, by rfl⟩ : syracuseStep 1457531 = 2186297) B2186297
theorem B5250433 : Blo 1455547 5250433 := bstep (se 2 (by rfl) ⟨1968912, by rfl⟩ : syracuseStep 5250433 = 3937825) B3937825
theorem B3939727 : Blo 1455547 3939727 := bstep (se 1 (by rfl) ⟨2954795, by rfl⟩ : syracuseStep 3939727 = 5909591) B5909591
theorem B1637851 : Blo 1455547 1637851 := bstep (se 1 (by rfl) ⟨1228388, by rfl⟩ : syracuseStep 1637851 = 2456777) B2456777
theorem B3276251 : Blo 1455547 3276251 := bstep (se 1 (by rfl) ⟨2457188, by rfl⟩ : syracuseStep 3276251 = 4914377) B4914377
theorem B4668961 : Blo 1455547 4668961 := bstep (se 2 (by rfl) ⟨1750860, by rfl⟩ : syracuseStep 4668961 = 3501721) B3501721
theorem B11206183 : Blo 1455547 11206183 := bstep (se 1 (by rfl) ⟨8404637, by rfl⟩ : syracuseStep 11206183 = 16809275) B16809275
theorem B1556047 : Blo 1455547 1556047 := bstep (se 1 (by rfl) ⟨1167035, by rfl⟩ : syracuseStep 1556047 = 2334071) B2334071
theorem B3686087 : Blo 1455547 3686087 := bstep (se 1 (by rfl) ⟨2764565, by rfl⟩ : syracuseStep 3686087 = 5529131) B5529131
theorem B4669127 : Blo 1455547 4669127 := bstep (se 1 (by rfl) ⟨3501845, by rfl⟩ : syracuseStep 4669127 = 7003691) B7003691
theorem B2457337 : Blo 1455547 2457337 := bstep (se 2 (by rfl) ⟨921501, by rfl⟩ : syracuseStep 2457337 = 1843003) B1843003
theorem B4669177 : Blo 1455547 4669177 := bstep (se 2 (by rfl) ⟨1750941, by rfl⟩ : syracuseStep 4669177 = 3501883) B3501883
theorem B170319665 : Blo 1455547 170319665 := bstep (se 2 (by rfl) ⟨63869874, by rfl⟩ : syracuseStep 170319665 = 127739749) B127739749
theorem B4145003 : Blo 1455547 4145003 := bstep (se 1 (by rfl) ⟨3108752, by rfl⟩ : syracuseStep 4145003 = 6217505) B6217505
theorem B1638319 : Blo 1455547 1638319 := bstep (se 1 (by rfl) ⟨1228739, by rfl⟩ : syracuseStep 1638319 = 2457479) B2457479
theorem B3276719 : Blo 1455547 3276719 := bstep (se 1 (by rfl) ⟨2457539, by rfl⟩ : syracuseStep 3276719 = 4915079) B4915079
theorem B3276809 : Blo 1455547 3276809 := bstep (se 2 (by rfl) ⟨1228803, by rfl⟩ : syracuseStep 3276809 = 2457607) B2457607
theorem B3547265 : Blo 1455547 3547265 := bstep (se 2 (by rfl) ⟨1330224, by rfl⟩ : syracuseStep 3547265 = 2660449) B2660449
theorem B28385597 : Blo 1455547 28385597 := bstep (se 3 (by rfl) ⟨5322299, by rfl⟩ : syracuseStep 28385597 = 10644599) B10644599
theorem B3277223 : Blo 1455547 3277223 := bstep (se 1 (by rfl) ⟨2457917, by rfl⟩ : syracuseStep 3277223 = 4915835) B4915835
theorem B1638823 : Blo 1455547 1638823 := bstep (se 1 (by rfl) ⟨1229117, by rfl⟩ : syracuseStep 1638823 = 2458235) B2458235
theorem B27984305 : Blo 1455547 27984305 := bstep (se 2 (by rfl) ⟨10494114, by rfl⟩ : syracuseStep 27984305 = 20988229) B20988229
theorem B3686867 : Blo 1455547 3686867 := bstep (se 1 (by rfl) ⟨2765150, by rfl⟩ : syracuseStep 3686867 = 5530301) B5530301
theorem B11813377 : Blo 1455547 11813377 := bstep (se 2 (by rfl) ⟨4430016, by rfl⟩ : syracuseStep 11813377 = 8860033) B8860033
theorem B3277331 : Blo 1455547 3277331 := bstep (se 1 (by rfl) ⟨2457998, by rfl⟩ : syracuseStep 3277331 = 4915997) B4915997
theorem B2073151 : Blo 1455547 2073151 := bstep (se 1 (by rfl) ⟨1554863, by rfl⟩ : syracuseStep 2073151 = 3109727) B3109727
theorem B3277385 : Blo 1455547 3277385 := bstep (se 2 (by rfl) ⟨1229019, by rfl⟩ : syracuseStep 3277385 = 2458039) B2458039
theorem B2073271 : Blo 1455547 2073271 := bstep (se 1 (by rfl) ⟨1554953, by rfl⟩ : syracuseStep 2073271 = 3109907) B3109907
theorem B6480749 : Blo 1455547 6480749 := bstep (se 3 (by rfl) ⟨1215140, by rfl⟩ : syracuseStep 6480749 = 2430281) B2430281
theorem B3498923 : Blo 1455547 3498923 := bstep (se 1 (by rfl) ⟨2624192, by rfl⟩ : syracuseStep 3498923 = 5248385) B5248385
theorem B3277799 : Blo 1455547 3277799 := bstep (se 1 (by rfl) ⟨2458349, by rfl⟩ : syracuseStep 3277799 = 4916699) B4916699
theorem B1639399 : Blo 1455547 1639399 := bstep (se 1 (by rfl) ⟨1229549, by rfl⟩ : syracuseStep 1639399 = 2459099) B2459099
theorem B4916321 : Blo 1455547 4916321 := bstep (se 2 (by rfl) ⟨1843620, by rfl⟩ : syracuseStep 4916321 = 3687241) B3687241
theorem B26576075 : Blo 1455547 26576075 := bstep (se 1 (by rfl) ⟨19932056, by rfl⟩ : syracuseStep 26576075 = 39864113) B39864113
theorem B25216271 : Blo 1455547 25216271 := bstep (se 1 (by rfl) ⟨18912203, by rfl⟩ : syracuseStep 25216271 = 37824407) B37824407
theorem B3278177 : Blo 1455547 3278177 := bstep (se 2 (by rfl) ⟨1229316, by rfl⟩ : syracuseStep 3278177 = 2458633) B2458633
theorem B3736955 : Blo 1455547 3736955 := bstep (se 1 (by rfl) ⟨2802716, by rfl⟩ : syracuseStep 3736955 = 5605433) B5605433
theorem B3327419 : Blo 1455547 3327419 := bstep (se 1 (by rfl) ⟨2495564, by rfl⟩ : syracuseStep 3327419 = 4991129) B4991129
theorem B3278267 : Blo 1455547 3278267 := bstep (se 1 (by rfl) ⟨2458700, by rfl⟩ : syracuseStep 3278267 = 4917401) B4917401
theorem B3499577 : Blo 1455547 3499577 := bstep (se 2 (by rfl) ⟨1312341, by rfl⟩ : syracuseStep 3499577 = 2624683) B2624683
theorem B3278393 : Blo 1455547 3278393 := bstep (se 2 (by rfl) ⟨1229397, by rfl⟩ : syracuseStep 3278393 = 2458795) B2458795
theorem B3688031 : Blo 1455547 3688031 := bstep (se 1 (by rfl) ⟨2766023, by rfl⟩ : syracuseStep 3688031 = 5532047) B5532047
theorem B2074415 : Blo 1455547 2074415 := bstep (se 1 (by rfl) ⟨1555811, by rfl⟩ : syracuseStep 2074415 = 3111623) B3111623
theorem B5252969 : Blo 1455547 5252969 := bstep (se 2 (by rfl) ⟨1969863, by rfl⟩ : syracuseStep 5252969 = 3939727) B3939727
theorem B2074729 : Blo 1455547 2074729 := bstep (se 2 (by rfl) ⟨778023, by rfl⟩ : syracuseStep 2074729 = 1556047) B1556047
theorem B9332921 : Blo 1455547 9332921 := bstep (se 2 (by rfl) ⟨3499845, by rfl⟩ : syracuseStep 9332921 = 6999691) B6999691
theorem B3279059 : Blo 1455547 3279059 := bstep (se 1 (by rfl) ⟨2459294, by rfl⟩ : syracuseStep 3279059 = 4918589) B4918589
theorem B3279113 : Blo 1455547 3279113 := bstep (se 2 (by rfl) ⟨1229667, by rfl⟩ : syracuseStep 3279113 = 2459335) B2459335
theorem B3688811 : Blo 1455547 3688811 := bstep (se 1 (by rfl) ⟨2766608, by rfl⟩ : syracuseStep 3688811 = 5533217) B5533217
theorem B12446081 : Blo 1455547 12446081 := bstep (se 2 (by rfl) ⟨4667280, by rfl⟩ : syracuseStep 12446081 = 9334561) B9334561
theorem B27986309 : Blo 1455547 27986309 := bstep (se 4 (by rfl) ⟨2623716, by rfl⟩ : syracuseStep 27986309 = 5247433) B5247433
theorem B4917671 : Blo 1455547 4917671 := bstep (se 1 (by rfl) ⟨3688253, by rfl⟩ : syracuseStep 4917671 = 7376507) B7376507
theorem B3279329 : Blo 1455547 3279329 := bstep (se 2 (by rfl) ⟨1229748, by rfl⟩ : syracuseStep 3279329 = 2459497) B2459497
theorem B3689023 : Blo 1455547 3689023 := bstep (se 1 (by rfl) ⟨2766767, by rfl⟩ : syracuseStep 3689023 = 5533535) B5533535
theorem B2763335 : Blo 1455547 2763335 := bstep (se 1 (by rfl) ⟨2072501, by rfl⟩ : syracuseStep 2763335 = 4145003) B4145003
theorem B4917833 : Blo 1455547 4917833 := bstep (se 2 (by rfl) ⟨1844187, by rfl⟩ : syracuseStep 4917833 = 3688375) B3688375
theorem B7375535 : Blo 1455547 7375535 := bstep (se 1 (by rfl) ⟨5531651, by rfl⟩ : syracuseStep 7375535 = 11063303) B11063303
theorem B3689135 : Blo 1455547 3689135 := bstep (se 1 (by rfl) ⟨2766851, by rfl⟩ : syracuseStep 3689135 = 5533703) B5533703
theorem B19180241 : Blo 1455547 19180241 := bstep (se 2 (by rfl) ⟨7192590, by rfl⟩ : syracuseStep 19180241 = 14385181) B14385181
theorem B2763487 : Blo 1455547 2763487 := bstep (se 1 (by rfl) ⟨2072615, by rfl⟩ : syracuseStep 2763487 = 4145231) B4145231
theorem B358706069 : Blo 1455547 358706069 := bstep (se 6 (by rfl) ⟨8407173, by rfl⟩ : syracuseStep 358706069 = 16814347) B16814347
theorem B7375859 : Blo 1455547 7375859 := bstep (se 1 (by rfl) ⟨5531894, by rfl⟩ : syracuseStep 7375859 = 11063789) B11063789
theorem B2624503 : Blo 1455547 2624503 := bstep (se 1 (by rfl) ⟨1968377, by rfl⟩ : syracuseStep 2624503 = 3936755) B3936755
theorem B14953643 : Blo 1455547 14953643 := bstep (se 1 (by rfl) ⟨11215232, by rfl⟩ : syracuseStep 14953643 = 22430465) B22430465
theorem B6647159 : Blo 1455547 6647159 := bstep (se 1 (by rfl) ⟨4985369, by rfl⟩ : syracuseStep 6647159 = 9970739) B9970739
theorem B15756743 : Blo 1455547 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B4148729 : Blo 1455547 4148729 := bstep (se 2 (by rfl) ⟨1555773, by rfl⟩ : syracuseStep 4148729 = 3111547) B3111547
theorem B7474849 : Blo 1455547 7474849 := bstep (se 2 (by rfl) ⟨2803068, by rfl⟩ : syracuseStep 7474849 = 5606137) B5606137
theorem B16600787 : Blo 1455547 16600787 := bstep (se 1 (by rfl) ⟨12450590, by rfl⟩ : syracuseStep 16600787 = 24901181) B24901181
theorem B2625259 : Blo 1455547 2625259 := bstep (se 1 (by rfl) ⟨1968944, by rfl⟩ : syracuseStep 2625259 = 3937889) B3937889
theorem B6639641 : Blo 1455547 6639641 := bstep (se 2 (by rfl) ⟨2489865, by rfl⟩ : syracuseStep 6639641 = 4979731) B4979731
theorem B7377155 : Blo 1455547 7377155 := bstep (se 1 (by rfl) ⟨5532866, by rfl⟩ : syracuseStep 7377155 = 11065733) B11065733
theorem B4665691 : Blo 1455547 4665691 := bstep (se 1 (by rfl) ⟨3499268, by rfl⟩ : syracuseStep 4665691 = 6998537) B6998537
theorem B2183591 : Blo 1455547 2183591 := bstep (se 1 (by rfl) ⟨1637693, by rfl⟩ : syracuseStep 2183591 = 3275387) B3275387
theorem B2183675 : Blo 1455547 2183675 := bstep (se 1 (by rfl) ⟨1637756, by rfl⟩ : syracuseStep 2183675 = 3275513) B3275513
theorem B7369217 : Blo 1455547 7369217 := bstep (se 2 (by rfl) ⟨2763456, by rfl⟩ : syracuseStep 7369217 = 5526913) B5526913
theorem B7000577 : Blo 1455547 7000577 := bstep (se 2 (by rfl) ⟨2625216, by rfl⟩ : syracuseStep 7000577 = 5250433) B5250433
theorem B7868947 : Blo 1455547 7868947 := bstep (se 1 (by rfl) ⟨5901710, by rfl⟩ : syracuseStep 7868947 = 11803421) B11803421
theorem B7377479 : Blo 1455547 7377479 := bstep (se 1 (by rfl) ⟨5533109, by rfl⟩ : syracuseStep 7377479 = 11066219) B11066219
theorem B2183801 : Blo 1455547 2183801 := bstep (se 2 (by rfl) ⟨818925, by rfl⟩ : syracuseStep 2183801 = 1637851) B1637851
theorem B2183855 : Blo 1455547 2183855 := bstep (se 1 (by rfl) ⟨1637891, by rfl⟩ : syracuseStep 2183855 = 3275783) B3275783
theorem B2183903 : Blo 1455547 2183903 := bstep (se 1 (by rfl) ⟨1637927, by rfl⟩ : syracuseStep 2183903 = 3275855) B3275855
theorem B7369703 : Blo 1455547 7369703 := bstep (se 1 (by rfl) ⟨5527277, by rfl⟩ : syracuseStep 7369703 = 11054555) B11054555
theorem B2184167 : Blo 1455547 2184167 := bstep (se 1 (by rfl) ⟨1638125, by rfl⟩ : syracuseStep 2184167 = 3276251) B3276251
theorem B6222905 : Blo 1455547 6222905 := bstep (se 2 (by rfl) ⟨2333589, by rfl⟩ : syracuseStep 6222905 = 4667179) B4667179
theorem B5248097 : Blo 1455547 5248097 := bstep (se 2 (by rfl) ⟨1968036, by rfl⟩ : syracuseStep 5248097 = 3936073) B3936073
theorem B63845495 : Blo 1455547 63845495 := bstep (se 1 (by rfl) ⟨47884121, by rfl⟩ : syracuseStep 63845495 = 95768243) B95768243
theorem B113546443 : Blo 1455547 113546443 := bstep (se 1 (by rfl) ⟨85159832, by rfl⟩ : syracuseStep 113546443 = 170319665) B170319665
theorem B2184425 : Blo 1455547 2184425 := bstep (se 2 (by rfl) ⟨819159, by rfl⟩ : syracuseStep 2184425 = 1638319) B1638319
theorem B2184479 : Blo 1455547 2184479 := bstep (se 1 (by rfl) ⟨1638359, by rfl⟩ : syracuseStep 2184479 = 3276719) B3276719
theorem B7370027 : Blo 1455547 7370027 := bstep (se 1 (by rfl) ⟨5527520, by rfl⟩ : syracuseStep 7370027 = 11055041) B11055041
theorem B3937673 : Blo 1455547 3937673 := bstep (se 2 (by rfl) ⟨1476627, by rfl⟩ : syracuseStep 3937673 = 2953255) B2953255
theorem B3323323 : Blo 1455547 3323323 := bstep (se 1 (by rfl) ⟨2492492, by rfl⟩ : syracuseStep 3323323 = 4984985) B4984985
theorem B2184647 : Blo 1455547 2184647 := bstep (se 1 (by rfl) ⟨1638485, by rfl⟩ : syracuseStep 2184647 = 3276971) B3276971
theorem B3110393 : Blo 1455547 3110393 := bstep (se 2 (by rfl) ⟨1166397, by rfl⟩ : syracuseStep 3110393 = 2332795) B2332795
theorem B1455611 : Blo 1455547 1455611 := bstep (se 1 (by rfl) ⟨1091708, by rfl⟩ : syracuseStep 1455611 = 2183417) B2183417
theorem B1455679 : Blo 1455547 1455679 := bstep (se 1 (by rfl) ⟨1091759, by rfl⟩ : syracuseStep 1455679 = 2183519) B2183519
theorem B1750591 : Blo 1455547 1750591 := bstep (se 1 (by rfl) ⟨1312943, by rfl⟩ : syracuseStep 1750591 = 2625887) B2625887
theorem B1455687 : Blo 1455547 1455687 := bstep (se 1 (by rfl) ⟨1091765, by rfl⟩ : syracuseStep 1455687 = 2183531) B2183531
theorem B1455839 : Blo 1455547 1455839 := bstep (se 1 (by rfl) ⟨1091879, by rfl⟩ : syracuseStep 1455839 = 2183759) B2183759
theorem B2185001 : Blo 1455547 2185001 := bstep (se 2 (by rfl) ⟨819375, by rfl⟩ : syracuseStep 2185001 = 1638751) B1638751
theorem B1455919 : Blo 1455547 1455919 := bstep (se 1 (by rfl) ⟨1091939, by rfl⟩ : syracuseStep 1455919 = 2183879) B2183879
theorem B2185007 : Blo 1455547 2185007 := bstep (se 1 (by rfl) ⟨1638755, by rfl⟩ : syracuseStep 2185007 = 3277511) B3277511
theorem B7378775 : Blo 1455547 7378775 := bstep (se 1 (by rfl) ⟨5534081, by rfl⟩ : syracuseStep 7378775 = 11068163) B11068163
theorem B1456027 : Blo 1455547 1456027 := bstep (se 1 (by rfl) ⟨1092020, by rfl⟩ : syracuseStep 1456027 = 2184041) B2184041
theorem B1456079 : Blo 1455547 1456079 := bstep (se 1 (by rfl) ⟨1092059, by rfl⟩ : syracuseStep 1456079 = 2184119) B2184119
theorem B1456103 : Blo 1455547 1456103 := bstep (se 1 (by rfl) ⟨1092077, by rfl⟩ : syracuseStep 1456103 = 2184155) B2184155
theorem B7370999 : Blo 1455547 7370999 := bstep (se 1 (by rfl) ⟨5528249, by rfl⟩ : syracuseStep 7370999 = 11056499) B11056499
theorem B4913405 : Blo 1455547 4913405 := bstep (se 3 (by rfl) ⟨921263, by rfl⟩ : syracuseStep 4913405 = 1842527) B1842527
theorem B2185481 : Blo 1455547 2185481 := bstep (se 2 (by rfl) ⟨819555, by rfl⟩ : syracuseStep 2185481 = 1639111) B1639111
theorem B1456415 : Blo 1455547 1456415 := bstep (se 1 (by rfl) ⟨1092311, by rfl⟩ : syracuseStep 1456415 = 2184623) B2184623
theorem B3275081 : Blo 1455547 3275081 := bstep (se 2 (by rfl) ⟨1228155, by rfl⟩ : syracuseStep 3275081 = 2456311) B2456311
theorem B3275099 : Blo 1455547 3275099 := bstep (se 1 (by rfl) ⟨2456324, by rfl⟩ : syracuseStep 3275099 = 4912649) B4912649
theorem B1456475 : Blo 1455547 1456475 := bstep (se 1 (by rfl) ⟨1092356, by rfl⟩ : syracuseStep 1456475 = 2184713) B2184713
theorem B1456495 : Blo 1455547 1456495 := bstep (se 1 (by rfl) ⟨1092371, by rfl⟩ : syracuseStep 1456495 = 2184743) B2184743
theorem B2185583 : Blo 1455547 2185583 := bstep (se 1 (by rfl) ⟨1639187, by rfl⟩ : syracuseStep 2185583 = 3278375) B3278375
theorem B1456551 : Blo 1455547 1456551 := bstep (se 1 (by rfl) ⟨1092413, by rfl⟩ : syracuseStep 1456551 = 2184827) B2184827
theorem B39836087 : Blo 1455547 39836087 := bstep (se 1 (by rfl) ⟨29877065, by rfl⟩ : syracuseStep 39836087 = 59754131) B59754131
theorem B3684791 : Blo 1455547 3684791 := bstep (se 1 (by rfl) ⟨2763593, by rfl⟩ : syracuseStep 3684791 = 5527187) B5527187
theorem B6224339 : Blo 1455547 6224339 := bstep (se 1 (by rfl) ⟨4668254, by rfl⟩ : syracuseStep 6224339 = 9336509) B9336509
theorem B1456635 : Blo 1455547 1456635 := bstep (se 1 (by rfl) ⟨1092476, by rfl⟩ : syracuseStep 1456635 = 2184953) B2184953
theorem B7092775 : Blo 1455547 7092775 := bstep (se 1 (by rfl) ⟨5319581, by rfl⟩ : syracuseStep 7092775 = 10639163) B10639163
theorem B1456703 : Blo 1455547 1456703 := bstep (se 1 (by rfl) ⟨1092527, by rfl⟩ : syracuseStep 1456703 = 2185055) B2185055
theorem B1456711 : Blo 1455547 1456711 := bstep (se 1 (by rfl) ⟨1092533, by rfl⟩ : syracuseStep 1456711 = 2185067) B2185067
theorem B2185799 : Blo 1455547 2185799 := bstep (se 1 (by rfl) ⟨1639349, by rfl⟩ : syracuseStep 2185799 = 3278699) B3278699
theorem B5905003 : Blo 1455547 5905003 := bstep (se 1 (by rfl) ⟨4428752, by rfl⟩ : syracuseStep 5905003 = 8857505) B8857505
theorem B2185835 : Blo 1455547 2185835 := bstep (se 1 (by rfl) ⟨1639376, by rfl⟩ : syracuseStep 2185835 = 3278753) B3278753
theorem B5249711 : Blo 1455547 5249711 := bstep (se 1 (by rfl) ⟨3937283, by rfl⟩ : syracuseStep 5249711 = 7874567) B7874567
theorem B215390933 : Blo 1455547 215390933 := bstep (se 7 (by rfl) ⟨2524112, by rfl⟩ : syracuseStep 215390933 = 5048225) B5048225
theorem B7371485 : Blo 1455547 7371485 := bstep (se 3 (by rfl) ⟨1382153, by rfl⟩ : syracuseStep 7371485 = 2764307) B2764307
theorem B1456863 : Blo 1455547 1456863 := bstep (se 1 (by rfl) ⟨1092647, by rfl⟩ : syracuseStep 1456863 = 2185295) B2185295
theorem B7985911 : Blo 1455547 7985911 := bstep (se 1 (by rfl) ⟨5989433, by rfl⟩ : syracuseStep 7985911 = 11978867) B11978867
theorem B1456943 : Blo 1455547 1456943 := bstep (se 1 (by rfl) ⟨1092707, by rfl⟩ : syracuseStep 1456943 = 2185415) B2185415
theorem B2456399 : Blo 1455547 2456399 := bstep (se 1 (by rfl) ⟨1842299, by rfl⟩ : syracuseStep 2456399 = 3684599) B3684599
theorem B2186063 : Blo 1455547 2186063 := bstep (se 1 (by rfl) ⟨1639547, by rfl⟩ : syracuseStep 2186063 = 3279095) B3279095
theorem B5905277 : Blo 1455547 5905277 := bstep (se 3 (by rfl) ⟨1107239, by rfl⟩ : syracuseStep 5905277 = 2214479) B2214479
theorem B3275675 : Blo 1455547 3275675 := bstep (se 1 (by rfl) ⟨2456756, by rfl⟩ : syracuseStep 3275675 = 4913513) B4913513
theorem B1457051 : Blo 1455547 1457051 := bstep (se 1 (by rfl) ⟨1092788, by rfl⟩ : syracuseStep 1457051 = 2185577) B2185577
theorem B1457103 : Blo 1455547 1457103 := bstep (se 1 (by rfl) ⟨1092827, by rfl⟩ : syracuseStep 1457103 = 2185655) B2185655
theorem B1457127 : Blo 1455547 1457127 := bstep (se 1 (by rfl) ⟨1092845, by rfl⟩ : syracuseStep 1457127 = 2185691) B2185691
theorem B7003151 : Blo 1455547 7003151 := bstep (se 1 (by rfl) ⟨5252363, by rfl⟩ : syracuseStep 7003151 = 10504727) B10504727
theorem B4914215 : Blo 1455547 4914215 := bstep (se 1 (by rfl) ⟨3685661, by rfl⟩ : syracuseStep 4914215 = 7371323) B7371323
theorem B3275873 : Blo 1455547 3275873 := bstep (se 2 (by rfl) ⟨1228452, by rfl⟩ : syracuseStep 3275873 = 2456905) B2456905
theorem B3112033 : Blo 1455547 3112033 := bstep (se 2 (by rfl) ⟨1167012, by rfl⟩ : syracuseStep 3112033 = 2334025) B2334025
theorem B11058443 : Blo 1455547 11058443 := bstep (se 1 (by rfl) ⟨8293832, by rfl⟩ : syracuseStep 11058443 = 16587665) B16587665
theorem B1457439 : Blo 1455547 1457439 := bstep (se 1 (by rfl) ⟨1093079, by rfl⟩ : syracuseStep 1457439 = 2186159) B2186159
theorem B1637671 : Blo 1455547 1637671 := bstep (se 1 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 1637671 = 2456507) B2456507
theorem B3276071 : Blo 1455547 3276071 := bstep (se 1 (by rfl) ⟨2457053, by rfl⟩ : syracuseStep 3276071 = 4914107) B4914107
theorem B1457499 : Blo 1455547 1457499 := bstep (se 1 (by rfl) ⟨1093124, by rfl⟩ : syracuseStep 1457499 = 2186249) B2186249
theorem B1637743 : Blo 1455547 1637743 := bstep (se 1 (by rfl) ⟨1228307, by rfl⟩ : syracuseStep 1637743 = 2456615) B2456615
theorem B1457519 : Blo 1455547 1457519 := bstep (se 1 (by rfl) ⟨1093139, by rfl⟩ : syracuseStep 1457519 = 2186279) B2186279
theorem B6225281 : Blo 1455547 6225281 := bstep (se 2 (by rfl) ⟨2334480, by rfl⟩ : syracuseStep 6225281 = 4668961) B4668961
theorem B14941577 : Blo 1455547 14941577 := bstep (se 2 (by rfl) ⟨5603091, by rfl⟩ : syracuseStep 14941577 = 11206183) B11206183
theorem B4914647 : Blo 1455547 4914647 := bstep (se 1 (by rfl) ⟨3685985, by rfl⟩ : syracuseStep 4914647 = 7371971) B7371971
theorem B3685895 : Blo 1455547 3685895 := bstep (se 1 (by rfl) ⟨2764421, by rfl⟩ : syracuseStep 3685895 = 5528843) B5528843
theorem B3685945 : Blo 1455547 3685945 := bstep (se 2 (by rfl) ⟨1382229, by rfl⟩ : syracuseStep 3685945 = 2764459) B2764459
theorem B1637959 : Blo 1455547 1637959 := bstep (se 1 (by rfl) ⟨1228469, by rfl⟩ : syracuseStep 1637959 = 2456939) B2456939
theorem B8412767 : Blo 1455547 8412767 := bstep (se 1 (by rfl) ⟨6309575, by rfl⟩ : syracuseStep 8412767 = 12619151) B12619151
theorem B3276449 : Blo 1455547 3276449 := bstep (se 2 (by rfl) ⟨1228668, by rfl⟩ : syracuseStep 3276449 = 2457337) B2457337
theorem B6225569 : Blo 1455547 6225569 := bstep (se 2 (by rfl) ⟨2334588, by rfl⟩ : syracuseStep 6225569 = 4669177) B4669177
theorem B2457391 : Blo 1455547 2457391 := bstep (se 1 (by rfl) ⟨1843043, by rfl⟩ : syracuseStep 2457391 = 3686087) B3686087
theorem B3112751 : Blo 1455547 3112751 := bstep (se 1 (by rfl) ⟨2334563, by rfl⟩ : syracuseStep 3112751 = 4669127) B4669127
theorem B3686249 : Blo 1455547 3686249 := bstep (se 2 (by rfl) ⟨1382343, by rfl⟩ : syracuseStep 3686249 = 2764687) B2764687
theorem B18915265 : Blo 1455547 18915265 := bstep (se 2 (by rfl) ⟨7093224, by rfl⟩ : syracuseStep 18915265 = 14186449) B14186449
theorem B1843175 : Blo 1455547 1843175 := bstep (se 1 (by rfl) ⟨1382381, by rfl⟩ : syracuseStep 1843175 = 2764763) B2764763
theorem B2457911 : Blo 1455547 2457911 := bstep (se 1 (by rfl) ⟨1843433, by rfl⟩ : syracuseStep 2457911 = 3686867) B3686867
theorem B3498731 : Blo 1455547 3498731 := bstep (se 1 (by rfl) ⟨2624048, by rfl⟩ : syracuseStep 3498731 = 5248097) B5248097
theorem B3277547 : Blo 1455547 3277547 := bstep (se 1 (by rfl) ⟨2458160, by rfl⟩ : syracuseStep 3277547 = 4916321) B4916321
theorem B7873337 : Blo 1455547 7873337 := bstep (se 2 (by rfl) ⟨2952501, by rfl⟩ : syracuseStep 7873337 = 5905003) B5905003
theorem B75694925 : Blo 1455547 75694925 := bstep (se 3 (by rfl) ⟨14192798, by rfl⟩ : syracuseStep 75694925 = 28385597) B28385597
theorem B16810847 : Blo 1455547 16810847 := bstep (se 1 (by rfl) ⟨12608135, by rfl⟩ : syracuseStep 16810847 = 25216271) B25216271
theorem B2073595 : Blo 1455547 2073595 := bstep (se 1 (by rfl) ⟨1555196, by rfl⟩ : syracuseStep 2073595 = 3110393) B3110393
theorem B2458687 : Blo 1455547 2458687 := bstep (se 1 (by rfl) ⟨1844015, by rfl⟩ : syracuseStep 2458687 = 3688031) B3688031
theorem B3499337 : Blo 1455547 3499337 := bstep (se 2 (by rfl) ⟨1312251, by rfl⟩ : syracuseStep 3499337 = 2624503) B2624503
theorem B2459207 : Blo 1455547 2459207 := bstep (se 1 (by rfl) ⟨1844405, by rfl⟩ : syracuseStep 2459207 = 3688811) B3688811
theorem B3278447 : Blo 1455547 3278447 := bstep (se 1 (by rfl) ⟨2458835, by rfl⟩ : syracuseStep 3278447 = 4917671) B4917671
theorem B3278555 : Blo 1455547 3278555 := bstep (se 1 (by rfl) ⟨2458916, by rfl⟩ : syracuseStep 3278555 = 4917833) B4917833
theorem B4917023 : Blo 1455547 4917023 := bstep (se 1 (by rfl) ⟨3687767, by rfl⟩ : syracuseStep 4917023 = 7375535) B7375535
theorem B2459423 : Blo 1455547 2459423 := bstep (se 1 (by rfl) ⟨1844567, by rfl⟩ : syracuseStep 2459423 = 3689135) B3689135
theorem B4917239 : Blo 1455547 4917239 := bstep (se 1 (by rfl) ⟨3687929, by rfl⟩ : syracuseStep 4917239 = 7375859) B7375859
theorem B5531773 : Blo 1455547 5531773 := bstep (se 3 (by rfl) ⟨1037207, by rfl⟩ : syracuseStep 5531773 = 2074415) B2074415
theorem B10504495 : Blo 1455547 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B3500345 : Blo 1455547 3500345 := bstep (se 2 (by rfl) ⟨1312629, by rfl⟩ : syracuseStep 3500345 = 2625259) B2625259
theorem B2075167 : Blo 1455547 2075167 := bstep (se 1 (by rfl) ⟨1556375, by rfl⟩ : syracuseStep 2075167 = 3112751) B3112751
theorem B4426427 : Blo 1455547 4426427 := bstep (se 1 (by rfl) ⟨3319820, by rfl⟩ : syracuseStep 4426427 = 6639641) B6639641
theorem B4918103 : Blo 1455547 4918103 := bstep (se 1 (by rfl) ⟨3688577, by rfl⟩ : syracuseStep 4918103 = 7377155) B7377155
theorem B18656203 : Blo 1455547 18656203 := bstep (se 1 (by rfl) ⟨13992152, by rfl⟩ : syracuseStep 18656203 = 27984305) B27984305
theorem B4918319 : Blo 1455547 4918319 := bstep (se 1 (by rfl) ⟨3688739, by rfl⟩ : syracuseStep 4918319 = 7377479) B7377479
theorem B4320499 : Blo 1455547 4320499 := bstep (se 1 (by rfl) ⟨3240374, by rfl⟩ : syracuseStep 4320499 = 6480749) B6480749
theorem B4148603 : Blo 1455547 4148603 := bstep (se 1 (by rfl) ⟨3111452, by rfl⟩ : syracuseStep 4148603 = 6222905) B6222905
theorem B9457033 : Blo 1455547 9457033 := bstep (se 2 (by rfl) ⟨3546387, by rfl⟩ : syracuseStep 9457033 = 7092775) B7092775
theorem B2764201 : Blo 1455547 2764201 := bstep (se 2 (by rfl) ⟨1036575, by rfl⟩ : syracuseStep 2764201 = 2073151) B2073151
theorem B4918697 : Blo 1455547 4918697 := bstep (se 2 (by rfl) ⟨1844511, by rfl⟩ : syracuseStep 4918697 = 3689023) B3689023
theorem B39865861 : Blo 1455547 39865861 := bstep (se 4 (by rfl) ⟨3737424, by rfl⟩ : syracuseStep 39865861 = 7474849) B7474849
theorem B2764361 : Blo 1455547 2764361 := bstep (se 2 (by rfl) ⟨1036635, by rfl⟩ : syracuseStep 2764361 = 2073271) B2073271
theorem B9965213 : Blo 1455547 9965213 := bstep (se 3 (by rfl) ⟨1868477, by rfl⟩ : syracuseStep 9965213 = 3736955) B3736955
theorem B4919183 : Blo 1455547 4919183 := bstep (se 1 (by rfl) ⟨3689387, by rfl⟩ : syracuseStep 4919183 = 7378775) B7378775
theorem B6221947 : Blo 1455547 6221947 := bstep (se 1 (by rfl) ⟨4666460, by rfl⟩ : syracuseStep 6221947 = 9332921) B9332921
theorem B4149377 : Blo 1455547 4149377 := bstep (se 2 (by rfl) ⟨1556016, by rfl⟩ : syracuseStep 4149377 = 3112033) B3112033
theorem B7368893 : Blo 1455547 7368893 := bstep (se 3 (by rfl) ⟨1381667, by rfl⟩ : syracuseStep 7368893 = 2763335) B2763335
theorem B2183387 : Blo 1455547 2183387 := bstep (se 1 (by rfl) ⟨1637540, by rfl⟩ : syracuseStep 2183387 = 3275081) B3275081
theorem B2183399 : Blo 1455547 2183399 := bstep (se 1 (by rfl) ⟨1637549, by rfl⟩ : syracuseStep 2183399 = 3275099) B3275099
theorem B18657539 : Blo 1455547 18657539 := bstep (se 1 (by rfl) ⟨13993154, by rfl⟩ : syracuseStep 18657539 = 27986309) B27986309
theorem B4149559 : Blo 1455547 4149559 := bstep (se 1 (by rfl) ⟨3112169, by rfl⟩ : syracuseStep 4149559 = 6224339) B6224339
theorem B2183561 : Blo 1455547 2183561 := bstep (se 2 (by rfl) ⟨818835, by rfl⟩ : syracuseStep 2183561 = 1637671) B1637671
theorem B143593955 : Blo 1455547 143593955 := bstep (se 1 (by rfl) ⟨107695466, by rfl⟩ : syracuseStep 143593955 = 215390933) B215390933
theorem B24883685 : Blo 1455547 24883685 := bstep (se 4 (by rfl) ⟨2332845, by rfl⟩ : syracuseStep 24883685 = 4665691) B4665691
theorem B2183657 : Blo 1455547 2183657 := bstep (se 2 (by rfl) ⟨818871, by rfl⟩ : syracuseStep 2183657 = 1637743) B1637743
theorem B3936851 : Blo 1455547 3936851 := bstep (se 1 (by rfl) ⟨2952638, by rfl⟩ : syracuseStep 3936851 = 5905277) B5905277
theorem B239137379 : Blo 1455547 239137379 := bstep (se 1 (by rfl) ⟨179353034, by rfl⟩ : syracuseStep 239137379 = 358706069) B358706069
theorem B2183783 : Blo 1455547 2183783 := bstep (se 1 (by rfl) ⟨1637837, by rfl⟩ : syracuseStep 2183783 = 3275675) B3275675
theorem B2183915 : Blo 1455547 2183915 := bstep (se 1 (by rfl) ⟨1637936, by rfl⟩ : syracuseStep 2183915 = 3275873) B3275873
theorem B2183945 : Blo 1455547 2183945 := bstep (se 2 (by rfl) ⟨818979, by rfl⟩ : syracuseStep 2183945 = 1637959) B1637959
theorem B2184047 : Blo 1455547 2184047 := bstep (se 1 (by rfl) ⟨1638035, by rfl⟩ : syracuseStep 2184047 = 3276071) B3276071
theorem B4150187 : Blo 1455547 4150187 := bstep (se 1 (by rfl) ⟨3112640, by rfl⟩ : syracuseStep 4150187 = 6225281) B6225281
theorem B2765819 : Blo 1455547 2765819 := bstep (se 1 (by rfl) ⟨2074364, by rfl⟩ : syracuseStep 2765819 = 4148729) B4148729
theorem B100881413 : Blo 1455547 100881413 := bstep (se 4 (by rfl) ⟨9457632, by rfl⟩ : syracuseStep 100881413 = 18915265) B18915265
theorem B5608511 : Blo 1455547 5608511 := bstep (se 1 (by rfl) ⟨4206383, by rfl⟩ : syracuseStep 5608511 = 8412767) B8412767
theorem B2184299 : Blo 1455547 2184299 := bstep (se 1 (by rfl) ⟨1638224, by rfl⟩ : syracuseStep 2184299 = 3276449) B3276449
theorem B4150379 : Blo 1455547 4150379 := bstep (se 1 (by rfl) ⟨3112784, by rfl⟩ : syracuseStep 4150379 = 6225569) B6225569
theorem B2184539 : Blo 1455547 2184539 := bstep (se 1 (by rfl) ⟨1638404, by rfl⟩ : syracuseStep 2184539 = 3276809) B3276809
theorem B2766305 : Blo 1455547 2766305 := bstep (se 2 (by rfl) ⟨1037364, by rfl⟩ : syracuseStep 2766305 = 2074729) B2074729
theorem B1455727 : Blo 1455547 1455727 := bstep (se 1 (by rfl) ⟨1091795, by rfl⟩ : syracuseStep 1455727 = 2183591) B2183591
theorem B2184815 : Blo 1455547 2184815 := bstep (se 1 (by rfl) ⟨1638611, by rfl⟩ : syracuseStep 2184815 = 3277223) B3277223
theorem B9336485 : Blo 1455547 9336485 := bstep (se 4 (by rfl) ⟨875295, by rfl⟩ : syracuseStep 9336485 = 1750591) B1750591
theorem B1455783 : Blo 1455547 1455783 := bstep (se 1 (by rfl) ⟨1091837, by rfl⟩ : syracuseStep 1455783 = 2183675) B2183675
theorem B4912811 : Blo 1455547 4912811 := bstep (se 1 (by rfl) ⟨3684608, by rfl⟩ : syracuseStep 4912811 = 7369217) B7369217
theorem B4667051 : Blo 1455547 4667051 := bstep (se 1 (by rfl) ⟨3500288, by rfl⟩ : syracuseStep 4667051 = 7000577) B7000577
theorem B2184887 : Blo 1455547 2184887 := bstep (se 1 (by rfl) ⟨1638665, by rfl⟩ : syracuseStep 2184887 = 3277331) B3277331
theorem B2184923 : Blo 1455547 2184923 := bstep (se 1 (by rfl) ⟨1638692, by rfl⟩ : syracuseStep 2184923 = 3277385) B3277385
theorem B1455867 : Blo 1455547 1455867 := bstep (se 1 (by rfl) ⟨1091900, by rfl⟩ : syracuseStep 1455867 = 2183801) B2183801
theorem B1455903 : Blo 1455547 1455903 := bstep (se 1 (by rfl) ⟨1091927, by rfl⟩ : syracuseStep 1455903 = 2183855) B2183855
theorem B1455935 : Blo 1455547 1455935 := bstep (se 1 (by rfl) ⟨1091951, by rfl⟩ : syracuseStep 1455935 = 2183903) B2183903
theorem B2185097 : Blo 1455547 2185097 := bstep (se 2 (by rfl) ⟨819411, by rfl⟩ : syracuseStep 2185097 = 1638823) B1638823
theorem B4913135 : Blo 1455547 4913135 := bstep (se 1 (by rfl) ⟨3684851, by rfl⟩ : syracuseStep 4913135 = 7369703) B7369703
theorem B1456111 : Blo 1455547 1456111 := bstep (se 1 (by rfl) ⟨1092083, by rfl⟩ : syracuseStep 1456111 = 2184167) B2184167
theorem B2185199 : Blo 1455547 2185199 := bstep (se 1 (by rfl) ⟨1638899, by rfl⟩ : syracuseStep 2185199 = 3277799) B3277799
theorem B15751169 : Blo 1455547 15751169 := bstep (se 2 (by rfl) ⟨5906688, by rfl⟩ : syracuseStep 15751169 = 11813377) B11813377
theorem B10491929 : Blo 1455547 10491929 := bstep (se 2 (by rfl) ⟨3934473, by rfl⟩ : syracuseStep 10491929 = 7868947) B7868947
theorem B42563663 : Blo 1455547 42563663 := bstep (se 1 (by rfl) ⟨31922747, by rfl⟩ : syracuseStep 42563663 = 63845495) B63845495
theorem B17717383 : Blo 1455547 17717383 := bstep (se 1 (by rfl) ⟨13288037, by rfl⟩ : syracuseStep 17717383 = 26576075) B26576075
theorem B1456283 : Blo 1455547 1456283 := bstep (se 1 (by rfl) ⟨1092212, by rfl⟩ : syracuseStep 1456283 = 2184425) B2184425
theorem B1456319 : Blo 1455547 1456319 := bstep (se 1 (by rfl) ⟨1092239, by rfl⟩ : syracuseStep 1456319 = 2184479) B2184479
theorem B4913351 : Blo 1455547 4913351 := bstep (se 1 (by rfl) ⟨3685013, by rfl⟩ : syracuseStep 4913351 = 7370027) B7370027
theorem B2185451 : Blo 1455547 2185451 := bstep (se 1 (by rfl) ⟨1639088, by rfl⟩ : syracuseStep 2185451 = 3278177) B3278177
theorem B2218279 : Blo 1455547 2218279 := bstep (se 1 (by rfl) ⟨1663709, by rfl⟩ : syracuseStep 2218279 = 3327419) B3327419
theorem B3684649 : Blo 1455547 3684649 := bstep (se 2 (by rfl) ⟨1381743, by rfl⟩ : syracuseStep 3684649 = 2763487) B2763487
theorem B2185511 : Blo 1455547 2185511 := bstep (se 1 (by rfl) ⟨1639133, by rfl⟩ : syracuseStep 2185511 = 3278267) B3278267
theorem B1456431 : Blo 1455547 1456431 := bstep (se 1 (by rfl) ⟨1092323, by rfl⟩ : syracuseStep 1456431 = 2184647) B2184647
theorem B10647881 : Blo 1455547 10647881 := bstep (se 2 (by rfl) ⟨3992955, by rfl⟩ : syracuseStep 10647881 = 7985911) B7985911
theorem B10500461 : Blo 1455547 10500461 := bstep (se 3 (by rfl) ⟨1968836, by rfl⟩ : syracuseStep 10500461 = 3937673) B3937673
theorem B2333051 : Blo 1455547 2333051 := bstep (se 1 (by rfl) ⟨1749788, by rfl⟩ : syracuseStep 2333051 = 3499577) B3499577
theorem B2185595 : Blo 1455547 2185595 := bstep (se 1 (by rfl) ⟨1639196, by rfl⟩ : syracuseStep 2185595 = 3278393) B3278393
theorem B1456667 : Blo 1455547 1456667 := bstep (se 1 (by rfl) ⟨1092500, by rfl⟩ : syracuseStep 1456667 = 2185001) B2185001
theorem B1456671 : Blo 1455547 1456671 := bstep (se 1 (by rfl) ⟨1092503, by rfl⟩ : syracuseStep 1456671 = 2185007) B2185007
theorem B2185865 : Blo 1455547 2185865 := bstep (se 2 (by rfl) ⟨819699, by rfl⟩ : syracuseStep 2185865 = 1639399) B1639399
theorem B37837493 : Blo 1455547 37837493 := bstep (se 5 (by rfl) ⟨1773632, by rfl⟩ : syracuseStep 37837493 = 3547265) B3547265
theorem B2186039 : Blo 1455547 2186039 := bstep (se 1 (by rfl) ⟨1639529, by rfl⟩ : syracuseStep 2186039 = 3279059) B3279059
theorem B4913999 : Blo 1455547 4913999 := bstep (se 1 (by rfl) ⟨3685499, by rfl⟩ : syracuseStep 4913999 = 7370999) B7370999
theorem B3275603 : Blo 1455547 3275603 := bstep (se 1 (by rfl) ⟨2456702, by rfl⟩ : syracuseStep 3275603 = 4913405) B4913405
theorem B1456987 : Blo 1455547 1456987 := bstep (se 1 (by rfl) ⟨1092740, by rfl⟩ : syracuseStep 1456987 = 2185481) B2185481
theorem B2186075 : Blo 1455547 2186075 := bstep (se 1 (by rfl) ⟨1639556, by rfl⟩ : syracuseStep 2186075 = 3279113) B3279113
theorem B1457055 : Blo 1455547 1457055 := bstep (se 1 (by rfl) ⟨1092791, by rfl⟩ : syracuseStep 1457055 = 2185583) B2185583
theorem B8297387 : Blo 1455547 8297387 := bstep (se 1 (by rfl) ⟨6223040, by rfl⟩ : syracuseStep 8297387 = 12446081) B12446081
theorem B151395257 : Blo 1455547 151395257 := bstep (se 2 (by rfl) ⟨56773221, by rfl⟩ : syracuseStep 151395257 = 113546443) B113546443
theorem B26557391 : Blo 1455547 26557391 := bstep (se 1 (by rfl) ⟨19918043, by rfl⟩ : syracuseStep 26557391 = 39836087) B39836087
theorem B2456527 : Blo 1455547 2456527 := bstep (se 1 (by rfl) ⟨1842395, by rfl⟩ : syracuseStep 2456527 = 3684791) B3684791
theorem B2186219 : Blo 1455547 2186219 := bstep (se 1 (by rfl) ⟨1639664, by rfl⟩ : syracuseStep 2186219 = 3279329) B3279329
theorem B1457199 : Blo 1455547 1457199 := bstep (se 1 (by rfl) ⟨1092899, by rfl⟩ : syracuseStep 1457199 = 2185799) B2185799
theorem B1457223 : Blo 1455547 1457223 := bstep (se 1 (by rfl) ⟨1092917, by rfl⟩ : syracuseStep 1457223 = 2185835) B2185835
theorem B13999229 : Blo 1455547 13999229 := bstep (se 3 (by rfl) ⟨2624855, by rfl⟩ : syracuseStep 13999229 = 5249711) B5249711
theorem B12786827 : Blo 1455547 12786827 := bstep (se 1 (by rfl) ⟨9590120, by rfl⟩ : syracuseStep 12786827 = 19180241) B19180241
theorem B4914323 : Blo 1455547 4914323 := bstep (se 1 (by rfl) ⟨3685742, by rfl⟩ : syracuseStep 4914323 = 7371485) B7371485
theorem B1637599 : Blo 1455547 1637599 := bstep (se 1 (by rfl) ⟨1228199, by rfl⟩ : syracuseStep 1637599 = 2456399) B2456399
theorem B1457375 : Blo 1455547 1457375 := bstep (se 1 (by rfl) ⟨1093031, by rfl⟩ : syracuseStep 1457375 = 2186063) B2186063
theorem B4431097 : Blo 1455547 4431097 := bstep (se 2 (by rfl) ⟨1661661, by rfl⟩ : syracuseStep 4431097 = 3323323) B3323323
theorem B4668767 : Blo 1455547 4668767 := bstep (se 1 (by rfl) ⟨3501575, by rfl⟩ : syracuseStep 4668767 = 7003151) B7003151
theorem B3276143 : Blo 1455547 3276143 := bstep (se 1 (by rfl) ⟨2457107, by rfl⟩ : syracuseStep 3276143 = 4914215) B4914215
theorem B4914593 : Blo 1455547 4914593 := bstep (se 2 (by rfl) ⟨1842972, by rfl⟩ : syracuseStep 4914593 = 3685945) B3685945
theorem B9969095 : Blo 1455547 9969095 := bstep (se 1 (by rfl) ⟨7476821, by rfl⟩ : syracuseStep 9969095 = 14953643) B14953643
theorem B7372295 : Blo 1455547 7372295 := bstep (se 1 (by rfl) ⟨5529221, by rfl⟩ : syracuseStep 7372295 = 11058443) B11058443
theorem B4431439 : Blo 1455547 4431439 := bstep (se 1 (by rfl) ⟨3323579, by rfl⟩ : syracuseStep 4431439 = 6647159) B6647159
theorem B9961051 : Blo 1455547 9961051 := bstep (se 1 (by rfl) ⟨7470788, by rfl⟩ : syracuseStep 9961051 = 14941577) B14941577
theorem B14007917 : Blo 1455547 14007917 := bstep (se 3 (by rfl) ⟨2626484, by rfl⟩ : syracuseStep 14007917 = 5252969) B5252969
theorem B3276431 : Blo 1455547 3276431 := bstep (se 1 (by rfl) ⟨2457323, by rfl⟩ : syracuseStep 3276431 = 4914647) B4914647
theorem B2457263 : Blo 1455547 2457263 := bstep (se 1 (by rfl) ⟨1842947, by rfl⟩ : syracuseStep 2457263 = 3685895) B3685895
theorem B3276521 : Blo 1455547 3276521 := bstep (se 2 (by rfl) ⟨1228695, by rfl⟩ : syracuseStep 3276521 = 2457391) B2457391
theorem B9330461 : Blo 1455547 9330461 := bstep (se 3 (by rfl) ⟨1749461, by rfl⟩ : syracuseStep 9330461 = 3498923) B3498923
theorem B11067191 : Blo 1455547 11067191 := bstep (se 1 (by rfl) ⟨8300393, by rfl⟩ : syracuseStep 11067191 = 16600787) B16600787
theorem B2457499 : Blo 1455547 2457499 := bstep (se 1 (by rfl) ⟨1843124, by rfl⟩ : syracuseStep 2457499 = 3686249) B3686249
theorem B4915133 : Blo 1455547 4915133 := bstep (se 3 (by rfl) ⟨921587, by rfl⟩ : syracuseStep 4915133 = 1843175) B1843175
theorem B1638607 : Blo 1455547 1638607 := bstep (se 1 (by rfl) ⟨1228955, by rfl⟩ : syracuseStep 1638607 = 2457911) B2457911
theorem B11067677 : Blo 1455547 11067677 := bstep (se 3 (by rfl) ⟨2075189, by rfl⟩ : syracuseStep 11067677 = 4150379) B4150379
theorem B16589123 : Blo 1455547 16589123 := bstep (se 1 (by rfl) ⟨12441842, by rfl⟩ : syracuseStep 16589123 = 24883685) B24883685
theorem B2957705 : Blo 1455547 2957705 := bstep (se 2 (by rfl) ⟨1109139, by rfl⟩ : syracuseStep 2957705 = 2218279) B2218279
theorem B159424919 : Blo 1455547 159424919 := bstep (se 1 (by rfl) ⟨119568689, by rfl⟩ : syracuseStep 159424919 = 239137379) B239137379
theorem B23634341 : Blo 1455547 23634341 := bstep (se 4 (by rfl) ⟨2215719, by rfl⟩ : syracuseStep 23634341 = 4431439) B4431439
theorem B50463283 : Blo 1455547 50463283 := bstep (se 1 (by rfl) ⟨37847462, by rfl⟩ : syracuseStep 50463283 = 75694925) B75694925
theorem B11207231 : Blo 1455547 11207231 := bstep (se 1 (by rfl) ⟨8405423, by rfl⟩ : syracuseStep 11207231 = 16810847) B16810847
theorem B1843879 : Blo 1455547 1843879 := bstep (se 1 (by rfl) ⟨1382909, by rfl⟩ : syracuseStep 1843879 = 2765819) B2765819
theorem B1844203 : Blo 1455547 1844203 := bstep (se 1 (by rfl) ⟨1383152, by rfl⟩ : syracuseStep 1844203 = 2766305) B2766305
theorem B1639471 : Blo 1455547 1639471 := bstep (se 1 (by rfl) ⟨1229603, by rfl⟩ : syracuseStep 1639471 = 2459207) B2459207
theorem B3278015 : Blo 1455547 3278015 := bstep (se 1 (by rfl) ⟨2458511, by rfl⟩ : syracuseStep 3278015 = 4917023) B4917023
theorem B1639615 : Blo 1455547 1639615 := bstep (se 1 (by rfl) ⟨1229711, by rfl⟩ : syracuseStep 1639615 = 2459423) B2459423
theorem B3278159 : Blo 1455547 3278159 := bstep (se 1 (by rfl) ⟨2458619, by rfl⟩ : syracuseStep 3278159 = 4917239) B4917239
theorem B3278249 : Blo 1455547 3278249 := bstep (se 2 (by rfl) ⟨1229343, by rfl⟩ : syracuseStep 3278249 = 2458687) B2458687
theorem B5760665 : Blo 1455547 5760665 := bstep (se 2 (by rfl) ⟨2160249, by rfl⟩ : syracuseStep 5760665 = 4320499) B4320499
theorem B25224995 : Blo 1455547 25224995 := bstep (se 1 (by rfl) ⟨18918746, by rfl⟩ : syracuseStep 25224995 = 37837493) B37837493
theorem B12609377 : Blo 1455547 12609377 := bstep (se 2 (by rfl) ⟨4728516, by rfl⟩ : syracuseStep 12609377 = 9457033) B9457033
theorem B3278735 : Blo 1455547 3278735 := bstep (se 1 (by rfl) ⟨2459051, by rfl⟩ : syracuseStep 3278735 = 4918103) B4918103
theorem B5531591 : Blo 1455547 5531591 := bstep (se 1 (by rfl) ⟨4148693, by rfl⟩ : syracuseStep 5531591 = 8297387) B8297387
theorem B17704927 : Blo 1455547 17704927 := bstep (se 1 (by rfl) ⟨13278695, by rfl⟩ : syracuseStep 17704927 = 26557391) B26557391
theorem B3278879 : Blo 1455547 3278879 := bstep (se 1 (by rfl) ⟨2459159, by rfl⟩ : syracuseStep 3278879 = 4918319) B4918319
theorem B9332819 : Blo 1455547 9332819 := bstep (se 1 (by rfl) ⟨6999614, by rfl⟩ : syracuseStep 9332819 = 13999229) B13999229
theorem B13281401 : Blo 1455547 13281401 := bstep (se 2 (by rfl) ⟨4980525, by rfl⟩ : syracuseStep 13281401 = 9961051) B9961051
theorem B3279131 : Blo 1455547 3279131 := bstep (se 1 (by rfl) ⟨2459348, by rfl⟩ : syracuseStep 3279131 = 4918697) B4918697
theorem B6646063 : Blo 1455547 6646063 := bstep (se 1 (by rfl) ⟨4984547, by rfl⟩ : syracuseStep 6646063 = 9969095) B9969095
theorem B6220307 : Blo 1455547 6220307 := bstep (se 1 (by rfl) ⟨4665230, by rfl⟩ : syracuseStep 6220307 = 9330461) B9330461
theorem B3279455 : Blo 1455547 3279455 := bstep (se 1 (by rfl) ⟨2459591, by rfl⟩ : syracuseStep 3279455 = 4919183) B4919183
theorem B7375697 : Blo 1455547 7375697 := bstep (se 2 (by rfl) ⟨2765886, by rfl⟩ : syracuseStep 7375697 = 5531773) B5531773
theorem B12438359 : Blo 1455547 12438359 := bstep (se 1 (by rfl) ⟨9328769, by rfl⟩ : syracuseStep 12438359 = 18657539) B18657539
theorem B34098205 : Blo 1455547 34098205 := bstep (se 3 (by rfl) ⟨6393413, by rfl⟩ : syracuseStep 34098205 = 12786827) B12786827
theorem B2624567 : Blo 1455547 2624567 := bstep (se 1 (by rfl) ⟨1968425, by rfl⟩ : syracuseStep 2624567 = 3936851) B3936851
theorem B5532745 : Blo 1455547 5532745 := bstep (se 2 (by rfl) ⟨2074779, by rfl⟩ : syracuseStep 5532745 = 4149559) B4149559
theorem B3739007 : Blo 1455547 3739007 := bstep (se 1 (by rfl) ⟨2804255, by rfl⟩ : syracuseStep 3739007 = 5608511) B5608511
theorem B9334253 : Blo 1455547 9334253 := bstep (se 3 (by rfl) ⟨1750172, by rfl⟩ : syracuseStep 9334253 = 3500345) B3500345
theorem B24874937 : Blo 1455547 24874937 := bstep (se 2 (by rfl) ⟨9328101, by rfl⟩ : syracuseStep 24874937 = 18656203) B18656203
theorem B2764793 : Blo 1455547 2764793 := bstep (se 2 (by rfl) ⟨1036797, by rfl⟩ : syracuseStep 2764793 = 2073595) B2073595
theorem B7098587 : Blo 1455547 7098587 := bstep (se 1 (by rfl) ⟨5323940, by rfl⟩ : syracuseStep 7098587 = 10647881) B10647881
theorem B7000307 : Blo 1455547 7000307 := bstep (se 1 (by rfl) ⟨5250230, by rfl⟩ : syracuseStep 7000307 = 10500461) B10500461
theorem B2183465 : Blo 1455547 2183465 := bstep (se 2 (by rfl) ⟨818799, by rfl⟩ : syracuseStep 2183465 = 1637599) B1637599
theorem B2183735 : Blo 1455547 2183735 := bstep (se 1 (by rfl) ⟨1637801, by rfl⟩ : syracuseStep 2183735 = 3275603) B3275603
theorem B100930171 : Blo 1455547 100930171 := bstep (se 1 (by rfl) ⟨75697628, by rfl⟩ : syracuseStep 100930171 = 151395257) B151395257
theorem B53154481 : Blo 1455547 53154481 := bstep (se 2 (by rfl) ⟨19932930, by rfl⟩ : syracuseStep 53154481 = 39865861) B39865861
theorem B2184095 : Blo 1455547 2184095 := bstep (se 1 (by rfl) ⟨1638071, by rfl⟩ : syracuseStep 2184095 = 3276143) B3276143
theorem B2765735 : Blo 1455547 2765735 := bstep (se 1 (by rfl) ⟨2074301, by rfl⟩ : syracuseStep 2765735 = 4148603) B4148603
theorem B2184287 : Blo 1455547 2184287 := bstep (se 1 (by rfl) ⟨1638215, by rfl⟩ : syracuseStep 2184287 = 3276431) B3276431
theorem B2184347 : Blo 1455547 2184347 := bstep (se 1 (by rfl) ⟨1638260, by rfl⟩ : syracuseStep 2184347 = 3276521) B3276521
theorem B7378127 : Blo 1455547 7378127 := bstep (se 1 (by rfl) ⟨5533595, by rfl⟩ : syracuseStep 7378127 = 11067191) B11067191
theorem B2766251 : Blo 1455547 2766251 := bstep (se 1 (by rfl) ⟨2074688, by rfl⟩ : syracuseStep 2766251 = 4149377) B4149377
theorem B4912595 : Blo 1455547 4912595 := bstep (se 1 (by rfl) ⟨3684446, by rfl⟩ : syracuseStep 4912595 = 7368893) B7368893
theorem B1455591 : Blo 1455547 1455591 := bstep (se 1 (by rfl) ⟨1091693, by rfl⟩ : syracuseStep 1455591 = 2183387) B2183387
theorem B1455599 : Blo 1455547 1455599 := bstep (se 1 (by rfl) ⟨1091699, by rfl⟩ : syracuseStep 1455599 = 2183399) B2183399
theorem B8295929 : Blo 1455547 8295929 := bstep (se 2 (by rfl) ⟨3110973, by rfl⟩ : syracuseStep 8295929 = 6221947) B6221947
theorem B23623177 : Blo 1455547 23623177 := bstep (se 2 (by rfl) ⟨8858691, by rfl⟩ : syracuseStep 23623177 = 17717383) B17717383
theorem B1455707 : Blo 1455547 1455707 := bstep (se 1 (by rfl) ⟨1091780, by rfl⟩ : syracuseStep 1455707 = 2183561) B2183561
theorem B95729303 : Blo 1455547 95729303 := bstep (se 1 (by rfl) ⟨71796977, by rfl⟩ : syracuseStep 95729303 = 143593955) B143593955
theorem B1455771 : Blo 1455547 1455771 := bstep (se 1 (by rfl) ⟨1091828, by rfl⟩ : syracuseStep 1455771 = 2183657) B2183657
theorem B4912865 : Blo 1455547 4912865 := bstep (se 2 (by rfl) ⟨1842324, by rfl⟩ : syracuseStep 4912865 = 3684649) B3684649
theorem B14005993 : Blo 1455547 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B1455855 : Blo 1455547 1455855 := bstep (se 1 (by rfl) ⟨1091891, by rfl⟩ : syracuseStep 1455855 = 2183783) B2183783
theorem B1455943 : Blo 1455547 1455943 := bstep (se 1 (by rfl) ⟨1091957, by rfl⟩ : syracuseStep 1455943 = 2183915) B2183915
theorem B2332487 : Blo 1455547 2332487 := bstep (se 1 (by rfl) ⟨1749365, by rfl⟩ : syracuseStep 2332487 = 3498731) B3498731
theorem B2185031 : Blo 1455547 2185031 := bstep (se 1 (by rfl) ⟨1638773, by rfl⟩ : syracuseStep 2185031 = 3277547) B3277547
theorem B1455963 : Blo 1455547 1455963 := bstep (se 1 (by rfl) ⟨1091972, by rfl⟩ : syracuseStep 1455963 = 2183945) B2183945
theorem B5248891 : Blo 1455547 5248891 := bstep (se 1 (by rfl) ⟨3936668, by rfl⟩ : syracuseStep 5248891 = 7873337) B7873337
theorem B1456031 : Blo 1455547 1456031 := bstep (se 1 (by rfl) ⟨1092023, by rfl⟩ : syracuseStep 1456031 = 2184047) B2184047
theorem B2766791 : Blo 1455547 2766791 := bstep (se 1 (by rfl) ⟨2075093, by rfl⟩ : syracuseStep 2766791 = 4150187) B4150187
theorem B67254275 : Blo 1455547 67254275 := bstep (se 1 (by rfl) ⟨50440706, by rfl⟩ : syracuseStep 67254275 = 100881413) B100881413
theorem B2766889 : Blo 1455547 2766889 := bstep (se 2 (by rfl) ⟨1037583, by rfl⟩ : syracuseStep 2766889 = 2075167) B2075167
theorem B1456199 : Blo 1455547 1456199 := bstep (se 1 (by rfl) ⟨1092149, by rfl⟩ : syracuseStep 1456199 = 2184299) B2184299
theorem B2332891 : Blo 1455547 2332891 := bstep (se 1 (by rfl) ⟨1749668, by rfl⟩ : syracuseStep 2332891 = 3499337) B3499337
theorem B1456359 : Blo 1455547 1456359 := bstep (se 1 (by rfl) ⟨1092269, by rfl⟩ : syracuseStep 1456359 = 2184539) B2184539
theorem B1456543 : Blo 1455547 1456543 := bstep (se 1 (by rfl) ⟨1092407, by rfl⟩ : syracuseStep 1456543 = 2184815) B2184815
theorem B2185631 : Blo 1455547 2185631 := bstep (se 1 (by rfl) ⟨1639223, by rfl⟩ : syracuseStep 2185631 = 3278447) B3278447
theorem B6224323 : Blo 1455547 6224323 := bstep (se 1 (by rfl) ⟨4668242, by rfl⟩ : syracuseStep 6224323 = 9336485) B9336485
theorem B3275207 : Blo 1455547 3275207 := bstep (se 1 (by rfl) ⟨2456405, by rfl⟩ : syracuseStep 3275207 = 4912811) B4912811
theorem B3111367 : Blo 1455547 3111367 := bstep (se 1 (by rfl) ⟨2333525, by rfl⟩ : syracuseStep 3111367 = 4667051) B4667051
theorem B1456591 : Blo 1455547 1456591 := bstep (se 1 (by rfl) ⟨1092443, by rfl⟩ : syracuseStep 1456591 = 2184887) B2184887
theorem B1456615 : Blo 1455547 1456615 := bstep (se 1 (by rfl) ⟨1092461, by rfl⟩ : syracuseStep 1456615 = 2184923) B2184923
theorem B2185703 : Blo 1455547 2185703 := bstep (se 1 (by rfl) ⟨1639277, by rfl⟩ : syracuseStep 2185703 = 3278555) B3278555
theorem B1456731 : Blo 1455547 1456731 := bstep (se 1 (by rfl) ⟨1092548, by rfl⟩ : syracuseStep 1456731 = 2185097) B2185097
theorem B3275369 : Blo 1455547 3275369 := bstep (se 2 (by rfl) ⟨1228263, by rfl⟩ : syracuseStep 3275369 = 2456527) B2456527
theorem B23632517 : Blo 1455547 23632517 := bstep (se 4 (by rfl) ⟨2215548, by rfl⟩ : syracuseStep 23632517 = 4431097) B4431097
theorem B3275423 : Blo 1455547 3275423 := bstep (se 1 (by rfl) ⟨2456567, by rfl⟩ : syracuseStep 3275423 = 4913135) B4913135
theorem B1456799 : Blo 1455547 1456799 := bstep (se 1 (by rfl) ⟨1092599, by rfl⟩ : syracuseStep 1456799 = 2185199) B2185199
theorem B10500779 : Blo 1455547 10500779 := bstep (se 1 (by rfl) ⟨7875584, by rfl⟩ : syracuseStep 10500779 = 15751169) B15751169
theorem B6994619 : Blo 1455547 6994619 := bstep (se 1 (by rfl) ⟨5245964, by rfl⟩ : syracuseStep 6994619 = 10491929) B10491929
theorem B28375775 : Blo 1455547 28375775 := bstep (se 1 (by rfl) ⟨21281831, by rfl⟩ : syracuseStep 28375775 = 42563663) B42563663
theorem B3275567 : Blo 1455547 3275567 := bstep (se 1 (by rfl) ⟨2456675, by rfl⟩ : syracuseStep 3275567 = 4913351) B4913351
theorem B1456967 : Blo 1455547 1456967 := bstep (se 1 (by rfl) ⟨1092725, by rfl⟩ : syracuseStep 1456967 = 2185451) B2185451
theorem B1457007 : Blo 1455547 1457007 := bstep (se 1 (by rfl) ⟨1092755, by rfl⟩ : syracuseStep 1457007 = 2185511) B2185511
theorem B1555367 : Blo 1455547 1555367 := bstep (se 1 (by rfl) ⟨1166525, by rfl⟩ : syracuseStep 1555367 = 2333051) B2333051
theorem B1457063 : Blo 1455547 1457063 := bstep (se 1 (by rfl) ⟨1092797, by rfl⟩ : syracuseStep 1457063 = 2185595) B2185595
theorem B1457243 : Blo 1455547 1457243 := bstep (se 1 (by rfl) ⟨1092932, by rfl⟩ : syracuseStep 1457243 = 2185865) B2185865
theorem B11803805 : Blo 1455547 11803805 := bstep (se 3 (by rfl) ⟨2213213, by rfl⟩ : syracuseStep 11803805 = 4426427) B4426427
theorem B1457359 : Blo 1455547 1457359 := bstep (se 1 (by rfl) ⟨1093019, by rfl⟩ : syracuseStep 1457359 = 2186039) B2186039
theorem B3275999 : Blo 1455547 3275999 := bstep (se 1 (by rfl) ⟨2456999, by rfl⟩ : syracuseStep 3275999 = 4913999) B4913999
theorem B3685601 : Blo 1455547 3685601 := bstep (se 2 (by rfl) ⟨1382100, by rfl⟩ : syracuseStep 3685601 = 2764201) B2764201
theorem B1457383 : Blo 1455547 1457383 := bstep (se 1 (by rfl) ⟨1093037, by rfl⟩ : syracuseStep 1457383 = 2186075) B2186075
theorem B1457479 : Blo 1455547 1457479 := bstep (se 1 (by rfl) ⟨1093109, by rfl⟩ : syracuseStep 1457479 = 2186219) B2186219
theorem B3276215 : Blo 1455547 3276215 := bstep (se 1 (by rfl) ⟨2457161, by rfl⟩ : syracuseStep 3276215 = 4914323) B4914323
theorem B3112511 : Blo 1455547 3112511 := bstep (se 1 (by rfl) ⟨2334383, by rfl⟩ : syracuseStep 3112511 = 4668767) B4668767
theorem B3276395 : Blo 1455547 3276395 := bstep (se 1 (by rfl) ⟨2457296, by rfl⟩ : syracuseStep 3276395 = 4914593) B4914593
theorem B4914863 : Blo 1455547 4914863 := bstep (se 1 (by rfl) ⟨3686147, by rfl⟩ : syracuseStep 4914863 = 7372295) B7372295
theorem B1842907 : Blo 1455547 1842907 := bstep (se 1 (by rfl) ⟨1382180, by rfl⟩ : syracuseStep 1842907 = 2764361) B2764361
theorem B9338611 : Blo 1455547 9338611 := bstep (se 1 (by rfl) ⟨7003958, by rfl⟩ : syracuseStep 9338611 = 14007917) B14007917
theorem B6643475 : Blo 1455547 6643475 := bstep (se 1 (by rfl) ⟨4982606, by rfl⟩ : syracuseStep 6643475 = 9965213) B9965213
theorem B1638175 : Blo 1455547 1638175 := bstep (se 1 (by rfl) ⟨1228631, by rfl⟩ : syracuseStep 1638175 = 2457263) B2457263
theorem B3276665 : Blo 1455547 3276665 := bstep (se 2 (by rfl) ⟨1228749, by rfl⟩ : syracuseStep 3276665 = 2457499) B2457499
theorem B3276755 : Blo 1455547 3276755 := bstep (se 1 (by rfl) ⟨2457566, by rfl⟩ : syracuseStep 3276755 = 4915133) B4915133
theorem B11059415 : Blo 1455547 11059415 := bstep (se 1 (by rfl) ⟨8294561, by rfl⟩ : syracuseStep 11059415 = 16589123) B16589123
theorem B106283279 : Blo 1455547 106283279 := bstep (se 1 (by rfl) ⟨79712459, by rfl⟩ : syracuseStep 106283279 = 159424919) B159424919
theorem B7471487 : Blo 1455547 7471487 := bstep (se 1 (by rfl) ⟨5603615, by rfl⟩ : syracuseStep 7471487 = 11207231) B11207231
theorem B8299097 : Blo 1455547 8299097 := bstep (se 2 (by rfl) ⟨3112161, by rfl⟩ : syracuseStep 8299097 = 6224323) B6224323
theorem B1843823 : Blo 1455547 1843823 := bstep (se 1 (by rfl) ⟨1382867, by rfl⟩ : syracuseStep 1843823 = 2765735) B2765735
theorem B2458505 : Blo 1455547 2458505 := bstep (se 2 (by rfl) ⟨921939, by rfl⟩ : syracuseStep 2458505 = 1843879) B1843879
theorem B5530619 : Blo 1455547 5530619 := bstep (se 1 (by rfl) ⟨4147964, by rfl⟩ : syracuseStep 5530619 = 8295929) B8295929
theorem B9970685 : Blo 1455547 9970685 := bstep (se 3 (by rfl) ⟨1869503, by rfl⟩ : syracuseStep 9970685 = 3739007) B3739007
theorem B8406251 : Blo 1455547 8406251 := bstep (se 1 (by rfl) ⟨6304688, by rfl⟩ : syracuseStep 8406251 = 12609377) B12609377
theorem B3687727 : Blo 1455547 3687727 := bstep (se 1 (by rfl) ⟨2765795, by rfl⟩ : syracuseStep 3687727 = 5531591) B5531591
theorem B1844527 : Blo 1455547 1844527 := bstep (se 1 (by rfl) ⟨1383395, by rfl⟩ : syracuseStep 1844527 = 2766791) B2766791
theorem B2458937 : Blo 1455547 2458937 := bstep (se 2 (by rfl) ⟨922101, by rfl⟩ : syracuseStep 2458937 = 1844203) B1844203
theorem B44836183 : Blo 1455547 44836183 := bstep (se 1 (by rfl) ⟨33627137, by rfl⟩ : syracuseStep 44836183 = 67254275) B67254275
theorem B8300029 : Blo 1455547 8300029 := bstep (se 3 (by rfl) ⟨1556255, by rfl⟩ : syracuseStep 8300029 = 3112511) B3112511
theorem B4146871 : Blo 1455547 4146871 := bstep (se 1 (by rfl) ⟨3110153, by rfl⟩ : syracuseStep 4146871 = 6220307) B6220307
theorem B16590581 : Blo 1455547 16590581 := bstep (se 5 (by rfl) ⟨777683, by rfl⟩ : syracuseStep 16590581 = 1555367) B1555367
theorem B4663079 : Blo 1455547 4663079 := bstep (se 1 (by rfl) ⟨3497309, by rfl⟩ : syracuseStep 4663079 = 6994619) B6994619
theorem B18917183 : Blo 1455547 18917183 := bstep (se 1 (by rfl) ⟨14187887, by rfl⟩ : syracuseStep 18917183 = 28375775) B28375775
theorem B4917131 : Blo 1455547 4917131 := bstep (se 1 (by rfl) ⟨3687848, by rfl⟩ : syracuseStep 4917131 = 7375697) B7375697
theorem B8292239 : Blo 1455547 8292239 := bstep (se 1 (by rfl) ⟨6219179, by rfl⟩ : syracuseStep 8292239 = 12438359) B12438359
theorem B6219965 : Blo 1455547 6219965 := bstep (se 3 (by rfl) ⟨1166243, by rfl⟩ : syracuseStep 6219965 = 2332487) B2332487
theorem B6998521 : Blo 1455547 6998521 := bstep (se 2 (by rfl) ⟨2624445, by rfl⟩ : syracuseStep 6998521 = 5248891) B5248891
theorem B16583291 : Blo 1455547 16583291 := bstep (se 1 (by rfl) ⟨12437468, by rfl⟩ : syracuseStep 16583291 = 24874937) B24874937
theorem B3689185 : Blo 1455547 3689185 := bstep (se 2 (by rfl) ⟨1383444, by rfl⟩ : syracuseStep 3689185 = 2766889) B2766889
theorem B6998845 : Blo 1455547 6998845 := bstep (se 3 (by rfl) ⟨1312283, by rfl⟩ : syracuseStep 6998845 = 2624567) B2624567
theorem B15756227 : Blo 1455547 15756227 := bstep (se 1 (by rfl) ⟨11817170, by rfl⟩ : syracuseStep 15756227 = 23634341) B23634341
theorem B4148489 : Blo 1455547 4148489 := bstep (se 2 (by rfl) ⟨1555683, by rfl⟩ : syracuseStep 4148489 = 3111367) B3111367
theorem B67284377 : Blo 1455547 67284377 := bstep (se 2 (by rfl) ⟨25231641, by rfl⟩ : syracuseStep 67284377 = 50463283) B50463283
theorem B4918751 : Blo 1455547 4918751 := bstep (se 1 (by rfl) ⟨3689063, by rfl⟩ : syracuseStep 4918751 = 7378127) B7378127
theorem B134573561 : Blo 1455547 134573561 := bstep (se 2 (by rfl) ⟨50465085, by rfl⟩ : syracuseStep 134573561 = 100930171) B100930171
theorem B70872641 : Blo 1455547 70872641 := bstep (se 2 (by rfl) ⟨26577240, by rfl⟩ : syracuseStep 70872641 = 53154481) B53154481
theorem B63819535 : Blo 1455547 63819535 := bstep (se 1 (by rfl) ⟨47864651, by rfl⟩ : syracuseStep 63819535 = 95729303) B95729303
theorem B7376669 : Blo 1455547 7376669 := bstep (se 3 (by rfl) ⟨1383125, by rfl⟩ : syracuseStep 7376669 = 2766251) B2766251
theorem B6221879 : Blo 1455547 6221879 := bstep (se 1 (by rfl) ⟨4666409, by rfl⟩ : syracuseStep 6221879 = 9332819) B9332819
theorem B7376993 : Blo 1455547 7376993 := bstep (se 2 (by rfl) ⟨2766372, by rfl⟩ : syracuseStep 7376993 = 5532745) B5532745
theorem B2183471 : Blo 1455547 2183471 := bstep (se 1 (by rfl) ⟨1637603, by rfl⟩ : syracuseStep 2183471 = 3275207) B3275207
theorem B2183579 : Blo 1455547 2183579 := bstep (se 1 (by rfl) ⟨1637684, by rfl⟩ : syracuseStep 2183579 = 3275369) B3275369
theorem B2183615 : Blo 1455547 2183615 := bstep (se 1 (by rfl) ⟨1637711, by rfl⟩ : syracuseStep 2183615 = 3275423) B3275423
theorem B7000519 : Blo 1455547 7000519 := bstep (se 1 (by rfl) ⟨5250389, by rfl⟩ : syracuseStep 7000519 = 10500779) B10500779
theorem B2183711 : Blo 1455547 2183711 := bstep (se 1 (by rfl) ⟨1637783, by rfl⟩ : syracuseStep 2183711 = 3275567) B3275567
theorem B7869203 : Blo 1455547 7869203 := bstep (se 1 (by rfl) ⟨5901902, by rfl⟩ : syracuseStep 7869203 = 11803805) B11803805
theorem B2183999 : Blo 1455547 2183999 := bstep (se 1 (by rfl) ⟨1637999, by rfl⟩ : syracuseStep 2183999 = 3275999) B3275999
theorem B2184143 : Blo 1455547 2184143 := bstep (se 1 (by rfl) ⟨1638107, by rfl⟩ : syracuseStep 2184143 = 3276215) B3276215
theorem B18674657 : Blo 1455547 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B6222835 : Blo 1455547 6222835 := bstep (se 1 (by rfl) ⟨4667126, by rfl⟩ : syracuseStep 6222835 = 9334253) B9334253
theorem B2184233 : Blo 1455547 2184233 := bstep (se 2 (by rfl) ⟨819087, by rfl⟩ : syracuseStep 2184233 = 1638175) B1638175
theorem B2184263 : Blo 1455547 2184263 := bstep (se 1 (by rfl) ⟨1638197, by rfl⟩ : syracuseStep 2184263 = 3276395) B3276395
theorem B4428983 : Blo 1455547 4428983 := bstep (se 1 (by rfl) ⟨3321737, by rfl⟩ : syracuseStep 4428983 = 6643475) B6643475
theorem B2184443 : Blo 1455547 2184443 := bstep (se 1 (by rfl) ⟨1638332, by rfl⟩ : syracuseStep 2184443 = 3276665) B3276665
theorem B23606569 : Blo 1455547 23606569 := bstep (se 2 (by rfl) ⟨8852463, by rfl⟩ : syracuseStep 23606569 = 17704927) B17704927
theorem B2184503 : Blo 1455547 2184503 := bstep (se 1 (by rfl) ⟨1638377, by rfl⟩ : syracuseStep 2184503 = 3276755) B3276755
theorem B4732391 : Blo 1455547 4732391 := bstep (se 1 (by rfl) ⟨3549293, by rfl⟩ : syracuseStep 4732391 = 7098587) B7098587
theorem B4666871 : Blo 1455547 4666871 := bstep (se 1 (by rfl) ⟨3500153, by rfl⟩ : syracuseStep 4666871 = 7000307) B7000307
theorem B7378451 : Blo 1455547 7378451 := bstep (se 1 (by rfl) ⟨5533838, by rfl⟩ : syracuseStep 7378451 = 11067677) B11067677
theorem B1455643 : Blo 1455547 1455643 := bstep (se 1 (by rfl) ⟨1091732, by rfl⟩ : syracuseStep 1455643 = 2183465) B2183465
theorem B1971803 : Blo 1455547 1971803 := bstep (se 1 (by rfl) ⟨1478852, by rfl⟩ : syracuseStep 1971803 = 2957705) B2957705
theorem B2184809 : Blo 1455547 2184809 := bstep (se 2 (by rfl) ⟨819303, by rfl⟩ : syracuseStep 2184809 = 1638607) B1638607
theorem B1455823 : Blo 1455547 1455823 := bstep (se 1 (by rfl) ⟨1091867, by rfl⟩ : syracuseStep 1455823 = 2183735) B2183735
theorem B8861417 : Blo 1455547 8861417 := bstep (se 2 (by rfl) ⟨3323031, by rfl⟩ : syracuseStep 8861417 = 6646063) B6646063
theorem B1456063 : Blo 1455547 1456063 := bstep (se 1 (by rfl) ⟨1092047, by rfl⟩ : syracuseStep 1456063 = 2184095) B2184095
theorem B1456191 : Blo 1455547 1456191 := bstep (se 1 (by rfl) ⟨1092143, by rfl⟩ : syracuseStep 1456191 = 2184287) B2184287
theorem B1456231 : Blo 1455547 1456231 := bstep (se 1 (by rfl) ⟨1092173, by rfl⟩ : syracuseStep 1456231 = 2184347) B2184347
theorem B2185343 : Blo 1455547 2185343 := bstep (se 1 (by rfl) ⟨1639007, by rfl⟩ : syracuseStep 2185343 = 3278015) B3278015
theorem B2185439 : Blo 1455547 2185439 := bstep (se 1 (by rfl) ⟨1639079, by rfl⟩ : syracuseStep 2185439 = 3278159) B3278159
theorem B2185499 : Blo 1455547 2185499 := bstep (se 1 (by rfl) ⟨1639124, by rfl⟩ : syracuseStep 2185499 = 3278249) B3278249
theorem B3275063 : Blo 1455547 3275063 := bstep (se 1 (by rfl) ⟨2456297, by rfl⟩ : syracuseStep 3275063 = 4912595) B4912595
theorem B3840443 : Blo 1455547 3840443 := bstep (se 1 (by rfl) ⟨2880332, by rfl⟩ : syracuseStep 3840443 = 5760665) B5760665
theorem B12442085 : Blo 1455547 12442085 := bstep (se 4 (by rfl) ⟨1166445, by rfl⟩ : syracuseStep 12442085 = 2332891) B2332891
theorem B3275243 : Blo 1455547 3275243 := bstep (se 1 (by rfl) ⟨2456432, by rfl⟩ : syracuseStep 3275243 = 4912865) B4912865
theorem B16816663 : Blo 1455547 16816663 := bstep (se 1 (by rfl) ⟨12612497, by rfl⟩ : syracuseStep 16816663 = 25224995) B25224995
theorem B1456687 : Blo 1455547 1456687 := bstep (se 1 (by rfl) ⟨1092515, by rfl⟩ : syracuseStep 1456687 = 2185031) B2185031
theorem B2185823 : Blo 1455547 2185823 := bstep (se 1 (by rfl) ⟨1639367, by rfl⟩ : syracuseStep 2185823 = 3278735) B3278735
theorem B2185919 : Blo 1455547 2185919 := bstep (se 1 (by rfl) ⟨1639439, by rfl⟩ : syracuseStep 2185919 = 3278879) B3278879
theorem B45464273 : Blo 1455547 45464273 := bstep (se 2 (by rfl) ⟨17049102, by rfl⟩ : syracuseStep 45464273 = 34098205) B34098205
theorem B2185961 : Blo 1455547 2185961 := bstep (se 2 (by rfl) ⟨819735, by rfl⟩ : syracuseStep 2185961 = 1639471) B1639471
theorem B8854267 : Blo 1455547 8854267 := bstep (se 1 (by rfl) ⟨6640700, by rfl⟩ : syracuseStep 8854267 = 13281401) B13281401
theorem B2186087 : Blo 1455547 2186087 := bstep (se 1 (by rfl) ⟨1639565, by rfl⟩ : syracuseStep 2186087 = 3279131) B3279131
theorem B2186153 : Blo 1455547 2186153 := bstep (se 2 (by rfl) ⟨819807, by rfl⟩ : syracuseStep 2186153 = 1639615) B1639615
theorem B1457087 : Blo 1455547 1457087 := bstep (se 1 (by rfl) ⟨1092815, by rfl⟩ : syracuseStep 1457087 = 2185631) B2185631
theorem B1457135 : Blo 1455547 1457135 := bstep (se 1 (by rfl) ⟨1092851, by rfl⟩ : syracuseStep 1457135 = 2185703) B2185703
theorem B63020045 : Blo 1455547 63020045 := bstep (se 3 (by rfl) ⟨11816258, by rfl⟩ : syracuseStep 63020045 = 23632517) B23632517
theorem B2186303 : Blo 1455547 2186303 := bstep (se 1 (by rfl) ⟨1639727, by rfl⟩ : syracuseStep 2186303 = 3279455) B3279455
theorem B31497569 : Blo 1455547 31497569 := bstep (se 2 (by rfl) ⟨11811588, by rfl⟩ : syracuseStep 31497569 = 23623177) B23623177
theorem B2457067 : Blo 1455547 2457067 := bstep (se 1 (by rfl) ⟨1842800, by rfl⟩ : syracuseStep 2457067 = 3685601) B3685601
theorem B2457209 : Blo 1455547 2457209 := bstep (se 2 (by rfl) ⟨921453, by rfl⟩ : syracuseStep 2457209 = 1842907) B1842907
theorem B12451481 : Blo 1455547 12451481 := bstep (se 2 (by rfl) ⟨4669305, by rfl⟩ : syracuseStep 12451481 = 9338611) B9338611
theorem B3276575 : Blo 1455547 3276575 := bstep (se 1 (by rfl) ⟨2457431, by rfl⟩ : syracuseStep 3276575 = 4914863) B4914863
theorem B7372781 : Blo 1455547 7372781 := bstep (se 3 (by rfl) ⟨1382396, by rfl⟩ : syracuseStep 7372781 = 2764793) B2764793
theorem B7372943 : Blo 1455547 7372943 := bstep (se 1 (by rfl) ⟨5529707, by rfl⟩ : syracuseStep 7372943 = 11059415) B11059415
theorem B1639003 : Blo 1455547 1639003 := bstep (se 1 (by rfl) ⟨1229252, by rfl⟩ : syracuseStep 1639003 = 2458505) B2458505
theorem B9331361 : Blo 1455547 9331361 := bstep (se 2 (by rfl) ⟨3499260, by rfl⟩ : syracuseStep 9331361 = 6998521) B6998521
theorem B3687079 : Blo 1455547 3687079 := bstep (se 1 (by rfl) ⟨2765309, by rfl⟩ : syracuseStep 3687079 = 5530619) B5530619
theorem B5604167 : Blo 1455547 5604167 := bstep (se 1 (by rfl) ⟨4203125, by rfl⟩ : syracuseStep 5604167 = 8406251) B8406251
theorem B1639291 : Blo 1455547 1639291 := bstep (se 1 (by rfl) ⟨1229468, by rfl⟩ : syracuseStep 1639291 = 2458937) B2458937
theorem B11805689 : Blo 1455547 11805689 := bstep (se 2 (by rfl) ⟨4427133, by rfl⟩ : syracuseStep 11805689 = 8854267) B8854267
theorem B19923965 : Blo 1455547 19923965 := bstep (se 3 (by rfl) ⟨3735743, by rfl⟩ : syracuseStep 19923965 = 7471487) B7471487
theorem B9331793 : Blo 1455547 9331793 := bstep (se 2 (by rfl) ⟨3499422, by rfl⟩ : syracuseStep 9331793 = 6998845) B6998845
theorem B5907611 : Blo 1455547 5907611 := bstep (se 1 (by rfl) ⟨4430708, by rfl⟩ : syracuseStep 5907611 = 8861417) B8861417
theorem B11060387 : Blo 1455547 11060387 := bstep (se 1 (by rfl) ⟨8295290, by rfl⟩ : syracuseStep 11060387 = 16590581) B16590581
theorem B3278087 : Blo 1455547 3278087 := bstep (se 1 (by rfl) ⟨2458565, by rfl⟩ : syracuseStep 3278087 = 4917131) B4917131
theorem B4146643 : Blo 1455547 4146643 := bstep (se 1 (by rfl) ⟨3109982, by rfl⟩ : syracuseStep 4146643 = 6219965) B6219965
theorem B4916861 : Blo 1455547 4916861 := bstep (se 3 (by rfl) ⟨921911, by rfl⟩ : syracuseStep 4916861 = 1843823) B1843823
theorem B31475425 : Blo 1455547 31475425 := bstep (se 2 (by rfl) ⟨11803284, by rfl⟩ : syracuseStep 31475425 = 23606569) B23606569
theorem B4916969 : Blo 1455547 4916969 := bstep (se 2 (by rfl) ⟨1843863, by rfl⟩ : syracuseStep 4916969 = 3687727) B3687727
theorem B2459369 : Blo 1455547 2459369 := bstep (se 2 (by rfl) ⟨922263, by rfl⟩ : syracuseStep 2459369 = 1844527) B1844527
theorem B10504151 : Blo 1455547 10504151 := bstep (se 1 (by rfl) ⟨7878113, by rfl⟩ : syracuseStep 10504151 = 15756227) B15756227
theorem B20998379 : Blo 1455547 20998379 := bstep (se 1 (by rfl) ⟨15748784, by rfl⟩ : syracuseStep 20998379 = 31497569) B31497569
theorem B3279167 : Blo 1455547 3279167 := bstep (se 1 (by rfl) ⟨2459375, by rfl⟩ : syracuseStep 3279167 = 4918751) B4918751
theorem B85092713 : Blo 1455547 85092713 := bstep (se 2 (by rfl) ⟨31909767, by rfl⟩ : syracuseStep 85092713 = 63819535) B63819535
theorem B8300987 : Blo 1455547 8300987 := bstep (se 1 (by rfl) ⟨6225740, by rfl⟩ : syracuseStep 8300987 = 12451481) B12451481
theorem B4917779 : Blo 1455547 4917779 := bstep (se 1 (by rfl) ⟨3688334, by rfl⟩ : syracuseStep 4917779 = 7376669) B7376669
theorem B4147919 : Blo 1455547 4147919 := bstep (se 1 (by rfl) ⟨3110939, by rfl⟩ : syracuseStep 4147919 = 6221879) B6221879
theorem B4917995 : Blo 1455547 4917995 := bstep (se 1 (by rfl) ⟨3688496, by rfl⟩ : syracuseStep 4917995 = 7376993) B7376993
theorem B89688869 : Blo 1455547 89688869 := bstep (se 4 (by rfl) ⟨8408331, by rfl⟩ : syracuseStep 89688869 = 16816663) B16816663
theorem B70855519 : Blo 1455547 70855519 := bstep (se 1 (by rfl) ⟨53141639, by rfl⟩ : syracuseStep 70855519 = 106283279) B106283279
theorem B5532731 : Blo 1455547 5532731 := bstep (se 1 (by rfl) ⟨4149548, by rfl⟩ : syracuseStep 5532731 = 8299097) B8299097
theorem B5246135 : Blo 1455547 5246135 := bstep (se 1 (by rfl) ⟨3934601, by rfl⟩ : syracuseStep 5246135 = 7869203) B7869203
theorem B9334025 : Blo 1455547 9334025 := bstep (se 2 (by rfl) ⟨3500259, by rfl⟩ : syracuseStep 9334025 = 7000519) B7000519
theorem B6647123 : Blo 1455547 6647123 := bstep (se 1 (by rfl) ⟨4985342, by rfl⟩ : syracuseStep 6647123 = 9970685) B9970685
theorem B2952655 : Blo 1455547 2952655 := bstep (se 1 (by rfl) ⟨2214491, by rfl⟩ : syracuseStep 2952655 = 4428983) B4428983
theorem B4918913 : Blo 1455547 4918913 := bstep (se 2 (by rfl) ⟨1844592, by rfl⟩ : syracuseStep 4918913 = 3689185) B3689185
theorem B4918967 : Blo 1455547 4918967 := bstep (se 1 (by rfl) ⟨3689225, by rfl⟩ : syracuseStep 4918967 = 7378451) B7378451
theorem B3108719 : Blo 1455547 3108719 := bstep (se 1 (by rfl) ⟨2331539, by rfl⟩ : syracuseStep 3108719 = 4663079) B4663079
theorem B12619709 : Blo 1455547 12619709 := bstep (se 3 (by rfl) ⟨2366195, by rfl⟩ : syracuseStep 12619709 = 4732391) B4732391
theorem B2183375 : Blo 1455547 2183375 := bstep (se 1 (by rfl) ⟨1637531, by rfl⟩ : syracuseStep 2183375 = 3275063) B3275063
theorem B2560295 : Blo 1455547 2560295 := bstep (se 1 (by rfl) ⟨1920221, by rfl⟩ : syracuseStep 2560295 = 3840443) B3840443
theorem B8294723 : Blo 1455547 8294723 := bstep (se 1 (by rfl) ⟨6221042, by rfl⟩ : syracuseStep 8294723 = 12442085) B12442085
theorem B2183495 : Blo 1455547 2183495 := bstep (se 1 (by rfl) ⟨1637621, by rfl⟩ : syracuseStep 2183495 = 3275243) B3275243
theorem B11055527 : Blo 1455547 11055527 := bstep (se 1 (by rfl) ⟨8291645, by rfl⟩ : syracuseStep 11055527 = 16583291) B16583291
theorem B59781577 : Blo 1455547 59781577 := bstep (se 2 (by rfl) ⟨22418091, by rfl⟩ : syracuseStep 59781577 = 44836183) B44836183
theorem B42013363 : Blo 1455547 42013363 := bstep (se 1 (by rfl) ⟨31510022, by rfl⟩ : syracuseStep 42013363 = 63020045) B63020045
theorem B2765659 : Blo 1455547 2765659 := bstep (se 1 (by rfl) ⟨2074244, by rfl⟩ : syracuseStep 2765659 = 4148489) B4148489
theorem B44856251 : Blo 1455547 44856251 := bstep (se 1 (by rfl) ⟨33642188, by rfl⟩ : syracuseStep 44856251 = 67284377) B67284377
theorem B89715707 : Blo 1455547 89715707 := bstep (se 1 (by rfl) ⟨67286780, by rfl⟩ : syracuseStep 89715707 = 134573561) B134573561
theorem B47248427 : Blo 1455547 47248427 := bstep (se 1 (by rfl) ⟨35436320, by rfl⟩ : syracuseStep 47248427 = 70872641) B70872641
theorem B2184383 : Blo 1455547 2184383 := bstep (se 1 (by rfl) ⟨1638287, by rfl⟩ : syracuseStep 2184383 = 3276575) B3276575
theorem B1455647 : Blo 1455547 1455647 := bstep (se 1 (by rfl) ⟨1091735, by rfl⟩ : syracuseStep 1455647 = 2183471) B2183471
theorem B1455719 : Blo 1455547 1455719 := bstep (se 1 (by rfl) ⟨1091789, by rfl⟩ : syracuseStep 1455719 = 2183579) B2183579
theorem B1455743 : Blo 1455547 1455743 := bstep (se 1 (by rfl) ⟨1091807, by rfl⟩ : syracuseStep 1455743 = 2183615) B2183615
theorem B1455807 : Blo 1455547 1455807 := bstep (se 1 (by rfl) ⟨1091855, by rfl⟩ : syracuseStep 1455807 = 2183711) B2183711
theorem B1455999 : Blo 1455547 1455999 := bstep (se 1 (by rfl) ⟨1091999, by rfl⟩ : syracuseStep 1455999 = 2183999) B2183999
theorem B1456095 : Blo 1455547 1456095 := bstep (se 1 (by rfl) ⟨1092071, by rfl⟩ : syracuseStep 1456095 = 2184143) B2184143
theorem B12449771 : Blo 1455547 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B1456155 : Blo 1455547 1456155 := bstep (se 1 (by rfl) ⟨1092116, by rfl⟩ : syracuseStep 1456155 = 2184233) B2184233
theorem B1456175 : Blo 1455547 1456175 := bstep (se 1 (by rfl) ⟨1092131, by rfl⟩ : syracuseStep 1456175 = 2184263) B2184263
theorem B1456295 : Blo 1455547 1456295 := bstep (se 1 (by rfl) ⟨1092221, by rfl⟩ : syracuseStep 1456295 = 2184443) B2184443
theorem B1456335 : Blo 1455547 1456335 := bstep (se 1 (by rfl) ⟨1092251, by rfl⟩ : syracuseStep 1456335 = 2184503) B2184503
theorem B3111247 : Blo 1455547 3111247 := bstep (se 1 (by rfl) ⟨2333435, by rfl⟩ : syracuseStep 3111247 = 4666871) B4666871
theorem B1456539 : Blo 1455547 1456539 := bstep (se 1 (by rfl) ⟨1092404, by rfl⟩ : syracuseStep 1456539 = 2184809) B2184809
theorem B5528159 : Blo 1455547 5528159 := bstep (se 1 (by rfl) ⟨4146119, by rfl⟩ : syracuseStep 5528159 = 8292239) B8292239
theorem B8297113 : Blo 1455547 8297113 := bstep (se 2 (by rfl) ⟨3111417, by rfl⟩ : syracuseStep 8297113 = 6222835) B6222835
theorem B1456895 : Blo 1455547 1456895 := bstep (se 1 (by rfl) ⟨1092671, by rfl⟩ : syracuseStep 1456895 = 2185343) B2185343
theorem B1456959 : Blo 1455547 1456959 := bstep (se 1 (by rfl) ⟨1092719, by rfl⟩ : syracuseStep 1456959 = 2185439) B2185439
theorem B1456999 : Blo 1455547 1456999 := bstep (se 1 (by rfl) ⟨1092749, by rfl⟩ : syracuseStep 1456999 = 2185499) B2185499
theorem B5258141 : Blo 1455547 5258141 := bstep (se 3 (by rfl) ⟨985901, by rfl⟩ : syracuseStep 5258141 = 1971803) B1971803
theorem B1457215 : Blo 1455547 1457215 := bstep (se 1 (by rfl) ⟨1092911, by rfl⟩ : syracuseStep 1457215 = 2185823) B2185823
theorem B1457279 : Blo 1455547 1457279 := bstep (se 1 (by rfl) ⟨1092959, by rfl⟩ : syracuseStep 1457279 = 2185919) B2185919
theorem B30309515 : Blo 1455547 30309515 := bstep (se 1 (by rfl) ⟨22732136, by rfl⟩ : syracuseStep 30309515 = 45464273) B45464273
theorem B1457307 : Blo 1455547 1457307 := bstep (se 1 (by rfl) ⟨1092980, by rfl⟩ : syracuseStep 1457307 = 2185961) B2185961
theorem B1457391 : Blo 1455547 1457391 := bstep (se 1 (by rfl) ⟨1093043, by rfl⟩ : syracuseStep 1457391 = 2186087) B2186087
theorem B1457435 : Blo 1455547 1457435 := bstep (se 1 (by rfl) ⟨1093076, by rfl⟩ : syracuseStep 1457435 = 2186153) B2186153
theorem B3276089 : Blo 1455547 3276089 := bstep (se 2 (by rfl) ⟨1228533, by rfl⟩ : syracuseStep 3276089 = 2457067) B2457067
theorem B11066705 : Blo 1455547 11066705 := bstep (se 2 (by rfl) ⟨4150014, by rfl⟩ : syracuseStep 11066705 = 8300029) B8300029
theorem B1457535 : Blo 1455547 1457535 := bstep (se 1 (by rfl) ⟨1093151, by rfl⟩ : syracuseStep 1457535 = 2186303) B2186303
theorem B50445821 : Blo 1455547 50445821 := bstep (se 3 (by rfl) ⟨9458591, by rfl⟩ : syracuseStep 50445821 = 18917183) B18917183
theorem B5529161 : Blo 1455547 5529161 := bstep (se 2 (by rfl) ⟨2073435, by rfl⟩ : syracuseStep 5529161 = 4146871) B4146871
theorem B1638139 : Blo 1455547 1638139 := bstep (se 1 (by rfl) ⟨1228604, by rfl⟩ : syracuseStep 1638139 = 2457209) B2457209
theorem B4915187 : Blo 1455547 4915187 := bstep (se 1 (by rfl) ⟨3686390, by rfl⟩ : syracuseStep 4915187 = 7372781) B7372781
theorem B4915295 : Blo 1455547 4915295 := bstep (se 1 (by rfl) ⟨3686471, by rfl⟩ : syracuseStep 4915295 = 7372943) B7372943
theorem B5529815 : Blo 1455547 5529815 := bstep (se 1 (by rfl) ⟨4147361, by rfl⟩ : syracuseStep 5529815 = 8294723) B8294723
theorem B15753629 : Blo 1455547 15753629 := bstep (se 3 (by rfl) ⟨2953805, by rfl⟩ : syracuseStep 15753629 = 5907611) B5907611
theorem B3736111 : Blo 1455547 3736111 := bstep (se 1 (by rfl) ⟨2802083, by rfl⟩ : syracuseStep 3736111 = 5604167) B5604167
theorem B79708769 : Blo 1455547 79708769 := bstep (se 2 (by rfl) ⟨29890788, by rfl⟩ : syracuseStep 79708769 = 59781577) B59781577
theorem B59810471 : Blo 1455547 59810471 := bstep (se 1 (by rfl) ⟨44857853, by rfl⟩ : syracuseStep 59810471 = 89715707) B89715707
theorem B31498951 : Blo 1455547 31498951 := bstep (se 1 (by rfl) ⟨23624213, by rfl⟩ : syracuseStep 31498951 = 47248427) B47248427
theorem B7373591 : Blo 1455547 7373591 := bstep (se 1 (by rfl) ⟨5530193, by rfl⟩ : syracuseStep 7373591 = 11060387) B11060387
theorem B4916105 : Blo 1455547 4916105 := bstep (se 2 (by rfl) ⟨1843539, by rfl⟩ : syracuseStep 4916105 = 3687079) B3687079
theorem B56017817 : Blo 1455547 56017817 := bstep (se 2 (by rfl) ⟨21006681, by rfl⟩ : syracuseStep 56017817 = 42013363) B42013363
theorem B3277907 : Blo 1455547 3277907 := bstep (se 1 (by rfl) ⟨2458430, by rfl⟩ : syracuseStep 3277907 = 4916861) B4916861
theorem B3687545 : Blo 1455547 3687545 := bstep (se 2 (by rfl) ⟨1382829, by rfl⟩ : syracuseStep 3687545 = 2765659) B2765659
theorem B3277979 : Blo 1455547 3277979 := bstep (se 1 (by rfl) ⟨2458484, by rfl⟩ : syracuseStep 3277979 = 4916969) B4916969
theorem B1639579 : Blo 1455547 1639579 := bstep (se 1 (by rfl) ⟨1229684, by rfl⟩ : syracuseStep 1639579 = 2459369) B2459369
theorem B8299847 : Blo 1455547 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B3278519 : Blo 1455547 3278519 := bstep (se 1 (by rfl) ⟨2458889, by rfl⟩ : syracuseStep 3278519 = 4917779) B4917779
theorem B3278663 : Blo 1455547 3278663 := bstep (se 1 (by rfl) ⟨2458997, by rfl⟩ : syracuseStep 3278663 = 4917995) B4917995
theorem B3688487 : Blo 1455547 3688487 := bstep (se 1 (by rfl) ⟨2766365, by rfl⟩ : syracuseStep 3688487 = 5532731) B5532731
theorem B33630547 : Blo 1455547 33630547 := bstep (se 1 (by rfl) ⟨25222910, by rfl⟩ : syracuseStep 33630547 = 50445821) B50445821
theorem B15747493 : Blo 1455547 15747493 := bstep (se 4 (by rfl) ⟨1476327, by rfl⟩ : syracuseStep 15747493 = 2952655) B2952655
theorem B3279275 : Blo 1455547 3279275 := bstep (se 1 (by rfl) ⟨2459456, by rfl⟩ : syracuseStep 3279275 = 4918913) B4918913
theorem B3279311 : Blo 1455547 3279311 := bstep (se 1 (by rfl) ⟨2459483, by rfl⟩ : syracuseStep 3279311 = 4918967) B4918967
theorem B4148329 : Blo 1455547 4148329 := bstep (se 2 (by rfl) ⟨1555623, by rfl⟩ : syracuseStep 4148329 = 3111247) B3111247
theorem B6220907 : Blo 1455547 6220907 := bstep (se 1 (by rfl) ⟨4665680, by rfl⟩ : syracuseStep 6220907 = 9331361) B9331361
theorem B29904167 : Blo 1455547 29904167 := bstep (se 1 (by rfl) ⟨22428125, by rfl⟩ : syracuseStep 29904167 = 44856251) B44856251
theorem B13282643 : Blo 1455547 13282643 := bstep (se 1 (by rfl) ⟨9961982, by rfl⟩ : syracuseStep 13282643 = 19923965) B19923965
theorem B6221195 : Blo 1455547 6221195 := bstep (se 1 (by rfl) ⟨4665896, by rfl⟩ : syracuseStep 6221195 = 9331793) B9331793
theorem B6827453 : Blo 1455547 6827453 := bstep (se 3 (by rfl) ⟨1280147, by rfl⟩ : syracuseStep 6827453 = 2560295) B2560295
theorem B11062817 : Blo 1455547 11062817 := bstep (se 2 (by rfl) ⟨4148556, by rfl⟩ : syracuseStep 11062817 = 8297113) B8297113
theorem B94474025 : Blo 1455547 94474025 := bstep (se 2 (by rfl) ⟨35427759, by rfl⟩ : syracuseStep 94474025 = 70855519) B70855519
theorem B3276791 : Blo 1455547 3276791 := bstep (se 1 (by rfl) ⟨2457593, by rfl⟩ : syracuseStep 3276791 = 4915187) B4915187
theorem B5533991 : Blo 1455547 5533991 := bstep (se 1 (by rfl) ⟨4150493, by rfl⟩ : syracuseStep 5533991 = 8300987) B8300987
theorem B2765279 : Blo 1455547 2765279 := bstep (se 1 (by rfl) ⟨2073959, by rfl⟩ : syracuseStep 2765279 = 4147919) B4147919
theorem B20206343 : Blo 1455547 20206343 := bstep (se 1 (by rfl) ⟨15154757, by rfl⟩ : syracuseStep 20206343 = 30309515) B30309515
theorem B6222683 : Blo 1455547 6222683 := bstep (se 1 (by rfl) ⟨4667012, by rfl⟩ : syracuseStep 6222683 = 9334025) B9334025
theorem B2184059 : Blo 1455547 2184059 := bstep (se 1 (by rfl) ⟨1638044, by rfl⟩ : syracuseStep 2184059 = 3276089) B3276089
theorem B7377803 : Blo 1455547 7377803 := bstep (se 1 (by rfl) ⟨5533352, by rfl⟩ : syracuseStep 7377803 = 11066705) B11066705
theorem B2184185 : Blo 1455547 2184185 := bstep (se 2 (by rfl) ⟨819069, by rfl⟩ : syracuseStep 2184185 = 1638139) B1638139
theorem B1455583 : Blo 1455547 1455583 := bstep (se 1 (by rfl) ⟨1091687, by rfl⟩ : syracuseStep 1455583 = 2183375) B2183375
theorem B1455663 : Blo 1455547 1455663 := bstep (se 1 (by rfl) ⟨1091747, by rfl⟩ : syracuseStep 1455663 = 2183495) B2183495
theorem B7370351 : Blo 1455547 7370351 := bstep (se 1 (by rfl) ⟨5527763, by rfl⟩ : syracuseStep 7370351 = 11055527) B11055527
theorem B7870459 : Blo 1455547 7870459 := bstep (se 1 (by rfl) ⟨5902844, by rfl⟩ : syracuseStep 7870459 = 11805689) B11805689
theorem B2185337 : Blo 1455547 2185337 := bstep (se 2 (by rfl) ⟨819501, by rfl⟩ : syracuseStep 2185337 = 1639003) B1639003
theorem B1456255 : Blo 1455547 1456255 := bstep (se 1 (by rfl) ⟨1092191, by rfl⟩ : syracuseStep 1456255 = 2184383) B2184383
theorem B2185391 : Blo 1455547 2185391 := bstep (se 1 (by rfl) ⟨1639043, by rfl⟩ : syracuseStep 2185391 = 3278087) B3278087
theorem B2185721 : Blo 1455547 2185721 := bstep (se 2 (by rfl) ⟨819645, by rfl⟩ : syracuseStep 2185721 = 1639291) B1639291
theorem B7002767 : Blo 1455547 7002767 := bstep (se 1 (by rfl) ⟨5252075, by rfl⟩ : syracuseStep 7002767 = 10504151) B10504151
theorem B13998919 : Blo 1455547 13998919 := bstep (se 1 (by rfl) ⟨10499189, by rfl⟩ : syracuseStep 13998919 = 20998379) B20998379
theorem B2186111 : Blo 1455547 2186111 := bstep (se 1 (by rfl) ⟨1639583, by rfl⟩ : syracuseStep 2186111 = 3279167) B3279167
theorem B56728475 : Blo 1455547 56728475 := bstep (se 1 (by rfl) ⟨42546356, by rfl⟩ : syracuseStep 56728475 = 85092713) B85092713
theorem B3685439 : Blo 1455547 3685439 := bstep (se 1 (by rfl) ⟨2764079, by rfl⟩ : syracuseStep 3685439 = 5528159) B5528159
theorem B59792579 : Blo 1455547 59792579 := bstep (se 1 (by rfl) ⟨44844434, by rfl⟩ : syracuseStep 59792579 = 89688869) B89688869
theorem B3505427 : Blo 1455547 3505427 := bstep (se 1 (by rfl) ⟨2629070, by rfl⟩ : syracuseStep 3505427 = 5258141) B5258141
theorem B5528857 : Blo 1455547 5528857 := bstep (se 2 (by rfl) ⟨2073321, by rfl⟩ : syracuseStep 5528857 = 4146643) B4146643
theorem B3497423 : Blo 1455547 3497423 := bstep (se 1 (by rfl) ⟨2623067, by rfl⟩ : syracuseStep 3497423 = 5246135) B5246135
theorem B4431415 : Blo 1455547 4431415 := bstep (se 1 (by rfl) ⟨3323561, by rfl⟩ : syracuseStep 4431415 = 6647123) B6647123
theorem B41967233 : Blo 1455547 41967233 := bstep (se 2 (by rfl) ⟨15737712, by rfl⟩ : syracuseStep 41967233 = 31475425) B31475425
theorem B3686107 : Blo 1455547 3686107 := bstep (se 1 (by rfl) ⟨2764580, by rfl⟩ : syracuseStep 3686107 = 5529161) B5529161
theorem B2072479 : Blo 1455547 2072479 := bstep (se 1 (by rfl) ⟨1554359, by rfl⟩ : syracuseStep 2072479 = 3108719) B3108719
theorem B8413139 : Blo 1455547 8413139 := bstep (se 1 (by rfl) ⟨6309854, by rfl⟩ : syracuseStep 8413139 = 12619709) B12619709
theorem B3276863 : Blo 1455547 3276863 := bstep (se 1 (by rfl) ⟨2457647, by rfl⟩ : syracuseStep 3276863 = 4915295) B4915295
theorem B3686543 : Blo 1455547 3686543 := bstep (se 1 (by rfl) ⟨2764907, by rfl⟩ : syracuseStep 3686543 = 5529815) B5529815
theorem B10502419 : Blo 1455547 10502419 := bstep (se 1 (by rfl) ⟨7876814, by rfl⟩ : syracuseStep 10502419 = 15753629) B15753629
theorem B4915727 : Blo 1455547 4915727 := bstep (se 1 (by rfl) ⟨3686795, by rfl⟩ : syracuseStep 4915727 = 7373591) B7373591
theorem B20996657 : Blo 1455547 20996657 := bstep (se 2 (by rfl) ⟨7873746, by rfl⟩ : syracuseStep 20996657 = 15747493) B15747493
theorem B3277403 : Blo 1455547 3277403 := bstep (se 1 (by rfl) ⟨2458052, by rfl⟩ : syracuseStep 3277403 = 4916105) B4916105
theorem B4981481 : Blo 1455547 4981481 := bstep (se 2 (by rfl) ⟨1868055, by rfl⟩ : syracuseStep 4981481 = 3736111) B3736111
theorem B2458363 : Blo 1455547 2458363 := bstep (se 1 (by rfl) ⟨1843772, by rfl⟩ : syracuseStep 2458363 = 3687545) B3687545
theorem B7374077 : Blo 1455547 7374077 := bstep (se 3 (by rfl) ⟨1382639, by rfl⟩ : syracuseStep 7374077 = 2765279) B2765279
theorem B2458991 : Blo 1455547 2458991 := bstep (se 1 (by rfl) ⟨1844243, by rfl⟩ : syracuseStep 2458991 = 3688487) B3688487
theorem B5531105 : Blo 1455547 5531105 := bstep (se 2 (by rfl) ⟨2074164, by rfl⟩ : syracuseStep 5531105 = 4148329) B4148329
theorem B4147271 : Blo 1455547 4147271 := bstep (se 1 (by rfl) ⟨3110453, by rfl⟩ : syracuseStep 4147271 = 6220907) B6220907
theorem B5908553 : Blo 1455547 5908553 := bstep (se 2 (by rfl) ⟨2215707, by rfl⟩ : syracuseStep 5908553 = 4431415) B4431415
theorem B2336951 : Blo 1455547 2336951 := bstep (se 1 (by rfl) ⟨1752713, by rfl⟩ : syracuseStep 2336951 = 3505427) B3505427
theorem B4147463 : Blo 1455547 4147463 := bstep (se 1 (by rfl) ⟨3110597, by rfl⟩ : syracuseStep 4147463 = 6221195) B6221195
theorem B7375211 : Blo 1455547 7375211 := bstep (se 1 (by rfl) ⟨5531408, by rfl⟩ : syracuseStep 7375211 = 11062817) B11062817
theorem B27978155 : Blo 1455547 27978155 := bstep (se 1 (by rfl) ⟨20983616, by rfl⟩ : syracuseStep 27978155 = 41967233) B41967233
theorem B62982683 : Blo 1455547 62982683 := bstep (se 1 (by rfl) ⟨47237012, by rfl⟩ : syracuseStep 62982683 = 94474025) B94474025
theorem B2763305 : Blo 1455547 2763305 := bstep (se 2 (by rfl) ⟨1036239, by rfl⟩ : syracuseStep 2763305 = 2072479) B2072479
theorem B3689327 : Blo 1455547 3689327 := bstep (se 1 (by rfl) ⟨2766995, by rfl⟩ : syracuseStep 3689327 = 5533991) B5533991
theorem B39873647 : Blo 1455547 39873647 := bstep (se 1 (by rfl) ⟨29905235, by rfl⟩ : syracuseStep 39873647 = 59810471) B59810471
theorem B13470895 : Blo 1455547 13470895 := bstep (se 1 (by rfl) ⟨10103171, by rfl⟩ : syracuseStep 13470895 = 20206343) B20206343
theorem B4148455 : Blo 1455547 4148455 := bstep (se 1 (by rfl) ⟨3111341, by rfl⟩ : syracuseStep 4148455 = 6222683) B6222683
theorem B4918535 : Blo 1455547 4918535 := bstep (se 1 (by rfl) ⟨3688901, by rfl⟩ : syracuseStep 4918535 = 7377803) B7377803
theorem B79744445 : Blo 1455547 79744445 := bstep (se 3 (by rfl) ⟨14952083, by rfl⟩ : syracuseStep 79744445 = 29904167) B29904167
theorem B5533231 : Blo 1455547 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B18665225 : Blo 1455547 18665225 := bstep (se 2 (by rfl) ⟨6999459, by rfl⟩ : syracuseStep 18665225 = 13998919) B13998919
theorem B37818983 : Blo 1455547 37818983 := bstep (se 1 (by rfl) ⟨28364237, by rfl⟩ : syracuseStep 37818983 = 56728475) B56728475
theorem B4551635 : Blo 1455547 4551635 := bstep (se 1 (by rfl) ⟨3413726, by rfl⟩ : syracuseStep 4551635 = 6827453) B6827453
theorem B5608759 : Blo 1455547 5608759 := bstep (se 1 (by rfl) ⟨4206569, by rfl⟩ : syracuseStep 5608759 = 8413139) B8413139
theorem B2184527 : Blo 1455547 2184527 := bstep (se 1 (by rfl) ⟨1638395, by rfl⟩ : syracuseStep 2184527 = 3276791) B3276791
theorem B53139179 : Blo 1455547 53139179 := bstep (se 1 (by rfl) ⟨39854384, by rfl⟩ : syracuseStep 53139179 = 79708769) B79708769
theorem B44840729 : Blo 1455547 44840729 := bstep (se 2 (by rfl) ⟨16815273, by rfl⟩ : syracuseStep 44840729 = 33630547) B33630547
theorem B1456039 : Blo 1455547 1456039 := bstep (se 1 (by rfl) ⟨1092029, by rfl⟩ : syracuseStep 1456039 = 2184059) B2184059
theorem B37345211 : Blo 1455547 37345211 := bstep (se 1 (by rfl) ⟨28008908, by rfl⟩ : syracuseStep 37345211 = 56017817) B56017817
theorem B1456123 : Blo 1455547 1456123 := bstep (se 1 (by rfl) ⟨1092092, by rfl⟩ : syracuseStep 1456123 = 2184185) B2184185
theorem B2185271 : Blo 1455547 2185271 := bstep (se 1 (by rfl) ⟨1638953, by rfl⟩ : syracuseStep 2185271 = 3277907) B3277907
theorem B2185319 : Blo 1455547 2185319 := bstep (se 1 (by rfl) ⟨1638989, by rfl⟩ : syracuseStep 2185319 = 3277979) B3277979
theorem B41998601 : Blo 1455547 41998601 := bstep (se 2 (by rfl) ⟨15749475, by rfl⟩ : syracuseStep 41998601 = 31498951) B31498951
theorem B4913567 : Blo 1455547 4913567 := bstep (se 1 (by rfl) ⟨3685175, by rfl⟩ : syracuseStep 4913567 = 7370351) B7370351
theorem B2185679 : Blo 1455547 2185679 := bstep (se 1 (by rfl) ⟨1639259, by rfl⟩ : syracuseStep 2185679 = 3278519) B3278519
theorem B2185775 : Blo 1455547 2185775 := bstep (se 1 (by rfl) ⟨1639331, by rfl⟩ : syracuseStep 2185775 = 3278663) B3278663
theorem B1456891 : Blo 1455547 1456891 := bstep (se 1 (by rfl) ⟨1092668, by rfl⟩ : syracuseStep 1456891 = 2185337) B2185337
theorem B1456927 : Blo 1455547 1456927 := bstep (se 1 (by rfl) ⟨1092695, by rfl⟩ : syracuseStep 1456927 = 2185391) B2185391
theorem B2186105 : Blo 1455547 2186105 := bstep (se 2 (by rfl) ⟨819789, by rfl⟩ : syracuseStep 2186105 = 1639579) B1639579
theorem B2186183 : Blo 1455547 2186183 := bstep (se 1 (by rfl) ⟨1639637, by rfl⟩ : syracuseStep 2186183 = 3279275) B3279275
theorem B2186207 : Blo 1455547 2186207 := bstep (se 1 (by rfl) ⟨1639655, by rfl⟩ : syracuseStep 2186207 = 3279311) B3279311
theorem B1457147 : Blo 1455547 1457147 := bstep (se 1 (by rfl) ⟨1092860, by rfl⟩ : syracuseStep 1457147 = 2185721) B2185721
theorem B7371809 : Blo 1455547 7371809 := bstep (se 2 (by rfl) ⟨2764428, by rfl⟩ : syracuseStep 7371809 = 5528857) B5528857
theorem B4668511 : Blo 1455547 4668511 := bstep (se 1 (by rfl) ⟨3501383, by rfl⟩ : syracuseStep 4668511 = 7002767) B7002767
theorem B1457407 : Blo 1455547 1457407 := bstep (se 1 (by rfl) ⟨1093055, by rfl⟩ : syracuseStep 1457407 = 2186111) B2186111
theorem B2456959 : Blo 1455547 2456959 := bstep (se 1 (by rfl) ⟨1842719, by rfl⟩ : syracuseStep 2456959 = 3685439) B3685439
theorem B39861719 : Blo 1455547 39861719 := bstep (se 1 (by rfl) ⟨29896289, by rfl⟩ : syracuseStep 39861719 = 59792579) B59792579
theorem B37305845 : Blo 1455547 37305845 := bstep (se 5 (by rfl) ⟨1748711, by rfl⟩ : syracuseStep 37305845 = 3497423) B3497423
theorem B8855095 : Blo 1455547 8855095 := bstep (se 1 (by rfl) ⟨6641321, by rfl⟩ : syracuseStep 8855095 = 13282643) B13282643
theorem B4914809 : Blo 1455547 4914809 := bstep (se 2 (by rfl) ⟨1843053, by rfl⟩ : syracuseStep 4914809 = 3686107) B3686107
theorem B10493945 : Blo 1455547 10493945 := bstep (se 2 (by rfl) ⟨3935229, by rfl⟩ : syracuseStep 10493945 = 7870459) B7870459
theorem B2457695 : Blo 1455547 2457695 := bstep (se 1 (by rfl) ⟨1843271, by rfl⟩ : syracuseStep 2457695 = 3686543) B3686543
theorem B3277151 : Blo 1455547 3277151 := bstep (se 1 (by rfl) ⟨2457863, by rfl⟩ : syracuseStep 3277151 = 4915727) B4915727
theorem B11059901 : Blo 1455547 11059901 := bstep (se 3 (by rfl) ⟨2073731, by rfl⟩ : syracuseStep 11059901 = 4147463) B4147463
theorem B4916051 : Blo 1455547 4916051 := bstep (se 1 (by rfl) ⟨3687038, by rfl⟩ : syracuseStep 4916051 = 7374077) B7374077
theorem B1639327 : Blo 1455547 1639327 := bstep (se 1 (by rfl) ⟨1229495, by rfl⟩ : syracuseStep 1639327 = 2458991) B2458991
theorem B3687403 : Blo 1455547 3687403 := bstep (se 1 (by rfl) ⟨2765552, by rfl⟩ : syracuseStep 3687403 = 5531105) B5531105
theorem B3277817 : Blo 1455547 3277817 := bstep (se 2 (by rfl) ⟨1229181, by rfl⟩ : syracuseStep 3277817 = 2458363) B2458363
theorem B29893819 : Blo 1455547 29893819 := bstep (se 1 (by rfl) ⟨22420364, by rfl⟩ : syracuseStep 29893819 = 44840729) B44840729
theorem B24896807 : Blo 1455547 24896807 := bstep (se 1 (by rfl) ⟨18672605, by rfl⟩ : syracuseStep 24896807 = 37345211) B37345211
theorem B4916807 : Blo 1455547 4916807 := bstep (se 1 (by rfl) ⟨3687605, by rfl⟩ : syracuseStep 4916807 = 7375211) B7375211
theorem B5531273 : Blo 1455547 5531273 := bstep (se 2 (by rfl) ⟨2074227, by rfl⟩ : syracuseStep 5531273 = 4148455) B4148455
theorem B2459551 : Blo 1455547 2459551 := bstep (se 1 (by rfl) ⟨1844663, by rfl⟩ : syracuseStep 2459551 = 3689327) B3689327
theorem B11806793 : Blo 1455547 11806793 := bstep (se 2 (by rfl) ⟨4427547, by rfl⟩ : syracuseStep 11806793 = 8855095) B8855095
theorem B3279023 : Blo 1455547 3279023 := bstep (se 1 (by rfl) ⟨2459267, by rfl⟩ : syracuseStep 3279023 = 4918535) B4918535
theorem B53135797 : Blo 1455547 53135797 := bstep (se 5 (by rfl) ⟨2490740, by rfl⟩ : syracuseStep 53135797 = 4981481) B4981481
theorem B14003225 : Blo 1455547 14003225 := bstep (se 2 (by rfl) ⟨5251209, by rfl⟩ : syracuseStep 14003225 = 10502419) B10502419
theorem B3034423 : Blo 1455547 3034423 := bstep (se 1 (by rfl) ⟨2275817, by rfl⟩ : syracuseStep 3034423 = 4551635) B4551635
theorem B35426119 : Blo 1455547 35426119 := bstep (se 1 (by rfl) ⟨26569589, by rfl⟩ : syracuseStep 35426119 = 53139179) B53139179
theorem B2764847 : Blo 1455547 2764847 := bstep (se 1 (by rfl) ⟨2073635, by rfl⟩ : syracuseStep 2764847 = 4147271) B4147271
theorem B17961193 : Blo 1455547 17961193 := bstep (se 2 (by rfl) ⟨6735447, by rfl⟩ : syracuseStep 17961193 = 13470895) B13470895
theorem B41988455 : Blo 1455547 41988455 := bstep (se 1 (by rfl) ⟨31491341, by rfl⟩ : syracuseStep 41988455 = 62982683) B62982683
theorem B7377641 : Blo 1455547 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B53162963 : Blo 1455547 53162963 := bstep (se 1 (by rfl) ⟨39872222, by rfl⟩ : syracuseStep 53162963 = 79744445) B79744445
theorem B2184575 : Blo 1455547 2184575 := bstep (se 1 (by rfl) ⟨1638431, by rfl⟩ : syracuseStep 2184575 = 3276863) B3276863
theorem B13997771 : Blo 1455547 13997771 := bstep (se 1 (by rfl) ⟨10498328, by rfl⟩ : syracuseStep 13997771 = 20996657) B20996657
theorem B2184935 : Blo 1455547 2184935 := bstep (se 1 (by rfl) ⟨1638701, by rfl⟩ : syracuseStep 2184935 = 3277403) B3277403
theorem B25212655 : Blo 1455547 25212655 := bstep (se 1 (by rfl) ⟨18909491, by rfl⟩ : syracuseStep 25212655 = 37818983) B37818983
theorem B6231869 : Blo 1455547 6231869 := bstep (se 3 (by rfl) ⟨1168475, by rfl⟩ : syracuseStep 6231869 = 2336951) B2336951
theorem B1456351 : Blo 1455547 1456351 := bstep (se 1 (by rfl) ⟨1092263, by rfl⟩ : syracuseStep 1456351 = 2184527) B2184527
theorem B1456847 : Blo 1455547 1456847 := bstep (se 1 (by rfl) ⟨1092635, by rfl⟩ : syracuseStep 1456847 = 2185271) B2185271
theorem B3939035 : Blo 1455547 3939035 := bstep (se 1 (by rfl) ⟨2954276, by rfl⟩ : syracuseStep 3939035 = 5908553) B5908553
theorem B1456879 : Blo 1455547 1456879 := bstep (se 1 (by rfl) ⟨1092659, by rfl⟩ : syracuseStep 1456879 = 2185319) B2185319
theorem B6224681 : Blo 1455547 6224681 := bstep (se 2 (by rfl) ⟨2334255, by rfl⟩ : syracuseStep 6224681 = 4668511) B4668511
theorem B27999067 : Blo 1455547 27999067 := bstep (se 1 (by rfl) ⟨20999300, by rfl⟩ : syracuseStep 27999067 = 41998601) B41998601
theorem B3275711 : Blo 1455547 3275711 := bstep (se 1 (by rfl) ⟨2456783, by rfl⟩ : syracuseStep 3275711 = 4913567) B4913567
theorem B18652103 : Blo 1455547 18652103 := bstep (se 1 (by rfl) ⟨13989077, by rfl⟩ : syracuseStep 18652103 = 27978155) B27978155
theorem B1457119 : Blo 1455547 1457119 := bstep (se 1 (by rfl) ⟨1092839, by rfl⟩ : syracuseStep 1457119 = 2185679) B2185679
theorem B1842203 : Blo 1455547 1842203 := bstep (se 1 (by rfl) ⟨1381652, by rfl⟩ : syracuseStep 1842203 = 2763305) B2763305
theorem B1457183 : Blo 1455547 1457183 := bstep (se 1 (by rfl) ⟨1092887, by rfl⟩ : syracuseStep 1457183 = 2185775) B2185775
theorem B7478345 : Blo 1455547 7478345 := bstep (se 2 (by rfl) ⟨2804379, by rfl⟩ : syracuseStep 7478345 = 5608759) B5608759
theorem B3275945 : Blo 1455547 3275945 := bstep (se 2 (by rfl) ⟨1228479, by rfl⟩ : syracuseStep 3275945 = 2456959) B2456959
theorem B1457403 : Blo 1455547 1457403 := bstep (se 1 (by rfl) ⟨1093052, by rfl⟩ : syracuseStep 1457403 = 2186105) B2186105
theorem B1457455 : Blo 1455547 1457455 := bstep (se 1 (by rfl) ⟨1093091, by rfl⟩ : syracuseStep 1457455 = 2186183) B2186183
theorem B1457471 : Blo 1455547 1457471 := bstep (se 1 (by rfl) ⟨1093103, by rfl⟩ : syracuseStep 1457471 = 2186207) B2186207
theorem B4914539 : Blo 1455547 4914539 := bstep (se 1 (by rfl) ⟨3685904, by rfl⟩ : syracuseStep 4914539 = 7371809) B7371809
theorem B26582431 : Blo 1455547 26582431 := bstep (se 1 (by rfl) ⟨19936823, by rfl⟩ : syracuseStep 26582431 = 39873647) B39873647
theorem B26574479 : Blo 1455547 26574479 := bstep (se 1 (by rfl) ⟨19930859, by rfl⟩ : syracuseStep 26574479 = 39861719) B39861719
theorem B24870563 : Blo 1455547 24870563 := bstep (se 1 (by rfl) ⟨18652922, by rfl⟩ : syracuseStep 24870563 = 37305845) B37305845
theorem B3276539 : Blo 1455547 3276539 := bstep (se 1 (by rfl) ⟨2457404, by rfl⟩ : syracuseStep 3276539 = 4914809) B4914809
theorem B12443483 : Blo 1455547 12443483 := bstep (se 1 (by rfl) ⟨9332612, by rfl⟩ : syracuseStep 12443483 = 18665225) B18665225
theorem B6995963 : Blo 1455547 6995963 := bstep (se 1 (by rfl) ⟨5246972, by rfl⟩ : syracuseStep 6995963 = 10493945) B10493945
theorem B1843231 : Blo 1455547 1843231 := bstep (se 1 (by rfl) ⟨1382423, by rfl⟩ : syracuseStep 1843231 = 2764847) B2764847
theorem B1638463 : Blo 1455547 1638463 := bstep (se 1 (by rfl) ⟨1228847, by rfl⟩ : syracuseStep 1638463 = 2457695) B2457695
theorem B27992303 : Blo 1455547 27992303 := bstep (se 1 (by rfl) ⟨20994227, by rfl⟩ : syracuseStep 27992303 = 41988455) B41988455
theorem B7373267 : Blo 1455547 7373267 := bstep (se 1 (by rfl) ⟨5529950, by rfl⟩ : syracuseStep 7373267 = 11059901) B11059901
theorem B3277367 : Blo 1455547 3277367 := bstep (se 1 (by rfl) ⟨2458025, by rfl⟩ : syracuseStep 3277367 = 4916051) B4916051
theorem B16597871 : Blo 1455547 16597871 := bstep (se 1 (by rfl) ⟨12448403, by rfl⟩ : syracuseStep 16597871 = 24896807) B24896807
theorem B3277871 : Blo 1455547 3277871 := bstep (se 1 (by rfl) ⟨2458403, by rfl⟩ : syracuseStep 3277871 = 4916807) B4916807
theorem B3687515 : Blo 1455547 3687515 := bstep (se 1 (by rfl) ⟨2765636, by rfl⟩ : syracuseStep 3687515 = 5531273) B5531273
theorem B37332089 : Blo 1455547 37332089 := bstep (se 2 (by rfl) ⟨13999533, by rfl⟩ : syracuseStep 37332089 = 27999067) B27999067
theorem B9331847 : Blo 1455547 9331847 := bstep (se 1 (by rfl) ⟨6998885, by rfl⟩ : syracuseStep 9331847 = 13997771) B13997771
theorem B4154579 : Blo 1455547 4154579 := bstep (se 1 (by rfl) ⟨3115934, by rfl⟩ : syracuseStep 4154579 = 6231869) B6231869
theorem B4916537 : Blo 1455547 4916537 := bstep (se 2 (by rfl) ⟨1843701, by rfl⟩ : syracuseStep 4916537 = 3687403) B3687403
theorem B10504093 : Blo 1455547 10504093 := bstep (se 3 (by rfl) ⟨1969517, by rfl⟩ : syracuseStep 10504093 = 3939035) B3939035
theorem B3279401 : Blo 1455547 3279401 := bstep (se 2 (by rfl) ⟨1229775, by rfl⟩ : syracuseStep 3279401 = 2459551) B2459551
theorem B4663975 : Blo 1455547 4663975 := bstep (se 1 (by rfl) ⟨3497981, by rfl⟩ : syracuseStep 4663975 = 6995963) B6995963
theorem B4918427 : Blo 1455547 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B70847729 : Blo 1455547 70847729 := bstep (se 2 (by rfl) ⟨26567898, by rfl⟩ : syracuseStep 70847729 = 53135797) B53135797
theorem B35441975 : Blo 1455547 35441975 := bstep (se 1 (by rfl) ⟨26581481, by rfl⟩ : syracuseStep 35441975 = 53162963) B53162963
theorem B95793029 : Blo 1455547 95793029 := bstep (se 4 (by rfl) ⟨8980596, by rfl⟩ : syracuseStep 95793029 = 17961193) B17961193
theorem B39858425 : Blo 1455547 39858425 := bstep (se 2 (by rfl) ⟨14946909, by rfl⟩ : syracuseStep 39858425 = 29893819) B29893819
theorem B4149787 : Blo 1455547 4149787 := bstep (se 1 (by rfl) ⟨3112340, by rfl⟩ : syracuseStep 4149787 = 6224681) B6224681
theorem B35443241 : Blo 1455547 35443241 := bstep (se 2 (by rfl) ⟨13291215, by rfl⟩ : syracuseStep 35443241 = 26582431) B26582431
theorem B2183807 : Blo 1455547 2183807 := bstep (se 1 (by rfl) ⟨1637855, by rfl⟩ : syracuseStep 2183807 = 3275711) B3275711
theorem B9335483 : Blo 1455547 9335483 := bstep (se 1 (by rfl) ⟨7001612, by rfl⟩ : syracuseStep 9335483 = 14003225) B14003225
theorem B4985563 : Blo 1455547 4985563 := bstep (se 1 (by rfl) ⟨3739172, by rfl⟩ : syracuseStep 4985563 = 7478345) B7478345
theorem B2183963 : Blo 1455547 2183963 := bstep (se 1 (by rfl) ⟨1637972, by rfl⟩ : syracuseStep 2183963 = 3275945) B3275945
theorem B33616873 : Blo 1455547 33616873 := bstep (se 2 (by rfl) ⟨12606327, by rfl⟩ : syracuseStep 33616873 = 25212655) B25212655
theorem B17716319 : Blo 1455547 17716319 := bstep (se 1 (by rfl) ⟨13287239, by rfl⟩ : syracuseStep 17716319 = 26574479) B26574479
theorem B2184359 : Blo 1455547 2184359 := bstep (se 1 (by rfl) ⟨1638269, by rfl⟩ : syracuseStep 2184359 = 3276539) B3276539
theorem B8295655 : Blo 1455547 8295655 := bstep (se 1 (by rfl) ⟨6221741, by rfl⟩ : syracuseStep 8295655 = 12443483) B12443483
theorem B4912541 : Blo 1455547 4912541 := bstep (se 3 (by rfl) ⟨921101, by rfl⟩ : syracuseStep 4912541 = 1842203) B1842203
theorem B2184767 : Blo 1455547 2184767 := bstep (se 1 (by rfl) ⟨1638575, by rfl⟩ : syracuseStep 2184767 = 3277151) B3277151
theorem B2185211 : Blo 1455547 2185211 := bstep (se 1 (by rfl) ⟨1638908, by rfl⟩ : syracuseStep 2185211 = 3277817) B3277817
theorem B1456383 : Blo 1455547 1456383 := bstep (se 1 (by rfl) ⟨1092287, by rfl⟩ : syracuseStep 1456383 = 2184575) B2184575
theorem B1456623 : Blo 1455547 1456623 := bstep (se 1 (by rfl) ⟨1092467, by rfl⟩ : syracuseStep 1456623 = 2184935) B2184935
theorem B2185769 : Blo 1455547 2185769 := bstep (se 2 (by rfl) ⟨819663, by rfl⟩ : syracuseStep 2185769 = 1639327) B1639327
theorem B7871195 : Blo 1455547 7871195 := bstep (se 1 (by rfl) ⟨5903396, by rfl⟩ : syracuseStep 7871195 = 11806793) B11806793
theorem B2186015 : Blo 1455547 2186015 := bstep (se 1 (by rfl) ⟨1639511, by rfl⟩ : syracuseStep 2186015 = 3279023) B3279023
theorem B4045897 : Blo 1455547 4045897 := bstep (se 2 (by rfl) ⟨1517211, by rfl⟩ : syracuseStep 4045897 = 3034423) B3034423
theorem B12434735 : Blo 1455547 12434735 := bstep (se 1 (by rfl) ⟨9326051, by rfl⟩ : syracuseStep 12434735 = 18652103) B18652103
theorem B3276359 : Blo 1455547 3276359 := bstep (se 1 (by rfl) ⟨2457269, by rfl⟩ : syracuseStep 3276359 = 4914539) B4914539
theorem B47234825 : Blo 1455547 47234825 := bstep (se 2 (by rfl) ⟨17713059, by rfl⟩ : syracuseStep 47234825 = 35426119) B35426119
theorem B16580375 : Blo 1455547 16580375 := bstep (se 1 (by rfl) ⟨12435281, by rfl⟩ : syracuseStep 16580375 = 24870563) B24870563
theorem B2457641 : Blo 1455547 2457641 := bstep (se 2 (by rfl) ⟨921615, by rfl⟩ : syracuseStep 2457641 = 1843231) B1843231
theorem B18661535 : Blo 1455547 18661535 := bstep (se 1 (by rfl) ⟨13996151, by rfl⟩ : syracuseStep 18661535 = 27992303) B27992303
theorem B4915511 : Blo 1455547 4915511 := bstep (se 1 (by rfl) ⟨3686633, by rfl⟩ : syracuseStep 4915511 = 7373267) B7373267
theorem B2458343 : Blo 1455547 2458343 := bstep (se 1 (by rfl) ⟨1843757, by rfl⟩ : syracuseStep 2458343 = 3687515) B3687515
theorem B24888059 : Blo 1455547 24888059 := bstep (se 1 (by rfl) ⟨18666044, by rfl⟩ : syracuseStep 24888059 = 37332089) B37332089
theorem B2769719 : Blo 1455547 2769719 := bstep (se 1 (by rfl) ⟨2077289, by rfl⟩ : syracuseStep 2769719 = 4154579) B4154579
theorem B3277691 : Blo 1455547 3277691 := bstep (se 1 (by rfl) ⟨2458268, by rfl⟩ : syracuseStep 3277691 = 4916537) B4916537
theorem B6218633 : Blo 1455547 6218633 := bstep (se 2 (by rfl) ⟨2331987, by rfl⟩ : syracuseStep 6218633 = 4663975) B4663975
theorem B11060873 : Blo 1455547 11060873 := bstep (se 2 (by rfl) ⟨4147827, by rfl⟩ : syracuseStep 11060873 = 8295655) B8295655
theorem B3278951 : Blo 1455547 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B23627983 : Blo 1455547 23627983 := bstep (se 1 (by rfl) ⟨17720987, by rfl⟩ : syracuseStep 23627983 = 35441975) B35441975
theorem B11053583 : Blo 1455547 11053583 := bstep (se 1 (by rfl) ⟨8290187, by rfl⟩ : syracuseStep 11053583 = 16580375) B16580375
theorem B23628827 : Blo 1455547 23628827 := bstep (se 1 (by rfl) ⟨17721620, by rfl⟩ : syracuseStep 23628827 = 35443241) B35443241
theorem B5533049 : Blo 1455547 5533049 := bstep (se 2 (by rfl) ⟨2074893, by rfl⟩ : syracuseStep 5533049 = 4149787) B4149787
theorem B6221231 : Blo 1455547 6221231 := bstep (se 1 (by rfl) ⟨4665923, by rfl⟩ : syracuseStep 6221231 = 9331847) B9331847
theorem B6647417 : Blo 1455547 6647417 := bstep (se 2 (by rfl) ⟨2492781, by rfl⟩ : syracuseStep 6647417 = 4985563) B4985563
theorem B44822497 : Blo 1455547 44822497 := bstep (se 2 (by rfl) ⟨16808436, by rfl⟩ : syracuseStep 44822497 = 33616873) B33616873
theorem B5394529 : Blo 1455547 5394529 := bstep (se 2 (by rfl) ⟨2022948, by rfl⟩ : syracuseStep 5394529 = 4045897) B4045897
theorem B5247463 : Blo 1455547 5247463 := bstep (se 1 (by rfl) ⟨3935597, by rfl⟩ : syracuseStep 5247463 = 7871195) B7871195
theorem B47231819 : Blo 1455547 47231819 := bstep (se 1 (by rfl) ⟨35423864, by rfl⟩ : syracuseStep 47231819 = 70847729) B70847729
theorem B2184239 : Blo 1455547 2184239 := bstep (se 1 (by rfl) ⟨1638179, by rfl⟩ : syracuseStep 2184239 = 3276359) B3276359
theorem B14005457 : Blo 1455547 14005457 := bstep (se 2 (by rfl) ⟨5252046, by rfl⟩ : syracuseStep 14005457 = 10504093) B10504093
theorem B63862019 : Blo 1455547 63862019 := bstep (se 1 (by rfl) ⟨47896514, by rfl⟩ : syracuseStep 63862019 = 95793029) B95793029
theorem B2184617 : Blo 1455547 2184617 := bstep (se 2 (by rfl) ⟨819231, by rfl⟩ : syracuseStep 2184617 = 1638463) B1638463
theorem B26572283 : Blo 1455547 26572283 := bstep (se 1 (by rfl) ⟨19929212, by rfl⟩ : syracuseStep 26572283 = 39858425) B39858425
theorem B2184911 : Blo 1455547 2184911 := bstep (se 1 (by rfl) ⟨1638683, by rfl⟩ : syracuseStep 2184911 = 3277367) B3277367
theorem B1455871 : Blo 1455547 1455871 := bstep (se 1 (by rfl) ⟨1091903, by rfl⟩ : syracuseStep 1455871 = 2183807) B2183807
theorem B6223655 : Blo 1455547 6223655 := bstep (se 1 (by rfl) ⟨4667741, by rfl⟩ : syracuseStep 6223655 = 9335483) B9335483
theorem B1455975 : Blo 1455547 1455975 := bstep (se 1 (by rfl) ⟨1091981, by rfl⟩ : syracuseStep 1455975 = 2183963) B2183963
theorem B11065247 : Blo 1455547 11065247 := bstep (se 1 (by rfl) ⟨8298935, by rfl⟩ : syracuseStep 11065247 = 16597871) B16597871
theorem B2185247 : Blo 1455547 2185247 := bstep (se 1 (by rfl) ⟨1638935, by rfl⟩ : syracuseStep 2185247 = 3277871) B3277871
theorem B11810879 : Blo 1455547 11810879 := bstep (se 1 (by rfl) ⟨8858159, by rfl⟩ : syracuseStep 11810879 = 17716319) B17716319
theorem B1456239 : Blo 1455547 1456239 := bstep (se 1 (by rfl) ⟨1092179, by rfl⟩ : syracuseStep 1456239 = 2184359) B2184359
theorem B3275027 : Blo 1455547 3275027 := bstep (se 1 (by rfl) ⟨2456270, by rfl⟩ : syracuseStep 3275027 = 4912541) B4912541
theorem B1456511 : Blo 1455547 1456511 := bstep (se 1 (by rfl) ⟨1092383, by rfl⟩ : syracuseStep 1456511 = 2184767) B2184767
theorem B1456807 : Blo 1455547 1456807 := bstep (se 1 (by rfl) ⟨1092605, by rfl⟩ : syracuseStep 1456807 = 2185211) B2185211
theorem B1457179 : Blo 1455547 1457179 := bstep (se 1 (by rfl) ⟨1092884, by rfl⟩ : syracuseStep 1457179 = 2185769) B2185769
theorem B2186267 : Blo 1455547 2186267 := bstep (se 1 (by rfl) ⟨1639700, by rfl⟩ : syracuseStep 2186267 = 3279401) B3279401
theorem B1457343 : Blo 1455547 1457343 := bstep (se 1 (by rfl) ⟨1093007, by rfl⟩ : syracuseStep 1457343 = 2186015) B2186015
theorem B8289823 : Blo 1455547 8289823 := bstep (se 1 (by rfl) ⟨6217367, by rfl⟩ : syracuseStep 8289823 = 12434735) B12434735
theorem B31489883 : Blo 1455547 31489883 := bstep (se 1 (by rfl) ⟨23617412, by rfl⟩ : syracuseStep 31489883 = 47234825) B47234825
theorem B1638427 : Blo 1455547 1638427 := bstep (se 1 (by rfl) ⟨1228820, by rfl⟩ : syracuseStep 1638427 = 2457641) B2457641
theorem B3277007 : Blo 1455547 3277007 := bstep (se 1 (by rfl) ⟨2457755, by rfl⟩ : syracuseStep 3277007 = 4915511) B4915511
theorem B1638895 : Blo 1455547 1638895 := bstep (se 1 (by rfl) ⟨1229171, by rfl⟩ : syracuseStep 1638895 = 2458343) B2458343
theorem B28770821 : Blo 1455547 28770821 := bstep (se 4 (by rfl) ⟨2697264, by rfl⟩ : syracuseStep 28770821 = 5394529) B5394529
theorem B4145755 : Blo 1455547 4145755 := bstep (se 1 (by rfl) ⟨3109316, by rfl⟩ : syracuseStep 4145755 = 6218633) B6218633
theorem B6996617 : Blo 1455547 6996617 := bstep (se 2 (by rfl) ⟨2623731, by rfl⟩ : syracuseStep 6996617 = 5247463) B5247463
theorem B42574679 : Blo 1455547 42574679 := bstep (se 1 (by rfl) ⟨31931009, by rfl⟩ : syracuseStep 42574679 = 63862019) B63862019
theorem B7373915 : Blo 1455547 7373915 := bstep (se 1 (by rfl) ⟨5530436, by rfl⟩ : syracuseStep 7373915 = 11060873) B11060873
theorem B7873919 : Blo 1455547 7873919 := bstep (se 1 (by rfl) ⟨5905439, by rfl⟩ : syracuseStep 7873919 = 11810879) B11810879
theorem B11053097 : Blo 1455547 11053097 := bstep (se 2 (by rfl) ⟨4144911, by rfl⟩ : syracuseStep 11053097 = 8289823) B8289823
theorem B3688699 : Blo 1455547 3688699 := bstep (se 1 (by rfl) ⟨2766524, by rfl⟩ : syracuseStep 3688699 = 5533049) B5533049
theorem B4147487 : Blo 1455547 4147487 := bstep (se 1 (by rfl) ⟨3110615, by rfl⟩ : syracuseStep 4147487 = 6221231) B6221231
theorem B59763329 : Blo 1455547 59763329 := bstep (se 2 (by rfl) ⟨22411248, by rfl⟩ : syracuseStep 59763329 = 44822497) B44822497
theorem B16592039 : Blo 1455547 16592039 := bstep (se 1 (by rfl) ⟨12444029, by rfl⟩ : syracuseStep 16592039 = 24888059) B24888059
theorem B17714855 : Blo 1455547 17714855 := bstep (se 1 (by rfl) ⟨13286141, by rfl⟩ : syracuseStep 17714855 = 26572283) B26572283
theorem B7376831 : Blo 1455547 7376831 := bstep (se 1 (by rfl) ⟨5532623, by rfl⟩ : syracuseStep 7376831 = 11065247) B11065247
theorem B2183351 : Blo 1455547 2183351 := bstep (se 1 (by rfl) ⟨1637513, by rfl⟩ : syracuseStep 2183351 = 3275027) B3275027
theorem B7369055 : Blo 1455547 7369055 := bstep (se 1 (by rfl) ⟨5526791, by rfl⟩ : syracuseStep 7369055 = 11053583) B11053583
theorem B7385917 : Blo 1455547 7385917 := bstep (se 3 (by rfl) ⟨1384859, by rfl⟩ : syracuseStep 7385917 = 2769719) B2769719
theorem B20993255 : Blo 1455547 20993255 := bstep (se 1 (by rfl) ⟨15744941, by rfl⟩ : syracuseStep 20993255 = 31489883) B31489883
theorem B12441023 : Blo 1455547 12441023 := bstep (se 1 (by rfl) ⟨9330767, by rfl⟩ : syracuseStep 12441023 = 18661535) B18661535
theorem B31503977 : Blo 1455547 31503977 := bstep (se 2 (by rfl) ⟨11813991, by rfl⟩ : syracuseStep 31503977 = 23627983) B23627983
theorem B31487879 : Blo 1455547 31487879 := bstep (se 1 (by rfl) ⟨23615909, by rfl⟩ : syracuseStep 31487879 = 47231819) B47231819
theorem B2185127 : Blo 1455547 2185127 := bstep (se 1 (by rfl) ⟨1638845, by rfl⟩ : syracuseStep 2185127 = 3277691) B3277691
theorem B1456159 : Blo 1455547 1456159 := bstep (se 1 (by rfl) ⟨1092119, by rfl⟩ : syracuseStep 1456159 = 2184239) B2184239
theorem B9336971 : Blo 1455547 9336971 := bstep (se 1 (by rfl) ⟨7002728, by rfl⟩ : syracuseStep 9336971 = 14005457) B14005457
theorem B1456411 : Blo 1455547 1456411 := bstep (se 1 (by rfl) ⟨1092308, by rfl⟩ : syracuseStep 1456411 = 2184617) B2184617
theorem B1456607 : Blo 1455547 1456607 := bstep (se 1 (by rfl) ⟨1092455, by rfl⟩ : syracuseStep 1456607 = 2184911) B2184911
theorem B1456831 : Blo 1455547 1456831 := bstep (se 1 (by rfl) ⟨1092623, by rfl⟩ : syracuseStep 1456831 = 2185247) B2185247
theorem B2185967 : Blo 1455547 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B15752551 : Blo 1455547 15752551 := bstep (se 1 (by rfl) ⟨11814413, by rfl⟩ : syracuseStep 15752551 = 23628827) B23628827
theorem B1457511 : Blo 1455547 1457511 := bstep (se 1 (by rfl) ⟨1093133, by rfl⟩ : syracuseStep 1457511 = 2186267) B2186267
theorem B16596413 : Blo 1455547 16596413 := bstep (se 3 (by rfl) ⟨3111827, by rfl⟩ : syracuseStep 16596413 = 6223655) B6223655
theorem B4431611 : Blo 1455547 4431611 := bstep (se 1 (by rfl) ⟨3323708, by rfl⟩ : syracuseStep 4431611 = 6647417) B6647417
theorem B4915943 : Blo 1455547 4915943 := bstep (se 1 (by rfl) ⟨3686957, by rfl⟩ : syracuseStep 4915943 = 7373915) B7373915
theorem B9847889 : Blo 1455547 9847889 := bstep (se 2 (by rfl) ⟨3692958, by rfl⟩ : syracuseStep 9847889 = 7385917) B7385917
theorem B11061359 : Blo 1455547 11061359 := bstep (se 1 (by rfl) ⟨8296019, by rfl⟩ : syracuseStep 11061359 = 16592039) B16592039
theorem B4917887 : Blo 1455547 4917887 := bstep (se 1 (by rfl) ⟨3688415, by rfl⟩ : syracuseStep 4917887 = 7376831) B7376831
theorem B4918265 : Blo 1455547 4918265 := bstep (se 2 (by rfl) ⟨1844349, by rfl⟩ : syracuseStep 4918265 = 3688699) B3688699
theorem B19180547 : Blo 1455547 19180547 := bstep (se 1 (by rfl) ⟨14385410, by rfl⟩ : syracuseStep 19180547 = 28770821) B28770821
theorem B4664411 : Blo 1455547 4664411 := bstep (se 1 (by rfl) ⟨3498308, by rfl⟩ : syracuseStep 4664411 = 6996617) B6996617
theorem B13995503 : Blo 1455547 13995503 := bstep (se 1 (by rfl) ⟨10496627, by rfl⟩ : syracuseStep 13995503 = 20993255) B20993255
theorem B8294015 : Blo 1455547 8294015 := bstep (se 1 (by rfl) ⟨6220511, by rfl⟩ : syracuseStep 8294015 = 12441023) B12441023
theorem B7368731 : Blo 1455547 7368731 := bstep (se 1 (by rfl) ⟨5526548, by rfl⟩ : syracuseStep 7368731 = 11053097) B11053097
theorem B2764991 : Blo 1455547 2764991 := bstep (se 1 (by rfl) ⟨2073743, by rfl⟩ : syracuseStep 2764991 = 4147487) B4147487
theorem B39842219 : Blo 1455547 39842219 := bstep (se 1 (by rfl) ⟨29881664, by rfl⟩ : syracuseStep 39842219 = 59763329) B59763329
theorem B11064275 : Blo 1455547 11064275 := bstep (se 1 (by rfl) ⟨8298206, by rfl⟩ : syracuseStep 11064275 = 16596413) B16596413
theorem B11809903 : Blo 1455547 11809903 := bstep (se 1 (by rfl) ⟨8857427, by rfl⟩ : syracuseStep 11809903 = 17714855) B17714855
theorem B2954407 : Blo 1455547 2954407 := bstep (se 1 (by rfl) ⟨2215805, by rfl⟩ : syracuseStep 2954407 = 4431611) B4431611
theorem B2184569 : Blo 1455547 2184569 := bstep (se 2 (by rfl) ⟨819213, by rfl⟩ : syracuseStep 2184569 = 1638427) B1638427
theorem B1455567 : Blo 1455547 1455567 := bstep (se 1 (by rfl) ⟨1091675, by rfl⟩ : syracuseStep 1455567 = 2183351) B2183351
theorem B2184671 : Blo 1455547 2184671 := bstep (se 1 (by rfl) ⟨1638503, by rfl⟩ : syracuseStep 2184671 = 3277007) B3277007
theorem B4912703 : Blo 1455547 4912703 := bstep (se 1 (by rfl) ⟨3684527, by rfl⟩ : syracuseStep 4912703 = 7369055) B7369055
theorem B28383119 : Blo 1455547 28383119 := bstep (se 1 (by rfl) ⟨21287339, by rfl⟩ : syracuseStep 28383119 = 42574679) B42574679
theorem B2185193 : Blo 1455547 2185193 := bstep (se 2 (by rfl) ⟨819447, by rfl⟩ : syracuseStep 2185193 = 1638895) B1638895
theorem B5527673 : Blo 1455547 5527673 := bstep (se 2 (by rfl) ⟨2072877, by rfl⟩ : syracuseStep 5527673 = 4145755) B4145755
theorem B5249279 : Blo 1455547 5249279 := bstep (se 1 (by rfl) ⟨3936959, by rfl⟩ : syracuseStep 5249279 = 7873919) B7873919
theorem B21002651 : Blo 1455547 21002651 := bstep (se 1 (by rfl) ⟨15751988, by rfl⟩ : syracuseStep 21002651 = 31503977) B31503977
theorem B1456751 : Blo 1455547 1456751 := bstep (se 1 (by rfl) ⟨1092563, by rfl⟩ : syracuseStep 1456751 = 2185127) B2185127
theorem B6224647 : Blo 1455547 6224647 := bstep (se 1 (by rfl) ⟨4668485, by rfl⟩ : syracuseStep 6224647 = 9336971) B9336971
theorem B21003401 : Blo 1455547 21003401 := bstep (se 2 (by rfl) ⟨7876275, by rfl⟩ : syracuseStep 21003401 = 15752551) B15752551
theorem B1457311 : Blo 1455547 1457311 := bstep (se 1 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 1457311 = 2185967) B2185967
theorem B83967677 : Blo 1455547 83967677 := bstep (se 3 (by rfl) ⟨15743939, by rfl⟩ : syracuseStep 83967677 = 31487879) B31487879
theorem B1843327 : Blo 1455547 1843327 := bstep (se 1 (by rfl) ⟨1382495, by rfl⟩ : syracuseStep 1843327 = 2764991) B2764991
theorem B3277295 : Blo 1455547 3277295 := bstep (se 1 (by rfl) ⟨2457971, by rfl⟩ : syracuseStep 3277295 = 4915943) B4915943
theorem B8299529 : Blo 1455547 8299529 := bstep (se 2 (by rfl) ⟨3112323, by rfl⟩ : syracuseStep 8299529 = 6224647) B6224647
theorem B7374239 : Blo 1455547 7374239 := bstep (se 1 (by rfl) ⟨5530679, by rfl⟩ : syracuseStep 7374239 = 11061359) B11061359
theorem B15746537 : Blo 1455547 15746537 := bstep (se 2 (by rfl) ⟨5904951, by rfl⟩ : syracuseStep 15746537 = 11809903) B11809903
theorem B3499519 : Blo 1455547 3499519 := bstep (se 1 (by rfl) ⟨2624639, by rfl⟩ : syracuseStep 3499519 = 5249279) B5249279
theorem B14001767 : Blo 1455547 14001767 := bstep (se 1 (by rfl) ⟨10501325, by rfl⟩ : syracuseStep 14001767 = 21002651) B21002651
theorem B3278591 : Blo 1455547 3278591 := bstep (se 1 (by rfl) ⟨2458943, by rfl⟩ : syracuseStep 3278591 = 4917887) B4917887
theorem B3278843 : Blo 1455547 3278843 := bstep (se 1 (by rfl) ⟨2459132, by rfl⟩ : syracuseStep 3278843 = 4918265) B4918265
theorem B14002267 : Blo 1455547 14002267 := bstep (se 1 (by rfl) ⟨10501700, by rfl⟩ : syracuseStep 14002267 = 21003401) B21003401
theorem B55978451 : Blo 1455547 55978451 := bstep (se 1 (by rfl) ⟨41983838, by rfl⟩ : syracuseStep 55978451 = 83967677) B83967677
theorem B7376183 : Blo 1455547 7376183 := bstep (se 1 (by rfl) ⟨5532137, by rfl⟩ : syracuseStep 7376183 = 11064275) B11064275
theorem B6565259 : Blo 1455547 6565259 := bstep (se 1 (by rfl) ⟨4923944, by rfl⟩ : syracuseStep 6565259 = 9847889) B9847889
theorem B106245917 : Blo 1455547 106245917 := bstep (se 3 (by rfl) ⟨19921109, by rfl⟩ : syracuseStep 106245917 = 39842219) B39842219
theorem B3109607 : Blo 1455547 3109607 := bstep (se 1 (by rfl) ⟨2332205, by rfl⟩ : syracuseStep 3109607 = 4664411) B4664411
theorem B4912487 : Blo 1455547 4912487 := bstep (se 1 (by rfl) ⟨3684365, by rfl⟩ : syracuseStep 4912487 = 7368731) B7368731
theorem B1456379 : Blo 1455547 1456379 := bstep (se 1 (by rfl) ⟨1092284, by rfl⟩ : syracuseStep 1456379 = 2184569) B2184569
theorem B1456447 : Blo 1455547 1456447 := bstep (se 1 (by rfl) ⟨1092335, by rfl⟩ : syracuseStep 1456447 = 2184671) B2184671
theorem B3275135 : Blo 1455547 3275135 := bstep (se 1 (by rfl) ⟨2456351, by rfl⟩ : syracuseStep 3275135 = 4912703) B4912703
theorem B18922079 : Blo 1455547 18922079 := bstep (se 1 (by rfl) ⟨14191559, by rfl⟩ : syracuseStep 18922079 = 28383119) B28383119
theorem B1456795 : Blo 1455547 1456795 := bstep (se 1 (by rfl) ⟨1092596, by rfl⟩ : syracuseStep 1456795 = 2185193) B2185193
theorem B3685115 : Blo 1455547 3685115 := bstep (se 1 (by rfl) ⟨2763836, by rfl⟩ : syracuseStep 3685115 = 5527673) B5527673
theorem B3939209 : Blo 1455547 3939209 := bstep (se 2 (by rfl) ⟨1477203, by rfl⟩ : syracuseStep 3939209 = 2954407) B2954407
theorem B12787031 : Blo 1455547 12787031 := bstep (se 1 (by rfl) ⟨9590273, by rfl⟩ : syracuseStep 12787031 = 19180547) B19180547
theorem B9330335 : Blo 1455547 9330335 := bstep (se 1 (by rfl) ⟨6997751, by rfl⟩ : syracuseStep 9330335 = 13995503) B13995503
theorem B5529343 : Blo 1455547 5529343 := bstep (se 1 (by rfl) ⟨4147007, by rfl⟩ : syracuseStep 5529343 = 8294015) B8294015
theorem B18669689 : Blo 1455547 18669689 := bstep (se 2 (by rfl) ⟨7001133, by rfl⟩ : syracuseStep 18669689 = 14002267) B14002267
theorem B2457769 : Blo 1455547 2457769 := bstep (se 2 (by rfl) ⟨921663, by rfl⟩ : syracuseStep 2457769 = 1843327) B1843327
theorem B2073071 : Blo 1455547 2073071 := bstep (se 1 (by rfl) ⟨1554803, by rfl⟩ : syracuseStep 2073071 = 3109607) B3109607
theorem B4916159 : Blo 1455547 4916159 := bstep (se 1 (by rfl) ⟨3687119, by rfl⟩ : syracuseStep 4916159 = 7374239) B7374239
theorem B17507357 : Blo 1455547 17507357 := bstep (se 3 (by rfl) ⟨3282629, by rfl⟩ : syracuseStep 17507357 = 6565259) B6565259
theorem B4917455 : Blo 1455547 4917455 := bstep (se 1 (by rfl) ⟨3688091, by rfl⟩ : syracuseStep 4917455 = 7376183) B7376183
theorem B6220223 : Blo 1455547 6220223 := bstep (se 1 (by rfl) ⟨4665167, by rfl⟩ : syracuseStep 6220223 = 9330335) B9330335
theorem B70830611 : Blo 1455547 70830611 := bstep (se 1 (by rfl) ⟨53122958, by rfl⟩ : syracuseStep 70830611 = 106245917) B106245917
theorem B5533019 : Blo 1455547 5533019 := bstep (se 1 (by rfl) ⟨4149764, by rfl⟩ : syracuseStep 5533019 = 8299529) B8299529
theorem B10497691 : Blo 1455547 10497691 := bstep (se 1 (by rfl) ⟨7873268, by rfl⟩ : syracuseStep 10497691 = 15746537) B15746537
theorem B9334511 : Blo 1455547 9334511 := bstep (se 1 (by rfl) ⟨7000883, by rfl⟩ : syracuseStep 9334511 = 14001767) B14001767
theorem B2183423 : Blo 1455547 2183423 := bstep (se 1 (by rfl) ⟨1637567, by rfl⟩ : syracuseStep 2183423 = 3275135) B3275135
theorem B37318967 : Blo 1455547 37318967 := bstep (se 1 (by rfl) ⟨27989225, by rfl⟩ : syracuseStep 37318967 = 55978451) B55978451
theorem B2626139 : Blo 1455547 2626139 := bstep (se 1 (by rfl) ⟨1969604, by rfl⟩ : syracuseStep 2626139 = 3939209) B3939209
theorem B4666025 : Blo 1455547 4666025 := bstep (se 2 (by rfl) ⟨1749759, by rfl⟩ : syracuseStep 4666025 = 3499519) B3499519
theorem B8524687 : Blo 1455547 8524687 := bstep (se 1 (by rfl) ⟨6393515, by rfl⟩ : syracuseStep 8524687 = 12787031) B12787031
theorem B2184863 : Blo 1455547 2184863 := bstep (se 1 (by rfl) ⟨1638647, by rfl⟩ : syracuseStep 2184863 = 3277295) B3277295
theorem B3274991 : Blo 1455547 3274991 := bstep (se 1 (by rfl) ⟨2456243, by rfl⟩ : syracuseStep 3274991 = 4912487) B4912487
theorem B2185727 : Blo 1455547 2185727 := bstep (se 1 (by rfl) ⟨1639295, by rfl⟩ : syracuseStep 2185727 = 3278591) B3278591
theorem B2185895 : Blo 1455547 2185895 := bstep (se 1 (by rfl) ⟨1639421, by rfl⟩ : syracuseStep 2185895 = 3278843) B3278843
theorem B12614719 : Blo 1455547 12614719 := bstep (se 1 (by rfl) ⟨9461039, by rfl⟩ : syracuseStep 12614719 = 18922079) B18922079
theorem B2456743 : Blo 1455547 2456743 := bstep (se 1 (by rfl) ⟨1842557, by rfl⟩ : syracuseStep 2456743 = 3685115) B3685115
theorem B7372457 : Blo 1455547 7372457 := bstep (se 2 (by rfl) ⟨2764671, by rfl⟩ : syracuseStep 7372457 = 5529343) B5529343
theorem B24879311 : Blo 1455547 24879311 := bstep (se 1 (by rfl) ⟨18659483, by rfl⟩ : syracuseStep 24879311 = 37318967) B37318967
theorem B3277025 : Blo 1455547 3277025 := bstep (se 2 (by rfl) ⟨1228884, by rfl⟩ : syracuseStep 3277025 = 2457769) B2457769
theorem B3277439 : Blo 1455547 3277439 := bstep (se 1 (by rfl) ⟨2458079, by rfl⟩ : syracuseStep 3277439 = 4916159) B4916159
theorem B16819625 : Blo 1455547 16819625 := bstep (se 2 (by rfl) ⟨6307359, by rfl⟩ : syracuseStep 16819625 = 12614719) B12614719
theorem B3278303 : Blo 1455547 3278303 := bstep (se 1 (by rfl) ⟨2458727, by rfl⟩ : syracuseStep 3278303 = 4917455) B4917455
theorem B4146815 : Blo 1455547 4146815 := bstep (se 1 (by rfl) ⟨3110111, by rfl⟩ : syracuseStep 4146815 = 6220223) B6220223
theorem B47220407 : Blo 1455547 47220407 := bstep (se 1 (by rfl) ⟨35415305, by rfl⟩ : syracuseStep 47220407 = 70830611) B70830611
theorem B3688679 : Blo 1455547 3688679 := bstep (se 1 (by rfl) ⟨2766509, by rfl⟩ : syracuseStep 3688679 = 5533019) B5533019
theorem B12446459 : Blo 1455547 12446459 := bstep (se 1 (by rfl) ⟨9334844, by rfl⟩ : syracuseStep 12446459 = 18669689) B18669689
theorem B11366249 : Blo 1455547 11366249 := bstep (se 2 (by rfl) ⟨4262343, by rfl⟩ : syracuseStep 11366249 = 8524687) B8524687
theorem B2183327 : Blo 1455547 2183327 := bstep (se 1 (by rfl) ⟨1637495, by rfl⟩ : syracuseStep 2183327 = 3274991) B3274991
theorem B13996921 : Blo 1455547 13996921 := bstep (se 2 (by rfl) ⟨5248845, by rfl⟩ : syracuseStep 13996921 = 10497691) B10497691
theorem B6223007 : Blo 1455547 6223007 := bstep (se 1 (by rfl) ⟨4667255, by rfl⟩ : syracuseStep 6223007 = 9334511) B9334511
theorem B1455615 : Blo 1455547 1455615 := bstep (se 1 (by rfl) ⟨1091711, by rfl⟩ : syracuseStep 1455615 = 2183423) B2183423
theorem B11671571 : Blo 1455547 11671571 := bstep (se 1 (by rfl) ⟨8753678, by rfl⟩ : syracuseStep 11671571 = 17507357) B17507357
theorem B1456575 : Blo 1455547 1456575 := bstep (se 1 (by rfl) ⟨1092431, by rfl⟩ : syracuseStep 1456575 = 2184863) B2184863
theorem B5528189 : Blo 1455547 5528189 := bstep (se 3 (by rfl) ⟨1036535, by rfl⟩ : syracuseStep 5528189 = 2073071) B2073071
theorem B3275657 : Blo 1455547 3275657 := bstep (se 2 (by rfl) ⟨1228371, by rfl⟩ : syracuseStep 3275657 = 2456743) B2456743
theorem B7003037 : Blo 1455547 7003037 := bstep (se 3 (by rfl) ⟨1313069, by rfl⟩ : syracuseStep 7003037 = 2626139) B2626139
theorem B1457151 : Blo 1455547 1457151 := bstep (se 1 (by rfl) ⟨1092863, by rfl⟩ : syracuseStep 1457151 = 2185727) B2185727
theorem B12442733 : Blo 1455547 12442733 := bstep (se 3 (by rfl) ⟨2333012, by rfl⟩ : syracuseStep 12442733 = 4666025) B4666025
theorem B1457263 : Blo 1455547 1457263 := bstep (se 1 (by rfl) ⟨1092947, by rfl⟩ : syracuseStep 1457263 = 2185895) B2185895
theorem B4914971 : Blo 1455547 4914971 := bstep (se 1 (by rfl) ⟨3686228, by rfl⟩ : syracuseStep 4914971 = 7372457) B7372457
theorem B18662561 : Blo 1455547 18662561 := bstep (se 2 (by rfl) ⟨6998460, by rfl⟩ : syracuseStep 18662561 = 13996921) B13996921
theorem B2459119 : Blo 1455547 2459119 := bstep (se 1 (by rfl) ⟨1844339, by rfl⟩ : syracuseStep 2459119 = 3688679) B3688679
theorem B31124189 : Blo 1455547 31124189 := bstep (se 3 (by rfl) ⟨5835785, by rfl⟩ : syracuseStep 31124189 = 11671571) B11671571
theorem B4148671 : Blo 1455547 4148671 := bstep (se 1 (by rfl) ⟨3111503, by rfl⟩ : syracuseStep 4148671 = 6223007) B6223007
theorem B2764543 : Blo 1455547 2764543 := bstep (se 1 (by rfl) ⟨2073407, by rfl⟩ : syracuseStep 2764543 = 4146815) B4146815
theorem B2183771 : Blo 1455547 2183771 := bstep (se 1 (by rfl) ⟨1637828, by rfl⟩ : syracuseStep 2183771 = 3275657) B3275657
theorem B8295155 : Blo 1455547 8295155 := bstep (se 1 (by rfl) ⟨6221366, by rfl⟩ : syracuseStep 8295155 = 12442733) B12442733
theorem B1455551 : Blo 1455547 1455551 := bstep (se 1 (by rfl) ⟨1091663, by rfl⟩ : syracuseStep 1455551 = 2183327) B2183327
theorem B16586207 : Blo 1455547 16586207 := bstep (se 1 (by rfl) ⟨12439655, by rfl⟩ : syracuseStep 16586207 = 24879311) B24879311
theorem B2184683 : Blo 1455547 2184683 := bstep (se 1 (by rfl) ⟨1638512, by rfl⟩ : syracuseStep 2184683 = 3277025) B3277025
theorem B2184959 : Blo 1455547 2184959 := bstep (se 1 (by rfl) ⟨1638719, by rfl⟩ : syracuseStep 2184959 = 3277439) B3277439
theorem B11213083 : Blo 1455547 11213083 := bstep (se 1 (by rfl) ⟨8409812, by rfl⟩ : syracuseStep 11213083 = 16819625) B16819625
theorem B2185535 : Blo 1455547 2185535 := bstep (se 1 (by rfl) ⟨1639151, by rfl⟩ : syracuseStep 2185535 = 3278303) B3278303
theorem B31480271 : Blo 1455547 31480271 := bstep (se 1 (by rfl) ⟨23610203, by rfl⟩ : syracuseStep 31480271 = 47220407) B47220407
theorem B3685459 : Blo 1455547 3685459 := bstep (se 1 (by rfl) ⟨2764094, by rfl⟩ : syracuseStep 3685459 = 5528189) B5528189
theorem B8297639 : Blo 1455547 8297639 := bstep (se 1 (by rfl) ⟨6223229, by rfl⟩ : syracuseStep 8297639 = 12446459) B12446459
theorem B4668691 : Blo 1455547 4668691 := bstep (se 1 (by rfl) ⟨3501518, by rfl⟩ : syracuseStep 4668691 = 7003037) B7003037
theorem B30309997 : Blo 1455547 30309997 := bstep (se 3 (by rfl) ⟨5683124, by rfl⟩ : syracuseStep 30309997 = 11366249) B11366249
theorem B3276647 : Blo 1455547 3276647 := bstep (se 1 (by rfl) ⟨2457485, by rfl⟩ : syracuseStep 3276647 = 4914971) B4914971
theorem B14950777 : Blo 1455547 14950777 := bstep (se 2 (by rfl) ⟨5606541, by rfl⟩ : syracuseStep 14950777 = 11213083) B11213083
theorem B5530103 : Blo 1455547 5530103 := bstep (se 1 (by rfl) ⟨4147577, by rfl⟩ : syracuseStep 5530103 = 8295155) B8295155
theorem B5531561 : Blo 1455547 5531561 := bstep (se 2 (by rfl) ⟨2074335, by rfl⟩ : syracuseStep 5531561 = 4148671) B4148671
theorem B3278825 : Blo 1455547 3278825 := bstep (se 2 (by rfl) ⟨1229559, by rfl⟩ : syracuseStep 3278825 = 2459119) B2459119
theorem B5531759 : Blo 1455547 5531759 := bstep (se 1 (by rfl) ⟨4148819, by rfl⟩ : syracuseStep 5531759 = 8297639) B8297639
theorem B40413329 : Blo 1455547 40413329 := bstep (se 2 (by rfl) ⟨15154998, by rfl⟩ : syracuseStep 40413329 = 30309997) B30309997
theorem B2184431 : Blo 1455547 2184431 := bstep (se 1 (by rfl) ⟨1638323, by rfl⟩ : syracuseStep 2184431 = 3276647) B3276647
theorem B1455847 : Blo 1455547 1455847 := bstep (se 1 (by rfl) ⟨1091885, by rfl⟩ : syracuseStep 1455847 = 2183771) B2183771
theorem B12441707 : Blo 1455547 12441707 := bstep (se 1 (by rfl) ⟨9331280, by rfl⟩ : syracuseStep 12441707 = 18662561) B18662561
theorem B11057471 : Blo 1455547 11057471 := bstep (se 1 (by rfl) ⟨8293103, by rfl⟩ : syracuseStep 11057471 = 16586207) B16586207
theorem B1456455 : Blo 1455547 1456455 := bstep (se 1 (by rfl) ⟨1092341, by rfl⟩ : syracuseStep 1456455 = 2184683) B2184683
theorem B1456639 : Blo 1455547 1456639 := bstep (se 1 (by rfl) ⟨1092479, by rfl⟩ : syracuseStep 1456639 = 2184959) B2184959
theorem B4913945 : Blo 1455547 4913945 := bstep (se 2 (by rfl) ⟨1842729, by rfl⟩ : syracuseStep 4913945 = 3685459) B3685459
theorem B1457023 : Blo 1455547 1457023 := bstep (se 1 (by rfl) ⟨1092767, by rfl⟩ : syracuseStep 1457023 = 2185535) B2185535
theorem B20986847 : Blo 1455547 20986847 := bstep (se 1 (by rfl) ⟨15740135, by rfl⟩ : syracuseStep 20986847 = 31480271) B31480271
theorem B6224921 : Blo 1455547 6224921 := bstep (se 2 (by rfl) ⟨2334345, by rfl⟩ : syracuseStep 6224921 = 4668691) B4668691
theorem B20749459 : Blo 1455547 20749459 := bstep (se 1 (by rfl) ⟨15562094, by rfl⟩ : syracuseStep 20749459 = 31124189) B31124189
theorem B3686057 : Blo 1455547 3686057 := bstep (se 2 (by rfl) ⟨1382271, by rfl⟩ : syracuseStep 3686057 = 2764543) B2764543
theorem B3686735 : Blo 1455547 3686735 := bstep (se 1 (by rfl) ⟨2765051, by rfl⟩ : syracuseStep 3686735 = 5530103) B5530103
theorem B3687707 : Blo 1455547 3687707 := bstep (se 1 (by rfl) ⟨2765780, by rfl⟩ : syracuseStep 3687707 = 5531561) B5531561
theorem B3687839 : Blo 1455547 3687839 := bstep (se 1 (by rfl) ⟨2765879, by rfl⟩ : syracuseStep 3687839 = 5531759) B5531759
theorem B27665945 : Blo 1455547 27665945 := bstep (se 2 (by rfl) ⟨10374729, by rfl⟩ : syracuseStep 27665945 = 20749459) B20749459
theorem B19934369 : Blo 1455547 19934369 := bstep (se 2 (by rfl) ⟨7475388, by rfl⟩ : syracuseStep 19934369 = 14950777) B14950777
theorem B8294471 : Blo 1455547 8294471 := bstep (se 1 (by rfl) ⟨6220853, by rfl⟩ : syracuseStep 8294471 = 12441707) B12441707
theorem B4149947 : Blo 1455547 4149947 := bstep (se 1 (by rfl) ⟨3112460, by rfl⟩ : syracuseStep 4149947 = 6224921) B6224921
theorem B1456287 : Blo 1455547 1456287 := bstep (se 1 (by rfl) ⟨1092215, by rfl⟩ : syracuseStep 1456287 = 2184431) B2184431
theorem B2185883 : Blo 1455547 2185883 := bstep (se 1 (by rfl) ⟨1639412, by rfl⟩ : syracuseStep 2185883 = 3278825) B3278825
theorem B26942219 : Blo 1455547 26942219 := bstep (se 1 (by rfl) ⟨20206664, by rfl⟩ : syracuseStep 26942219 = 40413329) B40413329
theorem B7371647 : Blo 1455547 7371647 := bstep (se 1 (by rfl) ⟨5528735, by rfl⟩ : syracuseStep 7371647 = 11057471) B11057471
theorem B3275963 : Blo 1455547 3275963 := bstep (se 1 (by rfl) ⟨2456972, by rfl⟩ : syracuseStep 3275963 = 4913945) B4913945
theorem B13991231 : Blo 1455547 13991231 := bstep (se 1 (by rfl) ⟨10493423, by rfl⟩ : syracuseStep 13991231 = 20986847) B20986847
theorem B2457371 : Blo 1455547 2457371 := bstep (se 1 (by rfl) ⟨1843028, by rfl⟩ : syracuseStep 2457371 = 3686057) B3686057
theorem B5529647 : Blo 1455547 5529647 := bstep (se 1 (by rfl) ⟨4147235, by rfl⟩ : syracuseStep 5529647 = 8294471) B8294471
theorem B2457823 : Blo 1455547 2457823 := bstep (se 1 (by rfl) ⟨1843367, by rfl⟩ : syracuseStep 2457823 = 3686735) B3686735
theorem B2458471 : Blo 1455547 2458471 := bstep (se 1 (by rfl) ⟨1843853, by rfl⟩ : syracuseStep 2458471 = 3687707) B3687707
theorem B2458559 : Blo 1455547 2458559 := bstep (se 1 (by rfl) ⟨1843919, by rfl⟩ : syracuseStep 2458559 = 3687839) B3687839
theorem B13289579 : Blo 1455547 13289579 := bstep (se 1 (by rfl) ⟨9967184, by rfl⟩ : syracuseStep 13289579 = 19934369) B19934369
theorem B18443963 : Blo 1455547 18443963 := bstep (se 1 (by rfl) ⟨13832972, by rfl⟩ : syracuseStep 18443963 = 27665945) B27665945
theorem B17961479 : Blo 1455547 17961479 := bstep (se 1 (by rfl) ⟨13471109, by rfl⟩ : syracuseStep 17961479 = 26942219) B26942219
theorem B2183975 : Blo 1455547 2183975 := bstep (se 1 (by rfl) ⟨1637981, by rfl⟩ : syracuseStep 2183975 = 3275963) B3275963
theorem B9327487 : Blo 1455547 9327487 := bstep (se 1 (by rfl) ⟨6995615, by rfl⟩ : syracuseStep 9327487 = 13991231) B13991231
theorem B2766631 : Blo 1455547 2766631 := bstep (se 1 (by rfl) ⟨2074973, by rfl⟩ : syracuseStep 2766631 = 4149947) B4149947
theorem B1457255 : Blo 1455547 1457255 := bstep (se 1 (by rfl) ⟨1092941, by rfl⟩ : syracuseStep 1457255 = 2185883) B2185883
theorem B4914431 : Blo 1455547 4914431 := bstep (se 1 (by rfl) ⟨3685823, by rfl⟩ : syracuseStep 4914431 = 7371647) B7371647
theorem B1638247 : Blo 1455547 1638247 := bstep (se 1 (by rfl) ⟨1228685, by rfl⟩ : syracuseStep 1638247 = 2457371) B2457371
theorem B3686431 : Blo 1455547 3686431 := bstep (se 1 (by rfl) ⟨2764823, by rfl⟩ : syracuseStep 3686431 = 5529647) B5529647
theorem B3277097 : Blo 1455547 3277097 := bstep (se 2 (by rfl) ⟨1228911, by rfl⟩ : syracuseStep 3277097 = 2457823) B2457823
theorem B1639039 : Blo 1455547 1639039 := bstep (se 1 (by rfl) ⟨1229279, by rfl⟩ : syracuseStep 1639039 = 2458559) B2458559
theorem B3277961 : Blo 1455547 3277961 := bstep (se 2 (by rfl) ⟨1229235, by rfl⟩ : syracuseStep 3277961 = 2458471) B2458471
theorem B12436649 : Blo 1455547 12436649 := bstep (se 2 (by rfl) ⟨4663743, by rfl⟩ : syracuseStep 12436649 = 9327487) B9327487
theorem B3688841 : Blo 1455547 3688841 := bstep (se 2 (by rfl) ⟨1383315, by rfl⟩ : syracuseStep 3688841 = 2766631) B2766631
theorem B8859719 : Blo 1455547 8859719 := bstep (se 1 (by rfl) ⟨6644789, by rfl⟩ : syracuseStep 8859719 = 13289579) B13289579
theorem B2184329 : Blo 1455547 2184329 := bstep (se 2 (by rfl) ⟨819123, by rfl⟩ : syracuseStep 2184329 = 1638247) B1638247
theorem B11974319 : Blo 1455547 11974319 := bstep (se 1 (by rfl) ⟨8980739, by rfl⟩ : syracuseStep 11974319 = 17961479) B17961479
theorem B1455983 : Blo 1455547 1455983 := bstep (se 1 (by rfl) ⟨1091987, by rfl⟩ : syracuseStep 1455983 = 2183975) B2183975
theorem B3276287 : Blo 1455547 3276287 := bstep (se 1 (by rfl) ⟨2457215, by rfl⟩ : syracuseStep 3276287 = 4914431) B4914431
theorem B12295975 : Blo 1455547 12295975 := bstep (se 1 (by rfl) ⟨9221981, by rfl⟩ : syracuseStep 12295975 = 18443963) B18443963
theorem B4915241 : Blo 1455547 4915241 := bstep (se 2 (by rfl) ⟨1843215, by rfl⟩ : syracuseStep 4915241 = 3686431) B3686431
theorem B5906479 : Blo 1455547 5906479 := bstep (se 1 (by rfl) ⟨4429859, by rfl⟩ : syracuseStep 5906479 = 8859719) B8859719
theorem B8291099 : Blo 1455547 8291099 := bstep (se 1 (by rfl) ⟨6218324, by rfl⟩ : syracuseStep 8291099 = 12436649) B12436649
theorem B2459227 : Blo 1455547 2459227 := bstep (se 1 (by rfl) ⟨1844420, by rfl⟩ : syracuseStep 2459227 = 3688841) B3688841
theorem B16394633 : Blo 1455547 16394633 := bstep (se 2 (by rfl) ⟨6147987, by rfl⟩ : syracuseStep 16394633 = 12295975) B12295975
theorem B7982879 : Blo 1455547 7982879 := bstep (se 1 (by rfl) ⟨5987159, by rfl⟩ : syracuseStep 7982879 = 11974319) B11974319
theorem B2184191 : Blo 1455547 2184191 := bstep (se 1 (by rfl) ⟨1638143, by rfl⟩ : syracuseStep 2184191 = 3276287) B3276287
theorem B2184731 : Blo 1455547 2184731 := bstep (se 1 (by rfl) ⟨1638548, by rfl⟩ : syracuseStep 2184731 = 3277097) B3277097
theorem B1456219 : Blo 1455547 1456219 := bstep (se 1 (by rfl) ⟨1092164, by rfl⟩ : syracuseStep 1456219 = 2184329) B2184329
theorem B2185307 : Blo 1455547 2185307 := bstep (se 1 (by rfl) ⟨1638980, by rfl⟩ : syracuseStep 2185307 = 3277961) B3277961
theorem B2185385 : Blo 1455547 2185385 := bstep (se 2 (by rfl) ⟨819519, by rfl⟩ : syracuseStep 2185385 = 1639039) B1639039
theorem B3276827 : Blo 1455547 3276827 := bstep (se 1 (by rfl) ⟨2457620, by rfl⟩ : syracuseStep 3276827 = 4915241) B4915241
theorem B10929755 : Blo 1455547 10929755 := bstep (se 1 (by rfl) ⟨8197316, by rfl⟩ : syracuseStep 10929755 = 16394633) B16394633
theorem B3278969 : Blo 1455547 3278969 := bstep (se 2 (by rfl) ⟨1229613, by rfl⟩ : syracuseStep 3278969 = 2459227) B2459227
theorem B7875305 : Blo 1455547 7875305 := bstep (se 2 (by rfl) ⟨2953239, by rfl⟩ : syracuseStep 7875305 = 5906479) B5906479
theorem B85150709 : Blo 1455547 85150709 := bstep (se 5 (by rfl) ⟨3991439, by rfl⟩ : syracuseStep 85150709 = 7982879) B7982879
theorem B5527399 : Blo 1455547 5527399 := bstep (se 1 (by rfl) ⟨4145549, by rfl⟩ : syracuseStep 5527399 = 8291099) B8291099
theorem B1456127 : Blo 1455547 1456127 := bstep (se 1 (by rfl) ⟨1092095, by rfl⟩ : syracuseStep 1456127 = 2184191) B2184191
theorem B1456487 : Blo 1455547 1456487 := bstep (se 1 (by rfl) ⟨1092365, by rfl⟩ : syracuseStep 1456487 = 2184731) B2184731
theorem B1456871 : Blo 1455547 1456871 := bstep (se 1 (by rfl) ⟨1092653, by rfl⟩ : syracuseStep 1456871 = 2185307) B2185307
theorem B1456923 : Blo 1455547 1456923 := bstep (se 1 (by rfl) ⟨1092692, by rfl⟩ : syracuseStep 1456923 = 2185385) B2185385
theorem B56767139 : Blo 1455547 56767139 := bstep (se 1 (by rfl) ⟨42575354, by rfl⟩ : syracuseStep 56767139 = 85150709) B85150709
theorem B7369865 : Blo 1455547 7369865 := bstep (se 2 (by rfl) ⟨2763699, by rfl⟩ : syracuseStep 7369865 = 5527399) B5527399
theorem B2184551 : Blo 1455547 2184551 := bstep (se 1 (by rfl) ⟨1638413, by rfl⟩ : syracuseStep 2184551 = 3276827) B3276827
theorem B2185979 : Blo 1455547 2185979 := bstep (se 1 (by rfl) ⟨1639484, by rfl⟩ : syracuseStep 2185979 = 3278969) B3278969
theorem B29146013 : Blo 1455547 29146013 := bstep (se 3 (by rfl) ⟨5464877, by rfl⟩ : syracuseStep 29146013 = 10929755) B10929755
theorem B5250203 : Blo 1455547 5250203 := bstep (se 1 (by rfl) ⟨3937652, by rfl⟩ : syracuseStep 5250203 = 7875305) B7875305
theorem B3500135 : Blo 1455547 3500135 := bstep (se 1 (by rfl) ⟨2625101, by rfl⟩ : syracuseStep 3500135 = 5250203) B5250203
theorem B37844759 : Blo 1455547 37844759 := bstep (se 1 (by rfl) ⟨28383569, by rfl⟩ : syracuseStep 37844759 = 56767139) B56767139
theorem B4913243 : Blo 1455547 4913243 := bstep (se 1 (by rfl) ⟨3684932, by rfl⟩ : syracuseStep 4913243 = 7369865) B7369865
theorem B1456367 : Blo 1455547 1456367 := bstep (se 1 (by rfl) ⟨1092275, by rfl⟩ : syracuseStep 1456367 = 2184551) B2184551
theorem B1457319 : Blo 1455547 1457319 := bstep (se 1 (by rfl) ⟨1092989, by rfl⟩ : syracuseStep 1457319 = 2185979) B2185979
theorem B19430675 : Blo 1455547 19430675 := bstep (se 1 (by rfl) ⟨14573006, by rfl⟩ : syracuseStep 19430675 = 29146013) B29146013
theorem B100919357 : Blo 1455547 100919357 := bstep (se 3 (by rfl) ⟨18922379, by rfl⟩ : syracuseStep 100919357 = 37844759) B37844759
theorem B12953783 : Blo 1455547 12953783 := bstep (se 1 (by rfl) ⟨9715337, by rfl⟩ : syracuseStep 12953783 = 19430675) B19430675
theorem B3275495 : Blo 1455547 3275495 := bstep (se 1 (by rfl) ⟨2456621, by rfl⟩ : syracuseStep 3275495 = 4913243) B4913243
theorem B2333423 : Blo 1455547 2333423 := bstep (se 1 (by rfl) ⟨1750067, by rfl⟩ : syracuseStep 2333423 = 3500135) B3500135
theorem B8635855 : Blo 1455547 8635855 := bstep (se 1 (by rfl) ⟨6476891, by rfl⟩ : syracuseStep 8635855 = 12953783) B12953783
theorem B2183663 : Blo 1455547 2183663 := bstep (se 1 (by rfl) ⟨1637747, by rfl⟩ : syracuseStep 2183663 = 3275495) B3275495
theorem B67279571 : Blo 1455547 67279571 := bstep (se 1 (by rfl) ⟨50459678, by rfl⟩ : syracuseStep 67279571 = 100919357) B100919357
theorem B1555615 : Blo 1455547 1555615 := bstep (se 1 (by rfl) ⟨1166711, by rfl⟩ : syracuseStep 1555615 = 2333423) B2333423
theorem B44853047 : Blo 1455547 44853047 := bstep (se 1 (by rfl) ⟨33639785, by rfl⟩ : syracuseStep 44853047 = 67279571) B67279571
theorem B11514473 : Blo 1455547 11514473 := bstep (se 2 (by rfl) ⟨4317927, by rfl⟩ : syracuseStep 11514473 = 8635855) B8635855
theorem B1455775 : Blo 1455547 1455775 := bstep (se 1 (by rfl) ⟨1091831, by rfl⟩ : syracuseStep 1455775 = 2183663) B2183663
theorem B8296613 : Blo 1455547 8296613 := bstep (se 4 (by rfl) ⟨777807, by rfl⟩ : syracuseStep 8296613 = 1555615) B1555615
theorem B7676315 : Blo 1455547 7676315 := bstep (se 1 (by rfl) ⟨5757236, by rfl⟩ : syracuseStep 7676315 = 11514473) B11514473
theorem B29902031 : Blo 1455547 29902031 := bstep (se 1 (by rfl) ⟨22426523, by rfl⟩ : syracuseStep 29902031 = 44853047) B44853047
theorem B5531075 : Blo 1455547 5531075 := bstep (se 1 (by rfl) ⟨4148306, by rfl⟩ : syracuseStep 5531075 = 8296613) B8296613
theorem B3687383 : Blo 1455547 3687383 := bstep (se 1 (by rfl) ⟨2765537, by rfl⟩ : syracuseStep 3687383 = 5531075) B5531075
theorem B19934687 : Blo 1455547 19934687 := bstep (se 1 (by rfl) ⟨14951015, by rfl⟩ : syracuseStep 19934687 = 29902031) B29902031
theorem B5117543 : Blo 1455547 5117543 := bstep (se 1 (by rfl) ⟨3838157, by rfl⟩ : syracuseStep 5117543 = 7676315) B7676315
theorem B2458255 : Blo 1455547 2458255 := bstep (se 1 (by rfl) ⟨1843691, by rfl⟩ : syracuseStep 2458255 = 3687383) B3687383
theorem B13289791 : Blo 1455547 13289791 := bstep (se 1 (by rfl) ⟨9967343, by rfl⟩ : syracuseStep 13289791 = 19934687) B19934687
theorem B3411695 : Blo 1455547 3411695 := bstep (se 1 (by rfl) ⟨2558771, by rfl⟩ : syracuseStep 3411695 = 5117543) B5117543
theorem B17719721 : Blo 1455547 17719721 := bstep (se 2 (by rfl) ⟨6644895, by rfl⟩ : syracuseStep 17719721 = 13289791) B13289791
theorem B3277673 : Blo 1455547 3277673 := bstep (se 2 (by rfl) ⟨1229127, by rfl⟩ : syracuseStep 3277673 = 2458255) B2458255
theorem B2274463 : Blo 1455547 2274463 := bstep (se 1 (by rfl) ⟨1705847, by rfl⟩ : syracuseStep 2274463 = 3411695) B3411695
theorem B11813147 : Blo 1455547 11813147 := bstep (se 1 (by rfl) ⟨8859860, by rfl⟩ : syracuseStep 11813147 = 17719721) B17719721
theorem B2185115 : Blo 1455547 2185115 := bstep (se 1 (by rfl) ⟨1638836, by rfl⟩ : syracuseStep 2185115 = 3277673) B3277673
theorem B12130469 : Blo 1455547 12130469 := bstep (se 4 (by rfl) ⟨1137231, by rfl⟩ : syracuseStep 12130469 = 2274463) B2274463
theorem B8086979 : Blo 1455547 8086979 := bstep (se 1 (by rfl) ⟨6065234, by rfl⟩ : syracuseStep 8086979 = 12130469) B12130469
theorem B7875431 : Blo 1455547 7875431 := bstep (se 1 (by rfl) ⟨5906573, by rfl⟩ : syracuseStep 7875431 = 11813147) B11813147
theorem B1456743 : Blo 1455547 1456743 := bstep (se 1 (by rfl) ⟨1092557, by rfl⟩ : syracuseStep 1456743 = 2185115) B2185115
theorem B21565277 : Blo 1455547 21565277 := bstep (se 3 (by rfl) ⟨4043489, by rfl⟩ : syracuseStep 21565277 = 8086979) B8086979
theorem B5250287 : Blo 1455547 5250287 := bstep (se 1 (by rfl) ⟨3937715, by rfl⟩ : syracuseStep 5250287 = 7875431) B7875431
theorem B3500191 : Blo 1455547 3500191 := bstep (se 1 (by rfl) ⟨2625143, by rfl⟩ : syracuseStep 3500191 = 5250287) B5250287
theorem B14376851 : Blo 1455547 14376851 := bstep (se 1 (by rfl) ⟨10782638, by rfl⟩ : syracuseStep 14376851 = 21565277) B21565277
theorem B18667685 : Blo 1455547 18667685 := bstep (se 4 (by rfl) ⟨1750095, by rfl⟩ : syracuseStep 18667685 = 3500191) B3500191
theorem B9584567 : Blo 1455547 9584567 := bstep (se 1 (by rfl) ⟨7188425, by rfl⟩ : syracuseStep 9584567 = 14376851) B14376851
theorem B12445123 : Blo 1455547 12445123 := bstep (se 1 (by rfl) ⟨9333842, by rfl⟩ : syracuseStep 12445123 = 18667685) B18667685
theorem B6389711 : Blo 1455547 6389711 := bstep (se 1 (by rfl) ⟨4792283, by rfl⟩ : syracuseStep 6389711 = 9584567) B9584567
theorem B16593497 : Blo 1455547 16593497 := bstep (se 2 (by rfl) ⟨6222561, by rfl⟩ : syracuseStep 16593497 = 12445123) B12445123
theorem B4259807 : Blo 1455547 4259807 := bstep (se 1 (by rfl) ⟨3194855, by rfl⟩ : syracuseStep 4259807 = 6389711) B6389711
theorem B11062331 : Blo 1455547 11062331 := bstep (se 1 (by rfl) ⟨8296748, by rfl⟩ : syracuseStep 11062331 = 16593497) B16593497
theorem B2839871 : Blo 1455547 2839871 := bstep (se 1 (by rfl) ⟨2129903, by rfl⟩ : syracuseStep 2839871 = 4259807) B4259807
theorem B7374887 : Blo 1455547 7374887 := bstep (se 1 (by rfl) ⟨5531165, by rfl⟩ : syracuseStep 7374887 = 11062331) B11062331
theorem B7572989 : Blo 1455547 7572989 := bstep (se 3 (by rfl) ⟨1419935, by rfl⟩ : syracuseStep 7572989 = 2839871) B2839871
theorem B4916591 : Blo 1455547 4916591 := bstep (se 1 (by rfl) ⟨3687443, by rfl⟩ : syracuseStep 4916591 = 7374887) B7374887
theorem B5048659 : Blo 1455547 5048659 := bstep (se 1 (by rfl) ⟨3786494, by rfl⟩ : syracuseStep 5048659 = 7572989) B7572989
theorem B3277727 : Blo 1455547 3277727 := bstep (se 1 (by rfl) ⟨2458295, by rfl⟩ : syracuseStep 3277727 = 4916591) B4916591
theorem B6731545 : Blo 1455547 6731545 := bstep (se 2 (by rfl) ⟨2524329, by rfl⟩ : syracuseStep 6731545 = 5048659) B5048659
theorem B8975393 : Blo 1455547 8975393 := bstep (se 2 (by rfl) ⟨3365772, by rfl⟩ : syracuseStep 8975393 = 6731545) B6731545
theorem B2185151 : Blo 1455547 2185151 := bstep (se 1 (by rfl) ⟨1638863, by rfl⟩ : syracuseStep 2185151 = 3277727) B3277727
theorem B5983595 : Blo 1455547 5983595 := bstep (se 1 (by rfl) ⟨4487696, by rfl⟩ : syracuseStep 5983595 = 8975393) B8975393
theorem B1456767 : Blo 1455547 1456767 := bstep (se 1 (by rfl) ⟨1092575, by rfl⟩ : syracuseStep 1456767 = 2185151) B2185151
theorem B3989063 : Blo 1455547 3989063 := bstep (se 1 (by rfl) ⟨2991797, by rfl⟩ : syracuseStep 3989063 = 5983595) B5983595
theorem B2659375 : Blo 1455547 2659375 := bstep (se 1 (by rfl) ⟨1994531, by rfl⟩ : syracuseStep 2659375 = 3989063) B3989063
theorem B14183333 : Blo 1455547 14183333 := bstep (se 4 (by rfl) ⟨1329687, by rfl⟩ : syracuseStep 14183333 = 2659375) B2659375
theorem B9455555 : Blo 1455547 9455555 := bstep (se 1 (by rfl) ⟨7091666, by rfl⟩ : syracuseStep 9455555 = 14183333) B14183333
theorem B6303703 : Blo 1455547 6303703 := bstep (se 1 (by rfl) ⟨4727777, by rfl⟩ : syracuseStep 6303703 = 9455555) B9455555
theorem B8404937 : Blo 1455547 8404937 := bstep (se 2 (by rfl) ⟨3151851, by rfl⟩ : syracuseStep 8404937 = 6303703) B6303703
theorem B5603291 : Blo 1455547 5603291 := bstep (se 1 (by rfl) ⟨4202468, by rfl⟩ : syracuseStep 5603291 = 8404937) B8404937
theorem B3735527 : Blo 1455547 3735527 := bstep (se 1 (by rfl) ⟨2801645, by rfl⟩ : syracuseStep 3735527 = 5603291) B5603291
theorem B39845621 : Blo 1455547 39845621 := bstep (se 5 (by rfl) ⟨1867763, by rfl⟩ : syracuseStep 39845621 = 3735527) B3735527
theorem B26563747 : Blo 1455547 26563747 := bstep (se 1 (by rfl) ⟨19922810, by rfl⟩ : syracuseStep 26563747 = 39845621) B39845621
theorem B35418329 : Blo 1455547 35418329 := bstep (se 2 (by rfl) ⟨13281873, by rfl⟩ : syracuseStep 35418329 = 26563747) B26563747
theorem B23612219 : Blo 1455547 23612219 := bstep (se 1 (by rfl) ⟨17709164, by rfl⟩ : syracuseStep 23612219 = 35418329) B35418329
theorem B15741479 : Blo 1455547 15741479 := bstep (se 1 (by rfl) ⟨11806109, by rfl⟩ : syracuseStep 15741479 = 23612219) B23612219
theorem B41977277 : Blo 1455547 41977277 := bstep (se 3 (by rfl) ⟨7870739, by rfl⟩ : syracuseStep 41977277 = 15741479) B15741479
theorem B27984851 : Blo 1455547 27984851 := bstep (se 1 (by rfl) ⟨20988638, by rfl⟩ : syracuseStep 27984851 = 41977277) B41977277
theorem B18656567 : Blo 1455547 18656567 := bstep (se 1 (by rfl) ⟨13992425, by rfl⟩ : syracuseStep 18656567 = 27984851) B27984851
theorem B12437711 : Blo 1455547 12437711 := bstep (se 1 (by rfl) ⟨9328283, by rfl⟩ : syracuseStep 12437711 = 18656567) B18656567
theorem B8291807 : Blo 1455547 8291807 := bstep (se 1 (by rfl) ⟨6218855, by rfl⟩ : syracuseStep 8291807 = 12437711) B12437711
theorem B5527871 : Blo 1455547 5527871 := bstep (se 1 (by rfl) ⟨4145903, by rfl⟩ : syracuseStep 5527871 = 8291807) B8291807
theorem B3685247 : Blo 1455547 3685247 := bstep (se 1 (by rfl) ⟨2763935, by rfl⟩ : syracuseStep 3685247 = 5527871) B5527871
theorem B2456831 : Blo 1455547 2456831 := bstep (se 1 (by rfl) ⟨1842623, by rfl⟩ : syracuseStep 2456831 = 3685247) B3685247
theorem B1637887 : Blo 1455547 1637887 := bstep (se 1 (by rfl) ⟨1228415, by rfl⟩ : syracuseStep 1637887 = 2456831) B2456831
theorem B2183849 : Blo 1455547 2183849 := bstep (se 2 (by rfl) ⟨818943, by rfl⟩ : syracuseStep 2183849 = 1637887) B1637887
theorem B1455899 : Blo 1455547 1455899 := bstep (se 1 (by rfl) ⟨1091924, by rfl⟩ : syracuseStep 1455899 = 2183849) B2183849

theorem C0 (j : ℕ) (h1 : 363886 ≤ j) (h2 : j ≤ 364386) : Blo 1455547 (4 * j + 3) := by
  interval_cases j
  · exact B1455547
  · exact B1455551
  · exact B1455555
  · exact B1455559
  · exact B1455563
  · exact B1455567
  · exact B1455571
  · exact B1455575
  · exact B1455579
  · exact B1455583
  · exact B1455587
  · exact B1455591
  · exact B1455595
  · exact B1455599
  · exact B1455603
  · exact B1455607
  · exact B1455611
  · exact B1455615
  · exact B1455619
  · exact B1455623
  · exact B1455627
  · exact B1455631
  · exact B1455635
  · exact B1455639
  · exact B1455643
  · exact B1455647
  · exact B1455651
  · exact B1455655
  · exact B1455659
  · exact B1455663
  · exact B1455667
  · exact B1455671
  · exact B1455675
  · exact B1455679
  · exact B1455683
  · exact B1455687
  · exact B1455691
  · exact B1455695
  · exact B1455699
  · exact B1455703
  · exact B1455707
  · exact B1455711
  · exact B1455715
  · exact B1455719
  · exact B1455723
  · exact B1455727
  · exact B1455731
  · exact B1455735
  · exact B1455739
  · exact B1455743
  · exact B1455747
  · exact B1455751
  · exact B1455755
  · exact B1455759
  · exact B1455763
  · exact B1455767
  · exact B1455771
  · exact B1455775
  · exact B1455779
  · exact B1455783
  · exact B1455787
  · exact B1455791
  · exact B1455795
  · exact B1455799
  · exact B1455803
  · exact B1455807
  · exact B1455811
  · exact B1455815
  · exact B1455819
  · exact B1455823
  · exact B1455827
  · exact B1455831
  · exact B1455835
  · exact B1455839
  · exact B1455843
  · exact B1455847
  · exact B1455851
  · exact B1455855
  · exact B1455859
  · exact B1455863
  · exact B1455867
  · exact B1455871
  · exact B1455875
  · exact B1455879
  · exact B1455883
  · exact B1455887
  · exact B1455891
  · exact B1455895
  · exact B1455899
  · exact B1455903
  · exact B1455907
  · exact B1455911
  · exact B1455915
  · exact B1455919
  · exact B1455923
  · exact B1455927
  · exact B1455931
  · exact B1455935
  · exact B1455939
  · exact B1455943
  · exact B1455947
  · exact B1455951
  · exact B1455955
  · exact B1455959
  · exact B1455963
  · exact B1455967
  · exact B1455971
  · exact B1455975
  · exact B1455979
  · exact B1455983
  · exact B1455987
  · exact B1455991
  · exact B1455995
  · exact B1455999
  · exact B1456003
  · exact B1456007
  · exact B1456011
  · exact B1456015
  · exact B1456019
  · exact B1456023
  · exact B1456027
  · exact B1456031
  · exact B1456035
  · exact B1456039
  · exact B1456043
  · exact B1456047
  · exact B1456051
  · exact B1456055
  · exact B1456059
  · exact B1456063
  · exact B1456067
  · exact B1456071
  · exact B1456075
  · exact B1456079
  · exact B1456083
  · exact B1456087
  · exact B1456091
  · exact B1456095
  · exact B1456099
  · exact B1456103
  · exact B1456107
  · exact B1456111
  · exact B1456115
  · exact B1456119
  · exact B1456123
  · exact B1456127
  · exact B1456131
  · exact B1456135
  · exact B1456139
  · exact B1456143
  · exact B1456147
  · exact B1456151
  · exact B1456155
  · exact B1456159
  · exact B1456163
  · exact B1456167
  · exact B1456171
  · exact B1456175
  · exact B1456179
  · exact B1456183
  · exact B1456187
  · exact B1456191
  · exact B1456195
  · exact B1456199
  · exact B1456203
  · exact B1456207
  · exact B1456211
  · exact B1456215
  · exact B1456219
  · exact B1456223
  · exact B1456227
  · exact B1456231
  · exact B1456235
  · exact B1456239
  · exact B1456243
  · exact B1456247
  · exact B1456251
  · exact B1456255
  · exact B1456259
  · exact B1456263
  · exact B1456267
  · exact B1456271
  · exact B1456275
  · exact B1456279
  · exact B1456283
  · exact B1456287
  · exact B1456291
  · exact B1456295
  · exact B1456299
  · exact B1456303
  · exact B1456307
  · exact B1456311
  · exact B1456315
  · exact B1456319
  · exact B1456323
  · exact B1456327
  · exact B1456331
  · exact B1456335
  · exact B1456339
  · exact B1456343
  · exact B1456347
  · exact B1456351
  · exact B1456355
  · exact B1456359
  · exact B1456363
  · exact B1456367
  · exact B1456371
  · exact B1456375
  · exact B1456379
  · exact B1456383
  · exact B1456387
  · exact B1456391
  · exact B1456395
  · exact B1456399
  · exact B1456403
  · exact B1456407
  · exact B1456411
  · exact B1456415
  · exact B1456419
  · exact B1456423
  · exact B1456427
  · exact B1456431
  · exact B1456435
  · exact B1456439
  · exact B1456443
  · exact B1456447
  · exact B1456451
  · exact B1456455
  · exact B1456459
  · exact B1456463
  · exact B1456467
  · exact B1456471
  · exact B1456475
  · exact B1456479
  · exact B1456483
  · exact B1456487
  · exact B1456491
  · exact B1456495
  · exact B1456499
  · exact B1456503
  · exact B1456507
  · exact B1456511
  · exact B1456515
  · exact B1456519
  · exact B1456523
  · exact B1456527
  · exact B1456531
  · exact B1456535
  · exact B1456539
  · exact B1456543
  · exact B1456547
  · exact B1456551
  · exact B1456555
  · exact B1456559
  · exact B1456563
  · exact B1456567
  · exact B1456571
  · exact B1456575
  · exact B1456579
  · exact B1456583
  · exact B1456587
  · exact B1456591
  · exact B1456595
  · exact B1456599
  · exact B1456603
  · exact B1456607
  · exact B1456611
  · exact B1456615
  · exact B1456619
  · exact B1456623
  · exact B1456627
  · exact B1456631
  · exact B1456635
  · exact B1456639
  · exact B1456643
  · exact B1456647
  · exact B1456651
  · exact B1456655
  · exact B1456659
  · exact B1456663
  · exact B1456667
  · exact B1456671
  · exact B1456675
  · exact B1456679
  · exact B1456683
  · exact B1456687
  · exact B1456691
  · exact B1456695
  · exact B1456699
  · exact B1456703
  · exact B1456707
  · exact B1456711
  · exact B1456715
  · exact B1456719
  · exact B1456723
  · exact B1456727
  · exact B1456731
  · exact B1456735
  · exact B1456739
  · exact B1456743
  · exact B1456747
  · exact B1456751
  · exact B1456755
  · exact B1456759
  · exact B1456763
  · exact B1456767
  · exact B1456771
  · exact B1456775
  · exact B1456779
  · exact B1456783
  · exact B1456787
  · exact B1456791
  · exact B1456795
  · exact B1456799
  · exact B1456803
  · exact B1456807
  · exact B1456811
  · exact B1456815
  · exact B1456819
  · exact B1456823
  · exact B1456827
  · exact B1456831
  · exact B1456835
  · exact B1456839
  · exact B1456843
  · exact B1456847
  · exact B1456851
  · exact B1456855
  · exact B1456859
  · exact B1456863
  · exact B1456867
  · exact B1456871
  · exact B1456875
  · exact B1456879
  · exact B1456883
  · exact B1456887
  · exact B1456891
  · exact B1456895
  · exact B1456899
  · exact B1456903
  · exact B1456907
  · exact B1456911
  · exact B1456915
  · exact B1456919
  · exact B1456923
  · exact B1456927
  · exact B1456931
  · exact B1456935
  · exact B1456939
  · exact B1456943
  · exact B1456947
  · exact B1456951
  · exact B1456955
  · exact B1456959
  · exact B1456963
  · exact B1456967
  · exact B1456971
  · exact B1456975
  · exact B1456979
  · exact B1456983
  · exact B1456987
  · exact B1456991
  · exact B1456995
  · exact B1456999
  · exact B1457003
  · exact B1457007
  · exact B1457011
  · exact B1457015
  · exact B1457019
  · exact B1457023
  · exact B1457027
  · exact B1457031
  · exact B1457035
  · exact B1457039
  · exact B1457043
  · exact B1457047
  · exact B1457051
  · exact B1457055
  · exact B1457059
  · exact B1457063
  · exact B1457067
  · exact B1457071
  · exact B1457075
  · exact B1457079
  · exact B1457083
  · exact B1457087
  · exact B1457091
  · exact B1457095
  · exact B1457099
  · exact B1457103
  · exact B1457107
  · exact B1457111
  · exact B1457115
  · exact B1457119
  · exact B1457123
  · exact B1457127
  · exact B1457131
  · exact B1457135
  · exact B1457139
  · exact B1457143
  · exact B1457147
  · exact B1457151
  · exact B1457155
  · exact B1457159
  · exact B1457163
  · exact B1457167
  · exact B1457171
  · exact B1457175
  · exact B1457179
  · exact B1457183
  · exact B1457187
  · exact B1457191
  · exact B1457195
  · exact B1457199
  · exact B1457203
  · exact B1457207
  · exact B1457211
  · exact B1457215
  · exact B1457219
  · exact B1457223
  · exact B1457227
  · exact B1457231
  · exact B1457235
  · exact B1457239
  · exact B1457243
  · exact B1457247
  · exact B1457251
  · exact B1457255
  · exact B1457259
  · exact B1457263
  · exact B1457267
  · exact B1457271
  · exact B1457275
  · exact B1457279
  · exact B1457283
  · exact B1457287
  · exact B1457291
  · exact B1457295
  · exact B1457299
  · exact B1457303
  · exact B1457307
  · exact B1457311
  · exact B1457315
  · exact B1457319
  · exact B1457323
  · exact B1457327
  · exact B1457331
  · exact B1457335
  · exact B1457339
  · exact B1457343
  · exact B1457347
  · exact B1457351
  · exact B1457355
  · exact B1457359
  · exact B1457363
  · exact B1457367
  · exact B1457371
  · exact B1457375
  · exact B1457379
  · exact B1457383
  · exact B1457387
  · exact B1457391
  · exact B1457395
  · exact B1457399
  · exact B1457403
  · exact B1457407
  · exact B1457411
  · exact B1457415
  · exact B1457419
  · exact B1457423
  · exact B1457427
  · exact B1457431
  · exact B1457435
  · exact B1457439
  · exact B1457443
  · exact B1457447
  · exact B1457451
  · exact B1457455
  · exact B1457459
  · exact B1457463
  · exact B1457467
  · exact B1457471
  · exact B1457475
  · exact B1457479
  · exact B1457483
  · exact B1457487
  · exact B1457491
  · exact B1457495
  · exact B1457499
  · exact B1457503
  · exact B1457507
  · exact B1457511
  · exact B1457515
  · exact B1457519
  · exact B1457523
  · exact B1457527
  · exact B1457531
  · exact B1457535
  · exact B1457539
  · exact B1457543
  · exact B1457547

theorem solution (m : ℕ) (hlo : 1455547 ≤ m) (hhi : m ≤ 1457547) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 363886 ≤ j := by omega
    have hj2 : j ≤ 364386 := by omega
    have hb : Blo 1455547 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
