-- Prove2me | solution 1 for syracuse_descends_range_191804_195804
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:50.650393+00:00
-- url     : https://prove2.me/submissions/cc7b59aa-742e-4c63-a5ca-5aa8e10ea96a

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


theorem B327685 : Blo 191804 327685 := bbase (se 4 (by rfl) ⟨30720, by rfl⟩ : syracuseStep 327685 = 61441) (by norm_num)
theorem B655397 : Blo 191804 655397 := bbase (se 4 (by rfl) ⟨61443, by rfl⟩ : syracuseStep 655397 = 122887) (by norm_num)
theorem B557093 : Blo 191804 557093 := bbase (se 4 (by rfl) ⟨52227, by rfl⟩ : syracuseStep 557093 = 104455) (by norm_num)
theorem B327773 : Blo 191804 327773 := bbase (se 3 (by rfl) ⟨61457, by rfl⟩ : syracuseStep 327773 = 122915) (by norm_num)
theorem B491629 : Blo 191804 491629 := bbase (se 3 (by rfl) ⟨92180, by rfl⟩ : syracuseStep 491629 = 184361) (by norm_num)
theorem B262261 : Blo 191804 262261 := bbase (se 5 (by rfl) ⟨12293, by rfl⟩ : syracuseStep 262261 = 24587) (by norm_num)
theorem B295093 : Blo 191804 295093 := bbase (se 5 (by rfl) ⟨13832, by rfl⟩ : syracuseStep 295093 = 27665) (by norm_num)
theorem B491741 : Blo 191804 491741 := bbase (se 3 (by rfl) ⟨92201, by rfl⟩ : syracuseStep 491741 = 184403) (by norm_num)
theorem B327901 : Blo 191804 327901 := bbase (se 3 (by rfl) ⟨61481, by rfl⟩ : syracuseStep 327901 = 122963) (by norm_num)
theorem B622885 : Blo 191804 622885 := bbase (se 4 (by rfl) ⟨58395, by rfl⟩ : syracuseStep 622885 = 116791) (by norm_num)
theorem B327989 : Blo 191804 327989 := bbase (se 5 (by rfl) ⟨15374, by rfl⟩ : syracuseStep 327989 = 30749) (by norm_num)
theorem B491933 : Blo 191804 491933 := bbase (se 3 (by rfl) ⟨92237, by rfl⟩ : syracuseStep 491933 = 184475) (by norm_num)
theorem B328117 : Blo 191804 328117 := bbase (se 5 (by rfl) ⟨15380, by rfl⟩ : syracuseStep 328117 = 30761) (by norm_num)
theorem B655829 : Blo 191804 655829 := bbase (se 7 (by rfl) ⟨7685, by rfl⟩ : syracuseStep 655829 = 15371) (by norm_num)
theorem B262645 : Blo 191804 262645 := bbase (se 5 (by rfl) ⟨12311, by rfl⟩ : syracuseStep 262645 = 24623) (by norm_num)
theorem B328205 : Blo 191804 328205 := bbase (se 3 (by rfl) ⟨61538, by rfl⟩ : syracuseStep 328205 = 123077) (by norm_num)
theorem B328333 : Blo 191804 328333 := bbase (se 3 (by rfl) ⟨61562, by rfl⟩ : syracuseStep 328333 = 123125) (by norm_num)
theorem B623285 : Blo 191804 623285 := bbase (se 5 (by rfl) ⟨29216, by rfl⟩ : syracuseStep 623285 = 58433) (by norm_num)
theorem B6292181 : Blo 191804 6292181 := bbase (se 7 (by rfl) ⟨73736, by rfl⟩ : syracuseStep 6292181 = 147473) (by norm_num)
theorem B328421 : Blo 191804 328421 := bbase (se 4 (by rfl) ⟨30789, by rfl⟩ : syracuseStep 328421 = 61579) (by norm_num)
theorem B492277 : Blo 191804 492277 := bbase (se 5 (by rfl) ⟨23075, by rfl⟩ : syracuseStep 492277 = 46151) (by norm_num)
theorem B819989 : Blo 191804 819989 := bbase (se 6 (by rfl) ⟨19218, by rfl⟩ : syracuseStep 819989 = 38437) (by norm_num)
theorem B492389 : Blo 191804 492389 := bbase (se 4 (by rfl) ⟨46161, by rfl⟩ : syracuseStep 492389 = 92323) (by norm_num)
theorem B328549 : Blo 191804 328549 := bbase (se 4 (by rfl) ⟨30801, by rfl⟩ : syracuseStep 328549 = 61603) (by norm_num)
theorem B656261 : Blo 191804 656261 := bbase (se 4 (by rfl) ⟨61524, by rfl⟩ : syracuseStep 656261 = 123049) (by norm_num)
theorem B328637 : Blo 191804 328637 := bbase (se 3 (by rfl) ⟨61619, by rfl⟩ : syracuseStep 328637 = 123239) (by norm_num)
theorem B492581 : Blo 191804 492581 := bbase (se 4 (by rfl) ⟨46179, by rfl⟩ : syracuseStep 492581 = 92359) (by norm_num)
theorem B394301 : Blo 191804 394301 := bbase (se 3 (by rfl) ⟨73931, by rfl⟩ : syracuseStep 394301 = 147863) (by norm_num)
theorem B328765 : Blo 191804 328765 := bbase (se 3 (by rfl) ⟨61643, by rfl⟩ : syracuseStep 328765 = 123287) (by norm_num)
theorem B984149 : Blo 191804 984149 := bbase (se 8 (by rfl) ⟨5766, by rfl⟩ : syracuseStep 984149 = 11533) (by norm_num)
theorem B230545 : Blo 191804 230545 := bbase (se 2 (by rfl) ⟨86454, by rfl⟩ : syracuseStep 230545 = 172909) (by norm_num)
theorem B328853 : Blo 191804 328853 := bbase (se 6 (by rfl) ⟨7707, by rfl⟩ : syracuseStep 328853 = 15415) (by norm_num)
theorem B3736853 : Blo 191804 3736853 := bbase (se 6 (by rfl) ⟨87582, by rfl⟩ : syracuseStep 3736853 = 175165) (by norm_num)
theorem B328981 : Blo 191804 328981 := bbase (se 6 (by rfl) ⟨7710, by rfl⟩ : syracuseStep 328981 = 15421) (by norm_num)
theorem B918821 : Blo 191804 918821 := bbase (se 4 (by rfl) ⟨86139, by rfl⟩ : syracuseStep 918821 = 172279) (by norm_num)
theorem B656693 : Blo 191804 656693 := bbase (se 5 (by rfl) ⟨30782, by rfl⟩ : syracuseStep 656693 = 61565) (by norm_num)
theorem B886085 : Blo 191804 886085 := bbase (se 4 (by rfl) ⟨83070, by rfl⟩ : syracuseStep 886085 = 166141) (by norm_num)
theorem B329069 : Blo 191804 329069 := bbase (se 3 (by rfl) ⟨61700, by rfl⟩ : syracuseStep 329069 = 123401) (by norm_num)
theorem B296309 : Blo 191804 296309 := bbase (se 5 (by rfl) ⟨13889, by rfl⟩ : syracuseStep 296309 = 27779) (by norm_num)
theorem B492925 : Blo 191804 492925 := bbase (se 3 (by rfl) ⟨92423, by rfl⟩ : syracuseStep 492925 = 184847) (by norm_num)
theorem B493037 : Blo 191804 493037 := bbase (se 3 (by rfl) ⟨92444, by rfl⟩ : syracuseStep 493037 = 184889) (by norm_num)
theorem B329197 : Blo 191804 329197 := bbase (se 3 (by rfl) ⟨61724, by rfl⟩ : syracuseStep 329197 = 123449) (by norm_num)
theorem B394813 : Blo 191804 394813 := bbase (se 3 (by rfl) ⟨74027, by rfl⟩ : syracuseStep 394813 = 148055) (by norm_num)
theorem B329285 : Blo 191804 329285 := bbase (se 4 (by rfl) ⟨30870, by rfl⟩ : syracuseStep 329285 = 61741) (by norm_num)
theorem B394885 : Blo 191804 394885 := bbase (se 4 (by rfl) ⟨37020, by rfl⟩ : syracuseStep 394885 = 74041) (by norm_num)
theorem B493229 : Blo 191804 493229 := bbase (se 3 (by rfl) ⟨92480, by rfl⟩ : syracuseStep 493229 = 184961) (by norm_num)
theorem B394949 : Blo 191804 394949 := bbase (se 4 (by rfl) ⟨37026, by rfl⟩ : syracuseStep 394949 = 74053) (by norm_num)
theorem B329413 : Blo 191804 329413 := bbase (se 4 (by rfl) ⟨30882, by rfl⟩ : syracuseStep 329413 = 61765) (by norm_num)
theorem B2197205 : Blo 191804 2197205 := bbase (se 7 (by rfl) ⟨25748, by rfl⟩ : syracuseStep 2197205 = 51497) (by norm_num)
theorem B657125 : Blo 191804 657125 := bbase (se 4 (by rfl) ⟨61605, by rfl⟩ : syracuseStep 657125 = 123211) (by norm_num)
theorem B329501 : Blo 191804 329501 := bbase (se 3 (by rfl) ⟨61781, by rfl⟩ : syracuseStep 329501 = 123563) (by norm_num)
theorem B395077 : Blo 191804 395077 := bbase (se 4 (by rfl) ⟨37038, by rfl⟩ : syracuseStep 395077 = 74077) (by norm_num)
theorem B264029 : Blo 191804 264029 := bbase (se 3 (by rfl) ⟨49505, by rfl⟩ : syracuseStep 264029 = 99011) (by norm_num)
theorem B427933 : Blo 191804 427933 := bbase (se 3 (by rfl) ⟨80237, by rfl⟩ : syracuseStep 427933 = 160475) (by norm_num)
theorem B329629 : Blo 191804 329629 := bbase (se 3 (by rfl) ⟨61805, by rfl⟩ : syracuseStep 329629 = 123611) (by norm_num)
theorem B296893 : Blo 191804 296893 := bbase (se 3 (by rfl) ⟨55667, by rfl⟩ : syracuseStep 296893 = 111335) (by norm_num)
theorem B329717 : Blo 191804 329717 := bbase (se 5 (by rfl) ⟨15455, by rfl⟩ : syracuseStep 329717 = 30911) (by norm_num)
theorem B493573 : Blo 191804 493573 := bbase (se 4 (by rfl) ⟨46272, by rfl⟩ : syracuseStep 493573 = 92545) (by norm_num)
theorem B395293 : Blo 191804 395293 := bbase (se 3 (by rfl) ⟨74117, by rfl⟩ : syracuseStep 395293 = 148235) (by norm_num)
theorem B1476725 : Blo 191804 1476725 := bbase (se 5 (by rfl) ⟨69221, by rfl⟩ : syracuseStep 1476725 = 138443) (by norm_num)
theorem B493685 : Blo 191804 493685 := bbase (se 5 (by rfl) ⟨23141, by rfl⟩ : syracuseStep 493685 = 46283) (by norm_num)
theorem B231545 : Blo 191804 231545 := bbase (se 2 (by rfl) ⟨86829, by rfl⟩ : syracuseStep 231545 = 173659) (by norm_num)
theorem B329845 : Blo 191804 329845 := bbase (se 5 (by rfl) ⟨15461, by rfl⟩ : syracuseStep 329845 = 30923) (by norm_num)
theorem B657557 : Blo 191804 657557 := bbase (se 6 (by rfl) ⟨15411, by rfl⟩ : syracuseStep 657557 = 30823) (by norm_num)
theorem B231617 : Blo 191804 231617 := bbase (se 2 (by rfl) ⟨86856, by rfl⟩ : syracuseStep 231617 = 173713) (by norm_num)
theorem B329933 : Blo 191804 329933 := bbase (se 3 (by rfl) ⟨61862, by rfl⟩ : syracuseStep 329933 = 123725) (by norm_num)
theorem B1575125 : Blo 191804 1575125 := bbase (se 7 (by rfl) ⟨18458, by rfl⟩ : syracuseStep 1575125 = 36917) (by norm_num)
theorem B493877 : Blo 191804 493877 := bbase (se 5 (by rfl) ⟨23150, by rfl⟩ : syracuseStep 493877 = 46301) (by norm_num)
theorem B330061 : Blo 191804 330061 := bbase (se 3 (by rfl) ⟨61886, by rfl⟩ : syracuseStep 330061 = 123773) (by norm_num)
theorem B985445 : Blo 191804 985445 := bbase (se 4 (by rfl) ⟨92385, by rfl⟩ : syracuseStep 985445 = 184771) (by norm_num)
theorem B330149 : Blo 191804 330149 := bbase (se 4 (by rfl) ⟨30951, by rfl⟩ : syracuseStep 330149 = 61903) (by norm_num)
theorem B1247669 : Blo 191804 1247669 := bbase (se 5 (by rfl) ⟨58484, by rfl⟩ : syracuseStep 1247669 = 116969) (by norm_num)
theorem B330173 : Blo 191804 330173 := bbase (se 3 (by rfl) ⟨61907, by rfl⟩ : syracuseStep 330173 = 123815) (by norm_num)
theorem B231925 : Blo 191804 231925 := bbase (se 5 (by rfl) ⟨10871, by rfl⟩ : syracuseStep 231925 = 21743) (by norm_num)
theorem B821765 : Blo 191804 821765 := bbase (se 4 (by rfl) ⟨77040, by rfl⟩ : syracuseStep 821765 = 154081) (by norm_num)
theorem B330277 : Blo 191804 330277 := bbase (se 4 (by rfl) ⟨30963, by rfl⟩ : syracuseStep 330277 = 61927) (by norm_num)
theorem B657989 : Blo 191804 657989 := bbase (se 4 (by rfl) ⟨61686, by rfl⟩ : syracuseStep 657989 = 123373) (by norm_num)
theorem B461389 : Blo 191804 461389 := bbase (se 3 (by rfl) ⟨86510, by rfl⟩ : syracuseStep 461389 = 173021) (by norm_num)
theorem B658037 : Blo 191804 658037 := bbase (se 5 (by rfl) ⟨30845, by rfl⟩ : syracuseStep 658037 = 61691) (by norm_num)
theorem B330365 : Blo 191804 330365 := bbase (se 3 (by rfl) ⟨61943, by rfl⟩ : syracuseStep 330365 = 123887) (by norm_num)
theorem B494221 : Blo 191804 494221 := bbase (se 3 (by rfl) ⟨92666, by rfl⟩ : syracuseStep 494221 = 185333) (by norm_num)
theorem B232093 : Blo 191804 232093 := bbase (se 3 (by rfl) ⟨43517, by rfl⟩ : syracuseStep 232093 = 87035) (by norm_num)
theorem B232141 : Blo 191804 232141 := bbase (se 3 (by rfl) ⟨43526, by rfl⟩ : syracuseStep 232141 = 87053) (by norm_num)
theorem B494333 : Blo 191804 494333 := bbase (se 3 (by rfl) ⟨92687, by rfl⟩ : syracuseStep 494333 = 185375) (by norm_num)
theorem B232237 : Blo 191804 232237 := bbase (se 3 (by rfl) ⟨43544, by rfl⟩ : syracuseStep 232237 = 87089) (by norm_num)
theorem B494525 : Blo 191804 494525 := bbase (se 3 (by rfl) ⟨92723, by rfl⟩ : syracuseStep 494525 = 185447) (by norm_num)
theorem B658421 : Blo 191804 658421 := bbase (se 5 (by rfl) ⟨30863, by rfl⟩ : syracuseStep 658421 = 61727) (by norm_num)
theorem B527573 : Blo 191804 527573 := bbase (se 7 (by rfl) ⟨6182, by rfl⟩ : syracuseStep 527573 = 12365) (by norm_num)
theorem B494869 : Blo 191804 494869 := bbase (se 6 (by rfl) ⟨11598, by rfl⟩ : syracuseStep 494869 = 23197) (by norm_num)
theorem B232813 : Blo 191804 232813 := bbase (se 3 (by rfl) ⟨43652, by rfl⟩ : syracuseStep 232813 = 87305) (by norm_num)
theorem B494981 : Blo 191804 494981 := bbase (se 4 (by rfl) ⟨46404, by rfl⟩ : syracuseStep 494981 = 92809) (by norm_num)
theorem B658853 : Blo 191804 658853 := bbase (se 4 (by rfl) ⟨61767, by rfl⟩ : syracuseStep 658853 = 123535) (by norm_num)
theorem B396733 : Blo 191804 396733 := bbase (se 3 (by rfl) ⟨74387, by rfl⟩ : syracuseStep 396733 = 148775) (by norm_num)
theorem B822757 : Blo 191804 822757 := bbase (se 4 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 822757 = 154267) (by norm_num)
theorem B462341 : Blo 191804 462341 := bbase (se 4 (by rfl) ⟨43344, by rfl⟩ : syracuseStep 462341 = 86689) (by norm_num)
theorem B1248821 : Blo 191804 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B462397 : Blo 191804 462397 := bbase (se 3 (by rfl) ⟨86699, by rfl⟩ : syracuseStep 462397 = 173399) (by norm_num)
theorem B495173 : Blo 191804 495173 := bbase (se 4 (by rfl) ⟨46422, by rfl⟩ : syracuseStep 495173 = 92845) (by norm_num)
theorem B986741 : Blo 191804 986741 := bbase (se 5 (by rfl) ⟨46253, by rfl⟩ : syracuseStep 986741 = 92507) (by norm_num)
theorem B364189 : Blo 191804 364189 := bbase (se 3 (by rfl) ⟨68285, by rfl⟩ : syracuseStep 364189 = 136571) (by norm_num)
theorem B659141 : Blo 191804 659141 := bbase (se 4 (by rfl) ⟨61794, by rfl⟩ : syracuseStep 659141 = 123589) (by norm_num)
theorem B364333 : Blo 191804 364333 := bbase (se 3 (by rfl) ⟨68312, by rfl⟩ : syracuseStep 364333 = 136625) (by norm_num)
theorem B659285 : Blo 191804 659285 := bbase (se 9 (by rfl) ⟨1931, by rfl⟩ : syracuseStep 659285 = 3863) (by norm_num)
theorem B397181 : Blo 191804 397181 := bbase (se 3 (by rfl) ⟨74471, by rfl⟩ : syracuseStep 397181 = 148943) (by norm_num)
theorem B495517 : Blo 191804 495517 := bbase (se 3 (by rfl) ⟨92909, by rfl⟩ : syracuseStep 495517 = 185819) (by norm_num)
theorem B462773 : Blo 191804 462773 := bbase (se 5 (by rfl) ⟨21692, by rfl⟩ : syracuseStep 462773 = 43385) (by norm_num)
theorem B364493 : Blo 191804 364493 := bbase (se 3 (by rfl) ⟨68342, by rfl⟩ : syracuseStep 364493 = 136685) (by norm_num)
theorem B495629 : Blo 191804 495629 := bbase (se 3 (by rfl) ⟨92930, by rfl⟩ : syracuseStep 495629 = 185861) (by norm_num)
theorem B987157 : Blo 191804 987157 := bbase (se 6 (by rfl) ⟨23136, by rfl⟩ : syracuseStep 987157 = 46273) (by norm_num)
theorem B495661 : Blo 191804 495661 := bbase (se 3 (by rfl) ⟨92936, by rfl⟩ : syracuseStep 495661 = 185873) (by norm_num)
theorem B200761 : Blo 191804 200761 := bbase (se 2 (by rfl) ⟨75285, by rfl⟩ : syracuseStep 200761 = 150571) (by norm_num)
theorem B364637 : Blo 191804 364637 := bbase (se 3 (by rfl) ⟨68369, by rfl⟩ : syracuseStep 364637 = 136739) (by norm_num)
theorem B888965 : Blo 191804 888965 := bbase (se 4 (by rfl) ⟨83340, by rfl⟩ : syracuseStep 888965 = 166681) (by norm_num)
theorem B463013 : Blo 191804 463013 := bbase (se 4 (by rfl) ⟨43407, by rfl⟩ : syracuseStep 463013 = 86815) (by norm_num)
theorem B659717 : Blo 191804 659717 := bbase (se 4 (by rfl) ⟨61848, by rfl⟩ : syracuseStep 659717 = 123697) (by norm_num)
theorem B233813 : Blo 191804 233813 := bbase (se 10 (by rfl) ⟨342, by rfl⟩ : syracuseStep 233813 = 685) (by norm_num)
theorem B364925 : Blo 191804 364925 := bbase (se 3 (by rfl) ⟨68423, by rfl⟩ : syracuseStep 364925 = 136847) (by norm_num)
theorem B233861 : Blo 191804 233861 := bbase (se 4 (by rfl) ⟨21924, by rfl⟩ : syracuseStep 233861 = 43849) (by norm_num)
theorem B627077 : Blo 191804 627077 := bbase (se 4 (by rfl) ⟨58788, by rfl⟩ : syracuseStep 627077 = 117577) (by norm_num)
theorem B1053109 : Blo 191804 1053109 := bbase (se 5 (by rfl) ⟨49364, by rfl⟩ : syracuseStep 1053109 = 98729) (by norm_num)
theorem B365077 : Blo 191804 365077 := bbase (se 6 (by rfl) ⟨8556, by rfl⟩ : syracuseStep 365077 = 17113) (by norm_num)
theorem B660149 : Blo 191804 660149 := bbase (se 5 (by rfl) ⟨30944, by rfl⟩ : syracuseStep 660149 = 61889) (by norm_num)
theorem B365381 : Blo 191804 365381 := bbase (se 4 (by rfl) ⟨34254, by rfl⟩ : syracuseStep 365381 = 68509) (by norm_num)
theorem B496493 : Blo 191804 496493 := bbase (se 3 (by rfl) ⟨93092, by rfl⟩ : syracuseStep 496493 = 186185) (by norm_num)
theorem B398189 : Blo 191804 398189 := bbase (se 3 (by rfl) ⟨74660, by rfl⟩ : syracuseStep 398189 = 149321) (by norm_num)
theorem B988037 : Blo 191804 988037 := bbase (se 4 (by rfl) ⟨92628, by rfl⟩ : syracuseStep 988037 = 185257) (by norm_num)
theorem B234409 : Blo 191804 234409 := bbase (se 2 (by rfl) ⟨87903, by rfl⟩ : syracuseStep 234409 = 175807) (by norm_num)
theorem B922565 : Blo 191804 922565 := bbase (se 4 (by rfl) ⟨86490, by rfl⟩ : syracuseStep 922565 = 172981) (by norm_num)
theorem B3052565 : Blo 191804 3052565 := bbase (se 6 (by rfl) ⟨71544, by rfl⟩ : syracuseStep 3052565 = 143089) (by norm_num)
theorem B660581 : Blo 191804 660581 := bbase (se 4 (by rfl) ⟨61929, by rfl⟩ : syracuseStep 660581 = 123859) (by norm_num)
theorem B988469 : Blo 191804 988469 := bbase (se 5 (by rfl) ⟨46334, by rfl⟩ : syracuseStep 988469 = 92669) (by norm_num)
theorem B333157 : Blo 191804 333157 := bbase (se 4 (by rfl) ⟨31233, by rfl⟩ : syracuseStep 333157 = 62467) (by norm_num)
theorem B791909 : Blo 191804 791909 := bbase (se 4 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 791909 = 148483) (by norm_num)
theorem B234889 : Blo 191804 234889 := bbase (se 2 (by rfl) ⟨88083, by rfl⟩ : syracuseStep 234889 = 176167) (by norm_num)
theorem B2004437 : Blo 191804 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B431621 : Blo 191804 431621 := bbase (se 4 (by rfl) ⟨40464, by rfl⟩ : syracuseStep 431621 = 80929) (by norm_num)
theorem B366133 : Blo 191804 366133 := bbase (se 5 (by rfl) ⟨17162, by rfl⟩ : syracuseStep 366133 = 34325) (by norm_num)
theorem B431693 : Blo 191804 431693 := bbase (se 3 (by rfl) ⟨80942, by rfl⟩ : syracuseStep 431693 = 161885) (by norm_num)
theorem B988757 : Blo 191804 988757 := bbase (se 8 (by rfl) ⟨5793, by rfl⟩ : syracuseStep 988757 = 11587) (by norm_num)
theorem B431765 : Blo 191804 431765 := bbase (se 6 (by rfl) ⟨10119, by rfl⟩ : syracuseStep 431765 = 20239) (by norm_num)
theorem B1316533 : Blo 191804 1316533 := bbase (se 5 (by rfl) ⟨61712, by rfl⟩ : syracuseStep 1316533 = 123425) (by norm_num)
theorem B366277 : Blo 191804 366277 := bbase (se 4 (by rfl) ⟨34338, by rfl⟩ : syracuseStep 366277 = 68677) (by norm_num)
theorem B431837 : Blo 191804 431837 := bbase (se 3 (by rfl) ⟨80969, by rfl⟩ : syracuseStep 431837 = 161939) (by norm_num)
theorem B431909 : Blo 191804 431909 := bbase (se 4 (by rfl) ⟨40491, by rfl⟩ : syracuseStep 431909 = 80983) (by norm_num)
theorem B366437 : Blo 191804 366437 := bbase (se 4 (by rfl) ⟨34353, by rfl⟩ : syracuseStep 366437 = 68707) (by norm_num)
theorem B431981 : Blo 191804 431981 := bbase (se 3 (by rfl) ⟨80996, by rfl⟩ : syracuseStep 431981 = 161993) (by norm_num)
theorem B432053 : Blo 191804 432053 := bbase (se 5 (by rfl) ⟨20252, by rfl⟩ : syracuseStep 432053 = 40505) (by norm_num)
theorem B366581 : Blo 191804 366581 := bbase (se 5 (by rfl) ⟨17183, by rfl⟩ : syracuseStep 366581 = 34367) (by norm_num)
theorem B432125 : Blo 191804 432125 := bbase (se 3 (by rfl) ⟨81023, by rfl⟩ : syracuseStep 432125 = 162047) (by norm_num)
theorem B432197 : Blo 191804 432197 := bbase (se 4 (by rfl) ⟨40518, by rfl⟩ : syracuseStep 432197 = 81037) (by norm_num)
theorem B432269 : Blo 191804 432269 := bbase (se 3 (by rfl) ⟨81050, by rfl⟩ : syracuseStep 432269 = 162101) (by norm_num)
theorem B989333 : Blo 191804 989333 := bbase (se 6 (by rfl) ⟨23187, by rfl⟩ : syracuseStep 989333 = 46375) (by norm_num)
theorem B432341 : Blo 191804 432341 := bbase (se 7 (by rfl) ⟨5066, by rfl⟩ : syracuseStep 432341 = 10133) (by norm_num)
theorem B366869 : Blo 191804 366869 := bbase (se 6 (by rfl) ⟨8598, by rfl⟩ : syracuseStep 366869 = 17197) (by norm_num)
theorem B432413 : Blo 191804 432413 := bbase (se 3 (by rfl) ⟨81077, by rfl⟩ : syracuseStep 432413 = 162155) (by norm_num)
theorem B432485 : Blo 191804 432485 := bbase (se 4 (by rfl) ⟨40545, by rfl⟩ : syracuseStep 432485 = 81091) (by norm_num)
theorem B432557 : Blo 191804 432557 := bbase (se 3 (by rfl) ⟨81104, by rfl⟩ : syracuseStep 432557 = 162209) (by norm_num)
theorem B367021 : Blo 191804 367021 := bbase (se 3 (by rfl) ⟨68816, by rfl⟩ : syracuseStep 367021 = 137633) (by norm_num)
theorem B432629 : Blo 191804 432629 := bbase (se 5 (by rfl) ⟨20279, by rfl⟩ : syracuseStep 432629 = 40559) (by norm_num)
theorem B432701 : Blo 191804 432701 := bbase (se 3 (by rfl) ⟨81131, by rfl⟩ : syracuseStep 432701 = 162263) (by norm_num)
theorem B432773 : Blo 191804 432773 := bbase (se 4 (by rfl) ⟨40572, by rfl⟩ : syracuseStep 432773 = 81145) (by norm_num)
theorem B432845 : Blo 191804 432845 := bbase (se 3 (by rfl) ⟨81158, by rfl⟩ : syracuseStep 432845 = 162317) (by norm_num)
theorem B3185365 : Blo 191804 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B367325 : Blo 191804 367325 := bbase (se 3 (by rfl) ⟨68873, by rfl⟩ : syracuseStep 367325 = 137747) (by norm_num)
theorem B432917 : Blo 191804 432917 := bbase (se 6 (by rfl) ⟨10146, by rfl⟩ : syracuseStep 432917 = 20293) (by norm_num)
theorem B432989 : Blo 191804 432989 := bbase (se 3 (by rfl) ⟨81185, by rfl⟩ : syracuseStep 432989 = 162371) (by norm_num)
theorem B433061 : Blo 191804 433061 := bbase (se 4 (by rfl) ⟨40599, by rfl⟩ : syracuseStep 433061 = 81199) (by norm_num)
theorem B433133 : Blo 191804 433133 := bbase (se 3 (by rfl) ⟨81212, by rfl⟩ : syracuseStep 433133 = 162425) (by norm_num)
theorem B433205 : Blo 191804 433205 := bbase (se 5 (by rfl) ⟨20306, by rfl⟩ : syracuseStep 433205 = 40613) (by norm_num)
theorem B1481813 : Blo 191804 1481813 := bbase (se 8 (by rfl) ⟨8682, by rfl⟩ : syracuseStep 1481813 = 17365) (by norm_num)
theorem B433277 : Blo 191804 433277 := bbase (se 3 (by rfl) ⟨81239, by rfl⟩ : syracuseStep 433277 = 162479) (by norm_num)
theorem B1645717 : Blo 191804 1645717 := bbase (se 6 (by rfl) ⟨38571, by rfl⟩ : syracuseStep 1645717 = 77143) (by norm_num)
theorem B433349 : Blo 191804 433349 := bbase (se 4 (by rfl) ⟨40626, by rfl⟩ : syracuseStep 433349 = 81253) (by norm_num)
theorem B466165 : Blo 191804 466165 := bbase (se 5 (by rfl) ⟨21851, by rfl⟩ : syracuseStep 466165 = 43703) (by norm_num)
theorem B695557 : Blo 191804 695557 := bbase (se 4 (by rfl) ⟨65208, by rfl⟩ : syracuseStep 695557 = 130417) (by norm_num)
theorem B433421 : Blo 191804 433421 := bbase (se 3 (by rfl) ⟨81266, by rfl⟩ : syracuseStep 433421 = 162533) (by norm_num)
theorem B433493 : Blo 191804 433493 := bbase (se 11 (by rfl) ⟨317, by rfl⟩ : syracuseStep 433493 = 635) (by norm_num)
theorem B728453 : Blo 191804 728453 := bbase (se 4 (by rfl) ⟨68292, by rfl⟩ : syracuseStep 728453 = 136585) (by norm_num)
theorem B433565 : Blo 191804 433565 := bbase (se 3 (by rfl) ⟨81293, by rfl⟩ : syracuseStep 433565 = 162587) (by norm_num)
theorem B990629 : Blo 191804 990629 := bbase (se 4 (by rfl) ⟨92871, by rfl⟩ : syracuseStep 990629 = 185743) (by norm_num)
theorem B368077 : Blo 191804 368077 := bbase (se 3 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 368077 = 138029) (by norm_num)
theorem B433637 : Blo 191804 433637 := bbase (se 4 (by rfl) ⟨40653, by rfl⟩ : syracuseStep 433637 = 81307) (by norm_num)
theorem B433709 : Blo 191804 433709 := bbase (se 3 (by rfl) ⟨81320, by rfl⟩ : syracuseStep 433709 = 162641) (by norm_num)
theorem B368221 : Blo 191804 368221 := bbase (se 3 (by rfl) ⟨69041, by rfl⟩ : syracuseStep 368221 = 138083) (by norm_num)
theorem B433781 : Blo 191804 433781 := bbase (se 5 (by rfl) ⟨20333, by rfl⟩ : syracuseStep 433781 = 40667) (by norm_num)
theorem B433853 : Blo 191804 433853 := bbase (se 3 (by rfl) ⟨81347, by rfl⟩ : syracuseStep 433853 = 162695) (by norm_num)
theorem B892613 : Blo 191804 892613 := bbase (se 4 (by rfl) ⟨83682, by rfl⟩ : syracuseStep 892613 = 167365) (by norm_num)
theorem B2989781 : Blo 191804 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B368381 : Blo 191804 368381 := bbase (se 3 (by rfl) ⟨69071, by rfl⟩ : syracuseStep 368381 = 138143) (by norm_num)
theorem B433925 : Blo 191804 433925 := bbase (se 4 (by rfl) ⟨40680, by rfl⟩ : syracuseStep 433925 = 81361) (by norm_num)
theorem B433997 : Blo 191804 433997 := bbase (se 3 (by rfl) ⟨81374, by rfl⟩ : syracuseStep 433997 = 162749) (by norm_num)
theorem B368525 : Blo 191804 368525 := bbase (se 3 (by rfl) ⟨69098, by rfl⟩ : syracuseStep 368525 = 138197) (by norm_num)
theorem B434069 : Blo 191804 434069 := bbase (se 6 (by rfl) ⟨10173, by rfl⟩ : syracuseStep 434069 = 20347) (by norm_num)
theorem B1253333 : Blo 191804 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B434141 : Blo 191804 434141 := bbase (se 3 (by rfl) ⟨81401, by rfl⟩ : syracuseStep 434141 = 162803) (by norm_num)
theorem B434213 : Blo 191804 434213 := bbase (se 4 (by rfl) ⟨40707, by rfl⟩ : syracuseStep 434213 = 81415) (by norm_num)
theorem B1450037 : Blo 191804 1450037 := bbase (se 5 (by rfl) ⟨67970, by rfl⟩ : syracuseStep 1450037 = 135941) (by norm_num)
theorem B434285 : Blo 191804 434285 := bbase (se 3 (by rfl) ⟨81428, by rfl⟩ : syracuseStep 434285 = 162857) (by norm_num)
theorem B204925 : Blo 191804 204925 := bbase (se 3 (by rfl) ⟨38423, by rfl⟩ : syracuseStep 204925 = 76847) (by norm_num)
theorem B368813 : Blo 191804 368813 := bbase (se 3 (by rfl) ⟨69152, by rfl⟩ : syracuseStep 368813 = 138305) (by norm_num)
theorem B434357 : Blo 191804 434357 := bbase (se 5 (by rfl) ⟨20360, by rfl⟩ : syracuseStep 434357 = 40721) (by norm_num)
theorem B2367701 : Blo 191804 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B434429 : Blo 191804 434429 := bbase (se 3 (by rfl) ⟨81455, by rfl⟩ : syracuseStep 434429 = 162911) (by norm_num)
theorem B434501 : Blo 191804 434501 := bbase (se 4 (by rfl) ⟨40734, by rfl⟩ : syracuseStep 434501 = 81469) (by norm_num)
theorem B368965 : Blo 191804 368965 := bbase (se 4 (by rfl) ⟨34590, by rfl⟩ : syracuseStep 368965 = 69181) (by norm_num)
theorem B827765 : Blo 191804 827765 := bbase (se 5 (by rfl) ⟨38801, by rfl⟩ : syracuseStep 827765 = 77603) (by norm_num)
theorem B434573 : Blo 191804 434573 := bbase (se 3 (by rfl) ⟨81482, by rfl⟩ : syracuseStep 434573 = 162965) (by norm_num)
theorem B434645 : Blo 191804 434645 := bbase (se 7 (by rfl) ⟨5093, by rfl⟩ : syracuseStep 434645 = 10187) (by norm_num)
theorem B205301 : Blo 191804 205301 := bbase (se 5 (by rfl) ⟨9623, by rfl⟩ : syracuseStep 205301 = 19247) (by norm_num)
theorem B434717 : Blo 191804 434717 := bbase (se 3 (by rfl) ⟨81509, by rfl⟩ : syracuseStep 434717 = 163019) (by norm_num)
theorem B205373 : Blo 191804 205373 := bbase (se 3 (by rfl) ⟨38507, by rfl⟩ : syracuseStep 205373 = 77015) (by norm_num)
theorem B1679957 : Blo 191804 1679957 := bbase (se 8 (by rfl) ⟨9843, by rfl⟩ : syracuseStep 1679957 = 19687) (by norm_num)
theorem B467549 : Blo 191804 467549 := bbase (se 3 (by rfl) ⟨87665, by rfl⟩ : syracuseStep 467549 = 175331) (by norm_num)
theorem B434789 : Blo 191804 434789 := bbase (se 4 (by rfl) ⟨40761, by rfl⟩ : syracuseStep 434789 = 81523) (by norm_num)
theorem B369269 : Blo 191804 369269 := bbase (se 5 (by rfl) ⟨17309, by rfl⟩ : syracuseStep 369269 = 34619) (by norm_num)
theorem B828053 : Blo 191804 828053 := bbase (se 6 (by rfl) ⟨19407, by rfl⟩ : syracuseStep 828053 = 38815) (by norm_num)
theorem B434861 : Blo 191804 434861 := bbase (se 3 (by rfl) ⟨81536, by rfl⟩ : syracuseStep 434861 = 163073) (by norm_num)
theorem B434933 : Blo 191804 434933 := bbase (se 5 (by rfl) ⟨20387, by rfl⟩ : syracuseStep 434933 = 40775) (by norm_num)
theorem B205561 : Blo 191804 205561 := bbase (se 2 (by rfl) ⟨77085, by rfl⟩ : syracuseStep 205561 = 154171) (by norm_num)
theorem B467741 : Blo 191804 467741 := bbase (se 3 (by rfl) ⟨87701, by rfl⟩ : syracuseStep 467741 = 175403) (by norm_num)
theorem B435005 : Blo 191804 435005 := bbase (se 3 (by rfl) ⟨81563, by rfl⟩ : syracuseStep 435005 = 163127) (by norm_num)
theorem B435077 : Blo 191804 435077 := bbase (se 4 (by rfl) ⟨40788, by rfl⟩ : syracuseStep 435077 = 81577) (by norm_num)
theorem B205745 : Blo 191804 205745 := bbase (se 2 (by rfl) ⟨77154, by rfl⟩ : syracuseStep 205745 = 154309) (by norm_num)
theorem B435149 : Blo 191804 435149 := bbase (se 3 (by rfl) ⟨81590, by rfl⟩ : syracuseStep 435149 = 163181) (by norm_num)
theorem B435221 : Blo 191804 435221 := bbase (se 6 (by rfl) ⟨10200, by rfl⟩ : syracuseStep 435221 = 20401) (by norm_num)
theorem B1647701 : Blo 191804 1647701 := bbase (se 8 (by rfl) ⟨9654, by rfl⟩ : syracuseStep 1647701 = 19309) (by norm_num)
theorem B435293 : Blo 191804 435293 := bbase (se 3 (by rfl) ⟨81617, by rfl⟩ : syracuseStep 435293 = 163235) (by norm_num)
theorem B435365 : Blo 191804 435365 := bbase (se 4 (by rfl) ⟨40815, by rfl⟩ : syracuseStep 435365 = 81631) (by norm_num)
theorem B795845 : Blo 191804 795845 := bbase (se 4 (by rfl) ⟨74610, by rfl⟩ : syracuseStep 795845 = 149221) (by norm_num)
theorem B435437 : Blo 191804 435437 := bbase (se 3 (by rfl) ⟨81644, by rfl⟩ : syracuseStep 435437 = 163289) (by norm_num)
theorem B435509 : Blo 191804 435509 := bbase (se 5 (by rfl) ⟨20414, by rfl⟩ : syracuseStep 435509 = 40829) (by norm_num)
theorem B370021 : Blo 191804 370021 := bbase (se 4 (by rfl) ⟨34689, by rfl⟩ : syracuseStep 370021 = 69379) (by norm_num)
theorem B435581 : Blo 191804 435581 := bbase (se 3 (by rfl) ⟨81671, by rfl⟩ : syracuseStep 435581 = 163343) (by norm_num)
theorem B828805 : Blo 191804 828805 := bbase (se 4 (by rfl) ⟨77700, by rfl⟩ : syracuseStep 828805 = 155401) (by norm_num)
theorem B730565 : Blo 191804 730565 := bbase (se 4 (by rfl) ⟨68490, by rfl⟩ : syracuseStep 730565 = 136981) (by norm_num)
theorem B435653 : Blo 191804 435653 := bbase (se 4 (by rfl) ⟨40842, by rfl⟩ : syracuseStep 435653 = 81685) (by norm_num)
theorem B370165 : Blo 191804 370165 := bbase (se 5 (by rfl) ⟨17351, by rfl⟩ : syracuseStep 370165 = 34703) (by norm_num)
theorem B435725 : Blo 191804 435725 := bbase (se 3 (by rfl) ⟨81698, by rfl⟩ : syracuseStep 435725 = 163397) (by norm_num)
theorem B435797 : Blo 191804 435797 := bbase (se 8 (by rfl) ⟨2553, by rfl⟩ : syracuseStep 435797 = 5107) (by norm_num)
theorem B370325 : Blo 191804 370325 := bbase (se 6 (by rfl) ⟨8679, by rfl⟩ : syracuseStep 370325 = 17359) (by norm_num)
theorem B435869 : Blo 191804 435869 := bbase (se 3 (by rfl) ⟨81725, by rfl⟩ : syracuseStep 435869 = 163451) (by norm_num)
theorem B206497 : Blo 191804 206497 := bbase (se 2 (by rfl) ⟨77436, by rfl⟩ : syracuseStep 206497 = 154873) (by norm_num)
theorem B730853 : Blo 191804 730853 := bbase (se 4 (by rfl) ⟨68517, by rfl⟩ : syracuseStep 730853 = 137035) (by norm_num)
theorem B435941 : Blo 191804 435941 := bbase (se 4 (by rfl) ⟨40869, by rfl⟩ : syracuseStep 435941 = 81739) (by norm_num)
theorem B206569 : Blo 191804 206569 := bbase (se 2 (by rfl) ⟨77463, by rfl⟩ : syracuseStep 206569 = 154927) (by norm_num)
theorem B370469 : Blo 191804 370469 := bbase (se 4 (by rfl) ⟨34731, by rfl⟩ : syracuseStep 370469 = 69463) (by norm_num)
theorem B436013 : Blo 191804 436013 := bbase (se 3 (by rfl) ⟨81752, by rfl⟩ : syracuseStep 436013 = 163505) (by norm_num)
theorem B436085 : Blo 191804 436085 := bbase (se 5 (by rfl) ⟨20441, by rfl⟩ : syracuseStep 436085 = 40883) (by norm_num)
theorem B206749 : Blo 191804 206749 := bbase (se 3 (by rfl) ⟨38765, by rfl⟩ : syracuseStep 206749 = 77531) (by norm_num)
theorem B436157 : Blo 191804 436157 := bbase (se 3 (by rfl) ⟨81779, by rfl⟩ : syracuseStep 436157 = 163559) (by norm_num)
theorem B436229 : Blo 191804 436229 := bbase (se 4 (by rfl) ⟨40896, by rfl⟩ : syracuseStep 436229 = 81793) (by norm_num)
theorem B370757 : Blo 191804 370757 := bbase (se 4 (by rfl) ⟨34758, by rfl⟩ : syracuseStep 370757 = 69517) (by norm_num)
theorem B436301 : Blo 191804 436301 := bbase (se 3 (by rfl) ⟨81806, by rfl⟩ : syracuseStep 436301 = 163613) (by norm_num)
theorem B829541 : Blo 191804 829541 := bbase (se 4 (by rfl) ⟨77769, by rfl⟩ : syracuseStep 829541 = 155539) (by norm_num)
theorem B436373 : Blo 191804 436373 := bbase (se 6 (by rfl) ⟨10227, by rfl⟩ : syracuseStep 436373 = 20455) (by norm_num)
theorem B436445 : Blo 191804 436445 := bbase (se 3 (by rfl) ⟨81833, by rfl⟩ : syracuseStep 436445 = 163667) (by norm_num)
theorem B370909 : Blo 191804 370909 := bbase (se 3 (by rfl) ⟨69545, by rfl⟩ : syracuseStep 370909 = 139091) (by norm_num)
theorem B436517 : Blo 191804 436517 := bbase (se 4 (by rfl) ⟨40923, by rfl⟩ : syracuseStep 436517 = 81847) (by norm_num)
theorem B469309 : Blo 191804 469309 := bbase (se 3 (by rfl) ⟨87995, by rfl⟩ : syracuseStep 469309 = 175991) (by norm_num)
theorem B9382229 : Blo 191804 9382229 := bbase (se 10 (by rfl) ⟨13743, by rfl⟩ : syracuseStep 9382229 = 27487) (by norm_num)
theorem B207193 : Blo 191804 207193 := bbase (se 2 (by rfl) ⟨77697, by rfl⟩ : syracuseStep 207193 = 155395) (by norm_num)
theorem B436589 : Blo 191804 436589 := bbase (se 3 (by rfl) ⟨81860, by rfl⟩ : syracuseStep 436589 = 163721) (by norm_num)
theorem B436661 : Blo 191804 436661 := bbase (se 5 (by rfl) ⟨20468, by rfl⟩ : syracuseStep 436661 = 40937) (by norm_num)
theorem B207317 : Blo 191804 207317 := bbase (se 7 (by rfl) ⟨2429, by rfl⟩ : syracuseStep 207317 = 4859) (by norm_num)
theorem B436733 : Blo 191804 436733 := bbase (se 3 (by rfl) ⟨81887, by rfl⟩ : syracuseStep 436733 = 163775) (by norm_num)
theorem B371213 : Blo 191804 371213 := bbase (se 3 (by rfl) ⟨69602, by rfl⟩ : syracuseStep 371213 = 139205) (by norm_num)
theorem B436805 : Blo 191804 436805 := bbase (se 4 (by rfl) ⟨40950, by rfl⟩ : syracuseStep 436805 = 81901) (by norm_num)
theorem B633413 : Blo 191804 633413 := bbase (se 4 (by rfl) ⟨59382, by rfl⟩ : syracuseStep 633413 = 118765) (by norm_num)
theorem B436877 : Blo 191804 436877 := bbase (se 3 (by rfl) ⟨81914, by rfl⟩ : syracuseStep 436877 = 163829) (by norm_num)
theorem B207569 : Blo 191804 207569 := bbase (se 2 (by rfl) ⟨77838, by rfl⟩ : syracuseStep 207569 = 155677) (by norm_num)
theorem B436949 : Blo 191804 436949 := bbase (se 7 (by rfl) ⟨5120, by rfl⟩ : syracuseStep 436949 = 10241) (by norm_num)
theorem B437021 : Blo 191804 437021 := bbase (se 3 (by rfl) ⟨81941, by rfl⟩ : syracuseStep 437021 = 163883) (by norm_num)
theorem B437093 : Blo 191804 437093 := bbase (se 4 (by rfl) ⟨40977, by rfl⟩ : syracuseStep 437093 = 81955) (by norm_num)
theorem B732037 : Blo 191804 732037 := bbase (se 4 (by rfl) ⟨68628, by rfl⟩ : syracuseStep 732037 = 137257) (by norm_num)
theorem B469925 : Blo 191804 469925 := bbase (se 4 (by rfl) ⟨44055, by rfl⟩ : syracuseStep 469925 = 88111) (by norm_num)
theorem B437165 : Blo 191804 437165 := bbase (se 3 (by rfl) ⟨81968, by rfl⟩ : syracuseStep 437165 = 163937) (by norm_num)
theorem B273341 : Blo 191804 273341 := bbase (se 3 (by rfl) ⟨51251, by rfl⟩ : syracuseStep 273341 = 102503) (by norm_num)
theorem B437237 : Blo 191804 437237 := bbase (se 5 (by rfl) ⟨20495, by rfl⟩ : syracuseStep 437237 = 40991) (by norm_num)
theorem B437309 : Blo 191804 437309 := bbase (se 3 (by rfl) ⟨81995, by rfl⟩ : syracuseStep 437309 = 163991) (by norm_num)
theorem B437381 : Blo 191804 437381 := bbase (se 4 (by rfl) ⟨41004, by rfl⟩ : syracuseStep 437381 = 82009) (by norm_num)
theorem B208013 : Blo 191804 208013 := bbase (se 3 (by rfl) ⟨39002, by rfl⟩ : syracuseStep 208013 = 78005) (by norm_num)
theorem B732341 : Blo 191804 732341 := bbase (se 5 (by rfl) ⟨34328, by rfl⟩ : syracuseStep 732341 = 68657) (by norm_num)
theorem B371893 : Blo 191804 371893 := bbase (se 5 (by rfl) ⟨17432, by rfl⟩ : syracuseStep 371893 = 34865) (by norm_num)
theorem B437453 : Blo 191804 437453 := bbase (se 3 (by rfl) ⟨82022, by rfl⟩ : syracuseStep 437453 = 164045) (by norm_num)
theorem B437525 : Blo 191804 437525 := bbase (se 6 (by rfl) ⟨10254, by rfl⟩ : syracuseStep 437525 = 20509) (by norm_num)
theorem B666917 : Blo 191804 666917 := bbase (se 4 (by rfl) ⟨62523, by rfl⟩ : syracuseStep 666917 = 125047) (by norm_num)
theorem B437597 : Blo 191804 437597 := bbase (se 3 (by rfl) ⟨82049, by rfl⟩ : syracuseStep 437597 = 164099) (by norm_num)
theorem B929141 : Blo 191804 929141 := bbase (se 5 (by rfl) ⟨43553, by rfl⟩ : syracuseStep 929141 = 87107) (by norm_num)
theorem B208261 : Blo 191804 208261 := bbase (se 4 (by rfl) ⟨19524, by rfl⟩ : syracuseStep 208261 = 39049) (by norm_num)
theorem B437669 : Blo 191804 437669 := bbase (se 4 (by rfl) ⟨41031, by rfl⟩ : syracuseStep 437669 = 82063) (by norm_num)
theorem B437741 : Blo 191804 437741 := bbase (se 3 (by rfl) ⟨82076, by rfl⟩ : syracuseStep 437741 = 164153) (by norm_num)
theorem B437813 : Blo 191804 437813 := bbase (se 5 (by rfl) ⟨20522, by rfl⟩ : syracuseStep 437813 = 41045) (by norm_num)
theorem B437885 : Blo 191804 437885 := bbase (se 3 (by rfl) ⟨82103, by rfl⟩ : syracuseStep 437885 = 164207) (by norm_num)
theorem B437957 : Blo 191804 437957 := bbase (se 4 (by rfl) ⟨41058, by rfl⟩ : syracuseStep 437957 = 82117) (by norm_num)
theorem B438005 : Blo 191804 438005 := bbase (se 5 (by rfl) ⟨20531, by rfl⟩ : syracuseStep 438005 = 41063) (by norm_num)
theorem B372485 : Blo 191804 372485 := bbase (se 4 (by rfl) ⟨34920, by rfl⟩ : syracuseStep 372485 = 69841) (by norm_num)
theorem B438029 : Blo 191804 438029 := bbase (se 3 (by rfl) ⟨82130, by rfl⟩ : syracuseStep 438029 = 164261) (by norm_num)
theorem B208705 : Blo 191804 208705 := bbase (se 2 (by rfl) ⟨78264, by rfl⟩ : syracuseStep 208705 = 156529) (by norm_num)
theorem B438101 : Blo 191804 438101 := bbase (se 9 (by rfl) ⟨1283, by rfl⟩ : syracuseStep 438101 = 2567) (by norm_num)
theorem B208765 : Blo 191804 208765 := bbase (se 3 (by rfl) ⟨39143, by rfl⟩ : syracuseStep 208765 = 78287) (by norm_num)
theorem B438173 : Blo 191804 438173 := bbase (se 3 (by rfl) ⟨82157, by rfl⟩ : syracuseStep 438173 = 164315) (by norm_num)
theorem B438245 : Blo 191804 438245 := bbase (se 4 (by rfl) ⟨41085, by rfl⟩ : syracuseStep 438245 = 82171) (by norm_num)
theorem B1847285 : Blo 191804 1847285 := bbase (se 5 (by rfl) ⟨86591, by rfl⟩ : syracuseStep 1847285 = 173183) (by norm_num)
theorem B438317 : Blo 191804 438317 := bbase (se 3 (by rfl) ⟨82184, by rfl⟩ : syracuseStep 438317 = 164369) (by norm_num)
theorem B307253 : Blo 191804 307253 := bbase (se 5 (by rfl) ⟨14402, by rfl⟩ : syracuseStep 307253 = 28805) (by norm_num)
theorem B438389 : Blo 191804 438389 := bbase (se 5 (by rfl) ⟨20549, by rfl⟩ : syracuseStep 438389 = 41099) (by norm_num)
theorem B209081 : Blo 191804 209081 := bbase (se 2 (by rfl) ⟨78405, by rfl⟩ : syracuseStep 209081 = 156811) (by norm_num)
theorem B438461 : Blo 191804 438461 := bbase (se 3 (by rfl) ⟨82211, by rfl⟩ : syracuseStep 438461 = 164423) (by norm_num)
theorem B438533 : Blo 191804 438533 := bbase (se 4 (by rfl) ⟨41112, by rfl⟩ : syracuseStep 438533 = 82225) (by norm_num)
theorem B274765 : Blo 191804 274765 := bbase (se 3 (by rfl) ⟨51518, by rfl⟩ : syracuseStep 274765 = 103037) (by norm_num)
theorem B438605 : Blo 191804 438605 := bbase (se 3 (by rfl) ⟨82238, by rfl⟩ : syracuseStep 438605 = 164477) (by norm_num)
theorem B438677 : Blo 191804 438677 := bbase (se 6 (by rfl) ⟨10281, by rfl⟩ : syracuseStep 438677 = 20563) (by norm_num)
theorem B438749 : Blo 191804 438749 := bbase (se 3 (by rfl) ⟨82265, by rfl⟩ : syracuseStep 438749 = 164531) (by norm_num)
theorem B438821 : Blo 191804 438821 := bbase (se 4 (by rfl) ⟨41139, by rfl⟩ : syracuseStep 438821 = 82279) (by norm_num)
theorem B438893 : Blo 191804 438893 := bbase (se 3 (by rfl) ⟨82292, by rfl⟩ : syracuseStep 438893 = 164585) (by norm_num)
theorem B438965 : Blo 191804 438965 := bbase (se 5 (by rfl) ⟨20576, by rfl⟩ : syracuseStep 438965 = 41153) (by norm_num)
theorem B439037 : Blo 191804 439037 := bbase (se 3 (by rfl) ⟨82319, by rfl⟩ : syracuseStep 439037 = 164639) (by norm_num)
theorem B439109 : Blo 191804 439109 := bbase (se 4 (by rfl) ⟨41166, by rfl⟩ : syracuseStep 439109 = 82333) (by norm_num)
theorem B799621 : Blo 191804 799621 := bbase (se 4 (by rfl) ⟨74964, by rfl⟩ : syracuseStep 799621 = 149929) (by norm_num)
theorem B439181 : Blo 191804 439181 := bbase (se 3 (by rfl) ⟨82346, by rfl⟩ : syracuseStep 439181 = 164693) (by norm_num)
theorem B275357 : Blo 191804 275357 := bbase (se 3 (by rfl) ⟨51629, by rfl⟩ : syracuseStep 275357 = 103259) (by norm_num)
theorem B439229 : Blo 191804 439229 := bbase (se 3 (by rfl) ⟨82355, by rfl⟩ : syracuseStep 439229 = 164711) (by norm_num)
theorem B439253 : Blo 191804 439253 := bbase (se 7 (by rfl) ⟨5147, by rfl⟩ : syracuseStep 439253 = 10295) (by norm_num)
theorem B275437 : Blo 191804 275437 := bbase (se 3 (by rfl) ⟨51644, by rfl⟩ : syracuseStep 275437 = 103289) (by norm_num)
theorem B439325 : Blo 191804 439325 := bbase (se 3 (by rfl) ⟨82373, by rfl⟩ : syracuseStep 439325 = 164747) (by norm_num)
theorem B242777 : Blo 191804 242777 := bbase (se 2 (by rfl) ⟨91041, by rfl⟩ : syracuseStep 242777 = 182083) (by norm_num)
theorem B275557 : Blo 191804 275557 := bbase (se 4 (by rfl) ⟨25833, by rfl⟩ : syracuseStep 275557 = 51667) (by norm_num)
theorem B439397 : Blo 191804 439397 := bbase (se 4 (by rfl) ⟨41193, by rfl⟩ : syracuseStep 439397 = 82387) (by norm_num)
theorem B242833 : Blo 191804 242833 := bbase (se 2 (by rfl) ⟨91062, by rfl⟩ : syracuseStep 242833 = 182125) (by norm_num)
theorem B373909 : Blo 191804 373909 := bbase (se 6 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 373909 = 17527) (by norm_num)
theorem B439469 : Blo 191804 439469 := bbase (se 3 (by rfl) ⟨82400, by rfl⟩ : syracuseStep 439469 = 164801) (by norm_num)
theorem B275653 : Blo 191804 275653 := bbase (se 4 (by rfl) ⟨25842, by rfl⟩ : syracuseStep 275653 = 51685) (by norm_num)
theorem B701669 : Blo 191804 701669 := bbase (se 4 (by rfl) ⟨65781, by rfl⟩ : syracuseStep 701669 = 131563) (by norm_num)
theorem B242929 : Blo 191804 242929 := bbase (se 2 (by rfl) ⟨91098, by rfl⟩ : syracuseStep 242929 = 182197) (by norm_num)
theorem B734453 : Blo 191804 734453 := bbase (se 5 (by rfl) ⟨34427, by rfl⟩ : syracuseStep 734453 = 68855) (by norm_num)
theorem B439541 : Blo 191804 439541 := bbase (se 5 (by rfl) ⟨20603, by rfl⟩ : syracuseStep 439541 = 41207) (by norm_num)
theorem B439613 : Blo 191804 439613 := bbase (se 3 (by rfl) ⟨82427, by rfl⟩ : syracuseStep 439613 = 164855) (by norm_num)
theorem B832837 : Blo 191804 832837 := bbase (se 4 (by rfl) ⟨78078, by rfl⟩ : syracuseStep 832837 = 156157) (by norm_num)
theorem B439685 : Blo 191804 439685 := bbase (se 4 (by rfl) ⟨41220, by rfl⟩ : syracuseStep 439685 = 82441) (by norm_num)
theorem B243101 : Blo 191804 243101 := bbase (se 3 (by rfl) ⟨45581, by rfl⟩ : syracuseStep 243101 = 91163) (by norm_num)
theorem B439757 : Blo 191804 439757 := bbase (se 3 (by rfl) ⟨82454, by rfl⟩ : syracuseStep 439757 = 164909) (by norm_num)
theorem B243157 : Blo 191804 243157 := bbase (se 7 (by rfl) ⟨2849, by rfl⟩ : syracuseStep 243157 = 5699) (by norm_num)
theorem B308701 : Blo 191804 308701 := bbase (se 3 (by rfl) ⟨57881, by rfl⟩ : syracuseStep 308701 = 115763) (by norm_num)
theorem B734741 : Blo 191804 734741 := bbase (se 6 (by rfl) ⟨17220, by rfl⟩ : syracuseStep 734741 = 34441) (by norm_num)
theorem B439829 : Blo 191804 439829 := bbase (se 6 (by rfl) ⟨10308, by rfl⟩ : syracuseStep 439829 = 20617) (by norm_num)
theorem B243253 : Blo 191804 243253 := bbase (se 5 (by rfl) ⟨11402, by rfl⟩ : syracuseStep 243253 = 22805) (by norm_num)
theorem B439901 : Blo 191804 439901 := bbase (se 3 (by rfl) ⟨82481, by rfl⟩ : syracuseStep 439901 = 164963) (by norm_num)
theorem B996965 : Blo 191804 996965 := bbase (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) (by norm_num)
theorem B439973 : Blo 191804 439973 := bbase (se 4 (by rfl) ⟨41247, by rfl⟩ : syracuseStep 439973 = 82495) (by norm_num)
theorem B276149 : Blo 191804 276149 := bbase (se 5 (by rfl) ⟨12944, by rfl⟩ : syracuseStep 276149 = 25889) (by norm_num)
theorem B243425 : Blo 191804 243425 := bbase (se 2 (by rfl) ⟨91284, by rfl⟩ : syracuseStep 243425 = 182569) (by norm_num)
theorem B440045 : Blo 191804 440045 := bbase (se 3 (by rfl) ⟨82508, by rfl⟩ : syracuseStep 440045 = 165017) (by norm_num)
theorem B243481 : Blo 191804 243481 := bbase (se 2 (by rfl) ⟨91305, by rfl⟩ : syracuseStep 243481 = 182611) (by norm_num)
theorem B440117 : Blo 191804 440117 := bbase (se 5 (by rfl) ⟨20630, by rfl⟩ : syracuseStep 440117 = 41261) (by norm_num)
theorem B669541 : Blo 191804 669541 := bbase (se 4 (by rfl) ⟨62769, by rfl⟩ : syracuseStep 669541 = 125539) (by norm_num)
theorem B243577 : Blo 191804 243577 := bbase (se 2 (by rfl) ⟨91341, by rfl⟩ : syracuseStep 243577 = 182683) (by norm_num)
theorem B440189 : Blo 191804 440189 := bbase (se 3 (by rfl) ⟨82535, by rfl⟩ : syracuseStep 440189 = 165071) (by norm_num)
theorem B440261 : Blo 191804 440261 := bbase (se 4 (by rfl) ⟨41274, by rfl⟩ : syracuseStep 440261 = 82549) (by norm_num)
theorem B669653 : Blo 191804 669653 := bbase (se 7 (by rfl) ⟨7847, by rfl⟩ : syracuseStep 669653 = 15695) (by norm_num)
theorem B1718261 : Blo 191804 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B440333 : Blo 191804 440333 := bbase (se 3 (by rfl) ⟨82562, by rfl⟩ : syracuseStep 440333 = 165125) (by norm_num)
theorem B243749 : Blo 191804 243749 := bbase (se 4 (by rfl) ⟨22851, by rfl⟩ : syracuseStep 243749 = 45703) (by norm_num)
theorem B440405 : Blo 191804 440405 := bbase (se 8 (by rfl) ⟨2580, by rfl⟩ : syracuseStep 440405 = 5161) (by norm_num)
theorem B243805 : Blo 191804 243805 := bbase (se 3 (by rfl) ⟨45713, by rfl⟩ : syracuseStep 243805 = 91427) (by norm_num)
theorem B440477 : Blo 191804 440477 := bbase (se 3 (by rfl) ⟨82589, by rfl⟩ : syracuseStep 440477 = 165179) (by norm_num)
theorem B243901 : Blo 191804 243901 := bbase (se 3 (by rfl) ⟨45731, by rfl⟩ : syracuseStep 243901 = 91463) (by norm_num)
theorem B276701 : Blo 191804 276701 := bbase (se 3 (by rfl) ⟨51881, by rfl⟩ : syracuseStep 276701 = 103763) (by norm_num)
theorem B440549 : Blo 191804 440549 := bbase (se 4 (by rfl) ⟨41301, by rfl⟩ : syracuseStep 440549 = 82603) (by norm_num)
theorem B244073 : Blo 191804 244073 := bbase (se 2 (by rfl) ⟨91527, by rfl⟩ : syracuseStep 244073 = 183055) (by norm_num)
theorem B244129 : Blo 191804 244129 := bbase (se 2 (by rfl) ⟨91548, by rfl⟩ : syracuseStep 244129 = 183097) (by norm_num)
theorem B244225 : Blo 191804 244225 := bbase (se 2 (by rfl) ⟨91584, by rfl⟩ : syracuseStep 244225 = 183169) (by norm_num)
theorem B244397 : Blo 191804 244397 := bbase (se 3 (by rfl) ⟨45824, by rfl⟩ : syracuseStep 244397 = 91649) (by norm_num)
theorem B735925 : Blo 191804 735925 := bbase (se 5 (by rfl) ⟨34496, by rfl⟩ : syracuseStep 735925 = 68993) (by norm_num)
theorem B244453 : Blo 191804 244453 := bbase (se 4 (by rfl) ⟨22917, by rfl⟩ : syracuseStep 244453 = 45835) (by norm_num)
theorem B244549 : Blo 191804 244549 := bbase (se 4 (by rfl) ⟨22926, by rfl⟩ : syracuseStep 244549 = 45853) (by norm_num)
theorem B310085 : Blo 191804 310085 := bbase (se 4 (by rfl) ⟨29070, by rfl⟩ : syracuseStep 310085 = 58141) (by norm_num)
theorem B277453 : Blo 191804 277453 := bbase (se 3 (by rfl) ⟨52022, by rfl⟩ : syracuseStep 277453 = 104045) (by norm_num)
theorem B736229 : Blo 191804 736229 := bbase (se 4 (by rfl) ⟨69021, by rfl⟩ : syracuseStep 736229 = 138043) (by norm_num)
theorem B244721 : Blo 191804 244721 := bbase (se 2 (by rfl) ⟨91770, by rfl⟩ : syracuseStep 244721 = 183541) (by norm_num)
theorem B310277 : Blo 191804 310277 := bbase (se 4 (by rfl) ⟨29088, by rfl⟩ : syracuseStep 310277 = 58177) (by norm_num)
theorem B244777 : Blo 191804 244777 := bbase (se 2 (by rfl) ⟨91791, by rfl⟩ : syracuseStep 244777 = 183583) (by norm_num)
theorem B244873 : Blo 191804 244873 := bbase (se 2 (by rfl) ⟨91827, by rfl⟩ : syracuseStep 244873 = 183655) (by norm_num)
theorem B933125 : Blo 191804 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B245045 : Blo 191804 245045 := bbase (se 5 (by rfl) ⟨11486, by rfl⟩ : syracuseStep 245045 = 22973) (by norm_num)
theorem B245101 : Blo 191804 245101 := bbase (se 3 (by rfl) ⟨45956, by rfl⟩ : syracuseStep 245101 = 91913) (by norm_num)
theorem B245197 : Blo 191804 245197 := bbase (se 3 (by rfl) ⟨45974, by rfl⟩ : syracuseStep 245197 = 91949) (by norm_num)
theorem B1261109 : Blo 191804 1261109 := bbase (se 5 (by rfl) ⟨59114, by rfl⟩ : syracuseStep 1261109 = 118229) (by norm_num)
theorem B245369 : Blo 191804 245369 := bbase (se 2 (by rfl) ⟨92013, by rfl⟩ : syracuseStep 245369 = 184027) (by norm_num)
theorem B245425 : Blo 191804 245425 := bbase (se 2 (by rfl) ⟨92034, by rfl⟩ : syracuseStep 245425 = 184069) (by norm_num)
theorem B278245 : Blo 191804 278245 := bbase (se 4 (by rfl) ⟨26085, by rfl⟩ : syracuseStep 278245 = 52171) (by norm_num)
theorem B442093 : Blo 191804 442093 := bbase (se 3 (by rfl) ⟨82892, by rfl⟩ : syracuseStep 442093 = 165785) (by norm_num)
theorem B245521 : Blo 191804 245521 := bbase (se 2 (by rfl) ⟨92070, by rfl⟩ : syracuseStep 245521 = 184141) (by norm_num)
theorem B376741 : Blo 191804 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B245693 : Blo 191804 245693 := bbase (se 3 (by rfl) ⟨46067, by rfl⟩ : syracuseStep 245693 = 92135) (by norm_num)
theorem B245749 : Blo 191804 245749 := bbase (se 5 (by rfl) ⟨11519, by rfl⟩ : syracuseStep 245749 = 23039) (by norm_num)
theorem B278581 : Blo 191804 278581 := bbase (se 5 (by rfl) ⟨13058, by rfl⟩ : syracuseStep 278581 = 26117) (by norm_num)
theorem B245845 : Blo 191804 245845 := bbase (se 8 (by rfl) ⟨1440, by rfl⟩ : syracuseStep 245845 = 2881) (by norm_num)
theorem B409789 : Blo 191804 409789 := bbase (se 3 (by rfl) ⟨76835, by rfl⟩ : syracuseStep 409789 = 153671) (by norm_num)
theorem B835829 : Blo 191804 835829 := bbase (se 5 (by rfl) ⟨39179, by rfl⟩ : syracuseStep 835829 = 78359) (by norm_num)
theorem B246017 : Blo 191804 246017 := bbase (se 2 (by rfl) ⟨92256, by rfl⟩ : syracuseStep 246017 = 184513) (by norm_num)
theorem B999701 : Blo 191804 999701 := bbase (se 6 (by rfl) ⟨23430, by rfl⟩ : syracuseStep 999701 = 46861) (by norm_num)
theorem B311597 : Blo 191804 311597 := bbase (se 3 (by rfl) ⟨58424, by rfl⟩ : syracuseStep 311597 = 116849) (by norm_num)
theorem B1458485 : Blo 191804 1458485 := bbase (se 5 (by rfl) ⟨68366, by rfl⟩ : syracuseStep 1458485 = 136733) (by norm_num)
theorem B246073 : Blo 191804 246073 := bbase (se 2 (by rfl) ⟨92277, by rfl⟩ : syracuseStep 246073 = 184555) (by norm_num)
theorem B311693 : Blo 191804 311693 := bbase (se 3 (by rfl) ⟨58442, by rfl⟩ : syracuseStep 311693 = 116885) (by norm_num)
theorem B246169 : Blo 191804 246169 := bbase (se 2 (by rfl) ⟨92313, by rfl⟩ : syracuseStep 246169 = 184627) (by norm_num)
theorem B311725 : Blo 191804 311725 := bbase (se 3 (by rfl) ⟨58448, by rfl⟩ : syracuseStep 311725 = 116897) (by norm_num)
theorem B246341 : Blo 191804 246341 := bbase (se 4 (by rfl) ⟨23094, by rfl⟩ : syracuseStep 246341 = 46189) (by norm_num)
theorem B246397 : Blo 191804 246397 := bbase (se 3 (by rfl) ⟨46199, by rfl⟩ : syracuseStep 246397 = 92399) (by norm_num)
theorem B410285 : Blo 191804 410285 := bbase (se 3 (by rfl) ⟨76928, by rfl⟩ : syracuseStep 410285 = 153857) (by norm_num)
theorem B246493 : Blo 191804 246493 := bbase (se 3 (by rfl) ⟨46217, by rfl⟩ : syracuseStep 246493 = 92435) (by norm_num)
theorem B246665 : Blo 191804 246665 := bbase (se 2 (by rfl) ⟨92499, by rfl⟩ : syracuseStep 246665 = 184999) (by norm_num)
theorem B246721 : Blo 191804 246721 := bbase (se 2 (by rfl) ⟨92520, by rfl⟩ : syracuseStep 246721 = 185041) (by norm_num)
theorem B246817 : Blo 191804 246817 := bbase (se 2 (by rfl) ⟨92556, by rfl⟩ : syracuseStep 246817 = 185113) (by norm_num)
theorem B738341 : Blo 191804 738341 := bbase (se 4 (by rfl) ⟨69219, by rfl⟩ : syracuseStep 738341 = 138439) (by norm_num)
theorem B279733 : Blo 191804 279733 := bbase (se 5 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 279733 = 26225) (by norm_num)
theorem B246989 : Blo 191804 246989 := bbase (se 3 (by rfl) ⟨46310, by rfl⟩ : syracuseStep 246989 = 92621) (by norm_num)
theorem B247045 : Blo 191804 247045 := bbase (se 4 (by rfl) ⟨23160, by rfl⟩ : syracuseStep 247045 = 46321) (by norm_num)
theorem B738629 : Blo 191804 738629 := bbase (se 4 (by rfl) ⟨69246, by rfl⟩ : syracuseStep 738629 = 138493) (by norm_num)
theorem B247141 : Blo 191804 247141 := bbase (se 4 (by rfl) ⟨23169, by rfl⟩ : syracuseStep 247141 = 46339) (by norm_num)
theorem B247297 : Blo 191804 247297 := bbase (se 2 (by rfl) ⟨92736, by rfl⟩ : syracuseStep 247297 = 185473) (by norm_num)
theorem B411149 : Blo 191804 411149 := bbase (se 3 (by rfl) ⟨77090, by rfl⟩ : syracuseStep 411149 = 154181) (by norm_num)
theorem B247313 : Blo 191804 247313 := bbase (se 2 (by rfl) ⟨92742, by rfl⟩ : syracuseStep 247313 = 185485) (by norm_num)
theorem B247369 : Blo 191804 247369 := bbase (se 2 (by rfl) ⟨92763, by rfl⟩ : syracuseStep 247369 = 185527) (by norm_num)
theorem B411293 : Blo 191804 411293 := bbase (se 3 (by rfl) ⟨77117, by rfl⟩ : syracuseStep 411293 = 154235) (by norm_num)
theorem B247465 : Blo 191804 247465 := bbase (se 2 (by rfl) ⟨92799, by rfl⟩ : syracuseStep 247465 = 185599) (by norm_num)
theorem B247609 : Blo 191804 247609 := bbase (se 2 (by rfl) ⟨92853, by rfl⟩ : syracuseStep 247609 = 185707) (by norm_num)
theorem B247637 : Blo 191804 247637 := bbase (se 9 (by rfl) ⟨725, by rfl⟩ : syracuseStep 247637 = 1451) (by norm_num)
theorem B247693 : Blo 191804 247693 := bbase (se 3 (by rfl) ⟨46442, by rfl⟩ : syracuseStep 247693 = 92885) (by norm_num)
theorem B313237 : Blo 191804 313237 := bbase (se 6 (by rfl) ⟨7341, by rfl⟩ : syracuseStep 313237 = 14683) (by norm_num)
theorem B247789 : Blo 191804 247789 := bbase (se 3 (by rfl) ⟨46460, by rfl⟩ : syracuseStep 247789 = 92921) (by norm_num)
theorem B1001605 : Blo 191804 1001605 := bbase (se 4 (by rfl) ⟨93900, by rfl⟩ : syracuseStep 1001605 = 187801) (by norm_num)
theorem B1099925 : Blo 191804 1099925 := bbase (se 6 (by rfl) ⟨25779, by rfl⟩ : syracuseStep 1099925 = 51559) (by norm_num)
theorem B412037 : Blo 191804 412037 := bbase (se 4 (by rfl) ⟨38628, by rfl⟩ : syracuseStep 412037 = 77257) (by norm_num)
theorem B739813 : Blo 191804 739813 := bbase (se 4 (by rfl) ⟨69357, by rfl⟩ : syracuseStep 739813 = 138715) (by norm_num)
theorem B215797 : Blo 191804 215797 := bbase (se 5 (by rfl) ⟨10115, by rfl⟩ : syracuseStep 215797 = 20231) (by norm_num)
theorem B740117 : Blo 191804 740117 := bbase (se 6 (by rfl) ⟨17346, by rfl⟩ : syracuseStep 740117 = 34693) (by norm_num)
theorem B215833 : Blo 191804 215833 := bbase (se 2 (by rfl) ⟨80937, by rfl⟩ : syracuseStep 215833 = 161875) (by norm_num)
theorem B215869 : Blo 191804 215869 := bbase (se 3 (by rfl) ⟨40475, by rfl⟩ : syracuseStep 215869 = 80951) (by norm_num)
theorem B215905 : Blo 191804 215905 := bbase (se 2 (by rfl) ⟨80964, by rfl⟩ : syracuseStep 215905 = 161929) (by norm_num)
theorem B1002341 : Blo 191804 1002341 := bbase (se 4 (by rfl) ⟨93969, by rfl⟩ : syracuseStep 1002341 = 187939) (by norm_num)
theorem B215941 : Blo 191804 215941 := bbase (se 4 (by rfl) ⟨20244, by rfl⟩ : syracuseStep 215941 = 40489) (by norm_num)
theorem B215977 : Blo 191804 215977 := bbase (se 2 (by rfl) ⟨80991, by rfl⟩ : syracuseStep 215977 = 161983) (by norm_num)
theorem B216013 : Blo 191804 216013 := bbase (se 3 (by rfl) ⟨40502, by rfl⟩ : syracuseStep 216013 = 81005) (by norm_num)
theorem B216049 : Blo 191804 216049 := bbase (se 2 (by rfl) ⟨81018, by rfl⟩ : syracuseStep 216049 = 162037) (by norm_num)
theorem B1395701 : Blo 191804 1395701 := bbase (se 5 (by rfl) ⟨65423, by rfl⟩ : syracuseStep 1395701 = 130847) (by norm_num)
theorem B216085 : Blo 191804 216085 := bbase (se 6 (by rfl) ⟨5064, by rfl⟩ : syracuseStep 216085 = 10129) (by norm_num)
theorem B216121 : Blo 191804 216121 := bbase (se 2 (by rfl) ⟨81045, by rfl⟩ : syracuseStep 216121 = 162091) (by norm_num)
theorem B2477141 : Blo 191804 2477141 := bbase (se 8 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 2477141 = 29029) (by norm_num)
theorem B216157 : Blo 191804 216157 := bbase (se 3 (by rfl) ⟨40529, by rfl⟩ : syracuseStep 216157 = 81059) (by norm_num)
theorem B412789 : Blo 191804 412789 := bbase (se 5 (by rfl) ⟨19349, by rfl⟩ : syracuseStep 412789 = 38699) (by norm_num)
theorem B216193 : Blo 191804 216193 := bbase (se 2 (by rfl) ⟨81072, by rfl⟩ : syracuseStep 216193 = 162145) (by norm_num)
theorem B216229 : Blo 191804 216229 := bbase (se 4 (by rfl) ⟨20271, by rfl⟩ : syracuseStep 216229 = 40543) (by norm_num)
theorem B216265 : Blo 191804 216265 := bbase (se 2 (by rfl) ⟨81099, by rfl⟩ : syracuseStep 216265 = 162199) (by norm_num)
theorem B216301 : Blo 191804 216301 := bbase (se 3 (by rfl) ⟨40556, by rfl⟩ : syracuseStep 216301 = 81113) (by norm_num)
theorem B412933 : Blo 191804 412933 := bbase (se 4 (by rfl) ⟨38712, by rfl⟩ : syracuseStep 412933 = 77425) (by norm_num)
theorem B216337 : Blo 191804 216337 := bbase (se 2 (by rfl) ⟨81126, by rfl⟩ : syracuseStep 216337 = 162253) (by norm_num)
theorem B642325 : Blo 191804 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B2379029 : Blo 191804 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B216373 : Blo 191804 216373 := bbase (se 5 (by rfl) ⟨10142, by rfl⟩ : syracuseStep 216373 = 20285) (by norm_num)
theorem B216409 : Blo 191804 216409 := bbase (se 2 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 216409 = 162307) (by norm_num)
theorem B216445 : Blo 191804 216445 := bbase (se 3 (by rfl) ⟨40583, by rfl⟩ : syracuseStep 216445 = 81167) (by norm_num)
theorem B216481 : Blo 191804 216481 := bbase (se 2 (by rfl) ⟨81180, by rfl⟩ : syracuseStep 216481 = 162361) (by norm_num)
theorem B216517 : Blo 191804 216517 := bbase (se 4 (by rfl) ⟨20298, by rfl⟩ : syracuseStep 216517 = 40597) (by norm_num)
theorem B216553 : Blo 191804 216553 := bbase (se 2 (by rfl) ⟨81207, by rfl⟩ : syracuseStep 216553 = 162415) (by norm_num)
theorem B216589 : Blo 191804 216589 := bbase (se 3 (by rfl) ⟨40610, by rfl⟩ : syracuseStep 216589 = 81221) (by norm_num)
theorem B216625 : Blo 191804 216625 := bbase (se 2 (by rfl) ⟨81234, by rfl⟩ : syracuseStep 216625 = 162469) (by norm_num)
theorem B216661 : Blo 191804 216661 := bbase (se 8 (by rfl) ⟨1269, by rfl⟩ : syracuseStep 216661 = 2539) (by norm_num)
theorem B216697 : Blo 191804 216697 := bbase (se 2 (by rfl) ⟨81261, by rfl⟩ : syracuseStep 216697 = 162523) (by norm_num)
theorem B413309 : Blo 191804 413309 := bbase (se 3 (by rfl) ⟨77495, by rfl⟩ : syracuseStep 413309 = 154991) (by norm_num)
theorem B216733 : Blo 191804 216733 := bbase (se 3 (by rfl) ⟨40637, by rfl⟩ : syracuseStep 216733 = 81275) (by norm_num)
theorem B216769 : Blo 191804 216769 := bbase (se 2 (by rfl) ⟨81288, by rfl⟩ : syracuseStep 216769 = 162577) (by norm_num)
theorem B216805 : Blo 191804 216805 := bbase (se 4 (by rfl) ⟨20325, by rfl⟩ : syracuseStep 216805 = 40651) (by norm_num)
theorem B216841 : Blo 191804 216841 := bbase (se 2 (by rfl) ⟨81315, by rfl⟩ : syracuseStep 216841 = 162631) (by norm_num)
theorem B216877 : Blo 191804 216877 := bbase (se 3 (by rfl) ⟨40664, by rfl⟩ : syracuseStep 216877 = 81329) (by norm_num)
theorem B216913 : Blo 191804 216913 := bbase (se 2 (by rfl) ⟨81342, by rfl⟩ : syracuseStep 216913 = 162685) (by norm_num)
theorem B216949 : Blo 191804 216949 := bbase (se 5 (by rfl) ⟨10169, by rfl⟩ : syracuseStep 216949 = 20339) (by norm_num)
theorem B216985 : Blo 191804 216985 := bbase (se 2 (by rfl) ⟨81369, by rfl⟩ : syracuseStep 216985 = 162739) (by norm_num)
theorem B217021 : Blo 191804 217021 := bbase (se 3 (by rfl) ⟨40691, by rfl⟩ : syracuseStep 217021 = 81383) (by norm_num)
theorem B217057 : Blo 191804 217057 := bbase (se 2 (by rfl) ⟨81396, by rfl⟩ : syracuseStep 217057 = 162793) (by norm_num)
theorem B413677 : Blo 191804 413677 := bbase (se 3 (by rfl) ⟨77564, by rfl⟩ : syracuseStep 413677 = 155129) (by norm_num)
theorem B217093 : Blo 191804 217093 := bbase (se 4 (by rfl) ⟨20352, by rfl⟩ : syracuseStep 217093 = 40705) (by norm_num)
theorem B217129 : Blo 191804 217129 := bbase (se 2 (by rfl) ⟨81423, by rfl⟩ : syracuseStep 217129 = 162847) (by norm_num)
theorem B217165 : Blo 191804 217165 := bbase (se 3 (by rfl) ⟨40718, by rfl⟩ : syracuseStep 217165 = 81437) (by norm_num)
theorem B217201 : Blo 191804 217201 := bbase (se 2 (by rfl) ⟨81450, by rfl⟩ : syracuseStep 217201 = 162901) (by norm_num)
theorem B217237 : Blo 191804 217237 := bbase (se 6 (by rfl) ⟨5091, by rfl⟩ : syracuseStep 217237 = 10183) (by norm_num)
theorem B217273 : Blo 191804 217273 := bbase (se 2 (by rfl) ⟨81477, by rfl⟩ : syracuseStep 217273 = 162955) (by norm_num)
theorem B217309 : Blo 191804 217309 := bbase (se 3 (by rfl) ⟨40745, by rfl⟩ : syracuseStep 217309 = 81491) (by norm_num)
theorem B938213 : Blo 191804 938213 := bbase (se 4 (by rfl) ⟨87957, by rfl⟩ : syracuseStep 938213 = 175915) (by norm_num)
theorem B217345 : Blo 191804 217345 := bbase (se 2 (by rfl) ⟨81504, by rfl⟩ : syracuseStep 217345 = 163009) (by norm_num)
theorem B217381 : Blo 191804 217381 := bbase (se 4 (by rfl) ⟨20379, by rfl⟩ : syracuseStep 217381 = 40759) (by norm_num)
theorem B217417 : Blo 191804 217417 := bbase (se 2 (by rfl) ⟨81531, by rfl⟩ : syracuseStep 217417 = 163063) (by norm_num)
theorem B217453 : Blo 191804 217453 := bbase (se 3 (by rfl) ⟨40772, by rfl⟩ : syracuseStep 217453 = 81545) (by norm_num)
theorem B217489 : Blo 191804 217489 := bbase (se 2 (by rfl) ⟨81558, by rfl⟩ : syracuseStep 217489 = 163117) (by norm_num)
theorem B938405 : Blo 191804 938405 := bbase (se 4 (by rfl) ⟨87975, by rfl⟩ : syracuseStep 938405 = 175951) (by norm_num)
theorem B971189 : Blo 191804 971189 := bbase (se 5 (by rfl) ⟨45524, by rfl⟩ : syracuseStep 971189 = 91049) (by norm_num)
theorem B217525 : Blo 191804 217525 := bbase (se 5 (by rfl) ⟨10196, by rfl⟩ : syracuseStep 217525 = 20393) (by norm_num)
theorem B217561 : Blo 191804 217561 := bbase (se 2 (by rfl) ⟨81585, by rfl⟩ : syracuseStep 217561 = 163171) (by norm_num)
theorem B217597 : Blo 191804 217597 := bbase (se 3 (by rfl) ⟨40799, by rfl⟩ : syracuseStep 217597 = 81599) (by norm_num)
theorem B217633 : Blo 191804 217633 := bbase (se 2 (by rfl) ⟨81612, by rfl⟩ : syracuseStep 217633 = 163225) (by norm_num)
theorem B217669 : Blo 191804 217669 := bbase (se 4 (by rfl) ⟨20406, by rfl⟩ : syracuseStep 217669 = 40813) (by norm_num)
theorem B217705 : Blo 191804 217705 := bbase (se 2 (by rfl) ⟨81639, by rfl⟩ : syracuseStep 217705 = 163279) (by norm_num)
theorem B217741 : Blo 191804 217741 := bbase (se 3 (by rfl) ⟨40826, by rfl⟩ : syracuseStep 217741 = 81653) (by norm_num)
theorem B217777 : Blo 191804 217777 := bbase (se 2 (by rfl) ⟨81666, by rfl⟩ : syracuseStep 217777 = 163333) (by norm_num)
theorem B217813 : Blo 191804 217813 := bbase (se 7 (by rfl) ⟨2552, by rfl⟩ : syracuseStep 217813 = 5105) (by norm_num)
theorem B217849 : Blo 191804 217849 := bbase (se 2 (by rfl) ⟨81693, by rfl⟩ : syracuseStep 217849 = 163387) (by norm_num)
theorem B217885 : Blo 191804 217885 := bbase (se 3 (by rfl) ⟨40853, by rfl⟩ : syracuseStep 217885 = 81707) (by norm_num)
theorem B938789 : Blo 191804 938789 := bbase (se 4 (by rfl) ⟨88011, by rfl⟩ : syracuseStep 938789 = 176023) (by norm_num)
theorem B348989 : Blo 191804 348989 := bbase (se 3 (by rfl) ⟨65435, by rfl⟩ : syracuseStep 348989 = 130871) (by norm_num)
theorem B217921 : Blo 191804 217921 := bbase (se 2 (by rfl) ⟨81720, by rfl⟩ : syracuseStep 217921 = 163441) (by norm_num)
theorem B742229 : Blo 191804 742229 := bbase (se 9 (by rfl) ⟨2174, by rfl⟩ : syracuseStep 742229 = 4349) (by norm_num)
theorem B217957 : Blo 191804 217957 := bbase (se 4 (by rfl) ⟨20433, by rfl⟩ : syracuseStep 217957 = 40867) (by norm_num)
theorem B217993 : Blo 191804 217993 := bbase (se 2 (by rfl) ⟨81747, by rfl⟩ : syracuseStep 217993 = 163495) (by norm_num)
theorem B1659797 : Blo 191804 1659797 := bbase (se 6 (by rfl) ⟨38901, by rfl⟩ : syracuseStep 1659797 = 77803) (by norm_num)
theorem B218029 : Blo 191804 218029 := bbase (se 3 (by rfl) ⟨40880, by rfl⟩ : syracuseStep 218029 = 81761) (by norm_num)
theorem B218065 : Blo 191804 218065 := bbase (se 2 (by rfl) ⟨81774, by rfl⟩ : syracuseStep 218065 = 163549) (by norm_num)
theorem B218101 : Blo 191804 218101 := bbase (se 5 (by rfl) ⟨10223, by rfl⟩ : syracuseStep 218101 = 20447) (by norm_num)
theorem B218137 : Blo 191804 218137 := bbase (se 2 (by rfl) ⟨81801, by rfl⟩ : syracuseStep 218137 = 163603) (by norm_num)
theorem B218173 : Blo 191804 218173 := bbase (se 3 (by rfl) ⟨40907, by rfl⟩ : syracuseStep 218173 = 81815) (by norm_num)
theorem B218209 : Blo 191804 218209 := bbase (se 2 (by rfl) ⟨81828, by rfl⟩ : syracuseStep 218209 = 163657) (by norm_num)
theorem B742517 : Blo 191804 742517 := bbase (se 5 (by rfl) ⟨34805, by rfl⟩ : syracuseStep 742517 = 69611) (by norm_num)
theorem B250997 : Blo 191804 250997 := bbase (se 5 (by rfl) ⟨11765, by rfl⟩ : syracuseStep 250997 = 23531) (by norm_num)
theorem B218245 : Blo 191804 218245 := bbase (se 4 (by rfl) ⟨20460, by rfl⟩ : syracuseStep 218245 = 40921) (by norm_num)
theorem B218281 : Blo 191804 218281 := bbase (se 2 (by rfl) ⟨81855, by rfl⟩ : syracuseStep 218281 = 163711) (by norm_num)
theorem B218317 : Blo 191804 218317 := bbase (se 3 (by rfl) ⟨40934, by rfl⟩ : syracuseStep 218317 = 81869) (by norm_num)
theorem B218353 : Blo 191804 218353 := bbase (se 2 (by rfl) ⟨81882, by rfl⟩ : syracuseStep 218353 = 163765) (by norm_num)
theorem B218389 : Blo 191804 218389 := bbase (se 6 (by rfl) ⟨5118, by rfl⟩ : syracuseStep 218389 = 10237) (by norm_num)
theorem B218425 : Blo 191804 218425 := bbase (se 2 (by rfl) ⟨81909, by rfl⟩ : syracuseStep 218425 = 163819) (by norm_num)
theorem B218461 : Blo 191804 218461 := bbase (se 3 (by rfl) ⟨40961, by rfl⟩ : syracuseStep 218461 = 81923) (by norm_num)
theorem B218497 : Blo 191804 218497 := bbase (se 2 (by rfl) ⟨81936, by rfl⟩ : syracuseStep 218497 = 163873) (by norm_num)
theorem B1037717 : Blo 191804 1037717 := bbase (se 6 (by rfl) ⟨24321, by rfl⟩ : syracuseStep 1037717 = 48643) (by norm_num)
theorem B218533 : Blo 191804 218533 := bbase (se 4 (by rfl) ⟨20487, by rfl⟩ : syracuseStep 218533 = 40975) (by norm_num)
theorem B1496501 : Blo 191804 1496501 := bbase (se 5 (by rfl) ⟨70148, by rfl⟩ : syracuseStep 1496501 = 140297) (by norm_num)
theorem B218569 : Blo 191804 218569 := bbase (se 2 (by rfl) ⟨81963, by rfl⟩ : syracuseStep 218569 = 163927) (by norm_num)
theorem B415181 : Blo 191804 415181 := bbase (se 3 (by rfl) ⟨77846, by rfl⟩ : syracuseStep 415181 = 155693) (by norm_num)
theorem B218605 : Blo 191804 218605 := bbase (se 3 (by rfl) ⟨40988, by rfl⟩ : syracuseStep 218605 = 81977) (by norm_num)
theorem B218641 : Blo 191804 218641 := bbase (se 2 (by rfl) ⟨81990, by rfl⟩ : syracuseStep 218641 = 163981) (by norm_num)
theorem B349733 : Blo 191804 349733 := bbase (se 4 (by rfl) ⟨32787, by rfl⟩ : syracuseStep 349733 = 65575) (by norm_num)
theorem B218677 : Blo 191804 218677 := bbase (se 5 (by rfl) ⟨10250, by rfl⟩ : syracuseStep 218677 = 20501) (by norm_num)
theorem B218713 : Blo 191804 218713 := bbase (se 2 (by rfl) ⟨82017, by rfl⟩ : syracuseStep 218713 = 164035) (by norm_num)
theorem B415325 : Blo 191804 415325 := bbase (se 3 (by rfl) ⟨77873, by rfl⟩ : syracuseStep 415325 = 155747) (by norm_num)
theorem B218749 : Blo 191804 218749 := bbase (se 3 (by rfl) ⟨41015, by rfl⟩ : syracuseStep 218749 = 82031) (by norm_num)
theorem B218785 : Blo 191804 218785 := bbase (se 2 (by rfl) ⟨82044, by rfl⟩ : syracuseStep 218785 = 164089) (by norm_num)
theorem B972485 : Blo 191804 972485 := bbase (se 4 (by rfl) ⟨91170, by rfl⟩ : syracuseStep 972485 = 182341) (by norm_num)
theorem B218821 : Blo 191804 218821 := bbase (se 4 (by rfl) ⟨20514, by rfl⟩ : syracuseStep 218821 = 41029) (by norm_num)
theorem B218857 : Blo 191804 218857 := bbase (se 2 (by rfl) ⟨82071, by rfl⟩ : syracuseStep 218857 = 164143) (by norm_num)
theorem B218893 : Blo 191804 218893 := bbase (se 3 (by rfl) ⟨41042, by rfl⟩ : syracuseStep 218893 = 82085) (by norm_num)
theorem B2119445 : Blo 191804 2119445 := bbase (se 6 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 2119445 = 99349) (by norm_num)
theorem B218929 : Blo 191804 218929 := bbase (se 2 (by rfl) ⟨82098, by rfl⟩ : syracuseStep 218929 = 164197) (by norm_num)
theorem B218965 : Blo 191804 218965 := bbase (se 9 (by rfl) ⟨641, by rfl⟩ : syracuseStep 218965 = 1283) (by norm_num)
theorem B219001 : Blo 191804 219001 := bbase (se 2 (by rfl) ⟨82125, by rfl⟩ : syracuseStep 219001 = 164251) (by norm_num)
theorem B219037 : Blo 191804 219037 := bbase (se 3 (by rfl) ⟨41069, by rfl⟩ : syracuseStep 219037 = 82139) (by norm_num)
theorem B219073 : Blo 191804 219073 := bbase (se 2 (by rfl) ⟨82152, by rfl⟩ : syracuseStep 219073 = 164305) (by norm_num)
theorem B415685 : Blo 191804 415685 := bbase (se 4 (by rfl) ⟨38970, by rfl⟩ : syracuseStep 415685 = 77941) (by norm_num)
theorem B219109 : Blo 191804 219109 := bbase (se 4 (by rfl) ⟨20541, by rfl⟩ : syracuseStep 219109 = 41083) (by norm_num)
theorem B219145 : Blo 191804 219145 := bbase (se 2 (by rfl) ⟨82179, by rfl⟩ : syracuseStep 219145 = 164359) (by norm_num)
theorem B219181 : Blo 191804 219181 := bbase (se 3 (by rfl) ⟨41096, by rfl⟩ : syracuseStep 219181 = 82193) (by norm_num)
theorem B219217 : Blo 191804 219217 := bbase (se 2 (by rfl) ⟨82206, by rfl⟩ : syracuseStep 219217 = 164413) (by norm_num)
theorem B219253 : Blo 191804 219253 := bbase (se 5 (by rfl) ⟨10277, by rfl⟩ : syracuseStep 219253 = 20555) (by norm_num)
theorem B219277 : Blo 191804 219277 := bbase (se 3 (by rfl) ⟨41114, by rfl⟩ : syracuseStep 219277 = 82229) (by norm_num)
theorem B219289 : Blo 191804 219289 := bbase (se 2 (by rfl) ⟨82233, by rfl⟩ : syracuseStep 219289 = 164467) (by norm_num)
theorem B219325 : Blo 191804 219325 := bbase (se 3 (by rfl) ⟨41123, by rfl⟩ : syracuseStep 219325 = 82247) (by norm_num)
theorem B547013 : Blo 191804 547013 := bbase (se 4 (by rfl) ⟨51282, by rfl⟩ : syracuseStep 547013 = 102565) (by norm_num)
theorem B219361 : Blo 191804 219361 := bbase (se 2 (by rfl) ⟨82260, by rfl⟩ : syracuseStep 219361 = 164521) (by norm_num)
theorem B1038581 : Blo 191804 1038581 := bbase (se 5 (by rfl) ⟨48683, by rfl⟩ : syracuseStep 1038581 = 97367) (by norm_num)
theorem B219397 : Blo 191804 219397 := bbase (se 4 (by rfl) ⟨20568, by rfl⟩ : syracuseStep 219397 = 41137) (by norm_num)
theorem B219433 : Blo 191804 219433 := bbase (se 2 (by rfl) ⟨82287, by rfl⟩ : syracuseStep 219433 = 164575) (by norm_num)
theorem B219469 : Blo 191804 219469 := bbase (se 3 (by rfl) ⟨41150, by rfl⟩ : syracuseStep 219469 = 82301) (by norm_num)
theorem B219505 : Blo 191804 219505 := bbase (se 2 (by rfl) ⟨82314, by rfl⟩ : syracuseStep 219505 = 164629) (by norm_num)
theorem B219541 : Blo 191804 219541 := bbase (se 6 (by rfl) ⟨5145, by rfl⟩ : syracuseStep 219541 = 10291) (by norm_num)
theorem B219577 : Blo 191804 219577 := bbase (se 2 (by rfl) ⟨82341, by rfl⟩ : syracuseStep 219577 = 164683) (by norm_num)
theorem B219613 : Blo 191804 219613 := bbase (se 3 (by rfl) ⟨41177, by rfl⟩ : syracuseStep 219613 = 82355) (by norm_num)
theorem B219649 : Blo 191804 219649 := bbase (se 2 (by rfl) ⟨82368, by rfl⟩ : syracuseStep 219649 = 164737) (by norm_num)
theorem B219685 : Blo 191804 219685 := bbase (se 4 (by rfl) ⟨20595, by rfl⟩ : syracuseStep 219685 = 41191) (by norm_num)
theorem B219721 : Blo 191804 219721 := bbase (se 2 (by rfl) ⟨82395, by rfl⟩ : syracuseStep 219721 = 164791) (by norm_num)
theorem B219757 : Blo 191804 219757 := bbase (se 3 (by rfl) ⟨41204, by rfl⟩ : syracuseStep 219757 = 82409) (by norm_num)
theorem B1235573 : Blo 191804 1235573 := bbase (se 5 (by rfl) ⟨57917, by rfl⟩ : syracuseStep 1235573 = 115835) (by norm_num)
theorem B219793 : Blo 191804 219793 := bbase (se 2 (by rfl) ⟨82422, by rfl⟩ : syracuseStep 219793 = 164845) (by norm_num)
theorem B219829 : Blo 191804 219829 := bbase (se 5 (by rfl) ⟨10304, by rfl⟩ : syracuseStep 219829 = 20609) (by norm_num)
theorem B219865 : Blo 191804 219865 := bbase (se 2 (by rfl) ⟨82449, by rfl⟩ : syracuseStep 219865 = 164899) (by norm_num)
theorem B219901 : Blo 191804 219901 := bbase (se 3 (by rfl) ⟨41231, by rfl⟩ : syracuseStep 219901 = 82463) (by norm_num)
theorem B351005 : Blo 191804 351005 := bbase (se 3 (by rfl) ⟨65813, by rfl⟩ : syracuseStep 351005 = 131627) (by norm_num)
theorem B219937 : Blo 191804 219937 := bbase (se 2 (by rfl) ⟨82476, by rfl⟩ : syracuseStep 219937 = 164953) (by norm_num)
theorem B416573 : Blo 191804 416573 := bbase (se 3 (by rfl) ⟨78107, by rfl⟩ : syracuseStep 416573 = 156215) (by norm_num)
theorem B219973 : Blo 191804 219973 := bbase (se 4 (by rfl) ⟨20622, by rfl⟩ : syracuseStep 219973 = 41245) (by norm_num)
theorem B547685 : Blo 191804 547685 := bbase (se 4 (by rfl) ⟨51345, by rfl⟩ : syracuseStep 547685 = 102691) (by norm_num)
theorem B220009 : Blo 191804 220009 := bbase (se 2 (by rfl) ⟨82503, by rfl⟩ : syracuseStep 220009 = 165007) (by norm_num)
theorem B220045 : Blo 191804 220045 := bbase (se 3 (by rfl) ⟨41258, by rfl⟩ : syracuseStep 220045 = 82517) (by norm_num)
theorem B220081 : Blo 191804 220081 := bbase (se 2 (by rfl) ⟨82530, by rfl⟩ : syracuseStep 220081 = 165061) (by norm_num)
theorem B973781 : Blo 191804 973781 := bbase (se 7 (by rfl) ⟨11411, by rfl⟩ : syracuseStep 973781 = 22823) (by norm_num)
theorem B220117 : Blo 191804 220117 := bbase (se 7 (by rfl) ⟨2579, by rfl⟩ : syracuseStep 220117 = 5159) (by norm_num)
theorem B220153 : Blo 191804 220153 := bbase (se 2 (by rfl) ⟨82557, by rfl⟩ : syracuseStep 220153 = 165115) (by norm_num)
theorem B351253 : Blo 191804 351253 := bbase (se 6 (by rfl) ⟨8232, by rfl⟩ : syracuseStep 351253 = 16465) (by norm_num)
theorem B220189 : Blo 191804 220189 := bbase (se 3 (by rfl) ⟨41285, by rfl⟩ : syracuseStep 220189 = 82571) (by norm_num)
theorem B416821 : Blo 191804 416821 := bbase (se 5 (by rfl) ⟨19538, by rfl⟩ : syracuseStep 416821 = 39077) (by norm_num)
theorem B220225 : Blo 191804 220225 := bbase (se 2 (by rfl) ⟨82584, by rfl⟩ : syracuseStep 220225 = 165169) (by norm_num)
theorem B220261 : Blo 191804 220261 := bbase (se 4 (by rfl) ⟨20649, by rfl⟩ : syracuseStep 220261 = 41299) (by norm_num)
theorem B351469 : Blo 191804 351469 := bbase (se 3 (by rfl) ⟨65900, by rfl⟩ : syracuseStep 351469 = 131801) (by norm_num)
theorem B548117 : Blo 191804 548117 := bbase (se 6 (by rfl) ⟨12846, by rfl⟩ : syracuseStep 548117 = 25693) (by norm_num)
theorem B777701 : Blo 191804 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B351757 : Blo 191804 351757 := bbase (se 3 (by rfl) ⟨65954, by rfl⟩ : syracuseStep 351757 = 131909) (by norm_num)
theorem B417325 : Blo 191804 417325 := bbase (se 3 (by rfl) ⟨78248, by rfl⟩ : syracuseStep 417325 = 156497) (by norm_num)
theorem B1466261 : Blo 191804 1466261 := bbase (se 6 (by rfl) ⟨34365, by rfl⟩ : syracuseStep 1466261 = 68731) (by norm_num)
theorem B548869 : Blo 191804 548869 := bbase (se 4 (by rfl) ⟨51456, by rfl⟩ : syracuseStep 548869 = 102913) (by norm_num)
theorem B352421 : Blo 191804 352421 := bbase (se 4 (by rfl) ⟨33039, by rfl⟩ : syracuseStep 352421 = 66079) (by norm_num)
theorem B254173 : Blo 191804 254173 := bbase (se 3 (by rfl) ⟨47657, by rfl⟩ : syracuseStep 254173 = 95315) (by norm_num)
theorem B975077 : Blo 191804 975077 := bbase (se 4 (by rfl) ⟨91413, by rfl⟩ : syracuseStep 975077 = 182827) (by norm_num)
theorem B680293 : Blo 191804 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B647621 : Blo 191804 647621 := bbase (se 4 (by rfl) ⟨60714, by rfl⟩ : syracuseStep 647621 = 121429) (by norm_num)
theorem B648053 : Blo 191804 648053 := bbase (se 5 (by rfl) ⟨30377, by rfl⟩ : syracuseStep 648053 = 60755) (by norm_num)
theorem B287717 : Blo 191804 287717 := bbase (se 4 (by rfl) ⟨26973, by rfl⟩ : syracuseStep 287717 = 53947) (by norm_num)
theorem B287741 : Blo 191804 287741 := bbase (se 3 (by rfl) ⟨53951, by rfl⟩ : syracuseStep 287741 = 107903) (by norm_num)
theorem B287765 : Blo 191804 287765 := bbase (se 6 (by rfl) ⟨6744, by rfl⟩ : syracuseStep 287765 = 13489) (by norm_num)
theorem B287789 : Blo 191804 287789 := bbase (se 3 (by rfl) ⟨53960, by rfl⟩ : syracuseStep 287789 = 107921) (by norm_num)
theorem B287813 : Blo 191804 287813 := bbase (se 4 (by rfl) ⟨26982, by rfl⟩ : syracuseStep 287813 = 53965) (by norm_num)
theorem B287837 : Blo 191804 287837 := bbase (se 3 (by rfl) ⟨53969, by rfl⟩ : syracuseStep 287837 = 107939) (by norm_num)
theorem B287861 : Blo 191804 287861 := bbase (se 5 (by rfl) ⟨13493, by rfl⟩ : syracuseStep 287861 = 26987) (by norm_num)
theorem B287885 : Blo 191804 287885 := bbase (se 3 (by rfl) ⟨53978, by rfl⟩ : syracuseStep 287885 = 107957) (by norm_num)
theorem B287909 : Blo 191804 287909 := bbase (se 4 (by rfl) ⟨26991, by rfl⟩ : syracuseStep 287909 = 53983) (by norm_num)
theorem B287933 : Blo 191804 287933 := bbase (se 3 (by rfl) ⟨53987, by rfl⟩ : syracuseStep 287933 = 107975) (by norm_num)
theorem B287957 : Blo 191804 287957 := bbase (se 7 (by rfl) ⟨3374, by rfl⟩ : syracuseStep 287957 = 6749) (by norm_num)
theorem B287981 : Blo 191804 287981 := bbase (se 3 (by rfl) ⟨53996, by rfl⟩ : syracuseStep 287981 = 107993) (by norm_num)
theorem B288005 : Blo 191804 288005 := bbase (se 4 (by rfl) ⟨27000, by rfl⟩ : syracuseStep 288005 = 54001) (by norm_num)
theorem B288029 : Blo 191804 288029 := bbase (se 3 (by rfl) ⟨54005, by rfl⟩ : syracuseStep 288029 = 108011) (by norm_num)
theorem B648485 : Blo 191804 648485 := bbase (se 4 (by rfl) ⟨60795, by rfl⟩ : syracuseStep 648485 = 121591) (by norm_num)
theorem B288053 : Blo 191804 288053 := bbase (se 5 (by rfl) ⟨13502, by rfl⟩ : syracuseStep 288053 = 27005) (by norm_num)
theorem B288077 : Blo 191804 288077 := bbase (se 3 (by rfl) ⟨54014, by rfl⟩ : syracuseStep 288077 = 108029) (by norm_num)
theorem B288101 : Blo 191804 288101 := bbase (se 4 (by rfl) ⟨27009, by rfl⟩ : syracuseStep 288101 = 54019) (by norm_num)
theorem B288125 : Blo 191804 288125 := bbase (se 3 (by rfl) ⟨54023, by rfl⟩ : syracuseStep 288125 = 108047) (by norm_num)
theorem B288149 : Blo 191804 288149 := bbase (se 6 (by rfl) ⟨6753, by rfl⟩ : syracuseStep 288149 = 13507) (by norm_num)
theorem B222629 : Blo 191804 222629 := bbase (se 4 (by rfl) ⟨20871, by rfl⟩ : syracuseStep 222629 = 41743) (by norm_num)
theorem B288173 : Blo 191804 288173 := bbase (se 3 (by rfl) ⟨54032, by rfl⟩ : syracuseStep 288173 = 108065) (by norm_num)
theorem B288197 : Blo 191804 288197 := bbase (se 4 (by rfl) ⟨27018, by rfl⟩ : syracuseStep 288197 = 54037) (by norm_num)
theorem B288221 : Blo 191804 288221 := bbase (se 3 (by rfl) ⟨54041, by rfl⟩ : syracuseStep 288221 = 108083) (by norm_num)
theorem B288245 : Blo 191804 288245 := bbase (se 5 (by rfl) ⟨13511, by rfl⟩ : syracuseStep 288245 = 27023) (by norm_num)
theorem B976373 : Blo 191804 976373 := bbase (se 5 (by rfl) ⟨45767, by rfl⟩ : syracuseStep 976373 = 91535) (by norm_num)
theorem B288269 : Blo 191804 288269 := bbase (se 3 (by rfl) ⟨54050, by rfl⟩ : syracuseStep 288269 = 108101) (by norm_num)
theorem B288293 : Blo 191804 288293 := bbase (se 4 (by rfl) ⟨27027, by rfl⟩ : syracuseStep 288293 = 54055) (by norm_num)
theorem B288317 : Blo 191804 288317 := bbase (se 3 (by rfl) ⟨54059, by rfl⟩ : syracuseStep 288317 = 108119) (by norm_num)
theorem B288341 : Blo 191804 288341 := bbase (se 8 (by rfl) ⟨1689, by rfl⟩ : syracuseStep 288341 = 3379) (by norm_num)
theorem B288365 : Blo 191804 288365 := bbase (se 3 (by rfl) ⟨54068, by rfl⟩ : syracuseStep 288365 = 108137) (by norm_num)
theorem B288389 : Blo 191804 288389 := bbase (se 4 (by rfl) ⟨27036, by rfl⟩ : syracuseStep 288389 = 54073) (by norm_num)
theorem B288413 : Blo 191804 288413 := bbase (se 3 (by rfl) ⟨54077, by rfl⟩ : syracuseStep 288413 = 108155) (by norm_num)
theorem B288437 : Blo 191804 288437 := bbase (se 5 (by rfl) ⟨13520, by rfl⟩ : syracuseStep 288437 = 27041) (by norm_num)
theorem B288461 : Blo 191804 288461 := bbase (se 3 (by rfl) ⟨54086, by rfl⟩ : syracuseStep 288461 = 108173) (by norm_num)
theorem B648917 : Blo 191804 648917 := bbase (se 7 (by rfl) ⟨7604, by rfl⟩ : syracuseStep 648917 = 15209) (by norm_num)
theorem B288485 : Blo 191804 288485 := bbase (se 4 (by rfl) ⟨27045, by rfl⟩ : syracuseStep 288485 = 54091) (by norm_num)
theorem B288509 : Blo 191804 288509 := bbase (se 3 (by rfl) ⟨54095, by rfl⟩ : syracuseStep 288509 = 108191) (by norm_num)
theorem B288533 : Blo 191804 288533 := bbase (se 6 (by rfl) ⟨6762, by rfl⟩ : syracuseStep 288533 = 13525) (by norm_num)
theorem B288557 : Blo 191804 288557 := bbase (se 3 (by rfl) ⟨54104, by rfl⟩ : syracuseStep 288557 = 108209) (by norm_num)
theorem B288581 : Blo 191804 288581 := bbase (se 4 (by rfl) ⟨27054, by rfl⟩ : syracuseStep 288581 = 54109) (by norm_num)
theorem B288605 : Blo 191804 288605 := bbase (se 3 (by rfl) ⟨54113, by rfl⟩ : syracuseStep 288605 = 108227) (by norm_num)
theorem B288629 : Blo 191804 288629 := bbase (se 5 (by rfl) ⟨13529, by rfl⟩ : syracuseStep 288629 = 27059) (by norm_num)
theorem B1173365 : Blo 191804 1173365 := bbase (se 5 (by rfl) ⟨55001, by rfl⟩ : syracuseStep 1173365 = 110003) (by norm_num)
theorem B288653 : Blo 191804 288653 := bbase (se 3 (by rfl) ⟨54122, by rfl⟩ : syracuseStep 288653 = 108245) (by norm_num)
theorem B288677 : Blo 191804 288677 := bbase (se 4 (by rfl) ⟨27063, by rfl⟩ : syracuseStep 288677 = 54127) (by norm_num)
theorem B288701 : Blo 191804 288701 := bbase (se 3 (by rfl) ⟨54131, by rfl⟩ : syracuseStep 288701 = 108263) (by norm_num)
theorem B288725 : Blo 191804 288725 := bbase (se 7 (by rfl) ⟨3383, by rfl⟩ : syracuseStep 288725 = 6767) (by norm_num)
theorem B288749 : Blo 191804 288749 := bbase (se 3 (by rfl) ⟨54140, by rfl⟩ : syracuseStep 288749 = 108281) (by norm_num)
theorem B288773 : Blo 191804 288773 := bbase (se 4 (by rfl) ⟨27072, by rfl⟩ : syracuseStep 288773 = 54145) (by norm_num)
theorem B1107989 : Blo 191804 1107989 := bbase (se 6 (by rfl) ⟨25968, by rfl⟩ : syracuseStep 1107989 = 51937) (by norm_num)
theorem B288797 : Blo 191804 288797 := bbase (se 3 (by rfl) ⟨54149, by rfl⟩ : syracuseStep 288797 = 108299) (by norm_num)
theorem B288821 : Blo 191804 288821 := bbase (se 5 (by rfl) ⟨13538, by rfl⟩ : syracuseStep 288821 = 27077) (by norm_num)
theorem B288845 : Blo 191804 288845 := bbase (se 3 (by rfl) ⟨54158, by rfl⟩ : syracuseStep 288845 = 108317) (by norm_num)
theorem B288869 : Blo 191804 288869 := bbase (se 4 (by rfl) ⟨27081, by rfl⟩ : syracuseStep 288869 = 54163) (by norm_num)
theorem B288893 : Blo 191804 288893 := bbase (se 3 (by rfl) ⟨54167, by rfl⟩ : syracuseStep 288893 = 108335) (by norm_num)
theorem B649349 : Blo 191804 649349 := bbase (se 4 (by rfl) ⟨60876, by rfl⟩ : syracuseStep 649349 = 121753) (by norm_num)
theorem B288917 : Blo 191804 288917 := bbase (se 6 (by rfl) ⟨6771, by rfl⟩ : syracuseStep 288917 = 13543) (by norm_num)
theorem B288941 : Blo 191804 288941 := bbase (se 3 (by rfl) ⟨54176, by rfl⟩ : syracuseStep 288941 = 108353) (by norm_num)
theorem B288965 : Blo 191804 288965 := bbase (se 4 (by rfl) ⟨27090, by rfl⟩ : syracuseStep 288965 = 54181) (by norm_num)
theorem B3565781 : Blo 191804 3565781 := bbase (se 7 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 3565781 = 83573) (by norm_num)
theorem B288989 : Blo 191804 288989 := bbase (se 3 (by rfl) ⟨54185, by rfl⟩ : syracuseStep 288989 = 108371) (by norm_num)
theorem B289013 : Blo 191804 289013 := bbase (se 5 (by rfl) ⟨13547, by rfl⟩ : syracuseStep 289013 = 27095) (by norm_num)
theorem B289037 : Blo 191804 289037 := bbase (se 3 (by rfl) ⟨54194, by rfl⟩ : syracuseStep 289037 = 108389) (by norm_num)
theorem B289061 : Blo 191804 289061 := bbase (se 4 (by rfl) ⟨27099, by rfl⟩ : syracuseStep 289061 = 54199) (by norm_num)
theorem B289085 : Blo 191804 289085 := bbase (se 3 (by rfl) ⟨54203, by rfl⟩ : syracuseStep 289085 = 108407) (by norm_num)
theorem B289109 : Blo 191804 289109 := bbase (se 10 (by rfl) ⟨423, by rfl⟩ : syracuseStep 289109 = 847) (by norm_num)
theorem B289133 : Blo 191804 289133 := bbase (se 3 (by rfl) ⟨54212, by rfl⟩ : syracuseStep 289133 = 108425) (by norm_num)
theorem B616837 : Blo 191804 616837 := bbase (se 4 (by rfl) ⟨57828, by rfl⟩ : syracuseStep 616837 = 115657) (by norm_num)
theorem B289157 : Blo 191804 289157 := bbase (se 4 (by rfl) ⟨27108, by rfl⟩ : syracuseStep 289157 = 54217) (by norm_num)
theorem B289181 : Blo 191804 289181 := bbase (se 3 (by rfl) ⟨54221, by rfl⟩ : syracuseStep 289181 = 108443) (by norm_num)
theorem B485797 : Blo 191804 485797 := bbase (se 4 (by rfl) ⟨45543, by rfl⟩ : syracuseStep 485797 = 91087) (by norm_num)
theorem B289205 : Blo 191804 289205 := bbase (se 5 (by rfl) ⟨13556, by rfl⟩ : syracuseStep 289205 = 27113) (by norm_num)
theorem B289229 : Blo 191804 289229 := bbase (se 3 (by rfl) ⟨54230, by rfl⟩ : syracuseStep 289229 = 108461) (by norm_num)
theorem B289253 : Blo 191804 289253 := bbase (se 4 (by rfl) ⟨27117, by rfl⟩ : syracuseStep 289253 = 54235) (by norm_num)
theorem B289277 : Blo 191804 289277 := bbase (se 3 (by rfl) ⟨54239, by rfl⟩ : syracuseStep 289277 = 108479) (by norm_num)
theorem B485909 : Blo 191804 485909 := bbase (se 6 (by rfl) ⟨11388, by rfl⟩ : syracuseStep 485909 = 22777) (by norm_num)
theorem B289301 : Blo 191804 289301 := bbase (se 6 (by rfl) ⟨6780, by rfl⟩ : syracuseStep 289301 = 13561) (by norm_num)
theorem B289325 : Blo 191804 289325 := bbase (se 3 (by rfl) ⟨54248, by rfl⟩ : syracuseStep 289325 = 108497) (by norm_num)
theorem B649781 : Blo 191804 649781 := bbase (se 5 (by rfl) ⟨30458, by rfl⟩ : syracuseStep 649781 = 60917) (by norm_num)
theorem B289349 : Blo 191804 289349 := bbase (se 4 (by rfl) ⟨27126, by rfl⟩ : syracuseStep 289349 = 54253) (by norm_num)
theorem B289373 : Blo 191804 289373 := bbase (se 3 (by rfl) ⟨54257, by rfl⟩ : syracuseStep 289373 = 108515) (by norm_num)
theorem B289397 : Blo 191804 289397 := bbase (se 5 (by rfl) ⟨13565, by rfl⟩ : syracuseStep 289397 = 27131) (by norm_num)
theorem B289421 : Blo 191804 289421 := bbase (se 3 (by rfl) ⟨54266, by rfl⟩ : syracuseStep 289421 = 108533) (by norm_num)
theorem B289445 : Blo 191804 289445 := bbase (se 4 (by rfl) ⟨27135, by rfl⟩ : syracuseStep 289445 = 54271) (by norm_num)
theorem B289469 : Blo 191804 289469 := bbase (se 3 (by rfl) ⟨54275, by rfl⟩ : syracuseStep 289469 = 108551) (by norm_num)
theorem B486101 : Blo 191804 486101 := bbase (se 7 (by rfl) ⟨5696, by rfl⟩ : syracuseStep 486101 = 11393) (by norm_num)
theorem B289493 : Blo 191804 289493 := bbase (se 7 (by rfl) ⟨3392, by rfl⟩ : syracuseStep 289493 = 6785) (by norm_num)
theorem B289517 : Blo 191804 289517 := bbase (se 3 (by rfl) ⟨54284, by rfl⟩ : syracuseStep 289517 = 108569) (by norm_num)
theorem B289541 : Blo 191804 289541 := bbase (se 4 (by rfl) ⟨27144, by rfl⟩ : syracuseStep 289541 = 54289) (by norm_num)
theorem B977669 : Blo 191804 977669 := bbase (se 4 (by rfl) ⟨91656, by rfl⟩ : syracuseStep 977669 = 183313) (by norm_num)
theorem B289565 : Blo 191804 289565 := bbase (se 3 (by rfl) ⟨54293, by rfl⟩ : syracuseStep 289565 = 108587) (by norm_num)
theorem B551717 : Blo 191804 551717 := bbase (se 4 (by rfl) ⟨51723, by rfl⟩ : syracuseStep 551717 = 103447) (by norm_num)
theorem B289589 : Blo 191804 289589 := bbase (se 5 (by rfl) ⟨13574, by rfl⟩ : syracuseStep 289589 = 27149) (by norm_num)
theorem B289613 : Blo 191804 289613 := bbase (se 3 (by rfl) ⟨54302, by rfl⟩ : syracuseStep 289613 = 108605) (by norm_num)
theorem B289637 : Blo 191804 289637 := bbase (se 4 (by rfl) ⟨27153, by rfl⟩ : syracuseStep 289637 = 54307) (by norm_num)
theorem B289661 : Blo 191804 289661 := bbase (se 3 (by rfl) ⟨54311, by rfl⟩ : syracuseStep 289661 = 108623) (by norm_num)
theorem B289685 : Blo 191804 289685 := bbase (se 6 (by rfl) ⟨6789, by rfl⟩ : syracuseStep 289685 = 13579) (by norm_num)
theorem B289709 : Blo 191804 289709 := bbase (se 3 (by rfl) ⟨54320, by rfl⟩ : syracuseStep 289709 = 108641) (by norm_num)
theorem B1043381 : Blo 191804 1043381 := bbase (se 5 (by rfl) ⟨48908, by rfl⟩ : syracuseStep 1043381 = 97817) (by norm_num)
theorem B289733 : Blo 191804 289733 := bbase (se 4 (by rfl) ⟨27162, by rfl⟩ : syracuseStep 289733 = 54325) (by norm_num)
theorem B289757 : Blo 191804 289757 := bbase (se 3 (by rfl) ⟨54329, by rfl⟩ : syracuseStep 289757 = 108659) (by norm_num)
theorem B650213 : Blo 191804 650213 := bbase (se 4 (by rfl) ⟨60957, by rfl⟩ : syracuseStep 650213 = 121915) (by norm_num)
theorem B289781 : Blo 191804 289781 := bbase (se 5 (by rfl) ⟨13583, by rfl⟩ : syracuseStep 289781 = 27167) (by norm_num)
theorem B289805 : Blo 191804 289805 := bbase (se 3 (by rfl) ⟨54338, by rfl⟩ : syracuseStep 289805 = 108677) (by norm_num)
theorem B289829 : Blo 191804 289829 := bbase (se 4 (by rfl) ⟨27171, by rfl⟩ : syracuseStep 289829 = 54343) (by norm_num)
theorem B486445 : Blo 191804 486445 := bbase (se 3 (by rfl) ⟨91208, by rfl⟩ : syracuseStep 486445 = 182417) (by norm_num)
theorem B289853 : Blo 191804 289853 := bbase (se 3 (by rfl) ⟨54347, by rfl⟩ : syracuseStep 289853 = 108695) (by norm_num)
theorem B289877 : Blo 191804 289877 := bbase (se 8 (by rfl) ⟨1698, by rfl⟩ : syracuseStep 289877 = 3397) (by norm_num)
theorem B289901 : Blo 191804 289901 := bbase (se 3 (by rfl) ⟨54356, by rfl⟩ : syracuseStep 289901 = 108713) (by norm_num)
theorem B289925 : Blo 191804 289925 := bbase (se 4 (by rfl) ⟨27180, by rfl⟩ : syracuseStep 289925 = 54361) (by norm_num)
theorem B421013 : Blo 191804 421013 := bbase (se 6 (by rfl) ⟨9867, by rfl⟩ : syracuseStep 421013 = 19735) (by norm_num)
theorem B486557 : Blo 191804 486557 := bbase (se 3 (by rfl) ⟨91229, by rfl⟩ : syracuseStep 486557 = 182459) (by norm_num)
theorem B289949 : Blo 191804 289949 := bbase (se 3 (by rfl) ⟨54365, by rfl⟩ : syracuseStep 289949 = 108731) (by norm_num)
theorem B289973 : Blo 191804 289973 := bbase (se 5 (by rfl) ⟨13592, by rfl⟩ : syracuseStep 289973 = 27185) (by norm_num)
theorem B1109173 : Blo 191804 1109173 := bbase (se 5 (by rfl) ⟨51992, by rfl⟩ : syracuseStep 1109173 = 103985) (by norm_num)
theorem B289997 : Blo 191804 289997 := bbase (se 3 (by rfl) ⟨54374, by rfl⟩ : syracuseStep 289997 = 108749) (by norm_num)
theorem B290021 : Blo 191804 290021 := bbase (se 4 (by rfl) ⟨27189, by rfl⟩ : syracuseStep 290021 = 54379) (by norm_num)
theorem B290045 : Blo 191804 290045 := bbase (se 3 (by rfl) ⟨54383, by rfl⟩ : syracuseStep 290045 = 108767) (by norm_num)
theorem B290069 : Blo 191804 290069 := bbase (se 6 (by rfl) ⟨6798, by rfl⟩ : syracuseStep 290069 = 13597) (by norm_num)
theorem B3534101 : Blo 191804 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B290093 : Blo 191804 290093 := bbase (se 3 (by rfl) ⟨54392, by rfl⟩ : syracuseStep 290093 = 108785) (by norm_num)
theorem B290117 : Blo 191804 290117 := bbase (se 4 (by rfl) ⟨27198, by rfl⟩ : syracuseStep 290117 = 54397) (by norm_num)
theorem B486749 : Blo 191804 486749 := bbase (se 3 (by rfl) ⟨91265, by rfl⟩ : syracuseStep 486749 = 182531) (by norm_num)
theorem B290141 : Blo 191804 290141 := bbase (se 3 (by rfl) ⟨54401, by rfl⟩ : syracuseStep 290141 = 108803) (by norm_num)
theorem B290165 : Blo 191804 290165 := bbase (se 5 (by rfl) ⟨13601, by rfl⟩ : syracuseStep 290165 = 27203) (by norm_num)
theorem B290189 : Blo 191804 290189 := bbase (se 3 (by rfl) ⟨54410, by rfl⟩ : syracuseStep 290189 = 108821) (by norm_num)
theorem B650645 : Blo 191804 650645 := bbase (se 6 (by rfl) ⟨15249, by rfl⟩ : syracuseStep 650645 = 30499) (by norm_num)
theorem B290213 : Blo 191804 290213 := bbase (se 4 (by rfl) ⟨27207, by rfl⟩ : syracuseStep 290213 = 54415) (by norm_num)
theorem B290237 : Blo 191804 290237 := bbase (se 3 (by rfl) ⟨54419, by rfl⟩ : syracuseStep 290237 = 108839) (by norm_num)
theorem B290261 : Blo 191804 290261 := bbase (se 7 (by rfl) ⟨3401, by rfl⟩ : syracuseStep 290261 = 6803) (by norm_num)
theorem B290285 : Blo 191804 290285 := bbase (se 3 (by rfl) ⟨54428, by rfl⟩ : syracuseStep 290285 = 108857) (by norm_num)
theorem B290309 : Blo 191804 290309 := bbase (se 4 (by rfl) ⟨27216, by rfl⟩ : syracuseStep 290309 = 54433) (by norm_num)
theorem B290333 : Blo 191804 290333 := bbase (se 3 (by rfl) ⟨54437, by rfl⟩ : syracuseStep 290333 = 108875) (by norm_num)
theorem B290357 : Blo 191804 290357 := bbase (se 5 (by rfl) ⟨13610, by rfl⟩ : syracuseStep 290357 = 27221) (by norm_num)
theorem B355909 : Blo 191804 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B290381 : Blo 191804 290381 := bbase (se 3 (by rfl) ⟨54446, by rfl⟩ : syracuseStep 290381 = 108893) (by norm_num)
theorem B290405 : Blo 191804 290405 := bbase (se 4 (by rfl) ⟨27225, by rfl⟩ : syracuseStep 290405 = 54451) (by norm_num)
theorem B290429 : Blo 191804 290429 := bbase (se 3 (by rfl) ⟨54455, by rfl⟩ : syracuseStep 290429 = 108911) (by norm_num)
theorem B290453 : Blo 191804 290453 := bbase (se 6 (by rfl) ⟨6807, by rfl⟩ : syracuseStep 290453 = 13615) (by norm_num)
theorem B290477 : Blo 191804 290477 := bbase (se 3 (by rfl) ⟨54464, by rfl⟩ : syracuseStep 290477 = 108929) (by norm_num)
theorem B487093 : Blo 191804 487093 := bbase (se 5 (by rfl) ⟨22832, by rfl⟩ : syracuseStep 487093 = 45665) (by norm_num)
theorem B290501 : Blo 191804 290501 := bbase (se 4 (by rfl) ⟨27234, by rfl⟩ : syracuseStep 290501 = 54469) (by norm_num)
theorem B290525 : Blo 191804 290525 := bbase (se 3 (by rfl) ⟨54473, by rfl⟩ : syracuseStep 290525 = 108947) (by norm_num)
theorem B454373 : Blo 191804 454373 := bbase (se 4 (by rfl) ⟨42597, by rfl⟩ : syracuseStep 454373 = 85195) (by norm_num)
theorem B290549 : Blo 191804 290549 := bbase (se 5 (by rfl) ⟨13619, by rfl⟩ : syracuseStep 290549 = 27239) (by norm_num)
theorem B290573 : Blo 191804 290573 := bbase (se 3 (by rfl) ⟨54482, by rfl⟩ : syracuseStep 290573 = 108965) (by norm_num)
theorem B487205 : Blo 191804 487205 := bbase (se 4 (by rfl) ⟨45675, by rfl⟩ : syracuseStep 487205 = 91351) (by norm_num)
theorem B290597 : Blo 191804 290597 := bbase (se 4 (by rfl) ⟨27243, by rfl⟩ : syracuseStep 290597 = 54487) (by norm_num)
theorem B290621 : Blo 191804 290621 := bbase (se 3 (by rfl) ⟨54491, by rfl⟩ : syracuseStep 290621 = 108983) (by norm_num)
theorem B651077 : Blo 191804 651077 := bbase (se 4 (by rfl) ⟨61038, by rfl⟩ : syracuseStep 651077 = 122077) (by norm_num)
theorem B290645 : Blo 191804 290645 := bbase (se 9 (by rfl) ⟨851, by rfl⟩ : syracuseStep 290645 = 1703) (by norm_num)
theorem B290669 : Blo 191804 290669 := bbase (se 3 (by rfl) ⟨54500, by rfl⟩ : syracuseStep 290669 = 109001) (by norm_num)
theorem B290693 : Blo 191804 290693 := bbase (se 4 (by rfl) ⟨27252, by rfl⟩ : syracuseStep 290693 = 54505) (by norm_num)
theorem B1044373 : Blo 191804 1044373 := bbase (se 6 (by rfl) ⟨24477, by rfl⟩ : syracuseStep 1044373 = 48955) (by norm_num)
theorem B290717 : Blo 191804 290717 := bbase (se 3 (by rfl) ⟨54509, by rfl⟩ : syracuseStep 290717 = 109019) (by norm_num)
theorem B290741 : Blo 191804 290741 := bbase (se 5 (by rfl) ⟨13628, by rfl⟩ : syracuseStep 290741 = 27257) (by norm_num)
theorem B552901 : Blo 191804 552901 := bbase (se 4 (by rfl) ⟨51834, by rfl⟩ : syracuseStep 552901 = 103669) (by norm_num)
theorem B290765 : Blo 191804 290765 := bbase (se 3 (by rfl) ⟨54518, by rfl⟩ : syracuseStep 290765 = 109037) (by norm_num)
theorem B487397 : Blo 191804 487397 := bbase (se 4 (by rfl) ⟨45693, by rfl⟩ : syracuseStep 487397 = 91387) (by norm_num)
theorem B290789 : Blo 191804 290789 := bbase (se 4 (by rfl) ⟨27261, by rfl⟩ : syracuseStep 290789 = 54523) (by norm_num)
theorem B290813 : Blo 191804 290813 := bbase (se 3 (by rfl) ⟨54527, by rfl⟩ : syracuseStep 290813 = 109055) (by norm_num)
theorem B978965 : Blo 191804 978965 := bbase (se 6 (by rfl) ⟨22944, by rfl⟩ : syracuseStep 978965 = 45889) (by norm_num)
theorem B290837 : Blo 191804 290837 := bbase (se 6 (by rfl) ⟨6816, by rfl⟩ : syracuseStep 290837 = 13633) (by norm_num)
theorem B290861 : Blo 191804 290861 := bbase (se 3 (by rfl) ⟨54536, by rfl⟩ : syracuseStep 290861 = 109073) (by norm_num)
theorem B290885 : Blo 191804 290885 := bbase (se 4 (by rfl) ⟨27270, by rfl⟩ : syracuseStep 290885 = 54541) (by norm_num)
theorem B290909 : Blo 191804 290909 := bbase (se 3 (by rfl) ⟨54545, by rfl⟩ : syracuseStep 290909 = 109091) (by norm_num)
theorem B553061 : Blo 191804 553061 := bbase (se 4 (by rfl) ⟨51849, by rfl⟩ : syracuseStep 553061 = 103699) (by norm_num)
theorem B290933 : Blo 191804 290933 := bbase (se 5 (by rfl) ⟨13637, by rfl⟩ : syracuseStep 290933 = 27275) (by norm_num)
theorem B290957 : Blo 191804 290957 := bbase (se 3 (by rfl) ⟨54554, by rfl⟩ : syracuseStep 290957 = 109109) (by norm_num)
theorem B290981 : Blo 191804 290981 := bbase (se 4 (by rfl) ⟨27279, by rfl⟩ : syracuseStep 290981 = 54559) (by norm_num)
theorem B291005 : Blo 191804 291005 := bbase (se 3 (by rfl) ⟨54563, by rfl⟩ : syracuseStep 291005 = 109127) (by norm_num)
theorem B323797 : Blo 191804 323797 := bbase (se 7 (by rfl) ⟨3794, by rfl⟩ : syracuseStep 323797 = 7589) (by norm_num)
theorem B291029 : Blo 191804 291029 := bbase (se 7 (by rfl) ⟨3410, by rfl⟩ : syracuseStep 291029 = 6821) (by norm_num)
theorem B291053 : Blo 191804 291053 := bbase (se 3 (by rfl) ⟨54572, by rfl⟩ : syracuseStep 291053 = 109145) (by norm_num)
theorem B651509 : Blo 191804 651509 := bbase (se 5 (by rfl) ⟨30539, by rfl⟩ : syracuseStep 651509 = 61079) (by norm_num)
theorem B291077 : Blo 191804 291077 := bbase (se 4 (by rfl) ⟨27288, by rfl⟩ : syracuseStep 291077 = 54577) (by norm_num)
theorem B291101 : Blo 191804 291101 := bbase (se 3 (by rfl) ⟨54581, by rfl⟩ : syracuseStep 291101 = 109163) (by norm_num)
theorem B323885 : Blo 191804 323885 := bbase (se 3 (by rfl) ⟨60728, by rfl⟩ : syracuseStep 323885 = 121457) (by norm_num)
theorem B520501 : Blo 191804 520501 := bbase (se 5 (by rfl) ⟨24398, by rfl⟩ : syracuseStep 520501 = 48797) (by norm_num)
theorem B291125 : Blo 191804 291125 := bbase (se 5 (by rfl) ⟨13646, by rfl⟩ : syracuseStep 291125 = 27293) (by norm_num)
theorem B487741 : Blo 191804 487741 := bbase (se 3 (by rfl) ⟨91451, by rfl⟩ : syracuseStep 487741 = 182903) (by norm_num)
theorem B291149 : Blo 191804 291149 := bbase (se 3 (by rfl) ⟨54590, by rfl⟩ : syracuseStep 291149 = 109181) (by norm_num)
theorem B553301 : Blo 191804 553301 := bbase (se 10 (by rfl) ⟨810, by rfl⟩ : syracuseStep 553301 = 1621) (by norm_num)
theorem B291173 : Blo 191804 291173 := bbase (se 4 (by rfl) ⟨27297, by rfl⟩ : syracuseStep 291173 = 54595) (by norm_num)
theorem B291197 : Blo 191804 291197 := bbase (se 3 (by rfl) ⟨54599, by rfl⟩ : syracuseStep 291197 = 109199) (by norm_num)
theorem B291221 : Blo 191804 291221 := bbase (se 6 (by rfl) ⟨6825, by rfl⟩ : syracuseStep 291221 = 13651) (by norm_num)
theorem B422309 : Blo 191804 422309 := bbase (se 4 (by rfl) ⟨39591, by rfl⟩ : syracuseStep 422309 = 79183) (by norm_num)
theorem B324013 : Blo 191804 324013 := bbase (se 3 (by rfl) ⟨60752, by rfl⟩ : syracuseStep 324013 = 121505) (by norm_num)
theorem B487853 : Blo 191804 487853 := bbase (se 3 (by rfl) ⟨91472, by rfl⟩ : syracuseStep 487853 = 182945) (by norm_num)
theorem B291245 : Blo 191804 291245 := bbase (se 3 (by rfl) ⟨54608, by rfl⟩ : syracuseStep 291245 = 109217) (by norm_num)
theorem B389557 : Blo 191804 389557 := bbase (se 5 (by rfl) ⟨18260, by rfl⟩ : syracuseStep 389557 = 36521) (by norm_num)
theorem B291269 : Blo 191804 291269 := bbase (se 4 (by rfl) ⟨27306, by rfl⟩ : syracuseStep 291269 = 54613) (by norm_num)
theorem B291293 : Blo 191804 291293 := bbase (se 3 (by rfl) ⟨54617, by rfl⟩ : syracuseStep 291293 = 109235) (by norm_num)
theorem B291317 : Blo 191804 291317 := bbase (se 5 (by rfl) ⟨13655, by rfl⟩ : syracuseStep 291317 = 27311) (by norm_num)
theorem B324101 : Blo 191804 324101 := bbase (se 4 (by rfl) ⟨30384, by rfl⟩ : syracuseStep 324101 = 60769) (by norm_num)
theorem B291341 : Blo 191804 291341 := bbase (se 3 (by rfl) ⟨54626, by rfl⟩ : syracuseStep 291341 = 109253) (by norm_num)
theorem B553493 : Blo 191804 553493 := bbase (se 6 (by rfl) ⟨12972, by rfl⟩ : syracuseStep 553493 = 25945) (by norm_num)
theorem B291365 : Blo 191804 291365 := bbase (se 4 (by rfl) ⟨27315, by rfl⟩ : syracuseStep 291365 = 54631) (by norm_num)
theorem B291389 : Blo 191804 291389 := bbase (se 3 (by rfl) ⟨54635, by rfl⟩ : syracuseStep 291389 = 109271) (by norm_num)
theorem B291413 : Blo 191804 291413 := bbase (se 8 (by rfl) ⟨1707, by rfl⟩ : syracuseStep 291413 = 3415) (by norm_num)
theorem B488045 : Blo 191804 488045 := bbase (se 3 (by rfl) ⟨91508, by rfl⟩ : syracuseStep 488045 = 183017) (by norm_num)
theorem B291437 : Blo 191804 291437 := bbase (se 3 (by rfl) ⟨54644, by rfl⟩ : syracuseStep 291437 = 109289) (by norm_num)
theorem B324229 : Blo 191804 324229 := bbase (se 4 (by rfl) ⟨30396, by rfl⟩ : syracuseStep 324229 = 60793) (by norm_num)
theorem B291461 : Blo 191804 291461 := bbase (se 4 (by rfl) ⟨27324, by rfl⟩ : syracuseStep 291461 = 54649) (by norm_num)
theorem B291485 : Blo 191804 291485 := bbase (se 3 (by rfl) ⟨54653, by rfl⟩ : syracuseStep 291485 = 109307) (by norm_num)
theorem B651941 : Blo 191804 651941 := bbase (se 4 (by rfl) ⟨61119, by rfl⟩ : syracuseStep 651941 = 122239) (by norm_num)
theorem B291509 : Blo 191804 291509 := bbase (se 5 (by rfl) ⟨13664, by rfl⟩ : syracuseStep 291509 = 27329) (by norm_num)
theorem B291533 : Blo 191804 291533 := bbase (se 3 (by rfl) ⟨54662, by rfl⟩ : syracuseStep 291533 = 109325) (by norm_num)
theorem B324317 : Blo 191804 324317 := bbase (se 3 (by rfl) ⟨60809, by rfl⟩ : syracuseStep 324317 = 121619) (by norm_num)
theorem B291557 : Blo 191804 291557 := bbase (se 4 (by rfl) ⟨27333, by rfl⟩ : syracuseStep 291557 = 54667) (by norm_num)
theorem B291581 : Blo 191804 291581 := bbase (se 3 (by rfl) ⟨54671, by rfl⟩ : syracuseStep 291581 = 109343) (by norm_num)
theorem B291605 : Blo 191804 291605 := bbase (se 6 (by rfl) ⟨6834, by rfl⟩ : syracuseStep 291605 = 13669) (by norm_num)
theorem B1667861 : Blo 191804 1667861 := bbase (se 6 (by rfl) ⟨39090, by rfl⟩ : syracuseStep 1667861 = 78181) (by norm_num)
theorem B291629 : Blo 191804 291629 := bbase (se 3 (by rfl) ⟨54680, by rfl⟩ : syracuseStep 291629 = 109361) (by norm_num)
theorem B750389 : Blo 191804 750389 := bbase (se 5 (by rfl) ⟨35174, by rfl⟩ : syracuseStep 750389 = 70349) (by norm_num)
theorem B291653 : Blo 191804 291653 := bbase (se 4 (by rfl) ⟨27342, by rfl⟩ : syracuseStep 291653 = 54685) (by norm_num)
theorem B324445 : Blo 191804 324445 := bbase (se 3 (by rfl) ⟨60833, by rfl⟩ : syracuseStep 324445 = 121667) (by norm_num)
theorem B291677 : Blo 191804 291677 := bbase (se 3 (by rfl) ⟨54689, by rfl⟩ : syracuseStep 291677 = 109379) (by norm_num)
theorem B291701 : Blo 191804 291701 := bbase (se 5 (by rfl) ⟨13673, by rfl⟩ : syracuseStep 291701 = 27347) (by norm_num)
theorem B291725 : Blo 191804 291725 := bbase (se 3 (by rfl) ⟨54698, by rfl⟩ : syracuseStep 291725 = 109397) (by norm_num)
theorem B291749 : Blo 191804 291749 := bbase (se 4 (by rfl) ⟨27351, by rfl⟩ : syracuseStep 291749 = 54703) (by norm_num)
theorem B324533 : Blo 191804 324533 := bbase (se 5 (by rfl) ⟨15212, by rfl⟩ : syracuseStep 324533 = 30425) (by norm_num)
theorem B291773 : Blo 191804 291773 := bbase (se 3 (by rfl) ⟨54707, by rfl⟩ : syracuseStep 291773 = 109415) (by norm_num)
theorem B488389 : Blo 191804 488389 := bbase (se 4 (by rfl) ⟨45786, by rfl⟩ : syracuseStep 488389 = 91573) (by norm_num)
theorem B291797 : Blo 191804 291797 := bbase (se 7 (by rfl) ⟨3419, by rfl⟩ : syracuseStep 291797 = 6839) (by norm_num)
theorem B291821 : Blo 191804 291821 := bbase (se 3 (by rfl) ⟨54716, by rfl⟩ : syracuseStep 291821 = 109433) (by norm_num)
theorem B291845 : Blo 191804 291845 := bbase (se 4 (by rfl) ⟨27360, by rfl⟩ : syracuseStep 291845 = 54721) (by norm_num)
theorem B291869 : Blo 191804 291869 := bbase (se 3 (by rfl) ⟨54725, by rfl⟩ : syracuseStep 291869 = 109451) (by norm_num)
theorem B324661 : Blo 191804 324661 := bbase (se 5 (by rfl) ⟨15218, by rfl⟩ : syracuseStep 324661 = 30437) (by norm_num)
theorem B488501 : Blo 191804 488501 := bbase (se 5 (by rfl) ⟨22898, by rfl⟩ : syracuseStep 488501 = 45797) (by norm_num)
theorem B291893 : Blo 191804 291893 := bbase (se 5 (by rfl) ⟨13682, by rfl⟩ : syracuseStep 291893 = 27365) (by norm_num)
theorem B291917 : Blo 191804 291917 := bbase (se 3 (by rfl) ⟨54734, by rfl⟩ : syracuseStep 291917 = 109469) (by norm_num)
theorem B652373 : Blo 191804 652373 := bbase (se 8 (by rfl) ⟨3822, by rfl⟩ : syracuseStep 652373 = 7645) (by norm_num)
theorem B291941 : Blo 191804 291941 := bbase (se 4 (by rfl) ⟨27369, by rfl⟩ : syracuseStep 291941 = 54739) (by norm_num)
theorem B1111157 : Blo 191804 1111157 := bbase (se 5 (by rfl) ⟨52085, by rfl⟩ : syracuseStep 1111157 = 104171) (by norm_num)
theorem B291965 : Blo 191804 291965 := bbase (se 3 (by rfl) ⟨54743, by rfl⟩ : syracuseStep 291965 = 109487) (by norm_num)
theorem B324749 : Blo 191804 324749 := bbase (se 3 (by rfl) ⟨60890, by rfl⟩ : syracuseStep 324749 = 121781) (by norm_num)
theorem B291989 : Blo 191804 291989 := bbase (se 6 (by rfl) ⟨6843, by rfl⟩ : syracuseStep 291989 = 13687) (by norm_num)
theorem B292013 : Blo 191804 292013 := bbase (se 3 (by rfl) ⟨54752, by rfl⟩ : syracuseStep 292013 = 109505) (by norm_num)
theorem B292037 : Blo 191804 292037 := bbase (se 4 (by rfl) ⟨27378, by rfl⟩ : syracuseStep 292037 = 54757) (by norm_num)
theorem B292061 : Blo 191804 292061 := bbase (se 3 (by rfl) ⟨54761, by rfl⟩ : syracuseStep 292061 = 109523) (by norm_num)
theorem B292085 : Blo 191804 292085 := bbase (se 5 (by rfl) ⟨13691, by rfl⟩ : syracuseStep 292085 = 27383) (by norm_num)
theorem B488693 : Blo 191804 488693 := bbase (se 5 (by rfl) ⟨22907, by rfl⟩ : syracuseStep 488693 = 45815) (by norm_num)
theorem B324877 : Blo 191804 324877 := bbase (se 3 (by rfl) ⟨60914, by rfl⟩ : syracuseStep 324877 = 121829) (by norm_num)
theorem B292109 : Blo 191804 292109 := bbase (se 3 (by rfl) ⟨54770, by rfl⟩ : syracuseStep 292109 = 109541) (by norm_num)
theorem B980261 : Blo 191804 980261 := bbase (se 4 (by rfl) ⟨91899, by rfl⟩ : syracuseStep 980261 = 183799) (by norm_num)
theorem B292133 : Blo 191804 292133 := bbase (se 4 (by rfl) ⟨27387, by rfl⟩ : syracuseStep 292133 = 54775) (by norm_num)
theorem B292157 : Blo 191804 292157 := bbase (se 3 (by rfl) ⟨54779, by rfl⟩ : syracuseStep 292157 = 109559) (by norm_num)
theorem B292181 : Blo 191804 292181 := bbase (se 13 (by rfl) ⟨53, by rfl⟩ : syracuseStep 292181 = 107) (by norm_num)
theorem B324965 : Blo 191804 324965 := bbase (se 4 (by rfl) ⟨30465, by rfl⟩ : syracuseStep 324965 = 60931) (by norm_num)
theorem B292205 : Blo 191804 292205 := bbase (se 3 (by rfl) ⟨54788, by rfl⟩ : syracuseStep 292205 = 109577) (by norm_num)
theorem B292229 : Blo 191804 292229 := bbase (se 4 (by rfl) ⟨27396, by rfl⟩ : syracuseStep 292229 = 54793) (by norm_num)
theorem B292253 : Blo 191804 292253 := bbase (se 3 (by rfl) ⟨54797, by rfl⟩ : syracuseStep 292253 = 109595) (by norm_num)
theorem B292277 : Blo 191804 292277 := bbase (se 5 (by rfl) ⟨13700, by rfl⟩ : syracuseStep 292277 = 27401) (by norm_num)
theorem B292301 : Blo 191804 292301 := bbase (se 3 (by rfl) ⟨54806, by rfl⟩ : syracuseStep 292301 = 109613) (by norm_num)
theorem B325093 : Blo 191804 325093 := bbase (se 4 (by rfl) ⟨30477, by rfl⟩ : syracuseStep 325093 = 60955) (by norm_num)
theorem B292325 : Blo 191804 292325 := bbase (se 4 (by rfl) ⟨27405, by rfl⟩ : syracuseStep 292325 = 54811) (by norm_num)
theorem B554485 : Blo 191804 554485 := bbase (se 5 (by rfl) ⟨25991, by rfl⟩ : syracuseStep 554485 = 51983) (by norm_num)
theorem B292349 : Blo 191804 292349 := bbase (se 3 (by rfl) ⟨54815, by rfl⟩ : syracuseStep 292349 = 109631) (by norm_num)
theorem B652805 : Blo 191804 652805 := bbase (se 4 (by rfl) ⟨61200, by rfl⟩ : syracuseStep 652805 = 122401) (by norm_num)
theorem B292373 : Blo 191804 292373 := bbase (se 6 (by rfl) ⟨6852, by rfl⟩ : syracuseStep 292373 = 13705) (by norm_num)
theorem B751141 : Blo 191804 751141 := bbase (se 4 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 751141 = 140839) (by norm_num)
theorem B292397 : Blo 191804 292397 := bbase (se 3 (by rfl) ⟨54824, by rfl⟩ : syracuseStep 292397 = 109649) (by norm_num)
theorem B325181 : Blo 191804 325181 := bbase (se 3 (by rfl) ⟨60971, by rfl⟩ : syracuseStep 325181 = 121943) (by norm_num)
theorem B292421 : Blo 191804 292421 := bbase (se 4 (by rfl) ⟨27414, by rfl⟩ : syracuseStep 292421 = 54829) (by norm_num)
theorem B489037 : Blo 191804 489037 := bbase (se 3 (by rfl) ⟨91694, by rfl⟩ : syracuseStep 489037 = 183389) (by norm_num)
theorem B292445 : Blo 191804 292445 := bbase (se 3 (by rfl) ⟨54833, by rfl⟩ : syracuseStep 292445 = 109667) (by norm_num)
theorem B292469 : Blo 191804 292469 := bbase (se 5 (by rfl) ⟨13709, by rfl⟩ : syracuseStep 292469 = 27419) (by norm_num)
theorem B292493 : Blo 191804 292493 := bbase (se 3 (by rfl) ⟨54842, by rfl⟩ : syracuseStep 292493 = 109685) (by norm_num)
theorem B292517 : Blo 191804 292517 := bbase (se 4 (by rfl) ⟨27423, by rfl⟩ : syracuseStep 292517 = 54847) (by norm_num)
theorem B325309 : Blo 191804 325309 := bbase (se 3 (by rfl) ⟨60995, by rfl⟩ : syracuseStep 325309 = 121991) (by norm_num)
theorem B489149 : Blo 191804 489149 := bbase (se 3 (by rfl) ⟨91715, by rfl⟩ : syracuseStep 489149 = 183431) (by norm_num)
theorem B292541 : Blo 191804 292541 := bbase (se 3 (by rfl) ⟨54851, by rfl⟩ : syracuseStep 292541 = 109703) (by norm_num)
theorem B1865429 : Blo 191804 1865429 := bbase (se 7 (by rfl) ⟨21860, by rfl⟩ : syracuseStep 1865429 = 43721) (by norm_num)
theorem B292565 : Blo 191804 292565 := bbase (se 7 (by rfl) ⟨3428, by rfl⟩ : syracuseStep 292565 = 6857) (by norm_num)
theorem B292589 : Blo 191804 292589 := bbase (se 3 (by rfl) ⟨54860, by rfl⟩ : syracuseStep 292589 = 109721) (by norm_num)
theorem B292613 : Blo 191804 292613 := bbase (se 4 (by rfl) ⟨27432, by rfl⟩ : syracuseStep 292613 = 54865) (by norm_num)
theorem B325397 : Blo 191804 325397 := bbase (se 6 (by rfl) ⟨7626, by rfl⟩ : syracuseStep 325397 = 15253) (by norm_num)
theorem B292637 : Blo 191804 292637 := bbase (se 3 (by rfl) ⟨54869, by rfl⟩ : syracuseStep 292637 = 109739) (by norm_num)
theorem B587557 : Blo 191804 587557 := bbase (se 4 (by rfl) ⟨55083, by rfl⟩ : syracuseStep 587557 = 110167) (by norm_num)
theorem B292661 : Blo 191804 292661 := bbase (se 5 (by rfl) ⟨13718, by rfl⟩ : syracuseStep 292661 = 27437) (by norm_num)
theorem B292685 : Blo 191804 292685 := bbase (se 3 (by rfl) ⟨54878, by rfl⟩ : syracuseStep 292685 = 109757) (by norm_num)
theorem B292709 : Blo 191804 292709 := bbase (se 4 (by rfl) ⟨27441, by rfl⟩ : syracuseStep 292709 = 54883) (by norm_num)
theorem B489341 : Blo 191804 489341 := bbase (se 3 (by rfl) ⟨91751, by rfl⟩ : syracuseStep 489341 = 183503) (by norm_num)
theorem B292733 : Blo 191804 292733 := bbase (se 3 (by rfl) ⟨54887, by rfl⟩ : syracuseStep 292733 = 109775) (by norm_num)
theorem B325525 : Blo 191804 325525 := bbase (se 6 (by rfl) ⟨7629, by rfl⟩ : syracuseStep 325525 = 15259) (by norm_num)
theorem B292757 : Blo 191804 292757 := bbase (se 6 (by rfl) ⟨6861, by rfl⟩ : syracuseStep 292757 = 13723) (by norm_num)
theorem B292781 : Blo 191804 292781 := bbase (se 3 (by rfl) ⟨54896, by rfl⟩ : syracuseStep 292781 = 109793) (by norm_num)
theorem B653237 : Blo 191804 653237 := bbase (se 5 (by rfl) ⟨30620, by rfl⟩ : syracuseStep 653237 = 61241) (by norm_num)
theorem B292805 : Blo 191804 292805 := bbase (se 4 (by rfl) ⟨27450, by rfl⟩ : syracuseStep 292805 = 54901) (by norm_num)
theorem B292829 : Blo 191804 292829 := bbase (se 3 (by rfl) ⟨54905, by rfl⟩ : syracuseStep 292829 = 109811) (by norm_num)
theorem B325613 : Blo 191804 325613 := bbase (se 3 (by rfl) ⟨61052, by rfl⟩ : syracuseStep 325613 = 122105) (by norm_num)
theorem B292853 : Blo 191804 292853 := bbase (se 5 (by rfl) ⟨13727, by rfl⟩ : syracuseStep 292853 = 27455) (by norm_num)
theorem B292877 : Blo 191804 292877 := bbase (se 3 (by rfl) ⟨54914, by rfl⟩ : syracuseStep 292877 = 109829) (by norm_num)
theorem B292901 : Blo 191804 292901 := bbase (se 4 (by rfl) ⟨27459, by rfl⟩ : syracuseStep 292901 = 54919) (by norm_num)
theorem B292925 : Blo 191804 292925 := bbase (se 3 (by rfl) ⟨54923, by rfl⟩ : syracuseStep 292925 = 109847) (by norm_num)
theorem B292949 : Blo 191804 292949 := bbase (se 8 (by rfl) ⟨1716, by rfl⟩ : syracuseStep 292949 = 3433) (by norm_num)
theorem B194653 : Blo 191804 194653 := bbase (se 3 (by rfl) ⟨36497, by rfl⟩ : syracuseStep 194653 = 72995) (by norm_num)
theorem B325741 : Blo 191804 325741 := bbase (se 3 (by rfl) ⟨61076, by rfl⟩ : syracuseStep 325741 = 122153) (by norm_num)
theorem B292973 : Blo 191804 292973 := bbase (se 3 (by rfl) ⟨54932, by rfl⟩ : syracuseStep 292973 = 109865) (by norm_num)
theorem B292997 : Blo 191804 292997 := bbase (se 4 (by rfl) ⟨27468, by rfl⟩ : syracuseStep 292997 = 54937) (by norm_num)
theorem B293021 : Blo 191804 293021 := bbase (se 3 (by rfl) ⟨54941, by rfl⟩ : syracuseStep 293021 = 109883) (by norm_num)
theorem B293045 : Blo 191804 293045 := bbase (se 5 (by rfl) ⟨13736, by rfl⟩ : syracuseStep 293045 = 27473) (by norm_num)
theorem B325829 : Blo 191804 325829 := bbase (se 4 (by rfl) ⟨30546, by rfl⟩ : syracuseStep 325829 = 61093) (by norm_num)
theorem B293069 : Blo 191804 293069 := bbase (se 3 (by rfl) ⟨54950, by rfl⟩ : syracuseStep 293069 = 109901) (by norm_num)
theorem B489685 : Blo 191804 489685 := bbase (se 7 (by rfl) ⟨5738, by rfl⟩ : syracuseStep 489685 = 11477) (by norm_num)
theorem B293093 : Blo 191804 293093 := bbase (se 4 (by rfl) ⟨27477, by rfl⟩ : syracuseStep 293093 = 54955) (by norm_num)
theorem B293117 : Blo 191804 293117 := bbase (se 3 (by rfl) ⟨54959, by rfl⟩ : syracuseStep 293117 = 109919) (by norm_num)
theorem B293141 : Blo 191804 293141 := bbase (se 6 (by rfl) ⟨6870, by rfl⟩ : syracuseStep 293141 = 13741) (by norm_num)
theorem B293165 : Blo 191804 293165 := bbase (se 3 (by rfl) ⟨54968, by rfl⟩ : syracuseStep 293165 = 109937) (by norm_num)
theorem B325957 : Blo 191804 325957 := bbase (se 4 (by rfl) ⟨30558, by rfl⟩ : syracuseStep 325957 = 61117) (by norm_num)
theorem B489797 : Blo 191804 489797 := bbase (se 4 (by rfl) ⟨45918, by rfl⟩ : syracuseStep 489797 = 91837) (by norm_num)
theorem B293189 : Blo 191804 293189 := bbase (se 4 (by rfl) ⟨27486, by rfl⟩ : syracuseStep 293189 = 54973) (by norm_num)
theorem B293213 : Blo 191804 293213 := bbase (se 3 (by rfl) ⟨54977, by rfl⟩ : syracuseStep 293213 = 109955) (by norm_num)
theorem B653669 : Blo 191804 653669 := bbase (se 4 (by rfl) ⟨61281, by rfl⟩ : syracuseStep 653669 = 122563) (by norm_num)
theorem B293237 : Blo 191804 293237 := bbase (se 5 (by rfl) ⟨13745, by rfl⟩ : syracuseStep 293237 = 27491) (by norm_num)
theorem B293261 : Blo 191804 293261 := bbase (se 3 (by rfl) ⟨54986, by rfl⟩ : syracuseStep 293261 = 109973) (by norm_num)
theorem B326045 : Blo 191804 326045 := bbase (se 3 (by rfl) ⟨61133, by rfl⟩ : syracuseStep 326045 = 122267) (by norm_num)
theorem B293285 : Blo 191804 293285 := bbase (se 4 (by rfl) ⟨27495, by rfl⟩ : syracuseStep 293285 = 54991) (by norm_num)
theorem B1800629 : Blo 191804 1800629 := bbase (se 5 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 1800629 = 168809) (by norm_num)
theorem B293309 : Blo 191804 293309 := bbase (se 3 (by rfl) ⟨54995, by rfl⟩ : syracuseStep 293309 = 109991) (by norm_num)
theorem B784837 : Blo 191804 784837 := bbase (se 4 (by rfl) ⟨73578, by rfl⟩ : syracuseStep 784837 = 147157) (by norm_num)
theorem B293333 : Blo 191804 293333 := bbase (se 7 (by rfl) ⟨3437, by rfl⟩ : syracuseStep 293333 = 6875) (by norm_num)
theorem B293357 : Blo 191804 293357 := bbase (se 3 (by rfl) ⟨55004, by rfl⟩ : syracuseStep 293357 = 110009) (by norm_num)
theorem B260597 : Blo 191804 260597 := bbase (se 5 (by rfl) ⟨12215, by rfl⟩ : syracuseStep 260597 = 24431) (by norm_num)
theorem B489989 : Blo 191804 489989 := bbase (se 4 (by rfl) ⟨45936, by rfl⟩ : syracuseStep 489989 = 91873) (by norm_num)
theorem B293381 : Blo 191804 293381 := bbase (se 4 (by rfl) ⟨27504, by rfl⟩ : syracuseStep 293381 = 55009) (by norm_num)
theorem B326173 : Blo 191804 326173 := bbase (se 3 (by rfl) ⟨61157, by rfl⟩ : syracuseStep 326173 = 122315) (by norm_num)
theorem B293405 : Blo 191804 293405 := bbase (se 3 (by rfl) ⟨55013, by rfl⟩ : syracuseStep 293405 = 110027) (by norm_num)
theorem B981557 : Blo 191804 981557 := bbase (se 5 (by rfl) ⟨46010, by rfl⟩ : syracuseStep 981557 = 92021) (by norm_num)
theorem B293429 : Blo 191804 293429 := bbase (se 5 (by rfl) ⟨13754, by rfl⟩ : syracuseStep 293429 = 27509) (by norm_num)
theorem B555589 : Blo 191804 555589 := bbase (se 4 (by rfl) ⟨52086, by rfl⟩ : syracuseStep 555589 = 104173) (by norm_num)
theorem B293453 : Blo 191804 293453 := bbase (se 3 (by rfl) ⟨55022, by rfl⟩ : syracuseStep 293453 = 110045) (by norm_num)
theorem B293477 : Blo 191804 293477 := bbase (se 4 (by rfl) ⟨27513, by rfl⟩ : syracuseStep 293477 = 55027) (by norm_num)
theorem B326261 : Blo 191804 326261 := bbase (se 5 (by rfl) ⟨15293, by rfl⟩ : syracuseStep 326261 = 30587) (by norm_num)
theorem B293501 : Blo 191804 293501 := bbase (se 3 (by rfl) ⟨55031, by rfl⟩ : syracuseStep 293501 = 110063) (by norm_num)
theorem B293525 : Blo 191804 293525 := bbase (se 6 (by rfl) ⟨6879, by rfl⟩ : syracuseStep 293525 = 13759) (by norm_num)
theorem B293549 : Blo 191804 293549 := bbase (se 3 (by rfl) ⟨55040, by rfl⟩ : syracuseStep 293549 = 110081) (by norm_num)
theorem B293573 : Blo 191804 293573 := bbase (se 4 (by rfl) ⟨27522, by rfl⟩ : syracuseStep 293573 = 55045) (by norm_num)
theorem B522965 : Blo 191804 522965 := bbase (se 7 (by rfl) ⟨6128, by rfl⟩ : syracuseStep 522965 = 12257) (by norm_num)
theorem B293597 : Blo 191804 293597 := bbase (se 3 (by rfl) ⟨55049, by rfl⟩ : syracuseStep 293597 = 110099) (by norm_num)
theorem B326389 : Blo 191804 326389 := bbase (se 5 (by rfl) ⟨15299, by rfl⟩ : syracuseStep 326389 = 30599) (by norm_num)
theorem B293621 : Blo 191804 293621 := bbase (se 5 (by rfl) ⟨13763, by rfl⟩ : syracuseStep 293621 = 27527) (by norm_num)
theorem B293645 : Blo 191804 293645 := bbase (se 3 (by rfl) ⟨55058, by rfl⟩ : syracuseStep 293645 = 110117) (by norm_num)
theorem B654101 : Blo 191804 654101 := bbase (se 6 (by rfl) ⟨15330, by rfl⟩ : syracuseStep 654101 = 30661) (by norm_num)
theorem B293669 : Blo 191804 293669 := bbase (se 4 (by rfl) ⟨27531, by rfl⟩ : syracuseStep 293669 = 55063) (by norm_num)
theorem B293693 : Blo 191804 293693 := bbase (se 3 (by rfl) ⟨55067, by rfl⟩ : syracuseStep 293693 = 110135) (by norm_num)
theorem B326477 : Blo 191804 326477 := bbase (se 3 (by rfl) ⟨61214, by rfl⟩ : syracuseStep 326477 = 122429) (by norm_num)
theorem B490333 : Blo 191804 490333 := bbase (se 3 (by rfl) ⟨91937, by rfl⟩ : syracuseStep 490333 = 183875) (by norm_num)
theorem B261029 : Blo 191804 261029 := bbase (se 4 (by rfl) ⟨24471, by rfl⟩ : syracuseStep 261029 = 48943) (by norm_num)
theorem B326605 : Blo 191804 326605 := bbase (se 3 (by rfl) ⟨61238, by rfl⟩ : syracuseStep 326605 = 122477) (by norm_num)
theorem B490445 : Blo 191804 490445 := bbase (se 3 (by rfl) ⟨91958, by rfl⟩ : syracuseStep 490445 = 183917) (by norm_num)
theorem B195593 : Blo 191804 195593 := bbase (se 2 (by rfl) ⟨73347, by rfl⟩ : syracuseStep 195593 = 146695) (by norm_num)
theorem B326693 : Blo 191804 326693 := bbase (se 4 (by rfl) ⟨30627, by rfl⟩ : syracuseStep 326693 = 61255) (by norm_num)
theorem B490637 : Blo 191804 490637 := bbase (se 3 (by rfl) ⟨91994, by rfl⟩ : syracuseStep 490637 = 183989) (by norm_num)
theorem B326821 : Blo 191804 326821 := bbase (se 4 (by rfl) ⟨30639, by rfl⟩ : syracuseStep 326821 = 61279) (by norm_num)
theorem B654533 : Blo 191804 654533 := bbase (se 4 (by rfl) ⟨61362, by rfl⟩ : syracuseStep 654533 = 122725) (by norm_num)
theorem B195809 : Blo 191804 195809 := bbase (se 2 (by rfl) ⟨73428, by rfl⟩ : syracuseStep 195809 = 146857) (by norm_num)
theorem B326909 : Blo 191804 326909 := bbase (se 3 (by rfl) ⟨61295, by rfl⟩ : syracuseStep 326909 = 122591) (by norm_num)
theorem B1113365 : Blo 191804 1113365 := bbase (se 6 (by rfl) ⟨26094, by rfl⟩ : syracuseStep 1113365 = 52189) (by norm_num)
theorem B195901 : Blo 191804 195901 := bbase (se 3 (by rfl) ⟨36731, by rfl⟩ : syracuseStep 195901 = 73463) (by norm_num)
theorem B327037 : Blo 191804 327037 := bbase (se 3 (by rfl) ⟨61319, by rfl⟩ : syracuseStep 327037 = 122639) (by norm_num)
theorem B621989 : Blo 191804 621989 := bbase (se 4 (by rfl) ⟨58311, by rfl⟩ : syracuseStep 621989 = 116623) (by norm_num)
theorem B327125 : Blo 191804 327125 := bbase (se 7 (by rfl) ⟨3833, by rfl⟩ : syracuseStep 327125 = 7667) (by norm_num)
theorem B490981 : Blo 191804 490981 := bbase (se 4 (by rfl) ⟨46029, by rfl⟩ : syracuseStep 490981 = 92059) (by norm_num)
theorem B1474037 : Blo 191804 1474037 := bbase (se 5 (by rfl) ⟨69095, by rfl⟩ : syracuseStep 1474037 = 138191) (by norm_num)
theorem B294437 : Blo 191804 294437 := bbase (se 4 (by rfl) ⟨27603, by rfl⟩ : syracuseStep 294437 = 55207) (by norm_num)
theorem B327253 : Blo 191804 327253 := bbase (se 8 (by rfl) ⟨1917, by rfl⟩ : syracuseStep 327253 = 3835) (by norm_num)
theorem B491093 : Blo 191804 491093 := bbase (se 8 (by rfl) ⟨2877, by rfl⟩ : syracuseStep 491093 = 5755) (by norm_num)
theorem B654965 : Blo 191804 654965 := bbase (se 5 (by rfl) ⟨30701, by rfl⟩ : syracuseStep 654965 = 61403) (by norm_num)
theorem B327341 : Blo 191804 327341 := bbase (se 3 (by rfl) ⟨61376, by rfl⟩ : syracuseStep 327341 = 122753) (by norm_num)
theorem B261829 : Blo 191804 261829 := bbase (se 4 (by rfl) ⟨24546, by rfl⟩ : syracuseStep 261829 = 49093) (by norm_num)
theorem B491285 : Blo 191804 491285 := bbase (se 6 (by rfl) ⟨11514, by rfl⟩ : syracuseStep 491285 = 23029) (by norm_num)
theorem B327469 : Blo 191804 327469 := bbase (se 3 (by rfl) ⟨61400, by rfl⟩ : syracuseStep 327469 = 122801) (by norm_num)
theorem B982853 : Blo 191804 982853 := bbase (se 4 (by rfl) ⟨92142, by rfl⟩ : syracuseStep 982853 = 184285) (by norm_num)
theorem B262013 : Blo 191804 262013 := bbase (se 3 (by rfl) ⟨49127, by rfl⟩ : syracuseStep 262013 = 98255) (by norm_num)
theorem B327557 : Blo 191804 327557 := bbase (se 4 (by rfl) ⟨30708, by rfl⟩ : syracuseStep 327557 = 61417) (by norm_num)
theorem B393133 : Blo 191804 393133 := bbase (se 3 (by rfl) ⟨73712, by rfl⟩ : syracuseStep 393133 = 147425) (by norm_num)
theorem B884693 : Blo 191804 884693 := bbase (se 7 (by rfl) ⟨10367, by rfl⟩ : syracuseStep 884693 = 20735) (by norm_num)
theorem B327793 : Blo 191804 327793 := bstep (se 2 (by rfl) ⟨122922, by rfl⟩ : syracuseStep 327793 = 245845) B245845
theorem B819341 : Blo 191804 819341 := bstep (se 3 (by rfl) ⟨153626, by rfl⟩ : syracuseStep 819341 = 307253) B307253
theorem B655505 : Blo 191804 655505 := bstep (se 2 (by rfl) ⟨245814, by rfl⟩ : syracuseStep 655505 = 491629) B491629
theorem B327827 : Blo 191804 327827 := bstep (se 1 (by rfl) ⟨245870, by rfl⟩ : syracuseStep 327827 = 491741) B491741
theorem B557219 : Blo 191804 557219 := bstep (se 1 (by rfl) ⟨417914, by rfl⟩ : syracuseStep 557219 = 835829) B835829
theorem B327955 : Blo 191804 327955 := bstep (se 1 (by rfl) ⟨245966, by rfl⟩ : syracuseStep 327955 = 491933) B491933
theorem B328097 : Blo 191804 328097 := bstep (se 2 (by rfl) ⟨123036, by rfl⟩ : syracuseStep 328097 = 246073) B246073
theorem B491953 : Blo 191804 491953 := bstep (se 2 (by rfl) ⟨184482, by rfl⟩ : syracuseStep 491953 = 368965) B368965
theorem B983501 : Blo 191804 983501 := bstep (se 3 (by rfl) ⟨184406, by rfl⟩ : syracuseStep 983501 = 368813) B368813
theorem B4194787 : Blo 191804 4194787 := bstep (se 1 (by rfl) ⟨3146090, by rfl⟩ : syracuseStep 4194787 = 6292181) B6292181
theorem B557549 : Blo 191804 557549 := bstep (se 3 (by rfl) ⟨104540, by rfl⟩ : syracuseStep 557549 = 209081) B209081
theorem B328225 : Blo 191804 328225 := bstep (se 2 (by rfl) ⟨123084, by rfl⟩ : syracuseStep 328225 = 246169) B246169
theorem B328259 : Blo 191804 328259 := bstep (se 1 (by rfl) ⟨246194, by rfl⟩ : syracuseStep 328259 = 492389) B492389
theorem B656045 : Blo 191804 656045 := bstep (se 3 (by rfl) ⟨123008, by rfl⟩ : syracuseStep 656045 = 246017) B246017
theorem B492227 : Blo 191804 492227 := bstep (se 1 (by rfl) ⟨369170, by rfl⟩ : syracuseStep 492227 = 738341) B738341
theorem B328387 : Blo 191804 328387 := bstep (se 1 (by rfl) ⟨246290, by rfl⟩ : syracuseStep 328387 = 492581) B492581
theorem B262867 : Blo 191804 262867 := bstep (se 1 (by rfl) ⟨197150, by rfl⟩ : syracuseStep 262867 = 394301) B394301
theorem B656099 : Blo 191804 656099 := bstep (se 1 (by rfl) ⟨492074, by rfl⟩ : syracuseStep 656099 = 984149) B984149
theorem B328529 : Blo 191804 328529 := bstep (se 2 (by rfl) ⟨123198, by rfl⟩ : syracuseStep 328529 = 246397) B246397
theorem B2491235 : Blo 191804 2491235 := bstep (se 1 (by rfl) ⟨1868426, by rfl⟩ : syracuseStep 2491235 = 3736853) B3736853
theorem B590723 : Blo 191804 590723 := bstep (se 1 (by rfl) ⟨443042, by rfl⟩ : syracuseStep 590723 = 886085) B886085
theorem B492419 : Blo 191804 492419 := bstep (se 1 (by rfl) ⟨369314, by rfl⟩ : syracuseStep 492419 = 738629) B738629
theorem B623501 : Blo 191804 623501 := bstep (se 3 (by rfl) ⟨116906, by rfl⟩ : syracuseStep 623501 = 233813) B233813
theorem B1573829 : Blo 191804 1573829 := bstep (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) B295093
theorem B328657 : Blo 191804 328657 := bstep (se 2 (by rfl) ⟨123246, by rfl⟩ : syracuseStep 328657 = 246493) B246493
theorem B656369 : Blo 191804 656369 := bstep (se 2 (by rfl) ⟨246138, by rfl⟩ : syracuseStep 656369 = 492277) B492277
theorem B328691 : Blo 191804 328691 := bstep (se 1 (by rfl) ⟨246518, by rfl⟩ : syracuseStep 328691 = 493037) B493037
theorem B623629 : Blo 191804 623629 := bstep (se 3 (by rfl) ⟨116930, by rfl⟩ : syracuseStep 623629 = 233861) B233861
theorem B328819 : Blo 191804 328819 := bstep (se 1 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 328819 = 493229) B493229
theorem B263299 : Blo 191804 263299 := bstep (se 1 (by rfl) ⟨197474, by rfl⟩ : syracuseStep 263299 = 394949) B394949
theorem B328961 : Blo 191804 328961 := bstep (se 2 (by rfl) ⟨123360, by rfl⟩ : syracuseStep 328961 = 246721) B246721
theorem B329089 : Blo 191804 329089 := bstep (se 2 (by rfl) ⟨123408, by rfl⟩ : syracuseStep 329089 = 246817) B246817
theorem B1475981 : Blo 191804 1475981 := bstep (se 3 (by rfl) ⟨276746, by rfl⟩ : syracuseStep 1475981 = 553493) B553493
theorem B329123 : Blo 191804 329123 := bstep (se 1 (by rfl) ⟨246842, by rfl⟩ : syracuseStep 329123 = 493685) B493685
theorem B1050083 : Blo 191804 1050083 := bstep (se 1 (by rfl) ⟨787562, by rfl⟩ : syracuseStep 1050083 = 1575125) B1575125
theorem B656909 : Blo 191804 656909 := bstep (se 3 (by rfl) ⟨123170, by rfl⟩ : syracuseStep 656909 = 246341) B246341
theorem B329251 : Blo 191804 329251 := bstep (se 1 (by rfl) ⟨246938, by rfl⟩ : syracuseStep 329251 = 493877) B493877
theorem B656963 : Blo 191804 656963 := bstep (se 1 (by rfl) ⟨492722, by rfl⟩ : syracuseStep 656963 = 985445) B985445
theorem B329393 : Blo 191804 329393 := bstep (se 2 (by rfl) ⟨123522, by rfl⟩ : syracuseStep 329393 = 247045) B247045
theorem B493361 : Blo 191804 493361 := bstep (se 2 (by rfl) ⟨185010, by rfl⟩ : syracuseStep 493361 = 370021) B370021
theorem B329521 : Blo 191804 329521 := bstep (se 2 (by rfl) ⟨123570, by rfl⟩ : syracuseStep 329521 = 247141) B247141
theorem B657233 : Blo 191804 657233 := bstep (se 2 (by rfl) ⟨246462, by rfl⟩ : syracuseStep 657233 = 492925) B492925
theorem B329555 : Blo 191804 329555 := bstep (se 1 (by rfl) ⟨247166, by rfl⟩ : syracuseStep 329555 = 494333) B494333
theorem B493411 : Blo 191804 493411 := bstep (se 1 (by rfl) ⟨370058, by rfl⟩ : syracuseStep 493411 = 740117) B740117
theorem B329683 : Blo 191804 329683 := bstep (se 1 (by rfl) ⟨247262, by rfl⟩ : syracuseStep 329683 = 494525) B494525
theorem B493553 : Blo 191804 493553 := bstep (se 2 (by rfl) ⟨185082, by rfl⟩ : syracuseStep 493553 = 370165) B370165
theorem B329729 : Blo 191804 329729 := bstep (se 2 (by rfl) ⟨123648, by rfl⟩ : syracuseStep 329729 = 247297) B247297
theorem B1247309 : Blo 191804 1247309 := bstep (se 3 (by rfl) ⟨233870, by rfl⟩ : syracuseStep 1247309 = 467741) B467741
theorem B526417 : Blo 191804 526417 := bstep (se 2 (by rfl) ⟨197406, by rfl⟩ : syracuseStep 526417 = 394813) B394813
theorem B329825 : Blo 191804 329825 := bstep (se 2 (by rfl) ⟨123684, by rfl⟩ : syracuseStep 329825 = 247369) B247369
theorem B2001037 : Blo 191804 2001037 := bstep (se 3 (by rfl) ⟨375194, by rfl⟩ : syracuseStep 2001037 = 750389) B750389
theorem B526513 : Blo 191804 526513 := bstep (se 2 (by rfl) ⟨197442, by rfl⟩ : syracuseStep 526513 = 394885) B394885
theorem B329953 : Blo 191804 329953 := bstep (se 2 (by rfl) ⟨123732, by rfl⟩ : syracuseStep 329953 = 247465) B247465
theorem B329987 : Blo 191804 329987 := bstep (se 1 (by rfl) ⟨247490, by rfl⟩ : syracuseStep 329987 = 494981) B494981
theorem B657773 : Blo 191804 657773 := bstep (se 3 (by rfl) ⟨123332, by rfl⟩ : syracuseStep 657773 = 246665) B246665
theorem B330115 : Blo 191804 330115 := bstep (se 1 (by rfl) ⟨247586, by rfl⟩ : syracuseStep 330115 = 495173) B495173
theorem B657827 : Blo 191804 657827 := bstep (se 1 (by rfl) ⟨493370, by rfl⟩ : syracuseStep 657827 = 986741) B986741
theorem B526769 : Blo 191804 526769 := bstep (se 2 (by rfl) ⟨197538, by rfl⟩ : syracuseStep 526769 = 395077) B395077
theorem B330257 : Blo 191804 330257 := bstep (se 2 (by rfl) ⟨123846, by rfl⟩ : syracuseStep 330257 = 247693) B247693
theorem B395857 : Blo 191804 395857 := bstep (se 2 (by rfl) ⟨148446, by rfl⟩ : syracuseStep 395857 = 296893) B296893
theorem B330385 : Blo 191804 330385 := bstep (se 2 (by rfl) ⟨123894, by rfl⟩ : syracuseStep 330385 = 247789) B247789
theorem B658097 : Blo 191804 658097 := bstep (se 2 (by rfl) ⟨246786, by rfl⟩ : syracuseStep 658097 = 493573) B493573
theorem B330419 : Blo 191804 330419 := bstep (se 1 (by rfl) ⟨247814, by rfl⟩ : syracuseStep 330419 = 495629) B495629
theorem B527057 : Blo 191804 527057 := bstep (se 2 (by rfl) ⟨197646, by rfl⟩ : syracuseStep 527057 = 395293) B395293
theorem B592643 : Blo 191804 592643 := bstep (se 1 (by rfl) ⟨444482, by rfl⟩ : syracuseStep 592643 = 888965) B888965
theorem B625475 : Blo 191804 625475 := bstep (se 1 (by rfl) ⟨469106, by rfl⟩ : syracuseStep 625475 = 938213) B938213
theorem B625603 : Blo 191804 625603 := bstep (se 1 (by rfl) ⟨469202, by rfl⟩ : syracuseStep 625603 = 938405) B938405
theorem B494545 : Blo 191804 494545 := bstep (se 2 (by rfl) ⟨185454, by rfl⟩ : syracuseStep 494545 = 370909) B370909
theorem B625745 : Blo 191804 625745 := bstep (se 2 (by rfl) ⟨234654, by rfl⟩ : syracuseStep 625745 = 469309) B469309
theorem B822449 : Blo 191804 822449 := bstep (se 2 (by rfl) ⟨308418, by rfl⟩ : syracuseStep 822449 = 616837) B616837
theorem B625859 : Blo 191804 625859 := bstep (se 1 (by rfl) ⟨469394, by rfl⟩ : syracuseStep 625859 = 938789) B938789
theorem B658637 : Blo 191804 658637 := bstep (se 3 (by rfl) ⟨123494, by rfl⟩ : syracuseStep 658637 = 246989) B246989
theorem B494819 : Blo 191804 494819 := bstep (se 1 (by rfl) ⟨371114, by rfl⟩ : syracuseStep 494819 = 742229) B742229
theorem B330995 : Blo 191804 330995 := bstep (se 1 (by rfl) ⟨248246, by rfl⟩ : syracuseStep 330995 = 496493) B496493
theorem B265459 : Blo 191804 265459 := bstep (se 1 (by rfl) ⟨199094, by rfl⟩ : syracuseStep 265459 = 398189) B398189
theorem B658691 : Blo 191804 658691 := bstep (se 1 (by rfl) ⟨494018, by rfl⟩ : syracuseStep 658691 = 988037) B988037
theorem B986417 : Blo 191804 986417 := bstep (se 2 (by rfl) ⟨369906, by rfl⟩ : syracuseStep 986417 = 739813) B739813
theorem B2035043 : Blo 191804 2035043 := bstep (se 1 (by rfl) ⟨1526282, by rfl⟩ : syracuseStep 2035043 = 3052565) B3052565
theorem B495011 : Blo 191804 495011 := bstep (se 1 (by rfl) ⟨371258, by rfl⟩ : syracuseStep 495011 = 742517) B742517
theorem B658961 : Blo 191804 658961 := bstep (se 2 (by rfl) ⟨247110, by rfl⟩ : syracuseStep 658961 = 494221) B494221
theorem B658979 : Blo 191804 658979 := bstep (se 1 (by rfl) ⟨494234, by rfl⟩ : syracuseStep 658979 = 988469) B988469
theorem B527939 : Blo 191804 527939 := bstep (se 1 (by rfl) ⟨395954, by rfl⟩ : syracuseStep 527939 = 791909) B791909
theorem B691811 : Blo 191804 691811 := bstep (se 1 (by rfl) ⟨518858, by rfl⟩ : syracuseStep 691811 = 1037717) B1037717
theorem B790157 : Blo 191804 790157 := bstep (se 3 (by rfl) ⟨148154, by rfl⟩ : syracuseStep 790157 = 296309) B296309
theorem B233155 : Blo 191804 233155 := bstep (se 1 (by rfl) ⟨174866, by rfl⟩ : syracuseStep 233155 = 349733) B349733
theorem B659171 : Blo 191804 659171 := bstep (se 1 (by rfl) ⟨494378, by rfl⟩ : syracuseStep 659171 = 988757) B988757
theorem B593677 : Blo 191804 593677 := bstep (se 3 (by rfl) ⟨111314, by rfl⟩ : syracuseStep 593677 = 222629) B222629
theorem B1412963 : Blo 191804 1412963 := bstep (se 1 (by rfl) ⟨1059722, by rfl⟩ : syracuseStep 1412963 = 2119445) B2119445
theorem B5345165 : Blo 191804 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B659501 : Blo 191804 659501 := bstep (se 3 (by rfl) ⟨123656, by rfl⟩ : syracuseStep 659501 = 247313) B247313
theorem B659555 : Blo 191804 659555 := bstep (se 1 (by rfl) ⟨494666, by rfl⟩ : syracuseStep 659555 = 989333) B989333
theorem B364675 : Blo 191804 364675 := bstep (se 1 (by rfl) ⟨273506, by rfl⟩ : syracuseStep 364675 = 547013) B547013
theorem B692387 : Blo 191804 692387 := bstep (se 1 (by rfl) ⟨519290, by rfl⟩ : syracuseStep 692387 = 1038581) B1038581
theorem B495857 : Blo 191804 495857 := bstep (se 2 (by rfl) ⟨185946, by rfl⟩ : syracuseStep 495857 = 371893) B371893
theorem B1478897 : Blo 191804 1478897 := bstep (se 2 (by rfl) ⟨554586, by rfl⟩ : syracuseStep 1478897 = 1109173) B1109173
theorem B856433 : Blo 191804 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B659825 : Blo 191804 659825 := bstep (se 2 (by rfl) ⟨247434, by rfl⟩ : syracuseStep 659825 = 494869) B494869
theorem B823715 : Blo 191804 823715 := bstep (se 1 (by rfl) ⟨617786, by rfl⟩ : syracuseStep 823715 = 1235573) B1235573
theorem B1315277 : Blo 191804 1315277 := bstep (se 3 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 1315277 = 493229) B493229
theorem B365123 : Blo 191804 365123 := bstep (se 1 (by rfl) ⟨273842, by rfl⟩ : syracuseStep 365123 = 547685) B547685
theorem B528977 : Blo 191804 528977 := bstep (se 2 (by rfl) ⟨198366, by rfl⟩ : syracuseStep 528977 = 396733) B396733
theorem B4264645 : Blo 191804 4264645 := bstep (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) B799621
theorem B987875 : Blo 191804 987875 := bstep (se 1 (by rfl) ⟨740906, by rfl⟩ : syracuseStep 987875 = 1481813) B1481813
theorem B365411 : Blo 191804 365411 := bstep (se 1 (by rfl) ⟨274058, by rfl⟩ : syracuseStep 365411 = 548117) B548117
theorem B660365 : Blo 191804 660365 := bstep (se 3 (by rfl) ⟨123818, by rfl⟩ : syracuseStep 660365 = 247637) B247637
theorem B660419 : Blo 191804 660419 := bstep (se 1 (by rfl) ⟨495314, by rfl⟩ : syracuseStep 660419 = 990629) B990629
theorem B595075 : Blo 191804 595075 := bstep (se 1 (by rfl) ⟨446306, by rfl⟩ : syracuseStep 595075 = 892613) B892613
theorem B660689 : Blo 191804 660689 := bstep (se 2 (by rfl) ⟨247758, by rfl⟩ : syracuseStep 660689 = 495517) B495517
theorem B1316209 : Blo 191804 1316209 := bstep (se 2 (by rfl) ⟨493578, by rfl⟩ : syracuseStep 1316209 = 987157) B987157
theorem B660881 : Blo 191804 660881 := bstep (se 2 (by rfl) ⟨247830, by rfl⟩ : syracuseStep 660881 = 495661) B495661
theorem B234947 : Blo 191804 234947 := bstep (se 1 (by rfl) ⟨176210, by rfl⟩ : syracuseStep 234947 = 352421) B352421
theorem B1578467 : Blo 191804 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B988685 : Blo 191804 988685 := bstep (se 3 (by rfl) ⟨185378, by rfl⟩ : syracuseStep 988685 = 370757) B370757
theorem B431729 : Blo 191804 431729 := bstep (se 2 (by rfl) ⟨161898, by rfl⟩ : syracuseStep 431729 = 323797) B323797
theorem B431747 : Blo 191804 431747 := bstep (se 1 (by rfl) ⟨323810, by rfl⟩ : syracuseStep 431747 = 647621) B647621
theorem B3937933 : Blo 191804 3937933 := bstep (se 3 (by rfl) ⟨738362, by rfl⟩ : syracuseStep 3937933 = 1476725) B1476725
theorem B1119971 : Blo 191804 1119971 := bstep (se 1 (by rfl) ⟨839978, by rfl⟩ : syracuseStep 1119971 = 1679957) B1679957
theorem B694001 : Blo 191804 694001 := bstep (se 2 (by rfl) ⟨260250, by rfl⟩ : syracuseStep 694001 = 520501) B520501
theorem B366353 : Blo 191804 366353 := bstep (se 2 (by rfl) ⟨137382, by rfl⟩ : syracuseStep 366353 = 274765) B274765
theorem B432017 : Blo 191804 432017 := bstep (se 2 (by rfl) ⟨162006, by rfl⟩ : syracuseStep 432017 = 324013) B324013
theorem B432035 : Blo 191804 432035 := bstep (se 1 (by rfl) ⟨324026, by rfl⟩ : syracuseStep 432035 = 648053) B648053
theorem B530563 : Blo 191804 530563 := bstep (se 1 (by rfl) ⟨397922, by rfl⟩ : syracuseStep 530563 = 795845) B795845
theorem B432305 : Blo 191804 432305 := bstep (se 2 (by rfl) ⟨162114, by rfl⟩ : syracuseStep 432305 = 324229) B324229
theorem B432323 : Blo 191804 432323 := bstep (se 1 (by rfl) ⟨324242, by rfl⟩ : syracuseStep 432323 = 648485) B648485
theorem B432593 : Blo 191804 432593 := bstep (se 2 (by rfl) ⟨162222, by rfl⟩ : syracuseStep 432593 = 324445) B324445
theorem B432611 : Blo 191804 432611 := bstep (se 1 (by rfl) ⟨324458, by rfl⟩ : syracuseStep 432611 = 648917) B648917
theorem B1874501 : Blo 191804 1874501 := bstep (se 4 (by rfl) ⟨175734, by rfl⟩ : syracuseStep 1874501 = 351469) B351469
theorem B694925 : Blo 191804 694925 := bstep (se 3 (by rfl) ⟨130298, by rfl⟩ : syracuseStep 694925 = 260597) B260597
theorem B367249 : Blo 191804 367249 := bstep (se 2 (by rfl) ⟨137718, by rfl⟩ : syracuseStep 367249 = 275437) B275437
theorem B432881 : Blo 191804 432881 := bstep (se 2 (by rfl) ⟨162330, by rfl⟩ : syracuseStep 432881 = 324661) B324661
theorem B432899 : Blo 191804 432899 := bstep (se 1 (by rfl) ⟨324674, by rfl⟩ : syracuseStep 432899 = 649349) B649349
theorem B367409 : Blo 191804 367409 := bstep (se 2 (by rfl) ⟨137778, by rfl⟩ : syracuseStep 367409 = 275557) B275557
theorem B498545 : Blo 191804 498545 := bstep (se 2 (by rfl) ⟨186954, by rfl⟩ : syracuseStep 498545 = 373909) B373909
theorem B433169 : Blo 191804 433169 := bstep (se 2 (by rfl) ⟨162438, by rfl⟩ : syracuseStep 433169 = 324877) B324877
theorem B433187 : Blo 191804 433187 := bstep (se 1 (by rfl) ⟨324890, by rfl⟩ : syracuseStep 433187 = 649781) B649781
theorem B367811 : Blo 191804 367811 := bstep (se 1 (by rfl) ⟨275858, by rfl⟩ : syracuseStep 367811 = 551717) B551717
theorem B695587 : Blo 191804 695587 := bstep (se 1 (by rfl) ⟨521690, by rfl⟩ : syracuseStep 695587 = 1043381) B1043381
theorem B433457 : Blo 191804 433457 := bstep (se 2 (by rfl) ⟨162546, by rfl⟩ : syracuseStep 433457 = 325093) B325093
theorem B433475 : Blo 191804 433475 := bstep (se 1 (by rfl) ⟨325106, by rfl⟩ : syracuseStep 433475 = 650213) B650213
theorem B1252741 : Blo 191804 1252741 := bstep (se 4 (by rfl) ⟨117444, by rfl⟩ : syracuseStep 1252741 = 234889) B234889
theorem B433745 : Blo 191804 433745 := bstep (se 2 (by rfl) ⟨162654, by rfl⟩ : syracuseStep 433745 = 325309) B325309
theorem B433763 : Blo 191804 433763 := bstep (se 1 (by rfl) ⟨325322, by rfl⟩ : syracuseStep 433763 = 650645) B650645
theorem B696077 : Blo 191804 696077 := bstep (se 3 (by rfl) ⟨130514, by rfl⟩ : syracuseStep 696077 = 261029) B261029
theorem B892721 : Blo 191804 892721 := bstep (se 2 (by rfl) ⟨334770, by rfl⟩ : syracuseStep 892721 = 669541) B669541
theorem B302915 : Blo 191804 302915 := bstep (se 1 (by rfl) ⟨227186, by rfl⟩ : syracuseStep 302915 = 454373) B454373
theorem B728909 : Blo 191804 728909 := bstep (se 3 (by rfl) ⟨136670, by rfl⟩ : syracuseStep 728909 = 273341) B273341
theorem B434033 : Blo 191804 434033 := bstep (se 2 (by rfl) ⟨162762, by rfl⟩ : syracuseStep 434033 = 325525) B325525
theorem B434051 : Blo 191804 434051 := bstep (se 1 (by rfl) ⟨325538, by rfl⟩ : syracuseStep 434051 = 651077) B651077
theorem B827405 : Blo 191804 827405 := bstep (se 3 (by rfl) ⟨155138, by rfl⟩ : syracuseStep 827405 = 310277) B310277
theorem B368707 : Blo 191804 368707 := bstep (se 1 (by rfl) ⟨276530, by rfl⟩ : syracuseStep 368707 = 553061) B553061
theorem B434321 : Blo 191804 434321 := bstep (se 2 (by rfl) ⟨162870, by rfl⟩ : syracuseStep 434321 = 325741) B325741
theorem B434339 : Blo 191804 434339 := bstep (se 1 (by rfl) ⟨325754, by rfl⟩ : syracuseStep 434339 = 651509) B651509
theorem B368867 : Blo 191804 368867 := bstep (se 1 (by rfl) ⟨276650, by rfl⟩ : syracuseStep 368867 = 553301) B553301
theorem B3744053 : Blo 191804 3744053 := bstep (se 5 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 3744053 = 351005) B351005
theorem B434609 : Blo 191804 434609 := bstep (se 2 (by rfl) ⟨162978, by rfl⟩ : syracuseStep 434609 = 325957) B325957
theorem B434627 : Blo 191804 434627 := bstep (se 1 (by rfl) ⟨325970, by rfl⟩ : syracuseStep 434627 = 651941) B651941
theorem B434897 : Blo 191804 434897 := bstep (se 2 (by rfl) ⟨163086, by rfl⟩ : syracuseStep 434897 = 326173) B326173
theorem B434915 : Blo 191804 434915 := bstep (se 1 (by rfl) ⟨326186, by rfl⟩ : syracuseStep 434915 = 652373) B652373
theorem B467779 : Blo 191804 467779 := bstep (se 1 (by rfl) ⟨350834, by rfl⟩ : syracuseStep 467779 = 701669) B701669
theorem B435185 : Blo 191804 435185 := bstep (se 2 (by rfl) ⟨163194, by rfl⟩ : syracuseStep 435185 = 326389) B326389
theorem B435203 : Blo 191804 435203 := bstep (se 1 (by rfl) ⟨326402, by rfl⟩ : syracuseStep 435203 = 652805) B652805
theorem B664643 : Blo 191804 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B2073869 : Blo 191804 2073869 := bstep (se 3 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 2073869 = 777701) B777701
theorem B369937 : Blo 191804 369937 := bstep (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) B277453
theorem B435473 : Blo 191804 435473 := bstep (se 2 (by rfl) ⟨163302, by rfl⟩ : syracuseStep 435473 = 326605) B326605
theorem B435491 : Blo 191804 435491 := bstep (se 1 (by rfl) ⟨326618, by rfl⟩ : syracuseStep 435491 = 653237) B653237
theorem B468337 : Blo 191804 468337 := bstep (se 2 (by rfl) ⟨175626, by rfl⟩ : syracuseStep 468337 = 351253) B351253
theorem B435761 : Blo 191804 435761 := bstep (se 2 (by rfl) ⟨163410, by rfl⟩ : syracuseStep 435761 = 326821) B326821
theorem B435779 : Blo 191804 435779 := bstep (se 1 (by rfl) ⟨326834, by rfl⟩ : syracuseStep 435779 = 653669) B653669
theorem B1320581 : Blo 191804 1320581 := bstep (se 4 (by rfl) ⟨123804, by rfl⟩ : syracuseStep 1320581 = 247609) B247609
theorem B927409 : Blo 191804 927409 := bstep (se 2 (by rfl) ⟨347778, by rfl⟩ : syracuseStep 927409 = 695557) B695557
theorem B436049 : Blo 191804 436049 := bstep (se 2 (by rfl) ⟨163518, by rfl⟩ : syracuseStep 436049 = 327037) B327037
theorem B436067 : Blo 191804 436067 := bstep (se 1 (by rfl) ⟨327050, by rfl⟩ : syracuseStep 436067 = 654101) B654101
theorem B206723 : Blo 191804 206723 := bstep (se 1 (by rfl) ⟨155042, by rfl⟩ : syracuseStep 206723 = 310085) B310085
theorem B993293 : Blo 191804 993293 := bstep (se 3 (by rfl) ⟨186242, by rfl⟩ : syracuseStep 993293 = 372485) B372485
theorem B469009 : Blo 191804 469009 := bstep (se 2 (by rfl) ⟨175878, by rfl⟩ : syracuseStep 469009 = 351757) B351757
theorem B436337 : Blo 191804 436337 := bstep (se 2 (by rfl) ⟨163626, by rfl⟩ : syracuseStep 436337 = 327253) B327253
theorem B436355 : Blo 191804 436355 := bstep (se 1 (by rfl) ⟨327266, by rfl⟩ : syracuseStep 436355 = 654533) B654533
theorem B2009285 : Blo 191804 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B370993 : Blo 191804 370993 := bstep (se 2 (by rfl) ⟨139122, by rfl⟩ : syracuseStep 370993 = 278245) B278245
theorem B1059149 : Blo 191804 1059149 := bstep (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) B397181
theorem B698701 : Blo 191804 698701 := bstep (se 3 (by rfl) ⟨131006, by rfl⟩ : syracuseStep 698701 = 262013) B262013
theorem B436625 : Blo 191804 436625 := bstep (se 2 (by rfl) ⟨163734, by rfl⟩ : syracuseStep 436625 = 327469) B327469
theorem B436643 : Blo 191804 436643 := bstep (se 1 (by rfl) ⟨327482, by rfl⟩ : syracuseStep 436643 = 654965) B654965
theorem B731825 : Blo 191804 731825 := bstep (se 2 (by rfl) ⟨274434, by rfl⟩ : syracuseStep 731825 = 548869) B548869
theorem B436913 : Blo 191804 436913 := bstep (se 2 (by rfl) ⟨163842, by rfl⟩ : syracuseStep 436913 = 327685) B327685
theorem B436931 : Blo 191804 436931 := bstep (se 1 (by rfl) ⟨327698, by rfl⟩ : syracuseStep 436931 = 655397) B655397
theorem B371395 : Blo 191804 371395 := bstep (se 1 (by rfl) ⟨278546, by rfl⟩ : syracuseStep 371395 = 557093) B557093
theorem B371441 : Blo 191804 371441 := bstep (se 2 (by rfl) ⟨139290, by rfl⟩ : syracuseStep 371441 = 278581) B278581
theorem B273233 : Blo 191804 273233 := bstep (se 2 (by rfl) ⟨102462, by rfl⟩ : syracuseStep 273233 = 204925) B204925
theorem B666467 : Blo 191804 666467 := bstep (se 1 (by rfl) ⟨499850, by rfl⟩ : syracuseStep 666467 = 999701) B999701
theorem B207731 : Blo 191804 207731 := bstep (se 1 (by rfl) ⟨155798, by rfl⟩ : syracuseStep 207731 = 311597) B311597
theorem B437201 : Blo 191804 437201 := bstep (se 2 (by rfl) ⟨163950, by rfl⟩ : syracuseStep 437201 = 327901) B327901
theorem B338897 : Blo 191804 338897 := bstep (se 2 (by rfl) ⟨127086, by rfl⟩ : syracuseStep 338897 = 254173) B254173
theorem B437219 : Blo 191804 437219 := bstep (se 1 (by rfl) ⟨327914, by rfl⟩ : syracuseStep 437219 = 655829) B655829
theorem B830513 : Blo 191804 830513 := bstep (se 2 (by rfl) ⟨311442, by rfl⟩ : syracuseStep 830513 = 622885) B622885
theorem B437489 : Blo 191804 437489 := bstep (se 2 (by rfl) ⟨164058, by rfl⟩ : syracuseStep 437489 = 328117) B328117
theorem B437507 : Blo 191804 437507 := bstep (se 1 (by rfl) ⟨328130, by rfl⟩ : syracuseStep 437507 = 656261) B656261
theorem B437777 : Blo 191804 437777 := bstep (se 2 (by rfl) ⟨164166, by rfl⟩ : syracuseStep 437777 = 328333) B328333
theorem B437795 : Blo 191804 437795 := bstep (se 1 (by rfl) ⟨328346, by rfl⟩ : syracuseStep 437795 = 656693) B656693
theorem B274099 : Blo 191804 274099 := bstep (se 1 (by rfl) ⟨205574, by rfl⟩ : syracuseStep 274099 = 411149) B411149
theorem B831181 : Blo 191804 831181 := bstep (se 3 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 831181 = 311693) B311693
theorem B274195 : Blo 191804 274195 := bstep (se 1 (by rfl) ⟨205646, by rfl⟩ : syracuseStep 274195 = 411293) B411293
theorem B438065 : Blo 191804 438065 := bstep (se 2 (by rfl) ⟨164274, by rfl⟩ : syracuseStep 438065 = 328549) B328549
theorem B438083 : Blo 191804 438083 := bstep (se 1 (by rfl) ⟨328562, by rfl⟩ : syracuseStep 438083 = 657125) B657125
theorem B438353 : Blo 191804 438353 := bstep (se 2 (by rfl) ⟨164382, by rfl⟩ : syracuseStep 438353 = 328765) B328765
theorem B438371 : Blo 191804 438371 := bstep (se 1 (by rfl) ⟨328778, by rfl⟩ : syracuseStep 438371 = 657557) B657557
theorem B733283 : Blo 191804 733283 := bstep (se 1 (by rfl) ⟨549962, by rfl⟩ : syracuseStep 733283 = 1099925) B1099925
theorem B372977 : Blo 191804 372977 := bstep (se 2 (by rfl) ⟨139866, by rfl⟩ : syracuseStep 372977 = 279733) B279733
theorem B274691 : Blo 191804 274691 := bstep (se 1 (by rfl) ⟨206018, by rfl⟩ : syracuseStep 274691 = 412037) B412037
theorem B831779 : Blo 191804 831779 := bstep (se 1 (by rfl) ⟨623834, by rfl⟩ : syracuseStep 831779 = 1247669) B1247669
theorem B438641 : Blo 191804 438641 := bstep (se 2 (by rfl) ⟨164490, by rfl⟩ : syracuseStep 438641 = 328981) B328981
theorem B438659 : Blo 191804 438659 := bstep (se 1 (by rfl) ⟨328994, by rfl⟩ : syracuseStep 438659 = 657989) B657989
theorem B438691 : Blo 191804 438691 := bstep (se 1 (by rfl) ⟨329018, by rfl⟩ : syracuseStep 438691 = 658037) B658037
theorem B1094093 : Blo 191804 1094093 := bstep (se 3 (by rfl) ⟨205142, by rfl⟩ : syracuseStep 1094093 = 410285) B410285
theorem B438929 : Blo 191804 438929 := bstep (se 2 (by rfl) ⟨164598, by rfl⟩ : syracuseStep 438929 = 329197) B329197
theorem B930467 : Blo 191804 930467 := bstep (se 1 (by rfl) ⟨697850, by rfl⟩ : syracuseStep 930467 = 1395701) B1395701
theorem B438947 : Blo 191804 438947 := bstep (se 1 (by rfl) ⟨329210, by rfl⟩ : syracuseStep 438947 = 658421) B658421
theorem B1651427 : Blo 191804 1651427 := bstep (se 1 (by rfl) ⟨1238570, by rfl⟩ : syracuseStep 1651427 = 2477141) B2477141
theorem B930637 : Blo 191804 930637 := bstep (se 3 (by rfl) ⟨174494, by rfl⟩ : syracuseStep 930637 = 348989) B348989
theorem B275329 : Blo 191804 275329 := bstep (se 2 (by rfl) ⟨103248, by rfl⟩ : syracuseStep 275329 = 206497) B206497
theorem B439217 : Blo 191804 439217 := bstep (se 2 (by rfl) ⟨164706, by rfl⟩ : syracuseStep 439217 = 329413) B329413
theorem B439235 : Blo 191804 439235 := bstep (se 1 (by rfl) ⟨329426, by rfl⟩ : syracuseStep 439235 = 658853) B658853
theorem B308227 : Blo 191804 308227 := bstep (se 1 (by rfl) ⟨231170, by rfl⟩ : syracuseStep 308227 = 462341) B462341
theorem B832547 : Blo 191804 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B734285 : Blo 191804 734285 := bstep (se 3 (by rfl) ⟨137678, by rfl⟩ : syracuseStep 734285 = 275357) B275357
theorem B439427 : Blo 191804 439427 := bstep (se 1 (by rfl) ⟨329570, by rfl⟩ : syracuseStep 439427 = 659141) B659141
theorem B275665 : Blo 191804 275665 := bstep (se 2 (by rfl) ⟨103374, by rfl⟩ : syracuseStep 275665 = 206749) B206749
theorem B570577 : Blo 191804 570577 := bstep (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) B427933
theorem B439505 : Blo 191804 439505 := bstep (se 2 (by rfl) ⟨164814, by rfl⟩ : syracuseStep 439505 = 329629) B329629
theorem B439523 : Blo 191804 439523 := bstep (se 1 (by rfl) ⟨329642, by rfl⟩ : syracuseStep 439523 = 659285) B659285
theorem B242995 : Blo 191804 242995 := bstep (se 1 (by rfl) ⟨182246, by rfl⟩ : syracuseStep 242995 = 364493) B364493
theorem B243091 : Blo 191804 243091 := bstep (se 1 (by rfl) ⟨182318, by rfl⟩ : syracuseStep 243091 = 364637) B364637
theorem B308675 : Blo 191804 308675 := bstep (se 1 (by rfl) ⟨231506, by rfl⟩ : syracuseStep 308675 = 463013) B463013
theorem B439793 : Blo 191804 439793 := bstep (se 2 (by rfl) ⟨164922, by rfl⟩ : syracuseStep 439793 = 329845) B329845
theorem B439811 : Blo 191804 439811 := bstep (se 1 (by rfl) ⟨329858, by rfl⟩ : syracuseStep 439811 = 659717) B659717
theorem B669325 : Blo 191804 669325 := bstep (se 3 (by rfl) ⟨125498, by rfl⟩ : syracuseStep 669325 = 250997) B250997
theorem B440081 : Blo 191804 440081 := bstep (se 2 (by rfl) ⟨165030, by rfl⟩ : syracuseStep 440081 = 330061) B330061
theorem B276257 : Blo 191804 276257 := bstep (se 2 (by rfl) ⟨103596, by rfl⟩ : syracuseStep 276257 = 207193) B207193
theorem B440099 : Blo 191804 440099 := bstep (se 1 (by rfl) ⟨330074, by rfl⟩ : syracuseStep 440099 = 660149) B660149
theorem B243587 : Blo 191804 243587 := bstep (se 1 (by rfl) ⟨182690, by rfl⟩ : syracuseStep 243587 = 365381) B365381
theorem B309233 : Blo 191804 309233 := bstep (se 2 (by rfl) ⟨115962, by rfl⟩ : syracuseStep 309233 = 231925) B231925
theorem B440369 : Blo 191804 440369 := bstep (se 2 (by rfl) ⟨165138, by rfl⟩ : syracuseStep 440369 = 330277) B330277
theorem B440387 : Blo 191804 440387 := bstep (se 1 (by rfl) ⟨330290, by rfl⟩ : syracuseStep 440387 = 660581) B660581
theorem B309457 : Blo 191804 309457 := bstep (se 2 (by rfl) ⟨116046, by rfl⟩ : syracuseStep 309457 = 232093) B232093
theorem B309521 : Blo 191804 309521 := bstep (se 2 (by rfl) ⟨116070, by rfl⟩ : syracuseStep 309521 = 232141) B232141
theorem B997667 : Blo 191804 997667 := bstep (se 1 (by rfl) ⟨748250, by rfl⟩ : syracuseStep 997667 = 1496501) B1496501
theorem B276787 : Blo 191804 276787 := bstep (se 1 (by rfl) ⟨207590, by rfl⟩ : syracuseStep 276787 = 415181) B415181
theorem B309649 : Blo 191804 309649 := bstep (se 2 (by rfl) ⟨116118, by rfl⟩ : syracuseStep 309649 = 232237) B232237
theorem B244291 : Blo 191804 244291 := bstep (se 1 (by rfl) ⟨183218, by rfl⟩ : syracuseStep 244291 = 366437) B366437
theorem B277123 : Blo 191804 277123 := bstep (se 1 (by rfl) ⟨207842, by rfl⟩ : syracuseStep 277123 = 415685) B415685
theorem B1096325 : Blo 191804 1096325 := bstep (se 4 (by rfl) ⟨102780, by rfl⟩ : syracuseStep 1096325 = 205561) B205561
theorem B244387 : Blo 191804 244387 := bstep (se 1 (by rfl) ⟨183290, by rfl⟩ : syracuseStep 244387 = 366581) B366581
theorem B736397 : Blo 191804 736397 := bstep (se 3 (by rfl) ⟨138074, by rfl⟩ : syracuseStep 736397 = 276149) B276149
theorem B244883 : Blo 191804 244883 := bstep (se 1 (by rfl) ⟨183662, by rfl⟩ : syracuseStep 244883 = 367325) B367325
theorem B277681 : Blo 191804 277681 := bstep (se 2 (by rfl) ⟨104130, by rfl⟩ : syracuseStep 277681 = 208261) B208261
theorem B277715 : Blo 191804 277715 := bstep (se 1 (by rfl) ⟨208286, by rfl⟩ : syracuseStep 277715 = 416573) B416573
theorem B1097009 : Blo 191804 1097009 := bstep (se 2 (by rfl) ⟨411378, by rfl⟩ : syracuseStep 1097009 = 822757) B822757
theorem B474545 : Blo 191804 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B278273 : Blo 191804 278273 := bstep (se 2 (by rfl) ⟨104352, by rfl⟩ : syracuseStep 278273 = 208705) B208705
theorem B278353 : Blo 191804 278353 := bstep (se 2 (by rfl) ⟨104382, by rfl⟩ : syracuseStep 278353 = 208765) B208765
theorem B245587 : Blo 191804 245587 := bstep (se 1 (by rfl) ⟨184190, by rfl⟩ : syracuseStep 245587 = 368381) B368381
theorem B1392497 : Blo 191804 1392497 := bstep (se 2 (by rfl) ⟨522186, by rfl⟩ : syracuseStep 1392497 = 1044373) B1044373
theorem B737201 : Blo 191804 737201 := bstep (se 2 (by rfl) ⟨276450, by rfl⟩ : syracuseStep 737201 = 552901) B552901
theorem B245683 : Blo 191804 245683 := bstep (se 1 (by rfl) ⟨184262, by rfl⟩ : syracuseStep 245683 = 368525) B368525
theorem B835555 : Blo 191804 835555 := bstep (se 1 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 835555 = 1253333) B1253333
theorem B966691 : Blo 191804 966691 := bstep (se 1 (by rfl) ⟨725018, by rfl⟩ : syracuseStep 966691 = 1450037) B1450037
theorem B311699 : Blo 191804 311699 := bstep (se 1 (by rfl) ⟨233774, by rfl⟩ : syracuseStep 311699 = 467549) B467549
theorem B246179 : Blo 191804 246179 := bstep (se 1 (by rfl) ⟨184634, by rfl⟩ : syracuseStep 246179 = 369269) B369269
theorem B737869 : Blo 191804 737869 := bstep (se 3 (by rfl) ⟨138350, by rfl⟩ : syracuseStep 737869 = 276701) B276701
theorem B1098467 : Blo 191804 1098467 := bstep (se 1 (by rfl) ⟨823850, by rfl⟩ : syracuseStep 1098467 = 1647701) B1647701
theorem B1229573 : Blo 191804 1229573 := bstep (se 4 (by rfl) ⟨115272, by rfl⟩ : syracuseStep 1229573 = 230545) B230545
theorem B246883 : Blo 191804 246883 := bstep (se 1 (by rfl) ⟨185162, by rfl⟩ : syracuseStep 246883 = 370325) B370325
theorem B246979 : Blo 191804 246979 := bstep (se 1 (by rfl) ⟨185234, by rfl⟩ : syracuseStep 246979 = 370469) B370469
theorem B312545 : Blo 191804 312545 := bstep (se 2 (by rfl) ⟨117204, by rfl⟩ : syracuseStep 312545 = 234409) B234409
theorem B4179221 : Blo 191804 4179221 := bstep (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) B195901
theorem B738659 : Blo 191804 738659 := bstep (se 1 (by rfl) ⟨553994, by rfl⟩ : syracuseStep 738659 = 1107989) B1107989
theorem B2377187 : Blo 191804 2377187 := bstep (se 1 (by rfl) ⟨1782890, by rfl⟩ : syracuseStep 2377187 = 3565781) B3565781
theorem B247475 : Blo 191804 247475 := bstep (se 1 (by rfl) ⟨185606, by rfl⟩ : syracuseStep 247475 = 371213) B371213
theorem B444209 : Blo 191804 444209 := bstep (se 2 (by rfl) ⟨166578, by rfl⟩ : syracuseStep 444209 = 333157) B333157
theorem B313283 : Blo 191804 313283 := bstep (se 1 (by rfl) ⟨234962, by rfl⟩ : syracuseStep 313283 = 469925) B469925
theorem B411601 : Blo 191804 411601 := bstep (se 2 (by rfl) ⟨154350, by rfl⟩ : syracuseStep 411601 = 308701) B308701
theorem B739313 : Blo 191804 739313 := bstep (se 2 (by rfl) ⟨277242, by rfl⟩ : syracuseStep 739313 = 554485) B554485
theorem B1001521 : Blo 191804 1001521 := bstep (se 2 (by rfl) ⟨375570, by rfl⟩ : syracuseStep 1001521 = 751141) B751141
theorem B280675 : Blo 191804 280675 := bstep (se 1 (by rfl) ⟨210506, by rfl⟩ : syracuseStep 280675 = 421013) B421013
theorem B444611 : Blo 191804 444611 := bstep (se 1 (by rfl) ⟨333458, by rfl⟩ : syracuseStep 444611 = 666917) B666917
theorem B1755377 : Blo 191804 1755377 := bstep (se 2 (by rfl) ⟨658266, by rfl⟩ : syracuseStep 1755377 = 1316533) B1316533
theorem B2672909 : Blo 191804 2672909 := bstep (se 3 (by rfl) ⟨501170, by rfl⟩ : syracuseStep 2672909 = 1002341) B1002341
theorem B1231523 : Blo 191804 1231523 := bstep (se 1 (by rfl) ⟨923642, by rfl⟩ : syracuseStep 1231523 = 1847285) B1847285
theorem B215923 : Blo 191804 215923 := bstep (se 1 (by rfl) ⟨161942, by rfl⟩ : syracuseStep 215923 = 323885) B323885
theorem B281539 : Blo 191804 281539 := bstep (se 1 (by rfl) ⟨211154, by rfl⟩ : syracuseStep 281539 = 422309) B422309
theorem B216067 : Blo 191804 216067 := bstep (se 1 (by rfl) ⟨162050, by rfl⟩ : syracuseStep 216067 = 324101) B324101
theorem B216211 : Blo 191804 216211 := bstep (se 1 (by rfl) ⟨162158, by rfl⟩ : syracuseStep 216211 = 324317) B324317
theorem B216355 : Blo 191804 216355 := bstep (se 1 (by rfl) ⟨162266, by rfl⟩ : syracuseStep 216355 = 324533) B324533
theorem B6344077 : Blo 191804 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B740771 : Blo 191804 740771 := bstep (se 1 (by rfl) ⟨555578, by rfl⟩ : syracuseStep 740771 = 1111157) B1111157
theorem B740785 : Blo 191804 740785 := bstep (se 2 (by rfl) ⟨277794, by rfl⟩ : syracuseStep 740785 = 555589) B555589
theorem B216499 : Blo 191804 216499 := bstep (se 1 (by rfl) ⟨162374, by rfl⟩ : syracuseStep 216499 = 324749) B324749
theorem B216643 : Blo 191804 216643 := bstep (se 1 (by rfl) ⟨162482, by rfl⟩ : syracuseStep 216643 = 324965) B324965
theorem B4247153 : Blo 191804 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B216787 : Blo 191804 216787 := bstep (se 1 (by rfl) ⟨162590, by rfl⟩ : syracuseStep 216787 = 325181) B325181
theorem B216931 : Blo 191804 216931 := bstep (se 1 (by rfl) ⟨162698, by rfl⟩ : syracuseStep 216931 = 325397) B325397
theorem B1101701 : Blo 191804 1101701 := bstep (se 4 (by rfl) ⟨103284, by rfl⟩ : syracuseStep 1101701 = 206569) B206569
theorem B446435 : Blo 191804 446435 := bstep (se 1 (by rfl) ⟨334826, by rfl⟩ : syracuseStep 446435 = 669653) B669653
theorem B217075 : Blo 191804 217075 := bstep (se 1 (by rfl) ⟨162806, by rfl⟩ : syracuseStep 217075 = 325613) B325613
theorem B217219 : Blo 191804 217219 := bstep (se 1 (by rfl) ⟨162914, by rfl⟩ : syracuseStep 217219 = 325829) B325829
theorem B3133637 : Blo 191804 3133637 := bstep (se 4 (by rfl) ⟨293778, by rfl⟩ : syracuseStep 3133637 = 587557) B587557
theorem B217363 : Blo 191804 217363 := bstep (se 1 (by rfl) ⟨163022, by rfl⟩ : syracuseStep 217363 = 326045) B326045
theorem B1200419 : Blo 191804 1200419 := bstep (se 1 (by rfl) ⟨900314, by rfl⟩ : syracuseStep 1200419 = 1800629) B1800629
theorem B1102157 : Blo 191804 1102157 := bstep (se 3 (by rfl) ⟨206654, by rfl⟩ : syracuseStep 1102157 = 413309) B413309
theorem B217507 : Blo 191804 217507 := bstep (se 1 (by rfl) ⟨163130, by rfl⟩ : syracuseStep 217507 = 326261) B326261
theorem B348643 : Blo 191804 348643 := bstep (se 1 (by rfl) ⟨261482, by rfl⟩ : syracuseStep 348643 = 522965) B522965
theorem B217651 : Blo 191804 217651 := bstep (se 1 (by rfl) ⟨163238, by rfl⟩ : syracuseStep 217651 = 326477) B326477
theorem B1168013 : Blo 191804 1168013 := bstep (se 3 (by rfl) ⟨219002, by rfl⟩ : syracuseStep 1168013 = 438005) B438005
theorem B217795 : Blo 191804 217795 := bstep (se 1 (by rfl) ⟨163346, by rfl⟩ : syracuseStep 217795 = 326693) B326693
theorem B217939 : Blo 191804 217939 := bstep (se 1 (by rfl) ⟨163454, by rfl⟩ : syracuseStep 217939 = 326909) B326909
theorem B742243 : Blo 191804 742243 := bstep (se 1 (by rfl) ⟨556682, by rfl⟩ : syracuseStep 742243 = 1113365) B1113365
theorem B349105 : Blo 191804 349105 := bstep (se 2 (by rfl) ⟨130914, by rfl⟩ : syracuseStep 349105 = 261829) B261829
theorem B414659 : Blo 191804 414659 := bstep (se 1 (by rfl) ⟨310994, by rfl⟩ : syracuseStep 414659 = 621989) B621989
theorem B218083 : Blo 191804 218083 := bstep (se 1 (by rfl) ⟨163562, by rfl⟩ : syracuseStep 218083 = 327125) B327125
theorem B840739 : Blo 191804 840739 := bstep (se 1 (by rfl) ⟨630554, by rfl⟩ : syracuseStep 840739 = 1261109) B1261109
theorem B218227 : Blo 191804 218227 := bstep (se 1 (by rfl) ⟨163670, by rfl⟩ : syracuseStep 218227 = 327341) B327341
theorem B1234061 : Blo 191804 1234061 := bstep (se 3 (by rfl) ⟨231386, by rfl⟩ : syracuseStep 1234061 = 462773) B462773
theorem B218371 : Blo 191804 218371 := bstep (se 1 (by rfl) ⟨163778, by rfl⟩ : syracuseStep 218371 = 327557) B327557
theorem B218515 : Blo 191804 218515 := bstep (se 1 (by rfl) ⟨163886, by rfl⟩ : syracuseStep 218515 = 327773) B327773
theorem B349681 : Blo 191804 349681 := bstep (se 2 (by rfl) ⟨131130, by rfl⟩ : syracuseStep 349681 = 262261) B262261
theorem B218659 : Blo 191804 218659 := bstep (se 1 (by rfl) ⟨163994, by rfl⟩ : syracuseStep 218659 = 327989) B327989
theorem B972323 : Blo 191804 972323 := bstep (se 1 (by rfl) ⟨729242, by rfl⟩ : syracuseStep 972323 = 1458485) B1458485
theorem B1070725 : Blo 191804 1070725 := bstep (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) B200761
theorem B218803 : Blo 191804 218803 := bstep (se 1 (by rfl) ⟨164102, by rfl⟩ : syracuseStep 218803 = 328205) B328205
theorem B415523 : Blo 191804 415523 := bstep (se 1 (by rfl) ⟨311642, by rfl⟩ : syracuseStep 415523 = 623285) B623285
theorem B907057 : Blo 191804 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B218947 : Blo 191804 218947 := bstep (se 1 (by rfl) ⟨164210, by rfl⟩ : syracuseStep 218947 = 328421) B328421
theorem B546659 : Blo 191804 546659 := bstep (se 1 (by rfl) ⟨409994, by rfl⟩ : syracuseStep 546659 = 819989) B819989
theorem B415633 : Blo 191804 415633 := bstep (se 2 (by rfl) ⟨155862, by rfl⟩ : syracuseStep 415633 = 311725) B311725
theorem B219091 : Blo 191804 219091 := bstep (se 1 (by rfl) ⟨164318, by rfl⟩ : syracuseStep 219091 = 328637) B328637
theorem B1169477 : Blo 191804 1169477 := bstep (se 4 (by rfl) ⟨109638, by rfl⟩ : syracuseStep 1169477 = 219277) B219277
theorem B219235 : Blo 191804 219235 := bstep (se 1 (by rfl) ⟨164426, by rfl⟩ : syracuseStep 219235 = 328853) B328853
theorem B219379 : Blo 191804 219379 := bstep (se 1 (by rfl) ⟨164534, by rfl⟩ : syracuseStep 219379 = 329069) B329069
theorem B2185541 : Blo 191804 2185541 := bstep (se 4 (by rfl) ⟨204894, by rfl⟩ : syracuseStep 2185541 = 409789) B409789
theorem B973133 : Blo 191804 973133 := bstep (se 3 (by rfl) ⟨182462, by rfl⟩ : syracuseStep 973133 = 364925) B364925
theorem B219523 : Blo 191804 219523 := bstep (se 1 (by rfl) ⟨164642, by rfl⟩ : syracuseStep 219523 = 329285) B329285
theorem B1464803 : Blo 191804 1464803 := bstep (se 1 (by rfl) ⟨1098602, by rfl⟩ : syracuseStep 1464803 = 2197205) B2197205
theorem B219667 : Blo 191804 219667 := bstep (se 1 (by rfl) ⟨164750, by rfl⟩ : syracuseStep 219667 = 329501) B329501
theorem B547469 : Blo 191804 547469 := bstep (se 3 (by rfl) ⟨102650, by rfl⟩ : syracuseStep 547469 = 205301) B205301
theorem B219811 : Blo 191804 219811 := bstep (se 1 (by rfl) ⟨164858, by rfl⟩ : syracuseStep 219811 = 329717) B329717
theorem B219955 : Blo 191804 219955 := bstep (se 1 (by rfl) ⟨164966, by rfl⟩ : syracuseStep 219955 = 329933) B329933
theorem B547661 : Blo 191804 547661 := bstep (se 3 (by rfl) ⟨102686, by rfl⟩ : syracuseStep 547661 = 205373) B205373
theorem B220099 : Blo 191804 220099 := bstep (se 1 (by rfl) ⟨165074, by rfl⟩ : syracuseStep 220099 = 330149) B330149
theorem B220115 : Blo 191804 220115 := bstep (se 1 (by rfl) ⟨165086, by rfl⟩ : syracuseStep 220115 = 330173) B330173
theorem B220243 : Blo 191804 220243 := bstep (se 1 (by rfl) ⟨165182, by rfl⟩ : syracuseStep 220243 = 330365) B330365
theorem B1105073 : Blo 191804 1105073 := bstep (se 2 (by rfl) ⟨414402, by rfl⟩ : syracuseStep 1105073 = 828805) B828805
theorem B875789 : Blo 191804 875789 := bstep (se 3 (by rfl) ⟨164210, by rfl⟩ : syracuseStep 875789 = 328421) B328421
theorem B351715 : Blo 191804 351715 := bstep (se 1 (by rfl) ⟨263786, by rfl⟩ : syracuseStep 351715 = 527573) B527573
theorem B2088629 : Blo 191804 2088629 := bstep (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) B195809
theorem B548653 : Blo 191804 548653 := bstep (se 3 (by rfl) ⟨102872, by rfl⟩ : syracuseStep 548653 = 205745) B205745
theorem B417649 : Blo 191804 417649 := bstep (se 2 (by rfl) ⟨156618, by rfl⟩ : syracuseStep 417649 = 313237) B313237
theorem B1335473 : Blo 191804 1335473 := bstep (se 2 (by rfl) ⟨500802, by rfl⟩ : syracuseStep 1335473 = 1001605) B1001605
theorem B647405 : Blo 191804 647405 := bstep (se 3 (by rfl) ⟨121388, by rfl⟩ : syracuseStep 647405 = 242777) B242777
theorem B418051 : Blo 191804 418051 := bstep (se 1 (by rfl) ⟨313538, by rfl⟩ : syracuseStep 418051 = 627077) B627077
theorem B647459 : Blo 191804 647459 := bstep (se 1 (by rfl) ⟨485594, by rfl⟩ : syracuseStep 647459 = 971189) B971189
theorem B647729 : Blo 191804 647729 := bstep (se 2 (by rfl) ⟨242898, by rfl⟩ : syracuseStep 647729 = 485797) B485797
theorem B1106531 : Blo 191804 1106531 := bstep (se 1 (by rfl) ⟨829898, by rfl⟩ : syracuseStep 1106531 = 1659797) B1659797
theorem B615043 : Blo 191804 615043 := bstep (se 1 (by rfl) ⟨461282, by rfl⟩ : syracuseStep 615043 = 922565) B922565
theorem B2450189 : Blo 191804 2450189 := bstep (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) B918821
theorem B615185 : Blo 191804 615185 := bstep (se 2 (by rfl) ⟨230694, by rfl⟩ : syracuseStep 615185 = 461389) B461389
theorem B287729 : Blo 191804 287729 := bstep (se 2 (by rfl) ⟨107898, by rfl⟩ : syracuseStep 287729 = 215797) B215797
theorem B287747 : Blo 191804 287747 := bstep (se 1 (by rfl) ⟨215810, by rfl⟩ : syracuseStep 287747 = 431621) B431621
theorem B287777 : Blo 191804 287777 := bstep (se 2 (by rfl) ⟨107916, by rfl⟩ : syracuseStep 287777 = 215833) B215833
theorem B287795 : Blo 191804 287795 := bstep (se 1 (by rfl) ⟨215846, by rfl⟩ : syracuseStep 287795 = 431693) B431693
theorem B648269 : Blo 191804 648269 := bstep (se 3 (by rfl) ⟨121550, by rfl⟩ : syracuseStep 648269 = 243101) B243101
theorem B287825 : Blo 191804 287825 := bstep (se 2 (by rfl) ⟨107934, by rfl⟩ : syracuseStep 287825 = 215869) B215869
theorem B287843 : Blo 191804 287843 := bstep (se 1 (by rfl) ⟨215882, by rfl⟩ : syracuseStep 287843 = 431765) B431765
theorem B287873 : Blo 191804 287873 := bstep (se 2 (by rfl) ⟨107952, by rfl⟩ : syracuseStep 287873 = 215905) B215905
theorem B648323 : Blo 191804 648323 := bstep (se 1 (by rfl) ⟨486242, by rfl⟩ : syracuseStep 648323 = 972485) B972485
theorem B287891 : Blo 191804 287891 := bstep (se 1 (by rfl) ⟨215918, by rfl⟩ : syracuseStep 287891 = 431837) B431837
theorem B287921 : Blo 191804 287921 := bstep (se 2 (by rfl) ⟨107970, by rfl⟩ : syracuseStep 287921 = 215941) B215941
theorem B976049 : Blo 191804 976049 := bstep (se 2 (by rfl) ⟨366018, by rfl⟩ : syracuseStep 976049 = 732037) B732037
theorem B287939 : Blo 191804 287939 := bstep (se 1 (by rfl) ⟨215954, by rfl⟩ : syracuseStep 287939 = 431909) B431909
theorem B287969 : Blo 191804 287969 := bstep (se 2 (by rfl) ⟨107988, by rfl⟩ : syracuseStep 287969 = 215977) B215977
theorem B287987 : Blo 191804 287987 := bstep (se 1 (by rfl) ⟨215990, by rfl⟩ : syracuseStep 287987 = 431981) B431981
theorem B288017 : Blo 191804 288017 := bstep (se 2 (by rfl) ⟨108006, by rfl⟩ : syracuseStep 288017 = 216013) B216013
theorem B288035 : Blo 191804 288035 := bstep (se 1 (by rfl) ⟨216026, by rfl⟩ : syracuseStep 288035 = 432053) B432053
theorem B288065 : Blo 191804 288065 := bstep (se 2 (by rfl) ⟨108024, by rfl⟩ : syracuseStep 288065 = 216049) B216049
theorem B288083 : Blo 191804 288083 := bstep (se 1 (by rfl) ⟨216062, by rfl⟩ : syracuseStep 288083 = 432125) B432125
theorem B288113 : Blo 191804 288113 := bstep (se 2 (by rfl) ⟨108042, by rfl⟩ : syracuseStep 288113 = 216085) B216085
theorem B288131 : Blo 191804 288131 := bstep (se 1 (by rfl) ⟨216098, by rfl⟩ : syracuseStep 288131 = 432197) B432197
theorem B648593 : Blo 191804 648593 := bstep (se 2 (by rfl) ⟨243222, by rfl⟩ : syracuseStep 648593 = 486445) B486445
theorem B288161 : Blo 191804 288161 := bstep (se 2 (by rfl) ⟨108060, by rfl⟩ : syracuseStep 288161 = 216121) B216121
theorem B288179 : Blo 191804 288179 := bstep (se 1 (by rfl) ⟨216134, by rfl⟩ : syracuseStep 288179 = 432269) B432269
theorem B288209 : Blo 191804 288209 := bstep (se 2 (by rfl) ⟨108078, by rfl⟩ : syracuseStep 288209 = 216157) B216157
theorem B288227 : Blo 191804 288227 := bstep (se 1 (by rfl) ⟨216170, by rfl⟩ : syracuseStep 288227 = 432341) B432341
theorem B550385 : Blo 191804 550385 := bstep (se 2 (by rfl) ⟨206394, by rfl⟩ : syracuseStep 550385 = 412789) B412789
theorem B288257 : Blo 191804 288257 := bstep (se 2 (by rfl) ⟨108096, by rfl⟩ : syracuseStep 288257 = 216193) B216193
theorem B288275 : Blo 191804 288275 := bstep (se 1 (by rfl) ⟨216206, by rfl⟩ : syracuseStep 288275 = 432413) B432413
theorem B288305 : Blo 191804 288305 := bstep (se 2 (by rfl) ⟨108114, by rfl⟩ : syracuseStep 288305 = 216229) B216229
theorem B288323 : Blo 191804 288323 := bstep (se 1 (by rfl) ⟨216242, by rfl⟩ : syracuseStep 288323 = 432485) B432485
theorem B1107533 : Blo 191804 1107533 := bstep (se 3 (by rfl) ⟨207662, by rfl⟩ : syracuseStep 1107533 = 415325) B415325
theorem B288353 : Blo 191804 288353 := bstep (se 2 (by rfl) ⟨108132, by rfl⟩ : syracuseStep 288353 = 216265) B216265
theorem B288371 : Blo 191804 288371 := bstep (se 1 (by rfl) ⟨216278, by rfl⟩ : syracuseStep 288371 = 432557) B432557
theorem B288401 : Blo 191804 288401 := bstep (se 2 (by rfl) ⟨108150, by rfl⟩ : syracuseStep 288401 = 216301) B216301
theorem B288419 : Blo 191804 288419 := bstep (se 1 (by rfl) ⟨216314, by rfl⟩ : syracuseStep 288419 = 432629) B432629
theorem B550577 : Blo 191804 550577 := bstep (se 2 (by rfl) ⟨206466, by rfl⟩ : syracuseStep 550577 = 412933) B412933
theorem B288449 : Blo 191804 288449 := bstep (se 2 (by rfl) ⟨108168, by rfl⟩ : syracuseStep 288449 = 216337) B216337
theorem B288467 : Blo 191804 288467 := bstep (se 1 (by rfl) ⟨216350, by rfl⟩ : syracuseStep 288467 = 432701) B432701
theorem B288497 : Blo 191804 288497 := bstep (se 2 (by rfl) ⟨108186, by rfl⟩ : syracuseStep 288497 = 216373) B216373
theorem B288515 : Blo 191804 288515 := bstep (se 1 (by rfl) ⟨216386, by rfl⟩ : syracuseStep 288515 = 432773) B432773
theorem B288545 : Blo 191804 288545 := bstep (se 2 (by rfl) ⟨108204, by rfl⟩ : syracuseStep 288545 = 216409) B216409
theorem B288563 : Blo 191804 288563 := bstep (se 1 (by rfl) ⟨216422, by rfl⟩ : syracuseStep 288563 = 432845) B432845
theorem B288593 : Blo 191804 288593 := bstep (se 2 (by rfl) ⟨108222, by rfl⟩ : syracuseStep 288593 = 216445) B216445
theorem B288611 : Blo 191804 288611 := bstep (se 1 (by rfl) ⟨216458, by rfl⟩ : syracuseStep 288611 = 432917) B432917
theorem B288641 : Blo 191804 288641 := bstep (se 2 (by rfl) ⟨108240, by rfl⟩ : syracuseStep 288641 = 216481) B216481
theorem B288659 : Blo 191804 288659 := bstep (se 1 (by rfl) ⟨216494, by rfl⟩ : syracuseStep 288659 = 432989) B432989
theorem B649133 : Blo 191804 649133 := bstep (se 3 (by rfl) ⟨121712, by rfl⟩ : syracuseStep 649133 = 243425) B243425
theorem B288689 : Blo 191804 288689 := bstep (se 2 (by rfl) ⟨108258, by rfl⟩ : syracuseStep 288689 = 216517) B216517
theorem B288707 : Blo 191804 288707 := bstep (se 1 (by rfl) ⟨216530, by rfl⟩ : syracuseStep 288707 = 433061) B433061
theorem B288737 : Blo 191804 288737 := bstep (se 2 (by rfl) ⟨108276, by rfl⟩ : syracuseStep 288737 = 216553) B216553
theorem B649187 : Blo 191804 649187 := bstep (se 1 (by rfl) ⟨486890, by rfl⟩ : syracuseStep 649187 = 973781) B973781
theorem B288755 : Blo 191804 288755 := bstep (se 1 (by rfl) ⟨216566, by rfl⟩ : syracuseStep 288755 = 433133) B433133
theorem B288785 : Blo 191804 288785 := bstep (se 2 (by rfl) ⟨108294, by rfl⟩ : syracuseStep 288785 = 216589) B216589
theorem B288803 : Blo 191804 288803 := bstep (se 1 (by rfl) ⟨216602, by rfl⟩ : syracuseStep 288803 = 433205) B433205
theorem B288833 : Blo 191804 288833 := bstep (se 2 (by rfl) ⟨108312, by rfl⟩ : syracuseStep 288833 = 216625) B216625
theorem B616529 : Blo 191804 616529 := bstep (se 2 (by rfl) ⟨231198, by rfl⟩ : syracuseStep 616529 = 462397) B462397
theorem B288851 : Blo 191804 288851 := bstep (se 1 (by rfl) ⟨216638, by rfl⟩ : syracuseStep 288851 = 433277) B433277
theorem B288881 : Blo 191804 288881 := bstep (se 2 (by rfl) ⟨108330, by rfl⟩ : syracuseStep 288881 = 216661) B216661
theorem B288899 : Blo 191804 288899 := bstep (se 1 (by rfl) ⟨216674, by rfl⟩ : syracuseStep 288899 = 433349) B433349
theorem B288929 : Blo 191804 288929 := bstep (se 2 (by rfl) ⟨108348, by rfl⟩ : syracuseStep 288929 = 216697) B216697
theorem B288947 : Blo 191804 288947 := bstep (se 1 (by rfl) ⟨216710, by rfl⟩ : syracuseStep 288947 = 433421) B433421
theorem B485585 : Blo 191804 485585 := bstep (se 2 (by rfl) ⟨182094, by rfl⟩ : syracuseStep 485585 = 364189) B364189
theorem B288977 : Blo 191804 288977 := bstep (se 2 (by rfl) ⟨108366, by rfl⟩ : syracuseStep 288977 = 216733) B216733
theorem B288995 : Blo 191804 288995 := bstep (se 1 (by rfl) ⟨216746, by rfl⟩ : syracuseStep 288995 = 433493) B433493
theorem B649457 : Blo 191804 649457 := bstep (se 2 (by rfl) ⟨243546, by rfl⟩ : syracuseStep 649457 = 487093) B487093
theorem B289025 : Blo 191804 289025 := bstep (se 2 (by rfl) ⟨108384, by rfl⟩ : syracuseStep 289025 = 216769) B216769
theorem B485635 : Blo 191804 485635 := bstep (se 1 (by rfl) ⟨364226, by rfl⟩ : syracuseStep 485635 = 728453) B728453
theorem B289043 : Blo 191804 289043 := bstep (se 1 (by rfl) ⟨216782, by rfl⟩ : syracuseStep 289043 = 433565) B433565
theorem B289073 : Blo 191804 289073 := bstep (se 2 (by rfl) ⟨108402, by rfl⟩ : syracuseStep 289073 = 216805) B216805
theorem B289091 : Blo 191804 289091 := bstep (se 1 (by rfl) ⟨216818, by rfl⟩ : syracuseStep 289091 = 433637) B433637
theorem B289121 : Blo 191804 289121 := bstep (se 2 (by rfl) ⟨108420, by rfl⟩ : syracuseStep 289121 = 216841) B216841
theorem B289139 : Blo 191804 289139 := bstep (se 1 (by rfl) ⟨216854, by rfl⟩ : syracuseStep 289139 = 433709) B433709
theorem B485777 : Blo 191804 485777 := bstep (se 2 (by rfl) ⟨182166, by rfl⟩ : syracuseStep 485777 = 364333) B364333
theorem B289169 : Blo 191804 289169 := bstep (se 2 (by rfl) ⟨108438, by rfl⟩ : syracuseStep 289169 = 216877) B216877
theorem B289187 : Blo 191804 289187 := bstep (se 1 (by rfl) ⟨216890, by rfl⟩ : syracuseStep 289187 = 433781) B433781
theorem B289217 : Blo 191804 289217 := bstep (se 2 (by rfl) ⟨108456, by rfl⟩ : syracuseStep 289217 = 216913) B216913
theorem B289235 : Blo 191804 289235 := bstep (se 1 (by rfl) ⟨216926, by rfl⟩ : syracuseStep 289235 = 433853) B433853
theorem B1993187 : Blo 191804 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B289265 : Blo 191804 289265 := bstep (se 2 (by rfl) ⟨108474, by rfl⟩ : syracuseStep 289265 = 216949) B216949
theorem B289283 : Blo 191804 289283 := bstep (se 1 (by rfl) ⟨216962, by rfl⟩ : syracuseStep 289283 = 433925) B433925
theorem B289313 : Blo 191804 289313 := bstep (se 2 (by rfl) ⟨108492, by rfl⟩ : syracuseStep 289313 = 216985) B216985
theorem B289331 : Blo 191804 289331 := bstep (se 1 (by rfl) ⟨216998, by rfl⟩ : syracuseStep 289331 = 433997) B433997
theorem B289361 : Blo 191804 289361 := bstep (se 2 (by rfl) ⟨108510, by rfl⟩ : syracuseStep 289361 = 217021) B217021
theorem B289379 : Blo 191804 289379 := bstep (se 1 (by rfl) ⟨217034, by rfl⟩ : syracuseStep 289379 = 434069) B434069
theorem B977507 : Blo 191804 977507 := bstep (se 1 (by rfl) ⟨733130, by rfl⟩ : syracuseStep 977507 = 1466261) B1466261
theorem B289409 : Blo 191804 289409 := bstep (se 2 (by rfl) ⟨108528, by rfl⟩ : syracuseStep 289409 = 217057) B217057
theorem B551569 : Blo 191804 551569 := bstep (se 2 (by rfl) ⟨206838, by rfl⟩ : syracuseStep 551569 = 413677) B413677
theorem B289427 : Blo 191804 289427 := bstep (se 1 (by rfl) ⟨217070, by rfl⟩ : syracuseStep 289427 = 434141) B434141
theorem B289457 : Blo 191804 289457 := bstep (se 2 (by rfl) ⟨108546, by rfl⟩ : syracuseStep 289457 = 217093) B217093
theorem B289475 : Blo 191804 289475 := bstep (se 1 (by rfl) ⟨217106, by rfl⟩ : syracuseStep 289475 = 434213) B434213
theorem B289505 : Blo 191804 289505 := bstep (se 2 (by rfl) ⟨108564, by rfl⟩ : syracuseStep 289505 = 217129) B217129
theorem B289523 : Blo 191804 289523 := bstep (se 1 (by rfl) ⟨217142, by rfl⟩ : syracuseStep 289523 = 434285) B434285
theorem B649997 : Blo 191804 649997 := bstep (se 3 (by rfl) ⟨121874, by rfl⟩ : syracuseStep 649997 = 243749) B243749
theorem B289553 : Blo 191804 289553 := bstep (se 2 (by rfl) ⟨108582, by rfl⟩ : syracuseStep 289553 = 217165) B217165
theorem B289571 : Blo 191804 289571 := bstep (se 1 (by rfl) ⟨217178, by rfl⟩ : syracuseStep 289571 = 434357) B434357
theorem B289601 : Blo 191804 289601 := bstep (se 2 (by rfl) ⟨108600, by rfl⟩ : syracuseStep 289601 = 217201) B217201
theorem B650051 : Blo 191804 650051 := bstep (se 1 (by rfl) ⟨487538, by rfl⟩ : syracuseStep 650051 = 975077) B975077
theorem B289619 : Blo 191804 289619 := bstep (se 1 (by rfl) ⟨217214, by rfl⟩ : syracuseStep 289619 = 434429) B434429
theorem B289649 : Blo 191804 289649 := bstep (se 2 (by rfl) ⟨108618, by rfl⟩ : syracuseStep 289649 = 217237) B217237
theorem B289667 : Blo 191804 289667 := bstep (se 1 (by rfl) ⟨217250, by rfl⟩ : syracuseStep 289667 = 434501) B434501
theorem B289697 : Blo 191804 289697 := bstep (se 2 (by rfl) ⟨108636, by rfl⟩ : syracuseStep 289697 = 217273) B217273
theorem B551843 : Blo 191804 551843 := bstep (se 1 (by rfl) ⟨413882, by rfl⟩ : syracuseStep 551843 = 827765) B827765
theorem B289715 : Blo 191804 289715 := bstep (se 1 (by rfl) ⟨217286, by rfl⟩ : syracuseStep 289715 = 434573) B434573
theorem B289745 : Blo 191804 289745 := bstep (se 2 (by rfl) ⟨108654, by rfl⟩ : syracuseStep 289745 = 217309) B217309
theorem B289763 : Blo 191804 289763 := bstep (se 1 (by rfl) ⟨217322, by rfl⟩ : syracuseStep 289763 = 434645) B434645
theorem B617453 : Blo 191804 617453 := bstep (se 3 (by rfl) ⟨115772, by rfl⟩ : syracuseStep 617453 = 231545) B231545
theorem B289793 : Blo 191804 289793 := bstep (se 2 (by rfl) ⟨108672, by rfl⟩ : syracuseStep 289793 = 217345) B217345
theorem B289811 : Blo 191804 289811 := bstep (se 1 (by rfl) ⟨217358, by rfl⟩ : syracuseStep 289811 = 434717) B434717
theorem B289841 : Blo 191804 289841 := bstep (se 2 (by rfl) ⟨108690, by rfl⟩ : syracuseStep 289841 = 217381) B217381
theorem B289859 : Blo 191804 289859 := bstep (se 1 (by rfl) ⟨217394, by rfl⟩ : syracuseStep 289859 = 434789) B434789
theorem B650321 : Blo 191804 650321 := bstep (se 2 (by rfl) ⟨243870, by rfl⟩ : syracuseStep 650321 = 487741) B487741
theorem B289889 : Blo 191804 289889 := bstep (se 2 (by rfl) ⟨108708, by rfl⟩ : syracuseStep 289889 = 217417) B217417
theorem B552035 : Blo 191804 552035 := bstep (se 1 (by rfl) ⟨414026, by rfl⟩ : syracuseStep 552035 = 828053) B828053
theorem B289907 : Blo 191804 289907 := bstep (se 1 (by rfl) ⟨217430, by rfl⟩ : syracuseStep 289907 = 434861) B434861
theorem B289937 : Blo 191804 289937 := bstep (se 2 (by rfl) ⟨108726, by rfl⟩ : syracuseStep 289937 = 217453) B217453
theorem B289955 : Blo 191804 289955 := bstep (se 1 (by rfl) ⟨217466, by rfl⟩ : syracuseStep 289955 = 434933) B434933
theorem B617645 : Blo 191804 617645 := bstep (se 3 (by rfl) ⟨115808, by rfl⟩ : syracuseStep 617645 = 231617) B231617
theorem B289985 : Blo 191804 289985 := bstep (se 2 (by rfl) ⟨108744, by rfl⟩ : syracuseStep 289985 = 217489) B217489
theorem B290003 : Blo 191804 290003 := bstep (se 1 (by rfl) ⟨217502, by rfl⟩ : syracuseStep 290003 = 435005) B435005
theorem B519409 : Blo 191804 519409 := bstep (se 2 (by rfl) ⟨194778, by rfl⟩ : syracuseStep 519409 = 389557) B389557
theorem B290033 : Blo 191804 290033 := bstep (se 2 (by rfl) ⟨108762, by rfl⟩ : syracuseStep 290033 = 217525) B217525
theorem B1404145 : Blo 191804 1404145 := bstep (se 2 (by rfl) ⟨526554, by rfl⟩ : syracuseStep 1404145 = 1053109) B1053109
theorem B290051 : Blo 191804 290051 := bstep (se 1 (by rfl) ⟨217538, by rfl⟩ : syracuseStep 290051 = 435077) B435077
theorem B290081 : Blo 191804 290081 := bstep (se 2 (by rfl) ⟨108780, by rfl⟩ : syracuseStep 290081 = 217561) B217561
theorem B290099 : Blo 191804 290099 := bstep (se 1 (by rfl) ⟨217574, by rfl⟩ : syracuseStep 290099 = 435149) B435149
theorem B191811 : Blo 191804 191811 := bstep (se 1 (by rfl) ⟨143858, by rfl⟩ : syracuseStep 191811 = 287717) B287717
theorem B290129 : Blo 191804 290129 := bstep (se 2 (by rfl) ⟨108798, by rfl⟩ : syracuseStep 290129 = 217597) B217597
theorem B191827 : Blo 191804 191827 := bstep (se 1 (by rfl) ⟨143870, by rfl⟩ : syracuseStep 191827 = 287741) B287741
theorem B191843 : Blo 191804 191843 := bstep (se 1 (by rfl) ⟨143882, by rfl⟩ : syracuseStep 191843 = 287765) B287765
theorem B290147 : Blo 191804 290147 := bstep (se 1 (by rfl) ⟨217610, by rfl⟩ : syracuseStep 290147 = 435221) B435221
theorem B486769 : Blo 191804 486769 := bstep (se 2 (by rfl) ⟨182538, by rfl⟩ : syracuseStep 486769 = 365077) B365077
theorem B191859 : Blo 191804 191859 := bstep (se 1 (by rfl) ⟨143894, by rfl⟩ : syracuseStep 191859 = 287789) B287789
theorem B290177 : Blo 191804 290177 := bstep (se 2 (by rfl) ⟨108816, by rfl⟩ : syracuseStep 290177 = 217633) B217633
theorem B191875 : Blo 191804 191875 := bstep (se 1 (by rfl) ⟨143906, by rfl⟩ : syracuseStep 191875 = 287813) B287813
theorem B978317 : Blo 191804 978317 := bstep (se 3 (by rfl) ⟨183434, by rfl⟩ : syracuseStep 978317 = 366869) B366869
theorem B191891 : Blo 191804 191891 := bstep (se 1 (by rfl) ⟨143918, by rfl⟩ : syracuseStep 191891 = 287837) B287837
theorem B290195 : Blo 191804 290195 := bstep (se 1 (by rfl) ⟨217646, by rfl⟩ : syracuseStep 290195 = 435293) B435293
theorem B191907 : Blo 191804 191907 := bstep (se 1 (by rfl) ⟨143930, by rfl⟩ : syracuseStep 191907 = 287861) B287861
theorem B290225 : Blo 191804 290225 := bstep (se 2 (by rfl) ⟨108834, by rfl⟩ : syracuseStep 290225 = 217669) B217669
theorem B191923 : Blo 191804 191923 := bstep (se 1 (by rfl) ⟨143942, by rfl⟩ : syracuseStep 191923 = 287885) B287885
theorem B191939 : Blo 191804 191939 := bstep (se 1 (by rfl) ⟨143954, by rfl⟩ : syracuseStep 191939 = 287909) B287909
theorem B290243 : Blo 191804 290243 := bstep (se 1 (by rfl) ⟨217682, by rfl⟩ : syracuseStep 290243 = 435365) B435365
theorem B191955 : Blo 191804 191955 := bstep (se 1 (by rfl) ⟨143966, by rfl⟩ : syracuseStep 191955 = 287933) B287933
theorem B290273 : Blo 191804 290273 := bstep (se 2 (by rfl) ⟨108852, by rfl⟩ : syracuseStep 290273 = 217705) B217705
theorem B191971 : Blo 191804 191971 := bstep (se 1 (by rfl) ⟨143978, by rfl⟩ : syracuseStep 191971 = 287957) B287957
theorem B191987 : Blo 191804 191987 := bstep (se 1 (by rfl) ⟨143990, by rfl⟩ : syracuseStep 191987 = 287981) B287981
theorem B290291 : Blo 191804 290291 := bstep (se 1 (by rfl) ⟨217718, by rfl⟩ : syracuseStep 290291 = 435437) B435437
theorem B192003 : Blo 191804 192003 := bstep (se 1 (by rfl) ⟨144002, by rfl⟩ : syracuseStep 192003 = 288005) B288005
theorem B290321 : Blo 191804 290321 := bstep (se 2 (by rfl) ⟨108870, by rfl⟩ : syracuseStep 290321 = 217741) B217741
theorem B192019 : Blo 191804 192019 := bstep (se 1 (by rfl) ⟨144014, by rfl⟩ : syracuseStep 192019 = 288029) B288029
theorem B192035 : Blo 191804 192035 := bstep (se 1 (by rfl) ⟨144026, by rfl⟩ : syracuseStep 192035 = 288053) B288053
theorem B290339 : Blo 191804 290339 := bstep (se 1 (by rfl) ⟨217754, by rfl⟩ : syracuseStep 290339 = 435509) B435509
theorem B192051 : Blo 191804 192051 := bstep (se 1 (by rfl) ⟨144038, by rfl⟩ : syracuseStep 192051 = 288077) B288077
theorem B290369 : Blo 191804 290369 := bstep (se 2 (by rfl) ⟨108888, by rfl⟩ : syracuseStep 290369 = 217777) B217777
theorem B192067 : Blo 191804 192067 := bstep (se 1 (by rfl) ⟨144050, by rfl⟩ : syracuseStep 192067 = 288101) B288101
theorem B192083 : Blo 191804 192083 := bstep (se 1 (by rfl) ⟨144062, by rfl⟩ : syracuseStep 192083 = 288125) B288125
theorem B290387 : Blo 191804 290387 := bstep (se 1 (by rfl) ⟨217790, by rfl⟩ : syracuseStep 290387 = 435581) B435581
theorem B192099 : Blo 191804 192099 := bstep (se 1 (by rfl) ⟨144074, by rfl⟩ : syracuseStep 192099 = 288149) B288149
theorem B650861 : Blo 191804 650861 := bstep (se 3 (by rfl) ⟨122036, by rfl⟩ : syracuseStep 650861 = 244073) B244073
theorem B290417 : Blo 191804 290417 := bstep (se 2 (by rfl) ⟨108906, by rfl⟩ : syracuseStep 290417 = 217813) B217813
theorem B192115 : Blo 191804 192115 := bstep (se 1 (by rfl) ⟨144086, by rfl⟩ : syracuseStep 192115 = 288173) B288173
theorem B192131 : Blo 191804 192131 := bstep (se 1 (by rfl) ⟨144098, by rfl⟩ : syracuseStep 192131 = 288197) B288197
theorem B487043 : Blo 191804 487043 := bstep (se 1 (by rfl) ⟨365282, by rfl⟩ : syracuseStep 487043 = 730565) B730565
theorem B290435 : Blo 191804 290435 := bstep (se 1 (by rfl) ⟨217826, by rfl⟩ : syracuseStep 290435 = 435653) B435653
theorem B192147 : Blo 191804 192147 := bstep (se 1 (by rfl) ⟨144110, by rfl⟩ : syracuseStep 192147 = 288221) B288221
theorem B290465 : Blo 191804 290465 := bstep (se 2 (by rfl) ⟨108924, by rfl⟩ : syracuseStep 290465 = 217849) B217849
theorem B192163 : Blo 191804 192163 := bstep (se 1 (by rfl) ⟨144122, by rfl⟩ : syracuseStep 192163 = 288245) B288245
theorem B650915 : Blo 191804 650915 := bstep (se 1 (by rfl) ⟨488186, by rfl⟩ : syracuseStep 650915 = 976373) B976373
theorem B192179 : Blo 191804 192179 := bstep (se 1 (by rfl) ⟨144134, by rfl⟩ : syracuseStep 192179 = 288269) B288269
theorem B290483 : Blo 191804 290483 := bstep (se 1 (by rfl) ⟨217862, by rfl⟩ : syracuseStep 290483 = 435725) B435725
theorem B192195 : Blo 191804 192195 := bstep (se 1 (by rfl) ⟨144146, by rfl⟩ : syracuseStep 192195 = 288293) B288293
theorem B1470149 : Blo 191804 1470149 := bstep (se 4 (by rfl) ⟨137826, by rfl⟩ : syracuseStep 1470149 = 275653) B275653
theorem B290513 : Blo 191804 290513 := bstep (se 2 (by rfl) ⟨108942, by rfl⟩ : syracuseStep 290513 = 217885) B217885
theorem B192211 : Blo 191804 192211 := bstep (se 1 (by rfl) ⟨144158, by rfl⟩ : syracuseStep 192211 = 288317) B288317
theorem B192227 : Blo 191804 192227 := bstep (se 1 (by rfl) ⟨144170, by rfl⟩ : syracuseStep 192227 = 288341) B288341
theorem B290531 : Blo 191804 290531 := bstep (se 1 (by rfl) ⟨217898, by rfl⟩ : syracuseStep 290531 = 435797) B435797
theorem B192243 : Blo 191804 192243 := bstep (se 1 (by rfl) ⟨144182, by rfl⟩ : syracuseStep 192243 = 288365) B288365
theorem B290561 : Blo 191804 290561 := bstep (se 2 (by rfl) ⟨108960, by rfl⟩ : syracuseStep 290561 = 217921) B217921
theorem B192259 : Blo 191804 192259 := bstep (se 1 (by rfl) ⟨144194, by rfl⟩ : syracuseStep 192259 = 288389) B288389
theorem B192275 : Blo 191804 192275 := bstep (se 1 (by rfl) ⟨144206, by rfl⟩ : syracuseStep 192275 = 288413) B288413
theorem B290579 : Blo 191804 290579 := bstep (se 1 (by rfl) ⟨217934, by rfl⟩ : syracuseStep 290579 = 435869) B435869
theorem B192291 : Blo 191804 192291 := bstep (se 1 (by rfl) ⟨144218, by rfl⟩ : syracuseStep 192291 = 288437) B288437
theorem B290609 : Blo 191804 290609 := bstep (se 2 (by rfl) ⟨108978, by rfl⟩ : syracuseStep 290609 = 217957) B217957
theorem B192307 : Blo 191804 192307 := bstep (se 1 (by rfl) ⟨144230, by rfl⟩ : syracuseStep 192307 = 288461) B288461
theorem B192323 : Blo 191804 192323 := bstep (se 1 (by rfl) ⟨144242, by rfl⟩ : syracuseStep 192323 = 288485) B288485
theorem B487235 : Blo 191804 487235 := bstep (se 1 (by rfl) ⟨365426, by rfl⟩ : syracuseStep 487235 = 730853) B730853
theorem B290627 : Blo 191804 290627 := bstep (se 1 (by rfl) ⟨217970, by rfl⟩ : syracuseStep 290627 = 435941) B435941
theorem B192339 : Blo 191804 192339 := bstep (se 1 (by rfl) ⟨144254, by rfl⟩ : syracuseStep 192339 = 288509) B288509
theorem B290657 : Blo 191804 290657 := bstep (se 2 (by rfl) ⟨108996, by rfl⟩ : syracuseStep 290657 = 217993) B217993
theorem B192355 : Blo 191804 192355 := bstep (se 1 (by rfl) ⟨144266, by rfl⟩ : syracuseStep 192355 = 288533) B288533
theorem B192371 : Blo 191804 192371 := bstep (se 1 (by rfl) ⟨144278, by rfl⟩ : syracuseStep 192371 = 288557) B288557
theorem B290675 : Blo 191804 290675 := bstep (se 1 (by rfl) ⟨218006, by rfl⟩ : syracuseStep 290675 = 436013) B436013
theorem B192387 : Blo 191804 192387 := bstep (se 1 (by rfl) ⟨144290, by rfl⟩ : syracuseStep 192387 = 288581) B288581
theorem B552845 : Blo 191804 552845 := bstep (se 3 (by rfl) ⟨103658, by rfl⟩ : syracuseStep 552845 = 207317) B207317
theorem B290705 : Blo 191804 290705 := bstep (se 2 (by rfl) ⟨109014, by rfl⟩ : syracuseStep 290705 = 218029) B218029
theorem B192403 : Blo 191804 192403 := bstep (se 1 (by rfl) ⟨144302, by rfl⟩ : syracuseStep 192403 = 288605) B288605
theorem B192419 : Blo 191804 192419 := bstep (se 1 (by rfl) ⟨144314, by rfl⟩ : syracuseStep 192419 = 288629) B288629
theorem B782243 : Blo 191804 782243 := bstep (se 1 (by rfl) ⟨586682, by rfl⟩ : syracuseStep 782243 = 1173365) B1173365
theorem B290723 : Blo 191804 290723 := bstep (se 1 (by rfl) ⟨218042, by rfl⟩ : syracuseStep 290723 = 436085) B436085
theorem B651185 : Blo 191804 651185 := bstep (se 2 (by rfl) ⟨244194, by rfl⟩ : syracuseStep 651185 = 488389) B488389
theorem B192435 : Blo 191804 192435 := bstep (se 1 (by rfl) ⟨144326, by rfl⟩ : syracuseStep 192435 = 288653) B288653
theorem B290753 : Blo 191804 290753 := bstep (se 2 (by rfl) ⟨109032, by rfl⟩ : syracuseStep 290753 = 218065) B218065
theorem B192451 : Blo 191804 192451 := bstep (se 1 (by rfl) ⟨144338, by rfl⟩ : syracuseStep 192451 = 288677) B288677
theorem B192467 : Blo 191804 192467 := bstep (se 1 (by rfl) ⟨144350, by rfl⟩ : syracuseStep 192467 = 288701) B288701
theorem B290771 : Blo 191804 290771 := bstep (se 1 (by rfl) ⟨218078, by rfl⟩ : syracuseStep 290771 = 436157) B436157
theorem B192483 : Blo 191804 192483 := bstep (se 1 (by rfl) ⟨144362, by rfl⟩ : syracuseStep 192483 = 288725) B288725
theorem B290801 : Blo 191804 290801 := bstep (se 2 (by rfl) ⟨109050, by rfl⟩ : syracuseStep 290801 = 218101) B218101
theorem B192499 : Blo 191804 192499 := bstep (se 1 (by rfl) ⟨144374, by rfl⟩ : syracuseStep 192499 = 288749) B288749
theorem B192515 : Blo 191804 192515 := bstep (se 1 (by rfl) ⟨144386, by rfl⟩ : syracuseStep 192515 = 288773) B288773
theorem B290819 : Blo 191804 290819 := bstep (se 1 (by rfl) ⟨218114, by rfl⟩ : syracuseStep 290819 = 436229) B436229
theorem B2191373 : Blo 191804 2191373 := bstep (se 3 (by rfl) ⟨410882, by rfl⟩ : syracuseStep 2191373 = 821765) B821765
theorem B192531 : Blo 191804 192531 := bstep (se 1 (by rfl) ⟨144398, by rfl⟩ : syracuseStep 192531 = 288797) B288797
theorem B290849 : Blo 191804 290849 := bstep (se 2 (by rfl) ⟨109068, by rfl⟩ : syracuseStep 290849 = 218137) B218137
theorem B192547 : Blo 191804 192547 := bstep (se 1 (by rfl) ⟨144410, by rfl⟩ : syracuseStep 192547 = 288821) B288821
theorem B192563 : Blo 191804 192563 := bstep (se 1 (by rfl) ⟨144422, by rfl⟩ : syracuseStep 192563 = 288845) B288845
theorem B290867 : Blo 191804 290867 := bstep (se 1 (by rfl) ⟨218150, by rfl⟩ : syracuseStep 290867 = 436301) B436301
theorem B192579 : Blo 191804 192579 := bstep (se 1 (by rfl) ⟨144434, by rfl⟩ : syracuseStep 192579 = 288869) B288869
theorem B553027 : Blo 191804 553027 := bstep (se 1 (by rfl) ⟨414770, by rfl⟩ : syracuseStep 553027 = 829541) B829541
theorem B290897 : Blo 191804 290897 := bstep (se 2 (by rfl) ⟨109086, by rfl⟩ : syracuseStep 290897 = 218173) B218173
theorem B192595 : Blo 191804 192595 := bstep (se 1 (by rfl) ⟨144446, by rfl⟩ : syracuseStep 192595 = 288893) B288893
theorem B192611 : Blo 191804 192611 := bstep (se 1 (by rfl) ⟨144458, by rfl⟩ : syracuseStep 192611 = 288917) B288917
theorem B290915 : Blo 191804 290915 := bstep (se 1 (by rfl) ⟨218186, by rfl⟩ : syracuseStep 290915 = 436373) B436373
theorem B192627 : Blo 191804 192627 := bstep (se 1 (by rfl) ⟨144470, by rfl⟩ : syracuseStep 192627 = 288941) B288941
theorem B290945 : Blo 191804 290945 := bstep (se 2 (by rfl) ⟨109104, by rfl⟩ : syracuseStep 290945 = 218209) B218209
theorem B192643 : Blo 191804 192643 := bstep (se 1 (by rfl) ⟨144482, by rfl⟩ : syracuseStep 192643 = 288965) B288965
theorem B192659 : Blo 191804 192659 := bstep (se 1 (by rfl) ⟨144494, by rfl⟩ : syracuseStep 192659 = 288989) B288989
theorem B290963 : Blo 191804 290963 := bstep (se 1 (by rfl) ⟨218222, by rfl⟩ : syracuseStep 290963 = 436445) B436445
theorem B192675 : Blo 191804 192675 := bstep (se 1 (by rfl) ⟨144506, by rfl⟩ : syracuseStep 192675 = 289013) B289013
theorem B290993 : Blo 191804 290993 := bstep (se 2 (by rfl) ⟨109122, by rfl⟩ : syracuseStep 290993 = 218245) B218245
theorem B192691 : Blo 191804 192691 := bstep (se 1 (by rfl) ⟨144518, by rfl⟩ : syracuseStep 192691 = 289037) B289037
theorem B323777 : Blo 191804 323777 := bstep (se 2 (by rfl) ⟨121416, by rfl⟩ : syracuseStep 323777 = 242833) B242833
theorem B192707 : Blo 191804 192707 := bstep (se 1 (by rfl) ⟨144530, by rfl⟩ : syracuseStep 192707 = 289061) B289061
theorem B291011 : Blo 191804 291011 := bstep (se 1 (by rfl) ⟨218258, by rfl⟩ : syracuseStep 291011 = 436517) B436517
theorem B192723 : Blo 191804 192723 := bstep (se 1 (by rfl) ⟨144542, by rfl⟩ : syracuseStep 192723 = 289085) B289085
theorem B291041 : Blo 191804 291041 := bstep (se 2 (by rfl) ⟨109140, by rfl⟩ : syracuseStep 291041 = 218281) B218281
theorem B192739 : Blo 191804 192739 := bstep (se 1 (by rfl) ⟨144554, by rfl⟩ : syracuseStep 192739 = 289109) B289109
theorem B6254819 : Blo 191804 6254819 := bstep (se 1 (by rfl) ⟨4691114, by rfl⟩ : syracuseStep 6254819 = 9382229) B9382229
theorem B192755 : Blo 191804 192755 := bstep (se 1 (by rfl) ⟨144566, by rfl⟩ : syracuseStep 192755 = 289133) B289133
theorem B291059 : Blo 191804 291059 := bstep (se 1 (by rfl) ⟨218294, by rfl⟩ : syracuseStep 291059 = 436589) B436589
theorem B192771 : Blo 191804 192771 := bstep (se 1 (by rfl) ⟨144578, by rfl⟩ : syracuseStep 192771 = 289157) B289157
theorem B291089 : Blo 191804 291089 := bstep (se 2 (by rfl) ⟨109158, by rfl⟩ : syracuseStep 291089 = 218317) B218317
theorem B192787 : Blo 191804 192787 := bstep (se 1 (by rfl) ⟨144590, by rfl⟩ : syracuseStep 192787 = 289181) B289181
theorem B192803 : Blo 191804 192803 := bstep (se 1 (by rfl) ⟨144602, by rfl⟩ : syracuseStep 192803 = 289205) B289205
theorem B291107 : Blo 191804 291107 := bstep (se 1 (by rfl) ⟨218330, by rfl⟩ : syracuseStep 291107 = 436661) B436661
theorem B192819 : Blo 191804 192819 := bstep (se 1 (by rfl) ⟨144614, by rfl⟩ : syracuseStep 192819 = 289229) B289229
theorem B323905 : Blo 191804 323905 := bstep (se 2 (by rfl) ⟨121464, by rfl⟩ : syracuseStep 323905 = 242929) B242929
theorem B291137 : Blo 191804 291137 := bstep (se 2 (by rfl) ⟨109176, by rfl⟩ : syracuseStep 291137 = 218353) B218353
theorem B192835 : Blo 191804 192835 := bstep (se 1 (by rfl) ⟨144626, by rfl⟩ : syracuseStep 192835 = 289253) B289253
theorem B192851 : Blo 191804 192851 := bstep (se 1 (by rfl) ⟨144638, by rfl⟩ : syracuseStep 192851 = 289277) B289277
theorem B291155 : Blo 191804 291155 := bstep (se 1 (by rfl) ⟨218366, by rfl⟩ : syracuseStep 291155 = 436733) B436733
theorem B323939 : Blo 191804 323939 := bstep (se 1 (by rfl) ⟨242954, by rfl⟩ : syracuseStep 323939 = 485909) B485909
theorem B192867 : Blo 191804 192867 := bstep (se 1 (by rfl) ⟨144650, by rfl⟩ : syracuseStep 192867 = 289301) B289301
theorem B291185 : Blo 191804 291185 := bstep (se 2 (by rfl) ⟨109194, by rfl⟩ : syracuseStep 291185 = 218389) B218389
theorem B192883 : Blo 191804 192883 := bstep (se 1 (by rfl) ⟨144662, by rfl⟩ : syracuseStep 192883 = 289325) B289325
theorem B422275 : Blo 191804 422275 := bstep (se 1 (by rfl) ⟨316706, by rfl⟩ : syracuseStep 422275 = 633413) B633413
theorem B192899 : Blo 191804 192899 := bstep (se 1 (by rfl) ⟨144674, by rfl⟩ : syracuseStep 192899 = 289349) B289349
theorem B291203 : Blo 191804 291203 := bstep (se 1 (by rfl) ⟨218402, by rfl⟩ : syracuseStep 291203 = 436805) B436805
theorem B192915 : Blo 191804 192915 := bstep (se 1 (by rfl) ⟨144686, by rfl⟩ : syracuseStep 192915 = 289373) B289373
theorem B291233 : Blo 191804 291233 := bstep (se 2 (by rfl) ⟨109212, by rfl⟩ : syracuseStep 291233 = 218425) B218425
theorem B192931 : Blo 191804 192931 := bstep (se 1 (by rfl) ⟨144698, by rfl⟩ : syracuseStep 192931 = 289397) B289397
theorem B1110449 : Blo 191804 1110449 := bstep (se 2 (by rfl) ⟨416418, by rfl⟩ : syracuseStep 1110449 = 832837) B832837
theorem B192947 : Blo 191804 192947 := bstep (se 1 (by rfl) ⟨144710, by rfl⟩ : syracuseStep 192947 = 289421) B289421
theorem B291251 : Blo 191804 291251 := bstep (se 1 (by rfl) ⟨218438, by rfl⟩ : syracuseStep 291251 = 436877) B436877
theorem B192963 : Blo 191804 192963 := bstep (se 1 (by rfl) ⟨144722, by rfl⟩ : syracuseStep 192963 = 289445) B289445
theorem B651725 : Blo 191804 651725 := bstep (se 3 (by rfl) ⟨122198, by rfl⟩ : syracuseStep 651725 = 244397) B244397
theorem B291281 : Blo 191804 291281 := bstep (se 2 (by rfl) ⟨109230, by rfl⟩ : syracuseStep 291281 = 218461) B218461
theorem B192979 : Blo 191804 192979 := bstep (se 1 (by rfl) ⟨144734, by rfl⟩ : syracuseStep 192979 = 289469) B289469
theorem B324067 : Blo 191804 324067 := bstep (se 1 (by rfl) ⟨243050, by rfl⟩ : syracuseStep 324067 = 486101) B486101
theorem B192995 : Blo 191804 192995 := bstep (se 1 (by rfl) ⟨144746, by rfl⟩ : syracuseStep 192995 = 289493) B289493
theorem B291299 : Blo 191804 291299 := bstep (se 1 (by rfl) ⟨218474, by rfl⟩ : syracuseStep 291299 = 436949) B436949
theorem B193011 : Blo 191804 193011 := bstep (se 1 (by rfl) ⟨144758, by rfl⟩ : syracuseStep 193011 = 289517) B289517
theorem B291329 : Blo 191804 291329 := bstep (se 2 (by rfl) ⟨109248, by rfl⟩ : syracuseStep 291329 = 218497) B218497
theorem B193027 : Blo 191804 193027 := bstep (se 1 (by rfl) ⟨144770, by rfl⟩ : syracuseStep 193027 = 289541) B289541
theorem B651779 : Blo 191804 651779 := bstep (se 1 (by rfl) ⟨488834, by rfl⟩ : syracuseStep 651779 = 977669) B977669
theorem B193043 : Blo 191804 193043 := bstep (se 1 (by rfl) ⟨144782, by rfl⟩ : syracuseStep 193043 = 289565) B289565
theorem B291347 : Blo 191804 291347 := bstep (se 1 (by rfl) ⟨218510, by rfl⟩ : syracuseStep 291347 = 437021) B437021
theorem B193059 : Blo 191804 193059 := bstep (se 1 (by rfl) ⟨144794, by rfl⟩ : syracuseStep 193059 = 289589) B289589
theorem B553517 : Blo 191804 553517 := bstep (se 3 (by rfl) ⟨103784, by rfl⟩ : syracuseStep 553517 = 207569) B207569
theorem B291377 : Blo 191804 291377 := bstep (se 2 (by rfl) ⟨109266, by rfl⟩ : syracuseStep 291377 = 218533) B218533
theorem B193075 : Blo 191804 193075 := bstep (se 1 (by rfl) ⟨144806, by rfl⟩ : syracuseStep 193075 = 289613) B289613
theorem B193091 : Blo 191804 193091 := bstep (se 1 (by rfl) ⟨144818, by rfl⟩ : syracuseStep 193091 = 289637) B289637
theorem B291395 : Blo 191804 291395 := bstep (se 1 (by rfl) ⟨218546, by rfl⟩ : syracuseStep 291395 = 437093) B437093
theorem B1241669 : Blo 191804 1241669 := bstep (se 4 (by rfl) ⟨116406, by rfl⟩ : syracuseStep 1241669 = 232813) B232813
theorem B193107 : Blo 191804 193107 := bstep (se 1 (by rfl) ⟨144830, by rfl⟩ : syracuseStep 193107 = 289661) B289661
theorem B291425 : Blo 191804 291425 := bstep (se 2 (by rfl) ⟨109284, by rfl⟩ : syracuseStep 291425 = 218569) B218569
theorem B193123 : Blo 191804 193123 := bstep (se 1 (by rfl) ⟨144842, by rfl⟩ : syracuseStep 193123 = 289685) B289685
theorem B324209 : Blo 191804 324209 := bstep (se 2 (by rfl) ⟨121578, by rfl⟩ : syracuseStep 324209 = 243157) B243157
theorem B193139 : Blo 191804 193139 := bstep (se 1 (by rfl) ⟨144854, by rfl⟩ : syracuseStep 193139 = 289709) B289709
theorem B291443 : Blo 191804 291443 := bstep (se 1 (by rfl) ⟨218582, by rfl⟩ : syracuseStep 291443 = 437165) B437165
theorem B193155 : Blo 191804 193155 := bstep (se 1 (by rfl) ⟨144866, by rfl⟩ : syracuseStep 193155 = 289733) B289733
theorem B291473 : Blo 191804 291473 := bstep (se 2 (by rfl) ⟨109302, by rfl⟩ : syracuseStep 291473 = 218605) B218605
theorem B193171 : Blo 191804 193171 := bstep (se 1 (by rfl) ⟨144878, by rfl⟩ : syracuseStep 193171 = 289757) B289757
theorem B193187 : Blo 191804 193187 := bstep (se 1 (by rfl) ⟨144890, by rfl⟩ : syracuseStep 193187 = 289781) B289781
theorem B291491 : Blo 191804 291491 := bstep (se 1 (by rfl) ⟨218618, by rfl⟩ : syracuseStep 291491 = 437237) B437237
theorem B193203 : Blo 191804 193203 := bstep (se 1 (by rfl) ⟨144902, by rfl⟩ : syracuseStep 193203 = 289805) B289805
theorem B291521 : Blo 191804 291521 := bstep (se 2 (by rfl) ⟨109320, by rfl⟩ : syracuseStep 291521 = 218641) B218641
theorem B193219 : Blo 191804 193219 := bstep (se 1 (by rfl) ⟨144914, by rfl⟩ : syracuseStep 193219 = 289829) B289829
theorem B193235 : Blo 191804 193235 := bstep (se 1 (by rfl) ⟨144926, by rfl⟩ : syracuseStep 193235 = 289853) B289853
theorem B291539 : Blo 191804 291539 := bstep (se 1 (by rfl) ⟨218654, by rfl⟩ : syracuseStep 291539 = 437309) B437309
theorem B193251 : Blo 191804 193251 := bstep (se 1 (by rfl) ⟨144938, by rfl⟩ : syracuseStep 193251 = 289877) B289877
theorem B324337 : Blo 191804 324337 := bstep (se 2 (by rfl) ⟨121626, by rfl⟩ : syracuseStep 324337 = 243253) B243253
theorem B488177 : Blo 191804 488177 := bstep (se 2 (by rfl) ⟨183066, by rfl⟩ : syracuseStep 488177 = 366133) B366133
theorem B193267 : Blo 191804 193267 := bstep (se 1 (by rfl) ⟨144950, by rfl⟩ : syracuseStep 193267 = 289901) B289901
theorem B291569 : Blo 191804 291569 := bstep (se 2 (by rfl) ⟨109338, by rfl⟩ : syracuseStep 291569 = 218677) B218677
theorem B193283 : Blo 191804 193283 := bstep (se 1 (by rfl) ⟨144962, by rfl⟩ : syracuseStep 193283 = 289925) B289925
theorem B291587 : Blo 191804 291587 := bstep (se 1 (by rfl) ⟨218690, by rfl⟩ : syracuseStep 291587 = 437381) B437381
theorem B652049 : Blo 191804 652049 := bstep (se 2 (by rfl) ⟨244518, by rfl⟩ : syracuseStep 652049 = 489037) B489037
theorem B324371 : Blo 191804 324371 := bstep (se 1 (by rfl) ⟨243278, by rfl⟩ : syracuseStep 324371 = 486557) B486557
theorem B193299 : Blo 191804 193299 := bstep (se 1 (by rfl) ⟨144974, by rfl⟩ : syracuseStep 193299 = 289949) B289949
theorem B291617 : Blo 191804 291617 := bstep (se 2 (by rfl) ⟨109356, by rfl⟩ : syracuseStep 291617 = 218713) B218713
theorem B488227 : Blo 191804 488227 := bstep (se 1 (by rfl) ⟨366170, by rfl⟩ : syracuseStep 488227 = 732341) B732341
theorem B193315 : Blo 191804 193315 := bstep (se 1 (by rfl) ⟨144986, by rfl⟩ : syracuseStep 193315 = 289973) B289973
theorem B193331 : Blo 191804 193331 := bstep (se 1 (by rfl) ⟨144998, by rfl⟩ : syracuseStep 193331 = 289997) B289997
theorem B291635 : Blo 191804 291635 := bstep (se 1 (by rfl) ⟨218726, by rfl⟩ : syracuseStep 291635 = 437453) B437453
theorem B193347 : Blo 191804 193347 := bstep (se 1 (by rfl) ⟨145010, by rfl⟩ : syracuseStep 193347 = 290021) B290021
theorem B291665 : Blo 191804 291665 := bstep (se 2 (by rfl) ⟨109374, by rfl⟩ : syracuseStep 291665 = 218749) B218749
theorem B193363 : Blo 191804 193363 := bstep (se 1 (by rfl) ⟨145022, by rfl⟩ : syracuseStep 193363 = 290045) B290045
theorem B193379 : Blo 191804 193379 := bstep (se 1 (by rfl) ⟨145034, by rfl⟩ : syracuseStep 193379 = 290069) B290069
theorem B2356067 : Blo 191804 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B291683 : Blo 191804 291683 := bstep (se 1 (by rfl) ⟨218762, by rfl⟩ : syracuseStep 291683 = 437525) B437525
theorem B193395 : Blo 191804 193395 := bstep (se 1 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 193395 = 290093) B290093
theorem B291713 : Blo 191804 291713 := bstep (se 2 (by rfl) ⟨109392, by rfl⟩ : syracuseStep 291713 = 218785) B218785
theorem B193411 : Blo 191804 193411 := bstep (se 1 (by rfl) ⟨145058, by rfl⟩ : syracuseStep 193411 = 290117) B290117
theorem B324499 : Blo 191804 324499 := bstep (se 1 (by rfl) ⟨243374, by rfl⟩ : syracuseStep 324499 = 486749) B486749
theorem B193427 : Blo 191804 193427 := bstep (se 1 (by rfl) ⟨145070, by rfl⟩ : syracuseStep 193427 = 290141) B290141
theorem B291731 : Blo 191804 291731 := bstep (se 1 (by rfl) ⟨218798, by rfl⟩ : syracuseStep 291731 = 437597) B437597
theorem B619427 : Blo 191804 619427 := bstep (se 1 (by rfl) ⟨464570, by rfl⟩ : syracuseStep 619427 = 929141) B929141
theorem B193443 : Blo 191804 193443 := bstep (se 1 (by rfl) ⟨145082, by rfl⟩ : syracuseStep 193443 = 290165) B290165
theorem B488369 : Blo 191804 488369 := bstep (se 2 (by rfl) ⟨183138, by rfl⟩ : syracuseStep 488369 = 366277) B366277
theorem B291761 : Blo 191804 291761 := bstep (se 2 (by rfl) ⟨109410, by rfl⟩ : syracuseStep 291761 = 218821) B218821
theorem B193459 : Blo 191804 193459 := bstep (se 1 (by rfl) ⟨145094, by rfl⟩ : syracuseStep 193459 = 290189) B290189
theorem B193475 : Blo 191804 193475 := bstep (se 1 (by rfl) ⟨145106, by rfl⟩ : syracuseStep 193475 = 290213) B290213
theorem B291779 : Blo 191804 291779 := bstep (se 1 (by rfl) ⟨218834, by rfl⟩ : syracuseStep 291779 = 437669) B437669
theorem B193491 : Blo 191804 193491 := bstep (se 1 (by rfl) ⟨145118, by rfl⟩ : syracuseStep 193491 = 290237) B290237
theorem B291809 : Blo 191804 291809 := bstep (se 2 (by rfl) ⟨109428, by rfl⟩ : syracuseStep 291809 = 218857) B218857
theorem B193507 : Blo 191804 193507 := bstep (se 1 (by rfl) ⟨145130, by rfl⟩ : syracuseStep 193507 = 290261) B290261
theorem B193523 : Blo 191804 193523 := bstep (se 1 (by rfl) ⟨145142, by rfl⟩ : syracuseStep 193523 = 290285) B290285
theorem B291827 : Blo 191804 291827 := bstep (se 1 (by rfl) ⟨218870, by rfl⟩ : syracuseStep 291827 = 437741) B437741
theorem B193539 : Blo 191804 193539 := bstep (se 1 (by rfl) ⟨145154, by rfl⟩ : syracuseStep 193539 = 290309) B290309
theorem B291857 : Blo 191804 291857 := bstep (se 2 (by rfl) ⟨109446, by rfl⟩ : syracuseStep 291857 = 218893) B218893
theorem B193555 : Blo 191804 193555 := bstep (se 1 (by rfl) ⟨145166, by rfl⟩ : syracuseStep 193555 = 290333) B290333
theorem B324641 : Blo 191804 324641 := bstep (se 2 (by rfl) ⟨121740, by rfl⟩ : syracuseStep 324641 = 243481) B243481
theorem B193571 : Blo 191804 193571 := bstep (se 1 (by rfl) ⟨145178, by rfl⟩ : syracuseStep 193571 = 290357) B290357
theorem B291875 : Blo 191804 291875 := bstep (se 1 (by rfl) ⟨218906, by rfl⟩ : syracuseStep 291875 = 437813) B437813
theorem B193587 : Blo 191804 193587 := bstep (se 1 (by rfl) ⟨145190, by rfl⟩ : syracuseStep 193587 = 290381) B290381
theorem B291905 : Blo 191804 291905 := bstep (se 2 (by rfl) ⟨109464, by rfl⟩ : syracuseStep 291905 = 218929) B218929
theorem B193603 : Blo 191804 193603 := bstep (se 1 (by rfl) ⟨145202, by rfl⟩ : syracuseStep 193603 = 290405) B290405
theorem B193619 : Blo 191804 193619 := bstep (se 1 (by rfl) ⟨145214, by rfl⟩ : syracuseStep 193619 = 290429) B290429
theorem B291923 : Blo 191804 291923 := bstep (se 1 (by rfl) ⟨218942, by rfl⟩ : syracuseStep 291923 = 437885) B437885
theorem B193635 : Blo 191804 193635 := bstep (se 1 (by rfl) ⟨145226, by rfl⟩ : syracuseStep 193635 = 290453) B290453
theorem B291953 : Blo 191804 291953 := bstep (se 2 (by rfl) ⟨109482, by rfl⟩ : syracuseStep 291953 = 218965) B218965
theorem B193651 : Blo 191804 193651 := bstep (se 1 (by rfl) ⟨145238, by rfl⟩ : syracuseStep 193651 = 290477) B290477
theorem B193667 : Blo 191804 193667 := bstep (se 1 (by rfl) ⟨145250, by rfl⟩ : syracuseStep 193667 = 290501) B290501
theorem B291971 : Blo 191804 291971 := bstep (se 1 (by rfl) ⟨218978, by rfl⟩ : syracuseStep 291971 = 437957) B437957
theorem B193683 : Blo 191804 193683 := bstep (se 1 (by rfl) ⟨145262, by rfl⟩ : syracuseStep 193683 = 290525) B290525
theorem B324769 : Blo 191804 324769 := bstep (se 2 (by rfl) ⟨121788, by rfl⟩ : syracuseStep 324769 = 243577) B243577
theorem B292001 : Blo 191804 292001 := bstep (se 2 (by rfl) ⟨109500, by rfl⟩ : syracuseStep 292001 = 219001) B219001
theorem B193699 : Blo 191804 193699 := bstep (se 1 (by rfl) ⟨145274, by rfl⟩ : syracuseStep 193699 = 290549) B290549
theorem B193715 : Blo 191804 193715 := bstep (se 1 (by rfl) ⟨145286, by rfl⟩ : syracuseStep 193715 = 290573) B290573
theorem B292019 : Blo 191804 292019 := bstep (se 1 (by rfl) ⟨219014, by rfl⟩ : syracuseStep 292019 = 438029) B438029
theorem B324803 : Blo 191804 324803 := bstep (se 1 (by rfl) ⟨243602, by rfl⟩ : syracuseStep 324803 = 487205) B487205
theorem B193731 : Blo 191804 193731 := bstep (se 1 (by rfl) ⟨145298, by rfl⟩ : syracuseStep 193731 = 290597) B290597
theorem B292049 : Blo 191804 292049 := bstep (se 2 (by rfl) ⟨109518, by rfl⟩ : syracuseStep 292049 = 219037) B219037
theorem B193747 : Blo 191804 193747 := bstep (se 1 (by rfl) ⟨145310, by rfl⟩ : syracuseStep 193747 = 290621) B290621
theorem B193763 : Blo 191804 193763 := bstep (se 1 (by rfl) ⟨145322, by rfl⟩ : syracuseStep 193763 = 290645) B290645
theorem B292067 : Blo 191804 292067 := bstep (se 1 (by rfl) ⟨219050, by rfl⟩ : syracuseStep 292067 = 438101) B438101
theorem B193779 : Blo 191804 193779 := bstep (se 1 (by rfl) ⟨145334, by rfl⟩ : syracuseStep 193779 = 290669) B290669
theorem B292097 : Blo 191804 292097 := bstep (se 2 (by rfl) ⟨109536, by rfl⟩ : syracuseStep 292097 = 219073) B219073
theorem B193795 : Blo 191804 193795 := bstep (se 1 (by rfl) ⟨145346, by rfl⟩ : syracuseStep 193795 = 290693) B290693
theorem B193811 : Blo 191804 193811 := bstep (se 1 (by rfl) ⟨145358, by rfl⟩ : syracuseStep 193811 = 290717) B290717
theorem B292115 : Blo 191804 292115 := bstep (se 1 (by rfl) ⟨219086, by rfl⟩ : syracuseStep 292115 = 438173) B438173
theorem B193827 : Blo 191804 193827 := bstep (se 1 (by rfl) ⟨145370, by rfl⟩ : syracuseStep 193827 = 290741) B290741
theorem B652589 : Blo 191804 652589 := bstep (se 3 (by rfl) ⟨122360, by rfl⟩ : syracuseStep 652589 = 244721) B244721
theorem B292145 : Blo 191804 292145 := bstep (se 2 (by rfl) ⟨109554, by rfl⟩ : syracuseStep 292145 = 219109) B219109
theorem B193843 : Blo 191804 193843 := bstep (se 1 (by rfl) ⟨145382, by rfl⟩ : syracuseStep 193843 = 290765) B290765
theorem B324931 : Blo 191804 324931 := bstep (se 1 (by rfl) ⟨243698, by rfl⟩ : syracuseStep 324931 = 487397) B487397
theorem B193859 : Blo 191804 193859 := bstep (se 1 (by rfl) ⟨145394, by rfl⟩ : syracuseStep 193859 = 290789) B290789
theorem B292163 : Blo 191804 292163 := bstep (se 1 (by rfl) ⟨219122, by rfl⟩ : syracuseStep 292163 = 438245) B438245
theorem B193875 : Blo 191804 193875 := bstep (se 1 (by rfl) ⟨145406, by rfl⟩ : syracuseStep 193875 = 290813) B290813
theorem B292193 : Blo 191804 292193 := bstep (se 2 (by rfl) ⟨109572, by rfl⟩ : syracuseStep 292193 = 219145) B219145
theorem B652643 : Blo 191804 652643 := bstep (se 1 (by rfl) ⟨489482, by rfl⟩ : syracuseStep 652643 = 978965) B978965
theorem B193891 : Blo 191804 193891 := bstep (se 1 (by rfl) ⟨145418, by rfl⟩ : syracuseStep 193891 = 290837) B290837
theorem B521581 : Blo 191804 521581 := bstep (se 3 (by rfl) ⟨97796, by rfl⟩ : syracuseStep 521581 = 195593) B195593
theorem B193907 : Blo 191804 193907 := bstep (se 1 (by rfl) ⟨145430, by rfl⟩ : syracuseStep 193907 = 290861) B290861
theorem B292211 : Blo 191804 292211 := bstep (se 1 (by rfl) ⟨219158, by rfl⟩ : syracuseStep 292211 = 438317) B438317
theorem B193923 : Blo 191804 193923 := bstep (se 1 (by rfl) ⟨145442, by rfl⟩ : syracuseStep 193923 = 290885) B290885
theorem B292241 : Blo 191804 292241 := bstep (se 2 (by rfl) ⟨109590, by rfl⟩ : syracuseStep 292241 = 219181) B219181
theorem B193939 : Blo 191804 193939 := bstep (se 1 (by rfl) ⟨145454, by rfl⟩ : syracuseStep 193939 = 290909) B290909
theorem B193955 : Blo 191804 193955 := bstep (se 1 (by rfl) ⟨145466, by rfl⟩ : syracuseStep 193955 = 290933) B290933
theorem B292259 : Blo 191804 292259 := bstep (se 1 (by rfl) ⟨219194, by rfl⟩ : syracuseStep 292259 = 438389) B438389
theorem B193971 : Blo 191804 193971 := bstep (se 1 (by rfl) ⟨145478, by rfl⟩ : syracuseStep 193971 = 290957) B290957
theorem B292289 : Blo 191804 292289 := bstep (se 2 (by rfl) ⟨109608, by rfl⟩ : syracuseStep 292289 = 219217) B219217
theorem B193987 : Blo 191804 193987 := bstep (se 1 (by rfl) ⟨145490, by rfl⟩ : syracuseStep 193987 = 290981) B290981
theorem B259537 : Blo 191804 259537 := bstep (se 2 (by rfl) ⟨97326, by rfl⟩ : syracuseStep 259537 = 194653) B194653
theorem B325073 : Blo 191804 325073 := bstep (se 2 (by rfl) ⟨121902, by rfl⟩ : syracuseStep 325073 = 243805) B243805
theorem B292307 : Blo 191804 292307 := bstep (se 1 (by rfl) ⟨219230, by rfl⟩ : syracuseStep 292307 = 438461) B438461
theorem B194003 : Blo 191804 194003 := bstep (se 1 (by rfl) ⟨145502, by rfl⟩ : syracuseStep 194003 = 291005) B291005
theorem B194019 : Blo 191804 194019 := bstep (se 1 (by rfl) ⟨145514, by rfl⟩ : syracuseStep 194019 = 291029) B291029
theorem B292337 : Blo 191804 292337 := bstep (se 2 (by rfl) ⟨109626, by rfl⟩ : syracuseStep 292337 = 219253) B219253
theorem B194035 : Blo 191804 194035 := bstep (se 1 (by rfl) ⟨145526, by rfl⟩ : syracuseStep 194035 = 291053) B291053
theorem B194051 : Blo 191804 194051 := bstep (se 1 (by rfl) ⟨145538, by rfl⟩ : syracuseStep 194051 = 291077) B291077
theorem B292355 : Blo 191804 292355 := bstep (se 1 (by rfl) ⟨219266, by rfl⟩ : syracuseStep 292355 = 438533) B438533
theorem B194067 : Blo 191804 194067 := bstep (se 1 (by rfl) ⟨145550, by rfl⟩ : syracuseStep 194067 = 291101) B291101
theorem B292385 : Blo 191804 292385 := bstep (se 2 (by rfl) ⟨109644, by rfl⟩ : syracuseStep 292385 = 219289) B219289
theorem B194083 : Blo 191804 194083 := bstep (se 1 (by rfl) ⟨145562, by rfl⟩ : syracuseStep 194083 = 291125) B291125
theorem B292403 : Blo 191804 292403 := bstep (se 1 (by rfl) ⟨219302, by rfl⟩ : syracuseStep 292403 = 438605) B438605
theorem B194099 : Blo 191804 194099 := bstep (se 1 (by rfl) ⟨145574, by rfl⟩ : syracuseStep 194099 = 291149) B291149
theorem B194115 : Blo 191804 194115 := bstep (se 1 (by rfl) ⟨145586, by rfl⟩ : syracuseStep 194115 = 291173) B291173
theorem B325201 : Blo 191804 325201 := bstep (se 2 (by rfl) ⟨121950, by rfl⟩ : syracuseStep 325201 = 243901) B243901
theorem B292433 : Blo 191804 292433 := bstep (se 2 (by rfl) ⟨109662, by rfl⟩ : syracuseStep 292433 = 219325) B219325
theorem B194131 : Blo 191804 194131 := bstep (se 1 (by rfl) ⟨145598, by rfl⟩ : syracuseStep 194131 = 291197) B291197
theorem B194147 : Blo 191804 194147 := bstep (se 1 (by rfl) ⟨145610, by rfl⟩ : syracuseStep 194147 = 291221) B291221
theorem B292451 : Blo 191804 292451 := bstep (se 1 (by rfl) ⟨219338, by rfl⟩ : syracuseStep 292451 = 438677) B438677
theorem B652913 : Blo 191804 652913 := bstep (se 2 (by rfl) ⟨244842, by rfl⟩ : syracuseStep 652913 = 489685) B489685
theorem B325235 : Blo 191804 325235 := bstep (se 1 (by rfl) ⟨243926, by rfl⟩ : syracuseStep 325235 = 487853) B487853
theorem B194163 : Blo 191804 194163 := bstep (se 1 (by rfl) ⟨145622, by rfl⟩ : syracuseStep 194163 = 291245) B291245
theorem B292481 : Blo 191804 292481 := bstep (se 2 (by rfl) ⟨109680, by rfl⟩ : syracuseStep 292481 = 219361) B219361
theorem B194179 : Blo 191804 194179 := bstep (se 1 (by rfl) ⟨145634, by rfl⟩ : syracuseStep 194179 = 291269) B291269
theorem B194195 : Blo 191804 194195 := bstep (se 1 (by rfl) ⟨145646, by rfl⟩ : syracuseStep 194195 = 291293) B291293
theorem B292499 : Blo 191804 292499 := bstep (se 1 (by rfl) ⟨219374, by rfl⟩ : syracuseStep 292499 = 438749) B438749
theorem B194211 : Blo 191804 194211 := bstep (se 1 (by rfl) ⟨145658, by rfl⟩ : syracuseStep 194211 = 291317) B291317
theorem B292529 : Blo 191804 292529 := bstep (se 2 (by rfl) ⟨109698, by rfl⟩ : syracuseStep 292529 = 219397) B219397
theorem B194227 : Blo 191804 194227 := bstep (se 1 (by rfl) ⟨145670, by rfl⟩ : syracuseStep 194227 = 291341) B291341
theorem B194243 : Blo 191804 194243 := bstep (se 1 (by rfl) ⟨145682, by rfl⟩ : syracuseStep 194243 = 291365) B291365
theorem B292547 : Blo 191804 292547 := bstep (se 1 (by rfl) ⟨219410, by rfl⟩ : syracuseStep 292547 = 438821) B438821
theorem B554701 : Blo 191804 554701 := bstep (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) B208013
theorem B194259 : Blo 191804 194259 := bstep (se 1 (by rfl) ⟨145694, by rfl⟩ : syracuseStep 194259 = 291389) B291389
theorem B292577 : Blo 191804 292577 := bstep (se 2 (by rfl) ⟨109716, by rfl⟩ : syracuseStep 292577 = 219433) B219433
theorem B194275 : Blo 191804 194275 := bstep (se 1 (by rfl) ⟨145706, by rfl⟩ : syracuseStep 194275 = 291413) B291413
theorem B325363 : Blo 191804 325363 := bstep (se 1 (by rfl) ⟨244022, by rfl⟩ : syracuseStep 325363 = 488045) B488045
theorem B194291 : Blo 191804 194291 := bstep (se 1 (by rfl) ⟨145718, by rfl⟩ : syracuseStep 194291 = 291437) B291437
theorem B292595 : Blo 191804 292595 := bstep (se 1 (by rfl) ⟨219446, by rfl⟩ : syracuseStep 292595 = 438893) B438893
theorem B194307 : Blo 191804 194307 := bstep (se 1 (by rfl) ⟨145730, by rfl⟩ : syracuseStep 194307 = 291461) B291461
theorem B292625 : Blo 191804 292625 := bstep (se 2 (by rfl) ⟨109734, by rfl⟩ : syracuseStep 292625 = 219469) B219469
theorem B194323 : Blo 191804 194323 := bstep (se 1 (by rfl) ⟨145742, by rfl⟩ : syracuseStep 194323 = 291485) B291485
theorem B194339 : Blo 191804 194339 := bstep (se 1 (by rfl) ⟨145754, by rfl⟩ : syracuseStep 194339 = 291509) B291509
theorem B292643 : Blo 191804 292643 := bstep (se 1 (by rfl) ⟨219482, by rfl⟩ : syracuseStep 292643 = 438965) B438965
theorem B194355 : Blo 191804 194355 := bstep (se 1 (by rfl) ⟨145766, by rfl⟩ : syracuseStep 194355 = 291533) B291533
theorem B292673 : Blo 191804 292673 := bstep (se 2 (by rfl) ⟨109752, by rfl⟩ : syracuseStep 292673 = 219505) B219505
theorem B194371 : Blo 191804 194371 := bstep (se 1 (by rfl) ⟨145778, by rfl⟩ : syracuseStep 194371 = 291557) B291557
theorem B194387 : Blo 191804 194387 := bstep (se 1 (by rfl) ⟨145790, by rfl⟩ : syracuseStep 194387 = 291581) B291581
theorem B292691 : Blo 191804 292691 := bstep (se 1 (by rfl) ⟨219518, by rfl⟩ : syracuseStep 292691 = 439037) B439037
theorem B194403 : Blo 191804 194403 := bstep (se 1 (by rfl) ⟨145802, by rfl⟩ : syracuseStep 194403 = 291605) B291605
theorem B1111907 : Blo 191804 1111907 := bstep (se 1 (by rfl) ⟨833930, by rfl⟩ : syracuseStep 1111907 = 1667861) B1667861
theorem B292721 : Blo 191804 292721 := bstep (se 2 (by rfl) ⟨109770, by rfl⟩ : syracuseStep 292721 = 219541) B219541
theorem B194419 : Blo 191804 194419 := bstep (se 1 (by rfl) ⟨145814, by rfl⟩ : syracuseStep 194419 = 291629) B291629
theorem B325505 : Blo 191804 325505 := bstep (se 2 (by rfl) ⟨122064, by rfl⟩ : syracuseStep 325505 = 244129) B244129
theorem B194435 : Blo 191804 194435 := bstep (se 1 (by rfl) ⟨145826, by rfl⟩ : syracuseStep 194435 = 291653) B291653
theorem B292739 : Blo 191804 292739 := bstep (se 1 (by rfl) ⟨219554, by rfl⟩ : syracuseStep 292739 = 439109) B439109
theorem B489361 : Blo 191804 489361 := bstep (se 2 (by rfl) ⟨183510, by rfl⟩ : syracuseStep 489361 = 367021) B367021
theorem B194451 : Blo 191804 194451 := bstep (se 1 (by rfl) ⟨145838, by rfl⟩ : syracuseStep 194451 = 291677) B291677
theorem B292769 : Blo 191804 292769 := bstep (se 2 (by rfl) ⟨109788, by rfl⟩ : syracuseStep 292769 = 219577) B219577
theorem B194467 : Blo 191804 194467 := bstep (se 1 (by rfl) ⟨145850, by rfl⟩ : syracuseStep 194467 = 291701) B291701
theorem B1046449 : Blo 191804 1046449 := bstep (se 2 (by rfl) ⟨392418, by rfl⟩ : syracuseStep 1046449 = 784837) B784837
theorem B194483 : Blo 191804 194483 := bstep (se 1 (by rfl) ⟨145862, by rfl⟩ : syracuseStep 194483 = 291725) B291725
theorem B292787 : Blo 191804 292787 := bstep (se 1 (by rfl) ⟨219590, by rfl⟩ : syracuseStep 292787 = 439181) B439181
theorem B194499 : Blo 191804 194499 := bstep (se 1 (by rfl) ⟨145874, by rfl⟩ : syracuseStep 194499 = 291749) B291749
theorem B292817 : Blo 191804 292817 := bstep (se 2 (by rfl) ⟨109806, by rfl⟩ : syracuseStep 292817 = 219613) B219613
theorem B292819 : Blo 191804 292819 := bstep (se 1 (by rfl) ⟨219614, by rfl⟩ : syracuseStep 292819 = 439229) B439229
theorem B194515 : Blo 191804 194515 := bstep (se 1 (by rfl) ⟨145886, by rfl⟩ : syracuseStep 194515 = 291773) B291773
theorem B194531 : Blo 191804 194531 := bstep (se 1 (by rfl) ⟨145898, by rfl⟩ : syracuseStep 194531 = 291797) B291797
theorem B292835 : Blo 191804 292835 := bstep (se 1 (by rfl) ⟨219626, by rfl⟩ : syracuseStep 292835 = 439253) B439253
theorem B194547 : Blo 191804 194547 := bstep (se 1 (by rfl) ⟨145910, by rfl⟩ : syracuseStep 194547 = 291821) B291821
theorem B325633 : Blo 191804 325633 := bstep (se 2 (by rfl) ⟨122112, by rfl⟩ : syracuseStep 325633 = 244225) B244225
theorem B194563 : Blo 191804 194563 := bstep (se 1 (by rfl) ⟨145922, by rfl⟩ : syracuseStep 194563 = 291845) B291845
theorem B292865 : Blo 191804 292865 := bstep (se 2 (by rfl) ⟨109824, by rfl⟩ : syracuseStep 292865 = 219649) B219649
theorem B2488333 : Blo 191804 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B194579 : Blo 191804 194579 := bstep (se 1 (by rfl) ⟨145934, by rfl⟩ : syracuseStep 194579 = 291869) B291869
theorem B292883 : Blo 191804 292883 := bstep (se 1 (by rfl) ⟨219662, by rfl⟩ : syracuseStep 292883 = 439325) B439325
theorem B325667 : Blo 191804 325667 := bstep (se 1 (by rfl) ⟨244250, by rfl⟩ : syracuseStep 325667 = 488501) B488501
theorem B194595 : Blo 191804 194595 := bstep (se 1 (by rfl) ⟨145946, by rfl⟩ : syracuseStep 194595 = 291893) B291893
theorem B292913 : Blo 191804 292913 := bstep (se 2 (by rfl) ⟨109842, by rfl⟩ : syracuseStep 292913 = 219685) B219685
theorem B194611 : Blo 191804 194611 := bstep (se 1 (by rfl) ⟨145958, by rfl⟩ : syracuseStep 194611 = 291917) B291917
theorem B194627 : Blo 191804 194627 := bstep (se 1 (by rfl) ⟨145970, by rfl⟩ : syracuseStep 194627 = 291941) B291941
theorem B292931 : Blo 191804 292931 := bstep (se 1 (by rfl) ⟨219698, by rfl⟩ : syracuseStep 292931 = 439397) B439397
theorem B194643 : Blo 191804 194643 := bstep (se 1 (by rfl) ⟨145982, by rfl⟩ : syracuseStep 194643 = 291965) B291965
theorem B292961 : Blo 191804 292961 := bstep (se 2 (by rfl) ⟨109860, by rfl⟩ : syracuseStep 292961 = 219721) B219721
theorem B194659 : Blo 191804 194659 := bstep (se 1 (by rfl) ⟨145994, by rfl⟩ : syracuseStep 194659 = 291989) B291989
theorem B194675 : Blo 191804 194675 := bstep (se 1 (by rfl) ⟨146006, by rfl⟩ : syracuseStep 194675 = 292013) B292013
theorem B292979 : Blo 191804 292979 := bstep (se 1 (by rfl) ⟨219734, by rfl⟩ : syracuseStep 292979 = 439469) B439469
theorem B194691 : Blo 191804 194691 := bstep (se 1 (by rfl) ⟨146018, by rfl⟩ : syracuseStep 194691 = 292037) B292037
theorem B653453 : Blo 191804 653453 := bstep (se 3 (by rfl) ⟨122522, by rfl⟩ : syracuseStep 653453 = 245045) B245045
theorem B293009 : Blo 191804 293009 := bstep (se 2 (by rfl) ⟨109878, by rfl⟩ : syracuseStep 293009 = 219757) B219757
theorem B194707 : Blo 191804 194707 := bstep (se 1 (by rfl) ⟨146030, by rfl⟩ : syracuseStep 194707 = 292061) B292061
theorem B325795 : Blo 191804 325795 := bstep (se 1 (by rfl) ⟨244346, by rfl⟩ : syracuseStep 325795 = 488693) B488693
theorem B489635 : Blo 191804 489635 := bstep (se 1 (by rfl) ⟨367226, by rfl⟩ : syracuseStep 489635 = 734453) B734453
theorem B194723 : Blo 191804 194723 := bstep (se 1 (by rfl) ⟨146042, by rfl⟩ : syracuseStep 194723 = 292085) B292085
theorem B293027 : Blo 191804 293027 := bstep (se 1 (by rfl) ⟨219770, by rfl⟩ : syracuseStep 293027 = 439541) B439541
theorem B194739 : Blo 191804 194739 := bstep (se 1 (by rfl) ⟨146054, by rfl⟩ : syracuseStep 194739 = 292109) B292109
theorem B293057 : Blo 191804 293057 := bstep (se 2 (by rfl) ⟨109896, by rfl⟩ : syracuseStep 293057 = 219793) B219793
theorem B653507 : Blo 191804 653507 := bstep (se 1 (by rfl) ⟨490130, by rfl⟩ : syracuseStep 653507 = 980261) B980261
theorem B194755 : Blo 191804 194755 := bstep (se 1 (by rfl) ⟨146066, by rfl⟩ : syracuseStep 194755 = 292133) B292133
theorem B194771 : Blo 191804 194771 := bstep (se 1 (by rfl) ⟨146078, by rfl⟩ : syracuseStep 194771 = 292157) B292157
theorem B293075 : Blo 191804 293075 := bstep (se 1 (by rfl) ⟨219806, by rfl⟩ : syracuseStep 293075 = 439613) B439613
theorem B194787 : Blo 191804 194787 := bstep (se 1 (by rfl) ⟨146090, by rfl⟩ : syracuseStep 194787 = 292181) B292181
theorem B981233 : Blo 191804 981233 := bstep (se 2 (by rfl) ⟨367962, by rfl⟩ : syracuseStep 981233 = 735925) B735925
theorem B293105 : Blo 191804 293105 := bstep (se 2 (by rfl) ⟨109914, by rfl⟩ : syracuseStep 293105 = 219829) B219829
theorem B194803 : Blo 191804 194803 := bstep (se 1 (by rfl) ⟨146102, by rfl⟩ : syracuseStep 194803 = 292205) B292205
theorem B194819 : Blo 191804 194819 := bstep (se 1 (by rfl) ⟨146114, by rfl⟩ : syracuseStep 194819 = 292229) B292229
theorem B293123 : Blo 191804 293123 := bstep (se 1 (by rfl) ⟨219842, by rfl⟩ : syracuseStep 293123 = 439685) B439685
theorem B194835 : Blo 191804 194835 := bstep (se 1 (by rfl) ⟨146126, by rfl⟩ : syracuseStep 194835 = 292253) B292253
theorem B293153 : Blo 191804 293153 := bstep (se 2 (by rfl) ⟨109932, by rfl⟩ : syracuseStep 293153 = 219865) B219865
theorem B194851 : Blo 191804 194851 := bstep (se 1 (by rfl) ⟨146138, by rfl⟩ : syracuseStep 194851 = 292277) B292277
theorem B325937 : Blo 191804 325937 := bstep (se 2 (by rfl) ⟨122226, by rfl⟩ : syracuseStep 325937 = 244453) B244453
theorem B194867 : Blo 191804 194867 := bstep (se 1 (by rfl) ⟨146150, by rfl⟩ : syracuseStep 194867 = 292301) B292301
theorem B293171 : Blo 191804 293171 := bstep (se 1 (by rfl) ⟨219878, by rfl⟩ : syracuseStep 293171 = 439757) B439757
theorem B2816309 : Blo 191804 2816309 := bstep (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) B264029
theorem B194883 : Blo 191804 194883 := bstep (se 1 (by rfl) ⟨146162, by rfl⟩ : syracuseStep 194883 = 292325) B292325
theorem B293201 : Blo 191804 293201 := bstep (se 2 (by rfl) ⟨109950, by rfl⟩ : syracuseStep 293201 = 219901) B219901
theorem B194899 : Blo 191804 194899 := bstep (se 1 (by rfl) ⟨146174, by rfl⟩ : syracuseStep 194899 = 292349) B292349
theorem B489827 : Blo 191804 489827 := bstep (se 1 (by rfl) ⟨367370, by rfl⟩ : syracuseStep 489827 = 734741) B734741
theorem B194915 : Blo 191804 194915 := bstep (se 1 (by rfl) ⟨146186, by rfl⟩ : syracuseStep 194915 = 292373) B292373
theorem B293219 : Blo 191804 293219 := bstep (se 1 (by rfl) ⟨219914, by rfl⟩ : syracuseStep 293219 = 439829) B439829
theorem B194931 : Blo 191804 194931 := bstep (se 1 (by rfl) ⟨146198, by rfl⟩ : syracuseStep 194931 = 292397) B292397
theorem B293249 : Blo 191804 293249 := bstep (se 2 (by rfl) ⟨109968, by rfl⟩ : syracuseStep 293249 = 219937) B219937
theorem B194947 : Blo 191804 194947 := bstep (se 1 (by rfl) ⟨146210, by rfl⟩ : syracuseStep 194947 = 292421) B292421
theorem B194963 : Blo 191804 194963 := bstep (se 1 (by rfl) ⟨146222, by rfl⟩ : syracuseStep 194963 = 292445) B292445
theorem B293267 : Blo 191804 293267 := bstep (se 1 (by rfl) ⟨219950, by rfl⟩ : syracuseStep 293267 = 439901) B439901
theorem B194979 : Blo 191804 194979 := bstep (se 1 (by rfl) ⟨146234, by rfl⟩ : syracuseStep 194979 = 292469) B292469
theorem B326065 : Blo 191804 326065 := bstep (se 2 (by rfl) ⟨122274, by rfl⟩ : syracuseStep 326065 = 244549) B244549
theorem B293297 : Blo 191804 293297 := bstep (se 2 (by rfl) ⟨109986, by rfl⟩ : syracuseStep 293297 = 219973) B219973
theorem B194995 : Blo 191804 194995 := bstep (se 1 (by rfl) ⟨146246, by rfl⟩ : syracuseStep 194995 = 292493) B292493
theorem B195011 : Blo 191804 195011 := bstep (se 1 (by rfl) ⟨146258, by rfl⟩ : syracuseStep 195011 = 292517) B292517
theorem B293315 : Blo 191804 293315 := bstep (se 1 (by rfl) ⟨219986, by rfl⟩ : syracuseStep 293315 = 439973) B439973
theorem B653777 : Blo 191804 653777 := bstep (se 2 (by rfl) ⟨245166, by rfl⟩ : syracuseStep 653777 = 490333) B490333
theorem B326099 : Blo 191804 326099 := bstep (se 1 (by rfl) ⟨244574, by rfl⟩ : syracuseStep 326099 = 489149) B489149
theorem B195027 : Blo 191804 195027 := bstep (se 1 (by rfl) ⟨146270, by rfl⟩ : syracuseStep 195027 = 292541) B292541
theorem B293345 : Blo 191804 293345 := bstep (se 2 (by rfl) ⟨110004, by rfl⟩ : syracuseStep 293345 = 220009) B220009
theorem B1243619 : Blo 191804 1243619 := bstep (se 1 (by rfl) ⟨932714, by rfl⟩ : syracuseStep 1243619 = 1865429) B1865429
theorem B195043 : Blo 191804 195043 := bstep (se 1 (by rfl) ⟨146282, by rfl⟩ : syracuseStep 195043 = 292565) B292565
theorem B195059 : Blo 191804 195059 := bstep (se 1 (by rfl) ⟨146294, by rfl⟩ : syracuseStep 195059 = 292589) B292589
theorem B293363 : Blo 191804 293363 := bstep (se 1 (by rfl) ⟨220022, by rfl⟩ : syracuseStep 293363 = 440045) B440045
theorem B195075 : Blo 191804 195075 := bstep (se 1 (by rfl) ⟨146306, by rfl⟩ : syracuseStep 195075 = 292613) B292613
theorem B293393 : Blo 191804 293393 := bstep (se 2 (by rfl) ⟨110022, by rfl⟩ : syracuseStep 293393 = 220045) B220045
theorem B195091 : Blo 191804 195091 := bstep (se 1 (by rfl) ⟨146318, by rfl⟩ : syracuseStep 195091 = 292637) B292637
theorem B195107 : Blo 191804 195107 := bstep (se 1 (by rfl) ⟨146330, by rfl⟩ : syracuseStep 195107 = 292661) B292661
theorem B293411 : Blo 191804 293411 := bstep (se 1 (by rfl) ⟨220058, by rfl⟩ : syracuseStep 293411 = 440117) B440117
theorem B195123 : Blo 191804 195123 := bstep (se 1 (by rfl) ⟨146342, by rfl⟩ : syracuseStep 195123 = 292685) B292685
theorem B293441 : Blo 191804 293441 := bstep (se 2 (by rfl) ⟨110040, by rfl⟩ : syracuseStep 293441 = 220081) B220081
theorem B195139 : Blo 191804 195139 := bstep (se 1 (by rfl) ⟨146354, by rfl⟩ : syracuseStep 195139 = 292709) B292709
theorem B326227 : Blo 191804 326227 := bstep (se 1 (by rfl) ⟨244670, by rfl⟩ : syracuseStep 326227 = 489341) B489341
theorem B195155 : Blo 191804 195155 := bstep (se 1 (by rfl) ⟨146366, by rfl⟩ : syracuseStep 195155 = 292733) B292733
theorem B293459 : Blo 191804 293459 := bstep (se 1 (by rfl) ⟨220094, by rfl⟩ : syracuseStep 293459 = 440189) B440189
theorem B195171 : Blo 191804 195171 := bstep (se 1 (by rfl) ⟨146378, by rfl⟩ : syracuseStep 195171 = 292757) B292757
theorem B293489 : Blo 191804 293489 := bstep (se 2 (by rfl) ⟨110058, by rfl⟩ : syracuseStep 293489 = 220117) B220117
theorem B195187 : Blo 191804 195187 := bstep (se 1 (by rfl) ⟨146390, by rfl⟩ : syracuseStep 195187 = 292781) B292781
theorem B195203 : Blo 191804 195203 := bstep (se 1 (by rfl) ⟨146402, by rfl⟩ : syracuseStep 195203 = 292805) B292805
theorem B293507 : Blo 191804 293507 := bstep (se 1 (by rfl) ⟨220130, by rfl⟩ : syracuseStep 293507 = 440261) B440261
theorem B195219 : Blo 191804 195219 := bstep (se 1 (by rfl) ⟨146414, by rfl⟩ : syracuseStep 195219 = 292829) B292829
theorem B293537 : Blo 191804 293537 := bstep (se 2 (by rfl) ⟨110076, by rfl⟩ : syracuseStep 293537 = 220153) B220153
theorem B1145507 : Blo 191804 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B195235 : Blo 191804 195235 := bstep (se 1 (by rfl) ⟨146426, by rfl⟩ : syracuseStep 195235 = 292853) B292853
theorem B195251 : Blo 191804 195251 := bstep (se 1 (by rfl) ⟨146438, by rfl⟩ : syracuseStep 195251 = 292877) B292877
theorem B293555 : Blo 191804 293555 := bstep (se 1 (by rfl) ⟨220166, by rfl⟩ : syracuseStep 293555 = 440333) B440333
theorem B195267 : Blo 191804 195267 := bstep (se 1 (by rfl) ⟨146450, by rfl⟩ : syracuseStep 195267 = 292901) B292901
theorem B293585 : Blo 191804 293585 := bstep (se 2 (by rfl) ⟨110094, by rfl⟩ : syracuseStep 293585 = 220189) B220189
theorem B195283 : Blo 191804 195283 := bstep (se 1 (by rfl) ⟨146462, by rfl⟩ : syracuseStep 195283 = 292925) B292925
theorem B326369 : Blo 191804 326369 := bstep (se 2 (by rfl) ⟨122388, by rfl⟩ : syracuseStep 326369 = 244777) B244777
theorem B195299 : Blo 191804 195299 := bstep (se 1 (by rfl) ⟨146474, by rfl⟩ : syracuseStep 195299 = 292949) B292949
theorem B293603 : Blo 191804 293603 := bstep (se 1 (by rfl) ⟨220202, by rfl⟩ : syracuseStep 293603 = 440405) B440405
theorem B555761 : Blo 191804 555761 := bstep (se 2 (by rfl) ⟨208410, by rfl⟩ : syracuseStep 555761 = 416821) B416821
theorem B195315 : Blo 191804 195315 := bstep (se 1 (by rfl) ⟨146486, by rfl⟩ : syracuseStep 195315 = 292973) B292973
theorem B293633 : Blo 191804 293633 := bstep (se 2 (by rfl) ⟨110112, by rfl⟩ : syracuseStep 293633 = 220225) B220225
theorem B195331 : Blo 191804 195331 := bstep (se 1 (by rfl) ⟨146498, by rfl⟩ : syracuseStep 195331 = 292997) B292997
theorem B195347 : Blo 191804 195347 := bstep (se 1 (by rfl) ⟨146510, by rfl⟩ : syracuseStep 195347 = 293021) B293021
theorem B293651 : Blo 191804 293651 := bstep (se 1 (by rfl) ⟨220238, by rfl⟩ : syracuseStep 293651 = 440477) B440477
theorem B195363 : Blo 191804 195363 := bstep (se 1 (by rfl) ⟨146522, by rfl⟩ : syracuseStep 195363 = 293045) B293045
theorem B293681 : Blo 191804 293681 := bstep (se 2 (by rfl) ⟨110130, by rfl⟩ : syracuseStep 293681 = 220261) B220261
theorem B195379 : Blo 191804 195379 := bstep (se 1 (by rfl) ⟨146534, by rfl⟩ : syracuseStep 195379 = 293069) B293069
theorem B195395 : Blo 191804 195395 := bstep (se 1 (by rfl) ⟨146546, by rfl⟩ : syracuseStep 195395 = 293093) B293093
theorem B293699 : Blo 191804 293699 := bstep (se 1 (by rfl) ⟨220274, by rfl⟩ : syracuseStep 293699 = 440549) B440549
theorem B195411 : Blo 191804 195411 := bstep (se 1 (by rfl) ⟨146558, by rfl⟩ : syracuseStep 195411 = 293117) B293117
theorem B326497 : Blo 191804 326497 := bstep (se 2 (by rfl) ⟨122436, by rfl⟩ : syracuseStep 326497 = 244873) B244873
theorem B195427 : Blo 191804 195427 := bstep (se 1 (by rfl) ⟨146570, by rfl⟩ : syracuseStep 195427 = 293141) B293141
theorem B2194289 : Blo 191804 2194289 := bstep (se 2 (by rfl) ⟨822858, by rfl⟩ : syracuseStep 2194289 = 1645717) B1645717
theorem B195443 : Blo 191804 195443 := bstep (se 1 (by rfl) ⟨146582, by rfl⟩ : syracuseStep 195443 = 293165) B293165
theorem B326531 : Blo 191804 326531 := bstep (se 1 (by rfl) ⟨244898, by rfl⟩ : syracuseStep 326531 = 489797) B489797
theorem B195459 : Blo 191804 195459 := bstep (se 1 (by rfl) ⟨146594, by rfl⟩ : syracuseStep 195459 = 293189) B293189
theorem B195475 : Blo 191804 195475 := bstep (se 1 (by rfl) ⟨146606, by rfl⟩ : syracuseStep 195475 = 293213) B293213
theorem B195491 : Blo 191804 195491 := bstep (se 1 (by rfl) ⟨146618, by rfl⟩ : syracuseStep 195491 = 293237) B293237
theorem B195507 : Blo 191804 195507 := bstep (se 1 (by rfl) ⟨146630, by rfl⟩ : syracuseStep 195507 = 293261) B293261
theorem B195523 : Blo 191804 195523 := bstep (se 1 (by rfl) ⟨146642, by rfl⟩ : syracuseStep 195523 = 293285) B293285
theorem B195539 : Blo 191804 195539 := bstep (se 1 (by rfl) ⟨146654, by rfl⟩ : syracuseStep 195539 = 293309) B293309
theorem B195555 : Blo 191804 195555 := bstep (se 1 (by rfl) ⟨146666, by rfl⟩ : syracuseStep 195555 = 293333) B293333
theorem B654317 : Blo 191804 654317 := bstep (se 3 (by rfl) ⟨122684, by rfl⟩ : syracuseStep 654317 = 245369) B245369
theorem B621553 : Blo 191804 621553 := bstep (se 2 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 621553 = 466165) B466165
theorem B195571 : Blo 191804 195571 := bstep (se 1 (by rfl) ⟨146678, by rfl⟩ : syracuseStep 195571 = 293357) B293357
theorem B326659 : Blo 191804 326659 := bstep (se 1 (by rfl) ⟨244994, by rfl⟩ : syracuseStep 326659 = 489989) B489989
theorem B195587 : Blo 191804 195587 := bstep (se 1 (by rfl) ⟨146690, by rfl⟩ : syracuseStep 195587 = 293381) B293381
theorem B195603 : Blo 191804 195603 := bstep (se 1 (by rfl) ⟨146702, by rfl⟩ : syracuseStep 195603 = 293405) B293405
theorem B654371 : Blo 191804 654371 := bstep (se 1 (by rfl) ⟨490778, by rfl⟩ : syracuseStep 654371 = 981557) B981557
theorem B195619 : Blo 191804 195619 := bstep (se 1 (by rfl) ⟨146714, by rfl⟩ : syracuseStep 195619 = 293429) B293429
theorem B195635 : Blo 191804 195635 := bstep (se 1 (by rfl) ⟨146726, by rfl⟩ : syracuseStep 195635 = 293453) B293453
theorem B195651 : Blo 191804 195651 := bstep (se 1 (by rfl) ⟨146738, by rfl⟩ : syracuseStep 195651 = 293477) B293477
theorem B195667 : Blo 191804 195667 := bstep (se 1 (by rfl) ⟨146750, by rfl⟩ : syracuseStep 195667 = 293501) B293501
theorem B195683 : Blo 191804 195683 := bstep (se 1 (by rfl) ⟨146762, by rfl⟩ : syracuseStep 195683 = 293525) B293525
theorem B195699 : Blo 191804 195699 := bstep (se 1 (by rfl) ⟨146774, by rfl⟩ : syracuseStep 195699 = 293549) B293549
theorem B195715 : Blo 191804 195715 := bstep (se 1 (by rfl) ⟨146786, by rfl⟩ : syracuseStep 195715 = 293573) B293573
theorem B326801 : Blo 191804 326801 := bstep (se 2 (by rfl) ⟨122550, by rfl⟩ : syracuseStep 326801 = 245101) B245101
theorem B195731 : Blo 191804 195731 := bstep (se 1 (by rfl) ⟨146798, by rfl⟩ : syracuseStep 195731 = 293597) B293597
theorem B195747 : Blo 191804 195747 := bstep (se 1 (by rfl) ⟨146810, by rfl⟩ : syracuseStep 195747 = 293621) B293621
theorem B195763 : Blo 191804 195763 := bstep (se 1 (by rfl) ⟨146822, by rfl⟩ : syracuseStep 195763 = 293645) B293645
theorem B195779 : Blo 191804 195779 := bstep (se 1 (by rfl) ⟨146834, by rfl⟩ : syracuseStep 195779 = 293669) B293669
theorem B195795 : Blo 191804 195795 := bstep (se 1 (by rfl) ⟨146846, by rfl⟩ : syracuseStep 195795 = 293693) B293693
theorem B326929 : Blo 191804 326929 := bstep (se 2 (by rfl) ⟨122598, by rfl⟩ : syracuseStep 326929 = 245197) B245197
theorem B490769 : Blo 191804 490769 := bstep (se 2 (by rfl) ⟨184038, by rfl⟩ : syracuseStep 490769 = 368077) B368077
theorem B654641 : Blo 191804 654641 := bstep (se 2 (by rfl) ⟨245490, by rfl⟩ : syracuseStep 654641 = 490981) B490981
theorem B326963 : Blo 191804 326963 := bstep (se 1 (by rfl) ⟨245222, by rfl⟩ : syracuseStep 326963 = 490445) B490445
theorem B490819 : Blo 191804 490819 := bstep (se 1 (by rfl) ⟨368114, by rfl⟩ : syracuseStep 490819 = 736229) B736229
theorem B556433 : Blo 191804 556433 := bstep (se 2 (by rfl) ⟨208662, by rfl⟩ : syracuseStep 556433 = 417325) B417325
theorem B327091 : Blo 191804 327091 := bstep (se 1 (by rfl) ⟨245318, by rfl⟩ : syracuseStep 327091 = 490637) B490637
theorem B490961 : Blo 191804 490961 := bstep (se 2 (by rfl) ⟨184110, by rfl⟩ : syracuseStep 490961 = 368221) B368221
theorem B327233 : Blo 191804 327233 := bstep (se 2 (by rfl) ⟨122712, by rfl⟩ : syracuseStep 327233 = 245425) B245425
theorem B589457 : Blo 191804 589457 := bstep (se 2 (by rfl) ⟨221046, by rfl⟩ : syracuseStep 589457 = 442093) B442093
theorem B982691 : Blo 191804 982691 := bstep (se 1 (by rfl) ⟨737018, by rfl⟩ : syracuseStep 982691 = 1474037) B1474037
theorem B327361 : Blo 191804 327361 := bstep (se 2 (by rfl) ⟨122760, by rfl⟩ : syracuseStep 327361 = 245521) B245521
theorem B196291 : Blo 191804 196291 := bstep (se 1 (by rfl) ⟨147218, by rfl⟩ : syracuseStep 196291 = 294437) B294437
theorem B327395 : Blo 191804 327395 := bstep (se 1 (by rfl) ⟨245546, by rfl⟩ : syracuseStep 327395 = 491093) B491093
theorem B5603093 : Blo 191804 5603093 := bstep (se 6 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 5603093 = 262645) B262645
theorem B655181 : Blo 191804 655181 := bstep (se 3 (by rfl) ⟨122846, by rfl⟩ : syracuseStep 655181 = 245693) B245693
theorem B327523 : Blo 191804 327523 := bstep (se 1 (by rfl) ⟨245642, by rfl⟩ : syracuseStep 327523 = 491285) B491285
theorem B655235 : Blo 191804 655235 := bstep (se 1 (by rfl) ⟨491426, by rfl⟩ : syracuseStep 655235 = 982853) B982853
theorem B2359181 : Blo 191804 2359181 := bstep (se 3 (by rfl) ⟨442346, by rfl⟩ : syracuseStep 2359181 = 884693) B884693
theorem B524177 : Blo 191804 524177 := bstep (se 2 (by rfl) ⟨196566, by rfl⟩ : syracuseStep 524177 = 393133) B393133
theorem B327665 : Blo 191804 327665 := bstep (se 2 (by rfl) ⟨122874, by rfl⟩ : syracuseStep 327665 = 245749) B245749
theorem B491609 : Blo 191804 491609 := bstep (se 2 (by rfl) ⟨184353, by rfl⟩ : syracuseStep 491609 = 368707) B368707
theorem B655667 : Blo 191804 655667 := bstep (se 1 (by rfl) ⟨491750, by rfl⟩ : syracuseStep 655667 = 983501) B983501
theorem B557401 : Blo 191804 557401 := bstep (se 2 (by rfl) ⟨209025, by rfl⟩ : syracuseStep 557401 = 418051) B418051
theorem B328151 : Blo 191804 328151 := bstep (se 1 (by rfl) ⟨246113, by rfl⟩ : syracuseStep 328151 = 492227) B492227
theorem B819715 : Blo 191804 819715 := bstep (se 1 (by rfl) ⟨614786, by rfl⟩ : syracuseStep 819715 = 1229573) B1229573
theorem B655937 : Blo 191804 655937 := bstep (se 2 (by rfl) ⟨245976, by rfl⟩ : syracuseStep 655937 = 491953) B491953
theorem B393815 : Blo 191804 393815 := bstep (se 1 (by rfl) ⟨295361, by rfl⟩ : syracuseStep 393815 = 590723) B590723
theorem B328279 : Blo 191804 328279 := bstep (se 1 (by rfl) ⟨246209, by rfl⟩ : syracuseStep 328279 = 492419) B492419
theorem B1049219 : Blo 191804 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B983825 : Blo 191804 983825 := bstep (se 2 (by rfl) ⟨368934, by rfl⟩ : syracuseStep 983825 = 737869) B737869
theorem B820057 : Blo 191804 820057 := bstep (se 2 (by rfl) ⟨307521, by rfl⟩ : syracuseStep 820057 = 615043) B615043
theorem B2786147 : Blo 191804 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B492439 : Blo 191804 492439 := bstep (se 1 (by rfl) ⟨369329, by rfl⟩ : syracuseStep 492439 = 738659) B738659
theorem B983987 : Blo 191804 983987 := bstep (se 1 (by rfl) ⟨737990, by rfl⟩ : syracuseStep 983987 = 1475981) B1475981
theorem B623705 : Blo 191804 623705 := bstep (se 2 (by rfl) ⟨233889, by rfl⟩ : syracuseStep 623705 = 467779) B467779
theorem B656477 : Blo 191804 656477 := bstep (se 3 (by rfl) ⟨123089, by rfl⟩ : syracuseStep 656477 = 246179) B246179
theorem B328907 : Blo 191804 328907 := bstep (se 1 (by rfl) ⟨246680, by rfl⟩ : syracuseStep 328907 = 493361) B493361
theorem B492875 : Blo 191804 492875 := bstep (se 1 (by rfl) ⟨369656, by rfl⟩ : syracuseStep 492875 = 739313) B739313
theorem B329035 : Blo 191804 329035 := bstep (se 1 (by rfl) ⟨246776, by rfl⟩ : syracuseStep 329035 = 493553) B493553
theorem B296407 : Blo 191804 296407 := bstep (se 1 (by rfl) ⟨222305, by rfl⟩ : syracuseStep 296407 = 444611) B444611
theorem B329177 : Blo 191804 329177 := bstep (se 2 (by rfl) ⟨123441, by rfl⟩ : syracuseStep 329177 = 246883) B246883
theorem B3311117 : Blo 191804 3311117 := bstep (se 3 (by rfl) ⟨620834, by rfl⟩ : syracuseStep 3311117 = 1241669) B1241669
theorem B1410605 : Blo 191804 1410605 := bstep (se 3 (by rfl) ⟨264488, by rfl⟩ : syracuseStep 1410605 = 528977) B528977
theorem B329305 : Blo 191804 329305 := bstep (se 2 (by rfl) ⟨123489, by rfl⟩ : syracuseStep 329305 = 246979) B246979
theorem B493249 : Blo 191804 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B821015 : Blo 191804 821015 := bstep (se 1 (by rfl) ⟨615761, by rfl⟩ : syracuseStep 821015 = 1231523) B1231523
theorem B624449 : Blo 191804 624449 := bstep (se 2 (by rfl) ⟨234168, by rfl⟩ : syracuseStep 624449 = 468337) B468337
theorem B329879 : Blo 191804 329879 := bstep (se 1 (by rfl) ⟨247409, by rfl⟩ : syracuseStep 329879 = 494819) B494819
theorem B657611 : Blo 191804 657611 := bstep (se 1 (by rfl) ⟨493208, by rfl⟩ : syracuseStep 657611 = 986417) B986417
theorem B493847 : Blo 191804 493847 := bstep (se 1 (by rfl) ⟨370385, by rfl⟩ : syracuseStep 493847 = 740771) B740771
theorem B330007 : Blo 191804 330007 := bstep (se 1 (by rfl) ⟨247505, by rfl⟩ : syracuseStep 330007 = 495011) B495011
theorem B461207 : Blo 191804 461207 := bstep (se 1 (by rfl) ⟨345905, by rfl⟩ : syracuseStep 461207 = 691811) B691811
theorem B526771 : Blo 191804 526771 := bstep (se 1 (by rfl) ⟨395078, by rfl⟩ : syracuseStep 526771 = 790157) B790157
theorem B657881 : Blo 191804 657881 := bstep (se 2 (by rfl) ⟨246705, by rfl⟩ : syracuseStep 657881 = 493411) B493411
theorem B297623 : Blo 191804 297623 := bstep (se 1 (by rfl) ⟨223217, by rfl⟩ : syracuseStep 297623 = 446435) B446435
theorem B461591 : Blo 191804 461591 := bstep (se 1 (by rfl) ⟨346193, by rfl⟩ : syracuseStep 461591 = 692387) B692387
theorem B330571 : Blo 191804 330571 := bstep (se 1 (by rfl) ⟨247928, by rfl⟩ : syracuseStep 330571 = 495857) B495857
theorem B985931 : Blo 191804 985931 := bstep (se 1 (by rfl) ⟨739448, by rfl⟩ : syracuseStep 985931 = 1478897) B1478897
theorem B1772381 : Blo 191804 1772381 := bstep (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) B664643
theorem B494657 : Blo 191804 494657 := bstep (se 2 (by rfl) ⟨185496, by rfl⟩ : syracuseStep 494657 = 370993) B370993
theorem B658583 : Blo 191804 658583 := bstep (se 1 (by rfl) ⟨493937, by rfl⟩ : syracuseStep 658583 = 987875) B987875
theorem B822707 : Blo 191804 822707 := bstep (se 1 (by rfl) ⟨617030, by rfl⟩ : syracuseStep 822707 = 1234061) B1234061
theorem B527809 : Blo 191804 527809 := bstep (se 2 (by rfl) ⟨197928, by rfl⟩ : syracuseStep 527809 = 395857) B395857
theorem B495193 : Blo 191804 495193 := bstep (se 2 (by rfl) ⟨185697, by rfl⟩ : syracuseStep 495193 = 371395) B371395
theorem B659123 : Blo 191804 659123 := bstep (se 1 (by rfl) ⟨494342, by rfl⟩ : syracuseStep 659123 = 988685) B988685
theorem B462667 : Blo 191804 462667 := bstep (se 1 (by rfl) ⟨347000, by rfl⟩ : syracuseStep 462667 = 694001) B694001
theorem B626525 : Blo 191804 626525 := bstep (se 3 (by rfl) ⟨117473, by rfl⟩ : syracuseStep 626525 = 234947) B234947
theorem B364439 : Blo 191804 364439 := bstep (se 1 (by rfl) ⟨273329, by rfl⟩ : syracuseStep 364439 = 546659) B546659
theorem B659393 : Blo 191804 659393 := bstep (se 2 (by rfl) ⟨247272, by rfl⟩ : syracuseStep 659393 = 494545) B494545
theorem B692545 : Blo 191804 692545 := bstep (se 2 (by rfl) ⟨259704, by rfl⟩ : syracuseStep 692545 = 519409) B519409
theorem B1872193 : Blo 191804 1872193 := bstep (se 2 (by rfl) ⟨702072, by rfl⟩ : syracuseStep 1872193 = 1404145) B1404145
theorem B1249667 : Blo 191804 1249667 := bstep (se 1 (by rfl) ⟨937250, by rfl⟩ : syracuseStep 1249667 = 1874501) B1874501
theorem B364979 : Blo 191804 364979 := bstep (se 1 (by rfl) ⟨273734, by rfl⟩ : syracuseStep 364979 = 547469) B547469
theorem B463283 : Blo 191804 463283 := bstep (se 1 (by rfl) ⟨347462, by rfl⟩ : syracuseStep 463283 = 694925) B694925
theorem B659933 : Blo 191804 659933 := bstep (se 3 (by rfl) ⟨123737, by rfl⟩ : syracuseStep 659933 = 247475) B247475
theorem B8458769 : Blo 191804 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B987713 : Blo 191804 987713 := bstep (se 2 (by rfl) ⟨370392, by rfl⟩ : syracuseStep 987713 = 740785) B740785
theorem B332363 : Blo 191804 332363 := bstep (se 1 (by rfl) ⟨249272, by rfl⟩ : syracuseStep 332363 = 498545) B498545
theorem B1184557 : Blo 191804 1184557 := bstep (se 3 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 1184557 = 444209) B444209
theorem B365465 : Blo 191804 365465 := bstep (se 2 (by rfl) ⟨137049, by rfl⟩ : syracuseStep 365465 = 274099) B274099
theorem B791569 : Blo 191804 791569 := bstep (se 2 (by rfl) ⟨296838, by rfl⟩ : syracuseStep 791569 = 593677) B593677
theorem B464051 : Blo 191804 464051 := bstep (se 1 (by rfl) ⟨348038, by rfl⟩ : syracuseStep 464051 = 696077) B696077
theorem B201943 : Blo 191804 201943 := bstep (se 1 (by rfl) ⟨151457, by rfl⟩ : syracuseStep 201943 = 302915) B302915
theorem B890315 : Blo 191804 890315 := bstep (se 1 (by rfl) ⟨667736, by rfl⟩ : syracuseStep 890315 = 1335473) B1335473
theorem B431603 : Blo 191804 431603 := bstep (se 1 (by rfl) ⟨323702, by rfl⟩ : syracuseStep 431603 = 647405) B647405
theorem B431639 : Blo 191804 431639 := bstep (se 1 (by rfl) ⟨323729, by rfl⟩ : syracuseStep 431639 = 647459) B647459
theorem B2496035 : Blo 191804 2496035 := bstep (se 1 (by rfl) ⟨1872026, by rfl⟩ : syracuseStep 2496035 = 3744053) B3744053
theorem B1644077 : Blo 191804 1644077 := bstep (se 3 (by rfl) ⟨308264, by rfl⟩ : syracuseStep 1644077 = 616529) B616529
theorem B431819 : Blo 191804 431819 := bstep (se 1 (by rfl) ⟨323864, by rfl⟩ : syracuseStep 431819 = 647729) B647729
theorem B431873 : Blo 191804 431873 := bstep (se 2 (by rfl) ⟨161952, by rfl⟩ : syracuseStep 431873 = 323905) B323905
theorem B563033 : Blo 191804 563033 := bstep (se 2 (by rfl) ⟨211137, by rfl⟩ : syracuseStep 563033 = 422275) B422275
theorem B432089 : Blo 191804 432089 := bstep (se 2 (by rfl) ⟨162033, by rfl⟩ : syracuseStep 432089 = 324067) B324067
theorem B825389 : Blo 191804 825389 := bstep (se 3 (by rfl) ⟨154760, by rfl⟩ : syracuseStep 825389 = 309521) B309521
theorem B432179 : Blo 191804 432179 := bstep (se 1 (by rfl) ⟨324134, by rfl⟩ : syracuseStep 432179 = 648269) B648269
theorem B432215 : Blo 191804 432215 := bstep (se 1 (by rfl) ⟨324161, by rfl⟩ : syracuseStep 432215 = 648323) B648323
theorem B1382579 : Blo 191804 1382579 := bstep (se 1 (by rfl) ⟨1036934, by rfl⟩ : syracuseStep 1382579 = 2073869) B2073869
theorem B432395 : Blo 191804 432395 := bstep (se 1 (by rfl) ⟨324296, by rfl⟩ : syracuseStep 432395 = 648593) B648593
theorem B432449 : Blo 191804 432449 := bstep (se 2 (by rfl) ⟨162168, by rfl⟩ : syracuseStep 432449 = 324337) B324337
theorem B366923 : Blo 191804 366923 := bstep (se 1 (by rfl) ⟨275192, by rfl⟩ : syracuseStep 366923 = 550385) B550385
theorem B989657 : Blo 191804 989657 := bstep (se 2 (by rfl) ⟨371121, by rfl⟩ : syracuseStep 989657 = 742243) B742243
theorem B367105 : Blo 191804 367105 := bstep (se 2 (by rfl) ⟨137664, by rfl⟩ : syracuseStep 367105 = 275329) B275329
theorem B432665 : Blo 191804 432665 := bstep (se 2 (by rfl) ⟨162249, by rfl⟩ : syracuseStep 432665 = 324499) B324499
theorem B465473 : Blo 191804 465473 := bstep (se 2 (by rfl) ⟨174552, by rfl⟩ : syracuseStep 465473 = 349105) B349105
theorem B432755 : Blo 191804 432755 := bstep (se 1 (by rfl) ⟨324566, by rfl⟩ : syracuseStep 432755 = 649133) B649133
theorem B432791 : Blo 191804 432791 := bstep (se 1 (by rfl) ⟨324593, by rfl⟩ : syracuseStep 432791 = 649187) B649187
theorem B662195 : Blo 191804 662195 := bstep (se 1 (by rfl) ⟨496646, by rfl⟩ : syracuseStep 662195 = 993293) B993293
theorem B1120985 : Blo 191804 1120985 := bstep (se 2 (by rfl) ⟨420369, by rfl⟩ : syracuseStep 1120985 = 840739) B840739
theorem B432971 : Blo 191804 432971 := bstep (se 1 (by rfl) ⟨324728, by rfl⟩ : syracuseStep 432971 = 649457) B649457
theorem B793433 : Blo 191804 793433 := bstep (se 2 (by rfl) ⟨297537, by rfl⟩ : syracuseStep 793433 = 595075) B595075
theorem B433025 : Blo 191804 433025 := bstep (se 2 (by rfl) ⟨162384, by rfl⟩ : syracuseStep 433025 = 324769) B324769
theorem B367553 : Blo 191804 367553 := bstep (se 2 (by rfl) ⟨137832, by rfl⟩ : syracuseStep 367553 = 275665) B275665
theorem B760769 : Blo 191804 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B433241 : Blo 191804 433241 := bstep (se 2 (by rfl) ⟨162465, by rfl⟩ : syracuseStep 433241 = 324931) B324931
theorem B3054685 : Blo 191804 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B695441 : Blo 191804 695441 := bstep (se 2 (by rfl) ⟨260790, by rfl⟩ : syracuseStep 695441 = 521581) B521581
theorem B433331 : Blo 191804 433331 := bstep (se 1 (by rfl) ⟨324998, by rfl⟩ : syracuseStep 433331 = 649997) B649997
theorem B433367 : Blo 191804 433367 := bstep (se 1 (by rfl) ⟨325025, by rfl⟩ : syracuseStep 433367 = 650051) B650051
theorem B367895 : Blo 191804 367895 := bstep (se 1 (by rfl) ⟨275921, by rfl⟩ : syracuseStep 367895 = 551843) B551843
theorem B466241 : Blo 191804 466241 := bstep (se 2 (by rfl) ⟨174840, by rfl⟩ : syracuseStep 466241 = 349681) B349681
theorem B1580381 : Blo 191804 1580381 := bstep (se 3 (by rfl) ⟨296321, by rfl⟩ : syracuseStep 1580381 = 592643) B592643
theorem B433547 : Blo 191804 433547 := bstep (se 1 (by rfl) ⟨325160, by rfl⟩ : syracuseStep 433547 = 650321) B650321
theorem B433601 : Blo 191804 433601 := bstep (se 2 (by rfl) ⟨162600, by rfl⟩ : syracuseStep 433601 = 325201) B325201
theorem B5250577 : Blo 191804 5250577 := bstep (se 2 (by rfl) ⟨1968966, by rfl⟩ : syracuseStep 5250577 = 3937933) B3937933
theorem B892433 : Blo 191804 892433 := bstep (se 2 (by rfl) ⟨334662, by rfl⟩ : syracuseStep 892433 = 669325) B669325
theorem B728621 : Blo 191804 728621 := bstep (se 3 (by rfl) ⟨136616, by rfl⟩ : syracuseStep 728621 = 273233) B273233
theorem B433817 : Blo 191804 433817 := bstep (se 2 (by rfl) ⟨162681, by rfl⟩ : syracuseStep 433817 = 325363) B325363
theorem B433907 : Blo 191804 433907 := bstep (se 1 (by rfl) ⟨325430, by rfl⟩ : syracuseStep 433907 = 650861) B650861
theorem B433943 : Blo 191804 433943 := bstep (se 1 (by rfl) ⟨325457, by rfl⟩ : syracuseStep 433943 = 650915) B650915
theorem B368563 : Blo 191804 368563 := bstep (se 1 (by rfl) ⟨276422, by rfl⟩ : syracuseStep 368563 = 552845) B552845
theorem B434123 : Blo 191804 434123 := bstep (se 1 (by rfl) ⟨325592, by rfl⟩ : syracuseStep 434123 = 651185) B651185
theorem B434177 : Blo 191804 434177 := bstep (se 2 (by rfl) ⟨162816, by rfl⟩ : syracuseStep 434177 = 325633) B325633
theorem B3317777 : Blo 191804 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B4169879 : Blo 191804 4169879 := bstep (se 1 (by rfl) ⟨3127409, by rfl⟩ : syracuseStep 4169879 = 6254819) B6254819
theorem B434393 : Blo 191804 434393 := bstep (se 2 (by rfl) ⟨162897, by rfl⟩ : syracuseStep 434393 = 325795) B325795
theorem B729395 : Blo 191804 729395 := bstep (se 1 (by rfl) ⟨547046, by rfl⟩ : syracuseStep 729395 = 1094093) B1094093
theorem B434483 : Blo 191804 434483 := bstep (se 1 (by rfl) ⟨325862, by rfl⟩ : syracuseStep 434483 = 651725) B651725
theorem B434519 : Blo 191804 434519 := bstep (se 1 (by rfl) ⟨325889, by rfl⟩ : syracuseStep 434519 = 651779) B651779
theorem B369011 : Blo 191804 369011 := bstep (se 1 (by rfl) ⟨276758, by rfl⟩ : syracuseStep 369011 = 553517) B553517
theorem B369049 : Blo 191804 369049 := bstep (se 2 (by rfl) ⟨138393, by rfl⟩ : syracuseStep 369049 = 276787) B276787
theorem B1647053 : Blo 191804 1647053 := bstep (se 3 (by rfl) ⟨308822, by rfl⟩ : syracuseStep 1647053 = 617645) B617645
theorem B434699 : Blo 191804 434699 := bstep (se 1 (by rfl) ⟨326024, by rfl⟩ : syracuseStep 434699 = 652049) B652049
theorem B434753 : Blo 191804 434753 := bstep (se 2 (by rfl) ⟨163032, by rfl⟩ : syracuseStep 434753 = 326065) B326065
theorem B434969 : Blo 191804 434969 := bstep (se 2 (by rfl) ⟨163113, by rfl⟩ : syracuseStep 434969 = 326227) B326227
theorem B369497 : Blo 191804 369497 := bstep (se 2 (by rfl) ⟨138561, by rfl⟩ : syracuseStep 369497 = 277123) B277123
theorem B435059 : Blo 191804 435059 := bstep (se 1 (by rfl) ⟨326294, by rfl⟩ : syracuseStep 435059 = 652589) B652589
theorem B435095 : Blo 191804 435095 := bstep (se 1 (by rfl) ⟨326321, by rfl⟩ : syracuseStep 435095 = 652643) B652643
theorem B205783 : Blo 191804 205783 := bstep (se 1 (by rfl) ⟨154337, by rfl⟩ : syracuseStep 205783 = 308675) B308675
theorem B435275 : Blo 191804 435275 := bstep (se 1 (by rfl) ⟨326456, by rfl⟩ : syracuseStep 435275 = 652913) B652913
theorem B435329 : Blo 191804 435329 := bstep (se 2 (by rfl) ⟨163248, by rfl⟩ : syracuseStep 435329 = 326497) B326497
theorem B828737 : Blo 191804 828737 := bstep (se 2 (by rfl) ⟨310776, by rfl⟩ : syracuseStep 828737 = 621553) B621553
theorem B206155 : Blo 191804 206155 := bstep (se 1 (by rfl) ⟨154616, by rfl⟩ : syracuseStep 206155 = 309233) B309233
theorem B435545 : Blo 191804 435545 := bstep (se 2 (by rfl) ⟨163329, by rfl⟩ : syracuseStep 435545 = 326659) B326659
theorem B435635 : Blo 191804 435635 := bstep (se 1 (by rfl) ⟨326726, by rfl⟩ : syracuseStep 435635 = 653453) B653453
theorem B435671 : Blo 191804 435671 := bstep (se 1 (by rfl) ⟨326753, by rfl⟩ : syracuseStep 435671 = 653507) B653507
theorem B665111 : Blo 191804 665111 := bstep (se 1 (by rfl) ⟨498833, by rfl⟩ : syracuseStep 665111 = 997667) B997667
theorem B1877539 : Blo 191804 1877539 := bstep (se 1 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 1877539 = 2816309) B2816309
theorem B370241 : Blo 191804 370241 := bstep (se 2 (by rfl) ⟨138840, by rfl⟩ : syracuseStep 370241 = 277681) B277681
theorem B435851 : Blo 191804 435851 := bstep (se 1 (by rfl) ⟨326888, by rfl⟩ : syracuseStep 435851 = 653777) B653777
theorem B829079 : Blo 191804 829079 := bstep (se 1 (by rfl) ⟨621809, by rfl⟩ : syracuseStep 829079 = 1243619) B1243619
theorem B435905 : Blo 191804 435905 := bstep (se 2 (by rfl) ⟨163464, by rfl⟩ : syracuseStep 435905 = 326929) B326929
theorem B927449 : Blo 191804 927449 := bstep (se 2 (by rfl) ⟨347793, by rfl⟩ : syracuseStep 927449 = 695587) B695587
theorem B730883 : Blo 191804 730883 := bstep (se 1 (by rfl) ⟨548162, by rfl⟩ : syracuseStep 730883 = 1096325) B1096325
theorem B370507 : Blo 191804 370507 := bstep (se 1 (by rfl) ⟨277880, by rfl⟩ : syracuseStep 370507 = 555761) B555761
theorem B436121 : Blo 191804 436121 := bstep (se 2 (by rfl) ⟨163545, by rfl⟩ : syracuseStep 436121 = 327091) B327091
theorem B468953 : Blo 191804 468953 := bstep (se 2 (by rfl) ⟨175857, by rfl⟩ : syracuseStep 468953 = 351715) B351715
theorem B436211 : Blo 191804 436211 := bstep (se 1 (by rfl) ⟨327158, by rfl⟩ : syracuseStep 436211 = 654317) B654317
theorem B436247 : Blo 191804 436247 := bstep (se 1 (by rfl) ⟨327185, by rfl⟩ : syracuseStep 436247 = 654371) B654371
theorem B731339 : Blo 191804 731339 := bstep (se 1 (by rfl) ⟨548504, by rfl⟩ : syracuseStep 731339 = 1097009) B1097009
theorem B436427 : Blo 191804 436427 := bstep (se 1 (by rfl) ⟨327320, by rfl⟩ : syracuseStep 436427 = 654641) B654641
theorem B436481 : Blo 191804 436481 := bstep (se 2 (by rfl) ⟨163680, by rfl⟩ : syracuseStep 436481 = 327361) B327361
theorem B370955 : Blo 191804 370955 := bstep (se 1 (by rfl) ⟨278216, by rfl⟩ : syracuseStep 370955 = 556433) B556433
theorem B731537 : Blo 191804 731537 := bstep (se 2 (by rfl) ⟨274326, by rfl⟩ : syracuseStep 731537 = 548653) B548653
theorem B371137 : Blo 191804 371137 := bstep (se 2 (by rfl) ⟨139176, by rfl⟩ : syracuseStep 371137 = 278353) B278353
theorem B436697 : Blo 191804 436697 := bstep (se 2 (by rfl) ⟨163761, by rfl⟩ : syracuseStep 436697 = 327523) B327523
theorem B436787 : Blo 191804 436787 := bstep (se 1 (by rfl) ⟨327590, by rfl⟩ : syracuseStep 436787 = 655181) B655181
theorem B928331 : Blo 191804 928331 := bstep (se 1 (by rfl) ⟨696248, by rfl⟩ : syracuseStep 928331 = 1392497) B1392497
theorem B436823 : Blo 191804 436823 := bstep (se 1 (by rfl) ⟨327617, by rfl⟩ : syracuseStep 436823 = 655235) B655235
theorem B1288921 : Blo 191804 1288921 := bstep (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) B966691
theorem B2501381 : Blo 191804 2501381 := bstep (se 4 (by rfl) ⟨234504, by rfl⟩ : syracuseStep 2501381 = 469009) B469009
theorem B437003 : Blo 191804 437003 := bstep (se 1 (by rfl) ⟨327752, by rfl⟩ : syracuseStep 437003 = 655505) B655505
theorem B371479 : Blo 191804 371479 := bstep (se 1 (by rfl) ⟨278609, by rfl⟩ : syracuseStep 371479 = 557219) B557219
theorem B437057 : Blo 191804 437057 := bstep (se 2 (by rfl) ⟨163896, by rfl⟩ : syracuseStep 437057 = 327793) B327793
theorem B371699 : Blo 191804 371699 := bstep (se 1 (by rfl) ⟨278774, by rfl⟩ : syracuseStep 371699 = 557549) B557549
theorem B437273 : Blo 191804 437273 := bstep (se 2 (by rfl) ⟨163977, by rfl⟩ : syracuseStep 437273 = 327955) B327955
theorem B437363 : Blo 191804 437363 := bstep (se 1 (by rfl) ⟨328022, by rfl⟩ : syracuseStep 437363 = 656045) B656045
theorem B732311 : Blo 191804 732311 := bstep (se 1 (by rfl) ⟨549233, by rfl⟩ : syracuseStep 732311 = 1098467) B1098467
theorem B437399 : Blo 191804 437399 := bstep (se 1 (by rfl) ⟨328049, by rfl⟩ : syracuseStep 437399 = 656099) B656099
theorem B437579 : Blo 191804 437579 := bstep (se 1 (by rfl) ⟨328184, by rfl⟩ : syracuseStep 437579 = 656369) B656369
theorem B732509 : Blo 191804 732509 := bstep (se 3 (by rfl) ⟨137345, by rfl⟩ : syracuseStep 732509 = 274691) B274691
theorem B437633 : Blo 191804 437633 := bstep (se 2 (by rfl) ⟨164112, by rfl⟩ : syracuseStep 437633 = 328225) B328225
theorem B437849 : Blo 191804 437849 := bstep (se 2 (by rfl) ⟨164193, by rfl⟩ : syracuseStep 437849 = 328387) B328387
theorem B700055 : Blo 191804 700055 := bstep (se 1 (by rfl) ⟨525041, by rfl⟩ : syracuseStep 700055 = 1050083) B1050083
theorem B1584791 : Blo 191804 1584791 := bstep (se 1 (by rfl) ⟨1188593, by rfl⟩ : syracuseStep 1584791 = 2377187) B2377187
theorem B437939 : Blo 191804 437939 := bstep (se 1 (by rfl) ⟨328454, by rfl⟩ : syracuseStep 437939 = 656909) B656909
theorem B437975 : Blo 191804 437975 := bstep (se 1 (by rfl) ⟨328481, by rfl⟩ : syracuseStep 437975 = 656963) B656963
theorem B831197 : Blo 191804 831197 := bstep (se 3 (by rfl) ⟨155849, by rfl⟩ : syracuseStep 831197 = 311699) B311699
theorem B438155 : Blo 191804 438155 := bstep (se 1 (by rfl) ⟨328616, by rfl⟩ : syracuseStep 438155 = 657233) B657233
theorem B438209 : Blo 191804 438209 := bstep (se 2 (by rfl) ⟨164328, by rfl⟩ : syracuseStep 438209 = 328657) B328657
theorem B208855 : Blo 191804 208855 := bstep (se 1 (by rfl) ⟨156641, by rfl⟩ : syracuseStep 208855 = 313283) B313283
theorem B831505 : Blo 191804 831505 := bstep (se 2 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 831505 = 623629) B623629
theorem B831539 : Blo 191804 831539 := bstep (se 1 (by rfl) ⟨623654, by rfl⟩ : syracuseStep 831539 = 1247309) B1247309
theorem B438425 : Blo 191804 438425 := bstep (se 2 (by rfl) ⟨164409, by rfl⟩ : syracuseStep 438425 = 328819) B328819
theorem B1781939 : Blo 191804 1781939 := bstep (se 1 (by rfl) ⟨1336454, by rfl⟩ : syracuseStep 1781939 = 2672909) B2672909
theorem B438515 : Blo 191804 438515 := bstep (se 1 (by rfl) ⟨328886, by rfl⟩ : syracuseStep 438515 = 657773) B657773
theorem B438551 : Blo 191804 438551 := bstep (se 1 (by rfl) ⟨328913, by rfl⟩ : syracuseStep 438551 = 657827) B657827
theorem B438731 : Blo 191804 438731 := bstep (se 1 (by rfl) ⟨329048, by rfl⟩ : syracuseStep 438731 = 658097) B658097
theorem B438785 : Blo 191804 438785 := bstep (se 2 (by rfl) ⟨164544, by rfl⟩ : syracuseStep 438785 = 329089) B329089
theorem B439001 : Blo 191804 439001 := bstep (se 2 (by rfl) ⟨164625, by rfl⟩ : syracuseStep 439001 = 329251) B329251
theorem B439091 : Blo 191804 439091 := bstep (se 1 (by rfl) ⟨329318, by rfl⟩ : syracuseStep 439091 = 658637) B658637
theorem B439127 : Blo 191804 439127 := bstep (se 1 (by rfl) ⟨329345, by rfl⟩ : syracuseStep 439127 = 658691) B658691
theorem B1356695 : Blo 191804 1356695 := bstep (se 1 (by rfl) ⟨1017521, by rfl⟩ : syracuseStep 1356695 = 2035043) B2035043
theorem B439307 : Blo 191804 439307 := bstep (se 1 (by rfl) ⟨329480, by rfl⟩ : syracuseStep 439307 = 658961) B658961
theorem B439319 : Blo 191804 439319 := bstep (se 1 (by rfl) ⟨329489, by rfl⟩ : syracuseStep 439319 = 658979) B658979
theorem B439361 : Blo 191804 439361 := bstep (se 2 (by rfl) ⟨164760, by rfl⟩ : syracuseStep 439361 = 329521) B329521
theorem B2831435 : Blo 191804 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B439447 : Blo 191804 439447 := bstep (se 1 (by rfl) ⟨329585, by rfl⟩ : syracuseStep 439447 = 659171) B659171
theorem B734467 : Blo 191804 734467 := bstep (se 1 (by rfl) ⟨550850, by rfl⟩ : syracuseStep 734467 = 1101701) B1101701
theorem B439577 : Blo 191804 439577 := bstep (se 2 (by rfl) ⟨164841, by rfl⟩ : syracuseStep 439577 = 329683) B329683
theorem B439667 : Blo 191804 439667 := bstep (se 1 (by rfl) ⟨329750, by rfl⟩ : syracuseStep 439667 = 659501) B659501
theorem B439703 : Blo 191804 439703 := bstep (se 1 (by rfl) ⟨329777, by rfl⟩ : syracuseStep 439703 = 659555) B659555
theorem B374233 : Blo 191804 374233 := bstep (se 2 (by rfl) ⟨140337, by rfl⟩ : syracuseStep 374233 = 280675) B280675
theorem B2668049 : Blo 191804 2668049 := bstep (se 2 (by rfl) ⟨1000518, by rfl⟩ : syracuseStep 2668049 = 2001037) B2001037
theorem B800279 : Blo 191804 800279 := bstep (se 1 (by rfl) ⟨600209, by rfl⟩ : syracuseStep 800279 = 1200419) B1200419
theorem B734771 : Blo 191804 734771 := bstep (se 1 (by rfl) ⟨551078, by rfl⟩ : syracuseStep 734771 = 1102157) B1102157
theorem B702017 : Blo 191804 702017 := bstep (se 2 (by rfl) ⟨263256, by rfl⟩ : syracuseStep 702017 = 526513) B526513
theorem B439883 : Blo 191804 439883 := bstep (se 1 (by rfl) ⟨329912, by rfl⟩ : syracuseStep 439883 = 659825) B659825
theorem B439937 : Blo 191804 439937 := bstep (se 2 (by rfl) ⟨164976, by rfl⟩ : syracuseStep 439937 = 329953) B329953
theorem B243415 : Blo 191804 243415 := bstep (se 1 (by rfl) ⟨182561, by rfl⟩ : syracuseStep 243415 = 365123) B365123
theorem B931601 : Blo 191804 931601 := bstep (se 2 (by rfl) ⟨349350, by rfl⟩ : syracuseStep 931601 = 698701) B698701
theorem B440153 : Blo 191804 440153 := bstep (se 2 (by rfl) ⟨165057, by rfl⟩ : syracuseStep 440153 = 330115) B330115
theorem B833453 : Blo 191804 833453 := bstep (se 3 (by rfl) ⟨156272, by rfl⟩ : syracuseStep 833453 = 312545) B312545
theorem B440243 : Blo 191804 440243 := bstep (se 1 (by rfl) ⟨330182, by rfl⟩ : syracuseStep 440243 = 660365) B660365
theorem B440279 : Blo 191804 440279 := bstep (se 1 (by rfl) ⟨330209, by rfl⟩ : syracuseStep 440279 = 660419) B660419
theorem B440459 : Blo 191804 440459 := bstep (se 1 (by rfl) ⟨330344, by rfl⟩ : syracuseStep 440459 = 660689) B660689
theorem B735425 : Blo 191804 735425 := bstep (se 2 (by rfl) ⟨275784, by rfl⟩ : syracuseStep 735425 = 551569) B551569
theorem B440513 : Blo 191804 440513 := bstep (se 2 (by rfl) ⟨165192, by rfl⟩ : syracuseStep 440513 = 330385) B330385
theorem B440587 : Blo 191804 440587 := bstep (se 1 (by rfl) ⟨330440, by rfl⟩ : syracuseStep 440587 = 660881) B660881
theorem B244235 : Blo 191804 244235 := bstep (se 1 (by rfl) ⟨183176, by rfl⟩ : syracuseStep 244235 = 366353) B366353
theorem B277015 : Blo 191804 277015 := bstep (se 1 (by rfl) ⟨207761, by rfl⟩ : syracuseStep 277015 = 415523) B415523
theorem B375385 : Blo 191804 375385 := bstep (se 2 (by rfl) ⟨140769, by rfl⟩ : syracuseStep 375385 = 281539) B281539
theorem B834137 : Blo 191804 834137 := bstep (se 2 (by rfl) ⟨312801, by rfl⟩ : syracuseStep 834137 = 625603) B625603
theorem B4209245 : Blo 191804 4209245 := bstep (se 3 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 4209245 = 1578467) B1578467
theorem B1457027 : Blo 191804 1457027 := bstep (se 1 (by rfl) ⟨1092770, by rfl⟩ : syracuseStep 1457027 = 2185541) B2185541
theorem B3521549 : Blo 191804 3521549 := bstep (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) B1320581
theorem B244939 : Blo 191804 244939 := bstep (se 1 (by rfl) ⟨183704, by rfl⟩ : syracuseStep 244939 = 367409) B367409
theorem B736685 : Blo 191804 736685 := bstep (se 3 (by rfl) ⟨138128, by rfl⟩ : syracuseStep 736685 = 276257) B276257
theorem B736715 : Blo 191804 736715 := bstep (se 1 (by rfl) ⟨552536, by rfl⟩ : syracuseStep 736715 = 1105073) B1105073
theorem B245207 : Blo 191804 245207 := bstep (se 1 (by rfl) ⟨183905, by rfl⟩ : syracuseStep 245207 = 367811) B367811
theorem B310873 : Blo 191804 310873 := bstep (se 2 (by rfl) ⟨116577, by rfl⟩ : syracuseStep 310873 = 233155) B233155
theorem B1392419 : Blo 191804 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B737369 : Blo 191804 737369 := bstep (se 2 (by rfl) ⟨276513, by rfl⟩ : syracuseStep 737369 = 553027) B553027
theorem B245911 : Blo 191804 245911 := bstep (se 1 (by rfl) ⟨184433, by rfl⟩ : syracuseStep 245911 = 368867) B368867
theorem B737687 : Blo 191804 737687 := bstep (se 1 (by rfl) ⟨553265, by rfl⟩ : syracuseStep 737687 = 1106531) B1106531
theorem B410123 : Blo 191804 410123 := bstep (se 1 (by rfl) ⟨307592, by rfl⟩ : syracuseStep 410123 = 615185) B615185
theorem B5686193 : Blo 191804 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B738355 : Blo 191804 738355 := bstep (se 1 (by rfl) ⟨553766, by rfl⟩ : syracuseStep 738355 = 1107533) B1107533
theorem B410969 : Blo 191804 410969 := bstep (se 2 (by rfl) ⟨154113, by rfl⟩ : syracuseStep 410969 = 308227) B308227
theorem B706099 : Blo 191804 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B1328791 : Blo 191804 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B1754945 : Blo 191804 1754945 := bstep (se 2 (by rfl) ⟨658104, by rfl⟩ : syracuseStep 1754945 = 1316209) B1316209
theorem B247627 : Blo 191804 247627 := bstep (se 1 (by rfl) ⟨185720, by rfl⟩ : syracuseStep 247627 = 371441) B371441
theorem B444311 : Blo 191804 444311 := bstep (se 1 (by rfl) ⟨333233, by rfl⟩ : syracuseStep 444311 = 666467) B666467
theorem B346049 : Blo 191804 346049 := bstep (se 2 (by rfl) ⟨129768, by rfl⟩ : syracuseStep 346049 = 259537) B259537
theorem B411635 : Blo 191804 411635 := bstep (se 1 (by rfl) ⟨308726, by rfl⟩ : syracuseStep 411635 = 617453) B617453
theorem B1427633 : Blo 191804 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B1460429 : Blo 191804 1460429 := bstep (se 3 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 1460429 = 547661) B547661
theorem B739601 : Blo 191804 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B1395265 : Blo 191804 1395265 := bstep (se 2 (by rfl) ⟨523224, by rfl⟩ : syracuseStep 1395265 = 1046449) B1046449
theorem B1460915 : Blo 191804 1460915 := bstep (se 1 (by rfl) ⟨1095686, by rfl⟩ : syracuseStep 1460915 = 2191373) B2191373
theorem B215851 : Blo 191804 215851 := bstep (se 1 (by rfl) ⟨161888, by rfl⟩ : syracuseStep 215851 = 323777) B323777
theorem B2214701 : Blo 191804 2214701 := bstep (se 3 (by rfl) ⟨415256, by rfl⟩ : syracuseStep 2214701 = 830513) B830513
theorem B248651 : Blo 191804 248651 := bstep (se 1 (by rfl) ⟨186488, by rfl⟩ : syracuseStep 248651 = 372977) B372977
theorem B707417 : Blo 191804 707417 := bstep (se 2 (by rfl) ⟨265281, by rfl⟩ : syracuseStep 707417 = 530563) B530563
theorem B215959 : Blo 191804 215959 := bstep (se 1 (by rfl) ⟨161969, by rfl⟩ : syracuseStep 215959 = 323939) B323939
theorem B412609 : Blo 191804 412609 := bstep (se 2 (by rfl) ⟨154728, by rfl⟩ : syracuseStep 412609 = 309457) B309457
theorem B740299 : Blo 191804 740299 := bstep (se 1 (by rfl) ⟨555224, by rfl⟩ : syracuseStep 740299 = 1110449) B1110449
theorem B216139 : Blo 191804 216139 := bstep (se 1 (by rfl) ⟨162104, by rfl⟩ : syracuseStep 216139 = 324209) B324209
theorem B1100951 : Blo 191804 1100951 := bstep (se 1 (by rfl) ⟨825713, by rfl⟩ : syracuseStep 1100951 = 1651427) B1651427
theorem B216247 : Blo 191804 216247 := bstep (se 1 (by rfl) ⟨162185, by rfl⟩ : syracuseStep 216247 = 324371) B324371
theorem B412865 : Blo 191804 412865 := bstep (se 2 (by rfl) ⟨154824, by rfl⟩ : syracuseStep 412865 = 309649) B309649
theorem B740573 : Blo 191804 740573 := bstep (se 3 (by rfl) ⟨138857, by rfl⟩ : syracuseStep 740573 = 277715) B277715
theorem B412951 : Blo 191804 412951 := bstep (se 1 (by rfl) ⟨309713, by rfl⟩ : syracuseStep 412951 = 619427) B619427
theorem B216427 : Blo 191804 216427 := bstep (se 1 (by rfl) ⟨162320, by rfl⟩ : syracuseStep 216427 = 324641) B324641
theorem B216535 : Blo 191804 216535 := bstep (se 1 (by rfl) ⟨162401, by rfl⟩ : syracuseStep 216535 = 324803) B324803
theorem B216715 : Blo 191804 216715 := bstep (se 1 (by rfl) ⟨162536, by rfl⟩ : syracuseStep 216715 = 325073) B325073
theorem B216823 : Blo 191804 216823 := bstep (se 1 (by rfl) ⟨162617, by rfl⟩ : syracuseStep 216823 = 325235) B325235
theorem B1265453 : Blo 191804 1265453 := bstep (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) B474545
theorem B741271 : Blo 191804 741271 := bstep (se 1 (by rfl) ⟨555953, by rfl⟩ : syracuseStep 741271 = 1111907) B1111907
theorem B217003 : Blo 191804 217003 := bstep (se 1 (by rfl) ⟨162752, by rfl⟩ : syracuseStep 217003 = 325505) B325505
theorem B217111 : Blo 191804 217111 := bstep (se 1 (by rfl) ⟨162833, by rfl⟩ : syracuseStep 217111 = 325667) B325667
theorem B1462373 : Blo 191804 1462373 := bstep (se 4 (by rfl) ⟨137097, by rfl⟩ : syracuseStep 1462373 = 274195) B274195
theorem B217291 : Blo 191804 217291 := bstep (se 1 (by rfl) ⟨162968, by rfl⟩ : syracuseStep 217291 = 325937) B325937
theorem B4837637 : Blo 191804 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B217399 : Blo 191804 217399 := bstep (se 1 (by rfl) ⟨163049, by rfl⟩ : syracuseStep 217399 = 326099) B326099
theorem B217579 : Blo 191804 217579 := bstep (se 1 (by rfl) ⟨163184, by rfl⟩ : syracuseStep 217579 = 326369) B326369
theorem B1462859 : Blo 191804 1462859 := bstep (se 1 (by rfl) ⟨1097144, by rfl⟩ : syracuseStep 1462859 = 2194289) B2194289
theorem B217687 : Blo 191804 217687 := bstep (se 1 (by rfl) ⟨163265, by rfl⟩ : syracuseStep 217687 = 326531) B326531
theorem B742061 : Blo 191804 742061 := bstep (se 3 (by rfl) ⟨139136, by rfl⟩ : syracuseStep 742061 = 278273) B278273
theorem B217867 : Blo 191804 217867 := bstep (se 1 (by rfl) ⟨163400, by rfl⟩ : syracuseStep 217867 = 326801) B326801
theorem B2380589 : Blo 191804 2380589 := bstep (se 3 (by rfl) ⟨446360, by rfl⟩ : syracuseStep 2380589 = 892721) B892721
theorem B217975 : Blo 191804 217975 := bstep (se 1 (by rfl) ⟨163481, by rfl⟩ : syracuseStep 217975 = 326963) B326963
theorem B218155 : Blo 191804 218155 := bstep (se 1 (by rfl) ⟨163616, by rfl⟩ : syracuseStep 218155 = 327233) B327233
theorem B218263 : Blo 191804 218263 := bstep (se 1 (by rfl) ⟨163697, by rfl⟩ : syracuseStep 218263 = 327395) B327395
theorem B349451 : Blo 191804 349451 := bstep (se 1 (by rfl) ⟨262088, by rfl⟩ : syracuseStep 349451 = 524177) B524177
theorem B218443 : Blo 191804 218443 := bstep (se 1 (by rfl) ⟨163832, by rfl⟩ : syracuseStep 218443 = 327665) B327665
theorem B546227 : Blo 191804 546227 := bstep (se 1 (by rfl) ⟨409670, by rfl⟩ : syracuseStep 546227 = 819341) B819341
theorem B218551 : Blo 191804 218551 := bstep (se 1 (by rfl) ⟨163913, by rfl⟩ : syracuseStep 218551 = 327827) B327827
theorem B218731 : Blo 191804 218731 := bstep (se 1 (by rfl) ⟨164048, by rfl⟩ : syracuseStep 218731 = 328097) B328097
theorem B218839 : Blo 191804 218839 := bstep (se 1 (by rfl) ⟨164129, by rfl⟩ : syracuseStep 218839 = 328259) B328259
theorem B2807557 : Blo 191804 2807557 := bstep (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) B526417
theorem B219019 : Blo 191804 219019 := bstep (se 1 (by rfl) ⟨164264, by rfl⟩ : syracuseStep 219019 = 328529) B328529
theorem B1660823 : Blo 191804 1660823 := bstep (se 1 (by rfl) ⟨1245617, by rfl⟩ : syracuseStep 1660823 = 2491235) B2491235
theorem B415667 : Blo 191804 415667 := bstep (se 1 (by rfl) ⟨311750, by rfl⟩ : syracuseStep 415667 = 623501) B623501
theorem B5593049 : Blo 191804 5593049 := bstep (se 2 (by rfl) ⟨2097393, by rfl⟩ : syracuseStep 5593049 = 4194787) B4194787
theorem B219127 : Blo 191804 219127 := bstep (se 1 (by rfl) ⟨164345, by rfl⟩ : syracuseStep 219127 = 328691) B328691
theorem B219307 : Blo 191804 219307 := bstep (se 1 (by rfl) ⟨164480, by rfl⟩ : syracuseStep 219307 = 328961) B328961
theorem B219415 : Blo 191804 219415 := bstep (se 1 (by rfl) ⟨164561, by rfl⟩ : syracuseStep 219415 = 329123) B329123
theorem B350489 : Blo 191804 350489 := bstep (se 2 (by rfl) ⟨131433, by rfl⟩ : syracuseStep 350489 = 262867) B262867
theorem B2283821 : Blo 191804 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B219595 : Blo 191804 219595 := bstep (se 1 (by rfl) ⟨164696, by rfl⟩ : syracuseStep 219595 = 329393) B329393
theorem B219703 : Blo 191804 219703 := bstep (se 1 (by rfl) ⟨164777, by rfl⟩ : syracuseStep 219703 = 329555) B329555
theorem B219883 : Blo 191804 219883 := bstep (se 1 (by rfl) ⟨164912, by rfl⟩ : syracuseStep 219883 = 329825) B329825
theorem B1170251 : Blo 191804 1170251 := bstep (se 1 (by rfl) ⟨877688, by rfl⟩ : syracuseStep 1170251 = 1755377) B1755377
theorem B219991 : Blo 191804 219991 := bstep (se 1 (by rfl) ⟨164993, by rfl⟩ : syracuseStep 219991 = 329987) B329987
theorem B351065 : Blo 191804 351065 := bstep (se 2 (by rfl) ⟨131649, by rfl⟩ : syracuseStep 351065 = 263299) B263299
theorem B351179 : Blo 191804 351179 := bstep (se 1 (by rfl) ⟨263384, by rfl⟩ : syracuseStep 351179 = 526769) B526769
theorem B220171 : Blo 191804 220171 := bstep (se 1 (by rfl) ⟨165128, by rfl⟩ : syracuseStep 220171 = 330257) B330257
theorem B220279 : Blo 191804 220279 := bstep (se 1 (by rfl) ⟨165209, by rfl⟩ : syracuseStep 220279 = 330419) B330419
theorem B351371 : Blo 191804 351371 := bstep (se 1 (by rfl) ⟨263528, by rfl⟩ : syracuseStep 351371 = 527057) B527057
theorem B416983 : Blo 191804 416983 := bstep (se 1 (by rfl) ⟨312737, by rfl⟩ : syracuseStep 416983 = 625475) B625475
theorem B417163 : Blo 191804 417163 := bstep (se 1 (by rfl) ⟨312872, by rfl⟩ : syracuseStep 417163 = 625745) B625745
theorem B548299 : Blo 191804 548299 := bstep (se 1 (by rfl) ⟨411224, by rfl⟩ : syracuseStep 548299 = 822449) B822449
theorem B417239 : Blo 191804 417239 := bstep (se 1 (by rfl) ⟨312929, by rfl⟩ : syracuseStep 417239 = 625859) B625859
theorem B220663 : Blo 191804 220663 := bstep (se 1 (by rfl) ⟨165497, by rfl⟩ : syracuseStep 220663 = 330995) B330995
theorem B1236545 : Blo 191804 1236545 := bstep (se 2 (by rfl) ⟨463704, by rfl⟩ : syracuseStep 1236545 = 927409) B927409
theorem B974429 : Blo 191804 974429 := bstep (se 3 (by rfl) ⟨182705, by rfl⟩ : syracuseStep 974429 = 365411) B365411
theorem B351959 : Blo 191804 351959 := bstep (se 1 (by rfl) ⟨263969, by rfl⟩ : syracuseStep 351959 = 527939) B527939
theorem B1105757 : Blo 191804 1105757 := bstep (se 3 (by rfl) ⟨207329, by rfl⟩ : syracuseStep 1105757 = 414659) B414659
theorem B1859429 : Blo 191804 1859429 := bstep (se 4 (by rfl) ⟨174321, by rfl⟩ : syracuseStep 1859429 = 348643) B348643
theorem B941975 : Blo 191804 941975 := bstep (se 1 (by rfl) ⟨706481, by rfl⟩ : syracuseStep 941975 = 1412963) B1412963
theorem B3563443 : Blo 191804 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B548801 : Blo 191804 548801 := bstep (se 2 (by rfl) ⟨205800, by rfl⟩ : syracuseStep 548801 = 411601) B411601
theorem B1335361 : Blo 191804 1335361 := bstep (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) B1001521
theorem B2089091 : Blo 191804 2089091 := bstep (se 1 (by rfl) ⟨1566818, by rfl⟩ : syracuseStep 2089091 = 3133637) B3133637
theorem B549143 : Blo 191804 549143 := bstep (se 1 (by rfl) ⟨411857, by rfl⟩ : syracuseStep 549143 = 823715) B823715
theorem B876851 : Blo 191804 876851 := bstep (se 1 (by rfl) ⟨657638, by rfl⟩ : syracuseStep 876851 = 1315277) B1315277
theorem B647513 : Blo 191804 647513 := bstep (se 2 (by rfl) ⟨242817, by rfl⟩ : syracuseStep 647513 = 485635) B485635
theorem B1171805 : Blo 191804 1171805 := bstep (se 3 (by rfl) ⟨219713, by rfl⟩ : syracuseStep 1171805 = 439427) B439427
theorem B778675 : Blo 191804 778675 := bstep (se 1 (by rfl) ⟨584006, by rfl⟩ : syracuseStep 778675 = 1168013) B1168013
theorem B648215 : Blo 191804 648215 := bstep (se 1 (by rfl) ⟨486161, by rfl⟩ : syracuseStep 648215 = 972323) B972323
theorem B287819 : Blo 191804 287819 := bstep (se 1 (by rfl) ⟨215864, by rfl⟩ : syracuseStep 287819 = 431729) B431729
theorem B287831 : Blo 191804 287831 := bstep (se 1 (by rfl) ⟨215873, by rfl⟩ : syracuseStep 287831 = 431747) B431747
theorem B746647 : Blo 191804 746647 := bstep (se 1 (by rfl) ⟨559985, by rfl⟩ : syracuseStep 746647 = 1119971) B1119971
theorem B287897 : Blo 191804 287897 := bstep (se 2 (by rfl) ⟨107961, by rfl⟩ : syracuseStep 287897 = 215923) B215923
theorem B288011 : Blo 191804 288011 := bstep (se 1 (by rfl) ⟨216008, by rfl⟩ : syracuseStep 288011 = 432017) B432017
theorem B288023 : Blo 191804 288023 := bstep (se 1 (by rfl) ⟨216017, by rfl⟩ : syracuseStep 288023 = 432035) B432035
theorem B288089 : Blo 191804 288089 := bstep (se 2 (by rfl) ⟨108033, by rfl⟩ : syracuseStep 288089 = 216067) B216067
theorem B779651 : Blo 191804 779651 := bstep (se 1 (by rfl) ⟨584738, by rfl⟩ : syracuseStep 779651 = 1169477) B1169477
theorem B288203 : Blo 191804 288203 := bstep (se 1 (by rfl) ⟨216152, by rfl⟩ : syracuseStep 288203 = 432305) B432305
theorem B288215 : Blo 191804 288215 := bstep (se 1 (by rfl) ⟨216161, by rfl⟩ : syracuseStep 288215 = 432323) B432323
theorem B288281 : Blo 191804 288281 := bstep (se 2 (by rfl) ⟨108105, by rfl⟩ : syracuseStep 288281 = 216211) B216211
theorem B648755 : Blo 191804 648755 := bstep (se 1 (by rfl) ⟨486566, by rfl⟩ : syracuseStep 648755 = 973133) B973133
theorem B288395 : Blo 191804 288395 := bstep (se 1 (by rfl) ⟨216296, by rfl⟩ : syracuseStep 288395 = 432593) B432593
theorem B288407 : Blo 191804 288407 := bstep (se 1 (by rfl) ⟨216305, by rfl⟩ : syracuseStep 288407 = 432611) B432611
theorem B976535 : Blo 191804 976535 := bstep (se 1 (by rfl) ⟨732401, by rfl⟩ : syracuseStep 976535 = 1464803) B1464803
theorem B353945 : Blo 191804 353945 := bstep (se 2 (by rfl) ⟨132729, by rfl⟩ : syracuseStep 353945 = 265459) B265459
theorem B288473 : Blo 191804 288473 := bstep (se 2 (by rfl) ⟨108177, by rfl⟩ : syracuseStep 288473 = 216355) B216355
theorem B1468205 : Blo 191804 1468205 := bstep (se 3 (by rfl) ⟨275288, by rfl⟩ : syracuseStep 1468205 = 550577) B550577
theorem B649025 : Blo 191804 649025 := bstep (se 2 (by rfl) ⟨243384, by rfl⟩ : syracuseStep 649025 = 486769) B486769
theorem B288587 : Blo 191804 288587 := bstep (se 1 (by rfl) ⟨216440, by rfl⟩ : syracuseStep 288587 = 432881) B432881
theorem B288599 : Blo 191804 288599 := bstep (se 1 (by rfl) ⟨216449, by rfl⟩ : syracuseStep 288599 = 432899) B432899
theorem B288665 : Blo 191804 288665 := bstep (se 2 (by rfl) ⟨108249, by rfl⟩ : syracuseStep 288665 = 216499) B216499
theorem B288779 : Blo 191804 288779 := bstep (se 1 (by rfl) ⟨216584, by rfl⟩ : syracuseStep 288779 = 433169) B433169
theorem B288791 : Blo 191804 288791 := bstep (se 1 (by rfl) ⟨216593, by rfl⟩ : syracuseStep 288791 = 433187) B433187
theorem B288857 : Blo 191804 288857 := bstep (se 2 (by rfl) ⟨108321, by rfl⟩ : syracuseStep 288857 = 216643) B216643
theorem B583859 : Blo 191804 583859 := bstep (se 1 (by rfl) ⟨437894, by rfl⟩ : syracuseStep 583859 = 875789) B875789
theorem B288971 : Blo 191804 288971 := bstep (se 1 (by rfl) ⟨216728, by rfl⟩ : syracuseStep 288971 = 433457) B433457
theorem B288983 : Blo 191804 288983 := bstep (se 1 (by rfl) ⟨216737, by rfl⟩ : syracuseStep 288983 = 433475) B433475
theorem B1108241 : Blo 191804 1108241 := bstep (se 2 (by rfl) ⟨415590, by rfl⟩ : syracuseStep 1108241 = 831181) B831181
theorem B289049 : Blo 191804 289049 := bstep (se 2 (by rfl) ⟨108393, by rfl⟩ : syracuseStep 289049 = 216787) B216787
theorem B649565 : Blo 191804 649565 := bstep (se 3 (by rfl) ⟨121793, by rfl⟩ : syracuseStep 649565 = 243587) B243587
theorem B551261 : Blo 191804 551261 := bstep (se 3 (by rfl) ⟨103361, by rfl⟩ : syracuseStep 551261 = 206723) B206723
theorem B289163 : Blo 191804 289163 := bstep (se 1 (by rfl) ⟨216872, by rfl⟩ : syracuseStep 289163 = 433745) B433745
theorem B289175 : Blo 191804 289175 := bstep (se 1 (by rfl) ⟨216881, by rfl⟩ : syracuseStep 289175 = 433763) B433763
theorem B289241 : Blo 191804 289241 := bstep (se 2 (by rfl) ⟨108465, by rfl⟩ : syracuseStep 289241 = 216931) B216931
theorem B485939 : Blo 191804 485939 := bstep (se 1 (by rfl) ⟨364454, by rfl⟩ : syracuseStep 485939 = 728909) B728909
theorem B289355 : Blo 191804 289355 := bstep (se 1 (by rfl) ⟨217016, by rfl⟩ : syracuseStep 289355 = 434033) B434033
theorem B289367 : Blo 191804 289367 := bstep (se 1 (by rfl) ⟨217025, by rfl⟩ : syracuseStep 289367 = 434051) B434051
theorem B289433 : Blo 191804 289433 := bstep (se 2 (by rfl) ⟨108537, by rfl⟩ : syracuseStep 289433 = 217075) B217075
theorem B879277 : Blo 191804 879277 := bstep (se 3 (by rfl) ⟨164864, by rfl⟩ : syracuseStep 879277 = 329729) B329729
theorem B551603 : Blo 191804 551603 := bstep (se 1 (by rfl) ⟨413702, by rfl⟩ : syracuseStep 551603 = 827405) B827405
theorem B289547 : Blo 191804 289547 := bstep (se 1 (by rfl) ⟨217160, by rfl⟩ : syracuseStep 289547 = 434321) B434321
theorem B289559 : Blo 191804 289559 := bstep (se 1 (by rfl) ⟨217169, by rfl⟩ : syracuseStep 289559 = 434339) B434339
theorem B486233 : Blo 191804 486233 := bstep (se 2 (by rfl) ⟨182337, by rfl⟩ : syracuseStep 486233 = 364675) B364675
theorem B289625 : Blo 191804 289625 := bstep (se 2 (by rfl) ⟨108609, by rfl⟩ : syracuseStep 289625 = 217219) B217219
theorem B289739 : Blo 191804 289739 := bstep (se 1 (by rfl) ⟨217304, by rfl⟩ : syracuseStep 289739 = 434609) B434609
theorem B289751 : Blo 191804 289751 := bstep (se 1 (by rfl) ⟨217313, by rfl⟩ : syracuseStep 289751 = 434627) B434627
theorem B289817 : Blo 191804 289817 := bstep (se 2 (by rfl) ⟨108681, by rfl⟩ : syracuseStep 289817 = 217363) B217363
theorem B289931 : Blo 191804 289931 := bstep (se 1 (by rfl) ⟨217448, by rfl⟩ : syracuseStep 289931 = 434897) B434897
theorem B289943 : Blo 191804 289943 := bstep (se 1 (by rfl) ⟨217457, by rfl⟩ : syracuseStep 289943 = 434915) B434915
theorem B1633459 : Blo 191804 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B584921 : Blo 191804 584921 := bstep (se 2 (by rfl) ⟨219345, by rfl⟩ : syracuseStep 584921 = 438691) B438691
theorem B290009 : Blo 191804 290009 := bstep (se 2 (by rfl) ⟨108753, by rfl⟩ : syracuseStep 290009 = 217507) B217507
theorem B191819 : Blo 191804 191819 := bstep (se 1 (by rfl) ⟨143864, by rfl⟩ : syracuseStep 191819 = 287729) B287729
theorem B290123 : Blo 191804 290123 := bstep (se 1 (by rfl) ⟨217592, by rfl⟩ : syracuseStep 290123 = 435185) B435185
theorem B191831 : Blo 191804 191831 := bstep (se 1 (by rfl) ⟨143873, by rfl⟩ : syracuseStep 191831 = 287747) B287747
theorem B290135 : Blo 191804 290135 := bstep (se 1 (by rfl) ⟨217601, by rfl⟩ : syracuseStep 290135 = 435203) B435203
theorem B191851 : Blo 191804 191851 := bstep (se 1 (by rfl) ⟨143888, by rfl⟩ : syracuseStep 191851 = 287777) B287777
theorem B191863 : Blo 191804 191863 := bstep (se 1 (by rfl) ⟨143897, by rfl⟩ : syracuseStep 191863 = 287795) B287795
theorem B191883 : Blo 191804 191883 := bstep (se 1 (by rfl) ⟨143912, by rfl⟩ : syracuseStep 191883 = 287825) B287825
theorem B191895 : Blo 191804 191895 := bstep (se 1 (by rfl) ⟨143921, by rfl⟩ : syracuseStep 191895 = 287843) B287843
theorem B290201 : Blo 191804 290201 := bstep (se 2 (by rfl) ⟨108825, by rfl⟩ : syracuseStep 290201 = 217651) B217651
theorem B191915 : Blo 191804 191915 := bstep (se 1 (by rfl) ⟨143936, by rfl⟩ : syracuseStep 191915 = 287873) B287873
theorem B191927 : Blo 191804 191927 := bstep (se 1 (by rfl) ⟨143945, by rfl⟩ : syracuseStep 191927 = 287891) B287891
theorem B191947 : Blo 191804 191947 := bstep (se 1 (by rfl) ⟨143960, by rfl⟩ : syracuseStep 191947 = 287921) B287921
theorem B650699 : Blo 191804 650699 := bstep (se 1 (by rfl) ⟨488024, by rfl⟩ : syracuseStep 650699 = 976049) B976049
theorem B191959 : Blo 191804 191959 := bstep (se 1 (by rfl) ⟨143969, by rfl⟩ : syracuseStep 191959 = 287939) B287939
theorem B191979 : Blo 191804 191979 := bstep (se 1 (by rfl) ⟨143984, by rfl⟩ : syracuseStep 191979 = 287969) B287969
theorem B191991 : Blo 191804 191991 := bstep (se 1 (by rfl) ⟨143993, by rfl⟩ : syracuseStep 191991 = 287987) B287987
theorem B192011 : Blo 191804 192011 := bstep (se 1 (by rfl) ⟨144008, by rfl⟩ : syracuseStep 192011 = 288017) B288017
theorem B290315 : Blo 191804 290315 := bstep (se 1 (by rfl) ⟨217736, by rfl⟩ : syracuseStep 290315 = 435473) B435473
theorem B192023 : Blo 191804 192023 := bstep (se 1 (by rfl) ⟨144017, by rfl⟩ : syracuseStep 192023 = 288035) B288035
theorem B290327 : Blo 191804 290327 := bstep (se 1 (by rfl) ⟨217745, by rfl⟩ : syracuseStep 290327 = 435491) B435491
theorem B192043 : Blo 191804 192043 := bstep (se 1 (by rfl) ⟨144032, by rfl⟩ : syracuseStep 192043 = 288065) B288065
theorem B192055 : Blo 191804 192055 := bstep (se 1 (by rfl) ⟨144041, by rfl⟩ : syracuseStep 192055 = 288083) B288083
theorem B192075 : Blo 191804 192075 := bstep (se 1 (by rfl) ⟨144056, by rfl⟩ : syracuseStep 192075 = 288113) B288113
theorem B192087 : Blo 191804 192087 := bstep (se 1 (by rfl) ⟨144065, by rfl⟩ : syracuseStep 192087 = 288131) B288131
theorem B290393 : Blo 191804 290393 := bstep (se 2 (by rfl) ⟨108897, by rfl⟩ : syracuseStep 290393 = 217795) B217795
theorem B192107 : Blo 191804 192107 := bstep (se 1 (by rfl) ⟨144080, by rfl⟩ : syracuseStep 192107 = 288161) B288161
theorem B192119 : Blo 191804 192119 := bstep (se 1 (by rfl) ⟨144089, by rfl⟩ : syracuseStep 192119 = 288179) B288179
theorem B192139 : Blo 191804 192139 := bstep (se 1 (by rfl) ⟨144104, by rfl⟩ : syracuseStep 192139 = 288209) B288209
theorem B192151 : Blo 191804 192151 := bstep (se 1 (by rfl) ⟨144113, by rfl⟩ : syracuseStep 192151 = 288227) B288227
theorem B192171 : Blo 191804 192171 := bstep (se 1 (by rfl) ⟨144128, by rfl⟩ : syracuseStep 192171 = 288257) B288257
theorem B192183 : Blo 191804 192183 := bstep (se 1 (by rfl) ⟨144137, by rfl⟩ : syracuseStep 192183 = 288275) B288275
theorem B192203 : Blo 191804 192203 := bstep (se 1 (by rfl) ⟨144152, by rfl⟩ : syracuseStep 192203 = 288305) B288305
theorem B290507 : Blo 191804 290507 := bstep (se 1 (by rfl) ⟨217880, by rfl⟩ : syracuseStep 290507 = 435761) B435761
theorem B192215 : Blo 191804 192215 := bstep (se 1 (by rfl) ⟨144161, by rfl⟩ : syracuseStep 192215 = 288323) B288323
theorem B290519 : Blo 191804 290519 := bstep (se 1 (by rfl) ⟨217889, by rfl⟩ : syracuseStep 290519 = 435779) B435779
theorem B650969 : Blo 191804 650969 := bstep (se 2 (by rfl) ⟨244113, by rfl⟩ : syracuseStep 650969 = 488227) B488227
theorem B192235 : Blo 191804 192235 := bstep (se 1 (by rfl) ⟨144176, by rfl⟩ : syracuseStep 192235 = 288353) B288353
theorem B192247 : Blo 191804 192247 := bstep (se 1 (by rfl) ⟨144185, by rfl⟩ : syracuseStep 192247 = 288371) B288371
theorem B192267 : Blo 191804 192267 := bstep (se 1 (by rfl) ⟨144200, by rfl⟩ : syracuseStep 192267 = 288401) B288401
theorem B1240849 : Blo 191804 1240849 := bstep (se 2 (by rfl) ⟨465318, by rfl⟩ : syracuseStep 1240849 = 930637) B930637
theorem B192279 : Blo 191804 192279 := bstep (se 1 (by rfl) ⟨144209, by rfl⟩ : syracuseStep 192279 = 288419) B288419
theorem B290585 : Blo 191804 290585 := bstep (se 2 (by rfl) ⟨108969, by rfl⟩ : syracuseStep 290585 = 217939) B217939
theorem B192299 : Blo 191804 192299 := bstep (se 1 (by rfl) ⟨144224, by rfl⟩ : syracuseStep 192299 = 288449) B288449
theorem B192311 : Blo 191804 192311 := bstep (se 1 (by rfl) ⟨144233, by rfl⟩ : syracuseStep 192311 = 288467) B288467
theorem B192331 : Blo 191804 192331 := bstep (se 1 (by rfl) ⟨144248, by rfl⟩ : syracuseStep 192331 = 288497) B288497
theorem B192343 : Blo 191804 192343 := bstep (se 1 (by rfl) ⟨144257, by rfl⟩ : syracuseStep 192343 = 288515) B288515
theorem B192363 : Blo 191804 192363 := bstep (se 1 (by rfl) ⟨144272, by rfl⟩ : syracuseStep 192363 = 288545) B288545
theorem B192375 : Blo 191804 192375 := bstep (se 1 (by rfl) ⟨144281, by rfl⟩ : syracuseStep 192375 = 288563) B288563
theorem B192395 : Blo 191804 192395 := bstep (se 1 (by rfl) ⟨144296, by rfl⟩ : syracuseStep 192395 = 288593) B288593
theorem B290699 : Blo 191804 290699 := bstep (se 1 (by rfl) ⟨218024, by rfl⟩ : syracuseStep 290699 = 436049) B436049
theorem B192407 : Blo 191804 192407 := bstep (se 1 (by rfl) ⟨144305, by rfl⟩ : syracuseStep 192407 = 288611) B288611
theorem B290711 : Blo 191804 290711 := bstep (se 1 (by rfl) ⟨218033, by rfl⟩ : syracuseStep 290711 = 436067) B436067
theorem B192427 : Blo 191804 192427 := bstep (se 1 (by rfl) ⟨144320, by rfl⟩ : syracuseStep 192427 = 288641) B288641
theorem B192439 : Blo 191804 192439 := bstep (se 1 (by rfl) ⟨144329, by rfl⟩ : syracuseStep 192439 = 288659) B288659
theorem B192459 : Blo 191804 192459 := bstep (se 1 (by rfl) ⟨144344, by rfl⟩ : syracuseStep 192459 = 288689) B288689
theorem B192471 : Blo 191804 192471 := bstep (se 1 (by rfl) ⟨144353, by rfl⟩ : syracuseStep 192471 = 288707) B288707
theorem B290777 : Blo 191804 290777 := bstep (se 2 (by rfl) ⟨109041, by rfl⟩ : syracuseStep 290777 = 218083) B218083
theorem B192491 : Blo 191804 192491 := bstep (se 1 (by rfl) ⟨144368, by rfl⟩ : syracuseStep 192491 = 288737) B288737
theorem B192503 : Blo 191804 192503 := bstep (se 1 (by rfl) ⟨144377, by rfl⟩ : syracuseStep 192503 = 288755) B288755
theorem B192523 : Blo 191804 192523 := bstep (se 1 (by rfl) ⟨144392, by rfl⟩ : syracuseStep 192523 = 288785) B288785
theorem B192535 : Blo 191804 192535 := bstep (se 1 (by rfl) ⟨144401, by rfl⟩ : syracuseStep 192535 = 288803) B288803
theorem B192555 : Blo 191804 192555 := bstep (se 1 (by rfl) ⟨144416, by rfl⟩ : syracuseStep 192555 = 288833) B288833
theorem B192567 : Blo 191804 192567 := bstep (se 1 (by rfl) ⟨144425, by rfl⟩ : syracuseStep 192567 = 288851) B288851
theorem B192587 : Blo 191804 192587 := bstep (se 1 (by rfl) ⟨144440, by rfl⟩ : syracuseStep 192587 = 288881) B288881
theorem B290891 : Blo 191804 290891 := bstep (se 1 (by rfl) ⟨218168, by rfl⟩ : syracuseStep 290891 = 436337) B436337
theorem B192599 : Blo 191804 192599 := bstep (se 1 (by rfl) ⟨144449, by rfl⟩ : syracuseStep 192599 = 288899) B288899
theorem B290903 : Blo 191804 290903 := bstep (se 1 (by rfl) ⟨218177, by rfl⟩ : syracuseStep 290903 = 436355) B436355
theorem B192619 : Blo 191804 192619 := bstep (se 1 (by rfl) ⟨144464, by rfl⟩ : syracuseStep 192619 = 288929) B288929
theorem B192631 : Blo 191804 192631 := bstep (se 1 (by rfl) ⟨144473, by rfl⟩ : syracuseStep 192631 = 288947) B288947
theorem B1339523 : Blo 191804 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B323723 : Blo 191804 323723 := bstep (se 1 (by rfl) ⟨242792, by rfl⟩ : syracuseStep 323723 = 485585) B485585
theorem B192651 : Blo 191804 192651 := bstep (se 1 (by rfl) ⟨144488, by rfl⟩ : syracuseStep 192651 = 288977) B288977
theorem B192663 : Blo 191804 192663 := bstep (se 1 (by rfl) ⟨144497, by rfl⟩ : syracuseStep 192663 = 288995) B288995
theorem B290969 : Blo 191804 290969 := bstep (se 2 (by rfl) ⟨109113, by rfl⟩ : syracuseStep 290969 = 218227) B218227
theorem B192683 : Blo 191804 192683 := bstep (se 1 (by rfl) ⟨144512, by rfl⟩ : syracuseStep 192683 = 289025) B289025
theorem B192695 : Blo 191804 192695 := bstep (se 1 (by rfl) ⟨144521, by rfl⟩ : syracuseStep 192695 = 289043) B289043
theorem B192715 : Blo 191804 192715 := bstep (se 1 (by rfl) ⟨144536, by rfl⟩ : syracuseStep 192715 = 289073) B289073
theorem B192727 : Blo 191804 192727 := bstep (se 1 (by rfl) ⟨144545, by rfl⟩ : syracuseStep 192727 = 289091) B289091
theorem B192747 : Blo 191804 192747 := bstep (se 1 (by rfl) ⟨144560, by rfl⟩ : syracuseStep 192747 = 289121) B289121
theorem B192759 : Blo 191804 192759 := bstep (se 1 (by rfl) ⟨144569, by rfl⟩ : syracuseStep 192759 = 289139) B289139
theorem B323851 : Blo 191804 323851 := bstep (se 1 (by rfl) ⟨242888, by rfl⟩ : syracuseStep 323851 = 485777) B485777
theorem B192779 : Blo 191804 192779 := bstep (se 1 (by rfl) ⟨144584, by rfl⟩ : syracuseStep 192779 = 289169) B289169
theorem B291083 : Blo 191804 291083 := bstep (se 1 (by rfl) ⟨218312, by rfl⟩ : syracuseStep 291083 = 436625) B436625
theorem B192791 : Blo 191804 192791 := bstep (se 1 (by rfl) ⟨144593, by rfl⟩ : syracuseStep 192791 = 289187) B289187
theorem B291095 : Blo 191804 291095 := bstep (se 1 (by rfl) ⟨218321, by rfl⟩ : syracuseStep 291095 = 436643) B436643
theorem B192811 : Blo 191804 192811 := bstep (se 1 (by rfl) ⟨144608, by rfl⟩ : syracuseStep 192811 = 289217) B289217
theorem B192823 : Blo 191804 192823 := bstep (se 1 (by rfl) ⟨144617, by rfl⟩ : syracuseStep 192823 = 289235) B289235
theorem B192843 : Blo 191804 192843 := bstep (se 1 (by rfl) ⟨144632, by rfl⟩ : syracuseStep 192843 = 289265) B289265
theorem B192855 : Blo 191804 192855 := bstep (se 1 (by rfl) ⟨144641, by rfl⟩ : syracuseStep 192855 = 289283) B289283
theorem B291161 : Blo 191804 291161 := bstep (se 2 (by rfl) ⟨109185, by rfl⟩ : syracuseStep 291161 = 218371) B218371
theorem B192875 : Blo 191804 192875 := bstep (se 1 (by rfl) ⟨144656, by rfl⟩ : syracuseStep 192875 = 289313) B289313
theorem B192887 : Blo 191804 192887 := bstep (se 1 (by rfl) ⟨144665, by rfl⟩ : syracuseStep 192887 = 289331) B289331
theorem B192907 : Blo 191804 192907 := bstep (se 1 (by rfl) ⟨144680, by rfl⟩ : syracuseStep 192907 = 289361) B289361
theorem B192919 : Blo 191804 192919 := bstep (se 1 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 192919 = 289379) B289379
theorem B651671 : Blo 191804 651671 := bstep (se 1 (by rfl) ⟨488753, by rfl⟩ : syracuseStep 651671 = 977507) B977507
theorem B323993 : Blo 191804 323993 := bstep (se 2 (by rfl) ⟨121497, by rfl⟩ : syracuseStep 323993 = 242995) B242995
theorem B192939 : Blo 191804 192939 := bstep (se 1 (by rfl) ⟨144704, by rfl⟩ : syracuseStep 192939 = 289409) B289409
theorem B192951 : Blo 191804 192951 := bstep (se 1 (by rfl) ⟨144713, by rfl⟩ : syracuseStep 192951 = 289427) B289427
theorem B487883 : Blo 191804 487883 := bstep (se 1 (by rfl) ⟨365912, by rfl⟩ : syracuseStep 487883 = 731825) B731825
theorem B192971 : Blo 191804 192971 := bstep (se 1 (by rfl) ⟨144728, by rfl⟩ : syracuseStep 192971 = 289457) B289457
theorem B291275 : Blo 191804 291275 := bstep (se 1 (by rfl) ⟨218456, by rfl⟩ : syracuseStep 291275 = 436913) B436913
theorem B192983 : Blo 191804 192983 := bstep (se 1 (by rfl) ⟨144737, by rfl⟩ : syracuseStep 192983 = 289475) B289475
theorem B291287 : Blo 191804 291287 := bstep (se 1 (by rfl) ⟨218465, by rfl⟩ : syracuseStep 291287 = 436931) B436931
theorem B193003 : Blo 191804 193003 := bstep (se 1 (by rfl) ⟨144752, by rfl⟩ : syracuseStep 193003 = 289505) B289505
theorem B193015 : Blo 191804 193015 := bstep (se 1 (by rfl) ⟨144761, by rfl⟩ : syracuseStep 193015 = 289523) B289523
theorem B193035 : Blo 191804 193035 := bstep (se 1 (by rfl) ⟨144776, by rfl⟩ : syracuseStep 193035 = 289553) B289553
theorem B193047 : Blo 191804 193047 := bstep (se 1 (by rfl) ⟨144785, by rfl⟩ : syracuseStep 193047 = 289571) B289571
theorem B324121 : Blo 191804 324121 := bstep (se 2 (by rfl) ⟨121545, by rfl⟩ : syracuseStep 324121 = 243091) B243091
theorem B291353 : Blo 191804 291353 := bstep (se 2 (by rfl) ⟨109257, by rfl⟩ : syracuseStep 291353 = 218515) B218515
theorem B193067 : Blo 191804 193067 := bstep (se 1 (by rfl) ⟨144800, by rfl⟩ : syracuseStep 193067 = 289601) B289601
theorem B193079 : Blo 191804 193079 := bstep (se 1 (by rfl) ⟨144809, by rfl⟩ : syracuseStep 193079 = 289619) B289619
theorem B193099 : Blo 191804 193099 := bstep (se 1 (by rfl) ⟨144824, by rfl⟩ : syracuseStep 193099 = 289649) B289649
theorem B193111 : Blo 191804 193111 := bstep (se 1 (by rfl) ⟨144833, by rfl⟩ : syracuseStep 193111 = 289667) B289667
theorem B193131 : Blo 191804 193131 := bstep (se 1 (by rfl) ⟨144848, by rfl⟩ : syracuseStep 193131 = 289697) B289697
theorem B193143 : Blo 191804 193143 := bstep (se 1 (by rfl) ⟨144857, by rfl⟩ : syracuseStep 193143 = 289715) B289715
theorem B193163 : Blo 191804 193163 := bstep (se 1 (by rfl) ⟨144872, by rfl⟩ : syracuseStep 193163 = 289745) B289745
theorem B291467 : Blo 191804 291467 := bstep (se 1 (by rfl) ⟨218600, by rfl⟩ : syracuseStep 291467 = 437201) B437201
theorem B225931 : Blo 191804 225931 := bstep (se 1 (by rfl) ⟨169448, by rfl⟩ : syracuseStep 225931 = 338897) B338897
theorem B193175 : Blo 191804 193175 := bstep (se 1 (by rfl) ⟨144881, by rfl⟩ : syracuseStep 193175 = 289763) B289763
theorem B291479 : Blo 191804 291479 := bstep (se 1 (by rfl) ⟨218609, by rfl⟩ : syracuseStep 291479 = 437219) B437219
theorem B193195 : Blo 191804 193195 := bstep (se 1 (by rfl) ⟨144896, by rfl⟩ : syracuseStep 193195 = 289793) B289793
theorem B193207 : Blo 191804 193207 := bstep (se 1 (by rfl) ⟨144905, by rfl⟩ : syracuseStep 193207 = 289811) B289811
theorem B193227 : Blo 191804 193227 := bstep (se 1 (by rfl) ⟨144920, by rfl⟩ : syracuseStep 193227 = 289841) B289841
theorem B193239 : Blo 191804 193239 := bstep (se 1 (by rfl) ⟨144929, by rfl⟩ : syracuseStep 193239 = 289859) B289859
theorem B291545 : Blo 191804 291545 := bstep (se 2 (by rfl) ⟨109329, by rfl⟩ : syracuseStep 291545 = 218659) B218659
theorem B193259 : Blo 191804 193259 := bstep (se 1 (by rfl) ⟨144944, by rfl⟩ : syracuseStep 193259 = 289889) B289889
theorem B193271 : Blo 191804 193271 := bstep (se 1 (by rfl) ⟨144953, by rfl⟩ : syracuseStep 193271 = 289907) B289907
theorem B193291 : Blo 191804 193291 := bstep (se 1 (by rfl) ⟨144968, by rfl⟩ : syracuseStep 193291 = 289937) B289937
theorem B193303 : Blo 191804 193303 := bstep (se 1 (by rfl) ⟨144977, by rfl⟩ : syracuseStep 193303 = 289955) B289955
theorem B193323 : Blo 191804 193323 := bstep (se 1 (by rfl) ⟨144992, by rfl⟩ : syracuseStep 193323 = 289985) B289985
theorem B193335 : Blo 191804 193335 := bstep (se 1 (by rfl) ⟨145001, by rfl⟩ : syracuseStep 193335 = 290003) B290003
theorem B193355 : Blo 191804 193355 := bstep (se 1 (by rfl) ⟨145016, by rfl⟩ : syracuseStep 193355 = 290033) B290033
theorem B291659 : Blo 191804 291659 := bstep (se 1 (by rfl) ⟨218744, by rfl⟩ : syracuseStep 291659 = 437489) B437489
theorem B193367 : Blo 191804 193367 := bstep (se 1 (by rfl) ⟨145025, by rfl⟩ : syracuseStep 193367 = 290051) B290051
theorem B291671 : Blo 191804 291671 := bstep (se 1 (by rfl) ⟨218753, by rfl⟩ : syracuseStep 291671 = 437507) B437507
theorem B193387 : Blo 191804 193387 := bstep (se 1 (by rfl) ⟨145040, by rfl⟩ : syracuseStep 193387 = 290081) B290081
theorem B193399 : Blo 191804 193399 := bstep (se 1 (by rfl) ⟨145049, by rfl⟩ : syracuseStep 193399 = 290099) B290099
theorem B193419 : Blo 191804 193419 := bstep (se 1 (by rfl) ⟨145064, by rfl⟩ : syracuseStep 193419 = 290129) B290129
theorem B193431 : Blo 191804 193431 := bstep (se 1 (by rfl) ⟨145073, by rfl⟩ : syracuseStep 193431 = 290147) B290147
theorem B291737 : Blo 191804 291737 := bstep (se 2 (by rfl) ⟨109401, by rfl⟩ : syracuseStep 291737 = 218803) B218803
theorem B193451 : Blo 191804 193451 := bstep (se 1 (by rfl) ⟨145088, by rfl⟩ : syracuseStep 193451 = 290177) B290177
theorem B652211 : Blo 191804 652211 := bstep (se 1 (by rfl) ⟨489158, by rfl⟩ : syracuseStep 652211 = 978317) B978317
theorem B193463 : Blo 191804 193463 := bstep (se 1 (by rfl) ⟨145097, by rfl⟩ : syracuseStep 193463 = 290195) B290195
theorem B193483 : Blo 191804 193483 := bstep (se 1 (by rfl) ⟨145112, by rfl⟩ : syracuseStep 193483 = 290225) B290225
theorem B193495 : Blo 191804 193495 := bstep (se 1 (by rfl) ⟨145121, by rfl⟩ : syracuseStep 193495 = 290243) B290243
theorem B553949 : Blo 191804 553949 := bstep (se 3 (by rfl) ⟨103865, by rfl⟩ : syracuseStep 553949 = 207731) B207731
theorem B193515 : Blo 191804 193515 := bstep (se 1 (by rfl) ⟨145136, by rfl⟩ : syracuseStep 193515 = 290273) B290273
theorem B193527 : Blo 191804 193527 := bstep (se 1 (by rfl) ⟨145145, by rfl⟩ : syracuseStep 193527 = 290291) B290291
theorem B193547 : Blo 191804 193547 := bstep (se 1 (by rfl) ⟨145160, by rfl⟩ : syracuseStep 193547 = 290321) B290321
theorem B291851 : Blo 191804 291851 := bstep (se 1 (by rfl) ⟨218888, by rfl⟩ : syracuseStep 291851 = 437777) B437777
theorem B193559 : Blo 191804 193559 := bstep (se 1 (by rfl) ⟨145169, by rfl⟩ : syracuseStep 193559 = 290339) B290339
theorem B291863 : Blo 191804 291863 := bstep (se 1 (by rfl) ⟨218897, by rfl⟩ : syracuseStep 291863 = 437795) B437795
theorem B193579 : Blo 191804 193579 := bstep (se 1 (by rfl) ⟨145184, by rfl⟩ : syracuseStep 193579 = 290369) B290369
theorem B193591 : Blo 191804 193591 := bstep (se 1 (by rfl) ⟨145193, by rfl⟩ : syracuseStep 193591 = 290387) B290387
theorem B193611 : Blo 191804 193611 := bstep (se 1 (by rfl) ⟨145208, by rfl⟩ : syracuseStep 193611 = 290417) B290417
theorem B324695 : Blo 191804 324695 := bstep (se 1 (by rfl) ⟨243521, by rfl⟩ : syracuseStep 324695 = 487043) B487043
theorem B193623 : Blo 191804 193623 := bstep (se 1 (by rfl) ⟨145217, by rfl⟩ : syracuseStep 193623 = 290435) B290435
theorem B291929 : Blo 191804 291929 := bstep (se 2 (by rfl) ⟨109473, by rfl⟩ : syracuseStep 291929 = 218947) B218947
theorem B193643 : Blo 191804 193643 := bstep (se 1 (by rfl) ⟨145232, by rfl⟩ : syracuseStep 193643 = 290465) B290465
theorem B193655 : Blo 191804 193655 := bstep (se 1 (by rfl) ⟨145241, by rfl⟩ : syracuseStep 193655 = 290483) B290483
theorem B980099 : Blo 191804 980099 := bstep (se 1 (by rfl) ⟨735074, by rfl⟩ : syracuseStep 980099 = 1470149) B1470149
theorem B193675 : Blo 191804 193675 := bstep (se 1 (by rfl) ⟨145256, by rfl⟩ : syracuseStep 193675 = 290513) B290513
theorem B193687 : Blo 191804 193687 := bstep (se 1 (by rfl) ⟨145265, by rfl⟩ : syracuseStep 193687 = 290531) B290531
theorem B193707 : Blo 191804 193707 := bstep (se 1 (by rfl) ⟨145280, by rfl⟩ : syracuseStep 193707 = 290561) B290561
theorem B193719 : Blo 191804 193719 := bstep (se 1 (by rfl) ⟨145289, by rfl⟩ : syracuseStep 193719 = 290579) B290579
theorem B652481 : Blo 191804 652481 := bstep (se 2 (by rfl) ⟨244680, by rfl⟩ : syracuseStep 652481 = 489361) B489361
theorem B554177 : Blo 191804 554177 := bstep (se 2 (by rfl) ⟨207816, by rfl⟩ : syracuseStep 554177 = 415633) B415633
theorem B193739 : Blo 191804 193739 := bstep (se 1 (by rfl) ⟨145304, by rfl⟩ : syracuseStep 193739 = 290609) B290609
theorem B292043 : Blo 191804 292043 := bstep (se 1 (by rfl) ⟨219032, by rfl⟩ : syracuseStep 292043 = 438065) B438065
theorem B324823 : Blo 191804 324823 := bstep (se 1 (by rfl) ⟨243617, by rfl⟩ : syracuseStep 324823 = 487235) B487235
theorem B193751 : Blo 191804 193751 := bstep (se 1 (by rfl) ⟨145313, by rfl⟩ : syracuseStep 193751 = 290627) B290627
theorem B292055 : Blo 191804 292055 := bstep (se 1 (by rfl) ⟨219041, by rfl⟩ : syracuseStep 292055 = 438083) B438083
theorem B586973 : Blo 191804 586973 := bstep (se 3 (by rfl) ⟨110057, by rfl⟩ : syracuseStep 586973 = 220115) B220115
theorem B193771 : Blo 191804 193771 := bstep (se 1 (by rfl) ⟨145328, by rfl⟩ : syracuseStep 193771 = 290657) B290657
theorem B193783 : Blo 191804 193783 := bstep (se 1 (by rfl) ⟨145337, by rfl⟩ : syracuseStep 193783 = 290675) B290675
theorem B193803 : Blo 191804 193803 := bstep (se 1 (by rfl) ⟨145352, by rfl⟩ : syracuseStep 193803 = 290705) B290705
theorem B521495 : Blo 191804 521495 := bstep (se 1 (by rfl) ⟨391121, by rfl⟩ : syracuseStep 521495 = 782243) B782243
theorem B193815 : Blo 191804 193815 := bstep (se 1 (by rfl) ⟨145361, by rfl⟩ : syracuseStep 193815 = 290723) B290723
theorem B390425 : Blo 191804 390425 := bstep (se 2 (by rfl) ⟨146409, by rfl⟩ : syracuseStep 390425 = 292819) B292819
theorem B292121 : Blo 191804 292121 := bstep (se 2 (by rfl) ⟨109545, by rfl⟩ : syracuseStep 292121 = 219091) B219091
theorem B193835 : Blo 191804 193835 := bstep (se 1 (by rfl) ⟨145376, by rfl⟩ : syracuseStep 193835 = 290753) B290753
theorem B193847 : Blo 191804 193847 := bstep (se 1 (by rfl) ⟨145385, by rfl⟩ : syracuseStep 193847 = 290771) B290771
theorem B193867 : Blo 191804 193867 := bstep (se 1 (by rfl) ⟨145400, by rfl⟩ : syracuseStep 193867 = 290801) B290801
theorem B193879 : Blo 191804 193879 := bstep (se 1 (by rfl) ⟨145409, by rfl⟩ : syracuseStep 193879 = 290819) B290819
theorem B193899 : Blo 191804 193899 := bstep (se 1 (by rfl) ⟨145424, by rfl⟩ : syracuseStep 193899 = 290849) B290849
theorem B193911 : Blo 191804 193911 := bstep (se 1 (by rfl) ⟨145433, by rfl⟩ : syracuseStep 193911 = 290867) B290867
theorem B193931 : Blo 191804 193931 := bstep (se 1 (by rfl) ⟨145448, by rfl⟩ : syracuseStep 193931 = 290897) B290897
theorem B292235 : Blo 191804 292235 := bstep (se 1 (by rfl) ⟨219176, by rfl⟩ : syracuseStep 292235 = 438353) B438353
theorem B292247 : Blo 191804 292247 := bstep (se 1 (by rfl) ⟨219185, by rfl⟩ : syracuseStep 292247 = 438371) B438371
theorem B488855 : Blo 191804 488855 := bstep (se 1 (by rfl) ⟨366641, by rfl⟩ : syracuseStep 488855 = 733283) B733283
theorem B193943 : Blo 191804 193943 := bstep (se 1 (by rfl) ⟨145457, by rfl⟩ : syracuseStep 193943 = 290915) B290915
theorem B193963 : Blo 191804 193963 := bstep (se 1 (by rfl) ⟨145472, by rfl⟩ : syracuseStep 193963 = 290945) B290945
theorem B193975 : Blo 191804 193975 := bstep (se 1 (by rfl) ⟨145481, by rfl⟩ : syracuseStep 193975 = 290963) B290963
theorem B193995 : Blo 191804 193995 := bstep (se 1 (by rfl) ⟨145496, by rfl⟩ : syracuseStep 193995 = 290993) B290993
theorem B194007 : Blo 191804 194007 := bstep (se 1 (by rfl) ⟨145505, by rfl⟩ : syracuseStep 194007 = 291011) B291011
theorem B292313 : Blo 191804 292313 := bstep (se 2 (by rfl) ⟨109617, by rfl⟩ : syracuseStep 292313 = 219235) B219235
theorem B194027 : Blo 191804 194027 := bstep (se 1 (by rfl) ⟨145520, by rfl⟩ : syracuseStep 194027 = 291041) B291041
theorem B194039 : Blo 191804 194039 := bstep (se 1 (by rfl) ⟨145529, by rfl⟩ : syracuseStep 194039 = 291059) B291059
theorem B194059 : Blo 191804 194059 := bstep (se 1 (by rfl) ⟨145544, by rfl⟩ : syracuseStep 194059 = 291089) B291089
theorem B194071 : Blo 191804 194071 := bstep (se 1 (by rfl) ⟨145553, by rfl⟩ : syracuseStep 194071 = 291107) B291107
theorem B554519 : Blo 191804 554519 := bstep (se 1 (by rfl) ⟨415889, by rfl⟩ : syracuseStep 554519 = 831779) B831779
theorem B194091 : Blo 191804 194091 := bstep (se 1 (by rfl) ⟨145568, by rfl⟩ : syracuseStep 194091 = 291137) B291137
theorem B194103 : Blo 191804 194103 := bstep (se 1 (by rfl) ⟨145577, by rfl⟩ : syracuseStep 194103 = 291155) B291155
theorem B194123 : Blo 191804 194123 := bstep (se 1 (by rfl) ⟨145592, by rfl⟩ : syracuseStep 194123 = 291185) B291185
theorem B292427 : Blo 191804 292427 := bstep (se 1 (by rfl) ⟨219320, by rfl⟩ : syracuseStep 292427 = 438641) B438641
theorem B194135 : Blo 191804 194135 := bstep (se 1 (by rfl) ⟨145601, by rfl⟩ : syracuseStep 194135 = 291203) B291203
theorem B292439 : Blo 191804 292439 := bstep (se 1 (by rfl) ⟨219329, by rfl⟩ : syracuseStep 292439 = 438659) B438659
theorem B1472093 : Blo 191804 1472093 := bstep (se 3 (by rfl) ⟨276017, by rfl⟩ : syracuseStep 1472093 = 552035) B552035
theorem B194155 : Blo 191804 194155 := bstep (se 1 (by rfl) ⟨145616, by rfl⟩ : syracuseStep 194155 = 291233) B291233
theorem B194167 : Blo 191804 194167 := bstep (se 1 (by rfl) ⟨145625, by rfl⟩ : syracuseStep 194167 = 291251) B291251
theorem B194187 : Blo 191804 194187 := bstep (se 1 (by rfl) ⟨145640, by rfl⟩ : syracuseStep 194187 = 291281) B291281
theorem B194199 : Blo 191804 194199 := bstep (se 1 (by rfl) ⟨145649, by rfl⟩ : syracuseStep 194199 = 291299) B291299
theorem B292505 : Blo 191804 292505 := bstep (se 2 (by rfl) ⟨109689, by rfl⟩ : syracuseStep 292505 = 219379) B219379
theorem B194219 : Blo 191804 194219 := bstep (se 1 (by rfl) ⟨145664, by rfl⟩ : syracuseStep 194219 = 291329) B291329
theorem B194231 : Blo 191804 194231 := bstep (se 1 (by rfl) ⟨145673, by rfl⟩ : syracuseStep 194231 = 291347) B291347
theorem B194251 : Blo 191804 194251 := bstep (se 1 (by rfl) ⟨145688, by rfl⟩ : syracuseStep 194251 = 291377) B291377
theorem B194263 : Blo 191804 194263 := bstep (se 1 (by rfl) ⟨145697, by rfl⟩ : syracuseStep 194263 = 291395) B291395
theorem B653021 : Blo 191804 653021 := bstep (se 3 (by rfl) ⟨122441, by rfl⟩ : syracuseStep 653021 = 244883) B244883
theorem B194283 : Blo 191804 194283 := bstep (se 1 (by rfl) ⟨145712, by rfl⟩ : syracuseStep 194283 = 291425) B291425
theorem B194295 : Blo 191804 194295 := bstep (se 1 (by rfl) ⟨145721, by rfl⟩ : syracuseStep 194295 = 291443) B291443
theorem B194315 : Blo 191804 194315 := bstep (se 1 (by rfl) ⟨145736, by rfl⟩ : syracuseStep 194315 = 291473) B291473
theorem B292619 : Blo 191804 292619 := bstep (se 1 (by rfl) ⟨219464, by rfl⟩ : syracuseStep 292619 = 438929) B438929
theorem B620311 : Blo 191804 620311 := bstep (se 1 (by rfl) ⟨465233, by rfl⟩ : syracuseStep 620311 = 930467) B930467
theorem B194327 : Blo 191804 194327 := bstep (se 1 (by rfl) ⟨145745, by rfl⟩ : syracuseStep 194327 = 291491) B291491
theorem B292631 : Blo 191804 292631 := bstep (se 1 (by rfl) ⟨219473, by rfl⟩ : syracuseStep 292631 = 438947) B438947
theorem B194347 : Blo 191804 194347 := bstep (se 1 (by rfl) ⟨145760, by rfl⟩ : syracuseStep 194347 = 291521) B291521
theorem B194359 : Blo 191804 194359 := bstep (se 1 (by rfl) ⟨145769, by rfl⟩ : syracuseStep 194359 = 291539) B291539
theorem B325451 : Blo 191804 325451 := bstep (se 1 (by rfl) ⟨244088, by rfl⟩ : syracuseStep 325451 = 488177) B488177
theorem B194379 : Blo 191804 194379 := bstep (se 1 (by rfl) ⟨145784, by rfl⟩ : syracuseStep 194379 = 291569) B291569
theorem B194391 : Blo 191804 194391 := bstep (se 1 (by rfl) ⟨145793, by rfl⟩ : syracuseStep 194391 = 291587) B291587
theorem B292697 : Blo 191804 292697 := bstep (se 2 (by rfl) ⟨109761, by rfl⟩ : syracuseStep 292697 = 219523) B219523
theorem B194411 : Blo 191804 194411 := bstep (se 1 (by rfl) ⟨145808, by rfl⟩ : syracuseStep 194411 = 291617) B291617
theorem B194423 : Blo 191804 194423 := bstep (se 1 (by rfl) ⟨145817, by rfl⟩ : syracuseStep 194423 = 291635) B291635
theorem B194443 : Blo 191804 194443 := bstep (se 1 (by rfl) ⟨145832, by rfl⟩ : syracuseStep 194443 = 291665) B291665
theorem B1570711 : Blo 191804 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B194455 : Blo 191804 194455 := bstep (se 1 (by rfl) ⟨145841, by rfl⟩ : syracuseStep 194455 = 291683) B291683
theorem B194475 : Blo 191804 194475 := bstep (se 1 (by rfl) ⟨145856, by rfl⟩ : syracuseStep 194475 = 291713) B291713
theorem B194487 : Blo 191804 194487 := bstep (se 1 (by rfl) ⟨145865, by rfl⟩ : syracuseStep 194487 = 291731) B291731
theorem B325579 : Blo 191804 325579 := bstep (se 1 (by rfl) ⟨244184, by rfl⟩ : syracuseStep 325579 = 488369) B488369
theorem B194507 : Blo 191804 194507 := bstep (se 1 (by rfl) ⟨145880, by rfl⟩ : syracuseStep 194507 = 291761) B291761
theorem B292811 : Blo 191804 292811 := bstep (se 1 (by rfl) ⟨219608, by rfl⟩ : syracuseStep 292811 = 439217) B439217
theorem B194519 : Blo 191804 194519 := bstep (se 1 (by rfl) ⟨145889, by rfl⟩ : syracuseStep 194519 = 291779) B291779
theorem B292823 : Blo 191804 292823 := bstep (se 1 (by rfl) ⟨219617, by rfl⟩ : syracuseStep 292823 = 439235) B439235
theorem B194539 : Blo 191804 194539 := bstep (se 1 (by rfl) ⟨145904, by rfl⟩ : syracuseStep 194539 = 291809) B291809
theorem B194551 : Blo 191804 194551 := bstep (se 1 (by rfl) ⟨145913, by rfl⟩ : syracuseStep 194551 = 291827) B291827
theorem B194571 : Blo 191804 194571 := bstep (se 1 (by rfl) ⟨145928, by rfl⟩ : syracuseStep 194571 = 291857) B291857
theorem B555031 : Blo 191804 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B194583 : Blo 191804 194583 := bstep (se 1 (by rfl) ⟨145937, by rfl⟩ : syracuseStep 194583 = 291875) B291875
theorem B292889 : Blo 191804 292889 := bstep (se 2 (by rfl) ⟨109833, by rfl⟩ : syracuseStep 292889 = 219667) B219667
theorem B194603 : Blo 191804 194603 := bstep (se 1 (by rfl) ⟨145952, by rfl⟩ : syracuseStep 194603 = 291905) B291905
theorem B489523 : Blo 191804 489523 := bstep (se 1 (by rfl) ⟨367142, by rfl⟩ : syracuseStep 489523 = 734285) B734285
theorem B194615 : Blo 191804 194615 := bstep (se 1 (by rfl) ⟨145961, by rfl⟩ : syracuseStep 194615 = 291923) B291923
theorem B194635 : Blo 191804 194635 := bstep (se 1 (by rfl) ⟨145976, by rfl⟩ : syracuseStep 194635 = 291953) B291953
theorem B194647 : Blo 191804 194647 := bstep (se 1 (by rfl) ⟨145985, by rfl⟩ : syracuseStep 194647 = 291971) B291971
theorem B325721 : Blo 191804 325721 := bstep (se 2 (by rfl) ⟨122145, by rfl⟩ : syracuseStep 325721 = 244291) B244291
theorem B194667 : Blo 191804 194667 := bstep (se 1 (by rfl) ⟨146000, by rfl⟩ : syracuseStep 194667 = 292001) B292001
theorem B194679 : Blo 191804 194679 := bstep (se 1 (by rfl) ⟨146009, by rfl⟩ : syracuseStep 194679 = 292019) B292019
theorem B194699 : Blo 191804 194699 := bstep (se 1 (by rfl) ⟨146024, by rfl⟩ : syracuseStep 194699 = 292049) B292049
theorem B293003 : Blo 191804 293003 := bstep (se 1 (by rfl) ⟨219752, by rfl⟩ : syracuseStep 293003 = 439505) B439505
theorem B194711 : Blo 191804 194711 := bstep (se 1 (by rfl) ⟨146033, by rfl⟩ : syracuseStep 194711 = 292067) B292067
theorem B293015 : Blo 191804 293015 := bstep (se 1 (by rfl) ⟨219761, by rfl⟩ : syracuseStep 293015 = 439523) B439523
theorem B194731 : Blo 191804 194731 := bstep (se 1 (by rfl) ⟨146048, by rfl⟩ : syracuseStep 194731 = 292097) B292097
theorem B194743 : Blo 191804 194743 := bstep (se 1 (by rfl) ⟨146057, by rfl⟩ : syracuseStep 194743 = 292115) B292115
theorem B489665 : Blo 191804 489665 := bstep (se 2 (by rfl) ⟨183624, by rfl⟩ : syracuseStep 489665 = 367249) B367249
theorem B194763 : Blo 191804 194763 := bstep (se 1 (by rfl) ⟨146072, by rfl⟩ : syracuseStep 194763 = 292145) B292145
theorem B194775 : Blo 191804 194775 := bstep (se 1 (by rfl) ⟨146081, by rfl⟩ : syracuseStep 194775 = 292163) B292163
theorem B325849 : Blo 191804 325849 := bstep (se 2 (by rfl) ⟨122193, by rfl⟩ : syracuseStep 325849 = 244387) B244387
theorem B293081 : Blo 191804 293081 := bstep (se 2 (by rfl) ⟨109905, by rfl⟩ : syracuseStep 293081 = 219811) B219811
theorem B194795 : Blo 191804 194795 := bstep (se 1 (by rfl) ⟨146096, by rfl⟩ : syracuseStep 194795 = 292193) B292193
theorem B194807 : Blo 191804 194807 := bstep (se 1 (by rfl) ⟨146105, by rfl⟩ : syracuseStep 194807 = 292211) B292211
theorem B194827 : Blo 191804 194827 := bstep (se 1 (by rfl) ⟨146120, by rfl⟩ : syracuseStep 194827 = 292241) B292241
theorem B194839 : Blo 191804 194839 := bstep (se 1 (by rfl) ⟨146129, by rfl⟩ : syracuseStep 194839 = 292259) B292259
theorem B194859 : Blo 191804 194859 := bstep (se 1 (by rfl) ⟨146144, by rfl⟩ : syracuseStep 194859 = 292289) B292289
theorem B194871 : Blo 191804 194871 := bstep (se 1 (by rfl) ⟨146153, by rfl⟩ : syracuseStep 194871 = 292307) B292307
theorem B194891 : Blo 191804 194891 := bstep (se 1 (by rfl) ⟨146168, by rfl⟩ : syracuseStep 194891 = 292337) B292337
theorem B293195 : Blo 191804 293195 := bstep (se 1 (by rfl) ⟨219896, by rfl⟩ : syracuseStep 293195 = 439793) B439793
theorem B194903 : Blo 191804 194903 := bstep (se 1 (by rfl) ⟨146177, by rfl⟩ : syracuseStep 194903 = 292355) B292355
theorem B293207 : Blo 191804 293207 := bstep (se 1 (by rfl) ⟨219905, by rfl⟩ : syracuseStep 293207 = 439811) B439811
theorem B194923 : Blo 191804 194923 := bstep (se 1 (by rfl) ⟨146192, by rfl⟩ : syracuseStep 194923 = 292385) B292385
theorem B194935 : Blo 191804 194935 := bstep (se 1 (by rfl) ⟨146201, by rfl⟩ : syracuseStep 194935 = 292403) B292403
theorem B194955 : Blo 191804 194955 := bstep (se 1 (by rfl) ⟨146216, by rfl⟩ : syracuseStep 194955 = 292433) B292433
theorem B194967 : Blo 191804 194967 := bstep (se 1 (by rfl) ⟨146225, by rfl⟩ : syracuseStep 194967 = 292451) B292451
theorem B293273 : Blo 191804 293273 := bstep (se 2 (by rfl) ⟨109977, by rfl⟩ : syracuseStep 293273 = 219955) B219955
theorem B194987 : Blo 191804 194987 := bstep (se 1 (by rfl) ⟨146240, by rfl⟩ : syracuseStep 194987 = 292481) B292481
theorem B194999 : Blo 191804 194999 := bstep (se 1 (by rfl) ⟨146249, by rfl⟩ : syracuseStep 194999 = 292499) B292499
theorem B195019 : Blo 191804 195019 := bstep (se 1 (by rfl) ⟨146264, by rfl⟩ : syracuseStep 195019 = 292529) B292529
theorem B195031 : Blo 191804 195031 := bstep (se 1 (by rfl) ⟨146273, by rfl⟩ : syracuseStep 195031 = 292547) B292547
theorem B195051 : Blo 191804 195051 := bstep (se 1 (by rfl) ⟨146288, by rfl⟩ : syracuseStep 195051 = 292577) B292577
theorem B195063 : Blo 191804 195063 := bstep (se 1 (by rfl) ⟨146297, by rfl⟩ : syracuseStep 195063 = 292595) B292595
theorem B195083 : Blo 191804 195083 := bstep (se 1 (by rfl) ⟨146312, by rfl⟩ : syracuseStep 195083 = 292625) B292625
theorem B293387 : Blo 191804 293387 := bstep (se 1 (by rfl) ⟨220040, by rfl⟩ : syracuseStep 293387 = 440081) B440081
theorem B195095 : Blo 191804 195095 := bstep (se 1 (by rfl) ⟨146321, by rfl⟩ : syracuseStep 195095 = 292643) B292643
theorem B293399 : Blo 191804 293399 := bstep (se 1 (by rfl) ⟨220049, by rfl⟩ : syracuseStep 293399 = 440099) B440099
theorem B195115 : Blo 191804 195115 := bstep (se 1 (by rfl) ⟨146336, by rfl⟩ : syracuseStep 195115 = 292673) B292673
theorem B195127 : Blo 191804 195127 := bstep (se 1 (by rfl) ⟨146345, by rfl⟩ : syracuseStep 195127 = 292691) B292691
theorem B195147 : Blo 191804 195147 := bstep (se 1 (by rfl) ⟨146360, by rfl⟩ : syracuseStep 195147 = 292721) B292721
theorem B195159 : Blo 191804 195159 := bstep (se 1 (by rfl) ⟨146369, by rfl⟩ : syracuseStep 195159 = 292739) B292739
theorem B293465 : Blo 191804 293465 := bstep (se 2 (by rfl) ⟨110049, by rfl⟩ : syracuseStep 293465 = 220099) B220099
theorem B195179 : Blo 191804 195179 := bstep (se 1 (by rfl) ⟨146384, by rfl⟩ : syracuseStep 195179 = 292769) B292769
theorem B195191 : Blo 191804 195191 := bstep (se 1 (by rfl) ⟨146393, by rfl⟩ : syracuseStep 195191 = 292787) B292787
theorem B195211 : Blo 191804 195211 := bstep (se 1 (by rfl) ⟨146408, by rfl⟩ : syracuseStep 195211 = 292817) B292817
theorem B195223 : Blo 191804 195223 := bstep (se 1 (by rfl) ⟨146417, by rfl⟩ : syracuseStep 195223 = 292835) B292835
theorem B195243 : Blo 191804 195243 := bstep (se 1 (by rfl) ⟨146432, by rfl⟩ : syracuseStep 195243 = 292865) B292865
theorem B195255 : Blo 191804 195255 := bstep (se 1 (by rfl) ⟨146441, by rfl⟩ : syracuseStep 195255 = 292883) B292883
theorem B195275 : Blo 191804 195275 := bstep (se 1 (by rfl) ⟨146456, by rfl⟩ : syracuseStep 195275 = 292913) B292913
theorem B293579 : Blo 191804 293579 := bstep (se 1 (by rfl) ⟨220184, by rfl⟩ : syracuseStep 293579 = 440369) B440369
theorem B195287 : Blo 191804 195287 := bstep (se 1 (by rfl) ⟨146465, by rfl⟩ : syracuseStep 195287 = 292931) B292931
theorem B293591 : Blo 191804 293591 := bstep (se 1 (by rfl) ⟨220193, by rfl⟩ : syracuseStep 293591 = 440387) B440387
theorem B195307 : Blo 191804 195307 := bstep (se 1 (by rfl) ⟨146480, by rfl⟩ : syracuseStep 195307 = 292961) B292961
theorem B195319 : Blo 191804 195319 := bstep (se 1 (by rfl) ⟨146489, by rfl⟩ : syracuseStep 195319 = 292979) B292979
theorem B195339 : Blo 191804 195339 := bstep (se 1 (by rfl) ⟨146504, by rfl⟩ : syracuseStep 195339 = 293009) B293009
theorem B326423 : Blo 191804 326423 := bstep (se 1 (by rfl) ⟨244817, by rfl⟩ : syracuseStep 326423 = 489635) B489635
theorem B195351 : Blo 191804 195351 := bstep (se 1 (by rfl) ⟨146513, by rfl⟩ : syracuseStep 195351 = 293027) B293027
theorem B293657 : Blo 191804 293657 := bstep (se 2 (by rfl) ⟨110121, by rfl⟩ : syracuseStep 293657 = 220243) B220243
theorem B195371 : Blo 191804 195371 := bstep (se 1 (by rfl) ⟨146528, by rfl⟩ : syracuseStep 195371 = 293057) B293057
theorem B195383 : Blo 191804 195383 := bstep (se 1 (by rfl) ⟨146537, by rfl⟩ : syracuseStep 195383 = 293075) B293075
theorem B654155 : Blo 191804 654155 := bstep (se 1 (by rfl) ⟨490616, by rfl⟩ : syracuseStep 654155 = 981233) B981233
theorem B195403 : Blo 191804 195403 := bstep (se 1 (by rfl) ⟨146552, by rfl⟩ : syracuseStep 195403 = 293105) B293105
theorem B195415 : Blo 191804 195415 := bstep (se 1 (by rfl) ⟨146561, by rfl⟩ : syracuseStep 195415 = 293123) B293123
theorem B195435 : Blo 191804 195435 := bstep (se 1 (by rfl) ⟨146576, by rfl⟩ : syracuseStep 195435 = 293153) B293153
theorem B195447 : Blo 191804 195447 := bstep (se 1 (by rfl) ⟨146585, by rfl⟩ : syracuseStep 195447 = 293171) B293171
theorem B195467 : Blo 191804 195467 := bstep (se 1 (by rfl) ⟨146600, by rfl⟩ : syracuseStep 195467 = 293201) B293201
theorem B326551 : Blo 191804 326551 := bstep (se 1 (by rfl) ⟨244913, by rfl⟩ : syracuseStep 326551 = 489827) B489827
theorem B195479 : Blo 191804 195479 := bstep (se 1 (by rfl) ⟨146609, by rfl⟩ : syracuseStep 195479 = 293219) B293219
theorem B195499 : Blo 191804 195499 := bstep (se 1 (by rfl) ⟨146624, by rfl⟩ : syracuseStep 195499 = 293249) B293249
theorem B195511 : Blo 191804 195511 := bstep (se 1 (by rfl) ⟨146633, by rfl⟩ : syracuseStep 195511 = 293267) B293267
theorem B195531 : Blo 191804 195531 := bstep (se 1 (by rfl) ⟨146648, by rfl⟩ : syracuseStep 195531 = 293297) B293297
theorem B195543 : Blo 191804 195543 := bstep (se 1 (by rfl) ⟨146657, by rfl⟩ : syracuseStep 195543 = 293315) B293315
theorem B195563 : Blo 191804 195563 := bstep (se 1 (by rfl) ⟨146672, by rfl⟩ : syracuseStep 195563 = 293345) B293345
theorem B195575 : Blo 191804 195575 := bstep (se 1 (by rfl) ⟨146681, by rfl⟩ : syracuseStep 195575 = 293363) B293363
theorem B195595 : Blo 191804 195595 := bstep (se 1 (by rfl) ⟨146696, by rfl⟩ : syracuseStep 195595 = 293393) B293393
theorem B195607 : Blo 191804 195607 := bstep (se 1 (by rfl) ⟨146705, by rfl⟩ : syracuseStep 195607 = 293411) B293411
theorem B195627 : Blo 191804 195627 := bstep (se 1 (by rfl) ⟨146720, by rfl⟩ : syracuseStep 195627 = 293441) B293441
theorem B1571885 : Blo 191804 1571885 := bstep (se 3 (by rfl) ⟨294728, by rfl⟩ : syracuseStep 1571885 = 589457) B589457
theorem B195639 : Blo 191804 195639 := bstep (se 1 (by rfl) ⟨146729, by rfl⟩ : syracuseStep 195639 = 293459) B293459
theorem B195659 : Blo 191804 195659 := bstep (se 1 (by rfl) ⟨146744, by rfl⟩ : syracuseStep 195659 = 293489) B293489
theorem B195671 : Blo 191804 195671 := bstep (se 1 (by rfl) ⟨146753, by rfl⟩ : syracuseStep 195671 = 293507) B293507
theorem B654425 : Blo 191804 654425 := bstep (se 2 (by rfl) ⟨245409, by rfl⟩ : syracuseStep 654425 = 490819) B490819
theorem B195691 : Blo 191804 195691 := bstep (se 1 (by rfl) ⟨146768, by rfl⟩ : syracuseStep 195691 = 293537) B293537
theorem B195703 : Blo 191804 195703 := bstep (se 1 (by rfl) ⟨146777, by rfl⟩ : syracuseStep 195703 = 293555) B293555
theorem B195723 : Blo 191804 195723 := bstep (se 1 (by rfl) ⟨146792, by rfl⟩ : syracuseStep 195723 = 293585) B293585
theorem B195735 : Blo 191804 195735 := bstep (se 1 (by rfl) ⟨146801, by rfl⟩ : syracuseStep 195735 = 293603) B293603
theorem B195755 : Blo 191804 195755 := bstep (se 1 (by rfl) ⟨146816, by rfl⟩ : syracuseStep 195755 = 293633) B293633
theorem B1670321 : Blo 191804 1670321 := bstep (se 2 (by rfl) ⟨626370, by rfl⟩ : syracuseStep 1670321 = 1252741) B1252741
theorem B195767 : Blo 191804 195767 := bstep (se 1 (by rfl) ⟨146825, by rfl⟩ : syracuseStep 195767 = 293651) B293651
theorem B195787 : Blo 191804 195787 := bstep (se 1 (by rfl) ⟨146840, by rfl⟩ : syracuseStep 195787 = 293681) B293681
theorem B195799 : Blo 191804 195799 := bstep (se 1 (by rfl) ⟨146849, by rfl⟩ : syracuseStep 195799 = 293699) B293699
theorem B490931 : Blo 191804 490931 := bstep (se 1 (by rfl) ⟨368198, by rfl⟩ : syracuseStep 490931 = 736397) B736397
theorem B327179 : Blo 191804 327179 := bstep (se 1 (by rfl) ⟨245384, by rfl⟩ : syracuseStep 327179 = 490769) B490769
theorem B261721 : Blo 191804 261721 := bstep (se 2 (by rfl) ⟨98145, by rfl⟩ : syracuseStep 261721 = 196291) B196291
theorem B327307 : Blo 191804 327307 := bstep (se 1 (by rfl) ⟨245480, by rfl⟩ : syracuseStep 327307 = 490961) B490961
theorem B655127 : Blo 191804 655127 := bstep (se 1 (by rfl) ⟨491345, by rfl⟩ : syracuseStep 655127 = 982691) B982691
theorem B327449 : Blo 191804 327449 := bstep (se 2 (by rfl) ⟨122793, by rfl⟩ : syracuseStep 327449 = 245587) B245587
theorem B556865 : Blo 191804 556865 := bstep (se 2 (by rfl) ⟨208824, by rfl⟩ : syracuseStep 556865 = 417649) B417649
theorem B3735395 : Blo 191804 3735395 := bstep (se 1 (by rfl) ⟨2801546, by rfl⟩ : syracuseStep 3735395 = 5603093) B5603093
theorem B327577 : Blo 191804 327577 := bstep (se 2 (by rfl) ⟨122841, by rfl⟩ : syracuseStep 327577 = 245683) B245683
theorem B1572787 : Blo 191804 1572787 := bstep (se 1 (by rfl) ⟨1179590, by rfl⟩ : syracuseStep 1572787 = 2359181) B2359181
theorem B491467 : Blo 191804 491467 := bstep (se 1 (by rfl) ⟨368600, by rfl⟩ : syracuseStep 491467 = 737201) B737201
theorem B1114073 : Blo 191804 1114073 := bstep (se 2 (by rfl) ⟨417777, by rfl⟩ : syracuseStep 1114073 = 835555) B835555
theorem B491579 : Blo 191804 491579 := bstep (se 1 (by rfl) ⟨368684, by rfl⟩ : syracuseStep 491579 = 737369) B737369
theorem B327739 : Blo 191804 327739 := bstep (se 1 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 327739 = 491609) B491609
theorem B327881 : Blo 191804 327881 := bstep (se 2 (by rfl) ⟨122955, by rfl⟩ : syracuseStep 327881 = 245911) B245911
theorem B491791 : Blo 191804 491791 := bstep (se 1 (by rfl) ⟨368843, by rfl⟩ : syracuseStep 491791 = 737687) B737687
theorem B262543 : Blo 191804 262543 := bstep (se 1 (by rfl) ⟨196907, by rfl⟩ : syracuseStep 262543 = 393815) B393815
theorem B655883 : Blo 191804 655883 := bstep (se 1 (by rfl) ⟨491912, by rfl⟩ : syracuseStep 655883 = 983825) B983825
theorem B492065 : Blo 191804 492065 := bstep (se 2 (by rfl) ⟨184524, by rfl⟩ : syracuseStep 492065 = 369049) B369049
theorem B655991 : Blo 191804 655991 := bstep (se 1 (by rfl) ⟨491993, by rfl⟩ : syracuseStep 655991 = 983987) B983987
theorem B328583 : Blo 191804 328583 := bstep (se 1 (by rfl) ⟨246437, by rfl⟩ : syracuseStep 328583 = 492875) B492875
theorem B656585 : Blo 191804 656585 := bstep (se 2 (by rfl) ⟨246219, by rfl⟩ : syracuseStep 656585 = 492439) B492439
theorem B296207 : Blo 191804 296207 := bstep (se 1 (by rfl) ⟨222155, by rfl⟩ : syracuseStep 296207 = 444311) B444311
theorem B230699 : Blo 191804 230699 := bstep (se 1 (by rfl) ⟨173024, by rfl⟩ : syracuseStep 230699 = 346049) B346049
theorem B984473 : Blo 191804 984473 := bstep (se 2 (by rfl) ⟨369177, by rfl⟩ : syracuseStep 984473 = 738355) B738355
theorem B951755 : Blo 191804 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B493067 : Blo 191804 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B329231 : Blo 191804 329231 := bstep (se 1 (by rfl) ⟨246923, by rfl⟩ : syracuseStep 329231 = 493847) B493847
theorem B198415 : Blo 191804 198415 := bstep (se 1 (by rfl) ⟨148811, by rfl⟩ : syracuseStep 198415 = 297623) B297623
theorem B1476467 : Blo 191804 1476467 := bstep (se 1 (by rfl) ⟨1107350, by rfl⟩ : syracuseStep 1476467 = 2214701) B2214701
theorem B657287 : Blo 191804 657287 := bstep (se 1 (by rfl) ⟨492965, by rfl⟩ : syracuseStep 657287 = 985931) B985931
theorem B395209 : Blo 191804 395209 := bstep (se 2 (by rfl) ⟨148203, by rfl⟩ : syracuseStep 395209 = 296407) B296407
theorem B329771 : Blo 191804 329771 := bstep (se 1 (by rfl) ⟨247328, by rfl⟩ : syracuseStep 329771 = 494657) B494657
theorem B493715 : Blo 191804 493715 := bstep (se 1 (by rfl) ⟨370286, by rfl⟩ : syracuseStep 493715 = 740573) B740573
theorem B1771721 : Blo 191804 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B657665 : Blo 191804 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B494009 : Blo 191804 494009 := bstep (se 2 (by rfl) ⟨185253, by rfl⟩ : syracuseStep 494009 = 370507) B370507
theorem B330169 : Blo 191804 330169 := bstep (se 2 (by rfl) ⟨123813, by rfl⟩ : syracuseStep 330169 = 247627) B247627
theorem B5639179 : Blo 191804 5639179 := bstep (se 1 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 5639179 = 8458769) B8458769
theorem B658475 : Blo 191804 658475 := bstep (se 1 (by rfl) ⟨493856, by rfl⟩ : syracuseStep 658475 = 987713) B987713
theorem B494707 : Blo 191804 494707 := bstep (se 1 (by rfl) ⟨371030, by rfl⟩ : syracuseStep 494707 = 742061) B742061
theorem B494849 : Blo 191804 494849 := bstep (se 2 (by rfl) ⟨185568, by rfl⟩ : syracuseStep 494849 = 371137) B371137
theorem B232967 : Blo 191804 232967 := bstep (se 1 (by rfl) ⟨174725, by rfl⟩ : syracuseStep 232967 = 349451) B349451
theorem B364151 : Blo 191804 364151 := bstep (se 1 (by rfl) ⟨273113, by rfl⟩ : syracuseStep 364151 = 546227) B546227
theorem B593543 : Blo 191804 593543 := bstep (se 1 (by rfl) ⟨445157, by rfl⟩ : syracuseStep 593543 = 890315) B890315
theorem B495305 : Blo 191804 495305 := bstep (se 2 (by rfl) ⟨185739, by rfl⟩ : syracuseStep 495305 = 371479) B371479
theorem B987065 : Blo 191804 987065 := bstep (se 2 (by rfl) ⟨370149, by rfl⟩ : syracuseStep 987065 = 740299) B740299
theorem B921719 : Blo 191804 921719 := bstep (se 1 (by rfl) ⟨691289, by rfl⟩ : syracuseStep 921719 = 1382579) B1382579
theorem B233659 : Blo 191804 233659 := bstep (se 1 (by rfl) ⟨175244, by rfl⟩ : syracuseStep 233659 = 350489) B350489
theorem B659771 : Blo 191804 659771 := bstep (se 1 (by rfl) ⟨494828, by rfl⟩ : syracuseStep 659771 = 989657) B989657
theorem B234119 : Blo 191804 234119 := bstep (se 1 (by rfl) ⟨175589, by rfl⟩ : syracuseStep 234119 = 351179) B351179
theorem B234247 : Blo 191804 234247 := bstep (se 1 (by rfl) ⟨175685, by rfl⟩ : syracuseStep 234247 = 351371) B351371
theorem B463627 : Blo 191804 463627 := bstep (se 1 (by rfl) ⟨347720, by rfl⟩ : syracuseStep 463627 = 695441) B695441
theorem B660257 : Blo 191804 660257 := bstep (se 2 (by rfl) ⟨247596, by rfl⟩ : syracuseStep 660257 = 495193) B495193
theorem B1053587 : Blo 191804 1053587 := bstep (se 1 (by rfl) ⟨790190, by rfl⟩ : syracuseStep 1053587 = 1580381) B1580381
theorem B594955 : Blo 191804 594955 := bstep (se 1 (by rfl) ⟨446216, by rfl⟩ : syracuseStep 594955 = 892433) B892433
theorem B824363 : Blo 191804 824363 := bstep (se 1 (by rfl) ⟨618272, by rfl⟩ : syracuseStep 824363 = 1236545) B1236545
theorem B988361 : Blo 191804 988361 := bstep (se 2 (by rfl) ⟨370635, by rfl⟩ : syracuseStep 988361 = 741271) B741271
theorem B627983 : Blo 191804 627983 := bstep (se 1 (by rfl) ⟨470987, by rfl⟩ : syracuseStep 627983 = 941975) B941975
theorem B365867 : Blo 191804 365867 := bstep (se 1 (by rfl) ⟨274400, by rfl⟩ : syracuseStep 365867 = 548801) B548801
theorem B366095 : Blo 191804 366095 := bstep (se 1 (by rfl) ⟨274571, by rfl⟩ : syracuseStep 366095 = 549143) B549143
theorem B431675 : Blo 191804 431675 := bstep (se 1 (by rfl) ⟨323756, by rfl⟩ : syracuseStep 431675 = 647513) B647513
theorem B431801 : Blo 191804 431801 := bstep (se 2 (by rfl) ⟨161925, by rfl⟩ : syracuseStep 431801 = 323851) B323851
theorem B923393 : Blo 191804 923393 := bstep (se 2 (by rfl) ⟨346272, by rfl⟩ : syracuseStep 923393 = 692545) B692545
theorem B2496257 : Blo 191804 2496257 := bstep (se 2 (by rfl) ⟨936096, by rfl⟩ : syracuseStep 2496257 = 1872193) B1872193
theorem B432143 : Blo 191804 432143 := bstep (se 1 (by rfl) ⟨324107, by rfl⟩ : syracuseStep 432143 = 648215) B648215
theorem B432161 : Blo 191804 432161 := bstep (se 2 (by rfl) ⟨162060, by rfl⟩ : syracuseStep 432161 = 324121) B324121
theorem B301241 : Blo 191804 301241 := bstep (se 2 (by rfl) ⟨112965, by rfl⟩ : syracuseStep 301241 = 225931) B225931
theorem B432503 : Blo 191804 432503 := bstep (se 1 (by rfl) ⟨324377, by rfl⟩ : syracuseStep 432503 = 648755) B648755
theorem B1579409 : Blo 191804 1579409 := bstep (se 2 (by rfl) ⟨592278, by rfl⟩ : syracuseStep 1579409 = 1184557) B1184557
theorem B235963 : Blo 191804 235963 := bstep (se 1 (by rfl) ⟨176972, by rfl⟩ : syracuseStep 235963 = 353945) B353945
theorem B432683 : Blo 191804 432683 := bstep (se 1 (by rfl) ⟨324512, by rfl⟩ : syracuseStep 432683 = 649025) B649025
theorem B1055425 : Blo 191804 1055425 := bstep (se 2 (by rfl) ⟨395784, by rfl⟩ : syracuseStep 1055425 = 791569) B791569
theorem B433043 : Blo 191804 433043 := bstep (se 1 (by rfl) ⟨324782, by rfl⟩ : syracuseStep 433043 = 649565) B649565
theorem B367507 : Blo 191804 367507 := bstep (se 1 (by rfl) ⟨275630, by rfl⟩ : syracuseStep 367507 = 551261) B551261
theorem B433097 : Blo 191804 433097 := bstep (se 2 (by rfl) ⟨162411, by rfl⟩ : syracuseStep 433097 = 324823) B324823
theorem B269257 : Blo 191804 269257 := bstep (se 2 (by rfl) ⟨100971, by rfl⟩ : syracuseStep 269257 = 201943) B201943
theorem B367735 : Blo 191804 367735 := bstep (se 1 (by rfl) ⟨275801, by rfl⟩ : syracuseStep 367735 = 551603) B551603
theorem B498977 : Blo 191804 498977 := bstep (se 2 (by rfl) ⟨187116, by rfl⟩ : syracuseStep 498977 = 374233) B374233
theorem B4726349 : Blo 191804 4726349 := bstep (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) B1772381
theorem B433799 : Blo 191804 433799 := bstep (se 1 (by rfl) ⟨325349, by rfl⟩ : syracuseStep 433799 = 650699) B650699
theorem B827081 : Blo 191804 827081 := bstep (se 2 (by rfl) ⟨310155, by rfl⟩ : syracuseStep 827081 = 620311) B620311
theorem B466703 : Blo 191804 466703 := bstep (se 1 (by rfl) ⟨350027, by rfl⟩ : syracuseStep 466703 = 700055) B700055
theorem B1056527 : Blo 191804 1056527 := bstep (se 1 (by rfl) ⟨792395, by rfl⟩ : syracuseStep 1056527 = 1584791) B1584791
theorem B433979 : Blo 191804 433979 := bstep (se 1 (by rfl) ⟨325484, by rfl⟩ : syracuseStep 433979 = 650969) B650969
theorem B434105 : Blo 191804 434105 := bstep (se 2 (by rfl) ⟨162789, by rfl⟩ : syracuseStep 434105 = 325579) B325579
theorem B893015 : Blo 191804 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B1187959 : Blo 191804 1187959 := bstep (se 1 (by rfl) ⟨890969, by rfl⟩ : syracuseStep 1187959 = 1781939) B1781939
theorem B434447 : Blo 191804 434447 := bstep (se 1 (by rfl) ⟨325835, by rfl⟩ : syracuseStep 434447 = 651671) B651671
theorem B434465 : Blo 191804 434465 := bstep (se 2 (by rfl) ⟨162924, by rfl⟩ : syracuseStep 434465 = 325849) B325849
theorem B434807 : Blo 191804 434807 := bstep (se 1 (by rfl) ⟨326105, by rfl⟩ : syracuseStep 434807 = 652211) B652211
theorem B369299 : Blo 191804 369299 := bstep (se 1 (by rfl) ⟨276974, by rfl⟩ : syracuseStep 369299 = 553949) B553949
theorem B369353 : Blo 191804 369353 := bstep (se 2 (by rfl) ⟨138507, by rfl⟩ : syracuseStep 369353 = 277015) B277015
theorem B500513 : Blo 191804 500513 := bstep (se 2 (by rfl) ⟨187692, by rfl⟩ : syracuseStep 500513 = 375385) B375385
theorem B434987 : Blo 191804 434987 := bstep (se 1 (by rfl) ⟨326240, by rfl⟩ : syracuseStep 434987 = 652481) B652481
theorem B369451 : Blo 191804 369451 := bstep (se 1 (by rfl) ⟨277088, by rfl⟩ : syracuseStep 369451 = 554177) B554177
theorem B1778699 : Blo 191804 1778699 := bstep (se 1 (by rfl) ⟨1334024, by rfl⟩ : syracuseStep 1778699 = 2668049) B2668049
theorem B533519 : Blo 191804 533519 := bstep (se 1 (by rfl) ⟨400139, by rfl⟩ : syracuseStep 533519 = 800279) B800279
theorem B369679 : Blo 191804 369679 := bstep (se 1 (by rfl) ⟨277259, by rfl⟩ : syracuseStep 369679 = 554519) B554519
theorem B468011 : Blo 191804 468011 := bstep (se 1 (by rfl) ⟨351008, by rfl⟩ : syracuseStep 468011 = 702017) B702017
theorem B435347 : Blo 191804 435347 := bstep (se 1 (by rfl) ⟨326510, by rfl⟩ : syracuseStep 435347 = 653021) B653021
theorem B435401 : Blo 191804 435401 := bstep (se 2 (by rfl) ⟨163275, by rfl⟩ : syracuseStep 435401 = 326551) B326551
theorem B4072913 : Blo 191804 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B436103 : Blo 191804 436103 := bstep (se 1 (by rfl) ⟨327077, by rfl⟩ : syracuseStep 436103 = 654155) B654155
theorem B731065 : Blo 191804 731065 := bstep (se 2 (by rfl) ⟨274149, by rfl⟩ : syracuseStep 731065 = 548299) B548299
theorem B436283 : Blo 191804 436283 := bstep (se 1 (by rfl) ⟨327212, by rfl⟩ : syracuseStep 436283 = 654425) B654425
theorem B436409 : Blo 191804 436409 := bstep (se 2 (by rfl) ⟨163653, by rfl⟩ : syracuseStep 436409 = 327307) B327307
theorem B436751 : Blo 191804 436751 := bstep (se 1 (by rfl) ⟨327563, by rfl⟩ : syracuseStep 436751 = 655127) B655127
theorem B928279 : Blo 191804 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B436769 : Blo 191804 436769 := bstep (se 2 (by rfl) ⟨163788, by rfl⟩ : syracuseStep 436769 = 327577) B327577
theorem B371243 : Blo 191804 371243 := bstep (se 1 (by rfl) ⟨278432, by rfl⟩ : syracuseStep 371243 = 556865) B556865
theorem B1780481 : Blo 191804 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B2960165 : Blo 191804 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B437111 : Blo 191804 437111 := bstep (se 1 (by rfl) ⟨327833, by rfl⟩ : syracuseStep 437111 = 655667) B655667
theorem B437291 : Blo 191804 437291 := bstep (se 1 (by rfl) ⟨327968, by rfl⟩ : syracuseStep 437291 = 655937) B655937
theorem B699479 : Blo 191804 699479 := bstep (se 1 (by rfl) ⟨524609, by rfl⟩ : syracuseStep 699479 = 1049219) B1049219
theorem B1092953 : Blo 191804 1092953 := bstep (se 2 (by rfl) ⟨409857, by rfl⟩ : syracuseStep 1092953 = 819715) B819715
theorem B437651 : Blo 191804 437651 := bstep (se 1 (by rfl) ⟨328238, by rfl⟩ : syracuseStep 437651 = 656477) B656477
theorem B437705 : Blo 191804 437705 := bstep (se 2 (by rfl) ⟨164139, by rfl⟩ : syracuseStep 437705 = 328279) B328279
theorem B273979 : Blo 191804 273979 := bstep (se 1 (by rfl) ⟨205484, by rfl⟩ : syracuseStep 273979 = 410969) B410969
theorem B3124813 : Blo 191804 3124813 := bstep (se 3 (by rfl) ⟨585902, by rfl⟩ : syracuseStep 3124813 = 1171805) B1171805
theorem B2207411 : Blo 191804 2207411 := bstep (se 1 (by rfl) ⟨1655558, by rfl⟩ : syracuseStep 2207411 = 3311117) B3311117
theorem B1093409 : Blo 191804 1093409 := bstep (se 2 (by rfl) ⟨410028, by rfl⟩ : syracuseStep 1093409 = 820057) B820057
theorem B274423 : Blo 191804 274423 := bstep (se 1 (by rfl) ⟨205817, by rfl⟩ : syracuseStep 274423 = 411635) B411635
theorem B1093661 : Blo 191804 1093661 := bstep (se 3 (by rfl) ⟨205061, by rfl⟩ : syracuseStep 1093661 = 410123) B410123
theorem B438407 : Blo 191804 438407 := bstep (se 1 (by rfl) ⟨328805, by rfl⟩ : syracuseStep 438407 = 657611) B657611
theorem B307471 : Blo 191804 307471 := bstep (se 1 (by rfl) ⟨230603, by rfl⟩ : syracuseStep 307471 = 461207) B461207
theorem B438587 : Blo 191804 438587 := bstep (se 1 (by rfl) ⟨328940, by rfl⟩ : syracuseStep 438587 = 657881) B657881
theorem B438713 : Blo 191804 438713 := bstep (se 2 (by rfl) ⟨164517, by rfl⟩ : syracuseStep 438713 = 329035) B329035
theorem B307727 : Blo 191804 307727 := bstep (se 1 (by rfl) ⟨230795, by rfl⟩ : syracuseStep 307727 = 461591) B461591
theorem B471611 : Blo 191804 471611 := bstep (se 1 (by rfl) ⟨353708, by rfl⟩ : syracuseStep 471611 = 707417) B707417
theorem B2503385 : Blo 191804 2503385 := bstep (se 2 (by rfl) ⟨938769, by rfl⟩ : syracuseStep 2503385 = 1877539) B1877539
theorem B733967 : Blo 191804 733967 := bstep (se 1 (by rfl) ⟨550475, by rfl⟩ : syracuseStep 733967 = 1100951) B1100951
theorem B439055 : Blo 191804 439055 := bstep (se 1 (by rfl) ⟨329291, by rfl⟩ : syracuseStep 439055 = 658583) B658583
theorem B439073 : Blo 191804 439073 := bstep (se 2 (by rfl) ⟨164652, by rfl⟩ : syracuseStep 439073 = 329305) B329305
theorem B275243 : Blo 191804 275243 := bstep (se 1 (by rfl) ⟨206432, by rfl⟩ : syracuseStep 275243 = 412865) B412865
theorem B439415 : Blo 191804 439415 := bstep (se 1 (by rfl) ⟨329561, by rfl⟩ : syracuseStep 439415 = 659123) B659123
theorem B439595 : Blo 191804 439595 := bstep (se 1 (by rfl) ⟨329696, by rfl⟩ : syracuseStep 439595 = 659393) B659393
theorem B3225091 : Blo 191804 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B833111 : Blo 191804 833111 := bstep (se 1 (by rfl) ⟨624833, by rfl⟩ : syracuseStep 833111 = 1249667) B1249667
theorem B243319 : Blo 191804 243319 := bstep (se 1 (by rfl) ⟨182489, by rfl⟩ : syracuseStep 243319 = 364979) B364979
theorem B308855 : Blo 191804 308855 := bstep (se 1 (by rfl) ⟨231641, by rfl⟩ : syracuseStep 308855 = 463283) B463283
theorem B439955 : Blo 191804 439955 := bstep (se 1 (by rfl) ⟨329966, by rfl⟩ : syracuseStep 439955 = 659933) B659933
theorem B440009 : Blo 191804 440009 := bstep (se 2 (by rfl) ⟨165003, by rfl⟩ : syracuseStep 440009 = 330007) B330007
theorem B1587059 : Blo 191804 1587059 := bstep (se 1 (by rfl) ⟨1190294, by rfl⟩ : syracuseStep 1587059 = 2380589) B2380589
theorem B702361 : Blo 191804 702361 := bstep (se 2 (by rfl) ⟨263385, by rfl⟩ : syracuseStep 702361 = 526771) B526771
theorem B243643 : Blo 191804 243643 := bstep (se 1 (by rfl) ⟨182732, by rfl⟩ : syracuseStep 243643 = 365465) B365465
theorem B309367 : Blo 191804 309367 := bstep (se 1 (by rfl) ⟨232025, by rfl⟩ : syracuseStep 309367 = 464051) B464051
theorem B1718561 : Blo 191804 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B1096051 : Blo 191804 1096051 := bstep (se 1 (by rfl) ⟨822038, by rfl⟩ : syracuseStep 1096051 = 1644077) B1644077
theorem B440761 : Blo 191804 440761 := bstep (se 2 (by rfl) ⟨165285, by rfl⟩ : syracuseStep 440761 = 330571) B330571
theorem B375355 : Blo 191804 375355 := bstep (se 1 (by rfl) ⟨281516, by rfl⟩ : syracuseStep 375355 = 563033) B563033
theorem B277111 : Blo 191804 277111 := bstep (se 1 (by rfl) ⟨207833, by rfl⟩ : syracuseStep 277111 = 415667) B415667
theorem B1522547 : Blo 191804 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B244615 : Blo 191804 244615 := bstep (se 1 (by rfl) ⟨183461, by rfl⟩ : syracuseStep 244615 = 366923) B366923
theorem B2177945 : Blo 191804 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B310315 : Blo 191804 310315 := bstep (se 1 (by rfl) ⟨232736, by rfl⟩ : syracuseStep 310315 = 465473) B465473
theorem B441463 : Blo 191804 441463 := bstep (se 1 (by rfl) ⟨331097, by rfl⟩ : syracuseStep 441463 = 662195) B662195
theorem B703745 : Blo 191804 703745 := bstep (se 2 (by rfl) ⟨263904, by rfl⟩ : syracuseStep 703745 = 527809) B527809
theorem B245035 : Blo 191804 245035 := bstep (se 1 (by rfl) ⟨183776, by rfl⟩ : syracuseStep 245035 = 367553) B367553
theorem B507179 : Blo 191804 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B245263 : Blo 191804 245263 := bstep (se 1 (by rfl) ⟨183947, by rfl⟩ : syracuseStep 245263 = 367895) B367895
theorem B278159 : Blo 191804 278159 := bstep (se 1 (by rfl) ⟨208619, by rfl⟩ : syracuseStep 278159 = 417239) B417239
theorem B1654465 : Blo 191804 1654465 := bstep (se 2 (by rfl) ⟨620424, by rfl⟩ : syracuseStep 1654465 = 1240849) B1240849
theorem B1097509 : Blo 191804 1097509 := bstep (se 4 (by rfl) ⟨102891, by rfl⟩ : syracuseStep 1097509 = 205783) B205783
theorem B737171 : Blo 191804 737171 := bstep (se 1 (by rfl) ⟨552878, by rfl⟩ : syracuseStep 737171 = 1105757) B1105757
theorem B278473 : Blo 191804 278473 := bstep (se 2 (by rfl) ⟨104427, by rfl⟩ : syracuseStep 278473 = 208855) B208855
theorem B2211851 : Blo 191804 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B1392727 : Blo 191804 1392727 := bstep (se 1 (by rfl) ⟨1044545, by rfl⟩ : syracuseStep 1392727 = 2089091) B2089091
theorem B246007 : Blo 191804 246007 := bstep (se 1 (by rfl) ⟨184505, by rfl⟩ : syracuseStep 246007 = 369011) B369011
theorem B1098035 : Blo 191804 1098035 := bstep (se 1 (by rfl) ⟨823526, by rfl⟩ : syracuseStep 1098035 = 1647053) B1647053
theorem B1556957 : Blo 191804 1556957 := bstep (se 3 (by rfl) ⟨291929, by rfl⟩ : syracuseStep 1556957 = 583859) B583859
theorem B246331 : Blo 191804 246331 := bstep (se 1 (by rfl) ⟨184748, by rfl⟩ : syracuseStep 246331 = 369497) B369497
theorem B3982117 : Blo 191804 3982117 := bstep (se 4 (by rfl) ⟨373323, by rfl⟩ : syracuseStep 3982117 = 746647) B746647
theorem B443407 : Blo 191804 443407 := bstep (se 1 (by rfl) ⟨332555, by rfl⟩ : syracuseStep 443407 = 665111) B665111
theorem B246827 : Blo 191804 246827 := bstep (se 1 (by rfl) ⟨185120, by rfl⟩ : syracuseStep 246827 = 370241) B370241
theorem B312635 : Blo 191804 312635 := bstep (se 1 (by rfl) ⟨234476, by rfl⟩ : syracuseStep 312635 = 468953) B468953
theorem B247303 : Blo 191804 247303 := bstep (se 1 (by rfl) ⟨185477, by rfl⟩ : syracuseStep 247303 = 370955) B370955
theorem B738827 : Blo 191804 738827 := bstep (se 1 (by rfl) ⟨554120, by rfl⟩ : syracuseStep 738827 = 1108241) B1108241
theorem B1099493 : Blo 191804 1099493 := bstep (se 4 (by rfl) ⟨103077, by rfl⟩ : syracuseStep 1099493 = 206155) B206155
theorem B247799 : Blo 191804 247799 := bstep (se 1 (by rfl) ⟨185849, by rfl⟩ : syracuseStep 247799 = 371699) B371699
theorem B936173 : Blo 191804 936173 := bstep (se 3 (by rfl) ⟨175532, by rfl⟩ : syracuseStep 936173 = 351065) B351065
theorem B2115821 : Blo 191804 2115821 := bstep (se 3 (by rfl) ⟨396716, by rfl⟩ : syracuseStep 2115821 = 793433) B793433
theorem B215815 : Blo 191804 215815 := bstep (se 1 (by rfl) ⟨161861, by rfl⟩ : syracuseStep 215815 = 323723) B323723
theorem B215995 : Blo 191804 215995 := bstep (se 1 (by rfl) ⟨161996, by rfl⟩ : syracuseStep 215995 = 323993) B323993
theorem B904463 : Blo 191804 904463 := bstep (se 1 (by rfl) ⟨678347, by rfl⟩ : syracuseStep 904463 = 1356695) B1356695
theorem B1887623 : Blo 191804 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B216463 : Blo 191804 216463 := bstep (se 1 (by rfl) ⟨162347, by rfl⟩ : syracuseStep 216463 = 324695) B324695
theorem B347663 : Blo 191804 347663 := bstep (se 1 (by rfl) ⟨260747, by rfl⟩ : syracuseStep 347663 = 521495) B521495
theorem B216967 : Blo 191804 216967 := bstep (se 1 (by rfl) ⟨162725, by rfl⟩ : syracuseStep 216967 = 325451) B325451
theorem B217147 : Blo 191804 217147 := bstep (se 1 (by rfl) ⟨162860, by rfl⟩ : syracuseStep 217147 = 325721) B325721
theorem B2806163 : Blo 191804 2806163 := bstep (se 1 (by rfl) ⟨2104622, by rfl⟩ : syracuseStep 2806163 = 4209245) B4209245
theorem B217615 : Blo 191804 217615 := bstep (se 1 (by rfl) ⟨163211, by rfl⟩ : syracuseStep 217615 = 326423) B326423
theorem B938557 : Blo 191804 938557 := bstep (se 3 (by rfl) ⟨175979, by rfl⟩ : syracuseStep 938557 = 351959) B351959
theorem B971351 : Blo 191804 971351 := bstep (se 1 (by rfl) ⟨728513, by rfl⟩ : syracuseStep 971351 = 1457027) B1457027
theorem B2347699 : Blo 191804 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B7000769 : Blo 191804 7000769 := bstep (se 2 (by rfl) ⟨2625288, by rfl⟩ : syracuseStep 7000769 = 5250577) B5250577
theorem B348961 : Blo 191804 348961 := bstep (se 2 (by rfl) ⟨130860, by rfl⟩ : syracuseStep 348961 = 261721) B261721
theorem B414497 : Blo 191804 414497 := bstep (se 2 (by rfl) ⟨155436, by rfl⟩ : syracuseStep 414497 = 310873) B310873
theorem B218119 : Blo 191804 218119 := bstep (se 1 (by rfl) ⟨163589, by rfl⟩ : syracuseStep 218119 = 327179) B327179
theorem B971837 : Blo 191804 971837 := bstep (se 3 (by rfl) ⟨182219, by rfl⟩ : syracuseStep 971837 = 364439) B364439
theorem B218299 : Blo 191804 218299 := bstep (se 1 (by rfl) ⟨163724, by rfl⟩ : syracuseStep 218299 = 327449) B327449
theorem B742715 : Blo 191804 742715 := bstep (se 1 (by rfl) ⟨557036, by rfl⟩ : syracuseStep 742715 = 1114073) B1114073
theorem B218767 : Blo 191804 218767 := bstep (se 1 (by rfl) ⟨164075, by rfl⟩ : syracuseStep 218767 = 328151) B328151
theorem B743201 : Blo 191804 743201 := bstep (se 2 (by rfl) ⟨278700, by rfl⟩ : syracuseStep 743201 = 557401) B557401
theorem B1857431 : Blo 191804 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B1038233 : Blo 191804 1038233 := bstep (se 2 (by rfl) ⟨389337, by rfl⟩ : syracuseStep 1038233 = 778675) B778675
theorem B3790795 : Blo 191804 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B219271 : Blo 191804 219271 := bstep (se 1 (by rfl) ⟨164453, by rfl⟩ : syracuseStep 219271 = 328907) B328907
theorem B219451 : Blo 191804 219451 := bstep (se 1 (by rfl) ⟨164588, by rfl⟩ : syracuseStep 219451 = 329177) B329177
theorem B940403 : Blo 191804 940403 := bstep (se 1 (by rfl) ⟨705302, by rfl⟩ : syracuseStep 940403 = 1410605) B1410605
theorem B547343 : Blo 191804 547343 := bstep (se 1 (by rfl) ⟨410507, by rfl⟩ : syracuseStep 547343 = 821015) B821015
theorem B1169963 : Blo 191804 1169963 := bstep (se 1 (by rfl) ⟨877472, by rfl⟩ : syracuseStep 1169963 = 1754945) B1754945
theorem B219919 : Blo 191804 219919 := bstep (se 1 (by rfl) ⟨164939, by rfl⟩ : syracuseStep 219919 = 329879) B329879
theorem B973619 : Blo 191804 973619 := bstep (se 1 (by rfl) ⟨730214, by rfl⟩ : syracuseStep 973619 = 1460429) B1460429
theorem B973943 : Blo 191804 973943 := bstep (se 1 (by rfl) ⟨730457, by rfl⟩ : syracuseStep 973943 = 1460915) B1460915
theorem B941465 : Blo 191804 941465 := bstep (se 2 (by rfl) ⟨353049, by rfl⟩ : syracuseStep 941465 = 706099) B706099
theorem B548471 : Blo 191804 548471 := bstep (se 1 (by rfl) ⟨411353, by rfl⟩ : syracuseStep 548471 = 822707) B822707
theorem B843635 : Blo 191804 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B417683 : Blo 191804 417683 := bstep (se 1 (by rfl) ⟨313262, by rfl⟩ : syracuseStep 417683 = 626525) B626525
theorem B974915 : Blo 191804 974915 := bstep (se 1 (by rfl) ⟨731186, by rfl⟩ : syracuseStep 974915 = 1462373) B1462373
theorem B1663213 : Blo 191804 1663213 := bstep (se 3 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 1663213 = 623705) B623705
theorem B975239 : Blo 191804 975239 := bstep (se 1 (by rfl) ⟨731429, by rfl⟩ : syracuseStep 975239 = 1462859) B1462859
theorem B221575 : Blo 191804 221575 := bstep (se 1 (by rfl) ⟨166181, by rfl⟩ : syracuseStep 221575 = 332363) B332363
theorem B1565261 : Blo 191804 1565261 := bstep (se 3 (by rfl) ⟨293486, by rfl⟩ : syracuseStep 1565261 = 586973) B586973
theorem B4973237 : Blo 191804 4973237 := bstep (se 5 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 4973237 = 466241) B466241
theorem B1041133 : Blo 191804 1041133 := bstep (se 3 (by rfl) ⟨195212, by rfl⟩ : syracuseStep 1041133 = 390425) B390425
theorem B1860353 : Blo 191804 1860353 := bstep (se 2 (by rfl) ⟨697632, by rfl⟩ : syracuseStep 1860353 = 1395265) B1395265
theorem B1172369 : Blo 191804 1172369 := bstep (se 2 (by rfl) ⟨439638, by rfl⟩ : syracuseStep 1172369 = 879277) B879277
theorem B287735 : Blo 191804 287735 := bstep (se 1 (by rfl) ⟨215801, by rfl⟩ : syracuseStep 287735 = 431603) B431603
theorem B287759 : Blo 191804 287759 := bstep (se 1 (by rfl) ⟨215819, by rfl⟩ : syracuseStep 287759 = 431639) B431639
theorem B1664023 : Blo 191804 1664023 := bstep (se 1 (by rfl) ⟨1248017, by rfl⟩ : syracuseStep 1664023 = 2496035) B2496035
theorem B287801 : Blo 191804 287801 := bstep (se 2 (by rfl) ⟨107925, by rfl⟩ : syracuseStep 287801 = 215851) B215851
theorem B287879 : Blo 191804 287879 := bstep (se 1 (by rfl) ⟨215909, by rfl⟩ : syracuseStep 287879 = 431819) B431819
theorem B287915 : Blo 191804 287915 := bstep (se 1 (by rfl) ⟨215936, by rfl⟩ : syracuseStep 287915 = 431873) B431873
theorem B287945 : Blo 191804 287945 := bstep (se 2 (by rfl) ⟨107979, by rfl⟩ : syracuseStep 287945 = 215959) B215959
theorem B550145 : Blo 191804 550145 := bstep (se 2 (by rfl) ⟨206304, by rfl⟩ : syracuseStep 550145 = 412609) B412609
theorem B1107215 : Blo 191804 1107215 := bstep (se 1 (by rfl) ⟨830411, by rfl⟩ : syracuseStep 1107215 = 1660823) B1660823
theorem B288059 : Blo 191804 288059 := bstep (se 1 (by rfl) ⟨216044, by rfl⟩ : syracuseStep 288059 = 432089) B432089
theorem B3728699 : Blo 191804 3728699 := bstep (se 1 (by rfl) ⟨2796524, by rfl⟩ : syracuseStep 3728699 = 5593049) B5593049
theorem B550259 : Blo 191804 550259 := bstep (se 1 (by rfl) ⟨412694, by rfl⟩ : syracuseStep 550259 = 825389) B825389
theorem B288119 : Blo 191804 288119 := bstep (se 1 (by rfl) ⟨216089, by rfl⟩ : syracuseStep 288119 = 432179) B432179
theorem B288143 : Blo 191804 288143 := bstep (se 1 (by rfl) ⟨216107, by rfl⟩ : syracuseStep 288143 = 432215) B432215
theorem B288185 : Blo 191804 288185 := bstep (se 2 (by rfl) ⟨108069, by rfl⟩ : syracuseStep 288185 = 216139) B216139
theorem B288263 : Blo 191804 288263 := bstep (se 1 (by rfl) ⟨216197, by rfl⟩ : syracuseStep 288263 = 432395) B432395
theorem B288299 : Blo 191804 288299 := bstep (se 1 (by rfl) ⟨216224, by rfl⟩ : syracuseStep 288299 = 432449) B432449
theorem B288329 : Blo 191804 288329 := bstep (se 2 (by rfl) ⟨108123, by rfl⟩ : syracuseStep 288329 = 216247) B216247
theorem B288443 : Blo 191804 288443 := bstep (se 1 (by rfl) ⟨216332, by rfl⟩ : syracuseStep 288443 = 432665) B432665
theorem B550601 : Blo 191804 550601 := bstep (se 2 (by rfl) ⟨206475, by rfl⟩ : syracuseStep 550601 = 412951) B412951
theorem B288503 : Blo 191804 288503 := bstep (se 1 (by rfl) ⟨216377, by rfl⟩ : syracuseStep 288503 = 432755) B432755
theorem B288527 : Blo 191804 288527 := bstep (se 1 (by rfl) ⟨216395, by rfl⟩ : syracuseStep 288527 = 432791) B432791
theorem B288569 : Blo 191804 288569 := bstep (se 2 (by rfl) ⟨108213, by rfl⟩ : syracuseStep 288569 = 216427) B216427
theorem B747323 : Blo 191804 747323 := bstep (se 1 (by rfl) ⟨560492, by rfl⟩ : syracuseStep 747323 = 1120985) B1120985
theorem B780167 : Blo 191804 780167 := bstep (se 1 (by rfl) ⟨585125, by rfl⟩ : syracuseStep 780167 = 1170251) B1170251
theorem B288647 : Blo 191804 288647 := bstep (se 1 (by rfl) ⟨216485, by rfl⟩ : syracuseStep 288647 = 432971) B432971
theorem B288683 : Blo 191804 288683 := bstep (se 1 (by rfl) ⟨216512, by rfl⟩ : syracuseStep 288683 = 433025) B433025
theorem B288713 : Blo 191804 288713 := bstep (se 2 (by rfl) ⟨108267, by rfl⟩ : syracuseStep 288713 = 216535) B216535
theorem B288827 : Blo 191804 288827 := bstep (se 1 (by rfl) ⟨216620, by rfl⟩ : syracuseStep 288827 = 433241) B433241
theorem B288887 : Blo 191804 288887 := bstep (se 1 (by rfl) ⟨216665, by rfl⟩ : syracuseStep 288887 = 433331) B433331
theorem B288911 : Blo 191804 288911 := bstep (se 1 (by rfl) ⟨216683, by rfl⟩ : syracuseStep 288911 = 433367) B433367
theorem B1665197 : Blo 191804 1665197 := bstep (se 3 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 1665197 = 624449) B624449
theorem B288953 : Blo 191804 288953 := bstep (se 2 (by rfl) ⟨108357, by rfl⟩ : syracuseStep 288953 = 216715) B216715
theorem B289031 : Blo 191804 289031 := bstep (se 1 (by rfl) ⟨216773, by rfl⟩ : syracuseStep 289031 = 433547) B433547
theorem B289067 : Blo 191804 289067 := bstep (se 1 (by rfl) ⟨216800, by rfl⟩ : syracuseStep 289067 = 433601) B433601
theorem B289097 : Blo 191804 289097 := bstep (se 2 (by rfl) ⟨108411, by rfl⟩ : syracuseStep 289097 = 216823) B216823
theorem B485747 : Blo 191804 485747 := bstep (se 1 (by rfl) ⟨364310, by rfl⟩ : syracuseStep 485747 = 728621) B728621
theorem B649619 : Blo 191804 649619 := bstep (se 1 (by rfl) ⟨487214, by rfl⟩ : syracuseStep 649619 = 974429) B974429
theorem B616889 : Blo 191804 616889 := bstep (se 2 (by rfl) ⟨231333, by rfl⟩ : syracuseStep 616889 = 462667) B462667
theorem B289211 : Blo 191804 289211 := bstep (se 1 (by rfl) ⟨216908, by rfl⟩ : syracuseStep 289211 = 433817) B433817
theorem B289271 : Blo 191804 289271 := bstep (se 1 (by rfl) ⟨216953, by rfl⟩ : syracuseStep 289271 = 433907) B433907
theorem B289295 : Blo 191804 289295 := bstep (se 1 (by rfl) ⟨216971, by rfl⟩ : syracuseStep 289295 = 433943) B433943
theorem B289337 : Blo 191804 289337 := bstep (se 2 (by rfl) ⟨108501, by rfl⟩ : syracuseStep 289337 = 217003) B217003
theorem B1239619 : Blo 191804 1239619 := bstep (se 1 (by rfl) ⟨929714, by rfl⟩ : syracuseStep 1239619 = 1859429) B1859429
theorem B289415 : Blo 191804 289415 := bstep (se 1 (by rfl) ⟨217061, by rfl⟩ : syracuseStep 289415 = 434123) B434123
theorem B289451 : Blo 191804 289451 := bstep (se 1 (by rfl) ⟨217088, by rfl⟩ : syracuseStep 289451 = 434177) B434177
theorem B1108673 : Blo 191804 1108673 := bstep (se 2 (by rfl) ⟨415752, by rfl⟩ : syracuseStep 1108673 = 831505) B831505
theorem B289481 : Blo 191804 289481 := bstep (se 2 (by rfl) ⟨108555, by rfl⟩ : syracuseStep 289481 = 217111) B217111
theorem B2779919 : Blo 191804 2779919 := bstep (se 1 (by rfl) ⟨2084939, by rfl⟩ : syracuseStep 2779919 = 4169879) B4169879
theorem B59894549 : Blo 191804 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B289595 : Blo 191804 289595 := bstep (se 1 (by rfl) ⟨217196, by rfl⟩ : syracuseStep 289595 = 434393) B434393
theorem B486263 : Blo 191804 486263 := bstep (se 1 (by rfl) ⟨364697, by rfl⟩ : syracuseStep 486263 = 729395) B729395
theorem B584567 : Blo 191804 584567 := bstep (se 1 (by rfl) ⟨438425, by rfl⟩ : syracuseStep 584567 = 876851) B876851
theorem B289655 : Blo 191804 289655 := bstep (se 1 (by rfl) ⟨217241, by rfl⟩ : syracuseStep 289655 = 434483) B434483
theorem B289679 : Blo 191804 289679 := bstep (se 1 (by rfl) ⟨217259, by rfl⟩ : syracuseStep 289679 = 434519) B434519
theorem B289721 : Blo 191804 289721 := bstep (se 2 (by rfl) ⟨108645, by rfl⟩ : syracuseStep 289721 = 217291) B217291
theorem B289799 : Blo 191804 289799 := bstep (se 1 (by rfl) ⟨217349, by rfl⟩ : syracuseStep 289799 = 434699) B434699
theorem B289835 : Blo 191804 289835 := bstep (se 1 (by rfl) ⟨217376, by rfl⟩ : syracuseStep 289835 = 434753) B434753
theorem B289865 : Blo 191804 289865 := bstep (se 2 (by rfl) ⟨108699, by rfl⟩ : syracuseStep 289865 = 217399) B217399
theorem B289979 : Blo 191804 289979 := bstep (se 1 (by rfl) ⟨217484, by rfl⟩ : syracuseStep 289979 = 434969) B434969
theorem B290039 : Blo 191804 290039 := bstep (se 1 (by rfl) ⟨217529, by rfl⟩ : syracuseStep 290039 = 435059) B435059
theorem B290063 : Blo 191804 290063 := bstep (se 1 (by rfl) ⟨217547, by rfl⟩ : syracuseStep 290063 = 435095) B435095
theorem B290105 : Blo 191804 290105 := bstep (se 2 (by rfl) ⟨108789, by rfl⟩ : syracuseStep 290105 = 217579) B217579
theorem B191879 : Blo 191804 191879 := bstep (se 1 (by rfl) ⟨143909, by rfl⟩ : syracuseStep 191879 = 287819) B287819
theorem B290183 : Blo 191804 290183 := bstep (se 1 (by rfl) ⟨217637, by rfl⟩ : syracuseStep 290183 = 435275) B435275
theorem B191887 : Blo 191804 191887 := bstep (se 1 (by rfl) ⟨143915, by rfl⟩ : syracuseStep 191887 = 287831) B287831
theorem B290219 : Blo 191804 290219 := bstep (se 1 (by rfl) ⟨217664, by rfl⟩ : syracuseStep 290219 = 435329) B435329
theorem B191931 : Blo 191804 191931 := bstep (se 1 (by rfl) ⟨143948, by rfl⟩ : syracuseStep 191931 = 287897) B287897
theorem B290249 : Blo 191804 290249 := bstep (se 2 (by rfl) ⟨108843, by rfl⟩ : syracuseStep 290249 = 217687) B217687
theorem B192007 : Blo 191804 192007 := bstep (se 1 (by rfl) ⟨144005, by rfl⟩ : syracuseStep 192007 = 288011) B288011
theorem B192015 : Blo 191804 192015 := bstep (se 1 (by rfl) ⟨144011, by rfl⟩ : syracuseStep 192015 = 288023) B288023
theorem B552491 : Blo 191804 552491 := bstep (se 1 (by rfl) ⟨414368, by rfl⟩ : syracuseStep 552491 = 828737) B828737
theorem B192059 : Blo 191804 192059 := bstep (se 1 (by rfl) ⟨144044, by rfl⟩ : syracuseStep 192059 = 288089) B288089
theorem B290363 : Blo 191804 290363 := bstep (se 1 (by rfl) ⟨217772, by rfl⟩ : syracuseStep 290363 = 435545) B435545
theorem B519767 : Blo 191804 519767 := bstep (se 1 (by rfl) ⟨389825, by rfl⟩ : syracuseStep 519767 = 779651) B779651
theorem B290423 : Blo 191804 290423 := bstep (se 1 (by rfl) ⟨217817, by rfl⟩ : syracuseStep 290423 = 435635) B435635
theorem B192135 : Blo 191804 192135 := bstep (se 1 (by rfl) ⟨144101, by rfl⟩ : syracuseStep 192135 = 288203) B288203
theorem B192143 : Blo 191804 192143 := bstep (se 1 (by rfl) ⟨144107, by rfl⟩ : syracuseStep 192143 = 288215) B288215
theorem B290447 : Blo 191804 290447 := bstep (se 1 (by rfl) ⟨217835, by rfl⟩ : syracuseStep 290447 = 435671) B435671
theorem B290489 : Blo 191804 290489 := bstep (se 2 (by rfl) ⟨108933, by rfl⟩ : syracuseStep 290489 = 217867) B217867
theorem B192187 : Blo 191804 192187 := bstep (se 1 (by rfl) ⟨144140, by rfl⟩ : syracuseStep 192187 = 288281) B288281
theorem B192263 : Blo 191804 192263 := bstep (se 1 (by rfl) ⟨144197, by rfl⟩ : syracuseStep 192263 = 288395) B288395
theorem B290567 : Blo 191804 290567 := bstep (se 1 (by rfl) ⟨217925, by rfl⟩ : syracuseStep 290567 = 435851) B435851
theorem B192271 : Blo 191804 192271 := bstep (se 1 (by rfl) ⟨144203, by rfl⟩ : syracuseStep 192271 = 288407) B288407
theorem B651023 : Blo 191804 651023 := bstep (se 1 (by rfl) ⟨488267, by rfl⟩ : syracuseStep 651023 = 976535) B976535
theorem B552719 : Blo 191804 552719 := bstep (se 1 (by rfl) ⟨414539, by rfl⟩ : syracuseStep 552719 = 829079) B829079
theorem B290603 : Blo 191804 290603 := bstep (se 1 (by rfl) ⟨217952, by rfl⟩ : syracuseStep 290603 = 435905) B435905
theorem B192315 : Blo 191804 192315 := bstep (se 1 (by rfl) ⟨144236, by rfl⟩ : syracuseStep 192315 = 288473) B288473
theorem B618299 : Blo 191804 618299 := bstep (se 1 (by rfl) ⟨463724, by rfl⟩ : syracuseStep 618299 = 927449) B927449
theorem B290633 : Blo 191804 290633 := bstep (se 2 (by rfl) ⟨108987, by rfl⟩ : syracuseStep 290633 = 217975) B217975
theorem B487255 : Blo 191804 487255 := bstep (se 1 (by rfl) ⟨365441, by rfl⟩ : syracuseStep 487255 = 730883) B730883
theorem B978803 : Blo 191804 978803 := bstep (se 1 (by rfl) ⟨734102, by rfl⟩ : syracuseStep 978803 = 1468205) B1468205
theorem B192391 : Blo 191804 192391 := bstep (se 1 (by rfl) ⟨144293, by rfl⟩ : syracuseStep 192391 = 288587) B288587
theorem B192399 : Blo 191804 192399 := bstep (se 1 (by rfl) ⟨144299, by rfl⟩ : syracuseStep 192399 = 288599) B288599
theorem B192443 : Blo 191804 192443 := bstep (se 1 (by rfl) ⟨144332, by rfl⟩ : syracuseStep 192443 = 288665) B288665
theorem B290747 : Blo 191804 290747 := bstep (se 1 (by rfl) ⟨218060, by rfl⟩ : syracuseStep 290747 = 436121) B436121
theorem B290807 : Blo 191804 290807 := bstep (se 1 (by rfl) ⟨218105, by rfl⟩ : syracuseStep 290807 = 436211) B436211
theorem B192519 : Blo 191804 192519 := bstep (se 1 (by rfl) ⟨144389, by rfl⟩ : syracuseStep 192519 = 288779) B288779
theorem B192527 : Blo 191804 192527 := bstep (se 1 (by rfl) ⟨144395, by rfl⟩ : syracuseStep 192527 = 288791) B288791
theorem B290831 : Blo 191804 290831 := bstep (se 1 (by rfl) ⟨218123, by rfl⟩ : syracuseStep 290831 = 436247) B436247
theorem B651293 : Blo 191804 651293 := bstep (se 3 (by rfl) ⟨122117, by rfl⟩ : syracuseStep 651293 = 244235) B244235
theorem B290873 : Blo 191804 290873 := bstep (se 2 (by rfl) ⟨109077, by rfl⟩ : syracuseStep 290873 = 218155) B218155
theorem B192571 : Blo 191804 192571 := bstep (se 1 (by rfl) ⟨144428, by rfl⟩ : syracuseStep 192571 = 288857) B288857
theorem B487559 : Blo 191804 487559 := bstep (se 1 (by rfl) ⟨365669, by rfl⟩ : syracuseStep 487559 = 731339) B731339
theorem B192647 : Blo 191804 192647 := bstep (se 1 (by rfl) ⟨144485, by rfl⟩ : syracuseStep 192647 = 288971) B288971
theorem B290951 : Blo 191804 290951 := bstep (se 1 (by rfl) ⟨218213, by rfl⟩ : syracuseStep 290951 = 436427) B436427
theorem B192655 : Blo 191804 192655 := bstep (se 1 (by rfl) ⟨144491, by rfl⟩ : syracuseStep 192655 = 288983) B288983
theorem B290987 : Blo 191804 290987 := bstep (se 1 (by rfl) ⟨218240, by rfl⟩ : syracuseStep 290987 = 436481) B436481
theorem B192699 : Blo 191804 192699 := bstep (se 1 (by rfl) ⟨144524, by rfl⟩ : syracuseStep 192699 = 289049) B289049
theorem B585929 : Blo 191804 585929 := bstep (se 2 (by rfl) ⟨219723, by rfl⟩ : syracuseStep 585929 = 439447) B439447
theorem B291017 : Blo 191804 291017 := bstep (se 2 (by rfl) ⟨109131, by rfl⟩ : syracuseStep 291017 = 218263) B218263
theorem B192775 : Blo 191804 192775 := bstep (se 1 (by rfl) ⟨144581, by rfl⟩ : syracuseStep 192775 = 289163) B289163
theorem B487691 : Blo 191804 487691 := bstep (se 1 (by rfl) ⟨365768, by rfl⟩ : syracuseStep 487691 = 731537) B731537
theorem B192783 : Blo 191804 192783 := bstep (se 1 (by rfl) ⟨144587, by rfl⟩ : syracuseStep 192783 = 289175) B289175
theorem B192827 : Blo 191804 192827 := bstep (se 1 (by rfl) ⟨144620, by rfl⟩ : syracuseStep 192827 = 289241) B289241
theorem B291131 : Blo 191804 291131 := bstep (se 1 (by rfl) ⟨218348, by rfl⟩ : syracuseStep 291131 = 436697) B436697
theorem B979289 : Blo 191804 979289 := bstep (se 2 (by rfl) ⟨367233, by rfl⟩ : syracuseStep 979289 = 734467) B734467
theorem B323959 : Blo 191804 323959 := bstep (se 1 (by rfl) ⟨242969, by rfl⟩ : syracuseStep 323959 = 485939) B485939
theorem B291191 : Blo 191804 291191 := bstep (se 1 (by rfl) ⟨218393, by rfl⟩ : syracuseStep 291191 = 436787) B436787
theorem B192903 : Blo 191804 192903 := bstep (se 1 (by rfl) ⟨144677, by rfl⟩ : syracuseStep 192903 = 289355) B289355
theorem B618887 : Blo 191804 618887 := bstep (se 1 (by rfl) ⟨464165, by rfl⟩ : syracuseStep 618887 = 928331) B928331
theorem B192911 : Blo 191804 192911 := bstep (se 1 (by rfl) ⟨144683, by rfl⟩ : syracuseStep 192911 = 289367) B289367
theorem B291215 : Blo 191804 291215 := bstep (se 1 (by rfl) ⟨218411, by rfl⟩ : syracuseStep 291215 = 436823) B436823
theorem B291257 : Blo 191804 291257 := bstep (se 2 (by rfl) ⟨109221, by rfl⟩ : syracuseStep 291257 = 218443) B218443
theorem B192955 : Blo 191804 192955 := bstep (se 1 (by rfl) ⟨144716, by rfl⟩ : syracuseStep 192955 = 289433) B289433
theorem B1667587 : Blo 191804 1667587 := bstep (se 1 (by rfl) ⟨1250690, by rfl⟩ : syracuseStep 1667587 = 2501381) B2501381
theorem B193031 : Blo 191804 193031 := bstep (se 1 (by rfl) ⟨144773, by rfl⟩ : syracuseStep 193031 = 289547) B289547
theorem B291335 : Blo 191804 291335 := bstep (se 1 (by rfl) ⟨218501, by rfl⟩ : syracuseStep 291335 = 437003) B437003
theorem B193039 : Blo 191804 193039 := bstep (se 1 (by rfl) ⟨144779, by rfl⟩ : syracuseStep 193039 = 289559) B289559
theorem B291371 : Blo 191804 291371 := bstep (se 1 (by rfl) ⟨218528, by rfl⟩ : syracuseStep 291371 = 437057) B437057
theorem B324155 : Blo 191804 324155 := bstep (se 1 (by rfl) ⟨243116, by rfl⟩ : syracuseStep 324155 = 486233) B486233
theorem B193083 : Blo 191804 193083 := bstep (se 1 (by rfl) ⟨144812, by rfl⟩ : syracuseStep 193083 = 289625) B289625
theorem B291401 : Blo 191804 291401 := bstep (se 2 (by rfl) ⟨109275, by rfl⟩ : syracuseStep 291401 = 218551) B218551
theorem B193159 : Blo 191804 193159 := bstep (se 1 (by rfl) ⟨144869, by rfl⟩ : syracuseStep 193159 = 289739) B289739
theorem B193167 : Blo 191804 193167 := bstep (se 1 (by rfl) ⟨144875, by rfl⟩ : syracuseStep 193167 = 289751) B289751
theorem B193211 : Blo 191804 193211 := bstep (se 1 (by rfl) ⟨144908, by rfl⟩ : syracuseStep 193211 = 289817) B289817
theorem B291515 : Blo 191804 291515 := bstep (se 1 (by rfl) ⟨218636, by rfl⟩ : syracuseStep 291515 = 437273) B437273
theorem B291575 : Blo 191804 291575 := bstep (se 1 (by rfl) ⟨218681, by rfl⟩ : syracuseStep 291575 = 437363) B437363
theorem B193287 : Blo 191804 193287 := bstep (se 1 (by rfl) ⟨144965, by rfl⟩ : syracuseStep 193287 = 289931) B289931
theorem B488207 : Blo 191804 488207 := bstep (se 1 (by rfl) ⟨366155, by rfl⟩ : syracuseStep 488207 = 732311) B732311
theorem B193295 : Blo 191804 193295 := bstep (se 1 (by rfl) ⟨144971, by rfl⟩ : syracuseStep 193295 = 289943) B289943
theorem B291599 : Blo 191804 291599 := bstep (se 1 (by rfl) ⟨218699, by rfl⟩ : syracuseStep 291599 = 437399) B437399
theorem B291641 : Blo 191804 291641 := bstep (se 2 (by rfl) ⟨109365, by rfl⟩ : syracuseStep 291641 = 218731) B218731
theorem B389947 : Blo 191804 389947 := bstep (se 1 (by rfl) ⟨292460, by rfl⟩ : syracuseStep 389947 = 584921) B584921
theorem B193339 : Blo 191804 193339 := bstep (se 1 (by rfl) ⟨145004, by rfl⟩ : syracuseStep 193339 = 290009) B290009
theorem B193415 : Blo 191804 193415 := bstep (se 1 (by rfl) ⟨145061, by rfl⟩ : syracuseStep 193415 = 290123) B290123
theorem B291719 : Blo 191804 291719 := bstep (se 1 (by rfl) ⟨218789, by rfl⟩ : syracuseStep 291719 = 437579) B437579
theorem B193423 : Blo 191804 193423 := bstep (se 1 (by rfl) ⟨145067, by rfl⟩ : syracuseStep 193423 = 290135) B290135
theorem B488339 : Blo 191804 488339 := bstep (se 1 (by rfl) ⟨366254, by rfl⟩ : syracuseStep 488339 = 732509) B732509
theorem B291755 : Blo 191804 291755 := bstep (se 1 (by rfl) ⟨218816, by rfl⟩ : syracuseStep 291755 = 437633) B437633
theorem B193467 : Blo 191804 193467 := bstep (se 1 (by rfl) ⟨145100, by rfl⟩ : syracuseStep 193467 = 290201) B290201
theorem B324553 : Blo 191804 324553 := bstep (se 2 (by rfl) ⟨121707, by rfl⟩ : syracuseStep 324553 = 243415) B243415
theorem B291785 : Blo 191804 291785 := bstep (se 2 (by rfl) ⟨109419, by rfl⟩ : syracuseStep 291785 = 218839) B218839
theorem B193543 : Blo 191804 193543 := bstep (se 1 (by rfl) ⟨145157, by rfl⟩ : syracuseStep 193543 = 290315) B290315
theorem B193551 : Blo 191804 193551 := bstep (se 1 (by rfl) ⟨145163, by rfl⟩ : syracuseStep 193551 = 290327) B290327
theorem B193595 : Blo 191804 193595 := bstep (se 1 (by rfl) ⟨145196, by rfl⟩ : syracuseStep 193595 = 290393) B290393
theorem B291899 : Blo 191804 291899 := bstep (se 1 (by rfl) ⟨218924, by rfl⟩ : syracuseStep 291899 = 437849) B437849
theorem B291959 : Blo 191804 291959 := bstep (se 1 (by rfl) ⟨218969, by rfl⟩ : syracuseStep 291959 = 437939) B437939
theorem B193671 : Blo 191804 193671 := bstep (se 1 (by rfl) ⟨145253, by rfl⟩ : syracuseStep 193671 = 290507) B290507
theorem B193679 : Blo 191804 193679 := bstep (se 1 (by rfl) ⟨145259, by rfl⟩ : syracuseStep 193679 = 290519) B290519
theorem B291983 : Blo 191804 291983 := bstep (se 1 (by rfl) ⟨218987, by rfl⟩ : syracuseStep 291983 = 437975) B437975
theorem B554131 : Blo 191804 554131 := bstep (se 1 (by rfl) ⟨415598, by rfl⟩ : syracuseStep 554131 = 831197) B831197
theorem B292025 : Blo 191804 292025 := bstep (se 2 (by rfl) ⟨109509, by rfl⟩ : syracuseStep 292025 = 219019) B219019
theorem B193723 : Blo 191804 193723 := bstep (se 1 (by rfl) ⟨145292, by rfl⟩ : syracuseStep 193723 = 290585) B290585
theorem B2094281 : Blo 191804 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B193799 : Blo 191804 193799 := bstep (se 1 (by rfl) ⟨145349, by rfl⟩ : syracuseStep 193799 = 290699) B290699
theorem B292103 : Blo 191804 292103 := bstep (se 1 (by rfl) ⟨219077, by rfl⟩ : syracuseStep 292103 = 438155) B438155
theorem B193807 : Blo 191804 193807 := bstep (se 1 (by rfl) ⟨145355, by rfl⟩ : syracuseStep 193807 = 290711) B290711
theorem B1176869 : Blo 191804 1176869 := bstep (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) B220663
theorem B292139 : Blo 191804 292139 := bstep (se 1 (by rfl) ⟨219104, by rfl⟩ : syracuseStep 292139 = 438209) B438209
theorem B193851 : Blo 191804 193851 := bstep (se 1 (by rfl) ⟨145388, by rfl⟩ : syracuseStep 193851 = 290777) B290777
theorem B292169 : Blo 191804 292169 := bstep (se 2 (by rfl) ⟨109563, by rfl⟩ : syracuseStep 292169 = 219127) B219127
theorem B554359 : Blo 191804 554359 := bstep (se 1 (by rfl) ⟨415769, by rfl⟩ : syracuseStep 554359 = 831539) B831539
theorem B193927 : Blo 191804 193927 := bstep (se 1 (by rfl) ⟨145445, by rfl⟩ : syracuseStep 193927 = 290891) B290891
theorem B193935 : Blo 191804 193935 := bstep (se 1 (by rfl) ⟨145451, by rfl⟩ : syracuseStep 193935 = 290903) B290903
theorem B652697 : Blo 191804 652697 := bstep (se 2 (by rfl) ⟨244761, by rfl⟩ : syracuseStep 652697 = 489523) B489523
theorem B193979 : Blo 191804 193979 := bstep (se 1 (by rfl) ⟨145484, by rfl⟩ : syracuseStep 193979 = 290969) B290969
theorem B292283 : Blo 191804 292283 := bstep (se 1 (by rfl) ⟨219212, by rfl⟩ : syracuseStep 292283 = 438425) B438425
theorem B292343 : Blo 191804 292343 := bstep (se 1 (by rfl) ⟨219257, by rfl⟩ : syracuseStep 292343 = 438515) B438515
theorem B194055 : Blo 191804 194055 := bstep (se 1 (by rfl) ⟨145541, by rfl⟩ : syracuseStep 194055 = 291083) B291083
theorem B194063 : Blo 191804 194063 := bstep (se 1 (by rfl) ⟨145547, by rfl⟩ : syracuseStep 194063 = 291095) B291095
theorem B292367 : Blo 191804 292367 := bstep (se 1 (by rfl) ⟨219275, by rfl⟩ : syracuseStep 292367 = 438551) B438551
theorem B292409 : Blo 191804 292409 := bstep (se 2 (by rfl) ⟨109653, by rfl⟩ : syracuseStep 292409 = 219307) B219307
theorem B194107 : Blo 191804 194107 := bstep (se 1 (by rfl) ⟨145580, by rfl⟩ : syracuseStep 194107 = 291161) B291161
theorem B325255 : Blo 191804 325255 := bstep (se 1 (by rfl) ⟨243941, by rfl⟩ : syracuseStep 325255 = 487883) B487883
theorem B194183 : Blo 191804 194183 := bstep (se 1 (by rfl) ⟨145637, by rfl⟩ : syracuseStep 194183 = 291275) B291275
theorem B292487 : Blo 191804 292487 := bstep (se 1 (by rfl) ⟨219365, by rfl⟩ : syracuseStep 292487 = 438731) B438731
theorem B194191 : Blo 191804 194191 := bstep (se 1 (by rfl) ⟨145643, by rfl⟩ : syracuseStep 194191 = 291287) B291287
theorem B292523 : Blo 191804 292523 := bstep (se 1 (by rfl) ⟨219392, by rfl⟩ : syracuseStep 292523 = 438785) B438785
theorem B587449 : Blo 191804 587449 := bstep (se 2 (by rfl) ⟨220293, by rfl⟩ : syracuseStep 587449 = 440587) B440587
theorem B194235 : Blo 191804 194235 := bstep (se 1 (by rfl) ⟨145676, by rfl⟩ : syracuseStep 194235 = 291353) B291353
theorem B292553 : Blo 191804 292553 := bstep (se 2 (by rfl) ⟨109707, by rfl⟩ : syracuseStep 292553 = 219415) B219415
theorem B194311 : Blo 191804 194311 := bstep (se 1 (by rfl) ⟨145733, by rfl⟩ : syracuseStep 194311 = 291467) B291467
theorem B194319 : Blo 191804 194319 := bstep (se 1 (by rfl) ⟨145739, by rfl⟩ : syracuseStep 194319 = 291479) B291479
theorem B194363 : Blo 191804 194363 := bstep (se 1 (by rfl) ⟨145772, by rfl⟩ : syracuseStep 194363 = 291545) B291545
theorem B292667 : Blo 191804 292667 := bstep (se 1 (by rfl) ⟨219500, by rfl⟩ : syracuseStep 292667 = 439001) B439001
theorem B292727 : Blo 191804 292727 := bstep (se 1 (by rfl) ⟨219545, by rfl⟩ : syracuseStep 292727 = 439091) B439091
theorem B194439 : Blo 191804 194439 := bstep (se 1 (by rfl) ⟨145829, by rfl⟩ : syracuseStep 194439 = 291659) B291659
theorem B194447 : Blo 191804 194447 := bstep (se 1 (by rfl) ⟨145835, by rfl⟩ : syracuseStep 194447 = 291671) B291671
theorem B292751 : Blo 191804 292751 := bstep (se 1 (by rfl) ⟨219563, by rfl⟩ : syracuseStep 292751 = 439127) B439127
theorem B292793 : Blo 191804 292793 := bstep (se 2 (by rfl) ⟨109797, by rfl⟩ : syracuseStep 292793 = 219595) B219595
theorem B194491 : Blo 191804 194491 := bstep (se 1 (by rfl) ⟨145868, by rfl⟩ : syracuseStep 194491 = 291737) B291737
theorem B489473 : Blo 191804 489473 := bstep (se 2 (by rfl) ⟨183552, by rfl⟩ : syracuseStep 489473 = 367105) B367105
theorem B194567 : Blo 191804 194567 := bstep (se 1 (by rfl) ⟨145925, by rfl⟩ : syracuseStep 194567 = 291851) B291851
theorem B292871 : Blo 191804 292871 := bstep (se 1 (by rfl) ⟨219653, by rfl⟩ : syracuseStep 292871 = 439307) B439307
theorem B292879 : Blo 191804 292879 := bstep (se 1 (by rfl) ⟨219659, by rfl⟩ : syracuseStep 292879 = 439319) B439319
theorem B194575 : Blo 191804 194575 := bstep (se 1 (by rfl) ⟨145931, by rfl⟩ : syracuseStep 194575 = 291863) B291863
theorem B292907 : Blo 191804 292907 := bstep (se 1 (by rfl) ⟨219680, by rfl⟩ : syracuseStep 292907 = 439361) B439361
theorem B194619 : Blo 191804 194619 := bstep (se 1 (by rfl) ⟨145964, by rfl⟩ : syracuseStep 194619 = 291929) B291929
theorem B292937 : Blo 191804 292937 := bstep (se 2 (by rfl) ⟨109851, by rfl⟩ : syracuseStep 292937 = 219703) B219703
theorem B653399 : Blo 191804 653399 := bstep (se 1 (by rfl) ⟨490049, by rfl⟩ : syracuseStep 653399 = 980099) B980099
theorem B2652277 : Blo 191804 2652277 := bstep (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) B248651
theorem B194695 : Blo 191804 194695 := bstep (se 1 (by rfl) ⟨146021, by rfl⟩ : syracuseStep 194695 = 292043) B292043
theorem B194703 : Blo 191804 194703 := bstep (se 1 (by rfl) ⟨146027, by rfl⟩ : syracuseStep 194703 = 292055) B292055
theorem B194747 : Blo 191804 194747 := bstep (se 1 (by rfl) ⟨146060, by rfl⟩ : syracuseStep 194747 = 292121) B292121
theorem B293051 : Blo 191804 293051 := bstep (se 1 (by rfl) ⟨219788, by rfl⟩ : syracuseStep 293051 = 439577) B439577
theorem B293111 : Blo 191804 293111 := bstep (se 1 (by rfl) ⟨219833, by rfl⟩ : syracuseStep 293111 = 439667) B439667
theorem B194823 : Blo 191804 194823 := bstep (se 1 (by rfl) ⟨146117, by rfl⟩ : syracuseStep 194823 = 292235) B292235
theorem B325903 : Blo 191804 325903 := bstep (se 1 (by rfl) ⟨244427, by rfl⟩ : syracuseStep 325903 = 488855) B488855
theorem B194831 : Blo 191804 194831 := bstep (se 1 (by rfl) ⟨146123, by rfl⟩ : syracuseStep 194831 = 292247) B292247
theorem B293135 : Blo 191804 293135 := bstep (se 1 (by rfl) ⟨219851, by rfl⟩ : syracuseStep 293135 = 439703) B439703
theorem B293177 : Blo 191804 293177 := bstep (se 2 (by rfl) ⟨109941, by rfl⟩ : syracuseStep 293177 = 219883) B219883
theorem B194875 : Blo 191804 194875 := bstep (se 1 (by rfl) ⟨146156, by rfl⟩ : syracuseStep 194875 = 292313) B292313
theorem B489847 : Blo 191804 489847 := bstep (se 1 (by rfl) ⟨367385, by rfl⟩ : syracuseStep 489847 = 734771) B734771
theorem B194951 : Blo 191804 194951 := bstep (se 1 (by rfl) ⟨146213, by rfl⟩ : syracuseStep 194951 = 292427) B292427
theorem B293255 : Blo 191804 293255 := bstep (se 1 (by rfl) ⟨219941, by rfl⟩ : syracuseStep 293255 = 439883) B439883
theorem B194959 : Blo 191804 194959 := bstep (se 1 (by rfl) ⟨146219, by rfl⟩ : syracuseStep 194959 = 292439) B292439
theorem B981395 : Blo 191804 981395 := bstep (se 1 (by rfl) ⟨736046, by rfl⟩ : syracuseStep 981395 = 1472093) B1472093
theorem B293291 : Blo 191804 293291 := bstep (se 1 (by rfl) ⟨219968, by rfl⟩ : syracuseStep 293291 = 439937) B439937
theorem B195003 : Blo 191804 195003 := bstep (se 1 (by rfl) ⟨146252, by rfl⟩ : syracuseStep 195003 = 292505) B292505
theorem B293321 : Blo 191804 293321 := bstep (se 2 (by rfl) ⟨109995, by rfl⟩ : syracuseStep 293321 = 219991) B219991
theorem B195079 : Blo 191804 195079 := bstep (se 1 (by rfl) ⟨146309, by rfl⟩ : syracuseStep 195079 = 292619) B292619
theorem B621067 : Blo 191804 621067 := bstep (se 1 (by rfl) ⟨465800, by rfl⟩ : syracuseStep 621067 = 931601) B931601
theorem B195087 : Blo 191804 195087 := bstep (se 1 (by rfl) ⟨146315, by rfl⟩ : syracuseStep 195087 = 292631) B292631
theorem B195131 : Blo 191804 195131 := bstep (se 1 (by rfl) ⟨146348, by rfl⟩ : syracuseStep 195131 = 292697) B292697
theorem B293435 : Blo 191804 293435 := bstep (se 1 (by rfl) ⟨220076, by rfl⟩ : syracuseStep 293435 = 440153) B440153
theorem B653885 : Blo 191804 653885 := bstep (se 3 (by rfl) ⟨122603, by rfl⟩ : syracuseStep 653885 = 245207) B245207
theorem B555635 : Blo 191804 555635 := bstep (se 1 (by rfl) ⟨416726, by rfl⟩ : syracuseStep 555635 = 833453) B833453
theorem B293495 : Blo 191804 293495 := bstep (se 1 (by rfl) ⟨220121, by rfl⟩ : syracuseStep 293495 = 440243) B440243
theorem B195207 : Blo 191804 195207 := bstep (se 1 (by rfl) ⟨146405, by rfl⟩ : syracuseStep 195207 = 292811) B292811
theorem B195215 : Blo 191804 195215 := bstep (se 1 (by rfl) ⟨146411, by rfl⟩ : syracuseStep 195215 = 292823) B292823
theorem B293519 : Blo 191804 293519 := bstep (se 1 (by rfl) ⟨220139, by rfl⟩ : syracuseStep 293519 = 440279) B440279
theorem B293561 : Blo 191804 293561 := bstep (se 2 (by rfl) ⟨110085, by rfl⟩ : syracuseStep 293561 = 220171) B220171
theorem B195259 : Blo 191804 195259 := bstep (se 1 (by rfl) ⟨146444, by rfl⟩ : syracuseStep 195259 = 292889) B292889
theorem B195335 : Blo 191804 195335 := bstep (se 1 (by rfl) ⟨146501, by rfl⟩ : syracuseStep 195335 = 293003) B293003
theorem B293639 : Blo 191804 293639 := bstep (se 1 (by rfl) ⟨220229, by rfl⟩ : syracuseStep 293639 = 440459) B440459
theorem B195343 : Blo 191804 195343 := bstep (se 1 (by rfl) ⟨146507, by rfl⟩ : syracuseStep 195343 = 293015) B293015
theorem B326443 : Blo 191804 326443 := bstep (se 1 (by rfl) ⟨244832, by rfl⟩ : syracuseStep 326443 = 489665) B489665
theorem B490283 : Blo 191804 490283 := bstep (se 1 (by rfl) ⟨367712, by rfl⟩ : syracuseStep 490283 = 735425) B735425
theorem B293675 : Blo 191804 293675 := bstep (se 1 (by rfl) ⟨220256, by rfl⟩ : syracuseStep 293675 = 440513) B440513
theorem B260921 : Blo 191804 260921 := bstep (se 2 (by rfl) ⟨97845, by rfl⟩ : syracuseStep 260921 = 195691) B195691
theorem B195387 : Blo 191804 195387 := bstep (se 1 (by rfl) ⟨146540, by rfl⟩ : syracuseStep 195387 = 293081) B293081
theorem B293705 : Blo 191804 293705 := bstep (se 2 (by rfl) ⟨110139, by rfl⟩ : syracuseStep 293705 = 220279) B220279
theorem B195463 : Blo 191804 195463 := bstep (se 1 (by rfl) ⟨146597, by rfl⟩ : syracuseStep 195463 = 293195) B293195
theorem B195471 : Blo 191804 195471 := bstep (se 1 (by rfl) ⟨146603, by rfl⟩ : syracuseStep 195471 = 293207) B293207
theorem B326585 : Blo 191804 326585 := bstep (se 2 (by rfl) ⟨122469, by rfl⟩ : syracuseStep 326585 = 244939) B244939
theorem B195515 : Blo 191804 195515 := bstep (se 1 (by rfl) ⟨146636, by rfl⟩ : syracuseStep 195515 = 293273) B293273
theorem B555977 : Blo 191804 555977 := bstep (se 2 (by rfl) ⟨208491, by rfl⟩ : syracuseStep 555977 = 416983) B416983
theorem B195591 : Blo 191804 195591 := bstep (se 1 (by rfl) ⟨146693, by rfl⟩ : syracuseStep 195591 = 293387) B293387
theorem B195599 : Blo 191804 195599 := bstep (se 1 (by rfl) ⟨146699, by rfl⟩ : syracuseStep 195599 = 293399) B293399
theorem B556091 : Blo 191804 556091 := bstep (se 1 (by rfl) ⟨417068, by rfl⟩ : syracuseStep 556091 = 834137) B834137
theorem B195643 : Blo 191804 195643 := bstep (se 1 (by rfl) ⟨146732, by rfl⟩ : syracuseStep 195643 = 293465) B293465
theorem B195719 : Blo 191804 195719 := bstep (se 1 (by rfl) ⟨146789, by rfl⟩ : syracuseStep 195719 = 293579) B293579
theorem B195727 : Blo 191804 195727 := bstep (se 1 (by rfl) ⟨146795, by rfl⟩ : syracuseStep 195727 = 293591) B293591
theorem B556217 : Blo 191804 556217 := bstep (se 2 (by rfl) ⟨208581, by rfl⟩ : syracuseStep 556217 = 417163) B417163
theorem B195771 : Blo 191804 195771 := bstep (se 1 (by rfl) ⟨146828, by rfl⟩ : syracuseStep 195771 = 293657) B293657
theorem B1047923 : Blo 191804 1047923 := bstep (se 1 (by rfl) ⟨785942, by rfl⟩ : syracuseStep 1047923 = 1571885) B1571885
theorem B1113547 : Blo 191804 1113547 := bstep (se 1 (by rfl) ⟨835160, by rfl⟩ : syracuseStep 1113547 = 1670321) B1670321
theorem B491123 : Blo 191804 491123 := bstep (se 1 (by rfl) ⟨368342, by rfl⟩ : syracuseStep 491123 = 736685) B736685
theorem B327287 : Blo 191804 327287 := bstep (se 1 (by rfl) ⟨245465, by rfl⟩ : syracuseStep 327287 = 490931) B490931
theorem B491143 : Blo 191804 491143 := bstep (se 1 (by rfl) ⟨368357, by rfl⟩ : syracuseStep 491143 = 736715) B736715
theorem B2490263 : Blo 191804 2490263 := bstep (se 1 (by rfl) ⟨1867697, by rfl⟩ : syracuseStep 2490263 = 3735395) B3735395
theorem B2097049 : Blo 191804 2097049 := bstep (se 2 (by rfl) ⟨786393, by rfl⟩ : syracuseStep 2097049 = 1572787) B1572787
theorem B491417 : Blo 191804 491417 := bstep (se 2 (by rfl) ⟨184281, by rfl⟩ : syracuseStep 491417 = 368563) B368563
theorem B4751257 : Blo 191804 4751257 := bstep (se 2 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 4751257 = 3563443) B3563443
theorem B655289 : Blo 191804 655289 := bstep (se 2 (by rfl) ⟨245733, by rfl⟩ : syracuseStep 655289 = 491467) B491467
theorem B5898269 : Blo 191804 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B327719 : Blo 191804 327719 := bstep (se 1 (by rfl) ⟨245789, by rfl⟩ : syracuseStep 327719 = 491579) B491579
theorem B328009 : Blo 191804 328009 := bstep (se 2 (by rfl) ⟨123003, by rfl⟩ : syracuseStep 328009 = 246007) B246007
theorem B655721 : Blo 191804 655721 := bstep (se 2 (by rfl) ⟨245895, by rfl⟩ : syracuseStep 655721 = 491791) B491791
theorem B328043 : Blo 191804 328043 := bstep (se 1 (by rfl) ⟨246032, by rfl⟩ : syracuseStep 328043 = 492065) B492065
theorem B295433 : Blo 191804 295433 := bstep (se 2 (by rfl) ⟨110787, by rfl⟩ : syracuseStep 295433 = 221575) B221575
theorem B328441 : Blo 191804 328441 := bstep (se 2 (by rfl) ⟨123165, by rfl⟩ : syracuseStep 328441 = 246331) B246331
theorem B197471 : Blo 191804 197471 := bstep (se 1 (by rfl) ⟨148103, by rfl⟩ : syracuseStep 197471 = 296207) B296207
theorem B656315 : Blo 191804 656315 := bstep (se 1 (by rfl) ⟨492236, by rfl⟩ : syracuseStep 656315 = 984473) B984473
theorem B328711 : Blo 191804 328711 := bstep (se 1 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 328711 = 493067) B493067
theorem B492551 : Blo 191804 492551 := bstep (se 1 (by rfl) ⟨369413, by rfl⟩ : syracuseStep 492551 = 738827) B738827
theorem B5309489 : Blo 191804 5309489 := bstep (se 2 (by rfl) ⟨1991058, by rfl⟩ : syracuseStep 5309489 = 3982117) B3982117
theorem B492601 : Blo 191804 492601 := bstep (se 2 (by rfl) ⟨184725, by rfl⟩ : syracuseStep 492601 = 369451) B369451
theorem B984311 : Blo 191804 984311 := bstep (se 1 (by rfl) ⟨738233, by rfl⟩ : syracuseStep 984311 = 1476467) B1476467
theorem B591209 : Blo 191804 591209 := bstep (se 2 (by rfl) ⟨221703, by rfl⟩ : syracuseStep 591209 = 443407) B443407
theorem B492905 : Blo 191804 492905 := bstep (se 2 (by rfl) ⟨184839, by rfl⟩ : syracuseStep 492905 = 369679) B369679
theorem B329143 : Blo 191804 329143 := bstep (se 1 (by rfl) ⟨246857, by rfl⟩ : syracuseStep 329143 = 493715) B493715
theorem B1181147 : Blo 191804 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B624115 : Blo 191804 624115 := bstep (se 1 (by rfl) ⟨468086, by rfl⟩ : syracuseStep 624115 = 936173) B936173
theorem B1410547 : Blo 191804 1410547 := bstep (se 1 (by rfl) ⟨1057910, by rfl⟩ : syracuseStep 1410547 = 2115821) B2115821
theorem B329339 : Blo 191804 329339 := bstep (se 1 (by rfl) ⟨247004, by rfl⟩ : syracuseStep 329339 = 494009) B494009
theorem B984797 : Blo 191804 984797 := bstep (se 3 (by rfl) ⟨184649, by rfl⟩ : syracuseStep 984797 = 369299) B369299
theorem B329737 : Blo 191804 329737 := bstep (se 2 (by rfl) ⟨123651, by rfl⟩ : syracuseStep 329737 = 247303) B247303
theorem B329899 : Blo 191804 329899 := bstep (se 1 (by rfl) ⟨247424, by rfl⟩ : syracuseStep 329899 = 494849) B494849
theorem B264553 : Blo 191804 264553 := bstep (se 2 (by rfl) ⟨99207, by rfl⟩ : syracuseStep 264553 = 198415) B198415
theorem B395695 : Blo 191804 395695 := bstep (se 1 (by rfl) ⟨296771, by rfl⟩ : syracuseStep 395695 = 593543) B593543
theorem B330203 : Blo 191804 330203 := bstep (se 1 (by rfl) ⟨247652, by rfl⟩ : syracuseStep 330203 = 495305) B495305
theorem B526945 : Blo 191804 526945 := bstep (se 2 (by rfl) ⟨197604, by rfl⟩ : syracuseStep 526945 = 395209) B395209
theorem B658043 : Blo 191804 658043 := bstep (se 1 (by rfl) ⟨493532, by rfl⟩ : syracuseStep 658043 = 987065) B987065
theorem B658205 : Blo 191804 658205 := bstep (se 3 (by rfl) ⟨123413, by rfl⟩ : syracuseStep 658205 = 246827) B246827
theorem B4950821 : Blo 191804 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B1870775 : Blo 191804 1870775 := bstep (se 1 (by rfl) ⟨1403081, by rfl⟩ : syracuseStep 1870775 = 2806163) B2806163
theorem B1477925 : Blo 191804 1477925 := bstep (se 4 (by rfl) ⟨138555, by rfl⟩ : syracuseStep 1477925 = 277111) B277111
theorem B658907 : Blo 191804 658907 := bstep (se 1 (by rfl) ⟨494180, by rfl⟩ : syracuseStep 658907 = 988361) B988361
theorem B495143 : Blo 191804 495143 := bstep (se 1 (by rfl) ⟨371357, by rfl⟩ : syracuseStep 495143 = 742715) B742715
theorem B495467 : Blo 191804 495467 := bstep (se 1 (by rfl) ⟨371600, by rfl⟩ : syracuseStep 495467 = 743201) B743201
theorem B692155 : Blo 191804 692155 := bstep (se 1 (by rfl) ⟨519116, by rfl⟩ : syracuseStep 692155 = 1038233) B1038233
theorem B200827 : Blo 191804 200827 := bstep (se 1 (by rfl) ⟨150620, by rfl⟩ : syracuseStep 200827 = 301241) B301241
theorem B659609 : Blo 191804 659609 := bstep (se 2 (by rfl) ⟨247353, by rfl⟩ : syracuseStep 659609 = 494707) B494707
theorem B626935 : Blo 191804 626935 := bstep (se 1 (by rfl) ⟨470201, by rfl⟩ : syracuseStep 626935 = 940403) B940403
theorem B1052939 : Blo 191804 1052939 := bstep (se 1 (by rfl) ⟨789704, by rfl⟩ : syracuseStep 1052939 = 1579409) B1579409
theorem B364895 : Blo 191804 364895 := bstep (se 1 (by rfl) ⟨273671, by rfl⟩ : syracuseStep 364895 = 547343) B547343
theorem B365305 : Blo 191804 365305 := bstep (se 2 (by rfl) ⟨136989, by rfl⟩ : syracuseStep 365305 = 273979) B273979
theorem B4166417 : Blo 191804 4166417 := bstep (se 2 (by rfl) ⟨1562406, by rfl⟩ : syracuseStep 4166417 = 3124813) B3124813
theorem B332651 : Blo 191804 332651 := bstep (se 1 (by rfl) ⟨249488, by rfl⟩ : syracuseStep 332651 = 498977) B498977
theorem B627643 : Blo 191804 627643 := bstep (se 1 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 627643 = 941465) B941465
theorem B3150899 : Blo 191804 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B365647 : Blo 191804 365647 := bstep (se 1 (by rfl) ⟨274235, by rfl⟩ : syracuseStep 365647 = 548471) B548471
theorem B660797 : Blo 191804 660797 := bstep (se 3 (by rfl) ⟨123899, by rfl⟩ : syracuseStep 660797 = 247799) B247799
theorem B365897 : Blo 191804 365897 := bstep (se 2 (by rfl) ⟨137211, by rfl⟩ : syracuseStep 365897 = 274423) B274423
theorem B595343 : Blo 191804 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B3315491 : Blo 191804 3315491 := bstep (se 1 (by rfl) ⟨2486618, by rfl⟩ : syracuseStep 3315491 = 4973237) B4973237
theorem B431945 : Blo 191804 431945 := bstep (se 2 (by rfl) ⟨161979, by rfl⟩ : syracuseStep 431945 = 323959) B323959
theorem B1185799 : Blo 191804 1185799 := bstep (se 1 (by rfl) ⟨889349, by rfl⟩ : syracuseStep 1185799 = 1778699) B1778699
theorem B1251409 : Blo 191804 1251409 := bstep (se 2 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 1251409 = 938557) B938557
theorem B366763 : Blo 191804 366763 := bstep (se 1 (by rfl) ⟨275072, by rfl⟩ : syracuseStep 366763 = 550145) B550145
theorem B366839 : Blo 191804 366839 := bstep (se 1 (by rfl) ⟨275129, by rfl⟩ : syracuseStep 366839 = 550259) B550259
theorem B465281 : Blo 191804 465281 := bstep (se 2 (by rfl) ⟨174480, by rfl⟩ : syracuseStep 465281 = 348961) B348961
theorem B367067 : Blo 191804 367067 := bstep (se 1 (by rfl) ⟨275300, by rfl⟩ : syracuseStep 367067 = 550601) B550601
theorem B498215 : Blo 191804 498215 := bstep (se 1 (by rfl) ⟨373661, by rfl⟩ : syracuseStep 498215 = 747323) B747323
theorem B432737 : Blo 191804 432737 := bstep (se 2 (by rfl) ⟨162276, by rfl⟩ : syracuseStep 432737 = 324553) B324553
theorem B793273 : Blo 191804 793273 := bstep (se 2 (by rfl) ⟨297477, by rfl⟩ : syracuseStep 793273 = 594955) B594955
theorem B989981 : Blo 191804 989981 := bstep (se 3 (by rfl) ⟨185621, by rfl⟩ : syracuseStep 989981 = 371243) B371243
theorem B433079 : Blo 191804 433079 := bstep (se 1 (by rfl) ⟨324809, by rfl⟩ : syracuseStep 433079 = 649619) B649619
theorem B1186987 : Blo 191804 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B4300121 : Blo 191804 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B466319 : Blo 191804 466319 := bstep (se 1 (by rfl) ⟨349739, by rfl⟩ : syracuseStep 466319 = 699479) B699479
theorem B695789 : Blo 191804 695789 := bstep (se 3 (by rfl) ⟨130460, by rfl⟩ : syracuseStep 695789 = 260921) B260921
theorem B433673 : Blo 191804 433673 := bstep (se 2 (by rfl) ⟨162627, by rfl⟩ : syracuseStep 433673 = 325255) B325255
theorem B728635 : Blo 191804 728635 := bstep (se 1 (by rfl) ⟨546476, by rfl⟩ : syracuseStep 728635 = 1092953) B1092953
theorem B368327 : Blo 191804 368327 := bstep (se 1 (by rfl) ⟨276245, by rfl⟩ : syracuseStep 368327 = 552491) B552491
theorem B434015 : Blo 191804 434015 := bstep (se 1 (by rfl) ⟨325511, by rfl⟩ : syracuseStep 434015 = 651023) B651023
theorem B368479 : Blo 191804 368479 := bstep (se 1 (by rfl) ⟨276359, by rfl⟩ : syracuseStep 368479 = 552719) B552719
theorem B728939 : Blo 191804 728939 := bstep (se 1 (by rfl) ⟨546704, by rfl⟩ : syracuseStep 728939 = 1093409) B1093409
theorem B5054393 : Blo 191804 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B729107 : Blo 191804 729107 := bstep (se 1 (by rfl) ⟨546830, by rfl⟩ : syracuseStep 729107 = 1093661) B1093661
theorem B434195 : Blo 191804 434195 := bstep (se 1 (by rfl) ⟨325646, by rfl⟩ : syracuseStep 434195 = 651293) B651293
theorem B205151 : Blo 191804 205151 := bstep (se 1 (by rfl) ⟨153863, by rfl⟩ : syracuseStep 205151 = 307727) B307727
theorem B434537 : Blo 191804 434537 := bstep (se 2 (by rfl) ⟨162951, by rfl⟩ : syracuseStep 434537 = 325903) B325903
theorem B828089 : Blo 191804 828089 := bstep (se 2 (by rfl) ⟨310533, by rfl⟩ : syracuseStep 828089 = 621067) B621067
theorem B500473 : Blo 191804 500473 := bstep (se 2 (by rfl) ⟨187677, by rfl⟩ : syracuseStep 500473 = 375355) B375355
theorem B1352477 : Blo 191804 1352477 := bstep (se 3 (by rfl) ⟨253589, by rfl⟩ : syracuseStep 1352477 = 507179) B507179
theorem B435131 : Blo 191804 435131 := bstep (se 1 (by rfl) ⟨326348, by rfl⟩ : syracuseStep 435131 = 652697) B652697
theorem B435257 : Blo 191804 435257 := bstep (se 2 (by rfl) ⟨163221, by rfl⟩ : syracuseStep 435257 = 326443) B326443
theorem B205903 : Blo 191804 205903 := bstep (se 1 (by rfl) ⟨154427, by rfl⟩ : syracuseStep 205903 = 308855) B308855
theorem B1058039 : Blo 191804 1058039 := bstep (se 1 (by rfl) ⟨793529, by rfl⟩ : syracuseStep 1058039 = 1587059) B1587059
theorem B927101 : Blo 191804 927101 := bstep (se 3 (by rfl) ⟨173831, by rfl⟩ : syracuseStep 927101 = 347663) B347663
theorem B435599 : Blo 191804 435599 := bstep (se 1 (by rfl) ⟨326699, by rfl⟩ : syracuseStep 435599 = 653399) B653399
theorem B435923 : Blo 191804 435923 := bstep (se 1 (by rfl) ⟨326942, by rfl⟩ : syracuseStep 435923 = 653885) B653885
theorem B370423 : Blo 191804 370423 := bstep (se 1 (by rfl) ⟨277817, by rfl⟩ : syracuseStep 370423 = 555635) B555635
theorem B1484729 : Blo 191804 1484729 := bstep (se 2 (by rfl) ⟨556773, by rfl⟩ : syracuseStep 1484729 = 1113547) B1113547
theorem B1451963 : Blo 191804 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B370651 : Blo 191804 370651 := bstep (se 1 (by rfl) ⟨277988, by rfl⟩ : syracuseStep 370651 = 555977) B555977
theorem B370727 : Blo 191804 370727 := bstep (se 1 (by rfl) ⟨278045, by rfl⟩ : syracuseStep 370727 = 556091) B556091
theorem B370811 : Blo 191804 370811 := bstep (se 1 (by rfl) ⟨278108, by rfl⟩ : syracuseStep 370811 = 556217) B556217
theorem B469163 : Blo 191804 469163 := bstep (se 1 (by rfl) ⟨351872, by rfl⟩ : syracuseStep 469163 = 703745) B703745
theorem B698615 : Blo 191804 698615 := bstep (se 1 (by rfl) ⟨523961, by rfl⟩ : syracuseStep 698615 = 1047923) B1047923
theorem B2205953 : Blo 191804 2205953 := bstep (se 2 (by rfl) ⟨827232, by rfl⟩ : syracuseStep 2205953 = 1654465) B1654465
theorem B2796065 : Blo 191804 2796065 := bstep (se 2 (by rfl) ⟨1048524, by rfl⟩ : syracuseStep 2796065 = 2097049) B2097049
theorem B6335009 : Blo 191804 6335009 := bstep (se 2 (by rfl) ⟨2375628, by rfl⟩ : syracuseStep 6335009 = 4751257) B4751257
theorem B371297 : Blo 191804 371297 := bstep (se 2 (by rfl) ⟨139236, by rfl⟩ : syracuseStep 371297 = 278473) B278473
theorem B436859 : Blo 191804 436859 := bstep (se 1 (by rfl) ⟨327644, by rfl⟩ : syracuseStep 436859 = 655289) B655289
theorem B436985 : Blo 191804 436985 := bstep (se 2 (by rfl) ⟨163869, by rfl⟩ : syracuseStep 436985 = 327739) B327739
theorem B1583945 : Blo 191804 1583945 := bstep (se 2 (by rfl) ⟨593979, by rfl⟩ : syracuseStep 1583945 = 1187959) B1187959
theorem B732023 : Blo 191804 732023 := bstep (se 1 (by rfl) ⟨549017, by rfl⟩ : syracuseStep 732023 = 1098035) B1098035
theorem B437255 : Blo 191804 437255 := bstep (se 1 (by rfl) ⟨327941, by rfl⟩ : syracuseStep 437255 = 655883) B655883
theorem B437327 : Blo 191804 437327 := bstep (se 1 (by rfl) ⟨327995, by rfl⟩ : syracuseStep 437327 = 655991) B655991
theorem B437723 : Blo 191804 437723 := bstep (se 1 (by rfl) ⟨328292, by rfl⟩ : syracuseStep 437723 = 656585) B656585
theorem B208423 : Blo 191804 208423 := bstep (se 1 (by rfl) ⟨156317, by rfl⟩ : syracuseStep 208423 = 312635) B312635
theorem B1388177 : Blo 191804 1388177 := bstep (se 2 (by rfl) ⟨520566, by rfl⟩ : syracuseStep 1388177 = 1041133) B1041133
theorem B1650365 : Blo 191804 1650365 := bstep (se 3 (by rfl) ⟨309443, by rfl⟩ : syracuseStep 1650365 = 618887) B618887
theorem B732995 : Blo 191804 732995 := bstep (se 1 (by rfl) ⟨549746, by rfl⟩ : syracuseStep 732995 = 1099493) B1099493
theorem B438191 : Blo 191804 438191 := bstep (se 1 (by rfl) ⟨328643, by rfl⟩ : syracuseStep 438191 = 657287) B657287
theorem B438443 : Blo 191804 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B438983 : Blo 191804 438983 := bstep (se 1 (by rfl) ⟨329237, by rfl⟩ : syracuseStep 438983 = 658475) B658475
theorem B733981 : Blo 191804 733981 := bstep (se 3 (by rfl) ⟨137621, by rfl⟩ : syracuseStep 733981 = 275243) B275243
theorem B602975 : Blo 191804 602975 := bstep (se 1 (by rfl) ⟨452231, by rfl⟩ : syracuseStep 602975 = 904463) B904463
theorem B1258415 : Blo 191804 1258415 := bstep (se 1 (by rfl) ⟨943811, by rfl⟩ : syracuseStep 1258415 = 1887623) B1887623
theorem B242767 : Blo 191804 242767 := bstep (se 1 (by rfl) ⟨182075, by rfl⟩ : syracuseStep 242767 = 364151) B364151
theorem B439847 : Blo 191804 439847 := bstep (se 1 (by rfl) ⟨329885, by rfl⟩ : syracuseStep 439847 = 659771) B659771
theorem B4667179 : Blo 191804 4667179 := bstep (se 1 (by rfl) ⟨3500384, by rfl⟩ : syracuseStep 4667179 = 7000769) B7000769
theorem B440171 : Blo 191804 440171 := bstep (se 1 (by rfl) ⟨330128, by rfl⟩ : syracuseStep 440171 = 660257) B660257
theorem B440225 : Blo 191804 440225 := bstep (se 2 (by rfl) ⟨165084, by rfl⟩ : syracuseStep 440225 = 330169) B330169
theorem B1652825 : Blo 191804 1652825 := bstep (se 2 (by rfl) ⟨619809, by rfl⟩ : syracuseStep 1652825 = 1239619) B1239619
theorem B243911 : Blo 191804 243911 := bstep (se 1 (by rfl) ⟨182933, by rfl⟩ : syracuseStep 243911 = 365867) B365867
theorem B244063 : Blo 191804 244063 := bstep (se 1 (by rfl) ⟨183047, by rfl⟩ : syracuseStep 244063 = 366095) B366095
theorem B7518905 : Blo 191804 7518905 := bstep (se 2 (by rfl) ⟨2819589, by rfl⟩ : syracuseStep 7518905 = 5639179) B5639179
theorem B2472677 : Blo 191804 2472677 := bstep (se 4 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 2472677 = 463627) B463627
theorem B311135 : Blo 191804 311135 := bstep (se 1 (by rfl) ⟨233351, by rfl⟩ : syracuseStep 311135 = 466703) B466703
theorem B704351 : Blo 191804 704351 := bstep (se 1 (by rfl) ⟨528263, by rfl⟩ : syracuseStep 704351 = 1056527) B1056527
theorem B311545 : Blo 191804 311545 := bstep (se 2 (by rfl) ⟨116829, by rfl⟩ : syracuseStep 311545 = 233659) B233659
theorem B409961 : Blo 191804 409961 := bstep (se 2 (by rfl) ⟨153735, by rfl⟩ : syracuseStep 409961 = 307471) B307471
theorem B246235 : Blo 191804 246235 := bstep (se 1 (by rfl) ⟨184676, by rfl⟩ : syracuseStep 246235 = 369353) B369353
theorem B312007 : Blo 191804 312007 := bstep (se 1 (by rfl) ⟨234005, by rfl⟩ : syracuseStep 312007 = 468011) B468011
theorem B738143 : Blo 191804 738143 := bstep (se 1 (by rfl) ⟨553607, by rfl⟩ : syracuseStep 738143 = 1107215) B1107215
theorem B3130265 : Blo 191804 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B312329 : Blo 191804 312329 := bstep (se 2 (by rfl) ⟨117123, by rfl⟩ : syracuseStep 312329 = 234247) B234247
theorem B738841 : Blo 191804 738841 := bstep (se 2 (by rfl) ⟨277065, by rfl⟩ : syracuseStep 738841 = 554131) B554131
theorem B411259 : Blo 191804 411259 := bstep (se 1 (by rfl) ⟨308444, by rfl⟩ : syracuseStep 411259 = 616889) B616889
theorem B739115 : Blo 191804 739115 := bstep (se 1 (by rfl) ⟨554336, by rfl⟩ : syracuseStep 739115 = 1108673) B1108673
theorem B739145 : Blo 191804 739145 := bstep (se 2 (by rfl) ⟨277179, by rfl⟩ : syracuseStep 739145 = 554359) B554359
theorem B1853279 : Blo 191804 1853279 := bstep (se 1 (by rfl) ⟨1389959, by rfl⟩ : syracuseStep 1853279 = 2779919) B2779919
theorem B39929699 : Blo 191804 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B346511 : Blo 191804 346511 := bstep (se 1 (by rfl) ⟨259883, by rfl⟩ : syracuseStep 346511 = 519767) B519767
theorem B936481 : Blo 191804 936481 := bstep (se 2 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 936481 = 702361) B702361
theorem B412199 : Blo 191804 412199 := bstep (se 1 (by rfl) ⟨309149, by rfl⟩ : syracuseStep 412199 = 618299) B618299
theorem B412489 : Blo 191804 412489 := bstep (se 2 (by rfl) ⟨154683, by rfl⟩ : syracuseStep 412489 = 309367) B309367
theorem B216103 : Blo 191804 216103 := bstep (se 1 (by rfl) ⟨162077, by rfl⟩ : syracuseStep 216103 = 324155) B324155
theorem B314407 : Blo 191804 314407 := bstep (se 1 (by rfl) ⟨235805, by rfl⟩ : syracuseStep 314407 = 471611) B471611
theorem B1461401 : Blo 191804 1461401 := bstep (se 2 (by rfl) ⟨548025, by rfl⟩ : syracuseStep 1461401 = 1096051) B1096051
theorem B314617 : Blo 191804 314617 := bstep (se 2 (by rfl) ⟨117981, by rfl⟩ : syracuseStep 314617 = 235963) B235963
theorem B1396187 : Blo 191804 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B413753 : Blo 191804 413753 := bstep (se 2 (by rfl) ⟨155157, by rfl⟩ : syracuseStep 413753 = 310315) B310315
theorem B741757 : Blo 191804 741757 := bstep (se 3 (by rfl) ⟨139079, by rfl⟩ : syracuseStep 741757 = 278159) B278159
theorem B217723 : Blo 191804 217723 := bstep (se 1 (by rfl) ⟨163292, by rfl⟩ : syracuseStep 217723 = 326585) B326585
theorem B2249693 : Blo 191804 2249693 := bstep (se 3 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 2249693 = 843635) B843635
theorem B1463345 : Blo 191804 1463345 := bstep (se 2 (by rfl) ⟨548754, by rfl⟩ : syracuseStep 1463345 = 1097509) B1097509
theorem B218191 : Blo 191804 218191 := bstep (se 1 (by rfl) ⟨163643, by rfl⟩ : syracuseStep 218191 = 327287) B327287
theorem B1660175 : Blo 191804 1660175 := bstep (se 1 (by rfl) ⟨1245131, by rfl⟩ : syracuseStep 1660175 = 2490263) B2490263
theorem B1856969 : Blo 191804 1856969 := bstep (se 2 (by rfl) ⟨696363, by rfl⟩ : syracuseStep 1856969 = 1392727) B1392727
theorem B218587 : Blo 191804 218587 := bstep (se 1 (by rfl) ⟨163940, by rfl⟩ : syracuseStep 218587 = 327881) B327881
theorem B2217617 : Blo 191804 2217617 := bstep (se 2 (by rfl) ⟨831606, by rfl⟩ : syracuseStep 2217617 = 1663213) B1663213
theorem B1037971 : Blo 191804 1037971 := bstep (se 1 (by rfl) ⟨778478, by rfl⟩ : syracuseStep 1037971 = 1556957) B1556957
theorem B350057 : Blo 191804 350057 := bstep (se 2 (by rfl) ⟨131271, by rfl⟩ : syracuseStep 350057 = 262543) B262543
theorem B219055 : Blo 191804 219055 := bstep (se 1 (by rfl) ⟨164291, by rfl⟩ : syracuseStep 219055 = 328583) B328583
theorem B22763477 : Blo 191804 22763477 := bstep (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) B533519
theorem B219487 : Blo 191804 219487 := bstep (se 1 (by rfl) ⟨164615, by rfl⟩ : syracuseStep 219487 = 329231) B329231
theorem B219847 : Blo 191804 219847 := bstep (se 1 (by rfl) ⟨164885, by rfl⟩ : syracuseStep 219847 = 329771) B329771
theorem B2218697 : Blo 191804 2218697 := bstep (se 2 (by rfl) ⟨832011, by rfl⟩ : syracuseStep 2218697 = 1664023) B1664023
theorem B1105325 : Blo 191804 1105325 := bstep (se 3 (by rfl) ⟨207248, by rfl⟩ : syracuseStep 1105325 = 414497) B414497
theorem B1334701 : Blo 191804 1334701 := bstep (se 3 (by rfl) ⟨250256, by rfl⟩ : syracuseStep 1334701 = 500513) B500513
theorem B2809565 : Blo 191804 2809565 := bstep (se 3 (by rfl) ⟨526793, by rfl⟩ : syracuseStep 2809565 = 1053587) B1053587
theorem B974753 : Blo 191804 974753 := bstep (se 2 (by rfl) ⟨365532, by rfl⟩ : syracuseStep 974753 = 731065) B731065
theorem B614479 : Blo 191804 614479 := bstep (se 1 (by rfl) ⟨460859, by rfl⟩ : syracuseStep 614479 = 921719) B921719
theorem B647567 : Blo 191804 647567 := bstep (se 1 (by rfl) ⟨485675, by rfl⟩ : syracuseStep 647567 = 971351) B971351
theorem B549575 : Blo 191804 549575 := bstep (se 1 (by rfl) ⟨412181, by rfl⟩ : syracuseStep 549575 = 824363) B824363
theorem B647891 : Blo 191804 647891 := bstep (se 1 (by rfl) ⟨485918, by rfl⟩ : syracuseStep 647891 = 971837) B971837
theorem B615197 : Blo 191804 615197 := bstep (se 3 (by rfl) ⟨115349, by rfl⟩ : syracuseStep 615197 = 230699) B230699
theorem B418655 : Blo 191804 418655 := bstep (se 1 (by rfl) ⟨313991, by rfl⟩ : syracuseStep 418655 = 627983) B627983
theorem B287753 : Blo 191804 287753 := bstep (se 2 (by rfl) ⟨107907, by rfl⟩ : syracuseStep 287753 = 215815) B215815
theorem B287783 : Blo 191804 287783 := bstep (se 1 (by rfl) ⟨215837, by rfl⟩ : syracuseStep 287783 = 431675) B431675
theorem B287867 : Blo 191804 287867 := bstep (se 1 (by rfl) ⟨215900, by rfl⟩ : syracuseStep 287867 = 431801) B431801
theorem B615595 : Blo 191804 615595 := bstep (se 1 (by rfl) ⟨461696, by rfl⟩ : syracuseStep 615595 = 923393) B923393
theorem B1664171 : Blo 191804 1664171 := bstep (se 1 (by rfl) ⟨1248128, by rfl⟩ : syracuseStep 1664171 = 2496257) B2496257
theorem B287993 : Blo 191804 287993 := bstep (se 2 (by rfl) ⟨107997, by rfl⟩ : syracuseStep 287993 = 215995) B215995
theorem B1238287 : Blo 191804 1238287 := bstep (se 1 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 1238287 = 1857431) B1857431
theorem B288095 : Blo 191804 288095 := bstep (se 1 (by rfl) ⟨216071, by rfl⟩ : syracuseStep 288095 = 432143) B432143
theorem B288107 : Blo 191804 288107 := bstep (se 1 (by rfl) ⟨216080, by rfl⟩ : syracuseStep 288107 = 432161) B432161
theorem B288335 : Blo 191804 288335 := bstep (se 1 (by rfl) ⟨216251, by rfl⟩ : syracuseStep 288335 = 432503) B432503
theorem B288455 : Blo 191804 288455 := bstep (se 1 (by rfl) ⟨216341, by rfl⟩ : syracuseStep 288455 = 432683) B432683
theorem B779975 : Blo 191804 779975 := bstep (se 1 (by rfl) ⟨584981, by rfl⟩ : syracuseStep 779975 = 1169963) B1169963
theorem B288617 : Blo 191804 288617 := bstep (se 2 (by rfl) ⟨108231, by rfl⟩ : syracuseStep 288617 = 216463) B216463
theorem B649079 : Blo 191804 649079 := bstep (se 1 (by rfl) ⟨486809, by rfl⟩ : syracuseStep 649079 = 973619) B973619
theorem B288695 : Blo 191804 288695 := bstep (se 1 (by rfl) ⟨216521, by rfl⟩ : syracuseStep 288695 = 433043) B433043
theorem B288731 : Blo 191804 288731 := bstep (se 1 (by rfl) ⟨216548, by rfl⟩ : syracuseStep 288731 = 433097) B433097
theorem B649295 : Blo 191804 649295 := bstep (se 1 (by rfl) ⟨486971, by rfl⟩ : syracuseStep 649295 = 973943) B973943
theorem B10152053 : Blo 191804 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B289199 : Blo 191804 289199 := bstep (se 1 (by rfl) ⟨216899, by rfl⟩ : syracuseStep 289199 = 433799) B433799
theorem B649673 : Blo 191804 649673 := bstep (se 2 (by rfl) ⟨243627, by rfl⟩ : syracuseStep 649673 = 487255) B487255
theorem B551387 : Blo 191804 551387 := bstep (se 1 (by rfl) ⟨413540, by rfl⟩ : syracuseStep 551387 = 827081) B827081
theorem B289289 : Blo 191804 289289 := bstep (se 2 (by rfl) ⟨108483, by rfl⟩ : syracuseStep 289289 = 216967) B216967
theorem B289319 : Blo 191804 289319 := bstep (se 1 (by rfl) ⟨216989, by rfl⟩ : syracuseStep 289319 = 433979) B433979
theorem B289403 : Blo 191804 289403 := bstep (se 1 (by rfl) ⟨217052, by rfl⟩ : syracuseStep 289403 = 434105) B434105
theorem B649943 : Blo 191804 649943 := bstep (se 1 (by rfl) ⟨487457, by rfl⟩ : syracuseStep 649943 = 974915) B974915
theorem B289529 : Blo 191804 289529 := bstep (se 2 (by rfl) ⟨108573, by rfl⟩ : syracuseStep 289529 = 217147) B217147
theorem B289631 : Blo 191804 289631 := bstep (se 1 (by rfl) ⟨217223, by rfl⟩ : syracuseStep 289631 = 434447) B434447
theorem B289643 : Blo 191804 289643 := bstep (se 1 (by rfl) ⟨217232, by rfl⟩ : syracuseStep 289643 = 434465) B434465
theorem B650159 : Blo 191804 650159 := bstep (se 1 (by rfl) ⟨487619, by rfl⟩ : syracuseStep 650159 = 975239) B975239
theorem B9989077 : Blo 191804 9989077 := bstep (se 7 (by rfl) ⟨117059, by rfl⟩ : syracuseStep 9989077 = 234119) B234119
theorem B1043507 : Blo 191804 1043507 := bstep (se 1 (by rfl) ⟨782630, by rfl⟩ : syracuseStep 1043507 = 1565261) B1565261
theorem B289871 : Blo 191804 289871 := bstep (se 1 (by rfl) ⟨217403, by rfl⟩ : syracuseStep 289871 = 434807) B434807
theorem B1240235 : Blo 191804 1240235 := bstep (se 1 (by rfl) ⟨930176, by rfl⟩ : syracuseStep 1240235 = 1860353) B1860353
theorem B289991 : Blo 191804 289991 := bstep (se 1 (by rfl) ⟨217493, by rfl⟩ : syracuseStep 289991 = 434987) B434987
theorem B781579 : Blo 191804 781579 := bstep (se 1 (by rfl) ⟨586184, by rfl⟩ : syracuseStep 781579 = 1172369) B1172369
theorem B191823 : Blo 191804 191823 := bstep (se 1 (by rfl) ⟨143867, by rfl⟩ : syracuseStep 191823 = 287735) B287735
theorem B2223449 : Blo 191804 2223449 := bstep (se 2 (by rfl) ⟨833793, by rfl⟩ : syracuseStep 2223449 = 1667587) B1667587
theorem B191839 : Blo 191804 191839 := bstep (se 1 (by rfl) ⟨143879, by rfl⟩ : syracuseStep 191839 = 287759) B287759
theorem B290153 : Blo 191804 290153 := bstep (se 2 (by rfl) ⟨108807, by rfl⟩ : syracuseStep 290153 = 217615) B217615
theorem B191867 : Blo 191804 191867 := bstep (se 1 (by rfl) ⟨143900, by rfl⟩ : syracuseStep 191867 = 287801) B287801
theorem B191919 : Blo 191804 191919 := bstep (se 1 (by rfl) ⟨143939, by rfl⟩ : syracuseStep 191919 = 287879) B287879
theorem B290231 : Blo 191804 290231 := bstep (se 1 (by rfl) ⟨217673, by rfl⟩ : syracuseStep 290231 = 435347) B435347
theorem B191943 : Blo 191804 191943 := bstep (se 1 (by rfl) ⟨143957, by rfl⟩ : syracuseStep 191943 = 287915) B287915
theorem B191963 : Blo 191804 191963 := bstep (se 1 (by rfl) ⟨143972, by rfl⟩ : syracuseStep 191963 = 287945) B287945
theorem B290267 : Blo 191804 290267 := bstep (se 1 (by rfl) ⟨217700, by rfl⟩ : syracuseStep 290267 = 435401) B435401
theorem B192039 : Blo 191804 192039 := bstep (se 1 (by rfl) ⟨144029, by rfl⟩ : syracuseStep 192039 = 288059) B288059
theorem B2485799 : Blo 191804 2485799 := bstep (se 1 (by rfl) ⟨1864349, by rfl⟩ : syracuseStep 2485799 = 3728699) B3728699
theorem B192079 : Blo 191804 192079 := bstep (se 1 (by rfl) ⟨144059, by rfl⟩ : syracuseStep 192079 = 288119) B288119
theorem B192095 : Blo 191804 192095 := bstep (se 1 (by rfl) ⟨144071, by rfl⟩ : syracuseStep 192095 = 288143) B288143
theorem B192123 : Blo 191804 192123 := bstep (se 1 (by rfl) ⟨144092, by rfl⟩ : syracuseStep 192123 = 288185) B288185
theorem B2715275 : Blo 191804 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B192175 : Blo 191804 192175 := bstep (se 1 (by rfl) ⟨144131, by rfl⟩ : syracuseStep 192175 = 288263) B288263
theorem B192199 : Blo 191804 192199 := bstep (se 1 (by rfl) ⟨144149, by rfl⟩ : syracuseStep 192199 = 288299) B288299
theorem B192219 : Blo 191804 192219 := bstep (se 1 (by rfl) ⟨144164, by rfl⟩ : syracuseStep 192219 = 288329) B288329
theorem B519929 : Blo 191804 519929 := bstep (se 2 (by rfl) ⟨194973, by rfl⟩ : syracuseStep 519929 = 389947) B389947
theorem B192295 : Blo 191804 192295 := bstep (se 1 (by rfl) ⟨144221, by rfl⟩ : syracuseStep 192295 = 288443) B288443
theorem B192335 : Blo 191804 192335 := bstep (se 1 (by rfl) ⟨144251, by rfl⟩ : syracuseStep 192335 = 288503) B288503
theorem B192351 : Blo 191804 192351 := bstep (se 1 (by rfl) ⟨144263, by rfl⟩ : syracuseStep 192351 = 288527) B288527
theorem B192379 : Blo 191804 192379 := bstep (se 1 (by rfl) ⟨144284, by rfl⟩ : syracuseStep 192379 = 288569) B288569
theorem B520111 : Blo 191804 520111 := bstep (se 1 (by rfl) ⟨390083, by rfl⟩ : syracuseStep 520111 = 780167) B780167
theorem B192431 : Blo 191804 192431 := bstep (se 1 (by rfl) ⟨144323, by rfl⟩ : syracuseStep 192431 = 288647) B288647
theorem B290735 : Blo 191804 290735 := bstep (se 1 (by rfl) ⟨218051, by rfl⟩ : syracuseStep 290735 = 436103) B436103
theorem B192455 : Blo 191804 192455 := bstep (se 1 (by rfl) ⟨144341, by rfl⟩ : syracuseStep 192455 = 288683) B288683
theorem B192475 : Blo 191804 192475 := bstep (se 1 (by rfl) ⟨144356, by rfl⟩ : syracuseStep 192475 = 288713) B288713
theorem B290825 : Blo 191804 290825 := bstep (se 2 (by rfl) ⟨109059, by rfl⟩ : syracuseStep 290825 = 218119) B218119
theorem B192551 : Blo 191804 192551 := bstep (se 1 (by rfl) ⟨144413, by rfl⟩ : syracuseStep 192551 = 288827) B288827
theorem B290855 : Blo 191804 290855 := bstep (se 1 (by rfl) ⟨218141, by rfl⟩ : syracuseStep 290855 = 436283) B436283
theorem B192591 : Blo 191804 192591 := bstep (se 1 (by rfl) ⟨144443, by rfl⟩ : syracuseStep 192591 = 288887) B288887
theorem B192607 : Blo 191804 192607 := bstep (se 1 (by rfl) ⟨144455, by rfl⟩ : syracuseStep 192607 = 288911) B288911
theorem B1110131 : Blo 191804 1110131 := bstep (se 1 (by rfl) ⟨832598, by rfl⟩ : syracuseStep 1110131 = 1665197) B1665197
theorem B192635 : Blo 191804 192635 := bstep (se 1 (by rfl) ⟨144476, by rfl⟩ : syracuseStep 192635 = 288953) B288953
theorem B290939 : Blo 191804 290939 := bstep (se 1 (by rfl) ⟨218204, by rfl⟩ : syracuseStep 290939 = 436409) B436409
theorem B192687 : Blo 191804 192687 := bstep (se 1 (by rfl) ⟨144515, by rfl⟩ : syracuseStep 192687 = 289031) B289031
theorem B192711 : Blo 191804 192711 := bstep (se 1 (by rfl) ⟨144533, by rfl⟩ : syracuseStep 192711 = 289067) B289067
theorem B192731 : Blo 191804 192731 := bstep (se 1 (by rfl) ⟨144548, by rfl⟩ : syracuseStep 192731 = 289097) B289097
theorem B323831 : Blo 191804 323831 := bstep (se 1 (by rfl) ⟨242873, by rfl⟩ : syracuseStep 323831 = 485747) B485747
theorem B291065 : Blo 191804 291065 := bstep (se 2 (by rfl) ⟨109149, by rfl⟩ : syracuseStep 291065 = 218299) B218299
theorem B192807 : Blo 191804 192807 := bstep (se 1 (by rfl) ⟨144605, by rfl⟩ : syracuseStep 192807 = 289211) B289211
theorem B192847 : Blo 191804 192847 := bstep (se 1 (by rfl) ⟨144635, by rfl⟩ : syracuseStep 192847 = 289271) B289271
theorem B192863 : Blo 191804 192863 := bstep (se 1 (by rfl) ⟨144647, by rfl⟩ : syracuseStep 192863 = 289295) B289295
theorem B291167 : Blo 191804 291167 := bstep (se 1 (by rfl) ⟨218375, by rfl⟩ : syracuseStep 291167 = 436751) B436751
theorem B291179 : Blo 191804 291179 := bstep (se 1 (by rfl) ⟨218384, by rfl⟩ : syracuseStep 291179 = 436769) B436769
theorem B192891 : Blo 191804 192891 := bstep (se 1 (by rfl) ⟨144668, by rfl⟩ : syracuseStep 192891 = 289337) B289337
theorem B192943 : Blo 191804 192943 := bstep (se 1 (by rfl) ⟨144707, by rfl⟩ : syracuseStep 192943 = 289415) B289415
theorem B192967 : Blo 191804 192967 := bstep (se 1 (by rfl) ⟨144725, by rfl⟩ : syracuseStep 192967 = 289451) B289451
theorem B192987 : Blo 191804 192987 := bstep (se 1 (by rfl) ⟨144740, by rfl⟩ : syracuseStep 192987 = 289481) B289481
theorem B193063 : Blo 191804 193063 := bstep (se 1 (by rfl) ⟨144797, by rfl⟩ : syracuseStep 193063 = 289595) B289595
theorem B324175 : Blo 191804 324175 := bstep (se 1 (by rfl) ⟨243131, by rfl⟩ : syracuseStep 324175 = 486263) B486263
theorem B389711 : Blo 191804 389711 := bstep (se 1 (by rfl) ⟨292283, by rfl⟩ : syracuseStep 389711 = 584567) B584567
theorem B193103 : Blo 191804 193103 := bstep (se 1 (by rfl) ⟨144827, by rfl⟩ : syracuseStep 193103 = 289655) B289655
theorem B291407 : Blo 191804 291407 := bstep (se 1 (by rfl) ⟨218555, by rfl⟩ : syracuseStep 291407 = 437111) B437111
theorem B193119 : Blo 191804 193119 := bstep (se 1 (by rfl) ⟨144839, by rfl⟩ : syracuseStep 193119 = 289679) B289679
theorem B193147 : Blo 191804 193147 := bstep (se 1 (by rfl) ⟨144860, by rfl⟩ : syracuseStep 193147 = 289721) B289721
theorem B193199 : Blo 191804 193199 := bstep (se 1 (by rfl) ⟨144899, by rfl⟩ : syracuseStep 193199 = 289799) B289799
theorem B193223 : Blo 191804 193223 := bstep (se 1 (by rfl) ⟨144917, by rfl⟩ : syracuseStep 193223 = 289835) B289835
theorem B291527 : Blo 191804 291527 := bstep (se 1 (by rfl) ⟨218645, by rfl⟩ : syracuseStep 291527 = 437291) B437291
theorem B193243 : Blo 191804 193243 := bstep (se 1 (by rfl) ⟨144932, by rfl⟩ : syracuseStep 193243 = 289865) B289865
theorem B7893773 : Blo 191804 7893773 := bstep (se 3 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 7893773 = 2960165) B2960165
theorem B193319 : Blo 191804 193319 := bstep (se 1 (by rfl) ⟨144989, by rfl⟩ : syracuseStep 193319 = 289979) B289979
theorem B324425 : Blo 191804 324425 := bstep (se 2 (by rfl) ⟨121659, by rfl⟩ : syracuseStep 324425 = 243319) B243319
theorem B193359 : Blo 191804 193359 := bstep (se 1 (by rfl) ⟨145019, by rfl⟩ : syracuseStep 193359 = 290039) B290039
theorem B193375 : Blo 191804 193375 := bstep (se 1 (by rfl) ⟨145031, by rfl⟩ : syracuseStep 193375 = 290063) B290063
theorem B291689 : Blo 191804 291689 := bstep (se 2 (by rfl) ⟨109383, by rfl⟩ : syracuseStep 291689 = 218767) B218767
theorem B193403 : Blo 191804 193403 := bstep (se 1 (by rfl) ⟨145052, by rfl⟩ : syracuseStep 193403 = 290105) B290105
theorem B783265 : Blo 191804 783265 := bstep (se 2 (by rfl) ⟨293724, by rfl⟩ : syracuseStep 783265 = 587449) B587449
theorem B193455 : Blo 191804 193455 := bstep (se 1 (by rfl) ⟨145091, by rfl⟩ : syracuseStep 193455 = 290183) B290183
theorem B291767 : Blo 191804 291767 := bstep (se 1 (by rfl) ⟨218825, by rfl⟩ : syracuseStep 291767 = 437651) B437651
theorem B193479 : Blo 191804 193479 := bstep (se 1 (by rfl) ⟨145109, by rfl⟩ : syracuseStep 193479 = 290219) B290219
theorem B193499 : Blo 191804 193499 := bstep (se 1 (by rfl) ⟨145124, by rfl⟩ : syracuseStep 193499 = 290249) B290249
theorem B291803 : Blo 191804 291803 := bstep (se 1 (by rfl) ⟨218852, by rfl⟩ : syracuseStep 291803 = 437705) B437705
theorem B193575 : Blo 191804 193575 := bstep (se 1 (by rfl) ⟨145181, by rfl⟩ : syracuseStep 193575 = 290363) B290363
theorem B193615 : Blo 191804 193615 := bstep (se 1 (by rfl) ⟨145211, by rfl⟩ : syracuseStep 193615 = 290423) B290423
theorem B193631 : Blo 191804 193631 := bstep (se 1 (by rfl) ⟨145223, by rfl⟩ : syracuseStep 193631 = 290447) B290447
theorem B1471607 : Blo 191804 1471607 := bstep (se 1 (by rfl) ⟨1103705, by rfl⟩ : syracuseStep 1471607 = 2207411) B2207411
theorem B193659 : Blo 191804 193659 := bstep (se 1 (by rfl) ⟨145244, by rfl⟩ : syracuseStep 193659 = 290489) B290489
theorem B193711 : Blo 191804 193711 := bstep (se 1 (by rfl) ⟨145283, by rfl⟩ : syracuseStep 193711 = 290567) B290567
theorem B193735 : Blo 191804 193735 := bstep (se 1 (by rfl) ⟨145301, by rfl⟩ : syracuseStep 193735 = 290603) B290603
theorem B193755 : Blo 191804 193755 := bstep (se 1 (by rfl) ⟨145316, by rfl⟩ : syracuseStep 193755 = 290633) B290633
theorem B652535 : Blo 191804 652535 := bstep (se 1 (by rfl) ⟨489401, by rfl⟩ : syracuseStep 652535 = 978803) B978803
theorem B324857 : Blo 191804 324857 := bstep (se 2 (by rfl) ⟨121821, by rfl⟩ : syracuseStep 324857 = 243643) B243643
theorem B193831 : Blo 191804 193831 := bstep (se 1 (by rfl) ⟨145373, by rfl⟩ : syracuseStep 193831 = 290747) B290747
theorem B193871 : Blo 191804 193871 := bstep (se 1 (by rfl) ⟨145403, by rfl⟩ : syracuseStep 193871 = 290807) B290807
theorem B193887 : Blo 191804 193887 := bstep (se 1 (by rfl) ⟨145415, by rfl⟩ : syracuseStep 193887 = 290831) B290831
theorem B390505 : Blo 191804 390505 := bstep (se 2 (by rfl) ⟨146439, by rfl⟩ : syracuseStep 390505 = 292879) B292879
theorem B193915 : Blo 191804 193915 := bstep (se 1 (by rfl) ⟨145436, by rfl⟩ : syracuseStep 193915 = 290873) B290873
theorem B325039 : Blo 191804 325039 := bstep (se 1 (by rfl) ⟨243779, by rfl⟩ : syracuseStep 325039 = 487559) B487559
theorem B193967 : Blo 191804 193967 := bstep (se 1 (by rfl) ⟨145475, by rfl⟩ : syracuseStep 193967 = 290951) B290951
theorem B292271 : Blo 191804 292271 := bstep (se 1 (by rfl) ⟨219203, by rfl⟩ : syracuseStep 292271 = 438407) B438407
theorem B193991 : Blo 191804 193991 := bstep (se 1 (by rfl) ⟨145493, by rfl⟩ : syracuseStep 193991 = 290987) B290987
theorem B390619 : Blo 191804 390619 := bstep (se 1 (by rfl) ⟨292964, by rfl⟩ : syracuseStep 390619 = 585929) B585929
theorem B194011 : Blo 191804 194011 := bstep (se 1 (by rfl) ⟨145508, by rfl⟩ : syracuseStep 194011 = 291017) B291017
theorem B3536369 : Blo 191804 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B325127 : Blo 191804 325127 := bstep (se 1 (by rfl) ⟨243845, by rfl⟩ : syracuseStep 325127 = 487691) B487691
theorem B292361 : Blo 191804 292361 := bstep (se 2 (by rfl) ⟨109635, by rfl⟩ : syracuseStep 292361 = 219271) B219271
theorem B292391 : Blo 191804 292391 := bstep (se 1 (by rfl) ⟨219293, by rfl⟩ : syracuseStep 292391 = 438587) B438587
theorem B194087 : Blo 191804 194087 := bstep (se 1 (by rfl) ⟨145565, by rfl⟩ : syracuseStep 194087 = 291131) B291131
theorem B652859 : Blo 191804 652859 := bstep (se 1 (by rfl) ⟨489644, by rfl⟩ : syracuseStep 652859 = 979289) B979289
theorem B194127 : Blo 191804 194127 := bstep (se 1 (by rfl) ⟨145595, by rfl⟩ : syracuseStep 194127 = 291191) B291191
theorem B194143 : Blo 191804 194143 := bstep (se 1 (by rfl) ⟨145607, by rfl⟩ : syracuseStep 194143 = 291215) B291215
theorem B194171 : Blo 191804 194171 := bstep (se 1 (by rfl) ⟨145628, by rfl⟩ : syracuseStep 194171 = 291257) B291257
theorem B292475 : Blo 191804 292475 := bstep (se 1 (by rfl) ⟨219356, by rfl⟩ : syracuseStep 292475 = 438713) B438713
theorem B194223 : Blo 191804 194223 := bstep (se 1 (by rfl) ⟨145667, by rfl⟩ : syracuseStep 194223 = 291335) B291335
theorem B194247 : Blo 191804 194247 := bstep (se 1 (by rfl) ⟨145685, by rfl⟩ : syracuseStep 194247 = 291371) B291371
theorem B194267 : Blo 191804 194267 := bstep (se 1 (by rfl) ⟨145700, by rfl⟩ : syracuseStep 194267 = 291401) B291401
theorem B292601 : Blo 191804 292601 := bstep (se 2 (by rfl) ⟨109725, by rfl⟩ : syracuseStep 292601 = 219451) B219451
theorem B194343 : Blo 191804 194343 := bstep (se 1 (by rfl) ⟨145757, by rfl⟩ : syracuseStep 194343 = 291515) B291515
theorem B1668923 : Blo 191804 1668923 := bstep (se 1 (by rfl) ⟨1251692, by rfl⟩ : syracuseStep 1668923 = 2503385) B2503385
theorem B653129 : Blo 191804 653129 := bstep (se 2 (by rfl) ⟨244923, by rfl⟩ : syracuseStep 653129 = 489847) B489847
theorem B194383 : Blo 191804 194383 := bstep (se 1 (by rfl) ⟨145787, by rfl⟩ : syracuseStep 194383 = 291575) B291575
theorem B325471 : Blo 191804 325471 := bstep (se 1 (by rfl) ⟨244103, by rfl⟩ : syracuseStep 325471 = 488207) B488207
theorem B489311 : Blo 191804 489311 := bstep (se 1 (by rfl) ⟨366983, by rfl⟩ : syracuseStep 489311 = 733967) B733967
theorem B194399 : Blo 191804 194399 := bstep (se 1 (by rfl) ⟨145799, by rfl⟩ : syracuseStep 194399 = 291599) B291599
theorem B292703 : Blo 191804 292703 := bstep (se 1 (by rfl) ⟨219527, by rfl⟩ : syracuseStep 292703 = 439055) B439055
theorem B292715 : Blo 191804 292715 := bstep (se 1 (by rfl) ⟨219536, by rfl⟩ : syracuseStep 292715 = 439073) B439073
theorem B194427 : Blo 191804 194427 := bstep (se 1 (by rfl) ⟨145820, by rfl⟩ : syracuseStep 194427 = 291641) B291641
theorem B587681 : Blo 191804 587681 := bstep (se 2 (by rfl) ⟨220380, by rfl⟩ : syracuseStep 587681 = 440761) B440761
theorem B194479 : Blo 191804 194479 := bstep (se 1 (by rfl) ⟨145859, by rfl⟩ : syracuseStep 194479 = 291719) B291719
theorem B325559 : Blo 191804 325559 := bstep (se 1 (by rfl) ⟨244169, by rfl⟩ : syracuseStep 325559 = 488339) B488339
theorem B194503 : Blo 191804 194503 := bstep (se 1 (by rfl) ⟨145877, by rfl⟩ : syracuseStep 194503 = 291755) B291755
theorem B194523 : Blo 191804 194523 := bstep (se 1 (by rfl) ⟨145892, by rfl⟩ : syracuseStep 194523 = 291785) B291785
theorem B194599 : Blo 191804 194599 := bstep (se 1 (by rfl) ⟨145949, by rfl⟩ : syracuseStep 194599 = 291899) B291899
theorem B194639 : Blo 191804 194639 := bstep (se 1 (by rfl) ⟨145979, by rfl⟩ : syracuseStep 194639 = 291959) B291959
theorem B292943 : Blo 191804 292943 := bstep (se 1 (by rfl) ⟨219707, by rfl⟩ : syracuseStep 292943 = 439415) B439415
theorem B194655 : Blo 191804 194655 := bstep (se 1 (by rfl) ⟨145991, by rfl⟩ : syracuseStep 194655 = 291983) B291983
theorem B194683 : Blo 191804 194683 := bstep (se 1 (by rfl) ⟨146012, by rfl⟩ : syracuseStep 194683 = 292025) B292025
theorem B194735 : Blo 191804 194735 := bstep (se 1 (by rfl) ⟨146051, by rfl⟩ : syracuseStep 194735 = 292103) B292103
theorem B784579 : Blo 191804 784579 := bstep (se 1 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 784579 = 1176869) B1176869
theorem B194759 : Blo 191804 194759 := bstep (se 1 (by rfl) ⟨146069, by rfl⟩ : syracuseStep 194759 = 292139) B292139
theorem B293063 : Blo 191804 293063 := bstep (se 1 (by rfl) ⟨219797, by rfl⟩ : syracuseStep 293063 = 439595) B439595
theorem B194779 : Blo 191804 194779 := bstep (se 1 (by rfl) ⟨146084, by rfl⟩ : syracuseStep 194779 = 292169) B292169
theorem B1407233 : Blo 191804 1407233 := bstep (se 2 (by rfl) ⟨527712, by rfl⟩ : syracuseStep 1407233 = 1055425) B1055425
theorem B194855 : Blo 191804 194855 := bstep (se 1 (by rfl) ⟨146141, by rfl⟩ : syracuseStep 194855 = 292283) B292283
theorem B194895 : Blo 191804 194895 := bstep (se 1 (by rfl) ⟨146171, by rfl⟩ : syracuseStep 194895 = 292343) B292343
theorem B194911 : Blo 191804 194911 := bstep (se 1 (by rfl) ⟨146183, by rfl⟩ : syracuseStep 194911 = 292367) B292367
theorem B293225 : Blo 191804 293225 := bstep (se 2 (by rfl) ⟨109959, by rfl⟩ : syracuseStep 293225 = 219919) B219919
theorem B194939 : Blo 191804 194939 := bstep (se 1 (by rfl) ⟨146204, by rfl⟩ : syracuseStep 194939 = 292409) B292409
theorem B555407 : Blo 191804 555407 := bstep (se 1 (by rfl) ⟨416555, by rfl⟩ : syracuseStep 555407 = 833111) B833111
theorem B194991 : Blo 191804 194991 := bstep (se 1 (by rfl) ⟨146243, by rfl⟩ : syracuseStep 194991 = 292487) B292487
theorem B293303 : Blo 191804 293303 := bstep (se 1 (by rfl) ⟨219977, by rfl⟩ : syracuseStep 293303 = 439955) B439955
theorem B195015 : Blo 191804 195015 := bstep (se 1 (by rfl) ⟨146261, by rfl⟩ : syracuseStep 195015 = 292523) B292523
theorem B195035 : Blo 191804 195035 := bstep (se 1 (by rfl) ⟨146276, by rfl⟩ : syracuseStep 195035 = 292553) B292553
theorem B293339 : Blo 191804 293339 := bstep (se 1 (by rfl) ⟨220004, by rfl⟩ : syracuseStep 293339 = 440009) B440009
theorem B326153 : Blo 191804 326153 := bstep (se 2 (by rfl) ⟨122307, by rfl⟩ : syracuseStep 326153 = 244615) B244615
theorem B490009 : Blo 191804 490009 := bstep (se 2 (by rfl) ⟨183753, by rfl⟩ : syracuseStep 490009 = 367507) B367507
theorem B195111 : Blo 191804 195111 := bstep (se 1 (by rfl) ⟨146333, by rfl⟩ : syracuseStep 195111 = 292667) B292667
theorem B195151 : Blo 191804 195151 := bstep (se 1 (by rfl) ⟨146363, by rfl⟩ : syracuseStep 195151 = 292727) B292727
theorem B195167 : Blo 191804 195167 := bstep (se 1 (by rfl) ⟨146375, by rfl⟩ : syracuseStep 195167 = 292751) B292751
theorem B359009 : Blo 191804 359009 := bstep (se 2 (by rfl) ⟨134628, by rfl⟩ : syracuseStep 359009 = 269257) B269257
theorem B195195 : Blo 191804 195195 := bstep (se 1 (by rfl) ⟨146396, by rfl⟩ : syracuseStep 195195 = 292793) B292793
theorem B326315 : Blo 191804 326315 := bstep (se 1 (by rfl) ⟨244736, by rfl⟩ : syracuseStep 326315 = 489473) B489473
theorem B195247 : Blo 191804 195247 := bstep (se 1 (by rfl) ⟨146435, by rfl⟩ : syracuseStep 195247 = 292871) B292871
theorem B621245 : Blo 191804 621245 := bstep (se 3 (by rfl) ⟨116483, by rfl⟩ : syracuseStep 621245 = 232967) B232967
theorem B195271 : Blo 191804 195271 := bstep (se 1 (by rfl) ⟨146453, by rfl⟩ : syracuseStep 195271 = 292907) B292907
theorem B195291 : Blo 191804 195291 := bstep (se 1 (by rfl) ⟨146468, by rfl⟩ : syracuseStep 195291 = 292937) B292937
theorem B195367 : Blo 191804 195367 := bstep (se 1 (by rfl) ⟨146525, by rfl⟩ : syracuseStep 195367 = 293051) B293051
theorem B588617 : Blo 191804 588617 := bstep (se 2 (by rfl) ⟨220731, by rfl⟩ : syracuseStep 588617 = 441463) B441463
theorem B490313 : Blo 191804 490313 := bstep (se 2 (by rfl) ⟨183867, by rfl⟩ : syracuseStep 490313 = 367735) B367735
theorem B195407 : Blo 191804 195407 := bstep (se 1 (by rfl) ⟨146555, by rfl⟩ : syracuseStep 195407 = 293111) B293111
theorem B195423 : Blo 191804 195423 := bstep (se 1 (by rfl) ⟨146567, by rfl⟩ : syracuseStep 195423 = 293135) B293135
theorem B1145707 : Blo 191804 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B195451 : Blo 191804 195451 := bstep (se 1 (by rfl) ⟨146588, by rfl⟩ : syracuseStep 195451 = 293177) B293177
theorem B195503 : Blo 191804 195503 := bstep (se 1 (by rfl) ⟨146627, by rfl⟩ : syracuseStep 195503 = 293255) B293255
theorem B654263 : Blo 191804 654263 := bstep (se 1 (by rfl) ⟨490697, by rfl⟩ : syracuseStep 654263 = 981395) B981395
theorem B195527 : Blo 191804 195527 := bstep (se 1 (by rfl) ⟨146645, by rfl⟩ : syracuseStep 195527 = 293291) B293291
theorem B195547 : Blo 191804 195547 := bstep (se 1 (by rfl) ⟨146660, by rfl⟩ : syracuseStep 195547 = 293321) B293321
theorem B195623 : Blo 191804 195623 := bstep (se 1 (by rfl) ⟨146717, by rfl⟩ : syracuseStep 195623 = 293435) B293435
theorem B326713 : Blo 191804 326713 := bstep (se 2 (by rfl) ⟨122517, by rfl⟩ : syracuseStep 326713 = 245035) B245035
theorem B195663 : Blo 191804 195663 := bstep (se 1 (by rfl) ⟨146747, by rfl⟩ : syracuseStep 195663 = 293495) B293495
theorem B195679 : Blo 191804 195679 := bstep (se 1 (by rfl) ⟨146759, by rfl⟩ : syracuseStep 195679 = 293519) B293519
theorem B195707 : Blo 191804 195707 := bstep (se 1 (by rfl) ⟨146780, by rfl⟩ : syracuseStep 195707 = 293561) B293561
theorem B195759 : Blo 191804 195759 := bstep (se 1 (by rfl) ⟨146819, by rfl⟩ : syracuseStep 195759 = 293639) B293639
theorem B326855 : Blo 191804 326855 := bstep (se 1 (by rfl) ⟨245141, by rfl⟩ : syracuseStep 326855 = 490283) B490283
theorem B195783 : Blo 191804 195783 := bstep (se 1 (by rfl) ⟨146837, by rfl⟩ : syracuseStep 195783 = 293675) B293675
theorem B195803 : Blo 191804 195803 := bstep (se 1 (by rfl) ⟨146852, by rfl⟩ : syracuseStep 195803 = 293705) B293705
theorem B1015031 : Blo 191804 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B327017 : Blo 191804 327017 := bstep (se 2 (by rfl) ⟨122631, by rfl⟩ : syracuseStep 327017 = 245263) B245263
theorem B654857 : Blo 191804 654857 := bstep (se 2 (by rfl) ⟨245571, by rfl⟩ : syracuseStep 654857 = 491143) B491143
theorem B1113821 : Blo 191804 1113821 := bstep (se 3 (by rfl) ⟨208841, by rfl⟩ : syracuseStep 1113821 = 417683) B417683
theorem B327415 : Blo 191804 327415 := bstep (se 1 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 327415 = 491123) B491123
theorem B491447 : Blo 191804 491447 := bstep (se 1 (by rfl) ⟨368585, by rfl⟩ : syracuseStep 491447 = 737171) B737171
theorem B327611 : Blo 191804 327611 := bstep (se 1 (by rfl) ⟨245708, by rfl⟩ : syracuseStep 327611 = 491417) B491417
theorem B15728717 : Blo 191804 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B819305 : Blo 191804 819305 := bstep (se 2 (by rfl) ⟨307239, by rfl⟩ : syracuseStep 819305 = 614479) B614479
theorem B196955 : Blo 191804 196955 := bstep (se 1 (by rfl) ⟨147716, by rfl⟩ : syracuseStep 196955 = 295433) B295433
theorem B492095 : Blo 191804 492095 := bstep (se 1 (by rfl) ⟨369071, by rfl⟩ : syracuseStep 492095 = 738143) B738143
theorem B328313 : Blo 191804 328313 := bstep (se 2 (by rfl) ⟨123117, by rfl⟩ : syracuseStep 328313 = 246235) B246235
theorem B328367 : Blo 191804 328367 := bstep (se 1 (by rfl) ⟨246275, by rfl⟩ : syracuseStep 328367 = 492551) B492551
theorem B3539659 : Blo 191804 3539659 := bstep (se 1 (by rfl) ⟨2654744, by rfl⟩ : syracuseStep 3539659 = 5309489) B5309489
theorem B656207 : Blo 191804 656207 := bstep (se 1 (by rfl) ⟨492155, by rfl⟩ : syracuseStep 656207 = 984311) B984311
theorem B394139 : Blo 191804 394139 := bstep (se 1 (by rfl) ⟨295604, by rfl⟩ : syracuseStep 394139 = 591209) B591209
theorem B328603 : Blo 191804 328603 := bstep (se 1 (by rfl) ⟨246452, by rfl⟩ : syracuseStep 328603 = 492905) B492905
theorem B656531 : Blo 191804 656531 := bstep (se 1 (by rfl) ⟨492398, by rfl⟩ : syracuseStep 656531 = 984797) B984797
theorem B492743 : Blo 191804 492743 := bstep (se 1 (by rfl) ⟨369557, by rfl⟩ : syracuseStep 492743 = 739115) B739115
theorem B492763 : Blo 191804 492763 := bstep (se 1 (by rfl) ⟨369572, by rfl⟩ : syracuseStep 492763 = 739145) B739145
theorem B656801 : Blo 191804 656801 := bstep (se 2 (by rfl) ⟨246300, by rfl⟩ : syracuseStep 656801 = 492601) B492601
theorem B820793 : Blo 191804 820793 := bstep (se 2 (by rfl) ⟨307797, by rfl⟩ : syracuseStep 820793 = 615595) B615595
theorem B231007 : Blo 191804 231007 := bstep (se 1 (by rfl) ⟨173255, by rfl⟩ : syracuseStep 231007 = 346511) B346511
theorem B1410949 : Blo 191804 1410949 := bstep (se 4 (by rfl) ⟨132276, by rfl⟩ : syracuseStep 1410949 = 264553) B264553
theorem B1247183 : Blo 191804 1247183 := bstep (se 1 (by rfl) ⟨935387, by rfl⟩ : syracuseStep 1247183 = 1870775) B1870775
theorem B985121 : Blo 191804 985121 := bstep (se 2 (by rfl) ⟨369420, by rfl⟩ : syracuseStep 985121 = 738841) B738841
theorem B3606605 : Blo 191804 3606605 := bstep (se 3 (by rfl) ⟨676238, by rfl⟩ : syracuseStep 3606605 = 1352477) B1352477
theorem B985283 : Blo 191804 985283 := bstep (se 1 (by rfl) ⟨738962, by rfl⟩ : syracuseStep 985283 = 1477925) B1477925
theorem B1116413 : Blo 191804 1116413 := bstep (se 3 (by rfl) ⟨209327, by rfl⟩ : syracuseStep 1116413 = 418655) B418655
theorem B526589 : Blo 191804 526589 := bstep (se 3 (by rfl) ⟨98735, by rfl⟩ : syracuseStep 526589 = 197471) B197471
theorem B1607933 : Blo 191804 1607933 := bstep (se 3 (by rfl) ⟨301487, by rfl⟩ : syracuseStep 1607933 = 602975) B602975
theorem B493897 : Blo 191804 493897 := bstep (se 2 (by rfl) ⟨185211, by rfl⟩ : syracuseStep 493897 = 370423) B370423
theorem B330095 : Blo 191804 330095 := bstep (se 1 (by rfl) ⟨247571, by rfl⟩ : syracuseStep 330095 = 495143) B495143
theorem B330311 : Blo 191804 330311 := bstep (se 1 (by rfl) ⟨247733, by rfl⟩ : syracuseStep 330311 = 495467) B495467
theorem B494201 : Blo 191804 494201 := bstep (se 2 (by rfl) ⟨185325, by rfl⟩ : syracuseStep 494201 = 370651) B370651
theorem B2100599 : Blo 191804 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B1248641 : Blo 191804 1248641 := bstep (se 2 (by rfl) ⟨468240, by rfl⟩ : syracuseStep 1248641 = 936481) B936481
theorem B396895 : Blo 191804 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B1478411 : Blo 191804 1478411 := bstep (se 1 (by rfl) ⟨1108808, by rfl⟩ : syracuseStep 1478411 = 2217617) B2217617
theorem B233371 : Blo 191804 233371 := bstep (se 1 (by rfl) ⟨175028, by rfl⟩ : syracuseStep 233371 = 350057) B350057
theorem B3149725 : Blo 191804 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B332143 : Blo 191804 332143 := bstep (se 1 (by rfl) ⟨249107, by rfl⟩ : syracuseStep 332143 = 498215) B498215
theorem B1479131 : Blo 191804 1479131 := bstep (se 1 (by rfl) ⟨1109348, by rfl⟩ : syracuseStep 1479131 = 2218697) B2218697
theorem B659987 : Blo 191804 659987 := bstep (se 1 (by rfl) ⟨494990, by rfl⟩ : syracuseStep 659987 = 989981) B989981
theorem B463859 : Blo 191804 463859 := bstep (se 1 (by rfl) ⟨347894, by rfl⟩ : syracuseStep 463859 = 695789) B695789
theorem B1873043 : Blo 191804 1873043 := bstep (se 1 (by rfl) ⟨1404782, by rfl⟩ : syracuseStep 1873043 = 2809565) B2809565
theorem B3871901 : Blo 191804 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B693481 : Blo 191804 693481 := bstep (se 2 (by rfl) ⟨260055, by rfl⟩ : syracuseStep 693481 = 520111) B520111
theorem B922873 : Blo 191804 922873 := bstep (se 2 (by rfl) ⟨346077, by rfl⟩ : syracuseStep 922873 = 692155) B692155
theorem B267769 : Blo 191804 267769 := bstep (se 2 (by rfl) ⟨100413, by rfl⟩ : syracuseStep 267769 = 200827) B200827
theorem B1676837 : Blo 191804 1676837 := bstep (se 4 (by rfl) ⟨157203, by rfl⟩ : syracuseStep 1676837 = 314407) B314407
theorem B431711 : Blo 191804 431711 := bstep (se 1 (by rfl) ⟨323783, by rfl⟩ : syracuseStep 431711 = 647567) B647567
theorem B1251101 : Blo 191804 1251101 := bstep (se 3 (by rfl) ⟨234581, by rfl⟩ : syracuseStep 1251101 = 469163) B469163
theorem B366383 : Blo 191804 366383 := bstep (se 1 (by rfl) ⟨274787, by rfl⟩ : syracuseStep 366383 = 549575) B549575
theorem B431927 : Blo 191804 431927 := bstep (se 1 (by rfl) ⟨323945, by rfl⟩ : syracuseStep 431927 = 647891) B647891
theorem B989009 : Blo 191804 989009 := bstep (se 2 (by rfl) ⟨370878, by rfl⟩ : syracuseStep 989009 = 741757) B741757
theorem B432233 : Blo 191804 432233 := bstep (se 2 (by rfl) ⟨162087, by rfl⟩ : syracuseStep 432233 = 324175) B324175
theorem B432719 : Blo 191804 432719 := bstep (se 1 (by rfl) ⟨324539, by rfl⟩ : syracuseStep 432719 = 649079) B649079
theorem B989819 : Blo 191804 989819 := bstep (se 1 (by rfl) ⟨742364, by rfl⟩ : syracuseStep 989819 = 1484729) B1484729
theorem B432863 : Blo 191804 432863 := bstep (se 1 (by rfl) ⟨324647, by rfl⟩ : syracuseStep 432863 = 649295) B649295
theorem B4168421 : Blo 191804 4168421 := bstep (se 4 (by rfl) ⟨390789, by rfl⟩ : syracuseStep 4168421 = 781579) B781579
theorem B465743 : Blo 191804 465743 := bstep (se 1 (by rfl) ⟨349307, by rfl⟩ : syracuseStep 465743 = 698615) B698615
theorem B433115 : Blo 191804 433115 := bstep (se 1 (by rfl) ⟨324836, by rfl⟩ : syracuseStep 433115 = 649673) B649673
theorem B367591 : Blo 191804 367591 := bstep (se 1 (by rfl) ⟨275693, by rfl⟩ : syracuseStep 367591 = 551387) B551387
theorem B433295 : Blo 191804 433295 := bstep (se 1 (by rfl) ⟨324971, by rfl⟩ : syracuseStep 433295 = 649943) B649943
theorem B1055963 : Blo 191804 1055963 := bstep (se 1 (by rfl) ⟨791972, by rfl⟩ : syracuseStep 1055963 = 1583945) B1583945
theorem B433385 : Blo 191804 433385 := bstep (se 2 (by rfl) ⟨162519, by rfl⟩ : syracuseStep 433385 = 325039) B325039
theorem B433439 : Blo 191804 433439 := bstep (se 1 (by rfl) ⟨325079, by rfl⟩ : syracuseStep 433439 = 650159) B650159
theorem B695671 : Blo 191804 695671 := bstep (se 1 (by rfl) ⟨521753, by rfl⟩ : syracuseStep 695671 = 1043507) B1043507
theorem B826823 : Blo 191804 826823 := bstep (se 1 (by rfl) ⟨620117, by rfl⟩ : syracuseStep 826823 = 1240235) B1240235
theorem B1383961 : Blo 191804 1383961 := bstep (se 2 (by rfl) ⟨518985, by rfl⟩ : syracuseStep 1383961 = 1037971) B1037971
theorem B1482299 : Blo 191804 1482299 := bstep (se 1 (by rfl) ⟨1111724, by rfl⟩ : syracuseStep 1482299 = 2223449) B2223449
theorem B7118405 : Blo 191804 7118405 := bstep (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) B1334701
theorem B1810183 : Blo 191804 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B925451 : Blo 191804 925451 := bstep (se 1 (by rfl) ⟨694088, by rfl⟩ : syracuseStep 925451 = 1388177) B1388177
theorem B433961 : Blo 191804 433961 := bstep (se 2 (by rfl) ⟨162735, by rfl⟩ : syracuseStep 433961 = 325471) B325471
theorem B1581065 : Blo 191804 1581065 := bstep (se 2 (by rfl) ⟨592899, by rfl⟩ : syracuseStep 1581065 = 1185799) B1185799
theorem B435023 : Blo 191804 435023 := bstep (se 1 (by rfl) ⟨326267, by rfl⟩ : syracuseStep 435023 = 652535) B652535
theorem B1057697 : Blo 191804 1057697 := bstep (se 2 (by rfl) ⟨396636, by rfl⟩ : syracuseStep 1057697 = 793273) B793273
theorem B435239 : Blo 191804 435239 := bstep (se 1 (by rfl) ⟨326429, by rfl⟩ : syracuseStep 435239 = 652859) B652859
theorem B435419 : Blo 191804 435419 := bstep (se 1 (by rfl) ⟨326564, by rfl⟩ : syracuseStep 435419 = 653129) B653129
theorem B435617 : Blo 191804 435617 := bstep (se 2 (by rfl) ⟨163356, by rfl⟩ : syracuseStep 435617 = 326713) B326713
theorem B1582649 : Blo 191804 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B370271 : Blo 191804 370271 := bstep (se 1 (by rfl) ⟨277703, by rfl⟩ : syracuseStep 370271 = 555407) B555407
theorem B239339 : Blo 191804 239339 := bstep (se 1 (by rfl) ⟨179504, by rfl⟩ : syracuseStep 239339 = 359009) B359009
theorem B1648451 : Blo 191804 1648451 := bstep (se 1 (by rfl) ⟨1236338, by rfl⟩ : syracuseStep 1648451 = 2472677) B2472677
theorem B436175 : Blo 191804 436175 := bstep (se 1 (by rfl) ⟨327131, by rfl⟩ : syracuseStep 436175 = 654263) B654263
theorem B829693 : Blo 191804 829693 := bstep (se 3 (by rfl) ⟨155567, by rfl⟩ : syracuseStep 829693 = 311135) B311135
theorem B436553 : Blo 191804 436553 := bstep (se 2 (by rfl) ⟨163707, by rfl⟩ : syracuseStep 436553 = 327415) B327415
theorem B436571 : Blo 191804 436571 := bstep (se 1 (by rfl) ⟨327428, by rfl⟩ : syracuseStep 436571 = 654857) B654857
theorem B469567 : Blo 191804 469567 := bstep (se 1 (by rfl) ⟨352175, by rfl⟩ : syracuseStep 469567 = 704351) B704351
theorem B273307 : Blo 191804 273307 := bstep (se 1 (by rfl) ⟨204980, by rfl⟩ : syracuseStep 273307 = 409961) B409961
theorem B437147 : Blo 191804 437147 := bstep (se 1 (by rfl) ⟨327860, by rfl⟩ : syracuseStep 437147 = 655721) B655721
theorem B437345 : Blo 191804 437345 := bstep (se 2 (by rfl) ⟨164004, by rfl⟩ : syracuseStep 437345 = 328009) B328009
theorem B437543 : Blo 191804 437543 := bstep (se 1 (by rfl) ⟨328157, by rfl⟩ : syracuseStep 437543 = 656315) B656315
theorem B208219 : Blo 191804 208219 := bstep (se 1 (by rfl) ⟨156164, by rfl⟩ : syracuseStep 208219 = 312329) B312329
theorem B437921 : Blo 191804 437921 := bstep (se 2 (by rfl) ⟨164220, by rfl⟩ : syracuseStep 437921 = 328441) B328441
theorem B667297 : Blo 191804 667297 := bstep (se 2 (by rfl) ⟨250236, by rfl⟩ : syracuseStep 667297 = 500473) B500473
theorem B26619799 : Blo 191804 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B438281 : Blo 191804 438281 := bstep (se 2 (by rfl) ⟨164355, by rfl⟩ : syracuseStep 438281 = 328711) B328711
theorem B274537 : Blo 191804 274537 := bstep (se 2 (by rfl) ⟨102951, by rfl⟩ : syracuseStep 274537 = 205903) B205903
theorem B1651049 : Blo 191804 1651049 := bstep (se 2 (by rfl) ⟨619143, by rfl⟩ : syracuseStep 1651049 = 1238287) B1238287
theorem B274799 : Blo 191804 274799 := bstep (se 1 (by rfl) ⟨206099, by rfl⟩ : syracuseStep 274799 = 412199) B412199
theorem B438695 : Blo 191804 438695 := bstep (se 1 (by rfl) ⟨329021, by rfl⟩ : syracuseStep 438695 = 658043) B658043
theorem B438803 : Blo 191804 438803 := bstep (se 1 (by rfl) ⟨329102, by rfl⟩ : syracuseStep 438803 = 658205) B658205
theorem B438857 : Blo 191804 438857 := bstep (se 2 (by rfl) ⟨164571, by rfl⟩ : syracuseStep 438857 = 329143) B329143
theorem B1880729 : Blo 191804 1880729 := bstep (se 2 (by rfl) ⟨705273, by rfl⟩ : syracuseStep 1880729 = 1410547) B1410547
theorem B2110373 : Blo 191804 2110373 := bstep (se 4 (by rfl) ⟨197847, by rfl⟩ : syracuseStep 2110373 = 395695) B395695
theorem B930791 : Blo 191804 930791 := bstep (se 1 (by rfl) ⟨698093, by rfl⟩ : syracuseStep 930791 = 1396187) B1396187
theorem B439271 : Blo 191804 439271 := bstep (se 1 (by rfl) ⟨329453, by rfl⟩ : syracuseStep 439271 = 658907) B658907
theorem B439649 : Blo 191804 439649 := bstep (se 2 (by rfl) ⟨164868, by rfl⟩ : syracuseStep 439649 = 329737) B329737
theorem B439739 : Blo 191804 439739 := bstep (se 1 (by rfl) ⟨329804, by rfl⟩ : syracuseStep 439739 = 659609) B659609
theorem B701959 : Blo 191804 701959 := bstep (se 1 (by rfl) ⟨526469, by rfl⟩ : syracuseStep 701959 = 1052939) B1052939
theorem B439865 : Blo 191804 439865 := bstep (se 2 (by rfl) ⟨164949, by rfl⟩ : syracuseStep 439865 = 329899) B329899
theorem B243263 : Blo 191804 243263 := bstep (se 1 (by rfl) ⟨182447, by rfl⟩ : syracuseStep 243263 = 364895) B364895
theorem B702593 : Blo 191804 702593 := bstep (se 2 (by rfl) ⟨263472, by rfl⟩ : syracuseStep 702593 = 526945) B526945
theorem B440531 : Blo 191804 440531 := bstep (se 1 (by rfl) ⟨330398, by rfl⟩ : syracuseStep 440531 = 660797) B660797
theorem B2210327 : Blo 191804 2210327 := bstep (se 1 (by rfl) ⟨1657745, by rfl⟩ : syracuseStep 2210327 = 3315491) B3315491
theorem B13318769 : Blo 191804 13318769 := bstep (se 2 (by rfl) ⟨4994538, by rfl⟩ : syracuseStep 13318769 = 9989077) B9989077
theorem B244559 : Blo 191804 244559 := bstep (se 1 (by rfl) ⟨183419, by rfl⟩ : syracuseStep 244559 = 366839) B366839
theorem B310187 : Blo 191804 310187 := bstep (se 1 (by rfl) ⟨232640, by rfl⟩ : syracuseStep 310187 = 465281) B465281
theorem B244711 : Blo 191804 244711 := bstep (se 1 (by rfl) ⟨183533, by rfl⟩ : syracuseStep 244711 = 367067) B367067
theorem B6110437 : Blo 191804 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B2866747 : Blo 191804 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B310879 : Blo 191804 310879 := bstep (se 1 (by rfl) ⟨233159, by rfl⟩ : syracuseStep 310879 = 466319) B466319
theorem B736883 : Blo 191804 736883 := bstep (se 1 (by rfl) ⟨552662, by rfl⟩ : syracuseStep 736883 = 1105325) B1105325
theorem B60702605 : Blo 191804 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B835913 : Blo 191804 835913 := bstep (se 2 (by rfl) ⟨313467, by rfl⟩ : syracuseStep 835913 = 626935) B626935
theorem B410131 : Blo 191804 410131 := bstep (se 1 (by rfl) ⟨307598, by rfl⟩ : syracuseStep 410131 = 615197) B615197
theorem B705359 : Blo 191804 705359 := bstep (se 1 (by rfl) ⟨529019, by rfl⟩ : syracuseStep 705359 = 1058039) B1058039
theorem B836857 : Blo 191804 836857 := bstep (se 2 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 836857 = 627643) B627643
theorem B247151 : Blo 191804 247151 := bstep (se 1 (by rfl) ⟨185363, by rfl⟩ : syracuseStep 247151 = 370727) B370727
theorem B6768035 : Blo 191804 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B247207 : Blo 191804 247207 := bstep (se 1 (by rfl) ⟨185405, by rfl⟩ : syracuseStep 247207 = 370811) B370811
theorem B247531 : Blo 191804 247531 := bstep (se 1 (by rfl) ⟨185648, by rfl⟩ : syracuseStep 247531 = 371297) B371297
theorem B1657199 : Blo 191804 1657199 := bstep (se 1 (by rfl) ⟨1242899, by rfl⟩ : syracuseStep 1657199 = 2485799) B2485799
theorem B1100243 : Blo 191804 1100243 := bstep (se 1 (by rfl) ⟨825182, by rfl⟩ : syracuseStep 1100243 = 1650365) B1650365
theorem B346619 : Blo 191804 346619 := bstep (se 1 (by rfl) ⟨259964, by rfl⟩ : syracuseStep 346619 = 519929) B519929
theorem B3328613 : Blo 191804 3328613 := bstep (se 4 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 3328613 = 624115) B624115
theorem B740087 : Blo 191804 740087 := bstep (se 1 (by rfl) ⟨555065, by rfl⟩ : syracuseStep 740087 = 1110131) B1110131
theorem B215887 : Blo 191804 215887 := bstep (se 1 (by rfl) ⟨161915, by rfl⟩ : syracuseStep 215887 = 323831) B323831
theorem B5262515 : Blo 191804 5262515 := bstep (se 1 (by rfl) ⟨3946886, by rfl⟩ : syracuseStep 5262515 = 7893773) B7893773
theorem B216283 : Blo 191804 216283 := bstep (se 1 (by rfl) ⟨162212, by rfl⟩ : syracuseStep 216283 = 324425) B324425
theorem B838943 : Blo 191804 838943 := bstep (se 1 (by rfl) ⟨629207, by rfl⟩ : syracuseStep 838943 = 1258415) B1258415
theorem B216571 : Blo 191804 216571 := bstep (se 1 (by rfl) ⟨162428, by rfl⟩ : syracuseStep 216571 = 324857) B324857
theorem B216751 : Blo 191804 216751 := bstep (se 1 (by rfl) ⟨162563, by rfl⟩ : syracuseStep 216751 = 325127) B325127
theorem B217039 : Blo 191804 217039 := bstep (se 1 (by rfl) ⟨162779, by rfl⟩ : syracuseStep 217039 = 325559) B325559
theorem B1101883 : Blo 191804 1101883 := bstep (se 1 (by rfl) ⟨826412, by rfl⟩ : syracuseStep 1101883 = 1652825) B1652825
theorem B938155 : Blo 191804 938155 := bstep (se 1 (by rfl) ⟨703616, by rfl⟩ : syracuseStep 938155 = 1407233) B1407233
theorem B217435 : Blo 191804 217435 := bstep (se 1 (by rfl) ⟨163076, by rfl⟩ : syracuseStep 217435 = 326153) B326153
theorem B217543 : Blo 191804 217543 := bstep (se 1 (by rfl) ⟨163157, by rfl⟩ : syracuseStep 217543 = 326315) B326315
theorem B414163 : Blo 191804 414163 := bstep (se 1 (by rfl) ⟨310622, by rfl⟩ : syracuseStep 414163 = 621245) B621245
theorem B971513 : Blo 191804 971513 := bstep (se 2 (by rfl) ⟨364317, by rfl⟩ : syracuseStep 971513 = 728635) B728635
theorem B217903 : Blo 191804 217903 := bstep (se 1 (by rfl) ⟨163427, by rfl⟩ : syracuseStep 217903 = 326855) B326855
theorem B676687 : Blo 191804 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B218011 : Blo 191804 218011 := bstep (se 1 (by rfl) ⟨163508, by rfl⟩ : syracuseStep 218011 = 327017) B327017
theorem B742547 : Blo 191804 742547 := bstep (se 1 (by rfl) ⟨556910, by rfl⟩ : syracuseStep 742547 = 1113821) B1113821
theorem B218407 : Blo 191804 218407 := bstep (se 1 (by rfl) ⟨163805, by rfl⟩ : syracuseStep 218407 = 327611) B327611
theorem B218479 : Blo 191804 218479 := bstep (se 1 (by rfl) ⟨163859, by rfl⟩ : syracuseStep 218479 = 327719) B327719
theorem B1103341 : Blo 191804 1103341 := bstep (se 3 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 1103341 = 413753) B413753
theorem B218695 : Blo 191804 218695 := bstep (se 1 (by rfl) ⟨164021, by rfl⟩ : syracuseStep 218695 = 328043) B328043
theorem B2086843 : Blo 191804 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B547069 : Blo 191804 547069 := bstep (se 3 (by rfl) ⟨102575, by rfl⟩ : syracuseStep 547069 = 205151) B205151
theorem B416009 : Blo 191804 416009 := bstep (se 2 (by rfl) ⟨156003, by rfl⟩ : syracuseStep 416009 = 312007) B312007
theorem B219559 : Blo 191804 219559 := bstep (se 1 (by rfl) ⟨164669, by rfl⟩ : syracuseStep 219559 = 329339) B329339
theorem B1235519 : Blo 191804 1235519 := bstep (se 1 (by rfl) ⟨926639, by rfl⟩ : syracuseStep 1235519 = 1853279) B1853279
theorem B1661573 : Blo 191804 1661573 := bstep (se 4 (by rfl) ⟨155772, by rfl⟩ : syracuseStep 1661573 = 311545) B311545
theorem B1039229 : Blo 191804 1039229 := bstep (se 3 (by rfl) ⟨194855, by rfl⟩ : syracuseStep 1039229 = 389711) B389711
theorem B220135 : Blo 191804 220135 := bstep (se 1 (by rfl) ⟨165101, by rfl⟩ : syracuseStep 220135 = 330203) B330203
theorem B974267 : Blo 191804 974267 := bstep (se 1 (by rfl) ⟨730700, by rfl⟩ : syracuseStep 974267 = 1461401) B1461401
theorem B548345 : Blo 191804 548345 := bstep (se 2 (by rfl) ⟨205629, by rfl⟩ : syracuseStep 548345 = 411259) B411259
theorem B2777611 : Blo 191804 2777611 := bstep (se 1 (by rfl) ⟨2083208, by rfl⟩ : syracuseStep 2777611 = 4166417) B4166417
theorem B221767 : Blo 191804 221767 := bstep (se 1 (by rfl) ⟨166325, by rfl⟩ : syracuseStep 221767 = 332651) B332651
theorem B1499795 : Blo 191804 1499795 := bstep (se 1 (by rfl) ⟨1124846, by rfl⟩ : syracuseStep 1499795 = 2249693) B2249693
theorem B975563 : Blo 191804 975563 := bstep (se 1 (by rfl) ⟨731672, by rfl⟩ : syracuseStep 975563 = 1463345) B1463345
theorem B1106783 : Blo 191804 1106783 := bstep (se 1 (by rfl) ⟨830087, by rfl⟩ : syracuseStep 1106783 = 1660175) B1660175
theorem B975725 : Blo 191804 975725 := bstep (se 3 (by rfl) ⟨182948, by rfl⟩ : syracuseStep 975725 = 365897) B365897
theorem B1237979 : Blo 191804 1237979 := bstep (se 1 (by rfl) ⟨928484, by rfl⟩ : syracuseStep 1237979 = 1856969) B1856969
theorem B549985 : Blo 191804 549985 := bstep (se 2 (by rfl) ⟨206244, by rfl⟩ : syracuseStep 549985 = 412489) B412489
theorem B287963 : Blo 191804 287963 := bstep (se 1 (by rfl) ⟨215972, by rfl⟩ : syracuseStep 287963 = 431945) B431945
theorem B288137 : Blo 191804 288137 := bstep (se 2 (by rfl) ⟨108051, by rfl⟩ : syracuseStep 288137 = 216103) B216103
theorem B419489 : Blo 191804 419489 := bstep (se 2 (by rfl) ⟨157308, by rfl⟩ : syracuseStep 419489 = 314617) B314617
theorem B288491 : Blo 191804 288491 := bstep (se 1 (by rfl) ⟨216368, by rfl⟩ : syracuseStep 288491 = 432737) B432737
theorem B288719 : Blo 191804 288719 := bstep (se 1 (by rfl) ⟨216539, by rfl⟩ : syracuseStep 288719 = 433079) B433079
theorem B289115 : Blo 191804 289115 := bstep (se 1 (by rfl) ⟨216836, by rfl⟩ : syracuseStep 289115 = 433673) B433673
theorem B289343 : Blo 191804 289343 := bstep (se 1 (by rfl) ⟨217007, by rfl⟩ : syracuseStep 289343 = 434015) B434015
theorem B485959 : Blo 191804 485959 := bstep (se 1 (by rfl) ⟨364469, by rfl⟩ : syracuseStep 485959 = 728939) B728939
theorem B649835 : Blo 191804 649835 := bstep (se 1 (by rfl) ⟨487376, by rfl⟩ : syracuseStep 649835 = 974753) B974753
theorem B3369595 : Blo 191804 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B486071 : Blo 191804 486071 := bstep (se 1 (by rfl) ⟨364553, by rfl⟩ : syracuseStep 486071 = 729107) B729107
theorem B289463 : Blo 191804 289463 := bstep (se 1 (by rfl) ⟨217097, by rfl⟩ : syracuseStep 289463 = 434195) B434195
theorem B289691 : Blo 191804 289691 := bstep (se 1 (by rfl) ⟨217268, by rfl⟩ : syracuseStep 289691 = 434537) B434537
theorem B552059 : Blo 191804 552059 := bstep (se 1 (by rfl) ⟨414044, by rfl⟩ : syracuseStep 552059 = 828089) B828089
theorem B650429 : Blo 191804 650429 := bstep (se 3 (by rfl) ⟨121955, by rfl⟩ : syracuseStep 650429 = 243911) B243911
theorem B290087 : Blo 191804 290087 := bstep (se 1 (by rfl) ⟨217565, by rfl⟩ : syracuseStep 290087 = 435131) B435131
theorem B191835 : Blo 191804 191835 := bstep (se 1 (by rfl) ⟨143876, by rfl⟩ : syracuseStep 191835 = 287753) B287753
theorem B191855 : Blo 191804 191855 := bstep (se 1 (by rfl) ⟨143891, by rfl⟩ : syracuseStep 191855 = 287783) B287783
theorem B290171 : Blo 191804 290171 := bstep (se 1 (by rfl) ⟨217628, by rfl⟩ : syracuseStep 290171 = 435257) B435257
theorem B191911 : Blo 191804 191911 := bstep (se 1 (by rfl) ⟨143933, by rfl⟩ : syracuseStep 191911 = 287867) B287867
theorem B1109447 : Blo 191804 1109447 := bstep (se 1 (by rfl) ⟨832085, by rfl⟩ : syracuseStep 1109447 = 1664171) B1664171
theorem B290297 : Blo 191804 290297 := bstep (se 2 (by rfl) ⟨108861, by rfl⟩ : syracuseStep 290297 = 217723) B217723
theorem B191995 : Blo 191804 191995 := bstep (se 1 (by rfl) ⟨143996, by rfl⟩ : syracuseStep 191995 = 287993) B287993
theorem B192063 : Blo 191804 192063 := bstep (se 1 (by rfl) ⟨144047, by rfl⟩ : syracuseStep 192063 = 288095) B288095
theorem B192071 : Blo 191804 192071 := bstep (se 1 (by rfl) ⟨144053, by rfl⟩ : syracuseStep 192071 = 288107) B288107
theorem B618067 : Blo 191804 618067 := bstep (se 1 (by rfl) ⟨463550, by rfl⟩ : syracuseStep 618067 = 927101) B927101
theorem B290399 : Blo 191804 290399 := bstep (se 1 (by rfl) ⟨217799, by rfl⟩ : syracuseStep 290399 = 435599) B435599
theorem B487073 : Blo 191804 487073 := bstep (se 2 (by rfl) ⟨182652, by rfl⟩ : syracuseStep 487073 = 365305) B365305
theorem B978641 : Blo 191804 978641 := bstep (se 2 (by rfl) ⟨366990, by rfl⟩ : syracuseStep 978641 = 733981) B733981
theorem B192223 : Blo 191804 192223 := bstep (se 1 (by rfl) ⟨144167, by rfl⟩ : syracuseStep 192223 = 288335) B288335
theorem B192303 : Blo 191804 192303 := bstep (se 1 (by rfl) ⟨144227, by rfl⟩ : syracuseStep 192303 = 288455) B288455
theorem B519983 : Blo 191804 519983 := bstep (se 1 (by rfl) ⟨389987, by rfl⟩ : syracuseStep 519983 = 779975) B779975
theorem B290615 : Blo 191804 290615 := bstep (se 1 (by rfl) ⟨217961, by rfl⟩ : syracuseStep 290615 = 435923) B435923
theorem B1044353 : Blo 191804 1044353 := bstep (se 2 (by rfl) ⟨391632, by rfl⟩ : syracuseStep 1044353 = 783265) B783265
theorem B192411 : Blo 191804 192411 := bstep (se 1 (by rfl) ⟨144308, by rfl⟩ : syracuseStep 192411 = 288617) B288617
theorem B192463 : Blo 191804 192463 := bstep (se 1 (by rfl) ⟨144347, by rfl⟩ : syracuseStep 192463 = 288695) B288695
theorem B192487 : Blo 191804 192487 := bstep (se 1 (by rfl) ⟨144365, by rfl⟩ : syracuseStep 192487 = 288731) B288731
theorem B323689 : Blo 191804 323689 := bstep (se 2 (by rfl) ⟨121383, by rfl⟩ : syracuseStep 323689 = 242767) B242767
theorem B487529 : Blo 191804 487529 := bstep (se 2 (by rfl) ⟨182823, by rfl⟩ : syracuseStep 487529 = 365647) B365647
theorem B290921 : Blo 191804 290921 := bstep (se 2 (by rfl) ⟨109095, by rfl⟩ : syracuseStep 290921 = 218191) B218191
theorem B1470635 : Blo 191804 1470635 := bstep (se 1 (by rfl) ⟨1102976, by rfl⟩ : syracuseStep 1470635 = 2205953) B2205953
theorem B192799 : Blo 191804 192799 := bstep (se 1 (by rfl) ⟨144599, by rfl⟩ : syracuseStep 192799 = 289199) B289199
theorem B192859 : Blo 191804 192859 := bstep (se 1 (by rfl) ⟨144644, by rfl⟩ : syracuseStep 192859 = 289289) B289289
theorem B1864043 : Blo 191804 1864043 := bstep (se 1 (by rfl) ⟨1398032, by rfl⟩ : syracuseStep 1864043 = 2796065) B2796065
theorem B4223339 : Blo 191804 4223339 := bstep (se 1 (by rfl) ⟨3167504, by rfl⟩ : syracuseStep 4223339 = 6335009) B6335009
theorem B192879 : Blo 191804 192879 := bstep (se 1 (by rfl) ⟨144659, by rfl⟩ : syracuseStep 192879 = 289319) B289319
theorem B192935 : Blo 191804 192935 := bstep (se 1 (by rfl) ⟨144701, by rfl⟩ : syracuseStep 192935 = 289403) B289403
theorem B291239 : Blo 191804 291239 := bstep (se 1 (by rfl) ⟨218429, by rfl⟩ : syracuseStep 291239 = 436859) B436859
theorem B520673 : Blo 191804 520673 := bstep (se 2 (by rfl) ⟨195252, by rfl⟩ : syracuseStep 520673 = 390505) B390505
theorem B193019 : Blo 191804 193019 := bstep (se 1 (by rfl) ⟨144764, by rfl⟩ : syracuseStep 193019 = 289529) B289529
theorem B291323 : Blo 191804 291323 := bstep (se 1 (by rfl) ⟨218492, by rfl⟩ : syracuseStep 291323 = 436985) B436985
theorem B193087 : Blo 191804 193087 := bstep (se 1 (by rfl) ⟨144815, by rfl⟩ : syracuseStep 193087 = 289631) B289631
theorem B193095 : Blo 191804 193095 := bstep (se 1 (by rfl) ⟨144821, by rfl⟩ : syracuseStep 193095 = 289643) B289643
theorem B488015 : Blo 191804 488015 := bstep (se 1 (by rfl) ⟨366011, by rfl⟩ : syracuseStep 488015 = 732023) B732023
theorem B520825 : Blo 191804 520825 := bstep (se 2 (by rfl) ⟨195309, by rfl⟩ : syracuseStep 520825 = 390619) B390619
theorem B291449 : Blo 191804 291449 := bstep (se 2 (by rfl) ⟨109293, by rfl⟩ : syracuseStep 291449 = 218587) B218587
theorem B291503 : Blo 191804 291503 := bstep (se 1 (by rfl) ⟨218627, by rfl⟩ : syracuseStep 291503 = 437255) B437255
theorem B193247 : Blo 191804 193247 := bstep (se 1 (by rfl) ⟨144935, by rfl⟩ : syracuseStep 193247 = 289871) B289871
theorem B291551 : Blo 191804 291551 := bstep (se 1 (by rfl) ⟨218663, by rfl⟩ : syracuseStep 291551 = 437327) B437327
theorem B13202189 : Blo 191804 13202189 := bstep (se 3 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 13202189 = 4950821) B4950821
theorem B193327 : Blo 191804 193327 := bstep (se 1 (by rfl) ⟨144995, by rfl⟩ : syracuseStep 193327 = 289991) B289991
theorem B193435 : Blo 191804 193435 := bstep (se 1 (by rfl) ⟨145076, by rfl⟩ : syracuseStep 193435 = 290153) B290153
theorem B193487 : Blo 191804 193487 := bstep (se 1 (by rfl) ⟨145115, by rfl⟩ : syracuseStep 193487 = 290231) B290231
theorem B291815 : Blo 191804 291815 := bstep (se 1 (by rfl) ⟨218861, by rfl⟩ : syracuseStep 291815 = 437723) B437723
theorem B193511 : Blo 191804 193511 := bstep (se 1 (by rfl) ⟨145133, by rfl⟩ : syracuseStep 193511 = 290267) B290267
theorem B6222905 : Blo 191804 6222905 := bstep (se 2 (by rfl) ⟨2333589, by rfl⟩ : syracuseStep 6222905 = 4667179) B4667179
theorem B488663 : Blo 191804 488663 := bstep (se 1 (by rfl) ⟨366497, by rfl⟩ : syracuseStep 488663 = 732995) B732995
theorem B292073 : Blo 191804 292073 := bstep (se 2 (by rfl) ⟨109527, by rfl⟩ : syracuseStep 292073 = 219055) B219055
theorem B193823 : Blo 191804 193823 := bstep (se 1 (by rfl) ⟨145367, by rfl⟩ : syracuseStep 193823 = 290735) B290735
theorem B292127 : Blo 191804 292127 := bstep (se 1 (by rfl) ⟨219095, by rfl⟩ : syracuseStep 292127 = 438191) B438191
theorem B193883 : Blo 191804 193883 := bstep (se 1 (by rfl) ⟨145412, by rfl⟩ : syracuseStep 193883 = 290825) B290825
theorem B193903 : Blo 191804 193903 := bstep (se 1 (by rfl) ⟨145427, by rfl⟩ : syracuseStep 193903 = 290855) B290855
theorem B193959 : Blo 191804 193959 := bstep (se 1 (by rfl) ⟨145469, by rfl⟩ : syracuseStep 193959 = 290939) B290939
theorem B1668545 : Blo 191804 1668545 := bstep (se 2 (by rfl) ⟨625704, by rfl⟩ : syracuseStep 1668545 = 1251409) B1251409
theorem B292295 : Blo 191804 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B194043 : Blo 191804 194043 := bstep (se 1 (by rfl) ⟨145532, by rfl⟩ : syracuseStep 194043 = 291065) B291065
theorem B1111589 : Blo 191804 1111589 := bstep (se 4 (by rfl) ⟨104211, by rfl⟩ : syracuseStep 1111589 = 208423) B208423
theorem B489017 : Blo 191804 489017 := bstep (se 2 (by rfl) ⟨183381, by rfl⟩ : syracuseStep 489017 = 366763) B366763
theorem B194111 : Blo 191804 194111 := bstep (se 1 (by rfl) ⟨145583, by rfl⟩ : syracuseStep 194111 = 291167) B291167
theorem B194119 : Blo 191804 194119 := bstep (se 1 (by rfl) ⟨145589, by rfl⟩ : syracuseStep 194119 = 291179) B291179
theorem B1046105 : Blo 191804 1046105 := bstep (se 2 (by rfl) ⟨392289, by rfl⟩ : syracuseStep 1046105 = 784579) B784579
theorem B521885 : Blo 191804 521885 := bstep (se 3 (by rfl) ⟨97853, by rfl⟩ : syracuseStep 521885 = 195707) B195707
theorem B194271 : Blo 191804 194271 := bstep (se 1 (by rfl) ⟨145703, by rfl⟩ : syracuseStep 194271 = 291407) B291407
theorem B325417 : Blo 191804 325417 := bstep (se 2 (by rfl) ⟨122031, by rfl⟩ : syracuseStep 325417 = 244063) B244063
theorem B292649 : Blo 191804 292649 := bstep (se 2 (by rfl) ⟨109743, by rfl⟩ : syracuseStep 292649 = 219487) B219487
theorem B194351 : Blo 191804 194351 := bstep (se 1 (by rfl) ⟨145763, by rfl⟩ : syracuseStep 194351 = 291527) B291527
theorem B292655 : Blo 191804 292655 := bstep (se 1 (by rfl) ⟨219491, by rfl⟩ : syracuseStep 292655 = 438983) B438983
theorem B194459 : Blo 191804 194459 := bstep (se 1 (by rfl) ⟨145844, by rfl⟩ : syracuseStep 194459 = 291689) B291689
theorem B194511 : Blo 191804 194511 := bstep (se 1 (by rfl) ⟨145883, by rfl⟩ : syracuseStep 194511 = 291767) B291767
theorem B194535 : Blo 191804 194535 := bstep (se 1 (by rfl) ⟨145901, by rfl⟩ : syracuseStep 194535 = 291803) B291803
theorem B653345 : Blo 191804 653345 := bstep (se 2 (by rfl) ⟨245004, by rfl⟩ : syracuseStep 653345 = 490009) B490009
theorem B981071 : Blo 191804 981071 := bstep (se 1 (by rfl) ⟨735803, by rfl⟩ : syracuseStep 981071 = 1471607) B1471607
theorem B293129 : Blo 191804 293129 := bstep (se 2 (by rfl) ⟨109923, by rfl⟩ : syracuseStep 293129 = 219847) B219847
theorem B194847 : Blo 191804 194847 := bstep (se 1 (by rfl) ⟨146135, by rfl⟩ : syracuseStep 194847 = 292271) B292271
theorem B2357579 : Blo 191804 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B194907 : Blo 191804 194907 := bstep (se 1 (by rfl) ⟨146180, by rfl⟩ : syracuseStep 194907 = 292361) B292361
theorem B194927 : Blo 191804 194927 := bstep (se 1 (by rfl) ⟨146195, by rfl⟩ : syracuseStep 194927 = 292391) B292391
theorem B293231 : Blo 191804 293231 := bstep (se 1 (by rfl) ⟨219923, by rfl⟩ : syracuseStep 293231 = 439847) B439847
theorem B194983 : Blo 191804 194983 := bstep (se 1 (by rfl) ⟨146237, by rfl⟩ : syracuseStep 194983 = 292475) B292475
theorem B195067 : Blo 191804 195067 := bstep (se 1 (by rfl) ⟨146300, by rfl⟩ : syracuseStep 195067 = 292601) B292601
theorem B1112615 : Blo 191804 1112615 := bstep (se 1 (by rfl) ⟨834461, by rfl⟩ : syracuseStep 1112615 = 1668923) B1668923
theorem B326207 : Blo 191804 326207 := bstep (se 1 (by rfl) ⟨244655, by rfl⟩ : syracuseStep 326207 = 489311) B489311
theorem B195135 : Blo 191804 195135 := bstep (se 1 (by rfl) ⟨146351, by rfl⟩ : syracuseStep 195135 = 292703) B292703
theorem B195143 : Blo 191804 195143 := bstep (se 1 (by rfl) ⟨146357, by rfl⟩ : syracuseStep 195143 = 292715) B292715
theorem B293447 : Blo 191804 293447 := bstep (se 1 (by rfl) ⟨220085, by rfl⟩ : syracuseStep 293447 = 440171) B440171
theorem B391787 : Blo 191804 391787 := bstep (se 1 (by rfl) ⟨293840, by rfl⟩ : syracuseStep 391787 = 587681) B587681
theorem B293483 : Blo 191804 293483 := bstep (se 1 (by rfl) ⟨220112, by rfl⟩ : syracuseStep 293483 = 440225) B440225
theorem B195295 : Blo 191804 195295 := bstep (se 1 (by rfl) ⟨146471, by rfl⟩ : syracuseStep 195295 = 292943) B292943
theorem B195375 : Blo 191804 195375 := bstep (se 1 (by rfl) ⟨146531, by rfl⟩ : syracuseStep 195375 = 293063) B293063
theorem B195483 : Blo 191804 195483 := bstep (se 1 (by rfl) ⟨146612, by rfl⟩ : syracuseStep 195483 = 293225) B293225
theorem B195535 : Blo 191804 195535 := bstep (se 1 (by rfl) ⟨146651, by rfl⟩ : syracuseStep 195535 = 293303) B293303
theorem B195559 : Blo 191804 195559 := bstep (se 1 (by rfl) ⟨146669, by rfl⟩ : syracuseStep 195559 = 293339) B293339
theorem B5012603 : Blo 191804 5012603 := bstep (se 1 (by rfl) ⟨3759452, by rfl⟩ : syracuseStep 5012603 = 7518905) B7518905
theorem B982205 : Blo 191804 982205 := bstep (se 3 (by rfl) ⟨184163, by rfl⟩ : syracuseStep 982205 = 368327) B368327
theorem B392411 : Blo 191804 392411 := bstep (se 1 (by rfl) ⟨294308, by rfl⟩ : syracuseStep 392411 = 588617) B588617
theorem B326875 : Blo 191804 326875 := bstep (se 1 (by rfl) ⟨245156, by rfl⟩ : syracuseStep 326875 = 490313) B490313
theorem B491305 : Blo 191804 491305 := bstep (se 2 (by rfl) ⟨184239, by rfl⟩ : syracuseStep 491305 = 368479) B368479
theorem B327631 : Blo 191804 327631 := bstep (se 1 (by rfl) ⟨245723, by rfl⟩ : syracuseStep 327631 = 491447) B491447
theorem B10485811 : Blo 191804 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B557275 : Blo 191804 557275 := bstep (se 1 (by rfl) ⟨417956, by rfl⟩ : syracuseStep 557275 = 835913) B835913
theorem B328063 : Blo 191804 328063 := bstep (se 1 (by rfl) ⟨246047, by rfl⟩ : syracuseStep 328063 = 492095) B492095
theorem B262759 : Blo 191804 262759 := bstep (se 1 (by rfl) ⟨197069, by rfl⟩ : syracuseStep 262759 = 394139) B394139
theorem B3703481 : Blo 191804 3703481 := bstep (se 2 (by rfl) ⟨1388805, by rfl⟩ : syracuseStep 3703481 = 2777611) B2777611
theorem B328495 : Blo 191804 328495 := bstep (se 1 (by rfl) ⟨246371, by rfl⟩ : syracuseStep 328495 = 492743) B492743
theorem B4719545 : Blo 191804 4719545 := bstep (se 2 (by rfl) ⟨1769829, by rfl⟩ : syracuseStep 4719545 = 3539659) B3539659
theorem B656747 : Blo 191804 656747 := bstep (se 1 (by rfl) ⟨492560, by rfl⟩ : syracuseStep 656747 = 985121) B985121
theorem B656855 : Blo 191804 656855 := bstep (se 1 (by rfl) ⟨492641, by rfl⟩ : syracuseStep 656855 = 985283) B985283
theorem B657017 : Blo 191804 657017 := bstep (se 2 (by rfl) ⟨246381, by rfl⟩ : syracuseStep 657017 = 492763) B492763
theorem B329467 : Blo 191804 329467 := bstep (se 1 (by rfl) ⟨247100, by rfl⟩ : syracuseStep 329467 = 494201) B494201
theorem B493391 : Blo 191804 493391 := bstep (se 1 (by rfl) ⟨370043, by rfl⟩ : syracuseStep 493391 = 740087) B740087
theorem B329609 : Blo 191804 329609 := bstep (se 2 (by rfl) ⟨123603, by rfl⟩ : syracuseStep 329609 = 247207) B247207
theorem B1771429 : Blo 191804 1771429 := bstep (se 4 (by rfl) ⟨166071, by rfl⟩ : syracuseStep 1771429 = 332143) B332143
theorem B3508343 : Blo 191804 3508343 := bstep (se 1 (by rfl) ⟨2631257, by rfl⟩ : syracuseStep 3508343 = 5262515) B5262515
theorem B559295 : Blo 191804 559295 := bstep (se 1 (by rfl) ⟨419471, by rfl⟩ : syracuseStep 559295 = 838943) B838943
theorem B330041 : Blo 191804 330041 := bstep (se 2 (by rfl) ⟨123765, by rfl⟩ : syracuseStep 330041 = 247531) B247531
theorem B985607 : Blo 191804 985607 := bstep (se 1 (by rfl) ⟨739205, by rfl⟩ : syracuseStep 985607 = 1478411) B1478411
theorem B986087 : Blo 191804 986087 := bstep (se 1 (by rfl) ⟨739565, by rfl⟩ : syracuseStep 986087 = 1479131) B1479131
theorem B1182757 : Blo 191804 1182757 := bstep (se 4 (by rfl) ⟨110883, by rfl⟩ : syracuseStep 1182757 = 221767) B221767
theorem B10325069 : Blo 191804 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B658529 : Blo 191804 658529 := bstep (se 2 (by rfl) ⟨246948, by rfl⟩ : syracuseStep 658529 = 493897) B493897
theorem B1248695 : Blo 191804 1248695 := bstep (se 1 (by rfl) ⟨936521, by rfl⟩ : syracuseStep 1248695 = 1873043) B1873043
theorem B495031 : Blo 191804 495031 := bstep (se 1 (by rfl) ⟨371273, by rfl⟩ : syracuseStep 495031 = 742547) B742547
theorem B4492793 : Blo 191804 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B2100853 : Blo 191804 2100853 := bstep (se 5 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 2100853 = 196955) B196955
theorem B659069 : Blo 191804 659069 := bstep (se 3 (by rfl) ⟨123575, by rfl⟩ : syracuseStep 659069 = 247151) B247151
theorem B1117891 : Blo 191804 1117891 := bstep (se 1 (by rfl) ⟨838418, by rfl⟩ : syracuseStep 1117891 = 1676837) B1676837
theorem B364409 : Blo 191804 364409 := bstep (se 2 (by rfl) ⟨136653, by rfl⟩ : syracuseStep 364409 = 273307) B273307
theorem B659339 : Blo 191804 659339 := bstep (se 1 (by rfl) ⟨494504, by rfl⟩ : syracuseStep 659339 = 989009) B989009
theorem B987389 : Blo 191804 987389 := bstep (se 3 (by rfl) ⟨185135, by rfl⟩ : syracuseStep 987389 = 370271) B370271
theorem B823679 : Blo 191804 823679 := bstep (se 1 (by rfl) ⟨617759, by rfl⟩ : syracuseStep 823679 = 1235519) B1235519
theorem B659879 : Blo 191804 659879 := bstep (se 1 (by rfl) ⟨494909, by rfl⟩ : syracuseStep 659879 = 989819) B989819
theorem B692819 : Blo 191804 692819 := bstep (se 1 (by rfl) ⟨519614, by rfl⟩ : syracuseStep 692819 = 1039229) B1039229
theorem B824089 : Blo 191804 824089 := bstep (se 2 (by rfl) ⟨309033, by rfl⟩ : syracuseStep 824089 = 618067) B618067
theorem B529193 : Blo 191804 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B365563 : Blo 191804 365563 := bstep (se 1 (by rfl) ⟨274172, by rfl⟩ : syracuseStep 365563 = 548345) B548345
theorem B988199 : Blo 191804 988199 := bstep (se 1 (by rfl) ⟨741149, by rfl⟩ : syracuseStep 988199 = 1482299) B1482299
theorem B35493065 : Blo 191804 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B4199633 : Blo 191804 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B1054043 : Blo 191804 1054043 := bstep (se 1 (by rfl) ⟨790532, by rfl⟩ : syracuseStep 1054043 = 1581065) B1581065
theorem B431585 : Blo 191804 431585 := bstep (se 2 (by rfl) ⟨161844, by rfl⟩ : syracuseStep 431585 = 323689) B323689
theorem B366049 : Blo 191804 366049 := bstep (se 2 (by rfl) ⟨137268, by rfl⟩ : syracuseStep 366049 = 274537) B274537
theorem B1250873 : Blo 191804 1250873 := bstep (se 2 (by rfl) ⟨469077, by rfl⟩ : syracuseStep 1250873 = 938155) B938155
theorem B825319 : Blo 191804 825319 := bstep (se 1 (by rfl) ⟨618989, by rfl⟩ : syracuseStep 825319 = 1237979) B1237979
theorem B694433 : Blo 191804 694433 := bstep (se 2 (by rfl) ⟨260412, by rfl⟩ : syracuseStep 694433 = 520825) B520825
theorem B1055099 : Blo 191804 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B4463237 : Blo 191804 4463237 := bstep (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) B836857
theorem B924317 : Blo 191804 924317 := bstep (se 3 (by rfl) ⟨173309, by rfl⟩ : syracuseStep 924317 = 346619) B346619
theorem B924641 : Blo 191804 924641 := bstep (se 2 (by rfl) ⟨346740, by rfl⟩ : syracuseStep 924641 = 693481) B693481
theorem B433223 : Blo 191804 433223 := bstep (se 1 (by rfl) ⟨324917, by rfl⟩ : syracuseStep 433223 = 649835) B649835
theorem B3710245 : Blo 191804 3710245 := bstep (se 4 (by rfl) ⟨347835, by rfl⟩ : syracuseStep 3710245 = 695671) B695671
theorem B368039 : Blo 191804 368039 := bstep (se 1 (by rfl) ⟨276029, by rfl⟩ : syracuseStep 368039 = 552059) B552059
theorem B433619 : Blo 191804 433619 := bstep (se 1 (by rfl) ⟨325214, by rfl⟩ : syracuseStep 433619 = 650429) B650429
theorem B433889 : Blo 191804 433889 := bstep (se 2 (by rfl) ⟨162708, by rfl⟩ : syracuseStep 433889 = 325417) B325417
theorem B827165 : Blo 191804 827165 := bstep (se 3 (by rfl) ⟨155093, by rfl⟩ : syracuseStep 827165 = 310187) B310187
theorem B729425 : Blo 191804 729425 := bstep (se 2 (by rfl) ⟨273534, by rfl⟩ : syracuseStep 729425 = 547069) B547069
theorem B1253819 : Blo 191804 1253819 := bstep (se 1 (by rfl) ⟨940364, by rfl⟩ : syracuseStep 1253819 = 1880729) B1880729
theorem B697403 : Blo 191804 697403 := bstep (se 1 (by rfl) ⟨523052, by rfl⟩ : syracuseStep 697403 = 1046105) B1046105
theorem B435563 : Blo 191804 435563 := bstep (se 1 (by rfl) ⟨326672, by rfl⟩ : syracuseStep 435563 = 653345) B653345
theorem B468395 : Blo 191804 468395 := bstep (se 1 (by rfl) ⟨351296, by rfl⟩ : syracuseStep 468395 = 702593) B702593
theorem B435833 : Blo 191804 435833 := bstep (se 2 (by rfl) ⟨163437, by rfl⟩ : syracuseStep 435833 = 326875) B326875
theorem B1845281 : Blo 191804 1845281 := bstep (se 2 (by rfl) ⟨691980, by rfl⟩ : syracuseStep 1845281 = 1383961) B1383961
theorem B436841 : Blo 191804 436841 := bstep (se 2 (by rfl) ⟨163815, by rfl⟩ : syracuseStep 436841 = 327631) B327631
theorem B437471 : Blo 191804 437471 := bstep (se 1 (by rfl) ⟨328103, by rfl⟩ : syracuseStep 437471 = 656207) B656207
theorem B437687 : Blo 191804 437687 := bstep (se 1 (by rfl) ⟨328265, by rfl⟩ : syracuseStep 437687 = 656531) B656531
theorem B437867 : Blo 191804 437867 := bstep (se 1 (by rfl) ⟨328400, by rfl⟩ : syracuseStep 437867 = 656801) B656801
theorem B732797 : Blo 191804 732797 := bstep (se 3 (by rfl) ⟨137399, by rfl⟩ : syracuseStep 732797 = 274799) B274799
theorem B438137 : Blo 191804 438137 := bstep (se 2 (by rfl) ⟨164301, by rfl⟩ : syracuseStep 438137 = 328603) B328603
theorem B1388461 : Blo 191804 1388461 := bstep (se 3 (by rfl) ⟨260336, by rfl⟩ : syracuseStep 1388461 = 520673) B520673
theorem B831455 : Blo 191804 831455 := bstep (se 1 (by rfl) ⟨623591, by rfl⟩ : syracuseStep 831455 = 1247183) B1247183
theorem B2404403 : Blo 191804 2404403 := bstep (se 1 (by rfl) ⟨1803302, by rfl⟩ : syracuseStep 2404403 = 3606605) B3606605
theorem B733313 : Blo 191804 733313 := bstep (se 2 (by rfl) ⟨274992, by rfl⟩ : syracuseStep 733313 = 549985) B549985
theorem B733495 : Blo 191804 733495 := bstep (se 1 (by rfl) ⟨550121, by rfl⟩ : syracuseStep 733495 = 1100243) B1100243
theorem B308009 : Blo 191804 308009 := bstep (se 2 (by rfl) ⟨115503, by rfl⟩ : syracuseStep 308009 = 231007) B231007
theorem B1880957 : Blo 191804 1880957 := bstep (se 3 (by rfl) ⟨352679, by rfl⟩ : syracuseStep 1880957 = 705359) B705359
theorem B832427 : Blo 191804 832427 := bstep (se 1 (by rfl) ⟨624320, by rfl⟩ : syracuseStep 832427 = 1248641) B1248641
theorem B2208869 : Blo 191804 2208869 := bstep (se 4 (by rfl) ⟨207081, by rfl⟩ : syracuseStep 2208869 = 414163) B414163
theorem B1881265 : Blo 191804 1881265 := bstep (se 2 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 1881265 = 1410949) B1410949
theorem B2504357 : Blo 191804 2504357 := bstep (se 4 (by rfl) ⟨234783, by rfl⟩ : syracuseStep 2504357 = 469567) B469567
theorem B439991 : Blo 191804 439991 := bstep (se 1 (by rfl) ⟨329993, by rfl⟩ : syracuseStep 439991 = 659987) B659987
theorem B309239 : Blo 191804 309239 := bstep (se 1 (by rfl) ⟨231929, by rfl⟩ : syracuseStep 309239 = 463859) B463859
theorem B834067 : Blo 191804 834067 := bstep (se 1 (by rfl) ⟨625550, by rfl⟩ : syracuseStep 834067 = 1251101) B1251101
theorem B277339 : Blo 191804 277339 := bstep (se 1 (by rfl) ⟨208004, by rfl⟩ : syracuseStep 277339 = 416009) B416009
theorem B277625 : Blo 191804 277625 := bstep (se 2 (by rfl) ⟨104109, by rfl⟩ : syracuseStep 277625 = 208219) B208219
theorem B310495 : Blo 191804 310495 := bstep (se 1 (by rfl) ⟨232871, by rfl⟩ : syracuseStep 310495 = 465743) B465743
theorem B638237 : Blo 191804 638237 := bstep (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) B239339
theorem B703975 : Blo 191804 703975 := bstep (se 1 (by rfl) ⟨527981, by rfl⟩ : syracuseStep 703975 = 1055963) B1055963
theorem B999863 : Blo 191804 999863 := bstep (se 1 (by rfl) ⟨749897, by rfl⟩ : syracuseStep 999863 = 1499795) B1499795
theorem B737855 : Blo 191804 737855 := bstep (se 1 (by rfl) ⟨553391, by rfl⟩ : syracuseStep 737855 = 1106783) B1106783
theorem B705131 : Blo 191804 705131 := bstep (se 1 (by rfl) ⟨528848, by rfl⟩ : syracuseStep 705131 = 1057697) B1057697
theorem B902249 : Blo 191804 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B279659 : Blo 191804 279659 := bstep (se 1 (by rfl) ⟨209744, by rfl⟩ : syracuseStep 279659 = 419489) B419489
theorem B1098967 : Blo 191804 1098967 := bstep (se 1 (by rfl) ⟨824225, by rfl⟩ : syracuseStep 1098967 = 1648451) B1648451
theorem B1230497 : Blo 191804 1230497 := bstep (se 2 (by rfl) ⟨461436, by rfl⟩ : syracuseStep 1230497 = 922873) B922873
theorem B935945 : Blo 191804 935945 := bstep (se 2 (by rfl) ⟨350979, by rfl⟩ : syracuseStep 935945 = 701959) B701959
theorem B739631 : Blo 191804 739631 := bstep (se 1 (by rfl) ⟨554723, by rfl⟩ : syracuseStep 739631 = 1109447) B1109447
theorem B346655 : Blo 191804 346655 := bstep (se 1 (by rfl) ⟨259991, by rfl⟩ : syracuseStep 346655 = 519983) B519983
theorem B1428101 : Blo 191804 1428101 := bstep (se 4 (by rfl) ⟨133884, by rfl⟩ : syracuseStep 1428101 = 267769) B267769
theorem B1100699 : Blo 191804 1100699 := bstep (se 1 (by rfl) ⟨825524, by rfl⟩ : syracuseStep 1100699 = 1651049) B1651049
theorem B8801459 : Blo 191804 8801459 := bstep (se 1 (by rfl) ⟨6601094, by rfl⟩ : syracuseStep 8801459 = 13202189) B13202189
theorem B4148603 : Blo 191804 4148603 := bstep (se 1 (by rfl) ⟨3111452, by rfl⟩ : syracuseStep 4148603 = 6222905) B6222905
theorem B3558917 : Blo 191804 3558917 := bstep (se 4 (by rfl) ⟨333648, by rfl⟩ : syracuseStep 3558917 = 667297) B667297
theorem B741059 : Blo 191804 741059 := bstep (se 1 (by rfl) ⟨555794, by rfl⟩ : syracuseStep 741059 = 1111589) B1111589
theorem B347923 : Blo 191804 347923 := bstep (se 1 (by rfl) ⟨260942, by rfl⟩ : syracuseStep 347923 = 521885) B521885
theorem B8147249 : Blo 191804 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B741743 : Blo 191804 741743 := bstep (se 1 (by rfl) ⟨556307, by rfl⟩ : syracuseStep 741743 = 1112615) B1112615
theorem B217471 : Blo 191804 217471 := bstep (se 1 (by rfl) ⟨163103, by rfl⟩ : syracuseStep 217471 = 326207) B326207
theorem B3822329 : Blo 191804 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B414505 : Blo 191804 414505 := bstep (se 2 (by rfl) ⟨155439, by rfl⟩ : syracuseStep 414505 = 310879) B310879
theorem B2413577 : Blo 191804 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B546203 : Blo 191804 546203 := bstep (se 1 (by rfl) ⟨409652, by rfl⟩ : syracuseStep 546203 = 819305) B819305
theorem B218875 : Blo 191804 218875 := bstep (se 1 (by rfl) ⟨164156, by rfl⟩ : syracuseStep 218875 = 328313) B328313
theorem B218911 : Blo 191804 218911 := bstep (se 1 (by rfl) ⟨164183, by rfl⟩ : syracuseStep 218911 = 328367) B328367
theorem B546841 : Blo 191804 546841 := bstep (se 2 (by rfl) ⟨205065, by rfl⟩ : syracuseStep 546841 = 410131) B410131
theorem B4512023 : Blo 191804 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B547195 : Blo 191804 547195 := bstep (se 1 (by rfl) ⟨410396, by rfl⟩ : syracuseStep 547195 = 820793) B820793
theorem B744275 : Blo 191804 744275 := bstep (se 1 (by rfl) ⟨558206, by rfl⟩ : syracuseStep 744275 = 1116413) B1116413
theorem B351059 : Blo 191804 351059 := bstep (se 1 (by rfl) ⟨263294, by rfl⟩ : syracuseStep 351059 = 526589) B526589
theorem B1071955 : Blo 191804 1071955 := bstep (se 1 (by rfl) ⟨803966, by rfl⟩ : syracuseStep 1071955 = 1607933) B1607933
theorem B1104799 : Blo 191804 1104799 := bstep (se 1 (by rfl) ⟨828599, by rfl⟩ : syracuseStep 1104799 = 1657199) B1657199
theorem B220063 : Blo 191804 220063 := bstep (se 1 (by rfl) ⟨165047, by rfl⟩ : syracuseStep 220063 = 330095) B330095
theorem B220207 : Blo 191804 220207 := bstep (se 1 (by rfl) ⟨165155, by rfl⟩ : syracuseStep 220207 = 330311) B330311
theorem B2219075 : Blo 191804 2219075 := bstep (se 1 (by rfl) ⟨1664306, by rfl⟩ : syracuseStep 2219075 = 3328613) B3328613
theorem B1400399 : Blo 191804 1400399 := bstep (se 1 (by rfl) ⟨1050299, by rfl⟩ : syracuseStep 1400399 = 2100599) B2100599
theorem B2482109 : Blo 191804 2482109 := bstep (se 3 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 2482109 = 930791) B930791
theorem B1106257 : Blo 191804 1106257 := bstep (se 2 (by rfl) ⟨414846, by rfl⟩ : syracuseStep 1106257 = 829693) B829693
theorem B647675 : Blo 191804 647675 := bstep (se 1 (by rfl) ⟨485756, by rfl⟩ : syracuseStep 647675 = 971513) B971513
theorem B647945 : Blo 191804 647945 := bstep (se 2 (by rfl) ⟨242979, by rfl⟩ : syracuseStep 647945 = 485959) B485959
theorem B287807 : Blo 191804 287807 := bstep (se 1 (by rfl) ⟨215855, by rfl⟩ : syracuseStep 287807 = 431711) B431711
theorem B287849 : Blo 191804 287849 := bstep (se 2 (by rfl) ⟨107943, by rfl⟩ : syracuseStep 287849 = 215887) B215887
theorem B779453 : Blo 191804 779453 := bstep (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) B292295
theorem B287951 : Blo 191804 287951 := bstep (se 1 (by rfl) ⟨215963, by rfl⟩ : syracuseStep 287951 = 431927) B431927
theorem B288155 : Blo 191804 288155 := bstep (se 1 (by rfl) ⟨216116, by rfl⟩ : syracuseStep 288155 = 432233) B432233
theorem B648701 : Blo 191804 648701 := bstep (se 3 (by rfl) ⟨121631, by rfl⟩ : syracuseStep 648701 = 243263) B243263
theorem B288377 : Blo 191804 288377 := bstep (se 2 (by rfl) ⟨108141, by rfl⟩ : syracuseStep 288377 = 216283) B216283
theorem B288479 : Blo 191804 288479 := bstep (se 1 (by rfl) ⟨216359, by rfl⟩ : syracuseStep 288479 = 432719) B432719
theorem B1107715 : Blo 191804 1107715 := bstep (se 1 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 1107715 = 1661573) B1661573
theorem B288575 : Blo 191804 288575 := bstep (se 1 (by rfl) ⟨216431, by rfl⟩ : syracuseStep 288575 = 432863) B432863
theorem B2778947 : Blo 191804 2778947 := bstep (se 1 (by rfl) ⟨2084210, by rfl⟩ : syracuseStep 2778947 = 4168421) B4168421
theorem B288743 : Blo 191804 288743 := bstep (se 1 (by rfl) ⟨216557, by rfl⟩ : syracuseStep 288743 = 433115) B433115
theorem B288761 : Blo 191804 288761 := bstep (se 2 (by rfl) ⟨108285, by rfl⟩ : syracuseStep 288761 = 216571) B216571
theorem B288863 : Blo 191804 288863 := bstep (se 1 (by rfl) ⟨216647, by rfl⟩ : syracuseStep 288863 = 433295) B433295
theorem B977021 : Blo 191804 977021 := bstep (se 3 (by rfl) ⟨183191, by rfl⟩ : syracuseStep 977021 = 366383) B366383
theorem B288923 : Blo 191804 288923 := bstep (se 1 (by rfl) ⟨216692, by rfl⟩ : syracuseStep 288923 = 433385) B433385
theorem B288959 : Blo 191804 288959 := bstep (se 1 (by rfl) ⟨216719, by rfl⟩ : syracuseStep 288959 = 433439) B433439
theorem B289001 : Blo 191804 289001 := bstep (se 2 (by rfl) ⟨108375, by rfl⟩ : syracuseStep 289001 = 216751) B216751
theorem B649511 : Blo 191804 649511 := bstep (se 1 (by rfl) ⟨487133, by rfl⟩ : syracuseStep 649511 = 974267) B974267
theorem B551215 : Blo 191804 551215 := bstep (se 1 (by rfl) ⟨413411, by rfl⟩ : syracuseStep 551215 = 826823) B826823
theorem B4745603 : Blo 191804 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B616967 : Blo 191804 616967 := bstep (se 1 (by rfl) ⟨462725, by rfl⟩ : syracuseStep 616967 = 925451) B925451
theorem B289307 : Blo 191804 289307 := bstep (se 1 (by rfl) ⟨216980, by rfl⟩ : syracuseStep 289307 = 433961) B433961
theorem B289385 : Blo 191804 289385 := bstep (se 2 (by rfl) ⟨108519, by rfl⟩ : syracuseStep 289385 = 217039) B217039
theorem B1469177 : Blo 191804 1469177 := bstep (se 2 (by rfl) ⟨550941, by rfl⟩ : syracuseStep 1469177 = 1101883) B1101883
theorem B289913 : Blo 191804 289913 := bstep (se 2 (by rfl) ⟨108717, by rfl⟩ : syracuseStep 289913 = 217435) B217435
theorem B650375 : Blo 191804 650375 := bstep (se 1 (by rfl) ⟨487781, by rfl⟩ : syracuseStep 650375 = 975563) B975563
theorem B290015 : Blo 191804 290015 := bstep (se 1 (by rfl) ⟨217511, by rfl⟩ : syracuseStep 290015 = 435023) B435023
theorem B650483 : Blo 191804 650483 := bstep (se 1 (by rfl) ⟨487862, by rfl⟩ : syracuseStep 650483 = 975725) B975725
theorem B290057 : Blo 191804 290057 := bstep (se 2 (by rfl) ⟨108771, by rfl⟩ : syracuseStep 290057 = 217543) B217543
theorem B290159 : Blo 191804 290159 := bstep (se 1 (by rfl) ⟨217619, by rfl⟩ : syracuseStep 290159 = 435239) B435239
theorem B191975 : Blo 191804 191975 := bstep (se 1 (by rfl) ⟨143981, by rfl⟩ : syracuseStep 191975 = 287963) B287963
theorem B290279 : Blo 191804 290279 := bstep (se 1 (by rfl) ⟨217709, by rfl⟩ : syracuseStep 290279 = 435419) B435419
theorem B192091 : Blo 191804 192091 := bstep (se 1 (by rfl) ⟨144068, by rfl⟩ : syracuseStep 192091 = 288137) B288137
theorem B290411 : Blo 191804 290411 := bstep (se 1 (by rfl) ⟨217808, by rfl⟩ : syracuseStep 290411 = 435617) B435617
theorem B290537 : Blo 191804 290537 := bstep (se 2 (by rfl) ⟨108951, by rfl⟩ : syracuseStep 290537 = 217903) B217903
theorem B192327 : Blo 191804 192327 := bstep (se 1 (by rfl) ⟨144245, by rfl⟩ : syracuseStep 192327 = 288491) B288491
theorem B290681 : Blo 191804 290681 := bstep (se 2 (by rfl) ⟨109005, by rfl⟩ : syracuseStep 290681 = 218011) B218011
theorem B192479 : Blo 191804 192479 := bstep (se 1 (by rfl) ⟨144359, by rfl⟩ : syracuseStep 192479 = 288719) B288719
theorem B290783 : Blo 191804 290783 := bstep (se 1 (by rfl) ⟨218087, by rfl⟩ : syracuseStep 290783 = 436175) B436175
theorem B291035 : Blo 191804 291035 := bstep (se 1 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 291035 = 436553) B436553
theorem B192743 : Blo 191804 192743 := bstep (se 1 (by rfl) ⟨144557, by rfl⟩ : syracuseStep 192743 = 289115) B289115
theorem B291047 : Blo 191804 291047 := bstep (se 1 (by rfl) ⟨218285, by rfl⟩ : syracuseStep 291047 = 436571) B436571
theorem B192895 : Blo 191804 192895 := bstep (se 1 (by rfl) ⟨144671, by rfl⟩ : syracuseStep 192895 = 289343) B289343
theorem B291209 : Blo 191804 291209 := bstep (se 2 (by rfl) ⟨109203, by rfl⟩ : syracuseStep 291209 = 218407) B218407
theorem B324047 : Blo 191804 324047 := bstep (se 1 (by rfl) ⟨243035, by rfl⟩ : syracuseStep 324047 = 486071) B486071
theorem B192975 : Blo 191804 192975 := bstep (se 1 (by rfl) ⟨144731, by rfl⟩ : syracuseStep 192975 = 289463) B289463
theorem B291305 : Blo 191804 291305 := bstep (se 2 (by rfl) ⟨109239, by rfl⟩ : syracuseStep 291305 = 218479) B218479
theorem B193127 : Blo 191804 193127 := bstep (se 1 (by rfl) ⟨144845, by rfl⟩ : syracuseStep 193127 = 289691) B289691
theorem B291431 : Blo 191804 291431 := bstep (se 1 (by rfl) ⟨218573, by rfl⟩ : syracuseStep 291431 = 437147) B437147
theorem B1471121 : Blo 191804 1471121 := bstep (se 2 (by rfl) ⟨551670, by rfl⟩ : syracuseStep 1471121 = 1103341) B1103341
theorem B291563 : Blo 191804 291563 := bstep (se 1 (by rfl) ⟨218672, by rfl⟩ : syracuseStep 291563 = 437345) B437345
theorem B291593 : Blo 191804 291593 := bstep (se 2 (by rfl) ⟨109347, by rfl⟩ : syracuseStep 291593 = 218695) B218695
theorem B193391 : Blo 191804 193391 := bstep (se 1 (by rfl) ⟨145043, by rfl⟩ : syracuseStep 193391 = 290087) B290087
theorem B291695 : Blo 191804 291695 := bstep (se 1 (by rfl) ⟨218771, by rfl⟩ : syracuseStep 291695 = 437543) B437543
theorem B652157 : Blo 191804 652157 := bstep (se 3 (by rfl) ⟨122279, by rfl⟩ : syracuseStep 652157 = 244559) B244559
theorem B193447 : Blo 191804 193447 := bstep (se 1 (by rfl) ⟨145085, by rfl⟩ : syracuseStep 193447 = 290171) B290171
theorem B193531 : Blo 191804 193531 := bstep (se 1 (by rfl) ⟨145148, by rfl⟩ : syracuseStep 193531 = 290297) B290297
theorem B193599 : Blo 191804 193599 := bstep (se 1 (by rfl) ⟨145199, by rfl⟩ : syracuseStep 193599 = 290399) B290399
theorem B324715 : Blo 191804 324715 := bstep (se 1 (by rfl) ⟨243536, by rfl⟩ : syracuseStep 324715 = 487073) B487073
theorem B291947 : Blo 191804 291947 := bstep (se 1 (by rfl) ⟨218960, by rfl⟩ : syracuseStep 291947 = 437921) B437921
theorem B652427 : Blo 191804 652427 := bstep (se 1 (by rfl) ⟨489320, by rfl⟩ : syracuseStep 652427 = 978641) B978641
theorem B193743 : Blo 191804 193743 := bstep (se 1 (by rfl) ⟨145307, by rfl⟩ : syracuseStep 193743 = 290615) B290615
theorem B2782457 : Blo 191804 2782457 := bstep (se 2 (by rfl) ⟨1043421, by rfl⟩ : syracuseStep 2782457 = 2086843) B2086843
theorem B292187 : Blo 191804 292187 := bstep (se 1 (by rfl) ⟨219140, by rfl⟩ : syracuseStep 292187 = 438281) B438281
theorem B325019 : Blo 191804 325019 := bstep (se 1 (by rfl) ⟨243764, by rfl⟩ : syracuseStep 325019 = 487529) B487529
theorem B193947 : Blo 191804 193947 := bstep (se 1 (by rfl) ⟨145460, by rfl⟩ : syracuseStep 193947 = 290921) B290921
theorem B980423 : Blo 191804 980423 := bstep (se 1 (by rfl) ⟨735317, by rfl⟩ : syracuseStep 980423 = 1470635) B1470635
theorem B1242695 : Blo 191804 1242695 := bstep (se 1 (by rfl) ⟨932021, by rfl⟩ : syracuseStep 1242695 = 1864043) B1864043
theorem B2815559 : Blo 191804 2815559 := bstep (se 1 (by rfl) ⟨2111669, by rfl⟩ : syracuseStep 2815559 = 4223339) B4223339
theorem B292463 : Blo 191804 292463 := bstep (se 1 (by rfl) ⟨219347, by rfl⟩ : syracuseStep 292463 = 438695) B438695
theorem B194159 : Blo 191804 194159 := bstep (se 1 (by rfl) ⟨145619, by rfl⟩ : syracuseStep 194159 = 291239) B291239
theorem B194215 : Blo 191804 194215 := bstep (se 1 (by rfl) ⟨145661, by rfl⟩ : syracuseStep 194215 = 291323) B291323
theorem B292535 : Blo 191804 292535 := bstep (se 1 (by rfl) ⟨219401, by rfl⟩ : syracuseStep 292535 = 438803) B438803
theorem B292571 : Blo 191804 292571 := bstep (se 1 (by rfl) ⟨219428, by rfl⟩ : syracuseStep 292571 = 438857) B438857
theorem B325343 : Blo 191804 325343 := bstep (se 1 (by rfl) ⟨244007, by rfl⟩ : syracuseStep 325343 = 488015) B488015
theorem B194299 : Blo 191804 194299 := bstep (se 1 (by rfl) ⟨145724, by rfl⟩ : syracuseStep 194299 = 291449) B291449
theorem B194335 : Blo 191804 194335 := bstep (se 1 (by rfl) ⟨145751, by rfl⟩ : syracuseStep 194335 = 291503) B291503
theorem B194367 : Blo 191804 194367 := bstep (se 1 (by rfl) ⟨145775, by rfl⟩ : syracuseStep 194367 = 291551) B291551
theorem B292745 : Blo 191804 292745 := bstep (se 2 (by rfl) ⟨109779, by rfl⟩ : syracuseStep 292745 = 219559) B219559
theorem B1046429 : Blo 191804 1046429 := bstep (se 3 (by rfl) ⟨196205, by rfl⟩ : syracuseStep 1046429 = 392411) B392411
theorem B1406915 : Blo 191804 1406915 := bstep (se 1 (by rfl) ⟨1055186, by rfl⟩ : syracuseStep 1406915 = 2110373) B2110373
theorem B194543 : Blo 191804 194543 := bstep (se 1 (by rfl) ⟨145907, by rfl⟩ : syracuseStep 194543 = 291815) B291815
theorem B292847 : Blo 191804 292847 := bstep (se 1 (by rfl) ⟨219635, by rfl⟩ : syracuseStep 292847 = 439271) B439271
theorem B325775 : Blo 191804 325775 := bstep (se 1 (by rfl) ⟨244331, by rfl⟩ : syracuseStep 325775 = 488663) B488663
theorem B194715 : Blo 191804 194715 := bstep (se 1 (by rfl) ⟨146036, by rfl⟩ : syracuseStep 194715 = 292073) B292073
theorem B194751 : Blo 191804 194751 := bstep (se 1 (by rfl) ⟨146063, by rfl⟩ : syracuseStep 194751 = 292127) B292127
theorem B293099 : Blo 191804 293099 := bstep (se 1 (by rfl) ⟨219824, by rfl⟩ : syracuseStep 293099 = 439649) B439649
theorem B293159 : Blo 191804 293159 := bstep (se 1 (by rfl) ⟨219869, by rfl⟩ : syracuseStep 293159 = 439739) B439739
theorem B1112363 : Blo 191804 1112363 := bstep (se 1 (by rfl) ⟨834272, by rfl⟩ : syracuseStep 1112363 = 1668545) B1668545
theorem B194863 : Blo 191804 194863 := bstep (se 1 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 194863 = 292295) B292295
theorem B326011 : Blo 191804 326011 := bstep (se 1 (by rfl) ⟨244508, by rfl⟩ : syracuseStep 326011 = 489017) B489017
theorem B293243 : Blo 191804 293243 := bstep (se 1 (by rfl) ⟨219932, by rfl⟩ : syracuseStep 293243 = 439865) B439865
theorem B195099 : Blo 191804 195099 := bstep (se 1 (by rfl) ⟨146324, by rfl⟩ : syracuseStep 195099 = 292649) B292649
theorem B195103 : Blo 191804 195103 := bstep (se 1 (by rfl) ⟨146327, by rfl⟩ : syracuseStep 195103 = 292655) B292655
theorem B326281 : Blo 191804 326281 := bstep (se 2 (by rfl) ⟨122355, by rfl⟩ : syracuseStep 326281 = 244711) B244711
theorem B490121 : Blo 191804 490121 := bstep (se 2 (by rfl) ⟨183795, by rfl⟩ : syracuseStep 490121 = 367591) B367591
theorem B293513 : Blo 191804 293513 := bstep (se 2 (by rfl) ⟨110067, by rfl⟩ : syracuseStep 293513 = 220135) B220135
theorem B654047 : Blo 191804 654047 := bstep (se 1 (by rfl) ⟨490535, by rfl⟩ : syracuseStep 654047 = 981071) B981071
theorem B293687 : Blo 191804 293687 := bstep (se 1 (by rfl) ⟨220265, by rfl⟩ : syracuseStep 293687 = 440531) B440531
theorem B195419 : Blo 191804 195419 := bstep (se 1 (by rfl) ⟨146564, by rfl⟩ : syracuseStep 195419 = 293129) B293129
theorem B1571719 : Blo 191804 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B195487 : Blo 191804 195487 := bstep (se 1 (by rfl) ⟨146615, by rfl⟩ : syracuseStep 195487 = 293231) B293231
theorem B1473551 : Blo 191804 1473551 := bstep (se 1 (by rfl) ⟨1105163, by rfl⟩ : syracuseStep 1473551 = 2210327) B2210327
theorem B195631 : Blo 191804 195631 := bstep (se 1 (by rfl) ⟨146723, by rfl⟩ : syracuseStep 195631 = 293447) B293447
theorem B261191 : Blo 191804 261191 := bstep (se 1 (by rfl) ⟨195893, by rfl⟩ : syracuseStep 261191 = 391787) B391787
theorem B195655 : Blo 191804 195655 := bstep (se 1 (by rfl) ⟨146741, by rfl⟩ : syracuseStep 195655 = 293483) B293483
theorem B8879179 : Blo 191804 8879179 := bstep (se 1 (by rfl) ⟨6659384, by rfl⟩ : syracuseStep 8879179 = 13318769) B13318769
theorem B3341735 : Blo 191804 3341735 := bstep (se 1 (by rfl) ⟨2506301, by rfl⟩ : syracuseStep 3341735 = 5012603) B5012603
theorem B654803 : Blo 191804 654803 := bstep (se 1 (by rfl) ⟨491102, by rfl⟩ : syracuseStep 654803 = 982205) B982205
theorem B1244645 : Blo 191804 1244645 := bstep (se 4 (by rfl) ⟨116685, by rfl⟩ : syracuseStep 1244645 = 233371) B233371
theorem B2784941 : Blo 191804 2784941 := bstep (se 3 (by rfl) ⟨522176, by rfl⟩ : syracuseStep 2784941 = 1044353) B1044353
theorem B655073 : Blo 191804 655073 := bstep (se 2 (by rfl) ⟨245652, by rfl⟩ : syracuseStep 655073 = 491305) B491305
theorem B491255 : Blo 191804 491255 := bstep (se 1 (by rfl) ⟨368441, by rfl⟩ : syracuseStep 491255 = 736883) B736883
theorem B40468403 : Blo 191804 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B491903 : Blo 191804 491903 := bstep (se 1 (by rfl) ⟨368927, by rfl⟩ : syracuseStep 491903 = 737855) B737855
theorem B1475009 : Blo 191804 1475009 := bstep (se 2 (by rfl) ⟨553128, by rfl⟩ : syracuseStep 1475009 = 1106257) B1106257
theorem B3146363 : Blo 191804 3146363 := bstep (se 1 (by rfl) ⟨2359772, by rfl⟩ : syracuseStep 3146363 = 4719545) B4719545
theorem B820331 : Blo 191804 820331 := bstep (se 1 (by rfl) ⟨615248, by rfl⟩ : syracuseStep 820331 = 1230497) B1230497
theorem B328927 : Blo 191804 328927 := bstep (se 1 (by rfl) ⟨246695, by rfl⟩ : syracuseStep 328927 = 493391) B493391
theorem B623963 : Blo 191804 623963 := bstep (se 1 (by rfl) ⟨467972, by rfl⟩ : syracuseStep 623963 = 935945) B935945
theorem B493087 : Blo 191804 493087 := bstep (se 1 (by rfl) ⟨369815, by rfl⟩ : syracuseStep 493087 = 739631) B739631
theorem B657071 : Blo 191804 657071 := bstep (se 1 (by rfl) ⟨492803, by rfl⟩ : syracuseStep 657071 = 985607) B985607
theorem B231103 : Blo 191804 231103 := bstep (se 1 (by rfl) ⟨173327, by rfl⟩ : syracuseStep 231103 = 346655) B346655
theorem B952067 : Blo 191804 952067 := bstep (se 1 (by rfl) ⟨714050, by rfl⟩ : syracuseStep 952067 = 1428101) B1428101
theorem B10192877 : Blo 191804 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B657391 : Blo 191804 657391 := bstep (se 1 (by rfl) ⟨493043, by rfl⟩ : syracuseStep 657391 = 986087) B986087
theorem B6883379 : Blo 191804 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B1411181 : Blo 191804 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B5867639 : Blo 191804 5867639 := bstep (se 1 (by rfl) ⟨4400729, by rfl⟩ : syracuseStep 5867639 = 8801459) B8801459
theorem B1476953 : Blo 191804 1476953 := bstep (se 2 (by rfl) ⟨553857, by rfl⟩ : syracuseStep 1476953 = 1107715) B1107715
theorem B494039 : Blo 191804 494039 := bstep (se 1 (by rfl) ⟨370529, by rfl⟩ : syracuseStep 494039 = 741059) B741059
theorem B2361905 : Blo 191804 2361905 := bstep (se 2 (by rfl) ⟨885714, by rfl⟩ : syracuseStep 2361905 = 1771429) B1771429
theorem B658259 : Blo 191804 658259 := bstep (se 1 (by rfl) ⟨493694, by rfl⟩ : syracuseStep 658259 = 987389) B987389
theorem B494495 : Blo 191804 494495 := bstep (se 1 (by rfl) ⟨370871, by rfl⟩ : syracuseStep 494495 = 741743) B741743
theorem B461879 : Blo 191804 461879 := bstep (se 1 (by rfl) ⟨346409, by rfl⟩ : syracuseStep 461879 = 692819) B692819
theorem B658799 : Blo 191804 658799 := bstep (se 1 (by rfl) ⟨494099, by rfl⟩ : syracuseStep 658799 = 988199) B988199
theorem B23662043 : Blo 191804 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B1577009 : Blo 191804 1577009 := bstep (se 2 (by rfl) ⟨591378, by rfl⟩ : syracuseStep 1577009 = 1182757) B1182757
theorem B660041 : Blo 191804 660041 := bstep (se 2 (by rfl) ⟨247515, by rfl⟩ : syracuseStep 660041 = 495031) B495031
theorem B1479383 : Blo 191804 1479383 := bstep (se 1 (by rfl) ⟨1109537, by rfl⟩ : syracuseStep 1479383 = 2219075) B2219075
theorem B463897 : Blo 191804 463897 := bstep (se 2 (by rfl) ⟨173961, by rfl⟩ : syracuseStep 463897 = 347923) B347923
theorem B4920749 : Blo 191804 4920749 := bstep (se 3 (by rfl) ⟨922640, by rfl⟩ : syracuseStep 4920749 = 1845281) B1845281
theorem B431783 : Blo 191804 431783 := bstep (se 1 (by rfl) ⟨323837, by rfl⟩ : syracuseStep 431783 = 647675) B647675
theorem B431963 : Blo 191804 431963 := bstep (se 1 (by rfl) ⟨323972, by rfl⟩ : syracuseStep 431963 = 647945) B647945
theorem B464935 : Blo 191804 464935 := bstep (se 1 (by rfl) ⟨348701, by rfl⟩ : syracuseStep 464935 = 697403) B697403
theorem B432467 : Blo 191804 432467 := bstep (se 1 (by rfl) ⟨324350, by rfl⟩ : syracuseStep 432467 = 648701) B648701
theorem B432953 : Blo 191804 432953 := bstep (se 2 (by rfl) ⟨162357, by rfl⟩ : syracuseStep 432953 = 324715) B324715
theorem B433007 : Blo 191804 433007 := bstep (se 1 (by rfl) ⟨324755, by rfl⟩ : syracuseStep 433007 = 649511) B649511
theorem B433583 : Blo 191804 433583 := bstep (se 1 (by rfl) ⟨325187, by rfl⟩ : syracuseStep 433583 = 650375) B650375
theorem B433655 : Blo 191804 433655 := bstep (se 1 (by rfl) ⟨325241, by rfl⟩ : syracuseStep 433655 = 650483) B650483
theorem B729121 : Blo 191804 729121 := bstep (se 2 (by rfl) ⟨273420, by rfl⟩ : syracuseStep 729121 = 546841) B546841
theorem B696509 : Blo 191804 696509 := bstep (se 3 (by rfl) ⟨130595, by rfl⟩ : syracuseStep 696509 = 261191) B261191
theorem B729593 : Blo 191804 729593 := bstep (se 2 (by rfl) ⟨273597, by rfl⟩ : syracuseStep 729593 = 547195) B547195
theorem B434681 : Blo 191804 434681 := bstep (se 2 (by rfl) ⟨163005, by rfl⟩ : syracuseStep 434681 = 326011) B326011
theorem B205339 : Blo 191804 205339 := bstep (se 1 (by rfl) ⟨154004, by rfl⟩ : syracuseStep 205339 = 308009) B308009
theorem B434771 : Blo 191804 434771 := bstep (se 1 (by rfl) ⟨326078, by rfl⟩ : syracuseStep 434771 = 652157) B652157
theorem B1253971 : Blo 191804 1253971 := bstep (se 1 (by rfl) ⟨940478, by rfl⟩ : syracuseStep 1253971 = 1880957) B1880957
theorem B434951 : Blo 191804 434951 := bstep (se 1 (by rfl) ⟨326213, by rfl⟩ : syracuseStep 434951 = 652427) B652427
theorem B435041 : Blo 191804 435041 := bstep (se 2 (by rfl) ⟨163140, by rfl⟩ : syracuseStep 435041 = 326281) B326281
theorem B828463 : Blo 191804 828463 := bstep (se 1 (by rfl) ⟨621347, by rfl⟩ : syracuseStep 828463 = 1242695) B1242695
theorem B1877039 : Blo 191804 1877039 := bstep (se 1 (by rfl) ⟨1407779, by rfl⟩ : syracuseStep 1877039 = 2815559) B2815559
theorem B369785 : Blo 191804 369785 := bstep (se 2 (by rfl) ⟨138669, by rfl⟩ : syracuseStep 369785 = 277339) B277339
theorem B697619 : Blo 191804 697619 := bstep (se 1 (by rfl) ⟨523214, by rfl⟩ : syracuseStep 697619 = 1046429) B1046429
theorem B206159 : Blo 191804 206159 := bstep (se 1 (by rfl) ⟨154619, by rfl⟩ : syracuseStep 206159 = 309239) B309239
theorem B11838905 : Blo 191804 11838905 := bstep (se 2 (by rfl) ⟨4439589, by rfl⟩ : syracuseStep 11838905 = 8879179) B8879179
theorem B436031 : Blo 191804 436031 := bstep (se 1 (by rfl) ⟨327023, by rfl⟩ : syracuseStep 436031 = 654047) B654047
theorem B436535 : Blo 191804 436535 := bstep (se 1 (by rfl) ⟨327401, by rfl⟩ : syracuseStep 436535 = 654803) B654803
theorem B829763 : Blo 191804 829763 := bstep (se 1 (by rfl) ⟨622322, by rfl⟩ : syracuseStep 829763 = 1244645) B1244645
theorem B436715 : Blo 191804 436715 := bstep (se 1 (by rfl) ⟨327536, by rfl⟩ : syracuseStep 436715 = 655073) B655073
theorem B26978935 : Blo 191804 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B666575 : Blo 191804 666575 := bstep (se 1 (by rfl) ⟨499931, by rfl⟩ : syracuseStep 666575 = 999863) B999863
theorem B470087 : Blo 191804 470087 := bstep (se 1 (by rfl) ⟨352565, by rfl⟩ : syracuseStep 470087 = 705131) B705131
theorem B2468987 : Blo 191804 2468987 := bstep (se 1 (by rfl) ⟨1851740, by rfl⟩ : syracuseStep 2468987 = 3703481) B3703481
theorem B437417 : Blo 191804 437417 := bstep (se 2 (by rfl) ⟨164031, by rfl⟩ : syracuseStep 437417 = 328063) B328063
theorem B601499 : Blo 191804 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B437831 : Blo 191804 437831 := bstep (se 1 (by rfl) ⟨328373, by rfl⟩ : syracuseStep 437831 = 656747) B656747
theorem B437903 : Blo 191804 437903 := bstep (se 1 (by rfl) ⟨328427, by rfl⟩ : syracuseStep 437903 = 656855) B656855
theorem B437993 : Blo 191804 437993 := bstep (se 2 (by rfl) ⟨164247, by rfl⟩ : syracuseStep 437993 = 328495) B328495
theorem B438011 : Blo 191804 438011 := bstep (se 1 (by rfl) ⟨328508, by rfl⟩ : syracuseStep 438011 = 657017) B657017
theorem B2338895 : Blo 191804 2338895 := bstep (se 1 (by rfl) ⟨1754171, by rfl⟩ : syracuseStep 2338895 = 3508343) B3508343
theorem B372863 : Blo 191804 372863 := bstep (se 1 (by rfl) ⟨279647, by rfl⟩ : syracuseStep 372863 = 559295) B559295
theorem B733799 : Blo 191804 733799 := bstep (se 1 (by rfl) ⟨550349, by rfl⟩ : syracuseStep 733799 = 1100699) B1100699
theorem B439019 : Blo 191804 439019 := bstep (se 1 (by rfl) ⟨329264, by rfl⟩ : syracuseStep 439019 = 658529) B658529
theorem B2765735 : Blo 191804 2765735 := bstep (se 1 (by rfl) ⟨2074301, by rfl⟩ : syracuseStep 2765735 = 4148603) B4148603
theorem B832463 : Blo 191804 832463 := bstep (se 1 (by rfl) ⟨624347, by rfl⟩ : syracuseStep 832463 = 1248695) B1248695
theorem B12530645 : Blo 191804 12530645 := bstep (se 7 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 12530645 = 293687) B293687
theorem B439289 : Blo 191804 439289 := bstep (se 2 (by rfl) ⟨164733, by rfl⟩ : syracuseStep 439289 = 329467) B329467
theorem B2372611 : Blo 191804 2372611 := bstep (se 1 (by rfl) ⟨1779458, by rfl⟩ : syracuseStep 2372611 = 3558917) B3558917
theorem B439379 : Blo 191804 439379 := bstep (se 1 (by rfl) ⟨329534, by rfl⟩ : syracuseStep 439379 = 659069) B659069
theorem B242939 : Blo 191804 242939 := bstep (se 1 (by rfl) ⟨182204, by rfl⟩ : syracuseStep 242939 = 364409) B364409
theorem B439559 : Blo 191804 439559 := bstep (se 1 (by rfl) ⟨329669, by rfl⟩ : syracuseStep 439559 = 659339) B659339
theorem B6436205 : Blo 191804 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B439919 : Blo 191804 439919 := bstep (se 1 (by rfl) ⟨329939, by rfl⟩ : syracuseStep 439919 = 659879) B659879
theorem B734953 : Blo 191804 734953 := bstep (se 2 (by rfl) ⟨275607, by rfl⟩ : syracuseStep 734953 = 551215) B551215
theorem B2799755 : Blo 191804 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B702695 : Blo 191804 702695 := bstep (se 1 (by rfl) ⟨527021, by rfl⟩ : syracuseStep 702695 = 1054043) B1054043
theorem B833915 : Blo 191804 833915 := bstep (se 1 (by rfl) ⟨625436, by rfl⟩ : syracuseStep 833915 = 1250873) B1250873
theorem B1456541 : Blo 191804 1456541 := bstep (se 3 (by rfl) ⟨273101, by rfl⟩ : syracuseStep 1456541 = 546203) B546203
theorem B703399 : Blo 191804 703399 := bstep (se 1 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 703399 = 1055099) B1055099
theorem B2801137 : Blo 191804 2801137 := bstep (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) B2100853
theorem B1490521 : Blo 191804 1490521 := bstep (se 2 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 1490521 = 1117891) B1117891
theorem B245359 : Blo 191804 245359 := bstep (se 1 (by rfl) ⟨184019, by rfl⟩ : syracuseStep 245359 = 368039) B368039
theorem B933599 : Blo 191804 933599 := bstep (se 1 (by rfl) ⟨700199, by rfl⟩ : syracuseStep 933599 = 1400399) B1400399
theorem B1851281 : Blo 191804 1851281 := bstep (se 2 (by rfl) ⟨694230, by rfl⟩ : syracuseStep 1851281 = 1388461) B1388461
theorem B1654739 : Blo 191804 1654739 := bstep (se 1 (by rfl) ⟨1241054, by rfl⟩ : syracuseStep 1654739 = 2482109) B2482109
theorem B835879 : Blo 191804 835879 := bstep (se 1 (by rfl) ⟨626909, by rfl⟩ : syracuseStep 835879 = 1253819) B1253819
theorem B1851821 : Blo 191804 1851821 := bstep (se 3 (by rfl) ⟨347216, by rfl⟩ : syracuseStep 1851821 = 694433) B694433
theorem B312263 : Blo 191804 312263 := bstep (se 1 (by rfl) ⟨234197, by rfl⟩ : syracuseStep 312263 = 468395) B468395
theorem B1098785 : Blo 191804 1098785 := bstep (se 2 (by rfl) ⟨412044, by rfl⟩ : syracuseStep 1098785 = 824089) B824089
theorem B1852631 : Blo 191804 1852631 := bstep (se 1 (by rfl) ⟨1389473, by rfl⟩ : syracuseStep 1852631 = 2778947) B2778947
theorem B2508353 : Blo 191804 2508353 := bstep (se 2 (by rfl) ⟨940632, by rfl⟩ : syracuseStep 2508353 = 1881265) B1881265
theorem B3163735 : Blo 191804 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B411311 : Blo 191804 411311 := bstep (se 1 (by rfl) ⟨308483, by rfl⟩ : syracuseStep 411311 = 616967) B616967
theorem B1984733 : Blo 191804 1984733 := bstep (se 3 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 1984733 = 744275) B744275
theorem B936157 : Blo 191804 936157 := bstep (se 3 (by rfl) ⟨175529, by rfl⟩ : syracuseStep 936157 = 351059) B351059
theorem B1100425 : Blo 191804 1100425 := bstep (se 2 (by rfl) ⟨412659, by rfl⟩ : syracuseStep 1100425 = 825319) B825319
theorem B216031 : Blo 191804 216031 := bstep (se 1 (by rfl) ⟨162023, by rfl⟩ : syracuseStep 216031 = 324047) B324047
theorem B740333 : Blo 191804 740333 := bstep (se 3 (by rfl) ⟨138812, by rfl⟩ : syracuseStep 740333 = 277625) B277625
theorem B1854971 : Blo 191804 1854971 := bstep (se 1 (by rfl) ⟨1391228, by rfl⟩ : syracuseStep 1854971 = 2782457) B2782457
theorem B216679 : Blo 191804 216679 := bstep (se 1 (by rfl) ⟨162509, by rfl⟩ : syracuseStep 216679 = 325019) B325019
theorem B1429273 : Blo 191804 1429273 := bstep (se 2 (by rfl) ⟨535977, by rfl⟩ : syracuseStep 1429273 = 1071955) B1071955
theorem B216895 : Blo 191804 216895 := bstep (se 1 (by rfl) ⟨162671, by rfl⟩ : syracuseStep 216895 = 325343) B325343
theorem B937943 : Blo 191804 937943 := bstep (se 1 (by rfl) ⟨703457, by rfl⟩ : syracuseStep 937943 = 1406915) B1406915
theorem B11980781 : Blo 191804 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B217183 : Blo 191804 217183 := bstep (se 1 (by rfl) ⟨162887, by rfl⟩ : syracuseStep 217183 = 325775) B325775
theorem B741575 : Blo 191804 741575 := bstep (se 1 (by rfl) ⟨556181, by rfl⟩ : syracuseStep 741575 = 1112363) B1112363
theorem B413993 : Blo 191804 413993 := bstep (se 2 (by rfl) ⟨155247, by rfl⟩ : syracuseStep 413993 = 310495) B310495
theorem B938633 : Blo 191804 938633 := bstep (se 2 (by rfl) ⟨351987, by rfl⟩ : syracuseStep 938633 = 703975) B703975
theorem B1856627 : Blo 191804 1856627 := bstep (se 1 (by rfl) ⟨1392470, by rfl⟩ : syracuseStep 1856627 = 2784941) B2784941
theorem B13981081 : Blo 191804 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B743033 : Blo 191804 743033 := bstep (se 2 (by rfl) ⟨278637, by rfl⟩ : syracuseStep 743033 = 557275) B557275
theorem B350345 : Blo 191804 350345 := bstep (se 2 (by rfl) ⟨131379, by rfl⟩ : syracuseStep 350345 = 262759) B262759
theorem B219739 : Blo 191804 219739 := bstep (se 1 (by rfl) ⟨164804, by rfl⟩ : syracuseStep 219739 = 329609) B329609
theorem B220027 : Blo 191804 220027 := bstep (se 1 (by rfl) ⟨165020, by rfl⟩ : syracuseStep 220027 = 330041) B330041
theorem B1465289 : Blo 191804 1465289 := bstep (se 2 (by rfl) ⟨549483, by rfl⟩ : syracuseStep 1465289 = 1098967) B1098967
theorem B5431499 : Blo 191804 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B549119 : Blo 191804 549119 := bstep (se 1 (by rfl) ⟨411839, by rfl⟩ : syracuseStep 549119 = 823679) B823679
theorem B745757 : Blo 191804 745757 := bstep (se 3 (by rfl) ⟨139829, by rfl⟩ : syracuseStep 745757 = 279659) B279659
theorem B779165 : Blo 191804 779165 := bstep (se 3 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 779165 = 292187) B292187
theorem B287723 : Blo 191804 287723 := bstep (se 1 (by rfl) ⟨215792, by rfl⟩ : syracuseStep 287723 = 431585) B431585
theorem B3008015 : Blo 191804 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B2975491 : Blo 191804 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B616211 : Blo 191804 616211 := bstep (se 1 (by rfl) ⟨462158, by rfl⟩ : syracuseStep 616211 = 924317) B924317
theorem B616427 : Blo 191804 616427 := bstep (se 1 (by rfl) ⟨462320, by rfl⟩ : syracuseStep 616427 = 924641) B924641
theorem B288815 : Blo 191804 288815 := bstep (se 1 (by rfl) ⟨216611, by rfl⟩ : syracuseStep 288815 = 433223) B433223
theorem B289079 : Blo 191804 289079 := bstep (se 1 (by rfl) ⟨216809, by rfl⟩ : syracuseStep 289079 = 433619) B433619
theorem B289259 : Blo 191804 289259 := bstep (se 1 (by rfl) ⟨216944, by rfl⟩ : syracuseStep 289259 = 433889) B433889
theorem B551443 : Blo 191804 551443 := bstep (se 1 (by rfl) ⟨413582, by rfl⟩ : syracuseStep 551443 = 827165) B827165
theorem B486283 : Blo 191804 486283 := bstep (se 1 (by rfl) ⟨364712, by rfl⟩ : syracuseStep 486283 = 729425) B729425
theorem B977993 : Blo 191804 977993 := bstep (se 2 (by rfl) ⟨366747, by rfl⟩ : syracuseStep 977993 = 733495) B733495
theorem B289961 : Blo 191804 289961 := bstep (se 2 (by rfl) ⟨108735, by rfl⟩ : syracuseStep 289961 = 217471) B217471
theorem B191871 : Blo 191804 191871 := bstep (se 1 (by rfl) ⟨143903, by rfl⟩ : syracuseStep 191871 = 287807) B287807
theorem B191899 : Blo 191804 191899 := bstep (se 1 (by rfl) ⟨143924, by rfl⟩ : syracuseStep 191899 = 287849) B287849
theorem B519635 : Blo 191804 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B191967 : Blo 191804 191967 := bstep (se 1 (by rfl) ⟨143975, by rfl⟩ : syracuseStep 191967 = 287951) B287951
theorem B290375 : Blo 191804 290375 := bstep (se 1 (by rfl) ⟨217781, by rfl⟩ : syracuseStep 290375 = 435563) B435563
theorem B192103 : Blo 191804 192103 := bstep (se 1 (by rfl) ⟨144077, by rfl⟩ : syracuseStep 192103 = 288155) B288155
theorem B552673 : Blo 191804 552673 := bstep (se 2 (by rfl) ⟨207252, by rfl⟩ : syracuseStep 552673 = 414505) B414505
theorem B192251 : Blo 191804 192251 := bstep (se 1 (by rfl) ⟨144188, by rfl⟩ : syracuseStep 192251 = 288377) B288377
theorem B290555 : Blo 191804 290555 := bstep (se 1 (by rfl) ⟨217916, by rfl⟩ : syracuseStep 290555 = 435833) B435833
theorem B192319 : Blo 191804 192319 := bstep (se 1 (by rfl) ⟨144239, by rfl⟩ : syracuseStep 192319 = 288479) B288479
theorem B192383 : Blo 191804 192383 := bstep (se 1 (by rfl) ⟨144287, by rfl⟩ : syracuseStep 192383 = 288575) B288575
theorem B192495 : Blo 191804 192495 := bstep (se 1 (by rfl) ⟨144371, by rfl⟩ : syracuseStep 192495 = 288743) B288743
theorem B487417 : Blo 191804 487417 := bstep (se 2 (by rfl) ⟨182781, by rfl⟩ : syracuseStep 487417 = 365563) B365563
theorem B192507 : Blo 191804 192507 := bstep (se 1 (by rfl) ⟨144380, by rfl⟩ : syracuseStep 192507 = 288761) B288761
theorem B192575 : Blo 191804 192575 := bstep (se 1 (by rfl) ⟨144431, by rfl⟩ : syracuseStep 192575 = 288863) B288863
theorem B651347 : Blo 191804 651347 := bstep (se 1 (by rfl) ⟨488510, by rfl⟩ : syracuseStep 651347 = 977021) B977021
theorem B192615 : Blo 191804 192615 := bstep (se 1 (by rfl) ⟨144461, by rfl⟩ : syracuseStep 192615 = 288923) B288923
theorem B192639 : Blo 191804 192639 := bstep (se 1 (by rfl) ⟨144479, by rfl⟩ : syracuseStep 192639 = 288959) B288959
theorem B192667 : Blo 191804 192667 := bstep (se 1 (by rfl) ⟨144500, by rfl⟩ : syracuseStep 192667 = 289001) B289001
theorem B192871 : Blo 191804 192871 := bstep (se 1 (by rfl) ⟨144653, by rfl⟩ : syracuseStep 192871 = 289307) B289307
theorem B192923 : Blo 191804 192923 := bstep (se 1 (by rfl) ⟨144692, by rfl⟩ : syracuseStep 192923 = 289385) B289385
theorem B291227 : Blo 191804 291227 := bstep (se 1 (by rfl) ⟨218420, by rfl⟩ : syracuseStep 291227 = 436841) B436841
theorem B979451 : Blo 191804 979451 := bstep (se 1 (by rfl) ⟨734588, by rfl⟩ : syracuseStep 979451 = 1469177) B1469177
theorem B488065 : Blo 191804 488065 := bstep (se 2 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 488065 = 366049) B366049
theorem B193275 : Blo 191804 193275 := bstep (se 1 (by rfl) ⟨144956, by rfl⟩ : syracuseStep 193275 = 289913) B289913
theorem B193343 : Blo 191804 193343 := bstep (se 1 (by rfl) ⟨145007, by rfl⟩ : syracuseStep 193343 = 290015) B290015
theorem B291647 : Blo 191804 291647 := bstep (se 1 (by rfl) ⟨218735, by rfl⟩ : syracuseStep 291647 = 437471) B437471
theorem B193371 : Blo 191804 193371 := bstep (se 1 (by rfl) ⟨145028, by rfl⟩ : syracuseStep 193371 = 290057) B290057
theorem B193439 : Blo 191804 193439 := bstep (se 1 (by rfl) ⟨145079, by rfl⟩ : syracuseStep 193439 = 290159) B290159
theorem B291791 : Blo 191804 291791 := bstep (se 1 (by rfl) ⟨218843, by rfl⟩ : syracuseStep 291791 = 437687) B437687
theorem B193519 : Blo 191804 193519 := bstep (se 1 (by rfl) ⟨145139, by rfl⟩ : syracuseStep 193519 = 290279) B290279
theorem B291833 : Blo 191804 291833 := bstep (se 2 (by rfl) ⟨109437, by rfl⟩ : syracuseStep 291833 = 218875) B218875
theorem B291881 : Blo 191804 291881 := bstep (se 2 (by rfl) ⟨109455, by rfl⟩ : syracuseStep 291881 = 218911) B218911
theorem B193607 : Blo 191804 193607 := bstep (se 1 (by rfl) ⟨145205, by rfl⟩ : syracuseStep 193607 = 290411) B290411
theorem B291911 : Blo 191804 291911 := bstep (se 1 (by rfl) ⟨218933, by rfl⟩ : syracuseStep 291911 = 437867) B437867
theorem B488531 : Blo 191804 488531 := bstep (se 1 (by rfl) ⟨366398, by rfl⟩ : syracuseStep 488531 = 732797) B732797
theorem B193691 : Blo 191804 193691 := bstep (se 1 (by rfl) ⟨145268, by rfl⟩ : syracuseStep 193691 = 290537) B290537
theorem B193787 : Blo 191804 193787 := bstep (se 1 (by rfl) ⟨145340, by rfl⟩ : syracuseStep 193787 = 290681) B290681
theorem B292091 : Blo 191804 292091 := bstep (se 1 (by rfl) ⟨219068, by rfl⟩ : syracuseStep 292091 = 438137) B438137
theorem B193855 : Blo 191804 193855 := bstep (se 1 (by rfl) ⟨145391, by rfl⟩ : syracuseStep 193855 = 290783) B290783
theorem B554303 : Blo 191804 554303 := bstep (se 1 (by rfl) ⟨415727, by rfl⟩ : syracuseStep 554303 = 831455) B831455
theorem B1602935 : Blo 191804 1602935 := bstep (se 1 (by rfl) ⟨1202201, by rfl⟩ : syracuseStep 1602935 = 2404403) B2404403
theorem B488875 : Blo 191804 488875 := bstep (se 1 (by rfl) ⟨366656, by rfl⟩ : syracuseStep 488875 = 733313) B733313
theorem B194023 : Blo 191804 194023 := bstep (se 1 (by rfl) ⟨145517, by rfl⟩ : syracuseStep 194023 = 291035) B291035
theorem B194031 : Blo 191804 194031 := bstep (se 1 (by rfl) ⟨145523, by rfl⟩ : syracuseStep 194031 = 291047) B291047
theorem B194139 : Blo 191804 194139 := bstep (se 1 (by rfl) ⟨145604, by rfl⟩ : syracuseStep 194139 = 291209) B291209
theorem B194203 : Blo 191804 194203 := bstep (se 1 (by rfl) ⟨145652, by rfl⟩ : syracuseStep 194203 = 291305) B291305
theorem B194287 : Blo 191804 194287 := bstep (se 1 (by rfl) ⟨145715, by rfl⟩ : syracuseStep 194287 = 291431) B291431
theorem B980747 : Blo 191804 980747 := bstep (se 1 (by rfl) ⟨735560, by rfl⟩ : syracuseStep 980747 = 1471121) B1471121
theorem B194375 : Blo 191804 194375 := bstep (se 1 (by rfl) ⟨145781, by rfl⟩ : syracuseStep 194375 = 291563) B291563
theorem B194395 : Blo 191804 194395 := bstep (se 1 (by rfl) ⟨145796, by rfl⟩ : syracuseStep 194395 = 291593) B291593
theorem B194463 : Blo 191804 194463 := bstep (se 1 (by rfl) ⟨145847, by rfl⟩ : syracuseStep 194463 = 291695) B291695
theorem B554951 : Blo 191804 554951 := bstep (se 1 (by rfl) ⟨416213, by rfl⟩ : syracuseStep 554951 = 832427) B832427
theorem B1112089 : Blo 191804 1112089 := bstep (se 2 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 1112089 = 834067) B834067
theorem B1472579 : Blo 191804 1472579 := bstep (se 1 (by rfl) ⟨1104434, by rfl⟩ : syracuseStep 1472579 = 2208869) B2208869
theorem B194631 : Blo 191804 194631 := bstep (se 1 (by rfl) ⟨145973, by rfl⟩ : syracuseStep 194631 = 291947) B291947
theorem B1701965 : Blo 191804 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B194791 : Blo 191804 194791 := bstep (se 1 (by rfl) ⟨146093, by rfl⟩ : syracuseStep 194791 = 292187) B292187
theorem B653615 : Blo 191804 653615 := bstep (se 1 (by rfl) ⟨490211, by rfl⟩ : syracuseStep 653615 = 980423) B980423
theorem B194975 : Blo 191804 194975 := bstep (se 1 (by rfl) ⟨146231, by rfl⟩ : syracuseStep 194975 = 292463) B292463
theorem B1669571 : Blo 191804 1669571 := bstep (se 1 (by rfl) ⟨1252178, by rfl⟩ : syracuseStep 1669571 = 2504357) B2504357
theorem B195023 : Blo 191804 195023 := bstep (se 1 (by rfl) ⟨146267, by rfl⟩ : syracuseStep 195023 = 292535) B292535
theorem B293327 : Blo 191804 293327 := bstep (se 1 (by rfl) ⟨219995, by rfl⟩ : syracuseStep 293327 = 439991) B439991
theorem B195047 : Blo 191804 195047 := bstep (se 1 (by rfl) ⟨146285, by rfl⟩ : syracuseStep 195047 = 292571) B292571
theorem B2095625 : Blo 191804 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B1473065 : Blo 191804 1473065 := bstep (se 2 (by rfl) ⟨552399, by rfl⟩ : syracuseStep 1473065 = 1104799) B1104799
theorem B293417 : Blo 191804 293417 := bstep (se 2 (by rfl) ⟨110031, by rfl⟩ : syracuseStep 293417 = 220063) B220063
theorem B195163 : Blo 191804 195163 := bstep (se 1 (by rfl) ⟨146372, by rfl⟩ : syracuseStep 195163 = 292745) B292745
theorem B195231 : Blo 191804 195231 := bstep (se 1 (by rfl) ⟨146423, by rfl⟩ : syracuseStep 195231 = 292847) B292847
theorem B293609 : Blo 191804 293609 := bstep (se 2 (by rfl) ⟨110103, by rfl⟩ : syracuseStep 293609 = 220207) B220207
theorem B195399 : Blo 191804 195399 := bstep (se 1 (by rfl) ⟨146549, by rfl⟩ : syracuseStep 195399 = 293099) B293099
theorem B195439 : Blo 191804 195439 := bstep (se 1 (by rfl) ⟨146579, by rfl⟩ : syracuseStep 195439 = 293159) B293159
theorem B195495 : Blo 191804 195495 := bstep (se 1 (by rfl) ⟨146621, by rfl⟩ : syracuseStep 195495 = 293243) B293243
theorem B4946993 : Blo 191804 4946993 := bstep (se 2 (by rfl) ⟨1855122, by rfl⟩ : syracuseStep 4946993 = 3710245) B3710245
theorem B326747 : Blo 191804 326747 := bstep (se 1 (by rfl) ⟨245060, by rfl⟩ : syracuseStep 326747 = 490121) B490121
theorem B195675 : Blo 191804 195675 := bstep (se 1 (by rfl) ⟨146756, by rfl⟩ : syracuseStep 195675 = 293513) B293513
theorem B195791 : Blo 191804 195791 := bstep (se 1 (by rfl) ⟨146843, by rfl⟩ : syracuseStep 195791 = 293687) B293687
theorem B982367 : Blo 191804 982367 := bstep (se 1 (by rfl) ⟨736775, by rfl⟩ : syracuseStep 982367 = 1473551) B1473551
theorem B2227823 : Blo 191804 2227823 := bstep (se 1 (by rfl) ⟨1670867, by rfl⟩ : syracuseStep 2227823 = 3341735) B3341735
theorem B327503 : Blo 191804 327503 := bstep (se 1 (by rfl) ⟨245627, by rfl⟩ : syracuseStep 327503 = 491255) B491255
theorem B327935 : Blo 191804 327935 := bstep (se 1 (by rfl) ⟨245951, by rfl⟩ : syracuseStep 327935 = 491903) B491903
theorem B983339 : Blo 191804 983339 := bstep (se 1 (by rfl) ⟨737504, by rfl⟩ : syracuseStep 983339 = 1475009) B1475009
theorem B1114505 : Blo 191804 1114505 := bstep (se 2 (by rfl) ⟨417939, by rfl⟩ : syracuseStep 1114505 = 835879) B835879
theorem B2097575 : Blo 191804 2097575 := bstep (se 1 (by rfl) ⟨1573181, by rfl⟩ : syracuseStep 2097575 = 3146363) B3146363
theorem B1671961 : Blo 191804 1671961 := bstep (se 2 (by rfl) ⟨626985, by rfl⟩ : syracuseStep 1671961 = 1253971) B1253971
theorem B1672235 : Blo 191804 1672235 := bstep (se 1 (by rfl) ⟨1254176, by rfl⟩ : syracuseStep 1672235 = 2508353) B2508353
theorem B4588919 : Blo 191804 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B984635 : Blo 191804 984635 := bstep (se 1 (by rfl) ⟨738476, by rfl⟩ : syracuseStep 984635 = 1476953) B1476953
theorem B329359 : Blo 191804 329359 := bstep (se 1 (by rfl) ⟨247019, by rfl⟩ : syracuseStep 329359 = 494039) B494039
theorem B1574603 : Blo 191804 1574603 := bstep (se 1 (by rfl) ⟨1180952, by rfl⟩ : syracuseStep 1574603 = 2361905) B2361905
theorem B329663 : Blo 191804 329663 := bstep (se 1 (by rfl) ⟨247247, by rfl⟩ : syracuseStep 329663 = 494495) B494495
theorem B657449 : Blo 191804 657449 := bstep (se 2 (by rfl) ⟨246543, by rfl⟩ : syracuseStep 657449 = 493087) B493087
theorem B3967321 : Blo 191804 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B625295 : Blo 191804 625295 := bstep (se 1 (by rfl) ⟨468971, by rfl⟩ : syracuseStep 625295 = 937943) B937943
theorem B1051339 : Blo 191804 1051339 := bstep (se 1 (by rfl) ⟨788504, by rfl⟩ : syracuseStep 1051339 = 1577009) B1577009
theorem B494383 : Blo 191804 494383 := bstep (se 1 (by rfl) ⟨370787, by rfl⟩ : syracuseStep 494383 = 741575) B741575
theorem B1248209 : Blo 191804 1248209 := bstep (se 2 (by rfl) ⟨468078, by rfl⟩ : syracuseStep 1248209 = 936157) B936157
theorem B986093 : Blo 191804 986093 := bstep (se 3 (by rfl) ⟨184892, by rfl⟩ : syracuseStep 986093 = 369785) B369785
theorem B986255 : Blo 191804 986255 := bstep (se 1 (by rfl) ⟨739691, by rfl⟩ : syracuseStep 986255 = 1479383) B1479383
theorem B3280499 : Blo 191804 3280499 := bstep (se 1 (by rfl) ⟨2460374, by rfl⟩ : syracuseStep 3280499 = 4920749) B4920749
theorem B495355 : Blo 191804 495355 := bstep (se 1 (by rfl) ⟨371516, by rfl⟩ : syracuseStep 495355 = 743033) B743033
theorem B1905697 : Blo 191804 1905697 := bstep (se 2 (by rfl) ⟨714636, by rfl⟩ : syracuseStep 1905697 = 1429273) B1429273
theorem B1479869 : Blo 191804 1479869 := bstep (se 3 (by rfl) ⟨277475, by rfl⟩ : syracuseStep 1479869 = 554951) B554951
theorem B464339 : Blo 191804 464339 := bstep (se 1 (by rfl) ⟨348254, by rfl⟩ : syracuseStep 464339 = 696509) B696509
theorem B497171 : Blo 191804 497171 := bstep (se 1 (by rfl) ⟨372878, by rfl⟩ : syracuseStep 497171 = 745757) B745757
theorem B1251359 : Blo 191804 1251359 := bstep (se 1 (by rfl) ⟨938519, by rfl⟩ : syracuseStep 1251359 = 1877039) B1877039
theorem B2005343 : Blo 191804 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B1645991 : Blo 191804 1645991 := bstep (se 1 (by rfl) ⟨1234493, by rfl⟩ : syracuseStep 1645991 = 2468987) B2468987
theorem B1974221 : Blo 191804 1974221 := bstep (se 3 (by rfl) ⟨370166, by rfl⟩ : syracuseStep 1974221 = 740333) B740333
theorem B1482785 : Blo 191804 1482785 := bstep (se 2 (by rfl) ⟨556044, by rfl⟩ : syracuseStep 1482785 = 1112089) B1112089
theorem B434231 : Blo 191804 434231 := bstep (se 1 (by rfl) ⟨325673, by rfl⟩ : syracuseStep 434231 = 651347) B651347
theorem B1843823 : Blo 191804 1843823 := bstep (se 1 (by rfl) ⟨1382867, by rfl⟩ : syracuseStep 1843823 = 2765735) B2765735
theorem B369535 : Blo 191804 369535 := bstep (se 1 (by rfl) ⟨277151, by rfl⟩ : syracuseStep 369535 = 554303) B554303
theorem B1385693 : Blo 191804 1385693 := bstep (se 3 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 1385693 = 519635) B519635
theorem B468463 : Blo 191804 468463 := bstep (se 1 (by rfl) ⟨351347, by rfl⟩ : syracuseStep 468463 = 702695) B702695
theorem B435743 : Blo 191804 435743 := bstep (se 1 (by rfl) ⟨326807, by rfl⟩ : syracuseStep 435743 = 653615) B653615
theorem B1485215 : Blo 191804 1485215 := bstep (se 1 (by rfl) ⟨1113911, by rfl⟩ : syracuseStep 1485215 = 2227823) B2227823
theorem B994301 : Blo 191804 994301 := bstep (se 3 (by rfl) ⟨186431, by rfl⟩ : syracuseStep 994301 = 372863) B372863
theorem B208175 : Blo 191804 208175 := bstep (se 1 (by rfl) ⟨156131, by rfl⟩ : syracuseStep 208175 = 312263) B312263
theorem B732523 : Blo 191804 732523 := bstep (se 1 (by rfl) ⟨549392, by rfl⟩ : syracuseStep 732523 = 1098785) B1098785
theorem B273785 : Blo 191804 273785 := bstep (se 2 (by rfl) ⟨102669, by rfl⟩ : syracuseStep 273785 = 205339) B205339
theorem B274207 : Blo 191804 274207 := bstep (se 1 (by rfl) ⟨205655, by rfl⟩ : syracuseStep 274207 = 411311) B411311
theorem B438047 : Blo 191804 438047 := bstep (se 1 (by rfl) ⟨328535, by rfl⟩ : syracuseStep 438047 = 657071) B657071
theorem B634711 : Blo 191804 634711 := bstep (se 1 (by rfl) ⟨476033, by rfl⟩ : syracuseStep 634711 = 952067) B952067
theorem B6795251 : Blo 191804 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B3911759 : Blo 191804 3911759 := bstep (se 1 (by rfl) ⟨2933819, by rfl⟩ : syracuseStep 3911759 = 5867639) B5867639
theorem B1323155 : Blo 191804 1323155 := bstep (se 1 (by rfl) ⟨992366, by rfl⟩ : syracuseStep 1323155 = 1984733) B1984733
theorem B438569 : Blo 191804 438569 := bstep (se 2 (by rfl) ⟨164463, by rfl⟩ : syracuseStep 438569 = 328927) B328927
theorem B2503021 : Blo 191804 2503021 := bstep (se 3 (by rfl) ⟨469316, by rfl⟩ : syracuseStep 2503021 = 938633) B938633
theorem B438839 : Blo 191804 438839 := bstep (se 1 (by rfl) ⟨329129, by rfl⟩ : syracuseStep 438839 = 658259) B658259
theorem B307919 : Blo 191804 307919 := bstep (se 1 (by rfl) ⟨230939, by rfl⟩ : syracuseStep 307919 = 461879) B461879
theorem B439199 : Blo 191804 439199 := bstep (se 1 (by rfl) ⟨329399, by rfl⟩ : syracuseStep 439199 = 658799) B658799
theorem B308137 : Blo 191804 308137 := bstep (se 2 (by rfl) ⟨115551, by rfl⟩ : syracuseStep 308137 = 231103) B231103
theorem B15774695 : Blo 191804 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B275995 : Blo 191804 275995 := bstep (se 1 (by rfl) ⟨206996, by rfl⟩ : syracuseStep 275995 = 413993) B413993
theorem B440027 : Blo 191804 440027 := bstep (se 1 (by rfl) ⟨330020, by rfl⟩ : syracuseStep 440027 = 660041) B660041
theorem B735257 : Blo 191804 735257 := bstep (se 2 (by rfl) ⟨275721, by rfl⟩ : syracuseStep 735257 = 551443) B551443
theorem B736897 : Blo 191804 736897 := bstep (se 2 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 736897 = 552673) B552673
theorem B3620999 : Blo 191804 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B934253 : Blo 191804 934253 := bstep (se 3 (by rfl) ⟨175172, by rfl⟩ : syracuseStep 934253 = 350345) B350345
theorem B410807 : Blo 191804 410807 := bstep (se 1 (by rfl) ⟨308105, by rfl⟩ : syracuseStep 410807 = 616211) B616211
theorem B410951 : Blo 191804 410951 := bstep (se 1 (by rfl) ⟨308213, by rfl⟩ : syracuseStep 410951 = 616427) B616427
theorem B3163481 : Blo 191804 3163481 := bstep (se 2 (by rfl) ⟨1186305, by rfl⟩ : syracuseStep 3163481 = 2372611) B2372611
theorem B444383 : Blo 191804 444383 := bstep (se 1 (by rfl) ⟨333287, by rfl⟩ : syracuseStep 444383 = 666575) B666575
theorem B313391 : Blo 191804 313391 := bstep (se 1 (by rfl) ⟨235043, by rfl⟩ : syracuseStep 313391 = 470087) B470087
theorem B1559263 : Blo 191804 1559263 := bstep (se 1 (by rfl) ⟨1169447, by rfl⟩ : syracuseStep 1559263 = 2338895) B2338895
theorem B1068623 : Blo 191804 1068623 := bstep (se 1 (by rfl) ⟨801467, by rfl⟩ : syracuseStep 1068623 = 1602935) B1602935
theorem B937865 : Blo 191804 937865 := bstep (se 2 (by rfl) ⟨351699, by rfl⟩ : syracuseStep 937865 = 703399) B703399
theorem B1134643 : Blo 191804 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B971027 : Blo 191804 971027 := bstep (se 1 (by rfl) ⟨728270, by rfl⟩ : syracuseStep 971027 = 1456541) B1456541
theorem B1397083 : Blo 191804 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B3297995 : Blo 191804 3297995 := bstep (se 1 (by rfl) ⟨2473496, by rfl⟩ : syracuseStep 3297995 = 4946993) B4946993
theorem B217831 : Blo 191804 217831 := bstep (se 1 (by rfl) ⟨163373, by rfl⟩ : syracuseStep 217831 = 326747) B326747
theorem B1987361 : Blo 191804 1987361 := bstep (se 2 (by rfl) ⟨745260, by rfl⟩ : syracuseStep 1987361 = 1490521) B1490521
theorem B218335 : Blo 191804 218335 := bstep (se 1 (by rfl) ⟨163751, by rfl⟩ : syracuseStep 218335 = 327503) B327503
theorem B1234187 : Blo 191804 1234187 := bstep (se 1 (by rfl) ⟨925640, by rfl⟩ : syracuseStep 1234187 = 1851281) B1851281
theorem B1103159 : Blo 191804 1103159 := bstep (se 1 (by rfl) ⟨827369, by rfl⟩ : syracuseStep 1103159 = 1654739) B1654739
theorem B972161 : Blo 191804 972161 := bstep (se 2 (by rfl) ⟨364560, by rfl⟩ : syracuseStep 972161 = 729121) B729121
theorem B1234547 : Blo 191804 1234547 := bstep (se 1 (by rfl) ⟨925910, by rfl⟩ : syracuseStep 1234547 = 1851821) B1851821
theorem B1464317 : Blo 191804 1464317 := bstep (se 3 (by rfl) ⟨274559, by rfl⟩ : syracuseStep 1464317 = 549119) B549119
theorem B546887 : Blo 191804 546887 := bstep (se 1 (by rfl) ⟨410165, by rfl⟩ : syracuseStep 546887 = 820331) B820331
theorem B1235087 : Blo 191804 1235087 := bstep (se 1 (by rfl) ⟨926315, by rfl⟩ : syracuseStep 1235087 = 1852631) B1852631
theorem B415975 : Blo 191804 415975 := bstep (se 1 (by rfl) ⟨311981, by rfl⟩ : syracuseStep 415975 = 623963) B623963
theorem B1104617 : Blo 191804 1104617 := bstep (se 2 (by rfl) ⟨414231, by rfl⟩ : syracuseStep 1104617 = 828463) B828463
theorem B940787 : Blo 191804 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B4218313 : Blo 191804 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B1236647 : Blo 191804 1236647 := bstep (se 1 (by rfl) ⟨927485, by rfl⟩ : syracuseStep 1236647 = 1854971) B1854971
theorem B876521 : Blo 191804 876521 := bstep (se 2 (by rfl) ⟨328695, by rfl⟩ : syracuseStep 876521 = 657391) B657391
theorem B7987187 : Blo 191804 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B647837 : Blo 191804 647837 := bstep (se 3 (by rfl) ⟨121469, by rfl⟩ : syracuseStep 647837 = 242939) B242939
theorem B1860317 : Blo 191804 1860317 := bstep (se 3 (by rfl) ⟨348809, by rfl⟩ : syracuseStep 1860317 = 697619) B697619
theorem B1237751 : Blo 191804 1237751 := bstep (se 1 (by rfl) ⟨928313, by rfl⟩ : syracuseStep 1237751 = 1856627) B1856627
theorem B35971913 : Blo 191804 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B1467233 : Blo 191804 1467233 := bstep (se 2 (by rfl) ⟨550212, by rfl⟩ : syracuseStep 1467233 = 1100425) B1100425
theorem B549757 : Blo 191804 549757 := bstep (se 3 (by rfl) ⟨103079, by rfl⟩ : syracuseStep 549757 = 206159) B206159
theorem B287855 : Blo 191804 287855 := bstep (se 1 (by rfl) ⟨215891, by rfl⟩ : syracuseStep 287855 = 431783) B431783
theorem B648377 : Blo 191804 648377 := bstep (se 2 (by rfl) ⟨243141, by rfl⟩ : syracuseStep 648377 = 486283) B486283
theorem B287975 : Blo 191804 287975 := bstep (se 1 (by rfl) ⟨215981, by rfl⟩ : syracuseStep 287975 = 431963) B431963
theorem B288041 : Blo 191804 288041 := bstep (se 2 (by rfl) ⟨108015, by rfl⟩ : syracuseStep 288041 = 216031) B216031
theorem B288311 : Blo 191804 288311 := bstep (se 1 (by rfl) ⟨216233, by rfl⟩ : syracuseStep 288311 = 432467) B432467
theorem B288635 : Blo 191804 288635 := bstep (se 1 (by rfl) ⟨216476, by rfl⟩ : syracuseStep 288635 = 432953) B432953
theorem B288671 : Blo 191804 288671 := bstep (se 1 (by rfl) ⟨216503, by rfl⟩ : syracuseStep 288671 = 433007) B433007
theorem B976859 : Blo 191804 976859 := bstep (se 1 (by rfl) ⟨732644, by rfl⟩ : syracuseStep 976859 = 1465289) B1465289
theorem B288905 : Blo 191804 288905 := bstep (se 2 (by rfl) ⟨108339, by rfl⟩ : syracuseStep 288905 = 216679) B216679
theorem B289055 : Blo 191804 289055 := bstep (se 1 (by rfl) ⟨216791, by rfl⟩ : syracuseStep 289055 = 433583) B433583
theorem B289103 : Blo 191804 289103 := bstep (se 1 (by rfl) ⟨216827, by rfl⟩ : syracuseStep 289103 = 433655) B433655
theorem B289193 : Blo 191804 289193 := bstep (se 2 (by rfl) ⟨108447, by rfl⟩ : syracuseStep 289193 = 216895) B216895
theorem B649889 : Blo 191804 649889 := bstep (se 2 (by rfl) ⟨243708, by rfl⟩ : syracuseStep 649889 = 487417) B487417
theorem B289577 : Blo 191804 289577 := bstep (se 2 (by rfl) ⟨108591, by rfl⟩ : syracuseStep 289577 = 217183) B217183
theorem B486395 : Blo 191804 486395 := bstep (se 1 (by rfl) ⟨364796, by rfl⟩ : syracuseStep 486395 = 729593) B729593
theorem B289787 : Blo 191804 289787 := bstep (se 1 (by rfl) ⟨217340, by rfl⟩ : syracuseStep 289787 = 434681) B434681
theorem B289847 : Blo 191804 289847 := bstep (se 1 (by rfl) ⟨217385, by rfl⟩ : syracuseStep 289847 = 434771) B434771
theorem B289967 : Blo 191804 289967 := bstep (se 1 (by rfl) ⟨217475, by rfl⟩ : syracuseStep 289967 = 434951) B434951
theorem B290027 : Blo 191804 290027 := bstep (se 1 (by rfl) ⟨217520, by rfl⟩ : syracuseStep 290027 = 435041) B435041
theorem B519443 : Blo 191804 519443 := bstep (se 1 (by rfl) ⟨389582, by rfl⟩ : syracuseStep 519443 = 779165) B779165
theorem B191815 : Blo 191804 191815 := bstep (se 1 (by rfl) ⟨143861, by rfl⟩ : syracuseStep 191815 = 287723) B287723
theorem B650753 : Blo 191804 650753 := bstep (se 2 (by rfl) ⟨244032, by rfl⟩ : syracuseStep 650753 = 488065) B488065
theorem B7892603 : Blo 191804 7892603 := bstep (se 1 (by rfl) ⟨5919452, by rfl⟩ : syracuseStep 7892603 = 11838905) B11838905
theorem B290687 : Blo 191804 290687 := bstep (se 1 (by rfl) ⟨218015, by rfl⟩ : syracuseStep 290687 = 436031) B436031
theorem B192543 : Blo 191804 192543 := bstep (se 1 (by rfl) ⟨144407, by rfl⟩ : syracuseStep 192543 = 288815) B288815
theorem B618529 : Blo 191804 618529 := bstep (se 2 (by rfl) ⟨231948, by rfl⟩ : syracuseStep 618529 = 463897) B463897
theorem B192719 : Blo 191804 192719 := bstep (se 1 (by rfl) ⟨144539, by rfl⟩ : syracuseStep 192719 = 289079) B289079
theorem B291023 : Blo 191804 291023 := bstep (se 1 (by rfl) ⟨218267, by rfl⟩ : syracuseStep 291023 = 436535) B436535
theorem B553175 : Blo 191804 553175 := bstep (se 1 (by rfl) ⟨414881, by rfl⟩ : syracuseStep 553175 = 829763) B829763
theorem B192839 : Blo 191804 192839 := bstep (se 1 (by rfl) ⟨144629, by rfl⟩ : syracuseStep 192839 = 289259) B289259
theorem B291143 : Blo 191804 291143 := bstep (se 1 (by rfl) ⟨218357, by rfl⟩ : syracuseStep 291143 = 436715) B436715
theorem B18641441 : Blo 191804 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B651833 : Blo 191804 651833 := bstep (se 2 (by rfl) ⟨244437, by rfl⟩ : syracuseStep 651833 = 488875) B488875
theorem B651995 : Blo 191804 651995 := bstep (se 1 (by rfl) ⟨488996, by rfl⟩ : syracuseStep 651995 = 977993) B977993
theorem B193307 : Blo 191804 193307 := bstep (se 1 (by rfl) ⟨144980, by rfl⟩ : syracuseStep 193307 = 289961) B289961
theorem B291611 : Blo 191804 291611 := bstep (se 1 (by rfl) ⟨218708, by rfl⟩ : syracuseStep 291611 = 437417) B437417
theorem B979937 : Blo 191804 979937 := bstep (se 2 (by rfl) ⟨367476, by rfl⟩ : syracuseStep 979937 = 734953) B734953
theorem B193583 : Blo 191804 193583 := bstep (se 1 (by rfl) ⟨145187, by rfl⟩ : syracuseStep 193583 = 290375) B290375
theorem B291887 : Blo 191804 291887 := bstep (se 1 (by rfl) ⟨218915, by rfl⟩ : syracuseStep 291887 = 437831) B437831
theorem B291935 : Blo 191804 291935 := bstep (se 1 (by rfl) ⟨218951, by rfl⟩ : syracuseStep 291935 = 437903) B437903
theorem B291995 : Blo 191804 291995 := bstep (se 1 (by rfl) ⟨218996, by rfl⟩ : syracuseStep 291995 = 437993) B437993
theorem B193703 : Blo 191804 193703 := bstep (se 1 (by rfl) ⟨145277, by rfl⟩ : syracuseStep 193703 = 290555) B290555
theorem B292007 : Blo 191804 292007 := bstep (se 1 (by rfl) ⟨219005, by rfl⟩ : syracuseStep 292007 = 438011) B438011
theorem B619913 : Blo 191804 619913 := bstep (se 2 (by rfl) ⟨232467, by rfl⟩ : syracuseStep 619913 = 464935) B464935
theorem B194151 : Blo 191804 194151 := bstep (se 1 (by rfl) ⟨145613, by rfl⟩ : syracuseStep 194151 = 291227) B291227
theorem B652967 : Blo 191804 652967 := bstep (se 1 (by rfl) ⟨489725, by rfl⟩ : syracuseStep 652967 = 979451) B979451
theorem B489199 : Blo 191804 489199 := bstep (se 1 (by rfl) ⟨366899, by rfl⟩ : syracuseStep 489199 = 733799) B733799
theorem B292679 : Blo 191804 292679 := bstep (se 1 (by rfl) ⟨219509, by rfl⟩ : syracuseStep 292679 = 439019) B439019
theorem B194431 : Blo 191804 194431 := bstep (se 1 (by rfl) ⟨145823, by rfl⟩ : syracuseStep 194431 = 291647) B291647
theorem B194527 : Blo 191804 194527 := bstep (se 1 (by rfl) ⟨145895, by rfl⟩ : syracuseStep 194527 = 291791) B291791
theorem B554975 : Blo 191804 554975 := bstep (se 1 (by rfl) ⟨416231, by rfl⟩ : syracuseStep 554975 = 832463) B832463
theorem B8353763 : Blo 191804 8353763 := bstep (se 1 (by rfl) ⟨6265322, by rfl⟩ : syracuseStep 8353763 = 12530645) B12530645
theorem B194555 : Blo 191804 194555 := bstep (se 1 (by rfl) ⟨145916, by rfl⟩ : syracuseStep 194555 = 291833) B291833
theorem B292859 : Blo 191804 292859 := bstep (se 1 (by rfl) ⟨219644, by rfl⟩ : syracuseStep 292859 = 439289) B439289
theorem B194587 : Blo 191804 194587 := bstep (se 1 (by rfl) ⟨145940, by rfl⟩ : syracuseStep 194587 = 291881) B291881
theorem B194607 : Blo 191804 194607 := bstep (se 1 (by rfl) ⟨145955, by rfl⟩ : syracuseStep 194607 = 291911) B291911
theorem B325687 : Blo 191804 325687 := bstep (se 1 (by rfl) ⟨244265, by rfl⟩ : syracuseStep 325687 = 488531) B488531
theorem B292919 : Blo 191804 292919 := bstep (se 1 (by rfl) ⟨219689, by rfl⟩ : syracuseStep 292919 = 439379) B439379
theorem B292985 : Blo 191804 292985 := bstep (se 2 (by rfl) ⟨109869, by rfl⟩ : syracuseStep 292985 = 219739) B219739
theorem B194727 : Blo 191804 194727 := bstep (se 1 (by rfl) ⟨146045, by rfl⟩ : syracuseStep 194727 = 292091) B292091
theorem B293039 : Blo 191804 293039 := bstep (se 1 (by rfl) ⟨219779, by rfl⟩ : syracuseStep 293039 = 439559) B439559
theorem B4290803 : Blo 191804 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B1603997 : Blo 191804 1603997 := bstep (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) B601499
theorem B293279 : Blo 191804 293279 := bstep (se 1 (by rfl) ⟨219959, by rfl⟩ : syracuseStep 293279 = 439919) B439919
theorem B293369 : Blo 191804 293369 := bstep (se 2 (by rfl) ⟨110013, by rfl⟩ : syracuseStep 293369 = 220027) B220027
theorem B653831 : Blo 191804 653831 := bstep (se 1 (by rfl) ⟨490373, by rfl⟩ : syracuseStep 653831 = 980747) B980747
theorem B981719 : Blo 191804 981719 := bstep (se 1 (by rfl) ⟨736289, by rfl⟩ : syracuseStep 981719 = 1472579) B1472579
theorem B1866503 : Blo 191804 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B555943 : Blo 191804 555943 := bstep (se 1 (by rfl) ⟨416957, by rfl⟩ : syracuseStep 555943 = 833915) B833915
theorem B1113047 : Blo 191804 1113047 := bstep (se 1 (by rfl) ⟨834785, by rfl⟩ : syracuseStep 1113047 = 1669571) B1669571
theorem B195551 : Blo 191804 195551 := bstep (se 1 (by rfl) ⟨146663, by rfl⟩ : syracuseStep 195551 = 293327) B293327
theorem B982043 : Blo 191804 982043 := bstep (se 1 (by rfl) ⟨736532, by rfl⟩ : syracuseStep 982043 = 1473065) B1473065
theorem B195611 : Blo 191804 195611 := bstep (se 1 (by rfl) ⟨146708, by rfl⟩ : syracuseStep 195611 = 293417) B293417
theorem B195739 : Blo 191804 195739 := bstep (se 1 (by rfl) ⟨146804, by rfl⟩ : syracuseStep 195739 = 293609) B293609
theorem B3734849 : Blo 191804 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B327145 : Blo 191804 327145 := bstep (se 2 (by rfl) ⟨122679, by rfl⟩ : syracuseStep 327145 = 245359) B245359
theorem B654911 : Blo 191804 654911 := bstep (se 1 (by rfl) ⟨491183, by rfl⟩ : syracuseStep 654911 = 982367) B982367
theorem B622399 : Blo 191804 622399 := bstep (se 1 (by rfl) ⟨466799, by rfl⟩ : syracuseStep 622399 = 933599) B933599
theorem B655559 : Blo 191804 655559 := bstep (se 1 (by rfl) ⟨491669, by rfl⟩ : syracuseStep 655559 = 983339) B983339
theorem B622835 : Blo 191804 622835 := bstep (se 1 (by rfl) ⟨467126, by rfl⟩ : syracuseStep 622835 = 934253) B934253
theorem B1114823 : Blo 191804 1114823 := bstep (se 1 (by rfl) ⟨836117, by rfl⟩ : syracuseStep 1114823 = 1672235) B1672235
theorem B2229281 : Blo 191804 2229281 := bstep (se 2 (by rfl) ⟨835980, by rfl⟩ : syracuseStep 2229281 = 1671961) B1671961
theorem B656423 : Blo 191804 656423 := bstep (se 1 (by rfl) ⟨492317, by rfl⟩ : syracuseStep 656423 = 984635) B984635
theorem B1049735 : Blo 191804 1049735 := bstep (se 1 (by rfl) ⟨787301, by rfl⟩ : syracuseStep 1049735 = 1574603) B1574603
theorem B492713 : Blo 191804 492713 := bstep (se 2 (by rfl) ⟨184767, by rfl⟩ : syracuseStep 492713 = 369535) B369535
theorem B296255 : Blo 191804 296255 := bstep (se 1 (by rfl) ⟨222191, by rfl⟩ : syracuseStep 296255 = 444383) B444383
theorem B821117 : Blo 191804 821117 := bstep (se 3 (by rfl) ⟨153959, by rfl⟩ : syracuseStep 821117 = 307919) B307919
theorem B624617 : Blo 191804 624617 := bstep (se 2 (by rfl) ⟨234231, by rfl⟩ : syracuseStep 624617 = 468463) B468463
theorem B657395 : Blo 191804 657395 := bstep (se 1 (by rfl) ⟨493046, by rfl⟩ : syracuseStep 657395 = 986093) B986093
theorem B657503 : Blo 191804 657503 := bstep (se 1 (by rfl) ⟨493127, by rfl⟩ : syracuseStep 657503 = 986255) B986255
theorem B625243 : Blo 191804 625243 := bstep (se 1 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 625243 = 937865) B937865
theorem B2198663 : Blo 191804 2198663 := bstep (se 1 (by rfl) ⟨1648997, by rfl⟩ : syracuseStep 2198663 = 3297995) B3297995
theorem B986579 : Blo 191804 986579 := bstep (se 1 (by rfl) ⟨739934, by rfl⟩ : syracuseStep 986579 = 1479869) B1479869
theorem B822791 : Blo 191804 822791 := bstep (se 1 (by rfl) ⟨617093, by rfl⟩ : syracuseStep 822791 = 1234187) B1234187
theorem B331447 : Blo 191804 331447 := bstep (se 1 (by rfl) ⟨248585, by rfl⟩ : syracuseStep 331447 = 497171) B497171
theorem B659177 : Blo 191804 659177 := bstep (se 2 (by rfl) ⟨247191, by rfl⟩ : syracuseStep 659177 = 494383) B494383
theorem B823031 : Blo 191804 823031 := bstep (se 1 (by rfl) ⟨617273, by rfl⟩ : syracuseStep 823031 = 1234547) B1234547
theorem B364591 : Blo 191804 364591 := bstep (se 1 (by rfl) ⟨273443, by rfl⟩ : syracuseStep 364591 = 546887) B546887
theorem B823391 : Blo 191804 823391 := bstep (se 1 (by rfl) ⟨617543, by rfl⟩ : syracuseStep 823391 = 1235087) B1235087
theorem B627191 : Blo 191804 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B660473 : Blo 191804 660473 := bstep (se 2 (by rfl) ⟨247677, by rfl⟩ : syracuseStep 660473 = 495355) B495355
theorem B365609 : Blo 191804 365609 := bstep (se 2 (by rfl) ⟨137103, by rfl⟩ : syracuseStep 365609 = 274207) B274207
theorem B824431 : Blo 191804 824431 := bstep (se 1 (by rfl) ⟨618323, by rfl⟩ : syracuseStep 824431 = 1236647) B1236647
theorem B1316147 : Blo 191804 1316147 := bstep (se 1 (by rfl) ⟨987110, by rfl⟩ : syracuseStep 1316147 = 1974221) B1974221
theorem B988523 : Blo 191804 988523 := bstep (se 1 (by rfl) ⟨741392, by rfl⟩ : syracuseStep 988523 = 1482785) B1482785
theorem B824705 : Blo 191804 824705 := bstep (se 2 (by rfl) ⟨309264, by rfl⟩ : syracuseStep 824705 = 618529) B618529
theorem B1512857 : Blo 191804 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B431891 : Blo 191804 431891 := bstep (se 1 (by rfl) ⟨323918, by rfl⟩ : syracuseStep 431891 = 647837) B647837
theorem B825167 : Blo 191804 825167 := bstep (se 1 (by rfl) ⟨618875, by rfl⟩ : syracuseStep 825167 = 1237751) B1237751
theorem B432251 : Blo 191804 432251 := bstep (se 1 (by rfl) ⟨324188, by rfl⟩ : syracuseStep 432251 = 648377) B648377
theorem B923795 : Blo 191804 923795 := bstep (se 1 (by rfl) ⟨692846, by rfl⟩ : syracuseStep 923795 = 1385693) B1385693
theorem B990143 : Blo 191804 990143 := bstep (se 1 (by rfl) ⟨742607, by rfl⟩ : syracuseStep 990143 = 1485215) B1485215
theorem B433259 : Blo 191804 433259 := bstep (se 1 (by rfl) ⟨324944, by rfl⟩ : syracuseStep 433259 = 649889) B649889
theorem B662867 : Blo 191804 662867 := bstep (se 1 (by rfl) ⟨497150, by rfl⟩ : syracuseStep 662867 = 994301) B994301
theorem B367993 : Blo 191804 367993 := bstep (se 2 (by rfl) ⟨137997, by rfl⟩ : syracuseStep 367993 = 275995) B275995
theorem B433835 : Blo 191804 433835 := bstep (se 1 (by rfl) ⟨325376, by rfl⟩ : syracuseStep 433835 = 650753) B650753
theorem B4530167 : Blo 191804 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B434249 : Blo 191804 434249 := bstep (se 2 (by rfl) ⟨162843, by rfl⟩ : syracuseStep 434249 = 325687) B325687
theorem B368783 : Blo 191804 368783 := bstep (se 1 (by rfl) ⟨276587, by rfl⟩ : syracuseStep 368783 = 553175) B553175
theorem B12427627 : Blo 191804 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B434555 : Blo 191804 434555 := bstep (se 1 (by rfl) ⟨325916, by rfl⟩ : syracuseStep 434555 = 651833) B651833
theorem B434663 : Blo 191804 434663 := bstep (se 1 (by rfl) ⟨325997, by rfl⟩ : syracuseStep 434663 = 651995) B651995
theorem B730093 : Blo 191804 730093 := bstep (se 3 (by rfl) ⟨136892, by rfl⟩ : syracuseStep 730093 = 273785) B273785
theorem B435311 : Blo 191804 435311 := bstep (se 1 (by rfl) ⟨326483, by rfl⟩ : syracuseStep 435311 = 652967) B652967
theorem B369983 : Blo 191804 369983 := bstep (se 1 (by rfl) ⟨277487, by rfl⟩ : syracuseStep 369983 = 554975) B554975
theorem B2860535 : Blo 191804 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B435887 : Blo 191804 435887 := bstep (se 1 (by rfl) ⟨326915, by rfl⟩ : syracuseStep 435887 = 653831) B653831
theorem B436193 : Blo 191804 436193 := bstep (se 2 (by rfl) ⟨163572, by rfl⟩ : syracuseStep 436193 = 327145) B327145
theorem B436607 : Blo 191804 436607 := bstep (se 1 (by rfl) ⟨327455, by rfl⟩ : syracuseStep 436607 = 654911) B654911
theorem B829865 : Blo 191804 829865 := bstep (se 2 (by rfl) ⟨311199, by rfl⟩ : syracuseStep 829865 = 622399) B622399
theorem B273871 : Blo 191804 273871 := bstep (se 1 (by rfl) ⟨205403, by rfl⟩ : syracuseStep 273871 = 410807) B410807
theorem B2108987 : Blo 191804 2108987 := bstep (se 1 (by rfl) ⟨1581740, by rfl⟩ : syracuseStep 2108987 = 3163481) B3163481
theorem B3059279 : Blo 191804 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B733009 : Blo 191804 733009 := bstep (se 2 (by rfl) ⟨274878, by rfl⟩ : syracuseStep 733009 = 549757) B549757
theorem B438299 : Blo 191804 438299 := bstep (se 1 (by rfl) ⟨328724, by rfl⟩ : syracuseStep 438299 = 657449) B657449
theorem B208927 : Blo 191804 208927 := bstep (se 1 (by rfl) ⟨156695, by rfl⟩ : syracuseStep 208927 = 313391) B313391
theorem B832139 : Blo 191804 832139 := bstep (se 1 (by rfl) ⟨624104, by rfl⟩ : syracuseStep 832139 = 1248209) B1248209
theorem B439145 : Blo 191804 439145 := bstep (se 2 (by rfl) ⟨164679, by rfl⟩ : syracuseStep 439145 = 329359) B329359
theorem B5289761 : Blo 191804 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B1324907 : Blo 191804 1324907 := bstep (se 1 (by rfl) ⟨993680, by rfl⟩ : syracuseStep 1324907 = 1987361) B1987361
theorem B1095869 : Blo 191804 1095869 := bstep (se 3 (by rfl) ⟨205475, by rfl⟩ : syracuseStep 1095869 = 410951) B410951
theorem B735439 : Blo 191804 735439 := bstep (se 1 (by rfl) ⟨551579, by rfl⟩ : syracuseStep 735439 = 1103159) B1103159
theorem B2079017 : Blo 191804 2079017 := bstep (se 2 (by rfl) ⟨779631, by rfl⟩ : syracuseStep 2079017 = 1559263) B1559263
theorem B834239 : Blo 191804 834239 := bstep (se 1 (by rfl) ⟨625679, by rfl⟩ : syracuseStep 834239 = 1251359) B1251359
theorem B736411 : Blo 191804 736411 := bstep (se 1 (by rfl) ⟨552308, by rfl⟩ : syracuseStep 736411 = 1104617) B1104617
theorem B1097327 : Blo 191804 1097327 := bstep (se 1 (by rfl) ⟨822995, by rfl⟩ : syracuseStep 1097327 = 1645991) B1645991
theorem B5324791 : Blo 191804 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B1229215 : Blo 191804 1229215 := bstep (se 1 (by rfl) ⟨921911, by rfl⟩ : syracuseStep 1229215 = 1843823) B1843823
theorem B410849 : Blo 191804 410849 := bstep (se 2 (by rfl) ⟨154068, by rfl⟩ : syracuseStep 410849 = 308137) B308137
theorem B2540929 : Blo 191804 2540929 := bstep (se 2 (by rfl) ⟨952848, by rfl⟩ : syracuseStep 2540929 = 1905697) B1905697
theorem B346295 : Blo 191804 346295 := bstep (se 1 (by rfl) ⟨259721, by rfl⟩ : syracuseStep 346295 = 519443) B519443
theorem B5261735 : Blo 191804 5261735 := bstep (se 1 (by rfl) ⟨3946301, by rfl⟩ : syracuseStep 5261735 = 7892603) B7892603
theorem B2607839 : Blo 191804 2607839 := bstep (se 1 (by rfl) ⟨1955879, by rfl⟩ : syracuseStep 2607839 = 3911759) B3911759
theorem B413275 : Blo 191804 413275 := bstep (se 1 (by rfl) ⟨309956, by rfl⟩ : syracuseStep 413275 = 619913) B619913
theorem B741257 : Blo 191804 741257 := bstep (se 2 (by rfl) ⟨277971, by rfl⟩ : syracuseStep 741257 = 555943) B555943
theorem B1069331 : Blo 191804 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B5624417 : Blo 191804 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B742031 : Blo 191804 742031 := bstep (se 1 (by rfl) ⟨556523, by rfl⟩ : syracuseStep 742031 = 1113047) B1113047
theorem B2413999 : Blo 191804 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B218623 : Blo 191804 218623 := bstep (se 1 (by rfl) ⟨163967, by rfl⟩ : syracuseStep 218623 = 327935) B327935
theorem B743003 : Blo 191804 743003 := bstep (se 1 (by rfl) ⟨557252, by rfl⟩ : syracuseStep 743003 = 1114505) B1114505
theorem B1398383 : Blo 191804 1398383 := bstep (se 1 (by rfl) ⟨1048787, by rfl⟩ : syracuseStep 1398383 = 2097575) B2097575
theorem B219775 : Blo 191804 219775 := bstep (se 1 (by rfl) ⟨164831, by rfl⟩ : syracuseStep 219775 = 329663) B329663
theorem B416863 : Blo 191804 416863 := bstep (se 1 (by rfl) ⟨312647, by rfl⟩ : syracuseStep 416863 = 625295) B625295
theorem B712415 : Blo 191804 712415 := bstep (se 1 (by rfl) ⟨534311, by rfl⟩ : syracuseStep 712415 = 1068623) B1068623
theorem B2186999 : Blo 191804 2186999 := bstep (se 1 (by rfl) ⟨1640249, by rfl⟩ : syracuseStep 2186999 = 3280499) B3280499
theorem B647351 : Blo 191804 647351 := bstep (se 1 (by rfl) ⟨485513, by rfl⟩ : syracuseStep 647351 = 971027) B971027
theorem B2220533 : Blo 191804 2220533 := bstep (se 5 (by rfl) ⟨104087, by rfl⟩ : syracuseStep 2220533 = 208175) B208175
theorem B648107 : Blo 191804 648107 := bstep (se 1 (by rfl) ⟨486080, by rfl⟩ : syracuseStep 648107 = 972161) B972161
theorem B1401785 : Blo 191804 1401785 := bstep (se 2 (by rfl) ⟨525669, by rfl⟩ : syracuseStep 1401785 = 1051339) B1051339
theorem B1238237 : Blo 191804 1238237 := bstep (se 3 (by rfl) ⟨232169, by rfl⟩ : syracuseStep 1238237 = 464339) B464339
theorem B976211 : Blo 191804 976211 := bstep (se 1 (by rfl) ⟨732158, by rfl⟩ : syracuseStep 976211 = 1464317) B1464317
theorem B1336895 : Blo 191804 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B976697 : Blo 191804 976697 := bstep (se 2 (by rfl) ⟨366261, by rfl⟩ : syracuseStep 976697 = 732523) B732523
theorem B846281 : Blo 191804 846281 := bstep (se 2 (by rfl) ⟨317355, by rfl⟩ : syracuseStep 846281 = 634711) B634711
theorem B584347 : Blo 191804 584347 := bstep (se 1 (by rfl) ⟨438260, by rfl⟩ : syracuseStep 584347 = 876521) B876521
theorem B518813 : Blo 191804 518813 := bstep (se 3 (by rfl) ⟨97277, by rfl⟩ : syracuseStep 518813 = 194555) B194555
theorem B289487 : Blo 191804 289487 := bstep (se 1 (by rfl) ⟨217115, by rfl⟩ : syracuseStep 289487 = 434231) B434231
theorem B1862777 : Blo 191804 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B3337361 : Blo 191804 3337361 := bstep (se 2 (by rfl) ⟨1251510, by rfl⟩ : syracuseStep 3337361 = 2503021) B2503021
theorem B1240211 : Blo 191804 1240211 := bstep (se 1 (by rfl) ⟨930158, by rfl⟩ : syracuseStep 1240211 = 1860317) B1860317
theorem B23981275 : Blo 191804 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B978155 : Blo 191804 978155 := bstep (se 1 (by rfl) ⟨733616, by rfl⟩ : syracuseStep 978155 = 1467233) B1467233
theorem B191903 : Blo 191804 191903 := bstep (se 1 (by rfl) ⟨143927, by rfl⟩ : syracuseStep 191903 = 287855) B287855
theorem B191983 : Blo 191804 191983 := bstep (se 1 (by rfl) ⟨143987, by rfl⟩ : syracuseStep 191983 = 287975) B287975
theorem B192027 : Blo 191804 192027 := bstep (se 1 (by rfl) ⟨144020, by rfl⟩ : syracuseStep 192027 = 288041) B288041
theorem B290441 : Blo 191804 290441 := bstep (se 2 (by rfl) ⟨108915, by rfl⟩ : syracuseStep 290441 = 217831) B217831
theorem B290495 : Blo 191804 290495 := bstep (se 1 (by rfl) ⟨217871, by rfl⟩ : syracuseStep 290495 = 435743) B435743
theorem B192207 : Blo 191804 192207 := bstep (se 1 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 192207 = 288311) B288311
theorem B192423 : Blo 191804 192423 := bstep (se 1 (by rfl) ⟨144317, by rfl⟩ : syracuseStep 192423 = 288635) B288635
theorem B192447 : Blo 191804 192447 := bstep (se 1 (by rfl) ⟨144335, by rfl⟩ : syracuseStep 192447 = 288671) B288671
theorem B651239 : Blo 191804 651239 := bstep (se 1 (by rfl) ⟨488429, by rfl⟩ : syracuseStep 651239 = 976859) B976859
theorem B192603 : Blo 191804 192603 := bstep (se 1 (by rfl) ⟨144452, by rfl⟩ : syracuseStep 192603 = 288905) B288905
theorem B192703 : Blo 191804 192703 := bstep (se 1 (by rfl) ⟨144527, by rfl⟩ : syracuseStep 192703 = 289055) B289055
theorem B192735 : Blo 191804 192735 := bstep (se 1 (by rfl) ⟨144551, by rfl⟩ : syracuseStep 192735 = 289103) B289103
theorem B192795 : Blo 191804 192795 := bstep (se 1 (by rfl) ⟨144596, by rfl⟩ : syracuseStep 192795 = 289193) B289193
theorem B291113 : Blo 191804 291113 := bstep (se 2 (by rfl) ⟨109167, by rfl⟩ : syracuseStep 291113 = 218335) B218335
theorem B193051 : Blo 191804 193051 := bstep (se 1 (by rfl) ⟨144788, by rfl⟩ : syracuseStep 193051 = 289577) B289577
theorem B324263 : Blo 191804 324263 := bstep (se 1 (by rfl) ⟨243197, by rfl⟩ : syracuseStep 324263 = 486395) B486395
theorem B193191 : Blo 191804 193191 := bstep (se 1 (by rfl) ⟨144893, by rfl⟩ : syracuseStep 193191 = 289787) B289787
theorem B193231 : Blo 191804 193231 := bstep (se 1 (by rfl) ⟨144923, by rfl⟩ : syracuseStep 193231 = 289847) B289847
theorem B193311 : Blo 191804 193311 := bstep (se 1 (by rfl) ⟨144983, by rfl⟩ : syracuseStep 193311 = 289967) B289967
theorem B193351 : Blo 191804 193351 := bstep (se 1 (by rfl) ⟨145013, by rfl⟩ : syracuseStep 193351 = 290027) B290027
theorem B652265 : Blo 191804 652265 := bstep (se 2 (by rfl) ⟨244599, by rfl⟩ : syracuseStep 652265 = 489199) B489199
theorem B292031 : Blo 191804 292031 := bstep (se 1 (by rfl) ⟨219023, by rfl⟩ : syracuseStep 292031 = 438047) B438047
theorem B193791 : Blo 191804 193791 := bstep (se 1 (by rfl) ⟨145343, by rfl⟩ : syracuseStep 193791 = 290687) B290687
theorem B882103 : Blo 191804 882103 := bstep (se 1 (by rfl) ⟨661577, by rfl⟩ : syracuseStep 882103 = 1323155) B1323155
theorem B194015 : Blo 191804 194015 := bstep (se 1 (by rfl) ⟨145511, by rfl⟩ : syracuseStep 194015 = 291023) B291023
theorem B292379 : Blo 191804 292379 := bstep (se 1 (by rfl) ⟨219284, by rfl⟩ : syracuseStep 292379 = 438569) B438569
theorem B194095 : Blo 191804 194095 := bstep (se 1 (by rfl) ⟨145571, by rfl⟩ : syracuseStep 194095 = 291143) B291143
theorem B554633 : Blo 191804 554633 := bstep (se 2 (by rfl) ⟨207987, by rfl⟩ : syracuseStep 554633 = 415975) B415975
theorem B292559 : Blo 191804 292559 := bstep (se 1 (by rfl) ⟨219419, by rfl⟩ : syracuseStep 292559 = 438839) B438839
theorem B194407 : Blo 191804 194407 := bstep (se 1 (by rfl) ⟨145805, by rfl⟩ : syracuseStep 194407 = 291611) B291611
theorem B292799 : Blo 191804 292799 := bstep (se 1 (by rfl) ⟨219599, by rfl⟩ : syracuseStep 292799 = 439199) B439199
theorem B653291 : Blo 191804 653291 := bstep (se 1 (by rfl) ⟨489968, by rfl⟩ : syracuseStep 653291 = 979937) B979937
theorem B10516463 : Blo 191804 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B194591 : Blo 191804 194591 := bstep (se 1 (by rfl) ⟨145943, by rfl⟩ : syracuseStep 194591 = 291887) B291887
theorem B194623 : Blo 191804 194623 := bstep (se 1 (by rfl) ⟨145967, by rfl⟩ : syracuseStep 194623 = 291935) B291935
theorem B194663 : Blo 191804 194663 := bstep (se 1 (by rfl) ⟨145997, by rfl⟩ : syracuseStep 194663 = 291995) B291995
theorem B194671 : Blo 191804 194671 := bstep (se 1 (by rfl) ⟨146003, by rfl⟩ : syracuseStep 194671 = 292007) B292007
theorem B293351 : Blo 191804 293351 := bstep (se 1 (by rfl) ⟨220013, by rfl⟩ : syracuseStep 293351 = 440027) B440027
theorem B195119 : Blo 191804 195119 := bstep (se 1 (by rfl) ⟨146339, by rfl⟩ : syracuseStep 195119 = 292679) B292679
theorem B5569175 : Blo 191804 5569175 := bstep (se 1 (by rfl) ⟨4176881, by rfl⟩ : syracuseStep 5569175 = 8353763) B8353763
theorem B195239 : Blo 191804 195239 := bstep (se 1 (by rfl) ⟨146429, by rfl⟩ : syracuseStep 195239 = 292859) B292859
theorem B490171 : Blo 191804 490171 := bstep (se 1 (by rfl) ⟨367628, by rfl⟩ : syracuseStep 490171 = 735257) B735257
theorem B195279 : Blo 191804 195279 := bstep (se 1 (by rfl) ⟨146459, by rfl⟩ : syracuseStep 195279 = 292919) B292919
theorem B195323 : Blo 191804 195323 := bstep (se 1 (by rfl) ⟨146492, by rfl⟩ : syracuseStep 195323 = 292985) B292985
theorem B195359 : Blo 191804 195359 := bstep (se 1 (by rfl) ⟨146519, by rfl⟩ : syracuseStep 195359 = 293039) B293039
theorem B195519 : Blo 191804 195519 := bstep (se 1 (by rfl) ⟨146639, by rfl⟩ : syracuseStep 195519 = 293279) B293279
theorem B195579 : Blo 191804 195579 := bstep (se 1 (by rfl) ⟨146684, by rfl⟩ : syracuseStep 195579 = 293369) B293369
theorem B654479 : Blo 191804 654479 := bstep (se 1 (by rfl) ⟨490859, by rfl⟩ : syracuseStep 654479 = 981719) B981719
theorem B1244335 : Blo 191804 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B654695 : Blo 191804 654695 := bstep (se 1 (by rfl) ⟨491021, by rfl⟩ : syracuseStep 654695 = 982043) B982043
theorem B982529 : Blo 191804 982529 := bstep (se 2 (by rfl) ⟨368448, by rfl⟩ : syracuseStep 982529 = 736897) B736897
theorem B2489899 : Blo 191804 2489899 := bstep (se 1 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 2489899 = 3734849) B3734849
theorem B1638953 : Blo 191804 1638953 := bstep (se 2 (by rfl) ⟨614607, by rfl⟩ : syracuseStep 1638953 = 1229215) B1229215
theorem B2851549 : Blo 191804 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B328475 : Blo 191804 328475 := bstep (se 1 (by rfl) ⟨246356, by rfl⟩ : syracuseStep 328475 = 492713) B492713
theorem B230863 : Blo 191804 230863 := bstep (se 1 (by rfl) ⟨173147, by rfl⟩ : syracuseStep 230863 = 346295) B346295
theorem B3507823 : Blo 191804 3507823 := bstep (se 1 (by rfl) ⟨2630867, by rfl⟩ : syracuseStep 3507823 = 5261735) B5261735
theorem B1738559 : Blo 191804 1738559 := bstep (se 1 (by rfl) ⟨1303919, by rfl⟩ : syracuseStep 1738559 = 2607839) B2607839
theorem B657719 : Blo 191804 657719 := bstep (se 1 (by rfl) ⟨493289, by rfl⟩ : syracuseStep 657719 = 986579) B986579
theorem B494171 : Blo 191804 494171 := bstep (se 1 (by rfl) ⟨370628, by rfl⟩ : syracuseStep 494171 = 741257) B741257
theorem B494687 : Blo 191804 494687 := bstep (se 1 (by rfl) ⟨371015, by rfl⟩ : syracuseStep 494687 = 742031) B742031
theorem B3509725 : Blo 191804 3509725 := bstep (se 3 (by rfl) ⟨658073, by rfl⟩ : syracuseStep 3509725 = 1316147) B1316147
theorem B790013 : Blo 191804 790013 := bstep (se 3 (by rfl) ⟨148127, by rfl⟩ : syracuseStep 790013 = 296255) B296255
theorem B659015 : Blo 191804 659015 := bstep (se 1 (by rfl) ⟨494261, by rfl⟩ : syracuseStep 659015 = 988523) B988523
theorem B495335 : Blo 191804 495335 := bstep (se 1 (by rfl) ⟨371501, by rfl⟩ : syracuseStep 495335 = 743003) B743003
theorem B4034285 : Blo 191804 4034285 := bstep (se 3 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 4034285 = 1512857) B1512857
theorem B365161 : Blo 191804 365161 := bstep (se 2 (by rfl) ⟨136935, by rfl⟩ : syracuseStep 365161 = 273871) B273871
theorem B660095 : Blo 191804 660095 := bstep (se 1 (by rfl) ⟨495071, by rfl⟩ : syracuseStep 660095 = 990143) B990143
theorem B3020111 : Blo 191804 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B431567 : Blo 191804 431567 := bstep (se 1 (by rfl) ⟨323675, by rfl⟩ : syracuseStep 431567 = 647351) B647351
theorem B1480355 : Blo 191804 1480355 := bstep (se 1 (by rfl) ⟨1110266, by rfl⟩ : syracuseStep 1480355 = 2220533) B2220533
theorem B432071 : Blo 191804 432071 := bstep (se 1 (by rfl) ⟨324053, by rfl⟩ : syracuseStep 432071 = 648107) B648107
theorem B825491 : Blo 191804 825491 := bstep (se 1 (by rfl) ⟨619118, by rfl⟩ : syracuseStep 825491 = 1238237) B1238237
theorem B1907023 : Blo 191804 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B891263 : Blo 191804 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B564187 : Blo 191804 564187 := bstep (se 1 (by rfl) ⟨423140, by rfl⟩ : syracuseStep 564187 = 846281) B846281
theorem B14851133 : Blo 191804 14851133 := bstep (se 3 (by rfl) ⟨2784587, by rfl⟩ : syracuseStep 14851133 = 5569175) B5569175
theorem B3218665 : Blo 191804 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B826807 : Blo 191804 826807 := bstep (se 1 (by rfl) ⟨620105, by rfl⟩ : syracuseStep 826807 = 1240211) B1240211
theorem B2039519 : Blo 191804 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B434159 : Blo 191804 434159 := bstep (se 1 (by rfl) ⟨325619, by rfl⟩ : syracuseStep 434159 = 651239) B651239
theorem B434843 : Blo 191804 434843 := bstep (se 1 (by rfl) ⟨326132, by rfl⟩ : syracuseStep 434843 = 652265) B652265
theorem B369755 : Blo 191804 369755 := bstep (se 1 (by rfl) ⟨277316, by rfl⟩ : syracuseStep 369755 = 554633) B554633
theorem B435527 : Blo 191804 435527 := bstep (se 1 (by rfl) ⟨326645, by rfl⟩ : syracuseStep 435527 = 653291) B653291
theorem B730579 : Blo 191804 730579 := bstep (se 1 (by rfl) ⟨547934, by rfl⟩ : syracuseStep 730579 = 1095869) B1095869
theorem B1386011 : Blo 191804 1386011 := bstep (se 1 (by rfl) ⟨1039508, by rfl⟩ : syracuseStep 1386011 = 2079017) B2079017
theorem B3319865 : Blo 191804 3319865 := bstep (se 2 (by rfl) ⟨1244949, by rfl⟩ : syracuseStep 3319865 = 2489899) B2489899
theorem B436319 : Blo 191804 436319 := bstep (se 1 (by rfl) ⟨327239, by rfl⟩ : syracuseStep 436319 = 654479) B654479
theorem B436463 : Blo 191804 436463 := bstep (se 1 (by rfl) ⟨327347, by rfl⟩ : syracuseStep 436463 = 654695) B654695
theorem B731551 : Blo 191804 731551 := bstep (se 1 (by rfl) ⟨548663, by rfl⟩ : syracuseStep 731551 = 1097327) B1097327
theorem B437039 : Blo 191804 437039 := bstep (se 1 (by rfl) ⟨327779, by rfl⟩ : syracuseStep 437039 = 655559) B655559
theorem B1486187 : Blo 191804 1486187 := bstep (se 1 (by rfl) ⟨1114640, by rfl⟩ : syracuseStep 1486187 = 2229281) B2229281
theorem B437615 : Blo 191804 437615 := bstep (se 1 (by rfl) ⟨328211, by rfl⟩ : syracuseStep 437615 = 656423) B656423
theorem B699823 : Blo 191804 699823 := bstep (se 1 (by rfl) ⟨524867, by rfl⟩ : syracuseStep 699823 = 1049735) B1049735
theorem B273899 : Blo 191804 273899 := bstep (se 1 (by rfl) ⟨205424, by rfl⟩ : syracuseStep 273899 = 410849) B410849
theorem B438263 : Blo 191804 438263 := bstep (se 1 (by rfl) ⟨328697, by rfl⟩ : syracuseStep 438263 = 657395) B657395
theorem B438335 : Blo 191804 438335 := bstep (se 1 (by rfl) ⟨328751, by rfl⟩ : syracuseStep 438335 = 657503) B657503
theorem B3387905 : Blo 191804 3387905 := bstep (se 2 (by rfl) ⟨1270464, by rfl⟩ : syracuseStep 3387905 = 2540929) B2540929
theorem B439451 : Blo 191804 439451 := bstep (se 1 (by rfl) ⟨329588, by rfl⟩ : syracuseStep 439451 = 659177) B659177
theorem B3749611 : Blo 191804 3749611 := bstep (se 1 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 3749611 = 5624417) B5624417
theorem B440315 : Blo 191804 440315 := bstep (se 1 (by rfl) ⟨330236, by rfl⟩ : syracuseStep 440315 = 660473) B660473
theorem B243739 : Blo 191804 243739 := bstep (se 1 (by rfl) ⟨182804, by rfl⟩ : syracuseStep 243739 = 365609) B365609
theorem B833657 : Blo 191804 833657 := bstep (se 2 (by rfl) ⟨312621, by rfl⟩ : syracuseStep 833657 = 625243) B625243
theorem B932255 : Blo 191804 932255 := bstep (se 1 (by rfl) ⟨699191, by rfl⟩ : syracuseStep 932255 = 1398383) B1398383
theorem B441911 : Blo 191804 441911 := bstep (se 1 (by rfl) ⟨331433, by rfl⟩ : syracuseStep 441911 = 662867) B662867
theorem B441929 : Blo 191804 441929 := bstep (se 2 (by rfl) ⟨165723, by rfl⟩ : syracuseStep 441929 = 331447) B331447
theorem B1457999 : Blo 191804 1457999 := bstep (se 1 (by rfl) ⟨1093499, by rfl⟩ : syracuseStep 1457999 = 2186999) B2186999
theorem B278569 : Blo 191804 278569 := bstep (se 2 (by rfl) ⟨104463, by rfl⟩ : syracuseStep 278569 = 208927) B208927
theorem B245855 : Blo 191804 245855 := bstep (se 1 (by rfl) ⟨184391, by rfl⟩ : syracuseStep 245855 = 368783) B368783
theorem B934523 : Blo 191804 934523 := bstep (se 1 (by rfl) ⟨700892, by rfl⟩ : syracuseStep 934523 = 1401785) B1401785
theorem B246655 : Blo 191804 246655 := bstep (se 1 (by rfl) ⟨184991, by rfl⟩ : syracuseStep 246655 = 369983) B369983
theorem B1099241 : Blo 191804 1099241 := bstep (se 2 (by rfl) ⟨412215, by rfl⟩ : syracuseStep 1099241 = 824431) B824431
theorem B345875 : Blo 191804 345875 := bstep (se 1 (by rfl) ⟨259406, by rfl⟩ : syracuseStep 345875 = 518813) B518813
theorem B216175 : Blo 191804 216175 := bstep (se 1 (by rfl) ⟨162131, by rfl⟩ : syracuseStep 216175 = 324263) B324263
theorem B3526507 : Blo 191804 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B1659113 : Blo 191804 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B7099721 : Blo 191804 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B415223 : Blo 191804 415223 := bstep (se 1 (by rfl) ⟨311417, by rfl⟩ : syracuseStep 415223 = 622835) B622835
theorem B743215 : Blo 191804 743215 := bstep (se 1 (by rfl) ⟨557411, by rfl⟩ : syracuseStep 743215 = 1114823) B1114823
theorem B16570169 : Blo 191804 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B547411 : Blo 191804 547411 := bstep (se 1 (by rfl) ⟨410558, by rfl⟩ : syracuseStep 547411 = 821117) B821117
theorem B973457 : Blo 191804 973457 := bstep (se 2 (by rfl) ⟨365046, by rfl⟩ : syracuseStep 973457 = 730093) B730093
theorem B416411 : Blo 191804 416411 := bstep (se 1 (by rfl) ⟨312308, by rfl⟩ : syracuseStep 416411 = 624617) B624617
theorem B1465775 : Blo 191804 1465775 := bstep (se 1 (by rfl) ⟨1099331, by rfl⟩ : syracuseStep 1465775 = 2198663) B2198663
theorem B548527 : Blo 191804 548527 := bstep (se 1 (by rfl) ⟨411395, by rfl⟩ : syracuseStep 548527 = 822791) B822791
theorem B548687 : Blo 191804 548687 := bstep (se 1 (by rfl) ⟨411515, by rfl⟩ : syracuseStep 548687 = 823031) B823031
theorem B548927 : Blo 191804 548927 := bstep (se 1 (by rfl) ⟨411695, by rfl⟩ : syracuseStep 548927 = 823391) B823391
theorem B418127 : Blo 191804 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B779129 : Blo 191804 779129 := bstep (se 2 (by rfl) ⟨292173, by rfl⟩ : syracuseStep 779129 = 584347) B584347
theorem B549803 : Blo 191804 549803 := bstep (se 1 (by rfl) ⟨412352, by rfl⟩ : syracuseStep 549803 = 824705) B824705
theorem B287927 : Blo 191804 287927 := bstep (se 1 (by rfl) ⟨215945, by rfl⟩ : syracuseStep 287927 = 431891) B431891
theorem B550111 : Blo 191804 550111 := bstep (se 1 (by rfl) ⟨412583, by rfl⟩ : syracuseStep 550111 = 825167) B825167
theorem B288167 : Blo 191804 288167 := bstep (se 1 (by rfl) ⟨216125, by rfl⟩ : syracuseStep 288167 = 432251) B432251
theorem B615863 : Blo 191804 615863 := bstep (se 1 (by rfl) ⟨461897, by rfl⟩ : syracuseStep 615863 = 923795) B923795
theorem B31975033 : Blo 191804 31975033 := bstep (se 2 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 31975033 = 23981275) B23981275
theorem B288839 : Blo 191804 288839 := bstep (se 1 (by rfl) ⟨216629, by rfl⟩ : syracuseStep 288839 = 433259) B433259
theorem B551033 : Blo 191804 551033 := bstep (se 2 (by rfl) ⟨206637, by rfl⟩ : syracuseStep 551033 = 413275) B413275
theorem B977345 : Blo 191804 977345 := bstep (se 2 (by rfl) ⟨366504, by rfl⟩ : syracuseStep 977345 = 733009) B733009
theorem B289223 : Blo 191804 289223 := bstep (se 1 (by rfl) ⟨216917, by rfl⟩ : syracuseStep 289223 = 433835) B433835
theorem B289499 : Blo 191804 289499 := bstep (se 1 (by rfl) ⟨217124, by rfl⟩ : syracuseStep 289499 = 434249) B434249
theorem B486121 : Blo 191804 486121 := bstep (se 2 (by rfl) ⟨182295, by rfl⟩ : syracuseStep 486121 = 364591) B364591
theorem B289703 : Blo 191804 289703 := bstep (se 1 (by rfl) ⟨217277, by rfl⟩ : syracuseStep 289703 = 434555) B434555
theorem B289775 : Blo 191804 289775 := bstep (se 1 (by rfl) ⟨217331, by rfl⟩ : syracuseStep 289775 = 434663) B434663
theorem B290207 : Blo 191804 290207 := bstep (se 1 (by rfl) ⟨217655, by rfl⟩ : syracuseStep 290207 = 435311) B435311
theorem B650807 : Blo 191804 650807 := bstep (se 1 (by rfl) ⟨488105, by rfl⟩ : syracuseStep 650807 = 976211) B976211
theorem B290591 : Blo 191804 290591 := bstep (se 1 (by rfl) ⟨217943, by rfl⟩ : syracuseStep 290591 = 435887) B435887
theorem B651131 : Blo 191804 651131 := bstep (se 1 (by rfl) ⟨488348, by rfl⟩ : syracuseStep 651131 = 976697) B976697
theorem B290795 : Blo 191804 290795 := bstep (se 1 (by rfl) ⟨218096, by rfl⟩ : syracuseStep 290795 = 436193) B436193
theorem B291071 : Blo 191804 291071 := bstep (se 1 (by rfl) ⟨218303, by rfl⟩ : syracuseStep 291071 = 436607) B436607
theorem B553243 : Blo 191804 553243 := bstep (se 1 (by rfl) ⟨414932, by rfl⟩ : syracuseStep 553243 = 829865) B829865
theorem B192991 : Blo 191804 192991 := bstep (se 1 (by rfl) ⟨144743, by rfl⟩ : syracuseStep 192991 = 289487) B289487
theorem B1176137 : Blo 191804 1176137 := bstep (se 2 (by rfl) ⟨441051, by rfl⟩ : syracuseStep 1176137 = 882103) B882103
theorem B291497 : Blo 191804 291497 := bstep (se 2 (by rfl) ⟨109311, by rfl⟩ : syracuseStep 291497 = 218623) B218623
theorem B1241851 : Blo 191804 1241851 := bstep (se 1 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 1241851 = 1862777) B1862777
theorem B2224907 : Blo 191804 2224907 := bstep (se 1 (by rfl) ⟨1668680, by rfl⟩ : syracuseStep 2224907 = 3337361) B3337361
theorem B652103 : Blo 191804 652103 := bstep (se 1 (by rfl) ⟨489077, by rfl⟩ : syracuseStep 652103 = 978155) B978155
theorem B1405991 : Blo 191804 1405991 := bstep (se 1 (by rfl) ⟨1054493, by rfl⟩ : syracuseStep 1405991 = 2108987) B2108987
theorem B193627 : Blo 191804 193627 := bstep (se 1 (by rfl) ⟨145220, by rfl⟩ : syracuseStep 193627 = 290441) B290441
theorem B193663 : Blo 191804 193663 := bstep (se 1 (by rfl) ⟨145247, by rfl⟩ : syracuseStep 193663 = 290495) B290495
theorem B292199 : Blo 191804 292199 := bstep (se 1 (by rfl) ⟨219149, by rfl⟩ : syracuseStep 292199 = 438299) B438299
theorem B194075 : Blo 191804 194075 := bstep (se 1 (by rfl) ⟨145556, by rfl⟩ : syracuseStep 194075 = 291113) B291113
theorem B980585 : Blo 191804 980585 := bstep (se 2 (by rfl) ⟨367719, by rfl⟩ : syracuseStep 980585 = 735439) B735439
theorem B554759 : Blo 191804 554759 := bstep (se 1 (by rfl) ⟨416069, by rfl⟩ : syracuseStep 554759 = 832139) B832139
theorem B292763 : Blo 191804 292763 := bstep (se 1 (by rfl) ⟨219572, by rfl⟩ : syracuseStep 292763 = 439145) B439145
theorem B194687 : Blo 191804 194687 := bstep (se 1 (by rfl) ⟨146015, by rfl⟩ : syracuseStep 194687 = 292031) B292031
theorem B293033 : Blo 191804 293033 := bstep (se 2 (by rfl) ⟨109887, by rfl⟩ : syracuseStep 293033 = 219775) B219775
theorem B653561 : Blo 191804 653561 := bstep (se 2 (by rfl) ⟨245085, by rfl⟩ : syracuseStep 653561 = 490171) B490171
theorem B194919 : Blo 191804 194919 := bstep (se 1 (by rfl) ⟨146189, by rfl⟩ : syracuseStep 194919 = 292379) B292379
theorem B195039 : Blo 191804 195039 := bstep (se 1 (by rfl) ⟨146279, by rfl⟩ : syracuseStep 195039 = 292559) B292559
theorem B883271 : Blo 191804 883271 := bstep (se 1 (by rfl) ⟨662453, by rfl⟩ : syracuseStep 883271 = 1324907) B1324907
theorem B195199 : Blo 191804 195199 := bstep (se 1 (by rfl) ⟨146399, by rfl⟩ : syracuseStep 195199 = 292799) B292799
theorem B7010975 : Blo 191804 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B555817 : Blo 191804 555817 := bstep (se 2 (by rfl) ⟨208431, by rfl⟩ : syracuseStep 555817 = 416863) B416863
theorem B981881 : Blo 191804 981881 := bstep (se 2 (by rfl) ⟨368205, by rfl⟩ : syracuseStep 981881 = 736411) B736411
theorem B195567 : Blo 191804 195567 := bstep (se 1 (by rfl) ⟨146675, by rfl⟩ : syracuseStep 195567 = 293351) B293351
theorem B556159 : Blo 191804 556159 := bstep (se 1 (by rfl) ⟨417119, by rfl⟩ : syracuseStep 556159 = 834239) B834239
theorem B490657 : Blo 191804 490657 := bstep (se 2 (by rfl) ⟨183996, by rfl⟩ : syracuseStep 490657 = 367993) B367993
theorem B1899773 : Blo 191804 1899773 := bstep (se 3 (by rfl) ⟨356207, by rfl⟩ : syracuseStep 1899773 = 712415) B712415
theorem B655019 : Blo 191804 655019 := bstep (se 1 (by rfl) ⟨491264, by rfl⟩ : syracuseStep 655019 = 982529) B982529
theorem B655613 : Blo 191804 655613 := bstep (se 3 (by rfl) ⟨122927, by rfl⟩ : syracuseStep 655613 = 245855) B245855
theorem B623015 : Blo 191804 623015 := bstep (se 1 (by rfl) ⟨467261, by rfl⟩ : syracuseStep 623015 = 934523) B934523
theorem B1115005 : Blo 191804 1115005 := bstep (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) B418127
theorem B328873 : Blo 191804 328873 := bstep (se 2 (by rfl) ⟨123327, by rfl⟩ : syracuseStep 328873 = 246655) B246655
theorem B329447 : Blo 191804 329447 := bstep (se 1 (by rfl) ⟨247085, by rfl⟩ : syracuseStep 329447 = 494171) B494171
theorem B329791 : Blo 191804 329791 := bstep (se 1 (by rfl) ⟨247343, by rfl⟩ : syracuseStep 329791 = 494687) B494687
theorem B42633377 : Blo 191804 42633377 := bstep (se 2 (by rfl) ⟨15987516, by rfl⟩ : syracuseStep 42633377 = 31975033) B31975033
theorem B526675 : Blo 191804 526675 := bstep (se 1 (by rfl) ⟨395006, by rfl⟩ : syracuseStep 526675 = 790013) B790013
theorem B330223 : Blo 191804 330223 := bstep (se 1 (by rfl) ⟨247667, by rfl⟩ : syracuseStep 330223 = 495335) B495335
theorem B2689523 : Blo 191804 2689523 := bstep (se 1 (by rfl) ⟨2017142, by rfl⟩ : syracuseStep 2689523 = 4034285) B4034285
theorem B986903 : Blo 191804 986903 := bstep (se 1 (by rfl) ⟨740177, by rfl⟩ : syracuseStep 986903 = 1480355) B1480355
theorem B1642301 : Blo 191804 1642301 := bstep (se 3 (by rfl) ⟨307931, by rfl⟩ : syracuseStep 1642301 = 615863) B615863
theorem B11046779 : Blo 191804 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B9900755 : Blo 191804 9900755 := bstep (se 1 (by rfl) ⟨7425566, by rfl⟩ : syracuseStep 9900755 = 14851133) B14851133
theorem B365791 : Blo 191804 365791 := bstep (se 1 (by rfl) ⟨274343, by rfl⟩ : syracuseStep 365791 = 548687) B548687
theorem B365951 : Blo 191804 365951 := bstep (se 1 (by rfl) ⟨274463, by rfl⟩ : syracuseStep 365951 = 548927) B548927
theorem B366535 : Blo 191804 366535 := bstep (se 1 (by rfl) ⟨274901, by rfl⟩ : syracuseStep 366535 = 549803) B549803
theorem B367355 : Blo 191804 367355 := bstep (se 1 (by rfl) ⟨275516, by rfl⟩ : syracuseStep 367355 = 551033) B551033
theorem B990791 : Blo 191804 990791 := bstep (se 1 (by rfl) ⟨743093, by rfl⟩ : syracuseStep 990791 = 1486187) B1486187
theorem B433871 : Blo 191804 433871 := bstep (se 1 (by rfl) ⟨325403, by rfl⟩ : syracuseStep 433871 = 650807) B650807
theorem B990953 : Blo 191804 990953 := bstep (se 2 (by rfl) ⟨371607, by rfl⟩ : syracuseStep 990953 = 743215) B743215
theorem B434087 : Blo 191804 434087 := bstep (se 1 (by rfl) ⟨325565, by rfl⟩ : syracuseStep 434087 = 651131) B651131
theorem B1483271 : Blo 191804 1483271 := bstep (se 1 (by rfl) ⟨1112453, by rfl⟩ : syracuseStep 1483271 = 2224907) B2224907
theorem B434735 : Blo 191804 434735 := bstep (se 1 (by rfl) ⟨326051, by rfl⟩ : syracuseStep 434735 = 652103) B652103
theorem B729881 : Blo 191804 729881 := bstep (se 2 (by rfl) ⟨273705, by rfl⟩ : syracuseStep 729881 = 547411) B547411
theorem B369839 : Blo 191804 369839 := bstep (se 1 (by rfl) ⟨277379, by rfl⟩ : syracuseStep 369839 = 554759) B554759
theorem B730397 : Blo 191804 730397 := bstep (se 3 (by rfl) ⟨136949, by rfl⟩ : syracuseStep 730397 = 273899) B273899
theorem B435707 : Blo 191804 435707 := bstep (se 1 (by rfl) ⟨326780, by rfl⟩ : syracuseStep 435707 = 653561) B653561
theorem B731369 : Blo 191804 731369 := bstep (se 2 (by rfl) ⟨274263, by rfl⟩ : syracuseStep 731369 = 548527) B548527
theorem B436679 : Blo 191804 436679 := bstep (se 1 (by rfl) ⟨327509, by rfl⟩ : syracuseStep 436679 = 655019) B655019
theorem B1485701 : Blo 191804 1485701 := bstep (se 4 (by rfl) ⟨139284, by rfl⟩ : syracuseStep 1485701 = 278569) B278569
theorem B1092635 : Blo 191804 1092635 := bstep (se 1 (by rfl) ⟨819476, by rfl⟩ : syracuseStep 1092635 = 1638953) B1638953
theorem B732827 : Blo 191804 732827 := bstep (se 1 (by rfl) ⟨549620, by rfl⟩ : syracuseStep 732827 = 1099241) B1099241
theorem B1159039 : Blo 191804 1159039 := bstep (se 1 (by rfl) ⟨869279, by rfl⟩ : syracuseStep 1159039 = 1738559) B1738559
theorem B8892341 : Blo 191804 8892341 := bstep (se 5 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 8892341 = 833657) B833657
theorem B438479 : Blo 191804 438479 := bstep (se 1 (by rfl) ⟨328859, by rfl⟩ : syracuseStep 438479 = 657719) B657719
theorem B733481 : Blo 191804 733481 := bstep (se 2 (by rfl) ⟨275055, by rfl⟩ : syracuseStep 733481 = 550111) B550111
theorem B307817 : Blo 191804 307817 := bstep (se 2 (by rfl) ⟨115431, by rfl⟩ : syracuseStep 307817 = 230863) B230863
theorem B439343 : Blo 191804 439343 := bstep (se 1 (by rfl) ⟨329507, by rfl⟩ : syracuseStep 439343 = 659015) B659015
theorem B440063 : Blo 191804 440063 := bstep (se 1 (by rfl) ⟨330047, by rfl⟩ : syracuseStep 440063 = 660095) B660095
theorem B4733147 : Blo 191804 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B2013407 : Blo 191804 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B276815 : Blo 191804 276815 := bstep (se 1 (by rfl) ⟨207611, by rfl⟩ : syracuseStep 276815 = 415223) B415223
theorem B277607 : Blo 191804 277607 := bstep (se 1 (by rfl) ⟨208205, by rfl⟩ : syracuseStep 277607 = 416411) B416411
theorem B60833045 : Blo 191804 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B4702009 : Blo 191804 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B1359679 : Blo 191804 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B737657 : Blo 191804 737657 := bstep (se 2 (by rfl) ⟨276621, by rfl⟩ : syracuseStep 737657 = 553243) B553243
theorem B246503 : Blo 191804 246503 := bstep (se 1 (by rfl) ⟨184877, by rfl⟩ : syracuseStep 246503 = 369755) B369755
theorem B1655801 : Blo 191804 1655801 := bstep (se 2 (by rfl) ⟨620925, by rfl⟩ : syracuseStep 1655801 = 1241851) B1241851
theorem B2376701 : Blo 191804 2376701 := bstep (se 3 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 2376701 = 891263) B891263
theorem B2213243 : Blo 191804 2213243 := bstep (se 1 (by rfl) ⟨1659932, by rfl⟩ : syracuseStep 2213243 = 3319865) B3319865
theorem B18695933 : Blo 191804 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B4999481 : Blo 191804 4999481 := bstep (se 2 (by rfl) ⟨1874805, by rfl⟩ : syracuseStep 4999481 = 3749611) B3749611
theorem B3689333 : Blo 191804 3689333 := bstep (se 5 (by rfl) ⟨172937, by rfl⟩ : syracuseStep 3689333 = 345875) B345875
theorem B2542697 : Blo 191804 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B937327 : Blo 191804 937327 := bstep (se 1 (by rfl) ⟨702995, by rfl⟩ : syracuseStep 937327 = 1405991) B1405991
theorem B741089 : Blo 191804 741089 := bstep (se 2 (by rfl) ⟨277908, by rfl⟩ : syracuseStep 741089 = 555817) B555817
theorem B741545 : Blo 191804 741545 := bstep (se 2 (by rfl) ⟨278079, by rfl⟩ : syracuseStep 741545 = 556159) B556159
theorem B1102409 : Blo 191804 1102409 := bstep (se 2 (by rfl) ⟨413403, by rfl⟩ : syracuseStep 1102409 = 826807) B826807
theorem B1266515 : Blo 191804 1266515 := bstep (se 1 (by rfl) ⟨949886, by rfl⟩ : syracuseStep 1266515 = 1899773) B1899773
theorem B971999 : Blo 191804 971999 := bstep (se 1 (by rfl) ⟨728999, by rfl⟩ : syracuseStep 971999 = 1457999) B1457999
theorem B218983 : Blo 191804 218983 := bstep (se 1 (by rfl) ⟨164237, by rfl⟩ : syracuseStep 218983 = 328475) B328475
theorem B974105 : Blo 191804 974105 := bstep (se 2 (by rfl) ⟨365289, by rfl⟩ : syracuseStep 974105 = 730579) B730579
theorem B4677097 : Blo 191804 4677097 := bstep (se 2 (by rfl) ⟨1753911, by rfl⟩ : syracuseStep 4677097 = 3507823) B3507823
theorem B1106075 : Blo 191804 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B975401 : Blo 191804 975401 := bstep (se 2 (by rfl) ⟨365775, by rfl⟩ : syracuseStep 975401 = 731551) B731551
theorem B287711 : Blo 191804 287711 := bstep (se 1 (by rfl) ⟨215783, by rfl⟩ : syracuseStep 287711 = 431567) B431567
theorem B648161 : Blo 191804 648161 := bstep (se 2 (by rfl) ⟨243060, by rfl⟩ : syracuseStep 648161 = 486121) B486121
theorem B288047 : Blo 191804 288047 := bstep (se 1 (by rfl) ⟨216035, by rfl⟩ : syracuseStep 288047 = 432071) B432071
theorem B3696029 : Blo 191804 3696029 := bstep (se 3 (by rfl) ⟨693005, by rfl⟩ : syracuseStep 3696029 = 1386011) B1386011
theorem B550327 : Blo 191804 550327 := bstep (se 1 (by rfl) ⟨412745, by rfl⟩ : syracuseStep 550327 = 825491) B825491
theorem B288233 : Blo 191804 288233 := bstep (se 2 (by rfl) ⟨108087, by rfl⟩ : syracuseStep 288233 = 216175) B216175
theorem B648971 : Blo 191804 648971 := bstep (se 1 (by rfl) ⟨486728, by rfl⟩ : syracuseStep 648971 = 973457) B973457
theorem B4679633 : Blo 191804 4679633 := bstep (se 2 (by rfl) ⟨1754862, by rfl⟩ : syracuseStep 4679633 = 3509725) B3509725
theorem B977183 : Blo 191804 977183 := bstep (se 1 (by rfl) ⟨732887, by rfl⟩ : syracuseStep 977183 = 1465775) B1465775
theorem B289439 : Blo 191804 289439 := bstep (se 1 (by rfl) ⟨217079, by rfl⟩ : syracuseStep 289439 = 434159) B434159
theorem B289895 : Blo 191804 289895 := bstep (se 1 (by rfl) ⟨217421, by rfl⟩ : syracuseStep 289895 = 434843) B434843
theorem B519419 : Blo 191804 519419 := bstep (se 1 (by rfl) ⟨389564, by rfl⟩ : syracuseStep 519419 = 779129) B779129
theorem B191951 : Blo 191804 191951 := bstep (se 1 (by rfl) ⟨143963, by rfl⟩ : syracuseStep 191951 = 287927) B287927
theorem B486881 : Blo 191804 486881 := bstep (se 2 (by rfl) ⟨182580, by rfl⟩ : syracuseStep 486881 = 365161) B365161
theorem B290351 : Blo 191804 290351 := bstep (se 1 (by rfl) ⟨217763, by rfl⟩ : syracuseStep 290351 = 435527) B435527
theorem B192111 : Blo 191804 192111 := bstep (se 1 (by rfl) ⟨144083, by rfl⟩ : syracuseStep 192111 = 288167) B288167
theorem B192559 : Blo 191804 192559 := bstep (se 1 (by rfl) ⟨144419, by rfl⟩ : syracuseStep 192559 = 288839) B288839
theorem B290879 : Blo 191804 290879 := bstep (se 1 (by rfl) ⟨218159, by rfl⟩ : syracuseStep 290879 = 436319) B436319
theorem B290975 : Blo 191804 290975 := bstep (se 1 (by rfl) ⟨218231, by rfl⟩ : syracuseStep 290975 = 436463) B436463
theorem B2355389 : Blo 191804 2355389 := bstep (se 3 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 2355389 = 883271) B883271
theorem B651563 : Blo 191804 651563 := bstep (se 1 (by rfl) ⟨488672, by rfl⟩ : syracuseStep 651563 = 977345) B977345
theorem B192815 : Blo 191804 192815 := bstep (se 1 (by rfl) ⟨144611, by rfl⟩ : syracuseStep 192815 = 289223) B289223
theorem B192999 : Blo 191804 192999 := bstep (se 1 (by rfl) ⟨144749, by rfl⟩ : syracuseStep 192999 = 289499) B289499
theorem B291359 : Blo 191804 291359 := bstep (se 1 (by rfl) ⟨218519, by rfl⟩ : syracuseStep 291359 = 437039) B437039
theorem B193135 : Blo 191804 193135 := bstep (se 1 (by rfl) ⟨144851, by rfl⟩ : syracuseStep 193135 = 289703) B289703
theorem B193183 : Blo 191804 193183 := bstep (se 1 (by rfl) ⟨144887, by rfl⟩ : syracuseStep 193183 = 289775) B289775
theorem B291743 : Blo 191804 291743 := bstep (se 1 (by rfl) ⟨218807, by rfl⟩ : syracuseStep 291743 = 437615) B437615
theorem B3732389 : Blo 191804 3732389 := bstep (se 4 (by rfl) ⟨349911, by rfl⟩ : syracuseStep 3732389 = 699823) B699823
theorem B193471 : Blo 191804 193471 := bstep (se 1 (by rfl) ⟨145103, by rfl⟩ : syracuseStep 193471 = 290207) B290207
theorem B193727 : Blo 191804 193727 := bstep (se 1 (by rfl) ⟨145295, by rfl⟩ : syracuseStep 193727 = 290591) B290591
theorem B193863 : Blo 191804 193863 := bstep (se 1 (by rfl) ⟨145397, by rfl⟩ : syracuseStep 193863 = 290795) B290795
theorem B292175 : Blo 191804 292175 := bstep (se 1 (by rfl) ⟨219131, by rfl⟩ : syracuseStep 292175 = 438263) B438263
theorem B324985 : Blo 191804 324985 := bstep (se 2 (by rfl) ⟨121869, by rfl⟩ : syracuseStep 324985 = 243739) B243739
theorem B292223 : Blo 191804 292223 := bstep (se 1 (by rfl) ⟨219167, by rfl⟩ : syracuseStep 292223 = 438335) B438335
theorem B194047 : Blo 191804 194047 := bstep (se 1 (by rfl) ⟨145535, by rfl⟩ : syracuseStep 194047 = 291071) B291071
theorem B2258603 : Blo 191804 2258603 := bstep (se 1 (by rfl) ⟨1693952, by rfl⟩ : syracuseStep 2258603 = 3387905) B3387905
theorem B784091 : Blo 191804 784091 := bstep (se 1 (by rfl) ⟨588068, by rfl⟩ : syracuseStep 784091 = 1176137) B1176137
theorem B194331 : Blo 191804 194331 := bstep (se 1 (by rfl) ⟨145748, by rfl⟩ : syracuseStep 194331 = 291497) B291497
theorem B292967 : Blo 191804 292967 := bstep (se 1 (by rfl) ⟨219725, by rfl⟩ : syracuseStep 292967 = 439451) B439451
theorem B194799 : Blo 191804 194799 := bstep (se 1 (by rfl) ⟨146099, by rfl⟩ : syracuseStep 194799 = 292199) B292199
theorem B653723 : Blo 191804 653723 := bstep (se 1 (by rfl) ⟨490292, by rfl⟩ : syracuseStep 653723 = 980585) B980585
theorem B195175 : Blo 191804 195175 := bstep (se 1 (by rfl) ⟨146381, by rfl⟩ : syracuseStep 195175 = 292763) B292763
theorem B752249 : Blo 191804 752249 := bstep (se 2 (by rfl) ⟨282093, by rfl⟩ : syracuseStep 752249 = 564187) B564187
theorem B293543 : Blo 191804 293543 := bstep (se 1 (by rfl) ⟨220157, by rfl⟩ : syracuseStep 293543 = 440315) B440315
theorem B195355 : Blo 191804 195355 := bstep (se 1 (by rfl) ⟨146516, by rfl⟩ : syracuseStep 195355 = 293033) B293033
theorem B654209 : Blo 191804 654209 := bstep (se 2 (by rfl) ⟨245328, by rfl⟩ : syracuseStep 654209 = 490657) B490657
theorem B621503 : Blo 191804 621503 := bstep (se 1 (by rfl) ⟨466127, by rfl⟩ : syracuseStep 621503 = 932255) B932255
theorem B4291553 : Blo 191804 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B654587 : Blo 191804 654587 := bstep (se 1 (by rfl) ⟨490940, by rfl⟩ : syracuseStep 654587 = 981881) B981881
theorem B294607 : Blo 191804 294607 := bstep (se 1 (by rfl) ⟨220955, by rfl⟩ : syracuseStep 294607 = 441911) B441911
theorem B294619 : Blo 191804 294619 := bstep (se 1 (by rfl) ⟨220964, by rfl⟩ : syracuseStep 294619 = 441929) B441929
theorem B491771 : Blo 191804 491771 := bstep (se 1 (by rfl) ⟨368828, by rfl⟩ : syracuseStep 491771 = 737657) B737657
theorem B1475495 : Blo 191804 1475495 := bstep (se 1 (by rfl) ⟨1106621, by rfl⟩ : syracuseStep 1475495 = 2213243) B2213243
theorem B2459555 : Blo 191804 2459555 := bstep (se 1 (by rfl) ⟨1844666, by rfl⟩ : syracuseStep 2459555 = 3689333) B3689333
theorem B657341 : Blo 191804 657341 := bstep (se 3 (by rfl) ⟨123251, by rfl⟩ : syracuseStep 657341 = 246503) B246503
theorem B494059 : Blo 191804 494059 := bstep (se 1 (by rfl) ⟨370544, by rfl⟩ : syracuseStep 494059 = 741089) B741089
theorem B657935 : Blo 191804 657935 := bstep (se 1 (by rfl) ⟨493451, by rfl⟩ : syracuseStep 657935 = 986903) B986903
theorem B494363 : Blo 191804 494363 := bstep (se 1 (by rfl) ⟨370772, by rfl⟩ : syracuseStep 494363 = 741545) B741545
theorem B1249769 : Blo 191804 1249769 := bstep (se 2 (by rfl) ⟨468663, by rfl⟩ : syracuseStep 1249769 = 937327) B937327
theorem B660527 : Blo 191804 660527 := bstep (se 1 (by rfl) ⟨495395, by rfl⟩ : syracuseStep 660527 = 990791) B990791
theorem B660635 : Blo 191804 660635 := bstep (se 1 (by rfl) ⟨495476, by rfl⟩ : syracuseStep 660635 = 990953) B990953
theorem B988847 : Blo 191804 988847 := bstep (se 1 (by rfl) ⟨741635, by rfl⟩ : syracuseStep 988847 = 1483271) B1483271
theorem B432107 : Blo 191804 432107 := bstep (se 1 (by rfl) ⟨324080, by rfl⟩ : syracuseStep 432107 = 648161) B648161
theorem B2464019 : Blo 191804 2464019 := bstep (se 1 (by rfl) ⟨1848014, by rfl⟩ : syracuseStep 2464019 = 3696029) B3696029
theorem B432647 : Blo 191804 432647 := bstep (se 1 (by rfl) ⟨324485, by rfl⟩ : syracuseStep 432647 = 648971) B648971
theorem B433313 : Blo 191804 433313 := bstep (se 2 (by rfl) ⟨162492, by rfl⟩ : syracuseStep 433313 = 324985) B324985
theorem B990467 : Blo 191804 990467 := bstep (se 1 (by rfl) ⟨742850, by rfl⟩ : syracuseStep 990467 = 1485701) B1485701
theorem B728423 : Blo 191804 728423 := bstep (se 1 (by rfl) ⟨546317, by rfl⟩ : syracuseStep 728423 = 1092635) B1092635
theorem B11444141 : Blo 191804 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B434375 : Blo 191804 434375 := bstep (se 1 (by rfl) ⟨325781, by rfl⟩ : syracuseStep 434375 = 651563) B651563
theorem B205211 : Blo 191804 205211 := bstep (se 1 (by rfl) ⟨153908, by rfl⟩ : syracuseStep 205211 = 307817) B307817
theorem B3155431 : Blo 191804 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B435815 : Blo 191804 435815 := bstep (se 1 (by rfl) ⟨326861, by rfl⟩ : syracuseStep 435815 = 653723) B653723
theorem B501499 : Blo 191804 501499 := bstep (se 1 (by rfl) ⟨376124, by rfl⟩ : syracuseStep 501499 = 752249) B752249
theorem B436139 : Blo 191804 436139 := bstep (se 1 (by rfl) ⟨327104, by rfl⟩ : syracuseStep 436139 = 654209) B654209
theorem B6236129 : Blo 191804 6236129 := bstep (se 2 (by rfl) ⟨2338548, by rfl⟩ : syracuseStep 6236129 = 4677097) B4677097
theorem B436391 : Blo 191804 436391 := bstep (se 1 (by rfl) ⟨327293, by rfl⟩ : syracuseStep 436391 = 654587) B654587
theorem B6269345 : Blo 191804 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B1812905 : Blo 191804 1812905 := bstep (se 2 (by rfl) ⟨679839, by rfl⟩ : syracuseStep 1812905 = 1359679) B1359679
theorem B437075 : Blo 191804 437075 := bstep (se 1 (by rfl) ⟨327806, by rfl⟩ : syracuseStep 437075 = 655613) B655613
theorem B1584467 : Blo 191804 1584467 := bstep (se 1 (by rfl) ⟨1188350, by rfl⟩ : syracuseStep 1584467 = 2376701) B2376701
theorem B1486673 : Blo 191804 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B12463955 : Blo 191804 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B28422251 : Blo 191804 28422251 := bstep (se 1 (by rfl) ⟨21316688, by rfl⟩ : syracuseStep 28422251 = 42633377) B42633377
theorem B438497 : Blo 191804 438497 := bstep (se 2 (by rfl) ⟨164436, by rfl⟩ : syracuseStep 438497 = 328873) B328873
theorem B733769 : Blo 191804 733769 := bstep (se 2 (by rfl) ⟨275163, by rfl⟩ : syracuseStep 733769 = 550327) B550327
theorem B1094867 : Blo 191804 1094867 := bstep (se 1 (by rfl) ⟨821150, by rfl⟩ : syracuseStep 1094867 = 1642301) B1642301
theorem B439721 : Blo 191804 439721 := bstep (se 2 (by rfl) ⟨164895, by rfl⟩ : syracuseStep 439721 = 329791) B329791
theorem B734939 : Blo 191804 734939 := bstep (se 1 (by rfl) ⟨551204, by rfl⟩ : syracuseStep 734939 = 1102409) B1102409
theorem B702233 : Blo 191804 702233 := bstep (se 2 (by rfl) ⟨263337, by rfl⟩ : syracuseStep 702233 = 526675) B526675
theorem B6600503 : Blo 191804 6600503 := bstep (se 1 (by rfl) ⟨4950377, by rfl⟩ : syracuseStep 6600503 = 9900755) B9900755
theorem B440297 : Blo 191804 440297 := bstep (se 2 (by rfl) ⟨165111, by rfl⟩ : syracuseStep 440297 = 330223) B330223
theorem B243967 : Blo 191804 243967 := bstep (se 1 (by rfl) ⟨182975, by rfl⟩ : syracuseStep 243967 = 365951) B365951
theorem B737383 : Blo 191804 737383 := bstep (se 1 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 737383 = 1106075) B1106075
theorem B246559 : Blo 191804 246559 := bstep (se 1 (by rfl) ⟨184919, by rfl⟩ : syracuseStep 246559 = 369839) B369839
theorem B738173 : Blo 191804 738173 := bstep (se 3 (by rfl) ⟨138407, by rfl⟩ : syracuseStep 738173 = 276815) B276815
theorem B346279 : Blo 191804 346279 := bstep (se 1 (by rfl) ⟨259709, by rfl⟩ : syracuseStep 346279 = 519419) B519419
theorem B740285 : Blo 191804 740285 := bstep (se 3 (by rfl) ⟨138803, by rfl⟩ : syracuseStep 740285 = 277607) B277607
theorem B414335 : Blo 191804 414335 := bstep (se 1 (by rfl) ⟨310751, by rfl⟩ : syracuseStep 414335 = 621503) B621503
theorem B6181541 : Blo 191804 6181541 := bstep (se 4 (by rfl) ⟨579519, by rfl⟩ : syracuseStep 6181541 = 1159039) B1159039
theorem B40555363 : Blo 191804 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B415343 : Blo 191804 415343 := bstep (se 1 (by rfl) ⟨311507, by rfl⟩ : syracuseStep 415343 = 623015) B623015
theorem B1103867 : Blo 191804 1103867 := bstep (se 1 (by rfl) ⟨827900, by rfl⟩ : syracuseStep 1103867 = 1655801) B1655801
theorem B219631 : Blo 191804 219631 := bstep (se 1 (by rfl) ⟨164723, by rfl⟩ : syracuseStep 219631 = 329447) B329447
theorem B3332987 : Blo 191804 3332987 := bstep (se 1 (by rfl) ⟨2499740, by rfl⟩ : syracuseStep 3332987 = 4999481) B4999481
theorem B1793015 : Blo 191804 1793015 := bstep (se 1 (by rfl) ⟨1344761, by rfl⟩ : syracuseStep 1793015 = 2689523) B2689523
theorem B1695131 : Blo 191804 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B7364519 : Blo 191804 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B844343 : Blo 191804 844343 := bstep (se 1 (by rfl) ⟨633257, by rfl⟩ : syracuseStep 844343 = 1266515) B1266515
theorem B647999 : Blo 191804 647999 := bstep (se 1 (by rfl) ⟨485999, by rfl⟩ : syracuseStep 647999 = 971999) B971999
theorem B2090909 : Blo 191804 2090909 := bstep (se 3 (by rfl) ⟨392045, by rfl⟩ : syracuseStep 2090909 = 784091) B784091
theorem B649403 : Blo 191804 649403 := bstep (se 1 (by rfl) ⟨487052, by rfl⟩ : syracuseStep 649403 = 974105) B974105
theorem B289247 : Blo 191804 289247 := bstep (se 1 (by rfl) ⟨216935, by rfl⟩ : syracuseStep 289247 = 433871) B433871
theorem B12479021 : Blo 191804 12479021 := bstep (se 3 (by rfl) ⟨2339816, by rfl⟩ : syracuseStep 12479021 = 4679633) B4679633
theorem B289391 : Blo 191804 289391 := bstep (se 1 (by rfl) ⟨217043, by rfl⟩ : syracuseStep 289391 = 434087) B434087
theorem B650267 : Blo 191804 650267 := bstep (se 1 (by rfl) ⟨487700, by rfl⟩ : syracuseStep 650267 = 975401) B975401
theorem B289823 : Blo 191804 289823 := bstep (se 1 (by rfl) ⟨217367, by rfl⟩ : syracuseStep 289823 = 434735) B434735
theorem B486587 : Blo 191804 486587 := bstep (se 1 (by rfl) ⟨364940, by rfl⟩ : syracuseStep 486587 = 729881) B729881
theorem B191807 : Blo 191804 191807 := bstep (se 1 (by rfl) ⟨143855, by rfl⟩ : syracuseStep 191807 = 287711) B287711
theorem B486931 : Blo 191804 486931 := bstep (se 1 (by rfl) ⟨365198, by rfl⟩ : syracuseStep 486931 = 730397) B730397
theorem B192031 : Blo 191804 192031 := bstep (se 1 (by rfl) ⟨144023, by rfl⟩ : syracuseStep 192031 = 288047) B288047
theorem B192155 : Blo 191804 192155 := bstep (se 1 (by rfl) ⟨144116, by rfl⟩ : syracuseStep 192155 = 288233) B288233
theorem B290471 : Blo 191804 290471 := bstep (se 1 (by rfl) ⟨217853, by rfl⟩ : syracuseStep 290471 = 435707) B435707
theorem B487579 : Blo 191804 487579 := bstep (se 1 (by rfl) ⟨365684, by rfl⟩ : syracuseStep 487579 = 731369) B731369
theorem B651455 : Blo 191804 651455 := bstep (se 1 (by rfl) ⟨488591, by rfl⟩ : syracuseStep 651455 = 977183) B977183
theorem B487721 : Blo 191804 487721 := bstep (se 2 (by rfl) ⟨182895, by rfl⟩ : syracuseStep 487721 = 365791) B365791
theorem B291119 : Blo 191804 291119 := bstep (se 1 (by rfl) ⟨218339, by rfl⟩ : syracuseStep 291119 = 436679) B436679
theorem B192959 : Blo 191804 192959 := bstep (se 1 (by rfl) ⟨144719, by rfl⟩ : syracuseStep 192959 = 289439) B289439
theorem B979613 : Blo 191804 979613 := bstep (se 3 (by rfl) ⟨183677, by rfl⟩ : syracuseStep 979613 = 367355) B367355
theorem B193263 : Blo 191804 193263 := bstep (se 1 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 193263 = 289895) B289895
theorem B324587 : Blo 191804 324587 := bstep (se 1 (by rfl) ⟨243440, by rfl⟩ : syracuseStep 324587 = 486881) B486881
theorem B193567 : Blo 191804 193567 := bstep (se 1 (by rfl) ⟨145175, by rfl⟩ : syracuseStep 193567 = 290351) B290351
theorem B488551 : Blo 191804 488551 := bstep (se 1 (by rfl) ⟨366413, by rfl⟩ : syracuseStep 488551 = 732827) B732827
theorem B291977 : Blo 191804 291977 := bstep (se 2 (by rfl) ⟨109491, by rfl⟩ : syracuseStep 291977 = 218983) B218983
theorem B488713 : Blo 191804 488713 := bstep (se 2 (by rfl) ⟨183267, by rfl⟩ : syracuseStep 488713 = 366535) B366535
theorem B5928227 : Blo 191804 5928227 := bstep (se 1 (by rfl) ⟨4446170, by rfl⟩ : syracuseStep 5928227 = 8892341) B8892341
theorem B193919 : Blo 191804 193919 := bstep (se 1 (by rfl) ⟨145439, by rfl⟩ : syracuseStep 193919 = 290879) B290879
theorem B193983 : Blo 191804 193983 := bstep (se 1 (by rfl) ⟨145487, by rfl⟩ : syracuseStep 193983 = 290975) B290975
theorem B1570259 : Blo 191804 1570259 := bstep (se 1 (by rfl) ⟨1177694, by rfl⟩ : syracuseStep 1570259 = 2355389) B2355389
theorem B292319 : Blo 191804 292319 := bstep (se 1 (by rfl) ⟨219239, by rfl⟩ : syracuseStep 292319 = 438479) B438479
theorem B488987 : Blo 191804 488987 := bstep (se 1 (by rfl) ⟨366740, by rfl⟩ : syracuseStep 488987 = 733481) B733481
theorem B194239 : Blo 191804 194239 := bstep (se 1 (by rfl) ⟨145679, by rfl⟩ : syracuseStep 194239 = 291359) B291359
theorem B194495 : Blo 191804 194495 := bstep (se 1 (by rfl) ⟨145871, by rfl⟩ : syracuseStep 194495 = 291743) B291743
theorem B2488259 : Blo 191804 2488259 := bstep (se 1 (by rfl) ⟨1866194, by rfl⟩ : syracuseStep 2488259 = 3732389) B3732389
theorem B292895 : Blo 191804 292895 := bstep (se 1 (by rfl) ⟨219671, by rfl⟩ : syracuseStep 292895 = 439343) B439343
theorem B194783 : Blo 191804 194783 := bstep (se 1 (by rfl) ⟨146087, by rfl⟩ : syracuseStep 194783 = 292175) B292175
theorem B194815 : Blo 191804 194815 := bstep (se 1 (by rfl) ⟨146111, by rfl⟩ : syracuseStep 194815 = 292223) B292223
theorem B1571237 : Blo 191804 1571237 := bstep (se 4 (by rfl) ⟨147303, by rfl⟩ : syracuseStep 1571237 = 294607) B294607
theorem B1505735 : Blo 191804 1505735 := bstep (se 1 (by rfl) ⟨1129301, by rfl⟩ : syracuseStep 1505735 = 2258603) B2258603
theorem B293375 : Blo 191804 293375 := bstep (se 1 (by rfl) ⟨220031, by rfl⟩ : syracuseStep 293375 = 440063) B440063
theorem B195311 : Blo 191804 195311 := bstep (se 1 (by rfl) ⟨146483, by rfl⟩ : syracuseStep 195311 = 292967) B292967
theorem B1342271 : Blo 191804 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B195695 : Blo 191804 195695 := bstep (se 1 (by rfl) ⟨146771, by rfl⟩ : syracuseStep 195695 = 293543) B293543
theorem B392825 : Blo 191804 392825 := bstep (se 2 (by rfl) ⟨147309, by rfl⟩ : syracuseStep 392825 = 294619) B294619
theorem B983177 : Blo 191804 983177 := bstep (se 2 (by rfl) ⟨368691, by rfl⟩ : syracuseStep 983177 = 737383) B737383
theorem B327847 : Blo 191804 327847 := bstep (se 1 (by rfl) ⟨245885, by rfl⟩ : syracuseStep 327847 = 491771) B491771
theorem B492115 : Blo 191804 492115 := bstep (se 1 (by rfl) ⟨369086, by rfl⟩ : syracuseStep 492115 = 738173) B738173
theorem B983663 : Blo 191804 983663 := bstep (se 1 (by rfl) ⟨737747, by rfl⟩ : syracuseStep 983663 = 1475495) B1475495
theorem B328745 : Blo 191804 328745 := bstep (se 2 (by rfl) ⟨123279, by rfl⟩ : syracuseStep 328745 = 246559) B246559
theorem B1639703 : Blo 191804 1639703 := bstep (se 1 (by rfl) ⟨1229777, by rfl⟩ : syracuseStep 1639703 = 2459555) B2459555
theorem B329575 : Blo 191804 329575 := bstep (se 1 (by rfl) ⟨247181, by rfl⟩ : syracuseStep 329575 = 494363) B494363
theorem B493523 : Blo 191804 493523 := bstep (se 1 (by rfl) ⟨370142, by rfl⟩ : syracuseStep 493523 = 740285) B740285
theorem B461705 : Blo 191804 461705 := bstep (se 2 (by rfl) ⟨173139, by rfl⟩ : syracuseStep 461705 = 346279) B346279
theorem B658745 : Blo 191804 658745 := bstep (se 2 (by rfl) ⟨247029, by rfl⟩ : syracuseStep 658745 = 494059) B494059
theorem B659231 : Blo 191804 659231 := bstep (se 1 (by rfl) ⟨494423, by rfl⟩ : syracuseStep 659231 = 988847) B988847
theorem B1642679 : Blo 191804 1642679 := bstep (se 1 (by rfl) ⟨1232009, by rfl⟩ : syracuseStep 1642679 = 2464019) B2464019
theorem B660311 : Blo 191804 660311 := bstep (se 1 (by rfl) ⟨495233, by rfl⟩ : syracuseStep 660311 = 990467) B990467
theorem B562895 : Blo 191804 562895 := bstep (se 1 (by rfl) ⟨422171, by rfl⟩ : syracuseStep 562895 = 844343) B844343
theorem B431999 : Blo 191804 431999 := bstep (se 1 (by rfl) ⟨323999, by rfl⟩ : syracuseStep 431999 = 647999) B647999
theorem B54073817 : Blo 191804 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B432935 : Blo 191804 432935 := bstep (se 1 (by rfl) ⟨324701, by rfl⟩ : syracuseStep 432935 = 649403) B649403
theorem B433511 : Blo 191804 433511 := bstep (se 1 (by rfl) ⟨325133, by rfl⟩ : syracuseStep 433511 = 650267) B650267
theorem B3579389 : Blo 191804 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B1056311 : Blo 191804 1056311 := bstep (se 1 (by rfl) ⟨792233, by rfl⟩ : syracuseStep 1056311 = 1584467) B1584467
theorem B991115 : Blo 191804 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B18948167 : Blo 191804 18948167 := bstep (se 1 (by rfl) ⟨14211125, by rfl⟩ : syracuseStep 18948167 = 28422251) B28422251
theorem B434303 : Blo 191804 434303 := bstep (se 1 (by rfl) ⟨325727, by rfl⟩ : syracuseStep 434303 = 651455) B651455
theorem B729911 : Blo 191804 729911 := bstep (se 1 (by rfl) ⟨547433, by rfl⟩ : syracuseStep 729911 = 1094867) B1094867
theorem B468155 : Blo 191804 468155 := bstep (se 1 (by rfl) ⟨351116, by rfl⟩ : syracuseStep 468155 = 702233) B702233
theorem B4400335 : Blo 191804 4400335 := bstep (se 1 (by rfl) ⟨3300251, by rfl⟩ : syracuseStep 4400335 = 6600503) B6600503
theorem B438227 : Blo 191804 438227 := bstep (se 1 (by rfl) ⟨328670, by rfl⟩ : syracuseStep 438227 = 657341) B657341
theorem B438623 : Blo 191804 438623 := bstep (se 1 (by rfl) ⟨328967, by rfl⟩ : syracuseStep 438623 = 657935) B657935
theorem B4207241 : Blo 191804 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B668665 : Blo 191804 668665 := bstep (se 2 (by rfl) ⟨250749, by rfl⟩ : syracuseStep 668665 = 501499) B501499
theorem B833179 : Blo 191804 833179 := bstep (se 1 (by rfl) ⟨624884, by rfl⟩ : syracuseStep 833179 = 1249769) B1249769
theorem B276223 : Blo 191804 276223 := bstep (se 1 (by rfl) ⟨207167, by rfl⟩ : syracuseStep 276223 = 414335) B414335
theorem B440351 : Blo 191804 440351 := bstep (se 1 (by rfl) ⟨330263, by rfl⟩ : syracuseStep 440351 = 660527) B660527
theorem B440423 : Blo 191804 440423 := bstep (se 1 (by rfl) ⟨330317, by rfl⟩ : syracuseStep 440423 = 660635) B660635
theorem B276895 : Blo 191804 276895 := bstep (se 1 (by rfl) ⟨207671, by rfl⟩ : syracuseStep 276895 = 415343) B415343
theorem B735911 : Blo 191804 735911 := bstep (se 1 (by rfl) ⟨551933, by rfl⟩ : syracuseStep 735911 = 1103867) B1103867
theorem B1195343 : Blo 191804 1195343 := bstep (se 1 (by rfl) ⟨896507, by rfl⟩ : syracuseStep 1195343 = 1793015) B1793015
theorem B1130087 : Blo 191804 1130087 := bstep (se 1 (by rfl) ⟨847565, by rfl⟩ : syracuseStep 1130087 = 1695131) B1695131
theorem B1393939 : Blo 191804 1393939 := bstep (se 1 (by rfl) ⟨1045454, by rfl⟩ : syracuseStep 1393939 = 2090909) B2090909
theorem B4179563 : Blo 191804 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B8309303 : Blo 191804 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B216391 : Blo 191804 216391 := bstep (se 1 (by rfl) ⟨162293, by rfl⟩ : syracuseStep 216391 = 324587) B324587
theorem B3952151 : Blo 191804 3952151 := bstep (se 1 (by rfl) ⟨2964113, by rfl⟩ : syracuseStep 3952151 = 5928227) B5928227
theorem B1658839 : Blo 191804 1658839 := bstep (se 1 (by rfl) ⟨1244129, by rfl⟩ : syracuseStep 1658839 = 2488259) B2488259
theorem B1003823 : Blo 191804 1003823 := bstep (se 1 (by rfl) ⟨752867, by rfl⟩ : syracuseStep 1003823 = 1505735) B1505735
theorem B547229 : Blo 191804 547229 := bstep (se 3 (by rfl) ⟨102605, by rfl⟩ : syracuseStep 547229 = 205211) B205211
theorem B4121027 : Blo 191804 4121027 := bstep (se 1 (by rfl) ⟨3090770, by rfl⟩ : syracuseStep 4121027 = 6181541) B6181541
theorem B288071 : Blo 191804 288071 := bstep (se 1 (by rfl) ⟨216053, by rfl⟩ : syracuseStep 288071 = 432107) B432107
theorem B288431 : Blo 191804 288431 := bstep (se 1 (by rfl) ⟨216323, by rfl⟩ : syracuseStep 288431 = 432647) B432647
theorem B2221991 : Blo 191804 2221991 := bstep (se 1 (by rfl) ⟨1666493, by rfl⟩ : syracuseStep 2221991 = 3332987) B3332987
theorem B649241 : Blo 191804 649241 := bstep (se 2 (by rfl) ⟨243465, by rfl⟩ : syracuseStep 649241 = 486931) B486931
theorem B288875 : Blo 191804 288875 := bstep (se 1 (by rfl) ⟨216656, by rfl⟩ : syracuseStep 288875 = 433313) B433313
theorem B485615 : Blo 191804 485615 := bstep (se 1 (by rfl) ⟨364211, by rfl⟩ : syracuseStep 485615 = 728423) B728423
theorem B4909679 : Blo 191804 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B7629427 : Blo 191804 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B289583 : Blo 191804 289583 := bstep (se 1 (by rfl) ⟨217187, by rfl⟩ : syracuseStep 289583 = 434375) B434375
theorem B650105 : Blo 191804 650105 := bstep (se 2 (by rfl) ⟨243789, by rfl⟩ : syracuseStep 650105 = 487579) B487579
theorem B290543 : Blo 191804 290543 := bstep (se 1 (by rfl) ⟨217907, by rfl⟩ : syracuseStep 290543 = 435815) B435815
theorem B290759 : Blo 191804 290759 := bstep (se 1 (by rfl) ⟨218069, by rfl⟩ : syracuseStep 290759 = 436139) B436139
theorem B4157419 : Blo 191804 4157419 := bstep (se 1 (by rfl) ⟨3118064, by rfl⟩ : syracuseStep 4157419 = 6236129) B6236129
theorem B290927 : Blo 191804 290927 := bstep (se 1 (by rfl) ⟨218195, by rfl⟩ : syracuseStep 290927 = 436391) B436391
theorem B651401 : Blo 191804 651401 := bstep (se 2 (by rfl) ⟨244275, by rfl⟩ : syracuseStep 651401 = 488551) B488551
theorem B1208603 : Blo 191804 1208603 := bstep (se 1 (by rfl) ⟨906452, by rfl⟩ : syracuseStep 1208603 = 1812905) B1812905
theorem B192831 : Blo 191804 192831 := bstep (se 1 (by rfl) ⟨144623, by rfl⟩ : syracuseStep 192831 = 289247) B289247
theorem B651617 : Blo 191804 651617 := bstep (se 2 (by rfl) ⟨244356, by rfl⟩ : syracuseStep 651617 = 488713) B488713
theorem B8319347 : Blo 191804 8319347 := bstep (se 1 (by rfl) ⟨6239510, by rfl⟩ : syracuseStep 8319347 = 12479021) B12479021
theorem B192927 : Blo 191804 192927 := bstep (se 1 (by rfl) ⟨144695, by rfl⟩ : syracuseStep 192927 = 289391) B289391
theorem B291383 : Blo 191804 291383 := bstep (se 1 (by rfl) ⟨218537, by rfl⟩ : syracuseStep 291383 = 437075) B437075
theorem B193215 : Blo 191804 193215 := bstep (se 1 (by rfl) ⟨144911, by rfl⟩ : syracuseStep 193215 = 289823) B289823
theorem B324391 : Blo 191804 324391 := bstep (se 1 (by rfl) ⟨243293, by rfl⟩ : syracuseStep 324391 = 486587) B486587
theorem B193647 : Blo 191804 193647 := bstep (se 1 (by rfl) ⟨145235, by rfl⟩ : syracuseStep 193647 = 290471) B290471
theorem B292331 : Blo 191804 292331 := bstep (se 1 (by rfl) ⟨219248, by rfl⟩ : syracuseStep 292331 = 438497) B438497
theorem B325147 : Blo 191804 325147 := bstep (se 1 (by rfl) ⟨243860, by rfl⟩ : syracuseStep 325147 = 487721) B487721
theorem B194079 : Blo 191804 194079 := bstep (se 1 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 194079 = 291119) B291119
theorem B259753 : Blo 191804 259753 := bstep (se 2 (by rfl) ⟨97407, by rfl⟩ : syracuseStep 259753 = 194815) B194815
theorem B325289 : Blo 191804 325289 := bstep (se 2 (by rfl) ⟨121983, by rfl⟩ : syracuseStep 325289 = 243967) B243967
theorem B489179 : Blo 191804 489179 := bstep (se 1 (by rfl) ⟨366884, by rfl⟩ : syracuseStep 489179 = 733769) B733769
theorem B653075 : Blo 191804 653075 := bstep (se 1 (by rfl) ⟨489806, by rfl⟩ : syracuseStep 653075 = 979613) B979613
theorem B292841 : Blo 191804 292841 := bstep (se 2 (by rfl) ⟨109815, by rfl⟩ : syracuseStep 292841 = 219631) B219631
theorem B194651 : Blo 191804 194651 := bstep (se 1 (by rfl) ⟨145988, by rfl⟩ : syracuseStep 194651 = 291977) B291977
theorem B293147 : Blo 191804 293147 := bstep (se 1 (by rfl) ⟨219860, by rfl⟩ : syracuseStep 293147 = 439721) B439721
theorem B1046839 : Blo 191804 1046839 := bstep (se 1 (by rfl) ⟨785129, by rfl⟩ : syracuseStep 1046839 = 1570259) B1570259
theorem B194879 : Blo 191804 194879 := bstep (se 1 (by rfl) ⟨146159, by rfl⟩ : syracuseStep 194879 = 292319) B292319
theorem B325991 : Blo 191804 325991 := bstep (se 1 (by rfl) ⟨244493, by rfl⟩ : syracuseStep 325991 = 488987) B488987
theorem B489959 : Blo 191804 489959 := bstep (se 1 (by rfl) ⟨367469, by rfl⟩ : syracuseStep 489959 = 734939) B734939
theorem B293531 : Blo 191804 293531 := bstep (se 1 (by rfl) ⟨220148, by rfl⟩ : syracuseStep 293531 = 440297) B440297
theorem B195263 : Blo 191804 195263 := bstep (se 1 (by rfl) ⟨146447, by rfl⟩ : syracuseStep 195263 = 292895) B292895
theorem B1047491 : Blo 191804 1047491 := bstep (se 1 (by rfl) ⟨785618, by rfl⟩ : syracuseStep 1047491 = 1571237) B1571237
theorem B195583 : Blo 191804 195583 := bstep (se 1 (by rfl) ⟨146687, by rfl⟩ : syracuseStep 195583 = 293375) B293375
theorem B261883 : Blo 191804 261883 := bstep (se 1 (by rfl) ⟨196412, by rfl⟩ : syracuseStep 261883 = 392825) B392825
theorem B655451 : Blo 191804 655451 := bstep (se 1 (by rfl) ⟨491588, by rfl⟩ : syracuseStep 655451 = 983177) B983177
theorem B655775 : Blo 191804 655775 := bstep (se 1 (by rfl) ⟨491831, by rfl⟩ : syracuseStep 655775 = 983663) B983663
theorem B656153 : Blo 191804 656153 := bstep (se 2 (by rfl) ⟨246057, by rfl⟩ : syracuseStep 656153 = 492115) B492115
theorem B2786375 : Blo 191804 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B329015 : Blo 191804 329015 := bstep (se 1 (by rfl) ⟨246761, by rfl⟩ : syracuseStep 329015 = 493523) B493523
theorem B5867113 : Blo 191804 5867113 := bstep (se 2 (by rfl) ⟨2200167, by rfl⟩ : syracuseStep 5867113 = 4400335) B4400335
theorem B5539535 : Blo 191804 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B364819 : Blo 191804 364819 := bstep (se 1 (by rfl) ⟨273614, by rfl⟩ : syracuseStep 364819 = 547229) B547229
theorem B36049211 : Blo 191804 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B660743 : Blo 191804 660743 := bstep (se 1 (by rfl) ⟨495557, by rfl⟩ : syracuseStep 660743 = 991115) B991115
theorem B5543225 : Blo 191804 5543225 := bstep (se 2 (by rfl) ⟨2078709, by rfl⟩ : syracuseStep 5543225 = 4157419) B4157419
theorem B432521 : Blo 191804 432521 := bstep (se 2 (by rfl) ⟨162195, by rfl⟩ : syracuseStep 432521 = 324391) B324391
theorem B1481327 : Blo 191804 1481327 := bstep (se 1 (by rfl) ⟨1110995, by rfl⟩ : syracuseStep 1481327 = 2221991) B2221991
theorem B432827 : Blo 191804 432827 := bstep (se 1 (by rfl) ⟨324620, by rfl⟩ : syracuseStep 432827 = 649241) B649241
theorem B433403 : Blo 191804 433403 := bstep (se 1 (by rfl) ⟨325052, by rfl⟩ : syracuseStep 433403 = 650105) B650105
theorem B433529 : Blo 191804 433529 := bstep (se 2 (by rfl) ⟨162573, by rfl⟩ : syracuseStep 433529 = 325147) B325147
theorem B368297 : Blo 191804 368297 := bstep (se 2 (by rfl) ⟨138111, by rfl⟩ : syracuseStep 368297 = 276223) B276223
theorem B434267 : Blo 191804 434267 := bstep (se 1 (by rfl) ⟨325700, by rfl⟩ : syracuseStep 434267 = 651401) B651401
theorem B434411 : Blo 191804 434411 := bstep (se 1 (by rfl) ⟨325808, by rfl⟩ : syracuseStep 434411 = 651617) B651617
theorem B5546231 : Blo 191804 5546231 := bstep (se 1 (by rfl) ⟨4159673, by rfl⟩ : syracuseStep 5546231 = 8319347) B8319347
theorem B369193 : Blo 191804 369193 := bstep (se 2 (by rfl) ⟨138447, by rfl⟩ : syracuseStep 369193 = 276895) B276895
theorem B435383 : Blo 191804 435383 := bstep (se 1 (by rfl) ⟨326537, by rfl⟩ : syracuseStep 435383 = 653075) B653075
theorem B698327 : Blo 191804 698327 := bstep (se 1 (by rfl) ⟨523745, by rfl⟩ : syracuseStep 698327 = 1047491) B1047491
theorem B796895 : Blo 191804 796895 := bstep (se 1 (by rfl) ⟨597671, by rfl⟩ : syracuseStep 796895 = 1195343) B1195343
theorem B437129 : Blo 191804 437129 := bstep (se 2 (by rfl) ⟨163923, by rfl⟩ : syracuseStep 437129 = 327847) B327847
theorem B1093135 : Blo 191804 1093135 := bstep (se 1 (by rfl) ⟨819851, by rfl⟩ : syracuseStep 1093135 = 1639703) B1639703
theorem B11219309 : Blo 191804 11219309 := bstep (se 3 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 11219309 = 4207241) B4207241
theorem B439163 : Blo 191804 439163 := bstep (se 1 (by rfl) ⟨329372, by rfl⟩ : syracuseStep 439163 = 658745) B658745
theorem B2634767 : Blo 191804 2634767 := bstep (se 1 (by rfl) ⟨1976075, by rfl⟩ : syracuseStep 2634767 = 3952151) B3952151
theorem B439433 : Blo 191804 439433 := bstep (se 2 (by rfl) ⟨164787, by rfl⟩ : syracuseStep 439433 = 329575) B329575
theorem B439487 : Blo 191804 439487 := bstep (se 1 (by rfl) ⟨329615, by rfl⟩ : syracuseStep 439487 = 659231) B659231
theorem B1095119 : Blo 191804 1095119 := bstep (se 1 (by rfl) ⟨821339, by rfl⟩ : syracuseStep 1095119 = 1642679) B1642679
theorem B669215 : Blo 191804 669215 := bstep (se 1 (by rfl) ⟨501911, by rfl⟩ : syracuseStep 669215 = 1003823) B1003823
theorem B440207 : Blo 191804 440207 := bstep (se 1 (by rfl) ⟨330155, by rfl⟩ : syracuseStep 440207 = 660311) B660311
theorem B10172569 : Blo 191804 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B375263 : Blo 191804 375263 := bstep (se 1 (by rfl) ⟨281447, by rfl⟩ : syracuseStep 375263 = 562895) B562895
theorem B704207 : Blo 191804 704207 := bstep (se 1 (by rfl) ⟨528155, by rfl⟩ : syracuseStep 704207 = 1056311) B1056311
theorem B2211785 : Blo 191804 2211785 := bstep (se 2 (by rfl) ⟨829419, by rfl⟩ : syracuseStep 2211785 = 1658839) B1658839
theorem B12632111 : Blo 191804 12632111 := bstep (se 1 (by rfl) ⟨9474083, by rfl⟩ : syracuseStep 12632111 = 18948167) B18948167
theorem B312103 : Blo 191804 312103 := bstep (se 1 (by rfl) ⟨234077, by rfl⟩ : syracuseStep 312103 = 468155) B468155
theorem B346337 : Blo 191804 346337 := bstep (se 2 (by rfl) ⟨129876, by rfl⟩ : syracuseStep 346337 = 259753) B259753
theorem B1231213 : Blo 191804 1231213 := bstep (se 3 (by rfl) ⟨230852, by rfl⟩ : syracuseStep 1231213 = 461705) B461705
theorem B805735 : Blo 191804 805735 := bstep (se 1 (by rfl) ⟨604301, by rfl⟩ : syracuseStep 805735 = 1208603) B1208603
theorem B1395785 : Blo 191804 1395785 := bstep (se 2 (by rfl) ⟨523419, by rfl⟩ : syracuseStep 1395785 = 1046839) B1046839
theorem B216859 : Blo 191804 216859 := bstep (se 1 (by rfl) ⟨162644, by rfl⟩ : syracuseStep 216859 = 325289) B325289
theorem B1396709 : Blo 191804 1396709 := bstep (se 4 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 1396709 = 261883) B261883
theorem B217327 : Blo 191804 217327 := bstep (se 1 (by rfl) ⟨162995, by rfl⟩ : syracuseStep 217327 = 325991) B325991
theorem B219163 : Blo 191804 219163 := bstep (se 1 (by rfl) ⟨164372, by rfl⟩ : syracuseStep 219163 = 328745) B328745
theorem B1858585 : Blo 191804 1858585 := bstep (se 2 (by rfl) ⟨696969, by rfl⟩ : syracuseStep 1858585 = 1393939) B1393939
theorem B287999 : Blo 191804 287999 := bstep (se 1 (by rfl) ⟨215999, by rfl⟩ : syracuseStep 287999 = 431999) B431999
theorem B288521 : Blo 191804 288521 := bstep (se 2 (by rfl) ⟨108195, by rfl⟩ : syracuseStep 288521 = 216391) B216391
theorem B288623 : Blo 191804 288623 := bstep (se 1 (by rfl) ⟨216467, by rfl⟩ : syracuseStep 288623 = 432935) B432935
theorem B289007 : Blo 191804 289007 := bstep (se 1 (by rfl) ⟨216755, by rfl⟩ : syracuseStep 289007 = 433511) B433511
theorem B2386259 : Blo 191804 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B3566213 : Blo 191804 3566213 := bstep (se 4 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 3566213 = 668665) B668665
theorem B289535 : Blo 191804 289535 := bstep (se 1 (by rfl) ⟨217151, by rfl⟩ : syracuseStep 289535 = 434303) B434303
theorem B2747351 : Blo 191804 2747351 := bstep (se 1 (by rfl) ⟨2060513, by rfl⟩ : syracuseStep 2747351 = 4121027) B4121027
theorem B486607 : Blo 191804 486607 := bstep (se 1 (by rfl) ⟨364955, by rfl⟩ : syracuseStep 486607 = 729911) B729911
theorem B192047 : Blo 191804 192047 := bstep (se 1 (by rfl) ⟨144035, by rfl⟩ : syracuseStep 192047 = 288071) B288071
theorem B192287 : Blo 191804 192287 := bstep (se 1 (by rfl) ⟨144215, by rfl⟩ : syracuseStep 192287 = 288431) B288431
theorem B192583 : Blo 191804 192583 := bstep (se 1 (by rfl) ⟨144437, by rfl⟩ : syracuseStep 192583 = 288875) B288875
theorem B323743 : Blo 191804 323743 := bstep (se 1 (by rfl) ⟨242807, by rfl⟩ : syracuseStep 323743 = 485615) B485615
theorem B3273119 : Blo 191804 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B193055 : Blo 191804 193055 := bstep (se 1 (by rfl) ⟨144791, by rfl⟩ : syracuseStep 193055 = 289583) B289583
theorem B1110905 : Blo 191804 1110905 := bstep (se 2 (by rfl) ⟨416589, by rfl⟩ : syracuseStep 1110905 = 833179) B833179
theorem B193695 : Blo 191804 193695 := bstep (se 1 (by rfl) ⟨145271, by rfl⟩ : syracuseStep 193695 = 290543) B290543
theorem B193839 : Blo 191804 193839 := bstep (se 1 (by rfl) ⟨145379, by rfl⟩ : syracuseStep 193839 = 290759) B290759
theorem B292151 : Blo 191804 292151 := bstep (se 1 (by rfl) ⟨219113, by rfl⟩ : syracuseStep 292151 = 438227) B438227
theorem B193951 : Blo 191804 193951 := bstep (se 1 (by rfl) ⟨145463, by rfl⟩ : syracuseStep 193951 = 290927) B290927
theorem B292415 : Blo 191804 292415 := bstep (se 1 (by rfl) ⟨219311, by rfl⟩ : syracuseStep 292415 = 438623) B438623
theorem B194255 : Blo 191804 194255 := bstep (se 1 (by rfl) ⟨145691, by rfl⟩ : syracuseStep 194255 = 291383) B291383
theorem B194887 : Blo 191804 194887 := bstep (se 1 (by rfl) ⟨146165, by rfl⟩ : syracuseStep 194887 = 292331) B292331
theorem B326119 : Blo 191804 326119 := bstep (se 1 (by rfl) ⟨244589, by rfl⟩ : syracuseStep 326119 = 489179) B489179
theorem B195227 : Blo 191804 195227 := bstep (se 1 (by rfl) ⟨146420, by rfl⟩ : syracuseStep 195227 = 292841) B292841
theorem B293567 : Blo 191804 293567 := bstep (se 1 (by rfl) ⟨220175, by rfl⟩ : syracuseStep 293567 = 440351) B440351
theorem B293615 : Blo 191804 293615 := bstep (se 1 (by rfl) ⟨220211, by rfl⟩ : syracuseStep 293615 = 440423) B440423
theorem B195431 : Blo 191804 195431 := bstep (se 1 (by rfl) ⟨146573, by rfl⟩ : syracuseStep 195431 = 293147) B293147
theorem B326639 : Blo 191804 326639 := bstep (se 1 (by rfl) ⟨244979, by rfl⟩ : syracuseStep 326639 = 489959) B489959
theorem B195687 : Blo 191804 195687 := bstep (se 1 (by rfl) ⟨146765, by rfl⟩ : syracuseStep 195687 = 293531) B293531
theorem B490607 : Blo 191804 490607 := bstep (se 1 (by rfl) ⟨367955, by rfl⟩ : syracuseStep 490607 = 735911) B735911
theorem B753391 : Blo 191804 753391 := bstep (se 1 (by rfl) ⟨565043, by rfl⟩ : syracuseStep 753391 = 1130087) B1130087
theorem B8421407 : Blo 191804 8421407 := bstep (se 1 (by rfl) ⟨6316055, by rfl⟩ : syracuseStep 8421407 = 12632111) B12632111
theorem B492257 : Blo 191804 492257 := bstep (se 2 (by rfl) ⟨184596, by rfl⟩ : syracuseStep 492257 = 369193) B369193
theorem B230891 : Blo 191804 230891 := bstep (se 1 (by rfl) ⟨173168, by rfl⟩ : syracuseStep 230891 = 346337) B346337
theorem B1641617 : Blo 191804 1641617 := bstep (se 2 (by rfl) ⟨615606, by rfl⟩ : syracuseStep 1641617 = 1231213) B1231213
theorem B987551 : Blo 191804 987551 := bstep (se 1 (by rfl) ⟨740663, by rfl⟩ : syracuseStep 987551 = 1481327) B1481327
theorem B431657 : Blo 191804 431657 := bstep (se 2 (by rfl) ⟨161871, by rfl⟩ : syracuseStep 431657 = 323743) B323743
theorem B465551 : Blo 191804 465551 := bstep (se 1 (by rfl) ⟨349163, by rfl⟩ : syracuseStep 465551 = 698327) B698327
theorem B531263 : Blo 191804 531263 := bstep (se 1 (by rfl) ⟨398447, by rfl⟩ : syracuseStep 531263 = 796895) B796895
theorem B7479539 : Blo 191804 7479539 := bstep (se 1 (by rfl) ⟨5609654, by rfl⟩ : syracuseStep 7479539 = 11219309) B11219309
theorem B434825 : Blo 191804 434825 := bstep (se 2 (by rfl) ⟨163059, by rfl⟩ : syracuseStep 434825 = 326119) B326119
theorem B730079 : Blo 191804 730079 := bstep (se 1 (by rfl) ⟨547559, by rfl⟩ : syracuseStep 730079 = 1095119) B1095119
theorem B469471 : Blo 191804 469471 := bstep (se 1 (by rfl) ⟨352103, by rfl⟩ : syracuseStep 469471 = 704207) B704207
theorem B436967 : Blo 191804 436967 := bstep (se 1 (by rfl) ⟨327725, by rfl⟩ : syracuseStep 436967 = 655451) B655451
theorem B437183 : Blo 191804 437183 := bstep (se 1 (by rfl) ⟨327887, by rfl⟩ : syracuseStep 437183 = 655775) B655775
theorem B437435 : Blo 191804 437435 := bstep (se 1 (by rfl) ⟨328076, by rfl⟩ : syracuseStep 437435 = 656153) B656153
theorem B930523 : Blo 191804 930523 := bstep (se 1 (by rfl) ⟨697892, by rfl⟩ : syracuseStep 930523 = 1395785) B1395785
theorem B931139 : Blo 191804 931139 := bstep (se 1 (by rfl) ⟨698354, by rfl⟩ : syracuseStep 931139 = 1396709) B1396709
theorem B24032807 : Blo 191804 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B440495 : Blo 191804 440495 := bstep (se 1 (by rfl) ⟨330371, by rfl⟩ : syracuseStep 440495 = 660743) B660743
theorem B1457513 : Blo 191804 1457513 := bstep (se 2 (by rfl) ⟨546567, by rfl⟩ : syracuseStep 1457513 = 1093135) B1093135
theorem B245531 : Blo 191804 245531 := bstep (se 1 (by rfl) ⟨184148, by rfl⟩ : syracuseStep 245531 = 368297) B368297
theorem B1590839 : Blo 191804 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B2377475 : Blo 191804 2377475 := bstep (se 1 (by rfl) ⟨1783106, by rfl⟩ : syracuseStep 2377475 = 3566213) B3566213
theorem B2182079 : Blo 191804 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B740603 : Blo 191804 740603 := bstep (se 1 (by rfl) ⟨555452, by rfl⟩ : syracuseStep 740603 = 1110905) B1110905
theorem B1756511 : Blo 191804 1756511 := bstep (se 1 (by rfl) ⟨1317383, by rfl⟩ : syracuseStep 1756511 = 2634767) B2634767
theorem B446143 : Blo 191804 446143 := bstep (se 1 (by rfl) ⟨334607, by rfl⟩ : syracuseStep 446143 = 669215) B669215
theorem B2478113 : Blo 191804 2478113 := bstep (se 2 (by rfl) ⟨929292, by rfl⟩ : syracuseStep 2478113 = 1858585) B1858585
theorem B250175 : Blo 191804 250175 := bstep (se 1 (by rfl) ⟨187631, by rfl⟩ : syracuseStep 250175 = 375263) B375263
theorem B217759 : Blo 191804 217759 := bstep (se 1 (by rfl) ⟨163319, by rfl⟩ : syracuseStep 217759 = 326639) B326639
theorem B1004521 : Blo 191804 1004521 := bstep (se 2 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 1004521 = 753391) B753391
theorem B1857583 : Blo 191804 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B219343 : Blo 191804 219343 := bstep (se 1 (by rfl) ⟨164507, by rfl⟩ : syracuseStep 219343 = 329015) B329015
theorem B3693023 : Blo 191804 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B7822817 : Blo 191804 7822817 := bstep (se 2 (by rfl) ⟨2933556, by rfl⟩ : syracuseStep 7822817 = 5867113) B5867113
theorem B3695483 : Blo 191804 3695483 := bstep (se 1 (by rfl) ⟨2771612, by rfl⟩ : syracuseStep 3695483 = 5543225) B5543225
theorem B1074313 : Blo 191804 1074313 := bstep (se 2 (by rfl) ⟨402867, by rfl⟩ : syracuseStep 1074313 = 805735) B805735
theorem B1664549 : Blo 191804 1664549 := bstep (se 4 (by rfl) ⟨156051, by rfl⟩ : syracuseStep 1664549 = 312103) B312103
theorem B288347 : Blo 191804 288347 := bstep (se 1 (by rfl) ⟨216260, by rfl⟩ : syracuseStep 288347 = 432521) B432521
theorem B648809 : Blo 191804 648809 := bstep (se 2 (by rfl) ⟨243303, by rfl⟩ : syracuseStep 648809 = 486607) B486607
theorem B288551 : Blo 191804 288551 := bstep (se 1 (by rfl) ⟨216413, by rfl⟩ : syracuseStep 288551 = 432827) B432827
theorem B288935 : Blo 191804 288935 := bstep (se 1 (by rfl) ⟨216701, by rfl⟩ : syracuseStep 288935 = 433403) B433403
theorem B289019 : Blo 191804 289019 := bstep (se 1 (by rfl) ⟨216764, by rfl⟩ : syracuseStep 289019 = 433529) B433529
theorem B289145 : Blo 191804 289145 := bstep (se 2 (by rfl) ⟨108429, by rfl⟩ : syracuseStep 289145 = 216859) B216859
theorem B289511 : Blo 191804 289511 := bstep (se 1 (by rfl) ⟨217133, by rfl⟩ : syracuseStep 289511 = 434267) B434267
theorem B289607 : Blo 191804 289607 := bstep (se 1 (by rfl) ⟨217205, by rfl⟩ : syracuseStep 289607 = 434411) B434411
theorem B3697487 : Blo 191804 3697487 := bstep (se 1 (by rfl) ⟨2773115, by rfl⟩ : syracuseStep 3697487 = 5546231) B5546231
theorem B289769 : Blo 191804 289769 := bstep (se 2 (by rfl) ⟨108663, by rfl⟩ : syracuseStep 289769 = 217327) B217327
theorem B486425 : Blo 191804 486425 := bstep (se 2 (by rfl) ⟨182409, by rfl⟩ : syracuseStep 486425 = 364819) B364819
theorem B290255 : Blo 191804 290255 := bstep (se 1 (by rfl) ⟨217691, by rfl⟩ : syracuseStep 290255 = 435383) B435383
theorem B191999 : Blo 191804 191999 := bstep (se 1 (by rfl) ⟨143999, by rfl⟩ : syracuseStep 191999 = 287999) B287999
theorem B192347 : Blo 191804 192347 := bstep (se 1 (by rfl) ⟨144260, by rfl⟩ : syracuseStep 192347 = 288521) B288521
theorem B192415 : Blo 191804 192415 := bstep (se 1 (by rfl) ⟨144311, by rfl⟩ : syracuseStep 192415 = 288623) B288623
theorem B192671 : Blo 191804 192671 := bstep (se 1 (by rfl) ⟨144503, by rfl⟩ : syracuseStep 192671 = 289007) B289007
theorem B193023 : Blo 191804 193023 := bstep (se 1 (by rfl) ⟨144767, by rfl⟩ : syracuseStep 193023 = 289535) B289535
theorem B291419 : Blo 191804 291419 := bstep (se 1 (by rfl) ⟨218564, by rfl⟩ : syracuseStep 291419 = 437129) B437129
theorem B1831567 : Blo 191804 1831567 := bstep (se 1 (by rfl) ⟨1373675, by rfl⟩ : syracuseStep 1831567 = 2747351) B2747351
theorem B292217 : Blo 191804 292217 := bstep (se 2 (by rfl) ⟨109581, by rfl⟩ : syracuseStep 292217 = 219163) B219163
theorem B13563425 : Blo 191804 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B292775 : Blo 191804 292775 := bstep (se 1 (by rfl) ⟨219581, by rfl⟩ : syracuseStep 292775 = 439163) B439163
theorem B292955 : Blo 191804 292955 := bstep (se 1 (by rfl) ⟨219716, by rfl⟩ : syracuseStep 292955 = 439433) B439433
theorem B292991 : Blo 191804 292991 := bstep (se 1 (by rfl) ⟨219743, by rfl⟩ : syracuseStep 292991 = 439487) B439487
theorem B194767 : Blo 191804 194767 := bstep (se 1 (by rfl) ⟨146075, by rfl⟩ : syracuseStep 194767 = 292151) B292151
theorem B194943 : Blo 191804 194943 := bstep (se 1 (by rfl) ⟨146207, by rfl⟩ : syracuseStep 194943 = 292415) B292415
theorem B293471 : Blo 191804 293471 := bstep (se 1 (by rfl) ⟨220103, by rfl⟩ : syracuseStep 293471 = 440207) B440207
theorem B195711 : Blo 191804 195711 := bstep (se 1 (by rfl) ⟨146783, by rfl⟩ : syracuseStep 195711 = 293567) B293567
theorem B195743 : Blo 191804 195743 := bstep (se 1 (by rfl) ⟨146807, by rfl⟩ : syracuseStep 195743 = 293615) B293615
theorem B327071 : Blo 191804 327071 := bstep (se 1 (by rfl) ⟨245303, by rfl⟩ : syracuseStep 327071 = 490607) B490607
theorem B1474523 : Blo 191804 1474523 := bstep (se 1 (by rfl) ⟨1105892, by rfl⟩ : syracuseStep 1474523 = 2211785) B2211785
theorem B328171 : Blo 191804 328171 := bstep (se 1 (by rfl) ⟨246128, by rfl⟩ : syracuseStep 328171 = 492257) B492257
theorem B493735 : Blo 191804 493735 := bstep (se 1 (by rfl) ⟨370301, by rfl⟩ : syracuseStep 493735 = 740603) B740603
theorem B658367 : Blo 191804 658367 := bstep (se 1 (by rfl) ⟨493775, by rfl⟩ : syracuseStep 658367 = 987551) B987551
theorem B625961 : Blo 191804 625961 := bstep (se 2 (by rfl) ⟨234735, by rfl⟩ : syracuseStep 625961 = 469471) B469471
theorem B2462015 : Blo 191804 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B594857 : Blo 191804 594857 := bstep (se 2 (by rfl) ⟨223071, by rfl⟩ : syracuseStep 594857 = 446143) B446143
theorem B5215211 : Blo 191804 5215211 := bstep (se 1 (by rfl) ⟨3911408, by rfl⟩ : syracuseStep 5215211 = 7822817) B7822817
theorem B4986359 : Blo 191804 4986359 := bstep (se 1 (by rfl) ⟨3739769, by rfl⟩ : syracuseStep 4986359 = 7479539) B7479539
theorem B2463655 : Blo 191804 2463655 := bstep (se 1 (by rfl) ⟨1847741, by rfl⟩ : syracuseStep 2463655 = 3695483) B3695483
theorem B432539 : Blo 191804 432539 := bstep (se 1 (by rfl) ⟨324404, by rfl⟩ : syracuseStep 432539 = 648809) B648809
theorem B2464991 : Blo 191804 2464991 := bstep (se 1 (by rfl) ⟨1848743, by rfl⟩ : syracuseStep 2464991 = 3697487) B3697487
theorem B1416701 : Blo 191804 1416701 := bstep (se 3 (by rfl) ⟨265631, by rfl⟩ : syracuseStep 1416701 = 531263) B531263
theorem B5614271 : Blo 191804 5614271 := bstep (se 1 (by rfl) ⟨4210703, by rfl⟩ : syracuseStep 5614271 = 8421407) B8421407
theorem B667133 : Blo 191804 667133 := bstep (se 3 (by rfl) ⟨125087, by rfl⟩ : syracuseStep 667133 = 250175) B250175
theorem B1060559 : Blo 191804 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B1584983 : Blo 191804 1584983 := bstep (se 1 (by rfl) ⟨1188737, by rfl⟩ : syracuseStep 1584983 = 2377475) B2377475
theorem B1094411 : Blo 191804 1094411 := bstep (se 1 (by rfl) ⟨820808, by rfl⟩ : syracuseStep 1094411 = 1641617) B1641617
theorem B1652075 : Blo 191804 1652075 := bstep (se 1 (by rfl) ⟨1239056, by rfl⟩ : syracuseStep 1652075 = 2478113) B2478113
theorem B310367 : Blo 191804 310367 := bstep (se 1 (by rfl) ⟨232775, by rfl⟩ : syracuseStep 310367 = 465551) B465551
theorem B2442089 : Blo 191804 2442089 := bstep (se 2 (by rfl) ⟨915783, by rfl⟩ : syracuseStep 2442089 = 1831567) B1831567
theorem B5818877 : Blo 191804 5818877 := bstep (se 3 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 5818877 = 2182079) B2182079
theorem B2476777 : Blo 191804 2476777 := bstep (se 2 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 2476777 = 1857583) B1857583
theorem B971675 : Blo 191804 971675 := bstep (se 1 (by rfl) ⟨728756, by rfl⟩ : syracuseStep 971675 = 1457513) B1457513
theorem B218047 : Blo 191804 218047 := bstep (se 1 (by rfl) ⟨163535, by rfl⟩ : syracuseStep 218047 = 327071) B327071
theorem B1432417 : Blo 191804 1432417 := bstep (se 2 (by rfl) ⟨537156, by rfl⟩ : syracuseStep 1432417 = 1074313) B1074313
theorem B1171007 : Blo 191804 1171007 := bstep (se 1 (by rfl) ⟨878255, by rfl⟩ : syracuseStep 1171007 = 1756511) B1756511
theorem B287771 : Blo 191804 287771 := bstep (se 1 (by rfl) ⟨215828, by rfl⟩ : syracuseStep 287771 = 431657) B431657
theorem B615709 : Blo 191804 615709 := bstep (se 3 (by rfl) ⟨115445, by rfl⟩ : syracuseStep 615709 = 230891) B230891
theorem B289883 : Blo 191804 289883 := bstep (se 1 (by rfl) ⟨217412, by rfl⟩ : syracuseStep 289883 = 434825) B434825
theorem B486719 : Blo 191804 486719 := bstep (se 1 (by rfl) ⟨365039, by rfl⟩ : syracuseStep 486719 = 730079) B730079
theorem B290345 : Blo 191804 290345 := bstep (se 2 (by rfl) ⟨108879, by rfl⟩ : syracuseStep 290345 = 217759) B217759
theorem B1240697 : Blo 191804 1240697 := bstep (se 2 (by rfl) ⟨465261, by rfl⟩ : syracuseStep 1240697 = 930523) B930523
theorem B1109699 : Blo 191804 1109699 := bstep (se 1 (by rfl) ⟨832274, by rfl⟩ : syracuseStep 1109699 = 1664549) B1664549
theorem B192231 : Blo 191804 192231 := bstep (se 1 (by rfl) ⟨144173, by rfl⟩ : syracuseStep 192231 = 288347) B288347
theorem B192367 : Blo 191804 192367 := bstep (se 1 (by rfl) ⟨144275, by rfl⟩ : syracuseStep 192367 = 288551) B288551
theorem B1339361 : Blo 191804 1339361 := bstep (se 2 (by rfl) ⟨502260, by rfl⟩ : syracuseStep 1339361 = 1004521) B1004521
theorem B192623 : Blo 191804 192623 := bstep (se 1 (by rfl) ⟨144467, by rfl⟩ : syracuseStep 192623 = 288935) B288935
theorem B192679 : Blo 191804 192679 := bstep (se 1 (by rfl) ⟨144509, by rfl⟩ : syracuseStep 192679 = 289019) B289019
theorem B192763 : Blo 191804 192763 := bstep (se 1 (by rfl) ⟨144572, by rfl⟩ : syracuseStep 192763 = 289145) B289145
theorem B193007 : Blo 191804 193007 := bstep (se 1 (by rfl) ⟨144755, by rfl⟩ : syracuseStep 193007 = 289511) B289511
theorem B291311 : Blo 191804 291311 := bstep (se 1 (by rfl) ⟨218483, by rfl⟩ : syracuseStep 291311 = 436967) B436967
theorem B193071 : Blo 191804 193071 := bstep (se 1 (by rfl) ⟨144803, by rfl⟩ : syracuseStep 193071 = 289607) B289607
theorem B291455 : Blo 191804 291455 := bstep (se 1 (by rfl) ⟨218591, by rfl⟩ : syracuseStep 291455 = 437183) B437183
theorem B193179 : Blo 191804 193179 := bstep (se 1 (by rfl) ⟨144884, by rfl⟩ : syracuseStep 193179 = 289769) B289769
theorem B324283 : Blo 191804 324283 := bstep (se 1 (by rfl) ⟨243212, by rfl⟩ : syracuseStep 324283 = 486425) B486425
theorem B291623 : Blo 191804 291623 := bstep (se 1 (by rfl) ⟨218717, by rfl⟩ : syracuseStep 291623 = 437435) B437435
theorem B193503 : Blo 191804 193503 := bstep (se 1 (by rfl) ⟨145127, by rfl⟩ : syracuseStep 193503 = 290255) B290255
theorem B292457 : Blo 191804 292457 := bstep (se 2 (by rfl) ⟨109671, by rfl⟩ : syracuseStep 292457 = 219343) B219343
theorem B194279 : Blo 191804 194279 := bstep (se 1 (by rfl) ⟨145709, by rfl⟩ : syracuseStep 194279 = 291419) B291419
theorem B620759 : Blo 191804 620759 := bstep (se 1 (by rfl) ⟨465569, by rfl⟩ : syracuseStep 620759 = 931139) B931139
theorem B194811 : Blo 191804 194811 := bstep (se 1 (by rfl) ⟨146108, by rfl⟩ : syracuseStep 194811 = 292217) B292217
theorem B9042283 : Blo 191804 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B16021871 : Blo 191804 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B195183 : Blo 191804 195183 := bstep (se 1 (by rfl) ⟨146387, by rfl⟩ : syracuseStep 195183 = 292775) B292775
theorem B195303 : Blo 191804 195303 := bstep (se 1 (by rfl) ⟨146477, by rfl⟩ : syracuseStep 195303 = 292955) B292955
theorem B195327 : Blo 191804 195327 := bstep (se 1 (by rfl) ⟨146495, by rfl⟩ : syracuseStep 195327 = 292991) B292991
theorem B293663 : Blo 191804 293663 := bstep (se 1 (by rfl) ⟨220247, by rfl⟩ : syracuseStep 293663 = 440495) B440495
theorem B195647 : Blo 191804 195647 := bstep (se 1 (by rfl) ⟨146735, by rfl⟩ : syracuseStep 195647 = 293471) B293471
theorem B654749 : Blo 191804 654749 := bstep (se 3 (by rfl) ⟨122765, by rfl⟩ : syracuseStep 654749 = 245531) B245531
theorem B983015 : Blo 191804 983015 := bstep (se 1 (by rfl) ⟨737261, by rfl⟩ : syracuseStep 983015 = 1474523) B1474523
theorem B820945 : Blo 191804 820945 := bstep (se 2 (by rfl) ⟨307854, by rfl⟩ : syracuseStep 820945 = 615709) B615709
theorem B1641343 : Blo 191804 1641343 := bstep (se 1 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 1641343 = 2462015) B2462015
theorem B658313 : Blo 191804 658313 := bstep (se 2 (by rfl) ⟨246867, by rfl⟩ : syracuseStep 658313 = 493735) B493735
theorem B396571 : Blo 191804 396571 := bstep (se 1 (by rfl) ⟨297428, by rfl⟩ : syracuseStep 396571 = 594857) B594857
theorem B3476807 : Blo 191804 3476807 := bstep (se 1 (by rfl) ⟨2607605, by rfl⟩ : syracuseStep 3476807 = 5215211) B5215211
theorem B1643327 : Blo 191804 1643327 := bstep (se 1 (by rfl) ⟨1232495, by rfl⟩ : syracuseStep 1643327 = 2464991) B2464991
theorem B432377 : Blo 191804 432377 := bstep (se 2 (by rfl) ⟨162141, by rfl⟩ : syracuseStep 432377 = 324283) B324283
theorem B3742847 : Blo 191804 3742847 := bstep (se 1 (by rfl) ⟨2807135, by rfl⟩ : syracuseStep 3742847 = 5614271) B5614271
theorem B827131 : Blo 191804 827131 := bstep (se 1 (by rfl) ⟨620348, by rfl⟩ : syracuseStep 827131 = 1240697) B1240697
theorem B3284873 : Blo 191804 3284873 := bstep (se 2 (by rfl) ⟨1231827, by rfl⟩ : syracuseStep 3284873 = 2463655) B2463655
theorem B1056655 : Blo 191804 1056655 := bstep (se 1 (by rfl) ⟨792491, by rfl⟩ : syracuseStep 1056655 = 1584983) B1584983
theorem B892907 : Blo 191804 892907 := bstep (se 1 (by rfl) ⟨669680, by rfl⟩ : syracuseStep 892907 = 1339361) B1339361
theorem B729607 : Blo 191804 729607 := bstep (se 1 (by rfl) ⟨547205, by rfl⟩ : syracuseStep 729607 = 1094411) B1094411
theorem B1909889 : Blo 191804 1909889 := bstep (se 2 (by rfl) ⟨716208, by rfl⟩ : syracuseStep 1909889 = 1432417) B1432417
theorem B206911 : Blo 191804 206911 := bstep (se 1 (by rfl) ⟨155183, by rfl⟩ : syracuseStep 206911 = 310367) B310367
theorem B436499 : Blo 191804 436499 := bstep (se 1 (by rfl) ⟨327374, by rfl⟩ : syracuseStep 436499 = 654749) B654749
theorem B437561 : Blo 191804 437561 := bstep (se 2 (by rfl) ⟨164085, by rfl⟩ : syracuseStep 437561 = 328171) B328171
theorem B3879251 : Blo 191804 3879251 := bstep (se 1 (by rfl) ⟨2909438, by rfl⟩ : syracuseStep 3879251 = 5818877) B5818877
theorem B438911 : Blo 191804 438911 := bstep (se 1 (by rfl) ⟨329183, by rfl⟩ : syracuseStep 438911 = 658367) B658367
theorem B3324239 : Blo 191804 3324239 := bstep (se 1 (by rfl) ⟨2493179, by rfl⟩ : syracuseStep 3324239 = 4986359) B4986359
theorem B444755 : Blo 191804 444755 := bstep (se 1 (by rfl) ⟨333566, by rfl⟩ : syracuseStep 444755 = 667133) B667133
theorem B739799 : Blo 191804 739799 := bstep (se 1 (by rfl) ⟨554849, by rfl⟩ : syracuseStep 739799 = 1109699) B1109699
theorem B707039 : Blo 191804 707039 := bstep (se 1 (by rfl) ⟨530279, by rfl⟩ : syracuseStep 707039 = 1060559) B1060559
theorem B1101383 : Blo 191804 1101383 := bstep (se 1 (by rfl) ⟨826037, by rfl⟩ : syracuseStep 1101383 = 1652075) B1652075
theorem B413839 : Blo 191804 413839 := bstep (se 1 (by rfl) ⟨310379, by rfl⟩ : syracuseStep 413839 = 620759) B620759
theorem B1628059 : Blo 191804 1628059 := bstep (se 1 (by rfl) ⟨1221044, by rfl⟩ : syracuseStep 1628059 = 2442089) B2442089
theorem B417307 : Blo 191804 417307 := bstep (se 1 (by rfl) ⟨312980, by rfl⟩ : syracuseStep 417307 = 625961) B625961
theorem B647783 : Blo 191804 647783 := bstep (se 1 (by rfl) ⟨485837, by rfl⟩ : syracuseStep 647783 = 971675) B971675
theorem B3302369 : Blo 191804 3302369 := bstep (se 2 (by rfl) ⟨1238388, by rfl⟩ : syracuseStep 3302369 = 2476777) B2476777
theorem B288359 : Blo 191804 288359 := bstep (se 1 (by rfl) ⟨216269, by rfl⟩ : syracuseStep 288359 = 432539) B432539
theorem B944467 : Blo 191804 944467 := bstep (se 1 (by rfl) ⟨708350, by rfl⟩ : syracuseStep 944467 = 1416701) B1416701
theorem B780671 : Blo 191804 780671 := bstep (se 1 (by rfl) ⟨585503, by rfl⟩ : syracuseStep 780671 = 1171007) B1171007
theorem B191847 : Blo 191804 191847 := bstep (se 1 (by rfl) ⟨143885, by rfl⟩ : syracuseStep 191847 = 287771) B287771
theorem B290729 : Blo 191804 290729 := bstep (se 2 (by rfl) ⟨109023, by rfl⟩ : syracuseStep 290729 = 218047) B218047
theorem B193255 : Blo 191804 193255 := bstep (se 1 (by rfl) ⟨144941, by rfl⟩ : syracuseStep 193255 = 289883) B289883
theorem B324479 : Blo 191804 324479 := bstep (se 1 (by rfl) ⟨243359, by rfl⟩ : syracuseStep 324479 = 486719) B486719
theorem B193563 : Blo 191804 193563 := bstep (se 1 (by rfl) ⟨145172, by rfl⟩ : syracuseStep 193563 = 290345) B290345
theorem B194207 : Blo 191804 194207 := bstep (se 1 (by rfl) ⟨145655, by rfl⟩ : syracuseStep 194207 = 291311) B291311
theorem B194303 : Blo 191804 194303 := bstep (se 1 (by rfl) ⟨145727, by rfl⟩ : syracuseStep 194303 = 291455) B291455
theorem B12056377 : Blo 191804 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B194415 : Blo 191804 194415 := bstep (se 1 (by rfl) ⟨145811, by rfl⟩ : syracuseStep 194415 = 291623) B291623
theorem B194971 : Blo 191804 194971 := bstep (se 1 (by rfl) ⟨146228, by rfl⟩ : syracuseStep 194971 = 292457) B292457
theorem B10681247 : Blo 191804 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B195775 : Blo 191804 195775 := bstep (se 1 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 195775 = 293663) B293663
theorem B655343 : Blo 191804 655343 := bstep (se 1 (by rfl) ⟨491507, by rfl⟩ : syracuseStep 655343 = 983015) B983015
theorem B296503 : Blo 191804 296503 := bstep (se 1 (by rfl) ⟨222377, by rfl⟩ : syracuseStep 296503 = 444755) B444755
theorem B493199 : Blo 191804 493199 := bstep (se 1 (by rfl) ⟨369899, by rfl⟩ : syracuseStep 493199 = 739799) B739799
theorem B528761 : Blo 191804 528761 := bstep (se 2 (by rfl) ⟨198285, by rfl⟩ : syracuseStep 528761 = 396571) B396571
theorem B2495231 : Blo 191804 2495231 := bstep (se 1 (by rfl) ⟨1871423, by rfl⟩ : syracuseStep 2495231 = 3742847) B3742847
theorem B595271 : Blo 191804 595271 := bstep (se 1 (by rfl) ⟨446453, by rfl⟩ : syracuseStep 595271 = 892907) B892907
theorem B431855 : Blo 191804 431855 := bstep (se 1 (by rfl) ⟨323891, by rfl⟩ : syracuseStep 431855 = 647783) B647783
theorem B2201579 : Blo 191804 2201579 := bstep (se 1 (by rfl) ⟨1651184, by rfl⟩ : syracuseStep 2201579 = 3302369) B3302369
theorem B2170745 : Blo 191804 2170745 := bstep (se 2 (by rfl) ⟨814029, by rfl⟩ : syracuseStep 2170745 = 1628059) B1628059
theorem B7120831 : Blo 191804 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B436895 : Blo 191804 436895 := bstep (se 1 (by rfl) ⟨327671, by rfl⟩ : syracuseStep 436895 = 655343) B655343
theorem B471359 : Blo 191804 471359 := bstep (se 1 (by rfl) ⟨353519, by rfl⟩ : syracuseStep 471359 = 707039) B707039
theorem B438875 : Blo 191804 438875 := bstep (se 1 (by rfl) ⟨329156, by rfl⟩ : syracuseStep 438875 = 658313) B658313
theorem B1094593 : Blo 191804 1094593 := bstep (se 2 (by rfl) ⟨410472, by rfl⟩ : syracuseStep 1094593 = 820945) B820945
theorem B734255 : Blo 191804 734255 := bstep (se 1 (by rfl) ⟨550691, by rfl⟩ : syracuseStep 734255 = 1101383) B1101383
theorem B275881 : Blo 191804 275881 := bstep (se 2 (by rfl) ⟨103455, by rfl⟩ : syracuseStep 275881 = 206911) B206911
theorem B1095551 : Blo 191804 1095551 := bstep (se 1 (by rfl) ⟨821663, by rfl⟩ : syracuseStep 1095551 = 1643327) B1643327
theorem B16075169 : Blo 191804 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B216319 : Blo 191804 216319 := bstep (se 1 (by rfl) ⟨162239, by rfl⟩ : syracuseStep 216319 = 324479) B324479
theorem B2216159 : Blo 191804 2216159 := bstep (se 1 (by rfl) ⟨1662119, by rfl⟩ : syracuseStep 2216159 = 3324239) B3324239
theorem B1102841 : Blo 191804 1102841 := bstep (se 2 (by rfl) ⟨413565, by rfl⟩ : syracuseStep 1102841 = 827131) B827131
theorem B972809 : Blo 191804 972809 := bstep (se 2 (by rfl) ⟨364803, by rfl⟩ : syracuseStep 972809 = 729607) B729607
theorem B5037157 : Blo 191804 5037157 := bstep (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) B944467
theorem B2317871 : Blo 191804 2317871 := bstep (se 1 (by rfl) ⟨1738403, by rfl⟩ : syracuseStep 2317871 = 3476807) B3476807
theorem B2188457 : Blo 191804 2188457 := bstep (se 2 (by rfl) ⟨820671, by rfl⟩ : syracuseStep 2188457 = 1641343) B1641343
theorem B288251 : Blo 191804 288251 := bstep (se 1 (by rfl) ⟨216188, by rfl⟩ : syracuseStep 288251 = 432377) B432377
theorem B2189915 : Blo 191804 2189915 := bstep (se 1 (by rfl) ⟨1642436, by rfl⟩ : syracuseStep 2189915 = 3284873) B3284873
theorem B551785 : Blo 191804 551785 := bstep (se 2 (by rfl) ⟨206919, by rfl⟩ : syracuseStep 551785 = 413839) B413839
theorem B1273259 : Blo 191804 1273259 := bstep (se 1 (by rfl) ⟨954944, by rfl⟩ : syracuseStep 1273259 = 1909889) B1909889
theorem B192239 : Blo 191804 192239 := bstep (se 1 (by rfl) ⟨144179, by rfl⟩ : syracuseStep 192239 = 288359) B288359
theorem B290999 : Blo 191804 290999 := bstep (se 1 (by rfl) ⟨218249, by rfl⟩ : syracuseStep 290999 = 436499) B436499
theorem B520447 : Blo 191804 520447 := bstep (se 1 (by rfl) ⟨390335, by rfl⟩ : syracuseStep 520447 = 780671) B780671
theorem B291707 : Blo 191804 291707 := bstep (se 1 (by rfl) ⟨218780, by rfl⟩ : syracuseStep 291707 = 437561) B437561
theorem B193819 : Blo 191804 193819 := bstep (se 1 (by rfl) ⟨145364, by rfl⟩ : syracuseStep 193819 = 290729) B290729
theorem B2586167 : Blo 191804 2586167 := bstep (se 1 (by rfl) ⟨1939625, by rfl⟩ : syracuseStep 2586167 = 3879251) B3879251
theorem B292607 : Blo 191804 292607 := bstep (se 1 (by rfl) ⟨219455, by rfl⟩ : syracuseStep 292607 = 438911) B438911
theorem B556409 : Blo 191804 556409 := bstep (se 2 (by rfl) ⟨208653, by rfl⟩ : syracuseStep 556409 = 417307) B417307
theorem B1408873 : Blo 191804 1408873 := bstep (se 2 (by rfl) ⟨528327, by rfl⟩ : syracuseStep 1408873 = 1056655) B1056655
theorem B328799 : Blo 191804 328799 := bstep (se 1 (by rfl) ⟨246599, by rfl⟩ : syracuseStep 328799 = 493199) B493199
theorem B6325397 : Blo 191804 6325397 := bstep (se 6 (by rfl) ⟨148251, by rfl⟩ : syracuseStep 6325397 = 296503) B296503
theorem B10716779 : Blo 191804 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B1477439 : Blo 191804 1477439 := bstep (se 1 (by rfl) ⟨1108079, by rfl⟩ : syracuseStep 1477439 = 2216159) B2216159
theorem B396847 : Blo 191804 396847 := bstep (se 1 (by rfl) ⟨297635, by rfl⟩ : syracuseStep 396847 = 595271) B595271
theorem B1545247 : Blo 191804 1545247 := bstep (se 1 (by rfl) ⟨1158935, by rfl⟩ : syracuseStep 1545247 = 2317871) B2317871
theorem B1447163 : Blo 191804 1447163 := bstep (se 1 (by rfl) ⟨1085372, by rfl⟩ : syracuseStep 1447163 = 2170745) B2170745
theorem B693929 : Blo 191804 693929 := bstep (se 2 (by rfl) ⟨260223, by rfl⟩ : syracuseStep 693929 = 520447) B520447
theorem B367841 : Blo 191804 367841 := bstep (se 2 (by rfl) ⟨137940, by rfl⟩ : syracuseStep 367841 = 275881) B275881
theorem B1483757 : Blo 191804 1483757 := bstep (se 3 (by rfl) ⟨278204, by rfl⟩ : syracuseStep 1483757 = 556409) B556409
theorem B730367 : Blo 191804 730367 := bstep (se 1 (by rfl) ⟨547775, by rfl⟩ : syracuseStep 730367 = 1095551) B1095551
theorem B1878497 : Blo 191804 1878497 := bstep (se 2 (by rfl) ⟨704436, by rfl⟩ : syracuseStep 1878497 = 1408873) B1408873
theorem B1256957 : Blo 191804 1256957 := bstep (se 3 (by rfl) ⟨235679, by rfl⟩ : syracuseStep 1256957 = 471359) B471359
theorem B735227 : Blo 191804 735227 := bstep (se 1 (by rfl) ⟨551420, by rfl⟩ : syracuseStep 735227 = 1102841) B1102841
theorem B735713 : Blo 191804 735713 := bstep (se 2 (by rfl) ⟨275892, by rfl⟩ : syracuseStep 735713 = 551785) B551785
theorem B1458971 : Blo 191804 1458971 := bstep (se 1 (by rfl) ⟨1094228, by rfl⟩ : syracuseStep 1458971 = 2188457) B2188457
theorem B1459457 : Blo 191804 1459457 := bstep (se 2 (by rfl) ⟨547296, by rfl⟩ : syracuseStep 1459457 = 1094593) B1094593
theorem B1459943 : Blo 191804 1459943 := bstep (se 1 (by rfl) ⟨1094957, by rfl⟩ : syracuseStep 1459943 = 2189915) B2189915
theorem B1724111 : Blo 191804 1724111 := bstep (se 1 (by rfl) ⟨1293083, by rfl⟩ : syracuseStep 1724111 = 2586167) B2586167
theorem B9494441 : Blo 191804 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B352507 : Blo 191804 352507 := bstep (se 1 (by rfl) ⟨264380, by rfl⟩ : syracuseStep 352507 = 528761) B528761
theorem B1663487 : Blo 191804 1663487 := bstep (se 1 (by rfl) ⟨1247615, by rfl⟩ : syracuseStep 1663487 = 2495231) B2495231
theorem B287903 : Blo 191804 287903 := bstep (se 1 (by rfl) ⟨215927, by rfl⟩ : syracuseStep 287903 = 431855) B431855
theorem B1467719 : Blo 191804 1467719 := bstep (se 1 (by rfl) ⟨1100789, by rfl⟩ : syracuseStep 1467719 = 2201579) B2201579
theorem B648539 : Blo 191804 648539 := bstep (se 1 (by rfl) ⟨486404, by rfl⟩ : syracuseStep 648539 = 972809) B972809
theorem B288425 : Blo 191804 288425 := bstep (se 2 (by rfl) ⟨108159, by rfl⟩ : syracuseStep 288425 = 216319) B216319
theorem B192167 : Blo 191804 192167 := bstep (se 1 (by rfl) ⟨144125, by rfl⟩ : syracuseStep 192167 = 288251) B288251
theorem B291263 : Blo 191804 291263 := bstep (se 1 (by rfl) ⟨218447, by rfl⟩ : syracuseStep 291263 = 436895) B436895
theorem B848839 : Blo 191804 848839 := bstep (se 1 (by rfl) ⟨636629, by rfl⟩ : syracuseStep 848839 = 1273259) B1273259
theorem B193999 : Blo 191804 193999 := bstep (se 1 (by rfl) ⟨145499, by rfl⟩ : syracuseStep 193999 = 290999) B290999
theorem B292583 : Blo 191804 292583 := bstep (se 1 (by rfl) ⟨219437, by rfl⟩ : syracuseStep 292583 = 438875) B438875
theorem B194471 : Blo 191804 194471 := bstep (se 1 (by rfl) ⟨145853, by rfl⟩ : syracuseStep 194471 = 291707) B291707
theorem B489503 : Blo 191804 489503 := bstep (se 1 (by rfl) ⟨367127, by rfl⟩ : syracuseStep 489503 = 734255) B734255
theorem B195071 : Blo 191804 195071 := bstep (se 1 (by rfl) ⟨146303, by rfl⟩ : syracuseStep 195071 = 292607) B292607
theorem B6716209 : Blo 191804 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B7144519 : Blo 191804 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B984959 : Blo 191804 984959 := bstep (se 1 (by rfl) ⟨738719, by rfl⟩ : syracuseStep 984959 = 1477439) B1477439
theorem B1149407 : Blo 191804 1149407 := bstep (se 1 (by rfl) ⟨862055, by rfl⟩ : syracuseStep 1149407 = 1724111) B1724111
theorem B462619 : Blo 191804 462619 := bstep (se 1 (by rfl) ⟨346964, by rfl⟩ : syracuseStep 462619 = 693929) B693929
theorem B529129 : Blo 191804 529129 := bstep (se 2 (by rfl) ⟨198423, by rfl⟩ : syracuseStep 529129 = 396847) B396847
theorem B6329627 : Blo 191804 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B989171 : Blo 191804 989171 := bstep (se 1 (by rfl) ⟨741878, by rfl⟩ : syracuseStep 989171 = 1483757) B1483757
theorem B432359 : Blo 191804 432359 := bstep (se 1 (by rfl) ⟨324269, by rfl⟩ : syracuseStep 432359 = 648539) B648539
theorem B1252331 : Blo 191804 1252331 := bstep (se 1 (by rfl) ⟨939248, by rfl⟩ : syracuseStep 1252331 = 1878497) B1878497
theorem B8954945 : Blo 191804 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B470009 : Blo 191804 470009 := bstep (se 2 (by rfl) ⟨176253, by rfl⟩ : syracuseStep 470009 = 352507) B352507
theorem B964775 : Blo 191804 964775 := bstep (se 1 (by rfl) ⟨723581, by rfl⟩ : syracuseStep 964775 = 1447163) B1447163
theorem B1131785 : Blo 191804 1131785 := bstep (se 2 (by rfl) ⟨424419, by rfl⟩ : syracuseStep 1131785 = 848839) B848839
theorem B837971 : Blo 191804 837971 := bstep (se 1 (by rfl) ⟨628478, by rfl⟩ : syracuseStep 837971 = 1256957) B1256957
theorem B972647 : Blo 191804 972647 := bstep (se 1 (by rfl) ⟨729485, by rfl⟩ : syracuseStep 972647 = 1458971) B1458971
theorem B219199 : Blo 191804 219199 := bstep (se 1 (by rfl) ⟨164399, by rfl⟩ : syracuseStep 219199 = 328799) B328799
theorem B4216931 : Blo 191804 4216931 := bstep (se 1 (by rfl) ⟨3162698, by rfl⟩ : syracuseStep 4216931 = 6325397) B6325397
theorem B972971 : Blo 191804 972971 := bstep (se 1 (by rfl) ⟨729728, by rfl⟩ : syracuseStep 972971 = 1459457) B1459457
theorem B973295 : Blo 191804 973295 := bstep (se 1 (by rfl) ⟨729971, by rfl⟩ : syracuseStep 973295 = 1459943) B1459943
theorem B1108991 : Blo 191804 1108991 := bstep (se 1 (by rfl) ⟨831743, by rfl⟩ : syracuseStep 1108991 = 1663487) B1663487
theorem B191935 : Blo 191804 191935 := bstep (se 1 (by rfl) ⟨143951, by rfl⟩ : syracuseStep 191935 = 287903) B287903
theorem B486911 : Blo 191804 486911 := bstep (se 1 (by rfl) ⟨365183, by rfl⟩ : syracuseStep 486911 = 730367) B730367
theorem B978479 : Blo 191804 978479 := bstep (se 1 (by rfl) ⟨733859, by rfl⟩ : syracuseStep 978479 = 1467719) B1467719
theorem B192283 : Blo 191804 192283 := bstep (se 1 (by rfl) ⟨144212, by rfl⟩ : syracuseStep 192283 = 288425) B288425
theorem B2060329 : Blo 191804 2060329 := bstep (se 2 (by rfl) ⟨772623, by rfl⟩ : syracuseStep 2060329 = 1545247) B1545247
theorem B194175 : Blo 191804 194175 := bstep (se 1 (by rfl) ⟨145631, by rfl⟩ : syracuseStep 194175 = 291263) B291263
theorem B980909 : Blo 191804 980909 := bstep (se 3 (by rfl) ⟨183920, by rfl⟩ : syracuseStep 980909 = 367841) B367841
theorem B195055 : Blo 191804 195055 := bstep (se 1 (by rfl) ⟨146291, by rfl⟩ : syracuseStep 195055 = 292583) B292583
theorem B490151 : Blo 191804 490151 := bstep (se 1 (by rfl) ⟨367613, by rfl⟩ : syracuseStep 490151 = 735227) B735227
theorem B326335 : Blo 191804 326335 := bstep (se 1 (by rfl) ⟨244751, by rfl⟩ : syracuseStep 326335 = 489503) B489503
theorem B490475 : Blo 191804 490475 := bstep (se 1 (by rfl) ⟨367856, by rfl⟩ : syracuseStep 490475 = 735713) B735713
theorem B754523 : Blo 191804 754523 := bstep (se 1 (by rfl) ⟨565892, by rfl⟩ : syracuseStep 754523 = 1131785) B1131785
theorem B656639 : Blo 191804 656639 := bstep (se 1 (by rfl) ⟨492479, by rfl⟩ : syracuseStep 656639 = 984959) B984959
theorem B558647 : Blo 191804 558647 := bstep (se 1 (by rfl) ⟨418985, by rfl⟩ : syracuseStep 558647 = 837971) B837971
theorem B659447 : Blo 191804 659447 := bstep (se 1 (by rfl) ⟨494585, by rfl⟩ : syracuseStep 659447 = 989171) B989171
theorem B5969963 : Blo 191804 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B1253357 : Blo 191804 1253357 := bstep (se 3 (by rfl) ⟨235004, by rfl⟩ : syracuseStep 1253357 = 470009) B470009
theorem B435113 : Blo 191804 435113 := bstep (se 2 (by rfl) ⟨163167, by rfl⟩ : syracuseStep 435113 = 326335) B326335
theorem B766271 : Blo 191804 766271 := bstep (se 1 (by rfl) ⟨574703, by rfl⟩ : syracuseStep 766271 = 1149407) B1149407
theorem B834887 : Blo 191804 834887 := bstep (se 1 (by rfl) ⟨626165, by rfl⟩ : syracuseStep 834887 = 1252331) B1252331
theorem B705505 : Blo 191804 705505 := bstep (se 2 (by rfl) ⟨264564, by rfl⟩ : syracuseStep 705505 = 529129) B529129
theorem B739327 : Blo 191804 739327 := bstep (se 1 (by rfl) ⟨554495, by rfl⟩ : syracuseStep 739327 = 1108991) B1108991
theorem B643183 : Blo 191804 643183 := bstep (se 1 (by rfl) ⟨482387, by rfl⟩ : syracuseStep 643183 = 964775) B964775
theorem B9526025 : Blo 191804 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B4219751 : Blo 191804 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B648431 : Blo 191804 648431 := bstep (se 1 (by rfl) ⟨486323, by rfl⟩ : syracuseStep 648431 = 972647) B972647
theorem B2811287 : Blo 191804 2811287 := bstep (se 1 (by rfl) ⟨2108465, by rfl⟩ : syracuseStep 2811287 = 4216931) B4216931
theorem B648647 : Blo 191804 648647 := bstep (se 1 (by rfl) ⟨486485, by rfl⟩ : syracuseStep 648647 = 972971) B972971
theorem B288239 : Blo 191804 288239 := bstep (se 1 (by rfl) ⟨216179, by rfl⟩ : syracuseStep 288239 = 432359) B432359
theorem B648863 : Blo 191804 648863 := bstep (se 1 (by rfl) ⟨486647, by rfl⟩ : syracuseStep 648863 = 973295) B973295
theorem B616825 : Blo 191804 616825 := bstep (se 2 (by rfl) ⟨231309, by rfl⟩ : syracuseStep 616825 = 462619) B462619
theorem B2747105 : Blo 191804 2747105 := bstep (se 2 (by rfl) ⟨1030164, by rfl⟩ : syracuseStep 2747105 = 2060329) B2060329
theorem B324607 : Blo 191804 324607 := bstep (se 1 (by rfl) ⟨243455, by rfl⟩ : syracuseStep 324607 = 486911) B486911
theorem B652319 : Blo 191804 652319 := bstep (se 1 (by rfl) ⟨489239, by rfl⟩ : syracuseStep 652319 = 978479) B978479
theorem B292265 : Blo 191804 292265 := bstep (se 2 (by rfl) ⟨109599, by rfl⟩ : syracuseStep 292265 = 219199) B219199
theorem B653939 : Blo 191804 653939 := bstep (se 1 (by rfl) ⟨490454, by rfl⟩ : syracuseStep 653939 = 980909) B980909
theorem B326767 : Blo 191804 326767 := bstep (se 1 (by rfl) ⟨245075, by rfl⟩ : syracuseStep 326767 = 490151) B490151
theorem B326983 : Blo 191804 326983 := bstep (se 1 (by rfl) ⟨245237, by rfl⟩ : syracuseStep 326983 = 490475) B490475
theorem B985769 : Blo 191804 985769 := bstep (se 2 (by rfl) ⟨369663, by rfl⟩ : syracuseStep 985769 = 739327) B739327
theorem B822433 : Blo 191804 822433 := bstep (se 2 (by rfl) ⟨308412, by rfl⟩ : syracuseStep 822433 = 616825) B616825
theorem B432287 : Blo 191804 432287 := bstep (se 1 (by rfl) ⟨324215, by rfl⟩ : syracuseStep 432287 = 648431) B648431
theorem B1874191 : Blo 191804 1874191 := bstep (se 1 (by rfl) ⟨1405643, by rfl⟩ : syracuseStep 1874191 = 2811287) B2811287
theorem B432431 : Blo 191804 432431 := bstep (se 1 (by rfl) ⟨324323, by rfl⟩ : syracuseStep 432431 = 648647) B648647
theorem B432575 : Blo 191804 432575 := bstep (se 1 (by rfl) ⟨324431, by rfl⟩ : syracuseStep 432575 = 648863) B648863
theorem B432809 : Blo 191804 432809 := bstep (se 2 (by rfl) ⟨162303, by rfl⟩ : syracuseStep 432809 = 324607) B324607
theorem B434879 : Blo 191804 434879 := bstep (se 1 (by rfl) ⟨326159, by rfl⟩ : syracuseStep 434879 = 652319) B652319
theorem B435689 : Blo 191804 435689 := bstep (se 2 (by rfl) ⟨163383, by rfl⟩ : syracuseStep 435689 = 326767) B326767
theorem B435959 : Blo 191804 435959 := bstep (se 1 (by rfl) ⟨326969, by rfl⟩ : syracuseStep 435959 = 653939) B653939
theorem B435977 : Blo 191804 435977 := bstep (se 2 (by rfl) ⟨163491, by rfl⟩ : syracuseStep 435977 = 326983) B326983
theorem B503015 : Blo 191804 503015 := bstep (se 1 (by rfl) ⟨377261, by rfl⟩ : syracuseStep 503015 = 754523) B754523
theorem B2043389 : Blo 191804 2043389 := bstep (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) B766271
theorem B437759 : Blo 191804 437759 := bstep (se 1 (by rfl) ⟨328319, by rfl⟩ : syracuseStep 437759 = 656639) B656639
theorem B372431 : Blo 191804 372431 := bstep (se 1 (by rfl) ⟨279323, by rfl⟩ : syracuseStep 372431 = 558647) B558647
theorem B439631 : Blo 191804 439631 := bstep (se 1 (by rfl) ⟨329723, by rfl⟩ : syracuseStep 439631 = 659447) B659447
theorem B3979975 : Blo 191804 3979975 := bstep (se 1 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 3979975 = 5969963) B5969963
theorem B180042709 : Blo 191804 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B835571 : Blo 191804 835571 := bstep (se 1 (by rfl) ⟨626678, by rfl⟩ : syracuseStep 835571 = 1253357) B1253357
theorem B940673 : Blo 191804 940673 := bstep (se 2 (by rfl) ⟨352752, by rfl⟩ : syracuseStep 940673 = 705505) B705505
theorem B13721237 : Blo 191804 13721237 := bstep (se 6 (by rfl) ⟨321591, by rfl⟩ : syracuseStep 13721237 = 643183) B643183
theorem B6350683 : Blo 191804 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B290075 : Blo 191804 290075 := bstep (se 1 (by rfl) ⟨217556, by rfl⟩ : syracuseStep 290075 = 435113) B435113
theorem B192159 : Blo 191804 192159 := bstep (se 1 (by rfl) ⟨144119, by rfl⟩ : syracuseStep 192159 = 288239) B288239
theorem B1831403 : Blo 191804 1831403 := bstep (se 1 (by rfl) ⟨1373552, by rfl⟩ : syracuseStep 1831403 = 2747105) B2747105
theorem B2226365 : Blo 191804 2226365 := bstep (se 3 (by rfl) ⟨417443, by rfl⟩ : syracuseStep 2226365 = 834887) B834887
theorem B194843 : Blo 191804 194843 := bstep (se 1 (by rfl) ⟨146132, by rfl⟩ : syracuseStep 194843 = 292265) B292265
theorem B657179 : Blo 191804 657179 := bstep (se 1 (by rfl) ⟨492884, by rfl⟩ : syracuseStep 657179 = 985769) B985769
theorem B627115 : Blo 191804 627115 := bstep (se 1 (by rfl) ⟨470336, by rfl⟩ : syracuseStep 627115 = 940673) B940673
theorem B9147491 : Blo 191804 9147491 := bstep (se 1 (by rfl) ⟨6860618, by rfl⟩ : syracuseStep 9147491 = 13721237) B13721237
theorem B1220935 : Blo 191804 1220935 := bstep (se 1 (by rfl) ⟨915701, by rfl⟩ : syracuseStep 1220935 = 1831403) B1831403
theorem B2498921 : Blo 191804 2498921 := bstep (se 2 (by rfl) ⟨937095, by rfl⟩ : syracuseStep 2498921 = 1874191) B1874191
theorem B5449037 : Blo 191804 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B1484243 : Blo 191804 1484243 := bstep (se 1 (by rfl) ⟨1113182, by rfl⟩ : syracuseStep 1484243 = 2226365) B2226365
theorem B8467577 : Blo 191804 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B1096577 : Blo 191804 1096577 := bstep (se 2 (by rfl) ⟨411216, by rfl⟩ : syracuseStep 1096577 = 822433) B822433
theorem B248287 : Blo 191804 248287 := bstep (se 1 (by rfl) ⟨186215, by rfl⟩ : syracuseStep 248287 = 372431) B372431
theorem B288191 : Blo 191804 288191 := bstep (se 1 (by rfl) ⟨216143, by rfl⟩ : syracuseStep 288191 = 432287) B432287
theorem B288287 : Blo 191804 288287 := bstep (se 1 (by rfl) ⟨216215, by rfl⟩ : syracuseStep 288287 = 432431) B432431
theorem B288383 : Blo 191804 288383 := bstep (se 1 (by rfl) ⟨216287, by rfl⟩ : syracuseStep 288383 = 432575) B432575
theorem B288539 : Blo 191804 288539 := bstep (se 1 (by rfl) ⟨216404, by rfl⟩ : syracuseStep 288539 = 432809) B432809
theorem B289919 : Blo 191804 289919 := bstep (se 1 (by rfl) ⟨217439, by rfl⟩ : syracuseStep 289919 = 434879) B434879
theorem B290459 : Blo 191804 290459 := bstep (se 1 (by rfl) ⟨217844, by rfl⟩ : syracuseStep 290459 = 435689) B435689
theorem B290639 : Blo 191804 290639 := bstep (se 1 (by rfl) ⟨217979, by rfl⟩ : syracuseStep 290639 = 435959) B435959
theorem B290651 : Blo 191804 290651 := bstep (se 1 (by rfl) ⟨217988, by rfl⟩ : syracuseStep 290651 = 435977) B435977
theorem B193383 : Blo 191804 193383 := bstep (se 1 (by rfl) ⟨145037, by rfl⟩ : syracuseStep 193383 = 290075) B290075
theorem B291839 : Blo 191804 291839 := bstep (se 1 (by rfl) ⟨218879, by rfl⟩ : syracuseStep 291839 = 437759) B437759
theorem B1341373 : Blo 191804 1341373 := bstep (se 3 (by rfl) ⟨251507, by rfl⟩ : syracuseStep 1341373 = 503015) B503015
theorem B293087 : Blo 191804 293087 := bstep (se 1 (by rfl) ⟨219815, by rfl⟩ : syracuseStep 293087 = 439631) B439631
theorem B5306633 : Blo 191804 5306633 := bstep (se 2 (by rfl) ⟨1989987, by rfl⟩ : syracuseStep 5306633 = 3979975) B3979975
theorem B240056945 : Blo 191804 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B557047 : Blo 191804 557047 := bstep (se 1 (by rfl) ⟨417785, by rfl⟩ : syracuseStep 557047 = 835571) B835571
theorem B331049 : Blo 191804 331049 := bstep (se 2 (by rfl) ⟨124143, by rfl⟩ : syracuseStep 331049 = 248287) B248287
theorem B6098327 : Blo 191804 6098327 := bstep (se 1 (by rfl) ⟨4573745, by rfl⟩ : syracuseStep 6098327 = 9147491) B9147491
theorem B989495 : Blo 191804 989495 := bstep (se 1 (by rfl) ⟨742121, by rfl⟩ : syracuseStep 989495 = 1484243) B1484243
theorem B5645051 : Blo 191804 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B731051 : Blo 191804 731051 := bstep (se 1 (by rfl) ⟨548288, by rfl⟩ : syracuseStep 731051 = 1096577) B1096577
theorem B438119 : Blo 191804 438119 := bstep (se 1 (by rfl) ⟨328589, by rfl⟩ : syracuseStep 438119 = 657179) B657179
theorem B14530765 : Blo 191804 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B836153 : Blo 191804 836153 := bstep (se 2 (by rfl) ⟨313557, by rfl⟩ : syracuseStep 836153 = 627115) B627115
theorem B1788497 : Blo 191804 1788497 := bstep (se 2 (by rfl) ⟨670686, by rfl⟩ : syracuseStep 1788497 = 1341373) B1341373
theorem B742729 : Blo 191804 742729 := bstep (se 2 (by rfl) ⟨278523, by rfl⟩ : syracuseStep 742729 = 557047) B557047
theorem B1627913 : Blo 191804 1627913 := bstep (se 2 (by rfl) ⟨610467, by rfl⟩ : syracuseStep 1627913 = 1220935) B1220935
theorem B1665947 : Blo 191804 1665947 := bstep (se 1 (by rfl) ⟨1249460, by rfl⟩ : syracuseStep 1665947 = 2498921) B2498921
theorem B192127 : Blo 191804 192127 := bstep (se 1 (by rfl) ⟨144095, by rfl⟩ : syracuseStep 192127 = 288191) B288191
theorem B192191 : Blo 191804 192191 := bstep (se 1 (by rfl) ⟨144143, by rfl⟩ : syracuseStep 192191 = 288287) B288287
theorem B192255 : Blo 191804 192255 := bstep (se 1 (by rfl) ⟨144191, by rfl⟩ : syracuseStep 192255 = 288383) B288383
theorem B192359 : Blo 191804 192359 := bstep (se 1 (by rfl) ⟨144269, by rfl⟩ : syracuseStep 192359 = 288539) B288539
theorem B193279 : Blo 191804 193279 := bstep (se 1 (by rfl) ⟨144959, by rfl⟩ : syracuseStep 193279 = 289919) B289919
theorem B193639 : Blo 191804 193639 := bstep (se 1 (by rfl) ⟨145229, by rfl⟩ : syracuseStep 193639 = 290459) B290459
theorem B193759 : Blo 191804 193759 := bstep (se 1 (by rfl) ⟨145319, by rfl⟩ : syracuseStep 193759 = 290639) B290639
theorem B193767 : Blo 191804 193767 := bstep (se 1 (by rfl) ⟨145325, by rfl⟩ : syracuseStep 193767 = 290651) B290651
theorem B194559 : Blo 191804 194559 := bstep (se 1 (by rfl) ⟨145919, by rfl⟩ : syracuseStep 194559 = 291839) B291839
theorem B195391 : Blo 191804 195391 := bstep (se 1 (by rfl) ⟨146543, by rfl⟩ : syracuseStep 195391 = 293087) B293087
theorem B3537755 : Blo 191804 3537755 := bstep (se 1 (by rfl) ⟨2653316, by rfl⟩ : syracuseStep 3537755 = 5306633) B5306633
theorem B160037963 : Blo 191804 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B557435 : Blo 191804 557435 := bstep (se 1 (by rfl) ⟨418076, by rfl⟩ : syracuseStep 557435 = 836153) B836153
theorem B4065551 : Blo 191804 4065551 := bstep (se 1 (by rfl) ⟨3049163, by rfl⟩ : syracuseStep 4065551 = 6098327) B6098327
theorem B1085275 : Blo 191804 1085275 := bstep (se 1 (by rfl) ⟨813956, by rfl⟩ : syracuseStep 1085275 = 1627913) B1627913
theorem B659663 : Blo 191804 659663 := bstep (se 1 (by rfl) ⟨494747, by rfl⟩ : syracuseStep 659663 = 989495) B989495
theorem B990305 : Blo 191804 990305 := bstep (se 2 (by rfl) ⟨371364, by rfl⟩ : syracuseStep 990305 = 742729) B742729
theorem B19374353 : Blo 191804 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B1192331 : Blo 191804 1192331 := bstep (se 1 (by rfl) ⟨894248, by rfl⟩ : syracuseStep 1192331 = 1788497) B1788497
theorem B220699 : Blo 191804 220699 := bstep (se 1 (by rfl) ⟨165524, by rfl⟩ : syracuseStep 220699 = 331049) B331049
theorem B3763367 : Blo 191804 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B487367 : Blo 191804 487367 := bstep (se 1 (by rfl) ⟨365525, by rfl⟩ : syracuseStep 487367 = 731051) B731051
theorem B1110631 : Blo 191804 1110631 := bstep (se 1 (by rfl) ⟨832973, by rfl⟩ : syracuseStep 1110631 = 1665947) B1665947
theorem B292079 : Blo 191804 292079 := bstep (se 1 (by rfl) ⟨219059, by rfl⟩ : syracuseStep 292079 = 438119) B438119
theorem B2358503 : Blo 191804 2358503 := bstep (se 1 (by rfl) ⟨1768877, by rfl⟩ : syracuseStep 2358503 = 3537755) B3537755
theorem B106691975 : Blo 191804 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B660203 : Blo 191804 660203 := bstep (se 1 (by rfl) ⟨495152, by rfl⟩ : syracuseStep 660203 = 990305) B990305
theorem B1447033 : Blo 191804 1447033 := bstep (se 2 (by rfl) ⟨542637, by rfl⟩ : syracuseStep 1447033 = 1085275) B1085275
theorem B12916235 : Blo 191804 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B1480841 : Blo 191804 1480841 := bstep (se 2 (by rfl) ⟨555315, by rfl⟩ : syracuseStep 1480841 = 1110631) B1110631
theorem B794887 : Blo 191804 794887 := bstep (se 1 (by rfl) ⟨596165, by rfl⟩ : syracuseStep 794887 = 1192331) B1192331
theorem B371623 : Blo 191804 371623 := bstep (se 1 (by rfl) ⟨278717, by rfl⟩ : syracuseStep 371623 = 557435) B557435
theorem B439775 : Blo 191804 439775 := bstep (se 1 (by rfl) ⟨329831, by rfl⟩ : syracuseStep 439775 = 659663) B659663
theorem B2508911 : Blo 191804 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B71127983 : Blo 191804 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B2710367 : Blo 191804 2710367 := bstep (se 1 (by rfl) ⟨2032775, by rfl⟩ : syracuseStep 2710367 = 4065551) B4065551
theorem B324911 : Blo 191804 324911 := bstep (se 1 (by rfl) ⟨243683, by rfl⟩ : syracuseStep 324911 = 487367) B487367
theorem B194719 : Blo 191804 194719 := bstep (se 1 (by rfl) ⟨146039, by rfl⟩ : syracuseStep 194719 = 292079) B292079
theorem B294265 : Blo 191804 294265 := bstep (se 2 (by rfl) ⟨110349, by rfl⟩ : syracuseStep 294265 = 220699) B220699
theorem B1572335 : Blo 191804 1572335 := bstep (se 1 (by rfl) ⟨1179251, by rfl⟩ : syracuseStep 1572335 = 2358503) B2358503
theorem B1672607 : Blo 191804 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B47418655 : Blo 191804 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B495497 : Blo 191804 495497 := bstep (se 2 (by rfl) ⟨185811, by rfl⟩ : syracuseStep 495497 = 371623) B371623
theorem B987227 : Blo 191804 987227 := bstep (se 1 (by rfl) ⟨740420, by rfl⟩ : syracuseStep 987227 = 1480841) B1480841
theorem B1806911 : Blo 191804 1806911 := bstep (se 1 (by rfl) ⟨1355183, by rfl⟩ : syracuseStep 1806911 = 2710367) B2710367
theorem B4239397 : Blo 191804 4239397 := bstep (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) B794887
theorem B440135 : Blo 191804 440135 := bstep (se 1 (by rfl) ⟨330101, by rfl⟩ : syracuseStep 440135 = 660203) B660203
theorem B216607 : Blo 191804 216607 := bstep (se 1 (by rfl) ⟨162455, by rfl⟩ : syracuseStep 216607 = 324911) B324911
theorem B8610823 : Blo 191804 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B1929377 : Blo 191804 1929377 := bstep (se 2 (by rfl) ⟨723516, by rfl⟩ : syracuseStep 1929377 = 1447033) B1447033
theorem B293183 : Blo 191804 293183 := bstep (se 1 (by rfl) ⟨219887, by rfl⟩ : syracuseStep 293183 = 439775) B439775
theorem B392353 : Blo 191804 392353 := bstep (se 2 (by rfl) ⟨147132, by rfl⟩ : syracuseStep 392353 = 294265) B294265
theorem B1048223 : Blo 191804 1048223 := bstep (se 1 (by rfl) ⟨786167, by rfl⟩ : syracuseStep 1048223 = 1572335) B1572335
theorem B22610117 : Blo 191804 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B5145005 : Blo 191804 5145005 := bstep (se 3 (by rfl) ⟨964688, by rfl⟩ : syracuseStep 5145005 = 1929377) B1929377
theorem B330331 : Blo 191804 330331 := bstep (se 1 (by rfl) ⟨247748, by rfl⟩ : syracuseStep 330331 = 495497) B495497
theorem B658151 : Blo 191804 658151 := bstep (se 1 (by rfl) ⟨493613, by rfl⟩ : syracuseStep 658151 = 987227) B987227
theorem B4460285 : Blo 191804 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B1321325 : Blo 191804 1321325 := bstep (se 3 (by rfl) ⟨247748, by rfl⟩ : syracuseStep 1321325 = 495497) B495497
theorem B698815 : Blo 191804 698815 := bstep (se 1 (by rfl) ⟨524111, by rfl⟩ : syracuseStep 698815 = 1048223) B1048223
theorem B11481097 : Blo 191804 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B63224873 : Blo 191804 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B1204607 : Blo 191804 1204607 := bstep (se 1 (by rfl) ⟨903455, by rfl⟩ : syracuseStep 1204607 = 1806911) B1806911
theorem B288809 : Blo 191804 288809 := bstep (se 2 (by rfl) ⟨108303, by rfl⟩ : syracuseStep 288809 = 216607) B216607
theorem B2092549 : Blo 191804 2092549 := bstep (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) B392353
theorem B293423 : Blo 191804 293423 := bstep (se 1 (by rfl) ⟨220067, by rfl⟩ : syracuseStep 293423 = 440135) B440135
theorem B195455 : Blo 191804 195455 := bstep (se 1 (by rfl) ⟨146591, by rfl⟩ : syracuseStep 195455 = 293183) B293183
theorem B60293645 : Blo 191804 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B2790065 : Blo 191804 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B15308129 : Blo 191804 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B42149915 : Blo 191804 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B438767 : Blo 191804 438767 := bstep (se 1 (by rfl) ⟨329075, by rfl⟩ : syracuseStep 438767 = 658151) B658151
theorem B931753 : Blo 191804 931753 := bstep (se 2 (by rfl) ⟨349407, by rfl⟩ : syracuseStep 931753 = 698815) B698815
theorem B440441 : Blo 191804 440441 := bstep (se 2 (by rfl) ⟨165165, by rfl⟩ : syracuseStep 440441 = 330331) B330331
theorem B803071 : Blo 191804 803071 := bstep (se 1 (by rfl) ⟨602303, by rfl⟩ : syracuseStep 803071 = 1204607) B1204607
theorem B13720013 : Blo 191804 13720013 := bstep (se 3 (by rfl) ⟨2572502, by rfl⟩ : syracuseStep 13720013 = 5145005) B5145005
theorem B2973523 : Blo 191804 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B192539 : Blo 191804 192539 := bstep (se 1 (by rfl) ⟨144404, by rfl⟩ : syracuseStep 192539 = 288809) B288809
theorem B880883 : Blo 191804 880883 := bstep (se 1 (by rfl) ⟨660662, by rfl⟩ : syracuseStep 880883 = 1321325) B1321325
theorem B195615 : Blo 191804 195615 := bstep (se 1 (by rfl) ⟨146711, by rfl⟩ : syracuseStep 195615 = 293423) B293423
theorem B7440173 : Blo 191804 7440173 := bstep (se 3 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 7440173 = 2790065) B2790065
theorem B9146675 : Blo 191804 9146675 := bstep (se 1 (by rfl) ⟨6860006, by rfl⟩ : syracuseStep 9146675 = 13720013) B13720013
theorem B28099943 : Blo 191804 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B1070761 : Blo 191804 1070761 := bstep (se 2 (by rfl) ⟨401535, by rfl⟩ : syracuseStep 1070761 = 803071) B803071
theorem B40195763 : Blo 191804 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B40821677 : Blo 191804 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B1242337 : Blo 191804 1242337 := bstep (se 2 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 1242337 = 931753) B931753
theorem B587255 : Blo 191804 587255 := bstep (se 1 (by rfl) ⟨440441, by rfl⟩ : syracuseStep 587255 = 880883) B880883
theorem B292511 : Blo 191804 292511 := bstep (se 1 (by rfl) ⟨219383, by rfl⟩ : syracuseStep 292511 = 438767) B438767
theorem B293627 : Blo 191804 293627 := bstep (se 1 (by rfl) ⟨220220, by rfl⟩ : syracuseStep 293627 = 440441) B440441
theorem B3964697 : Blo 191804 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B6097783 : Blo 191804 6097783 := bstep (se 1 (by rfl) ⟨4573337, by rfl⟩ : syracuseStep 6097783 = 9146675) B9146675
theorem B4960115 : Blo 191804 4960115 := bstep (se 1 (by rfl) ⟨3720086, by rfl⟩ : syracuseStep 4960115 = 7440173) B7440173
theorem B27214451 : Blo 191804 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B1656449 : Blo 191804 1656449 := bstep (se 2 (by rfl) ⟨621168, by rfl⟩ : syracuseStep 1656449 = 1242337) B1242337
theorem B1427681 : Blo 191804 1427681 := bstep (se 2 (by rfl) ⟨535380, by rfl⟩ : syracuseStep 1427681 = 1070761) B1070761
theorem B2643131 : Blo 191804 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B18733295 : Blo 191804 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B26797175 : Blo 191804 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B1566013 : Blo 191804 1566013 := bstep (se 3 (by rfl) ⟨293627, by rfl⟩ : syracuseStep 1566013 = 587255) B587255
theorem B195007 : Blo 191804 195007 := bstep (se 1 (by rfl) ⟨146255, by rfl⟩ : syracuseStep 195007 = 292511) B292511
theorem B195751 : Blo 191804 195751 := bstep (se 1 (by rfl) ⟨146813, by rfl⟩ : syracuseStep 195751 = 293627) B293627
theorem B951787 : Blo 191804 951787 := bstep (se 1 (by rfl) ⟨713840, by rfl⟩ : syracuseStep 951787 = 1427681) B1427681
theorem B8130377 : Blo 191804 8130377 := bstep (se 2 (by rfl) ⟨3048891, by rfl⟩ : syracuseStep 8130377 = 6097783) B6097783
theorem B12488863 : Blo 191804 12488863 := bstep (se 1 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 12488863 = 18733295) B18733295
theorem B17864783 : Blo 191804 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B18142967 : Blo 191804 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B1104299 : Blo 191804 1104299 := bstep (se 1 (by rfl) ⟨828224, by rfl⟩ : syracuseStep 1104299 = 1656449) B1656449
theorem B2088017 : Blo 191804 2088017 := bstep (se 2 (by rfl) ⟨783006, by rfl⟩ : syracuseStep 2088017 = 1566013) B1566013
theorem B1762087 : Blo 191804 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B3306743 : Blo 191804 3306743 := bstep (se 1 (by rfl) ⟨2480057, by rfl⟩ : syracuseStep 3306743 = 4960115) B4960115
theorem B16651817 : Blo 191804 16651817 := bstep (se 2 (by rfl) ⟨6244431, by rfl⟩ : syracuseStep 16651817 = 12488863) B12488863
theorem B2204495 : Blo 191804 2204495 := bstep (se 1 (by rfl) ⟨1653371, by rfl⟩ : syracuseStep 2204495 = 3306743) B3306743
theorem B5420251 : Blo 191804 5420251 := bstep (se 1 (by rfl) ⟨4065188, by rfl⟩ : syracuseStep 5420251 = 8130377) B8130377
theorem B11909855 : Blo 191804 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B736199 : Blo 191804 736199 := bstep (se 1 (by rfl) ⟨552149, by rfl⟩ : syracuseStep 736199 = 1104299) B1104299
theorem B48381245 : Blo 191804 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B1392011 : Blo 191804 1392011 := bstep (se 1 (by rfl) ⟨1044008, by rfl⟩ : syracuseStep 1392011 = 2088017) B2088017
theorem B2349449 : Blo 191804 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B1269049 : Blo 191804 1269049 := bstep (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) B951787
theorem B7939903 : Blo 191804 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B32254163 : Blo 191804 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B928007 : Blo 191804 928007 := bstep (se 1 (by rfl) ⟨696005, by rfl⟩ : syracuseStep 928007 = 1392011) B1392011
theorem B7227001 : Blo 191804 7227001 := bstep (se 2 (by rfl) ⟨2710125, by rfl⟩ : syracuseStep 7227001 = 5420251) B5420251
theorem B1692065 : Blo 191804 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B11101211 : Blo 191804 11101211 := bstep (se 1 (by rfl) ⟨8325908, by rfl⟩ : syracuseStep 11101211 = 16651817) B16651817
theorem B1566299 : Blo 191804 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B1469663 : Blo 191804 1469663 := bstep (se 1 (by rfl) ⟨1102247, by rfl⟩ : syracuseStep 1469663 = 2204495) B2204495
theorem B490799 : Blo 191804 490799 := bstep (se 1 (by rfl) ⟨368099, by rfl⟩ : syracuseStep 490799 = 736199) B736199
theorem B10586537 : Blo 191804 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B21502775 : Blo 191804 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B38544005 : Blo 191804 38544005 := bstep (se 4 (by rfl) ⟨3613500, by rfl⟩ : syracuseStep 38544005 = 7227001) B7227001
theorem B1128043 : Blo 191804 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B7400807 : Blo 191804 7400807 := bstep (se 1 (by rfl) ⟨5550605, by rfl⟩ : syracuseStep 7400807 = 11101211) B11101211
theorem B1044199 : Blo 191804 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B618671 : Blo 191804 618671 := bstep (se 1 (by rfl) ⟨464003, by rfl⟩ : syracuseStep 618671 = 928007) B928007
theorem B979775 : Blo 191804 979775 := bstep (se 1 (by rfl) ⟨734831, by rfl⟩ : syracuseStep 979775 = 1469663) B1469663
theorem B327199 : Blo 191804 327199 := bstep (se 1 (by rfl) ⟨245399, by rfl⟩ : syracuseStep 327199 = 490799) B490799
theorem B25696003 : Blo 191804 25696003 := bstep (se 1 (by rfl) ⟨19272002, by rfl⟩ : syracuseStep 25696003 = 38544005) B38544005
theorem B436265 : Blo 191804 436265 := bstep (se 2 (by rfl) ⟨163599, by rfl⟩ : syracuseStep 436265 = 327199) B327199
theorem B7057691 : Blo 191804 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B14335183 : Blo 191804 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B1392265 : Blo 191804 1392265 := bstep (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) B1044199
theorem B4933871 : Blo 191804 4933871 := bstep (se 1 (by rfl) ⟨3700403, by rfl⟩ : syracuseStep 4933871 = 7400807) B7400807
theorem B412447 : Blo 191804 412447 := bstep (se 1 (by rfl) ⟨309335, by rfl⟩ : syracuseStep 412447 = 618671) B618671
theorem B1504057 : Blo 191804 1504057 := bstep (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) B1128043
theorem B653183 : Blo 191804 653183 := bstep (se 1 (by rfl) ⟨489887, by rfl⟩ : syracuseStep 653183 = 979775) B979775
theorem B2005409 : Blo 191804 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B435455 : Blo 191804 435455 := bstep (se 1 (by rfl) ⟨326591, by rfl⟩ : syracuseStep 435455 = 653183) B653183
theorem B19113577 : Blo 191804 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B3289247 : Blo 191804 3289247 := bstep (se 1 (by rfl) ⟨2466935, by rfl⟩ : syracuseStep 3289247 = 4933871) B4933871
theorem B34261337 : Blo 191804 34261337 := bstep (se 2 (by rfl) ⟨12848001, by rfl⟩ : syracuseStep 34261337 = 25696003) B25696003
theorem B4705127 : Blo 191804 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B1856353 : Blo 191804 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B549929 : Blo 191804 549929 := bstep (se 2 (by rfl) ⟨206223, by rfl⟩ : syracuseStep 549929 = 412447) B412447
theorem B290843 : Blo 191804 290843 := bstep (se 1 (by rfl) ⟨218132, by rfl⟩ : syracuseStep 290843 = 436265) B436265
theorem B366619 : Blo 191804 366619 := bstep (se 1 (by rfl) ⟨274964, by rfl⟩ : syracuseStep 366619 = 549929) B549929
theorem B91363565 : Blo 191804 91363565 := bstep (se 3 (by rfl) ⟨17130668, by rfl⟩ : syracuseStep 91363565 = 34261337) B34261337
theorem B5347757 : Blo 191804 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B2475137 : Blo 191804 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B3136751 : Blo 191804 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B290303 : Blo 191804 290303 := bstep (se 1 (by rfl) ⟨217727, by rfl⟩ : syracuseStep 290303 = 435455) B435455
theorem B193895 : Blo 191804 193895 := bstep (se 1 (by rfl) ⟨145421, by rfl⟩ : syracuseStep 193895 = 290843) B290843
theorem B2192831 : Blo 191804 2192831 := bstep (se 1 (by rfl) ⟨1644623, by rfl⟩ : syracuseStep 2192831 = 3289247) B3289247
theorem B101939077 : Blo 191804 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B1650091 : Blo 191804 1650091 := bstep (se 1 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 1650091 = 2475137) B2475137
theorem B1461887 : Blo 191804 1461887 := bstep (se 1 (by rfl) ⟨1096415, by rfl⟩ : syracuseStep 1461887 = 2192831) B2192831
theorem B60909043 : Blo 191804 60909043 := bstep (se 1 (by rfl) ⟨45681782, by rfl⟩ : syracuseStep 60909043 = 91363565) B91363565
theorem B3565171 : Blo 191804 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B2091167 : Blo 191804 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B193535 : Blo 191804 193535 := bstep (se 1 (by rfl) ⟨145151, by rfl⟩ : syracuseStep 193535 = 290303) B290303
theorem B135918769 : Blo 191804 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B488825 : Blo 191804 488825 := bstep (se 2 (by rfl) ⟨183309, by rfl⟩ : syracuseStep 488825 = 366619) B366619
theorem B4753561 : Blo 191804 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B2200121 : Blo 191804 2200121 := bstep (se 2 (by rfl) ⟨825045, by rfl⟩ : syracuseStep 2200121 = 1650091) B1650091
theorem B81212057 : Blo 191804 81212057 := bstep (se 2 (by rfl) ⟨30454521, by rfl⟩ : syracuseStep 81212057 = 60909043) B60909043
theorem B1394111 : Blo 191804 1394111 := bstep (se 1 (by rfl) ⟨1045583, by rfl⟩ : syracuseStep 1394111 = 2091167) B2091167
theorem B181225025 : Blo 191804 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B974591 : Blo 191804 974591 := bstep (se 1 (by rfl) ⟨730943, by rfl⟩ : syracuseStep 974591 = 1461887) B1461887
theorem B325883 : Blo 191804 325883 := bstep (se 1 (by rfl) ⟨244412, by rfl⟩ : syracuseStep 325883 = 488825) B488825
theorem B120816683 : Blo 191804 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B54141371 : Blo 191804 54141371 := bstep (se 1 (by rfl) ⟨40606028, by rfl⟩ : syracuseStep 54141371 = 81212057) B81212057
theorem B929407 : Blo 191804 929407 := bstep (se 1 (by rfl) ⟨697055, by rfl⟩ : syracuseStep 929407 = 1394111) B1394111
theorem B6338081 : Blo 191804 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B217255 : Blo 191804 217255 := bstep (se 1 (by rfl) ⟨162941, by rfl⟩ : syracuseStep 217255 = 325883) B325883
theorem B1466747 : Blo 191804 1466747 := bstep (se 1 (by rfl) ⟨1100060, by rfl⟩ : syracuseStep 1466747 = 2200121) B2200121
theorem B649727 : Blo 191804 649727 := bstep (se 1 (by rfl) ⟨487295, by rfl⟩ : syracuseStep 649727 = 974591) B974591
theorem B80544455 : Blo 191804 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B433151 : Blo 191804 433151 := bstep (se 1 (by rfl) ⟨324863, by rfl⟩ : syracuseStep 433151 = 649727) B649727
theorem B36094247 : Blo 191804 36094247 := bstep (se 1 (by rfl) ⟨27070685, by rfl⟩ : syracuseStep 36094247 = 54141371) B54141371
theorem B1239209 : Blo 191804 1239209 := bstep (se 2 (by rfl) ⟨464703, by rfl⟩ : syracuseStep 1239209 = 929407) B929407
theorem B289673 : Blo 191804 289673 := bstep (se 2 (by rfl) ⟨108627, by rfl⟩ : syracuseStep 289673 = 217255) B217255
theorem B977831 : Blo 191804 977831 := bstep (se 1 (by rfl) ⟨733373, by rfl⟩ : syracuseStep 977831 = 1466747) B1466747
theorem B4225387 : Blo 191804 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B826139 : Blo 191804 826139 := bstep (se 1 (by rfl) ⟨619604, by rfl⟩ : syracuseStep 826139 = 1239209) B1239209
theorem B24062831 : Blo 191804 24062831 := bstep (se 1 (by rfl) ⟨18047123, by rfl⟩ : syracuseStep 24062831 = 36094247) B36094247
theorem B53696303 : Blo 191804 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B288767 : Blo 191804 288767 := bstep (se 1 (by rfl) ⟨216575, by rfl⟩ : syracuseStep 288767 = 433151) B433151
theorem B193115 : Blo 191804 193115 := bstep (se 1 (by rfl) ⟨144836, by rfl⟩ : syracuseStep 193115 = 289673) B289673
theorem B651887 : Blo 191804 651887 := bstep (se 1 (by rfl) ⟨488915, by rfl⟩ : syracuseStep 651887 = 977831) B977831
theorem B5633849 : Blo 191804 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B2203037 : Blo 191804 2203037 := bstep (se 3 (by rfl) ⟨413069, by rfl⟩ : syracuseStep 2203037 = 826139) B826139
theorem B434591 : Blo 191804 434591 := bstep (se 1 (by rfl) ⟨325943, by rfl⟩ : syracuseStep 434591 = 651887) B651887
theorem B35797535 : Blo 191804 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B16041887 : Blo 191804 16041887 := bstep (se 1 (by rfl) ⟨12031415, by rfl⟩ : syracuseStep 16041887 = 24062831) B24062831
theorem B3755899 : Blo 191804 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B192511 : Blo 191804 192511 := bstep (se 1 (by rfl) ⟨144383, by rfl⟩ : syracuseStep 192511 = 288767) B288767
theorem B23865023 : Blo 191804 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B10694591 : Blo 191804 10694591 := bstep (se 1 (by rfl) ⟨8020943, by rfl⟩ : syracuseStep 10694591 = 16041887) B16041887
theorem B1468691 : Blo 191804 1468691 := bstep (se 1 (by rfl) ⟨1101518, by rfl⟩ : syracuseStep 1468691 = 2203037) B2203037
theorem B5007865 : Blo 191804 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B289727 : Blo 191804 289727 := bstep (se 1 (by rfl) ⟨217295, by rfl⟩ : syracuseStep 289727 = 434591) B434591
theorem B15910015 : Blo 191804 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B7129727 : Blo 191804 7129727 := bstep (se 1 (by rfl) ⟨5347295, by rfl⟩ : syracuseStep 7129727 = 10694591) B10694591
theorem B6677153 : Blo 191804 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B979127 : Blo 191804 979127 := bstep (se 1 (by rfl) ⟨734345, by rfl⟩ : syracuseStep 979127 = 1468691) B1468691
theorem B193151 : Blo 191804 193151 := bstep (se 1 (by rfl) ⟨144863, by rfl⟩ : syracuseStep 193151 = 289727) B289727
theorem B4753151 : Blo 191804 4753151 := bstep (se 1 (by rfl) ⟨3564863, by rfl⟩ : syracuseStep 4753151 = 7129727) B7129727
theorem B21213353 : Blo 191804 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B4451435 : Blo 191804 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B652751 : Blo 191804 652751 := bstep (se 1 (by rfl) ⟨489563, by rfl⟩ : syracuseStep 652751 = 979127) B979127
theorem B435167 : Blo 191804 435167 := bstep (se 1 (by rfl) ⟨326375, by rfl⟩ : syracuseStep 435167 = 652751) B652751
theorem B2967623 : Blo 191804 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B14142235 : Blo 191804 14142235 := bstep (se 1 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 14142235 = 21213353) B21213353
theorem B3168767 : Blo 191804 3168767 := bstep (se 1 (by rfl) ⟨2376575, by rfl⟩ : syracuseStep 3168767 = 4753151) B4753151
theorem B1978415 : Blo 191804 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B18856313 : Blo 191804 18856313 := bstep (se 2 (by rfl) ⟨7071117, by rfl⟩ : syracuseStep 18856313 = 14142235) B14142235
theorem B290111 : Blo 191804 290111 := bstep (se 1 (by rfl) ⟨217583, by rfl⟩ : syracuseStep 290111 = 435167) B435167
theorem B8450045 : Blo 191804 8450045 := bstep (se 3 (by rfl) ⟨1584383, by rfl⟩ : syracuseStep 8450045 = 3168767) B3168767
theorem B1318943 : Blo 191804 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B12570875 : Blo 191804 12570875 := bstep (se 1 (by rfl) ⟨9428156, by rfl⟩ : syracuseStep 12570875 = 18856313) B18856313
theorem B193407 : Blo 191804 193407 := bstep (se 1 (by rfl) ⟨145055, by rfl⟩ : syracuseStep 193407 = 290111) B290111
theorem B5633363 : Blo 191804 5633363 := bstep (se 1 (by rfl) ⟨4225022, by rfl⟩ : syracuseStep 5633363 = 8450045) B8450045
theorem B3755575 : Blo 191804 3755575 := bstep (se 1 (by rfl) ⟨2816681, by rfl⟩ : syracuseStep 3755575 = 5633363) B5633363
theorem B8380583 : Blo 191804 8380583 := bstep (se 1 (by rfl) ⟨6285437, by rfl⟩ : syracuseStep 8380583 = 12570875) B12570875
theorem B879295 : Blo 191804 879295 := bstep (se 1 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 879295 = 1318943) B1318943
theorem B5587055 : Blo 191804 5587055 := bstep (se 1 (by rfl) ⟨4190291, by rfl⟩ : syracuseStep 5587055 = 8380583) B8380583
theorem B1172393 : Blo 191804 1172393 := bstep (se 2 (by rfl) ⟨439647, by rfl⟩ : syracuseStep 1172393 = 879295) B879295
theorem B5007433 : Blo 191804 5007433 := bstep (se 2 (by rfl) ⟨1877787, by rfl⟩ : syracuseStep 5007433 = 3755575) B3755575
theorem B3724703 : Blo 191804 3724703 := bstep (se 1 (by rfl) ⟨2793527, by rfl⟩ : syracuseStep 3724703 = 5587055) B5587055
theorem B6676577 : Blo 191804 6676577 := bstep (se 2 (by rfl) ⟨2503716, by rfl⟩ : syracuseStep 6676577 = 5007433) B5007433
theorem B781595 : Blo 191804 781595 := bstep (se 1 (by rfl) ⟨586196, by rfl⟩ : syracuseStep 781595 = 1172393) B1172393
theorem B2483135 : Blo 191804 2483135 := bstep (se 1 (by rfl) ⟨1862351, by rfl⟩ : syracuseStep 2483135 = 3724703) B3724703
theorem B4451051 : Blo 191804 4451051 := bstep (se 1 (by rfl) ⟨3338288, by rfl⟩ : syracuseStep 4451051 = 6676577) B6676577
theorem B521063 : Blo 191804 521063 := bstep (se 1 (by rfl) ⟨390797, by rfl⟩ : syracuseStep 521063 = 781595) B781595
theorem B1655423 : Blo 191804 1655423 := bstep (se 1 (by rfl) ⟨1241567, by rfl⟩ : syracuseStep 1655423 = 2483135) B2483135
theorem B2967367 : Blo 191804 2967367 := bstep (se 1 (by rfl) ⟨2225525, by rfl⟩ : syracuseStep 2967367 = 4451051) B4451051
theorem B347375 : Blo 191804 347375 := bstep (se 1 (by rfl) ⟨260531, by rfl⟩ : syracuseStep 347375 = 521063) B521063
theorem B231583 : Blo 191804 231583 := bstep (se 1 (by rfl) ⟨173687, by rfl⟩ : syracuseStep 231583 = 347375) B347375
theorem B1103615 : Blo 191804 1103615 := bstep (se 1 (by rfl) ⟨827711, by rfl⟩ : syracuseStep 1103615 = 1655423) B1655423
theorem B3956489 : Blo 191804 3956489 := bstep (se 2 (by rfl) ⟨1483683, by rfl⟩ : syracuseStep 3956489 = 2967367) B2967367
theorem B308777 : Blo 191804 308777 := bstep (se 2 (by rfl) ⟨115791, by rfl⟩ : syracuseStep 308777 = 231583) B231583
theorem B735743 : Blo 191804 735743 := bstep (se 1 (by rfl) ⟨551807, by rfl⟩ : syracuseStep 735743 = 1103615) B1103615
theorem B2637659 : Blo 191804 2637659 := bstep (se 1 (by rfl) ⟨1978244, by rfl⟩ : syracuseStep 2637659 = 3956489) B3956489
theorem B3293621 : Blo 191804 3293621 := bstep (se 5 (by rfl) ⟨154388, by rfl⟩ : syracuseStep 3293621 = 308777) B308777
theorem B1758439 : Blo 191804 1758439 := bstep (se 1 (by rfl) ⟨1318829, by rfl⟩ : syracuseStep 1758439 = 2637659) B2637659
theorem B490495 : Blo 191804 490495 := bstep (se 1 (by rfl) ⟨367871, by rfl⟩ : syracuseStep 490495 = 735743) B735743
theorem B2195747 : Blo 191804 2195747 := bstep (se 1 (by rfl) ⟨1646810, by rfl⟩ : syracuseStep 2195747 = 3293621) B3293621
theorem B2344585 : Blo 191804 2344585 := bstep (se 2 (by rfl) ⟨879219, by rfl⟩ : syracuseStep 2344585 = 1758439) B1758439
theorem B653993 : Blo 191804 653993 := bstep (se 2 (by rfl) ⟨245247, by rfl⟩ : syracuseStep 653993 = 490495) B490495
theorem B435995 : Blo 191804 435995 := bstep (se 1 (by rfl) ⟨326996, by rfl⟩ : syracuseStep 435995 = 653993) B653993
theorem B3126113 : Blo 191804 3126113 := bstep (se 2 (by rfl) ⟨1172292, by rfl⟩ : syracuseStep 3126113 = 2344585) B2344585
theorem B1463831 : Blo 191804 1463831 := bstep (se 1 (by rfl) ⟨1097873, by rfl⟩ : syracuseStep 1463831 = 2195747) B2195747
theorem B2084075 : Blo 191804 2084075 := bstep (se 1 (by rfl) ⟨1563056, by rfl⟩ : syracuseStep 2084075 = 3126113) B3126113
theorem B975887 : Blo 191804 975887 := bstep (se 1 (by rfl) ⟨731915, by rfl⟩ : syracuseStep 975887 = 1463831) B1463831
theorem B290663 : Blo 191804 290663 := bstep (se 1 (by rfl) ⟨217997, by rfl⟩ : syracuseStep 290663 = 435995) B435995
theorem B1389383 : Blo 191804 1389383 := bstep (se 1 (by rfl) ⟨1042037, by rfl⟩ : syracuseStep 1389383 = 2084075) B2084075
theorem B650591 : Blo 191804 650591 := bstep (se 1 (by rfl) ⟨487943, by rfl⟩ : syracuseStep 650591 = 975887) B975887
theorem B193775 : Blo 191804 193775 := bstep (se 1 (by rfl) ⟨145331, by rfl⟩ : syracuseStep 193775 = 290663) B290663
theorem B433727 : Blo 191804 433727 := bstep (se 1 (by rfl) ⟨325295, by rfl⟩ : syracuseStep 433727 = 650591) B650591
theorem B926255 : Blo 191804 926255 := bstep (se 1 (by rfl) ⟨694691, by rfl⟩ : syracuseStep 926255 = 1389383) B1389383
theorem B2470013 : Blo 191804 2470013 := bstep (se 3 (by rfl) ⟨463127, by rfl⟩ : syracuseStep 2470013 = 926255) B926255
theorem B289151 : Blo 191804 289151 := bstep (se 1 (by rfl) ⟨216863, by rfl⟩ : syracuseStep 289151 = 433727) B433727
theorem B1646675 : Blo 191804 1646675 := bstep (se 1 (by rfl) ⟨1235006, by rfl⟩ : syracuseStep 1646675 = 2470013) B2470013
theorem B192767 : Blo 191804 192767 := bstep (se 1 (by rfl) ⟨144575, by rfl⟩ : syracuseStep 192767 = 289151) B289151
theorem B1097783 : Blo 191804 1097783 := bstep (se 1 (by rfl) ⟨823337, by rfl⟩ : syracuseStep 1097783 = 1646675) B1646675
theorem B731855 : Blo 191804 731855 := bstep (se 1 (by rfl) ⟨548891, by rfl⟩ : syracuseStep 731855 = 1097783) B1097783
theorem B487903 : Blo 191804 487903 := bstep (se 1 (by rfl) ⟨365927, by rfl⟩ : syracuseStep 487903 = 731855) B731855
theorem B650537 : Blo 191804 650537 := bstep (se 2 (by rfl) ⟨243951, by rfl⟩ : syracuseStep 650537 = 487903) B487903
theorem B433691 : Blo 191804 433691 := bstep (se 1 (by rfl) ⟨325268, by rfl⟩ : syracuseStep 433691 = 650537) B650537
theorem B289127 : Blo 191804 289127 := bstep (se 1 (by rfl) ⟨216845, by rfl⟩ : syracuseStep 289127 = 433691) B433691
theorem B192751 : Blo 191804 192751 := bstep (se 1 (by rfl) ⟨144563, by rfl⟩ : syracuseStep 192751 = 289127) B289127

theorem C0 (j : ℕ) (h1 : 47951 ≤ j) (h2 : j ≤ 48650) : Blo 191804 (4 * j + 3) := by
  interval_cases j
  · exact B191807
  · exact B191811
  · exact B191815
  · exact B191819
  · exact B191823
  · exact B191827
  · exact B191831
  · exact B191835
  · exact B191839
  · exact B191843
  · exact B191847
  · exact B191851
  · exact B191855
  · exact B191859
  · exact B191863
  · exact B191867
  · exact B191871
  · exact B191875
  · exact B191879
  · exact B191883
  · exact B191887
  · exact B191891
  · exact B191895
  · exact B191899
  · exact B191903
  · exact B191907
  · exact B191911
  · exact B191915
  · exact B191919
  · exact B191923
  · exact B191927
  · exact B191931
  · exact B191935
  · exact B191939
  · exact B191943
  · exact B191947
  · exact B191951
  · exact B191955
  · exact B191959
  · exact B191963
  · exact B191967
  · exact B191971
  · exact B191975
  · exact B191979
  · exact B191983
  · exact B191987
  · exact B191991
  · exact B191995
  · exact B191999
  · exact B192003
  · exact B192007
  · exact B192011
  · exact B192015
  · exact B192019
  · exact B192023
  · exact B192027
  · exact B192031
  · exact B192035
  · exact B192039
  · exact B192043
  · exact B192047
  · exact B192051
  · exact B192055
  · exact B192059
  · exact B192063
  · exact B192067
  · exact B192071
  · exact B192075
  · exact B192079
  · exact B192083
  · exact B192087
  · exact B192091
  · exact B192095
  · exact B192099
  · exact B192103
  · exact B192107
  · exact B192111
  · exact B192115
  · exact B192119
  · exact B192123
  · exact B192127
  · exact B192131
  · exact B192135
  · exact B192139
  · exact B192143
  · exact B192147
  · exact B192151
  · exact B192155
  · exact B192159
  · exact B192163
  · exact B192167
  · exact B192171
  · exact B192175
  · exact B192179
  · exact B192183
  · exact B192187
  · exact B192191
  · exact B192195
  · exact B192199
  · exact B192203
  · exact B192207
  · exact B192211
  · exact B192215
  · exact B192219
  · exact B192223
  · exact B192227
  · exact B192231
  · exact B192235
  · exact B192239
  · exact B192243
  · exact B192247
  · exact B192251
  · exact B192255
  · exact B192259
  · exact B192263
  · exact B192267
  · exact B192271
  · exact B192275
  · exact B192279
  · exact B192283
  · exact B192287
  · exact B192291
  · exact B192295
  · exact B192299
  · exact B192303
  · exact B192307
  · exact B192311
  · exact B192315
  · exact B192319
  · exact B192323
  · exact B192327
  · exact B192331
  · exact B192335
  · exact B192339
  · exact B192343
  · exact B192347
  · exact B192351
  · exact B192355
  · exact B192359
  · exact B192363
  · exact B192367
  · exact B192371
  · exact B192375
  · exact B192379
  · exact B192383
  · exact B192387
  · exact B192391
  · exact B192395
  · exact B192399
  · exact B192403
  · exact B192407
  · exact B192411
  · exact B192415
  · exact B192419
  · exact B192423
  · exact B192427
  · exact B192431
  · exact B192435
  · exact B192439
  · exact B192443
  · exact B192447
  · exact B192451
  · exact B192455
  · exact B192459
  · exact B192463
  · exact B192467
  · exact B192471
  · exact B192475
  · exact B192479
  · exact B192483
  · exact B192487
  · exact B192491
  · exact B192495
  · exact B192499
  · exact B192503
  · exact B192507
  · exact B192511
  · exact B192515
  · exact B192519
  · exact B192523
  · exact B192527
  · exact B192531
  · exact B192535
  · exact B192539
  · exact B192543
  · exact B192547
  · exact B192551
  · exact B192555
  · exact B192559
  · exact B192563
  · exact B192567
  · exact B192571
  · exact B192575
  · exact B192579
  · exact B192583
  · exact B192587
  · exact B192591
  · exact B192595
  · exact B192599
  · exact B192603
  · exact B192607
  · exact B192611
  · exact B192615
  · exact B192619
  · exact B192623
  · exact B192627
  · exact B192631
  · exact B192635
  · exact B192639
  · exact B192643
  · exact B192647
  · exact B192651
  · exact B192655
  · exact B192659
  · exact B192663
  · exact B192667
  · exact B192671
  · exact B192675
  · exact B192679
  · exact B192683
  · exact B192687
  · exact B192691
  · exact B192695
  · exact B192699
  · exact B192703
  · exact B192707
  · exact B192711
  · exact B192715
  · exact B192719
  · exact B192723
  · exact B192727
  · exact B192731
  · exact B192735
  · exact B192739
  · exact B192743
  · exact B192747
  · exact B192751
  · exact B192755
  · exact B192759
  · exact B192763
  · exact B192767
  · exact B192771
  · exact B192775
  · exact B192779
  · exact B192783
  · exact B192787
  · exact B192791
  · exact B192795
  · exact B192799
  · exact B192803
  · exact B192807
  · exact B192811
  · exact B192815
  · exact B192819
  · exact B192823
  · exact B192827
  · exact B192831
  · exact B192835
  · exact B192839
  · exact B192843
  · exact B192847
  · exact B192851
  · exact B192855
  · exact B192859
  · exact B192863
  · exact B192867
  · exact B192871
  · exact B192875
  · exact B192879
  · exact B192883
  · exact B192887
  · exact B192891
  · exact B192895
  · exact B192899
  · exact B192903
  · exact B192907
  · exact B192911
  · exact B192915
  · exact B192919
  · exact B192923
  · exact B192927
  · exact B192931
  · exact B192935
  · exact B192939
  · exact B192943
  · exact B192947
  · exact B192951
  · exact B192955
  · exact B192959
  · exact B192963
  · exact B192967
  · exact B192971
  · exact B192975
  · exact B192979
  · exact B192983
  · exact B192987
  · exact B192991
  · exact B192995
  · exact B192999
  · exact B193003
  · exact B193007
  · exact B193011
  · exact B193015
  · exact B193019
  · exact B193023
  · exact B193027
  · exact B193031
  · exact B193035
  · exact B193039
  · exact B193043
  · exact B193047
  · exact B193051
  · exact B193055
  · exact B193059
  · exact B193063
  · exact B193067
  · exact B193071
  · exact B193075
  · exact B193079
  · exact B193083
  · exact B193087
  · exact B193091
  · exact B193095
  · exact B193099
  · exact B193103
  · exact B193107
  · exact B193111
  · exact B193115
  · exact B193119
  · exact B193123
  · exact B193127
  · exact B193131
  · exact B193135
  · exact B193139
  · exact B193143
  · exact B193147
  · exact B193151
  · exact B193155
  · exact B193159
  · exact B193163
  · exact B193167
  · exact B193171
  · exact B193175
  · exact B193179
  · exact B193183
  · exact B193187
  · exact B193191
  · exact B193195
  · exact B193199
  · exact B193203
  · exact B193207
  · exact B193211
  · exact B193215
  · exact B193219
  · exact B193223
  · exact B193227
  · exact B193231
  · exact B193235
  · exact B193239
  · exact B193243
  · exact B193247
  · exact B193251
  · exact B193255
  · exact B193259
  · exact B193263
  · exact B193267
  · exact B193271
  · exact B193275
  · exact B193279
  · exact B193283
  · exact B193287
  · exact B193291
  · exact B193295
  · exact B193299
  · exact B193303
  · exact B193307
  · exact B193311
  · exact B193315
  · exact B193319
  · exact B193323
  · exact B193327
  · exact B193331
  · exact B193335
  · exact B193339
  · exact B193343
  · exact B193347
  · exact B193351
  · exact B193355
  · exact B193359
  · exact B193363
  · exact B193367
  · exact B193371
  · exact B193375
  · exact B193379
  · exact B193383
  · exact B193387
  · exact B193391
  · exact B193395
  · exact B193399
  · exact B193403
  · exact B193407
  · exact B193411
  · exact B193415
  · exact B193419
  · exact B193423
  · exact B193427
  · exact B193431
  · exact B193435
  · exact B193439
  · exact B193443
  · exact B193447
  · exact B193451
  · exact B193455
  · exact B193459
  · exact B193463
  · exact B193467
  · exact B193471
  · exact B193475
  · exact B193479
  · exact B193483
  · exact B193487
  · exact B193491
  · exact B193495
  · exact B193499
  · exact B193503
  · exact B193507
  · exact B193511
  · exact B193515
  · exact B193519
  · exact B193523
  · exact B193527
  · exact B193531
  · exact B193535
  · exact B193539
  · exact B193543
  · exact B193547
  · exact B193551
  · exact B193555
  · exact B193559
  · exact B193563
  · exact B193567
  · exact B193571
  · exact B193575
  · exact B193579
  · exact B193583
  · exact B193587
  · exact B193591
  · exact B193595
  · exact B193599
  · exact B193603
  · exact B193607
  · exact B193611
  · exact B193615
  · exact B193619
  · exact B193623
  · exact B193627
  · exact B193631
  · exact B193635
  · exact B193639
  · exact B193643
  · exact B193647
  · exact B193651
  · exact B193655
  · exact B193659
  · exact B193663
  · exact B193667
  · exact B193671
  · exact B193675
  · exact B193679
  · exact B193683
  · exact B193687
  · exact B193691
  · exact B193695
  · exact B193699
  · exact B193703
  · exact B193707
  · exact B193711
  · exact B193715
  · exact B193719
  · exact B193723
  · exact B193727
  · exact B193731
  · exact B193735
  · exact B193739
  · exact B193743
  · exact B193747
  · exact B193751
  · exact B193755
  · exact B193759
  · exact B193763
  · exact B193767
  · exact B193771
  · exact B193775
  · exact B193779
  · exact B193783
  · exact B193787
  · exact B193791
  · exact B193795
  · exact B193799
  · exact B193803
  · exact B193807
  · exact B193811
  · exact B193815
  · exact B193819
  · exact B193823
  · exact B193827
  · exact B193831
  · exact B193835
  · exact B193839
  · exact B193843
  · exact B193847
  · exact B193851
  · exact B193855
  · exact B193859
  · exact B193863
  · exact B193867
  · exact B193871
  · exact B193875
  · exact B193879
  · exact B193883
  · exact B193887
  · exact B193891
  · exact B193895
  · exact B193899
  · exact B193903
  · exact B193907
  · exact B193911
  · exact B193915
  · exact B193919
  · exact B193923
  · exact B193927
  · exact B193931
  · exact B193935
  · exact B193939
  · exact B193943
  · exact B193947
  · exact B193951
  · exact B193955
  · exact B193959
  · exact B193963
  · exact B193967
  · exact B193971
  · exact B193975
  · exact B193979
  · exact B193983
  · exact B193987
  · exact B193991
  · exact B193995
  · exact B193999
  · exact B194003
  · exact B194007
  · exact B194011
  · exact B194015
  · exact B194019
  · exact B194023
  · exact B194027
  · exact B194031
  · exact B194035
  · exact B194039
  · exact B194043
  · exact B194047
  · exact B194051
  · exact B194055
  · exact B194059
  · exact B194063
  · exact B194067
  · exact B194071
  · exact B194075
  · exact B194079
  · exact B194083
  · exact B194087
  · exact B194091
  · exact B194095
  · exact B194099
  · exact B194103
  · exact B194107
  · exact B194111
  · exact B194115
  · exact B194119
  · exact B194123
  · exact B194127
  · exact B194131
  · exact B194135
  · exact B194139
  · exact B194143
  · exact B194147
  · exact B194151
  · exact B194155
  · exact B194159
  · exact B194163
  · exact B194167
  · exact B194171
  · exact B194175
  · exact B194179
  · exact B194183
  · exact B194187
  · exact B194191
  · exact B194195
  · exact B194199
  · exact B194203
  · exact B194207
  · exact B194211
  · exact B194215
  · exact B194219
  · exact B194223
  · exact B194227
  · exact B194231
  · exact B194235
  · exact B194239
  · exact B194243
  · exact B194247
  · exact B194251
  · exact B194255
  · exact B194259
  · exact B194263
  · exact B194267
  · exact B194271
  · exact B194275
  · exact B194279
  · exact B194283
  · exact B194287
  · exact B194291
  · exact B194295
  · exact B194299
  · exact B194303
  · exact B194307
  · exact B194311
  · exact B194315
  · exact B194319
  · exact B194323
  · exact B194327
  · exact B194331
  · exact B194335
  · exact B194339
  · exact B194343
  · exact B194347
  · exact B194351
  · exact B194355
  · exact B194359
  · exact B194363
  · exact B194367
  · exact B194371
  · exact B194375
  · exact B194379
  · exact B194383
  · exact B194387
  · exact B194391
  · exact B194395
  · exact B194399
  · exact B194403
  · exact B194407
  · exact B194411
  · exact B194415
  · exact B194419
  · exact B194423
  · exact B194427
  · exact B194431
  · exact B194435
  · exact B194439
  · exact B194443
  · exact B194447
  · exact B194451
  · exact B194455
  · exact B194459
  · exact B194463
  · exact B194467
  · exact B194471
  · exact B194475
  · exact B194479
  · exact B194483
  · exact B194487
  · exact B194491
  · exact B194495
  · exact B194499
  · exact B194503
  · exact B194507
  · exact B194511
  · exact B194515
  · exact B194519
  · exact B194523
  · exact B194527
  · exact B194531
  · exact B194535
  · exact B194539
  · exact B194543
  · exact B194547
  · exact B194551
  · exact B194555
  · exact B194559
  · exact B194563
  · exact B194567
  · exact B194571
  · exact B194575
  · exact B194579
  · exact B194583
  · exact B194587
  · exact B194591
  · exact B194595
  · exact B194599
  · exact B194603

theorem C1 (j : ℕ) (h1 : 48651 ≤ j) (h2 : j ≤ 48950) : Blo 191804 (4 * j + 3) := by
  interval_cases j
  · exact B194607
  · exact B194611
  · exact B194615
  · exact B194619
  · exact B194623
  · exact B194627
  · exact B194631
  · exact B194635
  · exact B194639
  · exact B194643
  · exact B194647
  · exact B194651
  · exact B194655
  · exact B194659
  · exact B194663
  · exact B194667
  · exact B194671
  · exact B194675
  · exact B194679
  · exact B194683
  · exact B194687
  · exact B194691
  · exact B194695
  · exact B194699
  · exact B194703
  · exact B194707
  · exact B194711
  · exact B194715
  · exact B194719
  · exact B194723
  · exact B194727
  · exact B194731
  · exact B194735
  · exact B194739
  · exact B194743
  · exact B194747
  · exact B194751
  · exact B194755
  · exact B194759
  · exact B194763
  · exact B194767
  · exact B194771
  · exact B194775
  · exact B194779
  · exact B194783
  · exact B194787
  · exact B194791
  · exact B194795
  · exact B194799
  · exact B194803
  · exact B194807
  · exact B194811
  · exact B194815
  · exact B194819
  · exact B194823
  · exact B194827
  · exact B194831
  · exact B194835
  · exact B194839
  · exact B194843
  · exact B194847
  · exact B194851
  · exact B194855
  · exact B194859
  · exact B194863
  · exact B194867
  · exact B194871
  · exact B194875
  · exact B194879
  · exact B194883
  · exact B194887
  · exact B194891
  · exact B194895
  · exact B194899
  · exact B194903
  · exact B194907
  · exact B194911
  · exact B194915
  · exact B194919
  · exact B194923
  · exact B194927
  · exact B194931
  · exact B194935
  · exact B194939
  · exact B194943
  · exact B194947
  · exact B194951
  · exact B194955
  · exact B194959
  · exact B194963
  · exact B194967
  · exact B194971
  · exact B194975
  · exact B194979
  · exact B194983
  · exact B194987
  · exact B194991
  · exact B194995
  · exact B194999
  · exact B195003
  · exact B195007
  · exact B195011
  · exact B195015
  · exact B195019
  · exact B195023
  · exact B195027
  · exact B195031
  · exact B195035
  · exact B195039
  · exact B195043
  · exact B195047
  · exact B195051
  · exact B195055
  · exact B195059
  · exact B195063
  · exact B195067
  · exact B195071
  · exact B195075
  · exact B195079
  · exact B195083
  · exact B195087
  · exact B195091
  · exact B195095
  · exact B195099
  · exact B195103
  · exact B195107
  · exact B195111
  · exact B195115
  · exact B195119
  · exact B195123
  · exact B195127
  · exact B195131
  · exact B195135
  · exact B195139
  · exact B195143
  · exact B195147
  · exact B195151
  · exact B195155
  · exact B195159
  · exact B195163
  · exact B195167
  · exact B195171
  · exact B195175
  · exact B195179
  · exact B195183
  · exact B195187
  · exact B195191
  · exact B195195
  · exact B195199
  · exact B195203
  · exact B195207
  · exact B195211
  · exact B195215
  · exact B195219
  · exact B195223
  · exact B195227
  · exact B195231
  · exact B195235
  · exact B195239
  · exact B195243
  · exact B195247
  · exact B195251
  · exact B195255
  · exact B195259
  · exact B195263
  · exact B195267
  · exact B195271
  · exact B195275
  · exact B195279
  · exact B195283
  · exact B195287
  · exact B195291
  · exact B195295
  · exact B195299
  · exact B195303
  · exact B195307
  · exact B195311
  · exact B195315
  · exact B195319
  · exact B195323
  · exact B195327
  · exact B195331
  · exact B195335
  · exact B195339
  · exact B195343
  · exact B195347
  · exact B195351
  · exact B195355
  · exact B195359
  · exact B195363
  · exact B195367
  · exact B195371
  · exact B195375
  · exact B195379
  · exact B195383
  · exact B195387
  · exact B195391
  · exact B195395
  · exact B195399
  · exact B195403
  · exact B195407
  · exact B195411
  · exact B195415
  · exact B195419
  · exact B195423
  · exact B195427
  · exact B195431
  · exact B195435
  · exact B195439
  · exact B195443
  · exact B195447
  · exact B195451
  · exact B195455
  · exact B195459
  · exact B195463
  · exact B195467
  · exact B195471
  · exact B195475
  · exact B195479
  · exact B195483
  · exact B195487
  · exact B195491
  · exact B195495
  · exact B195499
  · exact B195503
  · exact B195507
  · exact B195511
  · exact B195515
  · exact B195519
  · exact B195523
  · exact B195527
  · exact B195531
  · exact B195535
  · exact B195539
  · exact B195543
  · exact B195547
  · exact B195551
  · exact B195555
  · exact B195559
  · exact B195563
  · exact B195567
  · exact B195571
  · exact B195575
  · exact B195579
  · exact B195583
  · exact B195587
  · exact B195591
  · exact B195595
  · exact B195599
  · exact B195603
  · exact B195607
  · exact B195611
  · exact B195615
  · exact B195619
  · exact B195623
  · exact B195627
  · exact B195631
  · exact B195635
  · exact B195639
  · exact B195643
  · exact B195647
  · exact B195651
  · exact B195655
  · exact B195659
  · exact B195663
  · exact B195667
  · exact B195671
  · exact B195675
  · exact B195679
  · exact B195683
  · exact B195687
  · exact B195691
  · exact B195695
  · exact B195699
  · exact B195703
  · exact B195707
  · exact B195711
  · exact B195715
  · exact B195719
  · exact B195723
  · exact B195727
  · exact B195731
  · exact B195735
  · exact B195739
  · exact B195743
  · exact B195747
  · exact B195751
  · exact B195755
  · exact B195759
  · exact B195763
  · exact B195767
  · exact B195771
  · exact B195775
  · exact B195779
  · exact B195783
  · exact B195787
  · exact B195791
  · exact B195795
  · exact B195799
  · exact B195803

theorem solution (m : ℕ) (hlo : 191804 ≤ m) (hhi : m ≤ 195804) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 47951 ≤ j := by omega
    have hj2 : j ≤ 48950 := by omega
    have hb : Blo 191804 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 48651 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
