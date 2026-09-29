-- Prove2me | solution 1 for syracuse_descends_range_259821_263821
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:44:07.95439+00:00
-- url     : https://prove2.me/submissions/e2c05fff-020a-43fc-98bd-1e2d89f10473

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


theorem B393221 : Blo 259821 393221 := bbase (se 4 (by rfl) ⟨36864, by rfl⟩ : syracuseStep 393221 = 73729) (by norm_num)
theorem B294925 : Blo 259821 294925 := bbase (se 3 (by rfl) ⟨55298, by rfl⟩ : syracuseStep 294925 = 110597) (by norm_num)
theorem B393245 : Blo 259821 393245 := bbase (se 3 (by rfl) ⟨73733, by rfl⟩ : syracuseStep 393245 = 147467) (by norm_num)
theorem B294961 : Blo 259821 294961 := bbase (se 2 (by rfl) ⟨110610, by rfl⟩ : syracuseStep 294961 = 221221) (by norm_num)
theorem B884789 : Blo 259821 884789 := bbase (se 5 (by rfl) ⟨41474, by rfl⟩ : syracuseStep 884789 = 82949) (by norm_num)
theorem B589877 : Blo 259821 589877 := bbase (se 5 (by rfl) ⟨27650, by rfl⟩ : syracuseStep 589877 = 55301) (by norm_num)
theorem B393269 : Blo 259821 393269 := bbase (se 5 (by rfl) ⟨18434, by rfl⟩ : syracuseStep 393269 = 36869) (by norm_num)
theorem B393293 : Blo 259821 393293 := bbase (se 3 (by rfl) ⟨73742, by rfl⟩ : syracuseStep 393293 = 147485) (by norm_num)
theorem B294997 : Blo 259821 294997 := bbase (se 8 (by rfl) ⟨1728, by rfl⟩ : syracuseStep 294997 = 3457) (by norm_num)
theorem B393317 : Blo 259821 393317 := bbase (se 4 (by rfl) ⟨36873, by rfl⟩ : syracuseStep 393317 = 73747) (by norm_num)
theorem B295033 : Blo 259821 295033 := bbase (se 2 (by rfl) ⟨110637, by rfl⟩ : syracuseStep 295033 = 221275) (by norm_num)
theorem B589949 : Blo 259821 589949 := bbase (se 3 (by rfl) ⟨110615, by rfl⟩ : syracuseStep 589949 = 221231) (by norm_num)
theorem B393341 : Blo 259821 393341 := bbase (se 3 (by rfl) ⟨73751, by rfl⟩ : syracuseStep 393341 = 147503) (by norm_num)
theorem B393365 : Blo 259821 393365 := bbase (se 6 (by rfl) ⟨9219, by rfl⟩ : syracuseStep 393365 = 18439) (by norm_num)
theorem B295069 : Blo 259821 295069 := bbase (se 3 (by rfl) ⟨55325, by rfl⟩ : syracuseStep 295069 = 110651) (by norm_num)
theorem B393389 : Blo 259821 393389 := bbase (se 3 (by rfl) ⟨73760, by rfl⟩ : syracuseStep 393389 = 147521) (by norm_num)
theorem B295105 : Blo 259821 295105 := bbase (se 2 (by rfl) ⟨110664, by rfl⟩ : syracuseStep 295105 = 221329) (by norm_num)
theorem B590021 : Blo 259821 590021 := bbase (se 4 (by rfl) ⟨55314, by rfl⟩ : syracuseStep 590021 = 110629) (by norm_num)
theorem B393413 : Blo 259821 393413 := bbase (se 4 (by rfl) ⟨36882, by rfl⟩ : syracuseStep 393413 = 73765) (by norm_num)
theorem B393437 : Blo 259821 393437 := bbase (se 3 (by rfl) ⟨73769, by rfl⟩ : syracuseStep 393437 = 147539) (by norm_num)
theorem B295141 : Blo 259821 295141 := bbase (se 4 (by rfl) ⟨27669, by rfl⟩ : syracuseStep 295141 = 55339) (by norm_num)
theorem B557293 : Blo 259821 557293 := bbase (se 3 (by rfl) ⟨104492, by rfl⟩ : syracuseStep 557293 = 208985) (by norm_num)
theorem B393461 : Blo 259821 393461 := bbase (se 5 (by rfl) ⟨18443, by rfl⟩ : syracuseStep 393461 = 36887) (by norm_num)
theorem B2162933 : Blo 259821 2162933 := bbase (se 5 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 2162933 = 202775) (by norm_num)
theorem B295169 : Blo 259821 295169 := bbase (se 2 (by rfl) ⟨110688, by rfl⟩ : syracuseStep 295169 = 221377) (by norm_num)
theorem B295177 : Blo 259821 295177 := bbase (se 2 (by rfl) ⟨110691, by rfl⟩ : syracuseStep 295177 = 221383) (by norm_num)
theorem B590093 : Blo 259821 590093 := bbase (se 3 (by rfl) ⟨110642, by rfl⟩ : syracuseStep 590093 = 221285) (by norm_num)
theorem B393485 : Blo 259821 393485 := bbase (se 3 (by rfl) ⟨73778, by rfl⟩ : syracuseStep 393485 = 147557) (by norm_num)
theorem B393509 : Blo 259821 393509 := bbase (se 4 (by rfl) ⟨36891, by rfl⟩ : syracuseStep 393509 = 73783) (by norm_num)
theorem B295213 : Blo 259821 295213 := bbase (se 3 (by rfl) ⟨55352, by rfl⟩ : syracuseStep 295213 = 110705) (by norm_num)
theorem B393533 : Blo 259821 393533 := bbase (se 3 (by rfl) ⟨73787, by rfl⟩ : syracuseStep 393533 = 147575) (by norm_num)
theorem B295249 : Blo 259821 295249 := bbase (se 2 (by rfl) ⟨110718, by rfl⟩ : syracuseStep 295249 = 221437) (by norm_num)
theorem B590165 : Blo 259821 590165 := bbase (se 10 (by rfl) ⟨864, by rfl⟩ : syracuseStep 590165 = 1729) (by norm_num)
theorem B393557 : Blo 259821 393557 := bbase (se 10 (by rfl) ⟨576, by rfl⟩ : syracuseStep 393557 = 1153) (by norm_num)
theorem B393581 : Blo 259821 393581 := bbase (se 3 (by rfl) ⟨73796, by rfl⟩ : syracuseStep 393581 = 147593) (by norm_num)
theorem B295285 : Blo 259821 295285 := bbase (se 5 (by rfl) ⟨13841, by rfl⟩ : syracuseStep 295285 = 27683) (by norm_num)
theorem B393605 : Blo 259821 393605 := bbase (se 4 (by rfl) ⟨36900, by rfl⟩ : syracuseStep 393605 = 73801) (by norm_num)
theorem B295321 : Blo 259821 295321 := bbase (se 2 (by rfl) ⟨110745, by rfl⟩ : syracuseStep 295321 = 221491) (by norm_num)
theorem B590237 : Blo 259821 590237 := bbase (se 3 (by rfl) ⟨110669, by rfl⟩ : syracuseStep 590237 = 221339) (by norm_num)
theorem B393629 : Blo 259821 393629 := bbase (se 3 (by rfl) ⟨73805, by rfl⟩ : syracuseStep 393629 = 147611) (by norm_num)
theorem B393653 : Blo 259821 393653 := bbase (se 5 (by rfl) ⟨18452, by rfl⟩ : syracuseStep 393653 = 36905) (by norm_num)
theorem B295357 : Blo 259821 295357 := bbase (se 3 (by rfl) ⟨55379, by rfl⟩ : syracuseStep 295357 = 110759) (by norm_num)
theorem B393677 : Blo 259821 393677 := bbase (se 3 (by rfl) ⟨73814, by rfl⟩ : syracuseStep 393677 = 147629) (by norm_num)
theorem B295393 : Blo 259821 295393 := bbase (se 2 (by rfl) ⟨110772, by rfl⟩ : syracuseStep 295393 = 221545) (by norm_num)
theorem B885221 : Blo 259821 885221 := bbase (se 4 (by rfl) ⟨82989, by rfl⟩ : syracuseStep 885221 = 165979) (by norm_num)
theorem B590309 : Blo 259821 590309 := bbase (se 4 (by rfl) ⟨55341, by rfl⟩ : syracuseStep 590309 = 110683) (by norm_num)
theorem B393701 : Blo 259821 393701 := bbase (se 4 (by rfl) ⟨36909, by rfl⟩ : syracuseStep 393701 = 73819) (by norm_num)
theorem B393725 : Blo 259821 393725 := bbase (se 3 (by rfl) ⟨73823, by rfl⟩ : syracuseStep 393725 = 147647) (by norm_num)
theorem B295429 : Blo 259821 295429 := bbase (se 4 (by rfl) ⟨27696, by rfl⟩ : syracuseStep 295429 = 55393) (by norm_num)
theorem B393749 : Blo 259821 393749 := bbase (se 6 (by rfl) ⟨9228, by rfl⟩ : syracuseStep 393749 = 18457) (by norm_num)
theorem B295465 : Blo 259821 295465 := bbase (se 2 (by rfl) ⟨110799, by rfl⟩ : syracuseStep 295465 = 221599) (by norm_num)
theorem B590381 : Blo 259821 590381 := bbase (se 3 (by rfl) ⟨110696, by rfl⟩ : syracuseStep 590381 = 221393) (by norm_num)
theorem B393773 : Blo 259821 393773 := bbase (se 3 (by rfl) ⟨73832, by rfl⟩ : syracuseStep 393773 = 147665) (by norm_num)
theorem B393797 : Blo 259821 393797 := bbase (se 4 (by rfl) ⟨36918, by rfl⟩ : syracuseStep 393797 = 73837) (by norm_num)
theorem B295501 : Blo 259821 295501 := bbase (se 3 (by rfl) ⟨55406, by rfl⟩ : syracuseStep 295501 = 110813) (by norm_num)
theorem B393821 : Blo 259821 393821 := bbase (se 3 (by rfl) ⟨73841, by rfl⟩ : syracuseStep 393821 = 147683) (by norm_num)
theorem B295529 : Blo 259821 295529 := bbase (se 2 (by rfl) ⟨110823, by rfl⟩ : syracuseStep 295529 = 221647) (by norm_num)
theorem B295537 : Blo 259821 295537 := bbase (se 2 (by rfl) ⟨110826, by rfl⟩ : syracuseStep 295537 = 221653) (by norm_num)
theorem B590453 : Blo 259821 590453 := bbase (se 5 (by rfl) ⟨27677, by rfl⟩ : syracuseStep 590453 = 55355) (by norm_num)
theorem B393845 : Blo 259821 393845 := bbase (se 5 (by rfl) ⟨18461, by rfl⟩ : syracuseStep 393845 = 36923) (by norm_num)
theorem B393869 : Blo 259821 393869 := bbase (se 3 (by rfl) ⟨73850, by rfl⟩ : syracuseStep 393869 = 147701) (by norm_num)
theorem B5374613 : Blo 259821 5374613 := bbase (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) (by norm_num)
theorem B295573 : Blo 259821 295573 := bbase (se 6 (by rfl) ⟨6927, by rfl⟩ : syracuseStep 295573 = 13855) (by norm_num)
theorem B393893 : Blo 259821 393893 := bbase (se 4 (by rfl) ⟨36927, by rfl⟩ : syracuseStep 393893 = 73855) (by norm_num)
theorem B295609 : Blo 259821 295609 := bbase (se 2 (by rfl) ⟨110853, by rfl⟩ : syracuseStep 295609 = 221707) (by norm_num)
theorem B590525 : Blo 259821 590525 := bbase (se 3 (by rfl) ⟨110723, by rfl⟩ : syracuseStep 590525 = 221447) (by norm_num)
theorem B393917 : Blo 259821 393917 := bbase (se 3 (by rfl) ⟨73859, by rfl⟩ : syracuseStep 393917 = 147719) (by norm_num)
theorem B393941 : Blo 259821 393941 := bbase (se 7 (by rfl) ⟨4616, by rfl⟩ : syracuseStep 393941 = 9233) (by norm_num)
theorem B295645 : Blo 259821 295645 := bbase (se 3 (by rfl) ⟨55433, by rfl⟩ : syracuseStep 295645 = 110867) (by norm_num)
theorem B393965 : Blo 259821 393965 := bbase (se 3 (by rfl) ⟨73868, by rfl⟩ : syracuseStep 393965 = 147737) (by norm_num)
theorem B295681 : Blo 259821 295681 := bbase (se 2 (by rfl) ⟨110880, by rfl⟩ : syracuseStep 295681 = 221761) (by norm_num)
theorem B590597 : Blo 259821 590597 := bbase (se 4 (by rfl) ⟨55368, by rfl⟩ : syracuseStep 590597 = 110737) (by norm_num)
theorem B393989 : Blo 259821 393989 := bbase (se 4 (by rfl) ⟨36936, by rfl⟩ : syracuseStep 393989 = 73873) (by norm_num)
theorem B394013 : Blo 259821 394013 := bbase (se 3 (by rfl) ⟨73877, by rfl⟩ : syracuseStep 394013 = 147755) (by norm_num)
theorem B295717 : Blo 259821 295717 := bbase (se 4 (by rfl) ⟨27723, by rfl⟩ : syracuseStep 295717 = 55447) (by norm_num)
theorem B394037 : Blo 259821 394037 := bbase (se 5 (by rfl) ⟨18470, by rfl⟩ : syracuseStep 394037 = 36941) (by norm_num)
theorem B295753 : Blo 259821 295753 := bbase (se 2 (by rfl) ⟨110907, by rfl⟩ : syracuseStep 295753 = 221815) (by norm_num)
theorem B590669 : Blo 259821 590669 := bbase (se 3 (by rfl) ⟨110750, by rfl⟩ : syracuseStep 590669 = 221501) (by norm_num)
theorem B394061 : Blo 259821 394061 := bbase (se 3 (by rfl) ⟨73886, by rfl⟩ : syracuseStep 394061 = 147773) (by norm_num)
theorem B394085 : Blo 259821 394085 := bbase (se 4 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 394085 = 73891) (by norm_num)
theorem B295789 : Blo 259821 295789 := bbase (se 3 (by rfl) ⟨55460, by rfl⟩ : syracuseStep 295789 = 110921) (by norm_num)
theorem B394109 : Blo 259821 394109 := bbase (se 3 (by rfl) ⟨73895, by rfl⟩ : syracuseStep 394109 = 147791) (by norm_num)
theorem B295825 : Blo 259821 295825 := bbase (se 2 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 295825 = 221869) (by norm_num)
theorem B885653 : Blo 259821 885653 := bbase (se 6 (by rfl) ⟨20757, by rfl⟩ : syracuseStep 885653 = 41515) (by norm_num)
theorem B590741 : Blo 259821 590741 := bbase (se 6 (by rfl) ⟨13845, by rfl⟩ : syracuseStep 590741 = 27691) (by norm_num)
theorem B394133 : Blo 259821 394133 := bbase (se 6 (by rfl) ⟨9237, by rfl⟩ : syracuseStep 394133 = 18475) (by norm_num)
theorem B394157 : Blo 259821 394157 := bbase (se 3 (by rfl) ⟨73904, by rfl⟩ : syracuseStep 394157 = 147809) (by norm_num)
theorem B295861 : Blo 259821 295861 := bbase (se 5 (by rfl) ⟨13868, by rfl⟩ : syracuseStep 295861 = 27737) (by norm_num)
theorem B394181 : Blo 259821 394181 := bbase (se 4 (by rfl) ⟨36954, by rfl⟩ : syracuseStep 394181 = 73909) (by norm_num)
theorem B295897 : Blo 259821 295897 := bbase (se 2 (by rfl) ⟨110961, by rfl⟩ : syracuseStep 295897 = 221923) (by norm_num)
theorem B590813 : Blo 259821 590813 := bbase (se 3 (by rfl) ⟨110777, by rfl⟩ : syracuseStep 590813 = 221555) (by norm_num)
theorem B394205 : Blo 259821 394205 := bbase (se 3 (by rfl) ⟨73913, by rfl⟩ : syracuseStep 394205 = 147827) (by norm_num)
theorem B394229 : Blo 259821 394229 := bbase (se 5 (by rfl) ⟨18479, by rfl⟩ : syracuseStep 394229 = 36959) (by norm_num)
theorem B295933 : Blo 259821 295933 := bbase (se 3 (by rfl) ⟨55487, by rfl⟩ : syracuseStep 295933 = 110975) (by norm_num)
theorem B394253 : Blo 259821 394253 := bbase (se 3 (by rfl) ⟨73922, by rfl⟩ : syracuseStep 394253 = 147845) (by norm_num)
theorem B295969 : Blo 259821 295969 := bbase (se 2 (by rfl) ⟨110988, by rfl⟩ : syracuseStep 295969 = 221977) (by norm_num)
theorem B590885 : Blo 259821 590885 := bbase (se 4 (by rfl) ⟨55395, by rfl⟩ : syracuseStep 590885 = 110791) (by norm_num)
theorem B394277 : Blo 259821 394277 := bbase (se 4 (by rfl) ⟨36963, by rfl⟩ : syracuseStep 394277 = 73927) (by norm_num)
theorem B394301 : Blo 259821 394301 := bbase (se 3 (by rfl) ⟨73931, by rfl⟩ : syracuseStep 394301 = 147863) (by norm_num)
theorem B296005 : Blo 259821 296005 := bbase (se 4 (by rfl) ⟨27750, by rfl⟩ : syracuseStep 296005 = 55501) (by norm_num)
theorem B2688085 : Blo 259821 2688085 := bbase (se 8 (by rfl) ⟨15750, by rfl⟩ : syracuseStep 2688085 = 31501) (by norm_num)
theorem B394325 : Blo 259821 394325 := bbase (se 8 (by rfl) ⟨2310, by rfl⟩ : syracuseStep 394325 = 4621) (by norm_num)
theorem B558181 : Blo 259821 558181 := bbase (se 4 (by rfl) ⟨52329, by rfl⟩ : syracuseStep 558181 = 104659) (by norm_num)
theorem B296041 : Blo 259821 296041 := bbase (se 2 (by rfl) ⟨111015, by rfl⟩ : syracuseStep 296041 = 222031) (by norm_num)
theorem B590957 : Blo 259821 590957 := bbase (se 3 (by rfl) ⟨110804, by rfl⟩ : syracuseStep 590957 = 221609) (by norm_num)
theorem B394349 : Blo 259821 394349 := bbase (se 3 (by rfl) ⟨73940, by rfl⟩ : syracuseStep 394349 = 147881) (by norm_num)
theorem B394373 : Blo 259821 394373 := bbase (se 4 (by rfl) ⟨36972, by rfl⟩ : syracuseStep 394373 = 73945) (by norm_num)
theorem B296077 : Blo 259821 296077 := bbase (se 3 (by rfl) ⟨55514, by rfl⟩ : syracuseStep 296077 = 111029) (by norm_num)
theorem B394397 : Blo 259821 394397 := bbase (se 3 (by rfl) ⟨73949, by rfl⟩ : syracuseStep 394397 = 147899) (by norm_num)
theorem B296113 : Blo 259821 296113 := bbase (se 2 (by rfl) ⟨111042, by rfl⟩ : syracuseStep 296113 = 222085) (by norm_num)
theorem B591029 : Blo 259821 591029 := bbase (se 5 (by rfl) ⟨27704, by rfl⟩ : syracuseStep 591029 = 55409) (by norm_num)
theorem B394421 : Blo 259821 394421 := bbase (se 5 (by rfl) ⟨18488, by rfl⟩ : syracuseStep 394421 = 36977) (by norm_num)
theorem B722117 : Blo 259821 722117 := bbase (se 4 (by rfl) ⟨67698, by rfl⟩ : syracuseStep 722117 = 135397) (by norm_num)
theorem B394445 : Blo 259821 394445 := bbase (se 3 (by rfl) ⟨73958, by rfl⟩ : syracuseStep 394445 = 147917) (by norm_num)
theorem B296149 : Blo 259821 296149 := bbase (se 7 (by rfl) ⟨3470, by rfl⟩ : syracuseStep 296149 = 6941) (by norm_num)
theorem B394469 : Blo 259821 394469 := bbase (se 4 (by rfl) ⟨36981, by rfl⟩ : syracuseStep 394469 = 73963) (by norm_num)
theorem B820469 : Blo 259821 820469 := bbase (se 5 (by rfl) ⟨38459, by rfl⟩ : syracuseStep 820469 = 76919) (by norm_num)
theorem B296185 : Blo 259821 296185 := bbase (se 2 (by rfl) ⟨111069, by rfl⟩ : syracuseStep 296185 = 222139) (by norm_num)
theorem B591101 : Blo 259821 591101 := bbase (se 3 (by rfl) ⟨110831, by rfl⟩ : syracuseStep 591101 = 221663) (by norm_num)
theorem B394493 : Blo 259821 394493 := bbase (se 3 (by rfl) ⟨73967, by rfl⟩ : syracuseStep 394493 = 147935) (by norm_num)
theorem B328961 : Blo 259821 328961 := bbase (se 2 (by rfl) ⟨123360, by rfl⟩ : syracuseStep 328961 = 246721) (by norm_num)
theorem B394517 : Blo 259821 394517 := bbase (se 6 (by rfl) ⟨9246, by rfl⟩ : syracuseStep 394517 = 18493) (by norm_num)
theorem B296221 : Blo 259821 296221 := bbase (se 3 (by rfl) ⟨55541, by rfl⟩ : syracuseStep 296221 = 111083) (by norm_num)
theorem B394541 : Blo 259821 394541 := bbase (se 3 (by rfl) ⟨73976, by rfl⟩ : syracuseStep 394541 = 147953) (by norm_num)
theorem B329017 : Blo 259821 329017 := bbase (se 2 (by rfl) ⟨123381, by rfl⟩ : syracuseStep 329017 = 246763) (by norm_num)
theorem B296257 : Blo 259821 296257 := bbase (se 2 (by rfl) ⟨111096, by rfl⟩ : syracuseStep 296257 = 222193) (by norm_num)
theorem B886085 : Blo 259821 886085 := bbase (se 4 (by rfl) ⟨83070, by rfl⟩ : syracuseStep 886085 = 166141) (by norm_num)
theorem B591173 : Blo 259821 591173 := bbase (se 4 (by rfl) ⟨55422, by rfl⟩ : syracuseStep 591173 = 110845) (by norm_num)
theorem B394565 : Blo 259821 394565 := bbase (se 4 (by rfl) ⟨36990, by rfl⟩ : syracuseStep 394565 = 73981) (by norm_num)
theorem B394589 : Blo 259821 394589 := bbase (se 3 (by rfl) ⟨73985, by rfl⟩ : syracuseStep 394589 = 147971) (by norm_num)
theorem B296293 : Blo 259821 296293 := bbase (se 4 (by rfl) ⟨27777, by rfl⟩ : syracuseStep 296293 = 55555) (by norm_num)
theorem B394613 : Blo 259821 394613 := bbase (se 5 (by rfl) ⟨18497, by rfl⟩ : syracuseStep 394613 = 36995) (by norm_num)
theorem B296329 : Blo 259821 296329 := bbase (se 2 (by rfl) ⟨111123, by rfl⟩ : syracuseStep 296329 = 222247) (by norm_num)
theorem B591245 : Blo 259821 591245 := bbase (se 3 (by rfl) ⟨110858, by rfl⟩ : syracuseStep 591245 = 221717) (by norm_num)
theorem B394637 : Blo 259821 394637 := bbase (se 3 (by rfl) ⟨73994, by rfl⟩ : syracuseStep 394637 = 147989) (by norm_num)
theorem B329113 : Blo 259821 329113 := bbase (se 2 (by rfl) ⟨123417, by rfl⟩ : syracuseStep 329113 = 246835) (by norm_num)
theorem B394661 : Blo 259821 394661 := bbase (se 4 (by rfl) ⟨36999, by rfl⟩ : syracuseStep 394661 = 73999) (by norm_num)
theorem B296365 : Blo 259821 296365 := bbase (se 3 (by rfl) ⟨55568, by rfl⟩ : syracuseStep 296365 = 111137) (by norm_num)
theorem B394685 : Blo 259821 394685 := bbase (se 3 (by rfl) ⟨74003, by rfl⟩ : syracuseStep 394685 = 148007) (by norm_num)
theorem B296401 : Blo 259821 296401 := bbase (se 2 (by rfl) ⟨111150, by rfl⟩ : syracuseStep 296401 = 222301) (by norm_num)
theorem B591317 : Blo 259821 591317 := bbase (se 7 (by rfl) ⟨6929, by rfl⟩ : syracuseStep 591317 = 13859) (by norm_num)
theorem B394709 : Blo 259821 394709 := bbase (se 7 (by rfl) ⟨4625, by rfl⟩ : syracuseStep 394709 = 9251) (by norm_num)
theorem B394733 : Blo 259821 394733 := bbase (se 3 (by rfl) ⟨74012, by rfl⟩ : syracuseStep 394733 = 148025) (by norm_num)
theorem B296437 : Blo 259821 296437 := bbase (se 5 (by rfl) ⟨13895, by rfl⟩ : syracuseStep 296437 = 27791) (by norm_num)
theorem B394757 : Blo 259821 394757 := bbase (se 4 (by rfl) ⟨37008, by rfl⟩ : syracuseStep 394757 = 74017) (by norm_num)
theorem B296473 : Blo 259821 296473 := bbase (se 2 (by rfl) ⟨111177, by rfl⟩ : syracuseStep 296473 = 222355) (by norm_num)
theorem B591389 : Blo 259821 591389 := bbase (se 3 (by rfl) ⟨110885, by rfl⟩ : syracuseStep 591389 = 221771) (by norm_num)
theorem B394781 : Blo 259821 394781 := bbase (se 3 (by rfl) ⟨74021, by rfl⟩ : syracuseStep 394781 = 148043) (by norm_num)
theorem B296501 : Blo 259821 296501 := bbase (se 5 (by rfl) ⟨13898, by rfl⟩ : syracuseStep 296501 = 27797) (by norm_num)
theorem B394805 : Blo 259821 394805 := bbase (se 5 (by rfl) ⟨18506, by rfl⟩ : syracuseStep 394805 = 37013) (by norm_num)
theorem B296509 : Blo 259821 296509 := bbase (se 3 (by rfl) ⟨55595, by rfl⟩ : syracuseStep 296509 = 111191) (by norm_num)
theorem B329285 : Blo 259821 329285 := bbase (se 4 (by rfl) ⟨30870, by rfl⟩ : syracuseStep 329285 = 61741) (by norm_num)
theorem B394829 : Blo 259821 394829 := bbase (se 3 (by rfl) ⟨74030, by rfl⟩ : syracuseStep 394829 = 148061) (by norm_num)
theorem B558677 : Blo 259821 558677 := bbase (se 8 (by rfl) ⟨3273, by rfl⟩ : syracuseStep 558677 = 6547) (by norm_num)
theorem B296545 : Blo 259821 296545 := bbase (se 2 (by rfl) ⟨111204, by rfl⟩ : syracuseStep 296545 = 222409) (by norm_num)
theorem B591461 : Blo 259821 591461 := bbase (se 4 (by rfl) ⟨55449, by rfl⟩ : syracuseStep 591461 = 110899) (by norm_num)
theorem B394853 : Blo 259821 394853 := bbase (se 4 (by rfl) ⟨37017, by rfl⟩ : syracuseStep 394853 = 74035) (by norm_num)
theorem B1115765 : Blo 259821 1115765 := bbase (se 5 (by rfl) ⟨52301, by rfl⟩ : syracuseStep 1115765 = 104603) (by norm_num)
theorem B329341 : Blo 259821 329341 := bbase (se 3 (by rfl) ⟨61751, by rfl⟩ : syracuseStep 329341 = 123503) (by norm_num)
theorem B394877 : Blo 259821 394877 := bbase (se 3 (by rfl) ⟨74039, by rfl⟩ : syracuseStep 394877 = 148079) (by norm_num)
theorem B296581 : Blo 259821 296581 := bbase (se 4 (by rfl) ⟨27804, by rfl⟩ : syracuseStep 296581 = 55609) (by norm_num)
theorem B394901 : Blo 259821 394901 := bbase (se 6 (by rfl) ⟨9255, by rfl⟩ : syracuseStep 394901 = 18511) (by norm_num)
theorem B296617 : Blo 259821 296617 := bbase (se 2 (by rfl) ⟨111231, by rfl⟩ : syracuseStep 296617 = 222463) (by norm_num)
theorem B591533 : Blo 259821 591533 := bbase (se 3 (by rfl) ⟨110912, by rfl⟩ : syracuseStep 591533 = 221825) (by norm_num)
theorem B394925 : Blo 259821 394925 := bbase (se 3 (by rfl) ⟨74048, by rfl⟩ : syracuseStep 394925 = 148097) (by norm_num)
theorem B394949 : Blo 259821 394949 := bbase (se 4 (by rfl) ⟨37026, by rfl⟩ : syracuseStep 394949 = 74053) (by norm_num)
theorem B296653 : Blo 259821 296653 := bbase (se 3 (by rfl) ⟨55622, by rfl⟩ : syracuseStep 296653 = 111245) (by norm_num)
theorem B329437 : Blo 259821 329437 := bbase (se 3 (by rfl) ⟨61769, by rfl⟩ : syracuseStep 329437 = 123539) (by norm_num)
theorem B394973 : Blo 259821 394973 := bbase (se 3 (by rfl) ⟨74057, by rfl⟩ : syracuseStep 394973 = 148115) (by norm_num)
theorem B296689 : Blo 259821 296689 := bbase (se 2 (by rfl) ⟨111258, by rfl⟩ : syracuseStep 296689 = 222517) (by norm_num)
theorem B886517 : Blo 259821 886517 := bbase (se 5 (by rfl) ⟨41555, by rfl⟩ : syracuseStep 886517 = 83111) (by norm_num)
theorem B591605 : Blo 259821 591605 := bbase (se 5 (by rfl) ⟨27731, by rfl⟩ : syracuseStep 591605 = 55463) (by norm_num)
theorem B394997 : Blo 259821 394997 := bbase (se 5 (by rfl) ⟨18515, by rfl⟩ : syracuseStep 394997 = 37031) (by norm_num)
theorem B395021 : Blo 259821 395021 := bbase (se 3 (by rfl) ⟨74066, by rfl⟩ : syracuseStep 395021 = 148133) (by norm_num)
theorem B296725 : Blo 259821 296725 := bbase (se 6 (by rfl) ⟨6954, by rfl⟩ : syracuseStep 296725 = 13909) (by norm_num)
theorem B395045 : Blo 259821 395045 := bbase (se 4 (by rfl) ⟨37035, by rfl⟩ : syracuseStep 395045 = 74071) (by norm_num)
theorem B296761 : Blo 259821 296761 := bbase (se 2 (by rfl) ⟨111285, by rfl⟩ : syracuseStep 296761 = 222571) (by norm_num)
theorem B591677 : Blo 259821 591677 := bbase (se 3 (by rfl) ⟨110939, by rfl⟩ : syracuseStep 591677 = 221879) (by norm_num)
theorem B395069 : Blo 259821 395069 := bbase (se 3 (by rfl) ⟨74075, by rfl⟩ : syracuseStep 395069 = 148151) (by norm_num)
theorem B493381 : Blo 259821 493381 := bbase (se 4 (by rfl) ⟨46254, by rfl⟩ : syracuseStep 493381 = 92509) (by norm_num)
theorem B395093 : Blo 259821 395093 := bbase (se 9 (by rfl) ⟨1157, by rfl⟩ : syracuseStep 395093 = 2315) (by norm_num)
theorem B296797 : Blo 259821 296797 := bbase (se 3 (by rfl) ⟨55649, by rfl⟩ : syracuseStep 296797 = 111299) (by norm_num)
theorem B395117 : Blo 259821 395117 := bbase (se 3 (by rfl) ⟨74084, by rfl⟩ : syracuseStep 395117 = 148169) (by norm_num)
theorem B591749 : Blo 259821 591749 := bbase (se 4 (by rfl) ⟨55476, by rfl⟩ : syracuseStep 591749 = 110953) (by norm_num)
theorem B395141 : Blo 259821 395141 := bbase (se 4 (by rfl) ⟨37044, by rfl⟩ : syracuseStep 395141 = 74089) (by norm_num)
theorem B329609 : Blo 259821 329609 := bbase (se 2 (by rfl) ⟨123603, by rfl⟩ : syracuseStep 329609 = 247207) (by norm_num)
theorem B395165 : Blo 259821 395165 := bbase (se 3 (by rfl) ⟨74093, by rfl⟩ : syracuseStep 395165 = 148187) (by norm_num)
theorem B395189 : Blo 259821 395189 := bbase (se 5 (by rfl) ⟨18524, by rfl⟩ : syracuseStep 395189 = 37049) (by norm_num)
theorem B296893 : Blo 259821 296893 := bbase (se 3 (by rfl) ⟨55667, by rfl⟩ : syracuseStep 296893 = 111335) (by norm_num)
theorem B329665 : Blo 259821 329665 := bbase (se 2 (by rfl) ⟨123624, by rfl⟩ : syracuseStep 329665 = 247249) (by norm_num)
theorem B591821 : Blo 259821 591821 := bbase (se 3 (by rfl) ⟨110966, by rfl⟩ : syracuseStep 591821 = 221933) (by norm_num)
theorem B395213 : Blo 259821 395213 := bbase (se 3 (by rfl) ⟨74102, by rfl⟩ : syracuseStep 395213 = 148205) (by norm_num)
theorem B395237 : Blo 259821 395237 := bbase (se 4 (by rfl) ⟨37053, by rfl⟩ : syracuseStep 395237 = 74107) (by norm_num)
theorem B395261 : Blo 259821 395261 := bbase (se 3 (by rfl) ⟨74111, by rfl⟩ : syracuseStep 395261 = 148223) (by norm_num)
theorem B1673237 : Blo 259821 1673237 := bbase (se 6 (by rfl) ⟨39216, by rfl⟩ : syracuseStep 1673237 = 78433) (by norm_num)
theorem B4261909 : Blo 259821 4261909 := bbase (se 6 (by rfl) ⟨99888, by rfl⟩ : syracuseStep 4261909 = 199777) (by norm_num)
theorem B591893 : Blo 259821 591893 := bbase (se 6 (by rfl) ⟨13872, by rfl⟩ : syracuseStep 591893 = 27745) (by norm_num)
theorem B395285 : Blo 259821 395285 := bbase (se 6 (by rfl) ⟨9264, by rfl⟩ : syracuseStep 395285 = 18529) (by norm_num)
theorem B329761 : Blo 259821 329761 := bbase (se 2 (by rfl) ⟨123660, by rfl⟩ : syracuseStep 329761 = 247321) (by norm_num)
theorem B395309 : Blo 259821 395309 := bbase (se 3 (by rfl) ⟨74120, by rfl⟩ : syracuseStep 395309 = 148241) (by norm_num)
theorem B395333 : Blo 259821 395333 := bbase (se 4 (by rfl) ⟨37062, by rfl⟩ : syracuseStep 395333 = 74125) (by norm_num)
theorem B591965 : Blo 259821 591965 := bbase (se 3 (by rfl) ⟨110993, by rfl⟩ : syracuseStep 591965 = 221987) (by norm_num)
theorem B395357 : Blo 259821 395357 := bbase (se 3 (by rfl) ⟨74129, by rfl⟩ : syracuseStep 395357 = 148259) (by norm_num)
theorem B493685 : Blo 259821 493685 := bbase (se 5 (by rfl) ⟨23141, by rfl⟩ : syracuseStep 493685 = 46283) (by norm_num)
theorem B395381 : Blo 259821 395381 := bbase (se 5 (by rfl) ⟨18533, by rfl⟩ : syracuseStep 395381 = 37067) (by norm_num)
theorem B395405 : Blo 259821 395405 := bbase (se 3 (by rfl) ⟨74138, by rfl⟩ : syracuseStep 395405 = 148277) (by norm_num)
theorem B886949 : Blo 259821 886949 := bbase (se 4 (by rfl) ⟨83151, by rfl⟩ : syracuseStep 886949 = 166303) (by norm_num)
theorem B592037 : Blo 259821 592037 := bbase (se 4 (by rfl) ⟨55503, by rfl⟩ : syracuseStep 592037 = 111007) (by norm_num)
theorem B395429 : Blo 259821 395429 := bbase (se 4 (by rfl) ⟨37071, by rfl⟩ : syracuseStep 395429 = 74143) (by norm_num)
theorem B395453 : Blo 259821 395453 := bbase (se 3 (by rfl) ⟨74147, by rfl⟩ : syracuseStep 395453 = 148295) (by norm_num)
theorem B329933 : Blo 259821 329933 := bbase (se 3 (by rfl) ⟨61862, by rfl⟩ : syracuseStep 329933 = 123725) (by norm_num)
theorem B395477 : Blo 259821 395477 := bbase (se 7 (by rfl) ⟨4634, by rfl⟩ : syracuseStep 395477 = 9269) (by norm_num)
theorem B592109 : Blo 259821 592109 := bbase (se 3 (by rfl) ⟨111020, by rfl⟩ : syracuseStep 592109 = 222041) (by norm_num)
theorem B395501 : Blo 259821 395501 := bbase (se 3 (by rfl) ⟨74156, by rfl⟩ : syracuseStep 395501 = 148313) (by norm_num)
theorem B329989 : Blo 259821 329989 := bbase (se 4 (by rfl) ⟨30936, by rfl⟩ : syracuseStep 329989 = 61873) (by norm_num)
theorem B395525 : Blo 259821 395525 := bbase (se 4 (by rfl) ⟨37080, by rfl⟩ : syracuseStep 395525 = 74161) (by norm_num)
theorem B395549 : Blo 259821 395549 := bbase (se 3 (by rfl) ⟨74165, by rfl⟩ : syracuseStep 395549 = 148331) (by norm_num)
theorem B592181 : Blo 259821 592181 := bbase (se 5 (by rfl) ⟨27758, by rfl⟩ : syracuseStep 592181 = 55517) (by norm_num)
theorem B395573 : Blo 259821 395573 := bbase (se 5 (by rfl) ⟨18542, by rfl⟩ : syracuseStep 395573 = 37085) (by norm_num)
theorem B395597 : Blo 259821 395597 := bbase (se 3 (by rfl) ⟨74174, by rfl⟩ : syracuseStep 395597 = 148349) (by norm_num)
theorem B264529 : Blo 259821 264529 := bbase (se 2 (by rfl) ⟨99198, by rfl⟩ : syracuseStep 264529 = 198397) (by norm_num)
theorem B330085 : Blo 259821 330085 := bbase (se 4 (by rfl) ⟨30945, by rfl⟩ : syracuseStep 330085 = 61891) (by norm_num)
theorem B395621 : Blo 259821 395621 := bbase (se 4 (by rfl) ⟨37089, by rfl⟩ : syracuseStep 395621 = 74179) (by norm_num)
theorem B264553 : Blo 259821 264553 := bbase (se 2 (by rfl) ⟨99207, by rfl⟩ : syracuseStep 264553 = 198415) (by norm_num)
theorem B625013 : Blo 259821 625013 := bbase (se 5 (by rfl) ⟨29297, by rfl⟩ : syracuseStep 625013 = 58595) (by norm_num)
theorem B2394485 : Blo 259821 2394485 := bbase (se 5 (by rfl) ⟨112241, by rfl⟩ : syracuseStep 2394485 = 224483) (by norm_num)
theorem B592253 : Blo 259821 592253 := bbase (se 3 (by rfl) ⟨111047, by rfl⟩ : syracuseStep 592253 = 222095) (by norm_num)
theorem B395645 : Blo 259821 395645 := bbase (se 3 (by rfl) ⟨74183, by rfl⟩ : syracuseStep 395645 = 148367) (by norm_num)
theorem B395669 : Blo 259821 395669 := bbase (se 6 (by rfl) ⟨9273, by rfl⟩ : syracuseStep 395669 = 18547) (by norm_num)
theorem B657821 : Blo 259821 657821 := bbase (se 3 (by rfl) ⟨123341, by rfl⟩ : syracuseStep 657821 = 246683) (by norm_num)
theorem B395693 : Blo 259821 395693 := bbase (se 3 (by rfl) ⟨74192, by rfl⟩ : syracuseStep 395693 = 148385) (by norm_num)
theorem B592325 : Blo 259821 592325 := bbase (se 4 (by rfl) ⟨55530, by rfl⟩ : syracuseStep 592325 = 111061) (by norm_num)
theorem B395717 : Blo 259821 395717 := bbase (se 4 (by rfl) ⟨37098, by rfl⟩ : syracuseStep 395717 = 74197) (by norm_num)
theorem B559565 : Blo 259821 559565 := bbase (se 3 (by rfl) ⟨104918, by rfl⟩ : syracuseStep 559565 = 209837) (by norm_num)
theorem B592397 : Blo 259821 592397 := bbase (se 3 (by rfl) ⟨111074, by rfl⟩ : syracuseStep 592397 = 222149) (by norm_num)
theorem B330257 : Blo 259821 330257 := bbase (se 2 (by rfl) ⟨123846, by rfl⟩ : syracuseStep 330257 = 247693) (by norm_num)
theorem B625205 : Blo 259821 625205 := bbase (se 5 (by rfl) ⟨29306, by rfl⟩ : syracuseStep 625205 = 58613) (by norm_num)
theorem B559685 : Blo 259821 559685 := bbase (se 4 (by rfl) ⟨52470, by rfl⟩ : syracuseStep 559685 = 104941) (by norm_num)
theorem B330313 : Blo 259821 330313 := bbase (se 2 (by rfl) ⟨123867, by rfl⟩ : syracuseStep 330313 = 247735) (by norm_num)
theorem B887381 : Blo 259821 887381 := bbase (se 8 (by rfl) ⟨5199, by rfl⟩ : syracuseStep 887381 = 10399) (by norm_num)
theorem B592469 : Blo 259821 592469 := bbase (se 8 (by rfl) ⟨3471, by rfl⟩ : syracuseStep 592469 = 6943) (by norm_num)
theorem B1116773 : Blo 259821 1116773 := bbase (se 4 (by rfl) ⟨104697, by rfl⟩ : syracuseStep 1116773 = 209395) (by norm_num)
theorem B264845 : Blo 259821 264845 := bbase (se 3 (by rfl) ⟨49658, by rfl⟩ : syracuseStep 264845 = 99317) (by norm_num)
theorem B592541 : Blo 259821 592541 := bbase (se 3 (by rfl) ⟨111101, by rfl⟩ : syracuseStep 592541 = 222203) (by norm_num)
theorem B330409 : Blo 259821 330409 := bbase (se 2 (by rfl) ⟨123903, by rfl⟩ : syracuseStep 330409 = 247807) (by norm_num)
theorem B592613 : Blo 259821 592613 := bbase (se 4 (by rfl) ⟨55557, by rfl⟩ : syracuseStep 592613 = 111115) (by norm_num)
theorem B658165 : Blo 259821 658165 := bbase (se 5 (by rfl) ⟨30851, by rfl⟩ : syracuseStep 658165 = 61703) (by norm_num)
theorem B592685 : Blo 259821 592685 := bbase (se 3 (by rfl) ⟨111128, by rfl⟩ : syracuseStep 592685 = 222257) (by norm_num)
theorem B363317 : Blo 259821 363317 := bbase (se 5 (by rfl) ⟨17030, by rfl⟩ : syracuseStep 363317 = 34061) (by norm_num)
theorem B1084229 : Blo 259821 1084229 := bbase (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) (by norm_num)
theorem B330581 : Blo 259821 330581 := bbase (se 9 (by rfl) ⟨968, by rfl⟩ : syracuseStep 330581 = 1937) (by norm_num)
theorem B658277 : Blo 259821 658277 := bbase (se 4 (by rfl) ⟨61713, by rfl⟩ : syracuseStep 658277 = 123427) (by norm_num)
theorem B494437 : Blo 259821 494437 := bbase (se 4 (by rfl) ⟨46353, by rfl⟩ : syracuseStep 494437 = 92707) (by norm_num)
theorem B592757 : Blo 259821 592757 := bbase (se 5 (by rfl) ⟨27785, by rfl⟩ : syracuseStep 592757 = 55571) (by norm_num)
theorem B330637 : Blo 259821 330637 := bbase (se 3 (by rfl) ⟨61994, by rfl⟩ : syracuseStep 330637 = 123989) (by norm_num)
theorem B592829 : Blo 259821 592829 := bbase (se 3 (by rfl) ⟨111155, by rfl⟩ : syracuseStep 592829 = 222311) (by norm_num)
theorem B330733 : Blo 259821 330733 := bbase (se 3 (by rfl) ⟨62012, by rfl⟩ : syracuseStep 330733 = 124025) (by norm_num)
theorem B494581 : Blo 259821 494581 := bbase (se 5 (by rfl) ⟨23183, by rfl⟩ : syracuseStep 494581 = 46367) (by norm_num)
theorem B887813 : Blo 259821 887813 := bbase (se 4 (by rfl) ⟨83232, by rfl⟩ : syracuseStep 887813 = 166465) (by norm_num)
theorem B592901 : Blo 259821 592901 := bbase (se 4 (by rfl) ⟨55584, by rfl⟩ : syracuseStep 592901 = 111169) (by norm_num)
theorem B658469 : Blo 259821 658469 := bbase (se 4 (by rfl) ⟨61731, by rfl⟩ : syracuseStep 658469 = 123463) (by norm_num)
theorem B592973 : Blo 259821 592973 := bbase (se 3 (by rfl) ⟨111182, by rfl⟩ : syracuseStep 592973 = 222365) (by norm_num)
theorem B527477 : Blo 259821 527477 := bbase (se 5 (by rfl) ⟨24725, by rfl⟩ : syracuseStep 527477 = 49451) (by norm_num)
theorem B756869 : Blo 259821 756869 := bbase (se 4 (by rfl) ⟨70956, by rfl⟩ : syracuseStep 756869 = 141913) (by norm_num)
theorem B494741 : Blo 259821 494741 := bbase (se 6 (by rfl) ⟨11595, by rfl⟩ : syracuseStep 494741 = 23191) (by norm_num)
theorem B593045 : Blo 259821 593045 := bbase (se 6 (by rfl) ⟨13899, by rfl⟩ : syracuseStep 593045 = 27799) (by norm_num)
theorem B330905 : Blo 259821 330905 := bbase (se 2 (by rfl) ⟨124089, by rfl⟩ : syracuseStep 330905 = 248179) (by norm_num)
theorem B560317 : Blo 259821 560317 := bbase (se 3 (by rfl) ⟨105059, by rfl⟩ : syracuseStep 560317 = 210119) (by norm_num)
theorem B330961 : Blo 259821 330961 := bbase (se 2 (by rfl) ⟨124110, by rfl⟩ : syracuseStep 330961 = 248221) (by norm_num)
theorem B593117 : Blo 259821 593117 := bbase (se 3 (by rfl) ⟨111209, by rfl⟩ : syracuseStep 593117 = 222419) (by norm_num)
theorem B494885 : Blo 259821 494885 := bbase (se 4 (by rfl) ⟨46395, by rfl⟩ : syracuseStep 494885 = 92791) (by norm_num)
theorem B593189 : Blo 259821 593189 := bbase (se 4 (by rfl) ⟨55611, by rfl⟩ : syracuseStep 593189 = 111223) (by norm_num)
theorem B331057 : Blo 259821 331057 := bbase (se 2 (by rfl) ⟨124146, by rfl⟩ : syracuseStep 331057 = 248293) (by norm_num)
theorem B593261 : Blo 259821 593261 := bbase (se 3 (by rfl) ⟨111236, by rfl⟩ : syracuseStep 593261 = 222473) (by norm_num)
theorem B658813 : Blo 259821 658813 := bbase (se 3 (by rfl) ⟨123527, by rfl⟩ : syracuseStep 658813 = 247055) (by norm_num)
theorem B888245 : Blo 259821 888245 := bbase (se 5 (by rfl) ⟨41636, by rfl⟩ : syracuseStep 888245 = 83273) (by norm_num)
theorem B593333 : Blo 259821 593333 := bbase (se 5 (by rfl) ⟨27812, by rfl⟩ : syracuseStep 593333 = 55625) (by norm_num)
theorem B396733 : Blo 259821 396733 := bbase (se 3 (by rfl) ⟨74387, by rfl⟩ : syracuseStep 396733 = 148775) (by norm_num)
theorem B331229 : Blo 259821 331229 := bbase (se 3 (by rfl) ⟨62105, by rfl⟩ : syracuseStep 331229 = 124211) (by norm_num)
theorem B658925 : Blo 259821 658925 := bbase (se 3 (by rfl) ⟨123548, by rfl⟩ : syracuseStep 658925 = 247097) (by norm_num)
theorem B593405 : Blo 259821 593405 := bbase (se 3 (by rfl) ⟨111263, by rfl⟩ : syracuseStep 593405 = 222527) (by norm_num)
theorem B331285 : Blo 259821 331285 := bbase (se 6 (by rfl) ⟨7764, by rfl⟩ : syracuseStep 331285 = 15529) (by norm_num)
theorem B495173 : Blo 259821 495173 := bbase (se 4 (by rfl) ⟨46422, by rfl⟩ : syracuseStep 495173 = 92845) (by norm_num)
theorem B593477 : Blo 259821 593477 := bbase (se 4 (by rfl) ⟨55638, by rfl⟩ : syracuseStep 593477 = 111277) (by norm_num)
theorem B2526805 : Blo 259821 2526805 := bbase (se 8 (by rfl) ⟨14805, by rfl⟩ : syracuseStep 2526805 = 29611) (by norm_num)
theorem B331381 : Blo 259821 331381 := bbase (se 5 (by rfl) ⟨15533, by rfl⟩ : syracuseStep 331381 = 31067) (by norm_num)
theorem B593549 : Blo 259821 593549 := bbase (se 3 (by rfl) ⟨111290, by rfl⟩ : syracuseStep 593549 = 222581) (by norm_num)
theorem B659117 : Blo 259821 659117 := bbase (se 3 (by rfl) ⟨123584, by rfl⟩ : syracuseStep 659117 = 247169) (by norm_num)
theorem B495325 : Blo 259821 495325 := bbase (se 3 (by rfl) ⟨92873, by rfl⟩ : syracuseStep 495325 = 185747) (by norm_num)
theorem B593677 : Blo 259821 593677 := bbase (se 3 (by rfl) ⟨111314, by rfl⟩ : syracuseStep 593677 = 222629) (by norm_num)
theorem B266009 : Blo 259821 266009 := bbase (se 2 (by rfl) ⟨99753, by rfl⟩ : syracuseStep 266009 = 199507) (by norm_num)
theorem B331553 : Blo 259821 331553 := bbase (se 2 (by rfl) ⟨124332, by rfl⟩ : syracuseStep 331553 = 248665) (by norm_num)
theorem B331609 : Blo 259821 331609 := bbase (se 2 (by rfl) ⟨124353, by rfl⟩ : syracuseStep 331609 = 248707) (by norm_num)
theorem B888677 : Blo 259821 888677 := bbase (se 4 (by rfl) ⟨83313, by rfl⟩ : syracuseStep 888677 = 166627) (by norm_num)
theorem B2002805 : Blo 259821 2002805 := bbase (se 5 (by rfl) ⟨93881, by rfl⟩ : syracuseStep 2002805 = 187763) (by norm_num)
theorem B331705 : Blo 259821 331705 := bbase (se 2 (by rfl) ⟨124389, by rfl⟩ : syracuseStep 331705 = 248779) (by norm_num)
theorem B659461 : Blo 259821 659461 := bbase (se 4 (by rfl) ⟨61824, by rfl⟩ : syracuseStep 659461 = 123649) (by norm_num)
theorem B495629 : Blo 259821 495629 := bbase (se 3 (by rfl) ⟨92930, by rfl⟩ : syracuseStep 495629 = 185861) (by norm_num)
theorem B987173 : Blo 259821 987173 := bbase (se 4 (by rfl) ⟨92547, by rfl⟩ : syracuseStep 987173 = 185095) (by norm_num)
theorem B561205 : Blo 259821 561205 := bbase (se 5 (by rfl) ⟨26306, by rfl⟩ : syracuseStep 561205 = 52613) (by norm_num)
theorem B13176917 : Blo 259821 13176917 := bbase (se 8 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 13176917 = 154417) (by norm_num)
theorem B626773 : Blo 259821 626773 := bbase (se 8 (by rfl) ⟨3672, by rfl⟩ : syracuseStep 626773 = 7345) (by norm_num)
theorem B331877 : Blo 259821 331877 := bbase (se 4 (by rfl) ⟨31113, by rfl⟩ : syracuseStep 331877 = 62227) (by norm_num)
theorem B659573 : Blo 259821 659573 := bbase (se 5 (by rfl) ⟨30917, by rfl⟩ : syracuseStep 659573 = 61835) (by norm_num)
theorem B331933 : Blo 259821 331933 := bbase (se 3 (by rfl) ⟨62237, by rfl⟩ : syracuseStep 331933 = 124475) (by norm_num)
theorem B561325 : Blo 259821 561325 := bbase (se 3 (by rfl) ⟨105248, by rfl⟩ : syracuseStep 561325 = 210497) (by norm_num)
theorem B332029 : Blo 259821 332029 := bbase (se 3 (by rfl) ⟨62255, by rfl⟩ : syracuseStep 332029 = 124511) (by norm_num)
theorem B889109 : Blo 259821 889109 := bbase (se 6 (by rfl) ⟨20838, by rfl⟩ : syracuseStep 889109 = 41677) (by norm_num)
theorem B659765 : Blo 259821 659765 := bbase (se 5 (by rfl) ⟨30926, by rfl⟩ : syracuseStep 659765 = 61853) (by norm_num)
theorem B987461 : Blo 259821 987461 := bbase (se 4 (by rfl) ⟨92574, by rfl⟩ : syracuseStep 987461 = 185149) (by norm_num)
theorem B1118549 : Blo 259821 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B332201 : Blo 259821 332201 := bbase (se 2 (by rfl) ⟨124575, by rfl⟩ : syracuseStep 332201 = 249151) (by norm_num)
theorem B561581 : Blo 259821 561581 := bbase (se 3 (by rfl) ⟨105296, by rfl⟩ : syracuseStep 561581 = 210593) (by norm_num)
theorem B332257 : Blo 259821 332257 := bbase (se 2 (by rfl) ⟨124596, by rfl⟩ : syracuseStep 332257 = 249193) (by norm_num)
theorem B332353 : Blo 259821 332353 := bbase (se 2 (by rfl) ⟨124632, by rfl⟩ : syracuseStep 332353 = 249265) (by norm_num)
theorem B660109 : Blo 259821 660109 := bbase (se 3 (by rfl) ⟨123770, by rfl⟩ : syracuseStep 660109 = 247541) (by norm_num)
theorem B397997 : Blo 259821 397997 := bbase (se 3 (by rfl) ⟨74624, by rfl⟩ : syracuseStep 397997 = 149249) (by norm_num)
theorem B627389 : Blo 259821 627389 := bbase (se 3 (by rfl) ⟨117635, by rfl⟩ : syracuseStep 627389 = 235271) (by norm_num)
theorem B889541 : Blo 259821 889541 := bbase (se 4 (by rfl) ⟨83394, by rfl⟩ : syracuseStep 889541 = 166789) (by norm_num)
theorem B332525 : Blo 259821 332525 := bbase (se 3 (by rfl) ⟨62348, by rfl⟩ : syracuseStep 332525 = 124697) (by norm_num)
theorem B660221 : Blo 259821 660221 := bbase (se 3 (by rfl) ⟨123791, by rfl⟩ : syracuseStep 660221 = 247583) (by norm_num)
theorem B496381 : Blo 259821 496381 := bbase (se 3 (by rfl) ⟨93071, by rfl⟩ : syracuseStep 496381 = 186143) (by norm_num)
theorem B299785 : Blo 259821 299785 := bbase (se 2 (by rfl) ⟨112419, by rfl⟩ : syracuseStep 299785 = 224839) (by norm_num)
theorem B299809 : Blo 259821 299809 := bbase (se 2 (by rfl) ⟨112428, by rfl⟩ : syracuseStep 299809 = 224857) (by norm_num)
theorem B332581 : Blo 259821 332581 := bbase (se 4 (by rfl) ⟨31179, by rfl⟩ : syracuseStep 332581 = 62359) (by norm_num)
theorem B332677 : Blo 259821 332677 := bbase (se 4 (by rfl) ⟨31188, by rfl⟩ : syracuseStep 332677 = 62377) (by norm_num)
theorem B496525 : Blo 259821 496525 := bbase (se 3 (by rfl) ⟨93098, by rfl⟩ : syracuseStep 496525 = 186197) (by norm_num)
theorem B660413 : Blo 259821 660413 := bbase (se 3 (by rfl) ⟨123827, by rfl⟩ : syracuseStep 660413 = 247655) (by norm_num)
theorem B496685 : Blo 259821 496685 := bbase (se 3 (by rfl) ⟨93128, by rfl⟩ : syracuseStep 496685 = 186257) (by norm_num)
theorem B332849 : Blo 259821 332849 := bbase (se 2 (by rfl) ⟨124818, by rfl⟩ : syracuseStep 332849 = 249637) (by norm_num)
theorem B1315925 : Blo 259821 1315925 := bbase (se 8 (by rfl) ⟨7710, by rfl⟩ : syracuseStep 1315925 = 15421) (by norm_num)
theorem B332905 : Blo 259821 332905 := bbase (se 2 (by rfl) ⟨124839, by rfl⟩ : syracuseStep 332905 = 249679) (by norm_num)
theorem B889973 : Blo 259821 889973 := bbase (se 5 (by rfl) ⟨41717, by rfl⟩ : syracuseStep 889973 = 83435) (by norm_num)
theorem B496829 : Blo 259821 496829 := bbase (se 3 (by rfl) ⟨93155, by rfl⟩ : syracuseStep 496829 = 186311) (by norm_num)
theorem B333001 : Blo 259821 333001 := bbase (se 2 (by rfl) ⟨124875, by rfl⟩ : syracuseStep 333001 = 249751) (by norm_num)
theorem B660757 : Blo 259821 660757 := bbase (se 6 (by rfl) ⟨15486, by rfl⟩ : syracuseStep 660757 = 30973) (by norm_num)
theorem B562469 : Blo 259821 562469 := bbase (se 4 (by rfl) ⟨52731, by rfl⟩ : syracuseStep 562469 = 105463) (by norm_num)
theorem B791909 : Blo 259821 791909 := bbase (se 4 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 791909 = 148483) (by norm_num)
theorem B333173 : Blo 259821 333173 := bbase (se 5 (by rfl) ⟨15617, by rfl⟩ : syracuseStep 333173 = 31235) (by norm_num)
theorem B660869 : Blo 259821 660869 := bbase (se 4 (by rfl) ⟨61956, by rfl⟩ : syracuseStep 660869 = 123913) (by norm_num)
theorem B333229 : Blo 259821 333229 := bbase (se 3 (by rfl) ⟨62480, by rfl⟩ : syracuseStep 333229 = 124961) (by norm_num)
theorem B628165 : Blo 259821 628165 := bbase (se 4 (by rfl) ⟨58890, by rfl⟩ : syracuseStep 628165 = 117781) (by norm_num)
theorem B497117 : Blo 259821 497117 := bbase (se 3 (by rfl) ⟨93209, by rfl⟩ : syracuseStep 497117 = 186419) (by norm_num)
theorem B988645 : Blo 259821 988645 := bbase (se 4 (by rfl) ⟨92685, by rfl⟩ : syracuseStep 988645 = 185371) (by norm_num)
theorem B333325 : Blo 259821 333325 := bbase (se 3 (by rfl) ⟨62498, by rfl⟩ : syracuseStep 333325 = 124997) (by norm_num)
theorem B562709 : Blo 259821 562709 := bbase (se 6 (by rfl) ⟨13188, by rfl⟩ : syracuseStep 562709 = 26377) (by norm_num)
theorem B661061 : Blo 259821 661061 := bbase (se 4 (by rfl) ⟨61974, by rfl⟩ : syracuseStep 661061 = 123949) (by norm_num)
theorem B497269 : Blo 259821 497269 := bbase (se 5 (by rfl) ⟨23309, by rfl⟩ : syracuseStep 497269 = 46619) (by norm_num)
theorem B333497 : Blo 259821 333497 := bbase (se 2 (by rfl) ⟨125061, by rfl⟩ : syracuseStep 333497 = 250123) (by norm_num)
theorem B1218277 : Blo 259821 1218277 := bbase (se 4 (by rfl) ⟨114213, by rfl⟩ : syracuseStep 1218277 = 228427) (by norm_num)
theorem B333553 : Blo 259821 333553 := bbase (se 2 (by rfl) ⟨125082, by rfl⟩ : syracuseStep 333553 = 250165) (by norm_num)
theorem B988949 : Blo 259821 988949 := bbase (se 6 (by rfl) ⟨23178, by rfl⟩ : syracuseStep 988949 = 46357) (by norm_num)
theorem B333649 : Blo 259821 333649 := bbase (se 2 (by rfl) ⟨125118, by rfl⟩ : syracuseStep 333649 = 250237) (by norm_num)
theorem B595829 : Blo 259821 595829 := bbase (se 5 (by rfl) ⟨27929, by rfl⟩ : syracuseStep 595829 = 55859) (by norm_num)
theorem B661405 : Blo 259821 661405 := bbase (se 3 (by rfl) ⟨124013, by rfl⟩ : syracuseStep 661405 = 248027) (by norm_num)
theorem B497573 : Blo 259821 497573 := bbase (se 4 (by rfl) ⟨46647, by rfl⟩ : syracuseStep 497573 = 93295) (by norm_num)
theorem B1185749 : Blo 259821 1185749 := bbase (se 7 (by rfl) ⟨13895, by rfl⟩ : syracuseStep 1185749 = 27791) (by norm_num)
theorem B399325 : Blo 259821 399325 := bbase (se 3 (by rfl) ⟨74873, by rfl⟩ : syracuseStep 399325 = 149747) (by norm_num)
theorem B333821 : Blo 259821 333821 := bbase (se 3 (by rfl) ⟨62591, by rfl⟩ : syracuseStep 333821 = 125183) (by norm_num)
theorem B661517 : Blo 259821 661517 := bbase (se 3 (by rfl) ⟨124034, by rfl⟩ : syracuseStep 661517 = 248069) (by norm_num)
theorem B563213 : Blo 259821 563213 := bbase (se 3 (by rfl) ⟨105602, by rfl⟩ : syracuseStep 563213 = 211205) (by norm_num)
theorem B563221 : Blo 259821 563221 := bbase (se 6 (by rfl) ⟨13200, by rfl⟩ : syracuseStep 563221 = 26401) (by norm_num)
theorem B333877 : Blo 259821 333877 := bbase (se 5 (by rfl) ⟨15650, by rfl⟩ : syracuseStep 333877 = 31301) (by norm_num)
theorem B628877 : Blo 259821 628877 := bbase (se 3 (by rfl) ⟨117914, by rfl⟩ : syracuseStep 628877 = 235829) (by norm_num)
theorem B661709 : Blo 259821 661709 := bbase (se 3 (by rfl) ⟨124070, by rfl⟩ : syracuseStep 661709 = 248141) (by norm_num)
theorem B1317221 : Blo 259821 1317221 := bbase (se 4 (by rfl) ⟨123489, by rfl⟩ : syracuseStep 1317221 = 246979) (by norm_num)
theorem B596413 : Blo 259821 596413 := bbase (se 3 (by rfl) ⟨111827, by rfl⟩ : syracuseStep 596413 = 223655) (by norm_num)
theorem B1481237 : Blo 259821 1481237 := bbase (se 6 (by rfl) ⟨34716, by rfl⟩ : syracuseStep 1481237 = 69433) (by norm_num)
theorem B662053 : Blo 259821 662053 := bbase (se 4 (by rfl) ⟨62067, by rfl⟩ : syracuseStep 662053 = 124135) (by norm_num)
theorem B334477 : Blo 259821 334477 := bbase (se 3 (by rfl) ⟨62714, by rfl⟩ : syracuseStep 334477 = 125429) (by norm_num)
theorem B662165 : Blo 259821 662165 := bbase (se 6 (by rfl) ⟨15519, by rfl⟩ : syracuseStep 662165 = 31039) (by norm_num)
theorem B498325 : Blo 259821 498325 := bbase (se 6 (by rfl) ⟨11679, by rfl⟩ : syracuseStep 498325 = 23359) (by norm_num)
theorem B498469 : Blo 259821 498469 := bbase (se 4 (by rfl) ⟨46731, by rfl⟩ : syracuseStep 498469 = 93463) (by norm_num)
theorem B629549 : Blo 259821 629549 := bbase (se 3 (by rfl) ⟨118040, by rfl⟩ : syracuseStep 629549 = 236081) (by norm_num)
theorem B662357 : Blo 259821 662357 := bbase (se 9 (by rfl) ⟨1940, by rfl⟩ : syracuseStep 662357 = 3881) (by norm_num)
theorem B498629 : Blo 259821 498629 := bbase (se 4 (by rfl) ⟨46746, by rfl⟩ : syracuseStep 498629 = 93493) (by norm_num)
theorem B498773 : Blo 259821 498773 := bbase (se 8 (by rfl) ⟨2922, by rfl⟩ : syracuseStep 498773 = 5845) (by norm_num)
theorem B662701 : Blo 259821 662701 := bbase (se 3 (by rfl) ⟨124256, by rfl⟩ : syracuseStep 662701 = 248513) (by norm_num)
theorem B597253 : Blo 259821 597253 := bbase (se 4 (by rfl) ⟨55992, by rfl⟩ : syracuseStep 597253 = 111985) (by norm_num)
theorem B662813 : Blo 259821 662813 := bbase (se 3 (by rfl) ⟨124277, by rfl⟩ : syracuseStep 662813 = 248555) (by norm_num)
theorem B499061 : Blo 259821 499061 := bbase (se 5 (by rfl) ⟨23393, by rfl⟩ : syracuseStep 499061 = 46787) (by norm_num)
theorem B663005 : Blo 259821 663005 := bbase (se 3 (by rfl) ⟨124313, by rfl⟩ : syracuseStep 663005 = 248627) (by norm_num)
theorem B499213 : Blo 259821 499213 := bbase (se 3 (by rfl) ⟨93602, by rfl⟩ : syracuseStep 499213 = 187205) (by norm_num)
theorem B1318517 : Blo 259821 1318517 := bbase (se 5 (by rfl) ⟨61805, by rfl⟩ : syracuseStep 1318517 = 123611) (by norm_num)
theorem B1482421 : Blo 259821 1482421 := bbase (se 5 (by rfl) ⟨69488, by rfl⟩ : syracuseStep 1482421 = 138977) (by norm_num)
theorem B1253141 : Blo 259821 1253141 := bbase (se 6 (by rfl) ⟨29370, by rfl⟩ : syracuseStep 1253141 = 58741) (by norm_num)
theorem B663349 : Blo 259821 663349 := bbase (se 5 (by rfl) ⟨31094, by rfl⟩ : syracuseStep 663349 = 62189) (by norm_num)
theorem B499517 : Blo 259821 499517 := bbase (se 3 (by rfl) ⟨93659, by rfl⟩ : syracuseStep 499517 = 187319) (by norm_num)
theorem B991061 : Blo 259821 991061 := bbase (se 9 (by rfl) ⟨2903, by rfl⟩ : syracuseStep 991061 = 5807) (by norm_num)
theorem B761717 : Blo 259821 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B663461 : Blo 259821 663461 := bbase (se 4 (by rfl) ⟨62199, by rfl⟩ : syracuseStep 663461 = 124399) (by norm_num)
theorem B1253333 : Blo 259821 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B2400245 : Blo 259821 2400245 := bbase (se 5 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 2400245 = 225023) (by norm_num)
theorem B401501 : Blo 259821 401501 := bbase (se 3 (by rfl) ⟨75281, by rfl⟩ : syracuseStep 401501 = 150563) (by norm_num)
theorem B663653 : Blo 259821 663653 := bbase (se 4 (by rfl) ⟨62217, by rfl⟩ : syracuseStep 663653 = 124435) (by norm_num)
theorem B1351781 : Blo 259821 1351781 := bbase (se 4 (by rfl) ⟨126729, by rfl⟩ : syracuseStep 1351781 = 253459) (by norm_num)
theorem B991349 : Blo 259821 991349 := bbase (se 5 (by rfl) ⟨46469, by rfl⟩ : syracuseStep 991349 = 92939) (by norm_num)
theorem B2990357 : Blo 259821 2990357 := bbase (se 6 (by rfl) ⟨70086, by rfl⟩ : syracuseStep 2990357 = 140173) (by norm_num)
theorem B500021 : Blo 259821 500021 := bbase (se 5 (by rfl) ⟨23438, by rfl⟩ : syracuseStep 500021 = 46877) (by norm_num)
theorem B1253717 : Blo 259821 1253717 := bbase (se 10 (by rfl) ⟨1836, by rfl⟩ : syracuseStep 1253717 = 3673) (by norm_num)
theorem B598421 : Blo 259821 598421 := bbase (se 6 (by rfl) ⟨14025, by rfl⟩ : syracuseStep 598421 = 28051) (by norm_num)
theorem B663997 : Blo 259821 663997 := bbase (se 3 (by rfl) ⟨124499, by rfl⟩ : syracuseStep 663997 = 248999) (by norm_num)
theorem B1122821 : Blo 259821 1122821 := bbase (se 4 (by rfl) ⟨105264, by rfl⟩ : syracuseStep 1122821 = 210529) (by norm_num)
theorem B631309 : Blo 259821 631309 := bbase (se 3 (by rfl) ⟨118370, by rfl⟩ : syracuseStep 631309 = 236741) (by norm_num)
theorem B664109 : Blo 259821 664109 := bbase (se 3 (by rfl) ⟨124520, by rfl⟩ : syracuseStep 664109 = 249041) (by norm_num)
theorem B500269 : Blo 259821 500269 := bbase (se 3 (by rfl) ⟨93800, by rfl⟩ : syracuseStep 500269 = 187601) (by norm_num)
theorem B434765 : Blo 259821 434765 := bbase (se 3 (by rfl) ⟨81518, by rfl⟩ : syracuseStep 434765 = 163037) (by norm_num)
theorem B500413 : Blo 259821 500413 := bbase (se 3 (by rfl) ⟨93827, by rfl⟩ : syracuseStep 500413 = 187655) (by norm_num)
theorem B664301 : Blo 259821 664301 := bbase (se 3 (by rfl) ⟨124556, by rfl⟩ : syracuseStep 664301 = 249113) (by norm_num)
theorem B500573 : Blo 259821 500573 := bbase (se 3 (by rfl) ⟨93857, by rfl⟩ : syracuseStep 500573 = 187715) (by norm_num)
theorem B1319813 : Blo 259821 1319813 := bbase (se 4 (by rfl) ⟨123732, by rfl⟩ : syracuseStep 1319813 = 247465) (by norm_num)
theorem B500717 : Blo 259821 500717 := bbase (se 3 (by rfl) ⟨93884, by rfl⟩ : syracuseStep 500717 = 187769) (by norm_num)
theorem B664645 : Blo 259821 664645 := bbase (se 4 (by rfl) ⟨62310, by rfl⟩ : syracuseStep 664645 = 124621) (by norm_num)
theorem B631925 : Blo 259821 631925 := bbase (se 5 (by rfl) ⟨29621, by rfl⟩ : syracuseStep 631925 = 59243) (by norm_num)
theorem B664757 : Blo 259821 664757 := bbase (se 5 (by rfl) ⟨31160, by rfl⟩ : syracuseStep 664757 = 62321) (by norm_num)
theorem B1352933 : Blo 259821 1352933 := bbase (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) (by norm_num)
theorem B992533 : Blo 259821 992533 := bbase (se 6 (by rfl) ⟨23262, by rfl⟩ : syracuseStep 992533 = 46525) (by norm_num)
theorem B370013 : Blo 259821 370013 := bbase (se 3 (by rfl) ⟨69377, by rfl⟩ : syracuseStep 370013 = 138755) (by norm_num)
theorem B599405 : Blo 259821 599405 := bbase (se 3 (by rfl) ⟨112388, by rfl⟩ : syracuseStep 599405 = 224777) (by norm_num)
theorem B664949 : Blo 259821 664949 := bbase (se 5 (by rfl) ⟨31169, by rfl⟩ : syracuseStep 664949 = 62339) (by norm_num)
theorem B533989 : Blo 259821 533989 := bbase (se 4 (by rfl) ⟨50061, by rfl⟩ : syracuseStep 533989 = 100123) (by norm_num)
theorem B992837 : Blo 259821 992837 := bbase (se 4 (by rfl) ⟨93078, by rfl⟩ : syracuseStep 992837 = 186157) (by norm_num)
theorem B1484405 : Blo 259821 1484405 := bbase (se 5 (by rfl) ⟨69581, by rfl⟩ : syracuseStep 1484405 = 139163) (by norm_num)
theorem B566957 : Blo 259821 566957 := bbase (se 3 (by rfl) ⟨106304, by rfl⟩ : syracuseStep 566957 = 212609) (by norm_num)
theorem B665293 : Blo 259821 665293 := bbase (se 3 (by rfl) ⟨124742, by rfl⟩ : syracuseStep 665293 = 249485) (by norm_num)
theorem B665405 : Blo 259821 665405 := bbase (se 3 (by rfl) ⟨124763, by rfl⟩ : syracuseStep 665405 = 249527) (by norm_num)
theorem B632693 : Blo 259821 632693 := bbase (se 5 (by rfl) ⟨29657, by rfl⟩ : syracuseStep 632693 = 59315) (by norm_num)
theorem B632701 : Blo 259821 632701 := bbase (se 3 (by rfl) ⟨118631, by rfl⟩ : syracuseStep 632701 = 237263) (by norm_num)
theorem B534509 : Blo 259821 534509 := bbase (se 3 (by rfl) ⟨100220, by rfl⟩ : syracuseStep 534509 = 200441) (by norm_num)
theorem B665597 : Blo 259821 665597 := bbase (se 3 (by rfl) ⟨124799, by rfl⟩ : syracuseStep 665597 = 249599) (by norm_num)
theorem B370765 : Blo 259821 370765 := bbase (se 3 (by rfl) ⟨69518, by rfl⟩ : syracuseStep 370765 = 139037) (by norm_num)
theorem B600173 : Blo 259821 600173 := bbase (se 3 (by rfl) ⟨112532, by rfl⟩ : syracuseStep 600173 = 225065) (by norm_num)
theorem B1321109 : Blo 259821 1321109 := bbase (se 6 (by rfl) ⟨30963, by rfl⟩ : syracuseStep 1321109 = 61927) (by norm_num)
theorem B469157 : Blo 259821 469157 := bbase (se 4 (by rfl) ⟨43983, by rfl⟩ : syracuseStep 469157 = 87967) (by norm_num)
theorem B895157 : Blo 259821 895157 := bbase (se 5 (by rfl) ⟨41960, by rfl⟩ : syracuseStep 895157 = 83921) (by norm_num)
theorem B1124597 : Blo 259821 1124597 := bbase (se 5 (by rfl) ⟨52715, by rfl⟩ : syracuseStep 1124597 = 105431) (by norm_num)
theorem B665941 : Blo 259821 665941 := bbase (se 10 (by rfl) ⟨975, by rfl⟩ : syracuseStep 665941 = 1951) (by norm_num)
theorem B666053 : Blo 259821 666053 := bbase (se 4 (by rfl) ⟨62442, by rfl⟩ : syracuseStep 666053 = 124885) (by norm_num)
theorem B1124837 : Blo 259821 1124837 := bbase (se 4 (by rfl) ⟨105453, by rfl⟩ : syracuseStep 1124837 = 210907) (by norm_num)
theorem B666245 : Blo 259821 666245 := bbase (se 4 (by rfl) ⟨62460, by rfl⟩ : syracuseStep 666245 = 124921) (by norm_num)
theorem B633509 : Blo 259821 633509 := bbase (se 4 (by rfl) ⟨59391, by rfl⟩ : syracuseStep 633509 = 118783) (by norm_num)
theorem B404165 : Blo 259821 404165 := bbase (se 4 (by rfl) ⟨37890, by rfl⟩ : syracuseStep 404165 = 75781) (by norm_num)
theorem B469813 : Blo 259821 469813 := bbase (se 5 (by rfl) ⟨22022, by rfl⟩ : syracuseStep 469813 = 44045) (by norm_num)
theorem B371557 : Blo 259821 371557 := bbase (se 4 (by rfl) ⟨34833, by rfl⟩ : syracuseStep 371557 = 69667) (by norm_num)
theorem B666589 : Blo 259821 666589 := bbase (se 3 (by rfl) ⟨124985, by rfl⟩ : syracuseStep 666589 = 249971) (by norm_num)
theorem B601157 : Blo 259821 601157 := bbase (se 4 (by rfl) ⟨56358, by rfl⟩ : syracuseStep 601157 = 112717) (by norm_num)
theorem B666701 : Blo 259821 666701 := bbase (se 3 (by rfl) ⟨125006, by rfl⟩ : syracuseStep 666701 = 250013) (by norm_num)
theorem B601229 : Blo 259821 601229 := bbase (se 3 (by rfl) ⟨112730, by rfl⟩ : syracuseStep 601229 = 225461) (by norm_num)
theorem B797845 : Blo 259821 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B371893 : Blo 259821 371893 := bbase (se 5 (by rfl) ⟨17432, by rfl⟩ : syracuseStep 371893 = 34865) (by norm_num)
theorem B666893 : Blo 259821 666893 := bbase (se 3 (by rfl) ⟨125042, by rfl⟩ : syracuseStep 666893 = 250085) (by norm_num)
theorem B372109 : Blo 259821 372109 := bbase (se 3 (by rfl) ⟨69770, by rfl⟩ : syracuseStep 372109 = 139541) (by norm_num)
theorem B1322405 : Blo 259821 1322405 := bbase (se 4 (by rfl) ⟨123975, by rfl⟩ : syracuseStep 1322405 = 247951) (by norm_num)
theorem B470605 : Blo 259821 470605 := bbase (se 3 (by rfl) ⟨88238, by rfl⟩ : syracuseStep 470605 = 176477) (by norm_num)
theorem B667237 : Blo 259821 667237 := bbase (se 4 (by rfl) ⟨62553, by rfl⟩ : syracuseStep 667237 = 125107) (by norm_num)
theorem B994949 : Blo 259821 994949 := bbase (se 4 (by rfl) ⟨93276, by rfl⟩ : syracuseStep 994949 = 186553) (by norm_num)
theorem B667349 : Blo 259821 667349 := bbase (se 7 (by rfl) ⟨7820, by rfl⟩ : syracuseStep 667349 = 15641) (by norm_num)
theorem B372485 : Blo 259821 372485 := bbase (se 4 (by rfl) ⟨34920, by rfl⟩ : syracuseStep 372485 = 69841) (by norm_num)
theorem B1486613 : Blo 259821 1486613 := bbase (se 6 (by rfl) ⟨34842, by rfl⟩ : syracuseStep 1486613 = 69685) (by norm_num)
theorem B667541 : Blo 259821 667541 := bbase (se 6 (by rfl) ⟨15645, by rfl⟩ : syracuseStep 667541 = 31291) (by norm_num)
theorem B995237 : Blo 259821 995237 := bbase (se 4 (by rfl) ⟨93303, by rfl⟩ : syracuseStep 995237 = 186607) (by norm_num)
theorem B438493 : Blo 259821 438493 := bbase (se 3 (by rfl) ⟨82217, by rfl⟩ : syracuseStep 438493 = 164435) (by norm_num)
theorem B438581 : Blo 259821 438581 := bbase (se 5 (by rfl) ⟨20558, by rfl⟩ : syracuseStep 438581 = 41117) (by norm_num)
theorem B471413 : Blo 259821 471413 := bbase (se 5 (by rfl) ⟨22097, by rfl⟩ : syracuseStep 471413 = 44195) (by norm_num)
theorem B438709 : Blo 259821 438709 := bbase (se 5 (by rfl) ⟨20564, by rfl⟩ : syracuseStep 438709 = 41129) (by norm_num)
theorem B471557 : Blo 259821 471557 := bbase (se 4 (by rfl) ⟨44208, by rfl⟩ : syracuseStep 471557 = 88417) (by norm_num)
theorem B438797 : Blo 259821 438797 := bbase (se 3 (by rfl) ⟨82274, by rfl⟩ : syracuseStep 438797 = 164549) (by norm_num)
theorem B1258021 : Blo 259821 1258021 := bbase (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) (by norm_num)
theorem B438925 : Blo 259821 438925 := bbase (se 3 (by rfl) ⟨82298, by rfl⟩ : syracuseStep 438925 = 164597) (by norm_num)
theorem B1323701 : Blo 259821 1323701 := bbase (se 5 (by rfl) ⟨62048, by rfl⟩ : syracuseStep 1323701 = 124097) (by norm_num)
theorem B504517 : Blo 259821 504517 := bbase (se 4 (by rfl) ⟨47298, by rfl⟩ : syracuseStep 504517 = 94597) (by norm_num)
theorem B439013 : Blo 259821 439013 := bbase (se 4 (by rfl) ⟨41157, by rfl⟩ : syracuseStep 439013 = 82315) (by norm_num)
theorem B439141 : Blo 259821 439141 := bbase (se 4 (by rfl) ⟨41169, by rfl⟩ : syracuseStep 439141 = 82339) (by norm_num)
theorem B1422197 : Blo 259821 1422197 := bbase (se 5 (by rfl) ⟨66665, by rfl⟩ : syracuseStep 1422197 = 133331) (by norm_num)
theorem B439229 : Blo 259821 439229 := bbase (se 3 (by rfl) ⟨82355, by rfl⟩ : syracuseStep 439229 = 164711) (by norm_num)
theorem B1029077 : Blo 259821 1029077 := bbase (se 7 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 1029077 = 24119) (by norm_num)
theorem B439357 : Blo 259821 439357 := bbase (se 3 (by rfl) ⟨82379, by rfl⟩ : syracuseStep 439357 = 164759) (by norm_num)
theorem B996421 : Blo 259821 996421 := bbase (se 4 (by rfl) ⟨93414, by rfl⟩ : syracuseStep 996421 = 186829) (by norm_num)
theorem B1979477 : Blo 259821 1979477 := bbase (se 8 (by rfl) ⟨11598, by rfl⟩ : syracuseStep 1979477 = 23197) (by norm_num)
theorem B439445 : Blo 259821 439445 := bbase (se 6 (by rfl) ⟨10299, by rfl⟩ : syracuseStep 439445 = 20599) (by norm_num)
theorem B373909 : Blo 259821 373909 := bbase (se 6 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 373909 = 17527) (by norm_num)
theorem B472277 : Blo 259821 472277 := bbase (se 7 (by rfl) ⟨5534, by rfl⟩ : syracuseStep 472277 = 11069) (by norm_num)
theorem B439573 : Blo 259821 439573 := bbase (se 6 (by rfl) ⟨10302, by rfl⟩ : syracuseStep 439573 = 20605) (by norm_num)
theorem B832837 : Blo 259821 832837 := bbase (se 4 (by rfl) ⟨78078, by rfl⟩ : syracuseStep 832837 = 156157) (by norm_num)
theorem B439661 : Blo 259821 439661 := bbase (se 3 (by rfl) ⟨82436, by rfl⟩ : syracuseStep 439661 = 164873) (by norm_num)
theorem B996725 : Blo 259821 996725 := bbase (se 5 (by rfl) ⟨46721, by rfl⟩ : syracuseStep 996725 = 93443) (by norm_num)
theorem B439789 : Blo 259821 439789 := bbase (se 3 (by rfl) ⟨82460, by rfl⟩ : syracuseStep 439789 = 164921) (by norm_num)
theorem B439877 : Blo 259821 439877 := bbase (se 4 (by rfl) ⟨41238, by rfl⟩ : syracuseStep 439877 = 82477) (by norm_num)
theorem B440005 : Blo 259821 440005 := bbase (se 4 (by rfl) ⟨41250, by rfl⟩ : syracuseStep 440005 = 82501) (by norm_num)
theorem B833237 : Blo 259821 833237 := bbase (se 7 (by rfl) ⟨9764, by rfl⟩ : syracuseStep 833237 = 19529) (by norm_num)
theorem B374501 : Blo 259821 374501 := bbase (se 4 (by rfl) ⟨35109, by rfl⟩ : syracuseStep 374501 = 70219) (by norm_num)
theorem B440093 : Blo 259821 440093 := bbase (se 3 (by rfl) ⟨82517, by rfl⟩ : syracuseStep 440093 = 165035) (by norm_num)
theorem B374581 : Blo 259821 374581 := bbase (se 5 (by rfl) ⟨17558, by rfl⟩ : syracuseStep 374581 = 35117) (by norm_num)
theorem B2537365 : Blo 259821 2537365 := bbase (se 6 (by rfl) ⟨59469, by rfl⟩ : syracuseStep 2537365 = 118939) (by norm_num)
theorem B440221 : Blo 259821 440221 := bbase (se 3 (by rfl) ⟨82541, by rfl⟩ : syracuseStep 440221 = 165083) (by norm_num)
theorem B1062821 : Blo 259821 1062821 := bbase (se 4 (by rfl) ⟨99639, by rfl⟩ : syracuseStep 1062821 = 199279) (by norm_num)
theorem B374701 : Blo 259821 374701 := bbase (se 3 (by rfl) ⟨70256, by rfl⟩ : syracuseStep 374701 = 140513) (by norm_num)
theorem B1324997 : Blo 259821 1324997 := bbase (se 4 (by rfl) ⟨124218, by rfl⟩ : syracuseStep 1324997 = 248437) (by norm_num)
theorem B702437 : Blo 259821 702437 := bbase (se 4 (by rfl) ⟨65853, by rfl⟩ : syracuseStep 702437 = 131707) (by norm_num)
theorem B440309 : Blo 259821 440309 := bbase (se 5 (by rfl) ⟨20639, by rfl⟩ : syracuseStep 440309 = 41279) (by norm_num)
theorem B374797 : Blo 259821 374797 := bbase (se 3 (by rfl) ⟨70274, by rfl⟩ : syracuseStep 374797 = 140549) (by norm_num)
theorem B4110421 : Blo 259821 4110421 := bbase (se 8 (by rfl) ⟨24084, by rfl⟩ : syracuseStep 4110421 = 48169) (by norm_num)
theorem B440437 : Blo 259821 440437 := bbase (se 5 (by rfl) ⟨20645, by rfl⟩ : syracuseStep 440437 = 41291) (by norm_num)
theorem B440525 : Blo 259821 440525 := bbase (se 3 (by rfl) ⟨82598, by rfl⟩ : syracuseStep 440525 = 165197) (by norm_num)
theorem B669941 : Blo 259821 669941 := bbase (se 5 (by rfl) ⟨31403, by rfl⟩ : syracuseStep 669941 = 62807) (by norm_num)
theorem B899381 : Blo 259821 899381 := bbase (se 5 (by rfl) ⟨42158, by rfl⟩ : syracuseStep 899381 = 84317) (by norm_num)
theorem B440653 : Blo 259821 440653 := bbase (se 3 (by rfl) ⟨82622, by rfl⟩ : syracuseStep 440653 = 165245) (by norm_num)
theorem B440741 : Blo 259821 440741 := bbase (se 4 (by rfl) ⟨41319, by rfl⟩ : syracuseStep 440741 = 82639) (by norm_num)
theorem B375293 : Blo 259821 375293 := bbase (se 3 (by rfl) ⟨70367, by rfl⟩ : syracuseStep 375293 = 140735) (by norm_num)
theorem B440869 : Blo 259821 440869 := bbase (se 4 (by rfl) ⟨41331, by rfl⟩ : syracuseStep 440869 = 82663) (by norm_num)
theorem B440957 : Blo 259821 440957 := bbase (se 3 (by rfl) ⟨82679, by rfl⟩ : syracuseStep 440957 = 165359) (by norm_num)
theorem B441085 : Blo 259821 441085 := bbase (se 3 (by rfl) ⟨82703, by rfl⟩ : syracuseStep 441085 = 165407) (by norm_num)
theorem B441173 : Blo 259821 441173 := bbase (se 9 (by rfl) ⟨1292, by rfl⟩ : syracuseStep 441173 = 2585) (by norm_num)
theorem B1882997 : Blo 259821 1882997 := bbase (se 5 (by rfl) ⟨88265, by rfl⟩ : syracuseStep 1882997 = 176531) (by norm_num)
theorem B441301 : Blo 259821 441301 := bbase (se 7 (by rfl) ⟨5171, by rfl⟩ : syracuseStep 441301 = 10343) (by norm_num)
theorem B375797 : Blo 259821 375797 := bbase (se 5 (by rfl) ⟨17615, by rfl⟩ : syracuseStep 375797 = 35231) (by norm_num)
theorem B670709 : Blo 259821 670709 := bbase (se 5 (by rfl) ⟨31439, by rfl⟩ : syracuseStep 670709 = 62879) (by norm_num)
theorem B441389 : Blo 259821 441389 := bbase (se 3 (by rfl) ⟨82760, by rfl⟩ : syracuseStep 441389 = 165521) (by norm_num)
theorem B277553 : Blo 259821 277553 := bbase (se 2 (by rfl) ⟨104082, by rfl⟩ : syracuseStep 277553 = 208165) (by norm_num)
theorem B441517 : Blo 259821 441517 := bbase (se 3 (by rfl) ⟨82784, by rfl⟩ : syracuseStep 441517 = 165569) (by norm_num)
theorem B1326293 : Blo 259821 1326293 := bbase (se 7 (by rfl) ⟨15542, by rfl⟩ : syracuseStep 1326293 = 31085) (by norm_num)
theorem B441605 : Blo 259821 441605 := bbase (se 4 (by rfl) ⟨41400, by rfl⟩ : syracuseStep 441605 = 82801) (by norm_num)
theorem B441733 : Blo 259821 441733 := bbase (se 4 (by rfl) ⟨41412, by rfl⟩ : syracuseStep 441733 = 82825) (by norm_num)
theorem B1883573 : Blo 259821 1883573 := bbase (se 5 (by rfl) ⟨88292, by rfl⟩ : syracuseStep 1883573 = 176585) (by norm_num)
theorem B998837 : Blo 259821 998837 := bbase (se 5 (by rfl) ⟨46820, by rfl⟩ : syracuseStep 998837 = 93641) (by norm_num)
theorem B4996565 : Blo 259821 4996565 := bbase (se 7 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 4996565 = 117107) (by norm_num)
theorem B1686997 : Blo 259821 1686997 := bbase (se 7 (by rfl) ⟨19769, by rfl⟩ : syracuseStep 1686997 = 39539) (by norm_num)
theorem B441821 : Blo 259821 441821 := bbase (se 3 (by rfl) ⟨82841, by rfl⟩ : syracuseStep 441821 = 165683) (by norm_num)
theorem B277997 : Blo 259821 277997 := bbase (se 3 (by rfl) ⟨52124, by rfl⟩ : syracuseStep 277997 = 104249) (by norm_num)
theorem B900629 : Blo 259821 900629 := bbase (se 6 (by rfl) ⟨21108, by rfl⟩ : syracuseStep 900629 = 42217) (by norm_num)
theorem B441949 : Blo 259821 441949 := bbase (se 3 (by rfl) ⟨82865, by rfl⟩ : syracuseStep 441949 = 165731) (by norm_num)
theorem B442037 : Blo 259821 442037 := bbase (se 5 (by rfl) ⟨20720, by rfl⟩ : syracuseStep 442037 = 41441) (by norm_num)
theorem B999125 : Blo 259821 999125 := bbase (se 7 (by rfl) ⟨11708, by rfl⟩ : syracuseStep 999125 = 23417) (by norm_num)
theorem B278245 : Blo 259821 278245 := bbase (se 4 (by rfl) ⟨26085, by rfl⟩ : syracuseStep 278245 = 52171) (by norm_num)
theorem B442165 : Blo 259821 442165 := bbase (se 5 (by rfl) ⟨20726, by rfl⟩ : syracuseStep 442165 = 41453) (by norm_num)
theorem B442253 : Blo 259821 442253 := bbase (se 3 (by rfl) ⟨82922, by rfl⟩ : syracuseStep 442253 = 165845) (by norm_num)
theorem B442381 : Blo 259821 442381 := bbase (se 3 (by rfl) ⟨82946, by rfl⟩ : syracuseStep 442381 = 165893) (by norm_num)
theorem B3686485 : Blo 259821 3686485 := bbase (se 8 (by rfl) ⟨21600, by rfl⟩ : syracuseStep 3686485 = 43201) (by norm_num)
theorem B442469 : Blo 259821 442469 := bbase (se 4 (by rfl) ⟨41481, by rfl⟩ : syracuseStep 442469 = 82963) (by norm_num)
theorem B278689 : Blo 259821 278689 := bbase (se 2 (by rfl) ⟨104508, by rfl⟩ : syracuseStep 278689 = 209017) (by norm_num)
theorem B278749 : Blo 259821 278749 := bbase (se 3 (by rfl) ⟨52265, by rfl⟩ : syracuseStep 278749 = 104531) (by norm_num)
theorem B442597 : Blo 259821 442597 := bbase (se 4 (by rfl) ⟨41493, by rfl⟩ : syracuseStep 442597 = 82987) (by norm_num)
theorem B1589557 : Blo 259821 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B442685 : Blo 259821 442685 := bbase (se 3 (by rfl) ⟨83003, by rfl⟩ : syracuseStep 442685 = 166007) (by norm_num)
theorem B1589653 : Blo 259821 1589653 := bbase (se 6 (by rfl) ⟨37257, by rfl⟩ : syracuseStep 1589653 = 74515) (by norm_num)
theorem B442813 : Blo 259821 442813 := bbase (se 3 (by rfl) ⟨83027, by rfl⟩ : syracuseStep 442813 = 166055) (by norm_num)
theorem B1327589 : Blo 259821 1327589 := bbase (se 4 (by rfl) ⟨124461, by rfl⟩ : syracuseStep 1327589 = 248923) (by norm_num)
theorem B442901 : Blo 259821 442901 := bbase (se 6 (by rfl) ⟨10380, by rfl⟩ : syracuseStep 442901 = 20761) (by norm_num)
theorem B279065 : Blo 259821 279065 := bbase (se 2 (by rfl) ⟨104649, by rfl⟩ : syracuseStep 279065 = 209299) (by norm_num)
theorem B443029 : Blo 259821 443029 := bbase (se 6 (by rfl) ⟨10383, by rfl⟩ : syracuseStep 443029 = 20767) (by norm_num)
theorem B705205 : Blo 259821 705205 := bbase (se 5 (by rfl) ⟨33056, by rfl⟩ : syracuseStep 705205 = 66113) (by norm_num)
theorem B541381 : Blo 259821 541381 := bbase (se 4 (by rfl) ⟨50754, by rfl⟩ : syracuseStep 541381 = 101509) (by norm_num)
theorem B443117 : Blo 259821 443117 := bbase (se 3 (by rfl) ⟨83084, by rfl⟩ : syracuseStep 443117 = 166169) (by norm_num)
theorem B1262405 : Blo 259821 1262405 := bbase (se 4 (by rfl) ⟨118350, by rfl⟩ : syracuseStep 1262405 = 236701) (by norm_num)
theorem B443245 : Blo 259821 443245 := bbase (se 3 (by rfl) ⟨83108, by rfl⟩ : syracuseStep 443245 = 166217) (by norm_num)
theorem B1000309 : Blo 259821 1000309 := bbase (se 5 (by rfl) ⟨46889, by rfl⟩ : syracuseStep 1000309 = 93779) (by norm_num)
theorem B443333 : Blo 259821 443333 := bbase (se 4 (by rfl) ⟨41562, by rfl⟩ : syracuseStep 443333 = 83125) (by norm_num)
theorem B279509 : Blo 259821 279509 := bbase (se 7 (by rfl) ⟨3275, by rfl⟩ : syracuseStep 279509 = 6551) (by norm_num)
theorem B279569 : Blo 259821 279569 := bbase (se 2 (by rfl) ⟨104838, by rfl⟩ : syracuseStep 279569 = 209677) (by norm_num)
theorem B443461 : Blo 259821 443461 := bbase (se 4 (by rfl) ⟨41574, by rfl⟩ : syracuseStep 443461 = 83149) (by norm_num)
theorem B279697 : Blo 259821 279697 := bbase (se 2 (by rfl) ⟨104886, by rfl⟩ : syracuseStep 279697 = 209773) (by norm_num)
theorem B443549 : Blo 259821 443549 := bbase (se 3 (by rfl) ⟨83165, by rfl⟩ : syracuseStep 443549 = 166331) (by norm_num)
theorem B1000613 : Blo 259821 1000613 := bbase (se 4 (by rfl) ⟨93807, by rfl⟩ : syracuseStep 1000613 = 187615) (by norm_num)
theorem B312545 : Blo 259821 312545 := bbase (se 2 (by rfl) ⟨117204, by rfl⟩ : syracuseStep 312545 = 234409) (by norm_num)
theorem B312593 : Blo 259821 312593 := bbase (se 2 (by rfl) ⟨117222, by rfl⟩ : syracuseStep 312593 = 234445) (by norm_num)
theorem B443677 : Blo 259821 443677 := bbase (se 3 (by rfl) ⟨83189, by rfl⟩ : syracuseStep 443677 = 166379) (by norm_num)
theorem B443765 : Blo 259821 443765 := bbase (se 5 (by rfl) ⟨20801, by rfl⟩ : syracuseStep 443765 = 41603) (by norm_num)
theorem B837029 : Blo 259821 837029 := bbase (se 4 (by rfl) ⟨78471, by rfl⟩ : syracuseStep 837029 = 156943) (by norm_num)
theorem B443893 : Blo 259821 443893 := bbase (se 5 (by rfl) ⟨20807, by rfl⟩ : syracuseStep 443893 = 41615) (by norm_num)
theorem B1066517 : Blo 259821 1066517 := bbase (se 6 (by rfl) ⟨24996, by rfl⟩ : syracuseStep 1066517 = 49993) (by norm_num)
theorem B280141 : Blo 259821 280141 := bbase (se 3 (by rfl) ⟨52526, by rfl⟩ : syracuseStep 280141 = 105053) (by norm_num)
theorem B443981 : Blo 259821 443981 := bbase (se 3 (by rfl) ⟨83246, by rfl⟩ : syracuseStep 443981 = 166493) (by norm_num)
theorem B673429 : Blo 259821 673429 := bbase (se 6 (by rfl) ⟨15783, by rfl⟩ : syracuseStep 673429 = 31567) (by norm_num)
theorem B280261 : Blo 259821 280261 := bbase (se 4 (by rfl) ⟨26274, by rfl⟩ : syracuseStep 280261 = 52549) (by norm_num)
theorem B444109 : Blo 259821 444109 := bbase (se 3 (by rfl) ⟨83270, by rfl⟩ : syracuseStep 444109 = 166541) (by norm_num)
theorem B1328885 : Blo 259821 1328885 := bbase (se 5 (by rfl) ⟨62291, by rfl⟩ : syracuseStep 1328885 = 124583) (by norm_num)
theorem B3786517 : Blo 259821 3786517 := bbase (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) (by norm_num)
theorem B444197 : Blo 259821 444197 := bbase (se 4 (by rfl) ⟨41643, by rfl⟩ : syracuseStep 444197 = 83287) (by norm_num)
theorem B313141 : Blo 259821 313141 := bbase (se 5 (by rfl) ⟨14678, by rfl⟩ : syracuseStep 313141 = 29357) (by norm_num)
theorem B444325 : Blo 259821 444325 := bbase (se 4 (by rfl) ⟨41655, by rfl⟩ : syracuseStep 444325 = 83311) (by norm_num)
theorem B280513 : Blo 259821 280513 := bbase (se 2 (by rfl) ⟨105192, by rfl⟩ : syracuseStep 280513 = 210385) (by norm_num)
theorem B280517 : Blo 259821 280517 := bbase (se 4 (by rfl) ⟨26298, by rfl⟩ : syracuseStep 280517 = 52597) (by norm_num)
theorem B444413 : Blo 259821 444413 := bbase (se 3 (by rfl) ⟨83327, by rfl⟩ : syracuseStep 444413 = 166655) (by norm_num)
theorem B444541 : Blo 259821 444541 := bbase (se 3 (by rfl) ⟨83351, by rfl⟩ : syracuseStep 444541 = 166703) (by norm_num)
theorem B444629 : Blo 259821 444629 := bbase (se 7 (by rfl) ⟨5210, by rfl⟩ : syracuseStep 444629 = 10421) (by norm_num)
theorem B313621 : Blo 259821 313621 := bbase (se 6 (by rfl) ⟨7350, by rfl⟩ : syracuseStep 313621 = 14701) (by norm_num)
theorem B444757 : Blo 259821 444757 := bbase (se 10 (by rfl) ⟨651, by rfl⟩ : syracuseStep 444757 = 1303) (by norm_num)
theorem B444845 : Blo 259821 444845 := bbase (se 3 (by rfl) ⟨83408, by rfl⟩ : syracuseStep 444845 = 166817) (by norm_num)
theorem B838117 : Blo 259821 838117 := bbase (se 4 (by rfl) ⟨78573, by rfl⟩ : syracuseStep 838117 = 157147) (by norm_num)
theorem B281081 : Blo 259821 281081 := bbase (se 2 (by rfl) ⟨105405, by rfl⟩ : syracuseStep 281081 = 210811) (by norm_num)
theorem B444973 : Blo 259821 444973 := bbase (se 3 (by rfl) ⟨83432, by rfl⟩ : syracuseStep 444973 = 166865) (by norm_num)
theorem B739925 : Blo 259821 739925 := bbase (se 8 (by rfl) ⟨4335, by rfl⟩ : syracuseStep 739925 = 8671) (by norm_num)
theorem B445061 : Blo 259821 445061 := bbase (se 4 (by rfl) ⟨41724, by rfl⟩ : syracuseStep 445061 = 83449) (by norm_num)
theorem B281269 : Blo 259821 281269 := bbase (se 5 (by rfl) ⟨13184, by rfl⟩ : syracuseStep 281269 = 26369) (by norm_num)
theorem B445189 : Blo 259821 445189 := bbase (se 4 (by rfl) ⟨41736, by rfl⟩ : syracuseStep 445189 = 83473) (by norm_num)
theorem B740117 : Blo 259821 740117 := bbase (se 6 (by rfl) ⟨17346, by rfl⟩ : syracuseStep 740117 = 34693) (by norm_num)
theorem B2378645 : Blo 259821 2378645 := bbase (se 6 (by rfl) ⟨55749, by rfl⟩ : syracuseStep 2378645 = 111499) (by norm_num)
theorem B1330181 : Blo 259821 1330181 := bbase (se 4 (by rfl) ⟨124704, by rfl⟩ : syracuseStep 1330181 = 249409) (by norm_num)
theorem B314501 : Blo 259821 314501 := bbase (se 4 (by rfl) ⟨29484, by rfl⟩ : syracuseStep 314501 = 58969) (by norm_num)
theorem B314617 : Blo 259821 314617 := bbase (se 2 (by rfl) ⟨117981, by rfl⟩ : syracuseStep 314617 = 235963) (by norm_num)
theorem B314813 : Blo 259821 314813 := bbase (se 3 (by rfl) ⟨59027, by rfl⟩ : syracuseStep 314813 = 118055) (by norm_num)
theorem B970181 : Blo 259821 970181 := bbase (se 4 (by rfl) ⟨90954, by rfl⟩ : syracuseStep 970181 = 181909) (by norm_num)
theorem B839285 : Blo 259821 839285 := bbase (se 5 (by rfl) ⟨39341, by rfl⟩ : syracuseStep 839285 = 78683) (by norm_num)
theorem B741109 : Blo 259821 741109 := bbase (se 5 (by rfl) ⟨34739, by rfl⟩ : syracuseStep 741109 = 69479) (by norm_num)
theorem B315361 : Blo 259821 315361 := bbase (se 2 (by rfl) ⟨118260, by rfl⟩ : syracuseStep 315361 = 236521) (by norm_num)
theorem B708581 : Blo 259821 708581 := bbase (se 4 (by rfl) ⟨66429, by rfl⟩ : syracuseStep 708581 = 132859) (by norm_num)
theorem B577573 : Blo 259821 577573 := bbase (se 4 (by rfl) ⟨54147, by rfl⟩ : syracuseStep 577573 = 108295) (by norm_num)
theorem B315505 : Blo 259821 315505 := bbase (se 2 (by rfl) ⟨118314, by rfl⟩ : syracuseStep 315505 = 236629) (by norm_num)
theorem B938213 : Blo 259821 938213 := bbase (se 4 (by rfl) ⟨87957, by rfl⟩ : syracuseStep 938213 = 175915) (by norm_num)
theorem B1331477 : Blo 259821 1331477 := bbase (se 6 (by rfl) ⟨31206, by rfl⟩ : syracuseStep 1331477 = 62413) (by norm_num)
theorem B709013 : Blo 259821 709013 := bbase (se 6 (by rfl) ⟨16617, by rfl⟩ : syracuseStep 709013 = 33235) (by norm_num)
theorem B283133 : Blo 259821 283133 := bbase (se 3 (by rfl) ⟨53087, by rfl⟩ : syracuseStep 283133 = 106175) (by norm_num)
theorem B1987253 : Blo 259821 1987253 := bbase (se 5 (by rfl) ⟨93152, by rfl⟩ : syracuseStep 1987253 = 186305) (by norm_num)
theorem B938789 : Blo 259821 938789 := bbase (se 4 (by rfl) ⟨88011, by rfl⟩ : syracuseStep 938789 = 176023) (by norm_num)
theorem B742213 : Blo 259821 742213 := bbase (se 4 (by rfl) ⟨69582, by rfl⟩ : syracuseStep 742213 = 139165) (by norm_num)
theorem B7131989 : Blo 259821 7131989 := bbase (se 9 (by rfl) ⟨20894, by rfl⟩ : syracuseStep 7131989 = 41789) (by norm_num)
theorem B447365 : Blo 259821 447365 := bbase (se 4 (by rfl) ⟨41940, by rfl⟩ : syracuseStep 447365 = 83881) (by norm_num)
theorem B316553 : Blo 259821 316553 := bbase (se 2 (by rfl) ⟨118707, by rfl⟩ : syracuseStep 316553 = 237415) (by norm_num)
theorem B1267093 : Blo 259821 1267093 := bbase (se 6 (by rfl) ⟨29697, by rfl⟩ : syracuseStep 1267093 = 59395) (by norm_num)
theorem B841141 : Blo 259821 841141 := bbase (se 5 (by rfl) ⟨39428, by rfl⟩ : syracuseStep 841141 = 78857) (by norm_num)
theorem B1496501 : Blo 259821 1496501 := bbase (se 5 (by rfl) ⟨70148, by rfl⟩ : syracuseStep 1496501 = 140297) (by norm_num)
theorem B316885 : Blo 259821 316885 := bbase (se 7 (by rfl) ⟨3713, by rfl⟩ : syracuseStep 316885 = 7427) (by norm_num)
theorem B1136117 : Blo 259821 1136117 := bbase (se 5 (by rfl) ⟨53255, by rfl⟩ : syracuseStep 1136117 = 106511) (by norm_num)
theorem B1332773 : Blo 259821 1332773 := bbase (se 4 (by rfl) ⟨124947, by rfl⟩ : syracuseStep 1332773 = 249895) (by norm_num)
theorem B284293 : Blo 259821 284293 := bbase (se 4 (by rfl) ⟨26652, by rfl⟩ : syracuseStep 284293 = 53305) (by norm_num)
theorem B480901 : Blo 259821 480901 := bbase (se 4 (by rfl) ⟨45084, by rfl⟩ : syracuseStep 480901 = 90169) (by norm_num)
theorem B939941 : Blo 259821 939941 := bbase (se 4 (by rfl) ⟨88119, by rfl⟩ : syracuseStep 939941 = 176239) (by norm_num)
theorem B448453 : Blo 259821 448453 := bbase (se 4 (by rfl) ⟨42042, by rfl⟩ : syracuseStep 448453 = 84085) (by norm_num)
theorem B2414645 : Blo 259821 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B710741 : Blo 259821 710741 := bbase (se 8 (by rfl) ⟨4164, by rfl⟩ : syracuseStep 710741 = 8329) (by norm_num)
theorem B2513045 : Blo 259821 2513045 := bbase (se 6 (by rfl) ⟨58899, by rfl⟩ : syracuseStep 2513045 = 117799) (by norm_num)
theorem B612613 : Blo 259821 612613 := bbase (se 4 (by rfl) ⟨57432, by rfl⟩ : syracuseStep 612613 = 114865) (by norm_num)
theorem B743717 : Blo 259821 743717 := bbase (se 4 (by rfl) ⟨69723, by rfl⟩ : syracuseStep 743717 = 139447) (by norm_num)
theorem B842501 : Blo 259821 842501 := bbase (se 4 (by rfl) ⟨78984, by rfl⟩ : syracuseStep 842501 = 157969) (by norm_num)
theorem B1334069 : Blo 259821 1334069 := bbase (se 5 (by rfl) ⟨62534, by rfl⟩ : syracuseStep 1334069 = 125069) (by norm_num)
theorem B416573 : Blo 259821 416573 := bbase (se 3 (by rfl) ⟨78107, by rfl⟩ : syracuseStep 416573 = 156215) (by norm_num)
theorem B2087765 : Blo 259821 2087765 := bbase (se 9 (by rfl) ⟨6116, by rfl⟩ : syracuseStep 2087765 = 12233) (by norm_num)
theorem B416669 : Blo 259821 416669 := bbase (se 3 (by rfl) ⟨78125, by rfl⟩ : syracuseStep 416669 = 156251) (by norm_num)
theorem B416701 : Blo 259821 416701 := bbase (se 3 (by rfl) ⟨78131, by rfl⟩ : syracuseStep 416701 = 156263) (by norm_num)
theorem B973973 : Blo 259821 973973 := bbase (se 6 (by rfl) ⟨22827, by rfl⟩ : syracuseStep 973973 = 45655) (by norm_num)
theorem B318641 : Blo 259821 318641 := bbase (se 2 (by rfl) ⟨119490, by rfl⟩ : syracuseStep 318641 = 238981) (by norm_num)
theorem B2022965 : Blo 259821 2022965 := bbase (se 5 (by rfl) ⟨94826, by rfl⟩ : syracuseStep 2022965 = 189653) (by norm_num)
theorem B941701 : Blo 259821 941701 := bbase (se 4 (by rfl) ⟨88284, by rfl⟩ : syracuseStep 941701 = 176569) (by norm_num)
theorem B2219669 : Blo 259821 2219669 := bbase (se 6 (by rfl) ⟨52023, by rfl⟩ : syracuseStep 2219669 = 104047) (by norm_num)
theorem B745301 : Blo 259821 745301 := bbase (se 9 (by rfl) ⟨2183, by rfl⟩ : syracuseStep 745301 = 4367) (by norm_num)
theorem B712613 : Blo 259821 712613 := bbase (se 4 (by rfl) ⟨66807, by rfl⟩ : syracuseStep 712613 = 133615) (by norm_num)
theorem B942005 : Blo 259821 942005 := bbase (se 5 (by rfl) ⟨44156, by rfl⟩ : syracuseStep 942005 = 88313) (by norm_num)
theorem B1335365 : Blo 259821 1335365 := bbase (se 4 (by rfl) ⟨125190, by rfl⟩ : syracuseStep 1335365 = 250381) (by norm_num)
theorem B909413 : Blo 259821 909413 := bbase (se 4 (by rfl) ⟨85257, by rfl⟩ : syracuseStep 909413 = 170515) (by norm_num)
theorem B450773 : Blo 259821 450773 := bbase (se 7 (by rfl) ⟨5282, by rfl⟩ : syracuseStep 450773 = 10565) (by norm_num)
theorem B909605 : Blo 259821 909605 := bbase (se 4 (by rfl) ⟨85275, by rfl⟩ : syracuseStep 909605 = 170551) (by norm_num)
theorem B418213 : Blo 259821 418213 := bbase (se 4 (by rfl) ⟨39207, by rfl⟩ : syracuseStep 418213 = 78415) (by norm_num)
theorem B877013 : Blo 259821 877013 := bbase (se 7 (by rfl) ⟨10277, by rfl⟩ : syracuseStep 877013 = 20555) (by norm_num)
theorem B745973 : Blo 259821 745973 := bbase (se 5 (by rfl) ⟨34967, by rfl⟩ : syracuseStep 745973 = 69935) (by norm_num)
theorem B1696565 : Blo 259821 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B877445 : Blo 259821 877445 := bbase (se 4 (by rfl) ⟨82260, by rfl⟩ : syracuseStep 877445 = 164521) (by norm_num)
theorem B746405 : Blo 259821 746405 := bbase (se 4 (by rfl) ⟨69975, by rfl⟩ : syracuseStep 746405 = 139951) (by norm_num)
theorem B1369045 : Blo 259821 1369045 := bbase (se 7 (by rfl) ⟨16043, by rfl⟩ : syracuseStep 1369045 = 32087) (by norm_num)
theorem B418925 : Blo 259821 418925 := bbase (se 3 (by rfl) ⟨78548, by rfl⟩ : syracuseStep 418925 = 157097) (by norm_num)
theorem B877877 : Blo 259821 877877 := bbase (se 5 (by rfl) ⟨41150, by rfl⟩ : syracuseStep 877877 = 82301) (by norm_num)
theorem B386365 : Blo 259821 386365 := bbase (se 3 (by rfl) ⟨72443, by rfl⟩ : syracuseStep 386365 = 144887) (by norm_num)
theorem B747157 : Blo 259821 747157 := bbase (se 6 (by rfl) ⟨17511, by rfl⟩ : syracuseStep 747157 = 35023) (by norm_num)
theorem B648901 : Blo 259821 648901 := bbase (se 4 (by rfl) ⟨60834, by rfl⟩ : syracuseStep 648901 = 121669) (by norm_num)
theorem B878309 : Blo 259821 878309 := bbase (se 4 (by rfl) ⟨82341, by rfl⟩ : syracuseStep 878309 = 164683) (by norm_num)
theorem B1173253 : Blo 259821 1173253 := bbase (se 4 (by rfl) ⟨109992, by rfl⟩ : syracuseStep 1173253 = 219985) (by norm_num)
theorem B419597 : Blo 259821 419597 := bbase (se 3 (by rfl) ⟨78674, by rfl⟩ : syracuseStep 419597 = 157349) (by norm_num)
theorem B878741 : Blo 259821 878741 := bbase (se 6 (by rfl) ⟨20595, by rfl⟩ : syracuseStep 878741 = 41191) (by norm_num)
theorem B3565781 : Blo 259821 3565781 := bbase (se 7 (by rfl) ⟨41786, by rfl⟩ : syracuseStep 3565781 = 83573) (by norm_num)
theorem B420109 : Blo 259821 420109 := bbase (se 3 (by rfl) ⟨78770, by rfl⟩ : syracuseStep 420109 = 157541) (by norm_num)
theorem B4483349 : Blo 259821 4483349 := bbase (se 6 (by rfl) ⟨105078, by rfl⟩ : syracuseStep 4483349 = 210157) (by norm_num)
theorem B879173 : Blo 259821 879173 := bbase (se 4 (by rfl) ⟨82422, by rfl⟩ : syracuseStep 879173 = 164845) (by norm_num)
theorem B420565 : Blo 259821 420565 := bbase (se 7 (by rfl) ⟨4928, by rfl⟩ : syracuseStep 420565 = 9857) (by norm_num)
theorem B1338133 : Blo 259821 1338133 := bbase (se 6 (by rfl) ⟨31362, by rfl⟩ : syracuseStep 1338133 = 62725) (by norm_num)
theorem B584621 : Blo 259821 584621 := bbase (se 3 (by rfl) ⟨109616, by rfl⟩ : syracuseStep 584621 = 219233) (by norm_num)
theorem B584693 : Blo 259821 584693 := bbase (se 5 (by rfl) ⟨27407, by rfl⟩ : syracuseStep 584693 = 54815) (by norm_num)
theorem B879605 : Blo 259821 879605 := bbase (se 5 (by rfl) ⟨41231, by rfl⟩ : syracuseStep 879605 = 82463) (by norm_num)
theorem B1534997 : Blo 259821 1534997 := bbase (se 6 (by rfl) ⟨35976, by rfl⟩ : syracuseStep 1534997 = 71953) (by norm_num)
theorem B584765 : Blo 259821 584765 := bbase (se 3 (by rfl) ⟨109643, by rfl⟩ : syracuseStep 584765 = 219287) (by norm_num)
theorem B584837 : Blo 259821 584837 := bbase (se 4 (by rfl) ⟨54828, by rfl⟩ : syracuseStep 584837 = 109657) (by norm_num)
theorem B1338565 : Blo 259821 1338565 := bbase (se 4 (by rfl) ⟨125490, by rfl⟩ : syracuseStep 1338565 = 250981) (by norm_num)
theorem B584909 : Blo 259821 584909 := bbase (se 3 (by rfl) ⟨109670, by rfl⟩ : syracuseStep 584909 = 219341) (by norm_num)
theorem B584981 : Blo 259821 584981 := bbase (se 6 (by rfl) ⟨13710, by rfl⟩ : syracuseStep 584981 = 27421) (by norm_num)
theorem B585053 : Blo 259821 585053 := bbase (se 3 (by rfl) ⟨109697, by rfl⟩ : syracuseStep 585053 = 219395) (by norm_num)
theorem B421237 : Blo 259821 421237 := bbase (se 5 (by rfl) ⟨19745, by rfl⟩ : syracuseStep 421237 = 39491) (by norm_num)
theorem B585125 : Blo 259821 585125 := bbase (se 4 (by rfl) ⟨54855, by rfl⟩ : syracuseStep 585125 = 109711) (by norm_num)
theorem B880037 : Blo 259821 880037 := bbase (se 4 (by rfl) ⟨82503, by rfl⟩ : syracuseStep 880037 = 165007) (by norm_num)
theorem B585197 : Blo 259821 585197 := bbase (se 3 (by rfl) ⟨109724, by rfl⟩ : syracuseStep 585197 = 219449) (by norm_num)
theorem B585269 : Blo 259821 585269 := bbase (se 5 (by rfl) ⟨27434, by rfl⟩ : syracuseStep 585269 = 54869) (by norm_num)
theorem B585341 : Blo 259821 585341 := bbase (se 3 (by rfl) ⟨109751, by rfl⟩ : syracuseStep 585341 = 219503) (by norm_num)
theorem B585413 : Blo 259821 585413 := bbase (se 4 (by rfl) ⟨54882, by rfl⟩ : syracuseStep 585413 = 109765) (by norm_num)
theorem B585485 : Blo 259821 585485 := bbase (se 3 (by rfl) ⟨109778, by rfl⟩ : syracuseStep 585485 = 219557) (by norm_num)
theorem B421661 : Blo 259821 421661 := bbase (se 3 (by rfl) ⟨79061, by rfl⟩ : syracuseStep 421661 = 158123) (by norm_num)
theorem B585557 : Blo 259821 585557 := bbase (se 9 (by rfl) ⟨1715, by rfl⟩ : syracuseStep 585557 = 3431) (by norm_num)
theorem B880469 : Blo 259821 880469 := bbase (se 9 (by rfl) ⟨2579, by rfl⟩ : syracuseStep 880469 = 5159) (by norm_num)
theorem B585629 : Blo 259821 585629 := bbase (se 3 (by rfl) ⟨109805, by rfl⟩ : syracuseStep 585629 = 219611) (by norm_num)
theorem B585701 : Blo 259821 585701 := bbase (se 4 (by rfl) ⟨54909, by rfl⟩ : syracuseStep 585701 = 109819) (by norm_num)
theorem B585773 : Blo 259821 585773 := bbase (se 3 (by rfl) ⟨109832, by rfl⟩ : syracuseStep 585773 = 219665) (by norm_num)
theorem B454717 : Blo 259821 454717 := bbase (se 3 (by rfl) ⟨85259, by rfl⟩ : syracuseStep 454717 = 170519) (by norm_num)
theorem B421949 : Blo 259821 421949 := bbase (se 3 (by rfl) ⟨79115, by rfl⟩ : syracuseStep 421949 = 158231) (by norm_num)
theorem B585845 : Blo 259821 585845 := bbase (se 5 (by rfl) ⟨27461, by rfl⟩ : syracuseStep 585845 = 54923) (by norm_num)
theorem B585917 : Blo 259821 585917 := bbase (se 3 (by rfl) ⟨109859, by rfl⟩ : syracuseStep 585917 = 219719) (by norm_num)
theorem B585989 : Blo 259821 585989 := bbase (se 4 (by rfl) ⟨54936, by rfl⟩ : syracuseStep 585989 = 109873) (by norm_num)
theorem B880901 : Blo 259821 880901 := bbase (se 4 (by rfl) ⟨82584, by rfl⟩ : syracuseStep 880901 = 165169) (by norm_num)
theorem B1995029 : Blo 259821 1995029 := bbase (se 6 (by rfl) ⟨46758, by rfl⟩ : syracuseStep 1995029 = 93517) (by norm_num)
theorem B586061 : Blo 259821 586061 := bbase (se 3 (by rfl) ⟨109886, by rfl⟩ : syracuseStep 586061 = 219773) (by norm_num)
theorem B586133 : Blo 259821 586133 := bbase (se 6 (by rfl) ⟨13737, by rfl⟩ : syracuseStep 586133 = 27475) (by norm_num)
theorem B422309 : Blo 259821 422309 := bbase (se 4 (by rfl) ⟨39591, by rfl⟩ : syracuseStep 422309 = 79183) (by norm_num)
theorem B750005 : Blo 259821 750005 := bbase (se 5 (by rfl) ⟨35156, by rfl⟩ : syracuseStep 750005 = 70313) (by norm_num)
theorem B586205 : Blo 259821 586205 := bbase (se 3 (by rfl) ⟨109913, by rfl⟩ : syracuseStep 586205 = 219827) (by norm_num)
theorem B1667573 : Blo 259821 1667573 := bbase (se 5 (by rfl) ⟨78167, by rfl⟩ : syracuseStep 1667573 = 156335) (by norm_num)
theorem B1896949 : Blo 259821 1896949 := bbase (se 5 (by rfl) ⟨88919, by rfl⟩ : syracuseStep 1896949 = 177839) (by norm_num)
theorem B2126357 : Blo 259821 2126357 := bbase (se 6 (by rfl) ⟨49836, by rfl⟩ : syracuseStep 2126357 = 99673) (by norm_num)
theorem B586277 : Blo 259821 586277 := bbase (se 4 (by rfl) ⟨54963, by rfl⟩ : syracuseStep 586277 = 109927) (by norm_num)
theorem B389741 : Blo 259821 389741 := bbase (se 3 (by rfl) ⟨73076, by rfl⟩ : syracuseStep 389741 = 146153) (by norm_num)
theorem B586349 : Blo 259821 586349 := bbase (se 3 (by rfl) ⟨109940, by rfl⟩ : syracuseStep 586349 = 219881) (by norm_num)
theorem B389765 : Blo 259821 389765 := bbase (se 4 (by rfl) ⟨36540, by rfl⟩ : syracuseStep 389765 = 73081) (by norm_num)
theorem B389789 : Blo 259821 389789 := bbase (se 3 (by rfl) ⟨73085, by rfl⟩ : syracuseStep 389789 = 146171) (by norm_num)
theorem B389813 : Blo 259821 389813 := bbase (se 5 (by rfl) ⟨18272, by rfl⟩ : syracuseStep 389813 = 36545) (by norm_num)
theorem B586421 : Blo 259821 586421 := bbase (se 5 (by rfl) ⟨27488, by rfl⟩ : syracuseStep 586421 = 54977) (by norm_num)
theorem B881333 : Blo 259821 881333 := bbase (se 5 (by rfl) ⟨41312, by rfl⟩ : syracuseStep 881333 = 82625) (by norm_num)
theorem B389837 : Blo 259821 389837 := bbase (se 3 (by rfl) ⟨73094, by rfl⟩ : syracuseStep 389837 = 146189) (by norm_num)
theorem B389861 : Blo 259821 389861 := bbase (se 4 (by rfl) ⟨36549, by rfl⟩ : syracuseStep 389861 = 73099) (by norm_num)
theorem B389885 : Blo 259821 389885 := bbase (se 3 (by rfl) ⟨73103, by rfl⟩ : syracuseStep 389885 = 146207) (by norm_num)
theorem B586493 : Blo 259821 586493 := bbase (se 3 (by rfl) ⟨109967, by rfl⟩ : syracuseStep 586493 = 219935) (by norm_num)
theorem B389909 : Blo 259821 389909 := bbase (se 6 (by rfl) ⟨9138, by rfl⟩ : syracuseStep 389909 = 18277) (by norm_num)
theorem B389933 : Blo 259821 389933 := bbase (se 3 (by rfl) ⟨73112, by rfl⟩ : syracuseStep 389933 = 146225) (by norm_num)
theorem B389957 : Blo 259821 389957 := bbase (se 4 (by rfl) ⟨36558, by rfl⟩ : syracuseStep 389957 = 73117) (by norm_num)
theorem B586565 : Blo 259821 586565 := bbase (se 4 (by rfl) ⟨54990, by rfl⟩ : syracuseStep 586565 = 109981) (by norm_num)
theorem B389981 : Blo 259821 389981 := bbase (se 3 (by rfl) ⟨73121, by rfl⟩ : syracuseStep 389981 = 146243) (by norm_num)
theorem B390005 : Blo 259821 390005 := bbase (se 5 (by rfl) ⟨18281, by rfl⟩ : syracuseStep 390005 = 36563) (by norm_num)
theorem B390029 : Blo 259821 390029 := bbase (se 3 (by rfl) ⟨73130, by rfl⟩ : syracuseStep 390029 = 146261) (by norm_num)
theorem B586637 : Blo 259821 586637 := bbase (se 3 (by rfl) ⟨109994, by rfl⟩ : syracuseStep 586637 = 219989) (by norm_num)
theorem B390053 : Blo 259821 390053 := bbase (se 4 (by rfl) ⟨36567, by rfl⟩ : syracuseStep 390053 = 73135) (by norm_num)
theorem B390077 : Blo 259821 390077 := bbase (se 3 (by rfl) ⟨73139, by rfl⟩ : syracuseStep 390077 = 146279) (by norm_num)
theorem B390101 : Blo 259821 390101 := bbase (se 7 (by rfl) ⟨4571, by rfl⟩ : syracuseStep 390101 = 9143) (by norm_num)
theorem B586709 : Blo 259821 586709 := bbase (se 7 (by rfl) ⟨6875, by rfl⟩ : syracuseStep 586709 = 13751) (by norm_num)
theorem B390125 : Blo 259821 390125 := bbase (se 3 (by rfl) ⟨73148, by rfl⟩ : syracuseStep 390125 = 146297) (by norm_num)
theorem B390149 : Blo 259821 390149 := bbase (se 4 (by rfl) ⟨36576, by rfl⟩ : syracuseStep 390149 = 73153) (by norm_num)
theorem B390173 : Blo 259821 390173 := bbase (se 3 (by rfl) ⟨73157, by rfl⟩ : syracuseStep 390173 = 146315) (by norm_num)
theorem B586781 : Blo 259821 586781 := bbase (se 3 (by rfl) ⟨110021, by rfl⟩ : syracuseStep 586781 = 220043) (by norm_num)
theorem B390197 : Blo 259821 390197 := bbase (se 5 (by rfl) ⟨18290, by rfl⟩ : syracuseStep 390197 = 36581) (by norm_num)
theorem B390221 : Blo 259821 390221 := bbase (se 3 (by rfl) ⟨73166, by rfl⟩ : syracuseStep 390221 = 146333) (by norm_num)
theorem B390245 : Blo 259821 390245 := bbase (se 4 (by rfl) ⟨36585, by rfl⟩ : syracuseStep 390245 = 73171) (by norm_num)
theorem B586853 : Blo 259821 586853 := bbase (se 4 (by rfl) ⟨55017, by rfl⟩ : syracuseStep 586853 = 110035) (by norm_num)
theorem B881765 : Blo 259821 881765 := bbase (se 4 (by rfl) ⟨82665, by rfl⟩ : syracuseStep 881765 = 165331) (by norm_num)
theorem B390269 : Blo 259821 390269 := bbase (se 3 (by rfl) ⟨73175, by rfl⟩ : syracuseStep 390269 = 146351) (by norm_num)
theorem B390293 : Blo 259821 390293 := bbase (se 6 (by rfl) ⟨9147, by rfl⟩ : syracuseStep 390293 = 18295) (by norm_num)
theorem B390317 : Blo 259821 390317 := bbase (se 3 (by rfl) ⟨73184, by rfl⟩ : syracuseStep 390317 = 146369) (by norm_num)
theorem B586925 : Blo 259821 586925 := bbase (se 3 (by rfl) ⟨110048, by rfl⟩ : syracuseStep 586925 = 220097) (by norm_num)
theorem B390341 : Blo 259821 390341 := bbase (se 4 (by rfl) ⟨36594, by rfl⟩ : syracuseStep 390341 = 73189) (by norm_num)
theorem B390365 : Blo 259821 390365 := bbase (se 3 (by rfl) ⟨73193, by rfl⟩ : syracuseStep 390365 = 146387) (by norm_num)
theorem B390389 : Blo 259821 390389 := bbase (se 5 (by rfl) ⟨18299, by rfl⟩ : syracuseStep 390389 = 36599) (by norm_num)
theorem B586997 : Blo 259821 586997 := bbase (se 5 (by rfl) ⟨27515, by rfl⟩ : syracuseStep 586997 = 55031) (by norm_num)
theorem B390413 : Blo 259821 390413 := bbase (se 3 (by rfl) ⟨73202, by rfl⟩ : syracuseStep 390413 = 146405) (by norm_num)
theorem B390437 : Blo 259821 390437 := bbase (se 4 (by rfl) ⟨36603, by rfl⟩ : syracuseStep 390437 = 73207) (by norm_num)
theorem B390461 : Blo 259821 390461 := bbase (se 3 (by rfl) ⟨73211, by rfl⟩ : syracuseStep 390461 = 146423) (by norm_num)
theorem B587069 : Blo 259821 587069 := bbase (se 3 (by rfl) ⟨110075, by rfl⟩ : syracuseStep 587069 = 220151) (by norm_num)
theorem B390485 : Blo 259821 390485 := bbase (se 13 (by rfl) ⟨71, by rfl⟩ : syracuseStep 390485 = 143) (by norm_num)
theorem B390509 : Blo 259821 390509 := bbase (se 3 (by rfl) ⟨73220, by rfl⟩ : syracuseStep 390509 = 146441) (by norm_num)
theorem B390533 : Blo 259821 390533 := bbase (se 4 (by rfl) ⟨36612, by rfl⟩ : syracuseStep 390533 = 73225) (by norm_num)
theorem B587141 : Blo 259821 587141 := bbase (se 4 (by rfl) ⟨55044, by rfl⟩ : syracuseStep 587141 = 110089) (by norm_num)
theorem B390557 : Blo 259821 390557 := bbase (se 3 (by rfl) ⟨73229, by rfl⟩ : syracuseStep 390557 = 146459) (by norm_num)
theorem B390581 : Blo 259821 390581 := bbase (se 5 (by rfl) ⟨18308, by rfl⟩ : syracuseStep 390581 = 36617) (by norm_num)
theorem B390605 : Blo 259821 390605 := bbase (se 3 (by rfl) ⟨73238, by rfl⟩ : syracuseStep 390605 = 146477) (by norm_num)
theorem B587213 : Blo 259821 587213 := bbase (se 3 (by rfl) ⟨110102, by rfl⟩ : syracuseStep 587213 = 220205) (by norm_num)
theorem B390629 : Blo 259821 390629 := bbase (se 4 (by rfl) ⟨36621, by rfl⟩ : syracuseStep 390629 = 73243) (by norm_num)
theorem B292333 : Blo 259821 292333 := bbase (se 3 (by rfl) ⟨54812, by rfl⟩ : syracuseStep 292333 = 109625) (by norm_num)
theorem B390653 : Blo 259821 390653 := bbase (se 3 (by rfl) ⟨73247, by rfl⟩ : syracuseStep 390653 = 146495) (by norm_num)
theorem B292369 : Blo 259821 292369 := bbase (se 2 (by rfl) ⟨109638, by rfl⟩ : syracuseStep 292369 = 219277) (by norm_num)
theorem B390677 : Blo 259821 390677 := bbase (se 6 (by rfl) ⟨9156, by rfl⟩ : syracuseStep 390677 = 18313) (by norm_num)
theorem B587285 : Blo 259821 587285 := bbase (se 6 (by rfl) ⟨13764, by rfl⟩ : syracuseStep 587285 = 27529) (by norm_num)
theorem B882197 : Blo 259821 882197 := bbase (se 6 (by rfl) ⟨20676, by rfl⟩ : syracuseStep 882197 = 41353) (by norm_num)
theorem B751141 : Blo 259821 751141 := bbase (se 4 (by rfl) ⟨70419, by rfl⟩ : syracuseStep 751141 = 140839) (by norm_num)
theorem B390701 : Blo 259821 390701 := bbase (se 3 (by rfl) ⟨73256, by rfl⟩ : syracuseStep 390701 = 146513) (by norm_num)
theorem B292405 : Blo 259821 292405 := bbase (se 5 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 292405 = 27413) (by norm_num)
theorem B390725 : Blo 259821 390725 := bbase (se 4 (by rfl) ⟨36630, by rfl⟩ : syracuseStep 390725 = 73261) (by norm_num)
theorem B751189 : Blo 259821 751189 := bbase (se 8 (by rfl) ⟨4401, by rfl⟩ : syracuseStep 751189 = 8803) (by norm_num)
theorem B292441 : Blo 259821 292441 := bbase (se 2 (by rfl) ⟨109665, by rfl⟩ : syracuseStep 292441 = 219331) (by norm_num)
theorem B390749 : Blo 259821 390749 := bbase (se 3 (by rfl) ⟨73265, by rfl⟩ : syracuseStep 390749 = 146531) (by norm_num)
theorem B423517 : Blo 259821 423517 := bbase (se 3 (by rfl) ⟨79409, by rfl⟩ : syracuseStep 423517 = 158819) (by norm_num)
theorem B587357 : Blo 259821 587357 := bbase (se 3 (by rfl) ⟨110129, by rfl⟩ : syracuseStep 587357 = 220259) (by norm_num)
theorem B390773 : Blo 259821 390773 := bbase (se 5 (by rfl) ⟨18317, by rfl⟩ : syracuseStep 390773 = 36635) (by norm_num)
theorem B292477 : Blo 259821 292477 := bbase (se 3 (by rfl) ⟨54839, by rfl⟩ : syracuseStep 292477 = 109679) (by norm_num)
theorem B423557 : Blo 259821 423557 := bbase (se 4 (by rfl) ⟨39708, by rfl⟩ : syracuseStep 423557 = 79417) (by norm_num)
theorem B390797 : Blo 259821 390797 := bbase (se 3 (by rfl) ⟨73274, by rfl⟩ : syracuseStep 390797 = 146549) (by norm_num)
theorem B292513 : Blo 259821 292513 := bbase (se 2 (by rfl) ⟨109692, by rfl⟩ : syracuseStep 292513 = 219385) (by norm_num)
theorem B390821 : Blo 259821 390821 := bbase (se 4 (by rfl) ⟨36639, by rfl⟩ : syracuseStep 390821 = 73279) (by norm_num)
theorem B587429 : Blo 259821 587429 := bbase (se 4 (by rfl) ⟨55071, by rfl⟩ : syracuseStep 587429 = 110143) (by norm_num)
theorem B390845 : Blo 259821 390845 := bbase (se 3 (by rfl) ⟨73283, by rfl⟩ : syracuseStep 390845 = 146567) (by norm_num)
theorem B292549 : Blo 259821 292549 := bbase (se 4 (by rfl) ⟨27426, by rfl⟩ : syracuseStep 292549 = 54853) (by norm_num)
theorem B390869 : Blo 259821 390869 := bbase (se 7 (by rfl) ⟨4580, by rfl⟩ : syracuseStep 390869 = 9161) (by norm_num)
theorem B292585 : Blo 259821 292585 := bbase (se 2 (by rfl) ⟨109719, by rfl⟩ : syracuseStep 292585 = 219439) (by norm_num)
theorem B390893 : Blo 259821 390893 := bbase (se 3 (by rfl) ⟨73292, by rfl⟩ : syracuseStep 390893 = 146585) (by norm_num)
theorem B587501 : Blo 259821 587501 := bbase (se 3 (by rfl) ⟨110156, by rfl⟩ : syracuseStep 587501 = 220313) (by norm_num)
theorem B390917 : Blo 259821 390917 := bbase (se 4 (by rfl) ⟨36648, by rfl⟩ : syracuseStep 390917 = 73297) (by norm_num)
theorem B292621 : Blo 259821 292621 := bbase (se 3 (by rfl) ⟨54866, by rfl⟩ : syracuseStep 292621 = 109733) (by norm_num)
theorem B390941 : Blo 259821 390941 := bbase (se 3 (by rfl) ⟨73301, by rfl⟩ : syracuseStep 390941 = 146603) (by norm_num)
theorem B292657 : Blo 259821 292657 := bbase (se 2 (by rfl) ⟨109746, by rfl⟩ : syracuseStep 292657 = 219493) (by norm_num)
theorem B390965 : Blo 259821 390965 := bbase (se 5 (by rfl) ⟨18326, by rfl⟩ : syracuseStep 390965 = 36653) (by norm_num)
theorem B587573 : Blo 259821 587573 := bbase (se 5 (by rfl) ⟨27542, by rfl⟩ : syracuseStep 587573 = 55085) (by norm_num)
theorem B390989 : Blo 259821 390989 := bbase (se 3 (by rfl) ⟨73310, by rfl⟩ : syracuseStep 390989 = 146621) (by norm_num)
theorem B292693 : Blo 259821 292693 := bbase (se 9 (by rfl) ⟨857, by rfl⟩ : syracuseStep 292693 = 1715) (by norm_num)
theorem B391013 : Blo 259821 391013 := bbase (se 4 (by rfl) ⟨36657, by rfl⟩ : syracuseStep 391013 = 73315) (by norm_num)
theorem B292729 : Blo 259821 292729 := bbase (se 2 (by rfl) ⟨109773, by rfl⟩ : syracuseStep 292729 = 219547) (by norm_num)
theorem B391037 : Blo 259821 391037 := bbase (se 3 (by rfl) ⟨73319, by rfl⟩ : syracuseStep 391037 = 146639) (by norm_num)
theorem B587645 : Blo 259821 587645 := bbase (se 3 (by rfl) ⟨110183, by rfl⟩ : syracuseStep 587645 = 220367) (by norm_num)
theorem B391061 : Blo 259821 391061 := bbase (se 6 (by rfl) ⟨9165, by rfl⟩ : syracuseStep 391061 = 18331) (by norm_num)
theorem B292765 : Blo 259821 292765 := bbase (se 3 (by rfl) ⟨54893, by rfl⟩ : syracuseStep 292765 = 109787) (by norm_num)
theorem B391085 : Blo 259821 391085 := bbase (se 3 (by rfl) ⟨73328, by rfl⟩ : syracuseStep 391085 = 146657) (by norm_num)
theorem B292801 : Blo 259821 292801 := bbase (se 2 (by rfl) ⟨109800, by rfl⟩ : syracuseStep 292801 = 219601) (by norm_num)
theorem B391109 : Blo 259821 391109 := bbase (se 4 (by rfl) ⟨36666, by rfl⟩ : syracuseStep 391109 = 73333) (by norm_num)
theorem B587717 : Blo 259821 587717 := bbase (se 4 (by rfl) ⟨55098, by rfl⟩ : syracuseStep 587717 = 110197) (by norm_num)
theorem B882629 : Blo 259821 882629 := bbase (se 4 (by rfl) ⟨82746, by rfl⟩ : syracuseStep 882629 = 165493) (by norm_num)
theorem B391133 : Blo 259821 391133 := bbase (se 3 (by rfl) ⟨73337, by rfl⟩ : syracuseStep 391133 = 146675) (by norm_num)
theorem B292837 : Blo 259821 292837 := bbase (se 4 (by rfl) ⟨27453, by rfl⟩ : syracuseStep 292837 = 54907) (by norm_num)
theorem B391157 : Blo 259821 391157 := bbase (se 5 (by rfl) ⟨18335, by rfl⟩ : syracuseStep 391157 = 36671) (by norm_num)
theorem B292873 : Blo 259821 292873 := bbase (se 2 (by rfl) ⟨109827, by rfl⟩ : syracuseStep 292873 = 219655) (by norm_num)
theorem B391181 : Blo 259821 391181 := bbase (se 3 (by rfl) ⟨73346, by rfl⟩ : syracuseStep 391181 = 146693) (by norm_num)
theorem B587789 : Blo 259821 587789 := bbase (se 3 (by rfl) ⟨110210, by rfl⟩ : syracuseStep 587789 = 220421) (by norm_num)
theorem B391205 : Blo 259821 391205 := bbase (se 4 (by rfl) ⟨36675, by rfl⟩ : syracuseStep 391205 = 73351) (by norm_num)
theorem B292909 : Blo 259821 292909 := bbase (se 3 (by rfl) ⟨54920, by rfl⟩ : syracuseStep 292909 = 109841) (by norm_num)
theorem B391229 : Blo 259821 391229 := bbase (se 3 (by rfl) ⟨73355, by rfl⟩ : syracuseStep 391229 = 146711) (by norm_num)
theorem B292945 : Blo 259821 292945 := bbase (se 2 (by rfl) ⟨109854, by rfl⟩ : syracuseStep 292945 = 219709) (by norm_num)
theorem B391253 : Blo 259821 391253 := bbase (se 8 (by rfl) ⟨2292, by rfl⟩ : syracuseStep 391253 = 4585) (by norm_num)
theorem B587861 : Blo 259821 587861 := bbase (se 8 (by rfl) ⟨3444, by rfl⟩ : syracuseStep 587861 = 6889) (by norm_num)
theorem B391277 : Blo 259821 391277 := bbase (se 3 (by rfl) ⟨73364, by rfl⟩ : syracuseStep 391277 = 146729) (by norm_num)
theorem B292981 : Blo 259821 292981 := bbase (se 5 (by rfl) ⟨13733, by rfl⟩ : syracuseStep 292981 = 27467) (by norm_num)
theorem B391301 : Blo 259821 391301 := bbase (se 4 (by rfl) ⟨36684, by rfl⟩ : syracuseStep 391301 = 73369) (by norm_num)
theorem B555149 : Blo 259821 555149 := bbase (se 3 (by rfl) ⟨104090, by rfl⟩ : syracuseStep 555149 = 208181) (by norm_num)
theorem B293017 : Blo 259821 293017 := bbase (se 2 (by rfl) ⟨109881, by rfl⟩ : syracuseStep 293017 = 219763) (by norm_num)
theorem B391325 : Blo 259821 391325 := bbase (se 3 (by rfl) ⟨73373, by rfl⟩ : syracuseStep 391325 = 146747) (by norm_num)
theorem B587933 : Blo 259821 587933 := bbase (se 3 (by rfl) ⟨110237, by rfl⟩ : syracuseStep 587933 = 220475) (by norm_num)
theorem B391349 : Blo 259821 391349 := bbase (se 5 (by rfl) ⟨18344, by rfl⟩ : syracuseStep 391349 = 36689) (by norm_num)
theorem B293053 : Blo 259821 293053 := bbase (se 3 (by rfl) ⟨54947, by rfl⟩ : syracuseStep 293053 = 109895) (by norm_num)
theorem B391373 : Blo 259821 391373 := bbase (se 3 (by rfl) ⟨73382, by rfl⟩ : syracuseStep 391373 = 146765) (by norm_num)
theorem B293089 : Blo 259821 293089 := bbase (se 2 (by rfl) ⟨109908, by rfl⟩ : syracuseStep 293089 = 219817) (by norm_num)
theorem B391397 : Blo 259821 391397 := bbase (se 4 (by rfl) ⟨36693, by rfl⟩ : syracuseStep 391397 = 73387) (by norm_num)
theorem B588005 : Blo 259821 588005 := bbase (se 4 (by rfl) ⟨55125, by rfl⟩ : syracuseStep 588005 = 110251) (by norm_num)
theorem B391421 : Blo 259821 391421 := bbase (se 3 (by rfl) ⟨73391, by rfl⟩ : syracuseStep 391421 = 146783) (by norm_num)
theorem B293125 : Blo 259821 293125 := bbase (se 4 (by rfl) ⟨27480, by rfl⟩ : syracuseStep 293125 = 54961) (by norm_num)
theorem B391445 : Blo 259821 391445 := bbase (se 6 (by rfl) ⟨9174, by rfl⟩ : syracuseStep 391445 = 18349) (by norm_num)
theorem B555293 : Blo 259821 555293 := bbase (se 3 (by rfl) ⟨104117, by rfl⟩ : syracuseStep 555293 = 208235) (by norm_num)
theorem B293161 : Blo 259821 293161 := bbase (se 2 (by rfl) ⟨109935, by rfl⟩ : syracuseStep 293161 = 219871) (by norm_num)
theorem B391469 : Blo 259821 391469 := bbase (se 3 (by rfl) ⟨73400, by rfl⟩ : syracuseStep 391469 = 146801) (by norm_num)
theorem B588077 : Blo 259821 588077 := bbase (se 3 (by rfl) ⟨110264, by rfl⟩ : syracuseStep 588077 = 220529) (by norm_num)
theorem B391493 : Blo 259821 391493 := bbase (se 4 (by rfl) ⟨36702, by rfl⟩ : syracuseStep 391493 = 73405) (by norm_num)
theorem B293197 : Blo 259821 293197 := bbase (se 3 (by rfl) ⟨54974, by rfl⟩ : syracuseStep 293197 = 109949) (by norm_num)
theorem B391517 : Blo 259821 391517 := bbase (se 3 (by rfl) ⟨73409, by rfl⟩ : syracuseStep 391517 = 146819) (by norm_num)
theorem B293233 : Blo 259821 293233 := bbase (se 2 (by rfl) ⟨109962, by rfl⟩ : syracuseStep 293233 = 219925) (by norm_num)
theorem B391541 : Blo 259821 391541 := bbase (se 5 (by rfl) ⟨18353, by rfl⟩ : syracuseStep 391541 = 36707) (by norm_num)
theorem B588149 : Blo 259821 588149 := bbase (se 5 (by rfl) ⟨27569, by rfl⟩ : syracuseStep 588149 = 55139) (by norm_num)
theorem B883061 : Blo 259821 883061 := bbase (se 5 (by rfl) ⟨41393, by rfl⟩ : syracuseStep 883061 = 82787) (by norm_num)
theorem B391565 : Blo 259821 391565 := bbase (se 3 (by rfl) ⟨73418, by rfl⟩ : syracuseStep 391565 = 146837) (by norm_num)
theorem B293269 : Blo 259821 293269 := bbase (se 6 (by rfl) ⟨6873, by rfl⟩ : syracuseStep 293269 = 13747) (by norm_num)
theorem B391589 : Blo 259821 391589 := bbase (se 4 (by rfl) ⟨36711, by rfl⟩ : syracuseStep 391589 = 73423) (by norm_num)
theorem B293305 : Blo 259821 293305 := bbase (se 2 (by rfl) ⟨109989, by rfl⟩ : syracuseStep 293305 = 219979) (by norm_num)
theorem B391613 : Blo 259821 391613 := bbase (se 3 (by rfl) ⟨73427, by rfl⟩ : syracuseStep 391613 = 146855) (by norm_num)
theorem B588221 : Blo 259821 588221 := bbase (se 3 (by rfl) ⟨110291, by rfl⟩ : syracuseStep 588221 = 220583) (by norm_num)
theorem B391637 : Blo 259821 391637 := bbase (se 7 (by rfl) ⟨4589, by rfl⟩ : syracuseStep 391637 = 9179) (by norm_num)
theorem B293341 : Blo 259821 293341 := bbase (se 3 (by rfl) ⟨55001, by rfl⟩ : syracuseStep 293341 = 110003) (by norm_num)
theorem B391661 : Blo 259821 391661 := bbase (se 3 (by rfl) ⟨73436, by rfl⟩ : syracuseStep 391661 = 146873) (by norm_num)
theorem B293377 : Blo 259821 293377 := bbase (se 2 (by rfl) ⟨110016, by rfl⟩ : syracuseStep 293377 = 220033) (by norm_num)
theorem B391685 : Blo 259821 391685 := bbase (se 4 (by rfl) ⟨36720, by rfl⟩ : syracuseStep 391685 = 73441) (by norm_num)
theorem B588293 : Blo 259821 588293 := bbase (se 4 (by rfl) ⟨55152, by rfl⟩ : syracuseStep 588293 = 110305) (by norm_num)
theorem B3176981 : Blo 259821 3176981 := bbase (se 6 (by rfl) ⟨74460, by rfl⟩ : syracuseStep 3176981 = 148921) (by norm_num)
theorem B391709 : Blo 259821 391709 := bbase (se 3 (by rfl) ⟨73445, by rfl⟩ : syracuseStep 391709 = 146891) (by norm_num)
theorem B293413 : Blo 259821 293413 := bbase (se 4 (by rfl) ⟨27507, by rfl⟩ : syracuseStep 293413 = 55015) (by norm_num)
theorem B391733 : Blo 259821 391733 := bbase (se 5 (by rfl) ⟨18362, by rfl⟩ : syracuseStep 391733 = 36725) (by norm_num)
theorem B293449 : Blo 259821 293449 := bbase (se 2 (by rfl) ⟨110043, by rfl⟩ : syracuseStep 293449 = 220087) (by norm_num)
theorem B391757 : Blo 259821 391757 := bbase (se 3 (by rfl) ⟨73454, by rfl⟩ : syracuseStep 391757 = 146909) (by norm_num)
theorem B588365 : Blo 259821 588365 := bbase (se 3 (by rfl) ⟨110318, by rfl⟩ : syracuseStep 588365 = 220637) (by norm_num)
theorem B391781 : Blo 259821 391781 := bbase (se 4 (by rfl) ⟨36729, by rfl⟩ : syracuseStep 391781 = 73459) (by norm_num)
theorem B293485 : Blo 259821 293485 := bbase (se 3 (by rfl) ⟨55028, by rfl⟩ : syracuseStep 293485 = 110057) (by norm_num)
theorem B391805 : Blo 259821 391805 := bbase (se 3 (by rfl) ⟨73463, by rfl⟩ : syracuseStep 391805 = 146927) (by norm_num)
theorem B555653 : Blo 259821 555653 := bbase (se 4 (by rfl) ⟨52092, by rfl⟩ : syracuseStep 555653 = 104185) (by norm_num)
theorem B293521 : Blo 259821 293521 := bbase (se 2 (by rfl) ⟨110070, by rfl⟩ : syracuseStep 293521 = 220141) (by norm_num)
theorem B391829 : Blo 259821 391829 := bbase (se 6 (by rfl) ⟨9183, by rfl⟩ : syracuseStep 391829 = 18367) (by norm_num)
theorem B588437 : Blo 259821 588437 := bbase (se 6 (by rfl) ⟨13791, by rfl⟩ : syracuseStep 588437 = 27583) (by norm_num)
theorem B391853 : Blo 259821 391853 := bbase (se 3 (by rfl) ⟨73472, by rfl⟩ : syracuseStep 391853 = 146945) (by norm_num)
theorem B293557 : Blo 259821 293557 := bbase (se 5 (by rfl) ⟨13760, by rfl⟩ : syracuseStep 293557 = 27521) (by norm_num)
theorem B1112773 : Blo 259821 1112773 := bbase (se 4 (by rfl) ⟨104322, by rfl⟩ : syracuseStep 1112773 = 208645) (by norm_num)
theorem B391877 : Blo 259821 391877 := bbase (se 4 (by rfl) ⟨36738, by rfl⟩ : syracuseStep 391877 = 73477) (by norm_num)
theorem B293593 : Blo 259821 293593 := bbase (se 2 (by rfl) ⟨110097, by rfl⟩ : syracuseStep 293593 = 220195) (by norm_num)
theorem B391901 : Blo 259821 391901 := bbase (se 3 (by rfl) ⟨73481, by rfl⟩ : syracuseStep 391901 = 146963) (by norm_num)
theorem B588509 : Blo 259821 588509 := bbase (se 3 (by rfl) ⟨110345, by rfl⟩ : syracuseStep 588509 = 220691) (by norm_num)
theorem B391925 : Blo 259821 391925 := bbase (se 5 (by rfl) ⟨18371, by rfl⟩ : syracuseStep 391925 = 36743) (by norm_num)
theorem B293629 : Blo 259821 293629 := bbase (se 3 (by rfl) ⟨55055, by rfl⟩ : syracuseStep 293629 = 110111) (by norm_num)
theorem B391949 : Blo 259821 391949 := bbase (se 3 (by rfl) ⟨73490, by rfl⟩ : syracuseStep 391949 = 146981) (by norm_num)
theorem B293665 : Blo 259821 293665 := bbase (se 2 (by rfl) ⟨110124, by rfl⟩ : syracuseStep 293665 = 220249) (by norm_num)
theorem B391973 : Blo 259821 391973 := bbase (se 4 (by rfl) ⟨36747, by rfl⟩ : syracuseStep 391973 = 73495) (by norm_num)
theorem B588581 : Blo 259821 588581 := bbase (se 4 (by rfl) ⟨55179, by rfl⟩ : syracuseStep 588581 = 110359) (by norm_num)
theorem B883493 : Blo 259821 883493 := bbase (se 4 (by rfl) ⟨82827, by rfl⟩ : syracuseStep 883493 = 165655) (by norm_num)
theorem B391997 : Blo 259821 391997 := bbase (se 3 (by rfl) ⟨73499, by rfl⟩ : syracuseStep 391997 = 146999) (by norm_num)
theorem B293701 : Blo 259821 293701 := bbase (se 4 (by rfl) ⟨27534, by rfl⟩ : syracuseStep 293701 = 55069) (by norm_num)
theorem B1604437 : Blo 259821 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B392021 : Blo 259821 392021 := bbase (se 9 (by rfl) ⟨1148, by rfl⟩ : syracuseStep 392021 = 2297) (by norm_num)
theorem B293737 : Blo 259821 293737 := bbase (se 2 (by rfl) ⟨110151, by rfl⟩ : syracuseStep 293737 = 220303) (by norm_num)
theorem B392045 : Blo 259821 392045 := bbase (se 3 (by rfl) ⟨73508, by rfl⟩ : syracuseStep 392045 = 147017) (by norm_num)
theorem B588653 : Blo 259821 588653 := bbase (se 3 (by rfl) ⟨110372, by rfl⟩ : syracuseStep 588653 = 220745) (by norm_num)
theorem B392069 : Blo 259821 392069 := bbase (se 4 (by rfl) ⟨36756, by rfl⟩ : syracuseStep 392069 = 73513) (by norm_num)
theorem B293773 : Blo 259821 293773 := bbase (se 3 (by rfl) ⟨55082, by rfl⟩ : syracuseStep 293773 = 110165) (by norm_num)
theorem B392093 : Blo 259821 392093 := bbase (se 3 (by rfl) ⟨73517, by rfl⟩ : syracuseStep 392093 = 147035) (by norm_num)
theorem B293809 : Blo 259821 293809 := bbase (se 2 (by rfl) ⟨110178, by rfl⟩ : syracuseStep 293809 = 220357) (by norm_num)
theorem B392117 : Blo 259821 392117 := bbase (se 5 (by rfl) ⟨18380, by rfl⟩ : syracuseStep 392117 = 36761) (by norm_num)
theorem B588725 : Blo 259821 588725 := bbase (se 5 (by rfl) ⟨27596, by rfl⟩ : syracuseStep 588725 = 55193) (by norm_num)
theorem B392141 : Blo 259821 392141 := bbase (se 3 (by rfl) ⟨73526, by rfl⟩ : syracuseStep 392141 = 147053) (by norm_num)
theorem B293845 : Blo 259821 293845 := bbase (se 7 (by rfl) ⟨3443, by rfl⟩ : syracuseStep 293845 = 6887) (by norm_num)
theorem B392165 : Blo 259821 392165 := bbase (se 4 (by rfl) ⟨36765, by rfl⟩ : syracuseStep 392165 = 73531) (by norm_num)
theorem B293881 : Blo 259821 293881 := bbase (se 2 (by rfl) ⟨110205, by rfl⟩ : syracuseStep 293881 = 220411) (by norm_num)
theorem B392189 : Blo 259821 392189 := bbase (se 3 (by rfl) ⟨73535, by rfl⟩ : syracuseStep 392189 = 147071) (by norm_num)
theorem B588797 : Blo 259821 588797 := bbase (se 3 (by rfl) ⟨110399, by rfl⟩ : syracuseStep 588797 = 220799) (by norm_num)
theorem B392213 : Blo 259821 392213 := bbase (se 6 (by rfl) ⟨9192, by rfl⟩ : syracuseStep 392213 = 18385) (by norm_num)
theorem B293917 : Blo 259821 293917 := bbase (se 3 (by rfl) ⟨55109, by rfl⟩ : syracuseStep 293917 = 110219) (by norm_num)
theorem B392237 : Blo 259821 392237 := bbase (se 3 (by rfl) ⟨73544, by rfl⟩ : syracuseStep 392237 = 147089) (by norm_num)
theorem B293953 : Blo 259821 293953 := bbase (se 2 (by rfl) ⟨110232, by rfl⟩ : syracuseStep 293953 = 220465) (by norm_num)
theorem B392261 : Blo 259821 392261 := bbase (se 4 (by rfl) ⟨36774, by rfl⟩ : syracuseStep 392261 = 73549) (by norm_num)
theorem B588869 : Blo 259821 588869 := bbase (se 4 (by rfl) ⟨55206, by rfl⟩ : syracuseStep 588869 = 110413) (by norm_num)
theorem B392285 : Blo 259821 392285 := bbase (se 3 (by rfl) ⟨73553, by rfl⟩ : syracuseStep 392285 = 147107) (by norm_num)
theorem B293989 : Blo 259821 293989 := bbase (se 4 (by rfl) ⟨27561, by rfl⟩ : syracuseStep 293989 = 55123) (by norm_num)
theorem B392309 : Blo 259821 392309 := bbase (se 5 (by rfl) ⟨18389, by rfl⟩ : syracuseStep 392309 = 36779) (by norm_num)
theorem B294025 : Blo 259821 294025 := bbase (se 2 (by rfl) ⟨110259, by rfl⟩ : syracuseStep 294025 = 220519) (by norm_num)
theorem B392333 : Blo 259821 392333 := bbase (se 3 (by rfl) ⟨73562, by rfl⟩ : syracuseStep 392333 = 147125) (by norm_num)
theorem B588941 : Blo 259821 588941 := bbase (se 3 (by rfl) ⟨110426, by rfl⟩ : syracuseStep 588941 = 220853) (by norm_num)
theorem B392357 : Blo 259821 392357 := bbase (se 4 (by rfl) ⟨36783, by rfl⟩ : syracuseStep 392357 = 73567) (by norm_num)
theorem B294061 : Blo 259821 294061 := bbase (se 3 (by rfl) ⟨55136, by rfl⟩ : syracuseStep 294061 = 110273) (by norm_num)
theorem B392381 : Blo 259821 392381 := bbase (se 3 (by rfl) ⟨73571, by rfl⟩ : syracuseStep 392381 = 147143) (by norm_num)
theorem B294097 : Blo 259821 294097 := bbase (se 2 (by rfl) ⟨110286, by rfl⟩ : syracuseStep 294097 = 220573) (by norm_num)
theorem B392405 : Blo 259821 392405 := bbase (se 7 (by rfl) ⟨4598, by rfl⟩ : syracuseStep 392405 = 9197) (by norm_num)
theorem B589013 : Blo 259821 589013 := bbase (se 7 (by rfl) ⟨6902, by rfl⟩ : syracuseStep 589013 = 13805) (by norm_num)
theorem B883925 : Blo 259821 883925 := bbase (se 7 (by rfl) ⟨10358, by rfl⟩ : syracuseStep 883925 = 20717) (by norm_num)
theorem B392429 : Blo 259821 392429 := bbase (se 3 (by rfl) ⟨73580, by rfl⟩ : syracuseStep 392429 = 147161) (by norm_num)
theorem B294133 : Blo 259821 294133 := bbase (se 5 (by rfl) ⟨13787, by rfl⟩ : syracuseStep 294133 = 27575) (by norm_num)
theorem B392453 : Blo 259821 392453 := bbase (se 4 (by rfl) ⟨36792, by rfl⟩ : syracuseStep 392453 = 73585) (by norm_num)
theorem B294169 : Blo 259821 294169 := bbase (se 2 (by rfl) ⟨110313, by rfl⟩ : syracuseStep 294169 = 220627) (by norm_num)
theorem B392477 : Blo 259821 392477 := bbase (se 3 (by rfl) ⟨73589, by rfl⟩ : syracuseStep 392477 = 147179) (by norm_num)
theorem B589085 : Blo 259821 589085 := bbase (se 3 (by rfl) ⟨110453, by rfl⟩ : syracuseStep 589085 = 220907) (by norm_num)
theorem B392501 : Blo 259821 392501 := bbase (se 5 (by rfl) ⟨18398, by rfl⟩ : syracuseStep 392501 = 36797) (by norm_num)
theorem B294205 : Blo 259821 294205 := bbase (se 3 (by rfl) ⟨55163, by rfl⟩ : syracuseStep 294205 = 110327) (by norm_num)
theorem B392525 : Blo 259821 392525 := bbase (se 3 (by rfl) ⟨73598, by rfl⟩ : syracuseStep 392525 = 147197) (by norm_num)
theorem B294241 : Blo 259821 294241 := bbase (se 2 (by rfl) ⟨110340, by rfl⟩ : syracuseStep 294241 = 220681) (by norm_num)
theorem B392549 : Blo 259821 392549 := bbase (se 4 (by rfl) ⟨36801, by rfl⟩ : syracuseStep 392549 = 73603) (by norm_num)
theorem B589157 : Blo 259821 589157 := bbase (se 4 (by rfl) ⟨55233, by rfl⟩ : syracuseStep 589157 = 110467) (by norm_num)
theorem B392573 : Blo 259821 392573 := bbase (se 3 (by rfl) ⟨73607, by rfl⟩ : syracuseStep 392573 = 147215) (by norm_num)
theorem B294277 : Blo 259821 294277 := bbase (se 4 (by rfl) ⟨27588, by rfl⟩ : syracuseStep 294277 = 55177) (by norm_num)
theorem B392597 : Blo 259821 392597 := bbase (se 6 (by rfl) ⟨9201, by rfl⟩ : syracuseStep 392597 = 18403) (by norm_num)
theorem B294313 : Blo 259821 294313 := bbase (se 2 (by rfl) ⟨110367, by rfl⟩ : syracuseStep 294313 = 220735) (by norm_num)
theorem B392621 : Blo 259821 392621 := bbase (se 3 (by rfl) ⟨73616, by rfl⟩ : syracuseStep 392621 = 147233) (by norm_num)
theorem B589229 : Blo 259821 589229 := bbase (se 3 (by rfl) ⟨110480, by rfl⟩ : syracuseStep 589229 = 220961) (by norm_num)
theorem B392645 : Blo 259821 392645 := bbase (se 4 (by rfl) ⟨36810, by rfl⟩ : syracuseStep 392645 = 73621) (by norm_num)
theorem B294349 : Blo 259821 294349 := bbase (se 3 (by rfl) ⟨55190, by rfl⟩ : syracuseStep 294349 = 110381) (by norm_num)
theorem B392669 : Blo 259821 392669 := bbase (se 3 (by rfl) ⟨73625, by rfl⟩ : syracuseStep 392669 = 147251) (by norm_num)
theorem B294385 : Blo 259821 294385 := bbase (se 2 (by rfl) ⟨110394, by rfl⟩ : syracuseStep 294385 = 220789) (by norm_num)
theorem B392693 : Blo 259821 392693 := bbase (se 5 (by rfl) ⟨18407, by rfl⟩ : syracuseStep 392693 = 36815) (by norm_num)
theorem B589301 : Blo 259821 589301 := bbase (se 5 (by rfl) ⟨27623, by rfl⟩ : syracuseStep 589301 = 55247) (by norm_num)
theorem B556541 : Blo 259821 556541 := bbase (se 3 (by rfl) ⟨104351, by rfl⟩ : syracuseStep 556541 = 208703) (by norm_num)
theorem B392717 : Blo 259821 392717 := bbase (se 3 (by rfl) ⟨73634, by rfl⟩ : syracuseStep 392717 = 147269) (by norm_num)
theorem B2227733 : Blo 259821 2227733 := bbase (se 6 (by rfl) ⟨52212, by rfl⟩ : syracuseStep 2227733 = 104425) (by norm_num)
theorem B294421 : Blo 259821 294421 := bbase (se 6 (by rfl) ⟨6900, by rfl⟩ : syracuseStep 294421 = 13801) (by norm_num)
theorem B392741 : Blo 259821 392741 := bbase (se 4 (by rfl) ⟨36819, by rfl⟩ : syracuseStep 392741 = 73639) (by norm_num)
theorem B294457 : Blo 259821 294457 := bbase (se 2 (by rfl) ⟨110421, by rfl⟩ : syracuseStep 294457 = 220843) (by norm_num)
theorem B392765 : Blo 259821 392765 := bbase (se 3 (by rfl) ⟨73643, by rfl⟩ : syracuseStep 392765 = 147287) (by norm_num)
theorem B589373 : Blo 259821 589373 := bbase (se 3 (by rfl) ⟨110507, by rfl⟩ : syracuseStep 589373 = 221015) (by norm_num)
theorem B392789 : Blo 259821 392789 := bbase (se 8 (by rfl) ⟨2301, by rfl⟩ : syracuseStep 392789 = 4603) (by norm_num)
theorem B294493 : Blo 259821 294493 := bbase (se 3 (by rfl) ⟨55217, by rfl⟩ : syracuseStep 294493 = 110435) (by norm_num)
theorem B392813 : Blo 259821 392813 := bbase (se 3 (by rfl) ⟨73652, by rfl⟩ : syracuseStep 392813 = 147305) (by norm_num)
theorem B294529 : Blo 259821 294529 := bbase (se 2 (by rfl) ⟨110448, by rfl⟩ : syracuseStep 294529 = 220897) (by norm_num)
theorem B392837 : Blo 259821 392837 := bbase (se 4 (by rfl) ⟨36828, by rfl⟩ : syracuseStep 392837 = 73657) (by norm_num)
theorem B589445 : Blo 259821 589445 := bbase (se 4 (by rfl) ⟨55260, by rfl⟩ : syracuseStep 589445 = 110521) (by norm_num)
theorem B884357 : Blo 259821 884357 := bbase (se 4 (by rfl) ⟨82908, by rfl⟩ : syracuseStep 884357 = 165817) (by norm_num)
theorem B392861 : Blo 259821 392861 := bbase (se 3 (by rfl) ⟨73661, by rfl⟩ : syracuseStep 392861 = 147323) (by norm_num)
theorem B294565 : Blo 259821 294565 := bbase (se 4 (by rfl) ⟨27615, by rfl⟩ : syracuseStep 294565 = 55231) (by norm_num)
theorem B392885 : Blo 259821 392885 := bbase (se 5 (by rfl) ⟨18416, by rfl⟩ : syracuseStep 392885 = 36833) (by norm_num)
theorem B294601 : Blo 259821 294601 := bbase (se 2 (by rfl) ⟨110475, by rfl⟩ : syracuseStep 294601 = 220951) (by norm_num)
theorem B392909 : Blo 259821 392909 := bbase (se 3 (by rfl) ⟨73670, by rfl⟩ : syracuseStep 392909 = 147341) (by norm_num)
theorem B589517 : Blo 259821 589517 := bbase (se 3 (by rfl) ⟨110534, by rfl⟩ : syracuseStep 589517 = 221069) (by norm_num)
theorem B392933 : Blo 259821 392933 := bbase (se 4 (by rfl) ⟨36837, by rfl⟩ : syracuseStep 392933 = 73675) (by norm_num)
theorem B294637 : Blo 259821 294637 := bbase (se 3 (by rfl) ⟨55244, by rfl⟩ : syracuseStep 294637 = 110489) (by norm_num)
theorem B556789 : Blo 259821 556789 := bbase (se 5 (by rfl) ⟨26099, by rfl⟩ : syracuseStep 556789 = 52199) (by norm_num)
theorem B392957 : Blo 259821 392957 := bbase (se 3 (by rfl) ⟨73679, by rfl⟩ : syracuseStep 392957 = 147359) (by norm_num)
theorem B294673 : Blo 259821 294673 := bbase (se 2 (by rfl) ⟨110502, by rfl⟩ : syracuseStep 294673 = 221005) (by norm_num)
theorem B392981 : Blo 259821 392981 := bbase (se 6 (by rfl) ⟨9210, by rfl⟩ : syracuseStep 392981 = 18421) (by norm_num)
theorem B589589 : Blo 259821 589589 := bbase (se 6 (by rfl) ⟨13818, by rfl⟩ : syracuseStep 589589 = 27637) (by norm_num)
theorem B393005 : Blo 259821 393005 := bbase (se 3 (by rfl) ⟨73688, by rfl⟩ : syracuseStep 393005 = 147377) (by norm_num)
theorem B294709 : Blo 259821 294709 := bbase (se 5 (by rfl) ⟨13814, by rfl⟩ : syracuseStep 294709 = 27629) (by norm_num)
theorem B393029 : Blo 259821 393029 := bbase (se 4 (by rfl) ⟨36846, by rfl⟩ : syracuseStep 393029 = 73693) (by norm_num)
theorem B294745 : Blo 259821 294745 := bbase (se 2 (by rfl) ⟨110529, by rfl⟩ : syracuseStep 294745 = 221059) (by norm_num)
theorem B393053 : Blo 259821 393053 := bbase (se 3 (by rfl) ⟨73697, by rfl⟩ : syracuseStep 393053 = 147395) (by norm_num)
theorem B589661 : Blo 259821 589661 := bbase (se 3 (by rfl) ⟨110561, by rfl⟩ : syracuseStep 589661 = 221123) (by norm_num)
theorem B393077 : Blo 259821 393077 := bbase (se 5 (by rfl) ⟨18425, by rfl⟩ : syracuseStep 393077 = 36851) (by norm_num)
theorem B294781 : Blo 259821 294781 := bbase (se 3 (by rfl) ⟨55271, by rfl⟩ : syracuseStep 294781 = 110543) (by norm_num)
theorem B393101 : Blo 259821 393101 := bbase (se 3 (by rfl) ⟨73706, by rfl⟩ : syracuseStep 393101 = 147413) (by norm_num)
theorem B294817 : Blo 259821 294817 := bbase (se 2 (by rfl) ⟨110556, by rfl⟩ : syracuseStep 294817 = 221113) (by norm_num)
theorem B393125 : Blo 259821 393125 := bbase (se 4 (by rfl) ⟨36855, by rfl⟩ : syracuseStep 393125 = 73711) (by norm_num)
theorem B589733 : Blo 259821 589733 := bbase (se 4 (by rfl) ⟨55287, by rfl⟩ : syracuseStep 589733 = 110575) (by norm_num)
theorem B393149 : Blo 259821 393149 := bbase (se 3 (by rfl) ⟨73715, by rfl⟩ : syracuseStep 393149 = 147431) (by norm_num)
theorem B294853 : Blo 259821 294853 := bbase (se 4 (by rfl) ⟨27642, by rfl⟩ : syracuseStep 294853 = 55285) (by norm_num)
theorem B393173 : Blo 259821 393173 := bbase (se 7 (by rfl) ⟨4607, by rfl⟩ : syracuseStep 393173 = 9215) (by norm_num)
theorem B294889 : Blo 259821 294889 := bbase (se 2 (by rfl) ⟨110583, by rfl⟩ : syracuseStep 294889 = 221167) (by norm_num)
theorem B393197 : Blo 259821 393197 := bbase (se 3 (by rfl) ⟨73724, by rfl⟩ : syracuseStep 393197 = 147449) (by norm_num)
theorem B589805 : Blo 259821 589805 := bbase (se 3 (by rfl) ⟨110588, by rfl⟩ : syracuseStep 589805 = 221177) (by norm_num)
theorem B262147 : Blo 259821 262147 := bstep (se 1 (by rfl) ⟨196610, by rfl⟩ : syracuseStep 262147 = 393221) B393221
theorem B589841 : Blo 259821 589841 := bstep (se 2 (by rfl) ⟨221190, by rfl⟩ : syracuseStep 589841 = 442381) B442381
theorem B393233 : Blo 259821 393233 := bstep (se 2 (by rfl) ⟨147462, by rfl⟩ : syracuseStep 393233 = 294925) B294925
theorem B262163 : Blo 259821 262163 := bstep (se 1 (by rfl) ⟨196622, by rfl⟩ : syracuseStep 262163 = 393245) B393245
theorem B589859 : Blo 259821 589859 := bstep (se 1 (by rfl) ⟨442394, by rfl⟩ : syracuseStep 589859 = 884789) B884789
theorem B393251 : Blo 259821 393251 := bstep (se 1 (by rfl) ⟨294938, by rfl⟩ : syracuseStep 393251 = 589877) B589877
theorem B262179 : Blo 259821 262179 := bstep (se 1 (by rfl) ⟨196634, by rfl⟩ : syracuseStep 262179 = 393269) B393269
theorem B262195 : Blo 259821 262195 := bstep (se 1 (by rfl) ⟨196646, by rfl⟩ : syracuseStep 262195 = 393293) B393293
theorem B393281 : Blo 259821 393281 := bstep (se 2 (by rfl) ⟨147480, by rfl⟩ : syracuseStep 393281 = 294961) B294961
theorem B294979 : Blo 259821 294979 := bstep (se 1 (by rfl) ⟨221234, by rfl⟩ : syracuseStep 294979 = 442469) B442469
theorem B262211 : Blo 259821 262211 := bstep (se 1 (by rfl) ⟨196658, by rfl⟩ : syracuseStep 262211 = 393317) B393317
theorem B1998917 : Blo 259821 1998917 := bstep (se 4 (by rfl) ⟨187398, by rfl⟩ : syracuseStep 1998917 = 374797) B374797
theorem B393299 : Blo 259821 393299 := bstep (se 1 (by rfl) ⟨294974, by rfl⟩ : syracuseStep 393299 = 589949) B589949
theorem B262227 : Blo 259821 262227 := bstep (se 1 (by rfl) ⟨196670, by rfl⟩ : syracuseStep 262227 = 393341) B393341
theorem B262243 : Blo 259821 262243 := bstep (se 1 (by rfl) ⟨196682, by rfl⟩ : syracuseStep 262243 = 393365) B393365
theorem B4915313 : Blo 259821 4915313 := bstep (se 2 (by rfl) ⟨1843242, by rfl⟩ : syracuseStep 4915313 = 3686485) B3686485
theorem B393329 : Blo 259821 393329 := bstep (se 2 (by rfl) ⟨147498, by rfl⟩ : syracuseStep 393329 = 294997) B294997
theorem B262259 : Blo 259821 262259 := bstep (se 1 (by rfl) ⟨196694, by rfl⟩ : syracuseStep 262259 = 393389) B393389
theorem B393347 : Blo 259821 393347 := bstep (se 1 (by rfl) ⟨295010, by rfl⟩ : syracuseStep 393347 = 590021) B590021
theorem B262275 : Blo 259821 262275 := bstep (se 1 (by rfl) ⟨196706, by rfl⟩ : syracuseStep 262275 = 393413) B393413
theorem B262291 : Blo 259821 262291 := bstep (se 1 (by rfl) ⟨196718, by rfl⟩ : syracuseStep 262291 = 393437) B393437
theorem B393377 : Blo 259821 393377 := bstep (se 2 (by rfl) ⟨147516, by rfl⟩ : syracuseStep 393377 = 295033) B295033
theorem B262307 : Blo 259821 262307 := bstep (se 1 (by rfl) ⟨196730, by rfl⟩ : syracuseStep 262307 = 393461) B393461
theorem B1441955 : Blo 259821 1441955 := bstep (se 1 (by rfl) ⟨1081466, by rfl⟩ : syracuseStep 1441955 = 2162933) B2162933
theorem B393395 : Blo 259821 393395 := bstep (se 1 (by rfl) ⟨295046, by rfl⟩ : syracuseStep 393395 = 590093) B590093
theorem B262323 : Blo 259821 262323 := bstep (se 1 (by rfl) ⟨196742, by rfl⟩ : syracuseStep 262323 = 393485) B393485
theorem B262339 : Blo 259821 262339 := bstep (se 1 (by rfl) ⟨196754, by rfl⟩ : syracuseStep 262339 = 393509) B393509
theorem B393425 : Blo 259821 393425 := bstep (se 2 (by rfl) ⟨147534, by rfl⟩ : syracuseStep 393425 = 295069) B295069
theorem B295123 : Blo 259821 295123 := bstep (se 1 (by rfl) ⟨221342, by rfl⟩ : syracuseStep 295123 = 442685) B442685
theorem B262355 : Blo 259821 262355 := bstep (se 1 (by rfl) ⟨196766, by rfl⟩ : syracuseStep 262355 = 393533) B393533
theorem B393443 : Blo 259821 393443 := bstep (se 1 (by rfl) ⟨295082, by rfl⟩ : syracuseStep 393443 = 590165) B590165
theorem B262371 : Blo 259821 262371 := bstep (se 1 (by rfl) ⟨196778, by rfl⟩ : syracuseStep 262371 = 393557) B393557
theorem B262387 : Blo 259821 262387 := bstep (se 1 (by rfl) ⟨196790, by rfl⟩ : syracuseStep 262387 = 393581) B393581
theorem B393473 : Blo 259821 393473 := bstep (se 2 (by rfl) ⟨147552, by rfl⟩ : syracuseStep 393473 = 295105) B295105
theorem B262403 : Blo 259821 262403 := bstep (se 1 (by rfl) ⟨196802, by rfl⟩ : syracuseStep 262403 = 393605) B393605
theorem B885005 : Blo 259821 885005 := bstep (se 3 (by rfl) ⟨165938, by rfl⟩ : syracuseStep 885005 = 331877) B331877
theorem B393491 : Blo 259821 393491 := bstep (se 1 (by rfl) ⟨295118, by rfl⟩ : syracuseStep 393491 = 590237) B590237
theorem B262419 : Blo 259821 262419 := bstep (se 1 (by rfl) ⟨196814, by rfl⟩ : syracuseStep 262419 = 393629) B393629
theorem B262435 : Blo 259821 262435 := bstep (se 1 (by rfl) ⟨196826, by rfl⟩ : syracuseStep 262435 = 393653) B393653
theorem B590129 : Blo 259821 590129 := bstep (se 2 (by rfl) ⟨221298, by rfl⟩ : syracuseStep 590129 = 442597) B442597
theorem B393521 : Blo 259821 393521 := bstep (se 2 (by rfl) ⟨147570, by rfl⟩ : syracuseStep 393521 = 295141) B295141
theorem B262451 : Blo 259821 262451 := bstep (se 1 (by rfl) ⟨196838, by rfl⟩ : syracuseStep 262451 = 393677) B393677
theorem B885059 : Blo 259821 885059 := bstep (se 1 (by rfl) ⟨663794, by rfl⟩ : syracuseStep 885059 = 1327589) B1327589
theorem B590147 : Blo 259821 590147 := bstep (se 1 (by rfl) ⟨442610, by rfl⟩ : syracuseStep 590147 = 885221) B885221
theorem B393539 : Blo 259821 393539 := bstep (se 1 (by rfl) ⟨295154, by rfl⟩ : syracuseStep 393539 = 590309) B590309
theorem B262467 : Blo 259821 262467 := bstep (se 1 (by rfl) ⟨196850, by rfl⟩ : syracuseStep 262467 = 393701) B393701
theorem B262483 : Blo 259821 262483 := bstep (se 1 (by rfl) ⟨196862, by rfl⟩ : syracuseStep 262483 = 393725) B393725
theorem B393569 : Blo 259821 393569 := bstep (se 2 (by rfl) ⟨147588, by rfl⟩ : syracuseStep 393569 = 295177) B295177
theorem B295267 : Blo 259821 295267 := bstep (se 1 (by rfl) ⟨221450, by rfl⟩ : syracuseStep 295267 = 442901) B442901
theorem B262499 : Blo 259821 262499 := bstep (se 1 (by rfl) ⟨196874, by rfl⟩ : syracuseStep 262499 = 393749) B393749
theorem B393587 : Blo 259821 393587 := bstep (se 1 (by rfl) ⟨295190, by rfl⟩ : syracuseStep 393587 = 590381) B590381
theorem B262515 : Blo 259821 262515 := bstep (se 1 (by rfl) ⟨196886, by rfl⟩ : syracuseStep 262515 = 393773) B393773
theorem B262531 : Blo 259821 262531 := bstep (se 1 (by rfl) ⟨196898, by rfl⟩ : syracuseStep 262531 = 393797) B393797
theorem B393617 : Blo 259821 393617 := bstep (se 2 (by rfl) ⟨147606, by rfl⟩ : syracuseStep 393617 = 295213) B295213
theorem B262547 : Blo 259821 262547 := bstep (se 1 (by rfl) ⟨196910, by rfl⟩ : syracuseStep 262547 = 393821) B393821
theorem B393635 : Blo 259821 393635 := bstep (se 1 (by rfl) ⟨295226, by rfl⟩ : syracuseStep 393635 = 590453) B590453
theorem B262563 : Blo 259821 262563 := bstep (se 1 (by rfl) ⟨196922, by rfl⟩ : syracuseStep 262563 = 393845) B393845
theorem B262579 : Blo 259821 262579 := bstep (se 1 (by rfl) ⟨196934, by rfl⟩ : syracuseStep 262579 = 393869) B393869
theorem B393665 : Blo 259821 393665 := bstep (se 2 (by rfl) ⟨147624, by rfl⟩ : syracuseStep 393665 = 295249) B295249
theorem B262595 : Blo 259821 262595 := bstep (se 1 (by rfl) ⟨196946, by rfl⟩ : syracuseStep 262595 = 393893) B393893
theorem B393683 : Blo 259821 393683 := bstep (se 1 (by rfl) ⟨295262, by rfl⟩ : syracuseStep 393683 = 590525) B590525
theorem B262611 : Blo 259821 262611 := bstep (se 1 (by rfl) ⟨196958, by rfl⟩ : syracuseStep 262611 = 393917) B393917
theorem B262627 : Blo 259821 262627 := bstep (se 1 (by rfl) ⟨196970, by rfl⟩ : syracuseStep 262627 = 393941) B393941
theorem B393713 : Blo 259821 393713 := bstep (se 2 (by rfl) ⟨147642, by rfl⟩ : syracuseStep 393713 = 295285) B295285
theorem B295411 : Blo 259821 295411 := bstep (se 1 (by rfl) ⟨221558, by rfl⟩ : syracuseStep 295411 = 443117) B443117
theorem B262643 : Blo 259821 262643 := bstep (se 1 (by rfl) ⟨196982, by rfl⟩ : syracuseStep 262643 = 393965) B393965
theorem B393731 : Blo 259821 393731 := bstep (se 1 (by rfl) ⟨295298, by rfl⟩ : syracuseStep 393731 = 590597) B590597
theorem B262659 : Blo 259821 262659 := bstep (se 1 (by rfl) ⟨196994, by rfl⟩ : syracuseStep 262659 = 393989) B393989
theorem B262675 : Blo 259821 262675 := bstep (se 1 (by rfl) ⟨197006, by rfl⟩ : syracuseStep 262675 = 394013) B394013
theorem B393761 : Blo 259821 393761 := bstep (se 2 (by rfl) ⟨147660, by rfl⟩ : syracuseStep 393761 = 295321) B295321
theorem B262691 : Blo 259821 262691 := bstep (se 1 (by rfl) ⟨197018, by rfl⟩ : syracuseStep 262691 = 394037) B394037
theorem B557617 : Blo 259821 557617 := bstep (se 2 (by rfl) ⟨209106, by rfl⟩ : syracuseStep 557617 = 418213) B418213
theorem B393779 : Blo 259821 393779 := bstep (se 1 (by rfl) ⟨295334, by rfl⟩ : syracuseStep 393779 = 590669) B590669
theorem B262707 : Blo 259821 262707 := bstep (se 1 (by rfl) ⟨197030, by rfl⟩ : syracuseStep 262707 = 394061) B394061
theorem B262723 : Blo 259821 262723 := bstep (se 1 (by rfl) ⟨197042, by rfl⟩ : syracuseStep 262723 = 394085) B394085
theorem B885329 : Blo 259821 885329 := bstep (se 2 (by rfl) ⟨331998, by rfl⟩ : syracuseStep 885329 = 663997) B663997
theorem B590417 : Blo 259821 590417 := bstep (se 2 (by rfl) ⟨221406, by rfl⟩ : syracuseStep 590417 = 442813) B442813
theorem B393809 : Blo 259821 393809 := bstep (se 2 (by rfl) ⟨147678, by rfl⟩ : syracuseStep 393809 = 295357) B295357
theorem B262739 : Blo 259821 262739 := bstep (se 1 (by rfl) ⟨197054, by rfl⟩ : syracuseStep 262739 = 394109) B394109
theorem B590435 : Blo 259821 590435 := bstep (se 1 (by rfl) ⟨442826, by rfl⟩ : syracuseStep 590435 = 885653) B885653
theorem B393827 : Blo 259821 393827 := bstep (se 1 (by rfl) ⟨295370, by rfl⟩ : syracuseStep 393827 = 590741) B590741
theorem B262755 : Blo 259821 262755 := bstep (se 1 (by rfl) ⟨197066, by rfl⟩ : syracuseStep 262755 = 394133) B394133
theorem B262771 : Blo 259821 262771 := bstep (se 1 (by rfl) ⟨197078, by rfl⟩ : syracuseStep 262771 = 394157) B394157
theorem B393857 : Blo 259821 393857 := bstep (se 2 (by rfl) ⟨147696, by rfl⟩ : syracuseStep 393857 = 295393) B295393
theorem B295555 : Blo 259821 295555 := bstep (se 1 (by rfl) ⟨221666, by rfl⟩ : syracuseStep 295555 = 443333) B443333
theorem B262787 : Blo 259821 262787 := bstep (se 1 (by rfl) ⟨197090, by rfl⟩ : syracuseStep 262787 = 394181) B394181
theorem B393875 : Blo 259821 393875 := bstep (se 1 (by rfl) ⟨295406, by rfl⟩ : syracuseStep 393875 = 590813) B590813
theorem B262803 : Blo 259821 262803 := bstep (se 1 (by rfl) ⟨197102, by rfl⟩ : syracuseStep 262803 = 394205) B394205
theorem B262819 : Blo 259821 262819 := bstep (se 1 (by rfl) ⟨197114, by rfl⟩ : syracuseStep 262819 = 394229) B394229
theorem B393905 : Blo 259821 393905 := bstep (se 2 (by rfl) ⟨147714, by rfl⟩ : syracuseStep 393905 = 295429) B295429
theorem B262835 : Blo 259821 262835 := bstep (se 1 (by rfl) ⟨197126, by rfl⟩ : syracuseStep 262835 = 394253) B394253
theorem B393923 : Blo 259821 393923 := bstep (se 1 (by rfl) ⟨295442, by rfl⟩ : syracuseStep 393923 = 590885) B590885
theorem B262851 : Blo 259821 262851 := bstep (se 1 (by rfl) ⟨197138, by rfl⟩ : syracuseStep 262851 = 394277) B394277
theorem B262867 : Blo 259821 262867 := bstep (se 1 (by rfl) ⟨197150, by rfl⟩ : syracuseStep 262867 = 394301) B394301
theorem B393953 : Blo 259821 393953 := bstep (se 2 (by rfl) ⟨147732, by rfl⟩ : syracuseStep 393953 = 295465) B295465
theorem B262883 : Blo 259821 262883 := bstep (se 1 (by rfl) ⟨197162, by rfl⟩ : syracuseStep 262883 = 394325) B394325
theorem B393971 : Blo 259821 393971 := bstep (se 1 (by rfl) ⟨295478, by rfl⟩ : syracuseStep 393971 = 590957) B590957
theorem B262899 : Blo 259821 262899 := bstep (se 1 (by rfl) ⟨197174, by rfl⟩ : syracuseStep 262899 = 394349) B394349
theorem B262915 : Blo 259821 262915 := bstep (se 1 (by rfl) ⟨197186, by rfl⟩ : syracuseStep 262915 = 394373) B394373
theorem B394001 : Blo 259821 394001 := bstep (se 2 (by rfl) ⟨147750, by rfl⟩ : syracuseStep 394001 = 295501) B295501
theorem B295699 : Blo 259821 295699 := bstep (se 1 (by rfl) ⟨221774, by rfl⟩ : syracuseStep 295699 = 443549) B443549
theorem B262931 : Blo 259821 262931 := bstep (se 1 (by rfl) ⟨197198, by rfl⟩ : syracuseStep 262931 = 394397) B394397
theorem B12321557 : Blo 259821 12321557 := bstep (se 6 (by rfl) ⟨288786, by rfl⟩ : syracuseStep 12321557 = 577573) B577573
theorem B394019 : Blo 259821 394019 := bstep (se 1 (by rfl) ⟨295514, by rfl⟩ : syracuseStep 394019 = 591029) B591029
theorem B262947 : Blo 259821 262947 := bstep (se 1 (by rfl) ⟨197210, by rfl⟩ : syracuseStep 262947 = 394421) B394421
theorem B262963 : Blo 259821 262963 := bstep (se 1 (by rfl) ⟨197222, by rfl⟩ : syracuseStep 262963 = 394445) B394445
theorem B394049 : Blo 259821 394049 := bstep (se 2 (by rfl) ⟨147768, by rfl⟩ : syracuseStep 394049 = 295537) B295537
theorem B262979 : Blo 259821 262979 := bstep (se 1 (by rfl) ⟨197234, by rfl⟩ : syracuseStep 262979 = 394469) B394469
theorem B394067 : Blo 259821 394067 := bstep (se 1 (by rfl) ⟨295550, by rfl⟩ : syracuseStep 394067 = 591101) B591101
theorem B262995 : Blo 259821 262995 := bstep (se 1 (by rfl) ⟨197246, by rfl⟩ : syracuseStep 262995 = 394493) B394493
theorem B263011 : Blo 259821 263011 := bstep (se 1 (by rfl) ⟨197258, by rfl⟩ : syracuseStep 263011 = 394517) B394517
theorem B590705 : Blo 259821 590705 := bstep (se 2 (by rfl) ⟨221514, by rfl⟩ : syracuseStep 590705 = 443029) B443029
theorem B394097 : Blo 259821 394097 := bstep (se 2 (by rfl) ⟨147786, by rfl⟩ : syracuseStep 394097 = 295573) B295573
theorem B263027 : Blo 259821 263027 := bstep (se 1 (by rfl) ⟨197270, by rfl⟩ : syracuseStep 263027 = 394541) B394541
theorem B590723 : Blo 259821 590723 := bstep (se 1 (by rfl) ⟨443042, by rfl⟩ : syracuseStep 590723 = 886085) B886085
theorem B394115 : Blo 259821 394115 := bstep (se 1 (by rfl) ⟨295586, by rfl⟩ : syracuseStep 394115 = 591173) B591173
theorem B263043 : Blo 259821 263043 := bstep (se 1 (by rfl) ⟨197282, by rfl⟩ : syracuseStep 263043 = 394565) B394565
theorem B263059 : Blo 259821 263059 := bstep (se 1 (by rfl) ⟨197294, by rfl⟩ : syracuseStep 263059 = 394589) B394589
theorem B394145 : Blo 259821 394145 := bstep (se 2 (by rfl) ⟨147804, by rfl⟩ : syracuseStep 394145 = 295609) B295609
theorem B295843 : Blo 259821 295843 := bstep (se 1 (by rfl) ⟨221882, by rfl⟩ : syracuseStep 295843 = 443765) B443765
theorem B263075 : Blo 259821 263075 := bstep (se 1 (by rfl) ⟨197306, by rfl⟩ : syracuseStep 263075 = 394613) B394613
theorem B721841 : Blo 259821 721841 := bstep (se 2 (by rfl) ⟨270690, by rfl⟩ : syracuseStep 721841 = 541381) B541381
theorem B394163 : Blo 259821 394163 := bstep (se 1 (by rfl) ⟨295622, by rfl⟩ : syracuseStep 394163 = 591245) B591245
theorem B263091 : Blo 259821 263091 := bstep (se 1 (by rfl) ⟨197318, by rfl⟩ : syracuseStep 263091 = 394637) B394637
theorem B558019 : Blo 259821 558019 := bstep (se 1 (by rfl) ⟨418514, by rfl⟩ : syracuseStep 558019 = 837029) B837029
theorem B263107 : Blo 259821 263107 := bstep (se 1 (by rfl) ⟨197330, by rfl⟩ : syracuseStep 263107 = 394661) B394661
theorem B394193 : Blo 259821 394193 := bstep (se 2 (by rfl) ⟨147822, by rfl⟩ : syracuseStep 394193 = 295645) B295645
theorem B263123 : Blo 259821 263123 := bstep (se 1 (by rfl) ⟨197342, by rfl⟩ : syracuseStep 263123 = 394685) B394685
theorem B394211 : Blo 259821 394211 := bstep (se 1 (by rfl) ⟨295658, by rfl⟩ : syracuseStep 394211 = 591317) B591317
theorem B263139 : Blo 259821 263139 := bstep (se 1 (by rfl) ⟨197354, by rfl⟩ : syracuseStep 263139 = 394709) B394709
theorem B263155 : Blo 259821 263155 := bstep (se 1 (by rfl) ⟨197366, by rfl⟩ : syracuseStep 263155 = 394733) B394733
theorem B394241 : Blo 259821 394241 := bstep (se 2 (by rfl) ⟨147840, by rfl⟩ : syracuseStep 394241 = 295681) B295681
theorem B263171 : Blo 259821 263171 := bstep (se 1 (by rfl) ⟨197378, by rfl⟩ : syracuseStep 263171 = 394757) B394757
theorem B394259 : Blo 259821 394259 := bstep (se 1 (by rfl) ⟨295694, by rfl⟩ : syracuseStep 394259 = 591389) B591389
theorem B263187 : Blo 259821 263187 := bstep (se 1 (by rfl) ⟨197390, by rfl⟩ : syracuseStep 263187 = 394781) B394781
theorem B263203 : Blo 259821 263203 := bstep (se 1 (by rfl) ⟨197402, by rfl⟩ : syracuseStep 263203 = 394805) B394805
theorem B394289 : Blo 259821 394289 := bstep (se 2 (by rfl) ⟨147858, by rfl⟩ : syracuseStep 394289 = 295717) B295717
theorem B295987 : Blo 259821 295987 := bstep (se 1 (by rfl) ⟨221990, by rfl⟩ : syracuseStep 295987 = 443981) B443981
theorem B263219 : Blo 259821 263219 := bstep (se 1 (by rfl) ⟨197414, by rfl⟩ : syracuseStep 263219 = 394829) B394829
theorem B394307 : Blo 259821 394307 := bstep (se 1 (by rfl) ⟨295730, by rfl⟩ : syracuseStep 394307 = 591461) B591461
theorem B263235 : Blo 259821 263235 := bstep (se 1 (by rfl) ⟨197426, by rfl⟩ : syracuseStep 263235 = 394853) B394853
theorem B263251 : Blo 259821 263251 := bstep (se 1 (by rfl) ⟨197438, by rfl⟩ : syracuseStep 263251 = 394877) B394877
theorem B394337 : Blo 259821 394337 := bstep (se 2 (by rfl) ⟨147876, by rfl⟩ : syracuseStep 394337 = 295753) B295753
theorem B263267 : Blo 259821 263267 := bstep (se 1 (by rfl) ⟨197450, by rfl⟩ : syracuseStep 263267 = 394901) B394901
theorem B885869 : Blo 259821 885869 := bstep (se 3 (by rfl) ⟨166100, by rfl⟩ : syracuseStep 885869 = 332201) B332201
theorem B394355 : Blo 259821 394355 := bstep (se 1 (by rfl) ⟨295766, by rfl⟩ : syracuseStep 394355 = 591533) B591533
theorem B263283 : Blo 259821 263283 := bstep (se 1 (by rfl) ⟨197462, by rfl⟩ : syracuseStep 263283 = 394925) B394925
theorem B263299 : Blo 259821 263299 := bstep (se 1 (by rfl) ⟨197474, by rfl⟩ : syracuseStep 263299 = 394949) B394949
theorem B590993 : Blo 259821 590993 := bstep (se 2 (by rfl) ⟨221622, by rfl⟩ : syracuseStep 590993 = 443245) B443245
theorem B394385 : Blo 259821 394385 := bstep (se 2 (by rfl) ⟨147894, by rfl⟩ : syracuseStep 394385 = 295789) B295789
theorem B263315 : Blo 259821 263315 := bstep (se 1 (by rfl) ⟨197486, by rfl⟩ : syracuseStep 263315 = 394973) B394973
theorem B885923 : Blo 259821 885923 := bstep (se 1 (by rfl) ⟨664442, by rfl⟩ : syracuseStep 885923 = 1328885) B1328885
theorem B591011 : Blo 259821 591011 := bstep (se 1 (by rfl) ⟨443258, by rfl⟩ : syracuseStep 591011 = 886517) B886517
theorem B394403 : Blo 259821 394403 := bstep (se 1 (by rfl) ⟨295802, by rfl⟩ : syracuseStep 394403 = 591605) B591605
theorem B263331 : Blo 259821 263331 := bstep (se 1 (by rfl) ⟨197498, by rfl⟩ : syracuseStep 263331 = 394997) B394997
theorem B263347 : Blo 259821 263347 := bstep (se 1 (by rfl) ⟨197510, by rfl⟩ : syracuseStep 263347 = 395021) B395021
theorem B394433 : Blo 259821 394433 := bstep (se 2 (by rfl) ⟨147912, by rfl⟩ : syracuseStep 394433 = 295825) B295825
theorem B296131 : Blo 259821 296131 := bstep (se 1 (by rfl) ⟨222098, by rfl⟩ : syracuseStep 296131 = 444197) B444197
theorem B263363 : Blo 259821 263363 := bstep (se 1 (by rfl) ⟨197522, by rfl⟩ : syracuseStep 263363 = 395045) B395045
theorem B394451 : Blo 259821 394451 := bstep (se 1 (by rfl) ⟨295838, by rfl⟩ : syracuseStep 394451 = 591677) B591677
theorem B263379 : Blo 259821 263379 := bstep (se 1 (by rfl) ⟨197534, by rfl⟩ : syracuseStep 263379 = 395069) B395069
theorem B263395 : Blo 259821 263395 := bstep (se 1 (by rfl) ⟨197546, by rfl⟩ : syracuseStep 263395 = 395093) B395093
theorem B394481 : Blo 259821 394481 := bstep (se 2 (by rfl) ⟨147930, by rfl⟩ : syracuseStep 394481 = 295861) B295861
theorem B263411 : Blo 259821 263411 := bstep (se 1 (by rfl) ⟨197558, by rfl⟩ : syracuseStep 263411 = 395117) B395117
theorem B394499 : Blo 259821 394499 := bstep (se 1 (by rfl) ⟨295874, by rfl⟩ : syracuseStep 394499 = 591749) B591749
theorem B263427 : Blo 259821 263427 := bstep (se 1 (by rfl) ⟨197570, by rfl⟩ : syracuseStep 263427 = 395141) B395141
theorem B263443 : Blo 259821 263443 := bstep (se 1 (by rfl) ⟨197582, by rfl⟩ : syracuseStep 263443 = 395165) B395165
theorem B394529 : Blo 259821 394529 := bstep (se 2 (by rfl) ⟨147948, by rfl⟩ : syracuseStep 394529 = 295897) B295897
theorem B263459 : Blo 259821 263459 := bstep (se 1 (by rfl) ⟨197594, by rfl⟩ : syracuseStep 263459 = 395189) B395189
theorem B394547 : Blo 259821 394547 := bstep (se 1 (by rfl) ⟨295910, by rfl⟩ : syracuseStep 394547 = 591821) B591821
theorem B263475 : Blo 259821 263475 := bstep (se 1 (by rfl) ⟨197606, by rfl⟩ : syracuseStep 263475 = 395213) B395213
theorem B263491 : Blo 259821 263491 := bstep (se 1 (by rfl) ⟨197618, by rfl⟩ : syracuseStep 263491 = 395237) B395237
theorem B755021 : Blo 259821 755021 := bstep (se 3 (by rfl) ⟨141566, by rfl⟩ : syracuseStep 755021 = 283133) B283133
theorem B394577 : Blo 259821 394577 := bstep (se 2 (by rfl) ⟨147966, by rfl⟩ : syracuseStep 394577 = 295933) B295933
theorem B296275 : Blo 259821 296275 := bstep (se 1 (by rfl) ⟨222206, by rfl⟩ : syracuseStep 296275 = 444413) B444413
theorem B263507 : Blo 259821 263507 := bstep (se 1 (by rfl) ⟨197630, by rfl⟩ : syracuseStep 263507 = 395261) B395261
theorem B1115491 : Blo 259821 1115491 := bstep (se 1 (by rfl) ⟨836618, by rfl⟩ : syracuseStep 1115491 = 1673237) B1673237
theorem B394595 : Blo 259821 394595 := bstep (se 1 (by rfl) ⟨295946, by rfl⟩ : syracuseStep 394595 = 591893) B591893
theorem B263523 : Blo 259821 263523 := bstep (se 1 (by rfl) ⟨197642, by rfl⟩ : syracuseStep 263523 = 395285) B395285
theorem B263539 : Blo 259821 263539 := bstep (se 1 (by rfl) ⟨197654, by rfl⟩ : syracuseStep 263539 = 395309) B395309
theorem B394625 : Blo 259821 394625 := bstep (se 2 (by rfl) ⟨147984, by rfl⟩ : syracuseStep 394625 = 295969) B295969
theorem B263555 : Blo 259821 263555 := bstep (se 1 (by rfl) ⟨197666, by rfl⟩ : syracuseStep 263555 = 395333) B395333
theorem B394643 : Blo 259821 394643 := bstep (se 1 (by rfl) ⟨295982, by rfl⟩ : syracuseStep 394643 = 591965) B591965
theorem B263571 : Blo 259821 263571 := bstep (se 1 (by rfl) ⟨197678, by rfl⟩ : syracuseStep 263571 = 395357) B395357
theorem B329123 : Blo 259821 329123 := bstep (se 1 (by rfl) ⟨246842, by rfl⟩ : syracuseStep 329123 = 493685) B493685
theorem B263587 : Blo 259821 263587 := bstep (se 1 (by rfl) ⟨197690, by rfl⟩ : syracuseStep 263587 = 395381) B395381
theorem B886193 : Blo 259821 886193 := bstep (se 2 (by rfl) ⟨332322, by rfl⟩ : syracuseStep 886193 = 664645) B664645
theorem B591281 : Blo 259821 591281 := bstep (se 2 (by rfl) ⟨221730, by rfl⟩ : syracuseStep 591281 = 443461) B443461
theorem B394673 : Blo 259821 394673 := bstep (se 2 (by rfl) ⟨148002, by rfl⟩ : syracuseStep 394673 = 296005) B296005
theorem B263603 : Blo 259821 263603 := bstep (se 1 (by rfl) ⟨197702, by rfl⟩ : syracuseStep 263603 = 395405) B395405
theorem B591299 : Blo 259821 591299 := bstep (se 1 (by rfl) ⟨443474, by rfl⟩ : syracuseStep 591299 = 886949) B886949
theorem B394691 : Blo 259821 394691 := bstep (se 1 (by rfl) ⟨296018, by rfl⟩ : syracuseStep 394691 = 592037) B592037
theorem B1672645 : Blo 259821 1672645 := bstep (se 4 (by rfl) ⟨156810, by rfl⟩ : syracuseStep 1672645 = 313621) B313621
theorem B263619 : Blo 259821 263619 := bstep (se 1 (by rfl) ⟨197714, by rfl⟩ : syracuseStep 263619 = 395429) B395429
theorem B263635 : Blo 259821 263635 := bstep (se 1 (by rfl) ⟨197726, by rfl⟩ : syracuseStep 263635 = 395453) B395453
theorem B394721 : Blo 259821 394721 := bstep (se 2 (by rfl) ⟨148020, by rfl⟩ : syracuseStep 394721 = 296041) B296041
theorem B296419 : Blo 259821 296419 := bstep (se 1 (by rfl) ⟨222314, by rfl⟩ : syracuseStep 296419 = 444629) B444629
theorem B263651 : Blo 259821 263651 := bstep (se 1 (by rfl) ⟨197738, by rfl⟩ : syracuseStep 263651 = 395477) B395477
theorem B394739 : Blo 259821 394739 := bstep (se 1 (by rfl) ⟨296054, by rfl⟩ : syracuseStep 394739 = 592109) B592109
theorem B263667 : Blo 259821 263667 := bstep (se 1 (by rfl) ⟨197750, by rfl⟩ : syracuseStep 263667 = 395501) B395501
theorem B263683 : Blo 259821 263683 := bstep (se 1 (by rfl) ⟨197762, by rfl⟩ : syracuseStep 263683 = 395525) B395525
theorem B394769 : Blo 259821 394769 := bstep (se 2 (by rfl) ⟨148038, by rfl⟩ : syracuseStep 394769 = 296077) B296077
theorem B263699 : Blo 259821 263699 := bstep (se 1 (by rfl) ⟨197774, by rfl⟩ : syracuseStep 263699 = 395549) B395549
theorem B394787 : Blo 259821 394787 := bstep (se 1 (by rfl) ⟨296090, by rfl⟩ : syracuseStep 394787 = 592181) B592181
theorem B263715 : Blo 259821 263715 := bstep (se 1 (by rfl) ⟨197786, by rfl⟩ : syracuseStep 263715 = 395573) B395573
theorem B263731 : Blo 259821 263731 := bstep (se 1 (by rfl) ⟨197798, by rfl⟩ : syracuseStep 263731 = 395597) B395597
theorem B394817 : Blo 259821 394817 := bstep (se 2 (by rfl) ⟨148056, by rfl⟩ : syracuseStep 394817 = 296113) B296113
theorem B263747 : Blo 259821 263747 := bstep (se 1 (by rfl) ⟨197810, by rfl⟩ : syracuseStep 263747 = 395621) B395621
theorem B394835 : Blo 259821 394835 := bstep (se 1 (by rfl) ⟨296126, by rfl⟩ : syracuseStep 394835 = 592253) B592253
theorem B263763 : Blo 259821 263763 := bstep (se 1 (by rfl) ⟨197822, by rfl⟩ : syracuseStep 263763 = 395645) B395645
theorem B263779 : Blo 259821 263779 := bstep (se 1 (by rfl) ⟨197834, by rfl⟩ : syracuseStep 263779 = 395669) B395669
theorem B788077 : Blo 259821 788077 := bstep (se 3 (by rfl) ⟨147764, by rfl⟩ : syracuseStep 788077 = 295529) B295529
theorem B394865 : Blo 259821 394865 := bstep (se 2 (by rfl) ⟨148074, by rfl⟩ : syracuseStep 394865 = 296149) B296149
theorem B296563 : Blo 259821 296563 := bstep (se 1 (by rfl) ⟨222422, by rfl⟩ : syracuseStep 296563 = 444845) B444845
theorem B263795 : Blo 259821 263795 := bstep (se 1 (by rfl) ⟨197846, by rfl⟩ : syracuseStep 263795 = 395693) B395693
theorem B394883 : Blo 259821 394883 := bstep (se 1 (by rfl) ⟨296162, by rfl⟩ : syracuseStep 394883 = 592325) B592325
theorem B263811 : Blo 259821 263811 := bstep (se 1 (by rfl) ⟨197858, by rfl⟩ : syracuseStep 263811 = 395717) B395717
theorem B394913 : Blo 259821 394913 := bstep (se 2 (by rfl) ⟨148092, by rfl⟩ : syracuseStep 394913 = 296185) B296185
theorem B394931 : Blo 259821 394931 := bstep (se 1 (by rfl) ⟨296198, by rfl⟩ : syracuseStep 394931 = 592397) B592397
theorem B591569 : Blo 259821 591569 := bstep (se 2 (by rfl) ⟨221838, by rfl⟩ : syracuseStep 591569 = 443677) B443677
theorem B394961 : Blo 259821 394961 := bstep (se 2 (by rfl) ⟨148110, by rfl⟩ : syracuseStep 394961 = 296221) B296221
theorem B493283 : Blo 259821 493283 := bstep (se 1 (by rfl) ⟨369962, by rfl⟩ : syracuseStep 493283 = 739925) B739925
theorem B591587 : Blo 259821 591587 := bstep (se 1 (by rfl) ⟨443690, by rfl⟩ : syracuseStep 591587 = 887381) B887381
theorem B394979 : Blo 259821 394979 := bstep (se 1 (by rfl) ⟨296234, by rfl⟩ : syracuseStep 394979 = 592469) B592469
theorem B395009 : Blo 259821 395009 := bstep (se 2 (by rfl) ⟨148128, by rfl⟩ : syracuseStep 395009 = 296257) B296257
theorem B296707 : Blo 259821 296707 := bstep (se 1 (by rfl) ⟨222530, by rfl⟩ : syracuseStep 296707 = 445061) B445061
theorem B1410821 : Blo 259821 1410821 := bstep (se 4 (by rfl) ⟨132264, by rfl⟩ : syracuseStep 1410821 = 264529) B264529
theorem B395027 : Blo 259821 395027 := bstep (se 1 (by rfl) ⟨296270, by rfl⟩ : syracuseStep 395027 = 592541) B592541
theorem B395057 : Blo 259821 395057 := bstep (se 2 (by rfl) ⟨148146, by rfl⟩ : syracuseStep 395057 = 296293) B296293
theorem B395075 : Blo 259821 395075 := bstep (se 1 (by rfl) ⟨296306, by rfl⟩ : syracuseStep 395075 = 592613) B592613
theorem B395105 : Blo 259821 395105 := bstep (se 2 (by rfl) ⟨148164, by rfl⟩ : syracuseStep 395105 = 296329) B296329
theorem B395123 : Blo 259821 395123 := bstep (se 1 (by rfl) ⟨296342, by rfl⟩ : syracuseStep 395123 = 592685) B592685
theorem B722819 : Blo 259821 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B1410949 : Blo 259821 1410949 := bstep (se 4 (by rfl) ⟨132276, by rfl⟩ : syracuseStep 1410949 = 264553) B264553
theorem B395153 : Blo 259821 395153 := bstep (se 2 (by rfl) ⟨148182, by rfl⟩ : syracuseStep 395153 = 296365) B296365
theorem B395171 : Blo 259821 395171 := bstep (se 1 (by rfl) ⟨296378, by rfl⟩ : syracuseStep 395171 = 592757) B592757
theorem B395201 : Blo 259821 395201 := bstep (se 2 (by rfl) ⟨148200, by rfl⟩ : syracuseStep 395201 = 296401) B296401
theorem B886733 : Blo 259821 886733 := bstep (se 3 (by rfl) ⟨166262, by rfl⟩ : syracuseStep 886733 = 332525) B332525
theorem B395219 : Blo 259821 395219 := bstep (se 1 (by rfl) ⟨296414, by rfl⟩ : syracuseStep 395219 = 592829) B592829
theorem B591857 : Blo 259821 591857 := bstep (se 2 (by rfl) ⟨221946, by rfl⟩ : syracuseStep 591857 = 443893) B443893
theorem B395249 : Blo 259821 395249 := bstep (se 2 (by rfl) ⟨148218, by rfl⟩ : syracuseStep 395249 = 296437) B296437
theorem B886787 : Blo 259821 886787 := bstep (se 1 (by rfl) ⟨665090, by rfl⟩ : syracuseStep 886787 = 1330181) B1330181
theorem B591875 : Blo 259821 591875 := bstep (se 1 (by rfl) ⟨443906, by rfl⟩ : syracuseStep 591875 = 887813) B887813
theorem B395267 : Blo 259821 395267 := bstep (se 1 (by rfl) ⟨296450, by rfl⟩ : syracuseStep 395267 = 592901) B592901
theorem B395297 : Blo 259821 395297 := bstep (se 2 (by rfl) ⟨148236, by rfl⟩ : syracuseStep 395297 = 296473) B296473
theorem B395315 : Blo 259821 395315 := bstep (se 1 (by rfl) ⟨296486, by rfl⟩ : syracuseStep 395315 = 592973) B592973
theorem B395345 : Blo 259821 395345 := bstep (se 2 (by rfl) ⟨148254, by rfl⟩ : syracuseStep 395345 = 296509) B296509
theorem B329827 : Blo 259821 329827 := bstep (se 1 (by rfl) ⟨247370, by rfl⟩ : syracuseStep 329827 = 494741) B494741
theorem B395363 : Blo 259821 395363 := bstep (se 1 (by rfl) ⟨296522, by rfl⟩ : syracuseStep 395363 = 593045) B593045
theorem B395393 : Blo 259821 395393 := bstep (se 2 (by rfl) ⟨148272, by rfl⟩ : syracuseStep 395393 = 296545) B296545
theorem B395411 : Blo 259821 395411 := bstep (se 1 (by rfl) ⟨296558, by rfl⟩ : syracuseStep 395411 = 593117) B593117
theorem B395441 : Blo 259821 395441 := bstep (se 2 (by rfl) ⟨148290, by rfl⟩ : syracuseStep 395441 = 296581) B296581
theorem B329923 : Blo 259821 329923 := bstep (se 1 (by rfl) ⟨247442, by rfl⟩ : syracuseStep 329923 = 494885) B494885
theorem B395459 : Blo 259821 395459 := bstep (se 1 (by rfl) ⟨296594, by rfl⟩ : syracuseStep 395459 = 593189) B593189
theorem B395489 : Blo 259821 395489 := bstep (se 2 (by rfl) ⟨148308, by rfl⟩ : syracuseStep 395489 = 296617) B296617
theorem B395507 : Blo 259821 395507 := bstep (se 1 (by rfl) ⟨296630, by rfl⟩ : syracuseStep 395507 = 593261) B593261
theorem B887057 : Blo 259821 887057 := bstep (se 2 (by rfl) ⟨332646, by rfl⟩ : syracuseStep 887057 = 665293) B665293
theorem B592145 : Blo 259821 592145 := bstep (se 2 (by rfl) ⟨222054, by rfl⟩ : syracuseStep 592145 = 444109) B444109
theorem B395537 : Blo 259821 395537 := bstep (se 2 (by rfl) ⟨148326, by rfl⟩ : syracuseStep 395537 = 296653) B296653
theorem B592163 : Blo 259821 592163 := bstep (se 1 (by rfl) ⟨444122, by rfl⟩ : syracuseStep 592163 = 888245) B888245
theorem B395555 : Blo 259821 395555 := bstep (se 1 (by rfl) ⟨296666, by rfl⟩ : syracuseStep 395555 = 593333) B593333
theorem B395585 : Blo 259821 395585 := bstep (se 2 (by rfl) ⟨148344, by rfl⟩ : syracuseStep 395585 = 296689) B296689
theorem B3180869 : Blo 259821 3180869 := bstep (se 4 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 3180869 = 596413) B596413
theorem B395603 : Blo 259821 395603 := bstep (se 1 (by rfl) ⟨296702, by rfl⟩ : syracuseStep 395603 = 593405) B593405
theorem B5048689 : Blo 259821 5048689 := bstep (se 2 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 5048689 = 3786517) B3786517
theorem B395633 : Blo 259821 395633 := bstep (se 2 (by rfl) ⟨148362, by rfl⟩ : syracuseStep 395633 = 296725) B296725
theorem B395651 : Blo 259821 395651 := bstep (se 1 (by rfl) ⟨296738, by rfl⟩ : syracuseStep 395651 = 593477) B593477
theorem B395681 : Blo 259821 395681 := bstep (se 2 (by rfl) ⟨148380, by rfl⟩ : syracuseStep 395681 = 296761) B296761
theorem B559523 : Blo 259821 559523 := bstep (se 1 (by rfl) ⟨419642, by rfl⟩ : syracuseStep 559523 = 839285) B839285
theorem B657841 : Blo 259821 657841 := bstep (se 2 (by rfl) ⟨246690, by rfl⟩ : syracuseStep 657841 = 493381) B493381
theorem B395699 : Blo 259821 395699 := bstep (se 1 (by rfl) ⟨296774, by rfl⟩ : syracuseStep 395699 = 593549) B593549
theorem B395729 : Blo 259821 395729 := bstep (se 2 (by rfl) ⟨148398, by rfl⟩ : syracuseStep 395729 = 296797) B296797
theorem B592433 : Blo 259821 592433 := bstep (se 2 (by rfl) ⟨222162, by rfl⟩ : syracuseStep 592433 = 444325) B444325
theorem B592451 : Blo 259821 592451 := bstep (se 1 (by rfl) ⟨444338, by rfl⟩ : syracuseStep 592451 = 888677) B888677
theorem B395857 : Blo 259821 395857 := bstep (se 2 (by rfl) ⟨148446, by rfl⟩ : syracuseStep 395857 = 296893) B296893
theorem B330419 : Blo 259821 330419 := bstep (se 1 (by rfl) ⟨247814, by rfl⟩ : syracuseStep 330419 = 495629) B495629
theorem B3148469 : Blo 259821 3148469 := bstep (se 5 (by rfl) ⟨147584, by rfl⟩ : syracuseStep 3148469 = 295169) B295169
theorem B658115 : Blo 259821 658115 := bstep (se 1 (by rfl) ⟨493586, by rfl⟩ : syracuseStep 658115 = 987173) B987173
theorem B8784611 : Blo 259821 8784611 := bstep (se 1 (by rfl) ⟨6588458, by rfl⟩ : syracuseStep 8784611 = 13176917) B13176917
theorem B494353 : Blo 259821 494353 := bstep (se 2 (by rfl) ⟨185382, by rfl⟩ : syracuseStep 494353 = 370765) B370765
theorem B887597 : Blo 259821 887597 := bstep (se 3 (by rfl) ⟨166424, by rfl⟩ : syracuseStep 887597 = 332849) B332849
theorem B625475 : Blo 259821 625475 := bstep (se 1 (by rfl) ⟨469106, by rfl⟩ : syracuseStep 625475 = 938213) B938213
theorem B592721 : Blo 259821 592721 := bstep (se 2 (by rfl) ⟨222270, by rfl⟩ : syracuseStep 592721 = 444541) B444541
theorem B887651 : Blo 259821 887651 := bstep (se 1 (by rfl) ⟨665738, by rfl⟩ : syracuseStep 887651 = 1331477) B1331477
theorem B592739 : Blo 259821 592739 := bstep (se 1 (by rfl) ⟨444554, by rfl⟩ : syracuseStep 592739 = 889109) B889109
theorem B658307 : Blo 259821 658307 := bstep (se 1 (by rfl) ⟨493730, by rfl⟩ : syracuseStep 658307 = 987461) B987461
theorem B887921 : Blo 259821 887921 := bstep (se 2 (by rfl) ⟨332970, by rfl⟩ : syracuseStep 887921 = 665941) B665941
theorem B593009 : Blo 259821 593009 := bstep (se 2 (by rfl) ⟨222378, by rfl⟩ : syracuseStep 593009 = 444757) B444757
theorem B593027 : Blo 259821 593027 := bstep (se 1 (by rfl) ⟨444770, by rfl⟩ : syracuseStep 593027 = 889541) B889541
theorem B625859 : Blo 259821 625859 := bstep (se 1 (by rfl) ⟨469394, by rfl⟩ : syracuseStep 625859 = 938789) B938789
theorem B4754659 : Blo 259821 4754659 := bstep (se 1 (by rfl) ⟨3565994, by rfl⟩ : syracuseStep 4754659 = 7131989) B7131989
theorem B298243 : Blo 259821 298243 := bstep (se 1 (by rfl) ⟨223682, by rfl⟩ : syracuseStep 298243 = 447365) B447365
theorem B1117489 : Blo 259821 1117489 := bstep (se 2 (by rfl) ⟨419058, by rfl⟩ : syracuseStep 1117489 = 838117) B838117
theorem B331123 : Blo 259821 331123 := bstep (se 1 (by rfl) ⟨248342, by rfl⟩ : syracuseStep 331123 = 496685) B496685
theorem B593297 : Blo 259821 593297 := bstep (se 2 (by rfl) ⟨222486, by rfl⟩ : syracuseStep 593297 = 444973) B444973
theorem B593315 : Blo 259821 593315 := bstep (se 1 (by rfl) ⟨444986, by rfl⟩ : syracuseStep 593315 = 889973) B889973
theorem B331219 : Blo 259821 331219 := bstep (se 1 (by rfl) ⟨248414, by rfl⟩ : syracuseStep 331219 = 496829) B496829
theorem B527939 : Blo 259821 527939 := bstep (se 1 (by rfl) ⟨395954, by rfl⟩ : syracuseStep 527939 = 791909) B791909
theorem B986701 : Blo 259821 986701 := bstep (se 3 (by rfl) ⟨185006, by rfl⟩ : syracuseStep 986701 = 370013) B370013
theorem B560753 : Blo 259821 560753 := bstep (se 2 (by rfl) ⟨210282, by rfl⟩ : syracuseStep 560753 = 420565) B420565
theorem B888461 : Blo 259821 888461 := bstep (se 3 (by rfl) ⟨166586, by rfl⟩ : syracuseStep 888461 = 333173) B333173
theorem B593585 : Blo 259821 593585 := bstep (se 2 (by rfl) ⟨222594, by rfl⟩ : syracuseStep 593585 = 445189) B445189
theorem B888515 : Blo 259821 888515 := bstep (se 1 (by rfl) ⟨666386, by rfl⟩ : syracuseStep 888515 = 1332773) B1332773
theorem B626417 : Blo 259821 626417 := bstep (se 2 (by rfl) ⟨234906, by rfl⟩ : syracuseStep 626417 = 469813) B469813
theorem B659249 : Blo 259821 659249 := bstep (se 2 (by rfl) ⟨247218, by rfl⟩ : syracuseStep 659249 = 494437) B494437
theorem B495409 : Blo 259821 495409 := bstep (se 2 (by rfl) ⟨185778, by rfl⟩ : syracuseStep 495409 = 371557) B371557
theorem B659299 : Blo 259821 659299 := bstep (se 1 (by rfl) ⟨494474, by rfl⟩ : syracuseStep 659299 = 988949) B988949
theorem B397219 : Blo 259821 397219 := bstep (se 1 (by rfl) ⟨297914, by rfl⟩ : syracuseStep 397219 = 595829) B595829
theorem B626627 : Blo 259821 626627 := bstep (se 1 (by rfl) ⟨469970, by rfl⟩ : syracuseStep 626627 = 939941) B939941
theorem B331715 : Blo 259821 331715 := bstep (se 1 (by rfl) ⟨248786, by rfl⟩ : syracuseStep 331715 = 497573) B497573
theorem B888785 : Blo 259821 888785 := bstep (se 2 (by rfl) ⟨333294, by rfl⟩ : syracuseStep 888785 = 666589) B666589
theorem B790499 : Blo 259821 790499 := bstep (se 1 (by rfl) ⟨592874, by rfl⟩ : syracuseStep 790499 = 1185749) B1185749
theorem B659441 : Blo 259821 659441 := bstep (se 2 (by rfl) ⟨247290, by rfl⟩ : syracuseStep 659441 = 494581) B494581
theorem B1609763 : Blo 259821 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B1675363 : Blo 259821 1675363 := bstep (se 1 (by rfl) ⟨1256522, by rfl⟩ : syracuseStep 1675363 = 2513045) B2513045
theorem B790669 : Blo 259821 790669 := bstep (se 3 (by rfl) ⟨148250, by rfl⟩ : syracuseStep 790669 = 296501) B296501
theorem B495811 : Blo 259821 495811 := bstep (se 1 (by rfl) ⟨371858, by rfl⟩ : syracuseStep 495811 = 743717) B743717
theorem B495857 : Blo 259821 495857 := bstep (se 2 (by rfl) ⟨185946, by rfl⟩ : syracuseStep 495857 = 371893) B371893
theorem B987491 : Blo 259821 987491 := bstep (se 1 (by rfl) ⟨740618, by rfl⟩ : syracuseStep 987491 = 1481237) B1481237
theorem B8556997 : Blo 259821 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B889325 : Blo 259821 889325 := bstep (se 3 (by rfl) ⟨166748, by rfl⟩ : syracuseStep 889325 = 333497) B333497
theorem B561649 : Blo 259821 561649 := bstep (se 2 (by rfl) ⟨210618, by rfl⟩ : syracuseStep 561649 = 421237) B421237
theorem B561667 : Blo 259821 561667 := bstep (se 1 (by rfl) ⟨421250, by rfl⟩ : syracuseStep 561667 = 842501) B842501
theorem B496145 : Blo 259821 496145 := bstep (se 2 (by rfl) ⟨186054, by rfl⟩ : syracuseStep 496145 = 372109) B372109
theorem B889379 : Blo 259821 889379 := bstep (se 1 (by rfl) ⟨667034, by rfl⟩ : syracuseStep 889379 = 1334069) B1334069
theorem B528977 : Blo 259821 528977 := bstep (se 2 (by rfl) ⟨198366, by rfl⟩ : syracuseStep 528977 = 396733) B396733
theorem B332419 : Blo 259821 332419 := bstep (se 1 (by rfl) ⟨249314, by rfl⟩ : syracuseStep 332419 = 498629) B498629
theorem B332515 : Blo 259821 332515 := bstep (se 1 (by rfl) ⟨249386, by rfl⟩ : syracuseStep 332515 = 498773) B498773
theorem B627473 : Blo 259821 627473 := bstep (se 2 (by rfl) ⟨235302, by rfl⟩ : syracuseStep 627473 = 470605) B470605
theorem B889649 : Blo 259821 889649 := bstep (se 2 (by rfl) ⟨333618, by rfl⟩ : syracuseStep 889649 = 667237) B667237
theorem B660433 : Blo 259821 660433 := bstep (se 2 (by rfl) ⟨247662, by rfl⟩ : syracuseStep 660433 = 495325) B495325
theorem B988145 : Blo 259821 988145 := bstep (se 2 (by rfl) ⟨370554, by rfl⟩ : syracuseStep 988145 = 741109) B741109
theorem B791569 : Blo 259821 791569 := bstep (se 2 (by rfl) ⟨296838, by rfl⟩ : syracuseStep 791569 = 593677) B593677
theorem B1348643 : Blo 259821 1348643 := bstep (se 1 (by rfl) ⟨1011482, by rfl⟩ : syracuseStep 1348643 = 2022965) B2022965
theorem B1479779 : Blo 259821 1479779 := bstep (se 1 (by rfl) ⟨1109834, by rfl⟩ : syracuseStep 1479779 = 2219669) B2219669
theorem B333011 : Blo 259821 333011 := bstep (se 1 (by rfl) ⟨249758, by rfl⟩ : syracuseStep 333011 = 499517) B499517
theorem B660707 : Blo 259821 660707 := bstep (se 1 (by rfl) ⟨495530, by rfl⟩ : syracuseStep 660707 = 991061) B991061
theorem B496867 : Blo 259821 496867 := bstep (se 1 (by rfl) ⟨372650, by rfl⟩ : syracuseStep 496867 = 745301) B745301
theorem B628003 : Blo 259821 628003 := bstep (se 1 (by rfl) ⟨471002, by rfl⟩ : syracuseStep 628003 = 942005) B942005
theorem B890189 : Blo 259821 890189 := bstep (se 3 (by rfl) ⟨166910, by rfl⟩ : syracuseStep 890189 = 333821) B333821
theorem B890243 : Blo 259821 890243 := bstep (se 1 (by rfl) ⟨667682, by rfl⟩ : syracuseStep 890243 = 1335365) B1335365
theorem B267667 : Blo 259821 267667 := bstep (se 1 (by rfl) ⟨200750, by rfl⟩ : syracuseStep 267667 = 401501) B401501
theorem B660899 : Blo 259821 660899 := bstep (se 1 (by rfl) ⟨495674, by rfl⟩ : syracuseStep 660899 = 991349) B991349
theorem B300515 : Blo 259821 300515 := bstep (se 1 (by rfl) ⟨225386, by rfl⟩ : syracuseStep 300515 = 450773) B450773
theorem B333347 : Blo 259821 333347 := bstep (se 1 (by rfl) ⟨250010, by rfl⟩ : syracuseStep 333347 = 500021) B500021
theorem B398947 : Blo 259821 398947 := bstep (se 1 (by rfl) ⟨299210, by rfl⟩ : syracuseStep 398947 = 598421) B598421
theorem B497315 : Blo 259821 497315 := bstep (se 1 (by rfl) ⟨372986, by rfl⟩ : syracuseStep 497315 = 745973) B745973
theorem B1251085 : Blo 259821 1251085 := bstep (se 3 (by rfl) ⟨234578, by rfl⟩ : syracuseStep 1251085 = 469157) B469157
theorem B333715 : Blo 259821 333715 := bstep (se 1 (by rfl) ⟨250286, by rfl⟩ : syracuseStep 333715 = 500573) B500573
theorem B497603 : Blo 259821 497603 := bstep (se 1 (by rfl) ⟨373202, by rfl⟩ : syracuseStep 497603 = 746405) B746405
theorem B333811 : Blo 259821 333811 := bstep (se 1 (by rfl) ⟨250358, by rfl⟩ : syracuseStep 333811 = 500717) B500717
theorem B1677361 : Blo 259821 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B1480781 : Blo 259821 1480781 := bstep (se 3 (by rfl) ⟨277646, by rfl⟩ : syracuseStep 1480781 = 555293) B555293
theorem B2398349 : Blo 259821 2398349 := bstep (se 3 (by rfl) ⟨449690, by rfl⟩ : syracuseStep 2398349 = 899381) B899381
theorem B661841 : Blo 259821 661841 := bstep (se 2 (by rfl) ⟨248190, by rfl⟩ : syracuseStep 661841 = 496381) B496381
theorem B399713 : Blo 259821 399713 := bstep (se 2 (by rfl) ⟨149892, by rfl⟩ : syracuseStep 399713 = 299785) B299785
theorem B399745 : Blo 259821 399745 := bstep (se 2 (by rfl) ⟨149904, by rfl⟩ : syracuseStep 399745 = 299809) B299809
theorem B661891 : Blo 259821 661891 := bstep (se 1 (by rfl) ⟨496418, by rfl⟩ : syracuseStep 661891 = 992837) B992837
theorem B989603 : Blo 259821 989603 := bstep (se 1 (by rfl) ⟨742202, by rfl⟩ : syracuseStep 989603 = 1484405) B1484405
theorem B989617 : Blo 259821 989617 := bstep (se 2 (by rfl) ⟨371106, by rfl⟩ : syracuseStep 989617 = 742213) B742213
theorem B662033 : Blo 259821 662033 := bstep (se 2 (by rfl) ⟨248262, by rfl⟩ : syracuseStep 662033 = 496525) B496525
theorem B400115 : Blo 259821 400115 := bstep (se 1 (by rfl) ⟨300086, by rfl⟩ : syracuseStep 400115 = 600173) B600173
theorem B596771 : Blo 259821 596771 := bstep (se 1 (by rfl) ⟨447578, by rfl⟩ : syracuseStep 596771 = 895157) B895157
theorem B2988899 : Blo 259821 2988899 := bstep (se 1 (by rfl) ⟨2241674, by rfl⟩ : syracuseStep 2988899 = 4483349) B4483349
theorem B498545 : Blo 259821 498545 := bstep (se 2 (by rfl) ⟨186954, by rfl⟩ : syracuseStep 498545 = 373909) B373909
theorem B269443 : Blo 259821 269443 := bstep (se 1 (by rfl) ⟨202082, by rfl⟩ : syracuseStep 269443 = 404165) B404165
theorem B1121521 : Blo 259821 1121521 := bstep (se 2 (by rfl) ⟨420570, by rfl⟩ : syracuseStep 1121521 = 841141) B841141
theorem B1318193 : Blo 259821 1318193 := bstep (se 2 (by rfl) ⟨494322, by rfl⟩ : syracuseStep 1318193 = 988645) B988645
theorem B1023331 : Blo 259821 1023331 := bstep (se 1 (by rfl) ⟨767498, by rfl⟩ : syracuseStep 1023331 = 1534997) B1534997
theorem B400771 : Blo 259821 400771 := bstep (se 1 (by rfl) ⟨300578, by rfl⟩ : syracuseStep 400771 = 601157) B601157
theorem B1973645 : Blo 259821 1973645 := bstep (se 3 (by rfl) ⟨370058, by rfl⟩ : syracuseStep 1973645 = 740117) B740117
theorem B400819 : Blo 259821 400819 := bstep (se 1 (by rfl) ⟨300614, by rfl⟩ : syracuseStep 400819 = 601229) B601229
theorem B6757829 : Blo 259821 6757829 := bstep (se 4 (by rfl) ⟨633546, by rfl⟩ : syracuseStep 6757829 = 1267093) B1267093
theorem B564689 : Blo 259821 564689 := bstep (se 2 (by rfl) ⟨211758, by rfl⟩ : syracuseStep 564689 = 423517) B423517
theorem B663025 : Blo 259821 663025 := bstep (se 2 (by rfl) ⟨248634, by rfl⟩ : syracuseStep 663025 = 497269) B497269
theorem B499441 : Blo 259821 499441 := bstep (se 2 (by rfl) ⟨187290, by rfl⟩ : syracuseStep 499441 = 374581) B374581
theorem B663299 : Blo 259821 663299 := bstep (se 1 (by rfl) ⟨497474, by rfl⟩ : syracuseStep 663299 = 994949) B994949
theorem B991075 : Blo 259821 991075 := bstep (se 1 (by rfl) ⟨743306, by rfl⟩ : syracuseStep 991075 = 1486613) B1486613
theorem B3383153 : Blo 259821 3383153 := bstep (se 2 (by rfl) ⟨1268682, by rfl⟩ : syracuseStep 3383153 = 2537365) B2537365
theorem B499601 : Blo 259821 499601 := bstep (se 2 (by rfl) ⟨187350, by rfl⟩ : syracuseStep 499601 = 374701) B374701
theorem B597937 : Blo 259821 597937 := bstep (se 2 (by rfl) ⟨224226, by rfl⟩ : syracuseStep 597937 = 448453) B448453
theorem B663491 : Blo 259821 663491 := bstep (se 1 (by rfl) ⟨497618, by rfl⟩ : syracuseStep 663491 = 995237) B995237
theorem B532433 : Blo 259821 532433 := bstep (se 2 (by rfl) ⟨199662, by rfl⟩ : syracuseStep 532433 = 399325) B399325
theorem B5480561 : Blo 259821 5480561 := bstep (se 2 (by rfl) ⟨2055210, by rfl⟩ : syracuseStep 5480561 = 4110421) B4110421
theorem B500003 : Blo 259821 500003 := bstep (se 1 (by rfl) ⟨375002, by rfl⟩ : syracuseStep 500003 = 750005) B750005
theorem B1417571 : Blo 259821 1417571 := bstep (se 1 (by rfl) ⟨1063178, by rfl⟩ : syracuseStep 1417571 = 2126357) B2126357
theorem B3875381 : Blo 259821 3875381 := bstep (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) B363317
theorem B1516229 : Blo 259821 1516229 := bstep (se 4 (by rfl) ⟨142146, by rfl⟩ : syracuseStep 1516229 = 284293) B284293
theorem B1319651 : Blo 259821 1319651 := bstep (se 1 (by rfl) ⟨989738, by rfl⟩ : syracuseStep 1319651 = 1979477) B1979477
theorem B664433 : Blo 259821 664433 := bstep (se 2 (by rfl) ⟨249162, by rfl⟩ : syracuseStep 664433 = 498325) B498325
theorem B664483 : Blo 259821 664483 := bstep (se 1 (by rfl) ⟨498362, by rfl⟩ : syracuseStep 664483 = 996725) B996725
theorem B1483697 : Blo 259821 1483697 := bstep (se 2 (by rfl) ⟨556386, by rfl⟩ : syracuseStep 1483697 = 1112773) B1112773
theorem B664625 : Blo 259821 664625 := bstep (se 2 (by rfl) ⟨249234, by rfl⟩ : syracuseStep 664625 = 498469) B498469
theorem B370099 : Blo 259821 370099 := bstep (se 1 (by rfl) ⟨277574, by rfl⟩ : syracuseStep 370099 = 555149) B555149
theorem B1320461 : Blo 259821 1320461 := bstep (se 3 (by rfl) ⟨247586, by rfl⟩ : syracuseStep 1320461 = 495173) B495173
theorem B796337 : Blo 259821 796337 := bstep (se 2 (by rfl) ⟨298626, by rfl⟩ : syracuseStep 796337 = 597253) B597253
theorem B370435 : Blo 259821 370435 := bstep (se 1 (by rfl) ⟨277826, by rfl⟩ : syracuseStep 370435 = 555653) B555653
theorem B1255331 : Blo 259821 1255331 := bstep (se 1 (by rfl) ⟨941498, by rfl⟩ : syracuseStep 1255331 = 1882997) B1882997
theorem B993293 : Blo 259821 993293 := bstep (se 3 (by rfl) ⟨186242, by rfl⟩ : syracuseStep 993293 = 372485) B372485
theorem B665617 : Blo 259821 665617 := bstep (se 2 (by rfl) ⟨249606, by rfl⟩ : syracuseStep 665617 = 499213) B499213
theorem B1255601 : Blo 259821 1255601 := bstep (se 2 (by rfl) ⟨470850, by rfl⟩ : syracuseStep 1255601 = 941701) B941701
theorem B1976561 : Blo 259821 1976561 := bstep (se 2 (by rfl) ⟨741210, by rfl⟩ : syracuseStep 1976561 = 1482421) B1482421
theorem B1255715 : Blo 259821 1255715 := bstep (se 1 (by rfl) ⟨941786, by rfl⟩ : syracuseStep 1255715 = 1883573) B1883573
theorem B665891 : Blo 259821 665891 := bstep (se 1 (by rfl) ⟨499418, by rfl⟩ : syracuseStep 665891 = 998837) B998837
theorem B370993 : Blo 259821 370993 := bstep (se 2 (by rfl) ⟨139122, by rfl⟩ : syracuseStep 370993 = 278245) B278245
theorem B371027 : Blo 259821 371027 := bstep (se 1 (by rfl) ⟨278270, by rfl⟩ : syracuseStep 371027 = 556541) B556541
theorem B1485155 : Blo 259821 1485155 := bstep (se 1 (by rfl) ⟨1113866, by rfl⟩ : syracuseStep 1485155 = 2227733) B2227733
theorem B600419 : Blo 259821 600419 := bstep (se 1 (by rfl) ⟨450314, by rfl⟩ : syracuseStep 600419 = 900629) B900629
theorem B666083 : Blo 259821 666083 := bstep (se 1 (by rfl) ⟨499562, by rfl⟩ : syracuseStep 666083 = 999125) B999125
theorem B1125197 : Blo 259821 1125197 := bstep (se 3 (by rfl) ⟨210974, by rfl⟩ : syracuseStep 1125197 = 421949) B421949
theorem B371585 : Blo 259821 371585 := bstep (se 2 (by rfl) ⟨139344, by rfl⟩ : syracuseStep 371585 = 278689) B278689
theorem B371665 : Blo 259821 371665 := bstep (se 2 (by rfl) ⟨139374, by rfl⟩ : syracuseStep 371665 = 278749) B278749
theorem B1682693 : Blo 259821 1682693 := bstep (se 4 (by rfl) ⟨157752, by rfl⟩ : syracuseStep 1682693 = 315505) B315505
theorem B667025 : Blo 259821 667025 := bstep (se 2 (by rfl) ⟨250134, by rfl⟩ : syracuseStep 667025 = 500269) B500269
theorem B667075 : Blo 259821 667075 := bstep (se 1 (by rfl) ⟨500306, by rfl⟩ : syracuseStep 667075 = 1000613) B1000613
theorem B667217 : Blo 259821 667217 := bstep (se 2 (by rfl) ⟨250206, by rfl⟩ : syracuseStep 667217 = 500413) B500413
theorem B372451 : Blo 259821 372451 := bstep (se 1 (by rfl) ⟨279338, by rfl⟩ : syracuseStep 372451 = 558677) B558677
theorem B2240581 : Blo 259821 2240581 := bstep (se 4 (by rfl) ⟨210054, by rfl⟩ : syracuseStep 2240581 = 420109) B420109
theorem B372929 : Blo 259821 372929 := bstep (se 2 (by rfl) ⟨139848, by rfl⟩ : syracuseStep 372929 = 279697) B279697
theorem B1159373 : Blo 259821 1159373 := bstep (se 3 (by rfl) ⟨217382, by rfl⟩ : syracuseStep 1159373 = 434765) B434765
theorem B438547 : Blo 259821 438547 := bstep (se 1 (by rfl) ⟨328910, by rfl⟩ : syracuseStep 438547 = 657821) B657821
theorem B373043 : Blo 259821 373043 := bstep (se 1 (by rfl) ⟨279782, by rfl⟩ : syracuseStep 373043 = 559565) B559565
theorem B1323377 : Blo 259821 1323377 := bstep (se 2 (by rfl) ⟨496266, by rfl⟩ : syracuseStep 1323377 = 992533) B992533
theorem B373123 : Blo 259821 373123 := bstep (se 1 (by rfl) ⟨279842, by rfl⟩ : syracuseStep 373123 = 559685) B559685
theorem B14332301 : Blo 259821 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B438689 : Blo 259821 438689 := bstep (se 2 (by rfl) ⟨164508, by rfl⟩ : syracuseStep 438689 = 329017) B329017
theorem B438817 : Blo 259821 438817 := bstep (se 2 (by rfl) ⟨164556, by rfl⟩ : syracuseStep 438817 = 329113) B329113
theorem B438851 : Blo 259821 438851 := bstep (se 1 (by rfl) ⟨329138, by rfl⟩ : syracuseStep 438851 = 658277) B658277
theorem B1585763 : Blo 259821 1585763 := bstep (se 1 (by rfl) ⟨1189322, by rfl⟩ : syracuseStep 1585763 = 2378645) B2378645
theorem B438979 : Blo 259821 438979 := bstep (se 1 (by rfl) ⟨329234, by rfl⟩ : syracuseStep 438979 = 658469) B658469
theorem B439121 : Blo 259821 439121 := bstep (se 2 (by rfl) ⟨164670, by rfl⟩ : syracuseStep 439121 = 329341) B329341
theorem B996209 : Blo 259821 996209 := bstep (se 2 (by rfl) ⟨373578, by rfl⟩ : syracuseStep 996209 = 747157) B747157
theorem B897905 : Blo 259821 897905 := bstep (se 2 (by rfl) ⟨336714, by rfl⟩ : syracuseStep 897905 = 673429) B673429
theorem B373681 : Blo 259821 373681 := bstep (se 2 (by rfl) ⟨140130, by rfl⟩ : syracuseStep 373681 = 280261) B280261
theorem B439249 : Blo 259821 439249 := bstep (se 2 (by rfl) ⟨164718, by rfl⟩ : syracuseStep 439249 = 329437) B329437
theorem B439283 : Blo 259821 439283 := bstep (se 1 (by rfl) ⟨329462, by rfl⟩ : syracuseStep 439283 = 658925) B658925
theorem B439411 : Blo 259821 439411 := bstep (se 1 (by rfl) ⟨329558, by rfl⟩ : syracuseStep 439411 = 659117) B659117
theorem B439553 : Blo 259821 439553 := bstep (se 2 (by rfl) ⟨164832, by rfl⟩ : syracuseStep 439553 = 329665) B329665
theorem B472387 : Blo 259821 472387 := bstep (se 1 (by rfl) ⟨354290, by rfl⟩ : syracuseStep 472387 = 708581) B708581
theorem B5682545 : Blo 259821 5682545 := bstep (se 2 (by rfl) ⟨2130954, by rfl⟩ : syracuseStep 5682545 = 4261909) B4261909
theorem B439681 : Blo 259821 439681 := bstep (se 2 (by rfl) ⟨164880, by rfl⟩ : syracuseStep 439681 = 329761) B329761
theorem B439715 : Blo 259821 439715 := bstep (se 1 (by rfl) ⟨329786, by rfl⟩ : syracuseStep 439715 = 659573) B659573
theorem B439843 : Blo 259821 439843 := bstep (se 1 (by rfl) ⟨329882, by rfl⟩ : syracuseStep 439843 = 659765) B659765
theorem B472675 : Blo 259821 472675 := bstep (se 1 (by rfl) ⟨354506, by rfl⟩ : syracuseStep 472675 = 709013) B709013
theorem B374387 : Blo 259821 374387 := bstep (se 1 (by rfl) ⟨280790, by rfl⟩ : syracuseStep 374387 = 561581) B561581
theorem B439985 : Blo 259821 439985 := bstep (se 2 (by rfl) ⟨164994, by rfl⟩ : syracuseStep 439985 = 329989) B329989
theorem B1324835 : Blo 259821 1324835 := bstep (se 1 (by rfl) ⟨993626, by rfl⟩ : syracuseStep 1324835 = 1987253) B1987253
theorem B440113 : Blo 259821 440113 := bstep (se 2 (by rfl) ⟨165042, by rfl⟩ : syracuseStep 440113 = 330085) B330085
theorem B440147 : Blo 259821 440147 := bstep (se 1 (by rfl) ⟨330110, by rfl⟩ : syracuseStep 440147 = 660221) B660221
theorem B1259405 : Blo 259821 1259405 := bstep (se 3 (by rfl) ⟨236138, by rfl⟩ : syracuseStep 1259405 = 472277) B472277
theorem B833453 : Blo 259821 833453 := bstep (se 3 (by rfl) ⟨156272, by rfl⟩ : syracuseStep 833453 = 312545) B312545
theorem B440275 : Blo 259821 440275 := bstep (se 1 (by rfl) ⟨330206, by rfl⟩ : syracuseStep 440275 = 660413) B660413
theorem B833581 : Blo 259821 833581 := bstep (se 3 (by rfl) ⟨156296, by rfl⟩ : syracuseStep 833581 = 312593) B312593
theorem B440417 : Blo 259821 440417 := bstep (se 2 (by rfl) ⟨165156, by rfl⟩ : syracuseStep 440417 = 330313) B330313
theorem B440545 : Blo 259821 440545 := bstep (se 2 (by rfl) ⟨165204, by rfl⟩ : syracuseStep 440545 = 330409) B330409
theorem B375025 : Blo 259821 375025 := bstep (se 2 (by rfl) ⟨140634, by rfl⟩ : syracuseStep 375025 = 281269) B281269
theorem B440579 : Blo 259821 440579 := bstep (se 1 (by rfl) ⟨330434, by rfl⟩ : syracuseStep 440579 = 660869) B660869
theorem B997667 : Blo 259821 997667 := bstep (se 1 (by rfl) ⟨748250, by rfl⟩ : syracuseStep 997667 = 1496501) B1496501
theorem B375139 : Blo 259821 375139 := bstep (se 1 (by rfl) ⟨281354, by rfl⟩ : syracuseStep 375139 = 562709) B562709
theorem B1784177 : Blo 259821 1784177 := bstep (se 2 (by rfl) ⟨669066, by rfl⟩ : syracuseStep 1784177 = 1338133) B1338133
theorem B440707 : Blo 259821 440707 := bstep (se 1 (by rfl) ⟨330530, by rfl⟩ : syracuseStep 440707 = 661061) B661061
theorem B440849 : Blo 259821 440849 := bstep (se 2 (by rfl) ⟨165318, by rfl⟩ : syracuseStep 440849 = 330637) B330637
theorem B1325645 : Blo 259821 1325645 := bstep (se 3 (by rfl) ⟨248558, by rfl⟩ : syracuseStep 1325645 = 497117) B497117
theorem B3029645 : Blo 259821 3029645 := bstep (se 3 (by rfl) ⟨568058, by rfl⟩ : syracuseStep 3029645 = 1136117) B1136117
theorem B440977 : Blo 259821 440977 := bstep (se 2 (by rfl) ⟨165366, by rfl⟩ : syracuseStep 440977 = 330733) B330733
theorem B441011 : Blo 259821 441011 := bstep (se 1 (by rfl) ⟨330758, by rfl⟩ : syracuseStep 441011 = 661517) B661517
theorem B441139 : Blo 259821 441139 := bstep (se 1 (by rfl) ⟨330854, by rfl⟩ : syracuseStep 441139 = 661709) B661709
theorem B1063793 : Blo 259821 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B1784753 : Blo 259821 1784753 := bstep (se 2 (by rfl) ⟨669282, by rfl⟩ : syracuseStep 1784753 = 1338565) B1338565
theorem B441281 : Blo 259821 441281 := bstep (se 2 (by rfl) ⟨165480, by rfl⟩ : syracuseStep 441281 = 330961) B330961
theorem B441409 : Blo 259821 441409 := bstep (se 2 (by rfl) ⟨165528, by rfl⟩ : syracuseStep 441409 = 331057) B331057
theorem B441443 : Blo 259821 441443 := bstep (se 1 (by rfl) ⟨331082, by rfl⟩ : syracuseStep 441443 = 662165) B662165
theorem B277715 : Blo 259821 277715 := bstep (se 1 (by rfl) ⟨208286, by rfl⟩ : syracuseStep 277715 = 416573) B416573
theorem B1391843 : Blo 259821 1391843 := bstep (se 1 (by rfl) ⟨1043882, by rfl⟩ : syracuseStep 1391843 = 2087765) B2087765
theorem B441571 : Blo 259821 441571 := bstep (se 1 (by rfl) ⟨331178, by rfl⟩ : syracuseStep 441571 = 662357) B662357
theorem B998669 : Blo 259821 998669 := bstep (se 3 (by rfl) ⟨187250, by rfl⟩ : syracuseStep 998669 = 374501) B374501
theorem B441713 : Blo 259821 441713 := bstep (se 2 (by rfl) ⟨165642, by rfl⟩ : syracuseStep 441713 = 331285) B331285
theorem B441841 : Blo 259821 441841 := bstep (se 2 (by rfl) ⟨165690, by rfl⟩ : syracuseStep 441841 = 331381) B331381
theorem B441875 : Blo 259821 441875 := bstep (se 1 (by rfl) ⟨331406, by rfl⟩ : syracuseStep 441875 = 662813) B662813
theorem B442003 : Blo 259821 442003 := bstep (se 1 (by rfl) ⟨331502, by rfl⟩ : syracuseStep 442003 = 663005) B663005
theorem B442145 : Blo 259821 442145 := bstep (se 2 (by rfl) ⟨165804, by rfl⟩ : syracuseStep 442145 = 331609) B331609
theorem B835427 : Blo 259821 835427 := bstep (se 1 (by rfl) ⟨626570, by rfl⟩ : syracuseStep 835427 = 1253141) B1253141
theorem B442273 : Blo 259821 442273 := bstep (se 2 (by rfl) ⟨165852, by rfl⟩ : syracuseStep 442273 = 331705) B331705
theorem B507811 : Blo 259821 507811 := bstep (se 1 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 507811 = 761717) B761717
theorem B442307 : Blo 259821 442307 := bstep (se 1 (by rfl) ⟨331730, by rfl⟩ : syracuseStep 442307 = 663461) B663461
theorem B475075 : Blo 259821 475075 := bstep (se 1 (by rfl) ⟨356306, by rfl⟩ : syracuseStep 475075 = 712613) B712613
theorem B835555 : Blo 259821 835555 := bstep (se 1 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 835555 = 1253333) B1253333
theorem B442435 : Blo 259821 442435 := bstep (se 1 (by rfl) ⟨331826, by rfl⟩ : syracuseStep 442435 = 663653) B663653
theorem B606275 : Blo 259821 606275 := bstep (se 1 (by rfl) ⟨454706, by rfl⟩ : syracuseStep 606275 = 909413) B909413
theorem B901187 : Blo 259821 901187 := bstep (se 1 (by rfl) ⟨675890, by rfl⟩ : syracuseStep 901187 = 1351781) B1351781
theorem B606289 : Blo 259821 606289 := bstep (se 2 (by rfl) ⟨227358, by rfl⟩ : syracuseStep 606289 = 454717) B454717
theorem B835697 : Blo 259821 835697 := bstep (se 2 (by rfl) ⟨313386, by rfl⟩ : syracuseStep 835697 = 626773) B626773
theorem B606403 : Blo 259821 606403 := bstep (se 1 (by rfl) ⟨454802, by rfl⟩ : syracuseStep 606403 = 909605) B909605
theorem B442577 : Blo 259821 442577 := bstep (se 2 (by rfl) ⟨165966, by rfl⟩ : syracuseStep 442577 = 331933) B331933
theorem B835811 : Blo 259821 835811 := bstep (se 1 (by rfl) ⟨626858, by rfl⟩ : syracuseStep 835811 = 1253717) B1253717
theorem B442705 : Blo 259821 442705 := bstep (se 2 (by rfl) ⟨166014, by rfl⟩ : syracuseStep 442705 = 332029) B332029
theorem B442739 : Blo 259821 442739 := bstep (se 1 (by rfl) ⟨332054, by rfl⟩ : syracuseStep 442739 = 664109) B664109
theorem B14336453 : Blo 259821 14336453 := bstep (se 4 (by rfl) ⟨1344042, by rfl⟩ : syracuseStep 14336453 = 2688085) B2688085
theorem B442867 : Blo 259821 442867 := bstep (se 1 (by rfl) ⟨332150, by rfl⟩ : syracuseStep 442867 = 664301) B664301
theorem B1131043 : Blo 259821 1131043 := bstep (se 1 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 1131043 = 1696565) B1696565
theorem B443009 : Blo 259821 443009 := bstep (se 2 (by rfl) ⟨166128, by rfl⟩ : syracuseStep 443009 = 332257) B332257
theorem B279283 : Blo 259821 279283 := bstep (se 1 (by rfl) ⟨209462, by rfl⟩ : syracuseStep 279283 = 418925) B418925
theorem B443137 : Blo 259821 443137 := bstep (se 2 (by rfl) ⟨166176, by rfl⟩ : syracuseStep 443137 = 332353) B332353
theorem B443171 : Blo 259821 443171 := bstep (se 1 (by rfl) ⟨332378, by rfl⟩ : syracuseStep 443171 = 664757) B664757
theorem B901955 : Blo 259821 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B443299 : Blo 259821 443299 := bstep (se 1 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 443299 = 664949) B664949
theorem B672689 : Blo 259821 672689 := bstep (se 2 (by rfl) ⟨252258, by rfl⟩ : syracuseStep 672689 = 504517) B504517
theorem B443441 : Blo 259821 443441 := bstep (se 2 (by rfl) ⟨166290, by rfl⟩ : syracuseStep 443441 = 332581) B332581
theorem B377971 : Blo 259821 377971 := bstep (se 1 (by rfl) ⟨283478, by rfl⟩ : syracuseStep 377971 = 566957) B566957
theorem B443569 : Blo 259821 443569 := bstep (se 2 (by rfl) ⟨166338, by rfl⟩ : syracuseStep 443569 = 332677) B332677
theorem B279731 : Blo 259821 279731 := bstep (se 1 (by rfl) ⟨209798, by rfl⟩ : syracuseStep 279731 = 419597) B419597
theorem B443603 : Blo 259821 443603 := bstep (se 1 (by rfl) ⟨332702, by rfl⟩ : syracuseStep 443603 = 665405) B665405
theorem B1000781 : Blo 259821 1000781 := bstep (se 3 (by rfl) ⟨187646, by rfl⟩ : syracuseStep 1000781 = 375293) B375293
theorem B443731 : Blo 259821 443731 := bstep (se 1 (by rfl) ⟨332798, by rfl⟩ : syracuseStep 443731 = 665597) B665597
theorem B1328561 : Blo 259821 1328561 := bstep (se 2 (by rfl) ⟨498210, by rfl⟩ : syracuseStep 1328561 = 996421) B996421
theorem B443873 : Blo 259821 443873 := bstep (se 2 (by rfl) ⟨166452, by rfl⟩ : syracuseStep 443873 = 332905) B332905
theorem B2377187 : Blo 259821 2377187 := bstep (se 1 (by rfl) ⟨1782890, by rfl⟩ : syracuseStep 2377187 = 3565781) B3565781
theorem B444001 : Blo 259821 444001 := bstep (se 2 (by rfl) ⟨166500, by rfl⟩ : syracuseStep 444001 = 333001) B333001
theorem B444035 : Blo 259821 444035 := bstep (se 1 (by rfl) ⟨333026, by rfl⟩ : syracuseStep 444035 = 666053) B666053
theorem B706253 : Blo 259821 706253 := bstep (se 3 (by rfl) ⟨132422, by rfl⟩ : syracuseStep 706253 = 264845) B264845
theorem B444163 : Blo 259821 444163 := bstep (se 1 (by rfl) ⟨333122, by rfl⟩ : syracuseStep 444163 = 666245) B666245
theorem B4245301 : Blo 259821 4245301 := bstep (se 5 (by rfl) ⟨198998, by rfl⟩ : syracuseStep 4245301 = 397997) B397997
theorem B444305 : Blo 259821 444305 := bstep (se 2 (by rfl) ⟨166614, by rfl⟩ : syracuseStep 444305 = 333229) B333229
theorem B837553 : Blo 259821 837553 := bstep (se 2 (by rfl) ⟨314082, by rfl⟩ : syracuseStep 837553 = 628165) B628165
theorem B444433 : Blo 259821 444433 := bstep (se 2 (by rfl) ⟨166662, by rfl⟩ : syracuseStep 444433 = 333325) B333325
theorem B1001521 : Blo 259821 1001521 := bstep (se 2 (by rfl) ⟨375570, by rfl⟩ : syracuseStep 1001521 = 751141) B751141
theorem B444467 : Blo 259821 444467 := bstep (se 1 (by rfl) ⟨333350, by rfl⟩ : syracuseStep 444467 = 666701) B666701
theorem B1001585 : Blo 259821 1001585 := bstep (se 2 (by rfl) ⟨375594, by rfl⟩ : syracuseStep 1001585 = 751189) B751189
theorem B641201 : Blo 259821 641201 := bstep (se 2 (by rfl) ⟨240450, by rfl⟩ : syracuseStep 641201 = 480901) B480901
theorem B444595 : Blo 259821 444595 := bstep (se 1 (by rfl) ⟨333446, by rfl⟩ : syracuseStep 444595 = 666893) B666893
theorem B1624369 : Blo 259821 1624369 := bstep (se 2 (by rfl) ⟨609138, by rfl⟩ : syracuseStep 1624369 = 1218277) B1218277
theorem B444737 : Blo 259821 444737 := bstep (se 2 (by rfl) ⟨166776, by rfl⟩ : syracuseStep 444737 = 333553) B333553
theorem B444865 : Blo 259821 444865 := bstep (se 2 (by rfl) ⟨166824, by rfl⟩ : syracuseStep 444865 = 333649) B333649
theorem B444899 : Blo 259821 444899 := bstep (se 1 (by rfl) ⟨333674, by rfl⟩ : syracuseStep 444899 = 667349) B667349
theorem B281107 : Blo 259821 281107 := bstep (se 1 (by rfl) ⟨210830, by rfl⟩ : syracuseStep 281107 = 421661) B421661
theorem B445027 : Blo 259821 445027 := bstep (se 1 (by rfl) ⟨333770, by rfl⟩ : syracuseStep 445027 = 667541) B667541
theorem B1002125 : Blo 259821 1002125 := bstep (se 3 (by rfl) ⟨187898, by rfl⟩ : syracuseStep 1002125 = 375797) B375797
theorem B445169 : Blo 259821 445169 := bstep (se 2 (by rfl) ⟨166938, by rfl⟩ : syracuseStep 445169 = 333877) B333877
theorem B740141 : Blo 259821 740141 := bstep (se 3 (by rfl) ⟨138776, by rfl⟩ : syracuseStep 740141 = 277553) B277553
theorem B1330019 : Blo 259821 1330019 := bstep (se 1 (by rfl) ⟨997514, by rfl⟩ : syracuseStep 1330019 = 1995029) B1995029
theorem B314275 : Blo 259821 314275 := bstep (se 1 (by rfl) ⟨235706, by rfl⟩ : syracuseStep 314275 = 471413) B471413
theorem B2837429 : Blo 259821 2837429 := bstep (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) B266009
theorem B281539 : Blo 259821 281539 := bstep (se 1 (by rfl) ⟨211154, by rfl⟩ : syracuseStep 281539 = 422309) B422309
theorem B314371 : Blo 259821 314371 := bstep (se 1 (by rfl) ⟨235778, by rfl⟩ : syracuseStep 314371 = 471557) B471557
theorem B838669 : Blo 259821 838669 := bstep (se 3 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 838669 = 314501) B314501
theorem B2018317 : Blo 259821 2018317 := bstep (se 3 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 2018317 = 756869) B756869
theorem B1494085 : Blo 259821 1494085 := bstep (se 4 (by rfl) ⟨140070, by rfl⟩ : syracuseStep 1494085 = 280141) B280141
theorem B445969 : Blo 259821 445969 := bstep (se 2 (by rfl) ⟨167238, by rfl⟩ : syracuseStep 445969 = 334477) B334477
theorem B1330829 : Blo 259821 1330829 := bstep (se 3 (by rfl) ⟨249530, by rfl⟩ : syracuseStep 1330829 = 499061) B499061
theorem B3460805 : Blo 259821 3460805 := bstep (se 4 (by rfl) ⟨324450, by rfl⟩ : syracuseStep 3460805 = 648901) B648901
theorem B282371 : Blo 259821 282371 := bstep (se 1 (by rfl) ⟨211778, by rfl⟩ : syracuseStep 282371 = 423557) B423557
theorem B839501 : Blo 259821 839501 := bstep (se 3 (by rfl) ⟨157406, by rfl⟩ : syracuseStep 839501 = 314813) B314813
theorem B708547 : Blo 259821 708547 := bstep (se 1 (by rfl) ⟨531410, by rfl⟩ : syracuseStep 708547 = 1062821) B1062821
theorem B741325 : Blo 259821 741325 := bstep (se 3 (by rfl) ⟨138998, by rfl⟩ : syracuseStep 741325 = 277997) B277997
theorem B446627 : Blo 259821 446627 := bstep (se 1 (by rfl) ⟨334970, by rfl⟩ : syracuseStep 446627 = 669941) B669941
theorem B2117987 : Blo 259821 2117987 := bstep (se 1 (by rfl) ⟨1588490, by rfl⟩ : syracuseStep 2117987 = 3176981) B3176981
theorem B2249329 : Blo 259821 2249329 := bstep (se 2 (by rfl) ⟨843498, by rfl⟩ : syracuseStep 2249329 = 1686997) B1686997
theorem B447139 : Blo 259821 447139 := bstep (se 1 (by rfl) ⟨335354, by rfl⟩ : syracuseStep 447139 = 670709) B670709
theorem B3331043 : Blo 259821 3331043 := bstep (se 1 (by rfl) ⟨2498282, by rfl⟩ : syracuseStep 3331043 = 4996565) B4996565
theorem B742385 : Blo 259821 742385 := bstep (se 2 (by rfl) ⟨278394, by rfl⟩ : syracuseStep 742385 = 556789) B556789
theorem B1496069 : Blo 259821 1496069 := bstep (se 4 (by rfl) ⟨140256, by rfl⟩ : syracuseStep 1496069 = 280513) B280513
theorem B7492661 : Blo 259821 7492661 := bstep (se 5 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 7492661 = 702437) B702437
theorem B743057 : Blo 259821 743057 := bstep (se 2 (by rfl) ⟨278646, by rfl⟩ : syracuseStep 743057 = 557293) B557293
theorem B2119409 : Blo 259821 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B2119537 : Blo 259821 2119537 := bstep (se 2 (by rfl) ⟨794826, by rfl⟩ : syracuseStep 2119537 = 1589653) B1589653
theorem B841603 : Blo 259821 841603 := bstep (se 1 (by rfl) ⟨631202, by rfl⟩ : syracuseStep 841603 = 1262405) B1262405
theorem B841745 : Blo 259821 841745 := bstep (se 2 (by rfl) ⟨315654, by rfl⟩ : syracuseStep 841745 = 631309) B631309
theorem B481411 : Blo 259821 481411 := bstep (se 1 (by rfl) ⟨361058, by rfl⟩ : syracuseStep 481411 = 722117) B722117
theorem B711011 : Blo 259821 711011 := bstep (se 1 (by rfl) ⟨533258, by rfl⟩ : syracuseStep 711011 = 1066517) B1066517
theorem B743843 : Blo 259821 743843 := bstep (se 1 (by rfl) ⟨557882, by rfl⟩ : syracuseStep 743843 = 1115765) B1115765
theorem B1333745 : Blo 259821 1333745 := bstep (se 2 (by rfl) ⟨500154, by rfl⟩ : syracuseStep 1333745 = 1000309) B1000309
theorem B5626421 : Blo 259821 5626421 := bstep (se 5 (by rfl) ⟨263738, by rfl⟩ : syracuseStep 5626421 = 527477) B527477
theorem B744173 : Blo 259821 744173 := bstep (se 3 (by rfl) ⟨139532, by rfl⟩ : syracuseStep 744173 = 279065) B279065
theorem B744241 : Blo 259821 744241 := bstep (se 2 (by rfl) ⟨279090, by rfl⟩ : syracuseStep 744241 = 558181) B558181
theorem B1596323 : Blo 259821 1596323 := bstep (se 1 (by rfl) ⟨1197242, by rfl⟩ : syracuseStep 1596323 = 2394485) B2394485
theorem B416675 : Blo 259821 416675 := bstep (se 1 (by rfl) ⟨312506, by rfl⟩ : syracuseStep 416675 = 625013) B625013
theorem B744515 : Blo 259821 744515 := bstep (se 1 (by rfl) ⟨558386, by rfl⟩ : syracuseStep 744515 = 1116773) B1116773
theorem B515153 : Blo 259821 515153 := bstep (se 2 (by rfl) ⟨193182, by rfl⟩ : syracuseStep 515153 = 386365) B386365
theorem B711985 : Blo 259821 711985 := bstep (se 2 (by rfl) ⟨266994, by rfl⟩ : syracuseStep 711985 = 533989) B533989
theorem B646787 : Blo 259821 646787 := bstep (se 1 (by rfl) ⟨485090, by rfl⟩ : syracuseStep 646787 = 970181) B970181
theorem B1564337 : Blo 259821 1564337 := bstep (se 2 (by rfl) ⟨586626, by rfl⟩ : syracuseStep 1564337 = 1173253) B1173253
theorem B417521 : Blo 259821 417521 := bstep (se 2 (by rfl) ⟨156570, by rfl⟩ : syracuseStep 417521 = 313141) B313141
theorem B745357 : Blo 259821 745357 := bstep (se 3 (by rfl) ⟨139754, by rfl⟩ : syracuseStep 745357 = 279509) B279509
theorem B1335203 : Blo 259821 1335203 := bstep (se 1 (by rfl) ⟨1001402, by rfl⟩ : syracuseStep 1335203 = 2002805) B2002805
theorem B10117061 : Blo 259821 10117061 := bstep (se 4 (by rfl) ⟨948474, by rfl⟩ : syracuseStep 10117061 = 1896949) B1896949
theorem B745517 : Blo 259821 745517 := bstep (se 3 (by rfl) ⟨139784, by rfl⟩ : syracuseStep 745517 = 279569) B279569
theorem B745699 : Blo 259821 745699 := bstep (se 1 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 745699 = 1118549) B1118549
theorem B844141 : Blo 259821 844141 := bstep (se 3 (by rfl) ⟨158276, by rfl⟩ : syracuseStep 844141 = 316553) B316553
theorem B418259 : Blo 259821 418259 := bstep (se 1 (by rfl) ⟨313694, by rfl⟩ : syracuseStep 418259 = 627389) B627389
theorem B2187917 : Blo 259821 2187917 := bstep (se 3 (by rfl) ⟨410234, by rfl⟩ : syracuseStep 2187917 = 820469) B820469
theorem B877229 : Blo 259821 877229 := bstep (se 3 (by rfl) ⟨164480, by rfl⟩ : syracuseStep 877229 = 328961) B328961
theorem B877283 : Blo 259821 877283 := bstep (se 1 (by rfl) ⟨657962, by rfl⟩ : syracuseStep 877283 = 1315925) B1315925
theorem B1499917 : Blo 259821 1499917 := bstep (se 3 (by rfl) ⟨281234, by rfl⟩ : syracuseStep 1499917 = 562469) B562469
theorem B3761093 : Blo 259821 3761093 := bstep (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) B705205
theorem B1598413 : Blo 259821 1598413 := bstep (se 3 (by rfl) ⟨299702, by rfl⟩ : syracuseStep 1598413 = 599405) B599405
theorem B877553 : Blo 259821 877553 := bstep (se 2 (by rfl) ⟨329082, by rfl⟩ : syracuseStep 877553 = 658165) B658165
theorem B419251 : Blo 259821 419251 := bstep (se 1 (by rfl) ⟨314438, by rfl⟩ : syracuseStep 419251 = 628877) B628877
theorem B878093 : Blo 259821 878093 := bstep (se 3 (by rfl) ⟨164642, by rfl⟩ : syracuseStep 878093 = 329285) B329285
theorem B878147 : Blo 259821 878147 := bstep (se 1 (by rfl) ⟨658610, by rfl⟩ : syracuseStep 878147 = 1317221) B1317221
theorem B747089 : Blo 259821 747089 := bstep (se 2 (by rfl) ⟨280158, by rfl⟩ : syracuseStep 747089 = 560317) B560317
theorem B419489 : Blo 259821 419489 := bstep (se 2 (by rfl) ⟨157308, by rfl⟩ : syracuseStep 419489 = 314617) B314617
theorem B878417 : Blo 259821 878417 := bstep (se 2 (by rfl) ⟨329406, by rfl⟩ : syracuseStep 878417 = 658813) B658813
theorem B419699 : Blo 259821 419699 := bstep (se 1 (by rfl) ⟨314774, by rfl⟩ : syracuseStep 419699 = 629549) B629549
theorem B649315 : Blo 259821 649315 := bstep (se 1 (by rfl) ⟨486986, by rfl⟩ : syracuseStep 649315 = 973973) B973973
theorem B3369073 : Blo 259821 3369073 := bstep (se 2 (by rfl) ⟨1263402, by rfl⟩ : syracuseStep 3369073 = 2526805) B2526805
theorem B878957 : Blo 259821 878957 := bstep (se 3 (by rfl) ⟨164804, by rfl⟩ : syracuseStep 878957 = 329609) B329609
theorem B879011 : Blo 259821 879011 := bstep (se 1 (by rfl) ⟨659258, by rfl⟩ : syracuseStep 879011 = 1318517) B1318517
theorem B7301573 : Blo 259821 7301573 := bstep (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) B1369045
theorem B748045 : Blo 259821 748045 := bstep (se 3 (by rfl) ⟨140258, by rfl⟩ : syracuseStep 748045 = 280517) B280517
theorem B420481 : Blo 259821 420481 := bstep (se 2 (by rfl) ⟨157680, by rfl⟩ : syracuseStep 420481 = 315361) B315361
theorem B1600163 : Blo 259821 1600163 := bstep (se 1 (by rfl) ⟨1200122, by rfl⟩ : syracuseStep 1600163 = 2400245) B2400245
theorem B879281 : Blo 259821 879281 := bstep (se 2 (by rfl) ⟨329730, by rfl⟩ : syracuseStep 879281 = 659461) B659461
theorem B1501901 : Blo 259821 1501901 := bstep (se 3 (by rfl) ⟨281606, by rfl⟩ : syracuseStep 1501901 = 563213) B563213
theorem B748273 : Blo 259821 748273 := bstep (se 2 (by rfl) ⟨280602, by rfl⟩ : syracuseStep 748273 = 561205) B561205
theorem B1993571 : Blo 259821 1993571 := bstep (se 1 (by rfl) ⟨1495178, by rfl⟩ : syracuseStep 1993571 = 2990357) B2990357
theorem B1895309 : Blo 259821 1895309 := bstep (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) B710741
theorem B748433 : Blo 259821 748433 := bstep (se 2 (by rfl) ⟨280662, by rfl⟩ : syracuseStep 748433 = 561325) B561325
theorem B584657 : Blo 259821 584657 := bstep (se 2 (by rfl) ⟨219246, by rfl⟩ : syracuseStep 584657 = 438493) B438493
theorem B584675 : Blo 259821 584675 := bstep (se 1 (by rfl) ⟨438506, by rfl⟩ : syracuseStep 584675 = 877013) B877013
theorem B748547 : Blo 259821 748547 := bstep (se 1 (by rfl) ⟨561410, by rfl⟩ : syracuseStep 748547 = 1122821) B1122821
theorem B879821 : Blo 259821 879821 := bstep (se 3 (by rfl) ⟨164966, by rfl⟩ : syracuseStep 879821 = 329933) B329933
theorem B584945 : Blo 259821 584945 := bstep (se 2 (by rfl) ⟨219354, by rfl⟩ : syracuseStep 584945 = 438709) B438709
theorem B584963 : Blo 259821 584963 := bstep (se 1 (by rfl) ⟨438722, by rfl⟩ : syracuseStep 584963 = 877445) B877445
theorem B879875 : Blo 259821 879875 := bstep (se 1 (by rfl) ⟨659906, by rfl⟩ : syracuseStep 879875 = 1319813) B1319813
theorem B421283 : Blo 259821 421283 := bstep (se 1 (by rfl) ⟨315962, by rfl⟩ : syracuseStep 421283 = 631925) B631925
theorem B585233 : Blo 259821 585233 := bstep (se 2 (by rfl) ⟨219462, by rfl⟩ : syracuseStep 585233 = 438925) B438925
theorem B880145 : Blo 259821 880145 := bstep (se 2 (by rfl) ⟨330054, by rfl⟩ : syracuseStep 880145 = 660109) B660109
theorem B585251 : Blo 259821 585251 := bstep (se 1 (by rfl) ⟨438938, by rfl⟩ : syracuseStep 585251 = 877877) B877877
theorem B585521 : Blo 259821 585521 := bstep (se 2 (by rfl) ⟨219570, by rfl⟩ : syracuseStep 585521 = 439141) B439141
theorem B585539 : Blo 259821 585539 := bstep (se 1 (by rfl) ⟨439154, by rfl⟩ : syracuseStep 585539 = 878309) B878309
theorem B421795 : Blo 259821 421795 := bstep (se 1 (by rfl) ⟨316346, by rfl⟩ : syracuseStep 421795 = 632693) B632693
theorem B749549 : Blo 259821 749549 := bstep (se 3 (by rfl) ⟨140540, by rfl⟩ : syracuseStep 749549 = 281081) B281081
theorem B356339 : Blo 259821 356339 := bstep (se 1 (by rfl) ⟨267254, by rfl⟩ : syracuseStep 356339 = 534509) B534509
theorem B880685 : Blo 259821 880685 := bstep (se 3 (by rfl) ⟨165128, by rfl⟩ : syracuseStep 880685 = 330257) B330257
theorem B585809 : Blo 259821 585809 := bstep (se 2 (by rfl) ⟨219678, by rfl⟩ : syracuseStep 585809 = 439357) B439357
theorem B585827 : Blo 259821 585827 := bstep (se 1 (by rfl) ⟨439370, by rfl⟩ : syracuseStep 585827 = 878741) B878741
theorem B880739 : Blo 259821 880739 := bstep (se 1 (by rfl) ⟨660554, by rfl⟩ : syracuseStep 880739 = 1321109) B1321109
theorem B1667213 : Blo 259821 1667213 := bstep (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) B625205
theorem B749731 : Blo 259821 749731 := bstep (se 1 (by rfl) ⟨562298, by rfl⟩ : syracuseStep 749731 = 1124597) B1124597
theorem B749891 : Blo 259821 749891 := bstep (se 1 (by rfl) ⟨562418, by rfl⟩ : syracuseStep 749891 = 1124837) B1124837
theorem B586097 : Blo 259821 586097 := bstep (se 2 (by rfl) ⟨219786, by rfl⟩ : syracuseStep 586097 = 439573) B439573
theorem B881009 : Blo 259821 881009 := bstep (se 2 (by rfl) ⟨330378, by rfl⟩ : syracuseStep 881009 = 660757) B660757
theorem B586115 : Blo 259821 586115 := bstep (se 1 (by rfl) ⟨439586, by rfl⟩ : syracuseStep 586115 = 879173) B879173
theorem B1110449 : Blo 259821 1110449 := bstep (se 2 (by rfl) ⟨416418, by rfl⟩ : syracuseStep 1110449 = 832837) B832837
theorem B422339 : Blo 259821 422339 := bstep (se 1 (by rfl) ⟨316754, by rfl⟩ : syracuseStep 422339 = 633509) B633509
theorem B422513 : Blo 259821 422513 := bstep (se 2 (by rfl) ⟨158442, by rfl⟩ : syracuseStep 422513 = 316885) B316885
theorem B389747 : Blo 259821 389747 := bstep (se 1 (by rfl) ⟨292310, by rfl⟩ : syracuseStep 389747 = 584621) B584621
theorem B389777 : Blo 259821 389777 := bstep (se 2 (by rfl) ⟨146166, by rfl⟩ : syracuseStep 389777 = 292333) B292333
theorem B586385 : Blo 259821 586385 := bstep (se 2 (by rfl) ⟨219894, by rfl⟩ : syracuseStep 586385 = 439789) B439789
theorem B389795 : Blo 259821 389795 := bstep (se 1 (by rfl) ⟨292346, by rfl⟩ : syracuseStep 389795 = 584693) B584693
theorem B586403 : Blo 259821 586403 := bstep (se 1 (by rfl) ⟨439802, by rfl⟩ : syracuseStep 586403 = 879605) B879605
theorem B389825 : Blo 259821 389825 := bstep (se 2 (by rfl) ⟨146184, by rfl⟩ : syracuseStep 389825 = 292369) B292369
theorem B389843 : Blo 259821 389843 := bstep (se 1 (by rfl) ⟨292382, by rfl⟩ : syracuseStep 389843 = 584765) B584765
theorem B389873 : Blo 259821 389873 := bstep (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) B292405
theorem B389891 : Blo 259821 389891 := bstep (se 1 (by rfl) ⟨292418, by rfl⟩ : syracuseStep 389891 = 584837) B584837
theorem B389921 : Blo 259821 389921 := bstep (se 2 (by rfl) ⟨146220, by rfl⟩ : syracuseStep 389921 = 292441) B292441
theorem B389939 : Blo 259821 389939 := bstep (se 1 (by rfl) ⟨292454, by rfl⟩ : syracuseStep 389939 = 584909) B584909
theorem B389969 : Blo 259821 389969 := bstep (se 2 (by rfl) ⟨146238, by rfl⟩ : syracuseStep 389969 = 292477) B292477
theorem B389987 : Blo 259821 389987 := bstep (se 1 (by rfl) ⟨292490, by rfl⟩ : syracuseStep 389987 = 584981) B584981
theorem B390017 : Blo 259821 390017 := bstep (se 2 (by rfl) ⟨146256, by rfl⟩ : syracuseStep 390017 = 292513) B292513
theorem B881549 : Blo 259821 881549 := bstep (se 3 (by rfl) ⟨165290, by rfl⟩ : syracuseStep 881549 = 330581) B330581
theorem B390035 : Blo 259821 390035 := bstep (se 1 (by rfl) ⟨292526, by rfl⟩ : syracuseStep 390035 = 585053) B585053
theorem B390065 : Blo 259821 390065 := bstep (se 2 (by rfl) ⟨146274, by rfl⟩ : syracuseStep 390065 = 292549) B292549
theorem B586673 : Blo 259821 586673 := bstep (se 2 (by rfl) ⟨220002, by rfl⟩ : syracuseStep 586673 = 440005) B440005
theorem B390083 : Blo 259821 390083 := bstep (se 1 (by rfl) ⟨292562, by rfl⟩ : syracuseStep 390083 = 585125) B585125
theorem B586691 : Blo 259821 586691 := bstep (se 1 (by rfl) ⟨440018, by rfl⟩ : syracuseStep 586691 = 880037) B880037
theorem B881603 : Blo 259821 881603 := bstep (se 1 (by rfl) ⟨661202, by rfl⟩ : syracuseStep 881603 = 1322405) B1322405
theorem B390113 : Blo 259821 390113 := bstep (se 2 (by rfl) ⟨146292, by rfl⟩ : syracuseStep 390113 = 292585) B292585
theorem B390131 : Blo 259821 390131 := bstep (se 1 (by rfl) ⟨292598, by rfl⟩ : syracuseStep 390131 = 585197) B585197
theorem B390161 : Blo 259821 390161 := bstep (se 2 (by rfl) ⟨146310, by rfl⟩ : syracuseStep 390161 = 292621) B292621
theorem B390179 : Blo 259821 390179 := bstep (se 1 (by rfl) ⟨292634, by rfl⟩ : syracuseStep 390179 = 585269) B585269
theorem B390209 : Blo 259821 390209 := bstep (se 2 (by rfl) ⟨146328, by rfl⟩ : syracuseStep 390209 = 292657) B292657
theorem B1111117 : Blo 259821 1111117 := bstep (se 3 (by rfl) ⟨208334, by rfl⟩ : syracuseStep 1111117 = 416669) B416669
theorem B390227 : Blo 259821 390227 := bstep (se 1 (by rfl) ⟨292670, by rfl⟩ : syracuseStep 390227 = 585341) B585341
theorem B390257 : Blo 259821 390257 := bstep (se 2 (by rfl) ⟨146346, by rfl⟩ : syracuseStep 390257 = 292693) B292693
theorem B390275 : Blo 259821 390275 := bstep (se 1 (by rfl) ⟨292706, by rfl⟩ : syracuseStep 390275 = 585413) B585413
theorem B390305 : Blo 259821 390305 := bstep (se 2 (by rfl) ⟨146364, by rfl⟩ : syracuseStep 390305 = 292729) B292729
theorem B390323 : Blo 259821 390323 := bstep (se 1 (by rfl) ⟨292742, by rfl⟩ : syracuseStep 390323 = 585485) B585485
theorem B390353 : Blo 259821 390353 := bstep (se 2 (by rfl) ⟨146382, by rfl⟩ : syracuseStep 390353 = 292765) B292765
theorem B586961 : Blo 259821 586961 := bstep (se 2 (by rfl) ⟨220110, by rfl⟩ : syracuseStep 586961 = 440221) B440221
theorem B881873 : Blo 259821 881873 := bstep (se 2 (by rfl) ⟨330702, by rfl⟩ : syracuseStep 881873 = 661405) B661405
theorem B390371 : Blo 259821 390371 := bstep (se 1 (by rfl) ⟨292778, by rfl⟩ : syracuseStep 390371 = 585557) B585557
theorem B586979 : Blo 259821 586979 := bstep (se 1 (by rfl) ⟨440234, by rfl⟩ : syracuseStep 586979 = 880469) B880469
theorem B390401 : Blo 259821 390401 := bstep (se 2 (by rfl) ⟨146400, by rfl⟩ : syracuseStep 390401 = 292801) B292801
theorem B390419 : Blo 259821 390419 := bstep (se 1 (by rfl) ⟨292814, by rfl⟩ : syracuseStep 390419 = 585629) B585629
theorem B390449 : Blo 259821 390449 := bstep (se 2 (by rfl) ⟨146418, by rfl⟩ : syracuseStep 390449 = 292837) B292837
theorem B390467 : Blo 259821 390467 := bstep (se 1 (by rfl) ⟨292850, by rfl⟩ : syracuseStep 390467 = 585701) B585701
theorem B390497 : Blo 259821 390497 := bstep (se 2 (by rfl) ⟨146436, by rfl⟩ : syracuseStep 390497 = 292873) B292873
theorem B750961 : Blo 259821 750961 := bstep (se 2 (by rfl) ⟨281610, by rfl⟩ : syracuseStep 750961 = 563221) B563221
theorem B390515 : Blo 259821 390515 := bstep (se 1 (by rfl) ⟨292886, by rfl⟩ : syracuseStep 390515 = 585773) B585773
theorem B390545 : Blo 259821 390545 := bstep (se 2 (by rfl) ⟨146454, by rfl⟩ : syracuseStep 390545 = 292909) B292909
theorem B390563 : Blo 259821 390563 := bstep (se 1 (by rfl) ⟨292922, by rfl⟩ : syracuseStep 390563 = 585845) B585845
theorem B390593 : Blo 259821 390593 := bstep (se 2 (by rfl) ⟨146472, by rfl⟩ : syracuseStep 390593 = 292945) B292945
theorem B390611 : Blo 259821 390611 := bstep (se 1 (by rfl) ⟨292958, by rfl⟩ : syracuseStep 390611 = 585917) B585917
theorem B390641 : Blo 259821 390641 := bstep (se 2 (by rfl) ⟨146490, by rfl⟩ : syracuseStep 390641 = 292981) B292981
theorem B587249 : Blo 259821 587249 := bstep (se 2 (by rfl) ⟨220218, by rfl⟩ : syracuseStep 587249 = 440437) B440437
theorem B390659 : Blo 259821 390659 := bstep (se 1 (by rfl) ⟨292994, by rfl⟩ : syracuseStep 390659 = 585989) B585989
theorem B587267 : Blo 259821 587267 := bstep (se 1 (by rfl) ⟨440450, by rfl⟩ : syracuseStep 587267 = 880901) B880901
theorem B390689 : Blo 259821 390689 := bstep (se 2 (by rfl) ⟨146508, by rfl⟩ : syracuseStep 390689 = 293017) B293017
theorem B292387 : Blo 259821 292387 := bstep (se 1 (by rfl) ⟨219290, by rfl⟩ : syracuseStep 292387 = 438581) B438581
theorem B390707 : Blo 259821 390707 := bstep (se 1 (by rfl) ⟨293030, by rfl⟩ : syracuseStep 390707 = 586061) B586061
theorem B390737 : Blo 259821 390737 := bstep (se 2 (by rfl) ⟨146526, by rfl⟩ : syracuseStep 390737 = 293053) B293053
theorem B390755 : Blo 259821 390755 := bstep (se 1 (by rfl) ⟨293066, by rfl⟩ : syracuseStep 390755 = 586133) B586133
theorem B390785 : Blo 259821 390785 := bstep (se 2 (by rfl) ⟨146544, by rfl⟩ : syracuseStep 390785 = 293089) B293089
theorem B390803 : Blo 259821 390803 := bstep (se 1 (by rfl) ⟨293102, by rfl⟩ : syracuseStep 390803 = 586205) B586205
theorem B1111715 : Blo 259821 1111715 := bstep (se 1 (by rfl) ⟨833786, by rfl⟩ : syracuseStep 1111715 = 1667573) B1667573
theorem B390833 : Blo 259821 390833 := bstep (se 2 (by rfl) ⟨146562, by rfl⟩ : syracuseStep 390833 = 293125) B293125
theorem B816817 : Blo 259821 816817 := bstep (se 2 (by rfl) ⟨306306, by rfl⟩ : syracuseStep 816817 = 612613) B612613
theorem B292531 : Blo 259821 292531 := bstep (se 1 (by rfl) ⟨219398, by rfl⟩ : syracuseStep 292531 = 438797) B438797
theorem B390851 : Blo 259821 390851 := bstep (se 1 (by rfl) ⟨293138, by rfl⟩ : syracuseStep 390851 = 586277) B586277
theorem B390881 : Blo 259821 390881 := bstep (se 2 (by rfl) ⟨146580, by rfl⟩ : syracuseStep 390881 = 293161) B293161
theorem B882413 : Blo 259821 882413 := bstep (se 3 (by rfl) ⟨165452, by rfl⟩ : syracuseStep 882413 = 330905) B330905
theorem B259827 : Blo 259821 259827 := bstep (se 1 (by rfl) ⟨194870, by rfl⟩ : syracuseStep 259827 = 389741) B389741
theorem B390899 : Blo 259821 390899 := bstep (se 1 (by rfl) ⟨293174, by rfl⟩ : syracuseStep 390899 = 586349) B586349
theorem B259843 : Blo 259821 259843 := bstep (se 1 (by rfl) ⟨194882, by rfl⟩ : syracuseStep 259843 = 389765) B389765
theorem B390929 : Blo 259821 390929 := bstep (se 2 (by rfl) ⟨146598, by rfl⟩ : syracuseStep 390929 = 293197) B293197
theorem B587537 : Blo 259821 587537 := bstep (se 2 (by rfl) ⟨220326, by rfl⟩ : syracuseStep 587537 = 440653) B440653
theorem B259859 : Blo 259821 259859 := bstep (se 1 (by rfl) ⟨194894, by rfl⟩ : syracuseStep 259859 = 389789) B389789
theorem B259875 : Blo 259821 259875 := bstep (se 1 (by rfl) ⟨194906, by rfl⟩ : syracuseStep 259875 = 389813) B389813
theorem B390947 : Blo 259821 390947 := bstep (se 1 (by rfl) ⟨293210, by rfl⟩ : syracuseStep 390947 = 586421) B586421
theorem B587555 : Blo 259821 587555 := bstep (se 1 (by rfl) ⟨440666, by rfl⟩ : syracuseStep 587555 = 881333) B881333
theorem B882467 : Blo 259821 882467 := bstep (se 1 (by rfl) ⟨661850, by rfl⟩ : syracuseStep 882467 = 1323701) B1323701
theorem B849709 : Blo 259821 849709 := bstep (se 3 (by rfl) ⟨159320, by rfl⟩ : syracuseStep 849709 = 318641) B318641
theorem B259891 : Blo 259821 259891 := bstep (se 1 (by rfl) ⟨194918, by rfl⟩ : syracuseStep 259891 = 389837) B389837
theorem B390977 : Blo 259821 390977 := bstep (se 2 (by rfl) ⟨146616, by rfl⟩ : syracuseStep 390977 = 293233) B293233
theorem B259907 : Blo 259821 259907 := bstep (se 1 (by rfl) ⟨194930, by rfl⟩ : syracuseStep 259907 = 389861) B389861
theorem B292675 : Blo 259821 292675 := bstep (se 1 (by rfl) ⟨219506, by rfl⟩ : syracuseStep 292675 = 439013) B439013
theorem B259923 : Blo 259821 259923 := bstep (se 1 (by rfl) ⟨194942, by rfl⟩ : syracuseStep 259923 = 389885) B389885
theorem B390995 : Blo 259821 390995 := bstep (se 1 (by rfl) ⟨293246, by rfl⟩ : syracuseStep 390995 = 586493) B586493
theorem B259939 : Blo 259821 259939 := bstep (se 1 (by rfl) ⟨194954, by rfl⟩ : syracuseStep 259939 = 389909) B389909
theorem B391025 : Blo 259821 391025 := bstep (se 2 (by rfl) ⟨146634, by rfl⟩ : syracuseStep 391025 = 293269) B293269
theorem B259955 : Blo 259821 259955 := bstep (se 1 (by rfl) ⟨194966, by rfl⟩ : syracuseStep 259955 = 389933) B389933
theorem B259971 : Blo 259821 259971 := bstep (se 1 (by rfl) ⟨194978, by rfl⟩ : syracuseStep 259971 = 389957) B389957
theorem B391043 : Blo 259821 391043 := bstep (se 1 (by rfl) ⟨293282, by rfl⟩ : syracuseStep 391043 = 586565) B586565
theorem B259987 : Blo 259821 259987 := bstep (se 1 (by rfl) ⟨194990, by rfl⟩ : syracuseStep 259987 = 389981) B389981
theorem B391073 : Blo 259821 391073 := bstep (se 2 (by rfl) ⟨146652, by rfl⟩ : syracuseStep 391073 = 293305) B293305
theorem B948131 : Blo 259821 948131 := bstep (se 1 (by rfl) ⟨711098, by rfl⟩ : syracuseStep 948131 = 1422197) B1422197
theorem B260003 : Blo 259821 260003 := bstep (se 1 (by rfl) ⟨195002, by rfl⟩ : syracuseStep 260003 = 390005) B390005
theorem B260019 : Blo 259821 260019 := bstep (se 1 (by rfl) ⟨195014, by rfl⟩ : syracuseStep 260019 = 390029) B390029
theorem B391091 : Blo 259821 391091 := bstep (se 1 (by rfl) ⟨293318, by rfl⟩ : syracuseStep 391091 = 586637) B586637
theorem B260035 : Blo 259821 260035 := bstep (se 1 (by rfl) ⟨195026, by rfl⟩ : syracuseStep 260035 = 390053) B390053
theorem B391121 : Blo 259821 391121 := bstep (se 2 (by rfl) ⟨146670, by rfl⟩ : syracuseStep 391121 = 293341) B293341
theorem B260051 : Blo 259821 260051 := bstep (se 1 (by rfl) ⟨195038, by rfl⟩ : syracuseStep 260051 = 390077) B390077
theorem B292819 : Blo 259821 292819 := bstep (se 1 (by rfl) ⟨219614, by rfl⟩ : syracuseStep 292819 = 439229) B439229
theorem B260067 : Blo 259821 260067 := bstep (se 1 (by rfl) ⟨195050, by rfl⟩ : syracuseStep 260067 = 390101) B390101
theorem B391139 : Blo 259821 391139 := bstep (se 1 (by rfl) ⟨293354, by rfl⟩ : syracuseStep 391139 = 586709) B586709
theorem B686051 : Blo 259821 686051 := bstep (se 1 (by rfl) ⟨514538, by rfl⟩ : syracuseStep 686051 = 1029077) B1029077
theorem B260083 : Blo 259821 260083 := bstep (se 1 (by rfl) ⟨195062, by rfl⟩ : syracuseStep 260083 = 390125) B390125
theorem B391169 : Blo 259821 391169 := bstep (se 2 (by rfl) ⟨146688, by rfl⟩ : syracuseStep 391169 = 293377) B293377
theorem B260099 : Blo 259821 260099 := bstep (se 1 (by rfl) ⟨195074, by rfl⟩ : syracuseStep 260099 = 390149) B390149
theorem B260115 : Blo 259821 260115 := bstep (se 1 (by rfl) ⟨195086, by rfl⟩ : syracuseStep 260115 = 390173) B390173
theorem B391187 : Blo 259821 391187 := bstep (se 1 (by rfl) ⟨293390, by rfl⟩ : syracuseStep 391187 = 586781) B586781
theorem B260131 : Blo 259821 260131 := bstep (se 1 (by rfl) ⟨195098, by rfl⟩ : syracuseStep 260131 = 390197) B390197
theorem B391217 : Blo 259821 391217 := bstep (se 2 (by rfl) ⟨146706, by rfl⟩ : syracuseStep 391217 = 293413) B293413
theorem B587825 : Blo 259821 587825 := bstep (se 2 (by rfl) ⟨220434, by rfl⟩ : syracuseStep 587825 = 440869) B440869
theorem B260147 : Blo 259821 260147 := bstep (se 1 (by rfl) ⟨195110, by rfl⟩ : syracuseStep 260147 = 390221) B390221
theorem B882737 : Blo 259821 882737 := bstep (se 2 (by rfl) ⟨331026, by rfl⟩ : syracuseStep 882737 = 662053) B662053
theorem B260163 : Blo 259821 260163 := bstep (se 1 (by rfl) ⟨195122, by rfl⟩ : syracuseStep 260163 = 390245) B390245
theorem B391235 : Blo 259821 391235 := bstep (se 1 (by rfl) ⟨293426, by rfl⟩ : syracuseStep 391235 = 586853) B586853
theorem B587843 : Blo 259821 587843 := bstep (se 1 (by rfl) ⟨440882, by rfl⟩ : syracuseStep 587843 = 881765) B881765
theorem B260179 : Blo 259821 260179 := bstep (se 1 (by rfl) ⟨195134, by rfl⟩ : syracuseStep 260179 = 390269) B390269
theorem B391265 : Blo 259821 391265 := bstep (se 2 (by rfl) ⟨146724, by rfl⟩ : syracuseStep 391265 = 293449) B293449
theorem B260195 : Blo 259821 260195 := bstep (se 1 (by rfl) ⟨195146, by rfl⟩ : syracuseStep 260195 = 390293) B390293
theorem B292963 : Blo 259821 292963 := bstep (se 1 (by rfl) ⟨219722, by rfl⟩ : syracuseStep 292963 = 439445) B439445
theorem B260211 : Blo 259821 260211 := bstep (se 1 (by rfl) ⟨195158, by rfl⟩ : syracuseStep 260211 = 390317) B390317
theorem B391283 : Blo 259821 391283 := bstep (se 1 (by rfl) ⟨293462, by rfl⟩ : syracuseStep 391283 = 586925) B586925
theorem B260227 : Blo 259821 260227 := bstep (se 1 (by rfl) ⟨195170, by rfl⟩ : syracuseStep 260227 = 390341) B390341
theorem B391313 : Blo 259821 391313 := bstep (se 2 (by rfl) ⟨146742, by rfl⟩ : syracuseStep 391313 = 293485) B293485
theorem B260243 : Blo 259821 260243 := bstep (se 1 (by rfl) ⟨195182, by rfl⟩ : syracuseStep 260243 = 390365) B390365
theorem B260259 : Blo 259821 260259 := bstep (se 1 (by rfl) ⟨195194, by rfl⟩ : syracuseStep 260259 = 390389) B390389
theorem B391331 : Blo 259821 391331 := bstep (se 1 (by rfl) ⟨293498, by rfl⟩ : syracuseStep 391331 = 586997) B586997
theorem B260275 : Blo 259821 260275 := bstep (se 1 (by rfl) ⟨195206, by rfl⟩ : syracuseStep 260275 = 390413) B390413
theorem B391361 : Blo 259821 391361 := bstep (se 2 (by rfl) ⟨146760, by rfl⟩ : syracuseStep 391361 = 293521) B293521
theorem B260291 : Blo 259821 260291 := bstep (se 1 (by rfl) ⟨195218, by rfl⟩ : syracuseStep 260291 = 390437) B390437
theorem B260307 : Blo 259821 260307 := bstep (se 1 (by rfl) ⟨195230, by rfl⟩ : syracuseStep 260307 = 390461) B390461
theorem B391379 : Blo 259821 391379 := bstep (se 1 (by rfl) ⟨293534, by rfl⟩ : syracuseStep 391379 = 587069) B587069
theorem B260323 : Blo 259821 260323 := bstep (se 1 (by rfl) ⟨195242, by rfl⟩ : syracuseStep 260323 = 390485) B390485
theorem B391409 : Blo 259821 391409 := bstep (se 2 (by rfl) ⟨146778, by rfl⟩ : syracuseStep 391409 = 293557) B293557
theorem B260339 : Blo 259821 260339 := bstep (se 1 (by rfl) ⟨195254, by rfl⟩ : syracuseStep 260339 = 390509) B390509
theorem B293107 : Blo 259821 293107 := bstep (se 1 (by rfl) ⟨219830, by rfl⟩ : syracuseStep 293107 = 439661) B439661
theorem B260355 : Blo 259821 260355 := bstep (se 1 (by rfl) ⟨195266, by rfl⟩ : syracuseStep 260355 = 390533) B390533
theorem B391427 : Blo 259821 391427 := bstep (se 1 (by rfl) ⟨293570, by rfl⟩ : syracuseStep 391427 = 587141) B587141
theorem B260371 : Blo 259821 260371 := bstep (se 1 (by rfl) ⟨195278, by rfl⟩ : syracuseStep 260371 = 390557) B390557
theorem B391457 : Blo 259821 391457 := bstep (se 2 (by rfl) ⟨146796, by rfl⟩ : syracuseStep 391457 = 293593) B293593
theorem B260387 : Blo 259821 260387 := bstep (se 1 (by rfl) ⟨195290, by rfl⟩ : syracuseStep 260387 = 390581) B390581
theorem B260403 : Blo 259821 260403 := bstep (se 1 (by rfl) ⟨195302, by rfl⟩ : syracuseStep 260403 = 390605) B390605
theorem B391475 : Blo 259821 391475 := bstep (se 1 (by rfl) ⟨293606, by rfl⟩ : syracuseStep 391475 = 587213) B587213
theorem B260419 : Blo 259821 260419 := bstep (se 1 (by rfl) ⟨195314, by rfl⟩ : syracuseStep 260419 = 390629) B390629
theorem B391505 : Blo 259821 391505 := bstep (se 2 (by rfl) ⟨146814, by rfl⟩ : syracuseStep 391505 = 293629) B293629
theorem B588113 : Blo 259821 588113 := bstep (se 2 (by rfl) ⟨220542, by rfl⟩ : syracuseStep 588113 = 441085) B441085
theorem B260435 : Blo 259821 260435 := bstep (se 1 (by rfl) ⟨195326, by rfl⟩ : syracuseStep 260435 = 390653) B390653
theorem B260451 : Blo 259821 260451 := bstep (se 1 (by rfl) ⟨195338, by rfl⟩ : syracuseStep 260451 = 390677) B390677
theorem B391523 : Blo 259821 391523 := bstep (se 1 (by rfl) ⟨293642, by rfl⟩ : syracuseStep 391523 = 587285) B587285
theorem B588131 : Blo 259821 588131 := bstep (se 1 (by rfl) ⟨441098, by rfl⟩ : syracuseStep 588131 = 882197) B882197
theorem B260467 : Blo 259821 260467 := bstep (se 1 (by rfl) ⟨195350, by rfl⟩ : syracuseStep 260467 = 390701) B390701
theorem B391553 : Blo 259821 391553 := bstep (se 2 (by rfl) ⟨146832, by rfl⟩ : syracuseStep 391553 = 293665) B293665
theorem B260483 : Blo 259821 260483 := bstep (se 1 (by rfl) ⟨195362, by rfl⟩ : syracuseStep 260483 = 390725) B390725
theorem B293251 : Blo 259821 293251 := bstep (se 1 (by rfl) ⟨219938, by rfl⟩ : syracuseStep 293251 = 439877) B439877
theorem B260499 : Blo 259821 260499 := bstep (se 1 (by rfl) ⟨195374, by rfl⟩ : syracuseStep 260499 = 390749) B390749
theorem B391571 : Blo 259821 391571 := bstep (se 1 (by rfl) ⟨293678, by rfl⟩ : syracuseStep 391571 = 587357) B587357
theorem B260515 : Blo 259821 260515 := bstep (se 1 (by rfl) ⟨195386, by rfl⟩ : syracuseStep 260515 = 390773) B390773
theorem B391601 : Blo 259821 391601 := bstep (se 2 (by rfl) ⟨146850, by rfl⟩ : syracuseStep 391601 = 293701) B293701
theorem B260531 : Blo 259821 260531 := bstep (se 1 (by rfl) ⟨195398, by rfl⟩ : syracuseStep 260531 = 390797) B390797
theorem B260547 : Blo 259821 260547 := bstep (se 1 (by rfl) ⟨195410, by rfl⟩ : syracuseStep 260547 = 390821) B390821
theorem B391619 : Blo 259821 391619 := bstep (se 1 (by rfl) ⟨293714, by rfl⟩ : syracuseStep 391619 = 587429) B587429
theorem B260563 : Blo 259821 260563 := bstep (se 1 (by rfl) ⟨195422, by rfl⟩ : syracuseStep 260563 = 390845) B390845
theorem B391649 : Blo 259821 391649 := bstep (se 2 (by rfl) ⟨146868, by rfl⟩ : syracuseStep 391649 = 293737) B293737
theorem B555491 : Blo 259821 555491 := bstep (se 1 (by rfl) ⟨416618, by rfl⟩ : syracuseStep 555491 = 833237) B833237
theorem B260579 : Blo 259821 260579 := bstep (se 1 (by rfl) ⟨195434, by rfl⟩ : syracuseStep 260579 = 390869) B390869
theorem B260595 : Blo 259821 260595 := bstep (se 1 (by rfl) ⟨195446, by rfl⟩ : syracuseStep 260595 = 390893) B390893
theorem B391667 : Blo 259821 391667 := bstep (se 1 (by rfl) ⟨293750, by rfl⟩ : syracuseStep 391667 = 587501) B587501
theorem B260611 : Blo 259821 260611 := bstep (se 1 (by rfl) ⟨195458, by rfl⟩ : syracuseStep 260611 = 390917) B390917
theorem B391697 : Blo 259821 391697 := bstep (se 2 (by rfl) ⟨146886, by rfl⟩ : syracuseStep 391697 = 293773) B293773
theorem B260627 : Blo 259821 260627 := bstep (se 1 (by rfl) ⟨195470, by rfl⟩ : syracuseStep 260627 = 390941) B390941
theorem B293395 : Blo 259821 293395 := bstep (se 1 (by rfl) ⟨220046, by rfl⟩ : syracuseStep 293395 = 440093) B440093
theorem B260643 : Blo 259821 260643 := bstep (se 1 (by rfl) ⟨195482, by rfl⟩ : syracuseStep 260643 = 390965) B390965
theorem B391715 : Blo 259821 391715 := bstep (se 1 (by rfl) ⟨293786, by rfl⟩ : syracuseStep 391715 = 587573) B587573
theorem B260659 : Blo 259821 260659 := bstep (se 1 (by rfl) ⟨195494, by rfl⟩ : syracuseStep 260659 = 390989) B390989
theorem B391745 : Blo 259821 391745 := bstep (se 2 (by rfl) ⟨146904, by rfl⟩ : syracuseStep 391745 = 293809) B293809
theorem B260675 : Blo 259821 260675 := bstep (se 1 (by rfl) ⟨195506, by rfl⟩ : syracuseStep 260675 = 391013) B391013
theorem B883277 : Blo 259821 883277 := bstep (se 3 (by rfl) ⟨165614, by rfl⟩ : syracuseStep 883277 = 331229) B331229
theorem B555601 : Blo 259821 555601 := bstep (se 2 (by rfl) ⟨208350, by rfl⟩ : syracuseStep 555601 = 416701) B416701
theorem B260691 : Blo 259821 260691 := bstep (se 1 (by rfl) ⟨195518, by rfl⟩ : syracuseStep 260691 = 391037) B391037
theorem B391763 : Blo 259821 391763 := bstep (se 1 (by rfl) ⟨293822, by rfl⟩ : syracuseStep 391763 = 587645) B587645
theorem B260707 : Blo 259821 260707 := bstep (se 1 (by rfl) ⟨195530, by rfl⟩ : syracuseStep 260707 = 391061) B391061
theorem B391793 : Blo 259821 391793 := bstep (se 2 (by rfl) ⟨146922, by rfl⟩ : syracuseStep 391793 = 293845) B293845
theorem B588401 : Blo 259821 588401 := bstep (se 2 (by rfl) ⟨220650, by rfl⟩ : syracuseStep 588401 = 441301) B441301
theorem B260723 : Blo 259821 260723 := bstep (se 1 (by rfl) ⟨195542, by rfl⟩ : syracuseStep 260723 = 391085) B391085
theorem B260739 : Blo 259821 260739 := bstep (se 1 (by rfl) ⟨195554, by rfl⟩ : syracuseStep 260739 = 391109) B391109
theorem B391811 : Blo 259821 391811 := bstep (se 1 (by rfl) ⟨293858, by rfl⟩ : syracuseStep 391811 = 587717) B587717
theorem B588419 : Blo 259821 588419 := bstep (se 1 (by rfl) ⟨441314, by rfl⟩ : syracuseStep 588419 = 882629) B882629
theorem B883331 : Blo 259821 883331 := bstep (se 1 (by rfl) ⟨662498, by rfl⟩ : syracuseStep 883331 = 1324997) B1324997
theorem B260755 : Blo 259821 260755 := bstep (se 1 (by rfl) ⟨195566, by rfl⟩ : syracuseStep 260755 = 391133) B391133
theorem B391841 : Blo 259821 391841 := bstep (se 2 (by rfl) ⟨146940, by rfl⟩ : syracuseStep 391841 = 293881) B293881
theorem B260771 : Blo 259821 260771 := bstep (se 1 (by rfl) ⟨195578, by rfl⟩ : syracuseStep 260771 = 391157) B391157
theorem B293539 : Blo 259821 293539 := bstep (se 1 (by rfl) ⟨220154, by rfl⟩ : syracuseStep 293539 = 440309) B440309
theorem B260787 : Blo 259821 260787 := bstep (se 1 (by rfl) ⟨195590, by rfl⟩ : syracuseStep 260787 = 391181) B391181
theorem B391859 : Blo 259821 391859 := bstep (se 1 (by rfl) ⟨293894, by rfl⟩ : syracuseStep 391859 = 587789) B587789
theorem B260803 : Blo 259821 260803 := bstep (se 1 (by rfl) ⟨195602, by rfl⟩ : syracuseStep 260803 = 391205) B391205
theorem B391889 : Blo 259821 391889 := bstep (se 2 (by rfl) ⟨146958, by rfl⟩ : syracuseStep 391889 = 293917) B293917
theorem B260819 : Blo 259821 260819 := bstep (se 1 (by rfl) ⟨195614, by rfl⟩ : syracuseStep 260819 = 391229) B391229
theorem B260835 : Blo 259821 260835 := bstep (se 1 (by rfl) ⟨195626, by rfl⟩ : syracuseStep 260835 = 391253) B391253
theorem B391907 : Blo 259821 391907 := bstep (se 1 (by rfl) ⟨293930, by rfl⟩ : syracuseStep 391907 = 587861) B587861
theorem B260851 : Blo 259821 260851 := bstep (se 1 (by rfl) ⟨195638, by rfl⟩ : syracuseStep 260851 = 391277) B391277
theorem B391937 : Blo 259821 391937 := bstep (se 2 (by rfl) ⟨146976, by rfl⟩ : syracuseStep 391937 = 293953) B293953
theorem B260867 : Blo 259821 260867 := bstep (se 1 (by rfl) ⟨195650, by rfl⟩ : syracuseStep 260867 = 391301) B391301
theorem B260883 : Blo 259821 260883 := bstep (se 1 (by rfl) ⟨195662, by rfl⟩ : syracuseStep 260883 = 391325) B391325
theorem B391955 : Blo 259821 391955 := bstep (se 1 (by rfl) ⟨293966, by rfl⟩ : syracuseStep 391955 = 587933) B587933
theorem B260899 : Blo 259821 260899 := bstep (se 1 (by rfl) ⟨195674, by rfl⟩ : syracuseStep 260899 = 391349) B391349
theorem B391985 : Blo 259821 391985 := bstep (se 2 (by rfl) ⟨146994, by rfl⟩ : syracuseStep 391985 = 293989) B293989
theorem B260915 : Blo 259821 260915 := bstep (se 1 (by rfl) ⟨195686, by rfl⟩ : syracuseStep 260915 = 391373) B391373
theorem B293683 : Blo 259821 293683 := bstep (se 1 (by rfl) ⟨220262, by rfl⟩ : syracuseStep 293683 = 440525) B440525
theorem B260931 : Blo 259821 260931 := bstep (se 1 (by rfl) ⟨195698, by rfl⟩ : syracuseStep 260931 = 391397) B391397
theorem B392003 : Blo 259821 392003 := bstep (se 1 (by rfl) ⟨294002, by rfl⟩ : syracuseStep 392003 = 588005) B588005
theorem B260947 : Blo 259821 260947 := bstep (se 1 (by rfl) ⟨195710, by rfl⟩ : syracuseStep 260947 = 391421) B391421
theorem B392033 : Blo 259821 392033 := bstep (se 2 (by rfl) ⟨147012, by rfl⟩ : syracuseStep 392033 = 294025) B294025
theorem B260963 : Blo 259821 260963 := bstep (se 1 (by rfl) ⟨195722, by rfl⟩ : syracuseStep 260963 = 391445) B391445
theorem B260979 : Blo 259821 260979 := bstep (se 1 (by rfl) ⟨195734, by rfl⟩ : syracuseStep 260979 = 391469) B391469
theorem B392051 : Blo 259821 392051 := bstep (se 1 (by rfl) ⟨294038, by rfl⟩ : syracuseStep 392051 = 588077) B588077
theorem B260995 : Blo 259821 260995 := bstep (se 1 (by rfl) ⟨195746, by rfl⟩ : syracuseStep 260995 = 391493) B391493
theorem B392081 : Blo 259821 392081 := bstep (se 2 (by rfl) ⟨147030, by rfl⟩ : syracuseStep 392081 = 294061) B294061
theorem B588689 : Blo 259821 588689 := bstep (se 2 (by rfl) ⟨220758, by rfl⟩ : syracuseStep 588689 = 441517) B441517
theorem B261011 : Blo 259821 261011 := bstep (se 1 (by rfl) ⟨195758, by rfl⟩ : syracuseStep 261011 = 391517) B391517
theorem B883601 : Blo 259821 883601 := bstep (se 2 (by rfl) ⟨331350, by rfl⟩ : syracuseStep 883601 = 662701) B662701
theorem B588707 : Blo 259821 588707 := bstep (se 1 (by rfl) ⟨441530, by rfl⟩ : syracuseStep 588707 = 883061) B883061
theorem B261027 : Blo 259821 261027 := bstep (se 1 (by rfl) ⟨195770, by rfl⟩ : syracuseStep 261027 = 391541) B391541
theorem B392099 : Blo 259821 392099 := bstep (se 1 (by rfl) ⟨294074, by rfl⟩ : syracuseStep 392099 = 588149) B588149
theorem B261043 : Blo 259821 261043 := bstep (se 1 (by rfl) ⟨195782, by rfl⟩ : syracuseStep 261043 = 391565) B391565
theorem B392129 : Blo 259821 392129 := bstep (se 2 (by rfl) ⟨147048, by rfl⟩ : syracuseStep 392129 = 294097) B294097
theorem B261059 : Blo 259821 261059 := bstep (se 1 (by rfl) ⟨195794, by rfl⟩ : syracuseStep 261059 = 391589) B391589
theorem B293827 : Blo 259821 293827 := bstep (se 1 (by rfl) ⟨220370, by rfl⟩ : syracuseStep 293827 = 440741) B440741
theorem B261075 : Blo 259821 261075 := bstep (se 1 (by rfl) ⟨195806, by rfl⟩ : syracuseStep 261075 = 391613) B391613
theorem B392147 : Blo 259821 392147 := bstep (se 1 (by rfl) ⟨294110, by rfl⟩ : syracuseStep 392147 = 588221) B588221
theorem B261091 : Blo 259821 261091 := bstep (se 1 (by rfl) ⟨195818, by rfl⟩ : syracuseStep 261091 = 391637) B391637
theorem B392177 : Blo 259821 392177 := bstep (se 2 (by rfl) ⟨147066, by rfl⟩ : syracuseStep 392177 = 294133) B294133
theorem B261107 : Blo 259821 261107 := bstep (se 1 (by rfl) ⟨195830, by rfl⟩ : syracuseStep 261107 = 391661) B391661
theorem B261123 : Blo 259821 261123 := bstep (se 1 (by rfl) ⟨195842, by rfl⟩ : syracuseStep 261123 = 391685) B391685
theorem B392195 : Blo 259821 392195 := bstep (se 1 (by rfl) ⟨294146, by rfl⟩ : syracuseStep 392195 = 588293) B588293
theorem B261139 : Blo 259821 261139 := bstep (se 1 (by rfl) ⟨195854, by rfl⟩ : syracuseStep 261139 = 391709) B391709
theorem B392225 : Blo 259821 392225 := bstep (se 2 (by rfl) ⟨147084, by rfl⟩ : syracuseStep 392225 = 294169) B294169
theorem B261155 : Blo 259821 261155 := bstep (se 1 (by rfl) ⟨195866, by rfl⟩ : syracuseStep 261155 = 391733) B391733
theorem B261171 : Blo 259821 261171 := bstep (se 1 (by rfl) ⟨195878, by rfl⟩ : syracuseStep 261171 = 391757) B391757
theorem B392243 : Blo 259821 392243 := bstep (se 1 (by rfl) ⟨294182, by rfl⟩ : syracuseStep 392243 = 588365) B588365
theorem B261187 : Blo 259821 261187 := bstep (se 1 (by rfl) ⟨195890, by rfl⟩ : syracuseStep 261187 = 391781) B391781
theorem B392273 : Blo 259821 392273 := bstep (se 2 (by rfl) ⟨147102, by rfl⟩ : syracuseStep 392273 = 294205) B294205
theorem B261203 : Blo 259821 261203 := bstep (se 1 (by rfl) ⟨195902, by rfl⟩ : syracuseStep 261203 = 391805) B391805
theorem B293971 : Blo 259821 293971 := bstep (se 1 (by rfl) ⟨220478, by rfl⟩ : syracuseStep 293971 = 440957) B440957
theorem B261219 : Blo 259821 261219 := bstep (se 1 (by rfl) ⟨195914, by rfl⟩ : syracuseStep 261219 = 391829) B391829
theorem B392291 : Blo 259821 392291 := bstep (se 1 (by rfl) ⟨294218, by rfl⟩ : syracuseStep 392291 = 588437) B588437
theorem B261235 : Blo 259821 261235 := bstep (se 1 (by rfl) ⟨195926, by rfl⟩ : syracuseStep 261235 = 391853) B391853
theorem B392321 : Blo 259821 392321 := bstep (se 2 (by rfl) ⟨147120, by rfl⟩ : syracuseStep 392321 = 294241) B294241
theorem B261251 : Blo 259821 261251 := bstep (se 1 (by rfl) ⟨195938, by rfl⟩ : syracuseStep 261251 = 391877) B391877
theorem B261267 : Blo 259821 261267 := bstep (se 1 (by rfl) ⟨195950, by rfl⟩ : syracuseStep 261267 = 391901) B391901
theorem B392339 : Blo 259821 392339 := bstep (se 1 (by rfl) ⟨294254, by rfl⟩ : syracuseStep 392339 = 588509) B588509
theorem B261283 : Blo 259821 261283 := bstep (se 1 (by rfl) ⟨195962, by rfl⟩ : syracuseStep 261283 = 391925) B391925
theorem B392369 : Blo 259821 392369 := bstep (se 2 (by rfl) ⟨147138, by rfl⟩ : syracuseStep 392369 = 294277) B294277
theorem B588977 : Blo 259821 588977 := bstep (se 2 (by rfl) ⟨220866, by rfl⟩ : syracuseStep 588977 = 441733) B441733
theorem B261299 : Blo 259821 261299 := bstep (se 1 (by rfl) ⟨195974, by rfl⟩ : syracuseStep 261299 = 391949) B391949
theorem B261315 : Blo 259821 261315 := bstep (se 1 (by rfl) ⟨195986, by rfl⟩ : syracuseStep 261315 = 391973) B391973
theorem B392387 : Blo 259821 392387 := bstep (se 1 (by rfl) ⟨294290, by rfl⟩ : syracuseStep 392387 = 588581) B588581
theorem B588995 : Blo 259821 588995 := bstep (se 1 (by rfl) ⟨441746, by rfl⟩ : syracuseStep 588995 = 883493) B883493
theorem B261331 : Blo 259821 261331 := bstep (se 1 (by rfl) ⟨195998, by rfl⟩ : syracuseStep 261331 = 391997) B391997
theorem B392417 : Blo 259821 392417 := bstep (se 2 (by rfl) ⟨147156, by rfl⟩ : syracuseStep 392417 = 294313) B294313
theorem B261347 : Blo 259821 261347 := bstep (se 1 (by rfl) ⟨196010, by rfl⟩ : syracuseStep 261347 = 392021) B392021
theorem B294115 : Blo 259821 294115 := bstep (se 1 (by rfl) ⟨220586, by rfl⟩ : syracuseStep 294115 = 441173) B441173
theorem B261363 : Blo 259821 261363 := bstep (se 1 (by rfl) ⟨196022, by rfl⟩ : syracuseStep 261363 = 392045) B392045
theorem B392435 : Blo 259821 392435 := bstep (se 1 (by rfl) ⟨294326, by rfl⟩ : syracuseStep 392435 = 588653) B588653
theorem B261379 : Blo 259821 261379 := bstep (se 1 (by rfl) ⟨196034, by rfl⟩ : syracuseStep 261379 = 392069) B392069
theorem B392465 : Blo 259821 392465 := bstep (se 2 (by rfl) ⟨147174, by rfl⟩ : syracuseStep 392465 = 294349) B294349
theorem B261395 : Blo 259821 261395 := bstep (se 1 (by rfl) ⟨196046, by rfl⟩ : syracuseStep 261395 = 392093) B392093
theorem B261411 : Blo 259821 261411 := bstep (se 1 (by rfl) ⟨196058, by rfl⟩ : syracuseStep 261411 = 392117) B392117
theorem B392483 : Blo 259821 392483 := bstep (se 1 (by rfl) ⟨294362, by rfl⟩ : syracuseStep 392483 = 588725) B588725
theorem B261427 : Blo 259821 261427 := bstep (se 1 (by rfl) ⟨196070, by rfl⟩ : syracuseStep 261427 = 392141) B392141
theorem B392513 : Blo 259821 392513 := bstep (se 2 (by rfl) ⟨147192, by rfl⟩ : syracuseStep 392513 = 294385) B294385
theorem B261443 : Blo 259821 261443 := bstep (se 1 (by rfl) ⟨196082, by rfl⟩ : syracuseStep 261443 = 392165) B392165
theorem B3374405 : Blo 259821 3374405 := bstep (se 4 (by rfl) ⟨316350, by rfl⟩ : syracuseStep 3374405 = 632701) B632701
theorem B261459 : Blo 259821 261459 := bstep (se 1 (by rfl) ⟨196094, by rfl⟩ : syracuseStep 261459 = 392189) B392189
theorem B392531 : Blo 259821 392531 := bstep (se 1 (by rfl) ⟨294398, by rfl⟩ : syracuseStep 392531 = 588797) B588797
theorem B261475 : Blo 259821 261475 := bstep (se 1 (by rfl) ⟨196106, by rfl⟩ : syracuseStep 261475 = 392213) B392213
theorem B392561 : Blo 259821 392561 := bstep (se 2 (by rfl) ⟨147210, by rfl⟩ : syracuseStep 392561 = 294421) B294421
theorem B261491 : Blo 259821 261491 := bstep (se 1 (by rfl) ⟨196118, by rfl⟩ : syracuseStep 261491 = 392237) B392237
theorem B294259 : Blo 259821 294259 := bstep (se 1 (by rfl) ⟨220694, by rfl⟩ : syracuseStep 294259 = 441389) B441389
theorem B261507 : Blo 259821 261507 := bstep (se 1 (by rfl) ⟨196130, by rfl⟩ : syracuseStep 261507 = 392261) B392261
theorem B392579 : Blo 259821 392579 := bstep (se 1 (by rfl) ⟨294434, by rfl⟩ : syracuseStep 392579 = 588869) B588869
theorem B261523 : Blo 259821 261523 := bstep (se 1 (by rfl) ⟨196142, by rfl⟩ : syracuseStep 261523 = 392285) B392285
theorem B392609 : Blo 259821 392609 := bstep (se 2 (by rfl) ⟨147228, by rfl⟩ : syracuseStep 392609 = 294457) B294457
theorem B261539 : Blo 259821 261539 := bstep (se 1 (by rfl) ⟨196154, by rfl⟩ : syracuseStep 261539 = 392309) B392309
theorem B884141 : Blo 259821 884141 := bstep (se 3 (by rfl) ⟨165776, by rfl⟩ : syracuseStep 884141 = 331553) B331553
theorem B261555 : Blo 259821 261555 := bstep (se 1 (by rfl) ⟨196166, by rfl⟩ : syracuseStep 261555 = 392333) B392333
theorem B392627 : Blo 259821 392627 := bstep (se 1 (by rfl) ⟨294470, by rfl⟩ : syracuseStep 392627 = 588941) B588941
theorem B261571 : Blo 259821 261571 := bstep (se 1 (by rfl) ⟨196178, by rfl⟩ : syracuseStep 261571 = 392357) B392357
theorem B589265 : Blo 259821 589265 := bstep (se 2 (by rfl) ⟨220974, by rfl⟩ : syracuseStep 589265 = 441949) B441949
theorem B392657 : Blo 259821 392657 := bstep (se 2 (by rfl) ⟨147246, by rfl⟩ : syracuseStep 392657 = 294493) B294493
theorem B261587 : Blo 259821 261587 := bstep (se 1 (by rfl) ⟨196190, by rfl⟩ : syracuseStep 261587 = 392381) B392381
theorem B261603 : Blo 259821 261603 := bstep (se 1 (by rfl) ⟨196202, by rfl⟩ : syracuseStep 261603 = 392405) B392405
theorem B392675 : Blo 259821 392675 := bstep (se 1 (by rfl) ⟨294506, by rfl⟩ : syracuseStep 392675 = 589013) B589013
theorem B589283 : Blo 259821 589283 := bstep (se 1 (by rfl) ⟨441962, by rfl⟩ : syracuseStep 589283 = 883925) B883925
theorem B884195 : Blo 259821 884195 := bstep (se 1 (by rfl) ⟨663146, by rfl⟩ : syracuseStep 884195 = 1326293) B1326293
theorem B261619 : Blo 259821 261619 := bstep (se 1 (by rfl) ⟨196214, by rfl⟩ : syracuseStep 261619 = 392429) B392429
theorem B392705 : Blo 259821 392705 := bstep (se 2 (by rfl) ⟨147264, by rfl⟩ : syracuseStep 392705 = 294529) B294529
theorem B261635 : Blo 259821 261635 := bstep (se 1 (by rfl) ⟨196226, by rfl⟩ : syracuseStep 261635 = 392453) B392453
theorem B294403 : Blo 259821 294403 := bstep (se 1 (by rfl) ⟨220802, by rfl⟩ : syracuseStep 294403 = 441605) B441605
theorem B261651 : Blo 259821 261651 := bstep (se 1 (by rfl) ⟨196238, by rfl⟩ : syracuseStep 261651 = 392477) B392477
theorem B392723 : Blo 259821 392723 := bstep (se 1 (by rfl) ⟨294542, by rfl⟩ : syracuseStep 392723 = 589085) B589085
theorem B261667 : Blo 259821 261667 := bstep (se 1 (by rfl) ⟨196250, by rfl⟩ : syracuseStep 261667 = 392501) B392501
theorem B392753 : Blo 259821 392753 := bstep (se 2 (by rfl) ⟨147282, by rfl⟩ : syracuseStep 392753 = 294565) B294565
theorem B261683 : Blo 259821 261683 := bstep (se 1 (by rfl) ⟨196262, by rfl⟩ : syracuseStep 261683 = 392525) B392525
theorem B261699 : Blo 259821 261699 := bstep (se 1 (by rfl) ⟨196274, by rfl⟩ : syracuseStep 261699 = 392549) B392549
theorem B392771 : Blo 259821 392771 := bstep (se 1 (by rfl) ⟨294578, by rfl⟩ : syracuseStep 392771 = 589157) B589157
theorem B261715 : Blo 259821 261715 := bstep (se 1 (by rfl) ⟨196286, by rfl⟩ : syracuseStep 261715 = 392573) B392573
theorem B392801 : Blo 259821 392801 := bstep (se 2 (by rfl) ⟨147300, by rfl⟩ : syracuseStep 392801 = 294601) B294601
theorem B261731 : Blo 259821 261731 := bstep (se 1 (by rfl) ⟨196298, by rfl⟩ : syracuseStep 261731 = 392597) B392597
theorem B261747 : Blo 259821 261747 := bstep (se 1 (by rfl) ⟨196310, by rfl⟩ : syracuseStep 261747 = 392621) B392621
theorem B392819 : Blo 259821 392819 := bstep (se 1 (by rfl) ⟨294614, by rfl⟩ : syracuseStep 392819 = 589229) B589229
theorem B261763 : Blo 259821 261763 := bstep (se 1 (by rfl) ⟨196322, by rfl⟩ : syracuseStep 261763 = 392645) B392645
theorem B392849 : Blo 259821 392849 := bstep (se 2 (by rfl) ⟨147318, by rfl⟩ : syracuseStep 392849 = 294637) B294637
theorem B261779 : Blo 259821 261779 := bstep (se 1 (by rfl) ⟨196334, by rfl⟩ : syracuseStep 261779 = 392669) B392669
theorem B294547 : Blo 259821 294547 := bstep (se 1 (by rfl) ⟨220910, by rfl⟩ : syracuseStep 294547 = 441821) B441821
theorem B261795 : Blo 259821 261795 := bstep (se 1 (by rfl) ⟨196346, by rfl⟩ : syracuseStep 261795 = 392693) B392693
theorem B392867 : Blo 259821 392867 := bstep (se 1 (by rfl) ⟨294650, by rfl⟩ : syracuseStep 392867 = 589301) B589301
theorem B261811 : Blo 259821 261811 := bstep (se 1 (by rfl) ⟨196358, by rfl⟩ : syracuseStep 261811 = 392717) B392717
theorem B392897 : Blo 259821 392897 := bstep (se 2 (by rfl) ⟨147336, by rfl⟩ : syracuseStep 392897 = 294673) B294673
theorem B261827 : Blo 259821 261827 := bstep (se 1 (by rfl) ⟨196370, by rfl⟩ : syracuseStep 261827 = 392741) B392741
theorem B261843 : Blo 259821 261843 := bstep (se 1 (by rfl) ⟨196382, by rfl⟩ : syracuseStep 261843 = 392765) B392765
theorem B392915 : Blo 259821 392915 := bstep (se 1 (by rfl) ⟨294686, by rfl⟩ : syracuseStep 392915 = 589373) B589373
theorem B261859 : Blo 259821 261859 := bstep (se 1 (by rfl) ⟨196394, by rfl⟩ : syracuseStep 261859 = 392789) B392789
theorem B392945 : Blo 259821 392945 := bstep (se 2 (by rfl) ⟨147354, by rfl⟩ : syracuseStep 392945 = 294709) B294709
theorem B589553 : Blo 259821 589553 := bstep (se 2 (by rfl) ⟨221082, by rfl⟩ : syracuseStep 589553 = 442165) B442165
theorem B261875 : Blo 259821 261875 := bstep (se 1 (by rfl) ⟨196406, by rfl⟩ : syracuseStep 261875 = 392813) B392813
theorem B884465 : Blo 259821 884465 := bstep (se 2 (by rfl) ⟨331674, by rfl⟩ : syracuseStep 884465 = 663349) B663349
theorem B261891 : Blo 259821 261891 := bstep (se 1 (by rfl) ⟨196418, by rfl⟩ : syracuseStep 261891 = 392837) B392837
theorem B392963 : Blo 259821 392963 := bstep (se 1 (by rfl) ⟨294722, by rfl⟩ : syracuseStep 392963 = 589445) B589445
theorem B589571 : Blo 259821 589571 := bstep (se 1 (by rfl) ⟨442178, by rfl⟩ : syracuseStep 589571 = 884357) B884357
theorem B261907 : Blo 259821 261907 := bstep (se 1 (by rfl) ⟨196430, by rfl⟩ : syracuseStep 261907 = 392861) B392861
theorem B392993 : Blo 259821 392993 := bstep (se 2 (by rfl) ⟨147372, by rfl⟩ : syracuseStep 392993 = 294745) B294745
theorem B261923 : Blo 259821 261923 := bstep (se 1 (by rfl) ⟨196442, by rfl⟩ : syracuseStep 261923 = 392885) B392885
theorem B294691 : Blo 259821 294691 := bstep (se 1 (by rfl) ⟨221018, by rfl⟩ : syracuseStep 294691 = 442037) B442037
theorem B261939 : Blo 259821 261939 := bstep (se 1 (by rfl) ⟨196454, by rfl⟩ : syracuseStep 261939 = 392909) B392909
theorem B393011 : Blo 259821 393011 := bstep (se 1 (by rfl) ⟨294758, by rfl⟩ : syracuseStep 393011 = 589517) B589517
theorem B261955 : Blo 259821 261955 := bstep (se 1 (by rfl) ⟨196466, by rfl⟩ : syracuseStep 261955 = 392933) B392933
theorem B393041 : Blo 259821 393041 := bstep (se 2 (by rfl) ⟨147390, by rfl⟩ : syracuseStep 393041 = 294781) B294781
theorem B261971 : Blo 259821 261971 := bstep (se 1 (by rfl) ⟨196478, by rfl⟩ : syracuseStep 261971 = 392957) B392957
theorem B261987 : Blo 259821 261987 := bstep (se 1 (by rfl) ⟨196490, by rfl⟩ : syracuseStep 261987 = 392981) B392981
theorem B393059 : Blo 259821 393059 := bstep (se 1 (by rfl) ⟨294794, by rfl⟩ : syracuseStep 393059 = 589589) B589589
theorem B262003 : Blo 259821 262003 := bstep (se 1 (by rfl) ⟨196502, by rfl⟩ : syracuseStep 262003 = 393005) B393005
theorem B393089 : Blo 259821 393089 := bstep (se 2 (by rfl) ⟨147408, by rfl⟩ : syracuseStep 393089 = 294817) B294817
theorem B262019 : Blo 259821 262019 := bstep (se 1 (by rfl) ⟨196514, by rfl⟩ : syracuseStep 262019 = 393029) B393029
theorem B262035 : Blo 259821 262035 := bstep (se 1 (by rfl) ⟨196526, by rfl⟩ : syracuseStep 262035 = 393053) B393053
theorem B393107 : Blo 259821 393107 := bstep (se 1 (by rfl) ⟨294830, by rfl⟩ : syracuseStep 393107 = 589661) B589661
theorem B262051 : Blo 259821 262051 := bstep (se 1 (by rfl) ⟨196538, by rfl⟩ : syracuseStep 262051 = 393077) B393077
theorem B393137 : Blo 259821 393137 := bstep (se 2 (by rfl) ⟨147426, by rfl⟩ : syracuseStep 393137 = 294853) B294853
theorem B262067 : Blo 259821 262067 := bstep (se 1 (by rfl) ⟨196550, by rfl⟩ : syracuseStep 262067 = 393101) B393101
theorem B294835 : Blo 259821 294835 := bstep (se 1 (by rfl) ⟨221126, by rfl⟩ : syracuseStep 294835 = 442253) B442253
theorem B262083 : Blo 259821 262083 := bstep (se 1 (by rfl) ⟨196562, by rfl⟩ : syracuseStep 262083 = 393125) B393125
theorem B393155 : Blo 259821 393155 := bstep (se 1 (by rfl) ⟨294866, by rfl⟩ : syracuseStep 393155 = 589733) B589733
theorem B262099 : Blo 259821 262099 := bstep (se 1 (by rfl) ⟨196574, by rfl⟩ : syracuseStep 262099 = 393149) B393149
theorem B393185 : Blo 259821 393185 := bstep (se 2 (by rfl) ⟨147444, by rfl⟩ : syracuseStep 393185 = 294889) B294889
theorem B262115 : Blo 259821 262115 := bstep (se 1 (by rfl) ⟨196586, by rfl⟩ : syracuseStep 262115 = 393173) B393173
theorem B262131 : Blo 259821 262131 := bstep (se 1 (by rfl) ⟨196598, by rfl⟩ : syracuseStep 262131 = 393197) B393197
theorem B393203 : Blo 259821 393203 := bstep (se 1 (by rfl) ⟨294902, by rfl⟩ : syracuseStep 393203 = 589805) B589805
theorem B393227 : Blo 259821 393227 := bstep (se 1 (by rfl) ⟨294920, by rfl⟩ : syracuseStep 393227 = 589841) B589841
theorem B262155 : Blo 259821 262155 := bstep (se 1 (by rfl) ⟨196616, by rfl⟩ : syracuseStep 262155 = 393233) B393233
theorem B393239 : Blo 259821 393239 := bstep (se 1 (by rfl) ⟨294929, by rfl⟩ : syracuseStep 393239 = 589859) B589859
theorem B262167 : Blo 259821 262167 := bstep (se 1 (by rfl) ⟨196625, by rfl⟩ : syracuseStep 262167 = 393251) B393251
theorem B262187 : Blo 259821 262187 := bstep (se 1 (by rfl) ⟨196640, by rfl⟩ : syracuseStep 262187 = 393281) B393281
theorem B262199 : Blo 259821 262199 := bstep (se 1 (by rfl) ⟨196649, by rfl⟩ : syracuseStep 262199 = 393299) B393299
theorem B557131 : Blo 259821 557131 := bstep (se 1 (by rfl) ⟨417848, by rfl⟩ : syracuseStep 557131 = 835697) B835697
theorem B3276875 : Blo 259821 3276875 := bstep (se 1 (by rfl) ⟨2457656, by rfl⟩ : syracuseStep 3276875 = 4915313) B4915313
theorem B262219 : Blo 259821 262219 := bstep (se 1 (by rfl) ⟨196664, by rfl⟩ : syracuseStep 262219 = 393329) B393329
theorem B262231 : Blo 259821 262231 := bstep (se 1 (by rfl) ⟨196673, by rfl⟩ : syracuseStep 262231 = 393347) B393347
theorem B589913 : Blo 259821 589913 := bstep (se 2 (by rfl) ⟨221217, by rfl⟩ : syracuseStep 589913 = 442435) B442435
theorem B393305 : Blo 259821 393305 := bstep (se 2 (by rfl) ⟨147489, by rfl⟩ : syracuseStep 393305 = 294979) B294979
theorem B262251 : Blo 259821 262251 := bstep (se 1 (by rfl) ⟨196688, by rfl⟩ : syracuseStep 262251 = 393377) B393377
theorem B262263 : Blo 259821 262263 := bstep (se 1 (by rfl) ⟨196697, by rfl⟩ : syracuseStep 262263 = 393395) B393395
theorem B295051 : Blo 259821 295051 := bstep (se 1 (by rfl) ⟨221288, by rfl⟩ : syracuseStep 295051 = 442577) B442577
theorem B262283 : Blo 259821 262283 := bstep (se 1 (by rfl) ⟨196712, by rfl⟩ : syracuseStep 262283 = 393425) B393425
theorem B557207 : Blo 259821 557207 := bstep (se 1 (by rfl) ⟨417905, by rfl⟩ : syracuseStep 557207 = 835811) B835811
theorem B262295 : Blo 259821 262295 := bstep (se 1 (by rfl) ⟨196721, by rfl⟩ : syracuseStep 262295 = 393443) B393443
theorem B262315 : Blo 259821 262315 := bstep (se 1 (by rfl) ⟨196736, by rfl⟩ : syracuseStep 262315 = 393473) B393473
theorem B590003 : Blo 259821 590003 := bstep (se 1 (by rfl) ⟨442502, by rfl⟩ : syracuseStep 590003 = 885005) B885005
theorem B262327 : Blo 259821 262327 := bstep (se 1 (by rfl) ⟨196745, by rfl⟩ : syracuseStep 262327 = 393491) B393491
theorem B393419 : Blo 259821 393419 := bstep (se 1 (by rfl) ⟨295064, by rfl⟩ : syracuseStep 393419 = 590129) B590129
theorem B262347 : Blo 259821 262347 := bstep (se 1 (by rfl) ⟨196760, by rfl⟩ : syracuseStep 262347 = 393521) B393521
theorem B590039 : Blo 259821 590039 := bstep (se 1 (by rfl) ⟨442529, by rfl⟩ : syracuseStep 590039 = 885059) B885059
theorem B393431 : Blo 259821 393431 := bstep (se 1 (by rfl) ⟨295073, by rfl⟩ : syracuseStep 393431 = 590147) B590147
theorem B262359 : Blo 259821 262359 := bstep (se 1 (by rfl) ⟨196769, by rfl⟩ : syracuseStep 262359 = 393539) B393539
theorem B262379 : Blo 259821 262379 := bstep (se 1 (by rfl) ⟨196784, by rfl⟩ : syracuseStep 262379 = 393569) B393569
theorem B295159 : Blo 259821 295159 := bstep (se 1 (by rfl) ⟨221369, by rfl⟩ : syracuseStep 295159 = 442739) B442739
theorem B262391 : Blo 259821 262391 := bstep (se 1 (by rfl) ⟨196793, by rfl⟩ : syracuseStep 262391 = 393587) B393587
theorem B262411 : Blo 259821 262411 := bstep (se 1 (by rfl) ⟨196808, by rfl⟩ : syracuseStep 262411 = 393617) B393617
theorem B262423 : Blo 259821 262423 := bstep (se 1 (by rfl) ⟨196817, by rfl⟩ : syracuseStep 262423 = 393635) B393635
theorem B393497 : Blo 259821 393497 := bstep (se 2 (by rfl) ⟨147561, by rfl⟩ : syracuseStep 393497 = 295123) B295123
theorem B262443 : Blo 259821 262443 := bstep (se 1 (by rfl) ⟨196832, by rfl⟩ : syracuseStep 262443 = 393665) B393665
theorem B262455 : Blo 259821 262455 := bstep (se 1 (by rfl) ⟨196841, by rfl⟩ : syracuseStep 262455 = 393683) B393683
theorem B262475 : Blo 259821 262475 := bstep (se 1 (by rfl) ⟨196856, by rfl⟩ : syracuseStep 262475 = 393713) B393713
theorem B262487 : Blo 259821 262487 := bstep (se 1 (by rfl) ⟨196865, by rfl⟩ : syracuseStep 262487 = 393731) B393731
theorem B262507 : Blo 259821 262507 := bstep (se 1 (by rfl) ⟨196880, by rfl⟩ : syracuseStep 262507 = 393761) B393761
theorem B17170805 : Blo 259821 17170805 := bstep (se 5 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 17170805 = 1609763) B1609763
theorem B262519 : Blo 259821 262519 := bstep (se 1 (by rfl) ⟨196889, by rfl⟩ : syracuseStep 262519 = 393779) B393779
theorem B590219 : Blo 259821 590219 := bstep (se 1 (by rfl) ⟨442664, by rfl⟩ : syracuseStep 590219 = 885329) B885329
theorem B393611 : Blo 259821 393611 := bstep (se 1 (by rfl) ⟨295208, by rfl⟩ : syracuseStep 393611 = 590417) B590417
theorem B262539 : Blo 259821 262539 := bstep (se 1 (by rfl) ⟨196904, by rfl⟩ : syracuseStep 262539 = 393809) B393809
theorem B393623 : Blo 259821 393623 := bstep (se 1 (by rfl) ⟨295217, by rfl⟩ : syracuseStep 393623 = 590435) B590435
theorem B262551 : Blo 259821 262551 := bstep (se 1 (by rfl) ⟨196913, by rfl⟩ : syracuseStep 262551 = 393827) B393827
theorem B295339 : Blo 259821 295339 := bstep (se 1 (by rfl) ⟨221504, by rfl⟩ : syracuseStep 295339 = 443009) B443009
theorem B262571 : Blo 259821 262571 := bstep (se 1 (by rfl) ⟨196928, by rfl⟩ : syracuseStep 262571 = 393857) B393857
theorem B262583 : Blo 259821 262583 := bstep (se 1 (by rfl) ⟨196937, by rfl⟩ : syracuseStep 262583 = 393875) B393875
theorem B590273 : Blo 259821 590273 := bstep (se 2 (by rfl) ⟨221352, by rfl⟩ : syracuseStep 590273 = 442705) B442705
theorem B262603 : Blo 259821 262603 := bstep (se 1 (by rfl) ⟨196952, by rfl⟩ : syracuseStep 262603 = 393905) B393905
theorem B262615 : Blo 259821 262615 := bstep (se 1 (by rfl) ⟨196961, by rfl⟩ : syracuseStep 262615 = 393923) B393923
theorem B393689 : Blo 259821 393689 := bstep (se 2 (by rfl) ⟨147633, by rfl⟩ : syracuseStep 393689 = 295267) B295267
theorem B262635 : Blo 259821 262635 := bstep (se 1 (by rfl) ⟨196976, by rfl⟩ : syracuseStep 262635 = 393953) B393953
theorem B262647 : Blo 259821 262647 := bstep (se 1 (by rfl) ⟨196985, by rfl⟩ : syracuseStep 262647 = 393971) B393971
theorem B262667 : Blo 259821 262667 := bstep (se 1 (by rfl) ⟨197000, by rfl⟩ : syracuseStep 262667 = 394001) B394001
theorem B295447 : Blo 259821 295447 := bstep (se 1 (by rfl) ⟨221585, by rfl⟩ : syracuseStep 295447 = 443171) B443171
theorem B262679 : Blo 259821 262679 := bstep (se 1 (by rfl) ⟨197009, by rfl⟩ : syracuseStep 262679 = 394019) B394019
theorem B262699 : Blo 259821 262699 := bstep (se 1 (by rfl) ⟨197024, by rfl⟩ : syracuseStep 262699 = 394049) B394049
theorem B262711 : Blo 259821 262711 := bstep (se 1 (by rfl) ⟨197033, by rfl⟩ : syracuseStep 262711 = 394067) B394067
theorem B393803 : Blo 259821 393803 := bstep (se 1 (by rfl) ⟨295352, by rfl⟩ : syracuseStep 393803 = 590705) B590705
theorem B262731 : Blo 259821 262731 := bstep (se 1 (by rfl) ⟨197048, by rfl⟩ : syracuseStep 262731 = 394097) B394097
theorem B393815 : Blo 259821 393815 := bstep (se 1 (by rfl) ⟨295361, by rfl⟩ : syracuseStep 393815 = 590723) B590723
theorem B262743 : Blo 259821 262743 := bstep (se 1 (by rfl) ⟨197057, by rfl⟩ : syracuseStep 262743 = 394115) B394115
theorem B262763 : Blo 259821 262763 := bstep (se 1 (by rfl) ⟨197072, by rfl⟩ : syracuseStep 262763 = 394145) B394145
theorem B262775 : Blo 259821 262775 := bstep (se 1 (by rfl) ⟨197081, by rfl⟩ : syracuseStep 262775 = 394163) B394163
theorem B262795 : Blo 259821 262795 := bstep (se 1 (by rfl) ⟨197096, by rfl⟩ : syracuseStep 262795 = 394193) B394193
theorem B262807 : Blo 259821 262807 := bstep (se 1 (by rfl) ⟨197105, by rfl⟩ : syracuseStep 262807 = 394211) B394211
theorem B590489 : Blo 259821 590489 := bstep (se 2 (by rfl) ⟨221433, by rfl⟩ : syracuseStep 590489 = 442867) B442867
theorem B393881 : Blo 259821 393881 := bstep (se 2 (by rfl) ⟨147705, by rfl⟩ : syracuseStep 393881 = 295411) B295411
theorem B262827 : Blo 259821 262827 := bstep (se 1 (by rfl) ⟨197120, by rfl⟩ : syracuseStep 262827 = 394241) B394241
theorem B262839 : Blo 259821 262839 := bstep (se 1 (by rfl) ⟨197129, by rfl⟩ : syracuseStep 262839 = 394259) B394259
theorem B295627 : Blo 259821 295627 := bstep (se 1 (by rfl) ⟨221720, by rfl⟩ : syracuseStep 295627 = 443441) B443441
theorem B262859 : Blo 259821 262859 := bstep (se 1 (by rfl) ⟨197144, by rfl⟩ : syracuseStep 262859 = 394289) B394289
theorem B262871 : Blo 259821 262871 := bstep (se 1 (by rfl) ⟨197153, by rfl⟩ : syracuseStep 262871 = 394307) B394307
theorem B1508057 : Blo 259821 1508057 := bstep (se 2 (by rfl) ⟨565521, by rfl⟩ : syracuseStep 1508057 = 1131043) B1131043
theorem B262891 : Blo 259821 262891 := bstep (se 1 (by rfl) ⟨197168, by rfl⟩ : syracuseStep 262891 = 394337) B394337
theorem B590579 : Blo 259821 590579 := bstep (se 1 (by rfl) ⟨442934, by rfl⟩ : syracuseStep 590579 = 885869) B885869
theorem B262903 : Blo 259821 262903 := bstep (se 1 (by rfl) ⟨197177, by rfl⟩ : syracuseStep 262903 = 394355) B394355
theorem B393995 : Blo 259821 393995 := bstep (se 1 (by rfl) ⟨295496, by rfl⟩ : syracuseStep 393995 = 590993) B590993
theorem B262923 : Blo 259821 262923 := bstep (se 1 (by rfl) ⟨197192, by rfl⟩ : syracuseStep 262923 = 394385) B394385
theorem B590615 : Blo 259821 590615 := bstep (se 1 (by rfl) ⟨442961, by rfl⟩ : syracuseStep 590615 = 885923) B885923
theorem B394007 : Blo 259821 394007 := bstep (se 1 (by rfl) ⟨295505, by rfl⟩ : syracuseStep 394007 = 591011) B591011
theorem B262935 : Blo 259821 262935 := bstep (se 1 (by rfl) ⟨197201, by rfl⟩ : syracuseStep 262935 = 394403) B394403
theorem B262955 : Blo 259821 262955 := bstep (se 1 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 262955 = 394433) B394433
theorem B295735 : Blo 259821 295735 := bstep (se 1 (by rfl) ⟨221801, by rfl⟩ : syracuseStep 295735 = 443603) B443603
theorem B262967 : Blo 259821 262967 := bstep (se 1 (by rfl) ⟨197225, by rfl⟩ : syracuseStep 262967 = 394451) B394451
theorem B262987 : Blo 259821 262987 := bstep (se 1 (by rfl) ⟨197240, by rfl⟩ : syracuseStep 262987 = 394481) B394481
theorem B262999 : Blo 259821 262999 := bstep (se 1 (by rfl) ⟨197249, by rfl⟩ : syracuseStep 262999 = 394499) B394499
theorem B394073 : Blo 259821 394073 := bstep (se 2 (by rfl) ⟨147777, by rfl⟩ : syracuseStep 394073 = 295555) B295555
theorem B263019 : Blo 259821 263019 := bstep (se 1 (by rfl) ⟨197264, by rfl⟩ : syracuseStep 263019 = 394529) B394529
theorem B263031 : Blo 259821 263031 := bstep (se 1 (by rfl) ⟨197273, by rfl⟩ : syracuseStep 263031 = 394547) B394547
theorem B263051 : Blo 259821 263051 := bstep (se 1 (by rfl) ⟨197288, by rfl⟩ : syracuseStep 263051 = 394577) B394577
theorem B263063 : Blo 259821 263063 := bstep (se 1 (by rfl) ⟨197297, by rfl⟩ : syracuseStep 263063 = 394595) B394595
theorem B263083 : Blo 259821 263083 := bstep (se 1 (by rfl) ⟨197312, by rfl⟩ : syracuseStep 263083 = 394625) B394625
theorem B263095 : Blo 259821 263095 := bstep (se 1 (by rfl) ⟨197321, by rfl⟩ : syracuseStep 263095 = 394643) B394643
theorem B885707 : Blo 259821 885707 := bstep (se 1 (by rfl) ⟨664280, by rfl⟩ : syracuseStep 885707 = 1328561) B1328561
theorem B590795 : Blo 259821 590795 := bstep (se 1 (by rfl) ⟨443096, by rfl⟩ : syracuseStep 590795 = 886193) B886193
theorem B394187 : Blo 259821 394187 := bstep (se 1 (by rfl) ⟨295640, by rfl⟩ : syracuseStep 394187 = 591281) B591281
theorem B263115 : Blo 259821 263115 := bstep (se 1 (by rfl) ⟨197336, by rfl⟩ : syracuseStep 263115 = 394673) B394673
theorem B394199 : Blo 259821 394199 := bstep (se 1 (by rfl) ⟨295649, by rfl⟩ : syracuseStep 394199 = 591299) B591299
theorem B263127 : Blo 259821 263127 := bstep (se 1 (by rfl) ⟨197345, by rfl⟩ : syracuseStep 263127 = 394691) B394691
theorem B295915 : Blo 259821 295915 := bstep (se 1 (by rfl) ⟨221936, by rfl⟩ : syracuseStep 295915 = 443873) B443873
theorem B263147 : Blo 259821 263147 := bstep (se 1 (by rfl) ⟨197360, by rfl⟩ : syracuseStep 263147 = 394721) B394721
theorem B263159 : Blo 259821 263159 := bstep (se 1 (by rfl) ⟨197369, by rfl⟩ : syracuseStep 263159 = 394739) B394739
theorem B590849 : Blo 259821 590849 := bstep (se 2 (by rfl) ⟨221568, by rfl⟩ : syracuseStep 590849 = 443137) B443137
theorem B263179 : Blo 259821 263179 := bstep (se 1 (by rfl) ⟨197384, by rfl⟩ : syracuseStep 263179 = 394769) B394769
theorem B1999889 : Blo 259821 1999889 := bstep (se 2 (by rfl) ⟨749958, by rfl⟩ : syracuseStep 1999889 = 1499917) B1499917
theorem B263191 : Blo 259821 263191 := bstep (se 1 (by rfl) ⟨197393, by rfl⟩ : syracuseStep 263191 = 394787) B394787
theorem B394265 : Blo 259821 394265 := bstep (se 2 (by rfl) ⟨147849, by rfl⟩ : syracuseStep 394265 = 295699) B295699
theorem B263211 : Blo 259821 263211 := bstep (se 1 (by rfl) ⟨197408, by rfl⟩ : syracuseStep 263211 = 394817) B394817
theorem B263223 : Blo 259821 263223 := bstep (se 1 (by rfl) ⟨197417, by rfl⟩ : syracuseStep 263223 = 394835) B394835
theorem B263243 : Blo 259821 263243 := bstep (se 1 (by rfl) ⟨197432, by rfl⟩ : syracuseStep 263243 = 394865) B394865
theorem B296023 : Blo 259821 296023 := bstep (se 1 (by rfl) ⟨222017, by rfl⟩ : syracuseStep 296023 = 444035) B444035
theorem B263255 : Blo 259821 263255 := bstep (se 1 (by rfl) ⟨197441, by rfl⟩ : syracuseStep 263255 = 394883) B394883
theorem B263275 : Blo 259821 263275 := bstep (se 1 (by rfl) ⟨197456, by rfl⟩ : syracuseStep 263275 = 394913) B394913
theorem B263287 : Blo 259821 263287 := bstep (se 1 (by rfl) ⟨197465, by rfl⟩ : syracuseStep 263287 = 394931) B394931
theorem B394379 : Blo 259821 394379 := bstep (se 1 (by rfl) ⟨295784, by rfl⟩ : syracuseStep 394379 = 591569) B591569
theorem B263307 : Blo 259821 263307 := bstep (se 1 (by rfl) ⟨197480, by rfl⟩ : syracuseStep 263307 = 394961) B394961
theorem B328855 : Blo 259821 328855 := bstep (se 1 (by rfl) ⟨246641, by rfl⟩ : syracuseStep 328855 = 493283) B493283
theorem B394391 : Blo 259821 394391 := bstep (se 1 (by rfl) ⟨295793, by rfl⟩ : syracuseStep 394391 = 591587) B591587
theorem B263319 : Blo 259821 263319 := bstep (se 1 (by rfl) ⟨197489, by rfl⟩ : syracuseStep 263319 = 394979) B394979
theorem B263339 : Blo 259821 263339 := bstep (se 1 (by rfl) ⟨197504, by rfl⟩ : syracuseStep 263339 = 395009) B395009
theorem B263351 : Blo 259821 263351 := bstep (se 1 (by rfl) ⟨197513, by rfl⟩ : syracuseStep 263351 = 395027) B395027
theorem B263371 : Blo 259821 263371 := bstep (se 1 (by rfl) ⟨197528, by rfl⟩ : syracuseStep 263371 = 395057) B395057
theorem B263383 : Blo 259821 263383 := bstep (se 1 (by rfl) ⟨197537, by rfl⟩ : syracuseStep 263383 = 395075) B395075
theorem B885977 : Blo 259821 885977 := bstep (se 2 (by rfl) ⟨332241, by rfl⟩ : syracuseStep 885977 = 664483) B664483
theorem B591065 : Blo 259821 591065 := bstep (se 2 (by rfl) ⟨221649, by rfl⟩ : syracuseStep 591065 = 443299) B443299
theorem B394457 : Blo 259821 394457 := bstep (se 2 (by rfl) ⟨147921, by rfl⟩ : syracuseStep 394457 = 295843) B295843
theorem B263403 : Blo 259821 263403 := bstep (se 1 (by rfl) ⟨197552, by rfl⟩ : syracuseStep 263403 = 395105) B395105
theorem B263415 : Blo 259821 263415 := bstep (se 1 (by rfl) ⟨197561, by rfl⟩ : syracuseStep 263415 = 395123) B395123
theorem B296203 : Blo 259821 296203 := bstep (se 1 (by rfl) ⟨222152, by rfl⟩ : syracuseStep 296203 = 444305) B444305
theorem B263435 : Blo 259821 263435 := bstep (se 1 (by rfl) ⟨197576, by rfl⟩ : syracuseStep 263435 = 395153) B395153
theorem B2131217 : Blo 259821 2131217 := bstep (se 2 (by rfl) ⟨799206, by rfl⟩ : syracuseStep 2131217 = 1598413) B1598413
theorem B263447 : Blo 259821 263447 := bstep (se 1 (by rfl) ⟨197585, by rfl⟩ : syracuseStep 263447 = 395171) B395171
theorem B263467 : Blo 259821 263467 := bstep (se 1 (by rfl) ⟨197600, by rfl⟩ : syracuseStep 263467 = 395201) B395201
theorem B591155 : Blo 259821 591155 := bstep (se 1 (by rfl) ⟨443366, by rfl⟩ : syracuseStep 591155 = 886733) B886733
theorem B263479 : Blo 259821 263479 := bstep (se 1 (by rfl) ⟨197609, by rfl⟩ : syracuseStep 263479 = 395219) B395219
theorem B394571 : Blo 259821 394571 := bstep (se 1 (by rfl) ⟨295928, by rfl⟩ : syracuseStep 394571 = 591857) B591857
theorem B263499 : Blo 259821 263499 := bstep (se 1 (by rfl) ⟨197624, by rfl⟩ : syracuseStep 263499 = 395249) B395249
theorem B591191 : Blo 259821 591191 := bstep (se 1 (by rfl) ⟨443393, by rfl⟩ : syracuseStep 591191 = 886787) B886787
theorem B394583 : Blo 259821 394583 := bstep (se 1 (by rfl) ⟨295937, by rfl⟩ : syracuseStep 394583 = 591875) B591875
theorem B263511 : Blo 259821 263511 := bstep (se 1 (by rfl) ⟨197633, by rfl⟩ : syracuseStep 263511 = 395267) B395267
theorem B263531 : Blo 259821 263531 := bstep (se 1 (by rfl) ⟨197648, by rfl⟩ : syracuseStep 263531 = 395297) B395297
theorem B296311 : Blo 259821 296311 := bstep (se 1 (by rfl) ⟨222233, by rfl⟩ : syracuseStep 296311 = 444467) B444467
theorem B263543 : Blo 259821 263543 := bstep (se 1 (by rfl) ⟨197657, by rfl⟩ : syracuseStep 263543 = 395315) B395315
theorem B263563 : Blo 259821 263563 := bstep (se 1 (by rfl) ⟨197672, by rfl⟩ : syracuseStep 263563 = 395345) B395345
theorem B263575 : Blo 259821 263575 := bstep (se 1 (by rfl) ⟨197681, by rfl⟩ : syracuseStep 263575 = 395363) B395363
theorem B394649 : Blo 259821 394649 := bstep (se 2 (by rfl) ⟨147993, by rfl⟩ : syracuseStep 394649 = 295987) B295987
theorem B263595 : Blo 259821 263595 := bstep (se 1 (by rfl) ⟨197696, by rfl⟩ : syracuseStep 263595 = 395393) B395393
theorem B263607 : Blo 259821 263607 := bstep (se 1 (by rfl) ⟨197705, by rfl⟩ : syracuseStep 263607 = 395411) B395411
theorem B263627 : Blo 259821 263627 := bstep (se 1 (by rfl) ⟨197720, by rfl⟩ : syracuseStep 263627 = 395441) B395441
theorem B263639 : Blo 259821 263639 := bstep (se 1 (by rfl) ⟨197729, by rfl⟩ : syracuseStep 263639 = 395459) B395459
theorem B263659 : Blo 259821 263659 := bstep (se 1 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 263659 = 395489) B395489
theorem B263671 : Blo 259821 263671 := bstep (se 1 (by rfl) ⟨197753, by rfl⟩ : syracuseStep 263671 = 395507) B395507
theorem B591371 : Blo 259821 591371 := bstep (se 1 (by rfl) ⟨443528, by rfl⟩ : syracuseStep 591371 = 887057) B887057
theorem B394763 : Blo 259821 394763 := bstep (se 1 (by rfl) ⟨296072, by rfl⟩ : syracuseStep 394763 = 592145) B592145
theorem B263691 : Blo 259821 263691 := bstep (se 1 (by rfl) ⟨197768, by rfl⟩ : syracuseStep 263691 = 395537) B395537
theorem B394775 : Blo 259821 394775 := bstep (se 1 (by rfl) ⟨296081, by rfl⟩ : syracuseStep 394775 = 592163) B592163
theorem B263703 : Blo 259821 263703 := bstep (se 1 (by rfl) ⟨197777, by rfl⟩ : syracuseStep 263703 = 395555) B395555
theorem B296491 : Blo 259821 296491 := bstep (se 1 (by rfl) ⟨222368, by rfl⟩ : syracuseStep 296491 = 444737) B444737
theorem B263723 : Blo 259821 263723 := bstep (se 1 (by rfl) ⟨197792, by rfl⟩ : syracuseStep 263723 = 395585) B395585
theorem B1410605 : Blo 259821 1410605 := bstep (se 3 (by rfl) ⟨264488, by rfl⟩ : syracuseStep 1410605 = 528977) B528977
theorem B263735 : Blo 259821 263735 := bstep (se 1 (by rfl) ⟨197801, by rfl⟩ : syracuseStep 263735 = 395603) B395603
theorem B591425 : Blo 259821 591425 := bstep (se 2 (by rfl) ⟨221784, by rfl⟩ : syracuseStep 591425 = 443569) B443569
theorem B263755 : Blo 259821 263755 := bstep (se 1 (by rfl) ⟨197816, by rfl⟩ : syracuseStep 263755 = 395633) B395633
theorem B263767 : Blo 259821 263767 := bstep (se 1 (by rfl) ⟨197825, by rfl⟩ : syracuseStep 263767 = 395651) B395651
theorem B394841 : Blo 259821 394841 := bstep (se 2 (by rfl) ⟨148065, by rfl⟩ : syracuseStep 394841 = 296131) B296131
theorem B263787 : Blo 259821 263787 := bstep (se 1 (by rfl) ⟨197840, by rfl⟩ : syracuseStep 263787 = 395681) B395681
theorem B263799 : Blo 259821 263799 := bstep (se 1 (by rfl) ⟨197849, by rfl⟩ : syracuseStep 263799 = 395699) B395699
theorem B263819 : Blo 259821 263819 := bstep (se 1 (by rfl) ⟨197864, by rfl⟩ : syracuseStep 263819 = 395729) B395729
theorem B296599 : Blo 259821 296599 := bstep (se 1 (by rfl) ⟨222449, by rfl⟩ : syracuseStep 296599 = 444899) B444899
theorem B394955 : Blo 259821 394955 := bstep (se 1 (by rfl) ⟨296216, by rfl⟩ : syracuseStep 394955 = 592433) B592433
theorem B394967 : Blo 259821 394967 := bstep (se 1 (by rfl) ⟨296225, by rfl⟩ : syracuseStep 394967 = 592451) B592451
theorem B591641 : Blo 259821 591641 := bstep (se 2 (by rfl) ⟨221865, by rfl⟩ : syracuseStep 591641 = 443731) B443731
theorem B395033 : Blo 259821 395033 := bstep (se 2 (by rfl) ⟨148137, by rfl⟩ : syracuseStep 395033 = 296275) B296275
theorem B2098979 : Blo 259821 2098979 := bstep (se 1 (by rfl) ⟨1574234, by rfl⟩ : syracuseStep 2098979 = 3148469) B3148469
theorem B296779 : Blo 259821 296779 := bstep (se 1 (by rfl) ⟨222584, by rfl⟩ : syracuseStep 296779 = 445169) B445169
theorem B493427 : Blo 259821 493427 := bstep (se 1 (by rfl) ⟨370070, by rfl⟩ : syracuseStep 493427 = 740141) B740141
theorem B591731 : Blo 259821 591731 := bstep (se 1 (by rfl) ⟨443798, by rfl⟩ : syracuseStep 591731 = 887597) B887597
theorem B395147 : Blo 259821 395147 := bstep (se 1 (by rfl) ⟨296360, by rfl⟩ : syracuseStep 395147 = 592721) B592721
theorem B886679 : Blo 259821 886679 := bstep (se 1 (by rfl) ⟨665009, by rfl⟩ : syracuseStep 886679 = 1330019) B1330019
theorem B591767 : Blo 259821 591767 := bstep (se 1 (by rfl) ⟨443825, by rfl⟩ : syracuseStep 591767 = 887651) B887651
theorem B493465 : Blo 259821 493465 := bstep (se 2 (by rfl) ⟨185049, by rfl⟩ : syracuseStep 493465 = 370099) B370099
theorem B559001 : Blo 259821 559001 := bstep (se 2 (by rfl) ⟨209625, by rfl⟩ : syracuseStep 559001 = 419251) B419251
theorem B395159 : Blo 259821 395159 := bstep (se 1 (by rfl) ⟨296369, by rfl⟩ : syracuseStep 395159 = 592739) B592739
theorem B2230193 : Blo 259821 2230193 := bstep (se 2 (by rfl) ⟨836322, by rfl⟩ : syracuseStep 2230193 = 1672645) B1672645
theorem B395225 : Blo 259821 395225 := bstep (se 2 (by rfl) ⟨148209, by rfl⟩ : syracuseStep 395225 = 296419) B296419
theorem B1673261 : Blo 259821 1673261 := bstep (se 3 (by rfl) ⟨313736, by rfl⟩ : syracuseStep 1673261 = 627473) B627473
theorem B591947 : Blo 259821 591947 := bstep (se 1 (by rfl) ⟨443960, by rfl⟩ : syracuseStep 591947 = 887921) B887921
theorem B395339 : Blo 259821 395339 := bstep (se 1 (by rfl) ⟨296504, by rfl⟩ : syracuseStep 395339 = 593009) B593009
theorem B395351 : Blo 259821 395351 := bstep (se 1 (by rfl) ⟨296513, by rfl⟩ : syracuseStep 395351 = 593027) B593027
theorem B592001 : Blo 259821 592001 := bstep (se 2 (by rfl) ⟨222000, by rfl⟩ : syracuseStep 592001 = 444001) B444001
theorem B1050769 : Blo 259821 1050769 := bstep (se 2 (by rfl) ⟨394038, by rfl⟩ : syracuseStep 1050769 = 788077) B788077
theorem B395417 : Blo 259821 395417 := bstep (se 2 (by rfl) ⟨148281, by rfl⟩ : syracuseStep 395417 = 296563) B296563
theorem B395531 : Blo 259821 395531 := bstep (se 1 (by rfl) ⟨296648, by rfl⟩ : syracuseStep 395531 = 593297) B593297
theorem B395543 : Blo 259821 395543 := bstep (se 1 (by rfl) ⟨296657, by rfl⟩ : syracuseStep 395543 = 593315) B593315
theorem B493913 : Blo 259821 493913 := bstep (se 2 (by rfl) ⟨185217, by rfl⟩ : syracuseStep 493913 = 370435) B370435
theorem B592217 : Blo 259821 592217 := bstep (se 2 (by rfl) ⟨222081, by rfl⟩ : syracuseStep 592217 = 444163) B444163
theorem B395609 : Blo 259821 395609 := bstep (se 2 (by rfl) ⟨148353, by rfl⟩ : syracuseStep 395609 = 296707) B296707
theorem B8063381 : Blo 259821 8063381 := bstep (se 6 (by rfl) ⟨188985, by rfl⟩ : syracuseStep 8063381 = 377971) B377971
theorem B887219 : Blo 259821 887219 := bstep (se 1 (by rfl) ⟨665414, by rfl⟩ : syracuseStep 887219 = 1330829) B1330829
theorem B592307 : Blo 259821 592307 := bstep (se 1 (by rfl) ⟨444230, by rfl⟩ : syracuseStep 592307 = 888461) B888461
theorem B395723 : Blo 259821 395723 := bstep (se 1 (by rfl) ⟨296792, by rfl⟩ : syracuseStep 395723 = 593585) B593585
theorem B592343 : Blo 259821 592343 := bstep (se 1 (by rfl) ⟨444257, by rfl⟩ : syracuseStep 592343 = 888515) B888515
theorem B559667 : Blo 259821 559667 := bstep (se 1 (by rfl) ⟨419750, by rfl⟩ : syracuseStep 559667 = 839501) B839501
theorem B1116737 : Blo 259821 1116737 := bstep (se 2 (by rfl) ⟨418776, by rfl⟩ : syracuseStep 1116737 = 837553) B837553
theorem B592523 : Blo 259821 592523 := bstep (se 1 (by rfl) ⟨444392, by rfl⟩ : syracuseStep 592523 = 888785) B888785
theorem B526999 : Blo 259821 526999 := bstep (se 1 (by rfl) ⟨395249, by rfl⟩ : syracuseStep 526999 = 790499) B790499
theorem B887489 : Blo 259821 887489 := bstep (se 2 (by rfl) ⟨332808, by rfl⟩ : syracuseStep 887489 = 665617) B665617
theorem B592577 : Blo 259821 592577 := bstep (se 2 (by rfl) ⟨222216, by rfl⟩ : syracuseStep 592577 = 444433) B444433
theorem B297751 : Blo 259821 297751 := bstep (se 1 (by rfl) ⟨223313, by rfl⟩ : syracuseStep 297751 = 446627) B446627
theorem B4492097 : Blo 259821 4492097 := bstep (se 2 (by rfl) ⟨1684536, by rfl⟩ : syracuseStep 4492097 = 3369073) B3369073
theorem B330571 : Blo 259821 330571 := bstep (se 1 (by rfl) ⟨247928, by rfl⟩ : syracuseStep 330571 = 495857) B495857
theorem B658327 : Blo 259821 658327 := bstep (se 1 (by rfl) ⟨493745, by rfl⟩ : syracuseStep 658327 = 987491) B987491
theorem B1411991 : Blo 259821 1411991 := bstep (se 1 (by rfl) ⟨1058993, by rfl⟩ : syracuseStep 1411991 = 2117987) B2117987
theorem B592793 : Blo 259821 592793 := bstep (se 2 (by rfl) ⟨222297, by rfl⟩ : syracuseStep 592793 = 444595) B444595
theorem B592883 : Blo 259821 592883 := bstep (se 1 (by rfl) ⟨444662, by rfl⟩ : syracuseStep 592883 = 889325) B889325
theorem B592919 : Blo 259821 592919 := bstep (se 1 (by rfl) ⟨444689, by rfl⟩ : syracuseStep 592919 = 889379) B889379
theorem B494657 : Blo 259821 494657 := bstep (se 2 (by rfl) ⟨185496, by rfl⟩ : syracuseStep 494657 = 370993) B370993
theorem B2165825 : Blo 259821 2165825 := bstep (se 2 (by rfl) ⟨812184, by rfl⟩ : syracuseStep 2165825 = 1624369) B1624369
theorem B593099 : Blo 259821 593099 := bstep (se 1 (by rfl) ⟨444824, by rfl⟩ : syracuseStep 593099 = 889649) B889649
theorem B888029 : Blo 259821 888029 := bstep (se 3 (by rfl) ⟨166505, by rfl⟩ : syracuseStep 888029 = 333011) B333011
theorem B593153 : Blo 259821 593153 := bstep (se 2 (by rfl) ⟨222432, by rfl⟩ : syracuseStep 593153 = 444865) B444865
theorem B658763 : Blo 259821 658763 := bstep (se 1 (by rfl) ⟨494072, by rfl⟩ : syracuseStep 658763 = 988145) B988145
theorem B494923 : Blo 259821 494923 := bstep (se 1 (by rfl) ⟨371192, by rfl⟩ : syracuseStep 494923 = 742385) B742385
theorem B986519 : Blo 259821 986519 := bstep (se 1 (by rfl) ⟨739889, by rfl⟩ : syracuseStep 986519 = 1479779) B1479779
theorem B527809 : Blo 259821 527809 := bstep (se 2 (by rfl) ⟨197928, by rfl⟩ : syracuseStep 527809 = 395857) B395857
theorem B593369 : Blo 259821 593369 := bstep (se 2 (by rfl) ⟨222513, by rfl⟩ : syracuseStep 593369 = 445027) B445027
theorem B593459 : Blo 259821 593459 := bstep (se 1 (by rfl) ⟨445094, by rfl⟩ : syracuseStep 593459 = 890189) B890189
theorem B593495 : Blo 259821 593495 := bstep (se 1 (by rfl) ⟨445121, by rfl⟩ : syracuseStep 593495 = 890243) B890243
theorem B659137 : Blo 259821 659137 := bstep (se 2 (by rfl) ⟨247176, by rfl⟩ : syracuseStep 659137 = 494353) B494353
theorem B495371 : Blo 259821 495371 := bstep (se 1 (by rfl) ⟨371528, by rfl⟩ : syracuseStep 495371 = 743057) B743057
theorem B331543 : Blo 259821 331543 := bstep (se 1 (by rfl) ⟨248657, by rfl⟩ : syracuseStep 331543 = 497315) B497315
theorem B1412939 : Blo 259821 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B495553 : Blo 259821 495553 := bstep (se 2 (by rfl) ⟨185832, by rfl⟩ : syracuseStep 495553 = 371665) B371665
theorem B561163 : Blo 259821 561163 := bstep (se 1 (by rfl) ⟨420872, by rfl⟩ : syracuseStep 561163 = 841745) B841745
theorem B1118225 : Blo 259821 1118225 := bstep (se 2 (by rfl) ⟨419334, by rfl⟩ : syracuseStep 1118225 = 838669) B838669
theorem B2691089 : Blo 259821 2691089 := bstep (se 2 (by rfl) ⟨1009158, by rfl⟩ : syracuseStep 2691089 = 2018317) B2018317
theorem B987187 : Blo 259821 987187 := bstep (se 1 (by rfl) ⟨740390, by rfl⟩ : syracuseStep 987187 = 1480781) B1480781
theorem B659735 : Blo 259821 659735 := bstep (se 1 (by rfl) ⟨494801, by rfl⟩ : syracuseStep 659735 = 989603) B989603
theorem B495895 : Blo 259821 495895 := bstep (se 1 (by rfl) ⟨371921, by rfl⟩ : syracuseStep 495895 = 743843) B743843
theorem B889163 : Blo 259821 889163 := bstep (se 1 (by rfl) ⟨666872, by rfl⟩ : syracuseStep 889163 = 1333745) B1333745
theorem B397657 : Blo 259821 397657 := bstep (se 2 (by rfl) ⟨149121, by rfl⟩ : syracuseStep 397657 = 298243) B298243
theorem B496115 : Blo 259821 496115 := bstep (se 1 (by rfl) ⟨372086, by rfl⟩ : syracuseStep 496115 = 744173) B744173
theorem B266743 : Blo 259821 266743 := bstep (se 1 (by rfl) ⟨200057, by rfl⟩ : syracuseStep 266743 = 400115) B400115
theorem B397847 : Blo 259821 397847 := bstep (se 1 (by rfl) ⟨298385, by rfl⟩ : syracuseStep 397847 = 596771) B596771
theorem B332363 : Blo 259821 332363 := bstep (se 1 (by rfl) ⟨249272, by rfl⟩ : syracuseStep 332363 = 498545) B498545
theorem B889433 : Blo 259821 889433 := bstep (se 2 (by rfl) ⟨333537, by rfl⟩ : syracuseStep 889433 = 667075) B667075
theorem B594625 : Blo 259821 594625 := bstep (se 2 (by rfl) ⟨222984, by rfl⟩ : syracuseStep 594625 = 445969) B445969
theorem B496343 : Blo 259821 496343 := bstep (se 1 (by rfl) ⟨372257, by rfl⟩ : syracuseStep 496343 = 744515) B744515
theorem B1315601 : Blo 259821 1315601 := bstep (se 2 (by rfl) ⟨493350, by rfl⟩ : syracuseStep 1315601 = 986701) B986701
theorem B1315763 : Blo 259821 1315763 := bstep (se 1 (by rfl) ⟨986822, by rfl⟩ : syracuseStep 1315763 = 1973645) B1973645
theorem B496601 : Blo 259821 496601 := bstep (se 2 (by rfl) ⟨186225, by rfl⟩ : syracuseStep 496601 = 372451) B372451
theorem B1119197 : Blo 259821 1119197 := bstep (se 3 (by rfl) ⟨209849, by rfl⟩ : syracuseStep 1119197 = 419699) B419699
theorem B660545 : Blo 259821 660545 := bstep (se 2 (by rfl) ⟨247704, by rfl⟩ : syracuseStep 660545 = 495409) B495409
theorem B431191 : Blo 259821 431191 := bstep (se 1 (by rfl) ⟨323393, by rfl⟩ : syracuseStep 431191 = 646787) B646787
theorem B529625 : Blo 259821 529625 := bstep (se 2 (by rfl) ⟨198609, by rfl⟩ : syracuseStep 529625 = 397219) B397219
theorem B562393 : Blo 259821 562393 := bstep (se 2 (by rfl) ⟨210897, by rfl⟩ : syracuseStep 562393 = 421795) B421795
theorem B333067 : Blo 259821 333067 := bstep (se 1 (by rfl) ⟨249800, by rfl⟩ : syracuseStep 333067 = 499601) B499601
theorem B988433 : Blo 259821 988433 := bstep (se 2 (by rfl) ⟨370662, by rfl⟩ : syracuseStep 988433 = 741325) B741325
theorem B890135 : Blo 259821 890135 := bstep (se 1 (by rfl) ⟨667601, by rfl⟩ : syracuseStep 890135 = 1335203) B1335203
theorem B1676645 : Blo 259821 1676645 := bstep (se 4 (by rfl) ⟨157185, by rfl⟩ : syracuseStep 1676645 = 314371) B314371
theorem B497011 : Blo 259821 497011 := bstep (se 1 (by rfl) ⟨372758, by rfl⟩ : syracuseStep 497011 = 745517) B745517
theorem B2987441 : Blo 259821 2987441 := bstep (se 2 (by rfl) ⟨1120290, by rfl⟩ : syracuseStep 2987441 = 2240581) B2240581
theorem B2233817 : Blo 259821 2233817 := bstep (se 2 (by rfl) ⟨837681, by rfl⟩ : syracuseStep 2233817 = 1675363) B1675363
theorem B1054225 : Blo 259821 1054225 := bstep (se 2 (by rfl) ⟨395334, by rfl⟩ : syracuseStep 1054225 = 790669) B790669
theorem B333335 : Blo 259821 333335 := bstep (se 1 (by rfl) ⟨250001, by rfl⟩ : syracuseStep 333335 = 500003) B500003
theorem B661081 : Blo 259821 661081 := bstep (se 2 (by rfl) ⟨247905, by rfl⟩ : syracuseStep 661081 = 495811) B495811
theorem B1709869 : Blo 259821 1709869 := bstep (se 3 (by rfl) ⟨320600, by rfl⟩ : syracuseStep 1709869 = 641201) B641201
theorem B497497 : Blo 259821 497497 := bstep (se 2 (by rfl) ⟨186561, by rfl⟩ : syracuseStep 497497 = 373123) B373123
theorem B11409329 : Blo 259821 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B989131 : Blo 259821 989131 := bstep (se 1 (by rfl) ⟨741848, by rfl⟩ : syracuseStep 989131 = 1483697) B1483697
theorem B989405 : Blo 259821 989405 := bstep (se 3 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 989405 = 371027) B371027
theorem B498059 : Blo 259821 498059 := bstep (se 1 (by rfl) ⟨373544, by rfl⟩ : syracuseStep 498059 = 747089) B747089
theorem B530891 : Blo 259821 530891 := bstep (se 1 (by rfl) ⟨398168, by rfl⟩ : syracuseStep 530891 = 796337) B796337
theorem B498241 : Blo 259821 498241 := bstep (se 2 (by rfl) ⟨186840, by rfl⟩ : syracuseStep 498241 = 373681) B373681
theorem B662195 : Blo 259821 662195 := bstep (se 1 (by rfl) ⟨496646, by rfl⟩ : syracuseStep 662195 = 993293) B993293
theorem B1055425 : Blo 259821 1055425 := bstep (se 2 (by rfl) ⟨395784, by rfl⟩ : syracuseStep 1055425 = 791569) B791569
theorem B1481489 : Blo 259821 1481489 := bstep (se 2 (by rfl) ⟨555558, by rfl⟩ : syracuseStep 1481489 = 1111117) B1111117
theorem B1317707 : Blo 259821 1317707 := bstep (se 1 (by rfl) ⟨988280, by rfl⟩ : syracuseStep 1317707 = 1976561) B1976561
theorem B990103 : Blo 259821 990103 := bstep (se 1 (by rfl) ⟨742577, by rfl⟩ : syracuseStep 990103 = 1485155) B1485155
theorem B662489 : Blo 259821 662489 := bstep (se 2 (by rfl) ⟨248433, by rfl⟩ : syracuseStep 662489 = 496867) B496867
theorem B629849 : Blo 259821 629849 := bstep (se 2 (by rfl) ⟨236193, by rfl⟩ : syracuseStep 629849 = 472387) B472387
theorem B498955 : Blo 259821 498955 := bstep (se 1 (by rfl) ⟨374216, by rfl⟩ : syracuseStep 498955 = 748433) B748433
theorem B499031 : Blo 259821 499031 := bstep (se 1 (by rfl) ⟨374273, by rfl⟩ : syracuseStep 499031 = 748547) B748547
theorem B630233 : Blo 259821 630233 := bstep (se 2 (by rfl) ⟨236337, by rfl⟩ : syracuseStep 630233 = 472675) B472675
theorem B531929 : Blo 259821 531929 := bstep (se 2 (by rfl) ⟨199473, by rfl⟩ : syracuseStep 531929 = 398947) B398947
theorem B1121795 : Blo 259821 1121795 := bstep (se 1 (by rfl) ⟨841346, by rfl⟩ : syracuseStep 1121795 = 1682693) B1682693
theorem B1089089 : Blo 259821 1089089 := bstep (se 2 (by rfl) ⟨408408, by rfl⟩ : syracuseStep 1089089 = 816817) B816817
theorem B990893 : Blo 259821 990893 := bstep (se 3 (by rfl) ⟨185792, by rfl⟩ : syracuseStep 990893 = 371585) B371585
theorem B2826049 : Blo 259821 2826049 := bstep (se 2 (by rfl) ⟨1059768, by rfl⟩ : syracuseStep 2826049 = 2119537) B2119537
theorem B1122137 : Blo 259821 1122137 := bstep (se 2 (by rfl) ⟨420801, by rfl⟩ : syracuseStep 1122137 = 841603) B841603
theorem B499699 : Blo 259821 499699 := bstep (se 1 (by rfl) ⟨374774, by rfl⟩ : syracuseStep 499699 = 749549) B749549
theorem B2236481 : Blo 259821 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B499927 : Blo 259821 499927 := bstep (se 1 (by rfl) ⟨374945, by rfl⟩ : syracuseStep 499927 = 749891) B749891
theorem B500033 : Blo 259821 500033 := bstep (se 2 (by rfl) ⟨187512, by rfl⟩ : syracuseStep 500033 = 375025) B375025
theorem B1057175 : Blo 259821 1057175 := bstep (se 1 (by rfl) ⟨792881, by rfl⟩ : syracuseStep 1057175 = 1585763) B1585763
theorem B500185 : Blo 259821 500185 := bstep (se 2 (by rfl) ⟨187569, by rfl⟩ : syracuseStep 500185 = 375139) B375139
theorem B532993 : Blo 259821 532993 := bstep (se 2 (by rfl) ⟨199872, by rfl⟩ : syracuseStep 532993 = 399745) B399745
theorem B1319489 : Blo 259821 1319489 := bstep (se 2 (by rfl) ⟨494808, by rfl⟩ : syracuseStep 1319489 = 989617) B989617
theorem B664139 : Blo 259821 664139 := bstep (se 1 (by rfl) ⟨498104, by rfl⟩ : syracuseStep 664139 = 996209) B996209
theorem B598603 : Blo 259821 598603 := bstep (se 1 (by rfl) ⟨448952, by rfl⟩ : syracuseStep 598603 = 897905) B897905
theorem B3711581 : Blo 259821 3711581 := bstep (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) B1391843
theorem B992321 : Blo 259821 992321 := bstep (se 2 (by rfl) ⟨372120, by rfl⟩ : syracuseStep 992321 = 744241) B744241
theorem B632087 : Blo 259821 632087 := bstep (se 1 (by rfl) ⟨474065, by rfl⟩ : syracuseStep 632087 = 948131) B948131
theorem B665111 : Blo 259821 665111 := bstep (se 1 (by rfl) ⟨498833, by rfl⟩ : syracuseStep 665111 = 997667) B997667
theorem B4531781 : Blo 259821 4531781 := bstep (se 4 (by rfl) ⟨424854, by rfl⟩ : syracuseStep 4531781 = 849709) B849709
theorem B1189451 : Blo 259821 1189451 := bstep (se 1 (by rfl) ⟨892088, by rfl⟩ : syracuseStep 1189451 = 1784177) B1784177
theorem B370327 : Blo 259821 370327 := bstep (se 1 (by rfl) ⟨277745, by rfl⟩ : syracuseStep 370327 = 555491) B555491
theorem B4171565 : Blo 259821 4171565 := bstep (se 3 (by rfl) ⟨782168, by rfl⟩ : syracuseStep 4171565 = 1564337) B1564337
theorem B534361 : Blo 259821 534361 := bstep (se 2 (by rfl) ⟨200385, by rfl⟩ : syracuseStep 534361 = 400771) B400771
theorem B1189835 : Blo 259821 1189835 := bstep (se 1 (by rfl) ⟨892376, by rfl⟩ : syracuseStep 1189835 = 1784753) B1784753
theorem B665779 : Blo 259821 665779 := bstep (se 1 (by rfl) ⟨499334, by rfl⟩ : syracuseStep 665779 = 998669) B998669
theorem B665921 : Blo 259821 665921 := bstep (se 2 (by rfl) ⟨249720, by rfl⟩ : syracuseStep 665921 = 499441) B499441
theorem B1321433 : Blo 259821 1321433 := bstep (se 2 (by rfl) ⟨495537, by rfl⟩ : syracuseStep 1321433 = 991075) B991075
theorem B993809 : Blo 259821 993809 := bstep (se 2 (by rfl) ⟨372678, by rfl⟩ : syracuseStep 993809 = 745357) B745357
theorem B797249 : Blo 259821 797249 := bstep (se 2 (by rfl) ⟨298968, by rfl⟩ : syracuseStep 797249 = 597937) B597937
theorem B633433 : Blo 259821 633433 := bstep (se 2 (by rfl) ⟨237537, by rfl⟩ : syracuseStep 633433 = 475075) B475075
theorem B404183 : Blo 259821 404183 := bstep (se 1 (by rfl) ⟨303137, by rfl⟩ : syracuseStep 404183 = 606275) B606275
theorem B600791 : Blo 259821 600791 := bstep (se 1 (by rfl) ⟨450593, by rfl⟩ : syracuseStep 600791 = 901187) B901187
theorem B961303 : Blo 259821 961303 := bstep (se 1 (by rfl) ⟨720977, by rfl⟩ : syracuseStep 961303 = 1441955) B1441955
theorem B994265 : Blo 259821 994265 := bstep (se 2 (by rfl) ⟨372849, by rfl⟩ : syracuseStep 994265 = 745699) B745699
theorem B1125521 : Blo 259821 1125521 := bstep (se 2 (by rfl) ⟨422070, by rfl⟩ : syracuseStep 1125521 = 844141) B844141
theorem B994477 : Blo 259821 994477 := bstep (se 3 (by rfl) ⟨186464, by rfl⟩ : syracuseStep 994477 = 372929) B372929
theorem B994781 : Blo 259821 994781 := bstep (se 3 (by rfl) ⟨186521, by rfl⟩ : syracuseStep 994781 = 373043) B373043
theorem B503347 : Blo 259821 503347 := bstep (se 1 (by rfl) ⟨377510, by rfl⟩ : syracuseStep 503347 = 755021) B755021
theorem B667187 : Blo 259821 667187 := bstep (se 1 (by rfl) ⟨500390, by rfl⟩ : syracuseStep 667187 = 1000781) B1000781
theorem B1584791 : Blo 259821 1584791 := bstep (se 1 (by rfl) ⟨1188593, by rfl⟩ : syracuseStep 1584791 = 2377187) B2377187
theorem B372377 : Blo 259821 372377 := bstep (se 2 (by rfl) ⟨139641, by rfl⟩ : syracuseStep 372377 = 279283) B279283
theorem B2961197 : Blo 259821 2961197 := bstep (se 3 (by rfl) ⟨555224, by rfl⟩ : syracuseStep 2961197 = 1110449) B1110449
theorem B1126237 : Blo 259821 1126237 := bstep (se 3 (by rfl) ⟨211169, by rfl⟩ : syracuseStep 1126237 = 422339) B422339
theorem B1323053 : Blo 259821 1323053 := bstep (se 3 (by rfl) ⟨248072, by rfl⟩ : syracuseStep 1323053 = 496145) B496145
theorem B667723 : Blo 259821 667723 := bstep (se 1 (by rfl) ⟨500792, by rfl⟩ : syracuseStep 667723 = 1001585) B1001585
theorem B373015 : Blo 259821 373015 := bstep (se 1 (by rfl) ⟨279761, by rfl⟩ : syracuseStep 373015 = 559523) B559523
theorem B668083 : Blo 259821 668083 := bstep (se 1 (by rfl) ⟨501062, by rfl⟩ : syracuseStep 668083 = 1002125) B1002125
theorem B438743 : Blo 259821 438743 := bstep (se 1 (by rfl) ⟨329057, by rfl⟩ : syracuseStep 438743 = 658115) B658115
theorem B1487321 : Blo 259821 1487321 := bstep (se 2 (by rfl) ⟨557745, by rfl⟩ : syracuseStep 1487321 = 1115491) B1115491
theorem B438871 : Blo 259821 438871 := bstep (se 1 (by rfl) ⟨329153, by rfl⟩ : syracuseStep 438871 = 658307) B658307
theorem B2405213 : Blo 259821 2405213 := bstep (se 3 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 2405213 = 901955) B901955
theorem B373835 : Blo 259821 373835 := bstep (se 1 (by rfl) ⟨280376, by rfl⟩ : syracuseStep 373835 = 560753) B560753
theorem B2307203 : Blo 259821 2307203 := bstep (se 1 (by rfl) ⟨1730402, by rfl⟩ : syracuseStep 2307203 = 3460805) B3460805
theorem B1881265 : Blo 259821 1881265 := bstep (se 2 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 1881265 = 1410949) B1410949
theorem B439499 : Blo 259821 439499 := bstep (se 1 (by rfl) ⟨329624, by rfl⟩ : syracuseStep 439499 = 659249) B659249
theorem B439627 : Blo 259821 439627 := bstep (se 1 (by rfl) ⟨329720, by rfl⟩ : syracuseStep 439627 = 659441) B659441
theorem B439769 : Blo 259821 439769 := bstep (se 2 (by rfl) ⟨164913, by rfl⟩ : syracuseStep 439769 = 329827) B329827
theorem B865753 : Blo 259821 865753 := bstep (se 2 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 865753 = 649315) B649315
theorem B439897 : Blo 259821 439897 := bstep (se 2 (by rfl) ⟨164961, by rfl⟩ : syracuseStep 439897 = 329923) B329923
theorem B6731585 : Blo 259821 6731585 := bstep (se 2 (by rfl) ⟨2524344, by rfl⟩ : syracuseStep 6731585 = 5048689) B5048689
theorem B997379 : Blo 259821 997379 := bstep (se 1 (by rfl) ⟨748034, by rfl⟩ : syracuseStep 997379 = 1496069) B1496069
theorem B2242565 : Blo 259821 2242565 := bstep (se 4 (by rfl) ⟨210240, by rfl⟩ : syracuseStep 2242565 = 420481) B420481
theorem B997393 : Blo 259821 997393 := bstep (se 2 (by rfl) ⟨374022, by rfl⟩ : syracuseStep 997393 = 748045) B748045
theorem B899095 : Blo 259821 899095 := bstep (se 1 (by rfl) ⟨674321, by rfl⟩ : syracuseStep 899095 = 1348643) B1348643
theorem B374809 : Blo 259821 374809 := bstep (se 2 (by rfl) ⟨140553, by rfl⟩ : syracuseStep 374809 = 281107) B281107
theorem B4995107 : Blo 259821 4995107 := bstep (se 1 (by rfl) ⟨3746330, by rfl⟩ : syracuseStep 4995107 = 7492661) B7492661
theorem B440471 : Blo 259821 440471 := bstep (se 1 (by rfl) ⟨330353, by rfl⟩ : syracuseStep 440471 = 660707) B660707
theorem B440599 : Blo 259821 440599 := bstep (se 1 (by rfl) ⟨330449, by rfl⟩ : syracuseStep 440599 = 660899) B660899
theorem B997697 : Blo 259821 997697 := bstep (se 2 (by rfl) ⟨374136, by rfl⟩ : syracuseStep 997697 = 748273) B748273
theorem B375385 : Blo 259821 375385 := bstep (se 2 (by rfl) ⟨140769, by rfl⟩ : syracuseStep 375385 = 281539) B281539
theorem B801373 : Blo 259821 801373 := bstep (se 3 (by rfl) ⟨150257, by rfl⟩ : syracuseStep 801373 = 300515) B300515
theorem B441227 : Blo 259821 441227 := bstep (se 1 (by rfl) ⟨330920, by rfl⟩ : syracuseStep 441227 = 661841) B661841
theorem B474007 : Blo 259821 474007 := bstep (se 1 (by rfl) ⟨355505, by rfl⟩ : syracuseStep 474007 = 711011) B711011
theorem B6339545 : Blo 259821 6339545 := bstep (se 2 (by rfl) ⟨2377329, by rfl⟩ : syracuseStep 6339545 = 4754659) B4754659
theorem B998365 : Blo 259821 998365 := bstep (se 3 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 998365 = 374387) B374387
theorem B441355 : Blo 259821 441355 := bstep (se 1 (by rfl) ⟨331016, by rfl⟩ : syracuseStep 441355 = 662033) B662033
theorem B3750947 : Blo 259821 3750947 := bstep (se 1 (by rfl) ⟨2813210, by rfl⟩ : syracuseStep 3750947 = 5626421) B5626421
theorem B1489985 : Blo 259821 1489985 := bstep (se 2 (by rfl) ⟨558744, by rfl⟩ : syracuseStep 1489985 = 1117489) B1117489
theorem B441497 : Blo 259821 441497 := bstep (se 2 (by rfl) ⟨165561, by rfl⟩ : syracuseStep 441497 = 331123) B331123
theorem B1883341 : Blo 259821 1883341 := bstep (se 3 (by rfl) ⟨353126, by rfl⟩ : syracuseStep 1883341 = 706253) B706253
theorem B1064215 : Blo 259821 1064215 := bstep (se 1 (by rfl) ⟨798161, by rfl⟩ : syracuseStep 1064215 = 1596323) B1596323
theorem B441625 : Blo 259821 441625 := bstep (se 2 (by rfl) ⟨165609, by rfl⟩ : syracuseStep 441625 = 331219) B331219
theorem B343435 : Blo 259821 343435 := bstep (se 1 (by rfl) ⟨257576, by rfl⟩ : syracuseStep 343435 = 515153) B515153
theorem B4505219 : Blo 259821 4505219 := bstep (se 1 (by rfl) ⟨3378914, by rfl⟩ : syracuseStep 4505219 = 6757829) B6757829
theorem B442199 : Blo 259821 442199 := bstep (se 1 (by rfl) ⟨331649, by rfl⟩ : syracuseStep 442199 = 663299) B663299
theorem B1326941 : Blo 259821 1326941 := bstep (se 3 (by rfl) ⟨248801, by rfl⟩ : syracuseStep 1326941 = 497603) B497603
theorem B442327 : Blo 259821 442327 := bstep (se 1 (by rfl) ⟨331745, by rfl⟩ : syracuseStep 442327 = 663491) B663491
theorem B3653707 : Blo 259821 3653707 := bstep (se 1 (by rfl) ⟨2740280, by rfl⟩ : syracuseStep 3653707 = 5480561) B5480561
theorem B999641 : Blo 259821 999641 := bstep (se 2 (by rfl) ⟨374865, by rfl⟩ : syracuseStep 999641 = 749731) B749731
theorem B278839 : Blo 259821 278839 := bstep (se 1 (by rfl) ⟨209129, by rfl⟩ : syracuseStep 278839 = 418259) B418259
theorem B3555701 : Blo 259821 3555701 := bstep (se 5 (by rfl) ⟨166673, by rfl⟩ : syracuseStep 3555701 = 333347) B333347
theorem B1458611 : Blo 259821 1458611 := bstep (se 1 (by rfl) ⟨1093958, by rfl⟩ : syracuseStep 1458611 = 2187917) B2187917
theorem B442955 : Blo 259821 442955 := bstep (se 1 (by rfl) ⟨332216, by rfl⟩ : syracuseStep 442955 = 664433) B664433
theorem B2507395 : Blo 259821 2507395 := bstep (se 1 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 2507395 = 3761093) B3761093
theorem B443083 : Blo 259821 443083 := bstep (se 1 (by rfl) ⟨332312, by rfl⟩ : syracuseStep 443083 = 664625) B664625
theorem B2999105 : Blo 259821 2999105 := bstep (se 2 (by rfl) ⟨1124664, by rfl⟩ : syracuseStep 2999105 = 2249329) B2249329
theorem B443225 : Blo 259821 443225 := bstep (se 2 (by rfl) ⟨166209, by rfl⟩ : syracuseStep 443225 = 332419) B332419
theorem B1065901 : Blo 259821 1065901 := bstep (se 3 (by rfl) ⟨199856, by rfl⟩ : syracuseStep 1065901 = 399713) B399713
theorem B443353 : Blo 259821 443353 := bstep (se 2 (by rfl) ⟨166257, by rfl⟩ : syracuseStep 443353 = 332515) B332515
theorem B279659 : Blo 259821 279659 := bstep (se 1 (by rfl) ⟨209744, by rfl⟩ : syracuseStep 279659 = 419489) B419489
theorem B836887 : Blo 259821 836887 := bstep (se 1 (by rfl) ⟨627665, by rfl⟩ : syracuseStep 836887 = 1255331) B1255331
theorem B837067 : Blo 259821 837067 := bstep (se 1 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 837067 = 1255601) B1255601
theorem B837143 : Blo 259821 837143 := bstep (se 1 (by rfl) ⟨627857, by rfl⟩ : syracuseStep 837143 = 1255715) B1255715
theorem B443927 : Blo 259821 443927 := bstep (se 1 (by rfl) ⟨332945, by rfl⟩ : syracuseStep 443927 = 665891) B665891
theorem B4867715 : Blo 259821 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B444055 : Blo 259821 444055 := bstep (se 1 (by rfl) ⟨333041, by rfl⟩ : syracuseStep 444055 = 666083) B666083
theorem B837337 : Blo 259821 837337 := bstep (se 2 (by rfl) ⟨314001, by rfl⟩ : syracuseStep 837337 = 628003) B628003
theorem B1066775 : Blo 259821 1066775 := bstep (se 1 (by rfl) ⟨800081, by rfl⟩ : syracuseStep 1066775 = 1600163) B1600163
theorem B1001267 : Blo 259821 1001267 := bstep (se 1 (by rfl) ⟨750950, by rfl⟩ : syracuseStep 1001267 = 1501901) B1501901
theorem B1001281 : Blo 259821 1001281 := bstep (se 2 (by rfl) ⟨375480, by rfl⟩ : syracuseStep 1001281 = 750961) B750961
theorem B1329047 : Blo 259821 1329047 := bstep (se 1 (by rfl) ⟨996785, by rfl⟩ : syracuseStep 1329047 = 1993571) B1993571
theorem B1263539 : Blo 259821 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B1427557 : Blo 259821 1427557 := bstep (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) B267667
theorem B444683 : Blo 259821 444683 := bstep (se 1 (by rfl) ⟨333512, by rfl⟩ : syracuseStep 444683 = 667025) B667025
theorem B280855 : Blo 259821 280855 := bstep (se 1 (by rfl) ⟨210641, by rfl⟩ : syracuseStep 280855 = 421283) B421283
theorem B2836781 : Blo 259821 2836781 := bstep (se 3 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 2836781 = 1063793) B1063793
theorem B444811 : Blo 259821 444811 := bstep (se 1 (by rfl) ⟨333608, by rfl⟩ : syracuseStep 444811 = 667217) B667217
theorem B444953 : Blo 259821 444953 := bstep (se 2 (by rfl) ⟨166857, by rfl⟩ : syracuseStep 444953 = 333715) B333715
theorem B445081 : Blo 259821 445081 := bstep (se 2 (by rfl) ⟨166905, by rfl⟩ : syracuseStep 445081 = 333811) B333811
theorem B772915 : Blo 259821 772915 := bstep (se 1 (by rfl) ⟨579686, by rfl⟩ : syracuseStep 772915 = 1159373) B1159373
theorem B641881 : Blo 259821 641881 := bstep (se 2 (by rfl) ⟨240705, by rfl⟩ : syracuseStep 641881 = 481411) B481411
theorem B9554867 : Blo 259821 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B281675 : Blo 259821 281675 := bstep (se 1 (by rfl) ⟨211256, by rfl⟩ : syracuseStep 281675 = 422513) B422513
theorem B740573 : Blo 259821 740573 := bstep (se 3 (by rfl) ⟨138857, by rfl⟩ : syracuseStep 740573 = 277715) B277715
theorem B10833301 : Blo 259821 10833301 := bstep (se 6 (by rfl) ⟨253905, by rfl⟩ : syracuseStep 10833301 = 507811) B507811
theorem B740801 : Blo 259821 740801 := bstep (se 2 (by rfl) ⟨277800, by rfl⟩ : syracuseStep 740801 = 555601) B555601
theorem B3788363 : Blo 259821 3788363 := bstep (se 1 (by rfl) ⟨2841272, by rfl⟩ : syracuseStep 3788363 = 5682545) B5682545
theorem B741143 : Blo 259821 741143 := bstep (se 1 (by rfl) ⟨555857, by rfl⟩ : syracuseStep 741143 = 1111715) B1111715
theorem B839603 : Blo 259821 839603 := bstep (se 1 (by rfl) ⟨629702, by rfl⟩ : syracuseStep 839603 = 1259405) B1259405
theorem B1495361 : Blo 259821 1495361 := bstep (se 2 (by rfl) ⟨560760, by rfl⟩ : syracuseStep 1495361 = 1121521) B1121521
theorem B2019763 : Blo 259821 2019763 := bstep (se 1 (by rfl) ⟨1514822, by rfl⟩ : syracuseStep 2019763 = 3029645) B3029645
theorem B1364441 : Blo 259821 1364441 := bstep (se 2 (by rfl) ⟨511665, by rfl⟩ : syracuseStep 1364441 = 1023331) B1023331
theorem B2249603 : Blo 259821 2249603 := bstep (se 1 (by rfl) ⟨1687202, by rfl⟩ : syracuseStep 2249603 = 3374405) B3374405
theorem B1332611 : Blo 259821 1332611 := bstep (se 1 (by rfl) ⟨999458, by rfl⟩ : syracuseStep 1332611 = 1998917) B1998917
theorem B808385 : Blo 259821 808385 := bstep (se 2 (by rfl) ⟨303144, by rfl⟩ : syracuseStep 808385 = 606289) B606289
theorem B808537 : Blo 259821 808537 := bstep (se 2 (by rfl) ⟨303201, by rfl⟩ : syracuseStep 808537 = 606403) B606403
theorem B9557635 : Blo 259821 9557635 := bstep (se 1 (by rfl) ⟨7168226, by rfl⟩ : syracuseStep 9557635 = 14336453) B14336453
theorem B8214371 : Blo 259821 8214371 := bstep (se 1 (by rfl) ⟨6160778, by rfl⟩ : syracuseStep 8214371 = 12321557) B12321557
theorem B448459 : Blo 259821 448459 := bstep (se 1 (by rfl) ⟨336344, by rfl⟩ : syracuseStep 448459 = 672689) B672689
theorem B743489 : Blo 259821 743489 := bstep (se 2 (by rfl) ⟨278808, by rfl⟩ : syracuseStep 743489 = 557617) B557617
theorem B940547 : Blo 259821 940547 := bstep (se 1 (by rfl) ⟨705410, by rfl⟩ : syracuseStep 940547 = 1410821) B1410821
theorem B481879 : Blo 259821 481879 := bstep (se 1 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 481879 = 722819) B722819
theorem B744025 : Blo 259821 744025 := bstep (se 2 (by rfl) ⟨279009, by rfl⟩ : syracuseStep 744025 = 558019) B558019
theorem B2120579 : Blo 259821 2120579 := bstep (se 1 (by rfl) ⟨1590434, by rfl⟩ : syracuseStep 2120579 = 3180869) B3180869
theorem B5856407 : Blo 259821 5856407 := bstep (se 1 (by rfl) ⟨4392305, by rfl⟩ : syracuseStep 5856407 = 8784611) B8784611
theorem B416983 : Blo 259821 416983 := bstep (se 1 (by rfl) ⟨312737, by rfl⟩ : syracuseStep 416983 = 625475) B625475
theorem B1891619 : Blo 259821 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B417239 : Blo 259821 417239 := bstep (se 1 (by rfl) ⟨312929, by rfl⟩ : syracuseStep 417239 = 625859) B625859
theorem B351959 : Blo 259821 351959 := bstep (se 1 (by rfl) ⟨263969, by rfl⟩ : syracuseStep 351959 = 527939) B527939
theorem B5660401 : Blo 259821 5660401 := bstep (se 2 (by rfl) ⟨2122650, by rfl⟩ : syracuseStep 5660401 = 4245301) B4245301
theorem B417611 : Blo 259821 417611 := bstep (se 1 (by rfl) ⟨313208, by rfl⟩ : syracuseStep 417611 = 626417) B626417
theorem B1335361 : Blo 259821 1335361 := bstep (se 2 (by rfl) ⟨500760, by rfl⟩ : syracuseStep 1335361 = 1001521) B1001521
theorem B745949 : Blo 259821 745949 := bstep (se 3 (by rfl) ⟨139865, by rfl⟩ : syracuseStep 745949 = 279731) B279731
theorem B877121 : Blo 259821 877121 := bstep (se 2 (by rfl) ⟨328920, by rfl⟩ : syracuseStep 877121 = 657841) B657841
theorem B2220695 : Blo 259821 2220695 := bstep (se 1 (by rfl) ⟨1665521, by rfl⟩ : syracuseStep 2220695 = 3331043) B3331043
theorem B2384741 : Blo 259821 2384741 := bstep (se 4 (by rfl) ⟨223569, by rfl⟩ : syracuseStep 2384741 = 447139) B447139
theorem B877661 : Blo 259821 877661 := bstep (se 3 (by rfl) ⟨164561, by rfl⟩ : syracuseStep 877661 = 329123) B329123
theorem B419033 : Blo 259821 419033 := bstep (se 2 (by rfl) ⟨157137, by rfl⟩ : syracuseStep 419033 = 314275) B314275
theorem B1992113 : Blo 259821 1992113 := bstep (se 2 (by rfl) ⟨747042, by rfl⟩ : syracuseStep 1992113 = 1494085) B1494085
theorem B1598899 : Blo 259821 1598899 := bstep (se 1 (by rfl) ⟨1199174, by rfl⟩ : syracuseStep 1598899 = 2398349) B2398349
theorem B1992599 : Blo 259821 1992599 := bstep (se 1 (by rfl) ⟨1494449, by rfl⟩ : syracuseStep 1992599 = 2988899) B2988899
theorem B878795 : Blo 259821 878795 := bstep (se 1 (by rfl) ⟨659096, by rfl⟩ : syracuseStep 878795 = 1318193) B1318193
theorem B879065 : Blo 259821 879065 := bstep (se 2 (by rfl) ⟨329649, by rfl⟩ : syracuseStep 879065 = 659299) B659299
theorem B2255435 : Blo 259821 2255435 := bstep (se 1 (by rfl) ⟨1691576, by rfl⟩ : syracuseStep 2255435 = 3383153) B3383153
theorem B944729 : Blo 259821 944729 := bstep (se 2 (by rfl) ⟨354273, by rfl⟩ : syracuseStep 944729 = 708547) B708547
theorem B6744707 : Blo 259821 6744707 := bstep (se 1 (by rfl) ⟨5058530, by rfl⟩ : syracuseStep 6744707 = 10117061) B10117061
theorem B354955 : Blo 259821 354955 := bstep (se 1 (by rfl) ⟨266216, by rfl⟩ : syracuseStep 354955 = 532433) B532433
theorem B945047 : Blo 259821 945047 := bstep (se 1 (by rfl) ⟨708785, by rfl⟩ : syracuseStep 945047 = 1417571) B1417571
theorem B584729 : Blo 259821 584729 := bstep (se 2 (by rfl) ⟨219273, by rfl⟩ : syracuseStep 584729 = 438547) B438547
theorem B2583587 : Blo 259821 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B584819 : Blo 259821 584819 := bstep (se 1 (by rfl) ⟨438614, by rfl⟩ : syracuseStep 584819 = 877229) B877229
theorem B1010819 : Blo 259821 1010819 := bstep (se 1 (by rfl) ⟨758114, by rfl⟩ : syracuseStep 1010819 = 1516229) B1516229
theorem B584855 : Blo 259821 584855 := bstep (se 1 (by rfl) ⟨438641, by rfl⟩ : syracuseStep 584855 = 877283) B877283
theorem B879767 : Blo 259821 879767 := bstep (se 1 (by rfl) ⟨659825, by rfl⟩ : syracuseStep 879767 = 1319651) B1319651
theorem B748865 : Blo 259821 748865 := bstep (se 2 (by rfl) ⟨280824, by rfl⟩ : syracuseStep 748865 = 561649) B561649
theorem B585035 : Blo 259821 585035 := bstep (se 1 (by rfl) ⟨438776, by rfl⟩ : syracuseStep 585035 = 877553) B877553
theorem B748889 : Blo 259821 748889 := bstep (se 2 (by rfl) ⟨280833, by rfl⟩ : syracuseStep 748889 = 561667) B561667
theorem B585089 : Blo 259821 585089 := bstep (se 2 (by rfl) ⟨219408, by rfl⟩ : syracuseStep 585089 = 438817) B438817
theorem B585305 : Blo 259821 585305 := bstep (se 2 (by rfl) ⟨219489, by rfl⟩ : syracuseStep 585305 = 438979) B438979
theorem B1601117 : Blo 259821 1601117 := bstep (se 3 (by rfl) ⟨300209, by rfl⟩ : syracuseStep 1601117 = 600419) B600419
theorem B585395 : Blo 259821 585395 := bstep (se 1 (by rfl) ⟨439046, by rfl⟩ : syracuseStep 585395 = 878093) B878093
theorem B880307 : Blo 259821 880307 := bstep (se 1 (by rfl) ⟨660230, by rfl⟩ : syracuseStep 880307 = 1320461) B1320461
theorem B585431 : Blo 259821 585431 := bstep (se 1 (by rfl) ⟨439073, by rfl⟩ : syracuseStep 585431 = 878147) B878147
theorem B585611 : Blo 259821 585611 := bstep (se 1 (by rfl) ⟨439208, by rfl⟩ : syracuseStep 585611 = 878417) B878417
theorem B585665 : Blo 259821 585665 := bstep (se 2 (by rfl) ⟨219624, by rfl⟩ : syracuseStep 585665 = 439249) B439249
theorem B880577 : Blo 259821 880577 := bstep (se 2 (by rfl) ⟨330216, by rfl⟩ : syracuseStep 880577 = 660433) B660433
theorem B585881 : Blo 259821 585881 := bstep (se 2 (by rfl) ⟨219705, by rfl⟩ : syracuseStep 585881 = 439411) B439411
theorem B585971 : Blo 259821 585971 := bstep (se 1 (by rfl) ⟨439478, by rfl⟩ : syracuseStep 585971 = 878957) B878957
theorem B586007 : Blo 259821 586007 := bstep (se 1 (by rfl) ⟨439505, by rfl⟩ : syracuseStep 586007 = 879011) B879011
theorem B586187 : Blo 259821 586187 := bstep (se 1 (by rfl) ⟨439640, by rfl⟩ : syracuseStep 586187 = 879281) B879281
theorem B881117 : Blo 259821 881117 := bstep (se 3 (by rfl) ⟨165209, by rfl⟩ : syracuseStep 881117 = 330419) B330419
theorem B586241 : Blo 259821 586241 := bstep (se 2 (by rfl) ⟨219840, by rfl⟩ : syracuseStep 586241 = 439681) B439681
theorem B750131 : Blo 259821 750131 := bstep (se 1 (by rfl) ⟨562598, by rfl⟩ : syracuseStep 750131 = 1125197) B1125197
theorem B389771 : Blo 259821 389771 := bstep (se 1 (by rfl) ⟨292328, by rfl⟩ : syracuseStep 389771 = 584657) B584657
theorem B389783 : Blo 259821 389783 := bstep (se 1 (by rfl) ⟨292337, by rfl⟩ : syracuseStep 389783 = 584675) B584675
theorem B389849 : Blo 259821 389849 := bstep (se 2 (by rfl) ⟨146193, by rfl⟩ : syracuseStep 389849 = 292387) B292387
theorem B586457 : Blo 259821 586457 := bstep (se 2 (by rfl) ⟨219921, by rfl⟩ : syracuseStep 586457 = 439843) B439843
theorem B586547 : Blo 259821 586547 := bstep (se 1 (by rfl) ⟨439910, by rfl⟩ : syracuseStep 586547 = 879821) B879821
theorem B389963 : Blo 259821 389963 := bstep (se 1 (by rfl) ⟨292472, by rfl⟩ : syracuseStep 389963 = 584945) B584945
theorem B389975 : Blo 259821 389975 := bstep (se 1 (by rfl) ⟨292481, by rfl⟩ : syracuseStep 389975 = 584963) B584963
theorem B586583 : Blo 259821 586583 := bstep (se 1 (by rfl) ⟨439937, by rfl⟩ : syracuseStep 586583 = 879875) B879875
theorem B390041 : Blo 259821 390041 := bstep (se 2 (by rfl) ⟨146265, by rfl⟩ : syracuseStep 390041 = 292531) B292531
theorem B390155 : Blo 259821 390155 := bstep (se 1 (by rfl) ⟨292616, by rfl⟩ : syracuseStep 390155 = 585233) B585233
theorem B586763 : Blo 259821 586763 := bstep (se 1 (by rfl) ⟨440072, by rfl⟩ : syracuseStep 586763 = 880145) B880145
theorem B1668113 : Blo 259821 1668113 := bstep (se 2 (by rfl) ⟨625542, by rfl⟩ : syracuseStep 1668113 = 1251085) B1251085
theorem B390167 : Blo 259821 390167 := bstep (se 1 (by rfl) ⟨292625, by rfl⟩ : syracuseStep 390167 = 585251) B585251
theorem B586817 : Blo 259821 586817 := bstep (se 2 (by rfl) ⟨220056, by rfl⟩ : syracuseStep 586817 = 440113) B440113
theorem B390233 : Blo 259821 390233 := bstep (se 2 (by rfl) ⟨146337, by rfl⟩ : syracuseStep 390233 = 292675) B292675
theorem B1111133 : Blo 259821 1111133 := bstep (se 3 (by rfl) ⟨208337, by rfl⟩ : syracuseStep 1111133 = 416675) B416675
theorem B390347 : Blo 259821 390347 := bstep (se 1 (by rfl) ⟨292760, by rfl⟩ : syracuseStep 390347 = 585521) B585521
theorem B390359 : Blo 259821 390359 := bstep (se 1 (by rfl) ⟨292769, by rfl⟩ : syracuseStep 390359 = 585539) B585539
theorem B390425 : Blo 259821 390425 := bstep (se 2 (by rfl) ⟨146409, by rfl⟩ : syracuseStep 390425 = 292819) B292819
theorem B587033 : Blo 259821 587033 := bstep (se 2 (by rfl) ⟨220137, by rfl⟩ : syracuseStep 587033 = 440275) B440275
theorem B587123 : Blo 259821 587123 := bstep (se 1 (by rfl) ⟨440342, by rfl⟩ : syracuseStep 587123 = 880685) B880685
theorem B390539 : Blo 259821 390539 := bstep (se 1 (by rfl) ⟨292904, by rfl⟩ : syracuseStep 390539 = 585809) B585809
theorem B1111441 : Blo 259821 1111441 := bstep (se 2 (by rfl) ⟨416790, by rfl⟩ : syracuseStep 1111441 = 833581) B833581
theorem B390551 : Blo 259821 390551 := bstep (se 1 (by rfl) ⟨292913, by rfl⟩ : syracuseStep 390551 = 585827) B585827
theorem B587159 : Blo 259821 587159 := bstep (se 1 (by rfl) ⟨440369, by rfl⟩ : syracuseStep 587159 = 880739) B880739
theorem B1111475 : Blo 259821 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B390617 : Blo 259821 390617 := bstep (se 2 (by rfl) ⟨146481, by rfl⟩ : syracuseStep 390617 = 292963) B292963
theorem B390731 : Blo 259821 390731 := bstep (se 1 (by rfl) ⟨293048, by rfl⟩ : syracuseStep 390731 = 586097) B586097
theorem B587339 : Blo 259821 587339 := bstep (se 1 (by rfl) ⟨440504, by rfl⟩ : syracuseStep 587339 = 881009) B881009
theorem B882251 : Blo 259821 882251 := bstep (se 1 (by rfl) ⟨661688, by rfl⟩ : syracuseStep 882251 = 1323377) B1323377
theorem B390743 : Blo 259821 390743 := bstep (se 1 (by rfl) ⟨293057, by rfl⟩ : syracuseStep 390743 = 586115) B586115
theorem B292459 : Blo 259821 292459 := bstep (se 1 (by rfl) ⟨219344, by rfl⟩ : syracuseStep 292459 = 438689) B438689
theorem B587393 : Blo 259821 587393 := bstep (se 2 (by rfl) ⟨220272, by rfl⟩ : syracuseStep 587393 = 440545) B440545
theorem B390809 : Blo 259821 390809 := bstep (se 2 (by rfl) ⟨146553, by rfl⟩ : syracuseStep 390809 = 293107) B293107
theorem B292567 : Blo 259821 292567 := bstep (se 1 (by rfl) ⟨219425, by rfl⟩ : syracuseStep 292567 = 438851) B438851
theorem B259831 : Blo 259821 259831 := bstep (se 1 (by rfl) ⟨194873, by rfl⟩ : syracuseStep 259831 = 389747) B389747
theorem B259851 : Blo 259821 259851 := bstep (se 1 (by rfl) ⟨194888, by rfl⟩ : syracuseStep 259851 = 389777) B389777
theorem B390923 : Blo 259821 390923 := bstep (se 1 (by rfl) ⟨293192, by rfl⟩ : syracuseStep 390923 = 586385) B586385
theorem B259863 : Blo 259821 259863 := bstep (se 1 (by rfl) ⟨194897, by rfl⟩ : syracuseStep 259863 = 389795) B389795
theorem B390935 : Blo 259821 390935 := bstep (se 1 (by rfl) ⟨293201, by rfl⟩ : syracuseStep 390935 = 586403) B586403
theorem B259883 : Blo 259821 259883 := bstep (se 1 (by rfl) ⟨194912, by rfl⟩ : syracuseStep 259883 = 389825) B389825
theorem B259895 : Blo 259821 259895 := bstep (se 1 (by rfl) ⟨194921, by rfl⟩ : syracuseStep 259895 = 389843) B389843
theorem B259915 : Blo 259821 259915 := bstep (se 1 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 259915 = 389873) B389873
theorem B259927 : Blo 259821 259927 := bstep (se 1 (by rfl) ⟨194945, by rfl⟩ : syracuseStep 259927 = 389891) B389891
theorem B391001 : Blo 259821 391001 := bstep (se 2 (by rfl) ⟨146625, by rfl⟩ : syracuseStep 391001 = 293251) B293251
theorem B587609 : Blo 259821 587609 := bstep (se 2 (by rfl) ⟨220353, by rfl⟩ : syracuseStep 587609 = 440707) B440707
theorem B882521 : Blo 259821 882521 := bstep (se 2 (by rfl) ⟨330945, by rfl⟩ : syracuseStep 882521 = 661891) B661891
theorem B259947 : Blo 259821 259947 := bstep (se 1 (by rfl) ⟨194960, by rfl⟩ : syracuseStep 259947 = 389921) B389921
theorem B259959 : Blo 259821 259959 := bstep (se 1 (by rfl) ⟨194969, by rfl⟩ : syracuseStep 259959 = 389939) B389939
theorem B259979 : Blo 259821 259979 := bstep (se 1 (by rfl) ⟨194984, by rfl⟩ : syracuseStep 259979 = 389969) B389969
theorem B292747 : Blo 259821 292747 := bstep (se 1 (by rfl) ⟨219560, by rfl⟩ : syracuseStep 292747 = 439121) B439121
theorem B259991 : Blo 259821 259991 := bstep (se 1 (by rfl) ⟨194993, by rfl⟩ : syracuseStep 259991 = 389987) B389987
theorem B260011 : Blo 259821 260011 := bstep (se 1 (by rfl) ⟨195008, by rfl⟩ : syracuseStep 260011 = 390017) B390017
theorem B587699 : Blo 259821 587699 := bstep (se 1 (by rfl) ⟨440774, by rfl⟩ : syracuseStep 587699 = 881549) B881549
theorem B260023 : Blo 259821 260023 := bstep (se 1 (by rfl) ⟨195017, by rfl⟩ : syracuseStep 260023 = 390035) B390035
theorem B260043 : Blo 259821 260043 := bstep (se 1 (by rfl) ⟨195032, by rfl⟩ : syracuseStep 260043 = 390065) B390065
theorem B391115 : Blo 259821 391115 := bstep (se 1 (by rfl) ⟨293336, by rfl⟩ : syracuseStep 391115 = 586673) B586673
theorem B260055 : Blo 259821 260055 := bstep (se 1 (by rfl) ⟨195041, by rfl⟩ : syracuseStep 260055 = 390083) B390083
theorem B391127 : Blo 259821 391127 := bstep (se 1 (by rfl) ⟨293345, by rfl⟩ : syracuseStep 391127 = 586691) B586691
theorem B587735 : Blo 259821 587735 := bstep (se 1 (by rfl) ⟨440801, by rfl⟩ : syracuseStep 587735 = 881603) B881603
theorem B260075 : Blo 259821 260075 := bstep (se 1 (by rfl) ⟨195056, by rfl⟩ : syracuseStep 260075 = 390113) B390113
theorem B292855 : Blo 259821 292855 := bstep (se 1 (by rfl) ⟨219641, by rfl⟩ : syracuseStep 292855 = 439283) B439283
theorem B260087 : Blo 259821 260087 := bstep (se 1 (by rfl) ⟨195065, by rfl⟩ : syracuseStep 260087 = 390131) B390131
theorem B260107 : Blo 259821 260107 := bstep (se 1 (by rfl) ⟨195080, by rfl⟩ : syracuseStep 260107 = 390161) B390161
theorem B260119 : Blo 259821 260119 := bstep (se 1 (by rfl) ⟨195089, by rfl⟩ : syracuseStep 260119 = 390179) B390179
theorem B391193 : Blo 259821 391193 := bstep (se 2 (by rfl) ⟨146697, by rfl⟩ : syracuseStep 391193 = 293395) B293395
theorem B260139 : Blo 259821 260139 := bstep (se 1 (by rfl) ⟨195104, by rfl⟩ : syracuseStep 260139 = 390209) B390209
theorem B260151 : Blo 259821 260151 := bstep (se 1 (by rfl) ⟨195113, by rfl⟩ : syracuseStep 260151 = 390227) B390227
theorem B260171 : Blo 259821 260171 := bstep (se 1 (by rfl) ⟨195128, by rfl⟩ : syracuseStep 260171 = 390257) B390257
theorem B260183 : Blo 259821 260183 := bstep (se 1 (by rfl) ⟨195137, by rfl⟩ : syracuseStep 260183 = 390275) B390275
theorem B260203 : Blo 259821 260203 := bstep (se 1 (by rfl) ⟨195152, by rfl⟩ : syracuseStep 260203 = 390305) B390305
theorem B260215 : Blo 259821 260215 := bstep (se 1 (by rfl) ⟨195161, by rfl⟩ : syracuseStep 260215 = 390323) B390323
theorem B260235 : Blo 259821 260235 := bstep (se 1 (by rfl) ⟨195176, by rfl⟩ : syracuseStep 260235 = 390353) B390353
theorem B391307 : Blo 259821 391307 := bstep (se 1 (by rfl) ⟨293480, by rfl⟩ : syracuseStep 391307 = 586961) B586961
theorem B587915 : Blo 259821 587915 := bstep (se 1 (by rfl) ⟨440936, by rfl⟩ : syracuseStep 587915 = 881873) B881873
theorem B260247 : Blo 259821 260247 := bstep (se 1 (by rfl) ⟨195185, by rfl⟩ : syracuseStep 260247 = 390371) B390371
theorem B391319 : Blo 259821 391319 := bstep (se 1 (by rfl) ⟨293489, by rfl⟩ : syracuseStep 391319 = 586979) B586979
theorem B260267 : Blo 259821 260267 := bstep (se 1 (by rfl) ⟨195200, by rfl⟩ : syracuseStep 260267 = 390401) B390401
theorem B293035 : Blo 259821 293035 := bstep (se 1 (by rfl) ⟨219776, by rfl⟩ : syracuseStep 293035 = 439553) B439553
theorem B260279 : Blo 259821 260279 := bstep (se 1 (by rfl) ⟨195209, by rfl⟩ : syracuseStep 260279 = 390419) B390419
theorem B587969 : Blo 259821 587969 := bstep (se 2 (by rfl) ⟨220488, by rfl⟩ : syracuseStep 587969 = 440977) B440977
theorem B260299 : Blo 259821 260299 := bstep (se 1 (by rfl) ⟨195224, by rfl⟩ : syracuseStep 260299 = 390449) B390449
theorem B260311 : Blo 259821 260311 := bstep (se 1 (by rfl) ⟨195233, by rfl⟩ : syracuseStep 260311 = 390467) B390467
theorem B391385 : Blo 259821 391385 := bstep (se 2 (by rfl) ⟨146769, by rfl⟩ : syracuseStep 391385 = 293539) B293539
theorem B260331 : Blo 259821 260331 := bstep (se 1 (by rfl) ⟨195248, by rfl⟩ : syracuseStep 260331 = 390497) B390497
theorem B260343 : Blo 259821 260343 := bstep (se 1 (by rfl) ⟨195257, by rfl⟩ : syracuseStep 260343 = 390515) B390515
theorem B260363 : Blo 259821 260363 := bstep (se 1 (by rfl) ⟨195272, by rfl⟩ : syracuseStep 260363 = 390545) B390545
theorem B260375 : Blo 259821 260375 := bstep (se 1 (by rfl) ⟨195281, by rfl⟩ : syracuseStep 260375 = 390563) B390563
theorem B293143 : Blo 259821 293143 := bstep (se 1 (by rfl) ⟨219857, by rfl⟩ : syracuseStep 293143 = 439715) B439715
theorem B260395 : Blo 259821 260395 := bstep (se 1 (by rfl) ⟨195296, by rfl⟩ : syracuseStep 260395 = 390593) B390593
theorem B260407 : Blo 259821 260407 := bstep (se 1 (by rfl) ⟨195305, by rfl⟩ : syracuseStep 260407 = 390611) B390611
theorem B260427 : Blo 259821 260427 := bstep (se 1 (by rfl) ⟨195320, by rfl⟩ : syracuseStep 260427 = 390641) B390641
theorem B391499 : Blo 259821 391499 := bstep (se 1 (by rfl) ⟨293624, by rfl⟩ : syracuseStep 391499 = 587249) B587249
theorem B260439 : Blo 259821 260439 := bstep (se 1 (by rfl) ⟨195329, by rfl⟩ : syracuseStep 260439 = 390659) B390659
theorem B391511 : Blo 259821 391511 := bstep (se 1 (by rfl) ⟨293633, by rfl⟩ : syracuseStep 391511 = 587267) B587267
theorem B260459 : Blo 259821 260459 := bstep (se 1 (by rfl) ⟨195344, by rfl⟩ : syracuseStep 260459 = 390689) B390689
theorem B260471 : Blo 259821 260471 := bstep (se 1 (by rfl) ⟨195353, by rfl⟩ : syracuseStep 260471 = 390707) B390707
theorem B260491 : Blo 259821 260491 := bstep (se 1 (by rfl) ⟨195368, by rfl⟩ : syracuseStep 260491 = 390737) B390737
theorem B8550805 : Blo 259821 8550805 := bstep (se 6 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 8550805 = 400819) B400819
theorem B260503 : Blo 259821 260503 := bstep (se 1 (by rfl) ⟨195377, by rfl⟩ : syracuseStep 260503 = 390755) B390755
theorem B391577 : Blo 259821 391577 := bstep (se 2 (by rfl) ⟨146841, by rfl⟩ : syracuseStep 391577 = 293683) B293683
theorem B588185 : Blo 259821 588185 := bstep (se 2 (by rfl) ⟨220569, by rfl⟩ : syracuseStep 588185 = 441139) B441139
theorem B260523 : Blo 259821 260523 := bstep (se 1 (by rfl) ⟨195392, by rfl⟩ : syracuseStep 260523 = 390785) B390785
theorem B260535 : Blo 259821 260535 := bstep (se 1 (by rfl) ⟨195401, by rfl⟩ : syracuseStep 260535 = 390803) B390803
theorem B260555 : Blo 259821 260555 := bstep (se 1 (by rfl) ⟨195416, by rfl⟩ : syracuseStep 260555 = 390833) B390833
theorem B293323 : Blo 259821 293323 := bstep (se 1 (by rfl) ⟨219992, by rfl⟩ : syracuseStep 293323 = 439985) B439985
theorem B260567 : Blo 259821 260567 := bstep (se 1 (by rfl) ⟨195425, by rfl⟩ : syracuseStep 260567 = 390851) B390851
theorem B260587 : Blo 259821 260587 := bstep (se 1 (by rfl) ⟨195440, by rfl⟩ : syracuseStep 260587 = 390881) B390881
theorem B588275 : Blo 259821 588275 := bstep (se 1 (by rfl) ⟨441206, by rfl⟩ : syracuseStep 588275 = 882413) B882413
theorem B260599 : Blo 259821 260599 := bstep (se 1 (by rfl) ⟨195449, by rfl⟩ : syracuseStep 260599 = 390899) B390899
theorem B260619 : Blo 259821 260619 := bstep (se 1 (by rfl) ⟨195464, by rfl⟩ : syracuseStep 260619 = 390929) B390929
theorem B391691 : Blo 259821 391691 := bstep (se 1 (by rfl) ⟨293768, by rfl⟩ : syracuseStep 391691 = 587537) B587537
theorem B260631 : Blo 259821 260631 := bstep (se 1 (by rfl) ⟨195473, by rfl⟩ : syracuseStep 260631 = 390947) B390947
theorem B391703 : Blo 259821 391703 := bstep (se 1 (by rfl) ⟨293777, by rfl⟩ : syracuseStep 391703 = 587555) B587555
theorem B588311 : Blo 259821 588311 := bstep (se 1 (by rfl) ⟨441233, by rfl⟩ : syracuseStep 588311 = 882467) B882467
theorem B883223 : Blo 259821 883223 := bstep (se 1 (by rfl) ⟨662417, by rfl⟩ : syracuseStep 883223 = 1324835) B1324835
theorem B260651 : Blo 259821 260651 := bstep (se 1 (by rfl) ⟨195488, by rfl⟩ : syracuseStep 260651 = 390977) B390977
theorem B1505837 : Blo 259821 1505837 := bstep (se 3 (by rfl) ⟨282344, by rfl⟩ : syracuseStep 1505837 = 564689) B564689
theorem B260663 : Blo 259821 260663 := bstep (se 1 (by rfl) ⟨195497, by rfl⟩ : syracuseStep 260663 = 390995) B390995
theorem B293431 : Blo 259821 293431 := bstep (se 1 (by rfl) ⟨220073, by rfl⟩ : syracuseStep 293431 = 440147) B440147
theorem B260683 : Blo 259821 260683 := bstep (se 1 (by rfl) ⟨195512, by rfl⟩ : syracuseStep 260683 = 391025) B391025
theorem B260695 : Blo 259821 260695 := bstep (se 1 (by rfl) ⟨195521, by rfl⟩ : syracuseStep 260695 = 391043) B391043
theorem B391769 : Blo 259821 391769 := bstep (se 2 (by rfl) ⟨146913, by rfl⟩ : syracuseStep 391769 = 293827) B293827
theorem B260715 : Blo 259821 260715 := bstep (se 1 (by rfl) ⟨195536, by rfl⟩ : syracuseStep 260715 = 391073) B391073
theorem B555635 : Blo 259821 555635 := bstep (se 1 (by rfl) ⟨416726, by rfl⟩ : syracuseStep 555635 = 833453) B833453
theorem B260727 : Blo 259821 260727 := bstep (se 1 (by rfl) ⟨195545, by rfl⟩ : syracuseStep 260727 = 391091) B391091
theorem B260747 : Blo 259821 260747 := bstep (se 1 (by rfl) ⟨195560, by rfl⟩ : syracuseStep 260747 = 391121) B391121
theorem B260759 : Blo 259821 260759 := bstep (se 1 (by rfl) ⟨195569, by rfl⟩ : syracuseStep 260759 = 391139) B391139
theorem B457367 : Blo 259821 457367 := bstep (se 1 (by rfl) ⟨343025, by rfl⟩ : syracuseStep 457367 = 686051) B686051
theorem B260779 : Blo 259821 260779 := bstep (se 1 (by rfl) ⟨195584, by rfl⟩ : syracuseStep 260779 = 391169) B391169
theorem B260791 : Blo 259821 260791 := bstep (se 1 (by rfl) ⟨195593, by rfl⟩ : syracuseStep 260791 = 391187) B391187
theorem B260811 : Blo 259821 260811 := bstep (se 1 (by rfl) ⟨195608, by rfl⟩ : syracuseStep 260811 = 391217) B391217
theorem B391883 : Blo 259821 391883 := bstep (se 1 (by rfl) ⟨293912, by rfl⟩ : syracuseStep 391883 = 587825) B587825
theorem B588491 : Blo 259821 588491 := bstep (se 1 (by rfl) ⟨441368, by rfl⟩ : syracuseStep 588491 = 882737) B882737
theorem B260823 : Blo 259821 260823 := bstep (se 1 (by rfl) ⟨195617, by rfl⟩ : syracuseStep 260823 = 391235) B391235
theorem B391895 : Blo 259821 391895 := bstep (se 1 (by rfl) ⟨293921, by rfl⟩ : syracuseStep 391895 = 587843) B587843
theorem B260843 : Blo 259821 260843 := bstep (se 1 (by rfl) ⟨195632, by rfl⟩ : syracuseStep 260843 = 391265) B391265
theorem B293611 : Blo 259821 293611 := bstep (se 1 (by rfl) ⟨220208, by rfl⟩ : syracuseStep 293611 = 440417) B440417
theorem B260855 : Blo 259821 260855 := bstep (se 1 (by rfl) ⟨195641, by rfl⟩ : syracuseStep 260855 = 391283) B391283
theorem B588545 : Blo 259821 588545 := bstep (se 2 (by rfl) ⟨220704, by rfl⟩ : syracuseStep 588545 = 441409) B441409
theorem B260875 : Blo 259821 260875 := bstep (se 1 (by rfl) ⟨195656, by rfl⟩ : syracuseStep 260875 = 391313) B391313
theorem B260887 : Blo 259821 260887 := bstep (se 1 (by rfl) ⟨195665, by rfl⟩ : syracuseStep 260887 = 391331) B391331
theorem B391961 : Blo 259821 391961 := bstep (se 2 (by rfl) ⟨146985, by rfl⟩ : syracuseStep 391961 = 293971) B293971
theorem B260907 : Blo 259821 260907 := bstep (se 1 (by rfl) ⟨195680, by rfl⟩ : syracuseStep 260907 = 391361) B391361
theorem B260919 : Blo 259821 260919 := bstep (se 1 (by rfl) ⟨195689, by rfl⟩ : syracuseStep 260919 = 391379) B391379
theorem B260939 : Blo 259821 260939 := bstep (se 1 (by rfl) ⟨195704, by rfl⟩ : syracuseStep 260939 = 391409) B391409
theorem B260951 : Blo 259821 260951 := bstep (se 1 (by rfl) ⟨195713, by rfl⟩ : syracuseStep 260951 = 391427) B391427
theorem B293719 : Blo 259821 293719 := bstep (se 1 (by rfl) ⟨220289, by rfl⟩ : syracuseStep 293719 = 440579) B440579
theorem B359257 : Blo 259821 359257 := bstep (se 2 (by rfl) ⟨134721, by rfl⟩ : syracuseStep 359257 = 269443) B269443
theorem B260971 : Blo 259821 260971 := bstep (se 1 (by rfl) ⟨195728, by rfl⟩ : syracuseStep 260971 = 391457) B391457
theorem B260983 : Blo 259821 260983 := bstep (se 1 (by rfl) ⟨195737, by rfl⟩ : syracuseStep 260983 = 391475) B391475
theorem B261003 : Blo 259821 261003 := bstep (se 1 (by rfl) ⟨195752, by rfl⟩ : syracuseStep 261003 = 391505) B391505
theorem B392075 : Blo 259821 392075 := bstep (se 1 (by rfl) ⟨294056, by rfl⟩ : syracuseStep 392075 = 588113) B588113
theorem B261015 : Blo 259821 261015 := bstep (se 1 (by rfl) ⟨195761, by rfl⟩ : syracuseStep 261015 = 391523) B391523
theorem B392087 : Blo 259821 392087 := bstep (se 1 (by rfl) ⟨294065, by rfl⟩ : syracuseStep 392087 = 588131) B588131
theorem B261035 : Blo 259821 261035 := bstep (se 1 (by rfl) ⟨195776, by rfl⟩ : syracuseStep 261035 = 391553) B391553
theorem B261047 : Blo 259821 261047 := bstep (se 1 (by rfl) ⟨195785, by rfl⟩ : syracuseStep 261047 = 391571) B391571
theorem B261067 : Blo 259821 261067 := bstep (se 1 (by rfl) ⟨195800, by rfl⟩ : syracuseStep 261067 = 391601) B391601
theorem B261079 : Blo 259821 261079 := bstep (se 1 (by rfl) ⟨195809, by rfl⟩ : syracuseStep 261079 = 391619) B391619
theorem B392153 : Blo 259821 392153 := bstep (se 2 (by rfl) ⟨147057, by rfl⟩ : syracuseStep 392153 = 294115) B294115
theorem B588761 : Blo 259821 588761 := bstep (se 2 (by rfl) ⟨220785, by rfl⟩ : syracuseStep 588761 = 441571) B441571
theorem B261099 : Blo 259821 261099 := bstep (se 1 (by rfl) ⟨195824, by rfl⟩ : syracuseStep 261099 = 391649) B391649
theorem B261111 : Blo 259821 261111 := bstep (se 1 (by rfl) ⟨195833, by rfl⟩ : syracuseStep 261111 = 391667) B391667
theorem B261131 : Blo 259821 261131 := bstep (se 1 (by rfl) ⟨195848, by rfl⟩ : syracuseStep 261131 = 391697) B391697
theorem B293899 : Blo 259821 293899 := bstep (se 1 (by rfl) ⟨220424, by rfl⟩ : syracuseStep 293899 = 440849) B440849
theorem B261143 : Blo 259821 261143 := bstep (se 1 (by rfl) ⟨195857, by rfl⟩ : syracuseStep 261143 = 391715) B391715
theorem B261163 : Blo 259821 261163 := bstep (se 1 (by rfl) ⟨195872, by rfl⟩ : syracuseStep 261163 = 391745) B391745
theorem B588851 : Blo 259821 588851 := bstep (se 1 (by rfl) ⟨441638, by rfl⟩ : syracuseStep 588851 = 883277) B883277
theorem B883763 : Blo 259821 883763 := bstep (se 1 (by rfl) ⟨662822, by rfl⟩ : syracuseStep 883763 = 1325645) B1325645
theorem B261175 : Blo 259821 261175 := bstep (se 1 (by rfl) ⟨195881, by rfl⟩ : syracuseStep 261175 = 391763) B391763
theorem B949313 : Blo 259821 949313 := bstep (se 2 (by rfl) ⟨355992, by rfl⟩ : syracuseStep 949313 = 711985) B711985
theorem B261195 : Blo 259821 261195 := bstep (se 1 (by rfl) ⟨195896, by rfl⟩ : syracuseStep 261195 = 391793) B391793
theorem B392267 : Blo 259821 392267 := bstep (se 1 (by rfl) ⟨294200, by rfl⟩ : syracuseStep 392267 = 588401) B588401
theorem B261207 : Blo 259821 261207 := bstep (se 1 (by rfl) ⟨195905, by rfl⟩ : syracuseStep 261207 = 391811) B391811
theorem B392279 : Blo 259821 392279 := bstep (se 1 (by rfl) ⟨294209, by rfl⟩ : syracuseStep 392279 = 588419) B588419
theorem B588887 : Blo 259821 588887 := bstep (se 1 (by rfl) ⟨441665, by rfl⟩ : syracuseStep 588887 = 883331) B883331
theorem B261227 : Blo 259821 261227 := bstep (se 1 (by rfl) ⟨195920, by rfl⟩ : syracuseStep 261227 = 391841) B391841
theorem B261239 : Blo 259821 261239 := bstep (se 1 (by rfl) ⟨195929, by rfl⟩ : syracuseStep 261239 = 391859) B391859
theorem B294007 : Blo 259821 294007 := bstep (se 1 (by rfl) ⟨220505, by rfl⟩ : syracuseStep 294007 = 441011) B441011
theorem B261259 : Blo 259821 261259 := bstep (se 1 (by rfl) ⟨195944, by rfl⟩ : syracuseStep 261259 = 391889) B391889
theorem B261271 : Blo 259821 261271 := bstep (se 1 (by rfl) ⟨195953, by rfl⟩ : syracuseStep 261271 = 391907) B391907
theorem B392345 : Blo 259821 392345 := bstep (se 2 (by rfl) ⟨147129, by rfl⟩ : syracuseStep 392345 = 294259) B294259
theorem B261291 : Blo 259821 261291 := bstep (se 1 (by rfl) ⟨195968, by rfl⟩ : syracuseStep 261291 = 391937) B391937
theorem B7699637 : Blo 259821 7699637 := bstep (se 5 (by rfl) ⟨360920, by rfl⟩ : syracuseStep 7699637 = 721841) B721841
theorem B261303 : Blo 259821 261303 := bstep (se 1 (by rfl) ⟨195977, by rfl⟩ : syracuseStep 261303 = 391955) B391955
theorem B261323 : Blo 259821 261323 := bstep (se 1 (by rfl) ⟨195992, by rfl⟩ : syracuseStep 261323 = 391985) B391985
theorem B261335 : Blo 259821 261335 := bstep (se 1 (by rfl) ⟨196001, by rfl⟩ : syracuseStep 261335 = 392003) B392003
theorem B261355 : Blo 259821 261355 := bstep (se 1 (by rfl) ⟨196016, by rfl⟩ : syracuseStep 261355 = 392033) B392033
theorem B261367 : Blo 259821 261367 := bstep (se 1 (by rfl) ⟨196025, by rfl⟩ : syracuseStep 261367 = 392051) B392051
theorem B261387 : Blo 259821 261387 := bstep (se 1 (by rfl) ⟨196040, by rfl⟩ : syracuseStep 261387 = 392081) B392081
theorem B392459 : Blo 259821 392459 := bstep (se 1 (by rfl) ⟨294344, by rfl⟩ : syracuseStep 392459 = 588689) B588689
theorem B589067 : Blo 259821 589067 := bstep (se 1 (by rfl) ⟨441800, by rfl⟩ : syracuseStep 589067 = 883601) B883601
theorem B261399 : Blo 259821 261399 := bstep (se 1 (by rfl) ⟨196049, by rfl⟩ : syracuseStep 261399 = 392099) B392099
theorem B392471 : Blo 259821 392471 := bstep (se 1 (by rfl) ⟨294353, by rfl⟩ : syracuseStep 392471 = 588707) B588707
theorem B261419 : Blo 259821 261419 := bstep (se 1 (by rfl) ⟨196064, by rfl⟩ : syracuseStep 261419 = 392129) B392129
theorem B294187 : Blo 259821 294187 := bstep (se 1 (by rfl) ⟨220640, by rfl⟩ : syracuseStep 294187 = 441281) B441281
theorem B1113389 : Blo 259821 1113389 := bstep (se 3 (by rfl) ⟨208760, by rfl⟩ : syracuseStep 1113389 = 417521) B417521
theorem B261431 : Blo 259821 261431 := bstep (se 1 (by rfl) ⟨196073, by rfl⟩ : syracuseStep 261431 = 392147) B392147
theorem B589121 : Blo 259821 589121 := bstep (se 2 (by rfl) ⟨220920, by rfl⟩ : syracuseStep 589121 = 441841) B441841
theorem B884033 : Blo 259821 884033 := bstep (se 2 (by rfl) ⟨331512, by rfl⟩ : syracuseStep 884033 = 663025) B663025
theorem B261451 : Blo 259821 261451 := bstep (se 1 (by rfl) ⟨196088, by rfl⟩ : syracuseStep 261451 = 392177) B392177
theorem B261463 : Blo 259821 261463 := bstep (se 1 (by rfl) ⟨196097, by rfl⟩ : syracuseStep 261463 = 392195) B392195
theorem B392537 : Blo 259821 392537 := bstep (se 2 (by rfl) ⟨147201, by rfl⟩ : syracuseStep 392537 = 294403) B294403
theorem B752989 : Blo 259821 752989 := bstep (se 3 (by rfl) ⟨141185, by rfl⟩ : syracuseStep 752989 = 282371) B282371
theorem B261483 : Blo 259821 261483 := bstep (se 1 (by rfl) ⟨196112, by rfl⟩ : syracuseStep 261483 = 392225) B392225
theorem B261495 : Blo 259821 261495 := bstep (se 1 (by rfl) ⟨196121, by rfl⟩ : syracuseStep 261495 = 392243) B392243
theorem B261515 : Blo 259821 261515 := bstep (se 1 (by rfl) ⟨196136, by rfl⟩ : syracuseStep 261515 = 392273) B392273
theorem B261527 : Blo 259821 261527 := bstep (se 1 (by rfl) ⟨196145, by rfl⟩ : syracuseStep 261527 = 392291) B392291
theorem B294295 : Blo 259821 294295 := bstep (se 1 (by rfl) ⟨220721, by rfl⟩ : syracuseStep 294295 = 441443) B441443
theorem B261547 : Blo 259821 261547 := bstep (se 1 (by rfl) ⟨196160, by rfl⟩ : syracuseStep 261547 = 392321) B392321
theorem B261559 : Blo 259821 261559 := bstep (se 1 (by rfl) ⟨196169, by rfl⟩ : syracuseStep 261559 = 392339) B392339
theorem B261579 : Blo 259821 261579 := bstep (se 1 (by rfl) ⟨196184, by rfl⟩ : syracuseStep 261579 = 392369) B392369
theorem B392651 : Blo 259821 392651 := bstep (se 1 (by rfl) ⟨294488, by rfl⟩ : syracuseStep 392651 = 588977) B588977
theorem B261591 : Blo 259821 261591 := bstep (se 1 (by rfl) ⟨196193, by rfl⟩ : syracuseStep 261591 = 392387) B392387
theorem B392663 : Blo 259821 392663 := bstep (se 1 (by rfl) ⟨294497, by rfl⟩ : syracuseStep 392663 = 588995) B588995
theorem B261611 : Blo 259821 261611 := bstep (se 1 (by rfl) ⟨196208, by rfl⟩ : syracuseStep 261611 = 392417) B392417
theorem B261623 : Blo 259821 261623 := bstep (se 1 (by rfl) ⟨196217, by rfl⟩ : syracuseStep 261623 = 392435) B392435
theorem B261643 : Blo 259821 261643 := bstep (se 1 (by rfl) ⟨196232, by rfl⟩ : syracuseStep 261643 = 392465) B392465
theorem B261655 : Blo 259821 261655 := bstep (se 1 (by rfl) ⟨196241, by rfl⟩ : syracuseStep 261655 = 392483) B392483
theorem B392729 : Blo 259821 392729 := bstep (se 2 (by rfl) ⟨147273, by rfl⟩ : syracuseStep 392729 = 294547) B294547
theorem B589337 : Blo 259821 589337 := bstep (se 2 (by rfl) ⟨221001, by rfl⟩ : syracuseStep 589337 = 442003) B442003
theorem B261675 : Blo 259821 261675 := bstep (se 1 (by rfl) ⟨196256, by rfl⟩ : syracuseStep 261675 = 392513) B392513
theorem B261687 : Blo 259821 261687 := bstep (se 1 (by rfl) ⟨196265, by rfl⟩ : syracuseStep 261687 = 392531) B392531
theorem B261707 : Blo 259821 261707 := bstep (se 1 (by rfl) ⟨196280, by rfl⟩ : syracuseStep 261707 = 392561) B392561
theorem B294475 : Blo 259821 294475 := bstep (se 1 (by rfl) ⟨220856, by rfl⟩ : syracuseStep 294475 = 441713) B441713
theorem B261719 : Blo 259821 261719 := bstep (se 1 (by rfl) ⟨196289, by rfl⟩ : syracuseStep 261719 = 392579) B392579
theorem B261739 : Blo 259821 261739 := bstep (se 1 (by rfl) ⟨196304, by rfl⟩ : syracuseStep 261739 = 392609) B392609
theorem B589427 : Blo 259821 589427 := bstep (se 1 (by rfl) ⟨442070, by rfl⟩ : syracuseStep 589427 = 884141) B884141
theorem B261751 : Blo 259821 261751 := bstep (se 1 (by rfl) ⟨196313, by rfl⟩ : syracuseStep 261751 = 392627) B392627
theorem B261771 : Blo 259821 261771 := bstep (se 1 (by rfl) ⟨196328, by rfl⟩ : syracuseStep 261771 = 392657) B392657
theorem B392843 : Blo 259821 392843 := bstep (se 1 (by rfl) ⟨294632, by rfl⟩ : syracuseStep 392843 = 589265) B589265
theorem B261783 : Blo 259821 261783 := bstep (se 1 (by rfl) ⟨196337, by rfl⟩ : syracuseStep 261783 = 392675) B392675
theorem B392855 : Blo 259821 392855 := bstep (se 1 (by rfl) ⟨294641, by rfl⟩ : syracuseStep 392855 = 589283) B589283
theorem B589463 : Blo 259821 589463 := bstep (se 1 (by rfl) ⟨442097, by rfl⟩ : syracuseStep 589463 = 884195) B884195
theorem B261803 : Blo 259821 261803 := bstep (se 1 (by rfl) ⟨196352, by rfl⟩ : syracuseStep 261803 = 392705) B392705
theorem B261815 : Blo 259821 261815 := bstep (se 1 (by rfl) ⟨196361, by rfl⟩ : syracuseStep 261815 = 392723) B392723
theorem B294583 : Blo 259821 294583 := bstep (se 1 (by rfl) ⟨220937, by rfl⟩ : syracuseStep 294583 = 441875) B441875
theorem B261835 : Blo 259821 261835 := bstep (se 1 (by rfl) ⟨196376, by rfl⟩ : syracuseStep 261835 = 392753) B392753
theorem B261847 : Blo 259821 261847 := bstep (se 1 (by rfl) ⟨196385, by rfl⟩ : syracuseStep 261847 = 392771) B392771
theorem B392921 : Blo 259821 392921 := bstep (se 2 (by rfl) ⟨147345, by rfl⟩ : syracuseStep 392921 = 294691) B294691
theorem B261867 : Blo 259821 261867 := bstep (se 1 (by rfl) ⟨196400, by rfl⟩ : syracuseStep 261867 = 392801) B392801
theorem B261879 : Blo 259821 261879 := bstep (se 1 (by rfl) ⟨196409, by rfl⟩ : syracuseStep 261879 = 392819) B392819
theorem B261899 : Blo 259821 261899 := bstep (se 1 (by rfl) ⟨196424, by rfl⟩ : syracuseStep 261899 = 392849) B392849
theorem B261911 : Blo 259821 261911 := bstep (se 1 (by rfl) ⟨196433, by rfl⟩ : syracuseStep 261911 = 392867) B392867
theorem B261931 : Blo 259821 261931 := bstep (se 1 (by rfl) ⟨196448, by rfl⟩ : syracuseStep 261931 = 392897) B392897
theorem B261943 : Blo 259821 261943 := bstep (se 1 (by rfl) ⟨196457, by rfl⟩ : syracuseStep 261943 = 392915) B392915
theorem B261963 : Blo 259821 261963 := bstep (se 1 (by rfl) ⟨196472, by rfl⟩ : syracuseStep 261963 = 392945) B392945
theorem B393035 : Blo 259821 393035 := bstep (se 1 (by rfl) ⟨294776, by rfl⟩ : syracuseStep 393035 = 589553) B589553
theorem B589643 : Blo 259821 589643 := bstep (se 1 (by rfl) ⟨442232, by rfl⟩ : syracuseStep 589643 = 884465) B884465
theorem B261975 : Blo 259821 261975 := bstep (se 1 (by rfl) ⟨196481, by rfl⟩ : syracuseStep 261975 = 392963) B392963
theorem B393047 : Blo 259821 393047 := bstep (se 1 (by rfl) ⟨294785, by rfl⟩ : syracuseStep 393047 = 589571) B589571
theorem B1671005 : Blo 259821 1671005 := bstep (se 3 (by rfl) ⟨313313, by rfl⟩ : syracuseStep 1671005 = 626627) B626627
theorem B884573 : Blo 259821 884573 := bstep (se 3 (by rfl) ⟨165857, by rfl⟩ : syracuseStep 884573 = 331715) B331715
theorem B261995 : Blo 259821 261995 := bstep (se 1 (by rfl) ⟨196496, by rfl⟩ : syracuseStep 261995 = 392993) B392993
theorem B294763 : Blo 259821 294763 := bstep (se 1 (by rfl) ⟨221072, by rfl⟩ : syracuseStep 294763 = 442145) B442145
theorem B262007 : Blo 259821 262007 := bstep (se 1 (by rfl) ⟨196505, by rfl⟩ : syracuseStep 262007 = 393011) B393011
theorem B589697 : Blo 259821 589697 := bstep (se 2 (by rfl) ⟨221136, by rfl⟩ : syracuseStep 589697 = 442273) B442273
theorem B262027 : Blo 259821 262027 := bstep (se 1 (by rfl) ⟨196520, by rfl⟩ : syracuseStep 262027 = 393041) B393041
theorem B556951 : Blo 259821 556951 := bstep (se 1 (by rfl) ⟨417713, by rfl⟩ : syracuseStep 556951 = 835427) B835427
theorem B262039 : Blo 259821 262039 := bstep (se 1 (by rfl) ⟨196529, by rfl⟩ : syracuseStep 262039 = 393059) B393059
theorem B393113 : Blo 259821 393113 := bstep (se 2 (by rfl) ⟨147417, by rfl⟩ : syracuseStep 393113 = 294835) B294835
theorem B262059 : Blo 259821 262059 := bstep (se 1 (by rfl) ⟨196544, by rfl⟩ : syracuseStep 262059 = 393089) B393089
theorem B262071 : Blo 259821 262071 := bstep (se 1 (by rfl) ⟨196553, by rfl⟩ : syracuseStep 262071 = 393107) B393107
theorem B262091 : Blo 259821 262091 := bstep (se 1 (by rfl) ⟨196568, by rfl⟩ : syracuseStep 262091 = 393137) B393137
theorem B262103 : Blo 259821 262103 := bstep (se 1 (by rfl) ⟨196577, by rfl⟩ : syracuseStep 262103 = 393155) B393155
theorem B294871 : Blo 259821 294871 := bstep (se 1 (by rfl) ⟨221153, by rfl⟩ : syracuseStep 294871 = 442307) B442307
theorem B1114073 : Blo 259821 1114073 := bstep (se 2 (by rfl) ⟨417777, by rfl⟩ : syracuseStep 1114073 = 835555) B835555
theorem B950237 : Blo 259821 950237 := bstep (se 3 (by rfl) ⟨178169, by rfl⟩ : syracuseStep 950237 = 356339) B356339
theorem B262123 : Blo 259821 262123 := bstep (se 1 (by rfl) ⟨196592, by rfl⟩ : syracuseStep 262123 = 393185) B393185
theorem B262135 : Blo 259821 262135 := bstep (se 1 (by rfl) ⟨196601, by rfl⟩ : syracuseStep 262135 = 393203) B393203
theorem B262151 : Blo 259821 262151 := bstep (se 1 (by rfl) ⟨196613, by rfl⟩ : syracuseStep 262151 = 393227) B393227
theorem B262159 : Blo 259821 262159 := bstep (se 1 (by rfl) ⟨196619, by rfl⟩ : syracuseStep 262159 = 393239) B393239
theorem B393275 : Blo 259821 393275 := bstep (se 1 (by rfl) ⟨294956, by rfl⟩ : syracuseStep 393275 = 589913) B589913
theorem B262203 : Blo 259821 262203 := bstep (se 1 (by rfl) ⟨196652, by rfl⟩ : syracuseStep 262203 = 393305) B393305
theorem B393335 : Blo 259821 393335 := bstep (se 1 (by rfl) ⟨295001, by rfl⟩ : syracuseStep 393335 = 590003) B590003
theorem B262279 : Blo 259821 262279 := bstep (se 1 (by rfl) ⟨196709, by rfl⟩ : syracuseStep 262279 = 393419) B393419
theorem B393359 : Blo 259821 393359 := bstep (se 1 (by rfl) ⟨295019, by rfl⟩ : syracuseStep 393359 = 590039) B590039
theorem B262287 : Blo 259821 262287 := bstep (se 1 (by rfl) ⟨196715, by rfl⟩ : syracuseStep 262287 = 393431) B393431
theorem B393401 : Blo 259821 393401 := bstep (se 2 (by rfl) ⟨147525, by rfl⟩ : syracuseStep 393401 = 295051) B295051
theorem B262331 : Blo 259821 262331 := bstep (se 1 (by rfl) ⟨196748, by rfl⟩ : syracuseStep 262331 = 393497) B393497
theorem B393479 : Blo 259821 393479 := bstep (se 1 (by rfl) ⟨295109, by rfl⟩ : syracuseStep 393479 = 590219) B590219
theorem B262407 : Blo 259821 262407 := bstep (se 1 (by rfl) ⟨196805, by rfl⟩ : syracuseStep 262407 = 393611) B393611
theorem B262415 : Blo 259821 262415 := bstep (se 1 (by rfl) ⟨196811, by rfl⟩ : syracuseStep 262415 = 393623) B393623
theorem B393515 : Blo 259821 393515 := bstep (se 1 (by rfl) ⟨295136, by rfl⟩ : syracuseStep 393515 = 590273) B590273
theorem B262459 : Blo 259821 262459 := bstep (se 1 (by rfl) ⟨196844, by rfl⟩ : syracuseStep 262459 = 393689) B393689
theorem B393545 : Blo 259821 393545 := bstep (se 2 (by rfl) ⟨147579, by rfl⟩ : syracuseStep 393545 = 295159) B295159
theorem B295303 : Blo 259821 295303 := bstep (se 1 (by rfl) ⟨221477, by rfl⟩ : syracuseStep 295303 = 442955) B442955
theorem B262535 : Blo 259821 262535 := bstep (se 1 (by rfl) ⟨196901, by rfl⟩ : syracuseStep 262535 = 393803) B393803
theorem B262543 : Blo 259821 262543 := bstep (se 1 (by rfl) ⟨196907, by rfl⟩ : syracuseStep 262543 = 393815) B393815
theorem B393659 : Blo 259821 393659 := bstep (se 1 (by rfl) ⟨295244, by rfl⟩ : syracuseStep 393659 = 590489) B590489
theorem B262587 : Blo 259821 262587 := bstep (se 1 (by rfl) ⟨196940, by rfl⟩ : syracuseStep 262587 = 393881) B393881
theorem B393719 : Blo 259821 393719 := bstep (se 1 (by rfl) ⟨295289, by rfl⟩ : syracuseStep 393719 = 590579) B590579
theorem B262663 : Blo 259821 262663 := bstep (se 1 (by rfl) ⟨196997, by rfl⟩ : syracuseStep 262663 = 393995) B393995
theorem B393743 : Blo 259821 393743 := bstep (se 1 (by rfl) ⟨295307, by rfl⟩ : syracuseStep 393743 = 590615) B590615
theorem B262671 : Blo 259821 262671 := bstep (se 1 (by rfl) ⟨197003, by rfl⟩ : syracuseStep 262671 = 394007) B394007
theorem B1999403 : Blo 259821 1999403 := bstep (se 1 (by rfl) ⟨1499552, by rfl⟩ : syracuseStep 1999403 = 2999105) B2999105
theorem B393785 : Blo 259821 393785 := bstep (se 2 (by rfl) ⟨147669, by rfl⟩ : syracuseStep 393785 = 295339) B295339
theorem B295483 : Blo 259821 295483 := bstep (se 1 (by rfl) ⟨221612, by rfl⟩ : syracuseStep 295483 = 443225) B443225
theorem B262715 : Blo 259821 262715 := bstep (se 1 (by rfl) ⟨197036, by rfl⟩ : syracuseStep 262715 = 394073) B394073
theorem B590471 : Blo 259821 590471 := bstep (se 1 (by rfl) ⟨442853, by rfl⟩ : syracuseStep 590471 = 885707) B885707
theorem B393863 : Blo 259821 393863 := bstep (se 1 (by rfl) ⟨295397, by rfl⟩ : syracuseStep 393863 = 590795) B590795
theorem B262791 : Blo 259821 262791 := bstep (se 1 (by rfl) ⟨197093, by rfl⟩ : syracuseStep 262791 = 394187) B394187
theorem B262799 : Blo 259821 262799 := bstep (se 1 (by rfl) ⟨197099, by rfl⟩ : syracuseStep 262799 = 394199) B394199
theorem B393899 : Blo 259821 393899 := bstep (se 1 (by rfl) ⟨295424, by rfl⟩ : syracuseStep 393899 = 590849) B590849
theorem B262843 : Blo 259821 262843 := bstep (se 1 (by rfl) ⟨197132, by rfl⟩ : syracuseStep 262843 = 394265) B394265
theorem B393929 : Blo 259821 393929 := bstep (se 2 (by rfl) ⟨147723, by rfl⟩ : syracuseStep 393929 = 295447) B295447
theorem B262919 : Blo 259821 262919 := bstep (se 1 (by rfl) ⟨197189, by rfl⟩ : syracuseStep 262919 = 394379) B394379
theorem B262927 : Blo 259821 262927 := bstep (se 1 (by rfl) ⟨197195, by rfl⟩ : syracuseStep 262927 = 394391) B394391
theorem B590651 : Blo 259821 590651 := bstep (se 1 (by rfl) ⟨442988, by rfl⟩ : syracuseStep 590651 = 885977) B885977
theorem B394043 : Blo 259821 394043 := bstep (se 1 (by rfl) ⟨295532, by rfl⟩ : syracuseStep 394043 = 591065) B591065
theorem B262971 : Blo 259821 262971 := bstep (se 1 (by rfl) ⟨197228, by rfl⟩ : syracuseStep 262971 = 394457) B394457
theorem B3343193 : Blo 259821 3343193 := bstep (se 2 (by rfl) ⟨1253697, by rfl⟩ : syracuseStep 3343193 = 2507395) B2507395
theorem B394103 : Blo 259821 394103 := bstep (se 1 (by rfl) ⟨295577, by rfl⟩ : syracuseStep 394103 = 591155) B591155
theorem B263047 : Blo 259821 263047 := bstep (se 1 (by rfl) ⟨197285, by rfl⟩ : syracuseStep 263047 = 394571) B394571
theorem B394127 : Blo 259821 394127 := bstep (se 1 (by rfl) ⟨295595, by rfl⟩ : syracuseStep 394127 = 591191) B591191
theorem B263055 : Blo 259821 263055 := bstep (se 1 (by rfl) ⟨197291, by rfl⟩ : syracuseStep 263055 = 394583) B394583
theorem B590777 : Blo 259821 590777 := bstep (se 2 (by rfl) ⟨221541, by rfl⟩ : syracuseStep 590777 = 443083) B443083
theorem B394169 : Blo 259821 394169 := bstep (se 2 (by rfl) ⟨147813, by rfl⟩ : syracuseStep 394169 = 295627) B295627
theorem B263099 : Blo 259821 263099 := bstep (se 1 (by rfl) ⟨197324, by rfl⟩ : syracuseStep 263099 = 394649) B394649
theorem B394247 : Blo 259821 394247 := bstep (se 1 (by rfl) ⟨295685, by rfl⟩ : syracuseStep 394247 = 591371) B591371
theorem B263175 : Blo 259821 263175 := bstep (se 1 (by rfl) ⟨197381, by rfl⟩ : syracuseStep 263175 = 394763) B394763
theorem B558095 : Blo 259821 558095 := bstep (se 1 (by rfl) ⟨418571, by rfl⟩ : syracuseStep 558095 = 837143) B837143
theorem B295951 : Blo 259821 295951 := bstep (se 1 (by rfl) ⟨221963, by rfl⟩ : syracuseStep 295951 = 443927) B443927
theorem B263183 : Blo 259821 263183 := bstep (se 1 (by rfl) ⟨197387, by rfl⟩ : syracuseStep 263183 = 394775) B394775
theorem B394283 : Blo 259821 394283 := bstep (se 1 (by rfl) ⟨295712, by rfl⟩ : syracuseStep 394283 = 591425) B591425
theorem B263227 : Blo 259821 263227 := bstep (se 1 (by rfl) ⟨197420, by rfl⟩ : syracuseStep 263227 = 394841) B394841
theorem B394313 : Blo 259821 394313 := bstep (se 2 (by rfl) ⟨147867, by rfl⟩ : syracuseStep 394313 = 295735) B295735
theorem B3245143 : Blo 259821 3245143 := bstep (se 1 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 3245143 = 4867715) B4867715
theorem B263303 : Blo 259821 263303 := bstep (se 1 (by rfl) ⟨197477, by rfl⟩ : syracuseStep 263303 = 394955) B394955
theorem B263311 : Blo 259821 263311 := bstep (se 1 (by rfl) ⟨197483, by rfl⟩ : syracuseStep 263311 = 394967) B394967
theorem B394427 : Blo 259821 394427 := bstep (se 1 (by rfl) ⟨295820, by rfl⟩ : syracuseStep 394427 = 591641) B591641
theorem B263355 : Blo 259821 263355 := bstep (se 1 (by rfl) ⟨197516, by rfl⟩ : syracuseStep 263355 = 395033) B395033
theorem B328951 : Blo 259821 328951 := bstep (se 1 (by rfl) ⟨246713, by rfl⟩ : syracuseStep 328951 = 493427) B493427
theorem B394487 : Blo 259821 394487 := bstep (se 1 (by rfl) ⟨295865, by rfl⟩ : syracuseStep 394487 = 591731) B591731
theorem B263431 : Blo 259821 263431 := bstep (se 1 (by rfl) ⟨197573, by rfl⟩ : syracuseStep 263431 = 395147) B395147
theorem B886031 : Blo 259821 886031 := bstep (se 1 (by rfl) ⟨664523, by rfl⟩ : syracuseStep 886031 = 1329047) B1329047
theorem B591119 : Blo 259821 591119 := bstep (se 1 (by rfl) ⟨443339, by rfl⟩ : syracuseStep 591119 = 886679) B886679
theorem B394511 : Blo 259821 394511 := bstep (se 1 (by rfl) ⟨295883, by rfl⟩ : syracuseStep 394511 = 591767) B591767
theorem B263439 : Blo 259821 263439 := bstep (se 1 (by rfl) ⟨197579, by rfl⟩ : syracuseStep 263439 = 395159) B395159
theorem B591137 : Blo 259821 591137 := bstep (se 2 (by rfl) ⟨221676, by rfl⟩ : syracuseStep 591137 = 443353) B443353
theorem B394553 : Blo 259821 394553 := bstep (se 2 (by rfl) ⟨147957, by rfl⟩ : syracuseStep 394553 = 295915) B295915
theorem B263483 : Blo 259821 263483 := bstep (se 1 (by rfl) ⟨197612, by rfl⟩ : syracuseStep 263483 = 395225) B395225
theorem B1115507 : Blo 259821 1115507 := bstep (se 1 (by rfl) ⟨836630, by rfl⟩ : syracuseStep 1115507 = 1673261) B1673261
theorem B394631 : Blo 259821 394631 := bstep (se 1 (by rfl) ⟨295973, by rfl⟩ : syracuseStep 394631 = 591947) B591947
theorem B263559 : Blo 259821 263559 := bstep (se 1 (by rfl) ⟨197669, by rfl⟩ : syracuseStep 263559 = 395339) B395339
theorem B263567 : Blo 259821 263567 := bstep (se 1 (by rfl) ⟨197675, by rfl⟩ : syracuseStep 263567 = 395351) B395351
theorem B394667 : Blo 259821 394667 := bstep (se 1 (by rfl) ⟨296000, by rfl⟩ : syracuseStep 394667 = 592001) B592001
theorem B263611 : Blo 259821 263611 := bstep (se 1 (by rfl) ⟨197708, by rfl⟩ : syracuseStep 263611 = 395417) B395417
theorem B394697 : Blo 259821 394697 := bstep (se 2 (by rfl) ⟨148011, by rfl⟩ : syracuseStep 394697 = 296023) B296023
theorem B296455 : Blo 259821 296455 := bstep (se 1 (by rfl) ⟨222341, by rfl⟩ : syracuseStep 296455 = 444683) B444683
theorem B263687 : Blo 259821 263687 := bstep (se 1 (by rfl) ⟨197765, by rfl⟩ : syracuseStep 263687 = 395531) B395531
theorem B263695 : Blo 259821 263695 := bstep (se 1 (by rfl) ⟨197771, by rfl⟩ : syracuseStep 263695 = 395543) B395543
theorem B886301 : Blo 259821 886301 := bstep (se 3 (by rfl) ⟨166181, by rfl⟩ : syracuseStep 886301 = 332363) B332363
theorem B329275 : Blo 259821 329275 := bstep (se 1 (by rfl) ⟨246956, by rfl⟩ : syracuseStep 329275 = 493913) B493913
theorem B394811 : Blo 259821 394811 := bstep (se 1 (by rfl) ⟨296108, by rfl⟩ : syracuseStep 394811 = 592217) B592217
theorem B263739 : Blo 259821 263739 := bstep (se 1 (by rfl) ⟨197804, by rfl⟩ : syracuseStep 263739 = 395609) B395609
theorem B5375587 : Blo 259821 5375587 := bstep (se 1 (by rfl) ⟨4031690, by rfl⟩ : syracuseStep 5375587 = 8063381) B8063381
theorem B591479 : Blo 259821 591479 := bstep (se 1 (by rfl) ⟨443609, by rfl⟩ : syracuseStep 591479 = 887219) B887219
theorem B394871 : Blo 259821 394871 := bstep (se 1 (by rfl) ⟨296153, by rfl⟩ : syracuseStep 394871 = 592307) B592307
theorem B263815 : Blo 259821 263815 := bstep (se 1 (by rfl) ⟨197861, by rfl⟩ : syracuseStep 263815 = 395723) B395723
theorem B394895 : Blo 259821 394895 := bstep (se 1 (by rfl) ⟨296171, by rfl⟩ : syracuseStep 394895 = 592343) B592343
theorem B394937 : Blo 259821 394937 := bstep (se 2 (by rfl) ⟨148101, by rfl⟩ : syracuseStep 394937 = 296203) B296203
theorem B296635 : Blo 259821 296635 := bstep (se 1 (by rfl) ⟨222476, by rfl⟩ : syracuseStep 296635 = 444953) B444953
theorem B1115849 : Blo 259821 1115849 := bstep (se 2 (by rfl) ⟨418443, by rfl⟩ : syracuseStep 1115849 = 836887) B836887
theorem B395015 : Blo 259821 395015 := bstep (se 1 (by rfl) ⟨296261, by rfl⟩ : syracuseStep 395015 = 592523) B592523
theorem B591659 : Blo 259821 591659 := bstep (se 1 (by rfl) ⟨443744, by rfl⟩ : syracuseStep 591659 = 887489) B887489
theorem B395051 : Blo 259821 395051 := bstep (se 1 (by rfl) ⟨296288, by rfl⟩ : syracuseStep 395051 = 592577) B592577
theorem B395081 : Blo 259821 395081 := bstep (se 2 (by rfl) ⟨148155, by rfl⟩ : syracuseStep 395081 = 296311) B296311
theorem B2131865 : Blo 259821 2131865 := bstep (se 2 (by rfl) ⟨799449, by rfl⟩ : syracuseStep 2131865 = 1598899) B1598899
theorem B1116089 : Blo 259821 1116089 := bstep (se 2 (by rfl) ⟨418533, by rfl⟩ : syracuseStep 1116089 = 837067) B837067
theorem B395195 : Blo 259821 395195 := bstep (se 1 (by rfl) ⟨296396, by rfl⟩ : syracuseStep 395195 = 592793) B592793
theorem B395255 : Blo 259821 395255 := bstep (se 1 (by rfl) ⟨296441, by rfl⟩ : syracuseStep 395255 = 592883) B592883
theorem B395279 : Blo 259821 395279 := bstep (se 1 (by rfl) ⟨296459, by rfl⟩ : syracuseStep 395279 = 592919) B592919
theorem B329771 : Blo 259821 329771 := bstep (se 1 (by rfl) ⟨247328, by rfl⟩ : syracuseStep 329771 = 494657) B494657
theorem B395321 : Blo 259821 395321 := bstep (se 2 (by rfl) ⟨148245, by rfl⟩ : syracuseStep 395321 = 296491) B296491
theorem B395399 : Blo 259821 395399 := bstep (se 1 (by rfl) ⟨296549, by rfl⟩ : syracuseStep 395399 = 593099) B593099
theorem B493715 : Blo 259821 493715 := bstep (se 1 (by rfl) ⟨370286, by rfl⟩ : syracuseStep 493715 = 740573) B740573
theorem B592019 : Blo 259821 592019 := bstep (se 1 (by rfl) ⟨444014, by rfl⟩ : syracuseStep 592019 = 888029) B888029
theorem B395435 : Blo 259821 395435 := bstep (se 1 (by rfl) ⟨296576, by rfl⟩ : syracuseStep 395435 = 593153) B593153
theorem B493769 : Blo 259821 493769 := bstep (se 2 (by rfl) ⟨185163, by rfl⟩ : syracuseStep 493769 = 370327) B370327
theorem B592073 : Blo 259821 592073 := bstep (se 2 (by rfl) ⟨222027, by rfl⟩ : syracuseStep 592073 = 444055) B444055
theorem B395465 : Blo 259821 395465 := bstep (se 2 (by rfl) ⟨148299, by rfl⟩ : syracuseStep 395465 = 296599) B296599
theorem B657679 : Blo 259821 657679 := bstep (se 1 (by rfl) ⟨493259, by rfl⟩ : syracuseStep 657679 = 986519) B986519
theorem B1116449 : Blo 259821 1116449 := bstep (se 2 (by rfl) ⟨418668, by rfl⟩ : syracuseStep 1116449 = 837337) B837337
theorem B493867 : Blo 259821 493867 := bstep (se 1 (by rfl) ⟨370400, by rfl⟩ : syracuseStep 493867 = 740801) B740801
theorem B395579 : Blo 259821 395579 := bstep (se 1 (by rfl) ⟨296684, by rfl⟩ : syracuseStep 395579 = 593369) B593369
theorem B395639 : Blo 259821 395639 := bstep (se 1 (by rfl) ⟨296729, by rfl⟩ : syracuseStep 395639 = 593459) B593459
theorem B2525575 : Blo 259821 2525575 := bstep (se 1 (by rfl) ⟨1894181, by rfl⟩ : syracuseStep 2525575 = 3788363) B3788363
theorem B395663 : Blo 259821 395663 := bstep (se 1 (by rfl) ⟨296747, by rfl⟩ : syracuseStep 395663 = 593495) B593495
theorem B395705 : Blo 259821 395705 := bstep (se 2 (by rfl) ⟨148389, by rfl⟩ : syracuseStep 395705 = 296779) B296779
theorem B330247 : Blo 259821 330247 := bstep (se 1 (by rfl) ⟨247685, by rfl⟩ : syracuseStep 330247 = 495371) B495371
theorem B494095 : Blo 259821 494095 := bstep (se 1 (by rfl) ⟨370571, by rfl⟩ : syracuseStep 494095 = 741143) B741143
theorem B657953 : Blo 259821 657953 := bstep (se 2 (by rfl) ⟨246732, by rfl⟩ : syracuseStep 657953 = 493465) B493465
theorem B2984525 : Blo 259821 2984525 := bstep (se 3 (by rfl) ⟨559598, by rfl⟩ : syracuseStep 2984525 = 1119197) B1119197
theorem B1903409 : Blo 259821 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B592775 : Blo 259821 592775 := bstep (se 1 (by rfl) ⟨444581, by rfl⟩ : syracuseStep 592775 = 889163) B889163
theorem B887705 : Blo 259821 887705 := bstep (se 2 (by rfl) ⟨332889, by rfl⟩ : syracuseStep 887705 = 665779) B665779
theorem B330743 : Blo 259821 330743 := bstep (se 1 (by rfl) ⟨248057, by rfl⟩ : syracuseStep 330743 = 496115) B496115
theorem B265231 : Blo 259821 265231 := bstep (se 1 (by rfl) ⟨198923, by rfl⟩ : syracuseStep 265231 = 397847) B397847
theorem B592955 : Blo 259821 592955 := bstep (se 1 (by rfl) ⟨444716, by rfl⟩ : syracuseStep 592955 = 889433) B889433
theorem B330895 : Blo 259821 330895 := bstep (se 1 (by rfl) ⟨248171, by rfl⟩ : syracuseStep 330895 = 496343) B496343
theorem B593081 : Blo 259821 593081 := bstep (se 2 (by rfl) ⟨222405, by rfl⟩ : syracuseStep 593081 = 444811) B444811
theorem B1412333 : Blo 259821 1412333 := bstep (se 3 (by rfl) ⟨264812, by rfl⟩ : syracuseStep 1412333 = 529625) B529625
theorem B1117421 : Blo 259821 1117421 := bstep (se 3 (by rfl) ⟨209516, by rfl⟩ : syracuseStep 1117421 = 419033) B419033
theorem B331067 : Blo 259821 331067 := bstep (se 1 (by rfl) ⟨248300, by rfl⟩ : syracuseStep 331067 = 496601) B496601
theorem B658955 : Blo 259821 658955 := bstep (se 1 (by rfl) ⟨494216, by rfl⟩ : syracuseStep 658955 = 988433) B988433
theorem B593423 : Blo 259821 593423 := bstep (se 1 (by rfl) ⟨445067, by rfl⟩ : syracuseStep 593423 = 890135) B890135
theorem B593441 : Blo 259821 593441 := bstep (se 2 (by rfl) ⟨222540, by rfl⟩ : syracuseStep 593441 = 445081) B445081
theorem B1117763 : Blo 259821 1117763 := bstep (se 1 (by rfl) ⟨838322, by rfl⟩ : syracuseStep 1117763 = 1676645) B1676645
theorem B888407 : Blo 259821 888407 := bstep (se 1 (by rfl) ⟨666305, by rfl⟩ : syracuseStep 888407 = 1332611) B1332611
theorem B397001 : Blo 259821 397001 := bstep (se 2 (by rfl) ⟨148875, by rfl⟩ : syracuseStep 397001 = 297751) B297751
theorem B1281737 : Blo 259821 1281737 := bstep (se 2 (by rfl) ⟨480651, by rfl⟩ : syracuseStep 1281737 = 961303) B961303
theorem B855841 : Blo 259821 855841 := bstep (se 2 (by rfl) ⟨320940, by rfl⟩ : syracuseStep 855841 = 641881) B641881
theorem B5476247 : Blo 259821 5476247 := bstep (se 1 (by rfl) ⟨4107185, by rfl⟩ : syracuseStep 5476247 = 8214371) B8214371
theorem B7606219 : Blo 259821 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B495659 : Blo 259821 495659 := bstep (se 1 (by rfl) ⟨371744, by rfl⟩ : syracuseStep 495659 = 743489) B743489
theorem B888893 : Blo 259821 888893 := bstep (se 3 (by rfl) ⟨166667, by rfl⟩ : syracuseStep 888893 = 333335) B333335
theorem B659603 : Blo 259821 659603 := bstep (se 1 (by rfl) ⟨494702, by rfl⟩ : syracuseStep 659603 = 989405) B989405
theorem B332039 : Blo 259821 332039 := bstep (se 1 (by rfl) ⟨249029, by rfl⟩ : syracuseStep 332039 = 498059) B498059
theorem B627031 : Blo 259821 627031 := bstep (se 1 (by rfl) ⟨470273, by rfl⟩ : syracuseStep 627031 = 940547) B940547
theorem B659897 : Blo 259821 659897 := bstep (se 2 (by rfl) ⟨247461, by rfl⟩ : syracuseStep 659897 = 494923) B494923
theorem B987659 : Blo 259821 987659 := bstep (se 1 (by rfl) ⟨740744, by rfl⟩ : syracuseStep 987659 = 1481489) B1481489
theorem B1413719 : Blo 259821 1413719 := bstep (se 1 (by rfl) ⟨1060289, by rfl⟩ : syracuseStep 1413719 = 2120579) B2120579
theorem B8622773 : Blo 259821 8622773 := bstep (se 5 (by rfl) ⟨404192, by rfl⟩ : syracuseStep 8622773 = 808385) B808385
theorem B3904271 : Blo 259821 3904271 := bstep (se 1 (by rfl) ⟨2928203, by rfl⟩ : syracuseStep 3904271 = 5856407) B5856407
theorem B332687 : Blo 259821 332687 := bstep (se 1 (by rfl) ⟨249515, by rfl⟩ : syracuseStep 332687 = 499031) B499031
theorem B14554037 : Blo 259821 14554037 := bstep (se 5 (by rfl) ⟨682220, by rfl⟩ : syracuseStep 14554037 = 1364441) B1364441
theorem B726059 : Blo 259821 726059 := bstep (se 1 (by rfl) ⟨544544, by rfl⟩ : syracuseStep 726059 = 1089089) B1089089
theorem B660595 : Blo 259821 660595 := bstep (se 1 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 660595 = 990893) B990893
theorem B660737 : Blo 259821 660737 := bstep (se 2 (by rfl) ⟨247776, by rfl⟩ : syracuseStep 660737 = 495553) B495553
theorem B1316249 : Blo 259821 1316249 := bstep (se 2 (by rfl) ⟨493593, by rfl⟩ : syracuseStep 1316249 = 987187) B987187
theorem B890297 : Blo 259821 890297 := bstep (se 2 (by rfl) ⟨333861, by rfl⟩ : syracuseStep 890297 = 667723) B667723
theorem B661193 : Blo 259821 661193 := bstep (se 2 (by rfl) ⟨247947, by rfl⟩ : syracuseStep 661193 = 495895) B495895
theorem B497353 : Blo 259821 497353 := bstep (se 2 (by rfl) ⟨186507, by rfl⟩ : syracuseStep 497353 = 373015) B373015
theorem B1480463 : Blo 259821 1480463 := bstep (se 1 (by rfl) ⟨1110347, by rfl⟩ : syracuseStep 1480463 = 2220695) B2220695
theorem B530209 : Blo 259821 530209 := bstep (se 2 (by rfl) ⟨198828, by rfl⟩ : syracuseStep 530209 = 397657) B397657
theorem B890777 : Blo 259821 890777 := bstep (se 2 (by rfl) ⟨334041, by rfl⟩ : syracuseStep 890777 = 668083) B668083
theorem B2693017 : Blo 259821 2693017 := bstep (se 2 (by rfl) ⟨1009881, by rfl⟩ : syracuseStep 2693017 = 2019763) B2019763
theorem B661547 : Blo 259821 661547 := bstep (se 1 (by rfl) ⟨496160, by rfl⟩ : syracuseStep 661547 = 992321) B992321
theorem B792833 : Blo 259821 792833 := bstep (se 2 (by rfl) ⟨297312, by rfl⟩ : syracuseStep 792833 = 594625) B594625
theorem B3021187 : Blo 259821 3021187 := bstep (se 1 (by rfl) ⟨2265890, by rfl⟩ : syracuseStep 3021187 = 4531781) B4531781
theorem B793223 : Blo 259821 793223 := bstep (se 1 (by rfl) ⟨594917, by rfl⟩ : syracuseStep 793223 = 1189835) B1189835
theorem B662539 : Blo 259821 662539 := bstep (se 1 (by rfl) ⟨496904, by rfl⟩ : syracuseStep 662539 = 993809) B993809
theorem B629819 : Blo 259821 629819 := bstep (se 1 (by rfl) ⟨472364, by rfl⟩ : syracuseStep 629819 = 944729) B944729
theorem B1219645 : Blo 259821 1219645 := bstep (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) B457367
theorem B4496471 : Blo 259821 4496471 := bstep (se 1 (by rfl) ⟨3372353, by rfl⟩ : syracuseStep 4496471 = 6744707) B6744707
theorem B269455 : Blo 259821 269455 := bstep (se 1 (by rfl) ⟨202091, by rfl⟩ : syracuseStep 269455 = 404183) B404183
theorem B662681 : Blo 259821 662681 := bstep (se 2 (by rfl) ⟨248505, by rfl⟩ : syracuseStep 662681 = 497011) B497011
theorem B1481921 : Blo 259821 1481921 := bstep (se 2 (by rfl) ⟨555720, by rfl⟩ : syracuseStep 1481921 = 1111441) B1111441
theorem B630031 : Blo 259821 630031 := bstep (se 1 (by rfl) ⟨472523, by rfl⟩ : syracuseStep 630031 = 945047) B945047
theorem B662843 : Blo 259821 662843 := bstep (se 1 (by rfl) ⟨497132, by rfl⟩ : syracuseStep 662843 = 994265) B994265
theorem B499259 : Blo 259821 499259 := bstep (se 1 (by rfl) ⟨374444, by rfl⟩ : syracuseStep 499259 = 748889) B748889
theorem B663187 : Blo 259821 663187 := bstep (se 1 (by rfl) ⟨497390, by rfl⟩ : syracuseStep 663187 = 994781) B994781
theorem B1056527 : Blo 259821 1056527 := bstep (se 1 (by rfl) ⟨792395, by rfl⟩ : syracuseStep 1056527 = 1584791) B1584791
theorem B663329 : Blo 259821 663329 := bstep (se 2 (by rfl) ⟨248748, by rfl⟩ : syracuseStep 663329 = 497497) B497497
theorem B1974131 : Blo 259821 1974131 := bstep (se 1 (by rfl) ⟨1480598, by rfl⟩ : syracuseStep 1974131 = 2961197) B2961197
theorem B1318841 : Blo 259821 1318841 := bstep (se 2 (by rfl) ⟨494565, by rfl⟩ : syracuseStep 1318841 = 989131) B989131
theorem B499745 : Blo 259821 499745 := bstep (se 2 (by rfl) ⟨187404, by rfl⟩ : syracuseStep 499745 = 374809) B374809
theorem B5775533 : Blo 259821 5775533 := bstep (se 3 (by rfl) ⟨1082912, by rfl⟩ : syracuseStep 5775533 = 2165825) B2165825
theorem B991547 : Blo 259821 991547 := bstep (se 1 (by rfl) ⟨743660, by rfl⟩ : syracuseStep 991547 = 1487321) B1487321
theorem B2695517 : Blo 259821 2695517 := bstep (se 3 (by rfl) ⟨505409, by rfl⟩ : syracuseStep 2695517 = 1010819) B1010819
theorem B500087 : Blo 259821 500087 := bstep (se 1 (by rfl) ⟨375065, by rfl⟩ : syracuseStep 500087 = 750131) B750131
theorem B664321 : Blo 259821 664321 := bstep (se 2 (by rfl) ⟨249120, by rfl⟩ : syracuseStep 664321 = 498241) B498241
theorem B500513 : Blo 259821 500513 := bstep (se 2 (by rfl) ⟨187692, by rfl⟩ : syracuseStep 500513 = 375385) B375385
theorem B992033 : Blo 259821 992033 := bstep (se 2 (by rfl) ⟨372012, by rfl⟩ : syracuseStep 992033 = 744025) B744025
theorem B1320137 : Blo 259821 1320137 := bstep (se 2 (by rfl) ⟨495051, by rfl⟩ : syracuseStep 1320137 = 990103) B990103
theorem B632009 : Blo 259821 632009 := bstep (se 2 (by rfl) ⟨237003, by rfl⟩ : syracuseStep 632009 = 474007) B474007
theorem B664919 : Blo 259821 664919 := bstep (se 1 (by rfl) ⟨498689, by rfl⟩ : syracuseStep 664919 = 997379) B997379
theorem B665131 : Blo 259821 665131 := bstep (se 1 (by rfl) ⟨498848, by rfl⟩ : syracuseStep 665131 = 997697) B997697
theorem B665273 : Blo 259821 665273 := bstep (se 2 (by rfl) ⟨249477, by rfl⟩ : syracuseStep 665273 = 498955) B498955
theorem B1418953 : Blo 259821 1418953 := bstep (se 2 (by rfl) ⟨532107, by rfl⟩ : syracuseStep 1418953 = 1064215) B1064215
theorem B993005 : Blo 259821 993005 := bstep (se 3 (by rfl) ⟨186188, by rfl⟩ : syracuseStep 993005 = 372377) B372377
theorem B370423 : Blo 259821 370423 := bstep (se 1 (by rfl) ⟨277817, by rfl⟩ : syracuseStep 370423 = 555635) B555635
theorem B2500631 : Blo 259821 2500631 := bstep (se 1 (by rfl) ⟨1875473, by rfl⟩ : syracuseStep 2500631 = 3750947) B3750947
theorem B993323 : Blo 259821 993323 := bstep (se 1 (by rfl) ⟨744992, by rfl⟩ : syracuseStep 993323 = 1489985) B1489985
theorem B632875 : Blo 259821 632875 := bstep (se 1 (by rfl) ⟨474656, by rfl⟩ : syracuseStep 632875 = 949313) B949313
theorem B7547201 : Blo 259821 7547201 := bstep (se 2 (by rfl) ⟨2830200, by rfl⟩ : syracuseStep 7547201 = 5660401) B5660401
theorem B2238941 : Blo 259821 2238941 := bstep (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) B839603
theorem B633491 : Blo 259821 633491 := bstep (se 1 (by rfl) ⟨475118, by rfl⟩ : syracuseStep 633491 = 950237) B950237
theorem B666265 : Blo 259821 666265 := bstep (se 2 (by rfl) ⟨249849, by rfl⟩ : syracuseStep 666265 = 499699) B499699
theorem B1780481 : Blo 259821 1780481 := bstep (se 2 (by rfl) ⟨667680, by rfl⟩ : syracuseStep 1780481 = 1335361) B1335361
theorem B371471 : Blo 259821 371471 := bstep (se 1 (by rfl) ⟨278603, by rfl⟩ : syracuseStep 371471 = 557207) B557207
theorem B666427 : Blo 259821 666427 := bstep (se 1 (by rfl) ⟨499820, by rfl⟩ : syracuseStep 666427 = 999641) B999641
theorem B2370467 : Blo 259821 2370467 := bstep (se 1 (by rfl) ⟨1777850, by rfl⟩ : syracuseStep 2370467 = 3555701) B3555701
theorem B11447203 : Blo 259821 11447203 := bstep (se 1 (by rfl) ⟨8585402, by rfl⟩ : syracuseStep 11447203 = 17170805) B17170805
theorem B666569 : Blo 259821 666569 := bstep (se 2 (by rfl) ⟨249963, by rfl⟩ : syracuseStep 666569 = 499927) B499927
theorem B371785 : Blo 259821 371785 := bstep (se 2 (by rfl) ⟨139419, by rfl⟩ : syracuseStep 371785 = 278839) B278839
theorem B666913 : Blo 259821 666913 := bstep (se 2 (by rfl) ⟨250092, by rfl⟩ : syracuseStep 666913 = 500185) B500185
theorem B798137 : Blo 259821 798137 := bstep (se 2 (by rfl) ⟨299301, by rfl⟩ : syracuseStep 798137 = 598603) B598603
theorem B1420811 : Blo 259821 1420811 := bstep (se 1 (by rfl) ⟨1065608, by rfl⟩ : syracuseStep 1420811 = 2131217) B2131217
theorem B667511 : Blo 259821 667511 := bstep (se 1 (by rfl) ⟨500633, by rfl⟩ : syracuseStep 667511 = 1001267) B1001267
theorem B1421201 : Blo 259821 1421201 := bstep (se 2 (by rfl) ⟨532950, by rfl⟩ : syracuseStep 1421201 = 1065901) B1065901
theorem B1486795 : Blo 259821 1486795 := bstep (se 1 (by rfl) ⟨1115096, by rfl⟩ : syracuseStep 1486795 = 2230193) B2230193
theorem B438473 : Blo 259821 438473 := bstep (se 2 (by rfl) ⟨164427, by rfl⟩ : syracuseStep 438473 = 328855) B328855
theorem B2994731 : Blo 259821 2994731 := bstep (se 1 (by rfl) ⟨2246048, by rfl⟩ : syracuseStep 2994731 = 4492097) B4492097
theorem B6369911 : Blo 259821 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B439175 : Blo 259821 439175 := bstep (se 1 (by rfl) ⟨329381, by rfl⟩ : syracuseStep 439175 = 658763) B658763
theorem B1422629 : Blo 259821 1422629 := bstep (se 4 (by rfl) ⟨133371, by rfl⟩ : syracuseStep 1422629 = 266743) B266743
theorem B439823 : Blo 259821 439823 := bstep (se 1 (by rfl) ⟨329867, by rfl⟩ : syracuseStep 439823 = 659735) B659735
theorem B996893 : Blo 259821 996893 := bstep (se 3 (by rfl) ⟨186917, by rfl⟩ : syracuseStep 996893 = 373835) B373835
theorem B996907 : Blo 259821 996907 := bstep (se 1 (by rfl) ⟨747680, by rfl⟩ : syracuseStep 996907 = 1495361) B1495361
theorem B374473 : Blo 259821 374473 := bstep (se 2 (by rfl) ⟨140427, by rfl⟩ : syracuseStep 374473 = 280855) B280855
theorem B440363 : Blo 259821 440363 := bstep (se 1 (by rfl) ⟨330272, by rfl⟩ : syracuseStep 440363 = 660545) B660545
theorem B473273 : Blo 259821 473273 := bstep (se 2 (by rfl) ⟨177477, by rfl⟩ : syracuseStep 473273 = 354955) B354955
theorem B702665 : Blo 259821 702665 := bstep (se 2 (by rfl) ⟨263499, by rfl⟩ : syracuseStep 702665 = 526999) B526999
theorem B1489211 : Blo 259821 1489211 := bstep (se 1 (by rfl) ⟨1116908, by rfl⟩ : syracuseStep 1489211 = 2233817) B2233817
theorem B1030553 : Blo 259821 1030553 := bstep (se 2 (by rfl) ⟨386457, by rfl⟩ : syracuseStep 1030553 = 772915) B772915
theorem B440761 : Blo 259821 440761 := bstep (se 2 (by rfl) ⟨165285, by rfl⟩ : syracuseStep 440761 = 330571) B330571
theorem B1325969 : Blo 259821 1325969 := bstep (se 2 (by rfl) ⟨497238, by rfl⟩ : syracuseStep 1325969 = 994477) B994477
theorem B441463 : Blo 259821 441463 := bstep (se 1 (by rfl) ⟨331097, by rfl⟩ : syracuseStep 441463 = 662195) B662195
theorem B703745 : Blo 259821 703745 := bstep (se 2 (by rfl) ⟨263904, by rfl⟩ : syracuseStep 703745 = 527809) B527809
theorem B441659 : Blo 259821 441659 := bstep (se 1 (by rfl) ⟨331244, by rfl⟩ : syracuseStep 441659 = 662489) B662489
theorem B671129 : Blo 259821 671129 := bstep (se 2 (by rfl) ⟨251673, by rfl⟩ : syracuseStep 671129 = 503347) B503347
theorem B11124173 : Blo 259821 11124173 := bstep (se 3 (by rfl) ⟨2085782, by rfl⟩ : syracuseStep 11124173 = 4171565) B4171565
theorem B1261079 : Blo 259821 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B278159 : Blo 259821 278159 := bstep (se 1 (by rfl) ⟨208619, by rfl⟩ : syracuseStep 278159 = 417239) B417239
theorem B442057 : Blo 259821 442057 := bstep (se 2 (by rfl) ⟨165771, by rfl⟩ : syracuseStep 442057 = 331543) B331543
theorem B1490669 : Blo 259821 1490669 := bstep (se 3 (by rfl) ⟨279500, by rfl⟩ : syracuseStep 1490669 = 559001) B559001
theorem B278407 : Blo 259821 278407 := bstep (se 1 (by rfl) ⟨208805, by rfl⟩ : syracuseStep 278407 = 417611) B417611
theorem B1490987 : Blo 259821 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B704783 : Blo 259821 704783 := bstep (se 1 (by rfl) ⟨528587, by rfl⟩ : syracuseStep 704783 = 1057175) B1057175
theorem B442759 : Blo 259821 442759 := bstep (se 1 (by rfl) ⟨332069, by rfl⟩ : syracuseStep 442759 = 664139) B664139
theorem B2474387 : Blo 259821 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B1589827 : Blo 259821 1589827 := bstep (se 1 (by rfl) ⟨1192370, by rfl⟩ : syracuseStep 1589827 = 2384741) B2384741
theorem B1328075 : Blo 259821 1328075 := bstep (se 1 (by rfl) ⟨996056, by rfl⟩ : syracuseStep 1328075 = 1992113) B1992113
theorem B443407 : Blo 259821 443407 := bstep (se 1 (by rfl) ⟨332555, by rfl⟩ : syracuseStep 443407 = 665111) B665111
theorem B1328399 : Blo 259821 1328399 := bstep (se 1 (by rfl) ⟨996299, by rfl⟩ : syracuseStep 1328399 = 1992599) B1992599
theorem B574921 : Blo 259821 574921 := bstep (se 2 (by rfl) ⟨215595, by rfl⟩ : syracuseStep 574921 = 431191) B431191
theorem B4015565 : Blo 259821 4015565 := bstep (se 3 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 4015565 = 1505837) B1505837
theorem B1492445 : Blo 259821 1492445 := bstep (se 3 (by rfl) ⟨279833, by rfl⟩ : syracuseStep 1492445 = 559667) B559667
theorem B443947 : Blo 259821 443947 := bstep (se 1 (by rfl) ⟨332960, by rfl⟩ : syracuseStep 443947 = 665921) B665921
theorem B2508353 : Blo 259821 2508353 := bstep (se 2 (by rfl) ⟨940632, by rfl⟩ : syracuseStep 2508353 = 1881265) B1881265
theorem B444089 : Blo 259821 444089 := bstep (se 2 (by rfl) ⟨166533, by rfl⟩ : syracuseStep 444089 = 333067) B333067
theorem B1722391 : Blo 259821 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B444791 : Blo 259821 444791 := bstep (se 1 (by rfl) ⟨333593, by rfl⟩ : syracuseStep 444791 = 667187) B667187
theorem B2279825 : Blo 259821 2279825 := bstep (se 2 (by rfl) ⟨854934, by rfl⟩ : syracuseStep 2279825 = 1709869) B1709869
theorem B1067411 : Blo 259821 1067411 := bstep (se 1 (by rfl) ⟨800558, by rfl⟩ : syracuseStep 1067411 = 1601117) B1601117
theorem B1329857 : Blo 259821 1329857 := bstep (se 2 (by rfl) ⟨498696, by rfl⟩ : syracuseStep 1329857 = 997393) B997393
theorem B1198793 : Blo 259821 1198793 := bstep (se 2 (by rfl) ⟨449547, by rfl⟩ : syracuseStep 1198793 = 899095) B899095
theorem B740755 : Blo 259821 740755 := bstep (se 1 (by rfl) ⟨555566, by rfl⟩ : syracuseStep 740755 = 1111133) B1111133
theorem B642505 : Blo 259821 642505 := bstep (se 2 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 642505 = 481879) B481879
theorem B1068497 : Blo 259821 1068497 := bstep (se 2 (by rfl) ⟨400686, by rfl⟩ : syracuseStep 1068497 = 801373) B801373
theorem B740983 : Blo 259821 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B479009 : Blo 259821 479009 := bstep (se 2 (by rfl) ⟨179628, by rfl⟩ : syracuseStep 479009 = 359257) B359257
theorem B1331153 : Blo 259821 1331153 := bstep (se 2 (by rfl) ⟨499182, by rfl⟩ : syracuseStep 1331153 = 998365) B998365
theorem B1495043 : Blo 259821 1495043 := bstep (se 1 (by rfl) ⟨1121282, by rfl⟩ : syracuseStep 1495043 = 2242565) B2242565
theorem B3330071 : Blo 259821 3330071 := bstep (se 1 (by rfl) ⟨2497553, by rfl⟩ : syracuseStep 3330071 = 4995107) B4995107
theorem B2511121 : Blo 259821 2511121 := bstep (se 2 (by rfl) ⟨941670, by rfl⟩ : syracuseStep 2511121 = 1883341) B1883341
theorem B1003985 : Blo 259821 1003985 := bstep (se 2 (by rfl) ⟨376494, by rfl⟩ : syracuseStep 1003985 = 752989) B752989
theorem B18469397 : Blo 259821 18469397 := bstep (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) B865753
theorem B938557 : Blo 259821 938557 := bstep (se 3 (by rfl) ⟨175979, by rfl⟩ : syracuseStep 938557 = 351959) B351959
theorem B5133091 : Blo 259821 5133091 := bstep (se 1 (by rfl) ⟨3849818, by rfl⟩ : syracuseStep 5133091 = 7699637) B7699637
theorem B742259 : Blo 259821 742259 := bstep (se 1 (by rfl) ⟨556694, by rfl⟩ : syracuseStep 742259 = 1113389) B1113389
theorem B3003479 : Blo 259821 3003479 := bstep (se 1 (by rfl) ⟨2252609, by rfl⟩ : syracuseStep 3003479 = 4505219) B4505219
theorem B742601 : Blo 259821 742601 := bstep (se 2 (by rfl) ⟨278475, by rfl⟩ : syracuseStep 742601 = 556951) B556951
theorem B742715 : Blo 259821 742715 := bstep (se 1 (by rfl) ⟨557036, by rfl⟩ : syracuseStep 742715 = 1114073) B1114073
theorem B2184583 : Blo 259821 2184583 := bstep (se 1 (by rfl) ⟨1638437, by rfl⟩ : syracuseStep 2184583 = 3276875) B3276875
theorem B742841 : Blo 259821 742841 := bstep (se 2 (by rfl) ⟨278565, by rfl⟩ : syracuseStep 742841 = 557131) B557131
theorem B4871609 : Blo 259821 4871609 := bstep (se 2 (by rfl) ⟨1826853, by rfl⟩ : syracuseStep 4871609 = 3653707) B3653707
theorem B972407 : Blo 259821 972407 := bstep (se 1 (by rfl) ⟨729305, by rfl⟩ : syracuseStep 972407 = 1458611) B1458611
theorem B1005371 : Blo 259821 1005371 := bstep (se 1 (by rfl) ⟨754028, by rfl⟩ : syracuseStep 1005371 = 1508057) B1508057
theorem B710657 : Blo 259821 710657 := bstep (se 2 (by rfl) ⟨266496, by rfl⟩ : syracuseStep 710657 = 532993) B532993
theorem B1333259 : Blo 259821 1333259 := bstep (se 1 (by rfl) ⟨999944, by rfl⟩ : syracuseStep 1333259 = 1999889) B1999889
theorem B1333421 : Blo 259821 1333421 := bstep (se 3 (by rfl) ⟨250016, by rfl⟩ : syracuseStep 1333421 = 500033) B500033
theorem B940403 : Blo 259821 940403 := bstep (se 1 (by rfl) ⟨705302, by rfl⟩ : syracuseStep 940403 = 1410605) B1410605
theorem B1399319 : Blo 259821 1399319 := bstep (se 1 (by rfl) ⟨1049489, by rfl⟩ : syracuseStep 1399319 = 2098979) B2098979
theorem B1989197 : Blo 259821 1989197 := bstep (se 3 (by rfl) ⟨372974, by rfl⟩ : syracuseStep 1989197 = 745949) B745949
theorem B1891187 : Blo 259821 1891187 := bstep (se 1 (by rfl) ⟨1418390, by rfl⟩ : syracuseStep 1891187 = 2836781) B2836781
theorem B744491 : Blo 259821 744491 := bstep (se 1 (by rfl) ⟨558368, by rfl⟩ : syracuseStep 744491 = 1116737) B1116737
theorem B941327 : Blo 259821 941327 := bstep (se 1 (by rfl) ⟨705995, by rfl⟩ : syracuseStep 941327 = 1411991) B1411991
theorem B1335041 : Blo 259821 1335041 := bstep (se 2 (by rfl) ⟨500640, by rfl⟩ : syracuseStep 1335041 = 1001281) B1001281
theorem B712481 : Blo 259821 712481 := bstep (se 2 (by rfl) ⟨267180, by rfl⟩ : syracuseStep 712481 = 534361) B534361
theorem B941959 : Blo 259821 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B745483 : Blo 259821 745483 := bstep (se 1 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 745483 = 1118225) B1118225
theorem B1794059 : Blo 259821 1794059 := bstep (se 1 (by rfl) ⟨1345544, by rfl⟩ : syracuseStep 1794059 = 2691089) B2691089
theorem B1401025 : Blo 259821 1401025 := bstep (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) B1050769
theorem B745757 : Blo 259821 745757 := bstep (se 3 (by rfl) ⟨139829, by rfl⟩ : syracuseStep 745757 = 279659) B279659
theorem B877067 : Blo 259821 877067 := bstep (se 1 (by rfl) ⟨657800, by rfl⟩ : syracuseStep 877067 = 1315601) B1315601
theorem B1499735 : Blo 259821 1499735 := bstep (se 1 (by rfl) ⟨1124801, by rfl⟩ : syracuseStep 1499735 = 2249603) B2249603
theorem B877175 : Blo 259821 877175 := bstep (se 1 (by rfl) ⟨657881, by rfl⟩ : syracuseStep 877175 = 1315763) B1315763
theorem B844577 : Blo 259821 844577 := bstep (se 2 (by rfl) ⟨316716, by rfl⟩ : syracuseStep 844577 = 633433) B633433
theorem B1991627 : Blo 259821 1991627 := bstep (se 1 (by rfl) ⟨1493720, by rfl⟩ : syracuseStep 1991627 = 2987441) B2987441
theorem B877769 : Blo 259821 877769 := bstep (se 2 (by rfl) ⟨329163, by rfl⟩ : syracuseStep 877769 = 658327) B658327
theorem B3171869 : Blo 259821 3171869 := bstep (se 3 (by rfl) ⟨594725, by rfl⟩ : syracuseStep 3171869 = 1189451) B1189451
theorem B353927 : Blo 259821 353927 := bstep (se 1 (by rfl) ⟨265445, by rfl⟩ : syracuseStep 353927 = 530891) B530891
theorem B14444401 : Blo 259821 14444401 := bstep (se 2 (by rfl) ⟨5416650, by rfl⟩ : syracuseStep 14444401 = 10833301) B10833301
theorem B878471 : Blo 259821 878471 := bstep (se 1 (by rfl) ⟨658853, by rfl⟩ : syracuseStep 878471 = 1317707) B1317707
theorem B419899 : Blo 259821 419899 := bstep (se 1 (by rfl) ⟨314924, by rfl⟩ : syracuseStep 419899 = 629849) B629849
theorem B2844733 : Blo 259821 2844733 := bstep (se 3 (by rfl) ⟨533387, by rfl⟩ : syracuseStep 2844733 = 1066775) B1066775
theorem B878849 : Blo 259821 878849 := bstep (se 2 (by rfl) ⟨329568, by rfl⟩ : syracuseStep 878849 = 659137) B659137
theorem B420155 : Blo 259821 420155 := bstep (se 1 (by rfl) ⟨315116, by rfl⟩ : syracuseStep 420155 = 630233) B630233
theorem B354619 : Blo 259821 354619 := bstep (se 1 (by rfl) ⟨265964, by rfl⟩ : syracuseStep 354619 = 531929) B531929
theorem B747863 : Blo 259821 747863 := bstep (se 1 (by rfl) ⟨560897, by rfl⟩ : syracuseStep 747863 = 1121795) B1121795
theorem B1501649 : Blo 259821 1501649 := bstep (se 2 (by rfl) ⟨563118, by rfl⟩ : syracuseStep 1501649 = 1126237) B1126237
theorem B3369437 : Blo 259821 3369437 := bstep (se 3 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 3369437 = 1263539) B1263539
theorem B748091 : Blo 259821 748091 := bstep (se 1 (by rfl) ⟨561068, by rfl⟩ : syracuseStep 748091 = 1122137) B1122137
theorem B748217 : Blo 259821 748217 := bstep (se 2 (by rfl) ⟨280581, by rfl⟩ : syracuseStep 748217 = 561163) B561163
theorem B584747 : Blo 259821 584747 := bstep (se 1 (by rfl) ⟨438560, by rfl⟩ : syracuseStep 584747 = 877121) B877121
theorem B879659 : Blo 259821 879659 := bstep (se 1 (by rfl) ⟨659744, by rfl⟩ : syracuseStep 879659 = 1319489) B1319489
theorem B585107 : Blo 259821 585107 := bstep (se 1 (by rfl) ⟨438830, by rfl⟩ : syracuseStep 585107 = 877661) B877661
theorem B585161 : Blo 259821 585161 := bstep (se 2 (by rfl) ⟨219435, by rfl⟩ : syracuseStep 585161 = 438871) B438871
theorem B421391 : Blo 259821 421391 := bstep (se 1 (by rfl) ⟨316043, by rfl⟩ : syracuseStep 421391 = 632087) B632087
theorem B585863 : Blo 259821 585863 := bstep (se 1 (by rfl) ⟨439397, by rfl⟩ : syracuseStep 585863 = 878795) B878795
theorem B2125997 : Blo 259821 2125997 := bstep (se 3 (by rfl) ⟨398624, by rfl⟩ : syracuseStep 2125997 = 797249) B797249
theorem B749857 : Blo 259821 749857 := bstep (se 2 (by rfl) ⟨281196, by rfl⟩ : syracuseStep 749857 = 562393) B562393
theorem B586043 : Blo 259821 586043 := bstep (se 1 (by rfl) ⟨439532, by rfl⟩ : syracuseStep 586043 = 879065) B879065
theorem B880955 : Blo 259821 880955 := bstep (se 1 (by rfl) ⟨660716, by rfl⟩ : syracuseStep 880955 = 1321433) B1321433
theorem B1503623 : Blo 259821 1503623 := bstep (se 1 (by rfl) ⟨1127717, by rfl⟩ : syracuseStep 1503623 = 2255435) B2255435
theorem B586169 : Blo 259821 586169 := bstep (se 2 (by rfl) ⟨219813, by rfl⟩ : syracuseStep 586169 = 439627) B439627
theorem B1602109 : Blo 259821 1602109 := bstep (se 3 (by rfl) ⟨300395, by rfl⟩ : syracuseStep 1602109 = 600791) B600791
theorem B389819 : Blo 259821 389819 := bstep (se 1 (by rfl) ⟨292364, by rfl⟩ : syracuseStep 389819 = 584729) B584729
theorem B1405633 : Blo 259821 1405633 := bstep (se 2 (by rfl) ⟨527112, by rfl⟩ : syracuseStep 1405633 = 1054225) B1054225
theorem B389879 : Blo 259821 389879 := bstep (se 1 (by rfl) ⟨292409, by rfl⟩ : syracuseStep 389879 = 584819) B584819
theorem B750347 : Blo 259821 750347 := bstep (se 1 (by rfl) ⟨562760, by rfl⟩ : syracuseStep 750347 = 1125521) B1125521
theorem B389903 : Blo 259821 389903 := bstep (se 1 (by rfl) ⟨292427, by rfl⟩ : syracuseStep 389903 = 584855) B584855
theorem B586511 : Blo 259821 586511 := bstep (se 1 (by rfl) ⟨439883, by rfl⟩ : syracuseStep 586511 = 879767) B879767
theorem B586529 : Blo 259821 586529 := bstep (se 2 (by rfl) ⟨219948, by rfl⟩ : syracuseStep 586529 = 439897) B439897
theorem B881441 : Blo 259821 881441 := bstep (se 2 (by rfl) ⟨330540, by rfl⟩ : syracuseStep 881441 = 661081) B661081
theorem B1078049 : Blo 259821 1078049 := bstep (se 2 (by rfl) ⟨404268, by rfl⟩ : syracuseStep 1078049 = 808537) B808537
theorem B389945 : Blo 259821 389945 := bstep (se 2 (by rfl) ⟨146229, by rfl⟩ : syracuseStep 389945 = 292459) B292459
theorem B12743513 : Blo 259821 12743513 := bstep (se 2 (by rfl) ⟨4778817, by rfl⟩ : syracuseStep 12743513 = 9557635) B9557635
theorem B390023 : Blo 259821 390023 := bstep (se 1 (by rfl) ⟨292517, by rfl⟩ : syracuseStep 390023 = 585035) B585035
theorem B390059 : Blo 259821 390059 := bstep (se 1 (by rfl) ⟨292544, by rfl⟩ : syracuseStep 390059 = 585089) B585089
theorem B390089 : Blo 259821 390089 := bstep (se 2 (by rfl) ⟨146283, by rfl⟩ : syracuseStep 390089 = 292567) B292567
theorem B390203 : Blo 259821 390203 := bstep (se 1 (by rfl) ⟨292652, by rfl⟩ : syracuseStep 390203 = 585305) B585305
theorem B390263 : Blo 259821 390263 := bstep (se 1 (by rfl) ⟨292697, by rfl⟩ : syracuseStep 390263 = 585395) B585395
theorem B586871 : Blo 259821 586871 := bstep (se 1 (by rfl) ⟨440153, by rfl⟩ : syracuseStep 586871 = 880307) B880307
theorem B390287 : Blo 259821 390287 := bstep (se 1 (by rfl) ⟨292715, by rfl⟩ : syracuseStep 390287 = 585431) B585431
theorem B390329 : Blo 259821 390329 := bstep (se 2 (by rfl) ⟨146373, by rfl⟩ : syracuseStep 390329 = 292747) B292747
theorem B390407 : Blo 259821 390407 := bstep (se 1 (by rfl) ⟨292805, by rfl⟩ : syracuseStep 390407 = 585611) B585611
theorem B390443 : Blo 259821 390443 := bstep (se 1 (by rfl) ⟨292832, by rfl⟩ : syracuseStep 390443 = 585665) B585665
theorem B587051 : Blo 259821 587051 := bstep (se 1 (by rfl) ⟨440288, by rfl⟩ : syracuseStep 587051 = 880577) B880577
theorem B390473 : Blo 259821 390473 := bstep (se 2 (by rfl) ⟨146427, by rfl⟩ : syracuseStep 390473 = 292855) B292855
theorem B882035 : Blo 259821 882035 := bstep (se 1 (by rfl) ⟨661526, by rfl⟩ : syracuseStep 882035 = 1323053) B1323053
theorem B390587 : Blo 259821 390587 := bstep (se 1 (by rfl) ⟨292940, by rfl⟩ : syracuseStep 390587 = 585881) B585881
theorem B390647 : Blo 259821 390647 := bstep (se 1 (by rfl) ⟨292985, by rfl⟩ : syracuseStep 390647 = 585971) B585971
theorem B390671 : Blo 259821 390671 := bstep (se 1 (by rfl) ⟨293003, by rfl⟩ : syracuseStep 390671 = 586007) B586007
theorem B751133 : Blo 259821 751133 := bstep (se 3 (by rfl) ⟨140837, by rfl⟩ : syracuseStep 751133 = 281675) B281675
theorem B390713 : Blo 259821 390713 := bstep (se 2 (by rfl) ⟨146517, by rfl⟩ : syracuseStep 390713 = 293035) B293035
theorem B390791 : Blo 259821 390791 := bstep (se 1 (by rfl) ⟨293093, by rfl⟩ : syracuseStep 390791 = 586187) B586187
theorem B292495 : Blo 259821 292495 := bstep (se 1 (by rfl) ⟨219371, by rfl⟩ : syracuseStep 292495 = 438743) B438743
theorem B587411 : Blo 259821 587411 := bstep (se 1 (by rfl) ⟨440558, by rfl⟩ : syracuseStep 587411 = 881117) B881117
theorem B390827 : Blo 259821 390827 := bstep (se 1 (by rfl) ⟨293120, by rfl⟩ : syracuseStep 390827 = 586241) B586241
theorem B390857 : Blo 259821 390857 := bstep (se 2 (by rfl) ⟨146571, by rfl⟩ : syracuseStep 390857 = 293143) B293143
theorem B587465 : Blo 259821 587465 := bstep (se 2 (by rfl) ⟨220299, by rfl⟩ : syracuseStep 587465 = 440599) B440599
theorem B259847 : Blo 259821 259847 := bstep (se 1 (by rfl) ⟨194885, by rfl⟩ : syracuseStep 259847 = 389771) B389771
theorem B259855 : Blo 259821 259855 := bstep (se 1 (by rfl) ⟨194891, by rfl⟩ : syracuseStep 259855 = 389783) B389783
theorem B259899 : Blo 259821 259899 := bstep (se 1 (by rfl) ⟨194924, by rfl⟩ : syracuseStep 259899 = 389849) B389849
theorem B390971 : Blo 259821 390971 := bstep (se 1 (by rfl) ⟨293228, by rfl⟩ : syracuseStep 390971 = 586457) B586457
theorem B11401073 : Blo 259821 11401073 := bstep (se 2 (by rfl) ⟨4275402, by rfl⟩ : syracuseStep 11401073 = 8550805) B8550805
theorem B391031 : Blo 259821 391031 := bstep (se 1 (by rfl) ⟨293273, by rfl⟩ : syracuseStep 391031 = 586547) B586547
theorem B259975 : Blo 259821 259975 := bstep (se 1 (by rfl) ⟨194981, by rfl⟩ : syracuseStep 259975 = 389963) B389963
theorem B259983 : Blo 259821 259983 := bstep (se 1 (by rfl) ⟨194987, by rfl⟩ : syracuseStep 259983 = 389975) B389975
theorem B391055 : Blo 259821 391055 := bstep (se 1 (by rfl) ⟨293291, by rfl⟩ : syracuseStep 391055 = 586583) B586583
theorem B1603475 : Blo 259821 1603475 := bstep (se 1 (by rfl) ⟨1202606, by rfl⟩ : syracuseStep 1603475 = 2405213) B2405213
theorem B391097 : Blo 259821 391097 := bstep (se 2 (by rfl) ⟨146661, by rfl⟩ : syracuseStep 391097 = 293323) B293323
theorem B260027 : Blo 259821 260027 := bstep (se 1 (by rfl) ⟨195020, by rfl⟩ : syracuseStep 260027 = 390041) B390041
theorem B260103 : Blo 259821 260103 := bstep (se 1 (by rfl) ⟨195077, by rfl⟩ : syracuseStep 260103 = 390155) B390155
theorem B391175 : Blo 259821 391175 := bstep (se 1 (by rfl) ⟨293381, by rfl⟩ : syracuseStep 391175 = 586763) B586763
theorem B1112075 : Blo 259821 1112075 := bstep (se 1 (by rfl) ⟨834056, by rfl⟩ : syracuseStep 1112075 = 1668113) B1668113
theorem B260111 : Blo 259821 260111 := bstep (se 1 (by rfl) ⟨195083, by rfl⟩ : syracuseStep 260111 = 390167) B390167
theorem B391211 : Blo 259821 391211 := bstep (se 1 (by rfl) ⟨293408, by rfl⟩ : syracuseStep 391211 = 586817) B586817
theorem B260155 : Blo 259821 260155 := bstep (se 1 (by rfl) ⟨195116, by rfl⟩ : syracuseStep 260155 = 390233) B390233
theorem B391241 : Blo 259821 391241 := bstep (se 2 (by rfl) ⟨146715, by rfl⟩ : syracuseStep 391241 = 293431) B293431
theorem B1538135 : Blo 259821 1538135 := bstep (se 1 (by rfl) ⟨1153601, by rfl⟩ : syracuseStep 1538135 = 2307203) B2307203
theorem B260231 : Blo 259821 260231 := bstep (se 1 (by rfl) ⟨195173, by rfl⟩ : syracuseStep 260231 = 390347) B390347
theorem B292999 : Blo 259821 292999 := bstep (se 1 (by rfl) ⟨219749, by rfl⟩ : syracuseStep 292999 = 439499) B439499
theorem B260239 : Blo 259821 260239 := bstep (se 1 (by rfl) ⟨195179, by rfl⟩ : syracuseStep 260239 = 390359) B390359
theorem B1996973 : Blo 259821 1996973 := bstep (se 3 (by rfl) ⟨374432, by rfl⟩ : syracuseStep 1996973 = 748865) B748865
theorem B260283 : Blo 259821 260283 := bstep (se 1 (by rfl) ⟨195212, by rfl⟩ : syracuseStep 260283 = 390425) B390425
theorem B391355 : Blo 259821 391355 := bstep (se 1 (by rfl) ⟨293516, by rfl⟩ : syracuseStep 391355 = 587033) B587033
theorem B391415 : Blo 259821 391415 := bstep (se 1 (by rfl) ⟨293561, by rfl⟩ : syracuseStep 391415 = 587123) B587123
theorem B1407233 : Blo 259821 1407233 := bstep (se 2 (by rfl) ⟨527712, by rfl⟩ : syracuseStep 1407233 = 1055425) B1055425
theorem B260359 : Blo 259821 260359 := bstep (se 1 (by rfl) ⟨195269, by rfl⟩ : syracuseStep 260359 = 390539) B390539
theorem B260367 : Blo 259821 260367 := bstep (se 1 (by rfl) ⟨195275, by rfl⟩ : syracuseStep 260367 = 390551) B390551
theorem B391439 : Blo 259821 391439 := bstep (se 1 (by rfl) ⟨293579, by rfl⟩ : syracuseStep 391439 = 587159) B587159
theorem B391481 : Blo 259821 391481 := bstep (se 2 (by rfl) ⟨146805, by rfl⟩ : syracuseStep 391481 = 293611) B293611
theorem B260411 : Blo 259821 260411 := bstep (se 1 (by rfl) ⟨195308, by rfl⟩ : syracuseStep 260411 = 390617) B390617
theorem B293179 : Blo 259821 293179 := bstep (se 1 (by rfl) ⟨219884, by rfl⟩ : syracuseStep 293179 = 439769) B439769
theorem B260487 : Blo 259821 260487 := bstep (se 1 (by rfl) ⟨195365, by rfl⟩ : syracuseStep 260487 = 390731) B390731
theorem B391559 : Blo 259821 391559 := bstep (se 1 (by rfl) ⟨293669, by rfl⟩ : syracuseStep 391559 = 587339) B587339
theorem B588167 : Blo 259821 588167 := bstep (se 1 (by rfl) ⟨441125, by rfl⟩ : syracuseStep 588167 = 882251) B882251
theorem B260495 : Blo 259821 260495 := bstep (se 1 (by rfl) ⟨195371, by rfl⟩ : syracuseStep 260495 = 390743) B390743
theorem B391595 : Blo 259821 391595 := bstep (se 1 (by rfl) ⟨293696, by rfl⟩ : syracuseStep 391595 = 587393) B587393
theorem B260539 : Blo 259821 260539 := bstep (se 1 (by rfl) ⟨195404, by rfl⟩ : syracuseStep 260539 = 390809) B390809
theorem B391625 : Blo 259821 391625 := bstep (se 2 (by rfl) ⟨146859, by rfl⟩ : syracuseStep 391625 = 293719) B293719
theorem B260615 : Blo 259821 260615 := bstep (se 1 (by rfl) ⟨195461, by rfl⟩ : syracuseStep 260615 = 390923) B390923
theorem B260623 : Blo 259821 260623 := bstep (se 1 (by rfl) ⟨195467, by rfl⟩ : syracuseStep 260623 = 390935) B390935
theorem B4487723 : Blo 259821 4487723 := bstep (se 1 (by rfl) ⟨3365792, by rfl⟩ : syracuseStep 4487723 = 6731585) B6731585
theorem B260667 : Blo 259821 260667 := bstep (se 1 (by rfl) ⟨195500, by rfl⟩ : syracuseStep 260667 = 391001) B391001
theorem B391739 : Blo 259821 391739 := bstep (se 1 (by rfl) ⟨293804, by rfl⟩ : syracuseStep 391739 = 587609) B587609
theorem B588347 : Blo 259821 588347 := bstep (se 1 (by rfl) ⟨441260, by rfl⟩ : syracuseStep 588347 = 882521) B882521
theorem B391799 : Blo 259821 391799 := bstep (se 1 (by rfl) ⟨293849, by rfl⟩ : syracuseStep 391799 = 587699) B587699
theorem B260743 : Blo 259821 260743 := bstep (se 1 (by rfl) ⟨195557, by rfl⟩ : syracuseStep 260743 = 391115) B391115
theorem B260751 : Blo 259821 260751 := bstep (se 1 (by rfl) ⟨195563, by rfl⟩ : syracuseStep 260751 = 391127) B391127
theorem B391823 : Blo 259821 391823 := bstep (se 1 (by rfl) ⟨293867, by rfl⟩ : syracuseStep 391823 = 587735) B587735
theorem B391865 : Blo 259821 391865 := bstep (se 2 (by rfl) ⟨146949, by rfl⟩ : syracuseStep 391865 = 293899) B293899
theorem B588473 : Blo 259821 588473 := bstep (se 2 (by rfl) ⟨220677, by rfl⟩ : syracuseStep 588473 = 441355) B441355
theorem B260795 : Blo 259821 260795 := bstep (se 1 (by rfl) ⟨195596, by rfl⟩ : syracuseStep 260795 = 391193) B391193
theorem B260871 : Blo 259821 260871 := bstep (se 1 (by rfl) ⟨195653, by rfl⟩ : syracuseStep 260871 = 391307) B391307
theorem B391943 : Blo 259821 391943 := bstep (se 1 (by rfl) ⟨293957, by rfl⟩ : syracuseStep 391943 = 587915) B587915
theorem B260879 : Blo 259821 260879 := bstep (se 1 (by rfl) ⟨195659, by rfl⟩ : syracuseStep 260879 = 391319) B391319
theorem B293647 : Blo 259821 293647 := bstep (se 1 (by rfl) ⟨220235, by rfl⟩ : syracuseStep 293647 = 440471) B440471
theorem B391979 : Blo 259821 391979 := bstep (se 1 (by rfl) ⟨293984, by rfl⟩ : syracuseStep 391979 = 587969) B587969
theorem B260923 : Blo 259821 260923 := bstep (se 1 (by rfl) ⟨195692, by rfl⟩ : syracuseStep 260923 = 391385) B391385
theorem B392009 : Blo 259821 392009 := bstep (se 2 (by rfl) ⟨147003, by rfl⟩ : syracuseStep 392009 = 294007) B294007
theorem B260999 : Blo 259821 260999 := bstep (se 1 (by rfl) ⟨195749, by rfl⟩ : syracuseStep 260999 = 391499) B391499
theorem B261007 : Blo 259821 261007 := bstep (se 1 (by rfl) ⟨195755, by rfl⟩ : syracuseStep 261007 = 391511) B391511
theorem B261051 : Blo 259821 261051 := bstep (se 1 (by rfl) ⟨195788, by rfl⟩ : syracuseStep 261051 = 391577) B391577
theorem B392123 : Blo 259821 392123 := bstep (se 1 (by rfl) ⟨294092, by rfl⟩ : syracuseStep 392123 = 588185) B588185
theorem B555977 : Blo 259821 555977 := bstep (se 2 (by rfl) ⟨208491, by rfl⟩ : syracuseStep 555977 = 416983) B416983
theorem B392183 : Blo 259821 392183 := bstep (se 1 (by rfl) ⟨294137, by rfl⟩ : syracuseStep 392183 = 588275) B588275
theorem B261127 : Blo 259821 261127 := bstep (se 1 (by rfl) ⟨195845, by rfl⟩ : syracuseStep 261127 = 391691) B391691
theorem B261135 : Blo 259821 261135 := bstep (se 1 (by rfl) ⟨195851, by rfl⟩ : syracuseStep 261135 = 391703) B391703
theorem B392207 : Blo 259821 392207 := bstep (se 1 (by rfl) ⟨294155, by rfl⟩ : syracuseStep 392207 = 588311) B588311
theorem B588815 : Blo 259821 588815 := bstep (se 1 (by rfl) ⟨441611, by rfl⟩ : syracuseStep 588815 = 883223) B883223
theorem B588833 : Blo 259821 588833 := bstep (se 2 (by rfl) ⟨220812, by rfl⟩ : syracuseStep 588833 = 441625) B441625
theorem B392249 : Blo 259821 392249 := bstep (se 2 (by rfl) ⟨147093, by rfl⟩ : syracuseStep 392249 = 294187) B294187
theorem B261179 : Blo 259821 261179 := bstep (se 1 (by rfl) ⟨195884, by rfl⟩ : syracuseStep 261179 = 391769) B391769
theorem B261255 : Blo 259821 261255 := bstep (se 1 (by rfl) ⟨195941, by rfl⟩ : syracuseStep 261255 = 391883) B391883
theorem B392327 : Blo 259821 392327 := bstep (se 1 (by rfl) ⟨294245, by rfl⟩ : syracuseStep 392327 = 588491) B588491
theorem B261263 : Blo 259821 261263 := bstep (se 1 (by rfl) ⟨195947, by rfl⟩ : syracuseStep 261263 = 391895) B391895
theorem B392363 : Blo 259821 392363 := bstep (se 1 (by rfl) ⟨294272, by rfl⟩ : syracuseStep 392363 = 588545) B588545
theorem B457913 : Blo 259821 457913 := bstep (se 2 (by rfl) ⟨171717, by rfl⟩ : syracuseStep 457913 = 343435) B343435
theorem B261307 : Blo 259821 261307 := bstep (se 1 (by rfl) ⟨195980, by rfl⟩ : syracuseStep 261307 = 391961) B391961
theorem B392393 : Blo 259821 392393 := bstep (se 2 (by rfl) ⟨147147, by rfl⟩ : syracuseStep 392393 = 294295) B294295
theorem B261383 : Blo 259821 261383 := bstep (se 1 (by rfl) ⟨196037, by rfl⟩ : syracuseStep 261383 = 392075) B392075
theorem B294151 : Blo 259821 294151 := bstep (se 1 (by rfl) ⟨220613, by rfl⟩ : syracuseStep 294151 = 441227) B441227
theorem B261391 : Blo 259821 261391 := bstep (se 1 (by rfl) ⟨196043, by rfl⟩ : syracuseStep 261391 = 392087) B392087
theorem B4226363 : Blo 259821 4226363 := bstep (se 1 (by rfl) ⟨3169772, by rfl⟩ : syracuseStep 4226363 = 6339545) B6339545
theorem B261435 : Blo 259821 261435 := bstep (se 1 (by rfl) ⟨196076, by rfl⟩ : syracuseStep 261435 = 392153) B392153
theorem B392507 : Blo 259821 392507 := bstep (se 1 (by rfl) ⟨294380, by rfl⟩ : syracuseStep 392507 = 588761) B588761
theorem B392567 : Blo 259821 392567 := bstep (se 1 (by rfl) ⟨294425, by rfl⟩ : syracuseStep 392567 = 588851) B588851
theorem B589175 : Blo 259821 589175 := bstep (se 1 (by rfl) ⟨441881, by rfl⟩ : syracuseStep 589175 = 883763) B883763
theorem B261511 : Blo 259821 261511 := bstep (se 1 (by rfl) ⟨196133, by rfl⟩ : syracuseStep 261511 = 392267) B392267
theorem B261519 : Blo 259821 261519 := bstep (se 1 (by rfl) ⟨196139, by rfl⟩ : syracuseStep 261519 = 392279) B392279
theorem B392591 : Blo 259821 392591 := bstep (se 1 (by rfl) ⟨294443, by rfl⟩ : syracuseStep 392591 = 588887) B588887
theorem B392633 : Blo 259821 392633 := bstep (se 2 (by rfl) ⟨147237, by rfl⟩ : syracuseStep 392633 = 294475) B294475
theorem B261563 : Blo 259821 261563 := bstep (se 1 (by rfl) ⟨196172, by rfl⟩ : syracuseStep 261563 = 392345) B392345
theorem B294331 : Blo 259821 294331 := bstep (se 1 (by rfl) ⟨220748, by rfl⟩ : syracuseStep 294331 = 441497) B441497
theorem B261639 : Blo 259821 261639 := bstep (se 1 (by rfl) ⟨196229, by rfl⟩ : syracuseStep 261639 = 392459) B392459
theorem B392711 : Blo 259821 392711 := bstep (se 1 (by rfl) ⟨294533, by rfl⟩ : syracuseStep 392711 = 589067) B589067
theorem B261647 : Blo 259821 261647 := bstep (se 1 (by rfl) ⟨196235, by rfl⟩ : syracuseStep 261647 = 392471) B392471
theorem B392747 : Blo 259821 392747 := bstep (se 1 (by rfl) ⟨294560, by rfl⟩ : syracuseStep 392747 = 589121) B589121
theorem B589355 : Blo 259821 589355 := bstep (se 1 (by rfl) ⟨442016, by rfl⟩ : syracuseStep 589355 = 884033) B884033
theorem B261691 : Blo 259821 261691 := bstep (se 1 (by rfl) ⟨196268, by rfl⟩ : syracuseStep 261691 = 392537) B392537
theorem B392777 : Blo 259821 392777 := bstep (se 2 (by rfl) ⟨147291, by rfl⟩ : syracuseStep 392777 = 294583) B294583
theorem B261767 : Blo 259821 261767 := bstep (se 1 (by rfl) ⟨196325, by rfl⟩ : syracuseStep 261767 = 392651) B392651
theorem B261775 : Blo 259821 261775 := bstep (se 1 (by rfl) ⟨196331, by rfl⟩ : syracuseStep 261775 = 392663) B392663
theorem B261819 : Blo 259821 261819 := bstep (se 1 (by rfl) ⟨196364, by rfl⟩ : syracuseStep 261819 = 392729) B392729
theorem B392891 : Blo 259821 392891 := bstep (se 1 (by rfl) ⟨294668, by rfl⟩ : syracuseStep 392891 = 589337) B589337
theorem B2391781 : Blo 259821 2391781 := bstep (se 4 (by rfl) ⟨224229, by rfl⟩ : syracuseStep 2391781 = 448459) B448459
theorem B392951 : Blo 259821 392951 := bstep (se 1 (by rfl) ⟨294713, by rfl⟩ : syracuseStep 392951 = 589427) B589427
theorem B3768065 : Blo 259821 3768065 := bstep (se 2 (by rfl) ⟨1413024, by rfl⟩ : syracuseStep 3768065 = 2826049) B2826049
theorem B261895 : Blo 259821 261895 := bstep (se 1 (by rfl) ⟨196421, by rfl⟩ : syracuseStep 261895 = 392843) B392843
theorem B261903 : Blo 259821 261903 := bstep (se 1 (by rfl) ⟨196427, by rfl⟩ : syracuseStep 261903 = 392855) B392855
theorem B392975 : Blo 259821 392975 := bstep (se 1 (by rfl) ⟨294731, by rfl⟩ : syracuseStep 392975 = 589463) B589463
theorem B393017 : Blo 259821 393017 := bstep (se 2 (by rfl) ⟨147381, by rfl⟩ : syracuseStep 393017 = 294763) B294763
theorem B261947 : Blo 259821 261947 := bstep (se 1 (by rfl) ⟨196460, by rfl⟩ : syracuseStep 261947 = 392921) B392921
theorem B262023 : Blo 259821 262023 := bstep (se 1 (by rfl) ⟨196517, by rfl⟩ : syracuseStep 262023 = 393035) B393035
theorem B393095 : Blo 259821 393095 := bstep (se 1 (by rfl) ⟨294821, by rfl⟩ : syracuseStep 393095 = 589643) B589643
theorem B262031 : Blo 259821 262031 := bstep (se 1 (by rfl) ⟨196523, by rfl⟩ : syracuseStep 262031 = 393047) B393047
theorem B294799 : Blo 259821 294799 := bstep (se 1 (by rfl) ⟨221099, by rfl⟩ : syracuseStep 294799 = 442199) B442199
theorem B1114003 : Blo 259821 1114003 := bstep (se 1 (by rfl) ⟨835502, by rfl⟩ : syracuseStep 1114003 = 1671005) B1671005
theorem B589715 : Blo 259821 589715 := bstep (se 1 (by rfl) ⟨442286, by rfl⟩ : syracuseStep 589715 = 884573) B884573
theorem B884627 : Blo 259821 884627 := bstep (se 1 (by rfl) ⟨663470, by rfl⟩ : syracuseStep 884627 = 1326941) B1326941
theorem B393131 : Blo 259821 393131 := bstep (se 1 (by rfl) ⟨294848, by rfl⟩ : syracuseStep 393131 = 589697) B589697
theorem B262075 : Blo 259821 262075 := bstep (se 1 (by rfl) ⟨196556, by rfl⟩ : syracuseStep 262075 = 393113) B393113
theorem B393161 : Blo 259821 393161 := bstep (se 2 (by rfl) ⟨147435, by rfl⟩ : syracuseStep 393161 = 294871) B294871
theorem B589769 : Blo 259821 589769 := bstep (se 2 (by rfl) ⟨221163, by rfl⟩ : syracuseStep 589769 = 442327) B442327
theorem B262183 : Blo 259821 262183 := bstep (se 1 (by rfl) ⟨196637, by rfl⟩ : syracuseStep 262183 = 393275) B393275
theorem B262223 : Blo 259821 262223 := bstep (se 1 (by rfl) ⟨196667, by rfl⟩ : syracuseStep 262223 = 393335) B393335
theorem B262239 : Blo 259821 262239 := bstep (se 1 (by rfl) ⟨196679, by rfl⟩ : syracuseStep 262239 = 393359) B393359
theorem B262267 : Blo 259821 262267 := bstep (se 1 (by rfl) ⟨196700, by rfl⟩ : syracuseStep 262267 = 393401) B393401
theorem B262319 : Blo 259821 262319 := bstep (se 1 (by rfl) ⟨196739, by rfl⟩ : syracuseStep 262319 = 393479) B393479
theorem B262343 : Blo 259821 262343 := bstep (se 1 (by rfl) ⟨196757, by rfl⟩ : syracuseStep 262343 = 393515) B393515
theorem B262363 : Blo 259821 262363 := bstep (se 1 (by rfl) ⟨196772, by rfl⟩ : syracuseStep 262363 = 393545) B393545
theorem B1868033 : Blo 259821 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B262439 : Blo 259821 262439 := bstep (se 1 (by rfl) ⟨196829, by rfl⟩ : syracuseStep 262439 = 393659) B393659
theorem B262479 : Blo 259821 262479 := bstep (se 1 (by rfl) ⟨196859, by rfl⟩ : syracuseStep 262479 = 393719) B393719
theorem B262495 : Blo 259821 262495 := bstep (se 1 (by rfl) ⟨196871, by rfl⟩ : syracuseStep 262495 = 393743) B393743
theorem B262523 : Blo 259821 262523 := bstep (se 1 (by rfl) ⟨196892, by rfl⟩ : syracuseStep 262523 = 393785) B393785
theorem B393647 : Blo 259821 393647 := bstep (se 1 (by rfl) ⟨295235, by rfl⟩ : syracuseStep 393647 = 590471) B590471
theorem B262575 : Blo 259821 262575 := bstep (se 1 (by rfl) ⟨196931, by rfl⟩ : syracuseStep 262575 = 393863) B393863
theorem B262599 : Blo 259821 262599 := bstep (se 1 (by rfl) ⟨196949, by rfl⟩ : syracuseStep 262599 = 393899) B393899
theorem B262619 : Blo 259821 262619 := bstep (se 1 (by rfl) ⟨196964, by rfl⟩ : syracuseStep 262619 = 393929) B393929
theorem B590345 : Blo 259821 590345 := bstep (se 2 (by rfl) ⟨221379, by rfl⟩ : syracuseStep 590345 = 442759) B442759
theorem B393737 : Blo 259821 393737 := bstep (se 2 (by rfl) ⟨147651, by rfl⟩ : syracuseStep 393737 = 295303) B295303
theorem B393767 : Blo 259821 393767 := bstep (se 1 (by rfl) ⟨295325, by rfl⟩ : syracuseStep 393767 = 590651) B590651
theorem B262695 : Blo 259821 262695 := bstep (se 1 (by rfl) ⟨197021, by rfl⟩ : syracuseStep 262695 = 394043) B394043
theorem B2228795 : Blo 259821 2228795 := bstep (se 1 (by rfl) ⟨1671596, by rfl⟩ : syracuseStep 2228795 = 3343193) B3343193
theorem B262735 : Blo 259821 262735 := bstep (se 1 (by rfl) ⟨197051, by rfl⟩ : syracuseStep 262735 = 394103) B394103
theorem B262751 : Blo 259821 262751 := bstep (se 1 (by rfl) ⟨197063, by rfl⟩ : syracuseStep 262751 = 394127) B394127
theorem B393851 : Blo 259821 393851 := bstep (se 1 (by rfl) ⟨295388, by rfl⟩ : syracuseStep 393851 = 590777) B590777
theorem B262779 : Blo 259821 262779 := bstep (se 1 (by rfl) ⟨197084, by rfl⟩ : syracuseStep 262779 = 394169) B394169
theorem B885383 : Blo 259821 885383 := bstep (se 1 (by rfl) ⟨664037, by rfl⟩ : syracuseStep 885383 = 1328075) B1328075
theorem B262831 : Blo 259821 262831 := bstep (se 1 (by rfl) ⟨197123, by rfl⟩ : syracuseStep 262831 = 394247) B394247
theorem B885437 : Blo 259821 885437 := bstep (se 3 (by rfl) ⟨166019, by rfl⟩ : syracuseStep 885437 = 332039) B332039
theorem B262855 : Blo 259821 262855 := bstep (se 1 (by rfl) ⟨197141, by rfl⟩ : syracuseStep 262855 = 394283) B394283
theorem B262875 : Blo 259821 262875 := bstep (se 1 (by rfl) ⟨197156, by rfl⟩ : syracuseStep 262875 = 394313) B394313
theorem B393977 : Blo 259821 393977 := bstep (se 2 (by rfl) ⟨147741, by rfl⟩ : syracuseStep 393977 = 295483) B295483
theorem B262951 : Blo 259821 262951 := bstep (se 1 (by rfl) ⟨197213, by rfl⟩ : syracuseStep 262951 = 394427) B394427
theorem B262991 : Blo 259821 262991 := bstep (se 1 (by rfl) ⟨197243, by rfl⟩ : syracuseStep 262991 = 394487) B394487
theorem B885599 : Blo 259821 885599 := bstep (se 1 (by rfl) ⟨664199, by rfl⟩ : syracuseStep 885599 = 1328399) B1328399
theorem B590687 : Blo 259821 590687 := bstep (se 1 (by rfl) ⟨443015, by rfl⟩ : syracuseStep 590687 = 886031) B886031
theorem B394079 : Blo 259821 394079 := bstep (se 1 (by rfl) ⟨295559, by rfl⟩ : syracuseStep 394079 = 591119) B591119
theorem B263007 : Blo 259821 263007 := bstep (se 1 (by rfl) ⟨197255, by rfl⟩ : syracuseStep 263007 = 394511) B394511
theorem B394091 : Blo 259821 394091 := bstep (se 1 (by rfl) ⟨295568, by rfl⟩ : syracuseStep 394091 = 591137) B591137
theorem B263035 : Blo 259821 263035 := bstep (se 1 (by rfl) ⟨197276, by rfl⟩ : syracuseStep 263035 = 394553) B394553
theorem B263087 : Blo 259821 263087 := bstep (se 1 (by rfl) ⟨197315, by rfl⟩ : syracuseStep 263087 = 394631) B394631
theorem B263111 : Blo 259821 263111 := bstep (se 1 (by rfl) ⟨197333, by rfl⟩ : syracuseStep 263111 = 394667) B394667
theorem B263131 : Blo 259821 263131 := bstep (se 1 (by rfl) ⟨197348, by rfl⟩ : syracuseStep 263131 = 394697) B394697
theorem B885761 : Blo 259821 885761 := bstep (se 2 (by rfl) ⟨332160, by rfl⟩ : syracuseStep 885761 = 664321) B664321
theorem B590867 : Blo 259821 590867 := bstep (se 1 (by rfl) ⟨443150, by rfl⟩ : syracuseStep 590867 = 886301) B886301
theorem B263207 : Blo 259821 263207 := bstep (se 1 (by rfl) ⟨197405, by rfl⟩ : syracuseStep 263207 = 394811) B394811
theorem B1672235 : Blo 259821 1672235 := bstep (se 1 (by rfl) ⟨1254176, by rfl⟩ : syracuseStep 1672235 = 2508353) B2508353
theorem B394319 : Blo 259821 394319 := bstep (se 1 (by rfl) ⟨295739, by rfl⟩ : syracuseStep 394319 = 591479) B591479
theorem B263247 : Blo 259821 263247 := bstep (se 1 (by rfl) ⟨197435, by rfl⟩ : syracuseStep 263247 = 394871) B394871
theorem B263263 : Blo 259821 263263 := bstep (se 1 (by rfl) ⟨197447, by rfl⟩ : syracuseStep 263263 = 394895) B394895
theorem B296059 : Blo 259821 296059 := bstep (se 1 (by rfl) ⟨222044, by rfl⟩ : syracuseStep 296059 = 444089) B444089
theorem B263291 : Blo 259821 263291 := bstep (se 1 (by rfl) ⟨197468, by rfl⟩ : syracuseStep 263291 = 394937) B394937
theorem B263343 : Blo 259821 263343 := bstep (se 1 (by rfl) ⟨197507, by rfl⟩ : syracuseStep 263343 = 395015) B395015
theorem B394439 : Blo 259821 394439 := bstep (se 1 (by rfl) ⟨295829, by rfl⟩ : syracuseStep 394439 = 591659) B591659
theorem B263367 : Blo 259821 263367 := bstep (se 1 (by rfl) ⟨197525, by rfl⟩ : syracuseStep 263367 = 395051) B395051
theorem B263387 : Blo 259821 263387 := bstep (se 1 (by rfl) ⟨197540, by rfl⟩ : syracuseStep 263387 = 395081) B395081
theorem B263463 : Blo 259821 263463 := bstep (se 1 (by rfl) ⟨197597, by rfl⟩ : syracuseStep 263463 = 395195) B395195
theorem B263503 : Blo 259821 263503 := bstep (se 1 (by rfl) ⟨197627, by rfl⟩ : syracuseStep 263503 = 395255) B395255
theorem B263519 : Blo 259821 263519 := bstep (se 1 (by rfl) ⟨197639, by rfl⟩ : syracuseStep 263519 = 395279) B395279
theorem B591209 : Blo 259821 591209 := bstep (se 2 (by rfl) ⟨221703, by rfl⟩ : syracuseStep 591209 = 443407) B443407
theorem B394601 : Blo 259821 394601 := bstep (se 2 (by rfl) ⟨147975, by rfl⟩ : syracuseStep 394601 = 295951) B295951
theorem B263547 : Blo 259821 263547 := bstep (se 1 (by rfl) ⟨197660, by rfl⟩ : syracuseStep 263547 = 395321) B395321
theorem B263599 : Blo 259821 263599 := bstep (se 1 (by rfl) ⟨197699, by rfl⟩ : syracuseStep 263599 = 395399) B395399
theorem B394679 : Blo 259821 394679 := bstep (se 1 (by rfl) ⟨296009, by rfl⟩ : syracuseStep 394679 = 592019) B592019
theorem B263623 : Blo 259821 263623 := bstep (se 1 (by rfl) ⟨197717, by rfl⟩ : syracuseStep 263623 = 395435) B395435
theorem B4326857 : Blo 259821 4326857 := bstep (se 2 (by rfl) ⟨1622571, by rfl⟩ : syracuseStep 4326857 = 3245143) B3245143
theorem B329179 : Blo 259821 329179 := bstep (se 1 (by rfl) ⟨246884, by rfl⟩ : syracuseStep 329179 = 493769) B493769
theorem B394715 : Blo 259821 394715 := bstep (se 1 (by rfl) ⟨296036, by rfl⟩ : syracuseStep 394715 = 592073) B592073
theorem B263643 : Blo 259821 263643 := bstep (se 1 (by rfl) ⟨197732, by rfl⟩ : syracuseStep 263643 = 395465) B395465
theorem B263719 : Blo 259821 263719 := bstep (se 1 (by rfl) ⟨197789, by rfl⟩ : syracuseStep 263719 = 395579) B395579
theorem B296527 : Blo 259821 296527 := bstep (se 1 (by rfl) ⟨222395, by rfl⟩ : syracuseStep 296527 = 444791) B444791
theorem B263759 : Blo 259821 263759 := bstep (se 1 (by rfl) ⟨197819, by rfl⟩ : syracuseStep 263759 = 395639) B395639
theorem B263775 : Blo 259821 263775 := bstep (se 1 (by rfl) ⟨197831, by rfl⟩ : syracuseStep 263775 = 395663) B395663
theorem B263803 : Blo 259821 263803 := bstep (se 1 (by rfl) ⟨197852, by rfl⟩ : syracuseStep 263803 = 395705) B395705
theorem B3344165 : Blo 259821 3344165 := bstep (se 4 (by rfl) ⟨313515, by rfl⟩ : syracuseStep 3344165 = 627031) B627031
theorem B886571 : Blo 259821 886571 := bstep (se 1 (by rfl) ⟨664928, by rfl⟩ : syracuseStep 886571 = 1329857) B1329857
theorem B395183 : Blo 259821 395183 := bstep (se 1 (by rfl) ⟨296387, by rfl⟩ : syracuseStep 395183 = 592775) B592775
theorem B591803 : Blo 259821 591803 := bstep (se 1 (by rfl) ⟨443852, by rfl⟩ : syracuseStep 591803 = 887705) B887705
theorem B395273 : Blo 259821 395273 := bstep (se 2 (by rfl) ⟨148227, by rfl⟩ : syracuseStep 395273 = 296455) B296455
theorem B395303 : Blo 259821 395303 := bstep (se 1 (by rfl) ⟨296477, by rfl⟩ : syracuseStep 395303 = 592955) B592955
theorem B886841 : Blo 259821 886841 := bstep (se 2 (by rfl) ⟨332565, by rfl⟩ : syracuseStep 886841 = 665131) B665131
theorem B591929 : Blo 259821 591929 := bstep (se 2 (by rfl) ⟨221973, by rfl⟩ : syracuseStep 591929 = 443947) B443947
theorem B395387 : Blo 259821 395387 := bstep (se 1 (by rfl) ⟨296540, by rfl⟩ : syracuseStep 395387 = 593081) B593081
theorem B395513 : Blo 259821 395513 := bstep (se 2 (by rfl) ⟨148317, by rfl⟩ : syracuseStep 395513 = 296635) B296635
theorem B395615 : Blo 259821 395615 := bstep (se 1 (by rfl) ⟨296711, by rfl⟩ : syracuseStep 395615 = 593423) B593423
theorem B395627 : Blo 259821 395627 := bstep (se 1 (by rfl) ⟨296720, by rfl⟩ : syracuseStep 395627 = 593441) B593441
theorem B887165 : Blo 259821 887165 := bstep (se 3 (by rfl) ⟨166343, by rfl⟩ : syracuseStep 887165 = 332687) B332687
theorem B592271 : Blo 259821 592271 := bstep (se 1 (by rfl) ⟨444203, by rfl⟩ : syracuseStep 592271 = 888407) B888407
theorem B854491 : Blo 259821 854491 := bstep (se 1 (by rfl) ⟨640868, by rfl⟩ : syracuseStep 854491 = 1281737) B1281737
theorem B887435 : Blo 259821 887435 := bstep (se 1 (by rfl) ⟨665576, by rfl⟩ : syracuseStep 887435 = 1331153) B1331153
theorem B592595 : Blo 259821 592595 := bstep (se 1 (by rfl) ⟨444446, by rfl⟩ : syracuseStep 592595 = 888893) B888893
theorem B559865 : Blo 259821 559865 := bstep (se 2 (by rfl) ⟨209949, by rfl⟩ : syracuseStep 559865 = 419899) B419899
theorem B658439 : Blo 259821 658439 := bstep (se 1 (by rfl) ⟨493829, by rfl⟩ : syracuseStep 658439 = 987659) B987659
theorem B658489 : Blo 259821 658489 := bstep (se 2 (by rfl) ⟨246933, by rfl⟩ : syracuseStep 658489 = 493867) B493867
theorem B494839 : Blo 259821 494839 := bstep (se 1 (by rfl) ⟨371129, by rfl⟩ : syracuseStep 494839 = 742259) B742259
theorem B658793 : Blo 259821 658793 := bstep (se 2 (by rfl) ⟨247047, by rfl⟩ : syracuseStep 658793 = 494095) B494095
theorem B2002319 : Blo 259821 2002319 := bstep (se 1 (by rfl) ⟨1501739, by rfl⟩ : syracuseStep 2002319 = 3003479) B3003479
theorem B495067 : Blo 259821 495067 := bstep (se 1 (by rfl) ⟨371300, by rfl⟩ : syracuseStep 495067 = 742601) B742601
theorem B888353 : Blo 259821 888353 := bstep (se 2 (by rfl) ⟨333132, by rfl⟩ : syracuseStep 888353 = 666265) B666265
theorem B495143 : Blo 259821 495143 := bstep (se 1 (by rfl) ⟨371357, by rfl⟩ : syracuseStep 495143 = 742715) B742715
theorem B495227 : Blo 259821 495227 := bstep (se 1 (by rfl) ⟨371420, by rfl⟩ : syracuseStep 495227 = 742841) B742841
theorem B3247739 : Blo 259821 3247739 := bstep (se 1 (by rfl) ⟨2435804, by rfl⟩ : syracuseStep 3247739 = 4871609) B4871609
theorem B593531 : Blo 259821 593531 := bstep (se 1 (by rfl) ⟨445148, by rfl⟩ : syracuseStep 593531 = 890297) B890297
theorem B888569 : Blo 259821 888569 := bstep (se 2 (by rfl) ⟨333213, by rfl⟩ : syracuseStep 888569 = 666427) B666427
theorem B986975 : Blo 259821 986975 := bstep (se 1 (by rfl) ⟨740231, by rfl⟩ : syracuseStep 986975 = 1480463) B1480463
theorem B593851 : Blo 259821 593851 := bstep (se 1 (by rfl) ⟨445388, by rfl⟩ : syracuseStep 593851 = 890777) B890777
theorem B888839 : Blo 259821 888839 := bstep (se 1 (by rfl) ⟨666629, by rfl⟩ : syracuseStep 888839 = 1333259) B1333259
theorem B495713 : Blo 259821 495713 := bstep (se 2 (by rfl) ⟨185892, by rfl⟩ : syracuseStep 495713 = 371785) B371785
theorem B888947 : Blo 259821 888947 := bstep (se 1 (by rfl) ⟨666710, by rfl⟩ : syracuseStep 888947 = 1333421) B1333421
theorem B626935 : Blo 259821 626935 := bstep (se 1 (by rfl) ⟨470201, by rfl⟩ : syracuseStep 626935 = 940403) B940403
theorem B889217 : Blo 259821 889217 := bstep (se 2 (by rfl) ⟨333456, by rfl⟩ : syracuseStep 889217 = 666913) B666913
theorem B528815 : Blo 259821 528815 := bstep (se 1 (by rfl) ⟨396611, by rfl⟩ : syracuseStep 528815 = 793223) B793223
theorem B987673 : Blo 259821 987673 := bstep (se 2 (by rfl) ⟨370377, by rfl⟩ : syracuseStep 987673 = 740755) B740755
theorem B856673 : Blo 259821 856673 := bstep (se 2 (by rfl) ⟨321252, by rfl⟩ : syracuseStep 856673 = 642505) B642505
theorem B987947 : Blo 259821 987947 := bstep (se 1 (by rfl) ⟨740960, by rfl⟩ : syracuseStep 987947 = 1481921) B1481921
theorem B987977 : Blo 259821 987977 := bstep (se 2 (by rfl) ⟨370491, by rfl⟩ : syracuseStep 987977 = 740983) B740983
theorem B627551 : Blo 259821 627551 := bstep (se 1 (by rfl) ⟨470663, by rfl⟩ : syracuseStep 627551 = 941327) B941327
theorem B332839 : Blo 259821 332839 := bstep (se 1 (by rfl) ⟨249629, by rfl⟩ : syracuseStep 332839 = 499259) B499259
theorem B890027 : Blo 259821 890027 := bstep (se 1 (by rfl) ⟨667520, by rfl⟩ : syracuseStep 890027 = 1335041) B1335041
theorem B1316087 : Blo 259821 1316087 := bstep (se 1 (by rfl) ⟨987065, by rfl⟩ : syracuseStep 1316087 = 1974131) B1974131
theorem B333163 : Blo 259821 333163 := bstep (se 1 (by rfl) ⟨249872, by rfl⟩ : syracuseStep 333163 = 499745) B499745
theorem B497171 : Blo 259821 497171 := bstep (se 1 (by rfl) ⟨372878, by rfl⟩ : syracuseStep 497171 = 745757) B745757
theorem B661031 : Blo 259821 661031 := bstep (se 1 (by rfl) ⟨495773, by rfl⟩ : syracuseStep 661031 = 991547) B991547
theorem B333391 : Blo 259821 333391 := bstep (se 1 (by rfl) ⟨250043, by rfl⟩ : syracuseStep 333391 = 500087) B500087
theorem B3348161 : Blo 259821 3348161 := bstep (se 2 (by rfl) ⟨1255560, by rfl⟩ : syracuseStep 3348161 = 2511121) B2511121
theorem B1316573 : Blo 259821 1316573 := bstep (se 3 (by rfl) ⟨246857, by rfl⟩ : syracuseStep 1316573 = 493715) B493715
theorem B661355 : Blo 259821 661355 := bstep (se 1 (by rfl) ⟨496016, by rfl⟩ : syracuseStep 661355 = 992033) B992033
theorem B563051 : Blo 259821 563051 := bstep (se 1 (by rfl) ⟨422288, by rfl⟩ : syracuseStep 563051 = 844577) B844577
theorem B1251409 : Blo 259821 1251409 := bstep (se 2 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 1251409 = 938557) B938557
theorem B2136145 : Blo 259821 2136145 := bstep (se 2 (by rfl) ⟨801054, by rfl⟩ : syracuseStep 2136145 = 1602109) B1602109
theorem B1874177 : Blo 259821 1874177 := bstep (se 2 (by rfl) ⟨702816, by rfl⟩ : syracuseStep 1874177 = 1405633) B1405633
theorem B662003 : Blo 259821 662003 := bstep (se 1 (by rfl) ⟨496502, by rfl⟩ : syracuseStep 662003 = 993005) B993005
theorem B662215 : Blo 259821 662215 := bstep (se 1 (by rfl) ⟨496661, by rfl⟩ : syracuseStep 662215 = 993323) B993323
theorem B498575 : Blo 259821 498575 := bstep (se 1 (by rfl) ⟨373931, by rfl⟩ : syracuseStep 498575 = 747863) B747863
theorem B498727 : Blo 259821 498727 := bstep (se 1 (by rfl) ⟨374045, by rfl⟩ : syracuseStep 498727 = 748091) B748091
theorem B498811 : Blo 259821 498811 := bstep (se 1 (by rfl) ⟨374108, by rfl⟩ : syracuseStep 498811 = 748217) B748217
theorem B1186987 : Blo 259821 1186987 := bstep (se 1 (by rfl) ⟨890240, by rfl⟩ : syracuseStep 1186987 = 1780481) B1780481
theorem B1580311 : Blo 259821 1580311 := bstep (se 1 (by rfl) ⟨1185233, by rfl⟩ : syracuseStep 1580311 = 2370467) B2370467
theorem B990589 : Blo 259821 990589 := bstep (se 3 (by rfl) ⟨185735, by rfl⟩ : syracuseStep 990589 = 371471) B371471
theorem B663137 : Blo 259821 663137 := bstep (se 2 (by rfl) ⟨248676, by rfl⟩ : syracuseStep 663137 = 497353) B497353
theorem B499297 : Blo 259821 499297 := bstep (se 2 (by rfl) ⟨187236, by rfl⟩ : syracuseStep 499297 = 374473) B374473
theorem B532091 : Blo 259821 532091 := bstep (se 1 (by rfl) ⟨399068, by rfl⟩ : syracuseStep 532091 = 798137) B798137
theorem B1417331 : Blo 259821 1417331 := bstep (se 1 (by rfl) ⟨1062998, by rfl⟩ : syracuseStep 1417331 = 2125997) B2125997
theorem B500231 : Blo 259821 500231 := bstep (se 1 (by rfl) ⟨375173, by rfl⟩ : syracuseStep 500231 = 750347) B750347
theorem B8495675 : Blo 259821 8495675 := bstep (se 1 (by rfl) ⟨6371756, by rfl⟩ : syracuseStep 8495675 = 12743513) B12743513
theorem B664595 : Blo 259821 664595 := bstep (se 1 (by rfl) ⟨498446, by rfl⟩ : syracuseStep 664595 = 996893) B996893
theorem B500755 : Blo 259821 500755 := bstep (se 1 (by rfl) ⟨375566, by rfl⟩ : syracuseStep 500755 = 751133) B751133
theorem B29664461 : Blo 259821 29664461 := bstep (se 3 (by rfl) ⟨5562086, by rfl⟩ : syracuseStep 29664461 = 11124173) B11124173
theorem B1975589 : Blo 259821 1975589 := bstep (se 4 (by rfl) ⟨185211, by rfl⟩ : syracuseStep 1975589 = 370423) B370423
theorem B1025423 : Blo 259821 1025423 := bstep (se 1 (by rfl) ⟨769067, by rfl⟩ : syracuseStep 1025423 = 1538135) B1538135
theorem B468443 : Blo 259821 468443 := bstep (se 1 (by rfl) ⟨351332, by rfl⟩ : syracuseStep 468443 = 702665) B702665
theorem B2827781 : Blo 259821 2827781 := bstep (se 4 (by rfl) ⟨265104, by rfl⟩ : syracuseStep 2827781 = 530209) B530209
theorem B992807 : Blo 259821 992807 := bstep (se 1 (by rfl) ⟨744605, by rfl⟩ : syracuseStep 992807 = 1489211) B1489211
theorem B2991815 : Blo 259821 2991815 := bstep (se 1 (by rfl) ⟨2243861, by rfl⟩ : syracuseStep 2991815 = 4487723) B4487723
theorem B1058669 : Blo 259821 1058669 := bstep (se 3 (by rfl) ⟨198500, by rfl⟩ : syracuseStep 1058669 = 397001) B397001
theorem B370651 : Blo 259821 370651 := bstep (se 1 (by rfl) ⟨277988, by rfl⟩ : syracuseStep 370651 = 555977) B555977
theorem B1484837 : Blo 259821 1484837 := bstep (se 4 (by rfl) ⟨139203, by rfl⟩ : syracuseStep 1484837 = 278407) B278407
theorem B5023781 : Blo 259821 5023781 := bstep (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) B941959
theorem B305275 : Blo 259821 305275 := bstep (se 1 (by rfl) ⟨228956, by rfl⟩ : syracuseStep 305275 = 457913) B457913
theorem B469163 : Blo 259821 469163 := bstep (se 1 (by rfl) ⟨351872, by rfl⟩ : syracuseStep 469163 = 703745) B703745
theorem B3189041 : Blo 259821 3189041 := bstep (se 2 (by rfl) ⟨1195890, by rfl⟩ : syracuseStep 3189041 = 2391781) B2391781
theorem B993779 : Blo 259821 993779 := bstep (se 1 (by rfl) ⟨745334, by rfl⟩ : syracuseStep 993779 = 1490669) B1490669
theorem B1485337 : Blo 259821 1485337 := bstep (se 2 (by rfl) ⟨557001, by rfl⟩ : syracuseStep 1485337 = 1114003) B1114003
theorem B993977 : Blo 259821 993977 := bstep (se 2 (by rfl) ⟨372741, by rfl⟩ : syracuseStep 993977 = 745483) B745483
theorem B993991 : Blo 259821 993991 := bstep (se 1 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 993991 = 1490987) B1490987
theorem B1321757 : Blo 259821 1321757 := bstep (se 3 (by rfl) ⟨247829, by rfl⟩ : syracuseStep 1321757 = 495659) B495659
theorem B9186085 : Blo 259821 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B469855 : Blo 259821 469855 := bstep (se 1 (by rfl) ⟨352391, by rfl⟩ : syracuseStep 469855 = 704783) B704783
theorem B1649591 : Blo 259821 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B994963 : Blo 259821 994963 := bstep (se 1 (by rfl) ⟨746222, by rfl⟩ : syracuseStep 994963 = 1492445) B1492445
theorem B4009661 : Blo 259821 4009661 := bstep (se 3 (by rfl) ⟨751811, by rfl⟩ : syracuseStep 4009661 = 1503623) B1503623
theorem B1421243 : Blo 259821 1421243 := bstep (se 1 (by rfl) ⟨1065932, by rfl⟩ : syracuseStep 1421243 = 2131865) B2131865
theorem B1519883 : Blo 259821 1519883 := bstep (se 1 (by rfl) ⟨1139912, by rfl⟩ : syracuseStep 1519883 = 2279825) B2279825
theorem B438601 : Blo 259821 438601 := bstep (se 2 (by rfl) ⟨164475, by rfl⟩ : syracuseStep 438601 = 328951) B328951
theorem B438635 : Blo 259821 438635 := bstep (se 1 (by rfl) ⟨328976, by rfl⟩ : syracuseStep 438635 = 657953) B657953
theorem B799195 : Blo 259821 799195 := bstep (se 1 (by rfl) ⟨599396, by rfl⟩ : syracuseStep 799195 = 1198793) B1198793
theorem B766561 : Blo 259821 766561 := bstep (se 2 (by rfl) ⟨287460, by rfl⟩ : syracuseStep 766561 = 574921) B574921
theorem B439033 : Blo 259821 439033 := bstep (se 2 (by rfl) ⟨164637, by rfl⟩ : syracuseStep 439033 = 329275) B329275
theorem B439303 : Blo 259821 439303 := bstep (se 1 (by rfl) ⟨329477, by rfl⟩ : syracuseStep 439303 = 658955) B658955
theorem B38810765 : Blo 259821 38810765 := bstep (se 3 (by rfl) ⟨7277018, by rfl⟩ : syracuseStep 38810765 = 14554037) B14554037
theorem B3650831 : Blo 259821 3650831 := bstep (se 1 (by rfl) ⟨2738123, by rfl⟩ : syracuseStep 3650831 = 5476247) B5476247
theorem B996695 : Blo 259821 996695 := bstep (se 1 (by rfl) ⟨747521, by rfl⟩ : syracuseStep 996695 = 1495043) B1495043
theorem B1488253 : Blo 259821 1488253 := bstep (se 3 (by rfl) ⟨279047, by rfl⟩ : syracuseStep 1488253 = 558095) B558095
theorem B439735 : Blo 259821 439735 := bstep (se 1 (by rfl) ⟨329801, by rfl⟩ : syracuseStep 439735 = 659603) B659603
theorem B439931 : Blo 259821 439931 := bstep (se 1 (by rfl) ⟨329948, by rfl⟩ : syracuseStep 439931 = 659897) B659897
theorem B669323 : Blo 259821 669323 := bstep (se 1 (by rfl) ⟨501992, by rfl⟩ : syracuseStep 669323 = 1003985) B1003985
theorem B472825 : Blo 259821 472825 := bstep (se 2 (by rfl) ⟨177309, by rfl⟩ : syracuseStep 472825 = 354619) B354619
theorem B5748515 : Blo 259821 5748515 := bstep (se 1 (by rfl) ⟨4311386, by rfl⟩ : syracuseStep 5748515 = 8622773) B8622773
theorem B2602847 : Blo 259821 2602847 := bstep (se 1 (by rfl) ⟨1952135, by rfl⟩ : syracuseStep 2602847 = 3904271) B3904271
theorem B1685357 : Blo 259821 1685357 := bstep (se 3 (by rfl) ⟨316004, by rfl⟩ : syracuseStep 1685357 = 632009) B632009
theorem B440329 : Blo 259821 440329 := bstep (se 2 (by rfl) ⟨165123, by rfl⟩ : syracuseStep 440329 = 330247) B330247
theorem B440491 : Blo 259821 440491 := bstep (se 1 (by rfl) ⟨330368, by rfl⟩ : syracuseStep 440491 = 660737) B660737
theorem B440795 : Blo 259821 440795 := bstep (se 1 (by rfl) ⟨330596, by rfl⟩ : syracuseStep 440795 = 661193) B661193
theorem B670247 : Blo 259821 670247 := bstep (se 1 (by rfl) ⟨502685, by rfl⟩ : syracuseStep 670247 = 1005371) B1005371
theorem B473771 : Blo 259821 473771 := bstep (se 1 (by rfl) ⟨355328, by rfl⟩ : syracuseStep 473771 = 710657) B710657
theorem B441031 : Blo 259821 441031 := bstep (se 1 (by rfl) ⟨330773, by rfl⟩ : syracuseStep 441031 = 661547) B661547
theorem B441193 : Blo 259821 441193 := bstep (se 2 (by rfl) ⟨165447, by rfl⟩ : syracuseStep 441193 = 330895) B330895
theorem B932879 : Blo 259821 932879 := bstep (se 1 (by rfl) ⟨699659, by rfl⟩ : syracuseStep 932879 = 1399319) B1399319
theorem B1326131 : Blo 259821 1326131 := bstep (se 1 (by rfl) ⟨994598, by rfl⟩ : syracuseStep 1326131 = 1989197) B1989197
theorem B1260791 : Blo 259821 1260791 := bstep (se 1 (by rfl) ⟨945593, by rfl⟩ : syracuseStep 1260791 = 1891187) B1891187
theorem B2997647 : Blo 259821 2997647 := bstep (se 1 (by rfl) ⟨2248235, by rfl⟩ : syracuseStep 2997647 = 4496471) B4496471
theorem B441787 : Blo 259821 441787 := bstep (se 1 (by rfl) ⟨331340, by rfl⟩ : syracuseStep 441787 = 662681) B662681
theorem B441895 : Blo 259821 441895 := bstep (se 1 (by rfl) ⟨331421, by rfl⟩ : syracuseStep 441895 = 662843) B662843
theorem B704351 : Blo 259821 704351 := bstep (se 1 (by rfl) ⟨528263, by rfl⟩ : syracuseStep 704351 = 1056527) B1056527
theorem B442219 : Blo 259821 442219 := bstep (se 1 (by rfl) ⟨331664, by rfl⟩ : syracuseStep 442219 = 663329) B663329
theorem B10141625 : Blo 259821 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B1982393 : Blo 259821 1982393 := bstep (se 2 (by rfl) ⟨743397, by rfl⟩ : syracuseStep 1982393 = 1486795) B1486795
theorem B1196039 : Blo 259821 1196039 := bstep (se 1 (by rfl) ⟨897029, by rfl⟩ : syracuseStep 1196039 = 1794059) B1794059
theorem B3850355 : Blo 259821 3850355 := bstep (se 1 (by rfl) ⟨2887766, by rfl⟩ : syracuseStep 3850355 = 5775533) B5775533
theorem B999809 : Blo 259821 999809 := bstep (se 2 (by rfl) ⟨374928, by rfl⟩ : syracuseStep 999809 = 749857) B749857
theorem B999823 : Blo 259821 999823 := bstep (se 1 (by rfl) ⟨749867, by rfl⟩ : syracuseStep 999823 = 1499735) B1499735
theorem B1327751 : Blo 259821 1327751 := bstep (se 1 (by rfl) ⟨995813, by rfl⟩ : syracuseStep 1327751 = 1991627) B1991627
theorem B2114221 : Blo 259821 2114221 := bstep (se 3 (by rfl) ⟨396416, by rfl⟩ : syracuseStep 2114221 = 792833) B792833
theorem B443279 : Blo 259821 443279 := bstep (se 1 (by rfl) ⟨332459, by rfl⟩ : syracuseStep 443279 = 664919) B664919
theorem B2114579 : Blo 259821 2114579 := bstep (se 1 (by rfl) ⟨1585934, by rfl⟩ : syracuseStep 2114579 = 3171869) B3171869
theorem B443515 : Blo 259821 443515 := bstep (se 1 (by rfl) ⟨332636, by rfl⟩ : syracuseStep 443515 = 665273) B665273
theorem B2967029 : Blo 259821 2967029 := bstep (se 5 (by rfl) ⟨139079, by rfl⟩ : syracuseStep 2967029 = 278159) B278159
theorem B280103 : Blo 259821 280103 := bstep (se 1 (by rfl) ⟨210077, by rfl⟩ : syracuseStep 280103 = 420155) B420155
theorem B5031467 : Blo 259821 5031467 := bstep (se 1 (by rfl) ⟨3773600, by rfl⟩ : syracuseStep 5031467 = 7547201) B7547201
theorem B1001099 : Blo 259821 1001099 := bstep (se 1 (by rfl) ⟨750824, by rfl⟩ : syracuseStep 1001099 = 1501649) B1501649
theorem B1492627 : Blo 259821 1492627 := bstep (se 1 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 1492627 = 2238941) B2238941
theorem B2246291 : Blo 259821 2246291 := bstep (se 1 (by rfl) ⟨1684718, by rfl⟩ : syracuseStep 2246291 = 3369437) B3369437
theorem B444379 : Blo 259821 444379 := bstep (se 1 (by rfl) ⟨333284, by rfl⟩ : syracuseStep 444379 = 666569) B666569
theorem B1329209 : Blo 259821 1329209 := bstep (se 2 (by rfl) ⟨498453, by rfl⟩ : syracuseStep 1329209 = 996907) B996907
theorem B280927 : Blo 259821 280927 := bstep (se 1 (by rfl) ⟨210695, by rfl⟩ : syracuseStep 280927 = 421391) B421391
theorem B3590689 : Blo 259821 3590689 := bstep (se 2 (by rfl) ⟨1346508, by rfl⟩ : syracuseStep 3590689 = 2693017) B2693017
theorem B445007 : Blo 259821 445007 := bstep (se 1 (by rfl) ⟨333755, by rfl⟩ : syracuseStep 445007 = 667511) B667511
theorem B1985309 : Blo 259821 1985309 := bstep (se 3 (by rfl) ⟨372245, by rfl⟩ : syracuseStep 1985309 = 744491) B744491
theorem B4246607 : Blo 259821 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B1068983 : Blo 259821 1068983 := bstep (se 1 (by rfl) ⟨801737, by rfl⟩ : syracuseStep 1068983 = 1603475) B1603475
theorem B741383 : Blo 259821 741383 := bstep (se 1 (by rfl) ⟨556037, by rfl⟩ : syracuseStep 741383 = 1112075) B1112075
theorem B1626193 : Blo 259821 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B1331315 : Blo 259821 1331315 := bstep (se 1 (by rfl) ⟨998486, by rfl⟩ : syracuseStep 1331315 = 1996973) B1996973
theorem B315515 : Blo 259821 315515 := bstep (se 1 (by rfl) ⟨236636, by rfl⟩ : syracuseStep 315515 = 473273) B473273
theorem B938155 : Blo 259821 938155 := bstep (se 1 (by rfl) ⟨703616, by rfl⟩ : syracuseStep 938155 = 1407233) B1407233
theorem B840041 : Blo 259821 840041 := bstep (se 2 (by rfl) ⟨315015, by rfl⟩ : syracuseStep 840041 = 630031) B630031
theorem B447419 : Blo 259821 447419 := bstep (se 1 (by rfl) ⟨335564, by rfl⟩ : syracuseStep 447419 = 671129) B671129
theorem B840719 : Blo 259821 840719 := bstep (se 1 (by rfl) ⟨630539, by rfl⟩ : syracuseStep 840719 = 1261079) B1261079
theorem B2512043 : Blo 259821 2512043 := bstep (se 1 (by rfl) ⟨1884032, by rfl⟩ : syracuseStep 2512043 = 3768065) B3768065
theorem B1332935 : Blo 259821 1332935 := bstep (se 1 (by rfl) ⟨999701, by rfl⟩ : syracuseStep 1332935 = 1999403) B1999403
theorem B2119769 : Blo 259821 2119769 := bstep (se 2 (by rfl) ⟨794913, by rfl⟩ : syracuseStep 2119769 = 1589827) B1589827
theorem B743671 : Blo 259821 743671 := bstep (se 1 (by rfl) ⟨557753, by rfl⟩ : syracuseStep 743671 = 1115507) B1115507
theorem B2677043 : Blo 259821 2677043 := bstep (se 1 (by rfl) ⟨2007782, by rfl⟩ : syracuseStep 2677043 = 4015565) B4015565
theorem B743899 : Blo 259821 743899 := bstep (se 1 (by rfl) ⟨557924, by rfl⟩ : syracuseStep 743899 = 1115849) B1115849
theorem B744059 : Blo 259821 744059 := bstep (se 1 (by rfl) ⟨558044, by rfl⟩ : syracuseStep 744059 = 1116089) B1116089
theorem B744299 : Blo 259821 744299 := bstep (se 1 (by rfl) ⟨558224, by rfl⟩ : syracuseStep 744299 = 1116449) B1116449
theorem B711607 : Blo 259821 711607 := bstep (se 1 (by rfl) ⟨533705, by rfl⟩ : syracuseStep 711607 = 1067411) B1067411
theorem B1989683 : Blo 259821 1989683 := bstep (se 1 (by rfl) ⟨1492262, by rfl⟩ : syracuseStep 1989683 = 2984525) B2984525
theorem B1268939 : Blo 259821 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B1334701 : Blo 259821 1334701 := bstep (se 3 (by rfl) ⟨250256, by rfl⟩ : syracuseStep 1334701 = 500513) B500513
theorem B2874797 : Blo 259821 2874797 := bstep (se 3 (by rfl) ⟨539024, by rfl⟩ : syracuseStep 2874797 = 1078049) B1078049
theorem B7167449 : Blo 259821 7167449 := bstep (se 2 (by rfl) ⟨2687793, by rfl⟩ : syracuseStep 7167449 = 5375587) B5375587
theorem B941555 : Blo 259821 941555 := bstep (se 1 (by rfl) ⟨706166, by rfl⟩ : syracuseStep 941555 = 1412333) B1412333
theorem B744947 : Blo 259821 744947 := bstep (se 1 (by rfl) ⟨558710, by rfl⟩ : syracuseStep 744947 = 1117421) B1117421
theorem B1891937 : Blo 259821 1891937 := bstep (se 2 (by rfl) ⟨709476, by rfl⟩ : syracuseStep 1891937 = 1418953) B1418953
theorem B712331 : Blo 259821 712331 := bstep (se 1 (by rfl) ⟨534248, by rfl⟩ : syracuseStep 712331 = 1068497) B1068497
theorem B745175 : Blo 259821 745175 := bstep (se 1 (by rfl) ⟨558881, by rfl⟩ : syracuseStep 745175 = 1117763) B1117763
theorem B19259201 : Blo 259821 19259201 := bstep (se 2 (by rfl) ⟨7222200, by rfl⟩ : syracuseStep 19259201 = 14444401) B14444401
theorem B319339 : Blo 259821 319339 := bstep (se 1 (by rfl) ⟨239504, by rfl⟩ : syracuseStep 319339 = 479009) B479009
theorem B2220047 : Blo 259821 2220047 := bstep (se 1 (by rfl) ⟨1665035, by rfl⟩ : syracuseStep 2220047 = 3330071) B3330071
theorem B843833 : Blo 259821 843833 := bstep (se 2 (by rfl) ⟨316437, by rfl⟩ : syracuseStep 843833 = 632875) B632875
theorem B3792977 : Blo 259821 3792977 := bstep (se 2 (by rfl) ⟨1422366, by rfl⟩ : syracuseStep 3792977 = 2844733) B2844733
theorem B12312931 : Blo 259821 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B876905 : Blo 259821 876905 := bstep (se 2 (by rfl) ⟨328839, by rfl⟩ : syracuseStep 876905 = 657679) B657679
theorem B942479 : Blo 259821 942479 := bstep (se 1 (by rfl) ⟨706859, by rfl⟩ : syracuseStep 942479 = 1413719) B1413719
theorem B3367433 : Blo 259821 3367433 := bstep (se 2 (by rfl) ⟨1262787, by rfl⟩ : syracuseStep 3367433 = 2525575) B2525575
theorem B484039 : Blo 259821 484039 := bstep (se 1 (by rfl) ⟨363029, by rfl⟩ : syracuseStep 484039 = 726059) B726059
theorem B877499 : Blo 259821 877499 := bstep (se 1 (by rfl) ⟨658124, by rfl⟩ : syracuseStep 877499 = 1316249) B1316249
theorem B648271 : Blo 259821 648271 := bstep (se 1 (by rfl) ⟨486203, by rfl⟩ : syracuseStep 648271 = 972407) B972407
theorem B15262937 : Blo 259821 15262937 := bstep (se 2 (by rfl) ⟨5723601, by rfl⟩ : syracuseStep 15262937 = 11447203) B11447203
theorem B353641 : Blo 259821 353641 := bstep (se 2 (by rfl) ⟨132615, by rfl⟩ : syracuseStep 353641 = 265231) B265231
theorem B943805 : Blo 259821 943805 := bstep (se 3 (by rfl) ⟨176963, by rfl⟩ : syracuseStep 943805 = 353927) B353927
theorem B419879 : Blo 259821 419879 := bstep (se 1 (by rfl) ⟨314909, by rfl⟩ : syracuseStep 419879 = 629819) B629819
theorem B1141121 : Blo 259821 1141121 := bstep (se 2 (by rfl) ⟨427920, by rfl⟩ : syracuseStep 1141121 = 855841) B855841
theorem B879227 : Blo 259821 879227 := bstep (se 1 (by rfl) ⟨659420, by rfl⟩ : syracuseStep 879227 = 1318841) B1318841
theorem B879389 : Blo 259821 879389 := bstep (se 3 (by rfl) ⟨164885, by rfl⟩ : syracuseStep 879389 = 329771) B329771
theorem B1797011 : Blo 259821 1797011 := bstep (se 1 (by rfl) ⟨1347758, by rfl⟩ : syracuseStep 1797011 = 2695517) B2695517
theorem B584711 : Blo 259821 584711 := bstep (se 1 (by rfl) ⟨438533, by rfl⟩ : syracuseStep 584711 = 877067) B877067
theorem B584783 : Blo 259821 584783 := bstep (se 1 (by rfl) ⟨438587, by rfl⟩ : syracuseStep 584783 = 877175) B877175
theorem B585179 : Blo 259821 585179 := bstep (se 1 (by rfl) ⟨438884, by rfl⟩ : syracuseStep 585179 = 877769) B877769
theorem B880091 : Blo 259821 880091 := bstep (se 1 (by rfl) ⟨660068, by rfl⟩ : syracuseStep 880091 = 1320137) B1320137
theorem B6844121 : Blo 259821 6844121 := bstep (se 2 (by rfl) ⟨2566545, by rfl⟩ : syracuseStep 6844121 = 5133091) B5133091
theorem B585647 : Blo 259821 585647 := bstep (se 1 (by rfl) ⟨439235, by rfl⟩ : syracuseStep 585647 = 878471) B878471
theorem B1667087 : Blo 259821 1667087 := bstep (se 1 (by rfl) ⟨1250315, by rfl⟩ : syracuseStep 1667087 = 2500631) B2500631
theorem B880793 : Blo 259821 880793 := bstep (se 2 (by rfl) ⟨330297, by rfl⟩ : syracuseStep 880793 = 660595) B660595
theorem B585899 : Blo 259821 585899 := bstep (se 1 (by rfl) ⟨439424, by rfl⟩ : syracuseStep 585899 = 878849) B878849
theorem B422327 : Blo 259821 422327 := bstep (se 1 (by rfl) ⟨316745, by rfl⟩ : syracuseStep 422327 = 633491) B633491
theorem B2912777 : Blo 259821 2912777 := bstep (se 2 (by rfl) ⟨1092291, by rfl⟩ : syracuseStep 2912777 = 2184583) B2184583
theorem B389831 : Blo 259821 389831 := bstep (se 1 (by rfl) ⟨292373, by rfl⟩ : syracuseStep 389831 = 584747) B584747
theorem B586439 : Blo 259821 586439 := bstep (se 1 (by rfl) ⟨439829, by rfl⟩ : syracuseStep 586439 = 879659) B879659
theorem B389993 : Blo 259821 389993 := bstep (se 2 (by rfl) ⟨146247, by rfl⟩ : syracuseStep 389993 = 292495) B292495
theorem B390071 : Blo 259821 390071 := bstep (se 1 (by rfl) ⟨292553, by rfl⟩ : syracuseStep 390071 = 585107) B585107
theorem B390107 : Blo 259821 390107 := bstep (se 1 (by rfl) ⟨292580, by rfl⟩ : syracuseStep 390107 = 585161) B585161
theorem B947207 : Blo 259821 947207 := bstep (se 1 (by rfl) ⟨710405, by rfl⟩ : syracuseStep 947207 = 1420811) B1420811
theorem B947467 : Blo 259821 947467 := bstep (se 1 (by rfl) ⟨710600, by rfl⟩ : syracuseStep 947467 = 1421201) B1421201
theorem B881981 : Blo 259821 881981 := bstep (se 3 (by rfl) ⟨165371, by rfl⟩ : syracuseStep 881981 = 330743) B330743
theorem B390575 : Blo 259821 390575 := bstep (se 1 (by rfl) ⟨292931, by rfl⟩ : syracuseStep 390575 = 585863) B585863
theorem B292315 : Blo 259821 292315 := bstep (se 1 (by rfl) ⟨219236, by rfl⟩ : syracuseStep 292315 = 438473) B438473
theorem B390665 : Blo 259821 390665 := bstep (se 2 (by rfl) ⟨146499, by rfl⟩ : syracuseStep 390665 = 292999) B292999
theorem B390695 : Blo 259821 390695 := bstep (se 1 (by rfl) ⟨293021, by rfl⟩ : syracuseStep 390695 = 586043) B586043
theorem B587303 : Blo 259821 587303 := bstep (se 1 (by rfl) ⟨440477, by rfl⟩ : syracuseStep 587303 = 880955) B880955
theorem B390779 : Blo 259821 390779 := bstep (se 1 (by rfl) ⟨293084, by rfl⟩ : syracuseStep 390779 = 586169) B586169
theorem B1996487 : Blo 259821 1996487 := bstep (se 1 (by rfl) ⟨1497365, by rfl⟩ : syracuseStep 1996487 = 2994731) B2994731
theorem B390905 : Blo 259821 390905 := bstep (se 2 (by rfl) ⟨146589, by rfl⟩ : syracuseStep 390905 = 293179) B293179
theorem B259879 : Blo 259821 259879 := bstep (se 1 (by rfl) ⟨194909, by rfl⟩ : syracuseStep 259879 = 389819) B389819
theorem B259919 : Blo 259821 259919 := bstep (se 1 (by rfl) ⟨194939, by rfl⟩ : syracuseStep 259919 = 389879) B389879
theorem B4028249 : Blo 259821 4028249 := bstep (se 2 (by rfl) ⟨1510593, by rfl⟩ : syracuseStep 4028249 = 3021187) B3021187
theorem B259935 : Blo 259821 259935 := bstep (se 1 (by rfl) ⟨194951, by rfl⟩ : syracuseStep 259935 = 389903) B389903
theorem B391007 : Blo 259821 391007 := bstep (se 1 (by rfl) ⟨293255, by rfl⟩ : syracuseStep 391007 = 586511) B586511
theorem B391019 : Blo 259821 391019 := bstep (se 1 (by rfl) ⟨293264, by rfl⟩ : syracuseStep 391019 = 586529) B586529
theorem B587627 : Blo 259821 587627 := bstep (se 1 (by rfl) ⟨440720, by rfl⟩ : syracuseStep 587627 = 881441) B881441
theorem B259963 : Blo 259821 259963 := bstep (se 1 (by rfl) ⟨194972, by rfl⟩ : syracuseStep 259963 = 389945) B389945
theorem B587681 : Blo 259821 587681 := bstep (se 2 (by rfl) ⟨220380, by rfl⟩ : syracuseStep 587681 = 440761) B440761
theorem B260015 : Blo 259821 260015 := bstep (se 1 (by rfl) ⟨195011, by rfl⟩ : syracuseStep 260015 = 390023) B390023
theorem B292783 : Blo 259821 292783 := bstep (se 1 (by rfl) ⟨219587, by rfl⟩ : syracuseStep 292783 = 439175) B439175
theorem B260039 : Blo 259821 260039 := bstep (se 1 (by rfl) ⟨195029, by rfl⟩ : syracuseStep 260039 = 390059) B390059
theorem B260059 : Blo 259821 260059 := bstep (se 1 (by rfl) ⟨195044, by rfl⟩ : syracuseStep 260059 = 390089) B390089
theorem B260135 : Blo 259821 260135 := bstep (se 1 (by rfl) ⟨195101, by rfl⟩ : syracuseStep 260135 = 390203) B390203
theorem B260175 : Blo 259821 260175 := bstep (se 1 (by rfl) ⟨195131, by rfl⟩ : syracuseStep 260175 = 390263) B390263
theorem B391247 : Blo 259821 391247 := bstep (se 1 (by rfl) ⟨293435, by rfl⟩ : syracuseStep 391247 = 586871) B586871
theorem B260191 : Blo 259821 260191 := bstep (se 1 (by rfl) ⟨195143, by rfl⟩ : syracuseStep 260191 = 390287) B390287
theorem B260219 : Blo 259821 260219 := bstep (se 1 (by rfl) ⟨195164, by rfl⟩ : syracuseStep 260219 = 390329) B390329
theorem B882845 : Blo 259821 882845 := bstep (se 3 (by rfl) ⟨165533, by rfl⟩ : syracuseStep 882845 = 331067) B331067
theorem B260271 : Blo 259821 260271 := bstep (se 1 (by rfl) ⟨195203, by rfl⟩ : syracuseStep 260271 = 390407) B390407
theorem B948419 : Blo 259821 948419 := bstep (se 1 (by rfl) ⟨711314, by rfl⟩ : syracuseStep 948419 = 1422629) B1422629
theorem B260295 : Blo 259821 260295 := bstep (se 1 (by rfl) ⟨195221, by rfl⟩ : syracuseStep 260295 = 390443) B390443
theorem B391367 : Blo 259821 391367 := bstep (se 1 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 391367 = 587051) B587051
theorem B260315 : Blo 259821 260315 := bstep (se 1 (by rfl) ⟨195236, by rfl⟩ : syracuseStep 260315 = 390473) B390473
theorem B588023 : Blo 259821 588023 := bstep (se 1 (by rfl) ⟨441017, by rfl⟩ : syracuseStep 588023 = 882035) B882035
theorem B260391 : Blo 259821 260391 := bstep (se 1 (by rfl) ⟨195293, by rfl⟩ : syracuseStep 260391 = 390587) B390587
theorem B260431 : Blo 259821 260431 := bstep (se 1 (by rfl) ⟨195323, by rfl⟩ : syracuseStep 260431 = 390647) B390647
theorem B260447 : Blo 259821 260447 := bstep (se 1 (by rfl) ⟨195335, by rfl⟩ : syracuseStep 260447 = 390671) B390671
theorem B293215 : Blo 259821 293215 := bstep (se 1 (by rfl) ⟨219911, by rfl⟩ : syracuseStep 293215 = 439823) B439823
theorem B391529 : Blo 259821 391529 := bstep (se 2 (by rfl) ⟨146823, by rfl⟩ : syracuseStep 391529 = 293647) B293647
theorem B260475 : Blo 259821 260475 := bstep (se 1 (by rfl) ⟨195356, by rfl⟩ : syracuseStep 260475 = 390713) B390713
theorem B260527 : Blo 259821 260527 := bstep (se 1 (by rfl) ⟨195395, by rfl⟩ : syracuseStep 260527 = 390791) B390791
theorem B391607 : Blo 259821 391607 := bstep (se 1 (by rfl) ⟨293705, by rfl⟩ : syracuseStep 391607 = 587411) B587411
theorem B260551 : Blo 259821 260551 := bstep (se 1 (by rfl) ⟨195413, by rfl⟩ : syracuseStep 260551 = 390827) B390827
theorem B260571 : Blo 259821 260571 := bstep (se 1 (by rfl) ⟨195428, by rfl⟩ : syracuseStep 260571 = 390857) B390857
theorem B391643 : Blo 259821 391643 := bstep (se 1 (by rfl) ⟨293732, by rfl⟩ : syracuseStep 391643 = 587465) B587465
theorem B260647 : Blo 259821 260647 := bstep (se 1 (by rfl) ⟨195485, by rfl⟩ : syracuseStep 260647 = 390971) B390971
theorem B7600715 : Blo 259821 7600715 := bstep (se 1 (by rfl) ⟨5700536, by rfl⟩ : syracuseStep 7600715 = 11401073) B11401073
theorem B260687 : Blo 259821 260687 := bstep (se 1 (by rfl) ⟨195515, by rfl⟩ : syracuseStep 260687 = 391031) B391031
theorem B260703 : Blo 259821 260703 := bstep (se 1 (by rfl) ⟨195527, by rfl⟩ : syracuseStep 260703 = 391055) B391055
theorem B260731 : Blo 259821 260731 := bstep (se 1 (by rfl) ⟨195548, by rfl⟩ : syracuseStep 260731 = 391097) B391097
theorem B260783 : Blo 259821 260783 := bstep (se 1 (by rfl) ⟨195587, by rfl⟩ : syracuseStep 260783 = 391175) B391175
theorem B883385 : Blo 259821 883385 := bstep (se 2 (by rfl) ⟨331269, by rfl⟩ : syracuseStep 883385 = 662539) B662539
theorem B260807 : Blo 259821 260807 := bstep (se 1 (by rfl) ⟨195605, by rfl⟩ : syracuseStep 260807 = 391211) B391211
theorem B293575 : Blo 259821 293575 := bstep (se 1 (by rfl) ⟨220181, by rfl⟩ : syracuseStep 293575 = 440363) B440363
theorem B260827 : Blo 259821 260827 := bstep (se 1 (by rfl) ⟨195620, by rfl⟩ : syracuseStep 260827 = 391241) B391241
theorem B260903 : Blo 259821 260903 := bstep (se 1 (by rfl) ⟨195677, by rfl⟩ : syracuseStep 260903 = 391355) B391355
theorem B588617 : Blo 259821 588617 := bstep (se 2 (by rfl) ⟨220731, by rfl⟩ : syracuseStep 588617 = 441463) B441463
theorem B260943 : Blo 259821 260943 := bstep (se 1 (by rfl) ⟨195707, by rfl⟩ : syracuseStep 260943 = 391415) B391415
theorem B260959 : Blo 259821 260959 := bstep (se 1 (by rfl) ⟨195719, by rfl⟩ : syracuseStep 260959 = 391439) B391439
theorem B359273 : Blo 259821 359273 := bstep (se 2 (by rfl) ⟨134727, by rfl⟩ : syracuseStep 359273 = 269455) B269455
theorem B260987 : Blo 259821 260987 := bstep (se 1 (by rfl) ⟨195740, by rfl⟩ : syracuseStep 260987 = 391481) B391481
theorem B261039 : Blo 259821 261039 := bstep (se 1 (by rfl) ⟨195779, by rfl⟩ : syracuseStep 261039 = 391559) B391559
theorem B392111 : Blo 259821 392111 := bstep (se 1 (by rfl) ⟨294083, by rfl⟩ : syracuseStep 392111 = 588167) B588167
theorem B687035 : Blo 259821 687035 := bstep (se 1 (by rfl) ⟨515276, by rfl⟩ : syracuseStep 687035 = 1030553) B1030553
theorem B261063 : Blo 259821 261063 := bstep (se 1 (by rfl) ⟨195797, by rfl⟩ : syracuseStep 261063 = 391595) B391595
theorem B261083 : Blo 259821 261083 := bstep (se 1 (by rfl) ⟨195812, by rfl⟩ : syracuseStep 261083 = 391625) B391625
theorem B392201 : Blo 259821 392201 := bstep (se 2 (by rfl) ⟨147075, by rfl⟩ : syracuseStep 392201 = 294151) B294151
theorem B261159 : Blo 259821 261159 := bstep (se 1 (by rfl) ⟨195869, by rfl⟩ : syracuseStep 261159 = 391739) B391739
theorem B392231 : Blo 259821 392231 := bstep (se 1 (by rfl) ⟨294173, by rfl⟩ : syracuseStep 392231 = 588347) B588347
theorem B261199 : Blo 259821 261199 := bstep (se 1 (by rfl) ⟨195899, by rfl⟩ : syracuseStep 261199 = 391799) B391799
theorem B261215 : Blo 259821 261215 := bstep (se 1 (by rfl) ⟨195911, by rfl⟩ : syracuseStep 261215 = 391823) B391823
theorem B261243 : Blo 259821 261243 := bstep (se 1 (by rfl) ⟨195932, by rfl⟩ : syracuseStep 261243 = 391865) B391865
theorem B392315 : Blo 259821 392315 := bstep (se 1 (by rfl) ⟨294236, by rfl⟩ : syracuseStep 392315 = 588473) B588473
theorem B261295 : Blo 259821 261295 := bstep (se 1 (by rfl) ⟨195971, by rfl⟩ : syracuseStep 261295 = 391943) B391943
theorem B261319 : Blo 259821 261319 := bstep (se 1 (by rfl) ⟨195989, by rfl⟩ : syracuseStep 261319 = 391979) B391979
theorem B261339 : Blo 259821 261339 := bstep (se 1 (by rfl) ⟨196004, by rfl⟩ : syracuseStep 261339 = 392009) B392009
theorem B392441 : Blo 259821 392441 := bstep (se 2 (by rfl) ⟨147165, by rfl⟩ : syracuseStep 392441 = 294331) B294331
theorem B883979 : Blo 259821 883979 := bstep (se 1 (by rfl) ⟨662984, by rfl⟩ : syracuseStep 883979 = 1325969) B1325969
theorem B261415 : Blo 259821 261415 := bstep (se 1 (by rfl) ⟨196061, by rfl⟩ : syracuseStep 261415 = 392123) B392123
theorem B261455 : Blo 259821 261455 := bstep (se 1 (by rfl) ⟨196091, by rfl⟩ : syracuseStep 261455 = 392183) B392183
theorem B261471 : Blo 259821 261471 := bstep (se 1 (by rfl) ⟨196103, by rfl⟩ : syracuseStep 261471 = 392207) B392207
theorem B392543 : Blo 259821 392543 := bstep (se 1 (by rfl) ⟨294407, by rfl⟩ : syracuseStep 392543 = 588815) B588815
theorem B392555 : Blo 259821 392555 := bstep (se 1 (by rfl) ⟨294416, by rfl⟩ : syracuseStep 392555 = 588833) B588833
theorem B261499 : Blo 259821 261499 := bstep (se 1 (by rfl) ⟨196124, by rfl⟩ : syracuseStep 261499 = 392249) B392249
theorem B261551 : Blo 259821 261551 := bstep (se 1 (by rfl) ⟨196163, by rfl⟩ : syracuseStep 261551 = 392327) B392327
theorem B1899949 : Blo 259821 1899949 := bstep (se 3 (by rfl) ⟨356240, by rfl⟩ : syracuseStep 1899949 = 712481) B712481
theorem B261575 : Blo 259821 261575 := bstep (se 1 (by rfl) ⟨196181, by rfl⟩ : syracuseStep 261575 = 392363) B392363
theorem B261595 : Blo 259821 261595 := bstep (se 1 (by rfl) ⟨196196, by rfl⟩ : syracuseStep 261595 = 392393) B392393
theorem B884249 : Blo 259821 884249 := bstep (se 2 (by rfl) ⟨331593, by rfl⟩ : syracuseStep 884249 = 663187) B663187
theorem B2817575 : Blo 259821 2817575 := bstep (se 1 (by rfl) ⟨2113181, by rfl⟩ : syracuseStep 2817575 = 4226363) B4226363
theorem B261671 : Blo 259821 261671 := bstep (se 1 (by rfl) ⟨196253, by rfl⟩ : syracuseStep 261671 = 392507) B392507
theorem B294439 : Blo 259821 294439 := bstep (se 1 (by rfl) ⟨220829, by rfl⟩ : syracuseStep 294439 = 441659) B441659
theorem B261711 : Blo 259821 261711 := bstep (se 1 (by rfl) ⟨196283, by rfl⟩ : syracuseStep 261711 = 392567) B392567
theorem B392783 : Blo 259821 392783 := bstep (se 1 (by rfl) ⟨294587, by rfl⟩ : syracuseStep 392783 = 589175) B589175
theorem B261727 : Blo 259821 261727 := bstep (se 1 (by rfl) ⟨196295, by rfl⟩ : syracuseStep 261727 = 392591) B392591
theorem B589409 : Blo 259821 589409 := bstep (se 2 (by rfl) ⟨221028, by rfl⟩ : syracuseStep 589409 = 442057) B442057
theorem B261755 : Blo 259821 261755 := bstep (se 1 (by rfl) ⟨196316, by rfl⟩ : syracuseStep 261755 = 392633) B392633
theorem B261807 : Blo 259821 261807 := bstep (se 1 (by rfl) ⟨196355, by rfl⟩ : syracuseStep 261807 = 392711) B392711
theorem B261831 : Blo 259821 261831 := bstep (se 1 (by rfl) ⟨196373, by rfl⟩ : syracuseStep 261831 = 392747) B392747
theorem B392903 : Blo 259821 392903 := bstep (se 1 (by rfl) ⟨294677, by rfl⟩ : syracuseStep 392903 = 589355) B589355
theorem B261851 : Blo 259821 261851 := bstep (se 1 (by rfl) ⟨196388, by rfl⟩ : syracuseStep 261851 = 392777) B392777
theorem B261927 : Blo 259821 261927 := bstep (se 1 (by rfl) ⟨196445, by rfl⟩ : syracuseStep 261927 = 392891) B392891
theorem B261967 : Blo 259821 261967 := bstep (se 1 (by rfl) ⟨196475, by rfl⟩ : syracuseStep 261967 = 392951) B392951
theorem B261983 : Blo 259821 261983 := bstep (se 1 (by rfl) ⟨196487, by rfl⟩ : syracuseStep 261983 = 392975) B392975
theorem B393065 : Blo 259821 393065 := bstep (se 2 (by rfl) ⟨147399, by rfl⟩ : syracuseStep 393065 = 294799) B294799
theorem B262011 : Blo 259821 262011 := bstep (se 1 (by rfl) ⟨196508, by rfl⟩ : syracuseStep 262011 = 393017) B393017
theorem B262063 : Blo 259821 262063 := bstep (se 1 (by rfl) ⟨196547, by rfl⟩ : syracuseStep 262063 = 393095) B393095
theorem B393143 : Blo 259821 393143 := bstep (se 1 (by rfl) ⟨294857, by rfl⟩ : syracuseStep 393143 = 589715) B589715
theorem B589751 : Blo 259821 589751 := bstep (se 1 (by rfl) ⟨442313, by rfl⟩ : syracuseStep 589751 = 884627) B884627
theorem B262087 : Blo 259821 262087 := bstep (se 1 (by rfl) ⟨196565, by rfl⟩ : syracuseStep 262087 = 393131) B393131
theorem B262107 : Blo 259821 262107 := bstep (se 1 (by rfl) ⟨196580, by rfl⟩ : syracuseStep 262107 = 393161) B393161
theorem B393179 : Blo 259821 393179 := bstep (se 1 (by rfl) ⟨294884, by rfl⟩ : syracuseStep 393179 = 589769) B589769
theorem B262431 : Blo 259821 262431 := bstep (se 1 (by rfl) ⟨196823, by rfl⟩ : syracuseStep 262431 = 393647) B393647
theorem B393563 : Blo 259821 393563 := bstep (se 1 (by rfl) ⟨295172, by rfl⟩ : syracuseStep 393563 = 590345) B590345
theorem B262491 : Blo 259821 262491 := bstep (se 1 (by rfl) ⟨196868, by rfl⟩ : syracuseStep 262491 = 393737) B393737
theorem B262511 : Blo 259821 262511 := bstep (se 1 (by rfl) ⟨196883, by rfl⟩ : syracuseStep 262511 = 393767) B393767
theorem B262567 : Blo 259821 262567 := bstep (se 1 (by rfl) ⟨196925, by rfl⟩ : syracuseStep 262567 = 393851) B393851
theorem B885167 : Blo 259821 885167 := bstep (se 1 (by rfl) ⟨663875, by rfl⟩ : syracuseStep 885167 = 1327751) B1327751
theorem B590255 : Blo 259821 590255 := bstep (se 1 (by rfl) ⟨442691, by rfl⟩ : syracuseStep 590255 = 885383) B885383
theorem B590291 : Blo 259821 590291 := bstep (se 1 (by rfl) ⟨442718, by rfl⟩ : syracuseStep 590291 = 885437) B885437
theorem B16417241 : Blo 259821 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B262651 : Blo 259821 262651 := bstep (se 1 (by rfl) ⟨196988, by rfl⟩ : syracuseStep 262651 = 393977) B393977
theorem B590399 : Blo 259821 590399 := bstep (se 1 (by rfl) ⟨442799, by rfl⟩ : syracuseStep 590399 = 885599) B885599
theorem B393791 : Blo 259821 393791 := bstep (se 1 (by rfl) ⟨295343, by rfl⟩ : syracuseStep 393791 = 590687) B590687
theorem B262719 : Blo 259821 262719 := bstep (se 1 (by rfl) ⟨197039, by rfl⟩ : syracuseStep 262719 = 394079) B394079
theorem B262727 : Blo 259821 262727 := bstep (se 1 (by rfl) ⟨197045, by rfl⟩ : syracuseStep 262727 = 394091) B394091
theorem B295519 : Blo 259821 295519 := bstep (se 1 (by rfl) ⟨221639, by rfl⟩ : syracuseStep 295519 = 443279) B443279
theorem B590507 : Blo 259821 590507 := bstep (se 1 (by rfl) ⟨442880, by rfl⟩ : syracuseStep 590507 = 885761) B885761
theorem B4981421 : Blo 259821 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B1409719 : Blo 259821 1409719 := bstep (se 1 (by rfl) ⟨1057289, by rfl⟩ : syracuseStep 1409719 = 2114579) B2114579
theorem B393911 : Blo 259821 393911 := bstep (se 1 (by rfl) ⟨295433, by rfl⟩ : syracuseStep 393911 = 590867) B590867
theorem B1114823 : Blo 259821 1114823 := bstep (se 1 (by rfl) ⟨836117, by rfl⟩ : syracuseStep 1114823 = 1672235) B1672235
theorem B262879 : Blo 259821 262879 := bstep (se 1 (by rfl) ⟨197159, by rfl⟩ : syracuseStep 262879 = 394319) B394319
theorem B262959 : Blo 259821 262959 := bstep (se 1 (by rfl) ⟨197219, by rfl⟩ : syracuseStep 262959 = 394439) B394439
theorem B2818961 : Blo 259821 2818961 := bstep (se 2 (by rfl) ⟨1057110, by rfl⟩ : syracuseStep 2818961 = 2114221) B2114221
theorem B394139 : Blo 259821 394139 := bstep (se 1 (by rfl) ⟨295604, by rfl⟩ : syracuseStep 394139 = 591209) B591209
theorem B263067 : Blo 259821 263067 := bstep (se 1 (by rfl) ⟨197300, by rfl⟩ : syracuseStep 263067 = 394601) B394601
theorem B263119 : Blo 259821 263119 := bstep (se 1 (by rfl) ⟨197339, by rfl⟩ : syracuseStep 263119 = 394679) B394679
theorem B2884571 : Blo 259821 2884571 := bstep (se 1 (by rfl) ⟨2163428, by rfl⟩ : syracuseStep 2884571 = 4326857) B4326857
theorem B263143 : Blo 259821 263143 := bstep (se 1 (by rfl) ⟨197357, by rfl⟩ : syracuseStep 263143 = 394715) B394715
theorem B2229443 : Blo 259821 2229443 := bstep (se 1 (by rfl) ⟨1672082, by rfl⟩ : syracuseStep 2229443 = 3344165) B3344165
theorem B591047 : Blo 259821 591047 := bstep (se 1 (by rfl) ⟨443285, by rfl⟩ : syracuseStep 591047 = 886571) B886571
theorem B263455 : Blo 259821 263455 := bstep (se 1 (by rfl) ⟨197591, by rfl⟩ : syracuseStep 263455 = 395183) B395183
theorem B394535 : Blo 259821 394535 := bstep (se 1 (by rfl) ⟨295901, by rfl⟩ : syracuseStep 394535 = 591803) B591803
theorem B263515 : Blo 259821 263515 := bstep (se 1 (by rfl) ⟨197636, by rfl⟩ : syracuseStep 263515 = 395273) B395273
theorem B263535 : Blo 259821 263535 := bstep (se 1 (by rfl) ⟨197651, by rfl⟩ : syracuseStep 263535 = 395303) B395303
theorem B886139 : Blo 259821 886139 := bstep (se 1 (by rfl) ⟨664604, by rfl⟩ : syracuseStep 886139 = 1329209) B1329209
theorem B591227 : Blo 259821 591227 := bstep (se 1 (by rfl) ⟨443420, by rfl⟩ : syracuseStep 591227 = 886841) B886841
theorem B394619 : Blo 259821 394619 := bstep (se 1 (by rfl) ⟨295964, by rfl⟩ : syracuseStep 394619 = 591929) B591929
theorem B263591 : Blo 259821 263591 := bstep (se 1 (by rfl) ⟨197693, by rfl⟩ : syracuseStep 263591 = 395387) B395387
theorem B591353 : Blo 259821 591353 := bstep (se 2 (by rfl) ⟨221757, by rfl⟩ : syracuseStep 591353 = 443515) B443515
theorem B394745 : Blo 259821 394745 := bstep (se 2 (by rfl) ⟨148029, by rfl⟩ : syracuseStep 394745 = 296059) B296059
theorem B263675 : Blo 259821 263675 := bstep (se 1 (by rfl) ⟨197756, by rfl⟩ : syracuseStep 263675 = 395513) B395513
theorem B263743 : Blo 259821 263743 := bstep (se 1 (by rfl) ⟨197807, by rfl⟩ : syracuseStep 263743 = 395615) B395615
theorem B263751 : Blo 259821 263751 := bstep (se 1 (by rfl) ⟨197813, by rfl⟩ : syracuseStep 263751 = 395627) B395627
theorem B591443 : Blo 259821 591443 := bstep (se 1 (by rfl) ⟨443582, by rfl⟩ : syracuseStep 591443 = 887165) B887165
theorem B394847 : Blo 259821 394847 := bstep (se 1 (by rfl) ⟨296135, by rfl⟩ : syracuseStep 394847 = 592271) B592271
theorem B296671 : Blo 259821 296671 := bstep (se 1 (by rfl) ⟨222503, by rfl⟩ : syracuseStep 296671 = 445007) B445007
theorem B591623 : Blo 259821 591623 := bstep (se 1 (by rfl) ⟨443717, by rfl⟩ : syracuseStep 591623 = 887435) B887435
theorem B395063 : Blo 259821 395063 := bstep (se 1 (by rfl) ⟨296297, by rfl⟩ : syracuseStep 395063 = 592595) B592595
theorem B395369 : Blo 259821 395369 := bstep (se 2 (by rfl) ⟨148263, by rfl⟩ : syracuseStep 395369 = 296527) B296527
theorem B592235 : Blo 259821 592235 := bstep (se 1 (by rfl) ⟨444176, by rfl⟩ : syracuseStep 592235 = 888353) B888353
theorem B330095 : Blo 259821 330095 := bstep (se 1 (by rfl) ⟨247571, by rfl⟩ : syracuseStep 330095 = 495143) B495143
theorem B330151 : Blo 259821 330151 := bstep (se 1 (by rfl) ⟨247613, by rfl⟩ : syracuseStep 330151 = 495227) B495227
theorem B2165159 : Blo 259821 2165159 := bstep (se 1 (by rfl) ⟨1623869, by rfl⟩ : syracuseStep 2165159 = 3247739) B3247739
theorem B395687 : Blo 259821 395687 := bstep (se 1 (by rfl) ⟨296765, by rfl⟩ : syracuseStep 395687 = 593531) B593531
theorem B592379 : Blo 259821 592379 := bstep (se 1 (by rfl) ⟨444284, by rfl⟩ : syracuseStep 592379 = 888569) B888569
theorem B657983 : Blo 259821 657983 := bstep (se 1 (by rfl) ⟨493487, by rfl⟩ : syracuseStep 657983 = 986975) B986975
theorem B494201 : Blo 259821 494201 := bstep (se 2 (by rfl) ⟨185325, by rfl⟩ : syracuseStep 494201 = 370651) B370651
theorem B592505 : Blo 259821 592505 := bstep (se 2 (by rfl) ⟨222189, by rfl⟩ : syracuseStep 592505 = 444379) B444379
theorem B494255 : Blo 259821 494255 := bstep (se 1 (by rfl) ⟨370691, by rfl⟩ : syracuseStep 494255 = 741383) B741383
theorem B592559 : Blo 259821 592559 := bstep (se 1 (by rfl) ⟨444419, by rfl⟩ : syracuseStep 592559 = 888839) B888839
theorem B330475 : Blo 259821 330475 := bstep (se 1 (by rfl) ⟨247856, by rfl⟩ : syracuseStep 330475 = 495713) B495713
theorem B887543 : Blo 259821 887543 := bstep (se 1 (by rfl) ⟨665657, by rfl⟩ : syracuseStep 887543 = 1331315) B1331315
theorem B592631 : Blo 259821 592631 := bstep (se 1 (by rfl) ⟨444473, by rfl⟩ : syracuseStep 592631 = 888947) B888947
theorem B560027 : Blo 259821 560027 := bstep (se 1 (by rfl) ⟨420020, by rfl⟩ : syracuseStep 560027 = 840041) B840041
theorem B592811 : Blo 259821 592811 := bstep (se 1 (by rfl) ⟨444608, by rfl⟩ : syracuseStep 592811 = 889217) B889217
theorem B658631 : Blo 259821 658631 := bstep (se 1 (by rfl) ⟨493973, by rfl⟩ : syracuseStep 658631 = 987947) B987947
theorem B658651 : Blo 259821 658651 := bstep (se 1 (by rfl) ⟨493988, by rfl⟩ : syracuseStep 658651 = 987977) B987977
theorem B298279 : Blo 259821 298279 := bstep (se 1 (by rfl) ⟨223709, by rfl⟩ : syracuseStep 298279 = 447419) B447419
theorem B4787585 : Blo 259821 4787585 := bstep (se 2 (by rfl) ⟨1795344, by rfl⟩ : syracuseStep 4787585 = 3590689) B3590689
theorem B1674695 : Blo 259821 1674695 := bstep (se 1 (by rfl) ⟨1256021, by rfl⟩ : syracuseStep 1674695 = 2512043) B2512043
theorem B593351 : Blo 259821 593351 := bstep (se 1 (by rfl) ⟨445013, by rfl⟩ : syracuseStep 593351 = 890027) B890027
theorem B331447 : Blo 259821 331447 := bstep (se 1 (by rfl) ⟨248585, by rfl⟩ : syracuseStep 331447 = 497171) B497171
theorem B626473 : Blo 259821 626473 := bstep (se 2 (by rfl) ⟨234927, by rfl⟩ : syracuseStep 626473 = 469855) B469855
theorem B2232107 : Blo 259821 2232107 := bstep (se 1 (by rfl) ⟨1674080, by rfl⟩ : syracuseStep 2232107 = 3348161) B3348161
theorem B888623 : Blo 259821 888623 := bstep (se 1 (by rfl) ⟨666467, by rfl⟩ : syracuseStep 888623 = 1332935) B1332935
theorem B1249181 : Blo 259821 1249181 := bstep (se 3 (by rfl) ⟨234221, by rfl⟩ : syracuseStep 1249181 = 468443) B468443
theorem B1413179 : Blo 259821 1413179 := bstep (se 1 (by rfl) ⟨1059884, by rfl⟩ : syracuseStep 1413179 = 2119769) B2119769
theorem B1249451 : Blo 259821 1249451 := bstep (se 1 (by rfl) ⟨937088, by rfl⟩ : syracuseStep 1249451 = 1874177) B1874177
theorem B659785 : Blo 259821 659785 := bstep (se 2 (by rfl) ⟨247419, by rfl⟩ : syracuseStep 659785 = 494839) B494839
theorem B496039 : Blo 259821 496039 := bstep (se 1 (by rfl) ⟨372029, by rfl⟩ : syracuseStep 496039 = 744059) B744059
theorem B496199 : Blo 259821 496199 := bstep (se 1 (by rfl) ⟨372149, by rfl⟩ : syracuseStep 496199 = 744299) B744299
theorem B660089 : Blo 259821 660089 := bstep (se 2 (by rfl) ⟨247533, by rfl⟩ : syracuseStep 660089 = 495067) B495067
theorem B496631 : Blo 259821 496631 := bstep (se 1 (by rfl) ⟨372473, by rfl⟩ : syracuseStep 496631 = 744947) B744947
theorem B496783 : Blo 259821 496783 := bstep (se 1 (by rfl) ⟨372587, by rfl⟩ : syracuseStep 496783 = 745175) B745175
theorem B791801 : Blo 259821 791801 := bstep (se 2 (by rfl) ⟨296925, by rfl⟩ : syracuseStep 791801 = 593851) B593851
theorem B1480031 : Blo 259821 1480031 := bstep (se 1 (by rfl) ⟨1110023, by rfl⟩ : syracuseStep 1480031 = 2220047) B2220047
theorem B562555 : Blo 259821 562555 := bstep (se 1 (by rfl) ⟨421916, by rfl⟩ : syracuseStep 562555 = 843833) B843833
theorem B2528651 : Blo 259821 2528651 := bstep (se 1 (by rfl) ⟨1896488, by rfl⟩ : syracuseStep 2528651 = 3792977) B3792977
theorem B2168257 : Blo 259821 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B1250873 : Blo 259821 1250873 := bstep (se 2 (by rfl) ⟨469077, by rfl⟩ : syracuseStep 1250873 = 938155) B938155
theorem B628319 : Blo 259821 628319 := bstep (se 1 (by rfl) ⟨471239, by rfl⟩ : syracuseStep 628319 = 942479) B942479
theorem B333487 : Blo 259821 333487 := bstep (se 1 (by rfl) ⟨250115, by rfl⟩ : syracuseStep 333487 = 500231) B500231
theorem B1251101 : Blo 259821 1251101 := bstep (se 3 (by rfl) ⟨234581, by rfl⟩ : syracuseStep 1251101 = 469163) B469163
theorem B1316897 : Blo 259821 1316897 := bstep (se 2 (by rfl) ⟨493836, by rfl⟩ : syracuseStep 1316897 = 987673) B987673
theorem B1022081 : Blo 259821 1022081 := bstep (se 2 (by rfl) ⟨383280, by rfl⟩ : syracuseStep 1022081 = 766561) B766561
theorem B1317059 : Blo 259821 1317059 := bstep (se 1 (by rfl) ⟨987794, by rfl⟩ : syracuseStep 1317059 = 1975589) B1975589
theorem B661871 : Blo 259821 661871 := bstep (se 1 (by rfl) ⟨496403, by rfl⟩ : syracuseStep 661871 = 992807) B992807
theorem B629203 : Blo 259821 629203 := bstep (se 1 (by rfl) ⟨471902, by rfl⟩ : syracuseStep 629203 = 943805) B943805
theorem B989891 : Blo 259821 989891 := bstep (se 1 (by rfl) ⟨742418, by rfl⟩ : syracuseStep 989891 = 1484837) B1484837
theorem B3349187 : Blo 259821 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B760747 : Blo 259821 760747 := bstep (se 1 (by rfl) ⟨570560, by rfl⟩ : syracuseStep 760747 = 1141121) B1141121
theorem B662519 : Blo 259821 662519 := bstep (se 1 (by rfl) ⟨496889, by rfl⟩ : syracuseStep 662519 = 993779) B993779
theorem B662651 : Blo 259821 662651 := bstep (se 1 (by rfl) ⟨496988, by rfl⟩ : syracuseStep 662651 = 993977) B993977
theorem B7118405 : Blo 259821 7118405 := bstep (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) B1334701
theorem B958061 : Blo 259821 958061 := bstep (se 3 (by rfl) ⟨179636, by rfl⟩ : syracuseStep 958061 = 359273) B359273
theorem B630433 : Blo 259821 630433 := bstep (se 2 (by rfl) ⟨236412, by rfl⟩ : syracuseStep 630433 = 472825) B472825
theorem B4562747 : Blo 259821 4562747 := bstep (se 1 (by rfl) ⟨3422060, by rfl⟩ : syracuseStep 4562747 = 6844121) B6844121
theorem B991561 : Blo 259821 991561 := bstep (se 2 (by rfl) ⟨371835, by rfl⟩ : syracuseStep 991561 = 743671) B743671
theorem B1941851 : Blo 259821 1941851 := bstep (se 1 (by rfl) ⟨1456388, by rfl⟩ : syracuseStep 1941851 = 2912777) B2912777
theorem B991865 : Blo 259821 991865 := bstep (se 2 (by rfl) ⟨371949, by rfl⟩ : syracuseStep 991865 = 743899) B743899
theorem B631471 : Blo 259821 631471 := bstep (se 1 (by rfl) ⟨473603, by rfl⟩ : syracuseStep 631471 = 947207) B947207
theorem B2433887 : Blo 259821 2433887 := bstep (se 1 (by rfl) ⟨1825415, by rfl⟩ : syracuseStep 2433887 = 3650831) B3650831
theorem B664463 : Blo 259821 664463 := bstep (se 1 (by rfl) ⟨498347, by rfl⟩ : syracuseStep 664463 = 996695) B996695
theorem B1123571 : Blo 259821 1123571 := bstep (se 1 (by rfl) ⟨842678, by rfl⟩ : syracuseStep 1123571 = 1685357) B1685357
theorem B664969 : Blo 259821 664969 := bstep (se 2 (by rfl) ⟨249363, by rfl⟩ : syracuseStep 664969 = 498727) B498727
theorem B632279 : Blo 259821 632279 := bstep (se 1 (by rfl) ⟨474209, by rfl⟩ : syracuseStep 632279 = 948419) B948419
theorem B665081 : Blo 259821 665081 := bstep (se 2 (by rfl) ⟨249405, by rfl⟩ : syracuseStep 665081 = 498811) B498811
theorem B1582649 : Blo 259821 1582649 := bstep (se 2 (by rfl) ⟨593493, by rfl⟩ : syracuseStep 1582649 = 1186987) B1186987
theorem B2107081 : Blo 259821 2107081 := bstep (se 2 (by rfl) ⟨790155, by rfl⟩ : syracuseStep 2107081 = 1580311) B1580311
theorem B1320785 : Blo 259821 1320785 := bstep (se 2 (by rfl) ⟨495294, by rfl⟩ : syracuseStep 1320785 = 990589) B990589
theorem B117253973 : Blo 259821 117253973 := bstep (se 9 (by rfl) ⟨343517, by rfl⟩ : syracuseStep 117253973 = 687035) B687035
theorem B2533265 : Blo 259821 2533265 := bstep (se 2 (by rfl) ⟨949974, by rfl⟩ : syracuseStep 2533265 = 1899949) B1899949
theorem B665729 : Blo 259821 665729 := bstep (se 2 (by rfl) ⟨249648, by rfl⟩ : syracuseStep 665729 = 499297) B499297
theorem B1878383 : Blo 259821 1878383 := bstep (se 1 (by rfl) ⟨1408787, by rfl⟩ : syracuseStep 1878383 = 2817575) B2817575
theorem B469567 : Blo 259821 469567 := bstep (se 1 (by rfl) ⟨352175, by rfl⟩ : syracuseStep 469567 = 704351) B704351
theorem B6761083 : Blo 259821 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B1321595 : Blo 259821 1321595 := bstep (se 1 (by rfl) ⟨991196, by rfl⟩ : syracuseStep 1321595 = 1982393) B1982393
theorem B797359 : Blo 259821 797359 := bstep (se 1 (by rfl) ⟨598019, by rfl⟩ : syracuseStep 797359 = 1196039) B1196039
theorem B2566903 : Blo 259821 2566903 := bstep (se 1 (by rfl) ⟨1925177, by rfl⟩ : syracuseStep 2566903 = 3850355) B3850355
theorem B666539 : Blo 259821 666539 := bstep (se 1 (by rfl) ⟨499904, by rfl⟩ : syracuseStep 666539 = 999809) B999809
theorem B1485863 : Blo 259821 1485863 := bstep (se 1 (by rfl) ⟨1114397, by rfl⟩ : syracuseStep 1485863 = 2228795) B2228795
theorem B1978019 : Blo 259821 1978019 := bstep (se 1 (by rfl) ⟨1483514, by rfl⟩ : syracuseStep 1978019 = 2967029) B2967029
theorem B3354311 : Blo 259821 3354311 := bstep (se 1 (by rfl) ⟨2515733, by rfl⟩ : syracuseStep 3354311 = 5031467) B5031467
theorem B667399 : Blo 259821 667399 := bstep (se 1 (by rfl) ⟨500549, by rfl⟩ : syracuseStep 667399 = 1001099) B1001099
theorem B667673 : Blo 259821 667673 := bstep (se 2 (by rfl) ⟨250377, by rfl⟩ : syracuseStep 667673 = 500755) B500755
theorem B864361 : Blo 259821 864361 := bstep (se 2 (by rfl) ⟨324135, by rfl⟩ : syracuseStep 864361 = 648271) B648271
theorem B471521 : Blo 259821 471521 := bstep (se 2 (by rfl) ⟨176820, by rfl⟩ : syracuseStep 471521 = 353641) B353641
theorem B373243 : Blo 259821 373243 := bstep (se 1 (by rfl) ⟨279932, by rfl⟩ : syracuseStep 373243 = 559865) B559865
theorem B1323539 : Blo 259821 1323539 := bstep (se 1 (by rfl) ⟨992654, by rfl⟩ : syracuseStep 1323539 = 1985309) B1985309
theorem B438905 : Blo 259821 438905 := bstep (se 2 (by rfl) ⟨164589, by rfl⟩ : syracuseStep 438905 = 329179) B329179
theorem B438959 : Blo 259821 438959 := bstep (se 1 (by rfl) ⟨329219, by rfl⟩ : syracuseStep 438959 = 658439) B658439
theorem B2831071 : Blo 259821 2831071 := bstep (se 1 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 2831071 = 4246607) B4246607
theorem B439195 : Blo 259821 439195 := bstep (se 1 (by rfl) ⟨329396, by rfl⟩ : syracuseStep 439195 = 658793) B658793
theorem B2241917 : Blo 259821 2241917 := bstep (se 3 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 2241917 = 840719) B840719
theorem B407033 : Blo 259821 407033 := bstep (se 2 (by rfl) ⟨152637, by rfl⟩ : syracuseStep 407033 = 305275) B305275
theorem B571115 : Blo 259821 571115 := bstep (se 1 (by rfl) ⟨428336, by rfl⟩ : syracuseStep 571115 = 856673) B856673
theorem B1980449 : Blo 259821 1980449 := bstep (se 2 (by rfl) ⟨742668, by rfl⟩ : syracuseStep 1980449 = 1485337) B1485337
theorem B1325321 : Blo 259821 1325321 := bstep (se 2 (by rfl) ⟨496995, by rfl⟩ : syracuseStep 1325321 = 993991) B993991
theorem B440687 : Blo 259821 440687 := bstep (se 1 (by rfl) ⟨330515, by rfl⟩ : syracuseStep 440687 = 661031) B661031
theorem B440903 : Blo 259821 440903 := bstep (se 1 (by rfl) ⟨330677, by rfl⟩ : syracuseStep 440903 = 661355) B661355
theorem B375367 : Blo 259821 375367 := bstep (se 1 (by rfl) ⟨281525, by rfl⟩ : syracuseStep 375367 = 563051) B563051
theorem B1784695 : Blo 259821 1784695 := bstep (se 1 (by rfl) ⟨1338521, by rfl⟩ : syracuseStep 1784695 = 2677043) B2677043
theorem B441335 : Blo 259821 441335 := bstep (se 1 (by rfl) ⟨331001, by rfl⟩ : syracuseStep 441335 = 662003) B662003
theorem B1326455 : Blo 259821 1326455 := bstep (se 1 (by rfl) ⟨994841, by rfl⟩ : syracuseStep 1326455 = 1989683) B1989683
theorem B1326617 : Blo 259821 1326617 := bstep (se 2 (by rfl) ⟨497481, by rfl⟩ : syracuseStep 1326617 = 994963) B994963
theorem B1916531 : Blo 259821 1916531 := bstep (se 1 (by rfl) ⟨1437398, by rfl⟩ : syracuseStep 1916531 = 2874797) B2874797
theorem B1261291 : Blo 259821 1261291 := bstep (se 1 (by rfl) ⟨945968, by rfl⟩ : syracuseStep 1261291 = 1891937) B1891937
theorem B442091 : Blo 259821 442091 := bstep (se 1 (by rfl) ⟨331568, by rfl⟩ : syracuseStep 442091 = 663137) B663137
theorem B474887 : Blo 259821 474887 := bstep (se 1 (by rfl) ⟨356165, by rfl⟩ : syracuseStep 474887 = 712331) B712331
theorem B835913 : Blo 259821 835913 := bstep (se 2 (by rfl) ⟨313467, by rfl⟩ : syracuseStep 835913 = 626935) B626935
theorem B2244955 : Blo 259821 2244955 := bstep (se 1 (by rfl) ⟨1683716, by rfl⟩ : syracuseStep 2244955 = 3367433) B3367433
theorem B1065593 : Blo 259821 1065593 := bstep (se 2 (by rfl) ⟨399597, by rfl⟩ : syracuseStep 1065593 = 799195) B799195
theorem B443063 : Blo 259821 443063 := bstep (se 1 (by rfl) ⟨332297, by rfl⟩ : syracuseStep 443063 = 664595) B664595
theorem B19776307 : Blo 259821 19776307 := bstep (se 1 (by rfl) ⟨14832230, by rfl⟩ : syracuseStep 19776307 = 29664461) B29664461
theorem B10175291 : Blo 259821 10175291 := bstep (se 1 (by rfl) ⟨7631468, by rfl⟩ : syracuseStep 10175291 = 15262937) B15262937
theorem B1885187 : Blo 259821 1885187 := bstep (se 1 (by rfl) ⟨1413890, by rfl⟩ : syracuseStep 1885187 = 2827781) B2827781
theorem B705779 : Blo 259821 705779 := bstep (se 1 (by rfl) ⟨529334, by rfl⟩ : syracuseStep 705779 = 1058669) B1058669
theorem B279919 : Blo 259821 279919 := bstep (se 1 (by rfl) ⟨209939, by rfl⟩ : syracuseStep 279919 = 419879) B419879
theorem B443785 : Blo 259821 443785 := bstep (se 2 (by rfl) ⟨166419, by rfl⟩ : syracuseStep 443785 = 332839) B332839
theorem B1263289 : Blo 259821 1263289 := bstep (se 2 (by rfl) ⟨473733, by rfl⟩ : syracuseStep 1263289 = 947467) B947467
theorem B444217 : Blo 259821 444217 := bstep (se 2 (by rfl) ⟨166581, by rfl⟩ : syracuseStep 444217 = 333163) B333163
theorem B1984337 : Blo 259821 1984337 := bstep (se 2 (by rfl) ⟨744126, by rfl⟩ : syracuseStep 1984337 = 1488253) B1488253
theorem B1198007 : Blo 259821 1198007 := bstep (se 1 (by rfl) ⟨898505, by rfl⟩ : syracuseStep 1198007 = 1797011) B1797011
theorem B1099727 : Blo 259821 1099727 := bstep (se 1 (by rfl) ⟨824795, by rfl⟩ : syracuseStep 1099727 = 1649591) B1649591
theorem B444521 : Blo 259821 444521 := bstep (se 2 (by rfl) ⟨166695, by rfl⟩ : syracuseStep 444521 = 333391) B333391
theorem B1329533 : Blo 259821 1329533 := bstep (se 3 (by rfl) ⟨249287, by rfl⟩ : syracuseStep 1329533 = 498575) B498575
theorem B2673107 : Blo 259821 2673107 := bstep (se 1 (by rfl) ⟨2004830, by rfl⟩ : syracuseStep 2673107 = 4009661) B4009661
theorem B281551 : Blo 259821 281551 := bstep (se 1 (by rfl) ⟨211163, by rfl⟩ : syracuseStep 281551 = 422327) B422327
theorem B25873843 : Blo 259821 25873843 := bstep (se 1 (by rfl) ⟨19405382, by rfl⟩ : syracuseStep 25873843 = 38810765) B38810765
theorem B446215 : Blo 259821 446215 := bstep (se 1 (by rfl) ⟨334661, by rfl⟩ : syracuseStep 446215 = 669323) B669323
theorem B1330991 : Blo 259821 1330991 := bstep (se 1 (by rfl) ⟨998243, by rfl⟩ : syracuseStep 1330991 = 1996487) B1996487
theorem B2510813 : Blo 259821 2510813 := bstep (se 3 (by rfl) ⟨470777, by rfl⟩ : syracuseStep 2510813 = 941555) B941555
theorem B446831 : Blo 259821 446831 := bstep (se 1 (by rfl) ⟨335123, by rfl⟩ : syracuseStep 446831 = 670247) B670247
theorem B5067143 : Blo 259821 5067143 := bstep (se 1 (by rfl) ⟨3800357, by rfl⟩ : syracuseStep 5067143 = 7600715) B7600715
theorem B315847 : Blo 259821 315847 := bstep (se 1 (by rfl) ⟨236885, by rfl⟩ : syracuseStep 315847 = 473771) B473771
theorem B840527 : Blo 259821 840527 := bstep (se 1 (by rfl) ⟨630395, by rfl⟩ : syracuseStep 840527 = 1260791) B1260791
theorem B841373 : Blo 259821 841373 := bstep (se 3 (by rfl) ⟨157757, by rfl⟩ : syracuseStep 841373 = 315515) B315515
theorem B1333097 : Blo 259821 1333097 := bstep (se 2 (by rfl) ⟨499911, by rfl⟩ : syracuseStep 1333097 = 999823) B999823
theorem B645385 : Blo 259821 645385 := bstep (se 2 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 645385 = 484039) B484039
theorem B1497527 : Blo 259821 1497527 := bstep (se 1 (by rfl) ⟨1123145, by rfl⟩ : syracuseStep 1497527 = 2246291) B2246291
theorem B1498277 : Blo 259821 1498277 := bstep (se 4 (by rfl) ⟨140463, by rfl⟩ : syracuseStep 1498277 = 280927) B280927
theorem B1990169 : Blo 259821 1990169 := bstep (se 2 (by rfl) ⟨746313, by rfl⟩ : syracuseStep 1990169 = 1492627) B1492627
theorem B1334879 : Blo 259821 1334879 := bstep (se 1 (by rfl) ⟨1001159, by rfl⟩ : syracuseStep 1334879 = 2002319) B2002319
theorem B712655 : Blo 259821 712655 := bstep (se 1 (by rfl) ⟨534491, by rfl⟩ : syracuseStep 712655 = 1068983) B1068983
theorem B352543 : Blo 259821 352543 := bstep (se 1 (by rfl) ⟨264407, by rfl⟩ : syracuseStep 352543 = 528815) B528815
theorem B418367 : Blo 259821 418367 := bstep (se 1 (by rfl) ⟨313775, by rfl⟩ : syracuseStep 418367 = 627551) B627551
theorem B1139321 : Blo 259821 1139321 := bstep (se 2 (by rfl) ⟨427245, by rfl⟩ : syracuseStep 1139321 = 854491) B854491
theorem B877391 : Blo 259821 877391 := bstep (se 1 (by rfl) ⟨658043, by rfl⟩ : syracuseStep 877391 = 1316087) B1316087
theorem B12248113 : Blo 259821 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B877715 : Blo 259821 877715 := bstep (se 1 (by rfl) ⟨658286, by rfl⟩ : syracuseStep 877715 = 1316573) B1316573
theorem B877985 : Blo 259821 877985 := bstep (se 2 (by rfl) ⟨329244, by rfl⟩ : syracuseStep 877985 = 658489) B658489
theorem B746941 : Blo 259821 746941 := bstep (se 3 (by rfl) ⟨140051, by rfl⟩ : syracuseStep 746941 = 280103) B280103
theorem B845959 : Blo 259821 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B10741997 : Blo 259821 10741997 := bstep (se 3 (by rfl) ⟨2014124, by rfl⟩ : syracuseStep 10741997 = 4028249) B4028249
theorem B4778299 : Blo 259821 4778299 := bstep (se 1 (by rfl) ⟨3583724, by rfl⟩ : syracuseStep 4778299 = 7167449) B7167449
theorem B354727 : Blo 259821 354727 := bstep (se 1 (by rfl) ⟨266045, by rfl⟩ : syracuseStep 354727 = 532091) B532091
theorem B12839467 : Blo 259821 12839467 := bstep (se 1 (by rfl) ⟨9629600, by rfl⟩ : syracuseStep 12839467 = 19259201) B19259201
theorem B944887 : Blo 259821 944887 := bstep (se 1 (by rfl) ⟨708665, by rfl⟩ : syracuseStep 944887 = 1417331) B1417331
theorem B584603 : Blo 259821 584603 := bstep (se 1 (by rfl) ⟨438452, by rfl⟩ : syracuseStep 584603 = 876905) B876905
theorem B5663783 : Blo 259821 5663783 := bstep (se 1 (by rfl) ⟨4247837, by rfl⟩ : syracuseStep 5663783 = 8495675) B8495675
theorem B584801 : Blo 259821 584801 := bstep (se 2 (by rfl) ⟨219300, by rfl⟩ : syracuseStep 584801 = 438601) B438601
theorem B584999 : Blo 259821 584999 := bstep (se 1 (by rfl) ⟨438749, by rfl⟩ : syracuseStep 584999 = 877499) B877499
theorem B683615 : Blo 259821 683615 := bstep (se 1 (by rfl) ⟨512711, by rfl⟩ : syracuseStep 683615 = 1025423) B1025423
theorem B585377 : Blo 259821 585377 := bstep (se 2 (by rfl) ⟨219516, by rfl⟩ : syracuseStep 585377 = 439033) B439033
theorem B1994543 : Blo 259821 1994543 := bstep (se 1 (by rfl) ⟨1495907, by rfl⟩ : syracuseStep 1994543 = 2991815) B2991815
theorem B585737 : Blo 259821 585737 := bstep (se 2 (by rfl) ⟨219651, by rfl⟩ : syracuseStep 585737 = 439303) B439303
theorem B2126027 : Blo 259821 2126027 := bstep (se 1 (by rfl) ⟨1594520, by rfl⟩ : syracuseStep 2126027 = 3189041) B3189041
theorem B586151 : Blo 259821 586151 := bstep (se 1 (by rfl) ⟨439613, by rfl⟩ : syracuseStep 586151 = 879227) B879227
theorem B586259 : Blo 259821 586259 := bstep (se 1 (by rfl) ⟨439694, by rfl⟩ : syracuseStep 586259 = 879389) B879389
theorem B881171 : Blo 259821 881171 := bstep (se 1 (by rfl) ⟨660878, by rfl⟩ : syracuseStep 881171 = 1321757) B1321757
theorem B586313 : Blo 259821 586313 := bstep (se 2 (by rfl) ⟨219867, by rfl⟩ : syracuseStep 586313 = 439735) B439735
theorem B389753 : Blo 259821 389753 := bstep (se 2 (by rfl) ⟨146157, by rfl⟩ : syracuseStep 389753 = 292315) B292315
theorem B389807 : Blo 259821 389807 := bstep (se 1 (by rfl) ⟨292355, by rfl⟩ : syracuseStep 389807 = 584711) B584711
theorem B389855 : Blo 259821 389855 := bstep (se 1 (by rfl) ⟨292391, by rfl⟩ : syracuseStep 389855 = 584783) B584783
theorem B390119 : Blo 259821 390119 := bstep (se 1 (by rfl) ⟨292589, by rfl⟩ : syracuseStep 390119 = 585179) B585179
theorem B586727 : Blo 259821 586727 := bstep (se 1 (by rfl) ⟨440045, by rfl⟩ : syracuseStep 586727 = 880091) B880091
theorem B390377 : Blo 259821 390377 := bstep (se 2 (by rfl) ⟨146391, by rfl⟩ : syracuseStep 390377 = 292783) B292783
theorem B390431 : Blo 259821 390431 := bstep (se 1 (by rfl) ⟨292823, by rfl⟩ : syracuseStep 390431 = 585647) B585647
theorem B947495 : Blo 259821 947495 := bstep (se 1 (by rfl) ⟨710621, by rfl⟩ : syracuseStep 947495 = 1421243) B1421243
theorem B1111391 : Blo 259821 1111391 := bstep (se 1 (by rfl) ⟨833543, by rfl⟩ : syracuseStep 1111391 = 1667087) B1667087
theorem B587105 : Blo 259821 587105 := bstep (se 2 (by rfl) ⟨220164, by rfl⟩ : syracuseStep 587105 = 440329) B440329
theorem B587195 : Blo 259821 587195 := bstep (se 1 (by rfl) ⟨440396, by rfl⟩ : syracuseStep 587195 = 880793) B880793
theorem B1668545 : Blo 259821 1668545 := bstep (se 2 (by rfl) ⟨625704, by rfl⟩ : syracuseStep 1668545 = 1251409) B1251409
theorem B2848193 : Blo 259821 2848193 := bstep (se 2 (by rfl) ⟨1068072, by rfl⟩ : syracuseStep 2848193 = 2136145) B2136145
theorem B390599 : Blo 259821 390599 := bstep (se 1 (by rfl) ⟨292949, by rfl⟩ : syracuseStep 390599 = 585899) B585899
theorem B1013255 : Blo 259821 1013255 := bstep (se 1 (by rfl) ⟨759941, by rfl⟩ : syracuseStep 1013255 = 1519883) B1519883
theorem B587321 : Blo 259821 587321 := bstep (se 2 (by rfl) ⟨220245, by rfl⟩ : syracuseStep 587321 = 440491) B440491
theorem B292423 : Blo 259821 292423 := bstep (se 1 (by rfl) ⟨219317, by rfl⟩ : syracuseStep 292423 = 438635) B438635
theorem B390953 : Blo 259821 390953 := bstep (se 2 (by rfl) ⟨146607, by rfl⟩ : syracuseStep 390953 = 293215) B293215
theorem B259887 : Blo 259821 259887 := bstep (se 1 (by rfl) ⟨194915, by rfl⟩ : syracuseStep 259887 = 389831) B389831
theorem B390959 : Blo 259821 390959 := bstep (se 1 (by rfl) ⟨293219, by rfl⟩ : syracuseStep 390959 = 586439) B586439
theorem B259995 : Blo 259821 259995 := bstep (se 1 (by rfl) ⟨194996, by rfl⟩ : syracuseStep 259995 = 389993) B389993
theorem B260047 : Blo 259821 260047 := bstep (se 1 (by rfl) ⟨195035, by rfl⟩ : syracuseStep 260047 = 390071) B390071
theorem B260071 : Blo 259821 260071 := bstep (se 1 (by rfl) ⟨195053, by rfl⟩ : syracuseStep 260071 = 390107) B390107
theorem B587987 : Blo 259821 587987 := bstep (se 1 (by rfl) ⟨440990, by rfl⟩ : syracuseStep 587987 = 881981) B881981
theorem B391433 : Blo 259821 391433 := bstep (se 2 (by rfl) ⟨146787, by rfl⟩ : syracuseStep 391433 = 293575) B293575
theorem B588041 : Blo 259821 588041 := bstep (se 2 (by rfl) ⟨220515, by rfl⟩ : syracuseStep 588041 = 441031) B441031
theorem B882953 : Blo 259821 882953 := bstep (se 2 (by rfl) ⟨331107, by rfl⟩ : syracuseStep 882953 = 662215) B662215
theorem B260383 : Blo 259821 260383 := bstep (se 1 (by rfl) ⟨195287, by rfl⟩ : syracuseStep 260383 = 390575) B390575
theorem B260443 : Blo 259821 260443 := bstep (se 1 (by rfl) ⟨195332, by rfl⟩ : syracuseStep 260443 = 390665) B390665
theorem B260463 : Blo 259821 260463 := bstep (se 1 (by rfl) ⟨195347, by rfl⟩ : syracuseStep 260463 = 390695) B390695
theorem B391535 : Blo 259821 391535 := bstep (se 1 (by rfl) ⟨293651, by rfl⟩ : syracuseStep 391535 = 587303) B587303
theorem B260519 : Blo 259821 260519 := bstep (se 1 (by rfl) ⟨195389, by rfl⟩ : syracuseStep 260519 = 390779) B390779
theorem B293287 : Blo 259821 293287 := bstep (se 1 (by rfl) ⟨219965, by rfl⟩ : syracuseStep 293287 = 439931) B439931
theorem B588257 : Blo 259821 588257 := bstep (se 2 (by rfl) ⟨220596, by rfl⟩ : syracuseStep 588257 = 441193) B441193
theorem B260603 : Blo 259821 260603 := bstep (se 1 (by rfl) ⟨195452, by rfl⟩ : syracuseStep 260603 = 390905) B390905
theorem B3832343 : Blo 259821 3832343 := bstep (se 1 (by rfl) ⟨2874257, by rfl⟩ : syracuseStep 3832343 = 5748515) B5748515
theorem B1735231 : Blo 259821 1735231 := bstep (se 1 (by rfl) ⟨1301423, by rfl⟩ : syracuseStep 1735231 = 2602847) B2602847
theorem B260671 : Blo 259821 260671 := bstep (se 1 (by rfl) ⟨195503, by rfl⟩ : syracuseStep 260671 = 391007) B391007
theorem B260679 : Blo 259821 260679 := bstep (se 1 (by rfl) ⟨195509, by rfl⟩ : syracuseStep 260679 = 391019) B391019
theorem B391751 : Blo 259821 391751 := bstep (se 1 (by rfl) ⟨293813, by rfl⟩ : syracuseStep 391751 = 587627) B587627
theorem B948809 : Blo 259821 948809 := bstep (se 2 (by rfl) ⟨355803, by rfl⟩ : syracuseStep 948809 = 711607) B711607
theorem B391787 : Blo 259821 391787 := bstep (se 1 (by rfl) ⟨293840, by rfl⟩ : syracuseStep 391787 = 587681) B587681
theorem B260831 : Blo 259821 260831 := bstep (se 1 (by rfl) ⟨195623, by rfl⟩ : syracuseStep 260831 = 391247) B391247
theorem B588563 : Blo 259821 588563 := bstep (se 1 (by rfl) ⟨441422, by rfl⟩ : syracuseStep 588563 = 882845) B882845
theorem B260911 : Blo 259821 260911 := bstep (se 1 (by rfl) ⟨195683, by rfl⟩ : syracuseStep 260911 = 391367) B391367
theorem B392015 : Blo 259821 392015 := bstep (se 1 (by rfl) ⟨294011, by rfl⟩ : syracuseStep 392015 = 588023) B588023
theorem B261019 : Blo 259821 261019 := bstep (se 1 (by rfl) ⟨195764, by rfl⟩ : syracuseStep 261019 = 391529) B391529
theorem B261071 : Blo 259821 261071 := bstep (se 1 (by rfl) ⟨195803, by rfl⟩ : syracuseStep 261071 = 391607) B391607
theorem B261095 : Blo 259821 261095 := bstep (se 1 (by rfl) ⟨195821, by rfl⟩ : syracuseStep 261095 = 391643) B391643
theorem B293863 : Blo 259821 293863 := bstep (se 1 (by rfl) ⟨220397, by rfl⟩ : syracuseStep 293863 = 440795) B440795
theorem B588923 : Blo 259821 588923 := bstep (se 1 (by rfl) ⟨441692, by rfl⟩ : syracuseStep 588923 = 883385) B883385
theorem B392411 : Blo 259821 392411 := bstep (se 1 (by rfl) ⟨294308, by rfl⟩ : syracuseStep 392411 = 588617) B588617
theorem B589049 : Blo 259821 589049 := bstep (se 2 (by rfl) ⟨220893, by rfl⟩ : syracuseStep 589049 = 441787) B441787
theorem B261407 : Blo 259821 261407 := bstep (se 1 (by rfl) ⟨196055, by rfl⟩ : syracuseStep 261407 = 392111) B392111
theorem B261467 : Blo 259821 261467 := bstep (se 1 (by rfl) ⟨196100, by rfl⟩ : syracuseStep 261467 = 392201) B392201
theorem B621919 : Blo 259821 621919 := bstep (se 1 (by rfl) ⟨466439, by rfl⟩ : syracuseStep 621919 = 932879) B932879
theorem B261487 : Blo 259821 261487 := bstep (se 1 (by rfl) ⟨196115, by rfl⟩ : syracuseStep 261487 = 392231) B392231
theorem B884087 : Blo 259821 884087 := bstep (se 1 (by rfl) ⟨663065, by rfl⟩ : syracuseStep 884087 = 1326131) B1326131
theorem B392585 : Blo 259821 392585 := bstep (se 2 (by rfl) ⟨147219, by rfl⟩ : syracuseStep 392585 = 294439) B294439
theorem B589193 : Blo 259821 589193 := bstep (se 2 (by rfl) ⟨220947, by rfl⟩ : syracuseStep 589193 = 441895) B441895
theorem B261543 : Blo 259821 261543 := bstep (se 1 (by rfl) ⟨196157, by rfl⟩ : syracuseStep 261543 = 392315) B392315
theorem B261627 : Blo 259821 261627 := bstep (se 1 (by rfl) ⟨196220, by rfl⟩ : syracuseStep 261627 = 392441) B392441
theorem B589319 : Blo 259821 589319 := bstep (se 1 (by rfl) ⟨441989, by rfl⟩ : syracuseStep 589319 = 883979) B883979
theorem B261695 : Blo 259821 261695 := bstep (se 1 (by rfl) ⟨196271, by rfl⟩ : syracuseStep 261695 = 392543) B392543
theorem B261703 : Blo 259821 261703 := bstep (se 1 (by rfl) ⟨196277, by rfl⟩ : syracuseStep 261703 = 392555) B392555
theorem B1998431 : Blo 259821 1998431 := bstep (se 1 (by rfl) ⟨1498823, by rfl⟩ : syracuseStep 1998431 = 2997647) B2997647
theorem B589499 : Blo 259821 589499 := bstep (se 1 (by rfl) ⟨442124, by rfl⟩ : syracuseStep 589499 = 884249) B884249
theorem B261855 : Blo 259821 261855 := bstep (se 1 (by rfl) ⟨196391, by rfl⟩ : syracuseStep 261855 = 392783) B392783
theorem B392939 : Blo 259821 392939 := bstep (se 1 (by rfl) ⟨294704, by rfl⟩ : syracuseStep 392939 = 589409) B589409
theorem B261935 : Blo 259821 261935 := bstep (se 1 (by rfl) ⟨196451, by rfl⟩ : syracuseStep 261935 = 392903) B392903
theorem B589625 : Blo 259821 589625 := bstep (se 2 (by rfl) ⟨221109, by rfl⟩ : syracuseStep 589625 = 442219) B442219
theorem B425785 : Blo 259821 425785 := bstep (se 2 (by rfl) ⟨159669, by rfl⟩ : syracuseStep 425785 = 319339) B319339
theorem B262043 : Blo 259821 262043 := bstep (se 1 (by rfl) ⟨196532, by rfl⟩ : syracuseStep 262043 = 393065) B393065
theorem B262095 : Blo 259821 262095 := bstep (se 1 (by rfl) ⟨196571, by rfl⟩ : syracuseStep 262095 = 393143) B393143
theorem B393167 : Blo 259821 393167 := bstep (se 1 (by rfl) ⟨294875, by rfl⟩ : syracuseStep 393167 = 589751) B589751
theorem B262119 : Blo 259821 262119 := bstep (se 1 (by rfl) ⟨196589, by rfl⟩ : syracuseStep 262119 = 393179) B393179
theorem B557275 : Blo 259821 557275 := bstep (se 1 (by rfl) ⟨417956, by rfl⟩ : syracuseStep 557275 = 835913) B835913
theorem B262375 : Blo 259821 262375 := bstep (se 1 (by rfl) ⟨196781, by rfl⟩ : syracuseStep 262375 = 393563) B393563
theorem B590111 : Blo 259821 590111 := bstep (se 1 (by rfl) ⟨442583, by rfl⟩ : syracuseStep 590111 = 885167) B885167
theorem B393503 : Blo 259821 393503 := bstep (se 1 (by rfl) ⟨295127, by rfl⟩ : syracuseStep 393503 = 590255) B590255
theorem B393527 : Blo 259821 393527 := bstep (se 1 (by rfl) ⟨295145, by rfl⟩ : syracuseStep 393527 = 590291) B590291
theorem B10944827 : Blo 259821 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B393599 : Blo 259821 393599 := bstep (se 1 (by rfl) ⟨295199, by rfl⟩ : syracuseStep 393599 = 590399) B590399
theorem B262527 : Blo 259821 262527 := bstep (se 1 (by rfl) ⟨196895, by rfl⟩ : syracuseStep 262527 = 393791) B393791
theorem B393671 : Blo 259821 393671 := bstep (se 1 (by rfl) ⟨295253, by rfl⟩ : syracuseStep 393671 = 590507) B590507
theorem B295375 : Blo 259821 295375 := bstep (se 1 (by rfl) ⟨221531, by rfl⟩ : syracuseStep 295375 = 443063) B443063
theorem B262607 : Blo 259821 262607 := bstep (se 1 (by rfl) ⟨196955, by rfl⟩ : syracuseStep 262607 = 393911) B393911
theorem B6783527 : Blo 259821 6783527 := bstep (se 1 (by rfl) ⟨5087645, by rfl⟩ : syracuseStep 6783527 = 10175291) B10175291
theorem B262759 : Blo 259821 262759 := bstep (se 1 (by rfl) ⟨197069, by rfl⟩ : syracuseStep 262759 = 394139) B394139
theorem B394025 : Blo 259821 394025 := bstep (se 2 (by rfl) ⟨147759, by rfl⟩ : syracuseStep 394025 = 295519) B295519
theorem B394031 : Blo 259821 394031 := bstep (se 1 (by rfl) ⟨295523, by rfl⟩ : syracuseStep 394031 = 591047) B591047
theorem B263023 : Blo 259821 263023 := bstep (se 1 (by rfl) ⟨197267, by rfl⟩ : syracuseStep 263023 = 394535) B394535
theorem B5178269 : Blo 259821 5178269 := bstep (se 3 (by rfl) ⟨970925, by rfl⟩ : syracuseStep 5178269 = 1941851) B1941851
theorem B590759 : Blo 259821 590759 := bstep (se 1 (by rfl) ⟨443069, by rfl⟩ : syracuseStep 590759 = 886139) B886139
theorem B394151 : Blo 259821 394151 := bstep (se 1 (by rfl) ⟨295613, by rfl⟩ : syracuseStep 394151 = 591227) B591227
theorem B263079 : Blo 259821 263079 := bstep (se 1 (by rfl) ⟨197309, by rfl⟩ : syracuseStep 263079 = 394619) B394619
theorem B394235 : Blo 259821 394235 := bstep (se 1 (by rfl) ⟨295676, by rfl⟩ : syracuseStep 394235 = 591353) B591353
theorem B263163 : Blo 259821 263163 := bstep (se 1 (by rfl) ⟨197372, by rfl⟩ : syracuseStep 263163 = 394745) B394745
theorem B394295 : Blo 259821 394295 := bstep (se 1 (by rfl) ⟨295721, by rfl⟩ : syracuseStep 394295 = 591443) B591443
theorem B263231 : Blo 259821 263231 := bstep (se 1 (by rfl) ⟨197423, by rfl⟩ : syracuseStep 263231 = 394847) B394847
theorem B394415 : Blo 259821 394415 := bstep (se 1 (by rfl) ⟨295811, by rfl⟩ : syracuseStep 394415 = 591623) B591623
theorem B263375 : Blo 259821 263375 := bstep (se 1 (by rfl) ⟨197531, by rfl⟩ : syracuseStep 263375 = 395063) B395063
theorem B296347 : Blo 259821 296347 := bstep (se 1 (by rfl) ⟨222260, by rfl⟩ : syracuseStep 296347 = 444521) B444521
theorem B263579 : Blo 259821 263579 := bstep (se 1 (by rfl) ⟨197684, by rfl⟩ : syracuseStep 263579 = 395369) B395369
theorem B394823 : Blo 259821 394823 := bstep (se 1 (by rfl) ⟨296117, by rfl⟩ : syracuseStep 394823 = 592235) B592235
theorem B886355 : Blo 259821 886355 := bstep (se 1 (by rfl) ⟨664766, by rfl⟩ : syracuseStep 886355 = 1329533) B1329533
theorem B1443439 : Blo 259821 1443439 := bstep (se 1 (by rfl) ⟨1082579, by rfl⟩ : syracuseStep 1443439 = 2165159) B2165159
theorem B263791 : Blo 259821 263791 := bstep (se 1 (by rfl) ⟨197843, by rfl⟩ : syracuseStep 263791 = 395687) B395687
theorem B394919 : Blo 259821 394919 := bstep (se 1 (by rfl) ⟨296189, by rfl⟩ : syracuseStep 394919 = 592379) B592379
theorem B395003 : Blo 259821 395003 := bstep (se 1 (by rfl) ⟨296252, by rfl⟩ : syracuseStep 395003 = 592505) B592505
theorem B329503 : Blo 259821 329503 := bstep (se 1 (by rfl) ⟨247127, by rfl⟩ : syracuseStep 329503 = 494255) B494255
theorem B395039 : Blo 259821 395039 := bstep (se 1 (by rfl) ⟨296279, by rfl⟩ : syracuseStep 395039 = 592559) B592559
theorem B591695 : Blo 259821 591695 := bstep (se 1 (by rfl) ⟨443771, by rfl⟩ : syracuseStep 591695 = 887543) B887543
theorem B395087 : Blo 259821 395087 := bstep (se 1 (by rfl) ⟨296315, by rfl⟩ : syracuseStep 395087 = 592631) B592631
theorem B886625 : Blo 259821 886625 := bstep (se 2 (by rfl) ⟨332484, by rfl⟩ : syracuseStep 886625 = 664969) B664969
theorem B591713 : Blo 259821 591713 := bstep (se 2 (by rfl) ⟨221892, by rfl⟩ : syracuseStep 591713 = 443785) B443785
theorem B395207 : Blo 259821 395207 := bstep (se 1 (by rfl) ⟨296405, by rfl⟩ : syracuseStep 395207 = 592811) B592811
theorem B395561 : Blo 259821 395561 := bstep (se 2 (by rfl) ⟨148335, by rfl⟩ : syracuseStep 395561 = 296671) B296671
theorem B395567 : Blo 259821 395567 := bstep (se 1 (by rfl) ⟨296675, by rfl⟩ : syracuseStep 395567 = 593351) B593351
theorem B592289 : Blo 259821 592289 := bstep (se 2 (by rfl) ⟨222108, by rfl⟩ : syracuseStep 592289 = 444217) B444217
theorem B887327 : Blo 259821 887327 := bstep (se 1 (by rfl) ⟨665495, by rfl⟩ : syracuseStep 887327 = 1330991) B1330991
theorem B592415 : Blo 259821 592415 := bstep (se 1 (by rfl) ⟨444311, by rfl⟩ : syracuseStep 592415 = 888623) B888623
theorem B1673875 : Blo 259821 1673875 := bstep (se 1 (by rfl) ⟨1255406, by rfl⟩ : syracuseStep 1673875 = 2510813) B2510813
theorem B297887 : Blo 259821 297887 := bstep (se 1 (by rfl) ⟨223415, by rfl⟩ : syracuseStep 297887 = 446831) B446831
theorem B3378095 : Blo 259821 3378095 := bstep (se 1 (by rfl) ⟨2533571, by rfl⟩ : syracuseStep 3378095 = 5067143) B5067143
theorem B330799 : Blo 259821 330799 := bstep (se 1 (by rfl) ⟨248099, by rfl⟩ : syracuseStep 330799 = 496199) B496199
theorem B560351 : Blo 259821 560351 := bstep (se 1 (by rfl) ⟨420263, by rfl⟩ : syracuseStep 560351 = 840527) B840527
theorem B2526653 : Blo 259821 2526653 := bstep (se 3 (by rfl) ⟨473747, by rfl⟩ : syracuseStep 2526653 = 947495) B947495
theorem B9014777 : Blo 259821 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B527867 : Blo 259821 527867 := bstep (se 1 (by rfl) ⟨395900, by rfl⟩ : syracuseStep 527867 = 791801) B791801
theorem B986687 : Blo 259821 986687 := bstep (se 1 (by rfl) ⟨740015, by rfl⟩ : syracuseStep 986687 = 1480031) B1480031
theorem B560915 : Blo 259821 560915 := bstep (se 1 (by rfl) ⟨420686, by rfl⟩ : syracuseStep 560915 = 841373) B841373
theorem B888731 : Blo 259821 888731 := bstep (se 1 (by rfl) ⟨666548, by rfl⟩ : syracuseStep 888731 = 1333097) B1333097
theorem B659927 : Blo 259821 659927 := bstep (se 1 (by rfl) ⟨494945, by rfl⟩ : syracuseStep 659927 = 989891) B989891
theorem B2232791 : Blo 259821 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B594953 : Blo 259821 594953 := bstep (se 2 (by rfl) ⟨223107, by rfl⟩ : syracuseStep 594953 = 446215) B446215
theorem B889865 : Blo 259821 889865 := bstep (se 2 (by rfl) ⟨333699, by rfl⟩ : syracuseStep 889865 = 667399) B667399
theorem B889919 : Blo 259821 889919 := bstep (se 1 (by rfl) ⟨667439, by rfl⟩ : syracuseStep 889919 = 1334879) B1334879
theorem B1152481 : Blo 259821 1152481 := bstep (se 2 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 1152481 = 864361) B864361
theorem B661243 : Blo 259821 661243 := bstep (se 1 (by rfl) ⟨495932, by rfl⟩ : syracuseStep 661243 = 991865) B991865
theorem B759547 : Blo 259821 759547 := bstep (se 1 (by rfl) ⟨569660, by rfl⟩ : syracuseStep 759547 = 1139321) B1139321
theorem B661385 : Blo 259821 661385 := bstep (se 2 (by rfl) ⟨248019, by rfl⟩ : syracuseStep 661385 = 496039) B496039
theorem B497657 : Blo 259821 497657 := bstep (se 2 (by rfl) ⟨186621, by rfl⟩ : syracuseStep 497657 = 373243) B373243
theorem B3774761 : Blo 259821 3774761 := bstep (se 2 (by rfl) ⟨1415535, by rfl⟩ : syracuseStep 3774761 = 2831071) B2831071
theorem B1055099 : Blo 259821 1055099 := bstep (se 1 (by rfl) ⟨791324, by rfl⟩ : syracuseStep 1055099 = 1582649) B1582649
theorem B662377 : Blo 259821 662377 := bstep (se 2 (by rfl) ⟨248391, by rfl⟩ : syracuseStep 662377 = 496783) B496783
theorem B1252255 : Blo 259821 1252255 := bstep (se 1 (by rfl) ⟨939191, by rfl⟩ : syracuseStep 1252255 = 1878383) B1878383
theorem B1317869 : Blo 259821 1317869 := bstep (se 3 (by rfl) ⟨247100, by rfl⟩ : syracuseStep 1317869 = 494201) B494201
theorem B2891009 : Blo 259821 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B990575 : Blo 259821 990575 := bstep (se 1 (by rfl) ⟨742931, by rfl⟩ : syracuseStep 990575 = 1485863) B1485863
theorem B3775855 : Blo 259821 3775855 := bstep (se 1 (by rfl) ⟨2831891, by rfl⟩ : syracuseStep 3775855 = 5663783) B5663783
theorem B1318679 : Blo 259821 1318679 := bstep (se 1 (by rfl) ⟨989009, by rfl⟩ : syracuseStep 1318679 = 1978019) B1978019
theorem B2236207 : Blo 259821 2236207 := bstep (se 1 (by rfl) ⟨1677155, by rfl⟩ : syracuseStep 2236207 = 3354311) B3354311
theorem B1417351 : Blo 259821 1417351 := bstep (se 1 (by rfl) ⟨1063013, by rfl⟩ : syracuseStep 1417351 = 2126027) B2126027
theorem B860513 : Blo 259821 860513 := bstep (se 2 (by rfl) ⟨322692, by rfl⟩ : syracuseStep 860513 = 645385) B645385
theorem B500489 : Blo 259821 500489 := bstep (se 2 (by rfl) ⟨187683, by rfl⟩ : syracuseStep 500489 = 375367) B375367
theorem B271355 : Blo 259821 271355 := bstep (se 1 (by rfl) ⟨203516, by rfl⟩ : syracuseStep 271355 = 407033) B407033
theorem B4465853 : Blo 259821 4465853 := bstep (se 3 (by rfl) ⟨837347, by rfl⟩ : syracuseStep 4465853 = 1674695) B1674695
theorem B1320299 : Blo 259821 1320299 := bstep (se 1 (by rfl) ⟨990224, by rfl⟩ : syracuseStep 1320299 = 1980449) B1980449
theorem B632539 : Blo 259821 632539 := bstep (se 1 (by rfl) ⟨474404, by rfl⟩ : syracuseStep 632539 = 948809) B948809
theorem B829225 : Blo 259821 829225 := bstep (se 2 (by rfl) ⟨310959, by rfl⟩ : syracuseStep 829225 = 621919) B621919
theorem B1681721 : Blo 259821 1681721 := bstep (se 2 (by rfl) ⟨630645, by rfl⟩ : syracuseStep 1681721 = 1261291) B1261291
theorem B567713 : Blo 259821 567713 := bstep (se 2 (by rfl) ⟨212892, by rfl⟩ : syracuseStep 567713 = 425785) B425785
theorem B470057 : Blo 259821 470057 := bstep (se 2 (by rfl) ⟨176271, by rfl⟩ : syracuseStep 470057 = 352543) B352543
theorem B1322081 : Blo 259821 1322081 := bstep (se 2 (by rfl) ⟨495780, by rfl⟩ : syracuseStep 1322081 = 991561) B991561
theorem B3320947 : Blo 259821 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B2993273 : Blo 259821 2993273 := bstep (se 2 (by rfl) ⟨1122477, by rfl⟩ : syracuseStep 2993273 = 2244955) B2244955
theorem B1879307 : Blo 259821 1879307 := bstep (se 1 (by rfl) ⟨1409480, by rfl⟩ : syracuseStep 1879307 = 2818961) B2818961
theorem B1256791 : Blo 259821 1256791 := bstep (se 1 (by rfl) ⟨942593, by rfl⟩ : syracuseStep 1256791 = 1885187) B1885187
theorem B1486295 : Blo 259821 1486295 := bstep (se 1 (by rfl) ⟨1114721, by rfl⟩ : syracuseStep 1486295 = 2229443) B2229443
theorem B470519 : Blo 259821 470519 := bstep (se 1 (by rfl) ⟨352889, by rfl⟩ : syracuseStep 470519 = 705779) B705779
theorem B1879625 : Blo 259821 1879625 := bstep (se 2 (by rfl) ⟨704859, by rfl⟩ : syracuseStep 1879625 = 1409719) B1409719
theorem B1322891 : Blo 259821 1322891 := bstep (se 1 (by rfl) ⟨992168, by rfl⟩ : syracuseStep 1322891 = 1984337) B1984337
theorem B1257389 : Blo 259821 1257389 := bstep (se 3 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 1257389 = 471521) B471521
theorem B798671 : Blo 259821 798671 := bstep (se 1 (by rfl) ⟨599003, by rfl⟩ : syracuseStep 798671 = 1198007) B1198007
theorem B733151 : Blo 259821 733151 := bstep (se 1 (by rfl) ⟨549863, by rfl⟩ : syracuseStep 733151 = 1099727) B1099727
theorem B16330817 : Blo 259821 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B1782071 : Blo 259821 1782071 := bstep (se 1 (by rfl) ⟨1336553, by rfl⟩ : syracuseStep 1782071 = 2673107) B2673107
theorem B438655 : Blo 259821 438655 := bstep (se 1 (by rfl) ⟨328991, by rfl⟩ : syracuseStep 438655 = 657983) B657983
theorem B995921 : Blo 259821 995921 := bstep (se 2 (by rfl) ⟨373470, by rfl⟩ : syracuseStep 995921 = 746941) B746941
theorem B373351 : Blo 259821 373351 := bstep (se 1 (by rfl) ⟨280013, by rfl⟩ : syracuseStep 373351 = 560027) B560027
theorem B439087 : Blo 259821 439087 := bstep (se 1 (by rfl) ⟨329315, by rfl⟩ : syracuseStep 439087 = 658631) B658631
theorem B1684385 : Blo 259821 1684385 := bstep (se 2 (by rfl) ⟨631644, by rfl⟩ : syracuseStep 1684385 = 1263289) B1263289
theorem B3191723 : Blo 259821 3191723 := bstep (se 1 (by rfl) ⟨2393792, by rfl⟩ : syracuseStep 3191723 = 4787585) B4787585
theorem B1488071 : Blo 259821 1488071 := bstep (se 1 (by rfl) ⟨1116053, by rfl⟩ : syracuseStep 1488071 = 2232107) B2232107
theorem B832787 : Blo 259821 832787 := bstep (se 1 (by rfl) ⟨624590, by rfl⟩ : syracuseStep 832787 = 1249181) B1249181
theorem B1324349 : Blo 259821 1324349 := bstep (se 3 (by rfl) ⟨248315, by rfl⟩ : syracuseStep 1324349 = 496631) B496631
theorem B832967 : Blo 259821 832967 := bstep (se 1 (by rfl) ⟨624725, by rfl⟩ : syracuseStep 832967 = 1249451) B1249451
theorem B1127945 : Blo 259821 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B2504357 : Blo 259821 2504357 := bstep (se 4 (by rfl) ⟨234783, by rfl⟩ : syracuseStep 2504357 = 469567) B469567
theorem B6371065 : Blo 259821 6371065 := bstep (se 2 (by rfl) ⟨2389149, by rfl⟩ : syracuseStep 6371065 = 4778299) B4778299
theorem B440059 : Blo 259821 440059 := bstep (se 1 (by rfl) ⟨330044, by rfl⟩ : syracuseStep 440059 = 660089) B660089
theorem B472969 : Blo 259821 472969 := bstep (se 2 (by rfl) ⟨177363, by rfl⟩ : syracuseStep 472969 = 354727) B354727
theorem B440201 : Blo 259821 440201 := bstep (se 2 (by rfl) ⟨165075, by rfl⟩ : syracuseStep 440201 = 330151) B330151
theorem B2996189 : Blo 259821 2996189 := bstep (se 3 (by rfl) ⟨561785, by rfl⟩ : syracuseStep 2996189 = 1123571) B1123571
theorem B17119289 : Blo 259821 17119289 := bstep (se 2 (by rfl) ⟨6419733, by rfl⟩ : syracuseStep 17119289 = 12839467) B12839467
theorem B1063145 : Blo 259821 1063145 := bstep (se 2 (by rfl) ⟨398679, by rfl⟩ : syracuseStep 1063145 = 797359) B797359
theorem B1685767 : Blo 259821 1685767 := bstep (se 1 (by rfl) ⟨1264325, by rfl⟩ : syracuseStep 1685767 = 2528651) B2528651
theorem B440633 : Blo 259821 440633 := bstep (se 2 (by rfl) ⟨165237, by rfl⟩ : syracuseStep 440633 = 330475) B330475
theorem B1259849 : Blo 259821 1259849 := bstep (se 2 (by rfl) ⟨472443, by rfl⟩ : syracuseStep 1259849 = 944887) B944887
theorem B3422537 : Blo 259821 3422537 := bstep (se 2 (by rfl) ⟨1283451, by rfl⟩ : syracuseStep 3422537 = 2566903) B2566903
theorem B833915 : Blo 259821 833915 := bstep (se 1 (by rfl) ⟨625436, by rfl⟩ : syracuseStep 833915 = 1250873) B1250873
theorem B834067 : Blo 259821 834067 := bstep (se 1 (by rfl) ⟨625550, by rfl⟩ : syracuseStep 834067 = 1251101) B1251101
theorem B375401 : Blo 259821 375401 := bstep (se 2 (by rfl) ⟨140775, by rfl⟩ : syracuseStep 375401 = 281551) B281551
theorem B441247 : Blo 259821 441247 := bstep (se 1 (by rfl) ⟨330935, by rfl⟩ : syracuseStep 441247 = 661871) B661871
theorem B998351 : Blo 259821 998351 := bstep (se 1 (by rfl) ⟨748763, by rfl⟩ : syracuseStep 998351 = 1497527) B1497527
theorem B441679 : Blo 259821 441679 := bstep (se 1 (by rfl) ⟨331259, by rfl⟩ : syracuseStep 441679 = 662519) B662519
theorem B441767 : Blo 259821 441767 := bstep (se 1 (by rfl) ⟨331325, by rfl⟩ : syracuseStep 441767 = 662651) B662651
theorem B998851 : Blo 259821 998851 := bstep (se 1 (by rfl) ⟨749138, by rfl⟩ : syracuseStep 998851 = 1498277) B1498277
theorem B441929 : Blo 259821 441929 := bstep (se 2 (by rfl) ⟨165723, by rfl⟩ : syracuseStep 441929 = 331447) B331447
theorem B1326779 : Blo 259821 1326779 := bstep (se 1 (by rfl) ⟨995084, by rfl⟩ : syracuseStep 1326779 = 1990169) B1990169
theorem B638707 : Blo 259821 638707 := bstep (se 1 (by rfl) ⟨479030, by rfl⟩ : syracuseStep 638707 = 958061) B958061
theorem B475103 : Blo 259821 475103 := bstep (se 1 (by rfl) ⟨356327, by rfl⟩ : syracuseStep 475103 = 712655) B712655
theorem B278911 : Blo 259821 278911 := bstep (se 1 (by rfl) ⟨209183, by rfl⟩ : syracuseStep 278911 = 418367) B418367
theorem B1622591 : Blo 259821 1622591 := bstep (se 1 (by rfl) ⟨1216943, by rfl⟩ : syracuseStep 1622591 = 2433887) B2433887
theorem B442975 : Blo 259821 442975 := bstep (se 1 (by rfl) ⟨332231, by rfl⟩ : syracuseStep 442975 = 664463) B664463
theorem B443387 : Blo 259821 443387 := bstep (se 1 (by rfl) ⟨332540, by rfl⟩ : syracuseStep 443387 = 665081) B665081
theorem B78169315 : Blo 259821 78169315 := bstep (se 1 (by rfl) ⟨58626986, by rfl⟩ : syracuseStep 78169315 = 117253973) B117253973
theorem B1688843 : Blo 259821 1688843 := bstep (se 1 (by rfl) ⟨1266632, by rfl⟩ : syracuseStep 1688843 = 2533265) B2533265
theorem B443819 : Blo 259821 443819 := bstep (se 1 (by rfl) ⟨332864, by rfl⟩ : syracuseStep 443819 = 665729) B665729
theorem B7161331 : Blo 259821 7161331 := bstep (se 1 (by rfl) ⟨5370998, by rfl⟩ : syracuseStep 7161331 = 10741997) B10741997
theorem B1590821 : Blo 259821 1590821 := bstep (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) B298279
theorem B1492901 : Blo 259821 1492901 := bstep (se 4 (by rfl) ⟨139959, by rfl⟩ : syracuseStep 1492901 = 279919) B279919
theorem B444359 : Blo 259821 444359 := bstep (se 1 (by rfl) ⟨333269, by rfl⟩ : syracuseStep 444359 = 666539) B666539
theorem B444649 : Blo 259821 444649 := bstep (se 2 (by rfl) ⟨166743, by rfl⟩ : syracuseStep 444649 = 333487) B333487
theorem B1329695 : Blo 259821 1329695 := bstep (se 1 (by rfl) ⟨997271, by rfl⟩ : syracuseStep 1329695 = 1994543) B1994543
theorem B445115 : Blo 259821 445115 := bstep (se 1 (by rfl) ⟨333836, by rfl⟩ : syracuseStep 445115 = 667673) B667673
theorem B838937 : Blo 259821 838937 := bstep (se 2 (by rfl) ⟨314601, by rfl⟩ : syracuseStep 838937 = 629203) B629203
theorem B2313641 : Blo 259821 2313641 := bstep (se 2 (by rfl) ⟨867615, by rfl⟩ : syracuseStep 2313641 = 1735231) B1735231
theorem B3362309 : Blo 259821 3362309 := bstep (se 4 (by rfl) ⟨315216, by rfl⟩ : syracuseStep 3362309 = 630433) B630433
theorem B740927 : Blo 259821 740927 := bstep (se 1 (by rfl) ⟨555695, by rfl⟩ : syracuseStep 740927 = 1111391) B1111391
theorem B1494611 : Blo 259821 1494611 := bstep (se 1 (by rfl) ⟨1120958, by rfl⟩ : syracuseStep 1494611 = 2241917) B2241917
theorem B675503 : Blo 259821 675503 := bstep (se 1 (by rfl) ⟨506627, by rfl⟩ : syracuseStep 675503 = 1013255) B1013255
theorem B380743 : Blo 259821 380743 := bstep (se 1 (by rfl) ⟨285557, by rfl⟩ : syracuseStep 380743 = 571115) B571115
theorem B2379593 : Blo 259821 2379593 := bstep (se 2 (by rfl) ⟨892347, by rfl⟩ : syracuseStep 2379593 = 1784695) B1784695
theorem B1332287 : Blo 259821 1332287 := bstep (se 1 (by rfl) ⟨999215, by rfl⟩ : syracuseStep 1332287 = 1998431) B1998431
theorem B316591 : Blo 259821 316591 := bstep (se 1 (by rfl) ⟨237443, by rfl⟩ : syracuseStep 316591 = 474887) B474887
theorem B1923047 : Blo 259821 1923047 := bstep (se 1 (by rfl) ⟨1442285, by rfl⟩ : syracuseStep 1923047 = 2884571) B2884571
theorem B841961 : Blo 259821 841961 := bstep (se 2 (by rfl) ⟨315735, by rfl⟩ : syracuseStep 841961 = 631471) B631471
theorem B26368409 : Blo 259821 26368409 := bstep (se 2 (by rfl) ⟨9888153, by rfl⟩ : syracuseStep 26368409 = 19776307) B19776307
theorem B10902197 : Blo 259821 10902197 := bstep (se 5 (by rfl) ⟨511040, by rfl⟩ : syracuseStep 10902197 = 1022081) B1022081
theorem B2841581 : Blo 259821 2841581 := bstep (se 3 (by rfl) ⟨532796, by rfl⟩ : syracuseStep 2841581 = 1065593) B1065593
theorem B2972861 : Blo 259821 2972861 := bstep (se 3 (by rfl) ⟨557411, by rfl⟩ : syracuseStep 2972861 = 1114823) B1114823
theorem B2809441 : Blo 259821 2809441 := bstep (se 2 (by rfl) ⟨1053540, by rfl⟩ : syracuseStep 2809441 = 2107081) B2107081
theorem B942119 : Blo 259821 942119 := bstep (se 1 (by rfl) ⟨706589, by rfl⟩ : syracuseStep 942119 = 1413179) B1413179
theorem B418879 : Blo 259821 418879 := bstep (se 1 (by rfl) ⟨314159, by rfl⟩ : syracuseStep 418879 = 628319) B628319
theorem B877931 : Blo 259821 877931 := bstep (se 1 (by rfl) ⟨658448, by rfl⟩ : syracuseStep 877931 = 1316897) B1316897
theorem B878039 : Blo 259821 878039 := bstep (se 1 (by rfl) ⟨658529, by rfl⟩ : syracuseStep 878039 = 1317059) B1317059
theorem B878201 : Blo 259821 878201 := bstep (se 2 (by rfl) ⟨329325, by rfl⟩ : syracuseStep 878201 = 658651) B658651
theorem B34498457 : Blo 259821 34498457 := bstep (se 2 (by rfl) ⟨12936921, by rfl⟩ : syracuseStep 34498457 = 25873843) B25873843
theorem B4745603 : Blo 259821 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B3041831 : Blo 259821 3041831 := bstep (se 1 (by rfl) ⟨2281373, by rfl⟩ : syracuseStep 3041831 = 4562747) B4562747
theorem B879713 : Blo 259821 879713 := bstep (se 2 (by rfl) ⟨329892, by rfl⟩ : syracuseStep 879713 = 659785) B659785
theorem B584927 : Blo 259821 584927 := bstep (se 1 (by rfl) ⟨438695, by rfl⟩ : syracuseStep 584927 = 877391) B877391
theorem B421129 : Blo 259821 421129 := bstep (se 2 (by rfl) ⟨157923, by rfl⟩ : syracuseStep 421129 = 315847) B315847
theorem B585143 : Blo 259821 585143 := bstep (se 1 (by rfl) ⟨438857, by rfl⟩ : syracuseStep 585143 = 877715) B877715
theorem B585323 : Blo 259821 585323 := bstep (se 1 (by rfl) ⟨438992, by rfl⟩ : syracuseStep 585323 = 877985) B877985
theorem B880253 : Blo 259821 880253 := bstep (se 3 (by rfl) ⟨165047, by rfl⟩ : syracuseStep 880253 = 330095) B330095
theorem B421519 : Blo 259821 421519 := bstep (se 1 (by rfl) ⟨316139, by rfl⟩ : syracuseStep 421519 = 632279) B632279
theorem B585593 : Blo 259821 585593 := bstep (se 2 (by rfl) ⟨219597, by rfl⟩ : syracuseStep 585593 = 439195) B439195
theorem B880523 : Blo 259821 880523 := bstep (se 1 (by rfl) ⟨660392, by rfl⟩ : syracuseStep 880523 = 1320785) B1320785
theorem B881063 : Blo 259821 881063 := bstep (se 1 (by rfl) ⟨660797, by rfl⟩ : syracuseStep 881063 = 1321595) B1321595
theorem B750073 : Blo 259821 750073 := bstep (se 2 (by rfl) ⟨281277, by rfl⟩ : syracuseStep 750073 = 562555) B562555
theorem B389735 : Blo 259821 389735 := bstep (se 1 (by rfl) ⟨292301, by rfl⟩ : syracuseStep 389735 = 584603) B584603
theorem B389867 : Blo 259821 389867 := bstep (se 1 (by rfl) ⟨292400, by rfl⟩ : syracuseStep 389867 = 584801) B584801
theorem B389897 : Blo 259821 389897 := bstep (se 2 (by rfl) ⟨146211, by rfl⟩ : syracuseStep 389897 = 292423) B292423
theorem B389999 : Blo 259821 389999 := bstep (se 1 (by rfl) ⟨292499, by rfl⟩ : syracuseStep 389999 = 584999) B584999
theorem B455743 : Blo 259821 455743 := bstep (se 1 (by rfl) ⟨341807, by rfl⟩ : syracuseStep 455743 = 683615) B683615
theorem B390251 : Blo 259821 390251 := bstep (se 1 (by rfl) ⟨292688, by rfl⟩ : syracuseStep 390251 = 585377) B585377
theorem B390491 : Blo 259821 390491 := bstep (se 1 (by rfl) ⟨292868, by rfl⟩ : syracuseStep 390491 = 585737) B585737
theorem B390767 : Blo 259821 390767 := bstep (se 1 (by rfl) ⟨293075, by rfl⟩ : syracuseStep 390767 = 586151) B586151
theorem B390839 : Blo 259821 390839 := bstep (se 1 (by rfl) ⟨293129, by rfl⟩ : syracuseStep 390839 = 586259) B586259
theorem B587447 : Blo 259821 587447 := bstep (se 1 (by rfl) ⟨440585, by rfl⟩ : syracuseStep 587447 = 881171) B881171
theorem B882359 : Blo 259821 882359 := bstep (se 1 (by rfl) ⟨661769, by rfl⟩ : syracuseStep 882359 = 1323539) B1323539
theorem B390875 : Blo 259821 390875 := bstep (se 1 (by rfl) ⟨293156, by rfl⟩ : syracuseStep 390875 = 586313) B586313
theorem B259835 : Blo 259821 259835 := bstep (se 1 (by rfl) ⟨194876, by rfl⟩ : syracuseStep 259835 = 389753) B389753
theorem B292603 : Blo 259821 292603 := bstep (se 1 (by rfl) ⟨219452, by rfl⟩ : syracuseStep 292603 = 438905) B438905
theorem B259871 : Blo 259821 259871 := bstep (se 1 (by rfl) ⟨194903, by rfl⟩ : syracuseStep 259871 = 389807) B389807
theorem B292639 : Blo 259821 292639 := bstep (se 1 (by rfl) ⟨219479, by rfl⟩ : syracuseStep 292639 = 438959) B438959
theorem B259903 : Blo 259821 259903 := bstep (se 1 (by rfl) ⟨194927, by rfl⟩ : syracuseStep 259903 = 389855) B389855
theorem B391049 : Blo 259821 391049 := bstep (se 2 (by rfl) ⟨146643, by rfl⟩ : syracuseStep 391049 = 293287) B293287
theorem B260079 : Blo 259821 260079 := bstep (se 1 (by rfl) ⟨195059, by rfl⟩ : syracuseStep 260079 = 390119) B390119
theorem B391151 : Blo 259821 391151 := bstep (se 1 (by rfl) ⟨293363, by rfl⟩ : syracuseStep 391151 = 586727) B586727
theorem B260251 : Blo 259821 260251 := bstep (se 1 (by rfl) ⟨195188, by rfl⟩ : syracuseStep 260251 = 390377) B390377
theorem B260287 : Blo 259821 260287 := bstep (se 1 (by rfl) ⟨195215, by rfl⟩ : syracuseStep 260287 = 390431) B390431
theorem B391403 : Blo 259821 391403 := bstep (se 1 (by rfl) ⟨293552, by rfl⟩ : syracuseStep 391403 = 587105) B587105
theorem B391463 : Blo 259821 391463 := bstep (se 1 (by rfl) ⟨293597, by rfl⟩ : syracuseStep 391463 = 587195) B587195
theorem B1112363 : Blo 259821 1112363 := bstep (se 1 (by rfl) ⟨834272, by rfl⟩ : syracuseStep 1112363 = 1668545) B1668545
theorem B260399 : Blo 259821 260399 := bstep (se 1 (by rfl) ⟨195299, by rfl⟩ : syracuseStep 260399 = 390599) B390599
theorem B1898795 : Blo 259821 1898795 := bstep (se 1 (by rfl) ⟨1424096, by rfl⟩ : syracuseStep 1898795 = 2848193) B2848193
theorem B391547 : Blo 259821 391547 := bstep (se 1 (by rfl) ⟨293660, by rfl⟩ : syracuseStep 391547 = 587321) B587321
theorem B260635 : Blo 259821 260635 := bstep (se 1 (by rfl) ⟨195476, by rfl⟩ : syracuseStep 260635 = 390953) B390953
theorem B260639 : Blo 259821 260639 := bstep (se 1 (by rfl) ⟨195479, by rfl⟩ : syracuseStep 260639 = 390959) B390959
theorem B1014329 : Blo 259821 1014329 := bstep (se 2 (by rfl) ⟨380373, by rfl⟩ : syracuseStep 1014329 = 760747) B760747
theorem B391817 : Blo 259821 391817 := bstep (se 2 (by rfl) ⟨146931, by rfl⟩ : syracuseStep 391817 = 293863) B293863
theorem B391991 : Blo 259821 391991 := bstep (se 1 (by rfl) ⟨293993, by rfl⟩ : syracuseStep 391991 = 587987) B587987
theorem B260955 : Blo 259821 260955 := bstep (se 1 (by rfl) ⟨195716, by rfl⟩ : syracuseStep 260955 = 391433) B391433
theorem B392027 : Blo 259821 392027 := bstep (se 1 (by rfl) ⟨294020, by rfl⟩ : syracuseStep 392027 = 588041) B588041
theorem B588635 : Blo 259821 588635 := bstep (se 1 (by rfl) ⟨441476, by rfl⟩ : syracuseStep 588635 = 882953) B882953
theorem B883547 : Blo 259821 883547 := bstep (se 1 (by rfl) ⟨662660, by rfl⟩ : syracuseStep 883547 = 1325321) B1325321
theorem B3341189 : Blo 259821 3341189 := bstep (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) B626473
theorem B261023 : Blo 259821 261023 := bstep (se 1 (by rfl) ⟨195767, by rfl⟩ : syracuseStep 261023 = 391535) B391535
theorem B293791 : Blo 259821 293791 := bstep (se 1 (by rfl) ⟨220343, by rfl⟩ : syracuseStep 293791 = 440687) B440687
theorem B392171 : Blo 259821 392171 := bstep (se 1 (by rfl) ⟨294128, by rfl⟩ : syracuseStep 392171 = 588257) B588257
theorem B2554895 : Blo 259821 2554895 := bstep (se 1 (by rfl) ⟨1916171, by rfl⟩ : syracuseStep 2554895 = 3832343) B3832343
theorem B261167 : Blo 259821 261167 := bstep (se 1 (by rfl) ⟨195875, by rfl⟩ : syracuseStep 261167 = 391751) B391751
theorem B293935 : Blo 259821 293935 := bstep (se 1 (by rfl) ⟨220451, by rfl⟩ : syracuseStep 293935 = 440903) B440903
theorem B261191 : Blo 259821 261191 := bstep (se 1 (by rfl) ⟨195893, by rfl⟩ : syracuseStep 261191 = 391787) B391787
theorem B392375 : Blo 259821 392375 := bstep (se 1 (by rfl) ⟨294281, by rfl⟩ : syracuseStep 392375 = 588563) B588563
theorem B261343 : Blo 259821 261343 := bstep (se 1 (by rfl) ⟨196007, by rfl⟩ : syracuseStep 261343 = 392015) B392015
theorem B294223 : Blo 259821 294223 := bstep (se 1 (by rfl) ⟨220667, by rfl⟩ : syracuseStep 294223 = 441335) B441335
theorem B392615 : Blo 259821 392615 := bstep (se 1 (by rfl) ⟨294461, by rfl⟩ : syracuseStep 392615 = 588923) B588923
theorem B261607 : Blo 259821 261607 := bstep (se 1 (by rfl) ⟨196205, by rfl⟩ : syracuseStep 261607 = 392411) B392411
theorem B392699 : Blo 259821 392699 := bstep (se 1 (by rfl) ⟨294524, by rfl⟩ : syracuseStep 392699 = 589049) B589049
theorem B589391 : Blo 259821 589391 := bstep (se 1 (by rfl) ⟨442043, by rfl⟩ : syracuseStep 589391 = 884087) B884087
theorem B884303 : Blo 259821 884303 := bstep (se 1 (by rfl) ⟨663227, by rfl⟩ : syracuseStep 884303 = 1326455) B1326455
theorem B261723 : Blo 259821 261723 := bstep (se 1 (by rfl) ⟨196292, by rfl⟩ : syracuseStep 261723 = 392585) B392585
theorem B392795 : Blo 259821 392795 := bstep (se 1 (by rfl) ⟨294596, by rfl⟩ : syracuseStep 392795 = 589193) B589193
theorem B392879 : Blo 259821 392879 := bstep (se 1 (by rfl) ⟨294659, by rfl⟩ : syracuseStep 392879 = 589319) B589319
theorem B884411 : Blo 259821 884411 := bstep (se 1 (by rfl) ⟨663308, by rfl⟩ : syracuseStep 884411 = 1326617) B1326617
theorem B1277687 : Blo 259821 1277687 := bstep (se 1 (by rfl) ⟨958265, by rfl⟩ : syracuseStep 1277687 = 1916531) B1916531
theorem B392999 : Blo 259821 392999 := bstep (se 1 (by rfl) ⟨294749, by rfl⟩ : syracuseStep 392999 = 589499) B589499
theorem B261959 : Blo 259821 261959 := bstep (se 1 (by rfl) ⟨196469, by rfl⟩ : syracuseStep 261959 = 392939) B392939
theorem B294727 : Blo 259821 294727 := bstep (se 1 (by rfl) ⟨221045, by rfl⟩ : syracuseStep 294727 = 442091) B442091
theorem B393083 : Blo 259821 393083 := bstep (se 1 (by rfl) ⟨294812, by rfl⟩ : syracuseStep 393083 = 589625) B589625
theorem B262111 : Blo 259821 262111 := bstep (se 1 (by rfl) ⟨196583, by rfl⟩ : syracuseStep 262111 = 393167) B393167
theorem B393407 : Blo 259821 393407 := bstep (se 1 (by rfl) ⟨295055, by rfl⟩ : syracuseStep 393407 = 590111) B590111
theorem B262335 : Blo 259821 262335 := bstep (se 1 (by rfl) ⟨196751, by rfl⟩ : syracuseStep 262335 = 393503) B393503
theorem B262351 : Blo 259821 262351 := bstep (se 1 (by rfl) ⟨196763, by rfl⟩ : syracuseStep 262351 = 393527) B393527
theorem B262399 : Blo 259821 262399 := bstep (se 1 (by rfl) ⟨196799, by rfl⟩ : syracuseStep 262399 = 393599) B393599
theorem B262447 : Blo 259821 262447 := bstep (se 1 (by rfl) ⟨196835, by rfl⟩ : syracuseStep 262447 = 393671) B393671
theorem B1081727 : Blo 259821 1081727 := bstep (se 1 (by rfl) ⟨811295, by rfl⟩ : syracuseStep 1081727 = 1622591) B1622591
theorem B262683 : Blo 259821 262683 := bstep (se 1 (by rfl) ⟨197012, by rfl⟩ : syracuseStep 262683 = 394025) B394025
theorem B262687 : Blo 259821 262687 := bstep (se 1 (by rfl) ⟨197015, by rfl⟩ : syracuseStep 262687 = 394031) B394031
theorem B393833 : Blo 259821 393833 := bstep (se 2 (by rfl) ⟨147687, by rfl⟩ : syracuseStep 393833 = 295375) B295375
theorem B393839 : Blo 259821 393839 := bstep (se 1 (by rfl) ⟨295379, by rfl⟩ : syracuseStep 393839 = 590759) B590759
theorem B262767 : Blo 259821 262767 := bstep (se 1 (by rfl) ⟨197075, by rfl⟩ : syracuseStep 262767 = 394151) B394151
theorem B295591 : Blo 259821 295591 := bstep (se 1 (by rfl) ⟨221693, by rfl⟩ : syracuseStep 295591 = 443387) B443387
theorem B262823 : Blo 259821 262823 := bstep (se 1 (by rfl) ⟨197117, by rfl⟩ : syracuseStep 262823 = 394235) B394235
theorem B262863 : Blo 259821 262863 := bstep (se 1 (by rfl) ⟨197147, by rfl⟩ : syracuseStep 262863 = 394295) B394295
theorem B262943 : Blo 259821 262943 := bstep (se 1 (by rfl) ⟨197207, by rfl⟩ : syracuseStep 262943 = 394415) B394415
theorem B590633 : Blo 259821 590633 := bstep (se 2 (by rfl) ⟨221487, by rfl⟩ : syracuseStep 590633 = 442975) B442975
theorem B2294701 : Blo 259821 2294701 := bstep (se 3 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 2294701 = 860513) B860513
theorem B295879 : Blo 259821 295879 := bstep (se 1 (by rfl) ⟨221909, by rfl⟩ : syracuseStep 295879 = 443819) B443819
theorem B263215 : Blo 259821 263215 := bstep (se 1 (by rfl) ⟨197411, by rfl⟩ : syracuseStep 263215 = 394823) B394823
theorem B590903 : Blo 259821 590903 := bstep (se 1 (by rfl) ⟨443177, by rfl⟩ : syracuseStep 590903 = 886355) B886355
theorem B263279 : Blo 259821 263279 := bstep (se 1 (by rfl) ⟨197459, by rfl⟩ : syracuseStep 263279 = 394919) B394919
theorem B263335 : Blo 259821 263335 := bstep (se 1 (by rfl) ⟨197501, by rfl⟩ : syracuseStep 263335 = 395003) B395003
theorem B263359 : Blo 259821 263359 := bstep (se 1 (by rfl) ⟨197519, by rfl⟩ : syracuseStep 263359 = 395039) B395039
theorem B394463 : Blo 259821 394463 := bstep (se 1 (by rfl) ⟨295847, by rfl⟩ : syracuseStep 394463 = 591695) B591695
theorem B263391 : Blo 259821 263391 := bstep (se 1 (by rfl) ⟨197543, by rfl⟩ : syracuseStep 263391 = 395087) B395087
theorem B591083 : Blo 259821 591083 := bstep (se 1 (by rfl) ⟨443312, by rfl⟩ : syracuseStep 591083 = 886625) B886625
theorem B394475 : Blo 259821 394475 := bstep (se 1 (by rfl) ⟨295856, by rfl⟩ : syracuseStep 394475 = 591713) B591713
theorem B296239 : Blo 259821 296239 := bstep (se 1 (by rfl) ⟨222179, by rfl⟩ : syracuseStep 296239 = 444359) B444359
theorem B263471 : Blo 259821 263471 := bstep (se 1 (by rfl) ⟨197603, by rfl⟩ : syracuseStep 263471 = 395207) B395207
theorem B558505 : Blo 259821 558505 := bstep (se 2 (by rfl) ⟨209439, by rfl⟩ : syracuseStep 558505 = 418879) B418879
theorem B18089405 : Blo 259821 18089405 := bstep (se 3 (by rfl) ⟨3391763, by rfl⟩ : syracuseStep 18089405 = 6783527) B6783527
theorem B263707 : Blo 259821 263707 := bstep (se 1 (by rfl) ⟨197780, by rfl⟩ : syracuseStep 263707 = 395561) B395561
theorem B263711 : Blo 259821 263711 := bstep (se 1 (by rfl) ⟨197783, by rfl⟩ : syracuseStep 263711 = 395567) B395567
theorem B394859 : Blo 259821 394859 := bstep (se 1 (by rfl) ⟨296144, by rfl⟩ : syracuseStep 394859 = 592289) B592289
theorem B886463 : Blo 259821 886463 := bstep (se 1 (by rfl) ⟨664847, by rfl⟩ : syracuseStep 886463 = 1329695) B1329695
theorem B591551 : Blo 259821 591551 := bstep (se 1 (by rfl) ⟨443663, by rfl⟩ : syracuseStep 591551 = 887327) B887327
theorem B394943 : Blo 259821 394943 := bstep (se 1 (by rfl) ⟨296207, by rfl⟩ : syracuseStep 394943 = 592415) B592415
theorem B296743 : Blo 259821 296743 := bstep (se 1 (by rfl) ⟨222557, by rfl⟩ : syracuseStep 296743 = 445115) B445115
theorem B395129 : Blo 259821 395129 := bstep (se 2 (by rfl) ⟨148173, by rfl⟩ : syracuseStep 395129 = 296347) B296347
theorem B657791 : Blo 259821 657791 := bstep (se 1 (by rfl) ⟨493343, by rfl⟩ : syracuseStep 657791 = 986687) B986687
theorem B493951 : Blo 259821 493951 := bstep (se 1 (by rfl) ⟨370463, by rfl⟩ : syracuseStep 493951 = 740927) B740927
theorem B592487 : Blo 259821 592487 := bstep (se 1 (by rfl) ⟨444365, by rfl⟩ : syracuseStep 592487 = 888731) B888731
theorem B592865 : Blo 259821 592865 := bstep (se 2 (by rfl) ⟨222324, by rfl⟩ : syracuseStep 592865 = 444649) B444649
theorem B396635 : Blo 259821 396635 := bstep (se 1 (by rfl) ⟨297476, by rfl⟩ : syracuseStep 396635 = 594953) B594953
theorem B593243 : Blo 259821 593243 := bstep (se 1 (by rfl) ⟨444932, by rfl⟩ : syracuseStep 593243 = 889865) B889865
theorem B888191 : Blo 259821 888191 := bstep (se 1 (by rfl) ⟨666143, by rfl⟩ : syracuseStep 888191 = 1332287) B1332287
theorem B593279 : Blo 259821 593279 := bstep (se 1 (by rfl) ⟨444959, by rfl⟩ : syracuseStep 593279 = 889919) B889919
theorem B2231833 : Blo 259821 2231833 := bstep (se 2 (by rfl) ⟨836937, by rfl⟩ : syracuseStep 2231833 = 1673875) B1673875
theorem B1282031 : Blo 259821 1282031 := bstep (se 1 (by rfl) ⟨961523, by rfl⟩ : syracuseStep 1282031 = 1923047) B1923047
theorem B331771 : Blo 259821 331771 := bstep (se 1 (by rfl) ⟨248828, by rfl⟩ : syracuseStep 331771 = 497657) B497657
theorem B4427929 : Blo 259821 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B561505 : Blo 259821 561505 := bstep (se 2 (by rfl) ⟨210564, by rfl⟩ : syracuseStep 561505 = 421129) B421129
theorem B1675721 : Blo 259821 1675721 := bstep (se 2 (by rfl) ⟨628395, by rfl⟩ : syracuseStep 1675721 = 1256791) B1256791
theorem B562025 : Blo 259821 562025 := bstep (se 2 (by rfl) ⟨210759, by rfl⟩ : syracuseStep 562025 = 421519) B421519
theorem B660383 : Blo 259821 660383 := bstep (se 1 (by rfl) ⟨495287, by rfl⟩ : syracuseStep 660383 = 990575) B990575
theorem B628079 : Blo 259821 628079 := bstep (se 1 (by rfl) ⟨471059, by rfl⟩ : syracuseStep 628079 = 942119) B942119
theorem B333659 : Blo 259821 333659 := bstep (se 1 (by rfl) ⟨250244, by rfl⟩ : syracuseStep 333659 = 500489) B500489
theorem B497801 : Blo 259821 497801 := bstep (se 2 (by rfl) ⟨186675, by rfl⟩ : syracuseStep 497801 = 373351) B373351
theorem B1121147 : Blo 259821 1121147 := bstep (se 1 (by rfl) ⟨840860, by rfl⟩ : syracuseStep 1121147 = 1681721) B1681721
theorem B1252871 : Blo 259821 1252871 := bstep (se 1 (by rfl) ⟨939653, by rfl⟩ : syracuseStep 1252871 = 1879307) B1879307
theorem B990863 : Blo 259821 990863 := bstep (se 1 (by rfl) ⟨743147, by rfl⟩ : syracuseStep 990863 = 1486295) B1486295
theorem B8494753 : Blo 259821 8494753 := bstep (se 2 (by rfl) ⟨3185532, by rfl⟩ : syracuseStep 8494753 = 6371065) B6371065
theorem B1253083 : Blo 259821 1253083 := bstep (se 1 (by rfl) ⟨939812, by rfl⟩ : syracuseStep 1253083 = 1879625) B1879625
theorem B10887211 : Blo 259821 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B1253485 : Blo 259821 1253485 := bstep (se 3 (by rfl) ⟨235028, by rfl⟩ : syracuseStep 1253485 = 470057) B470057
theorem B1188047 : Blo 259821 1188047 := bstep (se 1 (by rfl) ⟨891035, by rfl⟩ : syracuseStep 1188047 = 1782071) B1782071
theorem B663947 : Blo 259821 663947 := bstep (se 1 (by rfl) ⟨497960, by rfl⟩ : syracuseStep 663947 = 995921) B995921
theorem B1122923 : Blo 259821 1122923 := bstep (se 1 (by rfl) ⟨842192, by rfl⟩ : syracuseStep 1122923 = 1684385) B1684385
theorem B7709357 : Blo 259821 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B2237165 : Blo 259821 2237165 := bstep (se 3 (by rfl) ⟨419468, by rfl⟩ : syracuseStep 2237165 = 838937) B838937
theorem B992047 : Blo 259821 992047 := bstep (se 1 (by rfl) ⟨744035, by rfl⟩ : syracuseStep 992047 = 1488071) B1488071
theorem B6169709 : Blo 259821 6169709 := bstep (se 3 (by rfl) ⟨1156820, by rfl⟩ : syracuseStep 6169709 = 2313641) B2313641
theorem B11412859 : Blo 259821 11412859 := bstep (se 1 (by rfl) ⟨8559644, by rfl⟩ : syracuseStep 11412859 = 17119289) B17119289
theorem B665567 : Blo 259821 665567 := bstep (se 1 (by rfl) ⟨499175, by rfl⟩ : syracuseStep 665567 = 998351) B998351
theorem B3745921 : Blo 259821 3745921 := bstep (se 2 (by rfl) ⟨1404720, by rfl⟩ : syracuseStep 3745921 = 2809441) B2809441
theorem B2894453 : Blo 259821 2894453 := bstep (se 5 (by rfl) ⟨135677, by rfl⟩ : syracuseStep 2894453 = 271355) B271355
theorem B371881 : Blo 259821 371881 := bstep (se 2 (by rfl) ⟨139455, by rfl⟩ : syracuseStep 371881 = 278911) B278911
theorem B3452179 : Blo 259821 3452179 := bstep (se 1 (by rfl) ⟨2589134, by rfl⟩ : syracuseStep 3452179 = 5178269) B5178269
theorem B1125895 : Blo 259821 1125895 := bstep (se 1 (by rfl) ⟨844421, by rfl⟩ : syracuseStep 1125895 = 1688843) B1688843
theorem B1060547 : Blo 259821 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B995267 : Blo 259821 995267 := bstep (se 1 (by rfl) ⟨746450, by rfl⟩ : syracuseStep 995267 = 1492901) B1492901
theorem B9548441 : Blo 259821 9548441 := bstep (se 2 (by rfl) ⟨3580665, by rfl⟩ : syracuseStep 9548441 = 7161331) B7161331
theorem B373567 : Blo 259821 373567 := bstep (se 1 (by rfl) ⟨280175, by rfl⟩ : syracuseStep 373567 = 560351) B560351
theorem B1684435 : Blo 259821 1684435 := bstep (se 1 (by rfl) ⟨1263326, by rfl⟩ : syracuseStep 1684435 = 2526653) B2526653
theorem B6009851 : Blo 259821 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B2241539 : Blo 259821 2241539 := bstep (se 1 (by rfl) ⟨1681154, by rfl⟩ : syracuseStep 2241539 = 3362309) B3362309
theorem B439337 : Blo 259821 439337 := bstep (se 2 (by rfl) ⟨164751, by rfl⟩ : syracuseStep 439337 = 329503) B329503
theorem B996407 : Blo 259821 996407 := bstep (se 1 (by rfl) ⟨747305, by rfl⟩ : syracuseStep 996407 = 1494611) B1494611
theorem B373943 : Blo 259821 373943 := bstep (se 1 (by rfl) ⟨280457, by rfl⟩ : syracuseStep 373943 = 560915) B560915
theorem B1586395 : Blo 259821 1586395 := bstep (se 1 (by rfl) ⟨1189796, by rfl⟩ : syracuseStep 1586395 = 2379593) B2379593
theorem B439951 : Blo 259821 439951 := bstep (se 1 (by rfl) ⟨329963, by rfl⟩ : syracuseStep 439951 = 659927) B659927
theorem B1488527 : Blo 259821 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B440923 : Blo 259821 440923 := bstep (se 1 (by rfl) ⟨330692, by rfl⟩ : syracuseStep 440923 = 661385) B661385
theorem B441065 : Blo 259821 441065 := bstep (se 2 (by rfl) ⟨165399, by rfl⟩ : syracuseStep 441065 = 330799) B330799
theorem B703399 : Blo 259821 703399 := bstep (se 1 (by rfl) ⟨527549, by rfl⟩ : syracuseStep 703399 = 1055099) B1055099
theorem B17578939 : Blo 259821 17578939 := bstep (se 1 (by rfl) ⟨13184204, by rfl⟩ : syracuseStep 17578939 = 26368409) B26368409
theorem B1981907 : Blo 259821 1981907 := bstep (se 1 (by rfl) ⟨1486430, by rfl⟩ : syracuseStep 1981907 = 2972861) B2972861
theorem B2245229 : Blo 259821 2245229 := bstep (se 3 (by rfl) ⟨420980, by rfl⟩ : syracuseStep 2245229 = 841961) B841961
theorem B1000097 : Blo 259821 1000097 := bstep (se 2 (by rfl) ⟨375036, by rfl⟩ : syracuseStep 1000097 = 750073) B750073
theorem B1688485 : Blo 259821 1688485 := bstep (se 4 (by rfl) ⟨158295, by rfl⟩ : syracuseStep 1688485 = 316591) B316591
theorem B607657 : Blo 259821 607657 := bstep (se 2 (by rfl) ⟨227871, by rfl⟩ : syracuseStep 607657 = 455743) B455743
theorem B8111549 : Blo 259821 8111549 := bstep (se 3 (by rfl) ⟨1520915, by rfl⟩ : syracuseStep 8111549 = 3041831) B3041831
theorem B3163735 : Blo 259821 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B378475 : Blo 259821 378475 := bstep (se 1 (by rfl) ⟨283856, by rfl⟩ : syracuseStep 378475 = 567713) B567713
theorem B1001069 : Blo 259821 1001069 := bstep (se 3 (by rfl) ⟨187700, by rfl⟩ : syracuseStep 1001069 = 375401) B375401
theorem B313679 : Blo 259821 313679 := bstep (se 1 (by rfl) ⟨235259, by rfl⟩ : syracuseStep 313679 = 470519) B470519
theorem B838259 : Blo 259821 838259 := bstep (se 1 (by rfl) ⟨628694, by rfl⟩ : syracuseStep 838259 = 1257389) B1257389
theorem B2247689 : Blo 259821 2247689 := bstep (se 2 (by rfl) ⟨842883, by rfl⟩ : syracuseStep 2247689 = 1685767) B1685767
theorem B4050917 : Blo 259821 4050917 := bstep (se 4 (by rfl) ⟨379773, by rfl⟩ : syracuseStep 4050917 = 759547) B759547
theorem B708763 : Blo 259821 708763 := bstep (se 1 (by rfl) ⟨531572, by rfl⟩ : syracuseStep 708763 = 1063145) B1063145
theorem B741575 : Blo 259821 741575 := bstep (se 1 (by rfl) ⟨556181, by rfl⟩ : syracuseStep 741575 = 1112363) B1112363
theorem B1265863 : Blo 259821 1265863 := bstep (se 1 (by rfl) ⟨949397, by rfl⟩ : syracuseStep 1265863 = 1898795) B1898795
theorem B839899 : Blo 259821 839899 := bstep (se 1 (by rfl) ⟨629924, by rfl⟩ : syracuseStep 839899 = 1259849) B1259849
theorem B2281691 : Blo 259821 2281691 := bstep (se 1 (by rfl) ⟨1711268, by rfl⟩ : syracuseStep 2281691 = 3422537) B3422537
theorem B676219 : Blo 259821 676219 := bstep (se 1 (by rfl) ⟨507164, by rfl⟩ : syracuseStep 676219 = 1014329) B1014329
theorem B5034473 : Blo 259821 5034473 := bstep (se 2 (by rfl) ⟨1887927, by rfl⟩ : syracuseStep 5034473 = 3775855) B3775855
theorem B1331801 : Blo 259821 1331801 := bstep (se 2 (by rfl) ⟨499425, by rfl⟩ : syracuseStep 1331801 = 998851) B998851
theorem B1266941 : Blo 259821 1266941 := bstep (se 3 (by rfl) ⟨237551, by rfl⟩ : syracuseStep 1266941 = 475103) B475103
theorem B1889801 : Blo 259821 1889801 := bstep (se 2 (by rfl) ⟨708675, by rfl⟩ : syracuseStep 1889801 = 1417351) B1417351
theorem B7296551 : Blo 259821 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B743033 : Blo 259821 743033 := bstep (se 2 (by rfl) ⟨278637, by rfl⟩ : syracuseStep 743033 = 557275) B557275
theorem B104225753 : Blo 259821 104225753 := bstep (se 2 (by rfl) ⟨39084657, by rfl⟩ : syracuseStep 104225753 = 78169315) B78169315
theorem B2252063 : Blo 259821 2252063 := bstep (se 1 (by rfl) ⟨1689047, by rfl⟩ : syracuseStep 2252063 = 3378095) B3378095
theorem B843385 : Blo 259821 843385 := bstep (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) B632539
theorem B351911 : Blo 259821 351911 := bstep (se 1 (by rfl) ⟨263933, by rfl⟩ : syracuseStep 351911 = 527867) B527867
theorem B1105633 : Blo 259821 1105633 := bstep (se 2 (by rfl) ⟨414612, by rfl⟩ : syracuseStep 1105633 = 829225) B829225
theorem B450335 : Blo 259821 450335 := bstep (se 1 (by rfl) ⟨337751, by rfl⟩ : syracuseStep 450335 = 675503) B675503
theorem B4448357 : Blo 259821 4448357 := bstep (se 4 (by rfl) ⟨417033, by rfl⟩ : syracuseStep 4448357 = 834067) B834067
theorem B3007853 : Blo 259821 3007853 := bstep (se 3 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 3007853 = 1127945) B1127945
theorem B2516507 : Blo 259821 2516507 := bstep (se 1 (by rfl) ⟨1887380, by rfl⟩ : syracuseStep 2516507 = 3774761) B3774761
theorem B7268131 : Blo 259821 7268131 := bstep (se 1 (by rfl) ⟨5451098, by rfl⟩ : syracuseStep 7268131 = 10902197) B10902197
theorem B878579 : Blo 259821 878579 := bstep (se 1 (by rfl) ⟨658934, by rfl⟩ : syracuseStep 878579 = 1317869) B1317869
theorem B1894387 : Blo 259821 1894387 := bstep (se 1 (by rfl) ⟨1420790, by rfl⟩ : syracuseStep 1894387 = 2841581) B2841581
theorem B879119 : Blo 259821 879119 := bstep (se 1 (by rfl) ⟨659339, by rfl⟩ : syracuseStep 879119 = 1318679) B1318679
theorem B584873 : Blo 259821 584873 := bstep (se 2 (by rfl) ⟨219327, by rfl⟩ : syracuseStep 584873 = 438655) B438655
theorem B2977235 : Blo 259821 2977235 := bstep (se 1 (by rfl) ⟨2232926, by rfl⟩ : syracuseStep 2977235 = 4465853) B4465853
theorem B585287 : Blo 259821 585287 := bstep (se 1 (by rfl) ⟨438965, by rfl⟩ : syracuseStep 585287 = 877931) B877931
theorem B880199 : Blo 259821 880199 := bstep (se 1 (by rfl) ⟨660149, by rfl⟩ : syracuseStep 880199 = 1320299) B1320299
theorem B585359 : Blo 259821 585359 := bstep (se 1 (by rfl) ⟨439019, by rfl⟩ : syracuseStep 585359 = 878039) B878039
theorem B585449 : Blo 259821 585449 := bstep (se 2 (by rfl) ⟨219543, by rfl⟩ : syracuseStep 585449 = 439087) B439087
theorem B585467 : Blo 259821 585467 := bstep (se 1 (by rfl) ⟨439100, by rfl⟩ : syracuseStep 585467 = 878201) B878201
theorem B22998971 : Blo 259821 22998971 := bstep (se 1 (by rfl) ⟨17249228, by rfl⟩ : syracuseStep 22998971 = 34498457) B34498457
theorem B1536641 : Blo 259821 1536641 := bstep (se 2 (by rfl) ⟨576240, by rfl⟩ : syracuseStep 1536641 = 1152481) B1152481
theorem B586475 : Blo 259821 586475 := bstep (se 1 (by rfl) ⟨439856, by rfl⟩ : syracuseStep 586475 = 879713) B879713
theorem B881387 : Blo 259821 881387 := bstep (se 1 (by rfl) ⟨661040, by rfl⟩ : syracuseStep 881387 = 1322081) B1322081
theorem B1995515 : Blo 259821 1995515 := bstep (se 1 (by rfl) ⟨1496636, by rfl⟩ : syracuseStep 1995515 = 2993273) B2993273
theorem B389951 : Blo 259821 389951 := bstep (se 1 (by rfl) ⟨292463, by rfl⟩ : syracuseStep 389951 = 584927) B584927
theorem B390095 : Blo 259821 390095 := bstep (se 1 (by rfl) ⟨292571, by rfl⟩ : syracuseStep 390095 = 585143) B585143
theorem B390137 : Blo 259821 390137 := bstep (se 2 (by rfl) ⟨146301, by rfl⟩ : syracuseStep 390137 = 292603) B292603
theorem B586745 : Blo 259821 586745 := bstep (se 2 (by rfl) ⟨220029, by rfl⟩ : syracuseStep 586745 = 440059) B440059
theorem B881657 : Blo 259821 881657 := bstep (se 2 (by rfl) ⟨330621, by rfl⟩ : syracuseStep 881657 = 661243) B661243
theorem B390185 : Blo 259821 390185 := bstep (se 2 (by rfl) ⟨146319, by rfl⟩ : syracuseStep 390185 = 292639) B292639
theorem B390215 : Blo 259821 390215 := bstep (se 1 (by rfl) ⟨292661, by rfl⟩ : syracuseStep 390215 = 585323) B585323
theorem B586835 : Blo 259821 586835 := bstep (se 1 (by rfl) ⟨440126, by rfl⟩ : syracuseStep 586835 = 880253) B880253
theorem B390395 : Blo 259821 390395 := bstep (se 1 (by rfl) ⟨292796, by rfl⟩ : syracuseStep 390395 = 585593) B585593
theorem B587015 : Blo 259821 587015 := bstep (se 1 (by rfl) ⟨440261, by rfl⟩ : syracuseStep 587015 = 880523) B880523
theorem B881927 : Blo 259821 881927 := bstep (se 1 (by rfl) ⟨661445, by rfl⟩ : syracuseStep 881927 = 1322891) B1322891
theorem B488767 : Blo 259821 488767 := bstep (se 1 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 488767 = 733151) B733151
theorem B587375 : Blo 259821 587375 := bstep (se 1 (by rfl) ⟨440531, by rfl⟩ : syracuseStep 587375 = 881063) B881063
theorem B259823 : Blo 259821 259823 := bstep (se 1 (by rfl) ⟨194867, by rfl⟩ : syracuseStep 259823 = 389735) B389735
theorem B259911 : Blo 259821 259911 := bstep (se 1 (by rfl) ⟨194933, by rfl⟩ : syracuseStep 259911 = 389867) B389867
theorem B259931 : Blo 259821 259931 := bstep (se 1 (by rfl) ⟨194948, by rfl⟩ : syracuseStep 259931 = 389897) B389897
theorem B259999 : Blo 259821 259999 := bstep (se 1 (by rfl) ⟨194999, by rfl⟩ : syracuseStep 259999 = 389999) B389999
theorem B7698341 : Blo 259821 7698341 := bstep (se 4 (by rfl) ⟨721719, by rfl⟩ : syracuseStep 7698341 = 1443439) B1443439
theorem B2127815 : Blo 259821 2127815 := bstep (se 1 (by rfl) ⟨1595861, by rfl⟩ : syracuseStep 2127815 = 3191723) B3191723
theorem B260167 : Blo 259821 260167 := bstep (se 1 (by rfl) ⟨195125, by rfl⟩ : syracuseStep 260167 = 390251) B390251
theorem B555191 : Blo 259821 555191 := bstep (se 1 (by rfl) ⟨416393, by rfl⟩ : syracuseStep 555191 = 832787) B832787
theorem B882899 : Blo 259821 882899 := bstep (se 1 (by rfl) ⟨662174, by rfl⟩ : syracuseStep 882899 = 1324349) B1324349
theorem B260327 : Blo 259821 260327 := bstep (se 1 (by rfl) ⟨195245, by rfl⟩ : syracuseStep 260327 = 390491) B390491
theorem B555311 : Blo 259821 555311 := bstep (se 1 (by rfl) ⟨416483, by rfl⟩ : syracuseStep 555311 = 832967) B832967
theorem B260511 : Blo 259821 260511 := bstep (se 1 (by rfl) ⟨195383, by rfl⟩ : syracuseStep 260511 = 390767) B390767
theorem B1669571 : Blo 259821 1669571 := bstep (se 1 (by rfl) ⟨1252178, by rfl⟩ : syracuseStep 1669571 = 2504357) B2504357
theorem B260559 : Blo 259821 260559 := bstep (se 1 (by rfl) ⟨195419, by rfl⟩ : syracuseStep 260559 = 390839) B390839
theorem B391631 : Blo 259821 391631 := bstep (se 1 (by rfl) ⟨293723, by rfl⟩ : syracuseStep 391631 = 587447) B587447
theorem B588239 : Blo 259821 588239 := bstep (se 1 (by rfl) ⟨441179, by rfl⟩ : syracuseStep 588239 = 882359) B882359
theorem B883169 : Blo 259821 883169 := bstep (se 2 (by rfl) ⟨331188, by rfl⟩ : syracuseStep 883169 = 662377) B662377
theorem B260583 : Blo 259821 260583 := bstep (se 1 (by rfl) ⟨195437, by rfl⟩ : syracuseStep 260583 = 390875) B390875
theorem B1669673 : Blo 259821 1669673 := bstep (se 2 (by rfl) ⟨626127, by rfl⟩ : syracuseStep 1669673 = 1252255) B1252255
theorem B391721 : Blo 259821 391721 := bstep (se 2 (by rfl) ⟨146895, by rfl⟩ : syracuseStep 391721 = 293791) B293791
theorem B588329 : Blo 259821 588329 := bstep (se 2 (by rfl) ⟨220623, by rfl⟩ : syracuseStep 588329 = 441247) B441247
theorem B260699 : Blo 259821 260699 := bstep (se 1 (by rfl) ⟨195524, by rfl⟩ : syracuseStep 260699 = 391049) B391049
theorem B293467 : Blo 259821 293467 := bstep (se 1 (by rfl) ⟨220100, by rfl⟩ : syracuseStep 293467 = 440201) B440201
theorem B1997459 : Blo 259821 1997459 := bstep (se 1 (by rfl) ⟨1498094, by rfl⟩ : syracuseStep 1997459 = 2996189) B2996189
theorem B260767 : Blo 259821 260767 := bstep (se 1 (by rfl) ⟨195575, by rfl⟩ : syracuseStep 260767 = 391151) B391151
theorem B391913 : Blo 259821 391913 := bstep (se 2 (by rfl) ⟨146967, by rfl⟩ : syracuseStep 391913 = 293935) B293935
theorem B260935 : Blo 259821 260935 := bstep (se 1 (by rfl) ⟨195701, by rfl⟩ : syracuseStep 260935 = 391403) B391403
theorem B260975 : Blo 259821 260975 := bstep (se 1 (by rfl) ⟨195731, by rfl⟩ : syracuseStep 260975 = 391463) B391463
theorem B293755 : Blo 259821 293755 := bstep (se 1 (by rfl) ⟨220316, by rfl⟩ : syracuseStep 293755 = 440633) B440633
theorem B555943 : Blo 259821 555943 := bstep (se 1 (by rfl) ⟨416957, by rfl⟩ : syracuseStep 555943 = 833915) B833915
theorem B261031 : Blo 259821 261031 := bstep (se 1 (by rfl) ⟨195773, by rfl⟩ : syracuseStep 261031 = 391547) B391547
theorem B3177461 : Blo 259821 3177461 := bstep (se 5 (by rfl) ⟨148943, by rfl⟩ : syracuseStep 3177461 = 297887) B297887
theorem B2030629 : Blo 259821 2030629 := bstep (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) B380743
theorem B261211 : Blo 259821 261211 := bstep (se 1 (by rfl) ⟨195908, by rfl⟩ : syracuseStep 261211 = 391817) B391817
theorem B392297 : Blo 259821 392297 := bstep (se 2 (by rfl) ⟨147111, by rfl⟩ : syracuseStep 392297 = 294223) B294223
theorem B588905 : Blo 259821 588905 := bstep (se 2 (by rfl) ⟨220839, by rfl⟩ : syracuseStep 588905 = 441679) B441679
theorem B261327 : Blo 259821 261327 := bstep (se 1 (by rfl) ⟨195995, by rfl⟩ : syracuseStep 261327 = 391991) B391991
theorem B261351 : Blo 259821 261351 := bstep (se 1 (by rfl) ⟨196013, by rfl⟩ : syracuseStep 261351 = 392027) B392027
theorem B392423 : Blo 259821 392423 := bstep (se 1 (by rfl) ⟨294317, by rfl⟩ : syracuseStep 392423 = 588635) B588635
theorem B589031 : Blo 259821 589031 := bstep (se 1 (by rfl) ⟨441773, by rfl⟩ : syracuseStep 589031 = 883547) B883547
theorem B2227459 : Blo 259821 2227459 := bstep (se 1 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 2227459 = 3341189) B3341189
theorem B261447 : Blo 259821 261447 := bstep (se 1 (by rfl) ⟨196085, by rfl⟩ : syracuseStep 261447 = 392171) B392171
theorem B1703263 : Blo 259821 1703263 := bstep (se 1 (by rfl) ⟨1277447, by rfl⟩ : syracuseStep 1703263 = 2554895) B2554895
theorem B2522501 : Blo 259821 2522501 := bstep (se 4 (by rfl) ⟨236484, by rfl⟩ : syracuseStep 2522501 = 472969) B472969
theorem B261583 : Blo 259821 261583 := bstep (se 1 (by rfl) ⟨196187, by rfl⟩ : syracuseStep 261583 = 392375) B392375
theorem B261743 : Blo 259821 261743 := bstep (se 1 (by rfl) ⟨196307, by rfl⟩ : syracuseStep 261743 = 392615) B392615
theorem B294511 : Blo 259821 294511 := bstep (se 1 (by rfl) ⟨220883, by rfl⟩ : syracuseStep 294511 = 441767) B441767
theorem B851609 : Blo 259821 851609 := bstep (se 2 (by rfl) ⟨319353, by rfl⟩ : syracuseStep 851609 = 638707) B638707
theorem B261799 : Blo 259821 261799 := bstep (se 1 (by rfl) ⟨196349, by rfl⟩ : syracuseStep 261799 = 392699) B392699
theorem B294619 : Blo 259821 294619 := bstep (se 1 (by rfl) ⟨220964, by rfl⟩ : syracuseStep 294619 = 441929) B441929
theorem B392927 : Blo 259821 392927 := bstep (se 1 (by rfl) ⟨294695, by rfl⟩ : syracuseStep 392927 = 589391) B589391
theorem B589535 : Blo 259821 589535 := bstep (se 1 (by rfl) ⟨442151, by rfl⟩ : syracuseStep 589535 = 884303) B884303
theorem B261863 : Blo 259821 261863 := bstep (se 1 (by rfl) ⟨196397, by rfl⟩ : syracuseStep 261863 = 392795) B392795
theorem B2981609 : Blo 259821 2981609 := bstep (se 2 (by rfl) ⟨1118103, by rfl⟩ : syracuseStep 2981609 = 2236207) B2236207
theorem B392969 : Blo 259821 392969 := bstep (se 2 (by rfl) ⟨147363, by rfl⟩ : syracuseStep 392969 = 294727) B294727
theorem B261919 : Blo 259821 261919 := bstep (se 1 (by rfl) ⟨196439, by rfl⟩ : syracuseStep 261919 = 392879) B392879
theorem B589607 : Blo 259821 589607 := bstep (se 1 (by rfl) ⟨442205, by rfl⟩ : syracuseStep 589607 = 884411) B884411
theorem B884519 : Blo 259821 884519 := bstep (se 1 (by rfl) ⟨663389, by rfl⟩ : syracuseStep 884519 = 1326779) B1326779
theorem B851791 : Blo 259821 851791 := bstep (se 1 (by rfl) ⟨638843, by rfl⟩ : syracuseStep 851791 = 1277687) B1277687
theorem B261999 : Blo 259821 261999 := bstep (se 1 (by rfl) ⟨196499, by rfl⟩ : syracuseStep 261999 = 392999) B392999
theorem B2129789 : Blo 259821 2129789 := bstep (se 3 (by rfl) ⟨399335, by rfl⟩ : syracuseStep 2129789 = 798671) B798671
theorem B262055 : Blo 259821 262055 := bstep (se 1 (by rfl) ⟨196541, by rfl⟩ : syracuseStep 262055 = 393083) B393083
theorem B14516281 : Blo 259821 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B262271 : Blo 259821 262271 := bstep (se 1 (by rfl) ⟨196703, by rfl⟩ : syracuseStep 262271 = 393407) B393407
theorem B1671313 : Blo 259821 1671313 := bstep (se 2 (by rfl) ⟨626742, by rfl⟩ : syracuseStep 1671313 = 1253485) B1253485
theorem B721151 : Blo 259821 721151 := bstep (se 1 (by rfl) ⟨540863, by rfl⟩ : syracuseStep 721151 = 1081727) B1081727
theorem B262555 : Blo 259821 262555 := bstep (se 1 (by rfl) ⟨196916, by rfl⟩ : syracuseStep 262555 = 393833) B393833
theorem B262559 : Blo 259821 262559 := bstep (se 1 (by rfl) ⟨196919, by rfl⟩ : syracuseStep 262559 = 393839) B393839
theorem B393755 : Blo 259821 393755 := bstep (se 1 (by rfl) ⟨295316, by rfl⟩ : syracuseStep 393755 = 590633) B590633
theorem B393935 : Blo 259821 393935 := bstep (se 1 (by rfl) ⟨295451, by rfl⟩ : syracuseStep 393935 = 590903) B590903
theorem B262975 : Blo 259821 262975 := bstep (se 1 (by rfl) ⟨197231, by rfl⟩ : syracuseStep 262975 = 394463) B394463
theorem B394055 : Blo 259821 394055 := bstep (se 1 (by rfl) ⟨295541, by rfl⟩ : syracuseStep 394055 = 591083) B591083
theorem B262983 : Blo 259821 262983 := bstep (se 1 (by rfl) ⟨197237, by rfl⟩ : syracuseStep 262983 = 394475) B394475
theorem B394121 : Blo 259821 394121 := bstep (se 2 (by rfl) ⟨147795, by rfl⟩ : syracuseStep 394121 = 295591) B295591
theorem B12059603 : Blo 259821 12059603 := bstep (se 1 (by rfl) ⟨9044702, by rfl⟩ : syracuseStep 12059603 = 18089405) B18089405
theorem B263239 : Blo 259821 263239 := bstep (se 1 (by rfl) ⟨197429, by rfl⟩ : syracuseStep 263239 = 394859) B394859
theorem B590975 : Blo 259821 590975 := bstep (se 1 (by rfl) ⟨443231, by rfl⟩ : syracuseStep 590975 = 886463) B886463
theorem B394367 : Blo 259821 394367 := bstep (se 1 (by rfl) ⟨295775, by rfl⟩ : syracuseStep 394367 = 591551) B591551
theorem B263295 : Blo 259821 263295 := bstep (se 1 (by rfl) ⟨197471, by rfl⟩ : syracuseStep 263295 = 394943) B394943
theorem B263419 : Blo 259821 263419 := bstep (se 1 (by rfl) ⟨197564, by rfl⟩ : syracuseStep 263419 = 395129) B395129
theorem B394505 : Blo 259821 394505 := bstep (se 2 (by rfl) ⟨147939, by rfl⟩ : syracuseStep 394505 = 295879) B295879
theorem B394985 : Blo 259821 394985 := bstep (se 2 (by rfl) ⟨148119, by rfl⟩ : syracuseStep 394985 = 296239) B296239
theorem B394991 : Blo 259821 394991 := bstep (se 1 (by rfl) ⟨296243, by rfl⟩ : syracuseStep 394991 = 592487) B592487
theorem B558839 : Blo 259821 558839 := bstep (se 1 (by rfl) ⟨419129, by rfl⟩ : syracuseStep 558839 = 838259) B838259
theorem B395243 : Blo 259821 395243 := bstep (se 1 (by rfl) ⟨296432, by rfl⟩ : syracuseStep 395243 = 592865) B592865
theorem B395495 : Blo 259821 395495 := bstep (se 1 (by rfl) ⟨296621, by rfl⟩ : syracuseStep 395495 = 593243) B593243
theorem B592127 : Blo 259821 592127 := bstep (se 1 (by rfl) ⟨444095, by rfl⟩ : syracuseStep 592127 = 888191) B888191
theorem B395519 : Blo 259821 395519 := bstep (se 1 (by rfl) ⟨296639, by rfl⟩ : syracuseStep 395519 = 593279) B593279
theorem B395657 : Blo 259821 395657 := bstep (se 2 (by rfl) ⟨148371, by rfl⟩ : syracuseStep 395657 = 296743) B296743
theorem B2525849 : Blo 259821 2525849 := bstep (se 2 (by rfl) ⟨947193, by rfl⟩ : syracuseStep 2525849 = 1894387) B1894387
theorem B854687 : Blo 259821 854687 := bstep (se 1 (by rfl) ⟨641015, by rfl⟩ : syracuseStep 854687 = 1282031) B1282031
theorem B1117147 : Blo 259821 1117147 := bstep (se 1 (by rfl) ⟨837860, by rfl⟩ : syracuseStep 1117147 = 1675721) B1675721
theorem B887867 : Blo 259821 887867 := bstep (se 1 (by rfl) ⟨665900, by rfl⟩ : syracuseStep 887867 = 1331801) B1331801
theorem B658601 : Blo 259821 658601 := bstep (se 2 (by rfl) ⟨246975, by rfl⟩ : syracuseStep 658601 = 493951) B493951
theorem B1674877 : Blo 259821 1674877 := bstep (se 3 (by rfl) ⟨314039, by rfl⟩ : syracuseStep 1674877 = 628079) B628079
theorem B21630797 : Blo 259821 21630797 := bstep (se 3 (by rfl) ⟨4055774, by rfl⟩ : syracuseStep 21630797 = 8111549) B8111549
theorem B331867 : Blo 259821 331867 := bstep (se 1 (by rfl) ⟨248900, by rfl⟩ : syracuseStep 331867 = 497801) B497801
theorem B889757 : Blo 259821 889757 := bstep (se 3 (by rfl) ⟨166829, by rfl⟩ : syracuseStep 889757 = 333659) B333659
theorem B660575 : Blo 259821 660575 := bstep (se 1 (by rfl) ⟨495431, by rfl⟩ : syracuseStep 660575 = 990863) B990863
theorem B300223 : Blo 259821 300223 := bstep (se 1 (by rfl) ⟨225167, by rfl⟩ : syracuseStep 300223 = 450335) B450335
theorem B792031 : Blo 259821 792031 := bstep (se 1 (by rfl) ⟨594023, by rfl⟩ : syracuseStep 792031 = 1188047) B1188047
theorem B1119865 : Blo 259821 1119865 := bstep (se 2 (by rfl) ⟨419949, by rfl⟩ : syracuseStep 1119865 = 839899) B839899
theorem B2005235 : Blo 259821 2005235 := bstep (se 1 (by rfl) ⟨1503926, by rfl⟩ : syracuseStep 2005235 = 3007853) B3007853
theorem B1677671 : Blo 259821 1677671 := bstep (se 1 (by rfl) ⟨1258253, by rfl⟩ : syracuseStep 1677671 = 2516507) B2516507
theorem B498089 : Blo 259821 498089 := bstep (se 2 (by rfl) ⟨186783, by rfl⟩ : syracuseStep 498089 = 373567) B373567
theorem B8460773 : Blo 259821 8460773 := bstep (se 4 (by rfl) ⟨793197, by rfl⟩ : syracuseStep 8460773 = 1586395) B1586395
theorem B663511 : Blo 259821 663511 := bstep (se 1 (by rfl) ⟨497633, by rfl⟩ : syracuseStep 663511 = 995267) B995267
theorem B1024427 : Blo 259821 1024427 := bstep (se 1 (by rfl) ⟨768320, by rfl⟩ : syracuseStep 1024427 = 1536641) B1536641
theorem B6365627 : Blo 259821 6365627 := bstep (se 1 (by rfl) ⟨4774220, by rfl⟩ : syracuseStep 6365627 = 9548441) B9548441
theorem B4006567 : Blo 259821 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B664271 : Blo 259821 664271 := bstep (se 1 (by rfl) ⟨498203, by rfl⟩ : syracuseStep 664271 = 996407) B996407
theorem B1057693 : Blo 259821 1057693 := bstep (se 3 (by rfl) ⟨198317, by rfl⟩ : syracuseStep 1057693 = 396635) B396635
theorem B992351 : Blo 259821 992351 := bstep (se 1 (by rfl) ⟨744263, by rfl⟩ : syracuseStep 992351 = 1488527) B1488527
theorem B23438585 : Blo 259821 23438585 := bstep (se 2 (by rfl) ⟨8789469, by rfl⟩ : syracuseStep 23438585 = 17578939) B17578939
theorem B1418543 : Blo 259821 1418543 := bstep (se 1 (by rfl) ⟨1063907, by rfl⟩ : syracuseStep 1418543 = 2127815) B2127815
theorem B370127 : Blo 259821 370127 := bstep (se 1 (by rfl) ⟨277595, by rfl⟩ : syracuseStep 370127 = 555191) B555191
theorem B370207 : Blo 259821 370207 := bstep (se 1 (by rfl) ⟨277655, by rfl⟩ : syracuseStep 370207 = 555311) B555311
theorem B2271017 : Blo 259821 2271017 := bstep (se 2 (by rfl) ⟨851631, by rfl⟩ : syracuseStep 2271017 = 1703263) B1703263
theorem B2828125 : Blo 259821 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B1124513 : Blo 259821 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B1681667 : Blo 259821 1681667 := bstep (se 1 (by rfl) ⟨1261250, by rfl⟩ : syracuseStep 1681667 = 2522501) B2522501
theorem B1321271 : Blo 259821 1321271 := bstep (se 1 (by rfl) ⟨990953, by rfl⟩ : syracuseStep 1321271 = 1981907) B1981907
theorem B567739 : Blo 259821 567739 := bstep (se 1 (by rfl) ⟨425804, by rfl⟩ : syracuseStep 567739 = 851609) B851609
theorem B1419859 : Blo 259821 1419859 := bstep (se 1 (by rfl) ⟨1064894, by rfl⟩ : syracuseStep 1419859 = 2129789) B2129789
theorem B666731 : Blo 259821 666731 := bstep (se 1 (by rfl) ⟨500048, by rfl⟩ : syracuseStep 666731 = 1000097) B1000097
theorem B1977533 : Blo 259821 1977533 := bstep (se 3 (by rfl) ⟨370787, by rfl⟩ : syracuseStep 1977533 = 741575) B741575
theorem B1322729 : Blo 259821 1322729 := bstep (se 2 (by rfl) ⟨496023, by rfl⟩ : syracuseStep 1322729 = 992047) B992047
theorem B667379 : Blo 259821 667379 := bstep (se 1 (by rfl) ⟨500534, by rfl⟩ : syracuseStep 667379 = 1001069) B1001069
theorem B438527 : Blo 259821 438527 := bstep (se 1 (by rfl) ⟨328895, by rfl⟩ : syracuseStep 438527 = 657791) B657791
theorem B15217145 : Blo 259821 15217145 := bstep (se 2 (by rfl) ⟨5706429, by rfl⟩ : syracuseStep 15217145 = 11412859) B11412859
theorem B2700611 : Blo 259821 2700611 := bstep (se 1 (by rfl) ⟨2025458, by rfl⟩ : syracuseStep 2700611 = 4050917) B4050917
theorem B1521127 : Blo 259821 1521127 := bstep (se 1 (by rfl) ⟨1140845, by rfl⟩ : syracuseStep 1521127 = 2281691) B2281691
theorem B4994561 : Blo 259821 4994561 := bstep (se 2 (by rfl) ⟨1872960, by rfl⟩ : syracuseStep 4994561 = 3745921) B3745921
theorem B3356315 : Blo 259821 3356315 := bstep (se 1 (by rfl) ⟨2517236, by rfl⟩ : syracuseStep 3356315 = 5034473) B5034473
theorem B997181 : Blo 259821 997181 := bstep (se 3 (by rfl) ⟨186971, by rfl⟩ : syracuseStep 997181 = 373943) B373943
theorem B440255 : Blo 259821 440255 := bstep (se 1 (by rfl) ⟨330191, by rfl⟩ : syracuseStep 440255 = 660383) B660383
theorem B1259867 : Blo 259821 1259867 := bstep (se 1 (by rfl) ⟨944900, by rfl⟩ : syracuseStep 1259867 = 1889801) B1889801
theorem B4864367 : Blo 259821 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B1981421 : Blo 259821 1981421 := bstep (se 3 (by rfl) ⟨371516, by rfl⟩ : syracuseStep 1981421 = 743033) B743033
theorem B4602905 : Blo 259821 4602905 := bstep (se 2 (by rfl) ⟨1726089, by rfl⟩ : syracuseStep 4602905 = 3452179) B3452179
theorem B69483835 : Blo 259821 69483835 := bstep (se 1 (by rfl) ⟨52112876, by rfl⟩ : syracuseStep 69483835 = 104225753) B104225753
theorem B835247 : Blo 259821 835247 := bstep (se 1 (by rfl) ⟨626435, by rfl⟩ : syracuseStep 835247 = 1252871) B1252871
theorem B20528909 : Blo 259821 20528909 := bstep (se 3 (by rfl) ⟨3849170, by rfl⟩ : syracuseStep 20528909 = 7698341) B7698341
theorem B442361 : Blo 259821 442361 := bstep (se 2 (by rfl) ⟨165885, by rfl⟩ : syracuseStep 442361 = 331771) B331771
theorem B2965571 : Blo 259821 2965571 := bstep (se 1 (by rfl) ⟨2224178, by rfl⟩ : syracuseStep 2965571 = 4448357) B4448357
theorem B442631 : Blo 259821 442631 := bstep (se 1 (by rfl) ⟨331973, by rfl⟩ : syracuseStep 442631 = 663947) B663947
theorem B1687817 : Blo 259821 1687817 := bstep (se 2 (by rfl) ⟨632931, by rfl⟩ : syracuseStep 1687817 = 1265863) B1265863
theorem B1491443 : Blo 259821 1491443 := bstep (se 1 (by rfl) ⟨1118582, by rfl⟩ : syracuseStep 1491443 = 2237165) B2237165
theorem B901625 : Blo 259821 901625 := bstep (se 2 (by rfl) ⟨338109, by rfl⟩ : syracuseStep 901625 = 676219) B676219
theorem B4113139 : Blo 259821 4113139 := bstep (se 1 (by rfl) ⟨3084854, by rfl⟩ : syracuseStep 4113139 = 6169709) B6169709
theorem B836477 : Blo 259821 836477 := bstep (se 3 (by rfl) ⟨156839, by rfl⟩ : syracuseStep 836477 = 313679) B313679
theorem B1983365 : Blo 259821 1983365 := bstep (se 4 (by rfl) ⟨185940, by rfl⟩ : syracuseStep 1983365 = 371881) B371881
theorem B2245913 : Blo 259821 2245913 := bstep (se 2 (by rfl) ⟨842217, by rfl⟩ : syracuseStep 2245913 = 1684435) B1684435
theorem B443711 : Blo 259821 443711 := bstep (se 1 (by rfl) ⟨332783, by rfl⟩ : syracuseStep 443711 = 665567) B665567
theorem B1984823 : Blo 259821 1984823 := bstep (se 1 (by rfl) ⟨1488617, by rfl⟩ : syracuseStep 1984823 = 2977235) B2977235
theorem B1330343 : Blo 259821 1330343 := bstep (se 1 (by rfl) ⟨997757, by rfl⟩ : syracuseStep 1330343 = 1995515) B1995515
theorem B2018533 : Blo 259821 2018533 := bstep (se 4 (by rfl) ⟨189237, by rfl⟩ : syracuseStep 2018533 = 378475) B378475
theorem B1494359 : Blo 259821 1494359 := bstep (se 1 (by rfl) ⟨1120769, by rfl⟩ : syracuseStep 1494359 = 2241539) B2241539
theorem B937865 : Blo 259821 937865 := bstep (se 2 (by rfl) ⟨351699, by rfl⟩ : syracuseStep 937865 = 703399) B703399
theorem B741257 : Blo 259821 741257 := bstep (se 2 (by rfl) ⟨277971, by rfl⟩ : syracuseStep 741257 = 555943) B555943
theorem B2707505 : Blo 259821 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B2969945 : Blo 259821 2969945 := bstep (se 2 (by rfl) ⟨1113729, by rfl⟩ : syracuseStep 2969945 = 2227459) B2227459
theorem B1331639 : Blo 259821 1331639 := bstep (se 1 (by rfl) ⟨998729, by rfl⟩ : syracuseStep 1331639 = 1997459) B1997459
theorem B938429 : Blo 259821 938429 := bstep (se 3 (by rfl) ⟨175955, by rfl⟩ : syracuseStep 938429 = 351911) B351911
theorem B2118307 : Blo 259821 2118307 := bstep (se 1 (by rfl) ⟨1588730, by rfl⟩ : syracuseStep 2118307 = 3177461) B3177461
theorem B11326337 : Blo 259821 11326337 := bstep (se 2 (by rfl) ⟨4247376, by rfl⟩ : syracuseStep 11326337 = 8494753) B8494753
theorem B1135721 : Blo 259821 1135721 := bstep (se 2 (by rfl) ⟨425895, by rfl⟩ : syracuseStep 1135721 = 851791) B851791
theorem B1987739 : Blo 259821 1987739 := bstep (se 1 (by rfl) ⟨1490804, by rfl⟩ : syracuseStep 1987739 = 2981609) B2981609
theorem B1496819 : Blo 259821 1496819 := bstep (se 1 (by rfl) ⟨1122614, by rfl⟩ : syracuseStep 1496819 = 2245229) B2245229
theorem B23615621 : Blo 259821 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B2251313 : Blo 259821 2251313 := bstep (se 2 (by rfl) ⟨844242, by rfl⟩ : syracuseStep 2251313 = 1688485) B1688485
theorem B810209 : Blo 259821 810209 := bstep (se 2 (by rfl) ⟨303828, by rfl⟩ : syracuseStep 810209 = 607657) B607657
theorem B1498459 : Blo 259821 1498459 := bstep (se 1 (by rfl) ⟨1123844, by rfl⟩ : syracuseStep 1498459 = 2247689) B2247689
theorem B4218313 : Blo 259821 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B1498733 : Blo 259821 1498733 := bstep (se 3 (by rfl) ⟨281012, by rfl⟩ : syracuseStep 1498733 = 562025) B562025
theorem B9690841 : Blo 259821 9690841 := bstep (se 2 (by rfl) ⟨3634065, by rfl⟩ : syracuseStep 9690841 = 7268131) B7268131
theorem B844627 : Blo 259821 844627 := bstep (se 1 (by rfl) ⟨633470, by rfl⟩ : syracuseStep 844627 = 1266941) B1266941
theorem B747431 : Blo 259821 747431 := bstep (se 1 (by rfl) ⟨560573, by rfl⟩ : syracuseStep 747431 = 1121147) B1121147
theorem B1501193 : Blo 259821 1501193 := bstep (se 2 (by rfl) ⟨562947, by rfl⟩ : syracuseStep 1501193 = 1125895) B1125895
theorem B2975777 : Blo 259821 2975777 := bstep (se 2 (by rfl) ⟨1115916, by rfl⟩ : syracuseStep 2975777 = 2231833) B2231833
theorem B1501375 : Blo 259821 1501375 := bstep (se 1 (by rfl) ⟨1126031, by rfl⟩ : syracuseStep 1501375 = 2252063) B2252063
theorem B945017 : Blo 259821 945017 := bstep (se 2 (by rfl) ⟨354381, by rfl⟩ : syracuseStep 945017 = 708763) B708763
theorem B748615 : Blo 259821 748615 := bstep (se 1 (by rfl) ⟨561461, by rfl⟩ : syracuseStep 748615 = 1122923) B1122923
theorem B5139571 : Blo 259821 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B748673 : Blo 259821 748673 := bstep (se 2 (by rfl) ⟨280752, by rfl⟩ : syracuseStep 748673 = 561505) B561505
theorem B585719 : Blo 259821 585719 := bstep (se 1 (by rfl) ⟨439289, by rfl⟩ : syracuseStep 585719 = 878579) B878579
theorem B586079 : Blo 259821 586079 := bstep (se 1 (by rfl) ⟨439559, by rfl⟩ : syracuseStep 586079 = 879119) B879119
theorem B1929635 : Blo 259821 1929635 := bstep (se 1 (by rfl) ⟨1447226, by rfl⟩ : syracuseStep 1929635 = 2894453) B2894453
theorem B651689 : Blo 259821 651689 := bstep (se 2 (by rfl) ⟨244383, by rfl⟩ : syracuseStep 651689 = 488767) B488767
theorem B389915 : Blo 259821 389915 := bstep (se 1 (by rfl) ⟨292436, by rfl⟩ : syracuseStep 389915 = 584873) B584873
theorem B586601 : Blo 259821 586601 := bstep (se 2 (by rfl) ⟨219975, by rfl⟩ : syracuseStep 586601 = 439951) B439951
theorem B2978693 : Blo 259821 2978693 := bstep (se 4 (by rfl) ⟨279252, by rfl⟩ : syracuseStep 2978693 = 558505) B558505
theorem B390191 : Blo 259821 390191 := bstep (se 1 (by rfl) ⟨292643, by rfl⟩ : syracuseStep 390191 = 585287) B585287
theorem B586799 : Blo 259821 586799 := bstep (se 1 (by rfl) ⟨440099, by rfl⟩ : syracuseStep 586799 = 880199) B880199
theorem B390239 : Blo 259821 390239 := bstep (se 1 (by rfl) ⟨292679, by rfl⟩ : syracuseStep 390239 = 585359) B585359
theorem B390299 : Blo 259821 390299 := bstep (se 1 (by rfl) ⟨292724, by rfl⟩ : syracuseStep 390299 = 585449) B585449
theorem B390311 : Blo 259821 390311 := bstep (se 1 (by rfl) ⟨292733, by rfl⟩ : syracuseStep 390311 = 585467) B585467
theorem B15332647 : Blo 259821 15332647 := bstep (se 1 (by rfl) ⟨11499485, by rfl⟩ : syracuseStep 15332647 = 22998971) B22998971
theorem B390983 : Blo 259821 390983 := bstep (se 1 (by rfl) ⟨293237, by rfl⟩ : syracuseStep 390983 = 586475) B586475
theorem B587591 : Blo 259821 587591 := bstep (se 1 (by rfl) ⟨440693, by rfl⟩ : syracuseStep 587591 = 881387) B881387
theorem B259967 : Blo 259821 259967 := bstep (se 1 (by rfl) ⟨194975, by rfl⟩ : syracuseStep 259967 = 389951) B389951
theorem B260063 : Blo 259821 260063 := bstep (se 1 (by rfl) ⟨195047, by rfl⟩ : syracuseStep 260063 = 390095) B390095
theorem B260091 : Blo 259821 260091 := bstep (se 1 (by rfl) ⟨195068, by rfl⟩ : syracuseStep 260091 = 390137) B390137
theorem B391163 : Blo 259821 391163 := bstep (se 1 (by rfl) ⟨293372, by rfl⟩ : syracuseStep 391163 = 586745) B586745
theorem B587771 : Blo 259821 587771 := bstep (se 1 (by rfl) ⟨440828, by rfl⟩ : syracuseStep 587771 = 881657) B881657
theorem B260123 : Blo 259821 260123 := bstep (se 1 (by rfl) ⟨195092, by rfl⟩ : syracuseStep 260123 = 390185) B390185
theorem B292891 : Blo 259821 292891 := bstep (se 1 (by rfl) ⟨219668, by rfl⟩ : syracuseStep 292891 = 439337) B439337
theorem B260143 : Blo 259821 260143 := bstep (se 1 (by rfl) ⟨195107, by rfl⟩ : syracuseStep 260143 = 390215) B390215
theorem B391223 : Blo 259821 391223 := bstep (se 1 (by rfl) ⟨293417, by rfl⟩ : syracuseStep 391223 = 586835) B586835
theorem B391289 : Blo 259821 391289 := bstep (se 2 (by rfl) ⟨146733, by rfl⟩ : syracuseStep 391289 = 293467) B293467
theorem B587897 : Blo 259821 587897 := bstep (se 2 (by rfl) ⟨220461, by rfl⟩ : syracuseStep 587897 = 440923) B440923
theorem B260263 : Blo 259821 260263 := bstep (se 1 (by rfl) ⟨195197, by rfl⟩ : syracuseStep 260263 = 390395) B390395
theorem B391343 : Blo 259821 391343 := bstep (se 1 (by rfl) ⟨293507, by rfl⟩ : syracuseStep 391343 = 587015) B587015
theorem B587951 : Blo 259821 587951 := bstep (se 1 (by rfl) ⟨440963, by rfl⟩ : syracuseStep 587951 = 881927) B881927
theorem B48953621 : Blo 259821 48953621 := bstep (se 6 (by rfl) ⟨1147350, by rfl⟩ : syracuseStep 48953621 = 2294701) B2294701
theorem B391583 : Blo 259821 391583 := bstep (se 1 (by rfl) ⟨293687, by rfl⟩ : syracuseStep 391583 = 587375) B587375
theorem B391673 : Blo 259821 391673 := bstep (se 2 (by rfl) ⟨146877, by rfl⟩ : syracuseStep 391673 = 293755) B293755
theorem B5896709 : Blo 259821 5896709 := bstep (se 4 (by rfl) ⟨552816, by rfl⟩ : syracuseStep 5896709 = 1105633) B1105633
theorem B588599 : Blo 259821 588599 := bstep (se 1 (by rfl) ⟨441449, by rfl⟩ : syracuseStep 588599 = 882899) B882899
theorem B1113047 : Blo 259821 1113047 := bstep (se 1 (by rfl) ⟨834785, by rfl⟩ : syracuseStep 1113047 = 1669571) B1669571
theorem B261087 : Blo 259821 261087 := bstep (se 1 (by rfl) ⟨195815, by rfl⟩ : syracuseStep 261087 = 391631) B391631
theorem B392159 : Blo 259821 392159 := bstep (se 1 (by rfl) ⟨294119, by rfl⟩ : syracuseStep 392159 = 588239) B588239
theorem B588779 : Blo 259821 588779 := bstep (se 1 (by rfl) ⟨441584, by rfl⟩ : syracuseStep 588779 = 883169) B883169
theorem B1113115 : Blo 259821 1113115 := bstep (se 1 (by rfl) ⟨834836, by rfl⟩ : syracuseStep 1113115 = 1669673) B1669673
theorem B261147 : Blo 259821 261147 := bstep (se 1 (by rfl) ⟨195860, by rfl⟩ : syracuseStep 261147 = 391721) B391721
theorem B392219 : Blo 259821 392219 := bstep (se 1 (by rfl) ⟨294164, by rfl⟩ : syracuseStep 392219 = 588329) B588329
theorem B261275 : Blo 259821 261275 := bstep (se 1 (by rfl) ⟨195956, by rfl⟩ : syracuseStep 261275 = 391913) B391913
theorem B294043 : Blo 259821 294043 := bstep (se 1 (by rfl) ⟨220532, by rfl⟩ : syracuseStep 294043 = 441065) B441065
theorem B261531 : Blo 259821 261531 := bstep (se 1 (by rfl) ⟨196148, by rfl⟩ : syracuseStep 261531 = 392297) B392297
theorem B392603 : Blo 259821 392603 := bstep (se 1 (by rfl) ⟨294452, by rfl⟩ : syracuseStep 392603 = 588905) B588905
theorem B392681 : Blo 259821 392681 := bstep (se 2 (by rfl) ⟨147255, by rfl⟩ : syracuseStep 392681 = 294511) B294511
theorem B261615 : Blo 259821 261615 := bstep (se 1 (by rfl) ⟨196211, by rfl⟩ : syracuseStep 261615 = 392423) B392423
theorem B392687 : Blo 259821 392687 := bstep (se 1 (by rfl) ⟨294515, by rfl⟩ : syracuseStep 392687 = 589031) B589031
theorem B1670777 : Blo 259821 1670777 := bstep (se 2 (by rfl) ⟨626541, by rfl⟩ : syracuseStep 1670777 = 1253083) B1253083
theorem B392825 : Blo 259821 392825 := bstep (se 2 (by rfl) ⟨147309, by rfl⟩ : syracuseStep 392825 = 294619) B294619
theorem B261951 : Blo 259821 261951 := bstep (se 1 (by rfl) ⟨196463, by rfl⟩ : syracuseStep 261951 = 392927) B392927
theorem B393023 : Blo 259821 393023 := bstep (se 1 (by rfl) ⟨294767, by rfl⟩ : syracuseStep 393023 = 589535) B589535
theorem B261979 : Blo 259821 261979 := bstep (se 1 (by rfl) ⟨196484, by rfl⟩ : syracuseStep 261979 = 392969) B392969
theorem B393071 : Blo 259821 393071 := bstep (se 1 (by rfl) ⟨294803, by rfl⟩ : syracuseStep 393071 = 589607) B589607
theorem B589679 : Blo 259821 589679 := bstep (se 1 (by rfl) ⟨442259, by rfl⟩ : syracuseStep 589679 = 884519) B884519
theorem B295087 : Blo 259821 295087 := bstep (se 1 (by rfl) ⟨221315, by rfl⟩ : syracuseStep 295087 = 442631) B442631
theorem B2228417 : Blo 259821 2228417 := bstep (se 2 (by rfl) ⟨835656, by rfl⟩ : syracuseStep 2228417 = 1671313) B1671313
theorem B262503 : Blo 259821 262503 := bstep (se 1 (by rfl) ⟨196877, by rfl⟩ : syracuseStep 262503 = 393755) B393755
theorem B262623 : Blo 259821 262623 := bstep (se 1 (by rfl) ⟨196967, by rfl⟩ : syracuseStep 262623 = 393935) B393935
theorem B262703 : Blo 259821 262703 := bstep (se 1 (by rfl) ⟨197027, by rfl⟩ : syracuseStep 262703 = 394055) B394055
theorem B557651 : Blo 259821 557651 := bstep (se 1 (by rfl) ⟨418238, by rfl⟩ : syracuseStep 557651 = 836477) B836477
theorem B262747 : Blo 259821 262747 := bstep (se 1 (by rfl) ⟨197060, by rfl⟩ : syracuseStep 262747 = 394121) B394121
theorem B393983 : Blo 259821 393983 := bstep (se 1 (by rfl) ⟨295487, by rfl⟩ : syracuseStep 393983 = 590975) B590975
theorem B262911 : Blo 259821 262911 := bstep (se 1 (by rfl) ⟨197183, by rfl⟩ : syracuseStep 262911 = 394367) B394367
theorem B263003 : Blo 259821 263003 := bstep (se 1 (by rfl) ⟨197252, by rfl⟩ : syracuseStep 263003 = 394505) B394505
theorem B295807 : Blo 259821 295807 := bstep (se 1 (by rfl) ⟨221855, by rfl⟩ : syracuseStep 295807 = 443711) B443711
theorem B263323 : Blo 259821 263323 := bstep (se 1 (by rfl) ⟨197492, by rfl⟩ : syracuseStep 263323 = 394985) B394985
theorem B263327 : Blo 259821 263327 := bstep (se 1 (by rfl) ⟨197495, by rfl⟩ : syracuseStep 263327 = 394991) B394991
theorem B1410257 : Blo 259821 1410257 := bstep (se 2 (by rfl) ⟨528846, by rfl⟩ : syracuseStep 1410257 = 1057693) B1057693
theorem B263495 : Blo 259821 263495 := bstep (se 1 (by rfl) ⟨197621, by rfl⟩ : syracuseStep 263495 = 395243) B395243
theorem B263663 : Blo 259821 263663 := bstep (se 1 (by rfl) ⟨197747, by rfl⟩ : syracuseStep 263663 = 395495) B395495
theorem B394751 : Blo 259821 394751 := bstep (se 1 (by rfl) ⟨296063, by rfl⟩ : syracuseStep 394751 = 592127) B592127
theorem B263679 : Blo 259821 263679 := bstep (se 1 (by rfl) ⟨197759, by rfl⟩ : syracuseStep 263679 = 395519) B395519
theorem B263771 : Blo 259821 263771 := bstep (se 1 (by rfl) ⟨197828, by rfl⟩ : syracuseStep 263771 = 395657) B395657
theorem B591911 : Blo 259821 591911 := bstep (se 1 (by rfl) ⟨443933, by rfl⟩ : syracuseStep 591911 = 887867) B887867
theorem B493609 : Blo 259821 493609 := bstep (se 2 (by rfl) ⟨185103, by rfl⟩ : syracuseStep 493609 = 370207) B370207
theorem B886895 : Blo 259821 886895 := bstep (se 1 (by rfl) ⟨665171, by rfl⟩ : syracuseStep 886895 = 1330343) B1330343
theorem B3770833 : Blo 259821 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B14420531 : Blo 259821 14420531 := bstep (se 1 (by rfl) ⟨10815398, by rfl⟩ : syracuseStep 14420531 = 21630797) B21630797
theorem B625243 : Blo 259821 625243 := bstep (se 1 (by rfl) ⟨468932, by rfl⟩ : syracuseStep 625243 = 937865) B937865
theorem B494171 : Blo 259821 494171 := bstep (se 1 (by rfl) ⟨370628, by rfl⟩ : syracuseStep 494171 = 741257) B741257
theorem B1805003 : Blo 259821 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B2001833 : Blo 259821 2001833 := bstep (se 2 (by rfl) ⟨750687, by rfl⟩ : syracuseStep 2001833 = 1501375) B1501375
theorem B887759 : Blo 259821 887759 := bstep (se 1 (by rfl) ⟨665819, by rfl⟩ : syracuseStep 887759 = 1331639) B1331639
theorem B625619 : Blo 259821 625619 := bstep (se 1 (by rfl) ⟨469214, by rfl⟩ : syracuseStep 625619 = 938429) B938429
theorem B756985 : Blo 259821 756985 := bstep (se 2 (by rfl) ⟨283869, by rfl⟩ : syracuseStep 756985 = 567739) B567739
theorem B593171 : Blo 259821 593171 := bstep (se 1 (by rfl) ⟨444878, by rfl⟩ : syracuseStep 593171 = 889757) B889757
theorem B757147 : Blo 259821 757147 := bstep (se 1 (by rfl) ⟨567860, by rfl⟩ : syracuseStep 757147 = 1135721) B1135721
theorem B21368357 : Blo 259821 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B987005 : Blo 259821 987005 := bstep (se 3 (by rfl) ⟨185063, by rfl⟩ : syracuseStep 987005 = 370127) B370127
theorem B6852761 : Blo 259821 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B1118447 : Blo 259821 1118447 := bstep (se 1 (by rfl) ⟨838835, by rfl⟩ : syracuseStep 1118447 = 1677671) B1677671
theorem B2691377 : Blo 259821 2691377 := bstep (se 2 (by rfl) ⟨1009266, by rfl⟩ : syracuseStep 2691377 = 2018533) B2018533
theorem B5640515 : Blo 259821 5640515 := bstep (se 1 (by rfl) ⟨4230386, by rfl⟩ : syracuseStep 5640515 = 8460773) B8460773
theorem B6951349 : Blo 259821 6951349 := bstep (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) B651689
theorem B2233169 : Blo 259821 2233169 := bstep (se 2 (by rfl) ⟨837438, by rfl⟩ : syracuseStep 2233169 = 1674877) B1674877
theorem B661567 : Blo 259821 661567 := bstep (se 1 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 661567 = 992351) B992351
theorem B2824409 : Blo 259821 2824409 := bstep (se 2 (by rfl) ⟨1059153, by rfl⟩ : syracuseStep 2824409 = 2118307) B2118307
theorem B498287 : Blo 259821 498287 := bstep (se 1 (by rfl) ⟨373715, by rfl⟩ : syracuseStep 498287 = 747431) B747431
theorem B1121111 : Blo 259821 1121111 := bstep (se 1 (by rfl) ⟨840833, by rfl⟩ : syracuseStep 1121111 = 1681667) B1681667
theorem B400297 : Blo 259821 400297 := bstep (se 2 (by rfl) ⟨150111, by rfl⟩ : syracuseStep 400297 = 300223) B300223
theorem B370580453 : Blo 259821 370580453 := bstep (se 4 (by rfl) ⟨34741917, by rfl⟩ : syracuseStep 370580453 = 69483835) B69483835
theorem B630011 : Blo 259821 630011 := bstep (se 1 (by rfl) ⟨472508, by rfl⟩ : syracuseStep 630011 = 945017) B945017
theorem B1056041 : Blo 259821 1056041 := bstep (se 2 (by rfl) ⟨396015, by rfl⟩ : syracuseStep 1056041 = 792031) B792031
theorem B499115 : Blo 259821 499115 := bstep (se 1 (by rfl) ⟨374336, by rfl⟩ : syracuseStep 499115 = 748673) B748673
theorem B1318355 : Blo 259821 1318355 := bstep (se 1 (by rfl) ⟨988766, by rfl⟩ : syracuseStep 1318355 = 1977533) B1977533
theorem B1286423 : Blo 259821 1286423 := bstep (se 1 (by rfl) ⟨964817, by rfl⟩ : syracuseStep 1286423 = 1929635) B1929635
theorem B2237543 : Blo 259821 2237543 := bstep (se 1 (by rfl) ⟨1678157, by rfl⟩ : syracuseStep 2237543 = 3356315) B3356315
theorem B664787 : Blo 259821 664787 := bstep (se 1 (by rfl) ⟨498590, by rfl⟩ : syracuseStep 664787 = 997181) B997181
theorem B1484153 : Blo 259821 1484153 := bstep (se 2 (by rfl) ⟨556557, by rfl⟩ : syracuseStep 1484153 = 1113115) B1113115
theorem B1320947 : Blo 259821 1320947 := bstep (se 1 (by rfl) ⟨990710, by rfl⟩ : syracuseStep 1320947 = 1981421) B1981421
theorem B12921121 : Blo 259821 12921121 := bstep (se 2 (by rfl) ⟨4845420, by rfl⟩ : syracuseStep 12921121 = 9690841) B9690841
theorem B1977047 : Blo 259821 1977047 := bstep (se 1 (by rfl) ⟨1482785, by rfl⟩ : syracuseStep 1977047 = 2965571) B2965571
theorem B994295 : Blo 259821 994295 := bstep (se 1 (by rfl) ⟨745721, by rfl⟩ : syracuseStep 994295 = 1491443) B1491443
theorem B1322243 : Blo 259821 1322243 := bstep (se 1 (by rfl) ⟨991682, by rfl⟩ : syracuseStep 1322243 = 1983365) B1983365
theorem B8039735 : Blo 259821 8039735 := bstep (se 1 (by rfl) ⟨6029801, by rfl⟩ : syracuseStep 8039735 = 12059603) B12059603
theorem B4500845 : Blo 259821 4500845 := bstep (se 3 (by rfl) ⟨843908, by rfl⟩ : syracuseStep 4500845 = 1687817) B1687817
theorem B5484185 : Blo 259821 5484185 := bstep (se 2 (by rfl) ⟨2056569, by rfl⟩ : syracuseStep 5484185 = 4113139) B4113139
theorem B1126169 : Blo 259821 1126169 := bstep (se 2 (by rfl) ⟨422313, by rfl⟩ : syracuseStep 1126169 = 844627) B844627
theorem B2731805 : Blo 259821 2731805 := bstep (se 3 (by rfl) ⟨512213, by rfl⟩ : syracuseStep 2731805 = 1024427) B1024427
theorem B2404333 : Blo 259821 2404333 := bstep (se 3 (by rfl) ⟨450812, by rfl⟩ : syracuseStep 2404333 = 901625) B901625
theorem B1323215 : Blo 259821 1323215 := bstep (se 1 (by rfl) ⟨992411, by rfl⟩ : syracuseStep 1323215 = 1984823) B1984823
theorem B1683899 : Blo 259821 1683899 := bstep (se 1 (by rfl) ⟨1262924, by rfl⟩ : syracuseStep 1683899 = 2525849) B2525849
theorem B569791 : Blo 259821 569791 := bstep (se 1 (by rfl) ⟨427343, by rfl⟩ : syracuseStep 569791 = 854687) B854687
theorem B439067 : Blo 259821 439067 := bstep (se 1 (by rfl) ⟨329300, by rfl⟩ : syracuseStep 439067 = 658601) B658601
theorem B996239 : Blo 259821 996239 := bstep (se 1 (by rfl) ⟨747179, by rfl⟩ : syracuseStep 996239 = 1494359) B1494359
theorem B1979963 : Blo 259821 1979963 := bstep (se 1 (by rfl) ⟨1484972, by rfl⟩ : syracuseStep 1979963 = 2969945) B2969945
theorem B7550891 : Blo 259821 7550891 := bstep (se 1 (by rfl) ⟨5663168, by rfl⟩ : syracuseStep 7550891 = 11326337) B11326337
theorem B440383 : Blo 259821 440383 := bstep (se 1 (by rfl) ⟨330287, by rfl⟩ : syracuseStep 440383 = 660575) B660575
theorem B1325159 : Blo 259821 1325159 := bstep (se 1 (by rfl) ⟨993869, by rfl⟩ : syracuseStep 1325159 = 1987739) B1987739
theorem B997879 : Blo 259821 997879 := bstep (se 1 (by rfl) ⟨748409, by rfl⟩ : syracuseStep 997879 = 1496819) B1496819
theorem B1489529 : Blo 259821 1489529 := bstep (se 2 (by rfl) ⟨558573, by rfl⟩ : syracuseStep 1489529 = 1117147) B1117147
theorem B15743747 : Blo 259821 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B998153 : Blo 259821 998153 := bstep (se 2 (by rfl) ⟨374307, by rfl⟩ : syracuseStep 998153 = 748615) B748615
theorem B1490237 : Blo 259821 1490237 := bstep (se 3 (by rfl) ⟨279419, by rfl⟩ : syracuseStep 1490237 = 558839) B558839
theorem B999155 : Blo 259821 999155 := bstep (se 1 (by rfl) ⟨749366, by rfl⟩ : syracuseStep 999155 = 1498733) B1498733
theorem B442489 : Blo 259821 442489 := bstep (se 2 (by rfl) ⟨165933, by rfl⟩ : syracuseStep 442489 = 331867) B331867
theorem B4243751 : Blo 259821 4243751 := bstep (se 1 (by rfl) ⟨3182813, by rfl⟩ : syracuseStep 4243751 = 6365627) B6365627
theorem B442847 : Blo 259821 442847 := bstep (se 1 (by rfl) ⟨332135, by rfl⟩ : syracuseStep 442847 = 664271) B664271
theorem B1328237 : Blo 259821 1328237 := bstep (se 3 (by rfl) ⟨249044, by rfl⟩ : syracuseStep 1328237 = 498089) B498089
theorem B1000795 : Blo 259821 1000795 := bstep (se 1 (by rfl) ⟨750596, by rfl⟩ : syracuseStep 1000795 = 1501193) B1501193
theorem B1983851 : Blo 259821 1983851 := bstep (se 1 (by rfl) ⟨1487888, by rfl⟩ : syracuseStep 1983851 = 2975777) B2975777
theorem B444487 : Blo 259821 444487 := bstep (se 1 (by rfl) ⟨333365, by rfl⟩ : syracuseStep 444487 = 666731) B666731
theorem B1493153 : Blo 259821 1493153 := bstep (se 2 (by rfl) ⟨559932, by rfl⟩ : syracuseStep 1493153 = 1119865) B1119865
theorem B444919 : Blo 259821 444919 := bstep (se 1 (by rfl) ⟨333689, by rfl⟩ : syracuseStep 444919 = 667379) B667379
theorem B10144763 : Blo 259821 10144763 := bstep (se 1 (by rfl) ⟨7608572, by rfl⟩ : syracuseStep 10144763 = 15217145) B15217145
theorem B1985795 : Blo 259821 1985795 := bstep (se 1 (by rfl) ⟨1489346, by rfl⟩ : syracuseStep 1985795 = 2978693) B2978693
theorem B3329707 : Blo 259821 3329707 := bstep (se 1 (by rfl) ⟨2497280, by rfl⟩ : syracuseStep 3329707 = 4994561) B4994561
theorem B839911 : Blo 259821 839911 := bstep (se 1 (by rfl) ⟨629933, by rfl⟩ : syracuseStep 839911 = 1259867) B1259867
theorem B5624417 : Blo 259821 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B742031 : Blo 259821 742031 := bstep (se 1 (by rfl) ⟨556523, by rfl⟩ : syracuseStep 742031 = 1113047) B1113047
theorem B3068603 : Blo 259821 3068603 := bstep (se 1 (by rfl) ⟨2301452, by rfl⟩ : syracuseStep 3068603 = 4602905) B4602905
theorem B13685939 : Blo 259821 13685939 := bstep (se 1 (by rfl) ⟨10264454, by rfl⟩ : syracuseStep 13685939 = 20528909) B20528909
theorem B19355041 : Blo 259821 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B480767 : Blo 259821 480767 := bstep (se 1 (by rfl) ⟨360575, by rfl⟩ : syracuseStep 480767 = 721151) B721151
theorem B1497275 : Blo 259821 1497275 := bstep (se 1 (by rfl) ⟨1122956, by rfl⟩ : syracuseStep 1497275 = 2245913) B2245913
theorem B1893145 : Blo 259821 1893145 := bstep (se 2 (by rfl) ⟨709929, by rfl⟩ : syracuseStep 1893145 = 1419859) B1419859
theorem B1336823 : Blo 259821 1336823 := bstep (se 1 (by rfl) ⟨1002617, by rfl⟩ : syracuseStep 1336823 = 2005235) B2005235
theorem B1500875 : Blo 259821 1500875 := bstep (se 1 (by rfl) ⟨1125656, by rfl⟩ : syracuseStep 1500875 = 2251313) B2251313
theorem B6056045 : Blo 259821 6056045 := bstep (se 3 (by rfl) ⟨1135508, by rfl⟩ : syracuseStep 6056045 = 2271017) B2271017
theorem B15625723 : Blo 259821 15625723 := bstep (se 1 (by rfl) ⟨11719292, by rfl⟩ : syracuseStep 15625723 = 23438585) B23438585
theorem B945695 : Blo 259821 945695 := bstep (se 1 (by rfl) ⟨709271, by rfl⟩ : syracuseStep 945695 = 1418543) B1418543
theorem B749675 : Blo 259821 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B880847 : Blo 259821 880847 := bstep (se 1 (by rfl) ⟨660635, by rfl⟩ : syracuseStep 880847 = 1321271) B1321271
theorem B20443529 : Blo 259821 20443529 := bstep (se 2 (by rfl) ⟨7666323, by rfl⟩ : syracuseStep 20443529 = 15332647) B15332647
theorem B2028169 : Blo 259821 2028169 := bstep (se 2 (by rfl) ⟨760563, by rfl⟩ : syracuseStep 2028169 = 1521127) B1521127
theorem B881819 : Blo 259821 881819 := bstep (se 1 (by rfl) ⟨661364, by rfl⟩ : syracuseStep 881819 = 1322729) B1322729
theorem B390479 : Blo 259821 390479 := bstep (se 1 (by rfl) ⟨292859, by rfl⟩ : syracuseStep 390479 = 585719) B585719
theorem B390521 : Blo 259821 390521 := bstep (se 2 (by rfl) ⟨146445, by rfl⟩ : syracuseStep 390521 = 292891) B292891
theorem B292351 : Blo 259821 292351 := bstep (se 1 (by rfl) ⟨219263, by rfl⟩ : syracuseStep 292351 = 438527) B438527
theorem B390719 : Blo 259821 390719 := bstep (se 1 (by rfl) ⟨293039, by rfl⟩ : syracuseStep 390719 = 586079) B586079
theorem B259943 : Blo 259821 259943 := bstep (se 1 (by rfl) ⟨194957, by rfl⟩ : syracuseStep 259943 = 389915) B389915
theorem B391067 : Blo 259821 391067 := bstep (se 1 (by rfl) ⟨293300, by rfl⟩ : syracuseStep 391067 = 586601) B586601
theorem B2160557 : Blo 259821 2160557 := bstep (se 3 (by rfl) ⟨405104, by rfl⟩ : syracuseStep 2160557 = 810209) B810209
theorem B260127 : Blo 259821 260127 := bstep (se 1 (by rfl) ⟨195095, by rfl⟩ : syracuseStep 260127 = 390191) B390191
theorem B391199 : Blo 259821 391199 := bstep (se 1 (by rfl) ⟨293399, by rfl⟩ : syracuseStep 391199 = 586799) B586799
theorem B260159 : Blo 259821 260159 := bstep (se 1 (by rfl) ⟨195119, by rfl⟩ : syracuseStep 260159 = 390239) B390239
theorem B260199 : Blo 259821 260199 := bstep (se 1 (by rfl) ⟨195149, by rfl⟩ : syracuseStep 260199 = 390299) B390299
theorem B260207 : Blo 259821 260207 := bstep (se 1 (by rfl) ⟨195155, by rfl⟩ : syracuseStep 260207 = 390311) B390311
theorem B1800407 : Blo 259821 1800407 := bstep (se 1 (by rfl) ⟨1350305, by rfl⟩ : syracuseStep 1800407 = 2700611) B2700611
theorem B260655 : Blo 259821 260655 := bstep (se 1 (by rfl) ⟨195491, by rfl⟩ : syracuseStep 260655 = 390983) B390983
theorem B391727 : Blo 259821 391727 := bstep (se 1 (by rfl) ⟨293795, by rfl⟩ : syracuseStep 391727 = 587591) B587591
theorem B293503 : Blo 259821 293503 := bstep (se 1 (by rfl) ⟨220127, by rfl⟩ : syracuseStep 293503 = 440255) B440255
theorem B260775 : Blo 259821 260775 := bstep (se 1 (by rfl) ⟨195581, by rfl⟩ : syracuseStep 260775 = 391163) B391163
theorem B391847 : Blo 259821 391847 := bstep (se 1 (by rfl) ⟨293885, by rfl⟩ : syracuseStep 391847 = 587771) B587771
theorem B260815 : Blo 259821 260815 := bstep (se 1 (by rfl) ⟨195611, by rfl⟩ : syracuseStep 260815 = 391223) B391223
theorem B260859 : Blo 259821 260859 := bstep (se 1 (by rfl) ⟨195644, by rfl⟩ : syracuseStep 260859 = 391289) B391289
theorem B391931 : Blo 259821 391931 := bstep (se 1 (by rfl) ⟨293948, by rfl⟩ : syracuseStep 391931 = 587897) B587897
theorem B260895 : Blo 259821 260895 := bstep (se 1 (by rfl) ⟨195671, by rfl⟩ : syracuseStep 260895 = 391343) B391343
theorem B391967 : Blo 259821 391967 := bstep (se 1 (by rfl) ⟨293975, by rfl⟩ : syracuseStep 391967 = 587951) B587951
theorem B32635747 : Blo 259821 32635747 := bstep (se 1 (by rfl) ⟨24476810, by rfl⟩ : syracuseStep 32635747 = 48953621) B48953621
theorem B392057 : Blo 259821 392057 := bstep (se 2 (by rfl) ⟨147021, by rfl⟩ : syracuseStep 392057 = 294043) B294043
theorem B3242911 : Blo 259821 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B261055 : Blo 259821 261055 := bstep (se 1 (by rfl) ⟨195791, by rfl⟩ : syracuseStep 261055 = 391583) B391583
theorem B261115 : Blo 259821 261115 := bstep (se 1 (by rfl) ⟨195836, by rfl⟩ : syracuseStep 261115 = 391673) B391673
theorem B3931139 : Blo 259821 3931139 := bstep (se 1 (by rfl) ⟨2948354, by rfl⟩ : syracuseStep 3931139 = 5896709) B5896709
theorem B1997945 : Blo 259821 1997945 := bstep (se 2 (by rfl) ⟨749229, by rfl⟩ : syracuseStep 1997945 = 1498459) B1498459
theorem B392399 : Blo 259821 392399 := bstep (se 1 (by rfl) ⟨294299, by rfl⟩ : syracuseStep 392399 = 588599) B588599
theorem B261439 : Blo 259821 261439 := bstep (se 1 (by rfl) ⟨196079, by rfl⟩ : syracuseStep 261439 = 392159) B392159
theorem B392519 : Blo 259821 392519 := bstep (se 1 (by rfl) ⟨294389, by rfl⟩ : syracuseStep 392519 = 588779) B588779
theorem B261479 : Blo 259821 261479 := bstep (se 1 (by rfl) ⟨196109, by rfl⟩ : syracuseStep 261479 = 392219) B392219
theorem B261735 : Blo 259821 261735 := bstep (se 1 (by rfl) ⟨196301, by rfl⟩ : syracuseStep 261735 = 392603) B392603
theorem B261787 : Blo 259821 261787 := bstep (se 1 (by rfl) ⟨196340, by rfl⟩ : syracuseStep 261787 = 392681) B392681
theorem B261791 : Blo 259821 261791 := bstep (se 1 (by rfl) ⟨196343, by rfl⟩ : syracuseStep 261791 = 392687) B392687
theorem B1113851 : Blo 259821 1113851 := bstep (se 1 (by rfl) ⟨835388, by rfl⟩ : syracuseStep 1113851 = 1670777) B1670777
theorem B261883 : Blo 259821 261883 := bstep (se 1 (by rfl) ⟨196412, by rfl⟩ : syracuseStep 261883 = 392825) B392825
theorem B556831 : Blo 259821 556831 := bstep (se 1 (by rfl) ⟨417623, by rfl⟩ : syracuseStep 556831 = 835247) B835247
theorem B262015 : Blo 259821 262015 := bstep (se 1 (by rfl) ⟨196511, by rfl⟩ : syracuseStep 262015 = 393023) B393023
theorem B262047 : Blo 259821 262047 := bstep (se 1 (by rfl) ⟨196535, by rfl⟩ : syracuseStep 262047 = 393071) B393071
theorem B393119 : Blo 259821 393119 := bstep (se 1 (by rfl) ⟨294839, by rfl⟩ : syracuseStep 393119 = 589679) B589679
theorem B884681 : Blo 259821 884681 := bstep (se 2 (by rfl) ⟨331755, by rfl⟩ : syracuseStep 884681 = 663511) B663511
theorem B294907 : Blo 259821 294907 := bstep (se 1 (by rfl) ⟨221180, by rfl⟩ : syracuseStep 294907 = 442361) B442361
theorem B589985 : Blo 259821 589985 := bstep (se 2 (by rfl) ⟨221244, by rfl⟩ : syracuseStep 589985 = 442489) B442489
theorem B393449 : Blo 259821 393449 := bstep (se 2 (by rfl) ⟨147543, by rfl⟩ : syracuseStep 393449 = 295087) B295087
theorem B295231 : Blo 259821 295231 := bstep (se 1 (by rfl) ⟨221423, by rfl⟩ : syracuseStep 295231 = 442847) B442847
theorem B262655 : Blo 259821 262655 := bstep (se 1 (by rfl) ⟨196991, by rfl⟩ : syracuseStep 262655 = 393983) B393983
theorem B885491 : Blo 259821 885491 := bstep (se 1 (by rfl) ⟨664118, by rfl⟩ : syracuseStep 885491 = 1328237) B1328237
theorem B54887381 : Blo 259821 54887381 := bstep (se 7 (by rfl) ⟨643211, by rfl⟩ : syracuseStep 54887381 = 1286423) B1286423
theorem B263167 : Blo 259821 263167 := bstep (se 1 (by rfl) ⟨197375, by rfl⟩ : syracuseStep 263167 = 394751) B394751
theorem B2524193 : Blo 259821 2524193 := bstep (se 2 (by rfl) ⟨946572, by rfl⟩ : syracuseStep 2524193 = 1893145) B1893145
theorem B394409 : Blo 259821 394409 := bstep (se 2 (by rfl) ⟨147903, by rfl⟩ : syracuseStep 394409 = 295807) B295807
theorem B394607 : Blo 259821 394607 := bstep (se 1 (by rfl) ⟨295955, by rfl⟩ : syracuseStep 394607 = 591911) B591911
theorem B591263 : Blo 259821 591263 := bstep (se 1 (by rfl) ⟨443447, by rfl⟩ : syracuseStep 591263 = 886895) B886895
theorem B329447 : Blo 259821 329447 := bstep (se 1 (by rfl) ⟨247085, by rfl⟩ : syracuseStep 329447 = 494171) B494171
theorem B591839 : Blo 259821 591839 := bstep (se 1 (by rfl) ⟨443879, by rfl⟩ : syracuseStep 591839 = 887759) B887759
theorem B395447 : Blo 259821 395447 := bstep (se 1 (by rfl) ⟨296585, by rfl⟩ : syracuseStep 395447 = 593171) B593171
theorem B658003 : Blo 259821 658003 := bstep (se 1 (by rfl) ⟨493502, by rfl⟩ : syracuseStep 658003 = 987005) B987005
theorem B658145 : Blo 259821 658145 := bstep (se 2 (by rfl) ⟨246804, by rfl⟩ : syracuseStep 658145 = 493609) B493609
theorem B592649 : Blo 259821 592649 := bstep (se 2 (by rfl) ⟨222243, by rfl⟩ : syracuseStep 592649 = 444487) B444487
theorem B494687 : Blo 259821 494687 := bstep (se 1 (by rfl) ⟨371015, by rfl⟩ : syracuseStep 494687 = 742031) B742031
theorem B593225 : Blo 259821 593225 := bstep (se 2 (by rfl) ⟨222459, by rfl⟩ : syracuseStep 593225 = 444919) B444919
theorem B332191 : Blo 259821 332191 := bstep (se 1 (by rfl) ⟨249143, by rfl⟩ : syracuseStep 332191 = 498287) B498287
theorem B332743 : Blo 259821 332743 := bstep (se 1 (by rfl) ⟨249557, by rfl⟩ : syracuseStep 332743 = 499115) B499115
theorem B1119881 : Blo 259821 1119881 := bstep (se 2 (by rfl) ⟨419955, by rfl⟩ : syracuseStep 1119881 = 839911) B839911
theorem B759721 : Blo 259821 759721 := bstep (se 2 (by rfl) ⟨284895, by rfl⟩ : syracuseStep 759721 = 569791) B569791
theorem B989435 : Blo 259821 989435 := bstep (se 1 (by rfl) ⟨742076, by rfl⟩ : syracuseStep 989435 = 1484153) B1484153
theorem B891215 : Blo 259821 891215 := bstep (se 1 (by rfl) ⟨668411, by rfl⟩ : syracuseStep 891215 = 1336823) B1336823
theorem B4037363 : Blo 259821 4037363 := bstep (se 1 (by rfl) ⟨3028022, by rfl⟩ : syracuseStep 4037363 = 6056045) B6056045
theorem B1318031 : Blo 259821 1318031 := bstep (se 1 (by rfl) ⟨988523, by rfl⟩ : syracuseStep 1318031 = 1977047) B1977047
theorem B662863 : Blo 259821 662863 := bstep (se 1 (by rfl) ⟨497147, by rfl⟩ : syracuseStep 662863 = 994295) B994295
theorem B499783 : Blo 259821 499783 := bstep (se 1 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 499783 = 749675) B749675
theorem B1122599 : Blo 259821 1122599 := bstep (se 1 (by rfl) ⟨841949, by rfl⟩ : syracuseStep 1122599 = 1683899) B1683899
theorem B664159 : Blo 259821 664159 := bstep (se 1 (by rfl) ⟨498119, by rfl⟩ : syracuseStep 664159 = 996239) B996239
theorem B1319975 : Blo 259821 1319975 := bstep (se 1 (by rfl) ⟨989981, by rfl⟩ : syracuseStep 1319975 = 1979963) B1979963
theorem B533729 : Blo 259821 533729 := bstep (se 2 (by rfl) ⟨200148, by rfl⟩ : syracuseStep 533729 = 400297) B400297
theorem B993019 : Blo 259821 993019 := bstep (se 1 (by rfl) ⟨744764, by rfl⟩ : syracuseStep 993019 = 1489529) B1489529
theorem B10495831 : Blo 259821 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B665435 : Blo 259821 665435 := bstep (se 1 (by rfl) ⟨499076, by rfl⟩ : syracuseStep 665435 = 998153) B998153
theorem B993491 : Blo 259821 993491 := bstep (se 1 (by rfl) ⟨745118, by rfl⟩ : syracuseStep 993491 = 1490237) B1490237
theorem B666103 : Blo 259821 666103 := bstep (se 1 (by rfl) ⟨499577, by rfl⟩ : syracuseStep 666103 = 999155) B999155
theorem B1485611 : Blo 259821 1485611 := bstep (se 1 (by rfl) ⟨1114208, by rfl⟩ : syracuseStep 1485611 = 2228417) B2228417
theorem B2829167 : Blo 259821 2829167 := bstep (se 1 (by rfl) ⟨2121875, by rfl⟩ : syracuseStep 2829167 = 4243751) B4243751
theorem B1322567 : Blo 259821 1322567 := bstep (se 1 (by rfl) ⟨991925, by rfl⟩ : syracuseStep 1322567 = 1983851) B1983851
theorem B995435 : Blo 259821 995435 := bstep (se 1 (by rfl) ⟨746576, by rfl⟩ : syracuseStep 995435 = 1493153) B1493153
theorem B1487069 : Blo 259821 1487069 := bstep (se 3 (by rfl) ⟨278825, by rfl⟩ : syracuseStep 1487069 = 557651) B557651
theorem B9613687 : Blo 259821 9613687 := bstep (se 1 (by rfl) ⟨7210265, by rfl⟩ : syracuseStep 9613687 = 14420531) B14420531
theorem B6763175 : Blo 259821 6763175 := bstep (se 1 (by rfl) ⟨5072381, by rfl⟩ : syracuseStep 6763175 = 10144763) B10144763
theorem B1323863 : Blo 259821 1323863 := bstep (se 1 (by rfl) ⟨992897, by rfl⟩ : syracuseStep 1323863 = 1985795) B1985795
theorem B4568507 : Blo 259821 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B2045735 : Blo 259821 2045735 := bstep (se 1 (by rfl) ⟨1534301, by rfl⟩ : syracuseStep 2045735 = 3068603) B3068603
theorem B1488779 : Blo 259821 1488779 := bstep (se 1 (by rfl) ⟨1116584, by rfl⟩ : syracuseStep 1488779 = 2233169) B2233169
theorem B5027777 : Blo 259821 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B9123959 : Blo 259821 9123959 := bstep (se 1 (by rfl) ⟨6842969, by rfl⟩ : syracuseStep 9123959 = 13685939) B13685939
theorem B833657 : Blo 259821 833657 := bstep (se 2 (by rfl) ⟨312621, by rfl⟩ : syracuseStep 833657 = 625243) B625243
theorem B998183 : Blo 259821 998183 := bstep (se 1 (by rfl) ⟨748637, by rfl⟩ : syracuseStep 998183 = 1497275) B1497275
theorem B1882939 : Blo 259821 1882939 := bstep (se 1 (by rfl) ⟨1412204, by rfl⟩ : syracuseStep 1882939 = 2824409) B2824409
theorem B247053635 : Blo 259821 247053635 := bstep (se 1 (by rfl) ⟨185290226, by rfl⟩ : syracuseStep 247053635 = 370580453) B370580453
theorem B704027 : Blo 259821 704027 := bstep (se 1 (by rfl) ⟨528020, by rfl⟩ : syracuseStep 704027 = 1056041) B1056041
theorem B4439609 : Blo 259821 4439609 := bstep (se 2 (by rfl) ⟨1664853, by rfl⟩ : syracuseStep 4439609 = 3329707) B3329707
theorem B5128181 : Blo 259821 5128181 := bstep (se 5 (by rfl) ⟨240383, by rfl⟩ : syracuseStep 5128181 = 480767) B480767
theorem B1491695 : Blo 259821 1491695 := bstep (se 1 (by rfl) ⟨1118771, by rfl⟩ : syracuseStep 1491695 = 2237543) B2237543
theorem B443191 : Blo 259821 443191 := bstep (se 1 (by rfl) ⟨332393, by rfl⟩ : syracuseStep 443191 = 664787) B664787
theorem B2704225 : Blo 259821 2704225 := bstep (se 2 (by rfl) ⟨1014084, by rfl⟩ : syracuseStep 2704225 = 2028169) B2028169
theorem B1000583 : Blo 259821 1000583 := bstep (se 1 (by rfl) ⟨750437, by rfl⟩ : syracuseStep 1000583 = 1500875) B1500875
theorem B25806721 : Blo 259821 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B5359823 : Blo 259821 5359823 := bstep (se 1 (by rfl) ⟨4019867, by rfl⟩ : syracuseStep 5359823 = 8039735) B8039735
theorem B3000563 : Blo 259821 3000563 := bstep (se 1 (by rfl) ⟨2250422, by rfl⟩ : syracuseStep 3000563 = 4500845) B4500845
theorem B3656123 : Blo 259821 3656123 := bstep (se 1 (by rfl) ⟨2742092, by rfl⟩ : syracuseStep 3656123 = 5484185) B5484185
theorem B1821203 : Blo 259821 1821203 := bstep (se 1 (by rfl) ⟨1365902, by rfl⟩ : syracuseStep 1821203 = 2731805) B2731805
theorem B1330505 : Blo 259821 1330505 := bstep (se 2 (by rfl) ⟨498939, by rfl⟩ : syracuseStep 1330505 = 997879) B997879
theorem B5033927 : Blo 259821 5033927 := bstep (se 1 (by rfl) ⟨3775445, by rfl⟩ : syracuseStep 5033927 = 7550891) B7550891
theorem B1200271 : Blo 259821 1200271 := bstep (se 1 (by rfl) ⟨900203, by rfl⟩ : syracuseStep 1200271 = 1800407) B1800407
theorem B1331963 : Blo 259821 1331963 := bstep (se 1 (by rfl) ⟨998972, by rfl⟩ : syracuseStep 1331963 = 1997945) B1997945
theorem B742441 : Blo 259821 742441 := bstep (se 2 (by rfl) ⟨278415, by rfl⟩ : syracuseStep 742441 = 556831) B556831
theorem B742567 : Blo 259821 742567 := bstep (se 1 (by rfl) ⟨556925, by rfl⟩ : syracuseStep 742567 = 1113851) B1113851
theorem B940171 : Blo 259821 940171 := bstep (se 1 (by rfl) ⟨705128, by rfl⟩ : syracuseStep 940171 = 1410257) B1410257
theorem B14998445 : Blo 259821 14998445 := bstep (se 3 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 14998445 = 5624417) B5624417
theorem B1334393 : Blo 259821 1334393 := bstep (se 2 (by rfl) ⟨500397, by rfl⟩ : syracuseStep 1334393 = 1000795) B1000795
theorem B1203335 : Blo 259821 1203335 := bstep (se 1 (by rfl) ⟨902501, by rfl⟩ : syracuseStep 1203335 = 1805003) B1805003
theorem B1334555 : Blo 259821 1334555 := bstep (se 1 (by rfl) ⟨1000916, by rfl⟩ : syracuseStep 1334555 = 2001833) B2001833
theorem B417079 : Blo 259821 417079 := bstep (se 1 (by rfl) ⟨312809, by rfl⟩ : syracuseStep 417079 = 625619) B625619
theorem B14245571 : Blo 259821 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B745631 : Blo 259821 745631 := bstep (se 1 (by rfl) ⟨559223, by rfl⟩ : syracuseStep 745631 = 1118447) B1118447
theorem B1794251 : Blo 259821 1794251 := bstep (se 1 (by rfl) ⟨1345688, by rfl⟩ : syracuseStep 1794251 = 2691377) B2691377
theorem B3760343 : Blo 259821 3760343 := bstep (se 1 (by rfl) ⟨2820257, by rfl⟩ : syracuseStep 3760343 = 5640515) B5640515
theorem B17228161 : Blo 259821 17228161 := bstep (se 2 (by rfl) ⟨6460560, by rfl⟩ : syracuseStep 17228161 = 12921121) B12921121
theorem B1009313 : Blo 259821 1009313 := bstep (se 2 (by rfl) ⟨378492, by rfl⟩ : syracuseStep 1009313 = 756985) B756985
theorem B1009529 : Blo 259821 1009529 := bstep (se 2 (by rfl) ⟨378573, by rfl⟩ : syracuseStep 1009529 = 757147) B757147
theorem B747407 : Blo 259821 747407 := bstep (se 1 (by rfl) ⟨560555, by rfl⟩ : syracuseStep 747407 = 1121111) B1121111
theorem B20834297 : Blo 259821 20834297 := bstep (se 2 (by rfl) ⟨7812861, by rfl⟩ : syracuseStep 20834297 = 15625723) B15625723
theorem B420007 : Blo 259821 420007 := bstep (se 1 (by rfl) ⟨315005, by rfl⟩ : syracuseStep 420007 = 630011) B630011
theorem B878903 : Blo 259821 878903 := bstep (se 1 (by rfl) ⟨659177, by rfl⟩ : syracuseStep 878903 = 1318355) B1318355
theorem B3205777 : Blo 259821 3205777 := bstep (se 2 (by rfl) ⟨1202166, by rfl⟩ : syracuseStep 3205777 = 2404333) B2404333
theorem B9268465 : Blo 259821 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B880631 : Blo 259821 880631 := bstep (se 1 (by rfl) ⟨660473, by rfl⟩ : syracuseStep 880631 = 1320947) B1320947
theorem B389801 : Blo 259821 389801 := bstep (se 2 (by rfl) ⟨146175, by rfl⟩ : syracuseStep 389801 = 292351) B292351
theorem B881495 : Blo 259821 881495 := bstep (se 1 (by rfl) ⟨661121, by rfl⟩ : syracuseStep 881495 = 1322243) B1322243
theorem B750779 : Blo 259821 750779 := bstep (se 1 (by rfl) ⟨563084, by rfl⟩ : syracuseStep 750779 = 1126169) B1126169
theorem B587177 : Blo 259821 587177 := bstep (se 2 (by rfl) ⟨220191, by rfl⟩ : syracuseStep 587177 = 440383) B440383
theorem B882089 : Blo 259821 882089 := bstep (se 2 (by rfl) ⟨330783, by rfl⟩ : syracuseStep 882089 = 661567) B661567
theorem B587231 : Blo 259821 587231 := bstep (se 1 (by rfl) ⟨440423, by rfl⟩ : syracuseStep 587231 = 880847) B880847
theorem B882143 : Blo 259821 882143 := bstep (se 1 (by rfl) ⟨661607, by rfl⟩ : syracuseStep 882143 = 1323215) B1323215
theorem B13629019 : Blo 259821 13629019 := bstep (se 1 (by rfl) ⟨10221764, by rfl⟩ : syracuseStep 13629019 = 20443529) B20443529
theorem B292711 : Blo 259821 292711 := bstep (se 1 (by rfl) ⟨219533, by rfl⟩ : syracuseStep 292711 = 439067) B439067
theorem B587879 : Blo 259821 587879 := bstep (se 1 (by rfl) ⟨440909, by rfl⟩ : syracuseStep 587879 = 881819) B881819
theorem B391337 : Blo 259821 391337 := bstep (se 2 (by rfl) ⟨146751, by rfl⟩ : syracuseStep 391337 = 293503) B293503
theorem B260319 : Blo 259821 260319 := bstep (se 1 (by rfl) ⟨195239, by rfl⟩ : syracuseStep 260319 = 390479) B390479
theorem B260347 : Blo 259821 260347 := bstep (se 1 (by rfl) ⟨195260, by rfl⟩ : syracuseStep 260347 = 390521) B390521
theorem B260479 : Blo 259821 260479 := bstep (se 1 (by rfl) ⟨195359, by rfl⟩ : syracuseStep 260479 = 390719) B390719
theorem B43514329 : Blo 259821 43514329 := bstep (se 2 (by rfl) ⟨16317873, by rfl⟩ : syracuseStep 43514329 = 32635747) B32635747
theorem B4323881 : Blo 259821 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B260711 : Blo 259821 260711 := bstep (se 1 (by rfl) ⟨195533, by rfl⟩ : syracuseStep 260711 = 391067) B391067
theorem B1440371 : Blo 259821 1440371 := bstep (se 1 (by rfl) ⟨1080278, by rfl⟩ : syracuseStep 1440371 = 2160557) B2160557
theorem B260799 : Blo 259821 260799 := bstep (se 1 (by rfl) ⟨195599, by rfl⟩ : syracuseStep 260799 = 391199) B391199
theorem B883439 : Blo 259821 883439 := bstep (se 1 (by rfl) ⟨662579, by rfl⟩ : syracuseStep 883439 = 1325159) B1325159
theorem B2521853 : Blo 259821 2521853 := bstep (se 3 (by rfl) ⟨472847, by rfl⟩ : syracuseStep 2521853 = 945695) B945695
theorem B261151 : Blo 259821 261151 := bstep (se 1 (by rfl) ⟨195863, by rfl⟩ : syracuseStep 261151 = 391727) B391727
theorem B261231 : Blo 259821 261231 := bstep (se 1 (by rfl) ⟨195923, by rfl⟩ : syracuseStep 261231 = 391847) B391847
theorem B261287 : Blo 259821 261287 := bstep (se 1 (by rfl) ⟨195965, by rfl⟩ : syracuseStep 261287 = 391931) B391931
theorem B261311 : Blo 259821 261311 := bstep (se 1 (by rfl) ⟨195983, by rfl⟩ : syracuseStep 261311 = 391967) B391967
theorem B261371 : Blo 259821 261371 := bstep (se 1 (by rfl) ⟨196028, by rfl⟩ : syracuseStep 261371 = 392057) B392057
theorem B2620759 : Blo 259821 2620759 := bstep (se 1 (by rfl) ⟨1965569, by rfl⟩ : syracuseStep 2620759 = 3931139) B3931139
theorem B261599 : Blo 259821 261599 := bstep (se 1 (by rfl) ⟨196199, by rfl⟩ : syracuseStep 261599 = 392399) B392399
theorem B261679 : Blo 259821 261679 := bstep (se 1 (by rfl) ⟨196259, by rfl⟩ : syracuseStep 261679 = 392519) B392519
theorem B262079 : Blo 259821 262079 := bstep (se 1 (by rfl) ⟨196559, by rfl⟩ : syracuseStep 262079 = 393119) B393119
theorem B589787 : Blo 259821 589787 := bstep (se 1 (by rfl) ⟨442340, by rfl⟩ : syracuseStep 589787 = 884681) B884681
theorem B393209 : Blo 259821 393209 := bstep (se 2 (by rfl) ⟨147453, by rfl⟩ : syracuseStep 393209 = 294907) B294907
theorem B393323 : Blo 259821 393323 := bstep (se 1 (by rfl) ⟨294992, by rfl⟩ : syracuseStep 393323 = 589985) B589985
theorem B262299 : Blo 259821 262299 := bstep (se 1 (by rfl) ⟨196724, by rfl⟩ : syracuseStep 262299 = 393449) B393449
theorem B393641 : Blo 259821 393641 := bstep (se 2 (by rfl) ⟨147615, by rfl⟩ : syracuseStep 393641 = 295231) B295231
theorem B590327 : Blo 259821 590327 := bstep (se 1 (by rfl) ⟨442745, by rfl⟩ : syracuseStep 590327 = 885491) B885491
theorem B22970881 : Blo 259821 22970881 := bstep (se 2 (by rfl) ⟨8614080, by rfl⟩ : syracuseStep 22970881 = 17228161) B17228161
theorem B262939 : Blo 259821 262939 := bstep (se 1 (by rfl) ⟨197204, by rfl⟩ : syracuseStep 262939 = 394409) B394409
theorem B885545 : Blo 259821 885545 := bstep (se 2 (by rfl) ⟨332079, by rfl⟩ : syracuseStep 885545 = 664159) B664159
theorem B263071 : Blo 259821 263071 := bstep (se 1 (by rfl) ⟨197303, by rfl⟩ : syracuseStep 263071 = 394607) B394607
theorem B394175 : Blo 259821 394175 := bstep (se 1 (by rfl) ⟨295631, by rfl⟩ : syracuseStep 394175 = 591263) B591263
theorem B590921 : Blo 259821 590921 := bstep (se 2 (by rfl) ⟨221595, by rfl⟩ : syracuseStep 590921 = 443191) B443191
theorem B3605633 : Blo 259821 3605633 := bstep (se 2 (by rfl) ⟨1352112, by rfl⟩ : syracuseStep 3605633 = 2704225) B2704225
theorem B394559 : Blo 259821 394559 := bstep (se 1 (by rfl) ⟨295919, by rfl⟩ : syracuseStep 394559 = 591839) B591839
theorem B263631 : Blo 259821 263631 := bstep (se 1 (by rfl) ⟨197723, by rfl⟩ : syracuseStep 263631 = 395447) B395447
theorem B3573215 : Blo 259821 3573215 := bstep (se 1 (by rfl) ⟨2679911, by rfl⟩ : syracuseStep 3573215 = 5359823) B5359823
theorem B2000375 : Blo 259821 2000375 := bstep (se 1 (by rfl) ⟨1500281, by rfl⟩ : syracuseStep 2000375 = 3000563) B3000563
theorem B1214135 : Blo 259821 1214135 := bstep (se 1 (by rfl) ⟨910601, by rfl⟩ : syracuseStep 1214135 = 1821203) B1821203
theorem B395099 : Blo 259821 395099 := bstep (se 1 (by rfl) ⟨296324, by rfl⟩ : syracuseStep 395099 = 592649) B592649
theorem B887003 : Blo 259821 887003 := bstep (se 1 (by rfl) ⟨665252, by rfl⟩ : syracuseStep 887003 = 1330505) B1330505
theorem B395483 : Blo 259821 395483 := bstep (se 1 (by rfl) ⟨296612, by rfl⟩ : syracuseStep 395483 = 593225) B593225
theorem B13994441 : Blo 259821 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B34408961 : Blo 259821 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B560009 : Blo 259821 560009 := bstep (se 2 (by rfl) ⟨210003, by rfl⟩ : syracuseStep 560009 = 420007) B420007
theorem B887975 : Blo 259821 887975 := bstep (se 1 (by rfl) ⟨665981, by rfl⟩ : syracuseStep 887975 = 1331963) B1331963
theorem B888137 : Blo 259821 888137 := bstep (se 2 (by rfl) ⟨333051, by rfl⟩ : syracuseStep 888137 = 666103) B666103
theorem B659623 : Blo 259821 659623 := bstep (se 1 (by rfl) ⟨494717, by rfl⟩ : syracuseStep 659623 = 989435) B989435
theorem B594143 : Blo 259821 594143 := bstep (se 1 (by rfl) ⟨445607, by rfl⟩ : syracuseStep 594143 = 891215) B891215
theorem B12357953 : Blo 259821 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B2691575 : Blo 259821 2691575 := bstep (se 1 (by rfl) ⟨2018681, by rfl⟩ : syracuseStep 2691575 = 4037363) B4037363
theorem B9998963 : Blo 259821 9998963 := bstep (se 1 (by rfl) ⟨7499222, by rfl⟩ : syracuseStep 9998963 = 14998445) B14998445
theorem B889595 : Blo 259821 889595 := bstep (se 1 (by rfl) ⟨667196, by rfl⟩ : syracuseStep 889595 = 1334393) B1334393
theorem B889703 : Blo 259821 889703 := bstep (se 1 (by rfl) ⟨667277, by rfl⟩ : syracuseStep 889703 = 1334555) B1334555
theorem B497087 : Blo 259821 497087 := bstep (se 1 (by rfl) ⟨372815, by rfl⟩ : syracuseStep 497087 = 745631) B745631
theorem B12818249 : Blo 259821 12818249 := bstep (se 2 (by rfl) ⟨4806843, by rfl⟩ : syracuseStep 12818249 = 9613687) B9613687
theorem B989921 : Blo 259821 989921 := bstep (se 2 (by rfl) ⟨371220, by rfl⟩ : syracuseStep 989921 = 742441) B742441
theorem B662327 : Blo 259821 662327 := bstep (se 1 (by rfl) ⟨496745, by rfl⟩ : syracuseStep 662327 = 993491) B993491
theorem B990089 : Blo 259821 990089 := bstep (se 2 (by rfl) ⟨371283, by rfl⟩ : syracuseStep 990089 = 742567) B742567
theorem B990407 : Blo 259821 990407 := bstep (se 1 (by rfl) ⟨742805, by rfl⟩ : syracuseStep 990407 = 1485611) B1485611
theorem B262139 : Blo 259821 262139 := bstep (se 1 (by rfl) ⟨196604, by rfl⟩ : syracuseStep 262139 = 393209) B393209
theorem B663623 : Blo 259821 663623 := bstep (se 1 (by rfl) ⟨497717, by rfl⟩ : syracuseStep 663623 = 995435) B995435
theorem B991379 : Blo 259821 991379 := bstep (se 1 (by rfl) ⟨743534, by rfl⟩ : syracuseStep 991379 = 1487069) B1487069
theorem B1253561 : Blo 259821 1253561 := bstep (se 2 (by rfl) ⟨470085, by rfl⟩ : syracuseStep 1253561 = 940171) B940171
theorem B1319165 : Blo 259821 1319165 := bstep (se 3 (by rfl) ⟨247343, by rfl⟩ : syracuseStep 1319165 = 494687) B494687
theorem B500519 : Blo 259821 500519 := bstep (se 1 (by rfl) ⟨375389, by rfl⟩ : syracuseStep 500519 = 750779) B750779
theorem B992519 : Blo 259821 992519 := bstep (se 1 (by rfl) ⟨744389, by rfl⟩ : syracuseStep 992519 = 1488779) B1488779
theorem B3351851 : Blo 259821 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B960247 : Blo 259821 960247 := bstep (se 1 (by rfl) ⟨720185, by rfl⟩ : syracuseStep 960247 = 1440371) B1440371
theorem B1681235 : Blo 259821 1681235 := bstep (se 1 (by rfl) ⟨1260926, by rfl⟩ : syracuseStep 1681235 = 2521853) B2521853
theorem B37988189 : Blo 259821 37988189 := bstep (se 3 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 37988189 = 14245571) B14245571
theorem B665455 : Blo 259821 665455 := bstep (se 1 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 665455 = 998183) B998183
theorem B164702423 : Blo 259821 164702423 := bstep (se 1 (by rfl) ⟨123526817, by rfl⟩ : syracuseStep 164702423 = 247053635) B247053635
theorem B469351 : Blo 259821 469351 := bstep (se 1 (by rfl) ⟨352013, by rfl⟩ : syracuseStep 469351 = 704027) B704027
theorem B2959739 : Blo 259821 2959739 := bstep (se 1 (by rfl) ⟨2219804, by rfl⟩ : syracuseStep 2959739 = 4439609) B4439609
theorem B3418787 : Blo 259821 3418787 := bstep (se 1 (by rfl) ⟨2564090, by rfl⟩ : syracuseStep 3418787 = 5128181) B5128181
theorem B666377 : Blo 259821 666377 := bstep (se 2 (by rfl) ⟨249891, by rfl⟩ : syracuseStep 666377 = 499783) B499783
theorem B994463 : Blo 259821 994463 := bstep (se 1 (by rfl) ⟨745847, by rfl⟩ : syracuseStep 994463 = 1491695) B1491695
theorem B1682795 : Blo 259821 1682795 := bstep (se 1 (by rfl) ⟨1262096, by rfl⟩ : syracuseStep 1682795 = 2524193) B2524193
theorem B667055 : Blo 259821 667055 := bstep (se 1 (by rfl) ⟨500291, by rfl⟩ : syracuseStep 667055 = 1000583) B1000583
theorem B2437415 : Blo 259821 2437415 := bstep (se 1 (by rfl) ⟨1828061, by rfl⟩ : syracuseStep 2437415 = 3656123) B3656123
theorem B438763 : Blo 259821 438763 := bstep (se 1 (by rfl) ⟨329072, by rfl⟩ : syracuseStep 438763 = 658145) B658145
theorem B1324025 : Blo 259821 1324025 := bstep (se 2 (by rfl) ⟨496509, by rfl⟩ : syracuseStep 1324025 = 993019) B993019
theorem B3355951 : Blo 259821 3355951 := bstep (se 1 (by rfl) ⟨2516963, by rfl⟩ : syracuseStep 3355951 = 5033927) B5033927
theorem B1423277 : Blo 259821 1423277 := bstep (se 3 (by rfl) ⟨266864, by rfl⟩ : syracuseStep 1423277 = 533729) B533729
theorem B4274369 : Blo 259821 4274369 := bstep (se 2 (by rfl) ⟨1602888, by rfl⟩ : syracuseStep 4274369 = 3205777) B3205777
theorem B802223 : Blo 259821 802223 := bstep (se 1 (by rfl) ⟨601667, by rfl⟩ : syracuseStep 802223 = 1203335) B1203335
theorem B1196167 : Blo 259821 1196167 := bstep (se 1 (by rfl) ⟨897125, by rfl⟩ : syracuseStep 1196167 = 1794251) B1794251
theorem B2506895 : Blo 259821 2506895 := bstep (se 1 (by rfl) ⟨1880171, by rfl⟩ : syracuseStep 2506895 = 3760343) B3760343
theorem B24330557 : Blo 259821 24330557 := bstep (se 3 (by rfl) ⟨4561979, by rfl⟩ : syracuseStep 24330557 = 9123959) B9123959
theorem B442921 : Blo 259821 442921 := bstep (se 2 (by rfl) ⟨166095, by rfl⟩ : syracuseStep 442921 = 332191) B332191
theorem B672875 : Blo 259821 672875 := bstep (se 1 (by rfl) ⟨504656, by rfl⟩ : syracuseStep 672875 = 1009313) B1009313
theorem B443623 : Blo 259821 443623 := bstep (se 1 (by rfl) ⟨332717, by rfl⟩ : syracuseStep 443623 = 665435) B665435
theorem B673019 : Blo 259821 673019 := bstep (se 1 (by rfl) ⟨504764, by rfl⟩ : syracuseStep 673019 = 1009529) B1009529
theorem B443657 : Blo 259821 443657 := bstep (se 2 (by rfl) ⟨166371, by rfl⟩ : syracuseStep 443657 = 332743) B332743
theorem B1886111 : Blo 259821 1886111 := bstep (se 1 (by rfl) ⟨1414583, by rfl⟩ : syracuseStep 1886111 = 2829167) B2829167
theorem B18172025 : Blo 259821 18172025 := bstep (se 2 (by rfl) ⟨6814509, by rfl⟩ : syracuseStep 18172025 = 13629019) B13629019
theorem B4508783 : Blo 259821 4508783 := bstep (se 1 (by rfl) ⟨3381587, by rfl⟩ : syracuseStep 4508783 = 6763175) B6763175
theorem B58019105 : Blo 259821 58019105 := bstep (se 2 (by rfl) ⟨21757164, by rfl⟩ : syracuseStep 58019105 = 43514329) B43514329
theorem B2510585 : Blo 259821 2510585 := bstep (se 2 (by rfl) ⟨941469, by rfl⟩ : syracuseStep 2510585 = 1882939) B1882939
theorem B1363823 : Blo 259821 1363823 := bstep (se 1 (by rfl) ⟨1022867, by rfl⟩ : syracuseStep 1363823 = 2045735) B2045735
theorem B3494345 : Blo 259821 3494345 := bstep (se 2 (by rfl) ⟨1310379, by rfl⟩ : syracuseStep 3494345 = 2620759) B2620759
theorem B36591587 : Blo 259821 36591587 := bstep (se 1 (by rfl) ⟨27443690, by rfl⟩ : syracuseStep 36591587 = 54887381) B54887381
theorem B877337 : Blo 259821 877337 := bstep (se 2 (by rfl) ⟨329001, by rfl⟩ : syracuseStep 877337 = 658003) B658003
theorem B746587 : Blo 259821 746587 := bstep (se 1 (by rfl) ⟨559940, by rfl⟩ : syracuseStep 746587 = 1119881) B1119881
theorem B878525 : Blo 259821 878525 := bstep (se 3 (by rfl) ⟨164723, by rfl⟩ : syracuseStep 878525 = 329447) B329447
theorem B878687 : Blo 259821 878687 := bstep (se 1 (by rfl) ⟨659015, by rfl⟩ : syracuseStep 878687 = 1318031) B1318031
theorem B1993085 : Blo 259821 1993085 := bstep (se 3 (by rfl) ⟨373703, by rfl⟩ : syracuseStep 1993085 = 747407) B747407
theorem B1600361 : Blo 259821 1600361 := bstep (se 2 (by rfl) ⟨600135, by rfl⟩ : syracuseStep 1600361 = 1200271) B1200271
theorem B748399 : Blo 259821 748399 := bstep (se 1 (by rfl) ⟨561299, by rfl⟩ : syracuseStep 748399 = 1122599) B1122599
theorem B2223085 : Blo 259821 2223085 := bstep (se 3 (by rfl) ⟨416828, by rfl⟩ : syracuseStep 2223085 = 833657) B833657
theorem B879983 : Blo 259821 879983 := bstep (se 1 (by rfl) ⟨659987, by rfl⟩ : syracuseStep 879983 = 1319975) B1319975
theorem B13889531 : Blo 259821 13889531 := bstep (se 1 (by rfl) ⟨10417148, by rfl⟩ : syracuseStep 13889531 = 20834297) B20834297
theorem B585935 : Blo 259821 585935 := bstep (se 1 (by rfl) ⟨439451, by rfl⟩ : syracuseStep 585935 = 878903) B878903
theorem B2224421 : Blo 259821 2224421 := bstep (se 4 (by rfl) ⟨208539, by rfl⟩ : syracuseStep 2224421 = 417079) B417079
theorem B881711 : Blo 259821 881711 := bstep (se 1 (by rfl) ⟨661283, by rfl⟩ : syracuseStep 881711 = 1322567) B1322567
theorem B390281 : Blo 259821 390281 := bstep (se 2 (by rfl) ⟨146355, by rfl⟩ : syracuseStep 390281 = 292711) B292711
theorem B1012961 : Blo 259821 1012961 := bstep (se 2 (by rfl) ⟨379860, by rfl⟩ : syracuseStep 1012961 = 759721) B759721
theorem B587087 : Blo 259821 587087 := bstep (se 1 (by rfl) ⟨440315, by rfl⟩ : syracuseStep 587087 = 880631) B880631
theorem B259867 : Blo 259821 259867 := bstep (se 1 (by rfl) ⟨194900, by rfl⟩ : syracuseStep 259867 = 389801) B389801
theorem B587663 : Blo 259821 587663 := bstep (se 1 (by rfl) ⟨440747, by rfl⟩ : syracuseStep 587663 = 881495) B881495
theorem B882575 : Blo 259821 882575 := bstep (se 1 (by rfl) ⟨661931, by rfl⟩ : syracuseStep 882575 = 1323863) B1323863
theorem B391451 : Blo 259821 391451 := bstep (se 1 (by rfl) ⟨293588, by rfl⟩ : syracuseStep 391451 = 587177) B587177
theorem B588059 : Blo 259821 588059 := bstep (se 1 (by rfl) ⟨441044, by rfl⟩ : syracuseStep 588059 = 882089) B882089
theorem B3045671 : Blo 259821 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B391487 : Blo 259821 391487 := bstep (se 1 (by rfl) ⟨293615, by rfl⟩ : syracuseStep 391487 = 587231) B587231
theorem B588095 : Blo 259821 588095 := bstep (se 1 (by rfl) ⟨441071, by rfl⟩ : syracuseStep 588095 = 882143) B882143
theorem B391919 : Blo 259821 391919 := bstep (se 1 (by rfl) ⟨293939, by rfl⟩ : syracuseStep 391919 = 587879) B587879
theorem B260891 : Blo 259821 260891 := bstep (se 1 (by rfl) ⟨195668, by rfl⟩ : syracuseStep 260891 = 391337) B391337
theorem B2882587 : Blo 259821 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B883817 : Blo 259821 883817 := bstep (se 2 (by rfl) ⟨331431, by rfl⟩ : syracuseStep 883817 = 662863) B662863
theorem B588959 : Blo 259821 588959 := bstep (se 1 (by rfl) ⟨441719, by rfl⟩ : syracuseStep 588959 = 883439) B883439
theorem B393191 : Blo 259821 393191 := bstep (se 1 (by rfl) ⟨294893, by rfl⟩ : syracuseStep 393191 = 589787) B589787
theorem B262215 : Blo 259821 262215 := bstep (se 1 (by rfl) ⟨196661, by rfl⟩ : syracuseStep 262215 = 393323) B393323
theorem B1671263 : Blo 259821 1671263 := bstep (se 1 (by rfl) ⟨1253447, by rfl⟩ : syracuseStep 1671263 = 2506895) B2506895
theorem B16220371 : Blo 259821 16220371 := bstep (se 1 (by rfl) ⟨12165278, by rfl⟩ : syracuseStep 16220371 = 24330557) B24330557
theorem B262427 : Blo 259821 262427 := bstep (se 1 (by rfl) ⟨196820, by rfl⟩ : syracuseStep 262427 = 393641) B393641
theorem B393551 : Blo 259821 393551 := bstep (se 1 (by rfl) ⟨295163, by rfl⟩ : syracuseStep 393551 = 590327) B590327
theorem B3342829 : Blo 259821 3342829 := bstep (se 3 (by rfl) ⟨626780, by rfl⟩ : syracuseStep 3342829 = 1253561) B1253561
theorem B590363 : Blo 259821 590363 := bstep (se 1 (by rfl) ⟨442772, by rfl⟩ : syracuseStep 590363 = 885545) B885545
theorem B262783 : Blo 259821 262783 := bstep (se 1 (by rfl) ⟨197087, by rfl⟩ : syracuseStep 262783 = 394175) B394175
theorem B393947 : Blo 259821 393947 := bstep (se 1 (by rfl) ⟨295460, by rfl⟩ : syracuseStep 393947 = 590921) B590921
theorem B590561 : Blo 259821 590561 := bstep (se 2 (by rfl) ⟨221460, by rfl⟩ : syracuseStep 590561 = 442921) B442921
theorem B295771 : Blo 259821 295771 := bstep (se 1 (by rfl) ⟨221828, by rfl⟩ : syracuseStep 295771 = 443657) B443657
theorem B263039 : Blo 259821 263039 := bstep (se 1 (by rfl) ⟨197279, by rfl⟩ : syracuseStep 263039 = 394559) B394559
theorem B263399 : Blo 259821 263399 := bstep (se 1 (by rfl) ⟨197549, by rfl⟩ : syracuseStep 263399 = 395099) B395099
theorem B591335 : Blo 259821 591335 := bstep (se 1 (by rfl) ⟨443501, by rfl⟩ : syracuseStep 591335 = 887003) B887003
theorem B263655 : Blo 259821 263655 := bstep (se 1 (by rfl) ⟨197741, by rfl⟩ : syracuseStep 263655 = 395483) B395483
theorem B591497 : Blo 259821 591497 := bstep (se 2 (by rfl) ⟨221811, by rfl⟩ : syracuseStep 591497 = 443623) B443623
theorem B22939307 : Blo 259821 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B591983 : Blo 259821 591983 := bstep (se 1 (by rfl) ⟨443987, by rfl⟩ : syracuseStep 591983 = 887975) B887975
theorem B592091 : Blo 259821 592091 := bstep (se 1 (by rfl) ⟨444068, by rfl⟩ : syracuseStep 592091 = 888137) B888137
theorem B1280329 : Blo 259821 1280329 := bstep (se 2 (by rfl) ⟨480123, by rfl⟩ : syracuseStep 1280329 = 960247) B960247
theorem B887273 : Blo 259821 887273 := bstep (se 2 (by rfl) ⟨332727, by rfl⟩ : syracuseStep 887273 = 665455) B665455
theorem B1673723 : Blo 259821 1673723 := bstep (se 1 (by rfl) ⟨1255292, by rfl⟩ : syracuseStep 1673723 = 2510585) B2510585
theorem B396095 : Blo 259821 396095 := bstep (se 1 (by rfl) ⟨297071, by rfl⟩ : syracuseStep 396095 = 594143) B594143
theorem B625801 : Blo 259821 625801 := bstep (se 2 (by rfl) ⟨234675, by rfl⟩ : syracuseStep 625801 = 469351) B469351
theorem B593063 : Blo 259821 593063 := bstep (se 1 (by rfl) ⟨444797, by rfl⟩ : syracuseStep 593063 = 889595) B889595
theorem B593135 : Blo 259821 593135 := bstep (se 1 (by rfl) ⟨444851, by rfl⟩ : syracuseStep 593135 = 889703) B889703
theorem B331391 : Blo 259821 331391 := bstep (se 1 (by rfl) ⟨248543, by rfl⟩ : syracuseStep 331391 = 497087) B497087
theorem B659947 : Blo 259821 659947 := bstep (se 1 (by rfl) ⟨494960, by rfl⟩ : syracuseStep 659947 = 989921) B989921
theorem B660059 : Blo 259821 660059 := bstep (se 1 (by rfl) ⟨495044, by rfl⟩ : syracuseStep 660059 = 990089) B990089
theorem B660271 : Blo 259821 660271 := bstep (se 1 (by rfl) ⟨495203, by rfl⟩ : syracuseStep 660271 = 990407) B990407
theorem B660919 : Blo 259821 660919 := bstep (se 1 (by rfl) ⟨495689, by rfl⟩ : syracuseStep 660919 = 991379) B991379
theorem B661679 : Blo 259821 661679 := bstep (se 1 (by rfl) ⟨496259, by rfl⟩ : syracuseStep 661679 = 992519) B992519
theorem B2234567 : Blo 259821 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B1120823 : Blo 259821 1120823 := bstep (se 1 (by rfl) ⟨840617, by rfl⟩ : syracuseStep 1120823 = 1681235) B1681235
theorem B1973159 : Blo 259821 1973159 := bstep (se 1 (by rfl) ⟨1479869, by rfl⟩ : syracuseStep 1973159 = 2959739) B2959739
theorem B662975 : Blo 259821 662975 := bstep (se 1 (by rfl) ⟨497231, by rfl⟩ : syracuseStep 662975 = 994463) B994463
theorem B1121863 : Blo 259821 1121863 := bstep (se 1 (by rfl) ⟨841397, by rfl⟩ : syracuseStep 1121863 = 1682795) B1682795
theorem B1482947 : Blo 259821 1482947 := bstep (se 1 (by rfl) ⟨1112210, by rfl⟩ : syracuseStep 1482947 = 2224421) B2224421
theorem B3843449 : Blo 259821 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B534815 : Blo 259821 534815 := bstep (se 1 (by rfl) ⟨401111, by rfl⟩ : syracuseStep 534815 = 802223) B802223
theorem B2403755 : Blo 259821 2403755 := bstep (se 1 (by rfl) ⟨1802816, by rfl⟩ : syracuseStep 2403755 = 3605633) B3605633
theorem B9318253 : Blo 259821 9318253 := bstep (se 3 (by rfl) ⟨1747172, by rfl⟩ : syracuseStep 9318253 = 3494345) B3494345
theorem B1257407 : Blo 259821 1257407 := bstep (se 1 (by rfl) ⟨943055, by rfl⟩ : syracuseStep 1257407 = 1886111) B1886111
theorem B995449 : Blo 259821 995449 := bstep (se 2 (by rfl) ⟨373293, by rfl⟩ : syracuseStep 995449 = 746587) B746587
theorem B373339 : Blo 259821 373339 := bstep (se 1 (by rfl) ⟨280004, by rfl⟩ : syracuseStep 373339 = 560009) B560009
theorem B38679403 : Blo 259821 38679403 := bstep (se 1 (by rfl) ⟨29009552, by rfl⟩ : syracuseStep 38679403 = 58019105) B58019105
theorem B8238635 : Blo 259821 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B6665975 : Blo 259821 6665975 := bstep (se 1 (by rfl) ⟨4999481, by rfl⟩ : syracuseStep 6665975 = 9998963) B9998963
theorem B997865 : Blo 259821 997865 := bstep (se 2 (by rfl) ⟨374199, by rfl⟩ : syracuseStep 997865 = 748399) B748399
theorem B2964113 : Blo 259821 2964113 := bstep (se 2 (by rfl) ⟨1111542, by rfl⟩ : syracuseStep 2964113 = 2223085) B2223085
theorem B24394391 : Blo 259821 24394391 := bstep (se 1 (by rfl) ⟨18295793, by rfl⟩ : syracuseStep 24394391 = 36591587) B36591587
theorem B441551 : Blo 259821 441551 := bstep (se 1 (by rfl) ⟨331163, by rfl⟩ : syracuseStep 441551 = 662327) B662327
theorem B442415 : Blo 259821 442415 := bstep (se 1 (by rfl) ⟨331811, by rfl⟩ : syracuseStep 442415 = 663623) B663623
theorem B1328723 : Blo 259821 1328723 := bstep (se 1 (by rfl) ⟨996542, by rfl⟩ : syracuseStep 1328723 = 1993085) B1993085
theorem B4474601 : Blo 259821 4474601 := bstep (se 2 (by rfl) ⟨1677975, by rfl⟩ : syracuseStep 4474601 = 3355951) B3355951
theorem B2279191 : Blo 259821 2279191 := bstep (se 1 (by rfl) ⟨1709393, by rfl⟩ : syracuseStep 2279191 = 3418787) B3418787
theorem B444251 : Blo 259821 444251 := bstep (se 1 (by rfl) ⟨333188, by rfl⟩ : syracuseStep 444251 = 666377) B666377
theorem B1066907 : Blo 259821 1066907 := bstep (se 1 (by rfl) ⟨800180, by rfl⟩ : syracuseStep 1066907 = 1600361) B1600361
theorem B444703 : Blo 259821 444703 := bstep (se 1 (by rfl) ⟨333527, by rfl⟩ : syracuseStep 444703 = 667055) B667055
theorem B9259687 : Blo 259821 9259687 := bstep (se 1 (by rfl) ⟨6944765, by rfl⟩ : syracuseStep 9259687 = 13889531) B13889531
theorem B1624943 : Blo 259821 1624943 := bstep (se 1 (by rfl) ⟨1218707, by rfl⟩ : syracuseStep 1624943 = 2437415) B2437415
theorem B675307 : Blo 259821 675307 := bstep (se 1 (by rfl) ⟨506480, by rfl⟩ : syracuseStep 675307 = 1012961) B1012961
theorem B1594889 : Blo 259821 1594889 := bstep (se 2 (by rfl) ⟨598083, by rfl⟩ : syracuseStep 1594889 = 1196167) B1196167
theorem B30627841 : Blo 259821 30627841 := bstep (se 2 (by rfl) ⟨11485440, by rfl⟩ : syracuseStep 30627841 = 22970881) B22970881
theorem B448583 : Blo 259821 448583 := bstep (se 1 (by rfl) ⟨336437, by rfl⟩ : syracuseStep 448583 = 672875) B672875
theorem B448679 : Blo 259821 448679 := bstep (se 1 (by rfl) ⟨336509, by rfl⟩ : syracuseStep 448679 = 673019) B673019
theorem B2382143 : Blo 259821 2382143 := bstep (se 1 (by rfl) ⟨1786607, by rfl⟩ : syracuseStep 2382143 = 3573215) B3573215
theorem B1333583 : Blo 259821 1333583 := bstep (se 1 (by rfl) ⟨1000187, by rfl⟩ : syracuseStep 1333583 = 2000375) B2000375
theorem B809423 : Blo 259821 809423 := bstep (se 1 (by rfl) ⟨607067, by rfl⟩ : syracuseStep 809423 = 1214135) B1214135
theorem B12114683 : Blo 259821 12114683 := bstep (se 1 (by rfl) ⟨9086012, by rfl⟩ : syracuseStep 12114683 = 18172025) B18172025
theorem B9329627 : Blo 259821 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B3005855 : Blo 259821 3005855 := bstep (se 1 (by rfl) ⟨2254391, by rfl⟩ : syracuseStep 3005855 = 4508783) B4508783
theorem B1334717 : Blo 259821 1334717 := bstep (se 3 (by rfl) ⟨250259, by rfl⟩ : syracuseStep 1334717 = 500519) B500519
theorem B909215 : Blo 259821 909215 := bstep (se 1 (by rfl) ⟨681911, by rfl⟩ : syracuseStep 909215 = 1363823) B1363823
theorem B1794383 : Blo 259821 1794383 := bstep (se 1 (by rfl) ⟨1345787, by rfl⟩ : syracuseStep 1794383 = 2691575) B2691575
theorem B8545499 : Blo 259821 8545499 := bstep (se 1 (by rfl) ⟨6409124, by rfl⟩ : syracuseStep 8545499 = 12818249) B12818249
theorem B879443 : Blo 259821 879443 := bstep (se 1 (by rfl) ⟨659582, by rfl⟩ : syracuseStep 879443 = 1319165) B1319165
theorem B879497 : Blo 259821 879497 := bstep (se 2 (by rfl) ⟨329811, by rfl⟩ : syracuseStep 879497 = 659623) B659623
theorem B584891 : Blo 259821 584891 := bstep (se 1 (by rfl) ⟨438668, by rfl⟩ : syracuseStep 584891 = 877337) B877337
theorem B585017 : Blo 259821 585017 := bstep (se 2 (by rfl) ⟨219381, by rfl⟩ : syracuseStep 585017 = 438763) B438763
theorem B25325459 : Blo 259821 25325459 := bstep (se 1 (by rfl) ⟨18994094, by rfl⟩ : syracuseStep 25325459 = 37988189) B37988189
theorem B585683 : Blo 259821 585683 := bstep (se 1 (by rfl) ⟨439262, by rfl⟩ : syracuseStep 585683 = 878525) B878525
theorem B585791 : Blo 259821 585791 := bstep (se 1 (by rfl) ⟨439343, by rfl⟩ : syracuseStep 585791 = 878687) B878687
theorem B109801615 : Blo 259821 109801615 := bstep (se 1 (by rfl) ⟨82351211, by rfl⟩ : syracuseStep 109801615 = 164702423) B164702423
theorem B586655 : Blo 259821 586655 := bstep (se 1 (by rfl) ⟨439991, by rfl⟩ : syracuseStep 586655 = 879983) B879983
theorem B390623 : Blo 259821 390623 := bstep (se 1 (by rfl) ⟨292967, by rfl⟩ : syracuseStep 390623 = 585935) B585935
theorem B882683 : Blo 259821 882683 := bstep (se 1 (by rfl) ⟨662012, by rfl⟩ : syracuseStep 882683 = 1324025) B1324025
theorem B587807 : Blo 259821 587807 := bstep (se 1 (by rfl) ⟨440855, by rfl⟩ : syracuseStep 587807 = 881711) B881711
theorem B260187 : Blo 259821 260187 := bstep (se 1 (by rfl) ⟨195140, by rfl⟩ : syracuseStep 260187 = 390281) B390281
theorem B391391 : Blo 259821 391391 := bstep (se 1 (by rfl) ⟨293543, by rfl⟩ : syracuseStep 391391 = 587087) B587087
theorem B391775 : Blo 259821 391775 := bstep (se 1 (by rfl) ⟨293831, by rfl⟩ : syracuseStep 391775 = 587663) B587663
theorem B588383 : Blo 259821 588383 := bstep (se 1 (by rfl) ⟨441287, by rfl⟩ : syracuseStep 588383 = 882575) B882575
theorem B948851 : Blo 259821 948851 := bstep (se 1 (by rfl) ⟨711638, by rfl⟩ : syracuseStep 948851 = 1423277) B1423277
theorem B2849579 : Blo 259821 2849579 := bstep (se 1 (by rfl) ⟨2137184, by rfl⟩ : syracuseStep 2849579 = 4274369) B4274369
theorem B260967 : Blo 259821 260967 := bstep (se 1 (by rfl) ⟨195725, by rfl⟩ : syracuseStep 260967 = 391451) B391451
theorem B392039 : Blo 259821 392039 := bstep (se 1 (by rfl) ⟨294029, by rfl⟩ : syracuseStep 392039 = 588059) B588059
theorem B2030447 : Blo 259821 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B260991 : Blo 259821 260991 := bstep (se 1 (by rfl) ⟨195743, by rfl⟩ : syracuseStep 260991 = 391487) B391487
theorem B392063 : Blo 259821 392063 := bstep (se 1 (by rfl) ⟨294047, by rfl⟩ : syracuseStep 392063 = 588095) B588095
theorem B261279 : Blo 259821 261279 := bstep (se 1 (by rfl) ⟨195959, by rfl⟩ : syracuseStep 261279 = 391919) B391919
theorem B589211 : Blo 259821 589211 := bstep (se 1 (by rfl) ⟨441908, by rfl⟩ : syracuseStep 589211 = 883817) B883817
theorem B392639 : Blo 259821 392639 := bstep (se 1 (by rfl) ⟨294479, by rfl⟩ : syracuseStep 392639 = 588959) B588959
theorem B262127 : Blo 259821 262127 := bstep (se 1 (by rfl) ⟨196595, by rfl⟩ : syracuseStep 262127 = 393191) B393191
theorem B294943 : Blo 259821 294943 := bstep (se 1 (by rfl) ⟨221207, by rfl⟩ : syracuseStep 294943 = 442415) B442415
theorem B1114175 : Blo 259821 1114175 := bstep (se 1 (by rfl) ⟨835631, by rfl⟩ : syracuseStep 1114175 = 1671263) B1671263
theorem B262367 : Blo 259821 262367 := bstep (se 1 (by rfl) ⟨196775, by rfl⟩ : syracuseStep 262367 = 393551) B393551
theorem B21627161 : Blo 259821 21627161 := bstep (se 2 (by rfl) ⟨8110185, by rfl⟩ : syracuseStep 21627161 = 16220371) B16220371
theorem B393575 : Blo 259821 393575 := bstep (se 1 (by rfl) ⟨295181, by rfl⟩ : syracuseStep 393575 = 590363) B590363
theorem B262631 : Blo 259821 262631 := bstep (se 1 (by rfl) ⟨196973, by rfl⟩ : syracuseStep 262631 = 393947) B393947
theorem B393707 : Blo 259821 393707 := bstep (se 1 (by rfl) ⟨295280, by rfl⟩ : syracuseStep 393707 = 590561) B590561
theorem B4457105 : Blo 259821 4457105 := bstep (se 2 (by rfl) ⟨1671414, by rfl⟩ : syracuseStep 4457105 = 3342829) B3342829
theorem B394223 : Blo 259821 394223 := bstep (se 1 (by rfl) ⟨295667, by rfl⟩ : syracuseStep 394223 = 591335) B591335
theorem B885815 : Blo 259821 885815 := bstep (se 1 (by rfl) ⟨664361, by rfl⟩ : syracuseStep 885815 = 1328723) B1328723
theorem B394331 : Blo 259821 394331 := bstep (se 1 (by rfl) ⟨295748, by rfl⟩ : syracuseStep 394331 = 591497) B591497
theorem B394361 : Blo 259821 394361 := bstep (se 2 (by rfl) ⟨147885, by rfl⟩ : syracuseStep 394361 = 295771) B295771
theorem B2983067 : Blo 259821 2983067 := bstep (se 1 (by rfl) ⟨2237300, by rfl⟩ : syracuseStep 2983067 = 4474601) B4474601
theorem B296167 : Blo 259821 296167 := bstep (se 1 (by rfl) ⟨222125, by rfl⟩ : syracuseStep 296167 = 444251) B444251
theorem B394655 : Blo 259821 394655 := bstep (se 1 (by rfl) ⟨295991, by rfl⟩ : syracuseStep 394655 = 591983) B591983
theorem B394727 : Blo 259821 394727 := bstep (se 1 (by rfl) ⟨296045, by rfl⟩ : syracuseStep 394727 = 592091) B592091
theorem B591515 : Blo 259821 591515 := bstep (se 1 (by rfl) ⟨443636, by rfl⟩ : syracuseStep 591515 = 887273) B887273
theorem B1115815 : Blo 259821 1115815 := bstep (se 1 (by rfl) ⟨836861, by rfl⟩ : syracuseStep 1115815 = 1673723) B1673723
theorem B1083295 : Blo 259821 1083295 := bstep (se 1 (by rfl) ⟨812471, by rfl⟩ : syracuseStep 1083295 = 1624943) B1624943
theorem B395375 : Blo 259821 395375 := bstep (se 1 (by rfl) ⟨296531, by rfl⟩ : syracuseStep 395375 = 593063) B593063
theorem B395423 : Blo 259821 395423 := bstep (se 1 (by rfl) ⟨296567, by rfl⟩ : syracuseStep 395423 = 593135) B593135
theorem B592937 : Blo 259821 592937 := bstep (se 2 (by rfl) ⟨222351, by rfl⟩ : syracuseStep 592937 = 444703) B444703
theorem B49384997 : Blo 259821 49384997 := bstep (se 4 (by rfl) ⟨4629843, by rfl⟩ : syracuseStep 49384997 = 9259687) B9259687
theorem B299119 : Blo 259821 299119 := bstep (se 1 (by rfl) ⟨224339, by rfl⟩ : syracuseStep 299119 = 448679) B448679
theorem B889055 : Blo 259821 889055 := bstep (se 1 (by rfl) ⟨666791, by rfl⟩ : syracuseStep 889055 = 1333583) B1333583
theorem B1315439 : Blo 259821 1315439 := bstep (se 1 (by rfl) ⟨986579, by rfl⟩ : syracuseStep 1315439 = 1973159) B1973159
theorem B2003903 : Blo 259821 2003903 := bstep (se 1 (by rfl) ⟨1502927, by rfl⟩ : syracuseStep 2003903 = 3005855) B3005855
theorem B889811 : Blo 259821 889811 := bstep (se 1 (by rfl) ⟨667358, by rfl⟩ : syracuseStep 889811 = 1334717) B1334717
theorem B12424337 : Blo 259821 12424337 := bstep (se 2 (by rfl) ⟨4659126, by rfl⟩ : syracuseStep 12424337 = 9318253) B9318253
theorem B988631 : Blo 259821 988631 := bstep (se 1 (by rfl) ⟨741473, by rfl⟩ : syracuseStep 988631 = 1482947) B1482947
theorem B2562299 : Blo 259821 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B1056253 : Blo 259821 1056253 := bstep (se 3 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 1056253 = 396095) B396095
theorem B24879005 : Blo 259821 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B16883639 : Blo 259821 16883639 := bstep (se 1 (by rfl) ⟨12662729, by rfl⟩ : syracuseStep 16883639 = 25325459) B25325459
theorem B40837121 : Blo 259821 40837121 := bstep (se 2 (by rfl) ⟨15313920, by rfl⟩ : syracuseStep 40837121 = 30627841) B30627841
theorem B665243 : Blo 259821 665243 := bstep (se 1 (by rfl) ⟨498932, by rfl⟩ : syracuseStep 665243 = 997865) B997865
theorem B632567 : Blo 259821 632567 := bstep (se 1 (by rfl) ⟨474425, by rfl⟩ : syracuseStep 632567 = 948851) B948851
theorem B1976075 : Blo 259821 1976075 := bstep (se 1 (by rfl) ⟨1482056, by rfl⟩ : syracuseStep 1976075 = 2964113) B2964113
theorem B16262927 : Blo 259821 16262927 := bstep (se 1 (by rfl) ⟨12197195, by rfl⟩ : syracuseStep 16262927 = 24394391) B24394391
theorem B1353631 : Blo 259821 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B440039 : Blo 259821 440039 := bstep (se 1 (by rfl) ⟨330029, by rfl⟩ : syracuseStep 440039 = 660059) B660059
theorem B1063259 : Blo 259821 1063259 := bstep (se 1 (by rfl) ⟨797444, by rfl⟩ : syracuseStep 1063259 = 1594889) B1594889
theorem B441119 : Blo 259821 441119 := bstep (se 1 (by rfl) ⟨330839, by rfl⟩ : syracuseStep 441119 = 661679) B661679
theorem B1489711 : Blo 259821 1489711 := bstep (se 1 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 1489711 = 2234567) B2234567
theorem B834401 : Blo 259821 834401 := bstep (se 2 (by rfl) ⟨312900, by rfl⟩ : syracuseStep 834401 = 625801) B625801
theorem B539615 : Blo 259821 539615 := bstep (se 1 (by rfl) ⟨404711, by rfl⟩ : syracuseStep 539615 = 809423) B809423
theorem B8076455 : Blo 259821 8076455 := bstep (se 1 (by rfl) ⟨6057341, by rfl⟩ : syracuseStep 8076455 = 12114683) B12114683
theorem B900409 : Blo 259821 900409 := bstep (se 2 (by rfl) ⟨337653, by rfl⟩ : syracuseStep 900409 = 675307) B675307
theorem B441983 : Blo 259821 441983 := bstep (se 1 (by rfl) ⟨331487, by rfl⟩ : syracuseStep 441983 = 662975) B662975
theorem B606143 : Blo 259821 606143 := bstep (se 1 (by rfl) ⟨454607, by rfl⟩ : syracuseStep 606143 = 909215) B909215
theorem B1327265 : Blo 259821 1327265 := bstep (se 2 (by rfl) ⟨497724, by rfl⟩ : syracuseStep 1327265 = 995449) B995449
theorem B1196221 : Blo 259821 1196221 := bstep (se 3 (by rfl) ⟨224291, by rfl⟩ : syracuseStep 1196221 = 448583) B448583
theorem B1196255 : Blo 259821 1196255 := bstep (se 1 (by rfl) ⟨897191, by rfl⟩ : syracuseStep 1196255 = 1794383) B1794383
theorem B27313685 : Blo 259821 27313685 := bstep (se 6 (by rfl) ⟨640164, by rfl⟩ : syracuseStep 27313685 = 1280329) B1280329
theorem B838271 : Blo 259821 838271 := bstep (se 1 (by rfl) ⟨628703, by rfl⟩ : syracuseStep 838271 = 1257407) B1257407
theorem B5492423 : Blo 259821 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B4443983 : Blo 259821 4443983 := bstep (se 1 (by rfl) ⟨3332987, by rfl⟩ : syracuseStep 4443983 = 6665975) B6665975
theorem B1495817 : Blo 259821 1495817 := bstep (se 2 (by rfl) ⟨560931, by rfl⟩ : syracuseStep 1495817 = 1121863) B1121863
theorem B15292871 : Blo 259821 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B711271 : Blo 259821 711271 := bstep (se 1 (by rfl) ⟨533453, by rfl⟩ : syracuseStep 711271 = 1066907) B1066907
theorem B3038921 : Blo 259821 3038921 := bstep (se 2 (by rfl) ⟨1139595, by rfl⟩ : syracuseStep 3038921 = 2279191) B2279191
theorem B1991141 : Blo 259821 1991141 := bstep (se 4 (by rfl) ⟨186669, by rfl⟩ : syracuseStep 1991141 = 373339) B373339
theorem B747215 : Blo 259821 747215 := bstep (se 1 (by rfl) ⟨560411, by rfl⟩ : syracuseStep 747215 = 1120823) B1120823
theorem B146402153 : Blo 259821 146402153 := bstep (se 2 (by rfl) ⟨54900807, by rfl⟩ : syracuseStep 146402153 = 109801615) B109801615
theorem B879929 : Blo 259821 879929 := bstep (se 2 (by rfl) ⟨329973, by rfl⟩ : syracuseStep 879929 = 659947) B659947
theorem B5696999 : Blo 259821 5696999 := bstep (se 1 (by rfl) ⟨4272749, by rfl⟩ : syracuseStep 5696999 = 8545499) B8545499
theorem B6352381 : Blo 259821 6352381 := bstep (se 3 (by rfl) ⟨1191071, by rfl⟩ : syracuseStep 6352381 = 2382143) B2382143
theorem B880361 : Blo 259821 880361 := bstep (se 2 (by rfl) ⟨330135, by rfl⟩ : syracuseStep 880361 = 660271) B660271
theorem B51572537 : Blo 259821 51572537 := bstep (se 2 (by rfl) ⟨19339701, by rfl⟩ : syracuseStep 51572537 = 38679403) B38679403
theorem B356543 : Blo 259821 356543 := bstep (se 1 (by rfl) ⟨267407, by rfl⟩ : syracuseStep 356543 = 534815) B534815
theorem B586295 : Blo 259821 586295 := bstep (se 1 (by rfl) ⟨439721, by rfl⟩ : syracuseStep 586295 = 879443) B879443
theorem B881225 : Blo 259821 881225 := bstep (se 2 (by rfl) ⟨330459, by rfl⟩ : syracuseStep 881225 = 660919) B660919
theorem B586331 : Blo 259821 586331 := bstep (se 1 (by rfl) ⟨439748, by rfl⟩ : syracuseStep 586331 = 879497) B879497
theorem B389927 : Blo 259821 389927 := bstep (se 1 (by rfl) ⟨292445, by rfl⟩ : syracuseStep 389927 = 584891) B584891
theorem B390011 : Blo 259821 390011 := bstep (se 1 (by rfl) ⟨292508, by rfl⟩ : syracuseStep 390011 = 585017) B585017
theorem B1602503 : Blo 259821 1602503 := bstep (se 1 (by rfl) ⟨1201877, by rfl⟩ : syracuseStep 1602503 = 2403755) B2403755
theorem B390455 : Blo 259821 390455 := bstep (se 1 (by rfl) ⟨292841, by rfl⟩ : syracuseStep 390455 = 585683) B585683
theorem B390527 : Blo 259821 390527 := bstep (se 1 (by rfl) ⟨292895, by rfl⟩ : syracuseStep 390527 = 585791) B585791
theorem B391103 : Blo 259821 391103 := bstep (se 1 (by rfl) ⟨293327, by rfl⟩ : syracuseStep 391103 = 586655) B586655
theorem B260415 : Blo 259821 260415 := bstep (se 1 (by rfl) ⟨195311, by rfl⟩ : syracuseStep 260415 = 390623) B390623
theorem B588455 : Blo 259821 588455 := bstep (se 1 (by rfl) ⟨441341, by rfl⟩ : syracuseStep 588455 = 882683) B882683
theorem B391871 : Blo 259821 391871 := bstep (se 1 (by rfl) ⟨293903, by rfl⟩ : syracuseStep 391871 = 587807) B587807
theorem B260927 : Blo 259821 260927 := bstep (se 1 (by rfl) ⟨195695, by rfl⟩ : syracuseStep 260927 = 391391) B391391
theorem B883709 : Blo 259821 883709 := bstep (se 3 (by rfl) ⟨165695, by rfl⟩ : syracuseStep 883709 = 331391) B331391
theorem B261183 : Blo 259821 261183 := bstep (se 1 (by rfl) ⟨195887, by rfl⟩ : syracuseStep 261183 = 391775) B391775
theorem B392255 : Blo 259821 392255 := bstep (se 1 (by rfl) ⟨294191, by rfl⟩ : syracuseStep 392255 = 588383) B588383
theorem B1899719 : Blo 259821 1899719 := bstep (se 1 (by rfl) ⟨1424789, by rfl⟩ : syracuseStep 1899719 = 2849579) B2849579
theorem B261359 : Blo 259821 261359 := bstep (se 1 (by rfl) ⟨196019, by rfl⟩ : syracuseStep 261359 = 392039) B392039
theorem B261375 : Blo 259821 261375 := bstep (se 1 (by rfl) ⟨196031, by rfl⟩ : syracuseStep 261375 = 392063) B392063
theorem B294367 : Blo 259821 294367 := bstep (se 1 (by rfl) ⟨220775, by rfl⟩ : syracuseStep 294367 = 441551) B441551
theorem B392807 : Blo 259821 392807 := bstep (se 1 (by rfl) ⟨294605, by rfl⟩ : syracuseStep 392807 = 589211) B589211
theorem B261759 : Blo 259821 261759 := bstep (se 1 (by rfl) ⟨196319, by rfl⟩ : syracuseStep 261759 = 392639) B392639
theorem B393257 : Blo 259821 393257 := bstep (se 2 (by rfl) ⟨147471, by rfl⟩ : syracuseStep 393257 = 294943) B294943
theorem B884843 : Blo 259821 884843 := bstep (se 1 (by rfl) ⟨663632, by rfl⟩ : syracuseStep 884843 = 1327265) B1327265
theorem B14418107 : Blo 259821 14418107 := bstep (se 1 (by rfl) ⟨10813580, by rfl⟩ : syracuseStep 14418107 = 21627161) B21627161
theorem B262383 : Blo 259821 262383 := bstep (se 1 (by rfl) ⟨196787, by rfl⟩ : syracuseStep 262383 = 393575) B393575
theorem B262471 : Blo 259821 262471 := bstep (se 1 (by rfl) ⟨196853, by rfl⟩ : syracuseStep 262471 = 393707) B393707
theorem B262815 : Blo 259821 262815 := bstep (se 1 (by rfl) ⟨197111, by rfl⟩ : syracuseStep 262815 = 394223) B394223
theorem B590543 : Blo 259821 590543 := bstep (se 1 (by rfl) ⟨442907, by rfl⟩ : syracuseStep 590543 = 885815) B885815
theorem B262887 : Blo 259821 262887 := bstep (se 1 (by rfl) ⟨197165, by rfl⟩ : syracuseStep 262887 = 394331) B394331
theorem B262907 : Blo 259821 262907 := bstep (se 1 (by rfl) ⟨197180, by rfl⟩ : syracuseStep 262907 = 394361) B394361
theorem B263103 : Blo 259821 263103 := bstep (se 1 (by rfl) ⟨197327, by rfl⟩ : syracuseStep 263103 = 394655) B394655
theorem B263151 : Blo 259821 263151 := bstep (se 1 (by rfl) ⟨197363, by rfl⟩ : syracuseStep 263151 = 394727) B394727
theorem B394343 : Blo 259821 394343 := bstep (se 1 (by rfl) ⟨295757, by rfl⟩ : syracuseStep 394343 = 591515) B591515
theorem B263583 : Blo 259821 263583 := bstep (se 1 (by rfl) ⟨197687, by rfl⟩ : syracuseStep 263583 = 395375) B395375
theorem B263615 : Blo 259821 263615 := bstep (se 1 (by rfl) ⟨197711, by rfl⟩ : syracuseStep 263615 = 395423) B395423
theorem B394889 : Blo 259821 394889 := bstep (se 2 (by rfl) ⟨148083, by rfl⟩ : syracuseStep 394889 = 296167) B296167
theorem B558847 : Blo 259821 558847 := bstep (se 1 (by rfl) ⟨419135, by rfl⟩ : syracuseStep 558847 = 838271) B838271
theorem B3803125 : Blo 259821 3803125 := bstep (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) B356543
theorem B395291 : Blo 259821 395291 := bstep (se 1 (by rfl) ⟨296468, by rfl⟩ : syracuseStep 395291 = 592937) B592937
theorem B1804841 : Blo 259821 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B592703 : Blo 259821 592703 := bstep (se 1 (by rfl) ⟨444527, by rfl⟩ : syracuseStep 592703 = 889055) B889055
theorem B593207 : Blo 259821 593207 := bstep (se 1 (by rfl) ⟨444905, by rfl⟩ : syracuseStep 593207 = 889811) B889811
theorem B659087 : Blo 259821 659087 := bstep (se 1 (by rfl) ⟨494315, by rfl⟩ : syracuseStep 659087 = 988631) B988631
theorem B1708199 : Blo 259821 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B10195247 : Blo 259821 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B16586003 : Blo 259821 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B398825 : Blo 259821 398825 := bstep (se 2 (by rfl) ⟨149559, by rfl⟩ : syracuseStep 398825 = 299119) B299119
theorem B498143 : Blo 259821 498143 := bstep (se 1 (by rfl) ⟨373607, by rfl⟩ : syracuseStep 498143 = 747215) B747215
theorem B1317383 : Blo 259821 1317383 := bstep (se 1 (by rfl) ⟨988037, by rfl⟩ : syracuseStep 1317383 = 1976075) B1976075
theorem B34381691 : Blo 259821 34381691 := bstep (se 1 (by rfl) ⟨25786268, by rfl⟩ : syracuseStep 34381691 = 51572537) B51572537
theorem B5384303 : Blo 259821 5384303 := bstep (se 1 (by rfl) ⟨4038227, by rfl⟩ : syracuseStep 5384303 = 8076455) B8076455
theorem B5777573 : Blo 259821 5777573 := bstep (se 4 (by rfl) ⟨541647, by rfl⟩ : syracuseStep 5777573 = 1083295) B1083295
theorem B404095 : Blo 259821 404095 := bstep (se 1 (by rfl) ⟨303071, by rfl⟩ : syracuseStep 404095 = 606143) B606143
theorem B3190013 : Blo 259821 3190013 := bstep (se 3 (by rfl) ⟨598127, by rfl⟩ : syracuseStep 3190013 = 1196255) B1196255
theorem B1487753 : Blo 259821 1487753 := bstep (se 2 (by rfl) ⟨557907, by rfl⟩ : syracuseStep 1487753 = 1115815) B1115815
theorem B2962655 : Blo 259821 2962655 := bstep (se 1 (by rfl) ⟨2221991, by rfl⟩ : syracuseStep 2962655 = 4443983) B4443983
theorem B997211 : Blo 259821 997211 := bstep (se 1 (by rfl) ⟨747908, by rfl⟩ : syracuseStep 997211 = 1495817) B1495817
theorem B1686845 : Blo 259821 1686845 := bstep (se 3 (by rfl) ⟨316283, by rfl⟩ : syracuseStep 1686845 = 632567) B632567
theorem B8469841 : Blo 259821 8469841 := bstep (se 2 (by rfl) ⟨3176190, by rfl⟩ : syracuseStep 8469841 = 6352381) B6352381
theorem B11255759 : Blo 259821 11255759 := bstep (se 1 (by rfl) ⟨8441819, by rfl⟩ : syracuseStep 11255759 = 16883639) B16883639
theorem B1327427 : Blo 259821 1327427 := bstep (se 1 (by rfl) ⟨995570, by rfl⟩ : syracuseStep 1327427 = 1991141) B1991141
theorem B443495 : Blo 259821 443495 := bstep (se 1 (by rfl) ⟨332621, by rfl⟩ : syracuseStep 443495 = 665243) B665243
theorem B97601435 : Blo 259821 97601435 := bstep (se 1 (by rfl) ⟨73201076, by rfl⟩ : syracuseStep 97601435 = 146402153) B146402153
theorem B1068335 : Blo 259821 1068335 := bstep (se 1 (by rfl) ⟨801251, by rfl⟩ : syracuseStep 1068335 = 1602503) B1602503
theorem B1986281 : Blo 259821 1986281 := bstep (se 2 (by rfl) ⟨744855, by rfl⟩ : syracuseStep 1986281 = 1489711) B1489711
theorem B708839 : Blo 259821 708839 := bstep (se 1 (by rfl) ⟨531629, by rfl⟩ : syracuseStep 708839 = 1063259) B1063259
theorem B1200545 : Blo 259821 1200545 := bstep (se 2 (by rfl) ⟨450204, by rfl⟩ : syracuseStep 1200545 = 900409) B900409
theorem B1266479 : Blo 259821 1266479 := bstep (se 1 (by rfl) ⟨949859, by rfl⟩ : syracuseStep 1266479 = 1899719) B1899719
theorem B742783 : Blo 259821 742783 := bstep (se 1 (by rfl) ⟨557087, by rfl⟩ : syracuseStep 742783 = 1114175) B1114175
theorem B1594961 : Blo 259821 1594961 := bstep (se 2 (by rfl) ⟨598110, by rfl⟩ : syracuseStep 1594961 = 1196221) B1196221
theorem B2971403 : Blo 259821 2971403 := bstep (se 1 (by rfl) ⟨2228552, by rfl⟩ : syracuseStep 2971403 = 4457105) B4457105
theorem B1988711 : Blo 259821 1988711 := bstep (se 1 (by rfl) ⟨1491533, by rfl⟩ : syracuseStep 1988711 = 2983067) B2983067
theorem B18209123 : Blo 259821 18209123 := bstep (se 1 (by rfl) ⟨13656842, by rfl⟩ : syracuseStep 18209123 = 27313685) B27313685
theorem B32923331 : Blo 259821 32923331 := bstep (se 1 (by rfl) ⟨24692498, by rfl⟩ : syracuseStep 32923331 = 49384997) B49384997
theorem B3661615 : Blo 259821 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B876959 : Blo 259821 876959 := bstep (se 1 (by rfl) ⟨657719, by rfl⟩ : syracuseStep 876959 = 1315439) B1315439
theorem B1335935 : Blo 259821 1335935 := bstep (se 1 (by rfl) ⟨1001951, by rfl⟩ : syracuseStep 1335935 = 2003903) B2003903
theorem B8282891 : Blo 259821 8282891 := bstep (se 1 (by rfl) ⟨6212168, by rfl⟩ : syracuseStep 8282891 = 12424337) B12424337
theorem B2025947 : Blo 259821 2025947 := bstep (se 1 (by rfl) ⟨1519460, by rfl⟩ : syracuseStep 2025947 = 3038921) B3038921
theorem B27224747 : Blo 259821 27224747 := bstep (se 1 (by rfl) ⟨20418560, by rfl⟩ : syracuseStep 27224747 = 40837121) B40837121
theorem B10841951 : Blo 259821 10841951 := bstep (se 1 (by rfl) ⟨8131463, by rfl⟩ : syracuseStep 10841951 = 16262927) B16262927
theorem B586619 : Blo 259821 586619 := bstep (se 1 (by rfl) ⟨439964, by rfl⟩ : syracuseStep 586619 = 879929) B879929
theorem B2225069 : Blo 259821 2225069 := bstep (se 3 (by rfl) ⟨417200, by rfl⟩ : syracuseStep 2225069 = 834401) B834401
theorem B3797999 : Blo 259821 3797999 := bstep (se 1 (by rfl) ⟨2848499, by rfl⟩ : syracuseStep 3797999 = 5696999) B5696999
theorem B586907 : Blo 259821 586907 := bstep (se 1 (by rfl) ⟨440180, by rfl⟩ : syracuseStep 586907 = 880361) B880361
theorem B390863 : Blo 259821 390863 := bstep (se 1 (by rfl) ⟨293147, by rfl⟩ : syracuseStep 390863 = 586295) B586295
theorem B587483 : Blo 259821 587483 := bstep (se 1 (by rfl) ⟨440612, by rfl⟩ : syracuseStep 587483 = 881225) B881225
theorem B390887 : Blo 259821 390887 := bstep (se 1 (by rfl) ⟨293165, by rfl⟩ : syracuseStep 390887 = 586331) B586331
theorem B259951 : Blo 259821 259951 := bstep (se 1 (by rfl) ⟨194963, by rfl⟩ : syracuseStep 259951 = 389927) B389927
theorem B260007 : Blo 259821 260007 := bstep (se 1 (by rfl) ⟨195005, by rfl⟩ : syracuseStep 260007 = 390011) B390011
theorem B948361 : Blo 259821 948361 := bstep (se 2 (by rfl) ⟨355635, by rfl⟩ : syracuseStep 948361 = 711271) B711271
theorem B260303 : Blo 259821 260303 := bstep (se 1 (by rfl) ⟨195227, by rfl⟩ : syracuseStep 260303 = 390455) B390455
theorem B260351 : Blo 259821 260351 := bstep (se 1 (by rfl) ⟨195263, by rfl⟩ : syracuseStep 260351 = 390527) B390527
theorem B293359 : Blo 259821 293359 := bstep (se 1 (by rfl) ⟨220019, by rfl⟩ : syracuseStep 293359 = 440039) B440039
theorem B260735 : Blo 259821 260735 := bstep (se 1 (by rfl) ⟨195551, by rfl⟩ : syracuseStep 260735 = 391103) B391103
theorem B392303 : Blo 259821 392303 := bstep (se 1 (by rfl) ⟨294227, by rfl⟩ : syracuseStep 392303 = 588455) B588455
theorem B261247 : Blo 259821 261247 := bstep (se 1 (by rfl) ⟨195935, by rfl⟩ : syracuseStep 261247 = 391871) B391871
theorem B294079 : Blo 259821 294079 := bstep (se 1 (by rfl) ⟨220559, by rfl⟩ : syracuseStep 294079 = 441119) B441119
theorem B392489 : Blo 259821 392489 := bstep (se 2 (by rfl) ⟨147183, by rfl⟩ : syracuseStep 392489 = 294367) B294367
theorem B359743 : Blo 259821 359743 := bstep (se 1 (by rfl) ⟨269807, by rfl⟩ : syracuseStep 359743 = 539615) B539615
theorem B1408337 : Blo 259821 1408337 := bstep (se 2 (by rfl) ⟨528126, by rfl⟩ : syracuseStep 1408337 = 1056253) B1056253
theorem B589139 : Blo 259821 589139 := bstep (se 1 (by rfl) ⟨441854, by rfl⟩ : syracuseStep 589139 = 883709) B883709
theorem B261503 : Blo 259821 261503 := bstep (se 1 (by rfl) ⟨196127, by rfl⟩ : syracuseStep 261503 = 392255) B392255
theorem B261871 : Blo 259821 261871 := bstep (se 1 (by rfl) ⟨196403, by rfl⟩ : syracuseStep 261871 = 392807) B392807
theorem B294655 : Blo 259821 294655 := bstep (se 1 (by rfl) ⟨220991, by rfl⟩ : syracuseStep 294655 = 441983) B441983
theorem B262171 : Blo 259821 262171 := bstep (se 1 (by rfl) ⟨196628, by rfl⟩ : syracuseStep 262171 = 393257) B393257
theorem B589895 : Blo 259821 589895 := bstep (se 1 (by rfl) ⟨442421, by rfl⟩ : syracuseStep 589895 = 884843) B884843
theorem B884951 : Blo 259821 884951 := bstep (se 1 (by rfl) ⟨663713, by rfl⟩ : syracuseStep 884951 = 1327427) B1327427
theorem B393695 : Blo 259821 393695 := bstep (se 1 (by rfl) ⟨295271, by rfl⟩ : syracuseStep 393695 = 590543) B590543
theorem B295663 : Blo 259821 295663 := bstep (se 1 (by rfl) ⟨221747, by rfl⟩ : syracuseStep 295663 = 443495) B443495
theorem B262895 : Blo 259821 262895 := bstep (se 1 (by rfl) ⟨197171, by rfl⟩ : syracuseStep 262895 = 394343) B394343
theorem B263259 : Blo 259821 263259 := bstep (se 1 (by rfl) ⟨197444, by rfl⟩ : syracuseStep 263259 = 394889) B394889
theorem B263527 : Blo 259821 263527 := bstep (se 1 (by rfl) ⟨197645, by rfl⟩ : syracuseStep 263527 = 395291) B395291
theorem B395135 : Blo 259821 395135 := bstep (se 1 (by rfl) ⟨296351, by rfl⟩ : syracuseStep 395135 = 592703) B592703
theorem B22087709 : Blo 259821 22087709 := bstep (se 3 (by rfl) ⟨4141445, by rfl⟩ : syracuseStep 22087709 = 8282891) B8282891
theorem B395471 : Blo 259821 395471 := bstep (se 1 (by rfl) ⟨296603, by rfl⟩ : syracuseStep 395471 = 593207) B593207
theorem B265883 : Blo 259821 265883 := bstep (se 1 (by rfl) ⟨199412, by rfl⟩ : syracuseStep 265883 = 398825) B398825
theorem B332095 : Blo 259821 332095 := bstep (se 1 (by rfl) ⟨249071, by rfl⟩ : syracuseStep 332095 = 498143) B498143
theorem B890623 : Blo 259821 890623 := bstep (se 1 (by rfl) ⟨667967, by rfl⟩ : syracuseStep 890623 = 1335935) B1335935
theorem B15406861 : Blo 259821 15406861 := bstep (se 3 (by rfl) ⟨2888786, by rfl⟩ : syracuseStep 15406861 = 5777573) B5777573
theorem B1350631 : Blo 259821 1350631 := bstep (se 1 (by rfl) ⟨1012973, by rfl⟩ : syracuseStep 1350631 = 2025947) B2025947
theorem B990377 : Blo 259821 990377 := bstep (se 2 (by rfl) ⟨371391, by rfl⟩ : syracuseStep 990377 = 742783) B742783
theorem B991835 : Blo 259821 991835 := bstep (se 1 (by rfl) ⟨743876, by rfl⟩ : syracuseStep 991835 = 1487753) B1487753
theorem B1483379 : Blo 259821 1483379 := bstep (se 1 (by rfl) ⟨1112534, by rfl⟩ : syracuseStep 1483379 = 2225069) B2225069
theorem B2531999 : Blo 259821 2531999 := bstep (se 1 (by rfl) ⟨1898999, by rfl⟩ : syracuseStep 2531999 = 3797999) B3797999
theorem B1975103 : Blo 259821 1975103 := bstep (se 1 (by rfl) ⟨1481327, by rfl⟩ : syracuseStep 1975103 = 2962655) B2962655
theorem B664807 : Blo 259821 664807 := bstep (se 1 (by rfl) ⟨498605, by rfl⟩ : syracuseStep 664807 = 997211) B997211
theorem B1124563 : Blo 259821 1124563 := bstep (se 1 (by rfl) ⟨843422, by rfl⟩ : syracuseStep 1124563 = 1686845) B1686845
theorem B9612071 : Blo 259821 9612071 := bstep (se 1 (by rfl) ⟨7209053, by rfl⟩ : syracuseStep 9612071 = 14418107) B14418107
theorem B439391 : Blo 259821 439391 := bstep (se 1 (by rfl) ⟨329543, by rfl⟩ : syracuseStep 439391 = 659087) B659087
theorem B1324187 : Blo 259821 1324187 := bstep (se 1 (by rfl) ⟨993140, by rfl⟩ : syracuseStep 1324187 = 1986281) B1986281
theorem B472559 : Blo 259821 472559 := bstep (se 1 (by rfl) ⟨354419, by rfl⟩ : syracuseStep 472559 = 708839) B708839
theorem B6796831 : Blo 259821 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B800363 : Blo 259821 800363 := bstep (se 1 (by rfl) ⟨600272, by rfl⟩ : syracuseStep 800363 = 1200545) B1200545
theorem B538793 : Blo 259821 538793 := bstep (se 2 (by rfl) ⟨202047, by rfl⟩ : syracuseStep 538793 = 404095) B404095
theorem B1063307 : Blo 259821 1063307 := bstep (se 1 (by rfl) ⟨797480, by rfl⟩ : syracuseStep 1063307 = 1594961) B1594961
theorem B1980935 : Blo 259821 1980935 := bstep (se 1 (by rfl) ⟨1485701, by rfl⟩ : syracuseStep 1980935 = 2971403) B2971403
theorem B1325807 : Blo 259821 1325807 := bstep (se 1 (by rfl) ⟨994355, by rfl⟩ : syracuseStep 1325807 = 1988711) B1988711
theorem B12139415 : Blo 259821 12139415 := bstep (se 1 (by rfl) ⟨9104561, by rfl⟩ : syracuseStep 12139415 = 18209123) B18209123
theorem B22921127 : Blo 259821 22921127 := bstep (se 1 (by rfl) ⟨17190845, by rfl⟩ : syracuseStep 22921127 = 34381691) B34381691
theorem B3589535 : Blo 259821 3589535 := bstep (se 1 (by rfl) ⟨2692151, by rfl⟩ : syracuseStep 3589535 = 5384303) B5384303
theorem B7227967 : Blo 259821 7227967 := bstep (se 1 (by rfl) ⟨5420975, by rfl⟩ : syracuseStep 7227967 = 10841951) B10841951
theorem B1264481 : Blo 259821 1264481 := bstep (se 2 (by rfl) ⟨474180, by rfl⟩ : syracuseStep 1264481 = 948361) B948361
theorem B479657 : Blo 259821 479657 := bstep (se 2 (by rfl) ⟨179871, by rfl⟩ : syracuseStep 479657 = 359743) B359743
theorem B11293121 : Blo 259821 11293121 := bstep (se 2 (by rfl) ⟨4234920, by rfl⟩ : syracuseStep 11293121 = 8469841) B8469841
theorem B938891 : Blo 259821 938891 := bstep (se 1 (by rfl) ⟨704168, by rfl⟩ : syracuseStep 938891 = 1408337) B1408337
theorem B65067623 : Blo 259821 65067623 := bstep (se 1 (by rfl) ⟨48800717, by rfl⟩ : syracuseStep 65067623 = 97601435) B97601435
theorem B1203227 : Blo 259821 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B712223 : Blo 259821 712223 := bstep (se 1 (by rfl) ⟨534167, by rfl⟩ : syracuseStep 712223 = 1068335) B1068335
theorem B745129 : Blo 259821 745129 := bstep (se 2 (by rfl) ⟨279423, by rfl⟩ : syracuseStep 745129 = 558847) B558847
theorem B5070833 : Blo 259821 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B1138799 : Blo 259821 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B844319 : Blo 259821 844319 := bstep (se 1 (by rfl) ⟨633239, by rfl⟩ : syracuseStep 844319 = 1266479) B1266479
theorem B44229341 : Blo 259821 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B878255 : Blo 259821 878255 := bstep (se 1 (by rfl) ⟨658691, by rfl⟩ : syracuseStep 878255 = 1317383) B1317383
theorem B21948887 : Blo 259821 21948887 := bstep (se 1 (by rfl) ⟨16461665, by rfl⟩ : syracuseStep 21948887 = 32923331) B32923331
theorem B584639 : Blo 259821 584639 := bstep (se 1 (by rfl) ⟨438479, by rfl⟩ : syracuseStep 584639 = 876959) B876959
theorem B18149831 : Blo 259821 18149831 := bstep (se 1 (by rfl) ⟨13612373, by rfl⟩ : syracuseStep 18149831 = 27224747) B27224747
theorem B2126675 : Blo 259821 2126675 := bstep (se 1 (by rfl) ⟨1595006, by rfl⟩ : syracuseStep 2126675 = 3190013) B3190013
theorem B391079 : Blo 259821 391079 := bstep (se 1 (by rfl) ⟨293309, by rfl⟩ : syracuseStep 391079 = 586619) B586619
theorem B391145 : Blo 259821 391145 := bstep (se 2 (by rfl) ⟨146679, by rfl⟩ : syracuseStep 391145 = 293359) B293359
theorem B391271 : Blo 259821 391271 := bstep (se 1 (by rfl) ⟨293453, by rfl⟩ : syracuseStep 391271 = 586907) B586907
theorem B260575 : Blo 259821 260575 := bstep (se 1 (by rfl) ⟨195431, by rfl⟩ : syracuseStep 260575 = 390863) B390863
theorem B391655 : Blo 259821 391655 := bstep (se 1 (by rfl) ⟨293741, by rfl⟩ : syracuseStep 391655 = 587483) B587483
theorem B260591 : Blo 259821 260591 := bstep (se 1 (by rfl) ⟨195443, by rfl⟩ : syracuseStep 260591 = 390887) B390887
theorem B19528613 : Blo 259821 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B392105 : Blo 259821 392105 := bstep (se 2 (by rfl) ⟨147039, by rfl⟩ : syracuseStep 392105 = 294079) B294079
theorem B261535 : Blo 259821 261535 := bstep (se 1 (by rfl) ⟨196151, by rfl⟩ : syracuseStep 261535 = 392303) B392303
theorem B261659 : Blo 259821 261659 := bstep (se 1 (by rfl) ⟨196244, by rfl⟩ : syracuseStep 261659 = 392489) B392489
theorem B392759 : Blo 259821 392759 := bstep (se 1 (by rfl) ⟨294569, by rfl⟩ : syracuseStep 392759 = 589139) B589139
theorem B392873 : Blo 259821 392873 := bstep (se 2 (by rfl) ⟨147327, by rfl⟩ : syracuseStep 392873 = 294655) B294655
theorem B7503839 : Blo 259821 7503839 := bstep (se 1 (by rfl) ⟨5627879, by rfl⟩ : syracuseStep 7503839 = 11255759) B11255759
theorem B393263 : Blo 259821 393263 := bstep (se 1 (by rfl) ⟨294947, by rfl⟩ : syracuseStep 393263 = 589895) B589895
theorem B589967 : Blo 259821 589967 := bstep (se 1 (by rfl) ⟨442475, by rfl⟩ : syracuseStep 589967 = 884951) B884951
theorem B235602229 : Blo 259821 235602229 := bstep (se 5 (by rfl) ⟨11043854, by rfl⟩ : syracuseStep 235602229 = 22087709) B22087709
theorem B262463 : Blo 259821 262463 := bstep (se 1 (by rfl) ⟨196847, by rfl⟩ : syracuseStep 262463 = 393695) B393695
theorem B2393023 : Blo 259821 2393023 := bstep (se 1 (by rfl) ⟨1794767, by rfl⟩ : syracuseStep 2393023 = 3589535) B3589535
theorem B394217 : Blo 259821 394217 := bstep (se 2 (by rfl) ⟨147831, by rfl⟩ : syracuseStep 394217 = 295663) B295663
theorem B263423 : Blo 259821 263423 := bstep (se 1 (by rfl) ⟨197567, by rfl⟩ : syracuseStep 263423 = 395135) B395135
theorem B263647 : Blo 259821 263647 := bstep (se 1 (by rfl) ⟨197735, by rfl⟩ : syracuseStep 263647 = 395471) B395471
theorem B886409 : Blo 259821 886409 := bstep (se 2 (by rfl) ⟨332403, by rfl⟩ : syracuseStep 886409 = 664807) B664807
theorem B5671133 : Blo 259821 5671133 := bstep (se 3 (by rfl) ⟨1063337, by rfl⟩ : syracuseStep 5671133 = 2126675) B2126675
theorem B625927 : Blo 259821 625927 := bstep (se 1 (by rfl) ⟨469445, by rfl⟩ : syracuseStep 625927 = 938891) B938891
theorem B9637289 : Blo 259821 9637289 := bstep (se 2 (by rfl) ⟨3613983, by rfl⟩ : syracuseStep 9637289 = 7227967) B7227967
theorem B660251 : Blo 259821 660251 := bstep (se 1 (by rfl) ⟨495188, by rfl⟩ : syracuseStep 660251 = 990377) B990377
theorem B3380555 : Blo 259821 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B562879 : Blo 259821 562879 := bstep (se 1 (by rfl) ⟨422159, by rfl⟩ : syracuseStep 562879 = 844319) B844319
theorem B661223 : Blo 259821 661223 := bstep (se 1 (by rfl) ⟨495917, by rfl⟩ : syracuseStep 661223 = 991835) B991835
theorem B988919 : Blo 259821 988919 := bstep (se 1 (by rfl) ⟨741689, by rfl⟩ : syracuseStep 988919 = 1483379) B1483379
theorem B1316735 : Blo 259821 1316735 := bstep (se 1 (by rfl) ⟨987551, by rfl⟩ : syracuseStep 1316735 = 1975103) B1975103
theorem B1187497 : Blo 259821 1187497 := bstep (se 2 (by rfl) ⟨445311, by rfl⟩ : syracuseStep 1187497 = 890623) B890623
theorem B12099887 : Blo 259821 12099887 := bstep (se 1 (by rfl) ⟨9074915, by rfl⟩ : syracuseStep 12099887 = 18149831) B18149831
theorem B533575 : Blo 259821 533575 := bstep (se 1 (by rfl) ⟨400181, by rfl⟩ : syracuseStep 533575 = 800363) B800363
theorem B1320623 : Blo 259821 1320623 := bstep (se 1 (by rfl) ⟨990467, by rfl⟩ : syracuseStep 1320623 = 1980935) B1980935
theorem B13019075 : Blo 259821 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B993505 : Blo 259821 993505 := bstep (se 2 (by rfl) ⟨372564, by rfl⟩ : syracuseStep 993505 = 745129) B745129
theorem B15280751 : Blo 259821 15280751 := bstep (se 1 (by rfl) ⟨11460563, by rfl⟩ : syracuseStep 15280751 = 22921127) B22921127
theorem B1260157 : Blo 259821 1260157 := bstep (se 3 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 1260157 = 472559) B472559
theorem B802151 : Blo 259821 802151 := bstep (se 1 (by rfl) ⟨601613, by rfl⟩ : syracuseStep 802151 = 1203227) B1203227
theorem B474815 : Blo 259821 474815 := bstep (se 1 (by rfl) ⟨356111, by rfl⟩ : syracuseStep 474815 = 712223) B712223
theorem B442793 : Blo 259821 442793 := bstep (se 2 (by rfl) ⟨166047, by rfl⟩ : syracuseStep 442793 = 332095) B332095
theorem B1687999 : Blo 259821 1687999 := bstep (se 1 (by rfl) ⟨1265999, by rfl⟩ : syracuseStep 1687999 = 2531999) B2531999
theorem B14632591 : Blo 259821 14632591 := bstep (se 1 (by rfl) ⟨10974443, by rfl⟩ : syracuseStep 14632591 = 21948887) B21948887
theorem B6408047 : Blo 259821 6408047 := bstep (se 1 (by rfl) ⟨4806035, by rfl⟩ : syracuseStep 6408047 = 9612071) B9612071
theorem B9062441 : Blo 259821 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B708871 : Blo 259821 708871 := bstep (se 1 (by rfl) ⟨531653, by rfl⟩ : syracuseStep 708871 = 1063307) B1063307
theorem B709021 : Blo 259821 709021 := bstep (se 3 (by rfl) ⟨132941, by rfl⟩ : syracuseStep 709021 = 265883) B265883
theorem B5002559 : Blo 259821 5002559 := bstep (se 1 (by rfl) ⟨3751919, by rfl⟩ : syracuseStep 5002559 = 7503839) B7503839
theorem B3036797 : Blo 259821 3036797 := bstep (se 3 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 3036797 = 1138799) B1138799
theorem B842987 : Blo 259821 842987 := bstep (se 1 (by rfl) ⟨632240, by rfl⟩ : syracuseStep 842987 = 1264481) B1264481
theorem B1499417 : Blo 259821 1499417 := bstep (se 2 (by rfl) ⟨562281, by rfl⟩ : syracuseStep 1499417 = 1124563) B1124563
theorem B319771 : Blo 259821 319771 := bstep (se 1 (by rfl) ⟨239828, by rfl⟩ : syracuseStep 319771 = 479657) B479657
theorem B7528747 : Blo 259821 7528747 := bstep (se 1 (by rfl) ⟨5646560, by rfl⟩ : syracuseStep 7528747 = 11293121) B11293121
theorem B43378415 : Blo 259821 43378415 := bstep (se 1 (by rfl) ⟨32533811, by rfl⟩ : syracuseStep 43378415 = 65067623) B65067623
theorem B29486227 : Blo 259821 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B585503 : Blo 259821 585503 := bstep (se 1 (by rfl) ⟨439127, by rfl⟩ : syracuseStep 585503 = 878255) B878255
theorem B389759 : Blo 259821 389759 := bstep (se 1 (by rfl) ⟨292319, by rfl⟩ : syracuseStep 389759 = 584639) B584639
theorem B20542481 : Blo 259821 20542481 := bstep (se 2 (by rfl) ⟨7703430, by rfl⟩ : syracuseStep 20542481 = 15406861) B15406861
theorem B292927 : Blo 259821 292927 := bstep (se 1 (by rfl) ⟨219695, by rfl⟩ : syracuseStep 292927 = 439391) B439391
theorem B882791 : Blo 259821 882791 := bstep (se 1 (by rfl) ⟨662093, by rfl⟩ : syracuseStep 882791 = 1324187) B1324187
theorem B260719 : Blo 259821 260719 := bstep (se 1 (by rfl) ⟨195539, by rfl⟩ : syracuseStep 260719 = 391079) B391079
theorem B1800841 : Blo 259821 1800841 := bstep (se 2 (by rfl) ⟨675315, by rfl⟩ : syracuseStep 1800841 = 1350631) B1350631
theorem B260763 : Blo 259821 260763 := bstep (se 1 (by rfl) ⟨195572, by rfl⟩ : syracuseStep 260763 = 391145) B391145
theorem B260847 : Blo 259821 260847 := bstep (se 1 (by rfl) ⟨195635, by rfl⟩ : syracuseStep 260847 = 391271) B391271
theorem B359195 : Blo 259821 359195 := bstep (se 1 (by rfl) ⟨269396, by rfl⟩ : syracuseStep 359195 = 538793) B538793
theorem B261103 : Blo 259821 261103 := bstep (se 1 (by rfl) ⟨195827, by rfl⟩ : syracuseStep 261103 = 391655) B391655
theorem B883871 : Blo 259821 883871 := bstep (se 1 (by rfl) ⟨662903, by rfl⟩ : syracuseStep 883871 = 1325807) B1325807
theorem B8092943 : Blo 259821 8092943 := bstep (se 1 (by rfl) ⟨6069707, by rfl⟩ : syracuseStep 8092943 = 12139415) B12139415
theorem B261403 : Blo 259821 261403 := bstep (se 1 (by rfl) ⟨196052, by rfl⟩ : syracuseStep 261403 = 392105) B392105
theorem B261839 : Blo 259821 261839 := bstep (se 1 (by rfl) ⟨196379, by rfl⟩ : syracuseStep 261839 = 392759) B392759
theorem B261915 : Blo 259821 261915 := bstep (se 1 (by rfl) ⟨196436, by rfl⟩ : syracuseStep 261915 = 392873) B392873
theorem B262175 : Blo 259821 262175 := bstep (se 1 (by rfl) ⟨196631, by rfl⟩ : syracuseStep 262175 = 393263) B393263
theorem B393311 : Blo 259821 393311 := bstep (se 1 (by rfl) ⟨294983, by rfl⟩ : syracuseStep 393311 = 589967) B589967
theorem B295195 : Blo 259821 295195 := bstep (se 1 (by rfl) ⟨221396, by rfl⟩ : syracuseStep 295195 = 442793) B442793
theorem B262811 : Blo 259821 262811 := bstep (se 1 (by rfl) ⟨197108, by rfl⟩ : syracuseStep 262811 = 394217) B394217
theorem B590939 : Blo 259821 590939 := bstep (se 1 (by rfl) ⟨443204, by rfl⟩ : syracuseStep 590939 = 886409) B886409
theorem B1705445 : Blo 259821 1705445 := bstep (se 4 (by rfl) ⟨159885, by rfl⟩ : syracuseStep 1705445 = 319771) B319771
theorem B6424859 : Blo 259821 6424859 := bstep (se 1 (by rfl) ⟨4818644, by rfl⟩ : syracuseStep 6424859 = 9637289) B9637289
theorem B659279 : Blo 259821 659279 := bstep (se 1 (by rfl) ⟨494459, by rfl⟩ : syracuseStep 659279 = 988919) B988919
theorem B561991 : Blo 259821 561991 := bstep (se 1 (by rfl) ⟨421493, by rfl⟩ : syracuseStep 561991 = 842987) B842987
theorem B8066591 : Blo 259821 8066591 := bstep (se 1 (by rfl) ⟨6049943, by rfl⟩ : syracuseStep 8066591 = 12099887) B12099887
theorem B957853 : Blo 259821 957853 := bstep (se 3 (by rfl) ⟨179597, by rfl⟩ : syracuseStep 957853 = 359195) B359195
theorem B1680209 : Blo 259821 1680209 := bstep (se 2 (by rfl) ⟨630078, by rfl⟩ : syracuseStep 1680209 = 1260157) B1260157
theorem B2401121 : Blo 259821 2401121 := bstep (se 2 (by rfl) ⟨900420, by rfl⟩ : syracuseStep 2401121 = 1800841) B1800841
theorem B1583329 : Blo 259821 1583329 := bstep (se 2 (by rfl) ⟨593748, by rfl⟩ : syracuseStep 1583329 = 1187497) B1187497
theorem B534767 : Blo 259821 534767 := bstep (se 1 (by rfl) ⟨401075, by rfl⟩ : syracuseStep 534767 = 802151) B802151
theorem B10038329 : Blo 259821 10038329 := bstep (se 2 (by rfl) ⟨3764373, by rfl⟩ : syracuseStep 10038329 = 7528747) B7528747
theorem B4272031 : Blo 259821 4272031 := bstep (se 1 (by rfl) ⟨3204023, by rfl⟩ : syracuseStep 4272031 = 6408047) B6408047
theorem B3190697 : Blo 259821 3190697 := bstep (se 2 (by rfl) ⟨1196511, by rfl⟩ : syracuseStep 3190697 = 2393023) B2393023
theorem B6041627 : Blo 259821 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B3780755 : Blo 259821 3780755 := bstep (se 1 (by rfl) ⟨2835566, by rfl⟩ : syracuseStep 3780755 = 5671133) B5671133
theorem B19510121 : Blo 259821 19510121 := bstep (se 2 (by rfl) ⟨7316295, by rfl⟩ : syracuseStep 19510121 = 14632591) B14632591
theorem B1324673 : Blo 259821 1324673 := bstep (se 2 (by rfl) ⟨496752, by rfl⟩ : syracuseStep 1324673 = 993505) B993505
theorem B440167 : Blo 259821 440167 := bstep (se 1 (by rfl) ⟨330125, by rfl⟩ : syracuseStep 440167 = 660251) B660251
theorem B440815 : Blo 259821 440815 := bstep (se 1 (by rfl) ⟨330611, by rfl⟩ : syracuseStep 440815 = 661223) B661223
theorem B834569 : Blo 259821 834569 := bstep (se 2 (by rfl) ⟨312963, by rfl⟩ : syracuseStep 834569 = 625927) B625927
theorem B999611 : Blo 259821 999611 := bstep (se 1 (by rfl) ⟨749708, by rfl⟩ : syracuseStep 999611 = 1499417) B1499417
theorem B28918943 : Blo 259821 28918943 := bstep (se 1 (by rfl) ⟨21689207, by rfl⟩ : syracuseStep 28918943 = 43378415) B43378415
theorem B3002021 : Blo 259821 3002021 := bstep (se 4 (by rfl) ⟨281439, by rfl⟩ : syracuseStep 3002021 = 562879) B562879
theorem B5395295 : Blo 259821 5395295 := bstep (se 1 (by rfl) ⟨4046471, by rfl⟩ : syracuseStep 5395295 = 8092943) B8092943
theorem B316543 : Blo 259821 316543 := bstep (se 1 (by rfl) ⟨237407, by rfl⟩ : syracuseStep 316543 = 474815) B474815
theorem B314136305 : Blo 259821 314136305 := bstep (se 2 (by rfl) ⟨117801114, by rfl⟩ : syracuseStep 314136305 = 235602229) B235602229
theorem B2250665 : Blo 259821 2250665 := bstep (se 2 (by rfl) ⟨843999, by rfl⟩ : syracuseStep 2250665 = 1687999) B1687999
theorem B711433 : Blo 259821 711433 := bstep (se 2 (by rfl) ⟨266787, by rfl⟩ : syracuseStep 711433 = 533575) B533575
theorem B3335039 : Blo 259821 3335039 := bstep (se 1 (by rfl) ⟨2501279, by rfl⟩ : syracuseStep 3335039 = 5002559) B5002559
theorem B2253703 : Blo 259821 2253703 := bstep (se 1 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 2253703 = 3380555) B3380555
theorem B2024531 : Blo 259821 2024531 := bstep (se 1 (by rfl) ⟨1518398, by rfl⟩ : syracuseStep 2024531 = 3036797) B3036797
theorem B877823 : Blo 259821 877823 := bstep (se 1 (by rfl) ⟨658367, by rfl⟩ : syracuseStep 877823 = 1316735) B1316735
theorem B39314969 : Blo 259821 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B945161 : Blo 259821 945161 := bstep (se 2 (by rfl) ⟨354435, by rfl⟩ : syracuseStep 945161 = 708871) B708871
theorem B945361 : Blo 259821 945361 := bstep (se 2 (by rfl) ⟨354510, by rfl⟩ : syracuseStep 945361 = 709021) B709021
theorem B880415 : Blo 259821 880415 := bstep (se 1 (by rfl) ⟨660311, by rfl⟩ : syracuseStep 880415 = 1320623) B1320623
theorem B8679383 : Blo 259821 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B10187167 : Blo 259821 10187167 := bstep (se 1 (by rfl) ⟨7640375, by rfl⟩ : syracuseStep 10187167 = 15280751) B15280751
theorem B390335 : Blo 259821 390335 := bstep (se 1 (by rfl) ⟨292751, by rfl⟩ : syracuseStep 390335 = 585503) B585503
theorem B390569 : Blo 259821 390569 := bstep (se 2 (by rfl) ⟨146463, by rfl⟩ : syracuseStep 390569 = 292927) B292927
theorem B259839 : Blo 259821 259839 := bstep (se 1 (by rfl) ⟨194879, by rfl⟩ : syracuseStep 259839 = 389759) B389759
theorem B13694987 : Blo 259821 13694987 := bstep (se 1 (by rfl) ⟨10271240, by rfl⟩ : syracuseStep 13694987 = 20542481) B20542481
theorem B588527 : Blo 259821 588527 := bstep (se 1 (by rfl) ⟨441395, by rfl⟩ : syracuseStep 588527 = 882791) B882791
theorem B589247 : Blo 259821 589247 := bstep (se 1 (by rfl) ⟨441935, by rfl⟩ : syracuseStep 589247 = 883871) B883871
theorem B262207 : Blo 259821 262207 := bstep (se 1 (by rfl) ⟨196655, by rfl⟩ : syracuseStep 262207 = 393311) B393311
theorem B393593 : Blo 259821 393593 := bstep (se 2 (by rfl) ⟨147597, by rfl⟩ : syracuseStep 393593 = 295195) B295195
theorem B393959 : Blo 259821 393959 := bstep (se 1 (by rfl) ⟨295469, by rfl⟩ : syracuseStep 393959 = 590939) B590939
theorem B14387453 : Blo 259821 14387453 := bstep (se 3 (by rfl) ⟨2697647, by rfl⟩ : syracuseStep 14387453 = 5395295) B5395295
theorem B2001347 : Blo 259821 2001347 := bstep (se 1 (by rfl) ⟨1501010, by rfl⟩ : syracuseStep 2001347 = 3002021) B3002021
theorem B5377727 : Blo 259821 5377727 := bstep (se 1 (by rfl) ⟨4033295, by rfl⟩ : syracuseStep 5377727 = 8066591) B8066591
theorem B209424203 : Blo 259821 209424203 := bstep (se 1 (by rfl) ⟨157068152, by rfl⟩ : syracuseStep 209424203 = 314136305) B314136305
theorem B1120139 : Blo 259821 1120139 := bstep (se 1 (by rfl) ⟨840104, by rfl⟩ : syracuseStep 1120139 = 1680209) B1680209
theorem B1349687 : Blo 259821 1349687 := bstep (se 1 (by rfl) ⟨1012265, by rfl⟩ : syracuseStep 1349687 = 2024531) B2024531
theorem B630107 : Blo 259821 630107 := bstep (se 1 (by rfl) ⟨472580, by rfl⟩ : syracuseStep 630107 = 945161) B945161
theorem B6692219 : Blo 259821 6692219 := bstep (se 1 (by rfl) ⟨5019164, by rfl⟩ : syracuseStep 6692219 = 10038329) B10038329
theorem B666407 : Blo 259821 666407 := bstep (se 1 (by rfl) ⟨499805, by rfl⟩ : syracuseStep 666407 = 999611) B999611
theorem B19279295 : Blo 259821 19279295 := bstep (se 1 (by rfl) ⟨14459471, by rfl⟩ : syracuseStep 19279295 = 28918943) B28918943
theorem B6402989 : Blo 259821 6402989 := bstep (se 3 (by rfl) ⟨1200560, by rfl⟩ : syracuseStep 6402989 = 2401121) B2401121
theorem B439519 : Blo 259821 439519 := bstep (se 1 (by rfl) ⟨329639, by rfl⟩ : syracuseStep 439519 = 659279) B659279
theorem B2111105 : Blo 259821 2111105 := bstep (se 2 (by rfl) ⟨791664, by rfl⟩ : syracuseStep 2111105 = 1583329) B1583329
theorem B13582889 : Blo 259821 13582889 := bstep (se 2 (by rfl) ⟨5093583, by rfl⟩ : syracuseStep 13582889 = 10187167) B10187167
theorem B1426045 : Blo 259821 1426045 := bstep (se 3 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 1426045 = 534767) B534767
theorem B5786255 : Blo 259821 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B9129991 : Blo 259821 9129991 := bstep (se 1 (by rfl) ⟨6847493, by rfl⟩ : syracuseStep 9129991 = 13694987) B13694987
theorem B1136963 : Blo 259821 1136963 := bstep (se 1 (by rfl) ⟨852722, by rfl⟩ : syracuseStep 1136963 = 1705445) B1705445
theorem B3004937 : Blo 259821 3004937 := bstep (se 2 (by rfl) ⟨1126851, by rfl⟩ : syracuseStep 3004937 = 2253703) B2253703
theorem B4283239 : Blo 259821 4283239 := bstep (se 1 (by rfl) ⟨3212429, by rfl⟩ : syracuseStep 4283239 = 6424859) B6424859
theorem B1500443 : Blo 259821 1500443 := bstep (se 1 (by rfl) ⟨1125332, by rfl⟩ : syracuseStep 1500443 = 2250665) B2250665
theorem B3794309 : Blo 259821 3794309 := bstep (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) B711433
theorem B5696041 : Blo 259821 5696041 := bstep (se 2 (by rfl) ⟨2136015, by rfl⟩ : syracuseStep 5696041 = 4272031) B4272031
theorem B2223359 : Blo 259821 2223359 := bstep (se 1 (by rfl) ⟨1667519, by rfl⟩ : syracuseStep 2223359 = 3335039) B3335039
theorem B585215 : Blo 259821 585215 := bstep (se 1 (by rfl) ⟨438911, by rfl⟩ : syracuseStep 585215 = 877823) B877823
theorem B26209979 : Blo 259821 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B5041925 : Blo 259821 5041925 := bstep (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) B945361
theorem B749321 : Blo 259821 749321 := bstep (se 2 (by rfl) ⟨280995, by rfl⟩ : syracuseStep 749321 = 561991) B561991
theorem B422057 : Blo 259821 422057 := bstep (se 2 (by rfl) ⟨158271, by rfl⟩ : syracuseStep 422057 = 316543) B316543
theorem B586889 : Blo 259821 586889 := bstep (se 2 (by rfl) ⟨220083, by rfl⟩ : syracuseStep 586889 = 440167) B440167
theorem B586943 : Blo 259821 586943 := bstep (se 1 (by rfl) ⟨440207, by rfl⟩ : syracuseStep 586943 = 880415) B880415
theorem B2127131 : Blo 259821 2127131 := bstep (se 1 (by rfl) ⟨1595348, by rfl⟩ : syracuseStep 2127131 = 3190697) B3190697
theorem B4027751 : Blo 259821 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B2520503 : Blo 259821 2520503 := bstep (se 1 (by rfl) ⟨1890377, by rfl⟩ : syracuseStep 2520503 = 3780755) B3780755
theorem B13006747 : Blo 259821 13006747 := bstep (se 1 (by rfl) ⟨9755060, by rfl⟩ : syracuseStep 13006747 = 19510121) B19510121
theorem B587753 : Blo 259821 587753 := bstep (se 2 (by rfl) ⟨220407, by rfl⟩ : syracuseStep 587753 = 440815) B440815
theorem B260223 : Blo 259821 260223 := bstep (se 1 (by rfl) ⟨195167, by rfl⟩ : syracuseStep 260223 = 390335) B390335
theorem B260379 : Blo 259821 260379 := bstep (se 1 (by rfl) ⟨195284, by rfl⟩ : syracuseStep 260379 = 390569) B390569
theorem B883115 : Blo 259821 883115 := bstep (se 1 (by rfl) ⟨662336, by rfl⟩ : syracuseStep 883115 = 1324673) B1324673
theorem B392351 : Blo 259821 392351 := bstep (se 1 (by rfl) ⟨294263, by rfl⟩ : syracuseStep 392351 = 588527) B588527
theorem B1277137 : Blo 259821 1277137 := bstep (se 2 (by rfl) ⟨478926, by rfl⟩ : syracuseStep 1277137 = 957853) B957853
theorem B556379 : Blo 259821 556379 := bstep (se 1 (by rfl) ⟨417284, by rfl⟩ : syracuseStep 556379 = 834569) B834569
theorem B392831 : Blo 259821 392831 := bstep (se 1 (by rfl) ⟨294623, by rfl⟩ : syracuseStep 392831 = 589247) B589247
theorem B262395 : Blo 259821 262395 := bstep (se 1 (by rfl) ⟨196796, by rfl⟩ : syracuseStep 262395 = 393593) B393593
theorem B262639 : Blo 259821 262639 := bstep (se 1 (by rfl) ⟨196979, by rfl⟩ : syracuseStep 262639 = 393959) B393959
theorem B1901393 : Blo 259821 1901393 := bstep (se 2 (by rfl) ⟨713022, by rfl⟩ : syracuseStep 1901393 = 1426045) B1426045
theorem B2003291 : Blo 259821 2003291 := bstep (se 1 (by rfl) ⟨1502468, by rfl⟩ : syracuseStep 2003291 = 3004937) B3004937
theorem B4461479 : Blo 259821 4461479 := bstep (se 1 (by rfl) ⟨3346109, by rfl⟩ : syracuseStep 4461479 = 6692219) B6692219
theorem B2529539 : Blo 259821 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B1482239 : Blo 259821 1482239 := bstep (se 1 (by rfl) ⟨1111679, by rfl⟩ : syracuseStep 1482239 = 2223359) B2223359
theorem B12852863 : Blo 259821 12852863 := bstep (se 1 (by rfl) ⟨9639647, by rfl⟩ : syracuseStep 12852863 = 19279295) B19279295
theorem B17473319 : Blo 259821 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B499547 : Blo 259821 499547 := bstep (se 1 (by rfl) ⟨374660, by rfl⟩ : syracuseStep 499547 = 749321) B749321
theorem B4268659 : Blo 259821 4268659 := bstep (se 1 (by rfl) ⟨3201494, by rfl⟩ : syracuseStep 4268659 = 6402989) B6402989
theorem B1418087 : Blo 259821 1418087 := bstep (se 1 (by rfl) ⟨1063565, by rfl⟩ : syracuseStep 1418087 = 2127131) B2127131
theorem B1680335 : Blo 259821 1680335 := bstep (se 1 (by rfl) ⟨1260251, by rfl⟩ : syracuseStep 1680335 = 2520503) B2520503
theorem B5710985 : Blo 259821 5710985 := bstep (se 2 (by rfl) ⟨2141619, by rfl⟩ : syracuseStep 5710985 = 4283239) B4283239
theorem B370919 : Blo 259821 370919 := bstep (se 1 (by rfl) ⟨278189, by rfl⟩ : syracuseStep 370919 = 556379) B556379
theorem B9055259 : Blo 259821 9055259 := bstep (se 1 (by rfl) ⟨6791444, by rfl⟩ : syracuseStep 9055259 = 13582889) B13582889
theorem B1125485 : Blo 259821 1125485 := bstep (se 3 (by rfl) ⟨211028, by rfl⟩ : syracuseStep 1125485 = 422057) B422057
theorem B3585151 : Blo 259821 3585151 := bstep (se 1 (by rfl) ⟨2688863, by rfl⟩ : syracuseStep 3585151 = 5377727) B5377727
theorem B899791 : Blo 259821 899791 := bstep (se 1 (by rfl) ⟨674843, by rfl⟩ : syracuseStep 899791 = 1349687) B1349687
theorem B12173321 : Blo 259821 12173321 := bstep (se 2 (by rfl) ⟨4564995, by rfl⟩ : syracuseStep 12173321 = 9129991) B9129991
theorem B3031901 : Blo 259821 3031901 := bstep (se 3 (by rfl) ⟨568481, by rfl⟩ : syracuseStep 3031901 = 1136963) B1136963
theorem B1000295 : Blo 259821 1000295 := bstep (se 1 (by rfl) ⟨750221, by rfl⟩ : syracuseStep 1000295 = 1500443) B1500443
theorem B444271 : Blo 259821 444271 := bstep (se 1 (by rfl) ⟨333203, by rfl⟩ : syracuseStep 444271 = 666407) B666407
theorem B3361283 : Blo 259821 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B9591635 : Blo 259821 9591635 := bstep (se 1 (by rfl) ⟨7193726, by rfl⟩ : syracuseStep 9591635 = 14387453) B14387453
theorem B1334231 : Blo 259821 1334231 := bstep (se 1 (by rfl) ⟨1000673, by rfl⟩ : syracuseStep 1334231 = 2001347) B2001347
theorem B3857503 : Blo 259821 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B139616135 : Blo 259821 139616135 := bstep (se 1 (by rfl) ⟨104712101, by rfl⟩ : syracuseStep 139616135 = 209424203) B209424203
theorem B7594721 : Blo 259821 7594721 := bstep (se 2 (by rfl) ⟨2848020, by rfl⟩ : syracuseStep 7594721 = 5696041) B5696041
theorem B746759 : Blo 259821 746759 := bstep (se 1 (by rfl) ⟨560069, by rfl⟩ : syracuseStep 746759 = 1120139) B1120139
theorem B420071 : Blo 259821 420071 := bstep (se 1 (by rfl) ⟨315053, by rfl⟩ : syracuseStep 420071 = 630107) B630107
theorem B6811397 : Blo 259821 6811397 := bstep (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) B1277137
theorem B586025 : Blo 259821 586025 := bstep (se 2 (by rfl) ⟨219759, by rfl⟩ : syracuseStep 586025 = 439519) B439519
theorem B390143 : Blo 259821 390143 := bstep (se 1 (by rfl) ⟨292607, by rfl⟩ : syracuseStep 390143 = 585215) B585215
theorem B391259 : Blo 259821 391259 := bstep (se 1 (by rfl) ⟨293444, by rfl⟩ : syracuseStep 391259 = 586889) B586889
theorem B391295 : Blo 259821 391295 := bstep (se 1 (by rfl) ⟨293471, by rfl⟩ : syracuseStep 391295 = 586943) B586943
theorem B2685167 : Blo 259821 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B1407403 : Blo 259821 1407403 := bstep (se 1 (by rfl) ⟨1055552, by rfl⟩ : syracuseStep 1407403 = 2111105) B2111105
theorem B391835 : Blo 259821 391835 := bstep (se 1 (by rfl) ⟨293876, by rfl⟩ : syracuseStep 391835 = 587753) B587753
theorem B588743 : Blo 259821 588743 := bstep (se 1 (by rfl) ⟨441557, by rfl⟩ : syracuseStep 588743 = 883115) B883115
theorem B261567 : Blo 259821 261567 := bstep (se 1 (by rfl) ⟨196175, by rfl⟩ : syracuseStep 261567 = 392351) B392351
theorem B69369317 : Blo 259821 69369317 := bstep (se 4 (by rfl) ⟨6503373, by rfl⟩ : syracuseStep 69369317 = 13006747) B13006747
theorem B261887 : Blo 259821 261887 := bstep (se 1 (by rfl) ⟨196415, by rfl⟩ : syracuseStep 261887 = 392831) B392831
theorem B592361 : Blo 259821 592361 := bstep (se 2 (by rfl) ⟨222135, by rfl⟩ : syracuseStep 592361 = 444271) B444271
theorem B6394423 : Blo 259821 6394423 := bstep (se 1 (by rfl) ⟨4795817, by rfl⟩ : syracuseStep 6394423 = 9591635) B9591635
theorem B889487 : Blo 259821 889487 := bstep (se 1 (by rfl) ⟨667115, by rfl⟩ : syracuseStep 889487 = 1334231) B1334231
theorem B988159 : Blo 259821 988159 := bstep (se 1 (by rfl) ⟨741119, by rfl⟩ : syracuseStep 988159 = 1482239) B1482239
theorem B989117 : Blo 259821 989117 := bstep (se 3 (by rfl) ⟨185459, by rfl⟩ : syracuseStep 989117 = 370919) B370919
theorem B1120189 : Blo 259821 1120189 := bstep (se 3 (by rfl) ⟨210035, by rfl⟩ : syracuseStep 1120189 = 420071) B420071
theorem B1120223 : Blo 259821 1120223 := bstep (se 1 (by rfl) ⟨840167, by rfl⟩ : syracuseStep 1120223 = 1680335) B1680335
theorem B3807323 : Blo 259821 3807323 := bstep (se 1 (by rfl) ⟨2855492, by rfl⟩ : syracuseStep 3807323 = 5710985) B5710985
theorem B497839 : Blo 259821 497839 := bstep (se 1 (by rfl) ⟨373379, by rfl⟩ : syracuseStep 497839 = 746759) B746759
theorem B6036839 : Blo 259821 6036839 := bstep (se 1 (by rfl) ⟨4527629, by rfl⟩ : syracuseStep 6036839 = 9055259) B9055259
theorem B1876537 : Blo 259821 1876537 := bstep (se 2 (by rfl) ⟨703701, by rfl⟩ : syracuseStep 1876537 = 1407403) B1407403
theorem B46246211 : Blo 259821 46246211 := bstep (se 1 (by rfl) ⟨34684658, by rfl⟩ : syracuseStep 46246211 = 69369317) B69369317
theorem B666863 : Blo 259821 666863 := bstep (se 1 (by rfl) ⟨500147, by rfl⟩ : syracuseStep 666863 = 1000295) B1000295
theorem B2240855 : Blo 259821 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B3781565 : Blo 259821 3781565 := bstep (se 3 (by rfl) ⟨709043, by rfl⟩ : syracuseStep 3781565 = 1418087) B1418087
theorem B1686359 : Blo 259821 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B8568575 : Blo 259821 8568575 := bstep (se 1 (by rfl) ⟨6426431, by rfl⟩ : syracuseStep 8568575 = 12852863) B12852863
theorem B11648879 : Blo 259821 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B93077423 : Blo 259821 93077423 := bstep (se 1 (by rfl) ⟨69808067, by rfl⟩ : syracuseStep 93077423 = 139616135) B139616135
theorem B5063147 : Blo 259821 5063147 := bstep (se 1 (by rfl) ⟨3797360, by rfl⟩ : syracuseStep 5063147 = 7594721) B7594721
theorem B19120805 : Blo 259821 19120805 := bstep (se 4 (by rfl) ⟨1792575, by rfl⟩ : syracuseStep 19120805 = 3585151) B3585151
theorem B4540931 : Blo 259821 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B1790111 : Blo 259821 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B1332125 : Blo 259821 1332125 := bstep (se 3 (by rfl) ⟨249773, by rfl⟩ : syracuseStep 1332125 = 499547) B499547
theorem B8115547 : Blo 259821 8115547 := bstep (se 1 (by rfl) ⟨6086660, by rfl⟩ : syracuseStep 8115547 = 12173321) B12173321
theorem B1267595 : Blo 259821 1267595 := bstep (se 1 (by rfl) ⟨950696, by rfl⟩ : syracuseStep 1267595 = 1901393) B1901393
theorem B2021267 : Blo 259821 2021267 := bstep (se 1 (by rfl) ⟨1515950, by rfl⟩ : syracuseStep 2021267 = 3031901) B3031901
theorem B5691545 : Blo 259821 5691545 := bstep (se 2 (by rfl) ⟨2134329, by rfl⟩ : syracuseStep 5691545 = 4268659) B4268659
theorem B1335527 : Blo 259821 1335527 := bstep (se 1 (by rfl) ⟨1001645, by rfl⟩ : syracuseStep 1335527 = 2003291) B2003291
theorem B2974319 : Blo 259821 2974319 := bstep (se 1 (by rfl) ⟨2230739, by rfl⟩ : syracuseStep 2974319 = 4461479) B4461479
theorem B19195541 : Blo 259821 19195541 := bstep (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) B899791
theorem B750323 : Blo 259821 750323 := bstep (se 1 (by rfl) ⟨562742, by rfl⟩ : syracuseStep 750323 = 1125485) B1125485
theorem B390683 : Blo 259821 390683 := bstep (se 1 (by rfl) ⟨293012, by rfl⟩ : syracuseStep 390683 = 586025) B586025
theorem B260095 : Blo 259821 260095 := bstep (se 1 (by rfl) ⟨195071, by rfl⟩ : syracuseStep 260095 = 390143) B390143
theorem B260839 : Blo 259821 260839 := bstep (se 1 (by rfl) ⟨195629, by rfl⟩ : syracuseStep 260839 = 391259) B391259
theorem B260863 : Blo 259821 260863 := bstep (se 1 (by rfl) ⟨195647, by rfl⟩ : syracuseStep 260863 = 391295) B391295
theorem B5143337 : Blo 259821 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B261223 : Blo 259821 261223 := bstep (se 1 (by rfl) ⟨195917, by rfl⟩ : syracuseStep 261223 = 391835) B391835
theorem B392495 : Blo 259821 392495 := bstep (se 1 (by rfl) ⟨294371, by rfl⟩ : syracuseStep 392495 = 588743) B588743
theorem B3375431 : Blo 259821 3375431 := bstep (se 1 (by rfl) ⟨2531573, by rfl⟩ : syracuseStep 3375431 = 5063147) B5063147
theorem B12747203 : Blo 259821 12747203 := bstep (se 1 (by rfl) ⟨9560402, by rfl⟩ : syracuseStep 12747203 = 19120805) B19120805
theorem B394907 : Blo 259821 394907 := bstep (se 1 (by rfl) ⟨296180, by rfl⟩ : syracuseStep 394907 = 592361) B592361
theorem B2000861 : Blo 259821 2000861 := bstep (se 3 (by rfl) ⟨375161, by rfl⟩ : syracuseStep 2000861 = 750323) B750323
theorem B592991 : Blo 259821 592991 := bstep (se 1 (by rfl) ⟨444743, by rfl⟩ : syracuseStep 592991 = 889487) B889487
theorem B888083 : Blo 259821 888083 := bstep (se 1 (by rfl) ⟨666062, by rfl⟩ : syracuseStep 888083 = 1332125) B1332125
theorem B1347511 : Blo 259821 1347511 := bstep (se 1 (by rfl) ⟨1010633, by rfl⟩ : syracuseStep 1347511 = 2021267) B2021267
theorem B659411 : Blo 259821 659411 := bstep (se 1 (by rfl) ⟨494558, by rfl⟩ : syracuseStep 659411 = 989117) B989117
theorem B890351 : Blo 259821 890351 := bstep (se 1 (by rfl) ⟨667763, by rfl⟩ : syracuseStep 890351 = 1335527) B1335527
theorem B8525897 : Blo 259821 8525897 := bstep (se 2 (by rfl) ⟨3197211, by rfl⟩ : syracuseStep 8525897 = 6394423) B6394423
theorem B1317545 : Blo 259821 1317545 := bstep (se 2 (by rfl) ⟨494079, by rfl⟩ : syracuseStep 1317545 = 988159) B988159
theorem B10820729 : Blo 259821 10820729 := bstep (se 2 (by rfl) ⟨4057773, by rfl⟩ : syracuseStep 10820729 = 8115547) B8115547
theorem B663785 : Blo 259821 663785 := bstep (se 2 (by rfl) ⟨248919, by rfl⟩ : syracuseStep 663785 = 497839) B497839
theorem B1124239 : Blo 259821 1124239 := bstep (se 1 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 1124239 = 1686359) B1686359
theorem B5712383 : Blo 259821 5712383 := bstep (se 1 (by rfl) ⟨4284287, by rfl⟩ : syracuseStep 5712383 = 8568575) B8568575
theorem B2502049 : Blo 259821 2502049 := bstep (se 2 (by rfl) ⟨938268, by rfl⟩ : syracuseStep 2502049 = 1876537) B1876537
theorem B3027287 : Blo 259821 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B2538215 : Blo 259821 2538215 := bstep (se 1 (by rfl) ⟨1903661, by rfl⟩ : syracuseStep 2538215 = 3807323) B3807323
theorem B1982879 : Blo 259821 1982879 := bstep (se 1 (by rfl) ⟨1487159, by rfl⟩ : syracuseStep 1982879 = 2974319) B2974319
theorem B12797027 : Blo 259821 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B444575 : Blo 259821 444575 := bstep (se 1 (by rfl) ⟨333431, by rfl⟩ : syracuseStep 444575 = 666863) B666863
theorem B1493585 : Blo 259821 1493585 := bstep (se 2 (by rfl) ⟨560094, by rfl⟩ : syracuseStep 1493585 = 1120189) B1120189
theorem B1493903 : Blo 259821 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B3428891 : Blo 259821 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B62051615 : Blo 259821 62051615 := bstep (se 1 (by rfl) ⟨46538711, by rfl⟩ : syracuseStep 62051615 = 93077423) B93077423
theorem B4773629 : Blo 259821 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B845063 : Blo 259821 845063 := bstep (se 1 (by rfl) ⟨633797, by rfl⟩ : syracuseStep 845063 = 1267595) B1267595
theorem B746815 : Blo 259821 746815 := bstep (se 1 (by rfl) ⟨560111, by rfl⟩ : syracuseStep 746815 = 1120223) B1120223
theorem B3794363 : Blo 259821 3794363 := bstep (se 1 (by rfl) ⟨2845772, by rfl⟩ : syracuseStep 3794363 = 5691545) B5691545
theorem B4024559 : Blo 259821 4024559 := bstep (se 1 (by rfl) ⟨3018419, by rfl⟩ : syracuseStep 4024559 = 6036839) B6036839
theorem B30830807 : Blo 259821 30830807 := bstep (se 1 (by rfl) ⟨23123105, by rfl⟩ : syracuseStep 30830807 = 46246211) B46246211
theorem B2521043 : Blo 259821 2521043 := bstep (se 1 (by rfl) ⟨1890782, by rfl⟩ : syracuseStep 2521043 = 3781565) B3781565
theorem B260455 : Blo 259821 260455 := bstep (se 1 (by rfl) ⟨195341, by rfl⟩ : syracuseStep 260455 = 390683) B390683
theorem B261663 : Blo 259821 261663 := bstep (se 1 (by rfl) ⟨196247, by rfl⟩ : syracuseStep 261663 = 392495) B392495
theorem B7765919 : Blo 259821 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B263271 : Blo 259821 263271 := bstep (se 1 (by rfl) ⟨197453, by rfl⟩ : syracuseStep 263271 = 394907) B394907
theorem B296383 : Blo 259821 296383 := bstep (se 1 (by rfl) ⟨222287, by rfl⟩ : syracuseStep 296383 = 444575) B444575
theorem B395327 : Blo 259821 395327 := bstep (se 1 (by rfl) ⟨296495, by rfl⟩ : syracuseStep 395327 = 592991) B592991
theorem B592055 : Blo 259821 592055 := bstep (se 1 (by rfl) ⟨444041, by rfl⟩ : syracuseStep 592055 = 888083) B888083
theorem B593567 : Blo 259821 593567 := bstep (se 1 (by rfl) ⟨445175, by rfl⟩ : syracuseStep 593567 = 890351) B890351
theorem B3182419 : Blo 259821 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B7213819 : Blo 259821 7213819 := bstep (se 1 (by rfl) ⟨5410364, by rfl⟩ : syracuseStep 7213819 = 10820729) B10820729
theorem B563375 : Blo 259821 563375 := bstep (se 1 (by rfl) ⟨422531, by rfl⟩ : syracuseStep 563375 = 845063) B845063
theorem B2529575 : Blo 259821 2529575 := bstep (se 1 (by rfl) ⟨1897181, by rfl⟩ : syracuseStep 2529575 = 3794363) B3794363
theorem B3808255 : Blo 259821 3808255 := bstep (se 1 (by rfl) ⟨2856191, by rfl⟩ : syracuseStep 3808255 = 5712383) B5712383
theorem B20553871 : Blo 259821 20553871 := bstep (se 1 (by rfl) ⟨15415403, by rfl⟩ : syracuseStep 20553871 = 30830807) B30830807
theorem B1680695 : Blo 259821 1680695 := bstep (se 1 (by rfl) ⟨1260521, by rfl⟩ : syracuseStep 1680695 = 2521043) B2521043
theorem B1321919 : Blo 259821 1321919 := bstep (se 1 (by rfl) ⟨991439, by rfl⟩ : syracuseStep 1321919 = 1982879) B1982879
theorem B8498135 : Blo 259821 8498135 := bstep (se 1 (by rfl) ⟨6373601, by rfl⟩ : syracuseStep 8498135 = 12747203) B12747203
theorem B8531351 : Blo 259821 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B995723 : Blo 259821 995723 := bstep (se 1 (by rfl) ⟨746792, by rfl⟩ : syracuseStep 995723 = 1493585) B1493585
theorem B995753 : Blo 259821 995753 := bstep (se 2 (by rfl) ⟨373407, by rfl⟩ : syracuseStep 995753 = 746815) B746815
theorem B995935 : Blo 259821 995935 := bstep (se 1 (by rfl) ⟨746951, by rfl⟩ : syracuseStep 995935 = 1493903) B1493903
theorem B439607 : Blo 259821 439607 := bstep (se 1 (by rfl) ⟨329705, by rfl⟩ : syracuseStep 439607 = 659411) B659411
theorem B41367743 : Blo 259821 41367743 := bstep (se 1 (by rfl) ⟨31025807, by rfl⟩ : syracuseStep 41367743 = 62051615) B62051615
theorem B5683931 : Blo 259821 5683931 := bstep (se 1 (by rfl) ⟨4262948, by rfl⟩ : syracuseStep 5683931 = 8525897) B8525897
theorem B442523 : Blo 259821 442523 := bstep (se 1 (by rfl) ⟨331892, by rfl⟩ : syracuseStep 442523 = 663785) B663785
theorem B2018191 : Blo 259821 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B1692143 : Blo 259821 1692143 := bstep (se 1 (by rfl) ⟨1269107, by rfl⟩ : syracuseStep 1692143 = 2538215) B2538215
theorem B2250287 : Blo 259821 2250287 := bstep (se 1 (by rfl) ⟨1687715, by rfl⟩ : syracuseStep 2250287 = 3375431) B3375431
theorem B1333907 : Blo 259821 1333907 := bstep (se 1 (by rfl) ⟨1000430, by rfl⟩ : syracuseStep 1333907 = 2000861) B2000861
theorem B1498985 : Blo 259821 1498985 := bstep (se 2 (by rfl) ⟨562119, by rfl⟩ : syracuseStep 1498985 = 1124239) B1124239
theorem B2285927 : Blo 259821 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B878363 : Blo 259821 878363 := bstep (se 1 (by rfl) ⟨658772, by rfl⟩ : syracuseStep 878363 = 1317545) B1317545
theorem B3336065 : Blo 259821 3336065 := bstep (se 2 (by rfl) ⟨1251024, by rfl⟩ : syracuseStep 3336065 = 2502049) B2502049
theorem B1796681 : Blo 259821 1796681 := bstep (se 2 (by rfl) ⟨673755, by rfl⟩ : syracuseStep 1796681 = 1347511) B1347511
theorem B2683039 : Blo 259821 2683039 := bstep (se 1 (by rfl) ⟨2012279, by rfl⟩ : syracuseStep 2683039 = 4024559) B4024559
theorem B5177279 : Blo 259821 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B295015 : Blo 259821 295015 := bstep (se 1 (by rfl) ⟨221261, by rfl⟩ : syracuseStep 295015 = 442523) B442523
theorem B263551 : Blo 259821 263551 := bstep (se 1 (by rfl) ⟨197663, by rfl⟩ : syracuseStep 263551 = 395327) B395327
theorem B394703 : Blo 259821 394703 := bstep (se 1 (by rfl) ⟨296027, by rfl⟩ : syracuseStep 394703 = 592055) B592055
theorem B395177 : Blo 259821 395177 := bstep (se 2 (by rfl) ⟨148191, by rfl⟩ : syracuseStep 395177 = 296383) B296383
theorem B395711 : Blo 259821 395711 := bstep (se 1 (by rfl) ⟨296783, by rfl⟩ : syracuseStep 395711 = 593567) B593567
theorem B2690921 : Blo 259821 2690921 := bstep (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) B2018191
theorem B889271 : Blo 259821 889271 := bstep (se 1 (by rfl) ⟨666953, by rfl⟩ : syracuseStep 889271 = 1333907) B1333907
theorem B3577385 : Blo 259821 3577385 := bstep (se 2 (by rfl) ⟨1341519, by rfl⟩ : syracuseStep 3577385 = 2683039) B2683039
theorem B1120463 : Blo 259821 1120463 := bstep (se 1 (by rfl) ⟨840347, by rfl⟩ : syracuseStep 1120463 = 1680695) B1680695
theorem B4791149 : Blo 259821 4791149 := bstep (se 3 (by rfl) ⟨898340, by rfl⟩ : syracuseStep 4791149 = 1796681) B1796681
theorem B663815 : Blo 259821 663815 := bstep (se 1 (by rfl) ⟨497861, by rfl⟩ : syracuseStep 663815 = 995723) B995723
theorem B663835 : Blo 259821 663835 := bstep (se 1 (by rfl) ⟨497876, by rfl⟩ : syracuseStep 663835 = 995753) B995753
theorem B13806077 : Blo 259821 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B27405161 : Blo 259821 27405161 := bstep (se 2 (by rfl) ⟨10276935, by rfl⟩ : syracuseStep 27405161 = 20553871) B20553871
theorem B1128095 : Blo 259821 1128095 := bstep (se 1 (by rfl) ⟨846071, by rfl⟩ : syracuseStep 1128095 = 1692143) B1692143
theorem B1686383 : Blo 259821 1686383 := bstep (se 1 (by rfl) ⟨1264787, by rfl⟩ : syracuseStep 1686383 = 2529575) B2529575
theorem B4243225 : Blo 259821 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B999323 : Blo 259821 999323 := bstep (se 1 (by rfl) ⟨749492, by rfl⟩ : syracuseStep 999323 = 1498985) B1498985
theorem B1523951 : Blo 259821 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B1327913 : Blo 259821 1327913 := bstep (se 2 (by rfl) ⟨497967, by rfl⟩ : syracuseStep 1327913 = 995935) B995935
theorem B9618425 : Blo 259821 9618425 := bstep (se 2 (by rfl) ⟨3606909, by rfl⟩ : syracuseStep 9618425 = 7213819) B7213819
theorem B5687567 : Blo 259821 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B27578495 : Blo 259821 27578495 := bstep (se 1 (by rfl) ⟨20683871, by rfl⟩ : syracuseStep 27578495 = 41367743) B41367743
theorem B3789287 : Blo 259821 3789287 := bstep (se 1 (by rfl) ⟨2841965, by rfl⟩ : syracuseStep 3789287 = 5683931) B5683931
theorem B1500191 : Blo 259821 1500191 := bstep (se 1 (by rfl) ⟨1125143, by rfl⟩ : syracuseStep 1500191 = 2250287) B2250287
theorem B1502333 : Blo 259821 1502333 := bstep (se 3 (by rfl) ⟨281687, by rfl⟩ : syracuseStep 1502333 = 563375) B563375
theorem B585575 : Blo 259821 585575 := bstep (se 1 (by rfl) ⟨439181, by rfl⟩ : syracuseStep 585575 = 878363) B878363
theorem B2224043 : Blo 259821 2224043 := bstep (se 1 (by rfl) ⟨1668032, by rfl⟩ : syracuseStep 2224043 = 3336065) B3336065
theorem B881279 : Blo 259821 881279 := bstep (se 1 (by rfl) ⟨660959, by rfl⟩ : syracuseStep 881279 = 1321919) B1321919
theorem B5665423 : Blo 259821 5665423 := bstep (se 1 (by rfl) ⟨4249067, by rfl⟩ : syracuseStep 5665423 = 8498135) B8498135
theorem B293071 : Blo 259821 293071 := bstep (se 1 (by rfl) ⟨219803, by rfl⟩ : syracuseStep 293071 = 439607) B439607
theorem B5077673 : Blo 259821 5077673 := bstep (se 2 (by rfl) ⟨1904127, by rfl⟩ : syracuseStep 5077673 = 3808255) B3808255
theorem B393353 : Blo 259821 393353 := bstep (se 2 (by rfl) ⟨147507, by rfl⟩ : syracuseStep 393353 = 295015) B295015
theorem B1015967 : Blo 259821 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B885113 : Blo 259821 885113 := bstep (se 2 (by rfl) ⟨331917, by rfl⟩ : syracuseStep 885113 = 663835) B663835
theorem B885275 : Blo 259821 885275 := bstep (se 1 (by rfl) ⟨663956, by rfl⟩ : syracuseStep 885275 = 1327913) B1327913
theorem B263135 : Blo 259821 263135 := bstep (se 1 (by rfl) ⟨197351, by rfl⟩ : syracuseStep 263135 = 394703) B394703
theorem B263451 : Blo 259821 263451 := bstep (se 1 (by rfl) ⟨197588, by rfl⟩ : syracuseStep 263451 = 395177) B395177
theorem B263807 : Blo 259821 263807 := bstep (se 1 (by rfl) ⟨197855, by rfl⟩ : syracuseStep 263807 = 395711) B395711
theorem B18385663 : Blo 259821 18385663 := bstep (se 1 (by rfl) ⟨13789247, by rfl⟩ : syracuseStep 18385663 = 27578495) B27578495
theorem B592847 : Blo 259821 592847 := bstep (se 1 (by rfl) ⟨444635, by rfl⟩ : syracuseStep 592847 = 889271) B889271
theorem B2526191 : Blo 259821 2526191 := bstep (se 1 (by rfl) ⟨1894643, by rfl⟩ : syracuseStep 2526191 = 3789287) B3789287
theorem B9539693 : Blo 259821 9539693 := bstep (se 3 (by rfl) ⟨1788692, by rfl⟩ : syracuseStep 9539693 = 3577385) B3577385
theorem B1482695 : Blo 259821 1482695 := bstep (se 1 (by rfl) ⟨1112021, by rfl⟩ : syracuseStep 1482695 = 2224043) B2224043
theorem B3385115 : Blo 259821 3385115 := bstep (se 1 (by rfl) ⟨2538836, by rfl⟩ : syracuseStep 3385115 = 5077673) B5077673
theorem B1124255 : Blo 259821 1124255 := bstep (se 1 (by rfl) ⟨843191, by rfl⟩ : syracuseStep 1124255 = 1686383) B1686383
theorem B666215 : Blo 259821 666215 := bstep (se 1 (by rfl) ⟨499661, by rfl⟩ : syracuseStep 666215 = 999323) B999323
theorem B3194099 : Blo 259821 3194099 := bstep (se 1 (by rfl) ⟨2395574, by rfl⟩ : syracuseStep 3194099 = 4791149) B4791149
theorem B442543 : Blo 259821 442543 := bstep (se 1 (by rfl) ⟨331907, by rfl⟩ : syracuseStep 442543 = 663815) B663815
theorem B1000127 : Blo 259821 1000127 := bstep (se 1 (by rfl) ⟨750095, by rfl⟩ : syracuseStep 1000127 = 1500191) B1500191
theorem B7553897 : Blo 259821 7553897 := bstep (se 2 (by rfl) ⟨2832711, by rfl⟩ : syracuseStep 7553897 = 5665423) B5665423
theorem B36816205 : Blo 259821 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B18270107 : Blo 259821 18270107 := bstep (se 1 (by rfl) ⟨13702580, by rfl⟩ : syracuseStep 18270107 = 27405161) B27405161
theorem B1001555 : Blo 259821 1001555 := bstep (se 1 (by rfl) ⟨751166, by rfl⟩ : syracuseStep 1001555 = 1502333) B1502333
theorem B5657633 : Blo 259821 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B6412283 : Blo 259821 6412283 := bstep (se 1 (by rfl) ⟨4809212, by rfl⟩ : syracuseStep 6412283 = 9618425) B9618425
theorem B3791711 : Blo 259821 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B746975 : Blo 259821 746975 := bstep (se 1 (by rfl) ⟨560231, by rfl⟩ : syracuseStep 746975 = 1120463) B1120463
theorem B390383 : Blo 259821 390383 := bstep (se 1 (by rfl) ⟨292787, by rfl⟩ : syracuseStep 390383 = 585575) B585575
theorem B390761 : Blo 259821 390761 := bstep (se 2 (by rfl) ⟨146535, by rfl⟩ : syracuseStep 390761 = 293071) B293071
theorem B587519 : Blo 259821 587519 := bstep (se 1 (by rfl) ⟨440639, by rfl⟩ : syracuseStep 587519 = 881279) B881279
theorem B752063 : Blo 259821 752063 := bstep (se 1 (by rfl) ⟨564047, by rfl⟩ : syracuseStep 752063 = 1128095) B1128095
theorem B7175789 : Blo 259821 7175789 := bstep (se 3 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 7175789 = 2690921) B2690921
theorem B262235 : Blo 259821 262235 := bstep (se 1 (by rfl) ⟨196676, by rfl⟩ : syracuseStep 262235 = 393353) B393353
theorem B590057 : Blo 259821 590057 := bstep (se 2 (by rfl) ⟨221271, by rfl⟩ : syracuseStep 590057 = 442543) B442543
theorem B590075 : Blo 259821 590075 := bstep (se 1 (by rfl) ⟨442556, by rfl⟩ : syracuseStep 590075 = 885113) B885113
theorem B590183 : Blo 259821 590183 := bstep (se 1 (by rfl) ⟨442637, by rfl⟩ : syracuseStep 590183 = 885275) B885275
theorem B49088273 : Blo 259821 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B395231 : Blo 259821 395231 := bstep (se 1 (by rfl) ⟨296423, by rfl⟩ : syracuseStep 395231 = 592847) B592847
theorem B6359795 : Blo 259821 6359795 := bstep (se 1 (by rfl) ⟨4769846, by rfl⟩ : syracuseStep 6359795 = 9539693) B9539693
theorem B3771755 : Blo 259821 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B24514217 : Blo 259821 24514217 := bstep (se 2 (by rfl) ⟨9192831, by rfl⟩ : syracuseStep 24514217 = 18385663) B18385663
theorem B2527807 : Blo 259821 2527807 := bstep (se 1 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 2527807 = 3791711) B3791711
theorem B988463 : Blo 259821 988463 := bstep (se 1 (by rfl) ⟨741347, by rfl⟩ : syracuseStep 988463 = 1482695) B1482695
theorem B497983 : Blo 259821 497983 := bstep (se 1 (by rfl) ⟨373487, by rfl⟩ : syracuseStep 497983 = 746975) B746975
theorem B2005501 : Blo 259821 2005501 := bstep (se 3 (by rfl) ⟨376031, by rfl⟩ : syracuseStep 2005501 = 752063) B752063
theorem B666751 : Blo 259821 666751 := bstep (se 1 (by rfl) ⟨500063, by rfl⟩ : syracuseStep 666751 = 1000127) B1000127
theorem B667703 : Blo 259821 667703 := bstep (se 1 (by rfl) ⟨500777, by rfl⟩ : syracuseStep 667703 = 1001555) B1001555
theorem B1684127 : Blo 259821 1684127 := bstep (se 1 (by rfl) ⟨1263095, by rfl⟩ : syracuseStep 1684127 = 2526191) B2526191
theorem B4274855 : Blo 259821 4274855 := bstep (se 1 (by rfl) ⟨3206141, by rfl⟩ : syracuseStep 4274855 = 6412283) B6412283
theorem B444143 : Blo 259821 444143 := bstep (se 1 (by rfl) ⟨333107, by rfl⟩ : syracuseStep 444143 = 666215) B666215
theorem B2709245 : Blo 259821 2709245 := bstep (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) B1015967
theorem B5035931 : Blo 259821 5035931 := bstep (se 1 (by rfl) ⟨3776948, by rfl⟩ : syracuseStep 5035931 = 7553897) B7553897
theorem B12180071 : Blo 259821 12180071 := bstep (se 1 (by rfl) ⟨9135053, by rfl⟩ : syracuseStep 12180071 = 18270107) B18270107
theorem B2256743 : Blo 259821 2256743 := bstep (se 1 (by rfl) ⟨1692557, by rfl⟩ : syracuseStep 2256743 = 3385115) B3385115
theorem B749503 : Blo 259821 749503 := bstep (se 1 (by rfl) ⟨562127, by rfl⟩ : syracuseStep 749503 = 1124255) B1124255
theorem B260255 : Blo 259821 260255 := bstep (se 1 (by rfl) ⟨195191, by rfl⟩ : syracuseStep 260255 = 390383) B390383
theorem B260507 : Blo 259821 260507 := bstep (se 1 (by rfl) ⟨195380, by rfl⟩ : syracuseStep 260507 = 390761) B390761
theorem B391679 : Blo 259821 391679 := bstep (se 1 (by rfl) ⟨293759, by rfl⟩ : syracuseStep 391679 = 587519) B587519
theorem B2129399 : Blo 259821 2129399 := bstep (se 1 (by rfl) ⟨1597049, by rfl⟩ : syracuseStep 2129399 = 3194099) B3194099
theorem B4783859 : Blo 259821 4783859 := bstep (se 1 (by rfl) ⟨3587894, by rfl⟩ : syracuseStep 4783859 = 7175789) B7175789
theorem B393371 : Blo 259821 393371 := bstep (se 1 (by rfl) ⟨295028, by rfl⟩ : syracuseStep 393371 = 590057) B590057
theorem B393383 : Blo 259821 393383 := bstep (se 1 (by rfl) ⟨295037, by rfl⟩ : syracuseStep 393383 = 590075) B590075
theorem B393455 : Blo 259821 393455 := bstep (se 1 (by rfl) ⟨295091, by rfl⟩ : syracuseStep 393455 = 590183) B590183
theorem B296095 : Blo 259821 296095 := bstep (se 1 (by rfl) ⟨222071, by rfl⟩ : syracuseStep 296095 = 444143) B444143
theorem B263487 : Blo 259821 263487 := bstep (se 1 (by rfl) ⟨197615, by rfl⟩ : syracuseStep 263487 = 395231) B395231
theorem B658975 : Blo 259821 658975 := bstep (se 1 (by rfl) ⟨494231, by rfl⟩ : syracuseStep 658975 = 988463) B988463
theorem B889001 : Blo 259821 889001 := bstep (se 2 (by rfl) ⟨333375, by rfl⟩ : syracuseStep 889001 = 666751) B666751
theorem B523608245 : Blo 259821 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B663977 : Blo 259821 663977 := bstep (se 2 (by rfl) ⟨248991, by rfl⟩ : syracuseStep 663977 = 497983) B497983
theorem B1122751 : Blo 259821 1122751 := bstep (se 1 (by rfl) ⟨842063, by rfl⟩ : syracuseStep 1122751 = 1684127) B1684127
theorem B1419599 : Blo 259821 1419599 := bstep (se 1 (by rfl) ⟨1064699, by rfl⟩ : syracuseStep 1419599 = 2129399) B2129399
theorem B3189239 : Blo 259821 3189239 := bstep (se 1 (by rfl) ⟨2391929, by rfl⟩ : syracuseStep 3189239 = 4783859) B4783859
theorem B4239863 : Blo 259821 4239863 := bstep (se 1 (by rfl) ⟨3179897, by rfl⟩ : syracuseStep 4239863 = 6359795) B6359795
theorem B3357287 : Blo 259821 3357287 := bstep (se 1 (by rfl) ⟨2517965, by rfl⟩ : syracuseStep 3357287 = 5035931) B5035931
theorem B7224653 : Blo 259821 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B999337 : Blo 259821 999337 := bstep (se 2 (by rfl) ⟨374751, by rfl⟩ : syracuseStep 999337 = 749503) B749503
theorem B445135 : Blo 259821 445135 := bstep (se 1 (by rfl) ⟨333851, by rfl⟩ : syracuseStep 445135 = 667703) B667703
theorem B2674001 : Blo 259821 2674001 := bstep (se 2 (by rfl) ⟨1002750, by rfl⟩ : syracuseStep 2674001 = 2005501) B2005501
theorem B2514503 : Blo 259821 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B16342811 : Blo 259821 16342811 := bstep (se 1 (by rfl) ⟨12257108, by rfl⟩ : syracuseStep 16342811 = 24514217) B24514217
theorem B8120047 : Blo 259821 8120047 := bstep (se 1 (by rfl) ⟨6090035, by rfl⟩ : syracuseStep 8120047 = 12180071) B12180071
theorem B3370409 : Blo 259821 3370409 := bstep (se 2 (by rfl) ⟨1263903, by rfl⟩ : syracuseStep 3370409 = 2527807) B2527807
theorem B1504495 : Blo 259821 1504495 := bstep (se 1 (by rfl) ⟨1128371, by rfl⟩ : syracuseStep 1504495 = 2256743) B2256743
theorem B261119 : Blo 259821 261119 := bstep (se 1 (by rfl) ⟨195839, by rfl⟩ : syracuseStep 261119 = 391679) B391679
theorem B2849903 : Blo 259821 2849903 := bstep (se 1 (by rfl) ⟨2137427, by rfl⟩ : syracuseStep 2849903 = 4274855) B4274855
theorem B262247 : Blo 259821 262247 := bstep (se 1 (by rfl) ⟨196685, by rfl⟩ : syracuseStep 262247 = 393371) B393371
theorem B262255 : Blo 259821 262255 := bstep (se 1 (by rfl) ⟨196691, by rfl⟩ : syracuseStep 262255 = 393383) B393383
theorem B262303 : Blo 259821 262303 := bstep (se 1 (by rfl) ⟨196727, by rfl⟩ : syracuseStep 262303 = 393455) B393455
theorem B394793 : Blo 259821 394793 := bstep (se 2 (by rfl) ⟨148047, by rfl⟩ : syracuseStep 394793 = 296095) B296095
theorem B592667 : Blo 259821 592667 := bstep (se 1 (by rfl) ⟨444500, by rfl⟩ : syracuseStep 592667 = 889001) B889001
theorem B593513 : Blo 259821 593513 := bstep (se 2 (by rfl) ⟨222567, by rfl⟩ : syracuseStep 593513 = 445135) B445135
theorem B2005993 : Blo 259821 2005993 := bstep (se 2 (by rfl) ⟨752247, by rfl⟩ : syracuseStep 2005993 = 1504495) B1504495
theorem B2826575 : Blo 259821 2826575 := bstep (se 1 (by rfl) ⟨2119931, by rfl⟩ : syracuseStep 2826575 = 4239863) B4239863
theorem B2238191 : Blo 259821 2238191 := bstep (se 1 (by rfl) ⟨1678643, by rfl⟩ : syracuseStep 2238191 = 3357287) B3357287
theorem B1782667 : Blo 259821 1782667 := bstep (se 1 (by rfl) ⟨1337000, by rfl⟩ : syracuseStep 1782667 = 2674001) B2674001
theorem B10826729 : Blo 259821 10826729 := bstep (se 2 (by rfl) ⟨4060023, by rfl⟩ : syracuseStep 10826729 = 8120047) B8120047
theorem B10895207 : Blo 259821 10895207 := bstep (se 1 (by rfl) ⟨8171405, by rfl⟩ : syracuseStep 10895207 = 16342811) B16342811
theorem B442651 : Blo 259821 442651 := bstep (se 1 (by rfl) ⟨331988, by rfl⟩ : syracuseStep 442651 = 663977) B663977
theorem B2246939 : Blo 259821 2246939 := bstep (se 1 (by rfl) ⟨1685204, by rfl⟩ : syracuseStep 2246939 = 3370409) B3370409
theorem B6705341 : Blo 259821 6705341 := bstep (se 3 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 6705341 = 2514503) B2514503
theorem B1332449 : Blo 259821 1332449 := bstep (se 2 (by rfl) ⟨499668, by rfl⟩ : syracuseStep 1332449 = 999337) B999337
theorem B1497001 : Blo 259821 1497001 := bstep (se 2 (by rfl) ⟨561375, by rfl⟩ : syracuseStep 1497001 = 1122751) B1122751
theorem B878633 : Blo 259821 878633 := bstep (se 2 (by rfl) ⟨329487, by rfl⟩ : syracuseStep 878633 = 658975) B658975
theorem B349072163 : Blo 259821 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B946399 : Blo 259821 946399 := bstep (se 1 (by rfl) ⟨709799, by rfl⟩ : syracuseStep 946399 = 1419599) B1419599
theorem B2126159 : Blo 259821 2126159 := bstep (se 1 (by rfl) ⟨1594619, by rfl⟩ : syracuseStep 2126159 = 3189239) B3189239
theorem B1899935 : Blo 259821 1899935 := bstep (se 1 (by rfl) ⟨1424951, by rfl⟩ : syracuseStep 1899935 = 2849903) B2849903
theorem B4816435 : Blo 259821 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B590201 : Blo 259821 590201 := bstep (se 2 (by rfl) ⟨221325, by rfl⟩ : syracuseStep 590201 = 442651) B442651
theorem B263195 : Blo 259821 263195 := bstep (se 1 (by rfl) ⟨197396, by rfl⟩ : syracuseStep 263195 = 394793) B394793
theorem B395111 : Blo 259821 395111 := bstep (se 1 (by rfl) ⟨296333, by rfl⟩ : syracuseStep 395111 = 592667) B592667
theorem B395675 : Blo 259821 395675 := bstep (se 1 (by rfl) ⟨296756, by rfl⟩ : syracuseStep 395675 = 593513) B593513
theorem B888299 : Blo 259821 888299 := bstep (se 1 (by rfl) ⟨666224, by rfl⟩ : syracuseStep 888299 = 1332449) B1332449
theorem B9507557 : Blo 259821 9507557 := bstep (se 4 (by rfl) ⟨891333, by rfl⟩ : syracuseStep 9507557 = 1782667) B1782667
theorem B1417439 : Blo 259821 1417439 := bstep (se 1 (by rfl) ⟨1063079, by rfl⟩ : syracuseStep 1417439 = 2126159) B2126159
theorem B7217819 : Blo 259821 7217819 := bstep (se 1 (by rfl) ⟨5413364, by rfl⟩ : syracuseStep 7217819 = 10826729) B10826729
theorem B4470227 : Blo 259821 4470227 := bstep (se 1 (by rfl) ⟨3352670, by rfl⟩ : syracuseStep 4470227 = 6705341) B6705341
theorem B1884383 : Blo 259821 1884383 := bstep (se 1 (by rfl) ⟨1413287, by rfl⟩ : syracuseStep 1884383 = 2826575) B2826575
theorem B1261865 : Blo 259821 1261865 := bstep (se 2 (by rfl) ⟨473199, by rfl⟩ : syracuseStep 1261865 = 946399) B946399
theorem B1492127 : Blo 259821 1492127 := bstep (se 1 (by rfl) ⟨1119095, by rfl⟩ : syracuseStep 1492127 = 2238191) B2238191
theorem B2674657 : Blo 259821 2674657 := bstep (se 2 (by rfl) ⟨1002996, by rfl⟩ : syracuseStep 2674657 = 2005993) B2005993
theorem B29053885 : Blo 259821 29053885 := bstep (se 3 (by rfl) ⟨5447603, by rfl⟩ : syracuseStep 29053885 = 10895207) B10895207
theorem B1266623 : Blo 259821 1266623 := bstep (se 1 (by rfl) ⟨949967, by rfl⟩ : syracuseStep 1266623 = 1899935) B1899935
theorem B1497959 : Blo 259821 1497959 := bstep (se 1 (by rfl) ⟨1123469, by rfl⟩ : syracuseStep 1497959 = 2246939) B2246939
theorem B585755 : Blo 259821 585755 := bstep (se 1 (by rfl) ⟨439316, by rfl⟩ : syracuseStep 585755 = 878633) B878633
theorem B232714775 : Blo 259821 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B1996001 : Blo 259821 1996001 := bstep (se 2 (by rfl) ⟨748500, by rfl⟩ : syracuseStep 1996001 = 1497001) B1497001
theorem B6421913 : Blo 259821 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B393467 : Blo 259821 393467 := bstep (se 1 (by rfl) ⟨295100, by rfl⟩ : syracuseStep 393467 = 590201) B590201
theorem B263407 : Blo 259821 263407 := bstep (se 1 (by rfl) ⟨197555, by rfl⟩ : syracuseStep 263407 = 395111) B395111
theorem B263783 : Blo 259821 263783 := bstep (se 1 (by rfl) ⟨197837, by rfl⟩ : syracuseStep 263783 = 395675) B395675
theorem B592199 : Blo 259821 592199 := bstep (se 1 (by rfl) ⟨444149, by rfl⟩ : syracuseStep 592199 = 888299) B888299
theorem B38738513 : Blo 259821 38738513 := bstep (se 2 (by rfl) ⟨14526942, by rfl⟩ : syracuseStep 38738513 = 29053885) B29053885
theorem B1256255 : Blo 259821 1256255 := bstep (se 1 (by rfl) ⟨942191, by rfl⟩ : syracuseStep 1256255 = 1884383) B1884383
theorem B994751 : Blo 259821 994751 := bstep (se 1 (by rfl) ⟨746063, by rfl⟩ : syracuseStep 994751 = 1492127) B1492127
theorem B6338371 : Blo 259821 6338371 := bstep (se 1 (by rfl) ⟨4753778, by rfl⟩ : syracuseStep 6338371 = 9507557) B9507557
theorem B998639 : Blo 259821 998639 := bstep (se 1 (by rfl) ⟨748979, by rfl⟩ : syracuseStep 998639 = 1497959) B1497959
theorem B155143183 : Blo 259821 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B1330667 : Blo 259821 1330667 := bstep (se 1 (by rfl) ⟨998000, by rfl⟩ : syracuseStep 1330667 = 1996001) B1996001
theorem B4281275 : Blo 259821 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B3364973 : Blo 259821 3364973 := bstep (se 3 (by rfl) ⟨630932, by rfl⟩ : syracuseStep 3364973 = 1261865) B1261865
theorem B844415 : Blo 259821 844415 := bstep (se 1 (by rfl) ⟨633311, by rfl⟩ : syracuseStep 844415 = 1266623) B1266623
theorem B3566209 : Blo 259821 3566209 := bstep (se 2 (by rfl) ⟨1337328, by rfl⟩ : syracuseStep 3566209 = 2674657) B2674657
theorem B944959 : Blo 259821 944959 := bstep (se 1 (by rfl) ⟨708719, by rfl⟩ : syracuseStep 944959 = 1417439) B1417439
theorem B4811879 : Blo 259821 4811879 := bstep (se 1 (by rfl) ⟨3608909, by rfl⟩ : syracuseStep 4811879 = 7217819) B7217819
theorem B390503 : Blo 259821 390503 := bstep (se 1 (by rfl) ⟨292877, by rfl⟩ : syracuseStep 390503 = 585755) B585755
theorem B2980151 : Blo 259821 2980151 := bstep (se 1 (by rfl) ⟨2235113, by rfl⟩ : syracuseStep 2980151 = 4470227) B4470227
theorem B262311 : Blo 259821 262311 := bstep (se 1 (by rfl) ⟨196733, by rfl⟩ : syracuseStep 262311 = 393467) B393467
theorem B394799 : Blo 259821 394799 := bstep (se 1 (by rfl) ⟨296099, by rfl⟩ : syracuseStep 394799 = 592199) B592199
theorem B887111 : Blo 259821 887111 := bstep (se 1 (by rfl) ⟨665333, by rfl⟩ : syracuseStep 887111 = 1330667) B1330667
theorem B4754945 : Blo 259821 4754945 := bstep (se 2 (by rfl) ⟨1783104, by rfl⟩ : syracuseStep 4754945 = 3566209) B3566209
theorem B25825675 : Blo 259821 25825675 := bstep (se 1 (by rfl) ⟨19369256, by rfl⟩ : syracuseStep 25825675 = 38738513) B38738513
theorem B562943 : Blo 259821 562943 := bstep (se 1 (by rfl) ⟨422207, by rfl⟩ : syracuseStep 562943 = 844415) B844415
theorem B663167 : Blo 259821 663167 := bstep (se 1 (by rfl) ⟨497375, by rfl⟩ : syracuseStep 663167 = 994751) B994751
theorem B665759 : Blo 259821 665759 := bstep (se 1 (by rfl) ⟨499319, by rfl⟩ : syracuseStep 665759 = 998639) B998639
theorem B11416733 : Blo 259821 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B1259945 : Blo 259821 1259945 := bstep (se 2 (by rfl) ⟨472479, by rfl⟩ : syracuseStep 1259945 = 944959) B944959
theorem B2243315 : Blo 259821 2243315 := bstep (se 1 (by rfl) ⟨1682486, by rfl⟩ : syracuseStep 2243315 = 3364973) B3364973
theorem B837503 : Blo 259821 837503 := bstep (se 1 (by rfl) ⟨628127, by rfl⟩ : syracuseStep 837503 = 1256255) B1256255
theorem B1986767 : Blo 259821 1986767 := bstep (se 1 (by rfl) ⟨1490075, by rfl⟩ : syracuseStep 1986767 = 2980151) B2980151
theorem B206857577 : Blo 259821 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B3207919 : Blo 259821 3207919 := bstep (se 1 (by rfl) ⟨2405939, by rfl⟩ : syracuseStep 3207919 = 4811879) B4811879
theorem B8451161 : Blo 259821 8451161 := bstep (se 2 (by rfl) ⟨3169185, by rfl⟩ : syracuseStep 8451161 = 6338371) B6338371
theorem B260335 : Blo 259821 260335 := bstep (se 1 (by rfl) ⟨195251, by rfl⟩ : syracuseStep 260335 = 390503) B390503
theorem B263199 : Blo 259821 263199 := bstep (se 1 (by rfl) ⟨197399, by rfl⟩ : syracuseStep 263199 = 394799) B394799
theorem B558335 : Blo 259821 558335 := bstep (se 1 (by rfl) ⟨418751, by rfl⟩ : syracuseStep 558335 = 837503) B837503
theorem B591407 : Blo 259821 591407 := bstep (se 1 (by rfl) ⟨443555, by rfl⟩ : syracuseStep 591407 = 887111) B887111
theorem B7611155 : Blo 259821 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B1324511 : Blo 259821 1324511 := bstep (se 1 (by rfl) ⟨993383, by rfl⟩ : syracuseStep 1324511 = 1986767) B1986767
theorem B375295 : Blo 259821 375295 := bstep (se 1 (by rfl) ⟨281471, by rfl⟩ : syracuseStep 375295 = 562943) B562943
theorem B442111 : Blo 259821 442111 := bstep (se 1 (by rfl) ⟨331583, by rfl⟩ : syracuseStep 442111 = 663167) B663167
theorem B137905051 : Blo 259821 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B4277225 : Blo 259821 4277225 := bstep (se 2 (by rfl) ⟨1603959, by rfl⟩ : syracuseStep 4277225 = 3207919) B3207919
theorem B443839 : Blo 259821 443839 := bstep (se 1 (by rfl) ⟨332879, by rfl⟩ : syracuseStep 443839 = 665759) B665759
theorem B839963 : Blo 259821 839963 := bstep (se 1 (by rfl) ⟨629972, by rfl⟩ : syracuseStep 839963 = 1259945) B1259945
theorem B1495543 : Blo 259821 1495543 := bstep (se 1 (by rfl) ⟨1121657, by rfl⟩ : syracuseStep 1495543 = 2243315) B2243315
theorem B3169963 : Blo 259821 3169963 := bstep (se 1 (by rfl) ⟨2377472, by rfl⟩ : syracuseStep 3169963 = 4754945) B4754945
theorem B34434233 : Blo 259821 34434233 := bstep (se 2 (by rfl) ⟨12912837, by rfl⟩ : syracuseStep 34434233 = 25825675) B25825675
theorem B5634107 : Blo 259821 5634107 := bstep (se 1 (by rfl) ⟨4225580, by rfl⟩ : syracuseStep 5634107 = 8451161) B8451161
theorem B2851483 : Blo 259821 2851483 := bstep (se 1 (by rfl) ⟨2138612, by rfl⟩ : syracuseStep 2851483 = 4277225) B4277225
theorem B394271 : Blo 259821 394271 := bstep (se 1 (by rfl) ⟨295703, by rfl⟩ : syracuseStep 394271 = 591407) B591407
theorem B591785 : Blo 259821 591785 := bstep (se 2 (by rfl) ⟨221919, by rfl⟩ : syracuseStep 591785 = 443839) B443839
theorem B559975 : Blo 259821 559975 := bstep (se 1 (by rfl) ⟨419981, by rfl⟩ : syracuseStep 559975 = 839963) B839963
theorem B500393 : Blo 259821 500393 := bstep (se 2 (by rfl) ⟨187647, by rfl⟩ : syracuseStep 500393 = 375295) B375295
theorem B372223 : Blo 259821 372223 := bstep (se 1 (by rfl) ⟨279167, by rfl⟩ : syracuseStep 372223 = 558335) B558335
theorem B183873401 : Blo 259821 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B22956155 : Blo 259821 22956155 := bstep (se 1 (by rfl) ⟨17217116, by rfl⟩ : syracuseStep 22956155 = 34434233) B34434233
theorem B3756071 : Blo 259821 3756071 := bstep (se 1 (by rfl) ⟨2817053, by rfl⟩ : syracuseStep 3756071 = 5634107) B5634107
theorem B5074103 : Blo 259821 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B1994057 : Blo 259821 1994057 := bstep (se 2 (by rfl) ⟨747771, by rfl⟩ : syracuseStep 1994057 = 1495543) B1495543
theorem B883007 : Blo 259821 883007 := bstep (se 1 (by rfl) ⟨662255, by rfl⟩ : syracuseStep 883007 = 1324511) B1324511
theorem B4226617 : Blo 259821 4226617 := bstep (se 2 (by rfl) ⟨1584981, by rfl⟩ : syracuseStep 4226617 = 3169963) B3169963
theorem B589481 : Blo 259821 589481 := bstep (se 2 (by rfl) ⟨221055, by rfl⟩ : syracuseStep 589481 = 442111) B442111
theorem B262847 : Blo 259821 262847 := bstep (se 1 (by rfl) ⟨197135, by rfl⟩ : syracuseStep 262847 = 394271) B394271
theorem B3801977 : Blo 259821 3801977 := bstep (se 2 (by rfl) ⟨1425741, by rfl⟩ : syracuseStep 3801977 = 2851483) B2851483
theorem B394523 : Blo 259821 394523 := bstep (se 1 (by rfl) ⟨295892, by rfl⟩ : syracuseStep 394523 = 591785) B591785
theorem B15304103 : Blo 259821 15304103 := bstep (se 1 (by rfl) ⟨11478077, by rfl⟩ : syracuseStep 15304103 = 22956155) B22956155
theorem B496297 : Blo 259821 496297 := bstep (se 2 (by rfl) ⟨186111, by rfl⟩ : syracuseStep 496297 = 372223) B372223
theorem B333595 : Blo 259821 333595 := bstep (se 1 (by rfl) ⟨250196, by rfl⟩ : syracuseStep 333595 = 500393) B500393
theorem B3382735 : Blo 259821 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B2504047 : Blo 259821 2504047 := bstep (se 1 (by rfl) ⟨1878035, by rfl⟩ : syracuseStep 2504047 = 3756071) B3756071
theorem B1329371 : Blo 259821 1329371 := bstep (se 1 (by rfl) ⟨997028, by rfl⟩ : syracuseStep 1329371 = 1994057) B1994057
theorem B746633 : Blo 259821 746633 := bstep (se 2 (by rfl) ⟨279987, by rfl⟩ : syracuseStep 746633 = 559975) B559975
theorem B122582267 : Blo 259821 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B588671 : Blo 259821 588671 := bstep (se 1 (by rfl) ⟨441503, by rfl⟩ : syracuseStep 588671 = 883007) B883007
theorem B5635489 : Blo 259821 5635489 := bstep (se 2 (by rfl) ⟨2113308, by rfl⟩ : syracuseStep 5635489 = 4226617) B4226617
theorem B392987 : Blo 259821 392987 := bstep (se 1 (by rfl) ⟨294740, by rfl⟩ : syracuseStep 392987 = 589481) B589481
theorem B263015 : Blo 259821 263015 := bstep (se 1 (by rfl) ⟨197261, by rfl⟩ : syracuseStep 263015 = 394523) B394523
theorem B886247 : Blo 259821 886247 := bstep (se 1 (by rfl) ⟨664685, by rfl⟩ : syracuseStep 886247 = 1329371) B1329371
theorem B497755 : Blo 259821 497755 := bstep (se 1 (by rfl) ⟨373316, by rfl⟩ : syracuseStep 497755 = 746633) B746633
theorem B661729 : Blo 259821 661729 := bstep (se 2 (by rfl) ⟨248148, by rfl⟩ : syracuseStep 661729 = 496297) B496297
theorem B7513985 : Blo 259821 7513985 := bstep (se 2 (by rfl) ⟨2817744, by rfl⟩ : syracuseStep 7513985 = 5635489) B5635489
theorem B2534651 : Blo 259821 2534651 := bstep (se 1 (by rfl) ⟨1900988, by rfl⟩ : syracuseStep 2534651 = 3801977) B3801977
theorem B10202735 : Blo 259821 10202735 := bstep (se 1 (by rfl) ⟨7652051, by rfl⟩ : syracuseStep 10202735 = 15304103) B15304103
theorem B444793 : Blo 259821 444793 := bstep (se 2 (by rfl) ⟨166797, by rfl⟩ : syracuseStep 444793 = 333595) B333595
theorem B4510313 : Blo 259821 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B3338729 : Blo 259821 3338729 := bstep (se 2 (by rfl) ⟨1252023, by rfl⟩ : syracuseStep 3338729 = 2504047) B2504047
theorem B81721511 : Blo 259821 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B392447 : Blo 259821 392447 := bstep (se 1 (by rfl) ⟨294335, by rfl⟩ : syracuseStep 392447 = 588671) B588671
theorem B261991 : Blo 259821 261991 := bstep (se 1 (by rfl) ⟨196493, by rfl⟩ : syracuseStep 261991 = 392987) B392987
theorem B590831 : Blo 259821 590831 := bstep (se 1 (by rfl) ⟨443123, by rfl⟩ : syracuseStep 590831 = 886247) B886247
theorem B593057 : Blo 259821 593057 := bstep (se 2 (by rfl) ⟨222396, by rfl⟩ : syracuseStep 593057 = 444793) B444793
theorem B663673 : Blo 259821 663673 := bstep (se 2 (by rfl) ⟨248877, by rfl⟩ : syracuseStep 663673 = 497755) B497755
theorem B1689767 : Blo 259821 1689767 := bstep (se 1 (by rfl) ⟨1267325, by rfl⟩ : syracuseStep 1689767 = 2534651) B2534651
theorem B6801823 : Blo 259821 6801823 := bstep (se 1 (by rfl) ⟨5101367, by rfl⟩ : syracuseStep 6801823 = 10202735) B10202735
theorem B54481007 : Blo 259821 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B3006875 : Blo 259821 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B5009323 : Blo 259821 5009323 := bstep (se 1 (by rfl) ⟨3756992, by rfl⟩ : syracuseStep 5009323 = 7513985) B7513985
theorem B882305 : Blo 259821 882305 := bstep (se 2 (by rfl) ⟨330864, by rfl⟩ : syracuseStep 882305 = 661729) B661729
theorem B2225819 : Blo 259821 2225819 := bstep (se 1 (by rfl) ⟨1669364, by rfl⟩ : syracuseStep 2225819 = 3338729) B3338729
theorem B261631 : Blo 259821 261631 := bstep (se 1 (by rfl) ⟨196223, by rfl⟩ : syracuseStep 261631 = 392447) B392447
theorem B884897 : Blo 259821 884897 := bstep (se 2 (by rfl) ⟨331836, by rfl⟩ : syracuseStep 884897 = 663673) B663673
theorem B393887 : Blo 259821 393887 := bstep (se 1 (by rfl) ⟨295415, by rfl⟩ : syracuseStep 393887 = 590831) B590831
theorem B395371 : Blo 259821 395371 := bstep (se 1 (by rfl) ⟨296528, by rfl⟩ : syracuseStep 395371 = 593057) B593057
theorem B2004583 : Blo 259821 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B1483879 : Blo 259821 1483879 := bstep (se 1 (by rfl) ⟨1112909, by rfl⟩ : syracuseStep 1483879 = 2225819) B2225819
theorem B1126511 : Blo 259821 1126511 := bstep (se 1 (by rfl) ⟨844883, by rfl⟩ : syracuseStep 1126511 = 1689767) B1689767
theorem B36320671 : Blo 259821 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B9069097 : Blo 259821 9069097 := bstep (se 2 (by rfl) ⟨3400911, by rfl⟩ : syracuseStep 9069097 = 6801823) B6801823
theorem B6679097 : Blo 259821 6679097 := bstep (se 2 (by rfl) ⟨2504661, by rfl⟩ : syracuseStep 6679097 = 5009323) B5009323
theorem B588203 : Blo 259821 588203 := bstep (se 1 (by rfl) ⟨441152, by rfl⟩ : syracuseStep 588203 = 882305) B882305
theorem B589931 : Blo 259821 589931 := bstep (se 1 (by rfl) ⟨442448, by rfl⟩ : syracuseStep 589931 = 884897) B884897
theorem B262591 : Blo 259821 262591 := bstep (se 1 (by rfl) ⟨196943, by rfl⟩ : syracuseStep 262591 = 393887) B393887
theorem B12092129 : Blo 259821 12092129 := bstep (se 2 (by rfl) ⟨4534548, by rfl⟩ : syracuseStep 12092129 = 9069097) B9069097
theorem B527161 : Blo 259821 527161 := bstep (se 2 (by rfl) ⟨197685, by rfl⟩ : syracuseStep 527161 = 395371) B395371
theorem B1978505 : Blo 259821 1978505 := bstep (se 2 (by rfl) ⟨741939, by rfl⟩ : syracuseStep 1978505 = 1483879) B1483879
theorem B2672777 : Blo 259821 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B4452731 : Blo 259821 4452731 := bstep (se 1 (by rfl) ⟨3339548, by rfl⟩ : syracuseStep 4452731 = 6679097) B6679097
theorem B48427561 : Blo 259821 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B751007 : Blo 259821 751007 := bstep (se 1 (by rfl) ⟨563255, by rfl⟩ : syracuseStep 751007 = 1126511) B1126511
theorem B392135 : Blo 259821 392135 := bstep (se 1 (by rfl) ⟨294101, by rfl⟩ : syracuseStep 392135 = 588203) B588203
theorem B393287 : Blo 259821 393287 := bstep (se 1 (by rfl) ⟨294965, by rfl⟩ : syracuseStep 393287 = 589931) B589931
theorem B8061419 : Blo 259821 8061419 := bstep (se 1 (by rfl) ⟨6046064, by rfl⟩ : syracuseStep 8061419 = 12092129) B12092129
theorem B258280325 : Blo 259821 258280325 := bstep (se 4 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 258280325 = 48427561) B48427561
theorem B1319003 : Blo 259821 1319003 := bstep (se 1 (by rfl) ⟨989252, by rfl⟩ : syracuseStep 1319003 = 1978505) B1978505
theorem B500671 : Blo 259821 500671 := bstep (se 1 (by rfl) ⟨375503, by rfl⟩ : syracuseStep 500671 = 751007) B751007
theorem B1781851 : Blo 259821 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B702881 : Blo 259821 702881 := bstep (se 2 (by rfl) ⟨263580, by rfl⟩ : syracuseStep 702881 = 527161) B527161
theorem B2968487 : Blo 259821 2968487 := bstep (se 1 (by rfl) ⟨2226365, by rfl⟩ : syracuseStep 2968487 = 4452731) B4452731
theorem B261423 : Blo 259821 261423 := bstep (se 1 (by rfl) ⟨196067, by rfl⟩ : syracuseStep 261423 = 392135) B392135
theorem B262191 : Blo 259821 262191 := bstep (se 1 (by rfl) ⟨196643, by rfl⟩ : syracuseStep 262191 = 393287) B393287
theorem B5374279 : Blo 259821 5374279 := bstep (se 1 (by rfl) ⟨4030709, by rfl⟩ : syracuseStep 5374279 = 8061419) B8061419
theorem B468587 : Blo 259821 468587 := bstep (se 1 (by rfl) ⟨351440, by rfl⟩ : syracuseStep 468587 = 702881) B702881
theorem B667561 : Blo 259821 667561 := bstep (se 2 (by rfl) ⟨250335, by rfl⟩ : syracuseStep 667561 = 500671) B500671
theorem B1978991 : Blo 259821 1978991 := bstep (se 1 (by rfl) ⟨1484243, by rfl⟩ : syracuseStep 1978991 = 2968487) B2968487
theorem B2375801 : Blo 259821 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B172186883 : Blo 259821 172186883 := bstep (se 1 (by rfl) ⟨129140162, by rfl⟩ : syracuseStep 172186883 = 258280325) B258280325
theorem B879335 : Blo 259821 879335 := bstep (se 1 (by rfl) ⟨659501, by rfl⟩ : syracuseStep 879335 = 1319003) B1319003
theorem B114791255 : Blo 259821 114791255 := bstep (se 1 (by rfl) ⟨86093441, by rfl⟩ : syracuseStep 114791255 = 172186883) B172186883
theorem B890081 : Blo 259821 890081 := bstep (se 2 (by rfl) ⟨333780, by rfl⟩ : syracuseStep 890081 = 667561) B667561
theorem B1319327 : Blo 259821 1319327 := bstep (se 1 (by rfl) ⟨989495, by rfl⟩ : syracuseStep 1319327 = 1978991) B1978991
theorem B1583867 : Blo 259821 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B312391 : Blo 259821 312391 := bstep (se 1 (by rfl) ⟨234293, by rfl⟩ : syracuseStep 312391 = 468587) B468587
theorem B7165705 : Blo 259821 7165705 := bstep (se 2 (by rfl) ⟨2687139, by rfl⟩ : syracuseStep 7165705 = 5374279) B5374279
theorem B586223 : Blo 259821 586223 := bstep (se 1 (by rfl) ⟨439667, by rfl⟩ : syracuseStep 586223 = 879335) B879335
theorem B593387 : Blo 259821 593387 := bstep (se 1 (by rfl) ⟨445040, by rfl⟩ : syracuseStep 593387 = 890081) B890081
theorem B1055911 : Blo 259821 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B76527503 : Blo 259821 76527503 := bstep (se 1 (by rfl) ⟨57395627, by rfl⟩ : syracuseStep 76527503 = 114791255) B114791255
theorem B9554273 : Blo 259821 9554273 := bstep (se 2 (by rfl) ⟨3582852, by rfl⟩ : syracuseStep 9554273 = 7165705) B7165705
theorem B416521 : Blo 259821 416521 := bstep (se 2 (by rfl) ⟨156195, by rfl⟩ : syracuseStep 416521 = 312391) B312391
theorem B879551 : Blo 259821 879551 := bstep (se 1 (by rfl) ⟨659663, by rfl⟩ : syracuseStep 879551 = 1319327) B1319327
theorem B390815 : Blo 259821 390815 := bstep (se 1 (by rfl) ⟨293111, by rfl⟩ : syracuseStep 390815 = 586223) B586223
theorem B395591 : Blo 259821 395591 := bstep (se 1 (by rfl) ⟨296693, by rfl⟩ : syracuseStep 395591 = 593387) B593387
theorem B6369515 : Blo 259821 6369515 := bstep (se 1 (by rfl) ⟨4777136, by rfl⟩ : syracuseStep 6369515 = 9554273) B9554273
theorem B2221445 : Blo 259821 2221445 := bstep (se 4 (by rfl) ⟨208260, by rfl⟩ : syracuseStep 2221445 = 416521) B416521
theorem B586367 : Blo 259821 586367 := bstep (se 1 (by rfl) ⟨439775, by rfl⟩ : syracuseStep 586367 = 879551) B879551
theorem B260543 : Blo 259821 260543 := bstep (se 1 (by rfl) ⟨195407, by rfl⟩ : syracuseStep 260543 = 390815) B390815
theorem B51018335 : Blo 259821 51018335 := bstep (se 1 (by rfl) ⟨38263751, by rfl⟩ : syracuseStep 51018335 = 76527503) B76527503
theorem B1407881 : Blo 259821 1407881 := bstep (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) B1055911
theorem B263727 : Blo 259821 263727 := bstep (se 1 (by rfl) ⟨197795, by rfl⟩ : syracuseStep 263727 = 395591) B395591
theorem B1480963 : Blo 259821 1480963 := bstep (se 1 (by rfl) ⟨1110722, by rfl⟩ : syracuseStep 1480963 = 2221445) B2221445
theorem B3754349 : Blo 259821 3754349 := bstep (se 3 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 3754349 = 1407881) B1407881
theorem B4246343 : Blo 259821 4246343 := bstep (se 1 (by rfl) ⟨3184757, by rfl⟩ : syracuseStep 4246343 = 6369515) B6369515
theorem B390911 : Blo 259821 390911 := bstep (se 1 (by rfl) ⟨293183, by rfl⟩ : syracuseStep 390911 = 586367) B586367
theorem B34012223 : Blo 259821 34012223 := bstep (se 1 (by rfl) ⟨25509167, by rfl⟩ : syracuseStep 34012223 = 51018335) B51018335
theorem B1974617 : Blo 259821 1974617 := bstep (se 2 (by rfl) ⟨740481, by rfl⟩ : syracuseStep 1974617 = 1480963) B1480963
theorem B2502899 : Blo 259821 2502899 := bstep (se 1 (by rfl) ⟨1877174, by rfl⟩ : syracuseStep 2502899 = 3754349) B3754349
theorem B2830895 : Blo 259821 2830895 := bstep (se 1 (by rfl) ⟨2123171, by rfl⟩ : syracuseStep 2830895 = 4246343) B4246343
theorem B260607 : Blo 259821 260607 := bstep (se 1 (by rfl) ⟨195455, by rfl⟩ : syracuseStep 260607 = 390911) B390911
theorem B22674815 : Blo 259821 22674815 := bstep (se 1 (by rfl) ⟨17006111, by rfl⟩ : syracuseStep 22674815 = 34012223) B34012223
theorem B1316411 : Blo 259821 1316411 := bstep (se 1 (by rfl) ⟨987308, by rfl⟩ : syracuseStep 1316411 = 1974617) B1974617
theorem B15116543 : Blo 259821 15116543 := bstep (se 1 (by rfl) ⟨11337407, by rfl⟩ : syracuseStep 15116543 = 22674815) B22674815
theorem B1887263 : Blo 259821 1887263 := bstep (se 1 (by rfl) ⟨1415447, by rfl⟩ : syracuseStep 1887263 = 2830895) B2830895
theorem B1668599 : Blo 259821 1668599 := bstep (se 1 (by rfl) ⟨1251449, by rfl⟩ : syracuseStep 1668599 = 2502899) B2502899
theorem B1258175 : Blo 259821 1258175 := bstep (se 1 (by rfl) ⟨943631, by rfl⟩ : syracuseStep 1258175 = 1887263) B1887263
theorem B10077695 : Blo 259821 10077695 := bstep (se 1 (by rfl) ⟨7558271, by rfl⟩ : syracuseStep 10077695 = 15116543) B15116543
theorem B877607 : Blo 259821 877607 := bstep (se 1 (by rfl) ⟨658205, by rfl⟩ : syracuseStep 877607 = 1316411) B1316411
theorem B1112399 : Blo 259821 1112399 := bstep (se 1 (by rfl) ⟨834299, by rfl⟩ : syracuseStep 1112399 = 1668599) B1668599
theorem B6718463 : Blo 259821 6718463 := bstep (se 1 (by rfl) ⟨5038847, by rfl⟩ : syracuseStep 6718463 = 10077695) B10077695
theorem B838783 : Blo 259821 838783 := bstep (se 1 (by rfl) ⟨629087, by rfl⟩ : syracuseStep 838783 = 1258175) B1258175
theorem B741599 : Blo 259821 741599 := bstep (se 1 (by rfl) ⟨556199, by rfl⟩ : syracuseStep 741599 = 1112399) B1112399
theorem B585071 : Blo 259821 585071 := bstep (se 1 (by rfl) ⟨438803, by rfl⟩ : syracuseStep 585071 = 877607) B877607
theorem B494399 : Blo 259821 494399 := bstep (se 1 (by rfl) ⟨370799, by rfl⟩ : syracuseStep 494399 = 741599) B741599
theorem B1118377 : Blo 259821 1118377 := bstep (se 2 (by rfl) ⟨419391, by rfl⟩ : syracuseStep 1118377 = 838783) B838783
theorem B4478975 : Blo 259821 4478975 := bstep (se 1 (by rfl) ⟨3359231, by rfl⟩ : syracuseStep 4478975 = 6718463) B6718463
theorem B390047 : Blo 259821 390047 := bstep (se 1 (by rfl) ⟨292535, by rfl⟩ : syracuseStep 390047 = 585071) B585071
theorem B329599 : Blo 259821 329599 := bstep (se 1 (by rfl) ⟨247199, by rfl⟩ : syracuseStep 329599 = 494399) B494399
theorem B2985983 : Blo 259821 2985983 := bstep (se 1 (by rfl) ⟨2239487, by rfl⟩ : syracuseStep 2985983 = 4478975) B4478975
theorem B1491169 : Blo 259821 1491169 := bstep (se 2 (by rfl) ⟨559188, by rfl⟩ : syracuseStep 1491169 = 1118377) B1118377
theorem B260031 : Blo 259821 260031 := bstep (se 1 (by rfl) ⟨195023, by rfl⟩ : syracuseStep 260031 = 390047) B390047
theorem B439465 : Blo 259821 439465 := bstep (se 2 (by rfl) ⟨164799, by rfl⟩ : syracuseStep 439465 = 329599) B329599
theorem B1988225 : Blo 259821 1988225 := bstep (se 2 (by rfl) ⟨745584, by rfl⟩ : syracuseStep 1988225 = 1491169) B1491169
theorem B1990655 : Blo 259821 1990655 := bstep (se 1 (by rfl) ⟨1492991, by rfl⟩ : syracuseStep 1990655 = 2985983) B2985983
theorem B1325483 : Blo 259821 1325483 := bstep (se 1 (by rfl) ⟨994112, by rfl⟩ : syracuseStep 1325483 = 1988225) B1988225
theorem B1327103 : Blo 259821 1327103 := bstep (se 1 (by rfl) ⟨995327, by rfl⟩ : syracuseStep 1327103 = 1990655) B1990655
theorem B585953 : Blo 259821 585953 := bstep (se 2 (by rfl) ⟨219732, by rfl⟩ : syracuseStep 585953 = 439465) B439465
theorem B884735 : Blo 259821 884735 := bstep (se 1 (by rfl) ⟨663551, by rfl⟩ : syracuseStep 884735 = 1327103) B1327103
theorem B390635 : Blo 259821 390635 := bstep (se 1 (by rfl) ⟨292976, by rfl⟩ : syracuseStep 390635 = 585953) B585953
theorem B883655 : Blo 259821 883655 := bstep (se 1 (by rfl) ⟨662741, by rfl⟩ : syracuseStep 883655 = 1325483) B1325483
theorem B260423 : Blo 259821 260423 := bstep (se 1 (by rfl) ⟨195317, by rfl⟩ : syracuseStep 260423 = 390635) B390635
theorem B589103 : Blo 259821 589103 := bstep (se 1 (by rfl) ⟨441827, by rfl⟩ : syracuseStep 589103 = 883655) B883655
theorem B589823 : Blo 259821 589823 := bstep (se 1 (by rfl) ⟨442367, by rfl⟩ : syracuseStep 589823 = 884735) B884735
theorem B393215 : Blo 259821 393215 := bstep (se 1 (by rfl) ⟨294911, by rfl⟩ : syracuseStep 393215 = 589823) B589823
theorem B392735 : Blo 259821 392735 := bstep (se 1 (by rfl) ⟨294551, by rfl⟩ : syracuseStep 392735 = 589103) B589103
theorem B262143 : Blo 259821 262143 := bstep (se 1 (by rfl) ⟨196607, by rfl⟩ : syracuseStep 262143 = 393215) B393215
theorem B261823 : Blo 259821 261823 := bstep (se 1 (by rfl) ⟨196367, by rfl⟩ : syracuseStep 261823 = 392735) B392735

theorem C0 (j : ℕ) (h1 : 64955 ≤ j) (h2 : j ≤ 65654) : Blo 259821 (4 * j + 3) := by
  interval_cases j
  · exact B259823
  · exact B259827
  · exact B259831
  · exact B259835
  · exact B259839
  · exact B259843
  · exact B259847
  · exact B259851
  · exact B259855
  · exact B259859
  · exact B259863
  · exact B259867
  · exact B259871
  · exact B259875
  · exact B259879
  · exact B259883
  · exact B259887
  · exact B259891
  · exact B259895
  · exact B259899
  · exact B259903
  · exact B259907
  · exact B259911
  · exact B259915
  · exact B259919
  · exact B259923
  · exact B259927
  · exact B259931
  · exact B259935
  · exact B259939
  · exact B259943
  · exact B259947
  · exact B259951
  · exact B259955
  · exact B259959
  · exact B259963
  · exact B259967
  · exact B259971
  · exact B259975
  · exact B259979
  · exact B259983
  · exact B259987
  · exact B259991
  · exact B259995
  · exact B259999
  · exact B260003
  · exact B260007
  · exact B260011
  · exact B260015
  · exact B260019
  · exact B260023
  · exact B260027
  · exact B260031
  · exact B260035
  · exact B260039
  · exact B260043
  · exact B260047
  · exact B260051
  · exact B260055
  · exact B260059
  · exact B260063
  · exact B260067
  · exact B260071
  · exact B260075
  · exact B260079
  · exact B260083
  · exact B260087
  · exact B260091
  · exact B260095
  · exact B260099
  · exact B260103
  · exact B260107
  · exact B260111
  · exact B260115
  · exact B260119
  · exact B260123
  · exact B260127
  · exact B260131
  · exact B260135
  · exact B260139
  · exact B260143
  · exact B260147
  · exact B260151
  · exact B260155
  · exact B260159
  · exact B260163
  · exact B260167
  · exact B260171
  · exact B260175
  · exact B260179
  · exact B260183
  · exact B260187
  · exact B260191
  · exact B260195
  · exact B260199
  · exact B260203
  · exact B260207
  · exact B260211
  · exact B260215
  · exact B260219
  · exact B260223
  · exact B260227
  · exact B260231
  · exact B260235
  · exact B260239
  · exact B260243
  · exact B260247
  · exact B260251
  · exact B260255
  · exact B260259
  · exact B260263
  · exact B260267
  · exact B260271
  · exact B260275
  · exact B260279
  · exact B260283
  · exact B260287
  · exact B260291
  · exact B260295
  · exact B260299
  · exact B260303
  · exact B260307
  · exact B260311
  · exact B260315
  · exact B260319
  · exact B260323
  · exact B260327
  · exact B260331
  · exact B260335
  · exact B260339
  · exact B260343
  · exact B260347
  · exact B260351
  · exact B260355
  · exact B260359
  · exact B260363
  · exact B260367
  · exact B260371
  · exact B260375
  · exact B260379
  · exact B260383
  · exact B260387
  · exact B260391
  · exact B260395
  · exact B260399
  · exact B260403
  · exact B260407
  · exact B260411
  · exact B260415
  · exact B260419
  · exact B260423
  · exact B260427
  · exact B260431
  · exact B260435
  · exact B260439
  · exact B260443
  · exact B260447
  · exact B260451
  · exact B260455
  · exact B260459
  · exact B260463
  · exact B260467
  · exact B260471
  · exact B260475
  · exact B260479
  · exact B260483
  · exact B260487
  · exact B260491
  · exact B260495
  · exact B260499
  · exact B260503
  · exact B260507
  · exact B260511
  · exact B260515
  · exact B260519
  · exact B260523
  · exact B260527
  · exact B260531
  · exact B260535
  · exact B260539
  · exact B260543
  · exact B260547
  · exact B260551
  · exact B260555
  · exact B260559
  · exact B260563
  · exact B260567
  · exact B260571
  · exact B260575
  · exact B260579
  · exact B260583
  · exact B260587
  · exact B260591
  · exact B260595
  · exact B260599
  · exact B260603
  · exact B260607
  · exact B260611
  · exact B260615
  · exact B260619
  · exact B260623
  · exact B260627
  · exact B260631
  · exact B260635
  · exact B260639
  · exact B260643
  · exact B260647
  · exact B260651
  · exact B260655
  · exact B260659
  · exact B260663
  · exact B260667
  · exact B260671
  · exact B260675
  · exact B260679
  · exact B260683
  · exact B260687
  · exact B260691
  · exact B260695
  · exact B260699
  · exact B260703
  · exact B260707
  · exact B260711
  · exact B260715
  · exact B260719
  · exact B260723
  · exact B260727
  · exact B260731
  · exact B260735
  · exact B260739
  · exact B260743
  · exact B260747
  · exact B260751
  · exact B260755
  · exact B260759
  · exact B260763
  · exact B260767
  · exact B260771
  · exact B260775
  · exact B260779
  · exact B260783
  · exact B260787
  · exact B260791
  · exact B260795
  · exact B260799
  · exact B260803
  · exact B260807
  · exact B260811
  · exact B260815
  · exact B260819
  · exact B260823
  · exact B260827
  · exact B260831
  · exact B260835
  · exact B260839
  · exact B260843
  · exact B260847
  · exact B260851
  · exact B260855
  · exact B260859
  · exact B260863
  · exact B260867
  · exact B260871
  · exact B260875
  · exact B260879
  · exact B260883
  · exact B260887
  · exact B260891
  · exact B260895
  · exact B260899
  · exact B260903
  · exact B260907
  · exact B260911
  · exact B260915
  · exact B260919
  · exact B260923
  · exact B260927
  · exact B260931
  · exact B260935
  · exact B260939
  · exact B260943
  · exact B260947
  · exact B260951
  · exact B260955
  · exact B260959
  · exact B260963
  · exact B260967
  · exact B260971
  · exact B260975
  · exact B260979
  · exact B260983
  · exact B260987
  · exact B260991
  · exact B260995
  · exact B260999
  · exact B261003
  · exact B261007
  · exact B261011
  · exact B261015
  · exact B261019
  · exact B261023
  · exact B261027
  · exact B261031
  · exact B261035
  · exact B261039
  · exact B261043
  · exact B261047
  · exact B261051
  · exact B261055
  · exact B261059
  · exact B261063
  · exact B261067
  · exact B261071
  · exact B261075
  · exact B261079
  · exact B261083
  · exact B261087
  · exact B261091
  · exact B261095
  · exact B261099
  · exact B261103
  · exact B261107
  · exact B261111
  · exact B261115
  · exact B261119
  · exact B261123
  · exact B261127
  · exact B261131
  · exact B261135
  · exact B261139
  · exact B261143
  · exact B261147
  · exact B261151
  · exact B261155
  · exact B261159
  · exact B261163
  · exact B261167
  · exact B261171
  · exact B261175
  · exact B261179
  · exact B261183
  · exact B261187
  · exact B261191
  · exact B261195
  · exact B261199
  · exact B261203
  · exact B261207
  · exact B261211
  · exact B261215
  · exact B261219
  · exact B261223
  · exact B261227
  · exact B261231
  · exact B261235
  · exact B261239
  · exact B261243
  · exact B261247
  · exact B261251
  · exact B261255
  · exact B261259
  · exact B261263
  · exact B261267
  · exact B261271
  · exact B261275
  · exact B261279
  · exact B261283
  · exact B261287
  · exact B261291
  · exact B261295
  · exact B261299
  · exact B261303
  · exact B261307
  · exact B261311
  · exact B261315
  · exact B261319
  · exact B261323
  · exact B261327
  · exact B261331
  · exact B261335
  · exact B261339
  · exact B261343
  · exact B261347
  · exact B261351
  · exact B261355
  · exact B261359
  · exact B261363
  · exact B261367
  · exact B261371
  · exact B261375
  · exact B261379
  · exact B261383
  · exact B261387
  · exact B261391
  · exact B261395
  · exact B261399
  · exact B261403
  · exact B261407
  · exact B261411
  · exact B261415
  · exact B261419
  · exact B261423
  · exact B261427
  · exact B261431
  · exact B261435
  · exact B261439
  · exact B261443
  · exact B261447
  · exact B261451
  · exact B261455
  · exact B261459
  · exact B261463
  · exact B261467
  · exact B261471
  · exact B261475
  · exact B261479
  · exact B261483
  · exact B261487
  · exact B261491
  · exact B261495
  · exact B261499
  · exact B261503
  · exact B261507
  · exact B261511
  · exact B261515
  · exact B261519
  · exact B261523
  · exact B261527
  · exact B261531
  · exact B261535
  · exact B261539
  · exact B261543
  · exact B261547
  · exact B261551
  · exact B261555
  · exact B261559
  · exact B261563
  · exact B261567
  · exact B261571
  · exact B261575
  · exact B261579
  · exact B261583
  · exact B261587
  · exact B261591
  · exact B261595
  · exact B261599
  · exact B261603
  · exact B261607
  · exact B261611
  · exact B261615
  · exact B261619
  · exact B261623
  · exact B261627
  · exact B261631
  · exact B261635
  · exact B261639
  · exact B261643
  · exact B261647
  · exact B261651
  · exact B261655
  · exact B261659
  · exact B261663
  · exact B261667
  · exact B261671
  · exact B261675
  · exact B261679
  · exact B261683
  · exact B261687
  · exact B261691
  · exact B261695
  · exact B261699
  · exact B261703
  · exact B261707
  · exact B261711
  · exact B261715
  · exact B261719
  · exact B261723
  · exact B261727
  · exact B261731
  · exact B261735
  · exact B261739
  · exact B261743
  · exact B261747
  · exact B261751
  · exact B261755
  · exact B261759
  · exact B261763
  · exact B261767
  · exact B261771
  · exact B261775
  · exact B261779
  · exact B261783
  · exact B261787
  · exact B261791
  · exact B261795
  · exact B261799
  · exact B261803
  · exact B261807
  · exact B261811
  · exact B261815
  · exact B261819
  · exact B261823
  · exact B261827
  · exact B261831
  · exact B261835
  · exact B261839
  · exact B261843
  · exact B261847
  · exact B261851
  · exact B261855
  · exact B261859
  · exact B261863
  · exact B261867
  · exact B261871
  · exact B261875
  · exact B261879
  · exact B261883
  · exact B261887
  · exact B261891
  · exact B261895
  · exact B261899
  · exact B261903
  · exact B261907
  · exact B261911
  · exact B261915
  · exact B261919
  · exact B261923
  · exact B261927
  · exact B261931
  · exact B261935
  · exact B261939
  · exact B261943
  · exact B261947
  · exact B261951
  · exact B261955
  · exact B261959
  · exact B261963
  · exact B261967
  · exact B261971
  · exact B261975
  · exact B261979
  · exact B261983
  · exact B261987
  · exact B261991
  · exact B261995
  · exact B261999
  · exact B262003
  · exact B262007
  · exact B262011
  · exact B262015
  · exact B262019
  · exact B262023
  · exact B262027
  · exact B262031
  · exact B262035
  · exact B262039
  · exact B262043
  · exact B262047
  · exact B262051
  · exact B262055
  · exact B262059
  · exact B262063
  · exact B262067
  · exact B262071
  · exact B262075
  · exact B262079
  · exact B262083
  · exact B262087
  · exact B262091
  · exact B262095
  · exact B262099
  · exact B262103
  · exact B262107
  · exact B262111
  · exact B262115
  · exact B262119
  · exact B262123
  · exact B262127
  · exact B262131
  · exact B262135
  · exact B262139
  · exact B262143
  · exact B262147
  · exact B262151
  · exact B262155
  · exact B262159
  · exact B262163
  · exact B262167
  · exact B262171
  · exact B262175
  · exact B262179
  · exact B262183
  · exact B262187
  · exact B262191
  · exact B262195
  · exact B262199
  · exact B262203
  · exact B262207
  · exact B262211
  · exact B262215
  · exact B262219
  · exact B262223
  · exact B262227
  · exact B262231
  · exact B262235
  · exact B262239
  · exact B262243
  · exact B262247
  · exact B262251
  · exact B262255
  · exact B262259
  · exact B262263
  · exact B262267
  · exact B262271
  · exact B262275
  · exact B262279
  · exact B262283
  · exact B262287
  · exact B262291
  · exact B262295
  · exact B262299
  · exact B262303
  · exact B262307
  · exact B262311
  · exact B262315
  · exact B262319
  · exact B262323
  · exact B262327
  · exact B262331
  · exact B262335
  · exact B262339
  · exact B262343
  · exact B262347
  · exact B262351
  · exact B262355
  · exact B262359
  · exact B262363
  · exact B262367
  · exact B262371
  · exact B262375
  · exact B262379
  · exact B262383
  · exact B262387
  · exact B262391
  · exact B262395
  · exact B262399
  · exact B262403
  · exact B262407
  · exact B262411
  · exact B262415
  · exact B262419
  · exact B262423
  · exact B262427
  · exact B262431
  · exact B262435
  · exact B262439
  · exact B262443
  · exact B262447
  · exact B262451
  · exact B262455
  · exact B262459
  · exact B262463
  · exact B262467
  · exact B262471
  · exact B262475
  · exact B262479
  · exact B262483
  · exact B262487
  · exact B262491
  · exact B262495
  · exact B262499
  · exact B262503
  · exact B262507
  · exact B262511
  · exact B262515
  · exact B262519
  · exact B262523
  · exact B262527
  · exact B262531
  · exact B262535
  · exact B262539
  · exact B262543
  · exact B262547
  · exact B262551
  · exact B262555
  · exact B262559
  · exact B262563
  · exact B262567
  · exact B262571
  · exact B262575
  · exact B262579
  · exact B262583
  · exact B262587
  · exact B262591
  · exact B262595
  · exact B262599
  · exact B262603
  · exact B262607
  · exact B262611
  · exact B262615
  · exact B262619

theorem C1 (j : ℕ) (h1 : 65655 ≤ j) (h2 : j ≤ 65954) : Blo 259821 (4 * j + 3) := by
  interval_cases j
  · exact B262623
  · exact B262627
  · exact B262631
  · exact B262635
  · exact B262639
  · exact B262643
  · exact B262647
  · exact B262651
  · exact B262655
  · exact B262659
  · exact B262663
  · exact B262667
  · exact B262671
  · exact B262675
  · exact B262679
  · exact B262683
  · exact B262687
  · exact B262691
  · exact B262695
  · exact B262699
  · exact B262703
  · exact B262707
  · exact B262711
  · exact B262715
  · exact B262719
  · exact B262723
  · exact B262727
  · exact B262731
  · exact B262735
  · exact B262739
  · exact B262743
  · exact B262747
  · exact B262751
  · exact B262755
  · exact B262759
  · exact B262763
  · exact B262767
  · exact B262771
  · exact B262775
  · exact B262779
  · exact B262783
  · exact B262787
  · exact B262791
  · exact B262795
  · exact B262799
  · exact B262803
  · exact B262807
  · exact B262811
  · exact B262815
  · exact B262819
  · exact B262823
  · exact B262827
  · exact B262831
  · exact B262835
  · exact B262839
  · exact B262843
  · exact B262847
  · exact B262851
  · exact B262855
  · exact B262859
  · exact B262863
  · exact B262867
  · exact B262871
  · exact B262875
  · exact B262879
  · exact B262883
  · exact B262887
  · exact B262891
  · exact B262895
  · exact B262899
  · exact B262903
  · exact B262907
  · exact B262911
  · exact B262915
  · exact B262919
  · exact B262923
  · exact B262927
  · exact B262931
  · exact B262935
  · exact B262939
  · exact B262943
  · exact B262947
  · exact B262951
  · exact B262955
  · exact B262959
  · exact B262963
  · exact B262967
  · exact B262971
  · exact B262975
  · exact B262979
  · exact B262983
  · exact B262987
  · exact B262991
  · exact B262995
  · exact B262999
  · exact B263003
  · exact B263007
  · exact B263011
  · exact B263015
  · exact B263019
  · exact B263023
  · exact B263027
  · exact B263031
  · exact B263035
  · exact B263039
  · exact B263043
  · exact B263047
  · exact B263051
  · exact B263055
  · exact B263059
  · exact B263063
  · exact B263067
  · exact B263071
  · exact B263075
  · exact B263079
  · exact B263083
  · exact B263087
  · exact B263091
  · exact B263095
  · exact B263099
  · exact B263103
  · exact B263107
  · exact B263111
  · exact B263115
  · exact B263119
  · exact B263123
  · exact B263127
  · exact B263131
  · exact B263135
  · exact B263139
  · exact B263143
  · exact B263147
  · exact B263151
  · exact B263155
  · exact B263159
  · exact B263163
  · exact B263167
  · exact B263171
  · exact B263175
  · exact B263179
  · exact B263183
  · exact B263187
  · exact B263191
  · exact B263195
  · exact B263199
  · exact B263203
  · exact B263207
  · exact B263211
  · exact B263215
  · exact B263219
  · exact B263223
  · exact B263227
  · exact B263231
  · exact B263235
  · exact B263239
  · exact B263243
  · exact B263247
  · exact B263251
  · exact B263255
  · exact B263259
  · exact B263263
  · exact B263267
  · exact B263271
  · exact B263275
  · exact B263279
  · exact B263283
  · exact B263287
  · exact B263291
  · exact B263295
  · exact B263299
  · exact B263303
  · exact B263307
  · exact B263311
  · exact B263315
  · exact B263319
  · exact B263323
  · exact B263327
  · exact B263331
  · exact B263335
  · exact B263339
  · exact B263343
  · exact B263347
  · exact B263351
  · exact B263355
  · exact B263359
  · exact B263363
  · exact B263367
  · exact B263371
  · exact B263375
  · exact B263379
  · exact B263383
  · exact B263387
  · exact B263391
  · exact B263395
  · exact B263399
  · exact B263403
  · exact B263407
  · exact B263411
  · exact B263415
  · exact B263419
  · exact B263423
  · exact B263427
  · exact B263431
  · exact B263435
  · exact B263439
  · exact B263443
  · exact B263447
  · exact B263451
  · exact B263455
  · exact B263459
  · exact B263463
  · exact B263467
  · exact B263471
  · exact B263475
  · exact B263479
  · exact B263483
  · exact B263487
  · exact B263491
  · exact B263495
  · exact B263499
  · exact B263503
  · exact B263507
  · exact B263511
  · exact B263515
  · exact B263519
  · exact B263523
  · exact B263527
  · exact B263531
  · exact B263535
  · exact B263539
  · exact B263543
  · exact B263547
  · exact B263551
  · exact B263555
  · exact B263559
  · exact B263563
  · exact B263567
  · exact B263571
  · exact B263575
  · exact B263579
  · exact B263583
  · exact B263587
  · exact B263591
  · exact B263595
  · exact B263599
  · exact B263603
  · exact B263607
  · exact B263611
  · exact B263615
  · exact B263619
  · exact B263623
  · exact B263627
  · exact B263631
  · exact B263635
  · exact B263639
  · exact B263643
  · exact B263647
  · exact B263651
  · exact B263655
  · exact B263659
  · exact B263663
  · exact B263667
  · exact B263671
  · exact B263675
  · exact B263679
  · exact B263683
  · exact B263687
  · exact B263691
  · exact B263695
  · exact B263699
  · exact B263703
  · exact B263707
  · exact B263711
  · exact B263715
  · exact B263719
  · exact B263723
  · exact B263727
  · exact B263731
  · exact B263735
  · exact B263739
  · exact B263743
  · exact B263747
  · exact B263751
  · exact B263755
  · exact B263759
  · exact B263763
  · exact B263767
  · exact B263771
  · exact B263775
  · exact B263779
  · exact B263783
  · exact B263787
  · exact B263791
  · exact B263795
  · exact B263799
  · exact B263803
  · exact B263807
  · exact B263811
  · exact B263815
  · exact B263819

theorem solution (m : ℕ) (hlo : 259821 ≤ m) (hhi : m ≤ 263821) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 64955 ≤ j := by omega
    have hj2 : j ≤ 65954 := by omega
    have hb : Blo 259821 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 65655 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
