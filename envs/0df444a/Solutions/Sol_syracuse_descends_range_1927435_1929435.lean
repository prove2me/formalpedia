-- Prove2me | solution 1 for syracuse_descends_range_1927435_1929435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T16:47:18.094487+00:00
-- url     : https://prove2.me/submissions/3fb608e6-b19d-4bc6-b88f-2b6b7e08d2ff

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

theorem B2168365 : Blo 1927435 2168365 := bbase (se 3 (by rfl) ⟨406568, by rfl⟩ : syracuseStep 2168365 = 813137) (by norm_num)
theorem B2891153 : Blo 1927435 2891153 := bstep (se 2 (by rfl) ⟨1084182, by rfl⟩ : syracuseStep 2891153 = 2168365) B2168365
theorem B1927435 : Blo 1927435 1927435 := bstep (se 1 (by rfl) ⟨1445576, by rfl⟩ : syracuseStep 1927435 = 2891153) B2891153
theorem B6505109 : Blo 1927435 6505109 := bbase (se 6 (by rfl) ⟨152463, by rfl⟩ : syracuseStep 6505109 = 304927) (by norm_num)
theorem B4336739 : Blo 1927435 4336739 := bstep (se 1 (by rfl) ⟨3252554, by rfl⟩ : syracuseStep 4336739 = 6505109) B6505109
theorem B2891159 : Blo 1927435 2891159 := bstep (se 1 (by rfl) ⟨2168369, by rfl⟩ : syracuseStep 2891159 = 4336739) B4336739
theorem B1927439 : Blo 1927435 1927439 := bstep (se 1 (by rfl) ⟨1445579, by rfl⟩ : syracuseStep 1927439 = 2891159) B2891159
theorem B2891165 : Blo 1927435 2891165 := bbase (se 3 (by rfl) ⟨542093, by rfl⟩ : syracuseStep 2891165 = 1084187) (by norm_num)
theorem B1927443 : Blo 1927435 1927443 := bstep (se 1 (by rfl) ⟨1445582, by rfl⟩ : syracuseStep 1927443 = 2891165) B2891165
theorem B4336757 : Blo 1927435 4336757 := bbase (se 5 (by rfl) ⟨203285, by rfl⟩ : syracuseStep 4336757 = 406571) (by norm_num)
theorem B2891171 : Blo 1927435 2891171 := bstep (se 1 (by rfl) ⟨2168378, by rfl⟩ : syracuseStep 2891171 = 4336757) B4336757
theorem B1927447 : Blo 1927435 1927447 := bstep (se 1 (by rfl) ⟨1445585, by rfl⟩ : syracuseStep 1927447 = 2891171) B2891171
theorem B16466165 : Blo 1927435 16466165 := bbase (se 5 (by rfl) ⟨771851, by rfl⟩ : syracuseStep 16466165 = 1543703) (by norm_num)
theorem B10977443 : Blo 1927435 10977443 := bstep (se 1 (by rfl) ⟨8233082, by rfl⟩ : syracuseStep 10977443 = 16466165) B16466165
theorem B7318295 : Blo 1927435 7318295 := bstep (se 1 (by rfl) ⟨5488721, by rfl⟩ : syracuseStep 7318295 = 10977443) B10977443
theorem B4878863 : Blo 1927435 4878863 := bstep (se 1 (by rfl) ⟨3659147, by rfl⟩ : syracuseStep 4878863 = 7318295) B7318295
theorem B3252575 : Blo 1927435 3252575 := bstep (se 1 (by rfl) ⟨2439431, by rfl⟩ : syracuseStep 3252575 = 4878863) B4878863
theorem B2168383 : Blo 1927435 2168383 := bstep (se 1 (by rfl) ⟨1626287, by rfl⟩ : syracuseStep 2168383 = 3252575) B3252575
theorem B2891177 : Blo 1927435 2891177 := bstep (se 2 (by rfl) ⟨1084191, by rfl⟩ : syracuseStep 2891177 = 2168383) B2168383
theorem B1927451 : Blo 1927435 1927451 := bstep (se 1 (by rfl) ⟨1445588, by rfl⟩ : syracuseStep 1927451 = 2891177) B2891177
theorem B7318309 : Blo 1927435 7318309 := bbase (se 4 (by rfl) ⟨686091, by rfl⟩ : syracuseStep 7318309 = 1372183) (by norm_num)
theorem B9757745 : Blo 1927435 9757745 := bstep (se 2 (by rfl) ⟨3659154, by rfl⟩ : syracuseStep 9757745 = 7318309) B7318309
theorem B6505163 : Blo 1927435 6505163 := bstep (se 1 (by rfl) ⟨4878872, by rfl⟩ : syracuseStep 6505163 = 9757745) B9757745
theorem B4336775 : Blo 1927435 4336775 := bstep (se 1 (by rfl) ⟨3252581, by rfl⟩ : syracuseStep 4336775 = 6505163) B6505163
theorem B2891183 : Blo 1927435 2891183 := bstep (se 1 (by rfl) ⟨2168387, by rfl⟩ : syracuseStep 2891183 = 4336775) B4336775
theorem B1927455 : Blo 1927435 1927455 := bstep (se 1 (by rfl) ⟨1445591, by rfl⟩ : syracuseStep 1927455 = 2891183) B2891183
theorem B2891189 : Blo 1927435 2891189 := bbase (se 5 (by rfl) ⟨135524, by rfl⟩ : syracuseStep 2891189 = 271049) (by norm_num)
theorem B1927459 : Blo 1927435 1927459 := bstep (se 1 (by rfl) ⟨1445594, by rfl⟩ : syracuseStep 1927459 = 2891189) B2891189
theorem B4878893 : Blo 1927435 4878893 := bbase (se 3 (by rfl) ⟨914792, by rfl⟩ : syracuseStep 4878893 = 1829585) (by norm_num)
theorem B3252595 : Blo 1927435 3252595 := bstep (se 1 (by rfl) ⟨2439446, by rfl⟩ : syracuseStep 3252595 = 4878893) B4878893
theorem B4336793 : Blo 1927435 4336793 := bstep (se 2 (by rfl) ⟨1626297, by rfl⟩ : syracuseStep 4336793 = 3252595) B3252595
theorem B2891195 : Blo 1927435 2891195 := bstep (se 1 (by rfl) ⟨2168396, by rfl⟩ : syracuseStep 2891195 = 4336793) B4336793
theorem B1927463 : Blo 1927435 1927463 := bstep (se 1 (by rfl) ⟨1445597, by rfl⟩ : syracuseStep 1927463 = 2891195) B2891195
theorem B2168401 : Blo 1927435 2168401 := bbase (se 2 (by rfl) ⟨813150, by rfl⟩ : syracuseStep 2168401 = 1626301) (by norm_num)
theorem B2891201 : Blo 1927435 2891201 := bstep (se 2 (by rfl) ⟨1084200, by rfl⟩ : syracuseStep 2891201 = 2168401) B2168401
theorem B1927467 : Blo 1927435 1927467 := bstep (se 1 (by rfl) ⟨1445600, by rfl⟩ : syracuseStep 1927467 = 2891201) B2891201
theorem B2744389 : Blo 1927435 2744389 := bbase (se 4 (by rfl) ⟨257286, by rfl⟩ : syracuseStep 2744389 = 514573) (by norm_num)
theorem B3659185 : Blo 1927435 3659185 := bstep (se 2 (by rfl) ⟨1372194, by rfl⟩ : syracuseStep 3659185 = 2744389) B2744389
theorem B4878913 : Blo 1927435 4878913 := bstep (se 2 (by rfl) ⟨1829592, by rfl⟩ : syracuseStep 4878913 = 3659185) B3659185
theorem B6505217 : Blo 1927435 6505217 := bstep (se 2 (by rfl) ⟨2439456, by rfl⟩ : syracuseStep 6505217 = 4878913) B4878913
theorem B4336811 : Blo 1927435 4336811 := bstep (se 1 (by rfl) ⟨3252608, by rfl⟩ : syracuseStep 4336811 = 6505217) B6505217
theorem B2891207 : Blo 1927435 2891207 := bstep (se 1 (by rfl) ⟨2168405, by rfl⟩ : syracuseStep 2891207 = 4336811) B4336811
theorem B1927471 : Blo 1927435 1927471 := bstep (se 1 (by rfl) ⟨1445603, by rfl⟩ : syracuseStep 1927471 = 2891207) B2891207
theorem B2891213 : Blo 1927435 2891213 := bbase (se 3 (by rfl) ⟨542102, by rfl⟩ : syracuseStep 2891213 = 1084205) (by norm_num)
theorem B1927475 : Blo 1927435 1927475 := bstep (se 1 (by rfl) ⟨1445606, by rfl⟩ : syracuseStep 1927475 = 2891213) B2891213
theorem B4336829 : Blo 1927435 4336829 := bbase (se 3 (by rfl) ⟨813155, by rfl⟩ : syracuseStep 4336829 = 1626311) (by norm_num)
theorem B2891219 : Blo 1927435 2891219 := bstep (se 1 (by rfl) ⟨2168414, by rfl⟩ : syracuseStep 2891219 = 4336829) B4336829
theorem B1927479 : Blo 1927435 1927479 := bstep (se 1 (by rfl) ⟨1445609, by rfl⟩ : syracuseStep 1927479 = 2891219) B2891219
theorem B3252629 : Blo 1927435 3252629 := bbase (se 6 (by rfl) ⟨76233, by rfl⟩ : syracuseStep 3252629 = 152467) (by norm_num)
theorem B2168419 : Blo 1927435 2168419 := bstep (se 1 (by rfl) ⟨1626314, by rfl⟩ : syracuseStep 2168419 = 3252629) B3252629
theorem B2891225 : Blo 1927435 2891225 := bstep (se 2 (by rfl) ⟨1084209, by rfl⟩ : syracuseStep 2891225 = 2168419) B2168419
theorem B1927483 : Blo 1927435 1927483 := bstep (se 1 (by rfl) ⟨1445612, by rfl⟩ : syracuseStep 1927483 = 2891225) B2891225
theorem B7519493 : Blo 1927435 7519493 := bbase (se 4 (by rfl) ⟨704952, by rfl⟩ : syracuseStep 7519493 = 1409905) (by norm_num)
theorem B20051981 : Blo 1927435 20051981 := bstep (se 3 (by rfl) ⟨3759746, by rfl⟩ : syracuseStep 20051981 = 7519493) B7519493
theorem B13367987 : Blo 1927435 13367987 := bstep (se 1 (by rfl) ⟨10025990, by rfl⟩ : syracuseStep 13367987 = 20051981) B20051981
theorem B8911991 : Blo 1927435 8911991 := bstep (se 1 (by rfl) ⟨6683993, by rfl⟩ : syracuseStep 8911991 = 13367987) B13367987
theorem B23765309 : Blo 1927435 23765309 := bstep (se 3 (by rfl) ⟨4455995, by rfl⟩ : syracuseStep 23765309 = 8911991) B8911991
theorem B15843539 : Blo 1927435 15843539 := bstep (se 1 (by rfl) ⟨11882654, by rfl⟩ : syracuseStep 15843539 = 23765309) B23765309
theorem B42249437 : Blo 1927435 42249437 := bstep (se 3 (by rfl) ⟨7921769, by rfl⟩ : syracuseStep 42249437 = 15843539) B15843539
theorem B28166291 : Blo 1927435 28166291 := bstep (se 1 (by rfl) ⟨21124718, by rfl⟩ : syracuseStep 28166291 = 42249437) B42249437
theorem B18777527 : Blo 1927435 18777527 := bstep (se 1 (by rfl) ⟨14083145, by rfl⟩ : syracuseStep 18777527 = 28166291) B28166291
theorem B12518351 : Blo 1927435 12518351 := bstep (se 1 (by rfl) ⟨9388763, by rfl⟩ : syracuseStep 12518351 = 18777527) B18777527
theorem B8345567 : Blo 1927435 8345567 := bstep (se 1 (by rfl) ⟨6259175, by rfl⟩ : syracuseStep 8345567 = 12518351) B12518351
theorem B5563711 : Blo 1927435 5563711 := bstep (se 1 (by rfl) ⟨4172783, by rfl⟩ : syracuseStep 5563711 = 8345567) B8345567
theorem B29673125 : Blo 1927435 29673125 := bstep (se 4 (by rfl) ⟨2781855, by rfl⟩ : syracuseStep 29673125 = 5563711) B5563711
theorem B19782083 : Blo 1927435 19782083 := bstep (se 1 (by rfl) ⟨14836562, by rfl⟩ : syracuseStep 19782083 = 29673125) B29673125
theorem B13188055 : Blo 1927435 13188055 := bstep (se 1 (by rfl) ⟨9891041, by rfl⟩ : syracuseStep 13188055 = 19782083) B19782083
theorem B17584073 : Blo 1927435 17584073 := bstep (se 2 (by rfl) ⟨6594027, by rfl⟩ : syracuseStep 17584073 = 13188055) B13188055
theorem B11722715 : Blo 1927435 11722715 := bstep (se 1 (by rfl) ⟨8792036, by rfl⟩ : syracuseStep 11722715 = 17584073) B17584073
theorem B7815143 : Blo 1927435 7815143 := bstep (se 1 (by rfl) ⟨5861357, by rfl⟩ : syracuseStep 7815143 = 11722715) B11722715
theorem B5210095 : Blo 1927435 5210095 := bstep (se 1 (by rfl) ⟨3907571, by rfl⟩ : syracuseStep 5210095 = 7815143) B7815143
theorem B6946793 : Blo 1927435 6946793 := bstep (se 2 (by rfl) ⟨2605047, by rfl⟩ : syracuseStep 6946793 = 5210095) B5210095
theorem B4631195 : Blo 1927435 4631195 := bstep (se 1 (by rfl) ⟨3473396, by rfl⟩ : syracuseStep 4631195 = 6946793) B6946793
theorem B12349853 : Blo 1927435 12349853 := bstep (se 3 (by rfl) ⟨2315597, by rfl⟩ : syracuseStep 12349853 = 4631195) B4631195
theorem B8233235 : Blo 1927435 8233235 := bstep (se 1 (by rfl) ⟨6174926, by rfl⟩ : syracuseStep 8233235 = 12349853) B12349853
theorem B5488823 : Blo 1927435 5488823 := bstep (se 1 (by rfl) ⟨4116617, by rfl⟩ : syracuseStep 5488823 = 8233235) B8233235
theorem B14636861 : Blo 1927435 14636861 := bstep (se 3 (by rfl) ⟨2744411, by rfl⟩ : syracuseStep 14636861 = 5488823) B5488823
theorem B9757907 : Blo 1927435 9757907 := bstep (se 1 (by rfl) ⟨7318430, by rfl⟩ : syracuseStep 9757907 = 14636861) B14636861
theorem B6505271 : Blo 1927435 6505271 := bstep (se 1 (by rfl) ⟨4878953, by rfl⟩ : syracuseStep 6505271 = 9757907) B9757907
theorem B4336847 : Blo 1927435 4336847 := bstep (se 1 (by rfl) ⟨3252635, by rfl⟩ : syracuseStep 4336847 = 6505271) B6505271
theorem B2891231 : Blo 1927435 2891231 := bstep (se 1 (by rfl) ⟨2168423, by rfl⟩ : syracuseStep 2891231 = 4336847) B4336847
theorem B1927487 : Blo 1927435 1927487 := bstep (se 1 (by rfl) ⟨1445615, by rfl⟩ : syracuseStep 1927487 = 2891231) B2891231
theorem B2891237 : Blo 1927435 2891237 := bbase (se 4 (by rfl) ⟨271053, by rfl⟩ : syracuseStep 2891237 = 542107) (by norm_num)
theorem B1927491 : Blo 1927435 1927491 := bstep (se 1 (by rfl) ⟨1445618, by rfl⟩ : syracuseStep 1927491 = 2891237) B2891237
theorem B4396037 : Blo 1927435 4396037 := bbase (se 4 (by rfl) ⟨412128, by rfl⟩ : syracuseStep 4396037 = 824257) (by norm_num)
theorem B11722765 : Blo 1927435 11722765 := bstep (se 3 (by rfl) ⟨2198018, by rfl⟩ : syracuseStep 11722765 = 4396037) B4396037
theorem B15630353 : Blo 1927435 15630353 := bstep (se 2 (by rfl) ⟨5861382, by rfl⟩ : syracuseStep 15630353 = 11722765) B11722765
theorem B10420235 : Blo 1927435 10420235 := bstep (se 1 (by rfl) ⟨7815176, by rfl⟩ : syracuseStep 10420235 = 15630353) B15630353
theorem B6946823 : Blo 1927435 6946823 := bstep (se 1 (by rfl) ⟨5210117, by rfl⟩ : syracuseStep 6946823 = 10420235) B10420235
theorem B18524861 : Blo 1927435 18524861 := bstep (se 3 (by rfl) ⟨3473411, by rfl⟩ : syracuseStep 18524861 = 6946823) B6946823
theorem B12349907 : Blo 1927435 12349907 := bstep (se 1 (by rfl) ⟨9262430, by rfl⟩ : syracuseStep 12349907 = 18524861) B18524861
theorem B8233271 : Blo 1927435 8233271 := bstep (se 1 (by rfl) ⟨6174953, by rfl⟩ : syracuseStep 8233271 = 12349907) B12349907
theorem B5488847 : Blo 1927435 5488847 := bstep (se 1 (by rfl) ⟨4116635, by rfl⟩ : syracuseStep 5488847 = 8233271) B8233271
theorem B3659231 : Blo 1927435 3659231 := bstep (se 1 (by rfl) ⟨2744423, by rfl⟩ : syracuseStep 3659231 = 5488847) B5488847
theorem B2439487 : Blo 1927435 2439487 := bstep (se 1 (by rfl) ⟨1829615, by rfl⟩ : syracuseStep 2439487 = 3659231) B3659231
theorem B3252649 : Blo 1927435 3252649 := bstep (se 2 (by rfl) ⟨1219743, by rfl⟩ : syracuseStep 3252649 = 2439487) B2439487
theorem B4336865 : Blo 1927435 4336865 := bstep (se 2 (by rfl) ⟨1626324, by rfl⟩ : syracuseStep 4336865 = 3252649) B3252649
theorem B2891243 : Blo 1927435 2891243 := bstep (se 1 (by rfl) ⟨2168432, by rfl⟩ : syracuseStep 2891243 = 4336865) B4336865
theorem B1927495 : Blo 1927435 1927495 := bstep (se 1 (by rfl) ⟨1445621, by rfl⟩ : syracuseStep 1927495 = 2891243) B2891243
theorem B2168437 : Blo 1927435 2168437 := bbase (se 5 (by rfl) ⟨101645, by rfl⟩ : syracuseStep 2168437 = 203291) (by norm_num)
theorem B2891249 : Blo 1927435 2891249 := bstep (se 2 (by rfl) ⟨1084218, by rfl⟩ : syracuseStep 2891249 = 2168437) B2168437
theorem B1927499 : Blo 1927435 1927499 := bstep (se 1 (by rfl) ⟨1445624, by rfl⟩ : syracuseStep 1927499 = 2891249) B2891249
theorem B2439497 : Blo 1927435 2439497 := bbase (se 2 (by rfl) ⟨914811, by rfl⟩ : syracuseStep 2439497 = 1829623) (by norm_num)
theorem B6505325 : Blo 1927435 6505325 := bstep (se 3 (by rfl) ⟨1219748, by rfl⟩ : syracuseStep 6505325 = 2439497) B2439497
theorem B4336883 : Blo 1927435 4336883 := bstep (se 1 (by rfl) ⟨3252662, by rfl⟩ : syracuseStep 4336883 = 6505325) B6505325
theorem B2891255 : Blo 1927435 2891255 := bstep (se 1 (by rfl) ⟨2168441, by rfl⟩ : syracuseStep 2891255 = 4336883) B4336883
theorem B1927503 : Blo 1927435 1927503 := bstep (se 1 (by rfl) ⟨1445627, by rfl⟩ : syracuseStep 1927503 = 2891255) B2891255
theorem B2891261 : Blo 1927435 2891261 := bbase (se 3 (by rfl) ⟨542111, by rfl⟩ : syracuseStep 2891261 = 1084223) (by norm_num)
theorem B1927507 : Blo 1927435 1927507 := bstep (se 1 (by rfl) ⟨1445630, by rfl⟩ : syracuseStep 1927507 = 2891261) B2891261
theorem B4336901 : Blo 1927435 4336901 := bbase (se 4 (by rfl) ⟨406584, by rfl⟩ : syracuseStep 4336901 = 813169) (by norm_num)
theorem B2891267 : Blo 1927435 2891267 := bstep (se 1 (by rfl) ⟨2168450, by rfl⟩ : syracuseStep 2891267 = 4336901) B4336901
theorem B1927511 : Blo 1927435 1927511 := bstep (se 1 (by rfl) ⟨1445633, by rfl⟩ : syracuseStep 1927511 = 2891267) B2891267
theorem B3659269 : Blo 1927435 3659269 := bbase (se 4 (by rfl) ⟨343056, by rfl⟩ : syracuseStep 3659269 = 686113) (by norm_num)
theorem B4879025 : Blo 1927435 4879025 := bstep (se 2 (by rfl) ⟨1829634, by rfl⟩ : syracuseStep 4879025 = 3659269) B3659269
theorem B3252683 : Blo 1927435 3252683 := bstep (se 1 (by rfl) ⟨2439512, by rfl⟩ : syracuseStep 3252683 = 4879025) B4879025
theorem B2168455 : Blo 1927435 2168455 := bstep (se 1 (by rfl) ⟨1626341, by rfl⟩ : syracuseStep 2168455 = 3252683) B3252683
theorem B2891273 : Blo 1927435 2891273 := bstep (se 2 (by rfl) ⟨1084227, by rfl⟩ : syracuseStep 2891273 = 2168455) B2168455
theorem B1927515 : Blo 1927435 1927515 := bstep (se 1 (by rfl) ⟨1445636, by rfl⟩ : syracuseStep 1927515 = 2891273) B2891273
theorem B9758069 : Blo 1927435 9758069 := bbase (se 5 (by rfl) ⟨457409, by rfl⟩ : syracuseStep 9758069 = 914819) (by norm_num)
theorem B6505379 : Blo 1927435 6505379 := bstep (se 1 (by rfl) ⟨4879034, by rfl⟩ : syracuseStep 6505379 = 9758069) B9758069
theorem B4336919 : Blo 1927435 4336919 := bstep (se 1 (by rfl) ⟨3252689, by rfl⟩ : syracuseStep 4336919 = 6505379) B6505379
theorem B2891279 : Blo 1927435 2891279 := bstep (se 1 (by rfl) ⟨2168459, by rfl⟩ : syracuseStep 2891279 = 4336919) B4336919
theorem B1927519 : Blo 1927435 1927519 := bstep (se 1 (by rfl) ⟨1445639, by rfl⟩ : syracuseStep 1927519 = 2891279) B2891279
theorem B2891285 : Blo 1927435 2891285 := bbase (se 6 (by rfl) ⟨67764, by rfl⟩ : syracuseStep 2891285 = 135529) (by norm_num)
theorem B1927523 : Blo 1927435 1927523 := bstep (se 1 (by rfl) ⟨1445642, by rfl⟩ : syracuseStep 1927523 = 2891285) B2891285
theorem B6684133 : Blo 1927435 6684133 := bbase (se 4 (by rfl) ⟨626637, by rfl⟩ : syracuseStep 6684133 = 1253275) (by norm_num)
theorem B8912177 : Blo 1927435 8912177 := bstep (se 2 (by rfl) ⟨3342066, by rfl⟩ : syracuseStep 8912177 = 6684133) B6684133
theorem B5941451 : Blo 1927435 5941451 := bstep (se 1 (by rfl) ⟨4456088, by rfl⟩ : syracuseStep 5941451 = 8912177) B8912177
theorem B15843869 : Blo 1927435 15843869 := bstep (se 3 (by rfl) ⟨2970725, by rfl⟩ : syracuseStep 15843869 = 5941451) B5941451
theorem B10562579 : Blo 1927435 10562579 := bstep (se 1 (by rfl) ⟨7921934, by rfl⟩ : syracuseStep 10562579 = 15843869) B15843869
theorem B7041719 : Blo 1927435 7041719 := bstep (se 1 (by rfl) ⟨5281289, by rfl⟩ : syracuseStep 7041719 = 10562579) B10562579
theorem B4694479 : Blo 1927435 4694479 := bstep (se 1 (by rfl) ⟨3520859, by rfl⟩ : syracuseStep 4694479 = 7041719) B7041719
theorem B25037221 : Blo 1927435 25037221 := bstep (se 4 (by rfl) ⟨2347239, by rfl⟩ : syracuseStep 25037221 = 4694479) B4694479
theorem B33382961 : Blo 1927435 33382961 := bstep (se 2 (by rfl) ⟨12518610, by rfl⟩ : syracuseStep 33382961 = 25037221) B25037221
theorem B22255307 : Blo 1927435 22255307 := bstep (se 1 (by rfl) ⟨16691480, by rfl⟩ : syracuseStep 22255307 = 33382961) B33382961
theorem B14836871 : Blo 1927435 14836871 := bstep (se 1 (by rfl) ⟨11127653, by rfl⟩ : syracuseStep 14836871 = 22255307) B22255307
theorem B9891247 : Blo 1927435 9891247 := bstep (se 1 (by rfl) ⟨7418435, by rfl⟩ : syracuseStep 9891247 = 14836871) B14836871
theorem B13188329 : Blo 1927435 13188329 := bstep (se 2 (by rfl) ⟨4945623, by rfl⟩ : syracuseStep 13188329 = 9891247) B9891247
theorem B8792219 : Blo 1927435 8792219 := bstep (se 1 (by rfl) ⟨6594164, by rfl⟩ : syracuseStep 8792219 = 13188329) B13188329
theorem B5861479 : Blo 1927435 5861479 := bstep (se 1 (by rfl) ⟨4396109, by rfl⟩ : syracuseStep 5861479 = 8792219) B8792219
theorem B7815305 : Blo 1927435 7815305 := bstep (se 2 (by rfl) ⟨2930739, by rfl⟩ : syracuseStep 7815305 = 5861479) B5861479
theorem B20840813 : Blo 1927435 20840813 := bstep (se 3 (by rfl) ⟨3907652, by rfl⟩ : syracuseStep 20840813 = 7815305) B7815305
theorem B13893875 : Blo 1927435 13893875 := bstep (se 1 (by rfl) ⟨10420406, by rfl⟩ : syracuseStep 13893875 = 20840813) B20840813
theorem B9262583 : Blo 1927435 9262583 := bstep (se 1 (by rfl) ⟨6946937, by rfl⟩ : syracuseStep 9262583 = 13893875) B13893875
theorem B6175055 : Blo 1927435 6175055 := bstep (se 1 (by rfl) ⟨4631291, by rfl⟩ : syracuseStep 6175055 = 9262583) B9262583
theorem B16466813 : Blo 1927435 16466813 := bstep (se 3 (by rfl) ⟨3087527, by rfl⟩ : syracuseStep 16466813 = 6175055) B6175055
theorem B10977875 : Blo 1927435 10977875 := bstep (se 1 (by rfl) ⟨8233406, by rfl⟩ : syracuseStep 10977875 = 16466813) B16466813
theorem B7318583 : Blo 1927435 7318583 := bstep (se 1 (by rfl) ⟨5488937, by rfl⟩ : syracuseStep 7318583 = 10977875) B10977875
theorem B4879055 : Blo 1927435 4879055 := bstep (se 1 (by rfl) ⟨3659291, by rfl⟩ : syracuseStep 4879055 = 7318583) B7318583
theorem B3252703 : Blo 1927435 3252703 := bstep (se 1 (by rfl) ⟨2439527, by rfl⟩ : syracuseStep 3252703 = 4879055) B4879055
theorem B4336937 : Blo 1927435 4336937 := bstep (se 2 (by rfl) ⟨1626351, by rfl⟩ : syracuseStep 4336937 = 3252703) B3252703
theorem B2891291 : Blo 1927435 2891291 := bstep (se 1 (by rfl) ⟨2168468, by rfl⟩ : syracuseStep 2891291 = 4336937) B4336937
theorem B1927527 : Blo 1927435 1927527 := bstep (se 1 (by rfl) ⟨1445645, by rfl⟩ : syracuseStep 1927527 = 2891291) B2891291
theorem B2168473 : Blo 1927435 2168473 := bbase (se 2 (by rfl) ⟨813177, by rfl⟩ : syracuseStep 2168473 = 1626355) (by norm_num)
theorem B2891297 : Blo 1927435 2891297 := bstep (se 2 (by rfl) ⟨1084236, by rfl⟩ : syracuseStep 2891297 = 2168473) B2168473
theorem B1927531 : Blo 1927435 1927531 := bstep (se 1 (by rfl) ⟨1445648, by rfl⟩ : syracuseStep 1927531 = 2891297) B2891297
theorem B7318613 : Blo 1927435 7318613 := bbase (se 8 (by rfl) ⟨42882, by rfl⟩ : syracuseStep 7318613 = 85765) (by norm_num)
theorem B4879075 : Blo 1927435 4879075 := bstep (se 1 (by rfl) ⟨3659306, by rfl⟩ : syracuseStep 4879075 = 7318613) B7318613
theorem B6505433 : Blo 1927435 6505433 := bstep (se 2 (by rfl) ⟨2439537, by rfl⟩ : syracuseStep 6505433 = 4879075) B4879075
theorem B4336955 : Blo 1927435 4336955 := bstep (se 1 (by rfl) ⟨3252716, by rfl⟩ : syracuseStep 4336955 = 6505433) B6505433
theorem B2891303 : Blo 1927435 2891303 := bstep (se 1 (by rfl) ⟨2168477, by rfl⟩ : syracuseStep 2891303 = 4336955) B4336955
theorem B1927535 : Blo 1927435 1927535 := bstep (se 1 (by rfl) ⟨1445651, by rfl⟩ : syracuseStep 1927535 = 2891303) B2891303
theorem B2891309 : Blo 1927435 2891309 := bbase (se 3 (by rfl) ⟨542120, by rfl⟩ : syracuseStep 2891309 = 1084241) (by norm_num)
theorem B1927539 : Blo 1927435 1927539 := bstep (se 1 (by rfl) ⟨1445654, by rfl⟩ : syracuseStep 1927539 = 2891309) B2891309
theorem B4336973 : Blo 1927435 4336973 := bbase (se 3 (by rfl) ⟨813182, by rfl⟩ : syracuseStep 4336973 = 1626365) (by norm_num)
theorem B2891315 : Blo 1927435 2891315 := bstep (se 1 (by rfl) ⟨2168486, by rfl⟩ : syracuseStep 2891315 = 4336973) B4336973
theorem B1927543 : Blo 1927435 1927543 := bstep (se 1 (by rfl) ⟨1445657, by rfl⟩ : syracuseStep 1927543 = 2891315) B2891315
theorem B2439553 : Blo 1927435 2439553 := bbase (se 2 (by rfl) ⟨914832, by rfl⟩ : syracuseStep 2439553 = 1829665) (by norm_num)
theorem B3252737 : Blo 1927435 3252737 := bstep (se 2 (by rfl) ⟨1219776, by rfl⟩ : syracuseStep 3252737 = 2439553) B2439553
theorem B2168491 : Blo 1927435 2168491 := bstep (se 1 (by rfl) ⟨1626368, by rfl⟩ : syracuseStep 2168491 = 3252737) B3252737
theorem B2891321 : Blo 1927435 2891321 := bstep (se 2 (by rfl) ⟨1084245, by rfl⟩ : syracuseStep 2891321 = 2168491) B2168491
theorem B1927547 : Blo 1927435 1927547 := bstep (se 1 (by rfl) ⟨1445660, by rfl⟩ : syracuseStep 1927547 = 2891321) B2891321
theorem B2058377 : Blo 1927435 2058377 := bbase (se 2 (by rfl) ⟨771891, by rfl⟩ : syracuseStep 2058377 = 1543783) (by norm_num)
theorem B21956021 : Blo 1927435 21956021 := bstep (se 5 (by rfl) ⟨1029188, by rfl⟩ : syracuseStep 21956021 = 2058377) B2058377
theorem B14637347 : Blo 1927435 14637347 := bstep (se 1 (by rfl) ⟨10978010, by rfl⟩ : syracuseStep 14637347 = 21956021) B21956021
theorem B9758231 : Blo 1927435 9758231 := bstep (se 1 (by rfl) ⟨7318673, by rfl⟩ : syracuseStep 9758231 = 14637347) B14637347
theorem B6505487 : Blo 1927435 6505487 := bstep (se 1 (by rfl) ⟨4879115, by rfl⟩ : syracuseStep 6505487 = 9758231) B9758231
theorem B4336991 : Blo 1927435 4336991 := bstep (se 1 (by rfl) ⟨3252743, by rfl⟩ : syracuseStep 4336991 = 6505487) B6505487
theorem B2891327 : Blo 1927435 2891327 := bstep (se 1 (by rfl) ⟨2168495, by rfl⟩ : syracuseStep 2891327 = 4336991) B4336991
theorem B1927551 : Blo 1927435 1927551 := bstep (se 1 (by rfl) ⟨1445663, by rfl⟩ : syracuseStep 1927551 = 2891327) B2891327
theorem B2891333 : Blo 1927435 2891333 := bbase (se 4 (by rfl) ⟨271062, by rfl⟩ : syracuseStep 2891333 = 542125) (by norm_num)
theorem B1927555 : Blo 1927435 1927555 := bstep (se 1 (by rfl) ⟨1445666, by rfl⟩ : syracuseStep 1927555 = 2891333) B2891333
theorem B3252757 : Blo 1927435 3252757 := bbase (se 6 (by rfl) ⟨76236, by rfl⟩ : syracuseStep 3252757 = 152473) (by norm_num)
theorem B4337009 : Blo 1927435 4337009 := bstep (se 2 (by rfl) ⟨1626378, by rfl⟩ : syracuseStep 4337009 = 3252757) B3252757
theorem B2891339 : Blo 1927435 2891339 := bstep (se 1 (by rfl) ⟨2168504, by rfl⟩ : syracuseStep 2891339 = 4337009) B4337009
theorem B1927559 : Blo 1927435 1927559 := bstep (se 1 (by rfl) ⟨1445669, by rfl⟩ : syracuseStep 1927559 = 2891339) B2891339
theorem B2168509 : Blo 1927435 2168509 := bbase (se 3 (by rfl) ⟨406595, by rfl⟩ : syracuseStep 2168509 = 813191) (by norm_num)
theorem B2891345 : Blo 1927435 2891345 := bstep (se 2 (by rfl) ⟨1084254, by rfl⟩ : syracuseStep 2891345 = 2168509) B2168509
theorem B1927563 : Blo 1927435 1927563 := bstep (se 1 (by rfl) ⟨1445672, by rfl⟩ : syracuseStep 1927563 = 2891345) B2891345
theorem B6505541 : Blo 1927435 6505541 := bbase (se 4 (by rfl) ⟨609894, by rfl⟩ : syracuseStep 6505541 = 1219789) (by norm_num)
theorem B4337027 : Blo 1927435 4337027 := bstep (se 1 (by rfl) ⟨3252770, by rfl⟩ : syracuseStep 4337027 = 6505541) B6505541
theorem B2891351 : Blo 1927435 2891351 := bstep (se 1 (by rfl) ⟨2168513, by rfl⟩ : syracuseStep 2891351 = 4337027) B4337027
theorem B1927567 : Blo 1927435 1927567 := bstep (se 1 (by rfl) ⟨1445675, by rfl⟩ : syracuseStep 1927567 = 2891351) B2891351
theorem B2891357 : Blo 1927435 2891357 := bbase (se 3 (by rfl) ⟨542129, by rfl⟩ : syracuseStep 2891357 = 1084259) (by norm_num)
theorem B1927571 : Blo 1927435 1927571 := bstep (se 1 (by rfl) ⟨1445678, by rfl⟩ : syracuseStep 1927571 = 2891357) B2891357
theorem B4337045 : Blo 1927435 4337045 := bbase (se 6 (by rfl) ⟨101649, by rfl⟩ : syracuseStep 4337045 = 203299) (by norm_num)
theorem B2891363 : Blo 1927435 2891363 := bstep (se 1 (by rfl) ⟨2168522, by rfl⟩ : syracuseStep 2891363 = 4337045) B4337045
theorem B1927575 : Blo 1927435 1927575 := bstep (se 1 (by rfl) ⟨1445681, by rfl⟩ : syracuseStep 1927575 = 2891363) B2891363
theorem B6259477 : Blo 1927435 6259477 := bbase (se 6 (by rfl) ⟨146706, by rfl⟩ : syracuseStep 6259477 = 293413) (by norm_num)
theorem B8345969 : Blo 1927435 8345969 := bstep (se 2 (by rfl) ⟨3129738, by rfl⟩ : syracuseStep 8345969 = 6259477) B6259477
theorem B5563979 : Blo 1927435 5563979 := bstep (se 1 (by rfl) ⟨4172984, by rfl⟩ : syracuseStep 5563979 = 8345969) B8345969
theorem B3709319 : Blo 1927435 3709319 := bstep (se 1 (by rfl) ⟨2781989, by rfl⟩ : syracuseStep 3709319 = 5563979) B5563979
theorem B9891517 : Blo 1927435 9891517 := bstep (se 3 (by rfl) ⟨1854659, by rfl⟩ : syracuseStep 9891517 = 3709319) B3709319
theorem B13188689 : Blo 1927435 13188689 := bstep (se 2 (by rfl) ⟨4945758, by rfl⟩ : syracuseStep 13188689 = 9891517) B9891517
theorem B8792459 : Blo 1927435 8792459 := bstep (se 1 (by rfl) ⟨6594344, by rfl⟩ : syracuseStep 8792459 = 13188689) B13188689
theorem B5861639 : Blo 1927435 5861639 := bstep (se 1 (by rfl) ⟨4396229, by rfl⟩ : syracuseStep 5861639 = 8792459) B8792459
theorem B3907759 : Blo 1927435 3907759 := bstep (se 1 (by rfl) ⟨2930819, by rfl⟩ : syracuseStep 3907759 = 5861639) B5861639
theorem B5210345 : Blo 1927435 5210345 := bstep (se 2 (by rfl) ⟨1953879, by rfl⟩ : syracuseStep 5210345 = 3907759) B3907759
theorem B13894253 : Blo 1927435 13894253 := bstep (se 3 (by rfl) ⟨2605172, by rfl⟩ : syracuseStep 13894253 = 5210345) B5210345
theorem B9262835 : Blo 1927435 9262835 := bstep (se 1 (by rfl) ⟨6947126, by rfl⟩ : syracuseStep 9262835 = 13894253) B13894253
theorem B6175223 : Blo 1927435 6175223 := bstep (se 1 (by rfl) ⟨4631417, by rfl⟩ : syracuseStep 6175223 = 9262835) B9262835
theorem B4116815 : Blo 1927435 4116815 := bstep (se 1 (by rfl) ⟨3087611, by rfl⟩ : syracuseStep 4116815 = 6175223) B6175223
theorem B2744543 : Blo 1927435 2744543 := bstep (se 1 (by rfl) ⟨2058407, by rfl⟩ : syracuseStep 2744543 = 4116815) B4116815
theorem B7318781 : Blo 1927435 7318781 := bstep (se 3 (by rfl) ⟨1372271, by rfl⟩ : syracuseStep 7318781 = 2744543) B2744543
theorem B4879187 : Blo 1927435 4879187 := bstep (se 1 (by rfl) ⟨3659390, by rfl⟩ : syracuseStep 4879187 = 7318781) B7318781
theorem B3252791 : Blo 1927435 3252791 := bstep (se 1 (by rfl) ⟨2439593, by rfl⟩ : syracuseStep 3252791 = 4879187) B4879187
theorem B2168527 : Blo 1927435 2168527 := bstep (se 1 (by rfl) ⟨1626395, by rfl⟩ : syracuseStep 2168527 = 3252791) B3252791
theorem B2891369 : Blo 1927435 2891369 := bstep (se 2 (by rfl) ⟨1084263, by rfl⟩ : syracuseStep 2891369 = 2168527) B2168527
theorem B1927579 : Blo 1927435 1927579 := bstep (se 1 (by rfl) ⟨1445684, by rfl⟩ : syracuseStep 1927579 = 2891369) B2891369
theorem B2315713 : Blo 1927435 2315713 := bbase (se 2 (by rfl) ⟨868392, by rfl⟩ : syracuseStep 2315713 = 1736785) (by norm_num)
theorem B3087617 : Blo 1927435 3087617 := bstep (se 2 (by rfl) ⟨1157856, by rfl⟩ : syracuseStep 3087617 = 2315713) B2315713
theorem B8233645 : Blo 1927435 8233645 := bstep (se 3 (by rfl) ⟨1543808, by rfl⟩ : syracuseStep 8233645 = 3087617) B3087617
theorem B10978193 : Blo 1927435 10978193 := bstep (se 2 (by rfl) ⟨4116822, by rfl⟩ : syracuseStep 10978193 = 8233645) B8233645
theorem B7318795 : Blo 1927435 7318795 := bstep (se 1 (by rfl) ⟨5489096, by rfl⟩ : syracuseStep 7318795 = 10978193) B10978193
theorem B9758393 : Blo 1927435 9758393 := bstep (se 2 (by rfl) ⟨3659397, by rfl⟩ : syracuseStep 9758393 = 7318795) B7318795
theorem B6505595 : Blo 1927435 6505595 := bstep (se 1 (by rfl) ⟨4879196, by rfl⟩ : syracuseStep 6505595 = 9758393) B9758393
theorem B4337063 : Blo 1927435 4337063 := bstep (se 1 (by rfl) ⟨3252797, by rfl⟩ : syracuseStep 4337063 = 6505595) B6505595
theorem B2891375 : Blo 1927435 2891375 := bstep (se 1 (by rfl) ⟨2168531, by rfl⟩ : syracuseStep 2891375 = 4337063) B4337063
theorem B1927583 : Blo 1927435 1927583 := bstep (se 1 (by rfl) ⟨1445687, by rfl⟩ : syracuseStep 1927583 = 2891375) B2891375
theorem B2891381 : Blo 1927435 2891381 := bbase (se 5 (by rfl) ⟨135533, by rfl⟩ : syracuseStep 2891381 = 271067) (by norm_num)
theorem B1927587 : Blo 1927435 1927587 := bstep (se 1 (by rfl) ⟨1445690, by rfl⟩ : syracuseStep 1927587 = 2891381) B2891381
theorem B3659413 : Blo 1927435 3659413 := bbase (se 6 (by rfl) ⟨85767, by rfl⟩ : syracuseStep 3659413 = 171535) (by norm_num)
theorem B4879217 : Blo 1927435 4879217 := bstep (se 2 (by rfl) ⟨1829706, by rfl⟩ : syracuseStep 4879217 = 3659413) B3659413
theorem B3252811 : Blo 1927435 3252811 := bstep (se 1 (by rfl) ⟨2439608, by rfl⟩ : syracuseStep 3252811 = 4879217) B4879217
theorem B4337081 : Blo 1927435 4337081 := bstep (se 2 (by rfl) ⟨1626405, by rfl⟩ : syracuseStep 4337081 = 3252811) B3252811
theorem B2891387 : Blo 1927435 2891387 := bstep (se 1 (by rfl) ⟨2168540, by rfl⟩ : syracuseStep 2891387 = 4337081) B4337081
theorem B1927591 : Blo 1927435 1927591 := bstep (se 1 (by rfl) ⟨1445693, by rfl⟩ : syracuseStep 1927591 = 2891387) B2891387
theorem B2168545 : Blo 1927435 2168545 := bbase (se 2 (by rfl) ⟨813204, by rfl⟩ : syracuseStep 2168545 = 1626409) (by norm_num)
theorem B2891393 : Blo 1927435 2891393 := bstep (se 2 (by rfl) ⟨1084272, by rfl⟩ : syracuseStep 2891393 = 2168545) B2168545
theorem B1927595 : Blo 1927435 1927595 := bstep (se 1 (by rfl) ⟨1445696, by rfl⟩ : syracuseStep 1927595 = 2891393) B2891393
theorem B4879237 : Blo 1927435 4879237 := bbase (se 4 (by rfl) ⟨457428, by rfl⟩ : syracuseStep 4879237 = 914857) (by norm_num)
theorem B6505649 : Blo 1927435 6505649 := bstep (se 2 (by rfl) ⟨2439618, by rfl⟩ : syracuseStep 6505649 = 4879237) B4879237
theorem B4337099 : Blo 1927435 4337099 := bstep (se 1 (by rfl) ⟨3252824, by rfl⟩ : syracuseStep 4337099 = 6505649) B6505649
theorem B2891399 : Blo 1927435 2891399 := bstep (se 1 (by rfl) ⟨2168549, by rfl⟩ : syracuseStep 2891399 = 4337099) B4337099
theorem B1927599 : Blo 1927435 1927599 := bstep (se 1 (by rfl) ⟨1445699, by rfl⟩ : syracuseStep 1927599 = 2891399) B2891399
theorem B2891405 : Blo 1927435 2891405 := bbase (se 3 (by rfl) ⟨542138, by rfl⟩ : syracuseStep 2891405 = 1084277) (by norm_num)
theorem B1927603 : Blo 1927435 1927603 := bstep (se 1 (by rfl) ⟨1445702, by rfl⟩ : syracuseStep 1927603 = 2891405) B2891405
theorem B4337117 : Blo 1927435 4337117 := bbase (se 3 (by rfl) ⟨813209, by rfl⟩ : syracuseStep 4337117 = 1626419) (by norm_num)
theorem B2891411 : Blo 1927435 2891411 := bstep (se 1 (by rfl) ⟨2168558, by rfl⟩ : syracuseStep 2891411 = 4337117) B4337117
theorem B1927607 : Blo 1927435 1927607 := bstep (se 1 (by rfl) ⟨1445705, by rfl⟩ : syracuseStep 1927607 = 2891411) B2891411
theorem B3252845 : Blo 1927435 3252845 := bbase (se 3 (by rfl) ⟨609908, by rfl⟩ : syracuseStep 3252845 = 1219817) (by norm_num)
theorem B2168563 : Blo 1927435 2168563 := bstep (se 1 (by rfl) ⟨1626422, by rfl⟩ : syracuseStep 2168563 = 3252845) B3252845
theorem B2891417 : Blo 1927435 2891417 := bstep (se 2 (by rfl) ⟨1084281, by rfl⟩ : syracuseStep 2891417 = 2168563) B2168563
theorem B1927611 : Blo 1927435 1927611 := bstep (se 1 (by rfl) ⟨1445708, by rfl⟩ : syracuseStep 1927611 = 2891417) B2891417
theorem B17585237 : Blo 1927435 17585237 := bbase (se 8 (by rfl) ⟨103038, by rfl⟩ : syracuseStep 17585237 = 206077) (by norm_num)
theorem B11723491 : Blo 1927435 11723491 := bstep (se 1 (by rfl) ⟨8792618, by rfl⟩ : syracuseStep 11723491 = 17585237) B17585237
theorem B15631321 : Blo 1927435 15631321 := bstep (se 2 (by rfl) ⟨5861745, by rfl⟩ : syracuseStep 15631321 = 11723491) B11723491
theorem B20841761 : Blo 1927435 20841761 := bstep (se 2 (by rfl) ⟨7815660, by rfl⟩ : syracuseStep 20841761 = 15631321) B15631321
theorem B13894507 : Blo 1927435 13894507 := bstep (se 1 (by rfl) ⟨10420880, by rfl⟩ : syracuseStep 13894507 = 20841761) B20841761
theorem B18526009 : Blo 1927435 18526009 := bstep (se 2 (by rfl) ⟨6947253, by rfl⟩ : syracuseStep 18526009 = 13894507) B13894507
theorem B24701345 : Blo 1927435 24701345 := bstep (se 2 (by rfl) ⟨9263004, by rfl⟩ : syracuseStep 24701345 = 18526009) B18526009
theorem B16467563 : Blo 1927435 16467563 := bstep (se 1 (by rfl) ⟨12350672, by rfl⟩ : syracuseStep 16467563 = 24701345) B24701345
theorem B10978375 : Blo 1927435 10978375 := bstep (se 1 (by rfl) ⟨8233781, by rfl⟩ : syracuseStep 10978375 = 16467563) B16467563
theorem B14637833 : Blo 1927435 14637833 := bstep (se 2 (by rfl) ⟨5489187, by rfl⟩ : syracuseStep 14637833 = 10978375) B10978375
theorem B9758555 : Blo 1927435 9758555 := bstep (se 1 (by rfl) ⟨7318916, by rfl⟩ : syracuseStep 9758555 = 14637833) B14637833
theorem B6505703 : Blo 1927435 6505703 := bstep (se 1 (by rfl) ⟨4879277, by rfl⟩ : syracuseStep 6505703 = 9758555) B9758555
theorem B4337135 : Blo 1927435 4337135 := bstep (se 1 (by rfl) ⟨3252851, by rfl⟩ : syracuseStep 4337135 = 6505703) B6505703
theorem B2891423 : Blo 1927435 2891423 := bstep (se 1 (by rfl) ⟨2168567, by rfl⟩ : syracuseStep 2891423 = 4337135) B4337135
theorem B1927615 : Blo 1927435 1927615 := bstep (se 1 (by rfl) ⟨1445711, by rfl⟩ : syracuseStep 1927615 = 2891423) B2891423
theorem B2891429 : Blo 1927435 2891429 := bbase (se 4 (by rfl) ⟨271071, by rfl⟩ : syracuseStep 2891429 = 542143) (by norm_num)
theorem B1927619 : Blo 1927435 1927619 := bstep (se 1 (by rfl) ⟨1445714, by rfl⟩ : syracuseStep 1927619 = 2891429) B2891429
theorem B2439649 : Blo 1927435 2439649 := bbase (se 2 (by rfl) ⟨914868, by rfl⟩ : syracuseStep 2439649 = 1829737) (by norm_num)
theorem B3252865 : Blo 1927435 3252865 := bstep (se 2 (by rfl) ⟨1219824, by rfl⟩ : syracuseStep 3252865 = 2439649) B2439649
theorem B4337153 : Blo 1927435 4337153 := bstep (se 2 (by rfl) ⟨1626432, by rfl⟩ : syracuseStep 4337153 = 3252865) B3252865
theorem B2891435 : Blo 1927435 2891435 := bstep (se 1 (by rfl) ⟨2168576, by rfl⟩ : syracuseStep 2891435 = 4337153) B4337153
theorem B1927623 : Blo 1927435 1927623 := bstep (se 1 (by rfl) ⟨1445717, by rfl⟩ : syracuseStep 1927623 = 2891435) B2891435
theorem B2168581 : Blo 1927435 2168581 := bbase (se 4 (by rfl) ⟨203304, by rfl⟩ : syracuseStep 2168581 = 406609) (by norm_num)
theorem B2891441 : Blo 1927435 2891441 := bstep (se 2 (by rfl) ⟨1084290, by rfl⟩ : syracuseStep 2891441 = 2168581) B2168581
theorem B1927627 : Blo 1927435 1927627 := bstep (se 1 (by rfl) ⟨1445720, by rfl⟩ : syracuseStep 1927627 = 2891441) B2891441
theorem B4396349 : Blo 1927435 4396349 := bbase (se 3 (by rfl) ⟨824315, by rfl⟩ : syracuseStep 4396349 = 1648631) (by norm_num)
theorem B2930899 : Blo 1927435 2930899 := bstep (se 1 (by rfl) ⟨2198174, by rfl⟩ : syracuseStep 2930899 = 4396349) B4396349
theorem B3907865 : Blo 1927435 3907865 := bstep (se 2 (by rfl) ⟨1465449, by rfl⟩ : syracuseStep 3907865 = 2930899) B2930899
theorem B10420973 : Blo 1927435 10420973 := bstep (se 3 (by rfl) ⟨1953932, by rfl⟩ : syracuseStep 10420973 = 3907865) B3907865
theorem B6947315 : Blo 1927435 6947315 := bstep (se 1 (by rfl) ⟨5210486, by rfl⟩ : syracuseStep 6947315 = 10420973) B10420973
theorem B4631543 : Blo 1927435 4631543 := bstep (se 1 (by rfl) ⟨3473657, by rfl⟩ : syracuseStep 4631543 = 6947315) B6947315
theorem B3087695 : Blo 1927435 3087695 := bstep (se 1 (by rfl) ⟨2315771, by rfl⟩ : syracuseStep 3087695 = 4631543) B4631543
theorem B2058463 : Blo 1927435 2058463 := bstep (se 1 (by rfl) ⟨1543847, by rfl⟩ : syracuseStep 2058463 = 3087695) B3087695
theorem B2744617 : Blo 1927435 2744617 := bstep (se 2 (by rfl) ⟨1029231, by rfl⟩ : syracuseStep 2744617 = 2058463) B2058463
theorem B3659489 : Blo 1927435 3659489 := bstep (se 2 (by rfl) ⟨1372308, by rfl⟩ : syracuseStep 3659489 = 2744617) B2744617
theorem B2439659 : Blo 1927435 2439659 := bstep (se 1 (by rfl) ⟨1829744, by rfl⟩ : syracuseStep 2439659 = 3659489) B3659489
theorem B6505757 : Blo 1927435 6505757 := bstep (se 3 (by rfl) ⟨1219829, by rfl⟩ : syracuseStep 6505757 = 2439659) B2439659
theorem B4337171 : Blo 1927435 4337171 := bstep (se 1 (by rfl) ⟨3252878, by rfl⟩ : syracuseStep 4337171 = 6505757) B6505757
theorem B2891447 : Blo 1927435 2891447 := bstep (se 1 (by rfl) ⟨2168585, by rfl⟩ : syracuseStep 2891447 = 4337171) B4337171
theorem B1927631 : Blo 1927435 1927631 := bstep (se 1 (by rfl) ⟨1445723, by rfl⟩ : syracuseStep 1927631 = 2891447) B2891447
theorem B2891453 : Blo 1927435 2891453 := bbase (se 3 (by rfl) ⟨542147, by rfl⟩ : syracuseStep 2891453 = 1084295) (by norm_num)
theorem B1927635 : Blo 1927435 1927635 := bstep (se 1 (by rfl) ⟨1445726, by rfl⟩ : syracuseStep 1927635 = 2891453) B2891453
theorem B4337189 : Blo 1927435 4337189 := bbase (se 4 (by rfl) ⟨406611, by rfl⟩ : syracuseStep 4337189 = 813223) (by norm_num)
theorem B2891459 : Blo 1927435 2891459 := bstep (se 1 (by rfl) ⟨2168594, by rfl⟩ : syracuseStep 2891459 = 4337189) B4337189
theorem B1927639 : Blo 1927435 1927639 := bstep (se 1 (by rfl) ⟨1445729, by rfl⟩ : syracuseStep 1927639 = 2891459) B2891459
theorem B4879349 : Blo 1927435 4879349 := bbase (se 5 (by rfl) ⟨228719, by rfl⟩ : syracuseStep 4879349 = 457439) (by norm_num)
theorem B3252899 : Blo 1927435 3252899 := bstep (se 1 (by rfl) ⟨2439674, by rfl⟩ : syracuseStep 3252899 = 4879349) B4879349
theorem B2168599 : Blo 1927435 2168599 := bstep (se 1 (by rfl) ⟨1626449, by rfl⟩ : syracuseStep 2168599 = 3252899) B3252899
theorem B2891465 : Blo 1927435 2891465 := bstep (se 2 (by rfl) ⟨1084299, by rfl⟩ : syracuseStep 2891465 = 2168599) B2168599
theorem B1927643 : Blo 1927435 1927643 := bstep (se 1 (by rfl) ⟨1445732, by rfl⟩ : syracuseStep 1927643 = 2891465) B2891465
theorem B6022885 : Blo 1927435 6022885 := bbase (se 4 (by rfl) ⟨564645, by rfl⟩ : syracuseStep 6022885 = 1129291) (by norm_num)
theorem B8030513 : Blo 1927435 8030513 := bstep (se 2 (by rfl) ⟨3011442, by rfl⟩ : syracuseStep 8030513 = 6022885) B6022885
theorem B5353675 : Blo 1927435 5353675 := bstep (se 1 (by rfl) ⟨4015256, by rfl⟩ : syracuseStep 5353675 = 8030513) B8030513
theorem B28552933 : Blo 1927435 28552933 := bstep (se 4 (by rfl) ⟨2676837, by rfl⟩ : syracuseStep 28552933 = 5353675) B5353675
theorem B38070577 : Blo 1927435 38070577 := bstep (se 2 (by rfl) ⟨14276466, by rfl⟩ : syracuseStep 38070577 = 28552933) B28552933
theorem B50760769 : Blo 1927435 50760769 := bstep (se 2 (by rfl) ⟨19035288, by rfl⟩ : syracuseStep 50760769 = 38070577) B38070577
theorem B67681025 : Blo 1927435 67681025 := bstep (se 2 (by rfl) ⟨25380384, by rfl⟩ : syracuseStep 67681025 = 50760769) B50760769
theorem B45120683 : Blo 1927435 45120683 := bstep (se 1 (by rfl) ⟨33840512, by rfl⟩ : syracuseStep 45120683 = 67681025) B67681025
theorem B120321821 : Blo 1927435 120321821 := bstep (se 3 (by rfl) ⟨22560341, by rfl⟩ : syracuseStep 120321821 = 45120683) B45120683
theorem B80214547 : Blo 1927435 80214547 := bstep (se 1 (by rfl) ⟨60160910, by rfl⟩ : syracuseStep 80214547 = 120321821) B120321821
theorem B106952729 : Blo 1927435 106952729 := bstep (se 2 (by rfl) ⟨40107273, by rfl⟩ : syracuseStep 106952729 = 80214547) B80214547
theorem B1140829109 : Blo 1927435 1140829109 := bstep (se 5 (by rfl) ⟨53476364, by rfl⟩ : syracuseStep 1140829109 = 106952729) B106952729
theorem B760552739 : Blo 1927435 760552739 := bstep (se 1 (by rfl) ⟨570414554, by rfl⟩ : syracuseStep 760552739 = 1140829109) B1140829109
theorem B507035159 : Blo 1927435 507035159 := bstep (se 1 (by rfl) ⟨380276369, by rfl⟩ : syracuseStep 507035159 = 760552739) B760552739
theorem B338023439 : Blo 1927435 338023439 := bstep (se 1 (by rfl) ⟨253517579, by rfl⟩ : syracuseStep 338023439 = 507035159) B507035159
theorem B225348959 : Blo 1927435 225348959 := bstep (se 1 (by rfl) ⟨169011719, by rfl⟩ : syracuseStep 225348959 = 338023439) B338023439
theorem B150232639 : Blo 1927435 150232639 := bstep (se 1 (by rfl) ⟨112674479, by rfl⟩ : syracuseStep 150232639 = 225348959) B225348959
theorem B200310185 : Blo 1927435 200310185 := bstep (se 2 (by rfl) ⟨75116319, by rfl⟩ : syracuseStep 200310185 = 150232639) B150232639
theorem B133540123 : Blo 1927435 133540123 := bstep (se 1 (by rfl) ⟨100155092, by rfl⟩ : syracuseStep 133540123 = 200310185) B200310185
theorem B178053497 : Blo 1927435 178053497 := bstep (se 2 (by rfl) ⟨66770061, by rfl⟩ : syracuseStep 178053497 = 133540123) B133540123
theorem B118702331 : Blo 1927435 118702331 := bstep (se 1 (by rfl) ⟨89026748, by rfl⟩ : syracuseStep 118702331 = 178053497) B178053497
theorem B79134887 : Blo 1927435 79134887 := bstep (se 1 (by rfl) ⟨59351165, by rfl⟩ : syracuseStep 79134887 = 118702331) B118702331
theorem B52756591 : Blo 1927435 52756591 := bstep (se 1 (by rfl) ⟨39567443, by rfl⟩ : syracuseStep 52756591 = 79134887) B79134887
theorem B70342121 : Blo 1927435 70342121 := bstep (se 2 (by rfl) ⟨26378295, by rfl⟩ : syracuseStep 70342121 = 52756591) B52756591
theorem B46894747 : Blo 1927435 46894747 := bstep (se 1 (by rfl) ⟨35171060, by rfl⟩ : syracuseStep 46894747 = 70342121) B70342121
theorem B62526329 : Blo 1927435 62526329 := bstep (se 2 (by rfl) ⟨23447373, by rfl⟩ : syracuseStep 62526329 = 46894747) B46894747
theorem B41684219 : Blo 1927435 41684219 := bstep (se 1 (by rfl) ⟨31263164, by rfl⟩ : syracuseStep 41684219 = 62526329) B62526329
theorem B27789479 : Blo 1927435 27789479 := bstep (se 1 (by rfl) ⟨20842109, by rfl⟩ : syracuseStep 27789479 = 41684219) B41684219
theorem B18526319 : Blo 1927435 18526319 := bstep (se 1 (by rfl) ⟨13894739, by rfl⟩ : syracuseStep 18526319 = 27789479) B27789479
theorem B12350879 : Blo 1927435 12350879 := bstep (se 1 (by rfl) ⟨9263159, by rfl⟩ : syracuseStep 12350879 = 18526319) B18526319
theorem B8233919 : Blo 1927435 8233919 := bstep (se 1 (by rfl) ⟨6175439, by rfl⟩ : syracuseStep 8233919 = 12350879) B12350879
theorem B5489279 : Blo 1927435 5489279 := bstep (se 1 (by rfl) ⟨4116959, by rfl⟩ : syracuseStep 5489279 = 8233919) B8233919
theorem B3659519 : Blo 1927435 3659519 := bstep (se 1 (by rfl) ⟨2744639, by rfl⟩ : syracuseStep 3659519 = 5489279) B5489279
theorem B9758717 : Blo 1927435 9758717 := bstep (se 3 (by rfl) ⟨1829759, by rfl⟩ : syracuseStep 9758717 = 3659519) B3659519
theorem B6505811 : Blo 1927435 6505811 := bstep (se 1 (by rfl) ⟨4879358, by rfl⟩ : syracuseStep 6505811 = 9758717) B9758717
theorem B4337207 : Blo 1927435 4337207 := bstep (se 1 (by rfl) ⟨3252905, by rfl⟩ : syracuseStep 4337207 = 6505811) B6505811
theorem B2891471 : Blo 1927435 2891471 := bstep (se 1 (by rfl) ⟨2168603, by rfl⟩ : syracuseStep 2891471 = 4337207) B4337207
theorem B1927647 : Blo 1927435 1927647 := bstep (se 1 (by rfl) ⟨1445735, by rfl⟩ : syracuseStep 1927647 = 2891471) B2891471
theorem B2891477 : Blo 1927435 2891477 := bbase (se 7 (by rfl) ⟨33884, by rfl⟩ : syracuseStep 2891477 = 67769) (by norm_num)
theorem B1927651 : Blo 1927435 1927651 := bstep (se 1 (by rfl) ⟨1445738, by rfl⟩ : syracuseStep 1927651 = 2891477) B2891477
theorem B3087733 : Blo 1927435 3087733 := bbase (se 5 (by rfl) ⟨144737, by rfl⟩ : syracuseStep 3087733 = 289475) (by norm_num)
theorem B4116977 : Blo 1927435 4116977 := bstep (se 2 (by rfl) ⟨1543866, by rfl⟩ : syracuseStep 4116977 = 3087733) B3087733
theorem B2744651 : Blo 1927435 2744651 := bstep (se 1 (by rfl) ⟨2058488, by rfl⟩ : syracuseStep 2744651 = 4116977) B4116977
theorem B7319069 : Blo 1927435 7319069 := bstep (se 3 (by rfl) ⟨1372325, by rfl⟩ : syracuseStep 7319069 = 2744651) B2744651
theorem B4879379 : Blo 1927435 4879379 := bstep (se 1 (by rfl) ⟨3659534, by rfl⟩ : syracuseStep 4879379 = 7319069) B7319069
theorem B3252919 : Blo 1927435 3252919 := bstep (se 1 (by rfl) ⟨2439689, by rfl⟩ : syracuseStep 3252919 = 4879379) B4879379
theorem B4337225 : Blo 1927435 4337225 := bstep (se 2 (by rfl) ⟨1626459, by rfl⟩ : syracuseStep 4337225 = 3252919) B3252919
theorem B2891483 : Blo 1927435 2891483 := bstep (se 1 (by rfl) ⟨2168612, by rfl⟩ : syracuseStep 2891483 = 4337225) B4337225
theorem B1927655 : Blo 1927435 1927655 := bstep (se 1 (by rfl) ⟨1445741, by rfl⟩ : syracuseStep 1927655 = 2891483) B2891483
theorem B2168617 : Blo 1927435 2168617 := bbase (se 2 (by rfl) ⟨813231, by rfl⟩ : syracuseStep 2168617 = 1626463) (by norm_num)
theorem B2891489 : Blo 1927435 2891489 := bstep (se 2 (by rfl) ⟨1084308, by rfl⟩ : syracuseStep 2891489 = 2168617) B2168617
theorem B1927659 : Blo 1927435 1927659 := bstep (se 1 (by rfl) ⟨1445744, by rfl⟩ : syracuseStep 1927659 = 2891489) B2891489
theorem B2315809 : Blo 1927435 2315809 := bbase (se 2 (by rfl) ⟨868428, by rfl⟩ : syracuseStep 2315809 = 1736857) (by norm_num)
theorem B12350981 : Blo 1927435 12350981 := bstep (se 4 (by rfl) ⟨1157904, by rfl⟩ : syracuseStep 12350981 = 2315809) B2315809
theorem B8233987 : Blo 1927435 8233987 := bstep (se 1 (by rfl) ⟨6175490, by rfl⟩ : syracuseStep 8233987 = 12350981) B12350981
theorem B10978649 : Blo 1927435 10978649 := bstep (se 2 (by rfl) ⟨4116993, by rfl⟩ : syracuseStep 10978649 = 8233987) B8233987
theorem B7319099 : Blo 1927435 7319099 := bstep (se 1 (by rfl) ⟨5489324, by rfl⟩ : syracuseStep 7319099 = 10978649) B10978649
theorem B4879399 : Blo 1927435 4879399 := bstep (se 1 (by rfl) ⟨3659549, by rfl⟩ : syracuseStep 4879399 = 7319099) B7319099
theorem B6505865 : Blo 1927435 6505865 := bstep (se 2 (by rfl) ⟨2439699, by rfl⟩ : syracuseStep 6505865 = 4879399) B4879399
theorem B4337243 : Blo 1927435 4337243 := bstep (se 1 (by rfl) ⟨3252932, by rfl⟩ : syracuseStep 4337243 = 6505865) B6505865
theorem B2891495 : Blo 1927435 2891495 := bstep (se 1 (by rfl) ⟨2168621, by rfl⟩ : syracuseStep 2891495 = 4337243) B4337243
theorem B1927663 : Blo 1927435 1927663 := bstep (se 1 (by rfl) ⟨1445747, by rfl⟩ : syracuseStep 1927663 = 2891495) B2891495
theorem B2891501 : Blo 1927435 2891501 := bbase (se 3 (by rfl) ⟨542156, by rfl⟩ : syracuseStep 2891501 = 1084313) (by norm_num)
theorem B1927667 : Blo 1927435 1927667 := bstep (se 1 (by rfl) ⟨1445750, by rfl⟩ : syracuseStep 1927667 = 2891501) B2891501
theorem B4337261 : Blo 1927435 4337261 := bbase (se 3 (by rfl) ⟨813236, by rfl⟩ : syracuseStep 4337261 = 1626473) (by norm_num)
theorem B2891507 : Blo 1927435 2891507 := bstep (se 1 (by rfl) ⟨2168630, by rfl⟩ : syracuseStep 2891507 = 4337261) B4337261
theorem B1927671 : Blo 1927435 1927671 := bstep (se 1 (by rfl) ⟨1445753, by rfl⟩ : syracuseStep 1927671 = 2891507) B2891507
theorem B3659573 : Blo 1927435 3659573 := bbase (se 5 (by rfl) ⟨171542, by rfl⟩ : syracuseStep 3659573 = 343085) (by norm_num)
theorem B2439715 : Blo 1927435 2439715 := bstep (se 1 (by rfl) ⟨1829786, by rfl⟩ : syracuseStep 2439715 = 3659573) B3659573
theorem B3252953 : Blo 1927435 3252953 := bstep (se 2 (by rfl) ⟨1219857, by rfl⟩ : syracuseStep 3252953 = 2439715) B2439715
theorem B2168635 : Blo 1927435 2168635 := bstep (se 1 (by rfl) ⟨1626476, by rfl⟩ : syracuseStep 2168635 = 3252953) B3252953
theorem B2891513 : Blo 1927435 2891513 := bstep (se 2 (by rfl) ⟨1084317, by rfl⟩ : syracuseStep 2891513 = 2168635) B2168635
theorem B1927675 : Blo 1927435 1927675 := bstep (se 1 (by rfl) ⟨1445756, by rfl⟩ : syracuseStep 1927675 = 2891513) B2891513
theorem B66771157 : Blo 1927435 66771157 := bbase (se 7 (by rfl) ⟨782474, by rfl⟩ : syracuseStep 66771157 = 1564949) (by norm_num)
theorem B89028209 : Blo 1927435 89028209 := bstep (se 2 (by rfl) ⟨33385578, by rfl⟩ : syracuseStep 89028209 = 66771157) B66771157
theorem B59352139 : Blo 1927435 59352139 := bstep (se 1 (by rfl) ⟨44514104, by rfl⟩ : syracuseStep 59352139 = 89028209) B89028209
theorem B79136185 : Blo 1927435 79136185 := bstep (se 2 (by rfl) ⟨29676069, by rfl⟩ : syracuseStep 79136185 = 59352139) B59352139
theorem B105514913 : Blo 1927435 105514913 := bstep (se 2 (by rfl) ⟨39568092, by rfl⟩ : syracuseStep 105514913 = 79136185) B79136185
theorem B281373101 : Blo 1927435 281373101 := bstep (se 3 (by rfl) ⟨52757456, by rfl⟩ : syracuseStep 281373101 = 105514913) B105514913
theorem B187582067 : Blo 1927435 187582067 := bstep (se 1 (by rfl) ⟨140686550, by rfl⟩ : syracuseStep 187582067 = 281373101) B281373101
theorem B125054711 : Blo 1927435 125054711 := bstep (se 1 (by rfl) ⟨93791033, by rfl⟩ : syracuseStep 125054711 = 187582067) B187582067
theorem B83369807 : Blo 1927435 83369807 := bstep (se 1 (by rfl) ⟨62527355, by rfl⟩ : syracuseStep 83369807 = 125054711) B125054711
theorem B55579871 : Blo 1927435 55579871 := bstep (se 1 (by rfl) ⟨41684903, by rfl⟩ : syracuseStep 55579871 = 83369807) B83369807
theorem B37053247 : Blo 1927435 37053247 := bstep (se 1 (by rfl) ⟨27789935, by rfl⟩ : syracuseStep 37053247 = 55579871) B55579871
theorem B49404329 : Blo 1927435 49404329 := bstep (se 2 (by rfl) ⟨18526623, by rfl⟩ : syracuseStep 49404329 = 37053247) B37053247
theorem B32936219 : Blo 1927435 32936219 := bstep (se 1 (by rfl) ⟨24702164, by rfl⟩ : syracuseStep 32936219 = 49404329) B49404329
theorem B21957479 : Blo 1927435 21957479 := bstep (se 1 (by rfl) ⟨16468109, by rfl⟩ : syracuseStep 21957479 = 32936219) B32936219
theorem B14638319 : Blo 1927435 14638319 := bstep (se 1 (by rfl) ⟨10978739, by rfl⟩ : syracuseStep 14638319 = 21957479) B21957479
theorem B9758879 : Blo 1927435 9758879 := bstep (se 1 (by rfl) ⟨7319159, by rfl⟩ : syracuseStep 9758879 = 14638319) B14638319
theorem B6505919 : Blo 1927435 6505919 := bstep (se 1 (by rfl) ⟨4879439, by rfl⟩ : syracuseStep 6505919 = 9758879) B9758879
theorem B4337279 : Blo 1927435 4337279 := bstep (se 1 (by rfl) ⟨3252959, by rfl⟩ : syracuseStep 4337279 = 6505919) B6505919
theorem B2891519 : Blo 1927435 2891519 := bstep (se 1 (by rfl) ⟨2168639, by rfl⟩ : syracuseStep 2891519 = 4337279) B4337279
theorem B1927679 : Blo 1927435 1927679 := bstep (se 1 (by rfl) ⟨1445759, by rfl⟩ : syracuseStep 1927679 = 2891519) B2891519
theorem B2891525 : Blo 1927435 2891525 := bbase (se 4 (by rfl) ⟨271080, by rfl⟩ : syracuseStep 2891525 = 542161) (by norm_num)
theorem B1927683 : Blo 1927435 1927683 := bstep (se 1 (by rfl) ⟨1445762, by rfl⟩ : syracuseStep 1927683 = 2891525) B2891525
theorem B3252973 : Blo 1927435 3252973 := bbase (se 3 (by rfl) ⟨609932, by rfl⟩ : syracuseStep 3252973 = 1219865) (by norm_num)
theorem B4337297 : Blo 1927435 4337297 := bstep (se 2 (by rfl) ⟨1626486, by rfl⟩ : syracuseStep 4337297 = 3252973) B3252973
theorem B2891531 : Blo 1927435 2891531 := bstep (se 1 (by rfl) ⟨2168648, by rfl⟩ : syracuseStep 2891531 = 4337297) B4337297
theorem B1927687 : Blo 1927435 1927687 := bstep (se 1 (by rfl) ⟨1445765, by rfl⟩ : syracuseStep 1927687 = 2891531) B2891531
theorem B2168653 : Blo 1927435 2168653 := bbase (se 3 (by rfl) ⟨406622, by rfl⟩ : syracuseStep 2168653 = 813245) (by norm_num)
theorem B2891537 : Blo 1927435 2891537 := bstep (se 2 (by rfl) ⟨1084326, by rfl⟩ : syracuseStep 2891537 = 2168653) B2168653
theorem B1927691 : Blo 1927435 1927691 := bstep (se 1 (by rfl) ⟨1445768, by rfl⟩ : syracuseStep 1927691 = 2891537) B2891537
theorem B6505973 : Blo 1927435 6505973 := bbase (se 5 (by rfl) ⟨304967, by rfl⟩ : syracuseStep 6505973 = 609935) (by norm_num)
theorem B4337315 : Blo 1927435 4337315 := bstep (se 1 (by rfl) ⟨3252986, by rfl⟩ : syracuseStep 4337315 = 6505973) B6505973
theorem B2891543 : Blo 1927435 2891543 := bstep (se 1 (by rfl) ⟨2168657, by rfl⟩ : syracuseStep 2891543 = 4337315) B4337315
theorem B1927695 : Blo 1927435 1927695 := bstep (se 1 (by rfl) ⟨1445771, by rfl⟩ : syracuseStep 1927695 = 2891543) B2891543
theorem B2891549 : Blo 1927435 2891549 := bbase (se 3 (by rfl) ⟨542165, by rfl⟩ : syracuseStep 2891549 = 1084331) (by norm_num)
theorem B1927699 : Blo 1927435 1927699 := bstep (se 1 (by rfl) ⟨1445774, by rfl⟩ : syracuseStep 1927699 = 2891549) B2891549
theorem B4337333 : Blo 1927435 4337333 := bbase (se 5 (by rfl) ⟨203312, by rfl⟩ : syracuseStep 4337333 = 406625) (by norm_num)
theorem B2891555 : Blo 1927435 2891555 := bstep (se 1 (by rfl) ⟨2168666, by rfl⟩ : syracuseStep 2891555 = 4337333) B4337333
theorem B1927703 : Blo 1927435 1927703 := bstep (se 1 (by rfl) ⟨1445777, by rfl⟩ : syracuseStep 1927703 = 2891555) B2891555
theorem B10978901 : Blo 1927435 10978901 := bbase (se 8 (by rfl) ⟨64329, by rfl⟩ : syracuseStep 10978901 = 128659) (by norm_num)
theorem B7319267 : Blo 1927435 7319267 := bstep (se 1 (by rfl) ⟨5489450, by rfl⟩ : syracuseStep 7319267 = 10978901) B10978901
theorem B4879511 : Blo 1927435 4879511 := bstep (se 1 (by rfl) ⟨3659633, by rfl⟩ : syracuseStep 4879511 = 7319267) B7319267
theorem B3253007 : Blo 1927435 3253007 := bstep (se 1 (by rfl) ⟨2439755, by rfl⟩ : syracuseStep 3253007 = 4879511) B4879511
theorem B2168671 : Blo 1927435 2168671 := bstep (se 1 (by rfl) ⟨1626503, by rfl⟩ : syracuseStep 2168671 = 3253007) B3253007
theorem B2891561 : Blo 1927435 2891561 := bstep (se 2 (by rfl) ⟨1084335, by rfl⟩ : syracuseStep 2891561 = 2168671) B2168671
theorem B1927707 : Blo 1927435 1927707 := bstep (se 1 (by rfl) ⟨1445780, by rfl⟩ : syracuseStep 1927707 = 2891561) B2891561
theorem B5489461 : Blo 1927435 5489461 := bbase (se 5 (by rfl) ⟨257318, by rfl⟩ : syracuseStep 5489461 = 514637) (by norm_num)
theorem B7319281 : Blo 1927435 7319281 := bstep (se 2 (by rfl) ⟨2744730, by rfl⟩ : syracuseStep 7319281 = 5489461) B5489461
theorem B9759041 : Blo 1927435 9759041 := bstep (se 2 (by rfl) ⟨3659640, by rfl⟩ : syracuseStep 9759041 = 7319281) B7319281
theorem B6506027 : Blo 1927435 6506027 := bstep (se 1 (by rfl) ⟨4879520, by rfl⟩ : syracuseStep 6506027 = 9759041) B9759041
theorem B4337351 : Blo 1927435 4337351 := bstep (se 1 (by rfl) ⟨3253013, by rfl⟩ : syracuseStep 4337351 = 6506027) B6506027
theorem B2891567 : Blo 1927435 2891567 := bstep (se 1 (by rfl) ⟨2168675, by rfl⟩ : syracuseStep 2891567 = 4337351) B4337351
theorem B1927711 : Blo 1927435 1927711 := bstep (se 1 (by rfl) ⟨1445783, by rfl⟩ : syracuseStep 1927711 = 2891567) B2891567
theorem B2891573 : Blo 1927435 2891573 := bbase (se 5 (by rfl) ⟨135542, by rfl⟩ : syracuseStep 2891573 = 271085) (by norm_num)
theorem B1927715 : Blo 1927435 1927715 := bstep (se 1 (by rfl) ⟨1445786, by rfl⟩ : syracuseStep 1927715 = 2891573) B2891573
theorem B4879541 : Blo 1927435 4879541 := bbase (se 5 (by rfl) ⟨228728, by rfl⟩ : syracuseStep 4879541 = 457457) (by norm_num)
theorem B3253027 : Blo 1927435 3253027 := bstep (se 1 (by rfl) ⟨2439770, by rfl⟩ : syracuseStep 3253027 = 4879541) B4879541
theorem B4337369 : Blo 1927435 4337369 := bstep (se 2 (by rfl) ⟨1626513, by rfl⟩ : syracuseStep 4337369 = 3253027) B3253027
theorem B2891579 : Blo 1927435 2891579 := bstep (se 1 (by rfl) ⟨2168684, by rfl⟩ : syracuseStep 2891579 = 4337369) B4337369
theorem B1927719 : Blo 1927435 1927719 := bstep (se 1 (by rfl) ⟨1445789, by rfl⟩ : syracuseStep 1927719 = 2891579) B2891579
theorem B2168689 : Blo 1927435 2168689 := bbase (se 2 (by rfl) ⟨813258, by rfl⟩ : syracuseStep 2168689 = 1626517) (by norm_num)
theorem B2891585 : Blo 1927435 2891585 := bstep (se 2 (by rfl) ⟨1084344, by rfl⟩ : syracuseStep 2891585 = 2168689) B2168689
theorem B1927723 : Blo 1927435 1927723 := bstep (se 1 (by rfl) ⟨1445792, by rfl⟩ : syracuseStep 1927723 = 2891585) B2891585
theorem B8234261 : Blo 1927435 8234261 := bbase (se 6 (by rfl) ⟨192990, by rfl⟩ : syracuseStep 8234261 = 385981) (by norm_num)
theorem B5489507 : Blo 1927435 5489507 := bstep (se 1 (by rfl) ⟨4117130, by rfl⟩ : syracuseStep 5489507 = 8234261) B8234261
theorem B3659671 : Blo 1927435 3659671 := bstep (se 1 (by rfl) ⟨2744753, by rfl⟩ : syracuseStep 3659671 = 5489507) B5489507
theorem B4879561 : Blo 1927435 4879561 := bstep (se 2 (by rfl) ⟨1829835, by rfl⟩ : syracuseStep 4879561 = 3659671) B3659671
theorem B6506081 : Blo 1927435 6506081 := bstep (se 2 (by rfl) ⟨2439780, by rfl⟩ : syracuseStep 6506081 = 4879561) B4879561
theorem B4337387 : Blo 1927435 4337387 := bstep (se 1 (by rfl) ⟨3253040, by rfl⟩ : syracuseStep 4337387 = 6506081) B6506081
theorem B2891591 : Blo 1927435 2891591 := bstep (se 1 (by rfl) ⟨2168693, by rfl⟩ : syracuseStep 2891591 = 4337387) B4337387
theorem B1927727 : Blo 1927435 1927727 := bstep (se 1 (by rfl) ⟨1445795, by rfl⟩ : syracuseStep 1927727 = 2891591) B2891591
theorem B2891597 : Blo 1927435 2891597 := bbase (se 3 (by rfl) ⟨542174, by rfl⟩ : syracuseStep 2891597 = 1084349) (by norm_num)
theorem B1927731 : Blo 1927435 1927731 := bstep (se 1 (by rfl) ⟨1445798, by rfl⟩ : syracuseStep 1927731 = 2891597) B2891597
theorem B4337405 : Blo 1927435 4337405 := bbase (se 3 (by rfl) ⟨813263, by rfl⟩ : syracuseStep 4337405 = 1626527) (by norm_num)
theorem B2891603 : Blo 1927435 2891603 := bstep (se 1 (by rfl) ⟨2168702, by rfl⟩ : syracuseStep 2891603 = 4337405) B4337405
theorem B1927735 : Blo 1927435 1927735 := bstep (se 1 (by rfl) ⟨1445801, by rfl⟩ : syracuseStep 1927735 = 2891603) B2891603
theorem B3253061 : Blo 1927435 3253061 := bbase (se 4 (by rfl) ⟨304974, by rfl⟩ : syracuseStep 3253061 = 609949) (by norm_num)
theorem B2168707 : Blo 1927435 2168707 := bstep (se 1 (by rfl) ⟨1626530, by rfl⟩ : syracuseStep 2168707 = 3253061) B3253061
theorem B2891609 : Blo 1927435 2891609 := bstep (se 2 (by rfl) ⟨1084353, by rfl⟩ : syracuseStep 2891609 = 2168707) B2168707
theorem B1927739 : Blo 1927435 1927739 := bstep (se 1 (by rfl) ⟨1445804, by rfl⟩ : syracuseStep 1927739 = 2891609) B2891609
theorem B14638805 : Blo 1927435 14638805 := bbase (se 7 (by rfl) ⟨171548, by rfl⟩ : syracuseStep 14638805 = 343097) (by norm_num)
theorem B9759203 : Blo 1927435 9759203 := bstep (se 1 (by rfl) ⟨7319402, by rfl⟩ : syracuseStep 9759203 = 14638805) B14638805
theorem B6506135 : Blo 1927435 6506135 := bstep (se 1 (by rfl) ⟨4879601, by rfl⟩ : syracuseStep 6506135 = 9759203) B9759203
theorem B4337423 : Blo 1927435 4337423 := bstep (se 1 (by rfl) ⟨3253067, by rfl⟩ : syracuseStep 4337423 = 6506135) B6506135
theorem B2891615 : Blo 1927435 2891615 := bstep (se 1 (by rfl) ⟨2168711, by rfl⟩ : syracuseStep 2891615 = 4337423) B4337423
theorem B1927743 : Blo 1927435 1927743 := bstep (se 1 (by rfl) ⟨1445807, by rfl⟩ : syracuseStep 1927743 = 2891615) B2891615
theorem B2891621 : Blo 1927435 2891621 := bbase (se 4 (by rfl) ⟨271089, by rfl⟩ : syracuseStep 2891621 = 542179) (by norm_num)
theorem B1927747 : Blo 1927435 1927747 := bstep (se 1 (by rfl) ⟨1445810, by rfl⟩ : syracuseStep 1927747 = 2891621) B2891621
theorem B3659717 : Blo 1927435 3659717 := bbase (se 4 (by rfl) ⟨343098, by rfl⟩ : syracuseStep 3659717 = 686197) (by norm_num)
theorem B2439811 : Blo 1927435 2439811 := bstep (se 1 (by rfl) ⟨1829858, by rfl⟩ : syracuseStep 2439811 = 3659717) B3659717
theorem B3253081 : Blo 1927435 3253081 := bstep (se 2 (by rfl) ⟨1219905, by rfl⟩ : syracuseStep 3253081 = 2439811) B2439811
theorem B4337441 : Blo 1927435 4337441 := bstep (se 2 (by rfl) ⟨1626540, by rfl⟩ : syracuseStep 4337441 = 3253081) B3253081
theorem B2891627 : Blo 1927435 2891627 := bstep (se 1 (by rfl) ⟨2168720, by rfl⟩ : syracuseStep 2891627 = 4337441) B4337441
theorem B1927751 : Blo 1927435 1927751 := bstep (se 1 (by rfl) ⟨1445813, by rfl⟩ : syracuseStep 1927751 = 2891627) B2891627
theorem B2168725 : Blo 1927435 2168725 := bbase (se 6 (by rfl) ⟨50829, by rfl⟩ : syracuseStep 2168725 = 101659) (by norm_num)
theorem B2891633 : Blo 1927435 2891633 := bstep (se 2 (by rfl) ⟨1084362, by rfl⟩ : syracuseStep 2891633 = 2168725) B2168725
theorem B1927755 : Blo 1927435 1927755 := bstep (se 1 (by rfl) ⟨1445816, by rfl⟩ : syracuseStep 1927755 = 2891633) B2891633
theorem B2439821 : Blo 1927435 2439821 := bbase (se 3 (by rfl) ⟨457466, by rfl⟩ : syracuseStep 2439821 = 914933) (by norm_num)
theorem B6506189 : Blo 1927435 6506189 := bstep (se 3 (by rfl) ⟨1219910, by rfl⟩ : syracuseStep 6506189 = 2439821) B2439821
theorem B4337459 : Blo 1927435 4337459 := bstep (se 1 (by rfl) ⟨3253094, by rfl⟩ : syracuseStep 4337459 = 6506189) B6506189
theorem B2891639 : Blo 1927435 2891639 := bstep (se 1 (by rfl) ⟨2168729, by rfl⟩ : syracuseStep 2891639 = 4337459) B4337459
theorem B1927759 : Blo 1927435 1927759 := bstep (se 1 (by rfl) ⟨1445819, by rfl⟩ : syracuseStep 1927759 = 2891639) B2891639
theorem B2891645 : Blo 1927435 2891645 := bbase (se 3 (by rfl) ⟨542183, by rfl⟩ : syracuseStep 2891645 = 1084367) (by norm_num)
theorem B1927763 : Blo 1927435 1927763 := bstep (se 1 (by rfl) ⟨1445822, by rfl⟩ : syracuseStep 1927763 = 2891645) B2891645
theorem B4337477 : Blo 1927435 4337477 := bbase (se 4 (by rfl) ⟨406638, by rfl⟩ : syracuseStep 4337477 = 813277) (by norm_num)
theorem B2891651 : Blo 1927435 2891651 := bstep (se 1 (by rfl) ⟨2168738, by rfl⟩ : syracuseStep 2891651 = 4337477) B4337477
theorem B1927767 : Blo 1927435 1927767 := bstep (se 1 (by rfl) ⟨1445825, by rfl⟩ : syracuseStep 1927767 = 2891651) B2891651
theorem B5564533 : Blo 1927435 5564533 := bbase (se 5 (by rfl) ⟨260837, by rfl⟩ : syracuseStep 5564533 = 521675) (by norm_num)
theorem B7419377 : Blo 1927435 7419377 := bstep (se 2 (by rfl) ⟨2782266, by rfl⟩ : syracuseStep 7419377 = 5564533) B5564533
theorem B19785005 : Blo 1927435 19785005 := bstep (se 3 (by rfl) ⟨3709688, by rfl⟩ : syracuseStep 19785005 = 7419377) B7419377
theorem B13190003 : Blo 1927435 13190003 := bstep (se 1 (by rfl) ⟨9892502, by rfl⟩ : syracuseStep 13190003 = 19785005) B19785005
theorem B8793335 : Blo 1927435 8793335 := bstep (se 1 (by rfl) ⟨6595001, by rfl⟩ : syracuseStep 8793335 = 13190003) B13190003
theorem B5862223 : Blo 1927435 5862223 := bstep (se 1 (by rfl) ⟨4396667, by rfl⟩ : syracuseStep 5862223 = 8793335) B8793335
theorem B7816297 : Blo 1927435 7816297 := bstep (se 2 (by rfl) ⟨2931111, by rfl⟩ : syracuseStep 7816297 = 5862223) B5862223
theorem B10421729 : Blo 1927435 10421729 := bstep (se 2 (by rfl) ⟨3908148, by rfl⟩ : syracuseStep 10421729 = 7816297) B7816297
theorem B6947819 : Blo 1927435 6947819 := bstep (se 1 (by rfl) ⟨5210864, by rfl⟩ : syracuseStep 6947819 = 10421729) B10421729
theorem B4631879 : Blo 1927435 4631879 := bstep (se 1 (by rfl) ⟨3473909, by rfl⟩ : syracuseStep 4631879 = 6947819) B6947819
theorem B3087919 : Blo 1927435 3087919 := bstep (se 1 (by rfl) ⟨2315939, by rfl⟩ : syracuseStep 3087919 = 4631879) B4631879
theorem B4117225 : Blo 1927435 4117225 := bstep (se 2 (by rfl) ⟨1543959, by rfl⟩ : syracuseStep 4117225 = 3087919) B3087919
theorem B5489633 : Blo 1927435 5489633 := bstep (se 2 (by rfl) ⟨2058612, by rfl⟩ : syracuseStep 5489633 = 4117225) B4117225
theorem B3659755 : Blo 1927435 3659755 := bstep (se 1 (by rfl) ⟨2744816, by rfl⟩ : syracuseStep 3659755 = 5489633) B5489633
theorem B4879673 : Blo 1927435 4879673 := bstep (se 2 (by rfl) ⟨1829877, by rfl⟩ : syracuseStep 4879673 = 3659755) B3659755
theorem B3253115 : Blo 1927435 3253115 := bstep (se 1 (by rfl) ⟨2439836, by rfl⟩ : syracuseStep 3253115 = 4879673) B4879673
theorem B2168743 : Blo 1927435 2168743 := bstep (se 1 (by rfl) ⟨1626557, by rfl⟩ : syracuseStep 2168743 = 3253115) B3253115
theorem B2891657 : Blo 1927435 2891657 := bstep (se 2 (by rfl) ⟨1084371, by rfl⟩ : syracuseStep 2891657 = 2168743) B2168743
theorem B1927771 : Blo 1927435 1927771 := bstep (se 1 (by rfl) ⟨1445828, by rfl⟩ : syracuseStep 1927771 = 2891657) B2891657
theorem B9759365 : Blo 1927435 9759365 := bbase (se 4 (by rfl) ⟨914940, by rfl⟩ : syracuseStep 9759365 = 1829881) (by norm_num)
theorem B6506243 : Blo 1927435 6506243 := bstep (se 1 (by rfl) ⟨4879682, by rfl⟩ : syracuseStep 6506243 = 9759365) B9759365
theorem B4337495 : Blo 1927435 4337495 := bstep (se 1 (by rfl) ⟨3253121, by rfl⟩ : syracuseStep 4337495 = 6506243) B6506243
theorem B2891663 : Blo 1927435 2891663 := bstep (se 1 (by rfl) ⟨2168747, by rfl⟩ : syracuseStep 2891663 = 4337495) B4337495
theorem B1927775 : Blo 1927435 1927775 := bstep (se 1 (by rfl) ⟨1445831, by rfl⟩ : syracuseStep 1927775 = 2891663) B2891663
theorem B2891669 : Blo 1927435 2891669 := bbase (se 6 (by rfl) ⟨67773, by rfl⟩ : syracuseStep 2891669 = 135547) (by norm_num)
theorem B1927779 : Blo 1927435 1927779 := bstep (se 1 (by rfl) ⟨1445834, by rfl⟩ : syracuseStep 1927779 = 2891669) B2891669
theorem B2058625 : Blo 1927435 2058625 := bbase (se 2 (by rfl) ⟨771984, by rfl⟩ : syracuseStep 2058625 = 1543969) (by norm_num)
theorem B10979333 : Blo 1927435 10979333 := bstep (se 4 (by rfl) ⟨1029312, by rfl⟩ : syracuseStep 10979333 = 2058625) B2058625
theorem B7319555 : Blo 1927435 7319555 := bstep (se 1 (by rfl) ⟨5489666, by rfl⟩ : syracuseStep 7319555 = 10979333) B10979333
theorem B4879703 : Blo 1927435 4879703 := bstep (se 1 (by rfl) ⟨3659777, by rfl⟩ : syracuseStep 4879703 = 7319555) B7319555
theorem B3253135 : Blo 1927435 3253135 := bstep (se 1 (by rfl) ⟨2439851, by rfl⟩ : syracuseStep 3253135 = 4879703) B4879703
theorem B4337513 : Blo 1927435 4337513 := bstep (se 2 (by rfl) ⟨1626567, by rfl⟩ : syracuseStep 4337513 = 3253135) B3253135
theorem B2891675 : Blo 1927435 2891675 := bstep (se 1 (by rfl) ⟨2168756, by rfl⟩ : syracuseStep 2891675 = 4337513) B4337513
theorem B1927783 : Blo 1927435 1927783 := bstep (se 1 (by rfl) ⟨1445837, by rfl⟩ : syracuseStep 1927783 = 2891675) B2891675
theorem B2168761 : Blo 1927435 2168761 := bbase (se 2 (by rfl) ⟨813285, by rfl⟩ : syracuseStep 2168761 = 1626571) (by norm_num)
theorem B2891681 : Blo 1927435 2891681 := bstep (se 2 (by rfl) ⟨1084380, by rfl⟩ : syracuseStep 2891681 = 2168761) B2168761
theorem B1927787 : Blo 1927435 1927787 := bstep (se 1 (by rfl) ⟨1445840, by rfl⟩ : syracuseStep 1927787 = 2891681) B2891681
theorem B3908189 : Blo 1927435 3908189 := bbase (se 3 (by rfl) ⟨732785, by rfl⟩ : syracuseStep 3908189 = 1465571) (by norm_num)
theorem B2605459 : Blo 1927435 2605459 := bstep (se 1 (by rfl) ⟨1954094, by rfl⟩ : syracuseStep 2605459 = 3908189) B3908189
theorem B3473945 : Blo 1927435 3473945 := bstep (se 2 (by rfl) ⟨1302729, by rfl⟩ : syracuseStep 3473945 = 2605459) B2605459
theorem B2315963 : Blo 1927435 2315963 := bstep (se 1 (by rfl) ⟨1736972, by rfl⟩ : syracuseStep 2315963 = 3473945) B3473945
theorem B6175901 : Blo 1927435 6175901 := bstep (se 3 (by rfl) ⟨1157981, by rfl⟩ : syracuseStep 6175901 = 2315963) B2315963
theorem B4117267 : Blo 1927435 4117267 := bstep (se 1 (by rfl) ⟨3087950, by rfl⟩ : syracuseStep 4117267 = 6175901) B6175901
theorem B5489689 : Blo 1927435 5489689 := bstep (se 2 (by rfl) ⟨2058633, by rfl⟩ : syracuseStep 5489689 = 4117267) B4117267
theorem B7319585 : Blo 1927435 7319585 := bstep (se 2 (by rfl) ⟨2744844, by rfl⟩ : syracuseStep 7319585 = 5489689) B5489689
theorem B4879723 : Blo 1927435 4879723 := bstep (se 1 (by rfl) ⟨3659792, by rfl⟩ : syracuseStep 4879723 = 7319585) B7319585
theorem B6506297 : Blo 1927435 6506297 := bstep (se 2 (by rfl) ⟨2439861, by rfl⟩ : syracuseStep 6506297 = 4879723) B4879723
theorem B4337531 : Blo 1927435 4337531 := bstep (se 1 (by rfl) ⟨3253148, by rfl⟩ : syracuseStep 4337531 = 6506297) B6506297
theorem B2891687 : Blo 1927435 2891687 := bstep (se 1 (by rfl) ⟨2168765, by rfl⟩ : syracuseStep 2891687 = 4337531) B4337531
theorem B1927791 : Blo 1927435 1927791 := bstep (se 1 (by rfl) ⟨1445843, by rfl⟩ : syracuseStep 1927791 = 2891687) B2891687
theorem B2891693 : Blo 1927435 2891693 := bbase (se 3 (by rfl) ⟨542192, by rfl⟩ : syracuseStep 2891693 = 1084385) (by norm_num)
theorem B1927795 : Blo 1927435 1927795 := bstep (se 1 (by rfl) ⟨1445846, by rfl⟩ : syracuseStep 1927795 = 2891693) B2891693
theorem B4337549 : Blo 1927435 4337549 := bbase (se 3 (by rfl) ⟨813290, by rfl⟩ : syracuseStep 4337549 = 1626581) (by norm_num)
theorem B2891699 : Blo 1927435 2891699 := bstep (se 1 (by rfl) ⟨2168774, by rfl⟩ : syracuseStep 2891699 = 4337549) B4337549
theorem B1927799 : Blo 1927435 1927799 := bstep (se 1 (by rfl) ⟨1445849, by rfl⟩ : syracuseStep 1927799 = 2891699) B2891699
theorem B2439877 : Blo 1927435 2439877 := bbase (se 4 (by rfl) ⟨228738, by rfl⟩ : syracuseStep 2439877 = 457477) (by norm_num)
theorem B3253169 : Blo 1927435 3253169 := bstep (se 2 (by rfl) ⟨1219938, by rfl⟩ : syracuseStep 3253169 = 2439877) B2439877
theorem B2168779 : Blo 1927435 2168779 := bstep (se 1 (by rfl) ⟨1626584, by rfl⟩ : syracuseStep 2168779 = 3253169) B3253169
theorem B2891705 : Blo 1927435 2891705 := bstep (se 2 (by rfl) ⟨1084389, by rfl⟩ : syracuseStep 2891705 = 2168779) B2168779
theorem B1927803 : Blo 1927435 1927803 := bstep (se 1 (by rfl) ⟨1445852, by rfl⟩ : syracuseStep 1927803 = 2891705) B2891705
theorem B4946341 : Blo 1927435 4946341 := bbase (se 4 (by rfl) ⟨463719, by rfl⟩ : syracuseStep 4946341 = 927439) (by norm_num)
theorem B6595121 : Blo 1927435 6595121 := bstep (se 2 (by rfl) ⟨2473170, by rfl⟩ : syracuseStep 6595121 = 4946341) B4946341
theorem B17586989 : Blo 1927435 17586989 := bstep (se 3 (by rfl) ⟨3297560, by rfl⟩ : syracuseStep 17586989 = 6595121) B6595121
theorem B11724659 : Blo 1927435 11724659 := bstep (se 1 (by rfl) ⟨8793494, by rfl⟩ : syracuseStep 11724659 = 17586989) B17586989
theorem B7816439 : Blo 1927435 7816439 := bstep (se 1 (by rfl) ⟨5862329, by rfl⟩ : syracuseStep 7816439 = 11724659) B11724659
theorem B20843837 : Blo 1927435 20843837 := bstep (se 3 (by rfl) ⟨3908219, by rfl⟩ : syracuseStep 20843837 = 7816439) B7816439
theorem B13895891 : Blo 1927435 13895891 := bstep (se 1 (by rfl) ⟨10421918, by rfl⟩ : syracuseStep 13895891 = 20843837) B20843837
theorem B9263927 : Blo 1927435 9263927 := bstep (se 1 (by rfl) ⟨6947945, by rfl⟩ : syracuseStep 9263927 = 13895891) B13895891
theorem B24703805 : Blo 1927435 24703805 := bstep (se 3 (by rfl) ⟨4631963, by rfl⟩ : syracuseStep 24703805 = 9263927) B9263927
theorem B16469203 : Blo 1927435 16469203 := bstep (se 1 (by rfl) ⟨12351902, by rfl⟩ : syracuseStep 16469203 = 24703805) B24703805
theorem B21958937 : Blo 1927435 21958937 := bstep (se 2 (by rfl) ⟨8234601, by rfl⟩ : syracuseStep 21958937 = 16469203) B16469203
theorem B14639291 : Blo 1927435 14639291 := bstep (se 1 (by rfl) ⟨10979468, by rfl⟩ : syracuseStep 14639291 = 21958937) B21958937
theorem B9759527 : Blo 1927435 9759527 := bstep (se 1 (by rfl) ⟨7319645, by rfl⟩ : syracuseStep 9759527 = 14639291) B14639291
theorem B6506351 : Blo 1927435 6506351 := bstep (se 1 (by rfl) ⟨4879763, by rfl⟩ : syracuseStep 6506351 = 9759527) B9759527
theorem B4337567 : Blo 1927435 4337567 := bstep (se 1 (by rfl) ⟨3253175, by rfl⟩ : syracuseStep 4337567 = 6506351) B6506351
theorem B2891711 : Blo 1927435 2891711 := bstep (se 1 (by rfl) ⟨2168783, by rfl⟩ : syracuseStep 2891711 = 4337567) B4337567
theorem B1927807 : Blo 1927435 1927807 := bstep (se 1 (by rfl) ⟨1445855, by rfl⟩ : syracuseStep 1927807 = 2891711) B2891711
theorem B2891717 : Blo 1927435 2891717 := bbase (se 4 (by rfl) ⟨271098, by rfl⟩ : syracuseStep 2891717 = 542197) (by norm_num)
theorem B1927811 : Blo 1927435 1927811 := bstep (se 1 (by rfl) ⟨1445858, by rfl⟩ : syracuseStep 1927811 = 2891717) B2891717
theorem B3253189 : Blo 1927435 3253189 := bbase (se 4 (by rfl) ⟨304986, by rfl⟩ : syracuseStep 3253189 = 609973) (by norm_num)
theorem B4337585 : Blo 1927435 4337585 := bstep (se 2 (by rfl) ⟨1626594, by rfl⟩ : syracuseStep 4337585 = 3253189) B3253189
theorem B2891723 : Blo 1927435 2891723 := bstep (se 1 (by rfl) ⟨2168792, by rfl⟩ : syracuseStep 2891723 = 4337585) B4337585
theorem B1927815 : Blo 1927435 1927815 := bstep (se 1 (by rfl) ⟨1445861, by rfl⟩ : syracuseStep 1927815 = 2891723) B2891723
theorem B2168797 : Blo 1927435 2168797 := bbase (se 3 (by rfl) ⟨406649, by rfl⟩ : syracuseStep 2168797 = 813299) (by norm_num)
theorem B2891729 : Blo 1927435 2891729 := bstep (se 2 (by rfl) ⟨1084398, by rfl⟩ : syracuseStep 2891729 = 2168797) B2168797
theorem B1927819 : Blo 1927435 1927819 := bstep (se 1 (by rfl) ⟨1445864, by rfl⟩ : syracuseStep 1927819 = 2891729) B2891729
theorem B6506405 : Blo 1927435 6506405 := bbase (se 4 (by rfl) ⟨609975, by rfl⟩ : syracuseStep 6506405 = 1219951) (by norm_num)
theorem B4337603 : Blo 1927435 4337603 := bstep (se 1 (by rfl) ⟨3253202, by rfl⟩ : syracuseStep 4337603 = 6506405) B6506405
theorem B2891735 : Blo 1927435 2891735 := bstep (se 1 (by rfl) ⟨2168801, by rfl⟩ : syracuseStep 2891735 = 4337603) B4337603
theorem B1927823 : Blo 1927435 1927823 := bstep (se 1 (by rfl) ⟨1445867, by rfl⟩ : syracuseStep 1927823 = 2891735) B2891735
theorem B2891741 : Blo 1927435 2891741 := bbase (se 3 (by rfl) ⟨542201, by rfl⟩ : syracuseStep 2891741 = 1084403) (by norm_num)
theorem B1927827 : Blo 1927435 1927827 := bstep (se 1 (by rfl) ⟨1445870, by rfl⟩ : syracuseStep 1927827 = 2891741) B2891741
theorem B4337621 : Blo 1927435 4337621 := bbase (se 7 (by rfl) ⟨50831, by rfl⟩ : syracuseStep 4337621 = 101663) (by norm_num)
theorem B2891747 : Blo 1927435 2891747 := bstep (se 1 (by rfl) ⟨2168810, by rfl⟩ : syracuseStep 2891747 = 4337621) B4337621
theorem B1927831 : Blo 1927435 1927831 := bstep (se 1 (by rfl) ⟨1445873, by rfl⟩ : syracuseStep 1927831 = 2891747) B2891747
theorem B12352085 : Blo 1927435 12352085 := bbase (se 8 (by rfl) ⟨72375, by rfl⟩ : syracuseStep 12352085 = 144751) (by norm_num)
theorem B8234723 : Blo 1927435 8234723 := bstep (se 1 (by rfl) ⟨6176042, by rfl⟩ : syracuseStep 8234723 = 12352085) B12352085
theorem B5489815 : Blo 1927435 5489815 := bstep (se 1 (by rfl) ⟨4117361, by rfl⟩ : syracuseStep 5489815 = 8234723) B8234723
theorem B7319753 : Blo 1927435 7319753 := bstep (se 2 (by rfl) ⟨2744907, by rfl⟩ : syracuseStep 7319753 = 5489815) B5489815
theorem B4879835 : Blo 1927435 4879835 := bstep (se 1 (by rfl) ⟨3659876, by rfl⟩ : syracuseStep 4879835 = 7319753) B7319753
theorem B3253223 : Blo 1927435 3253223 := bstep (se 1 (by rfl) ⟨2439917, by rfl⟩ : syracuseStep 3253223 = 4879835) B4879835
theorem B2168815 : Blo 1927435 2168815 := bstep (se 1 (by rfl) ⟨1626611, by rfl⟩ : syracuseStep 2168815 = 3253223) B3253223
theorem B2891753 : Blo 1927435 2891753 := bstep (se 2 (by rfl) ⟨1084407, by rfl⟩ : syracuseStep 2891753 = 2168815) B2168815
theorem B1927835 : Blo 1927435 1927835 := bstep (se 1 (by rfl) ⟨1445876, by rfl⟩ : syracuseStep 1927835 = 2891753) B2891753
theorem B7419637 : Blo 1927435 7419637 := bbase (se 5 (by rfl) ⟨347795, by rfl⟩ : syracuseStep 7419637 = 695591) (by norm_num)
theorem B9892849 : Blo 1927435 9892849 := bstep (se 2 (by rfl) ⟨3709818, by rfl⟩ : syracuseStep 9892849 = 7419637) B7419637
theorem B13190465 : Blo 1927435 13190465 := bstep (se 2 (by rfl) ⟨4946424, by rfl⟩ : syracuseStep 13190465 = 9892849) B9892849
theorem B8793643 : Blo 1927435 8793643 := bstep (se 1 (by rfl) ⟨6595232, by rfl⟩ : syracuseStep 8793643 = 13190465) B13190465
theorem B11724857 : Blo 1927435 11724857 := bstep (se 2 (by rfl) ⟨4396821, by rfl⟩ : syracuseStep 11724857 = 8793643) B8793643
theorem B7816571 : Blo 1927435 7816571 := bstep (se 1 (by rfl) ⟨5862428, by rfl⟩ : syracuseStep 7816571 = 11724857) B11724857
theorem B5211047 : Blo 1927435 5211047 := bstep (se 1 (by rfl) ⟨3908285, by rfl⟩ : syracuseStep 5211047 = 7816571) B7816571
theorem B3474031 : Blo 1927435 3474031 := bstep (se 1 (by rfl) ⟨2605523, by rfl⟩ : syracuseStep 3474031 = 5211047) B5211047
theorem B4632041 : Blo 1927435 4632041 := bstep (se 2 (by rfl) ⟨1737015, by rfl⟩ : syracuseStep 4632041 = 3474031) B3474031
theorem B3088027 : Blo 1927435 3088027 := bstep (se 1 (by rfl) ⟨2316020, by rfl⟩ : syracuseStep 3088027 = 4632041) B4632041
theorem B16469477 : Blo 1927435 16469477 := bstep (se 4 (by rfl) ⟨1544013, by rfl⟩ : syracuseStep 16469477 = 3088027) B3088027
theorem B10979651 : Blo 1927435 10979651 := bstep (se 1 (by rfl) ⟨8234738, by rfl⟩ : syracuseStep 10979651 = 16469477) B16469477
theorem B7319767 : Blo 1927435 7319767 := bstep (se 1 (by rfl) ⟨5489825, by rfl⟩ : syracuseStep 7319767 = 10979651) B10979651
theorem B9759689 : Blo 1927435 9759689 := bstep (se 2 (by rfl) ⟨3659883, by rfl⟩ : syracuseStep 9759689 = 7319767) B7319767
theorem B6506459 : Blo 1927435 6506459 := bstep (se 1 (by rfl) ⟨4879844, by rfl⟩ : syracuseStep 6506459 = 9759689) B9759689
theorem B4337639 : Blo 1927435 4337639 := bstep (se 1 (by rfl) ⟨3253229, by rfl⟩ : syracuseStep 4337639 = 6506459) B6506459
theorem B2891759 : Blo 1927435 2891759 := bstep (se 1 (by rfl) ⟨2168819, by rfl⟩ : syracuseStep 2891759 = 4337639) B4337639
theorem B1927839 : Blo 1927435 1927839 := bstep (se 1 (by rfl) ⟨1445879, by rfl⟩ : syracuseStep 1927839 = 2891759) B2891759
theorem B2891765 : Blo 1927435 2891765 := bbase (se 5 (by rfl) ⟨135551, by rfl⟩ : syracuseStep 2891765 = 271103) (by norm_num)
theorem B1927843 : Blo 1927435 1927843 := bstep (se 1 (by rfl) ⟨1445882, by rfl⟩ : syracuseStep 1927843 = 2891765) B2891765
theorem B4632061 : Blo 1927435 4632061 := bbase (se 3 (by rfl) ⟨868511, by rfl⟩ : syracuseStep 4632061 = 1737023) (by norm_num)
theorem B6176081 : Blo 1927435 6176081 := bstep (se 2 (by rfl) ⟨2316030, by rfl⟩ : syracuseStep 6176081 = 4632061) B4632061
theorem B4117387 : Blo 1927435 4117387 := bstep (se 1 (by rfl) ⟨3088040, by rfl⟩ : syracuseStep 4117387 = 6176081) B6176081
theorem B5489849 : Blo 1927435 5489849 := bstep (se 2 (by rfl) ⟨2058693, by rfl⟩ : syracuseStep 5489849 = 4117387) B4117387
theorem B3659899 : Blo 1927435 3659899 := bstep (se 1 (by rfl) ⟨2744924, by rfl⟩ : syracuseStep 3659899 = 5489849) B5489849
theorem B4879865 : Blo 1927435 4879865 := bstep (se 2 (by rfl) ⟨1829949, by rfl⟩ : syracuseStep 4879865 = 3659899) B3659899
theorem B3253243 : Blo 1927435 3253243 := bstep (se 1 (by rfl) ⟨2439932, by rfl⟩ : syracuseStep 3253243 = 4879865) B4879865
theorem B4337657 : Blo 1927435 4337657 := bstep (se 2 (by rfl) ⟨1626621, by rfl⟩ : syracuseStep 4337657 = 3253243) B3253243
theorem B2891771 : Blo 1927435 2891771 := bstep (se 1 (by rfl) ⟨2168828, by rfl⟩ : syracuseStep 2891771 = 4337657) B4337657
theorem B1927847 : Blo 1927435 1927847 := bstep (se 1 (by rfl) ⟨1445885, by rfl⟩ : syracuseStep 1927847 = 2891771) B2891771
theorem B2168833 : Blo 1927435 2168833 := bbase (se 2 (by rfl) ⟨813312, by rfl⟩ : syracuseStep 2168833 = 1626625) (by norm_num)
theorem B2891777 : Blo 1927435 2891777 := bstep (se 2 (by rfl) ⟨1084416, by rfl⟩ : syracuseStep 2891777 = 2168833) B2168833
theorem B1927851 : Blo 1927435 1927851 := bstep (se 1 (by rfl) ⟨1445888, by rfl⟩ : syracuseStep 1927851 = 2891777) B2891777
theorem B4879885 : Blo 1927435 4879885 := bbase (se 3 (by rfl) ⟨914978, by rfl⟩ : syracuseStep 4879885 = 1829957) (by norm_num)
theorem B6506513 : Blo 1927435 6506513 := bstep (se 2 (by rfl) ⟨2439942, by rfl⟩ : syracuseStep 6506513 = 4879885) B4879885
theorem B4337675 : Blo 1927435 4337675 := bstep (se 1 (by rfl) ⟨3253256, by rfl⟩ : syracuseStep 4337675 = 6506513) B6506513
theorem B2891783 : Blo 1927435 2891783 := bstep (se 1 (by rfl) ⟨2168837, by rfl⟩ : syracuseStep 2891783 = 4337675) B4337675
theorem B1927855 : Blo 1927435 1927855 := bstep (se 1 (by rfl) ⟨1445891, by rfl⟩ : syracuseStep 1927855 = 2891783) B2891783
theorem B2891789 : Blo 1927435 2891789 := bbase (se 3 (by rfl) ⟨542210, by rfl⟩ : syracuseStep 2891789 = 1084421) (by norm_num)
theorem B1927859 : Blo 1927435 1927859 := bstep (se 1 (by rfl) ⟨1445894, by rfl⟩ : syracuseStep 1927859 = 2891789) B2891789
theorem B4337693 : Blo 1927435 4337693 := bbase (se 3 (by rfl) ⟨813317, by rfl⟩ : syracuseStep 4337693 = 1626635) (by norm_num)
theorem B2891795 : Blo 1927435 2891795 := bstep (se 1 (by rfl) ⟨2168846, by rfl⟩ : syracuseStep 2891795 = 4337693) B4337693
theorem B1927863 : Blo 1927435 1927863 := bstep (se 1 (by rfl) ⟨1445897, by rfl⟩ : syracuseStep 1927863 = 2891795) B2891795
theorem B3253277 : Blo 1927435 3253277 := bbase (se 3 (by rfl) ⟨609989, by rfl⟩ : syracuseStep 3253277 = 1219979) (by norm_num)
theorem B2168851 : Blo 1927435 2168851 := bstep (se 1 (by rfl) ⟨1626638, by rfl⟩ : syracuseStep 2168851 = 3253277) B3253277
theorem B2891801 : Blo 1927435 2891801 := bstep (se 2 (by rfl) ⟨1084425, by rfl⟩ : syracuseStep 2891801 = 2168851) B2168851
theorem B1927867 : Blo 1927435 1927867 := bstep (se 1 (by rfl) ⟨1445900, by rfl⟩ : syracuseStep 1927867 = 2891801) B2891801
theorem B4695317 : Blo 1927435 4695317 := bbase (se 6 (by rfl) ⟨110046, by rfl⟩ : syracuseStep 4695317 = 220093) (by norm_num)
theorem B3130211 : Blo 1927435 3130211 := bstep (se 1 (by rfl) ⟨2347658, by rfl⟩ : syracuseStep 3130211 = 4695317) B4695317
theorem B8347229 : Blo 1927435 8347229 := bstep (se 3 (by rfl) ⟨1565105, by rfl⟩ : syracuseStep 8347229 = 3130211) B3130211
theorem B5564819 : Blo 1927435 5564819 := bstep (se 1 (by rfl) ⟨4173614, by rfl⟩ : syracuseStep 5564819 = 8347229) B8347229
theorem B14839517 : Blo 1927435 14839517 := bstep (se 3 (by rfl) ⟨2782409, by rfl⟩ : syracuseStep 14839517 = 5564819) B5564819
theorem B9893011 : Blo 1927435 9893011 := bstep (se 1 (by rfl) ⟨7419758, by rfl⟩ : syracuseStep 9893011 = 14839517) B14839517
theorem B13190681 : Blo 1927435 13190681 := bstep (se 2 (by rfl) ⟨4946505, by rfl⟩ : syracuseStep 13190681 = 9893011) B9893011
theorem B8793787 : Blo 1927435 8793787 := bstep (se 1 (by rfl) ⟨6595340, by rfl⟩ : syracuseStep 8793787 = 13190681) B13190681
theorem B11725049 : Blo 1927435 11725049 := bstep (se 2 (by rfl) ⟨4396893, by rfl⟩ : syracuseStep 11725049 = 8793787) B8793787
theorem B7816699 : Blo 1927435 7816699 := bstep (se 1 (by rfl) ⟨5862524, by rfl⟩ : syracuseStep 7816699 = 11725049) B11725049
theorem B10422265 : Blo 1927435 10422265 := bstep (se 2 (by rfl) ⟨3908349, by rfl⟩ : syracuseStep 10422265 = 7816699) B7816699
theorem B13896353 : Blo 1927435 13896353 := bstep (se 2 (by rfl) ⟨5211132, by rfl⟩ : syracuseStep 13896353 = 10422265) B10422265
theorem B9264235 : Blo 1927435 9264235 := bstep (se 1 (by rfl) ⟨6948176, by rfl⟩ : syracuseStep 9264235 = 13896353) B13896353
theorem B12352313 : Blo 1927435 12352313 := bstep (se 2 (by rfl) ⟨4632117, by rfl⟩ : syracuseStep 12352313 = 9264235) B9264235
theorem B8234875 : Blo 1927435 8234875 := bstep (se 1 (by rfl) ⟨6176156, by rfl⟩ : syracuseStep 8234875 = 12352313) B12352313
theorem B10979833 : Blo 1927435 10979833 := bstep (se 2 (by rfl) ⟨4117437, by rfl⟩ : syracuseStep 10979833 = 8234875) B8234875
theorem B14639777 : Blo 1927435 14639777 := bstep (se 2 (by rfl) ⟨5489916, by rfl⟩ : syracuseStep 14639777 = 10979833) B10979833
theorem B9759851 : Blo 1927435 9759851 := bstep (se 1 (by rfl) ⟨7319888, by rfl⟩ : syracuseStep 9759851 = 14639777) B14639777
theorem B6506567 : Blo 1927435 6506567 := bstep (se 1 (by rfl) ⟨4879925, by rfl⟩ : syracuseStep 6506567 = 9759851) B9759851
theorem B4337711 : Blo 1927435 4337711 := bstep (se 1 (by rfl) ⟨3253283, by rfl⟩ : syracuseStep 4337711 = 6506567) B6506567
theorem B2891807 : Blo 1927435 2891807 := bstep (se 1 (by rfl) ⟨2168855, by rfl⟩ : syracuseStep 2891807 = 4337711) B4337711
theorem B1927871 : Blo 1927435 1927871 := bstep (se 1 (by rfl) ⟨1445903, by rfl⟩ : syracuseStep 1927871 = 2891807) B2891807
theorem B2891813 : Blo 1927435 2891813 := bbase (se 4 (by rfl) ⟨271107, by rfl⟩ : syracuseStep 2891813 = 542215) (by norm_num)
theorem B1927875 : Blo 1927435 1927875 := bstep (se 1 (by rfl) ⟨1445906, by rfl⟩ : syracuseStep 1927875 = 2891813) B2891813
theorem B2439973 : Blo 1927435 2439973 := bbase (se 4 (by rfl) ⟨228747, by rfl⟩ : syracuseStep 2439973 = 457495) (by norm_num)
theorem B3253297 : Blo 1927435 3253297 := bstep (se 2 (by rfl) ⟨1219986, by rfl⟩ : syracuseStep 3253297 = 2439973) B2439973
theorem B4337729 : Blo 1927435 4337729 := bstep (se 2 (by rfl) ⟨1626648, by rfl⟩ : syracuseStep 4337729 = 3253297) B3253297
theorem B2891819 : Blo 1927435 2891819 := bstep (se 1 (by rfl) ⟨2168864, by rfl⟩ : syracuseStep 2891819 = 4337729) B4337729
theorem B1927879 : Blo 1927435 1927879 := bstep (se 1 (by rfl) ⟨1445909, by rfl⟩ : syracuseStep 1927879 = 2891819) B2891819
theorem B2168869 : Blo 1927435 2168869 := bbase (se 4 (by rfl) ⟨203331, by rfl⟩ : syracuseStep 2168869 = 406663) (by norm_num)
theorem B2891825 : Blo 1927435 2891825 := bstep (se 2 (by rfl) ⟨1084434, by rfl⟩ : syracuseStep 2891825 = 2168869) B2168869
theorem B1927883 : Blo 1927435 1927883 := bstep (se 1 (by rfl) ⟨1445912, by rfl⟩ : syracuseStep 1927883 = 2891825) B2891825
theorem B4632157 : Blo 1927435 4632157 := bbase (se 3 (by rfl) ⟨868529, by rfl⟩ : syracuseStep 4632157 = 1737059) (by norm_num)
theorem B6176209 : Blo 1927435 6176209 := bstep (se 2 (by rfl) ⟨2316078, by rfl⟩ : syracuseStep 6176209 = 4632157) B4632157
theorem B8234945 : Blo 1927435 8234945 := bstep (se 2 (by rfl) ⟨3088104, by rfl⟩ : syracuseStep 8234945 = 6176209) B6176209
theorem B5489963 : Blo 1927435 5489963 := bstep (se 1 (by rfl) ⟨4117472, by rfl⟩ : syracuseStep 5489963 = 8234945) B8234945
theorem B3659975 : Blo 1927435 3659975 := bstep (se 1 (by rfl) ⟨2744981, by rfl⟩ : syracuseStep 3659975 = 5489963) B5489963
theorem B2439983 : Blo 1927435 2439983 := bstep (se 1 (by rfl) ⟨1829987, by rfl⟩ : syracuseStep 2439983 = 3659975) B3659975
theorem B6506621 : Blo 1927435 6506621 := bstep (se 3 (by rfl) ⟨1219991, by rfl⟩ : syracuseStep 6506621 = 2439983) B2439983
theorem B4337747 : Blo 1927435 4337747 := bstep (se 1 (by rfl) ⟨3253310, by rfl⟩ : syracuseStep 4337747 = 6506621) B6506621
theorem B2891831 : Blo 1927435 2891831 := bstep (se 1 (by rfl) ⟨2168873, by rfl⟩ : syracuseStep 2891831 = 4337747) B4337747
theorem B1927887 : Blo 1927435 1927887 := bstep (se 1 (by rfl) ⟨1445915, by rfl⟩ : syracuseStep 1927887 = 2891831) B2891831
theorem B2891837 : Blo 1927435 2891837 := bbase (se 3 (by rfl) ⟨542219, by rfl⟩ : syracuseStep 2891837 = 1084439) (by norm_num)
theorem B1927891 : Blo 1927435 1927891 := bstep (se 1 (by rfl) ⟨1445918, by rfl⟩ : syracuseStep 1927891 = 2891837) B2891837
theorem B4337765 : Blo 1927435 4337765 := bbase (se 4 (by rfl) ⟨406665, by rfl⟩ : syracuseStep 4337765 = 813331) (by norm_num)
theorem B2891843 : Blo 1927435 2891843 := bstep (se 1 (by rfl) ⟨2168882, by rfl⟩ : syracuseStep 2891843 = 4337765) B4337765
theorem B1927895 : Blo 1927435 1927895 := bstep (se 1 (by rfl) ⟨1445921, by rfl⟩ : syracuseStep 1927895 = 2891843) B2891843
theorem B4879997 : Blo 1927435 4879997 := bbase (se 3 (by rfl) ⟨914999, by rfl⟩ : syracuseStep 4879997 = 1829999) (by norm_num)
theorem B3253331 : Blo 1927435 3253331 := bstep (se 1 (by rfl) ⟨2439998, by rfl⟩ : syracuseStep 3253331 = 4879997) B4879997
theorem B2168887 : Blo 1927435 2168887 := bstep (se 1 (by rfl) ⟨1626665, by rfl⟩ : syracuseStep 2168887 = 3253331) B3253331
theorem B2891849 : Blo 1927435 2891849 := bstep (se 2 (by rfl) ⟨1084443, by rfl⟩ : syracuseStep 2891849 = 2168887) B2168887
theorem B1927899 : Blo 1927435 1927899 := bstep (se 1 (by rfl) ⟨1445924, by rfl⟩ : syracuseStep 1927899 = 2891849) B2891849
theorem B3660005 : Blo 1927435 3660005 := bbase (se 4 (by rfl) ⟨343125, by rfl⟩ : syracuseStep 3660005 = 686251) (by norm_num)
theorem B9760013 : Blo 1927435 9760013 := bstep (se 3 (by rfl) ⟨1830002, by rfl⟩ : syracuseStep 9760013 = 3660005) B3660005
theorem B6506675 : Blo 1927435 6506675 := bstep (se 1 (by rfl) ⟨4880006, by rfl⟩ : syracuseStep 6506675 = 9760013) B9760013
theorem B4337783 : Blo 1927435 4337783 := bstep (se 1 (by rfl) ⟨3253337, by rfl⟩ : syracuseStep 4337783 = 6506675) B6506675
theorem B2891855 : Blo 1927435 2891855 := bstep (se 1 (by rfl) ⟨2168891, by rfl⟩ : syracuseStep 2891855 = 4337783) B4337783
theorem B1927903 : Blo 1927435 1927903 := bstep (se 1 (by rfl) ⟨1445927, by rfl⟩ : syracuseStep 1927903 = 2891855) B2891855
theorem B2891861 : Blo 1927435 2891861 := bbase (se 8 (by rfl) ⟨16944, by rfl⟩ : syracuseStep 2891861 = 33889) (by norm_num)
theorem B1927907 : Blo 1927435 1927907 := bstep (se 1 (by rfl) ⟨1445930, by rfl⟩ : syracuseStep 1927907 = 2891861) B2891861
theorem B3709957 : Blo 1927435 3709957 := bbase (se 4 (by rfl) ⟨347808, by rfl⟩ : syracuseStep 3709957 = 695617) (by norm_num)
theorem B4946609 : Blo 1927435 4946609 := bstep (se 2 (by rfl) ⟨1854978, by rfl⟩ : syracuseStep 4946609 = 3709957) B3709957
theorem B13190957 : Blo 1927435 13190957 := bstep (se 3 (by rfl) ⟨2473304, by rfl⟩ : syracuseStep 13190957 = 4946609) B4946609
theorem B8793971 : Blo 1927435 8793971 := bstep (se 1 (by rfl) ⟨6595478, by rfl⟩ : syracuseStep 8793971 = 13190957) B13190957
theorem B5862647 : Blo 1927435 5862647 := bstep (se 1 (by rfl) ⟨4396985, by rfl⟩ : syracuseStep 5862647 = 8793971) B8793971
theorem B3908431 : Blo 1927435 3908431 := bstep (se 1 (by rfl) ⟨2931323, by rfl⟩ : syracuseStep 3908431 = 5862647) B5862647
theorem B20844965 : Blo 1927435 20844965 := bstep (se 4 (by rfl) ⟨1954215, by rfl⟩ : syracuseStep 20844965 = 3908431) B3908431
theorem B13896643 : Blo 1927435 13896643 := bstep (se 1 (by rfl) ⟨10422482, by rfl⟩ : syracuseStep 13896643 = 20844965) B20844965
theorem B18528857 : Blo 1927435 18528857 := bstep (se 2 (by rfl) ⟨6948321, by rfl⟩ : syracuseStep 18528857 = 13896643) B13896643
theorem B12352571 : Blo 1927435 12352571 := bstep (se 1 (by rfl) ⟨9264428, by rfl⟩ : syracuseStep 12352571 = 18528857) B18528857
theorem B8235047 : Blo 1927435 8235047 := bstep (se 1 (by rfl) ⟨6176285, by rfl⟩ : syracuseStep 8235047 = 12352571) B12352571
theorem B5490031 : Blo 1927435 5490031 := bstep (se 1 (by rfl) ⟨4117523, by rfl⟩ : syracuseStep 5490031 = 8235047) B8235047
theorem B7320041 : Blo 1927435 7320041 := bstep (se 2 (by rfl) ⟨2745015, by rfl⟩ : syracuseStep 7320041 = 5490031) B5490031
theorem B4880027 : Blo 1927435 4880027 := bstep (se 1 (by rfl) ⟨3660020, by rfl⟩ : syracuseStep 4880027 = 7320041) B7320041
theorem B3253351 : Blo 1927435 3253351 := bstep (se 1 (by rfl) ⟨2440013, by rfl⟩ : syracuseStep 3253351 = 4880027) B4880027
theorem B4337801 : Blo 1927435 4337801 := bstep (se 2 (by rfl) ⟨1626675, by rfl⟩ : syracuseStep 4337801 = 3253351) B3253351
theorem B2891867 : Blo 1927435 2891867 := bstep (se 1 (by rfl) ⟨2168900, by rfl⟩ : syracuseStep 2891867 = 4337801) B4337801
theorem B1927911 : Blo 1927435 1927911 := bstep (se 1 (by rfl) ⟨1445933, by rfl⟩ : syracuseStep 1927911 = 2891867) B2891867
theorem B2168905 : Blo 1927435 2168905 := bbase (se 2 (by rfl) ⟨813339, by rfl⟩ : syracuseStep 2168905 = 1626679) (by norm_num)
theorem B2891873 : Blo 1927435 2891873 := bstep (se 2 (by rfl) ⟨1084452, by rfl⟩ : syracuseStep 2891873 = 2168905) B2168905
theorem B1927915 : Blo 1927435 1927915 := bstep (se 1 (by rfl) ⟨1445936, by rfl⟩ : syracuseStep 1927915 = 2891873) B2891873
theorem B2347717 : Blo 1927435 2347717 := bbase (se 4 (by rfl) ⟨220098, by rfl⟩ : syracuseStep 2347717 = 440197) (by norm_num)
theorem B3130289 : Blo 1927435 3130289 := bstep (se 2 (by rfl) ⟨1173858, by rfl⟩ : syracuseStep 3130289 = 2347717) B2347717
theorem B33389749 : Blo 1927435 33389749 := bstep (se 5 (by rfl) ⟨1565144, by rfl⟩ : syracuseStep 33389749 = 3130289) B3130289
theorem B44519665 : Blo 1927435 44519665 := bstep (se 2 (by rfl) ⟨16694874, by rfl⟩ : syracuseStep 44519665 = 33389749) B33389749
theorem B59359553 : Blo 1927435 59359553 := bstep (se 2 (by rfl) ⟨22259832, by rfl⟩ : syracuseStep 59359553 = 44519665) B44519665
theorem B39573035 : Blo 1927435 39573035 := bstep (se 1 (by rfl) ⟨29679776, by rfl⟩ : syracuseStep 39573035 = 59359553) B59359553
theorem B26382023 : Blo 1927435 26382023 := bstep (se 1 (by rfl) ⟨19786517, by rfl⟩ : syracuseStep 26382023 = 39573035) B39573035
theorem B17588015 : Blo 1927435 17588015 := bstep (se 1 (by rfl) ⟨13191011, by rfl⟩ : syracuseStep 17588015 = 26382023) B26382023
theorem B11725343 : Blo 1927435 11725343 := bstep (se 1 (by rfl) ⟨8794007, by rfl⟩ : syracuseStep 11725343 = 17588015) B17588015
theorem B7816895 : Blo 1927435 7816895 := bstep (se 1 (by rfl) ⟨5862671, by rfl⟩ : syracuseStep 7816895 = 11725343) B11725343
theorem B5211263 : Blo 1927435 5211263 := bstep (se 1 (by rfl) ⟨3908447, by rfl⟩ : syracuseStep 5211263 = 7816895) B7816895
theorem B3474175 : Blo 1927435 3474175 := bstep (se 1 (by rfl) ⟨2605631, by rfl⟩ : syracuseStep 3474175 = 5211263) B5211263
theorem B4632233 : Blo 1927435 4632233 := bstep (se 2 (by rfl) ⟨1737087, by rfl⟩ : syracuseStep 4632233 = 3474175) B3474175
theorem B12352621 : Blo 1927435 12352621 := bstep (se 3 (by rfl) ⟨2316116, by rfl⟩ : syracuseStep 12352621 = 4632233) B4632233
theorem B16470161 : Blo 1927435 16470161 := bstep (se 2 (by rfl) ⟨6176310, by rfl⟩ : syracuseStep 16470161 = 12352621) B12352621
theorem B10980107 : Blo 1927435 10980107 := bstep (se 1 (by rfl) ⟨8235080, by rfl⟩ : syracuseStep 10980107 = 16470161) B16470161
theorem B7320071 : Blo 1927435 7320071 := bstep (se 1 (by rfl) ⟨5490053, by rfl⟩ : syracuseStep 7320071 = 10980107) B10980107
theorem B4880047 : Blo 1927435 4880047 := bstep (se 1 (by rfl) ⟨3660035, by rfl⟩ : syracuseStep 4880047 = 7320071) B7320071
theorem B6506729 : Blo 1927435 6506729 := bstep (se 2 (by rfl) ⟨2440023, by rfl⟩ : syracuseStep 6506729 = 4880047) B4880047
theorem B4337819 : Blo 1927435 4337819 := bstep (se 1 (by rfl) ⟨3253364, by rfl⟩ : syracuseStep 4337819 = 6506729) B6506729
theorem B2891879 : Blo 1927435 2891879 := bstep (se 1 (by rfl) ⟨2168909, by rfl⟩ : syracuseStep 2891879 = 4337819) B4337819
theorem B1927919 : Blo 1927435 1927919 := bstep (se 1 (by rfl) ⟨1445939, by rfl⟩ : syracuseStep 1927919 = 2891879) B2891879
theorem B2891885 : Blo 1927435 2891885 := bbase (se 3 (by rfl) ⟨542228, by rfl⟩ : syracuseStep 2891885 = 1084457) (by norm_num)
theorem B1927923 : Blo 1927435 1927923 := bstep (se 1 (by rfl) ⟨1445942, by rfl⟩ : syracuseStep 1927923 = 2891885) B2891885
theorem B4337837 : Blo 1927435 4337837 := bbase (se 3 (by rfl) ⟨813344, by rfl⟩ : syracuseStep 4337837 = 1626689) (by norm_num)
theorem B2891891 : Blo 1927435 2891891 := bstep (se 1 (by rfl) ⟨2168918, by rfl⟩ : syracuseStep 2891891 = 4337837) B4337837
theorem B1927927 : Blo 1927435 1927927 := bstep (se 1 (by rfl) ⟨1445945, by rfl⟩ : syracuseStep 1927927 = 2891891) B2891891
theorem B5862709 : Blo 1927435 5862709 := bbase (se 5 (by rfl) ⟨274814, by rfl⟩ : syracuseStep 5862709 = 549629) (by norm_num)
theorem B31267781 : Blo 1927435 31267781 := bstep (se 4 (by rfl) ⟨2931354, by rfl⟩ : syracuseStep 31267781 = 5862709) B5862709
theorem B20845187 : Blo 1927435 20845187 := bstep (se 1 (by rfl) ⟨15633890, by rfl⟩ : syracuseStep 20845187 = 31267781) B31267781
theorem B13896791 : Blo 1927435 13896791 := bstep (se 1 (by rfl) ⟨10422593, by rfl⟩ : syracuseStep 13896791 = 20845187) B20845187
theorem B9264527 : Blo 1927435 9264527 := bstep (se 1 (by rfl) ⟨6948395, by rfl⟩ : syracuseStep 9264527 = 13896791) B13896791
theorem B6176351 : Blo 1927435 6176351 := bstep (se 1 (by rfl) ⟨4632263, by rfl⟩ : syracuseStep 6176351 = 9264527) B9264527
theorem B4117567 : Blo 1927435 4117567 := bstep (se 1 (by rfl) ⟨3088175, by rfl⟩ : syracuseStep 4117567 = 6176351) B6176351
theorem B5490089 : Blo 1927435 5490089 := bstep (se 2 (by rfl) ⟨2058783, by rfl⟩ : syracuseStep 5490089 = 4117567) B4117567
theorem B3660059 : Blo 1927435 3660059 := bstep (se 1 (by rfl) ⟨2745044, by rfl⟩ : syracuseStep 3660059 = 5490089) B5490089
theorem B2440039 : Blo 1927435 2440039 := bstep (se 1 (by rfl) ⟨1830029, by rfl⟩ : syracuseStep 2440039 = 3660059) B3660059
theorem B3253385 : Blo 1927435 3253385 := bstep (se 2 (by rfl) ⟨1220019, by rfl⟩ : syracuseStep 3253385 = 2440039) B2440039
theorem B2168923 : Blo 1927435 2168923 := bstep (se 1 (by rfl) ⟨1626692, by rfl⟩ : syracuseStep 2168923 = 3253385) B3253385
theorem B2891897 : Blo 1927435 2891897 := bstep (se 2 (by rfl) ⟨1084461, by rfl⟩ : syracuseStep 2891897 = 2168923) B2168923
theorem B1927931 : Blo 1927435 1927931 := bstep (se 1 (by rfl) ⟨1445948, by rfl⟩ : syracuseStep 1927931 = 2891897) B2891897
theorem B25042517 : Blo 1927435 25042517 := bbase (se 8 (by rfl) ⟨146733, by rfl⟩ : syracuseStep 25042517 = 293467) (by norm_num)
theorem B16695011 : Blo 1927435 16695011 := bstep (se 1 (by rfl) ⟨12521258, by rfl⟩ : syracuseStep 16695011 = 25042517) B25042517
theorem B44520029 : Blo 1927435 44520029 := bstep (se 3 (by rfl) ⟨8347505, by rfl⟩ : syracuseStep 44520029 = 16695011) B16695011
theorem B29680019 : Blo 1927435 29680019 := bstep (se 1 (by rfl) ⟨22260014, by rfl⟩ : syracuseStep 29680019 = 44520029) B44520029
theorem B19786679 : Blo 1927435 19786679 := bstep (se 1 (by rfl) ⟨14840009, by rfl⟩ : syracuseStep 19786679 = 29680019) B29680019
theorem B13191119 : Blo 1927435 13191119 := bstep (se 1 (by rfl) ⟨9893339, by rfl⟩ : syracuseStep 13191119 = 19786679) B19786679
theorem B8794079 : Blo 1927435 8794079 := bstep (se 1 (by rfl) ⟨6595559, by rfl⟩ : syracuseStep 8794079 = 13191119) B13191119
theorem B5862719 : Blo 1927435 5862719 := bstep (se 1 (by rfl) ⟨4397039, by rfl⟩ : syracuseStep 5862719 = 8794079) B8794079
theorem B15633917 : Blo 1927435 15633917 := bstep (se 3 (by rfl) ⟨2931359, by rfl⟩ : syracuseStep 15633917 = 5862719) B5862719
theorem B10422611 : Blo 1927435 10422611 := bstep (se 1 (by rfl) ⟨7816958, by rfl⟩ : syracuseStep 10422611 = 15633917) B15633917
theorem B6948407 : Blo 1927435 6948407 := bstep (se 1 (by rfl) ⟨5211305, by rfl⟩ : syracuseStep 6948407 = 10422611) B10422611
theorem B4632271 : Blo 1927435 4632271 := bstep (se 1 (by rfl) ⟨3474203, by rfl⟩ : syracuseStep 4632271 = 6948407) B6948407
theorem B24705445 : Blo 1927435 24705445 := bstep (se 4 (by rfl) ⟨2316135, by rfl⟩ : syracuseStep 24705445 = 4632271) B4632271
theorem B32940593 : Blo 1927435 32940593 := bstep (se 2 (by rfl) ⟨12352722, by rfl⟩ : syracuseStep 32940593 = 24705445) B24705445
theorem B21960395 : Blo 1927435 21960395 := bstep (se 1 (by rfl) ⟨16470296, by rfl⟩ : syracuseStep 21960395 = 32940593) B32940593
theorem B14640263 : Blo 1927435 14640263 := bstep (se 1 (by rfl) ⟨10980197, by rfl⟩ : syracuseStep 14640263 = 21960395) B21960395
theorem B9760175 : Blo 1927435 9760175 := bstep (se 1 (by rfl) ⟨7320131, by rfl⟩ : syracuseStep 9760175 = 14640263) B14640263
theorem B6506783 : Blo 1927435 6506783 := bstep (se 1 (by rfl) ⟨4880087, by rfl⟩ : syracuseStep 6506783 = 9760175) B9760175
theorem B4337855 : Blo 1927435 4337855 := bstep (se 1 (by rfl) ⟨3253391, by rfl⟩ : syracuseStep 4337855 = 6506783) B6506783
theorem B2891903 : Blo 1927435 2891903 := bstep (se 1 (by rfl) ⟨2168927, by rfl⟩ : syracuseStep 2891903 = 4337855) B4337855
theorem B1927935 : Blo 1927435 1927935 := bstep (se 1 (by rfl) ⟨1445951, by rfl⟩ : syracuseStep 1927935 = 2891903) B2891903
theorem B2891909 : Blo 1927435 2891909 := bbase (se 4 (by rfl) ⟨271116, by rfl⟩ : syracuseStep 2891909 = 542233) (by norm_num)
theorem B1927939 : Blo 1927435 1927939 := bstep (se 1 (by rfl) ⟨1445954, by rfl⟩ : syracuseStep 1927939 = 2891909) B2891909
theorem B3253405 : Blo 1927435 3253405 := bbase (se 3 (by rfl) ⟨610013, by rfl⟩ : syracuseStep 3253405 = 1220027) (by norm_num)
theorem B4337873 : Blo 1927435 4337873 := bstep (se 2 (by rfl) ⟨1626702, by rfl⟩ : syracuseStep 4337873 = 3253405) B3253405
theorem B2891915 : Blo 1927435 2891915 := bstep (se 1 (by rfl) ⟨2168936, by rfl⟩ : syracuseStep 2891915 = 4337873) B4337873
theorem B1927943 : Blo 1927435 1927943 := bstep (se 1 (by rfl) ⟨1445957, by rfl⟩ : syracuseStep 1927943 = 2891915) B2891915
theorem B2168941 : Blo 1927435 2168941 := bbase (se 3 (by rfl) ⟨406676, by rfl⟩ : syracuseStep 2168941 = 813353) (by norm_num)
theorem B2891921 : Blo 1927435 2891921 := bstep (se 2 (by rfl) ⟨1084470, by rfl⟩ : syracuseStep 2891921 = 2168941) B2168941
theorem B1927947 : Blo 1927435 1927947 := bstep (se 1 (by rfl) ⟨1445960, by rfl⟩ : syracuseStep 1927947 = 2891921) B2891921
theorem B6506837 : Blo 1927435 6506837 := bbase (se 10 (by rfl) ⟨9531, by rfl⟩ : syracuseStep 6506837 = 19063) (by norm_num)
theorem B4337891 : Blo 1927435 4337891 := bstep (se 1 (by rfl) ⟨3253418, by rfl⟩ : syracuseStep 4337891 = 6506837) B6506837
theorem B2891927 : Blo 1927435 2891927 := bstep (se 1 (by rfl) ⟨2168945, by rfl⟩ : syracuseStep 2891927 = 4337891) B4337891
theorem B1927951 : Blo 1927435 1927951 := bstep (se 1 (by rfl) ⟨1445963, by rfl⟩ : syracuseStep 1927951 = 2891927) B2891927
theorem B2891933 : Blo 1927435 2891933 := bbase (se 3 (by rfl) ⟨542237, by rfl⟩ : syracuseStep 2891933 = 1084475) (by norm_num)
theorem B1927955 : Blo 1927435 1927955 := bstep (se 1 (by rfl) ⟨1445966, by rfl⟩ : syracuseStep 1927955 = 2891933) B2891933
theorem B4337909 : Blo 1927435 4337909 := bbase (se 5 (by rfl) ⟨203339, by rfl⟩ : syracuseStep 4337909 = 406679) (by norm_num)
theorem B2891939 : Blo 1927435 2891939 := bstep (se 1 (by rfl) ⟨2168954, by rfl⟩ : syracuseStep 2891939 = 4337909) B4337909
theorem B1927959 : Blo 1927435 1927959 := bstep (se 1 (by rfl) ⟨1445969, by rfl⟩ : syracuseStep 1927959 = 2891939) B2891939
theorem B3297829 : Blo 1927435 3297829 := bbase (se 4 (by rfl) ⟨309171, by rfl⟩ : syracuseStep 3297829 = 618343) (by norm_num)
theorem B4397105 : Blo 1927435 4397105 := bstep (se 2 (by rfl) ⟨1648914, by rfl⟩ : syracuseStep 4397105 = 3297829) B3297829
theorem B2931403 : Blo 1927435 2931403 := bstep (se 1 (by rfl) ⟨2198552, by rfl⟩ : syracuseStep 2931403 = 4397105) B4397105
theorem B3908537 : Blo 1927435 3908537 := bstep (se 2 (by rfl) ⟨1465701, by rfl⟩ : syracuseStep 3908537 = 2931403) B2931403
theorem B2605691 : Blo 1927435 2605691 := bstep (se 1 (by rfl) ⟨1954268, by rfl⟩ : syracuseStep 2605691 = 3908537) B3908537
theorem B6948509 : Blo 1927435 6948509 := bstep (se 3 (by rfl) ⟨1302845, by rfl⟩ : syracuseStep 6948509 = 2605691) B2605691
theorem B18529357 : Blo 1927435 18529357 := bstep (se 3 (by rfl) ⟨3474254, by rfl⟩ : syracuseStep 18529357 = 6948509) B6948509
theorem B24705809 : Blo 1927435 24705809 := bstep (se 2 (by rfl) ⟨9264678, by rfl⟩ : syracuseStep 24705809 = 18529357) B18529357
theorem B16470539 : Blo 1927435 16470539 := bstep (se 1 (by rfl) ⟨12352904, by rfl⟩ : syracuseStep 16470539 = 24705809) B24705809
theorem B10980359 : Blo 1927435 10980359 := bstep (se 1 (by rfl) ⟨8235269, by rfl⟩ : syracuseStep 10980359 = 16470539) B16470539
theorem B7320239 : Blo 1927435 7320239 := bstep (se 1 (by rfl) ⟨5490179, by rfl⟩ : syracuseStep 7320239 = 10980359) B10980359
theorem B4880159 : Blo 1927435 4880159 := bstep (se 1 (by rfl) ⟨3660119, by rfl⟩ : syracuseStep 4880159 = 7320239) B7320239
theorem B3253439 : Blo 1927435 3253439 := bstep (se 1 (by rfl) ⟨2440079, by rfl⟩ : syracuseStep 3253439 = 4880159) B4880159
theorem B2168959 : Blo 1927435 2168959 := bstep (se 1 (by rfl) ⟨1626719, by rfl⟩ : syracuseStep 2168959 = 3253439) B3253439
theorem B2891945 : Blo 1927435 2891945 := bstep (se 2 (by rfl) ⟨1084479, by rfl⟩ : syracuseStep 2891945 = 2168959) B2168959
theorem B1927963 : Blo 1927435 1927963 := bstep (se 1 (by rfl) ⟨1445972, by rfl⟩ : syracuseStep 1927963 = 2891945) B2891945
theorem B4632349 : Blo 1927435 4632349 := bbase (se 3 (by rfl) ⟨868565, by rfl⟩ : syracuseStep 4632349 = 1737131) (by norm_num)
theorem B6176465 : Blo 1927435 6176465 := bstep (se 2 (by rfl) ⟨2316174, by rfl⟩ : syracuseStep 6176465 = 4632349) B4632349
theorem B4117643 : Blo 1927435 4117643 := bstep (se 1 (by rfl) ⟨3088232, by rfl⟩ : syracuseStep 4117643 = 6176465) B6176465
theorem B2745095 : Blo 1927435 2745095 := bstep (se 1 (by rfl) ⟨2058821, by rfl⟩ : syracuseStep 2745095 = 4117643) B4117643
theorem B7320253 : Blo 1927435 7320253 := bstep (se 3 (by rfl) ⟨1372547, by rfl⟩ : syracuseStep 7320253 = 2745095) B2745095
theorem B9760337 : Blo 1927435 9760337 := bstep (se 2 (by rfl) ⟨3660126, by rfl⟩ : syracuseStep 9760337 = 7320253) B7320253
theorem B6506891 : Blo 1927435 6506891 := bstep (se 1 (by rfl) ⟨4880168, by rfl⟩ : syracuseStep 6506891 = 9760337) B9760337
theorem B4337927 : Blo 1927435 4337927 := bstep (se 1 (by rfl) ⟨3253445, by rfl⟩ : syracuseStep 4337927 = 6506891) B6506891
theorem B2891951 : Blo 1927435 2891951 := bstep (se 1 (by rfl) ⟨2168963, by rfl⟩ : syracuseStep 2891951 = 4337927) B4337927
theorem B1927967 : Blo 1927435 1927967 := bstep (se 1 (by rfl) ⟨1445975, by rfl⟩ : syracuseStep 1927967 = 2891951) B2891951
theorem B2891957 : Blo 1927435 2891957 := bbase (se 5 (by rfl) ⟨135560, by rfl⟩ : syracuseStep 2891957 = 271121) (by norm_num)
theorem B1927971 : Blo 1927435 1927971 := bstep (se 1 (by rfl) ⟨1445978, by rfl⟩ : syracuseStep 1927971 = 2891957) B2891957
theorem B4880189 : Blo 1927435 4880189 := bbase (se 3 (by rfl) ⟨915035, by rfl⟩ : syracuseStep 4880189 = 1830071) (by norm_num)
theorem B3253459 : Blo 1927435 3253459 := bstep (se 1 (by rfl) ⟨2440094, by rfl⟩ : syracuseStep 3253459 = 4880189) B4880189
theorem B4337945 : Blo 1927435 4337945 := bstep (se 2 (by rfl) ⟨1626729, by rfl⟩ : syracuseStep 4337945 = 3253459) B3253459
theorem B2891963 : Blo 1927435 2891963 := bstep (se 1 (by rfl) ⟨2168972, by rfl⟩ : syracuseStep 2891963 = 4337945) B4337945
theorem B1927975 : Blo 1927435 1927975 := bstep (se 1 (by rfl) ⟨1445981, by rfl⟩ : syracuseStep 1927975 = 2891963) B2891963
theorem B2168977 : Blo 1927435 2168977 := bbase (se 2 (by rfl) ⟨813366, by rfl⟩ : syracuseStep 2168977 = 1626733) (by norm_num)
theorem B2891969 : Blo 1927435 2891969 := bstep (se 2 (by rfl) ⟨1084488, by rfl⟩ : syracuseStep 2891969 = 2168977) B2168977
theorem B1927979 : Blo 1927435 1927979 := bstep (se 1 (by rfl) ⟨1445984, by rfl⟩ : syracuseStep 1927979 = 2891969) B2891969
theorem B3660157 : Blo 1927435 3660157 := bbase (se 3 (by rfl) ⟨686279, by rfl⟩ : syracuseStep 3660157 = 1372559) (by norm_num)
theorem B4880209 : Blo 1927435 4880209 := bstep (se 2 (by rfl) ⟨1830078, by rfl⟩ : syracuseStep 4880209 = 3660157) B3660157
theorem B6506945 : Blo 1927435 6506945 := bstep (se 2 (by rfl) ⟨2440104, by rfl⟩ : syracuseStep 6506945 = 4880209) B4880209
theorem B4337963 : Blo 1927435 4337963 := bstep (se 1 (by rfl) ⟨3253472, by rfl⟩ : syracuseStep 4337963 = 6506945) B6506945
theorem B2891975 : Blo 1927435 2891975 := bstep (se 1 (by rfl) ⟨2168981, by rfl⟩ : syracuseStep 2891975 = 4337963) B4337963
theorem B1927983 : Blo 1927435 1927983 := bstep (se 1 (by rfl) ⟨1445987, by rfl⟩ : syracuseStep 1927983 = 2891975) B2891975
theorem B2891981 : Blo 1927435 2891981 := bbase (se 3 (by rfl) ⟨542246, by rfl⟩ : syracuseStep 2891981 = 1084493) (by norm_num)
theorem B1927987 : Blo 1927435 1927987 := bstep (se 1 (by rfl) ⟨1445990, by rfl⟩ : syracuseStep 1927987 = 2891981) B2891981
theorem B4337981 : Blo 1927435 4337981 := bbase (se 3 (by rfl) ⟨813371, by rfl⟩ : syracuseStep 4337981 = 1626743) (by norm_num)
theorem B2891987 : Blo 1927435 2891987 := bstep (se 1 (by rfl) ⟨2168990, by rfl⟩ : syracuseStep 2891987 = 4337981) B4337981
theorem B1927991 : Blo 1927435 1927991 := bstep (se 1 (by rfl) ⟨1445993, by rfl⟩ : syracuseStep 1927991 = 2891987) B2891987
theorem B3253493 : Blo 1927435 3253493 := bbase (se 5 (by rfl) ⟨152507, by rfl⟩ : syracuseStep 3253493 = 305015) (by norm_num)
theorem B2168995 : Blo 1927435 2168995 := bstep (se 1 (by rfl) ⟨1626746, by rfl⟩ : syracuseStep 2168995 = 3253493) B3253493
theorem B2891993 : Blo 1927435 2891993 := bstep (se 2 (by rfl) ⟨1084497, by rfl⟩ : syracuseStep 2891993 = 2168995) B2168995
theorem B1927995 : Blo 1927435 1927995 := bstep (se 1 (by rfl) ⟨1445996, by rfl⟩ : syracuseStep 1927995 = 2891993) B2891993
theorem B2198593 : Blo 1927435 2198593 := bbase (se 2 (by rfl) ⟨824472, by rfl⟩ : syracuseStep 2198593 = 1648945) (by norm_num)
theorem B11725829 : Blo 1927435 11725829 := bstep (se 4 (by rfl) ⟨1099296, by rfl⟩ : syracuseStep 11725829 = 2198593) B2198593
theorem B7817219 : Blo 1927435 7817219 := bstep (se 1 (by rfl) ⟨5862914, by rfl⟩ : syracuseStep 7817219 = 11725829) B11725829
theorem B5211479 : Blo 1927435 5211479 := bstep (se 1 (by rfl) ⟨3908609, by rfl⟩ : syracuseStep 5211479 = 7817219) B7817219
theorem B13897277 : Blo 1927435 13897277 := bstep (se 3 (by rfl) ⟨2605739, by rfl⟩ : syracuseStep 13897277 = 5211479) B5211479
theorem B9264851 : Blo 1927435 9264851 := bstep (se 1 (by rfl) ⟨6948638, by rfl⟩ : syracuseStep 9264851 = 13897277) B13897277
theorem B6176567 : Blo 1927435 6176567 := bstep (se 1 (by rfl) ⟨4632425, by rfl⟩ : syracuseStep 6176567 = 9264851) B9264851
theorem B4117711 : Blo 1927435 4117711 := bstep (se 1 (by rfl) ⟨3088283, by rfl⟩ : syracuseStep 4117711 = 6176567) B6176567
theorem B5490281 : Blo 1927435 5490281 := bstep (se 2 (by rfl) ⟨2058855, by rfl⟩ : syracuseStep 5490281 = 4117711) B4117711
theorem B14640749 : Blo 1927435 14640749 := bstep (se 3 (by rfl) ⟨2745140, by rfl⟩ : syracuseStep 14640749 = 5490281) B5490281
theorem B9760499 : Blo 1927435 9760499 := bstep (se 1 (by rfl) ⟨7320374, by rfl⟩ : syracuseStep 9760499 = 14640749) B14640749
theorem B6506999 : Blo 1927435 6506999 := bstep (se 1 (by rfl) ⟨4880249, by rfl⟩ : syracuseStep 6506999 = 9760499) B9760499
theorem B4337999 : Blo 1927435 4337999 := bstep (se 1 (by rfl) ⟨3253499, by rfl⟩ : syracuseStep 4337999 = 6506999) B6506999
theorem B2891999 : Blo 1927435 2891999 := bstep (se 1 (by rfl) ⟨2168999, by rfl⟩ : syracuseStep 2891999 = 4337999) B4337999
theorem B1927999 : Blo 1927435 1927999 := bstep (se 1 (by rfl) ⟨1445999, by rfl⟩ : syracuseStep 1927999 = 2891999) B2891999
theorem B2892005 : Blo 1927435 2892005 := bbase (se 4 (by rfl) ⟨271125, by rfl⟩ : syracuseStep 2892005 = 542251) (by norm_num)
theorem B1928003 : Blo 1927435 1928003 := bstep (se 1 (by rfl) ⟨1446002, by rfl⟩ : syracuseStep 1928003 = 2892005) B2892005
theorem B4759717 : Blo 1927435 4759717 := bbase (se 4 (by rfl) ⟨446223, by rfl⟩ : syracuseStep 4759717 = 892447) (by norm_num)
theorem B6346289 : Blo 1927435 6346289 := bstep (se 2 (by rfl) ⟨2379858, by rfl⟩ : syracuseStep 6346289 = 4759717) B4759717
theorem B4230859 : Blo 1927435 4230859 := bstep (se 1 (by rfl) ⟨3173144, by rfl⟩ : syracuseStep 4230859 = 6346289) B6346289
theorem B5641145 : Blo 1927435 5641145 := bstep (se 2 (by rfl) ⟨2115429, by rfl⟩ : syracuseStep 5641145 = 4230859) B4230859
theorem B3760763 : Blo 1927435 3760763 := bstep (se 1 (by rfl) ⟨2820572, by rfl⟩ : syracuseStep 3760763 = 5641145) B5641145
theorem B10028701 : Blo 1927435 10028701 := bstep (se 3 (by rfl) ⟨1880381, by rfl⟩ : syracuseStep 10028701 = 3760763) B3760763
theorem B13371601 : Blo 1927435 13371601 := bstep (se 2 (by rfl) ⟨5014350, by rfl⟩ : syracuseStep 13371601 = 10028701) B10028701
theorem B17828801 : Blo 1927435 17828801 := bstep (se 2 (by rfl) ⟨6685800, by rfl⟩ : syracuseStep 17828801 = 13371601) B13371601
theorem B11885867 : Blo 1927435 11885867 := bstep (se 1 (by rfl) ⟨8914400, by rfl⟩ : syracuseStep 11885867 = 17828801) B17828801
theorem B7923911 : Blo 1927435 7923911 := bstep (se 1 (by rfl) ⟨5942933, by rfl⟩ : syracuseStep 7923911 = 11885867) B11885867
theorem B21130429 : Blo 1927435 21130429 := bstep (se 3 (by rfl) ⟨3961955, by rfl⟩ : syracuseStep 21130429 = 7923911) B7923911
theorem B28173905 : Blo 1927435 28173905 := bstep (se 2 (by rfl) ⟨10565214, by rfl⟩ : syracuseStep 28173905 = 21130429) B21130429
theorem B18782603 : Blo 1927435 18782603 := bstep (se 1 (by rfl) ⟨14086952, by rfl⟩ : syracuseStep 18782603 = 28173905) B28173905
theorem B12521735 : Blo 1927435 12521735 := bstep (se 1 (by rfl) ⟨9391301, by rfl⟩ : syracuseStep 12521735 = 18782603) B18782603
theorem B8347823 : Blo 1927435 8347823 := bstep (se 1 (by rfl) ⟨6260867, by rfl⟩ : syracuseStep 8347823 = 12521735) B12521735
theorem B5565215 : Blo 1927435 5565215 := bstep (se 1 (by rfl) ⟨4173911, by rfl⟩ : syracuseStep 5565215 = 8347823) B8347823
theorem B3710143 : Blo 1927435 3710143 := bstep (se 1 (by rfl) ⟨2782607, by rfl⟩ : syracuseStep 3710143 = 5565215) B5565215
theorem B19787429 : Blo 1927435 19787429 := bstep (se 4 (by rfl) ⟨1855071, by rfl⟩ : syracuseStep 19787429 = 3710143) B3710143
theorem B13191619 : Blo 1927435 13191619 := bstep (se 1 (by rfl) ⟨9893714, by rfl⟩ : syracuseStep 13191619 = 19787429) B19787429
theorem B17588825 : Blo 1927435 17588825 := bstep (se 2 (by rfl) ⟨6595809, by rfl⟩ : syracuseStep 17588825 = 13191619) B13191619
theorem B11725883 : Blo 1927435 11725883 := bstep (se 1 (by rfl) ⟨8794412, by rfl⟩ : syracuseStep 11725883 = 17588825) B17588825
theorem B7817255 : Blo 1927435 7817255 := bstep (se 1 (by rfl) ⟨5862941, by rfl⟩ : syracuseStep 7817255 = 11725883) B11725883
theorem B5211503 : Blo 1927435 5211503 := bstep (se 1 (by rfl) ⟨3908627, by rfl⟩ : syracuseStep 5211503 = 7817255) B7817255
theorem B3474335 : Blo 1927435 3474335 := bstep (se 1 (by rfl) ⟨2605751, by rfl⟩ : syracuseStep 3474335 = 5211503) B5211503
theorem B2316223 : Blo 1927435 2316223 := bstep (se 1 (by rfl) ⟨1737167, by rfl⟩ : syracuseStep 2316223 = 3474335) B3474335
theorem B3088297 : Blo 1927435 3088297 := bstep (se 2 (by rfl) ⟨1158111, by rfl⟩ : syracuseStep 3088297 = 2316223) B2316223
theorem B4117729 : Blo 1927435 4117729 := bstep (se 2 (by rfl) ⟨1544148, by rfl⟩ : syracuseStep 4117729 = 3088297) B3088297
theorem B5490305 : Blo 1927435 5490305 := bstep (se 2 (by rfl) ⟨2058864, by rfl⟩ : syracuseStep 5490305 = 4117729) B4117729
theorem B3660203 : Blo 1927435 3660203 := bstep (se 1 (by rfl) ⟨2745152, by rfl⟩ : syracuseStep 3660203 = 5490305) B5490305
theorem B2440135 : Blo 1927435 2440135 := bstep (se 1 (by rfl) ⟨1830101, by rfl⟩ : syracuseStep 2440135 = 3660203) B3660203
theorem B3253513 : Blo 1927435 3253513 := bstep (se 2 (by rfl) ⟨1220067, by rfl⟩ : syracuseStep 3253513 = 2440135) B2440135
theorem B4338017 : Blo 1927435 4338017 := bstep (se 2 (by rfl) ⟨1626756, by rfl⟩ : syracuseStep 4338017 = 3253513) B3253513
theorem B2892011 : Blo 1927435 2892011 := bstep (se 1 (by rfl) ⟨2169008, by rfl⟩ : syracuseStep 2892011 = 4338017) B4338017
theorem B1928007 : Blo 1927435 1928007 := bstep (se 1 (by rfl) ⟨1446005, by rfl⟩ : syracuseStep 1928007 = 2892011) B2892011
theorem B2169013 : Blo 1927435 2169013 := bbase (se 5 (by rfl) ⟨101672, by rfl⟩ : syracuseStep 2169013 = 203345) (by norm_num)
theorem B2892017 : Blo 1927435 2892017 := bstep (se 2 (by rfl) ⟨1084506, by rfl⟩ : syracuseStep 2892017 = 2169013) B2169013
theorem B1928011 : Blo 1927435 1928011 := bstep (se 1 (by rfl) ⟨1446008, by rfl⟩ : syracuseStep 1928011 = 2892017) B2892017
theorem B2440145 : Blo 1927435 2440145 := bbase (se 2 (by rfl) ⟨915054, by rfl⟩ : syracuseStep 2440145 = 1830109) (by norm_num)
theorem B6507053 : Blo 1927435 6507053 := bstep (se 3 (by rfl) ⟨1220072, by rfl⟩ : syracuseStep 6507053 = 2440145) B2440145
theorem B4338035 : Blo 1927435 4338035 := bstep (se 1 (by rfl) ⟨3253526, by rfl⟩ : syracuseStep 4338035 = 6507053) B6507053
theorem B2892023 : Blo 1927435 2892023 := bstep (se 1 (by rfl) ⟨2169017, by rfl⟩ : syracuseStep 2892023 = 4338035) B4338035
theorem B1928015 : Blo 1927435 1928015 := bstep (se 1 (by rfl) ⟨1446011, by rfl⟩ : syracuseStep 1928015 = 2892023) B2892023
theorem B2892029 : Blo 1927435 2892029 := bbase (se 3 (by rfl) ⟨542255, by rfl⟩ : syracuseStep 2892029 = 1084511) (by norm_num)
theorem B1928019 : Blo 1927435 1928019 := bstep (se 1 (by rfl) ⟨1446014, by rfl⟩ : syracuseStep 1928019 = 2892029) B2892029
theorem B4338053 : Blo 1927435 4338053 := bbase (se 4 (by rfl) ⟨406692, by rfl⟩ : syracuseStep 4338053 = 813385) (by norm_num)
theorem B2892035 : Blo 1927435 2892035 := bstep (se 1 (by rfl) ⟨2169026, by rfl⟩ : syracuseStep 2892035 = 4338053) B4338053
theorem B1928023 : Blo 1927435 1928023 := bstep (se 1 (by rfl) ⟨1446017, by rfl⟩ : syracuseStep 1928023 = 2892035) B2892035
theorem B2745181 : Blo 1927435 2745181 := bbase (se 3 (by rfl) ⟨514721, by rfl⟩ : syracuseStep 2745181 = 1029443) (by norm_num)
theorem B3660241 : Blo 1927435 3660241 := bstep (se 2 (by rfl) ⟨1372590, by rfl⟩ : syracuseStep 3660241 = 2745181) B2745181
theorem B4880321 : Blo 1927435 4880321 := bstep (se 2 (by rfl) ⟨1830120, by rfl⟩ : syracuseStep 4880321 = 3660241) B3660241
theorem B3253547 : Blo 1927435 3253547 := bstep (se 1 (by rfl) ⟨2440160, by rfl⟩ : syracuseStep 3253547 = 4880321) B4880321
theorem B2169031 : Blo 1927435 2169031 := bstep (se 1 (by rfl) ⟨1626773, by rfl⟩ : syracuseStep 2169031 = 3253547) B3253547
theorem B2892041 : Blo 1927435 2892041 := bstep (se 2 (by rfl) ⟨1084515, by rfl⟩ : syracuseStep 2892041 = 2169031) B2169031
theorem B1928027 : Blo 1927435 1928027 := bstep (se 1 (by rfl) ⟨1446020, by rfl⟩ : syracuseStep 1928027 = 2892041) B2892041
theorem B9760661 : Blo 1927435 9760661 := bbase (se 6 (by rfl) ⟨228765, by rfl⟩ : syracuseStep 9760661 = 457531) (by norm_num)
theorem B6507107 : Blo 1927435 6507107 := bstep (se 1 (by rfl) ⟨4880330, by rfl⟩ : syracuseStep 6507107 = 9760661) B9760661
theorem B4338071 : Blo 1927435 4338071 := bstep (se 1 (by rfl) ⟨3253553, by rfl⟩ : syracuseStep 4338071 = 6507107) B6507107
theorem B2892047 : Blo 1927435 2892047 := bstep (se 1 (by rfl) ⟨2169035, by rfl⟩ : syracuseStep 2892047 = 4338071) B4338071
theorem B1928031 : Blo 1927435 1928031 := bstep (se 1 (by rfl) ⟨1446023, by rfl⟩ : syracuseStep 1928031 = 2892047) B2892047
theorem B2892053 : Blo 1927435 2892053 := bbase (se 6 (by rfl) ⟨67782, by rfl⟩ : syracuseStep 2892053 = 135565) (by norm_num)
theorem B1928035 : Blo 1927435 1928035 := bstep (se 1 (by rfl) ⟨1446026, by rfl⟩ : syracuseStep 1928035 = 2892053) B2892053
theorem B7817381 : Blo 1927435 7817381 := bbase (se 4 (by rfl) ⟨732879, by rfl⟩ : syracuseStep 7817381 = 1465759) (by norm_num)
theorem B5211587 : Blo 1927435 5211587 := bstep (se 1 (by rfl) ⟨3908690, by rfl⟩ : syracuseStep 5211587 = 7817381) B7817381
theorem B13897565 : Blo 1927435 13897565 := bstep (se 3 (by rfl) ⟨2605793, by rfl⟩ : syracuseStep 13897565 = 5211587) B5211587
theorem B9265043 : Blo 1927435 9265043 := bstep (se 1 (by rfl) ⟨6948782, by rfl⟩ : syracuseStep 9265043 = 13897565) B13897565
theorem B24706781 : Blo 1927435 24706781 := bstep (se 3 (by rfl) ⟨4632521, by rfl⟩ : syracuseStep 24706781 = 9265043) B9265043
theorem B16471187 : Blo 1927435 16471187 := bstep (se 1 (by rfl) ⟨12353390, by rfl⟩ : syracuseStep 16471187 = 24706781) B24706781
theorem B10980791 : Blo 1927435 10980791 := bstep (se 1 (by rfl) ⟨8235593, by rfl⟩ : syracuseStep 10980791 = 16471187) B16471187
theorem B7320527 : Blo 1927435 7320527 := bstep (se 1 (by rfl) ⟨5490395, by rfl⟩ : syracuseStep 7320527 = 10980791) B10980791
theorem B4880351 : Blo 1927435 4880351 := bstep (se 1 (by rfl) ⟨3660263, by rfl⟩ : syracuseStep 4880351 = 7320527) B7320527
theorem B3253567 : Blo 1927435 3253567 := bstep (se 1 (by rfl) ⟨2440175, by rfl⟩ : syracuseStep 3253567 = 4880351) B4880351
theorem B4338089 : Blo 1927435 4338089 := bstep (se 2 (by rfl) ⟨1626783, by rfl⟩ : syracuseStep 4338089 = 3253567) B3253567
theorem B2892059 : Blo 1927435 2892059 := bstep (se 1 (by rfl) ⟨2169044, by rfl⟩ : syracuseStep 2892059 = 4338089) B4338089
theorem B1928039 : Blo 1927435 1928039 := bstep (se 1 (by rfl) ⟨1446029, by rfl⟩ : syracuseStep 1928039 = 2892059) B2892059
theorem B2169049 : Blo 1927435 2169049 := bbase (se 2 (by rfl) ⟨813393, by rfl⟩ : syracuseStep 2169049 = 1626787) (by norm_num)
theorem B2892065 : Blo 1927435 2892065 := bstep (se 2 (by rfl) ⟨1084524, by rfl⟩ : syracuseStep 2892065 = 2169049) B2169049
theorem B1928043 : Blo 1927435 1928043 := bstep (se 1 (by rfl) ⟨1446032, by rfl⟩ : syracuseStep 1928043 = 2892065) B2892065
theorem B13191893 : Blo 1927435 13191893 := bbase (se 7 (by rfl) ⟨154592, by rfl⟩ : syracuseStep 13191893 = 309185) (by norm_num)
theorem B8794595 : Blo 1927435 8794595 := bstep (se 1 (by rfl) ⟨6595946, by rfl⟩ : syracuseStep 8794595 = 13191893) B13191893
theorem B5863063 : Blo 1927435 5863063 := bstep (se 1 (by rfl) ⟨4397297, by rfl⟩ : syracuseStep 5863063 = 8794595) B8794595
theorem B7817417 : Blo 1927435 7817417 := bstep (se 2 (by rfl) ⟨2931531, by rfl⟩ : syracuseStep 7817417 = 5863063) B5863063
theorem B5211611 : Blo 1927435 5211611 := bstep (se 1 (by rfl) ⟨3908708, by rfl⟩ : syracuseStep 5211611 = 7817417) B7817417
theorem B3474407 : Blo 1927435 3474407 := bstep (se 1 (by rfl) ⟨2605805, by rfl⟩ : syracuseStep 3474407 = 5211611) B5211611
theorem B2316271 : Blo 1927435 2316271 := bstep (se 1 (by rfl) ⟨1737203, by rfl⟩ : syracuseStep 2316271 = 3474407) B3474407
theorem B3088361 : Blo 1927435 3088361 := bstep (se 2 (by rfl) ⟨1158135, by rfl⟩ : syracuseStep 3088361 = 2316271) B2316271
theorem B2058907 : Blo 1927435 2058907 := bstep (se 1 (by rfl) ⟨1544180, by rfl⟩ : syracuseStep 2058907 = 3088361) B3088361
theorem B2745209 : Blo 1927435 2745209 := bstep (se 2 (by rfl) ⟨1029453, by rfl⟩ : syracuseStep 2745209 = 2058907) B2058907
theorem B7320557 : Blo 1927435 7320557 := bstep (se 3 (by rfl) ⟨1372604, by rfl⟩ : syracuseStep 7320557 = 2745209) B2745209
theorem B4880371 : Blo 1927435 4880371 := bstep (se 1 (by rfl) ⟨3660278, by rfl⟩ : syracuseStep 4880371 = 7320557) B7320557
theorem B6507161 : Blo 1927435 6507161 := bstep (se 2 (by rfl) ⟨2440185, by rfl⟩ : syracuseStep 6507161 = 4880371) B4880371
theorem B4338107 : Blo 1927435 4338107 := bstep (se 1 (by rfl) ⟨3253580, by rfl⟩ : syracuseStep 4338107 = 6507161) B6507161
theorem B2892071 : Blo 1927435 2892071 := bstep (se 1 (by rfl) ⟨2169053, by rfl⟩ : syracuseStep 2892071 = 4338107) B4338107
theorem B1928047 : Blo 1927435 1928047 := bstep (se 1 (by rfl) ⟨1446035, by rfl⟩ : syracuseStep 1928047 = 2892071) B2892071
theorem B2892077 : Blo 1927435 2892077 := bbase (se 3 (by rfl) ⟨542264, by rfl⟩ : syracuseStep 2892077 = 1084529) (by norm_num)
theorem B1928051 : Blo 1927435 1928051 := bstep (se 1 (by rfl) ⟨1446038, by rfl⟩ : syracuseStep 1928051 = 2892077) B2892077
theorem B4338125 : Blo 1927435 4338125 := bbase (se 3 (by rfl) ⟨813398, by rfl⟩ : syracuseStep 4338125 = 1626797) (by norm_num)
theorem B2892083 : Blo 1927435 2892083 := bstep (se 1 (by rfl) ⟨2169062, by rfl⟩ : syracuseStep 2892083 = 4338125) B4338125
theorem B1928055 : Blo 1927435 1928055 := bstep (se 1 (by rfl) ⟨1446041, by rfl⟩ : syracuseStep 1928055 = 2892083) B2892083
theorem B2440201 : Blo 1927435 2440201 := bbase (se 2 (by rfl) ⟨915075, by rfl⟩ : syracuseStep 2440201 = 1830151) (by norm_num)
theorem B3253601 : Blo 1927435 3253601 := bstep (se 2 (by rfl) ⟨1220100, by rfl⟩ : syracuseStep 3253601 = 2440201) B2440201
theorem B2169067 : Blo 1927435 2169067 := bstep (se 1 (by rfl) ⟨1626800, by rfl⟩ : syracuseStep 2169067 = 3253601) B3253601
theorem B2892089 : Blo 1927435 2892089 := bstep (se 2 (by rfl) ⟨1084533, by rfl⟩ : syracuseStep 2892089 = 2169067) B2169067
theorem B1928059 : Blo 1927435 1928059 := bstep (se 1 (by rfl) ⟨1446044, by rfl⟩ : syracuseStep 1928059 = 2892089) B2892089
theorem B7817477 : Blo 1927435 7817477 := bbase (se 4 (by rfl) ⟨732888, by rfl⟩ : syracuseStep 7817477 = 1465777) (by norm_num)
theorem B20846605 : Blo 1927435 20846605 := bstep (se 3 (by rfl) ⟨3908738, by rfl⟩ : syracuseStep 20846605 = 7817477) B7817477
theorem B27795473 : Blo 1927435 27795473 := bstep (se 2 (by rfl) ⟨10423302, by rfl⟩ : syracuseStep 27795473 = 20846605) B20846605
theorem B18530315 : Blo 1927435 18530315 := bstep (se 1 (by rfl) ⟨13897736, by rfl⟩ : syracuseStep 18530315 = 27795473) B27795473
theorem B12353543 : Blo 1927435 12353543 := bstep (se 1 (by rfl) ⟨9265157, by rfl⟩ : syracuseStep 12353543 = 18530315) B18530315
theorem B8235695 : Blo 1927435 8235695 := bstep (se 1 (by rfl) ⟨6176771, by rfl⟩ : syracuseStep 8235695 = 12353543) B12353543
theorem B21961853 : Blo 1927435 21961853 := bstep (se 3 (by rfl) ⟨4117847, by rfl⟩ : syracuseStep 21961853 = 8235695) B8235695
theorem B14641235 : Blo 1927435 14641235 := bstep (se 1 (by rfl) ⟨10980926, by rfl⟩ : syracuseStep 14641235 = 21961853) B21961853
theorem B9760823 : Blo 1927435 9760823 := bstep (se 1 (by rfl) ⟨7320617, by rfl⟩ : syracuseStep 9760823 = 14641235) B14641235
theorem B6507215 : Blo 1927435 6507215 := bstep (se 1 (by rfl) ⟨4880411, by rfl⟩ : syracuseStep 6507215 = 9760823) B9760823
theorem B4338143 : Blo 1927435 4338143 := bstep (se 1 (by rfl) ⟨3253607, by rfl⟩ : syracuseStep 4338143 = 6507215) B6507215
theorem B2892095 : Blo 1927435 2892095 := bstep (se 1 (by rfl) ⟨2169071, by rfl⟩ : syracuseStep 2892095 = 4338143) B4338143
theorem B1928063 : Blo 1927435 1928063 := bstep (se 1 (by rfl) ⟨1446047, by rfl⟩ : syracuseStep 1928063 = 2892095) B2892095
theorem B2892101 : Blo 1927435 2892101 := bbase (se 4 (by rfl) ⟨271134, by rfl⟩ : syracuseStep 2892101 = 542269) (by norm_num)
theorem B1928067 : Blo 1927435 1928067 := bstep (se 1 (by rfl) ⟨1446050, by rfl⟩ : syracuseStep 1928067 = 2892101) B2892101
theorem B3253621 : Blo 1927435 3253621 := bbase (se 5 (by rfl) ⟨152513, by rfl⟩ : syracuseStep 3253621 = 305027) (by norm_num)
theorem B4338161 : Blo 1927435 4338161 := bstep (se 2 (by rfl) ⟨1626810, by rfl⟩ : syracuseStep 4338161 = 3253621) B3253621
theorem B2892107 : Blo 1927435 2892107 := bstep (se 1 (by rfl) ⟨2169080, by rfl⟩ : syracuseStep 2892107 = 4338161) B4338161
theorem B1928071 : Blo 1927435 1928071 := bstep (se 1 (by rfl) ⟨1446053, by rfl⟩ : syracuseStep 1928071 = 2892107) B2892107
theorem B2169085 : Blo 1927435 2169085 := bbase (se 3 (by rfl) ⟨406703, by rfl⟩ : syracuseStep 2169085 = 813407) (by norm_num)
theorem B2892113 : Blo 1927435 2892113 := bstep (se 2 (by rfl) ⟨1084542, by rfl⟩ : syracuseStep 2892113 = 2169085) B2169085
theorem B1928075 : Blo 1927435 1928075 := bstep (se 1 (by rfl) ⟨1446056, by rfl⟩ : syracuseStep 1928075 = 2892113) B2892113
theorem B6507269 : Blo 1927435 6507269 := bbase (se 4 (by rfl) ⟨610056, by rfl⟩ : syracuseStep 6507269 = 1220113) (by norm_num)
theorem B4338179 : Blo 1927435 4338179 := bstep (se 1 (by rfl) ⟨3253634, by rfl⟩ : syracuseStep 4338179 = 6507269) B6507269
theorem B2892119 : Blo 1927435 2892119 := bstep (se 1 (by rfl) ⟨2169089, by rfl⟩ : syracuseStep 2892119 = 4338179) B4338179
theorem B1928079 : Blo 1927435 1928079 := bstep (se 1 (by rfl) ⟨1446059, by rfl⟩ : syracuseStep 1928079 = 2892119) B2892119
theorem B2892125 : Blo 1927435 2892125 := bbase (se 3 (by rfl) ⟨542273, by rfl⟩ : syracuseStep 2892125 = 1084547) (by norm_num)
theorem B1928083 : Blo 1927435 1928083 := bstep (se 1 (by rfl) ⟨1446062, by rfl⟩ : syracuseStep 1928083 = 2892125) B2892125
theorem B4338197 : Blo 1927435 4338197 := bbase (se 6 (by rfl) ⟨101676, by rfl⟩ : syracuseStep 4338197 = 203353) (by norm_num)
theorem B2892131 : Blo 1927435 2892131 := bstep (se 1 (by rfl) ⟨2169098, by rfl⟩ : syracuseStep 2892131 = 4338197) B4338197
theorem B1928087 : Blo 1927435 1928087 := bstep (se 1 (by rfl) ⟨1446065, by rfl⟩ : syracuseStep 1928087 = 2892131) B2892131
theorem B7320725 : Blo 1927435 7320725 := bbase (se 6 (by rfl) ⟨171579, by rfl⟩ : syracuseStep 7320725 = 343159) (by norm_num)
theorem B4880483 : Blo 1927435 4880483 := bstep (se 1 (by rfl) ⟨3660362, by rfl⟩ : syracuseStep 4880483 = 7320725) B7320725
theorem B3253655 : Blo 1927435 3253655 := bstep (se 1 (by rfl) ⟨2440241, by rfl⟩ : syracuseStep 3253655 = 4880483) B4880483
theorem B2169103 : Blo 1927435 2169103 := bstep (se 1 (by rfl) ⟨1626827, by rfl⟩ : syracuseStep 2169103 = 3253655) B3253655
theorem B2892137 : Blo 1927435 2892137 := bstep (se 2 (by rfl) ⟨1084551, by rfl⟩ : syracuseStep 2892137 = 2169103) B2169103
theorem B1928091 : Blo 1927435 1928091 := bstep (se 1 (by rfl) ⟨1446068, by rfl⟩ : syracuseStep 1928091 = 2892137) B2892137
theorem B10981109 : Blo 1927435 10981109 := bbase (se 5 (by rfl) ⟨514739, by rfl⟩ : syracuseStep 10981109 = 1029479) (by norm_num)
theorem B7320739 : Blo 1927435 7320739 := bstep (se 1 (by rfl) ⟨5490554, by rfl⟩ : syracuseStep 7320739 = 10981109) B10981109
theorem B9760985 : Blo 1927435 9760985 := bstep (se 2 (by rfl) ⟨3660369, by rfl⟩ : syracuseStep 9760985 = 7320739) B7320739
theorem B6507323 : Blo 1927435 6507323 := bstep (se 1 (by rfl) ⟨4880492, by rfl⟩ : syracuseStep 6507323 = 9760985) B9760985
theorem B4338215 : Blo 1927435 4338215 := bstep (se 1 (by rfl) ⟨3253661, by rfl⟩ : syracuseStep 4338215 = 6507323) B6507323
theorem B2892143 : Blo 1927435 2892143 := bstep (se 1 (by rfl) ⟨2169107, by rfl⟩ : syracuseStep 2892143 = 4338215) B4338215
theorem B1928095 : Blo 1927435 1928095 := bstep (se 1 (by rfl) ⟨1446071, by rfl⟩ : syracuseStep 1928095 = 2892143) B2892143
theorem B2892149 : Blo 1927435 2892149 := bbase (se 5 (by rfl) ⟨135569, by rfl⟩ : syracuseStep 2892149 = 271139) (by norm_num)
theorem B1928099 : Blo 1927435 1928099 := bstep (se 1 (by rfl) ⟨1446074, by rfl⟩ : syracuseStep 1928099 = 2892149) B2892149
theorem B4632677 : Blo 1927435 4632677 := bbase (se 4 (by rfl) ⟨434313, by rfl⟩ : syracuseStep 4632677 = 868627) (by norm_num)
theorem B3088451 : Blo 1927435 3088451 := bstep (se 1 (by rfl) ⟨2316338, by rfl⟩ : syracuseStep 3088451 = 4632677) B4632677
theorem B2058967 : Blo 1927435 2058967 := bstep (se 1 (by rfl) ⟨1544225, by rfl⟩ : syracuseStep 2058967 = 3088451) B3088451
theorem B2745289 : Blo 1927435 2745289 := bstep (se 2 (by rfl) ⟨1029483, by rfl⟩ : syracuseStep 2745289 = 2058967) B2058967
theorem B3660385 : Blo 1927435 3660385 := bstep (se 2 (by rfl) ⟨1372644, by rfl⟩ : syracuseStep 3660385 = 2745289) B2745289
theorem B4880513 : Blo 1927435 4880513 := bstep (se 2 (by rfl) ⟨1830192, by rfl⟩ : syracuseStep 4880513 = 3660385) B3660385
theorem B3253675 : Blo 1927435 3253675 := bstep (se 1 (by rfl) ⟨2440256, by rfl⟩ : syracuseStep 3253675 = 4880513) B4880513
theorem B4338233 : Blo 1927435 4338233 := bstep (se 2 (by rfl) ⟨1626837, by rfl⟩ : syracuseStep 4338233 = 3253675) B3253675
theorem B2892155 : Blo 1927435 2892155 := bstep (se 1 (by rfl) ⟨2169116, by rfl⟩ : syracuseStep 2892155 = 4338233) B4338233
theorem B1928103 : Blo 1927435 1928103 := bstep (se 1 (by rfl) ⟨1446077, by rfl⟩ : syracuseStep 1928103 = 2892155) B2892155
theorem B2169121 : Blo 1927435 2169121 := bbase (se 2 (by rfl) ⟨813420, by rfl⟩ : syracuseStep 2169121 = 1626841) (by norm_num)
theorem B2892161 : Blo 1927435 2892161 := bstep (se 2 (by rfl) ⟨1084560, by rfl⟩ : syracuseStep 2892161 = 2169121) B2169121
theorem B1928107 : Blo 1927435 1928107 := bstep (se 1 (by rfl) ⟨1446080, by rfl⟩ : syracuseStep 1928107 = 2892161) B2892161
theorem B4880533 : Blo 1927435 4880533 := bbase (se 6 (by rfl) ⟨114387, by rfl⟩ : syracuseStep 4880533 = 228775) (by norm_num)
theorem B6507377 : Blo 1927435 6507377 := bstep (se 2 (by rfl) ⟨2440266, by rfl⟩ : syracuseStep 6507377 = 4880533) B4880533
theorem B4338251 : Blo 1927435 4338251 := bstep (se 1 (by rfl) ⟨3253688, by rfl⟩ : syracuseStep 4338251 = 6507377) B6507377
theorem B2892167 : Blo 1927435 2892167 := bstep (se 1 (by rfl) ⟨2169125, by rfl⟩ : syracuseStep 2892167 = 4338251) B4338251
theorem B1928111 : Blo 1927435 1928111 := bstep (se 1 (by rfl) ⟨1446083, by rfl⟩ : syracuseStep 1928111 = 2892167) B2892167
theorem B2892173 : Blo 1927435 2892173 := bbase (se 3 (by rfl) ⟨542282, by rfl⟩ : syracuseStep 2892173 = 1084565) (by norm_num)
theorem B1928115 : Blo 1927435 1928115 := bstep (se 1 (by rfl) ⟨1446086, by rfl⟩ : syracuseStep 1928115 = 2892173) B2892173
theorem B4338269 : Blo 1927435 4338269 := bbase (se 3 (by rfl) ⟨813425, by rfl⟩ : syracuseStep 4338269 = 1626851) (by norm_num)
theorem B2892179 : Blo 1927435 2892179 := bstep (se 1 (by rfl) ⟨2169134, by rfl⟩ : syracuseStep 2892179 = 4338269) B4338269
theorem B1928119 : Blo 1927435 1928119 := bstep (se 1 (by rfl) ⟨1446089, by rfl⟩ : syracuseStep 1928119 = 2892179) B2892179
theorem B3253709 : Blo 1927435 3253709 := bbase (se 3 (by rfl) ⟨610070, by rfl⟩ : syracuseStep 3253709 = 1220141) (by norm_num)
theorem B2169139 : Blo 1927435 2169139 := bstep (se 1 (by rfl) ⟨1626854, by rfl⟩ : syracuseStep 2169139 = 3253709) B3253709
theorem B2892185 : Blo 1927435 2892185 := bstep (se 2 (by rfl) ⟨1084569, by rfl⟩ : syracuseStep 2892185 = 2169139) B2169139
theorem B1928123 : Blo 1927435 1928123 := bstep (se 1 (by rfl) ⟨1446092, by rfl⟩ : syracuseStep 1928123 = 2892185) B2892185
theorem B9894325 : Blo 1927435 9894325 := bbase (se 5 (by rfl) ⟨463796, by rfl⟩ : syracuseStep 9894325 = 927593) (by norm_num)
theorem B13192433 : Blo 1927435 13192433 := bstep (se 2 (by rfl) ⟨4947162, by rfl⟩ : syracuseStep 13192433 = 9894325) B9894325
theorem B8794955 : Blo 1927435 8794955 := bstep (se 1 (by rfl) ⟨6596216, by rfl⟩ : syracuseStep 8794955 = 13192433) B13192433
theorem B5863303 : Blo 1927435 5863303 := bstep (se 1 (by rfl) ⟨4397477, by rfl⟩ : syracuseStep 5863303 = 8794955) B8794955
theorem B7817737 : Blo 1927435 7817737 := bstep (se 2 (by rfl) ⟨2931651, by rfl⟩ : syracuseStep 7817737 = 5863303) B5863303
theorem B10423649 : Blo 1927435 10423649 := bstep (se 2 (by rfl) ⟨3908868, by rfl⟩ : syracuseStep 10423649 = 7817737) B7817737
theorem B6949099 : Blo 1927435 6949099 := bstep (se 1 (by rfl) ⟨5211824, by rfl⟩ : syracuseStep 6949099 = 10423649) B10423649
theorem B9265465 : Blo 1927435 9265465 := bstep (se 2 (by rfl) ⟨3474549, by rfl⟩ : syracuseStep 9265465 = 6949099) B6949099
theorem B12353953 : Blo 1927435 12353953 := bstep (se 2 (by rfl) ⟨4632732, by rfl⟩ : syracuseStep 12353953 = 9265465) B9265465
theorem B16471937 : Blo 1927435 16471937 := bstep (se 2 (by rfl) ⟨6176976, by rfl⟩ : syracuseStep 16471937 = 12353953) B12353953
theorem B10981291 : Blo 1927435 10981291 := bstep (se 1 (by rfl) ⟨8235968, by rfl⟩ : syracuseStep 10981291 = 16471937) B16471937
theorem B14641721 : Blo 1927435 14641721 := bstep (se 2 (by rfl) ⟨5490645, by rfl⟩ : syracuseStep 14641721 = 10981291) B10981291
theorem B9761147 : Blo 1927435 9761147 := bstep (se 1 (by rfl) ⟨7320860, by rfl⟩ : syracuseStep 9761147 = 14641721) B14641721
theorem B6507431 : Blo 1927435 6507431 := bstep (se 1 (by rfl) ⟨4880573, by rfl⟩ : syracuseStep 6507431 = 9761147) B9761147
theorem B4338287 : Blo 1927435 4338287 := bstep (se 1 (by rfl) ⟨3253715, by rfl⟩ : syracuseStep 4338287 = 6507431) B6507431
theorem B2892191 : Blo 1927435 2892191 := bstep (se 1 (by rfl) ⟨2169143, by rfl⟩ : syracuseStep 2892191 = 4338287) B4338287
theorem B1928127 : Blo 1927435 1928127 := bstep (se 1 (by rfl) ⟨1446095, by rfl⟩ : syracuseStep 1928127 = 2892191) B2892191
theorem B2892197 : Blo 1927435 2892197 := bbase (se 4 (by rfl) ⟨271143, by rfl⟩ : syracuseStep 2892197 = 542287) (by norm_num)
theorem B1928131 : Blo 1927435 1928131 := bstep (se 1 (by rfl) ⟨1446098, by rfl⟩ : syracuseStep 1928131 = 2892197) B2892197
theorem B2440297 : Blo 1927435 2440297 := bbase (se 2 (by rfl) ⟨915111, by rfl⟩ : syracuseStep 2440297 = 1830223) (by norm_num)
theorem B3253729 : Blo 1927435 3253729 := bstep (se 2 (by rfl) ⟨1220148, by rfl⟩ : syracuseStep 3253729 = 2440297) B2440297
theorem B4338305 : Blo 1927435 4338305 := bstep (se 2 (by rfl) ⟨1626864, by rfl⟩ : syracuseStep 4338305 = 3253729) B3253729
theorem B2892203 : Blo 1927435 2892203 := bstep (se 1 (by rfl) ⟨2169152, by rfl⟩ : syracuseStep 2892203 = 4338305) B4338305
theorem B1928135 : Blo 1927435 1928135 := bstep (se 1 (by rfl) ⟨1446101, by rfl⟩ : syracuseStep 1928135 = 2892203) B2892203
theorem B2169157 : Blo 1927435 2169157 := bbase (se 4 (by rfl) ⟨203358, by rfl⟩ : syracuseStep 2169157 = 406717) (by norm_num)
theorem B2892209 : Blo 1927435 2892209 := bstep (se 2 (by rfl) ⟨1084578, by rfl⟩ : syracuseStep 2892209 = 2169157) B2169157
theorem B1928139 : Blo 1927435 1928139 := bstep (se 1 (by rfl) ⟨1446104, by rfl⟩ : syracuseStep 1928139 = 2892209) B2892209
theorem B3660461 : Blo 1927435 3660461 := bbase (se 3 (by rfl) ⟨686336, by rfl⟩ : syracuseStep 3660461 = 1372673) (by norm_num)
theorem B2440307 : Blo 1927435 2440307 := bstep (se 1 (by rfl) ⟨1830230, by rfl⟩ : syracuseStep 2440307 = 3660461) B3660461
theorem B6507485 : Blo 1927435 6507485 := bstep (se 3 (by rfl) ⟨1220153, by rfl⟩ : syracuseStep 6507485 = 2440307) B2440307
theorem B4338323 : Blo 1927435 4338323 := bstep (se 1 (by rfl) ⟨3253742, by rfl⟩ : syracuseStep 4338323 = 6507485) B6507485
theorem B2892215 : Blo 1927435 2892215 := bstep (se 1 (by rfl) ⟨2169161, by rfl⟩ : syracuseStep 2892215 = 4338323) B4338323
theorem B1928143 : Blo 1927435 1928143 := bstep (se 1 (by rfl) ⟨1446107, by rfl⟩ : syracuseStep 1928143 = 2892215) B2892215
theorem B2892221 : Blo 1927435 2892221 := bbase (se 3 (by rfl) ⟨542291, by rfl⟩ : syracuseStep 2892221 = 1084583) (by norm_num)
theorem B1928147 : Blo 1927435 1928147 := bstep (se 1 (by rfl) ⟨1446110, by rfl⟩ : syracuseStep 1928147 = 2892221) B2892221
theorem B4338341 : Blo 1927435 4338341 := bbase (se 4 (by rfl) ⟨406719, by rfl⟩ : syracuseStep 4338341 = 813439) (by norm_num)
theorem B2892227 : Blo 1927435 2892227 := bstep (se 1 (by rfl) ⟨2169170, by rfl⟩ : syracuseStep 2892227 = 4338341) B4338341
theorem B1928151 : Blo 1927435 1928151 := bstep (se 1 (by rfl) ⟨1446113, by rfl⟩ : syracuseStep 1928151 = 2892227) B2892227
theorem B4880645 : Blo 1927435 4880645 := bbase (se 4 (by rfl) ⟨457560, by rfl⟩ : syracuseStep 4880645 = 915121) (by norm_num)
theorem B3253763 : Blo 1927435 3253763 := bstep (se 1 (by rfl) ⟨2440322, by rfl⟩ : syracuseStep 3253763 = 4880645) B4880645
theorem B2169175 : Blo 1927435 2169175 := bstep (se 1 (by rfl) ⟨1626881, by rfl⟩ : syracuseStep 2169175 = 3253763) B3253763
theorem B2892233 : Blo 1927435 2892233 := bstep (se 2 (by rfl) ⟨1084587, by rfl⟩ : syracuseStep 2892233 = 2169175) B2169175
theorem B1928155 : Blo 1927435 1928155 := bstep (se 1 (by rfl) ⟨1446116, by rfl⟩ : syracuseStep 1928155 = 2892233) B2892233
theorem B4118053 : Blo 1927435 4118053 := bbase (se 4 (by rfl) ⟨386067, by rfl⟩ : syracuseStep 4118053 = 772135) (by norm_num)
theorem B5490737 : Blo 1927435 5490737 := bstep (se 2 (by rfl) ⟨2059026, by rfl⟩ : syracuseStep 5490737 = 4118053) B4118053
theorem B3660491 : Blo 1927435 3660491 := bstep (se 1 (by rfl) ⟨2745368, by rfl⟩ : syracuseStep 3660491 = 5490737) B5490737
theorem B9761309 : Blo 1927435 9761309 := bstep (se 3 (by rfl) ⟨1830245, by rfl⟩ : syracuseStep 9761309 = 3660491) B3660491
theorem B6507539 : Blo 1927435 6507539 := bstep (se 1 (by rfl) ⟨4880654, by rfl⟩ : syracuseStep 6507539 = 9761309) B9761309
theorem B4338359 : Blo 1927435 4338359 := bstep (se 1 (by rfl) ⟨3253769, by rfl⟩ : syracuseStep 4338359 = 6507539) B6507539
theorem B2892239 : Blo 1927435 2892239 := bstep (se 1 (by rfl) ⟨2169179, by rfl⟩ : syracuseStep 2892239 = 4338359) B4338359
theorem B1928159 : Blo 1927435 1928159 := bstep (se 1 (by rfl) ⟨1446119, by rfl⟩ : syracuseStep 1928159 = 2892239) B2892239
theorem B2892245 : Blo 1927435 2892245 := bbase (se 7 (by rfl) ⟨33893, by rfl⟩ : syracuseStep 2892245 = 67787) (by norm_num)
theorem B1928163 : Blo 1927435 1928163 := bstep (se 1 (by rfl) ⟨1446122, by rfl⟩ : syracuseStep 1928163 = 2892245) B2892245
theorem B7321013 : Blo 1927435 7321013 := bbase (se 5 (by rfl) ⟨343172, by rfl⟩ : syracuseStep 7321013 = 686345) (by norm_num)
theorem B4880675 : Blo 1927435 4880675 := bstep (se 1 (by rfl) ⟨3660506, by rfl⟩ : syracuseStep 4880675 = 7321013) B7321013
theorem B3253783 : Blo 1927435 3253783 := bstep (se 1 (by rfl) ⟨2440337, by rfl⟩ : syracuseStep 3253783 = 4880675) B4880675
theorem B4338377 : Blo 1927435 4338377 := bstep (se 2 (by rfl) ⟨1626891, by rfl⟩ : syracuseStep 4338377 = 3253783) B3253783
theorem B2892251 : Blo 1927435 2892251 := bstep (se 1 (by rfl) ⟨2169188, by rfl⟩ : syracuseStep 2892251 = 4338377) B4338377
theorem B1928167 : Blo 1927435 1928167 := bstep (se 1 (by rfl) ⟨1446125, by rfl⟩ : syracuseStep 1928167 = 2892251) B2892251
theorem B2169193 : Blo 1927435 2169193 := bbase (se 2 (by rfl) ⟨813447, by rfl⟩ : syracuseStep 2169193 = 1626895) (by norm_num)
theorem B2892257 : Blo 1927435 2892257 := bstep (se 2 (by rfl) ⟨1084596, by rfl⟩ : syracuseStep 2892257 = 2169193) B2169193
theorem B1928171 : Blo 1927435 1928171 := bstep (se 1 (by rfl) ⟨1446128, by rfl⟩ : syracuseStep 1928171 = 2892257) B2892257
theorem B2931725 : Blo 1927435 2931725 := bbase (se 3 (by rfl) ⟨549698, by rfl⟩ : syracuseStep 2931725 = 1099397) (by norm_num)
theorem B7817933 : Blo 1927435 7817933 := bstep (se 3 (by rfl) ⟨1465862, by rfl⟩ : syracuseStep 7817933 = 2931725) B2931725
theorem B5211955 : Blo 1927435 5211955 := bstep (se 1 (by rfl) ⟨3908966, by rfl⟩ : syracuseStep 5211955 = 7817933) B7817933
theorem B6949273 : Blo 1927435 6949273 := bstep (se 2 (by rfl) ⟨2605977, by rfl⟩ : syracuseStep 6949273 = 5211955) B5211955
theorem B9265697 : Blo 1927435 9265697 := bstep (se 2 (by rfl) ⟨3474636, by rfl⟩ : syracuseStep 9265697 = 6949273) B6949273
theorem B6177131 : Blo 1927435 6177131 := bstep (se 1 (by rfl) ⟨4632848, by rfl⟩ : syracuseStep 6177131 = 9265697) B9265697
theorem B4118087 : Blo 1927435 4118087 := bstep (se 1 (by rfl) ⟨3088565, by rfl⟩ : syracuseStep 4118087 = 6177131) B6177131
theorem B10981565 : Blo 1927435 10981565 := bstep (se 3 (by rfl) ⟨2059043, by rfl⟩ : syracuseStep 10981565 = 4118087) B4118087
theorem B7321043 : Blo 1927435 7321043 := bstep (se 1 (by rfl) ⟨5490782, by rfl⟩ : syracuseStep 7321043 = 10981565) B10981565
theorem B4880695 : Blo 1927435 4880695 := bstep (se 1 (by rfl) ⟨3660521, by rfl⟩ : syracuseStep 4880695 = 7321043) B7321043
theorem B6507593 : Blo 1927435 6507593 := bstep (se 2 (by rfl) ⟨2440347, by rfl⟩ : syracuseStep 6507593 = 4880695) B4880695
theorem B4338395 : Blo 1927435 4338395 := bstep (se 1 (by rfl) ⟨3253796, by rfl⟩ : syracuseStep 4338395 = 6507593) B6507593
theorem B2892263 : Blo 1927435 2892263 := bstep (se 1 (by rfl) ⟨2169197, by rfl⟩ : syracuseStep 2892263 = 4338395) B4338395
theorem B1928175 : Blo 1927435 1928175 := bstep (se 1 (by rfl) ⟨1446131, by rfl⟩ : syracuseStep 1928175 = 2892263) B2892263
theorem B2892269 : Blo 1927435 2892269 := bbase (se 3 (by rfl) ⟨542300, by rfl⟩ : syracuseStep 2892269 = 1084601) (by norm_num)
theorem B1928179 : Blo 1927435 1928179 := bstep (se 1 (by rfl) ⟨1446134, by rfl⟩ : syracuseStep 1928179 = 2892269) B2892269
theorem B4338413 : Blo 1927435 4338413 := bbase (se 3 (by rfl) ⟨813452, by rfl⟩ : syracuseStep 4338413 = 1626905) (by norm_num)
theorem B2892275 : Blo 1927435 2892275 := bstep (se 1 (by rfl) ⟨2169206, by rfl⟩ : syracuseStep 2892275 = 4338413) B4338413
theorem B1928183 : Blo 1927435 1928183 := bstep (se 1 (by rfl) ⟨1446137, by rfl⟩ : syracuseStep 1928183 = 2892275) B2892275
theorem B2059057 : Blo 1927435 2059057 := bbase (se 2 (by rfl) ⟨772146, by rfl⟩ : syracuseStep 2059057 = 1544293) (by norm_num)
theorem B2745409 : Blo 1927435 2745409 := bstep (se 2 (by rfl) ⟨1029528, by rfl⟩ : syracuseStep 2745409 = 2059057) B2059057
theorem B3660545 : Blo 1927435 3660545 := bstep (se 2 (by rfl) ⟨1372704, by rfl⟩ : syracuseStep 3660545 = 2745409) B2745409
theorem B2440363 : Blo 1927435 2440363 := bstep (se 1 (by rfl) ⟨1830272, by rfl⟩ : syracuseStep 2440363 = 3660545) B3660545
theorem B3253817 : Blo 1927435 3253817 := bstep (se 2 (by rfl) ⟨1220181, by rfl⟩ : syracuseStep 3253817 = 2440363) B2440363
theorem B2169211 : Blo 1927435 2169211 := bstep (se 1 (by rfl) ⟨1626908, by rfl⟩ : syracuseStep 2169211 = 3253817) B3253817
theorem B2892281 : Blo 1927435 2892281 := bstep (se 2 (by rfl) ⟨1084605, by rfl⟩ : syracuseStep 2892281 = 2169211) B2169211
theorem B1928187 : Blo 1927435 1928187 := bstep (se 1 (by rfl) ⟨1446140, by rfl⟩ : syracuseStep 1928187 = 2892281) B2892281
theorem B11751509 : Blo 1927435 11751509 := bbase (se 8 (by rfl) ⟨68856, by rfl⟩ : syracuseStep 11751509 = 137713) (by norm_num)
theorem B7834339 : Blo 1927435 7834339 := bstep (se 1 (by rfl) ⟨5875754, by rfl⟩ : syracuseStep 7834339 = 11751509) B11751509
theorem B41783141 : Blo 1927435 41783141 := bstep (se 4 (by rfl) ⟨3917169, by rfl⟩ : syracuseStep 41783141 = 7834339) B7834339
theorem B27855427 : Blo 1927435 27855427 := bstep (se 1 (by rfl) ⟨20891570, by rfl⟩ : syracuseStep 27855427 = 41783141) B41783141
theorem B37140569 : Blo 1927435 37140569 := bstep (se 2 (by rfl) ⟨13927713, by rfl⟩ : syracuseStep 37140569 = 27855427) B27855427
theorem B24760379 : Blo 1927435 24760379 := bstep (se 1 (by rfl) ⟨18570284, by rfl⟩ : syracuseStep 24760379 = 37140569) B37140569
theorem B16506919 : Blo 1927435 16506919 := bstep (se 1 (by rfl) ⟨12380189, by rfl⟩ : syracuseStep 16506919 = 24760379) B24760379
theorem B88036901 : Blo 1927435 88036901 := bstep (se 4 (by rfl) ⟨8253459, by rfl⟩ : syracuseStep 88036901 = 16506919) B16506919
theorem B58691267 : Blo 1927435 58691267 := bstep (se 1 (by rfl) ⟨44018450, by rfl⟩ : syracuseStep 58691267 = 88036901) B88036901
theorem B39127511 : Blo 1927435 39127511 := bstep (se 1 (by rfl) ⟨29345633, by rfl⟩ : syracuseStep 39127511 = 58691267) B58691267
theorem B26085007 : Blo 1927435 26085007 := bstep (se 1 (by rfl) ⟨19563755, by rfl⟩ : syracuseStep 26085007 = 39127511) B39127511
theorem B34780009 : Blo 1927435 34780009 := bstep (se 2 (by rfl) ⟨13042503, by rfl⟩ : syracuseStep 34780009 = 26085007) B26085007
theorem B46373345 : Blo 1927435 46373345 := bstep (se 2 (by rfl) ⟨17390004, by rfl⟩ : syracuseStep 46373345 = 34780009) B34780009
theorem B30915563 : Blo 1927435 30915563 := bstep (se 1 (by rfl) ⟨23186672, by rfl⟩ : syracuseStep 30915563 = 46373345) B46373345
theorem B329766005 : Blo 1927435 329766005 := bstep (se 5 (by rfl) ⟨15457781, by rfl⟩ : syracuseStep 329766005 = 30915563) B30915563
theorem B219844003 : Blo 1927435 219844003 := bstep (se 1 (by rfl) ⟨164883002, by rfl⟩ : syracuseStep 219844003 = 329766005) B329766005
theorem B293125337 : Blo 1927435 293125337 := bstep (se 2 (by rfl) ⟨109922001, by rfl⟩ : syracuseStep 293125337 = 219844003) B219844003
theorem B195416891 : Blo 1927435 195416891 := bstep (se 1 (by rfl) ⟨146562668, by rfl⟩ : syracuseStep 195416891 = 293125337) B293125337
theorem B130277927 : Blo 1927435 130277927 := bstep (se 1 (by rfl) ⟨97708445, by rfl⟩ : syracuseStep 130277927 = 195416891) B195416891
theorem B347407805 : Blo 1927435 347407805 := bstep (se 3 (by rfl) ⟨65138963, by rfl⟩ : syracuseStep 347407805 = 130277927) B130277927
theorem B231605203 : Blo 1927435 231605203 := bstep (se 1 (by rfl) ⟨173703902, by rfl⟩ : syracuseStep 231605203 = 347407805) B347407805
theorem B308806937 : Blo 1927435 308806937 := bstep (se 2 (by rfl) ⟨115802601, by rfl⟩ : syracuseStep 308806937 = 231605203) B231605203
theorem B205871291 : Blo 1927435 205871291 := bstep (se 1 (by rfl) ⟨154403468, by rfl⟩ : syracuseStep 205871291 = 308806937) B308806937
theorem B137247527 : Blo 1927435 137247527 := bstep (se 1 (by rfl) ⟨102935645, by rfl⟩ : syracuseStep 137247527 = 205871291) B205871291
theorem B91498351 : Blo 1927435 91498351 := bstep (se 1 (by rfl) ⟨68623763, by rfl⟩ : syracuseStep 91498351 = 137247527) B137247527
theorem B121997801 : Blo 1927435 121997801 := bstep (se 2 (by rfl) ⟨45749175, by rfl⟩ : syracuseStep 121997801 = 91498351) B91498351
theorem B81331867 : Blo 1927435 81331867 := bstep (se 1 (by rfl) ⟨60998900, by rfl⟩ : syracuseStep 81331867 = 121997801) B121997801
theorem B108442489 : Blo 1927435 108442489 := bstep (se 2 (by rfl) ⟨40665933, by rfl⟩ : syracuseStep 108442489 = 81331867) B81331867
theorem B144589985 : Blo 1927435 144589985 := bstep (se 2 (by rfl) ⟨54221244, by rfl⟩ : syracuseStep 144589985 = 108442489) B108442489
theorem B96393323 : Blo 1927435 96393323 := bstep (se 1 (by rfl) ⟨72294992, by rfl⟩ : syracuseStep 96393323 = 144589985) B144589985
theorem B64262215 : Blo 1927435 64262215 := bstep (se 1 (by rfl) ⟨48196661, by rfl⟩ : syracuseStep 64262215 = 96393323) B96393323
theorem B85682953 : Blo 1927435 85682953 := bstep (se 2 (by rfl) ⟨32131107, by rfl⟩ : syracuseStep 85682953 = 64262215) B64262215
theorem B456975749 : Blo 1927435 456975749 := bstep (se 4 (by rfl) ⟨42841476, by rfl⟩ : syracuseStep 456975749 = 85682953) B85682953
theorem B304650499 : Blo 1927435 304650499 := bstep (se 1 (by rfl) ⟨228487874, by rfl⟩ : syracuseStep 304650499 = 456975749) B456975749
theorem B406200665 : Blo 1927435 406200665 := bstep (se 2 (by rfl) ⟨152325249, by rfl⟩ : syracuseStep 406200665 = 304650499) B304650499
theorem B270800443 : Blo 1927435 270800443 := bstep (se 1 (by rfl) ⟨203100332, by rfl⟩ : syracuseStep 270800443 = 406200665) B406200665
theorem B361067257 : Blo 1927435 361067257 := bstep (se 2 (by rfl) ⟨135400221, by rfl⟩ : syracuseStep 361067257 = 270800443) B270800443
theorem B481423009 : Blo 1927435 481423009 := bstep (se 2 (by rfl) ⟨180533628, by rfl⟩ : syracuseStep 481423009 = 361067257) B361067257
theorem B641897345 : Blo 1927435 641897345 := bstep (se 2 (by rfl) ⟨240711504, by rfl⟩ : syracuseStep 641897345 = 481423009) B481423009
theorem B1711726253 : Blo 1927435 1711726253 := bstep (se 3 (by rfl) ⟨320948672, by rfl⟩ : syracuseStep 1711726253 = 641897345) B641897345
theorem B1141150835 : Blo 1927435 1141150835 := bstep (se 1 (by rfl) ⟨855863126, by rfl⟩ : syracuseStep 1141150835 = 1711726253) B1711726253
theorem B760767223 : Blo 1927435 760767223 := bstep (se 1 (by rfl) ⟨570575417, by rfl⟩ : syracuseStep 760767223 = 1141150835) B1141150835
theorem B1014356297 : Blo 1927435 1014356297 := bstep (se 2 (by rfl) ⟨380383611, by rfl⟩ : syracuseStep 1014356297 = 760767223) B760767223
theorem B676237531 : Blo 1927435 676237531 := bstep (se 1 (by rfl) ⟨507178148, by rfl⟩ : syracuseStep 676237531 = 1014356297) B1014356297
theorem B901650041 : Blo 1927435 901650041 := bstep (se 2 (by rfl) ⟨338118765, by rfl⟩ : syracuseStep 901650041 = 676237531) B676237531
theorem B601100027 : Blo 1927435 601100027 := bstep (se 1 (by rfl) ⟨450825020, by rfl⟩ : syracuseStep 601100027 = 901650041) B901650041
theorem B400733351 : Blo 1927435 400733351 := bstep (se 1 (by rfl) ⟨300550013, by rfl⟩ : syracuseStep 400733351 = 601100027) B601100027
theorem B267155567 : Blo 1927435 267155567 := bstep (se 1 (by rfl) ⟨200366675, by rfl⟩ : syracuseStep 267155567 = 400733351) B400733351
theorem B178103711 : Blo 1927435 178103711 := bstep (se 1 (by rfl) ⟨133577783, by rfl⟩ : syracuseStep 178103711 = 267155567) B267155567
theorem B118735807 : Blo 1927435 118735807 := bstep (se 1 (by rfl) ⟨89051855, by rfl⟩ : syracuseStep 118735807 = 178103711) B178103711
theorem B158314409 : Blo 1927435 158314409 := bstep (se 2 (by rfl) ⟨59367903, by rfl⟩ : syracuseStep 158314409 = 118735807) B118735807
theorem B105542939 : Blo 1927435 105542939 := bstep (se 1 (by rfl) ⟨79157204, by rfl⟩ : syracuseStep 105542939 = 158314409) B158314409
theorem B70361959 : Blo 1927435 70361959 := bstep (se 1 (by rfl) ⟨52771469, by rfl⟩ : syracuseStep 70361959 = 105542939) B105542939
theorem B93815945 : Blo 1927435 93815945 := bstep (se 2 (by rfl) ⟨35180979, by rfl⟩ : syracuseStep 93815945 = 70361959) B70361959
theorem B62543963 : Blo 1927435 62543963 := bstep (se 1 (by rfl) ⟨46907972, by rfl⟩ : syracuseStep 62543963 = 93815945) B93815945
theorem B41695975 : Blo 1927435 41695975 := bstep (se 1 (by rfl) ⟨31271981, by rfl⟩ : syracuseStep 41695975 = 62543963) B62543963
theorem B55594633 : Blo 1927435 55594633 := bstep (se 2 (by rfl) ⟨20847987, by rfl⟩ : syracuseStep 55594633 = 41695975) B41695975
theorem B74126177 : Blo 1927435 74126177 := bstep (se 2 (by rfl) ⟨27797316, by rfl⟩ : syracuseStep 74126177 = 55594633) B55594633
theorem B49417451 : Blo 1927435 49417451 := bstep (se 1 (by rfl) ⟨37063088, by rfl⟩ : syracuseStep 49417451 = 74126177) B74126177
theorem B32944967 : Blo 1927435 32944967 := bstep (se 1 (by rfl) ⟨24708725, by rfl⟩ : syracuseStep 32944967 = 49417451) B49417451
theorem B21963311 : Blo 1927435 21963311 := bstep (se 1 (by rfl) ⟨16472483, by rfl⟩ : syracuseStep 21963311 = 32944967) B32944967
theorem B14642207 : Blo 1927435 14642207 := bstep (se 1 (by rfl) ⟨10981655, by rfl⟩ : syracuseStep 14642207 = 21963311) B21963311
theorem B9761471 : Blo 1927435 9761471 := bstep (se 1 (by rfl) ⟨7321103, by rfl⟩ : syracuseStep 9761471 = 14642207) B14642207
theorem B6507647 : Blo 1927435 6507647 := bstep (se 1 (by rfl) ⟨4880735, by rfl⟩ : syracuseStep 6507647 = 9761471) B9761471
theorem B4338431 : Blo 1927435 4338431 := bstep (se 1 (by rfl) ⟨3253823, by rfl⟩ : syracuseStep 4338431 = 6507647) B6507647
theorem B2892287 : Blo 1927435 2892287 := bstep (se 1 (by rfl) ⟨2169215, by rfl⟩ : syracuseStep 2892287 = 4338431) B4338431
theorem B1928191 : Blo 1927435 1928191 := bstep (se 1 (by rfl) ⟨1446143, by rfl⟩ : syracuseStep 1928191 = 2892287) B2892287
theorem B2892293 : Blo 1927435 2892293 := bbase (se 4 (by rfl) ⟨271152, by rfl⟩ : syracuseStep 2892293 = 542305) (by norm_num)
theorem B1928195 : Blo 1927435 1928195 := bstep (se 1 (by rfl) ⟨1446146, by rfl⟩ : syracuseStep 1928195 = 2892293) B2892293
theorem B3253837 : Blo 1927435 3253837 := bbase (se 3 (by rfl) ⟨610094, by rfl⟩ : syracuseStep 3253837 = 1220189) (by norm_num)
theorem B4338449 : Blo 1927435 4338449 := bstep (se 2 (by rfl) ⟨1626918, by rfl⟩ : syracuseStep 4338449 = 3253837) B3253837
theorem B2892299 : Blo 1927435 2892299 := bstep (se 1 (by rfl) ⟨2169224, by rfl⟩ : syracuseStep 2892299 = 4338449) B4338449
theorem B1928199 : Blo 1927435 1928199 := bstep (se 1 (by rfl) ⟨1446149, by rfl⟩ : syracuseStep 1928199 = 2892299) B2892299
theorem B2169229 : Blo 1927435 2169229 := bbase (se 3 (by rfl) ⟨406730, by rfl⟩ : syracuseStep 2169229 = 813461) (by norm_num)
theorem B2892305 : Blo 1927435 2892305 := bstep (se 2 (by rfl) ⟨1084614, by rfl⟩ : syracuseStep 2892305 = 2169229) B2169229
theorem B1928203 : Blo 1927435 1928203 := bstep (se 1 (by rfl) ⟨1446152, by rfl⟩ : syracuseStep 1928203 = 2892305) B2892305
theorem B6507701 : Blo 1927435 6507701 := bbase (se 5 (by rfl) ⟨305048, by rfl⟩ : syracuseStep 6507701 = 610097) (by norm_num)
theorem B4338467 : Blo 1927435 4338467 := bstep (se 1 (by rfl) ⟨3253850, by rfl⟩ : syracuseStep 4338467 = 6507701) B6507701
theorem B2892311 : Blo 1927435 2892311 := bstep (se 1 (by rfl) ⟨2169233, by rfl⟩ : syracuseStep 2892311 = 4338467) B4338467
theorem B1928207 : Blo 1927435 1928207 := bstep (se 1 (by rfl) ⟨1446155, by rfl⟩ : syracuseStep 1928207 = 2892311) B2892311
theorem B2892317 : Blo 1927435 2892317 := bbase (se 3 (by rfl) ⟨542309, by rfl⟩ : syracuseStep 2892317 = 1084619) (by norm_num)
theorem B1928211 : Blo 1927435 1928211 := bstep (se 1 (by rfl) ⟨1446158, by rfl⟩ : syracuseStep 1928211 = 2892317) B2892317
theorem B4338485 : Blo 1927435 4338485 := bbase (se 5 (by rfl) ⟨203366, by rfl⟩ : syracuseStep 4338485 = 406733) (by norm_num)
theorem B2892323 : Blo 1927435 2892323 := bstep (se 1 (by rfl) ⟨2169242, by rfl⟩ : syracuseStep 2892323 = 4338485) B4338485
theorem B1928215 : Blo 1927435 1928215 := bstep (se 1 (by rfl) ⟨1446161, by rfl⟩ : syracuseStep 1928215 = 2892323) B2892323
theorem B9265909 : Blo 1927435 9265909 := bbase (se 5 (by rfl) ⟨434339, by rfl⟩ : syracuseStep 9265909 = 868679) (by norm_num)
theorem B12354545 : Blo 1927435 12354545 := bstep (se 2 (by rfl) ⟨4632954, by rfl⟩ : syracuseStep 12354545 = 9265909) B9265909
theorem B8236363 : Blo 1927435 8236363 := bstep (se 1 (by rfl) ⟨6177272, by rfl⟩ : syracuseStep 8236363 = 12354545) B12354545
theorem B10981817 : Blo 1927435 10981817 := bstep (se 2 (by rfl) ⟨4118181, by rfl⟩ : syracuseStep 10981817 = 8236363) B8236363
theorem B7321211 : Blo 1927435 7321211 := bstep (se 1 (by rfl) ⟨5490908, by rfl⟩ : syracuseStep 7321211 = 10981817) B10981817
theorem B4880807 : Blo 1927435 4880807 := bstep (se 1 (by rfl) ⟨3660605, by rfl⟩ : syracuseStep 4880807 = 7321211) B7321211
theorem B3253871 : Blo 1927435 3253871 := bstep (se 1 (by rfl) ⟨2440403, by rfl⟩ : syracuseStep 3253871 = 4880807) B4880807
theorem B2169247 : Blo 1927435 2169247 := bstep (se 1 (by rfl) ⟨1626935, by rfl⟩ : syracuseStep 2169247 = 3253871) B3253871
theorem B2892329 : Blo 1927435 2892329 := bstep (se 2 (by rfl) ⟨1084623, by rfl⟩ : syracuseStep 2892329 = 2169247) B2169247
theorem B1928219 : Blo 1927435 1928219 := bstep (se 1 (by rfl) ⟨1446164, by rfl⟩ : syracuseStep 1928219 = 2892329) B2892329
theorem B3710557 : Blo 1927435 3710557 := bbase (se 3 (by rfl) ⟨695729, by rfl⟩ : syracuseStep 3710557 = 1391459) (by norm_num)
theorem B4947409 : Blo 1927435 4947409 := bstep (se 2 (by rfl) ⟨1855278, by rfl⟩ : syracuseStep 4947409 = 3710557) B3710557
theorem B6596545 : Blo 1927435 6596545 := bstep (se 2 (by rfl) ⟨2473704, by rfl⟩ : syracuseStep 6596545 = 4947409) B4947409
theorem B8795393 : Blo 1927435 8795393 := bstep (se 2 (by rfl) ⟨3298272, by rfl⟩ : syracuseStep 8795393 = 6596545) B6596545
theorem B5863595 : Blo 1927435 5863595 := bstep (se 1 (by rfl) ⟨4397696, by rfl⟩ : syracuseStep 5863595 = 8795393) B8795393
theorem B15636253 : Blo 1927435 15636253 := bstep (se 3 (by rfl) ⟨2931797, by rfl⟩ : syracuseStep 15636253 = 5863595) B5863595
theorem B20848337 : Blo 1927435 20848337 := bstep (se 2 (by rfl) ⟨7818126, by rfl⟩ : syracuseStep 20848337 = 15636253) B15636253
theorem B13898891 : Blo 1927435 13898891 := bstep (se 1 (by rfl) ⟨10424168, by rfl⟩ : syracuseStep 13898891 = 20848337) B20848337
theorem B9265927 : Blo 1927435 9265927 := bstep (se 1 (by rfl) ⟨6949445, by rfl⟩ : syracuseStep 9265927 = 13898891) B13898891
theorem B12354569 : Blo 1927435 12354569 := bstep (se 2 (by rfl) ⟨4632963, by rfl⟩ : syracuseStep 12354569 = 9265927) B9265927
theorem B8236379 : Blo 1927435 8236379 := bstep (se 1 (by rfl) ⟨6177284, by rfl⟩ : syracuseStep 8236379 = 12354569) B12354569
theorem B5490919 : Blo 1927435 5490919 := bstep (se 1 (by rfl) ⟨4118189, by rfl⟩ : syracuseStep 5490919 = 8236379) B8236379
theorem B7321225 : Blo 1927435 7321225 := bstep (se 2 (by rfl) ⟨2745459, by rfl⟩ : syracuseStep 7321225 = 5490919) B5490919
theorem B9761633 : Blo 1927435 9761633 := bstep (se 2 (by rfl) ⟨3660612, by rfl⟩ : syracuseStep 9761633 = 7321225) B7321225
theorem B6507755 : Blo 1927435 6507755 := bstep (se 1 (by rfl) ⟨4880816, by rfl⟩ : syracuseStep 6507755 = 9761633) B9761633
theorem B4338503 : Blo 1927435 4338503 := bstep (se 1 (by rfl) ⟨3253877, by rfl⟩ : syracuseStep 4338503 = 6507755) B6507755
theorem B2892335 : Blo 1927435 2892335 := bstep (se 1 (by rfl) ⟨2169251, by rfl⟩ : syracuseStep 2892335 = 4338503) B4338503
theorem B1928223 : Blo 1927435 1928223 := bstep (se 1 (by rfl) ⟨1446167, by rfl⟩ : syracuseStep 1928223 = 2892335) B2892335
theorem B2892341 : Blo 1927435 2892341 := bbase (se 5 (by rfl) ⟨135578, by rfl⟩ : syracuseStep 2892341 = 271157) (by norm_num)
theorem B1928227 : Blo 1927435 1928227 := bstep (se 1 (by rfl) ⟨1446170, by rfl⟩ : syracuseStep 1928227 = 2892341) B2892341
theorem B4880837 : Blo 1927435 4880837 := bbase (se 4 (by rfl) ⟨457578, by rfl⟩ : syracuseStep 4880837 = 915157) (by norm_num)
theorem B3253891 : Blo 1927435 3253891 := bstep (se 1 (by rfl) ⟨2440418, by rfl⟩ : syracuseStep 3253891 = 4880837) B4880837
theorem B4338521 : Blo 1927435 4338521 := bstep (se 2 (by rfl) ⟨1626945, by rfl⟩ : syracuseStep 4338521 = 3253891) B3253891
theorem B2892347 : Blo 1927435 2892347 := bstep (se 1 (by rfl) ⟨2169260, by rfl⟩ : syracuseStep 2892347 = 4338521) B4338521
theorem B1928231 : Blo 1927435 1928231 := bstep (se 1 (by rfl) ⟨1446173, by rfl⟩ : syracuseStep 1928231 = 2892347) B2892347
theorem B2169265 : Blo 1927435 2169265 := bbase (se 2 (by rfl) ⟨813474, by rfl⟩ : syracuseStep 2169265 = 1626949) (by norm_num)
theorem B2892353 : Blo 1927435 2892353 := bstep (se 2 (by rfl) ⟨1084632, by rfl⟩ : syracuseStep 2892353 = 2169265) B2169265
theorem B1928235 : Blo 1927435 1928235 := bstep (se 1 (by rfl) ⟨1446176, by rfl⟩ : syracuseStep 1928235 = 2892353) B2892353
theorem B5490965 : Blo 1927435 5490965 := bbase (se 6 (by rfl) ⟨128694, by rfl⟩ : syracuseStep 5490965 = 257389) (by norm_num)
theorem B3660643 : Blo 1927435 3660643 := bstep (se 1 (by rfl) ⟨2745482, by rfl⟩ : syracuseStep 3660643 = 5490965) B5490965
theorem B4880857 : Blo 1927435 4880857 := bstep (se 2 (by rfl) ⟨1830321, by rfl⟩ : syracuseStep 4880857 = 3660643) B3660643
theorem B6507809 : Blo 1927435 6507809 := bstep (se 2 (by rfl) ⟨2440428, by rfl⟩ : syracuseStep 6507809 = 4880857) B4880857
theorem B4338539 : Blo 1927435 4338539 := bstep (se 1 (by rfl) ⟨3253904, by rfl⟩ : syracuseStep 4338539 = 6507809) B6507809
theorem B2892359 : Blo 1927435 2892359 := bstep (se 1 (by rfl) ⟨2169269, by rfl⟩ : syracuseStep 2892359 = 4338539) B4338539
theorem B1928239 : Blo 1927435 1928239 := bstep (se 1 (by rfl) ⟨1446179, by rfl⟩ : syracuseStep 1928239 = 2892359) B2892359
theorem B2892365 : Blo 1927435 2892365 := bbase (se 3 (by rfl) ⟨542318, by rfl⟩ : syracuseStep 2892365 = 1084637) (by norm_num)
theorem B1928243 : Blo 1927435 1928243 := bstep (se 1 (by rfl) ⟨1446182, by rfl⟩ : syracuseStep 1928243 = 2892365) B2892365
theorem B4338557 : Blo 1927435 4338557 := bbase (se 3 (by rfl) ⟨813479, by rfl⟩ : syracuseStep 4338557 = 1626959) (by norm_num)
theorem B2892371 : Blo 1927435 2892371 := bstep (se 1 (by rfl) ⟨2169278, by rfl⟩ : syracuseStep 2892371 = 4338557) B4338557
theorem B1928247 : Blo 1927435 1928247 := bstep (se 1 (by rfl) ⟨1446185, by rfl⟩ : syracuseStep 1928247 = 2892371) B2892371
theorem B3253925 : Blo 1927435 3253925 := bbase (se 4 (by rfl) ⟨305055, by rfl⟩ : syracuseStep 3253925 = 610111) (by norm_num)
theorem B2169283 : Blo 1927435 2169283 := bstep (se 1 (by rfl) ⟨1626962, by rfl⟩ : syracuseStep 2169283 = 3253925) B3253925
theorem B2892377 : Blo 1927435 2892377 := bstep (se 2 (by rfl) ⟨1084641, by rfl⟩ : syracuseStep 2892377 = 2169283) B2169283
theorem B1928251 : Blo 1927435 1928251 := bstep (se 1 (by rfl) ⟨1446188, by rfl⟩ : syracuseStep 1928251 = 2892377) B2892377
theorem B2059129 : Blo 1927435 2059129 := bbase (se 2 (by rfl) ⟨772173, by rfl⟩ : syracuseStep 2059129 = 1544347) (by norm_num)
theorem B2745505 : Blo 1927435 2745505 := bstep (se 2 (by rfl) ⟨1029564, by rfl⟩ : syracuseStep 2745505 = 2059129) B2059129
theorem B14642693 : Blo 1927435 14642693 := bstep (se 4 (by rfl) ⟨1372752, by rfl⟩ : syracuseStep 14642693 = 2745505) B2745505
theorem B9761795 : Blo 1927435 9761795 := bstep (se 1 (by rfl) ⟨7321346, by rfl⟩ : syracuseStep 9761795 = 14642693) B14642693
theorem B6507863 : Blo 1927435 6507863 := bstep (se 1 (by rfl) ⟨4880897, by rfl⟩ : syracuseStep 6507863 = 9761795) B9761795
theorem B4338575 : Blo 1927435 4338575 := bstep (se 1 (by rfl) ⟨3253931, by rfl⟩ : syracuseStep 4338575 = 6507863) B6507863
theorem B2892383 : Blo 1927435 2892383 := bstep (se 1 (by rfl) ⟨2169287, by rfl⟩ : syracuseStep 2892383 = 4338575) B4338575
theorem B1928255 : Blo 1927435 1928255 := bstep (se 1 (by rfl) ⟨1446191, by rfl⟩ : syracuseStep 1928255 = 2892383) B2892383
theorem B2892389 : Blo 1927435 2892389 := bbase (se 4 (by rfl) ⟨271161, by rfl⟩ : syracuseStep 2892389 = 542323) (by norm_num)
theorem B1928259 : Blo 1927435 1928259 := bstep (se 1 (by rfl) ⟨1446194, by rfl⟩ : syracuseStep 1928259 = 2892389) B2892389
theorem B2745517 : Blo 1927435 2745517 := bbase (se 3 (by rfl) ⟨514784, by rfl⟩ : syracuseStep 2745517 = 1029569) (by norm_num)
theorem B3660689 : Blo 1927435 3660689 := bstep (se 2 (by rfl) ⟨1372758, by rfl⟩ : syracuseStep 3660689 = 2745517) B2745517
theorem B2440459 : Blo 1927435 2440459 := bstep (se 1 (by rfl) ⟨1830344, by rfl⟩ : syracuseStep 2440459 = 3660689) B3660689
theorem B3253945 : Blo 1927435 3253945 := bstep (se 2 (by rfl) ⟨1220229, by rfl⟩ : syracuseStep 3253945 = 2440459) B2440459
theorem B4338593 : Blo 1927435 4338593 := bstep (se 2 (by rfl) ⟨1626972, by rfl⟩ : syracuseStep 4338593 = 3253945) B3253945
theorem B2892395 : Blo 1927435 2892395 := bstep (se 1 (by rfl) ⟨2169296, by rfl⟩ : syracuseStep 2892395 = 4338593) B4338593
theorem B1928263 : Blo 1927435 1928263 := bstep (se 1 (by rfl) ⟨1446197, by rfl⟩ : syracuseStep 1928263 = 2892395) B2892395
theorem B2169301 : Blo 1927435 2169301 := bbase (se 7 (by rfl) ⟨25421, by rfl⟩ : syracuseStep 2169301 = 50843) (by norm_num)
theorem B2892401 : Blo 1927435 2892401 := bstep (se 2 (by rfl) ⟨1084650, by rfl⟩ : syracuseStep 2892401 = 2169301) B2169301
theorem B1928267 : Blo 1927435 1928267 := bstep (se 1 (by rfl) ⟨1446200, by rfl⟩ : syracuseStep 1928267 = 2892401) B2892401
theorem B2440469 : Blo 1927435 2440469 := bbase (se 6 (by rfl) ⟨57198, by rfl⟩ : syracuseStep 2440469 = 114397) (by norm_num)
theorem B6507917 : Blo 1927435 6507917 := bstep (se 3 (by rfl) ⟨1220234, by rfl⟩ : syracuseStep 6507917 = 2440469) B2440469
theorem B4338611 : Blo 1927435 4338611 := bstep (se 1 (by rfl) ⟨3253958, by rfl⟩ : syracuseStep 4338611 = 6507917) B6507917
theorem B2892407 : Blo 1927435 2892407 := bstep (se 1 (by rfl) ⟨2169305, by rfl⟩ : syracuseStep 2892407 = 4338611) B4338611
theorem B1928271 : Blo 1927435 1928271 := bstep (se 1 (by rfl) ⟨1446203, by rfl⟩ : syracuseStep 1928271 = 2892407) B2892407
theorem B2892413 : Blo 1927435 2892413 := bbase (se 3 (by rfl) ⟨542327, by rfl⟩ : syracuseStep 2892413 = 1084655) (by norm_num)
theorem B1928275 : Blo 1927435 1928275 := bstep (se 1 (by rfl) ⟨1446206, by rfl⟩ : syracuseStep 1928275 = 2892413) B2892413
theorem B4338629 : Blo 1927435 4338629 := bbase (se 4 (by rfl) ⟨406746, by rfl⟩ : syracuseStep 4338629 = 813493) (by norm_num)
theorem B2892419 : Blo 1927435 2892419 := bstep (se 1 (by rfl) ⟨2169314, by rfl⟩ : syracuseStep 2892419 = 4338629) B4338629
theorem B1928279 : Blo 1927435 1928279 := bstep (se 1 (by rfl) ⟨1446209, by rfl⟩ : syracuseStep 1928279 = 2892419) B2892419
theorem B4633109 : Blo 1927435 4633109 := bbase (se 6 (by rfl) ⟨108588, by rfl⟩ : syracuseStep 4633109 = 217177) (by norm_num)
theorem B3088739 : Blo 1927435 3088739 := bstep (se 1 (by rfl) ⟨2316554, by rfl⟩ : syracuseStep 3088739 = 4633109) B4633109
theorem B8236637 : Blo 1927435 8236637 := bstep (se 3 (by rfl) ⟨1544369, by rfl⟩ : syracuseStep 8236637 = 3088739) B3088739
theorem B5491091 : Blo 1927435 5491091 := bstep (se 1 (by rfl) ⟨4118318, by rfl⟩ : syracuseStep 5491091 = 8236637) B8236637
theorem B3660727 : Blo 1927435 3660727 := bstep (se 1 (by rfl) ⟨2745545, by rfl⟩ : syracuseStep 3660727 = 5491091) B5491091
theorem B4880969 : Blo 1927435 4880969 := bstep (se 2 (by rfl) ⟨1830363, by rfl⟩ : syracuseStep 4880969 = 3660727) B3660727
theorem B3253979 : Blo 1927435 3253979 := bstep (se 1 (by rfl) ⟨2440484, by rfl⟩ : syracuseStep 3253979 = 4880969) B4880969
theorem B2169319 : Blo 1927435 2169319 := bstep (se 1 (by rfl) ⟨1626989, by rfl⟩ : syracuseStep 2169319 = 3253979) B3253979
theorem B2892425 : Blo 1927435 2892425 := bstep (se 2 (by rfl) ⟨1084659, by rfl⟩ : syracuseStep 2892425 = 2169319) B2169319
theorem B1928283 : Blo 1927435 1928283 := bstep (se 1 (by rfl) ⟨1446212, by rfl⟩ : syracuseStep 1928283 = 2892425) B2892425
theorem B9761957 : Blo 1927435 9761957 := bbase (se 4 (by rfl) ⟨915183, by rfl⟩ : syracuseStep 9761957 = 1830367) (by norm_num)
theorem B6507971 : Blo 1927435 6507971 := bstep (se 1 (by rfl) ⟨4880978, by rfl⟩ : syracuseStep 6507971 = 9761957) B9761957
theorem B4338647 : Blo 1927435 4338647 := bstep (se 1 (by rfl) ⟨3253985, by rfl⟩ : syracuseStep 4338647 = 6507971) B6507971
theorem B2892431 : Blo 1927435 2892431 := bstep (se 1 (by rfl) ⟨2169323, by rfl⟩ : syracuseStep 2892431 = 4338647) B4338647
theorem B1928287 : Blo 1927435 1928287 := bstep (se 1 (by rfl) ⟨1446215, by rfl⟩ : syracuseStep 1928287 = 2892431) B2892431
theorem B2892437 : Blo 1927435 2892437 := bbase (se 6 (by rfl) ⟨67791, by rfl⟩ : syracuseStep 2892437 = 135583) (by norm_num)
theorem B1928291 : Blo 1927435 1928291 := bstep (se 1 (by rfl) ⟨1446218, by rfl⟩ : syracuseStep 1928291 = 2892437) B2892437
theorem B4397861 : Blo 1927435 4397861 := bbase (se 4 (by rfl) ⟨412299, by rfl⟩ : syracuseStep 4397861 = 824599) (by norm_num)
theorem B11727629 : Blo 1927435 11727629 := bstep (se 3 (by rfl) ⟨2198930, by rfl⟩ : syracuseStep 11727629 = 4397861) B4397861
theorem B7818419 : Blo 1927435 7818419 := bstep (se 1 (by rfl) ⟨5863814, by rfl⟩ : syracuseStep 7818419 = 11727629) B11727629
theorem B5212279 : Blo 1927435 5212279 := bstep (se 1 (by rfl) ⟨3909209, by rfl⟩ : syracuseStep 5212279 = 7818419) B7818419
theorem B27798821 : Blo 1927435 27798821 := bstep (se 4 (by rfl) ⟨2606139, by rfl⟩ : syracuseStep 27798821 = 5212279) B5212279
theorem B18532547 : Blo 1927435 18532547 := bstep (se 1 (by rfl) ⟨13899410, by rfl⟩ : syracuseStep 18532547 = 27798821) B27798821
theorem B12355031 : Blo 1927435 12355031 := bstep (se 1 (by rfl) ⟨9266273, by rfl⟩ : syracuseStep 12355031 = 18532547) B18532547
theorem B8236687 : Blo 1927435 8236687 := bstep (se 1 (by rfl) ⟨6177515, by rfl⟩ : syracuseStep 8236687 = 12355031) B12355031
theorem B10982249 : Blo 1927435 10982249 := bstep (se 2 (by rfl) ⟨4118343, by rfl⟩ : syracuseStep 10982249 = 8236687) B8236687
theorem B7321499 : Blo 1927435 7321499 := bstep (se 1 (by rfl) ⟨5491124, by rfl⟩ : syracuseStep 7321499 = 10982249) B10982249
theorem B4880999 : Blo 1927435 4880999 := bstep (se 1 (by rfl) ⟨3660749, by rfl⟩ : syracuseStep 4880999 = 7321499) B7321499
theorem B3253999 : Blo 1927435 3253999 := bstep (se 1 (by rfl) ⟨2440499, by rfl⟩ : syracuseStep 3253999 = 4880999) B4880999
theorem B4338665 : Blo 1927435 4338665 := bstep (se 2 (by rfl) ⟨1626999, by rfl⟩ : syracuseStep 4338665 = 3253999) B3253999
theorem B2892443 : Blo 1927435 2892443 := bstep (se 1 (by rfl) ⟨2169332, by rfl⟩ : syracuseStep 2892443 = 4338665) B4338665
theorem B1928295 : Blo 1927435 1928295 := bstep (se 1 (by rfl) ⟨1446221, by rfl⟩ : syracuseStep 1928295 = 2892443) B2892443
theorem B2169337 : Blo 1927435 2169337 := bbase (se 2 (by rfl) ⟨813501, by rfl⟩ : syracuseStep 2169337 = 1627003) (by norm_num)
theorem B2892449 : Blo 1927435 2892449 := bstep (se 2 (by rfl) ⟨1084668, by rfl⟩ : syracuseStep 2892449 = 2169337) B2169337
theorem B1928299 : Blo 1927435 1928299 := bstep (se 1 (by rfl) ⟨1446224, by rfl⟩ : syracuseStep 1928299 = 2892449) B2892449
theorem B6177541 : Blo 1927435 6177541 := bbase (se 4 (by rfl) ⟨579144, by rfl⟩ : syracuseStep 6177541 = 1158289) (by norm_num)
theorem B8236721 : Blo 1927435 8236721 := bstep (se 2 (by rfl) ⟨3088770, by rfl⟩ : syracuseStep 8236721 = 6177541) B6177541
theorem B5491147 : Blo 1927435 5491147 := bstep (se 1 (by rfl) ⟨4118360, by rfl⟩ : syracuseStep 5491147 = 8236721) B8236721
theorem B7321529 : Blo 1927435 7321529 := bstep (se 2 (by rfl) ⟨2745573, by rfl⟩ : syracuseStep 7321529 = 5491147) B5491147
theorem B4881019 : Blo 1927435 4881019 := bstep (se 1 (by rfl) ⟨3660764, by rfl⟩ : syracuseStep 4881019 = 7321529) B7321529
theorem B6508025 : Blo 1927435 6508025 := bstep (se 2 (by rfl) ⟨2440509, by rfl⟩ : syracuseStep 6508025 = 4881019) B4881019
theorem B4338683 : Blo 1927435 4338683 := bstep (se 1 (by rfl) ⟨3254012, by rfl⟩ : syracuseStep 4338683 = 6508025) B6508025
theorem B2892455 : Blo 1927435 2892455 := bstep (se 1 (by rfl) ⟨2169341, by rfl⟩ : syracuseStep 2892455 = 4338683) B4338683
theorem B1928303 : Blo 1927435 1928303 := bstep (se 1 (by rfl) ⟨1446227, by rfl⟩ : syracuseStep 1928303 = 2892455) B2892455
theorem B2892461 : Blo 1927435 2892461 := bbase (se 3 (by rfl) ⟨542336, by rfl⟩ : syracuseStep 2892461 = 1084673) (by norm_num)
theorem B1928307 : Blo 1927435 1928307 := bstep (se 1 (by rfl) ⟨1446230, by rfl⟩ : syracuseStep 1928307 = 2892461) B2892461
theorem B4338701 : Blo 1927435 4338701 := bbase (se 3 (by rfl) ⟨813506, by rfl⟩ : syracuseStep 4338701 = 1627013) (by norm_num)
theorem B2892467 : Blo 1927435 2892467 := bstep (se 1 (by rfl) ⟨2169350, by rfl⟩ : syracuseStep 2892467 = 4338701) B4338701
theorem B1928311 : Blo 1927435 1928311 := bstep (se 1 (by rfl) ⟨1446233, by rfl⟩ : syracuseStep 1928311 = 2892467) B2892467
theorem B2440525 : Blo 1927435 2440525 := bbase (se 3 (by rfl) ⟨457598, by rfl⟩ : syracuseStep 2440525 = 915197) (by norm_num)
theorem B3254033 : Blo 1927435 3254033 := bstep (se 2 (by rfl) ⟨1220262, by rfl⟩ : syracuseStep 3254033 = 2440525) B2440525
theorem B2169355 : Blo 1927435 2169355 := bstep (se 1 (by rfl) ⟨1627016, by rfl⟩ : syracuseStep 2169355 = 3254033) B3254033
theorem B2892473 : Blo 1927435 2892473 := bstep (se 2 (by rfl) ⟨1084677, by rfl⟩ : syracuseStep 2892473 = 2169355) B2169355
theorem B1928315 : Blo 1927435 1928315 := bstep (se 1 (by rfl) ⟨1446236, by rfl⟩ : syracuseStep 1928315 = 2892473) B2892473
theorem B35183317 : Blo 1927435 35183317 := bbase (se 7 (by rfl) ⟨412304, by rfl⟩ : syracuseStep 35183317 = 824609) (by norm_num)
theorem B46911089 : Blo 1927435 46911089 := bstep (se 2 (by rfl) ⟨17591658, by rfl⟩ : syracuseStep 46911089 = 35183317) B35183317
theorem B31274059 : Blo 1927435 31274059 := bstep (se 1 (by rfl) ⟨23455544, by rfl⟩ : syracuseStep 31274059 = 46911089) B46911089
theorem B41698745 : Blo 1927435 41698745 := bstep (se 2 (by rfl) ⟨15637029, by rfl⟩ : syracuseStep 41698745 = 31274059) B31274059
theorem B27799163 : Blo 1927435 27799163 := bstep (se 1 (by rfl) ⟨20849372, by rfl⟩ : syracuseStep 27799163 = 41698745) B41698745
theorem B18532775 : Blo 1927435 18532775 := bstep (se 1 (by rfl) ⟨13899581, by rfl⟩ : syracuseStep 18532775 = 27799163) B27799163
theorem B12355183 : Blo 1927435 12355183 := bstep (se 1 (by rfl) ⟨9266387, by rfl⟩ : syracuseStep 12355183 = 18532775) B18532775
theorem B16473577 : Blo 1927435 16473577 := bstep (se 2 (by rfl) ⟨6177591, by rfl⟩ : syracuseStep 16473577 = 12355183) B12355183
theorem B21964769 : Blo 1927435 21964769 := bstep (se 2 (by rfl) ⟨8236788, by rfl⟩ : syracuseStep 21964769 = 16473577) B16473577
theorem B14643179 : Blo 1927435 14643179 := bstep (se 1 (by rfl) ⟨10982384, by rfl⟩ : syracuseStep 14643179 = 21964769) B21964769
theorem B9762119 : Blo 1927435 9762119 := bstep (se 1 (by rfl) ⟨7321589, by rfl⟩ : syracuseStep 9762119 = 14643179) B14643179
theorem B6508079 : Blo 1927435 6508079 := bstep (se 1 (by rfl) ⟨4881059, by rfl⟩ : syracuseStep 6508079 = 9762119) B9762119
theorem B4338719 : Blo 1927435 4338719 := bstep (se 1 (by rfl) ⟨3254039, by rfl⟩ : syracuseStep 4338719 = 6508079) B6508079
theorem B2892479 : Blo 1927435 2892479 := bstep (se 1 (by rfl) ⟨2169359, by rfl⟩ : syracuseStep 2892479 = 4338719) B4338719
theorem B1928319 : Blo 1927435 1928319 := bstep (se 1 (by rfl) ⟨1446239, by rfl⟩ : syracuseStep 1928319 = 2892479) B2892479
theorem B2892485 : Blo 1927435 2892485 := bbase (se 4 (by rfl) ⟨271170, by rfl⟩ : syracuseStep 2892485 = 542341) (by norm_num)
theorem B1928323 : Blo 1927435 1928323 := bstep (se 1 (by rfl) ⟨1446242, by rfl⟩ : syracuseStep 1928323 = 2892485) B2892485
theorem B3254053 : Blo 1927435 3254053 := bbase (se 4 (by rfl) ⟨305067, by rfl⟩ : syracuseStep 3254053 = 610135) (by norm_num)
theorem B4338737 : Blo 1927435 4338737 := bstep (se 2 (by rfl) ⟨1627026, by rfl⟩ : syracuseStep 4338737 = 3254053) B3254053
theorem B2892491 : Blo 1927435 2892491 := bstep (se 1 (by rfl) ⟨2169368, by rfl⟩ : syracuseStep 2892491 = 4338737) B4338737
theorem B1928327 : Blo 1927435 1928327 := bstep (se 1 (by rfl) ⟨1446245, by rfl⟩ : syracuseStep 1928327 = 2892491) B2892491
theorem B2169373 : Blo 1927435 2169373 := bbase (se 3 (by rfl) ⟨406757, by rfl⟩ : syracuseStep 2169373 = 813515) (by norm_num)
theorem B2892497 : Blo 1927435 2892497 := bstep (se 2 (by rfl) ⟨1084686, by rfl⟩ : syracuseStep 2892497 = 2169373) B2169373
theorem B1928331 : Blo 1927435 1928331 := bstep (se 1 (by rfl) ⟨1446248, by rfl⟩ : syracuseStep 1928331 = 2892497) B2892497
theorem B6508133 : Blo 1927435 6508133 := bbase (se 4 (by rfl) ⟨610137, by rfl⟩ : syracuseStep 6508133 = 1220275) (by norm_num)
theorem B4338755 : Blo 1927435 4338755 := bstep (se 1 (by rfl) ⟨3254066, by rfl⟩ : syracuseStep 4338755 = 6508133) B6508133
theorem B2892503 : Blo 1927435 2892503 := bstep (se 1 (by rfl) ⟨2169377, by rfl⟩ : syracuseStep 2892503 = 4338755) B4338755
theorem B1928335 : Blo 1927435 1928335 := bstep (se 1 (by rfl) ⟨1446251, by rfl⟩ : syracuseStep 1928335 = 2892503) B2892503
theorem B2892509 : Blo 1927435 2892509 := bbase (se 3 (by rfl) ⟨542345, by rfl⟩ : syracuseStep 2892509 = 1084691) (by norm_num)
theorem B1928339 : Blo 1927435 1928339 := bstep (se 1 (by rfl) ⟨1446254, by rfl⟩ : syracuseStep 1928339 = 2892509) B2892509
theorem B4338773 : Blo 1927435 4338773 := bbase (se 8 (by rfl) ⟨25422, by rfl⟩ : syracuseStep 4338773 = 50845) (by norm_num)
theorem B2892515 : Blo 1927435 2892515 := bstep (se 1 (by rfl) ⟨2169386, by rfl⟩ : syracuseStep 2892515 = 4338773) B4338773
theorem B1928343 : Blo 1927435 1928343 := bstep (se 1 (by rfl) ⟨1446257, by rfl⟩ : syracuseStep 1928343 = 2892515) B2892515
theorem B5212421 : Blo 1927435 5212421 := bbase (se 4 (by rfl) ⟨488664, by rfl⟩ : syracuseStep 5212421 = 977329) (by norm_num)
theorem B3474947 : Blo 1927435 3474947 := bstep (se 1 (by rfl) ⟨2606210, by rfl⟩ : syracuseStep 3474947 = 5212421) B5212421
theorem B9266525 : Blo 1927435 9266525 := bstep (se 3 (by rfl) ⟨1737473, by rfl⟩ : syracuseStep 9266525 = 3474947) B3474947
theorem B6177683 : Blo 1927435 6177683 := bstep (se 1 (by rfl) ⟨4633262, by rfl⟩ : syracuseStep 6177683 = 9266525) B9266525
theorem B4118455 : Blo 1927435 4118455 := bstep (se 1 (by rfl) ⟨3088841, by rfl⟩ : syracuseStep 4118455 = 6177683) B6177683
theorem B5491273 : Blo 1927435 5491273 := bstep (se 2 (by rfl) ⟨2059227, by rfl⟩ : syracuseStep 5491273 = 4118455) B4118455
theorem B7321697 : Blo 1927435 7321697 := bstep (se 2 (by rfl) ⟨2745636, by rfl⟩ : syracuseStep 7321697 = 5491273) B5491273
theorem B4881131 : Blo 1927435 4881131 := bstep (se 1 (by rfl) ⟨3660848, by rfl⟩ : syracuseStep 4881131 = 7321697) B7321697
theorem B3254087 : Blo 1927435 3254087 := bstep (se 1 (by rfl) ⟨2440565, by rfl⟩ : syracuseStep 3254087 = 4881131) B4881131
theorem B2169391 : Blo 1927435 2169391 := bstep (se 1 (by rfl) ⟨1627043, by rfl⟩ : syracuseStep 2169391 = 3254087) B3254087
theorem B2892521 : Blo 1927435 2892521 := bstep (se 2 (by rfl) ⟨1084695, by rfl⟩ : syracuseStep 2892521 = 2169391) B2169391
theorem B1928347 : Blo 1927435 1928347 := bstep (se 1 (by rfl) ⟨1446260, by rfl⟩ : syracuseStep 1928347 = 2892521) B2892521
theorem B5943989 : Blo 1927435 5943989 := bbase (se 5 (by rfl) ⟨278624, by rfl⟩ : syracuseStep 5943989 = 557249) (by norm_num)
theorem B15850637 : Blo 1927435 15850637 := bstep (se 3 (by rfl) ⟨2971994, by rfl⟩ : syracuseStep 15850637 = 5943989) B5943989
theorem B10567091 : Blo 1927435 10567091 := bstep (se 1 (by rfl) ⟨7925318, by rfl⟩ : syracuseStep 10567091 = 15850637) B15850637
theorem B7044727 : Blo 1927435 7044727 := bstep (se 1 (by rfl) ⟨5283545, by rfl⟩ : syracuseStep 7044727 = 10567091) B10567091
theorem B9392969 : Blo 1927435 9392969 := bstep (se 2 (by rfl) ⟨3522363, by rfl⟩ : syracuseStep 9392969 = 7044727) B7044727
theorem B25047917 : Blo 1927435 25047917 := bstep (se 3 (by rfl) ⟨4696484, by rfl⟩ : syracuseStep 25047917 = 9392969) B9392969
theorem B16698611 : Blo 1927435 16698611 := bstep (se 1 (by rfl) ⟨12523958, by rfl⟩ : syracuseStep 16698611 = 25047917) B25047917
theorem B11132407 : Blo 1927435 11132407 := bstep (se 1 (by rfl) ⟨8349305, by rfl⟩ : syracuseStep 11132407 = 16698611) B16698611
theorem B59372837 : Blo 1927435 59372837 := bstep (se 4 (by rfl) ⟨5566203, by rfl⟩ : syracuseStep 59372837 = 11132407) B11132407
theorem B39581891 : Blo 1927435 39581891 := bstep (se 1 (by rfl) ⟨29686418, by rfl⟩ : syracuseStep 39581891 = 59372837) B59372837
theorem B26387927 : Blo 1927435 26387927 := bstep (se 1 (by rfl) ⟨19790945, by rfl⟩ : syracuseStep 26387927 = 39581891) B39581891
theorem B17591951 : Blo 1927435 17591951 := bstep (se 1 (by rfl) ⟨13193963, by rfl⟩ : syracuseStep 17591951 = 26387927) B26387927
theorem B46911869 : Blo 1927435 46911869 := bstep (se 3 (by rfl) ⟨8795975, by rfl⟩ : syracuseStep 46911869 = 17591951) B17591951
theorem B31274579 : Blo 1927435 31274579 := bstep (se 1 (by rfl) ⟨23455934, by rfl⟩ : syracuseStep 31274579 = 46911869) B46911869
theorem B20849719 : Blo 1927435 20849719 := bstep (se 1 (by rfl) ⟨15637289, by rfl⟩ : syracuseStep 20849719 = 31274579) B31274579
theorem B27799625 : Blo 1927435 27799625 := bstep (se 2 (by rfl) ⟨10424859, by rfl⟩ : syracuseStep 27799625 = 20849719) B20849719
theorem B18533083 : Blo 1927435 18533083 := bstep (se 1 (by rfl) ⟨13899812, by rfl⟩ : syracuseStep 18533083 = 27799625) B27799625
theorem B24710777 : Blo 1927435 24710777 := bstep (se 2 (by rfl) ⟨9266541, by rfl⟩ : syracuseStep 24710777 = 18533083) B18533083
theorem B16473851 : Blo 1927435 16473851 := bstep (se 1 (by rfl) ⟨12355388, by rfl⟩ : syracuseStep 16473851 = 24710777) B24710777
theorem B10982567 : Blo 1927435 10982567 := bstep (se 1 (by rfl) ⟨8236925, by rfl⟩ : syracuseStep 10982567 = 16473851) B16473851
theorem B7321711 : Blo 1927435 7321711 := bstep (se 1 (by rfl) ⟨5491283, by rfl⟩ : syracuseStep 7321711 = 10982567) B10982567
theorem B9762281 : Blo 1927435 9762281 := bstep (se 2 (by rfl) ⟨3660855, by rfl⟩ : syracuseStep 9762281 = 7321711) B7321711
theorem B6508187 : Blo 1927435 6508187 := bstep (se 1 (by rfl) ⟨4881140, by rfl⟩ : syracuseStep 6508187 = 9762281) B9762281
theorem B4338791 : Blo 1927435 4338791 := bstep (se 1 (by rfl) ⟨3254093, by rfl⟩ : syracuseStep 4338791 = 6508187) B6508187
theorem B2892527 : Blo 1927435 2892527 := bstep (se 1 (by rfl) ⟨2169395, by rfl⟩ : syracuseStep 2892527 = 4338791) B4338791
theorem B1928351 : Blo 1927435 1928351 := bstep (se 1 (by rfl) ⟨1446263, by rfl⟩ : syracuseStep 1928351 = 2892527) B2892527
theorem B2892533 : Blo 1927435 2892533 := bbase (se 5 (by rfl) ⟨135587, by rfl⟩ : syracuseStep 2892533 = 271175) (by norm_num)
theorem B1928355 : Blo 1927435 1928355 := bstep (se 1 (by rfl) ⟨1446266, by rfl⟩ : syracuseStep 1928355 = 2892533) B2892533
theorem B5212453 : Blo 1927435 5212453 := bbase (se 4 (by rfl) ⟨488667, by rfl⟩ : syracuseStep 5212453 = 977335) (by norm_num)
theorem B6949937 : Blo 1927435 6949937 := bstep (se 2 (by rfl) ⟨2606226, by rfl⟩ : syracuseStep 6949937 = 5212453) B5212453
theorem B4633291 : Blo 1927435 4633291 := bstep (se 1 (by rfl) ⟨3474968, by rfl⟩ : syracuseStep 4633291 = 6949937) B6949937
theorem B6177721 : Blo 1927435 6177721 := bstep (se 2 (by rfl) ⟨2316645, by rfl⟩ : syracuseStep 6177721 = 4633291) B4633291
theorem B8236961 : Blo 1927435 8236961 := bstep (se 2 (by rfl) ⟨3088860, by rfl⟩ : syracuseStep 8236961 = 6177721) B6177721
theorem B5491307 : Blo 1927435 5491307 := bstep (se 1 (by rfl) ⟨4118480, by rfl⟩ : syracuseStep 5491307 = 8236961) B8236961
theorem B3660871 : Blo 1927435 3660871 := bstep (se 1 (by rfl) ⟨2745653, by rfl⟩ : syracuseStep 3660871 = 5491307) B5491307
theorem B4881161 : Blo 1927435 4881161 := bstep (se 2 (by rfl) ⟨1830435, by rfl⟩ : syracuseStep 4881161 = 3660871) B3660871
theorem B3254107 : Blo 1927435 3254107 := bstep (se 1 (by rfl) ⟨2440580, by rfl⟩ : syracuseStep 3254107 = 4881161) B4881161
theorem B4338809 : Blo 1927435 4338809 := bstep (se 2 (by rfl) ⟨1627053, by rfl⟩ : syracuseStep 4338809 = 3254107) B3254107
theorem B2892539 : Blo 1927435 2892539 := bstep (se 1 (by rfl) ⟨2169404, by rfl⟩ : syracuseStep 2892539 = 4338809) B4338809
theorem B1928359 : Blo 1927435 1928359 := bstep (se 1 (by rfl) ⟨1446269, by rfl⟩ : syracuseStep 1928359 = 2892539) B2892539
theorem B2169409 : Blo 1927435 2169409 := bbase (se 2 (by rfl) ⟨813528, by rfl⟩ : syracuseStep 2169409 = 1627057) (by norm_num)
theorem B2892545 : Blo 1927435 2892545 := bstep (se 2 (by rfl) ⟨1084704, by rfl⟩ : syracuseStep 2892545 = 2169409) B2169409
theorem B1928363 : Blo 1927435 1928363 := bstep (se 1 (by rfl) ⟨1446272, by rfl⟩ : syracuseStep 1928363 = 2892545) B2892545
theorem B4881181 : Blo 1927435 4881181 := bbase (se 3 (by rfl) ⟨915221, by rfl⟩ : syracuseStep 4881181 = 1830443) (by norm_num)
theorem B6508241 : Blo 1927435 6508241 := bstep (se 2 (by rfl) ⟨2440590, by rfl⟩ : syracuseStep 6508241 = 4881181) B4881181
theorem B4338827 : Blo 1927435 4338827 := bstep (se 1 (by rfl) ⟨3254120, by rfl⟩ : syracuseStep 4338827 = 6508241) B6508241
theorem B2892551 : Blo 1927435 2892551 := bstep (se 1 (by rfl) ⟨2169413, by rfl⟩ : syracuseStep 2892551 = 4338827) B4338827
theorem B1928367 : Blo 1927435 1928367 := bstep (se 1 (by rfl) ⟨1446275, by rfl⟩ : syracuseStep 1928367 = 2892551) B2892551
theorem B2892557 : Blo 1927435 2892557 := bbase (se 3 (by rfl) ⟨542354, by rfl⟩ : syracuseStep 2892557 = 1084709) (by norm_num)
theorem B1928371 : Blo 1927435 1928371 := bstep (se 1 (by rfl) ⟨1446278, by rfl⟩ : syracuseStep 1928371 = 2892557) B2892557
theorem B4338845 : Blo 1927435 4338845 := bbase (se 3 (by rfl) ⟨813533, by rfl⟩ : syracuseStep 4338845 = 1627067) (by norm_num)
theorem B2892563 : Blo 1927435 2892563 := bstep (se 1 (by rfl) ⟨2169422, by rfl⟩ : syracuseStep 2892563 = 4338845) B4338845
theorem B1928375 : Blo 1927435 1928375 := bstep (se 1 (by rfl) ⟨1446281, by rfl⟩ : syracuseStep 1928375 = 2892563) B2892563
theorem B3254141 : Blo 1927435 3254141 := bbase (se 3 (by rfl) ⟨610151, by rfl⟩ : syracuseStep 3254141 = 1220303) (by norm_num)
theorem B2169427 : Blo 1927435 2169427 := bstep (se 1 (by rfl) ⟨1627070, by rfl⟩ : syracuseStep 2169427 = 3254141) B3254141
theorem B2892569 : Blo 1927435 2892569 := bstep (se 2 (by rfl) ⟨1084713, by rfl⟩ : syracuseStep 2892569 = 2169427) B2169427
theorem B1928379 : Blo 1927435 1928379 := bstep (se 1 (by rfl) ⟨1446284, by rfl⟩ : syracuseStep 1928379 = 2892569) B2892569
theorem B6177797 : Blo 1927435 6177797 := bbase (se 4 (by rfl) ⟨579168, by rfl⟩ : syracuseStep 6177797 = 1158337) (by norm_num)
theorem B4118531 : Blo 1927435 4118531 := bstep (se 1 (by rfl) ⟨3088898, by rfl⟩ : syracuseStep 4118531 = 6177797) B6177797
theorem B10982749 : Blo 1927435 10982749 := bstep (se 3 (by rfl) ⟨2059265, by rfl⟩ : syracuseStep 10982749 = 4118531) B4118531
theorem B14643665 : Blo 1927435 14643665 := bstep (se 2 (by rfl) ⟨5491374, by rfl⟩ : syracuseStep 14643665 = 10982749) B10982749
theorem B9762443 : Blo 1927435 9762443 := bstep (se 1 (by rfl) ⟨7321832, by rfl⟩ : syracuseStep 9762443 = 14643665) B14643665
theorem B6508295 : Blo 1927435 6508295 := bstep (se 1 (by rfl) ⟨4881221, by rfl⟩ : syracuseStep 6508295 = 9762443) B9762443
theorem B4338863 : Blo 1927435 4338863 := bstep (se 1 (by rfl) ⟨3254147, by rfl⟩ : syracuseStep 4338863 = 6508295) B6508295
theorem B2892575 : Blo 1927435 2892575 := bstep (se 1 (by rfl) ⟨2169431, by rfl⟩ : syracuseStep 2892575 = 4338863) B4338863
theorem B1928383 : Blo 1927435 1928383 := bstep (se 1 (by rfl) ⟨1446287, by rfl⟩ : syracuseStep 1928383 = 2892575) B2892575
theorem B2892581 : Blo 1927435 2892581 := bbase (se 4 (by rfl) ⟨271179, by rfl⟩ : syracuseStep 2892581 = 542359) (by norm_num)
theorem B1928387 : Blo 1927435 1928387 := bstep (se 1 (by rfl) ⟨1446290, by rfl⟩ : syracuseStep 1928387 = 2892581) B2892581
theorem B2440621 : Blo 1927435 2440621 := bbase (se 3 (by rfl) ⟨457616, by rfl⟩ : syracuseStep 2440621 = 915233) (by norm_num)
theorem B3254161 : Blo 1927435 3254161 := bstep (se 2 (by rfl) ⟨1220310, by rfl⟩ : syracuseStep 3254161 = 2440621) B2440621
theorem B4338881 : Blo 1927435 4338881 := bstep (se 2 (by rfl) ⟨1627080, by rfl⟩ : syracuseStep 4338881 = 3254161) B3254161
theorem B2892587 : Blo 1927435 2892587 := bstep (se 1 (by rfl) ⟨2169440, by rfl⟩ : syracuseStep 2892587 = 4338881) B4338881
theorem B1928391 : Blo 1927435 1928391 := bstep (se 1 (by rfl) ⟨1446293, by rfl⟩ : syracuseStep 1928391 = 2892587) B2892587
theorem B2169445 : Blo 1927435 2169445 := bbase (se 4 (by rfl) ⟨203385, by rfl⟩ : syracuseStep 2169445 = 406771) (by norm_num)
theorem B2892593 : Blo 1927435 2892593 := bstep (se 2 (by rfl) ⟨1084722, by rfl⟩ : syracuseStep 2892593 = 2169445) B2169445
theorem B1928395 : Blo 1927435 1928395 := bstep (se 1 (by rfl) ⟨1446296, by rfl⟩ : syracuseStep 1928395 = 2892593) B2892593
theorem B3088925 : Blo 1927435 3088925 := bbase (se 3 (by rfl) ⟨579173, by rfl⟩ : syracuseStep 3088925 = 1158347) (by norm_num)
theorem B2059283 : Blo 1927435 2059283 := bstep (se 1 (by rfl) ⟨1544462, by rfl⟩ : syracuseStep 2059283 = 3088925) B3088925
theorem B5491421 : Blo 1927435 5491421 := bstep (se 3 (by rfl) ⟨1029641, by rfl⟩ : syracuseStep 5491421 = 2059283) B2059283
theorem B3660947 : Blo 1927435 3660947 := bstep (se 1 (by rfl) ⟨2745710, by rfl⟩ : syracuseStep 3660947 = 5491421) B5491421
theorem B2440631 : Blo 1927435 2440631 := bstep (se 1 (by rfl) ⟨1830473, by rfl⟩ : syracuseStep 2440631 = 3660947) B3660947
theorem B6508349 : Blo 1927435 6508349 := bstep (se 3 (by rfl) ⟨1220315, by rfl⟩ : syracuseStep 6508349 = 2440631) B2440631
theorem B4338899 : Blo 1927435 4338899 := bstep (se 1 (by rfl) ⟨3254174, by rfl⟩ : syracuseStep 4338899 = 6508349) B6508349
theorem B2892599 : Blo 1927435 2892599 := bstep (se 1 (by rfl) ⟨2169449, by rfl⟩ : syracuseStep 2892599 = 4338899) B4338899
theorem B1928399 : Blo 1927435 1928399 := bstep (se 1 (by rfl) ⟨1446299, by rfl⟩ : syracuseStep 1928399 = 2892599) B2892599
theorem B2892605 : Blo 1927435 2892605 := bbase (se 3 (by rfl) ⟨542363, by rfl⟩ : syracuseStep 2892605 = 1084727) (by norm_num)
theorem B1928403 : Blo 1927435 1928403 := bstep (se 1 (by rfl) ⟨1446302, by rfl⟩ : syracuseStep 1928403 = 2892605) B2892605
theorem B4338917 : Blo 1927435 4338917 := bbase (se 4 (by rfl) ⟨406773, by rfl⟩ : syracuseStep 4338917 = 813547) (by norm_num)
theorem B2892611 : Blo 1927435 2892611 := bstep (se 1 (by rfl) ⟨2169458, by rfl⟩ : syracuseStep 2892611 = 4338917) B4338917
theorem B1928407 : Blo 1927435 1928407 := bstep (se 1 (by rfl) ⟨1446305, by rfl⟩ : syracuseStep 1928407 = 2892611) B2892611
theorem B4881293 : Blo 1927435 4881293 := bbase (se 3 (by rfl) ⟨915242, by rfl⟩ : syracuseStep 4881293 = 1830485) (by norm_num)
theorem B3254195 : Blo 1927435 3254195 := bstep (se 1 (by rfl) ⟨2440646, by rfl⟩ : syracuseStep 3254195 = 4881293) B4881293
theorem B2169463 : Blo 1927435 2169463 := bstep (se 1 (by rfl) ⟨1627097, by rfl⟩ : syracuseStep 2169463 = 3254195) B3254195
theorem B2892617 : Blo 1927435 2892617 := bstep (se 2 (by rfl) ⟨1084731, by rfl⟩ : syracuseStep 2892617 = 2169463) B2169463
theorem B1928411 : Blo 1927435 1928411 := bstep (se 1 (by rfl) ⟨1446308, by rfl⟩ : syracuseStep 1928411 = 2892617) B2892617
theorem B2745733 : Blo 1927435 2745733 := bbase (se 4 (by rfl) ⟨257412, by rfl⟩ : syracuseStep 2745733 = 514825) (by norm_num)
theorem B3660977 : Blo 1927435 3660977 := bstep (se 2 (by rfl) ⟨1372866, by rfl⟩ : syracuseStep 3660977 = 2745733) B2745733
theorem B9762605 : Blo 1927435 9762605 := bstep (se 3 (by rfl) ⟨1830488, by rfl⟩ : syracuseStep 9762605 = 3660977) B3660977
theorem B6508403 : Blo 1927435 6508403 := bstep (se 1 (by rfl) ⟨4881302, by rfl⟩ : syracuseStep 6508403 = 9762605) B9762605
theorem B4338935 : Blo 1927435 4338935 := bstep (se 1 (by rfl) ⟨3254201, by rfl⟩ : syracuseStep 4338935 = 6508403) B6508403
theorem B2892623 : Blo 1927435 2892623 := bstep (se 1 (by rfl) ⟨2169467, by rfl⟩ : syracuseStep 2892623 = 4338935) B4338935
theorem B1928415 : Blo 1927435 1928415 := bstep (se 1 (by rfl) ⟨1446311, by rfl⟩ : syracuseStep 1928415 = 2892623) B2892623
theorem B2892629 : Blo 1927435 2892629 := bbase (se 9 (by rfl) ⟨8474, by rfl⟩ : syracuseStep 2892629 = 16949) (by norm_num)
theorem B1928419 : Blo 1927435 1928419 := bstep (se 1 (by rfl) ⟨1446314, by rfl⟩ : syracuseStep 1928419 = 2892629) B2892629
theorem B4633445 : Blo 1927435 4633445 := bbase (se 4 (by rfl) ⟨434385, by rfl⟩ : syracuseStep 4633445 = 868771) (by norm_num)
theorem B3088963 : Blo 1927435 3088963 := bstep (se 1 (by rfl) ⟨2316722, by rfl⟩ : syracuseStep 3088963 = 4633445) B4633445
theorem B4118617 : Blo 1927435 4118617 := bstep (se 2 (by rfl) ⟨1544481, by rfl⟩ : syracuseStep 4118617 = 3088963) B3088963
theorem B5491489 : Blo 1927435 5491489 := bstep (se 2 (by rfl) ⟨2059308, by rfl⟩ : syracuseStep 5491489 = 4118617) B4118617
theorem B7321985 : Blo 1927435 7321985 := bstep (se 2 (by rfl) ⟨2745744, by rfl⟩ : syracuseStep 7321985 = 5491489) B5491489
theorem B4881323 : Blo 1927435 4881323 := bstep (se 1 (by rfl) ⟨3660992, by rfl⟩ : syracuseStep 4881323 = 7321985) B7321985
theorem B3254215 : Blo 1927435 3254215 := bstep (se 1 (by rfl) ⟨2440661, by rfl⟩ : syracuseStep 3254215 = 4881323) B4881323
theorem B4338953 : Blo 1927435 4338953 := bstep (se 2 (by rfl) ⟨1627107, by rfl⟩ : syracuseStep 4338953 = 3254215) B3254215
theorem B2892635 : Blo 1927435 2892635 := bstep (se 1 (by rfl) ⟨2169476, by rfl⟩ : syracuseStep 2892635 = 4338953) B4338953
theorem B1928423 : Blo 1927435 1928423 := bstep (se 1 (by rfl) ⟨1446317, by rfl⟩ : syracuseStep 1928423 = 2892635) B2892635
theorem B2169481 : Blo 1927435 2169481 := bbase (se 2 (by rfl) ⟨813555, by rfl⟩ : syracuseStep 2169481 = 1627111) (by norm_num)
theorem B2892641 : Blo 1927435 2892641 := bstep (se 2 (by rfl) ⟨1084740, by rfl⟩ : syracuseStep 2892641 = 2169481) B2169481
theorem B1928427 : Blo 1927435 1928427 := bstep (se 1 (by rfl) ⟨1446320, by rfl⟩ : syracuseStep 1928427 = 2892641) B2892641
theorem B8796341 : Blo 1927435 8796341 := bbase (se 5 (by rfl) ⟨412328, by rfl⟩ : syracuseStep 8796341 = 824657) (by norm_num)
theorem B5864227 : Blo 1927435 5864227 := bstep (se 1 (by rfl) ⟨4398170, by rfl⟩ : syracuseStep 5864227 = 8796341) B8796341
theorem B31275877 : Blo 1927435 31275877 := bstep (se 4 (by rfl) ⟨2932113, by rfl⟩ : syracuseStep 31275877 = 5864227) B5864227
theorem B41701169 : Blo 1927435 41701169 := bstep (se 2 (by rfl) ⟨15637938, by rfl⟩ : syracuseStep 41701169 = 31275877) B31275877
theorem B27800779 : Blo 1927435 27800779 := bstep (se 1 (by rfl) ⟨20850584, by rfl⟩ : syracuseStep 27800779 = 41701169) B41701169
theorem B37067705 : Blo 1927435 37067705 := bstep (se 2 (by rfl) ⟨13900389, by rfl⟩ : syracuseStep 37067705 = 27800779) B27800779
theorem B24711803 : Blo 1927435 24711803 := bstep (se 1 (by rfl) ⟨18533852, by rfl⟩ : syracuseStep 24711803 = 37067705) B37067705
theorem B16474535 : Blo 1927435 16474535 := bstep (se 1 (by rfl) ⟨12355901, by rfl⟩ : syracuseStep 16474535 = 24711803) B24711803
theorem B10983023 : Blo 1927435 10983023 := bstep (se 1 (by rfl) ⟨8237267, by rfl⟩ : syracuseStep 10983023 = 16474535) B16474535
theorem B7322015 : Blo 1927435 7322015 := bstep (se 1 (by rfl) ⟨5491511, by rfl⟩ : syracuseStep 7322015 = 10983023) B10983023
theorem B4881343 : Blo 1927435 4881343 := bstep (se 1 (by rfl) ⟨3661007, by rfl⟩ : syracuseStep 4881343 = 7322015) B7322015
theorem B6508457 : Blo 1927435 6508457 := bstep (se 2 (by rfl) ⟨2440671, by rfl⟩ : syracuseStep 6508457 = 4881343) B4881343
theorem B4338971 : Blo 1927435 4338971 := bstep (se 1 (by rfl) ⟨3254228, by rfl⟩ : syracuseStep 4338971 = 6508457) B6508457
theorem B2892647 : Blo 1927435 2892647 := bstep (se 1 (by rfl) ⟨2169485, by rfl⟩ : syracuseStep 2892647 = 4338971) B4338971
theorem B1928431 : Blo 1927435 1928431 := bstep (se 1 (by rfl) ⟨1446323, by rfl⟩ : syracuseStep 1928431 = 2892647) B2892647
theorem B2892653 : Blo 1927435 2892653 := bbase (se 3 (by rfl) ⟨542372, by rfl⟩ : syracuseStep 2892653 = 1084745) (by norm_num)
theorem B1928435 : Blo 1927435 1928435 := bstep (se 1 (by rfl) ⟨1446326, by rfl⟩ : syracuseStep 1928435 = 2892653) B2892653
theorem B4338989 : Blo 1927435 4338989 := bbase (se 3 (by rfl) ⟨813560, by rfl⟩ : syracuseStep 4338989 = 1627121) (by norm_num)
theorem B2892659 : Blo 1927435 2892659 := bstep (se 1 (by rfl) ⟨2169494, by rfl⟩ : syracuseStep 2892659 = 4338989) B4338989
theorem B1928439 : Blo 1927435 1928439 := bstep (se 1 (by rfl) ⟨1446329, by rfl⟩ : syracuseStep 1928439 = 2892659) B2892659
theorem B2932133 : Blo 1927435 2932133 := bbase (se 4 (by rfl) ⟨274887, by rfl⟩ : syracuseStep 2932133 = 549775) (by norm_num)
theorem B7819021 : Blo 1927435 7819021 := bstep (se 3 (by rfl) ⟨1466066, by rfl⟩ : syracuseStep 7819021 = 2932133) B2932133
theorem B10425361 : Blo 1927435 10425361 := bstep (se 2 (by rfl) ⟨3909510, by rfl⟩ : syracuseStep 10425361 = 7819021) B7819021
theorem B13900481 : Blo 1927435 13900481 := bstep (se 2 (by rfl) ⟨5212680, by rfl⟩ : syracuseStep 13900481 = 10425361) B10425361
theorem B9266987 : Blo 1927435 9266987 := bstep (se 1 (by rfl) ⟨6950240, by rfl⟩ : syracuseStep 9266987 = 13900481) B13900481
theorem B6177991 : Blo 1927435 6177991 := bstep (se 1 (by rfl) ⟨4633493, by rfl⟩ : syracuseStep 6177991 = 9266987) B9266987
theorem B8237321 : Blo 1927435 8237321 := bstep (se 2 (by rfl) ⟨3088995, by rfl⟩ : syracuseStep 8237321 = 6177991) B6177991
theorem B5491547 : Blo 1927435 5491547 := bstep (se 1 (by rfl) ⟨4118660, by rfl⟩ : syracuseStep 5491547 = 8237321) B8237321
theorem B3661031 : Blo 1927435 3661031 := bstep (se 1 (by rfl) ⟨2745773, by rfl⟩ : syracuseStep 3661031 = 5491547) B5491547
theorem B2440687 : Blo 1927435 2440687 := bstep (se 1 (by rfl) ⟨1830515, by rfl⟩ : syracuseStep 2440687 = 3661031) B3661031
theorem B3254249 : Blo 1927435 3254249 := bstep (se 2 (by rfl) ⟨1220343, by rfl⟩ : syracuseStep 3254249 = 2440687) B2440687
theorem B2169499 : Blo 1927435 2169499 := bstep (se 1 (by rfl) ⟨1627124, by rfl⟩ : syracuseStep 2169499 = 3254249) B3254249
theorem B2892665 : Blo 1927435 2892665 := bstep (se 2 (by rfl) ⟨1084749, by rfl⟩ : syracuseStep 2892665 = 2169499) B2169499
theorem B1928443 : Blo 1927435 1928443 := bstep (se 1 (by rfl) ⟨1446332, by rfl⟩ : syracuseStep 1928443 = 2892665) B2892665
theorem B18534005 : Blo 1927435 18534005 := bbase (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) (by norm_num)
theorem B12356003 : Blo 1927435 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B32949341 : Blo 1927435 32949341 := bstep (se 3 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 32949341 = 12356003) B12356003
theorem B21966227 : Blo 1927435 21966227 := bstep (se 1 (by rfl) ⟨16474670, by rfl⟩ : syracuseStep 21966227 = 32949341) B32949341
theorem B14644151 : Blo 1927435 14644151 := bstep (se 1 (by rfl) ⟨10983113, by rfl⟩ : syracuseStep 14644151 = 21966227) B21966227
theorem B9762767 : Blo 1927435 9762767 := bstep (se 1 (by rfl) ⟨7322075, by rfl⟩ : syracuseStep 9762767 = 14644151) B14644151
theorem B6508511 : Blo 1927435 6508511 := bstep (se 1 (by rfl) ⟨4881383, by rfl⟩ : syracuseStep 6508511 = 9762767) B9762767
theorem B4339007 : Blo 1927435 4339007 := bstep (se 1 (by rfl) ⟨3254255, by rfl⟩ : syracuseStep 4339007 = 6508511) B6508511
theorem B2892671 : Blo 1927435 2892671 := bstep (se 1 (by rfl) ⟨2169503, by rfl⟩ : syracuseStep 2892671 = 4339007) B4339007
theorem B1928447 : Blo 1927435 1928447 := bstep (se 1 (by rfl) ⟨1446335, by rfl⟩ : syracuseStep 1928447 = 2892671) B2892671
theorem B2892677 : Blo 1927435 2892677 := bbase (se 4 (by rfl) ⟨271188, by rfl⟩ : syracuseStep 2892677 = 542377) (by norm_num)
theorem B1928451 : Blo 1927435 1928451 := bstep (se 1 (by rfl) ⟨1446338, by rfl⟩ : syracuseStep 1928451 = 2892677) B2892677
theorem B3254269 : Blo 1927435 3254269 := bbase (se 3 (by rfl) ⟨610175, by rfl⟩ : syracuseStep 3254269 = 1220351) (by norm_num)
theorem B4339025 : Blo 1927435 4339025 := bstep (se 2 (by rfl) ⟨1627134, by rfl⟩ : syracuseStep 4339025 = 3254269) B3254269
theorem B2892683 : Blo 1927435 2892683 := bstep (se 1 (by rfl) ⟨2169512, by rfl⟩ : syracuseStep 2892683 = 4339025) B4339025
theorem B1928455 : Blo 1927435 1928455 := bstep (se 1 (by rfl) ⟨1446341, by rfl⟩ : syracuseStep 1928455 = 2892683) B2892683
theorem B2169517 : Blo 1927435 2169517 := bbase (se 3 (by rfl) ⟨406784, by rfl⟩ : syracuseStep 2169517 = 813569) (by norm_num)
theorem B2892689 : Blo 1927435 2892689 := bstep (se 2 (by rfl) ⟨1084758, by rfl⟩ : syracuseStep 2892689 = 2169517) B2169517
theorem B1928459 : Blo 1927435 1928459 := bstep (se 1 (by rfl) ⟨1446344, by rfl⟩ : syracuseStep 1928459 = 2892689) B2892689
theorem B6508565 : Blo 1927435 6508565 := bbase (se 6 (by rfl) ⟨152544, by rfl⟩ : syracuseStep 6508565 = 305089) (by norm_num)
theorem B4339043 : Blo 1927435 4339043 := bstep (se 1 (by rfl) ⟨3254282, by rfl⟩ : syracuseStep 4339043 = 6508565) B6508565
theorem B2892695 : Blo 1927435 2892695 := bstep (se 1 (by rfl) ⟨2169521, by rfl⟩ : syracuseStep 2892695 = 4339043) B4339043
theorem B1928463 : Blo 1927435 1928463 := bstep (se 1 (by rfl) ⟨1446347, by rfl⟩ : syracuseStep 1928463 = 2892695) B2892695
theorem B2892701 : Blo 1927435 2892701 := bbase (se 3 (by rfl) ⟨542381, by rfl⟩ : syracuseStep 2892701 = 1084763) (by norm_num)
theorem B1928467 : Blo 1927435 1928467 := bstep (se 1 (by rfl) ⟨1446350, by rfl⟩ : syracuseStep 1928467 = 2892701) B2892701
theorem B4339061 : Blo 1927435 4339061 := bbase (se 5 (by rfl) ⟨203393, by rfl⟩ : syracuseStep 4339061 = 406787) (by norm_num)
theorem B2892707 : Blo 1927435 2892707 := bstep (se 1 (by rfl) ⟨2169530, by rfl⟩ : syracuseStep 2892707 = 4339061) B4339061
theorem B1928471 : Blo 1927435 1928471 := bstep (se 1 (by rfl) ⟨1446353, by rfl⟩ : syracuseStep 1928471 = 2892707) B2892707
theorem B5566565 : Blo 1927435 5566565 := bbase (se 4 (by rfl) ⟨521865, by rfl⟩ : syracuseStep 5566565 = 1043731) (by norm_num)
theorem B3711043 : Blo 1927435 3711043 := bstep (se 1 (by rfl) ⟨2783282, by rfl⟩ : syracuseStep 3711043 = 5566565) B5566565
theorem B4948057 : Blo 1927435 4948057 := bstep (se 2 (by rfl) ⟨1855521, by rfl⟩ : syracuseStep 4948057 = 3711043) B3711043
theorem B6597409 : Blo 1927435 6597409 := bstep (se 2 (by rfl) ⟨2474028, by rfl⟩ : syracuseStep 6597409 = 4948057) B4948057
theorem B8796545 : Blo 1927435 8796545 := bstep (se 2 (by rfl) ⟨3298704, by rfl⟩ : syracuseStep 8796545 = 6597409) B6597409
theorem B5864363 : Blo 1927435 5864363 := bstep (se 1 (by rfl) ⟨4398272, by rfl⟩ : syracuseStep 5864363 = 8796545) B8796545
theorem B3909575 : Blo 1927435 3909575 := bstep (se 1 (by rfl) ⟨2932181, by rfl⟩ : syracuseStep 3909575 = 5864363) B5864363
theorem B2606383 : Blo 1927435 2606383 := bstep (se 1 (by rfl) ⟨1954787, by rfl⟩ : syracuseStep 2606383 = 3909575) B3909575
theorem B13900709 : Blo 1927435 13900709 := bstep (se 4 (by rfl) ⟨1303191, by rfl⟩ : syracuseStep 13900709 = 2606383) B2606383
theorem B9267139 : Blo 1927435 9267139 := bstep (se 1 (by rfl) ⟨6950354, by rfl⟩ : syracuseStep 9267139 = 13900709) B13900709
theorem B12356185 : Blo 1927435 12356185 := bstep (se 2 (by rfl) ⟨4633569, by rfl⟩ : syracuseStep 12356185 = 9267139) B9267139
theorem B16474913 : Blo 1927435 16474913 := bstep (se 2 (by rfl) ⟨6178092, by rfl⟩ : syracuseStep 16474913 = 12356185) B12356185
theorem B10983275 : Blo 1927435 10983275 := bstep (se 1 (by rfl) ⟨8237456, by rfl⟩ : syracuseStep 10983275 = 16474913) B16474913
theorem B7322183 : Blo 1927435 7322183 := bstep (se 1 (by rfl) ⟨5491637, by rfl⟩ : syracuseStep 7322183 = 10983275) B10983275
theorem B4881455 : Blo 1927435 4881455 := bstep (se 1 (by rfl) ⟨3661091, by rfl⟩ : syracuseStep 4881455 = 7322183) B7322183
theorem B3254303 : Blo 1927435 3254303 := bstep (se 1 (by rfl) ⟨2440727, by rfl⟩ : syracuseStep 3254303 = 4881455) B4881455
theorem B2169535 : Blo 1927435 2169535 := bstep (se 1 (by rfl) ⟨1627151, by rfl⟩ : syracuseStep 2169535 = 3254303) B3254303
theorem B2892713 : Blo 1927435 2892713 := bstep (se 2 (by rfl) ⟨1084767, by rfl⟩ : syracuseStep 2892713 = 2169535) B2169535
theorem B1928475 : Blo 1927435 1928475 := bstep (se 1 (by rfl) ⟨1446356, by rfl⟩ : syracuseStep 1928475 = 2892713) B2892713
theorem B7322197 : Blo 1927435 7322197 := bbase (se 8 (by rfl) ⟨42903, by rfl⟩ : syracuseStep 7322197 = 85807) (by norm_num)
theorem B9762929 : Blo 1927435 9762929 := bstep (se 2 (by rfl) ⟨3661098, by rfl⟩ : syracuseStep 9762929 = 7322197) B7322197
theorem B6508619 : Blo 1927435 6508619 := bstep (se 1 (by rfl) ⟨4881464, by rfl⟩ : syracuseStep 6508619 = 9762929) B9762929
theorem B4339079 : Blo 1927435 4339079 := bstep (se 1 (by rfl) ⟨3254309, by rfl⟩ : syracuseStep 4339079 = 6508619) B6508619
theorem B2892719 : Blo 1927435 2892719 := bstep (se 1 (by rfl) ⟨2169539, by rfl⟩ : syracuseStep 2892719 = 4339079) B4339079
theorem B1928479 : Blo 1927435 1928479 := bstep (se 1 (by rfl) ⟨1446359, by rfl⟩ : syracuseStep 1928479 = 2892719) B2892719
theorem B2892725 : Blo 1927435 2892725 := bbase (se 5 (by rfl) ⟨135596, by rfl⟩ : syracuseStep 2892725 = 271193) (by norm_num)
theorem B1928483 : Blo 1927435 1928483 := bstep (se 1 (by rfl) ⟨1446362, by rfl⟩ : syracuseStep 1928483 = 2892725) B2892725
theorem B4881485 : Blo 1927435 4881485 := bbase (se 3 (by rfl) ⟨915278, by rfl⟩ : syracuseStep 4881485 = 1830557) (by norm_num)
theorem B3254323 : Blo 1927435 3254323 := bstep (se 1 (by rfl) ⟨2440742, by rfl⟩ : syracuseStep 3254323 = 4881485) B4881485
theorem B4339097 : Blo 1927435 4339097 := bstep (se 2 (by rfl) ⟨1627161, by rfl⟩ : syracuseStep 4339097 = 3254323) B3254323
theorem B2892731 : Blo 1927435 2892731 := bstep (se 1 (by rfl) ⟨2169548, by rfl⟩ : syracuseStep 2892731 = 4339097) B4339097
theorem B1928487 : Blo 1927435 1928487 := bstep (se 1 (by rfl) ⟨1446365, by rfl⟩ : syracuseStep 1928487 = 2892731) B2892731
theorem B2169553 : Blo 1927435 2169553 := bbase (se 2 (by rfl) ⟨813582, by rfl⟩ : syracuseStep 2169553 = 1627165) (by norm_num)
theorem B2892737 : Blo 1927435 2892737 := bstep (se 2 (by rfl) ⟨1084776, by rfl⟩ : syracuseStep 2892737 = 2169553) B2169553
theorem B1928491 : Blo 1927435 1928491 := bstep (se 1 (by rfl) ⟨1446368, by rfl⟩ : syracuseStep 1928491 = 2892737) B2892737
theorem B2316809 : Blo 1927435 2316809 := bbase (se 2 (by rfl) ⟨868803, by rfl⟩ : syracuseStep 2316809 = 1737607) (by norm_num)
theorem B6178157 : Blo 1927435 6178157 := bstep (se 3 (by rfl) ⟨1158404, by rfl⟩ : syracuseStep 6178157 = 2316809) B2316809
theorem B4118771 : Blo 1927435 4118771 := bstep (se 1 (by rfl) ⟨3089078, by rfl⟩ : syracuseStep 4118771 = 6178157) B6178157
theorem B2745847 : Blo 1927435 2745847 := bstep (se 1 (by rfl) ⟨2059385, by rfl⟩ : syracuseStep 2745847 = 4118771) B4118771
theorem B3661129 : Blo 1927435 3661129 := bstep (se 2 (by rfl) ⟨1372923, by rfl⟩ : syracuseStep 3661129 = 2745847) B2745847
theorem B4881505 : Blo 1927435 4881505 := bstep (se 2 (by rfl) ⟨1830564, by rfl⟩ : syracuseStep 4881505 = 3661129) B3661129
theorem B6508673 : Blo 1927435 6508673 := bstep (se 2 (by rfl) ⟨2440752, by rfl⟩ : syracuseStep 6508673 = 4881505) B4881505
theorem B4339115 : Blo 1927435 4339115 := bstep (se 1 (by rfl) ⟨3254336, by rfl⟩ : syracuseStep 4339115 = 6508673) B6508673
theorem B2892743 : Blo 1927435 2892743 := bstep (se 1 (by rfl) ⟨2169557, by rfl⟩ : syracuseStep 2892743 = 4339115) B4339115
theorem B1928495 : Blo 1927435 1928495 := bstep (se 1 (by rfl) ⟨1446371, by rfl⟩ : syracuseStep 1928495 = 2892743) B2892743
theorem B2892749 : Blo 1927435 2892749 := bbase (se 3 (by rfl) ⟨542390, by rfl⟩ : syracuseStep 2892749 = 1084781) (by norm_num)
theorem B1928499 : Blo 1927435 1928499 := bstep (se 1 (by rfl) ⟨1446374, by rfl⟩ : syracuseStep 1928499 = 2892749) B2892749
theorem B4339133 : Blo 1927435 4339133 := bbase (se 3 (by rfl) ⟨813587, by rfl⟩ : syracuseStep 4339133 = 1627175) (by norm_num)
theorem B2892755 : Blo 1927435 2892755 := bstep (se 1 (by rfl) ⟨2169566, by rfl⟩ : syracuseStep 2892755 = 4339133) B4339133
theorem B1928503 : Blo 1927435 1928503 := bstep (se 1 (by rfl) ⟨1446377, by rfl⟩ : syracuseStep 1928503 = 2892755) B2892755
theorem B3254357 : Blo 1927435 3254357 := bbase (se 8 (by rfl) ⟨19068, by rfl⟩ : syracuseStep 3254357 = 38137) (by norm_num)
theorem B2169571 : Blo 1927435 2169571 := bstep (se 1 (by rfl) ⟨1627178, by rfl⟩ : syracuseStep 2169571 = 3254357) B3254357
theorem B2892761 : Blo 1927435 2892761 := bstep (se 2 (by rfl) ⟨1084785, by rfl⟩ : syracuseStep 2892761 = 2169571) B2169571
theorem B1928507 : Blo 1927435 1928507 := bstep (se 1 (by rfl) ⟨1446380, by rfl⟩ : syracuseStep 1928507 = 2892761) B2892761
theorem B4760957 : Blo 1927435 4760957 := bbase (se 3 (by rfl) ⟨892679, by rfl⟩ : syracuseStep 4760957 = 1785359) (by norm_num)
theorem B3173971 : Blo 1927435 3173971 := bstep (se 1 (by rfl) ⟨2380478, by rfl⟩ : syracuseStep 3173971 = 4760957) B4760957
theorem B4231961 : Blo 1927435 4231961 := bstep (se 2 (by rfl) ⟨1586985, by rfl⟩ : syracuseStep 4231961 = 3173971) B3173971
theorem B2821307 : Blo 1927435 2821307 := bstep (se 1 (by rfl) ⟨2115980, by rfl⟩ : syracuseStep 2821307 = 4231961) B4231961
theorem B7523485 : Blo 1927435 7523485 := bstep (se 3 (by rfl) ⟨1410653, by rfl⟩ : syracuseStep 7523485 = 2821307) B2821307
theorem B160501013 : Blo 1927435 160501013 := bstep (se 6 (by rfl) ⟨3761742, by rfl⟩ : syracuseStep 160501013 = 7523485) B7523485
theorem B107000675 : Blo 1927435 107000675 := bstep (se 1 (by rfl) ⟨80250506, by rfl⟩ : syracuseStep 107000675 = 160501013) B160501013
theorem B71333783 : Blo 1927435 71333783 := bstep (se 1 (by rfl) ⟨53500337, by rfl⟩ : syracuseStep 71333783 = 107000675) B107000675
theorem B47555855 : Blo 1927435 47555855 := bstep (se 1 (by rfl) ⟨35666891, by rfl⟩ : syracuseStep 47555855 = 71333783) B71333783
theorem B31703903 : Blo 1927435 31703903 := bstep (se 1 (by rfl) ⟨23777927, by rfl⟩ : syracuseStep 31703903 = 47555855) B47555855
theorem B21135935 : Blo 1927435 21135935 := bstep (se 1 (by rfl) ⟨15851951, by rfl⟩ : syracuseStep 21135935 = 31703903) B31703903
theorem B56362493 : Blo 1927435 56362493 := bstep (se 3 (by rfl) ⟨10567967, by rfl⟩ : syracuseStep 56362493 = 21135935) B21135935
theorem B150299981 : Blo 1927435 150299981 := bstep (se 3 (by rfl) ⟨28181246, by rfl⟩ : syracuseStep 150299981 = 56362493) B56362493
theorem B100199987 : Blo 1927435 100199987 := bstep (se 1 (by rfl) ⟨75149990, by rfl⟩ : syracuseStep 100199987 = 150299981) B150299981
theorem B66799991 : Blo 1927435 66799991 := bstep (se 1 (by rfl) ⟨50099993, by rfl⟩ : syracuseStep 66799991 = 100199987) B100199987
theorem B44533327 : Blo 1927435 44533327 := bstep (se 1 (by rfl) ⟨33399995, by rfl⟩ : syracuseStep 44533327 = 66799991) B66799991
theorem B59377769 : Blo 1927435 59377769 := bstep (se 2 (by rfl) ⟨22266663, by rfl⟩ : syracuseStep 59377769 = 44533327) B44533327
theorem B39585179 : Blo 1927435 39585179 := bstep (se 1 (by rfl) ⟨29688884, by rfl⟩ : syracuseStep 39585179 = 59377769) B59377769
theorem B26390119 : Blo 1927435 26390119 := bstep (se 1 (by rfl) ⟨19792589, by rfl⟩ : syracuseStep 26390119 = 39585179) B39585179
theorem B35186825 : Blo 1927435 35186825 := bstep (se 2 (by rfl) ⟨13195059, by rfl⟩ : syracuseStep 35186825 = 26390119) B26390119
theorem B23457883 : Blo 1927435 23457883 := bstep (se 1 (by rfl) ⟨17593412, by rfl⟩ : syracuseStep 23457883 = 35186825) B35186825
theorem B31277177 : Blo 1927435 31277177 := bstep (se 2 (by rfl) ⟨11728941, by rfl⟩ : syracuseStep 31277177 = 23457883) B23457883
theorem B20851451 : Blo 1927435 20851451 := bstep (se 1 (by rfl) ⟨15638588, by rfl⟩ : syracuseStep 20851451 = 31277177) B31277177
theorem B13900967 : Blo 1927435 13900967 := bstep (se 1 (by rfl) ⟨10425725, by rfl⟩ : syracuseStep 13900967 = 20851451) B20851451
theorem B9267311 : Blo 1927435 9267311 := bstep (se 1 (by rfl) ⟨6950483, by rfl⟩ : syracuseStep 9267311 = 13900967) B13900967
theorem B6178207 : Blo 1927435 6178207 := bstep (se 1 (by rfl) ⟨4633655, by rfl⟩ : syracuseStep 6178207 = 9267311) B9267311
theorem B8237609 : Blo 1927435 8237609 := bstep (se 2 (by rfl) ⟨3089103, by rfl⟩ : syracuseStep 8237609 = 6178207) B6178207
theorem B5491739 : Blo 1927435 5491739 := bstep (se 1 (by rfl) ⟨4118804, by rfl⟩ : syracuseStep 5491739 = 8237609) B8237609
theorem B14644637 : Blo 1927435 14644637 := bstep (se 3 (by rfl) ⟨2745869, by rfl⟩ : syracuseStep 14644637 = 5491739) B5491739
theorem B9763091 : Blo 1927435 9763091 := bstep (se 1 (by rfl) ⟨7322318, by rfl⟩ : syracuseStep 9763091 = 14644637) B14644637
theorem B6508727 : Blo 1927435 6508727 := bstep (se 1 (by rfl) ⟨4881545, by rfl⟩ : syracuseStep 6508727 = 9763091) B9763091
theorem B4339151 : Blo 1927435 4339151 := bstep (se 1 (by rfl) ⟨3254363, by rfl⟩ : syracuseStep 4339151 = 6508727) B6508727
theorem B2892767 : Blo 1927435 2892767 := bstep (se 1 (by rfl) ⟨2169575, by rfl⟩ : syracuseStep 2892767 = 4339151) B4339151
theorem B1928511 : Blo 1927435 1928511 := bstep (se 1 (by rfl) ⟨1446383, by rfl⟩ : syracuseStep 1928511 = 2892767) B2892767
theorem B2892773 : Blo 1927435 2892773 := bbase (se 4 (by rfl) ⟨271197, by rfl⟩ : syracuseStep 2892773 = 542395) (by norm_num)
theorem B1928515 : Blo 1927435 1928515 := bstep (se 1 (by rfl) ⟨1446386, by rfl⟩ : syracuseStep 1928515 = 2892773) B2892773
theorem B3089117 : Blo 1927435 3089117 := bbase (se 3 (by rfl) ⟨579209, by rfl⟩ : syracuseStep 3089117 = 1158419) (by norm_num)
theorem B8237645 : Blo 1927435 8237645 := bstep (se 3 (by rfl) ⟨1544558, by rfl⟩ : syracuseStep 8237645 = 3089117) B3089117
theorem B5491763 : Blo 1927435 5491763 := bstep (se 1 (by rfl) ⟨4118822, by rfl⟩ : syracuseStep 5491763 = 8237645) B8237645
theorem B3661175 : Blo 1927435 3661175 := bstep (se 1 (by rfl) ⟨2745881, by rfl⟩ : syracuseStep 3661175 = 5491763) B5491763
theorem B2440783 : Blo 1927435 2440783 := bstep (se 1 (by rfl) ⟨1830587, by rfl⟩ : syracuseStep 2440783 = 3661175) B3661175
theorem B3254377 : Blo 1927435 3254377 := bstep (se 2 (by rfl) ⟨1220391, by rfl⟩ : syracuseStep 3254377 = 2440783) B2440783
theorem B4339169 : Blo 1927435 4339169 := bstep (se 2 (by rfl) ⟨1627188, by rfl⟩ : syracuseStep 4339169 = 3254377) B3254377
theorem B2892779 : Blo 1927435 2892779 := bstep (se 1 (by rfl) ⟨2169584, by rfl⟩ : syracuseStep 2892779 = 4339169) B4339169
theorem B1928519 : Blo 1927435 1928519 := bstep (se 1 (by rfl) ⟨1446389, by rfl⟩ : syracuseStep 1928519 = 2892779) B2892779
theorem B2169589 : Blo 1927435 2169589 := bbase (se 5 (by rfl) ⟨101699, by rfl⟩ : syracuseStep 2169589 = 203399) (by norm_num)
theorem B2892785 : Blo 1927435 2892785 := bstep (se 2 (by rfl) ⟨1084794, by rfl⟩ : syracuseStep 2892785 = 2169589) B2169589
theorem B1928523 : Blo 1927435 1928523 := bstep (se 1 (by rfl) ⟨1446392, by rfl⟩ : syracuseStep 1928523 = 2892785) B2892785
theorem B2440793 : Blo 1927435 2440793 := bbase (se 2 (by rfl) ⟨915297, by rfl⟩ : syracuseStep 2440793 = 1830595) (by norm_num)
theorem B6508781 : Blo 1927435 6508781 := bstep (se 3 (by rfl) ⟨1220396, by rfl⟩ : syracuseStep 6508781 = 2440793) B2440793
theorem B4339187 : Blo 1927435 4339187 := bstep (se 1 (by rfl) ⟨3254390, by rfl⟩ : syracuseStep 4339187 = 6508781) B6508781
theorem B2892791 : Blo 1927435 2892791 := bstep (se 1 (by rfl) ⟨2169593, by rfl⟩ : syracuseStep 2892791 = 4339187) B4339187
theorem B1928527 : Blo 1927435 1928527 := bstep (se 1 (by rfl) ⟨1446395, by rfl⟩ : syracuseStep 1928527 = 2892791) B2892791
theorem B2892797 : Blo 1927435 2892797 := bbase (se 3 (by rfl) ⟨542399, by rfl⟩ : syracuseStep 2892797 = 1084799) (by norm_num)
theorem B1928531 : Blo 1927435 1928531 := bstep (se 1 (by rfl) ⟨1446398, by rfl⟩ : syracuseStep 1928531 = 2892797) B2892797
theorem B4339205 : Blo 1927435 4339205 := bbase (se 4 (by rfl) ⟨406800, by rfl⟩ : syracuseStep 4339205 = 813601) (by norm_num)
theorem B2892803 : Blo 1927435 2892803 := bstep (se 1 (by rfl) ⟨2169602, by rfl⟩ : syracuseStep 2892803 = 4339205) B4339205
theorem B1928535 : Blo 1927435 1928535 := bstep (se 1 (by rfl) ⟨1446401, by rfl⟩ : syracuseStep 1928535 = 2892803) B2892803
theorem B3661213 : Blo 1927435 3661213 := bbase (se 3 (by rfl) ⟨686477, by rfl⟩ : syracuseStep 3661213 = 1372955) (by norm_num)
theorem B4881617 : Blo 1927435 4881617 := bstep (se 2 (by rfl) ⟨1830606, by rfl⟩ : syracuseStep 4881617 = 3661213) B3661213
theorem B3254411 : Blo 1927435 3254411 := bstep (se 1 (by rfl) ⟨2440808, by rfl⟩ : syracuseStep 3254411 = 4881617) B4881617
theorem B2169607 : Blo 1927435 2169607 := bstep (se 1 (by rfl) ⟨1627205, by rfl⟩ : syracuseStep 2169607 = 3254411) B3254411
theorem B2892809 : Blo 1927435 2892809 := bstep (se 2 (by rfl) ⟨1084803, by rfl⟩ : syracuseStep 2892809 = 2169607) B2169607
theorem B1928539 : Blo 1927435 1928539 := bstep (se 1 (by rfl) ⟨1446404, by rfl⟩ : syracuseStep 1928539 = 2892809) B2892809
theorem B9763253 : Blo 1927435 9763253 := bbase (se 5 (by rfl) ⟨457652, by rfl⟩ : syracuseStep 9763253 = 915305) (by norm_num)
theorem B6508835 : Blo 1927435 6508835 := bstep (se 1 (by rfl) ⟨4881626, by rfl⟩ : syracuseStep 6508835 = 9763253) B9763253
theorem B4339223 : Blo 1927435 4339223 := bstep (se 1 (by rfl) ⟨3254417, by rfl⟩ : syracuseStep 4339223 = 6508835) B6508835
theorem B2892815 : Blo 1927435 2892815 := bstep (se 1 (by rfl) ⟨2169611, by rfl⟩ : syracuseStep 2892815 = 4339223) B4339223
theorem B1928543 : Blo 1927435 1928543 := bstep (se 1 (by rfl) ⟨1446407, by rfl⟩ : syracuseStep 1928543 = 2892815) B2892815
theorem B2892821 : Blo 1927435 2892821 := bbase (se 6 (by rfl) ⟨67800, by rfl⟩ : syracuseStep 2892821 = 135601) (by norm_num)
theorem B1928547 : Blo 1927435 1928547 := bstep (se 1 (by rfl) ⟨1446410, by rfl⟩ : syracuseStep 1928547 = 2892821) B2892821
theorem B2474125 : Blo 1927435 2474125 := bbase (se 3 (by rfl) ⟨463898, by rfl⟩ : syracuseStep 2474125 = 927797) (by norm_num)
theorem B13195333 : Blo 1927435 13195333 := bstep (se 4 (by rfl) ⟨1237062, by rfl⟩ : syracuseStep 13195333 = 2474125) B2474125
theorem B17593777 : Blo 1927435 17593777 := bstep (se 2 (by rfl) ⟨6597666, by rfl⟩ : syracuseStep 17593777 = 13195333) B13195333
theorem B93833477 : Blo 1927435 93833477 := bstep (se 4 (by rfl) ⟨8796888, by rfl⟩ : syracuseStep 93833477 = 17593777) B17593777
theorem B62555651 : Blo 1927435 62555651 := bstep (se 1 (by rfl) ⟨46916738, by rfl⟩ : syracuseStep 62555651 = 93833477) B93833477
theorem B41703767 : Blo 1927435 41703767 := bstep (se 1 (by rfl) ⟨31277825, by rfl⟩ : syracuseStep 41703767 = 62555651) B62555651
theorem B27802511 : Blo 1927435 27802511 := bstep (se 1 (by rfl) ⟨20851883, by rfl⟩ : syracuseStep 27802511 = 41703767) B41703767
theorem B18535007 : Blo 1927435 18535007 := bstep (se 1 (by rfl) ⟨13901255, by rfl⟩ : syracuseStep 18535007 = 27802511) B27802511
theorem B12356671 : Blo 1927435 12356671 := bstep (se 1 (by rfl) ⟨9267503, by rfl⟩ : syracuseStep 12356671 = 18535007) B18535007
theorem B16475561 : Blo 1927435 16475561 := bstep (se 2 (by rfl) ⟨6178335, by rfl⟩ : syracuseStep 16475561 = 12356671) B12356671
theorem B10983707 : Blo 1927435 10983707 := bstep (se 1 (by rfl) ⟨8237780, by rfl⟩ : syracuseStep 10983707 = 16475561) B16475561
theorem B7322471 : Blo 1927435 7322471 := bstep (se 1 (by rfl) ⟨5491853, by rfl⟩ : syracuseStep 7322471 = 10983707) B10983707
theorem B4881647 : Blo 1927435 4881647 := bstep (se 1 (by rfl) ⟨3661235, by rfl⟩ : syracuseStep 4881647 = 7322471) B7322471
theorem B3254431 : Blo 1927435 3254431 := bstep (se 1 (by rfl) ⟨2440823, by rfl⟩ : syracuseStep 3254431 = 4881647) B4881647
theorem B4339241 : Blo 1927435 4339241 := bstep (se 2 (by rfl) ⟨1627215, by rfl⟩ : syracuseStep 4339241 = 3254431) B3254431
theorem B2892827 : Blo 1927435 2892827 := bstep (se 1 (by rfl) ⟨2169620, by rfl⟩ : syracuseStep 2892827 = 4339241) B4339241
theorem B1928551 : Blo 1927435 1928551 := bstep (se 1 (by rfl) ⟨1446413, by rfl⟩ : syracuseStep 1928551 = 2892827) B2892827
theorem B2169625 : Blo 1927435 2169625 := bbase (se 2 (by rfl) ⟨813609, by rfl⟩ : syracuseStep 2169625 = 1627219) (by norm_num)
theorem B2892833 : Blo 1927435 2892833 := bstep (se 2 (by rfl) ⟨1084812, by rfl⟩ : syracuseStep 2892833 = 2169625) B2169625
theorem B1928555 : Blo 1927435 1928555 := bstep (se 1 (by rfl) ⟨1446416, by rfl⟩ : syracuseStep 1928555 = 2892833) B2892833
theorem B7322501 : Blo 1927435 7322501 := bbase (se 4 (by rfl) ⟨686484, by rfl⟩ : syracuseStep 7322501 = 1372969) (by norm_num)
theorem B4881667 : Blo 1927435 4881667 := bstep (se 1 (by rfl) ⟨3661250, by rfl⟩ : syracuseStep 4881667 = 7322501) B7322501
theorem B6508889 : Blo 1927435 6508889 := bstep (se 2 (by rfl) ⟨2440833, by rfl⟩ : syracuseStep 6508889 = 4881667) B4881667
theorem B4339259 : Blo 1927435 4339259 := bstep (se 1 (by rfl) ⟨3254444, by rfl⟩ : syracuseStep 4339259 = 6508889) B6508889
theorem B2892839 : Blo 1927435 2892839 := bstep (se 1 (by rfl) ⟨2169629, by rfl⟩ : syracuseStep 2892839 = 4339259) B4339259
theorem B1928559 : Blo 1927435 1928559 := bstep (se 1 (by rfl) ⟨1446419, by rfl⟩ : syracuseStep 1928559 = 2892839) B2892839
theorem B2892845 : Blo 1927435 2892845 := bbase (se 3 (by rfl) ⟨542408, by rfl⟩ : syracuseStep 2892845 = 1084817) (by norm_num)
theorem B1928563 : Blo 1927435 1928563 := bstep (se 1 (by rfl) ⟨1446422, by rfl⟩ : syracuseStep 1928563 = 2892845) B2892845
theorem B4339277 : Blo 1927435 4339277 := bbase (se 3 (by rfl) ⟨813614, by rfl⟩ : syracuseStep 4339277 = 1627229) (by norm_num)
theorem B2892851 : Blo 1927435 2892851 := bstep (se 1 (by rfl) ⟨2169638, by rfl⟩ : syracuseStep 2892851 = 4339277) B4339277
theorem B1928567 : Blo 1927435 1928567 := bstep (se 1 (by rfl) ⟨1446425, by rfl⟩ : syracuseStep 1928567 = 2892851) B2892851
theorem B2440849 : Blo 1927435 2440849 := bbase (se 2 (by rfl) ⟨915318, by rfl⟩ : syracuseStep 2440849 = 1830637) (by norm_num)
theorem B3254465 : Blo 1927435 3254465 := bstep (se 2 (by rfl) ⟨1220424, by rfl⟩ : syracuseStep 3254465 = 2440849) B2440849
theorem B2169643 : Blo 1927435 2169643 := bstep (se 1 (by rfl) ⟨1627232, by rfl⟩ : syracuseStep 2169643 = 3254465) B3254465
theorem B2892857 : Blo 1927435 2892857 := bstep (se 2 (by rfl) ⟨1084821, by rfl⟩ : syracuseStep 2892857 = 2169643) B2169643
theorem B1928571 : Blo 1927435 1928571 := bstep (se 1 (by rfl) ⟨1446428, by rfl⟩ : syracuseStep 1928571 = 2892857) B2892857
theorem B4118941 : Blo 1927435 4118941 := bbase (se 3 (by rfl) ⟨772301, by rfl⟩ : syracuseStep 4118941 = 1544603) (by norm_num)
theorem B21967685 : Blo 1927435 21967685 := bstep (se 4 (by rfl) ⟨2059470, by rfl⟩ : syracuseStep 21967685 = 4118941) B4118941
theorem B14645123 : Blo 1927435 14645123 := bstep (se 1 (by rfl) ⟨10983842, by rfl⟩ : syracuseStep 14645123 = 21967685) B21967685
theorem B9763415 : Blo 1927435 9763415 := bstep (se 1 (by rfl) ⟨7322561, by rfl⟩ : syracuseStep 9763415 = 14645123) B14645123
theorem B6508943 : Blo 1927435 6508943 := bstep (se 1 (by rfl) ⟨4881707, by rfl⟩ : syracuseStep 6508943 = 9763415) B9763415
theorem B4339295 : Blo 1927435 4339295 := bstep (se 1 (by rfl) ⟨3254471, by rfl⟩ : syracuseStep 4339295 = 6508943) B6508943
theorem B2892863 : Blo 1927435 2892863 := bstep (se 1 (by rfl) ⟨2169647, by rfl⟩ : syracuseStep 2892863 = 4339295) B4339295
theorem B1928575 : Blo 1927435 1928575 := bstep (se 1 (by rfl) ⟨1446431, by rfl⟩ : syracuseStep 1928575 = 2892863) B2892863
theorem B2892869 : Blo 1927435 2892869 := bbase (se 4 (by rfl) ⟨271206, by rfl⟩ : syracuseStep 2892869 = 542413) (by norm_num)
theorem B1928579 : Blo 1927435 1928579 := bstep (se 1 (by rfl) ⟨1446434, by rfl⟩ : syracuseStep 1928579 = 2892869) B2892869
theorem B3254485 : Blo 1927435 3254485 := bbase (se 7 (by rfl) ⟨38138, by rfl⟩ : syracuseStep 3254485 = 76277) (by norm_num)
theorem B4339313 : Blo 1927435 4339313 := bstep (se 2 (by rfl) ⟨1627242, by rfl⟩ : syracuseStep 4339313 = 3254485) B3254485
theorem B2892875 : Blo 1927435 2892875 := bstep (se 1 (by rfl) ⟨2169656, by rfl⟩ : syracuseStep 2892875 = 4339313) B4339313
theorem B1928583 : Blo 1927435 1928583 := bstep (se 1 (by rfl) ⟨1446437, by rfl⟩ : syracuseStep 1928583 = 2892875) B2892875
theorem B2169661 : Blo 1927435 2169661 := bbase (se 3 (by rfl) ⟨406811, by rfl⟩ : syracuseStep 2169661 = 813623) (by norm_num)
theorem B2892881 : Blo 1927435 2892881 := bstep (se 2 (by rfl) ⟨1084830, by rfl⟩ : syracuseStep 2892881 = 2169661) B2169661
theorem B1928587 : Blo 1927435 1928587 := bstep (se 1 (by rfl) ⟨1446440, by rfl⟩ : syracuseStep 1928587 = 2892881) B2892881
theorem B6508997 : Blo 1927435 6508997 := bbase (se 4 (by rfl) ⟨610218, by rfl⟩ : syracuseStep 6508997 = 1220437) (by norm_num)
theorem B4339331 : Blo 1927435 4339331 := bstep (se 1 (by rfl) ⟨3254498, by rfl⟩ : syracuseStep 4339331 = 6508997) B6508997
theorem B2892887 : Blo 1927435 2892887 := bstep (se 1 (by rfl) ⟨2169665, by rfl⟩ : syracuseStep 2892887 = 4339331) B4339331
theorem B1928591 : Blo 1927435 1928591 := bstep (se 1 (by rfl) ⟨1446443, by rfl⟩ : syracuseStep 1928591 = 2892887) B2892887
theorem B2892893 : Blo 1927435 2892893 := bbase (se 3 (by rfl) ⟨542417, by rfl⟩ : syracuseStep 2892893 = 1084835) (by norm_num)
theorem B1928595 : Blo 1927435 1928595 := bstep (se 1 (by rfl) ⟨1446446, by rfl⟩ : syracuseStep 1928595 = 2892893) B2892893
theorem B4339349 : Blo 1927435 4339349 := bbase (se 6 (by rfl) ⟨101703, by rfl⟩ : syracuseStep 4339349 = 203407) (by norm_num)
theorem B2892899 : Blo 1927435 2892899 := bstep (se 1 (by rfl) ⟨2169674, by rfl⟩ : syracuseStep 2892899 = 4339349) B4339349
theorem B1928599 : Blo 1927435 1928599 := bstep (se 1 (by rfl) ⟨1446449, by rfl⟩ : syracuseStep 1928599 = 2892899) B2892899
theorem B2059501 : Blo 1927435 2059501 := bbase (se 3 (by rfl) ⟨386156, by rfl⟩ : syracuseStep 2059501 = 772313) (by norm_num)
theorem B2746001 : Blo 1927435 2746001 := bstep (se 2 (by rfl) ⟨1029750, by rfl⟩ : syracuseStep 2746001 = 2059501) B2059501
theorem B7322669 : Blo 1927435 7322669 := bstep (se 3 (by rfl) ⟨1373000, by rfl⟩ : syracuseStep 7322669 = 2746001) B2746001
theorem B4881779 : Blo 1927435 4881779 := bstep (se 1 (by rfl) ⟨3661334, by rfl⟩ : syracuseStep 4881779 = 7322669) B7322669
theorem B3254519 : Blo 1927435 3254519 := bstep (se 1 (by rfl) ⟨2440889, by rfl⟩ : syracuseStep 3254519 = 4881779) B4881779
theorem B2169679 : Blo 1927435 2169679 := bstep (se 1 (by rfl) ⟨1627259, by rfl⟩ : syracuseStep 2169679 = 3254519) B3254519
theorem B2892905 : Blo 1927435 2892905 := bstep (se 2 (by rfl) ⟨1084839, by rfl⟩ : syracuseStep 2892905 = 2169679) B2169679
theorem B1928603 : Blo 1927435 1928603 := bstep (se 1 (by rfl) ⟨1446452, by rfl⟩ : syracuseStep 1928603 = 2892905) B2892905
theorem B7819685 : Blo 1927435 7819685 := bbase (se 4 (by rfl) ⟨733095, by rfl⟩ : syracuseStep 7819685 = 1466191) (by norm_num)
theorem B5213123 : Blo 1927435 5213123 := bstep (se 1 (by rfl) ⟨3909842, by rfl⟩ : syracuseStep 5213123 = 7819685) B7819685
theorem B3475415 : Blo 1927435 3475415 := bstep (se 1 (by rfl) ⟨2606561, by rfl⟩ : syracuseStep 3475415 = 5213123) B5213123
theorem B2316943 : Blo 1927435 2316943 := bstep (se 1 (by rfl) ⟨1737707, by rfl⟩ : syracuseStep 2316943 = 3475415) B3475415
theorem B12357029 : Blo 1927435 12357029 := bstep (se 4 (by rfl) ⟨1158471, by rfl⟩ : syracuseStep 12357029 = 2316943) B2316943
theorem B8238019 : Blo 1927435 8238019 := bstep (se 1 (by rfl) ⟨6178514, by rfl⟩ : syracuseStep 8238019 = 12357029) B12357029
theorem B10984025 : Blo 1927435 10984025 := bstep (se 2 (by rfl) ⟨4119009, by rfl⟩ : syracuseStep 10984025 = 8238019) B8238019
theorem B7322683 : Blo 1927435 7322683 := bstep (se 1 (by rfl) ⟨5492012, by rfl⟩ : syracuseStep 7322683 = 10984025) B10984025
theorem B9763577 : Blo 1927435 9763577 := bstep (se 2 (by rfl) ⟨3661341, by rfl⟩ : syracuseStep 9763577 = 7322683) B7322683
theorem B6509051 : Blo 1927435 6509051 := bstep (se 1 (by rfl) ⟨4881788, by rfl⟩ : syracuseStep 6509051 = 9763577) B9763577
theorem B4339367 : Blo 1927435 4339367 := bstep (se 1 (by rfl) ⟨3254525, by rfl⟩ : syracuseStep 4339367 = 6509051) B6509051
theorem B2892911 : Blo 1927435 2892911 := bstep (se 1 (by rfl) ⟨2169683, by rfl⟩ : syracuseStep 2892911 = 4339367) B4339367
theorem B1928607 : Blo 1927435 1928607 := bstep (se 1 (by rfl) ⟨1446455, by rfl⟩ : syracuseStep 1928607 = 2892911) B2892911
theorem B2892917 : Blo 1927435 2892917 := bbase (se 5 (by rfl) ⟨135605, by rfl⟩ : syracuseStep 2892917 = 271211) (by norm_num)
theorem B1928611 : Blo 1927435 1928611 := bstep (se 1 (by rfl) ⟨1446458, by rfl⟩ : syracuseStep 1928611 = 2892917) B2892917
theorem B3661357 : Blo 1927435 3661357 := bbase (se 3 (by rfl) ⟨686504, by rfl⟩ : syracuseStep 3661357 = 1373009) (by norm_num)
theorem B4881809 : Blo 1927435 4881809 := bstep (se 2 (by rfl) ⟨1830678, by rfl⟩ : syracuseStep 4881809 = 3661357) B3661357
theorem B3254539 : Blo 1927435 3254539 := bstep (se 1 (by rfl) ⟨2440904, by rfl⟩ : syracuseStep 3254539 = 4881809) B4881809
theorem B4339385 : Blo 1927435 4339385 := bstep (se 2 (by rfl) ⟨1627269, by rfl⟩ : syracuseStep 4339385 = 3254539) B3254539
theorem B2892923 : Blo 1927435 2892923 := bstep (se 1 (by rfl) ⟨2169692, by rfl⟩ : syracuseStep 2892923 = 4339385) B4339385
theorem B1928615 : Blo 1927435 1928615 := bstep (se 1 (by rfl) ⟨1446461, by rfl⟩ : syracuseStep 1928615 = 2892923) B2892923
theorem B2169697 : Blo 1927435 2169697 := bbase (se 2 (by rfl) ⟨813636, by rfl⟩ : syracuseStep 2169697 = 1627273) (by norm_num)
theorem B2892929 : Blo 1927435 2892929 := bstep (se 2 (by rfl) ⟨1084848, by rfl⟩ : syracuseStep 2892929 = 2169697) B2169697
theorem B1928619 : Blo 1927435 1928619 := bstep (se 1 (by rfl) ⟨1446464, by rfl⟩ : syracuseStep 1928619 = 2892929) B2892929
theorem B4881829 : Blo 1927435 4881829 := bbase (se 4 (by rfl) ⟨457671, by rfl⟩ : syracuseStep 4881829 = 915343) (by norm_num)
theorem B6509105 : Blo 1927435 6509105 := bstep (se 2 (by rfl) ⟨2440914, by rfl⟩ : syracuseStep 6509105 = 4881829) B4881829
theorem B4339403 : Blo 1927435 4339403 := bstep (se 1 (by rfl) ⟨3254552, by rfl⟩ : syracuseStep 4339403 = 6509105) B6509105
theorem B2892935 : Blo 1927435 2892935 := bstep (se 1 (by rfl) ⟨2169701, by rfl⟩ : syracuseStep 2892935 = 4339403) B4339403
theorem B1928623 : Blo 1927435 1928623 := bstep (se 1 (by rfl) ⟨1446467, by rfl⟩ : syracuseStep 1928623 = 2892935) B2892935
theorem B2892941 : Blo 1927435 2892941 := bbase (se 3 (by rfl) ⟨542426, by rfl⟩ : syracuseStep 2892941 = 1084853) (by norm_num)
theorem B1928627 : Blo 1927435 1928627 := bstep (se 1 (by rfl) ⟨1446470, by rfl⟩ : syracuseStep 1928627 = 2892941) B2892941
theorem B4339421 : Blo 1927435 4339421 := bbase (se 3 (by rfl) ⟨813641, by rfl⟩ : syracuseStep 4339421 = 1627283) (by norm_num)
theorem B2892947 : Blo 1927435 2892947 := bstep (se 1 (by rfl) ⟨2169710, by rfl⟩ : syracuseStep 2892947 = 4339421) B4339421
theorem B1928631 : Blo 1927435 1928631 := bstep (se 1 (by rfl) ⟨1446473, by rfl⟩ : syracuseStep 1928631 = 2892947) B2892947
theorem B3254573 : Blo 1927435 3254573 := bbase (se 3 (by rfl) ⟨610232, by rfl⟩ : syracuseStep 3254573 = 1220465) (by norm_num)
theorem B2169715 : Blo 1927435 2169715 := bstep (se 1 (by rfl) ⟨1627286, by rfl⟩ : syracuseStep 2169715 = 3254573) B3254573
theorem B2892953 : Blo 1927435 2892953 := bstep (se 2 (by rfl) ⟨1084857, by rfl⟩ : syracuseStep 2892953 = 2169715) B2169715
theorem B1928635 : Blo 1927435 1928635 := bstep (se 1 (by rfl) ⟨1446476, by rfl⟩ : syracuseStep 1928635 = 2892953) B2892953
theorem B37071701 : Blo 1927435 37071701 := bbase (se 9 (by rfl) ⟨108608, by rfl⟩ : syracuseStep 37071701 = 217217) (by norm_num)
theorem B24714467 : Blo 1927435 24714467 := bstep (se 1 (by rfl) ⟨18535850, by rfl⟩ : syracuseStep 24714467 = 37071701) B37071701
theorem B16476311 : Blo 1927435 16476311 := bstep (se 1 (by rfl) ⟨12357233, by rfl⟩ : syracuseStep 16476311 = 24714467) B24714467
theorem B10984207 : Blo 1927435 10984207 := bstep (se 1 (by rfl) ⟨8238155, by rfl⟩ : syracuseStep 10984207 = 16476311) B16476311
theorem B14645609 : Blo 1927435 14645609 := bstep (se 2 (by rfl) ⟨5492103, by rfl⟩ : syracuseStep 14645609 = 10984207) B10984207
theorem B9763739 : Blo 1927435 9763739 := bstep (se 1 (by rfl) ⟨7322804, by rfl⟩ : syracuseStep 9763739 = 14645609) B14645609
theorem B6509159 : Blo 1927435 6509159 := bstep (se 1 (by rfl) ⟨4881869, by rfl⟩ : syracuseStep 6509159 = 9763739) B9763739
theorem B4339439 : Blo 1927435 4339439 := bstep (se 1 (by rfl) ⟨3254579, by rfl⟩ : syracuseStep 4339439 = 6509159) B6509159
theorem B2892959 : Blo 1927435 2892959 := bstep (se 1 (by rfl) ⟨2169719, by rfl⟩ : syracuseStep 2892959 = 4339439) B4339439
theorem B1928639 : Blo 1927435 1928639 := bstep (se 1 (by rfl) ⟨1446479, by rfl⟩ : syracuseStep 1928639 = 2892959) B2892959
theorem B2892965 : Blo 1927435 2892965 := bbase (se 4 (by rfl) ⟨271215, by rfl⟩ : syracuseStep 2892965 = 542431) (by norm_num)
theorem B1928643 : Blo 1927435 1928643 := bstep (se 1 (by rfl) ⟨1446482, by rfl⟩ : syracuseStep 1928643 = 2892965) B2892965
theorem B2440945 : Blo 1927435 2440945 := bbase (se 2 (by rfl) ⟨915354, by rfl⟩ : syracuseStep 2440945 = 1830709) (by norm_num)
theorem B3254593 : Blo 1927435 3254593 := bstep (se 2 (by rfl) ⟨1220472, by rfl⟩ : syracuseStep 3254593 = 2440945) B2440945
theorem B4339457 : Blo 1927435 4339457 := bstep (se 2 (by rfl) ⟨1627296, by rfl⟩ : syracuseStep 4339457 = 3254593) B3254593
theorem B2892971 : Blo 1927435 2892971 := bstep (se 1 (by rfl) ⟨2169728, by rfl⟩ : syracuseStep 2892971 = 4339457) B4339457
theorem B1928647 : Blo 1927435 1928647 := bstep (se 1 (by rfl) ⟨1446485, by rfl⟩ : syracuseStep 1928647 = 2892971) B2892971
theorem B2169733 : Blo 1927435 2169733 := bbase (se 4 (by rfl) ⟨203412, by rfl⟩ : syracuseStep 2169733 = 406825) (by norm_num)
theorem B2892977 : Blo 1927435 2892977 := bstep (se 2 (by rfl) ⟨1084866, by rfl⟩ : syracuseStep 2892977 = 2169733) B2169733
theorem B1928651 : Blo 1927435 1928651 := bstep (se 1 (by rfl) ⟨1446488, by rfl⟩ : syracuseStep 1928651 = 2892977) B2892977
theorem B3909941 : Blo 1927435 3909941 := bbase (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) (by norm_num)
theorem B2606627 : Blo 1927435 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B6951005 : Blo 1927435 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B4634003 : Blo 1927435 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B3089335 : Blo 1927435 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B4119113 : Blo 1927435 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B2746075 : Blo 1927435 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B3661433 : Blo 1927435 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B2440955 : Blo 1927435 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B6509213 : Blo 1927435 6509213 := bstep (se 3 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 6509213 = 2440955) B2440955
theorem B4339475 : Blo 1927435 4339475 := bstep (se 1 (by rfl) ⟨3254606, by rfl⟩ : syracuseStep 4339475 = 6509213) B6509213
theorem B2892983 : Blo 1927435 2892983 := bstep (se 1 (by rfl) ⟨2169737, by rfl⟩ : syracuseStep 2892983 = 4339475) B4339475
theorem B1928655 : Blo 1927435 1928655 := bstep (se 1 (by rfl) ⟨1446491, by rfl⟩ : syracuseStep 1928655 = 2892983) B2892983
theorem B2892989 : Blo 1927435 2892989 := bbase (se 3 (by rfl) ⟨542435, by rfl⟩ : syracuseStep 2892989 = 1084871) (by norm_num)
theorem B1928659 : Blo 1927435 1928659 := bstep (se 1 (by rfl) ⟨1446494, by rfl⟩ : syracuseStep 1928659 = 2892989) B2892989
theorem B4339493 : Blo 1927435 4339493 := bbase (se 4 (by rfl) ⟨406827, by rfl⟩ : syracuseStep 4339493 = 813655) (by norm_num)
theorem B2892995 : Blo 1927435 2892995 := bstep (se 1 (by rfl) ⟨2169746, by rfl⟩ : syracuseStep 2892995 = 4339493) B4339493
theorem B1928663 : Blo 1927435 1928663 := bstep (se 1 (by rfl) ⟨1446497, by rfl⟩ : syracuseStep 1928663 = 2892995) B2892995
theorem B4881941 : Blo 1927435 4881941 := bbase (se 6 (by rfl) ⟨114420, by rfl⟩ : syracuseStep 4881941 = 228841) (by norm_num)
theorem B3254627 : Blo 1927435 3254627 := bstep (se 1 (by rfl) ⟨2440970, by rfl⟩ : syracuseStep 3254627 = 4881941) B4881941
theorem B2169751 : Blo 1927435 2169751 := bstep (se 1 (by rfl) ⟨1627313, by rfl⟩ : syracuseStep 2169751 = 3254627) B3254627
theorem B2893001 : Blo 1927435 2893001 := bstep (se 2 (by rfl) ⟨1084875, by rfl⟩ : syracuseStep 2893001 = 2169751) B2169751
theorem B1928667 : Blo 1927435 1928667 := bstep (se 1 (by rfl) ⟨1446500, by rfl⟩ : syracuseStep 1928667 = 2893001) B2893001
theorem B8238293 : Blo 1927435 8238293 := bbase (se 7 (by rfl) ⟨96542, by rfl⟩ : syracuseStep 8238293 = 193085) (by norm_num)
theorem B5492195 : Blo 1927435 5492195 := bstep (se 1 (by rfl) ⟨4119146, by rfl⟩ : syracuseStep 5492195 = 8238293) B8238293
theorem B3661463 : Blo 1927435 3661463 := bstep (se 1 (by rfl) ⟨2746097, by rfl⟩ : syracuseStep 3661463 = 5492195) B5492195
theorem B9763901 : Blo 1927435 9763901 := bstep (se 3 (by rfl) ⟨1830731, by rfl⟩ : syracuseStep 9763901 = 3661463) B3661463
theorem B6509267 : Blo 1927435 6509267 := bstep (se 1 (by rfl) ⟨4881950, by rfl⟩ : syracuseStep 6509267 = 9763901) B9763901
theorem B4339511 : Blo 1927435 4339511 := bstep (se 1 (by rfl) ⟨3254633, by rfl⟩ : syracuseStep 4339511 = 6509267) B6509267
theorem B2893007 : Blo 1927435 2893007 := bstep (se 1 (by rfl) ⟨2169755, by rfl⟩ : syracuseStep 2893007 = 4339511) B4339511
theorem B1928671 : Blo 1927435 1928671 := bstep (se 1 (by rfl) ⟨1446503, by rfl⟩ : syracuseStep 1928671 = 2893007) B2893007
theorem B2893013 : Blo 1927435 2893013 := bbase (se 7 (by rfl) ⟨33902, by rfl⟩ : syracuseStep 2893013 = 67805) (by norm_num)
theorem B1928675 : Blo 1927435 1928675 := bstep (se 1 (by rfl) ⟨1446506, by rfl⟩ : syracuseStep 1928675 = 2893013) B2893013
theorem B2746109 : Blo 1927435 2746109 := bbase (se 3 (by rfl) ⟨514895, by rfl⟩ : syracuseStep 2746109 = 1029791) (by norm_num)
theorem B7322957 : Blo 1927435 7322957 := bstep (se 3 (by rfl) ⟨1373054, by rfl⟩ : syracuseStep 7322957 = 2746109) B2746109
theorem B4881971 : Blo 1927435 4881971 := bstep (se 1 (by rfl) ⟨3661478, by rfl⟩ : syracuseStep 4881971 = 7322957) B7322957
theorem B3254647 : Blo 1927435 3254647 := bstep (se 1 (by rfl) ⟨2440985, by rfl⟩ : syracuseStep 3254647 = 4881971) B4881971
theorem B4339529 : Blo 1927435 4339529 := bstep (se 2 (by rfl) ⟨1627323, by rfl⟩ : syracuseStep 4339529 = 3254647) B3254647
theorem B2893019 : Blo 1927435 2893019 := bstep (se 1 (by rfl) ⟨2169764, by rfl⟩ : syracuseStep 2893019 = 4339529) B4339529
theorem B1928679 : Blo 1927435 1928679 := bstep (se 1 (by rfl) ⟨1446509, by rfl⟩ : syracuseStep 1928679 = 2893019) B2893019
theorem B2169769 : Blo 1927435 2169769 := bbase (se 2 (by rfl) ⟨813663, by rfl⟩ : syracuseStep 2169769 = 1627327) (by norm_num)
theorem B2893025 : Blo 1927435 2893025 := bstep (se 2 (by rfl) ⟨1084884, by rfl⟩ : syracuseStep 2893025 = 2169769) B2169769
theorem B1928683 : Blo 1927435 1928683 := bstep (se 1 (by rfl) ⟨1446512, by rfl⟩ : syracuseStep 1928683 = 2893025) B2893025
theorem B7045957 : Blo 1927435 7045957 := bbase (se 4 (by rfl) ⟨660558, by rfl⟩ : syracuseStep 7045957 = 1321117) (by norm_num)
theorem B37578437 : Blo 1927435 37578437 := bstep (se 4 (by rfl) ⟨3522978, by rfl⟩ : syracuseStep 37578437 = 7045957) B7045957
theorem B25052291 : Blo 1927435 25052291 := bstep (se 1 (by rfl) ⟨18789218, by rfl⟩ : syracuseStep 25052291 = 37578437) B37578437
theorem B16701527 : Blo 1927435 16701527 := bstep (se 1 (by rfl) ⟨12526145, by rfl⟩ : syracuseStep 16701527 = 25052291) B25052291
theorem B11134351 : Blo 1927435 11134351 := bstep (se 1 (by rfl) ⟨8350763, by rfl⟩ : syracuseStep 11134351 = 16701527) B16701527
theorem B14845801 : Blo 1927435 14845801 := bstep (se 2 (by rfl) ⟨5567175, by rfl⟩ : syracuseStep 14845801 = 11134351) B11134351
theorem B19794401 : Blo 1927435 19794401 := bstep (se 2 (by rfl) ⟨7422900, by rfl⟩ : syracuseStep 19794401 = 14845801) B14845801
theorem B13196267 : Blo 1927435 13196267 := bstep (se 1 (by rfl) ⟨9897200, by rfl⟩ : syracuseStep 13196267 = 19794401) B19794401
theorem B8797511 : Blo 1927435 8797511 := bstep (se 1 (by rfl) ⟨6598133, by rfl⟩ : syracuseStep 8797511 = 13196267) B13196267
theorem B5865007 : Blo 1927435 5865007 := bstep (se 1 (by rfl) ⟨4398755, by rfl⟩ : syracuseStep 5865007 = 8797511) B8797511
theorem B7820009 : Blo 1927435 7820009 := bstep (se 2 (by rfl) ⟨2932503, by rfl⟩ : syracuseStep 7820009 = 5865007) B5865007
theorem B5213339 : Blo 1927435 5213339 := bstep (se 1 (by rfl) ⟨3910004, by rfl⟩ : syracuseStep 5213339 = 7820009) B7820009
theorem B3475559 : Blo 1927435 3475559 := bstep (se 1 (by rfl) ⟨2606669, by rfl⟩ : syracuseStep 3475559 = 5213339) B5213339
theorem B9268157 : Blo 1927435 9268157 := bstep (se 3 (by rfl) ⟨1737779, by rfl⟩ : syracuseStep 9268157 = 3475559) B3475559
theorem B6178771 : Blo 1927435 6178771 := bstep (se 1 (by rfl) ⟨4634078, by rfl⟩ : syracuseStep 6178771 = 9268157) B9268157
theorem B8238361 : Blo 1927435 8238361 := bstep (se 2 (by rfl) ⟨3089385, by rfl⟩ : syracuseStep 8238361 = 6178771) B6178771
theorem B10984481 : Blo 1927435 10984481 := bstep (se 2 (by rfl) ⟨4119180, by rfl⟩ : syracuseStep 10984481 = 8238361) B8238361
theorem B7322987 : Blo 1927435 7322987 := bstep (se 1 (by rfl) ⟨5492240, by rfl⟩ : syracuseStep 7322987 = 10984481) B10984481
theorem B4881991 : Blo 1927435 4881991 := bstep (se 1 (by rfl) ⟨3661493, by rfl⟩ : syracuseStep 4881991 = 7322987) B7322987
theorem B6509321 : Blo 1927435 6509321 := bstep (se 2 (by rfl) ⟨2440995, by rfl⟩ : syracuseStep 6509321 = 4881991) B4881991
theorem B4339547 : Blo 1927435 4339547 := bstep (se 1 (by rfl) ⟨3254660, by rfl⟩ : syracuseStep 4339547 = 6509321) B6509321
theorem B2893031 : Blo 1927435 2893031 := bstep (se 1 (by rfl) ⟨2169773, by rfl⟩ : syracuseStep 2893031 = 4339547) B4339547
theorem B1928687 : Blo 1927435 1928687 := bstep (se 1 (by rfl) ⟨1446515, by rfl⟩ : syracuseStep 1928687 = 2893031) B2893031
theorem B2893037 : Blo 1927435 2893037 := bbase (se 3 (by rfl) ⟨542444, by rfl⟩ : syracuseStep 2893037 = 1084889) (by norm_num)
theorem B1928691 : Blo 1927435 1928691 := bstep (se 1 (by rfl) ⟨1446518, by rfl⟩ : syracuseStep 1928691 = 2893037) B2893037
theorem B4339565 : Blo 1927435 4339565 := bbase (se 3 (by rfl) ⟨813668, by rfl⟩ : syracuseStep 4339565 = 1627337) (by norm_num)
theorem B2893043 : Blo 1927435 2893043 := bstep (se 1 (by rfl) ⟨2169782, by rfl⟩ : syracuseStep 2893043 = 4339565) B4339565
theorem B1928695 : Blo 1927435 1928695 := bstep (se 1 (by rfl) ⟨1446521, by rfl⟩ : syracuseStep 1928695 = 2893043) B2893043
theorem B3661517 : Blo 1927435 3661517 := bbase (se 3 (by rfl) ⟨686534, by rfl⟩ : syracuseStep 3661517 = 1373069) (by norm_num)
theorem B2441011 : Blo 1927435 2441011 := bstep (se 1 (by rfl) ⟨1830758, by rfl⟩ : syracuseStep 2441011 = 3661517) B3661517
theorem B3254681 : Blo 1927435 3254681 := bstep (se 2 (by rfl) ⟨1220505, by rfl⟩ : syracuseStep 3254681 = 2441011) B2441011
theorem B2169787 : Blo 1927435 2169787 := bstep (se 1 (by rfl) ⟨1627340, by rfl⟩ : syracuseStep 2169787 = 3254681) B3254681
theorem B2893049 : Blo 1927435 2893049 := bstep (se 2 (by rfl) ⟨1084893, by rfl⟩ : syracuseStep 2893049 = 2169787) B2169787
theorem B1928699 : Blo 1927435 1928699 := bstep (se 1 (by rfl) ⟨1446524, by rfl⟩ : syracuseStep 1928699 = 2893049) B2893049
theorem B5213381 : Blo 1927435 5213381 := bbase (se 4 (by rfl) ⟨488754, by rfl⟩ : syracuseStep 5213381 = 977509) (by norm_num)
theorem B13902349 : Blo 1927435 13902349 := bstep (se 3 (by rfl) ⟨2606690, by rfl⟩ : syracuseStep 13902349 = 5213381) B5213381
theorem B18536465 : Blo 1927435 18536465 := bstep (se 2 (by rfl) ⟨6951174, by rfl⟩ : syracuseStep 18536465 = 13902349) B13902349
theorem B49430573 : Blo 1927435 49430573 := bstep (se 3 (by rfl) ⟨9268232, by rfl⟩ : syracuseStep 49430573 = 18536465) B18536465
theorem B32953715 : Blo 1927435 32953715 := bstep (se 1 (by rfl) ⟨24715286, by rfl⟩ : syracuseStep 32953715 = 49430573) B49430573
theorem B21969143 : Blo 1927435 21969143 := bstep (se 1 (by rfl) ⟨16476857, by rfl⟩ : syracuseStep 21969143 = 32953715) B32953715
theorem B14646095 : Blo 1927435 14646095 := bstep (se 1 (by rfl) ⟨10984571, by rfl⟩ : syracuseStep 14646095 = 21969143) B21969143
theorem B9764063 : Blo 1927435 9764063 := bstep (se 1 (by rfl) ⟨7323047, by rfl⟩ : syracuseStep 9764063 = 14646095) B14646095
theorem B6509375 : Blo 1927435 6509375 := bstep (se 1 (by rfl) ⟨4882031, by rfl⟩ : syracuseStep 6509375 = 9764063) B9764063
theorem B4339583 : Blo 1927435 4339583 := bstep (se 1 (by rfl) ⟨3254687, by rfl⟩ : syracuseStep 4339583 = 6509375) B6509375
theorem B2893055 : Blo 1927435 2893055 := bstep (se 1 (by rfl) ⟨2169791, by rfl⟩ : syracuseStep 2893055 = 4339583) B4339583
theorem B1928703 : Blo 1927435 1928703 := bstep (se 1 (by rfl) ⟨1446527, by rfl⟩ : syracuseStep 1928703 = 2893055) B2893055
theorem B2893061 : Blo 1927435 2893061 := bbase (se 4 (by rfl) ⟨271224, by rfl⟩ : syracuseStep 2893061 = 542449) (by norm_num)
theorem B1928707 : Blo 1927435 1928707 := bstep (se 1 (by rfl) ⟨1446530, by rfl⟩ : syracuseStep 1928707 = 2893061) B2893061
theorem B3254701 : Blo 1927435 3254701 := bbase (se 3 (by rfl) ⟨610256, by rfl⟩ : syracuseStep 3254701 = 1220513) (by norm_num)
theorem B4339601 : Blo 1927435 4339601 := bstep (se 2 (by rfl) ⟨1627350, by rfl⟩ : syracuseStep 4339601 = 3254701) B3254701
theorem B2893067 : Blo 1927435 2893067 := bstep (se 1 (by rfl) ⟨2169800, by rfl⟩ : syracuseStep 2893067 = 4339601) B4339601
theorem B1928711 : Blo 1927435 1928711 := bstep (se 1 (by rfl) ⟨1446533, by rfl⟩ : syracuseStep 1928711 = 2893067) B2893067
theorem B2169805 : Blo 1927435 2169805 := bbase (se 3 (by rfl) ⟨406838, by rfl⟩ : syracuseStep 2169805 = 813677) (by norm_num)
theorem B2893073 : Blo 1927435 2893073 := bstep (se 2 (by rfl) ⟨1084902, by rfl⟩ : syracuseStep 2893073 = 2169805) B2169805
theorem B1928715 : Blo 1927435 1928715 := bstep (se 1 (by rfl) ⟨1446536, by rfl⟩ : syracuseStep 1928715 = 2893073) B2893073
theorem B6509429 : Blo 1927435 6509429 := bbase (se 5 (by rfl) ⟨305129, by rfl⟩ : syracuseStep 6509429 = 610259) (by norm_num)
theorem B4339619 : Blo 1927435 4339619 := bstep (se 1 (by rfl) ⟨3254714, by rfl⟩ : syracuseStep 4339619 = 6509429) B6509429
theorem B2893079 : Blo 1927435 2893079 := bstep (se 1 (by rfl) ⟨2169809, by rfl⟩ : syracuseStep 2893079 = 4339619) B4339619
theorem B1928719 : Blo 1927435 1928719 := bstep (se 1 (by rfl) ⟨1446539, by rfl⟩ : syracuseStep 1928719 = 2893079) B2893079
theorem B2893085 : Blo 1927435 2893085 := bbase (se 3 (by rfl) ⟨542453, by rfl⟩ : syracuseStep 2893085 = 1084907) (by norm_num)
theorem B1928723 : Blo 1927435 1928723 := bstep (se 1 (by rfl) ⟨1446542, by rfl⟩ : syracuseStep 1928723 = 2893085) B2893085
theorem B4339637 : Blo 1927435 4339637 := bbase (se 5 (by rfl) ⟨203420, by rfl⟩ : syracuseStep 4339637 = 406841) (by norm_num)
theorem B2893091 : Blo 1927435 2893091 := bstep (se 1 (by rfl) ⟨2169818, by rfl⟩ : syracuseStep 2893091 = 4339637) B4339637
theorem B1928727 : Blo 1927435 1928727 := bstep (se 1 (by rfl) ⟨1446545, by rfl⟩ : syracuseStep 1928727 = 2893091) B2893091
theorem B3523061 : Blo 1927435 3523061 := bbase (se 5 (by rfl) ⟨165143, by rfl⟩ : syracuseStep 3523061 = 330287) (by norm_num)
theorem B9394829 : Blo 1927435 9394829 := bstep (se 3 (by rfl) ⟨1761530, by rfl⟩ : syracuseStep 9394829 = 3523061) B3523061
theorem B6263219 : Blo 1927435 6263219 := bstep (se 1 (by rfl) ⟨4697414, by rfl⟩ : syracuseStep 6263219 = 9394829) B9394829
theorem B4175479 : Blo 1927435 4175479 := bstep (se 1 (by rfl) ⟨3131609, by rfl⟩ : syracuseStep 4175479 = 6263219) B6263219
theorem B5567305 : Blo 1927435 5567305 := bstep (se 2 (by rfl) ⟨2087739, by rfl⟩ : syracuseStep 5567305 = 4175479) B4175479
theorem B7423073 : Blo 1927435 7423073 := bstep (se 2 (by rfl) ⟨2783652, by rfl⟩ : syracuseStep 7423073 = 5567305) B5567305
theorem B4948715 : Blo 1927435 4948715 := bstep (se 1 (by rfl) ⟨3711536, by rfl⟩ : syracuseStep 4948715 = 7423073) B7423073
theorem B3299143 : Blo 1927435 3299143 := bstep (se 1 (by rfl) ⟨2474357, by rfl⟩ : syracuseStep 3299143 = 4948715) B4948715
theorem B4398857 : Blo 1927435 4398857 := bstep (se 2 (by rfl) ⟨1649571, by rfl⟩ : syracuseStep 4398857 = 3299143) B3299143
theorem B2932571 : Blo 1927435 2932571 := bstep (se 1 (by rfl) ⟨2199428, by rfl⟩ : syracuseStep 2932571 = 4398857) B4398857
theorem B7820189 : Blo 1927435 7820189 := bstep (se 3 (by rfl) ⟨1466285, by rfl⟩ : syracuseStep 7820189 = 2932571) B2932571
theorem B5213459 : Blo 1927435 5213459 := bstep (se 1 (by rfl) ⟨3910094, by rfl⟩ : syracuseStep 5213459 = 7820189) B7820189
theorem B3475639 : Blo 1927435 3475639 := bstep (se 1 (by rfl) ⟨2606729, by rfl⟩ : syracuseStep 3475639 = 5213459) B5213459
theorem B4634185 : Blo 1927435 4634185 := bstep (se 2 (by rfl) ⟨1737819, by rfl⟩ : syracuseStep 4634185 = 3475639) B3475639
theorem B6178913 : Blo 1927435 6178913 := bstep (se 2 (by rfl) ⟨2317092, by rfl⟩ : syracuseStep 6178913 = 4634185) B4634185
theorem B4119275 : Blo 1927435 4119275 := bstep (se 1 (by rfl) ⟨3089456, by rfl⟩ : syracuseStep 4119275 = 6178913) B6178913
theorem B10984733 : Blo 1927435 10984733 := bstep (se 3 (by rfl) ⟨2059637, by rfl⟩ : syracuseStep 10984733 = 4119275) B4119275
theorem B7323155 : Blo 1927435 7323155 := bstep (se 1 (by rfl) ⟨5492366, by rfl⟩ : syracuseStep 7323155 = 10984733) B10984733
theorem B4882103 : Blo 1927435 4882103 := bstep (se 1 (by rfl) ⟨3661577, by rfl⟩ : syracuseStep 4882103 = 7323155) B7323155
theorem B3254735 : Blo 1927435 3254735 := bstep (se 1 (by rfl) ⟨2441051, by rfl⟩ : syracuseStep 3254735 = 4882103) B4882103
theorem B2169823 : Blo 1927435 2169823 := bstep (se 1 (by rfl) ⟨1627367, by rfl⟩ : syracuseStep 2169823 = 3254735) B3254735
theorem B2893097 : Blo 1927435 2893097 := bstep (se 2 (by rfl) ⟨1084911, by rfl⟩ : syracuseStep 2893097 = 2169823) B2169823
theorem B1928731 : Blo 1927435 1928731 := bstep (se 1 (by rfl) ⟨1446548, by rfl⟩ : syracuseStep 1928731 = 2893097) B2893097
theorem B2317097 : Blo 1927435 2317097 := bbase (se 2 (by rfl) ⟨868911, by rfl⟩ : syracuseStep 2317097 = 1737823) (by norm_num)
theorem B6178925 : Blo 1927435 6178925 := bstep (se 3 (by rfl) ⟨1158548, by rfl⟩ : syracuseStep 6178925 = 2317097) B2317097
theorem B4119283 : Blo 1927435 4119283 := bstep (se 1 (by rfl) ⟨3089462, by rfl⟩ : syracuseStep 4119283 = 6178925) B6178925
theorem B5492377 : Blo 1927435 5492377 := bstep (se 2 (by rfl) ⟨2059641, by rfl⟩ : syracuseStep 5492377 = 4119283) B4119283
theorem B7323169 : Blo 1927435 7323169 := bstep (se 2 (by rfl) ⟨2746188, by rfl⟩ : syracuseStep 7323169 = 5492377) B5492377
theorem B9764225 : Blo 1927435 9764225 := bstep (se 2 (by rfl) ⟨3661584, by rfl⟩ : syracuseStep 9764225 = 7323169) B7323169
theorem B6509483 : Blo 1927435 6509483 := bstep (se 1 (by rfl) ⟨4882112, by rfl⟩ : syracuseStep 6509483 = 9764225) B9764225
theorem B4339655 : Blo 1927435 4339655 := bstep (se 1 (by rfl) ⟨3254741, by rfl⟩ : syracuseStep 4339655 = 6509483) B6509483
theorem B2893103 : Blo 1927435 2893103 := bstep (se 1 (by rfl) ⟨2169827, by rfl⟩ : syracuseStep 2893103 = 4339655) B4339655
theorem B1928735 : Blo 1927435 1928735 := bstep (se 1 (by rfl) ⟨1446551, by rfl⟩ : syracuseStep 1928735 = 2893103) B2893103
theorem B2893109 : Blo 1927435 2893109 := bbase (se 5 (by rfl) ⟨135614, by rfl⟩ : syracuseStep 2893109 = 271229) (by norm_num)
theorem B1928739 : Blo 1927435 1928739 := bstep (se 1 (by rfl) ⟨1446554, by rfl⟩ : syracuseStep 1928739 = 2893109) B2893109
theorem B4882133 : Blo 1927435 4882133 := bbase (se 7 (by rfl) ⟨57212, by rfl⟩ : syracuseStep 4882133 = 114425) (by norm_num)
theorem B3254755 : Blo 1927435 3254755 := bstep (se 1 (by rfl) ⟨2441066, by rfl⟩ : syracuseStep 3254755 = 4882133) B4882133
theorem B4339673 : Blo 1927435 4339673 := bstep (se 2 (by rfl) ⟨1627377, by rfl⟩ : syracuseStep 4339673 = 3254755) B3254755
theorem B2893115 : Blo 1927435 2893115 := bstep (se 1 (by rfl) ⟨2169836, by rfl⟩ : syracuseStep 2893115 = 4339673) B4339673
theorem B1928743 : Blo 1927435 1928743 := bstep (se 1 (by rfl) ⟨1446557, by rfl⟩ : syracuseStep 1928743 = 2893115) B2893115
theorem B2169841 : Blo 1927435 2169841 := bbase (se 2 (by rfl) ⟨813690, by rfl⟩ : syracuseStep 2169841 = 1627381) (by norm_num)
theorem B2893121 : Blo 1927435 2893121 := bstep (se 2 (by rfl) ⟨1084920, by rfl⟩ : syracuseStep 2893121 = 2169841) B2169841
theorem B1928747 : Blo 1927435 1928747 := bstep (se 1 (by rfl) ⟨1446560, by rfl⟩ : syracuseStep 1928747 = 2893121) B2893121
theorem B6951349 : Blo 1927435 6951349 := bbase (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) (by norm_num)
theorem B9268465 : Blo 1927435 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B12357953 : Blo 1927435 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B8238635 : Blo 1927435 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B5492423 : Blo 1927435 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B3661615 : Blo 1927435 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B4882153 : Blo 1927435 4882153 := bstep (se 2 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 4882153 = 3661615) B3661615
theorem B6509537 : Blo 1927435 6509537 := bstep (se 2 (by rfl) ⟨2441076, by rfl⟩ : syracuseStep 6509537 = 4882153) B4882153
theorem B4339691 : Blo 1927435 4339691 := bstep (se 1 (by rfl) ⟨3254768, by rfl⟩ : syracuseStep 4339691 = 6509537) B6509537
theorem B2893127 : Blo 1927435 2893127 := bstep (se 1 (by rfl) ⟨2169845, by rfl⟩ : syracuseStep 2893127 = 4339691) B4339691
theorem B1928751 : Blo 1927435 1928751 := bstep (se 1 (by rfl) ⟨1446563, by rfl⟩ : syracuseStep 1928751 = 2893127) B2893127
theorem B2893133 : Blo 1927435 2893133 := bbase (se 3 (by rfl) ⟨542462, by rfl⟩ : syracuseStep 2893133 = 1084925) (by norm_num)
theorem B1928755 : Blo 1927435 1928755 := bstep (se 1 (by rfl) ⟨1446566, by rfl⟩ : syracuseStep 1928755 = 2893133) B2893133
theorem B4339709 : Blo 1927435 4339709 := bbase (se 3 (by rfl) ⟨813695, by rfl⟩ : syracuseStep 4339709 = 1627391) (by norm_num)
theorem B2893139 : Blo 1927435 2893139 := bstep (se 1 (by rfl) ⟨2169854, by rfl⟩ : syracuseStep 2893139 = 4339709) B4339709
theorem B1928759 : Blo 1927435 1928759 := bstep (se 1 (by rfl) ⟨1446569, by rfl⟩ : syracuseStep 1928759 = 2893139) B2893139
theorem B3254789 : Blo 1927435 3254789 := bbase (se 4 (by rfl) ⟨305136, by rfl⟩ : syracuseStep 3254789 = 610273) (by norm_num)
theorem B2169859 : Blo 1927435 2169859 := bstep (se 1 (by rfl) ⟨1627394, by rfl⟩ : syracuseStep 2169859 = 3254789) B3254789
theorem B2893145 : Blo 1927435 2893145 := bstep (se 2 (by rfl) ⟨1084929, by rfl⟩ : syracuseStep 2893145 = 2169859) B2169859
theorem B1928763 : Blo 1927435 1928763 := bstep (se 1 (by rfl) ⟨1446572, by rfl⟩ : syracuseStep 1928763 = 2893145) B2893145
theorem B14646581 : Blo 1927435 14646581 := bbase (se 5 (by rfl) ⟨686558, by rfl⟩ : syracuseStep 14646581 = 1373117) (by norm_num)
theorem B9764387 : Blo 1927435 9764387 := bstep (se 1 (by rfl) ⟨7323290, by rfl⟩ : syracuseStep 9764387 = 14646581) B14646581
theorem B6509591 : Blo 1927435 6509591 := bstep (se 1 (by rfl) ⟨4882193, by rfl⟩ : syracuseStep 6509591 = 9764387) B9764387
theorem B4339727 : Blo 1927435 4339727 := bstep (se 1 (by rfl) ⟨3254795, by rfl⟩ : syracuseStep 4339727 = 6509591) B6509591
theorem B2893151 : Blo 1927435 2893151 := bstep (se 1 (by rfl) ⟨2169863, by rfl⟩ : syracuseStep 2893151 = 4339727) B4339727
theorem B1928767 : Blo 1927435 1928767 := bstep (se 1 (by rfl) ⟨1446575, by rfl⟩ : syracuseStep 1928767 = 2893151) B2893151
theorem B2893157 : Blo 1927435 2893157 := bbase (se 4 (by rfl) ⟨271233, by rfl⟩ : syracuseStep 2893157 = 542467) (by norm_num)
theorem B1928771 : Blo 1927435 1928771 := bstep (se 1 (by rfl) ⟨1446578, by rfl⟩ : syracuseStep 1928771 = 2893157) B2893157
theorem B3661661 : Blo 1927435 3661661 := bbase (se 3 (by rfl) ⟨686561, by rfl⟩ : syracuseStep 3661661 = 1373123) (by norm_num)
theorem B2441107 : Blo 1927435 2441107 := bstep (se 1 (by rfl) ⟨1830830, by rfl⟩ : syracuseStep 2441107 = 3661661) B3661661
theorem B3254809 : Blo 1927435 3254809 := bstep (se 2 (by rfl) ⟨1220553, by rfl⟩ : syracuseStep 3254809 = 2441107) B2441107
theorem B4339745 : Blo 1927435 4339745 := bstep (se 2 (by rfl) ⟨1627404, by rfl⟩ : syracuseStep 4339745 = 3254809) B3254809
theorem B2893163 : Blo 1927435 2893163 := bstep (se 1 (by rfl) ⟨2169872, by rfl⟩ : syracuseStep 2893163 = 4339745) B4339745
theorem B1928775 : Blo 1927435 1928775 := bstep (se 1 (by rfl) ⟨1446581, by rfl⟩ : syracuseStep 1928775 = 2893163) B2893163
theorem B2169877 : Blo 1927435 2169877 := bbase (se 6 (by rfl) ⟨50856, by rfl⟩ : syracuseStep 2169877 = 101713) (by norm_num)
theorem B2893169 : Blo 1927435 2893169 := bstep (se 2 (by rfl) ⟨1084938, by rfl⟩ : syracuseStep 2893169 = 2169877) B2169877
theorem B1928779 : Blo 1927435 1928779 := bstep (se 1 (by rfl) ⟨1446584, by rfl⟩ : syracuseStep 1928779 = 2893169) B2893169
theorem B2441117 : Blo 1927435 2441117 := bbase (se 3 (by rfl) ⟨457709, by rfl⟩ : syracuseStep 2441117 = 915419) (by norm_num)
theorem B6509645 : Blo 1927435 6509645 := bstep (se 3 (by rfl) ⟨1220558, by rfl⟩ : syracuseStep 6509645 = 2441117) B2441117
theorem B4339763 : Blo 1927435 4339763 := bstep (se 1 (by rfl) ⟨3254822, by rfl⟩ : syracuseStep 4339763 = 6509645) B6509645
theorem B2893175 : Blo 1927435 2893175 := bstep (se 1 (by rfl) ⟨2169881, by rfl⟩ : syracuseStep 2893175 = 4339763) B4339763
theorem B1928783 : Blo 1927435 1928783 := bstep (se 1 (by rfl) ⟨1446587, by rfl⟩ : syracuseStep 1928783 = 2893175) B2893175
theorem B2893181 : Blo 1927435 2893181 := bbase (se 3 (by rfl) ⟨542471, by rfl⟩ : syracuseStep 2893181 = 1084943) (by norm_num)
theorem B1928787 : Blo 1927435 1928787 := bstep (se 1 (by rfl) ⟨1446590, by rfl⟩ : syracuseStep 1928787 = 2893181) B2893181
theorem B4339781 : Blo 1927435 4339781 := bbase (se 4 (by rfl) ⟨406854, by rfl⟩ : syracuseStep 4339781 = 813709) (by norm_num)
theorem B2893187 : Blo 1927435 2893187 := bstep (se 1 (by rfl) ⟨2169890, by rfl⟩ : syracuseStep 2893187 = 4339781) B4339781
theorem B1928791 : Blo 1927435 1928791 := bstep (se 1 (by rfl) ⟨1446593, by rfl⟩ : syracuseStep 1928791 = 2893187) B2893187
theorem B5492549 : Blo 1927435 5492549 := bbase (se 4 (by rfl) ⟨514926, by rfl⟩ : syracuseStep 5492549 = 1029853) (by norm_num)
theorem B3661699 : Blo 1927435 3661699 := bstep (se 1 (by rfl) ⟨2746274, by rfl⟩ : syracuseStep 3661699 = 5492549) B5492549
theorem B4882265 : Blo 1927435 4882265 := bstep (se 2 (by rfl) ⟨1830849, by rfl⟩ : syracuseStep 4882265 = 3661699) B3661699
theorem B3254843 : Blo 1927435 3254843 := bstep (se 1 (by rfl) ⟨2441132, by rfl⟩ : syracuseStep 3254843 = 4882265) B4882265
theorem B2169895 : Blo 1927435 2169895 := bstep (se 1 (by rfl) ⟨1627421, by rfl⟩ : syracuseStep 2169895 = 3254843) B3254843
theorem B2893193 : Blo 1927435 2893193 := bstep (se 2 (by rfl) ⟨1084947, by rfl⟩ : syracuseStep 2893193 = 2169895) B2169895
theorem B1928795 : Blo 1927435 1928795 := bstep (se 1 (by rfl) ⟨1446596, by rfl⟩ : syracuseStep 1928795 = 2893193) B2893193
theorem B9764549 : Blo 1927435 9764549 := bbase (se 4 (by rfl) ⟨915426, by rfl⟩ : syracuseStep 9764549 = 1830853) (by norm_num)
theorem B6509699 : Blo 1927435 6509699 := bstep (se 1 (by rfl) ⟨4882274, by rfl⟩ : syracuseStep 6509699 = 9764549) B9764549
theorem B4339799 : Blo 1927435 4339799 := bstep (se 1 (by rfl) ⟨3254849, by rfl⟩ : syracuseStep 4339799 = 6509699) B6509699
theorem B2893199 : Blo 1927435 2893199 := bstep (se 1 (by rfl) ⟨2169899, by rfl⟩ : syracuseStep 2893199 = 4339799) B4339799
theorem B1928799 : Blo 1927435 1928799 := bstep (se 1 (by rfl) ⟨1446599, by rfl⟩ : syracuseStep 1928799 = 2893199) B2893199
theorem B2893205 : Blo 1927435 2893205 := bbase (se 6 (by rfl) ⟨67809, by rfl⟩ : syracuseStep 2893205 = 135619) (by norm_num)
theorem B1928803 : Blo 1927435 1928803 := bstep (se 1 (by rfl) ⟨1446602, by rfl⟩ : syracuseStep 1928803 = 2893205) B2893205
theorem B4119437 : Blo 1927435 4119437 := bbase (se 3 (by rfl) ⟨772394, by rfl⟩ : syracuseStep 4119437 = 1544789) (by norm_num)
theorem B10985165 : Blo 1927435 10985165 := bstep (se 3 (by rfl) ⟨2059718, by rfl⟩ : syracuseStep 10985165 = 4119437) B4119437
theorem B7323443 : Blo 1927435 7323443 := bstep (se 1 (by rfl) ⟨5492582, by rfl⟩ : syracuseStep 7323443 = 10985165) B10985165
theorem B4882295 : Blo 1927435 4882295 := bstep (se 1 (by rfl) ⟨3661721, by rfl⟩ : syracuseStep 4882295 = 7323443) B7323443
theorem B3254863 : Blo 1927435 3254863 := bstep (se 1 (by rfl) ⟨2441147, by rfl⟩ : syracuseStep 3254863 = 4882295) B4882295
theorem B4339817 : Blo 1927435 4339817 := bstep (se 2 (by rfl) ⟨1627431, by rfl⟩ : syracuseStep 4339817 = 3254863) B3254863
theorem B2893211 : Blo 1927435 2893211 := bstep (se 1 (by rfl) ⟨2169908, by rfl⟩ : syracuseStep 2893211 = 4339817) B4339817
theorem B1928807 : Blo 1927435 1928807 := bstep (se 1 (by rfl) ⟨1446605, by rfl⟩ : syracuseStep 1928807 = 2893211) B2893211
theorem B2169913 : Blo 1927435 2169913 := bbase (se 2 (by rfl) ⟨813717, by rfl⟩ : syracuseStep 2169913 = 1627435) (by norm_num)
theorem B2893217 : Blo 1927435 2893217 := bstep (se 2 (by rfl) ⟨1084956, by rfl⟩ : syracuseStep 2893217 = 2169913) B2169913
theorem B1928811 : Blo 1927435 1928811 := bstep (se 1 (by rfl) ⟨1446608, by rfl⟩ : syracuseStep 1928811 = 2893217) B2893217
theorem B7423397 : Blo 1927435 7423397 := bbase (se 4 (by rfl) ⟨695943, by rfl⟩ : syracuseStep 7423397 = 1391887) (by norm_num)
theorem B4948931 : Blo 1927435 4948931 := bstep (se 1 (by rfl) ⟨3711698, by rfl⟩ : syracuseStep 4948931 = 7423397) B7423397
theorem B3299287 : Blo 1927435 3299287 := bstep (se 1 (by rfl) ⟨2474465, by rfl⟩ : syracuseStep 3299287 = 4948931) B4948931
theorem B4399049 : Blo 1927435 4399049 := bstep (se 2 (by rfl) ⟨1649643, by rfl⟩ : syracuseStep 4399049 = 3299287) B3299287
theorem B2932699 : Blo 1927435 2932699 := bstep (se 1 (by rfl) ⟨2199524, by rfl⟩ : syracuseStep 2932699 = 4399049) B4399049
theorem B3910265 : Blo 1927435 3910265 := bstep (se 2 (by rfl) ⟨1466349, by rfl⟩ : syracuseStep 3910265 = 2932699) B2932699
theorem B2606843 : Blo 1927435 2606843 := bstep (se 1 (by rfl) ⟨1955132, by rfl⟩ : syracuseStep 2606843 = 3910265) B3910265
theorem B6951581 : Blo 1927435 6951581 := bstep (se 3 (by rfl) ⟨1303421, by rfl⟩ : syracuseStep 6951581 = 2606843) B2606843
theorem B4634387 : Blo 1927435 4634387 := bstep (se 1 (by rfl) ⟨3475790, by rfl⟩ : syracuseStep 4634387 = 6951581) B6951581
theorem B3089591 : Blo 1927435 3089591 := bstep (se 1 (by rfl) ⟨2317193, by rfl⟩ : syracuseStep 3089591 = 4634387) B4634387
theorem B2059727 : Blo 1927435 2059727 := bstep (se 1 (by rfl) ⟨1544795, by rfl⟩ : syracuseStep 2059727 = 3089591) B3089591
theorem B5492605 : Blo 1927435 5492605 := bstep (se 3 (by rfl) ⟨1029863, by rfl⟩ : syracuseStep 5492605 = 2059727) B2059727
theorem B7323473 : Blo 1927435 7323473 := bstep (se 2 (by rfl) ⟨2746302, by rfl⟩ : syracuseStep 7323473 = 5492605) B5492605
theorem B4882315 : Blo 1927435 4882315 := bstep (se 1 (by rfl) ⟨3661736, by rfl⟩ : syracuseStep 4882315 = 7323473) B7323473
theorem B6509753 : Blo 1927435 6509753 := bstep (se 2 (by rfl) ⟨2441157, by rfl⟩ : syracuseStep 6509753 = 4882315) B4882315
theorem B4339835 : Blo 1927435 4339835 := bstep (se 1 (by rfl) ⟨3254876, by rfl⟩ : syracuseStep 4339835 = 6509753) B6509753
theorem B2893223 : Blo 1927435 2893223 := bstep (se 1 (by rfl) ⟨2169917, by rfl⟩ : syracuseStep 2893223 = 4339835) B4339835
theorem B1928815 : Blo 1927435 1928815 := bstep (se 1 (by rfl) ⟨1446611, by rfl⟩ : syracuseStep 1928815 = 2893223) B2893223
theorem B2893229 : Blo 1927435 2893229 := bbase (se 3 (by rfl) ⟨542480, by rfl⟩ : syracuseStep 2893229 = 1084961) (by norm_num)
theorem B1928819 : Blo 1927435 1928819 := bstep (se 1 (by rfl) ⟨1446614, by rfl⟩ : syracuseStep 1928819 = 2893229) B2893229
theorem B4339853 : Blo 1927435 4339853 := bbase (se 3 (by rfl) ⟨813722, by rfl⟩ : syracuseStep 4339853 = 1627445) (by norm_num)
theorem B2893235 : Blo 1927435 2893235 := bstep (se 1 (by rfl) ⟨2169926, by rfl⟩ : syracuseStep 2893235 = 4339853) B4339853
theorem B1928823 : Blo 1927435 1928823 := bstep (se 1 (by rfl) ⟨1446617, by rfl⟩ : syracuseStep 1928823 = 2893235) B2893235
theorem B2441173 : Blo 1927435 2441173 := bbase (se 7 (by rfl) ⟨28607, by rfl⟩ : syracuseStep 2441173 = 57215) (by norm_num)
theorem B3254897 : Blo 1927435 3254897 := bstep (se 2 (by rfl) ⟨1220586, by rfl⟩ : syracuseStep 3254897 = 2441173) B2441173
theorem B2169931 : Blo 1927435 2169931 := bstep (se 1 (by rfl) ⟨1627448, by rfl⟩ : syracuseStep 2169931 = 3254897) B3254897
theorem B2893241 : Blo 1927435 2893241 := bstep (se 2 (by rfl) ⟨1084965, by rfl⟩ : syracuseStep 2893241 = 2169931) B2169931
theorem B1928827 : Blo 1927435 1928827 := bstep (se 1 (by rfl) ⟨1446620, by rfl⟩ : syracuseStep 1928827 = 2893241) B2893241
theorem B9523493 : Blo 1927435 9523493 := bbase (se 4 (by rfl) ⟨892827, by rfl⟩ : syracuseStep 9523493 = 1785655) (by norm_num)
theorem B6348995 : Blo 1927435 6348995 := bstep (se 1 (by rfl) ⟨4761746, by rfl⟩ : syracuseStep 6348995 = 9523493) B9523493
theorem B4232663 : Blo 1927435 4232663 := bstep (se 1 (by rfl) ⟨3174497, by rfl⟩ : syracuseStep 4232663 = 6348995) B6348995
theorem B2821775 : Blo 1927435 2821775 := bstep (se 1 (by rfl) ⟨2116331, by rfl⟩ : syracuseStep 2821775 = 4232663) B4232663
theorem B7524733 : Blo 1927435 7524733 := bstep (se 3 (by rfl) ⟨1410887, by rfl⟩ : syracuseStep 7524733 = 2821775) B2821775
theorem B10032977 : Blo 1927435 10032977 := bstep (se 2 (by rfl) ⟨3762366, by rfl⟩ : syracuseStep 10032977 = 7524733) B7524733
theorem B6688651 : Blo 1927435 6688651 := bstep (se 1 (by rfl) ⟨5016488, by rfl⟩ : syracuseStep 6688651 = 10032977) B10032977
theorem B8918201 : Blo 1927435 8918201 := bstep (se 2 (by rfl) ⟨3344325, by rfl⟩ : syracuseStep 8918201 = 6688651) B6688651
theorem B5945467 : Blo 1927435 5945467 := bstep (se 1 (by rfl) ⟨4459100, by rfl⟩ : syracuseStep 5945467 = 8918201) B8918201
theorem B7927289 : Blo 1927435 7927289 := bstep (se 2 (by rfl) ⟨2972733, by rfl⟩ : syracuseStep 7927289 = 5945467) B5945467
theorem B84557749 : Blo 1927435 84557749 := bstep (se 5 (by rfl) ⟨3963644, by rfl⟩ : syracuseStep 84557749 = 7927289) B7927289
theorem B112743665 : Blo 1927435 112743665 := bstep (se 2 (by rfl) ⟨42278874, by rfl⟩ : syracuseStep 112743665 = 84557749) B84557749
theorem B75162443 : Blo 1927435 75162443 := bstep (se 1 (by rfl) ⟨56371832, by rfl⟩ : syracuseStep 75162443 = 112743665) B112743665
theorem B801732725 : Blo 1927435 801732725 := bstep (se 5 (by rfl) ⟨37581221, by rfl⟩ : syracuseStep 801732725 = 75162443) B75162443
theorem B534488483 : Blo 1927435 534488483 := bstep (se 1 (by rfl) ⟨400866362, by rfl⟩ : syracuseStep 534488483 = 801732725) B801732725
theorem B356325655 : Blo 1927435 356325655 := bstep (se 1 (by rfl) ⟨267244241, by rfl⟩ : syracuseStep 356325655 = 534488483) B534488483
theorem B475100873 : Blo 1927435 475100873 := bstep (se 2 (by rfl) ⟨178162827, by rfl⟩ : syracuseStep 475100873 = 356325655) B356325655
theorem B316733915 : Blo 1927435 316733915 := bstep (se 1 (by rfl) ⟨237550436, by rfl⟩ : syracuseStep 316733915 = 475100873) B475100873
theorem B211155943 : Blo 1927435 211155943 := bstep (se 1 (by rfl) ⟨158366957, by rfl⟩ : syracuseStep 211155943 = 316733915) B316733915
theorem B281541257 : Blo 1927435 281541257 := bstep (se 2 (by rfl) ⟨105577971, by rfl⟩ : syracuseStep 281541257 = 211155943) B211155943
theorem B187694171 : Blo 1927435 187694171 := bstep (se 1 (by rfl) ⟨140770628, by rfl⟩ : syracuseStep 187694171 = 281541257) B281541257
theorem B125129447 : Blo 1927435 125129447 := bstep (se 1 (by rfl) ⟨93847085, by rfl⟩ : syracuseStep 125129447 = 187694171) B187694171
theorem B83419631 : Blo 1927435 83419631 := bstep (se 1 (by rfl) ⟨62564723, by rfl⟩ : syracuseStep 83419631 = 125129447) B125129447
theorem B55613087 : Blo 1927435 55613087 := bstep (se 1 (by rfl) ⟨41709815, by rfl⟩ : syracuseStep 55613087 = 83419631) B83419631
theorem B37075391 : Blo 1927435 37075391 := bstep (se 1 (by rfl) ⟨27806543, by rfl⟩ : syracuseStep 37075391 = 55613087) B55613087
theorem B24716927 : Blo 1927435 24716927 := bstep (se 1 (by rfl) ⟨18537695, by rfl⟩ : syracuseStep 24716927 = 37075391) B37075391
theorem B16477951 : Blo 1927435 16477951 := bstep (se 1 (by rfl) ⟨12358463, by rfl⟩ : syracuseStep 16477951 = 24716927) B24716927
theorem B21970601 : Blo 1927435 21970601 := bstep (se 2 (by rfl) ⟨8238975, by rfl⟩ : syracuseStep 21970601 = 16477951) B16477951
theorem B14647067 : Blo 1927435 14647067 := bstep (se 1 (by rfl) ⟨10985300, by rfl⟩ : syracuseStep 14647067 = 21970601) B21970601
theorem B9764711 : Blo 1927435 9764711 := bstep (se 1 (by rfl) ⟨7323533, by rfl⟩ : syracuseStep 9764711 = 14647067) B14647067
theorem B6509807 : Blo 1927435 6509807 := bstep (se 1 (by rfl) ⟨4882355, by rfl⟩ : syracuseStep 6509807 = 9764711) B9764711
theorem B4339871 : Blo 1927435 4339871 := bstep (se 1 (by rfl) ⟨3254903, by rfl⟩ : syracuseStep 4339871 = 6509807) B6509807
theorem B2893247 : Blo 1927435 2893247 := bstep (se 1 (by rfl) ⟨2169935, by rfl⟩ : syracuseStep 2893247 = 4339871) B4339871
theorem B1928831 : Blo 1927435 1928831 := bstep (se 1 (by rfl) ⟨1446623, by rfl⟩ : syracuseStep 1928831 = 2893247) B2893247
theorem B2893253 : Blo 1927435 2893253 := bbase (se 4 (by rfl) ⟨271242, by rfl⟩ : syracuseStep 2893253 = 542485) (by norm_num)
theorem B1928835 : Blo 1927435 1928835 := bstep (se 1 (by rfl) ⟨1446626, by rfl⟩ : syracuseStep 1928835 = 2893253) B2893253
theorem B3254917 : Blo 1927435 3254917 := bbase (se 4 (by rfl) ⟨305148, by rfl⟩ : syracuseStep 3254917 = 610297) (by norm_num)
theorem B4339889 : Blo 1927435 4339889 := bstep (se 2 (by rfl) ⟨1627458, by rfl⟩ : syracuseStep 4339889 = 3254917) B3254917
theorem B2893259 : Blo 1927435 2893259 := bstep (se 1 (by rfl) ⟨2169944, by rfl⟩ : syracuseStep 2893259 = 4339889) B4339889
theorem B1928839 : Blo 1927435 1928839 := bstep (se 1 (by rfl) ⟨1446629, by rfl⟩ : syracuseStep 1928839 = 2893259) B2893259
theorem B2169949 : Blo 1927435 2169949 := bbase (se 3 (by rfl) ⟨406865, by rfl⟩ : syracuseStep 2169949 = 813731) (by norm_num)
theorem B2893265 : Blo 1927435 2893265 := bstep (se 2 (by rfl) ⟨1084974, by rfl⟩ : syracuseStep 2893265 = 2169949) B2169949
theorem B1928843 : Blo 1927435 1928843 := bstep (se 1 (by rfl) ⟨1446632, by rfl⟩ : syracuseStep 1928843 = 2893265) B2893265
theorem B6509861 : Blo 1927435 6509861 := bbase (se 4 (by rfl) ⟨610299, by rfl⟩ : syracuseStep 6509861 = 1220599) (by norm_num)
theorem B4339907 : Blo 1927435 4339907 := bstep (se 1 (by rfl) ⟨3254930, by rfl⟩ : syracuseStep 4339907 = 6509861) B6509861
theorem B2893271 : Blo 1927435 2893271 := bstep (se 1 (by rfl) ⟨2169953, by rfl⟩ : syracuseStep 2893271 = 4339907) B4339907
theorem B1928847 : Blo 1927435 1928847 := bstep (se 1 (by rfl) ⟨1446635, by rfl⟩ : syracuseStep 1928847 = 2893271) B2893271
theorem B2893277 : Blo 1927435 2893277 := bbase (se 3 (by rfl) ⟨542489, by rfl⟩ : syracuseStep 2893277 = 1084979) (by norm_num)
theorem B1928851 : Blo 1927435 1928851 := bstep (se 1 (by rfl) ⟨1446638, by rfl⟩ : syracuseStep 1928851 = 2893277) B2893277
theorem B4339925 : Blo 1927435 4339925 := bbase (se 7 (by rfl) ⟨50858, by rfl⟩ : syracuseStep 4339925 = 101717) (by norm_num)
theorem B2893283 : Blo 1927435 2893283 := bstep (se 1 (by rfl) ⟨2169962, by rfl⟩ : syracuseStep 2893283 = 4339925) B4339925
theorem B1928855 : Blo 1927435 1928855 := bstep (se 1 (by rfl) ⟨1446641, by rfl⟩ : syracuseStep 1928855 = 2893283) B2893283
theorem B11731061 : Blo 1927435 11731061 := bbase (se 5 (by rfl) ⟨549893, by rfl⟩ : syracuseStep 11731061 = 1099787) (by norm_num)
theorem B7820707 : Blo 1927435 7820707 := bstep (se 1 (by rfl) ⟨5865530, by rfl⟩ : syracuseStep 7820707 = 11731061) B11731061
theorem B10427609 : Blo 1927435 10427609 := bstep (se 2 (by rfl) ⟨3910353, by rfl⟩ : syracuseStep 10427609 = 7820707) B7820707
theorem B6951739 : Blo 1927435 6951739 := bstep (se 1 (by rfl) ⟨5213804, by rfl⟩ : syracuseStep 6951739 = 10427609) B10427609
theorem B9268985 : Blo 1927435 9268985 := bstep (se 2 (by rfl) ⟨3475869, by rfl⟩ : syracuseStep 9268985 = 6951739) B6951739
theorem B6179323 : Blo 1927435 6179323 := bstep (se 1 (by rfl) ⟨4634492, by rfl⟩ : syracuseStep 6179323 = 9268985) B9268985
theorem B8239097 : Blo 1927435 8239097 := bstep (se 2 (by rfl) ⟨3089661, by rfl⟩ : syracuseStep 8239097 = 6179323) B6179323
theorem B5492731 : Blo 1927435 5492731 := bstep (se 1 (by rfl) ⟨4119548, by rfl⟩ : syracuseStep 5492731 = 8239097) B8239097
theorem B7323641 : Blo 1927435 7323641 := bstep (se 2 (by rfl) ⟨2746365, by rfl⟩ : syracuseStep 7323641 = 5492731) B5492731
theorem B4882427 : Blo 1927435 4882427 := bstep (se 1 (by rfl) ⟨3661820, by rfl⟩ : syracuseStep 4882427 = 7323641) B7323641
theorem B3254951 : Blo 1927435 3254951 := bstep (se 1 (by rfl) ⟨2441213, by rfl⟩ : syracuseStep 3254951 = 4882427) B4882427
theorem B2169967 : Blo 1927435 2169967 := bstep (se 1 (by rfl) ⟨1627475, by rfl⟩ : syracuseStep 2169967 = 3254951) B3254951
theorem B2893289 : Blo 1927435 2893289 := bstep (se 2 (by rfl) ⟨1084983, by rfl⟩ : syracuseStep 2893289 = 2169967) B2169967
theorem B1928859 : Blo 1927435 1928859 := bstep (se 1 (by rfl) ⟨1446644, by rfl⟩ : syracuseStep 1928859 = 2893289) B2893289
theorem B4634501 : Blo 1927435 4634501 := bbase (se 4 (by rfl) ⟨434484, by rfl⟩ : syracuseStep 4634501 = 868969) (by norm_num)
theorem B12358669 : Blo 1927435 12358669 := bstep (se 3 (by rfl) ⟨2317250, by rfl⟩ : syracuseStep 12358669 = 4634501) B4634501
theorem B16478225 : Blo 1927435 16478225 := bstep (se 2 (by rfl) ⟨6179334, by rfl⟩ : syracuseStep 16478225 = 12358669) B12358669
theorem B10985483 : Blo 1927435 10985483 := bstep (se 1 (by rfl) ⟨8239112, by rfl⟩ : syracuseStep 10985483 = 16478225) B16478225
theorem B7323655 : Blo 1927435 7323655 := bstep (se 1 (by rfl) ⟨5492741, by rfl⟩ : syracuseStep 7323655 = 10985483) B10985483
theorem B9764873 : Blo 1927435 9764873 := bstep (se 2 (by rfl) ⟨3661827, by rfl⟩ : syracuseStep 9764873 = 7323655) B7323655
theorem B6509915 : Blo 1927435 6509915 := bstep (se 1 (by rfl) ⟨4882436, by rfl⟩ : syracuseStep 6509915 = 9764873) B9764873
theorem B4339943 : Blo 1927435 4339943 := bstep (se 1 (by rfl) ⟨3254957, by rfl⟩ : syracuseStep 4339943 = 6509915) B6509915
theorem B2893295 : Blo 1927435 2893295 := bstep (se 1 (by rfl) ⟨2169971, by rfl⟩ : syracuseStep 2893295 = 4339943) B4339943
theorem B1928863 : Blo 1927435 1928863 := bstep (se 1 (by rfl) ⟨1446647, by rfl⟩ : syracuseStep 1928863 = 2893295) B2893295
theorem B2893301 : Blo 1927435 2893301 := bbase (se 5 (by rfl) ⟨135623, by rfl⟩ : syracuseStep 2893301 = 271247) (by norm_num)
theorem B1928867 : Blo 1927435 1928867 := bstep (se 1 (by rfl) ⟨1446650, by rfl⟩ : syracuseStep 1928867 = 2893301) B2893301
theorem B2317261 : Blo 1927435 2317261 := bbase (se 3 (by rfl) ⟨434486, by rfl⟩ : syracuseStep 2317261 = 868973) (by norm_num)
theorem B3089681 : Blo 1927435 3089681 := bstep (se 2 (by rfl) ⟨1158630, by rfl⟩ : syracuseStep 3089681 = 2317261) B2317261
theorem B2059787 : Blo 1927435 2059787 := bstep (se 1 (by rfl) ⟨1544840, by rfl⟩ : syracuseStep 2059787 = 3089681) B3089681
theorem B5492765 : Blo 1927435 5492765 := bstep (se 3 (by rfl) ⟨1029893, by rfl⟩ : syracuseStep 5492765 = 2059787) B2059787
theorem B3661843 : Blo 1927435 3661843 := bstep (se 1 (by rfl) ⟨2746382, by rfl⟩ : syracuseStep 3661843 = 5492765) B5492765
theorem B4882457 : Blo 1927435 4882457 := bstep (se 2 (by rfl) ⟨1830921, by rfl⟩ : syracuseStep 4882457 = 3661843) B3661843
theorem B3254971 : Blo 1927435 3254971 := bstep (se 1 (by rfl) ⟨2441228, by rfl⟩ : syracuseStep 3254971 = 4882457) B4882457
theorem B4339961 : Blo 1927435 4339961 := bstep (se 2 (by rfl) ⟨1627485, by rfl⟩ : syracuseStep 4339961 = 3254971) B3254971
theorem B2893307 : Blo 1927435 2893307 := bstep (se 1 (by rfl) ⟨2169980, by rfl⟩ : syracuseStep 2893307 = 4339961) B4339961
theorem B1928871 : Blo 1927435 1928871 := bstep (se 1 (by rfl) ⟨1446653, by rfl⟩ : syracuseStep 1928871 = 2893307) B2893307
theorem B2169985 : Blo 1927435 2169985 := bbase (se 2 (by rfl) ⟨813744, by rfl⟩ : syracuseStep 2169985 = 1627489) (by norm_num)
theorem B2893313 : Blo 1927435 2893313 := bstep (se 2 (by rfl) ⟨1084992, by rfl⟩ : syracuseStep 2893313 = 2169985) B2169985
theorem B1928875 : Blo 1927435 1928875 := bstep (se 1 (by rfl) ⟨1446656, by rfl⟩ : syracuseStep 1928875 = 2893313) B2893313
theorem B4882477 : Blo 1927435 4882477 := bbase (se 3 (by rfl) ⟨915464, by rfl⟩ : syracuseStep 4882477 = 1830929) (by norm_num)
theorem B6509969 : Blo 1927435 6509969 := bstep (se 2 (by rfl) ⟨2441238, by rfl⟩ : syracuseStep 6509969 = 4882477) B4882477
theorem B4339979 : Blo 1927435 4339979 := bstep (se 1 (by rfl) ⟨3254984, by rfl⟩ : syracuseStep 4339979 = 6509969) B6509969
theorem B2893319 : Blo 1927435 2893319 := bstep (se 1 (by rfl) ⟨2169989, by rfl⟩ : syracuseStep 2893319 = 4339979) B4339979
theorem B1928879 : Blo 1927435 1928879 := bstep (se 1 (by rfl) ⟨1446659, by rfl⟩ : syracuseStep 1928879 = 2893319) B2893319
theorem B2893325 : Blo 1927435 2893325 := bbase (se 3 (by rfl) ⟨542498, by rfl⟩ : syracuseStep 2893325 = 1084997) (by norm_num)
theorem B1928883 : Blo 1927435 1928883 := bstep (se 1 (by rfl) ⟨1446662, by rfl⟩ : syracuseStep 1928883 = 2893325) B2893325
theorem B4339997 : Blo 1927435 4339997 := bbase (se 3 (by rfl) ⟨813749, by rfl⟩ : syracuseStep 4339997 = 1627499) (by norm_num)
theorem B2893331 : Blo 1927435 2893331 := bstep (se 1 (by rfl) ⟨2169998, by rfl⟩ : syracuseStep 2893331 = 4339997) B4339997
theorem B1928887 : Blo 1927435 1928887 := bstep (se 1 (by rfl) ⟨1446665, by rfl⟩ : syracuseStep 1928887 = 2893331) B2893331
theorem B3255005 : Blo 1927435 3255005 := bbase (se 3 (by rfl) ⟨610313, by rfl⟩ : syracuseStep 3255005 = 1220627) (by norm_num)
theorem B2170003 : Blo 1927435 2170003 := bstep (se 1 (by rfl) ⟨1627502, by rfl⟩ : syracuseStep 2170003 = 3255005) B3255005
theorem B2893337 : Blo 1927435 2893337 := bstep (se 2 (by rfl) ⟨1085001, by rfl⟩ : syracuseStep 2893337 = 2170003) B2170003
theorem B1928891 : Blo 1927435 1928891 := bstep (se 1 (by rfl) ⟨1446668, by rfl⟩ : syracuseStep 1928891 = 2893337) B2893337
theorem B2317289 : Blo 1927435 2317289 := bbase (se 2 (by rfl) ⟨868983, by rfl⟩ : syracuseStep 2317289 = 1737967) (by norm_num)
theorem B6179437 : Blo 1927435 6179437 := bstep (se 3 (by rfl) ⟨1158644, by rfl⟩ : syracuseStep 6179437 = 2317289) B2317289
theorem B8239249 : Blo 1927435 8239249 := bstep (se 2 (by rfl) ⟨3089718, by rfl⟩ : syracuseStep 8239249 = 6179437) B6179437
theorem B10985665 : Blo 1927435 10985665 := bstep (se 2 (by rfl) ⟨4119624, by rfl⟩ : syracuseStep 10985665 = 8239249) B8239249
theorem B14647553 : Blo 1927435 14647553 := bstep (se 2 (by rfl) ⟨5492832, by rfl⟩ : syracuseStep 14647553 = 10985665) B10985665
theorem B9765035 : Blo 1927435 9765035 := bstep (se 1 (by rfl) ⟨7323776, by rfl⟩ : syracuseStep 9765035 = 14647553) B14647553
theorem B6510023 : Blo 1927435 6510023 := bstep (se 1 (by rfl) ⟨4882517, by rfl⟩ : syracuseStep 6510023 = 9765035) B9765035
theorem B4340015 : Blo 1927435 4340015 := bstep (se 1 (by rfl) ⟨3255011, by rfl⟩ : syracuseStep 4340015 = 6510023) B6510023
theorem B2893343 : Blo 1927435 2893343 := bstep (se 1 (by rfl) ⟨2170007, by rfl⟩ : syracuseStep 2893343 = 4340015) B4340015
theorem B1928895 : Blo 1927435 1928895 := bstep (se 1 (by rfl) ⟨1446671, by rfl⟩ : syracuseStep 1928895 = 2893343) B2893343
theorem B2893349 : Blo 1927435 2893349 := bbase (se 4 (by rfl) ⟨271251, by rfl⟩ : syracuseStep 2893349 = 542503) (by norm_num)
theorem B1928899 : Blo 1927435 1928899 := bstep (se 1 (by rfl) ⟨1446674, by rfl⟩ : syracuseStep 1928899 = 2893349) B2893349
theorem B2441269 : Blo 1927435 2441269 := bbase (se 5 (by rfl) ⟨114434, by rfl⟩ : syracuseStep 2441269 = 228869) (by norm_num)
theorem B3255025 : Blo 1927435 3255025 := bstep (se 2 (by rfl) ⟨1220634, by rfl⟩ : syracuseStep 3255025 = 2441269) B2441269
theorem B4340033 : Blo 1927435 4340033 := bstep (se 2 (by rfl) ⟨1627512, by rfl⟩ : syracuseStep 4340033 = 3255025) B3255025
theorem B2893355 : Blo 1927435 2893355 := bstep (se 1 (by rfl) ⟨2170016, by rfl⟩ : syracuseStep 2893355 = 4340033) B4340033
theorem B1928903 : Blo 1927435 1928903 := bstep (se 1 (by rfl) ⟨1446677, by rfl⟩ : syracuseStep 1928903 = 2893355) B2893355
theorem B2170021 : Blo 1927435 2170021 := bbase (se 4 (by rfl) ⟨203439, by rfl⟩ : syracuseStep 2170021 = 406879) (by norm_num)
theorem B2893361 : Blo 1927435 2893361 := bstep (se 2 (by rfl) ⟨1085010, by rfl⟩ : syracuseStep 2893361 = 2170021) B2170021
theorem B1928907 : Blo 1927435 1928907 := bstep (se 1 (by rfl) ⟨1446680, by rfl⟩ : syracuseStep 1928907 = 2893361) B2893361
theorem B6598901 : Blo 1927435 6598901 := bbase (se 5 (by rfl) ⟨309323, by rfl⟩ : syracuseStep 6598901 = 618647) (by norm_num)
theorem B4399267 : Blo 1927435 4399267 := bstep (se 1 (by rfl) ⟨3299450, by rfl⟩ : syracuseStep 4399267 = 6598901) B6598901
theorem B5865689 : Blo 1927435 5865689 := bstep (se 2 (by rfl) ⟨2199633, by rfl⟩ : syracuseStep 5865689 = 4399267) B4399267
theorem B3910459 : Blo 1927435 3910459 := bstep (se 1 (by rfl) ⟨2932844, by rfl⟩ : syracuseStep 3910459 = 5865689) B5865689
theorem B5213945 : Blo 1927435 5213945 := bstep (se 2 (by rfl) ⟨1955229, by rfl⟩ : syracuseStep 5213945 = 3910459) B3910459
theorem B3475963 : Blo 1927435 3475963 := bstep (se 1 (by rfl) ⟨2606972, by rfl⟩ : syracuseStep 3475963 = 5213945) B5213945
theorem B18538469 : Blo 1927435 18538469 := bstep (se 4 (by rfl) ⟨1737981, by rfl⟩ : syracuseStep 18538469 = 3475963) B3475963
theorem B12358979 : Blo 1927435 12358979 := bstep (se 1 (by rfl) ⟨9269234, by rfl⟩ : syracuseStep 12358979 = 18538469) B18538469
theorem B8239319 : Blo 1927435 8239319 := bstep (se 1 (by rfl) ⟨6179489, by rfl⟩ : syracuseStep 8239319 = 12358979) B12358979
theorem B5492879 : Blo 1927435 5492879 := bstep (se 1 (by rfl) ⟨4119659, by rfl⟩ : syracuseStep 5492879 = 8239319) B8239319
theorem B3661919 : Blo 1927435 3661919 := bstep (se 1 (by rfl) ⟨2746439, by rfl⟩ : syracuseStep 3661919 = 5492879) B5492879
theorem B2441279 : Blo 1927435 2441279 := bstep (se 1 (by rfl) ⟨1830959, by rfl⟩ : syracuseStep 2441279 = 3661919) B3661919
theorem B6510077 : Blo 1927435 6510077 := bstep (se 3 (by rfl) ⟨1220639, by rfl⟩ : syracuseStep 6510077 = 2441279) B2441279
theorem B4340051 : Blo 1927435 4340051 := bstep (se 1 (by rfl) ⟨3255038, by rfl⟩ : syracuseStep 4340051 = 6510077) B6510077
theorem B2893367 : Blo 1927435 2893367 := bstep (se 1 (by rfl) ⟨2170025, by rfl⟩ : syracuseStep 2893367 = 4340051) B4340051
theorem B1928911 : Blo 1927435 1928911 := bstep (se 1 (by rfl) ⟨1446683, by rfl⟩ : syracuseStep 1928911 = 2893367) B2893367
theorem B2893373 : Blo 1927435 2893373 := bbase (se 3 (by rfl) ⟨542507, by rfl⟩ : syracuseStep 2893373 = 1085015) (by norm_num)
theorem B1928915 : Blo 1927435 1928915 := bstep (se 1 (by rfl) ⟨1446686, by rfl⟩ : syracuseStep 1928915 = 2893373) B2893373
theorem B4340069 : Blo 1927435 4340069 := bbase (se 4 (by rfl) ⟨406881, by rfl⟩ : syracuseStep 4340069 = 813763) (by norm_num)
theorem B2893379 : Blo 1927435 2893379 := bstep (se 1 (by rfl) ⟨2170034, by rfl⟩ : syracuseStep 2893379 = 4340069) B4340069
theorem B1928919 : Blo 1927435 1928919 := bstep (se 1 (by rfl) ⟨1446689, by rfl⟩ : syracuseStep 1928919 = 2893379) B2893379
theorem B4882589 : Blo 1927435 4882589 := bbase (se 3 (by rfl) ⟨915485, by rfl⟩ : syracuseStep 4882589 = 1830971) (by norm_num)
theorem B3255059 : Blo 1927435 3255059 := bstep (se 1 (by rfl) ⟨2441294, by rfl⟩ : syracuseStep 3255059 = 4882589) B4882589
theorem B2170039 : Blo 1927435 2170039 := bstep (se 1 (by rfl) ⟨1627529, by rfl⟩ : syracuseStep 2170039 = 3255059) B3255059
theorem B2893385 : Blo 1927435 2893385 := bstep (se 2 (by rfl) ⟨1085019, by rfl⟩ : syracuseStep 2893385 = 2170039) B2170039
theorem B1928923 : Blo 1927435 1928923 := bstep (se 1 (by rfl) ⟨1446692, by rfl⟩ : syracuseStep 1928923 = 2893385) B2893385
theorem B3661949 : Blo 1927435 3661949 := bbase (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) (by norm_num)
theorem B9765197 : Blo 1927435 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B6510131 : Blo 1927435 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B4340087 : Blo 1927435 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B2893391 : Blo 1927435 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B1928927 : Blo 1927435 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B2893397 : Blo 1927435 2893397 := bbase (se 8 (by rfl) ⟨16953, by rfl⟩ : syracuseStep 2893397 = 33907) (by norm_num)
theorem B1928931 : Blo 1927435 1928931 := bstep (se 1 (by rfl) ⟨1446698, by rfl⟩ : syracuseStep 1928931 = 2893397) B2893397
theorem B2607005 : Blo 1927435 2607005 := bbase (se 3 (by rfl) ⟨488813, by rfl⟩ : syracuseStep 2607005 = 977627) (by norm_num)
theorem B6952013 : Blo 1927435 6952013 := bstep (se 3 (by rfl) ⟨1303502, by rfl⟩ : syracuseStep 6952013 = 2607005) B2607005
theorem B4634675 : Blo 1927435 4634675 := bstep (se 1 (by rfl) ⟨3476006, by rfl⟩ : syracuseStep 4634675 = 6952013) B6952013
theorem B3089783 : Blo 1927435 3089783 := bstep (se 1 (by rfl) ⟨2317337, by rfl⟩ : syracuseStep 3089783 = 4634675) B4634675
theorem B8239421 : Blo 1927435 8239421 := bstep (se 3 (by rfl) ⟨1544891, by rfl⟩ : syracuseStep 8239421 = 3089783) B3089783
theorem B5492947 : Blo 1927435 5492947 := bstep (se 1 (by rfl) ⟨4119710, by rfl⟩ : syracuseStep 5492947 = 8239421) B8239421
theorem B7323929 : Blo 1927435 7323929 := bstep (se 2 (by rfl) ⟨2746473, by rfl⟩ : syracuseStep 7323929 = 5492947) B5492947
theorem B4882619 : Blo 1927435 4882619 := bstep (se 1 (by rfl) ⟨3661964, by rfl⟩ : syracuseStep 4882619 = 7323929) B7323929
theorem B3255079 : Blo 1927435 3255079 := bstep (se 1 (by rfl) ⟨2441309, by rfl⟩ : syracuseStep 3255079 = 4882619) B4882619
theorem B4340105 : Blo 1927435 4340105 := bstep (se 2 (by rfl) ⟨1627539, by rfl⟩ : syracuseStep 4340105 = 3255079) B3255079
theorem B2893403 : Blo 1927435 2893403 := bstep (se 1 (by rfl) ⟨2170052, by rfl⟩ : syracuseStep 2893403 = 4340105) B4340105
theorem B1928935 : Blo 1927435 1928935 := bstep (se 1 (by rfl) ⟨1446701, by rfl⟩ : syracuseStep 1928935 = 2893403) B2893403
theorem B2170057 : Blo 1927435 2170057 := bbase (se 2 (by rfl) ⟨813771, by rfl⟩ : syracuseStep 2170057 = 1627543) (by norm_num)
theorem B2893409 : Blo 1927435 2893409 := bstep (se 2 (by rfl) ⟨1085028, by rfl⟩ : syracuseStep 2893409 = 2170057) B2170057
theorem B1928939 : Blo 1927435 1928939 := bstep (se 1 (by rfl) ⟨1446704, by rfl⟩ : syracuseStep 1928939 = 2893409) B2893409
theorem B2972909 : Blo 1927435 2972909 := bbase (se 3 (by rfl) ⟨557420, by rfl⟩ : syracuseStep 2972909 = 1114841) (by norm_num)
theorem B7927757 : Blo 1927435 7927757 := bstep (se 3 (by rfl) ⟨1486454, by rfl⟩ : syracuseStep 7927757 = 2972909) B2972909
theorem B5285171 : Blo 1927435 5285171 := bstep (se 1 (by rfl) ⟨3963878, by rfl⟩ : syracuseStep 5285171 = 7927757) B7927757
theorem B3523447 : Blo 1927435 3523447 := bstep (se 1 (by rfl) ⟨2642585, by rfl⟩ : syracuseStep 3523447 = 5285171) B5285171
theorem B4697929 : Blo 1927435 4697929 := bstep (se 2 (by rfl) ⟨1761723, by rfl⟩ : syracuseStep 4697929 = 3523447) B3523447
theorem B6263905 : Blo 1927435 6263905 := bstep (se 2 (by rfl) ⟨2348964, by rfl⟩ : syracuseStep 6263905 = 4697929) B4697929
theorem B8351873 : Blo 1927435 8351873 := bstep (se 2 (by rfl) ⟨3131952, by rfl⟩ : syracuseStep 8351873 = 6263905) B6263905
theorem B5567915 : Blo 1927435 5567915 := bstep (se 1 (by rfl) ⟨4175936, by rfl⟩ : syracuseStep 5567915 = 8351873) B8351873
theorem B3711943 : Blo 1927435 3711943 := bstep (se 1 (by rfl) ⟨2783957, by rfl⟩ : syracuseStep 3711943 = 5567915) B5567915
theorem B4949257 : Blo 1927435 4949257 := bstep (se 2 (by rfl) ⟨1855971, by rfl⟩ : syracuseStep 4949257 = 3711943) B3711943
theorem B6599009 : Blo 1927435 6599009 := bstep (se 2 (by rfl) ⟨2474628, by rfl⟩ : syracuseStep 6599009 = 4949257) B4949257
theorem B4399339 : Blo 1927435 4399339 := bstep (se 1 (by rfl) ⟨3299504, by rfl⟩ : syracuseStep 4399339 = 6599009) B6599009
theorem B5865785 : Blo 1927435 5865785 := bstep (se 2 (by rfl) ⟨2199669, by rfl⟩ : syracuseStep 5865785 = 4399339) B4399339
theorem B3910523 : Blo 1927435 3910523 := bstep (se 1 (by rfl) ⟨2932892, by rfl⟩ : syracuseStep 3910523 = 5865785) B5865785
theorem B10428061 : Blo 1927435 10428061 := bstep (se 3 (by rfl) ⟨1955261, by rfl⟩ : syracuseStep 10428061 = 3910523) B3910523
theorem B13904081 : Blo 1927435 13904081 := bstep (se 2 (by rfl) ⟨5214030, by rfl⟩ : syracuseStep 13904081 = 10428061) B10428061
theorem B9269387 : Blo 1927435 9269387 := bstep (se 1 (by rfl) ⟨6952040, by rfl⟩ : syracuseStep 9269387 = 13904081) B13904081
theorem B6179591 : Blo 1927435 6179591 := bstep (se 1 (by rfl) ⟨4634693, by rfl⟩ : syracuseStep 6179591 = 9269387) B9269387
theorem B16478909 : Blo 1927435 16478909 := bstep (se 3 (by rfl) ⟨3089795, by rfl⟩ : syracuseStep 16478909 = 6179591) B6179591
theorem B10985939 : Blo 1927435 10985939 := bstep (se 1 (by rfl) ⟨8239454, by rfl⟩ : syracuseStep 10985939 = 16478909) B16478909
theorem B7323959 : Blo 1927435 7323959 := bstep (se 1 (by rfl) ⟨5492969, by rfl⟩ : syracuseStep 7323959 = 10985939) B10985939
theorem B4882639 : Blo 1927435 4882639 := bstep (se 1 (by rfl) ⟨3661979, by rfl⟩ : syracuseStep 4882639 = 7323959) B7323959
theorem B6510185 : Blo 1927435 6510185 := bstep (se 2 (by rfl) ⟨2441319, by rfl⟩ : syracuseStep 6510185 = 4882639) B4882639
theorem B4340123 : Blo 1927435 4340123 := bstep (se 1 (by rfl) ⟨3255092, by rfl⟩ : syracuseStep 4340123 = 6510185) B6510185
theorem B2893415 : Blo 1927435 2893415 := bstep (se 1 (by rfl) ⟨2170061, by rfl⟩ : syracuseStep 2893415 = 4340123) B4340123
theorem B1928943 : Blo 1927435 1928943 := bstep (se 1 (by rfl) ⟨1446707, by rfl⟩ : syracuseStep 1928943 = 2893415) B2893415
theorem B2893421 : Blo 1927435 2893421 := bbase (se 3 (by rfl) ⟨542516, by rfl⟩ : syracuseStep 2893421 = 1085033) (by norm_num)
theorem B1928947 : Blo 1927435 1928947 := bstep (se 1 (by rfl) ⟨1446710, by rfl⟩ : syracuseStep 1928947 = 2893421) B2893421
theorem B4340141 : Blo 1927435 4340141 := bbase (se 3 (by rfl) ⟨813776, by rfl⟩ : syracuseStep 4340141 = 1627553) (by norm_num)
theorem B2893427 : Blo 1927435 2893427 := bstep (se 1 (by rfl) ⟨2170070, by rfl⟩ : syracuseStep 2893427 = 4340141) B4340141
theorem B1928951 : Blo 1927435 1928951 := bstep (se 1 (by rfl) ⟨1446713, by rfl⟩ : syracuseStep 1928951 = 2893427) B2893427
theorem B2059877 : Blo 1927435 2059877 := bbase (se 4 (by rfl) ⟨193113, by rfl⟩ : syracuseStep 2059877 = 386227) (by norm_num)
theorem B5493005 : Blo 1927435 5493005 := bstep (se 3 (by rfl) ⟨1029938, by rfl⟩ : syracuseStep 5493005 = 2059877) B2059877
theorem B3662003 : Blo 1927435 3662003 := bstep (se 1 (by rfl) ⟨2746502, by rfl⟩ : syracuseStep 3662003 = 5493005) B5493005
theorem B2441335 : Blo 1927435 2441335 := bstep (se 1 (by rfl) ⟨1831001, by rfl⟩ : syracuseStep 2441335 = 3662003) B3662003
theorem B3255113 : Blo 1927435 3255113 := bstep (se 2 (by rfl) ⟨1220667, by rfl⟩ : syracuseStep 3255113 = 2441335) B2441335
theorem B2170075 : Blo 1927435 2170075 := bstep (se 1 (by rfl) ⟨1627556, by rfl⟩ : syracuseStep 2170075 = 3255113) B3255113
theorem B2893433 : Blo 1927435 2893433 := bstep (se 2 (by rfl) ⟨1085037, by rfl⟩ : syracuseStep 2893433 = 2170075) B2170075
theorem B1928955 : Blo 1927435 1928955 := bstep (se 1 (by rfl) ⟨1446716, by rfl⟩ : syracuseStep 1928955 = 2893433) B2893433
theorem B5016821 : Blo 1927435 5016821 := bbase (se 5 (by rfl) ⟨235163, by rfl⟩ : syracuseStep 5016821 = 470327) (by norm_num)
theorem B13378189 : Blo 1927435 13378189 := bstep (se 3 (by rfl) ⟨2508410, by rfl⟩ : syracuseStep 13378189 = 5016821) B5016821
theorem B17837585 : Blo 1927435 17837585 := bstep (se 2 (by rfl) ⟨6689094, by rfl⟩ : syracuseStep 17837585 = 13378189) B13378189
theorem B11891723 : Blo 1927435 11891723 := bstep (se 1 (by rfl) ⟨8918792, by rfl⟩ : syracuseStep 11891723 = 17837585) B17837585
theorem B31711261 : Blo 1927435 31711261 := bstep (se 3 (by rfl) ⟨5945861, by rfl⟩ : syracuseStep 31711261 = 11891723) B11891723
theorem B42281681 : Blo 1927435 42281681 := bstep (se 2 (by rfl) ⟨15855630, by rfl⟩ : syracuseStep 42281681 = 31711261) B31711261
theorem B451004597 : Blo 1927435 451004597 := bstep (se 5 (by rfl) ⟨21140840, by rfl⟩ : syracuseStep 451004597 = 42281681) B42281681
theorem B300669731 : Blo 1927435 300669731 := bstep (se 1 (by rfl) ⟨225502298, by rfl⟩ : syracuseStep 300669731 = 451004597) B451004597
theorem B200446487 : Blo 1927435 200446487 := bstep (se 1 (by rfl) ⟨150334865, by rfl⟩ : syracuseStep 200446487 = 300669731) B300669731
theorem B133630991 : Blo 1927435 133630991 := bstep (se 1 (by rfl) ⟨100223243, by rfl⟩ : syracuseStep 133630991 = 200446487) B200446487
theorem B89087327 : Blo 1927435 89087327 := bstep (se 1 (by rfl) ⟨66815495, by rfl⟩ : syracuseStep 89087327 = 133630991) B133630991
theorem B59391551 : Blo 1927435 59391551 := bstep (se 1 (by rfl) ⟨44543663, by rfl⟩ : syracuseStep 59391551 = 89087327) B89087327
theorem B39594367 : Blo 1927435 39594367 := bstep (se 1 (by rfl) ⟨29695775, by rfl⟩ : syracuseStep 39594367 = 59391551) B59391551
theorem B52792489 : Blo 1927435 52792489 := bstep (se 2 (by rfl) ⟨19797183, by rfl⟩ : syracuseStep 52792489 = 39594367) B39594367
theorem B70389985 : Blo 1927435 70389985 := bstep (se 2 (by rfl) ⟨26396244, by rfl⟩ : syracuseStep 70389985 = 52792489) B52792489
theorem B93853313 : Blo 1927435 93853313 := bstep (se 2 (by rfl) ⟨35194992, by rfl⟩ : syracuseStep 93853313 = 70389985) B70389985
theorem B62568875 : Blo 1927435 62568875 := bstep (se 1 (by rfl) ⟨46926656, by rfl⟩ : syracuseStep 62568875 = 93853313) B93853313
theorem B41712583 : Blo 1927435 41712583 := bstep (se 1 (by rfl) ⟨31284437, by rfl⟩ : syracuseStep 41712583 = 62568875) B62568875
theorem B55616777 : Blo 1927435 55616777 := bstep (se 2 (by rfl) ⟨20856291, by rfl⟩ : syracuseStep 55616777 = 41712583) B41712583
theorem B37077851 : Blo 1927435 37077851 := bstep (se 1 (by rfl) ⟨27808388, by rfl⟩ : syracuseStep 37077851 = 55616777) B55616777
theorem B24718567 : Blo 1927435 24718567 := bstep (se 1 (by rfl) ⟨18538925, by rfl⟩ : syracuseStep 24718567 = 37077851) B37077851
theorem B32958089 : Blo 1927435 32958089 := bstep (se 2 (by rfl) ⟨12359283, by rfl⟩ : syracuseStep 32958089 = 24718567) B24718567
theorem B21972059 : Blo 1927435 21972059 := bstep (se 1 (by rfl) ⟨16479044, by rfl⟩ : syracuseStep 21972059 = 32958089) B32958089
theorem B14648039 : Blo 1927435 14648039 := bstep (se 1 (by rfl) ⟨10986029, by rfl⟩ : syracuseStep 14648039 = 21972059) B21972059
theorem B9765359 : Blo 1927435 9765359 := bstep (se 1 (by rfl) ⟨7324019, by rfl⟩ : syracuseStep 9765359 = 14648039) B14648039
theorem B6510239 : Blo 1927435 6510239 := bstep (se 1 (by rfl) ⟨4882679, by rfl⟩ : syracuseStep 6510239 = 9765359) B9765359
theorem B4340159 : Blo 1927435 4340159 := bstep (se 1 (by rfl) ⟨3255119, by rfl⟩ : syracuseStep 4340159 = 6510239) B6510239
theorem B2893439 : Blo 1927435 2893439 := bstep (se 1 (by rfl) ⟨2170079, by rfl⟩ : syracuseStep 2893439 = 4340159) B4340159
theorem B1928959 : Blo 1927435 1928959 := bstep (se 1 (by rfl) ⟨1446719, by rfl⟩ : syracuseStep 1928959 = 2893439) B2893439
theorem B2893445 : Blo 1927435 2893445 := bbase (se 4 (by rfl) ⟨271260, by rfl⟩ : syracuseStep 2893445 = 542521) (by norm_num)
theorem B1928963 : Blo 1927435 1928963 := bstep (se 1 (by rfl) ⟨1446722, by rfl⟩ : syracuseStep 1928963 = 2893445) B2893445
theorem B3255133 : Blo 1927435 3255133 := bbase (se 3 (by rfl) ⟨610337, by rfl⟩ : syracuseStep 3255133 = 1220675) (by norm_num)
theorem B4340177 : Blo 1927435 4340177 := bstep (se 2 (by rfl) ⟨1627566, by rfl⟩ : syracuseStep 4340177 = 3255133) B3255133
theorem B2893451 : Blo 1927435 2893451 := bstep (se 1 (by rfl) ⟨2170088, by rfl⟩ : syracuseStep 2893451 = 4340177) B4340177
theorem B1928967 : Blo 1927435 1928967 := bstep (se 1 (by rfl) ⟨1446725, by rfl⟩ : syracuseStep 1928967 = 2893451) B2893451
theorem B2170093 : Blo 1927435 2170093 := bbase (se 3 (by rfl) ⟨406892, by rfl⟩ : syracuseStep 2170093 = 813785) (by norm_num)
theorem B2893457 : Blo 1927435 2893457 := bstep (se 2 (by rfl) ⟨1085046, by rfl⟩ : syracuseStep 2893457 = 2170093) B2170093
theorem B1928971 : Blo 1927435 1928971 := bstep (se 1 (by rfl) ⟨1446728, by rfl⟩ : syracuseStep 1928971 = 2893457) B2893457
theorem B6510293 : Blo 1927435 6510293 := bbase (se 7 (by rfl) ⟨76292, by rfl⟩ : syracuseStep 6510293 = 152585) (by norm_num)
theorem B4340195 : Blo 1927435 4340195 := bstep (se 1 (by rfl) ⟨3255146, by rfl⟩ : syracuseStep 4340195 = 6510293) B6510293
theorem B2893463 : Blo 1927435 2893463 := bstep (se 1 (by rfl) ⟨2170097, by rfl⟩ : syracuseStep 2893463 = 4340195) B4340195
theorem B1928975 : Blo 1927435 1928975 := bstep (se 1 (by rfl) ⟨1446731, by rfl⟩ : syracuseStep 1928975 = 2893463) B2893463
theorem B2893469 : Blo 1927435 2893469 := bbase (se 3 (by rfl) ⟨542525, by rfl⟩ : syracuseStep 2893469 = 1085051) (by norm_num)
theorem B1928979 : Blo 1927435 1928979 := bstep (se 1 (by rfl) ⟨1446734, by rfl⟩ : syracuseStep 1928979 = 2893469) B2893469
theorem B4340213 : Blo 1927435 4340213 := bbase (se 5 (by rfl) ⟨203447, by rfl⟩ : syracuseStep 4340213 = 406895) (by norm_num)
theorem B2893475 : Blo 1927435 2893475 := bstep (se 1 (by rfl) ⟨2170106, by rfl⟩ : syracuseStep 2893475 = 4340213) B4340213
theorem B1928983 : Blo 1927435 1928983 := bstep (se 1 (by rfl) ⟨1446737, by rfl⟩ : syracuseStep 1928983 = 2893475) B2893475
theorem B5721013 : Blo 1927435 5721013 := bbase (se 5 (by rfl) ⟨268172, by rfl⟩ : syracuseStep 5721013 = 536345) (by norm_num)
theorem B7628017 : Blo 1927435 7628017 := bstep (se 2 (by rfl) ⟨2860506, by rfl⟩ : syracuseStep 7628017 = 5721013) B5721013
theorem B10170689 : Blo 1927435 10170689 := bstep (se 2 (by rfl) ⟨3814008, by rfl⟩ : syracuseStep 10170689 = 7628017) B7628017
theorem B27121837 : Blo 1927435 27121837 := bstep (se 3 (by rfl) ⟨5085344, by rfl⟩ : syracuseStep 27121837 = 10170689) B10170689
theorem B36162449 : Blo 1927435 36162449 := bstep (se 2 (by rfl) ⟨13560918, by rfl⟩ : syracuseStep 36162449 = 27121837) B27121837
theorem B24108299 : Blo 1927435 24108299 := bstep (se 1 (by rfl) ⟨18081224, by rfl⟩ : syracuseStep 24108299 = 36162449) B36162449
theorem B16072199 : Blo 1927435 16072199 := bstep (se 1 (by rfl) ⟨12054149, by rfl⟩ : syracuseStep 16072199 = 24108299) B24108299
theorem B10714799 : Blo 1927435 10714799 := bstep (se 1 (by rfl) ⟨8036099, by rfl⟩ : syracuseStep 10714799 = 16072199) B16072199
theorem B28572797 : Blo 1927435 28572797 := bstep (se 3 (by rfl) ⟨5357399, by rfl⟩ : syracuseStep 28572797 = 10714799) B10714799
theorem B19048531 : Blo 1927435 19048531 := bstep (se 1 (by rfl) ⟨14286398, by rfl⟩ : syracuseStep 19048531 = 28572797) B28572797
theorem B25398041 : Blo 1927435 25398041 := bstep (se 2 (by rfl) ⟨9524265, by rfl⟩ : syracuseStep 25398041 = 19048531) B19048531
theorem B270912437 : Blo 1927435 270912437 := bstep (se 5 (by rfl) ⟨12699020, by rfl⟩ : syracuseStep 270912437 = 25398041) B25398041
theorem B180608291 : Blo 1927435 180608291 := bstep (se 1 (by rfl) ⟨135456218, by rfl⟩ : syracuseStep 180608291 = 270912437) B270912437
theorem B120405527 : Blo 1927435 120405527 := bstep (se 1 (by rfl) ⟨90304145, by rfl⟩ : syracuseStep 120405527 = 180608291) B180608291
theorem B80270351 : Blo 1927435 80270351 := bstep (se 1 (by rfl) ⟨60202763, by rfl⟩ : syracuseStep 80270351 = 120405527) B120405527
theorem B53513567 : Blo 1927435 53513567 := bstep (se 1 (by rfl) ⟨40135175, by rfl⟩ : syracuseStep 53513567 = 80270351) B80270351
theorem B35675711 : Blo 1927435 35675711 := bstep (se 1 (by rfl) ⟨26756783, by rfl⟩ : syracuseStep 35675711 = 53513567) B53513567
theorem B23783807 : Blo 1927435 23783807 := bstep (se 1 (by rfl) ⟨17837855, by rfl⟩ : syracuseStep 23783807 = 35675711) B35675711
theorem B15855871 : Blo 1927435 15855871 := bstep (se 1 (by rfl) ⟨11891903, by rfl⟩ : syracuseStep 15855871 = 23783807) B23783807
theorem B21141161 : Blo 1927435 21141161 := bstep (se 2 (by rfl) ⟨7927935, by rfl⟩ : syracuseStep 21141161 = 15855871) B15855871
theorem B14094107 : Blo 1927435 14094107 := bstep (se 1 (by rfl) ⟨10570580, by rfl⟩ : syracuseStep 14094107 = 21141161) B21141161
theorem B9396071 : Blo 1927435 9396071 := bstep (se 1 (by rfl) ⟨7047053, by rfl⟩ : syracuseStep 9396071 = 14094107) B14094107
theorem B6264047 : Blo 1927435 6264047 := bstep (se 1 (by rfl) ⟨4698035, by rfl⟩ : syracuseStep 6264047 = 9396071) B9396071
theorem B4176031 : Blo 1927435 4176031 := bstep (se 1 (by rfl) ⟨3132023, by rfl⟩ : syracuseStep 4176031 = 6264047) B6264047
theorem B5568041 : Blo 1927435 5568041 := bstep (se 2 (by rfl) ⟨2088015, by rfl⟩ : syracuseStep 5568041 = 4176031) B4176031
theorem B14848109 : Blo 1927435 14848109 := bstep (se 3 (by rfl) ⟨2784020, by rfl⟩ : syracuseStep 14848109 = 5568041) B5568041
theorem B9898739 : Blo 1927435 9898739 := bstep (se 1 (by rfl) ⟨7424054, by rfl⟩ : syracuseStep 9898739 = 14848109) B14848109
theorem B6599159 : Blo 1927435 6599159 := bstep (se 1 (by rfl) ⟨4949369, by rfl⟩ : syracuseStep 6599159 = 9898739) B9898739
theorem B4399439 : Blo 1927435 4399439 := bstep (se 1 (by rfl) ⟨3299579, by rfl⟩ : syracuseStep 4399439 = 6599159) B6599159
theorem B46927349 : Blo 1927435 46927349 := bstep (se 5 (by rfl) ⟨2199719, by rfl⟩ : syracuseStep 46927349 = 4399439) B4399439
theorem B31284899 : Blo 1927435 31284899 := bstep (se 1 (by rfl) ⟨23463674, by rfl⟩ : syracuseStep 31284899 = 46927349) B46927349
theorem B20856599 : Blo 1927435 20856599 := bstep (se 1 (by rfl) ⟨15642449, by rfl⟩ : syracuseStep 20856599 = 31284899) B31284899
theorem B13904399 : Blo 1927435 13904399 := bstep (se 1 (by rfl) ⟨10428299, by rfl⟩ : syracuseStep 13904399 = 20856599) B20856599
theorem B37078397 : Blo 1927435 37078397 := bstep (se 3 (by rfl) ⟨6952199, by rfl⟩ : syracuseStep 37078397 = 13904399) B13904399
theorem B24718931 : Blo 1927435 24718931 := bstep (se 1 (by rfl) ⟨18539198, by rfl⟩ : syracuseStep 24718931 = 37078397) B37078397
theorem B16479287 : Blo 1927435 16479287 := bstep (se 1 (by rfl) ⟨12359465, by rfl⟩ : syracuseStep 16479287 = 24718931) B24718931
theorem B10986191 : Blo 1927435 10986191 := bstep (se 1 (by rfl) ⟨8239643, by rfl⟩ : syracuseStep 10986191 = 16479287) B16479287
theorem B7324127 : Blo 1927435 7324127 := bstep (se 1 (by rfl) ⟨5493095, by rfl⟩ : syracuseStep 7324127 = 10986191) B10986191
theorem B4882751 : Blo 1927435 4882751 := bstep (se 1 (by rfl) ⟨3662063, by rfl⟩ : syracuseStep 4882751 = 7324127) B7324127
theorem B3255167 : Blo 1927435 3255167 := bstep (se 1 (by rfl) ⟨2441375, by rfl⟩ : syracuseStep 3255167 = 4882751) B4882751
theorem B2170111 : Blo 1927435 2170111 := bstep (se 1 (by rfl) ⟨1627583, by rfl⟩ : syracuseStep 2170111 = 3255167) B3255167
theorem B2893481 : Blo 1927435 2893481 := bstep (se 2 (by rfl) ⟨1085055, by rfl⟩ : syracuseStep 2893481 = 2170111) B2170111
theorem B1928987 : Blo 1927435 1928987 := bstep (se 1 (by rfl) ⟨1446740, by rfl⟩ : syracuseStep 1928987 = 2893481) B2893481
theorem B2317405 : Blo 1927435 2317405 := bbase (se 3 (by rfl) ⟨434513, by rfl⟩ : syracuseStep 2317405 = 869027) (by norm_num)
theorem B3089873 : Blo 1927435 3089873 := bstep (se 2 (by rfl) ⟨1158702, by rfl⟩ : syracuseStep 3089873 = 2317405) B2317405
theorem B2059915 : Blo 1927435 2059915 := bstep (se 1 (by rfl) ⟨1544936, by rfl⟩ : syracuseStep 2059915 = 3089873) B3089873
theorem B2746553 : Blo 1927435 2746553 := bstep (se 2 (by rfl) ⟨1029957, by rfl⟩ : syracuseStep 2746553 = 2059915) B2059915
theorem B7324141 : Blo 1927435 7324141 := bstep (se 3 (by rfl) ⟨1373276, by rfl⟩ : syracuseStep 7324141 = 2746553) B2746553
theorem B9765521 : Blo 1927435 9765521 := bstep (se 2 (by rfl) ⟨3662070, by rfl⟩ : syracuseStep 9765521 = 7324141) B7324141
theorem B6510347 : Blo 1927435 6510347 := bstep (se 1 (by rfl) ⟨4882760, by rfl⟩ : syracuseStep 6510347 = 9765521) B9765521
theorem B4340231 : Blo 1927435 4340231 := bstep (se 1 (by rfl) ⟨3255173, by rfl⟩ : syracuseStep 4340231 = 6510347) B6510347
theorem B2893487 : Blo 1927435 2893487 := bstep (se 1 (by rfl) ⟨2170115, by rfl⟩ : syracuseStep 2893487 = 4340231) B4340231
theorem B1928991 : Blo 1927435 1928991 := bstep (se 1 (by rfl) ⟨1446743, by rfl⟩ : syracuseStep 1928991 = 2893487) B2893487
theorem B2893493 : Blo 1927435 2893493 := bbase (se 5 (by rfl) ⟨135632, by rfl⟩ : syracuseStep 2893493 = 271265) (by norm_num)
theorem B1928995 : Blo 1927435 1928995 := bstep (se 1 (by rfl) ⟨1446746, by rfl⟩ : syracuseStep 1928995 = 2893493) B2893493
theorem B4882781 : Blo 1927435 4882781 := bbase (se 3 (by rfl) ⟨915521, by rfl⟩ : syracuseStep 4882781 = 1831043) (by norm_num)
theorem B3255187 : Blo 1927435 3255187 := bstep (se 1 (by rfl) ⟨2441390, by rfl⟩ : syracuseStep 3255187 = 4882781) B4882781
theorem B4340249 : Blo 1927435 4340249 := bstep (se 2 (by rfl) ⟨1627593, by rfl⟩ : syracuseStep 4340249 = 3255187) B3255187
theorem B2893499 : Blo 1927435 2893499 := bstep (se 1 (by rfl) ⟨2170124, by rfl⟩ : syracuseStep 2893499 = 4340249) B4340249
theorem B1928999 : Blo 1927435 1928999 := bstep (se 1 (by rfl) ⟨1446749, by rfl⟩ : syracuseStep 1928999 = 2893499) B2893499
theorem B2170129 : Blo 1927435 2170129 := bbase (se 2 (by rfl) ⟨813798, by rfl⟩ : syracuseStep 2170129 = 1627597) (by norm_num)
theorem B2893505 : Blo 1927435 2893505 := bstep (se 2 (by rfl) ⟨1085064, by rfl⟩ : syracuseStep 2893505 = 2170129) B2170129
theorem B1929003 : Blo 1927435 1929003 := bstep (se 1 (by rfl) ⟨1446752, by rfl⟩ : syracuseStep 1929003 = 2893505) B2893505
theorem B3662101 : Blo 1927435 3662101 := bbase (se 6 (by rfl) ⟨85830, by rfl⟩ : syracuseStep 3662101 = 171661) (by norm_num)
theorem B4882801 : Blo 1927435 4882801 := bstep (se 2 (by rfl) ⟨1831050, by rfl⟩ : syracuseStep 4882801 = 3662101) B3662101
theorem B6510401 : Blo 1927435 6510401 := bstep (se 2 (by rfl) ⟨2441400, by rfl⟩ : syracuseStep 6510401 = 4882801) B4882801
theorem B4340267 : Blo 1927435 4340267 := bstep (se 1 (by rfl) ⟨3255200, by rfl⟩ : syracuseStep 4340267 = 6510401) B6510401
theorem B2893511 : Blo 1927435 2893511 := bstep (se 1 (by rfl) ⟨2170133, by rfl⟩ : syracuseStep 2893511 = 4340267) B4340267
theorem B1929007 : Blo 1927435 1929007 := bstep (se 1 (by rfl) ⟨1446755, by rfl⟩ : syracuseStep 1929007 = 2893511) B2893511
theorem B2893517 : Blo 1927435 2893517 := bbase (se 3 (by rfl) ⟨542534, by rfl⟩ : syracuseStep 2893517 = 1085069) (by norm_num)
theorem B1929011 : Blo 1927435 1929011 := bstep (se 1 (by rfl) ⟨1446758, by rfl⟩ : syracuseStep 1929011 = 2893517) B2893517
theorem B4340285 : Blo 1927435 4340285 := bbase (se 3 (by rfl) ⟨813803, by rfl⟩ : syracuseStep 4340285 = 1627607) (by norm_num)
theorem B2893523 : Blo 1927435 2893523 := bstep (se 1 (by rfl) ⟨2170142, by rfl⟩ : syracuseStep 2893523 = 4340285) B4340285
theorem B1929015 : Blo 1927435 1929015 := bstep (se 1 (by rfl) ⟨1446761, by rfl⟩ : syracuseStep 1929015 = 2893523) B2893523
theorem B3255221 : Blo 1927435 3255221 := bbase (se 5 (by rfl) ⟨152588, by rfl⟩ : syracuseStep 3255221 = 305177) (by norm_num)
theorem B2170147 : Blo 1927435 2170147 := bstep (se 1 (by rfl) ⟨1627610, by rfl⟩ : syracuseStep 2170147 = 3255221) B3255221
theorem B2893529 : Blo 1927435 2893529 := bstep (se 2 (by rfl) ⟨1085073, by rfl⟩ : syracuseStep 2893529 = 2170147) B2170147
theorem B1929019 : Blo 1927435 1929019 := bstep (se 1 (by rfl) ⟨1446764, by rfl⟩ : syracuseStep 1929019 = 2893529) B2893529
theorem B2059949 : Blo 1927435 2059949 := bbase (se 3 (by rfl) ⟨386240, by rfl⟩ : syracuseStep 2059949 = 772481) (by norm_num)
theorem B5493197 : Blo 1927435 5493197 := bstep (se 3 (by rfl) ⟨1029974, by rfl⟩ : syracuseStep 5493197 = 2059949) B2059949
theorem B14648525 : Blo 1927435 14648525 := bstep (se 3 (by rfl) ⟨2746598, by rfl⟩ : syracuseStep 14648525 = 5493197) B5493197
theorem B9765683 : Blo 1927435 9765683 := bstep (se 1 (by rfl) ⟨7324262, by rfl⟩ : syracuseStep 9765683 = 14648525) B14648525
theorem B6510455 : Blo 1927435 6510455 := bstep (se 1 (by rfl) ⟨4882841, by rfl⟩ : syracuseStep 6510455 = 9765683) B9765683
theorem B4340303 : Blo 1927435 4340303 := bstep (se 1 (by rfl) ⟨3255227, by rfl⟩ : syracuseStep 4340303 = 6510455) B6510455
theorem B2893535 : Blo 1927435 2893535 := bstep (se 1 (by rfl) ⟨2170151, by rfl⟩ : syracuseStep 2893535 = 4340303) B4340303
theorem B1929023 : Blo 1927435 1929023 := bstep (se 1 (by rfl) ⟨1446767, by rfl⟩ : syracuseStep 1929023 = 2893535) B2893535
theorem B2893541 : Blo 1927435 2893541 := bbase (se 4 (by rfl) ⟨271269, by rfl⟩ : syracuseStep 2893541 = 542539) (by norm_num)
theorem B1929027 : Blo 1927435 1929027 := bstep (se 1 (by rfl) ⟨1446770, by rfl⟩ : syracuseStep 1929027 = 2893541) B2893541
theorem B5493221 : Blo 1927435 5493221 := bbase (se 4 (by rfl) ⟨514989, by rfl⟩ : syracuseStep 5493221 = 1029979) (by norm_num)
theorem B3662147 : Blo 1927435 3662147 := bstep (se 1 (by rfl) ⟨2746610, by rfl⟩ : syracuseStep 3662147 = 5493221) B5493221
theorem B2441431 : Blo 1927435 2441431 := bstep (se 1 (by rfl) ⟨1831073, by rfl⟩ : syracuseStep 2441431 = 3662147) B3662147
theorem B3255241 : Blo 1927435 3255241 := bstep (se 2 (by rfl) ⟨1220715, by rfl⟩ : syracuseStep 3255241 = 2441431) B2441431
theorem B4340321 : Blo 1927435 4340321 := bstep (se 2 (by rfl) ⟨1627620, by rfl⟩ : syracuseStep 4340321 = 3255241) B3255241
theorem B2893547 : Blo 1927435 2893547 := bstep (se 1 (by rfl) ⟨2170160, by rfl⟩ : syracuseStep 2893547 = 4340321) B4340321
theorem B1929031 : Blo 1927435 1929031 := bstep (se 1 (by rfl) ⟨1446773, by rfl⟩ : syracuseStep 1929031 = 2893547) B2893547
theorem B2170165 : Blo 1927435 2170165 := bbase (se 5 (by rfl) ⟨101726, by rfl⟩ : syracuseStep 2170165 = 203453) (by norm_num)
theorem B2893553 : Blo 1927435 2893553 := bstep (se 2 (by rfl) ⟨1085082, by rfl⟩ : syracuseStep 2893553 = 2170165) B2170165
theorem B1929035 : Blo 1927435 1929035 := bstep (se 1 (by rfl) ⟨1446776, by rfl⟩ : syracuseStep 1929035 = 2893553) B2893553
theorem B2441441 : Blo 1927435 2441441 := bbase (se 2 (by rfl) ⟨915540, by rfl⟩ : syracuseStep 2441441 = 1831081) (by norm_num)
theorem B6510509 : Blo 1927435 6510509 := bstep (se 3 (by rfl) ⟨1220720, by rfl⟩ : syracuseStep 6510509 = 2441441) B2441441
theorem B4340339 : Blo 1927435 4340339 := bstep (se 1 (by rfl) ⟨3255254, by rfl⟩ : syracuseStep 4340339 = 6510509) B6510509
theorem B2893559 : Blo 1927435 2893559 := bstep (se 1 (by rfl) ⟨2170169, by rfl⟩ : syracuseStep 2893559 = 4340339) B4340339
theorem B1929039 : Blo 1927435 1929039 := bstep (se 1 (by rfl) ⟨1446779, by rfl⟩ : syracuseStep 1929039 = 2893559) B2893559
theorem B2893565 : Blo 1927435 2893565 := bbase (se 3 (by rfl) ⟨542543, by rfl⟩ : syracuseStep 2893565 = 1085087) (by norm_num)
theorem B1929043 : Blo 1927435 1929043 := bstep (se 1 (by rfl) ⟨1446782, by rfl⟩ : syracuseStep 1929043 = 2893565) B2893565
theorem B4340357 : Blo 1927435 4340357 := bbase (se 4 (by rfl) ⟨406908, by rfl⟩ : syracuseStep 4340357 = 813817) (by norm_num)
theorem B2893571 : Blo 1927435 2893571 := bstep (se 1 (by rfl) ⟨2170178, by rfl⟩ : syracuseStep 2893571 = 4340357) B4340357
theorem B1929047 : Blo 1927435 1929047 := bstep (se 1 (by rfl) ⟨1446785, by rfl⟩ : syracuseStep 1929047 = 2893571) B2893571
theorem B9269909 : Blo 1927435 9269909 := bbase (se 6 (by rfl) ⟨217263, by rfl⟩ : syracuseStep 9269909 = 434527) (by norm_num)
theorem B6179939 : Blo 1927435 6179939 := bstep (se 1 (by rfl) ⟨4634954, by rfl⟩ : syracuseStep 6179939 = 9269909) B9269909
theorem B4119959 : Blo 1927435 4119959 := bstep (se 1 (by rfl) ⟨3089969, by rfl⟩ : syracuseStep 4119959 = 6179939) B6179939
theorem B2746639 : Blo 1927435 2746639 := bstep (se 1 (by rfl) ⟨2059979, by rfl⟩ : syracuseStep 2746639 = 4119959) B4119959
theorem B3662185 : Blo 1927435 3662185 := bstep (se 2 (by rfl) ⟨1373319, by rfl⟩ : syracuseStep 3662185 = 2746639) B2746639
theorem B4882913 : Blo 1927435 4882913 := bstep (se 2 (by rfl) ⟨1831092, by rfl⟩ : syracuseStep 4882913 = 3662185) B3662185
theorem B3255275 : Blo 1927435 3255275 := bstep (se 1 (by rfl) ⟨2441456, by rfl⟩ : syracuseStep 3255275 = 4882913) B4882913
theorem B2170183 : Blo 1927435 2170183 := bstep (se 1 (by rfl) ⟨1627637, by rfl⟩ : syracuseStep 2170183 = 3255275) B3255275
theorem B2893577 : Blo 1927435 2893577 := bstep (se 2 (by rfl) ⟨1085091, by rfl⟩ : syracuseStep 2893577 = 2170183) B2170183
theorem B1929051 : Blo 1927435 1929051 := bstep (se 1 (by rfl) ⟨1446788, by rfl⟩ : syracuseStep 1929051 = 2893577) B2893577
theorem B9765845 : Blo 1927435 9765845 := bbase (se 7 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 9765845 = 228887) (by norm_num)
theorem B6510563 : Blo 1927435 6510563 := bstep (se 1 (by rfl) ⟨4882922, by rfl⟩ : syracuseStep 6510563 = 9765845) B9765845
theorem B4340375 : Blo 1927435 4340375 := bstep (se 1 (by rfl) ⟨3255281, by rfl⟩ : syracuseStep 4340375 = 6510563) B6510563
theorem B2893583 : Blo 1927435 2893583 := bstep (se 1 (by rfl) ⟨2170187, by rfl⟩ : syracuseStep 2893583 = 4340375) B4340375
theorem B1929055 : Blo 1927435 1929055 := bstep (se 1 (by rfl) ⟨1446791, by rfl⟩ : syracuseStep 1929055 = 2893583) B2893583
theorem B2893589 : Blo 1927435 2893589 := bbase (se 6 (by rfl) ⟨67818, by rfl⟩ : syracuseStep 2893589 = 135637) (by norm_num)
theorem B1929059 : Blo 1927435 1929059 := bstep (se 1 (by rfl) ⟨1446794, by rfl⟩ : syracuseStep 1929059 = 2893589) B2893589
theorem B9396437 : Blo 1927435 9396437 := bbase (se 7 (by rfl) ⟨110114, by rfl⟩ : syracuseStep 9396437 = 220229) (by norm_num)
theorem B100228661 : Blo 1927435 100228661 := bstep (se 5 (by rfl) ⟨4698218, by rfl⟩ : syracuseStep 100228661 = 9396437) B9396437
theorem B66819107 : Blo 1927435 66819107 := bstep (se 1 (by rfl) ⟨50114330, by rfl⟩ : syracuseStep 66819107 = 100228661) B100228661
theorem B44546071 : Blo 1927435 44546071 := bstep (se 1 (by rfl) ⟨33409553, by rfl⟩ : syracuseStep 44546071 = 66819107) B66819107
theorem B59394761 : Blo 1927435 59394761 := bstep (se 2 (by rfl) ⟨22273035, by rfl⟩ : syracuseStep 59394761 = 44546071) B44546071
theorem B39596507 : Blo 1927435 39596507 := bstep (se 1 (by rfl) ⟨29697380, by rfl⟩ : syracuseStep 39596507 = 59394761) B59394761
theorem B26397671 : Blo 1927435 26397671 := bstep (se 1 (by rfl) ⟨19798253, by rfl⟩ : syracuseStep 26397671 = 39596507) B39596507
theorem B70393789 : Blo 1927435 70393789 := bstep (se 3 (by rfl) ⟨13198835, by rfl⟩ : syracuseStep 70393789 = 26397671) B26397671
theorem B93858385 : Blo 1927435 93858385 := bstep (se 2 (by rfl) ⟨35196894, by rfl⟩ : syracuseStep 93858385 = 70393789) B70393789
theorem B125144513 : Blo 1927435 125144513 := bstep (se 2 (by rfl) ⟨46929192, by rfl⟩ : syracuseStep 125144513 = 93858385) B93858385
theorem B83429675 : Blo 1927435 83429675 := bstep (se 1 (by rfl) ⟨62572256, by rfl⟩ : syracuseStep 83429675 = 125144513) B125144513
theorem B55619783 : Blo 1927435 55619783 := bstep (se 1 (by rfl) ⟨41714837, by rfl⟩ : syracuseStep 55619783 = 83429675) B83429675
theorem B37079855 : Blo 1927435 37079855 := bstep (se 1 (by rfl) ⟨27809891, by rfl⟩ : syracuseStep 37079855 = 55619783) B55619783
theorem B24719903 : Blo 1927435 24719903 := bstep (se 1 (by rfl) ⟨18539927, by rfl⟩ : syracuseStep 24719903 = 37079855) B37079855
theorem B16479935 : Blo 1927435 16479935 := bstep (se 1 (by rfl) ⟨12359951, by rfl⟩ : syracuseStep 16479935 = 24719903) B24719903
theorem B10986623 : Blo 1927435 10986623 := bstep (se 1 (by rfl) ⟨8239967, by rfl⟩ : syracuseStep 10986623 = 16479935) B16479935
theorem B7324415 : Blo 1927435 7324415 := bstep (se 1 (by rfl) ⟨5493311, by rfl⟩ : syracuseStep 7324415 = 10986623) B10986623
theorem B4882943 : Blo 1927435 4882943 := bstep (se 1 (by rfl) ⟨3662207, by rfl⟩ : syracuseStep 4882943 = 7324415) B7324415
theorem B3255295 : Blo 1927435 3255295 := bstep (se 1 (by rfl) ⟨2441471, by rfl⟩ : syracuseStep 3255295 = 4882943) B4882943
theorem B4340393 : Blo 1927435 4340393 := bstep (se 2 (by rfl) ⟨1627647, by rfl⟩ : syracuseStep 4340393 = 3255295) B3255295
theorem B2893595 : Blo 1927435 2893595 := bstep (se 1 (by rfl) ⟨2170196, by rfl⟩ : syracuseStep 2893595 = 4340393) B4340393
theorem B1929063 : Blo 1927435 1929063 := bstep (se 1 (by rfl) ⟨1446797, by rfl⟩ : syracuseStep 1929063 = 2893595) B2893595
theorem B2170201 : Blo 1927435 2170201 := bbase (se 2 (by rfl) ⟨813825, by rfl⟩ : syracuseStep 2170201 = 1627651) (by norm_num)
theorem B2893601 : Blo 1927435 2893601 := bstep (se 2 (by rfl) ⟨1085100, by rfl⟩ : syracuseStep 2893601 = 2170201) B2170201
theorem B1929067 : Blo 1927435 1929067 := bstep (se 1 (by rfl) ⟨1446800, by rfl⟩ : syracuseStep 1929067 = 2893601) B2893601
theorem B2317501 : Blo 1927435 2317501 := bbase (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) (by norm_num)
theorem B3090001 : Blo 1927435 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B4120001 : Blo 1927435 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B2746667 : Blo 1927435 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B7324445 : Blo 1927435 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B4882963 : Blo 1927435 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B6510617 : Blo 1927435 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B4340411 : Blo 1927435 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B2893607 : Blo 1927435 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B1929071 : Blo 1927435 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B2893613 : Blo 1927435 2893613 := bbase (se 3 (by rfl) ⟨542552, by rfl⟩ : syracuseStep 2893613 = 1085105) (by norm_num)
theorem B1929075 : Blo 1927435 1929075 := bstep (se 1 (by rfl) ⟨1446806, by rfl⟩ : syracuseStep 1929075 = 2893613) B2893613
theorem B4340429 : Blo 1927435 4340429 := bbase (se 3 (by rfl) ⟨813830, by rfl⟩ : syracuseStep 4340429 = 1627661) (by norm_num)
theorem B2893619 : Blo 1927435 2893619 := bstep (se 1 (by rfl) ⟨2170214, by rfl⟩ : syracuseStep 2893619 = 4340429) B4340429
theorem B1929079 : Blo 1927435 1929079 := bstep (se 1 (by rfl) ⟨1446809, by rfl⟩ : syracuseStep 1929079 = 2893619) B2893619
theorem B2441497 : Blo 1927435 2441497 := bbase (se 2 (by rfl) ⟨915561, by rfl⟩ : syracuseStep 2441497 = 1831123) (by norm_num)
theorem B3255329 : Blo 1927435 3255329 := bstep (se 2 (by rfl) ⟨1220748, by rfl⟩ : syracuseStep 3255329 = 2441497) B2441497
theorem B2170219 : Blo 1927435 2170219 := bstep (se 1 (by rfl) ⟨1627664, by rfl⟩ : syracuseStep 2170219 = 3255329) B3255329
theorem B2893625 : Blo 1927435 2893625 := bstep (se 2 (by rfl) ⟨1085109, by rfl⟩ : syracuseStep 2893625 = 2170219) B2170219
theorem B1929083 : Blo 1927435 1929083 := bstep (se 1 (by rfl) ⟨1446812, by rfl⟩ : syracuseStep 1929083 = 2893625) B2893625
theorem B8240069 : Blo 1927435 8240069 := bbase (se 4 (by rfl) ⟨772506, by rfl⟩ : syracuseStep 8240069 = 1545013) (by norm_num)
theorem B21973517 : Blo 1927435 21973517 := bstep (se 3 (by rfl) ⟨4120034, by rfl⟩ : syracuseStep 21973517 = 8240069) B8240069
theorem B14649011 : Blo 1927435 14649011 := bstep (se 1 (by rfl) ⟨10986758, by rfl⟩ : syracuseStep 14649011 = 21973517) B21973517
theorem B9766007 : Blo 1927435 9766007 := bstep (se 1 (by rfl) ⟨7324505, by rfl⟩ : syracuseStep 9766007 = 14649011) B14649011
theorem B6510671 : Blo 1927435 6510671 := bstep (se 1 (by rfl) ⟨4883003, by rfl⟩ : syracuseStep 6510671 = 9766007) B9766007
theorem B4340447 : Blo 1927435 4340447 := bstep (se 1 (by rfl) ⟨3255335, by rfl⟩ : syracuseStep 4340447 = 6510671) B6510671
theorem B2893631 : Blo 1927435 2893631 := bstep (se 1 (by rfl) ⟨2170223, by rfl⟩ : syracuseStep 2893631 = 4340447) B4340447
theorem B1929087 : Blo 1927435 1929087 := bstep (se 1 (by rfl) ⟨1446815, by rfl⟩ : syracuseStep 1929087 = 2893631) B2893631
theorem B2893637 : Blo 1927435 2893637 := bbase (se 4 (by rfl) ⟨271278, by rfl⟩ : syracuseStep 2893637 = 542557) (by norm_num)
theorem B1929091 : Blo 1927435 1929091 := bstep (se 1 (by rfl) ⟨1446818, by rfl⟩ : syracuseStep 1929091 = 2893637) B2893637
theorem B3255349 : Blo 1927435 3255349 := bbase (se 5 (by rfl) ⟨152594, by rfl⟩ : syracuseStep 3255349 = 305189) (by norm_num)
theorem B4340465 : Blo 1927435 4340465 := bstep (se 2 (by rfl) ⟨1627674, by rfl⟩ : syracuseStep 4340465 = 3255349) B3255349
theorem B2893643 : Blo 1927435 2893643 := bstep (se 1 (by rfl) ⟨2170232, by rfl⟩ : syracuseStep 2893643 = 4340465) B4340465
theorem B1929095 : Blo 1927435 1929095 := bstep (se 1 (by rfl) ⟨1446821, by rfl⟩ : syracuseStep 1929095 = 2893643) B2893643
theorem B2170237 : Blo 1927435 2170237 := bbase (se 3 (by rfl) ⟨406919, by rfl⟩ : syracuseStep 2170237 = 813839) (by norm_num)
theorem B2893649 : Blo 1927435 2893649 := bstep (se 2 (by rfl) ⟨1085118, by rfl⟩ : syracuseStep 2893649 = 2170237) B2170237
theorem B1929099 : Blo 1927435 1929099 := bstep (se 1 (by rfl) ⟨1446824, by rfl⟩ : syracuseStep 1929099 = 2893649) B2893649
theorem B6510725 : Blo 1927435 6510725 := bbase (se 4 (by rfl) ⟨610380, by rfl⟩ : syracuseStep 6510725 = 1220761) (by norm_num)
theorem B4340483 : Blo 1927435 4340483 := bstep (se 1 (by rfl) ⟨3255362, by rfl⟩ : syracuseStep 4340483 = 6510725) B6510725
theorem B2893655 : Blo 1927435 2893655 := bstep (se 1 (by rfl) ⟨2170241, by rfl⟩ : syracuseStep 2893655 = 4340483) B4340483
theorem B1929103 : Blo 1927435 1929103 := bstep (se 1 (by rfl) ⟨1446827, by rfl⟩ : syracuseStep 1929103 = 2893655) B2893655
theorem B2893661 : Blo 1927435 2893661 := bbase (se 3 (by rfl) ⟨542561, by rfl⟩ : syracuseStep 2893661 = 1085123) (by norm_num)
theorem B1929107 : Blo 1927435 1929107 := bstep (se 1 (by rfl) ⟨1446830, by rfl⟩ : syracuseStep 1929107 = 2893661) B2893661
theorem B4340501 : Blo 1927435 4340501 := bbase (se 6 (by rfl) ⟨101730, by rfl⟩ : syracuseStep 4340501 = 203461) (by norm_num)
theorem B2893667 : Blo 1927435 2893667 := bstep (se 1 (by rfl) ⟨2170250, by rfl⟩ : syracuseStep 2893667 = 4340501) B4340501
theorem B1929111 : Blo 1927435 1929111 := bstep (se 1 (by rfl) ⟨1446833, by rfl⟩ : syracuseStep 1929111 = 2893667) B2893667
theorem B7324613 : Blo 1927435 7324613 := bbase (se 4 (by rfl) ⟨686682, by rfl⟩ : syracuseStep 7324613 = 1373365) (by norm_num)
theorem B4883075 : Blo 1927435 4883075 := bstep (se 1 (by rfl) ⟨3662306, by rfl⟩ : syracuseStep 4883075 = 7324613) B7324613
theorem B3255383 : Blo 1927435 3255383 := bstep (se 1 (by rfl) ⟨2441537, by rfl⟩ : syracuseStep 3255383 = 4883075) B4883075
theorem B2170255 : Blo 1927435 2170255 := bstep (se 1 (by rfl) ⟨1627691, by rfl⟩ : syracuseStep 2170255 = 3255383) B3255383
theorem B2893673 : Blo 1927435 2893673 := bstep (se 2 (by rfl) ⟨1085127, by rfl⟩ : syracuseStep 2893673 = 2170255) B2170255
theorem B1929115 : Blo 1927435 1929115 := bstep (se 1 (by rfl) ⟨1446836, by rfl⟩ : syracuseStep 1929115 = 2893673) B2893673
theorem B10429013 : Blo 1927435 10429013 := bbase (se 8 (by rfl) ⟨61107, by rfl⟩ : syracuseStep 10429013 = 122215) (by norm_num)
theorem B6952675 : Blo 1927435 6952675 := bstep (se 1 (by rfl) ⟨5214506, by rfl⟩ : syracuseStep 6952675 = 10429013) B10429013
theorem B9270233 : Blo 1927435 9270233 := bstep (se 2 (by rfl) ⟨3476337, by rfl⟩ : syracuseStep 9270233 = 6952675) B6952675
theorem B6180155 : Blo 1927435 6180155 := bstep (se 1 (by rfl) ⟨4635116, by rfl⟩ : syracuseStep 6180155 = 9270233) B9270233
theorem B4120103 : Blo 1927435 4120103 := bstep (se 1 (by rfl) ⟨3090077, by rfl⟩ : syracuseStep 4120103 = 6180155) B6180155
theorem B10986941 : Blo 1927435 10986941 := bstep (se 3 (by rfl) ⟨2060051, by rfl⟩ : syracuseStep 10986941 = 4120103) B4120103
theorem B7324627 : Blo 1927435 7324627 := bstep (se 1 (by rfl) ⟨5493470, by rfl⟩ : syracuseStep 7324627 = 10986941) B10986941
theorem B9766169 : Blo 1927435 9766169 := bstep (se 2 (by rfl) ⟨3662313, by rfl⟩ : syracuseStep 9766169 = 7324627) B7324627
theorem B6510779 : Blo 1927435 6510779 := bstep (se 1 (by rfl) ⟨4883084, by rfl⟩ : syracuseStep 6510779 = 9766169) B9766169
theorem B4340519 : Blo 1927435 4340519 := bstep (se 1 (by rfl) ⟨3255389, by rfl⟩ : syracuseStep 4340519 = 6510779) B6510779
theorem B2893679 : Blo 1927435 2893679 := bstep (se 1 (by rfl) ⟨2170259, by rfl⟩ : syracuseStep 2893679 = 4340519) B4340519
theorem B1929119 : Blo 1927435 1929119 := bstep (se 1 (by rfl) ⟨1446839, by rfl⟩ : syracuseStep 1929119 = 2893679) B2893679
theorem B2893685 : Blo 1927435 2893685 := bbase (se 5 (by rfl) ⟨135641, by rfl⟩ : syracuseStep 2893685 = 271283) (by norm_num)
theorem B1929123 : Blo 1927435 1929123 := bstep (se 1 (by rfl) ⟨1446842, by rfl⟩ : syracuseStep 1929123 = 2893685) B2893685
theorem B1955449 : Blo 1927435 1955449 := bbase (se 2 (by rfl) ⟨733293, by rfl⟩ : syracuseStep 1955449 = 1466587) (by norm_num)
theorem B2607265 : Blo 1927435 2607265 := bstep (se 2 (by rfl) ⟨977724, by rfl⟩ : syracuseStep 2607265 = 1955449) B1955449
theorem B3476353 : Blo 1927435 3476353 := bstep (se 2 (by rfl) ⟨1303632, by rfl⟩ : syracuseStep 3476353 = 2607265) B2607265
theorem B4635137 : Blo 1927435 4635137 := bstep (se 2 (by rfl) ⟨1738176, by rfl⟩ : syracuseStep 4635137 = 3476353) B3476353
theorem B3090091 : Blo 1927435 3090091 := bstep (se 1 (by rfl) ⟨2317568, by rfl⟩ : syracuseStep 3090091 = 4635137) B4635137
theorem B4120121 : Blo 1927435 4120121 := bstep (se 2 (by rfl) ⟨1545045, by rfl⟩ : syracuseStep 4120121 = 3090091) B3090091
theorem B2746747 : Blo 1927435 2746747 := bstep (se 1 (by rfl) ⟨2060060, by rfl⟩ : syracuseStep 2746747 = 4120121) B4120121
theorem B3662329 : Blo 1927435 3662329 := bstep (se 2 (by rfl) ⟨1373373, by rfl⟩ : syracuseStep 3662329 = 2746747) B2746747
theorem B4883105 : Blo 1927435 4883105 := bstep (se 2 (by rfl) ⟨1831164, by rfl⟩ : syracuseStep 4883105 = 3662329) B3662329
theorem B3255403 : Blo 1927435 3255403 := bstep (se 1 (by rfl) ⟨2441552, by rfl⟩ : syracuseStep 3255403 = 4883105) B4883105
theorem B4340537 : Blo 1927435 4340537 := bstep (se 2 (by rfl) ⟨1627701, by rfl⟩ : syracuseStep 4340537 = 3255403) B3255403
theorem B2893691 : Blo 1927435 2893691 := bstep (se 1 (by rfl) ⟨2170268, by rfl⟩ : syracuseStep 2893691 = 4340537) B4340537
theorem B1929127 : Blo 1927435 1929127 := bstep (se 1 (by rfl) ⟨1446845, by rfl⟩ : syracuseStep 1929127 = 2893691) B2893691
theorem B2170273 : Blo 1927435 2170273 := bbase (se 2 (by rfl) ⟨813852, by rfl⟩ : syracuseStep 2170273 = 1627705) (by norm_num)
theorem B2893697 : Blo 1927435 2893697 := bstep (se 2 (by rfl) ⟨1085136, by rfl⟩ : syracuseStep 2893697 = 2170273) B2170273
theorem B1929131 : Blo 1927435 1929131 := bstep (se 1 (by rfl) ⟨1446848, by rfl⟩ : syracuseStep 1929131 = 2893697) B2893697
theorem B4883125 : Blo 1927435 4883125 := bbase (se 5 (by rfl) ⟨228896, by rfl⟩ : syracuseStep 4883125 = 457793) (by norm_num)
theorem B6510833 : Blo 1927435 6510833 := bstep (se 2 (by rfl) ⟨2441562, by rfl⟩ : syracuseStep 6510833 = 4883125) B4883125
theorem B4340555 : Blo 1927435 4340555 := bstep (se 1 (by rfl) ⟨3255416, by rfl⟩ : syracuseStep 4340555 = 6510833) B6510833
theorem B2893703 : Blo 1927435 2893703 := bstep (se 1 (by rfl) ⟨2170277, by rfl⟩ : syracuseStep 2893703 = 4340555) B4340555
theorem B1929135 : Blo 1927435 1929135 := bstep (se 1 (by rfl) ⟨1446851, by rfl⟩ : syracuseStep 1929135 = 2893703) B2893703
theorem B2893709 : Blo 1927435 2893709 := bbase (se 3 (by rfl) ⟨542570, by rfl⟩ : syracuseStep 2893709 = 1085141) (by norm_num)
theorem B1929139 : Blo 1927435 1929139 := bstep (se 1 (by rfl) ⟨1446854, by rfl⟩ : syracuseStep 1929139 = 2893709) B2893709
theorem B4340573 : Blo 1927435 4340573 := bbase (se 3 (by rfl) ⟨813857, by rfl⟩ : syracuseStep 4340573 = 1627715) (by norm_num)
theorem B2893715 : Blo 1927435 2893715 := bstep (se 1 (by rfl) ⟨2170286, by rfl⟩ : syracuseStep 2893715 = 4340573) B4340573
theorem B1929143 : Blo 1927435 1929143 := bstep (se 1 (by rfl) ⟨1446857, by rfl⟩ : syracuseStep 1929143 = 2893715) B2893715
theorem B3255437 : Blo 1927435 3255437 := bbase (se 3 (by rfl) ⟨610394, by rfl⟩ : syracuseStep 3255437 = 1220789) (by norm_num)
theorem B2170291 : Blo 1927435 2170291 := bstep (se 1 (by rfl) ⟨1627718, by rfl⟩ : syracuseStep 2170291 = 3255437) B3255437
theorem B2893721 : Blo 1927435 2893721 := bstep (se 2 (by rfl) ⟨1085145, by rfl⟩ : syracuseStep 2893721 = 2170291) B2170291
theorem B1929147 : Blo 1927435 1929147 := bstep (se 1 (by rfl) ⟨1446860, by rfl⟩ : syracuseStep 1929147 = 2893721) B2893721
theorem B3299861 : Blo 1927435 3299861 := bbase (se 6 (by rfl) ⟨77340, by rfl⟩ : syracuseStep 3299861 = 154681) (by norm_num)
theorem B2199907 : Blo 1927435 2199907 := bstep (se 1 (by rfl) ⟨1649930, by rfl⟩ : syracuseStep 2199907 = 3299861) B3299861
theorem B2933209 : Blo 1927435 2933209 := bstep (se 2 (by rfl) ⟨1099953, by rfl⟩ : syracuseStep 2933209 = 2199907) B2199907
theorem B3910945 : Blo 1927435 3910945 := bstep (se 2 (by rfl) ⟨1466604, by rfl⟩ : syracuseStep 3910945 = 2933209) B2933209
theorem B5214593 : Blo 1927435 5214593 := bstep (se 2 (by rfl) ⟨1955472, by rfl⟩ : syracuseStep 5214593 = 3910945) B3910945
theorem B3476395 : Blo 1927435 3476395 := bstep (se 1 (by rfl) ⟨2607296, by rfl⟩ : syracuseStep 3476395 = 5214593) B5214593
theorem B4635193 : Blo 1927435 4635193 := bstep (se 2 (by rfl) ⟨1738197, by rfl⟩ : syracuseStep 4635193 = 3476395) B3476395
theorem B6180257 : Blo 1927435 6180257 := bstep (se 2 (by rfl) ⟨2317596, by rfl⟩ : syracuseStep 6180257 = 4635193) B4635193
theorem B16480685 : Blo 1927435 16480685 := bstep (se 3 (by rfl) ⟨3090128, by rfl⟩ : syracuseStep 16480685 = 6180257) B6180257
theorem B10987123 : Blo 1927435 10987123 := bstep (se 1 (by rfl) ⟨8240342, by rfl⟩ : syracuseStep 10987123 = 16480685) B16480685
theorem B14649497 : Blo 1927435 14649497 := bstep (se 2 (by rfl) ⟨5493561, by rfl⟩ : syracuseStep 14649497 = 10987123) B10987123
theorem B9766331 : Blo 1927435 9766331 := bstep (se 1 (by rfl) ⟨7324748, by rfl⟩ : syracuseStep 9766331 = 14649497) B14649497
theorem B6510887 : Blo 1927435 6510887 := bstep (se 1 (by rfl) ⟨4883165, by rfl⟩ : syracuseStep 6510887 = 9766331) B9766331
theorem B4340591 : Blo 1927435 4340591 := bstep (se 1 (by rfl) ⟨3255443, by rfl⟩ : syracuseStep 4340591 = 6510887) B6510887
theorem B2893727 : Blo 1927435 2893727 := bstep (se 1 (by rfl) ⟨2170295, by rfl⟩ : syracuseStep 2893727 = 4340591) B4340591
theorem B1929151 : Blo 1927435 1929151 := bstep (se 1 (by rfl) ⟨1446863, by rfl⟩ : syracuseStep 1929151 = 2893727) B2893727
theorem B2893733 : Blo 1927435 2893733 := bbase (se 4 (by rfl) ⟨271287, by rfl⟩ : syracuseStep 2893733 = 542575) (by norm_num)
theorem B1929155 : Blo 1927435 1929155 := bstep (se 1 (by rfl) ⟨1446866, by rfl⟩ : syracuseStep 1929155 = 2893733) B2893733
theorem B2441593 : Blo 1927435 2441593 := bbase (se 2 (by rfl) ⟨915597, by rfl⟩ : syracuseStep 2441593 = 1831195) (by norm_num)
theorem B3255457 : Blo 1927435 3255457 := bstep (se 2 (by rfl) ⟨1220796, by rfl⟩ : syracuseStep 3255457 = 2441593) B2441593
theorem B4340609 : Blo 1927435 4340609 := bstep (se 2 (by rfl) ⟨1627728, by rfl⟩ : syracuseStep 4340609 = 3255457) B3255457
theorem B2893739 : Blo 1927435 2893739 := bstep (se 1 (by rfl) ⟨2170304, by rfl⟩ : syracuseStep 2893739 = 4340609) B4340609
theorem B1929159 : Blo 1927435 1929159 := bstep (se 1 (by rfl) ⟨1446869, by rfl⟩ : syracuseStep 1929159 = 2893739) B2893739
theorem B2170309 : Blo 1927435 2170309 := bbase (se 4 (by rfl) ⟨203466, by rfl⟩ : syracuseStep 2170309 = 406933) (by norm_num)
theorem B2893745 : Blo 1927435 2893745 := bstep (se 2 (by rfl) ⟨1085154, by rfl⟩ : syracuseStep 2893745 = 2170309) B2170309
theorem B1929163 : Blo 1927435 1929163 := bstep (se 1 (by rfl) ⟨1446872, by rfl⟩ : syracuseStep 1929163 = 2893745) B2893745
theorem B3662405 : Blo 1927435 3662405 := bbase (se 4 (by rfl) ⟨343350, by rfl⟩ : syracuseStep 3662405 = 686701) (by norm_num)
theorem B2441603 : Blo 1927435 2441603 := bstep (se 1 (by rfl) ⟨1831202, by rfl⟩ : syracuseStep 2441603 = 3662405) B3662405
theorem B6510941 : Blo 1927435 6510941 := bstep (se 3 (by rfl) ⟨1220801, by rfl⟩ : syracuseStep 6510941 = 2441603) B2441603
theorem B4340627 : Blo 1927435 4340627 := bstep (se 1 (by rfl) ⟨3255470, by rfl⟩ : syracuseStep 4340627 = 6510941) B6510941
theorem B2893751 : Blo 1927435 2893751 := bstep (se 1 (by rfl) ⟨2170313, by rfl⟩ : syracuseStep 2893751 = 4340627) B4340627
theorem B1929167 : Blo 1927435 1929167 := bstep (se 1 (by rfl) ⟨1446875, by rfl⟩ : syracuseStep 1929167 = 2893751) B2893751
theorem B2893757 : Blo 1927435 2893757 := bbase (se 3 (by rfl) ⟨542579, by rfl⟩ : syracuseStep 2893757 = 1085159) (by norm_num)
theorem B1929171 : Blo 1927435 1929171 := bstep (se 1 (by rfl) ⟨1446878, by rfl⟩ : syracuseStep 1929171 = 2893757) B2893757
theorem B4340645 : Blo 1927435 4340645 := bbase (se 4 (by rfl) ⟨406935, by rfl⟩ : syracuseStep 4340645 = 813871) (by norm_num)
theorem B2893763 : Blo 1927435 2893763 := bstep (se 1 (by rfl) ⟨2170322, by rfl⟩ : syracuseStep 2893763 = 4340645) B4340645
theorem B1929175 : Blo 1927435 1929175 := bstep (se 1 (by rfl) ⟨1446881, by rfl⟩ : syracuseStep 1929175 = 2893763) B2893763
theorem B4883237 : Blo 1927435 4883237 := bbase (se 4 (by rfl) ⟨457803, by rfl⟩ : syracuseStep 4883237 = 915607) (by norm_num)
theorem B3255491 : Blo 1927435 3255491 := bstep (se 1 (by rfl) ⟨2441618, by rfl⟩ : syracuseStep 3255491 = 4883237) B4883237
theorem B2170327 : Blo 1927435 2170327 := bstep (se 1 (by rfl) ⟨1627745, by rfl⟩ : syracuseStep 2170327 = 3255491) B3255491
theorem B2893769 : Blo 1927435 2893769 := bstep (se 2 (by rfl) ⟨1085163, by rfl⟩ : syracuseStep 2893769 = 2170327) B2170327
theorem B1929179 : Blo 1927435 1929179 := bstep (se 1 (by rfl) ⟨1446884, by rfl⟩ : syracuseStep 1929179 = 2893769) B2893769
theorem B5493653 : Blo 1927435 5493653 := bbase (se 6 (by rfl) ⟨128757, by rfl⟩ : syracuseStep 5493653 = 257515) (by norm_num)
theorem B3662435 : Blo 1927435 3662435 := bstep (se 1 (by rfl) ⟨2746826, by rfl⟩ : syracuseStep 3662435 = 5493653) B5493653
theorem B9766493 : Blo 1927435 9766493 := bstep (se 3 (by rfl) ⟨1831217, by rfl⟩ : syracuseStep 9766493 = 3662435) B3662435
theorem B6510995 : Blo 1927435 6510995 := bstep (se 1 (by rfl) ⟨4883246, by rfl⟩ : syracuseStep 6510995 = 9766493) B9766493
theorem B4340663 : Blo 1927435 4340663 := bstep (se 1 (by rfl) ⟨3255497, by rfl⟩ : syracuseStep 4340663 = 6510995) B6510995
theorem B2893775 : Blo 1927435 2893775 := bstep (se 1 (by rfl) ⟨2170331, by rfl⟩ : syracuseStep 2893775 = 4340663) B4340663
theorem B1929183 : Blo 1927435 1929183 := bstep (se 1 (by rfl) ⟨1446887, by rfl⟩ : syracuseStep 1929183 = 2893775) B2893775
theorem B2893781 : Blo 1927435 2893781 := bbase (se 7 (by rfl) ⟨33911, by rfl⟩ : syracuseStep 2893781 = 67823) (by norm_num)
theorem B1929187 : Blo 1927435 1929187 := bstep (se 1 (by rfl) ⟨1446890, by rfl⟩ : syracuseStep 1929187 = 2893781) B2893781
theorem B7324901 : Blo 1927435 7324901 := bbase (se 4 (by rfl) ⟨686709, by rfl⟩ : syracuseStep 7324901 = 1373419) (by norm_num)
theorem B4883267 : Blo 1927435 4883267 := bstep (se 1 (by rfl) ⟨3662450, by rfl⟩ : syracuseStep 4883267 = 7324901) B7324901
theorem B3255511 : Blo 1927435 3255511 := bstep (se 1 (by rfl) ⟨2441633, by rfl⟩ : syracuseStep 3255511 = 4883267) B4883267
theorem B4340681 : Blo 1927435 4340681 := bstep (se 2 (by rfl) ⟨1627755, by rfl⟩ : syracuseStep 4340681 = 3255511) B3255511
theorem B2893787 : Blo 1927435 2893787 := bstep (se 1 (by rfl) ⟨2170340, by rfl⟩ : syracuseStep 2893787 = 4340681) B4340681
theorem B1929191 : Blo 1927435 1929191 := bstep (se 1 (by rfl) ⟨1446893, by rfl⟩ : syracuseStep 1929191 = 2893787) B2893787
theorem B2170345 : Blo 1927435 2170345 := bbase (se 2 (by rfl) ⟨813879, by rfl⟩ : syracuseStep 2170345 = 1627759) (by norm_num)
theorem B2893793 : Blo 1927435 2893793 := bstep (se 2 (by rfl) ⟨1085172, by rfl⟩ : syracuseStep 2893793 = 2170345) B2170345
theorem B1929195 : Blo 1927435 1929195 := bstep (se 1 (by rfl) ⟨1446896, by rfl⟩ : syracuseStep 1929195 = 2893793) B2893793
theorem B2060137 : Blo 1927435 2060137 := bbase (se 2 (by rfl) ⟨772551, by rfl⟩ : syracuseStep 2060137 = 1545103) (by norm_num)
theorem B10987397 : Blo 1927435 10987397 := bstep (se 4 (by rfl) ⟨1030068, by rfl⟩ : syracuseStep 10987397 = 2060137) B2060137
theorem B7324931 : Blo 1927435 7324931 := bstep (se 1 (by rfl) ⟨5493698, by rfl⟩ : syracuseStep 7324931 = 10987397) B10987397
theorem B4883287 : Blo 1927435 4883287 := bstep (se 1 (by rfl) ⟨3662465, by rfl⟩ : syracuseStep 4883287 = 7324931) B7324931
theorem B6511049 : Blo 1927435 6511049 := bstep (se 2 (by rfl) ⟨2441643, by rfl⟩ : syracuseStep 6511049 = 4883287) B4883287
theorem B4340699 : Blo 1927435 4340699 := bstep (se 1 (by rfl) ⟨3255524, by rfl⟩ : syracuseStep 4340699 = 6511049) B6511049
theorem B2893799 : Blo 1927435 2893799 := bstep (se 1 (by rfl) ⟨2170349, by rfl⟩ : syracuseStep 2893799 = 4340699) B4340699
theorem B1929199 : Blo 1927435 1929199 := bstep (se 1 (by rfl) ⟨1446899, by rfl⟩ : syracuseStep 1929199 = 2893799) B2893799
theorem B2893805 : Blo 1927435 2893805 := bbase (se 3 (by rfl) ⟨542588, by rfl⟩ : syracuseStep 2893805 = 1085177) (by norm_num)
theorem B1929203 : Blo 1927435 1929203 := bstep (se 1 (by rfl) ⟨1446902, by rfl⟩ : syracuseStep 1929203 = 2893805) B2893805
theorem B4340717 : Blo 1927435 4340717 := bbase (se 3 (by rfl) ⟨813884, by rfl⟩ : syracuseStep 4340717 = 1627769) (by norm_num)
theorem B2893811 : Blo 1927435 2893811 := bstep (se 1 (by rfl) ⟨2170358, by rfl⟩ : syracuseStep 2893811 = 4340717) B4340717
theorem B1929207 : Blo 1927435 1929207 := bstep (se 1 (by rfl) ⟨1446905, by rfl⟩ : syracuseStep 1929207 = 2893811) B2893811
theorem B4120301 : Blo 1927435 4120301 := bbase (se 3 (by rfl) ⟨772556, by rfl⟩ : syracuseStep 4120301 = 1545113) (by norm_num)
theorem B2746867 : Blo 1927435 2746867 := bstep (se 1 (by rfl) ⟨2060150, by rfl⟩ : syracuseStep 2746867 = 4120301) B4120301
theorem B3662489 : Blo 1927435 3662489 := bstep (se 2 (by rfl) ⟨1373433, by rfl⟩ : syracuseStep 3662489 = 2746867) B2746867
theorem B2441659 : Blo 1927435 2441659 := bstep (se 1 (by rfl) ⟨1831244, by rfl⟩ : syracuseStep 2441659 = 3662489) B3662489
theorem B3255545 : Blo 1927435 3255545 := bstep (se 2 (by rfl) ⟨1220829, by rfl⟩ : syracuseStep 3255545 = 2441659) B2441659
theorem B2170363 : Blo 1927435 2170363 := bstep (se 1 (by rfl) ⟨1627772, by rfl⟩ : syracuseStep 2170363 = 3255545) B3255545
theorem B2893817 : Blo 1927435 2893817 := bstep (se 2 (by rfl) ⟨1085181, by rfl⟩ : syracuseStep 2893817 = 2170363) B2170363
theorem B1929211 : Blo 1927435 1929211 := bstep (se 1 (by rfl) ⟨1446908, by rfl⟩ : syracuseStep 1929211 = 2893817) B2893817
theorem B4698589 : Blo 1927435 4698589 := bbase (se 3 (by rfl) ⟨880985, by rfl⟩ : syracuseStep 4698589 = 1761971) (by norm_num)
theorem B6264785 : Blo 1927435 6264785 := bstep (se 2 (by rfl) ⟨2349294, by rfl⟩ : syracuseStep 6264785 = 4698589) B4698589
theorem B4176523 : Blo 1927435 4176523 := bstep (se 1 (by rfl) ⟨3132392, by rfl⟩ : syracuseStep 4176523 = 6264785) B6264785
theorem B5568697 : Blo 1927435 5568697 := bstep (se 2 (by rfl) ⟨2088261, by rfl⟩ : syracuseStep 5568697 = 4176523) B4176523
theorem B7424929 : Blo 1927435 7424929 := bstep (se 2 (by rfl) ⟨2784348, by rfl⟩ : syracuseStep 7424929 = 5568697) B5568697
theorem B39599621 : Blo 1927435 39599621 := bstep (se 4 (by rfl) ⟨3712464, by rfl⟩ : syracuseStep 39599621 = 7424929) B7424929
theorem B26399747 : Blo 1927435 26399747 := bstep (se 1 (by rfl) ⟨19799810, by rfl⟩ : syracuseStep 26399747 = 39599621) B39599621
theorem B70399325 : Blo 1927435 70399325 := bstep (se 3 (by rfl) ⟨13199873, by rfl⟩ : syracuseStep 70399325 = 26399747) B26399747
theorem B187731533 : Blo 1927435 187731533 := bstep (se 3 (by rfl) ⟨35199662, by rfl⟩ : syracuseStep 187731533 = 70399325) B70399325
theorem B125154355 : Blo 1927435 125154355 := bstep (se 1 (by rfl) ⟨93865766, by rfl⟩ : syracuseStep 125154355 = 187731533) B187731533
theorem B166872473 : Blo 1927435 166872473 := bstep (se 2 (by rfl) ⟨62577177, by rfl⟩ : syracuseStep 166872473 = 125154355) B125154355
theorem B111248315 : Blo 1927435 111248315 := bstep (se 1 (by rfl) ⟨83436236, by rfl⟩ : syracuseStep 111248315 = 166872473) B166872473
theorem B74165543 : Blo 1927435 74165543 := bstep (se 1 (by rfl) ⟨55624157, by rfl⟩ : syracuseStep 74165543 = 111248315) B111248315
theorem B49443695 : Blo 1927435 49443695 := bstep (se 1 (by rfl) ⟨37082771, by rfl⟩ : syracuseStep 49443695 = 74165543) B74165543
theorem B32962463 : Blo 1927435 32962463 := bstep (se 1 (by rfl) ⟨24721847, by rfl⟩ : syracuseStep 32962463 = 49443695) B49443695
theorem B21974975 : Blo 1927435 21974975 := bstep (se 1 (by rfl) ⟨16481231, by rfl⟩ : syracuseStep 21974975 = 32962463) B32962463
theorem B14649983 : Blo 1927435 14649983 := bstep (se 1 (by rfl) ⟨10987487, by rfl⟩ : syracuseStep 14649983 = 21974975) B21974975
theorem B9766655 : Blo 1927435 9766655 := bstep (se 1 (by rfl) ⟨7324991, by rfl⟩ : syracuseStep 9766655 = 14649983) B14649983
theorem B6511103 : Blo 1927435 6511103 := bstep (se 1 (by rfl) ⟨4883327, by rfl⟩ : syracuseStep 6511103 = 9766655) B9766655
theorem B4340735 : Blo 1927435 4340735 := bstep (se 1 (by rfl) ⟨3255551, by rfl⟩ : syracuseStep 4340735 = 6511103) B6511103
theorem B2893823 : Blo 1927435 2893823 := bstep (se 1 (by rfl) ⟨2170367, by rfl⟩ : syracuseStep 2893823 = 4340735) B4340735
theorem B1929215 : Blo 1927435 1929215 := bstep (se 1 (by rfl) ⟨1446911, by rfl⟩ : syracuseStep 1929215 = 2893823) B2893823
theorem B2893829 : Blo 1927435 2893829 := bbase (se 4 (by rfl) ⟨271296, by rfl⟩ : syracuseStep 2893829 = 542593) (by norm_num)
theorem B1929219 : Blo 1927435 1929219 := bstep (se 1 (by rfl) ⟨1446914, by rfl⟩ : syracuseStep 1929219 = 2893829) B2893829
theorem B3255565 : Blo 1927435 3255565 := bbase (se 3 (by rfl) ⟨610418, by rfl⟩ : syracuseStep 3255565 = 1220837) (by norm_num)
theorem B4340753 : Blo 1927435 4340753 := bstep (se 2 (by rfl) ⟨1627782, by rfl⟩ : syracuseStep 4340753 = 3255565) B3255565
theorem B2893835 : Blo 1927435 2893835 := bstep (se 1 (by rfl) ⟨2170376, by rfl⟩ : syracuseStep 2893835 = 4340753) B4340753
theorem B1929223 : Blo 1927435 1929223 := bstep (se 1 (by rfl) ⟨1446917, by rfl⟩ : syracuseStep 1929223 = 2893835) B2893835
theorem B2170381 : Blo 1927435 2170381 := bbase (se 3 (by rfl) ⟨406946, by rfl⟩ : syracuseStep 2170381 = 813893) (by norm_num)
theorem B2893841 : Blo 1927435 2893841 := bstep (se 2 (by rfl) ⟨1085190, by rfl⟩ : syracuseStep 2893841 = 2170381) B2170381
theorem B1929227 : Blo 1927435 1929227 := bstep (se 1 (by rfl) ⟨1446920, by rfl⟩ : syracuseStep 1929227 = 2893841) B2893841
theorem B6511157 : Blo 1927435 6511157 := bbase (se 5 (by rfl) ⟨305210, by rfl⟩ : syracuseStep 6511157 = 610421) (by norm_num)
theorem B4340771 : Blo 1927435 4340771 := bstep (se 1 (by rfl) ⟨3255578, by rfl⟩ : syracuseStep 4340771 = 6511157) B6511157
theorem B2893847 : Blo 1927435 2893847 := bstep (se 1 (by rfl) ⟨2170385, by rfl⟩ : syracuseStep 2893847 = 4340771) B4340771
theorem B1929231 : Blo 1927435 1929231 := bstep (se 1 (by rfl) ⟨1446923, by rfl⟩ : syracuseStep 1929231 = 2893847) B2893847
theorem B2893853 : Blo 1927435 2893853 := bbase (se 3 (by rfl) ⟨542597, by rfl⟩ : syracuseStep 2893853 = 1085195) (by norm_num)
theorem B1929235 : Blo 1927435 1929235 := bstep (se 1 (by rfl) ⟨1446926, by rfl⟩ : syracuseStep 1929235 = 2893853) B2893853
theorem B4340789 : Blo 1927435 4340789 := bbase (se 5 (by rfl) ⟨203474, by rfl⟩ : syracuseStep 4340789 = 406949) (by norm_num)
theorem B2893859 : Blo 1927435 2893859 := bstep (se 1 (by rfl) ⟨2170394, by rfl⟩ : syracuseStep 2893859 = 4340789) B4340789
theorem B1929239 : Blo 1927435 1929239 := bstep (se 1 (by rfl) ⟨1446929, by rfl⟩ : syracuseStep 1929239 = 2893859) B2893859
theorem B10429685 : Blo 1927435 10429685 := bbase (se 5 (by rfl) ⟨488891, by rfl⟩ : syracuseStep 10429685 = 977783) (by norm_num)
theorem B6953123 : Blo 1927435 6953123 := bstep (se 1 (by rfl) ⟨5214842, by rfl⟩ : syracuseStep 6953123 = 10429685) B10429685
theorem B4635415 : Blo 1927435 4635415 := bstep (se 1 (by rfl) ⟨3476561, by rfl⟩ : syracuseStep 4635415 = 6953123) B6953123
theorem B6180553 : Blo 1927435 6180553 := bstep (se 2 (by rfl) ⟨2317707, by rfl⟩ : syracuseStep 6180553 = 4635415) B4635415
theorem B8240737 : Blo 1927435 8240737 := bstep (se 2 (by rfl) ⟨3090276, by rfl⟩ : syracuseStep 8240737 = 6180553) B6180553
theorem B10987649 : Blo 1927435 10987649 := bstep (se 2 (by rfl) ⟨4120368, by rfl⟩ : syracuseStep 10987649 = 8240737) B8240737
theorem B7325099 : Blo 1927435 7325099 := bstep (se 1 (by rfl) ⟨5493824, by rfl⟩ : syracuseStep 7325099 = 10987649) B10987649
theorem B4883399 : Blo 1927435 4883399 := bstep (se 1 (by rfl) ⟨3662549, by rfl⟩ : syracuseStep 4883399 = 7325099) B7325099
theorem B3255599 : Blo 1927435 3255599 := bstep (se 1 (by rfl) ⟨2441699, by rfl⟩ : syracuseStep 3255599 = 4883399) B4883399
theorem B2170399 : Blo 1927435 2170399 := bstep (se 1 (by rfl) ⟨1627799, by rfl⟩ : syracuseStep 2170399 = 3255599) B3255599
theorem B2893865 : Blo 1927435 2893865 := bstep (se 2 (by rfl) ⟨1085199, by rfl⟩ : syracuseStep 2893865 = 2170399) B2170399
theorem B1929243 : Blo 1927435 1929243 := bstep (se 1 (by rfl) ⟨1446932, by rfl⟩ : syracuseStep 1929243 = 2893865) B2893865
theorem B6180565 : Blo 1927435 6180565 := bbase (se 7 (by rfl) ⟨72428, by rfl⟩ : syracuseStep 6180565 = 144857) (by norm_num)
theorem B8240753 : Blo 1927435 8240753 := bstep (se 2 (by rfl) ⟨3090282, by rfl⟩ : syracuseStep 8240753 = 6180565) B6180565
theorem B5493835 : Blo 1927435 5493835 := bstep (se 1 (by rfl) ⟨4120376, by rfl⟩ : syracuseStep 5493835 = 8240753) B8240753
theorem B7325113 : Blo 1927435 7325113 := bstep (se 2 (by rfl) ⟨2746917, by rfl⟩ : syracuseStep 7325113 = 5493835) B5493835
theorem B9766817 : Blo 1927435 9766817 := bstep (se 2 (by rfl) ⟨3662556, by rfl⟩ : syracuseStep 9766817 = 7325113) B7325113
theorem B6511211 : Blo 1927435 6511211 := bstep (se 1 (by rfl) ⟨4883408, by rfl⟩ : syracuseStep 6511211 = 9766817) B9766817
theorem B4340807 : Blo 1927435 4340807 := bstep (se 1 (by rfl) ⟨3255605, by rfl⟩ : syracuseStep 4340807 = 6511211) B6511211
theorem B2893871 : Blo 1927435 2893871 := bstep (se 1 (by rfl) ⟨2170403, by rfl⟩ : syracuseStep 2893871 = 4340807) B4340807
theorem B1929247 : Blo 1927435 1929247 := bstep (se 1 (by rfl) ⟨1446935, by rfl⟩ : syracuseStep 1929247 = 2893871) B2893871
theorem B2893877 : Blo 1927435 2893877 := bbase (se 5 (by rfl) ⟨135650, by rfl⟩ : syracuseStep 2893877 = 271301) (by norm_num)
theorem B1929251 : Blo 1927435 1929251 := bstep (se 1 (by rfl) ⟨1446938, by rfl⟩ : syracuseStep 1929251 = 2893877) B2893877
theorem B4883429 : Blo 1927435 4883429 := bbase (se 4 (by rfl) ⟨457821, by rfl⟩ : syracuseStep 4883429 = 915643) (by norm_num)
theorem B3255619 : Blo 1927435 3255619 := bstep (se 1 (by rfl) ⟨2441714, by rfl⟩ : syracuseStep 3255619 = 4883429) B4883429
theorem B4340825 : Blo 1927435 4340825 := bstep (se 2 (by rfl) ⟨1627809, by rfl⟩ : syracuseStep 4340825 = 3255619) B3255619
theorem B2893883 : Blo 1927435 2893883 := bstep (se 1 (by rfl) ⟨2170412, by rfl⟩ : syracuseStep 2893883 = 4340825) B4340825
theorem B1929255 : Blo 1927435 1929255 := bstep (se 1 (by rfl) ⟨1446941, by rfl⟩ : syracuseStep 1929255 = 2893883) B2893883
theorem B2170417 : Blo 1927435 2170417 := bbase (se 2 (by rfl) ⟨813906, by rfl⟩ : syracuseStep 2170417 = 1627813) (by norm_num)
theorem B2893889 : Blo 1927435 2893889 := bstep (se 2 (by rfl) ⟨1085208, by rfl⟩ : syracuseStep 2893889 = 2170417) B2170417
theorem B1929259 : Blo 1927435 1929259 := bstep (se 1 (by rfl) ⟨1446944, by rfl⟩ : syracuseStep 1929259 = 2893889) B2893889
theorem B4582637 : Blo 1927435 4582637 := bbase (se 3 (by rfl) ⟨859244, by rfl⟩ : syracuseStep 4582637 = 1718489) (by norm_num)
theorem B3055091 : Blo 1927435 3055091 := bstep (se 1 (by rfl) ⟨2291318, by rfl⟩ : syracuseStep 3055091 = 4582637) B4582637
theorem B8146909 : Blo 1927435 8146909 := bstep (se 3 (by rfl) ⟨1527545, by rfl⟩ : syracuseStep 8146909 = 3055091) B3055091
theorem B10862545 : Blo 1927435 10862545 := bstep (se 2 (by rfl) ⟨4073454, by rfl⟩ : syracuseStep 10862545 = 8146909) B8146909
theorem B14483393 : Blo 1927435 14483393 := bstep (se 2 (by rfl) ⟨5431272, by rfl⟩ : syracuseStep 14483393 = 10862545) B10862545
theorem B9655595 : Blo 1927435 9655595 := bstep (se 1 (by rfl) ⟨7241696, by rfl⟩ : syracuseStep 9655595 = 14483393) B14483393
theorem B6437063 : Blo 1927435 6437063 := bstep (se 1 (by rfl) ⟨4827797, by rfl⟩ : syracuseStep 6437063 = 9655595) B9655595
theorem B4291375 : Blo 1927435 4291375 := bstep (se 1 (by rfl) ⟨3218531, by rfl⟩ : syracuseStep 4291375 = 6437063) B6437063
theorem B5721833 : Blo 1927435 5721833 := bstep (se 2 (by rfl) ⟨2145687, by rfl⟩ : syracuseStep 5721833 = 4291375) B4291375
theorem B3814555 : Blo 1927435 3814555 := bstep (se 1 (by rfl) ⟨2860916, by rfl⟩ : syracuseStep 3814555 = 5721833) B5721833
theorem B5086073 : Blo 1927435 5086073 := bstep (se 2 (by rfl) ⟨1907277, by rfl⟩ : syracuseStep 5086073 = 3814555) B3814555
theorem B13562861 : Blo 1927435 13562861 := bstep (se 3 (by rfl) ⟨2543036, by rfl⟩ : syracuseStep 13562861 = 5086073) B5086073
theorem B36167629 : Blo 1927435 36167629 := bstep (se 3 (by rfl) ⟨6781430, by rfl⟩ : syracuseStep 36167629 = 13562861) B13562861
theorem B48223505 : Blo 1927435 48223505 := bstep (se 2 (by rfl) ⟨18083814, by rfl⟩ : syracuseStep 48223505 = 36167629) B36167629
theorem B32149003 : Blo 1927435 32149003 := bstep (se 1 (by rfl) ⟨24111752, by rfl⟩ : syracuseStep 32149003 = 48223505) B48223505
theorem B42865337 : Blo 1927435 42865337 := bstep (se 2 (by rfl) ⟨16074501, by rfl⟩ : syracuseStep 42865337 = 32149003) B32149003
theorem B28576891 : Blo 1927435 28576891 := bstep (se 1 (by rfl) ⟨21432668, by rfl⟩ : syracuseStep 28576891 = 42865337) B42865337
theorem B152410085 : Blo 1927435 152410085 := bstep (se 4 (by rfl) ⟨14288445, by rfl⟩ : syracuseStep 152410085 = 28576891) B28576891
theorem B101606723 : Blo 1927435 101606723 := bstep (se 1 (by rfl) ⟨76205042, by rfl⟩ : syracuseStep 101606723 = 152410085) B152410085
theorem B67737815 : Blo 1927435 67737815 := bstep (se 1 (by rfl) ⟨50803361, by rfl⟩ : syracuseStep 67737815 = 101606723) B101606723
theorem B45158543 : Blo 1927435 45158543 := bstep (se 1 (by rfl) ⟨33868907, by rfl⟩ : syracuseStep 45158543 = 67737815) B67737815
theorem B30105695 : Blo 1927435 30105695 := bstep (se 1 (by rfl) ⟨22579271, by rfl⟩ : syracuseStep 30105695 = 45158543) B45158543
theorem B80281853 : Blo 1927435 80281853 := bstep (se 3 (by rfl) ⟨15052847, by rfl⟩ : syracuseStep 80281853 = 30105695) B30105695
theorem B53521235 : Blo 1927435 53521235 := bstep (se 1 (by rfl) ⟨40140926, by rfl⟩ : syracuseStep 53521235 = 80281853) B80281853
theorem B35680823 : Blo 1927435 35680823 := bstep (se 1 (by rfl) ⟨26760617, by rfl⟩ : syracuseStep 35680823 = 53521235) B53521235
theorem B23787215 : Blo 1927435 23787215 := bstep (se 1 (by rfl) ⟨17840411, by rfl⟩ : syracuseStep 23787215 = 35680823) B35680823
theorem B15858143 : Blo 1927435 15858143 := bstep (se 1 (by rfl) ⟨11893607, by rfl⟩ : syracuseStep 15858143 = 23787215) B23787215
theorem B10572095 : Blo 1927435 10572095 := bstep (se 1 (by rfl) ⟨7929071, by rfl⟩ : syracuseStep 10572095 = 15858143) B15858143
theorem B7048063 : Blo 1927435 7048063 := bstep (se 1 (by rfl) ⟨5286047, by rfl⟩ : syracuseStep 7048063 = 10572095) B10572095
theorem B9397417 : Blo 1927435 9397417 := bstep (se 2 (by rfl) ⟨3524031, by rfl⟩ : syracuseStep 9397417 = 7048063) B7048063
theorem B12529889 : Blo 1927435 12529889 := bstep (se 2 (by rfl) ⟨4698708, by rfl⟩ : syracuseStep 12529889 = 9397417) B9397417
theorem B8353259 : Blo 1927435 8353259 := bstep (se 1 (by rfl) ⟨6264944, by rfl⟩ : syracuseStep 8353259 = 12529889) B12529889
theorem B5568839 : Blo 1927435 5568839 := bstep (se 1 (by rfl) ⟨4176629, by rfl⟩ : syracuseStep 5568839 = 8353259) B8353259
theorem B3712559 : Blo 1927435 3712559 := bstep (se 1 (by rfl) ⟨2784419, by rfl⟩ : syracuseStep 3712559 = 5568839) B5568839
theorem B9900157 : Blo 1927435 9900157 := bstep (se 3 (by rfl) ⟨1856279, by rfl⟩ : syracuseStep 9900157 = 3712559) B3712559
theorem B13200209 : Blo 1927435 13200209 := bstep (se 2 (by rfl) ⟨4950078, by rfl⟩ : syracuseStep 13200209 = 9900157) B9900157
theorem B8800139 : Blo 1927435 8800139 := bstep (se 1 (by rfl) ⟨6600104, by rfl⟩ : syracuseStep 8800139 = 13200209) B13200209
theorem B5866759 : Blo 1927435 5866759 := bstep (se 1 (by rfl) ⟨4400069, by rfl⟩ : syracuseStep 5866759 = 8800139) B8800139
theorem B7822345 : Blo 1927435 7822345 := bstep (se 2 (by rfl) ⟨2933379, by rfl⟩ : syracuseStep 7822345 = 5866759) B5866759
theorem B10429793 : Blo 1927435 10429793 := bstep (se 2 (by rfl) ⟨3911172, by rfl⟩ : syracuseStep 10429793 = 7822345) B7822345
theorem B6953195 : Blo 1927435 6953195 := bstep (se 1 (by rfl) ⟨5214896, by rfl⟩ : syracuseStep 6953195 = 10429793) B10429793
theorem B4635463 : Blo 1927435 4635463 := bstep (se 1 (by rfl) ⟨3476597, by rfl⟩ : syracuseStep 4635463 = 6953195) B6953195
theorem B6180617 : Blo 1927435 6180617 := bstep (se 2 (by rfl) ⟨2317731, by rfl⟩ : syracuseStep 6180617 = 4635463) B4635463
theorem B4120411 : Blo 1927435 4120411 := bstep (se 1 (by rfl) ⟨3090308, by rfl⟩ : syracuseStep 4120411 = 6180617) B6180617
theorem B5493881 : Blo 1927435 5493881 := bstep (se 2 (by rfl) ⟨2060205, by rfl⟩ : syracuseStep 5493881 = 4120411) B4120411
theorem B3662587 : Blo 1927435 3662587 := bstep (se 1 (by rfl) ⟨2746940, by rfl⟩ : syracuseStep 3662587 = 5493881) B5493881
theorem B4883449 : Blo 1927435 4883449 := bstep (se 2 (by rfl) ⟨1831293, by rfl⟩ : syracuseStep 4883449 = 3662587) B3662587
theorem B6511265 : Blo 1927435 6511265 := bstep (se 2 (by rfl) ⟨2441724, by rfl⟩ : syracuseStep 6511265 = 4883449) B4883449
theorem B4340843 : Blo 1927435 4340843 := bstep (se 1 (by rfl) ⟨3255632, by rfl⟩ : syracuseStep 4340843 = 6511265) B6511265
theorem B2893895 : Blo 1927435 2893895 := bstep (se 1 (by rfl) ⟨2170421, by rfl⟩ : syracuseStep 2893895 = 4340843) B4340843
theorem B1929263 : Blo 1927435 1929263 := bstep (se 1 (by rfl) ⟨1446947, by rfl⟩ : syracuseStep 1929263 = 2893895) B2893895
theorem B2893901 : Blo 1927435 2893901 := bbase (se 3 (by rfl) ⟨542606, by rfl⟩ : syracuseStep 2893901 = 1085213) (by norm_num)
theorem B1929267 : Blo 1927435 1929267 := bstep (se 1 (by rfl) ⟨1446950, by rfl⟩ : syracuseStep 1929267 = 2893901) B2893901
theorem B4340861 : Blo 1927435 4340861 := bbase (se 3 (by rfl) ⟨813911, by rfl⟩ : syracuseStep 4340861 = 1627823) (by norm_num)
theorem B2893907 : Blo 1927435 2893907 := bstep (se 1 (by rfl) ⟨2170430, by rfl⟩ : syracuseStep 2893907 = 4340861) B4340861
theorem B1929271 : Blo 1927435 1929271 := bstep (se 1 (by rfl) ⟨1446953, by rfl⟩ : syracuseStep 1929271 = 2893907) B2893907
theorem B3255653 : Blo 1927435 3255653 := bbase (se 4 (by rfl) ⟨305217, by rfl⟩ : syracuseStep 3255653 = 610435) (by norm_num)
theorem B2170435 : Blo 1927435 2170435 := bstep (se 1 (by rfl) ⟨1627826, by rfl⟩ : syracuseStep 2170435 = 3255653) B3255653
theorem B2893913 : Blo 1927435 2893913 := bstep (se 2 (by rfl) ⟨1085217, by rfl⟩ : syracuseStep 2893913 = 2170435) B2170435
theorem B1929275 : Blo 1927435 1929275 := bstep (se 1 (by rfl) ⟨1446956, by rfl⟩ : syracuseStep 1929275 = 2893913) B2893913
theorem B4120445 : Blo 1927435 4120445 := bbase (se 3 (by rfl) ⟨772583, by rfl⟩ : syracuseStep 4120445 = 1545167) (by norm_num)
theorem B2746963 : Blo 1927435 2746963 := bstep (se 1 (by rfl) ⟨2060222, by rfl⟩ : syracuseStep 2746963 = 4120445) B4120445
theorem B14650469 : Blo 1927435 14650469 := bstep (se 4 (by rfl) ⟨1373481, by rfl⟩ : syracuseStep 14650469 = 2746963) B2746963
theorem B9766979 : Blo 1927435 9766979 := bstep (se 1 (by rfl) ⟨7325234, by rfl⟩ : syracuseStep 9766979 = 14650469) B14650469
theorem B6511319 : Blo 1927435 6511319 := bstep (se 1 (by rfl) ⟨4883489, by rfl⟩ : syracuseStep 6511319 = 9766979) B9766979
theorem B4340879 : Blo 1927435 4340879 := bstep (se 1 (by rfl) ⟨3255659, by rfl⟩ : syracuseStep 4340879 = 6511319) B6511319
theorem B2893919 : Blo 1927435 2893919 := bstep (se 1 (by rfl) ⟨2170439, by rfl⟩ : syracuseStep 2893919 = 4340879) B4340879
theorem B1929279 : Blo 1927435 1929279 := bstep (se 1 (by rfl) ⟨1446959, by rfl⟩ : syracuseStep 1929279 = 2893919) B2893919
theorem B2893925 : Blo 1927435 2893925 := bbase (se 4 (by rfl) ⟨271305, by rfl⟩ : syracuseStep 2893925 = 542611) (by norm_num)
theorem B1929283 : Blo 1927435 1929283 := bstep (se 1 (by rfl) ⟨1446962, by rfl⟩ : syracuseStep 1929283 = 2893925) B2893925
theorem B18084053 : Blo 1927435 18084053 := bbase (se 7 (by rfl) ⟨211922, by rfl⟩ : syracuseStep 18084053 = 423845) (by norm_num)
theorem B12056035 : Blo 1927435 12056035 := bstep (se 1 (by rfl) ⟨9042026, by rfl⟩ : syracuseStep 12056035 = 18084053) B18084053
theorem B16074713 : Blo 1927435 16074713 := bstep (se 2 (by rfl) ⟨6028017, by rfl⟩ : syracuseStep 16074713 = 12056035) B12056035
theorem B10716475 : Blo 1927435 10716475 := bstep (se 1 (by rfl) ⟨8037356, by rfl⟩ : syracuseStep 10716475 = 16074713) B16074713
theorem B14288633 : Blo 1927435 14288633 := bstep (se 2 (by rfl) ⟨5358237, by rfl⟩ : syracuseStep 14288633 = 10716475) B10716475
theorem B9525755 : Blo 1927435 9525755 := bstep (se 1 (by rfl) ⟨7144316, by rfl⟩ : syracuseStep 9525755 = 14288633) B14288633
theorem B6350503 : Blo 1927435 6350503 := bstep (se 1 (by rfl) ⟨4762877, by rfl⟩ : syracuseStep 6350503 = 9525755) B9525755
theorem B8467337 : Blo 1927435 8467337 := bstep (se 2 (by rfl) ⟨3175251, by rfl⟩ : syracuseStep 8467337 = 6350503) B6350503
theorem B5644891 : Blo 1927435 5644891 := bstep (se 1 (by rfl) ⟨4233668, by rfl⟩ : syracuseStep 5644891 = 8467337) B8467337
theorem B7526521 : Blo 1927435 7526521 := bstep (se 2 (by rfl) ⟨2822445, by rfl⟩ : syracuseStep 7526521 = 5644891) B5644891
theorem B10035361 : Blo 1927435 10035361 := bstep (se 2 (by rfl) ⟨3763260, by rfl⟩ : syracuseStep 10035361 = 7526521) B7526521
theorem B13380481 : Blo 1927435 13380481 := bstep (se 2 (by rfl) ⟨5017680, by rfl⟩ : syracuseStep 13380481 = 10035361) B10035361
theorem B17840641 : Blo 1927435 17840641 := bstep (se 2 (by rfl) ⟨6690240, by rfl⟩ : syracuseStep 17840641 = 13380481) B13380481
theorem B23787521 : Blo 1927435 23787521 := bstep (se 2 (by rfl) ⟨8920320, by rfl⟩ : syracuseStep 23787521 = 17840641) B17840641
theorem B15858347 : Blo 1927435 15858347 := bstep (se 1 (by rfl) ⟨11893760, by rfl⟩ : syracuseStep 15858347 = 23787521) B23787521
theorem B42288925 : Blo 1927435 42288925 := bstep (se 3 (by rfl) ⟨7929173, by rfl⟩ : syracuseStep 42288925 = 15858347) B15858347
theorem B56385233 : Blo 1927435 56385233 := bstep (se 2 (by rfl) ⟨21144462, by rfl⟩ : syracuseStep 56385233 = 42288925) B42288925
theorem B37590155 : Blo 1927435 37590155 := bstep (se 1 (by rfl) ⟨28192616, by rfl⟩ : syracuseStep 37590155 = 56385233) B56385233
theorem B25060103 : Blo 1927435 25060103 := bstep (se 1 (by rfl) ⟨18795077, by rfl⟩ : syracuseStep 25060103 = 37590155) B37590155
theorem B16706735 : Blo 1927435 16706735 := bstep (se 1 (by rfl) ⟨12530051, by rfl⟩ : syracuseStep 16706735 = 25060103) B25060103
theorem B11137823 : Blo 1927435 11137823 := bstep (se 1 (by rfl) ⟨8353367, by rfl⟩ : syracuseStep 11137823 = 16706735) B16706735
theorem B7425215 : Blo 1927435 7425215 := bstep (se 1 (by rfl) ⟨5568911, by rfl⟩ : syracuseStep 7425215 = 11137823) B11137823
theorem B4950143 : Blo 1927435 4950143 := bstep (se 1 (by rfl) ⟨3712607, by rfl⟩ : syracuseStep 4950143 = 7425215) B7425215
theorem B3300095 : Blo 1927435 3300095 := bstep (se 1 (by rfl) ⟨2475071, by rfl⟩ : syracuseStep 3300095 = 4950143) B4950143
theorem B2200063 : Blo 1927435 2200063 := bstep (se 1 (by rfl) ⟨1650047, by rfl⟩ : syracuseStep 2200063 = 3300095) B3300095
theorem B2933417 : Blo 1927435 2933417 := bstep (se 2 (by rfl) ⟨1100031, by rfl⟩ : syracuseStep 2933417 = 2200063) B2200063
theorem B1955611 : Blo 1927435 1955611 := bstep (se 1 (by rfl) ⟨1466708, by rfl⟩ : syracuseStep 1955611 = 2933417) B2933417
theorem B2607481 : Blo 1927435 2607481 := bstep (se 2 (by rfl) ⟨977805, by rfl⟩ : syracuseStep 2607481 = 1955611) B1955611
theorem B13906565 : Blo 1927435 13906565 := bstep (se 4 (by rfl) ⟨1303740, by rfl⟩ : syracuseStep 13906565 = 2607481) B2607481
theorem B9271043 : Blo 1927435 9271043 := bstep (se 1 (by rfl) ⟨6953282, by rfl⟩ : syracuseStep 9271043 = 13906565) B13906565
theorem B6180695 : Blo 1927435 6180695 := bstep (se 1 (by rfl) ⟨4635521, by rfl⟩ : syracuseStep 6180695 = 9271043) B9271043
theorem B4120463 : Blo 1927435 4120463 := bstep (se 1 (by rfl) ⟨3090347, by rfl⟩ : syracuseStep 4120463 = 6180695) B6180695
theorem B2746975 : Blo 1927435 2746975 := bstep (se 1 (by rfl) ⟨2060231, by rfl⟩ : syracuseStep 2746975 = 4120463) B4120463
theorem B3662633 : Blo 1927435 3662633 := bstep (se 2 (by rfl) ⟨1373487, by rfl⟩ : syracuseStep 3662633 = 2746975) B2746975
theorem B2441755 : Blo 1927435 2441755 := bstep (se 1 (by rfl) ⟨1831316, by rfl⟩ : syracuseStep 2441755 = 3662633) B3662633
theorem B3255673 : Blo 1927435 3255673 := bstep (se 2 (by rfl) ⟨1220877, by rfl⟩ : syracuseStep 3255673 = 2441755) B2441755
theorem B4340897 : Blo 1927435 4340897 := bstep (se 2 (by rfl) ⟨1627836, by rfl⟩ : syracuseStep 4340897 = 3255673) B3255673
theorem B2893931 : Blo 1927435 2893931 := bstep (se 1 (by rfl) ⟨2170448, by rfl⟩ : syracuseStep 2893931 = 4340897) B4340897
theorem B1929287 : Blo 1927435 1929287 := bstep (se 1 (by rfl) ⟨1446965, by rfl⟩ : syracuseStep 1929287 = 2893931) B2893931
theorem B2170453 : Blo 1927435 2170453 := bbase (se 8 (by rfl) ⟨12717, by rfl⟩ : syracuseStep 2170453 = 25435) (by norm_num)
theorem B2893937 : Blo 1927435 2893937 := bstep (se 2 (by rfl) ⟨1085226, by rfl⟩ : syracuseStep 2893937 = 2170453) B2170453
theorem B1929291 : Blo 1927435 1929291 := bstep (se 1 (by rfl) ⟨1446968, by rfl⟩ : syracuseStep 1929291 = 2893937) B2893937
theorem B2441765 : Blo 1927435 2441765 := bbase (se 4 (by rfl) ⟨228915, by rfl⟩ : syracuseStep 2441765 = 457831) (by norm_num)
theorem B6511373 : Blo 1927435 6511373 := bstep (se 3 (by rfl) ⟨1220882, by rfl⟩ : syracuseStep 6511373 = 2441765) B2441765
theorem B4340915 : Blo 1927435 4340915 := bstep (se 1 (by rfl) ⟨3255686, by rfl⟩ : syracuseStep 4340915 = 6511373) B6511373
theorem B2893943 : Blo 1927435 2893943 := bstep (se 1 (by rfl) ⟨2170457, by rfl⟩ : syracuseStep 2893943 = 4340915) B4340915
theorem B1929295 : Blo 1927435 1929295 := bstep (se 1 (by rfl) ⟨1446971, by rfl⟩ : syracuseStep 1929295 = 2893943) B2893943
theorem B2893949 : Blo 1927435 2893949 := bbase (se 3 (by rfl) ⟨542615, by rfl⟩ : syracuseStep 2893949 = 1085231) (by norm_num)
theorem B1929299 : Blo 1927435 1929299 := bstep (se 1 (by rfl) ⟨1446974, by rfl⟩ : syracuseStep 1929299 = 2893949) B2893949
theorem B4340933 : Blo 1927435 4340933 := bbase (se 4 (by rfl) ⟨406962, by rfl⟩ : syracuseStep 4340933 = 813925) (by norm_num)
theorem B2893955 : Blo 1927435 2893955 := bstep (se 1 (by rfl) ⟨2170466, by rfl⟩ : syracuseStep 2893955 = 4340933) B4340933
theorem B1929303 : Blo 1927435 1929303 := bstep (se 1 (by rfl) ⟨1446977, by rfl⟩ : syracuseStep 1929303 = 2893955) B2893955
theorem B3476677 : Blo 1927435 3476677 := bbase (se 4 (by rfl) ⟨325938, by rfl⟩ : syracuseStep 3476677 = 651877) (by norm_num)
theorem B4635569 : Blo 1927435 4635569 := bstep (se 2 (by rfl) ⟨1738338, by rfl⟩ : syracuseStep 4635569 = 3476677) B3476677
theorem B12361517 : Blo 1927435 12361517 := bstep (se 3 (by rfl) ⟨2317784, by rfl⟩ : syracuseStep 12361517 = 4635569) B4635569
theorem B8241011 : Blo 1927435 8241011 := bstep (se 1 (by rfl) ⟨6180758, by rfl⟩ : syracuseStep 8241011 = 12361517) B12361517
theorem B5494007 : Blo 1927435 5494007 := bstep (se 1 (by rfl) ⟨4120505, by rfl⟩ : syracuseStep 5494007 = 8241011) B8241011
theorem B3662671 : Blo 1927435 3662671 := bstep (se 1 (by rfl) ⟨2747003, by rfl⟩ : syracuseStep 3662671 = 5494007) B5494007
theorem B4883561 : Blo 1927435 4883561 := bstep (se 2 (by rfl) ⟨1831335, by rfl⟩ : syracuseStep 4883561 = 3662671) B3662671
theorem B3255707 : Blo 1927435 3255707 := bstep (se 1 (by rfl) ⟨2441780, by rfl⟩ : syracuseStep 3255707 = 4883561) B4883561
theorem B2170471 : Blo 1927435 2170471 := bstep (se 1 (by rfl) ⟨1627853, by rfl⟩ : syracuseStep 2170471 = 3255707) B3255707
theorem B2893961 : Blo 1927435 2893961 := bstep (se 2 (by rfl) ⟨1085235, by rfl⟩ : syracuseStep 2893961 = 2170471) B2170471
theorem B1929307 : Blo 1927435 1929307 := bstep (se 1 (by rfl) ⟨1446980, by rfl⟩ : syracuseStep 1929307 = 2893961) B2893961
theorem B9767141 : Blo 1927435 9767141 := bbase (se 4 (by rfl) ⟨915669, by rfl⟩ : syracuseStep 9767141 = 1831339) (by norm_num)
theorem B6511427 : Blo 1927435 6511427 := bstep (se 1 (by rfl) ⟨4883570, by rfl⟩ : syracuseStep 6511427 = 9767141) B9767141
theorem B4340951 : Blo 1927435 4340951 := bstep (se 1 (by rfl) ⟨3255713, by rfl⟩ : syracuseStep 4340951 = 6511427) B6511427
theorem B2893967 : Blo 1927435 2893967 := bstep (se 1 (by rfl) ⟨2170475, by rfl⟩ : syracuseStep 2893967 = 4340951) B4340951
theorem B1929311 : Blo 1927435 1929311 := bstep (se 1 (by rfl) ⟨1446983, by rfl⟩ : syracuseStep 1929311 = 2893967) B2893967
theorem B2893973 : Blo 1927435 2893973 := bbase (se 6 (by rfl) ⟨67827, by rfl⟩ : syracuseStep 2893973 = 135655) (by norm_num)
theorem B1929315 : Blo 1927435 1929315 := bstep (se 1 (by rfl) ⟨1446986, by rfl⟩ : syracuseStep 1929315 = 2893973) B2893973
theorem B8241061 : Blo 1927435 8241061 := bbase (se 4 (by rfl) ⟨772599, by rfl⟩ : syracuseStep 8241061 = 1545199) (by norm_num)
theorem B10988081 : Blo 1927435 10988081 := bstep (se 2 (by rfl) ⟨4120530, by rfl⟩ : syracuseStep 10988081 = 8241061) B8241061
theorem B7325387 : Blo 1927435 7325387 := bstep (se 1 (by rfl) ⟨5494040, by rfl⟩ : syracuseStep 7325387 = 10988081) B10988081
theorem B4883591 : Blo 1927435 4883591 := bstep (se 1 (by rfl) ⟨3662693, by rfl⟩ : syracuseStep 4883591 = 7325387) B7325387
theorem B3255727 : Blo 1927435 3255727 := bstep (se 1 (by rfl) ⟨2441795, by rfl⟩ : syracuseStep 3255727 = 4883591) B4883591
theorem B4340969 : Blo 1927435 4340969 := bstep (se 2 (by rfl) ⟨1627863, by rfl⟩ : syracuseStep 4340969 = 3255727) B3255727
theorem B2893979 : Blo 1927435 2893979 := bstep (se 1 (by rfl) ⟨2170484, by rfl⟩ : syracuseStep 2893979 = 4340969) B4340969
theorem B1929319 : Blo 1927435 1929319 := bstep (se 1 (by rfl) ⟨1446989, by rfl⟩ : syracuseStep 1929319 = 2893979) B2893979
theorem B2170489 : Blo 1927435 2170489 := bbase (se 2 (by rfl) ⟨813933, by rfl⟩ : syracuseStep 2170489 = 1627867) (by norm_num)
theorem B2893985 : Blo 1927435 2893985 := bstep (se 2 (by rfl) ⟨1085244, by rfl⟩ : syracuseStep 2893985 = 2170489) B2170489
theorem B1929323 : Blo 1927435 1929323 := bstep (se 1 (by rfl) ⟨1446992, by rfl⟩ : syracuseStep 1929323 = 2893985) B2893985
theorem B2475121 : Blo 1927435 2475121 := bbase (se 2 (by rfl) ⟨928170, by rfl⟩ : syracuseStep 2475121 = 1856341) (by norm_num)
theorem B3300161 : Blo 1927435 3300161 := bstep (se 2 (by rfl) ⟨1237560, by rfl⟩ : syracuseStep 3300161 = 2475121) B2475121
theorem B8800429 : Blo 1927435 8800429 := bstep (se 3 (by rfl) ⟨1650080, by rfl⟩ : syracuseStep 8800429 = 3300161) B3300161
theorem B11733905 : Blo 1927435 11733905 := bstep (se 2 (by rfl) ⟨4400214, by rfl⟩ : syracuseStep 11733905 = 8800429) B8800429
theorem B7822603 : Blo 1927435 7822603 := bstep (se 1 (by rfl) ⟨5866952, by rfl⟩ : syracuseStep 7822603 = 11733905) B11733905
theorem B10430137 : Blo 1927435 10430137 := bstep (se 2 (by rfl) ⟨3911301, by rfl⟩ : syracuseStep 10430137 = 7822603) B7822603
theorem B13906849 : Blo 1927435 13906849 := bstep (se 2 (by rfl) ⟨5215068, by rfl⟩ : syracuseStep 13906849 = 10430137) B10430137
theorem B18542465 : Blo 1927435 18542465 := bstep (se 2 (by rfl) ⟨6953424, by rfl⟩ : syracuseStep 18542465 = 13906849) B13906849
theorem B12361643 : Blo 1927435 12361643 := bstep (se 1 (by rfl) ⟨9271232, by rfl⟩ : syracuseStep 12361643 = 18542465) B18542465
theorem B8241095 : Blo 1927435 8241095 := bstep (se 1 (by rfl) ⟨6180821, by rfl⟩ : syracuseStep 8241095 = 12361643) B12361643
theorem B5494063 : Blo 1927435 5494063 := bstep (se 1 (by rfl) ⟨4120547, by rfl⟩ : syracuseStep 5494063 = 8241095) B8241095
theorem B7325417 : Blo 1927435 7325417 := bstep (se 2 (by rfl) ⟨2747031, by rfl⟩ : syracuseStep 7325417 = 5494063) B5494063
theorem B4883611 : Blo 1927435 4883611 := bstep (se 1 (by rfl) ⟨3662708, by rfl⟩ : syracuseStep 4883611 = 7325417) B7325417
theorem B6511481 : Blo 1927435 6511481 := bstep (se 2 (by rfl) ⟨2441805, by rfl⟩ : syracuseStep 6511481 = 4883611) B4883611
theorem B4340987 : Blo 1927435 4340987 := bstep (se 1 (by rfl) ⟨3255740, by rfl⟩ : syracuseStep 4340987 = 6511481) B6511481
theorem B2893991 : Blo 1927435 2893991 := bstep (se 1 (by rfl) ⟨2170493, by rfl⟩ : syracuseStep 2893991 = 4340987) B4340987
theorem B1929327 : Blo 1927435 1929327 := bstep (se 1 (by rfl) ⟨1446995, by rfl⟩ : syracuseStep 1929327 = 2893991) B2893991
theorem B2893997 : Blo 1927435 2893997 := bbase (se 3 (by rfl) ⟨542624, by rfl⟩ : syracuseStep 2893997 = 1085249) (by norm_num)
theorem B1929331 : Blo 1927435 1929331 := bstep (se 1 (by rfl) ⟨1446998, by rfl⟩ : syracuseStep 1929331 = 2893997) B2893997
theorem B4341005 : Blo 1927435 4341005 := bbase (se 3 (by rfl) ⟨813938, by rfl⟩ : syracuseStep 4341005 = 1627877) (by norm_num)
theorem B2894003 : Blo 1927435 2894003 := bstep (se 1 (by rfl) ⟨2170502, by rfl⟩ : syracuseStep 2894003 = 4341005) B4341005
theorem B1929335 : Blo 1927435 1929335 := bstep (se 1 (by rfl) ⟨1447001, by rfl⟩ : syracuseStep 1929335 = 2894003) B2894003
theorem B2441821 : Blo 1927435 2441821 := bbase (se 3 (by rfl) ⟨457841, by rfl⟩ : syracuseStep 2441821 = 915683) (by norm_num)
theorem B3255761 : Blo 1927435 3255761 := bstep (se 2 (by rfl) ⟨1220910, by rfl⟩ : syracuseStep 3255761 = 2441821) B2441821
theorem B2170507 : Blo 1927435 2170507 := bstep (se 1 (by rfl) ⟨1627880, by rfl⟩ : syracuseStep 2170507 = 3255761) B3255761
theorem B2894009 : Blo 1927435 2894009 := bstep (se 2 (by rfl) ⟨1085253, by rfl⟩ : syracuseStep 2894009 = 2170507) B2170507
theorem B1929339 : Blo 1927435 1929339 := bstep (se 1 (by rfl) ⟨1447004, by rfl⟩ : syracuseStep 1929339 = 2894009) B2894009
theorem B16482325 : Blo 1927435 16482325 := bbase (se 6 (by rfl) ⟨386304, by rfl⟩ : syracuseStep 16482325 = 772609) (by norm_num)
theorem B21976433 : Blo 1927435 21976433 := bstep (se 2 (by rfl) ⟨8241162, by rfl⟩ : syracuseStep 21976433 = 16482325) B16482325
theorem B14650955 : Blo 1927435 14650955 := bstep (se 1 (by rfl) ⟨10988216, by rfl⟩ : syracuseStep 14650955 = 21976433) B21976433
theorem B9767303 : Blo 1927435 9767303 := bstep (se 1 (by rfl) ⟨7325477, by rfl⟩ : syracuseStep 9767303 = 14650955) B14650955
theorem B6511535 : Blo 1927435 6511535 := bstep (se 1 (by rfl) ⟨4883651, by rfl⟩ : syracuseStep 6511535 = 9767303) B9767303
theorem B4341023 : Blo 1927435 4341023 := bstep (se 1 (by rfl) ⟨3255767, by rfl⟩ : syracuseStep 4341023 = 6511535) B6511535
theorem B2894015 : Blo 1927435 2894015 := bstep (se 1 (by rfl) ⟨2170511, by rfl⟩ : syracuseStep 2894015 = 4341023) B4341023
theorem B1929343 : Blo 1927435 1929343 := bstep (se 1 (by rfl) ⟨1447007, by rfl⟩ : syracuseStep 1929343 = 2894015) B2894015
theorem B2894021 : Blo 1927435 2894021 := bbase (se 4 (by rfl) ⟨271314, by rfl⟩ : syracuseStep 2894021 = 542629) (by norm_num)
theorem B1929347 : Blo 1927435 1929347 := bstep (se 1 (by rfl) ⟨1447010, by rfl⟩ : syracuseStep 1929347 = 2894021) B2894021
theorem B3255781 : Blo 1927435 3255781 := bbase (se 4 (by rfl) ⟨305229, by rfl⟩ : syracuseStep 3255781 = 610459) (by norm_num)
theorem B4341041 : Blo 1927435 4341041 := bstep (se 2 (by rfl) ⟨1627890, by rfl⟩ : syracuseStep 4341041 = 3255781) B3255781
theorem B2894027 : Blo 1927435 2894027 := bstep (se 1 (by rfl) ⟨2170520, by rfl⟩ : syracuseStep 2894027 = 4341041) B4341041
theorem B1929351 : Blo 1927435 1929351 := bstep (se 1 (by rfl) ⟨1447013, by rfl⟩ : syracuseStep 1929351 = 2894027) B2894027
theorem B2170525 : Blo 1927435 2170525 := bbase (se 3 (by rfl) ⟨406973, by rfl⟩ : syracuseStep 2170525 = 813947) (by norm_num)
theorem B2894033 : Blo 1927435 2894033 := bstep (se 2 (by rfl) ⟨1085262, by rfl⟩ : syracuseStep 2894033 = 2170525) B2170525
theorem B1929355 : Blo 1927435 1929355 := bstep (se 1 (by rfl) ⟨1447016, by rfl⟩ : syracuseStep 1929355 = 2894033) B2894033
theorem B6511589 : Blo 1927435 6511589 := bbase (se 4 (by rfl) ⟨610461, by rfl⟩ : syracuseStep 6511589 = 1220923) (by norm_num)
theorem B4341059 : Blo 1927435 4341059 := bstep (se 1 (by rfl) ⟨3255794, by rfl⟩ : syracuseStep 4341059 = 6511589) B6511589
theorem B2894039 : Blo 1927435 2894039 := bstep (se 1 (by rfl) ⟨2170529, by rfl⟩ : syracuseStep 2894039 = 4341059) B4341059
theorem B1929359 : Blo 1927435 1929359 := bstep (se 1 (by rfl) ⟨1447019, by rfl⟩ : syracuseStep 1929359 = 2894039) B2894039
theorem B2894045 : Blo 1927435 2894045 := bbase (se 3 (by rfl) ⟨542633, by rfl⟩ : syracuseStep 2894045 = 1085267) (by norm_num)
theorem B1929363 : Blo 1927435 1929363 := bstep (se 1 (by rfl) ⟨1447022, by rfl⟩ : syracuseStep 1929363 = 2894045) B2894045
theorem B4341077 : Blo 1927435 4341077 := bbase (se 11 (by rfl) ⟨3179, by rfl⟩ : syracuseStep 4341077 = 6359) (by norm_num)
theorem B2894051 : Blo 1927435 2894051 := bstep (se 1 (by rfl) ⟨2170538, by rfl⟩ : syracuseStep 2894051 = 4341077) B4341077
theorem B1929367 : Blo 1927435 1929367 := bstep (se 1 (by rfl) ⟨1447025, by rfl⟩ : syracuseStep 1929367 = 2894051) B2894051
theorem B2060321 : Blo 1927435 2060321 := bbase (se 2 (by rfl) ⟨772620, by rfl⟩ : syracuseStep 2060321 = 1545241) (by norm_num)
theorem B5494189 : Blo 1927435 5494189 := bstep (se 3 (by rfl) ⟨1030160, by rfl⟩ : syracuseStep 5494189 = 2060321) B2060321
theorem B7325585 : Blo 1927435 7325585 := bstep (se 2 (by rfl) ⟨2747094, by rfl⟩ : syracuseStep 7325585 = 5494189) B5494189
theorem B4883723 : Blo 1927435 4883723 := bstep (se 1 (by rfl) ⟨3662792, by rfl⟩ : syracuseStep 4883723 = 7325585) B7325585
theorem B3255815 : Blo 1927435 3255815 := bstep (se 1 (by rfl) ⟨2441861, by rfl⟩ : syracuseStep 3255815 = 4883723) B4883723
theorem B2170543 : Blo 1927435 2170543 := bstep (se 1 (by rfl) ⟨1627907, by rfl⟩ : syracuseStep 2170543 = 3255815) B3255815
theorem B2894057 : Blo 1927435 2894057 := bstep (se 2 (by rfl) ⟨1085271, by rfl⟩ : syracuseStep 2894057 = 2170543) B2170543
theorem B1929371 : Blo 1927435 1929371 := bstep (se 1 (by rfl) ⟨1447028, by rfl⟩ : syracuseStep 1929371 = 2894057) B2894057
theorem B6600485 : Blo 1927435 6600485 := bbase (se 4 (by rfl) ⟨618795, by rfl⟩ : syracuseStep 6600485 = 1237591) (by norm_num)
theorem B17601293 : Blo 1927435 17601293 := bstep (se 3 (by rfl) ⟨3300242, by rfl⟩ : syracuseStep 17601293 = 6600485) B6600485
theorem B11734195 : Blo 1927435 11734195 := bstep (se 1 (by rfl) ⟨8800646, by rfl⟩ : syracuseStep 11734195 = 17601293) B17601293
theorem B15645593 : Blo 1927435 15645593 := bstep (se 2 (by rfl) ⟨5867097, by rfl⟩ : syracuseStep 15645593 = 11734195) B11734195
theorem B41721581 : Blo 1927435 41721581 := bstep (se 3 (by rfl) ⟨7822796, by rfl⟩ : syracuseStep 41721581 = 15645593) B15645593
theorem B27814387 : Blo 1927435 27814387 := bstep (se 1 (by rfl) ⟨20860790, by rfl⟩ : syracuseStep 27814387 = 41721581) B41721581
theorem B37085849 : Blo 1927435 37085849 := bstep (se 2 (by rfl) ⟨13907193, by rfl⟩ : syracuseStep 37085849 = 27814387) B27814387
theorem B24723899 : Blo 1927435 24723899 := bstep (se 1 (by rfl) ⟨18542924, by rfl⟩ : syracuseStep 24723899 = 37085849) B37085849
theorem B16482599 : Blo 1927435 16482599 := bstep (se 1 (by rfl) ⟨12361949, by rfl⟩ : syracuseStep 16482599 = 24723899) B24723899
theorem B10988399 : Blo 1927435 10988399 := bstep (se 1 (by rfl) ⟨8241299, by rfl⟩ : syracuseStep 10988399 = 16482599) B16482599
theorem B7325599 : Blo 1927435 7325599 := bstep (se 1 (by rfl) ⟨5494199, by rfl⟩ : syracuseStep 7325599 = 10988399) B10988399
theorem B9767465 : Blo 1927435 9767465 := bstep (se 2 (by rfl) ⟨3662799, by rfl⟩ : syracuseStep 9767465 = 7325599) B7325599
theorem B6511643 : Blo 1927435 6511643 := bstep (se 1 (by rfl) ⟨4883732, by rfl⟩ : syracuseStep 6511643 = 9767465) B9767465
theorem B4341095 : Blo 1927435 4341095 := bstep (se 1 (by rfl) ⟨3255821, by rfl⟩ : syracuseStep 4341095 = 6511643) B6511643
theorem B2894063 : Blo 1927435 2894063 := bstep (se 1 (by rfl) ⟨2170547, by rfl⟩ : syracuseStep 2894063 = 4341095) B4341095
theorem B1929375 : Blo 1927435 1929375 := bstep (se 1 (by rfl) ⟨1447031, by rfl⟩ : syracuseStep 1929375 = 2894063) B2894063
theorem B2894069 : Blo 1927435 2894069 := bbase (se 5 (by rfl) ⟨135659, by rfl⟩ : syracuseStep 2894069 = 271319) (by norm_num)
theorem B1929379 : Blo 1927435 1929379 := bstep (se 1 (by rfl) ⟨1447034, by rfl⟩ : syracuseStep 1929379 = 2894069) B2894069
theorem B3964781 : Blo 1927435 3964781 := bbase (se 3 (by rfl) ⟨743396, by rfl⟩ : syracuseStep 3964781 = 1486793) (by norm_num)
theorem B10572749 : Blo 1927435 10572749 := bstep (se 3 (by rfl) ⟨1982390, by rfl⟩ : syracuseStep 10572749 = 3964781) B3964781
theorem B7048499 : Blo 1927435 7048499 := bstep (se 1 (by rfl) ⟨5286374, by rfl⟩ : syracuseStep 7048499 = 10572749) B10572749
theorem B18795997 : Blo 1927435 18795997 := bstep (se 3 (by rfl) ⟨3524249, by rfl⟩ : syracuseStep 18795997 = 7048499) B7048499
theorem B25061329 : Blo 1927435 25061329 := bstep (se 2 (by rfl) ⟨9397998, by rfl⟩ : syracuseStep 25061329 = 18795997) B18795997
theorem B33415105 : Blo 1927435 33415105 := bstep (se 2 (by rfl) ⟨12530664, by rfl⟩ : syracuseStep 33415105 = 25061329) B25061329
theorem B44553473 : Blo 1927435 44553473 := bstep (se 2 (by rfl) ⟨16707552, by rfl⟩ : syracuseStep 44553473 = 33415105) B33415105
theorem B29702315 : Blo 1927435 29702315 := bstep (se 1 (by rfl) ⟨22276736, by rfl⟩ : syracuseStep 29702315 = 44553473) B44553473
theorem B19801543 : Blo 1927435 19801543 := bstep (se 1 (by rfl) ⟨14851157, by rfl⟩ : syracuseStep 19801543 = 29702315) B29702315
theorem B26402057 : Blo 1927435 26402057 := bstep (se 2 (by rfl) ⟨9900771, by rfl⟩ : syracuseStep 26402057 = 19801543) B19801543
theorem B17601371 : Blo 1927435 17601371 := bstep (se 1 (by rfl) ⟨13201028, by rfl⟩ : syracuseStep 17601371 = 26402057) B26402057
theorem B11734247 : Blo 1927435 11734247 := bstep (se 1 (by rfl) ⟨8800685, by rfl⟩ : syracuseStep 11734247 = 17601371) B17601371
theorem B7822831 : Blo 1927435 7822831 := bstep (se 1 (by rfl) ⟨5867123, by rfl⟩ : syracuseStep 7822831 = 11734247) B11734247
theorem B10430441 : Blo 1927435 10430441 := bstep (se 2 (by rfl) ⟨3911415, by rfl⟩ : syracuseStep 10430441 = 7822831) B7822831
theorem B6953627 : Blo 1927435 6953627 := bstep (se 1 (by rfl) ⟨5215220, by rfl⟩ : syracuseStep 6953627 = 10430441) B10430441
theorem B18543005 : Blo 1927435 18543005 := bstep (se 3 (by rfl) ⟨3476813, by rfl⟩ : syracuseStep 18543005 = 6953627) B6953627
theorem B12362003 : Blo 1927435 12362003 := bstep (se 1 (by rfl) ⟨9271502, by rfl⟩ : syracuseStep 12362003 = 18543005) B18543005
theorem B8241335 : Blo 1927435 8241335 := bstep (se 1 (by rfl) ⟨6181001, by rfl⟩ : syracuseStep 8241335 = 12362003) B12362003
theorem B5494223 : Blo 1927435 5494223 := bstep (se 1 (by rfl) ⟨4120667, by rfl⟩ : syracuseStep 5494223 = 8241335) B8241335
theorem B3662815 : Blo 1927435 3662815 := bstep (se 1 (by rfl) ⟨2747111, by rfl⟩ : syracuseStep 3662815 = 5494223) B5494223
theorem B4883753 : Blo 1927435 4883753 := bstep (se 2 (by rfl) ⟨1831407, by rfl⟩ : syracuseStep 4883753 = 3662815) B3662815
theorem B3255835 : Blo 1927435 3255835 := bstep (se 1 (by rfl) ⟨2441876, by rfl⟩ : syracuseStep 3255835 = 4883753) B4883753
theorem B4341113 : Blo 1927435 4341113 := bstep (se 2 (by rfl) ⟨1627917, by rfl⟩ : syracuseStep 4341113 = 3255835) B3255835
theorem B2894075 : Blo 1927435 2894075 := bstep (se 1 (by rfl) ⟨2170556, by rfl⟩ : syracuseStep 2894075 = 4341113) B4341113
theorem B1929383 : Blo 1927435 1929383 := bstep (se 1 (by rfl) ⟨1447037, by rfl⟩ : syracuseStep 1929383 = 2894075) B2894075
theorem B2170561 : Blo 1927435 2170561 := bbase (se 2 (by rfl) ⟨813960, by rfl⟩ : syracuseStep 2170561 = 1627921) (by norm_num)
theorem B2894081 : Blo 1927435 2894081 := bstep (se 2 (by rfl) ⟨1085280, by rfl⟩ : syracuseStep 2894081 = 2170561) B2170561
theorem B1929387 : Blo 1927435 1929387 := bstep (se 1 (by rfl) ⟨1447040, by rfl⟩ : syracuseStep 1929387 = 2894081) B2894081
theorem B4883773 : Blo 1927435 4883773 := bbase (se 3 (by rfl) ⟨915707, by rfl⟩ : syracuseStep 4883773 = 1831415) (by norm_num)
theorem B6511697 : Blo 1927435 6511697 := bstep (se 2 (by rfl) ⟨2441886, by rfl⟩ : syracuseStep 6511697 = 4883773) B4883773
theorem B4341131 : Blo 1927435 4341131 := bstep (se 1 (by rfl) ⟨3255848, by rfl⟩ : syracuseStep 4341131 = 6511697) B6511697
theorem B2894087 : Blo 1927435 2894087 := bstep (se 1 (by rfl) ⟨2170565, by rfl⟩ : syracuseStep 2894087 = 4341131) B4341131
theorem B1929391 : Blo 1927435 1929391 := bstep (se 1 (by rfl) ⟨1447043, by rfl⟩ : syracuseStep 1929391 = 2894087) B2894087
theorem B2894093 : Blo 1927435 2894093 := bbase (se 3 (by rfl) ⟨542642, by rfl⟩ : syracuseStep 2894093 = 1085285) (by norm_num)
theorem B1929395 : Blo 1927435 1929395 := bstep (se 1 (by rfl) ⟨1447046, by rfl⟩ : syracuseStep 1929395 = 2894093) B2894093
theorem B4341149 : Blo 1927435 4341149 := bbase (se 3 (by rfl) ⟨813965, by rfl⟩ : syracuseStep 4341149 = 1627931) (by norm_num)
theorem B2894099 : Blo 1927435 2894099 := bstep (se 1 (by rfl) ⟨2170574, by rfl⟩ : syracuseStep 2894099 = 4341149) B4341149
theorem B1929399 : Blo 1927435 1929399 := bstep (se 1 (by rfl) ⟨1447049, by rfl⟩ : syracuseStep 1929399 = 2894099) B2894099
theorem B3255869 : Blo 1927435 3255869 := bbase (se 3 (by rfl) ⟨610475, by rfl⟩ : syracuseStep 3255869 = 1220951) (by norm_num)
theorem B2170579 : Blo 1927435 2170579 := bstep (se 1 (by rfl) ⟨1627934, by rfl⟩ : syracuseStep 2170579 = 3255869) B3255869
theorem B2894105 : Blo 1927435 2894105 := bstep (se 2 (by rfl) ⟨1085289, by rfl⟩ : syracuseStep 2894105 = 2170579) B2170579
theorem B1929403 : Blo 1927435 1929403 := bstep (se 1 (by rfl) ⟨1447052, by rfl⟩ : syracuseStep 1929403 = 2894105) B2894105
theorem B14851349 : Blo 1927435 14851349 := bbase (se 6 (by rfl) ⟨348078, by rfl⟩ : syracuseStep 14851349 = 696157) (by norm_num)
theorem B9900899 : Blo 1927435 9900899 := bstep (se 1 (by rfl) ⟨7425674, by rfl⟩ : syracuseStep 9900899 = 14851349) B14851349
theorem B6600599 : Blo 1927435 6600599 := bstep (se 1 (by rfl) ⟨4950449, by rfl⟩ : syracuseStep 6600599 = 9900899) B9900899
theorem B4400399 : Blo 1927435 4400399 := bstep (se 1 (by rfl) ⟨3300299, by rfl⟩ : syracuseStep 4400399 = 6600599) B6600599
theorem B2933599 : Blo 1927435 2933599 := bstep (se 1 (by rfl) ⟨2200199, by rfl⟩ : syracuseStep 2933599 = 4400399) B4400399
theorem B3911465 : Blo 1927435 3911465 := bstep (se 2 (by rfl) ⟨1466799, by rfl⟩ : syracuseStep 3911465 = 2933599) B2933599
theorem B2607643 : Blo 1927435 2607643 := bstep (se 1 (by rfl) ⟨1955732, by rfl⟩ : syracuseStep 2607643 = 3911465) B3911465
theorem B3476857 : Blo 1927435 3476857 := bstep (se 2 (by rfl) ⟨1303821, by rfl⟩ : syracuseStep 3476857 = 2607643) B2607643
theorem B4635809 : Blo 1927435 4635809 := bstep (se 2 (by rfl) ⟨1738428, by rfl⟩ : syracuseStep 4635809 = 3476857) B3476857
theorem B3090539 : Blo 1927435 3090539 := bstep (se 1 (by rfl) ⟨2317904, by rfl⟩ : syracuseStep 3090539 = 4635809) B4635809
theorem B2060359 : Blo 1927435 2060359 := bstep (se 1 (by rfl) ⟨1545269, by rfl⟩ : syracuseStep 2060359 = 3090539) B3090539
theorem B10988581 : Blo 1927435 10988581 := bstep (se 4 (by rfl) ⟨1030179, by rfl⟩ : syracuseStep 10988581 = 2060359) B2060359
theorem B14651441 : Blo 1927435 14651441 := bstep (se 2 (by rfl) ⟨5494290, by rfl⟩ : syracuseStep 14651441 = 10988581) B10988581
theorem B9767627 : Blo 1927435 9767627 := bstep (se 1 (by rfl) ⟨7325720, by rfl⟩ : syracuseStep 9767627 = 14651441) B14651441
theorem B6511751 : Blo 1927435 6511751 := bstep (se 1 (by rfl) ⟨4883813, by rfl⟩ : syracuseStep 6511751 = 9767627) B9767627
theorem B4341167 : Blo 1927435 4341167 := bstep (se 1 (by rfl) ⟨3255875, by rfl⟩ : syracuseStep 4341167 = 6511751) B6511751
theorem B2894111 : Blo 1927435 2894111 := bstep (se 1 (by rfl) ⟨2170583, by rfl⟩ : syracuseStep 2894111 = 4341167) B4341167
theorem B1929407 : Blo 1927435 1929407 := bstep (se 1 (by rfl) ⟨1447055, by rfl⟩ : syracuseStep 1929407 = 2894111) B2894111
theorem B2894117 : Blo 1927435 2894117 := bbase (se 4 (by rfl) ⟨271323, by rfl⟩ : syracuseStep 2894117 = 542647) (by norm_num)
theorem B1929411 : Blo 1927435 1929411 := bstep (se 1 (by rfl) ⟨1447058, by rfl⟩ : syracuseStep 1929411 = 2894117) B2894117
theorem B2441917 : Blo 1927435 2441917 := bbase (se 3 (by rfl) ⟨457859, by rfl⟩ : syracuseStep 2441917 = 915719) (by norm_num)
theorem B3255889 : Blo 1927435 3255889 := bstep (se 2 (by rfl) ⟨1220958, by rfl⟩ : syracuseStep 3255889 = 2441917) B2441917
theorem B4341185 : Blo 1927435 4341185 := bstep (se 2 (by rfl) ⟨1627944, by rfl⟩ : syracuseStep 4341185 = 3255889) B3255889
theorem B2894123 : Blo 1927435 2894123 := bstep (se 1 (by rfl) ⟨2170592, by rfl⟩ : syracuseStep 2894123 = 4341185) B4341185
theorem B1929415 : Blo 1927435 1929415 := bstep (se 1 (by rfl) ⟨1447061, by rfl⟩ : syracuseStep 1929415 = 2894123) B2894123
theorem B2170597 : Blo 1927435 2170597 := bbase (se 4 (by rfl) ⟨203493, by rfl⟩ : syracuseStep 2170597 = 406987) (by norm_num)
theorem B2894129 : Blo 1927435 2894129 := bstep (se 2 (by rfl) ⟨1085298, by rfl⟩ : syracuseStep 2894129 = 2170597) B2170597
theorem B1929419 : Blo 1927435 1929419 := bstep (se 1 (by rfl) ⟨1447064, by rfl⟩ : syracuseStep 1929419 = 2894129) B2894129
theorem B3090565 : Blo 1927435 3090565 := bbase (se 4 (by rfl) ⟨289740, by rfl⟩ : syracuseStep 3090565 = 579481) (by norm_num)
theorem B4120753 : Blo 1927435 4120753 := bstep (se 2 (by rfl) ⟨1545282, by rfl⟩ : syracuseStep 4120753 = 3090565) B3090565
theorem B5494337 : Blo 1927435 5494337 := bstep (se 2 (by rfl) ⟨2060376, by rfl⟩ : syracuseStep 5494337 = 4120753) B4120753
theorem B3662891 : Blo 1927435 3662891 := bstep (se 1 (by rfl) ⟨2747168, by rfl⟩ : syracuseStep 3662891 = 5494337) B5494337
theorem B2441927 : Blo 1927435 2441927 := bstep (se 1 (by rfl) ⟨1831445, by rfl⟩ : syracuseStep 2441927 = 3662891) B3662891
theorem B6511805 : Blo 1927435 6511805 := bstep (se 3 (by rfl) ⟨1220963, by rfl⟩ : syracuseStep 6511805 = 2441927) B2441927
theorem B4341203 : Blo 1927435 4341203 := bstep (se 1 (by rfl) ⟨3255902, by rfl⟩ : syracuseStep 4341203 = 6511805) B6511805
theorem B2894135 : Blo 1927435 2894135 := bstep (se 1 (by rfl) ⟨2170601, by rfl⟩ : syracuseStep 2894135 = 4341203) B4341203
theorem B1929423 : Blo 1927435 1929423 := bstep (se 1 (by rfl) ⟨1447067, by rfl⟩ : syracuseStep 1929423 = 2894135) B2894135
theorem B2894141 : Blo 1927435 2894141 := bbase (se 3 (by rfl) ⟨542651, by rfl⟩ : syracuseStep 2894141 = 1085303) (by norm_num)
theorem B1929427 : Blo 1927435 1929427 := bstep (se 1 (by rfl) ⟨1447070, by rfl⟩ : syracuseStep 1929427 = 2894141) B2894141
theorem B4341221 : Blo 1927435 4341221 := bbase (se 4 (by rfl) ⟨406989, by rfl⟩ : syracuseStep 4341221 = 813979) (by norm_num)
theorem B2894147 : Blo 1927435 2894147 := bstep (se 1 (by rfl) ⟨2170610, by rfl⟩ : syracuseStep 2894147 = 4341221) B4341221
theorem B1929431 : Blo 1927435 1929431 := bstep (se 1 (by rfl) ⟨1447073, by rfl⟩ : syracuseStep 1929431 = 2894147) B2894147
theorem B4883885 : Blo 1927435 4883885 := bbase (se 3 (by rfl) ⟨915728, by rfl⟩ : syracuseStep 4883885 = 1831457) (by norm_num)
theorem B3255923 : Blo 1927435 3255923 := bstep (se 1 (by rfl) ⟨2441942, by rfl⟩ : syracuseStep 3255923 = 4883885) B4883885
theorem B2170615 : Blo 1927435 2170615 := bstep (se 1 (by rfl) ⟨1627961, by rfl⟩ : syracuseStep 2170615 = 3255923) B3255923
theorem B2894153 : Blo 1927435 2894153 := bstep (se 2 (by rfl) ⟨1085307, by rfl⟩ : syracuseStep 2894153 = 2170615) B2170615
theorem B1929435 : Blo 1927435 1929435 := bstep (se 1 (by rfl) ⟨1447076, by rfl⟩ : syracuseStep 1929435 = 2894153) B2894153
theorem C0 (j : ℕ) (h1 : 481858 ≤ j) (h2 : j ≤ 482358) : Blo 1927435 (4 * j + 3) := by
  interval_cases j
  · exact B1927435
  · exact B1927439
  · exact B1927443
  · exact B1927447
  · exact B1927451
  · exact B1927455
  · exact B1927459
  · exact B1927463
  · exact B1927467
  · exact B1927471
  · exact B1927475
  · exact B1927479
  · exact B1927483
  · exact B1927487
  · exact B1927491
  · exact B1927495
  · exact B1927499
  · exact B1927503
  · exact B1927507
  · exact B1927511
  · exact B1927515
  · exact B1927519
  · exact B1927523
  · exact B1927527
  · exact B1927531
  · exact B1927535
  · exact B1927539
  · exact B1927543
  · exact B1927547
  · exact B1927551
  · exact B1927555
  · exact B1927559
  · exact B1927563
  · exact B1927567
  · exact B1927571
  · exact B1927575
  · exact B1927579
  · exact B1927583
  · exact B1927587
  · exact B1927591
  · exact B1927595
  · exact B1927599
  · exact B1927603
  · exact B1927607
  · exact B1927611
  · exact B1927615
  · exact B1927619
  · exact B1927623
  · exact B1927627
  · exact B1927631
  · exact B1927635
  · exact B1927639
  · exact B1927643
  · exact B1927647
  · exact B1927651
  · exact B1927655
  · exact B1927659
  · exact B1927663
  · exact B1927667
  · exact B1927671
  · exact B1927675
  · exact B1927679
  · exact B1927683
  · exact B1927687
  · exact B1927691
  · exact B1927695
  · exact B1927699
  · exact B1927703
  · exact B1927707
  · exact B1927711
  · exact B1927715
  · exact B1927719
  · exact B1927723
  · exact B1927727
  · exact B1927731
  · exact B1927735
  · exact B1927739
  · exact B1927743
  · exact B1927747
  · exact B1927751
  · exact B1927755
  · exact B1927759
  · exact B1927763
  · exact B1927767
  · exact B1927771
  · exact B1927775
  · exact B1927779
  · exact B1927783
  · exact B1927787
  · exact B1927791
  · exact B1927795
  · exact B1927799
  · exact B1927803
  · exact B1927807
  · exact B1927811
  · exact B1927815
  · exact B1927819
  · exact B1927823
  · exact B1927827
  · exact B1927831
  · exact B1927835
  · exact B1927839
  · exact B1927843
  · exact B1927847
  · exact B1927851
  · exact B1927855
  · exact B1927859
  · exact B1927863
  · exact B1927867
  · exact B1927871
  · exact B1927875
  · exact B1927879
  · exact B1927883
  · exact B1927887
  · exact B1927891
  · exact B1927895
  · exact B1927899
  · exact B1927903
  · exact B1927907
  · exact B1927911
  · exact B1927915
  · exact B1927919
  · exact B1927923
  · exact B1927927
  · exact B1927931
  · exact B1927935
  · exact B1927939
  · exact B1927943
  · exact B1927947
  · exact B1927951
  · exact B1927955
  · exact B1927959
  · exact B1927963
  · exact B1927967
  · exact B1927971
  · exact B1927975
  · exact B1927979
  · exact B1927983
  · exact B1927987
  · exact B1927991
  · exact B1927995
  · exact B1927999
  · exact B1928003
  · exact B1928007
  · exact B1928011
  · exact B1928015
  · exact B1928019
  · exact B1928023
  · exact B1928027
  · exact B1928031
  · exact B1928035
  · exact B1928039
  · exact B1928043
  · exact B1928047
  · exact B1928051
  · exact B1928055
  · exact B1928059
  · exact B1928063
  · exact B1928067
  · exact B1928071
  · exact B1928075
  · exact B1928079
  · exact B1928083
  · exact B1928087
  · exact B1928091
  · exact B1928095
  · exact B1928099
  · exact B1928103
  · exact B1928107
  · exact B1928111
  · exact B1928115
  · exact B1928119
  · exact B1928123
  · exact B1928127
  · exact B1928131
  · exact B1928135
  · exact B1928139
  · exact B1928143
  · exact B1928147
  · exact B1928151
  · exact B1928155
  · exact B1928159
  · exact B1928163
  · exact B1928167
  · exact B1928171
  · exact B1928175
  · exact B1928179
  · exact B1928183
  · exact B1928187
  · exact B1928191
  · exact B1928195
  · exact B1928199
  · exact B1928203
  · exact B1928207
  · exact B1928211
  · exact B1928215
  · exact B1928219
  · exact B1928223
  · exact B1928227
  · exact B1928231
  · exact B1928235
  · exact B1928239
  · exact B1928243
  · exact B1928247
  · exact B1928251
  · exact B1928255
  · exact B1928259
  · exact B1928263
  · exact B1928267
  · exact B1928271
  · exact B1928275
  · exact B1928279
  · exact B1928283
  · exact B1928287
  · exact B1928291
  · exact B1928295
  · exact B1928299
  · exact B1928303
  · exact B1928307
  · exact B1928311
  · exact B1928315
  · exact B1928319
  · exact B1928323
  · exact B1928327
  · exact B1928331
  · exact B1928335
  · exact B1928339
  · exact B1928343
  · exact B1928347
  · exact B1928351
  · exact B1928355
  · exact B1928359
  · exact B1928363
  · exact B1928367
  · exact B1928371
  · exact B1928375
  · exact B1928379
  · exact B1928383
  · exact B1928387
  · exact B1928391
  · exact B1928395
  · exact B1928399
  · exact B1928403
  · exact B1928407
  · exact B1928411
  · exact B1928415
  · exact B1928419
  · exact B1928423
  · exact B1928427
  · exact B1928431
  · exact B1928435
  · exact B1928439
  · exact B1928443
  · exact B1928447
  · exact B1928451
  · exact B1928455
  · exact B1928459
  · exact B1928463
  · exact B1928467
  · exact B1928471
  · exact B1928475
  · exact B1928479
  · exact B1928483
  · exact B1928487
  · exact B1928491
  · exact B1928495
  · exact B1928499
  · exact B1928503
  · exact B1928507
  · exact B1928511
  · exact B1928515
  · exact B1928519
  · exact B1928523
  · exact B1928527
  · exact B1928531
  · exact B1928535
  · exact B1928539
  · exact B1928543
  · exact B1928547
  · exact B1928551
  · exact B1928555
  · exact B1928559
  · exact B1928563
  · exact B1928567
  · exact B1928571
  · exact B1928575
  · exact B1928579
  · exact B1928583
  · exact B1928587
  · exact B1928591
  · exact B1928595
  · exact B1928599
  · exact B1928603
  · exact B1928607
  · exact B1928611
  · exact B1928615
  · exact B1928619
  · exact B1928623
  · exact B1928627
  · exact B1928631
  · exact B1928635
  · exact B1928639
  · exact B1928643
  · exact B1928647
  · exact B1928651
  · exact B1928655
  · exact B1928659
  · exact B1928663
  · exact B1928667
  · exact B1928671
  · exact B1928675
  · exact B1928679
  · exact B1928683
  · exact B1928687
  · exact B1928691
  · exact B1928695
  · exact B1928699
  · exact B1928703
  · exact B1928707
  · exact B1928711
  · exact B1928715
  · exact B1928719
  · exact B1928723
  · exact B1928727
  · exact B1928731
  · exact B1928735
  · exact B1928739
  · exact B1928743
  · exact B1928747
  · exact B1928751
  · exact B1928755
  · exact B1928759
  · exact B1928763
  · exact B1928767
  · exact B1928771
  · exact B1928775
  · exact B1928779
  · exact B1928783
  · exact B1928787
  · exact B1928791
  · exact B1928795
  · exact B1928799
  · exact B1928803
  · exact B1928807
  · exact B1928811
  · exact B1928815
  · exact B1928819
  · exact B1928823
  · exact B1928827
  · exact B1928831
  · exact B1928835
  · exact B1928839
  · exact B1928843
  · exact B1928847
  · exact B1928851
  · exact B1928855
  · exact B1928859
  · exact B1928863
  · exact B1928867
  · exact B1928871
  · exact B1928875
  · exact B1928879
  · exact B1928883
  · exact B1928887
  · exact B1928891
  · exact B1928895
  · exact B1928899
  · exact B1928903
  · exact B1928907
  · exact B1928911
  · exact B1928915
  · exact B1928919
  · exact B1928923
  · exact B1928927
  · exact B1928931
  · exact B1928935
  · exact B1928939
  · exact B1928943
  · exact B1928947
  · exact B1928951
  · exact B1928955
  · exact B1928959
  · exact B1928963
  · exact B1928967
  · exact B1928971
  · exact B1928975
  · exact B1928979
  · exact B1928983
  · exact B1928987
  · exact B1928991
  · exact B1928995
  · exact B1928999
  · exact B1929003
  · exact B1929007
  · exact B1929011
  · exact B1929015
  · exact B1929019
  · exact B1929023
  · exact B1929027
  · exact B1929031
  · exact B1929035
  · exact B1929039
  · exact B1929043
  · exact B1929047
  · exact B1929051
  · exact B1929055
  · exact B1929059
  · exact B1929063
  · exact B1929067
  · exact B1929071
  · exact B1929075
  · exact B1929079
  · exact B1929083
  · exact B1929087
  · exact B1929091
  · exact B1929095
  · exact B1929099
  · exact B1929103
  · exact B1929107
  · exact B1929111
  · exact B1929115
  · exact B1929119
  · exact B1929123
  · exact B1929127
  · exact B1929131
  · exact B1929135
  · exact B1929139
  · exact B1929143
  · exact B1929147
  · exact B1929151
  · exact B1929155
  · exact B1929159
  · exact B1929163
  · exact B1929167
  · exact B1929171
  · exact B1929175
  · exact B1929179
  · exact B1929183
  · exact B1929187
  · exact B1929191
  · exact B1929195
  · exact B1929199
  · exact B1929203
  · exact B1929207
  · exact B1929211
  · exact B1929215
  · exact B1929219
  · exact B1929223
  · exact B1929227
  · exact B1929231
  · exact B1929235
  · exact B1929239
  · exact B1929243
  · exact B1929247
  · exact B1929251
  · exact B1929255
  · exact B1929259
  · exact B1929263
  · exact B1929267
  · exact B1929271
  · exact B1929275
  · exact B1929279
  · exact B1929283
  · exact B1929287
  · exact B1929291
  · exact B1929295
  · exact B1929299
  · exact B1929303
  · exact B1929307
  · exact B1929311
  · exact B1929315
  · exact B1929319
  · exact B1929323
  · exact B1929327
  · exact B1929331
  · exact B1929335
  · exact B1929339
  · exact B1929343
  · exact B1929347
  · exact B1929351
  · exact B1929355
  · exact B1929359
  · exact B1929363
  · exact B1929367
  · exact B1929371
  · exact B1929375
  · exact B1929379
  · exact B1929383
  · exact B1929387
  · exact B1929391
  · exact B1929395
  · exact B1929399
  · exact B1929403
  · exact B1929407
  · exact B1929411
  · exact B1929415
  · exact B1929419
  · exact B1929423
  · exact B1929427
  · exact B1929431
  · exact B1929435
theorem solution (m : ℕ) (hlo : 1927435 ≤ m) (hhi : m ≤ 1929435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 481858 ≤ j := by omega
    have hj2 : j ≤ 482358 := by omega
    have hb : Blo 1927435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
