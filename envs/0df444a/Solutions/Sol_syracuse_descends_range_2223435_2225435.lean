-- Prove2me | solution 1 for syracuse_descends_range_2223435_2225435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:41.998272+00:00
-- url     : https://prove2.me/submissions/8dd0730c-310c-4c20-8e9a-b16c2f5c65d2

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

theorem B2501365 : Blo 2223435 2501365 := bbase (se 5 (by rfl) ⟨117251, by rfl⟩ : syracuseStep 2501365 = 234503) (by norm_num)
theorem B3335153 : Blo 2223435 3335153 := bstep (se 2 (by rfl) ⟨1250682, by rfl⟩ : syracuseStep 3335153 = 2501365) B2501365
theorem B2223435 : Blo 2223435 2223435 := bstep (se 1 (by rfl) ⟨1667576, by rfl⟩ : syracuseStep 2223435 = 3335153) B3335153
theorem B2814041 : Blo 2223435 2814041 := bbase (se 2 (by rfl) ⟨1055265, by rfl⟩ : syracuseStep 2814041 = 2110531) (by norm_num)
theorem B7504109 : Blo 2223435 7504109 := bstep (se 3 (by rfl) ⟨1407020, by rfl⟩ : syracuseStep 7504109 = 2814041) B2814041
theorem B5002739 : Blo 2223435 5002739 := bstep (se 1 (by rfl) ⟨3752054, by rfl⟩ : syracuseStep 5002739 = 7504109) B7504109
theorem B3335159 : Blo 2223435 3335159 := bstep (se 1 (by rfl) ⟨2501369, by rfl⟩ : syracuseStep 3335159 = 5002739) B5002739
theorem B2223439 : Blo 2223435 2223439 := bstep (se 1 (by rfl) ⟨1667579, by rfl⟩ : syracuseStep 2223439 = 3335159) B3335159
theorem B3335165 : Blo 2223435 3335165 := bbase (se 3 (by rfl) ⟨625343, by rfl⟩ : syracuseStep 3335165 = 1250687) (by norm_num)
theorem B2223443 : Blo 2223435 2223443 := bstep (se 1 (by rfl) ⟨1667582, by rfl⟩ : syracuseStep 2223443 = 3335165) B3335165
theorem B5002757 : Blo 2223435 5002757 := bbase (se 4 (by rfl) ⟨469008, by rfl⟩ : syracuseStep 5002757 = 938017) (by norm_num)
theorem B3335171 : Blo 2223435 3335171 := bstep (se 1 (by rfl) ⟨2501378, by rfl⟩ : syracuseStep 3335171 = 5002757) B5002757
theorem B2223447 : Blo 2223435 2223447 := bstep (se 1 (by rfl) ⟨1667585, by rfl⟩ : syracuseStep 2223447 = 3335171) B3335171
theorem B4221085 : Blo 2223435 4221085 := bbase (se 3 (by rfl) ⟨791453, by rfl⟩ : syracuseStep 4221085 = 1582907) (by norm_num)
theorem B5628113 : Blo 2223435 5628113 := bstep (se 2 (by rfl) ⟨2110542, by rfl⟩ : syracuseStep 5628113 = 4221085) B4221085
theorem B3752075 : Blo 2223435 3752075 := bstep (se 1 (by rfl) ⟨2814056, by rfl⟩ : syracuseStep 3752075 = 5628113) B5628113
theorem B2501383 : Blo 2223435 2501383 := bstep (se 1 (by rfl) ⟨1876037, by rfl⟩ : syracuseStep 2501383 = 3752075) B3752075
theorem B3335177 : Blo 2223435 3335177 := bstep (se 2 (by rfl) ⟨1250691, by rfl⟩ : syracuseStep 3335177 = 2501383) B2501383
theorem B2223451 : Blo 2223435 2223451 := bstep (se 1 (by rfl) ⟨1667588, by rfl⟩ : syracuseStep 2223451 = 3335177) B3335177
theorem B11256245 : Blo 2223435 11256245 := bbase (se 5 (by rfl) ⟨527636, by rfl⟩ : syracuseStep 11256245 = 1055273) (by norm_num)
theorem B7504163 : Blo 2223435 7504163 := bstep (se 1 (by rfl) ⟨5628122, by rfl⟩ : syracuseStep 7504163 = 11256245) B11256245
theorem B5002775 : Blo 2223435 5002775 := bstep (se 1 (by rfl) ⟨3752081, by rfl⟩ : syracuseStep 5002775 = 7504163) B7504163
theorem B3335183 : Blo 2223435 3335183 := bstep (se 1 (by rfl) ⟨2501387, by rfl⟩ : syracuseStep 3335183 = 5002775) B5002775
theorem B2223455 : Blo 2223435 2223455 := bstep (se 1 (by rfl) ⟨1667591, by rfl⟩ : syracuseStep 2223455 = 3335183) B3335183
theorem B3335189 : Blo 2223435 3335189 := bbase (se 6 (by rfl) ⟨78168, by rfl⟩ : syracuseStep 3335189 = 156337) (by norm_num)
theorem B2223459 : Blo 2223435 2223459 := bstep (se 1 (by rfl) ⟨1667594, by rfl⟩ : syracuseStep 2223459 = 3335189) B3335189
theorem B8557397 : Blo 2223435 8557397 := bbase (se 9 (by rfl) ⟨25070, by rfl⟩ : syracuseStep 8557397 = 50141) (by norm_num)
theorem B5704931 : Blo 2223435 5704931 := bstep (se 1 (by rfl) ⟨4278698, by rfl⟩ : syracuseStep 5704931 = 8557397) B8557397
theorem B15213149 : Blo 2223435 15213149 := bstep (se 3 (by rfl) ⟨2852465, by rfl⟩ : syracuseStep 15213149 = 5704931) B5704931
theorem B10142099 : Blo 2223435 10142099 := bstep (se 1 (by rfl) ⟨7606574, by rfl⟩ : syracuseStep 10142099 = 15213149) B15213149
theorem B6761399 : Blo 2223435 6761399 := bstep (se 1 (by rfl) ⟨5071049, by rfl⟩ : syracuseStep 6761399 = 10142099) B10142099
theorem B72121589 : Blo 2223435 72121589 := bstep (se 5 (by rfl) ⟨3380699, by rfl⟩ : syracuseStep 72121589 = 6761399) B6761399
theorem B48081059 : Blo 2223435 48081059 := bstep (se 1 (by rfl) ⟨36060794, by rfl⟩ : syracuseStep 48081059 = 72121589) B72121589
theorem B32054039 : Blo 2223435 32054039 := bstep (se 1 (by rfl) ⟨24040529, by rfl⟩ : syracuseStep 32054039 = 48081059) B48081059
theorem B21369359 : Blo 2223435 21369359 := bstep (se 1 (by rfl) ⟨16027019, by rfl⟩ : syracuseStep 21369359 = 32054039) B32054039
theorem B14246239 : Blo 2223435 14246239 := bstep (se 1 (by rfl) ⟨10684679, by rfl⟩ : syracuseStep 14246239 = 21369359) B21369359
theorem B18994985 : Blo 2223435 18994985 := bstep (se 2 (by rfl) ⟨7123119, by rfl⟩ : syracuseStep 18994985 = 14246239) B14246239
theorem B12663323 : Blo 2223435 12663323 := bstep (se 1 (by rfl) ⟨9497492, by rfl⟩ : syracuseStep 12663323 = 18994985) B18994985
theorem B8442215 : Blo 2223435 8442215 := bstep (se 1 (by rfl) ⟨6331661, by rfl⟩ : syracuseStep 8442215 = 12663323) B12663323
theorem B5628143 : Blo 2223435 5628143 := bstep (se 1 (by rfl) ⟨4221107, by rfl⟩ : syracuseStep 5628143 = 8442215) B8442215
theorem B3752095 : Blo 2223435 3752095 := bstep (se 1 (by rfl) ⟨2814071, by rfl⟩ : syracuseStep 3752095 = 5628143) B5628143
theorem B5002793 : Blo 2223435 5002793 := bstep (se 2 (by rfl) ⟨1876047, by rfl⟩ : syracuseStep 5002793 = 3752095) B3752095
theorem B3335195 : Blo 2223435 3335195 := bstep (se 1 (by rfl) ⟨2501396, by rfl⟩ : syracuseStep 3335195 = 5002793) B5002793
theorem B2223463 : Blo 2223435 2223463 := bstep (se 1 (by rfl) ⟨1667597, by rfl⟩ : syracuseStep 2223463 = 3335195) B3335195
theorem B2501401 : Blo 2223435 2501401 := bbase (se 2 (by rfl) ⟨938025, by rfl⟩ : syracuseStep 2501401 = 1876051) (by norm_num)
theorem B3335201 : Blo 2223435 3335201 := bstep (se 2 (by rfl) ⟨1250700, by rfl⟩ : syracuseStep 3335201 = 2501401) B2501401
theorem B2223467 : Blo 2223435 2223467 := bstep (se 1 (by rfl) ⟨1667600, by rfl⟩ : syracuseStep 2223467 = 3335201) B3335201
theorem B8442245 : Blo 2223435 8442245 := bbase (se 4 (by rfl) ⟨791460, by rfl⟩ : syracuseStep 8442245 = 1582921) (by norm_num)
theorem B5628163 : Blo 2223435 5628163 := bstep (se 1 (by rfl) ⟨4221122, by rfl⟩ : syracuseStep 5628163 = 8442245) B8442245
theorem B7504217 : Blo 2223435 7504217 := bstep (se 2 (by rfl) ⟨2814081, by rfl⟩ : syracuseStep 7504217 = 5628163) B5628163
theorem B5002811 : Blo 2223435 5002811 := bstep (se 1 (by rfl) ⟨3752108, by rfl⟩ : syracuseStep 5002811 = 7504217) B7504217
theorem B3335207 : Blo 2223435 3335207 := bstep (se 1 (by rfl) ⟨2501405, by rfl⟩ : syracuseStep 3335207 = 5002811) B5002811
theorem B2223471 : Blo 2223435 2223471 := bstep (se 1 (by rfl) ⟨1667603, by rfl⟩ : syracuseStep 2223471 = 3335207) B3335207
theorem B3335213 : Blo 2223435 3335213 := bbase (se 3 (by rfl) ⟨625352, by rfl⟩ : syracuseStep 3335213 = 1250705) (by norm_num)
theorem B2223475 : Blo 2223435 2223475 := bstep (se 1 (by rfl) ⟨1667606, by rfl⟩ : syracuseStep 2223475 = 3335213) B3335213
theorem B5002829 : Blo 2223435 5002829 := bbase (se 3 (by rfl) ⟨938030, by rfl⟩ : syracuseStep 5002829 = 1876061) (by norm_num)
theorem B3335219 : Blo 2223435 3335219 := bstep (se 1 (by rfl) ⟨2501414, by rfl⟩ : syracuseStep 3335219 = 5002829) B5002829
theorem B2223479 : Blo 2223435 2223479 := bstep (se 1 (by rfl) ⟨1667609, by rfl⟩ : syracuseStep 2223479 = 3335219) B3335219
theorem B2814097 : Blo 2223435 2814097 := bbase (se 2 (by rfl) ⟨1055286, by rfl⟩ : syracuseStep 2814097 = 2110573) (by norm_num)
theorem B3752129 : Blo 2223435 3752129 := bstep (se 2 (by rfl) ⟨1407048, by rfl⟩ : syracuseStep 3752129 = 2814097) B2814097
theorem B2501419 : Blo 2223435 2501419 := bstep (se 1 (by rfl) ⟨1876064, by rfl⟩ : syracuseStep 2501419 = 3752129) B3752129
theorem B3335225 : Blo 2223435 3335225 := bstep (se 2 (by rfl) ⟨1250709, by rfl⟩ : syracuseStep 3335225 = 2501419) B2501419
theorem B2223483 : Blo 2223435 2223483 := bstep (se 1 (by rfl) ⟨1667612, by rfl⟩ : syracuseStep 2223483 = 3335225) B3335225
theorem B4748797 : Blo 2223435 4748797 := bbase (se 3 (by rfl) ⟨890399, by rfl⟩ : syracuseStep 4748797 = 1780799) (by norm_num)
theorem B25326917 : Blo 2223435 25326917 := bstep (se 4 (by rfl) ⟨2374398, by rfl⟩ : syracuseStep 25326917 = 4748797) B4748797
theorem B16884611 : Blo 2223435 16884611 := bstep (se 1 (by rfl) ⟨12663458, by rfl⟩ : syracuseStep 16884611 = 25326917) B25326917
theorem B11256407 : Blo 2223435 11256407 := bstep (se 1 (by rfl) ⟨8442305, by rfl⟩ : syracuseStep 11256407 = 16884611) B16884611
theorem B7504271 : Blo 2223435 7504271 := bstep (se 1 (by rfl) ⟨5628203, by rfl⟩ : syracuseStep 7504271 = 11256407) B11256407
theorem B5002847 : Blo 2223435 5002847 := bstep (se 1 (by rfl) ⟨3752135, by rfl⟩ : syracuseStep 5002847 = 7504271) B7504271
theorem B3335231 : Blo 2223435 3335231 := bstep (se 1 (by rfl) ⟨2501423, by rfl⟩ : syracuseStep 3335231 = 5002847) B5002847
theorem B2223487 : Blo 2223435 2223487 := bstep (se 1 (by rfl) ⟨1667615, by rfl⟩ : syracuseStep 2223487 = 3335231) B3335231
theorem B3335237 : Blo 2223435 3335237 := bbase (se 4 (by rfl) ⟨312678, by rfl⟩ : syracuseStep 3335237 = 625357) (by norm_num)
theorem B2223491 : Blo 2223435 2223491 := bstep (se 1 (by rfl) ⟨1667618, by rfl⟩ : syracuseStep 2223491 = 3335237) B3335237
theorem B3752149 : Blo 2223435 3752149 := bbase (se 7 (by rfl) ⟨43970, by rfl⟩ : syracuseStep 3752149 = 87941) (by norm_num)
theorem B5002865 : Blo 2223435 5002865 := bstep (se 2 (by rfl) ⟨1876074, by rfl⟩ : syracuseStep 5002865 = 3752149) B3752149
theorem B3335243 : Blo 2223435 3335243 := bstep (se 1 (by rfl) ⟨2501432, by rfl⟩ : syracuseStep 3335243 = 5002865) B5002865
theorem B2223495 : Blo 2223435 2223495 := bstep (se 1 (by rfl) ⟨1667621, by rfl⟩ : syracuseStep 2223495 = 3335243) B3335243
theorem B2501437 : Blo 2223435 2501437 := bbase (se 3 (by rfl) ⟨469019, by rfl⟩ : syracuseStep 2501437 = 938039) (by norm_num)
theorem B3335249 : Blo 2223435 3335249 := bstep (se 2 (by rfl) ⟨1250718, by rfl⟩ : syracuseStep 3335249 = 2501437) B2501437
theorem B2223499 : Blo 2223435 2223499 := bstep (se 1 (by rfl) ⟨1667624, by rfl⟩ : syracuseStep 2223499 = 3335249) B3335249
theorem B7504325 : Blo 2223435 7504325 := bbase (se 4 (by rfl) ⟨703530, by rfl⟩ : syracuseStep 7504325 = 1407061) (by norm_num)
theorem B5002883 : Blo 2223435 5002883 := bstep (se 1 (by rfl) ⟨3752162, by rfl⟩ : syracuseStep 5002883 = 7504325) B7504325
theorem B3335255 : Blo 2223435 3335255 := bstep (se 1 (by rfl) ⟨2501441, by rfl⟩ : syracuseStep 3335255 = 5002883) B5002883
theorem B2223503 : Blo 2223435 2223503 := bstep (se 1 (by rfl) ⟨1667627, by rfl⟩ : syracuseStep 2223503 = 3335255) B3335255
theorem B3335261 : Blo 2223435 3335261 := bbase (se 3 (by rfl) ⟨625361, by rfl⟩ : syracuseStep 3335261 = 1250723) (by norm_num)
theorem B2223507 : Blo 2223435 2223507 := bstep (se 1 (by rfl) ⟨1667630, by rfl⟩ : syracuseStep 2223507 = 3335261) B3335261
theorem B5002901 : Blo 2223435 5002901 := bbase (se 6 (by rfl) ⟨117255, by rfl⟩ : syracuseStep 5002901 = 234511) (by norm_num)
theorem B3335267 : Blo 2223435 3335267 := bstep (se 1 (by rfl) ⟨2501450, by rfl⟩ : syracuseStep 3335267 = 5002901) B5002901
theorem B2223511 : Blo 2223435 2223511 := bstep (se 1 (by rfl) ⟨1667633, by rfl⟩ : syracuseStep 2223511 = 3335267) B3335267
theorem B2374429 : Blo 2223435 2374429 := bbase (se 3 (by rfl) ⟨445205, by rfl⟩ : syracuseStep 2374429 = 890411) (by norm_num)
theorem B3165905 : Blo 2223435 3165905 := bstep (se 2 (by rfl) ⟨1187214, by rfl⟩ : syracuseStep 3165905 = 2374429) B2374429
theorem B8442413 : Blo 2223435 8442413 := bstep (se 3 (by rfl) ⟨1582952, by rfl⟩ : syracuseStep 8442413 = 3165905) B3165905
theorem B5628275 : Blo 2223435 5628275 := bstep (se 1 (by rfl) ⟨4221206, by rfl⟩ : syracuseStep 5628275 = 8442413) B8442413
theorem B3752183 : Blo 2223435 3752183 := bstep (se 1 (by rfl) ⟨2814137, by rfl⟩ : syracuseStep 3752183 = 5628275) B5628275
theorem B2501455 : Blo 2223435 2501455 := bstep (se 1 (by rfl) ⟨1876091, by rfl⟩ : syracuseStep 2501455 = 3752183) B3752183
theorem B3335273 : Blo 2223435 3335273 := bstep (se 2 (by rfl) ⟨1250727, by rfl⟩ : syracuseStep 3335273 = 2501455) B2501455
theorem B2223515 : Blo 2223435 2223515 := bstep (se 1 (by rfl) ⟨1667636, by rfl⟩ : syracuseStep 2223515 = 3335273) B3335273
theorem B2671237 : Blo 2223435 2671237 := bbase (se 4 (by rfl) ⟨250428, by rfl⟩ : syracuseStep 2671237 = 500857) (by norm_num)
theorem B14246597 : Blo 2223435 14246597 := bstep (se 4 (by rfl) ⟨1335618, by rfl⟩ : syracuseStep 14246597 = 2671237) B2671237
theorem B9497731 : Blo 2223435 9497731 := bstep (se 1 (by rfl) ⟨7123298, by rfl⟩ : syracuseStep 9497731 = 14246597) B14246597
theorem B12663641 : Blo 2223435 12663641 := bstep (se 2 (by rfl) ⟨4748865, by rfl⟩ : syracuseStep 12663641 = 9497731) B9497731
theorem B8442427 : Blo 2223435 8442427 := bstep (se 1 (by rfl) ⟨6331820, by rfl⟩ : syracuseStep 8442427 = 12663641) B12663641
theorem B11256569 : Blo 2223435 11256569 := bstep (se 2 (by rfl) ⟨4221213, by rfl⟩ : syracuseStep 11256569 = 8442427) B8442427
theorem B7504379 : Blo 2223435 7504379 := bstep (se 1 (by rfl) ⟨5628284, by rfl⟩ : syracuseStep 7504379 = 11256569) B11256569
theorem B5002919 : Blo 2223435 5002919 := bstep (se 1 (by rfl) ⟨3752189, by rfl⟩ : syracuseStep 5002919 = 7504379) B7504379
theorem B3335279 : Blo 2223435 3335279 := bstep (se 1 (by rfl) ⟨2501459, by rfl⟩ : syracuseStep 3335279 = 5002919) B5002919
theorem B2223519 : Blo 2223435 2223519 := bstep (se 1 (by rfl) ⟨1667639, by rfl⟩ : syracuseStep 2223519 = 3335279) B3335279
theorem B3335285 : Blo 2223435 3335285 := bbase (se 5 (by rfl) ⟨156341, by rfl⟩ : syracuseStep 3335285 = 312683) (by norm_num)
theorem B2223523 : Blo 2223435 2223523 := bstep (se 1 (by rfl) ⟨1667642, by rfl⟩ : syracuseStep 2223523 = 3335285) B3335285
theorem B4221229 : Blo 2223435 4221229 := bbase (se 3 (by rfl) ⟨791480, by rfl⟩ : syracuseStep 4221229 = 1582961) (by norm_num)
theorem B5628305 : Blo 2223435 5628305 := bstep (se 2 (by rfl) ⟨2110614, by rfl⟩ : syracuseStep 5628305 = 4221229) B4221229
theorem B3752203 : Blo 2223435 3752203 := bstep (se 1 (by rfl) ⟨2814152, by rfl⟩ : syracuseStep 3752203 = 5628305) B5628305
theorem B5002937 : Blo 2223435 5002937 := bstep (se 2 (by rfl) ⟨1876101, by rfl⟩ : syracuseStep 5002937 = 3752203) B3752203
theorem B3335291 : Blo 2223435 3335291 := bstep (se 1 (by rfl) ⟨2501468, by rfl⟩ : syracuseStep 3335291 = 5002937) B5002937
theorem B2223527 : Blo 2223435 2223527 := bstep (se 1 (by rfl) ⟨1667645, by rfl⟩ : syracuseStep 2223527 = 3335291) B3335291
theorem B2501473 : Blo 2223435 2501473 := bbase (se 2 (by rfl) ⟨938052, by rfl⟩ : syracuseStep 2501473 = 1876105) (by norm_num)
theorem B3335297 : Blo 2223435 3335297 := bstep (se 2 (by rfl) ⟨1250736, by rfl⟩ : syracuseStep 3335297 = 2501473) B2501473
theorem B2223531 : Blo 2223435 2223531 := bstep (se 1 (by rfl) ⟨1667648, by rfl⟩ : syracuseStep 2223531 = 3335297) B3335297
theorem B5628325 : Blo 2223435 5628325 := bbase (se 4 (by rfl) ⟨527655, by rfl⟩ : syracuseStep 5628325 = 1055311) (by norm_num)
theorem B7504433 : Blo 2223435 7504433 := bstep (se 2 (by rfl) ⟨2814162, by rfl⟩ : syracuseStep 7504433 = 5628325) B5628325
theorem B5002955 : Blo 2223435 5002955 := bstep (se 1 (by rfl) ⟨3752216, by rfl⟩ : syracuseStep 5002955 = 7504433) B7504433
theorem B3335303 : Blo 2223435 3335303 := bstep (se 1 (by rfl) ⟨2501477, by rfl⟩ : syracuseStep 3335303 = 5002955) B5002955
theorem B2223535 : Blo 2223435 2223535 := bstep (se 1 (by rfl) ⟨1667651, by rfl⟩ : syracuseStep 2223535 = 3335303) B3335303
theorem B3335309 : Blo 2223435 3335309 := bbase (se 3 (by rfl) ⟨625370, by rfl⟩ : syracuseStep 3335309 = 1250741) (by norm_num)
theorem B2223539 : Blo 2223435 2223539 := bstep (se 1 (by rfl) ⟨1667654, by rfl⟩ : syracuseStep 2223539 = 3335309) B3335309
theorem B5002973 : Blo 2223435 5002973 := bbase (se 3 (by rfl) ⟨938057, by rfl⟩ : syracuseStep 5002973 = 1876115) (by norm_num)
theorem B3335315 : Blo 2223435 3335315 := bstep (se 1 (by rfl) ⟨2501486, by rfl⟩ : syracuseStep 3335315 = 5002973) B5002973
theorem B2223543 : Blo 2223435 2223543 := bstep (se 1 (by rfl) ⟨1667657, by rfl⟩ : syracuseStep 2223543 = 3335315) B3335315
theorem B3752237 : Blo 2223435 3752237 := bbase (se 3 (by rfl) ⟨703544, by rfl⟩ : syracuseStep 3752237 = 1407089) (by norm_num)
theorem B2501491 : Blo 2223435 2501491 := bstep (se 1 (by rfl) ⟨1876118, by rfl⟩ : syracuseStep 2501491 = 3752237) B3752237
theorem B3335321 : Blo 2223435 3335321 := bstep (se 2 (by rfl) ⟨1250745, by rfl⟩ : syracuseStep 3335321 = 2501491) B2501491
theorem B2223547 : Blo 2223435 2223547 := bstep (se 1 (by rfl) ⟨1667660, by rfl⟩ : syracuseStep 2223547 = 3335321) B3335321
theorem B2253889 : Blo 2223435 2253889 := bbase (se 2 (by rfl) ⟨845208, by rfl⟩ : syracuseStep 2253889 = 1690417) (by norm_num)
theorem B3005185 : Blo 2223435 3005185 := bstep (se 2 (by rfl) ⟨1126944, by rfl⟩ : syracuseStep 3005185 = 2253889) B2253889
theorem B4006913 : Blo 2223435 4006913 := bstep (se 2 (by rfl) ⟨1502592, by rfl⟩ : syracuseStep 4006913 = 3005185) B3005185
theorem B42740405 : Blo 2223435 42740405 := bstep (se 5 (by rfl) ⟨2003456, by rfl⟩ : syracuseStep 42740405 = 4006913) B4006913
theorem B28493603 : Blo 2223435 28493603 := bstep (se 1 (by rfl) ⟨21370202, by rfl⟩ : syracuseStep 28493603 = 42740405) B42740405
theorem B18995735 : Blo 2223435 18995735 := bstep (se 1 (by rfl) ⟨14246801, by rfl⟩ : syracuseStep 18995735 = 28493603) B28493603
theorem B12663823 : Blo 2223435 12663823 := bstep (se 1 (by rfl) ⟨9497867, by rfl⟩ : syracuseStep 12663823 = 18995735) B18995735
theorem B16885097 : Blo 2223435 16885097 := bstep (se 2 (by rfl) ⟨6331911, by rfl⟩ : syracuseStep 16885097 = 12663823) B12663823
theorem B11256731 : Blo 2223435 11256731 := bstep (se 1 (by rfl) ⟨8442548, by rfl⟩ : syracuseStep 11256731 = 16885097) B16885097
theorem B7504487 : Blo 2223435 7504487 := bstep (se 1 (by rfl) ⟨5628365, by rfl⟩ : syracuseStep 7504487 = 11256731) B11256731
theorem B5002991 : Blo 2223435 5002991 := bstep (se 1 (by rfl) ⟨3752243, by rfl⟩ : syracuseStep 5002991 = 7504487) B7504487
theorem B3335327 : Blo 2223435 3335327 := bstep (se 1 (by rfl) ⟨2501495, by rfl⟩ : syracuseStep 3335327 = 5002991) B5002991
theorem B2223551 : Blo 2223435 2223551 := bstep (se 1 (by rfl) ⟨1667663, by rfl⟩ : syracuseStep 2223551 = 3335327) B3335327
theorem B3335333 : Blo 2223435 3335333 := bbase (se 4 (by rfl) ⟨312687, by rfl⟩ : syracuseStep 3335333 = 625375) (by norm_num)
theorem B2223555 : Blo 2223435 2223555 := bstep (se 1 (by rfl) ⟨1667666, by rfl⟩ : syracuseStep 2223555 = 3335333) B3335333
theorem B2814193 : Blo 2223435 2814193 := bbase (se 2 (by rfl) ⟨1055322, by rfl⟩ : syracuseStep 2814193 = 2110645) (by norm_num)
theorem B3752257 : Blo 2223435 3752257 := bstep (se 2 (by rfl) ⟨1407096, by rfl⟩ : syracuseStep 3752257 = 2814193) B2814193
theorem B5003009 : Blo 2223435 5003009 := bstep (se 2 (by rfl) ⟨1876128, by rfl⟩ : syracuseStep 5003009 = 3752257) B3752257
theorem B3335339 : Blo 2223435 3335339 := bstep (se 1 (by rfl) ⟨2501504, by rfl⟩ : syracuseStep 3335339 = 5003009) B5003009
theorem B2223559 : Blo 2223435 2223559 := bstep (se 1 (by rfl) ⟨1667669, by rfl⟩ : syracuseStep 2223559 = 3335339) B3335339
theorem B2501509 : Blo 2223435 2501509 := bbase (se 4 (by rfl) ⟨234516, by rfl⟩ : syracuseStep 2501509 = 469033) (by norm_num)
theorem B3335345 : Blo 2223435 3335345 := bstep (se 2 (by rfl) ⟨1250754, by rfl⟩ : syracuseStep 3335345 = 2501509) B2501509
theorem B2223563 : Blo 2223435 2223563 := bstep (se 1 (by rfl) ⟨1667672, by rfl⟩ : syracuseStep 2223563 = 3335345) B3335345
theorem B66771157 : Blo 2223435 66771157 := bbase (se 7 (by rfl) ⟨782474, by rfl⟩ : syracuseStep 66771157 = 1564949) (by norm_num)
theorem B89028209 : Blo 2223435 89028209 := bstep (se 2 (by rfl) ⟨33385578, by rfl⟩ : syracuseStep 89028209 = 66771157) B66771157
theorem B59352139 : Blo 2223435 59352139 := bstep (se 1 (by rfl) ⟨44514104, by rfl⟩ : syracuseStep 59352139 = 89028209) B89028209
theorem B79136185 : Blo 2223435 79136185 := bstep (se 2 (by rfl) ⟨29676069, by rfl⟩ : syracuseStep 79136185 = 59352139) B59352139
theorem B105514913 : Blo 2223435 105514913 := bstep (se 2 (by rfl) ⟨39568092, by rfl⟩ : syracuseStep 105514913 = 79136185) B79136185
theorem B281373101 : Blo 2223435 281373101 := bstep (se 3 (by rfl) ⟨52757456, by rfl⟩ : syracuseStep 281373101 = 105514913) B105514913
theorem B187582067 : Blo 2223435 187582067 := bstep (se 1 (by rfl) ⟨140686550, by rfl⟩ : syracuseStep 187582067 = 281373101) B281373101
theorem B125054711 : Blo 2223435 125054711 := bstep (se 1 (by rfl) ⟨93791033, by rfl⟩ : syracuseStep 125054711 = 187582067) B187582067
theorem B83369807 : Blo 2223435 83369807 := bstep (se 1 (by rfl) ⟨62527355, by rfl⟩ : syracuseStep 83369807 = 125054711) B125054711
theorem B55579871 : Blo 2223435 55579871 := bstep (se 1 (by rfl) ⟨41684903, by rfl⟩ : syracuseStep 55579871 = 83369807) B83369807
theorem B37053247 : Blo 2223435 37053247 := bstep (se 1 (by rfl) ⟨27789935, by rfl⟩ : syracuseStep 37053247 = 55579871) B55579871
theorem B49404329 : Blo 2223435 49404329 := bstep (se 2 (by rfl) ⟨18526623, by rfl⟩ : syracuseStep 49404329 = 37053247) B37053247
theorem B32936219 : Blo 2223435 32936219 := bstep (se 1 (by rfl) ⟨24702164, by rfl⟩ : syracuseStep 32936219 = 49404329) B49404329
theorem B21957479 : Blo 2223435 21957479 := bstep (se 1 (by rfl) ⟨16468109, by rfl⟩ : syracuseStep 21957479 = 32936219) B32936219
theorem B14638319 : Blo 2223435 14638319 := bstep (se 1 (by rfl) ⟨10978739, by rfl⟩ : syracuseStep 14638319 = 21957479) B21957479
theorem B9758879 : Blo 2223435 9758879 := bstep (se 1 (by rfl) ⟨7319159, by rfl⟩ : syracuseStep 9758879 = 14638319) B14638319
theorem B6505919 : Blo 2223435 6505919 := bstep (se 1 (by rfl) ⟨4879439, by rfl⟩ : syracuseStep 6505919 = 9758879) B9758879
theorem B4337279 : Blo 2223435 4337279 := bstep (se 1 (by rfl) ⟨3252959, by rfl⟩ : syracuseStep 4337279 = 6505919) B6505919
theorem B2891519 : Blo 2223435 2891519 := bstep (se 1 (by rfl) ⟨2168639, by rfl⟩ : syracuseStep 2891519 = 4337279) B4337279
theorem B30842869 : Blo 2223435 30842869 := bstep (se 5 (by rfl) ⟨1445759, by rfl⟩ : syracuseStep 30842869 = 2891519) B2891519
theorem B41123825 : Blo 2223435 41123825 := bstep (se 2 (by rfl) ⟨15421434, by rfl⟩ : syracuseStep 41123825 = 30842869) B30842869
theorem B27415883 : Blo 2223435 27415883 := bstep (se 1 (by rfl) ⟨20561912, by rfl⟩ : syracuseStep 27415883 = 41123825) B41123825
theorem B18277255 : Blo 2223435 18277255 := bstep (se 1 (by rfl) ⟨13707941, by rfl⟩ : syracuseStep 18277255 = 27415883) B27415883
theorem B24369673 : Blo 2223435 24369673 := bstep (se 2 (by rfl) ⟨9138627, by rfl⟩ : syracuseStep 24369673 = 18277255) B18277255
theorem B32492897 : Blo 2223435 32492897 := bstep (se 2 (by rfl) ⟨12184836, by rfl⟩ : syracuseStep 32492897 = 24369673) B24369673
theorem B21661931 : Blo 2223435 21661931 := bstep (se 1 (by rfl) ⟨16246448, by rfl⟩ : syracuseStep 21661931 = 32492897) B32492897
theorem B57765149 : Blo 2223435 57765149 := bstep (se 3 (by rfl) ⟨10830965, by rfl⟩ : syracuseStep 57765149 = 21661931) B21661931
theorem B38510099 : Blo 2223435 38510099 := bstep (se 1 (by rfl) ⟨28882574, by rfl⟩ : syracuseStep 38510099 = 57765149) B57765149
theorem B25673399 : Blo 2223435 25673399 := bstep (se 1 (by rfl) ⟨19255049, by rfl⟩ : syracuseStep 25673399 = 38510099) B38510099
theorem B17115599 : Blo 2223435 17115599 := bstep (se 1 (by rfl) ⟨12836699, by rfl⟩ : syracuseStep 17115599 = 25673399) B25673399
theorem B11410399 : Blo 2223435 11410399 := bstep (se 1 (by rfl) ⟨8557799, by rfl⟩ : syracuseStep 11410399 = 17115599) B17115599
theorem B60855461 : Blo 2223435 60855461 := bstep (se 4 (by rfl) ⟨5705199, by rfl⟩ : syracuseStep 60855461 = 11410399) B11410399
theorem B40570307 : Blo 2223435 40570307 := bstep (se 1 (by rfl) ⟨30427730, by rfl⟩ : syracuseStep 40570307 = 60855461) B60855461
theorem B27046871 : Blo 2223435 27046871 := bstep (se 1 (by rfl) ⟨20285153, by rfl⟩ : syracuseStep 27046871 = 40570307) B40570307
theorem B18031247 : Blo 2223435 18031247 := bstep (se 1 (by rfl) ⟨13523435, by rfl⟩ : syracuseStep 18031247 = 27046871) B27046871
theorem B12020831 : Blo 2223435 12020831 := bstep (se 1 (by rfl) ⟨9015623, by rfl⟩ : syracuseStep 12020831 = 18031247) B18031247
theorem B8013887 : Blo 2223435 8013887 := bstep (se 1 (by rfl) ⟨6010415, by rfl⟩ : syracuseStep 8013887 = 12020831) B12020831
theorem B5342591 : Blo 2223435 5342591 := bstep (se 1 (by rfl) ⟨4006943, by rfl⟩ : syracuseStep 5342591 = 8013887) B8013887
theorem B3561727 : Blo 2223435 3561727 := bstep (se 1 (by rfl) ⟨2671295, by rfl⟩ : syracuseStep 3561727 = 5342591) B5342591
theorem B4748969 : Blo 2223435 4748969 := bstep (se 2 (by rfl) ⟨1780863, by rfl⟩ : syracuseStep 4748969 = 3561727) B3561727
theorem B3165979 : Blo 2223435 3165979 := bstep (se 1 (by rfl) ⟨2374484, by rfl⟩ : syracuseStep 3165979 = 4748969) B4748969
theorem B4221305 : Blo 2223435 4221305 := bstep (se 2 (by rfl) ⟨1582989, by rfl⟩ : syracuseStep 4221305 = 3165979) B3165979
theorem B2814203 : Blo 2223435 2814203 := bstep (se 1 (by rfl) ⟨2110652, by rfl⟩ : syracuseStep 2814203 = 4221305) B4221305
theorem B7504541 : Blo 2223435 7504541 := bstep (se 3 (by rfl) ⟨1407101, by rfl⟩ : syracuseStep 7504541 = 2814203) B2814203
theorem B5003027 : Blo 2223435 5003027 := bstep (se 1 (by rfl) ⟨3752270, by rfl⟩ : syracuseStep 5003027 = 7504541) B7504541
theorem B3335351 : Blo 2223435 3335351 := bstep (se 1 (by rfl) ⟨2501513, by rfl⟩ : syracuseStep 3335351 = 5003027) B5003027
theorem B2223567 : Blo 2223435 2223567 := bstep (se 1 (by rfl) ⟨1667675, by rfl⟩ : syracuseStep 2223567 = 3335351) B3335351
theorem B3335357 : Blo 2223435 3335357 := bbase (se 3 (by rfl) ⟨625379, by rfl⟩ : syracuseStep 3335357 = 1250759) (by norm_num)
theorem B2223571 : Blo 2223435 2223571 := bstep (se 1 (by rfl) ⟨1667678, by rfl⟩ : syracuseStep 2223571 = 3335357) B3335357
theorem B5003045 : Blo 2223435 5003045 := bbase (se 4 (by rfl) ⟨469035, by rfl⟩ : syracuseStep 5003045 = 938071) (by norm_num)
theorem B3335363 : Blo 2223435 3335363 := bstep (se 1 (by rfl) ⟨2501522, by rfl⟩ : syracuseStep 3335363 = 5003045) B5003045
theorem B2223575 : Blo 2223435 2223575 := bstep (se 1 (by rfl) ⟨1667681, by rfl⟩ : syracuseStep 2223575 = 3335363) B3335363
theorem B5628437 : Blo 2223435 5628437 := bbase (se 6 (by rfl) ⟨131916, by rfl⟩ : syracuseStep 5628437 = 263833) (by norm_num)
theorem B3752291 : Blo 2223435 3752291 := bstep (se 1 (by rfl) ⟨2814218, by rfl⟩ : syracuseStep 3752291 = 5628437) B5628437
theorem B2501527 : Blo 2223435 2501527 := bstep (se 1 (by rfl) ⟨1876145, by rfl⟩ : syracuseStep 2501527 = 3752291) B3752291
theorem B3335369 : Blo 2223435 3335369 := bstep (se 2 (by rfl) ⟨1250763, by rfl⟩ : syracuseStep 3335369 = 2501527) B2501527
theorem B2223579 : Blo 2223435 2223579 := bstep (se 1 (by rfl) ⟨1667684, by rfl⟩ : syracuseStep 2223579 = 3335369) B3335369
theorem B9498005 : Blo 2223435 9498005 := bbase (se 6 (by rfl) ⟨222609, by rfl⟩ : syracuseStep 9498005 = 445219) (by norm_num)
theorem B6332003 : Blo 2223435 6332003 := bstep (se 1 (by rfl) ⟨4749002, by rfl⟩ : syracuseStep 6332003 = 9498005) B9498005
theorem B4221335 : Blo 2223435 4221335 := bstep (se 1 (by rfl) ⟨3166001, by rfl⟩ : syracuseStep 4221335 = 6332003) B6332003
theorem B11256893 : Blo 2223435 11256893 := bstep (se 3 (by rfl) ⟨2110667, by rfl⟩ : syracuseStep 11256893 = 4221335) B4221335
theorem B7504595 : Blo 2223435 7504595 := bstep (se 1 (by rfl) ⟨5628446, by rfl⟩ : syracuseStep 7504595 = 11256893) B11256893
theorem B5003063 : Blo 2223435 5003063 := bstep (se 1 (by rfl) ⟨3752297, by rfl⟩ : syracuseStep 5003063 = 7504595) B7504595
theorem B3335375 : Blo 2223435 3335375 := bstep (se 1 (by rfl) ⟨2501531, by rfl⟩ : syracuseStep 3335375 = 5003063) B5003063
theorem B2223583 : Blo 2223435 2223583 := bstep (se 1 (by rfl) ⟨1667687, by rfl⟩ : syracuseStep 2223583 = 3335375) B3335375
theorem B3335381 : Blo 2223435 3335381 := bbase (se 7 (by rfl) ⟨39086, by rfl⟩ : syracuseStep 3335381 = 78173) (by norm_num)
theorem B2223587 : Blo 2223435 2223587 := bstep (se 1 (by rfl) ⟨1667690, by rfl⟩ : syracuseStep 2223587 = 3335381) B3335381
theorem B3166013 : Blo 2223435 3166013 := bbase (se 3 (by rfl) ⟨593627, by rfl⟩ : syracuseStep 3166013 = 1187255) (by norm_num)
theorem B8442701 : Blo 2223435 8442701 := bstep (se 3 (by rfl) ⟨1583006, by rfl⟩ : syracuseStep 8442701 = 3166013) B3166013
theorem B5628467 : Blo 2223435 5628467 := bstep (se 1 (by rfl) ⟨4221350, by rfl⟩ : syracuseStep 5628467 = 8442701) B8442701
theorem B3752311 : Blo 2223435 3752311 := bstep (se 1 (by rfl) ⟨2814233, by rfl⟩ : syracuseStep 3752311 = 5628467) B5628467
theorem B5003081 : Blo 2223435 5003081 := bstep (se 2 (by rfl) ⟨1876155, by rfl⟩ : syracuseStep 5003081 = 3752311) B3752311
theorem B3335387 : Blo 2223435 3335387 := bstep (se 1 (by rfl) ⟨2501540, by rfl⟩ : syracuseStep 3335387 = 5003081) B5003081
theorem B2223591 : Blo 2223435 2223591 := bstep (se 1 (by rfl) ⟨1667693, by rfl⟩ : syracuseStep 2223591 = 3335387) B3335387
theorem B2501545 : Blo 2223435 2501545 := bbase (se 2 (by rfl) ⟨938079, by rfl⟩ : syracuseStep 2501545 = 1876159) (by norm_num)
theorem B3335393 : Blo 2223435 3335393 := bstep (se 2 (by rfl) ⟨1250772, by rfl⟩ : syracuseStep 3335393 = 2501545) B2501545
theorem B2223595 : Blo 2223435 2223595 := bstep (se 1 (by rfl) ⟨1667696, by rfl⟩ : syracuseStep 2223595 = 3335393) B3335393
theorem B10685333 : Blo 2223435 10685333 := bbase (se 6 (by rfl) ⟨250437, by rfl⟩ : syracuseStep 10685333 = 500875) (by norm_num)
theorem B7123555 : Blo 2223435 7123555 := bstep (se 1 (by rfl) ⟨5342666, by rfl⟩ : syracuseStep 7123555 = 10685333) B10685333
theorem B9498073 : Blo 2223435 9498073 := bstep (se 2 (by rfl) ⟨3561777, by rfl⟩ : syracuseStep 9498073 = 7123555) B7123555
theorem B12664097 : Blo 2223435 12664097 := bstep (se 2 (by rfl) ⟨4749036, by rfl⟩ : syracuseStep 12664097 = 9498073) B9498073
theorem B8442731 : Blo 2223435 8442731 := bstep (se 1 (by rfl) ⟨6332048, by rfl⟩ : syracuseStep 8442731 = 12664097) B12664097
theorem B5628487 : Blo 2223435 5628487 := bstep (se 1 (by rfl) ⟨4221365, by rfl⟩ : syracuseStep 5628487 = 8442731) B8442731
theorem B7504649 : Blo 2223435 7504649 := bstep (se 2 (by rfl) ⟨2814243, by rfl⟩ : syracuseStep 7504649 = 5628487) B5628487
theorem B5003099 : Blo 2223435 5003099 := bstep (se 1 (by rfl) ⟨3752324, by rfl⟩ : syracuseStep 5003099 = 7504649) B7504649
theorem B3335399 : Blo 2223435 3335399 := bstep (se 1 (by rfl) ⟨2501549, by rfl⟩ : syracuseStep 3335399 = 5003099) B5003099
theorem B2223599 : Blo 2223435 2223599 := bstep (se 1 (by rfl) ⟨1667699, by rfl⟩ : syracuseStep 2223599 = 3335399) B3335399
theorem B3335405 : Blo 2223435 3335405 := bbase (se 3 (by rfl) ⟨625388, by rfl⟩ : syracuseStep 3335405 = 1250777) (by norm_num)
theorem B2223603 : Blo 2223435 2223603 := bstep (se 1 (by rfl) ⟨1667702, by rfl⟩ : syracuseStep 2223603 = 3335405) B3335405
theorem B5003117 : Blo 2223435 5003117 := bbase (se 3 (by rfl) ⟨938084, by rfl⟩ : syracuseStep 5003117 = 1876169) (by norm_num)
theorem B3335411 : Blo 2223435 3335411 := bstep (se 1 (by rfl) ⟨2501558, by rfl⟩ : syracuseStep 3335411 = 5003117) B5003117
theorem B2223607 : Blo 2223435 2223607 := bstep (se 1 (by rfl) ⟨1667705, by rfl⟩ : syracuseStep 2223607 = 3335411) B3335411
theorem B4221389 : Blo 2223435 4221389 := bbase (se 3 (by rfl) ⟨791510, by rfl⟩ : syracuseStep 4221389 = 1583021) (by norm_num)
theorem B2814259 : Blo 2223435 2814259 := bstep (se 1 (by rfl) ⟨2110694, by rfl⟩ : syracuseStep 2814259 = 4221389) B4221389
theorem B3752345 : Blo 2223435 3752345 := bstep (se 2 (by rfl) ⟨1407129, by rfl⟩ : syracuseStep 3752345 = 2814259) B2814259
theorem B2501563 : Blo 2223435 2501563 := bstep (se 1 (by rfl) ⟨1876172, by rfl⟩ : syracuseStep 2501563 = 3752345) B3752345
theorem B3335417 : Blo 2223435 3335417 := bstep (se 2 (by rfl) ⟨1250781, by rfl⟩ : syracuseStep 3335417 = 2501563) B2501563
theorem B2223611 : Blo 2223435 2223611 := bstep (se 1 (by rfl) ⟨1667708, by rfl⟩ : syracuseStep 2223611 = 3335417) B3335417
theorem B6761861 : Blo 2223435 6761861 := bbase (se 4 (by rfl) ⟨633924, by rfl⟩ : syracuseStep 6761861 = 1267849) (by norm_num)
theorem B4507907 : Blo 2223435 4507907 := bstep (se 1 (by rfl) ⟨3380930, by rfl⟩ : syracuseStep 4507907 = 6761861) B6761861
theorem B12021085 : Blo 2223435 12021085 := bstep (se 3 (by rfl) ⟨2253953, by rfl⟩ : syracuseStep 12021085 = 4507907) B4507907
theorem B16028113 : Blo 2223435 16028113 := bstep (se 2 (by rfl) ⟨6010542, by rfl⟩ : syracuseStep 16028113 = 12021085) B12021085
theorem B21370817 : Blo 2223435 21370817 := bstep (se 2 (by rfl) ⟨8014056, by rfl⟩ : syracuseStep 21370817 = 16028113) B16028113
theorem B56988845 : Blo 2223435 56988845 := bstep (se 3 (by rfl) ⟨10685408, by rfl⟩ : syracuseStep 56988845 = 21370817) B21370817
theorem B37992563 : Blo 2223435 37992563 := bstep (se 1 (by rfl) ⟨28494422, by rfl⟩ : syracuseStep 37992563 = 56988845) B56988845
theorem B25328375 : Blo 2223435 25328375 := bstep (se 1 (by rfl) ⟨18996281, by rfl⟩ : syracuseStep 25328375 = 37992563) B37992563
theorem B16885583 : Blo 2223435 16885583 := bstep (se 1 (by rfl) ⟨12664187, by rfl⟩ : syracuseStep 16885583 = 25328375) B25328375
theorem B11257055 : Blo 2223435 11257055 := bstep (se 1 (by rfl) ⟨8442791, by rfl⟩ : syracuseStep 11257055 = 16885583) B16885583
theorem B7504703 : Blo 2223435 7504703 := bstep (se 1 (by rfl) ⟨5628527, by rfl⟩ : syracuseStep 7504703 = 11257055) B11257055
theorem B5003135 : Blo 2223435 5003135 := bstep (se 1 (by rfl) ⟨3752351, by rfl⟩ : syracuseStep 5003135 = 7504703) B7504703
theorem B3335423 : Blo 2223435 3335423 := bstep (se 1 (by rfl) ⟨2501567, by rfl⟩ : syracuseStep 3335423 = 5003135) B5003135
theorem B2223615 : Blo 2223435 2223615 := bstep (se 1 (by rfl) ⟨1667711, by rfl⟩ : syracuseStep 2223615 = 3335423) B3335423
theorem B3335429 : Blo 2223435 3335429 := bbase (se 4 (by rfl) ⟨312696, by rfl⟩ : syracuseStep 3335429 = 625393) (by norm_num)
theorem B2223619 : Blo 2223435 2223619 := bstep (se 1 (by rfl) ⟨1667714, by rfl⟩ : syracuseStep 2223619 = 3335429) B3335429
theorem B3752365 : Blo 2223435 3752365 := bbase (se 3 (by rfl) ⟨703568, by rfl⟩ : syracuseStep 3752365 = 1407137) (by norm_num)
theorem B5003153 : Blo 2223435 5003153 := bstep (se 2 (by rfl) ⟨1876182, by rfl⟩ : syracuseStep 5003153 = 3752365) B3752365
theorem B3335435 : Blo 2223435 3335435 := bstep (se 1 (by rfl) ⟨2501576, by rfl⟩ : syracuseStep 3335435 = 5003153) B5003153
theorem B2223623 : Blo 2223435 2223623 := bstep (se 1 (by rfl) ⟨1667717, by rfl⟩ : syracuseStep 2223623 = 3335435) B3335435
theorem B2501581 : Blo 2223435 2501581 := bbase (se 3 (by rfl) ⟨469046, by rfl⟩ : syracuseStep 2501581 = 938093) (by norm_num)
theorem B3335441 : Blo 2223435 3335441 := bstep (se 2 (by rfl) ⟨1250790, by rfl⟩ : syracuseStep 3335441 = 2501581) B2501581
theorem B2223627 : Blo 2223435 2223627 := bstep (se 1 (by rfl) ⟨1667720, by rfl⟩ : syracuseStep 2223627 = 3335441) B3335441
theorem B7504757 : Blo 2223435 7504757 := bbase (se 5 (by rfl) ⟨351785, by rfl⟩ : syracuseStep 7504757 = 703571) (by norm_num)
theorem B5003171 : Blo 2223435 5003171 := bstep (se 1 (by rfl) ⟨3752378, by rfl⟩ : syracuseStep 5003171 = 7504757) B7504757
theorem B3335447 : Blo 2223435 3335447 := bstep (se 1 (by rfl) ⟨2501585, by rfl⟩ : syracuseStep 3335447 = 5003171) B5003171
theorem B2223631 : Blo 2223435 2223631 := bstep (se 1 (by rfl) ⟨1667723, by rfl⟩ : syracuseStep 2223631 = 3335447) B3335447
theorem B3335453 : Blo 2223435 3335453 := bbase (se 3 (by rfl) ⟨625397, by rfl⟩ : syracuseStep 3335453 = 1250795) (by norm_num)
theorem B2223635 : Blo 2223435 2223635 := bstep (se 1 (by rfl) ⟨1667726, by rfl⟩ : syracuseStep 2223635 = 3335453) B3335453
theorem B5003189 : Blo 2223435 5003189 := bbase (se 5 (by rfl) ⟨234524, by rfl⟩ : syracuseStep 5003189 = 469049) (by norm_num)
theorem B3335459 : Blo 2223435 3335459 := bstep (se 1 (by rfl) ⟨2501594, by rfl⟩ : syracuseStep 3335459 = 5003189) B5003189
theorem B2223639 : Blo 2223435 2223639 := bstep (se 1 (by rfl) ⟨1667729, by rfl⟩ : syracuseStep 2223639 = 3335459) B3335459
theorem B5342773 : Blo 2223435 5342773 := bbase (se 5 (by rfl) ⟨250442, by rfl⟩ : syracuseStep 5342773 = 500885) (by norm_num)
theorem B7123697 : Blo 2223435 7123697 := bstep (se 2 (by rfl) ⟨2671386, by rfl⟩ : syracuseStep 7123697 = 5342773) B5342773
theorem B4749131 : Blo 2223435 4749131 := bstep (se 1 (by rfl) ⟨3561848, by rfl⟩ : syracuseStep 4749131 = 7123697) B7123697
theorem B12664349 : Blo 2223435 12664349 := bstep (se 3 (by rfl) ⟨2374565, by rfl⟩ : syracuseStep 12664349 = 4749131) B4749131
theorem B8442899 : Blo 2223435 8442899 := bstep (se 1 (by rfl) ⟨6332174, by rfl⟩ : syracuseStep 8442899 = 12664349) B12664349
theorem B5628599 : Blo 2223435 5628599 := bstep (se 1 (by rfl) ⟨4221449, by rfl⟩ : syracuseStep 5628599 = 8442899) B8442899
theorem B3752399 : Blo 2223435 3752399 := bstep (se 1 (by rfl) ⟨2814299, by rfl⟩ : syracuseStep 3752399 = 5628599) B5628599
theorem B2501599 : Blo 2223435 2501599 := bstep (se 1 (by rfl) ⟨1876199, by rfl⟩ : syracuseStep 2501599 = 3752399) B3752399
theorem B3335465 : Blo 2223435 3335465 := bstep (se 2 (by rfl) ⟨1250799, by rfl⟩ : syracuseStep 3335465 = 2501599) B2501599
theorem B2223643 : Blo 2223435 2223643 := bstep (se 1 (by rfl) ⟨1667732, by rfl⟩ : syracuseStep 2223643 = 3335465) B3335465
theorem B5705405 : Blo 2223435 5705405 := bbase (se 3 (by rfl) ⟨1069763, by rfl⟩ : syracuseStep 5705405 = 2139527) (by norm_num)
theorem B3803603 : Blo 2223435 3803603 := bstep (se 1 (by rfl) ⟨2852702, by rfl⟩ : syracuseStep 3803603 = 5705405) B5705405
theorem B10142941 : Blo 2223435 10142941 := bstep (se 3 (by rfl) ⟨1901801, by rfl⟩ : syracuseStep 10142941 = 3803603) B3803603
theorem B13523921 : Blo 2223435 13523921 := bstep (se 2 (by rfl) ⟨5071470, by rfl⟩ : syracuseStep 13523921 = 10142941) B10142941
theorem B9015947 : Blo 2223435 9015947 := bstep (se 1 (by rfl) ⟨6761960, by rfl⟩ : syracuseStep 9015947 = 13523921) B13523921
theorem B6010631 : Blo 2223435 6010631 := bstep (se 1 (by rfl) ⟨4507973, by rfl⟩ : syracuseStep 6010631 = 9015947) B9015947
theorem B4007087 : Blo 2223435 4007087 := bstep (se 1 (by rfl) ⟨3005315, by rfl⟩ : syracuseStep 4007087 = 6010631) B6010631
theorem B2671391 : Blo 2223435 2671391 := bstep (se 1 (by rfl) ⟨2003543, by rfl⟩ : syracuseStep 2671391 = 4007087) B4007087
theorem B7123709 : Blo 2223435 7123709 := bstep (se 3 (by rfl) ⟨1335695, by rfl⟩ : syracuseStep 7123709 = 2671391) B2671391
theorem B4749139 : Blo 2223435 4749139 := bstep (se 1 (by rfl) ⟨3561854, by rfl⟩ : syracuseStep 4749139 = 7123709) B7123709
theorem B6332185 : Blo 2223435 6332185 := bstep (se 2 (by rfl) ⟨2374569, by rfl⟩ : syracuseStep 6332185 = 4749139) B4749139
theorem B8442913 : Blo 2223435 8442913 := bstep (se 2 (by rfl) ⟨3166092, by rfl⟩ : syracuseStep 8442913 = 6332185) B6332185
theorem B11257217 : Blo 2223435 11257217 := bstep (se 2 (by rfl) ⟨4221456, by rfl⟩ : syracuseStep 11257217 = 8442913) B8442913
theorem B7504811 : Blo 2223435 7504811 := bstep (se 1 (by rfl) ⟨5628608, by rfl⟩ : syracuseStep 7504811 = 11257217) B11257217
theorem B5003207 : Blo 2223435 5003207 := bstep (se 1 (by rfl) ⟨3752405, by rfl⟩ : syracuseStep 5003207 = 7504811) B7504811
theorem B3335471 : Blo 2223435 3335471 := bstep (se 1 (by rfl) ⟨2501603, by rfl⟩ : syracuseStep 3335471 = 5003207) B5003207
theorem B2223647 : Blo 2223435 2223647 := bstep (se 1 (by rfl) ⟨1667735, by rfl⟩ : syracuseStep 2223647 = 3335471) B3335471
theorem B3335477 : Blo 2223435 3335477 := bbase (se 5 (by rfl) ⟨156350, by rfl⟩ : syracuseStep 3335477 = 312701) (by norm_num)
theorem B2223651 : Blo 2223435 2223651 := bstep (se 1 (by rfl) ⟨1667738, by rfl⟩ : syracuseStep 2223651 = 3335477) B3335477
theorem B5628629 : Blo 2223435 5628629 := bbase (se 7 (by rfl) ⟨65960, by rfl⟩ : syracuseStep 5628629 = 131921) (by norm_num)
theorem B3752419 : Blo 2223435 3752419 := bstep (se 1 (by rfl) ⟨2814314, by rfl⟩ : syracuseStep 3752419 = 5628629) B5628629
theorem B5003225 : Blo 2223435 5003225 := bstep (se 2 (by rfl) ⟨1876209, by rfl⟩ : syracuseStep 5003225 = 3752419) B3752419
theorem B3335483 : Blo 2223435 3335483 := bstep (se 1 (by rfl) ⟨2501612, by rfl⟩ : syracuseStep 3335483 = 5003225) B5003225
theorem B2223655 : Blo 2223435 2223655 := bstep (se 1 (by rfl) ⟨1667741, by rfl⟩ : syracuseStep 2223655 = 3335483) B3335483
theorem B2501617 : Blo 2223435 2501617 := bbase (se 2 (by rfl) ⟨938106, by rfl⟩ : syracuseStep 2501617 = 1876213) (by norm_num)
theorem B3335489 : Blo 2223435 3335489 := bstep (se 2 (by rfl) ⟨1250808, by rfl⟩ : syracuseStep 3335489 = 2501617) B2501617
theorem B2223659 : Blo 2223435 2223659 := bstep (se 1 (by rfl) ⟨1667744, by rfl⟩ : syracuseStep 2223659 = 3335489) B3335489
theorem B18032021 : Blo 2223435 18032021 := bbase (se 6 (by rfl) ⟨422625, by rfl⟩ : syracuseStep 18032021 = 845251) (by norm_num)
theorem B12021347 : Blo 2223435 12021347 := bstep (se 1 (by rfl) ⟨9016010, by rfl⟩ : syracuseStep 12021347 = 18032021) B18032021
theorem B8014231 : Blo 2223435 8014231 := bstep (se 1 (by rfl) ⟨6010673, by rfl⟩ : syracuseStep 8014231 = 12021347) B12021347
theorem B10685641 : Blo 2223435 10685641 := bstep (se 2 (by rfl) ⟨4007115, by rfl⟩ : syracuseStep 10685641 = 8014231) B8014231
theorem B14247521 : Blo 2223435 14247521 := bstep (se 2 (by rfl) ⟨5342820, by rfl⟩ : syracuseStep 14247521 = 10685641) B10685641
theorem B9498347 : Blo 2223435 9498347 := bstep (se 1 (by rfl) ⟨7123760, by rfl⟩ : syracuseStep 9498347 = 14247521) B14247521
theorem B6332231 : Blo 2223435 6332231 := bstep (se 1 (by rfl) ⟨4749173, by rfl⟩ : syracuseStep 6332231 = 9498347) B9498347
theorem B4221487 : Blo 2223435 4221487 := bstep (se 1 (by rfl) ⟨3166115, by rfl⟩ : syracuseStep 4221487 = 6332231) B6332231
theorem B5628649 : Blo 2223435 5628649 := bstep (se 2 (by rfl) ⟨2110743, by rfl⟩ : syracuseStep 5628649 = 4221487) B4221487
theorem B7504865 : Blo 2223435 7504865 := bstep (se 2 (by rfl) ⟨2814324, by rfl⟩ : syracuseStep 7504865 = 5628649) B5628649
theorem B5003243 : Blo 2223435 5003243 := bstep (se 1 (by rfl) ⟨3752432, by rfl⟩ : syracuseStep 5003243 = 7504865) B7504865
theorem B3335495 : Blo 2223435 3335495 := bstep (se 1 (by rfl) ⟨2501621, by rfl⟩ : syracuseStep 3335495 = 5003243) B5003243
theorem B2223663 : Blo 2223435 2223663 := bstep (se 1 (by rfl) ⟨1667747, by rfl⟩ : syracuseStep 2223663 = 3335495) B3335495
theorem B3335501 : Blo 2223435 3335501 := bbase (se 3 (by rfl) ⟨625406, by rfl⟩ : syracuseStep 3335501 = 1250813) (by norm_num)
theorem B2223667 : Blo 2223435 2223667 := bstep (se 1 (by rfl) ⟨1667750, by rfl⟩ : syracuseStep 2223667 = 3335501) B3335501
theorem B5003261 : Blo 2223435 5003261 := bbase (se 3 (by rfl) ⟨938111, by rfl⟩ : syracuseStep 5003261 = 1876223) (by norm_num)
theorem B3335507 : Blo 2223435 3335507 := bstep (se 1 (by rfl) ⟨2501630, by rfl⟩ : syracuseStep 3335507 = 5003261) B5003261
theorem B2223671 : Blo 2223435 2223671 := bstep (se 1 (by rfl) ⟨1667753, by rfl⟩ : syracuseStep 2223671 = 3335507) B3335507
theorem B3752453 : Blo 2223435 3752453 := bbase (se 4 (by rfl) ⟨351792, by rfl⟩ : syracuseStep 3752453 = 703585) (by norm_num)
theorem B2501635 : Blo 2223435 2501635 := bstep (se 1 (by rfl) ⟨1876226, by rfl⟩ : syracuseStep 2501635 = 3752453) B3752453
theorem B3335513 : Blo 2223435 3335513 := bstep (se 2 (by rfl) ⟨1250817, by rfl⟩ : syracuseStep 3335513 = 2501635) B2501635
theorem B2223675 : Blo 2223435 2223675 := bstep (se 1 (by rfl) ⟨1667756, by rfl⟩ : syracuseStep 2223675 = 3335513) B3335513
theorem B16886069 : Blo 2223435 16886069 := bbase (se 5 (by rfl) ⟨791534, by rfl⟩ : syracuseStep 16886069 = 1583069) (by norm_num)
theorem B11257379 : Blo 2223435 11257379 := bstep (se 1 (by rfl) ⟨8443034, by rfl⟩ : syracuseStep 11257379 = 16886069) B16886069
theorem B7504919 : Blo 2223435 7504919 := bstep (se 1 (by rfl) ⟨5628689, by rfl⟩ : syracuseStep 7504919 = 11257379) B11257379
theorem B5003279 : Blo 2223435 5003279 := bstep (se 1 (by rfl) ⟨3752459, by rfl⟩ : syracuseStep 5003279 = 7504919) B7504919
theorem B3335519 : Blo 2223435 3335519 := bstep (se 1 (by rfl) ⟨2501639, by rfl⟩ : syracuseStep 3335519 = 5003279) B5003279
theorem B2223679 : Blo 2223435 2223679 := bstep (se 1 (by rfl) ⟨1667759, by rfl⟩ : syracuseStep 2223679 = 3335519) B3335519
theorem B3335525 : Blo 2223435 3335525 := bbase (se 4 (by rfl) ⟨312705, by rfl⟩ : syracuseStep 3335525 = 625411) (by norm_num)
theorem B2223683 : Blo 2223435 2223683 := bstep (se 1 (by rfl) ⟨1667762, by rfl⟩ : syracuseStep 2223683 = 3335525) B3335525
theorem B4221533 : Blo 2223435 4221533 := bbase (se 3 (by rfl) ⟨791537, by rfl⟩ : syracuseStep 4221533 = 1583075) (by norm_num)
theorem B2814355 : Blo 2223435 2814355 := bstep (se 1 (by rfl) ⟨2110766, by rfl⟩ : syracuseStep 2814355 = 4221533) B4221533
theorem B3752473 : Blo 2223435 3752473 := bstep (se 2 (by rfl) ⟨1407177, by rfl⟩ : syracuseStep 3752473 = 2814355) B2814355
theorem B5003297 : Blo 2223435 5003297 := bstep (se 2 (by rfl) ⟨1876236, by rfl⟩ : syracuseStep 5003297 = 3752473) B3752473
theorem B3335531 : Blo 2223435 3335531 := bstep (se 1 (by rfl) ⟨2501648, by rfl⟩ : syracuseStep 3335531 = 5003297) B5003297
theorem B2223687 : Blo 2223435 2223687 := bstep (se 1 (by rfl) ⟨1667765, by rfl⟩ : syracuseStep 2223687 = 3335531) B3335531
theorem B2501653 : Blo 2223435 2501653 := bbase (se 6 (by rfl) ⟨58632, by rfl⟩ : syracuseStep 2501653 = 117265) (by norm_num)
theorem B3335537 : Blo 2223435 3335537 := bstep (se 2 (by rfl) ⟨1250826, by rfl⟩ : syracuseStep 3335537 = 2501653) B2501653
theorem B2223691 : Blo 2223435 2223691 := bstep (se 1 (by rfl) ⟨1667768, by rfl⟩ : syracuseStep 2223691 = 3335537) B3335537
theorem B2814365 : Blo 2223435 2814365 := bbase (se 3 (by rfl) ⟨527693, by rfl⟩ : syracuseStep 2814365 = 1055387) (by norm_num)
theorem B7504973 : Blo 2223435 7504973 := bstep (se 3 (by rfl) ⟨1407182, by rfl⟩ : syracuseStep 7504973 = 2814365) B2814365
theorem B5003315 : Blo 2223435 5003315 := bstep (se 1 (by rfl) ⟨3752486, by rfl⟩ : syracuseStep 5003315 = 7504973) B7504973
theorem B3335543 : Blo 2223435 3335543 := bstep (se 1 (by rfl) ⟨2501657, by rfl⟩ : syracuseStep 3335543 = 5003315) B5003315
theorem B2223695 : Blo 2223435 2223695 := bstep (se 1 (by rfl) ⟨1667771, by rfl⟩ : syracuseStep 2223695 = 3335543) B3335543
theorem B3335549 : Blo 2223435 3335549 := bbase (se 3 (by rfl) ⟨625415, by rfl⟩ : syracuseStep 3335549 = 1250831) (by norm_num)
theorem B2223699 : Blo 2223435 2223699 := bstep (se 1 (by rfl) ⟨1667774, by rfl⟩ : syracuseStep 2223699 = 3335549) B3335549
theorem B5003333 : Blo 2223435 5003333 := bbase (se 4 (by rfl) ⟨469062, by rfl⟩ : syracuseStep 5003333 = 938125) (by norm_num)
theorem B3335555 : Blo 2223435 3335555 := bstep (se 1 (by rfl) ⟨2501666, by rfl⟩ : syracuseStep 3335555 = 5003333) B5003333
theorem B2223703 : Blo 2223435 2223703 := bstep (se 1 (by rfl) ⟨1667777, by rfl⟩ : syracuseStep 2223703 = 3335555) B3335555
theorem B6332357 : Blo 2223435 6332357 := bbase (se 4 (by rfl) ⟨593658, by rfl⟩ : syracuseStep 6332357 = 1187317) (by norm_num)
theorem B4221571 : Blo 2223435 4221571 := bstep (se 1 (by rfl) ⟨3166178, by rfl⟩ : syracuseStep 4221571 = 6332357) B6332357
theorem B5628761 : Blo 2223435 5628761 := bstep (se 2 (by rfl) ⟨2110785, by rfl⟩ : syracuseStep 5628761 = 4221571) B4221571
theorem B3752507 : Blo 2223435 3752507 := bstep (se 1 (by rfl) ⟨2814380, by rfl⟩ : syracuseStep 3752507 = 5628761) B5628761
theorem B2501671 : Blo 2223435 2501671 := bstep (se 1 (by rfl) ⟨1876253, by rfl⟩ : syracuseStep 2501671 = 3752507) B3752507
theorem B3335561 : Blo 2223435 3335561 := bstep (se 2 (by rfl) ⟨1250835, by rfl⟩ : syracuseStep 3335561 = 2501671) B2501671
theorem B2223707 : Blo 2223435 2223707 := bstep (se 1 (by rfl) ⟨1667780, by rfl⟩ : syracuseStep 2223707 = 3335561) B3335561
theorem B11257541 : Blo 2223435 11257541 := bbase (se 4 (by rfl) ⟨1055394, by rfl⟩ : syracuseStep 11257541 = 2110789) (by norm_num)
theorem B7505027 : Blo 2223435 7505027 := bstep (se 1 (by rfl) ⟨5628770, by rfl⟩ : syracuseStep 7505027 = 11257541) B11257541
theorem B5003351 : Blo 2223435 5003351 := bstep (se 1 (by rfl) ⟨3752513, by rfl⟩ : syracuseStep 5003351 = 7505027) B7505027
theorem B3335567 : Blo 2223435 3335567 := bstep (se 1 (by rfl) ⟨2501675, by rfl⟩ : syracuseStep 3335567 = 5003351) B5003351
theorem B2223711 : Blo 2223435 2223711 := bstep (se 1 (by rfl) ⟨1667783, by rfl⟩ : syracuseStep 2223711 = 3335567) B3335567
theorem B3335573 : Blo 2223435 3335573 := bbase (se 6 (by rfl) ⟨78177, by rfl⟩ : syracuseStep 3335573 = 156355) (by norm_num)
theorem B2223715 : Blo 2223435 2223715 := bstep (se 1 (by rfl) ⟨1667786, by rfl⟩ : syracuseStep 2223715 = 3335573) B3335573
theorem B4749293 : Blo 2223435 4749293 := bbase (se 3 (by rfl) ⟨890492, by rfl⟩ : syracuseStep 4749293 = 1780985) (by norm_num)
theorem B12664781 : Blo 2223435 12664781 := bstep (se 3 (by rfl) ⟨2374646, by rfl⟩ : syracuseStep 12664781 = 4749293) B4749293
theorem B8443187 : Blo 2223435 8443187 := bstep (se 1 (by rfl) ⟨6332390, by rfl⟩ : syracuseStep 8443187 = 12664781) B12664781
theorem B5628791 : Blo 2223435 5628791 := bstep (se 1 (by rfl) ⟨4221593, by rfl⟩ : syracuseStep 5628791 = 8443187) B8443187
theorem B3752527 : Blo 2223435 3752527 := bstep (se 1 (by rfl) ⟨2814395, by rfl⟩ : syracuseStep 3752527 = 5628791) B5628791
theorem B5003369 : Blo 2223435 5003369 := bstep (se 2 (by rfl) ⟨1876263, by rfl⟩ : syracuseStep 5003369 = 3752527) B3752527
theorem B3335579 : Blo 2223435 3335579 := bstep (se 1 (by rfl) ⟨2501684, by rfl⟩ : syracuseStep 3335579 = 5003369) B5003369
theorem B2223719 : Blo 2223435 2223719 := bstep (se 1 (by rfl) ⟨1667789, by rfl⟩ : syracuseStep 2223719 = 3335579) B3335579
theorem B2501689 : Blo 2223435 2501689 := bbase (se 2 (by rfl) ⟨938133, by rfl⟩ : syracuseStep 2501689 = 1876267) (by norm_num)
theorem B3335585 : Blo 2223435 3335585 := bstep (se 2 (by rfl) ⟨1250844, by rfl⟩ : syracuseStep 3335585 = 2501689) B2501689
theorem B2223723 : Blo 2223435 2223723 := bstep (se 1 (by rfl) ⟨1667792, by rfl⟩ : syracuseStep 2223723 = 3335585) B3335585
theorem B2605493 : Blo 2223435 2605493 := bbase (se 5 (by rfl) ⟨122132, by rfl⟩ : syracuseStep 2605493 = 244265) (by norm_num)
theorem B6947981 : Blo 2223435 6947981 := bstep (se 3 (by rfl) ⟨1302746, by rfl⟩ : syracuseStep 6947981 = 2605493) B2605493
theorem B4631987 : Blo 2223435 4631987 := bstep (se 1 (by rfl) ⟨3473990, by rfl⟩ : syracuseStep 4631987 = 6947981) B6947981
theorem B12351965 : Blo 2223435 12351965 := bstep (se 3 (by rfl) ⟨2315993, by rfl⟩ : syracuseStep 12351965 = 4631987) B4631987
theorem B131754293 : Blo 2223435 131754293 := bstep (se 5 (by rfl) ⟨6175982, by rfl⟩ : syracuseStep 131754293 = 12351965) B12351965
theorem B87836195 : Blo 2223435 87836195 := bstep (se 1 (by rfl) ⟨65877146, by rfl⟩ : syracuseStep 87836195 = 131754293) B131754293
theorem B234229853 : Blo 2223435 234229853 := bstep (se 3 (by rfl) ⟨43918097, by rfl⟩ : syracuseStep 234229853 = 87836195) B87836195
theorem B624612941 : Blo 2223435 624612941 := bstep (se 3 (by rfl) ⟨117114926, by rfl⟩ : syracuseStep 624612941 = 234229853) B234229853
theorem B416408627 : Blo 2223435 416408627 := bstep (se 1 (by rfl) ⟨312306470, by rfl⟩ : syracuseStep 416408627 = 624612941) B624612941
theorem B277605751 : Blo 2223435 277605751 := bstep (se 1 (by rfl) ⟨208204313, by rfl⟩ : syracuseStep 277605751 = 416408627) B416408627
theorem B370141001 : Blo 2223435 370141001 := bstep (se 2 (by rfl) ⟨138802875, by rfl⟩ : syracuseStep 370141001 = 277605751) B277605751
theorem B246760667 : Blo 2223435 246760667 := bstep (se 1 (by rfl) ⟨185070500, by rfl⟩ : syracuseStep 246760667 = 370141001) B370141001
theorem B164507111 : Blo 2223435 164507111 := bstep (se 1 (by rfl) ⟨123380333, by rfl⟩ : syracuseStep 164507111 = 246760667) B246760667
theorem B109671407 : Blo 2223435 109671407 := bstep (se 1 (by rfl) ⟨82253555, by rfl⟩ : syracuseStep 109671407 = 164507111) B164507111
theorem B73114271 : Blo 2223435 73114271 := bstep (se 1 (by rfl) ⟨54835703, by rfl⟩ : syracuseStep 73114271 = 109671407) B109671407
theorem B48742847 : Blo 2223435 48742847 := bstep (se 1 (by rfl) ⟨36557135, by rfl⟩ : syracuseStep 48742847 = 73114271) B73114271
theorem B32495231 : Blo 2223435 32495231 := bstep (se 1 (by rfl) ⟨24371423, by rfl⟩ : syracuseStep 32495231 = 48742847) B48742847
theorem B21663487 : Blo 2223435 21663487 := bstep (se 1 (by rfl) ⟨16247615, by rfl⟩ : syracuseStep 21663487 = 32495231) B32495231
theorem B28884649 : Blo 2223435 28884649 := bstep (se 2 (by rfl) ⟨10831743, by rfl⟩ : syracuseStep 28884649 = 21663487) B21663487
theorem B38512865 : Blo 2223435 38512865 := bstep (se 2 (by rfl) ⟨14442324, by rfl⟩ : syracuseStep 38512865 = 28884649) B28884649
theorem B102700973 : Blo 2223435 102700973 := bstep (se 3 (by rfl) ⟨19256432, by rfl⟩ : syracuseStep 102700973 = 38512865) B38512865
theorem B68467315 : Blo 2223435 68467315 := bstep (se 1 (by rfl) ⟨51350486, by rfl⟩ : syracuseStep 68467315 = 102700973) B102700973
theorem B91289753 : Blo 2223435 91289753 := bstep (se 2 (by rfl) ⟨34233657, by rfl⟩ : syracuseStep 91289753 = 68467315) B68467315
theorem B60859835 : Blo 2223435 60859835 := bstep (se 1 (by rfl) ⟨45644876, by rfl⟩ : syracuseStep 60859835 = 91289753) B91289753
theorem B40573223 : Blo 2223435 40573223 := bstep (se 1 (by rfl) ⟨30429917, by rfl⟩ : syracuseStep 40573223 = 60859835) B60859835
theorem B27048815 : Blo 2223435 27048815 := bstep (se 1 (by rfl) ⟨20286611, by rfl⟩ : syracuseStep 27048815 = 40573223) B40573223
theorem B18032543 : Blo 2223435 18032543 := bstep (se 1 (by rfl) ⟨13524407, by rfl⟩ : syracuseStep 18032543 = 27048815) B27048815
theorem B12021695 : Blo 2223435 12021695 := bstep (se 1 (by rfl) ⟨9016271, by rfl⟩ : syracuseStep 12021695 = 18032543) B18032543
theorem B8014463 : Blo 2223435 8014463 := bstep (se 1 (by rfl) ⟨6010847, by rfl⟩ : syracuseStep 8014463 = 12021695) B12021695
theorem B5342975 : Blo 2223435 5342975 := bstep (se 1 (by rfl) ⟨4007231, by rfl⟩ : syracuseStep 5342975 = 8014463) B8014463
theorem B3561983 : Blo 2223435 3561983 := bstep (se 1 (by rfl) ⟨2671487, by rfl⟩ : syracuseStep 3561983 = 5342975) B5342975
theorem B2374655 : Blo 2223435 2374655 := bstep (se 1 (by rfl) ⟨1780991, by rfl⟩ : syracuseStep 2374655 = 3561983) B3561983
theorem B6332413 : Blo 2223435 6332413 := bstep (se 3 (by rfl) ⟨1187327, by rfl⟩ : syracuseStep 6332413 = 2374655) B2374655
theorem B8443217 : Blo 2223435 8443217 := bstep (se 2 (by rfl) ⟨3166206, by rfl⟩ : syracuseStep 8443217 = 6332413) B6332413
theorem B5628811 : Blo 2223435 5628811 := bstep (se 1 (by rfl) ⟨4221608, by rfl⟩ : syracuseStep 5628811 = 8443217) B8443217
theorem B7505081 : Blo 2223435 7505081 := bstep (se 2 (by rfl) ⟨2814405, by rfl⟩ : syracuseStep 7505081 = 5628811) B5628811
theorem B5003387 : Blo 2223435 5003387 := bstep (se 1 (by rfl) ⟨3752540, by rfl⟩ : syracuseStep 5003387 = 7505081) B7505081
theorem B3335591 : Blo 2223435 3335591 := bstep (se 1 (by rfl) ⟨2501693, by rfl⟩ : syracuseStep 3335591 = 5003387) B5003387
theorem B2223727 : Blo 2223435 2223727 := bstep (se 1 (by rfl) ⟨1667795, by rfl⟩ : syracuseStep 2223727 = 3335591) B3335591
theorem B3335597 : Blo 2223435 3335597 := bbase (se 3 (by rfl) ⟨625424, by rfl⟩ : syracuseStep 3335597 = 1250849) (by norm_num)
theorem B2223731 : Blo 2223435 2223731 := bstep (se 1 (by rfl) ⟨1667798, by rfl⟩ : syracuseStep 2223731 = 3335597) B3335597
theorem B5003405 : Blo 2223435 5003405 := bbase (se 3 (by rfl) ⟨938138, by rfl⟩ : syracuseStep 5003405 = 1876277) (by norm_num)
theorem B3335603 : Blo 2223435 3335603 := bstep (se 1 (by rfl) ⟨2501702, by rfl⟩ : syracuseStep 3335603 = 5003405) B5003405
theorem B2223735 : Blo 2223435 2223735 := bstep (se 1 (by rfl) ⟨1667801, by rfl⟩ : syracuseStep 2223735 = 3335603) B3335603
theorem B2814421 : Blo 2223435 2814421 := bbase (se 7 (by rfl) ⟨32981, by rfl⟩ : syracuseStep 2814421 = 65963) (by norm_num)
theorem B3752561 : Blo 2223435 3752561 := bstep (se 2 (by rfl) ⟨1407210, by rfl⟩ : syracuseStep 3752561 = 2814421) B2814421
theorem B2501707 : Blo 2223435 2501707 := bstep (se 1 (by rfl) ⟨1876280, by rfl⟩ : syracuseStep 2501707 = 3752561) B3752561
theorem B3335609 : Blo 2223435 3335609 := bstep (se 2 (by rfl) ⟨1250853, by rfl⟩ : syracuseStep 3335609 = 2501707) B2501707
theorem B2223739 : Blo 2223435 2223739 := bstep (se 1 (by rfl) ⟨1667804, by rfl⟩ : syracuseStep 2223739 = 3335609) B3335609
theorem B4337621 : Blo 2223435 4337621 := bbase (se 7 (by rfl) ⟨50831, by rfl⟩ : syracuseStep 4337621 = 101663) (by norm_num)
theorem B2891747 : Blo 2223435 2891747 := bstep (se 1 (by rfl) ⟨2168810, by rfl⟩ : syracuseStep 2891747 = 4337621) B4337621
theorem B7711325 : Blo 2223435 7711325 := bstep (se 3 (by rfl) ⟨1445873, by rfl⟩ : syracuseStep 7711325 = 2891747) B2891747
theorem B5140883 : Blo 2223435 5140883 := bstep (se 1 (by rfl) ⟨3855662, by rfl⟩ : syracuseStep 5140883 = 7711325) B7711325
theorem B3427255 : Blo 2223435 3427255 := bstep (se 1 (by rfl) ⟨2570441, by rfl⟩ : syracuseStep 3427255 = 5140883) B5140883
theorem B18278693 : Blo 2223435 18278693 := bstep (se 4 (by rfl) ⟨1713627, by rfl⟩ : syracuseStep 18278693 = 3427255) B3427255
theorem B12185795 : Blo 2223435 12185795 := bstep (se 1 (by rfl) ⟨9139346, by rfl⟩ : syracuseStep 12185795 = 18278693) B18278693
theorem B8123863 : Blo 2223435 8123863 := bstep (se 1 (by rfl) ⟨6092897, by rfl⟩ : syracuseStep 8123863 = 12185795) B12185795
theorem B10831817 : Blo 2223435 10831817 := bstep (se 2 (by rfl) ⟨4061931, by rfl⟩ : syracuseStep 10831817 = 8123863) B8123863
theorem B28884845 : Blo 2223435 28884845 := bstep (se 3 (by rfl) ⟨5415908, by rfl⟩ : syracuseStep 28884845 = 10831817) B10831817
theorem B19256563 : Blo 2223435 19256563 := bstep (se 1 (by rfl) ⟨14442422, by rfl⟩ : syracuseStep 19256563 = 28884845) B28884845
theorem B25675417 : Blo 2223435 25675417 := bstep (se 2 (by rfl) ⟨9628281, by rfl⟩ : syracuseStep 25675417 = 19256563) B19256563
theorem B34233889 : Blo 2223435 34233889 := bstep (se 2 (by rfl) ⟨12837708, by rfl⟩ : syracuseStep 34233889 = 25675417) B25675417
theorem B45645185 : Blo 2223435 45645185 := bstep (se 2 (by rfl) ⟨17116944, by rfl⟩ : syracuseStep 45645185 = 34233889) B34233889
theorem B30430123 : Blo 2223435 30430123 := bstep (se 1 (by rfl) ⟨22822592, by rfl⟩ : syracuseStep 30430123 = 45645185) B45645185
theorem B162293989 : Blo 2223435 162293989 := bstep (se 4 (by rfl) ⟨15215061, by rfl⟩ : syracuseStep 162293989 = 30430123) B30430123
theorem B216391985 : Blo 2223435 216391985 := bstep (se 2 (by rfl) ⟨81146994, by rfl⟩ : syracuseStep 216391985 = 162293989) B162293989
theorem B144261323 : Blo 2223435 144261323 := bstep (se 1 (by rfl) ⟨108195992, by rfl⟩ : syracuseStep 144261323 = 216391985) B216391985
theorem B96174215 : Blo 2223435 96174215 := bstep (se 1 (by rfl) ⟨72130661, by rfl⟩ : syracuseStep 96174215 = 144261323) B144261323
theorem B64116143 : Blo 2223435 64116143 := bstep (se 1 (by rfl) ⟨48087107, by rfl⟩ : syracuseStep 64116143 = 96174215) B96174215
theorem B42744095 : Blo 2223435 42744095 := bstep (se 1 (by rfl) ⟨32058071, by rfl⟩ : syracuseStep 42744095 = 64116143) B64116143
theorem B28496063 : Blo 2223435 28496063 := bstep (se 1 (by rfl) ⟨21372047, by rfl⟩ : syracuseStep 28496063 = 42744095) B42744095
theorem B18997375 : Blo 2223435 18997375 := bstep (se 1 (by rfl) ⟨14248031, by rfl⟩ : syracuseStep 18997375 = 28496063) B28496063
theorem B25329833 : Blo 2223435 25329833 := bstep (se 2 (by rfl) ⟨9498687, by rfl⟩ : syracuseStep 25329833 = 18997375) B18997375
theorem B16886555 : Blo 2223435 16886555 := bstep (se 1 (by rfl) ⟨12664916, by rfl⟩ : syracuseStep 16886555 = 25329833) B25329833
theorem B11257703 : Blo 2223435 11257703 := bstep (se 1 (by rfl) ⟨8443277, by rfl⟩ : syracuseStep 11257703 = 16886555) B16886555
theorem B7505135 : Blo 2223435 7505135 := bstep (se 1 (by rfl) ⟨5628851, by rfl⟩ : syracuseStep 7505135 = 11257703) B11257703
theorem B5003423 : Blo 2223435 5003423 := bstep (se 1 (by rfl) ⟨3752567, by rfl⟩ : syracuseStep 5003423 = 7505135) B7505135
theorem B3335615 : Blo 2223435 3335615 := bstep (se 1 (by rfl) ⟨2501711, by rfl⟩ : syracuseStep 3335615 = 5003423) B5003423
theorem B2223743 : Blo 2223435 2223743 := bstep (se 1 (by rfl) ⟨1667807, by rfl⟩ : syracuseStep 2223743 = 3335615) B3335615
theorem B3335621 : Blo 2223435 3335621 := bbase (se 4 (by rfl) ⟨312714, by rfl⟩ : syracuseStep 3335621 = 625429) (by norm_num)
theorem B2223747 : Blo 2223435 2223747 := bstep (se 1 (by rfl) ⟨1667810, by rfl⟩ : syracuseStep 2223747 = 3335621) B3335621
theorem B3752581 : Blo 2223435 3752581 := bbase (se 4 (by rfl) ⟨351804, by rfl⟩ : syracuseStep 3752581 = 703609) (by norm_num)
theorem B5003441 : Blo 2223435 5003441 := bstep (se 2 (by rfl) ⟨1876290, by rfl⟩ : syracuseStep 5003441 = 3752581) B3752581
theorem B3335627 : Blo 2223435 3335627 := bstep (se 1 (by rfl) ⟨2501720, by rfl⟩ : syracuseStep 3335627 = 5003441) B5003441
theorem B2223751 : Blo 2223435 2223751 := bstep (se 1 (by rfl) ⟨1667813, by rfl⟩ : syracuseStep 2223751 = 3335627) B3335627
theorem B2501725 : Blo 2223435 2501725 := bbase (se 3 (by rfl) ⟨469073, by rfl⟩ : syracuseStep 2501725 = 938147) (by norm_num)
theorem B3335633 : Blo 2223435 3335633 := bstep (se 2 (by rfl) ⟨1250862, by rfl⟩ : syracuseStep 3335633 = 2501725) B2501725
theorem B2223755 : Blo 2223435 2223755 := bstep (se 1 (by rfl) ⟨1667816, by rfl⟩ : syracuseStep 2223755 = 3335633) B3335633
theorem B7505189 : Blo 2223435 7505189 := bbase (se 4 (by rfl) ⟨703611, by rfl⟩ : syracuseStep 7505189 = 1407223) (by norm_num)
theorem B5003459 : Blo 2223435 5003459 := bstep (se 1 (by rfl) ⟨3752594, by rfl⟩ : syracuseStep 5003459 = 7505189) B7505189
theorem B3335639 : Blo 2223435 3335639 := bstep (se 1 (by rfl) ⟨2501729, by rfl⟩ : syracuseStep 3335639 = 5003459) B5003459
theorem B2223759 : Blo 2223435 2223759 := bstep (se 1 (by rfl) ⟨1667819, by rfl⟩ : syracuseStep 2223759 = 3335639) B3335639
theorem B3335645 : Blo 2223435 3335645 := bbase (se 3 (by rfl) ⟨625433, by rfl⟩ : syracuseStep 3335645 = 1250867) (by norm_num)
theorem B2223763 : Blo 2223435 2223763 := bstep (se 1 (by rfl) ⟨1667822, by rfl⟩ : syracuseStep 2223763 = 3335645) B3335645
theorem B5003477 : Blo 2223435 5003477 := bbase (se 7 (by rfl) ⟨58634, by rfl⟩ : syracuseStep 5003477 = 117269) (by norm_num)
theorem B3335651 : Blo 2223435 3335651 := bstep (se 1 (by rfl) ⟨2501738, by rfl⟩ : syracuseStep 3335651 = 5003477) B5003477
theorem B2223767 : Blo 2223435 2223767 := bstep (se 1 (by rfl) ⟨1667825, by rfl⟩ : syracuseStep 2223767 = 3335651) B3335651
theorem B2535877 : Blo 2223435 2535877 := bbase (se 4 (by rfl) ⟨237738, by rfl⟩ : syracuseStep 2535877 = 475477) (by norm_num)
theorem B3381169 : Blo 2223435 3381169 := bstep (se 2 (by rfl) ⟨1267938, by rfl⟩ : syracuseStep 3381169 = 2535877) B2535877
theorem B4508225 : Blo 2223435 4508225 := bstep (se 2 (by rfl) ⟨1690584, by rfl⟩ : syracuseStep 4508225 = 3381169) B3381169
theorem B3005483 : Blo 2223435 3005483 := bstep (se 1 (by rfl) ⟨2254112, by rfl⟩ : syracuseStep 3005483 = 4508225) B4508225
theorem B8014621 : Blo 2223435 8014621 := bstep (se 3 (by rfl) ⟨1502741, by rfl⟩ : syracuseStep 8014621 = 3005483) B3005483
theorem B10686161 : Blo 2223435 10686161 := bstep (se 2 (by rfl) ⟨4007310, by rfl⟩ : syracuseStep 10686161 = 8014621) B8014621
theorem B7124107 : Blo 2223435 7124107 := bstep (se 1 (by rfl) ⟨5343080, by rfl⟩ : syracuseStep 7124107 = 10686161) B10686161
theorem B9498809 : Blo 2223435 9498809 := bstep (se 2 (by rfl) ⟨3562053, by rfl⟩ : syracuseStep 9498809 = 7124107) B7124107
theorem B6332539 : Blo 2223435 6332539 := bstep (se 1 (by rfl) ⟨4749404, by rfl⟩ : syracuseStep 6332539 = 9498809) B9498809
theorem B8443385 : Blo 2223435 8443385 := bstep (se 2 (by rfl) ⟨3166269, by rfl⟩ : syracuseStep 8443385 = 6332539) B6332539
theorem B5628923 : Blo 2223435 5628923 := bstep (se 1 (by rfl) ⟨4221692, by rfl⟩ : syracuseStep 5628923 = 8443385) B8443385
theorem B3752615 : Blo 2223435 3752615 := bstep (se 1 (by rfl) ⟨2814461, by rfl⟩ : syracuseStep 3752615 = 5628923) B5628923
theorem B2501743 : Blo 2223435 2501743 := bstep (se 1 (by rfl) ⟨1876307, by rfl⟩ : syracuseStep 2501743 = 3752615) B3752615
theorem B3335657 : Blo 2223435 3335657 := bstep (se 2 (by rfl) ⟨1250871, by rfl⟩ : syracuseStep 3335657 = 2501743) B2501743
theorem B2223771 : Blo 2223435 2223771 := bstep (se 1 (by rfl) ⟨1667828, by rfl⟩ : syracuseStep 2223771 = 3335657) B3335657
theorem B4007317 : Blo 2223435 4007317 := bbase (se 6 (by rfl) ⟨93921, by rfl⟩ : syracuseStep 4007317 = 187843) (by norm_num)
theorem B5343089 : Blo 2223435 5343089 := bstep (se 2 (by rfl) ⟨2003658, by rfl⟩ : syracuseStep 5343089 = 4007317) B4007317
theorem B14248237 : Blo 2223435 14248237 := bstep (se 3 (by rfl) ⟨2671544, by rfl⟩ : syracuseStep 14248237 = 5343089) B5343089
theorem B18997649 : Blo 2223435 18997649 := bstep (se 2 (by rfl) ⟨7124118, by rfl⟩ : syracuseStep 18997649 = 14248237) B14248237
theorem B12665099 : Blo 2223435 12665099 := bstep (se 1 (by rfl) ⟨9498824, by rfl⟩ : syracuseStep 12665099 = 18997649) B18997649
theorem B8443399 : Blo 2223435 8443399 := bstep (se 1 (by rfl) ⟨6332549, by rfl⟩ : syracuseStep 8443399 = 12665099) B12665099
theorem B11257865 : Blo 2223435 11257865 := bstep (se 2 (by rfl) ⟨4221699, by rfl⟩ : syracuseStep 11257865 = 8443399) B8443399
theorem B7505243 : Blo 2223435 7505243 := bstep (se 1 (by rfl) ⟨5628932, by rfl⟩ : syracuseStep 7505243 = 11257865) B11257865
theorem B5003495 : Blo 2223435 5003495 := bstep (se 1 (by rfl) ⟨3752621, by rfl⟩ : syracuseStep 5003495 = 7505243) B7505243
theorem B3335663 : Blo 2223435 3335663 := bstep (se 1 (by rfl) ⟨2501747, by rfl⟩ : syracuseStep 3335663 = 5003495) B5003495
theorem B2223775 : Blo 2223435 2223775 := bstep (se 1 (by rfl) ⟨1667831, by rfl⟩ : syracuseStep 2223775 = 3335663) B3335663
theorem B3335669 : Blo 2223435 3335669 := bbase (se 5 (by rfl) ⟨156359, by rfl⟩ : syracuseStep 3335669 = 312719) (by norm_num)
theorem B2223779 : Blo 2223435 2223779 := bstep (se 1 (by rfl) ⟨1667834, by rfl⟩ : syracuseStep 2223779 = 3335669) B3335669
theorem B4007333 : Blo 2223435 4007333 := bbase (se 4 (by rfl) ⟨375687, by rfl⟩ : syracuseStep 4007333 = 751375) (by norm_num)
theorem B2671555 : Blo 2223435 2671555 := bstep (se 1 (by rfl) ⟨2003666, by rfl⟩ : syracuseStep 2671555 = 4007333) B4007333
theorem B3562073 : Blo 2223435 3562073 := bstep (se 2 (by rfl) ⟨1335777, by rfl⟩ : syracuseStep 3562073 = 2671555) B2671555
theorem B2374715 : Blo 2223435 2374715 := bstep (se 1 (by rfl) ⟨1781036, by rfl⟩ : syracuseStep 2374715 = 3562073) B3562073
theorem B6332573 : Blo 2223435 6332573 := bstep (se 3 (by rfl) ⟨1187357, by rfl⟩ : syracuseStep 6332573 = 2374715) B2374715
theorem B4221715 : Blo 2223435 4221715 := bstep (se 1 (by rfl) ⟨3166286, by rfl⟩ : syracuseStep 4221715 = 6332573) B6332573
theorem B5628953 : Blo 2223435 5628953 := bstep (se 2 (by rfl) ⟨2110857, by rfl⟩ : syracuseStep 5628953 = 4221715) B4221715
theorem B3752635 : Blo 2223435 3752635 := bstep (se 1 (by rfl) ⟨2814476, by rfl⟩ : syracuseStep 3752635 = 5628953) B5628953
theorem B5003513 : Blo 2223435 5003513 := bstep (se 2 (by rfl) ⟨1876317, by rfl⟩ : syracuseStep 5003513 = 3752635) B3752635
theorem B3335675 : Blo 2223435 3335675 := bstep (se 1 (by rfl) ⟨2501756, by rfl⟩ : syracuseStep 3335675 = 5003513) B5003513
theorem B2223783 : Blo 2223435 2223783 := bstep (se 1 (by rfl) ⟨1667837, by rfl⟩ : syracuseStep 2223783 = 3335675) B3335675
theorem B2501761 : Blo 2223435 2501761 := bbase (se 2 (by rfl) ⟨938160, by rfl⟩ : syracuseStep 2501761 = 1876321) (by norm_num)
theorem B3335681 : Blo 2223435 3335681 := bstep (se 2 (by rfl) ⟨1250880, by rfl⟩ : syracuseStep 3335681 = 2501761) B2501761
theorem B2223787 : Blo 2223435 2223787 := bstep (se 1 (by rfl) ⟨1667840, by rfl⟩ : syracuseStep 2223787 = 3335681) B3335681
theorem B5628973 : Blo 2223435 5628973 := bbase (se 3 (by rfl) ⟨1055432, by rfl⟩ : syracuseStep 5628973 = 2110865) (by norm_num)
theorem B7505297 : Blo 2223435 7505297 := bstep (se 2 (by rfl) ⟨2814486, by rfl⟩ : syracuseStep 7505297 = 5628973) B5628973
theorem B5003531 : Blo 2223435 5003531 := bstep (se 1 (by rfl) ⟨3752648, by rfl⟩ : syracuseStep 5003531 = 7505297) B7505297
theorem B3335687 : Blo 2223435 3335687 := bstep (se 1 (by rfl) ⟨2501765, by rfl⟩ : syracuseStep 3335687 = 5003531) B5003531
theorem B2223791 : Blo 2223435 2223791 := bstep (se 1 (by rfl) ⟨1667843, by rfl⟩ : syracuseStep 2223791 = 3335687) B3335687
theorem B3335693 : Blo 2223435 3335693 := bbase (se 3 (by rfl) ⟨625442, by rfl⟩ : syracuseStep 3335693 = 1250885) (by norm_num)
theorem B2223795 : Blo 2223435 2223795 := bstep (se 1 (by rfl) ⟨1667846, by rfl⟩ : syracuseStep 2223795 = 3335693) B3335693
theorem B5003549 : Blo 2223435 5003549 := bbase (se 3 (by rfl) ⟨938165, by rfl⟩ : syracuseStep 5003549 = 1876331) (by norm_num)
theorem B3335699 : Blo 2223435 3335699 := bstep (se 1 (by rfl) ⟨2501774, by rfl⟩ : syracuseStep 3335699 = 5003549) B5003549
theorem B2223799 : Blo 2223435 2223799 := bstep (se 1 (by rfl) ⟨1667849, by rfl⟩ : syracuseStep 2223799 = 3335699) B3335699
theorem B3752669 : Blo 2223435 3752669 := bbase (se 3 (by rfl) ⟨703625, by rfl⟩ : syracuseStep 3752669 = 1407251) (by norm_num)
theorem B2501779 : Blo 2223435 2501779 := bstep (se 1 (by rfl) ⟨1876334, by rfl⟩ : syracuseStep 2501779 = 3752669) B3752669
theorem B3335705 : Blo 2223435 3335705 := bstep (se 2 (by rfl) ⟨1250889, by rfl⟩ : syracuseStep 3335705 = 2501779) B2501779
theorem B2223803 : Blo 2223435 2223803 := bstep (se 1 (by rfl) ⟨1667852, by rfl⟩ : syracuseStep 2223803 = 3335705) B3335705
theorem B2407141 : Blo 2223435 2407141 := bbase (se 4 (by rfl) ⟨225669, by rfl⟩ : syracuseStep 2407141 = 451339) (by norm_num)
theorem B12838085 : Blo 2223435 12838085 := bstep (se 4 (by rfl) ⟨1203570, by rfl⟩ : syracuseStep 12838085 = 2407141) B2407141
theorem B8558723 : Blo 2223435 8558723 := bstep (se 1 (by rfl) ⟨6419042, by rfl⟩ : syracuseStep 8558723 = 12838085) B12838085
theorem B5705815 : Blo 2223435 5705815 := bstep (se 1 (by rfl) ⟨4279361, by rfl⟩ : syracuseStep 5705815 = 8558723) B8558723
theorem B7607753 : Blo 2223435 7607753 := bstep (se 2 (by rfl) ⟨2852907, by rfl⟩ : syracuseStep 7607753 = 5705815) B5705815
theorem B5071835 : Blo 2223435 5071835 := bstep (se 1 (by rfl) ⟨3803876, by rfl⟩ : syracuseStep 5071835 = 7607753) B7607753
theorem B13524893 : Blo 2223435 13524893 := bstep (se 3 (by rfl) ⟨2535917, by rfl⟩ : syracuseStep 13524893 = 5071835) B5071835
theorem B9016595 : Blo 2223435 9016595 := bstep (se 1 (by rfl) ⟨6762446, by rfl⟩ : syracuseStep 9016595 = 13524893) B13524893
theorem B6011063 : Blo 2223435 6011063 := bstep (se 1 (by rfl) ⟨4508297, by rfl⟩ : syracuseStep 6011063 = 9016595) B9016595
theorem B4007375 : Blo 2223435 4007375 := bstep (se 1 (by rfl) ⟨3005531, by rfl⟩ : syracuseStep 4007375 = 6011063) B6011063
theorem B2671583 : Blo 2223435 2671583 := bstep (se 1 (by rfl) ⟨2003687, by rfl⟩ : syracuseStep 2671583 = 4007375) B4007375
theorem B7124221 : Blo 2223435 7124221 := bstep (se 3 (by rfl) ⟨1335791, by rfl⟩ : syracuseStep 7124221 = 2671583) B2671583
theorem B9498961 : Blo 2223435 9498961 := bstep (se 2 (by rfl) ⟨3562110, by rfl⟩ : syracuseStep 9498961 = 7124221) B7124221
theorem B12665281 : Blo 2223435 12665281 := bstep (se 2 (by rfl) ⟨4749480, by rfl⟩ : syracuseStep 12665281 = 9498961) B9498961
theorem B16887041 : Blo 2223435 16887041 := bstep (se 2 (by rfl) ⟨6332640, by rfl⟩ : syracuseStep 16887041 = 12665281) B12665281
theorem B11258027 : Blo 2223435 11258027 := bstep (se 1 (by rfl) ⟨8443520, by rfl⟩ : syracuseStep 11258027 = 16887041) B16887041
theorem B7505351 : Blo 2223435 7505351 := bstep (se 1 (by rfl) ⟨5629013, by rfl⟩ : syracuseStep 7505351 = 11258027) B11258027
theorem B5003567 : Blo 2223435 5003567 := bstep (se 1 (by rfl) ⟨3752675, by rfl⟩ : syracuseStep 5003567 = 7505351) B7505351
theorem B3335711 : Blo 2223435 3335711 := bstep (se 1 (by rfl) ⟨2501783, by rfl⟩ : syracuseStep 3335711 = 5003567) B5003567
theorem B2223807 : Blo 2223435 2223807 := bstep (se 1 (by rfl) ⟨1667855, by rfl⟩ : syracuseStep 2223807 = 3335711) B3335711
theorem B3335717 : Blo 2223435 3335717 := bbase (se 4 (by rfl) ⟨312723, by rfl⟩ : syracuseStep 3335717 = 625447) (by norm_num)
theorem B2223811 : Blo 2223435 2223811 := bstep (se 1 (by rfl) ⟨1667858, by rfl⟩ : syracuseStep 2223811 = 3335717) B3335717
theorem B2814517 : Blo 2223435 2814517 := bbase (se 5 (by rfl) ⟨131930, by rfl⟩ : syracuseStep 2814517 = 263861) (by norm_num)
theorem B3752689 : Blo 2223435 3752689 := bstep (se 2 (by rfl) ⟨1407258, by rfl⟩ : syracuseStep 3752689 = 2814517) B2814517
theorem B5003585 : Blo 2223435 5003585 := bstep (se 2 (by rfl) ⟨1876344, by rfl⟩ : syracuseStep 5003585 = 3752689) B3752689
theorem B3335723 : Blo 2223435 3335723 := bstep (se 1 (by rfl) ⟨2501792, by rfl⟩ : syracuseStep 3335723 = 5003585) B5003585
theorem B2223815 : Blo 2223435 2223815 := bstep (se 1 (by rfl) ⟨1667861, by rfl⟩ : syracuseStep 2223815 = 3335723) B3335723
theorem B2501797 : Blo 2223435 2501797 := bbase (se 4 (by rfl) ⟨234543, by rfl⟩ : syracuseStep 2501797 = 469087) (by norm_num)
theorem B3335729 : Blo 2223435 3335729 := bstep (se 2 (by rfl) ⟨1250898, by rfl⟩ : syracuseStep 3335729 = 2501797) B2501797
theorem B2223819 : Blo 2223435 2223819 := bstep (se 1 (by rfl) ⟨1667864, by rfl⟩ : syracuseStep 2223819 = 3335729) B3335729
theorem B21372821 : Blo 2223435 21372821 := bbase (se 6 (by rfl) ⟨500925, by rfl⟩ : syracuseStep 21372821 = 1001851) (by norm_num)
theorem B14248547 : Blo 2223435 14248547 := bstep (se 1 (by rfl) ⟨10686410, by rfl⟩ : syracuseStep 14248547 = 21372821) B21372821
theorem B9499031 : Blo 2223435 9499031 := bstep (se 1 (by rfl) ⟨7124273, by rfl⟩ : syracuseStep 9499031 = 14248547) B14248547
theorem B6332687 : Blo 2223435 6332687 := bstep (se 1 (by rfl) ⟨4749515, by rfl⟩ : syracuseStep 6332687 = 9499031) B9499031
theorem B4221791 : Blo 2223435 4221791 := bstep (se 1 (by rfl) ⟨3166343, by rfl⟩ : syracuseStep 4221791 = 6332687) B6332687
theorem B2814527 : Blo 2223435 2814527 := bstep (se 1 (by rfl) ⟨2110895, by rfl⟩ : syracuseStep 2814527 = 4221791) B4221791
theorem B7505405 : Blo 2223435 7505405 := bstep (se 3 (by rfl) ⟨1407263, by rfl⟩ : syracuseStep 7505405 = 2814527) B2814527
theorem B5003603 : Blo 2223435 5003603 := bstep (se 1 (by rfl) ⟨3752702, by rfl⟩ : syracuseStep 5003603 = 7505405) B7505405
theorem B3335735 : Blo 2223435 3335735 := bstep (se 1 (by rfl) ⟨2501801, by rfl⟩ : syracuseStep 3335735 = 5003603) B5003603
theorem B2223823 : Blo 2223435 2223823 := bstep (se 1 (by rfl) ⟨1667867, by rfl⟩ : syracuseStep 2223823 = 3335735) B3335735
theorem B3335741 : Blo 2223435 3335741 := bbase (se 3 (by rfl) ⟨625451, by rfl⟩ : syracuseStep 3335741 = 1250903) (by norm_num)
theorem B2223827 : Blo 2223435 2223827 := bstep (se 1 (by rfl) ⟨1667870, by rfl⟩ : syracuseStep 2223827 = 3335741) B3335741
theorem B5003621 : Blo 2223435 5003621 := bbase (se 4 (by rfl) ⟨469089, by rfl⟩ : syracuseStep 5003621 = 938179) (by norm_num)
theorem B3335747 : Blo 2223435 3335747 := bstep (se 1 (by rfl) ⟨2501810, by rfl⟩ : syracuseStep 3335747 = 5003621) B5003621
theorem B2223831 : Blo 2223435 2223831 := bstep (se 1 (by rfl) ⟨1667873, by rfl⟩ : syracuseStep 2223831 = 3335747) B3335747
theorem B5629085 : Blo 2223435 5629085 := bbase (se 3 (by rfl) ⟨1055453, by rfl⟩ : syracuseStep 5629085 = 2110907) (by norm_num)
theorem B3752723 : Blo 2223435 3752723 := bstep (se 1 (by rfl) ⟨2814542, by rfl⟩ : syracuseStep 3752723 = 5629085) B5629085
theorem B2501815 : Blo 2223435 2501815 := bstep (se 1 (by rfl) ⟨1876361, by rfl⟩ : syracuseStep 2501815 = 3752723) B3752723
theorem B3335753 : Blo 2223435 3335753 := bstep (se 2 (by rfl) ⟨1250907, by rfl⟩ : syracuseStep 3335753 = 2501815) B2501815
theorem B2223835 : Blo 2223435 2223835 := bstep (se 1 (by rfl) ⟨1667876, by rfl⟩ : syracuseStep 2223835 = 3335753) B3335753
theorem B4221821 : Blo 2223435 4221821 := bbase (se 3 (by rfl) ⟨791591, by rfl⟩ : syracuseStep 4221821 = 1583183) (by norm_num)
theorem B11258189 : Blo 2223435 11258189 := bstep (se 3 (by rfl) ⟨2110910, by rfl⟩ : syracuseStep 11258189 = 4221821) B4221821
theorem B7505459 : Blo 2223435 7505459 := bstep (se 1 (by rfl) ⟨5629094, by rfl⟩ : syracuseStep 7505459 = 11258189) B11258189
theorem B5003639 : Blo 2223435 5003639 := bstep (se 1 (by rfl) ⟨3752729, by rfl⟩ : syracuseStep 5003639 = 7505459) B7505459
theorem B3335759 : Blo 2223435 3335759 := bstep (se 1 (by rfl) ⟨2501819, by rfl⟩ : syracuseStep 3335759 = 5003639) B5003639
theorem B2223839 : Blo 2223435 2223839 := bstep (se 1 (by rfl) ⟨1667879, by rfl⟩ : syracuseStep 2223839 = 3335759) B3335759
theorem B3335765 : Blo 2223435 3335765 := bbase (se 8 (by rfl) ⟨19545, by rfl⟩ : syracuseStep 3335765 = 39091) (by norm_num)
theorem B2223843 : Blo 2223435 2223843 := bstep (se 1 (by rfl) ⟨1667882, by rfl⟩ : syracuseStep 2223843 = 3335765) B3335765
theorem B22823669 : Blo 2223435 22823669 := bbase (se 5 (by rfl) ⟨1069859, by rfl⟩ : syracuseStep 22823669 = 2139719) (by norm_num)
theorem B15215779 : Blo 2223435 15215779 := bstep (se 1 (by rfl) ⟨11411834, by rfl⟩ : syracuseStep 15215779 = 22823669) B22823669
theorem B20287705 : Blo 2223435 20287705 := bstep (se 2 (by rfl) ⟨7607889, by rfl⟩ : syracuseStep 20287705 = 15215779) B15215779
theorem B27050273 : Blo 2223435 27050273 := bstep (se 2 (by rfl) ⟨10143852, by rfl⟩ : syracuseStep 27050273 = 20287705) B20287705
theorem B18033515 : Blo 2223435 18033515 := bstep (se 1 (by rfl) ⟨13525136, by rfl⟩ : syracuseStep 18033515 = 27050273) B27050273
theorem B12022343 : Blo 2223435 12022343 := bstep (se 1 (by rfl) ⟨9016757, by rfl⟩ : syracuseStep 12022343 = 18033515) B18033515
theorem B8014895 : Blo 2223435 8014895 := bstep (se 1 (by rfl) ⟨6011171, by rfl⟩ : syracuseStep 8014895 = 12022343) B12022343
theorem B5343263 : Blo 2223435 5343263 := bstep (se 1 (by rfl) ⟨4007447, by rfl⟩ : syracuseStep 5343263 = 8014895) B8014895
theorem B3562175 : Blo 2223435 3562175 := bstep (se 1 (by rfl) ⟨2671631, by rfl⟩ : syracuseStep 3562175 = 5343263) B5343263
theorem B9499133 : Blo 2223435 9499133 := bstep (se 3 (by rfl) ⟨1781087, by rfl⟩ : syracuseStep 9499133 = 3562175) B3562175
theorem B6332755 : Blo 2223435 6332755 := bstep (se 1 (by rfl) ⟨4749566, by rfl⟩ : syracuseStep 6332755 = 9499133) B9499133
theorem B8443673 : Blo 2223435 8443673 := bstep (se 2 (by rfl) ⟨3166377, by rfl⟩ : syracuseStep 8443673 = 6332755) B6332755
theorem B5629115 : Blo 2223435 5629115 := bstep (se 1 (by rfl) ⟨4221836, by rfl⟩ : syracuseStep 5629115 = 8443673) B8443673
theorem B3752743 : Blo 2223435 3752743 := bstep (se 1 (by rfl) ⟨2814557, by rfl⟩ : syracuseStep 3752743 = 5629115) B5629115
theorem B5003657 : Blo 2223435 5003657 := bstep (se 2 (by rfl) ⟨1876371, by rfl⟩ : syracuseStep 5003657 = 3752743) B3752743
theorem B3335771 : Blo 2223435 3335771 := bstep (se 1 (by rfl) ⟨2501828, by rfl⟩ : syracuseStep 3335771 = 5003657) B5003657
theorem B2223847 : Blo 2223435 2223847 := bstep (se 1 (by rfl) ⟨1667885, by rfl⟩ : syracuseStep 2223847 = 3335771) B3335771
theorem B2501833 : Blo 2223435 2501833 := bbase (se 2 (by rfl) ⟨938187, by rfl⟩ : syracuseStep 2501833 = 1876375) (by norm_num)
theorem B3335777 : Blo 2223435 3335777 := bstep (se 2 (by rfl) ⟨1250916, by rfl⟩ : syracuseStep 3335777 = 2501833) B2501833
theorem B2223851 : Blo 2223435 2223851 := bstep (se 1 (by rfl) ⟨1667888, by rfl⟩ : syracuseStep 2223851 = 3335777) B3335777
theorem B16029845 : Blo 2223435 16029845 := bbase (se 6 (by rfl) ⟨375699, by rfl⟩ : syracuseStep 16029845 = 751399) (by norm_num)
theorem B10686563 : Blo 2223435 10686563 := bstep (se 1 (by rfl) ⟨8014922, by rfl⟩ : syracuseStep 10686563 = 16029845) B16029845
theorem B7124375 : Blo 2223435 7124375 := bstep (se 1 (by rfl) ⟨5343281, by rfl⟩ : syracuseStep 7124375 = 10686563) B10686563
theorem B18998333 : Blo 2223435 18998333 := bstep (se 3 (by rfl) ⟨3562187, by rfl⟩ : syracuseStep 18998333 = 7124375) B7124375
theorem B12665555 : Blo 2223435 12665555 := bstep (se 1 (by rfl) ⟨9499166, by rfl⟩ : syracuseStep 12665555 = 18998333) B18998333
theorem B8443703 : Blo 2223435 8443703 := bstep (se 1 (by rfl) ⟨6332777, by rfl⟩ : syracuseStep 8443703 = 12665555) B12665555
theorem B5629135 : Blo 2223435 5629135 := bstep (se 1 (by rfl) ⟨4221851, by rfl⟩ : syracuseStep 5629135 = 8443703) B8443703
theorem B7505513 : Blo 2223435 7505513 := bstep (se 2 (by rfl) ⟨2814567, by rfl⟩ : syracuseStep 7505513 = 5629135) B5629135
theorem B5003675 : Blo 2223435 5003675 := bstep (se 1 (by rfl) ⟨3752756, by rfl⟩ : syracuseStep 5003675 = 7505513) B7505513
theorem B3335783 : Blo 2223435 3335783 := bstep (se 1 (by rfl) ⟨2501837, by rfl⟩ : syracuseStep 3335783 = 5003675) B5003675
theorem B2223855 : Blo 2223435 2223855 := bstep (se 1 (by rfl) ⟨1667891, by rfl⟩ : syracuseStep 2223855 = 3335783) B3335783
theorem B3335789 : Blo 2223435 3335789 := bbase (se 3 (by rfl) ⟨625460, by rfl⟩ : syracuseStep 3335789 = 1250921) (by norm_num)
theorem B2223859 : Blo 2223435 2223859 := bstep (se 1 (by rfl) ⟨1667894, by rfl⟩ : syracuseStep 2223859 = 3335789) B3335789
theorem B5003693 : Blo 2223435 5003693 := bbase (se 3 (by rfl) ⟨938192, by rfl⟩ : syracuseStep 5003693 = 1876385) (by norm_num)
theorem B3335795 : Blo 2223435 3335795 := bstep (se 1 (by rfl) ⟨2501846, by rfl⟩ : syracuseStep 3335795 = 5003693) B5003693
theorem B2223863 : Blo 2223435 2223863 := bstep (se 1 (by rfl) ⟨1667897, by rfl⟩ : syracuseStep 2223863 = 3335795) B3335795
theorem B2374805 : Blo 2223435 2374805 := bbase (se 6 (by rfl) ⟨55659, by rfl⟩ : syracuseStep 2374805 = 111319) (by norm_num)
theorem B6332813 : Blo 2223435 6332813 := bstep (se 3 (by rfl) ⟨1187402, by rfl⟩ : syracuseStep 6332813 = 2374805) B2374805
theorem B4221875 : Blo 2223435 4221875 := bstep (se 1 (by rfl) ⟨3166406, by rfl⟩ : syracuseStep 4221875 = 6332813) B6332813
theorem B2814583 : Blo 2223435 2814583 := bstep (se 1 (by rfl) ⟨2110937, by rfl⟩ : syracuseStep 2814583 = 4221875) B4221875
theorem B3752777 : Blo 2223435 3752777 := bstep (se 2 (by rfl) ⟨1407291, by rfl⟩ : syracuseStep 3752777 = 2814583) B2814583
theorem B2501851 : Blo 2223435 2501851 := bstep (se 1 (by rfl) ⟨1876388, by rfl⟩ : syracuseStep 2501851 = 3752777) B3752777
theorem B3335801 : Blo 2223435 3335801 := bstep (se 2 (by rfl) ⟨1250925, by rfl⟩ : syracuseStep 3335801 = 2501851) B2501851
theorem B2223867 : Blo 2223435 2223867 := bstep (se 1 (by rfl) ⟨1667900, by rfl⟩ : syracuseStep 2223867 = 3335801) B3335801
theorem B8558965 : Blo 2223435 8558965 := bbase (se 5 (by rfl) ⟨401201, by rfl⟩ : syracuseStep 8558965 = 802403) (by norm_num)
theorem B45647813 : Blo 2223435 45647813 := bstep (se 4 (by rfl) ⟨4279482, by rfl⟩ : syracuseStep 45647813 = 8558965) B8558965
theorem B30431875 : Blo 2223435 30431875 := bstep (se 1 (by rfl) ⟨22823906, by rfl⟩ : syracuseStep 30431875 = 45647813) B45647813
theorem B40575833 : Blo 2223435 40575833 := bstep (se 2 (by rfl) ⟨15215937, by rfl⟩ : syracuseStep 40575833 = 30431875) B30431875
theorem B27050555 : Blo 2223435 27050555 := bstep (se 1 (by rfl) ⟨20287916, by rfl⟩ : syracuseStep 27050555 = 40575833) B40575833
theorem B72134813 : Blo 2223435 72134813 := bstep (se 3 (by rfl) ⟨13525277, by rfl⟩ : syracuseStep 72134813 = 27050555) B27050555
theorem B48089875 : Blo 2223435 48089875 := bstep (se 1 (by rfl) ⟨36067406, by rfl⟩ : syracuseStep 48089875 = 72134813) B72134813
theorem B64119833 : Blo 2223435 64119833 := bstep (se 2 (by rfl) ⟨24044937, by rfl⟩ : syracuseStep 64119833 = 48089875) B48089875
theorem B42746555 : Blo 2223435 42746555 := bstep (se 1 (by rfl) ⟨32059916, by rfl⟩ : syracuseStep 42746555 = 64119833) B64119833
theorem B28497703 : Blo 2223435 28497703 := bstep (se 1 (by rfl) ⟨21373277, by rfl⟩ : syracuseStep 28497703 = 42746555) B42746555
theorem B37996937 : Blo 2223435 37996937 := bstep (se 2 (by rfl) ⟨14248851, by rfl⟩ : syracuseStep 37996937 = 28497703) B28497703
theorem B25331291 : Blo 2223435 25331291 := bstep (se 1 (by rfl) ⟨18998468, by rfl⟩ : syracuseStep 25331291 = 37996937) B37996937
theorem B16887527 : Blo 2223435 16887527 := bstep (se 1 (by rfl) ⟨12665645, by rfl⟩ : syracuseStep 16887527 = 25331291) B25331291
theorem B11258351 : Blo 2223435 11258351 := bstep (se 1 (by rfl) ⟨8443763, by rfl⟩ : syracuseStep 11258351 = 16887527) B16887527
theorem B7505567 : Blo 2223435 7505567 := bstep (se 1 (by rfl) ⟨5629175, by rfl⟩ : syracuseStep 7505567 = 11258351) B11258351
theorem B5003711 : Blo 2223435 5003711 := bstep (se 1 (by rfl) ⟨3752783, by rfl⟩ : syracuseStep 5003711 = 7505567) B7505567
theorem B3335807 : Blo 2223435 3335807 := bstep (se 1 (by rfl) ⟨2501855, by rfl⟩ : syracuseStep 3335807 = 5003711) B5003711
theorem B2223871 : Blo 2223435 2223871 := bstep (se 1 (by rfl) ⟨1667903, by rfl⟩ : syracuseStep 2223871 = 3335807) B3335807
theorem B3335813 : Blo 2223435 3335813 := bbase (se 4 (by rfl) ⟨312732, by rfl⟩ : syracuseStep 3335813 = 625465) (by norm_num)
theorem B2223875 : Blo 2223435 2223875 := bstep (se 1 (by rfl) ⟨1667906, by rfl⟩ : syracuseStep 2223875 = 3335813) B3335813
theorem B3752797 : Blo 2223435 3752797 := bbase (se 3 (by rfl) ⟨703649, by rfl⟩ : syracuseStep 3752797 = 1407299) (by norm_num)
theorem B5003729 : Blo 2223435 5003729 := bstep (se 2 (by rfl) ⟨1876398, by rfl⟩ : syracuseStep 5003729 = 3752797) B3752797
theorem B3335819 : Blo 2223435 3335819 := bstep (se 1 (by rfl) ⟨2501864, by rfl⟩ : syracuseStep 3335819 = 5003729) B5003729
theorem B2223879 : Blo 2223435 2223879 := bstep (se 1 (by rfl) ⟨1667909, by rfl⟩ : syracuseStep 2223879 = 3335819) B3335819
theorem B2501869 : Blo 2223435 2501869 := bbase (se 3 (by rfl) ⟨469100, by rfl⟩ : syracuseStep 2501869 = 938201) (by norm_num)
theorem B3335825 : Blo 2223435 3335825 := bstep (se 2 (by rfl) ⟨1250934, by rfl⟩ : syracuseStep 3335825 = 2501869) B2501869
theorem B2223883 : Blo 2223435 2223883 := bstep (se 1 (by rfl) ⟨1667912, by rfl⟩ : syracuseStep 2223883 = 3335825) B3335825
theorem B7505621 : Blo 2223435 7505621 := bbase (se 7 (by rfl) ⟨87956, by rfl⟩ : syracuseStep 7505621 = 175913) (by norm_num)
theorem B5003747 : Blo 2223435 5003747 := bstep (se 1 (by rfl) ⟨3752810, by rfl⟩ : syracuseStep 5003747 = 7505621) B7505621
theorem B3335831 : Blo 2223435 3335831 := bstep (se 1 (by rfl) ⟨2501873, by rfl⟩ : syracuseStep 3335831 = 5003747) B5003747
theorem B2223887 : Blo 2223435 2223887 := bstep (se 1 (by rfl) ⟨1667915, by rfl⟩ : syracuseStep 2223887 = 3335831) B3335831
theorem B3335837 : Blo 2223435 3335837 := bbase (se 3 (by rfl) ⟨625469, by rfl⟩ : syracuseStep 3335837 = 1250939) (by norm_num)
theorem B2223891 : Blo 2223435 2223891 := bstep (se 1 (by rfl) ⟨1667918, by rfl⟩ : syracuseStep 2223891 = 3335837) B3335837
theorem B5003765 : Blo 2223435 5003765 := bbase (se 5 (by rfl) ⟨234551, by rfl⟩ : syracuseStep 5003765 = 469103) (by norm_num)
theorem B3335843 : Blo 2223435 3335843 := bstep (se 1 (by rfl) ⟨2501882, by rfl⟩ : syracuseStep 3335843 = 5003765) B5003765
theorem B2223895 : Blo 2223435 2223895 := bstep (se 1 (by rfl) ⟨1667921, by rfl⟩ : syracuseStep 2223895 = 3335843) B3335843
theorem B2853025 : Blo 2223435 2853025 := bbase (se 2 (by rfl) ⟨1069884, by rfl⟩ : syracuseStep 2853025 = 2139769) (by norm_num)
theorem B15216133 : Blo 2223435 15216133 := bstep (se 4 (by rfl) ⟨1426512, by rfl⟩ : syracuseStep 15216133 = 2853025) B2853025
theorem B20288177 : Blo 2223435 20288177 := bstep (se 2 (by rfl) ⟨7608066, by rfl⟩ : syracuseStep 20288177 = 15216133) B15216133
theorem B13525451 : Blo 2223435 13525451 := bstep (se 1 (by rfl) ⟨10144088, by rfl⟩ : syracuseStep 13525451 = 20288177) B20288177
theorem B9016967 : Blo 2223435 9016967 := bstep (se 1 (by rfl) ⟨6762725, by rfl⟩ : syracuseStep 9016967 = 13525451) B13525451
theorem B24045245 : Blo 2223435 24045245 := bstep (se 3 (by rfl) ⟨4508483, by rfl⟩ : syracuseStep 24045245 = 9016967) B9016967
theorem B16030163 : Blo 2223435 16030163 := bstep (se 1 (by rfl) ⟨12022622, by rfl⟩ : syracuseStep 16030163 = 24045245) B24045245
theorem B42747101 : Blo 2223435 42747101 := bstep (se 3 (by rfl) ⟨8015081, by rfl⟩ : syracuseStep 42747101 = 16030163) B16030163
theorem B28498067 : Blo 2223435 28498067 := bstep (se 1 (by rfl) ⟨21373550, by rfl⟩ : syracuseStep 28498067 = 42747101) B42747101
theorem B18998711 : Blo 2223435 18998711 := bstep (se 1 (by rfl) ⟨14249033, by rfl⟩ : syracuseStep 18998711 = 28498067) B28498067
theorem B12665807 : Blo 2223435 12665807 := bstep (se 1 (by rfl) ⟨9499355, by rfl⟩ : syracuseStep 12665807 = 18998711) B18998711
theorem B8443871 : Blo 2223435 8443871 := bstep (se 1 (by rfl) ⟨6332903, by rfl⟩ : syracuseStep 8443871 = 12665807) B12665807
theorem B5629247 : Blo 2223435 5629247 := bstep (se 1 (by rfl) ⟨4221935, by rfl⟩ : syracuseStep 5629247 = 8443871) B8443871
theorem B3752831 : Blo 2223435 3752831 := bstep (se 1 (by rfl) ⟨2814623, by rfl⟩ : syracuseStep 3752831 = 5629247) B5629247
theorem B2501887 : Blo 2223435 2501887 := bstep (se 1 (by rfl) ⟨1876415, by rfl⟩ : syracuseStep 2501887 = 3752831) B3752831
theorem B3335849 : Blo 2223435 3335849 := bstep (se 2 (by rfl) ⟨1250943, by rfl⟩ : syracuseStep 3335849 = 2501887) B2501887
theorem B2223899 : Blo 2223435 2223899 := bstep (se 1 (by rfl) ⟨1667924, by rfl⟩ : syracuseStep 2223899 = 3335849) B3335849
theorem B4007549 : Blo 2223435 4007549 := bbase (se 3 (by rfl) ⟨751415, by rfl⟩ : syracuseStep 4007549 = 1502831) (by norm_num)
theorem B2671699 : Blo 2223435 2671699 := bstep (se 1 (by rfl) ⟨2003774, by rfl⟩ : syracuseStep 2671699 = 4007549) B4007549
theorem B3562265 : Blo 2223435 3562265 := bstep (se 2 (by rfl) ⟨1335849, by rfl⟩ : syracuseStep 3562265 = 2671699) B2671699
theorem B2374843 : Blo 2223435 2374843 := bstep (se 1 (by rfl) ⟨1781132, by rfl⟩ : syracuseStep 2374843 = 3562265) B3562265
theorem B3166457 : Blo 2223435 3166457 := bstep (se 2 (by rfl) ⟨1187421, by rfl⟩ : syracuseStep 3166457 = 2374843) B2374843
theorem B8443885 : Blo 2223435 8443885 := bstep (se 3 (by rfl) ⟨1583228, by rfl⟩ : syracuseStep 8443885 = 3166457) B3166457
theorem B11258513 : Blo 2223435 11258513 := bstep (se 2 (by rfl) ⟨4221942, by rfl⟩ : syracuseStep 11258513 = 8443885) B8443885
theorem B7505675 : Blo 2223435 7505675 := bstep (se 1 (by rfl) ⟨5629256, by rfl⟩ : syracuseStep 7505675 = 11258513) B11258513
theorem B5003783 : Blo 2223435 5003783 := bstep (se 1 (by rfl) ⟨3752837, by rfl⟩ : syracuseStep 5003783 = 7505675) B7505675
theorem B3335855 : Blo 2223435 3335855 := bstep (se 1 (by rfl) ⟨2501891, by rfl⟩ : syracuseStep 3335855 = 5003783) B5003783
theorem B2223903 : Blo 2223435 2223903 := bstep (se 1 (by rfl) ⟨1667927, by rfl⟩ : syracuseStep 2223903 = 3335855) B3335855
theorem B3335861 : Blo 2223435 3335861 := bbase (se 5 (by rfl) ⟨156368, by rfl⟩ : syracuseStep 3335861 = 312737) (by norm_num)
theorem B2223907 : Blo 2223435 2223907 := bstep (se 1 (by rfl) ⟨1667930, by rfl⟩ : syracuseStep 2223907 = 3335861) B3335861
theorem B5629277 : Blo 2223435 5629277 := bbase (se 3 (by rfl) ⟨1055489, by rfl⟩ : syracuseStep 5629277 = 2110979) (by norm_num)
theorem B3752851 : Blo 2223435 3752851 := bstep (se 1 (by rfl) ⟨2814638, by rfl⟩ : syracuseStep 3752851 = 5629277) B5629277
theorem B5003801 : Blo 2223435 5003801 := bstep (se 2 (by rfl) ⟨1876425, by rfl⟩ : syracuseStep 5003801 = 3752851) B3752851
theorem B3335867 : Blo 2223435 3335867 := bstep (se 1 (by rfl) ⟨2501900, by rfl⟩ : syracuseStep 3335867 = 5003801) B5003801
theorem B2223911 : Blo 2223435 2223911 := bstep (se 1 (by rfl) ⟨1667933, by rfl⟩ : syracuseStep 2223911 = 3335867) B3335867
theorem B2501905 : Blo 2223435 2501905 := bbase (se 2 (by rfl) ⟨938214, by rfl⟩ : syracuseStep 2501905 = 1876429) (by norm_num)
theorem B3335873 : Blo 2223435 3335873 := bstep (se 2 (by rfl) ⟨1250952, by rfl⟩ : syracuseStep 3335873 = 2501905) B2501905
theorem B2223915 : Blo 2223435 2223915 := bstep (se 1 (by rfl) ⟨1667936, by rfl⟩ : syracuseStep 2223915 = 3335873) B3335873
theorem B4221973 : Blo 2223435 4221973 := bbase (se 6 (by rfl) ⟨98952, by rfl⟩ : syracuseStep 4221973 = 197905) (by norm_num)
theorem B5629297 : Blo 2223435 5629297 := bstep (se 2 (by rfl) ⟨2110986, by rfl⟩ : syracuseStep 5629297 = 4221973) B4221973
theorem B7505729 : Blo 2223435 7505729 := bstep (se 2 (by rfl) ⟨2814648, by rfl⟩ : syracuseStep 7505729 = 5629297) B5629297
theorem B5003819 : Blo 2223435 5003819 := bstep (se 1 (by rfl) ⟨3752864, by rfl⟩ : syracuseStep 5003819 = 7505729) B7505729
theorem B3335879 : Blo 2223435 3335879 := bstep (se 1 (by rfl) ⟨2501909, by rfl⟩ : syracuseStep 3335879 = 5003819) B5003819
theorem B2223919 : Blo 2223435 2223919 := bstep (se 1 (by rfl) ⟨1667939, by rfl⟩ : syracuseStep 2223919 = 3335879) B3335879
theorem B3335885 : Blo 2223435 3335885 := bbase (se 3 (by rfl) ⟨625478, by rfl⟩ : syracuseStep 3335885 = 1250957) (by norm_num)
theorem B2223923 : Blo 2223435 2223923 := bstep (se 1 (by rfl) ⟨1667942, by rfl⟩ : syracuseStep 2223923 = 3335885) B3335885
theorem B5003837 : Blo 2223435 5003837 := bbase (se 3 (by rfl) ⟨938219, by rfl⟩ : syracuseStep 5003837 = 1876439) (by norm_num)
theorem B3335891 : Blo 2223435 3335891 := bstep (se 1 (by rfl) ⟨2501918, by rfl⟩ : syracuseStep 3335891 = 5003837) B5003837
theorem B2223927 : Blo 2223435 2223927 := bstep (se 1 (by rfl) ⟨1667945, by rfl⟩ : syracuseStep 2223927 = 3335891) B3335891
theorem B3752885 : Blo 2223435 3752885 := bbase (se 5 (by rfl) ⟨175916, by rfl⟩ : syracuseStep 3752885 = 351833) (by norm_num)
theorem B2501923 : Blo 2223435 2501923 := bstep (se 1 (by rfl) ⟨1876442, by rfl⟩ : syracuseStep 2501923 = 3752885) B3752885
theorem B3335897 : Blo 2223435 3335897 := bstep (se 2 (by rfl) ⟨1250961, by rfl⟩ : syracuseStep 3335897 = 2501923) B2501923
theorem B2223931 : Blo 2223435 2223931 := bstep (se 1 (by rfl) ⟨1667948, by rfl⟩ : syracuseStep 2223931 = 3335897) B3335897
theorem B2374877 : Blo 2223435 2374877 := bbase (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) (by norm_num)
theorem B6333005 : Blo 2223435 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B16888013 : Blo 2223435 16888013 := bstep (se 3 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 16888013 = 6333005) B6333005
theorem B11258675 : Blo 2223435 11258675 := bstep (se 1 (by rfl) ⟨8444006, by rfl⟩ : syracuseStep 11258675 = 16888013) B16888013
theorem B7505783 : Blo 2223435 7505783 := bstep (se 1 (by rfl) ⟨5629337, by rfl⟩ : syracuseStep 7505783 = 11258675) B11258675
theorem B5003855 : Blo 2223435 5003855 := bstep (se 1 (by rfl) ⟨3752891, by rfl⟩ : syracuseStep 5003855 = 7505783) B7505783
theorem B3335903 : Blo 2223435 3335903 := bstep (se 1 (by rfl) ⟨2501927, by rfl⟩ : syracuseStep 3335903 = 5003855) B5003855
theorem B2223935 : Blo 2223435 2223935 := bstep (se 1 (by rfl) ⟨1667951, by rfl⟩ : syracuseStep 2223935 = 3335903) B3335903
theorem B3335909 : Blo 2223435 3335909 := bbase (se 4 (by rfl) ⟨312741, by rfl⟩ : syracuseStep 3335909 = 625483) (by norm_num)
theorem B2223939 : Blo 2223435 2223939 := bstep (se 1 (by rfl) ⟨1667954, by rfl⟩ : syracuseStep 2223939 = 3335909) B3335909
theorem B6333029 : Blo 2223435 6333029 := bbase (se 4 (by rfl) ⟨593721, by rfl⟩ : syracuseStep 6333029 = 1187443) (by norm_num)
theorem B4222019 : Blo 2223435 4222019 := bstep (se 1 (by rfl) ⟨3166514, by rfl⟩ : syracuseStep 4222019 = 6333029) B6333029
theorem B2814679 : Blo 2223435 2814679 := bstep (se 1 (by rfl) ⟨2111009, by rfl⟩ : syracuseStep 2814679 = 4222019) B4222019
theorem B3752905 : Blo 2223435 3752905 := bstep (se 2 (by rfl) ⟨1407339, by rfl⟩ : syracuseStep 3752905 = 2814679) B2814679
theorem B5003873 : Blo 2223435 5003873 := bstep (se 2 (by rfl) ⟨1876452, by rfl⟩ : syracuseStep 5003873 = 3752905) B3752905
theorem B3335915 : Blo 2223435 3335915 := bstep (se 1 (by rfl) ⟨2501936, by rfl⟩ : syracuseStep 3335915 = 5003873) B5003873
theorem B2223943 : Blo 2223435 2223943 := bstep (se 1 (by rfl) ⟨1667957, by rfl⟩ : syracuseStep 2223943 = 3335915) B3335915
theorem B2501941 : Blo 2223435 2501941 := bbase (se 5 (by rfl) ⟨117278, by rfl⟩ : syracuseStep 2501941 = 234557) (by norm_num)
theorem B3335921 : Blo 2223435 3335921 := bstep (se 2 (by rfl) ⟨1250970, by rfl⟩ : syracuseStep 3335921 = 2501941) B2501941
theorem B2223947 : Blo 2223435 2223947 := bstep (se 1 (by rfl) ⟨1667960, by rfl⟩ : syracuseStep 2223947 = 3335921) B3335921
theorem B2814689 : Blo 2223435 2814689 := bbase (se 2 (by rfl) ⟨1055508, by rfl⟩ : syracuseStep 2814689 = 2111017) (by norm_num)
theorem B7505837 : Blo 2223435 7505837 := bstep (se 3 (by rfl) ⟨1407344, by rfl⟩ : syracuseStep 7505837 = 2814689) B2814689
theorem B5003891 : Blo 2223435 5003891 := bstep (se 1 (by rfl) ⟨3752918, by rfl⟩ : syracuseStep 5003891 = 7505837) B7505837
theorem B3335927 : Blo 2223435 3335927 := bstep (se 1 (by rfl) ⟨2501945, by rfl⟩ : syracuseStep 3335927 = 5003891) B5003891
theorem B2223951 : Blo 2223435 2223951 := bstep (se 1 (by rfl) ⟨1667963, by rfl⟩ : syracuseStep 2223951 = 3335927) B3335927
theorem B3335933 : Blo 2223435 3335933 := bbase (se 3 (by rfl) ⟨625487, by rfl⟩ : syracuseStep 3335933 = 1250975) (by norm_num)
theorem B2223955 : Blo 2223435 2223955 := bstep (se 1 (by rfl) ⟨1667966, by rfl⟩ : syracuseStep 2223955 = 3335933) B3335933
theorem B5003909 : Blo 2223435 5003909 := bbase (se 4 (by rfl) ⟨469116, by rfl⟩ : syracuseStep 5003909 = 938233) (by norm_num)
theorem B3335939 : Blo 2223435 3335939 := bstep (se 1 (by rfl) ⟨2501954, by rfl⟩ : syracuseStep 3335939 = 5003909) B5003909
theorem B2223959 : Blo 2223435 2223959 := bstep (se 1 (by rfl) ⟨1667969, by rfl⟩ : syracuseStep 2223959 = 3335939) B3335939
theorem B2285065 : Blo 2223435 2285065 := bbase (se 2 (by rfl) ⟨856899, by rfl⟩ : syracuseStep 2285065 = 1713799) (by norm_num)
theorem B3046753 : Blo 2223435 3046753 := bstep (se 2 (by rfl) ⟨1142532, by rfl⟩ : syracuseStep 3046753 = 2285065) B2285065
theorem B16249349 : Blo 2223435 16249349 := bstep (se 4 (by rfl) ⟨1523376, by rfl⟩ : syracuseStep 16249349 = 3046753) B3046753
theorem B10832899 : Blo 2223435 10832899 := bstep (se 1 (by rfl) ⟨8124674, by rfl⟩ : syracuseStep 10832899 = 16249349) B16249349
theorem B14443865 : Blo 2223435 14443865 := bstep (se 2 (by rfl) ⟨5416449, by rfl⟩ : syracuseStep 14443865 = 10832899) B10832899
theorem B9629243 : Blo 2223435 9629243 := bstep (se 1 (by rfl) ⟨7221932, by rfl⟩ : syracuseStep 9629243 = 14443865) B14443865
theorem B6419495 : Blo 2223435 6419495 := bstep (se 1 (by rfl) ⟨4814621, by rfl⟩ : syracuseStep 6419495 = 9629243) B9629243
theorem B4279663 : Blo 2223435 4279663 := bstep (se 1 (by rfl) ⟨3209747, by rfl⟩ : syracuseStep 4279663 = 6419495) B6419495
theorem B5706217 : Blo 2223435 5706217 := bstep (se 2 (by rfl) ⟨2139831, by rfl⟩ : syracuseStep 5706217 = 4279663) B4279663
theorem B7608289 : Blo 2223435 7608289 := bstep (se 2 (by rfl) ⟨2853108, by rfl⟩ : syracuseStep 7608289 = 5706217) B5706217
theorem B10144385 : Blo 2223435 10144385 := bstep (se 2 (by rfl) ⟨3804144, by rfl⟩ : syracuseStep 10144385 = 7608289) B7608289
theorem B6762923 : Blo 2223435 6762923 := bstep (se 1 (by rfl) ⟨5072192, by rfl⟩ : syracuseStep 6762923 = 10144385) B10144385
theorem B4508615 : Blo 2223435 4508615 := bstep (se 1 (by rfl) ⟨3381461, by rfl⟩ : syracuseStep 4508615 = 6762923) B6762923
theorem B3005743 : Blo 2223435 3005743 := bstep (se 1 (by rfl) ⟨2254307, by rfl⟩ : syracuseStep 3005743 = 4508615) B4508615
theorem B4007657 : Blo 2223435 4007657 := bstep (se 2 (by rfl) ⟨1502871, by rfl⟩ : syracuseStep 4007657 = 3005743) B3005743
theorem B10687085 : Blo 2223435 10687085 := bstep (se 3 (by rfl) ⟨2003828, by rfl⟩ : syracuseStep 10687085 = 4007657) B4007657
theorem B7124723 : Blo 2223435 7124723 := bstep (se 1 (by rfl) ⟨5343542, by rfl⟩ : syracuseStep 7124723 = 10687085) B10687085
theorem B4749815 : Blo 2223435 4749815 := bstep (se 1 (by rfl) ⟨3562361, by rfl⟩ : syracuseStep 4749815 = 7124723) B7124723
theorem B3166543 : Blo 2223435 3166543 := bstep (se 1 (by rfl) ⟨2374907, by rfl⟩ : syracuseStep 3166543 = 4749815) B4749815
theorem B4222057 : Blo 2223435 4222057 := bstep (se 2 (by rfl) ⟨1583271, by rfl⟩ : syracuseStep 4222057 = 3166543) B3166543
theorem B5629409 : Blo 2223435 5629409 := bstep (se 2 (by rfl) ⟨2111028, by rfl⟩ : syracuseStep 5629409 = 4222057) B4222057
theorem B3752939 : Blo 2223435 3752939 := bstep (se 1 (by rfl) ⟨2814704, by rfl⟩ : syracuseStep 3752939 = 5629409) B5629409
theorem B2501959 : Blo 2223435 2501959 := bstep (se 1 (by rfl) ⟨1876469, by rfl⟩ : syracuseStep 2501959 = 3752939) B3752939
theorem B3335945 : Blo 2223435 3335945 := bstep (se 2 (by rfl) ⟨1250979, by rfl⟩ : syracuseStep 3335945 = 2501959) B2501959
theorem B2223963 : Blo 2223435 2223963 := bstep (se 1 (by rfl) ⟨1667972, by rfl⟩ : syracuseStep 2223963 = 3335945) B3335945
theorem B11258837 : Blo 2223435 11258837 := bbase (se 7 (by rfl) ⟨131939, by rfl⟩ : syracuseStep 11258837 = 263879) (by norm_num)
theorem B7505891 : Blo 2223435 7505891 := bstep (se 1 (by rfl) ⟨5629418, by rfl⟩ : syracuseStep 7505891 = 11258837) B11258837
theorem B5003927 : Blo 2223435 5003927 := bstep (se 1 (by rfl) ⟨3752945, by rfl⟩ : syracuseStep 5003927 = 7505891) B7505891
theorem B3335951 : Blo 2223435 3335951 := bstep (se 1 (by rfl) ⟨2501963, by rfl⟩ : syracuseStep 3335951 = 5003927) B5003927
theorem B2223967 : Blo 2223435 2223967 := bstep (se 1 (by rfl) ⟨1667975, by rfl⟩ : syracuseStep 2223967 = 3335951) B3335951
theorem B3335957 : Blo 2223435 3335957 := bbase (se 6 (by rfl) ⟨78186, by rfl⟩ : syracuseStep 3335957 = 156373) (by norm_num)
theorem B2223971 : Blo 2223435 2223971 := bstep (se 1 (by rfl) ⟨1667978, by rfl⟩ : syracuseStep 2223971 = 3335957) B3335957
theorem B4880333 : Blo 2223435 4880333 := bbase (se 3 (by rfl) ⟨915062, by rfl⟩ : syracuseStep 4880333 = 1830125) (by norm_num)
theorem B3253555 : Blo 2223435 3253555 := bstep (se 1 (by rfl) ⟨2440166, by rfl⟩ : syracuseStep 3253555 = 4880333) B4880333
theorem B4338073 : Blo 2223435 4338073 := bstep (se 2 (by rfl) ⟨1626777, by rfl⟩ : syracuseStep 4338073 = 3253555) B3253555
theorem B5784097 : Blo 2223435 5784097 := bstep (se 2 (by rfl) ⟨2169036, by rfl⟩ : syracuseStep 5784097 = 4338073) B4338073
theorem B7712129 : Blo 2223435 7712129 := bstep (se 2 (by rfl) ⟨2892048, by rfl⟩ : syracuseStep 7712129 = 5784097) B5784097
theorem B20565677 : Blo 2223435 20565677 := bstep (se 3 (by rfl) ⟨3856064, by rfl⟩ : syracuseStep 20565677 = 7712129) B7712129
theorem B54841805 : Blo 2223435 54841805 := bstep (se 3 (by rfl) ⟨10282838, by rfl⟩ : syracuseStep 54841805 = 20565677) B20565677
theorem B36561203 : Blo 2223435 36561203 := bstep (se 1 (by rfl) ⟨27420902, by rfl⟩ : syracuseStep 36561203 = 54841805) B54841805
theorem B24374135 : Blo 2223435 24374135 := bstep (se 1 (by rfl) ⟨18280601, by rfl⟩ : syracuseStep 24374135 = 36561203) B36561203
theorem B16249423 : Blo 2223435 16249423 := bstep (se 1 (by rfl) ⟨12187067, by rfl⟩ : syracuseStep 16249423 = 24374135) B24374135
theorem B21665897 : Blo 2223435 21665897 := bstep (se 2 (by rfl) ⟨8124711, by rfl⟩ : syracuseStep 21665897 = 16249423) B16249423
theorem B14443931 : Blo 2223435 14443931 := bstep (se 1 (by rfl) ⟨10832948, by rfl⟩ : syracuseStep 14443931 = 21665897) B21665897
theorem B9629287 : Blo 2223435 9629287 := bstep (se 1 (by rfl) ⟨7221965, by rfl⟩ : syracuseStep 9629287 = 14443931) B14443931
theorem B51356197 : Blo 2223435 51356197 := bstep (se 4 (by rfl) ⟨4814643, by rfl⟩ : syracuseStep 51356197 = 9629287) B9629287
theorem B68474929 : Blo 2223435 68474929 := bstep (se 2 (by rfl) ⟨25678098, by rfl⟩ : syracuseStep 68474929 = 51356197) B51356197
theorem B91299905 : Blo 2223435 91299905 := bstep (se 2 (by rfl) ⟨34237464, by rfl⟩ : syracuseStep 91299905 = 68474929) B68474929
theorem B60866603 : Blo 2223435 60866603 := bstep (se 1 (by rfl) ⟨45649952, by rfl⟩ : syracuseStep 60866603 = 91299905) B91299905
theorem B40577735 : Blo 2223435 40577735 := bstep (se 1 (by rfl) ⟨30433301, by rfl⟩ : syracuseStep 40577735 = 60866603) B60866603
theorem B27051823 : Blo 2223435 27051823 := bstep (se 1 (by rfl) ⟨20288867, by rfl⟩ : syracuseStep 27051823 = 40577735) B40577735
theorem B144276389 : Blo 2223435 144276389 := bstep (se 4 (by rfl) ⟨13525911, by rfl⟩ : syracuseStep 144276389 = 27051823) B27051823
theorem B96184259 : Blo 2223435 96184259 := bstep (se 1 (by rfl) ⟨72138194, by rfl⟩ : syracuseStep 96184259 = 144276389) B144276389
theorem B64122839 : Blo 2223435 64122839 := bstep (se 1 (by rfl) ⟨48092129, by rfl⟩ : syracuseStep 64122839 = 96184259) B96184259
theorem B42748559 : Blo 2223435 42748559 := bstep (se 1 (by rfl) ⟨32061419, by rfl⟩ : syracuseStep 42748559 = 64122839) B64122839
theorem B28499039 : Blo 2223435 28499039 := bstep (se 1 (by rfl) ⟨21374279, by rfl⟩ : syracuseStep 28499039 = 42748559) B42748559
theorem B18999359 : Blo 2223435 18999359 := bstep (se 1 (by rfl) ⟨14249519, by rfl⟩ : syracuseStep 18999359 = 28499039) B28499039
theorem B12666239 : Blo 2223435 12666239 := bstep (se 1 (by rfl) ⟨9499679, by rfl⟩ : syracuseStep 12666239 = 18999359) B18999359
theorem B8444159 : Blo 2223435 8444159 := bstep (se 1 (by rfl) ⟨6333119, by rfl⟩ : syracuseStep 8444159 = 12666239) B12666239
theorem B5629439 : Blo 2223435 5629439 := bstep (se 1 (by rfl) ⟨4222079, by rfl⟩ : syracuseStep 5629439 = 8444159) B8444159
theorem B3752959 : Blo 2223435 3752959 := bstep (se 1 (by rfl) ⟨2814719, by rfl⟩ : syracuseStep 3752959 = 5629439) B5629439
theorem B5003945 : Blo 2223435 5003945 := bstep (se 2 (by rfl) ⟨1876479, by rfl⟩ : syracuseStep 5003945 = 3752959) B3752959
theorem B3335963 : Blo 2223435 3335963 := bstep (se 1 (by rfl) ⟨2501972, by rfl⟩ : syracuseStep 3335963 = 5003945) B5003945
theorem B2223975 : Blo 2223435 2223975 := bstep (se 1 (by rfl) ⟨1667981, by rfl⟩ : syracuseStep 2223975 = 3335963) B3335963
theorem B2501977 : Blo 2223435 2501977 := bbase (se 2 (by rfl) ⟨938241, by rfl⟩ : syracuseStep 2501977 = 1876483) (by norm_num)
theorem B3335969 : Blo 2223435 3335969 := bstep (se 2 (by rfl) ⟨1250988, by rfl⟩ : syracuseStep 3335969 = 2501977) B2501977
theorem B2223979 : Blo 2223435 2223979 := bstep (se 1 (by rfl) ⟨1667984, by rfl⟩ : syracuseStep 2223979 = 3335969) B3335969
theorem B4007693 : Blo 2223435 4007693 := bbase (se 3 (by rfl) ⟨751442, by rfl⟩ : syracuseStep 4007693 = 1502885) (by norm_num)
theorem B2671795 : Blo 2223435 2671795 := bstep (se 1 (by rfl) ⟨2003846, by rfl⟩ : syracuseStep 2671795 = 4007693) B4007693
theorem B3562393 : Blo 2223435 3562393 := bstep (se 2 (by rfl) ⟨1335897, by rfl⟩ : syracuseStep 3562393 = 2671795) B2671795
theorem B4749857 : Blo 2223435 4749857 := bstep (se 2 (by rfl) ⟨1781196, by rfl⟩ : syracuseStep 4749857 = 3562393) B3562393
theorem B3166571 : Blo 2223435 3166571 := bstep (se 1 (by rfl) ⟨2374928, by rfl⟩ : syracuseStep 3166571 = 4749857) B4749857
theorem B8444189 : Blo 2223435 8444189 := bstep (se 3 (by rfl) ⟨1583285, by rfl⟩ : syracuseStep 8444189 = 3166571) B3166571
theorem B5629459 : Blo 2223435 5629459 := bstep (se 1 (by rfl) ⟨4222094, by rfl⟩ : syracuseStep 5629459 = 8444189) B8444189
theorem B7505945 : Blo 2223435 7505945 := bstep (se 2 (by rfl) ⟨2814729, by rfl⟩ : syracuseStep 7505945 = 5629459) B5629459
theorem B5003963 : Blo 2223435 5003963 := bstep (se 1 (by rfl) ⟨3752972, by rfl⟩ : syracuseStep 5003963 = 7505945) B7505945
theorem B3335975 : Blo 2223435 3335975 := bstep (se 1 (by rfl) ⟨2501981, by rfl⟩ : syracuseStep 3335975 = 5003963) B5003963
theorem B2223983 : Blo 2223435 2223983 := bstep (se 1 (by rfl) ⟨1667987, by rfl⟩ : syracuseStep 2223983 = 3335975) B3335975
theorem B3335981 : Blo 2223435 3335981 := bbase (se 3 (by rfl) ⟨625496, by rfl⟩ : syracuseStep 3335981 = 1250993) (by norm_num)
theorem B2223987 : Blo 2223435 2223987 := bstep (se 1 (by rfl) ⟨1667990, by rfl⟩ : syracuseStep 2223987 = 3335981) B3335981
theorem B5003981 : Blo 2223435 5003981 := bbase (se 3 (by rfl) ⟨938246, by rfl⟩ : syracuseStep 5003981 = 1876493) (by norm_num)
theorem B3335987 : Blo 2223435 3335987 := bstep (se 1 (by rfl) ⟨2501990, by rfl⟩ : syracuseStep 3335987 = 5003981) B5003981
theorem B2223991 : Blo 2223435 2223991 := bstep (se 1 (by rfl) ⟨1667993, by rfl⟩ : syracuseStep 2223991 = 3335987) B3335987
theorem B2814745 : Blo 2223435 2814745 := bbase (se 2 (by rfl) ⟨1055529, by rfl⟩ : syracuseStep 2814745 = 2111059) (by norm_num)
theorem B3752993 : Blo 2223435 3752993 := bstep (se 2 (by rfl) ⟨1407372, by rfl⟩ : syracuseStep 3752993 = 2814745) B2814745
theorem B2501995 : Blo 2223435 2501995 := bstep (se 1 (by rfl) ⟨1876496, by rfl⟩ : syracuseStep 2501995 = 3752993) B3752993
theorem B3335993 : Blo 2223435 3335993 := bstep (se 2 (by rfl) ⟨1250997, by rfl⟩ : syracuseStep 3335993 = 2501995) B2501995
theorem B2223995 : Blo 2223435 2223995 := bstep (se 1 (by rfl) ⟨1667996, by rfl⟩ : syracuseStep 2223995 = 3335993) B3335993
theorem B9499781 : Blo 2223435 9499781 := bbase (se 4 (by rfl) ⟨890604, by rfl⟩ : syracuseStep 9499781 = 1781209) (by norm_num)
theorem B25332749 : Blo 2223435 25332749 := bstep (se 3 (by rfl) ⟨4749890, by rfl⟩ : syracuseStep 25332749 = 9499781) B9499781
theorem B16888499 : Blo 2223435 16888499 := bstep (se 1 (by rfl) ⟨12666374, by rfl⟩ : syracuseStep 16888499 = 25332749) B25332749
theorem B11258999 : Blo 2223435 11258999 := bstep (se 1 (by rfl) ⟨8444249, by rfl⟩ : syracuseStep 11258999 = 16888499) B16888499
theorem B7505999 : Blo 2223435 7505999 := bstep (se 1 (by rfl) ⟨5629499, by rfl⟩ : syracuseStep 7505999 = 11258999) B11258999
theorem B5003999 : Blo 2223435 5003999 := bstep (se 1 (by rfl) ⟨3752999, by rfl⟩ : syracuseStep 5003999 = 7505999) B7505999
theorem B3335999 : Blo 2223435 3335999 := bstep (se 1 (by rfl) ⟨2501999, by rfl⟩ : syracuseStep 3335999 = 5003999) B5003999
theorem B2223999 : Blo 2223435 2223999 := bstep (se 1 (by rfl) ⟨1667999, by rfl⟩ : syracuseStep 2223999 = 3335999) B3335999
theorem B3336005 : Blo 2223435 3336005 := bbase (se 4 (by rfl) ⟨312750, by rfl⟩ : syracuseStep 3336005 = 625501) (by norm_num)
theorem B2224003 : Blo 2223435 2224003 := bstep (se 1 (by rfl) ⟨1668002, by rfl⟩ : syracuseStep 2224003 = 3336005) B3336005
theorem B3753013 : Blo 2223435 3753013 := bbase (se 5 (by rfl) ⟨175922, by rfl⟩ : syracuseStep 3753013 = 351845) (by norm_num)
theorem B5004017 : Blo 2223435 5004017 := bstep (se 2 (by rfl) ⟨1876506, by rfl⟩ : syracuseStep 5004017 = 3753013) B3753013
theorem B3336011 : Blo 2223435 3336011 := bstep (se 1 (by rfl) ⟨2502008, by rfl⟩ : syracuseStep 3336011 = 5004017) B5004017
theorem B2224007 : Blo 2223435 2224007 := bstep (se 1 (by rfl) ⟨1668005, by rfl⟩ : syracuseStep 2224007 = 3336011) B3336011
theorem B2502013 : Blo 2223435 2502013 := bbase (se 3 (by rfl) ⟨469127, by rfl⟩ : syracuseStep 2502013 = 938255) (by norm_num)
theorem B3336017 : Blo 2223435 3336017 := bstep (se 2 (by rfl) ⟨1251006, by rfl⟩ : syracuseStep 3336017 = 2502013) B2502013
theorem B2224011 : Blo 2223435 2224011 := bstep (se 1 (by rfl) ⟨1668008, by rfl⟩ : syracuseStep 2224011 = 3336017) B3336017
theorem B7506053 : Blo 2223435 7506053 := bbase (se 4 (by rfl) ⟨703692, by rfl⟩ : syracuseStep 7506053 = 1407385) (by norm_num)
theorem B5004035 : Blo 2223435 5004035 := bstep (se 1 (by rfl) ⟨3753026, by rfl⟩ : syracuseStep 5004035 = 7506053) B7506053
theorem B3336023 : Blo 2223435 3336023 := bstep (se 1 (by rfl) ⟨2502017, by rfl⟩ : syracuseStep 3336023 = 5004035) B5004035
theorem B2224015 : Blo 2223435 2224015 := bstep (se 1 (by rfl) ⟨1668011, by rfl⟩ : syracuseStep 2224015 = 3336023) B3336023
theorem B3336029 : Blo 2223435 3336029 := bbase (se 3 (by rfl) ⟨625505, by rfl⟩ : syracuseStep 3336029 = 1251011) (by norm_num)
theorem B2224019 : Blo 2223435 2224019 := bstep (se 1 (by rfl) ⟨1668014, by rfl⟩ : syracuseStep 2224019 = 3336029) B3336029
theorem B5004053 : Blo 2223435 5004053 := bbase (se 6 (by rfl) ⟨117282, by rfl⟩ : syracuseStep 5004053 = 234565) (by norm_num)
theorem B3336035 : Blo 2223435 3336035 := bstep (se 1 (by rfl) ⟨2502026, by rfl⟩ : syracuseStep 3336035 = 5004053) B5004053
theorem B2224023 : Blo 2223435 2224023 := bstep (se 1 (by rfl) ⟨1668017, by rfl⟩ : syracuseStep 2224023 = 3336035) B3336035
theorem B8444357 : Blo 2223435 8444357 := bbase (se 4 (by rfl) ⟨791658, by rfl⟩ : syracuseStep 8444357 = 1583317) (by norm_num)
theorem B5629571 : Blo 2223435 5629571 := bstep (se 1 (by rfl) ⟨4222178, by rfl⟩ : syracuseStep 5629571 = 8444357) B8444357
theorem B3753047 : Blo 2223435 3753047 := bstep (se 1 (by rfl) ⟨2814785, by rfl⟩ : syracuseStep 3753047 = 5629571) B5629571
theorem B2502031 : Blo 2223435 2502031 := bstep (se 1 (by rfl) ⟨1876523, by rfl⟩ : syracuseStep 2502031 = 3753047) B3753047
theorem B3336041 : Blo 2223435 3336041 := bstep (se 2 (by rfl) ⟨1251015, by rfl⟩ : syracuseStep 3336041 = 2502031) B2502031
theorem B2224027 : Blo 2223435 2224027 := bstep (se 1 (by rfl) ⟨1668020, by rfl⟩ : syracuseStep 2224027 = 3336041) B3336041
theorem B8015557 : Blo 2223435 8015557 := bbase (se 4 (by rfl) ⟨751458, by rfl⟩ : syracuseStep 8015557 = 1502917) (by norm_num)
theorem B10687409 : Blo 2223435 10687409 := bstep (se 2 (by rfl) ⟨4007778, by rfl⟩ : syracuseStep 10687409 = 8015557) B8015557
theorem B7124939 : Blo 2223435 7124939 := bstep (se 1 (by rfl) ⟨5343704, by rfl⟩ : syracuseStep 7124939 = 10687409) B10687409
theorem B4749959 : Blo 2223435 4749959 := bstep (se 1 (by rfl) ⟨3562469, by rfl⟩ : syracuseStep 4749959 = 7124939) B7124939
theorem B12666557 : Blo 2223435 12666557 := bstep (se 3 (by rfl) ⟨2374979, by rfl⟩ : syracuseStep 12666557 = 4749959) B4749959
theorem B8444371 : Blo 2223435 8444371 := bstep (se 1 (by rfl) ⟨6333278, by rfl⟩ : syracuseStep 8444371 = 12666557) B12666557
theorem B11259161 : Blo 2223435 11259161 := bstep (se 2 (by rfl) ⟨4222185, by rfl⟩ : syracuseStep 11259161 = 8444371) B8444371
theorem B7506107 : Blo 2223435 7506107 := bstep (se 1 (by rfl) ⟨5629580, by rfl⟩ : syracuseStep 7506107 = 11259161) B11259161
theorem B5004071 : Blo 2223435 5004071 := bstep (se 1 (by rfl) ⟨3753053, by rfl⟩ : syracuseStep 5004071 = 7506107) B7506107
theorem B3336047 : Blo 2223435 3336047 := bstep (se 1 (by rfl) ⟨2502035, by rfl⟩ : syracuseStep 3336047 = 5004071) B5004071
theorem B2224031 : Blo 2223435 2224031 := bstep (se 1 (by rfl) ⟨1668023, by rfl⟩ : syracuseStep 2224031 = 3336047) B3336047
theorem B3336053 : Blo 2223435 3336053 := bbase (se 5 (by rfl) ⟨156377, by rfl⟩ : syracuseStep 3336053 = 312755) (by norm_num)
theorem B2224035 : Blo 2223435 2224035 := bstep (se 1 (by rfl) ⟨1668026, by rfl⟩ : syracuseStep 2224035 = 3336053) B3336053
theorem B5343725 : Blo 2223435 5343725 := bbase (se 3 (by rfl) ⟨1001948, by rfl⟩ : syracuseStep 5343725 = 2003897) (by norm_num)
theorem B3562483 : Blo 2223435 3562483 := bstep (se 1 (by rfl) ⟨2671862, by rfl⟩ : syracuseStep 3562483 = 5343725) B5343725
theorem B4749977 : Blo 2223435 4749977 := bstep (se 2 (by rfl) ⟨1781241, by rfl⟩ : syracuseStep 4749977 = 3562483) B3562483
theorem B3166651 : Blo 2223435 3166651 := bstep (se 1 (by rfl) ⟨2374988, by rfl⟩ : syracuseStep 3166651 = 4749977) B4749977
theorem B4222201 : Blo 2223435 4222201 := bstep (se 2 (by rfl) ⟨1583325, by rfl⟩ : syracuseStep 4222201 = 3166651) B3166651
theorem B5629601 : Blo 2223435 5629601 := bstep (se 2 (by rfl) ⟨2111100, by rfl⟩ : syracuseStep 5629601 = 4222201) B4222201
theorem B3753067 : Blo 2223435 3753067 := bstep (se 1 (by rfl) ⟨2814800, by rfl⟩ : syracuseStep 3753067 = 5629601) B5629601
theorem B5004089 : Blo 2223435 5004089 := bstep (se 2 (by rfl) ⟨1876533, by rfl⟩ : syracuseStep 5004089 = 3753067) B3753067
theorem B3336059 : Blo 2223435 3336059 := bstep (se 1 (by rfl) ⟨2502044, by rfl⟩ : syracuseStep 3336059 = 5004089) B5004089
theorem B2224039 : Blo 2223435 2224039 := bstep (se 1 (by rfl) ⟨1668029, by rfl⟩ : syracuseStep 2224039 = 3336059) B3336059
theorem B2502049 : Blo 2223435 2502049 := bbase (se 2 (by rfl) ⟨938268, by rfl⟩ : syracuseStep 2502049 = 1876537) (by norm_num)
theorem B3336065 : Blo 2223435 3336065 := bstep (se 2 (by rfl) ⟨1251024, by rfl⟩ : syracuseStep 3336065 = 2502049) B2502049
theorem B2224043 : Blo 2223435 2224043 := bstep (se 1 (by rfl) ⟨1668032, by rfl⟩ : syracuseStep 2224043 = 3336065) B3336065
theorem B5629621 : Blo 2223435 5629621 := bbase (se 5 (by rfl) ⟨263888, by rfl⟩ : syracuseStep 5629621 = 527777) (by norm_num)
theorem B7506161 : Blo 2223435 7506161 := bstep (se 2 (by rfl) ⟨2814810, by rfl⟩ : syracuseStep 7506161 = 5629621) B5629621
theorem B5004107 : Blo 2223435 5004107 := bstep (se 1 (by rfl) ⟨3753080, by rfl⟩ : syracuseStep 5004107 = 7506161) B7506161
theorem B3336071 : Blo 2223435 3336071 := bstep (se 1 (by rfl) ⟨2502053, by rfl⟩ : syracuseStep 3336071 = 5004107) B5004107
theorem B2224047 : Blo 2223435 2224047 := bstep (se 1 (by rfl) ⟨1668035, by rfl⟩ : syracuseStep 2224047 = 3336071) B3336071
theorem B3336077 : Blo 2223435 3336077 := bbase (se 3 (by rfl) ⟨625514, by rfl⟩ : syracuseStep 3336077 = 1251029) (by norm_num)
theorem B2224051 : Blo 2223435 2224051 := bstep (se 1 (by rfl) ⟨1668038, by rfl⟩ : syracuseStep 2224051 = 3336077) B3336077
theorem B5004125 : Blo 2223435 5004125 := bbase (se 3 (by rfl) ⟨938273, by rfl⟩ : syracuseStep 5004125 = 1876547) (by norm_num)
theorem B3336083 : Blo 2223435 3336083 := bstep (se 1 (by rfl) ⟨2502062, by rfl⟩ : syracuseStep 3336083 = 5004125) B5004125
theorem B2224055 : Blo 2223435 2224055 := bstep (se 1 (by rfl) ⟨1668041, by rfl⟩ : syracuseStep 2224055 = 3336083) B3336083
theorem B3753101 : Blo 2223435 3753101 := bbase (se 3 (by rfl) ⟨703706, by rfl⟩ : syracuseStep 3753101 = 1407413) (by norm_num)
theorem B2502067 : Blo 2223435 2502067 := bstep (se 1 (by rfl) ⟨1876550, by rfl⟩ : syracuseStep 2502067 = 3753101) B3753101
theorem B3336089 : Blo 2223435 3336089 := bstep (se 2 (by rfl) ⟨1251033, by rfl⟩ : syracuseStep 3336089 = 2502067) B2502067
theorem B2224059 : Blo 2223435 2224059 := bstep (se 1 (by rfl) ⟨1668044, by rfl⟩ : syracuseStep 2224059 = 3336089) B3336089
theorem B5343781 : Blo 2223435 5343781 := bbase (se 4 (by rfl) ⟨500979, by rfl⟩ : syracuseStep 5343781 = 1001959) (by norm_num)
theorem B7125041 : Blo 2223435 7125041 := bstep (se 2 (by rfl) ⟨2671890, by rfl⟩ : syracuseStep 7125041 = 5343781) B5343781
theorem B19000109 : Blo 2223435 19000109 := bstep (se 3 (by rfl) ⟨3562520, by rfl⟩ : syracuseStep 19000109 = 7125041) B7125041
theorem B12666739 : Blo 2223435 12666739 := bstep (se 1 (by rfl) ⟨9500054, by rfl⟩ : syracuseStep 12666739 = 19000109) B19000109
theorem B16888985 : Blo 2223435 16888985 := bstep (se 2 (by rfl) ⟨6333369, by rfl⟩ : syracuseStep 16888985 = 12666739) B12666739
theorem B11259323 : Blo 2223435 11259323 := bstep (se 1 (by rfl) ⟨8444492, by rfl⟩ : syracuseStep 11259323 = 16888985) B16888985
theorem B7506215 : Blo 2223435 7506215 := bstep (se 1 (by rfl) ⟨5629661, by rfl⟩ : syracuseStep 7506215 = 11259323) B11259323
theorem B5004143 : Blo 2223435 5004143 := bstep (se 1 (by rfl) ⟨3753107, by rfl⟩ : syracuseStep 5004143 = 7506215) B7506215
theorem B3336095 : Blo 2223435 3336095 := bstep (se 1 (by rfl) ⟨2502071, by rfl⟩ : syracuseStep 3336095 = 5004143) B5004143
theorem B2224063 : Blo 2223435 2224063 := bstep (se 1 (by rfl) ⟨1668047, by rfl⟩ : syracuseStep 2224063 = 3336095) B3336095
theorem B3336101 : Blo 2223435 3336101 := bbase (se 4 (by rfl) ⟨312759, by rfl⟩ : syracuseStep 3336101 = 625519) (by norm_num)
theorem B2224067 : Blo 2223435 2224067 := bstep (se 1 (by rfl) ⟨1668050, by rfl⟩ : syracuseStep 2224067 = 3336101) B3336101
theorem B2814841 : Blo 2223435 2814841 := bbase (se 2 (by rfl) ⟨1055565, by rfl⟩ : syracuseStep 2814841 = 2111131) (by norm_num)
theorem B3753121 : Blo 2223435 3753121 := bstep (se 2 (by rfl) ⟨1407420, by rfl⟩ : syracuseStep 3753121 = 2814841) B2814841
theorem B5004161 : Blo 2223435 5004161 := bstep (se 2 (by rfl) ⟨1876560, by rfl⟩ : syracuseStep 5004161 = 3753121) B3753121
theorem B3336107 : Blo 2223435 3336107 := bstep (se 1 (by rfl) ⟨2502080, by rfl⟩ : syracuseStep 3336107 = 5004161) B5004161
theorem B2224071 : Blo 2223435 2224071 := bstep (se 1 (by rfl) ⟨1668053, by rfl⟩ : syracuseStep 2224071 = 3336107) B3336107
theorem B2502085 : Blo 2223435 2502085 := bbase (se 4 (by rfl) ⟨234570, by rfl⟩ : syracuseStep 2502085 = 469141) (by norm_num)
theorem B3336113 : Blo 2223435 3336113 := bstep (se 2 (by rfl) ⟨1251042, by rfl⟩ : syracuseStep 3336113 = 2502085) B2502085
theorem B2224075 : Blo 2223435 2224075 := bstep (se 1 (by rfl) ⟨1668056, by rfl⟩ : syracuseStep 2224075 = 3336113) B3336113
theorem B4222277 : Blo 2223435 4222277 := bbase (se 4 (by rfl) ⟨395838, by rfl⟩ : syracuseStep 4222277 = 791677) (by norm_num)
theorem B2814851 : Blo 2223435 2814851 := bstep (se 1 (by rfl) ⟨2111138, by rfl⟩ : syracuseStep 2814851 = 4222277) B4222277
theorem B7506269 : Blo 2223435 7506269 := bstep (se 3 (by rfl) ⟨1407425, by rfl⟩ : syracuseStep 7506269 = 2814851) B2814851
theorem B5004179 : Blo 2223435 5004179 := bstep (se 1 (by rfl) ⟨3753134, by rfl⟩ : syracuseStep 5004179 = 7506269) B7506269
theorem B3336119 : Blo 2223435 3336119 := bstep (se 1 (by rfl) ⟨2502089, by rfl⟩ : syracuseStep 3336119 = 5004179) B5004179
theorem B2224079 : Blo 2223435 2224079 := bstep (se 1 (by rfl) ⟨1668059, by rfl⟩ : syracuseStep 2224079 = 3336119) B3336119
theorem B3336125 : Blo 2223435 3336125 := bbase (se 3 (by rfl) ⟨625523, by rfl⟩ : syracuseStep 3336125 = 1251047) (by norm_num)
theorem B2224083 : Blo 2223435 2224083 := bstep (se 1 (by rfl) ⟨1668062, by rfl⟩ : syracuseStep 2224083 = 3336125) B3336125
theorem B5004197 : Blo 2223435 5004197 := bbase (se 4 (by rfl) ⟨469143, by rfl⟩ : syracuseStep 5004197 = 938287) (by norm_num)
theorem B3336131 : Blo 2223435 3336131 := bstep (se 1 (by rfl) ⟨2502098, by rfl⟩ : syracuseStep 3336131 = 5004197) B5004197
theorem B2224087 : Blo 2223435 2224087 := bstep (se 1 (by rfl) ⟨1668065, by rfl⟩ : syracuseStep 2224087 = 3336131) B3336131
theorem B5629733 : Blo 2223435 5629733 := bbase (se 4 (by rfl) ⟨527787, by rfl⟩ : syracuseStep 5629733 = 1055575) (by norm_num)
theorem B3753155 : Blo 2223435 3753155 := bstep (se 1 (by rfl) ⟨2814866, by rfl⟩ : syracuseStep 3753155 = 5629733) B5629733
theorem B2502103 : Blo 2223435 2502103 := bstep (se 1 (by rfl) ⟨1876577, by rfl⟩ : syracuseStep 2502103 = 3753155) B3753155
theorem B3336137 : Blo 2223435 3336137 := bstep (se 2 (by rfl) ⟨1251051, by rfl⟩ : syracuseStep 3336137 = 2502103) B2502103
theorem B2224091 : Blo 2223435 2224091 := bstep (se 1 (by rfl) ⟨1668068, by rfl⟩ : syracuseStep 2224091 = 3336137) B3336137
theorem B6333461 : Blo 2223435 6333461 := bbase (se 6 (by rfl) ⟨148440, by rfl⟩ : syracuseStep 6333461 = 296881) (by norm_num)
theorem B4222307 : Blo 2223435 4222307 := bstep (se 1 (by rfl) ⟨3166730, by rfl⟩ : syracuseStep 4222307 = 6333461) B6333461
theorem B11259485 : Blo 2223435 11259485 := bstep (se 3 (by rfl) ⟨2111153, by rfl⟩ : syracuseStep 11259485 = 4222307) B4222307
theorem B7506323 : Blo 2223435 7506323 := bstep (se 1 (by rfl) ⟨5629742, by rfl⟩ : syracuseStep 7506323 = 11259485) B11259485
theorem B5004215 : Blo 2223435 5004215 := bstep (se 1 (by rfl) ⟨3753161, by rfl⟩ : syracuseStep 5004215 = 7506323) B7506323
theorem B3336143 : Blo 2223435 3336143 := bstep (se 1 (by rfl) ⟨2502107, by rfl⟩ : syracuseStep 3336143 = 5004215) B5004215
theorem B2224095 : Blo 2223435 2224095 := bstep (se 1 (by rfl) ⟨1668071, by rfl⟩ : syracuseStep 2224095 = 3336143) B3336143
theorem B3336149 : Blo 2223435 3336149 := bbase (se 7 (by rfl) ⟨39095, by rfl⟩ : syracuseStep 3336149 = 78191) (by norm_num)
theorem B2224099 : Blo 2223435 2224099 := bstep (se 1 (by rfl) ⟨1668074, by rfl⟩ : syracuseStep 2224099 = 3336149) B3336149
theorem B8444645 : Blo 2223435 8444645 := bbase (se 4 (by rfl) ⟨791685, by rfl⟩ : syracuseStep 8444645 = 1583371) (by norm_num)
theorem B5629763 : Blo 2223435 5629763 := bstep (se 1 (by rfl) ⟨4222322, by rfl⟩ : syracuseStep 5629763 = 8444645) B8444645
theorem B3753175 : Blo 2223435 3753175 := bstep (se 1 (by rfl) ⟨2814881, by rfl⟩ : syracuseStep 3753175 = 5629763) B5629763
theorem B5004233 : Blo 2223435 5004233 := bstep (se 2 (by rfl) ⟨1876587, by rfl⟩ : syracuseStep 5004233 = 3753175) B3753175
theorem B3336155 : Blo 2223435 3336155 := bstep (se 1 (by rfl) ⟨2502116, by rfl⟩ : syracuseStep 3336155 = 5004233) B5004233
theorem B2224103 : Blo 2223435 2224103 := bstep (se 1 (by rfl) ⟨1668077, by rfl⟩ : syracuseStep 2224103 = 3336155) B3336155
theorem B2502121 : Blo 2223435 2502121 := bbase (se 2 (by rfl) ⟨938295, by rfl⟩ : syracuseStep 2502121 = 1876591) (by norm_num)
theorem B3336161 : Blo 2223435 3336161 := bstep (se 2 (by rfl) ⟨1251060, by rfl⟩ : syracuseStep 3336161 = 2502121) B2502121
theorem B2224107 : Blo 2223435 2224107 := bstep (se 1 (by rfl) ⟨1668080, by rfl⟩ : syracuseStep 2224107 = 3336161) B3336161
theorem B2375065 : Blo 2223435 2375065 := bbase (se 2 (by rfl) ⟨890649, by rfl⟩ : syracuseStep 2375065 = 1781299) (by norm_num)
theorem B12667013 : Blo 2223435 12667013 := bstep (se 4 (by rfl) ⟨1187532, by rfl⟩ : syracuseStep 12667013 = 2375065) B2375065
theorem B8444675 : Blo 2223435 8444675 := bstep (se 1 (by rfl) ⟨6333506, by rfl⟩ : syracuseStep 8444675 = 12667013) B12667013
theorem B5629783 : Blo 2223435 5629783 := bstep (se 1 (by rfl) ⟨4222337, by rfl⟩ : syracuseStep 5629783 = 8444675) B8444675
theorem B7506377 : Blo 2223435 7506377 := bstep (se 2 (by rfl) ⟨2814891, by rfl⟩ : syracuseStep 7506377 = 5629783) B5629783
theorem B5004251 : Blo 2223435 5004251 := bstep (se 1 (by rfl) ⟨3753188, by rfl⟩ : syracuseStep 5004251 = 7506377) B7506377
theorem B3336167 : Blo 2223435 3336167 := bstep (se 1 (by rfl) ⟨2502125, by rfl⟩ : syracuseStep 3336167 = 5004251) B5004251
theorem B2224111 : Blo 2223435 2224111 := bstep (se 1 (by rfl) ⟨1668083, by rfl⟩ : syracuseStep 2224111 = 3336167) B3336167
theorem B3336173 : Blo 2223435 3336173 := bbase (se 3 (by rfl) ⟨625532, by rfl⟩ : syracuseStep 3336173 = 1251065) (by norm_num)
theorem B2224115 : Blo 2223435 2224115 := bstep (se 1 (by rfl) ⟨1668086, by rfl⟩ : syracuseStep 2224115 = 3336173) B3336173
theorem B5004269 : Blo 2223435 5004269 := bbase (se 3 (by rfl) ⟨938300, by rfl⟩ : syracuseStep 5004269 = 1876601) (by norm_num)
theorem B3336179 : Blo 2223435 3336179 := bstep (se 1 (by rfl) ⟨2502134, by rfl⟩ : syracuseStep 3336179 = 5004269) B5004269
theorem B2224119 : Blo 2223435 2224119 := bstep (se 1 (by rfl) ⟨1668089, by rfl⟩ : syracuseStep 2224119 = 3336179) B3336179
theorem B4750157 : Blo 2223435 4750157 := bbase (se 3 (by rfl) ⟨890654, by rfl⟩ : syracuseStep 4750157 = 1781309) (by norm_num)
theorem B3166771 : Blo 2223435 3166771 := bstep (se 1 (by rfl) ⟨2375078, by rfl⟩ : syracuseStep 3166771 = 4750157) B4750157
theorem B4222361 : Blo 2223435 4222361 := bstep (se 2 (by rfl) ⟨1583385, by rfl⟩ : syracuseStep 4222361 = 3166771) B3166771
theorem B2814907 : Blo 2223435 2814907 := bstep (se 1 (by rfl) ⟨2111180, by rfl⟩ : syracuseStep 2814907 = 4222361) B4222361
theorem B3753209 : Blo 2223435 3753209 := bstep (se 2 (by rfl) ⟨1407453, by rfl⟩ : syracuseStep 3753209 = 2814907) B2814907
theorem B2502139 : Blo 2223435 2502139 := bstep (se 1 (by rfl) ⟨1876604, by rfl⟩ : syracuseStep 2502139 = 3753209) B3753209
theorem B3336185 : Blo 2223435 3336185 := bstep (se 2 (by rfl) ⟨1251069, by rfl⟩ : syracuseStep 3336185 = 2502139) B2502139
theorem B2224123 : Blo 2223435 2224123 := bstep (se 1 (by rfl) ⟨1668092, by rfl⟩ : syracuseStep 2224123 = 3336185) B3336185
theorem B23137973 : Blo 2223435 23137973 := bbase (se 5 (by rfl) ⟨1084592, by rfl⟩ : syracuseStep 23137973 = 2169185) (by norm_num)
theorem B15425315 : Blo 2223435 15425315 := bstep (se 1 (by rfl) ⟨11568986, by rfl⟩ : syracuseStep 15425315 = 23137973) B23137973
theorem B10283543 : Blo 2223435 10283543 := bstep (se 1 (by rfl) ⟨7712657, by rfl⟩ : syracuseStep 10283543 = 15425315) B15425315
theorem B6855695 : Blo 2223435 6855695 := bstep (se 1 (by rfl) ⟨5141771, by rfl⟩ : syracuseStep 6855695 = 10283543) B10283543
theorem B4570463 : Blo 2223435 4570463 := bstep (se 1 (by rfl) ⟨3427847, by rfl⟩ : syracuseStep 4570463 = 6855695) B6855695
theorem B12187901 : Blo 2223435 12187901 := bstep (se 3 (by rfl) ⟨2285231, by rfl⟩ : syracuseStep 12187901 = 4570463) B4570463
theorem B8125267 : Blo 2223435 8125267 := bstep (se 1 (by rfl) ⟨6093950, by rfl⟩ : syracuseStep 8125267 = 12187901) B12187901
theorem B10833689 : Blo 2223435 10833689 := bstep (se 2 (by rfl) ⟨4062633, by rfl⟩ : syracuseStep 10833689 = 8125267) B8125267
theorem B7222459 : Blo 2223435 7222459 := bstep (se 1 (by rfl) ⟨5416844, by rfl⟩ : syracuseStep 7222459 = 10833689) B10833689
theorem B9629945 : Blo 2223435 9629945 := bstep (se 2 (by rfl) ⟨3611229, by rfl⟩ : syracuseStep 9629945 = 7222459) B7222459
theorem B6419963 : Blo 2223435 6419963 := bstep (se 1 (by rfl) ⟨4814972, by rfl⟩ : syracuseStep 6419963 = 9629945) B9629945
theorem B4279975 : Blo 2223435 4279975 := bstep (se 1 (by rfl) ⟨3209981, by rfl⟩ : syracuseStep 4279975 = 6419963) B6419963
theorem B22826533 : Blo 2223435 22826533 := bstep (se 4 (by rfl) ⟨2139987, by rfl⟩ : syracuseStep 22826533 = 4279975) B4279975
theorem B30435377 : Blo 2223435 30435377 := bstep (se 2 (by rfl) ⟨11413266, by rfl⟩ : syracuseStep 30435377 = 22826533) B22826533
theorem B324644021 : Blo 2223435 324644021 := bstep (se 5 (by rfl) ⟨15217688, by rfl⟩ : syracuseStep 324644021 = 30435377) B30435377
theorem B216429347 : Blo 2223435 216429347 := bstep (se 1 (by rfl) ⟨162322010, by rfl⟩ : syracuseStep 216429347 = 324644021) B324644021
theorem B144286231 : Blo 2223435 144286231 := bstep (se 1 (by rfl) ⟨108214673, by rfl⟩ : syracuseStep 144286231 = 216429347) B216429347
theorem B192381641 : Blo 2223435 192381641 := bstep (se 2 (by rfl) ⟨72143115, by rfl⟩ : syracuseStep 192381641 = 144286231) B144286231
theorem B128254427 : Blo 2223435 128254427 := bstep (se 1 (by rfl) ⟨96190820, by rfl⟩ : syracuseStep 128254427 = 192381641) B192381641
theorem B85502951 : Blo 2223435 85502951 := bstep (se 1 (by rfl) ⟨64127213, by rfl⟩ : syracuseStep 85502951 = 128254427) B128254427
theorem B57001967 : Blo 2223435 57001967 := bstep (se 1 (by rfl) ⟨42751475, by rfl⟩ : syracuseStep 57001967 = 85502951) B85502951
theorem B38001311 : Blo 2223435 38001311 := bstep (se 1 (by rfl) ⟨28500983, by rfl⟩ : syracuseStep 38001311 = 57001967) B57001967
theorem B25334207 : Blo 2223435 25334207 := bstep (se 1 (by rfl) ⟨19000655, by rfl⟩ : syracuseStep 25334207 = 38001311) B38001311
theorem B16889471 : Blo 2223435 16889471 := bstep (se 1 (by rfl) ⟨12667103, by rfl⟩ : syracuseStep 16889471 = 25334207) B25334207
theorem B11259647 : Blo 2223435 11259647 := bstep (se 1 (by rfl) ⟨8444735, by rfl⟩ : syracuseStep 11259647 = 16889471) B16889471
theorem B7506431 : Blo 2223435 7506431 := bstep (se 1 (by rfl) ⟨5629823, by rfl⟩ : syracuseStep 7506431 = 11259647) B11259647
theorem B5004287 : Blo 2223435 5004287 := bstep (se 1 (by rfl) ⟨3753215, by rfl⟩ : syracuseStep 5004287 = 7506431) B7506431
theorem B3336191 : Blo 2223435 3336191 := bstep (se 1 (by rfl) ⟨2502143, by rfl⟩ : syracuseStep 3336191 = 5004287) B5004287
theorem B2224127 : Blo 2223435 2224127 := bstep (se 1 (by rfl) ⟨1668095, by rfl⟩ : syracuseStep 2224127 = 3336191) B3336191
theorem B3336197 : Blo 2223435 3336197 := bbase (se 4 (by rfl) ⟨312768, by rfl⟩ : syracuseStep 3336197 = 625537) (by norm_num)
theorem B2224131 : Blo 2223435 2224131 := bstep (se 1 (by rfl) ⟨1668098, by rfl⟩ : syracuseStep 2224131 = 3336197) B3336197
theorem B3753229 : Blo 2223435 3753229 := bbase (se 3 (by rfl) ⟨703730, by rfl⟩ : syracuseStep 3753229 = 1407461) (by norm_num)
theorem B5004305 : Blo 2223435 5004305 := bstep (se 2 (by rfl) ⟨1876614, by rfl⟩ : syracuseStep 5004305 = 3753229) B3753229
theorem B3336203 : Blo 2223435 3336203 := bstep (se 1 (by rfl) ⟨2502152, by rfl⟩ : syracuseStep 3336203 = 5004305) B5004305
theorem B2224135 : Blo 2223435 2224135 := bstep (se 1 (by rfl) ⟨1668101, by rfl⟩ : syracuseStep 2224135 = 3336203) B3336203
theorem B2502157 : Blo 2223435 2502157 := bbase (se 3 (by rfl) ⟨469154, by rfl⟩ : syracuseStep 2502157 = 938309) (by norm_num)
theorem B3336209 : Blo 2223435 3336209 := bstep (se 2 (by rfl) ⟨1251078, by rfl⟩ : syracuseStep 3336209 = 2502157) B2502157
theorem B2224139 : Blo 2223435 2224139 := bstep (se 1 (by rfl) ⟨1668104, by rfl⟩ : syracuseStep 2224139 = 3336209) B3336209
theorem B7506485 : Blo 2223435 7506485 := bbase (se 5 (by rfl) ⟨351866, by rfl⟩ : syracuseStep 7506485 = 703733) (by norm_num)
theorem B5004323 : Blo 2223435 5004323 := bstep (se 1 (by rfl) ⟨3753242, by rfl⟩ : syracuseStep 5004323 = 7506485) B7506485
theorem B3336215 : Blo 2223435 3336215 := bstep (se 1 (by rfl) ⟨2502161, by rfl⟩ : syracuseStep 3336215 = 5004323) B5004323
theorem B2224143 : Blo 2223435 2224143 := bstep (se 1 (by rfl) ⟨1668107, by rfl⟩ : syracuseStep 2224143 = 3336215) B3336215
theorem B3336221 : Blo 2223435 3336221 := bbase (se 3 (by rfl) ⟨625541, by rfl⟩ : syracuseStep 3336221 = 1251083) (by norm_num)
theorem B2224147 : Blo 2223435 2224147 := bstep (se 1 (by rfl) ⟨1668110, by rfl⟩ : syracuseStep 2224147 = 3336221) B3336221
theorem B5004341 : Blo 2223435 5004341 := bbase (se 5 (by rfl) ⟨234578, by rfl⟩ : syracuseStep 5004341 = 469157) (by norm_num)
theorem B3336227 : Blo 2223435 3336227 := bstep (se 1 (by rfl) ⟨2502170, by rfl⟩ : syracuseStep 3336227 = 5004341) B5004341
theorem B2224151 : Blo 2223435 2224151 := bstep (se 1 (by rfl) ⟨1668113, by rfl⟩ : syracuseStep 2224151 = 3336227) B3336227
theorem B8016005 : Blo 2223435 8016005 := bbase (se 4 (by rfl) ⟨751500, by rfl⟩ : syracuseStep 8016005 = 1503001) (by norm_num)
theorem B5344003 : Blo 2223435 5344003 := bstep (se 1 (by rfl) ⟨4008002, by rfl⟩ : syracuseStep 5344003 = 8016005) B8016005
theorem B7125337 : Blo 2223435 7125337 := bstep (se 2 (by rfl) ⟨2672001, by rfl⟩ : syracuseStep 7125337 = 5344003) B5344003
theorem B9500449 : Blo 2223435 9500449 := bstep (se 2 (by rfl) ⟨3562668, by rfl⟩ : syracuseStep 9500449 = 7125337) B7125337
theorem B12667265 : Blo 2223435 12667265 := bstep (se 2 (by rfl) ⟨4750224, by rfl⟩ : syracuseStep 12667265 = 9500449) B9500449
theorem B8444843 : Blo 2223435 8444843 := bstep (se 1 (by rfl) ⟨6333632, by rfl⟩ : syracuseStep 8444843 = 12667265) B12667265
theorem B5629895 : Blo 2223435 5629895 := bstep (se 1 (by rfl) ⟨4222421, by rfl⟩ : syracuseStep 5629895 = 8444843) B8444843
theorem B3753263 : Blo 2223435 3753263 := bstep (se 1 (by rfl) ⟨2814947, by rfl⟩ : syracuseStep 3753263 = 5629895) B5629895
theorem B2502175 : Blo 2223435 2502175 := bstep (se 1 (by rfl) ⟨1876631, by rfl⟩ : syracuseStep 2502175 = 3753263) B3753263
theorem B3336233 : Blo 2223435 3336233 := bstep (se 2 (by rfl) ⟨1251087, by rfl⟩ : syracuseStep 3336233 = 2502175) B2502175
theorem B2224155 : Blo 2223435 2224155 := bstep (se 1 (by rfl) ⟨1668116, by rfl⟩ : syracuseStep 2224155 = 3336233) B3336233
theorem B7125349 : Blo 2223435 7125349 := bbase (se 4 (by rfl) ⟨668001, by rfl⟩ : syracuseStep 7125349 = 1336003) (by norm_num)
theorem B9500465 : Blo 2223435 9500465 := bstep (se 2 (by rfl) ⟨3562674, by rfl⟩ : syracuseStep 9500465 = 7125349) B7125349
theorem B6333643 : Blo 2223435 6333643 := bstep (se 1 (by rfl) ⟨4750232, by rfl⟩ : syracuseStep 6333643 = 9500465) B9500465
theorem B8444857 : Blo 2223435 8444857 := bstep (se 2 (by rfl) ⟨3166821, by rfl⟩ : syracuseStep 8444857 = 6333643) B6333643
theorem B11259809 : Blo 2223435 11259809 := bstep (se 2 (by rfl) ⟨4222428, by rfl⟩ : syracuseStep 11259809 = 8444857) B8444857
theorem B7506539 : Blo 2223435 7506539 := bstep (se 1 (by rfl) ⟨5629904, by rfl⟩ : syracuseStep 7506539 = 11259809) B11259809
theorem B5004359 : Blo 2223435 5004359 := bstep (se 1 (by rfl) ⟨3753269, by rfl⟩ : syracuseStep 5004359 = 7506539) B7506539
theorem B3336239 : Blo 2223435 3336239 := bstep (se 1 (by rfl) ⟨2502179, by rfl⟩ : syracuseStep 3336239 = 5004359) B5004359
theorem B2224159 : Blo 2223435 2224159 := bstep (se 1 (by rfl) ⟨1668119, by rfl⟩ : syracuseStep 2224159 = 3336239) B3336239
theorem B3336245 : Blo 2223435 3336245 := bbase (se 5 (by rfl) ⟨156386, by rfl⟩ : syracuseStep 3336245 = 312773) (by norm_num)
theorem B2224163 : Blo 2223435 2224163 := bstep (se 1 (by rfl) ⟨1668122, by rfl⟩ : syracuseStep 2224163 = 3336245) B3336245
theorem B5629925 : Blo 2223435 5629925 := bbase (se 4 (by rfl) ⟨527805, by rfl⟩ : syracuseStep 5629925 = 1055611) (by norm_num)
theorem B3753283 : Blo 2223435 3753283 := bstep (se 1 (by rfl) ⟨2814962, by rfl⟩ : syracuseStep 3753283 = 5629925) B5629925
theorem B5004377 : Blo 2223435 5004377 := bstep (se 2 (by rfl) ⟨1876641, by rfl⟩ : syracuseStep 5004377 = 3753283) B3753283
theorem B3336251 : Blo 2223435 3336251 := bstep (se 1 (by rfl) ⟨2502188, by rfl⟩ : syracuseStep 3336251 = 5004377) B5004377
theorem B2224167 : Blo 2223435 2224167 := bstep (se 1 (by rfl) ⟨1668125, by rfl⟩ : syracuseStep 2224167 = 3336251) B3336251
theorem B2502193 : Blo 2223435 2502193 := bbase (se 2 (by rfl) ⟨938322, by rfl⟩ : syracuseStep 2502193 = 1876645) (by norm_num)
theorem B3336257 : Blo 2223435 3336257 := bstep (se 2 (by rfl) ⟨1251096, by rfl⟩ : syracuseStep 3336257 = 2502193) B2502193
theorem B2224171 : Blo 2223435 2224171 := bstep (se 1 (by rfl) ⟨1668128, by rfl⟩ : syracuseStep 2224171 = 3336257) B3336257
theorem B3006029 : Blo 2223435 3006029 := bbase (se 3 (by rfl) ⟨563630, by rfl⟩ : syracuseStep 3006029 = 1127261) (by norm_num)
theorem B8016077 : Blo 2223435 8016077 := bstep (se 3 (by rfl) ⟨1503014, by rfl⟩ : syracuseStep 8016077 = 3006029) B3006029
theorem B5344051 : Blo 2223435 5344051 := bstep (se 1 (by rfl) ⟨4008038, by rfl⟩ : syracuseStep 5344051 = 8016077) B8016077
theorem B7125401 : Blo 2223435 7125401 := bstep (se 2 (by rfl) ⟨2672025, by rfl⟩ : syracuseStep 7125401 = 5344051) B5344051
theorem B4750267 : Blo 2223435 4750267 := bstep (se 1 (by rfl) ⟨3562700, by rfl⟩ : syracuseStep 4750267 = 7125401) B7125401
theorem B6333689 : Blo 2223435 6333689 := bstep (se 2 (by rfl) ⟨2375133, by rfl⟩ : syracuseStep 6333689 = 4750267) B4750267
theorem B4222459 : Blo 2223435 4222459 := bstep (se 1 (by rfl) ⟨3166844, by rfl⟩ : syracuseStep 4222459 = 6333689) B6333689
theorem B5629945 : Blo 2223435 5629945 := bstep (se 2 (by rfl) ⟨2111229, by rfl⟩ : syracuseStep 5629945 = 4222459) B4222459
theorem B7506593 : Blo 2223435 7506593 := bstep (se 2 (by rfl) ⟨2814972, by rfl⟩ : syracuseStep 7506593 = 5629945) B5629945
theorem B5004395 : Blo 2223435 5004395 := bstep (se 1 (by rfl) ⟨3753296, by rfl⟩ : syracuseStep 5004395 = 7506593) B7506593
theorem B3336263 : Blo 2223435 3336263 := bstep (se 1 (by rfl) ⟨2502197, by rfl⟩ : syracuseStep 3336263 = 5004395) B5004395
theorem B2224175 : Blo 2223435 2224175 := bstep (se 1 (by rfl) ⟨1668131, by rfl⟩ : syracuseStep 2224175 = 3336263) B3336263
theorem B3336269 : Blo 2223435 3336269 := bbase (se 3 (by rfl) ⟨625550, by rfl⟩ : syracuseStep 3336269 = 1251101) (by norm_num)
theorem B2224179 : Blo 2223435 2224179 := bstep (se 1 (by rfl) ⟨1668134, by rfl⟩ : syracuseStep 2224179 = 3336269) B3336269
theorem B5004413 : Blo 2223435 5004413 := bbase (se 3 (by rfl) ⟨938327, by rfl⟩ : syracuseStep 5004413 = 1876655) (by norm_num)
theorem B3336275 : Blo 2223435 3336275 := bstep (se 1 (by rfl) ⟨2502206, by rfl⟩ : syracuseStep 3336275 = 5004413) B5004413
theorem B2224183 : Blo 2223435 2224183 := bstep (se 1 (by rfl) ⟨1668137, by rfl⟩ : syracuseStep 2224183 = 3336275) B3336275
theorem B3753317 : Blo 2223435 3753317 := bbase (se 4 (by rfl) ⟨351873, by rfl⟩ : syracuseStep 3753317 = 703747) (by norm_num)
theorem B2502211 : Blo 2223435 2502211 := bstep (se 1 (by rfl) ⟨1876658, by rfl⟩ : syracuseStep 2502211 = 3753317) B3753317
theorem B3336281 : Blo 2223435 3336281 := bstep (se 2 (by rfl) ⟨1251105, by rfl⟩ : syracuseStep 3336281 = 2502211) B2502211
theorem B2224187 : Blo 2223435 2224187 := bstep (se 1 (by rfl) ⟨1668140, by rfl⟩ : syracuseStep 2224187 = 3336281) B3336281
theorem B4750301 : Blo 2223435 4750301 := bbase (se 3 (by rfl) ⟨890681, by rfl⟩ : syracuseStep 4750301 = 1781363) (by norm_num)
theorem B3166867 : Blo 2223435 3166867 := bstep (se 1 (by rfl) ⟨2375150, by rfl⟩ : syracuseStep 3166867 = 4750301) B4750301
theorem B16889957 : Blo 2223435 16889957 := bstep (se 4 (by rfl) ⟨1583433, by rfl⟩ : syracuseStep 16889957 = 3166867) B3166867
theorem B11259971 : Blo 2223435 11259971 := bstep (se 1 (by rfl) ⟨8444978, by rfl⟩ : syracuseStep 11259971 = 16889957) B16889957
theorem B7506647 : Blo 2223435 7506647 := bstep (se 1 (by rfl) ⟨5629985, by rfl⟩ : syracuseStep 7506647 = 11259971) B11259971
theorem B5004431 : Blo 2223435 5004431 := bstep (se 1 (by rfl) ⟨3753323, by rfl⟩ : syracuseStep 5004431 = 7506647) B7506647
theorem B3336287 : Blo 2223435 3336287 := bstep (se 1 (by rfl) ⟨2502215, by rfl⟩ : syracuseStep 3336287 = 5004431) B5004431
theorem B2224191 : Blo 2223435 2224191 := bstep (se 1 (by rfl) ⟨1668143, by rfl⟩ : syracuseStep 2224191 = 3336287) B3336287
theorem B3336293 : Blo 2223435 3336293 := bbase (se 4 (by rfl) ⟨312777, by rfl⟩ : syracuseStep 3336293 = 625555) (by norm_num)
theorem B2224195 : Blo 2223435 2224195 := bstep (se 1 (by rfl) ⟨1668146, by rfl⟩ : syracuseStep 2224195 = 3336293) B3336293
theorem B5706821 : Blo 2223435 5706821 := bbase (se 4 (by rfl) ⟨535014, by rfl⟩ : syracuseStep 5706821 = 1070029) (by norm_num)
theorem B15218189 : Blo 2223435 15218189 := bstep (se 3 (by rfl) ⟨2853410, by rfl⟩ : syracuseStep 15218189 = 5706821) B5706821
theorem B10145459 : Blo 2223435 10145459 := bstep (se 1 (by rfl) ⟨7609094, by rfl⟩ : syracuseStep 10145459 = 15218189) B15218189
theorem B27054557 : Blo 2223435 27054557 := bstep (se 3 (by rfl) ⟨5072729, by rfl⟩ : syracuseStep 27054557 = 10145459) B10145459
theorem B18036371 : Blo 2223435 18036371 := bstep (se 1 (by rfl) ⟨13527278, by rfl⟩ : syracuseStep 18036371 = 27054557) B27054557
theorem B12024247 : Blo 2223435 12024247 := bstep (se 1 (by rfl) ⟨9018185, by rfl⟩ : syracuseStep 12024247 = 18036371) B18036371
theorem B16032329 : Blo 2223435 16032329 := bstep (se 2 (by rfl) ⟨6012123, by rfl⟩ : syracuseStep 16032329 = 12024247) B12024247
theorem B10688219 : Blo 2223435 10688219 := bstep (se 1 (by rfl) ⟨8016164, by rfl⟩ : syracuseStep 10688219 = 16032329) B16032329
theorem B7125479 : Blo 2223435 7125479 := bstep (se 1 (by rfl) ⟨5344109, by rfl⟩ : syracuseStep 7125479 = 10688219) B10688219
theorem B4750319 : Blo 2223435 4750319 := bstep (se 1 (by rfl) ⟨3562739, by rfl⟩ : syracuseStep 4750319 = 7125479) B7125479
theorem B3166879 : Blo 2223435 3166879 := bstep (se 1 (by rfl) ⟨2375159, by rfl⟩ : syracuseStep 3166879 = 4750319) B4750319
theorem B4222505 : Blo 2223435 4222505 := bstep (se 2 (by rfl) ⟨1583439, by rfl⟩ : syracuseStep 4222505 = 3166879) B3166879
theorem B2815003 : Blo 2223435 2815003 := bstep (se 1 (by rfl) ⟨2111252, by rfl⟩ : syracuseStep 2815003 = 4222505) B4222505
theorem B3753337 : Blo 2223435 3753337 := bstep (se 2 (by rfl) ⟨1407501, by rfl⟩ : syracuseStep 3753337 = 2815003) B2815003
theorem B5004449 : Blo 2223435 5004449 := bstep (se 2 (by rfl) ⟨1876668, by rfl⟩ : syracuseStep 5004449 = 3753337) B3753337
theorem B3336299 : Blo 2223435 3336299 := bstep (se 1 (by rfl) ⟨2502224, by rfl⟩ : syracuseStep 3336299 = 5004449) B5004449
theorem B2224199 : Blo 2223435 2224199 := bstep (se 1 (by rfl) ⟨1668149, by rfl⟩ : syracuseStep 2224199 = 3336299) B3336299
theorem B2502229 : Blo 2223435 2502229 := bbase (se 8 (by rfl) ⟨14661, by rfl⟩ : syracuseStep 2502229 = 29323) (by norm_num)
theorem B3336305 : Blo 2223435 3336305 := bstep (se 2 (by rfl) ⟨1251114, by rfl⟩ : syracuseStep 3336305 = 2502229) B2502229
theorem B2224203 : Blo 2223435 2224203 := bstep (se 1 (by rfl) ⟨1668152, by rfl⟩ : syracuseStep 2224203 = 3336305) B3336305
theorem B2815013 : Blo 2223435 2815013 := bbase (se 4 (by rfl) ⟨263907, by rfl⟩ : syracuseStep 2815013 = 527815) (by norm_num)
theorem B7506701 : Blo 2223435 7506701 := bstep (se 3 (by rfl) ⟨1407506, by rfl⟩ : syracuseStep 7506701 = 2815013) B2815013
theorem B5004467 : Blo 2223435 5004467 := bstep (se 1 (by rfl) ⟨3753350, by rfl⟩ : syracuseStep 5004467 = 7506701) B7506701
theorem B3336311 : Blo 2223435 3336311 := bstep (se 1 (by rfl) ⟨2502233, by rfl⟩ : syracuseStep 3336311 = 5004467) B5004467
theorem B2224207 : Blo 2223435 2224207 := bstep (se 1 (by rfl) ⟨1668155, by rfl⟩ : syracuseStep 2224207 = 3336311) B3336311
theorem B3336317 : Blo 2223435 3336317 := bbase (se 3 (by rfl) ⟨625559, by rfl⟩ : syracuseStep 3336317 = 1251119) (by norm_num)
theorem B2224211 : Blo 2223435 2224211 := bstep (se 1 (by rfl) ⟨1668158, by rfl⟩ : syracuseStep 2224211 = 3336317) B3336317
theorem B5004485 : Blo 2223435 5004485 := bbase (se 4 (by rfl) ⟨469170, by rfl⟩ : syracuseStep 5004485 = 938341) (by norm_num)
theorem B3336323 : Blo 2223435 3336323 := bstep (se 1 (by rfl) ⟨2502242, by rfl⟩ : syracuseStep 3336323 = 5004485) B5004485
theorem B2224215 : Blo 2223435 2224215 := bstep (se 1 (by rfl) ⟨1668161, by rfl⟩ : syracuseStep 2224215 = 3336323) B3336323
theorem B5344157 : Blo 2223435 5344157 := bbase (se 3 (by rfl) ⟨1002029, by rfl⟩ : syracuseStep 5344157 = 2004059) (by norm_num)
theorem B14251085 : Blo 2223435 14251085 := bstep (se 3 (by rfl) ⟨2672078, by rfl⟩ : syracuseStep 14251085 = 5344157) B5344157
theorem B9500723 : Blo 2223435 9500723 := bstep (se 1 (by rfl) ⟨7125542, by rfl⟩ : syracuseStep 9500723 = 14251085) B14251085
theorem B6333815 : Blo 2223435 6333815 := bstep (se 1 (by rfl) ⟨4750361, by rfl⟩ : syracuseStep 6333815 = 9500723) B9500723
theorem B4222543 : Blo 2223435 4222543 := bstep (se 1 (by rfl) ⟨3166907, by rfl⟩ : syracuseStep 4222543 = 6333815) B6333815
theorem B5630057 : Blo 2223435 5630057 := bstep (se 2 (by rfl) ⟨2111271, by rfl⟩ : syracuseStep 5630057 = 4222543) B4222543
theorem B3753371 : Blo 2223435 3753371 := bstep (se 1 (by rfl) ⟨2815028, by rfl⟩ : syracuseStep 3753371 = 5630057) B5630057
theorem B2502247 : Blo 2223435 2502247 := bstep (se 1 (by rfl) ⟨1876685, by rfl⟩ : syracuseStep 2502247 = 3753371) B3753371
theorem B3336329 : Blo 2223435 3336329 := bstep (se 2 (by rfl) ⟨1251123, by rfl⟩ : syracuseStep 3336329 = 2502247) B2502247
theorem B2224219 : Blo 2223435 2224219 := bstep (se 1 (by rfl) ⟨1668164, by rfl⟩ : syracuseStep 2224219 = 3336329) B3336329
theorem B11260133 : Blo 2223435 11260133 := bbase (se 4 (by rfl) ⟨1055637, by rfl⟩ : syracuseStep 11260133 = 2111275) (by norm_num)
theorem B7506755 : Blo 2223435 7506755 := bstep (se 1 (by rfl) ⟨5630066, by rfl⟩ : syracuseStep 7506755 = 11260133) B11260133
theorem B5004503 : Blo 2223435 5004503 := bstep (se 1 (by rfl) ⟨3753377, by rfl⟩ : syracuseStep 5004503 = 7506755) B7506755
theorem B3336335 : Blo 2223435 3336335 := bstep (se 1 (by rfl) ⟨2502251, by rfl⟩ : syracuseStep 3336335 = 5004503) B5004503
theorem B2224223 : Blo 2223435 2224223 := bstep (se 1 (by rfl) ⟨1668167, by rfl⟩ : syracuseStep 2224223 = 3336335) B3336335
theorem B3336341 : Blo 2223435 3336341 := bbase (se 6 (by rfl) ⟨78195, by rfl⟩ : syracuseStep 3336341 = 156391) (by norm_num)
theorem B2224227 : Blo 2223435 2224227 := bstep (se 1 (by rfl) ⟨1668170, by rfl⟩ : syracuseStep 2224227 = 3336341) B3336341
theorem B9500773 : Blo 2223435 9500773 := bbase (se 4 (by rfl) ⟨890697, by rfl⟩ : syracuseStep 9500773 = 1781395) (by norm_num)
theorem B12667697 : Blo 2223435 12667697 := bstep (se 2 (by rfl) ⟨4750386, by rfl⟩ : syracuseStep 12667697 = 9500773) B9500773
theorem B8445131 : Blo 2223435 8445131 := bstep (se 1 (by rfl) ⟨6333848, by rfl⟩ : syracuseStep 8445131 = 12667697) B12667697
theorem B5630087 : Blo 2223435 5630087 := bstep (se 1 (by rfl) ⟨4222565, by rfl⟩ : syracuseStep 5630087 = 8445131) B8445131
theorem B3753391 : Blo 2223435 3753391 := bstep (se 1 (by rfl) ⟨2815043, by rfl⟩ : syracuseStep 3753391 = 5630087) B5630087
theorem B5004521 : Blo 2223435 5004521 := bstep (se 2 (by rfl) ⟨1876695, by rfl⟩ : syracuseStep 5004521 = 3753391) B3753391
theorem B3336347 : Blo 2223435 3336347 := bstep (se 1 (by rfl) ⟨2502260, by rfl⟩ : syracuseStep 3336347 = 5004521) B5004521
theorem B2224231 : Blo 2223435 2224231 := bstep (se 1 (by rfl) ⟨1668173, by rfl⟩ : syracuseStep 2224231 = 3336347) B3336347
theorem B2502265 : Blo 2223435 2502265 := bbase (se 2 (by rfl) ⟨938349, by rfl⟩ : syracuseStep 2502265 = 1876699) (by norm_num)
theorem B3336353 : Blo 2223435 3336353 := bstep (se 2 (by rfl) ⟨1251132, by rfl⟩ : syracuseStep 3336353 = 2502265) B2502265
theorem B2224235 : Blo 2223435 2224235 := bstep (se 1 (by rfl) ⟨1668176, by rfl⟩ : syracuseStep 2224235 = 3336353) B3336353
theorem B4509173 : Blo 2223435 4509173 := bbase (se 5 (by rfl) ⟨211367, by rfl⟩ : syracuseStep 4509173 = 422735) (by norm_num)
theorem B3006115 : Blo 2223435 3006115 := bstep (se 1 (by rfl) ⟨2254586, by rfl⟩ : syracuseStep 3006115 = 4509173) B4509173
theorem B16032613 : Blo 2223435 16032613 := bstep (se 4 (by rfl) ⟨1503057, by rfl⟩ : syracuseStep 16032613 = 3006115) B3006115
theorem B21376817 : Blo 2223435 21376817 := bstep (se 2 (by rfl) ⟨8016306, by rfl⟩ : syracuseStep 21376817 = 16032613) B16032613
theorem B14251211 : Blo 2223435 14251211 := bstep (se 1 (by rfl) ⟨10688408, by rfl⟩ : syracuseStep 14251211 = 21376817) B21376817
theorem B9500807 : Blo 2223435 9500807 := bstep (se 1 (by rfl) ⟨7125605, by rfl⟩ : syracuseStep 9500807 = 14251211) B14251211
theorem B6333871 : Blo 2223435 6333871 := bstep (se 1 (by rfl) ⟨4750403, by rfl⟩ : syracuseStep 6333871 = 9500807) B9500807
theorem B8445161 : Blo 2223435 8445161 := bstep (se 2 (by rfl) ⟨3166935, by rfl⟩ : syracuseStep 8445161 = 6333871) B6333871
theorem B5630107 : Blo 2223435 5630107 := bstep (se 1 (by rfl) ⟨4222580, by rfl⟩ : syracuseStep 5630107 = 8445161) B8445161
theorem B7506809 : Blo 2223435 7506809 := bstep (se 2 (by rfl) ⟨2815053, by rfl⟩ : syracuseStep 7506809 = 5630107) B5630107
theorem B5004539 : Blo 2223435 5004539 := bstep (se 1 (by rfl) ⟨3753404, by rfl⟩ : syracuseStep 5004539 = 7506809) B7506809
theorem B3336359 : Blo 2223435 3336359 := bstep (se 1 (by rfl) ⟨2502269, by rfl⟩ : syracuseStep 3336359 = 5004539) B5004539
theorem B2224239 : Blo 2223435 2224239 := bstep (se 1 (by rfl) ⟨1668179, by rfl⟩ : syracuseStep 2224239 = 3336359) B3336359
theorem B3336365 : Blo 2223435 3336365 := bbase (se 3 (by rfl) ⟨625568, by rfl⟩ : syracuseStep 3336365 = 1251137) (by norm_num)
theorem B2224243 : Blo 2223435 2224243 := bstep (se 1 (by rfl) ⟨1668182, by rfl⟩ : syracuseStep 2224243 = 3336365) B3336365
theorem B5004557 : Blo 2223435 5004557 := bbase (se 3 (by rfl) ⟨938354, by rfl⟩ : syracuseStep 5004557 = 1876709) (by norm_num)
theorem B3336371 : Blo 2223435 3336371 := bstep (se 1 (by rfl) ⟨2502278, by rfl⟩ : syracuseStep 3336371 = 5004557) B5004557
theorem B2224247 : Blo 2223435 2224247 := bstep (se 1 (by rfl) ⟨1668185, by rfl⟩ : syracuseStep 2224247 = 3336371) B3336371
theorem B2815069 : Blo 2223435 2815069 := bbase (se 3 (by rfl) ⟨527825, by rfl⟩ : syracuseStep 2815069 = 1055651) (by norm_num)
theorem B3753425 : Blo 2223435 3753425 := bstep (se 2 (by rfl) ⟨1407534, by rfl⟩ : syracuseStep 3753425 = 2815069) B2815069
theorem B2502283 : Blo 2223435 2502283 := bstep (se 1 (by rfl) ⟨1876712, by rfl⟩ : syracuseStep 2502283 = 3753425) B3753425
theorem B3336377 : Blo 2223435 3336377 := bstep (se 2 (by rfl) ⟨1251141, by rfl⟩ : syracuseStep 3336377 = 2502283) B2502283
theorem B2224251 : Blo 2223435 2224251 := bstep (se 1 (by rfl) ⟨1668188, by rfl⟩ : syracuseStep 2224251 = 3336377) B3336377
theorem B19001749 : Blo 2223435 19001749 := bbase (se 6 (by rfl) ⟨445353, by rfl⟩ : syracuseStep 19001749 = 890707) (by norm_num)
theorem B25335665 : Blo 2223435 25335665 := bstep (se 2 (by rfl) ⟨9500874, by rfl⟩ : syracuseStep 25335665 = 19001749) B19001749
theorem B16890443 : Blo 2223435 16890443 := bstep (se 1 (by rfl) ⟨12667832, by rfl⟩ : syracuseStep 16890443 = 25335665) B25335665
theorem B11260295 : Blo 2223435 11260295 := bstep (se 1 (by rfl) ⟨8445221, by rfl⟩ : syracuseStep 11260295 = 16890443) B16890443
theorem B7506863 : Blo 2223435 7506863 := bstep (se 1 (by rfl) ⟨5630147, by rfl⟩ : syracuseStep 7506863 = 11260295) B11260295
theorem B5004575 : Blo 2223435 5004575 := bstep (se 1 (by rfl) ⟨3753431, by rfl⟩ : syracuseStep 5004575 = 7506863) B7506863
theorem B3336383 : Blo 2223435 3336383 := bstep (se 1 (by rfl) ⟨2502287, by rfl⟩ : syracuseStep 3336383 = 5004575) B5004575
theorem B2224255 : Blo 2223435 2224255 := bstep (se 1 (by rfl) ⟨1668191, by rfl⟩ : syracuseStep 2224255 = 3336383) B3336383
theorem B3336389 : Blo 2223435 3336389 := bbase (se 4 (by rfl) ⟨312786, by rfl⟩ : syracuseStep 3336389 = 625573) (by norm_num)
theorem B2224259 : Blo 2223435 2224259 := bstep (se 1 (by rfl) ⟨1668194, by rfl⟩ : syracuseStep 2224259 = 3336389) B3336389
theorem B3753445 : Blo 2223435 3753445 := bbase (se 4 (by rfl) ⟨351885, by rfl⟩ : syracuseStep 3753445 = 703771) (by norm_num)
theorem B5004593 : Blo 2223435 5004593 := bstep (se 2 (by rfl) ⟨1876722, by rfl⟩ : syracuseStep 5004593 = 3753445) B3753445
theorem B3336395 : Blo 2223435 3336395 := bstep (se 1 (by rfl) ⟨2502296, by rfl⟩ : syracuseStep 3336395 = 5004593) B5004593
theorem B2224263 : Blo 2223435 2224263 := bstep (se 1 (by rfl) ⟨1668197, by rfl⟩ : syracuseStep 2224263 = 3336395) B3336395
theorem B2502301 : Blo 2223435 2502301 := bbase (se 3 (by rfl) ⟨469181, by rfl⟩ : syracuseStep 2502301 = 938363) (by norm_num)
theorem B3336401 : Blo 2223435 3336401 := bstep (se 2 (by rfl) ⟨1251150, by rfl⟩ : syracuseStep 3336401 = 2502301) B2502301
theorem B2224267 : Blo 2223435 2224267 := bstep (se 1 (by rfl) ⟨1668200, by rfl⟩ : syracuseStep 2224267 = 3336401) B3336401
theorem B7506917 : Blo 2223435 7506917 := bbase (se 4 (by rfl) ⟨703773, by rfl⟩ : syracuseStep 7506917 = 1407547) (by norm_num)
theorem B5004611 : Blo 2223435 5004611 := bstep (se 1 (by rfl) ⟨3753458, by rfl⟩ : syracuseStep 5004611 = 7506917) B7506917
theorem B3336407 : Blo 2223435 3336407 := bstep (se 1 (by rfl) ⟨2502305, by rfl⟩ : syracuseStep 3336407 = 5004611) B5004611
theorem B2224271 : Blo 2223435 2224271 := bstep (se 1 (by rfl) ⟨1668203, by rfl⟩ : syracuseStep 2224271 = 3336407) B3336407
theorem B3336413 : Blo 2223435 3336413 := bbase (se 3 (by rfl) ⟨625577, by rfl⟩ : syracuseStep 3336413 = 1251155) (by norm_num)
theorem B2224275 : Blo 2223435 2224275 := bstep (se 1 (by rfl) ⟨1668206, by rfl⟩ : syracuseStep 2224275 = 3336413) B3336413
theorem B5004629 : Blo 2223435 5004629 := bbase (se 11 (by rfl) ⟨3665, by rfl⟩ : syracuseStep 5004629 = 7331) (by norm_num)
theorem B3336419 : Blo 2223435 3336419 := bstep (se 1 (by rfl) ⟨2502314, by rfl⟩ : syracuseStep 3336419 = 5004629) B5004629
theorem B2224279 : Blo 2223435 2224279 := bstep (se 1 (by rfl) ⟨1668209, by rfl⟩ : syracuseStep 2224279 = 3336419) B3336419
theorem B2375249 : Blo 2223435 2375249 := bbase (se 2 (by rfl) ⟨890718, by rfl⟩ : syracuseStep 2375249 = 1781437) (by norm_num)
theorem B6333997 : Blo 2223435 6333997 := bstep (se 3 (by rfl) ⟨1187624, by rfl⟩ : syracuseStep 6333997 = 2375249) B2375249
theorem B8445329 : Blo 2223435 8445329 := bstep (se 2 (by rfl) ⟨3166998, by rfl⟩ : syracuseStep 8445329 = 6333997) B6333997
theorem B5630219 : Blo 2223435 5630219 := bstep (se 1 (by rfl) ⟨4222664, by rfl⟩ : syracuseStep 5630219 = 8445329) B8445329
theorem B3753479 : Blo 2223435 3753479 := bstep (se 1 (by rfl) ⟨2815109, by rfl⟩ : syracuseStep 3753479 = 5630219) B5630219
theorem B2502319 : Blo 2223435 2502319 := bstep (se 1 (by rfl) ⟨1876739, by rfl⟩ : syracuseStep 2502319 = 3753479) B3753479
theorem B3336425 : Blo 2223435 3336425 := bstep (se 2 (by rfl) ⟨1251159, by rfl⟩ : syracuseStep 3336425 = 2502319) B2502319
theorem B2224283 : Blo 2223435 2224283 := bstep (se 1 (by rfl) ⟨1668212, by rfl⟩ : syracuseStep 2224283 = 3336425) B3336425
theorem B10834469 : Blo 2223435 10834469 := bbase (se 4 (by rfl) ⟨1015731, by rfl⟩ : syracuseStep 10834469 = 2031463) (by norm_num)
theorem B7222979 : Blo 2223435 7222979 := bstep (se 1 (by rfl) ⟨5417234, by rfl⟩ : syracuseStep 7222979 = 10834469) B10834469
theorem B4815319 : Blo 2223435 4815319 := bstep (se 1 (by rfl) ⟨3611489, by rfl⟩ : syracuseStep 4815319 = 7222979) B7222979
theorem B6420425 : Blo 2223435 6420425 := bstep (se 2 (by rfl) ⟨2407659, by rfl⟩ : syracuseStep 6420425 = 4815319) B4815319
theorem B17121133 : Blo 2223435 17121133 := bstep (se 3 (by rfl) ⟨3210212, by rfl⟩ : syracuseStep 17121133 = 6420425) B6420425
theorem B22828177 : Blo 2223435 22828177 := bstep (se 2 (by rfl) ⟨8560566, by rfl⟩ : syracuseStep 22828177 = 17121133) B17121133
theorem B30437569 : Blo 2223435 30437569 := bstep (se 2 (by rfl) ⟨11414088, by rfl⟩ : syracuseStep 30437569 = 22828177) B22828177
theorem B40583425 : Blo 2223435 40583425 := bstep (se 2 (by rfl) ⟨15218784, by rfl⟩ : syracuseStep 40583425 = 30437569) B30437569
theorem B54111233 : Blo 2223435 54111233 := bstep (se 2 (by rfl) ⟨20291712, by rfl⟩ : syracuseStep 54111233 = 40583425) B40583425
theorem B36074155 : Blo 2223435 36074155 := bstep (se 1 (by rfl) ⟨27055616, by rfl⟩ : syracuseStep 36074155 = 54111233) B54111233
theorem B48098873 : Blo 2223435 48098873 := bstep (se 2 (by rfl) ⟨18037077, by rfl⟩ : syracuseStep 48098873 = 36074155) B36074155
theorem B32065915 : Blo 2223435 32065915 := bstep (se 1 (by rfl) ⟨24049436, by rfl⟩ : syracuseStep 32065915 = 48098873) B48098873
theorem B42754553 : Blo 2223435 42754553 := bstep (se 2 (by rfl) ⟨16032957, by rfl⟩ : syracuseStep 42754553 = 32065915) B32065915
theorem B28503035 : Blo 2223435 28503035 := bstep (se 1 (by rfl) ⟨21377276, by rfl⟩ : syracuseStep 28503035 = 42754553) B42754553
theorem B19002023 : Blo 2223435 19002023 := bstep (se 1 (by rfl) ⟨14251517, by rfl⟩ : syracuseStep 19002023 = 28503035) B28503035
theorem B12668015 : Blo 2223435 12668015 := bstep (se 1 (by rfl) ⟨9501011, by rfl⟩ : syracuseStep 12668015 = 19002023) B19002023
theorem B8445343 : Blo 2223435 8445343 := bstep (se 1 (by rfl) ⟨6334007, by rfl⟩ : syracuseStep 8445343 = 12668015) B12668015
theorem B11260457 : Blo 2223435 11260457 := bstep (se 2 (by rfl) ⟨4222671, by rfl⟩ : syracuseStep 11260457 = 8445343) B8445343
theorem B7506971 : Blo 2223435 7506971 := bstep (se 1 (by rfl) ⟨5630228, by rfl⟩ : syracuseStep 7506971 = 11260457) B11260457
theorem B5004647 : Blo 2223435 5004647 := bstep (se 1 (by rfl) ⟨3753485, by rfl⟩ : syracuseStep 5004647 = 7506971) B7506971
theorem B3336431 : Blo 2223435 3336431 := bstep (se 1 (by rfl) ⟨2502323, by rfl⟩ : syracuseStep 3336431 = 5004647) B5004647
theorem B2224287 : Blo 2223435 2224287 := bstep (se 1 (by rfl) ⟨1668215, by rfl⟩ : syracuseStep 2224287 = 3336431) B3336431
theorem B3336437 : Blo 2223435 3336437 := bbase (se 5 (by rfl) ⟨156395, by rfl⟩ : syracuseStep 3336437 = 312791) (by norm_num)
theorem B2224291 : Blo 2223435 2224291 := bstep (se 1 (by rfl) ⟨1668218, by rfl⟩ : syracuseStep 2224291 = 3336437) B3336437
theorem B9630677 : Blo 2223435 9630677 := bbase (se 7 (by rfl) ⟨112859, by rfl⟩ : syracuseStep 9630677 = 225719) (by norm_num)
theorem B25681805 : Blo 2223435 25681805 := bstep (se 3 (by rfl) ⟨4815338, by rfl⟩ : syracuseStep 25681805 = 9630677) B9630677
theorem B17121203 : Blo 2223435 17121203 := bstep (se 1 (by rfl) ⟨12840902, by rfl⟩ : syracuseStep 17121203 = 25681805) B25681805
theorem B11414135 : Blo 2223435 11414135 := bstep (se 1 (by rfl) ⟨8560601, by rfl⟩ : syracuseStep 11414135 = 17121203) B17121203
theorem B7609423 : Blo 2223435 7609423 := bstep (se 1 (by rfl) ⟨5707067, by rfl⟩ : syracuseStep 7609423 = 11414135) B11414135
theorem B10145897 : Blo 2223435 10145897 := bstep (se 2 (by rfl) ⟨3804711, by rfl⟩ : syracuseStep 10145897 = 7609423) B7609423
theorem B6763931 : Blo 2223435 6763931 := bstep (se 1 (by rfl) ⟨5072948, by rfl⟩ : syracuseStep 6763931 = 10145897) B10145897
theorem B4509287 : Blo 2223435 4509287 := bstep (se 1 (by rfl) ⟨3381965, by rfl⟩ : syracuseStep 4509287 = 6763931) B6763931
theorem B3006191 : Blo 2223435 3006191 := bstep (se 1 (by rfl) ⟨2254643, by rfl⟩ : syracuseStep 3006191 = 4509287) B4509287
theorem B8016509 : Blo 2223435 8016509 := bstep (se 3 (by rfl) ⟨1503095, by rfl⟩ : syracuseStep 8016509 = 3006191) B3006191
theorem B21377357 : Blo 2223435 21377357 := bstep (se 3 (by rfl) ⟨4008254, by rfl⟩ : syracuseStep 21377357 = 8016509) B8016509
theorem B14251571 : Blo 2223435 14251571 := bstep (se 1 (by rfl) ⟨10688678, by rfl⟩ : syracuseStep 14251571 = 21377357) B21377357
theorem B9501047 : Blo 2223435 9501047 := bstep (se 1 (by rfl) ⟨7125785, by rfl⟩ : syracuseStep 9501047 = 14251571) B14251571
theorem B6334031 : Blo 2223435 6334031 := bstep (se 1 (by rfl) ⟨4750523, by rfl⟩ : syracuseStep 6334031 = 9501047) B9501047
theorem B4222687 : Blo 2223435 4222687 := bstep (se 1 (by rfl) ⟨3167015, by rfl⟩ : syracuseStep 4222687 = 6334031) B6334031
theorem B5630249 : Blo 2223435 5630249 := bstep (se 2 (by rfl) ⟨2111343, by rfl⟩ : syracuseStep 5630249 = 4222687) B4222687
theorem B3753499 : Blo 2223435 3753499 := bstep (se 1 (by rfl) ⟨2815124, by rfl⟩ : syracuseStep 3753499 = 5630249) B5630249
theorem B5004665 : Blo 2223435 5004665 := bstep (se 2 (by rfl) ⟨1876749, by rfl⟩ : syracuseStep 5004665 = 3753499) B3753499
theorem B3336443 : Blo 2223435 3336443 := bstep (se 1 (by rfl) ⟨2502332, by rfl⟩ : syracuseStep 3336443 = 5004665) B5004665
theorem B2224295 : Blo 2223435 2224295 := bstep (se 1 (by rfl) ⟨1668221, by rfl⟩ : syracuseStep 2224295 = 3336443) B3336443
theorem B2502337 : Blo 2223435 2502337 := bbase (se 2 (by rfl) ⟨938376, by rfl⟩ : syracuseStep 2502337 = 1876753) (by norm_num)
theorem B3336449 : Blo 2223435 3336449 := bstep (se 2 (by rfl) ⟨1251168, by rfl⟩ : syracuseStep 3336449 = 2502337) B2502337
theorem B2224299 : Blo 2223435 2224299 := bstep (se 1 (by rfl) ⟨1668224, by rfl⟩ : syracuseStep 2224299 = 3336449) B3336449
theorem B5630269 : Blo 2223435 5630269 := bbase (se 3 (by rfl) ⟨1055675, by rfl⟩ : syracuseStep 5630269 = 2111351) (by norm_num)
theorem B7507025 : Blo 2223435 7507025 := bstep (se 2 (by rfl) ⟨2815134, by rfl⟩ : syracuseStep 7507025 = 5630269) B5630269
theorem B5004683 : Blo 2223435 5004683 := bstep (se 1 (by rfl) ⟨3753512, by rfl⟩ : syracuseStep 5004683 = 7507025) B7507025
theorem B3336455 : Blo 2223435 3336455 := bstep (se 1 (by rfl) ⟨2502341, by rfl⟩ : syracuseStep 3336455 = 5004683) B5004683
theorem B2224303 : Blo 2223435 2224303 := bstep (se 1 (by rfl) ⟨1668227, by rfl⟩ : syracuseStep 2224303 = 3336455) B3336455
theorem B3336461 : Blo 2223435 3336461 := bbase (se 3 (by rfl) ⟨625586, by rfl⟩ : syracuseStep 3336461 = 1251173) (by norm_num)
theorem B2224307 : Blo 2223435 2224307 := bstep (se 1 (by rfl) ⟨1668230, by rfl⟩ : syracuseStep 2224307 = 3336461) B3336461
theorem B5004701 : Blo 2223435 5004701 := bbase (se 3 (by rfl) ⟨938381, by rfl⟩ : syracuseStep 5004701 = 1876763) (by norm_num)
theorem B3336467 : Blo 2223435 3336467 := bstep (se 1 (by rfl) ⟨2502350, by rfl⟩ : syracuseStep 3336467 = 5004701) B5004701
theorem B2224311 : Blo 2223435 2224311 := bstep (se 1 (by rfl) ⟨1668233, by rfl⟩ : syracuseStep 2224311 = 3336467) B3336467
theorem B3753533 : Blo 2223435 3753533 := bbase (se 3 (by rfl) ⟨703787, by rfl⟩ : syracuseStep 3753533 = 1407575) (by norm_num)
theorem B2502355 : Blo 2223435 2502355 := bstep (se 1 (by rfl) ⟨1876766, by rfl⟩ : syracuseStep 2502355 = 3753533) B3753533
theorem B3336473 : Blo 2223435 3336473 := bstep (se 2 (by rfl) ⟨1251177, by rfl⟩ : syracuseStep 3336473 = 2502355) B2502355
theorem B2224315 : Blo 2223435 2224315 := bstep (se 1 (by rfl) ⟨1668236, by rfl⟩ : syracuseStep 2224315 = 3336473) B3336473
theorem B5344397 : Blo 2223435 5344397 := bbase (se 3 (by rfl) ⟨1002074, by rfl⟩ : syracuseStep 5344397 = 2004149) (by norm_num)
theorem B3562931 : Blo 2223435 3562931 := bstep (se 1 (by rfl) ⟨2672198, by rfl⟩ : syracuseStep 3562931 = 5344397) B5344397
theorem B2375287 : Blo 2223435 2375287 := bstep (se 1 (by rfl) ⟨1781465, by rfl⟩ : syracuseStep 2375287 = 3562931) B3562931
theorem B12668197 : Blo 2223435 12668197 := bstep (se 4 (by rfl) ⟨1187643, by rfl⟩ : syracuseStep 12668197 = 2375287) B2375287
theorem B16890929 : Blo 2223435 16890929 := bstep (se 2 (by rfl) ⟨6334098, by rfl⟩ : syracuseStep 16890929 = 12668197) B12668197
theorem B11260619 : Blo 2223435 11260619 := bstep (se 1 (by rfl) ⟨8445464, by rfl⟩ : syracuseStep 11260619 = 16890929) B16890929
theorem B7507079 : Blo 2223435 7507079 := bstep (se 1 (by rfl) ⟨5630309, by rfl⟩ : syracuseStep 7507079 = 11260619) B11260619
theorem B5004719 : Blo 2223435 5004719 := bstep (se 1 (by rfl) ⟨3753539, by rfl⟩ : syracuseStep 5004719 = 7507079) B7507079
theorem B3336479 : Blo 2223435 3336479 := bstep (se 1 (by rfl) ⟨2502359, by rfl⟩ : syracuseStep 3336479 = 5004719) B5004719
theorem B2224319 : Blo 2223435 2224319 := bstep (se 1 (by rfl) ⟨1668239, by rfl⟩ : syracuseStep 2224319 = 3336479) B3336479
theorem B3336485 : Blo 2223435 3336485 := bbase (se 4 (by rfl) ⟨312795, by rfl⟩ : syracuseStep 3336485 = 625591) (by norm_num)
theorem B2224323 : Blo 2223435 2224323 := bstep (se 1 (by rfl) ⟨1668242, by rfl⟩ : syracuseStep 2224323 = 3336485) B3336485
theorem B2815165 : Blo 2223435 2815165 := bbase (se 3 (by rfl) ⟨527843, by rfl⟩ : syracuseStep 2815165 = 1055687) (by norm_num)
theorem B3753553 : Blo 2223435 3753553 := bstep (se 2 (by rfl) ⟨1407582, by rfl⟩ : syracuseStep 3753553 = 2815165) B2815165
theorem B5004737 : Blo 2223435 5004737 := bstep (se 2 (by rfl) ⟨1876776, by rfl⟩ : syracuseStep 5004737 = 3753553) B3753553
theorem B3336491 : Blo 2223435 3336491 := bstep (se 1 (by rfl) ⟨2502368, by rfl⟩ : syracuseStep 3336491 = 5004737) B5004737
theorem B2224327 : Blo 2223435 2224327 := bstep (se 1 (by rfl) ⟨1668245, by rfl⟩ : syracuseStep 2224327 = 3336491) B3336491
theorem B2502373 : Blo 2223435 2502373 := bbase (se 4 (by rfl) ⟨234597, by rfl⟩ : syracuseStep 2502373 = 469195) (by norm_num)
theorem B3336497 : Blo 2223435 3336497 := bstep (se 2 (by rfl) ⟨1251186, by rfl⟩ : syracuseStep 3336497 = 2502373) B2502373
theorem B2224331 : Blo 2223435 2224331 := bstep (se 1 (by rfl) ⟨1668248, by rfl⟩ : syracuseStep 2224331 = 3336497) B3336497
theorem B3562957 : Blo 2223435 3562957 := bbase (se 3 (by rfl) ⟨668054, by rfl⟩ : syracuseStep 3562957 = 1336109) (by norm_num)
theorem B4750609 : Blo 2223435 4750609 := bstep (se 2 (by rfl) ⟨1781478, by rfl⟩ : syracuseStep 4750609 = 3562957) B3562957
theorem B6334145 : Blo 2223435 6334145 := bstep (se 2 (by rfl) ⟨2375304, by rfl⟩ : syracuseStep 6334145 = 4750609) B4750609
theorem B4222763 : Blo 2223435 4222763 := bstep (se 1 (by rfl) ⟨3167072, by rfl⟩ : syracuseStep 4222763 = 6334145) B6334145
theorem B2815175 : Blo 2223435 2815175 := bstep (se 1 (by rfl) ⟨2111381, by rfl⟩ : syracuseStep 2815175 = 4222763) B4222763
theorem B7507133 : Blo 2223435 7507133 := bstep (se 3 (by rfl) ⟨1407587, by rfl⟩ : syracuseStep 7507133 = 2815175) B2815175
theorem B5004755 : Blo 2223435 5004755 := bstep (se 1 (by rfl) ⟨3753566, by rfl⟩ : syracuseStep 5004755 = 7507133) B7507133
theorem B3336503 : Blo 2223435 3336503 := bstep (se 1 (by rfl) ⟨2502377, by rfl⟩ : syracuseStep 3336503 = 5004755) B5004755
theorem B2224335 : Blo 2223435 2224335 := bstep (se 1 (by rfl) ⟨1668251, by rfl⟩ : syracuseStep 2224335 = 3336503) B3336503
theorem B3336509 : Blo 2223435 3336509 := bbase (se 3 (by rfl) ⟨625595, by rfl⟩ : syracuseStep 3336509 = 1251191) (by norm_num)
theorem B2224339 : Blo 2223435 2224339 := bstep (se 1 (by rfl) ⟨1668254, by rfl⟩ : syracuseStep 2224339 = 3336509) B3336509
theorem B5004773 : Blo 2223435 5004773 := bbase (se 4 (by rfl) ⟨469197, by rfl⟩ : syracuseStep 5004773 = 938395) (by norm_num)
theorem B3336515 : Blo 2223435 3336515 := bstep (se 1 (by rfl) ⟨2502386, by rfl⟩ : syracuseStep 3336515 = 5004773) B5004773
theorem B2224343 : Blo 2223435 2224343 := bstep (se 1 (by rfl) ⟨1668257, by rfl⟩ : syracuseStep 2224343 = 3336515) B3336515
theorem B5630381 : Blo 2223435 5630381 := bbase (se 3 (by rfl) ⟨1055696, by rfl⟩ : syracuseStep 5630381 = 2111393) (by norm_num)
theorem B3753587 : Blo 2223435 3753587 := bstep (se 1 (by rfl) ⟨2815190, by rfl⟩ : syracuseStep 3753587 = 5630381) B5630381
theorem B2502391 : Blo 2223435 2502391 := bstep (se 1 (by rfl) ⟨1876793, by rfl⟩ : syracuseStep 2502391 = 3753587) B3753587
theorem B3336521 : Blo 2223435 3336521 := bstep (se 2 (by rfl) ⟨1251195, by rfl⟩ : syracuseStep 3336521 = 2502391) B2502391
theorem B2224347 : Blo 2223435 2224347 := bstep (se 1 (by rfl) ⟨1668260, by rfl⟩ : syracuseStep 2224347 = 3336521) B3336521
theorem B2672237 : Blo 2223435 2672237 := bbase (se 3 (by rfl) ⟨501044, by rfl⟩ : syracuseStep 2672237 = 1002089) (by norm_num)
theorem B7125965 : Blo 2223435 7125965 := bstep (se 3 (by rfl) ⟨1336118, by rfl⟩ : syracuseStep 7125965 = 2672237) B2672237
theorem B4750643 : Blo 2223435 4750643 := bstep (se 1 (by rfl) ⟨3562982, by rfl⟩ : syracuseStep 4750643 = 7125965) B7125965
theorem B3167095 : Blo 2223435 3167095 := bstep (se 1 (by rfl) ⟨2375321, by rfl⟩ : syracuseStep 3167095 = 4750643) B4750643
theorem B4222793 : Blo 2223435 4222793 := bstep (se 2 (by rfl) ⟨1583547, by rfl⟩ : syracuseStep 4222793 = 3167095) B3167095
theorem B11260781 : Blo 2223435 11260781 := bstep (se 3 (by rfl) ⟨2111396, by rfl⟩ : syracuseStep 11260781 = 4222793) B4222793
theorem B7507187 : Blo 2223435 7507187 := bstep (se 1 (by rfl) ⟨5630390, by rfl⟩ : syracuseStep 7507187 = 11260781) B11260781
theorem B5004791 : Blo 2223435 5004791 := bstep (se 1 (by rfl) ⟨3753593, by rfl⟩ : syracuseStep 5004791 = 7507187) B7507187
theorem B3336527 : Blo 2223435 3336527 := bstep (se 1 (by rfl) ⟨2502395, by rfl⟩ : syracuseStep 3336527 = 5004791) B5004791
theorem B2224351 : Blo 2223435 2224351 := bstep (se 1 (by rfl) ⟨1668263, by rfl⟩ : syracuseStep 2224351 = 3336527) B3336527
theorem B3336533 : Blo 2223435 3336533 := bbase (se 10 (by rfl) ⟨4887, by rfl⟩ : syracuseStep 3336533 = 9775) (by norm_num)
theorem B2224355 : Blo 2223435 2224355 := bstep (se 1 (by rfl) ⟨1668266, by rfl⟩ : syracuseStep 2224355 = 3336533) B3336533
theorem B6334213 : Blo 2223435 6334213 := bbase (se 4 (by rfl) ⟨593832, by rfl⟩ : syracuseStep 6334213 = 1187665) (by norm_num)
theorem B8445617 : Blo 2223435 8445617 := bstep (se 2 (by rfl) ⟨3167106, by rfl⟩ : syracuseStep 8445617 = 6334213) B6334213
theorem B5630411 : Blo 2223435 5630411 := bstep (se 1 (by rfl) ⟨4222808, by rfl⟩ : syracuseStep 5630411 = 8445617) B8445617
theorem B3753607 : Blo 2223435 3753607 := bstep (se 1 (by rfl) ⟨2815205, by rfl⟩ : syracuseStep 3753607 = 5630411) B5630411
theorem B5004809 : Blo 2223435 5004809 := bstep (se 2 (by rfl) ⟨1876803, by rfl⟩ : syracuseStep 5004809 = 3753607) B3753607
theorem B3336539 : Blo 2223435 3336539 := bstep (se 1 (by rfl) ⟨2502404, by rfl⟩ : syracuseStep 3336539 = 5004809) B5004809
theorem B2224359 : Blo 2223435 2224359 := bstep (se 1 (by rfl) ⟨1668269, by rfl⟩ : syracuseStep 2224359 = 3336539) B3336539
theorem B2502409 : Blo 2223435 2502409 := bbase (se 2 (by rfl) ⟨938403, by rfl⟩ : syracuseStep 2502409 = 1876807) (by norm_num)
theorem B3336545 : Blo 2223435 3336545 := bstep (se 2 (by rfl) ⟨1251204, by rfl⟩ : syracuseStep 3336545 = 2502409) B2502409
theorem B2224363 : Blo 2223435 2224363 := bstep (se 1 (by rfl) ⟨1668272, by rfl⟩ : syracuseStep 2224363 = 3336545) B3336545
theorem B17832149 : Blo 2223435 17832149 := bbase (se 7 (by rfl) ⟨208970, by rfl⟩ : syracuseStep 17832149 = 417941) (by norm_num)
theorem B11888099 : Blo 2223435 11888099 := bstep (se 1 (by rfl) ⟨8916074, by rfl⟩ : syracuseStep 11888099 = 17832149) B17832149
theorem B7925399 : Blo 2223435 7925399 := bstep (se 1 (by rfl) ⟨5944049, by rfl⟩ : syracuseStep 7925399 = 11888099) B11888099
theorem B84537589 : Blo 2223435 84537589 := bstep (se 5 (by rfl) ⟨3962699, by rfl⟩ : syracuseStep 84537589 = 7925399) B7925399
theorem B112716785 : Blo 2223435 112716785 := bstep (se 2 (by rfl) ⟨42268794, by rfl⟩ : syracuseStep 112716785 = 84537589) B84537589
theorem B75144523 : Blo 2223435 75144523 := bstep (se 1 (by rfl) ⟨56358392, by rfl⟩ : syracuseStep 75144523 = 112716785) B112716785
theorem B100192697 : Blo 2223435 100192697 := bstep (se 2 (by rfl) ⟨37572261, by rfl⟩ : syracuseStep 100192697 = 75144523) B75144523
theorem B66795131 : Blo 2223435 66795131 := bstep (se 1 (by rfl) ⟨50096348, by rfl⟩ : syracuseStep 66795131 = 100192697) B100192697
theorem B178120349 : Blo 2223435 178120349 := bstep (se 3 (by rfl) ⟨33397565, by rfl⟩ : syracuseStep 178120349 = 66795131) B66795131
theorem B118746899 : Blo 2223435 118746899 := bstep (se 1 (by rfl) ⟨89060174, by rfl⟩ : syracuseStep 118746899 = 178120349) B178120349
theorem B79164599 : Blo 2223435 79164599 := bstep (se 1 (by rfl) ⟨59373449, by rfl⟩ : syracuseStep 79164599 = 118746899) B118746899
theorem B211105597 : Blo 2223435 211105597 := bstep (se 3 (by rfl) ⟨39582299, by rfl⟩ : syracuseStep 211105597 = 79164599) B79164599
theorem B281474129 : Blo 2223435 281474129 := bstep (se 2 (by rfl) ⟨105552798, by rfl⟩ : syracuseStep 281474129 = 211105597) B211105597
theorem B187649419 : Blo 2223435 187649419 := bstep (se 1 (by rfl) ⟨140737064, by rfl⟩ : syracuseStep 187649419 = 281474129) B281474129
theorem B250199225 : Blo 2223435 250199225 := bstep (se 2 (by rfl) ⟨93824709, by rfl⟩ : syracuseStep 250199225 = 187649419) B187649419
theorem B166799483 : Blo 2223435 166799483 := bstep (se 1 (by rfl) ⟨125099612, by rfl⟩ : syracuseStep 166799483 = 250199225) B250199225
theorem B111199655 : Blo 2223435 111199655 := bstep (se 1 (by rfl) ⟨83399741, by rfl⟩ : syracuseStep 111199655 = 166799483) B166799483
theorem B296532413 : Blo 2223435 296532413 := bstep (se 3 (by rfl) ⟨55599827, by rfl⟩ : syracuseStep 296532413 = 111199655) B111199655
theorem B197688275 : Blo 2223435 197688275 := bstep (se 1 (by rfl) ⟨148266206, by rfl⟩ : syracuseStep 197688275 = 296532413) B296532413
theorem B131792183 : Blo 2223435 131792183 := bstep (se 1 (by rfl) ⟨98844137, by rfl⟩ : syracuseStep 131792183 = 197688275) B197688275
theorem B87861455 : Blo 2223435 87861455 := bstep (se 1 (by rfl) ⟨65896091, by rfl⟩ : syracuseStep 87861455 = 131792183) B131792183
theorem B58574303 : Blo 2223435 58574303 := bstep (se 1 (by rfl) ⟨43930727, by rfl⟩ : syracuseStep 58574303 = 87861455) B87861455
theorem B39049535 : Blo 2223435 39049535 := bstep (se 1 (by rfl) ⟨29287151, by rfl⟩ : syracuseStep 39049535 = 58574303) B58574303
theorem B26033023 : Blo 2223435 26033023 := bstep (se 1 (by rfl) ⟨19524767, by rfl⟩ : syracuseStep 26033023 = 39049535) B39049535
theorem B34710697 : Blo 2223435 34710697 := bstep (se 2 (by rfl) ⟨13016511, by rfl⟩ : syracuseStep 34710697 = 26033023) B26033023
theorem B46280929 : Blo 2223435 46280929 := bstep (se 2 (by rfl) ⟨17355348, by rfl⟩ : syracuseStep 46280929 = 34710697) B34710697
theorem B61707905 : Blo 2223435 61707905 := bstep (se 2 (by rfl) ⟨23140464, by rfl⟩ : syracuseStep 61707905 = 46280929) B46280929
theorem B41138603 : Blo 2223435 41138603 := bstep (se 1 (by rfl) ⟨30853952, by rfl⟩ : syracuseStep 41138603 = 61707905) B61707905
theorem B27425735 : Blo 2223435 27425735 := bstep (se 1 (by rfl) ⟨20569301, by rfl⟩ : syracuseStep 27425735 = 41138603) B41138603
theorem B18283823 : Blo 2223435 18283823 := bstep (se 1 (by rfl) ⟨13712867, by rfl⟩ : syracuseStep 18283823 = 27425735) B27425735
theorem B12189215 : Blo 2223435 12189215 := bstep (se 1 (by rfl) ⟨9141911, by rfl⟩ : syracuseStep 12189215 = 18283823) B18283823
theorem B8126143 : Blo 2223435 8126143 := bstep (se 1 (by rfl) ⟨6094607, by rfl⟩ : syracuseStep 8126143 = 12189215) B12189215
theorem B43339429 : Blo 2223435 43339429 := bstep (se 4 (by rfl) ⟨4063071, by rfl⟩ : syracuseStep 43339429 = 8126143) B8126143
theorem B57785905 : Blo 2223435 57785905 := bstep (se 2 (by rfl) ⟨21669714, by rfl⟩ : syracuseStep 57785905 = 43339429) B43339429
theorem B308191493 : Blo 2223435 308191493 := bstep (se 4 (by rfl) ⟨28892952, by rfl⟩ : syracuseStep 308191493 = 57785905) B57785905
theorem B205460995 : Blo 2223435 205460995 := bstep (se 1 (by rfl) ⟨154095746, by rfl⟩ : syracuseStep 205460995 = 308191493) B308191493
theorem B273947993 : Blo 2223435 273947993 := bstep (se 2 (by rfl) ⟨102730497, by rfl⟩ : syracuseStep 273947993 = 205460995) B205460995
theorem B182631995 : Blo 2223435 182631995 := bstep (se 1 (by rfl) ⟨136973996, by rfl⟩ : syracuseStep 182631995 = 273947993) B273947993
theorem B121754663 : Blo 2223435 121754663 := bstep (se 1 (by rfl) ⟨91315997, by rfl⟩ : syracuseStep 121754663 = 182631995) B182631995
theorem B81169775 : Blo 2223435 81169775 := bstep (se 1 (by rfl) ⟨60877331, by rfl⟩ : syracuseStep 81169775 = 121754663) B121754663
theorem B54113183 : Blo 2223435 54113183 := bstep (se 1 (by rfl) ⟨40584887, by rfl⟩ : syracuseStep 54113183 = 81169775) B81169775
theorem B36075455 : Blo 2223435 36075455 := bstep (se 1 (by rfl) ⟨27056591, by rfl⟩ : syracuseStep 36075455 = 54113183) B54113183
theorem B24050303 : Blo 2223435 24050303 := bstep (se 1 (by rfl) ⟨18037727, by rfl⟩ : syracuseStep 24050303 = 36075455) B36075455
theorem B16033535 : Blo 2223435 16033535 := bstep (se 1 (by rfl) ⟨12025151, by rfl⟩ : syracuseStep 16033535 = 24050303) B24050303
theorem B10689023 : Blo 2223435 10689023 := bstep (se 1 (by rfl) ⟨8016767, by rfl⟩ : syracuseStep 10689023 = 16033535) B16033535
theorem B28504061 : Blo 2223435 28504061 := bstep (se 3 (by rfl) ⟨5344511, by rfl⟩ : syracuseStep 28504061 = 10689023) B10689023
theorem B19002707 : Blo 2223435 19002707 := bstep (se 1 (by rfl) ⟨14252030, by rfl⟩ : syracuseStep 19002707 = 28504061) B28504061
theorem B12668471 : Blo 2223435 12668471 := bstep (se 1 (by rfl) ⟨9501353, by rfl⟩ : syracuseStep 12668471 = 19002707) B19002707
theorem B8445647 : Blo 2223435 8445647 := bstep (se 1 (by rfl) ⟨6334235, by rfl⟩ : syracuseStep 8445647 = 12668471) B12668471
theorem B5630431 : Blo 2223435 5630431 := bstep (se 1 (by rfl) ⟨4222823, by rfl⟩ : syracuseStep 5630431 = 8445647) B8445647
theorem B7507241 : Blo 2223435 7507241 := bstep (se 2 (by rfl) ⟨2815215, by rfl⟩ : syracuseStep 7507241 = 5630431) B5630431
theorem B5004827 : Blo 2223435 5004827 := bstep (se 1 (by rfl) ⟨3753620, by rfl⟩ : syracuseStep 5004827 = 7507241) B7507241
theorem B3336551 : Blo 2223435 3336551 := bstep (se 1 (by rfl) ⟨2502413, by rfl⟩ : syracuseStep 3336551 = 5004827) B5004827
theorem B2224367 : Blo 2223435 2224367 := bstep (se 1 (by rfl) ⟨1668275, by rfl⟩ : syracuseStep 2224367 = 3336551) B3336551
theorem B3336557 : Blo 2223435 3336557 := bbase (se 3 (by rfl) ⟨625604, by rfl⟩ : syracuseStep 3336557 = 1251209) (by norm_num)
theorem B2224371 : Blo 2223435 2224371 := bstep (se 1 (by rfl) ⟨1668278, by rfl⟩ : syracuseStep 2224371 = 3336557) B3336557
theorem B5004845 : Blo 2223435 5004845 := bbase (se 3 (by rfl) ⟨938408, by rfl⟩ : syracuseStep 5004845 = 1876817) (by norm_num)
theorem B3336563 : Blo 2223435 3336563 := bstep (se 1 (by rfl) ⟨2502422, by rfl⟩ : syracuseStep 3336563 = 5004845) B5004845
theorem B2224375 : Blo 2223435 2224375 := bstep (se 1 (by rfl) ⟨1668281, by rfl⟩ : syracuseStep 2224375 = 3336563) B3336563
theorem B3382093 : Blo 2223435 3382093 := bbase (se 3 (by rfl) ⟨634142, by rfl⟩ : syracuseStep 3382093 = 1268285) (by norm_num)
theorem B18037829 : Blo 2223435 18037829 := bstep (se 4 (by rfl) ⟨1691046, by rfl⟩ : syracuseStep 18037829 = 3382093) B3382093
theorem B48100877 : Blo 2223435 48100877 := bstep (se 3 (by rfl) ⟨9018914, by rfl⟩ : syracuseStep 48100877 = 18037829) B18037829
theorem B32067251 : Blo 2223435 32067251 := bstep (se 1 (by rfl) ⟨24050438, by rfl⟩ : syracuseStep 32067251 = 48100877) B48100877
theorem B21378167 : Blo 2223435 21378167 := bstep (se 1 (by rfl) ⟨16033625, by rfl⟩ : syracuseStep 21378167 = 32067251) B32067251
theorem B14252111 : Blo 2223435 14252111 := bstep (se 1 (by rfl) ⟨10689083, by rfl⟩ : syracuseStep 14252111 = 21378167) B21378167
theorem B9501407 : Blo 2223435 9501407 := bstep (se 1 (by rfl) ⟨7126055, by rfl⟩ : syracuseStep 9501407 = 14252111) B14252111
theorem B6334271 : Blo 2223435 6334271 := bstep (se 1 (by rfl) ⟨4750703, by rfl⟩ : syracuseStep 6334271 = 9501407) B9501407
theorem B4222847 : Blo 2223435 4222847 := bstep (se 1 (by rfl) ⟨3167135, by rfl⟩ : syracuseStep 4222847 = 6334271) B6334271
theorem B2815231 : Blo 2223435 2815231 := bstep (se 1 (by rfl) ⟨2111423, by rfl⟩ : syracuseStep 2815231 = 4222847) B4222847
theorem B3753641 : Blo 2223435 3753641 := bstep (se 2 (by rfl) ⟨1407615, by rfl⟩ : syracuseStep 3753641 = 2815231) B2815231
theorem B2502427 : Blo 2223435 2502427 := bstep (se 1 (by rfl) ⟨1876820, by rfl⟩ : syracuseStep 2502427 = 3753641) B3753641
theorem B3336569 : Blo 2223435 3336569 := bstep (se 2 (by rfl) ⟨1251213, by rfl⟩ : syracuseStep 3336569 = 2502427) B2502427
theorem B2224379 : Blo 2223435 2224379 := bstep (se 1 (by rfl) ⟨1668284, by rfl⟩ : syracuseStep 2224379 = 3336569) B3336569
theorem B4008413 : Blo 2223435 4008413 := bbase (se 3 (by rfl) ⟨751577, by rfl⟩ : syracuseStep 4008413 = 1503155) (by norm_num)
theorem B2672275 : Blo 2223435 2672275 := bstep (se 1 (by rfl) ⟨2004206, by rfl⟩ : syracuseStep 2672275 = 4008413) B4008413
theorem B3563033 : Blo 2223435 3563033 := bstep (se 2 (by rfl) ⟨1336137, by rfl⟩ : syracuseStep 3563033 = 2672275) B2672275
theorem B38005685 : Blo 2223435 38005685 := bstep (se 5 (by rfl) ⟨1781516, by rfl⟩ : syracuseStep 38005685 = 3563033) B3563033
theorem B25337123 : Blo 2223435 25337123 := bstep (se 1 (by rfl) ⟨19002842, by rfl⟩ : syracuseStep 25337123 = 38005685) B38005685
theorem B16891415 : Blo 2223435 16891415 := bstep (se 1 (by rfl) ⟨12668561, by rfl⟩ : syracuseStep 16891415 = 25337123) B25337123
theorem B11260943 : Blo 2223435 11260943 := bstep (se 1 (by rfl) ⟨8445707, by rfl⟩ : syracuseStep 11260943 = 16891415) B16891415
theorem B7507295 : Blo 2223435 7507295 := bstep (se 1 (by rfl) ⟨5630471, by rfl⟩ : syracuseStep 7507295 = 11260943) B11260943
theorem B5004863 : Blo 2223435 5004863 := bstep (se 1 (by rfl) ⟨3753647, by rfl⟩ : syracuseStep 5004863 = 7507295) B7507295
theorem B3336575 : Blo 2223435 3336575 := bstep (se 1 (by rfl) ⟨2502431, by rfl⟩ : syracuseStep 3336575 = 5004863) B5004863
theorem B2224383 : Blo 2223435 2224383 := bstep (se 1 (by rfl) ⟨1668287, by rfl⟩ : syracuseStep 2224383 = 3336575) B3336575
theorem B3336581 : Blo 2223435 3336581 := bbase (se 4 (by rfl) ⟨312804, by rfl⟩ : syracuseStep 3336581 = 625609) (by norm_num)
theorem B2224387 : Blo 2223435 2224387 := bstep (se 1 (by rfl) ⟨1668290, by rfl⟩ : syracuseStep 2224387 = 3336581) B3336581
theorem B3753661 : Blo 2223435 3753661 := bbase (se 3 (by rfl) ⟨703811, by rfl⟩ : syracuseStep 3753661 = 1407623) (by norm_num)
theorem B5004881 : Blo 2223435 5004881 := bstep (se 2 (by rfl) ⟨1876830, by rfl⟩ : syracuseStep 5004881 = 3753661) B3753661
theorem B3336587 : Blo 2223435 3336587 := bstep (se 1 (by rfl) ⟨2502440, by rfl⟩ : syracuseStep 3336587 = 5004881) B5004881
theorem B2224391 : Blo 2223435 2224391 := bstep (se 1 (by rfl) ⟨1668293, by rfl⟩ : syracuseStep 2224391 = 3336587) B3336587
theorem B2502445 : Blo 2223435 2502445 := bbase (se 3 (by rfl) ⟨469208, by rfl⟩ : syracuseStep 2502445 = 938417) (by norm_num)
theorem B3336593 : Blo 2223435 3336593 := bstep (se 2 (by rfl) ⟨1251222, by rfl⟩ : syracuseStep 3336593 = 2502445) B2502445
theorem B2224395 : Blo 2223435 2224395 := bstep (se 1 (by rfl) ⟨1668296, by rfl⟩ : syracuseStep 2224395 = 3336593) B3336593
theorem B7507349 : Blo 2223435 7507349 := bbase (se 6 (by rfl) ⟨175953, by rfl⟩ : syracuseStep 7507349 = 351907) (by norm_num)
theorem B5004899 : Blo 2223435 5004899 := bstep (se 1 (by rfl) ⟨3753674, by rfl⟩ : syracuseStep 5004899 = 7507349) B7507349
theorem B3336599 : Blo 2223435 3336599 := bstep (se 1 (by rfl) ⟨2502449, by rfl⟩ : syracuseStep 3336599 = 5004899) B5004899
theorem B2224399 : Blo 2223435 2224399 := bstep (se 1 (by rfl) ⟨1668299, by rfl⟩ : syracuseStep 2224399 = 3336599) B3336599
theorem B3336605 : Blo 2223435 3336605 := bbase (se 3 (by rfl) ⟨625613, by rfl⟩ : syracuseStep 3336605 = 1251227) (by norm_num)
theorem B2224403 : Blo 2223435 2224403 := bstep (se 1 (by rfl) ⟨1668302, by rfl⟩ : syracuseStep 2224403 = 3336605) B3336605
theorem B5004917 : Blo 2223435 5004917 := bbase (se 5 (by rfl) ⟨234605, by rfl⟩ : syracuseStep 5004917 = 469211) (by norm_num)
theorem B3336611 : Blo 2223435 3336611 := bstep (se 1 (by rfl) ⟨2502458, by rfl⟩ : syracuseStep 3336611 = 5004917) B5004917
theorem B2224407 : Blo 2223435 2224407 := bstep (se 1 (by rfl) ⟨1668305, by rfl⟩ : syracuseStep 2224407 = 3336611) B3336611
theorem B2672309 : Blo 2223435 2672309 := bbase (se 5 (by rfl) ⟨125264, by rfl⟩ : syracuseStep 2672309 = 250529) (by norm_num)
theorem B7126157 : Blo 2223435 7126157 := bstep (se 3 (by rfl) ⟨1336154, by rfl⟩ : syracuseStep 7126157 = 2672309) B2672309
theorem B19003085 : Blo 2223435 19003085 := bstep (se 3 (by rfl) ⟨3563078, by rfl⟩ : syracuseStep 19003085 = 7126157) B7126157
theorem B12668723 : Blo 2223435 12668723 := bstep (se 1 (by rfl) ⟨9501542, by rfl⟩ : syracuseStep 12668723 = 19003085) B19003085
theorem B8445815 : Blo 2223435 8445815 := bstep (se 1 (by rfl) ⟨6334361, by rfl⟩ : syracuseStep 8445815 = 12668723) B12668723
theorem B5630543 : Blo 2223435 5630543 := bstep (se 1 (by rfl) ⟨4222907, by rfl⟩ : syracuseStep 5630543 = 8445815) B8445815
theorem B3753695 : Blo 2223435 3753695 := bstep (se 1 (by rfl) ⟨2815271, by rfl⟩ : syracuseStep 3753695 = 5630543) B5630543
theorem B2502463 : Blo 2223435 2502463 := bstep (se 1 (by rfl) ⟨1876847, by rfl⟩ : syracuseStep 2502463 = 3753695) B3753695
theorem B3336617 : Blo 2223435 3336617 := bstep (se 2 (by rfl) ⟨1251231, by rfl⟩ : syracuseStep 3336617 = 2502463) B2502463
theorem B2224411 : Blo 2223435 2224411 := bstep (se 1 (by rfl) ⟨1668308, by rfl⟩ : syracuseStep 2224411 = 3336617) B3336617
theorem B8445829 : Blo 2223435 8445829 := bbase (se 4 (by rfl) ⟨791796, by rfl⟩ : syracuseStep 8445829 = 1583593) (by norm_num)
theorem B11261105 : Blo 2223435 11261105 := bstep (se 2 (by rfl) ⟨4222914, by rfl⟩ : syracuseStep 11261105 = 8445829) B8445829
theorem B7507403 : Blo 2223435 7507403 := bstep (se 1 (by rfl) ⟨5630552, by rfl⟩ : syracuseStep 7507403 = 11261105) B11261105
theorem B5004935 : Blo 2223435 5004935 := bstep (se 1 (by rfl) ⟨3753701, by rfl⟩ : syracuseStep 5004935 = 7507403) B7507403
theorem B3336623 : Blo 2223435 3336623 := bstep (se 1 (by rfl) ⟨2502467, by rfl⟩ : syracuseStep 3336623 = 5004935) B5004935
theorem B2224415 : Blo 2223435 2224415 := bstep (se 1 (by rfl) ⟨1668311, by rfl⟩ : syracuseStep 2224415 = 3336623) B3336623
theorem B3336629 : Blo 2223435 3336629 := bbase (se 5 (by rfl) ⟨156404, by rfl⟩ : syracuseStep 3336629 = 312809) (by norm_num)
theorem B2224419 : Blo 2223435 2224419 := bstep (se 1 (by rfl) ⟨1668314, by rfl⟩ : syracuseStep 2224419 = 3336629) B3336629
theorem B5630573 : Blo 2223435 5630573 := bbase (se 3 (by rfl) ⟨1055732, by rfl⟩ : syracuseStep 5630573 = 2111465) (by norm_num)
theorem B3753715 : Blo 2223435 3753715 := bstep (se 1 (by rfl) ⟨2815286, by rfl⟩ : syracuseStep 3753715 = 5630573) B5630573
theorem B5004953 : Blo 2223435 5004953 := bstep (se 2 (by rfl) ⟨1876857, by rfl⟩ : syracuseStep 5004953 = 3753715) B3753715
theorem B3336635 : Blo 2223435 3336635 := bstep (se 1 (by rfl) ⟨2502476, by rfl⟩ : syracuseStep 3336635 = 5004953) B5004953
theorem B2224423 : Blo 2223435 2224423 := bstep (se 1 (by rfl) ⟨1668317, by rfl⟩ : syracuseStep 2224423 = 3336635) B3336635
theorem B2502481 : Blo 2223435 2502481 := bbase (se 2 (by rfl) ⟨938430, by rfl⟩ : syracuseStep 2502481 = 1876861) (by norm_num)
theorem B3336641 : Blo 2223435 3336641 := bstep (se 2 (by rfl) ⟨1251240, by rfl⟩ : syracuseStep 3336641 = 2502481) B2502481
theorem B2224427 : Blo 2223435 2224427 := bstep (se 1 (by rfl) ⟨1668320, by rfl⟩ : syracuseStep 2224427 = 3336641) B3336641
theorem B2407817 : Blo 2223435 2407817 := bbase (se 2 (by rfl) ⟨902931, by rfl⟩ : syracuseStep 2407817 = 1805863) (by norm_num)
theorem B6420845 : Blo 2223435 6420845 := bstep (se 3 (by rfl) ⟨1203908, by rfl⟩ : syracuseStep 6420845 = 2407817) B2407817
theorem B4280563 : Blo 2223435 4280563 := bstep (se 1 (by rfl) ⟨3210422, by rfl⟩ : syracuseStep 4280563 = 6420845) B6420845
theorem B5707417 : Blo 2223435 5707417 := bstep (se 2 (by rfl) ⟨2140281, by rfl⟩ : syracuseStep 5707417 = 4280563) B4280563
theorem B7609889 : Blo 2223435 7609889 := bstep (se 2 (by rfl) ⟨2853708, by rfl⟩ : syracuseStep 7609889 = 5707417) B5707417
theorem B20293037 : Blo 2223435 20293037 := bstep (se 3 (by rfl) ⟨3804944, by rfl⟩ : syracuseStep 20293037 = 7609889) B7609889
theorem B13528691 : Blo 2223435 13528691 := bstep (se 1 (by rfl) ⟨10146518, by rfl⟩ : syracuseStep 13528691 = 20293037) B20293037
theorem B9019127 : Blo 2223435 9019127 := bstep (se 1 (by rfl) ⟨6764345, by rfl⟩ : syracuseStep 9019127 = 13528691) B13528691
theorem B6012751 : Blo 2223435 6012751 := bstep (se 1 (by rfl) ⟨4509563, by rfl⟩ : syracuseStep 6012751 = 9019127) B9019127
theorem B8017001 : Blo 2223435 8017001 := bstep (se 2 (by rfl) ⟨3006375, by rfl⟩ : syracuseStep 8017001 = 6012751) B6012751
theorem B5344667 : Blo 2223435 5344667 := bstep (se 1 (by rfl) ⟨4008500, by rfl⟩ : syracuseStep 5344667 = 8017001) B8017001
theorem B3563111 : Blo 2223435 3563111 := bstep (se 1 (by rfl) ⟨2672333, by rfl⟩ : syracuseStep 3563111 = 5344667) B5344667
theorem B2375407 : Blo 2223435 2375407 := bstep (se 1 (by rfl) ⟨1781555, by rfl⟩ : syracuseStep 2375407 = 3563111) B3563111
theorem B3167209 : Blo 2223435 3167209 := bstep (se 2 (by rfl) ⟨1187703, by rfl⟩ : syracuseStep 3167209 = 2375407) B2375407
theorem B4222945 : Blo 2223435 4222945 := bstep (se 2 (by rfl) ⟨1583604, by rfl⟩ : syracuseStep 4222945 = 3167209) B3167209
theorem B5630593 : Blo 2223435 5630593 := bstep (se 2 (by rfl) ⟨2111472, by rfl⟩ : syracuseStep 5630593 = 4222945) B4222945
theorem B7507457 : Blo 2223435 7507457 := bstep (se 2 (by rfl) ⟨2815296, by rfl⟩ : syracuseStep 7507457 = 5630593) B5630593
theorem B5004971 : Blo 2223435 5004971 := bstep (se 1 (by rfl) ⟨3753728, by rfl⟩ : syracuseStep 5004971 = 7507457) B7507457
theorem B3336647 : Blo 2223435 3336647 := bstep (se 1 (by rfl) ⟨2502485, by rfl⟩ : syracuseStep 3336647 = 5004971) B5004971
theorem B2224431 : Blo 2223435 2224431 := bstep (se 1 (by rfl) ⟨1668323, by rfl⟩ : syracuseStep 2224431 = 3336647) B3336647
theorem B3336653 : Blo 2223435 3336653 := bbase (se 3 (by rfl) ⟨625622, by rfl⟩ : syracuseStep 3336653 = 1251245) (by norm_num)
theorem B2224435 : Blo 2223435 2224435 := bstep (se 1 (by rfl) ⟨1668326, by rfl⟩ : syracuseStep 2224435 = 3336653) B3336653
theorem B5004989 : Blo 2223435 5004989 := bbase (se 3 (by rfl) ⟨938435, by rfl⟩ : syracuseStep 5004989 = 1876871) (by norm_num)
theorem B3336659 : Blo 2223435 3336659 := bstep (se 1 (by rfl) ⟨2502494, by rfl⟩ : syracuseStep 3336659 = 5004989) B5004989
theorem B2224439 : Blo 2223435 2224439 := bstep (se 1 (by rfl) ⟨1668329, by rfl⟩ : syracuseStep 2224439 = 3336659) B3336659
theorem B3753749 : Blo 2223435 3753749 := bbase (se 6 (by rfl) ⟨87978, by rfl⟩ : syracuseStep 3753749 = 175957) (by norm_num)
theorem B2502499 : Blo 2223435 2502499 := bstep (se 1 (by rfl) ⟨1876874, by rfl⟩ : syracuseStep 2502499 = 3753749) B3753749
theorem B3336665 : Blo 2223435 3336665 := bstep (se 2 (by rfl) ⟨1251249, by rfl⟩ : syracuseStep 3336665 = 2502499) B2502499
theorem B2224443 : Blo 2223435 2224443 := bstep (se 1 (by rfl) ⟨1668332, by rfl⟩ : syracuseStep 2224443 = 3336665) B3336665
theorem B12189653 : Blo 2223435 12189653 := bbase (se 7 (by rfl) ⟨142847, by rfl⟩ : syracuseStep 12189653 = 285695) (by norm_num)
theorem B8126435 : Blo 2223435 8126435 := bstep (se 1 (by rfl) ⟨6094826, by rfl⟩ : syracuseStep 8126435 = 12189653) B12189653
theorem B21670493 : Blo 2223435 21670493 := bstep (se 3 (by rfl) ⟨4063217, by rfl⟩ : syracuseStep 21670493 = 8126435) B8126435
theorem B57787981 : Blo 2223435 57787981 := bstep (se 3 (by rfl) ⟨10835246, by rfl⟩ : syracuseStep 57787981 = 21670493) B21670493
theorem B308202565 : Blo 2223435 308202565 := bstep (se 4 (by rfl) ⟨28893990, by rfl⟩ : syracuseStep 308202565 = 57787981) B57787981
theorem B410936753 : Blo 2223435 410936753 := bstep (se 2 (by rfl) ⟨154101282, by rfl⟩ : syracuseStep 410936753 = 308202565) B308202565
theorem B273957835 : Blo 2223435 273957835 := bstep (se 1 (by rfl) ⟨205468376, by rfl⟩ : syracuseStep 273957835 = 410936753) B410936753
theorem B365277113 : Blo 2223435 365277113 := bstep (se 2 (by rfl) ⟨136978917, by rfl⟩ : syracuseStep 365277113 = 273957835) B273957835
theorem B243518075 : Blo 2223435 243518075 := bstep (se 1 (by rfl) ⟨182638556, by rfl⟩ : syracuseStep 243518075 = 365277113) B365277113
theorem B162345383 : Blo 2223435 162345383 := bstep (se 1 (by rfl) ⟨121759037, by rfl⟩ : syracuseStep 162345383 = 243518075) B243518075
theorem B108230255 : Blo 2223435 108230255 := bstep (se 1 (by rfl) ⟨81172691, by rfl⟩ : syracuseStep 108230255 = 162345383) B162345383
theorem B72153503 : Blo 2223435 72153503 := bstep (se 1 (by rfl) ⟨54115127, by rfl⟩ : syracuseStep 72153503 = 108230255) B108230255
theorem B48102335 : Blo 2223435 48102335 := bstep (se 1 (by rfl) ⟨36076751, by rfl⟩ : syracuseStep 48102335 = 72153503) B72153503
theorem B32068223 : Blo 2223435 32068223 := bstep (se 1 (by rfl) ⟨24051167, by rfl⟩ : syracuseStep 32068223 = 48102335) B48102335
theorem B21378815 : Blo 2223435 21378815 := bstep (se 1 (by rfl) ⟨16034111, by rfl⟩ : syracuseStep 21378815 = 32068223) B32068223
theorem B14252543 : Blo 2223435 14252543 := bstep (se 1 (by rfl) ⟨10689407, by rfl⟩ : syracuseStep 14252543 = 21378815) B21378815
theorem B9501695 : Blo 2223435 9501695 := bstep (se 1 (by rfl) ⟨7126271, by rfl⟩ : syracuseStep 9501695 = 14252543) B14252543
theorem B6334463 : Blo 2223435 6334463 := bstep (se 1 (by rfl) ⟨4750847, by rfl⟩ : syracuseStep 6334463 = 9501695) B9501695
theorem B16891901 : Blo 2223435 16891901 := bstep (se 3 (by rfl) ⟨3167231, by rfl⟩ : syracuseStep 16891901 = 6334463) B6334463
theorem B11261267 : Blo 2223435 11261267 := bstep (se 1 (by rfl) ⟨8445950, by rfl⟩ : syracuseStep 11261267 = 16891901) B16891901
theorem B7507511 : Blo 2223435 7507511 := bstep (se 1 (by rfl) ⟨5630633, by rfl⟩ : syracuseStep 7507511 = 11261267) B11261267
theorem B5005007 : Blo 2223435 5005007 := bstep (se 1 (by rfl) ⟨3753755, by rfl⟩ : syracuseStep 5005007 = 7507511) B7507511
theorem B3336671 : Blo 2223435 3336671 := bstep (se 1 (by rfl) ⟨2502503, by rfl⟩ : syracuseStep 3336671 = 5005007) B5005007
theorem B2224447 : Blo 2223435 2224447 := bstep (se 1 (by rfl) ⟨1668335, by rfl⟩ : syracuseStep 2224447 = 3336671) B3336671
theorem B3336677 : Blo 2223435 3336677 := bbase (se 4 (by rfl) ⟨312813, by rfl⟩ : syracuseStep 3336677 = 625627) (by norm_num)
theorem B2224451 : Blo 2223435 2224451 := bstep (se 1 (by rfl) ⟨1668338, by rfl⟩ : syracuseStep 2224451 = 3336677) B3336677
theorem B14252597 : Blo 2223435 14252597 := bbase (se 5 (by rfl) ⟨668090, by rfl⟩ : syracuseStep 14252597 = 1336181) (by norm_num)
theorem B9501731 : Blo 2223435 9501731 := bstep (se 1 (by rfl) ⟨7126298, by rfl⟩ : syracuseStep 9501731 = 14252597) B14252597
theorem B6334487 : Blo 2223435 6334487 := bstep (se 1 (by rfl) ⟨4750865, by rfl⟩ : syracuseStep 6334487 = 9501731) B9501731
theorem B4222991 : Blo 2223435 4222991 := bstep (se 1 (by rfl) ⟨3167243, by rfl⟩ : syracuseStep 4222991 = 6334487) B6334487
theorem B2815327 : Blo 2223435 2815327 := bstep (se 1 (by rfl) ⟨2111495, by rfl⟩ : syracuseStep 2815327 = 4222991) B4222991
theorem B3753769 : Blo 2223435 3753769 := bstep (se 2 (by rfl) ⟨1407663, by rfl⟩ : syracuseStep 3753769 = 2815327) B2815327
theorem B5005025 : Blo 2223435 5005025 := bstep (se 2 (by rfl) ⟨1876884, by rfl⟩ : syracuseStep 5005025 = 3753769) B3753769
theorem B3336683 : Blo 2223435 3336683 := bstep (se 1 (by rfl) ⟨2502512, by rfl⟩ : syracuseStep 3336683 = 5005025) B5005025
theorem B2224455 : Blo 2223435 2224455 := bstep (se 1 (by rfl) ⟨1668341, by rfl⟩ : syracuseStep 2224455 = 3336683) B3336683
theorem B2502517 : Blo 2223435 2502517 := bbase (se 5 (by rfl) ⟨117305, by rfl⟩ : syracuseStep 2502517 = 234611) (by norm_num)
theorem B3336689 : Blo 2223435 3336689 := bstep (se 2 (by rfl) ⟨1251258, by rfl⟩ : syracuseStep 3336689 = 2502517) B2502517
theorem B2224459 : Blo 2223435 2224459 := bstep (se 1 (by rfl) ⟨1668344, by rfl⟩ : syracuseStep 2224459 = 3336689) B3336689
theorem B2815337 : Blo 2223435 2815337 := bbase (se 2 (by rfl) ⟨1055751, by rfl⟩ : syracuseStep 2815337 = 2111503) (by norm_num)
theorem B7507565 : Blo 2223435 7507565 := bstep (se 3 (by rfl) ⟨1407668, by rfl⟩ : syracuseStep 7507565 = 2815337) B2815337
theorem B5005043 : Blo 2223435 5005043 := bstep (se 1 (by rfl) ⟨3753782, by rfl⟩ : syracuseStep 5005043 = 7507565) B7507565
theorem B3336695 : Blo 2223435 3336695 := bstep (se 1 (by rfl) ⟨2502521, by rfl⟩ : syracuseStep 3336695 = 5005043) B5005043
theorem B2224463 : Blo 2223435 2224463 := bstep (se 1 (by rfl) ⟨1668347, by rfl⟩ : syracuseStep 2224463 = 3336695) B3336695
theorem B3336701 : Blo 2223435 3336701 := bbase (se 3 (by rfl) ⟨625631, by rfl⟩ : syracuseStep 3336701 = 1251263) (by norm_num)
theorem B2224467 : Blo 2223435 2224467 := bstep (se 1 (by rfl) ⟨1668350, by rfl⟩ : syracuseStep 2224467 = 3336701) B3336701
theorem B5005061 : Blo 2223435 5005061 := bbase (se 4 (by rfl) ⟨469224, by rfl⟩ : syracuseStep 5005061 = 938449) (by norm_num)
theorem B3336707 : Blo 2223435 3336707 := bstep (se 1 (by rfl) ⟨2502530, by rfl⟩ : syracuseStep 3336707 = 5005061) B5005061
theorem B2224471 : Blo 2223435 2224471 := bstep (se 1 (by rfl) ⟨1668353, by rfl⟩ : syracuseStep 2224471 = 3336707) B3336707
theorem B4223029 : Blo 2223435 4223029 := bbase (se 5 (by rfl) ⟨197954, by rfl⟩ : syracuseStep 4223029 = 395909) (by norm_num)
theorem B5630705 : Blo 2223435 5630705 := bstep (se 2 (by rfl) ⟨2111514, by rfl⟩ : syracuseStep 5630705 = 4223029) B4223029
theorem B3753803 : Blo 2223435 3753803 := bstep (se 1 (by rfl) ⟨2815352, by rfl⟩ : syracuseStep 3753803 = 5630705) B5630705
theorem B2502535 : Blo 2223435 2502535 := bstep (se 1 (by rfl) ⟨1876901, by rfl⟩ : syracuseStep 2502535 = 3753803) B3753803
theorem B3336713 : Blo 2223435 3336713 := bstep (se 2 (by rfl) ⟨1251267, by rfl⟩ : syracuseStep 3336713 = 2502535) B2502535
theorem B2224475 : Blo 2223435 2224475 := bstep (se 1 (by rfl) ⟨1668356, by rfl⟩ : syracuseStep 2224475 = 3336713) B3336713
theorem B11261429 : Blo 2223435 11261429 := bbase (se 5 (by rfl) ⟨527879, by rfl⟩ : syracuseStep 11261429 = 1055759) (by norm_num)
theorem B7507619 : Blo 2223435 7507619 := bstep (se 1 (by rfl) ⟨5630714, by rfl⟩ : syracuseStep 7507619 = 11261429) B11261429
theorem B5005079 : Blo 2223435 5005079 := bstep (se 1 (by rfl) ⟨3753809, by rfl⟩ : syracuseStep 5005079 = 7507619) B7507619
theorem B3336719 : Blo 2223435 3336719 := bstep (se 1 (by rfl) ⟨2502539, by rfl⟩ : syracuseStep 3336719 = 5005079) B5005079
theorem B2224479 : Blo 2223435 2224479 := bstep (se 1 (by rfl) ⟨1668359, by rfl⟩ : syracuseStep 2224479 = 3336719) B3336719
theorem B3336725 : Blo 2223435 3336725 := bbase (se 6 (by rfl) ⟨78204, by rfl⟩ : syracuseStep 3336725 = 156409) (by norm_num)
theorem B2224483 : Blo 2223435 2224483 := bstep (se 1 (by rfl) ⟨1668362, by rfl⟩ : syracuseStep 2224483 = 3336725) B3336725
theorem B19003733 : Blo 2223435 19003733 := bbase (se 10 (by rfl) ⟨27837, by rfl⟩ : syracuseStep 19003733 = 55675) (by norm_num)
theorem B12669155 : Blo 2223435 12669155 := bstep (se 1 (by rfl) ⟨9501866, by rfl⟩ : syracuseStep 12669155 = 19003733) B19003733
theorem B8446103 : Blo 2223435 8446103 := bstep (se 1 (by rfl) ⟨6334577, by rfl⟩ : syracuseStep 8446103 = 12669155) B12669155
theorem B5630735 : Blo 2223435 5630735 := bstep (se 1 (by rfl) ⟨4223051, by rfl⟩ : syracuseStep 5630735 = 8446103) B8446103
theorem B3753823 : Blo 2223435 3753823 := bstep (se 1 (by rfl) ⟨2815367, by rfl⟩ : syracuseStep 3753823 = 5630735) B5630735
theorem B5005097 : Blo 2223435 5005097 := bstep (se 2 (by rfl) ⟨1876911, by rfl⟩ : syracuseStep 5005097 = 3753823) B3753823
theorem B3336731 : Blo 2223435 3336731 := bstep (se 1 (by rfl) ⟨2502548, by rfl⟩ : syracuseStep 3336731 = 5005097) B5005097
theorem B2224487 : Blo 2223435 2224487 := bstep (se 1 (by rfl) ⟨1668365, by rfl⟩ : syracuseStep 2224487 = 3336731) B3336731
theorem B2502553 : Blo 2223435 2502553 := bbase (se 2 (by rfl) ⟨938457, by rfl⟩ : syracuseStep 2502553 = 1876915) (by norm_num)
theorem B3336737 : Blo 2223435 3336737 := bstep (se 2 (by rfl) ⟨1251276, by rfl⟩ : syracuseStep 3336737 = 2502553) B2502553
theorem B2224491 : Blo 2223435 2224491 := bstep (se 1 (by rfl) ⟨1668368, by rfl⟩ : syracuseStep 2224491 = 3336737) B3336737
theorem B8446133 : Blo 2223435 8446133 := bbase (se 5 (by rfl) ⟨395912, by rfl⟩ : syracuseStep 8446133 = 791825) (by norm_num)
theorem B5630755 : Blo 2223435 5630755 := bstep (se 1 (by rfl) ⟨4223066, by rfl⟩ : syracuseStep 5630755 = 8446133) B8446133
theorem B7507673 : Blo 2223435 7507673 := bstep (se 2 (by rfl) ⟨2815377, by rfl⟩ : syracuseStep 7507673 = 5630755) B5630755
theorem B5005115 : Blo 2223435 5005115 := bstep (se 1 (by rfl) ⟨3753836, by rfl⟩ : syracuseStep 5005115 = 7507673) B7507673
theorem B3336743 : Blo 2223435 3336743 := bstep (se 1 (by rfl) ⟨2502557, by rfl⟩ : syracuseStep 3336743 = 5005115) B5005115
theorem B2224495 : Blo 2223435 2224495 := bstep (se 1 (by rfl) ⟨1668371, by rfl⟩ : syracuseStep 2224495 = 3336743) B3336743
theorem B3336749 : Blo 2223435 3336749 := bbase (se 3 (by rfl) ⟨625640, by rfl⟩ : syracuseStep 3336749 = 1251281) (by norm_num)
theorem B2224499 : Blo 2223435 2224499 := bstep (se 1 (by rfl) ⟨1668374, by rfl⟩ : syracuseStep 2224499 = 3336749) B3336749
theorem B5005133 : Blo 2223435 5005133 := bbase (se 3 (by rfl) ⟨938462, by rfl⟩ : syracuseStep 5005133 = 1876925) (by norm_num)
theorem B3336755 : Blo 2223435 3336755 := bstep (se 1 (by rfl) ⟨2502566, by rfl⟩ : syracuseStep 3336755 = 5005133) B5005133
theorem B2224503 : Blo 2223435 2224503 := bstep (se 1 (by rfl) ⟨1668377, by rfl⟩ : syracuseStep 2224503 = 3336755) B3336755
theorem B2815393 : Blo 2223435 2815393 := bbase (se 2 (by rfl) ⟨1055772, by rfl⟩ : syracuseStep 2815393 = 2111545) (by norm_num)
theorem B3753857 : Blo 2223435 3753857 := bstep (se 2 (by rfl) ⟨1407696, by rfl⟩ : syracuseStep 3753857 = 2815393) B2815393
theorem B2502571 : Blo 2223435 2502571 := bstep (se 1 (by rfl) ⟨1876928, by rfl⟩ : syracuseStep 2502571 = 3753857) B3753857
theorem B3336761 : Blo 2223435 3336761 := bstep (se 2 (by rfl) ⟨1251285, by rfl⟩ : syracuseStep 3336761 = 2502571) B2502571
theorem B2224507 : Blo 2223435 2224507 := bstep (se 1 (by rfl) ⟨1668380, by rfl⟩ : syracuseStep 2224507 = 3336761) B3336761
theorem B25338581 : Blo 2223435 25338581 := bbase (se 7 (by rfl) ⟨296936, by rfl⟩ : syracuseStep 25338581 = 593873) (by norm_num)
theorem B16892387 : Blo 2223435 16892387 := bstep (se 1 (by rfl) ⟨12669290, by rfl⟩ : syracuseStep 16892387 = 25338581) B25338581
theorem B11261591 : Blo 2223435 11261591 := bstep (se 1 (by rfl) ⟨8446193, by rfl⟩ : syracuseStep 11261591 = 16892387) B16892387
theorem B7507727 : Blo 2223435 7507727 := bstep (se 1 (by rfl) ⟨5630795, by rfl⟩ : syracuseStep 7507727 = 11261591) B11261591
theorem B5005151 : Blo 2223435 5005151 := bstep (se 1 (by rfl) ⟨3753863, by rfl⟩ : syracuseStep 5005151 = 7507727) B7507727
theorem B3336767 : Blo 2223435 3336767 := bstep (se 1 (by rfl) ⟨2502575, by rfl⟩ : syracuseStep 3336767 = 5005151) B5005151
theorem B2224511 : Blo 2223435 2224511 := bstep (se 1 (by rfl) ⟨1668383, by rfl⟩ : syracuseStep 2224511 = 3336767) B3336767
theorem B3336773 : Blo 2223435 3336773 := bbase (se 4 (by rfl) ⟨312822, by rfl⟩ : syracuseStep 3336773 = 625645) (by norm_num)
theorem B2224515 : Blo 2223435 2224515 := bstep (se 1 (by rfl) ⟨1668386, by rfl⟩ : syracuseStep 2224515 = 3336773) B3336773
theorem B3753877 : Blo 2223435 3753877 := bbase (se 6 (by rfl) ⟨87981, by rfl⟩ : syracuseStep 3753877 = 175963) (by norm_num)
theorem B5005169 : Blo 2223435 5005169 := bstep (se 2 (by rfl) ⟨1876938, by rfl⟩ : syracuseStep 5005169 = 3753877) B3753877
theorem B3336779 : Blo 2223435 3336779 := bstep (se 1 (by rfl) ⟨2502584, by rfl⟩ : syracuseStep 3336779 = 5005169) B5005169
theorem B2224519 : Blo 2223435 2224519 := bstep (se 1 (by rfl) ⟨1668389, by rfl⟩ : syracuseStep 2224519 = 3336779) B3336779
theorem B2502589 : Blo 2223435 2502589 := bbase (se 3 (by rfl) ⟨469235, by rfl⟩ : syracuseStep 2502589 = 938471) (by norm_num)
theorem B3336785 : Blo 2223435 3336785 := bstep (se 2 (by rfl) ⟨1251294, by rfl⟩ : syracuseStep 3336785 = 2502589) B2502589
theorem B2224523 : Blo 2223435 2224523 := bstep (se 1 (by rfl) ⟨1668392, by rfl⟩ : syracuseStep 2224523 = 3336785) B3336785
theorem B7507781 : Blo 2223435 7507781 := bbase (se 4 (by rfl) ⟨703854, by rfl⟩ : syracuseStep 7507781 = 1407709) (by norm_num)
theorem B5005187 : Blo 2223435 5005187 := bstep (se 1 (by rfl) ⟨3753890, by rfl⟩ : syracuseStep 5005187 = 7507781) B7507781
theorem B3336791 : Blo 2223435 3336791 := bstep (se 1 (by rfl) ⟨2502593, by rfl⟩ : syracuseStep 3336791 = 5005187) B5005187
theorem B2224527 : Blo 2223435 2224527 := bstep (se 1 (by rfl) ⟨1668395, by rfl⟩ : syracuseStep 2224527 = 3336791) B3336791
theorem B3336797 : Blo 2223435 3336797 := bbase (se 3 (by rfl) ⟨625649, by rfl⟩ : syracuseStep 3336797 = 1251299) (by norm_num)
theorem B2224531 : Blo 2223435 2224531 := bstep (se 1 (by rfl) ⟨1668398, by rfl⟩ : syracuseStep 2224531 = 3336797) B3336797
theorem B5005205 : Blo 2223435 5005205 := bbase (se 6 (by rfl) ⟨117309, by rfl⟩ : syracuseStep 5005205 = 234619) (by norm_num)
theorem B3336803 : Blo 2223435 3336803 := bstep (se 1 (by rfl) ⟨2502602, by rfl⟩ : syracuseStep 3336803 = 5005205) B5005205
theorem B2224535 : Blo 2223435 2224535 := bstep (se 1 (by rfl) ⟨1668401, by rfl⟩ : syracuseStep 2224535 = 3336803) B3336803
theorem B4751045 : Blo 2223435 4751045 := bbase (se 4 (by rfl) ⟨445410, by rfl⟩ : syracuseStep 4751045 = 890821) (by norm_num)
theorem B3167363 : Blo 2223435 3167363 := bstep (se 1 (by rfl) ⟨2375522, by rfl⟩ : syracuseStep 3167363 = 4751045) B4751045
theorem B8446301 : Blo 2223435 8446301 := bstep (se 3 (by rfl) ⟨1583681, by rfl⟩ : syracuseStep 8446301 = 3167363) B3167363
theorem B5630867 : Blo 2223435 5630867 := bstep (se 1 (by rfl) ⟨4223150, by rfl⟩ : syracuseStep 5630867 = 8446301) B8446301
theorem B3753911 : Blo 2223435 3753911 := bstep (se 1 (by rfl) ⟨2815433, by rfl⟩ : syracuseStep 3753911 = 5630867) B5630867
theorem B2502607 : Blo 2223435 2502607 := bstep (se 1 (by rfl) ⟨1876955, by rfl⟩ : syracuseStep 2502607 = 3753911) B3753911
theorem B3336809 : Blo 2223435 3336809 := bstep (se 2 (by rfl) ⟨1251303, by rfl⟩ : syracuseStep 3336809 = 2502607) B2502607
theorem B2224539 : Blo 2223435 2224539 := bstep (se 1 (by rfl) ⟨1668404, by rfl⟩ : syracuseStep 2224539 = 3336809) B3336809
theorem B4008701 : Blo 2223435 4008701 := bbase (se 3 (by rfl) ⟨751631, by rfl⟩ : syracuseStep 4008701 = 1503263) (by norm_num)
theorem B10689869 : Blo 2223435 10689869 := bstep (se 3 (by rfl) ⟨2004350, by rfl⟩ : syracuseStep 10689869 = 4008701) B4008701
theorem B7126579 : Blo 2223435 7126579 := bstep (se 1 (by rfl) ⟨5344934, by rfl⟩ : syracuseStep 7126579 = 10689869) B10689869
theorem B9502105 : Blo 2223435 9502105 := bstep (se 2 (by rfl) ⟨3563289, by rfl⟩ : syracuseStep 9502105 = 7126579) B7126579
theorem B12669473 : Blo 2223435 12669473 := bstep (se 2 (by rfl) ⟨4751052, by rfl⟩ : syracuseStep 12669473 = 9502105) B9502105
theorem B8446315 : Blo 2223435 8446315 := bstep (se 1 (by rfl) ⟨6334736, by rfl⟩ : syracuseStep 8446315 = 12669473) B12669473
theorem B11261753 : Blo 2223435 11261753 := bstep (se 2 (by rfl) ⟨4223157, by rfl⟩ : syracuseStep 11261753 = 8446315) B8446315
theorem B7507835 : Blo 2223435 7507835 := bstep (se 1 (by rfl) ⟨5630876, by rfl⟩ : syracuseStep 7507835 = 11261753) B11261753
theorem B5005223 : Blo 2223435 5005223 := bstep (se 1 (by rfl) ⟨3753917, by rfl⟩ : syracuseStep 5005223 = 7507835) B7507835
theorem B3336815 : Blo 2223435 3336815 := bstep (se 1 (by rfl) ⟨2502611, by rfl⟩ : syracuseStep 3336815 = 5005223) B5005223
theorem B2224543 : Blo 2223435 2224543 := bstep (se 1 (by rfl) ⟨1668407, by rfl⟩ : syracuseStep 2224543 = 3336815) B3336815
theorem B3336821 : Blo 2223435 3336821 := bbase (se 5 (by rfl) ⟨156413, by rfl⟩ : syracuseStep 3336821 = 312827) (by norm_num)
theorem B2224547 : Blo 2223435 2224547 := bstep (se 1 (by rfl) ⟨1668410, by rfl⟩ : syracuseStep 2224547 = 3336821) B3336821
theorem B4223173 : Blo 2223435 4223173 := bbase (se 4 (by rfl) ⟨395922, by rfl⟩ : syracuseStep 4223173 = 791845) (by norm_num)
theorem B5630897 : Blo 2223435 5630897 := bstep (se 2 (by rfl) ⟨2111586, by rfl⟩ : syracuseStep 5630897 = 4223173) B4223173
theorem B3753931 : Blo 2223435 3753931 := bstep (se 1 (by rfl) ⟨2815448, by rfl⟩ : syracuseStep 3753931 = 5630897) B5630897
theorem B5005241 : Blo 2223435 5005241 := bstep (se 2 (by rfl) ⟨1876965, by rfl⟩ : syracuseStep 5005241 = 3753931) B3753931
theorem B3336827 : Blo 2223435 3336827 := bstep (se 1 (by rfl) ⟨2502620, by rfl⟩ : syracuseStep 3336827 = 5005241) B5005241
theorem B2224551 : Blo 2223435 2224551 := bstep (se 1 (by rfl) ⟨1668413, by rfl⟩ : syracuseStep 2224551 = 3336827) B3336827
theorem B2502625 : Blo 2223435 2502625 := bbase (se 2 (by rfl) ⟨938484, by rfl⟩ : syracuseStep 2502625 = 1876969) (by norm_num)
theorem B3336833 : Blo 2223435 3336833 := bstep (se 2 (by rfl) ⟨1251312, by rfl⟩ : syracuseStep 3336833 = 2502625) B2502625
theorem B2224555 : Blo 2223435 2224555 := bstep (se 1 (by rfl) ⟨1668416, by rfl⟩ : syracuseStep 2224555 = 3336833) B3336833
theorem B5630917 : Blo 2223435 5630917 := bbase (se 4 (by rfl) ⟨527898, by rfl⟩ : syracuseStep 5630917 = 1055797) (by norm_num)
theorem B7507889 : Blo 2223435 7507889 := bstep (se 2 (by rfl) ⟨2815458, by rfl⟩ : syracuseStep 7507889 = 5630917) B5630917
theorem B5005259 : Blo 2223435 5005259 := bstep (se 1 (by rfl) ⟨3753944, by rfl⟩ : syracuseStep 5005259 = 7507889) B7507889
theorem B3336839 : Blo 2223435 3336839 := bstep (se 1 (by rfl) ⟨2502629, by rfl⟩ : syracuseStep 3336839 = 5005259) B5005259
theorem B2224559 : Blo 2223435 2224559 := bstep (se 1 (by rfl) ⟨1668419, by rfl⟩ : syracuseStep 2224559 = 3336839) B3336839
theorem B3336845 : Blo 2223435 3336845 := bbase (se 3 (by rfl) ⟨625658, by rfl⟩ : syracuseStep 3336845 = 1251317) (by norm_num)
theorem B2224563 : Blo 2223435 2224563 := bstep (se 1 (by rfl) ⟨1668422, by rfl⟩ : syracuseStep 2224563 = 3336845) B3336845
theorem B5005277 : Blo 2223435 5005277 := bbase (se 3 (by rfl) ⟨938489, by rfl⟩ : syracuseStep 5005277 = 1876979) (by norm_num)
theorem B3336851 : Blo 2223435 3336851 := bstep (se 1 (by rfl) ⟨2502638, by rfl⟩ : syracuseStep 3336851 = 5005277) B5005277
theorem B2224567 : Blo 2223435 2224567 := bstep (se 1 (by rfl) ⟨1668425, by rfl⟩ : syracuseStep 2224567 = 3336851) B3336851
theorem B3753965 : Blo 2223435 3753965 := bbase (se 3 (by rfl) ⟨703868, by rfl⟩ : syracuseStep 3753965 = 1407737) (by norm_num)
theorem B2502643 : Blo 2223435 2502643 := bstep (se 1 (by rfl) ⟨1876982, by rfl⟩ : syracuseStep 2502643 = 3753965) B3753965
theorem B3336857 : Blo 2223435 3336857 := bstep (se 2 (by rfl) ⟨1251321, by rfl⟩ : syracuseStep 3336857 = 2502643) B2502643
theorem B2224571 : Blo 2223435 2224571 := bstep (se 1 (by rfl) ⟨1668428, by rfl⟩ : syracuseStep 2224571 = 3336857) B3336857
theorem B2853893 : Blo 2223435 2853893 := bbase (se 4 (by rfl) ⟨267552, by rfl⟩ : syracuseStep 2853893 = 535105) (by norm_num)
theorem B7610381 : Blo 2223435 7610381 := bstep (se 3 (by rfl) ⟨1426946, by rfl⟩ : syracuseStep 7610381 = 2853893) B2853893
theorem B5073587 : Blo 2223435 5073587 := bstep (se 1 (by rfl) ⟨3805190, by rfl⟩ : syracuseStep 5073587 = 7610381) B7610381
theorem B3382391 : Blo 2223435 3382391 := bstep (se 1 (by rfl) ⟨2536793, by rfl⟩ : syracuseStep 3382391 = 5073587) B5073587
theorem B2254927 : Blo 2223435 2254927 := bstep (se 1 (by rfl) ⟨1691195, by rfl⟩ : syracuseStep 2254927 = 3382391) B3382391
theorem B3006569 : Blo 2223435 3006569 := bstep (se 2 (by rfl) ⟨1127463, by rfl⟩ : syracuseStep 3006569 = 2254927) B2254927
theorem B8017517 : Blo 2223435 8017517 := bstep (se 3 (by rfl) ⟨1503284, by rfl⟩ : syracuseStep 8017517 = 3006569) B3006569
theorem B5345011 : Blo 2223435 5345011 := bstep (se 1 (by rfl) ⟨4008758, by rfl⟩ : syracuseStep 5345011 = 8017517) B8017517
theorem B28506725 : Blo 2223435 28506725 := bstep (se 4 (by rfl) ⟨2672505, by rfl⟩ : syracuseStep 28506725 = 5345011) B5345011
theorem B19004483 : Blo 2223435 19004483 := bstep (se 1 (by rfl) ⟨14253362, by rfl⟩ : syracuseStep 19004483 = 28506725) B28506725
theorem B12669655 : Blo 2223435 12669655 := bstep (se 1 (by rfl) ⟨9502241, by rfl⟩ : syracuseStep 12669655 = 19004483) B19004483
theorem B16892873 : Blo 2223435 16892873 := bstep (se 2 (by rfl) ⟨6334827, by rfl⟩ : syracuseStep 16892873 = 12669655) B12669655
theorem B11261915 : Blo 2223435 11261915 := bstep (se 1 (by rfl) ⟨8446436, by rfl⟩ : syracuseStep 11261915 = 16892873) B16892873
theorem B7507943 : Blo 2223435 7507943 := bstep (se 1 (by rfl) ⟨5630957, by rfl⟩ : syracuseStep 7507943 = 11261915) B11261915
theorem B5005295 : Blo 2223435 5005295 := bstep (se 1 (by rfl) ⟨3753971, by rfl⟩ : syracuseStep 5005295 = 7507943) B7507943
theorem B3336863 : Blo 2223435 3336863 := bstep (se 1 (by rfl) ⟨2502647, by rfl⟩ : syracuseStep 3336863 = 5005295) B5005295
theorem B2224575 : Blo 2223435 2224575 := bstep (se 1 (by rfl) ⟨1668431, by rfl⟩ : syracuseStep 2224575 = 3336863) B3336863
theorem B3336869 : Blo 2223435 3336869 := bbase (se 4 (by rfl) ⟨312831, by rfl⟩ : syracuseStep 3336869 = 625663) (by norm_num)
theorem B2224579 : Blo 2223435 2224579 := bstep (se 1 (by rfl) ⟨1668434, by rfl⟩ : syracuseStep 2224579 = 3336869) B3336869
theorem B2815489 : Blo 2223435 2815489 := bbase (se 2 (by rfl) ⟨1055808, by rfl⟩ : syracuseStep 2815489 = 2111617) (by norm_num)
theorem B3753985 : Blo 2223435 3753985 := bstep (se 2 (by rfl) ⟨1407744, by rfl⟩ : syracuseStep 3753985 = 2815489) B2815489
theorem B5005313 : Blo 2223435 5005313 := bstep (se 2 (by rfl) ⟨1876992, by rfl⟩ : syracuseStep 5005313 = 3753985) B3753985
theorem B3336875 : Blo 2223435 3336875 := bstep (se 1 (by rfl) ⟨2502656, by rfl⟩ : syracuseStep 3336875 = 5005313) B5005313
theorem B2224583 : Blo 2223435 2224583 := bstep (se 1 (by rfl) ⟨1668437, by rfl⟩ : syracuseStep 2224583 = 3336875) B3336875
theorem B2502661 : Blo 2223435 2502661 := bbase (se 4 (by rfl) ⟨234624, by rfl⟩ : syracuseStep 2502661 = 469249) (by norm_num)
theorem B3336881 : Blo 2223435 3336881 := bstep (se 2 (by rfl) ⟨1251330, by rfl⟩ : syracuseStep 3336881 = 2502661) B2502661
theorem B2224587 : Blo 2223435 2224587 := bstep (se 1 (by rfl) ⟨1668440, by rfl⟩ : syracuseStep 2224587 = 3336881) B3336881
theorem B3167437 : Blo 2223435 3167437 := bbase (se 3 (by rfl) ⟨593894, by rfl⟩ : syracuseStep 3167437 = 1187789) (by norm_num)
theorem B4223249 : Blo 2223435 4223249 := bstep (se 2 (by rfl) ⟨1583718, by rfl⟩ : syracuseStep 4223249 = 3167437) B3167437
theorem B2815499 : Blo 2223435 2815499 := bstep (se 1 (by rfl) ⟨2111624, by rfl⟩ : syracuseStep 2815499 = 4223249) B4223249
theorem B7507997 : Blo 2223435 7507997 := bstep (se 3 (by rfl) ⟨1407749, by rfl⟩ : syracuseStep 7507997 = 2815499) B2815499
theorem B5005331 : Blo 2223435 5005331 := bstep (se 1 (by rfl) ⟨3753998, by rfl⟩ : syracuseStep 5005331 = 7507997) B7507997
theorem B3336887 : Blo 2223435 3336887 := bstep (se 1 (by rfl) ⟨2502665, by rfl⟩ : syracuseStep 3336887 = 5005331) B5005331
theorem B2224591 : Blo 2223435 2224591 := bstep (se 1 (by rfl) ⟨1668443, by rfl⟩ : syracuseStep 2224591 = 3336887) B3336887
theorem B3336893 : Blo 2223435 3336893 := bbase (se 3 (by rfl) ⟨625667, by rfl⟩ : syracuseStep 3336893 = 1251335) (by norm_num)
theorem B2224595 : Blo 2223435 2224595 := bstep (se 1 (by rfl) ⟨1668446, by rfl⟩ : syracuseStep 2224595 = 3336893) B3336893
theorem B5005349 : Blo 2223435 5005349 := bbase (se 4 (by rfl) ⟨469251, by rfl⟩ : syracuseStep 5005349 = 938503) (by norm_num)
theorem B3336899 : Blo 2223435 3336899 := bstep (se 1 (by rfl) ⟨2502674, by rfl⟩ : syracuseStep 3336899 = 5005349) B5005349
theorem B2224599 : Blo 2223435 2224599 := bstep (se 1 (by rfl) ⟨1668449, by rfl⟩ : syracuseStep 2224599 = 3336899) B3336899
theorem B5631029 : Blo 2223435 5631029 := bbase (se 5 (by rfl) ⟨263954, by rfl⟩ : syracuseStep 5631029 = 527909) (by norm_num)
theorem B3754019 : Blo 2223435 3754019 := bstep (se 1 (by rfl) ⟨2815514, by rfl⟩ : syracuseStep 3754019 = 5631029) B5631029
theorem B2502679 : Blo 2223435 2502679 := bstep (se 1 (by rfl) ⟨1877009, by rfl⟩ : syracuseStep 2502679 = 3754019) B3754019
theorem B3336905 : Blo 2223435 3336905 := bstep (se 2 (by rfl) ⟨1251339, by rfl⟩ : syracuseStep 3336905 = 2502679) B2502679
theorem B2224603 : Blo 2223435 2224603 := bstep (se 1 (by rfl) ⟨1668452, by rfl⟩ : syracuseStep 2224603 = 3336905) B3336905
theorem B7322581 : Blo 2223435 7322581 := bbase (se 7 (by rfl) ⟨85811, by rfl⟩ : syracuseStep 7322581 = 171623) (by norm_num)
theorem B39053765 : Blo 2223435 39053765 := bstep (se 4 (by rfl) ⟨3661290, by rfl⟩ : syracuseStep 39053765 = 7322581) B7322581
theorem B26035843 : Blo 2223435 26035843 := bstep (se 1 (by rfl) ⟨19526882, by rfl⟩ : syracuseStep 26035843 = 39053765) B39053765
theorem B34714457 : Blo 2223435 34714457 := bstep (se 2 (by rfl) ⟨13017921, by rfl⟩ : syracuseStep 34714457 = 26035843) B26035843
theorem B23142971 : Blo 2223435 23142971 := bstep (se 1 (by rfl) ⟨17357228, by rfl⟩ : syracuseStep 23142971 = 34714457) B34714457
theorem B15428647 : Blo 2223435 15428647 := bstep (se 1 (by rfl) ⟨11571485, by rfl⟩ : syracuseStep 15428647 = 23142971) B23142971
theorem B82286117 : Blo 2223435 82286117 := bstep (se 4 (by rfl) ⟨7714323, by rfl⟩ : syracuseStep 82286117 = 15428647) B15428647
theorem B54857411 : Blo 2223435 54857411 := bstep (se 1 (by rfl) ⟨41143058, by rfl⟩ : syracuseStep 54857411 = 82286117) B82286117
theorem B36571607 : Blo 2223435 36571607 := bstep (se 1 (by rfl) ⟨27428705, by rfl⟩ : syracuseStep 36571607 = 54857411) B54857411
theorem B24381071 : Blo 2223435 24381071 := bstep (se 1 (by rfl) ⟨18285803, by rfl⟩ : syracuseStep 24381071 = 36571607) B36571607
theorem B16254047 : Blo 2223435 16254047 := bstep (se 1 (by rfl) ⟨12190535, by rfl⟩ : syracuseStep 16254047 = 24381071) B24381071
theorem B10836031 : Blo 2223435 10836031 := bstep (se 1 (by rfl) ⟨8127023, by rfl⟩ : syracuseStep 10836031 = 16254047) B16254047
theorem B14448041 : Blo 2223435 14448041 := bstep (se 2 (by rfl) ⟨5418015, by rfl⟩ : syracuseStep 14448041 = 10836031) B10836031
theorem B9632027 : Blo 2223435 9632027 := bstep (se 1 (by rfl) ⟨7224020, by rfl⟩ : syracuseStep 9632027 = 14448041) B14448041
theorem B6421351 : Blo 2223435 6421351 := bstep (se 1 (by rfl) ⟨4816013, by rfl⟩ : syracuseStep 6421351 = 9632027) B9632027
theorem B8561801 : Blo 2223435 8561801 := bstep (se 2 (by rfl) ⟨3210675, by rfl⟩ : syracuseStep 8561801 = 6421351) B6421351
theorem B22831469 : Blo 2223435 22831469 := bstep (se 3 (by rfl) ⟨4280900, by rfl⟩ : syracuseStep 22831469 = 8561801) B8561801
theorem B15220979 : Blo 2223435 15220979 := bstep (se 1 (by rfl) ⟨11415734, by rfl⟩ : syracuseStep 15220979 = 22831469) B22831469
theorem B10147319 : Blo 2223435 10147319 := bstep (se 1 (by rfl) ⟨7610489, by rfl⟩ : syracuseStep 10147319 = 15220979) B15220979
theorem B6764879 : Blo 2223435 6764879 := bstep (se 1 (by rfl) ⟨5073659, by rfl⟩ : syracuseStep 6764879 = 10147319) B10147319
theorem B4509919 : Blo 2223435 4509919 := bstep (se 1 (by rfl) ⟨3382439, by rfl⟩ : syracuseStep 4509919 = 6764879) B6764879
theorem B6013225 : Blo 2223435 6013225 := bstep (se 2 (by rfl) ⟨2254959, by rfl⟩ : syracuseStep 6013225 = 4509919) B4509919
theorem B8017633 : Blo 2223435 8017633 := bstep (se 2 (by rfl) ⟨3006612, by rfl⟩ : syracuseStep 8017633 = 6013225) B6013225
theorem B10690177 : Blo 2223435 10690177 := bstep (se 2 (by rfl) ⟨4008816, by rfl⟩ : syracuseStep 10690177 = 8017633) B8017633
theorem B14253569 : Blo 2223435 14253569 := bstep (se 2 (by rfl) ⟨5345088, by rfl⟩ : syracuseStep 14253569 = 10690177) B10690177
theorem B9502379 : Blo 2223435 9502379 := bstep (se 1 (by rfl) ⟨7126784, by rfl⟩ : syracuseStep 9502379 = 14253569) B14253569
theorem B6334919 : Blo 2223435 6334919 := bstep (se 1 (by rfl) ⟨4751189, by rfl⟩ : syracuseStep 6334919 = 9502379) B9502379
theorem B4223279 : Blo 2223435 4223279 := bstep (se 1 (by rfl) ⟨3167459, by rfl⟩ : syracuseStep 4223279 = 6334919) B6334919
theorem B11262077 : Blo 2223435 11262077 := bstep (se 3 (by rfl) ⟨2111639, by rfl⟩ : syracuseStep 11262077 = 4223279) B4223279
theorem B7508051 : Blo 2223435 7508051 := bstep (se 1 (by rfl) ⟨5631038, by rfl⟩ : syracuseStep 7508051 = 11262077) B11262077
theorem B5005367 : Blo 2223435 5005367 := bstep (se 1 (by rfl) ⟨3754025, by rfl⟩ : syracuseStep 5005367 = 7508051) B7508051
theorem B3336911 : Blo 2223435 3336911 := bstep (se 1 (by rfl) ⟨2502683, by rfl⟩ : syracuseStep 3336911 = 5005367) B5005367
theorem B2224607 : Blo 2223435 2224607 := bstep (se 1 (by rfl) ⟨1668455, by rfl⟩ : syracuseStep 2224607 = 3336911) B3336911
theorem B3336917 : Blo 2223435 3336917 := bbase (se 7 (by rfl) ⟨39104, by rfl⟩ : syracuseStep 3336917 = 78209) (by norm_num)
theorem B2224611 : Blo 2223435 2224611 := bstep (se 1 (by rfl) ⟨1668458, by rfl⟩ : syracuseStep 2224611 = 3336917) B3336917
theorem B10426133 : Blo 2223435 10426133 := bbase (se 6 (by rfl) ⟨244362, by rfl⟩ : syracuseStep 10426133 = 488725) (by norm_num)
theorem B6950755 : Blo 2223435 6950755 := bstep (se 1 (by rfl) ⟨5213066, by rfl⟩ : syracuseStep 6950755 = 10426133) B10426133
theorem B37070693 : Blo 2223435 37070693 := bstep (se 4 (by rfl) ⟨3475377, by rfl⟩ : syracuseStep 37070693 = 6950755) B6950755
theorem B24713795 : Blo 2223435 24713795 := bstep (se 1 (by rfl) ⟨18535346, by rfl⟩ : syracuseStep 24713795 = 37070693) B37070693
theorem B65903453 : Blo 2223435 65903453 := bstep (se 3 (by rfl) ⟨12356897, by rfl⟩ : syracuseStep 65903453 = 24713795) B24713795
theorem B43935635 : Blo 2223435 43935635 := bstep (se 1 (by rfl) ⟨32951726, by rfl⟩ : syracuseStep 43935635 = 65903453) B65903453
theorem B29290423 : Blo 2223435 29290423 := bstep (se 1 (by rfl) ⟨21967817, by rfl⟩ : syracuseStep 29290423 = 43935635) B43935635
theorem B39053897 : Blo 2223435 39053897 := bstep (se 2 (by rfl) ⟨14645211, by rfl⟩ : syracuseStep 39053897 = 29290423) B29290423
theorem B26035931 : Blo 2223435 26035931 := bstep (se 1 (by rfl) ⟨19526948, by rfl⟩ : syracuseStep 26035931 = 39053897) B39053897
theorem B69429149 : Blo 2223435 69429149 := bstep (se 3 (by rfl) ⟨13017965, by rfl⟩ : syracuseStep 69429149 = 26035931) B26035931
theorem B46286099 : Blo 2223435 46286099 := bstep (se 1 (by rfl) ⟨34714574, by rfl⟩ : syracuseStep 46286099 = 69429149) B69429149
theorem B30857399 : Blo 2223435 30857399 := bstep (se 1 (by rfl) ⟨23143049, by rfl⟩ : syracuseStep 30857399 = 46286099) B46286099
theorem B20571599 : Blo 2223435 20571599 := bstep (se 1 (by rfl) ⟨15428699, by rfl⟩ : syracuseStep 20571599 = 30857399) B30857399
theorem B13714399 : Blo 2223435 13714399 := bstep (se 1 (by rfl) ⟨10285799, by rfl⟩ : syracuseStep 13714399 = 20571599) B20571599
theorem B73143461 : Blo 2223435 73143461 := bstep (se 4 (by rfl) ⟨6857199, by rfl⟩ : syracuseStep 73143461 = 13714399) B13714399
theorem B48762307 : Blo 2223435 48762307 := bstep (se 1 (by rfl) ⟨36571730, by rfl⟩ : syracuseStep 48762307 = 73143461) B73143461
theorem B260065637 : Blo 2223435 260065637 := bstep (se 4 (by rfl) ⟨24381153, by rfl⟩ : syracuseStep 260065637 = 48762307) B48762307
theorem B173377091 : Blo 2223435 173377091 := bstep (se 1 (by rfl) ⟨130032818, by rfl⟩ : syracuseStep 173377091 = 260065637) B260065637
theorem B115584727 : Blo 2223435 115584727 := bstep (se 1 (by rfl) ⟨86688545, by rfl⟩ : syracuseStep 115584727 = 173377091) B173377091
theorem B154112969 : Blo 2223435 154112969 := bstep (se 2 (by rfl) ⟨57792363, by rfl⟩ : syracuseStep 154112969 = 115584727) B115584727
theorem B102741979 : Blo 2223435 102741979 := bstep (se 1 (by rfl) ⟨77056484, by rfl⟩ : syracuseStep 102741979 = 154112969) B154112969
theorem B136989305 : Blo 2223435 136989305 := bstep (se 2 (by rfl) ⟨51370989, by rfl⟩ : syracuseStep 136989305 = 102741979) B102741979
theorem B91326203 : Blo 2223435 91326203 := bstep (se 1 (by rfl) ⟨68494652, by rfl⟩ : syracuseStep 91326203 = 136989305) B136989305
theorem B60884135 : Blo 2223435 60884135 := bstep (se 1 (by rfl) ⟨45663101, by rfl⟩ : syracuseStep 60884135 = 91326203) B91326203
theorem B40589423 : Blo 2223435 40589423 := bstep (se 1 (by rfl) ⟨30442067, by rfl⟩ : syracuseStep 40589423 = 60884135) B60884135
theorem B27059615 : Blo 2223435 27059615 := bstep (se 1 (by rfl) ⟨20294711, by rfl⟩ : syracuseStep 27059615 = 40589423) B40589423
theorem B18039743 : Blo 2223435 18039743 := bstep (se 1 (by rfl) ⟨13529807, by rfl⟩ : syracuseStep 18039743 = 27059615) B27059615
theorem B12026495 : Blo 2223435 12026495 := bstep (se 1 (by rfl) ⟨9019871, by rfl⟩ : syracuseStep 12026495 = 18039743) B18039743
theorem B8017663 : Blo 2223435 8017663 := bstep (se 1 (by rfl) ⟨6013247, by rfl⟩ : syracuseStep 8017663 = 12026495) B12026495
theorem B10690217 : Blo 2223435 10690217 := bstep (se 2 (by rfl) ⟨4008831, by rfl⟩ : syracuseStep 10690217 = 8017663) B8017663
theorem B7126811 : Blo 2223435 7126811 := bstep (se 1 (by rfl) ⟨5345108, by rfl⟩ : syracuseStep 7126811 = 10690217) B10690217
theorem B4751207 : Blo 2223435 4751207 := bstep (se 1 (by rfl) ⟨3563405, by rfl⟩ : syracuseStep 4751207 = 7126811) B7126811
theorem B3167471 : Blo 2223435 3167471 := bstep (se 1 (by rfl) ⟨2375603, by rfl⟩ : syracuseStep 3167471 = 4751207) B4751207
theorem B8446589 : Blo 2223435 8446589 := bstep (se 3 (by rfl) ⟨1583735, by rfl⟩ : syracuseStep 8446589 = 3167471) B3167471
theorem B5631059 : Blo 2223435 5631059 := bstep (se 1 (by rfl) ⟨4223294, by rfl⟩ : syracuseStep 5631059 = 8446589) B8446589
theorem B3754039 : Blo 2223435 3754039 := bstep (se 1 (by rfl) ⟨2815529, by rfl⟩ : syracuseStep 3754039 = 5631059) B5631059
theorem B5005385 : Blo 2223435 5005385 := bstep (se 2 (by rfl) ⟨1877019, by rfl⟩ : syracuseStep 5005385 = 3754039) B3754039
theorem B3336923 : Blo 2223435 3336923 := bstep (se 1 (by rfl) ⟨2502692, by rfl⟩ : syracuseStep 3336923 = 5005385) B5005385
theorem B2224615 : Blo 2223435 2224615 := bstep (se 1 (by rfl) ⟨1668461, by rfl⟩ : syracuseStep 2224615 = 3336923) B3336923
theorem B2502697 : Blo 2223435 2502697 := bbase (se 2 (by rfl) ⟨938511, by rfl⟩ : syracuseStep 2502697 = 1877023) (by norm_num)
theorem B3336929 : Blo 2223435 3336929 := bstep (se 2 (by rfl) ⟨1251348, by rfl⟩ : syracuseStep 3336929 = 2502697) B2502697
theorem B2224619 : Blo 2223435 2224619 := bstep (se 1 (by rfl) ⟨1668464, by rfl⟩ : syracuseStep 2224619 = 3336929) B3336929
theorem B5418053 : Blo 2223435 5418053 := bbase (se 4 (by rfl) ⟨507942, by rfl⟩ : syracuseStep 5418053 = 1015885) (by norm_num)
theorem B3612035 : Blo 2223435 3612035 := bstep (se 1 (by rfl) ⟨2709026, by rfl⟩ : syracuseStep 3612035 = 5418053) B5418053
theorem B9632093 : Blo 2223435 9632093 := bstep (se 3 (by rfl) ⟨1806017, by rfl⟩ : syracuseStep 9632093 = 3612035) B3612035
theorem B25685581 : Blo 2223435 25685581 := bstep (se 3 (by rfl) ⟨4816046, by rfl⟩ : syracuseStep 25685581 = 9632093) B9632093
theorem B34247441 : Blo 2223435 34247441 := bstep (se 2 (by rfl) ⟨12842790, by rfl⟩ : syracuseStep 34247441 = 25685581) B25685581
theorem B22831627 : Blo 2223435 22831627 := bstep (se 1 (by rfl) ⟨17123720, by rfl⟩ : syracuseStep 22831627 = 34247441) B34247441
theorem B30442169 : Blo 2223435 30442169 := bstep (se 2 (by rfl) ⟨11415813, by rfl⟩ : syracuseStep 30442169 = 22831627) B22831627
theorem B81179117 : Blo 2223435 81179117 := bstep (se 3 (by rfl) ⟨15221084, by rfl⟩ : syracuseStep 81179117 = 30442169) B30442169
theorem B54119411 : Blo 2223435 54119411 := bstep (se 1 (by rfl) ⟨40589558, by rfl⟩ : syracuseStep 54119411 = 81179117) B81179117
theorem B36079607 : Blo 2223435 36079607 := bstep (se 1 (by rfl) ⟨27059705, by rfl⟩ : syracuseStep 36079607 = 54119411) B54119411
theorem B24053071 : Blo 2223435 24053071 := bstep (se 1 (by rfl) ⟨18039803, by rfl⟩ : syracuseStep 24053071 = 36079607) B36079607
theorem B32070761 : Blo 2223435 32070761 := bstep (se 2 (by rfl) ⟨12026535, by rfl⟩ : syracuseStep 32070761 = 24053071) B24053071
theorem B21380507 : Blo 2223435 21380507 := bstep (se 1 (by rfl) ⟨16035380, by rfl⟩ : syracuseStep 21380507 = 32070761) B32070761
theorem B14253671 : Blo 2223435 14253671 := bstep (se 1 (by rfl) ⟨10690253, by rfl⟩ : syracuseStep 14253671 = 21380507) B21380507
theorem B9502447 : Blo 2223435 9502447 := bstep (se 1 (by rfl) ⟨7126835, by rfl⟩ : syracuseStep 9502447 = 14253671) B14253671
theorem B12669929 : Blo 2223435 12669929 := bstep (se 2 (by rfl) ⟨4751223, by rfl⟩ : syracuseStep 12669929 = 9502447) B9502447
theorem B8446619 : Blo 2223435 8446619 := bstep (se 1 (by rfl) ⟨6334964, by rfl⟩ : syracuseStep 8446619 = 12669929) B12669929
theorem B5631079 : Blo 2223435 5631079 := bstep (se 1 (by rfl) ⟨4223309, by rfl⟩ : syracuseStep 5631079 = 8446619) B8446619
theorem B7508105 : Blo 2223435 7508105 := bstep (se 2 (by rfl) ⟨2815539, by rfl⟩ : syracuseStep 7508105 = 5631079) B5631079
theorem B5005403 : Blo 2223435 5005403 := bstep (se 1 (by rfl) ⟨3754052, by rfl⟩ : syracuseStep 5005403 = 7508105) B7508105
theorem B3336935 : Blo 2223435 3336935 := bstep (se 1 (by rfl) ⟨2502701, by rfl⟩ : syracuseStep 3336935 = 5005403) B5005403
theorem B2224623 : Blo 2223435 2224623 := bstep (se 1 (by rfl) ⟨1668467, by rfl⟩ : syracuseStep 2224623 = 3336935) B3336935
theorem B3336941 : Blo 2223435 3336941 := bbase (se 3 (by rfl) ⟨625676, by rfl⟩ : syracuseStep 3336941 = 1251353) (by norm_num)
theorem B2224627 : Blo 2223435 2224627 := bstep (se 1 (by rfl) ⟨1668470, by rfl⟩ : syracuseStep 2224627 = 3336941) B3336941
theorem B5005421 : Blo 2223435 5005421 := bbase (se 3 (by rfl) ⟨938516, by rfl⟩ : syracuseStep 5005421 = 1877033) (by norm_num)
theorem B3336947 : Blo 2223435 3336947 := bstep (se 1 (by rfl) ⟨2502710, by rfl⟩ : syracuseStep 3336947 = 5005421) B5005421
theorem B2224631 : Blo 2223435 2224631 := bstep (se 1 (by rfl) ⟨1668473, by rfl⟩ : syracuseStep 2224631 = 3336947) B3336947
theorem B4223333 : Blo 2223435 4223333 := bbase (se 4 (by rfl) ⟨395937, by rfl⟩ : syracuseStep 4223333 = 791875) (by norm_num)
theorem B2815555 : Blo 2223435 2815555 := bstep (se 1 (by rfl) ⟨2111666, by rfl⟩ : syracuseStep 2815555 = 4223333) B4223333
theorem B3754073 : Blo 2223435 3754073 := bstep (se 2 (by rfl) ⟨1407777, by rfl⟩ : syracuseStep 3754073 = 2815555) B2815555
theorem B2502715 : Blo 2223435 2502715 := bstep (se 1 (by rfl) ⟨1877036, by rfl⟩ : syracuseStep 2502715 = 3754073) B3754073
theorem B3336953 : Blo 2223435 3336953 := bstep (se 2 (by rfl) ⟨1251357, by rfl⟩ : syracuseStep 3336953 = 2502715) B2502715
theorem B2224635 : Blo 2223435 2224635 := bstep (se 1 (by rfl) ⟨1668476, by rfl⟩ : syracuseStep 2224635 = 3336953) B3336953
theorem B2408041 : Blo 2223435 2408041 := bbase (se 2 (by rfl) ⟨903015, by rfl⟩ : syracuseStep 2408041 = 1806031) (by norm_num)
theorem B3210721 : Blo 2223435 3210721 := bstep (se 2 (by rfl) ⟨1204020, by rfl⟩ : syracuseStep 3210721 = 2408041) B2408041
theorem B17123845 : Blo 2223435 17123845 := bstep (se 4 (by rfl) ⟨1605360, by rfl⟩ : syracuseStep 17123845 = 3210721) B3210721
theorem B22831793 : Blo 2223435 22831793 := bstep (se 2 (by rfl) ⟨8561922, by rfl⟩ : syracuseStep 22831793 = 17123845) B17123845
theorem B15221195 : Blo 2223435 15221195 := bstep (se 1 (by rfl) ⟨11415896, by rfl⟩ : syracuseStep 15221195 = 22831793) B22831793
theorem B10147463 : Blo 2223435 10147463 := bstep (se 1 (by rfl) ⟨7610597, by rfl⟩ : syracuseStep 10147463 = 15221195) B15221195
theorem B6764975 : Blo 2223435 6764975 := bstep (se 1 (by rfl) ⟨5073731, by rfl⟩ : syracuseStep 6764975 = 10147463) B10147463
theorem B4509983 : Blo 2223435 4509983 := bstep (se 1 (by rfl) ⟨3382487, by rfl⟩ : syracuseStep 4509983 = 6764975) B6764975
theorem B12026621 : Blo 2223435 12026621 := bstep (se 3 (by rfl) ⟨2254991, by rfl⟩ : syracuseStep 12026621 = 4509983) B4509983
theorem B8017747 : Blo 2223435 8017747 := bstep (se 1 (by rfl) ⟨6013310, by rfl⟩ : syracuseStep 8017747 = 12026621) B12026621
theorem B42761317 : Blo 2223435 42761317 := bstep (se 4 (by rfl) ⟨4008873, by rfl⟩ : syracuseStep 42761317 = 8017747) B8017747
theorem B57015089 : Blo 2223435 57015089 := bstep (se 2 (by rfl) ⟨21380658, by rfl⟩ : syracuseStep 57015089 = 42761317) B42761317
theorem B38010059 : Blo 2223435 38010059 := bstep (se 1 (by rfl) ⟨28507544, by rfl⟩ : syracuseStep 38010059 = 57015089) B57015089
theorem B25340039 : Blo 2223435 25340039 := bstep (se 1 (by rfl) ⟨19005029, by rfl⟩ : syracuseStep 25340039 = 38010059) B38010059
theorem B16893359 : Blo 2223435 16893359 := bstep (se 1 (by rfl) ⟨12670019, by rfl⟩ : syracuseStep 16893359 = 25340039) B25340039
theorem B11262239 : Blo 2223435 11262239 := bstep (se 1 (by rfl) ⟨8446679, by rfl⟩ : syracuseStep 11262239 = 16893359) B16893359
theorem B7508159 : Blo 2223435 7508159 := bstep (se 1 (by rfl) ⟨5631119, by rfl⟩ : syracuseStep 7508159 = 11262239) B11262239
theorem B5005439 : Blo 2223435 5005439 := bstep (se 1 (by rfl) ⟨3754079, by rfl⟩ : syracuseStep 5005439 = 7508159) B7508159
theorem B3336959 : Blo 2223435 3336959 := bstep (se 1 (by rfl) ⟨2502719, by rfl⟩ : syracuseStep 3336959 = 5005439) B5005439
theorem B2224639 : Blo 2223435 2224639 := bstep (se 1 (by rfl) ⟨1668479, by rfl⟩ : syracuseStep 2224639 = 3336959) B3336959
theorem B3336965 : Blo 2223435 3336965 := bbase (se 4 (by rfl) ⟨312840, by rfl⟩ : syracuseStep 3336965 = 625681) (by norm_num)
theorem B2224643 : Blo 2223435 2224643 := bstep (se 1 (by rfl) ⟨1668482, by rfl⟩ : syracuseStep 2224643 = 3336965) B3336965
theorem B3754093 : Blo 2223435 3754093 := bbase (se 3 (by rfl) ⟨703892, by rfl⟩ : syracuseStep 3754093 = 1407785) (by norm_num)
theorem B5005457 : Blo 2223435 5005457 := bstep (se 2 (by rfl) ⟨1877046, by rfl⟩ : syracuseStep 5005457 = 3754093) B3754093
theorem B3336971 : Blo 2223435 3336971 := bstep (se 1 (by rfl) ⟨2502728, by rfl⟩ : syracuseStep 3336971 = 5005457) B5005457
theorem B2224647 : Blo 2223435 2224647 := bstep (se 1 (by rfl) ⟨1668485, by rfl⟩ : syracuseStep 2224647 = 3336971) B3336971
theorem B2502733 : Blo 2223435 2502733 := bbase (se 3 (by rfl) ⟨469262, by rfl⟩ : syracuseStep 2502733 = 938525) (by norm_num)
theorem B3336977 : Blo 2223435 3336977 := bstep (se 2 (by rfl) ⟨1251366, by rfl⟩ : syracuseStep 3336977 = 2502733) B2502733
theorem B2224651 : Blo 2223435 2224651 := bstep (se 1 (by rfl) ⟨1668488, by rfl⟩ : syracuseStep 2224651 = 3336977) B3336977
theorem B7508213 : Blo 2223435 7508213 := bbase (se 5 (by rfl) ⟨351947, by rfl⟩ : syracuseStep 7508213 = 703895) (by norm_num)
theorem B5005475 : Blo 2223435 5005475 := bstep (se 1 (by rfl) ⟨3754106, by rfl⟩ : syracuseStep 5005475 = 7508213) B7508213
theorem B3336983 : Blo 2223435 3336983 := bstep (se 1 (by rfl) ⟨2502737, by rfl⟩ : syracuseStep 3336983 = 5005475) B5005475
theorem B2224655 : Blo 2223435 2224655 := bstep (se 1 (by rfl) ⟨1668491, by rfl⟩ : syracuseStep 2224655 = 3336983) B3336983
theorem B3336989 : Blo 2223435 3336989 := bbase (se 3 (by rfl) ⟨625685, by rfl⟩ : syracuseStep 3336989 = 1251371) (by norm_num)
theorem B2224659 : Blo 2223435 2224659 := bstep (se 1 (by rfl) ⟨1668494, by rfl⟩ : syracuseStep 2224659 = 3336989) B3336989
theorem B5005493 : Blo 2223435 5005493 := bbase (se 5 (by rfl) ⟨234632, by rfl⟩ : syracuseStep 5005493 = 469265) (by norm_num)
theorem B3336995 : Blo 2223435 3336995 := bstep (se 1 (by rfl) ⟨2502746, by rfl⟩ : syracuseStep 3336995 = 5005493) B5005493
theorem B2224663 : Blo 2223435 2224663 := bstep (se 1 (by rfl) ⟨1668497, by rfl⟩ : syracuseStep 2224663 = 3336995) B3336995
theorem B2672617 : Blo 2223435 2672617 := bbase (se 2 (by rfl) ⟨1002231, by rfl⟩ : syracuseStep 2672617 = 2004463) (by norm_num)
theorem B3563489 : Blo 2223435 3563489 := bstep (se 2 (by rfl) ⟨1336308, by rfl⟩ : syracuseStep 3563489 = 2672617) B2672617
theorem B2375659 : Blo 2223435 2375659 := bstep (se 1 (by rfl) ⟨1781744, by rfl⟩ : syracuseStep 2375659 = 3563489) B3563489
theorem B12670181 : Blo 2223435 12670181 := bstep (se 4 (by rfl) ⟨1187829, by rfl⟩ : syracuseStep 12670181 = 2375659) B2375659
theorem B8446787 : Blo 2223435 8446787 := bstep (se 1 (by rfl) ⟨6335090, by rfl⟩ : syracuseStep 8446787 = 12670181) B12670181
theorem B5631191 : Blo 2223435 5631191 := bstep (se 1 (by rfl) ⟨4223393, by rfl⟩ : syracuseStep 5631191 = 8446787) B8446787
theorem B3754127 : Blo 2223435 3754127 := bstep (se 1 (by rfl) ⟨2815595, by rfl⟩ : syracuseStep 3754127 = 5631191) B5631191
theorem B2502751 : Blo 2223435 2502751 := bstep (se 1 (by rfl) ⟨1877063, by rfl⟩ : syracuseStep 2502751 = 3754127) B3754127
theorem B3337001 : Blo 2223435 3337001 := bstep (se 2 (by rfl) ⟨1251375, by rfl⟩ : syracuseStep 3337001 = 2502751) B2502751
theorem B2224667 : Blo 2223435 2224667 := bstep (se 1 (by rfl) ⟨1668500, by rfl⟩ : syracuseStep 2224667 = 3337001) B3337001
theorem B2408077 : Blo 2223435 2408077 := bbase (se 3 (by rfl) ⟨451514, by rfl⟩ : syracuseStep 2408077 = 903029) (by norm_num)
theorem B3210769 : Blo 2223435 3210769 := bstep (se 2 (by rfl) ⟨1204038, by rfl⟩ : syracuseStep 3210769 = 2408077) B2408077
theorem B4281025 : Blo 2223435 4281025 := bstep (se 2 (by rfl) ⟨1605384, by rfl⟩ : syracuseStep 4281025 = 3210769) B3210769
theorem B5708033 : Blo 2223435 5708033 := bstep (se 2 (by rfl) ⟨2140512, by rfl⟩ : syracuseStep 5708033 = 4281025) B4281025
theorem B3805355 : Blo 2223435 3805355 := bstep (se 1 (by rfl) ⟨2854016, by rfl⟩ : syracuseStep 3805355 = 5708033) B5708033
theorem B2536903 : Blo 2223435 2536903 := bstep (se 1 (by rfl) ⟨1902677, by rfl⟩ : syracuseStep 2536903 = 3805355) B3805355
theorem B13530149 : Blo 2223435 13530149 := bstep (se 4 (by rfl) ⟨1268451, by rfl⟩ : syracuseStep 13530149 = 2536903) B2536903
theorem B9020099 : Blo 2223435 9020099 := bstep (se 1 (by rfl) ⟨6765074, by rfl⟩ : syracuseStep 9020099 = 13530149) B13530149
theorem B6013399 : Blo 2223435 6013399 := bstep (se 1 (by rfl) ⟨4510049, by rfl⟩ : syracuseStep 6013399 = 9020099) B9020099
theorem B8017865 : Blo 2223435 8017865 := bstep (se 2 (by rfl) ⟨3006699, by rfl⟩ : syracuseStep 8017865 = 6013399) B6013399
theorem B5345243 : Blo 2223435 5345243 := bstep (se 1 (by rfl) ⟨4008932, by rfl⟩ : syracuseStep 5345243 = 8017865) B8017865
theorem B3563495 : Blo 2223435 3563495 := bstep (se 1 (by rfl) ⟨2672621, by rfl⟩ : syracuseStep 3563495 = 5345243) B5345243
theorem B2375663 : Blo 2223435 2375663 := bstep (se 1 (by rfl) ⟨1781747, by rfl⟩ : syracuseStep 2375663 = 3563495) B3563495
theorem B6335101 : Blo 2223435 6335101 := bstep (se 3 (by rfl) ⟨1187831, by rfl⟩ : syracuseStep 6335101 = 2375663) B2375663
theorem B8446801 : Blo 2223435 8446801 := bstep (se 2 (by rfl) ⟨3167550, by rfl⟩ : syracuseStep 8446801 = 6335101) B6335101
theorem B11262401 : Blo 2223435 11262401 := bstep (se 2 (by rfl) ⟨4223400, by rfl⟩ : syracuseStep 11262401 = 8446801) B8446801
theorem B7508267 : Blo 2223435 7508267 := bstep (se 1 (by rfl) ⟨5631200, by rfl⟩ : syracuseStep 7508267 = 11262401) B11262401
theorem B5005511 : Blo 2223435 5005511 := bstep (se 1 (by rfl) ⟨3754133, by rfl⟩ : syracuseStep 5005511 = 7508267) B7508267
theorem B3337007 : Blo 2223435 3337007 := bstep (se 1 (by rfl) ⟨2502755, by rfl⟩ : syracuseStep 3337007 = 5005511) B5005511
theorem B2224671 : Blo 2223435 2224671 := bstep (se 1 (by rfl) ⟨1668503, by rfl⟩ : syracuseStep 2224671 = 3337007) B3337007
theorem B3337013 : Blo 2223435 3337013 := bbase (se 5 (by rfl) ⟨156422, by rfl⟩ : syracuseStep 3337013 = 312845) (by norm_num)
theorem B2224675 : Blo 2223435 2224675 := bstep (se 1 (by rfl) ⟨1668506, by rfl⟩ : syracuseStep 2224675 = 3337013) B3337013
theorem B5631221 : Blo 2223435 5631221 := bbase (se 5 (by rfl) ⟨263963, by rfl⟩ : syracuseStep 5631221 = 527927) (by norm_num)
theorem B3754147 : Blo 2223435 3754147 := bstep (se 1 (by rfl) ⟨2815610, by rfl⟩ : syracuseStep 3754147 = 5631221) B5631221
theorem B5005529 : Blo 2223435 5005529 := bstep (se 2 (by rfl) ⟨1877073, by rfl⟩ : syracuseStep 5005529 = 3754147) B3754147
theorem B3337019 : Blo 2223435 3337019 := bstep (se 1 (by rfl) ⟨2502764, by rfl⟩ : syracuseStep 3337019 = 5005529) B5005529
theorem B2224679 : Blo 2223435 2224679 := bstep (se 1 (by rfl) ⟨1668509, by rfl⟩ : syracuseStep 2224679 = 3337019) B3337019
theorem B2502769 : Blo 2223435 2502769 := bbase (se 2 (by rfl) ⟨938538, by rfl⟩ : syracuseStep 2502769 = 1877077) (by norm_num)
theorem B3337025 : Blo 2223435 3337025 := bstep (se 2 (by rfl) ⟨1251384, by rfl⟩ : syracuseStep 3337025 = 2502769) B2502769
theorem B2224683 : Blo 2223435 2224683 := bstep (se 1 (by rfl) ⟨1668512, by rfl⟩ : syracuseStep 2224683 = 3337025) B3337025
theorem B2255041 : Blo 2223435 2255041 := bbase (se 2 (by rfl) ⟨845640, by rfl⟩ : syracuseStep 2255041 = 1691281) (by norm_num)
theorem B3006721 : Blo 2223435 3006721 := bstep (se 2 (by rfl) ⟨1127520, by rfl⟩ : syracuseStep 3006721 = 2255041) B2255041
theorem B4008961 : Blo 2223435 4008961 := bstep (se 2 (by rfl) ⟨1503360, by rfl⟩ : syracuseStep 4008961 = 3006721) B3006721
theorem B5345281 : Blo 2223435 5345281 := bstep (se 2 (by rfl) ⟨2004480, by rfl⟩ : syracuseStep 5345281 = 4008961) B4008961
theorem B7127041 : Blo 2223435 7127041 := bstep (se 2 (by rfl) ⟨2672640, by rfl⟩ : syracuseStep 7127041 = 5345281) B5345281
theorem B9502721 : Blo 2223435 9502721 := bstep (se 2 (by rfl) ⟨3563520, by rfl⟩ : syracuseStep 9502721 = 7127041) B7127041
theorem B6335147 : Blo 2223435 6335147 := bstep (se 1 (by rfl) ⟨4751360, by rfl⟩ : syracuseStep 6335147 = 9502721) B9502721
theorem B4223431 : Blo 2223435 4223431 := bstep (se 1 (by rfl) ⟨3167573, by rfl⟩ : syracuseStep 4223431 = 6335147) B6335147
theorem B5631241 : Blo 2223435 5631241 := bstep (se 2 (by rfl) ⟨2111715, by rfl⟩ : syracuseStep 5631241 = 4223431) B4223431
theorem B7508321 : Blo 2223435 7508321 := bstep (se 2 (by rfl) ⟨2815620, by rfl⟩ : syracuseStep 7508321 = 5631241) B5631241
theorem B5005547 : Blo 2223435 5005547 := bstep (se 1 (by rfl) ⟨3754160, by rfl⟩ : syracuseStep 5005547 = 7508321) B7508321
theorem B3337031 : Blo 2223435 3337031 := bstep (se 1 (by rfl) ⟨2502773, by rfl⟩ : syracuseStep 3337031 = 5005547) B5005547
theorem B2224687 : Blo 2223435 2224687 := bstep (se 1 (by rfl) ⟨1668515, by rfl⟩ : syracuseStep 2224687 = 3337031) B3337031
theorem B3337037 : Blo 2223435 3337037 := bbase (se 3 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 3337037 = 1251389) (by norm_num)
theorem B2224691 : Blo 2223435 2224691 := bstep (se 1 (by rfl) ⟨1668518, by rfl⟩ : syracuseStep 2224691 = 3337037) B3337037
theorem B5005565 : Blo 2223435 5005565 := bbase (se 3 (by rfl) ⟨938543, by rfl⟩ : syracuseStep 5005565 = 1877087) (by norm_num)
theorem B3337043 : Blo 2223435 3337043 := bstep (se 1 (by rfl) ⟨2502782, by rfl⟩ : syracuseStep 3337043 = 5005565) B5005565
theorem B2224695 : Blo 2223435 2224695 := bstep (se 1 (by rfl) ⟨1668521, by rfl⟩ : syracuseStep 2224695 = 3337043) B3337043
theorem B3754181 : Blo 2223435 3754181 := bbase (se 4 (by rfl) ⟨351954, by rfl⟩ : syracuseStep 3754181 = 703909) (by norm_num)
theorem B2502787 : Blo 2223435 2502787 := bstep (se 1 (by rfl) ⟨1877090, by rfl⟩ : syracuseStep 2502787 = 3754181) B3754181
theorem B3337049 : Blo 2223435 3337049 := bstep (se 2 (by rfl) ⟨1251393, by rfl⟩ : syracuseStep 3337049 = 2502787) B2502787
theorem B2224699 : Blo 2223435 2224699 := bstep (se 1 (by rfl) ⟨1668524, by rfl⟩ : syracuseStep 2224699 = 3337049) B3337049
theorem B16893845 : Blo 2223435 16893845 := bbase (se 6 (by rfl) ⟨395949, by rfl⟩ : syracuseStep 16893845 = 791899) (by norm_num)
theorem B11262563 : Blo 2223435 11262563 := bstep (se 1 (by rfl) ⟨8446922, by rfl⟩ : syracuseStep 11262563 = 16893845) B16893845
theorem B7508375 : Blo 2223435 7508375 := bstep (se 1 (by rfl) ⟨5631281, by rfl⟩ : syracuseStep 7508375 = 11262563) B11262563
theorem B5005583 : Blo 2223435 5005583 := bstep (se 1 (by rfl) ⟨3754187, by rfl⟩ : syracuseStep 5005583 = 7508375) B7508375
theorem B3337055 : Blo 2223435 3337055 := bstep (se 1 (by rfl) ⟨2502791, by rfl⟩ : syracuseStep 3337055 = 5005583) B5005583
theorem B2224703 : Blo 2223435 2224703 := bstep (se 1 (by rfl) ⟨1668527, by rfl⟩ : syracuseStep 2224703 = 3337055) B3337055
theorem B3337061 : Blo 2223435 3337061 := bbase (se 4 (by rfl) ⟨312849, by rfl⟩ : syracuseStep 3337061 = 625699) (by norm_num)
theorem B2224707 : Blo 2223435 2224707 := bstep (se 1 (by rfl) ⟨1668530, by rfl⟩ : syracuseStep 2224707 = 3337061) B3337061
theorem B4223477 : Blo 2223435 4223477 := bbase (se 5 (by rfl) ⟨197975, by rfl⟩ : syracuseStep 4223477 = 395951) (by norm_num)
theorem B2815651 : Blo 2223435 2815651 := bstep (se 1 (by rfl) ⟨2111738, by rfl⟩ : syracuseStep 2815651 = 4223477) B4223477
theorem B3754201 : Blo 2223435 3754201 := bstep (se 2 (by rfl) ⟨1407825, by rfl⟩ : syracuseStep 3754201 = 2815651) B2815651
theorem B5005601 : Blo 2223435 5005601 := bstep (se 2 (by rfl) ⟨1877100, by rfl⟩ : syracuseStep 5005601 = 3754201) B3754201
theorem B3337067 : Blo 2223435 3337067 := bstep (se 1 (by rfl) ⟨2502800, by rfl⟩ : syracuseStep 3337067 = 5005601) B5005601
theorem B2224711 : Blo 2223435 2224711 := bstep (se 1 (by rfl) ⟨1668533, by rfl⟩ : syracuseStep 2224711 = 3337067) B3337067
theorem B2502805 : Blo 2223435 2502805 := bbase (se 6 (by rfl) ⟨58659, by rfl⟩ : syracuseStep 2502805 = 117319) (by norm_num)
theorem B3337073 : Blo 2223435 3337073 := bstep (se 2 (by rfl) ⟨1251402, by rfl⟩ : syracuseStep 3337073 = 2502805) B2502805
theorem B2224715 : Blo 2223435 2224715 := bstep (se 1 (by rfl) ⟨1668536, by rfl⟩ : syracuseStep 2224715 = 3337073) B3337073
theorem B2815661 : Blo 2223435 2815661 := bbase (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) (by norm_num)
theorem B7508429 : Blo 2223435 7508429 := bstep (se 3 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 7508429 = 2815661) B2815661
theorem B5005619 : Blo 2223435 5005619 := bstep (se 1 (by rfl) ⟨3754214, by rfl⟩ : syracuseStep 5005619 = 7508429) B7508429
theorem B3337079 : Blo 2223435 3337079 := bstep (se 1 (by rfl) ⟨2502809, by rfl⟩ : syracuseStep 3337079 = 5005619) B5005619
theorem B2224719 : Blo 2223435 2224719 := bstep (se 1 (by rfl) ⟨1668539, by rfl⟩ : syracuseStep 2224719 = 3337079) B3337079
theorem B3337085 : Blo 2223435 3337085 := bbase (se 3 (by rfl) ⟨625703, by rfl⟩ : syracuseStep 3337085 = 1251407) (by norm_num)
theorem B2224723 : Blo 2223435 2224723 := bstep (se 1 (by rfl) ⟨1668542, by rfl⟩ : syracuseStep 2224723 = 3337085) B3337085
theorem B5005637 : Blo 2223435 5005637 := bbase (se 4 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 5005637 = 938557) (by norm_num)
theorem B3337091 : Blo 2223435 3337091 := bstep (se 1 (by rfl) ⟨2502818, by rfl⟩ : syracuseStep 3337091 = 5005637) B5005637
theorem B2224727 : Blo 2223435 2224727 := bstep (se 1 (by rfl) ⟨1668545, by rfl⟩ : syracuseStep 2224727 = 3337091) B3337091
theorem B11416373 : Blo 2223435 11416373 := bbase (se 5 (by rfl) ⟨535142, by rfl⟩ : syracuseStep 11416373 = 1070285) (by norm_num)
theorem B7610915 : Blo 2223435 7610915 := bstep (se 1 (by rfl) ⟨5708186, by rfl⟩ : syracuseStep 7610915 = 11416373) B11416373
theorem B5073943 : Blo 2223435 5073943 := bstep (se 1 (by rfl) ⟨3805457, by rfl⟩ : syracuseStep 5073943 = 7610915) B7610915
theorem B6765257 : Blo 2223435 6765257 := bstep (se 2 (by rfl) ⟨2536971, by rfl⟩ : syracuseStep 6765257 = 5073943) B5073943
theorem B4510171 : Blo 2223435 4510171 := bstep (se 1 (by rfl) ⟨3382628, by rfl⟩ : syracuseStep 4510171 = 6765257) B6765257
theorem B24054245 : Blo 2223435 24054245 := bstep (se 4 (by rfl) ⟨2255085, by rfl⟩ : syracuseStep 24054245 = 4510171) B4510171
theorem B16036163 : Blo 2223435 16036163 := bstep (se 1 (by rfl) ⟨12027122, by rfl⟩ : syracuseStep 16036163 = 24054245) B24054245
theorem B10690775 : Blo 2223435 10690775 := bstep (se 1 (by rfl) ⟨8018081, by rfl⟩ : syracuseStep 10690775 = 16036163) B16036163
theorem B7127183 : Blo 2223435 7127183 := bstep (se 1 (by rfl) ⟨5345387, by rfl⟩ : syracuseStep 7127183 = 10690775) B10690775
theorem B4751455 : Blo 2223435 4751455 := bstep (se 1 (by rfl) ⟨3563591, by rfl⟩ : syracuseStep 4751455 = 7127183) B7127183
theorem B6335273 : Blo 2223435 6335273 := bstep (se 2 (by rfl) ⟨2375727, by rfl⟩ : syracuseStep 6335273 = 4751455) B4751455
theorem B4223515 : Blo 2223435 4223515 := bstep (se 1 (by rfl) ⟨3167636, by rfl⟩ : syracuseStep 4223515 = 6335273) B6335273
theorem B5631353 : Blo 2223435 5631353 := bstep (se 2 (by rfl) ⟨2111757, by rfl⟩ : syracuseStep 5631353 = 4223515) B4223515
theorem B3754235 : Blo 2223435 3754235 := bstep (se 1 (by rfl) ⟨2815676, by rfl⟩ : syracuseStep 3754235 = 5631353) B5631353
theorem B2502823 : Blo 2223435 2502823 := bstep (se 1 (by rfl) ⟨1877117, by rfl⟩ : syracuseStep 2502823 = 3754235) B3754235
theorem B3337097 : Blo 2223435 3337097 := bstep (se 2 (by rfl) ⟨1251411, by rfl⟩ : syracuseStep 3337097 = 2502823) B2502823
theorem B2224731 : Blo 2223435 2224731 := bstep (se 1 (by rfl) ⟨1668548, by rfl⟩ : syracuseStep 2224731 = 3337097) B3337097
theorem B11262725 : Blo 2223435 11262725 := bbase (se 4 (by rfl) ⟨1055880, by rfl⟩ : syracuseStep 11262725 = 2111761) (by norm_num)
theorem B7508483 : Blo 2223435 7508483 := bstep (se 1 (by rfl) ⟨5631362, by rfl⟩ : syracuseStep 7508483 = 11262725) B11262725
theorem B5005655 : Blo 2223435 5005655 := bstep (se 1 (by rfl) ⟨3754241, by rfl⟩ : syracuseStep 5005655 = 7508483) B7508483
theorem B3337103 : Blo 2223435 3337103 := bstep (se 1 (by rfl) ⟨2502827, by rfl⟩ : syracuseStep 3337103 = 5005655) B5005655
theorem B2224735 : Blo 2223435 2224735 := bstep (se 1 (by rfl) ⟨1668551, by rfl⟩ : syracuseStep 2224735 = 3337103) B3337103
theorem B3337109 : Blo 2223435 3337109 := bbase (se 6 (by rfl) ⟨78213, by rfl⟩ : syracuseStep 3337109 = 156427) (by norm_num)
theorem B2224739 : Blo 2223435 2224739 := bstep (se 1 (by rfl) ⟨1668554, by rfl⟩ : syracuseStep 2224739 = 3337109) B3337109
theorem B12670613 : Blo 2223435 12670613 := bbase (se 6 (by rfl) ⟨296967, by rfl⟩ : syracuseStep 12670613 = 593935) (by norm_num)
theorem B8447075 : Blo 2223435 8447075 := bstep (se 1 (by rfl) ⟨6335306, by rfl⟩ : syracuseStep 8447075 = 12670613) B12670613
theorem B5631383 : Blo 2223435 5631383 := bstep (se 1 (by rfl) ⟨4223537, by rfl⟩ : syracuseStep 5631383 = 8447075) B8447075
theorem B3754255 : Blo 2223435 3754255 := bstep (se 1 (by rfl) ⟨2815691, by rfl⟩ : syracuseStep 3754255 = 5631383) B5631383
theorem B5005673 : Blo 2223435 5005673 := bstep (se 2 (by rfl) ⟨1877127, by rfl⟩ : syracuseStep 5005673 = 3754255) B3754255
theorem B3337115 : Blo 2223435 3337115 := bstep (se 1 (by rfl) ⟨2502836, by rfl⟩ : syracuseStep 3337115 = 5005673) B5005673
theorem B2224743 : Blo 2223435 2224743 := bstep (se 1 (by rfl) ⟨1668557, by rfl⟩ : syracuseStep 2224743 = 3337115) B3337115
theorem B2502841 : Blo 2223435 2502841 := bbase (se 2 (by rfl) ⟨938565, by rfl⟩ : syracuseStep 2502841 = 1877131) (by norm_num)
theorem B3337121 : Blo 2223435 3337121 := bstep (se 2 (by rfl) ⟨1251420, by rfl⟩ : syracuseStep 3337121 = 2502841) B2502841
theorem B2224747 : Blo 2223435 2224747 := bstep (se 1 (by rfl) ⟨1668560, by rfl⟩ : syracuseStep 2224747 = 3337121) B3337121
theorem B5708237 : Blo 2223435 5708237 := bbase (se 3 (by rfl) ⟨1070294, by rfl⟩ : syracuseStep 5708237 = 2140589) (by norm_num)
theorem B15221965 : Blo 2223435 15221965 := bstep (se 3 (by rfl) ⟨2854118, by rfl⟩ : syracuseStep 15221965 = 5708237) B5708237
theorem B20295953 : Blo 2223435 20295953 := bstep (se 2 (by rfl) ⟨7610982, by rfl⟩ : syracuseStep 20295953 = 15221965) B15221965
theorem B13530635 : Blo 2223435 13530635 := bstep (se 1 (by rfl) ⟨10147976, by rfl⟩ : syracuseStep 13530635 = 20295953) B20295953
theorem B9020423 : Blo 2223435 9020423 := bstep (se 1 (by rfl) ⟨6765317, by rfl⟩ : syracuseStep 9020423 = 13530635) B13530635
theorem B6013615 : Blo 2223435 6013615 := bstep (se 1 (by rfl) ⟨4510211, by rfl⟩ : syracuseStep 6013615 = 9020423) B9020423
theorem B8018153 : Blo 2223435 8018153 := bstep (se 2 (by rfl) ⟨3006807, by rfl⟩ : syracuseStep 8018153 = 6013615) B6013615
theorem B5345435 : Blo 2223435 5345435 := bstep (se 1 (by rfl) ⟨4009076, by rfl⟩ : syracuseStep 5345435 = 8018153) B8018153
theorem B3563623 : Blo 2223435 3563623 := bstep (se 1 (by rfl) ⟨2672717, by rfl⟩ : syracuseStep 3563623 = 5345435) B5345435
theorem B4751497 : Blo 2223435 4751497 := bstep (se 2 (by rfl) ⟨1781811, by rfl⟩ : syracuseStep 4751497 = 3563623) B3563623
theorem B6335329 : Blo 2223435 6335329 := bstep (se 2 (by rfl) ⟨2375748, by rfl⟩ : syracuseStep 6335329 = 4751497) B4751497
theorem B8447105 : Blo 2223435 8447105 := bstep (se 2 (by rfl) ⟨3167664, by rfl⟩ : syracuseStep 8447105 = 6335329) B6335329
theorem B5631403 : Blo 2223435 5631403 := bstep (se 1 (by rfl) ⟨4223552, by rfl⟩ : syracuseStep 5631403 = 8447105) B8447105
theorem B7508537 : Blo 2223435 7508537 := bstep (se 2 (by rfl) ⟨2815701, by rfl⟩ : syracuseStep 7508537 = 5631403) B5631403
theorem B5005691 : Blo 2223435 5005691 := bstep (se 1 (by rfl) ⟨3754268, by rfl⟩ : syracuseStep 5005691 = 7508537) B7508537
theorem B3337127 : Blo 2223435 3337127 := bstep (se 1 (by rfl) ⟨2502845, by rfl⟩ : syracuseStep 3337127 = 5005691) B5005691
theorem B2224751 : Blo 2223435 2224751 := bstep (se 1 (by rfl) ⟨1668563, by rfl⟩ : syracuseStep 2224751 = 3337127) B3337127
theorem B3337133 : Blo 2223435 3337133 := bbase (se 3 (by rfl) ⟨625712, by rfl⟩ : syracuseStep 3337133 = 1251425) (by norm_num)
theorem B2224755 : Blo 2223435 2224755 := bstep (se 1 (by rfl) ⟨1668566, by rfl⟩ : syracuseStep 2224755 = 3337133) B3337133
theorem B5005709 : Blo 2223435 5005709 := bbase (se 3 (by rfl) ⟨938570, by rfl⟩ : syracuseStep 5005709 = 1877141) (by norm_num)
theorem B3337139 : Blo 2223435 3337139 := bstep (se 1 (by rfl) ⟨2502854, by rfl⟩ : syracuseStep 3337139 = 5005709) B5005709
theorem B2224759 : Blo 2223435 2224759 := bstep (se 1 (by rfl) ⟨1668569, by rfl⟩ : syracuseStep 2224759 = 3337139) B3337139
theorem B2815717 : Blo 2223435 2815717 := bbase (se 4 (by rfl) ⟨263973, by rfl⟩ : syracuseStep 2815717 = 527947) (by norm_num)
theorem B3754289 : Blo 2223435 3754289 := bstep (se 2 (by rfl) ⟨1407858, by rfl⟩ : syracuseStep 3754289 = 2815717) B2815717
theorem B2502859 : Blo 2223435 2502859 := bstep (se 1 (by rfl) ⟨1877144, by rfl⟩ : syracuseStep 2502859 = 3754289) B3754289
theorem B3337145 : Blo 2223435 3337145 := bstep (se 2 (by rfl) ⟨1251429, by rfl⟩ : syracuseStep 3337145 = 2502859) B2502859
theorem B2224763 : Blo 2223435 2224763 := bstep (se 1 (by rfl) ⟨1668572, by rfl⟩ : syracuseStep 2224763 = 3337145) B3337145
theorem B9020485 : Blo 2223435 9020485 := bbase (se 4 (by rfl) ⟨845670, by rfl⟩ : syracuseStep 9020485 = 1691341) (by norm_num)
theorem B12027313 : Blo 2223435 12027313 := bstep (se 2 (by rfl) ⟨4510242, by rfl⟩ : syracuseStep 12027313 = 9020485) B9020485
theorem B16036417 : Blo 2223435 16036417 := bstep (se 2 (by rfl) ⟨6013656, by rfl⟩ : syracuseStep 16036417 = 12027313) B12027313
theorem B21381889 : Blo 2223435 21381889 := bstep (se 2 (by rfl) ⟨8018208, by rfl⟩ : syracuseStep 21381889 = 16036417) B16036417
theorem B28509185 : Blo 2223435 28509185 := bstep (se 2 (by rfl) ⟨10690944, by rfl⟩ : syracuseStep 28509185 = 21381889) B21381889
theorem B19006123 : Blo 2223435 19006123 := bstep (se 1 (by rfl) ⟨14254592, by rfl⟩ : syracuseStep 19006123 = 28509185) B28509185
theorem B25341497 : Blo 2223435 25341497 := bstep (se 2 (by rfl) ⟨9503061, by rfl⟩ : syracuseStep 25341497 = 19006123) B19006123
theorem B16894331 : Blo 2223435 16894331 := bstep (se 1 (by rfl) ⟨12670748, by rfl⟩ : syracuseStep 16894331 = 25341497) B25341497
theorem B11262887 : Blo 2223435 11262887 := bstep (se 1 (by rfl) ⟨8447165, by rfl⟩ : syracuseStep 11262887 = 16894331) B16894331
theorem B7508591 : Blo 2223435 7508591 := bstep (se 1 (by rfl) ⟨5631443, by rfl⟩ : syracuseStep 7508591 = 11262887) B11262887
theorem B5005727 : Blo 2223435 5005727 := bstep (se 1 (by rfl) ⟨3754295, by rfl⟩ : syracuseStep 5005727 = 7508591) B7508591
theorem B3337151 : Blo 2223435 3337151 := bstep (se 1 (by rfl) ⟨2502863, by rfl⟩ : syracuseStep 3337151 = 5005727) B5005727
theorem B2224767 : Blo 2223435 2224767 := bstep (se 1 (by rfl) ⟨1668575, by rfl⟩ : syracuseStep 2224767 = 3337151) B3337151
theorem B3337157 : Blo 2223435 3337157 := bbase (se 4 (by rfl) ⟨312858, by rfl⟩ : syracuseStep 3337157 = 625717) (by norm_num)
theorem B2224771 : Blo 2223435 2224771 := bstep (se 1 (by rfl) ⟨1668578, by rfl⟩ : syracuseStep 2224771 = 3337157) B3337157
theorem B3754309 : Blo 2223435 3754309 := bbase (se 4 (by rfl) ⟨351966, by rfl⟩ : syracuseStep 3754309 = 703933) (by norm_num)
theorem B5005745 : Blo 2223435 5005745 := bstep (se 2 (by rfl) ⟨1877154, by rfl⟩ : syracuseStep 5005745 = 3754309) B3754309
theorem B3337163 : Blo 2223435 3337163 := bstep (se 1 (by rfl) ⟨2502872, by rfl⟩ : syracuseStep 3337163 = 5005745) B5005745
theorem B2224775 : Blo 2223435 2224775 := bstep (se 1 (by rfl) ⟨1668581, by rfl⟩ : syracuseStep 2224775 = 3337163) B3337163
theorem B2502877 : Blo 2223435 2502877 := bbase (se 3 (by rfl) ⟨469289, by rfl⟩ : syracuseStep 2502877 = 938579) (by norm_num)
theorem B3337169 : Blo 2223435 3337169 := bstep (se 2 (by rfl) ⟨1251438, by rfl⟩ : syracuseStep 3337169 = 2502877) B2502877
theorem B2224779 : Blo 2223435 2224779 := bstep (se 1 (by rfl) ⟨1668584, by rfl⟩ : syracuseStep 2224779 = 3337169) B3337169
theorem B7508645 : Blo 2223435 7508645 := bbase (se 4 (by rfl) ⟨703935, by rfl⟩ : syracuseStep 7508645 = 1407871) (by norm_num)
theorem B5005763 : Blo 2223435 5005763 := bstep (se 1 (by rfl) ⟨3754322, by rfl⟩ : syracuseStep 5005763 = 7508645) B7508645
theorem B3337175 : Blo 2223435 3337175 := bstep (se 1 (by rfl) ⟨2502881, by rfl⟩ : syracuseStep 3337175 = 5005763) B5005763
theorem B2224783 : Blo 2223435 2224783 := bstep (se 1 (by rfl) ⟨1668587, by rfl⟩ : syracuseStep 2224783 = 3337175) B3337175
theorem B3337181 : Blo 2223435 3337181 := bbase (se 3 (by rfl) ⟨625721, by rfl⟩ : syracuseStep 3337181 = 1251443) (by norm_num)
theorem B2224787 : Blo 2223435 2224787 := bstep (se 1 (by rfl) ⟨1668590, by rfl⟩ : syracuseStep 2224787 = 3337181) B3337181
theorem B5005781 : Blo 2223435 5005781 := bbase (se 7 (by rfl) ⟨58661, by rfl⟩ : syracuseStep 5005781 = 117323) (by norm_num)
theorem B3337187 : Blo 2223435 3337187 := bstep (se 1 (by rfl) ⟨2502890, by rfl⟩ : syracuseStep 3337187 = 5005781) B5005781
theorem B2224791 : Blo 2223435 2224791 := bstep (se 1 (by rfl) ⟨1668593, by rfl⟩ : syracuseStep 2224791 = 3337187) B3337187
theorem B13530901 : Blo 2223435 13530901 := bbase (se 6 (by rfl) ⟨317130, by rfl⟩ : syracuseStep 13530901 = 634261) (by norm_num)
theorem B18041201 : Blo 2223435 18041201 := bstep (se 2 (by rfl) ⟨6765450, by rfl⟩ : syracuseStep 18041201 = 13530901) B13530901
theorem B12027467 : Blo 2223435 12027467 := bstep (se 1 (by rfl) ⟨9020600, by rfl⟩ : syracuseStep 12027467 = 18041201) B18041201
theorem B32073245 : Blo 2223435 32073245 := bstep (se 3 (by rfl) ⟨6013733, by rfl⟩ : syracuseStep 32073245 = 12027467) B12027467
theorem B21382163 : Blo 2223435 21382163 := bstep (se 1 (by rfl) ⟨16036622, by rfl⟩ : syracuseStep 21382163 = 32073245) B32073245
theorem B14254775 : Blo 2223435 14254775 := bstep (se 1 (by rfl) ⟨10691081, by rfl⟩ : syracuseStep 14254775 = 21382163) B21382163
theorem B9503183 : Blo 2223435 9503183 := bstep (se 1 (by rfl) ⟨7127387, by rfl⟩ : syracuseStep 9503183 = 14254775) B14254775
theorem B6335455 : Blo 2223435 6335455 := bstep (se 1 (by rfl) ⟨4751591, by rfl⟩ : syracuseStep 6335455 = 9503183) B9503183
theorem B8447273 : Blo 2223435 8447273 := bstep (se 2 (by rfl) ⟨3167727, by rfl⟩ : syracuseStep 8447273 = 6335455) B6335455
theorem B5631515 : Blo 2223435 5631515 := bstep (se 1 (by rfl) ⟨4223636, by rfl⟩ : syracuseStep 5631515 = 8447273) B8447273
theorem B3754343 : Blo 2223435 3754343 := bstep (se 1 (by rfl) ⟨2815757, by rfl⟩ : syracuseStep 3754343 = 5631515) B5631515
theorem B2502895 : Blo 2223435 2502895 := bstep (se 1 (by rfl) ⟨1877171, by rfl⟩ : syracuseStep 2502895 = 3754343) B3754343
theorem B3337193 : Blo 2223435 3337193 := bstep (se 2 (by rfl) ⟨1251447, by rfl⟩ : syracuseStep 3337193 = 2502895) B2502895
theorem B2224795 : Blo 2223435 2224795 := bstep (se 1 (by rfl) ⟨1668596, by rfl⟩ : syracuseStep 2224795 = 3337193) B3337193
theorem B4281269 : Blo 2223435 4281269 := bbase (se 5 (by rfl) ⟨200684, by rfl⟩ : syracuseStep 4281269 = 401369) (by norm_num)
theorem B11416717 : Blo 2223435 11416717 := bstep (se 3 (by rfl) ⟨2140634, by rfl⟩ : syracuseStep 11416717 = 4281269) B4281269
theorem B60889157 : Blo 2223435 60889157 := bstep (se 4 (by rfl) ⟨5708358, by rfl⟩ : syracuseStep 60889157 = 11416717) B11416717
theorem B40592771 : Blo 2223435 40592771 := bstep (se 1 (by rfl) ⟨30444578, by rfl⟩ : syracuseStep 40592771 = 60889157) B60889157
theorem B27061847 : Blo 2223435 27061847 := bstep (se 1 (by rfl) ⟨20296385, by rfl⟩ : syracuseStep 27061847 = 40592771) B40592771
theorem B18041231 : Blo 2223435 18041231 := bstep (se 1 (by rfl) ⟨13530923, by rfl⟩ : syracuseStep 18041231 = 27061847) B27061847
theorem B12027487 : Blo 2223435 12027487 := bstep (se 1 (by rfl) ⟨9020615, by rfl⟩ : syracuseStep 12027487 = 18041231) B18041231
theorem B16036649 : Blo 2223435 16036649 := bstep (se 2 (by rfl) ⟨6013743, by rfl⟩ : syracuseStep 16036649 = 12027487) B12027487
theorem B10691099 : Blo 2223435 10691099 := bstep (se 1 (by rfl) ⟨8018324, by rfl⟩ : syracuseStep 10691099 = 16036649) B16036649
theorem B7127399 : Blo 2223435 7127399 := bstep (se 1 (by rfl) ⟨5345549, by rfl⟩ : syracuseStep 7127399 = 10691099) B10691099
theorem B19006397 : Blo 2223435 19006397 := bstep (se 3 (by rfl) ⟨3563699, by rfl⟩ : syracuseStep 19006397 = 7127399) B7127399
theorem B12670931 : Blo 2223435 12670931 := bstep (se 1 (by rfl) ⟨9503198, by rfl⟩ : syracuseStep 12670931 = 19006397) B19006397
theorem B8447287 : Blo 2223435 8447287 := bstep (se 1 (by rfl) ⟨6335465, by rfl⟩ : syracuseStep 8447287 = 12670931) B12670931
theorem B11263049 : Blo 2223435 11263049 := bstep (se 2 (by rfl) ⟨4223643, by rfl⟩ : syracuseStep 11263049 = 8447287) B8447287
theorem B7508699 : Blo 2223435 7508699 := bstep (se 1 (by rfl) ⟨5631524, by rfl⟩ : syracuseStep 7508699 = 11263049) B11263049
theorem B5005799 : Blo 2223435 5005799 := bstep (se 1 (by rfl) ⟨3754349, by rfl⟩ : syracuseStep 5005799 = 7508699) B7508699
theorem B3337199 : Blo 2223435 3337199 := bstep (se 1 (by rfl) ⟨2502899, by rfl⟩ : syracuseStep 3337199 = 5005799) B5005799
theorem B2224799 : Blo 2223435 2224799 := bstep (se 1 (by rfl) ⟨1668599, by rfl⟩ : syracuseStep 2224799 = 3337199) B3337199
theorem B3337205 : Blo 2223435 3337205 := bbase (se 5 (by rfl) ⟨156431, by rfl⟩ : syracuseStep 3337205 = 312863) (by norm_num)
theorem B2224803 : Blo 2223435 2224803 := bstep (se 1 (by rfl) ⟨1668602, by rfl⟩ : syracuseStep 2224803 = 3337205) B3337205
theorem B2672785 : Blo 2223435 2672785 := bbase (se 2 (by rfl) ⟨1002294, by rfl⟩ : syracuseStep 2672785 = 2004589) (by norm_num)
theorem B3563713 : Blo 2223435 3563713 := bstep (se 2 (by rfl) ⟨1336392, by rfl⟩ : syracuseStep 3563713 = 2672785) B2672785
theorem B4751617 : Blo 2223435 4751617 := bstep (se 2 (by rfl) ⟨1781856, by rfl⟩ : syracuseStep 4751617 = 3563713) B3563713
theorem B6335489 : Blo 2223435 6335489 := bstep (se 2 (by rfl) ⟨2375808, by rfl⟩ : syracuseStep 6335489 = 4751617) B4751617
theorem B4223659 : Blo 2223435 4223659 := bstep (se 1 (by rfl) ⟨3167744, by rfl⟩ : syracuseStep 4223659 = 6335489) B6335489
theorem B5631545 : Blo 2223435 5631545 := bstep (se 2 (by rfl) ⟨2111829, by rfl⟩ : syracuseStep 5631545 = 4223659) B4223659
theorem B3754363 : Blo 2223435 3754363 := bstep (se 1 (by rfl) ⟨2815772, by rfl⟩ : syracuseStep 3754363 = 5631545) B5631545
theorem B5005817 : Blo 2223435 5005817 := bstep (se 2 (by rfl) ⟨1877181, by rfl⟩ : syracuseStep 5005817 = 3754363) B3754363
theorem B3337211 : Blo 2223435 3337211 := bstep (se 1 (by rfl) ⟨2502908, by rfl⟩ : syracuseStep 3337211 = 5005817) B5005817
theorem B2224807 : Blo 2223435 2224807 := bstep (se 1 (by rfl) ⟨1668605, by rfl⟩ : syracuseStep 2224807 = 3337211) B3337211
theorem B2502913 : Blo 2223435 2502913 := bbase (se 2 (by rfl) ⟨938592, by rfl⟩ : syracuseStep 2502913 = 1877185) (by norm_num)
theorem B3337217 : Blo 2223435 3337217 := bstep (se 2 (by rfl) ⟨1251456, by rfl⟩ : syracuseStep 3337217 = 2502913) B2502913
theorem B2224811 : Blo 2223435 2224811 := bstep (se 1 (by rfl) ⟨1668608, by rfl⟩ : syracuseStep 2224811 = 3337217) B3337217
theorem B5631565 : Blo 2223435 5631565 := bbase (se 3 (by rfl) ⟨1055918, by rfl⟩ : syracuseStep 5631565 = 2111837) (by norm_num)
theorem B7508753 : Blo 2223435 7508753 := bstep (se 2 (by rfl) ⟨2815782, by rfl⟩ : syracuseStep 7508753 = 5631565) B5631565
theorem B5005835 : Blo 2223435 5005835 := bstep (se 1 (by rfl) ⟨3754376, by rfl⟩ : syracuseStep 5005835 = 7508753) B7508753
theorem B3337223 : Blo 2223435 3337223 := bstep (se 1 (by rfl) ⟨2502917, by rfl⟩ : syracuseStep 3337223 = 5005835) B5005835
theorem B2224815 : Blo 2223435 2224815 := bstep (se 1 (by rfl) ⟨1668611, by rfl⟩ : syracuseStep 2224815 = 3337223) B3337223
theorem B3337229 : Blo 2223435 3337229 := bbase (se 3 (by rfl) ⟨625730, by rfl⟩ : syracuseStep 3337229 = 1251461) (by norm_num)
theorem B2224819 : Blo 2223435 2224819 := bstep (se 1 (by rfl) ⟨1668614, by rfl⟩ : syracuseStep 2224819 = 3337229) B3337229
theorem B5005853 : Blo 2223435 5005853 := bbase (se 3 (by rfl) ⟨938597, by rfl⟩ : syracuseStep 5005853 = 1877195) (by norm_num)
theorem B3337235 : Blo 2223435 3337235 := bstep (se 1 (by rfl) ⟨2502926, by rfl⟩ : syracuseStep 3337235 = 5005853) B5005853
theorem B2224823 : Blo 2223435 2224823 := bstep (se 1 (by rfl) ⟨1668617, by rfl⟩ : syracuseStep 2224823 = 3337235) B3337235
theorem B3754397 : Blo 2223435 3754397 := bbase (se 3 (by rfl) ⟨703949, by rfl⟩ : syracuseStep 3754397 = 1407899) (by norm_num)
theorem B2502931 : Blo 2223435 2502931 := bstep (se 1 (by rfl) ⟨1877198, by rfl⟩ : syracuseStep 2502931 = 3754397) B3754397
theorem B3337241 : Blo 2223435 3337241 := bstep (se 2 (by rfl) ⟨1251465, by rfl⟩ : syracuseStep 3337241 = 2502931) B2502931
theorem B2224827 : Blo 2223435 2224827 := bstep (se 1 (by rfl) ⟨1668620, by rfl⟩ : syracuseStep 2224827 = 3337241) B3337241
theorem B2408249 : Blo 2223435 2408249 := bbase (se 2 (by rfl) ⟨903093, by rfl⟩ : syracuseStep 2408249 = 1806187) (by norm_num)
theorem B6421997 : Blo 2223435 6421997 := bstep (se 3 (by rfl) ⟨1204124, by rfl⟩ : syracuseStep 6421997 = 2408249) B2408249
theorem B4281331 : Blo 2223435 4281331 := bstep (se 1 (by rfl) ⟨3210998, by rfl⟩ : syracuseStep 4281331 = 6421997) B6421997
theorem B5708441 : Blo 2223435 5708441 := bstep (se 2 (by rfl) ⟨2140665, by rfl⟩ : syracuseStep 5708441 = 4281331) B4281331
theorem B3805627 : Blo 2223435 3805627 := bstep (se 1 (by rfl) ⟨2854220, by rfl⟩ : syracuseStep 3805627 = 5708441) B5708441
theorem B5074169 : Blo 2223435 5074169 := bstep (se 2 (by rfl) ⟨1902813, by rfl⟩ : syracuseStep 5074169 = 3805627) B3805627
theorem B54124469 : Blo 2223435 54124469 := bstep (se 5 (by rfl) ⟨2537084, by rfl⟩ : syracuseStep 54124469 = 5074169) B5074169
theorem B36082979 : Blo 2223435 36082979 := bstep (se 1 (by rfl) ⟨27062234, by rfl⟩ : syracuseStep 36082979 = 54124469) B54124469
theorem B24055319 : Blo 2223435 24055319 := bstep (se 1 (by rfl) ⟨18041489, by rfl⟩ : syracuseStep 24055319 = 36082979) B36082979
theorem B16036879 : Blo 2223435 16036879 := bstep (se 1 (by rfl) ⟨12027659, by rfl⟩ : syracuseStep 16036879 = 24055319) B24055319
theorem B21382505 : Blo 2223435 21382505 := bstep (se 2 (by rfl) ⟨8018439, by rfl⟩ : syracuseStep 21382505 = 16036879) B16036879
theorem B14255003 : Blo 2223435 14255003 := bstep (se 1 (by rfl) ⟨10691252, by rfl⟩ : syracuseStep 14255003 = 21382505) B21382505
theorem B9503335 : Blo 2223435 9503335 := bstep (se 1 (by rfl) ⟨7127501, by rfl⟩ : syracuseStep 9503335 = 14255003) B14255003
theorem B12671113 : Blo 2223435 12671113 := bstep (se 2 (by rfl) ⟨4751667, by rfl⟩ : syracuseStep 12671113 = 9503335) B9503335
theorem B16894817 : Blo 2223435 16894817 := bstep (se 2 (by rfl) ⟨6335556, by rfl⟩ : syracuseStep 16894817 = 12671113) B12671113
theorem B11263211 : Blo 2223435 11263211 := bstep (se 1 (by rfl) ⟨8447408, by rfl⟩ : syracuseStep 11263211 = 16894817) B16894817
theorem B7508807 : Blo 2223435 7508807 := bstep (se 1 (by rfl) ⟨5631605, by rfl⟩ : syracuseStep 7508807 = 11263211) B11263211
theorem B5005871 : Blo 2223435 5005871 := bstep (se 1 (by rfl) ⟨3754403, by rfl⟩ : syracuseStep 5005871 = 7508807) B7508807
theorem B3337247 : Blo 2223435 3337247 := bstep (se 1 (by rfl) ⟨2502935, by rfl⟩ : syracuseStep 3337247 = 5005871) B5005871
theorem B2224831 : Blo 2223435 2224831 := bstep (se 1 (by rfl) ⟨1668623, by rfl⟩ : syracuseStep 2224831 = 3337247) B3337247
theorem B3337253 : Blo 2223435 3337253 := bbase (se 4 (by rfl) ⟨312867, by rfl⟩ : syracuseStep 3337253 = 625735) (by norm_num)
theorem B2224835 : Blo 2223435 2224835 := bstep (se 1 (by rfl) ⟨1668626, by rfl⟩ : syracuseStep 2224835 = 3337253) B3337253
theorem B2815813 : Blo 2223435 2815813 := bbase (se 4 (by rfl) ⟨263982, by rfl⟩ : syracuseStep 2815813 = 527965) (by norm_num)
theorem B3754417 : Blo 2223435 3754417 := bstep (se 2 (by rfl) ⟨1407906, by rfl⟩ : syracuseStep 3754417 = 2815813) B2815813
theorem B5005889 : Blo 2223435 5005889 := bstep (se 2 (by rfl) ⟨1877208, by rfl⟩ : syracuseStep 5005889 = 3754417) B3754417
theorem B3337259 : Blo 2223435 3337259 := bstep (se 1 (by rfl) ⟨2502944, by rfl⟩ : syracuseStep 3337259 = 5005889) B5005889
theorem B2224839 : Blo 2223435 2224839 := bstep (se 1 (by rfl) ⟨1668629, by rfl⟩ : syracuseStep 2224839 = 3337259) B3337259
theorem B2502949 : Blo 2223435 2502949 := bbase (se 4 (by rfl) ⟨234651, by rfl⟩ : syracuseStep 2502949 = 469303) (by norm_num)
theorem B3337265 : Blo 2223435 3337265 := bstep (se 2 (by rfl) ⟨1251474, by rfl⟩ : syracuseStep 3337265 = 2502949) B2502949
theorem B2224843 : Blo 2223435 2224843 := bstep (se 1 (by rfl) ⟨1668632, by rfl⟩ : syracuseStep 2224843 = 3337265) B3337265
theorem B2672833 : Blo 2223435 2672833 := bbase (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) (by norm_num)
theorem B3563777 : Blo 2223435 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B9503405 : Blo 2223435 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B6335603 : Blo 2223435 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B4223735 : Blo 2223435 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B2815823 : Blo 2223435 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B7508861 : Blo 2223435 7508861 := bstep (se 3 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 7508861 = 2815823) B2815823
theorem B5005907 : Blo 2223435 5005907 := bstep (se 1 (by rfl) ⟨3754430, by rfl⟩ : syracuseStep 5005907 = 7508861) B7508861
theorem B3337271 : Blo 2223435 3337271 := bstep (se 1 (by rfl) ⟨2502953, by rfl⟩ : syracuseStep 3337271 = 5005907) B5005907
theorem B2224847 : Blo 2223435 2224847 := bstep (se 1 (by rfl) ⟨1668635, by rfl⟩ : syracuseStep 2224847 = 3337271) B3337271
theorem B3337277 : Blo 2223435 3337277 := bbase (se 3 (by rfl) ⟨625739, by rfl⟩ : syracuseStep 3337277 = 1251479) (by norm_num)
theorem B2224851 : Blo 2223435 2224851 := bstep (se 1 (by rfl) ⟨1668638, by rfl⟩ : syracuseStep 2224851 = 3337277) B3337277
theorem B5005925 : Blo 2223435 5005925 := bbase (se 4 (by rfl) ⟨469305, by rfl⟩ : syracuseStep 5005925 = 938611) (by norm_num)
theorem B3337283 : Blo 2223435 3337283 := bstep (se 1 (by rfl) ⟨2502962, by rfl⟩ : syracuseStep 3337283 = 5005925) B5005925
theorem B2224855 : Blo 2223435 2224855 := bstep (se 1 (by rfl) ⟨1668641, by rfl⟩ : syracuseStep 2224855 = 3337283) B3337283
theorem B5631677 : Blo 2223435 5631677 := bbase (se 3 (by rfl) ⟨1055939, by rfl⟩ : syracuseStep 5631677 = 2111879) (by norm_num)
theorem B3754451 : Blo 2223435 3754451 := bstep (se 1 (by rfl) ⟨2815838, by rfl⟩ : syracuseStep 3754451 = 5631677) B5631677
theorem B2502967 : Blo 2223435 2502967 := bstep (se 1 (by rfl) ⟨1877225, by rfl⟩ : syracuseStep 2502967 = 3754451) B3754451
theorem B3337289 : Blo 2223435 3337289 := bstep (se 2 (by rfl) ⟨1251483, by rfl⟩ : syracuseStep 3337289 = 2502967) B2502967
theorem B2224859 : Blo 2223435 2224859 := bstep (se 1 (by rfl) ⟨1668644, by rfl⟩ : syracuseStep 2224859 = 3337289) B3337289
theorem B4223765 : Blo 2223435 4223765 := bbase (se 6 (by rfl) ⟨98994, by rfl⟩ : syracuseStep 4223765 = 197989) (by norm_num)
theorem B11263373 : Blo 2223435 11263373 := bstep (se 3 (by rfl) ⟨2111882, by rfl⟩ : syracuseStep 11263373 = 4223765) B4223765
theorem B7508915 : Blo 2223435 7508915 := bstep (se 1 (by rfl) ⟨5631686, by rfl⟩ : syracuseStep 7508915 = 11263373) B11263373
theorem B5005943 : Blo 2223435 5005943 := bstep (se 1 (by rfl) ⟨3754457, by rfl⟩ : syracuseStep 5005943 = 7508915) B7508915
theorem B3337295 : Blo 2223435 3337295 := bstep (se 1 (by rfl) ⟨2502971, by rfl⟩ : syracuseStep 3337295 = 5005943) B5005943
theorem B2224863 : Blo 2223435 2224863 := bstep (se 1 (by rfl) ⟨1668647, by rfl⟩ : syracuseStep 2224863 = 3337295) B3337295
theorem B3337301 : Blo 2223435 3337301 := bbase (se 8 (by rfl) ⟨19554, by rfl⟩ : syracuseStep 3337301 = 39109) (by norm_num)
theorem B2224867 : Blo 2223435 2224867 := bstep (se 1 (by rfl) ⟨1668650, by rfl⟩ : syracuseStep 2224867 = 3337301) B3337301
theorem B2854273 : Blo 2223435 2854273 := bbase (se 2 (by rfl) ⟨1070352, by rfl⟩ : syracuseStep 2854273 = 2140705) (by norm_num)
theorem B3805697 : Blo 2223435 3805697 := bstep (se 2 (by rfl) ⟨1427136, by rfl⟩ : syracuseStep 3805697 = 2854273) B2854273
theorem B2537131 : Blo 2223435 2537131 := bstep (se 1 (by rfl) ⟨1902848, by rfl⟩ : syracuseStep 2537131 = 3805697) B3805697
theorem B3382841 : Blo 2223435 3382841 := bstep (se 2 (by rfl) ⟨1268565, by rfl⟩ : syracuseStep 3382841 = 2537131) B2537131
theorem B9020909 : Blo 2223435 9020909 := bstep (se 3 (by rfl) ⟨1691420, by rfl⟩ : syracuseStep 9020909 = 3382841) B3382841
theorem B6013939 : Blo 2223435 6013939 := bstep (se 1 (by rfl) ⟨4510454, by rfl⟩ : syracuseStep 6013939 = 9020909) B9020909
theorem B8018585 : Blo 2223435 8018585 := bstep (se 2 (by rfl) ⟨3006969, by rfl⟩ : syracuseStep 8018585 = 6013939) B6013939
theorem B5345723 : Blo 2223435 5345723 := bstep (se 1 (by rfl) ⟨4009292, by rfl⟩ : syracuseStep 5345723 = 8018585) B8018585
theorem B14255261 : Blo 2223435 14255261 := bstep (se 3 (by rfl) ⟨2672861, by rfl⟩ : syracuseStep 14255261 = 5345723) B5345723
theorem B9503507 : Blo 2223435 9503507 := bstep (se 1 (by rfl) ⟨7127630, by rfl⟩ : syracuseStep 9503507 = 14255261) B14255261
theorem B6335671 : Blo 2223435 6335671 := bstep (se 1 (by rfl) ⟨4751753, by rfl⟩ : syracuseStep 6335671 = 9503507) B9503507
theorem B8447561 : Blo 2223435 8447561 := bstep (se 2 (by rfl) ⟨3167835, by rfl⟩ : syracuseStep 8447561 = 6335671) B6335671
theorem B5631707 : Blo 2223435 5631707 := bstep (se 1 (by rfl) ⟨4223780, by rfl⟩ : syracuseStep 5631707 = 8447561) B8447561
theorem B3754471 : Blo 2223435 3754471 := bstep (se 1 (by rfl) ⟨2815853, by rfl⟩ : syracuseStep 3754471 = 5631707) B5631707
theorem B5005961 : Blo 2223435 5005961 := bstep (se 2 (by rfl) ⟨1877235, by rfl⟩ : syracuseStep 5005961 = 3754471) B3754471
theorem B3337307 : Blo 2223435 3337307 := bstep (se 1 (by rfl) ⟨2502980, by rfl⟩ : syracuseStep 3337307 = 5005961) B5005961
theorem B2224871 : Blo 2223435 2224871 := bstep (se 1 (by rfl) ⟨1668653, by rfl⟩ : syracuseStep 2224871 = 3337307) B3337307
theorem B2502985 : Blo 2223435 2502985 := bbase (se 2 (by rfl) ⟨938619, by rfl⟩ : syracuseStep 2502985 = 1877239) (by norm_num)
theorem B3337313 : Blo 2223435 3337313 := bstep (se 2 (by rfl) ⟨1251492, by rfl⟩ : syracuseStep 3337313 = 2502985) B2502985
theorem B2224875 : Blo 2223435 2224875 := bstep (se 1 (by rfl) ⟨1668656, by rfl⟩ : syracuseStep 2224875 = 3337313) B3337313
theorem B3805709 : Blo 2223435 3805709 := bbase (se 3 (by rfl) ⟨713570, by rfl⟩ : syracuseStep 3805709 = 1427141) (by norm_num)
theorem B40594229 : Blo 2223435 40594229 := bstep (se 5 (by rfl) ⟨1902854, by rfl⟩ : syracuseStep 40594229 = 3805709) B3805709
theorem B27062819 : Blo 2223435 27062819 := bstep (se 1 (by rfl) ⟨20297114, by rfl⟩ : syracuseStep 27062819 = 40594229) B40594229
theorem B18041879 : Blo 2223435 18041879 := bstep (se 1 (by rfl) ⟨13531409, by rfl⟩ : syracuseStep 18041879 = 27062819) B27062819
theorem B48111677 : Blo 2223435 48111677 := bstep (se 3 (by rfl) ⟨9020939, by rfl⟩ : syracuseStep 48111677 = 18041879) B18041879
theorem B32074451 : Blo 2223435 32074451 := bstep (se 1 (by rfl) ⟨24055838, by rfl⟩ : syracuseStep 32074451 = 48111677) B48111677
theorem B21382967 : Blo 2223435 21382967 := bstep (se 1 (by rfl) ⟨16037225, by rfl⟩ : syracuseStep 21382967 = 32074451) B32074451
theorem B14255311 : Blo 2223435 14255311 := bstep (se 1 (by rfl) ⟨10691483, by rfl⟩ : syracuseStep 14255311 = 21382967) B21382967
theorem B19007081 : Blo 2223435 19007081 := bstep (se 2 (by rfl) ⟨7127655, by rfl⟩ : syracuseStep 19007081 = 14255311) B14255311
theorem B12671387 : Blo 2223435 12671387 := bstep (se 1 (by rfl) ⟨9503540, by rfl⟩ : syracuseStep 12671387 = 19007081) B19007081
theorem B8447591 : Blo 2223435 8447591 := bstep (se 1 (by rfl) ⟨6335693, by rfl⟩ : syracuseStep 8447591 = 12671387) B12671387
theorem B5631727 : Blo 2223435 5631727 := bstep (se 1 (by rfl) ⟨4223795, by rfl⟩ : syracuseStep 5631727 = 8447591) B8447591
theorem B7508969 : Blo 2223435 7508969 := bstep (se 2 (by rfl) ⟨2815863, by rfl⟩ : syracuseStep 7508969 = 5631727) B5631727
theorem B5005979 : Blo 2223435 5005979 := bstep (se 1 (by rfl) ⟨3754484, by rfl⟩ : syracuseStep 5005979 = 7508969) B7508969
theorem B3337319 : Blo 2223435 3337319 := bstep (se 1 (by rfl) ⟨2502989, by rfl⟩ : syracuseStep 3337319 = 5005979) B5005979
theorem B2224879 : Blo 2223435 2224879 := bstep (se 1 (by rfl) ⟨1668659, by rfl⟩ : syracuseStep 2224879 = 3337319) B3337319
theorem B3337325 : Blo 2223435 3337325 := bbase (se 3 (by rfl) ⟨625748, by rfl⟩ : syracuseStep 3337325 = 1251497) (by norm_num)
theorem B2224883 : Blo 2223435 2224883 := bstep (se 1 (by rfl) ⟨1668662, by rfl⟩ : syracuseStep 2224883 = 3337325) B3337325
theorem B5005997 : Blo 2223435 5005997 := bbase (se 3 (by rfl) ⟨938624, by rfl⟩ : syracuseStep 5005997 = 1877249) (by norm_num)
theorem B3337331 : Blo 2223435 3337331 := bstep (se 1 (by rfl) ⟨2502998, by rfl⟩ : syracuseStep 3337331 = 5005997) B5005997
theorem B2224887 : Blo 2223435 2224887 := bstep (se 1 (by rfl) ⟨1668665, by rfl⟩ : syracuseStep 2224887 = 3337331) B3337331
theorem B4751797 : Blo 2223435 4751797 := bbase (se 5 (by rfl) ⟨222740, by rfl⟩ : syracuseStep 4751797 = 445481) (by norm_num)
theorem B6335729 : Blo 2223435 6335729 := bstep (se 2 (by rfl) ⟨2375898, by rfl⟩ : syracuseStep 6335729 = 4751797) B4751797
theorem B4223819 : Blo 2223435 4223819 := bstep (se 1 (by rfl) ⟨3167864, by rfl⟩ : syracuseStep 4223819 = 6335729) B6335729
theorem B2815879 : Blo 2223435 2815879 := bstep (se 1 (by rfl) ⟨2111909, by rfl⟩ : syracuseStep 2815879 = 4223819) B4223819
theorem B3754505 : Blo 2223435 3754505 := bstep (se 2 (by rfl) ⟨1407939, by rfl⟩ : syracuseStep 3754505 = 2815879) B2815879
theorem B2503003 : Blo 2223435 2503003 := bstep (se 1 (by rfl) ⟨1877252, by rfl⟩ : syracuseStep 2503003 = 3754505) B3754505
theorem B3337337 : Blo 2223435 3337337 := bstep (se 2 (by rfl) ⟨1251501, by rfl⟩ : syracuseStep 3337337 = 2503003) B2503003
theorem B2224891 : Blo 2223435 2224891 := bstep (se 1 (by rfl) ⟨1668668, by rfl⟩ : syracuseStep 2224891 = 3337337) B3337337
theorem B40594517 : Blo 2223435 40594517 := bbase (se 8 (by rfl) ⟨237858, by rfl⟩ : syracuseStep 40594517 = 475717) (by norm_num)
theorem B27063011 : Blo 2223435 27063011 := bstep (se 1 (by rfl) ⟨20297258, by rfl⟩ : syracuseStep 27063011 = 40594517) B40594517
theorem B72168029 : Blo 2223435 72168029 := bstep (se 3 (by rfl) ⟨13531505, by rfl⟩ : syracuseStep 72168029 = 27063011) B27063011
theorem B48112019 : Blo 2223435 48112019 := bstep (se 1 (by rfl) ⟨36084014, by rfl⟩ : syracuseStep 48112019 = 72168029) B72168029
theorem B32074679 : Blo 2223435 32074679 := bstep (se 1 (by rfl) ⟨24056009, by rfl⟩ : syracuseStep 32074679 = 48112019) B48112019
theorem B21383119 : Blo 2223435 21383119 := bstep (se 1 (by rfl) ⟨16037339, by rfl⟩ : syracuseStep 21383119 = 32074679) B32074679
theorem B28510825 : Blo 2223435 28510825 := bstep (se 2 (by rfl) ⟨10691559, by rfl⟩ : syracuseStep 28510825 = 21383119) B21383119
theorem B38014433 : Blo 2223435 38014433 := bstep (se 2 (by rfl) ⟨14255412, by rfl⟩ : syracuseStep 38014433 = 28510825) B28510825
theorem B25342955 : Blo 2223435 25342955 := bstep (se 1 (by rfl) ⟨19007216, by rfl⟩ : syracuseStep 25342955 = 38014433) B38014433
theorem B16895303 : Blo 2223435 16895303 := bstep (se 1 (by rfl) ⟨12671477, by rfl⟩ : syracuseStep 16895303 = 25342955) B25342955
theorem B11263535 : Blo 2223435 11263535 := bstep (se 1 (by rfl) ⟨8447651, by rfl⟩ : syracuseStep 11263535 = 16895303) B16895303
theorem B7509023 : Blo 2223435 7509023 := bstep (se 1 (by rfl) ⟨5631767, by rfl⟩ : syracuseStep 7509023 = 11263535) B11263535
theorem B5006015 : Blo 2223435 5006015 := bstep (se 1 (by rfl) ⟨3754511, by rfl⟩ : syracuseStep 5006015 = 7509023) B7509023
theorem B3337343 : Blo 2223435 3337343 := bstep (se 1 (by rfl) ⟨2503007, by rfl⟩ : syracuseStep 3337343 = 5006015) B5006015
theorem B2224895 : Blo 2223435 2224895 := bstep (se 1 (by rfl) ⟨1668671, by rfl⟩ : syracuseStep 2224895 = 3337343) B3337343
theorem B3337349 : Blo 2223435 3337349 := bbase (se 4 (by rfl) ⟨312876, by rfl⟩ : syracuseStep 3337349 = 625753) (by norm_num)
theorem B2224899 : Blo 2223435 2224899 := bstep (se 1 (by rfl) ⟨1668674, by rfl⟩ : syracuseStep 2224899 = 3337349) B3337349
theorem B3754525 : Blo 2223435 3754525 := bbase (se 3 (by rfl) ⟨703973, by rfl⟩ : syracuseStep 3754525 = 1407947) (by norm_num)
theorem B5006033 : Blo 2223435 5006033 := bstep (se 2 (by rfl) ⟨1877262, by rfl⟩ : syracuseStep 5006033 = 3754525) B3754525
theorem B3337355 : Blo 2223435 3337355 := bstep (se 1 (by rfl) ⟨2503016, by rfl⟩ : syracuseStep 3337355 = 5006033) B5006033
theorem B2224903 : Blo 2223435 2224903 := bstep (se 1 (by rfl) ⟨1668677, by rfl⟩ : syracuseStep 2224903 = 3337355) B3337355
theorem B2503021 : Blo 2223435 2503021 := bbase (se 3 (by rfl) ⟨469316, by rfl⟩ : syracuseStep 2503021 = 938633) (by norm_num)
theorem B3337361 : Blo 2223435 3337361 := bstep (se 2 (by rfl) ⟨1251510, by rfl⟩ : syracuseStep 3337361 = 2503021) B2503021
theorem B2224907 : Blo 2223435 2224907 := bstep (se 1 (by rfl) ⟨1668680, by rfl⟩ : syracuseStep 2224907 = 3337361) B3337361
theorem B7509077 : Blo 2223435 7509077 := bbase (se 8 (by rfl) ⟨43998, by rfl⟩ : syracuseStep 7509077 = 87997) (by norm_num)
theorem B5006051 : Blo 2223435 5006051 := bstep (se 1 (by rfl) ⟨3754538, by rfl⟩ : syracuseStep 5006051 = 7509077) B7509077
theorem B3337367 : Blo 2223435 3337367 := bstep (se 1 (by rfl) ⟨2503025, by rfl⟩ : syracuseStep 3337367 = 5006051) B5006051
theorem B2224911 : Blo 2223435 2224911 := bstep (se 1 (by rfl) ⟨1668683, by rfl⟩ : syracuseStep 2224911 = 3337367) B3337367
theorem B3337373 : Blo 2223435 3337373 := bbase (se 3 (by rfl) ⟨625757, by rfl⟩ : syracuseStep 3337373 = 1251515) (by norm_num)
theorem B2224915 : Blo 2223435 2224915 := bstep (se 1 (by rfl) ⟨1668686, by rfl⟩ : syracuseStep 2224915 = 3337373) B3337373
theorem B5006069 : Blo 2223435 5006069 := bbase (se 5 (by rfl) ⟨234659, by rfl⟩ : syracuseStep 5006069 = 469319) (by norm_num)
theorem B3337379 : Blo 2223435 3337379 := bstep (se 1 (by rfl) ⟨2503034, by rfl⟩ : syracuseStep 3337379 = 5006069) B5006069
theorem B2224919 : Blo 2223435 2224919 := bstep (se 1 (by rfl) ⟨1668689, by rfl⟩ : syracuseStep 2224919 = 3337379) B3337379
theorem B28511189 : Blo 2223435 28511189 := bbase (se 7 (by rfl) ⟨334115, by rfl⟩ : syracuseStep 28511189 = 668231) (by norm_num)
theorem B19007459 : Blo 2223435 19007459 := bstep (se 1 (by rfl) ⟨14255594, by rfl⟩ : syracuseStep 19007459 = 28511189) B28511189
theorem B12671639 : Blo 2223435 12671639 := bstep (se 1 (by rfl) ⟨9503729, by rfl⟩ : syracuseStep 12671639 = 19007459) B19007459
theorem B8447759 : Blo 2223435 8447759 := bstep (se 1 (by rfl) ⟨6335819, by rfl⟩ : syracuseStep 8447759 = 12671639) B12671639
theorem B5631839 : Blo 2223435 5631839 := bstep (se 1 (by rfl) ⟨4223879, by rfl⟩ : syracuseStep 5631839 = 8447759) B8447759
theorem B3754559 : Blo 2223435 3754559 := bstep (se 1 (by rfl) ⟨2815919, by rfl⟩ : syracuseStep 3754559 = 5631839) B5631839
theorem B2503039 : Blo 2223435 2503039 := bstep (se 1 (by rfl) ⟨1877279, by rfl⟩ : syracuseStep 2503039 = 3754559) B3754559
theorem B3337385 : Blo 2223435 3337385 := bstep (se 2 (by rfl) ⟨1251519, by rfl⟩ : syracuseStep 3337385 = 2503039) B2503039
theorem B2224923 : Blo 2223435 2224923 := bstep (se 1 (by rfl) ⟨1668692, by rfl⟩ : syracuseStep 2224923 = 3337385) B3337385
theorem B2672929 : Blo 2223435 2672929 := bbase (se 2 (by rfl) ⟨1002348, by rfl⟩ : syracuseStep 2672929 = 2004697) (by norm_num)
theorem B3563905 : Blo 2223435 3563905 := bstep (se 2 (by rfl) ⟨1336464, by rfl⟩ : syracuseStep 3563905 = 2672929) B2672929
theorem B4751873 : Blo 2223435 4751873 := bstep (se 2 (by rfl) ⟨1781952, by rfl⟩ : syracuseStep 4751873 = 3563905) B3563905
theorem B3167915 : Blo 2223435 3167915 := bstep (se 1 (by rfl) ⟨2375936, by rfl⟩ : syracuseStep 3167915 = 4751873) B4751873
theorem B8447773 : Blo 2223435 8447773 := bstep (se 3 (by rfl) ⟨1583957, by rfl⟩ : syracuseStep 8447773 = 3167915) B3167915
theorem B11263697 : Blo 2223435 11263697 := bstep (se 2 (by rfl) ⟨4223886, by rfl⟩ : syracuseStep 11263697 = 8447773) B8447773
theorem B7509131 : Blo 2223435 7509131 := bstep (se 1 (by rfl) ⟨5631848, by rfl⟩ : syracuseStep 7509131 = 11263697) B11263697
theorem B5006087 : Blo 2223435 5006087 := bstep (se 1 (by rfl) ⟨3754565, by rfl⟩ : syracuseStep 5006087 = 7509131) B7509131
theorem B3337391 : Blo 2223435 3337391 := bstep (se 1 (by rfl) ⟨2503043, by rfl⟩ : syracuseStep 3337391 = 5006087) B5006087
theorem B2224927 : Blo 2223435 2224927 := bstep (se 1 (by rfl) ⟨1668695, by rfl⟩ : syracuseStep 2224927 = 3337391) B3337391
theorem B3337397 : Blo 2223435 3337397 := bbase (se 5 (by rfl) ⟨156440, by rfl⟩ : syracuseStep 3337397 = 312881) (by norm_num)
theorem B2224931 : Blo 2223435 2224931 := bstep (se 1 (by rfl) ⟨1668698, by rfl⟩ : syracuseStep 2224931 = 3337397) B3337397
theorem B5631869 : Blo 2223435 5631869 := bbase (se 3 (by rfl) ⟨1055975, by rfl⟩ : syracuseStep 5631869 = 2111951) (by norm_num)
theorem B3754579 : Blo 2223435 3754579 := bstep (se 1 (by rfl) ⟨2815934, by rfl⟩ : syracuseStep 3754579 = 5631869) B5631869
theorem B5006105 : Blo 2223435 5006105 := bstep (se 2 (by rfl) ⟨1877289, by rfl⟩ : syracuseStep 5006105 = 3754579) B3754579
theorem B3337403 : Blo 2223435 3337403 := bstep (se 1 (by rfl) ⟨2503052, by rfl⟩ : syracuseStep 3337403 = 5006105) B5006105
theorem B2224935 : Blo 2223435 2224935 := bstep (se 1 (by rfl) ⟨1668701, by rfl⟩ : syracuseStep 2224935 = 3337403) B3337403
theorem B2503057 : Blo 2223435 2503057 := bbase (se 2 (by rfl) ⟨938646, by rfl⟩ : syracuseStep 2503057 = 1877293) (by norm_num)
theorem B3337409 : Blo 2223435 3337409 := bstep (se 2 (by rfl) ⟨1251528, by rfl⟩ : syracuseStep 3337409 = 2503057) B2503057
theorem B2224939 : Blo 2223435 2224939 := bstep (se 1 (by rfl) ⟨1668704, by rfl⟩ : syracuseStep 2224939 = 3337409) B3337409
theorem B4223917 : Blo 2223435 4223917 := bbase (se 3 (by rfl) ⟨791984, by rfl⟩ : syracuseStep 4223917 = 1583969) (by norm_num)
theorem B5631889 : Blo 2223435 5631889 := bstep (se 2 (by rfl) ⟨2111958, by rfl⟩ : syracuseStep 5631889 = 4223917) B4223917
theorem B7509185 : Blo 2223435 7509185 := bstep (se 2 (by rfl) ⟨2815944, by rfl⟩ : syracuseStep 7509185 = 5631889) B5631889
theorem B5006123 : Blo 2223435 5006123 := bstep (se 1 (by rfl) ⟨3754592, by rfl⟩ : syracuseStep 5006123 = 7509185) B7509185
theorem B3337415 : Blo 2223435 3337415 := bstep (se 1 (by rfl) ⟨2503061, by rfl⟩ : syracuseStep 3337415 = 5006123) B5006123
theorem B2224943 : Blo 2223435 2224943 := bstep (se 1 (by rfl) ⟨1668707, by rfl⟩ : syracuseStep 2224943 = 3337415) B3337415
theorem B3337421 : Blo 2223435 3337421 := bbase (se 3 (by rfl) ⟨625766, by rfl⟩ : syracuseStep 3337421 = 1251533) (by norm_num)
theorem B2224947 : Blo 2223435 2224947 := bstep (se 1 (by rfl) ⟨1668710, by rfl⟩ : syracuseStep 2224947 = 3337421) B3337421
theorem B5006141 : Blo 2223435 5006141 := bbase (se 3 (by rfl) ⟨938651, by rfl⟩ : syracuseStep 5006141 = 1877303) (by norm_num)
theorem B3337427 : Blo 2223435 3337427 := bstep (se 1 (by rfl) ⟨2503070, by rfl⟩ : syracuseStep 3337427 = 5006141) B5006141
theorem B2224951 : Blo 2223435 2224951 := bstep (se 1 (by rfl) ⟨1668713, by rfl⟩ : syracuseStep 2224951 = 3337427) B3337427
theorem B3754613 : Blo 2223435 3754613 := bbase (se 5 (by rfl) ⟨175997, by rfl⟩ : syracuseStep 3754613 = 351995) (by norm_num)
theorem B2503075 : Blo 2223435 2503075 := bstep (se 1 (by rfl) ⟨1877306, by rfl⟩ : syracuseStep 2503075 = 3754613) B3754613
theorem B3337433 : Blo 2223435 3337433 := bstep (se 2 (by rfl) ⟨1251537, by rfl⟩ : syracuseStep 3337433 = 2503075) B2503075
theorem B2224955 : Blo 2223435 2224955 := bstep (se 1 (by rfl) ⟨1668716, by rfl⟩ : syracuseStep 2224955 = 3337433) B3337433
theorem B4751941 : Blo 2223435 4751941 := bbase (se 4 (by rfl) ⟨445494, by rfl⟩ : syracuseStep 4751941 = 890989) (by norm_num)
theorem B6335921 : Blo 2223435 6335921 := bstep (se 2 (by rfl) ⟨2375970, by rfl⟩ : syracuseStep 6335921 = 4751941) B4751941
theorem B16895789 : Blo 2223435 16895789 := bstep (se 3 (by rfl) ⟨3167960, by rfl⟩ : syracuseStep 16895789 = 6335921) B6335921
theorem B11263859 : Blo 2223435 11263859 := bstep (se 1 (by rfl) ⟨8447894, by rfl⟩ : syracuseStep 11263859 = 16895789) B16895789
theorem B7509239 : Blo 2223435 7509239 := bstep (se 1 (by rfl) ⟨5631929, by rfl⟩ : syracuseStep 7509239 = 11263859) B11263859
theorem B5006159 : Blo 2223435 5006159 := bstep (se 1 (by rfl) ⟨3754619, by rfl⟩ : syracuseStep 5006159 = 7509239) B7509239
theorem B3337439 : Blo 2223435 3337439 := bstep (se 1 (by rfl) ⟨2503079, by rfl⟩ : syracuseStep 3337439 = 5006159) B5006159
theorem B2224959 : Blo 2223435 2224959 := bstep (se 1 (by rfl) ⟨1668719, by rfl⟩ : syracuseStep 2224959 = 3337439) B3337439
theorem B3337445 : Blo 2223435 3337445 := bbase (se 4 (by rfl) ⟨312885, by rfl⟩ : syracuseStep 3337445 = 625771) (by norm_num)
theorem B2224963 : Blo 2223435 2224963 := bstep (se 1 (by rfl) ⟨1668722, by rfl⟩ : syracuseStep 2224963 = 3337445) B3337445
theorem B10691909 : Blo 2223435 10691909 := bbase (se 4 (by rfl) ⟨1002366, by rfl⟩ : syracuseStep 10691909 = 2004733) (by norm_num)
theorem B7127939 : Blo 2223435 7127939 := bstep (se 1 (by rfl) ⟨5345954, by rfl⟩ : syracuseStep 7127939 = 10691909) B10691909
theorem B4751959 : Blo 2223435 4751959 := bstep (se 1 (by rfl) ⟨3563969, by rfl⟩ : syracuseStep 4751959 = 7127939) B7127939
theorem B6335945 : Blo 2223435 6335945 := bstep (se 2 (by rfl) ⟨2375979, by rfl⟩ : syracuseStep 6335945 = 4751959) B4751959
theorem B4223963 : Blo 2223435 4223963 := bstep (se 1 (by rfl) ⟨3167972, by rfl⟩ : syracuseStep 4223963 = 6335945) B6335945
theorem B2815975 : Blo 2223435 2815975 := bstep (se 1 (by rfl) ⟨2111981, by rfl⟩ : syracuseStep 2815975 = 4223963) B4223963
theorem B3754633 : Blo 2223435 3754633 := bstep (se 2 (by rfl) ⟨1407987, by rfl⟩ : syracuseStep 3754633 = 2815975) B2815975
theorem B5006177 : Blo 2223435 5006177 := bstep (se 2 (by rfl) ⟨1877316, by rfl⟩ : syracuseStep 5006177 = 3754633) B3754633
theorem B3337451 : Blo 2223435 3337451 := bstep (se 1 (by rfl) ⟨2503088, by rfl⟩ : syracuseStep 3337451 = 5006177) B5006177
theorem B2224967 : Blo 2223435 2224967 := bstep (se 1 (by rfl) ⟨1668725, by rfl⟩ : syracuseStep 2224967 = 3337451) B3337451
theorem B2503093 : Blo 2223435 2503093 := bbase (se 5 (by rfl) ⟨117332, by rfl⟩ : syracuseStep 2503093 = 234665) (by norm_num)
theorem B3337457 : Blo 2223435 3337457 := bstep (se 2 (by rfl) ⟨1251546, by rfl⟩ : syracuseStep 3337457 = 2503093) B2503093
theorem B2224971 : Blo 2223435 2224971 := bstep (se 1 (by rfl) ⟨1668728, by rfl⟩ : syracuseStep 2224971 = 3337457) B3337457
theorem B2815985 : Blo 2223435 2815985 := bbase (se 2 (by rfl) ⟨1055994, by rfl⟩ : syracuseStep 2815985 = 2111989) (by norm_num)
theorem B7509293 : Blo 2223435 7509293 := bstep (se 3 (by rfl) ⟨1407992, by rfl⟩ : syracuseStep 7509293 = 2815985) B2815985
theorem B5006195 : Blo 2223435 5006195 := bstep (se 1 (by rfl) ⟨3754646, by rfl⟩ : syracuseStep 5006195 = 7509293) B7509293
theorem B3337463 : Blo 2223435 3337463 := bstep (se 1 (by rfl) ⟨2503097, by rfl⟩ : syracuseStep 3337463 = 5006195) B5006195
theorem B2224975 : Blo 2223435 2224975 := bstep (se 1 (by rfl) ⟨1668731, by rfl⟩ : syracuseStep 2224975 = 3337463) B3337463
theorem B3337469 : Blo 2223435 3337469 := bbase (se 3 (by rfl) ⟨625775, by rfl⟩ : syracuseStep 3337469 = 1251551) (by norm_num)
theorem B2224979 : Blo 2223435 2224979 := bstep (se 1 (by rfl) ⟨1668734, by rfl⟩ : syracuseStep 2224979 = 3337469) B3337469
theorem B5006213 : Blo 2223435 5006213 := bbase (se 4 (by rfl) ⟨469332, by rfl⟩ : syracuseStep 5006213 = 938665) (by norm_num)
theorem B3337475 : Blo 2223435 3337475 := bstep (se 1 (by rfl) ⟨2503106, by rfl⟩ : syracuseStep 3337475 = 5006213) B5006213
theorem B2224983 : Blo 2223435 2224983 := bstep (se 1 (by rfl) ⟨1668737, by rfl⟩ : syracuseStep 2224983 = 3337475) B3337475
theorem B2376001 : Blo 2223435 2376001 := bbase (se 2 (by rfl) ⟨891000, by rfl⟩ : syracuseStep 2376001 = 1782001) (by norm_num)
theorem B3168001 : Blo 2223435 3168001 := bstep (se 2 (by rfl) ⟨1188000, by rfl⟩ : syracuseStep 3168001 = 2376001) B2376001
theorem B4224001 : Blo 2223435 4224001 := bstep (se 2 (by rfl) ⟨1584000, by rfl⟩ : syracuseStep 4224001 = 3168001) B3168001
theorem B5632001 : Blo 2223435 5632001 := bstep (se 2 (by rfl) ⟨2112000, by rfl⟩ : syracuseStep 5632001 = 4224001) B4224001
theorem B3754667 : Blo 2223435 3754667 := bstep (se 1 (by rfl) ⟨2816000, by rfl⟩ : syracuseStep 3754667 = 5632001) B5632001
theorem B2503111 : Blo 2223435 2503111 := bstep (se 1 (by rfl) ⟨1877333, by rfl⟩ : syracuseStep 2503111 = 3754667) B3754667
theorem B3337481 : Blo 2223435 3337481 := bstep (se 2 (by rfl) ⟨1251555, by rfl⟩ : syracuseStep 3337481 = 2503111) B2503111
theorem B2224987 : Blo 2223435 2224987 := bstep (se 1 (by rfl) ⟨1668740, by rfl⟩ : syracuseStep 2224987 = 3337481) B3337481
theorem B11264021 : Blo 2223435 11264021 := bbase (se 6 (by rfl) ⟨264000, by rfl⟩ : syracuseStep 11264021 = 528001) (by norm_num)
theorem B7509347 : Blo 2223435 7509347 := bstep (se 1 (by rfl) ⟨5632010, by rfl⟩ : syracuseStep 7509347 = 11264021) B11264021
theorem B5006231 : Blo 2223435 5006231 := bstep (se 1 (by rfl) ⟨3754673, by rfl⟩ : syracuseStep 5006231 = 7509347) B7509347
theorem B3337487 : Blo 2223435 3337487 := bstep (se 1 (by rfl) ⟨2503115, by rfl⟩ : syracuseStep 3337487 = 5006231) B5006231
theorem B2224991 : Blo 2223435 2224991 := bstep (se 1 (by rfl) ⟨1668743, by rfl⟩ : syracuseStep 2224991 = 3337487) B3337487
theorem B3337493 : Blo 2223435 3337493 := bbase (se 6 (by rfl) ⟨78222, by rfl⟩ : syracuseStep 3337493 = 156445) (by norm_num)
theorem B2224995 : Blo 2223435 2224995 := bstep (se 1 (by rfl) ⟨1668746, by rfl⟩ : syracuseStep 2224995 = 3337493) B3337493
theorem B5786765 : Blo 2223435 5786765 := bbase (se 3 (by rfl) ⟨1085018, by rfl⟩ : syracuseStep 5786765 = 2170037) (by norm_num)
theorem B3857843 : Blo 2223435 3857843 := bstep (se 1 (by rfl) ⟨2893382, by rfl⟩ : syracuseStep 3857843 = 5786765) B5786765
theorem B2571895 : Blo 2223435 2571895 := bstep (se 1 (by rfl) ⟨1928921, by rfl⟩ : syracuseStep 2571895 = 3857843) B3857843
theorem B13716773 : Blo 2223435 13716773 := bstep (se 4 (by rfl) ⟨1285947, by rfl⟩ : syracuseStep 13716773 = 2571895) B2571895
theorem B9144515 : Blo 2223435 9144515 := bstep (se 1 (by rfl) ⟨6858386, by rfl⟩ : syracuseStep 9144515 = 13716773) B13716773
theorem B6096343 : Blo 2223435 6096343 := bstep (se 1 (by rfl) ⟨4572257, by rfl⟩ : syracuseStep 6096343 = 9144515) B9144515
theorem B8128457 : Blo 2223435 8128457 := bstep (se 2 (by rfl) ⟨3048171, by rfl⟩ : syracuseStep 8128457 = 6096343) B6096343
theorem B5418971 : Blo 2223435 5418971 := bstep (se 1 (by rfl) ⟨4064228, by rfl⟩ : syracuseStep 5418971 = 8128457) B8128457
theorem B3612647 : Blo 2223435 3612647 := bstep (se 1 (by rfl) ⟨2709485, by rfl⟩ : syracuseStep 3612647 = 5418971) B5418971
theorem B9633725 : Blo 2223435 9633725 := bstep (se 3 (by rfl) ⟨1806323, by rfl⟩ : syracuseStep 9633725 = 3612647) B3612647
theorem B6422483 : Blo 2223435 6422483 := bstep (se 1 (by rfl) ⟨4816862, by rfl⟩ : syracuseStep 6422483 = 9633725) B9633725
theorem B4281655 : Blo 2223435 4281655 := bstep (se 1 (by rfl) ⟨3211241, by rfl⟩ : syracuseStep 4281655 = 6422483) B6422483
theorem B5708873 : Blo 2223435 5708873 := bstep (se 2 (by rfl) ⟨2140827, by rfl⟩ : syracuseStep 5708873 = 4281655) B4281655
theorem B3805915 : Blo 2223435 3805915 := bstep (se 1 (by rfl) ⟨2854436, by rfl⟩ : syracuseStep 3805915 = 5708873) B5708873
theorem B5074553 : Blo 2223435 5074553 := bstep (se 2 (by rfl) ⟨1902957, by rfl⟩ : syracuseStep 5074553 = 3805915) B3805915
theorem B3383035 : Blo 2223435 3383035 := bstep (se 1 (by rfl) ⟨2537276, by rfl⟩ : syracuseStep 3383035 = 5074553) B5074553
theorem B18042853 : Blo 2223435 18042853 := bstep (se 4 (by rfl) ⟨1691517, by rfl⟩ : syracuseStep 18042853 = 3383035) B3383035
theorem B24057137 : Blo 2223435 24057137 := bstep (se 2 (by rfl) ⟨9021426, by rfl⟩ : syracuseStep 24057137 = 18042853) B18042853
theorem B16038091 : Blo 2223435 16038091 := bstep (se 1 (by rfl) ⟨12028568, by rfl⟩ : syracuseStep 16038091 = 24057137) B24057137
theorem B21384121 : Blo 2223435 21384121 := bstep (se 2 (by rfl) ⟨8019045, by rfl⟩ : syracuseStep 21384121 = 16038091) B16038091
theorem B28512161 : Blo 2223435 28512161 := bstep (se 2 (by rfl) ⟨10692060, by rfl⟩ : syracuseStep 28512161 = 21384121) B21384121
theorem B19008107 : Blo 2223435 19008107 := bstep (se 1 (by rfl) ⟨14256080, by rfl⟩ : syracuseStep 19008107 = 28512161) B28512161
theorem B12672071 : Blo 2223435 12672071 := bstep (se 1 (by rfl) ⟨9504053, by rfl⟩ : syracuseStep 12672071 = 19008107) B19008107
theorem B8448047 : Blo 2223435 8448047 := bstep (se 1 (by rfl) ⟨6336035, by rfl⟩ : syracuseStep 8448047 = 12672071) B12672071
theorem B5632031 : Blo 2223435 5632031 := bstep (se 1 (by rfl) ⟨4224023, by rfl⟩ : syracuseStep 5632031 = 8448047) B8448047
theorem B3754687 : Blo 2223435 3754687 := bstep (se 1 (by rfl) ⟨2816015, by rfl⟩ : syracuseStep 3754687 = 5632031) B5632031
theorem B5006249 : Blo 2223435 5006249 := bstep (se 2 (by rfl) ⟨1877343, by rfl⟩ : syracuseStep 5006249 = 3754687) B3754687
theorem B3337499 : Blo 2223435 3337499 := bstep (se 1 (by rfl) ⟨2503124, by rfl⟩ : syracuseStep 3337499 = 5006249) B5006249
theorem B2224999 : Blo 2223435 2224999 := bstep (se 1 (by rfl) ⟨1668749, by rfl⟩ : syracuseStep 2224999 = 3337499) B3337499
theorem B2503129 : Blo 2223435 2503129 := bbase (se 2 (by rfl) ⟨938673, by rfl⟩ : syracuseStep 2503129 = 1877347) (by norm_num)
theorem B3337505 : Blo 2223435 3337505 := bstep (se 2 (by rfl) ⟨1251564, by rfl⟩ : syracuseStep 3337505 = 2503129) B2503129
theorem B2225003 : Blo 2223435 2225003 := bstep (se 1 (by rfl) ⟨1668752, by rfl⟩ : syracuseStep 2225003 = 3337505) B3337505
theorem B3168029 : Blo 2223435 3168029 := bbase (se 3 (by rfl) ⟨594005, by rfl⟩ : syracuseStep 3168029 = 1188011) (by norm_num)
theorem B8448077 : Blo 2223435 8448077 := bstep (se 3 (by rfl) ⟨1584014, by rfl⟩ : syracuseStep 8448077 = 3168029) B3168029
theorem B5632051 : Blo 2223435 5632051 := bstep (se 1 (by rfl) ⟨4224038, by rfl⟩ : syracuseStep 5632051 = 8448077) B8448077
theorem B7509401 : Blo 2223435 7509401 := bstep (se 2 (by rfl) ⟨2816025, by rfl⟩ : syracuseStep 7509401 = 5632051) B5632051
theorem B5006267 : Blo 2223435 5006267 := bstep (se 1 (by rfl) ⟨3754700, by rfl⟩ : syracuseStep 5006267 = 7509401) B7509401
theorem B3337511 : Blo 2223435 3337511 := bstep (se 1 (by rfl) ⟨2503133, by rfl⟩ : syracuseStep 3337511 = 5006267) B5006267
theorem B2225007 : Blo 2223435 2225007 := bstep (se 1 (by rfl) ⟨1668755, by rfl⟩ : syracuseStep 2225007 = 3337511) B3337511
theorem B3337517 : Blo 2223435 3337517 := bbase (se 3 (by rfl) ⟨625784, by rfl⟩ : syracuseStep 3337517 = 1251569) (by norm_num)
theorem B2225011 : Blo 2223435 2225011 := bstep (se 1 (by rfl) ⟨1668758, by rfl⟩ : syracuseStep 2225011 = 3337517) B3337517
theorem B5006285 : Blo 2223435 5006285 := bbase (se 3 (by rfl) ⟨938678, by rfl⟩ : syracuseStep 5006285 = 1877357) (by norm_num)
theorem B3337523 : Blo 2223435 3337523 := bstep (se 1 (by rfl) ⟨2503142, by rfl⟩ : syracuseStep 3337523 = 5006285) B5006285
theorem B2225015 : Blo 2223435 2225015 := bstep (se 1 (by rfl) ⟨1668761, by rfl⟩ : syracuseStep 2225015 = 3337523) B3337523
theorem B2816041 : Blo 2223435 2816041 := bbase (se 2 (by rfl) ⟨1056015, by rfl⟩ : syracuseStep 2816041 = 2112031) (by norm_num)
theorem B3754721 : Blo 2223435 3754721 := bstep (se 2 (by rfl) ⟨1408020, by rfl⟩ : syracuseStep 3754721 = 2816041) B2816041
theorem B2503147 : Blo 2223435 2503147 := bstep (se 1 (by rfl) ⟨1877360, by rfl⟩ : syracuseStep 2503147 = 3754721) B3754721
theorem B3337529 : Blo 2223435 3337529 := bstep (se 2 (by rfl) ⟨1251573, by rfl⟩ : syracuseStep 3337529 = 2503147) B2503147
theorem B2225019 : Blo 2223435 2225019 := bstep (se 1 (by rfl) ⟨1668764, by rfl⟩ : syracuseStep 2225019 = 3337529) B3337529
theorem B3612685 : Blo 2223435 3612685 := bbase (se 3 (by rfl) ⟨677378, by rfl⟩ : syracuseStep 3612685 = 1354757) (by norm_num)
theorem B4816913 : Blo 2223435 4816913 := bstep (se 2 (by rfl) ⟨1806342, by rfl⟩ : syracuseStep 4816913 = 3612685) B3612685
theorem B12845101 : Blo 2223435 12845101 := bstep (se 3 (by rfl) ⟨2408456, by rfl⟩ : syracuseStep 12845101 = 4816913) B4816913
theorem B17126801 : Blo 2223435 17126801 := bstep (se 2 (by rfl) ⟨6422550, by rfl⟩ : syracuseStep 17126801 = 12845101) B12845101
theorem B11417867 : Blo 2223435 11417867 := bstep (se 1 (by rfl) ⟨8563400, by rfl⟩ : syracuseStep 11417867 = 17126801) B17126801
theorem B7611911 : Blo 2223435 7611911 := bstep (se 1 (by rfl) ⟨5708933, by rfl⟩ : syracuseStep 7611911 = 11417867) B11417867
theorem B5074607 : Blo 2223435 5074607 := bstep (se 1 (by rfl) ⟨3805955, by rfl⟩ : syracuseStep 5074607 = 7611911) B7611911
theorem B13532285 : Blo 2223435 13532285 := bstep (se 3 (by rfl) ⟨2537303, by rfl⟩ : syracuseStep 13532285 = 5074607) B5074607
theorem B36086093 : Blo 2223435 36086093 := bstep (se 3 (by rfl) ⟨6766142, by rfl⟩ : syracuseStep 36086093 = 13532285) B13532285
theorem B24057395 : Blo 2223435 24057395 := bstep (se 1 (by rfl) ⟨18043046, by rfl⟩ : syracuseStep 24057395 = 36086093) B36086093
theorem B16038263 : Blo 2223435 16038263 := bstep (se 1 (by rfl) ⟨12028697, by rfl⟩ : syracuseStep 16038263 = 24057395) B24057395
theorem B10692175 : Blo 2223435 10692175 := bstep (se 1 (by rfl) ⟨8019131, by rfl⟩ : syracuseStep 10692175 = 16038263) B16038263
theorem B14256233 : Blo 2223435 14256233 := bstep (se 2 (by rfl) ⟨5346087, by rfl⟩ : syracuseStep 14256233 = 10692175) B10692175
theorem B9504155 : Blo 2223435 9504155 := bstep (se 1 (by rfl) ⟨7128116, by rfl⟩ : syracuseStep 9504155 = 14256233) B14256233
theorem B25344413 : Blo 2223435 25344413 := bstep (se 3 (by rfl) ⟨4752077, by rfl⟩ : syracuseStep 25344413 = 9504155) B9504155
theorem B16896275 : Blo 2223435 16896275 := bstep (se 1 (by rfl) ⟨12672206, by rfl⟩ : syracuseStep 16896275 = 25344413) B25344413
theorem B11264183 : Blo 2223435 11264183 := bstep (se 1 (by rfl) ⟨8448137, by rfl⟩ : syracuseStep 11264183 = 16896275) B16896275
theorem B7509455 : Blo 2223435 7509455 := bstep (se 1 (by rfl) ⟨5632091, by rfl⟩ : syracuseStep 7509455 = 11264183) B11264183
theorem B5006303 : Blo 2223435 5006303 := bstep (se 1 (by rfl) ⟨3754727, by rfl⟩ : syracuseStep 5006303 = 7509455) B7509455
theorem B3337535 : Blo 2223435 3337535 := bstep (se 1 (by rfl) ⟨2503151, by rfl⟩ : syracuseStep 3337535 = 5006303) B5006303
theorem B2225023 : Blo 2223435 2225023 := bstep (se 1 (by rfl) ⟨1668767, by rfl⟩ : syracuseStep 2225023 = 3337535) B3337535
theorem B3337541 : Blo 2223435 3337541 := bbase (se 4 (by rfl) ⟨312894, by rfl⟩ : syracuseStep 3337541 = 625789) (by norm_num)
theorem B2225027 : Blo 2223435 2225027 := bstep (se 1 (by rfl) ⟨1668770, by rfl⟩ : syracuseStep 2225027 = 3337541) B3337541
theorem B3754741 : Blo 2223435 3754741 := bbase (se 5 (by rfl) ⟨176003, by rfl⟩ : syracuseStep 3754741 = 352007) (by norm_num)
theorem B5006321 : Blo 2223435 5006321 := bstep (se 2 (by rfl) ⟨1877370, by rfl⟩ : syracuseStep 5006321 = 3754741) B3754741
theorem B3337547 : Blo 2223435 3337547 := bstep (se 1 (by rfl) ⟨2503160, by rfl⟩ : syracuseStep 3337547 = 5006321) B5006321
theorem B2225031 : Blo 2223435 2225031 := bstep (se 1 (by rfl) ⟨1668773, by rfl⟩ : syracuseStep 2225031 = 3337547) B3337547
theorem B2503165 : Blo 2223435 2503165 := bbase (se 3 (by rfl) ⟨469343, by rfl⟩ : syracuseStep 2503165 = 938687) (by norm_num)
theorem B3337553 : Blo 2223435 3337553 := bstep (se 2 (by rfl) ⟨1251582, by rfl⟩ : syracuseStep 3337553 = 2503165) B2503165
theorem B2225035 : Blo 2223435 2225035 := bstep (se 1 (by rfl) ⟨1668776, by rfl⟩ : syracuseStep 2225035 = 3337553) B3337553
theorem B7509509 : Blo 2223435 7509509 := bbase (se 4 (by rfl) ⟨704016, by rfl⟩ : syracuseStep 7509509 = 1408033) (by norm_num)
theorem B5006339 : Blo 2223435 5006339 := bstep (se 1 (by rfl) ⟨3754754, by rfl⟩ : syracuseStep 5006339 = 7509509) B7509509
theorem B3337559 : Blo 2223435 3337559 := bstep (se 1 (by rfl) ⟨2503169, by rfl⟩ : syracuseStep 3337559 = 5006339) B5006339
theorem B2225039 : Blo 2223435 2225039 := bstep (se 1 (by rfl) ⟨1668779, by rfl⟩ : syracuseStep 2225039 = 3337559) B3337559
theorem B3337565 : Blo 2223435 3337565 := bbase (se 3 (by rfl) ⟨625793, by rfl⟩ : syracuseStep 3337565 = 1251587) (by norm_num)
theorem B2225043 : Blo 2223435 2225043 := bstep (se 1 (by rfl) ⟨1668782, by rfl⟩ : syracuseStep 2225043 = 3337565) B3337565
theorem B5006357 : Blo 2223435 5006357 := bbase (se 6 (by rfl) ⟨117336, by rfl⟩ : syracuseStep 5006357 = 234673) (by norm_num)
theorem B3337571 : Blo 2223435 3337571 := bstep (se 1 (by rfl) ⟨2503178, by rfl⟩ : syracuseStep 3337571 = 5006357) B5006357
theorem B2225047 : Blo 2223435 2225047 := bstep (se 1 (by rfl) ⟨1668785, by rfl⟩ : syracuseStep 2225047 = 3337571) B3337571
theorem B8448245 : Blo 2223435 8448245 := bbase (se 5 (by rfl) ⟨396011, by rfl⟩ : syracuseStep 8448245 = 792023) (by norm_num)
theorem B5632163 : Blo 2223435 5632163 := bstep (se 1 (by rfl) ⟨4224122, by rfl⟩ : syracuseStep 5632163 = 8448245) B8448245
theorem B3754775 : Blo 2223435 3754775 := bstep (se 1 (by rfl) ⟨2816081, by rfl⟩ : syracuseStep 3754775 = 5632163) B5632163
theorem B2503183 : Blo 2223435 2503183 := bstep (se 1 (by rfl) ⟨1877387, by rfl⟩ : syracuseStep 2503183 = 3754775) B3754775
theorem B3337577 : Blo 2223435 3337577 := bstep (se 2 (by rfl) ⟨1251591, by rfl⟩ : syracuseStep 3337577 = 2503183) B2503183
theorem B2225051 : Blo 2223435 2225051 := bstep (se 1 (by rfl) ⟨1668788, by rfl⟩ : syracuseStep 2225051 = 3337577) B3337577
theorem B2376073 : Blo 2223435 2376073 := bbase (se 2 (by rfl) ⟨891027, by rfl⟩ : syracuseStep 2376073 = 1782055) (by norm_num)
theorem B12672389 : Blo 2223435 12672389 := bstep (se 4 (by rfl) ⟨1188036, by rfl⟩ : syracuseStep 12672389 = 2376073) B2376073
theorem B8448259 : Blo 2223435 8448259 := bstep (se 1 (by rfl) ⟨6336194, by rfl⟩ : syracuseStep 8448259 = 12672389) B12672389
theorem B11264345 : Blo 2223435 11264345 := bstep (se 2 (by rfl) ⟨4224129, by rfl⟩ : syracuseStep 11264345 = 8448259) B8448259
theorem B7509563 : Blo 2223435 7509563 := bstep (se 1 (by rfl) ⟨5632172, by rfl⟩ : syracuseStep 7509563 = 11264345) B11264345
theorem B5006375 : Blo 2223435 5006375 := bstep (se 1 (by rfl) ⟨3754781, by rfl⟩ : syracuseStep 5006375 = 7509563) B7509563
theorem B3337583 : Blo 2223435 3337583 := bstep (se 1 (by rfl) ⟨2503187, by rfl⟩ : syracuseStep 3337583 = 5006375) B5006375
theorem B2225055 : Blo 2223435 2225055 := bstep (se 1 (by rfl) ⟨1668791, by rfl⟩ : syracuseStep 2225055 = 3337583) B3337583
theorem B3337589 : Blo 2223435 3337589 := bbase (se 5 (by rfl) ⟨156449, by rfl⟩ : syracuseStep 3337589 = 312899) (by norm_num)
theorem B2225059 : Blo 2223435 2225059 := bstep (se 1 (by rfl) ⟨1668794, by rfl⟩ : syracuseStep 2225059 = 3337589) B3337589
theorem B3168109 : Blo 2223435 3168109 := bbase (se 3 (by rfl) ⟨594020, by rfl⟩ : syracuseStep 3168109 = 1188041) (by norm_num)
theorem B4224145 : Blo 2223435 4224145 := bstep (se 2 (by rfl) ⟨1584054, by rfl⟩ : syracuseStep 4224145 = 3168109) B3168109
theorem B5632193 : Blo 2223435 5632193 := bstep (se 2 (by rfl) ⟨2112072, by rfl⟩ : syracuseStep 5632193 = 4224145) B4224145
theorem B3754795 : Blo 2223435 3754795 := bstep (se 1 (by rfl) ⟨2816096, by rfl⟩ : syracuseStep 3754795 = 5632193) B5632193
theorem B5006393 : Blo 2223435 5006393 := bstep (se 2 (by rfl) ⟨1877397, by rfl⟩ : syracuseStep 5006393 = 3754795) B3754795
theorem B3337595 : Blo 2223435 3337595 := bstep (se 1 (by rfl) ⟨2503196, by rfl⟩ : syracuseStep 3337595 = 5006393) B5006393
theorem B2225063 : Blo 2223435 2225063 := bstep (se 1 (by rfl) ⟨1668797, by rfl⟩ : syracuseStep 2225063 = 3337595) B3337595
theorem B2503201 : Blo 2223435 2503201 := bbase (se 2 (by rfl) ⟨938700, by rfl⟩ : syracuseStep 2503201 = 1877401) (by norm_num)
theorem B3337601 : Blo 2223435 3337601 := bstep (se 2 (by rfl) ⟨1251600, by rfl⟩ : syracuseStep 3337601 = 2503201) B2503201
theorem B2225067 : Blo 2223435 2225067 := bstep (se 1 (by rfl) ⟨1668800, by rfl⟩ : syracuseStep 2225067 = 3337601) B3337601
theorem B5632213 : Blo 2223435 5632213 := bbase (se 7 (by rfl) ⟨66002, by rfl⟩ : syracuseStep 5632213 = 132005) (by norm_num)
theorem B7509617 : Blo 2223435 7509617 := bstep (se 2 (by rfl) ⟨2816106, by rfl⟩ : syracuseStep 7509617 = 5632213) B5632213
theorem B5006411 : Blo 2223435 5006411 := bstep (se 1 (by rfl) ⟨3754808, by rfl⟩ : syracuseStep 5006411 = 7509617) B7509617
theorem B3337607 : Blo 2223435 3337607 := bstep (se 1 (by rfl) ⟨2503205, by rfl⟩ : syracuseStep 3337607 = 5006411) B5006411
theorem B2225071 : Blo 2223435 2225071 := bstep (se 1 (by rfl) ⟨1668803, by rfl⟩ : syracuseStep 2225071 = 3337607) B3337607
theorem B3337613 : Blo 2223435 3337613 := bbase (se 3 (by rfl) ⟨625802, by rfl⟩ : syracuseStep 3337613 = 1251605) (by norm_num)
theorem B2225075 : Blo 2223435 2225075 := bstep (se 1 (by rfl) ⟨1668806, by rfl⟩ : syracuseStep 2225075 = 3337613) B3337613
theorem B5006429 : Blo 2223435 5006429 := bbase (se 3 (by rfl) ⟨938705, by rfl⟩ : syracuseStep 5006429 = 1877411) (by norm_num)
theorem B3337619 : Blo 2223435 3337619 := bstep (se 1 (by rfl) ⟨2503214, by rfl⟩ : syracuseStep 3337619 = 5006429) B5006429
theorem B2225079 : Blo 2223435 2225079 := bstep (se 1 (by rfl) ⟨1668809, by rfl⟩ : syracuseStep 2225079 = 3337619) B3337619
theorem B3754829 : Blo 2223435 3754829 := bbase (se 3 (by rfl) ⟨704030, by rfl⟩ : syracuseStep 3754829 = 1408061) (by norm_num)
theorem B2503219 : Blo 2223435 2503219 := bstep (se 1 (by rfl) ⟨1877414, by rfl⟩ : syracuseStep 2503219 = 3754829) B3754829
theorem B3337625 : Blo 2223435 3337625 := bstep (se 2 (by rfl) ⟨1251609, by rfl⟩ : syracuseStep 3337625 = 2503219) B2503219
theorem B2225083 : Blo 2223435 2225083 := bstep (se 1 (by rfl) ⟨1668812, by rfl⟩ : syracuseStep 2225083 = 3337625) B3337625
theorem B3007261 : Blo 2223435 3007261 := bbase (se 3 (by rfl) ⟨563861, by rfl⟩ : syracuseStep 3007261 = 1127723) (by norm_num)
theorem B4009681 : Blo 2223435 4009681 := bstep (se 2 (by rfl) ⟨1503630, by rfl⟩ : syracuseStep 4009681 = 3007261) B3007261
theorem B21384965 : Blo 2223435 21384965 := bstep (se 4 (by rfl) ⟨2004840, by rfl⟩ : syracuseStep 21384965 = 4009681) B4009681
theorem B14256643 : Blo 2223435 14256643 := bstep (se 1 (by rfl) ⟨10692482, by rfl⟩ : syracuseStep 14256643 = 21384965) B21384965
theorem B19008857 : Blo 2223435 19008857 := bstep (se 2 (by rfl) ⟨7128321, by rfl⟩ : syracuseStep 19008857 = 14256643) B14256643
theorem B12672571 : Blo 2223435 12672571 := bstep (se 1 (by rfl) ⟨9504428, by rfl⟩ : syracuseStep 12672571 = 19008857) B19008857
theorem B16896761 : Blo 2223435 16896761 := bstep (se 2 (by rfl) ⟨6336285, by rfl⟩ : syracuseStep 16896761 = 12672571) B12672571
theorem B11264507 : Blo 2223435 11264507 := bstep (se 1 (by rfl) ⟨8448380, by rfl⟩ : syracuseStep 11264507 = 16896761) B16896761
theorem B7509671 : Blo 2223435 7509671 := bstep (se 1 (by rfl) ⟨5632253, by rfl⟩ : syracuseStep 7509671 = 11264507) B11264507
theorem B5006447 : Blo 2223435 5006447 := bstep (se 1 (by rfl) ⟨3754835, by rfl⟩ : syracuseStep 5006447 = 7509671) B7509671
theorem B3337631 : Blo 2223435 3337631 := bstep (se 1 (by rfl) ⟨2503223, by rfl⟩ : syracuseStep 3337631 = 5006447) B5006447
theorem B2225087 : Blo 2223435 2225087 := bstep (se 1 (by rfl) ⟨1668815, by rfl⟩ : syracuseStep 2225087 = 3337631) B3337631
theorem B3337637 : Blo 2223435 3337637 := bbase (se 4 (by rfl) ⟨312903, by rfl⟩ : syracuseStep 3337637 = 625807) (by norm_num)
theorem B2225091 : Blo 2223435 2225091 := bstep (se 1 (by rfl) ⟨1668818, by rfl⟩ : syracuseStep 2225091 = 3337637) B3337637
theorem B2816137 : Blo 2223435 2816137 := bbase (se 2 (by rfl) ⟨1056051, by rfl⟩ : syracuseStep 2816137 = 2112103) (by norm_num)
theorem B3754849 : Blo 2223435 3754849 := bstep (se 2 (by rfl) ⟨1408068, by rfl⟩ : syracuseStep 3754849 = 2816137) B2816137
theorem B5006465 : Blo 2223435 5006465 := bstep (se 2 (by rfl) ⟨1877424, by rfl⟩ : syracuseStep 5006465 = 3754849) B3754849
theorem B3337643 : Blo 2223435 3337643 := bstep (se 1 (by rfl) ⟨2503232, by rfl⟩ : syracuseStep 3337643 = 5006465) B5006465
theorem B2225095 : Blo 2223435 2225095 := bstep (se 1 (by rfl) ⟨1668821, by rfl⟩ : syracuseStep 2225095 = 3337643) B3337643
theorem B2503237 : Blo 2223435 2503237 := bbase (se 4 (by rfl) ⟨234678, by rfl⟩ : syracuseStep 2503237 = 469357) (by norm_num)
theorem B3337649 : Blo 2223435 3337649 := bstep (se 2 (by rfl) ⟨1251618, by rfl⟩ : syracuseStep 3337649 = 2503237) B2503237
theorem B2225099 : Blo 2223435 2225099 := bstep (se 1 (by rfl) ⟨1668824, by rfl⟩ : syracuseStep 2225099 = 3337649) B3337649
theorem B4224221 : Blo 2223435 4224221 := bbase (se 3 (by rfl) ⟨792041, by rfl⟩ : syracuseStep 4224221 = 1584083) (by norm_num)
theorem B2816147 : Blo 2223435 2816147 := bstep (se 1 (by rfl) ⟨2112110, by rfl⟩ : syracuseStep 2816147 = 4224221) B4224221
theorem B7509725 : Blo 2223435 7509725 := bstep (se 3 (by rfl) ⟨1408073, by rfl⟩ : syracuseStep 7509725 = 2816147) B2816147
theorem B5006483 : Blo 2223435 5006483 := bstep (se 1 (by rfl) ⟨3754862, by rfl⟩ : syracuseStep 5006483 = 7509725) B7509725
theorem B3337655 : Blo 2223435 3337655 := bstep (se 1 (by rfl) ⟨2503241, by rfl⟩ : syracuseStep 3337655 = 5006483) B5006483
theorem B2225103 : Blo 2223435 2225103 := bstep (se 1 (by rfl) ⟨1668827, by rfl⟩ : syracuseStep 2225103 = 3337655) B3337655
theorem B3337661 : Blo 2223435 3337661 := bbase (se 3 (by rfl) ⟨625811, by rfl⟩ : syracuseStep 3337661 = 1251623) (by norm_num)
theorem B2225107 : Blo 2223435 2225107 := bstep (se 1 (by rfl) ⟨1668830, by rfl⟩ : syracuseStep 2225107 = 3337661) B3337661
theorem B5006501 : Blo 2223435 5006501 := bbase (se 4 (by rfl) ⟨469359, by rfl⟩ : syracuseStep 5006501 = 938719) (by norm_num)
theorem B3337667 : Blo 2223435 3337667 := bstep (se 1 (by rfl) ⟨2503250, by rfl⟩ : syracuseStep 3337667 = 5006501) B5006501
theorem B2225111 : Blo 2223435 2225111 := bstep (se 1 (by rfl) ⟨1668833, by rfl⟩ : syracuseStep 2225111 = 3337667) B3337667
theorem B5632325 : Blo 2223435 5632325 := bbase (se 4 (by rfl) ⟨528030, by rfl⟩ : syracuseStep 5632325 = 1056061) (by norm_num)
theorem B3754883 : Blo 2223435 3754883 := bstep (se 1 (by rfl) ⟨2816162, by rfl⟩ : syracuseStep 3754883 = 5632325) B5632325
theorem B2503255 : Blo 2223435 2503255 := bstep (se 1 (by rfl) ⟨1877441, by rfl⟩ : syracuseStep 2503255 = 3754883) B3754883
theorem B3337673 : Blo 2223435 3337673 := bstep (se 2 (by rfl) ⟨1251627, by rfl⟩ : syracuseStep 3337673 = 2503255) B2503255
theorem B2225115 : Blo 2223435 2225115 := bstep (se 1 (by rfl) ⟨1668836, by rfl⟩ : syracuseStep 2225115 = 3337673) B3337673
theorem B18043829 : Blo 2223435 18043829 := bbase (se 5 (by rfl) ⟨845804, by rfl⟩ : syracuseStep 18043829 = 1691609) (by norm_num)
theorem B12029219 : Blo 2223435 12029219 := bstep (se 1 (by rfl) ⟨9021914, by rfl⟩ : syracuseStep 12029219 = 18043829) B18043829
theorem B8019479 : Blo 2223435 8019479 := bstep (se 1 (by rfl) ⟨6014609, by rfl⟩ : syracuseStep 8019479 = 12029219) B12029219
theorem B5346319 : Blo 2223435 5346319 := bstep (se 1 (by rfl) ⟨4009739, by rfl⟩ : syracuseStep 5346319 = 8019479) B8019479
theorem B7128425 : Blo 2223435 7128425 := bstep (se 2 (by rfl) ⟨2673159, by rfl⟩ : syracuseStep 7128425 = 5346319) B5346319
theorem B4752283 : Blo 2223435 4752283 := bstep (se 1 (by rfl) ⟨3564212, by rfl⟩ : syracuseStep 4752283 = 7128425) B7128425
theorem B6336377 : Blo 2223435 6336377 := bstep (se 2 (by rfl) ⟨2376141, by rfl⟩ : syracuseStep 6336377 = 4752283) B4752283
theorem B4224251 : Blo 2223435 4224251 := bstep (se 1 (by rfl) ⟨3168188, by rfl⟩ : syracuseStep 4224251 = 6336377) B6336377
theorem B11264669 : Blo 2223435 11264669 := bstep (se 3 (by rfl) ⟨2112125, by rfl⟩ : syracuseStep 11264669 = 4224251) B4224251
theorem B7509779 : Blo 2223435 7509779 := bstep (se 1 (by rfl) ⟨5632334, by rfl⟩ : syracuseStep 7509779 = 11264669) B11264669
theorem B5006519 : Blo 2223435 5006519 := bstep (se 1 (by rfl) ⟨3754889, by rfl⟩ : syracuseStep 5006519 = 7509779) B7509779
theorem B3337679 : Blo 2223435 3337679 := bstep (se 1 (by rfl) ⟨2503259, by rfl⟩ : syracuseStep 3337679 = 5006519) B5006519
theorem B2225119 : Blo 2223435 2225119 := bstep (se 1 (by rfl) ⟨1668839, by rfl⟩ : syracuseStep 2225119 = 3337679) B3337679
theorem B3337685 : Blo 2223435 3337685 := bbase (se 7 (by rfl) ⟨39113, by rfl⟩ : syracuseStep 3337685 = 78227) (by norm_num)
theorem B2225123 : Blo 2223435 2225123 := bstep (se 1 (by rfl) ⟨1668842, by rfl⟩ : syracuseStep 2225123 = 3337685) B3337685
theorem B8448533 : Blo 2223435 8448533 := bbase (se 6 (by rfl) ⟨198012, by rfl⟩ : syracuseStep 8448533 = 396025) (by norm_num)
theorem B5632355 : Blo 2223435 5632355 := bstep (se 1 (by rfl) ⟨4224266, by rfl⟩ : syracuseStep 5632355 = 8448533) B8448533
theorem B3754903 : Blo 2223435 3754903 := bstep (se 1 (by rfl) ⟨2816177, by rfl⟩ : syracuseStep 3754903 = 5632355) B5632355
theorem B5006537 : Blo 2223435 5006537 := bstep (se 2 (by rfl) ⟨1877451, by rfl⟩ : syracuseStep 5006537 = 3754903) B3754903
theorem B3337691 : Blo 2223435 3337691 := bstep (se 1 (by rfl) ⟨2503268, by rfl⟩ : syracuseStep 3337691 = 5006537) B5006537
theorem B2225127 : Blo 2223435 2225127 := bstep (se 1 (by rfl) ⟨1668845, by rfl⟩ : syracuseStep 2225127 = 3337691) B3337691
theorem B2503273 : Blo 2223435 2503273 := bbase (se 2 (by rfl) ⟨938727, by rfl⟩ : syracuseStep 2503273 = 1877455) (by norm_num)
theorem B3337697 : Blo 2223435 3337697 := bstep (se 2 (by rfl) ⟨1251636, by rfl⟩ : syracuseStep 3337697 = 2503273) B2503273
theorem B2225131 : Blo 2223435 2225131 := bstep (se 1 (by rfl) ⟨1668848, by rfl⟩ : syracuseStep 2225131 = 3337697) B3337697
theorem B4752317 : Blo 2223435 4752317 := bbase (se 3 (by rfl) ⟨891059, by rfl⟩ : syracuseStep 4752317 = 1782119) (by norm_num)
theorem B12672845 : Blo 2223435 12672845 := bstep (se 3 (by rfl) ⟨2376158, by rfl⟩ : syracuseStep 12672845 = 4752317) B4752317
theorem B8448563 : Blo 2223435 8448563 := bstep (se 1 (by rfl) ⟨6336422, by rfl⟩ : syracuseStep 8448563 = 12672845) B12672845
theorem B5632375 : Blo 2223435 5632375 := bstep (se 1 (by rfl) ⟨4224281, by rfl⟩ : syracuseStep 5632375 = 8448563) B8448563
theorem B7509833 : Blo 2223435 7509833 := bstep (se 2 (by rfl) ⟨2816187, by rfl⟩ : syracuseStep 7509833 = 5632375) B5632375
theorem B5006555 : Blo 2223435 5006555 := bstep (se 1 (by rfl) ⟨3754916, by rfl⟩ : syracuseStep 5006555 = 7509833) B7509833
theorem B3337703 : Blo 2223435 3337703 := bstep (se 1 (by rfl) ⟨2503277, by rfl⟩ : syracuseStep 3337703 = 5006555) B5006555
theorem B2225135 : Blo 2223435 2225135 := bstep (se 1 (by rfl) ⟨1668851, by rfl⟩ : syracuseStep 2225135 = 3337703) B3337703
theorem B3337709 : Blo 2223435 3337709 := bbase (se 3 (by rfl) ⟨625820, by rfl⟩ : syracuseStep 3337709 = 1251641) (by norm_num)
theorem B2225139 : Blo 2223435 2225139 := bstep (se 1 (by rfl) ⟨1668854, by rfl⟩ : syracuseStep 2225139 = 3337709) B3337709
theorem B5006573 : Blo 2223435 5006573 := bbase (se 3 (by rfl) ⟨938732, by rfl⟩ : syracuseStep 5006573 = 1877465) (by norm_num)
theorem B3337715 : Blo 2223435 3337715 := bstep (se 1 (by rfl) ⟨2503286, by rfl⟩ : syracuseStep 3337715 = 5006573) B5006573
theorem B2225143 : Blo 2223435 2225143 := bstep (se 1 (by rfl) ⟨1668857, by rfl⟩ : syracuseStep 2225143 = 3337715) B3337715
theorem B3168229 : Blo 2223435 3168229 := bbase (se 4 (by rfl) ⟨297021, by rfl⟩ : syracuseStep 3168229 = 594043) (by norm_num)
theorem B4224305 : Blo 2223435 4224305 := bstep (se 2 (by rfl) ⟨1584114, by rfl⟩ : syracuseStep 4224305 = 3168229) B3168229
theorem B2816203 : Blo 2223435 2816203 := bstep (se 1 (by rfl) ⟨2112152, by rfl⟩ : syracuseStep 2816203 = 4224305) B4224305
theorem B3754937 : Blo 2223435 3754937 := bstep (se 2 (by rfl) ⟨1408101, by rfl⟩ : syracuseStep 3754937 = 2816203) B2816203
theorem B2503291 : Blo 2223435 2503291 := bstep (se 1 (by rfl) ⟨1877468, by rfl⟩ : syracuseStep 2503291 = 3754937) B3754937
theorem B3337721 : Blo 2223435 3337721 := bstep (se 2 (by rfl) ⟨1251645, by rfl⟩ : syracuseStep 3337721 = 2503291) B2503291
theorem B2225147 : Blo 2223435 2225147 := bstep (se 1 (by rfl) ⟨1668860, by rfl⟩ : syracuseStep 2225147 = 3337721) B3337721
theorem B10149797 : Blo 2223435 10149797 := bbase (se 4 (by rfl) ⟨951543, by rfl⟩ : syracuseStep 10149797 = 1903087) (by norm_num)
theorem B27066125 : Blo 2223435 27066125 := bstep (se 3 (by rfl) ⟨5074898, by rfl⟩ : syracuseStep 27066125 = 10149797) B10149797
theorem B18044083 : Blo 2223435 18044083 := bstep (se 1 (by rfl) ⟨13533062, by rfl⟩ : syracuseStep 18044083 = 27066125) B27066125
theorem B24058777 : Blo 2223435 24058777 := bstep (se 2 (by rfl) ⟨9022041, by rfl⟩ : syracuseStep 24058777 = 18044083) B18044083
theorem B32078369 : Blo 2223435 32078369 := bstep (se 2 (by rfl) ⟨12029388, by rfl⟩ : syracuseStep 32078369 = 24058777) B24058777
theorem B85542317 : Blo 2223435 85542317 := bstep (se 3 (by rfl) ⟨16039184, by rfl⟩ : syracuseStep 85542317 = 32078369) B32078369
theorem B57028211 : Blo 2223435 57028211 := bstep (se 1 (by rfl) ⟨42771158, by rfl⟩ : syracuseStep 57028211 = 85542317) B85542317
theorem B38018807 : Blo 2223435 38018807 := bstep (se 1 (by rfl) ⟨28514105, by rfl⟩ : syracuseStep 38018807 = 57028211) B57028211
theorem B25345871 : Blo 2223435 25345871 := bstep (se 1 (by rfl) ⟨19009403, by rfl⟩ : syracuseStep 25345871 = 38018807) B38018807
theorem B16897247 : Blo 2223435 16897247 := bstep (se 1 (by rfl) ⟨12672935, by rfl⟩ : syracuseStep 16897247 = 25345871) B25345871
theorem B11264831 : Blo 2223435 11264831 := bstep (se 1 (by rfl) ⟨8448623, by rfl⟩ : syracuseStep 11264831 = 16897247) B16897247
theorem B7509887 : Blo 2223435 7509887 := bstep (se 1 (by rfl) ⟨5632415, by rfl⟩ : syracuseStep 7509887 = 11264831) B11264831
theorem B5006591 : Blo 2223435 5006591 := bstep (se 1 (by rfl) ⟨3754943, by rfl⟩ : syracuseStep 5006591 = 7509887) B7509887
theorem B3337727 : Blo 2223435 3337727 := bstep (se 1 (by rfl) ⟨2503295, by rfl⟩ : syracuseStep 3337727 = 5006591) B5006591
theorem B2225151 : Blo 2223435 2225151 := bstep (se 1 (by rfl) ⟨1668863, by rfl⟩ : syracuseStep 2225151 = 3337727) B3337727
theorem B3337733 : Blo 2223435 3337733 := bbase (se 4 (by rfl) ⟨312912, by rfl⟩ : syracuseStep 3337733 = 625825) (by norm_num)
theorem B2225155 : Blo 2223435 2225155 := bstep (se 1 (by rfl) ⟨1668866, by rfl⟩ : syracuseStep 2225155 = 3337733) B3337733
theorem B3754957 : Blo 2223435 3754957 := bbase (se 3 (by rfl) ⟨704054, by rfl⟩ : syracuseStep 3754957 = 1408109) (by norm_num)
theorem B5006609 : Blo 2223435 5006609 := bstep (se 2 (by rfl) ⟨1877478, by rfl⟩ : syracuseStep 5006609 = 3754957) B3754957
theorem B3337739 : Blo 2223435 3337739 := bstep (se 1 (by rfl) ⟨2503304, by rfl⟩ : syracuseStep 3337739 = 5006609) B5006609
theorem B2225159 : Blo 2223435 2225159 := bstep (se 1 (by rfl) ⟨1668869, by rfl⟩ : syracuseStep 2225159 = 3337739) B3337739
theorem B2503309 : Blo 2223435 2503309 := bbase (se 3 (by rfl) ⟨469370, by rfl⟩ : syracuseStep 2503309 = 938741) (by norm_num)
theorem B3337745 : Blo 2223435 3337745 := bstep (se 2 (by rfl) ⟨1251654, by rfl⟩ : syracuseStep 3337745 = 2503309) B2503309
theorem B2225163 : Blo 2223435 2225163 := bstep (se 1 (by rfl) ⟨1668872, by rfl⟩ : syracuseStep 2225163 = 3337745) B3337745
theorem B7509941 : Blo 2223435 7509941 := bbase (se 5 (by rfl) ⟨352028, by rfl⟩ : syracuseStep 7509941 = 704057) (by norm_num)
theorem B5006627 : Blo 2223435 5006627 := bstep (se 1 (by rfl) ⟨3754970, by rfl⟩ : syracuseStep 5006627 = 7509941) B7509941
theorem B3337751 : Blo 2223435 3337751 := bstep (se 1 (by rfl) ⟨2503313, by rfl⟩ : syracuseStep 3337751 = 5006627) B5006627
theorem B2225167 : Blo 2223435 2225167 := bstep (se 1 (by rfl) ⟨1668875, by rfl⟩ : syracuseStep 2225167 = 3337751) B3337751
theorem B3337757 : Blo 2223435 3337757 := bbase (se 3 (by rfl) ⟨625829, by rfl⟩ : syracuseStep 3337757 = 1251659) (by norm_num)
theorem B2225171 : Blo 2223435 2225171 := bstep (se 1 (by rfl) ⟨1668878, by rfl⟩ : syracuseStep 2225171 = 3337757) B3337757
theorem B5006645 : Blo 2223435 5006645 := bbase (se 5 (by rfl) ⟨234686, by rfl⟩ : syracuseStep 5006645 = 469373) (by norm_num)
theorem B3337763 : Blo 2223435 3337763 := bstep (se 1 (by rfl) ⟨2503322, by rfl⟩ : syracuseStep 3337763 = 5006645) B5006645
theorem B2225175 : Blo 2223435 2225175 := bstep (se 1 (by rfl) ⟨1668881, by rfl⟩ : syracuseStep 2225175 = 3337763) B3337763
theorem B7225877 : Blo 2223435 7225877 := bbase (se 6 (by rfl) ⟨169356, by rfl⟩ : syracuseStep 7225877 = 338713) (by norm_num)
theorem B4817251 : Blo 2223435 4817251 := bstep (se 1 (by rfl) ⟨3612938, by rfl⟩ : syracuseStep 4817251 = 7225877) B7225877
theorem B25692005 : Blo 2223435 25692005 := bstep (se 4 (by rfl) ⟨2408625, by rfl⟩ : syracuseStep 25692005 = 4817251) B4817251
theorem B68512013 : Blo 2223435 68512013 := bstep (se 3 (by rfl) ⟨12846002, by rfl⟩ : syracuseStep 68512013 = 25692005) B25692005
theorem B45674675 : Blo 2223435 45674675 := bstep (se 1 (by rfl) ⟨34256006, by rfl⟩ : syracuseStep 45674675 = 68512013) B68512013
theorem B30449783 : Blo 2223435 30449783 := bstep (se 1 (by rfl) ⟨22837337, by rfl⟩ : syracuseStep 30449783 = 45674675) B45674675
theorem B20299855 : Blo 2223435 20299855 := bstep (se 1 (by rfl) ⟨15224891, by rfl⟩ : syracuseStep 20299855 = 30449783) B30449783
theorem B27066473 : Blo 2223435 27066473 := bstep (se 2 (by rfl) ⟨10149927, by rfl⟩ : syracuseStep 27066473 = 20299855) B20299855
theorem B18044315 : Blo 2223435 18044315 := bstep (se 1 (by rfl) ⟨13533236, by rfl⟩ : syracuseStep 18044315 = 27066473) B27066473
theorem B12029543 : Blo 2223435 12029543 := bstep (se 1 (by rfl) ⟨9022157, by rfl⟩ : syracuseStep 12029543 = 18044315) B18044315
theorem B8019695 : Blo 2223435 8019695 := bstep (se 1 (by rfl) ⟨6014771, by rfl⟩ : syracuseStep 8019695 = 12029543) B12029543
theorem B21385853 : Blo 2223435 21385853 := bstep (se 3 (by rfl) ⟨4009847, by rfl⟩ : syracuseStep 21385853 = 8019695) B8019695
theorem B14257235 : Blo 2223435 14257235 := bstep (se 1 (by rfl) ⟨10692926, by rfl⟩ : syracuseStep 14257235 = 21385853) B21385853
theorem B9504823 : Blo 2223435 9504823 := bstep (se 1 (by rfl) ⟨7128617, by rfl⟩ : syracuseStep 9504823 = 14257235) B14257235
theorem B12673097 : Blo 2223435 12673097 := bstep (se 2 (by rfl) ⟨4752411, by rfl⟩ : syracuseStep 12673097 = 9504823) B9504823
theorem B8448731 : Blo 2223435 8448731 := bstep (se 1 (by rfl) ⟨6336548, by rfl⟩ : syracuseStep 8448731 = 12673097) B12673097
theorem B5632487 : Blo 2223435 5632487 := bstep (se 1 (by rfl) ⟨4224365, by rfl⟩ : syracuseStep 5632487 = 8448731) B8448731
theorem B3754991 : Blo 2223435 3754991 := bstep (se 1 (by rfl) ⟨2816243, by rfl⟩ : syracuseStep 3754991 = 5632487) B5632487
theorem B2503327 : Blo 2223435 2503327 := bstep (se 1 (by rfl) ⟨1877495, by rfl⟩ : syracuseStep 2503327 = 3754991) B3754991
theorem B3337769 : Blo 2223435 3337769 := bstep (se 2 (by rfl) ⟨1251663, by rfl⟩ : syracuseStep 3337769 = 2503327) B2503327
theorem B2225179 : Blo 2223435 2225179 := bstep (se 1 (by rfl) ⟨1668884, by rfl⟩ : syracuseStep 2225179 = 3337769) B3337769
theorem B15224917 : Blo 2223435 15224917 := bbase (se 8 (by rfl) ⟨89208, by rfl⟩ : syracuseStep 15224917 = 178417) (by norm_num)
theorem B20299889 : Blo 2223435 20299889 := bstep (se 2 (by rfl) ⟨7612458, by rfl⟩ : syracuseStep 20299889 = 15224917) B15224917
theorem B13533259 : Blo 2223435 13533259 := bstep (se 1 (by rfl) ⟨10149944, by rfl⟩ : syracuseStep 13533259 = 20299889) B20299889
theorem B18044345 : Blo 2223435 18044345 := bstep (se 2 (by rfl) ⟨6766629, by rfl⟩ : syracuseStep 18044345 = 13533259) B13533259
theorem B12029563 : Blo 2223435 12029563 := bstep (se 1 (by rfl) ⟨9022172, by rfl⟩ : syracuseStep 12029563 = 18044345) B18044345
theorem B16039417 : Blo 2223435 16039417 := bstep (se 2 (by rfl) ⟨6014781, by rfl⟩ : syracuseStep 16039417 = 12029563) B12029563
theorem B21385889 : Blo 2223435 21385889 := bstep (se 2 (by rfl) ⟨8019708, by rfl⟩ : syracuseStep 21385889 = 16039417) B16039417
theorem B14257259 : Blo 2223435 14257259 := bstep (se 1 (by rfl) ⟨10692944, by rfl⟩ : syracuseStep 14257259 = 21385889) B21385889
theorem B9504839 : Blo 2223435 9504839 := bstep (se 1 (by rfl) ⟨7128629, by rfl⟩ : syracuseStep 9504839 = 14257259) B14257259
theorem B6336559 : Blo 2223435 6336559 := bstep (se 1 (by rfl) ⟨4752419, by rfl⟩ : syracuseStep 6336559 = 9504839) B9504839
theorem B8448745 : Blo 2223435 8448745 := bstep (se 2 (by rfl) ⟨3168279, by rfl⟩ : syracuseStep 8448745 = 6336559) B6336559
theorem B11264993 : Blo 2223435 11264993 := bstep (se 2 (by rfl) ⟨4224372, by rfl⟩ : syracuseStep 11264993 = 8448745) B8448745
theorem B7509995 : Blo 2223435 7509995 := bstep (se 1 (by rfl) ⟨5632496, by rfl⟩ : syracuseStep 7509995 = 11264993) B11264993
theorem B5006663 : Blo 2223435 5006663 := bstep (se 1 (by rfl) ⟨3754997, by rfl⟩ : syracuseStep 5006663 = 7509995) B7509995
theorem B3337775 : Blo 2223435 3337775 := bstep (se 1 (by rfl) ⟨2503331, by rfl⟩ : syracuseStep 3337775 = 5006663) B5006663
theorem B2225183 : Blo 2223435 2225183 := bstep (se 1 (by rfl) ⟨1668887, by rfl⟩ : syracuseStep 2225183 = 3337775) B3337775
theorem B3337781 : Blo 2223435 3337781 := bbase (se 5 (by rfl) ⟨156458, by rfl⟩ : syracuseStep 3337781 = 312917) (by norm_num)
theorem B2225187 : Blo 2223435 2225187 := bstep (se 1 (by rfl) ⟨1668890, by rfl⟩ : syracuseStep 2225187 = 3337781) B3337781
theorem B5632517 : Blo 2223435 5632517 := bbase (se 4 (by rfl) ⟨528048, by rfl⟩ : syracuseStep 5632517 = 1056097) (by norm_num)
theorem B3755011 : Blo 2223435 3755011 := bstep (se 1 (by rfl) ⟨2816258, by rfl⟩ : syracuseStep 3755011 = 5632517) B5632517
theorem B5006681 : Blo 2223435 5006681 := bstep (se 2 (by rfl) ⟨1877505, by rfl⟩ : syracuseStep 5006681 = 3755011) B3755011
theorem B3337787 : Blo 2223435 3337787 := bstep (se 1 (by rfl) ⟨2503340, by rfl⟩ : syracuseStep 3337787 = 5006681) B5006681
theorem B2225191 : Blo 2223435 2225191 := bstep (se 1 (by rfl) ⟨1668893, by rfl⟩ : syracuseStep 2225191 = 3337787) B3337787
theorem B2503345 : Blo 2223435 2503345 := bbase (se 2 (by rfl) ⟨938754, by rfl⟩ : syracuseStep 2503345 = 1877509) (by norm_num)
theorem B3337793 : Blo 2223435 3337793 := bstep (se 2 (by rfl) ⟨1251672, by rfl⟩ : syracuseStep 3337793 = 2503345) B2503345
theorem B2225195 : Blo 2223435 2225195 := bstep (se 1 (by rfl) ⟨1668896, by rfl⟩ : syracuseStep 2225195 = 3337793) B3337793
theorem B3564341 : Blo 2223435 3564341 := bbase (se 5 (by rfl) ⟨167078, by rfl⟩ : syracuseStep 3564341 = 334157) (by norm_num)
theorem B2376227 : Blo 2223435 2376227 := bstep (se 1 (by rfl) ⟨1782170, by rfl⟩ : syracuseStep 2376227 = 3564341) B3564341
theorem B6336605 : Blo 2223435 6336605 := bstep (se 3 (by rfl) ⟨1188113, by rfl⟩ : syracuseStep 6336605 = 2376227) B2376227
theorem B4224403 : Blo 2223435 4224403 := bstep (se 1 (by rfl) ⟨3168302, by rfl⟩ : syracuseStep 4224403 = 6336605) B6336605
theorem B5632537 : Blo 2223435 5632537 := bstep (se 2 (by rfl) ⟨2112201, by rfl⟩ : syracuseStep 5632537 = 4224403) B4224403
theorem B7510049 : Blo 2223435 7510049 := bstep (se 2 (by rfl) ⟨2816268, by rfl⟩ : syracuseStep 7510049 = 5632537) B5632537
theorem B5006699 : Blo 2223435 5006699 := bstep (se 1 (by rfl) ⟨3755024, by rfl⟩ : syracuseStep 5006699 = 7510049) B7510049
theorem B3337799 : Blo 2223435 3337799 := bstep (se 1 (by rfl) ⟨2503349, by rfl⟩ : syracuseStep 3337799 = 5006699) B5006699
theorem B2225199 : Blo 2223435 2225199 := bstep (se 1 (by rfl) ⟨1668899, by rfl⟩ : syracuseStep 2225199 = 3337799) B3337799
theorem B3337805 : Blo 2223435 3337805 := bbase (se 3 (by rfl) ⟨625838, by rfl⟩ : syracuseStep 3337805 = 1251677) (by norm_num)
theorem B2225203 : Blo 2223435 2225203 := bstep (se 1 (by rfl) ⟨1668902, by rfl⟩ : syracuseStep 2225203 = 3337805) B3337805
theorem B5006717 : Blo 2223435 5006717 := bbase (se 3 (by rfl) ⟨938759, by rfl⟩ : syracuseStep 5006717 = 1877519) (by norm_num)
theorem B3337811 : Blo 2223435 3337811 := bstep (se 1 (by rfl) ⟨2503358, by rfl⟩ : syracuseStep 3337811 = 5006717) B5006717
theorem B2225207 : Blo 2223435 2225207 := bstep (se 1 (by rfl) ⟨1668905, by rfl⟩ : syracuseStep 2225207 = 3337811) B3337811
theorem B3755045 : Blo 2223435 3755045 := bbase (se 4 (by rfl) ⟨352035, by rfl⟩ : syracuseStep 3755045 = 704071) (by norm_num)
theorem B2503363 : Blo 2223435 2503363 := bstep (se 1 (by rfl) ⟨1877522, by rfl⟩ : syracuseStep 2503363 = 3755045) B3755045
theorem B3337817 : Blo 2223435 3337817 := bstep (se 2 (by rfl) ⟨1251681, by rfl⟩ : syracuseStep 3337817 = 2503363) B2503363
theorem B2225211 : Blo 2223435 2225211 := bstep (se 1 (by rfl) ⟨1668908, by rfl⟩ : syracuseStep 2225211 = 3337817) B3337817
theorem B3168325 : Blo 2223435 3168325 := bbase (se 4 (by rfl) ⟨297030, by rfl⟩ : syracuseStep 3168325 = 594061) (by norm_num)
theorem B16897733 : Blo 2223435 16897733 := bstep (se 4 (by rfl) ⟨1584162, by rfl⟩ : syracuseStep 16897733 = 3168325) B3168325
theorem B11265155 : Blo 2223435 11265155 := bstep (se 1 (by rfl) ⟨8448866, by rfl⟩ : syracuseStep 11265155 = 16897733) B16897733
theorem B7510103 : Blo 2223435 7510103 := bstep (se 1 (by rfl) ⟨5632577, by rfl⟩ : syracuseStep 7510103 = 11265155) B11265155
theorem B5006735 : Blo 2223435 5006735 := bstep (se 1 (by rfl) ⟨3755051, by rfl⟩ : syracuseStep 5006735 = 7510103) B7510103
theorem B3337823 : Blo 2223435 3337823 := bstep (se 1 (by rfl) ⟨2503367, by rfl⟩ : syracuseStep 3337823 = 5006735) B5006735
theorem B2225215 : Blo 2223435 2225215 := bstep (se 1 (by rfl) ⟨1668911, by rfl⟩ : syracuseStep 2225215 = 3337823) B3337823
theorem B3337829 : Blo 2223435 3337829 := bbase (se 4 (by rfl) ⟨312921, by rfl⟩ : syracuseStep 3337829 = 625843) (by norm_num)
theorem B2225219 : Blo 2223435 2225219 := bstep (se 1 (by rfl) ⟨1668914, by rfl⟩ : syracuseStep 2225219 = 3337829) B3337829
theorem B2376253 : Blo 2223435 2376253 := bbase (se 3 (by rfl) ⟨445547, by rfl⟩ : syracuseStep 2376253 = 891095) (by norm_num)
theorem B3168337 : Blo 2223435 3168337 := bstep (se 2 (by rfl) ⟨1188126, by rfl⟩ : syracuseStep 3168337 = 2376253) B2376253
theorem B4224449 : Blo 2223435 4224449 := bstep (se 2 (by rfl) ⟨1584168, by rfl⟩ : syracuseStep 4224449 = 3168337) B3168337
theorem B2816299 : Blo 2223435 2816299 := bstep (se 1 (by rfl) ⟨2112224, by rfl⟩ : syracuseStep 2816299 = 4224449) B4224449
theorem B3755065 : Blo 2223435 3755065 := bstep (se 2 (by rfl) ⟨1408149, by rfl⟩ : syracuseStep 3755065 = 2816299) B2816299
theorem B5006753 : Blo 2223435 5006753 := bstep (se 2 (by rfl) ⟨1877532, by rfl⟩ : syracuseStep 5006753 = 3755065) B3755065
theorem B3337835 : Blo 2223435 3337835 := bstep (se 1 (by rfl) ⟨2503376, by rfl⟩ : syracuseStep 3337835 = 5006753) B5006753
theorem B2225223 : Blo 2223435 2225223 := bstep (se 1 (by rfl) ⟨1668917, by rfl⟩ : syracuseStep 2225223 = 3337835) B3337835
theorem B2503381 : Blo 2223435 2503381 := bbase (se 7 (by rfl) ⟨29336, by rfl⟩ : syracuseStep 2503381 = 58673) (by norm_num)
theorem B3337841 : Blo 2223435 3337841 := bstep (se 2 (by rfl) ⟨1251690, by rfl⟩ : syracuseStep 3337841 = 2503381) B2503381
theorem B2225227 : Blo 2223435 2225227 := bstep (se 1 (by rfl) ⟨1668920, by rfl⟩ : syracuseStep 2225227 = 3337841) B3337841
theorem B2816309 : Blo 2223435 2816309 := bbase (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) (by norm_num)
theorem B7510157 : Blo 2223435 7510157 := bstep (se 3 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 7510157 = 2816309) B2816309
theorem B5006771 : Blo 2223435 5006771 := bstep (se 1 (by rfl) ⟨3755078, by rfl⟩ : syracuseStep 5006771 = 7510157) B7510157
theorem B3337847 : Blo 2223435 3337847 := bstep (se 1 (by rfl) ⟨2503385, by rfl⟩ : syracuseStep 3337847 = 5006771) B5006771
theorem B2225231 : Blo 2223435 2225231 := bstep (se 1 (by rfl) ⟨1668923, by rfl⟩ : syracuseStep 2225231 = 3337847) B3337847
theorem B3337853 : Blo 2223435 3337853 := bbase (se 3 (by rfl) ⟨625847, by rfl⟩ : syracuseStep 3337853 = 1251695) (by norm_num)
theorem B2225235 : Blo 2223435 2225235 := bstep (se 1 (by rfl) ⟨1668926, by rfl⟩ : syracuseStep 2225235 = 3337853) B3337853
theorem B5006789 : Blo 2223435 5006789 := bbase (se 4 (by rfl) ⟨469386, by rfl⟩ : syracuseStep 5006789 = 938773) (by norm_num)
theorem B3337859 : Blo 2223435 3337859 := bstep (se 1 (by rfl) ⟨2503394, by rfl⟩ : syracuseStep 3337859 = 5006789) B5006789
theorem B2225239 : Blo 2223435 2225239 := bstep (se 1 (by rfl) ⟨1668929, by rfl⟩ : syracuseStep 2225239 = 3337859) B3337859
theorem B5214541 : Blo 2223435 5214541 := bbase (se 3 (by rfl) ⟨977726, by rfl⟩ : syracuseStep 5214541 = 1955453) (by norm_num)
theorem B6952721 : Blo 2223435 6952721 := bstep (se 2 (by rfl) ⟨2607270, by rfl⟩ : syracuseStep 6952721 = 5214541) B5214541
theorem B18540589 : Blo 2223435 18540589 := bstep (se 3 (by rfl) ⟨3476360, by rfl⟩ : syracuseStep 18540589 = 6952721) B6952721
theorem B24720785 : Blo 2223435 24720785 := bstep (se 2 (by rfl) ⟨9270294, by rfl⟩ : syracuseStep 24720785 = 18540589) B18540589
theorem B16480523 : Blo 2223435 16480523 := bstep (se 1 (by rfl) ⟨12360392, by rfl⟩ : syracuseStep 16480523 = 24720785) B24720785
theorem B10987015 : Blo 2223435 10987015 := bstep (se 1 (by rfl) ⟨8240261, by rfl⟩ : syracuseStep 10987015 = 16480523) B16480523
theorem B14649353 : Blo 2223435 14649353 := bstep (se 2 (by rfl) ⟨5493507, by rfl⟩ : syracuseStep 14649353 = 10987015) B10987015
theorem B9766235 : Blo 2223435 9766235 := bstep (se 1 (by rfl) ⟨7324676, by rfl⟩ : syracuseStep 9766235 = 14649353) B14649353
theorem B6510823 : Blo 2223435 6510823 := bstep (se 1 (by rfl) ⟨4883117, by rfl⟩ : syracuseStep 6510823 = 9766235) B9766235
theorem B34724389 : Blo 2223435 34724389 := bstep (se 4 (by rfl) ⟨3255411, by rfl⟩ : syracuseStep 34724389 = 6510823) B6510823
theorem B46299185 : Blo 2223435 46299185 := bstep (se 2 (by rfl) ⟨17362194, by rfl⟩ : syracuseStep 46299185 = 34724389) B34724389
theorem B30866123 : Blo 2223435 30866123 := bstep (se 1 (by rfl) ⟨23149592, by rfl⟩ : syracuseStep 30866123 = 46299185) B46299185
theorem B20577415 : Blo 2223435 20577415 := bstep (se 1 (by rfl) ⟨15433061, by rfl⟩ : syracuseStep 20577415 = 30866123) B30866123
theorem B27436553 : Blo 2223435 27436553 := bstep (se 2 (by rfl) ⟨10288707, by rfl⟩ : syracuseStep 27436553 = 20577415) B20577415
theorem B18291035 : Blo 2223435 18291035 := bstep (se 1 (by rfl) ⟨13718276, by rfl⟩ : syracuseStep 18291035 = 27436553) B27436553
theorem B48776093 : Blo 2223435 48776093 := bstep (se 3 (by rfl) ⟨9145517, by rfl⟩ : syracuseStep 48776093 = 18291035) B18291035
theorem B32517395 : Blo 2223435 32517395 := bstep (se 1 (by rfl) ⟨24388046, by rfl⟩ : syracuseStep 32517395 = 48776093) B48776093
theorem B21678263 : Blo 2223435 21678263 := bstep (se 1 (by rfl) ⟨16258697, by rfl⟩ : syracuseStep 21678263 = 32517395) B32517395
theorem B14452175 : Blo 2223435 14452175 := bstep (se 1 (by rfl) ⟨10839131, by rfl⟩ : syracuseStep 14452175 = 21678263) B21678263
theorem B9634783 : Blo 2223435 9634783 := bstep (se 1 (by rfl) ⟨7226087, by rfl⟩ : syracuseStep 9634783 = 14452175) B14452175
theorem B12846377 : Blo 2223435 12846377 := bstep (se 2 (by rfl) ⟨4817391, by rfl⟩ : syracuseStep 12846377 = 9634783) B9634783
theorem B8564251 : Blo 2223435 8564251 := bstep (se 1 (by rfl) ⟨6423188, by rfl⟩ : syracuseStep 8564251 = 12846377) B12846377
theorem B11419001 : Blo 2223435 11419001 := bstep (se 2 (by rfl) ⟨4282125, by rfl⟩ : syracuseStep 11419001 = 8564251) B8564251
theorem B7612667 : Blo 2223435 7612667 := bstep (se 1 (by rfl) ⟨5709500, by rfl⟩ : syracuseStep 7612667 = 11419001) B11419001
theorem B5075111 : Blo 2223435 5075111 := bstep (se 1 (by rfl) ⟨3806333, by rfl⟩ : syracuseStep 5075111 = 7612667) B7612667
theorem B3383407 : Blo 2223435 3383407 := bstep (se 1 (by rfl) ⟨2537555, by rfl⟩ : syracuseStep 3383407 = 5075111) B5075111
theorem B4511209 : Blo 2223435 4511209 := bstep (se 2 (by rfl) ⟨1691703, by rfl⟩ : syracuseStep 4511209 = 3383407) B3383407
theorem B6014945 : Blo 2223435 6014945 := bstep (se 2 (by rfl) ⟨2255604, by rfl⟩ : syracuseStep 6014945 = 4511209) B4511209
theorem B16039853 : Blo 2223435 16039853 := bstep (se 3 (by rfl) ⟨3007472, by rfl⟩ : syracuseStep 16039853 = 6014945) B6014945
theorem B10693235 : Blo 2223435 10693235 := bstep (se 1 (by rfl) ⟨8019926, by rfl⟩ : syracuseStep 10693235 = 16039853) B16039853
theorem B7128823 : Blo 2223435 7128823 := bstep (se 1 (by rfl) ⟨5346617, by rfl⟩ : syracuseStep 7128823 = 10693235) B10693235
theorem B9505097 : Blo 2223435 9505097 := bstep (se 2 (by rfl) ⟨3564411, by rfl⟩ : syracuseStep 9505097 = 7128823) B7128823
theorem B6336731 : Blo 2223435 6336731 := bstep (se 1 (by rfl) ⟨4752548, by rfl⟩ : syracuseStep 6336731 = 9505097) B9505097
theorem B4224487 : Blo 2223435 4224487 := bstep (se 1 (by rfl) ⟨3168365, by rfl⟩ : syracuseStep 4224487 = 6336731) B6336731
theorem B5632649 : Blo 2223435 5632649 := bstep (se 2 (by rfl) ⟨2112243, by rfl⟩ : syracuseStep 5632649 = 4224487) B4224487
theorem B3755099 : Blo 2223435 3755099 := bstep (se 1 (by rfl) ⟨2816324, by rfl⟩ : syracuseStep 3755099 = 5632649) B5632649
theorem B2503399 : Blo 2223435 2503399 := bstep (se 1 (by rfl) ⟨1877549, by rfl⟩ : syracuseStep 2503399 = 3755099) B3755099
theorem B3337865 : Blo 2223435 3337865 := bstep (se 2 (by rfl) ⟨1251699, by rfl⟩ : syracuseStep 3337865 = 2503399) B2503399
theorem B2225243 : Blo 2223435 2225243 := bstep (se 1 (by rfl) ⟨1668932, by rfl⟩ : syracuseStep 2225243 = 3337865) B3337865
theorem B11265317 : Blo 2223435 11265317 := bbase (se 4 (by rfl) ⟨1056123, by rfl⟩ : syracuseStep 11265317 = 2112247) (by norm_num)
theorem B7510211 : Blo 2223435 7510211 := bstep (se 1 (by rfl) ⟨5632658, by rfl⟩ : syracuseStep 7510211 = 11265317) B11265317
theorem B5006807 : Blo 2223435 5006807 := bstep (se 1 (by rfl) ⟨3755105, by rfl⟩ : syracuseStep 5006807 = 7510211) B7510211
theorem B3337871 : Blo 2223435 3337871 := bstep (se 1 (by rfl) ⟨2503403, by rfl⟩ : syracuseStep 3337871 = 5006807) B5006807
theorem B2225247 : Blo 2223435 2225247 := bstep (se 1 (by rfl) ⟨1668935, by rfl⟩ : syracuseStep 2225247 = 3337871) B3337871
theorem B3337877 : Blo 2223435 3337877 := bbase (se 6 (by rfl) ⟨78231, by rfl⟩ : syracuseStep 3337877 = 156463) (by norm_num)
theorem B2225251 : Blo 2223435 2225251 := bstep (se 1 (by rfl) ⟨1668938, by rfl⟩ : syracuseStep 2225251 = 3337877) B3337877
theorem B2854765 : Blo 2223435 2854765 := bbase (se 3 (by rfl) ⟨535268, by rfl⟩ : syracuseStep 2854765 = 1070537) (by norm_num)
theorem B3806353 : Blo 2223435 3806353 := bstep (se 2 (by rfl) ⟨1427382, by rfl⟩ : syracuseStep 3806353 = 2854765) B2854765
theorem B5075137 : Blo 2223435 5075137 := bstep (se 2 (by rfl) ⟨1903176, by rfl⟩ : syracuseStep 5075137 = 3806353) B3806353
theorem B6766849 : Blo 2223435 6766849 := bstep (se 2 (by rfl) ⟨2537568, by rfl⟩ : syracuseStep 6766849 = 5075137) B5075137
theorem B9022465 : Blo 2223435 9022465 := bstep (se 2 (by rfl) ⟨3383424, by rfl⟩ : syracuseStep 9022465 = 6766849) B6766849
theorem B12029953 : Blo 2223435 12029953 := bstep (se 2 (by rfl) ⟨4511232, by rfl⟩ : syracuseStep 12029953 = 9022465) B9022465
theorem B16039937 : Blo 2223435 16039937 := bstep (se 2 (by rfl) ⟨6014976, by rfl⟩ : syracuseStep 16039937 = 12029953) B12029953
theorem B10693291 : Blo 2223435 10693291 := bstep (se 1 (by rfl) ⟨8019968, by rfl⟩ : syracuseStep 10693291 = 16039937) B16039937
theorem B14257721 : Blo 2223435 14257721 := bstep (se 2 (by rfl) ⟨5346645, by rfl⟩ : syracuseStep 14257721 = 10693291) B10693291
theorem B9505147 : Blo 2223435 9505147 := bstep (se 1 (by rfl) ⟨7128860, by rfl⟩ : syracuseStep 9505147 = 14257721) B14257721
theorem B12673529 : Blo 2223435 12673529 := bstep (se 2 (by rfl) ⟨4752573, by rfl⟩ : syracuseStep 12673529 = 9505147) B9505147
theorem B8449019 : Blo 2223435 8449019 := bstep (se 1 (by rfl) ⟨6336764, by rfl⟩ : syracuseStep 8449019 = 12673529) B12673529
theorem B5632679 : Blo 2223435 5632679 := bstep (se 1 (by rfl) ⟨4224509, by rfl⟩ : syracuseStep 5632679 = 8449019) B8449019
theorem B3755119 : Blo 2223435 3755119 := bstep (se 1 (by rfl) ⟨2816339, by rfl⟩ : syracuseStep 3755119 = 5632679) B5632679
theorem B5006825 : Blo 2223435 5006825 := bstep (se 2 (by rfl) ⟨1877559, by rfl⟩ : syracuseStep 5006825 = 3755119) B3755119
theorem B3337883 : Blo 2223435 3337883 := bstep (se 1 (by rfl) ⟨2503412, by rfl⟩ : syracuseStep 3337883 = 5006825) B5006825
theorem B2225255 : Blo 2223435 2225255 := bstep (se 1 (by rfl) ⟨1668941, by rfl⟩ : syracuseStep 2225255 = 3337883) B3337883
theorem B2503417 : Blo 2223435 2503417 := bbase (se 2 (by rfl) ⟨938781, by rfl⟩ : syracuseStep 2503417 = 1877563) (by norm_num)
theorem B3337889 : Blo 2223435 3337889 := bstep (se 2 (by rfl) ⟨1251708, by rfl⟩ : syracuseStep 3337889 = 2503417) B2503417
theorem B2225259 : Blo 2223435 2225259 := bstep (se 1 (by rfl) ⟨1668944, by rfl⟩ : syracuseStep 2225259 = 3337889) B3337889
theorem B13533749 : Blo 2223435 13533749 := bbase (se 5 (by rfl) ⟨634394, by rfl⟩ : syracuseStep 13533749 = 1268789) (by norm_num)
theorem B9022499 : Blo 2223435 9022499 := bstep (se 1 (by rfl) ⟨6766874, by rfl⟩ : syracuseStep 9022499 = 13533749) B13533749
theorem B6014999 : Blo 2223435 6014999 := bstep (se 1 (by rfl) ⟨4511249, by rfl⟩ : syracuseStep 6014999 = 9022499) B9022499
theorem B4009999 : Blo 2223435 4009999 := bstep (se 1 (by rfl) ⟨3007499, by rfl⟩ : syracuseStep 4009999 = 6014999) B6014999
theorem B5346665 : Blo 2223435 5346665 := bstep (se 2 (by rfl) ⟨2004999, by rfl⟩ : syracuseStep 5346665 = 4009999) B4009999
theorem B3564443 : Blo 2223435 3564443 := bstep (se 1 (by rfl) ⟨2673332, by rfl⟩ : syracuseStep 3564443 = 5346665) B5346665
theorem B9505181 : Blo 2223435 9505181 := bstep (se 3 (by rfl) ⟨1782221, by rfl⟩ : syracuseStep 9505181 = 3564443) B3564443
theorem B6336787 : Blo 2223435 6336787 := bstep (se 1 (by rfl) ⟨4752590, by rfl⟩ : syracuseStep 6336787 = 9505181) B9505181
theorem B8449049 : Blo 2223435 8449049 := bstep (se 2 (by rfl) ⟨3168393, by rfl⟩ : syracuseStep 8449049 = 6336787) B6336787
theorem B5632699 : Blo 2223435 5632699 := bstep (se 1 (by rfl) ⟨4224524, by rfl⟩ : syracuseStep 5632699 = 8449049) B8449049
theorem B7510265 : Blo 2223435 7510265 := bstep (se 2 (by rfl) ⟨2816349, by rfl⟩ : syracuseStep 7510265 = 5632699) B5632699
theorem B5006843 : Blo 2223435 5006843 := bstep (se 1 (by rfl) ⟨3755132, by rfl⟩ : syracuseStep 5006843 = 7510265) B7510265
theorem B3337895 : Blo 2223435 3337895 := bstep (se 1 (by rfl) ⟨2503421, by rfl⟩ : syracuseStep 3337895 = 5006843) B5006843
theorem B2225263 : Blo 2223435 2225263 := bstep (se 1 (by rfl) ⟨1668947, by rfl⟩ : syracuseStep 2225263 = 3337895) B3337895
theorem B3337901 : Blo 2223435 3337901 := bbase (se 3 (by rfl) ⟨625856, by rfl⟩ : syracuseStep 3337901 = 1251713) (by norm_num)
theorem B2225267 : Blo 2223435 2225267 := bstep (se 1 (by rfl) ⟨1668950, by rfl⟩ : syracuseStep 2225267 = 3337901) B3337901
theorem B5006861 : Blo 2223435 5006861 := bbase (se 3 (by rfl) ⟨938786, by rfl⟩ : syracuseStep 5006861 = 1877573) (by norm_num)
theorem B3337907 : Blo 2223435 3337907 := bstep (se 1 (by rfl) ⟨2503430, by rfl⟩ : syracuseStep 3337907 = 5006861) B5006861
theorem B2225271 : Blo 2223435 2225271 := bstep (se 1 (by rfl) ⟨1668953, by rfl⟩ : syracuseStep 2225271 = 3337907) B3337907
theorem B2816365 : Blo 2223435 2816365 := bbase (se 3 (by rfl) ⟨528068, by rfl⟩ : syracuseStep 2816365 = 1056137) (by norm_num)
theorem B3755153 : Blo 2223435 3755153 := bstep (se 2 (by rfl) ⟨1408182, by rfl⟩ : syracuseStep 3755153 = 2816365) B2816365
theorem B2503435 : Blo 2223435 2503435 := bstep (se 1 (by rfl) ⟨1877576, by rfl⟩ : syracuseStep 2503435 = 3755153) B3755153
theorem B3337913 : Blo 2223435 3337913 := bstep (se 2 (by rfl) ⟨1251717, by rfl⟩ : syracuseStep 3337913 = 2503435) B2503435
theorem B2225275 : Blo 2223435 2225275 := bstep (se 1 (by rfl) ⟨1668956, by rfl⟩ : syracuseStep 2225275 = 3337913) B3337913
theorem B3383461 : Blo 2223435 3383461 := bbase (se 4 (by rfl) ⟨317199, by rfl⟩ : syracuseStep 3383461 = 634399) (by norm_num)
theorem B4511281 : Blo 2223435 4511281 := bstep (se 2 (by rfl) ⟨1691730, by rfl⟩ : syracuseStep 4511281 = 3383461) B3383461
theorem B6015041 : Blo 2223435 6015041 := bstep (se 2 (by rfl) ⟨2255640, by rfl⟩ : syracuseStep 6015041 = 4511281) B4511281
theorem B4010027 : Blo 2223435 4010027 := bstep (se 1 (by rfl) ⟨3007520, by rfl⟩ : syracuseStep 4010027 = 6015041) B6015041
theorem B10693405 : Blo 2223435 10693405 := bstep (se 3 (by rfl) ⟨2005013, by rfl⟩ : syracuseStep 10693405 = 4010027) B4010027
theorem B14257873 : Blo 2223435 14257873 := bstep (se 2 (by rfl) ⟨5346702, by rfl⟩ : syracuseStep 14257873 = 10693405) B10693405
theorem B19010497 : Blo 2223435 19010497 := bstep (se 2 (by rfl) ⟨7128936, by rfl⟩ : syracuseStep 19010497 = 14257873) B14257873
theorem B25347329 : Blo 2223435 25347329 := bstep (se 2 (by rfl) ⟨9505248, by rfl⟩ : syracuseStep 25347329 = 19010497) B19010497
theorem B16898219 : Blo 2223435 16898219 := bstep (se 1 (by rfl) ⟨12673664, by rfl⟩ : syracuseStep 16898219 = 25347329) B25347329
theorem B11265479 : Blo 2223435 11265479 := bstep (se 1 (by rfl) ⟨8449109, by rfl⟩ : syracuseStep 11265479 = 16898219) B16898219
theorem B7510319 : Blo 2223435 7510319 := bstep (se 1 (by rfl) ⟨5632739, by rfl⟩ : syracuseStep 7510319 = 11265479) B11265479
theorem B5006879 : Blo 2223435 5006879 := bstep (se 1 (by rfl) ⟨3755159, by rfl⟩ : syracuseStep 5006879 = 7510319) B7510319
theorem B3337919 : Blo 2223435 3337919 := bstep (se 1 (by rfl) ⟨2503439, by rfl⟩ : syracuseStep 3337919 = 5006879) B5006879
theorem B2225279 : Blo 2223435 2225279 := bstep (se 1 (by rfl) ⟨1668959, by rfl⟩ : syracuseStep 2225279 = 3337919) B3337919
theorem B3337925 : Blo 2223435 3337925 := bbase (se 4 (by rfl) ⟨312930, by rfl⟩ : syracuseStep 3337925 = 625861) (by norm_num)
theorem B2225283 : Blo 2223435 2225283 := bstep (se 1 (by rfl) ⟨1668962, by rfl⟩ : syracuseStep 2225283 = 3337925) B3337925
theorem B3755173 : Blo 2223435 3755173 := bbase (se 4 (by rfl) ⟨352047, by rfl⟩ : syracuseStep 3755173 = 704095) (by norm_num)
theorem B5006897 : Blo 2223435 5006897 := bstep (se 2 (by rfl) ⟨1877586, by rfl⟩ : syracuseStep 5006897 = 3755173) B3755173
theorem B3337931 : Blo 2223435 3337931 := bstep (se 1 (by rfl) ⟨2503448, by rfl⟩ : syracuseStep 3337931 = 5006897) B5006897
theorem B2225287 : Blo 2223435 2225287 := bstep (se 1 (by rfl) ⟨1668965, by rfl⟩ : syracuseStep 2225287 = 3337931) B3337931
theorem B2503453 : Blo 2223435 2503453 := bbase (se 3 (by rfl) ⟨469397, by rfl⟩ : syracuseStep 2503453 = 938795) (by norm_num)
theorem B3337937 : Blo 2223435 3337937 := bstep (se 2 (by rfl) ⟨1251726, by rfl⟩ : syracuseStep 3337937 = 2503453) B2503453
theorem B2225291 : Blo 2223435 2225291 := bstep (se 1 (by rfl) ⟨1668968, by rfl⟩ : syracuseStep 2225291 = 3337937) B3337937
theorem B7510373 : Blo 2223435 7510373 := bbase (se 4 (by rfl) ⟨704097, by rfl⟩ : syracuseStep 7510373 = 1408195) (by norm_num)
theorem B5006915 : Blo 2223435 5006915 := bstep (se 1 (by rfl) ⟨3755186, by rfl⟩ : syracuseStep 5006915 = 7510373) B7510373
theorem B3337943 : Blo 2223435 3337943 := bstep (se 1 (by rfl) ⟨2503457, by rfl⟩ : syracuseStep 3337943 = 5006915) B5006915
theorem B2225295 : Blo 2223435 2225295 := bstep (se 1 (by rfl) ⟨1668971, by rfl⟩ : syracuseStep 2225295 = 3337943) B3337943
theorem B3337949 : Blo 2223435 3337949 := bbase (se 3 (by rfl) ⟨625865, by rfl⟩ : syracuseStep 3337949 = 1251731) (by norm_num)
theorem B2225299 : Blo 2223435 2225299 := bstep (se 1 (by rfl) ⟨1668974, by rfl⟩ : syracuseStep 2225299 = 3337949) B3337949
theorem B5006933 : Blo 2223435 5006933 := bbase (se 8 (by rfl) ⟨29337, by rfl⟩ : syracuseStep 5006933 = 58675) (by norm_num)
theorem B3337955 : Blo 2223435 3337955 := bstep (se 1 (by rfl) ⟨2503466, by rfl⟩ : syracuseStep 3337955 = 5006933) B5006933
theorem B2225303 : Blo 2223435 2225303 := bstep (se 1 (by rfl) ⟨1668977, by rfl⟩ : syracuseStep 2225303 = 3337955) B3337955
theorem B4752685 : Blo 2223435 4752685 := bbase (se 3 (by rfl) ⟨891128, by rfl⟩ : syracuseStep 4752685 = 1782257) (by norm_num)
theorem B6336913 : Blo 2223435 6336913 := bstep (se 2 (by rfl) ⟨2376342, by rfl⟩ : syracuseStep 6336913 = 4752685) B4752685
theorem B8449217 : Blo 2223435 8449217 := bstep (se 2 (by rfl) ⟨3168456, by rfl⟩ : syracuseStep 8449217 = 6336913) B6336913
theorem B5632811 : Blo 2223435 5632811 := bstep (se 1 (by rfl) ⟨4224608, by rfl⟩ : syracuseStep 5632811 = 8449217) B8449217
theorem B3755207 : Blo 2223435 3755207 := bstep (se 1 (by rfl) ⟨2816405, by rfl⟩ : syracuseStep 3755207 = 5632811) B5632811
theorem B2503471 : Blo 2223435 2503471 := bstep (se 1 (by rfl) ⟨1877603, by rfl⟩ : syracuseStep 2503471 = 3755207) B3755207
theorem B3337961 : Blo 2223435 3337961 := bstep (se 2 (by rfl) ⟨1251735, by rfl⟩ : syracuseStep 3337961 = 2503471) B2503471
theorem B2225307 : Blo 2223435 2225307 := bstep (se 1 (by rfl) ⟨1668980, by rfl⟩ : syracuseStep 2225307 = 3337961) B3337961
theorem B13534037 : Blo 2223435 13534037 := bbase (se 9 (by rfl) ⟨39650, by rfl⟩ : syracuseStep 13534037 = 79301) (by norm_num)
theorem B9022691 : Blo 2223435 9022691 := bstep (se 1 (by rfl) ⟨6767018, by rfl⟩ : syracuseStep 9022691 = 13534037) B13534037
theorem B24060509 : Blo 2223435 24060509 := bstep (se 3 (by rfl) ⟨4511345, by rfl⟩ : syracuseStep 24060509 = 9022691) B9022691
theorem B16040339 : Blo 2223435 16040339 := bstep (se 1 (by rfl) ⟨12030254, by rfl⟩ : syracuseStep 16040339 = 24060509) B24060509
theorem B10693559 : Blo 2223435 10693559 := bstep (se 1 (by rfl) ⟨8020169, by rfl⟩ : syracuseStep 10693559 = 16040339) B16040339
theorem B28516157 : Blo 2223435 28516157 := bstep (se 3 (by rfl) ⟨5346779, by rfl⟩ : syracuseStep 28516157 = 10693559) B10693559
theorem B19010771 : Blo 2223435 19010771 := bstep (se 1 (by rfl) ⟨14258078, by rfl⟩ : syracuseStep 19010771 = 28516157) B28516157
theorem B12673847 : Blo 2223435 12673847 := bstep (se 1 (by rfl) ⟨9505385, by rfl⟩ : syracuseStep 12673847 = 19010771) B19010771
theorem B8449231 : Blo 2223435 8449231 := bstep (se 1 (by rfl) ⟨6336923, by rfl⟩ : syracuseStep 8449231 = 12673847) B12673847
theorem B11265641 : Blo 2223435 11265641 := bstep (se 2 (by rfl) ⟨4224615, by rfl⟩ : syracuseStep 11265641 = 8449231) B8449231
theorem B7510427 : Blo 2223435 7510427 := bstep (se 1 (by rfl) ⟨5632820, by rfl⟩ : syracuseStep 7510427 = 11265641) B11265641
theorem B5006951 : Blo 2223435 5006951 := bstep (se 1 (by rfl) ⟨3755213, by rfl⟩ : syracuseStep 5006951 = 7510427) B7510427
theorem B3337967 : Blo 2223435 3337967 := bstep (se 1 (by rfl) ⟨2503475, by rfl⟩ : syracuseStep 3337967 = 5006951) B5006951
theorem B2225311 : Blo 2223435 2225311 := bstep (se 1 (by rfl) ⟨1668983, by rfl⟩ : syracuseStep 2225311 = 3337967) B3337967
theorem B3337973 : Blo 2223435 3337973 := bbase (se 5 (by rfl) ⟨156467, by rfl⟩ : syracuseStep 3337973 = 312935) (by norm_num)
theorem B2225315 : Blo 2223435 2225315 := bstep (se 1 (by rfl) ⟨1668986, by rfl⟩ : syracuseStep 2225315 = 3337973) B3337973
theorem B3564533 : Blo 2223435 3564533 := bbase (se 5 (by rfl) ⟨167087, by rfl⟩ : syracuseStep 3564533 = 334175) (by norm_num)
theorem B9505421 : Blo 2223435 9505421 := bstep (se 3 (by rfl) ⟨1782266, by rfl⟩ : syracuseStep 9505421 = 3564533) B3564533
theorem B6336947 : Blo 2223435 6336947 := bstep (se 1 (by rfl) ⟨4752710, by rfl⟩ : syracuseStep 6336947 = 9505421) B9505421
theorem B4224631 : Blo 2223435 4224631 := bstep (se 1 (by rfl) ⟨3168473, by rfl⟩ : syracuseStep 4224631 = 6336947) B6336947
theorem B5632841 : Blo 2223435 5632841 := bstep (se 2 (by rfl) ⟨2112315, by rfl⟩ : syracuseStep 5632841 = 4224631) B4224631
theorem B3755227 : Blo 2223435 3755227 := bstep (se 1 (by rfl) ⟨2816420, by rfl⟩ : syracuseStep 3755227 = 5632841) B5632841
theorem B5006969 : Blo 2223435 5006969 := bstep (se 2 (by rfl) ⟨1877613, by rfl⟩ : syracuseStep 5006969 = 3755227) B3755227
theorem B3337979 : Blo 2223435 3337979 := bstep (se 1 (by rfl) ⟨2503484, by rfl⟩ : syracuseStep 3337979 = 5006969) B5006969
theorem B2225319 : Blo 2223435 2225319 := bstep (se 1 (by rfl) ⟨1668989, by rfl⟩ : syracuseStep 2225319 = 3337979) B3337979
theorem B2503489 : Blo 2223435 2503489 := bbase (se 2 (by rfl) ⟨938808, by rfl⟩ : syracuseStep 2503489 = 1877617) (by norm_num)
theorem B3337985 : Blo 2223435 3337985 := bstep (se 2 (by rfl) ⟨1251744, by rfl⟩ : syracuseStep 3337985 = 2503489) B2503489
theorem B2225323 : Blo 2223435 2225323 := bstep (se 1 (by rfl) ⟨1668992, by rfl⟩ : syracuseStep 2225323 = 3337985) B3337985
theorem B5632861 : Blo 2223435 5632861 := bbase (se 3 (by rfl) ⟨1056161, by rfl⟩ : syracuseStep 5632861 = 2112323) (by norm_num)
theorem B7510481 : Blo 2223435 7510481 := bstep (se 2 (by rfl) ⟨2816430, by rfl⟩ : syracuseStep 7510481 = 5632861) B5632861
theorem B5006987 : Blo 2223435 5006987 := bstep (se 1 (by rfl) ⟨3755240, by rfl⟩ : syracuseStep 5006987 = 7510481) B7510481
theorem B3337991 : Blo 2223435 3337991 := bstep (se 1 (by rfl) ⟨2503493, by rfl⟩ : syracuseStep 3337991 = 5006987) B5006987
theorem B2225327 : Blo 2223435 2225327 := bstep (se 1 (by rfl) ⟨1668995, by rfl⟩ : syracuseStep 2225327 = 3337991) B3337991
theorem B3337997 : Blo 2223435 3337997 := bbase (se 3 (by rfl) ⟨625874, by rfl⟩ : syracuseStep 3337997 = 1251749) (by norm_num)
theorem B2225331 : Blo 2223435 2225331 := bstep (se 1 (by rfl) ⟨1668998, by rfl⟩ : syracuseStep 2225331 = 3337997) B3337997
theorem B5007005 : Blo 2223435 5007005 := bbase (se 3 (by rfl) ⟨938813, by rfl⟩ : syracuseStep 5007005 = 1877627) (by norm_num)
theorem B3338003 : Blo 2223435 3338003 := bstep (se 1 (by rfl) ⟨2503502, by rfl⟩ : syracuseStep 3338003 = 5007005) B5007005
theorem B2225335 : Blo 2223435 2225335 := bstep (se 1 (by rfl) ⟨1669001, by rfl⟩ : syracuseStep 2225335 = 3338003) B3338003
theorem B3755261 : Blo 2223435 3755261 := bbase (se 3 (by rfl) ⟨704111, by rfl⟩ : syracuseStep 3755261 = 1408223) (by norm_num)
theorem B2503507 : Blo 2223435 2503507 := bstep (se 1 (by rfl) ⟨1877630, by rfl⟩ : syracuseStep 2503507 = 3755261) B3755261
theorem B3338009 : Blo 2223435 3338009 := bstep (se 2 (by rfl) ⟨1251753, by rfl⟩ : syracuseStep 3338009 = 2503507) B2503507
theorem B2225339 : Blo 2223435 2225339 := bstep (se 1 (by rfl) ⟨1669004, by rfl⟩ : syracuseStep 2225339 = 3338009) B3338009
theorem B5799757 : Blo 2223435 5799757 := bbase (se 3 (by rfl) ⟨1087454, by rfl⟩ : syracuseStep 5799757 = 2174909) (by norm_num)
theorem B7733009 : Blo 2223435 7733009 := bstep (se 2 (by rfl) ⟨2899878, by rfl⟩ : syracuseStep 7733009 = 5799757) B5799757
theorem B5155339 : Blo 2223435 5155339 := bstep (se 1 (by rfl) ⟨3866504, by rfl⟩ : syracuseStep 5155339 = 7733009) B7733009
theorem B6873785 : Blo 2223435 6873785 := bstep (se 2 (by rfl) ⟨2577669, by rfl⟩ : syracuseStep 6873785 = 5155339) B5155339
theorem B4582523 : Blo 2223435 4582523 := bstep (se 1 (by rfl) ⟨3436892, by rfl⟩ : syracuseStep 4582523 = 6873785) B6873785
theorem B3055015 : Blo 2223435 3055015 := bstep (se 1 (by rfl) ⟨2291261, by rfl⟩ : syracuseStep 3055015 = 4582523) B4582523
theorem B16293413 : Blo 2223435 16293413 := bstep (se 4 (by rfl) ⟨1527507, by rfl⟩ : syracuseStep 16293413 = 3055015) B3055015
theorem B10862275 : Blo 2223435 10862275 := bstep (se 1 (by rfl) ⟨8146706, by rfl⟩ : syracuseStep 10862275 = 16293413) B16293413
theorem B14483033 : Blo 2223435 14483033 := bstep (se 2 (by rfl) ⟨5431137, by rfl⟩ : syracuseStep 14483033 = 10862275) B10862275
theorem B9655355 : Blo 2223435 9655355 := bstep (se 1 (by rfl) ⟨7241516, by rfl⟩ : syracuseStep 9655355 = 14483033) B14483033
theorem B25747613 : Blo 2223435 25747613 := bstep (se 3 (by rfl) ⟨4827677, by rfl⟩ : syracuseStep 25747613 = 9655355) B9655355
theorem B17165075 : Blo 2223435 17165075 := bstep (se 1 (by rfl) ⟨12873806, by rfl⟩ : syracuseStep 17165075 = 25747613) B25747613
theorem B45773533 : Blo 2223435 45773533 := bstep (se 3 (by rfl) ⟨8582537, by rfl⟩ : syracuseStep 45773533 = 17165075) B17165075
theorem B61031377 : Blo 2223435 61031377 := bstep (se 2 (by rfl) ⟨22886766, by rfl⟩ : syracuseStep 61031377 = 45773533) B45773533
theorem B325500677 : Blo 2223435 325500677 := bstep (se 4 (by rfl) ⟨30515688, by rfl⟩ : syracuseStep 325500677 = 61031377) B61031377
theorem B217000451 : Blo 2223435 217000451 := bstep (se 1 (by rfl) ⟨162750338, by rfl⟩ : syracuseStep 217000451 = 325500677) B325500677
theorem B144666967 : Blo 2223435 144666967 := bstep (se 1 (by rfl) ⟨108500225, by rfl⟩ : syracuseStep 144666967 = 217000451) B217000451
theorem B192889289 : Blo 2223435 192889289 := bstep (se 2 (by rfl) ⟨72333483, by rfl⟩ : syracuseStep 192889289 = 144666967) B144666967
theorem B128592859 : Blo 2223435 128592859 := bstep (se 1 (by rfl) ⟨96444644, by rfl⟩ : syracuseStep 128592859 = 192889289) B192889289
theorem B171457145 : Blo 2223435 171457145 := bstep (se 2 (by rfl) ⟨64296429, by rfl⟩ : syracuseStep 171457145 = 128592859) B128592859
theorem B114304763 : Blo 2223435 114304763 := bstep (se 1 (by rfl) ⟨85728572, by rfl⟩ : syracuseStep 114304763 = 171457145) B171457145
theorem B76203175 : Blo 2223435 76203175 := bstep (se 1 (by rfl) ⟨57152381, by rfl⟩ : syracuseStep 76203175 = 114304763) B114304763
theorem B101604233 : Blo 2223435 101604233 := bstep (se 2 (by rfl) ⟨38101587, by rfl⟩ : syracuseStep 101604233 = 76203175) B76203175
theorem B270944621 : Blo 2223435 270944621 := bstep (se 3 (by rfl) ⟨50802116, by rfl⟩ : syracuseStep 270944621 = 101604233) B101604233
theorem B180629747 : Blo 2223435 180629747 := bstep (se 1 (by rfl) ⟨135472310, by rfl⟩ : syracuseStep 180629747 = 270944621) B270944621
theorem B120419831 : Blo 2223435 120419831 := bstep (se 1 (by rfl) ⟨90314873, by rfl⟩ : syracuseStep 120419831 = 180629747) B180629747
theorem B321119549 : Blo 2223435 321119549 := bstep (se 3 (by rfl) ⟨60209915, by rfl⟩ : syracuseStep 321119549 = 120419831) B120419831
theorem B214079699 : Blo 2223435 214079699 := bstep (se 1 (by rfl) ⟨160559774, by rfl⟩ : syracuseStep 214079699 = 321119549) B321119549
theorem B570879197 : Blo 2223435 570879197 := bstep (se 3 (by rfl) ⟨107039849, by rfl⟩ : syracuseStep 570879197 = 214079699) B214079699
theorem B380586131 : Blo 2223435 380586131 := bstep (se 1 (by rfl) ⟨285439598, by rfl⟩ : syracuseStep 380586131 = 570879197) B570879197
theorem B253724087 : Blo 2223435 253724087 := bstep (se 1 (by rfl) ⟨190293065, by rfl⟩ : syracuseStep 253724087 = 380586131) B380586131
theorem B169149391 : Blo 2223435 169149391 := bstep (se 1 (by rfl) ⟨126862043, by rfl⟩ : syracuseStep 169149391 = 253724087) B253724087
theorem B902130085 : Blo 2223435 902130085 := bstep (se 4 (by rfl) ⟨84574695, by rfl⟩ : syracuseStep 902130085 = 169149391) B169149391
theorem B1202840113 : Blo 2223435 1202840113 := bstep (se 2 (by rfl) ⟨451065042, by rfl⟩ : syracuseStep 1202840113 = 902130085) B902130085
theorem B1603786817 : Blo 2223435 1603786817 := bstep (se 2 (by rfl) ⟨601420056, by rfl⟩ : syracuseStep 1603786817 = 1202840113) B1202840113
theorem B1069191211 : Blo 2223435 1069191211 := bstep (se 1 (by rfl) ⟨801893408, by rfl⟩ : syracuseStep 1069191211 = 1603786817) B1603786817
theorem B1425588281 : Blo 2223435 1425588281 := bstep (se 2 (by rfl) ⟨534595605, by rfl⟩ : syracuseStep 1425588281 = 1069191211) B1069191211
theorem B950392187 : Blo 2223435 950392187 := bstep (se 1 (by rfl) ⟨712794140, by rfl⟩ : syracuseStep 950392187 = 1425588281) B1425588281
theorem B633594791 : Blo 2223435 633594791 := bstep (se 1 (by rfl) ⟨475196093, by rfl⟩ : syracuseStep 633594791 = 950392187) B950392187
theorem B422396527 : Blo 2223435 422396527 := bstep (se 1 (by rfl) ⟨316797395, by rfl⟩ : syracuseStep 422396527 = 633594791) B633594791
theorem B563195369 : Blo 2223435 563195369 := bstep (se 2 (by rfl) ⟨211198263, by rfl⟩ : syracuseStep 563195369 = 422396527) B422396527
theorem B1501854317 : Blo 2223435 1501854317 := bstep (se 3 (by rfl) ⟨281597684, by rfl⟩ : syracuseStep 1501854317 = 563195369) B563195369
theorem B1001236211 : Blo 2223435 1001236211 := bstep (se 1 (by rfl) ⟨750927158, by rfl⟩ : syracuseStep 1001236211 = 1501854317) B1501854317
theorem B667490807 : Blo 2223435 667490807 := bstep (se 1 (by rfl) ⟨500618105, by rfl⟩ : syracuseStep 667490807 = 1001236211) B1001236211
theorem B1779975485 : Blo 2223435 1779975485 := bstep (se 3 (by rfl) ⟨333745403, by rfl⟩ : syracuseStep 1779975485 = 667490807) B667490807
theorem B1186650323 : Blo 2223435 1186650323 := bstep (se 1 (by rfl) ⟨889987742, by rfl⟩ : syracuseStep 1186650323 = 1779975485) B1779975485
theorem B791100215 : Blo 2223435 791100215 := bstep (se 1 (by rfl) ⟨593325161, by rfl⟩ : syracuseStep 791100215 = 1186650323) B1186650323
theorem B527400143 : Blo 2223435 527400143 := bstep (se 1 (by rfl) ⟨395550107, by rfl⟩ : syracuseStep 527400143 = 791100215) B791100215
theorem B351600095 : Blo 2223435 351600095 := bstep (se 1 (by rfl) ⟨263700071, by rfl⟩ : syracuseStep 351600095 = 527400143) B527400143
theorem B234400063 : Blo 2223435 234400063 := bstep (se 1 (by rfl) ⟨175800047, by rfl⟩ : syracuseStep 234400063 = 351600095) B351600095
theorem B312533417 : Blo 2223435 312533417 := bstep (se 2 (by rfl) ⟨117200031, by rfl⟩ : syracuseStep 312533417 = 234400063) B234400063
theorem B208355611 : Blo 2223435 208355611 := bstep (se 1 (by rfl) ⟨156266708, by rfl⟩ : syracuseStep 208355611 = 312533417) B312533417
theorem B277807481 : Blo 2223435 277807481 := bstep (se 2 (by rfl) ⟨104177805, by rfl⟩ : syracuseStep 277807481 = 208355611) B208355611
theorem B185204987 : Blo 2223435 185204987 := bstep (se 1 (by rfl) ⟨138903740, by rfl⟩ : syracuseStep 185204987 = 277807481) B277807481
theorem B123469991 : Blo 2223435 123469991 := bstep (se 1 (by rfl) ⟨92602493, by rfl⟩ : syracuseStep 123469991 = 185204987) B185204987
theorem B82313327 : Blo 2223435 82313327 := bstep (se 1 (by rfl) ⟨61734995, by rfl⟩ : syracuseStep 82313327 = 123469991) B123469991
theorem B54875551 : Blo 2223435 54875551 := bstep (se 1 (by rfl) ⟨41156663, by rfl⟩ : syracuseStep 54875551 = 82313327) B82313327
theorem B73167401 : Blo 2223435 73167401 := bstep (se 2 (by rfl) ⟨27437775, by rfl⟩ : syracuseStep 73167401 = 54875551) B54875551
theorem B195113069 : Blo 2223435 195113069 := bstep (se 3 (by rfl) ⟨36583700, by rfl⟩ : syracuseStep 195113069 = 73167401) B73167401
theorem B130075379 : Blo 2223435 130075379 := bstep (se 1 (by rfl) ⟨97556534, by rfl⟩ : syracuseStep 130075379 = 195113069) B195113069
theorem B86716919 : Blo 2223435 86716919 := bstep (se 1 (by rfl) ⟨65037689, by rfl⟩ : syracuseStep 86716919 = 130075379) B130075379
theorem B57811279 : Blo 2223435 57811279 := bstep (se 1 (by rfl) ⟨43358459, by rfl⟩ : syracuseStep 57811279 = 86716919) B86716919
theorem B77081705 : Blo 2223435 77081705 := bstep (se 2 (by rfl) ⟨28905639, by rfl⟩ : syracuseStep 77081705 = 57811279) B57811279
theorem B51387803 : Blo 2223435 51387803 := bstep (se 1 (by rfl) ⟨38540852, by rfl⟩ : syracuseStep 51387803 = 77081705) B77081705
theorem B34258535 : Blo 2223435 34258535 := bstep (se 1 (by rfl) ⟨25693901, by rfl⟩ : syracuseStep 34258535 = 51387803) B51387803
theorem B22839023 : Blo 2223435 22839023 := bstep (se 1 (by rfl) ⟨17129267, by rfl⟩ : syracuseStep 22839023 = 34258535) B34258535
theorem B15226015 : Blo 2223435 15226015 := bstep (se 1 (by rfl) ⟨11419511, by rfl⟩ : syracuseStep 15226015 = 22839023) B22839023
theorem B20301353 : Blo 2223435 20301353 := bstep (se 2 (by rfl) ⟨7613007, by rfl⟩ : syracuseStep 20301353 = 15226015) B15226015
theorem B13534235 : Blo 2223435 13534235 := bstep (se 1 (by rfl) ⟨10150676, by rfl⟩ : syracuseStep 13534235 = 20301353) B20301353
theorem B9022823 : Blo 2223435 9022823 := bstep (se 1 (by rfl) ⟨6767117, by rfl⟩ : syracuseStep 9022823 = 13534235) B13534235
theorem B6015215 : Blo 2223435 6015215 := bstep (se 1 (by rfl) ⟨4511411, by rfl⟩ : syracuseStep 6015215 = 9022823) B9022823
theorem B4010143 : Blo 2223435 4010143 := bstep (se 1 (by rfl) ⟨3007607, by rfl⟩ : syracuseStep 4010143 = 6015215) B6015215
theorem B5346857 : Blo 2223435 5346857 := bstep (se 2 (by rfl) ⟨2005071, by rfl⟩ : syracuseStep 5346857 = 4010143) B4010143
theorem B3564571 : Blo 2223435 3564571 := bstep (se 1 (by rfl) ⟨2673428, by rfl⟩ : syracuseStep 3564571 = 5346857) B5346857
theorem B4752761 : Blo 2223435 4752761 := bstep (se 2 (by rfl) ⟨1782285, by rfl⟩ : syracuseStep 4752761 = 3564571) B3564571
theorem B12674029 : Blo 2223435 12674029 := bstep (se 3 (by rfl) ⟨2376380, by rfl⟩ : syracuseStep 12674029 = 4752761) B4752761
theorem B16898705 : Blo 2223435 16898705 := bstep (se 2 (by rfl) ⟨6337014, by rfl⟩ : syracuseStep 16898705 = 12674029) B12674029
theorem B11265803 : Blo 2223435 11265803 := bstep (se 1 (by rfl) ⟨8449352, by rfl⟩ : syracuseStep 11265803 = 16898705) B16898705
theorem B7510535 : Blo 2223435 7510535 := bstep (se 1 (by rfl) ⟨5632901, by rfl⟩ : syracuseStep 7510535 = 11265803) B11265803
theorem B5007023 : Blo 2223435 5007023 := bstep (se 1 (by rfl) ⟨3755267, by rfl⟩ : syracuseStep 5007023 = 7510535) B7510535
theorem B3338015 : Blo 2223435 3338015 := bstep (se 1 (by rfl) ⟨2503511, by rfl⟩ : syracuseStep 3338015 = 5007023) B5007023
theorem B2225343 : Blo 2223435 2225343 := bstep (se 1 (by rfl) ⟨1669007, by rfl⟩ : syracuseStep 2225343 = 3338015) B3338015
theorem B3338021 : Blo 2223435 3338021 := bbase (se 4 (by rfl) ⟨312939, by rfl⟩ : syracuseStep 3338021 = 625879) (by norm_num)
theorem B2225347 : Blo 2223435 2225347 := bstep (se 1 (by rfl) ⟨1669010, by rfl⟩ : syracuseStep 2225347 = 3338021) B3338021
theorem B2816461 : Blo 2223435 2816461 := bbase (se 3 (by rfl) ⟨528086, by rfl⟩ : syracuseStep 2816461 = 1056173) (by norm_num)
theorem B3755281 : Blo 2223435 3755281 := bstep (se 2 (by rfl) ⟨1408230, by rfl⟩ : syracuseStep 3755281 = 2816461) B2816461
theorem B5007041 : Blo 2223435 5007041 := bstep (se 2 (by rfl) ⟨1877640, by rfl⟩ : syracuseStep 5007041 = 3755281) B3755281
theorem B3338027 : Blo 2223435 3338027 := bstep (se 1 (by rfl) ⟨2503520, by rfl⟩ : syracuseStep 3338027 = 5007041) B5007041
theorem B2225351 : Blo 2223435 2225351 := bstep (se 1 (by rfl) ⟨1669013, by rfl⟩ : syracuseStep 2225351 = 3338027) B3338027
theorem B2503525 : Blo 2223435 2503525 := bbase (se 4 (by rfl) ⟨234705, by rfl⟩ : syracuseStep 2503525 = 469411) (by norm_num)
theorem B3338033 : Blo 2223435 3338033 := bstep (se 2 (by rfl) ⟨1251762, by rfl⟩ : syracuseStep 3338033 = 2503525) B2503525
theorem B2225355 : Blo 2223435 2225355 := bstep (se 1 (by rfl) ⟨1669016, by rfl⟩ : syracuseStep 2225355 = 3338033) B3338033
theorem B6337061 : Blo 2223435 6337061 := bbase (se 4 (by rfl) ⟨594099, by rfl⟩ : syracuseStep 6337061 = 1188199) (by norm_num)
theorem B4224707 : Blo 2223435 4224707 := bstep (se 1 (by rfl) ⟨3168530, by rfl⟩ : syracuseStep 4224707 = 6337061) B6337061
theorem B2816471 : Blo 2223435 2816471 := bstep (se 1 (by rfl) ⟨2112353, by rfl⟩ : syracuseStep 2816471 = 4224707) B4224707
theorem B7510589 : Blo 2223435 7510589 := bstep (se 3 (by rfl) ⟨1408235, by rfl⟩ : syracuseStep 7510589 = 2816471) B2816471
theorem B5007059 : Blo 2223435 5007059 := bstep (se 1 (by rfl) ⟨3755294, by rfl⟩ : syracuseStep 5007059 = 7510589) B7510589
theorem B3338039 : Blo 2223435 3338039 := bstep (se 1 (by rfl) ⟨2503529, by rfl⟩ : syracuseStep 3338039 = 5007059) B5007059
theorem B2225359 : Blo 2223435 2225359 := bstep (se 1 (by rfl) ⟨1669019, by rfl⟩ : syracuseStep 2225359 = 3338039) B3338039
theorem B3338045 : Blo 2223435 3338045 := bbase (se 3 (by rfl) ⟨625883, by rfl⟩ : syracuseStep 3338045 = 1251767) (by norm_num)
theorem B2225363 : Blo 2223435 2225363 := bstep (se 1 (by rfl) ⟨1669022, by rfl⟩ : syracuseStep 2225363 = 3338045) B3338045
theorem B5007077 : Blo 2223435 5007077 := bbase (se 4 (by rfl) ⟨469413, by rfl⟩ : syracuseStep 5007077 = 938827) (by norm_num)
theorem B3338051 : Blo 2223435 3338051 := bstep (se 1 (by rfl) ⟨2503538, by rfl⟩ : syracuseStep 3338051 = 5007077) B5007077
theorem B2225367 : Blo 2223435 2225367 := bstep (se 1 (by rfl) ⟨1669025, by rfl⟩ : syracuseStep 2225367 = 3338051) B3338051
theorem B5632973 : Blo 2223435 5632973 := bbase (se 3 (by rfl) ⟨1056182, by rfl⟩ : syracuseStep 5632973 = 2112365) (by norm_num)
theorem B3755315 : Blo 2223435 3755315 := bstep (se 1 (by rfl) ⟨2816486, by rfl⟩ : syracuseStep 3755315 = 5632973) B5632973
theorem B2503543 : Blo 2223435 2503543 := bstep (se 1 (by rfl) ⟨1877657, by rfl⟩ : syracuseStep 2503543 = 3755315) B3755315
theorem B3338057 : Blo 2223435 3338057 := bstep (se 2 (by rfl) ⟨1251771, by rfl⟩ : syracuseStep 3338057 = 2503543) B2503543
theorem B2225371 : Blo 2223435 2225371 := bstep (se 1 (by rfl) ⟨1669028, by rfl⟩ : syracuseStep 2225371 = 3338057) B3338057
theorem B4511477 : Blo 2223435 4511477 := bbase (se 5 (by rfl) ⟨211475, by rfl⟩ : syracuseStep 4511477 = 422951) (by norm_num)
theorem B12030605 : Blo 2223435 12030605 := bstep (se 3 (by rfl) ⟨2255738, by rfl⟩ : syracuseStep 12030605 = 4511477) B4511477
theorem B8020403 : Blo 2223435 8020403 := bstep (se 1 (by rfl) ⟨6015302, by rfl⟩ : syracuseStep 8020403 = 12030605) B12030605
theorem B5346935 : Blo 2223435 5346935 := bstep (se 1 (by rfl) ⟨4010201, by rfl⟩ : syracuseStep 5346935 = 8020403) B8020403
theorem B3564623 : Blo 2223435 3564623 := bstep (se 1 (by rfl) ⟨2673467, by rfl⟩ : syracuseStep 3564623 = 5346935) B5346935
theorem B2376415 : Blo 2223435 2376415 := bstep (se 1 (by rfl) ⟨1782311, by rfl⟩ : syracuseStep 2376415 = 3564623) B3564623
theorem B3168553 : Blo 2223435 3168553 := bstep (se 2 (by rfl) ⟨1188207, by rfl⟩ : syracuseStep 3168553 = 2376415) B2376415
theorem B4224737 : Blo 2223435 4224737 := bstep (se 2 (by rfl) ⟨1584276, by rfl⟩ : syracuseStep 4224737 = 3168553) B3168553
theorem B11265965 : Blo 2223435 11265965 := bstep (se 3 (by rfl) ⟨2112368, by rfl⟩ : syracuseStep 11265965 = 4224737) B4224737
theorem B7510643 : Blo 2223435 7510643 := bstep (se 1 (by rfl) ⟨5632982, by rfl⟩ : syracuseStep 7510643 = 11265965) B11265965
theorem B5007095 : Blo 2223435 5007095 := bstep (se 1 (by rfl) ⟨3755321, by rfl⟩ : syracuseStep 5007095 = 7510643) B7510643
theorem B3338063 : Blo 2223435 3338063 := bstep (se 1 (by rfl) ⟨2503547, by rfl⟩ : syracuseStep 3338063 = 5007095) B5007095
theorem B2225375 : Blo 2223435 2225375 := bstep (se 1 (by rfl) ⟨1669031, by rfl⟩ : syracuseStep 2225375 = 3338063) B3338063
theorem B3338069 : Blo 2223435 3338069 := bbase (se 9 (by rfl) ⟨9779, by rfl⟩ : syracuseStep 3338069 = 19559) (by norm_num)
theorem B2225379 : Blo 2223435 2225379 := bstep (se 1 (by rfl) ⟨1669034, by rfl⟩ : syracuseStep 2225379 = 3338069) B3338069
theorem B11419717 : Blo 2223435 11419717 := bbase (se 4 (by rfl) ⟨1070598, by rfl⟩ : syracuseStep 11419717 = 2141197) (by norm_num)
theorem B15226289 : Blo 2223435 15226289 := bstep (se 2 (by rfl) ⟨5709858, by rfl⟩ : syracuseStep 15226289 = 11419717) B11419717
theorem B10150859 : Blo 2223435 10150859 := bstep (se 1 (by rfl) ⟨7613144, by rfl⟩ : syracuseStep 10150859 = 15226289) B15226289
theorem B6767239 : Blo 2223435 6767239 := bstep (se 1 (by rfl) ⟨5075429, by rfl⟩ : syracuseStep 6767239 = 10150859) B10150859
theorem B9022985 : Blo 2223435 9022985 := bstep (se 2 (by rfl) ⟨3383619, by rfl⟩ : syracuseStep 9022985 = 6767239) B6767239
theorem B6015323 : Blo 2223435 6015323 := bstep (se 1 (by rfl) ⟨4511492, by rfl⟩ : syracuseStep 6015323 = 9022985) B9022985
theorem B16040861 : Blo 2223435 16040861 := bstep (se 3 (by rfl) ⟨3007661, by rfl⟩ : syracuseStep 16040861 = 6015323) B6015323
theorem B10693907 : Blo 2223435 10693907 := bstep (se 1 (by rfl) ⟨8020430, by rfl⟩ : syracuseStep 10693907 = 16040861) B16040861
theorem B7129271 : Blo 2223435 7129271 := bstep (se 1 (by rfl) ⟨5346953, by rfl⟩ : syracuseStep 7129271 = 10693907) B10693907
theorem B4752847 : Blo 2223435 4752847 := bstep (se 1 (by rfl) ⟨3564635, by rfl⟩ : syracuseStep 4752847 = 7129271) B7129271
theorem B6337129 : Blo 2223435 6337129 := bstep (se 2 (by rfl) ⟨2376423, by rfl⟩ : syracuseStep 6337129 = 4752847) B4752847
theorem B8449505 : Blo 2223435 8449505 := bstep (se 2 (by rfl) ⟨3168564, by rfl⟩ : syracuseStep 8449505 = 6337129) B6337129
theorem B5633003 : Blo 2223435 5633003 := bstep (se 1 (by rfl) ⟨4224752, by rfl⟩ : syracuseStep 5633003 = 8449505) B8449505
theorem B3755335 : Blo 2223435 3755335 := bstep (se 1 (by rfl) ⟨2816501, by rfl⟩ : syracuseStep 3755335 = 5633003) B5633003
theorem B5007113 : Blo 2223435 5007113 := bstep (se 2 (by rfl) ⟨1877667, by rfl⟩ : syracuseStep 5007113 = 3755335) B3755335
theorem B3338075 : Blo 2223435 3338075 := bstep (se 1 (by rfl) ⟨2503556, by rfl⟩ : syracuseStep 3338075 = 5007113) B5007113
theorem B2225383 : Blo 2223435 2225383 := bstep (se 1 (by rfl) ⟨1669037, by rfl⟩ : syracuseStep 2225383 = 3338075) B3338075
theorem B2503561 : Blo 2223435 2503561 := bbase (se 2 (by rfl) ⟨938835, by rfl⟩ : syracuseStep 2503561 = 1877671) (by norm_num)
theorem B3338081 : Blo 2223435 3338081 := bstep (se 2 (by rfl) ⟨1251780, by rfl⟩ : syracuseStep 3338081 = 2503561) B2503561
theorem B2225387 : Blo 2223435 2225387 := bstep (se 1 (by rfl) ⟨1669040, by rfl⟩ : syracuseStep 2225387 = 3338081) B3338081
theorem B8681669 : Blo 2223435 8681669 := bbase (se 4 (by rfl) ⟨813906, by rfl⟩ : syracuseStep 8681669 = 1627813) (by norm_num)
theorem B5787779 : Blo 2223435 5787779 := bstep (se 1 (by rfl) ⟨4340834, by rfl⟩ : syracuseStep 5787779 = 8681669) B8681669
theorem B15434077 : Blo 2223435 15434077 := bstep (se 3 (by rfl) ⟨2893889, by rfl⟩ : syracuseStep 15434077 = 5787779) B5787779
theorem B20578769 : Blo 2223435 20578769 := bstep (se 2 (by rfl) ⟨7717038, by rfl⟩ : syracuseStep 20578769 = 15434077) B15434077
theorem B13719179 : Blo 2223435 13719179 := bstep (se 1 (by rfl) ⟨10289384, by rfl⟩ : syracuseStep 13719179 = 20578769) B20578769
theorem B36584477 : Blo 2223435 36584477 := bstep (se 3 (by rfl) ⟨6859589, by rfl⟩ : syracuseStep 36584477 = 13719179) B13719179
theorem B24389651 : Blo 2223435 24389651 := bstep (se 1 (by rfl) ⟨18292238, by rfl⟩ : syracuseStep 24389651 = 36584477) B36584477
theorem B16259767 : Blo 2223435 16259767 := bstep (se 1 (by rfl) ⟨12194825, by rfl⟩ : syracuseStep 16259767 = 24389651) B24389651
theorem B86718757 : Blo 2223435 86718757 := bstep (se 4 (by rfl) ⟨8129883, by rfl⟩ : syracuseStep 86718757 = 16259767) B16259767
theorem B115625009 : Blo 2223435 115625009 := bstep (se 2 (by rfl) ⟨43359378, by rfl⟩ : syracuseStep 115625009 = 86718757) B86718757
theorem B77083339 : Blo 2223435 77083339 := bstep (se 1 (by rfl) ⟨57812504, by rfl⟩ : syracuseStep 77083339 = 115625009) B115625009
theorem B102777785 : Blo 2223435 102777785 := bstep (se 2 (by rfl) ⟨38541669, by rfl⟩ : syracuseStep 102777785 = 77083339) B77083339
theorem B68518523 : Blo 2223435 68518523 := bstep (se 1 (by rfl) ⟨51388892, by rfl⟩ : syracuseStep 68518523 = 102777785) B102777785
theorem B45679015 : Blo 2223435 45679015 := bstep (se 1 (by rfl) ⟨34259261, by rfl⟩ : syracuseStep 45679015 = 68518523) B68518523
theorem B60905353 : Blo 2223435 60905353 := bstep (se 2 (by rfl) ⟨22839507, by rfl⟩ : syracuseStep 60905353 = 45679015) B45679015
theorem B81207137 : Blo 2223435 81207137 := bstep (se 2 (by rfl) ⟨30452676, by rfl⟩ : syracuseStep 81207137 = 60905353) B60905353
theorem B216552365 : Blo 2223435 216552365 := bstep (se 3 (by rfl) ⟨40603568, by rfl⟩ : syracuseStep 216552365 = 81207137) B81207137
theorem B144368243 : Blo 2223435 144368243 := bstep (se 1 (by rfl) ⟨108276182, by rfl⟩ : syracuseStep 144368243 = 216552365) B216552365
theorem B96245495 : Blo 2223435 96245495 := bstep (se 1 (by rfl) ⟨72184121, by rfl⟩ : syracuseStep 96245495 = 144368243) B144368243
theorem B64163663 : Blo 2223435 64163663 := bstep (se 1 (by rfl) ⟨48122747, by rfl⟩ : syracuseStep 64163663 = 96245495) B96245495
theorem B42775775 : Blo 2223435 42775775 := bstep (se 1 (by rfl) ⟨32081831, by rfl⟩ : syracuseStep 42775775 = 64163663) B64163663
theorem B28517183 : Blo 2223435 28517183 := bstep (se 1 (by rfl) ⟨21387887, by rfl⟩ : syracuseStep 28517183 = 42775775) B42775775
theorem B19011455 : Blo 2223435 19011455 := bstep (se 1 (by rfl) ⟨14258591, by rfl⟩ : syracuseStep 19011455 = 28517183) B28517183
theorem B12674303 : Blo 2223435 12674303 := bstep (se 1 (by rfl) ⟨9505727, by rfl⟩ : syracuseStep 12674303 = 19011455) B19011455
theorem B8449535 : Blo 2223435 8449535 := bstep (se 1 (by rfl) ⟨6337151, by rfl⟩ : syracuseStep 8449535 = 12674303) B12674303
theorem B5633023 : Blo 2223435 5633023 := bstep (se 1 (by rfl) ⟨4224767, by rfl⟩ : syracuseStep 5633023 = 8449535) B8449535
theorem B7510697 : Blo 2223435 7510697 := bstep (se 2 (by rfl) ⟨2816511, by rfl⟩ : syracuseStep 7510697 = 5633023) B5633023
theorem B5007131 : Blo 2223435 5007131 := bstep (se 1 (by rfl) ⟨3755348, by rfl⟩ : syracuseStep 5007131 = 7510697) B7510697
theorem B3338087 : Blo 2223435 3338087 := bstep (se 1 (by rfl) ⟨2503565, by rfl⟩ : syracuseStep 3338087 = 5007131) B5007131
theorem B2225391 : Blo 2223435 2225391 := bstep (se 1 (by rfl) ⟨1669043, by rfl⟩ : syracuseStep 2225391 = 3338087) B3338087
theorem B3338093 : Blo 2223435 3338093 := bbase (se 3 (by rfl) ⟨625892, by rfl⟩ : syracuseStep 3338093 = 1251785) (by norm_num)
theorem B2225395 : Blo 2223435 2225395 := bstep (se 1 (by rfl) ⟨1669046, by rfl⟩ : syracuseStep 2225395 = 3338093) B3338093
theorem B5007149 : Blo 2223435 5007149 := bbase (se 3 (by rfl) ⟨938840, by rfl⟩ : syracuseStep 5007149 = 1877681) (by norm_num)
theorem B3338099 : Blo 2223435 3338099 := bstep (se 1 (by rfl) ⟨2503574, by rfl⟩ : syracuseStep 3338099 = 5007149) B5007149
theorem B2225399 : Blo 2223435 2225399 := bstep (se 1 (by rfl) ⟨1669049, by rfl⟩ : syracuseStep 2225399 = 3338099) B3338099
theorem B9505781 : Blo 2223435 9505781 := bbase (se 5 (by rfl) ⟨445583, by rfl⟩ : syracuseStep 9505781 = 891167) (by norm_num)
theorem B6337187 : Blo 2223435 6337187 := bstep (se 1 (by rfl) ⟨4752890, by rfl⟩ : syracuseStep 6337187 = 9505781) B9505781
theorem B4224791 : Blo 2223435 4224791 := bstep (se 1 (by rfl) ⟨3168593, by rfl⟩ : syracuseStep 4224791 = 6337187) B6337187
theorem B2816527 : Blo 2223435 2816527 := bstep (se 1 (by rfl) ⟨2112395, by rfl⟩ : syracuseStep 2816527 = 4224791) B4224791
theorem B3755369 : Blo 2223435 3755369 := bstep (se 2 (by rfl) ⟨1408263, by rfl⟩ : syracuseStep 3755369 = 2816527) B2816527
theorem B2503579 : Blo 2223435 2503579 := bstep (se 1 (by rfl) ⟨1877684, by rfl⟩ : syracuseStep 2503579 = 3755369) B3755369
theorem B3338105 : Blo 2223435 3338105 := bstep (se 2 (by rfl) ⟨1251789, by rfl⟩ : syracuseStep 3338105 = 2503579) B2503579
theorem B2225403 : Blo 2223435 2225403 := bstep (se 1 (by rfl) ⟨1669052, by rfl⟩ : syracuseStep 2225403 = 3338105) B3338105
theorem B2673505 : Blo 2223435 2673505 := bbase (se 2 (by rfl) ⟨1002564, by rfl⟩ : syracuseStep 2673505 = 2005129) (by norm_num)
theorem B14258693 : Blo 2223435 14258693 := bstep (se 4 (by rfl) ⟨1336752, by rfl⟩ : syracuseStep 14258693 = 2673505) B2673505
theorem B38023181 : Blo 2223435 38023181 := bstep (se 3 (by rfl) ⟨7129346, by rfl⟩ : syracuseStep 38023181 = 14258693) B14258693
theorem B25348787 : Blo 2223435 25348787 := bstep (se 1 (by rfl) ⟨19011590, by rfl⟩ : syracuseStep 25348787 = 38023181) B38023181
theorem B16899191 : Blo 2223435 16899191 := bstep (se 1 (by rfl) ⟨12674393, by rfl⟩ : syracuseStep 16899191 = 25348787) B25348787
theorem B11266127 : Blo 2223435 11266127 := bstep (se 1 (by rfl) ⟨8449595, by rfl⟩ : syracuseStep 11266127 = 16899191) B16899191
theorem B7510751 : Blo 2223435 7510751 := bstep (se 1 (by rfl) ⟨5633063, by rfl⟩ : syracuseStep 7510751 = 11266127) B11266127
theorem B5007167 : Blo 2223435 5007167 := bstep (se 1 (by rfl) ⟨3755375, by rfl⟩ : syracuseStep 5007167 = 7510751) B7510751
theorem B3338111 : Blo 2223435 3338111 := bstep (se 1 (by rfl) ⟨2503583, by rfl⟩ : syracuseStep 3338111 = 5007167) B5007167
theorem B2225407 : Blo 2223435 2225407 := bstep (se 1 (by rfl) ⟨1669055, by rfl⟩ : syracuseStep 2225407 = 3338111) B3338111
theorem B3338117 : Blo 2223435 3338117 := bbase (se 4 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 3338117 = 625897) (by norm_num)
theorem B2225411 : Blo 2223435 2225411 := bstep (se 1 (by rfl) ⟨1669058, by rfl⟩ : syracuseStep 2225411 = 3338117) B3338117
theorem B3755389 : Blo 2223435 3755389 := bbase (se 3 (by rfl) ⟨704135, by rfl⟩ : syracuseStep 3755389 = 1408271) (by norm_num)
theorem B5007185 : Blo 2223435 5007185 := bstep (se 2 (by rfl) ⟨1877694, by rfl⟩ : syracuseStep 5007185 = 3755389) B3755389
theorem B3338123 : Blo 2223435 3338123 := bstep (se 1 (by rfl) ⟨2503592, by rfl⟩ : syracuseStep 3338123 = 5007185) B5007185
theorem B2225415 : Blo 2223435 2225415 := bstep (se 1 (by rfl) ⟨1669061, by rfl⟩ : syracuseStep 2225415 = 3338123) B3338123
theorem B2503597 : Blo 2223435 2503597 := bbase (se 3 (by rfl) ⟨469424, by rfl⟩ : syracuseStep 2503597 = 938849) (by norm_num)
theorem B3338129 : Blo 2223435 3338129 := bstep (se 2 (by rfl) ⟨1251798, by rfl⟩ : syracuseStep 3338129 = 2503597) B2503597
theorem B2225419 : Blo 2223435 2225419 := bstep (se 1 (by rfl) ⟨1669064, by rfl⟩ : syracuseStep 2225419 = 3338129) B3338129
theorem B7510805 : Blo 2223435 7510805 := bbase (se 6 (by rfl) ⟨176034, by rfl⟩ : syracuseStep 7510805 = 352069) (by norm_num)
theorem B5007203 : Blo 2223435 5007203 := bstep (se 1 (by rfl) ⟨3755402, by rfl⟩ : syracuseStep 5007203 = 7510805) B7510805
theorem B3338135 : Blo 2223435 3338135 := bstep (se 1 (by rfl) ⟨2503601, by rfl⟩ : syracuseStep 3338135 = 5007203) B5007203
theorem B2225423 : Blo 2223435 2225423 := bstep (se 1 (by rfl) ⟨1669067, by rfl⟩ : syracuseStep 2225423 = 3338135) B3338135
theorem B3338141 : Blo 2223435 3338141 := bbase (se 3 (by rfl) ⟨625901, by rfl⟩ : syracuseStep 3338141 = 1251803) (by norm_num)
theorem B2225427 : Blo 2223435 2225427 := bstep (se 1 (by rfl) ⟨1669070, by rfl⟩ : syracuseStep 2225427 = 3338141) B3338141
theorem B5007221 : Blo 2223435 5007221 := bbase (se 5 (by rfl) ⟨234713, by rfl⟩ : syracuseStep 5007221 = 469427) (by norm_num)
theorem B3338147 : Blo 2223435 3338147 := bstep (se 1 (by rfl) ⟨2503610, by rfl⟩ : syracuseStep 3338147 = 5007221) B5007221
theorem B2225431 : Blo 2223435 2225431 := bstep (se 1 (by rfl) ⟨1669073, by rfl⟩ : syracuseStep 2225431 = 3338147) B3338147
theorem B10572277 : Blo 2223435 10572277 := bbase (se 5 (by rfl) ⟨495575, by rfl⟩ : syracuseStep 10572277 = 991151) (by norm_num)
theorem B14096369 : Blo 2223435 14096369 := bstep (se 2 (by rfl) ⟨5286138, by rfl⟩ : syracuseStep 14096369 = 10572277) B10572277
theorem B9397579 : Blo 2223435 9397579 := bstep (se 1 (by rfl) ⟨7048184, by rfl⟩ : syracuseStep 9397579 = 14096369) B14096369
theorem B12530105 : Blo 2223435 12530105 := bstep (se 2 (by rfl) ⟨4698789, by rfl⟩ : syracuseStep 12530105 = 9397579) B9397579
theorem B8353403 : Blo 2223435 8353403 := bstep (se 1 (by rfl) ⟨6265052, by rfl⟩ : syracuseStep 8353403 = 12530105) B12530105
theorem B5568935 : Blo 2223435 5568935 := bstep (se 1 (by rfl) ⟨4176701, by rfl⟩ : syracuseStep 5568935 = 8353403) B8353403
theorem B59401973 : Blo 2223435 59401973 := bstep (se 5 (by rfl) ⟨2784467, by rfl⟩ : syracuseStep 59401973 = 5568935) B5568935
theorem B39601315 : Blo 2223435 39601315 := bstep (se 1 (by rfl) ⟨29700986, by rfl⟩ : syracuseStep 39601315 = 59401973) B59401973
theorem B52801753 : Blo 2223435 52801753 := bstep (se 2 (by rfl) ⟨19800657, by rfl⟩ : syracuseStep 52801753 = 39601315) B39601315
theorem B70402337 : Blo 2223435 70402337 := bstep (se 2 (by rfl) ⟨26400876, by rfl⟩ : syracuseStep 70402337 = 52801753) B52801753
theorem B46934891 : Blo 2223435 46934891 := bstep (se 1 (by rfl) ⟨35201168, by rfl⟩ : syracuseStep 46934891 = 70402337) B70402337
theorem B31289927 : Blo 2223435 31289927 := bstep (se 1 (by rfl) ⟨23467445, by rfl⟩ : syracuseStep 31289927 = 46934891) B46934891
theorem B333759221 : Blo 2223435 333759221 := bstep (se 5 (by rfl) ⟨15644963, by rfl⟩ : syracuseStep 333759221 = 31289927) B31289927
theorem B222506147 : Blo 2223435 222506147 := bstep (se 1 (by rfl) ⟨166879610, by rfl⟩ : syracuseStep 222506147 = 333759221) B333759221
theorem B593349725 : Blo 2223435 593349725 := bstep (se 3 (by rfl) ⟨111253073, by rfl⟩ : syracuseStep 593349725 = 222506147) B222506147
theorem B1582265933 : Blo 2223435 1582265933 := bstep (se 3 (by rfl) ⟨296674862, by rfl⟩ : syracuseStep 1582265933 = 593349725) B593349725
theorem B1054843955 : Blo 2223435 1054843955 := bstep (se 1 (by rfl) ⟨791132966, by rfl⟩ : syracuseStep 1054843955 = 1582265933) B1582265933
theorem B703229303 : Blo 2223435 703229303 := bstep (se 1 (by rfl) ⟨527421977, by rfl⟩ : syracuseStep 703229303 = 1054843955) B1054843955
theorem B468819535 : Blo 2223435 468819535 := bstep (se 1 (by rfl) ⟨351614651, by rfl⟩ : syracuseStep 468819535 = 703229303) B703229303
theorem B625092713 : Blo 2223435 625092713 := bstep (se 2 (by rfl) ⟨234409767, by rfl⟩ : syracuseStep 625092713 = 468819535) B468819535
theorem B416728475 : Blo 2223435 416728475 := bstep (se 1 (by rfl) ⟨312546356, by rfl⟩ : syracuseStep 416728475 = 625092713) B625092713
theorem B277818983 : Blo 2223435 277818983 := bstep (se 1 (by rfl) ⟨208364237, by rfl⟩ : syracuseStep 277818983 = 416728475) B416728475
theorem B185212655 : Blo 2223435 185212655 := bstep (se 1 (by rfl) ⟨138909491, by rfl⟩ : syracuseStep 185212655 = 277818983) B277818983
theorem B123475103 : Blo 2223435 123475103 := bstep (se 1 (by rfl) ⟨92606327, by rfl⟩ : syracuseStep 123475103 = 185212655) B185212655
theorem B82316735 : Blo 2223435 82316735 := bstep (se 1 (by rfl) ⟨61737551, by rfl⟩ : syracuseStep 82316735 = 123475103) B123475103
theorem B54877823 : Blo 2223435 54877823 := bstep (se 1 (by rfl) ⟨41158367, by rfl⟩ : syracuseStep 54877823 = 82316735) B82316735
theorem B36585215 : Blo 2223435 36585215 := bstep (se 1 (by rfl) ⟨27438911, by rfl⟩ : syracuseStep 36585215 = 54877823) B54877823
theorem B24390143 : Blo 2223435 24390143 := bstep (se 1 (by rfl) ⟨18292607, by rfl⟩ : syracuseStep 24390143 = 36585215) B36585215
theorem B16260095 : Blo 2223435 16260095 := bstep (se 1 (by rfl) ⟨12195071, by rfl⟩ : syracuseStep 16260095 = 24390143) B24390143
theorem B10840063 : Blo 2223435 10840063 := bstep (se 1 (by rfl) ⟨8130047, by rfl⟩ : syracuseStep 10840063 = 16260095) B16260095
theorem B14453417 : Blo 2223435 14453417 := bstep (se 2 (by rfl) ⟨5420031, by rfl⟩ : syracuseStep 14453417 = 10840063) B10840063
theorem B9635611 : Blo 2223435 9635611 := bstep (se 1 (by rfl) ⟨7226708, by rfl⟩ : syracuseStep 9635611 = 14453417) B14453417
theorem B12847481 : Blo 2223435 12847481 := bstep (se 2 (by rfl) ⟨4817805, by rfl⟩ : syracuseStep 12847481 = 9635611) B9635611
theorem B8564987 : Blo 2223435 8564987 := bstep (se 1 (by rfl) ⟨6423740, by rfl⟩ : syracuseStep 8564987 = 12847481) B12847481
theorem B22839965 : Blo 2223435 22839965 := bstep (se 3 (by rfl) ⟨4282493, by rfl⟩ : syracuseStep 22839965 = 8564987) B8564987
theorem B15226643 : Blo 2223435 15226643 := bstep (se 1 (by rfl) ⟨11419982, by rfl⟩ : syracuseStep 15226643 = 22839965) B22839965
theorem B10151095 : Blo 2223435 10151095 := bstep (se 1 (by rfl) ⟨7613321, by rfl⟩ : syracuseStep 10151095 = 15226643) B15226643
theorem B13534793 : Blo 2223435 13534793 := bstep (se 2 (by rfl) ⟨5075547, by rfl⟩ : syracuseStep 13534793 = 10151095) B10151095
theorem B9023195 : Blo 2223435 9023195 := bstep (se 1 (by rfl) ⟨6767396, by rfl⟩ : syracuseStep 9023195 = 13534793) B13534793
theorem B24061853 : Blo 2223435 24061853 := bstep (se 3 (by rfl) ⟨4511597, by rfl⟩ : syracuseStep 24061853 = 9023195) B9023195
theorem B16041235 : Blo 2223435 16041235 := bstep (se 1 (by rfl) ⟨12030926, by rfl⟩ : syracuseStep 16041235 = 24061853) B24061853
theorem B21388313 : Blo 2223435 21388313 := bstep (se 2 (by rfl) ⟨8020617, by rfl⟩ : syracuseStep 21388313 = 16041235) B16041235
theorem B14258875 : Blo 2223435 14258875 := bstep (se 1 (by rfl) ⟨10694156, by rfl⟩ : syracuseStep 14258875 = 21388313) B21388313
theorem B19011833 : Blo 2223435 19011833 := bstep (se 2 (by rfl) ⟨7129437, by rfl⟩ : syracuseStep 19011833 = 14258875) B14258875
theorem B12674555 : Blo 2223435 12674555 := bstep (se 1 (by rfl) ⟨9505916, by rfl⟩ : syracuseStep 12674555 = 19011833) B19011833
theorem B8449703 : Blo 2223435 8449703 := bstep (se 1 (by rfl) ⟨6337277, by rfl⟩ : syracuseStep 8449703 = 12674555) B12674555
theorem B5633135 : Blo 2223435 5633135 := bstep (se 1 (by rfl) ⟨4224851, by rfl⟩ : syracuseStep 5633135 = 8449703) B8449703
theorem B3755423 : Blo 2223435 3755423 := bstep (se 1 (by rfl) ⟨2816567, by rfl⟩ : syracuseStep 3755423 = 5633135) B5633135
theorem B2503615 : Blo 2223435 2503615 := bstep (se 1 (by rfl) ⟨1877711, by rfl⟩ : syracuseStep 2503615 = 3755423) B3755423
theorem B3338153 : Blo 2223435 3338153 := bstep (se 2 (by rfl) ⟨1251807, by rfl⟩ : syracuseStep 3338153 = 2503615) B2503615
theorem B2225435 : Blo 2223435 2225435 := bstep (se 1 (by rfl) ⟨1669076, by rfl⟩ : syracuseStep 2225435 = 3338153) B3338153
theorem C0 (j : ℕ) (h1 : 555858 ≤ j) (h2 : j ≤ 556358) : Blo 2223435 (4 * j + 3) := by
  interval_cases j
  · exact B2223435
  · exact B2223439
  · exact B2223443
  · exact B2223447
  · exact B2223451
  · exact B2223455
  · exact B2223459
  · exact B2223463
  · exact B2223467
  · exact B2223471
  · exact B2223475
  · exact B2223479
  · exact B2223483
  · exact B2223487
  · exact B2223491
  · exact B2223495
  · exact B2223499
  · exact B2223503
  · exact B2223507
  · exact B2223511
  · exact B2223515
  · exact B2223519
  · exact B2223523
  · exact B2223527
  · exact B2223531
  · exact B2223535
  · exact B2223539
  · exact B2223543
  · exact B2223547
  · exact B2223551
  · exact B2223555
  · exact B2223559
  · exact B2223563
  · exact B2223567
  · exact B2223571
  · exact B2223575
  · exact B2223579
  · exact B2223583
  · exact B2223587
  · exact B2223591
  · exact B2223595
  · exact B2223599
  · exact B2223603
  · exact B2223607
  · exact B2223611
  · exact B2223615
  · exact B2223619
  · exact B2223623
  · exact B2223627
  · exact B2223631
  · exact B2223635
  · exact B2223639
  · exact B2223643
  · exact B2223647
  · exact B2223651
  · exact B2223655
  · exact B2223659
  · exact B2223663
  · exact B2223667
  · exact B2223671
  · exact B2223675
  · exact B2223679
  · exact B2223683
  · exact B2223687
  · exact B2223691
  · exact B2223695
  · exact B2223699
  · exact B2223703
  · exact B2223707
  · exact B2223711
  · exact B2223715
  · exact B2223719
  · exact B2223723
  · exact B2223727
  · exact B2223731
  · exact B2223735
  · exact B2223739
  · exact B2223743
  · exact B2223747
  · exact B2223751
  · exact B2223755
  · exact B2223759
  · exact B2223763
  · exact B2223767
  · exact B2223771
  · exact B2223775
  · exact B2223779
  · exact B2223783
  · exact B2223787
  · exact B2223791
  · exact B2223795
  · exact B2223799
  · exact B2223803
  · exact B2223807
  · exact B2223811
  · exact B2223815
  · exact B2223819
  · exact B2223823
  · exact B2223827
  · exact B2223831
  · exact B2223835
  · exact B2223839
  · exact B2223843
  · exact B2223847
  · exact B2223851
  · exact B2223855
  · exact B2223859
  · exact B2223863
  · exact B2223867
  · exact B2223871
  · exact B2223875
  · exact B2223879
  · exact B2223883
  · exact B2223887
  · exact B2223891
  · exact B2223895
  · exact B2223899
  · exact B2223903
  · exact B2223907
  · exact B2223911
  · exact B2223915
  · exact B2223919
  · exact B2223923
  · exact B2223927
  · exact B2223931
  · exact B2223935
  · exact B2223939
  · exact B2223943
  · exact B2223947
  · exact B2223951
  · exact B2223955
  · exact B2223959
  · exact B2223963
  · exact B2223967
  · exact B2223971
  · exact B2223975
  · exact B2223979
  · exact B2223983
  · exact B2223987
  · exact B2223991
  · exact B2223995
  · exact B2223999
  · exact B2224003
  · exact B2224007
  · exact B2224011
  · exact B2224015
  · exact B2224019
  · exact B2224023
  · exact B2224027
  · exact B2224031
  · exact B2224035
  · exact B2224039
  · exact B2224043
  · exact B2224047
  · exact B2224051
  · exact B2224055
  · exact B2224059
  · exact B2224063
  · exact B2224067
  · exact B2224071
  · exact B2224075
  · exact B2224079
  · exact B2224083
  · exact B2224087
  · exact B2224091
  · exact B2224095
  · exact B2224099
  · exact B2224103
  · exact B2224107
  · exact B2224111
  · exact B2224115
  · exact B2224119
  · exact B2224123
  · exact B2224127
  · exact B2224131
  · exact B2224135
  · exact B2224139
  · exact B2224143
  · exact B2224147
  · exact B2224151
  · exact B2224155
  · exact B2224159
  · exact B2224163
  · exact B2224167
  · exact B2224171
  · exact B2224175
  · exact B2224179
  · exact B2224183
  · exact B2224187
  · exact B2224191
  · exact B2224195
  · exact B2224199
  · exact B2224203
  · exact B2224207
  · exact B2224211
  · exact B2224215
  · exact B2224219
  · exact B2224223
  · exact B2224227
  · exact B2224231
  · exact B2224235
  · exact B2224239
  · exact B2224243
  · exact B2224247
  · exact B2224251
  · exact B2224255
  · exact B2224259
  · exact B2224263
  · exact B2224267
  · exact B2224271
  · exact B2224275
  · exact B2224279
  · exact B2224283
  · exact B2224287
  · exact B2224291
  · exact B2224295
  · exact B2224299
  · exact B2224303
  · exact B2224307
  · exact B2224311
  · exact B2224315
  · exact B2224319
  · exact B2224323
  · exact B2224327
  · exact B2224331
  · exact B2224335
  · exact B2224339
  · exact B2224343
  · exact B2224347
  · exact B2224351
  · exact B2224355
  · exact B2224359
  · exact B2224363
  · exact B2224367
  · exact B2224371
  · exact B2224375
  · exact B2224379
  · exact B2224383
  · exact B2224387
  · exact B2224391
  · exact B2224395
  · exact B2224399
  · exact B2224403
  · exact B2224407
  · exact B2224411
  · exact B2224415
  · exact B2224419
  · exact B2224423
  · exact B2224427
  · exact B2224431
  · exact B2224435
  · exact B2224439
  · exact B2224443
  · exact B2224447
  · exact B2224451
  · exact B2224455
  · exact B2224459
  · exact B2224463
  · exact B2224467
  · exact B2224471
  · exact B2224475
  · exact B2224479
  · exact B2224483
  · exact B2224487
  · exact B2224491
  · exact B2224495
  · exact B2224499
  · exact B2224503
  · exact B2224507
  · exact B2224511
  · exact B2224515
  · exact B2224519
  · exact B2224523
  · exact B2224527
  · exact B2224531
  · exact B2224535
  · exact B2224539
  · exact B2224543
  · exact B2224547
  · exact B2224551
  · exact B2224555
  · exact B2224559
  · exact B2224563
  · exact B2224567
  · exact B2224571
  · exact B2224575
  · exact B2224579
  · exact B2224583
  · exact B2224587
  · exact B2224591
  · exact B2224595
  · exact B2224599
  · exact B2224603
  · exact B2224607
  · exact B2224611
  · exact B2224615
  · exact B2224619
  · exact B2224623
  · exact B2224627
  · exact B2224631
  · exact B2224635
  · exact B2224639
  · exact B2224643
  · exact B2224647
  · exact B2224651
  · exact B2224655
  · exact B2224659
  · exact B2224663
  · exact B2224667
  · exact B2224671
  · exact B2224675
  · exact B2224679
  · exact B2224683
  · exact B2224687
  · exact B2224691
  · exact B2224695
  · exact B2224699
  · exact B2224703
  · exact B2224707
  · exact B2224711
  · exact B2224715
  · exact B2224719
  · exact B2224723
  · exact B2224727
  · exact B2224731
  · exact B2224735
  · exact B2224739
  · exact B2224743
  · exact B2224747
  · exact B2224751
  · exact B2224755
  · exact B2224759
  · exact B2224763
  · exact B2224767
  · exact B2224771
  · exact B2224775
  · exact B2224779
  · exact B2224783
  · exact B2224787
  · exact B2224791
  · exact B2224795
  · exact B2224799
  · exact B2224803
  · exact B2224807
  · exact B2224811
  · exact B2224815
  · exact B2224819
  · exact B2224823
  · exact B2224827
  · exact B2224831
  · exact B2224835
  · exact B2224839
  · exact B2224843
  · exact B2224847
  · exact B2224851
  · exact B2224855
  · exact B2224859
  · exact B2224863
  · exact B2224867
  · exact B2224871
  · exact B2224875
  · exact B2224879
  · exact B2224883
  · exact B2224887
  · exact B2224891
  · exact B2224895
  · exact B2224899
  · exact B2224903
  · exact B2224907
  · exact B2224911
  · exact B2224915
  · exact B2224919
  · exact B2224923
  · exact B2224927
  · exact B2224931
  · exact B2224935
  · exact B2224939
  · exact B2224943
  · exact B2224947
  · exact B2224951
  · exact B2224955
  · exact B2224959
  · exact B2224963
  · exact B2224967
  · exact B2224971
  · exact B2224975
  · exact B2224979
  · exact B2224983
  · exact B2224987
  · exact B2224991
  · exact B2224995
  · exact B2224999
  · exact B2225003
  · exact B2225007
  · exact B2225011
  · exact B2225015
  · exact B2225019
  · exact B2225023
  · exact B2225027
  · exact B2225031
  · exact B2225035
  · exact B2225039
  · exact B2225043
  · exact B2225047
  · exact B2225051
  · exact B2225055
  · exact B2225059
  · exact B2225063
  · exact B2225067
  · exact B2225071
  · exact B2225075
  · exact B2225079
  · exact B2225083
  · exact B2225087
  · exact B2225091
  · exact B2225095
  · exact B2225099
  · exact B2225103
  · exact B2225107
  · exact B2225111
  · exact B2225115
  · exact B2225119
  · exact B2225123
  · exact B2225127
  · exact B2225131
  · exact B2225135
  · exact B2225139
  · exact B2225143
  · exact B2225147
  · exact B2225151
  · exact B2225155
  · exact B2225159
  · exact B2225163
  · exact B2225167
  · exact B2225171
  · exact B2225175
  · exact B2225179
  · exact B2225183
  · exact B2225187
  · exact B2225191
  · exact B2225195
  · exact B2225199
  · exact B2225203
  · exact B2225207
  · exact B2225211
  · exact B2225215
  · exact B2225219
  · exact B2225223
  · exact B2225227
  · exact B2225231
  · exact B2225235
  · exact B2225239
  · exact B2225243
  · exact B2225247
  · exact B2225251
  · exact B2225255
  · exact B2225259
  · exact B2225263
  · exact B2225267
  · exact B2225271
  · exact B2225275
  · exact B2225279
  · exact B2225283
  · exact B2225287
  · exact B2225291
  · exact B2225295
  · exact B2225299
  · exact B2225303
  · exact B2225307
  · exact B2225311
  · exact B2225315
  · exact B2225319
  · exact B2225323
  · exact B2225327
  · exact B2225331
  · exact B2225335
  · exact B2225339
  · exact B2225343
  · exact B2225347
  · exact B2225351
  · exact B2225355
  · exact B2225359
  · exact B2225363
  · exact B2225367
  · exact B2225371
  · exact B2225375
  · exact B2225379
  · exact B2225383
  · exact B2225387
  · exact B2225391
  · exact B2225395
  · exact B2225399
  · exact B2225403
  · exact B2225407
  · exact B2225411
  · exact B2225415
  · exact B2225419
  · exact B2225423
  · exact B2225427
  · exact B2225431
  · exact B2225435
theorem solution (m : ℕ) (hlo : 2223435 ≤ m) (hhi : m ≤ 2225435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 555858 ≤ j := by omega
    have hj2 : j ≤ 556358 := by omega
    have hb : Blo 2223435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
