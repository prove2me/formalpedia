-- Prove2me | solution 1 for syracuse_descends_range_1425532_1427532
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:41:41.115188+00:00
-- url     : https://prove2.me/submissions/6426d2e1-db2e-460d-b878-dbe29f40453e

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


theorem B1605649 : Blo 1425532 1605649 := bbase (se 2 (by rfl) ⟨602118, by rfl⟩ : syracuseStep 1605649 = 1204237) (by norm_num)
theorem B5783573 : Blo 1425532 5783573 := bbase (se 6 (by rfl) ⟨135552, by rfl⟩ : syracuseStep 5783573 = 271105) (by norm_num)
theorem B3612701 : Blo 1425532 3612701 := bbase (se 3 (by rfl) ⟨677381, by rfl⟩ : syracuseStep 3612701 = 1354763) (by norm_num)
theorem B2408501 : Blo 1425532 2408501 := bbase (se 5 (by rfl) ⟨112898, by rfl⟩ : syracuseStep 2408501 = 225797) (by norm_num)
theorem B1605685 : Blo 1425532 1605685 := bbase (se 5 (by rfl) ⟨75266, by rfl⟩ : syracuseStep 1605685 = 150533) (by norm_num)
theorem B3211325 : Blo 1425532 3211325 := bbase (se 3 (by rfl) ⟨602123, by rfl⟩ : syracuseStep 3211325 = 1204247) (by norm_num)
theorem B1605721 : Blo 1425532 1605721 := bbase (se 2 (by rfl) ⟨602145, by rfl⟩ : syracuseStep 1605721 = 1204291) (by norm_num)
theorem B1605757 : Blo 1425532 1605757 := bbase (se 3 (by rfl) ⟨301079, by rfl⟩ : syracuseStep 1605757 = 602159) (by norm_num)
theorem B3211397 : Blo 1425532 3211397 := bbase (se 4 (by rfl) ⟨301068, by rfl⟩ : syracuseStep 3211397 = 602137) (by norm_num)
theorem B1605793 : Blo 1425532 1605793 := bbase (se 2 (by rfl) ⟨602172, by rfl⟩ : syracuseStep 1605793 = 1204345) (by norm_num)
theorem B2408629 : Blo 1425532 2408629 := bbase (se 5 (by rfl) ⟨112904, by rfl⟩ : syracuseStep 2408629 = 225809) (by norm_num)
theorem B2138309 : Blo 1425532 2138309 := bbase (se 4 (by rfl) ⟨200466, by rfl⟩ : syracuseStep 2138309 = 400933) (by norm_num)
theorem B1605829 : Blo 1425532 1605829 := bbase (se 4 (by rfl) ⟨150546, by rfl⟩ : syracuseStep 1605829 = 301093) (by norm_num)
theorem B3211469 : Blo 1425532 3211469 := bbase (se 3 (by rfl) ⟨602150, by rfl⟩ : syracuseStep 3211469 = 1204301) (by norm_num)
theorem B2138333 : Blo 1425532 2138333 := bbase (se 3 (by rfl) ⟨400937, by rfl⟩ : syracuseStep 2138333 = 801875) (by norm_num)
theorem B3047645 : Blo 1425532 3047645 := bbase (se 3 (by rfl) ⟨571433, by rfl⟩ : syracuseStep 3047645 = 1142867) (by norm_num)
theorem B3047653 : Blo 1425532 3047653 := bbase (se 4 (by rfl) ⟨285717, by rfl⟩ : syracuseStep 3047653 = 571435) (by norm_num)
theorem B1605865 : Blo 1425532 1605865 := bbase (se 2 (by rfl) ⟨602199, by rfl⟩ : syracuseStep 1605865 = 1204399) (by norm_num)
theorem B2138357 : Blo 1425532 2138357 := bbase (se 5 (by rfl) ⟨100235, by rfl⟩ : syracuseStep 2138357 = 200471) (by norm_num)
theorem B2138381 : Blo 1425532 2138381 := bbase (se 3 (by rfl) ⟨400946, by rfl⟩ : syracuseStep 2138381 = 801893) (by norm_num)
theorem B2285837 : Blo 1425532 2285837 := bbase (se 3 (by rfl) ⟨428594, by rfl⟩ : syracuseStep 2285837 = 857189) (by norm_num)
theorem B3211541 : Blo 1425532 3211541 := bbase (se 6 (by rfl) ⟨75270, by rfl⟩ : syracuseStep 3211541 = 150541) (by norm_num)
theorem B2408717 : Blo 1425532 2408717 := bbase (se 3 (by rfl) ⟨451634, by rfl⟩ : syracuseStep 2408717 = 903269) (by norm_num)
theorem B2138405 : Blo 1425532 2138405 := bbase (se 4 (by rfl) ⟨200475, by rfl⟩ : syracuseStep 2138405 = 400951) (by norm_num)
theorem B1605937 : Blo 1425532 1605937 := bbase (se 2 (by rfl) ⟨602226, by rfl⟩ : syracuseStep 1605937 = 1204453) (by norm_num)
theorem B2138429 : Blo 1425532 2138429 := bbase (se 3 (by rfl) ⟨400955, by rfl⟩ : syracuseStep 2138429 = 801911) (by norm_num)
theorem B2138453 : Blo 1425532 2138453 := bbase (se 10 (by rfl) ⟨3132, by rfl⟩ : syracuseStep 2138453 = 6265) (by norm_num)
theorem B7225685 : Blo 1425532 7225685 := bbase (se 10 (by rfl) ⟨10584, by rfl⟩ : syracuseStep 7225685 = 21169) (by norm_num)
theorem B1605973 : Blo 1425532 1605973 := bbase (se 10 (by rfl) ⟨2352, by rfl⟩ : syracuseStep 1605973 = 4705) (by norm_num)
theorem B3211613 : Blo 1425532 3211613 := bbase (se 3 (by rfl) ⟨602177, by rfl⟩ : syracuseStep 3211613 = 1204355) (by norm_num)
theorem B2138477 : Blo 1425532 2138477 := bbase (se 3 (by rfl) ⟨400964, by rfl⟩ : syracuseStep 2138477 = 801929) (by norm_num)
theorem B3613045 : Blo 1425532 3613045 := bbase (se 5 (by rfl) ⟨169361, by rfl⟩ : syracuseStep 3613045 = 338723) (by norm_num)
theorem B2138501 : Blo 1425532 2138501 := bbase (se 4 (by rfl) ⟨200484, by rfl⟩ : syracuseStep 2138501 = 400969) (by norm_num)
theorem B4817285 : Blo 1425532 4817285 := bbase (se 4 (by rfl) ⟨451620, by rfl⟩ : syracuseStep 4817285 = 903241) (by norm_num)
theorem B2408845 : Blo 1425532 2408845 := bbase (se 3 (by rfl) ⟨451658, by rfl⟩ : syracuseStep 2408845 = 903317) (by norm_num)
theorem B4882837 : Blo 1425532 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B2138525 : Blo 1425532 2138525 := bbase (se 3 (by rfl) ⟨400973, by rfl⟩ : syracuseStep 2138525 = 801947) (by norm_num)
theorem B3211685 : Blo 1425532 3211685 := bbase (se 4 (by rfl) ⟨301095, by rfl⟩ : syracuseStep 3211685 = 602191) (by norm_num)
theorem B1761713 : Blo 1425532 1761713 := bbase (se 2 (by rfl) ⟨660642, by rfl⟩ : syracuseStep 1761713 = 1321285) (by norm_num)
theorem B2138549 : Blo 1425532 2138549 := bbase (se 5 (by rfl) ⟨100244, by rfl⟩ : syracuseStep 2138549 = 200489) (by norm_num)
theorem B2138573 : Blo 1425532 2138573 := bbase (se 3 (by rfl) ⟨400982, by rfl⟩ : syracuseStep 2138573 = 801965) (by norm_num)
theorem B2138597 : Blo 1425532 2138597 := bbase (se 4 (by rfl) ⟨200493, by rfl⟩ : syracuseStep 2138597 = 400987) (by norm_num)
theorem B3613157 : Blo 1425532 3613157 := bbase (se 4 (by rfl) ⟨338733, by rfl⟩ : syracuseStep 3613157 = 677467) (by norm_num)
theorem B2408933 : Blo 1425532 2408933 := bbase (se 4 (by rfl) ⟨225837, by rfl⟩ : syracuseStep 2408933 = 451675) (by norm_num)
theorem B3211757 : Blo 1425532 3211757 := bbase (se 3 (by rfl) ⟨602204, by rfl⟩ : syracuseStep 3211757 = 1204409) (by norm_num)
theorem B2138621 : Blo 1425532 2138621 := bbase (se 3 (by rfl) ⟨400991, by rfl⟩ : syracuseStep 2138621 = 801983) (by norm_num)
theorem B2032133 : Blo 1425532 2032133 := bbase (se 4 (by rfl) ⟨190512, by rfl⟩ : syracuseStep 2032133 = 381025) (by norm_num)
theorem B2138645 : Blo 1425532 2138645 := bbase (se 6 (by rfl) ⟨50124, by rfl⟩ : syracuseStep 2138645 = 100249) (by norm_num)
theorem B4063765 : Blo 1425532 4063765 := bbase (se 6 (by rfl) ⟨95244, by rfl⟩ : syracuseStep 4063765 = 190489) (by norm_num)
theorem B2138669 : Blo 1425532 2138669 := bbase (se 3 (by rfl) ⟨401000, by rfl⟩ : syracuseStep 2138669 = 802001) (by norm_num)
theorem B3211829 : Blo 1425532 3211829 := bbase (se 5 (by rfl) ⟨150554, by rfl⟩ : syracuseStep 3211829 = 301109) (by norm_num)
theorem B2138693 : Blo 1425532 2138693 := bbase (se 4 (by rfl) ⟨200502, by rfl⟩ : syracuseStep 2138693 = 401005) (by norm_num)
theorem B1524305 : Blo 1425532 1524305 := bbase (se 2 (by rfl) ⟨571614, by rfl⟩ : syracuseStep 1524305 = 1143229) (by norm_num)
theorem B2138717 : Blo 1425532 2138717 := bbase (se 3 (by rfl) ⟨401009, by rfl⟩ : syracuseStep 2138717 = 802019) (by norm_num)
theorem B2138741 : Blo 1425532 2138741 := bbase (se 5 (by rfl) ⟨100253, by rfl⟩ : syracuseStep 2138741 = 200507) (by norm_num)
theorem B3211901 : Blo 1425532 3211901 := bbase (se 3 (by rfl) ⟨602231, by rfl⟩ : syracuseStep 3211901 = 1204463) (by norm_num)
theorem B2138765 : Blo 1425532 2138765 := bbase (se 3 (by rfl) ⟨401018, by rfl⟩ : syracuseStep 2138765 = 802037) (by norm_num)
theorem B2138789 : Blo 1425532 2138789 := bbase (se 4 (by rfl) ⟨200511, by rfl⟩ : syracuseStep 2138789 = 401023) (by norm_num)
theorem B2507429 : Blo 1425532 2507429 := bbase (se 4 (by rfl) ⟨235071, by rfl⟩ : syracuseStep 2507429 = 470143) (by norm_num)
theorem B3613349 : Blo 1425532 3613349 := bbase (se 4 (by rfl) ⟨338751, by rfl⟩ : syracuseStep 3613349 = 677503) (by norm_num)
theorem B5415605 : Blo 1425532 5415605 := bbase (se 5 (by rfl) ⟨253856, by rfl⟩ : syracuseStep 5415605 = 507713) (by norm_num)
theorem B4063925 : Blo 1425532 4063925 := bbase (se 5 (by rfl) ⟨190496, by rfl⟩ : syracuseStep 4063925 = 380993) (by norm_num)
theorem B2138813 : Blo 1425532 2138813 := bbase (se 3 (by rfl) ⟨401027, by rfl⟩ : syracuseStep 2138813 = 802055) (by norm_num)
theorem B2138837 : Blo 1425532 2138837 := bbase (se 7 (by rfl) ⟨25064, by rfl⟩ : syracuseStep 2138837 = 50129) (by norm_num)
theorem B2138861 : Blo 1425532 2138861 := bbase (se 3 (by rfl) ⟨401036, by rfl⟩ : syracuseStep 2138861 = 802073) (by norm_num)
theorem B7217909 : Blo 1425532 7217909 := bbase (se 5 (by rfl) ⟨338339, by rfl⟩ : syracuseStep 7217909 = 676679) (by norm_num)
theorem B2138885 : Blo 1425532 2138885 := bbase (se 4 (by rfl) ⟨200520, by rfl⟩ : syracuseStep 2138885 = 401041) (by norm_num)
theorem B1712917 : Blo 1425532 1712917 := bbase (se 6 (by rfl) ⟨40146, by rfl⟩ : syracuseStep 1712917 = 80293) (by norm_num)
theorem B1712921 : Blo 1425532 1712921 := bbase (se 2 (by rfl) ⟨642345, by rfl⟩ : syracuseStep 1712921 = 1284691) (by norm_num)
theorem B2138909 : Blo 1425532 2138909 := bbase (se 3 (by rfl) ⟨401045, by rfl⟩ : syracuseStep 2138909 = 802091) (by norm_num)
theorem B2138933 : Blo 1425532 2138933 := bbase (se 5 (by rfl) ⟨100262, by rfl⟩ : syracuseStep 2138933 = 200525) (by norm_num)
theorem B4817717 : Blo 1425532 4817717 := bbase (se 5 (by rfl) ⟨225830, by rfl⟩ : syracuseStep 4817717 = 451661) (by norm_num)
theorem B2138957 : Blo 1425532 2138957 := bbase (se 3 (by rfl) ⟨401054, by rfl⟩ : syracuseStep 2138957 = 802109) (by norm_num)
theorem B8790869 : Blo 1425532 8790869 := bbase (se 9 (by rfl) ⟨25754, by rfl⟩ : syracuseStep 8790869 = 51509) (by norm_num)
theorem B2138981 : Blo 1425532 2138981 := bbase (se 4 (by rfl) ⟨200529, by rfl⟩ : syracuseStep 2138981 = 401059) (by norm_num)
theorem B1737577 : Blo 1425532 1737577 := bbase (se 2 (by rfl) ⟨651591, by rfl⟩ : syracuseStep 1737577 = 1303183) (by norm_num)
theorem B2139005 : Blo 1425532 2139005 := bbase (se 3 (by rfl) ⟨401063, by rfl⟩ : syracuseStep 2139005 = 802127) (by norm_num)
theorem B2139029 : Blo 1425532 2139029 := bbase (se 6 (by rfl) ⟨50133, by rfl⟩ : syracuseStep 2139029 = 100267) (by norm_num)
theorem B4064165 : Blo 1425532 4064165 := bbase (se 4 (by rfl) ⟨381015, by rfl⟩ : syracuseStep 4064165 = 762031) (by norm_num)
theorem B2139053 : Blo 1425532 2139053 := bbase (se 3 (by rfl) ⟨401072, by rfl⟩ : syracuseStep 2139053 = 802145) (by norm_num)
theorem B2139077 : Blo 1425532 2139077 := bbase (se 4 (by rfl) ⟨200538, by rfl⟩ : syracuseStep 2139077 = 401077) (by norm_num)
theorem B5415893 : Blo 1425532 5415893 := bbase (se 7 (by rfl) ⟨63467, by rfl⟩ : syracuseStep 5415893 = 126935) (by norm_num)
theorem B2139101 : Blo 1425532 2139101 := bbase (se 3 (by rfl) ⟨401081, by rfl⟩ : syracuseStep 2139101 = 802163) (by norm_num)
theorem B2139125 : Blo 1425532 2139125 := bbase (se 5 (by rfl) ⟨100271, by rfl⟩ : syracuseStep 2139125 = 200543) (by norm_num)
theorem B2139149 : Blo 1425532 2139149 := bbase (se 3 (by rfl) ⟨401090, by rfl⟩ : syracuseStep 2139149 = 802181) (by norm_num)
theorem B2139173 : Blo 1425532 2139173 := bbase (se 4 (by rfl) ⟨200547, by rfl⟩ : syracuseStep 2139173 = 401095) (by norm_num)
theorem B2139197 : Blo 1425532 2139197 := bbase (se 3 (by rfl) ⟨401099, by rfl⟩ : syracuseStep 2139197 = 802199) (by norm_num)
theorem B3253325 : Blo 1425532 3253325 := bbase (se 3 (by rfl) ⟨609998, by rfl⟩ : syracuseStep 3253325 = 1219997) (by norm_num)
theorem B2139221 : Blo 1425532 2139221 := bbase (se 8 (by rfl) ⟨12534, by rfl⟩ : syracuseStep 2139221 = 25069) (by norm_num)
theorem B4064357 : Blo 1425532 4064357 := bbase (se 4 (by rfl) ⟨381033, by rfl⟩ : syracuseStep 4064357 = 762067) (by norm_num)
theorem B2139245 : Blo 1425532 2139245 := bbase (se 3 (by rfl) ⟨401108, by rfl⟩ : syracuseStep 2139245 = 802217) (by norm_num)
theorem B6095989 : Blo 1425532 6095989 := bbase (se 5 (by rfl) ⟨285749, by rfl⟩ : syracuseStep 6095989 = 571499) (by norm_num)
theorem B2139269 : Blo 1425532 2139269 := bbase (se 4 (by rfl) ⟨200556, by rfl⟩ : syracuseStep 2139269 = 401113) (by norm_num)
theorem B2139293 : Blo 1425532 2139293 := bbase (se 3 (by rfl) ⟨401117, by rfl⟩ : syracuseStep 2139293 = 802235) (by norm_num)
theorem B2139317 : Blo 1425532 2139317 := bbase (se 5 (by rfl) ⟨100280, by rfl⟩ : syracuseStep 2139317 = 200561) (by norm_num)
theorem B2139341 : Blo 1425532 2139341 := bbase (se 3 (by rfl) ⟨401126, by rfl⟩ : syracuseStep 2139341 = 802253) (by norm_num)
theorem B2139365 : Blo 1425532 2139365 := bbase (se 4 (by rfl) ⟨200565, by rfl⟩ : syracuseStep 2139365 = 401131) (by norm_num)
theorem B2139389 : Blo 1425532 2139389 := bbase (se 3 (by rfl) ⟨401135, by rfl⟩ : syracuseStep 2139389 = 802271) (by norm_num)
theorem B1713421 : Blo 1425532 1713421 := bbase (se 3 (by rfl) ⟨321266, by rfl⟩ : syracuseStep 1713421 = 642533) (by norm_num)
theorem B2139413 : Blo 1425532 2139413 := bbase (se 6 (by rfl) ⟨50142, by rfl⟩ : syracuseStep 2139413 = 100285) (by norm_num)
theorem B2139437 : Blo 1425532 2139437 := bbase (se 3 (by rfl) ⟨401144, by rfl⟩ : syracuseStep 2139437 = 802289) (by norm_num)
theorem B2139461 : Blo 1425532 2139461 := bbase (se 4 (by rfl) ⟨200574, by rfl⟩ : syracuseStep 2139461 = 401149) (by norm_num)
theorem B3048781 : Blo 1425532 3048781 := bbase (se 3 (by rfl) ⟨571646, by rfl⟩ : syracuseStep 3048781 = 1143293) (by norm_num)
theorem B2139485 : Blo 1425532 2139485 := bbase (se 3 (by rfl) ⟨401153, by rfl⟩ : syracuseStep 2139485 = 802307) (by norm_num)
theorem B2139509 : Blo 1425532 2139509 := bbase (se 5 (by rfl) ⟨100289, by rfl⟩ : syracuseStep 2139509 = 200579) (by norm_num)
theorem B2139533 : Blo 1425532 2139533 := bbase (se 3 (by rfl) ⟨401162, by rfl⟩ : syracuseStep 2139533 = 802325) (by norm_num)
theorem B5137829 : Blo 1425532 5137829 := bbase (se 4 (by rfl) ⟨481671, by rfl⟩ : syracuseStep 5137829 = 963343) (by norm_num)
theorem B2139557 : Blo 1425532 2139557 := bbase (se 4 (by rfl) ⟨200583, by rfl⟩ : syracuseStep 2139557 = 401167) (by norm_num)
theorem B2139581 : Blo 1425532 2139581 := bbase (se 3 (by rfl) ⟨401171, by rfl⟩ : syracuseStep 2139581 = 802343) (by norm_num)
theorem B2139605 : Blo 1425532 2139605 := bbase (se 7 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 2139605 = 50147) (by norm_num)
theorem B2139629 : Blo 1425532 2139629 := bbase (se 3 (by rfl) ⟨401180, by rfl⟩ : syracuseStep 2139629 = 802361) (by norm_num)
theorem B2139653 : Blo 1425532 2139653 := bbase (se 4 (by rfl) ⟨200592, by rfl⟩ : syracuseStep 2139653 = 401185) (by norm_num)
theorem B2139677 : Blo 1425532 2139677 := bbase (se 3 (by rfl) ⟨401189, by rfl⟩ : syracuseStep 2139677 = 802379) (by norm_num)
theorem B2139701 : Blo 1425532 2139701 := bbase (se 5 (by rfl) ⟨100298, by rfl⟩ : syracuseStep 2139701 = 200597) (by norm_num)
theorem B2139725 : Blo 1425532 2139725 := bbase (se 3 (by rfl) ⟨401198, by rfl⟩ : syracuseStep 2139725 = 802397) (by norm_num)
theorem B2139749 : Blo 1425532 2139749 := bbase (se 4 (by rfl) ⟨200601, by rfl⟩ : syracuseStep 2139749 = 401203) (by norm_num)
theorem B2139773 : Blo 1425532 2139773 := bbase (se 3 (by rfl) ⟨401207, by rfl⟩ : syracuseStep 2139773 = 802415) (by norm_num)
theorem B1713805 : Blo 1425532 1713805 := bbase (se 3 (by rfl) ⟨321338, by rfl⟩ : syracuseStep 1713805 = 642677) (by norm_num)
theorem B2139797 : Blo 1425532 2139797 := bbase (se 6 (by rfl) ⟨50151, by rfl⟩ : syracuseStep 2139797 = 100303) (by norm_num)
theorem B2139821 : Blo 1425532 2139821 := bbase (se 3 (by rfl) ⟨401216, by rfl⟩ : syracuseStep 2139821 = 802433) (by norm_num)
theorem B2139845 : Blo 1425532 2139845 := bbase (se 4 (by rfl) ⟨200610, by rfl⟩ : syracuseStep 2139845 = 401221) (by norm_num)
theorem B2139869 : Blo 1425532 2139869 := bbase (se 3 (by rfl) ⟨401225, by rfl⟩ : syracuseStep 2139869 = 802451) (by norm_num)
theorem B2139893 : Blo 1425532 2139893 := bbase (se 5 (by rfl) ⟨100307, by rfl⟩ : syracuseStep 2139893 = 200615) (by norm_num)
theorem B2139917 : Blo 1425532 2139917 := bbase (se 3 (by rfl) ⟨401234, by rfl⟩ : syracuseStep 2139917 = 802469) (by norm_num)
theorem B15255317 : Blo 1425532 15255317 := bbase (se 6 (by rfl) ⟨357546, by rfl⟩ : syracuseStep 15255317 = 715093) (by norm_num)
theorem B2139941 : Blo 1425532 2139941 := bbase (se 4 (by rfl) ⟨200619, by rfl⟩ : syracuseStep 2139941 = 401239) (by norm_num)
theorem B2139965 : Blo 1425532 2139965 := bbase (se 3 (by rfl) ⟨401243, by rfl⟩ : syracuseStep 2139965 = 802487) (by norm_num)
theorem B2139989 : Blo 1425532 2139989 := bbase (se 9 (by rfl) ⟨6269, by rfl⟩ : syracuseStep 2139989 = 12539) (by norm_num)
theorem B2140013 : Blo 1425532 2140013 := bbase (se 3 (by rfl) ⟨401252, by rfl⟩ : syracuseStep 2140013 = 802505) (by norm_num)
theorem B9135989 : Blo 1425532 9135989 := bbase (se 5 (by rfl) ⟨428249, by rfl⟩ : syracuseStep 9135989 = 856499) (by norm_num)
theorem B2140037 : Blo 1425532 2140037 := bbase (se 4 (by rfl) ⟨200628, by rfl⟩ : syracuseStep 2140037 = 401257) (by norm_num)
theorem B2140061 : Blo 1425532 2140061 := bbase (se 3 (by rfl) ⟨401261, by rfl⟩ : syracuseStep 2140061 = 802523) (by norm_num)
theorem B2140085 : Blo 1425532 2140085 := bbase (se 5 (by rfl) ⟨100316, by rfl⟩ : syracuseStep 2140085 = 200633) (by norm_num)
theorem B2140109 : Blo 1425532 2140109 := bbase (se 3 (by rfl) ⟨401270, by rfl⟩ : syracuseStep 2140109 = 802541) (by norm_num)
theorem B2140133 : Blo 1425532 2140133 := bbase (se 4 (by rfl) ⟨200637, by rfl⟩ : syracuseStep 2140133 = 401275) (by norm_num)
theorem B1804285 : Blo 1425532 1804285 := bbase (se 3 (by rfl) ⟨338303, by rfl⟩ : syracuseStep 1804285 = 676607) (by norm_num)
theorem B2140157 : Blo 1425532 2140157 := bbase (se 3 (by rfl) ⟨401279, by rfl⟩ : syracuseStep 2140157 = 802559) (by norm_num)
theorem B7219205 : Blo 1425532 7219205 := bbase (se 4 (by rfl) ⟨676800, by rfl⟩ : syracuseStep 7219205 = 1353601) (by norm_num)
theorem B2140181 : Blo 1425532 2140181 := bbase (se 6 (by rfl) ⟨50160, by rfl⟩ : syracuseStep 2140181 = 100321) (by norm_num)
theorem B2140205 : Blo 1425532 2140205 := bbase (se 3 (by rfl) ⟨401288, by rfl⟩ : syracuseStep 2140205 = 802577) (by norm_num)
theorem B2140229 : Blo 1425532 2140229 := bbase (se 4 (by rfl) ⟨200646, by rfl⟩ : syracuseStep 2140229 = 401293) (by norm_num)
theorem B3254357 : Blo 1425532 3254357 := bbase (se 8 (by rfl) ⟨19068, by rfl⟩ : syracuseStep 3254357 = 38137) (by norm_num)
theorem B2140253 : Blo 1425532 2140253 := bbase (se 3 (by rfl) ⟨401297, by rfl⟩ : syracuseStep 2140253 = 802595) (by norm_num)
theorem B5564533 : Blo 1425532 5564533 := bbase (se 5 (by rfl) ⟨260837, by rfl⟩ : syracuseStep 5564533 = 521675) (by norm_num)
theorem B5417077 : Blo 1425532 5417077 := bbase (se 5 (by rfl) ⟨253925, by rfl⟩ : syracuseStep 5417077 = 507851) (by norm_num)
theorem B2140277 : Blo 1425532 2140277 := bbase (se 5 (by rfl) ⟨100325, by rfl⟩ : syracuseStep 2140277 = 200651) (by norm_num)
theorem B2140301 : Blo 1425532 2140301 := bbase (se 3 (by rfl) ⟨401306, by rfl⟩ : syracuseStep 2140301 = 802613) (by norm_num)
theorem B2140325 : Blo 1425532 2140325 := bbase (se 4 (by rfl) ⟨200655, by rfl⟩ : syracuseStep 2140325 = 401311) (by norm_num)
theorem B1804457 : Blo 1425532 1804457 := bbase (se 2 (by rfl) ⟨676671, by rfl⟩ : syracuseStep 1804457 = 1353343) (by norm_num)
theorem B2140349 : Blo 1425532 2140349 := bbase (se 3 (by rfl) ⟨401315, by rfl⟩ : syracuseStep 2140349 = 802631) (by norm_num)
theorem B2140373 : Blo 1425532 2140373 := bbase (se 7 (by rfl) ⟨25082, by rfl⟩ : syracuseStep 2140373 = 50165) (by norm_num)
theorem B13715669 : Blo 1425532 13715669 := bbase (se 7 (by rfl) ⟨160730, by rfl⟩ : syracuseStep 13715669 = 321461) (by norm_num)
theorem B1804513 : Blo 1425532 1804513 := bbase (se 2 (by rfl) ⟨676692, by rfl⟩ : syracuseStep 1804513 = 1353385) (by norm_num)
theorem B4950245 : Blo 1425532 4950245 := bbase (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) (by norm_num)
theorem B2140397 : Blo 1425532 2140397 := bbase (se 3 (by rfl) ⟨401324, by rfl⟩ : syracuseStep 2140397 = 802649) (by norm_num)
theorem B2140421 : Blo 1425532 2140421 := bbase (se 4 (by rfl) ⟨200664, by rfl⟩ : syracuseStep 2140421 = 401329) (by norm_num)
theorem B2140445 : Blo 1425532 2140445 := bbase (se 3 (by rfl) ⟨401333, by rfl⟩ : syracuseStep 2140445 = 802667) (by norm_num)
theorem B1648945 : Blo 1425532 1648945 := bbase (se 2 (by rfl) ⟨618354, by rfl⟩ : syracuseStep 1648945 = 1236709) (by norm_num)
theorem B4630837 : Blo 1425532 4630837 := bbase (se 5 (by rfl) ⟨217070, by rfl⟩ : syracuseStep 4630837 = 434141) (by norm_num)
theorem B2140469 : Blo 1425532 2140469 := bbase (se 5 (by rfl) ⟨100334, by rfl⟩ : syracuseStep 2140469 = 200669) (by norm_num)
theorem B1804609 : Blo 1425532 1804609 := bbase (se 2 (by rfl) ⟨676728, by rfl⟩ : syracuseStep 1804609 = 1353457) (by norm_num)
theorem B1605901 : Blo 1425532 1605901 := bbase (se 3 (by rfl) ⟨301106, by rfl⟩ : syracuseStep 1605901 = 602213) (by norm_num)
theorem B2140493 : Blo 1425532 2140493 := bbase (se 3 (by rfl) ⟨401342, by rfl⟩ : syracuseStep 2140493 = 802685) (by norm_num)
theorem B2140517 : Blo 1425532 2140517 := bbase (se 4 (by rfl) ⟨200673, by rfl⟩ : syracuseStep 2140517 = 401347) (by norm_num)
theorem B2140541 : Blo 1425532 2140541 := bbase (se 3 (by rfl) ⟨401351, by rfl⟩ : syracuseStep 2140541 = 802703) (by norm_num)
theorem B2140565 : Blo 1425532 2140565 := bbase (se 6 (by rfl) ⟨50169, by rfl⟩ : syracuseStep 2140565 = 100339) (by norm_num)
theorem B5417381 : Blo 1425532 5417381 := bbase (se 4 (by rfl) ⟨507879, by rfl⟩ : syracuseStep 5417381 = 1015759) (by norm_num)
theorem B2140589 : Blo 1425532 2140589 := bbase (se 3 (by rfl) ⟨401360, by rfl⟩ : syracuseStep 2140589 = 802721) (by norm_num)
theorem B2140613 : Blo 1425532 2140613 := bbase (se 4 (by rfl) ⟨200682, by rfl⟩ : syracuseStep 2140613 = 401365) (by norm_num)
theorem B2140637 : Blo 1425532 2140637 := bbase (se 3 (by rfl) ⟨401369, by rfl⟩ : syracuseStep 2140637 = 802739) (by norm_num)
theorem B4811237 : Blo 1425532 4811237 := bbase (se 4 (by rfl) ⟨451053, by rfl⟩ : syracuseStep 4811237 = 902107) (by norm_num)
theorem B1804781 : Blo 1425532 1804781 := bbase (se 3 (by rfl) ⟨338396, by rfl⟩ : syracuseStep 1804781 = 676793) (by norm_num)
theorem B2140661 : Blo 1425532 2140661 := bbase (se 5 (by rfl) ⟨100343, by rfl⟩ : syracuseStep 2140661 = 200687) (by norm_num)
theorem B1927685 : Blo 1425532 1927685 := bbase (se 4 (by rfl) ⟨180720, by rfl⟩ : syracuseStep 1927685 = 361441) (by norm_num)
theorem B2140685 : Blo 1425532 2140685 := bbase (se 3 (by rfl) ⟨401378, by rfl⟩ : syracuseStep 2140685 = 802757) (by norm_num)
theorem B1714709 : Blo 1425532 1714709 := bbase (se 6 (by rfl) ⟨40188, by rfl⟩ : syracuseStep 1714709 = 80377) (by norm_num)
theorem B2746909 : Blo 1425532 2746909 := bbase (se 3 (by rfl) ⟨515045, by rfl⟩ : syracuseStep 2746909 = 1030091) (by norm_num)
theorem B1804837 : Blo 1425532 1804837 := bbase (se 4 (by rfl) ⟨169203, by rfl⟩ : syracuseStep 1804837 = 338407) (by norm_num)
theorem B2140709 : Blo 1425532 2140709 := bbase (se 4 (by rfl) ⟨200691, by rfl⟩ : syracuseStep 2140709 = 401383) (by norm_num)
theorem B2140733 : Blo 1425532 2140733 := bbase (se 3 (by rfl) ⟨401387, by rfl⟩ : syracuseStep 2140733 = 802775) (by norm_num)
theorem B6097477 : Blo 1425532 6097477 := bbase (se 4 (by rfl) ⟨571638, by rfl⟩ : syracuseStep 6097477 = 1143277) (by norm_num)
theorem B2140757 : Blo 1425532 2140757 := bbase (se 8 (by rfl) ⟨12543, by rfl⟩ : syracuseStep 2140757 = 25087) (by norm_num)
theorem B6097493 : Blo 1425532 6097493 := bbase (se 8 (by rfl) ⟨35727, by rfl⟩ : syracuseStep 6097493 = 71455) (by norm_num)
theorem B2140781 : Blo 1425532 2140781 := bbase (se 3 (by rfl) ⟨401396, by rfl⟩ : syracuseStep 2140781 = 802793) (by norm_num)
theorem B1804933 : Blo 1425532 1804933 := bbase (se 4 (by rfl) ⟨169212, by rfl⟩ : syracuseStep 1804933 = 338425) (by norm_num)
theorem B2140805 : Blo 1425532 2140805 := bbase (se 4 (by rfl) ⟨200700, by rfl⟩ : syracuseStep 2140805 = 401401) (by norm_num)
theorem B1927837 : Blo 1425532 1927837 := bbase (se 3 (by rfl) ⟨361469, by rfl⟩ : syracuseStep 1927837 = 722939) (by norm_num)
theorem B2140829 : Blo 1425532 2140829 := bbase (se 3 (by rfl) ⟨401405, by rfl⟩ : syracuseStep 2140829 = 802811) (by norm_num)
theorem B2198197 : Blo 1425532 2198197 := bbase (se 5 (by rfl) ⟨103040, by rfl⟩ : syracuseStep 2198197 = 206081) (by norm_num)
theorem B2140853 : Blo 1425532 2140853 := bbase (se 5 (by rfl) ⟨100352, by rfl⟩ : syracuseStep 2140853 = 200705) (by norm_num)
theorem B2140877 : Blo 1425532 2140877 := bbase (se 3 (by rfl) ⟨401414, by rfl⟩ : syracuseStep 2140877 = 802829) (by norm_num)
theorem B2140901 : Blo 1425532 2140901 := bbase (se 4 (by rfl) ⟨200709, by rfl⟩ : syracuseStep 2140901 = 401419) (by norm_num)
theorem B2140925 : Blo 1425532 2140925 := bbase (se 3 (by rfl) ⟨401423, by rfl⟩ : syracuseStep 2140925 = 802847) (by norm_num)
theorem B1927957 : Blo 1425532 1927957 := bbase (se 6 (by rfl) ⟨45186, by rfl⟩ : syracuseStep 1927957 = 90373) (by norm_num)
theorem B2140949 : Blo 1425532 2140949 := bbase (se 6 (by rfl) ⟨50178, by rfl⟩ : syracuseStep 2140949 = 100357) (by norm_num)
theorem B1714969 : Blo 1425532 1714969 := bbase (se 2 (by rfl) ⟨643113, by rfl⟩ : syracuseStep 1714969 = 1286227) (by norm_num)
theorem B2140973 : Blo 1425532 2140973 := bbase (se 3 (by rfl) ⟨401432, by rfl⟩ : syracuseStep 2140973 = 802865) (by norm_num)
theorem B1805105 : Blo 1425532 1805105 := bbase (se 2 (by rfl) ⟨676914, by rfl⟩ : syracuseStep 1805105 = 1353829) (by norm_num)
theorem B2140997 : Blo 1425532 2140997 := bbase (se 4 (by rfl) ⟨200718, by rfl⟩ : syracuseStep 2140997 = 401437) (by norm_num)
theorem B2141021 : Blo 1425532 2141021 := bbase (se 3 (by rfl) ⟨401441, by rfl⟩ : syracuseStep 2141021 = 802883) (by norm_num)
theorem B1805161 : Blo 1425532 1805161 := bbase (se 2 (by rfl) ⟨676935, by rfl⟩ : syracuseStep 1805161 = 1353871) (by norm_num)
theorem B2141045 : Blo 1425532 2141045 := bbase (se 5 (by rfl) ⟨100361, by rfl⟩ : syracuseStep 2141045 = 200723) (by norm_num)
theorem B2141069 : Blo 1425532 2141069 := bbase (se 3 (by rfl) ⟨401450, by rfl⟩ : syracuseStep 2141069 = 802901) (by norm_num)
theorem B4811669 : Blo 1425532 4811669 := bbase (se 6 (by rfl) ⟨112773, by rfl⟩ : syracuseStep 4811669 = 225547) (by norm_num)
theorem B2141093 : Blo 1425532 2141093 := bbase (se 4 (by rfl) ⟨200727, by rfl⟩ : syracuseStep 2141093 = 401455) (by norm_num)
theorem B2141117 : Blo 1425532 2141117 := bbase (se 3 (by rfl) ⟨401459, by rfl⟩ : syracuseStep 2141117 = 802919) (by norm_num)
theorem B1805257 : Blo 1425532 1805257 := bbase (se 2 (by rfl) ⟨676971, by rfl⟩ : syracuseStep 1805257 = 1353943) (by norm_num)
theorem B2141141 : Blo 1425532 2141141 := bbase (se 7 (by rfl) ⟨25091, by rfl⟩ : syracuseStep 2141141 = 50183) (by norm_num)
theorem B2141165 : Blo 1425532 2141165 := bbase (se 3 (by rfl) ⟨401468, by rfl⟩ : syracuseStep 2141165 = 802937) (by norm_num)
theorem B2141189 : Blo 1425532 2141189 := bbase (se 4 (by rfl) ⟨200736, by rfl⟩ : syracuseStep 2141189 = 401473) (by norm_num)
theorem B2141213 : Blo 1425532 2141213 := bbase (se 3 (by rfl) ⟨401477, by rfl⟩ : syracuseStep 2141213 = 802955) (by norm_num)
theorem B2141237 : Blo 1425532 2141237 := bbase (se 5 (by rfl) ⟨100370, by rfl⟩ : syracuseStep 2141237 = 200741) (by norm_num)
theorem B2141261 : Blo 1425532 2141261 := bbase (se 3 (by rfl) ⟨401486, by rfl⟩ : syracuseStep 2141261 = 802973) (by norm_num)
theorem B2141285 : Blo 1425532 2141285 := bbase (se 4 (by rfl) ⟨200745, by rfl⟩ : syracuseStep 2141285 = 401491) (by norm_num)
theorem B1805429 : Blo 1425532 1805429 := bbase (se 5 (by rfl) ⟨84629, by rfl⟩ : syracuseStep 1805429 = 169259) (by norm_num)
theorem B1805485 : Blo 1425532 1805485 := bbase (se 3 (by rfl) ⟨338528, by rfl⟩ : syracuseStep 1805485 = 677057) (by norm_num)
theorem B8129717 : Blo 1425532 8129717 := bbase (se 5 (by rfl) ⟨381080, by rfl⟩ : syracuseStep 8129717 = 762161) (by norm_num)
theorem B3427525 : Blo 1425532 3427525 := bbase (se 4 (by rfl) ⟨321330, by rfl⟩ : syracuseStep 3427525 = 642661) (by norm_num)
theorem B1805581 : Blo 1425532 1805581 := bbase (se 3 (by rfl) ⟨338546, by rfl⟩ : syracuseStep 1805581 = 677093) (by norm_num)
theorem B2706709 : Blo 1425532 2706709 := bbase (se 6 (by rfl) ⟨63438, by rfl⟩ : syracuseStep 2706709 = 126877) (by norm_num)
theorem B7220501 : Blo 1425532 7220501 := bbase (se 6 (by rfl) ⟨169230, by rfl⟩ : syracuseStep 7220501 = 338461) (by norm_num)
theorem B3255589 : Blo 1425532 3255589 := bbase (se 4 (by rfl) ⟨305211, by rfl⟩ : syracuseStep 3255589 = 610423) (by norm_num)
theorem B8121653 : Blo 1425532 8121653 := bbase (se 5 (by rfl) ⟨380702, by rfl⟩ : syracuseStep 8121653 = 761405) (by norm_num)
theorem B4812101 : Blo 1425532 4812101 := bbase (se 4 (by rfl) ⟨451134, by rfl⟩ : syracuseStep 4812101 = 902269) (by norm_num)
theorem B2198869 : Blo 1425532 2198869 := bbase (se 11 (by rfl) ⟨1610, by rfl⟩ : syracuseStep 2198869 = 3221) (by norm_num)
theorem B2706853 : Blo 1425532 2706853 := bbase (se 4 (by rfl) ⟨253767, by rfl⟩ : syracuseStep 2706853 = 507535) (by norm_num)
theorem B1805753 : Blo 1425532 1805753 := bbase (se 2 (by rfl) ⟨677157, by rfl⟩ : syracuseStep 1805753 = 1354315) (by norm_num)
theorem B1805809 : Blo 1425532 1805809 := bbase (se 2 (by rfl) ⟨677178, by rfl⟩ : syracuseStep 1805809 = 1354357) (by norm_num)
theorem B3853813 : Blo 1425532 3853813 := bbase (se 5 (by rfl) ⟨180647, by rfl⟩ : syracuseStep 3853813 = 361295) (by norm_num)
theorem B3427861 : Blo 1425532 3427861 := bbase (se 6 (by rfl) ⟨80340, by rfl⟩ : syracuseStep 3427861 = 160681) (by norm_num)
theorem B2707013 : Blo 1425532 2707013 := bbase (se 4 (by rfl) ⟨253782, by rfl⟩ : syracuseStep 2707013 = 507565) (by norm_num)
theorem B1805905 : Blo 1425532 1805905 := bbase (se 2 (by rfl) ⟨677214, by rfl⟩ : syracuseStep 1805905 = 1354429) (by norm_num)
theorem B1830493 : Blo 1425532 1830493 := bbase (se 3 (by rfl) ⟨343217, by rfl⟩ : syracuseStep 1830493 = 686435) (by norm_num)
theorem B1625737 : Blo 1425532 1625737 := bbase (se 2 (by rfl) ⟨609651, by rfl⟩ : syracuseStep 1625737 = 1219303) (by norm_num)
theorem B6950549 : Blo 1425532 6950549 := bbase (se 6 (by rfl) ⟨162903, by rfl⟩ : syracuseStep 6950549 = 325807) (by norm_num)
theorem B1445533 : Blo 1425532 1445533 := bbase (se 3 (by rfl) ⟨271037, by rfl⟩ : syracuseStep 1445533 = 542075) (by norm_num)
theorem B1445537 : Blo 1425532 1445537 := bbase (se 2 (by rfl) ⟨542076, by rfl⟩ : syracuseStep 1445537 = 1084153) (by norm_num)
theorem B1445569 : Blo 1425532 1445569 := bbase (se 2 (by rfl) ⟨542088, by rfl⟩ : syracuseStep 1445569 = 1084177) (by norm_num)
theorem B2707157 : Blo 1425532 2707157 := bbase (se 7 (by rfl) ⟨31724, by rfl⟩ : syracuseStep 2707157 = 63449) (by norm_num)
theorem B4812533 : Blo 1425532 4812533 := bbase (se 5 (by rfl) ⟨225587, by rfl⟩ : syracuseStep 4812533 = 451175) (by norm_num)
theorem B1806077 : Blo 1425532 1806077 := bbase (se 3 (by rfl) ⟨338639, by rfl⟩ : syracuseStep 1806077 = 677279) (by norm_num)
theorem B4878085 : Blo 1425532 4878085 := bbase (se 4 (by rfl) ⟨457320, by rfl⟩ : syracuseStep 4878085 = 914641) (by norm_num)
theorem B1806133 : Blo 1425532 1806133 := bbase (se 5 (by rfl) ⟨84662, by rfl⟩ : syracuseStep 1806133 = 169325) (by norm_num)
theorem B24358805 : Blo 1425532 24358805 := bbase (se 6 (by rfl) ⟨570909, by rfl⟩ : syracuseStep 24358805 = 1141819) (by norm_num)
theorem B1806229 : Blo 1425532 1806229 := bbase (se 6 (by rfl) ⟨42333, by rfl⟩ : syracuseStep 1806229 = 84667) (by norm_num)
theorem B1445797 : Blo 1425532 1445797 := bbase (se 4 (by rfl) ⟨135543, by rfl⟩ : syracuseStep 1445797 = 271087) (by norm_num)
theorem B3608509 : Blo 1425532 3608509 := bbase (se 3 (by rfl) ⟨676595, by rfl⟩ : syracuseStep 3608509 = 1353191) (by norm_num)
theorem B2707445 : Blo 1425532 2707445 := bbase (se 5 (by rfl) ⟨126911, by rfl⟩ : syracuseStep 2707445 = 253823) (by norm_num)
theorem B16240661 : Blo 1425532 16240661 := bbase (se 6 (by rfl) ⟨380640, by rfl⟩ : syracuseStep 16240661 = 761281) (by norm_num)
theorem B3608621 : Blo 1425532 3608621 := bbase (se 3 (by rfl) ⟨676616, by rfl⟩ : syracuseStep 3608621 = 1353233) (by norm_num)
theorem B1806401 : Blo 1425532 1806401 := bbase (se 2 (by rfl) ⟨677400, by rfl⟩ : syracuseStep 1806401 = 1354801) (by norm_num)
theorem B27775061 : Blo 1425532 27775061 := bbase (se 8 (by rfl) ⟨162744, by rfl⟩ : syracuseStep 27775061 = 325489) (by norm_num)
theorem B13897813 : Blo 1425532 13897813 := bbase (se 8 (by rfl) ⟨81432, by rfl⟩ : syracuseStep 13897813 = 162865) (by norm_num)
theorem B1806457 : Blo 1425532 1806457 := bbase (se 2 (by rfl) ⟨677421, by rfl⟩ : syracuseStep 1806457 = 1354843) (by norm_num)
theorem B3428477 : Blo 1425532 3428477 := bbase (se 3 (by rfl) ⟨642839, by rfl⟩ : syracuseStep 3428477 = 1285679) (by norm_num)
theorem B3657869 : Blo 1425532 3657869 := bbase (se 3 (by rfl) ⟨685850, by rfl⟩ : syracuseStep 3657869 = 1371701) (by norm_num)
theorem B2707597 : Blo 1425532 2707597 := bbase (se 3 (by rfl) ⟨507674, by rfl⟩ : syracuseStep 2707597 = 1015349) (by norm_num)
theorem B15429781 : Blo 1425532 15429781 := bbase (se 6 (by rfl) ⟨361635, by rfl⟩ : syracuseStep 15429781 = 723271) (by norm_num)
theorem B4812965 : Blo 1425532 4812965 := bbase (se 4 (by rfl) ⟨451215, by rfl⟩ : syracuseStep 4812965 = 902431) (by norm_num)
theorem B1806553 : Blo 1425532 1806553 := bbase (se 2 (by rfl) ⟨677457, by rfl⟩ : syracuseStep 1806553 = 1354915) (by norm_num)
theorem B3608813 : Blo 1425532 3608813 := bbase (se 3 (by rfl) ⟨676652, by rfl⟩ : syracuseStep 3608813 = 1353305) (by norm_num)
theorem B3207509 : Blo 1425532 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B12194165 : Blo 1425532 12194165 := bbase (se 5 (by rfl) ⟨571601, by rfl⟩ : syracuseStep 12194165 = 1143203) (by norm_num)
theorem B3207581 : Blo 1425532 3207581 := bbase (se 3 (by rfl) ⟨601421, by rfl⟩ : syracuseStep 3207581 = 1202843) (by norm_num)
theorem B2707901 : Blo 1425532 2707901 := bbase (se 3 (by rfl) ⟨507731, by rfl⟩ : syracuseStep 2707901 = 1015463) (by norm_num)
theorem B3207653 : Blo 1425532 3207653 := bbase (se 4 (by rfl) ⟨300717, by rfl⟩ : syracuseStep 3207653 = 601435) (by norm_num)
theorem B5419493 : Blo 1425532 5419493 := bbase (se 4 (by rfl) ⟨508077, by rfl⟩ : syracuseStep 5419493 = 1016155) (by norm_num)
theorem B7221797 : Blo 1425532 7221797 := bbase (se 4 (by rfl) ⟨677043, by rfl⟩ : syracuseStep 7221797 = 1354087) (by norm_num)
theorem B3207725 : Blo 1425532 3207725 := bbase (se 3 (by rfl) ⟨601448, by rfl⟩ : syracuseStep 3207725 = 1202897) (by norm_num)
theorem B3428909 : Blo 1425532 3428909 := bbase (se 3 (by rfl) ⟨642920, by rfl⟩ : syracuseStep 3428909 = 1285841) (by norm_num)
theorem B3609157 : Blo 1425532 3609157 := bbase (se 4 (by rfl) ⟨338358, by rfl⟩ : syracuseStep 3609157 = 676717) (by norm_num)
theorem B4059733 : Blo 1425532 4059733 := bbase (se 8 (by rfl) ⟨23787, by rfl⟩ : syracuseStep 4059733 = 47575) (by norm_num)
theorem B4813397 : Blo 1425532 4813397 := bbase (se 8 (by rfl) ⟨28203, by rfl⟩ : syracuseStep 4813397 = 56407) (by norm_num)
theorem B3207797 : Blo 1425532 3207797 := bbase (se 5 (by rfl) ⟨150365, by rfl⟩ : syracuseStep 3207797 = 300731) (by norm_num)
theorem B3854981 : Blo 1425532 3854981 := bbase (se 4 (by rfl) ⟨361404, by rfl⟩ : syracuseStep 3854981 = 722809) (by norm_num)
theorem B3609269 : Blo 1425532 3609269 := bbase (se 5 (by rfl) ⟨169184, by rfl⟩ : syracuseStep 3609269 = 338369) (by norm_num)
theorem B1626809 : Blo 1425532 1626809 := bbase (se 2 (by rfl) ⟨610053, by rfl⟩ : syracuseStep 1626809 = 1220107) (by norm_num)
theorem B3207869 : Blo 1425532 3207869 := bbase (se 3 (by rfl) ⟨601475, by rfl⟩ : syracuseStep 3207869 = 1202951) (by norm_num)
theorem B3207941 : Blo 1425532 3207941 := bbase (se 4 (by rfl) ⟨300744, by rfl⟩ : syracuseStep 3207941 = 601489) (by norm_num)
theorem B5419781 : Blo 1425532 5419781 := bbase (se 4 (by rfl) ⟨508104, by rfl⟩ : syracuseStep 5419781 = 1016209) (by norm_num)
theorem B3208013 : Blo 1425532 3208013 := bbase (se 3 (by rfl) ⟨601502, by rfl⟩ : syracuseStep 3208013 = 1203005) (by norm_num)
theorem B3609461 : Blo 1425532 3609461 := bbase (se 5 (by rfl) ⟨169193, by rfl⟩ : syracuseStep 3609461 = 338387) (by norm_num)
theorem B3855221 : Blo 1425532 3855221 := bbase (se 5 (by rfl) ⟨180713, by rfl⟩ : syracuseStep 3855221 = 361427) (by norm_num)
theorem B3208085 : Blo 1425532 3208085 := bbase (se 6 (by rfl) ⟨75189, by rfl⟩ : syracuseStep 3208085 = 150379) (by norm_num)
theorem B6091685 : Blo 1425532 6091685 := bbase (se 4 (by rfl) ⟨571095, by rfl⟩ : syracuseStep 6091685 = 1142191) (by norm_num)
theorem B6173621 : Blo 1425532 6173621 := bbase (se 5 (by rfl) ⟨289388, by rfl⟩ : syracuseStep 6173621 = 578777) (by norm_num)
theorem B1627069 : Blo 1425532 1627069 := bbase (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) (by norm_num)
theorem B4568021 : Blo 1425532 4568021 := bbase (se 7 (by rfl) ⟨53531, by rfl⟩ : syracuseStep 4568021 = 107063) (by norm_num)
theorem B3208157 : Blo 1425532 3208157 := bbase (se 3 (by rfl) ⟨601529, by rfl⟩ : syracuseStep 3208157 = 1203059) (by norm_num)
theorem B4813829 : Blo 1425532 4813829 := bbase (se 4 (by rfl) ⟨451296, by rfl⟩ : syracuseStep 4813829 = 902593) (by norm_num)
theorem B3208229 : Blo 1425532 3208229 := bbase (se 4 (by rfl) ⟨300771, by rfl⟩ : syracuseStep 3208229 = 601543) (by norm_num)
theorem B3208301 : Blo 1425532 3208301 := bbase (se 3 (by rfl) ⟨601556, by rfl⟩ : syracuseStep 3208301 = 1203113) (by norm_num)
theorem B3429533 : Blo 1425532 3429533 := bbase (se 3 (by rfl) ⟨643037, by rfl⟩ : syracuseStep 3429533 = 1286075) (by norm_num)
theorem B2708653 : Blo 1425532 2708653 := bbase (se 3 (by rfl) ⟨507872, by rfl⟩ : syracuseStep 2708653 = 1015745) (by norm_num)
theorem B3208373 : Blo 1425532 3208373 := bbase (se 5 (by rfl) ⟨150392, by rfl⟩ : syracuseStep 3208373 = 300785) (by norm_num)
theorem B1627333 : Blo 1425532 1627333 := bbase (se 4 (by rfl) ⟨152562, by rfl⟩ : syracuseStep 1627333 = 305125) (by norm_num)
theorem B3609805 : Blo 1425532 3609805 := bbase (se 3 (by rfl) ⟨676838, by rfl⟩ : syracuseStep 3609805 = 1353677) (by norm_num)
theorem B2405605 : Blo 1425532 2405605 := bbase (se 4 (by rfl) ⟨225525, by rfl⟩ : syracuseStep 2405605 = 451051) (by norm_num)
theorem B3208445 : Blo 1425532 3208445 := bbase (se 3 (by rfl) ⟨601583, by rfl⟩ : syracuseStep 3208445 = 1203167) (by norm_num)
theorem B2405693 : Blo 1425532 2405693 := bbase (se 3 (by rfl) ⟨451067, by rfl⟩ : syracuseStep 2405693 = 902135) (by norm_num)
theorem B3609917 : Blo 1425532 3609917 := bbase (se 3 (by rfl) ⟨676859, by rfl⟩ : syracuseStep 3609917 = 1353719) (by norm_num)
theorem B2708797 : Blo 1425532 2708797 := bbase (se 3 (by rfl) ⟨507899, by rfl⟩ : syracuseStep 2708797 = 1015799) (by norm_num)
theorem B3208517 : Blo 1425532 3208517 := bbase (se 4 (by rfl) ⟨300798, by rfl⟩ : syracuseStep 3208517 = 601597) (by norm_num)
theorem B1627489 : Blo 1425532 1627489 := bbase (se 2 (by rfl) ⟨610308, by rfl⟩ : syracuseStep 1627489 = 1220617) (by norm_num)
theorem B3044749 : Blo 1425532 3044749 := bbase (se 3 (by rfl) ⟨570890, by rfl⟩ : syracuseStep 3044749 = 1141781) (by norm_num)
theorem B3208589 : Blo 1425532 3208589 := bbase (se 3 (by rfl) ⟨601610, by rfl⟩ : syracuseStep 3208589 = 1203221) (by norm_num)
theorem B4814261 : Blo 1425532 4814261 := bbase (se 5 (by rfl) ⟨225668, by rfl⟩ : syracuseStep 4814261 = 451337) (by norm_num)
theorem B2405821 : Blo 1425532 2405821 := bbase (se 3 (by rfl) ⟨451091, by rfl⟩ : syracuseStep 2405821 = 902183) (by norm_num)
theorem B3208661 : Blo 1425532 3208661 := bbase (se 7 (by rfl) ⟨37601, by rfl⟩ : syracuseStep 3208661 = 75203) (by norm_num)
theorem B2708957 : Blo 1425532 2708957 := bbase (se 3 (by rfl) ⟨507929, by rfl⟩ : syracuseStep 2708957 = 1015859) (by norm_num)
theorem B1627625 : Blo 1425532 1627625 := bbase (se 2 (by rfl) ⟨610359, by rfl⟩ : syracuseStep 1627625 = 1220719) (by norm_num)
theorem B3659261 : Blo 1425532 3659261 := bbase (se 3 (by rfl) ⟨686111, by rfl⟩ : syracuseStep 3659261 = 1372223) (by norm_num)
theorem B3610109 : Blo 1425532 3610109 := bbase (se 3 (by rfl) ⟨676895, by rfl⟩ : syracuseStep 3610109 = 1353791) (by norm_num)
theorem B2405909 : Blo 1425532 2405909 := bbase (se 6 (by rfl) ⟨56388, by rfl⟩ : syracuseStep 2405909 = 112777) (by norm_num)
theorem B3208733 : Blo 1425532 3208733 := bbase (se 3 (by rfl) ⟨601637, by rfl⟩ : syracuseStep 3208733 = 1203275) (by norm_num)
theorem B3208805 : Blo 1425532 3208805 := bbase (se 4 (by rfl) ⟨300825, by rfl⟩ : syracuseStep 3208805 = 601651) (by norm_num)
theorem B2709101 : Blo 1425532 2709101 := bbase (se 3 (by rfl) ⟨507956, by rfl⟩ : syracuseStep 2709101 = 1015913) (by norm_num)
theorem B2406037 : Blo 1425532 2406037 := bbase (se 6 (by rfl) ⟨56391, by rfl⟩ : syracuseStep 2406037 = 112783) (by norm_num)
theorem B3208877 : Blo 1425532 3208877 := bbase (se 3 (by rfl) ⟨601664, by rfl⟩ : syracuseStep 3208877 = 1203329) (by norm_num)
theorem B2406125 : Blo 1425532 2406125 := bbase (se 3 (by rfl) ⟨451148, by rfl⟩ : syracuseStep 2406125 = 902297) (by norm_num)
theorem B3659501 : Blo 1425532 3659501 := bbase (se 3 (by rfl) ⟨686156, by rfl⟩ : syracuseStep 3659501 = 1372313) (by norm_num)
theorem B2569973 : Blo 1425532 2569973 := bbase (se 5 (by rfl) ⟨120467, by rfl⟩ : syracuseStep 2569973 = 240935) (by norm_num)
theorem B3208949 : Blo 1425532 3208949 := bbase (se 5 (by rfl) ⟨150419, by rfl⟩ : syracuseStep 3208949 = 300839) (by norm_num)
theorem B6854453 : Blo 1425532 6854453 := bbase (se 5 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 6854453 = 642605) (by norm_num)
theorem B7223093 : Blo 1425532 7223093 := bbase (se 5 (by rfl) ⟨338582, by rfl⟩ : syracuseStep 7223093 = 677165) (by norm_num)
theorem B3209021 : Blo 1425532 3209021 := bbase (se 3 (by rfl) ⟨601691, by rfl⟩ : syracuseStep 3209021 = 1203383) (by norm_num)
theorem B3610453 : Blo 1425532 3610453 := bbase (se 9 (by rfl) ⟨10577, by rfl⟩ : syracuseStep 3610453 = 21155) (by norm_num)
theorem B4814693 : Blo 1425532 4814693 := bbase (se 4 (by rfl) ⟨451377, by rfl⟩ : syracuseStep 4814693 = 902755) (by norm_num)
theorem B2406253 : Blo 1425532 2406253 := bbase (se 3 (by rfl) ⟨451172, by rfl⟩ : syracuseStep 2406253 = 902345) (by norm_num)
theorem B3209093 : Blo 1425532 3209093 := bbase (se 4 (by rfl) ⟨300852, by rfl⟩ : syracuseStep 3209093 = 601705) (by norm_num)
theorem B2709389 : Blo 1425532 2709389 := bbase (se 3 (by rfl) ⟨508010, by rfl⟩ : syracuseStep 2709389 = 1016021) (by norm_num)
theorem B2406341 : Blo 1425532 2406341 := bbase (se 4 (by rfl) ⟨225594, by rfl⟩ : syracuseStep 2406341 = 451189) (by norm_num)
theorem B3610565 : Blo 1425532 3610565 := bbase (se 4 (by rfl) ⟨338490, by rfl⟩ : syracuseStep 3610565 = 676981) (by norm_num)
theorem B3209165 : Blo 1425532 3209165 := bbase (se 3 (by rfl) ⟨601718, by rfl⟩ : syracuseStep 3209165 = 1203437) (by norm_num)
theorem B3209237 : Blo 1425532 3209237 := bbase (se 6 (by rfl) ⟨75216, by rfl⟩ : syracuseStep 3209237 = 150433) (by norm_num)
theorem B2709541 : Blo 1425532 2709541 := bbase (se 4 (by rfl) ⟨254019, by rfl⟩ : syracuseStep 2709541 = 508039) (by norm_num)
theorem B2439229 : Blo 1425532 2439229 := bbase (se 3 (by rfl) ⟨457355, by rfl⟩ : syracuseStep 2439229 = 914711) (by norm_num)
theorem B2406469 : Blo 1425532 2406469 := bbase (se 4 (by rfl) ⟨225606, by rfl⟩ : syracuseStep 2406469 = 451213) (by norm_num)
theorem B3209309 : Blo 1425532 3209309 := bbase (se 3 (by rfl) ⟨601745, by rfl⟩ : syracuseStep 3209309 = 1203491) (by norm_num)
theorem B5142629 : Blo 1425532 5142629 := bbase (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) (by norm_num)
theorem B3610757 : Blo 1425532 3610757 := bbase (se 4 (by rfl) ⟨338508, by rfl⟩ : syracuseStep 3610757 = 677017) (by norm_num)
theorem B17356949 : Blo 1425532 17356949 := bbase (se 6 (by rfl) ⟨406803, by rfl⟩ : syracuseStep 17356949 = 813607) (by norm_num)
theorem B1603741 : Blo 1425532 1603741 := bbase (se 3 (by rfl) ⟨300701, by rfl⟩ : syracuseStep 1603741 = 601403) (by norm_num)
theorem B2406557 : Blo 1425532 2406557 := bbase (se 3 (by rfl) ⟨451229, by rfl⟩ : syracuseStep 2406557 = 902459) (by norm_num)
theorem B3209381 : Blo 1425532 3209381 := bbase (se 4 (by rfl) ⟨300879, by rfl⟩ : syracuseStep 3209381 = 601759) (by norm_num)
theorem B1603777 : Blo 1425532 1603777 := bbase (se 2 (by rfl) ⟨601416, by rfl⟩ : syracuseStep 1603777 = 1202833) (by norm_num)
theorem B1603813 : Blo 1425532 1603813 := bbase (se 4 (by rfl) ⟨150357, by rfl⟩ : syracuseStep 1603813 = 300715) (by norm_num)
theorem B3209453 : Blo 1425532 3209453 := bbase (se 3 (by rfl) ⟨601772, by rfl⟩ : syracuseStep 3209453 = 1203545) (by norm_num)
theorem B11565301 : Blo 1425532 11565301 := bbase (se 5 (by rfl) ⟨542123, by rfl⟩ : syracuseStep 11565301 = 1084247) (by norm_num)
theorem B3045637 : Blo 1425532 3045637 := bbase (se 4 (by rfl) ⟨285528, by rfl⟩ : syracuseStep 3045637 = 571057) (by norm_num)
theorem B1603849 : Blo 1425532 1603849 := bbase (se 2 (by rfl) ⟨601443, by rfl⟩ : syracuseStep 1603849 = 1202887) (by norm_num)
theorem B4815125 : Blo 1425532 4815125 := bbase (se 6 (by rfl) ⟨112854, by rfl⟩ : syracuseStep 4815125 = 225709) (by norm_num)
theorem B2283805 : Blo 1425532 2283805 := bbase (se 3 (by rfl) ⟨428213, by rfl⟩ : syracuseStep 2283805 = 856427) (by norm_num)
theorem B2406685 : Blo 1425532 2406685 := bbase (se 3 (by rfl) ⟨451253, by rfl⟩ : syracuseStep 2406685 = 902507) (by norm_num)
theorem B1603885 : Blo 1425532 1603885 := bbase (se 3 (by rfl) ⟨300728, by rfl⟩ : syracuseStep 1603885 = 601457) (by norm_num)
theorem B3209525 : Blo 1425532 3209525 := bbase (se 5 (by rfl) ⟨150446, by rfl⟩ : syracuseStep 3209525 = 300893) (by norm_num)
theorem B5413189 : Blo 1425532 5413189 := bbase (se 4 (by rfl) ⟨507486, by rfl⟩ : syracuseStep 5413189 = 1014973) (by norm_num)
theorem B1603921 : Blo 1425532 1603921 := bbase (se 2 (by rfl) ⟨601470, by rfl⟩ : syracuseStep 1603921 = 1202941) (by norm_num)
theorem B2709845 : Blo 1425532 2709845 := bbase (se 10 (by rfl) ⟨3969, by rfl⟩ : syracuseStep 2709845 = 7939) (by norm_num)
theorem B6256997 : Blo 1425532 6256997 := bbase (se 4 (by rfl) ⟨586593, by rfl⟩ : syracuseStep 6256997 = 1173187) (by norm_num)
theorem B1603957 : Blo 1425532 1603957 := bbase (se 5 (by rfl) ⟨75185, by rfl⟩ : syracuseStep 1603957 = 150371) (by norm_num)
theorem B2406773 : Blo 1425532 2406773 := bbase (se 5 (by rfl) ⟨112817, by rfl⟩ : syracuseStep 2406773 = 225635) (by norm_num)
theorem B2169205 : Blo 1425532 2169205 := bbase (se 5 (by rfl) ⟨101681, by rfl⟩ : syracuseStep 2169205 = 203363) (by norm_num)
theorem B10836341 : Blo 1425532 10836341 := bbase (se 5 (by rfl) ⟨507953, by rfl⟩ : syracuseStep 10836341 = 1015907) (by norm_num)
theorem B3045757 : Blo 1425532 3045757 := bbase (se 3 (by rfl) ⟨571079, by rfl⟩ : syracuseStep 3045757 = 1142159) (by norm_num)
theorem B3209597 : Blo 1425532 3209597 := bbase (se 3 (by rfl) ⟨601799, by rfl⟩ : syracuseStep 3209597 = 1203599) (by norm_num)
theorem B1603993 : Blo 1425532 1603993 := bbase (se 2 (by rfl) ⟨601497, by rfl⟩ : syracuseStep 1603993 = 1202995) (by norm_num)
theorem B1604029 : Blo 1425532 1604029 := bbase (se 3 (by rfl) ⟨300755, by rfl⟩ : syracuseStep 1604029 = 601511) (by norm_num)
theorem B3209669 : Blo 1425532 3209669 := bbase (se 4 (by rfl) ⟨300906, by rfl⟩ : syracuseStep 3209669 = 601813) (by norm_num)
theorem B3611101 : Blo 1425532 3611101 := bbase (se 3 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 3611101 = 1354163) (by norm_num)
theorem B1604065 : Blo 1425532 1604065 := bbase (se 2 (by rfl) ⟨601524, by rfl⟩ : syracuseStep 1604065 = 1203049) (by norm_num)
theorem B2406901 : Blo 1425532 2406901 := bbase (se 5 (by rfl) ⟨112823, by rfl⟩ : syracuseStep 2406901 = 225647) (by norm_num)
theorem B1604101 : Blo 1425532 1604101 := bbase (se 4 (by rfl) ⟨150384, by rfl⟩ : syracuseStep 1604101 = 300769) (by norm_num)
theorem B3389957 : Blo 1425532 3389957 := bbase (se 4 (by rfl) ⟨317808, by rfl⟩ : syracuseStep 3389957 = 635617) (by norm_num)
theorem B3209741 : Blo 1425532 3209741 := bbase (se 3 (by rfl) ⟨601826, by rfl⟩ : syracuseStep 3209741 = 1203653) (by norm_num)
theorem B21142037 : Blo 1425532 21142037 := bbase (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) (by norm_num)
theorem B1604137 : Blo 1425532 1604137 := bbase (se 2 (by rfl) ⟨601551, by rfl⟩ : syracuseStep 1604137 = 1203103) (by norm_num)
theorem B1604173 : Blo 1425532 1604173 := bbase (se 3 (by rfl) ⟨300782, by rfl⟩ : syracuseStep 1604173 = 601565) (by norm_num)
theorem B2406989 : Blo 1425532 2406989 := bbase (se 3 (by rfl) ⟨451310, by rfl⟩ : syracuseStep 2406989 = 902621) (by norm_num)
theorem B3611213 : Blo 1425532 3611213 := bbase (se 3 (by rfl) ⟨677102, by rfl⟩ : syracuseStep 3611213 = 1354205) (by norm_num)
theorem B3209813 : Blo 1425532 3209813 := bbase (se 8 (by rfl) ⟨18807, by rfl⟩ : syracuseStep 3209813 = 37615) (by norm_num)
theorem B1604209 : Blo 1425532 1604209 := bbase (se 2 (by rfl) ⟨601578, by rfl⟩ : syracuseStep 1604209 = 1203157) (by norm_num)
theorem B5413493 : Blo 1425532 5413493 := bbase (se 5 (by rfl) ⟨253757, by rfl⟩ : syracuseStep 5413493 = 507515) (by norm_num)
theorem B2030197 : Blo 1425532 2030197 := bbase (se 5 (by rfl) ⟨95165, by rfl⟩ : syracuseStep 2030197 = 190331) (by norm_num)
theorem B3046013 : Blo 1425532 3046013 := bbase (se 3 (by rfl) ⟨571127, by rfl⟩ : syracuseStep 3046013 = 1142255) (by norm_num)
theorem B1604245 : Blo 1425532 1604245 := bbase (se 6 (by rfl) ⟨37599, by rfl⟩ : syracuseStep 1604245 = 75199) (by norm_num)
theorem B6093461 : Blo 1425532 6093461 := bbase (se 6 (by rfl) ⟨142815, by rfl⟩ : syracuseStep 6093461 = 285631) (by norm_num)
theorem B3209885 : Blo 1425532 3209885 := bbase (se 3 (by rfl) ⟨601853, by rfl⟩ : syracuseStep 3209885 = 1203707) (by norm_num)
theorem B1522357 : Blo 1425532 1522357 := bbase (se 5 (by rfl) ⟨71360, by rfl⟩ : syracuseStep 1522357 = 142721) (by norm_num)
theorem B2570933 : Blo 1425532 2570933 := bbase (se 5 (by rfl) ⟨120512, by rfl⟩ : syracuseStep 2570933 = 241025) (by norm_num)
theorem B1604281 : Blo 1425532 1604281 := bbase (se 2 (by rfl) ⟨601605, by rfl⟩ : syracuseStep 1604281 = 1203211) (by norm_num)
theorem B4815557 : Blo 1425532 4815557 := bbase (se 4 (by rfl) ⟨451458, by rfl⟩ : syracuseStep 4815557 = 902917) (by norm_num)
theorem B2407117 : Blo 1425532 2407117 := bbase (se 3 (by rfl) ⟨451334, by rfl⟩ : syracuseStep 2407117 = 902669) (by norm_num)
theorem B1604317 : Blo 1425532 1604317 := bbase (se 3 (by rfl) ⟨300809, by rfl⟩ : syracuseStep 1604317 = 601619) (by norm_num)
theorem B3209957 : Blo 1425532 3209957 := bbase (se 4 (by rfl) ⟨300933, by rfl⟩ : syracuseStep 3209957 = 601867) (by norm_num)
theorem B1604353 : Blo 1425532 1604353 := bbase (se 2 (by rfl) ⟨601632, by rfl⟩ : syracuseStep 1604353 = 1203265) (by norm_num)
theorem B3611405 : Blo 1425532 3611405 := bbase (se 3 (by rfl) ⟨677138, by rfl⟩ : syracuseStep 3611405 = 1354277) (by norm_num)
theorem B10828565 : Blo 1425532 10828565 := bbase (se 6 (by rfl) ⟨253794, by rfl⟩ : syracuseStep 10828565 = 507589) (by norm_num)
theorem B1604389 : Blo 1425532 1604389 := bbase (se 4 (by rfl) ⟨150411, by rfl⟩ : syracuseStep 1604389 = 300823) (by norm_num)
theorem B2407205 : Blo 1425532 2407205 := bbase (se 4 (by rfl) ⟨225675, by rfl⟩ : syracuseStep 2407205 = 451351) (by norm_num)
theorem B1522477 : Blo 1425532 1522477 := bbase (se 3 (by rfl) ⟨285464, by rfl⟩ : syracuseStep 1522477 = 570929) (by norm_num)
theorem B3210029 : Blo 1425532 3210029 := bbase (se 3 (by rfl) ⟨601880, by rfl⟩ : syracuseStep 3210029 = 1203761) (by norm_num)
theorem B1604425 : Blo 1425532 1604425 := bbase (se 2 (by rfl) ⟨601659, by rfl⟩ : syracuseStep 1604425 = 1203319) (by norm_num)
theorem B1604461 : Blo 1425532 1604461 := bbase (se 3 (by rfl) ⟨300836, by rfl⟩ : syracuseStep 1604461 = 601673) (by norm_num)
theorem B3210101 : Blo 1425532 3210101 := bbase (se 5 (by rfl) ⟨150473, by rfl⟩ : syracuseStep 3210101 = 300947) (by norm_num)
theorem B6093701 : Blo 1425532 6093701 := bbase (se 4 (by rfl) ⟨571284, by rfl⟩ : syracuseStep 6093701 = 1142569) (by norm_num)
theorem B1604497 : Blo 1425532 1604497 := bbase (se 2 (by rfl) ⟨601686, by rfl⟩ : syracuseStep 1604497 = 1203373) (by norm_num)
theorem B2284453 : Blo 1425532 2284453 := bbase (se 4 (by rfl) ⟨214167, by rfl⟩ : syracuseStep 2284453 = 428335) (by norm_num)
theorem B2407333 : Blo 1425532 2407333 := bbase (se 4 (by rfl) ⟨225687, by rfl⟩ : syracuseStep 2407333 = 451375) (by norm_num)
theorem B8231861 : Blo 1425532 8231861 := bbase (se 5 (by rfl) ⟨385868, by rfl⟩ : syracuseStep 8231861 = 771737) (by norm_num)
theorem B1604533 : Blo 1425532 1604533 := bbase (se 5 (by rfl) ⟨75212, by rfl⟩ : syracuseStep 1604533 = 150425) (by norm_num)
theorem B3210173 : Blo 1425532 3210173 := bbase (se 3 (by rfl) ⟨601907, by rfl⟩ : syracuseStep 3210173 = 1203815) (by norm_num)
theorem B1604569 : Blo 1425532 1604569 := bbase (se 2 (by rfl) ⟨601713, by rfl⟩ : syracuseStep 1604569 = 1203427) (by norm_num)
theorem B12352501 : Blo 1425532 12352501 := bbase (se 5 (by rfl) ⟨579023, by rfl⟩ : syracuseStep 12352501 = 1158047) (by norm_num)
theorem B1604605 : Blo 1425532 1604605 := bbase (se 3 (by rfl) ⟨300863, by rfl⟩ : syracuseStep 1604605 = 601727) (by norm_num)
theorem B2407421 : Blo 1425532 2407421 := bbase (se 3 (by rfl) ⟨451391, by rfl⟩ : syracuseStep 2407421 = 902783) (by norm_num)
theorem B3210245 : Blo 1425532 3210245 := bbase (se 4 (by rfl) ⟨300960, by rfl⟩ : syracuseStep 3210245 = 601921) (by norm_num)
theorem B1604641 : Blo 1425532 1604641 := bbase (se 2 (by rfl) ⟨601740, by rfl⟩ : syracuseStep 1604641 = 1203481) (by norm_num)
theorem B1522729 : Blo 1425532 1522729 := bbase (se 2 (by rfl) ⟨571023, by rfl⟩ : syracuseStep 1522729 = 1142047) (by norm_num)
theorem B1522733 : Blo 1425532 1522733 := bbase (se 3 (by rfl) ⟨285512, by rfl⟩ : syracuseStep 1522733 = 571025) (by norm_num)
theorem B1604677 : Blo 1425532 1604677 := bbase (se 4 (by rfl) ⟨150438, by rfl⟩ : syracuseStep 1604677 = 300877) (by norm_num)
theorem B7224389 : Blo 1425532 7224389 := bbase (se 4 (by rfl) ⟨677286, by rfl⟩ : syracuseStep 7224389 = 1354573) (by norm_num)
theorem B3210317 : Blo 1425532 3210317 := bbase (se 3 (by rfl) ⟨601934, by rfl⟩ : syracuseStep 3210317 = 1203869) (by norm_num)
theorem B5143637 : Blo 1425532 5143637 := bbase (se 8 (by rfl) ⟨30138, by rfl⟩ : syracuseStep 5143637 = 60277) (by norm_num)
theorem B3611749 : Blo 1425532 3611749 := bbase (se 4 (by rfl) ⟨338601, by rfl⟩ : syracuseStep 3611749 = 677203) (by norm_num)
theorem B1604713 : Blo 1425532 1604713 := bbase (se 2 (by rfl) ⟨601767, by rfl⟩ : syracuseStep 1604713 = 1203535) (by norm_num)
theorem B4815989 : Blo 1425532 4815989 := bbase (se 5 (by rfl) ⟨225749, by rfl⟩ : syracuseStep 4815989 = 451499) (by norm_num)
theorem B2407549 : Blo 1425532 2407549 := bbase (se 3 (by rfl) ⟨451415, by rfl⟩ : syracuseStep 2407549 = 902831) (by norm_num)
theorem B1604749 : Blo 1425532 1604749 := bbase (se 3 (by rfl) ⟨300890, by rfl⟩ : syracuseStep 1604749 = 601781) (by norm_num)
theorem B3210389 : Blo 1425532 3210389 := bbase (se 6 (by rfl) ⟨75243, by rfl⟩ : syracuseStep 3210389 = 150487) (by norm_num)
theorem B2604197 : Blo 1425532 2604197 := bbase (se 4 (by rfl) ⟨244143, by rfl⟩ : syracuseStep 2604197 = 488287) (by norm_num)
theorem B1604785 : Blo 1425532 1604785 := bbase (se 2 (by rfl) ⟨601794, by rfl⟩ : syracuseStep 1604785 = 1203589) (by norm_num)
theorem B2030789 : Blo 1425532 2030789 := bbase (se 4 (by rfl) ⟨190386, by rfl⟩ : syracuseStep 2030789 = 380773) (by norm_num)
theorem B1604821 : Blo 1425532 1604821 := bbase (se 7 (by rfl) ⟨18806, by rfl⟩ : syracuseStep 1604821 = 37613) (by norm_num)
theorem B2407637 : Blo 1425532 2407637 := bbase (se 7 (by rfl) ⟨28214, by rfl⟩ : syracuseStep 2407637 = 56429) (by norm_num)
theorem B3611861 : Blo 1425532 3611861 := bbase (se 7 (by rfl) ⟨42326, by rfl⟩ : syracuseStep 3611861 = 84653) (by norm_num)
theorem B3210461 : Blo 1425532 3210461 := bbase (se 3 (by rfl) ⟨601961, by rfl⟩ : syracuseStep 3210461 = 1203923) (by norm_num)
theorem B2604277 : Blo 1425532 2604277 := bbase (se 5 (by rfl) ⟨122075, by rfl⟩ : syracuseStep 2604277 = 244151) (by norm_num)
theorem B1604857 : Blo 1425532 1604857 := bbase (se 2 (by rfl) ⟨601821, by rfl⟩ : syracuseStep 1604857 = 1203643) (by norm_num)
theorem B2030869 : Blo 1425532 2030869 := bbase (se 6 (by rfl) ⟨47598, by rfl⟩ : syracuseStep 2030869 = 95197) (by norm_num)
theorem B1604893 : Blo 1425532 1604893 := bbase (se 3 (by rfl) ⟨300917, by rfl⟩ : syracuseStep 1604893 = 601835) (by norm_num)
theorem B3210533 : Blo 1425532 3210533 := bbase (se 4 (by rfl) ⟨300987, by rfl⟩ : syracuseStep 3210533 = 601975) (by norm_num)
theorem B1604929 : Blo 1425532 1604929 := bbase (se 2 (by rfl) ⟨601848, by rfl⟩ : syracuseStep 1604929 = 1203697) (by norm_num)
theorem B2407765 : Blo 1425532 2407765 := bbase (se 11 (by rfl) ⟨1763, by rfl⟩ : syracuseStep 2407765 = 3527) (by norm_num)
theorem B1604965 : Blo 1425532 1604965 := bbase (se 4 (by rfl) ⟨150465, by rfl⟩ : syracuseStep 1604965 = 300931) (by norm_num)
theorem B3210605 : Blo 1425532 3210605 := bbase (se 3 (by rfl) ⟨601988, by rfl⟩ : syracuseStep 3210605 = 1203977) (by norm_num)
theorem B4062581 : Blo 1425532 4062581 := bbase (se 5 (by rfl) ⟨190433, by rfl⟩ : syracuseStep 4062581 = 380867) (by norm_num)
theorem B1605001 : Blo 1425532 1605001 := bbase (se 2 (by rfl) ⟨601875, by rfl⟩ : syracuseStep 1605001 = 1203751) (by norm_num)
theorem B2030989 : Blo 1425532 2030989 := bbase (se 3 (by rfl) ⟨380810, by rfl⟩ : syracuseStep 2030989 = 761621) (by norm_num)
theorem B3612053 : Blo 1425532 3612053 := bbase (se 6 (by rfl) ⟨84657, by rfl⟩ : syracuseStep 3612053 = 169315) (by norm_num)
theorem B1605037 : Blo 1425532 1605037 := bbase (se 3 (by rfl) ⟨300944, by rfl⟩ : syracuseStep 1605037 = 601889) (by norm_num)
theorem B2407853 : Blo 1425532 2407853 := bbase (se 3 (by rfl) ⟨451472, by rfl⟩ : syracuseStep 2407853 = 902945) (by norm_num)
theorem B3210677 : Blo 1425532 3210677 := bbase (se 5 (by rfl) ⟨150500, by rfl⟩ : syracuseStep 3210677 = 301001) (by norm_num)
theorem B1605073 : Blo 1425532 1605073 := bbase (se 2 (by rfl) ⟨601902, by rfl⟩ : syracuseStep 1605073 = 1203805) (by norm_num)
theorem B2031085 : Blo 1425532 2031085 := bbase (se 3 (by rfl) ⟨380828, by rfl⟩ : syracuseStep 2031085 = 761657) (by norm_num)
theorem B3046901 : Blo 1425532 3046901 := bbase (se 5 (by rfl) ⟨142823, by rfl⟩ : syracuseStep 3046901 = 285647) (by norm_num)
theorem B1605109 : Blo 1425532 1605109 := bbase (se 5 (by rfl) ⟨75239, by rfl⟩ : syracuseStep 1605109 = 150479) (by norm_num)
theorem B3210749 : Blo 1425532 3210749 := bbase (se 3 (by rfl) ⟨602015, by rfl⟩ : syracuseStep 3210749 = 1204031) (by norm_num)
theorem B9141781 : Blo 1425532 9141781 := bbase (se 6 (by rfl) ⟨214260, by rfl⟩ : syracuseStep 9141781 = 428521) (by norm_num)
theorem B1605145 : Blo 1425532 1605145 := bbase (se 2 (by rfl) ⟨601929, by rfl⟩ : syracuseStep 1605145 = 1203859) (by norm_num)
theorem B4816421 : Blo 1425532 4816421 := bbase (se 4 (by rfl) ⟨451539, by rfl⟩ : syracuseStep 4816421 = 903079) (by norm_num)
theorem B2407981 : Blo 1425532 2407981 := bbase (se 3 (by rfl) ⟨451496, by rfl⟩ : syracuseStep 2407981 = 902993) (by norm_num)
theorem B3661357 : Blo 1425532 3661357 := bbase (se 3 (by rfl) ⟨686504, by rfl⟩ : syracuseStep 3661357 = 1373009) (by norm_num)
theorem B1605181 : Blo 1425532 1605181 := bbase (se 3 (by rfl) ⟨300971, by rfl⟩ : syracuseStep 1605181 = 601943) (by norm_num)
theorem B3210821 : Blo 1425532 3210821 := bbase (se 4 (by rfl) ⟨301014, by rfl⟩ : syracuseStep 3210821 = 602029) (by norm_num)
theorem B3857989 : Blo 1425532 3857989 := bbase (se 4 (by rfl) ⟨361686, by rfl⟩ : syracuseStep 3857989 = 723373) (by norm_num)
theorem B27401813 : Blo 1425532 27401813 := bbase (se 8 (by rfl) ⟨160557, by rfl⟩ : syracuseStep 27401813 = 321115) (by norm_num)
theorem B1523297 : Blo 1425532 1523297 := bbase (se 2 (by rfl) ⟨571236, by rfl⟩ : syracuseStep 1523297 = 1142473) (by norm_num)
theorem B1605217 : Blo 1425532 1605217 := bbase (se 2 (by rfl) ⟨601956, by rfl⟩ : syracuseStep 1605217 = 1203913) (by norm_num)
theorem B1605253 : Blo 1425532 1605253 := bbase (se 4 (by rfl) ⟨150492, by rfl⟩ : syracuseStep 1605253 = 300985) (by norm_num)
theorem B2408069 : Blo 1425532 2408069 := bbase (se 4 (by rfl) ⟨225756, by rfl⟩ : syracuseStep 2408069 = 451513) (by norm_num)
theorem B3210893 : Blo 1425532 3210893 := bbase (se 3 (by rfl) ⟨602042, by rfl⟩ : syracuseStep 3210893 = 1204085) (by norm_num)
theorem B4570789 : Blo 1425532 4570789 := bbase (se 4 (by rfl) ⟨428511, by rfl⟩ : syracuseStep 4570789 = 857023) (by norm_num)
theorem B1605289 : Blo 1425532 1605289 := bbase (se 2 (by rfl) ⟨601983, by rfl⟩ : syracuseStep 1605289 = 1203967) (by norm_num)
theorem B1605325 : Blo 1425532 1605325 := bbase (se 3 (by rfl) ⟨300998, by rfl⟩ : syracuseStep 1605325 = 601997) (by norm_num)
theorem B3210965 : Blo 1425532 3210965 := bbase (se 7 (by rfl) ⟨37628, by rfl⟩ : syracuseStep 3210965 = 75257) (by norm_num)
theorem B3047141 : Blo 1425532 3047141 := bbase (se 4 (by rfl) ⟨285669, by rfl⟩ : syracuseStep 3047141 = 571339) (by norm_num)
theorem B3612397 : Blo 1425532 3612397 := bbase (se 3 (by rfl) ⟨677324, by rfl⟩ : syracuseStep 3612397 = 1354649) (by norm_num)
theorem B1605361 : Blo 1425532 1605361 := bbase (se 2 (by rfl) ⟨602010, by rfl⟩ : syracuseStep 1605361 = 1204021) (by norm_num)
theorem B2408197 : Blo 1425532 2408197 := bbase (se 4 (by rfl) ⟨225768, by rfl⟩ : syracuseStep 2408197 = 451537) (by norm_num)
theorem B1605397 : Blo 1425532 1605397 := bbase (se 6 (by rfl) ⟨37626, by rfl⟩ : syracuseStep 1605397 = 75253) (by norm_num)
theorem B1523485 : Blo 1425532 1523485 := bbase (se 3 (by rfl) ⟨285653, by rfl⟩ : syracuseStep 1523485 = 571307) (by norm_num)
theorem B3211037 : Blo 1425532 3211037 := bbase (se 3 (by rfl) ⟨602069, by rfl⟩ : syracuseStep 3211037 = 1204139) (by norm_num)
theorem B1605433 : Blo 1425532 1605433 := bbase (se 2 (by rfl) ⟨602037, by rfl⟩ : syracuseStep 1605433 = 1204075) (by norm_num)
theorem B2285381 : Blo 1425532 2285381 := bbase (se 4 (by rfl) ⟨214254, by rfl⟩ : syracuseStep 2285381 = 428509) (by norm_num)
theorem B1605469 : Blo 1425532 1605469 := bbase (se 3 (by rfl) ⟨301025, by rfl⟩ : syracuseStep 1605469 = 602051) (by norm_num)
theorem B2408285 : Blo 1425532 2408285 := bbase (se 3 (by rfl) ⟨451553, by rfl⟩ : syracuseStep 2408285 = 903107) (by norm_num)
theorem B3612509 : Blo 1425532 3612509 := bbase (se 3 (by rfl) ⟨677345, by rfl⟩ : syracuseStep 3612509 = 1354691) (by norm_num)
theorem B3211109 : Blo 1425532 3211109 := bbase (se 4 (by rfl) ⟨301041, by rfl⟩ : syracuseStep 3211109 = 602083) (by norm_num)
theorem B1605505 : Blo 1425532 1605505 := bbase (se 2 (by rfl) ⟨602064, by rfl⟩ : syracuseStep 1605505 = 1204129) (by norm_num)
theorem B2572165 : Blo 1425532 2572165 := bbase (se 4 (by rfl) ⟨241140, by rfl⟩ : syracuseStep 2572165 = 482281) (by norm_num)
theorem B1605541 : Blo 1425532 1605541 := bbase (se 4 (by rfl) ⟨150519, by rfl⟩ : syracuseStep 1605541 = 301039) (by norm_num)
theorem B3211181 : Blo 1425532 3211181 := bbase (se 3 (by rfl) ⟨602096, by rfl⟩ : syracuseStep 3211181 = 1204193) (by norm_num)
theorem B1605577 : Blo 1425532 1605577 := bbase (se 2 (by rfl) ⟨602091, by rfl⟩ : syracuseStep 1605577 = 1204183) (by norm_num)
theorem B4816853 : Blo 1425532 4816853 := bbase (se 7 (by rfl) ⟨56447, by rfl⟩ : syracuseStep 4816853 = 112895) (by norm_num)
theorem B2031581 : Blo 1425532 2031581 := bbase (se 3 (by rfl) ⟨380921, by rfl⟩ : syracuseStep 2031581 = 761843) (by norm_num)
theorem B2408413 : Blo 1425532 2408413 := bbase (se 3 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 2408413 = 903155) (by norm_num)
theorem B1605613 : Blo 1425532 1605613 := bbase (se 3 (by rfl) ⟨301052, by rfl⟩ : syracuseStep 1605613 = 602105) (by norm_num)
theorem B7315445 : Blo 1425532 7315445 := bbase (se 5 (by rfl) ⟨342911, by rfl⟩ : syracuseStep 7315445 = 685823) (by norm_num)
theorem B3211253 : Blo 1425532 3211253 := bbase (se 5 (by rfl) ⟨150527, by rfl⟩ : syracuseStep 3211253 = 301055) (by norm_num)
theorem B2408467 : Blo 1425532 2408467 := bstep (se 1 (by rfl) ⟨1806350, by rfl⟩ : syracuseStep 2408467 = 3612701) B3612701
theorem B1605667 : Blo 1425532 1605667 := bstep (se 1 (by rfl) ⟨1204250, by rfl⟩ : syracuseStep 1605667 = 2408501) B2408501
theorem B3612721 : Blo 1425532 3612721 := bstep (se 2 (by rfl) ⟨1354770, by rfl⟩ : syracuseStep 3612721 = 2709541) B2709541
theorem B3252305 : Blo 1425532 3252305 := bstep (se 2 (by rfl) ⟨1219614, by rfl⟩ : syracuseStep 3252305 = 2439229) B2439229
theorem B2285651 : Blo 1425532 2285651 := bstep (se 1 (by rfl) ⟨1714238, by rfl⟩ : syracuseStep 2285651 = 3428477) B3428477
theorem B18530417 : Blo 1425532 18530417 := bstep (se 2 (by rfl) ⟨6948906, by rfl⟩ : syracuseStep 18530417 = 13897813) B13897813
theorem B1425539 : Blo 1425532 1425539 := bstep (se 1 (by rfl) ⟨1069154, by rfl⟩ : syracuseStep 1425539 = 2138309) B2138309
theorem B1425555 : Blo 1425532 1425555 := bstep (se 1 (by rfl) ⟨1069166, by rfl⟩ : syracuseStep 1425555 = 2138333) B2138333
theorem B2408609 : Blo 1425532 2408609 := bstep (se 2 (by rfl) ⟨903228, by rfl⟩ : syracuseStep 2408609 = 1806457) B1806457
theorem B1425571 : Blo 1425532 1425571 := bstep (se 1 (by rfl) ⟨1069178, by rfl⟩ : syracuseStep 1425571 = 2138357) B2138357
theorem B4817069 : Blo 1425532 4817069 := bstep (se 3 (by rfl) ⟨903200, by rfl⟩ : syracuseStep 4817069 = 1806401) B1806401
theorem B1425587 : Blo 1425532 1425587 := bstep (se 1 (by rfl) ⟨1069190, by rfl⟩ : syracuseStep 1425587 = 2138381) B2138381
theorem B1523891 : Blo 1425532 1523891 := bstep (se 1 (by rfl) ⟨1142918, by rfl⟩ : syracuseStep 1523891 = 2285837) B2285837
theorem B1605811 : Blo 1425532 1605811 := bstep (se 1 (by rfl) ⟨1204358, by rfl⟩ : syracuseStep 1605811 = 2408717) B2408717
theorem B1425603 : Blo 1425532 1425603 := bstep (se 1 (by rfl) ⟨1069202, by rfl⟩ : syracuseStep 1425603 = 2138405) B2138405
theorem B8675533 : Blo 1425532 8675533 := bstep (se 3 (by rfl) ⟨1626662, by rfl⟩ : syracuseStep 8675533 = 3253325) B3253325
theorem B2138321 : Blo 1425532 2138321 := bstep (se 2 (by rfl) ⟨801870, by rfl⟩ : syracuseStep 2138321 = 1603741) B1603741
theorem B1425619 : Blo 1425532 1425619 := bstep (se 1 (by rfl) ⟨1069214, by rfl⟩ : syracuseStep 1425619 = 2138429) B2138429
theorem B2138339 : Blo 1425532 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B1425635 : Blo 1425532 1425635 := bstep (se 1 (by rfl) ⟨1069226, by rfl⟩ : syracuseStep 1425635 = 2138453) B2138453
theorem B4817123 : Blo 1425532 4817123 := bstep (se 1 (by rfl) ⟨3612842, by rfl⟩ : syracuseStep 4817123 = 7225685) B7225685
theorem B3211505 : Blo 1425532 3211505 := bstep (se 2 (by rfl) ⟨1204314, by rfl⟩ : syracuseStep 3211505 = 2408629) B2408629
theorem B1425651 : Blo 1425532 1425651 := bstep (se 1 (by rfl) ⟨1069238, by rfl⟩ : syracuseStep 1425651 = 2138477) B2138477
theorem B2138369 : Blo 1425532 2138369 := bstep (se 2 (by rfl) ⟨801888, by rfl⟩ : syracuseStep 2138369 = 1603777) B1603777
theorem B1425667 : Blo 1425532 1425667 := bstep (se 1 (by rfl) ⟨1069250, by rfl⟩ : syracuseStep 1425667 = 2138501) B2138501
theorem B3211523 : Blo 1425532 3211523 := bstep (se 1 (by rfl) ⟨2408642, by rfl⟩ : syracuseStep 3211523 = 4817285) B4817285
theorem B10838285 : Blo 1425532 10838285 := bstep (se 3 (by rfl) ⟨2032178, by rfl⟩ : syracuseStep 10838285 = 4064357) B4064357
theorem B2138387 : Blo 1425532 2138387 := bstep (se 1 (by rfl) ⟨1603790, by rfl⟩ : syracuseStep 2138387 = 3207581) B3207581
theorem B1425683 : Blo 1425532 1425683 := bstep (se 1 (by rfl) ⟨1069262, by rfl⟩ : syracuseStep 1425683 = 2138525) B2138525
theorem B2408737 : Blo 1425532 2408737 := bstep (se 2 (by rfl) ⟨903276, by rfl⟩ : syracuseStep 2408737 = 1806553) B1806553
theorem B1425699 : Blo 1425532 1425699 := bstep (se 1 (by rfl) ⟨1069274, by rfl⟩ : syracuseStep 1425699 = 2138549) B2138549
theorem B2138417 : Blo 1425532 2138417 := bstep (se 2 (by rfl) ⟨801906, by rfl⟩ : syracuseStep 2138417 = 1603813) B1603813
theorem B4063537 : Blo 1425532 4063537 := bstep (se 2 (by rfl) ⟨1523826, by rfl⟩ : syracuseStep 4063537 = 3047653) B3047653
theorem B1425715 : Blo 1425532 1425715 := bstep (se 1 (by rfl) ⟨1069286, by rfl⟩ : syracuseStep 1425715 = 2138573) B2138573
theorem B2138435 : Blo 1425532 2138435 := bstep (se 1 (by rfl) ⟨1603826, by rfl⟩ : syracuseStep 2138435 = 3207653) B3207653
theorem B1425731 : Blo 1425532 1425731 := bstep (se 1 (by rfl) ⟨1069298, by rfl⟩ : syracuseStep 1425731 = 2138597) B2138597
theorem B3612995 : Blo 1425532 3612995 := bstep (se 1 (by rfl) ⟨2709746, by rfl⟩ : syracuseStep 3612995 = 5419493) B5419493
theorem B2408771 : Blo 1425532 2408771 := bstep (se 1 (by rfl) ⟨1806578, by rfl⟩ : syracuseStep 2408771 = 3613157) B3613157
theorem B1605955 : Blo 1425532 1605955 := bstep (se 1 (by rfl) ⟨1204466, by rfl⟩ : syracuseStep 1605955 = 2408933) B2408933
theorem B1425747 : Blo 1425532 1425747 := bstep (se 1 (by rfl) ⟨1069310, by rfl⟩ : syracuseStep 1425747 = 2138621) B2138621
theorem B2138465 : Blo 1425532 2138465 := bstep (se 2 (by rfl) ⟨801924, by rfl⟩ : syracuseStep 2138465 = 1603849) B1603849
theorem B1425763 : Blo 1425532 1425763 := bstep (se 1 (by rfl) ⟨1069322, by rfl⟩ : syracuseStep 1425763 = 2138645) B2138645
theorem B2138483 : Blo 1425532 2138483 := bstep (se 1 (by rfl) ⟨1603862, by rfl⟩ : syracuseStep 2138483 = 3207725) B3207725
theorem B1425779 : Blo 1425532 1425779 := bstep (se 1 (by rfl) ⟨1069334, by rfl⟩ : syracuseStep 1425779 = 2138669) B2138669
theorem B2285939 : Blo 1425532 2285939 := bstep (se 1 (by rfl) ⟨1714454, by rfl⟩ : syracuseStep 2285939 = 3428909) B3428909
theorem B1425795 : Blo 1425532 1425795 := bstep (se 1 (by rfl) ⟨1069346, by rfl⟩ : syracuseStep 1425795 = 2138693) B2138693
theorem B2138513 : Blo 1425532 2138513 := bstep (se 2 (by rfl) ⟨801942, by rfl⟩ : syracuseStep 2138513 = 1603885) B1603885
theorem B1425811 : Blo 1425532 1425811 := bstep (se 1 (by rfl) ⟨1069358, by rfl⟩ : syracuseStep 1425811 = 2138717) B2138717
theorem B2138531 : Blo 1425532 2138531 := bstep (se 1 (by rfl) ⟨1603898, by rfl⟩ : syracuseStep 2138531 = 3207797) B3207797
theorem B1425827 : Blo 1425532 1425827 := bstep (se 1 (by rfl) ⟨1069370, by rfl⟩ : syracuseStep 1425827 = 2138741) B2138741
theorem B7217585 : Blo 1425532 7217585 := bstep (se 2 (by rfl) ⟨2706594, by rfl⟩ : syracuseStep 7217585 = 5413189) B5413189
theorem B1425843 : Blo 1425532 1425843 := bstep (se 1 (by rfl) ⟨1069382, by rfl⟩ : syracuseStep 1425843 = 2138765) B2138765
theorem B2138561 : Blo 1425532 2138561 := bstep (se 2 (by rfl) ⟨801960, by rfl⟩ : syracuseStep 2138561 = 1603921) B1603921
theorem B1425859 : Blo 1425532 1425859 := bstep (se 1 (by rfl) ⟨1069394, by rfl⟩ : syracuseStep 1425859 = 2138789) B2138789
theorem B2408899 : Blo 1425532 2408899 := bstep (se 1 (by rfl) ⟨1806674, by rfl⟩ : syracuseStep 2408899 = 3613349) B3613349
theorem B2138579 : Blo 1425532 2138579 := bstep (se 1 (by rfl) ⟨1603934, by rfl⟩ : syracuseStep 2138579 = 3207869) B3207869
theorem B1425875 : Blo 1425532 1425875 := bstep (se 1 (by rfl) ⟨1069406, by rfl⟩ : syracuseStep 1425875 = 2138813) B2138813
theorem B1425891 : Blo 1425532 1425891 := bstep (se 1 (by rfl) ⟨1069418, by rfl⟩ : syracuseStep 1425891 = 2138837) B2138837
theorem B2138609 : Blo 1425532 2138609 := bstep (se 2 (by rfl) ⟨801978, by rfl⟩ : syracuseStep 2138609 = 1603957) B1603957
theorem B1425907 : Blo 1425532 1425907 := bstep (se 1 (by rfl) ⟨1069430, by rfl⟩ : syracuseStep 1425907 = 2138861) B2138861
theorem B4817393 : Blo 1425532 4817393 := bstep (se 2 (by rfl) ⟨1806522, by rfl⟩ : syracuseStep 4817393 = 3613045) B3613045
theorem B2138627 : Blo 1425532 2138627 := bstep (se 1 (by rfl) ⟨1603970, by rfl⟩ : syracuseStep 2138627 = 3207941) B3207941
theorem B1425923 : Blo 1425532 1425923 := bstep (se 1 (by rfl) ⟨1069442, by rfl⟩ : syracuseStep 1425923 = 2138885) B2138885
theorem B3613187 : Blo 1425532 3613187 := bstep (se 1 (by rfl) ⟨2709890, by rfl⟩ : syracuseStep 3613187 = 5419781) B5419781
theorem B5415437 : Blo 1425532 5415437 := bstep (se 3 (by rfl) ⟨1015394, by rfl⟩ : syracuseStep 5415437 = 2030789) B2030789
theorem B3211793 : Blo 1425532 3211793 := bstep (se 2 (by rfl) ⟨1204422, by rfl⟩ : syracuseStep 3211793 = 2408845) B2408845
theorem B1425939 : Blo 1425532 1425939 := bstep (se 1 (by rfl) ⟨1069454, by rfl⟩ : syracuseStep 1425939 = 2138909) B2138909
theorem B2138657 : Blo 1425532 2138657 := bstep (se 2 (by rfl) ⟨801996, by rfl⟩ : syracuseStep 2138657 = 1603993) B1603993
theorem B1425955 : Blo 1425532 1425955 := bstep (se 1 (by rfl) ⟨1069466, by rfl⟩ : syracuseStep 1425955 = 2138933) B2138933
theorem B3211811 : Blo 1425532 3211811 := bstep (se 1 (by rfl) ⟨2408858, by rfl⟩ : syracuseStep 3211811 = 4817717) B4817717
theorem B2138675 : Blo 1425532 2138675 := bstep (se 1 (by rfl) ⟨1604006, by rfl⟩ : syracuseStep 2138675 = 3208013) B3208013
theorem B1425971 : Blo 1425532 1425971 := bstep (se 1 (by rfl) ⟨1069478, by rfl⟩ : syracuseStep 1425971 = 2138957) B2138957
theorem B1425987 : Blo 1425532 1425987 := bstep (se 1 (by rfl) ⟨1069490, by rfl⟩ : syracuseStep 1425987 = 2138981) B2138981
theorem B8127053 : Blo 1425532 8127053 := bstep (se 3 (by rfl) ⟨1523822, by rfl⟩ : syracuseStep 8127053 = 3047645) B3047645
theorem B2138705 : Blo 1425532 2138705 := bstep (se 2 (by rfl) ⟨802014, by rfl⟩ : syracuseStep 2138705 = 1604029) B1604029
theorem B1426003 : Blo 1425532 1426003 := bstep (se 1 (by rfl) ⟨1069502, by rfl⟩ : syracuseStep 1426003 = 2139005) B2139005
theorem B2138723 : Blo 1425532 2138723 := bstep (se 1 (by rfl) ⟨1604042, by rfl⟩ : syracuseStep 2138723 = 3208085) B3208085
theorem B1426019 : Blo 1425532 1426019 := bstep (se 1 (by rfl) ⟨1069514, by rfl⟩ : syracuseStep 1426019 = 2139029) B2139029
theorem B1426035 : Blo 1425532 1426035 := bstep (se 1 (by rfl) ⟨1069526, by rfl⟩ : syracuseStep 1426035 = 2139053) B2139053
theorem B2138753 : Blo 1425532 2138753 := bstep (se 2 (by rfl) ⟨802032, by rfl⟩ : syracuseStep 2138753 = 1604065) B1604065
theorem B1426051 : Blo 1425532 1426051 := bstep (se 1 (by rfl) ⟨1069538, by rfl⟩ : syracuseStep 1426051 = 2139077) B2139077
theorem B2138771 : Blo 1425532 2138771 := bstep (se 1 (by rfl) ⟨1604078, by rfl⟩ : syracuseStep 2138771 = 3208157) B3208157
theorem B1426067 : Blo 1425532 1426067 := bstep (se 1 (by rfl) ⟨1069550, by rfl⟩ : syracuseStep 1426067 = 2139101) B2139101
theorem B1426083 : Blo 1425532 1426083 := bstep (se 1 (by rfl) ⟨1069562, by rfl⟩ : syracuseStep 1426083 = 2139125) B2139125
theorem B2138801 : Blo 1425532 2138801 := bstep (se 2 (by rfl) ⟨802050, by rfl⟩ : syracuseStep 2138801 = 1604101) B1604101
theorem B1426099 : Blo 1425532 1426099 := bstep (se 1 (by rfl) ⟨1069574, by rfl⟩ : syracuseStep 1426099 = 2139149) B2139149
theorem B2138819 : Blo 1425532 2138819 := bstep (se 1 (by rfl) ⟨1604114, by rfl⟩ : syracuseStep 2138819 = 3208229) B3208229
theorem B1426115 : Blo 1425532 1426115 := bstep (se 1 (by rfl) ⟨1069586, by rfl⟩ : syracuseStep 1426115 = 2139173) B2139173
theorem B3662545 : Blo 1425532 3662545 := bstep (se 2 (by rfl) ⟨1373454, by rfl⟩ : syracuseStep 3662545 = 2746909) B2746909
theorem B1426131 : Blo 1425532 1426131 := bstep (se 1 (by rfl) ⟨1069598, by rfl⟩ : syracuseStep 1426131 = 2139197) B2139197
theorem B2138849 : Blo 1425532 2138849 := bstep (se 2 (by rfl) ⟨802068, by rfl⟩ : syracuseStep 2138849 = 1604137) B1604137
theorem B1426147 : Blo 1425532 1426147 := bstep (se 1 (by rfl) ⟨1069610, by rfl⟩ : syracuseStep 1426147 = 2139221) B2139221
theorem B2138867 : Blo 1425532 2138867 := bstep (se 1 (by rfl) ⟨1604150, by rfl⟩ : syracuseStep 2138867 = 3208301) B3208301
theorem B1426163 : Blo 1425532 1426163 := bstep (se 1 (by rfl) ⟨1069622, by rfl⟩ : syracuseStep 1426163 = 2139245) B2139245
theorem B1426179 : Blo 1425532 1426179 := bstep (se 1 (by rfl) ⟨1069634, by rfl⟩ : syracuseStep 1426179 = 2139269) B2139269
theorem B2138897 : Blo 1425532 2138897 := bstep (se 2 (by rfl) ⟨802086, by rfl⟩ : syracuseStep 2138897 = 1604173) B1604173
theorem B1426195 : Blo 1425532 1426195 := bstep (se 1 (by rfl) ⟨1069646, by rfl⟩ : syracuseStep 1426195 = 2139293) B2139293
theorem B2286355 : Blo 1425532 2286355 := bstep (se 1 (by rfl) ⟨1714766, by rfl⟩ : syracuseStep 2286355 = 3429533) B3429533
theorem B2138915 : Blo 1425532 2138915 := bstep (se 1 (by rfl) ⟨1604186, by rfl⟩ : syracuseStep 2138915 = 3208373) B3208373
theorem B1426211 : Blo 1425532 1426211 := bstep (se 1 (by rfl) ⟨1069658, by rfl⟩ : syracuseStep 1426211 = 2139317) B2139317
theorem B1426227 : Blo 1425532 1426227 := bstep (se 1 (by rfl) ⟨1069670, by rfl⟩ : syracuseStep 1426227 = 2139341) B2139341
theorem B2138945 : Blo 1425532 2138945 := bstep (se 2 (by rfl) ⟨802104, by rfl⟩ : syracuseStep 2138945 = 1604209) B1604209
theorem B1426243 : Blo 1425532 1426243 := bstep (se 1 (by rfl) ⟨1069682, by rfl⟩ : syracuseStep 1426243 = 2139365) B2139365
theorem B7709509 : Blo 1425532 7709509 := bstep (se 4 (by rfl) ⟨722766, by rfl⟩ : syracuseStep 7709509 = 1445533) B1445533
theorem B2138963 : Blo 1425532 2138963 := bstep (se 1 (by rfl) ⟨1604222, by rfl⟩ : syracuseStep 2138963 = 3208445) B3208445
theorem B1426259 : Blo 1425532 1426259 := bstep (se 1 (by rfl) ⟨1069694, by rfl⟩ : syracuseStep 1426259 = 2139389) B2139389
theorem B1426275 : Blo 1425532 1426275 := bstep (se 1 (by rfl) ⟨1069706, by rfl⟩ : syracuseStep 1426275 = 2139413) B2139413
theorem B2138993 : Blo 1425532 2138993 := bstep (se 2 (by rfl) ⟨802122, by rfl⟩ : syracuseStep 2138993 = 1604245) B1604245
theorem B1426291 : Blo 1425532 1426291 := bstep (se 1 (by rfl) ⟨1069718, by rfl⟩ : syracuseStep 1426291 = 2139437) B2139437
theorem B2139011 : Blo 1425532 2139011 := bstep (se 1 (by rfl) ⟨1604258, by rfl⟩ : syracuseStep 2139011 = 3208517) B3208517
theorem B1426307 : Blo 1425532 1426307 := bstep (se 1 (by rfl) ⟨1069730, by rfl⟩ : syracuseStep 1426307 = 2139461) B2139461
theorem B1426323 : Blo 1425532 1426323 := bstep (se 1 (by rfl) ⟨1069742, by rfl⟩ : syracuseStep 1426323 = 2139485) B2139485
theorem B2139041 : Blo 1425532 2139041 := bstep (se 2 (by rfl) ⟨802140, by rfl⟩ : syracuseStep 2139041 = 1604281) B1604281
theorem B1426339 : Blo 1425532 1426339 := bstep (se 1 (by rfl) ⟨1069754, by rfl⟩ : syracuseStep 1426339 = 2139509) B2139509
theorem B2139059 : Blo 1425532 2139059 := bstep (se 1 (by rfl) ⟨1604294, by rfl⟩ : syracuseStep 2139059 = 3208589) B3208589
theorem B1426355 : Blo 1425532 1426355 := bstep (se 1 (by rfl) ⟨1069766, by rfl⟩ : syracuseStep 1426355 = 2139533) B2139533
theorem B1426371 : Blo 1425532 1426371 := bstep (se 1 (by rfl) ⟨1069778, by rfl⟩ : syracuseStep 1426371 = 2139557) B2139557
theorem B3425219 : Blo 1425532 3425219 := bstep (se 1 (by rfl) ⟨2568914, by rfl⟩ : syracuseStep 3425219 = 5137829) B5137829
theorem B8119237 : Blo 1425532 8119237 := bstep (se 4 (by rfl) ⟨761178, by rfl⟩ : syracuseStep 8119237 = 1522357) B1522357
theorem B11723717 : Blo 1425532 11723717 := bstep (se 4 (by rfl) ⟨1099098, by rfl⟩ : syracuseStep 11723717 = 2198197) B2198197
theorem B2139089 : Blo 1425532 2139089 := bstep (se 2 (by rfl) ⟨802158, by rfl⟩ : syracuseStep 2139089 = 1604317) B1604317
theorem B1426387 : Blo 1425532 1426387 := bstep (se 1 (by rfl) ⟨1069790, by rfl⟩ : syracuseStep 1426387 = 2139581) B2139581
theorem B2139107 : Blo 1425532 2139107 := bstep (se 1 (by rfl) ⟨1604330, by rfl⟩ : syracuseStep 2139107 = 3208661) B3208661
theorem B1426403 : Blo 1425532 1426403 := bstep (se 1 (by rfl) ⟨1069802, by rfl⟩ : syracuseStep 1426403 = 2139605) B2139605
theorem B1426419 : Blo 1425532 1426419 := bstep (se 1 (by rfl) ⟨1069814, by rfl⟩ : syracuseStep 1426419 = 2139629) B2139629
theorem B2139137 : Blo 1425532 2139137 := bstep (se 2 (by rfl) ⟨802176, by rfl⟩ : syracuseStep 2139137 = 1604353) B1604353
theorem B1426435 : Blo 1425532 1426435 := bstep (se 1 (by rfl) ⟨1069826, by rfl⟩ : syracuseStep 1426435 = 2139653) B2139653
theorem B2139155 : Blo 1425532 2139155 := bstep (se 1 (by rfl) ⟨1604366, by rfl⟩ : syracuseStep 2139155 = 3208733) B3208733
theorem B1426451 : Blo 1425532 1426451 := bstep (se 1 (by rfl) ⟨1069838, by rfl⟩ : syracuseStep 1426451 = 2139677) B2139677
theorem B2286625 : Blo 1425532 2286625 := bstep (se 2 (by rfl) ⟨857484, by rfl⟩ : syracuseStep 2286625 = 1714969) B1714969
theorem B1426467 : Blo 1425532 1426467 := bstep (se 1 (by rfl) ⟨1069850, by rfl⟩ : syracuseStep 1426467 = 2139701) B2139701
theorem B2139185 : Blo 1425532 2139185 := bstep (se 2 (by rfl) ⟨802194, by rfl⟩ : syracuseStep 2139185 = 1604389) B1604389
theorem B1426483 : Blo 1425532 1426483 := bstep (se 1 (by rfl) ⟨1069862, by rfl⟩ : syracuseStep 1426483 = 2139725) B2139725
theorem B2139203 : Blo 1425532 2139203 := bstep (se 1 (by rfl) ⟨1604402, by rfl⟩ : syracuseStep 2139203 = 3208805) B3208805
theorem B1426499 : Blo 1425532 1426499 := bstep (se 1 (by rfl) ⟨1069874, by rfl⟩ : syracuseStep 1426499 = 2139749) B2139749
theorem B1426515 : Blo 1425532 1426515 := bstep (se 1 (by rfl) ⟨1069886, by rfl⟩ : syracuseStep 1426515 = 2139773) B2139773
theorem B2139233 : Blo 1425532 2139233 := bstep (se 2 (by rfl) ⟨802212, by rfl⟩ : syracuseStep 2139233 = 1604425) B1604425
theorem B1426531 : Blo 1425532 1426531 := bstep (se 1 (by rfl) ⟨1069898, by rfl⟩ : syracuseStep 1426531 = 2139797) B2139797
theorem B2139251 : Blo 1425532 2139251 := bstep (se 1 (by rfl) ⟨1604438, by rfl⟩ : syracuseStep 2139251 = 3208877) B3208877
theorem B1426547 : Blo 1425532 1426547 := bstep (se 1 (by rfl) ⟨1069910, by rfl⟩ : syracuseStep 1426547 = 2139821) B2139821
theorem B1426563 : Blo 1425532 1426563 := bstep (se 1 (by rfl) ⟨1069922, by rfl⟩ : syracuseStep 1426563 = 2139845) B2139845
theorem B2139281 : Blo 1425532 2139281 := bstep (se 2 (by rfl) ⟨802230, by rfl⟩ : syracuseStep 2139281 = 1604461) B1604461
theorem B1426579 : Blo 1425532 1426579 := bstep (se 1 (by rfl) ⟨1069934, by rfl⟩ : syracuseStep 1426579 = 2139869) B2139869
theorem B2139299 : Blo 1425532 2139299 := bstep (se 1 (by rfl) ⟨1604474, by rfl⟩ : syracuseStep 2139299 = 3208949) B3208949
theorem B1426595 : Blo 1425532 1426595 := bstep (se 1 (by rfl) ⟨1069946, by rfl⟩ : syracuseStep 1426595 = 2139893) B2139893
theorem B1426611 : Blo 1425532 1426611 := bstep (se 1 (by rfl) ⟨1069958, by rfl⟩ : syracuseStep 1426611 = 2139917) B2139917
theorem B2139329 : Blo 1425532 2139329 := bstep (se 2 (by rfl) ⟨802248, by rfl⟩ : syracuseStep 2139329 = 1604497) B1604497
theorem B1426627 : Blo 1425532 1426627 := bstep (se 1 (by rfl) ⟨1069970, by rfl⟩ : syracuseStep 1426627 = 2139941) B2139941
theorem B2139347 : Blo 1425532 2139347 := bstep (se 1 (by rfl) ⟨1604510, by rfl⟩ : syracuseStep 2139347 = 3209021) B3209021
theorem B1426643 : Blo 1425532 1426643 := bstep (se 1 (by rfl) ⟨1069982, by rfl⟩ : syracuseStep 1426643 = 2139965) B2139965
theorem B1426659 : Blo 1425532 1426659 := bstep (se 1 (by rfl) ⟨1069994, by rfl⟩ : syracuseStep 1426659 = 2139989) B2139989
theorem B2139377 : Blo 1425532 2139377 := bstep (se 2 (by rfl) ⟨802266, by rfl⟩ : syracuseStep 2139377 = 1604533) B1604533
theorem B1426675 : Blo 1425532 1426675 := bstep (se 1 (by rfl) ⟨1070006, by rfl⟩ : syracuseStep 1426675 = 2140013) B2140013
theorem B2139395 : Blo 1425532 2139395 := bstep (se 1 (by rfl) ⟨1604546, by rfl⟩ : syracuseStep 2139395 = 3209093) B3209093
theorem B1426691 : Blo 1425532 1426691 := bstep (se 1 (by rfl) ⟨1070018, by rfl⟩ : syracuseStep 1426691 = 2140037) B2140037
theorem B1426707 : Blo 1425532 1426707 := bstep (se 1 (by rfl) ⟨1070030, by rfl⟩ : syracuseStep 1426707 = 2140061) B2140061
theorem B2139425 : Blo 1425532 2139425 := bstep (se 2 (by rfl) ⟨802284, by rfl⟩ : syracuseStep 2139425 = 1604569) B1604569
theorem B1426723 : Blo 1425532 1426723 := bstep (se 1 (by rfl) ⟨1070042, by rfl⟩ : syracuseStep 1426723 = 2140085) B2140085
theorem B2139443 : Blo 1425532 2139443 := bstep (se 1 (by rfl) ⟨1604582, by rfl⟩ : syracuseStep 2139443 = 3209165) B3209165
theorem B1426739 : Blo 1425532 1426739 := bstep (se 1 (by rfl) ⟨1070054, by rfl⟩ : syracuseStep 1426739 = 2140109) B2140109
theorem B1426755 : Blo 1425532 1426755 := bstep (se 1 (by rfl) ⟨1070066, by rfl⟩ : syracuseStep 1426755 = 2140133) B2140133
theorem B2139473 : Blo 1425532 2139473 := bstep (se 2 (by rfl) ⟨802302, by rfl⟩ : syracuseStep 2139473 = 1604605) B1604605
theorem B1426771 : Blo 1425532 1426771 := bstep (se 1 (by rfl) ⟨1070078, by rfl⟩ : syracuseStep 1426771 = 2140157) B2140157
theorem B2139491 : Blo 1425532 2139491 := bstep (se 1 (by rfl) ⟨1604618, by rfl⟩ : syracuseStep 2139491 = 3209237) B3209237
theorem B1426787 : Blo 1425532 1426787 := bstep (se 1 (by rfl) ⟨1070090, by rfl⟩ : syracuseStep 1426787 = 2140181) B2140181
theorem B1426803 : Blo 1425532 1426803 := bstep (se 1 (by rfl) ⟨1070102, by rfl⟩ : syracuseStep 1426803 = 2140205) B2140205
theorem B2139521 : Blo 1425532 2139521 := bstep (se 2 (by rfl) ⟨802320, by rfl⟩ : syracuseStep 2139521 = 1604641) B1604641
theorem B1426819 : Blo 1425532 1426819 := bstep (se 1 (by rfl) ⟨1070114, by rfl⟩ : syracuseStep 1426819 = 2140229) B2140229
theorem B4572557 : Blo 1425532 4572557 := bstep (se 3 (by rfl) ⟨857354, by rfl⟩ : syracuseStep 4572557 = 1714709) B1714709
theorem B2139539 : Blo 1425532 2139539 := bstep (se 1 (by rfl) ⟨1604654, by rfl⟩ : syracuseStep 2139539 = 3209309) B3209309
theorem B1426835 : Blo 1425532 1426835 := bstep (se 1 (by rfl) ⟨1070126, by rfl⟩ : syracuseStep 1426835 = 2140253) B2140253
theorem B1426851 : Blo 1425532 1426851 := bstep (se 1 (by rfl) ⟨1070138, by rfl⟩ : syracuseStep 1426851 = 2140277) B2140277
theorem B2139569 : Blo 1425532 2139569 := bstep (se 2 (by rfl) ⟨802338, by rfl⟩ : syracuseStep 2139569 = 1604677) B1604677
theorem B1426867 : Blo 1425532 1426867 := bstep (se 1 (by rfl) ⟨1070150, by rfl⟩ : syracuseStep 1426867 = 2140301) B2140301
theorem B2139587 : Blo 1425532 2139587 := bstep (se 1 (by rfl) ⟨1604690, by rfl⟩ : syracuseStep 2139587 = 3209381) B3209381
theorem B1426883 : Blo 1425532 1426883 := bstep (se 1 (by rfl) ⟨1070162, by rfl⟩ : syracuseStep 1426883 = 2140325) B2140325
theorem B1426899 : Blo 1425532 1426899 := bstep (se 1 (by rfl) ⟨1070174, by rfl⟩ : syracuseStep 1426899 = 2140349) B2140349
theorem B2139617 : Blo 1425532 2139617 := bstep (se 2 (by rfl) ⟨802356, by rfl⟩ : syracuseStep 2139617 = 1604713) B1604713
theorem B1426915 : Blo 1425532 1426915 := bstep (se 1 (by rfl) ⟨1070186, by rfl⟩ : syracuseStep 1426915 = 2140373) B2140373
theorem B9143779 : Blo 1425532 9143779 := bstep (se 1 (by rfl) ⟨6857834, by rfl⟩ : syracuseStep 9143779 = 13715669) B13715669
theorem B8127985 : Blo 1425532 8127985 := bstep (se 2 (by rfl) ⟨3047994, by rfl⟩ : syracuseStep 8127985 = 6095989) B6095989
theorem B2139635 : Blo 1425532 2139635 := bstep (se 1 (by rfl) ⟨1604726, by rfl⟩ : syracuseStep 2139635 = 3209453) B3209453
theorem B1426931 : Blo 1425532 1426931 := bstep (se 1 (by rfl) ⟨1070198, by rfl⟩ : syracuseStep 1426931 = 2140397) B2140397
theorem B1426947 : Blo 1425532 1426947 := bstep (se 1 (by rfl) ⟨1070210, by rfl⟩ : syracuseStep 1426947 = 2140421) B2140421
theorem B2139665 : Blo 1425532 2139665 := bstep (se 2 (by rfl) ⟨802374, by rfl⟩ : syracuseStep 2139665 = 1604749) B1604749
theorem B1426963 : Blo 1425532 1426963 := bstep (se 1 (by rfl) ⟨1070222, by rfl⟩ : syracuseStep 1426963 = 2140445) B2140445
theorem B2139683 : Blo 1425532 2139683 := bstep (se 1 (by rfl) ⟨1604762, by rfl⟩ : syracuseStep 2139683 = 3209525) B3209525
theorem B1426979 : Blo 1425532 1426979 := bstep (se 1 (by rfl) ⟨1070234, by rfl⟩ : syracuseStep 1426979 = 2140469) B2140469
theorem B4064813 : Blo 1425532 4064813 := bstep (se 3 (by rfl) ⟨762152, by rfl⟩ : syracuseStep 4064813 = 1524305) B1524305
theorem B1426995 : Blo 1425532 1426995 := bstep (se 1 (by rfl) ⟨1070246, by rfl⟩ : syracuseStep 1426995 = 2140493) B2140493
theorem B2139713 : Blo 1425532 2139713 := bstep (se 2 (by rfl) ⟨802392, by rfl⟩ : syracuseStep 2139713 = 1604785) B1604785
theorem B4171331 : Blo 1425532 4171331 := bstep (se 1 (by rfl) ⟨3128498, by rfl⟩ : syracuseStep 4171331 = 6256997) B6256997
theorem B1427011 : Blo 1425532 1427011 := bstep (se 1 (by rfl) ⟨1070258, by rfl⟩ : syracuseStep 1427011 = 2140517) B2140517
theorem B2139731 : Blo 1425532 2139731 := bstep (se 1 (by rfl) ⟨1604798, by rfl⟩ : syracuseStep 2139731 = 3209597) B3209597
theorem B1427027 : Blo 1425532 1427027 := bstep (se 1 (by rfl) ⟨1070270, by rfl⟩ : syracuseStep 1427027 = 2140541) B2140541
theorem B1427043 : Blo 1425532 1427043 := bstep (se 1 (by rfl) ⟨1070282, by rfl⟩ : syracuseStep 1427043 = 2140565) B2140565
theorem B2139761 : Blo 1425532 2139761 := bstep (se 2 (by rfl) ⟨802410, by rfl⟩ : syracuseStep 2139761 = 1604821) B1604821
theorem B1427059 : Blo 1425532 1427059 := bstep (se 1 (by rfl) ⟨1070294, by rfl⟩ : syracuseStep 1427059 = 2140589) B2140589
theorem B2139779 : Blo 1425532 2139779 := bstep (se 1 (by rfl) ⟨1604834, by rfl⟩ : syracuseStep 2139779 = 3209669) B3209669
theorem B1427075 : Blo 1425532 1427075 := bstep (se 1 (by rfl) ⟨1070306, by rfl⟩ : syracuseStep 1427075 = 2140613) B2140613
theorem B1427091 : Blo 1425532 1427091 := bstep (se 1 (by rfl) ⟨1070318, by rfl⟩ : syracuseStep 1427091 = 2140637) B2140637
theorem B2139809 : Blo 1425532 2139809 := bstep (se 2 (by rfl) ⟨802428, by rfl⟩ : syracuseStep 2139809 = 1604857) B1604857
theorem B1427107 : Blo 1425532 1427107 := bstep (se 1 (by rfl) ⟨1070330, by rfl⟩ : syracuseStep 1427107 = 2140661) B2140661
theorem B2139827 : Blo 1425532 2139827 := bstep (se 1 (by rfl) ⟨1604870, by rfl⟩ : syracuseStep 2139827 = 3209741) B3209741
theorem B1427123 : Blo 1425532 1427123 := bstep (se 1 (by rfl) ⟨1070342, by rfl⟩ : syracuseStep 1427123 = 2140685) B2140685
theorem B1427139 : Blo 1425532 1427139 := bstep (se 1 (by rfl) ⟨1070354, by rfl⟩ : syracuseStep 1427139 = 2140709) B2140709
theorem B2139857 : Blo 1425532 2139857 := bstep (se 2 (by rfl) ⟨802446, by rfl⟩ : syracuseStep 2139857 = 1604893) B1604893
theorem B1427155 : Blo 1425532 1427155 := bstep (se 1 (by rfl) ⟨1070366, by rfl⟩ : syracuseStep 1427155 = 2140733) B2140733
theorem B2139875 : Blo 1425532 2139875 := bstep (se 1 (by rfl) ⟨1604906, by rfl⟩ : syracuseStep 2139875 = 3209813) B3209813
theorem B1427171 : Blo 1425532 1427171 := bstep (se 1 (by rfl) ⟨1070378, by rfl⟩ : syracuseStep 1427171 = 2140757) B2140757
theorem B4064995 : Blo 1425532 4064995 := bstep (se 1 (by rfl) ⟨3048746, by rfl⟩ : syracuseStep 4064995 = 6097493) B6097493
theorem B1427187 : Blo 1425532 1427187 := bstep (se 1 (by rfl) ⟨1070390, by rfl⟩ : syracuseStep 1427187 = 2140781) B2140781
theorem B2139905 : Blo 1425532 2139905 := bstep (se 2 (by rfl) ⟨802464, by rfl⟩ : syracuseStep 2139905 = 1604929) B1604929
theorem B1427203 : Blo 1425532 1427203 := bstep (se 1 (by rfl) ⟨1070402, by rfl⟩ : syracuseStep 1427203 = 2140805) B2140805
theorem B6686477 : Blo 1425532 6686477 := bstep (se 3 (by rfl) ⟨1253714, by rfl⟩ : syracuseStep 6686477 = 2507429) B2507429
theorem B4065041 : Blo 1425532 4065041 := bstep (se 2 (by rfl) ⟨1524390, by rfl⟩ : syracuseStep 4065041 = 3048781) B3048781
theorem B2139923 : Blo 1425532 2139923 := bstep (se 1 (by rfl) ⟨1604942, by rfl⟩ : syracuseStep 2139923 = 3209885) B3209885
theorem B1427219 : Blo 1425532 1427219 := bstep (se 1 (by rfl) ⟨1070414, by rfl⟩ : syracuseStep 1427219 = 2140829) B2140829
theorem B46909205 : Blo 1425532 46909205 := bstep (se 6 (by rfl) ⟨1099434, by rfl⟩ : syracuseStep 46909205 = 2198869) B2198869
theorem B1713955 : Blo 1425532 1713955 := bstep (se 1 (by rfl) ⟨1285466, by rfl⟩ : syracuseStep 1713955 = 2570933) B2570933
theorem B1427235 : Blo 1425532 1427235 := bstep (se 1 (by rfl) ⟨1070426, by rfl⟩ : syracuseStep 1427235 = 2140853) B2140853
theorem B2139953 : Blo 1425532 2139953 := bstep (se 2 (by rfl) ⟨802482, by rfl⟩ : syracuseStep 2139953 = 1604965) B1604965
theorem B1427251 : Blo 1425532 1427251 := bstep (se 1 (by rfl) ⟨1070438, by rfl⟩ : syracuseStep 1427251 = 2140877) B2140877
theorem B2139971 : Blo 1425532 2139971 := bstep (se 1 (by rfl) ⟨1604978, by rfl⟩ : syracuseStep 2139971 = 3209957) B3209957
theorem B1427267 : Blo 1425532 1427267 := bstep (se 1 (by rfl) ⟨1070450, by rfl⟩ : syracuseStep 1427267 = 2140901) B2140901
theorem B1427283 : Blo 1425532 1427283 := bstep (se 1 (by rfl) ⟨1070462, by rfl⟩ : syracuseStep 1427283 = 2140925) B2140925
theorem B2140001 : Blo 1425532 2140001 := bstep (se 2 (by rfl) ⟨802500, by rfl⟩ : syracuseStep 2140001 = 1605001) B1605001
theorem B7219043 : Blo 1425532 7219043 := bstep (se 1 (by rfl) ⟨5414282, by rfl⟩ : syracuseStep 7219043 = 10828565) B10828565
theorem B1427299 : Blo 1425532 1427299 := bstep (se 1 (by rfl) ⟨1070474, by rfl⟩ : syracuseStep 1427299 = 2140949) B2140949
theorem B2140019 : Blo 1425532 2140019 := bstep (se 1 (by rfl) ⟨1605014, by rfl⟩ : syracuseStep 2140019 = 3210029) B3210029
theorem B1427315 : Blo 1425532 1427315 := bstep (se 1 (by rfl) ⟨1070486, by rfl⟩ : syracuseStep 1427315 = 2140973) B2140973
theorem B9267077 : Blo 1425532 9267077 := bstep (se 4 (by rfl) ⟨868788, by rfl⟩ : syracuseStep 9267077 = 1737577) B1737577
theorem B1427331 : Blo 1425532 1427331 := bstep (se 1 (by rfl) ⟨1070498, by rfl⟩ : syracuseStep 1427331 = 2140997) B2140997
theorem B2140049 : Blo 1425532 2140049 := bstep (se 2 (by rfl) ⟨802518, by rfl⟩ : syracuseStep 2140049 = 1605037) B1605037
theorem B1427347 : Blo 1425532 1427347 := bstep (se 1 (by rfl) ⟨1070510, by rfl⟩ : syracuseStep 1427347 = 2141021) B2141021
theorem B2140067 : Blo 1425532 2140067 := bstep (se 1 (by rfl) ⟨1605050, by rfl⟩ : syracuseStep 2140067 = 3210101) B3210101
theorem B1427363 : Blo 1425532 1427363 := bstep (se 1 (by rfl) ⟨1070522, by rfl⟩ : syracuseStep 1427363 = 2141045) B2141045
theorem B1427379 : Blo 1425532 1427379 := bstep (se 1 (by rfl) ⟨1070534, by rfl⟩ : syracuseStep 1427379 = 2141069) B2141069
theorem B17352629 : Blo 1425532 17352629 := bstep (se 5 (by rfl) ⟨813404, by rfl⟩ : syracuseStep 17352629 = 1626809) B1626809
theorem B2140097 : Blo 1425532 2140097 := bstep (se 2 (by rfl) ⟨802536, by rfl⟩ : syracuseStep 2140097 = 1605073) B1605073
theorem B1427395 : Blo 1425532 1427395 := bstep (se 1 (by rfl) ⟨1070546, by rfl⟩ : syracuseStep 1427395 = 2141093) B2141093
theorem B2140115 : Blo 1425532 2140115 := bstep (se 1 (by rfl) ⟨1605086, by rfl⟩ : syracuseStep 2140115 = 3210173) B3210173
theorem B1427411 : Blo 1425532 1427411 := bstep (se 1 (by rfl) ⟨1070558, by rfl⟩ : syracuseStep 1427411 = 2141117) B2141117
theorem B1427427 : Blo 1425532 1427427 := bstep (se 1 (by rfl) ⟨1070570, by rfl⟩ : syracuseStep 1427427 = 2141141) B2141141
theorem B5138417 : Blo 1425532 5138417 := bstep (se 2 (by rfl) ⟨1926906, by rfl⟩ : syracuseStep 5138417 = 3853813) B3853813
theorem B2140145 : Blo 1425532 2140145 := bstep (se 2 (by rfl) ⟨802554, by rfl⟩ : syracuseStep 2140145 = 1605109) B1605109
theorem B1427443 : Blo 1425532 1427443 := bstep (se 1 (by rfl) ⟨1070582, by rfl⟩ : syracuseStep 1427443 = 2141165) B2141165
theorem B2140163 : Blo 1425532 2140163 := bstep (se 1 (by rfl) ⟨1605122, by rfl⟩ : syracuseStep 2140163 = 3210245) B3210245
theorem B1427459 : Blo 1425532 1427459 := bstep (se 1 (by rfl) ⟨1070594, by rfl⟩ : syracuseStep 1427459 = 2141189) B2141189
theorem B1427475 : Blo 1425532 1427475 := bstep (se 1 (by rfl) ⟨1070606, by rfl⟩ : syracuseStep 1427475 = 2141213) B2141213
theorem B2140193 : Blo 1425532 2140193 := bstep (se 2 (by rfl) ⟨802572, by rfl⟩ : syracuseStep 2140193 = 1605145) B1605145
theorem B1427491 : Blo 1425532 1427491 := bstep (se 1 (by rfl) ⟨1070618, by rfl⟩ : syracuseStep 1427491 = 2141237) B2141237
theorem B2140211 : Blo 1425532 2140211 := bstep (se 1 (by rfl) ⟨1605158, by rfl⟩ : syracuseStep 2140211 = 3210317) B3210317
theorem B1427507 : Blo 1425532 1427507 := bstep (se 1 (by rfl) ⟨1070630, by rfl⟩ : syracuseStep 1427507 = 2141261) B2141261
theorem B1427523 : Blo 1425532 1427523 := bstep (se 1 (by rfl) ⟨1070642, by rfl⟩ : syracuseStep 1427523 = 2141285) B2141285
theorem B2140241 : Blo 1425532 2140241 := bstep (se 2 (by rfl) ⟨802590, by rfl⟩ : syracuseStep 2140241 = 1605181) B1605181
theorem B2140259 : Blo 1425532 2140259 := bstep (se 1 (by rfl) ⟨1605194, by rfl⟩ : syracuseStep 2140259 = 3210389) B3210389
theorem B2140289 : Blo 1425532 2140289 := bstep (se 2 (by rfl) ⟨802608, by rfl⟩ : syracuseStep 2140289 = 1605217) B1605217
theorem B2140307 : Blo 1425532 2140307 := bstep (se 1 (by rfl) ⟨1605230, by rfl⟩ : syracuseStep 2140307 = 3210461) B3210461
theorem B2140337 : Blo 1425532 2140337 := bstep (se 2 (by rfl) ⟨802626, by rfl⟩ : syracuseStep 2140337 = 1605253) B1605253
theorem B2140355 : Blo 1425532 2140355 := bstep (se 1 (by rfl) ⟨1605266, by rfl⟩ : syracuseStep 2140355 = 3210533) B3210533
theorem B2140385 : Blo 1425532 2140385 := bstep (se 2 (by rfl) ⟨802644, by rfl⟩ : syracuseStep 2140385 = 1605289) B1605289
theorem B2140403 : Blo 1425532 2140403 := bstep (se 1 (by rfl) ⟨1605302, by rfl⟩ : syracuseStep 2140403 = 3210605) B3210605
theorem B2140433 : Blo 1425532 2140433 := bstep (se 2 (by rfl) ⟨802662, by rfl⟩ : syracuseStep 2140433 = 1605325) B1605325
theorem B2140451 : Blo 1425532 2140451 := bstep (se 1 (by rfl) ⟨1605338, by rfl⟩ : syracuseStep 2140451 = 3210677) B3210677
theorem B2140481 : Blo 1425532 2140481 := bstep (se 2 (by rfl) ⟨802680, by rfl⟩ : syracuseStep 2140481 = 1605361) B1605361
theorem B2140499 : Blo 1425532 2140499 := bstep (se 1 (by rfl) ⟨1605374, by rfl⟩ : syracuseStep 2140499 = 3210749) B3210749
theorem B2140529 : Blo 1425532 2140529 := bstep (se 2 (by rfl) ⟨802698, by rfl⟩ : syracuseStep 2140529 = 1605397) B1605397
theorem B1804675 : Blo 1425532 1804675 := bstep (se 1 (by rfl) ⟨1353506, by rfl⟩ : syracuseStep 1804675 = 2707013) B2707013
theorem B2140547 : Blo 1425532 2140547 := bstep (se 1 (by rfl) ⟨1605410, by rfl⟩ : syracuseStep 2140547 = 3210821) B3210821
theorem B2140577 : Blo 1425532 2140577 := bstep (se 2 (by rfl) ⟨802716, by rfl⟩ : syracuseStep 2140577 = 1605433) B1605433
theorem B2140595 : Blo 1425532 2140595 := bstep (se 1 (by rfl) ⟨1605446, by rfl⟩ : syracuseStep 2140595 = 3210893) B3210893
theorem B2140625 : Blo 1425532 2140625 := bstep (se 2 (by rfl) ⟨802734, by rfl⟩ : syracuseStep 2140625 = 1605469) B1605469
theorem B1804771 : Blo 1425532 1804771 := bstep (se 1 (by rfl) ⟨1353578, by rfl⟩ : syracuseStep 1804771 = 2707157) B2707157
theorem B2140643 : Blo 1425532 2140643 := bstep (se 1 (by rfl) ⟨1605482, by rfl⟩ : syracuseStep 2140643 = 3210965) B3210965
theorem B2140673 : Blo 1425532 2140673 := bstep (se 2 (by rfl) ⟨802752, by rfl⟩ : syracuseStep 2140673 = 1605505) B1605505
theorem B2140691 : Blo 1425532 2140691 := bstep (se 1 (by rfl) ⟨1605518, by rfl⟩ : syracuseStep 2140691 = 3211037) B3211037
theorem B1927729 : Blo 1425532 1927729 := bstep (se 2 (by rfl) ⟨722898, by rfl⟩ : syracuseStep 1927729 = 1445797) B1445797
theorem B2140721 : Blo 1425532 2140721 := bstep (se 2 (by rfl) ⟨802770, by rfl⟩ : syracuseStep 2140721 = 1605541) B1605541
theorem B2140739 : Blo 1425532 2140739 := bstep (se 1 (by rfl) ⟨1605554, by rfl⟩ : syracuseStep 2140739 = 3211109) B3211109
theorem B10832453 : Blo 1425532 10832453 := bstep (se 4 (by rfl) ⟨1015542, by rfl⟩ : syracuseStep 10832453 = 2031085) B2031085
theorem B5417549 : Blo 1425532 5417549 := bstep (se 3 (by rfl) ⟨1015790, by rfl⟩ : syracuseStep 5417549 = 2031581) B2031581
theorem B4811345 : Blo 1425532 4811345 := bstep (se 2 (by rfl) ⟨1804254, by rfl⟩ : syracuseStep 4811345 = 3608509) B3608509
theorem B2140769 : Blo 1425532 2140769 := bstep (se 2 (by rfl) ⟨802788, by rfl⟩ : syracuseStep 2140769 = 1605577) B1605577
theorem B16239203 : Blo 1425532 16239203 := bstep (se 1 (by rfl) ⟨12179402, by rfl⟩ : syracuseStep 16239203 = 24358805) B24358805
theorem B2140787 : Blo 1425532 2140787 := bstep (se 1 (by rfl) ⟨1605590, by rfl⟩ : syracuseStep 2140787 = 3211181) B3211181
theorem B19507853 : Blo 1425532 19507853 := bstep (se 3 (by rfl) ⟨3657722, by rfl⟩ : syracuseStep 19507853 = 7315445) B7315445
theorem B7219853 : Blo 1425532 7219853 := bstep (se 3 (by rfl) ⟨1353722, by rfl⟩ : syracuseStep 7219853 = 2707445) B2707445
theorem B2140817 : Blo 1425532 2140817 := bstep (se 2 (by rfl) ⟨802806, by rfl⟩ : syracuseStep 2140817 = 1605613) B1605613
theorem B2140835 : Blo 1425532 2140835 := bstep (se 1 (by rfl) ⟨1605626, by rfl⟩ : syracuseStep 2140835 = 3211253) B3211253
theorem B2140865 : Blo 1425532 2140865 := bstep (se 2 (by rfl) ⟨802824, by rfl⟩ : syracuseStep 2140865 = 1605649) B1605649
theorem B2140883 : Blo 1425532 2140883 := bstep (se 1 (by rfl) ⟨1605662, by rfl⟩ : syracuseStep 2140883 = 3211325) B3211325
theorem B18516707 : Blo 1425532 18516707 := bstep (se 1 (by rfl) ⟨13887530, by rfl⟩ : syracuseStep 18516707 = 27775061) B27775061
theorem B2140913 : Blo 1425532 2140913 := bstep (se 2 (by rfl) ⟨802842, by rfl⟩ : syracuseStep 2140913 = 1605685) B1605685
theorem B2140931 : Blo 1425532 2140931 := bstep (se 1 (by rfl) ⟨1605698, by rfl⟩ : syracuseStep 2140931 = 3211397) B3211397
theorem B2140961 : Blo 1425532 2140961 := bstep (se 2 (by rfl) ⟨802860, by rfl⟩ : syracuseStep 2140961 = 1605721) B1605721
theorem B2140979 : Blo 1425532 2140979 := bstep (se 1 (by rfl) ⟨1605734, by rfl⟩ : syracuseStep 2140979 = 3211469) B3211469
theorem B2141009 : Blo 1425532 2141009 := bstep (se 2 (by rfl) ⟨802878, by rfl⟩ : syracuseStep 2141009 = 1605757) B1605757
theorem B2141027 : Blo 1425532 2141027 := bstep (se 1 (by rfl) ⟨1605770, by rfl⟩ : syracuseStep 2141027 = 3211541) B3211541
theorem B20573041 : Blo 1425532 20573041 := bstep (se 2 (by rfl) ⟨7714890, by rfl⟩ : syracuseStep 20573041 = 15429781) B15429781
theorem B2141057 : Blo 1425532 2141057 := bstep (se 2 (by rfl) ⟨802896, by rfl⟩ : syracuseStep 2141057 = 1605793) B1605793
theorem B8121221 : Blo 1425532 8121221 := bstep (se 4 (by rfl) ⟨761364, by rfl⟩ : syracuseStep 8121221 = 1522729) B1522729
theorem B2141075 : Blo 1425532 2141075 := bstep (se 1 (by rfl) ⟨1605806, by rfl⟩ : syracuseStep 2141075 = 3211613) B3211613
theorem B8129443 : Blo 1425532 8129443 := bstep (se 1 (by rfl) ⟨6097082, by rfl⟩ : syracuseStep 8129443 = 12194165) B12194165
theorem B2141105 : Blo 1425532 2141105 := bstep (se 2 (by rfl) ⟨802914, by rfl⟩ : syracuseStep 2141105 = 1605829) B1605829
theorem B2141123 : Blo 1425532 2141123 := bstep (se 1 (by rfl) ⟨1605842, by rfl⟩ : syracuseStep 2141123 = 3211685) B3211685
theorem B1805267 : Blo 1425532 1805267 := bstep (se 1 (by rfl) ⟨1353950, by rfl⟩ : syracuseStep 1805267 = 2707901) B2707901
theorem B2141153 : Blo 1425532 2141153 := bstep (se 2 (by rfl) ⟨802932, by rfl⟩ : syracuseStep 2141153 = 1605865) B1605865
theorem B15420401 : Blo 1425532 15420401 := bstep (se 2 (by rfl) ⟨5782650, by rfl⟩ : syracuseStep 15420401 = 11565301) B11565301
theorem B2141171 : Blo 1425532 2141171 := bstep (se 1 (by rfl) ⟨1605878, by rfl⟩ : syracuseStep 2141171 = 3211757) B3211757
theorem B2141201 : Blo 1425532 2141201 := bstep (se 2 (by rfl) ⟨802950, by rfl⟩ : syracuseStep 2141201 = 1605901) B1605901
theorem B2141219 : Blo 1425532 2141219 := bstep (se 1 (by rfl) ⟨1605914, by rfl⟩ : syracuseStep 2141219 = 3211829) B3211829
theorem B2198593 : Blo 1425532 2198593 := bstep (se 2 (by rfl) ⟨824472, by rfl⟩ : syracuseStep 2198593 = 1648945) B1648945
theorem B2141249 : Blo 1425532 2141249 := bstep (se 2 (by rfl) ⟨802968, by rfl⟩ : syracuseStep 2141249 = 1605937) B1605937
theorem B2141267 : Blo 1425532 2141267 := bstep (se 1 (by rfl) ⟨1605950, by rfl⟩ : syracuseStep 2141267 = 3211901) B3211901
theorem B4811885 : Blo 1425532 4811885 := bstep (se 3 (by rfl) ⟨902228, by rfl⟩ : syracuseStep 4811885 = 1804457) B1804457
theorem B2141297 : Blo 1425532 2141297 := bstep (se 2 (by rfl) ⟨802986, by rfl⟩ : syracuseStep 2141297 = 1605973) B1605973
theorem B4811939 : Blo 1425532 4811939 := bstep (se 1 (by rfl) ⟨3608954, by rfl⟩ : syracuseStep 4811939 = 7217909) B7217909
theorem B13200653 : Blo 1425532 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B4115747 : Blo 1425532 4115747 := bstep (se 1 (by rfl) ⟨3086810, by rfl⟩ : syracuseStep 4115747 = 6173621) B6173621
theorem B5418353 : Blo 1425532 5418353 := bstep (se 2 (by rfl) ⟨2031882, by rfl⟩ : syracuseStep 5418353 = 4063765) B4063765
theorem B4812209 : Blo 1425532 4812209 := bstep (se 2 (by rfl) ⟨1804578, by rfl⟩ : syracuseStep 4812209 = 3609157) B3609157
theorem B8129969 : Blo 1425532 8129969 := bstep (se 2 (by rfl) ⟨3048738, by rfl⟩ : syracuseStep 8129969 = 6097477) B6097477
theorem B2706929 : Blo 1425532 2706929 := bstep (se 2 (by rfl) ⟨1015098, by rfl⟩ : syracuseStep 2706929 = 2030197) B2030197
theorem B1805971 : Blo 1425532 1805971 := bstep (se 1 (by rfl) ⟨1354478, by rfl⟩ : syracuseStep 1805971 = 2708957) B2708957
theorem B1806067 : Blo 1425532 1806067 := bstep (se 1 (by rfl) ⟨1354550, by rfl⟩ : syracuseStep 1806067 = 2709101) B2709101
theorem B10170211 : Blo 1425532 10170211 := bstep (se 1 (by rfl) ⟨7627658, by rfl⟩ : syracuseStep 10170211 = 15255317) B15255317
theorem B6090659 : Blo 1425532 6090659 := bstep (se 1 (by rfl) ⟨4567994, by rfl⟩ : syracuseStep 6090659 = 9135989) B9135989
theorem B4812749 : Blo 1425532 4812749 := bstep (se 3 (by rfl) ⟨902390, by rfl⟩ : syracuseStep 4812749 = 1804781) B1804781
theorem B16470001 : Blo 1425532 16470001 := bstep (se 2 (by rfl) ⟨6176250, by rfl⟩ : syracuseStep 16470001 = 12352501) B12352501
theorem B4812803 : Blo 1425532 4812803 := bstep (se 1 (by rfl) ⟨3609602, by rfl⟩ : syracuseStep 4812803 = 7219205) B7219205
theorem B5140493 : Blo 1425532 5140493 := bstep (se 3 (by rfl) ⟨963842, by rfl⟩ : syracuseStep 5140493 = 1927685) B1927685
theorem B5419021 : Blo 1425532 5419021 := bstep (se 3 (by rfl) ⟨1016066, by rfl⟩ : syracuseStep 5419021 = 2032133) B2032133
theorem B30838805 : Blo 1425532 30838805 := bstep (se 6 (by rfl) ⟨722784, by rfl⟩ : syracuseStep 30838805 = 1445569) B1445569
theorem B3428419 : Blo 1425532 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B11571299 : Blo 1425532 11571299 := bstep (se 1 (by rfl) ⟨8678474, by rfl⟩ : syracuseStep 11571299 = 17356949) B17356949
theorem B1806563 : Blo 1425532 1806563 := bstep (se 1 (by rfl) ⟨1354922, by rfl⟩ : syracuseStep 1806563 = 2709845) B2709845
theorem B4813073 : Blo 1425532 4813073 := bstep (se 2 (by rfl) ⟨1804902, by rfl⟩ : syracuseStep 4813073 = 3609805) B3609805
theorem B3207473 : Blo 1425532 3207473 := bstep (se 2 (by rfl) ⟨1202802, by rfl⟩ : syracuseStep 3207473 = 2405605) B2405605
theorem B3207491 : Blo 1425532 3207491 := bstep (se 1 (by rfl) ⟨2405618, by rfl⟩ : syracuseStep 3207491 = 4811237) B4811237
theorem B14094691 : Blo 1425532 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B3608945 : Blo 1425532 3608945 := bstep (se 2 (by rfl) ⟨1353354, by rfl⟩ : syracuseStep 3608945 = 2706709) B2706709
theorem B2707825 : Blo 1425532 2707825 := bstep (se 2 (by rfl) ⟨1015434, by rfl⟩ : syracuseStep 2707825 = 2030869) B2030869
theorem B3608995 : Blo 1425532 3608995 := bstep (se 1 (by rfl) ⟨2706746, by rfl⟩ : syracuseStep 3608995 = 5413493) B5413493
theorem B3854765 : Blo 1425532 3854765 := bstep (se 3 (by rfl) ⟨722768, by rfl⟩ : syracuseStep 3854765 = 1445537) B1445537
theorem B4059665 : Blo 1425532 4059665 := bstep (se 2 (by rfl) ⟨1522374, by rfl⟩ : syracuseStep 4059665 = 3044749) B3044749
theorem B2707985 : Blo 1425532 2707985 := bstep (se 2 (by rfl) ⟨1015494, by rfl⟩ : syracuseStep 2707985 = 2030989) B2030989
theorem B3609137 : Blo 1425532 3609137 := bstep (se 2 (by rfl) ⟨1353426, by rfl⟩ : syracuseStep 3609137 = 2706853) B2706853
theorem B3207761 : Blo 1425532 3207761 := bstep (se 2 (by rfl) ⟨1202910, by rfl⟩ : syracuseStep 3207761 = 2405821) B2405821
theorem B3207779 : Blo 1425532 3207779 := bstep (se 1 (by rfl) ⟨2405834, by rfl⟩ : syracuseStep 3207779 = 4811669) B4811669
theorem B6853261 : Blo 1425532 6853261 := bstep (se 3 (by rfl) ⟨1284986, by rfl⟩ : syracuseStep 6853261 = 2569973) B2569973
theorem B3429091 : Blo 1425532 3429091 := bstep (se 1 (by rfl) ⟨2571818, by rfl⟩ : syracuseStep 3429091 = 5143637) B5143637
theorem B4567789 : Blo 1425532 4567789 := bstep (se 3 (by rfl) ⟨856460, by rfl⟩ : syracuseStep 4567789 = 1712921) B1712921
theorem B5419811 : Blo 1425532 5419811 := bstep (se 1 (by rfl) ⟨4064858, by rfl⟩ : syracuseStep 5419811 = 8129717) B8129717
theorem B4813613 : Blo 1425532 4813613 := bstep (se 3 (by rfl) ⟨902552, by rfl⟩ : syracuseStep 4813613 = 1805105) B1805105
theorem B2167649 : Blo 1425532 2167649 := bstep (se 2 (by rfl) ⟨812868, by rfl⟩ : syracuseStep 2167649 = 1625737) B1625737
theorem B4813667 : Blo 1425532 4813667 := bstep (se 1 (by rfl) ⟨3610250, by rfl⟩ : syracuseStep 4813667 = 7220501) B7220501
theorem B3208049 : Blo 1425532 3208049 := bstep (se 2 (by rfl) ⟨1203018, by rfl⟩ : syracuseStep 3208049 = 2406037) B2406037
theorem B3208067 : Blo 1425532 3208067 := bstep (se 1 (by rfl) ⟨2406050, by rfl⟩ : syracuseStep 3208067 = 4812101) B4812101
theorem B23442317 : Blo 1425532 23442317 := bstep (se 3 (by rfl) ⟨4395434, by rfl⟩ : syracuseStep 23442317 = 8790869) B8790869
theorem B2708387 : Blo 1425532 2708387 := bstep (se 1 (by rfl) ⟨2031290, by rfl⟩ : syracuseStep 2708387 = 4062581) B4062581
theorem B4633699 : Blo 1425532 4633699 := bstep (se 1 (by rfl) ⟨3475274, by rfl⟩ : syracuseStep 4633699 = 6950549) B6950549
theorem B4813937 : Blo 1425532 4813937 := bstep (se 2 (by rfl) ⟨1805226, by rfl⟩ : syracuseStep 4813937 = 3610453) B3610453
theorem B3208337 : Blo 1425532 3208337 := bstep (se 2 (by rfl) ⟨1203126, by rfl⟩ : syracuseStep 3208337 = 2406253) B2406253
theorem B3208355 : Blo 1425532 3208355 := bstep (se 1 (by rfl) ⟨2406266, by rfl⟩ : syracuseStep 3208355 = 4812533) B4812533
theorem B3429553 : Blo 1425532 3429553 := bstep (se 2 (by rfl) ⟨1286082, by rfl⟩ : syracuseStep 3429553 = 2572165) B2572165
theorem B39032117 : Blo 1425532 39032117 := bstep (se 5 (by rfl) ⟨1829630, by rfl⟩ : syracuseStep 39032117 = 3659261) B3659261
theorem B2405713 : Blo 1425532 2405713 := bstep (se 2 (by rfl) ⟨902142, by rfl⟩ : syracuseStep 2405713 = 1804285) B1804285
theorem B10827107 : Blo 1425532 10827107 := bstep (se 1 (by rfl) ⟨8120330, by rfl⟩ : syracuseStep 10827107 = 16240661) B16240661
theorem B2405747 : Blo 1425532 2405747 := bstep (se 1 (by rfl) ⟨1804310, by rfl⟩ : syracuseStep 2405747 = 3608621) B3608621
theorem B15422861 : Blo 1425532 15422861 := bstep (se 3 (by rfl) ⟨2891786, by rfl⟩ : syracuseStep 15422861 = 5783573) B5783573
theorem B3208625 : Blo 1425532 3208625 := bstep (se 2 (by rfl) ⟨1203234, by rfl⟩ : syracuseStep 3208625 = 2406469) B2406469
theorem B2438579 : Blo 1425532 2438579 := bstep (se 1 (by rfl) ⟨1828934, by rfl⟩ : syracuseStep 2438579 = 3657869) B3657869
theorem B3208643 : Blo 1425532 3208643 := bstep (se 1 (by rfl) ⟨2406482, by rfl⟩ : syracuseStep 3208643 = 4812965) B4812965
theorem B4060621 : Blo 1425532 4060621 := bstep (se 3 (by rfl) ⟨761366, by rfl⟩ : syracuseStep 4060621 = 1522733) B1522733
theorem B7419377 : Blo 1425532 7419377 := bstep (se 2 (by rfl) ⟨2782266, by rfl⟩ : syracuseStep 7419377 = 5564533) B5564533
theorem B7222769 : Blo 1425532 7222769 := bstep (se 2 (by rfl) ⟨2708538, by rfl⟩ : syracuseStep 7222769 = 5417077) B5417077
theorem B2405875 : Blo 1425532 2405875 := bstep (se 1 (by rfl) ⟨1804406, by rfl⟩ : syracuseStep 2405875 = 3608813) B3608813
theorem B3610129 : Blo 1425532 3610129 := bstep (se 2 (by rfl) ⟨1353798, by rfl⟩ : syracuseStep 3610129 = 2707597) B2707597
theorem B2406017 : Blo 1425532 2406017 := bstep (se 2 (by rfl) ⟨902256, by rfl⟩ : syracuseStep 2406017 = 1804513) B1804513
theorem B4814477 : Blo 1425532 4814477 := bstep (se 3 (by rfl) ⟨902714, by rfl⟩ : syracuseStep 4814477 = 1805429) B1805429
theorem B4060849 : Blo 1425532 4060849 := bstep (se 2 (by rfl) ⟨1522818, by rfl⟩ : syracuseStep 4060849 = 3045637) B3045637
theorem B4814531 : Blo 1425532 4814531 := bstep (se 1 (by rfl) ⟨3610898, by rfl⟩ : syracuseStep 4814531 = 7221797) B7221797
theorem B3208913 : Blo 1425532 3208913 := bstep (se 2 (by rfl) ⟨1203342, by rfl⟩ : syracuseStep 3208913 = 2406685) B2406685
theorem B3208931 : Blo 1425532 3208931 := bstep (se 1 (by rfl) ⟨2406698, by rfl⟩ : syracuseStep 3208931 = 4813397) B4813397
theorem B6174449 : Blo 1425532 6174449 := bstep (se 2 (by rfl) ⟨2315418, by rfl⟩ : syracuseStep 6174449 = 4630837) B4630837
theorem B2406145 : Blo 1425532 2406145 := bstep (se 2 (by rfl) ⟨902304, by rfl⟩ : syracuseStep 2406145 = 1804609) B1804609
theorem B2569987 : Blo 1425532 2569987 := bstep (se 1 (by rfl) ⟨1927490, by rfl⟩ : syracuseStep 2569987 = 3854981) B3854981
theorem B6944525 : Blo 1425532 6944525 := bstep (se 3 (by rfl) ⟨1302098, by rfl⟩ : syracuseStep 6944525 = 2604197) B2604197
theorem B2406179 : Blo 1425532 2406179 := bstep (se 1 (by rfl) ⟨1804634, by rfl⟩ : syracuseStep 2406179 = 3609269) B3609269
theorem B3610403 : Blo 1425532 3610403 := bstep (se 1 (by rfl) ⟨2707802, by rfl⟩ : syracuseStep 3610403 = 5415605) B5415605
theorem B2709283 : Blo 1425532 2709283 := bstep (se 1 (by rfl) ⟨2031962, by rfl⟩ : syracuseStep 2709283 = 4063925) B4063925
theorem B4061009 : Blo 1425532 4061009 := bstep (se 2 (by rfl) ⟨1522878, by rfl⟩ : syracuseStep 4061009 = 3045757) B3045757
theorem B6510449 : Blo 1425532 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B2406307 : Blo 1425532 2406307 := bstep (se 1 (by rfl) ⟨1804730, by rfl⟩ : syracuseStep 2406307 = 3609461) B3609461
theorem B2570147 : Blo 1425532 2570147 := bstep (se 1 (by rfl) ⟨1927610, by rfl⟩ : syracuseStep 2570147 = 3855221) B3855221
theorem B4061123 : Blo 1425532 4061123 := bstep (se 1 (by rfl) ⟨3045842, by rfl⟩ : syracuseStep 4061123 = 6091685) B6091685
theorem B2709443 : Blo 1425532 2709443 := bstep (se 1 (by rfl) ⟨2032082, by rfl⟩ : syracuseStep 2709443 = 4064165) B4064165
theorem B4814801 : Blo 1425532 4814801 := bstep (se 2 (by rfl) ⟨1805550, by rfl⟩ : syracuseStep 4814801 = 3611101) B3611101
theorem B3045347 : Blo 1425532 3045347 := bstep (se 1 (by rfl) ⟨2284010, by rfl⟩ : syracuseStep 3045347 = 4568021) B4568021
theorem B3610595 : Blo 1425532 3610595 := bstep (se 1 (by rfl) ⟨2707946, by rfl⟩ : syracuseStep 3610595 = 5415893) B5415893
theorem B3209201 : Blo 1425532 3209201 := bstep (se 2 (by rfl) ⟨1203450, by rfl⟩ : syracuseStep 3209201 = 2406901) B2406901
theorem B3209219 : Blo 1425532 3209219 := bstep (se 1 (by rfl) ⟨2406914, by rfl⟩ : syracuseStep 3209219 = 4813829) B4813829
theorem B2406449 : Blo 1425532 2406449 := bstep (se 2 (by rfl) ⟨902418, by rfl⟩ : syracuseStep 2406449 = 1804837) B1804837
theorem B9140293 : Blo 1425532 9140293 := bstep (se 4 (by rfl) ⟨856902, by rfl⟩ : syracuseStep 9140293 = 1713805) B1713805
theorem B5412977 : Blo 1425532 5412977 := bstep (se 2 (by rfl) ⟨2029866, by rfl⟩ : syracuseStep 5412977 = 4059733) B4059733
theorem B2406577 : Blo 1425532 2406577 := bstep (se 2 (by rfl) ⟨902466, by rfl⟩ : syracuseStep 2406577 = 1804933) B1804933
theorem B2570449 : Blo 1425532 2570449 := bstep (se 2 (by rfl) ⟨963918, by rfl⟩ : syracuseStep 2570449 = 1927837) B1927837
theorem B1603795 : Blo 1425532 1603795 := bstep (se 1 (by rfl) ⟨1202846, by rfl⟩ : syracuseStep 1603795 = 2405693) B2405693
theorem B2406611 : Blo 1425532 2406611 := bstep (se 1 (by rfl) ⟨1804958, by rfl⟩ : syracuseStep 2406611 = 3609917) B3609917
theorem B3209489 : Blo 1425532 3209489 := bstep (se 2 (by rfl) ⟨1203558, by rfl⟩ : syracuseStep 3209489 = 2407117) B2407117
theorem B3209507 : Blo 1425532 3209507 := bstep (se 1 (by rfl) ⟨2407130, by rfl⟩ : syracuseStep 3209507 = 4814261) B4814261
theorem B2406739 : Blo 1425532 2406739 := bstep (se 1 (by rfl) ⟨1805054, by rfl⟩ : syracuseStep 2406739 = 3610109) B3610109
theorem B1603939 : Blo 1425532 1603939 := bstep (se 1 (by rfl) ⟨1202954, by rfl⟩ : syracuseStep 1603939 = 2405909) B2405909
theorem B2283889 : Blo 1425532 2283889 := bstep (se 2 (by rfl) ⟨856458, by rfl⟩ : syracuseStep 2283889 = 1712917) B1712917
theorem B2570609 : Blo 1425532 2570609 := bstep (se 2 (by rfl) ⟨963978, by rfl⟩ : syracuseStep 2570609 = 1927957) B1927957
theorem B2029969 : Blo 1425532 2029969 := bstep (se 2 (by rfl) ⟨761238, by rfl⟩ : syracuseStep 2029969 = 1522477) B1522477
theorem B2406881 : Blo 1425532 2406881 := bstep (se 2 (by rfl) ⟨902580, by rfl⟩ : syracuseStep 2406881 = 1805161) B1805161
theorem B4815341 : Blo 1425532 4815341 := bstep (se 3 (by rfl) ⟨902876, by rfl⟩ : syracuseStep 4815341 = 1805753) B1805753
theorem B1604083 : Blo 1425532 1604083 := bstep (se 1 (by rfl) ⟨1203062, by rfl⟩ : syracuseStep 1604083 = 2406125) B2406125
theorem B2439667 : Blo 1425532 2439667 := bstep (se 1 (by rfl) ⟨1829750, by rfl⟩ : syracuseStep 2439667 = 3659501) B3659501
theorem B4569635 : Blo 1425532 4569635 := bstep (se 1 (by rfl) ⟨3427226, by rfl⟩ : syracuseStep 4569635 = 6854453) B6854453
theorem B4815395 : Blo 1425532 4815395 := bstep (se 1 (by rfl) ⟨3611546, by rfl⟩ : syracuseStep 4815395 = 7223093) B7223093
theorem B3045937 : Blo 1425532 3045937 := bstep (se 2 (by rfl) ⟨1142226, by rfl⟩ : syracuseStep 3045937 = 2284453) B2284453
theorem B3209777 : Blo 1425532 3209777 := bstep (se 2 (by rfl) ⟨1203666, by rfl⟩ : syracuseStep 3209777 = 2407333) B2407333
theorem B3209795 : Blo 1425532 3209795 := bstep (se 1 (by rfl) ⟨2407346, by rfl⟩ : syracuseStep 3209795 = 4814693) B4814693
theorem B2169425 : Blo 1425532 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B2407009 : Blo 1425532 2407009 := bstep (se 2 (by rfl) ⟨902628, by rfl⟩ : syracuseStep 2407009 = 1805257) B1805257
theorem B4340333 : Blo 1425532 4340333 := bstep (se 3 (by rfl) ⟨813812, by rfl⟩ : syracuseStep 4340333 = 1627625) B1627625
theorem B2407043 : Blo 1425532 2407043 := bstep (se 1 (by rfl) ⟨1805282, by rfl⟩ : syracuseStep 2407043 = 3610565) B3610565
theorem B1604227 : Blo 1425532 1604227 := bstep (se 1 (by rfl) ⟨1203170, by rfl⟩ : syracuseStep 1604227 = 2406341) B2406341
theorem B8125069 : Blo 1425532 8125069 := bstep (se 3 (by rfl) ⟨1523450, by rfl⟩ : syracuseStep 8125069 = 3046901) B3046901
theorem B2169571 : Blo 1425532 2169571 := bstep (se 1 (by rfl) ⟨1627178, by rfl⟩ : syracuseStep 2169571 = 3254357) B3254357
theorem B2407171 : Blo 1425532 2407171 := bstep (se 1 (by rfl) ⟨1805378, by rfl⟩ : syracuseStep 2407171 = 3610757) B3610757
theorem B1604371 : Blo 1425532 1604371 := bstep (se 1 (by rfl) ⟨1203278, by rfl⟩ : syracuseStep 1604371 = 2406557) B2406557
theorem B34716437 : Blo 1425532 34716437 := bstep (se 6 (by rfl) ⟨813666, by rfl⟩ : syracuseStep 34716437 = 1627333) B1627333
theorem B4815665 : Blo 1425532 4815665 := bstep (se 2 (by rfl) ⟨1805874, by rfl⟩ : syracuseStep 4815665 = 3611749) B3611749
theorem B12180293 : Blo 1425532 12180293 := bstep (se 4 (by rfl) ⟨1141902, by rfl⟩ : syracuseStep 12180293 = 2283805) B2283805
theorem B3210065 : Blo 1425532 3210065 := bstep (se 2 (by rfl) ⟨1203774, by rfl⟩ : syracuseStep 3210065 = 2407549) B2407549
theorem B3210083 : Blo 1425532 3210083 := bstep (se 1 (by rfl) ⟨2407562, by rfl⟩ : syracuseStep 3210083 = 4815125) B4815125
theorem B2407313 : Blo 1425532 2407313 := bstep (se 2 (by rfl) ⟨902742, by rfl⟩ : syracuseStep 2407313 = 1805485) B1805485
theorem B3611537 : Blo 1425532 3611537 := bstep (se 2 (by rfl) ⟨1354326, by rfl⟩ : syracuseStep 3611537 = 2708653) B2708653
theorem B1604515 : Blo 1425532 1604515 := bstep (se 1 (by rfl) ⟨1203386, by rfl⟩ : syracuseStep 1604515 = 2406773) B2406773
theorem B7224227 : Blo 1425532 7224227 := bstep (se 1 (by rfl) ⟨5418170, by rfl⟩ : syracuseStep 7224227 = 10836341) B10836341
theorem B4062125 : Blo 1425532 4062125 := bstep (se 3 (by rfl) ⟨761648, by rfl⟩ : syracuseStep 4062125 = 1523297) B1523297
theorem B4570033 : Blo 1425532 4570033 := bstep (se 2 (by rfl) ⟨1713762, by rfl⟩ : syracuseStep 4570033 = 3427525) B3427525
theorem B3611587 : Blo 1425532 3611587 := bstep (se 1 (by rfl) ⟨2708690, by rfl⟩ : syracuseStep 3611587 = 5417381) B5417381
theorem B3472369 : Blo 1425532 3472369 := bstep (se 2 (by rfl) ⟨1302138, by rfl⟩ : syracuseStep 3472369 = 2604277) B2604277
theorem B2259971 : Blo 1425532 2259971 := bstep (se 1 (by rfl) ⟨1694978, by rfl⟩ : syracuseStep 2259971 = 3389957) B3389957
theorem B2284561 : Blo 1425532 2284561 := bstep (se 2 (by rfl) ⟨856710, by rfl⟩ : syracuseStep 2284561 = 1713421) B1713421
theorem B2407441 : Blo 1425532 2407441 := bstep (se 2 (by rfl) ⟨902790, by rfl⟩ : syracuseStep 2407441 = 1805581) B1805581
theorem B4340785 : Blo 1425532 4340785 := bstep (se 2 (by rfl) ⟨1627794, by rfl⟩ : syracuseStep 4340785 = 3255589) B3255589
theorem B1604659 : Blo 1425532 1604659 := bstep (se 1 (by rfl) ⟨1203494, by rfl⟩ : syracuseStep 1604659 = 2406989) B2406989
theorem B2407475 : Blo 1425532 2407475 := bstep (se 1 (by rfl) ⟨1805606, by rfl⟩ : syracuseStep 2407475 = 3611213) B3611213
theorem B3611729 : Blo 1425532 3611729 := bstep (se 2 (by rfl) ⟨1354398, by rfl⟩ : syracuseStep 3611729 = 2708797) B2708797
theorem B2030675 : Blo 1425532 2030675 := bstep (se 1 (by rfl) ⟨1523006, by rfl⟩ : syracuseStep 2030675 = 3046013) B3046013
theorem B4062307 : Blo 1425532 4062307 := bstep (se 1 (by rfl) ⟨3046730, by rfl⟩ : syracuseStep 4062307 = 6093461) B6093461
theorem B3210353 : Blo 1425532 3210353 := bstep (se 2 (by rfl) ⟨1203882, by rfl⟩ : syracuseStep 3210353 = 2407765) B2407765
theorem B2169985 : Blo 1425532 2169985 := bstep (se 2 (by rfl) ⟨813744, by rfl⟩ : syracuseStep 2169985 = 1627489) B1627489
theorem B3210371 : Blo 1425532 3210371 := bstep (se 1 (by rfl) ⟨2407778, by rfl⟩ : syracuseStep 3210371 = 4815557) B4815557
theorem B2407603 : Blo 1425532 2407603 := bstep (se 1 (by rfl) ⟨1805702, by rfl⟩ : syracuseStep 2407603 = 3611405) B3611405
theorem B18791605 : Blo 1425532 18791605 := bstep (se 5 (by rfl) ⟨880856, by rfl⟩ : syracuseStep 18791605 = 1761713) B1761713
theorem B1604803 : Blo 1425532 1604803 := bstep (se 1 (by rfl) ⟨1203602, by rfl⟩ : syracuseStep 1604803 = 2407205) B2407205
theorem B4062467 : Blo 1425532 4062467 := bstep (se 1 (by rfl) ⟨3046850, by rfl⟩ : syracuseStep 4062467 = 6093701) B6093701
theorem B5487907 : Blo 1425532 5487907 := bstep (se 1 (by rfl) ⟨4115930, by rfl⟩ : syracuseStep 5487907 = 8231861) B8231861
theorem B2407745 : Blo 1425532 2407745 := bstep (se 2 (by rfl) ⟨902904, by rfl⟩ : syracuseStep 2407745 = 1805809) B1805809
theorem B4816205 : Blo 1425532 4816205 := bstep (se 3 (by rfl) ⟨903038, by rfl⟩ : syracuseStep 4816205 = 1806077) B1806077
theorem B1604947 : Blo 1425532 1604947 := bstep (se 1 (by rfl) ⟨1203710, by rfl⟩ : syracuseStep 1604947 = 2407421) B2407421
theorem B4570481 : Blo 1425532 4570481 := bstep (se 2 (by rfl) ⟨1713930, by rfl⟩ : syracuseStep 4570481 = 3427861) B3427861
theorem B12189041 : Blo 1425532 12189041 := bstep (se 2 (by rfl) ⟨4570890, by rfl⟩ : syracuseStep 12189041 = 9141781) B9141781
theorem B4816259 : Blo 1425532 4816259 := bstep (se 1 (by rfl) ⟨3612194, by rfl⟩ : syracuseStep 4816259 = 7224389) B7224389
theorem B3210641 : Blo 1425532 3210641 := bstep (se 2 (by rfl) ⟨1203990, by rfl⟩ : syracuseStep 3210641 = 2407981) B2407981
theorem B4881809 : Blo 1425532 4881809 := bstep (se 2 (by rfl) ⟨1830678, by rfl⟩ : syracuseStep 4881809 = 3661357) B3661357
theorem B3210659 : Blo 1425532 3210659 := bstep (se 1 (by rfl) ⟨2407994, by rfl⟩ : syracuseStep 3210659 = 4815989) B4815989
theorem B5143985 : Blo 1425532 5143985 := bstep (se 2 (by rfl) ⟨1928994, by rfl⟩ : syracuseStep 5143985 = 3857989) B3857989
theorem B2407873 : Blo 1425532 2407873 := bstep (se 2 (by rfl) ⟨902952, by rfl⟩ : syracuseStep 2407873 = 1805905) B1805905
theorem B2440657 : Blo 1425532 2440657 := bstep (se 2 (by rfl) ⟨915246, by rfl⟩ : syracuseStep 2440657 = 1830493) B1830493
theorem B1605091 : Blo 1425532 1605091 := bstep (se 1 (by rfl) ⟨1203818, by rfl⟩ : syracuseStep 1605091 = 2407637) B2407637
theorem B2407907 : Blo 1425532 2407907 := bstep (se 1 (by rfl) ⟨1805930, by rfl⟩ : syracuseStep 2407907 = 3611861) B3611861
theorem B6094349 : Blo 1425532 6094349 := bstep (se 3 (by rfl) ⟨1142690, by rfl⟩ : syracuseStep 6094349 = 2285381) B2285381
theorem B5414435 : Blo 1425532 5414435 := bstep (se 1 (by rfl) ⟨4060826, by rfl⟩ : syracuseStep 5414435 = 8121653) B8121653
theorem B6094385 : Blo 1425532 6094385 := bstep (se 2 (by rfl) ⟨2285394, by rfl⟩ : syracuseStep 6094385 = 4570789) B4570789
theorem B2408035 : Blo 1425532 2408035 := bstep (se 1 (by rfl) ⟨1806026, by rfl⟩ : syracuseStep 2408035 = 3612053) B3612053
theorem B1605235 : Blo 1425532 1605235 := bstep (se 1 (by rfl) ⟨1203926, by rfl⟩ : syracuseStep 1605235 = 2407853) B2407853
theorem B4816529 : Blo 1425532 4816529 := bstep (se 2 (by rfl) ⟨1806198, by rfl⟩ : syracuseStep 4816529 = 3612397) B3612397
theorem B6504113 : Blo 1425532 6504113 := bstep (se 2 (by rfl) ⟨2439042, by rfl⟩ : syracuseStep 6504113 = 4878085) B4878085
theorem B3210929 : Blo 1425532 3210929 := bstep (se 2 (by rfl) ⟨1204098, by rfl⟩ : syracuseStep 3210929 = 2408197) B2408197
theorem B3210947 : Blo 1425532 3210947 := bstep (se 1 (by rfl) ⟨2408210, by rfl⟩ : syracuseStep 3210947 = 4816421) B4816421
theorem B7225037 : Blo 1425532 7225037 := bstep (se 3 (by rfl) ⟨1354694, by rfl⟩ : syracuseStep 7225037 = 2709389) B2709389
theorem B2031313 : Blo 1425532 2031313 := bstep (se 2 (by rfl) ⟨761742, by rfl⟩ : syracuseStep 2031313 = 1523485) B1523485
theorem B18267875 : Blo 1425532 18267875 := bstep (se 1 (by rfl) ⟨13700906, by rfl⟩ : syracuseStep 18267875 = 27401813) B27401813
theorem B2408177 : Blo 1425532 2408177 := bstep (se 2 (by rfl) ⟨903066, by rfl⟩ : syracuseStep 2408177 = 1806133) B1806133
theorem B1605379 : Blo 1425532 1605379 := bstep (se 1 (by rfl) ⟨1204034, by rfl⟩ : syracuseStep 1605379 = 2408069) B2408069
theorem B46276373 : Blo 1425532 46276373 := bstep (se 6 (by rfl) ⟨1084602, by rfl⟩ : syracuseStep 46276373 = 2169205) B2169205
theorem B2031427 : Blo 1425532 2031427 := bstep (se 1 (by rfl) ⟨1523570, by rfl⟩ : syracuseStep 2031427 = 3047141) B3047141
theorem B2408305 : Blo 1425532 2408305 := bstep (se 2 (by rfl) ⟨903114, by rfl⟩ : syracuseStep 2408305 = 1806229) B1806229
theorem B1605523 : Blo 1425532 1605523 := bstep (se 1 (by rfl) ⟨1204142, by rfl⟩ : syracuseStep 1605523 = 2408285) B2408285
theorem B2408339 : Blo 1425532 2408339 := bstep (se 1 (by rfl) ⟨1806254, by rfl⟩ : syracuseStep 2408339 = 3612509) B3612509
theorem B3211217 : Blo 1425532 3211217 := bstep (se 2 (by rfl) ⟨1204206, by rfl⟩ : syracuseStep 3211217 = 2408413) B2408413
theorem B3211235 : Blo 1425532 3211235 := bstep (se 1 (by rfl) ⟨2408426, by rfl⟩ : syracuseStep 3211235 = 4816853) B4816853
theorem B7225361 : Blo 1425532 7225361 := bstep (se 2 (by rfl) ⟨2709510, by rfl⟩ : syracuseStep 7225361 = 5419021) B5419021
theorem B3211289 : Blo 1425532 3211289 := bstep (se 2 (by rfl) ⟨1204233, by rfl⟩ : syracuseStep 3211289 = 2408467) B2408467
theorem B1523767 : Blo 1425532 1523767 := bstep (se 1 (by rfl) ⟨1142825, by rfl⟩ : syracuseStep 1523767 = 2285651) B2285651
theorem B4816961 : Blo 1425532 4816961 := bstep (se 2 (by rfl) ⟨1806360, by rfl⟩ : syracuseStep 4816961 = 3612721) B3612721
theorem B4571225 : Blo 1425532 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B1605739 : Blo 1425532 1605739 := bstep (se 1 (by rfl) ⟨1204304, by rfl⟩ : syracuseStep 1605739 = 2408609) B2408609
theorem B3211379 : Blo 1425532 3211379 := bstep (se 1 (by rfl) ⟨2408534, by rfl⟩ : syracuseStep 3211379 = 4817069) B4817069
theorem B1425547 : Blo 1425532 1425547 := bstep (se 1 (by rfl) ⟨1069160, by rfl⟩ : syracuseStep 1425547 = 2138321) B2138321
theorem B1425559 : Blo 1425532 1425559 := bstep (se 1 (by rfl) ⟨1069169, by rfl⟩ : syracuseStep 1425559 = 2138339) B2138339
theorem B3211415 : Blo 1425532 3211415 := bstep (se 1 (by rfl) ⟨2408561, by rfl⟩ : syracuseStep 3211415 = 4817123) B4817123
theorem B1425579 : Blo 1425532 1425579 := bstep (se 1 (by rfl) ⟨1069184, by rfl⟩ : syracuseStep 1425579 = 2138369) B2138369
theorem B7225523 : Blo 1425532 7225523 := bstep (se 1 (by rfl) ⟨5419142, by rfl⟩ : syracuseStep 7225523 = 10838285) B10838285
theorem B1425591 : Blo 1425532 1425591 := bstep (se 1 (by rfl) ⟨1069193, by rfl⟩ : syracuseStep 1425591 = 2138387) B2138387
theorem B2138315 : Blo 1425532 2138315 := bstep (se 1 (by rfl) ⟨1603736, by rfl⟩ : syracuseStep 2138315 = 3207473) B3207473
theorem B1425611 : Blo 1425532 1425611 := bstep (se 1 (by rfl) ⟨1069208, by rfl⟩ : syracuseStep 1425611 = 2138417) B2138417
theorem B2138327 : Blo 1425532 2138327 := bstep (se 1 (by rfl) ⟨1603745, by rfl⟩ : syracuseStep 2138327 = 3207491) B3207491
theorem B1425623 : Blo 1425532 1425623 := bstep (se 1 (by rfl) ⟨1069217, by rfl⟩ : syracuseStep 1425623 = 2138435) B2138435
theorem B2408663 : Blo 1425532 2408663 := bstep (se 1 (by rfl) ⟨1806497, by rfl⟩ : syracuseStep 2408663 = 3612995) B3612995
theorem B5415133 : Blo 1425532 5415133 := bstep (se 3 (by rfl) ⟨1015337, by rfl⟩ : syracuseStep 5415133 = 2030675) B2030675
theorem B1425643 : Blo 1425532 1425643 := bstep (se 1 (by rfl) ⟨1069232, by rfl⟩ : syracuseStep 1425643 = 2138465) B2138465
theorem B1425655 : Blo 1425532 1425655 := bstep (se 1 (by rfl) ⟨1069241, by rfl⟩ : syracuseStep 1425655 = 2138483) B2138483
theorem B1425675 : Blo 1425532 1425675 := bstep (se 1 (by rfl) ⟨1069256, by rfl⟩ : syracuseStep 1425675 = 2138513) B2138513
theorem B11567377 : Blo 1425532 11567377 := bstep (se 2 (by rfl) ⟨4337766, by rfl⟩ : syracuseStep 11567377 = 8675533) B8675533
theorem B1425687 : Blo 1425532 1425687 := bstep (se 1 (by rfl) ⟨1069265, by rfl⟩ : syracuseStep 1425687 = 2138531) B2138531
theorem B2138393 : Blo 1425532 2138393 := bstep (se 2 (by rfl) ⟨801897, by rfl⟩ : syracuseStep 2138393 = 1603795) B1603795
theorem B1425707 : Blo 1425532 1425707 := bstep (se 1 (by rfl) ⟨1069280, by rfl⟩ : syracuseStep 1425707 = 2138561) B2138561
theorem B49414445 : Blo 1425532 49414445 := bstep (se 3 (by rfl) ⟨9265208, by rfl⟩ : syracuseStep 49414445 = 18530417) B18530417
theorem B1425719 : Blo 1425532 1425719 := bstep (se 1 (by rfl) ⟨1069289, by rfl⟩ : syracuseStep 1425719 = 2138579) B2138579
theorem B1425739 : Blo 1425532 1425739 := bstep (se 1 (by rfl) ⟨1069304, by rfl⟩ : syracuseStep 1425739 = 2138609) B2138609
theorem B3211595 : Blo 1425532 3211595 := bstep (se 1 (by rfl) ⟨2408696, by rfl⟩ : syracuseStep 3211595 = 4817393) B4817393
theorem B1425751 : Blo 1425532 1425751 := bstep (se 1 (by rfl) ⟨1069313, by rfl⟩ : syracuseStep 1425751 = 2138627) B2138627
theorem B2408791 : Blo 1425532 2408791 := bstep (se 1 (by rfl) ⟨1806593, by rfl⟩ : syracuseStep 2408791 = 3613187) B3613187
theorem B1425771 : Blo 1425532 1425771 := bstep (se 1 (by rfl) ⟨1069328, by rfl⟩ : syracuseStep 1425771 = 2138657) B2138657
theorem B1425783 : Blo 1425532 1425783 := bstep (se 1 (by rfl) ⟨1069337, by rfl⟩ : syracuseStep 1425783 = 2138675) B2138675
theorem B3211649 : Blo 1425532 3211649 := bstep (se 2 (by rfl) ⟨1204368, by rfl⟩ : syracuseStep 3211649 = 2408737) B2408737
theorem B2138507 : Blo 1425532 2138507 := bstep (se 1 (by rfl) ⟨1603880, by rfl⟩ : syracuseStep 2138507 = 3207761) B3207761
theorem B1425803 : Blo 1425532 1425803 := bstep (se 1 (by rfl) ⟨1069352, by rfl⟩ : syracuseStep 1425803 = 2138705) B2138705
theorem B2138519 : Blo 1425532 2138519 := bstep (se 1 (by rfl) ⟨1603889, by rfl⟩ : syracuseStep 2138519 = 3207779) B3207779
theorem B1425815 : Blo 1425532 1425815 := bstep (se 1 (by rfl) ⟨1069361, by rfl⟩ : syracuseStep 1425815 = 2138723) B2138723
theorem B1425835 : Blo 1425532 1425835 := bstep (se 1 (by rfl) ⟨1069376, by rfl⟩ : syracuseStep 1425835 = 2138753) B2138753
theorem B1425847 : Blo 1425532 1425847 := bstep (se 1 (by rfl) ⟨1069385, by rfl⟩ : syracuseStep 1425847 = 2138771) B2138771
theorem B1425867 : Blo 1425532 1425867 := bstep (se 1 (by rfl) ⟨1069400, by rfl⟩ : syracuseStep 1425867 = 2138801) B2138801
theorem B1425879 : Blo 1425532 1425879 := bstep (se 1 (by rfl) ⟨1069409, by rfl⟩ : syracuseStep 1425879 = 2138819) B2138819
theorem B2138585 : Blo 1425532 2138585 := bstep (se 2 (by rfl) ⟨801969, by rfl⟩ : syracuseStep 2138585 = 1603939) B1603939
theorem B4063709 : Blo 1425532 4063709 := bstep (se 3 (by rfl) ⟨761945, by rfl⟩ : syracuseStep 4063709 = 1523891) B1523891
theorem B1425899 : Blo 1425532 1425899 := bstep (se 1 (by rfl) ⟨1069424, by rfl⟩ : syracuseStep 1425899 = 2138849) B2138849
theorem B1425911 : Blo 1425532 1425911 := bstep (se 1 (by rfl) ⟨1069433, by rfl⟩ : syracuseStep 1425911 = 2138867) B2138867
theorem B1425931 : Blo 1425532 1425931 := bstep (se 1 (by rfl) ⟨1069448, by rfl⟩ : syracuseStep 1425931 = 2138897) B2138897
theorem B1425943 : Blo 1425532 1425943 := bstep (se 1 (by rfl) ⟨1069457, by rfl⟩ : syracuseStep 1425943 = 2138915) B2138915
theorem B3613207 : Blo 1425532 3613207 := bstep (se 1 (by rfl) ⟨2709905, by rfl⟩ : syracuseStep 3613207 = 5419811) B5419811
theorem B1425963 : Blo 1425532 1425963 := bstep (se 1 (by rfl) ⟨1069472, by rfl⟩ : syracuseStep 1425963 = 2138945) B2138945
theorem B1425975 : Blo 1425532 1425975 := bstep (se 1 (by rfl) ⟨1069481, by rfl⟩ : syracuseStep 1425975 = 2138963) B2138963
theorem B2138699 : Blo 1425532 2138699 := bstep (se 1 (by rfl) ⟨1604024, by rfl⟩ : syracuseStep 2138699 = 3208049) B3208049
theorem B1425995 : Blo 1425532 1425995 := bstep (se 1 (by rfl) ⟨1069496, by rfl⟩ : syracuseStep 1425995 = 2138993) B2138993
theorem B2138711 : Blo 1425532 2138711 := bstep (se 1 (by rfl) ⟨1604033, by rfl⟩ : syracuseStep 2138711 = 3208067) B3208067
theorem B1426007 : Blo 1425532 1426007 := bstep (se 1 (by rfl) ⟨1069505, by rfl⟩ : syracuseStep 1426007 = 2139011) B2139011
theorem B3211865 : Blo 1425532 3211865 := bstep (se 2 (by rfl) ⟨1204449, by rfl⟩ : syracuseStep 3211865 = 2408899) B2408899
theorem B4817501 : Blo 1425532 4817501 := bstep (se 3 (by rfl) ⟨903281, by rfl⟩ : syracuseStep 4817501 = 1806563) B1806563
theorem B1426027 : Blo 1425532 1426027 := bstep (se 1 (by rfl) ⟨1069520, by rfl⟩ : syracuseStep 1426027 = 2139041) B2139041
theorem B1426039 : Blo 1425532 1426039 := bstep (se 1 (by rfl) ⟨1069529, by rfl⟩ : syracuseStep 1426039 = 2139059) B2139059
theorem B7815811 : Blo 1425532 7815811 := bstep (se 1 (by rfl) ⟨5861858, by rfl⟩ : syracuseStep 7815811 = 11723717) B11723717
theorem B1426059 : Blo 1425532 1426059 := bstep (se 1 (by rfl) ⟨1069544, by rfl⟩ : syracuseStep 1426059 = 2139089) B2139089
theorem B1426071 : Blo 1425532 1426071 := bstep (se 1 (by rfl) ⟨1069553, by rfl⟩ : syracuseStep 1426071 = 2139107) B2139107
theorem B2138777 : Blo 1425532 2138777 := bstep (se 2 (by rfl) ⟨802041, by rfl⟩ : syracuseStep 2138777 = 1604083) B1604083
theorem B3252889 : Blo 1425532 3252889 := bstep (se 2 (by rfl) ⟨1219833, by rfl⟩ : syracuseStep 3252889 = 2439667) B2439667
theorem B1426091 : Blo 1425532 1426091 := bstep (se 1 (by rfl) ⟨1069568, by rfl⟩ : syracuseStep 1426091 = 2139137) B2139137
theorem B1426103 : Blo 1425532 1426103 := bstep (se 1 (by rfl) ⟨1069577, by rfl⟩ : syracuseStep 1426103 = 2139155) B2139155
theorem B1426123 : Blo 1425532 1426123 := bstep (se 1 (by rfl) ⟨1069592, by rfl⟩ : syracuseStep 1426123 = 2139185) B2139185
theorem B1426135 : Blo 1425532 1426135 := bstep (se 1 (by rfl) ⟨1069601, by rfl⟩ : syracuseStep 1426135 = 2139203) B2139203
theorem B1426155 : Blo 1425532 1426155 := bstep (se 1 (by rfl) ⟨1069616, by rfl⟩ : syracuseStep 1426155 = 2139233) B2139233
theorem B1426167 : Blo 1425532 1426167 := bstep (se 1 (by rfl) ⟨1069625, by rfl⟩ : syracuseStep 1426167 = 2139251) B2139251
theorem B2138891 : Blo 1425532 2138891 := bstep (se 1 (by rfl) ⟨1604168, by rfl⟩ : syracuseStep 2138891 = 3208337) B3208337
theorem B1426187 : Blo 1425532 1426187 := bstep (se 1 (by rfl) ⟨1069640, by rfl⟩ : syracuseStep 1426187 = 2139281) B2139281
theorem B2138903 : Blo 1425532 2138903 := bstep (se 1 (by rfl) ⟨1604177, by rfl⟩ : syracuseStep 2138903 = 3208355) B3208355
theorem B1426199 : Blo 1425532 1426199 := bstep (se 1 (by rfl) ⟨1069649, by rfl⟩ : syracuseStep 1426199 = 2139299) B2139299
theorem B1426219 : Blo 1425532 1426219 := bstep (se 1 (by rfl) ⟨1069664, by rfl⟩ : syracuseStep 1426219 = 2139329) B2139329
theorem B1426231 : Blo 1425532 1426231 := bstep (se 1 (by rfl) ⟨1069673, by rfl⟩ : syracuseStep 1426231 = 2139347) B2139347
theorem B1426251 : Blo 1425532 1426251 := bstep (se 1 (by rfl) ⟨1069688, by rfl⟩ : syracuseStep 1426251 = 2139377) B2139377
theorem B1426263 : Blo 1425532 1426263 := bstep (se 1 (by rfl) ⟨1069697, by rfl⟩ : syracuseStep 1426263 = 2139395) B2139395
theorem B2138969 : Blo 1425532 2138969 := bstep (se 2 (by rfl) ⟨802113, by rfl⟩ : syracuseStep 2138969 = 1604227) B1604227
theorem B1426283 : Blo 1425532 1426283 := bstep (se 1 (by rfl) ⟨1069712, by rfl⟩ : syracuseStep 1426283 = 2139425) B2139425
theorem B1426295 : Blo 1425532 1426295 := bstep (se 1 (by rfl) ⟨1069721, by rfl⟩ : syracuseStep 1426295 = 2139443) B2139443
theorem B1426315 : Blo 1425532 1426315 := bstep (se 1 (by rfl) ⟨1069736, by rfl⟩ : syracuseStep 1426315 = 2139473) B2139473
theorem B7218071 : Blo 1425532 7218071 := bstep (se 1 (by rfl) ⟨5413553, by rfl⟩ : syracuseStep 7218071 = 10827107) B10827107
theorem B1426327 : Blo 1425532 1426327 := bstep (se 1 (by rfl) ⟨1069745, by rfl⟩ : syracuseStep 1426327 = 2139491) B2139491
theorem B1426347 : Blo 1425532 1426347 := bstep (se 1 (by rfl) ⟨1069760, by rfl⟩ : syracuseStep 1426347 = 2139521) B2139521
theorem B10281907 : Blo 1425532 10281907 := bstep (se 1 (by rfl) ⟨7711430, by rfl⟩ : syracuseStep 10281907 = 15422861) B15422861
theorem B3048371 : Blo 1425532 3048371 := bstep (se 1 (by rfl) ⟨2286278, by rfl⟩ : syracuseStep 3048371 = 4572557) B4572557
theorem B1426359 : Blo 1425532 1426359 := bstep (se 1 (by rfl) ⟨1069769, by rfl⟩ : syracuseStep 1426359 = 2139539) B2139539
theorem B4883393 : Blo 1425532 4883393 := bstep (se 2 (by rfl) ⟨1831272, by rfl⟩ : syracuseStep 4883393 = 3662545) B3662545
theorem B2139083 : Blo 1425532 2139083 := bstep (se 1 (by rfl) ⟨1604312, by rfl⟩ : syracuseStep 2139083 = 3208625) B3208625
theorem B1426379 : Blo 1425532 1426379 := bstep (se 1 (by rfl) ⟨1069784, by rfl⟩ : syracuseStep 1426379 = 2139569) B2139569
theorem B2139095 : Blo 1425532 2139095 := bstep (se 1 (by rfl) ⟨1604321, by rfl⟩ : syracuseStep 2139095 = 3208643) B3208643
theorem B1426391 : Blo 1425532 1426391 := bstep (se 1 (by rfl) ⟨1069793, by rfl⟩ : syracuseStep 1426391 = 2139587) B2139587
theorem B2892761 : Blo 1425532 2892761 := bstep (se 2 (by rfl) ⟨1084785, by rfl⟩ : syracuseStep 2892761 = 2169571) B2169571
theorem B4572121 : Blo 1425532 4572121 := bstep (se 2 (by rfl) ⟨1714545, by rfl⟩ : syracuseStep 4572121 = 3429091) B3429091
theorem B6095837 : Blo 1425532 6095837 := bstep (se 3 (by rfl) ⟨1142969, by rfl⟩ : syracuseStep 6095837 = 2285939) B2285939
theorem B1426411 : Blo 1425532 1426411 := bstep (se 1 (by rfl) ⟨1069808, by rfl⟩ : syracuseStep 1426411 = 2139617) B2139617
theorem B1426423 : Blo 1425532 1426423 := bstep (se 1 (by rfl) ⟨1069817, by rfl⟩ : syracuseStep 1426423 = 2139635) B2139635
theorem B1426443 : Blo 1425532 1426443 := bstep (se 1 (by rfl) ⟨1069832, by rfl⟩ : syracuseStep 1426443 = 2139665) B2139665
theorem B1426455 : Blo 1425532 1426455 := bstep (se 1 (by rfl) ⟨1069841, by rfl⟩ : syracuseStep 1426455 = 2139683) B2139683
theorem B2139161 : Blo 1425532 2139161 := bstep (se 2 (by rfl) ⟨802185, by rfl⟩ : syracuseStep 2139161 = 1604371) B1604371
theorem B3048473 : Blo 1425532 3048473 := bstep (se 2 (by rfl) ⟨1143177, by rfl⟩ : syracuseStep 3048473 = 2286355) B2286355
theorem B1426475 : Blo 1425532 1426475 := bstep (se 1 (by rfl) ⟨1069856, by rfl⟩ : syracuseStep 1426475 = 2139713) B2139713
theorem B1426487 : Blo 1425532 1426487 := bstep (se 1 (by rfl) ⟨1069865, by rfl⟩ : syracuseStep 1426487 = 2139731) B2139731
theorem B1426507 : Blo 1425532 1426507 := bstep (se 1 (by rfl) ⟨1069880, by rfl⟩ : syracuseStep 1426507 = 2139761) B2139761
theorem B1426519 : Blo 1425532 1426519 := bstep (se 1 (by rfl) ⟨1069889, by rfl⟩ : syracuseStep 1426519 = 2139779) B2139779
theorem B1426539 : Blo 1425532 1426539 := bstep (se 1 (by rfl) ⟨1069904, by rfl⟩ : syracuseStep 1426539 = 2139809) B2139809
theorem B1426551 : Blo 1425532 1426551 := bstep (se 1 (by rfl) ⟨1069913, by rfl⟩ : syracuseStep 1426551 = 2139827) B2139827
theorem B2139275 : Blo 1425532 2139275 := bstep (se 1 (by rfl) ⟨1604456, by rfl⟩ : syracuseStep 2139275 = 3208913) B3208913
theorem B1426571 : Blo 1425532 1426571 := bstep (se 1 (by rfl) ⟨1069928, by rfl⟩ : syracuseStep 1426571 = 2139857) B2139857
theorem B2139287 : Blo 1425532 2139287 := bstep (se 1 (by rfl) ⟨1604465, by rfl⟩ : syracuseStep 2139287 = 3208931) B3208931
theorem B1426583 : Blo 1425532 1426583 := bstep (se 1 (by rfl) ⟨1069937, by rfl⟩ : syracuseStep 1426583 = 2139875) B2139875
theorem B1426603 : Blo 1425532 1426603 := bstep (se 1 (by rfl) ⟨1069952, by rfl⟩ : syracuseStep 1426603 = 2139905) B2139905
theorem B4629683 : Blo 1425532 4629683 := bstep (se 1 (by rfl) ⟨3472262, by rfl⟩ : syracuseStep 4629683 = 6944525) B6944525
theorem B4457651 : Blo 1425532 4457651 := bstep (se 1 (by rfl) ⟨3343238, by rfl⟩ : syracuseStep 4457651 = 6686477) B6686477
theorem B1426615 : Blo 1425532 1426615 := bstep (se 1 (by rfl) ⟨1069961, by rfl⟩ : syracuseStep 1426615 = 2139923) B2139923
theorem B1426635 : Blo 1425532 1426635 := bstep (se 1 (by rfl) ⟨1069976, by rfl⟩ : syracuseStep 1426635 = 2139953) B2139953
theorem B1426647 : Blo 1425532 1426647 := bstep (se 1 (by rfl) ⟨1069985, by rfl⟩ : syracuseStep 1426647 = 2139971) B2139971
theorem B2139353 : Blo 1425532 2139353 := bstep (se 2 (by rfl) ⟨802257, by rfl⟩ : syracuseStep 2139353 = 1604515) B1604515
theorem B10839257 : Blo 1425532 10839257 := bstep (se 2 (by rfl) ⟨4064721, by rfl⟩ : syracuseStep 10839257 = 8129443) B8129443
theorem B1426667 : Blo 1425532 1426667 := bstep (se 1 (by rfl) ⟨1070000, by rfl⟩ : syracuseStep 1426667 = 2140001) B2140001
theorem B1426679 : Blo 1425532 1426679 := bstep (se 1 (by rfl) ⟨1070009, by rfl⟩ : syracuseStep 1426679 = 2140019) B2140019
theorem B6178051 : Blo 1425532 6178051 := bstep (se 1 (by rfl) ⟨4633538, by rfl⟩ : syracuseStep 6178051 = 9267077) B9267077
theorem B1426699 : Blo 1425532 1426699 := bstep (se 1 (by rfl) ⟨1070024, by rfl⟩ : syracuseStep 1426699 = 2140049) B2140049
theorem B1713431 : Blo 1425532 1713431 := bstep (se 1 (by rfl) ⟨1285073, by rfl⟩ : syracuseStep 1713431 = 2570147) B2570147
theorem B1426711 : Blo 1425532 1426711 := bstep (se 1 (by rfl) ⟨1070033, by rfl⟩ : syracuseStep 1426711 = 2140067) B2140067
theorem B11568419 : Blo 1425532 11568419 := bstep (se 1 (by rfl) ⟨8676314, by rfl⟩ : syracuseStep 11568419 = 17352629) B17352629
theorem B1426731 : Blo 1425532 1426731 := bstep (se 1 (by rfl) ⟨1070048, by rfl⟩ : syracuseStep 1426731 = 2140097) B2140097
theorem B19785005 : Blo 1425532 19785005 := bstep (se 3 (by rfl) ⟨3709688, by rfl⟩ : syracuseStep 19785005 = 7419377) B7419377
theorem B1426743 : Blo 1425532 1426743 := bstep (se 1 (by rfl) ⟨1070057, by rfl⟩ : syracuseStep 1426743 = 2140115) B2140115
theorem B2139467 : Blo 1425532 2139467 := bstep (se 1 (by rfl) ⟨1604600, by rfl⟩ : syracuseStep 2139467 = 3209201) B3209201
theorem B1426763 : Blo 1425532 1426763 := bstep (se 1 (by rfl) ⟨1070072, by rfl⟩ : syracuseStep 1426763 = 2140145) B2140145
theorem B2139479 : Blo 1425532 2139479 := bstep (se 1 (by rfl) ⟨1604609, by rfl⟩ : syracuseStep 2139479 = 3209219) B3209219
theorem B1426775 : Blo 1425532 1426775 := bstep (se 1 (by rfl) ⟨1070081, by rfl⟩ : syracuseStep 1426775 = 2140163) B2140163
theorem B13706597 : Blo 1425532 13706597 := bstep (se 4 (by rfl) ⟨1284993, by rfl⟩ : syracuseStep 13706597 = 2569987) B2569987
theorem B1426795 : Blo 1425532 1426795 := bstep (se 1 (by rfl) ⟨1070096, by rfl⟩ : syracuseStep 1426795 = 2140193) B2140193
theorem B1426807 : Blo 1425532 1426807 := bstep (se 1 (by rfl) ⟨1070105, by rfl⟩ : syracuseStep 1426807 = 2140211) B2140211
theorem B3048833 : Blo 1425532 3048833 := bstep (se 2 (by rfl) ⟨1143312, by rfl⟩ : syracuseStep 3048833 = 2286625) B2286625
theorem B1426827 : Blo 1425532 1426827 := bstep (se 1 (by rfl) ⟨1070120, by rfl⟩ : syracuseStep 1426827 = 2140241) B2140241
theorem B1426839 : Blo 1425532 1426839 := bstep (se 1 (by rfl) ⟨1070129, by rfl⟩ : syracuseStep 1426839 = 2140259) B2140259
theorem B2139545 : Blo 1425532 2139545 := bstep (se 2 (by rfl) ⟨802329, by rfl⟩ : syracuseStep 2139545 = 1604659) B1604659
theorem B1426859 : Blo 1425532 1426859 := bstep (se 1 (by rfl) ⟨1070144, by rfl⟩ : syracuseStep 1426859 = 2140289) B2140289
theorem B1426871 : Blo 1425532 1426871 := bstep (se 1 (by rfl) ⟨1070153, by rfl⟩ : syracuseStep 1426871 = 2140307) B2140307
theorem B1426891 : Blo 1425532 1426891 := bstep (se 1 (by rfl) ⟨1070168, by rfl⟩ : syracuseStep 1426891 = 2140337) B2140337
theorem B1426903 : Blo 1425532 1426903 := bstep (se 1 (by rfl) ⟨1070177, by rfl⟩ : syracuseStep 1426903 = 2140355) B2140355
theorem B5416409 : Blo 1425532 5416409 := bstep (se 2 (by rfl) ⟨2031153, by rfl⟩ : syracuseStep 5416409 = 4062307) B4062307
theorem B6178265 : Blo 1425532 6178265 := bstep (se 2 (by rfl) ⟨2316849, by rfl⟩ : syracuseStep 6178265 = 4633699) B4633699
theorem B1426923 : Blo 1425532 1426923 := bstep (se 1 (by rfl) ⟨1070192, by rfl⟩ : syracuseStep 1426923 = 2140385) B2140385
theorem B1426935 : Blo 1425532 1426935 := bstep (se 1 (by rfl) ⟨1070201, by rfl⟩ : syracuseStep 1426935 = 2140403) B2140403
theorem B2893313 : Blo 1425532 2893313 := bstep (se 2 (by rfl) ⟨1084992, by rfl⟩ : syracuseStep 2893313 = 2169985) B2169985
theorem B2139659 : Blo 1425532 2139659 := bstep (se 1 (by rfl) ⟨1604744, by rfl⟩ : syracuseStep 2139659 = 3209489) B3209489
theorem B1426955 : Blo 1425532 1426955 := bstep (se 1 (by rfl) ⟨1070216, by rfl⟩ : syracuseStep 1426955 = 2140433) B2140433
theorem B2139671 : Blo 1425532 2139671 := bstep (se 1 (by rfl) ⟨1604753, by rfl⟩ : syracuseStep 2139671 = 3209507) B3209507
theorem B1426967 : Blo 1425532 1426967 := bstep (se 1 (by rfl) ⟨1070225, by rfl⟩ : syracuseStep 1426967 = 2140451) B2140451
theorem B1426987 : Blo 1425532 1426987 := bstep (se 1 (by rfl) ⟨1070240, by rfl⟩ : syracuseStep 1426987 = 2140481) B2140481
theorem B1426999 : Blo 1425532 1426999 := bstep (se 1 (by rfl) ⟨1070249, by rfl⟩ : syracuseStep 1426999 = 2140499) B2140499
theorem B4572737 : Blo 1425532 4572737 := bstep (se 2 (by rfl) ⟨1714776, by rfl⟩ : syracuseStep 4572737 = 3429553) B3429553
theorem B1713739 : Blo 1425532 1713739 := bstep (se 1 (by rfl) ⟨1285304, by rfl⟩ : syracuseStep 1713739 = 2570609) B2570609
theorem B1427019 : Blo 1425532 1427019 := bstep (se 1 (by rfl) ⟨1070264, by rfl⟩ : syracuseStep 1427019 = 2140529) B2140529
theorem B1427031 : Blo 1425532 1427031 := bstep (se 1 (by rfl) ⟨1070273, by rfl⟩ : syracuseStep 1427031 = 2140547) B2140547
theorem B2139737 : Blo 1425532 2139737 := bstep (se 2 (by rfl) ⟨802401, by rfl⟩ : syracuseStep 2139737 = 1604803) B1604803
theorem B1427051 : Blo 1425532 1427051 := bstep (se 1 (by rfl) ⟨1070288, by rfl⟩ : syracuseStep 1427051 = 2140577) B2140577
theorem B1427063 : Blo 1425532 1427063 := bstep (se 1 (by rfl) ⟨1070297, by rfl⟩ : syracuseStep 1427063 = 2140595) B2140595
theorem B1427083 : Blo 1425532 1427083 := bstep (se 1 (by rfl) ⟨1070312, by rfl⟩ : syracuseStep 1427083 = 2140625) B2140625
theorem B1427095 : Blo 1425532 1427095 := bstep (se 1 (by rfl) ⟨1070321, by rfl⟩ : syracuseStep 1427095 = 2140643) B2140643
theorem B1427115 : Blo 1425532 1427115 := bstep (se 1 (by rfl) ⟨1070336, by rfl⟩ : syracuseStep 1427115 = 2140673) B2140673
theorem B1427127 : Blo 1425532 1427127 := bstep (se 1 (by rfl) ⟨1070345, by rfl⟩ : syracuseStep 1427127 = 2140691) B2140691
theorem B2139851 : Blo 1425532 2139851 := bstep (se 1 (by rfl) ⟨1604888, by rfl⟩ : syracuseStep 2139851 = 3209777) B3209777
theorem B1427147 : Blo 1425532 1427147 := bstep (se 1 (by rfl) ⟨1070360, by rfl⟩ : syracuseStep 1427147 = 2140721) B2140721
theorem B2139863 : Blo 1425532 2139863 := bstep (se 1 (by rfl) ⟨1604897, by rfl⟩ : syracuseStep 2139863 = 3209795) B3209795
theorem B1427159 : Blo 1425532 1427159 := bstep (se 1 (by rfl) ⟨1070369, by rfl⟩ : syracuseStep 1427159 = 2140739) B2140739
theorem B7317209 : Blo 1425532 7317209 := bstep (se 2 (by rfl) ⟨2743953, by rfl⟩ : syracuseStep 7317209 = 5487907) B5487907
theorem B1427179 : Blo 1425532 1427179 := bstep (se 1 (by rfl) ⟨1070384, by rfl⟩ : syracuseStep 1427179 = 2140769) B2140769
theorem B2893555 : Blo 1425532 2893555 := bstep (se 1 (by rfl) ⟨2170166, by rfl⟩ : syracuseStep 2893555 = 4340333) B4340333
theorem B1427191 : Blo 1425532 1427191 := bstep (se 1 (by rfl) ⟨1070393, by rfl⟩ : syracuseStep 1427191 = 2140787) B2140787
theorem B1427211 : Blo 1425532 1427211 := bstep (se 1 (by rfl) ⟨1070408, by rfl⟩ : syracuseStep 1427211 = 2140817) B2140817
theorem B1427223 : Blo 1425532 1427223 := bstep (se 1 (by rfl) ⟨1070417, by rfl⟩ : syracuseStep 1427223 = 2140835) B2140835
theorem B2139929 : Blo 1425532 2139929 := bstep (se 2 (by rfl) ⟨802473, by rfl⟩ : syracuseStep 2139929 = 1604947) B1604947
theorem B1427243 : Blo 1425532 1427243 := bstep (se 1 (by rfl) ⟨1070432, by rfl⟩ : syracuseStep 1427243 = 2140865) B2140865
theorem B1427255 : Blo 1425532 1427255 := bstep (se 1 (by rfl) ⟨1070441, by rfl⟩ : syracuseStep 1427255 = 2140883) B2140883
theorem B1427275 : Blo 1425532 1427275 := bstep (se 1 (by rfl) ⟨1070456, by rfl⟩ : syracuseStep 1427275 = 2140913) B2140913
theorem B1427287 : Blo 1425532 1427287 := bstep (se 1 (by rfl) ⟨1070465, by rfl⟩ : syracuseStep 1427287 = 2140931) B2140931
theorem B23144291 : Blo 1425532 23144291 := bstep (se 1 (by rfl) ⟨17358218, by rfl⟩ : syracuseStep 23144291 = 34716437) B34716437
theorem B75171685 : Blo 1425532 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B1427307 : Blo 1425532 1427307 := bstep (se 1 (by rfl) ⟨1070480, by rfl⟩ : syracuseStep 1427307 = 2140961) B2140961
theorem B1427319 : Blo 1425532 1427319 := bstep (se 1 (by rfl) ⟨1070489, by rfl⟩ : syracuseStep 1427319 = 2140979) B2140979
theorem B8120195 : Blo 1425532 8120195 := bstep (se 1 (by rfl) ⟨6090146, by rfl⟩ : syracuseStep 8120195 = 12180293) B12180293
theorem B2140043 : Blo 1425532 2140043 := bstep (se 1 (by rfl) ⟨1605032, by rfl⟩ : syracuseStep 2140043 = 3210065) B3210065
theorem B1427339 : Blo 1425532 1427339 := bstep (se 1 (by rfl) ⟨1070504, by rfl⟩ : syracuseStep 1427339 = 2141009) B2141009
theorem B2140055 : Blo 1425532 2140055 := bstep (se 1 (by rfl) ⟨1605041, by rfl⟩ : syracuseStep 2140055 = 3210083) B3210083
theorem B1427351 : Blo 1425532 1427351 := bstep (se 1 (by rfl) ⟨1070513, by rfl⟩ : syracuseStep 1427351 = 2141027) B2141027
theorem B1427371 : Blo 1425532 1427371 := bstep (se 1 (by rfl) ⟨1070528, by rfl⟩ : syracuseStep 1427371 = 2141057) B2141057
theorem B1427383 : Blo 1425532 1427383 := bstep (se 1 (by rfl) ⟨1070537, by rfl⟩ : syracuseStep 1427383 = 2141075) B2141075
theorem B1427403 : Blo 1425532 1427403 := bstep (se 1 (by rfl) ⟨1070552, by rfl⟩ : syracuseStep 1427403 = 2141105) B2141105
theorem B1427415 : Blo 1425532 1427415 := bstep (se 1 (by rfl) ⟨1070561, by rfl⟩ : syracuseStep 1427415 = 2141123) B2141123
theorem B2140121 : Blo 1425532 2140121 := bstep (se 2 (by rfl) ⟨802545, by rfl⟩ : syracuseStep 2140121 = 1605091) B1605091
theorem B12191705 : Blo 1425532 12191705 := bstep (se 2 (by rfl) ⟨4571889, by rfl⟩ : syracuseStep 12191705 = 9143779) B9143779
theorem B1427435 : Blo 1425532 1427435 := bstep (se 1 (by rfl) ⟨1070576, by rfl⟩ : syracuseStep 1427435 = 2141153) B2141153
theorem B1427447 : Blo 1425532 1427447 := bstep (se 1 (by rfl) ⟨1070585, by rfl⟩ : syracuseStep 1427447 = 2141171) B2141171
theorem B1427467 : Blo 1425532 1427467 := bstep (se 1 (by rfl) ⟨1070600, by rfl⟩ : syracuseStep 1427467 = 2141201) B2141201
theorem B1427479 : Blo 1425532 1427479 := bstep (se 1 (by rfl) ⟨1070609, by rfl⟩ : syracuseStep 1427479 = 2141219) B2141219
theorem B1427499 : Blo 1425532 1427499 := bstep (se 1 (by rfl) ⟨1070624, by rfl⟩ : syracuseStep 1427499 = 2141249) B2141249
theorem B1427511 : Blo 1425532 1427511 := bstep (se 1 (by rfl) ⟨1070633, by rfl⟩ : syracuseStep 1427511 = 2141267) B2141267
theorem B1605847 : Blo 1425532 1605847 := bstep (se 1 (by rfl) ⟨1204385, by rfl⟩ : syracuseStep 1605847 = 2408771) B2408771
theorem B2140235 : Blo 1425532 2140235 := bstep (se 1 (by rfl) ⟨1605176, by rfl⟩ : syracuseStep 2140235 = 3210353) B3210353
theorem B1427531 : Blo 1425532 1427531 := bstep (se 1 (by rfl) ⟨1070648, by rfl⟩ : syracuseStep 1427531 = 2141297) B2141297
theorem B2140247 : Blo 1425532 2140247 := bstep (se 1 (by rfl) ⟨1605185, by rfl⟩ : syracuseStep 2140247 = 3210371) B3210371
theorem B2140313 : Blo 1425532 2140313 := bstep (se 2 (by rfl) ⟨802617, by rfl⟩ : syracuseStep 2140313 = 1605235) B1605235
theorem B8800435 : Blo 1425532 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B2140427 : Blo 1425532 2140427 := bstep (se 1 (by rfl) ⟨1605320, by rfl⟩ : syracuseStep 2140427 = 3210641) B3210641
theorem B3254539 : Blo 1425532 3254539 := bstep (se 1 (by rfl) ⟨2440904, by rfl⟩ : syracuseStep 3254539 = 4881809) B4881809
theorem B2140439 : Blo 1425532 2140439 := bstep (se 1 (by rfl) ⟨1605329, by rfl⟩ : syracuseStep 2140439 = 3210659) B3210659
theorem B1804619 : Blo 1425532 1804619 := bstep (se 1 (by rfl) ⟨1353464, by rfl⟩ : syracuseStep 1804619 = 2706929) B2706929
theorem B2140505 : Blo 1425532 2140505 := bstep (se 2 (by rfl) ⟨802689, by rfl⟩ : syracuseStep 2140505 = 1605379) B1605379
theorem B4336075 : Blo 1425532 4336075 := bstep (se 1 (by rfl) ⟨3252056, by rfl⟩ : syracuseStep 4336075 = 6504113) B6504113
theorem B2140619 : Blo 1425532 2140619 := bstep (se 1 (by rfl) ⟨1605464, by rfl⟩ : syracuseStep 2140619 = 3210929) B3210929
theorem B2140631 : Blo 1425532 2140631 := bstep (se 1 (by rfl) ⟨1605473, by rfl⟩ : syracuseStep 2140631 = 3210947) B3210947
theorem B13560281 : Blo 1425532 13560281 := bstep (se 2 (by rfl) ⟨5085105, by rfl⟩ : syracuseStep 13560281 = 10170211) B10170211
theorem B2140697 : Blo 1425532 2140697 := bstep (se 2 (by rfl) ⟨802761, by rfl⟩ : syracuseStep 2140697 = 1605523) B1605523
theorem B2140811 : Blo 1425532 2140811 := bstep (se 1 (by rfl) ⟨1605608, by rfl⟩ : syracuseStep 2140811 = 3211217) B3211217
theorem B2140823 : Blo 1425532 2140823 := bstep (se 1 (by rfl) ⟨1605617, by rfl⟩ : syracuseStep 2140823 = 3211235) B3211235
theorem B3426995 : Blo 1425532 3426995 := bstep (se 1 (by rfl) ⟨2570246, by rfl⟩ : syracuseStep 3426995 = 5140493) B5140493
theorem B2140889 : Blo 1425532 2140889 := bstep (se 2 (by rfl) ⟨802833, by rfl⟩ : syracuseStep 2140889 = 1605667) B1605667
theorem B2141003 : Blo 1425532 2141003 := bstep (se 1 (by rfl) ⟨1605752, by rfl⟩ : syracuseStep 2141003 = 3211505) B3211505
theorem B2141015 : Blo 1425532 2141015 := bstep (se 1 (by rfl) ⟨1605761, by rfl⟩ : syracuseStep 2141015 = 3211523) B3211523
theorem B2141081 : Blo 1425532 2141081 := bstep (se 2 (by rfl) ⟨802905, by rfl⟩ : syracuseStep 2141081 = 1605811) B1605811
theorem B3427265 : Blo 1425532 3427265 := bstep (se 2 (by rfl) ⟨1285224, by rfl⟩ : syracuseStep 3427265 = 2570449) B2570449
theorem B4811723 : Blo 1425532 4811723 := bstep (se 1 (by rfl) ⟨3608792, by rfl⟩ : syracuseStep 4811723 = 7217585) B7217585
theorem B11725829 : Blo 1425532 11725829 := bstep (se 4 (by rfl) ⟨1099296, by rfl⟩ : syracuseStep 11725829 = 2198593) B2198593
theorem B2706443 : Blo 1425532 2706443 := bstep (se 1 (by rfl) ⟨2029832, by rfl⟩ : syracuseStep 2706443 = 4059665) B4059665
theorem B1805323 : Blo 1425532 1805323 := bstep (se 1 (by rfl) ⟨1353992, by rfl⟩ : syracuseStep 1805323 = 2707985) B2707985
theorem B2141195 : Blo 1425532 2141195 := bstep (se 1 (by rfl) ⟨1605896, by rfl⟩ : syracuseStep 2141195 = 3211793) B3211793
theorem B2141207 : Blo 1425532 2141207 := bstep (se 1 (by rfl) ⟨1605905, by rfl⟩ : syracuseStep 2141207 = 3211811) B3211811
theorem B5418035 : Blo 1425532 5418035 := bstep (se 1 (by rfl) ⟨4063526, by rfl⟩ : syracuseStep 5418035 = 8127053) B8127053
theorem B5418049 : Blo 1425532 5418049 := bstep (se 2 (by rfl) ⟨2031768, by rfl⟩ : syracuseStep 5418049 = 4063537) B4063537
theorem B2141273 : Blo 1425532 2141273 := bstep (se 2 (by rfl) ⟨802977, by rfl⟩ : syracuseStep 2141273 = 1605955) B1605955
theorem B2706625 : Blo 1425532 2706625 := bstep (se 2 (by rfl) ⟨1014984, by rfl⟩ : syracuseStep 2706625 = 2029969) B2029969
theorem B4811993 : Blo 1425532 4811993 := bstep (se 2 (by rfl) ⟨1804497, by rfl⟩ : syracuseStep 4811993 = 3608995) B3608995
theorem B1445099 : Blo 1425532 1445099 := bstep (se 1 (by rfl) ⟨1083824, by rfl⟩ : syracuseStep 1445099 = 2167649) B2167649
theorem B1805591 : Blo 1425532 1805591 := bstep (se 1 (by rfl) ⟨1354193, by rfl⟩ : syracuseStep 1805591 = 2708387) B2708387
theorem B9137681 : Blo 1425532 9137681 := bstep (se 2 (by rfl) ⟨3426630, by rfl⟩ : syracuseStep 9137681 = 6853261) B6853261
theorem B10833425 : Blo 1425532 10833425 := bstep (se 2 (by rfl) ⟨4062534, by rfl⟩ : syracuseStep 10833425 = 8125069) B8125069
theorem B26021411 : Blo 1425532 26021411 := bstep (se 1 (by rfl) ⟨19516058, by rfl⟩ : syracuseStep 26021411 = 39032117) B39032117
theorem B1625719 : Blo 1425532 1625719 := bstep (se 1 (by rfl) ⟨1219289, by rfl⟩ : syracuseStep 1625719 = 2438579) B2438579
theorem B6090385 : Blo 1425532 6090385 := bstep (se 2 (by rfl) ⟨2283894, by rfl⟩ : syracuseStep 6090385 = 4567789) B4567789
theorem B2780887 : Blo 1425532 2780887 := bstep (se 1 (by rfl) ⟨2085665, by rfl⟩ : syracuseStep 2780887 = 4171331) B4171331
theorem B27430721 : Blo 1425532 27430721 := bstep (se 2 (by rfl) ⟨10286520, by rfl⟩ : syracuseStep 27430721 = 20573041) B20573041
theorem B4116299 : Blo 1425532 4116299 := bstep (se 1 (by rfl) ⟨3087224, by rfl⟩ : syracuseStep 4116299 = 6174449) B6174449
theorem B31272803 : Blo 1425532 31272803 := bstep (se 1 (by rfl) ⟨23454602, by rfl⟩ : syracuseStep 31272803 = 46909205) B46909205
theorem B2707339 : Blo 1425532 2707339 := bstep (se 1 (by rfl) ⟨2030504, by rfl⟩ : syracuseStep 2707339 = 4061009) B4061009
theorem B4812695 : Blo 1425532 4812695 := bstep (se 1 (by rfl) ⟨3609521, by rfl⟩ : syracuseStep 4812695 = 7219043) B7219043
theorem B10825649 : Blo 1425532 10825649 := bstep (se 2 (by rfl) ⟨4059618, by rfl⟩ : syracuseStep 10825649 = 8119237) B8119237
theorem B2707415 : Blo 1425532 2707415 := bstep (se 1 (by rfl) ⟨2030561, by rfl⟩ : syracuseStep 2707415 = 4061123) B4061123
theorem B1806295 : Blo 1425532 1806295 := bstep (se 1 (by rfl) ⟨1354721, by rfl⟩ : syracuseStep 1806295 = 2709443) B2709443
theorem B5787713 : Blo 1425532 5787713 := bstep (se 2 (by rfl) ⟨2170392, by rfl⟩ : syracuseStep 5787713 = 4340785) B4340785
theorem B3608651 : Blo 1425532 3608651 := bstep (se 1 (by rfl) ⟨2706488, by rfl⟩ : syracuseStep 3608651 = 5412977) B5412977
theorem B25055473 : Blo 1425532 25055473 := bstep (se 2 (by rfl) ⟨9395802, by rfl⟩ : syracuseStep 25055473 = 18791605) B18791605
theorem B7221635 : Blo 1425532 7221635 := bstep (se 1 (by rfl) ⟨5416226, by rfl⟩ : syracuseStep 7221635 = 10832453) B10832453
theorem B3207563 : Blo 1425532 3207563 := bstep (se 1 (by rfl) ⟨2405672, by rfl⟩ : syracuseStep 3207563 = 4811345) B4811345
theorem B1446283 : Blo 1425532 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B10826135 : Blo 1425532 10826135 := bstep (se 1 (by rfl) ⟨8119601, by rfl⟩ : syracuseStep 10826135 = 16239203) B16239203
theorem B13005235 : Blo 1425532 13005235 := bstep (se 1 (by rfl) ⟨9753926, by rfl⟩ : syracuseStep 13005235 = 19507853) B19507853
theorem B4813235 : Blo 1425532 4813235 := bstep (se 1 (by rfl) ⟨3609926, by rfl⟩ : syracuseStep 4813235 = 7219853) B7219853
theorem B3207617 : Blo 1425532 3207617 := bstep (se 2 (by rfl) ⟨1202856, by rfl⟩ : syracuseStep 3207617 = 2405713) B2405713
theorem B2708083 : Blo 1425532 2708083 := bstep (se 1 (by rfl) ⟨2031062, by rfl⟩ : syracuseStep 2708083 = 4062125) B4062125
theorem B3207833 : Blo 1425532 3207833 := bstep (se 2 (by rfl) ⟨1202937, by rfl⟩ : syracuseStep 3207833 = 2405875) B2405875
theorem B4813505 : Blo 1425532 4813505 := bstep (se 2 (by rfl) ⟨1805064, by rfl⟩ : syracuseStep 4813505 = 3610129) B3610129
theorem B3207923 : Blo 1425532 3207923 := bstep (se 1 (by rfl) ⟨2405942, by rfl⟩ : syracuseStep 3207923 = 4811885) B4811885
theorem B3207959 : Blo 1425532 3207959 := bstep (se 1 (by rfl) ⟨2405969, by rfl⟩ : syracuseStep 3207959 = 4811939) B4811939
theorem B2708311 : Blo 1425532 2708311 := bstep (se 1 (by rfl) ⟨2031233, by rfl⟩ : syracuseStep 2708311 = 4062467) B4062467
theorem B2708417 : Blo 1425532 2708417 := bstep (se 2 (by rfl) ⟨1015656, by rfl⟩ : syracuseStep 2708417 = 2031313) B2031313
theorem B3208139 : Blo 1425532 3208139 := bstep (se 1 (by rfl) ⟨2406104, by rfl⟩ : syracuseStep 3208139 = 4812209) B4812209
theorem B3429323 : Blo 1425532 3429323 := bstep (se 1 (by rfl) ⟨2571992, by rfl⟩ : syracuseStep 3429323 = 5143985) B5143985
theorem B5419979 : Blo 1425532 5419979 := bstep (se 1 (by rfl) ⟨4064984, by rfl⟩ : syracuseStep 5419979 = 8129969) B8129969
theorem B5419993 : Blo 1425532 5419993 := bstep (se 2 (by rfl) ⟨2032497, by rfl⟩ : syracuseStep 5419993 = 4064995) B4064995
theorem B3208193 : Blo 1425532 3208193 := bstep (se 2 (by rfl) ⟨1203072, by rfl⟩ : syracuseStep 3208193 = 2406145) B2406145
theorem B3609623 : Blo 1425532 3609623 := bstep (se 1 (by rfl) ⟨2707217, by rfl⟩ : syracuseStep 3609623 = 5414435) B5414435
theorem B2708569 : Blo 1425532 2708569 := bstep (se 2 (by rfl) ⟨1015713, by rfl⟩ : syracuseStep 2708569 = 2031427) B2031427
theorem B12178583 : Blo 1425532 12178583 := bstep (se 1 (by rfl) ⟨9133937, by rfl⟩ : syracuseStep 12178583 = 18267875) B18267875
theorem B3208409 : Blo 1425532 3208409 := bstep (se 2 (by rfl) ⟨1203153, by rfl⟩ : syracuseStep 3208409 = 2406307) B2406307
theorem B4814045 : Blo 1425532 4814045 := bstep (se 3 (by rfl) ⟨902633, by rfl⟩ : syracuseStep 4814045 = 1805267) B1805267
theorem B18519301 : Blo 1425532 18519301 := bstep (se 4 (by rfl) ⟨1736184, by rfl⟩ : syracuseStep 18519301 = 3472369) B3472369
theorem B4060439 : Blo 1425532 4060439 := bstep (se 1 (by rfl) ⟨3045329, by rfl⟩ : syracuseStep 4060439 = 6090659) B6090659
theorem B13702445 : Blo 1425532 13702445 := bstep (se 3 (by rfl) ⟨2569208, by rfl⟩ : syracuseStep 13702445 = 5138417) B5138417
theorem B3208499 : Blo 1425532 3208499 := bstep (se 1 (by rfl) ⟨2406374, by rfl⟩ : syracuseStep 3208499 = 4812749) B4812749
theorem B21960001 : Blo 1425532 21960001 := bstep (se 2 (by rfl) ⟨8235000, by rfl⟩ : syracuseStep 21960001 = 16470001) B16470001
theorem B3208535 : Blo 1425532 3208535 := bstep (se 1 (by rfl) ⟨2406401, by rfl⟩ : syracuseStep 3208535 = 4812803) B4812803
theorem B20559203 : Blo 1425532 20559203 := bstep (se 1 (by rfl) ⟨15419402, by rfl⟩ : syracuseStep 20559203 = 30838805) B30838805
theorem B2168203 : Blo 1425532 2168203 := bstep (se 1 (by rfl) ⟨1626152, by rfl⟩ : syracuseStep 2168203 = 3252305) B3252305
theorem B7714199 : Blo 1425532 7714199 := bstep (se 1 (by rfl) ⟨5785649, by rfl⟩ : syracuseStep 7714199 = 11571299) B11571299
theorem B12187057 : Blo 1425532 12187057 := bstep (se 2 (by rfl) ⟨4570146, by rfl⟩ : syracuseStep 12187057 = 9140293) B9140293
theorem B3208715 : Blo 1425532 3208715 := bstep (se 1 (by rfl) ⟨2406536, by rfl⟩ : syracuseStep 3208715 = 4813073) B4813073
theorem B3208769 : Blo 1425532 3208769 := bstep (se 2 (by rfl) ⟨1203288, by rfl⟩ : syracuseStep 3208769 = 2406577) B2406577
theorem B2405963 : Blo 1425532 2405963 := bstep (se 1 (by rfl) ⟨1804472, by rfl⟩ : syracuseStep 2405963 = 3608945) B3608945
theorem B2569843 : Blo 1425532 2569843 := bstep (se 1 (by rfl) ⟨1927382, by rfl⟩ : syracuseStep 2569843 = 3854765) B3854765
theorem B3610291 : Blo 1425532 3610291 := bstep (se 1 (by rfl) ⟨2707718, by rfl⟩ : syracuseStep 3610291 = 5415437) B5415437
theorem B2406091 : Blo 1425532 2406091 := bstep (se 1 (by rfl) ⟨1804568, by rfl⟩ : syracuseStep 2406091 = 3609137) B3609137
theorem B3208985 : Blo 1425532 3208985 := bstep (se 2 (by rfl) ⟨1203369, by rfl⟩ : syracuseStep 3208985 = 2406739) B2406739
theorem B3045185 : Blo 1425532 3045185 := bstep (se 2 (by rfl) ⟨1141944, by rfl⟩ : syracuseStep 3045185 = 2283889) B2283889
theorem B3610433 : Blo 1425532 3610433 := bstep (se 2 (by rfl) ⟨1353912, by rfl⟩ : syracuseStep 3610433 = 2707825) B2707825
theorem B2406233 : Blo 1425532 2406233 := bstep (se 2 (by rfl) ⟨902337, by rfl⟩ : syracuseStep 2406233 = 1804675) B1804675
theorem B3209075 : Blo 1425532 3209075 := bstep (se 1 (by rfl) ⟨2406806, by rfl⟩ : syracuseStep 3209075 = 4813613) B4813613
theorem B3209111 : Blo 1425532 3209111 := bstep (se 1 (by rfl) ⟨2406833, by rfl⟩ : syracuseStep 3209111 = 4813667) B4813667
theorem B15628211 : Blo 1425532 15628211 := bstep (se 1 (by rfl) ⟨11721158, by rfl⟩ : syracuseStep 15628211 = 23442317) B23442317
theorem B2283479 : Blo 1425532 2283479 := bstep (se 1 (by rfl) ⟨1712609, by rfl⟩ : syracuseStep 2283479 = 3425219) B3425219
theorem B2406361 : Blo 1425532 2406361 := bstep (se 2 (by rfl) ⟨902385, by rfl⟩ : syracuseStep 2406361 = 1804771) B1804771
theorem B4061249 : Blo 1425532 4061249 := bstep (se 2 (by rfl) ⟨1522968, by rfl⟩ : syracuseStep 4061249 = 3045937) B3045937
theorem B2570305 : Blo 1425532 2570305 := bstep (se 2 (by rfl) ⟨963864, by rfl⟩ : syracuseStep 2570305 = 1927729) B1927729
theorem B3209291 : Blo 1425532 3209291 := bstep (se 1 (by rfl) ⟨2406968, by rfl⟩ : syracuseStep 3209291 = 4813937) B4813937
theorem B3209345 : Blo 1425532 3209345 := bstep (se 2 (by rfl) ⟨1203504, by rfl⟩ : syracuseStep 3209345 = 2407009) B2407009
theorem B1603831 : Blo 1425532 1603831 := bstep (se 1 (by rfl) ⟨1202873, by rfl⟩ : syracuseStep 1603831 = 2405747) B2405747
theorem B4815179 : Blo 1425532 4815179 := bstep (se 1 (by rfl) ⟨3611384, by rfl⟩ : syracuseStep 4815179 = 7222769) B7222769
theorem B3209561 : Blo 1425532 3209561 := bstep (se 2 (by rfl) ⟨1203585, by rfl⟩ : syracuseStep 3209561 = 2407171) B2407171
theorem B2709875 : Blo 1425532 2709875 := bstep (se 1 (by rfl) ⟨2032406, by rfl⟩ : syracuseStep 2709875 = 4064813) B4064813
theorem B1604011 : Blo 1425532 1604011 := bstep (se 1 (by rfl) ⟨1203008, by rfl⟩ : syracuseStep 1604011 = 2406017) B2406017
theorem B10279345 : Blo 1425532 10279345 := bstep (se 2 (by rfl) ⟨3854754, by rfl⟩ : syracuseStep 10279345 = 7709509) B7709509
theorem B3209651 : Blo 1425532 3209651 := bstep (se 1 (by rfl) ⟨2407238, by rfl⟩ : syracuseStep 3209651 = 4814477) B4814477
theorem B3209687 : Blo 1425532 3209687 := bstep (se 1 (by rfl) ⟨2407265, by rfl⟩ : syracuseStep 3209687 = 4814531) B4814531
theorem B2710027 : Blo 1425532 2710027 := bstep (se 1 (by rfl) ⟨2032520, by rfl⟩ : syracuseStep 2710027 = 4065041) B4065041
theorem B1604119 : Blo 1425532 1604119 := bstep (se 1 (by rfl) ⟨1203089, by rfl⟩ : syracuseStep 1604119 = 2406179) B2406179
theorem B2406935 : Blo 1425532 2406935 := bstep (se 1 (by rfl) ⟨1805201, by rfl⟩ : syracuseStep 2406935 = 3610403) B3610403
theorem B6093377 : Blo 1425532 6093377 := bstep (se 2 (by rfl) ⟨2285016, by rfl⟩ : syracuseStep 6093377 = 4570033) B4570033
theorem B4340299 : Blo 1425532 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B4815449 : Blo 1425532 4815449 := bstep (se 2 (by rfl) ⟨1805793, by rfl⟩ : syracuseStep 4815449 = 3611587) B3611587
theorem B3209867 : Blo 1425532 3209867 := bstep (se 1 (by rfl) ⟨2407400, by rfl⟩ : syracuseStep 3209867 = 4814801) B4814801
theorem B2030231 : Blo 1425532 2030231 := bstep (se 1 (by rfl) ⟨1522673, by rfl⟩ : syracuseStep 2030231 = 3045347) B3045347
theorem B2407063 : Blo 1425532 2407063 := bstep (se 1 (by rfl) ⟨1805297, by rfl⟩ : syracuseStep 2407063 = 3610595) B3610595
theorem B3046081 : Blo 1425532 3046081 := bstep (se 2 (by rfl) ⟨1142280, by rfl⟩ : syracuseStep 3046081 = 2284561) B2284561
theorem B3209921 : Blo 1425532 3209921 := bstep (se 2 (by rfl) ⟨1203720, by rfl⟩ : syracuseStep 3209921 = 2407441) B2407441
theorem B1604299 : Blo 1425532 1604299 := bstep (se 1 (by rfl) ⟨1203224, by rfl⟩ : syracuseStep 1604299 = 2406449) B2406449
theorem B1604407 : Blo 1425532 1604407 := bstep (se 1 (by rfl) ⟨1203305, by rfl⟩ : syracuseStep 1604407 = 2406611) B2406611
theorem B3210137 : Blo 1425532 3210137 := bstep (se 2 (by rfl) ⟨1203801, by rfl⟩ : syracuseStep 3210137 = 2407603) B2407603
theorem B1604587 : Blo 1425532 1604587 := bstep (se 1 (by rfl) ⟨1203440, by rfl⟩ : syracuseStep 1604587 = 2406881) B2406881
theorem B3210227 : Blo 1425532 3210227 := bstep (se 1 (by rfl) ⟨2407670, by rfl⟩ : syracuseStep 3210227 = 4815341) B4815341
theorem B3046423 : Blo 1425532 3046423 := bstep (se 1 (by rfl) ⟨2284817, by rfl⟩ : syracuseStep 3046423 = 4569635) B4569635
theorem B3210263 : Blo 1425532 3210263 := bstep (se 1 (by rfl) ⟨2407697, by rfl⟩ : syracuseStep 3210263 = 4815395) B4815395
theorem B3611699 : Blo 1425532 3611699 := bstep (se 1 (by rfl) ⟨2708774, by rfl⟩ : syracuseStep 3611699 = 5417549) B5417549
theorem B1604695 : Blo 1425532 1604695 := bstep (se 1 (by rfl) ⟨1203521, by rfl⟩ : syracuseStep 1604695 = 2407043) B2407043
theorem B12344471 : Blo 1425532 12344471 := bstep (se 1 (by rfl) ⟨9258353, by rfl⟩ : syracuseStep 12344471 = 18516707) B18516707
theorem B3210443 : Blo 1425532 3210443 := bstep (se 1 (by rfl) ⟨2407832, by rfl⟩ : syracuseStep 3210443 = 4815665) B4815665
theorem B3210497 : Blo 1425532 3210497 := bstep (se 2 (by rfl) ⟨1203936, by rfl⟩ : syracuseStep 3210497 = 2407873) B2407873
theorem B5414147 : Blo 1425532 5414147 := bstep (se 1 (by rfl) ⟨4060610, by rfl⟩ : syracuseStep 5414147 = 8121221) B8121221
theorem B1604875 : Blo 1425532 1604875 := bstep (se 1 (by rfl) ⟨1203656, by rfl⟩ : syracuseStep 1604875 = 2407313) B2407313
theorem B2407691 : Blo 1425532 2407691 := bstep (se 1 (by rfl) ⟨1805768, by rfl⟩ : syracuseStep 2407691 = 3611537) B3611537
theorem B5414161 : Blo 1425532 5414161 := bstep (se 2 (by rfl) ⟨2030310, by rfl⟩ : syracuseStep 5414161 = 4060621) B4060621
theorem B4816151 : Blo 1425532 4816151 := bstep (se 1 (by rfl) ⟨3612113, by rfl⟩ : syracuseStep 4816151 = 7224227) B7224227
theorem B10837313 : Blo 1425532 10837313 := bstep (se 2 (by rfl) ⟨4063992, by rfl⟩ : syracuseStep 10837313 = 8127985) B8127985
theorem B10280267 : Blo 1425532 10280267 := bstep (se 1 (by rfl) ⟨7710200, by rfl⟩ : syracuseStep 10280267 = 15420401) B15420401
theorem B1506647 : Blo 1425532 1506647 := bstep (se 1 (by rfl) ⟨1129985, by rfl⟩ : syracuseStep 1506647 = 2259971) B2259971
theorem B1604983 : Blo 1425532 1604983 := bstep (se 1 (by rfl) ⟨1203737, by rfl⟩ : syracuseStep 1604983 = 2407475) B2407475
theorem B2407819 : Blo 1425532 2407819 := bstep (se 1 (by rfl) ⟨1805864, by rfl⟩ : syracuseStep 2407819 = 3611729) B3611729
theorem B3210713 : Blo 1425532 3210713 := bstep (se 2 (by rfl) ⟨1204017, by rfl⟩ : syracuseStep 3210713 = 2408035) B2408035
theorem B2743831 : Blo 1425532 2743831 := bstep (se 1 (by rfl) ⟨2057873, by rfl⟩ : syracuseStep 2743831 = 4115747) B4115747
theorem B2407961 : Blo 1425532 2407961 := bstep (se 2 (by rfl) ⟨902985, by rfl⟩ : syracuseStep 2407961 = 1805971) B1805971
theorem B1605163 : Blo 1425532 1605163 := bstep (se 1 (by rfl) ⟨1203872, by rfl⟩ : syracuseStep 1605163 = 2407745) B2407745
theorem B3210803 : Blo 1425532 3210803 := bstep (se 1 (by rfl) ⟨2408102, by rfl⟩ : syracuseStep 3210803 = 4816205) B4816205
theorem B5414465 : Blo 1425532 5414465 := bstep (se 2 (by rfl) ⟨2030424, by rfl⟩ : syracuseStep 5414465 = 4060849) B4060849
theorem B3046987 : Blo 1425532 3046987 := bstep (se 1 (by rfl) ⟨2285240, by rfl⟩ : syracuseStep 3046987 = 4570481) B4570481
theorem B8126027 : Blo 1425532 8126027 := bstep (se 1 (by rfl) ⟨6094520, by rfl⟩ : syracuseStep 8126027 = 12189041) B12189041
theorem B3612235 : Blo 1425532 3612235 := bstep (se 1 (by rfl) ⟨2709176, by rfl⟩ : syracuseStep 3612235 = 5418353) B5418353
theorem B3210839 : Blo 1425532 3210839 := bstep (se 1 (by rfl) ⟨2408129, by rfl⟩ : syracuseStep 3210839 = 4816259) B4816259
theorem B1605271 : Blo 1425532 1605271 := bstep (se 1 (by rfl) ⟨1203953, by rfl⟩ : syracuseStep 1605271 = 2407907) B2407907
theorem B2408089 : Blo 1425532 2408089 := bstep (se 2 (by rfl) ⟨903033, by rfl⟩ : syracuseStep 2408089 = 1806067) B1806067
theorem B4062899 : Blo 1425532 4062899 := bstep (se 1 (by rfl) ⟨3047174, by rfl⟩ : syracuseStep 4062899 = 6094349) B6094349
theorem B4062923 : Blo 1425532 4062923 := bstep (se 1 (by rfl) ⟨3047192, by rfl⟩ : syracuseStep 4062923 = 6094385) B6094385
theorem B2285273 : Blo 1425532 2285273 := bstep (se 2 (by rfl) ⟨856977, by rfl⟩ : syracuseStep 2285273 = 1713955) B1713955
theorem B3612377 : Blo 1425532 3612377 := bstep (se 2 (by rfl) ⟨1354641, by rfl⟩ : syracuseStep 3612377 = 2709283) B2709283
theorem B13016837 : Blo 1425532 13016837 := bstep (se 4 (by rfl) ⟨1220328, by rfl⟩ : syracuseStep 13016837 = 2440657) B2440657
theorem B3211019 : Blo 1425532 3211019 := bstep (se 1 (by rfl) ⟨2408264, by rfl⟩ : syracuseStep 3211019 = 4816529) B4816529
theorem B4816691 : Blo 1425532 4816691 := bstep (se 1 (by rfl) ⟨3612518, by rfl⟩ : syracuseStep 4816691 = 7225037) B7225037
theorem B3211073 : Blo 1425532 3211073 := bstep (se 2 (by rfl) ⟨1204152, by rfl⟩ : syracuseStep 3211073 = 2408305) B2408305
theorem B1605451 : Blo 1425532 1605451 := bstep (se 1 (by rfl) ⟨1204088, by rfl⟩ : syracuseStep 1605451 = 2408177) B2408177
theorem B30850915 : Blo 1425532 30850915 := bstep (se 1 (by rfl) ⟨23138186, by rfl⟩ : syracuseStep 30850915 = 46276373) B46276373
theorem B1605559 : Blo 1425532 1605559 := bstep (se 1 (by rfl) ⟨1204169, by rfl⟩ : syracuseStep 1605559 = 2408339) B2408339
theorem B4816907 : Blo 1425532 4816907 := bstep (se 1 (by rfl) ⟨3612680, by rfl⟩ : syracuseStep 4816907 = 7225361) B7225361
theorem B3211307 : Blo 1425532 3211307 := bstep (se 1 (by rfl) ⟨2408480, by rfl⟩ : syracuseStep 3211307 = 4816961) B4816961
theorem B3047483 : Blo 1425532 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B2031689 : Blo 1425532 2031689 := bstep (se 2 (by rfl) ⟨761883, by rfl⟩ : syracuseStep 2031689 = 1523767) B1523767
theorem B4817015 : Blo 1425532 4817015 := bstep (se 1 (by rfl) ⟨3612761, by rfl⟩ : syracuseStep 4817015 = 7225523) B7225523
theorem B1425543 : Blo 1425532 1425543 := bstep (se 1 (by rfl) ⟨1069157, by rfl⟩ : syracuseStep 1425543 = 2138315) B2138315
theorem B1425551 : Blo 1425532 1425551 := bstep (se 1 (by rfl) ⟨1069163, by rfl⟩ : syracuseStep 1425551 = 2138327) B2138327
theorem B1605775 : Blo 1425532 1605775 := bstep (se 1 (by rfl) ⟨1204331, by rfl⟩ : syracuseStep 1605775 = 2408663) B2408663
theorem B15433901 : Blo 1425532 15433901 := bstep (se 3 (by rfl) ⟨2893856, by rfl⟩ : syracuseStep 15433901 = 5787713) B5787713
theorem B1425595 : Blo 1425532 1425595 := bstep (se 1 (by rfl) ⟨1069196, by rfl⟩ : syracuseStep 1425595 = 2138393) B2138393
theorem B2138375 : Blo 1425532 2138375 := bstep (se 1 (by rfl) ⟨1603781, by rfl⟩ : syracuseStep 2138375 = 3207563) B3207563
theorem B1425671 : Blo 1425532 1425671 := bstep (se 1 (by rfl) ⟨1069253, by rfl⟩ : syracuseStep 1425671 = 2138507) B2138507
theorem B7217423 : Blo 1425532 7217423 := bstep (se 1 (by rfl) ⟨5413067, by rfl⟩ : syracuseStep 7217423 = 10826135) B10826135
theorem B1425679 : Blo 1425532 1425679 := bstep (se 1 (by rfl) ⟨1069259, by rfl⟩ : syracuseStep 1425679 = 2138519) B2138519
theorem B2138411 : Blo 1425532 2138411 := bstep (se 1 (by rfl) ⟨1603808, by rfl⟩ : syracuseStep 2138411 = 3207617) B3207617
theorem B1425723 : Blo 1425532 1425723 := bstep (se 1 (by rfl) ⟨1069292, by rfl⟩ : syracuseStep 1425723 = 2138585) B2138585
theorem B33407297 : Blo 1425532 33407297 := bstep (se 2 (by rfl) ⟨12527736, by rfl⟩ : syracuseStep 33407297 = 25055473) B25055473
theorem B2138441 : Blo 1425532 2138441 := bstep (se 2 (by rfl) ⟨801915, by rfl⟩ : syracuseStep 2138441 = 1603831) B1603831
theorem B1425799 : Blo 1425532 1425799 := bstep (se 1 (by rfl) ⟨1069349, by rfl⟩ : syracuseStep 1425799 = 2138699) B2138699
theorem B1425807 : Blo 1425532 1425807 := bstep (se 1 (by rfl) ⟨1069355, by rfl⟩ : syracuseStep 1425807 = 2138711) B2138711
theorem B3211667 : Blo 1425532 3211667 := bstep (se 1 (by rfl) ⟨2408750, by rfl⟩ : syracuseStep 3211667 = 4817501) B4817501
theorem B2138555 : Blo 1425532 2138555 := bstep (se 1 (by rfl) ⟨1603916, by rfl⟩ : syracuseStep 2138555 = 3207833) B3207833
theorem B1425851 : Blo 1425532 1425851 := bstep (se 1 (by rfl) ⟨1069388, by rfl⟩ : syracuseStep 1425851 = 2138777) B2138777
theorem B3211721 : Blo 1425532 3211721 := bstep (se 2 (by rfl) ⟨1204395, by rfl⟩ : syracuseStep 3211721 = 2408791) B2408791
theorem B12345821 : Blo 1425532 12345821 := bstep (se 3 (by rfl) ⟨2314841, by rfl⟩ : syracuseStep 12345821 = 4629683) B4629683
theorem B11887069 : Blo 1425532 11887069 := bstep (se 3 (by rfl) ⟨2228825, by rfl⟩ : syracuseStep 11887069 = 4457651) B4457651
theorem B2138615 : Blo 1425532 2138615 := bstep (se 1 (by rfl) ⟨1603961, by rfl⟩ : syracuseStep 2138615 = 3207923) B3207923
theorem B1425927 : Blo 1425532 1425927 := bstep (se 1 (by rfl) ⟨1069445, by rfl⟩ : syracuseStep 1425927 = 2138891) B2138891
theorem B2138639 : Blo 1425532 2138639 := bstep (se 1 (by rfl) ⟨1603979, by rfl⟩ : syracuseStep 2138639 = 3207959) B3207959
theorem B1425935 : Blo 1425532 1425935 := bstep (se 1 (by rfl) ⟨1069451, by rfl⟩ : syracuseStep 1425935 = 2138903) B2138903
theorem B2138681 : Blo 1425532 2138681 := bstep (se 2 (by rfl) ⟨802005, by rfl⟩ : syracuseStep 2138681 = 1604011) B1604011
theorem B1425979 : Blo 1425532 1425979 := bstep (se 1 (by rfl) ⟨1069484, by rfl⟩ : syracuseStep 1425979 = 2138969) B2138969
theorem B13705793 : Blo 1425532 13705793 := bstep (se 2 (by rfl) ⟨5139672, by rfl⟩ : syracuseStep 13705793 = 10279345) B10279345
theorem B2032247 : Blo 1425532 2032247 := bstep (se 1 (by rfl) ⟨1524185, by rfl⟩ : syracuseStep 2032247 = 3048371) B3048371
theorem B2138759 : Blo 1425532 2138759 := bstep (se 1 (by rfl) ⟨1604069, by rfl⟩ : syracuseStep 2138759 = 3208139) B3208139
theorem B1426055 : Blo 1425532 1426055 := bstep (se 1 (by rfl) ⟨1069541, by rfl⟩ : syracuseStep 1426055 = 2139083) B2139083
theorem B2286215 : Blo 1425532 2286215 := bstep (se 1 (by rfl) ⟨1714661, by rfl⟩ : syracuseStep 2286215 = 3429323) B3429323
theorem B3613319 : Blo 1425532 3613319 := bstep (se 1 (by rfl) ⟨2709989, by rfl⟩ : syracuseStep 3613319 = 5419979) B5419979
theorem B1426063 : Blo 1425532 1426063 := bstep (se 1 (by rfl) ⟨1069547, by rfl⟩ : syracuseStep 1426063 = 2139095) B2139095
theorem B4063891 : Blo 1425532 4063891 := bstep (se 1 (by rfl) ⟨3047918, by rfl⟩ : syracuseStep 4063891 = 6095837) B6095837
theorem B2138795 : Blo 1425532 2138795 := bstep (se 1 (by rfl) ⟨1604096, by rfl⟩ : syracuseStep 2138795 = 3208193) B3208193
theorem B3613369 : Blo 1425532 3613369 := bstep (se 2 (by rfl) ⟨1355013, by rfl⟩ : syracuseStep 3613369 = 2710027) B2710027
theorem B1426107 : Blo 1425532 1426107 := bstep (se 1 (by rfl) ⟨1069580, by rfl⟩ : syracuseStep 1426107 = 2139161) B2139161
theorem B2138825 : Blo 1425532 2138825 := bstep (se 2 (by rfl) ⟨802059, by rfl⟩ : syracuseStep 2138825 = 1604119) B1604119
theorem B4817609 : Blo 1425532 4817609 := bstep (se 2 (by rfl) ⟨1806603, by rfl⟩ : syracuseStep 4817609 = 3613207) B3613207
theorem B1426183 : Blo 1425532 1426183 := bstep (se 1 (by rfl) ⟨1069637, by rfl⟩ : syracuseStep 1426183 = 2139275) B2139275
theorem B8119055 : Blo 1425532 8119055 := bstep (se 1 (by rfl) ⟨6089291, by rfl⟩ : syracuseStep 8119055 = 12178583) B12178583
theorem B1426191 : Blo 1425532 1426191 := bstep (se 1 (by rfl) ⟨1069643, by rfl⟩ : syracuseStep 1426191 = 2139287) B2139287
theorem B2138939 : Blo 1425532 2138939 := bstep (se 1 (by rfl) ⟨1604204, by rfl⟩ : syracuseStep 2138939 = 3208409) B3208409
theorem B1426235 : Blo 1425532 1426235 := bstep (se 1 (by rfl) ⟨1069676, by rfl⟩ : syracuseStep 1426235 = 2139353) B2139353
theorem B7226171 : Blo 1425532 7226171 := bstep (se 1 (by rfl) ⟨5419628, by rfl⟩ : syracuseStep 7226171 = 10839257) B10839257
theorem B10421081 : Blo 1425532 10421081 := bstep (se 2 (by rfl) ⟨3907905, by rfl⟩ : syracuseStep 10421081 = 7815811) B7815811
theorem B13190003 : Blo 1425532 13190003 := bstep (se 1 (by rfl) ⟨9892502, by rfl⟩ : syracuseStep 13190003 = 19785005) B19785005
theorem B9134963 : Blo 1425532 9134963 := bstep (se 1 (by rfl) ⟨6851222, by rfl⟩ : syracuseStep 9134963 = 13702445) B13702445
theorem B2138999 : Blo 1425532 2138999 := bstep (se 1 (by rfl) ⟨1604249, by rfl⟩ : syracuseStep 2138999 = 3208499) B3208499
theorem B1426311 : Blo 1425532 1426311 := bstep (se 1 (by rfl) ⟨1069733, by rfl⟩ : syracuseStep 1426311 = 2139467) B2139467
theorem B2139023 : Blo 1425532 2139023 := bstep (se 1 (by rfl) ⟨1604267, by rfl⟩ : syracuseStep 2139023 = 3208535) B3208535
theorem B1426319 : Blo 1425532 1426319 := bstep (se 1 (by rfl) ⟨1069739, by rfl⟩ : syracuseStep 1426319 = 2139479) B2139479
theorem B13706135 : Blo 1425532 13706135 := bstep (se 1 (by rfl) ⟨10279601, by rfl⟩ : syracuseStep 13706135 = 20559203) B20559203
theorem B2032555 : Blo 1425532 2032555 := bstep (se 1 (by rfl) ⟨1524416, by rfl⟩ : syracuseStep 2032555 = 3048833) B3048833
theorem B2139065 : Blo 1425532 2139065 := bstep (se 2 (by rfl) ⟨802149, by rfl⟩ : syracuseStep 2139065 = 1604299) B1604299
theorem B1426363 : Blo 1425532 1426363 := bstep (se 1 (by rfl) ⟨1069772, by rfl⟩ : syracuseStep 1426363 = 2139545) B2139545
theorem B7226333 : Blo 1425532 7226333 := bstep (se 3 (by rfl) ⟨1354937, by rfl⟩ : syracuseStep 7226333 = 2709875) B2709875
theorem B2139143 : Blo 1425532 2139143 := bstep (se 1 (by rfl) ⟨1604357, by rfl⟩ : syracuseStep 2139143 = 3208715) B3208715
theorem B1426439 : Blo 1425532 1426439 := bstep (se 1 (by rfl) ⟨1069829, by rfl⟩ : syracuseStep 1426439 = 2139659) B2139659
theorem B1426447 : Blo 1425532 1426447 := bstep (se 1 (by rfl) ⟨1069835, by rfl⟩ : syracuseStep 1426447 = 2139671) B2139671
theorem B2139179 : Blo 1425532 2139179 := bstep (se 1 (by rfl) ⟨1604384, by rfl⟩ : syracuseStep 2139179 = 3208769) B3208769
theorem B3048491 : Blo 1425532 3048491 := bstep (se 1 (by rfl) ⟨2286368, by rfl⟩ : syracuseStep 3048491 = 4572737) B4572737
theorem B1426491 : Blo 1425532 1426491 := bstep (se 1 (by rfl) ⟨1069868, by rfl⟩ : syracuseStep 1426491 = 2139737) B2139737
theorem B2139209 : Blo 1425532 2139209 := bstep (se 2 (by rfl) ⟨802203, by rfl⟩ : syracuseStep 2139209 = 1604407) B1604407
theorem B1426567 : Blo 1425532 1426567 := bstep (se 1 (by rfl) ⟨1069925, by rfl⟩ : syracuseStep 1426567 = 2139851) B2139851
theorem B1426575 : Blo 1425532 1426575 := bstep (se 1 (by rfl) ⟨1069931, by rfl⟩ : syracuseStep 1426575 = 2139863) B2139863
theorem B2139323 : Blo 1425532 2139323 := bstep (se 1 (by rfl) ⟨1604492, by rfl⟩ : syracuseStep 2139323 = 3208985) B3208985
theorem B1426619 : Blo 1425532 1426619 := bstep (se 1 (by rfl) ⟨1069964, by rfl⟩ : syracuseStep 1426619 = 2139929) B2139929
theorem B2139383 : Blo 1425532 2139383 := bstep (se 1 (by rfl) ⟨1604537, by rfl⟩ : syracuseStep 2139383 = 3209075) B3209075
theorem B1426695 : Blo 1425532 1426695 := bstep (se 1 (by rfl) ⟨1070021, by rfl⟩ : syracuseStep 1426695 = 2140043) B2140043
theorem B2139407 : Blo 1425532 2139407 := bstep (se 1 (by rfl) ⟨1604555, by rfl⟩ : syracuseStep 2139407 = 3209111) B3209111
theorem B1426703 : Blo 1425532 1426703 := bstep (se 1 (by rfl) ⟨1070027, by rfl⟩ : syracuseStep 1426703 = 2140055) B2140055
theorem B6096161 : Blo 1425532 6096161 := bstep (se 2 (by rfl) ⟨2286060, by rfl⟩ : syracuseStep 6096161 = 4572121) B4572121
theorem B7226657 : Blo 1425532 7226657 := bstep (se 2 (by rfl) ⟨2709996, by rfl⟩ : syracuseStep 7226657 = 5419993) B5419993
theorem B2139449 : Blo 1425532 2139449 := bstep (se 2 (by rfl) ⟨802293, by rfl⟩ : syracuseStep 2139449 = 1604587) B1604587
theorem B1426747 : Blo 1425532 1426747 := bstep (se 1 (by rfl) ⟨1070060, by rfl⟩ : syracuseStep 1426747 = 2140121) B2140121
theorem B8127803 : Blo 1425532 8127803 := bstep (se 1 (by rfl) ⟨6095852, by rfl⟩ : syracuseStep 8127803 = 12191705) B12191705
theorem B32949605 : Blo 1425532 32949605 := bstep (se 4 (by rfl) ⟨3089025, by rfl⟩ : syracuseStep 32949605 = 6178051) B6178051
theorem B2139527 : Blo 1425532 2139527 := bstep (se 1 (by rfl) ⟨1604645, by rfl⟩ : syracuseStep 2139527 = 3209291) B3209291
theorem B1426823 : Blo 1425532 1426823 := bstep (se 1 (by rfl) ⟨1070117, by rfl⟩ : syracuseStep 1426823 = 2140235) B2140235
theorem B1426831 : Blo 1425532 1426831 := bstep (se 1 (by rfl) ⟨1070123, by rfl⟩ : syracuseStep 1426831 = 2140247) B2140247
theorem B2139563 : Blo 1425532 2139563 := bstep (se 1 (by rfl) ⟨1604672, by rfl⟩ : syracuseStep 2139563 = 3209345) B3209345
theorem B1426875 : Blo 1425532 1426875 := bstep (se 1 (by rfl) ⟨1070156, by rfl⟩ : syracuseStep 1426875 = 2140313) B2140313
theorem B2139593 : Blo 1425532 2139593 := bstep (se 2 (by rfl) ⟨802347, by rfl⟩ : syracuseStep 2139593 = 1604695) B1604695
theorem B1426951 : Blo 1425532 1426951 := bstep (se 1 (by rfl) ⟨1070213, by rfl⟩ : syracuseStep 1426951 = 2140427) B2140427
theorem B1426959 : Blo 1425532 1426959 := bstep (se 1 (by rfl) ⟨1070219, by rfl⟩ : syracuseStep 1426959 = 2140439) B2140439
theorem B2139707 : Blo 1425532 2139707 := bstep (se 1 (by rfl) ⟨1604780, by rfl⟩ : syracuseStep 2139707 = 3209561) B3209561
theorem B1427003 : Blo 1425532 1427003 := bstep (se 1 (by rfl) ⟨1070252, by rfl⟩ : syracuseStep 1427003 = 2140505) B2140505
theorem B2139767 : Blo 1425532 2139767 := bstep (se 1 (by rfl) ⟨1604825, by rfl⟩ : syracuseStep 2139767 = 3209651) B3209651
theorem B1427079 : Blo 1425532 1427079 := bstep (se 1 (by rfl) ⟨1070309, by rfl⟩ : syracuseStep 1427079 = 2140619) B2140619
theorem B2139791 : Blo 1425532 2139791 := bstep (se 1 (by rfl) ⟨1604843, by rfl⟩ : syracuseStep 2139791 = 3209687) B3209687
theorem B1427087 : Blo 1425532 1427087 := bstep (se 1 (by rfl) ⟨1070315, by rfl⟩ : syracuseStep 1427087 = 2140631) B2140631
theorem B24692401 : Blo 1425532 24692401 := bstep (se 2 (by rfl) ⟨9259650, by rfl⟩ : syracuseStep 24692401 = 18519301) B18519301
theorem B2139833 : Blo 1425532 2139833 := bstep (se 2 (by rfl) ⟨802437, by rfl⟩ : syracuseStep 2139833 = 1604875) B1604875
theorem B1427131 : Blo 1425532 1427131 := bstep (se 1 (by rfl) ⟨1070348, by rfl⟩ : syracuseStep 1427131 = 2140697) B2140697
theorem B7218881 : Blo 1425532 7218881 := bstep (se 2 (by rfl) ⟨2707080, by rfl⟩ : syracuseStep 7218881 = 5414161) B5414161
theorem B29280001 : Blo 1425532 29280001 := bstep (se 2 (by rfl) ⟨10980000, by rfl⟩ : syracuseStep 29280001 = 21960001) B21960001
theorem B2139911 : Blo 1425532 2139911 := bstep (se 1 (by rfl) ⟨1604933, by rfl⟩ : syracuseStep 2139911 = 3209867) B3209867
theorem B1427207 : Blo 1425532 1427207 := bstep (se 1 (by rfl) ⟨1070405, by rfl⟩ : syracuseStep 1427207 = 2140811) B2140811
theorem B1427215 : Blo 1425532 1427215 := bstep (se 1 (by rfl) ⟨1070411, by rfl⟩ : syracuseStep 1427215 = 2140823) B2140823
theorem B2139947 : Blo 1425532 2139947 := bstep (se 1 (by rfl) ⟨1604960, by rfl⟩ : syracuseStep 2139947 = 3209921) B3209921
theorem B1427259 : Blo 1425532 1427259 := bstep (se 1 (by rfl) ⟨1070444, by rfl⟩ : syracuseStep 1427259 = 2140889) B2140889
theorem B2139977 : Blo 1425532 2139977 := bstep (se 2 (by rfl) ⟨802491, by rfl⟩ : syracuseStep 2139977 = 1604983) B1604983
theorem B1427335 : Blo 1425532 1427335 := bstep (se 1 (by rfl) ⟨1070501, by rfl⟩ : syracuseStep 1427335 = 2141003) B2141003
theorem B1427343 : Blo 1425532 1427343 := bstep (se 1 (by rfl) ⟨1070507, by rfl⟩ : syracuseStep 1427343 = 2141015) B2141015
theorem B2140091 : Blo 1425532 2140091 := bstep (se 1 (by rfl) ⟨1605068, by rfl⟩ : syracuseStep 2140091 = 3210137) B3210137
theorem B1427387 : Blo 1425532 1427387 := bstep (se 1 (by rfl) ⟨1070540, by rfl⟩ : syracuseStep 1427387 = 2141081) B2141081
theorem B2140151 : Blo 1425532 2140151 := bstep (se 1 (by rfl) ⟨1605113, by rfl⟩ : syracuseStep 2140151 = 3210227) B3210227
theorem B7817219 : Blo 1425532 7817219 := bstep (se 1 (by rfl) ⟨5862914, by rfl⟩ : syracuseStep 7817219 = 11725829) B11725829
theorem B1804295 : Blo 1425532 1804295 := bstep (se 1 (by rfl) ⟨1353221, by rfl⟩ : syracuseStep 1804295 = 2706443) B2706443
theorem B1427463 : Blo 1425532 1427463 := bstep (se 1 (by rfl) ⟨1070597, by rfl⟩ : syracuseStep 1427463 = 2141195) B2141195
theorem B2140175 : Blo 1425532 2140175 := bstep (se 1 (by rfl) ⟨1605131, by rfl⟩ : syracuseStep 2140175 = 3210263) B3210263
theorem B1427471 : Blo 1425532 1427471 := bstep (se 1 (by rfl) ⟨1070603, by rfl⟩ : syracuseStep 1427471 = 2141207) B2141207
theorem B2140217 : Blo 1425532 2140217 := bstep (se 2 (by rfl) ⟨802581, by rfl⟩ : syracuseStep 2140217 = 1605163) B1605163
theorem B1427515 : Blo 1425532 1427515 := bstep (se 1 (by rfl) ⟨1070636, by rfl⟩ : syracuseStep 1427515 = 2141273) B2141273
theorem B2140295 : Blo 1425532 2140295 := bstep (se 1 (by rfl) ⟨1605221, by rfl⟩ : syracuseStep 2140295 = 3210443) B3210443
theorem B3426457 : Blo 1425532 3426457 := bstep (se 2 (by rfl) ⟨1284921, by rfl⟩ : syracuseStep 3426457 = 2569843) B2569843
theorem B2140331 : Blo 1425532 2140331 := bstep (se 1 (by rfl) ⟨1605248, by rfl⟩ : syracuseStep 2140331 = 3210497) B3210497
theorem B8120513 : Blo 1425532 8120513 := bstep (se 2 (by rfl) ⟨3045192, by rfl⟩ : syracuseStep 8120513 = 6090385) B6090385
theorem B2140361 : Blo 1425532 2140361 := bstep (se 2 (by rfl) ⟨802635, by rfl⟩ : syracuseStep 2140361 = 1605271) B1605271
theorem B2140475 : Blo 1425532 2140475 := bstep (se 1 (by rfl) ⟨1605356, by rfl⟩ : syracuseStep 2140475 = 3210713) B3210713
theorem B2140535 : Blo 1425532 2140535 := bstep (se 1 (by rfl) ⟨1605401, by rfl⟩ : syracuseStep 2140535 = 3210803) B3210803
theorem B5417351 : Blo 1425532 5417351 := bstep (se 1 (by rfl) ⟨4063013, by rfl⟩ : syracuseStep 5417351 = 8126027) B8126027
theorem B2140559 : Blo 1425532 2140559 := bstep (se 1 (by rfl) ⟨1605419, by rfl⟩ : syracuseStep 2140559 = 3210839) B3210839
theorem B2140601 : Blo 1425532 2140601 := bstep (se 2 (by rfl) ⟨802725, by rfl⟩ : syracuseStep 2140601 = 1605451) B1605451
theorem B41134553 : Blo 1425532 41134553 := bstep (se 2 (by rfl) ⟨15425457, by rfl⟩ : syracuseStep 41134553 = 30850915) B30850915
theorem B8677891 : Blo 1425532 8677891 := bstep (se 1 (by rfl) ⟨6508418, by rfl⟩ : syracuseStep 8677891 = 13016837) B13016837
theorem B2140679 : Blo 1425532 2140679 := bstep (se 1 (by rfl) ⟨1605509, by rfl⟩ : syracuseStep 2140679 = 3211019) B3211019
theorem B18287147 : Blo 1425532 18287147 := bstep (se 1 (by rfl) ⟨13715360, by rfl⟩ : syracuseStep 18287147 = 27430721) B27430721
theorem B2140715 : Blo 1425532 2140715 := bstep (se 1 (by rfl) ⟨1605536, by rfl⟩ : syracuseStep 2140715 = 3211073) B3211073
theorem B2140745 : Blo 1425532 2140745 := bstep (se 2 (by rfl) ⟨802779, by rfl⟩ : syracuseStep 2140745 = 1605559) B1605559
theorem B1804943 : Blo 1425532 1804943 := bstep (se 1 (by rfl) ⟨1353707, by rfl⟩ : syracuseStep 1804943 = 2707415) B2707415
theorem B2140859 : Blo 1425532 2140859 := bstep (se 1 (by rfl) ⟨1605644, by rfl⟩ : syracuseStep 2140859 = 3211289) B3211289
theorem B8129261 : Blo 1425532 8129261 := bstep (se 3 (by rfl) ⟨1524236, by rfl⟩ : syracuseStep 8129261 = 3048473) B3048473
theorem B2140919 : Blo 1425532 2140919 := bstep (se 1 (by rfl) ⟨1605689, by rfl⟩ : syracuseStep 2140919 = 3211379) B3211379
theorem B3427073 : Blo 1425532 3427073 := bstep (se 2 (by rfl) ⟨1285152, by rfl⟩ : syracuseStep 3427073 = 2570305) B2570305
theorem B2140943 : Blo 1425532 2140943 := bstep (se 1 (by rfl) ⟨1605707, by rfl⟩ : syracuseStep 2140943 = 3211415) B3211415
theorem B2140985 : Blo 1425532 2140985 := bstep (se 2 (by rfl) ⟨802869, by rfl⟩ : syracuseStep 2140985 = 1605739) B1605739
theorem B32942963 : Blo 1425532 32942963 := bstep (se 1 (by rfl) ⟨24707222, by rfl⟩ : syracuseStep 32942963 = 49414445) B49414445
theorem B2141063 : Blo 1425532 2141063 := bstep (se 1 (by rfl) ⟨1605797, by rfl⟩ : syracuseStep 2141063 = 3211595) B3211595
theorem B11733913 : Blo 1425532 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B2141099 : Blo 1425532 2141099 := bstep (se 1 (by rfl) ⟨1605824, by rfl⟩ : syracuseStep 2141099 = 3211649) B3211649
theorem B2141129 : Blo 1425532 2141129 := bstep (se 2 (by rfl) ⟨802923, by rfl⟩ : syracuseStep 2141129 = 1605847) B1605847
theorem B7220177 : Blo 1425532 7220177 := bstep (se 2 (by rfl) ⟨2707566, by rfl⟩ : syracuseStep 7220177 = 5415133) B5415133
theorem B2141243 : Blo 1425532 2141243 := bstep (se 1 (by rfl) ⟨1605932, by rfl⟩ : syracuseStep 2141243 = 3211865) B3211865
theorem B1928377 : Blo 1425532 1928377 := bstep (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) B1446283
theorem B4812047 : Blo 1425532 4812047 := bstep (se 1 (by rfl) ⟨3609035, by rfl⟩ : syracuseStep 4812047 = 7218071) B7218071
theorem B3853597 : Blo 1425532 3853597 := bstep (se 3 (by rfl) ⟨722549, by rfl⟩ : syracuseStep 3853597 = 1445099) B1445099
theorem B1928507 : Blo 1425532 1928507 := bstep (se 1 (by rfl) ⟨1446380, by rfl⟩ : syracuseStep 1928507 = 2892761) B2892761
theorem B5787065 : Blo 1425532 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B2706959 : Blo 1425532 2706959 := bstep (se 1 (by rfl) ⟨2030219, by rfl⟩ : syracuseStep 2706959 = 4060439) B4060439
theorem B7712279 : Blo 1425532 7712279 := bstep (se 1 (by rfl) ⟨5784209, by rfl⟩ : syracuseStep 7712279 = 11568419) B11568419
theorem B4812317 : Blo 1425532 4812317 := bstep (se 3 (by rfl) ⟨902309, by rfl⟩ : syracuseStep 4812317 = 1804619) B1804619
theorem B4017725 : Blo 1425532 4017725 := bstep (se 3 (by rfl) ⟨753323, by rfl⟩ : syracuseStep 4017725 = 1506647) B1506647
theorem B9137731 : Blo 1425532 9137731 := bstep (se 1 (by rfl) ⟨6853298, by rfl⟩ : syracuseStep 9137731 = 13706597) B13706597
theorem B1928875 : Blo 1425532 1928875 := bstep (se 1 (by rfl) ⟨1446656, by rfl⟩ : syracuseStep 1928875 = 2893313) B2893313
theorem B4878139 : Blo 1425532 4878139 := bstep (se 1 (by rfl) ⟨3658604, by rfl⟩ : syracuseStep 4878139 = 7317209) B7317209
theorem B15429527 : Blo 1425532 15429527 := bstep (se 1 (by rfl) ⟨11572145, by rfl⟩ : syracuseStep 15429527 = 23144291) B23144291
theorem B2707499 : Blo 1425532 2707499 := bstep (se 1 (by rfl) ⟨2030624, by rfl⟩ : syracuseStep 2707499 = 4061249) B4061249
theorem B3608833 : Blo 1425532 3608833 := bstep (se 2 (by rfl) ⟨1353312, by rfl⟩ : syracuseStep 3608833 = 2706625) B2706625
theorem B9040187 : Blo 1425532 9040187 := bstep (se 1 (by rfl) ⟨6780140, by rfl⟩ : syracuseStep 9040187 = 13560281) B13560281
theorem B9138653 : Blo 1425532 9138653 := bstep (se 3 (by rfl) ⟨1713497, by rfl⟩ : syracuseStep 9138653 = 3426995) B3426995
theorem B10834397 : Blo 1425532 10834397 := bstep (se 3 (by rfl) ⟨2031449, by rfl⟩ : syracuseStep 10834397 = 4062899) B4062899
theorem B16249409 : Blo 1425532 16249409 := bstep (se 2 (by rfl) ⟨6093528, by rfl⟩ : syracuseStep 16249409 = 12187057) B12187057
theorem B3207815 : Blo 1425532 3207815 := bstep (se 1 (by rfl) ⟨2405861, by rfl⟩ : syracuseStep 3207815 = 4811723) B4811723
theorem B3658441 : Blo 1425532 3658441 := bstep (se 2 (by rfl) ⟨1371915, by rfl⟩ : syracuseStep 3658441 = 2743831) B2743831
theorem B8229647 : Blo 1425532 8229647 := bstep (se 1 (by rfl) ⟨6172235, by rfl⟩ : syracuseStep 8229647 = 12344471) B12344471
theorem B3207995 : Blo 1425532 3207995 := bstep (se 1 (by rfl) ⟨2405996, by rfl⟩ : syracuseStep 3207995 = 4811993) B4811993
theorem B2167625 : Blo 1425532 2167625 := bstep (se 2 (by rfl) ⟨812859, by rfl⟩ : syracuseStep 2167625 = 1625719) B1625719
theorem B3609431 : Blo 1425532 3609431 := bstep (se 1 (by rfl) ⟨2707073, by rfl⟩ : syracuseStep 3609431 = 5414147) B5414147
theorem B6853511 : Blo 1425532 6853511 := bstep (se 1 (by rfl) ⟨5140133, by rfl⟩ : syracuseStep 6853511 = 10280267) B10280267
theorem B4813721 : Blo 1425532 4813721 := bstep (se 2 (by rfl) ⟨1805145, by rfl⟩ : syracuseStep 4813721 = 3610291) B3610291
theorem B3208121 : Blo 1425532 3208121 := bstep (se 2 (by rfl) ⟨1203045, by rfl⟩ : syracuseStep 3208121 = 2406091) B2406091
theorem B3707849 : Blo 1425532 3707849 := bstep (se 2 (by rfl) ⟨1390443, by rfl⟩ : syracuseStep 3707849 = 2780887) B2780887
theorem B6091787 : Blo 1425532 6091787 := bstep (se 1 (by rfl) ⟨4568840, by rfl⟩ : syracuseStep 6091787 = 9137681) B9137681
theorem B7222283 : Blo 1425532 7222283 := bstep (se 1 (by rfl) ⟨5416712, by rfl⟩ : syracuseStep 7222283 = 10833425) B10833425
theorem B17347607 : Blo 1425532 17347607 := bstep (se 1 (by rfl) ⟨13010705, by rfl⟩ : syracuseStep 17347607 = 26021411) B26021411
theorem B3609643 : Blo 1425532 3609643 := bstep (se 1 (by rfl) ⟨2707232, by rfl⟩ : syracuseStep 3609643 = 5414465) B5414465
theorem B2708615 : Blo 1425532 2708615 := bstep (se 1 (by rfl) ⟨2031461, by rfl⟩ : syracuseStep 2708615 = 4062923) B4062923
theorem B7222445 : Blo 1425532 7222445 := bstep (se 3 (by rfl) ⟨1354208, by rfl⟩ : syracuseStep 7222445 = 2708417) B2708417
theorem B13022381 : Blo 1425532 13022381 := bstep (se 3 (by rfl) ⟨2441696, by rfl⟩ : syracuseStep 13022381 = 4883393) B4883393
theorem B3609785 : Blo 1425532 3609785 := bstep (se 2 (by rfl) ⟨1353669, by rfl⟩ : syracuseStep 3609785 = 2707339) B2707339
theorem B3208463 : Blo 1425532 3208463 := bstep (se 1 (by rfl) ⟨2406347, by rfl⟩ : syracuseStep 3208463 = 4812695) B4812695
theorem B3208481 : Blo 1425532 3208481 := bstep (se 2 (by rfl) ⟨1203180, by rfl⟩ : syracuseStep 3208481 = 2406361) B2406361
theorem B2405767 : Blo 1425532 2405767 := bstep (se 1 (by rfl) ⟨1804325, by rfl⟩ : syracuseStep 2405767 = 3608651) B3608651
theorem B4814423 : Blo 1425532 4814423 := bstep (se 1 (by rfl) ⟨3610817, by rfl⟩ : syracuseStep 4814423 = 7221635) B7221635
theorem B3208823 : Blo 1425532 3208823 := bstep (se 1 (by rfl) ⟨2406617, by rfl⟩ : syracuseStep 3208823 = 4813235) B4813235
theorem B2709139 : Blo 1425532 2709139 := bstep (se 1 (by rfl) ⟨2031854, by rfl⟩ : syracuseStep 2709139 = 4063709) B4063709
theorem B4339385 : Blo 1425532 4339385 := bstep (se 2 (by rfl) ⟨1627269, by rfl⟩ : syracuseStep 4339385 = 3254539) B3254539
theorem B15423169 : Blo 1425532 15423169 := bstep (se 2 (by rfl) ⟨5783688, by rfl⟩ : syracuseStep 15423169 = 11567377) B11567377
theorem B3209003 : Blo 1425532 3209003 := bstep (se 1 (by rfl) ⟨2406752, by rfl⟩ : syracuseStep 3209003 = 4813505) B4813505
theorem B17340313 : Blo 1425532 17340313 := bstep (se 2 (by rfl) ⟨6502617, by rfl⟩ : syracuseStep 17340313 = 13005235) B13005235
theorem B2406415 : Blo 1425532 2406415 := bstep (se 1 (by rfl) ⟨1804811, by rfl⟩ : syracuseStep 2406415 = 3609623) B3609623
theorem B4569149 : Blo 1425532 4569149 := bstep (se 3 (by rfl) ⟨856715, by rfl⟩ : syracuseStep 4569149 = 1713431) B1713431
theorem B4814909 : Blo 1425532 4814909 := bstep (se 3 (by rfl) ⟨902795, by rfl⟩ : syracuseStep 4814909 = 1805591) B1805591
theorem B17348741 : Blo 1425532 17348741 := bstep (se 4 (by rfl) ⟨1626444, by rfl⟩ : syracuseStep 17348741 = 3252889) B3252889
theorem B3209363 : Blo 1425532 3209363 := bstep (se 1 (by rfl) ⟨2407022, by rfl⟩ : syracuseStep 3209363 = 4814045) B4814045
theorem B3610777 : Blo 1425532 3610777 := bstep (se 2 (by rfl) ⟨1354041, by rfl⟩ : syracuseStep 3610777 = 2708083) B2708083
theorem B3209417 : Blo 1425532 3209417 := bstep (se 2 (by rfl) ⟨1203531, by rfl⟩ : syracuseStep 3209417 = 2407063) B2407063
theorem B4061441 : Blo 1425532 4061441 := bstep (se 2 (by rfl) ⟨1523040, by rfl⟩ : syracuseStep 4061441 = 3046081) B3046081
theorem B5142799 : Blo 1425532 5142799 := bstep (se 1 (by rfl) ⟨3857099, by rfl⟩ : syracuseStep 5142799 = 7714199) B7714199
theorem B3610939 : Blo 1425532 3610939 := bstep (se 1 (by rfl) ⟨2708204, by rfl⟩ : syracuseStep 3610939 = 5416409) B5416409
theorem B4118843 : Blo 1425532 4118843 := bstep (se 1 (by rfl) ⟨3089132, by rfl⟩ : syracuseStep 4118843 = 6178265) B6178265
theorem B1603975 : Blo 1425532 1603975 := bstep (se 1 (by rfl) ⟨1202981, by rfl⟩ : syracuseStep 1603975 = 2405963) B2405963
theorem B3611081 : Blo 1425532 3611081 := bstep (se 2 (by rfl) ⟨1354155, by rfl⟩ : syracuseStep 3611081 = 2708311) B2708311
theorem B2030123 : Blo 1425532 2030123 := bstep (se 1 (by rfl) ⟨1522592, by rfl⟩ : syracuseStep 2030123 = 3045185) B3045185
theorem B2406955 : Blo 1425532 2406955 := bstep (se 1 (by rfl) ⟨1805216, by rfl⟩ : syracuseStep 2406955 = 3610433) B3610433
theorem B1604155 : Blo 1425532 1604155 := bstep (se 1 (by rfl) ⟨1203116, by rfl⟩ : syracuseStep 1604155 = 2406233) B2406233
theorem B5413463 : Blo 1425532 5413463 := bstep (se 1 (by rfl) ⟨4060097, by rfl⟩ : syracuseStep 5413463 = 8120195) B8120195
theorem B10418807 : Blo 1425532 10418807 := bstep (se 1 (by rfl) ⟨7814105, by rfl⟩ : syracuseStep 10418807 = 15628211) B15628211
theorem B1522319 : Blo 1425532 1522319 := bstep (se 1 (by rfl) ⟨1141739, by rfl⟩ : syracuseStep 1522319 = 2283479) B2283479
theorem B2407097 : Blo 1425532 2407097 := bstep (se 2 (by rfl) ⟨902661, by rfl⟩ : syracuseStep 2407097 = 1805323) B1805323
theorem B4061897 : Blo 1425532 4061897 := bstep (se 2 (by rfl) ⟨1523211, by rfl⟩ : syracuseStep 4061897 = 3046423) B3046423
theorem B7224065 : Blo 1425532 7224065 := bstep (se 2 (by rfl) ⟨2709024, by rfl⟩ : syracuseStep 7224065 = 5418049) B5418049
theorem B3611425 : Blo 1425532 3611425 := bstep (se 2 (by rfl) ⟨1354284, by rfl⟩ : syracuseStep 3611425 = 2708569) B2708569
theorem B3210119 : Blo 1425532 3210119 := bstep (se 1 (by rfl) ⟨2407589, by rfl⟩ : syracuseStep 3210119 = 4815179) B4815179
theorem B1604623 : Blo 1425532 1604623 := bstep (se 1 (by rfl) ⟨1203467, by rfl⟩ : syracuseStep 1604623 = 2406935) B2406935
theorem B4062251 : Blo 1425532 4062251 := bstep (se 1 (by rfl) ⟨3046688, by rfl⟩ : syracuseStep 4062251 = 6093377) B6093377
theorem B3210299 : Blo 1425532 3210299 := bstep (se 1 (by rfl) ⟨2407724, by rfl⟩ : syracuseStep 3210299 = 4815449) B4815449
theorem B5413949 : Blo 1425532 5413949 := bstep (se 3 (by rfl) ⟨1015115, by rfl⟩ : syracuseStep 5413949 = 2030231) B2030231
theorem B2890937 : Blo 1425532 2890937 := bstep (se 2 (by rfl) ⟨1084101, by rfl⟩ : syracuseStep 2890937 = 2168203) B2168203
theorem B3210425 : Blo 1425532 3210425 := bstep (se 2 (by rfl) ⟨1203909, by rfl⟩ : syracuseStep 3210425 = 2407819) B2407819
theorem B6094061 : Blo 1425532 6094061 := bstep (se 3 (by rfl) ⟨1142636, by rfl⟩ : syracuseStep 6094061 = 2285273) B2285273
theorem B2284843 : Blo 1425532 2284843 := bstep (se 1 (by rfl) ⟨1713632, by rfl⟩ : syracuseStep 2284843 = 3427265) B3427265
theorem B2407799 : Blo 1425532 2407799 := bstep (se 1 (by rfl) ⟨1805849, by rfl⟩ : syracuseStep 2407799 = 3611699) B3611699
theorem B3612023 : Blo 1425532 3612023 := bstep (se 1 (by rfl) ⟨2709017, by rfl⟩ : syracuseStep 3612023 = 5418035) B5418035
theorem B2284985 : Blo 1425532 2284985 := bstep (se 2 (by rfl) ⟨856869, by rfl⟩ : syracuseStep 2284985 = 1713739) B1713739
theorem B4062649 : Blo 1425532 4062649 := bstep (se 2 (by rfl) ⟨1523493, by rfl⟩ : syracuseStep 4062649 = 3046987) B3046987
theorem B4816313 : Blo 1425532 4816313 := bstep (se 2 (by rfl) ⟨1806117, by rfl⟩ : syracuseStep 4816313 = 3612235) B3612235
theorem B1605127 : Blo 1425532 1605127 := bstep (se 1 (by rfl) ⟨1203845, by rfl⟩ : syracuseStep 1605127 = 2407691) B2407691
theorem B3210767 : Blo 1425532 3210767 := bstep (se 1 (by rfl) ⟨2408075, by rfl⟩ : syracuseStep 3210767 = 4816151) B4816151
theorem B10976797 : Blo 1425532 10976797 := bstep (se 3 (by rfl) ⟨2058149, by rfl⟩ : syracuseStep 10976797 = 4116299) B4116299
theorem B3210785 : Blo 1425532 3210785 := bstep (se 2 (by rfl) ⟨1204044, by rfl⟩ : syracuseStep 3210785 = 2408089) B2408089
theorem B7224875 : Blo 1425532 7224875 := bstep (se 1 (by rfl) ⟨5418656, by rfl⟩ : syracuseStep 7224875 = 10837313) B10837313
theorem B54836837 : Blo 1425532 54836837 := bstep (se 4 (by rfl) ⟨5140953, by rfl⟩ : syracuseStep 54836837 = 10281907) B10281907
theorem B3858073 : Blo 1425532 3858073 := bstep (se 2 (by rfl) ⟨1446777, by rfl⟩ : syracuseStep 3858073 = 2893555) B2893555
theorem B1605307 : Blo 1425532 1605307 := bstep (se 1 (by rfl) ⟨1203980, by rfl⟩ : syracuseStep 1605307 = 2407961) B2407961
theorem B23125733 : Blo 1425532 23125733 := bstep (se 4 (by rfl) ⟨2168037, by rfl⟩ : syracuseStep 23125733 = 4336075) B4336075
theorem B100228913 : Blo 1425532 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B2408251 : Blo 1425532 2408251 := bstep (se 1 (by rfl) ⟨1806188, by rfl⟩ : syracuseStep 2408251 = 3612377) B3612377
theorem B3211127 : Blo 1425532 3211127 := bstep (se 1 (by rfl) ⟨2408345, by rfl⟩ : syracuseStep 3211127 = 4816691) B4816691
theorem B20848535 : Blo 1425532 20848535 := bstep (se 1 (by rfl) ⟨15636401, by rfl⟩ : syracuseStep 20848535 = 31272803) B31272803
theorem B2408393 : Blo 1425532 2408393 := bstep (se 2 (by rfl) ⟨903147, by rfl⟩ : syracuseStep 2408393 = 1806295) B1806295
theorem B7217099 : Blo 1425532 7217099 := bstep (se 1 (by rfl) ⟨5412824, by rfl⟩ : syracuseStep 7217099 = 10825649) B10825649
theorem B3211271 : Blo 1425532 3211271 := bstep (se 1 (by rfl) ⟨2408453, by rfl⟩ : syracuseStep 3211271 = 4816907) B4816907
theorem B2031655 : Blo 1425532 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B3211343 : Blo 1425532 3211343 := bstep (se 1 (by rfl) ⟨2408507, by rfl⟩ : syracuseStep 3211343 = 4817015) B4817015
theorem B10289267 : Blo 1425532 10289267 := bstep (se 1 (by rfl) ⟨7716950, by rfl⟩ : syracuseStep 10289267 = 15433901) B15433901
theorem B1425583 : Blo 1425532 1425583 := bstep (se 1 (by rfl) ⟨1069187, by rfl⟩ : syracuseStep 1425583 = 2138375) B2138375
theorem B1425607 : Blo 1425532 1425607 := bstep (se 1 (by rfl) ⟨1069205, by rfl⟩ : syracuseStep 1425607 = 2138411) B2138411
theorem B1425627 : Blo 1425532 1425627 := bstep (se 1 (by rfl) ⟨1069220, by rfl⟩ : syracuseStep 1425627 = 2138441) B2138441
theorem B1425703 : Blo 1425532 1425703 := bstep (se 1 (by rfl) ⟨1069277, by rfl⟩ : syracuseStep 1425703 = 2138555) B2138555
theorem B1425743 : Blo 1425532 1425743 := bstep (se 1 (by rfl) ⟨1069307, by rfl⟩ : syracuseStep 1425743 = 2138615) B2138615
theorem B1425759 : Blo 1425532 1425759 := bstep (se 1 (by rfl) ⟨1069319, by rfl⟩ : syracuseStep 1425759 = 2138639) B2138639
theorem B6857065 : Blo 1425532 6857065 := bstep (se 2 (by rfl) ⟨2571399, by rfl⟩ : syracuseStep 6857065 = 5142799) B5142799
theorem B1425787 : Blo 1425532 1425787 := bstep (se 1 (by rfl) ⟨1069340, by rfl⟩ : syracuseStep 1425787 = 2138681) B2138681
theorem B2138543 : Blo 1425532 2138543 := bstep (se 1 (by rfl) ⟨1603907, by rfl⟩ : syracuseStep 2138543 = 3207815) B3207815
theorem B1425839 : Blo 1425532 1425839 := bstep (se 1 (by rfl) ⟨1069379, by rfl⟩ : syracuseStep 1425839 = 2138759) B2138759
theorem B1524143 : Blo 1425532 1524143 := bstep (se 1 (by rfl) ⟨1143107, by rfl⟩ : syracuseStep 1524143 = 2286215) B2286215
theorem B2408879 : Blo 1425532 2408879 := bstep (se 1 (by rfl) ⟨1806659, by rfl⟩ : syracuseStep 2408879 = 3613319) B3613319
theorem B1425863 : Blo 1425532 1425863 := bstep (se 1 (by rfl) ⟨1069397, by rfl⟩ : syracuseStep 1425863 = 2138795) B2138795
theorem B1425883 : Blo 1425532 1425883 := bstep (se 1 (by rfl) ⟨1069412, by rfl⟩ : syracuseStep 1425883 = 2138825) B2138825
theorem B3211739 : Blo 1425532 3211739 := bstep (se 1 (by rfl) ⟨2408804, by rfl⟩ : syracuseStep 3211739 = 4817609) B4817609
theorem B7709165 : Blo 1425532 7709165 := bstep (se 3 (by rfl) ⟨1445468, by rfl⟩ : syracuseStep 7709165 = 2890937) B2890937
theorem B2138633 : Blo 1425532 2138633 := bstep (se 2 (by rfl) ⟨801987, by rfl⟩ : syracuseStep 2138633 = 1603975) B1603975
theorem B2138663 : Blo 1425532 2138663 := bstep (se 1 (by rfl) ⟨1603997, by rfl⟩ : syracuseStep 2138663 = 3207995) B3207995
theorem B1425959 : Blo 1425532 1425959 := bstep (se 1 (by rfl) ⟨1069469, by rfl⟩ : syracuseStep 1425959 = 2138939) B2138939
theorem B4817447 : Blo 1425532 4817447 := bstep (se 1 (by rfl) ⟨3613085, by rfl⟩ : syracuseStep 4817447 = 7226171) B7226171
theorem B6947387 : Blo 1425532 6947387 := bstep (se 1 (by rfl) ⟨5210540, by rfl⟩ : syracuseStep 6947387 = 10421081) B10421081
theorem B1425999 : Blo 1425532 1425999 := bstep (se 1 (by rfl) ⟨1069499, by rfl⟩ : syracuseStep 1425999 = 2138999) B2138999
theorem B1426015 : Blo 1425532 1426015 := bstep (se 1 (by rfl) ⟨1069511, by rfl⟩ : syracuseStep 1426015 = 2139023) B2139023
theorem B2138747 : Blo 1425532 2138747 := bstep (se 1 (by rfl) ⟨1604060, by rfl⟩ : syracuseStep 2138747 = 3208121) B3208121
theorem B1426043 : Blo 1425532 1426043 := bstep (se 1 (by rfl) ⟨1069532, by rfl⟩ : syracuseStep 1426043 = 2139065) B2139065
theorem B4817555 : Blo 1425532 4817555 := bstep (se 1 (by rfl) ⟨3613166, by rfl⟩ : syracuseStep 4817555 = 7226333) B7226333
theorem B10830509 : Blo 1425532 10830509 := bstep (se 3 (by rfl) ⟨2030720, by rfl⟩ : syracuseStep 10830509 = 4061441) B4061441
theorem B1426095 : Blo 1425532 1426095 := bstep (se 1 (by rfl) ⟨1069571, by rfl⟩ : syracuseStep 1426095 = 2139143) B2139143
theorem B1426119 : Blo 1425532 1426119 := bstep (se 1 (by rfl) ⟨1069589, by rfl⟩ : syracuseStep 1426119 = 2139179) B2139179
theorem B2032327 : Blo 1425532 2032327 := bstep (se 1 (by rfl) ⟨1524245, by rfl⟩ : syracuseStep 2032327 = 3048491) B3048491
theorem B1426139 : Blo 1425532 1426139 := bstep (se 1 (by rfl) ⟨1069604, by rfl⟩ : syracuseStep 1426139 = 2139209) B2139209
theorem B2138873 : Blo 1425532 2138873 := bstep (se 2 (by rfl) ⟨802077, by rfl⟩ : syracuseStep 2138873 = 1604155) B1604155
theorem B1426215 : Blo 1425532 1426215 := bstep (se 1 (by rfl) ⟨1069661, by rfl⟩ : syracuseStep 1426215 = 2139323) B2139323
theorem B1426255 : Blo 1425532 1426255 := bstep (se 1 (by rfl) ⟨1069691, by rfl⟩ : syracuseStep 1426255 = 2139383) B2139383
theorem B2138975 : Blo 1425532 2138975 := bstep (se 1 (by rfl) ⟨1604231, by rfl⟩ : syracuseStep 2138975 = 3208463) B3208463
theorem B1426271 : Blo 1425532 1426271 := bstep (se 1 (by rfl) ⟨1069703, by rfl⟩ : syracuseStep 1426271 = 2139407) B2139407
theorem B2138987 : Blo 1425532 2138987 := bstep (se 1 (by rfl) ⟨1604240, by rfl⟩ : syracuseStep 2138987 = 3208481) B3208481
theorem B4064107 : Blo 1425532 4064107 := bstep (se 1 (by rfl) ⟨3048080, by rfl⟩ : syracuseStep 4064107 = 6096161) B6096161
theorem B4817771 : Blo 1425532 4817771 := bstep (se 1 (by rfl) ⟨3613328, by rfl⟩ : syracuseStep 4817771 = 7226657) B7226657
theorem B1426299 : Blo 1425532 1426299 := bstep (se 1 (by rfl) ⟨1069724, by rfl⟩ : syracuseStep 1426299 = 2139449) B2139449
theorem B4817825 : Blo 1425532 4817825 := bstep (se 2 (by rfl) ⟨1806684, by rfl⟩ : syracuseStep 4817825 = 3613369) B3613369
theorem B1426351 : Blo 1425532 1426351 := bstep (se 1 (by rfl) ⟨1069763, by rfl⟩ : syracuseStep 1426351 = 2139527) B2139527
theorem B1426375 : Blo 1425532 1426375 := bstep (se 1 (by rfl) ⟨1069781, by rfl⟩ : syracuseStep 1426375 = 2139563) B2139563
theorem B1426395 : Blo 1425532 1426395 := bstep (se 1 (by rfl) ⟨1069796, by rfl⟩ : syracuseStep 1426395 = 2139593) B2139593
theorem B1426471 : Blo 1425532 1426471 := bstep (se 1 (by rfl) ⟨1069853, by rfl⟩ : syracuseStep 1426471 = 2139707) B2139707
theorem B2139215 : Blo 1425532 2139215 := bstep (se 1 (by rfl) ⟨1604411, by rfl⟩ : syracuseStep 2139215 = 3208823) B3208823
theorem B1426511 : Blo 1425532 1426511 := bstep (se 1 (by rfl) ⟨1069883, by rfl⟩ : syracuseStep 1426511 = 2139767) B2139767
theorem B1426527 : Blo 1425532 1426527 := bstep (se 1 (by rfl) ⟨1069895, by rfl⟩ : syracuseStep 1426527 = 2139791) B2139791
theorem B1426555 : Blo 1425532 1426555 := bstep (se 1 (by rfl) ⟨1069916, by rfl⟩ : syracuseStep 1426555 = 2139833) B2139833
theorem B2892923 : Blo 1425532 2892923 := bstep (se 1 (by rfl) ⟨2169692, by rfl⟩ : syracuseStep 2892923 = 4339385) B4339385
theorem B1426607 : Blo 1425532 1426607 := bstep (se 1 (by rfl) ⟨1069955, by rfl⟩ : syracuseStep 1426607 = 2139911) B2139911
theorem B2139335 : Blo 1425532 2139335 := bstep (se 1 (by rfl) ⟨1604501, by rfl⟩ : syracuseStep 2139335 = 3209003) B3209003
theorem B1426631 : Blo 1425532 1426631 := bstep (se 1 (by rfl) ⟨1069973, by rfl⟩ : syracuseStep 1426631 = 2139947) B2139947
theorem B1426651 : Blo 1425532 1426651 := bstep (se 1 (by rfl) ⟨1069988, by rfl⟩ : syracuseStep 1426651 = 2139977) B2139977
theorem B1426727 : Blo 1425532 1426727 := bstep (se 1 (by rfl) ⟨1070045, by rfl⟩ : syracuseStep 1426727 = 2140091) B2140091
theorem B1426767 : Blo 1425532 1426767 := bstep (se 1 (by rfl) ⟨1070075, by rfl⟩ : syracuseStep 1426767 = 2140151) B2140151
theorem B5211479 : Blo 1425532 5211479 := bstep (se 1 (by rfl) ⟨3908609, by rfl⟩ : syracuseStep 5211479 = 7817219) B7817219
theorem B1426783 : Blo 1425532 1426783 := bstep (se 1 (by rfl) ⟨1070087, by rfl⟩ : syracuseStep 1426783 = 2140175) B2140175
theorem B2139497 : Blo 1425532 2139497 := bstep (se 2 (by rfl) ⟨802311, by rfl⟩ : syracuseStep 2139497 = 1604623) B1604623
theorem B1426811 : Blo 1425532 1426811 := bstep (se 1 (by rfl) ⟨1070108, by rfl⟩ : syracuseStep 1426811 = 2140217) B2140217
theorem B7218557 : Blo 1425532 7218557 := bstep (se 3 (by rfl) ⟨1353479, by rfl⟩ : syracuseStep 7218557 = 2706959) B2706959
theorem B1426863 : Blo 1425532 1426863 := bstep (se 1 (by rfl) ⟨1070147, by rfl⟩ : syracuseStep 1426863 = 2140295) B2140295
theorem B2139575 : Blo 1425532 2139575 := bstep (se 1 (by rfl) ⟨1604681, by rfl⟩ : syracuseStep 2139575 = 3209363) B3209363
theorem B1426887 : Blo 1425532 1426887 := bstep (se 1 (by rfl) ⟨1070165, by rfl⟩ : syracuseStep 1426887 = 2140331) B2140331
theorem B2139611 : Blo 1425532 2139611 := bstep (se 1 (by rfl) ⟨1604708, by rfl⟩ : syracuseStep 2139611 = 3209417) B3209417
theorem B1426907 : Blo 1425532 1426907 := bstep (se 1 (by rfl) ⟨1070180, by rfl⟩ : syracuseStep 1426907 = 2140361) B2140361
theorem B2745895 : Blo 1425532 2745895 := bstep (se 1 (by rfl) ⟨2059421, by rfl⟩ : syracuseStep 2745895 = 4118843) B4118843
theorem B1426983 : Blo 1425532 1426983 := bstep (se 1 (by rfl) ⟨1070237, by rfl⟩ : syracuseStep 1426983 = 2140475) B2140475
theorem B1427023 : Blo 1425532 1427023 := bstep (se 1 (by rfl) ⟨1070267, by rfl⟩ : syracuseStep 1427023 = 2140535) B2140535
theorem B1427039 : Blo 1425532 1427039 := bstep (se 1 (by rfl) ⟨1070279, by rfl⟩ : syracuseStep 1427039 = 2140559) B2140559
theorem B1427067 : Blo 1425532 1427067 := bstep (se 1 (by rfl) ⟨1070300, by rfl⟩ : syracuseStep 1427067 = 2140601) B2140601
theorem B1427119 : Blo 1425532 1427119 := bstep (se 1 (by rfl) ⟨1070339, by rfl⟩ : syracuseStep 1427119 = 2140679) B2140679
theorem B12191431 : Blo 1425532 12191431 := bstep (se 1 (by rfl) ⟨9143573, by rfl⟩ : syracuseStep 12191431 = 18287147) B18287147
theorem B1427143 : Blo 1425532 1427143 := bstep (se 1 (by rfl) ⟨1070357, by rfl⟩ : syracuseStep 1427143 = 2140715) B2140715
theorem B5138129 : Blo 1425532 5138129 := bstep (se 2 (by rfl) ⟨1926798, by rfl⟩ : syracuseStep 5138129 = 3853597) B3853597
theorem B1427163 : Blo 1425532 1427163 := bstep (se 1 (by rfl) ⟨1070372, by rfl⟩ : syracuseStep 1427163 = 2140745) B2140745
theorem B1427239 : Blo 1425532 1427239 := bstep (se 1 (by rfl) ⟨1070429, by rfl⟩ : syracuseStep 1427239 = 2140859) B2140859
theorem B1427279 : Blo 1425532 1427279 := bstep (se 1 (by rfl) ⟨1070459, by rfl⟩ : syracuseStep 1427279 = 2140919) B2140919
theorem B1427295 : Blo 1425532 1427295 := bstep (se 1 (by rfl) ⟨1070471, by rfl⟩ : syracuseStep 1427295 = 2140943) B2140943
theorem B1427323 : Blo 1425532 1427323 := bstep (se 1 (by rfl) ⟨1070492, by rfl⟩ : syracuseStep 1427323 = 2140985) B2140985
theorem B5416865 : Blo 1425532 5416865 := bstep (se 2 (by rfl) ⟨2031324, by rfl⟩ : syracuseStep 5416865 = 4062649) B4062649
theorem B2140079 : Blo 1425532 2140079 := bstep (se 1 (by rfl) ⟨1605059, by rfl⟩ : syracuseStep 2140079 = 3210119) B3210119
theorem B1427375 : Blo 1425532 1427375 := bstep (se 1 (by rfl) ⟨1070531, by rfl⟩ : syracuseStep 1427375 = 2141063) B2141063
theorem B1427399 : Blo 1425532 1427399 := bstep (se 1 (by rfl) ⟨1070549, by rfl⟩ : syracuseStep 1427399 = 2141099) B2141099
theorem B1427419 : Blo 1425532 1427419 := bstep (se 1 (by rfl) ⟨1070564, by rfl⟩ : syracuseStep 1427419 = 2141129) B2141129
theorem B2140169 : Blo 1425532 2140169 := bstep (se 2 (by rfl) ⟨802563, by rfl⟩ : syracuseStep 2140169 = 1605127) B1605127
theorem B2140199 : Blo 1425532 2140199 := bstep (se 1 (by rfl) ⟨1605149, by rfl⟩ : syracuseStep 2140199 = 3210299) B3210299
theorem B1427495 : Blo 1425532 1427495 := bstep (se 1 (by rfl) ⟨1070621, by rfl⟩ : syracuseStep 1427495 = 2141243) B2141243
theorem B12183641 : Blo 1425532 12183641 := bstep (se 2 (by rfl) ⟨4568865, by rfl⟩ : syracuseStep 12183641 = 9137731) B9137731
theorem B2140283 : Blo 1425532 2140283 := bstep (se 1 (by rfl) ⟨1605212, by rfl⟩ : syracuseStep 2140283 = 3210425) B3210425
theorem B62580869 : Blo 1425532 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B2140409 : Blo 1425532 2140409 := bstep (se 2 (by rfl) ⟨802653, by rfl⟩ : syracuseStep 2140409 = 1605307) B1605307
theorem B20564225 : Blo 1425532 20564225 := bstep (se 2 (by rfl) ⟨7711584, by rfl⟩ : syracuseStep 20564225 = 15423169) B15423169
theorem B2140511 : Blo 1425532 2140511 := bstep (se 1 (by rfl) ⟨1605383, by rfl⟩ : syracuseStep 2140511 = 3210767) B3210767
theorem B2140523 : Blo 1425532 2140523 := bstep (se 1 (by rfl) ⟨1605392, by rfl⟩ : syracuseStep 2140523 = 3210785) B3210785
theorem B23120417 : Blo 1425532 23120417 := bstep (se 2 (by rfl) ⟨8670156, by rfl⟩ : syracuseStep 23120417 = 17340313) B17340313
theorem B2140751 : Blo 1425532 2140751 := bstep (se 1 (by rfl) ⟨1605563, by rfl⟩ : syracuseStep 2140751 = 3211127) B3211127
theorem B4811399 : Blo 1425532 4811399 := bstep (se 1 (by rfl) ⟨3608549, by rfl⟩ : syracuseStep 4811399 = 7217099) B7217099
theorem B4811453 : Blo 1425532 4811453 := bstep (se 3 (by rfl) ⟨902147, by rfl⟩ : syracuseStep 4811453 = 1804295) B1804295
theorem B1804999 : Blo 1425532 1804999 := bstep (se 1 (by rfl) ⟨1353749, by rfl⟩ : syracuseStep 1804999 = 2707499) B2707499
theorem B2140871 : Blo 1425532 2140871 := bstep (se 1 (by rfl) ⟨1605653, by rfl⟩ : syracuseStep 2140871 = 3211307) B3211307
theorem B4811615 : Blo 1425532 4811615 := bstep (se 1 (by rfl) ⟨3608711, by rfl⟩ : syracuseStep 4811615 = 7217423) B7217423
theorem B2141033 : Blo 1425532 2141033 := bstep (se 2 (by rfl) ⟨802887, by rfl⟩ : syracuseStep 2141033 = 1605775) B1605775
theorem B5417837 : Blo 1425532 5417837 := bstep (se 3 (by rfl) ⟨1015844, by rfl⟩ : syracuseStep 5417837 = 2031689) B2031689
theorem B2141111 : Blo 1425532 2141111 := bstep (se 1 (by rfl) ⟨1605833, by rfl⟩ : syracuseStep 2141111 = 3211667) B3211667
theorem B2141147 : Blo 1425532 2141147 := bstep (se 1 (by rfl) ⟨1605860, by rfl⟩ : syracuseStep 2141147 = 3211721) B3211721
theorem B4811777 : Blo 1425532 4811777 := bstep (se 2 (by rfl) ⟨1804416, by rfl⟩ : syracuseStep 4811777 = 3608833) B3608833
theorem B9137195 : Blo 1425532 9137195 := bstep (se 1 (by rfl) ⟨6852896, by rfl⟩ : syracuseStep 9137195 = 13705793) B13705793
theorem B10832939 : Blo 1425532 10832939 := bstep (se 1 (by rfl) ⟨8124704, by rfl⟩ : syracuseStep 10832939 = 16249409) B16249409
theorem B1445083 : Blo 1425532 1445083 := bstep (se 1 (by rfl) ⟨1083812, by rfl⟩ : syracuseStep 1445083 = 2167625) B2167625
theorem B6089975 : Blo 1425532 6089975 := bstep (se 1 (by rfl) ⟨4567481, by rfl⟩ : syracuseStep 6089975 = 9134963) B9134963
theorem B8793335 : Blo 1425532 8793335 := bstep (se 1 (by rfl) ⟨6595001, by rfl⟩ : syracuseStep 8793335 = 13190003) B13190003
theorem B9137423 : Blo 1425532 9137423 := bstep (se 1 (by rfl) ⟨6853067, by rfl⟩ : syracuseStep 9137423 = 13706135) B13706135
theorem B11570521 : Blo 1425532 11570521 := bstep (se 2 (by rfl) ⟨4338945, by rfl⟩ : syracuseStep 11570521 = 8677891) B8677891
theorem B1805743 : Blo 1425532 1805743 := bstep (se 1 (by rfl) ⟨1354307, by rfl⟩ : syracuseStep 1805743 = 2708615) B2708615
theorem B5418521 : Blo 1425532 5418521 := bstep (se 2 (by rfl) ⟨2031945, by rfl⟩ : syracuseStep 5418521 = 4063891) B4063891
theorem B5418535 : Blo 1425532 5418535 := bstep (se 1 (by rfl) ⟨4063901, by rfl⟩ : syracuseStep 5418535 = 8127803) B8127803
theorem B21966403 : Blo 1425532 21966403 := bstep (se 1 (by rfl) ⟨16474802, by rfl⟩ : syracuseStep 21966403 = 32949605) B32949605
theorem B4877921 : Blo 1425532 4877921 := bstep (se 2 (by rfl) ⟨1829220, by rfl⟩ : syracuseStep 4877921 = 3658441) B3658441
theorem B10284677 : Blo 1425532 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B4812587 : Blo 1425532 4812587 := bstep (se 1 (by rfl) ⟨3609440, by rfl⟩ : syracuseStep 4812587 = 7218881) B7218881
theorem B4812857 : Blo 1425532 4812857 := bstep (se 2 (by rfl) ⟨1804821, by rfl⟩ : syracuseStep 4812857 = 3609643) B3609643
theorem B27423035 : Blo 1425532 27423035 := bstep (se 1 (by rfl) ⟨20567276, by rfl⟩ : syracuseStep 27423035 = 41134553) B41134553
theorem B5419325 : Blo 1425532 5419325 := bstep (se 3 (by rfl) ⟨1016123, by rfl⟩ : syracuseStep 5419325 = 2032247) B2032247
theorem B4059517 : Blo 1425532 4059517 := bstep (se 3 (by rfl) ⟨761159, by rfl⟩ : syracuseStep 4059517 = 1522319) B1522319
theorem B4813181 : Blo 1425532 4813181 := bstep (se 3 (by rfl) ⟨902471, by rfl⟩ : syracuseStep 4813181 = 1804943) B1804943
theorem B3608975 : Blo 1425532 3608975 := bstep (se 1 (by rfl) ⟨2706731, by rfl⟩ : syracuseStep 3608975 = 5413463) B5413463
theorem B2707931 : Blo 1425532 2707931 := bstep (se 1 (by rfl) ⟨2030948, by rfl⟩ : syracuseStep 2707931 = 4061897) B4061897
theorem B5419507 : Blo 1425532 5419507 := bstep (se 1 (by rfl) ⟨4064630, by rfl⟩ : syracuseStep 5419507 = 8129261) B8129261
theorem B3207689 : Blo 1425532 3207689 := bstep (se 2 (by rfl) ⟨1202883, by rfl⟩ : syracuseStep 3207689 = 2405767) B2405767
theorem B4813451 : Blo 1425532 4813451 := bstep (se 1 (by rfl) ⟨3610088, by rfl⟩ : syracuseStep 4813451 = 7220177) B7220177
theorem B2708167 : Blo 1425532 2708167 := bstep (se 1 (by rfl) ⟨2031125, by rfl⟩ : syracuseStep 2708167 = 4062251) B4062251
theorem B14635729 : Blo 1425532 14635729 := bstep (se 2 (by rfl) ⟨5488398, by rfl⟩ : syracuseStep 14635729 = 10976797) B10976797
theorem B3609299 : Blo 1425532 3609299 := bstep (se 1 (by rfl) ⟨2706974, by rfl⟩ : syracuseStep 3609299 = 5413949) B5413949
theorem B3208031 : Blo 1425532 3208031 := bstep (se 1 (by rfl) ⟨2406023, by rfl⟩ : syracuseStep 3208031 = 4812047) B4812047
theorem B39040001 : Blo 1425532 39040001 := bstep (se 2 (by rfl) ⟨14640000, by rfl⟩ : syracuseStep 39040001 = 29280001) B29280001
theorem B5141519 : Blo 1425532 5141519 := bstep (se 1 (by rfl) ⟨3856139, by rfl⟩ : syracuseStep 5141519 = 7712279) B7712279
theorem B3208211 : Blo 1425532 3208211 := bstep (se 1 (by rfl) ⟨2406158, by rfl⟩ : syracuseStep 3208211 = 4812317) B4812317
theorem B36557891 : Blo 1425532 36557891 := bstep (se 1 (by rfl) ⟨27418418, by rfl⟩ : syracuseStep 36557891 = 54836837) B54836837
theorem B66819275 : Blo 1425532 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B13899023 : Blo 1425532 13899023 := bstep (se 1 (by rfl) ⟨10424267, by rfl⟩ : syracuseStep 13899023 = 20848535) B20848535
theorem B10286351 : Blo 1425532 10286351 := bstep (se 1 (by rfl) ⟨7714763, by rfl⟩ : syracuseStep 10286351 = 15429527) B15429527
theorem B3208553 : Blo 1425532 3208553 := bstep (se 2 (by rfl) ⟨1203207, by rfl⟩ : syracuseStep 3208553 = 2406415) B2406415
theorem B4568609 : Blo 1425532 4568609 := bstep (se 2 (by rfl) ⟨1713228, by rfl⟩ : syracuseStep 4568609 = 3426457) B3426457
theorem B4814369 : Blo 1425532 4814369 := bstep (se 2 (by rfl) ⟨1805388, by rfl⟩ : syracuseStep 4814369 = 3610777) B3610777
theorem B22271531 : Blo 1425532 22271531 := bstep (se 1 (by rfl) ⟨16703648, by rfl⟩ : syracuseStep 22271531 = 33407297) B33407297
theorem B8230547 : Blo 1425532 8230547 := bstep (se 1 (by rfl) ⟨6172910, by rfl⟩ : syracuseStep 8230547 = 12345821) B12345821
theorem B6092435 : Blo 1425532 6092435 := bstep (se 1 (by rfl) ⟨4569326, by rfl⟩ : syracuseStep 6092435 = 9138653) B9138653
theorem B7222931 : Blo 1425532 7222931 := bstep (se 1 (by rfl) ⟨5417198, by rfl⟩ : syracuseStep 7222931 = 10834397) B10834397
theorem B4814585 : Blo 1425532 4814585 := bstep (se 2 (by rfl) ⟨1805469, by rfl⟩ : syracuseStep 4814585 = 3610939) B3610939
theorem B5412703 : Blo 1425532 5412703 := bstep (se 1 (by rfl) ⟨4059527, by rfl⟩ : syracuseStep 5412703 = 8119055) B8119055
theorem B2406287 : Blo 1425532 2406287 := bstep (se 1 (by rfl) ⟨1804715, by rfl⟩ : syracuseStep 2406287 = 3609431) B3609431
theorem B3209147 : Blo 1425532 3209147 := bstep (se 1 (by rfl) ⟨2406860, by rfl⟩ : syracuseStep 3209147 = 4813721) B4813721
theorem B15849425 : Blo 1425532 15849425 := bstep (se 2 (by rfl) ⟨5943534, by rfl⟩ : syracuseStep 15849425 = 11887069) B11887069
theorem B2471899 : Blo 1425532 2471899 := bstep (se 1 (by rfl) ⟨1853924, by rfl⟩ : syracuseStep 2471899 = 3707849) B3707849
theorem B4061191 : Blo 1425532 4061191 := bstep (se 1 (by rfl) ⟨3045893, by rfl⟩ : syracuseStep 4061191 = 6091787) B6091787
theorem B4814855 : Blo 1425532 4814855 := bstep (se 1 (by rfl) ⟨3611141, by rfl⟩ : syracuseStep 4814855 = 7222283) B7222283
theorem B11565071 : Blo 1425532 11565071 := bstep (se 1 (by rfl) ⟨8673803, by rfl⟩ : syracuseStep 11565071 = 17347607) B17347607
theorem B3209273 : Blo 1425532 3209273 := bstep (se 2 (by rfl) ⟨1203477, by rfl⟩ : syracuseStep 3209273 = 2406955) B2406955
theorem B4814963 : Blo 1425532 4814963 := bstep (se 1 (by rfl) ⟨3611222, by rfl⟩ : syracuseStep 4814963 = 7222445) B7222445
theorem B8681587 : Blo 1425532 8681587 := bstep (se 1 (by rfl) ⟨6511190, by rfl⟩ : syracuseStep 8681587 = 13022381) B13022381
theorem B2406523 : Blo 1425532 2406523 := bstep (se 1 (by rfl) ⟨1804892, by rfl⟩ : syracuseStep 2406523 = 3609785) B3609785
theorem B20576389 : Blo 1425532 20576389 := bstep (se 4 (by rfl) ⟨1929036, by rfl⟩ : syracuseStep 20576389 = 3858073) B3858073
theorem B5142685 : Blo 1425532 5142685 := bstep (se 3 (by rfl) ⟨964253, by rfl⟩ : syracuseStep 5142685 = 1928507) B1928507
theorem B24107165 : Blo 1425532 24107165 := bstep (se 3 (by rfl) ⟨4520093, by rfl⟩ : syracuseStep 24107165 = 9040187) B9040187
theorem B4815233 : Blo 1425532 4815233 := bstep (se 2 (by rfl) ⟨1805712, by rfl⟩ : syracuseStep 4815233 = 3611425) B3611425
theorem B3209615 : Blo 1425532 3209615 := bstep (se 1 (by rfl) ⟨2407211, by rfl⟩ : syracuseStep 3209615 = 4814423) B4814423
theorem B2710073 : Blo 1425532 2710073 := bstep (se 2 (by rfl) ⟨1016277, by rfl⟩ : syracuseStep 2710073 = 2032555) B2032555
theorem B3046099 : Blo 1425532 3046099 := bstep (se 1 (by rfl) ⟨2284574, by rfl⟩ : syracuseStep 3046099 = 4569149) B4569149
theorem B3209939 : Blo 1425532 3209939 := bstep (se 1 (by rfl) ⟨2407454, by rfl⟩ : syracuseStep 3209939 = 4814909) B4814909
theorem B11565827 : Blo 1425532 11565827 := bstep (se 1 (by rfl) ⟨8674370, by rfl⟩ : syracuseStep 11565827 = 17348741) B17348741
theorem B5413661 : Blo 1425532 5413661 := bstep (se 3 (by rfl) ⟨1015061, by rfl⟩ : syracuseStep 5413661 = 2030123) B2030123
theorem B5413675 : Blo 1425532 5413675 := bstep (se 1 (by rfl) ⟨4060256, by rfl⟩ : syracuseStep 5413675 = 8120513) B8120513
theorem B3611567 : Blo 1425532 3611567 := bstep (se 1 (by rfl) ⟨2708675, by rfl⟩ : syracuseStep 3611567 = 5417351) B5417351
theorem B2407387 : Blo 1425532 2407387 := bstep (se 1 (by rfl) ⟨1805540, by rfl⟩ : syracuseStep 2407387 = 3611081) B3611081
theorem B3046457 : Blo 1425532 3046457 := bstep (se 2 (by rfl) ⟨1142421, by rfl⟩ : syracuseStep 3046457 = 2284843) B2284843
theorem B6945871 : Blo 1425532 6945871 := bstep (se 1 (by rfl) ⟨5209403, by rfl⟩ : syracuseStep 6945871 = 10418807) B10418807
theorem B1604731 : Blo 1425532 1604731 := bstep (se 1 (by rfl) ⟨1203548, by rfl⟩ : syracuseStep 1604731 = 2407097) B2407097
theorem B2284715 : Blo 1425532 2284715 := bstep (se 1 (by rfl) ⟨1713536, by rfl⟩ : syracuseStep 2284715 = 3427073) B3427073
theorem B4816043 : Blo 1425532 4816043 := bstep (se 1 (by rfl) ⟨3612032, by rfl⟩ : syracuseStep 4816043 = 7224065) B7224065
theorem B21961975 : Blo 1425532 21961975 := bstep (se 1 (by rfl) ⟨16471481, by rfl⟩ : syracuseStep 21961975 = 32942963) B32942963
theorem B21945725 : Blo 1425532 21945725 := bstep (se 3 (by rfl) ⟨4114823, by rfl⟩ : syracuseStep 21945725 = 8229647) B8229647
theorem B4062707 : Blo 1425532 4062707 := bstep (se 1 (by rfl) ⟨3047030, by rfl⟩ : syracuseStep 4062707 = 6094061) B6094061
theorem B3612185 : Blo 1425532 3612185 := bstep (se 2 (by rfl) ⟨1354569, by rfl⟩ : syracuseStep 3612185 = 2709139) B2709139
theorem B2571833 : Blo 1425532 2571833 := bstep (se 2 (by rfl) ⟨964437, by rfl⟩ : syracuseStep 2571833 = 1928875) B1928875
theorem B32923201 : Blo 1425532 32923201 := bstep (se 2 (by rfl) ⟨12346200, by rfl⟩ : syracuseStep 32923201 = 24692401) B24692401
theorem B1605199 : Blo 1425532 1605199 := bstep (se 1 (by rfl) ⟨1203899, by rfl⟩ : syracuseStep 1605199 = 2407799) B2407799
theorem B2408015 : Blo 1425532 2408015 := bstep (se 1 (by rfl) ⟨1806011, by rfl⟩ : syracuseStep 2408015 = 3612023) B3612023
theorem B1523323 : Blo 1425532 1523323 := bstep (se 1 (by rfl) ⟨1142492, by rfl⟩ : syracuseStep 1523323 = 2284985) B2284985
theorem B3210875 : Blo 1425532 3210875 := bstep (se 1 (by rfl) ⟨2408156, by rfl⟩ : syracuseStep 3210875 = 4816313) B4816313
theorem B3858043 : Blo 1425532 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B18276029 : Blo 1425532 18276029 := bstep (se 3 (by rfl) ⟨3426755, by rfl⟩ : syracuseStep 18276029 = 6853511) B6853511
theorem B4816583 : Blo 1425532 4816583 := bstep (se 1 (by rfl) ⟨3612437, by rfl⟩ : syracuseStep 4816583 = 7224875) B7224875
theorem B2678483 : Blo 1425532 2678483 := bstep (se 1 (by rfl) ⟨2008862, by rfl⟩ : syracuseStep 2678483 = 4017725) B4017725
theorem B6504185 : Blo 1425532 6504185 := bstep (se 2 (by rfl) ⟨2439069, by rfl⟩ : syracuseStep 6504185 = 4878139) B4878139
theorem B3211001 : Blo 1425532 3211001 := bstep (se 2 (by rfl) ⟨1204125, by rfl⟩ : syracuseStep 3211001 = 2408251) B2408251
theorem B15417155 : Blo 1425532 15417155 := bstep (se 1 (by rfl) ⟨11562866, by rfl⟩ : syracuseStep 15417155 = 23125733) B23125733
theorem B1605595 : Blo 1425532 1605595 := bstep (se 1 (by rfl) ⟨1204196, by rfl⟩ : syracuseStep 1605595 = 2408393) B2408393
theorem B5414921 : Blo 1425532 5414921 := bstep (se 2 (by rfl) ⟨2030595, by rfl⟩ : syracuseStep 5414921 = 4061191) B4061191
theorem B27435185 : Blo 1425532 27435185 := bstep (se 2 (by rfl) ⟨10288194, by rfl⟩ : syracuseStep 27435185 = 20576389) B20576389
theorem B6856913 : Blo 1425532 6856913 := bstep (se 2 (by rfl) ⟨2571342, by rfl⟩ : syracuseStep 6856913 = 5142685) B5142685
theorem B3612883 : Blo 1425532 3612883 := bstep (se 1 (by rfl) ⟨2709662, by rfl⟩ : syracuseStep 3612883 = 5419325) B5419325
theorem B1425695 : Blo 1425532 1425695 := bstep (se 1 (by rfl) ⟨1069271, by rfl⟩ : syracuseStep 1425695 = 2138543) B2138543
theorem B1605919 : Blo 1425532 1605919 := bstep (se 1 (by rfl) ⟨1204439, by rfl⟩ : syracuseStep 1605919 = 2408879) B2408879
theorem B2138459 : Blo 1425532 2138459 := bstep (se 1 (by rfl) ⟨1603844, by rfl⟩ : syracuseStep 2138459 = 3207689) B3207689
theorem B1425755 : Blo 1425532 1425755 := bstep (se 1 (by rfl) ⟨1069316, by rfl⟩ : syracuseStep 1425755 = 2138633) B2138633
theorem B1425775 : Blo 1425532 1425775 := bstep (se 1 (by rfl) ⟨1069331, by rfl⟩ : syracuseStep 1425775 = 2138663) B2138663
theorem B3211631 : Blo 1425532 3211631 := bstep (se 1 (by rfl) ⟨2408723, by rfl⟩ : syracuseStep 3211631 = 4817447) B4817447
theorem B1425831 : Blo 1425532 1425831 := bstep (se 1 (by rfl) ⟨1069373, by rfl⟩ : syracuseStep 1425831 = 2138747) B2138747
theorem B3211703 : Blo 1425532 3211703 := bstep (se 1 (by rfl) ⟨2408777, by rfl⟩ : syracuseStep 3211703 = 4817555) B4817555
theorem B1425915 : Blo 1425532 1425915 := bstep (se 1 (by rfl) ⟨1069436, by rfl⟩ : syracuseStep 1425915 = 2138873) B2138873
theorem B2138687 : Blo 1425532 2138687 := bstep (se 1 (by rfl) ⟨1604015, by rfl⟩ : syracuseStep 2138687 = 3208031) B3208031
theorem B1425983 : Blo 1425532 1425983 := bstep (se 1 (by rfl) ⟨1069487, by rfl⟩ : syracuseStep 1425983 = 2138975) B2138975
theorem B1425991 : Blo 1425532 1425991 := bstep (se 1 (by rfl) ⟨1069493, by rfl⟩ : syracuseStep 1425991 = 2138987) B2138987
theorem B3211847 : Blo 1425532 3211847 := bstep (se 1 (by rfl) ⟨2408885, by rfl⟩ : syracuseStep 3211847 = 4817771) B4817771
theorem B46301797 : Blo 1425532 46301797 := bstep (se 4 (by rfl) ⟨4340793, by rfl⟩ : syracuseStep 46301797 = 8681587) B8681587
theorem B3211883 : Blo 1425532 3211883 := bstep (se 1 (by rfl) ⟨2408912, by rfl⟩ : syracuseStep 3211883 = 4817825) B4817825
theorem B7226009 : Blo 1425532 7226009 := bstep (se 2 (by rfl) ⟨2709753, by rfl⟩ : syracuseStep 7226009 = 5419507) B5419507
theorem B26026667 : Blo 1425532 26026667 := bstep (se 1 (by rfl) ⟨19520000, by rfl⟩ : syracuseStep 26026667 = 39040001) B39040001
theorem B2138807 : Blo 1425532 2138807 := bstep (se 1 (by rfl) ⟨1604105, by rfl⟩ : syracuseStep 2138807 = 3208211) B3208211
theorem B24371927 : Blo 1425532 24371927 := bstep (se 1 (by rfl) ⟨18278945, by rfl⟩ : syracuseStep 24371927 = 36557891) B36557891
theorem B1426143 : Blo 1425532 1426143 := bstep (se 1 (by rfl) ⟨1069607, by rfl⟩ : syracuseStep 1426143 = 2139215) B2139215
theorem B1426223 : Blo 1425532 1426223 := bstep (se 1 (by rfl) ⟨1069667, by rfl⟩ : syracuseStep 1426223 = 2139335) B2139335
theorem B9266015 : Blo 1425532 9266015 := bstep (se 1 (by rfl) ⟨6949511, by rfl⟩ : syracuseStep 9266015 = 13899023) B13899023
theorem B6857567 : Blo 1425532 6857567 := bstep (se 1 (by rfl) ⟨5143175, by rfl⟩ : syracuseStep 6857567 = 10286351) B10286351
theorem B2139035 : Blo 1425532 2139035 := bstep (se 1 (by rfl) ⟨1604276, by rfl⟩ : syracuseStep 2139035 = 3208553) B3208553
theorem B1426331 : Blo 1425532 1426331 := bstep (se 1 (by rfl) ⟨1069748, by rfl⟩ : syracuseStep 1426331 = 2139497) B2139497
theorem B19514305 : Blo 1425532 19514305 := bstep (se 2 (by rfl) ⟨7317864, by rfl⟩ : syracuseStep 19514305 = 14635729) B14635729
theorem B1426383 : Blo 1425532 1426383 := bstep (se 1 (by rfl) ⟨1069787, by rfl⟩ : syracuseStep 1426383 = 2139575) B2139575
theorem B1426407 : Blo 1425532 1426407 := bstep (se 1 (by rfl) ⟨1069805, by rfl⟩ : syracuseStep 1426407 = 2139611) B2139611
theorem B7218233 : Blo 1425532 7218233 := bstep (se 2 (by rfl) ⟨2706837, by rfl⟩ : syracuseStep 7218233 = 5413675) B5413675
theorem B4064381 : Blo 1425532 4064381 := bstep (se 3 (by rfl) ⟨762071, by rfl⟩ : syracuseStep 4064381 = 1524143) B1524143
theorem B3425419 : Blo 1425532 3425419 := bstep (se 1 (by rfl) ⟨2569064, by rfl⟩ : syracuseStep 3425419 = 5138129) B5138129
theorem B1426719 : Blo 1425532 1426719 := bstep (se 1 (by rfl) ⟨1070039, by rfl⟩ : syracuseStep 1426719 = 2140079) B2140079
theorem B2139431 : Blo 1425532 2139431 := bstep (se 1 (by rfl) ⟨1604573, by rfl⟩ : syracuseStep 2139431 = 3209147) B3209147
theorem B1426779 : Blo 1425532 1426779 := bstep (se 1 (by rfl) ⟨1070084, by rfl⟩ : syracuseStep 1426779 = 2140169) B2140169
theorem B7710047 : Blo 1425532 7710047 := bstep (se 1 (by rfl) ⟨5782535, by rfl⟩ : syracuseStep 7710047 = 11565071) B11565071
theorem B1426799 : Blo 1425532 1426799 := bstep (se 1 (by rfl) ⟨1070099, by rfl⟩ : syracuseStep 1426799 = 2140199) B2140199
theorem B2139515 : Blo 1425532 2139515 := bstep (se 1 (by rfl) ⟨1604636, by rfl⟩ : syracuseStep 2139515 = 3209273) B3209273
theorem B1426855 : Blo 1425532 1426855 := bstep (se 1 (by rfl) ⟨1070141, by rfl⟩ : syracuseStep 1426855 = 2140283) B2140283
theorem B12182957 : Blo 1425532 12182957 := bstep (se 3 (by rfl) ⟨2284304, by rfl⟩ : syracuseStep 12182957 = 4568609) B4568609
theorem B2139641 : Blo 1425532 2139641 := bstep (se 2 (by rfl) ⟨802365, by rfl⟩ : syracuseStep 2139641 = 1604731) B1604731
theorem B1426939 : Blo 1425532 1426939 := bstep (se 1 (by rfl) ⟨1070204, by rfl⟩ : syracuseStep 1426939 = 2140409) B2140409
theorem B1427007 : Blo 1425532 1427007 := bstep (se 1 (by rfl) ⟨1070255, by rfl⟩ : syracuseStep 1427007 = 2140511) B2140511
theorem B1427015 : Blo 1425532 1427015 := bstep (se 1 (by rfl) ⟨1070261, by rfl⟩ : syracuseStep 1427015 = 2140523) B2140523
theorem B2139743 : Blo 1425532 2139743 := bstep (se 1 (by rfl) ⟨1604807, by rfl⟩ : syracuseStep 2139743 = 3209615) B3209615
theorem B16246493 : Blo 1425532 16246493 := bstep (se 3 (by rfl) ⟨3046217, by rfl⟩ : syracuseStep 16246493 = 6092435) B6092435
theorem B1427167 : Blo 1425532 1427167 := bstep (se 1 (by rfl) ⟨1070375, by rfl⟩ : syracuseStep 1427167 = 2140751) B2140751
theorem B15427361 : Blo 1425532 15427361 := bstep (se 2 (by rfl) ⟨5785260, by rfl⟩ : syracuseStep 15427361 = 11570521) B11570521
theorem B1427247 : Blo 1425532 1427247 := bstep (se 1 (by rfl) ⟨1070435, by rfl⟩ : syracuseStep 1427247 = 2140871) B2140871
theorem B2139959 : Blo 1425532 2139959 := bstep (se 1 (by rfl) ⟨1604969, by rfl⟩ : syracuseStep 2139959 = 3209939) B3209939
theorem B7710551 : Blo 1425532 7710551 := bstep (se 1 (by rfl) ⟨5782913, by rfl⟩ : syracuseStep 7710551 = 11565827) B11565827
theorem B36571013 : Blo 1425532 36571013 := bstep (se 4 (by rfl) ⟨3428532, by rfl⟩ : syracuseStep 36571013 = 6857065) B6857065
theorem B1427355 : Blo 1425532 1427355 := bstep (se 1 (by rfl) ⟨1070516, by rfl⟩ : syracuseStep 1427355 = 2141033) B2141033
theorem B1427407 : Blo 1425532 1427407 := bstep (se 1 (by rfl) ⟨1070555, by rfl⟩ : syracuseStep 1427407 = 2141111) B2141111
theorem B1427431 : Blo 1425532 1427431 := bstep (se 1 (by rfl) ⟨1070573, by rfl⟩ : syracuseStep 1427431 = 2141147) B2141147
theorem B29288537 : Blo 1425532 29288537 := bstep (se 2 (by rfl) ⟨10983201, by rfl⟩ : syracuseStep 29288537 = 21966403) B21966403
theorem B2140265 : Blo 1425532 2140265 := bstep (se 2 (by rfl) ⟨802599, by rfl⟩ : syracuseStep 2140265 = 1605199) B1605199
theorem B16255241 : Blo 1425532 16255241 := bstep (se 2 (by rfl) ⟨6095715, by rfl⟩ : syracuseStep 16255241 = 12191431) B12191431
theorem B1714555 : Blo 1425532 1714555 := bstep (se 1 (by rfl) ⟨1285916, by rfl⟩ : syracuseStep 1714555 = 2571833) B2571833
theorem B2140583 : Blo 1425532 2140583 := bstep (se 1 (by rfl) ⟨1605437, by rfl⟩ : syracuseStep 2140583 = 3210875) B3210875
theorem B12184019 : Blo 1425532 12184019 := bstep (se 1 (by rfl) ⟨9138014, by rfl⟩ : syracuseStep 12184019 = 18276029) B18276029
theorem B4336123 : Blo 1425532 4336123 := bstep (se 1 (by rfl) ⟨3252092, by rfl⟩ : syracuseStep 4336123 = 6504185) B6504185
theorem B2140667 : Blo 1425532 2140667 := bstep (se 1 (by rfl) ⟨1605500, by rfl⟩ : syracuseStep 2140667 = 3211001) B3211001
theorem B3295865 : Blo 1425532 3295865 := bstep (se 2 (by rfl) ⟨1235949, by rfl⟩ : syracuseStep 3295865 = 2471899) B2471899
theorem B2140793 : Blo 1425532 2140793 := bstep (se 2 (by rfl) ⟨802797, by rfl⟩ : syracuseStep 2140793 = 1605595) B1605595
theorem B2140847 : Blo 1425532 2140847 := bstep (se 1 (by rfl) ⟨1605635, by rfl⟩ : syracuseStep 2140847 = 3211271) B3211271
theorem B2140895 : Blo 1425532 2140895 := bstep (se 1 (by rfl) ⟨1605671, by rfl⟩ : syracuseStep 2140895 = 3211343) B3211343
theorem B6859511 : Blo 1425532 6859511 := bstep (se 1 (by rfl) ⟨5144633, by rfl⟩ : syracuseStep 6859511 = 10289267) B10289267
theorem B2141159 : Blo 1425532 2141159 := bstep (se 1 (by rfl) ⟨1605869, by rfl⟩ : syracuseStep 2141159 = 3211739) B3211739
theorem B5139443 : Blo 1425532 5139443 := bstep (se 1 (by rfl) ⟨3854582, by rfl⟩ : syracuseStep 5139443 = 7709165) B7709165
theorem B4631591 : Blo 1425532 4631591 := bstep (se 1 (by rfl) ⟨3473693, by rfl⟩ : syracuseStep 4631591 = 6947387) B6947387
theorem B7220339 : Blo 1425532 7220339 := bstep (se 1 (by rfl) ⟨5415254, by rfl⟩ : syracuseStep 7220339 = 10830509) B10830509
theorem B3427679 : Blo 1425532 3427679 := bstep (se 1 (by rfl) ⟨2570759, by rfl⟩ : syracuseStep 3427679 = 5141519) B5141519
theorem B1928615 : Blo 1425532 1928615 := bstep (se 1 (by rfl) ⟨1446461, by rfl⟩ : syracuseStep 1928615 = 2892923) B2892923
theorem B13897277 : Blo 1425532 13897277 := bstep (se 3 (by rfl) ⟨2605739, by rfl⟩ : syracuseStep 13897277 = 5211479) B5211479
theorem B4812371 : Blo 1425532 4812371 := bstep (se 1 (by rfl) ⟨3609278, by rfl⟩ : syracuseStep 4812371 = 7218557) B7218557
theorem B5418809 : Blo 1425532 5418809 := bstep (se 2 (by rfl) ⟨2032053, by rfl⟩ : syracuseStep 5418809 = 4064107) B4064107
theorem B7221149 : Blo 1425532 7221149 := bstep (se 3 (by rfl) ⟨1353965, by rfl⟩ : syracuseStep 7221149 = 2707931) B2707931
theorem B8122427 : Blo 1425532 8122427 := bstep (se 1 (by rfl) ⟨6091820, by rfl⟩ : syracuseStep 8122427 = 12183641) B12183641
theorem B9261161 : Blo 1425532 9261161 := bstep (se 2 (by rfl) ⟨3472935, by rfl⟩ : syracuseStep 9261161 = 6945871) B6945871
theorem B13709483 : Blo 1425532 13709483 := bstep (se 1 (by rfl) ⟨10282112, by rfl⟩ : syracuseStep 13709483 = 20564225) B20564225
theorem B29282633 : Blo 1425532 29282633 := bstep (se 2 (by rfl) ⟨10980987, by rfl⟩ : syracuseStep 29282633 = 21961975) B21961975
theorem B15413611 : Blo 1425532 15413611 := bstep (se 1 (by rfl) ⟨11560208, by rfl⟩ : syracuseStep 15413611 = 23120417) B23120417
theorem B1806715 : Blo 1425532 1806715 := bstep (se 1 (by rfl) ⟨1355036, by rfl⟩ : syracuseStep 1806715 = 2710073) B2710073
theorem B3207599 : Blo 1425532 3207599 := bstep (se 1 (by rfl) ⟨2405699, by rfl⟩ : syracuseStep 3207599 = 4811399) B4811399
theorem B3207635 : Blo 1425532 3207635 := bstep (se 1 (by rfl) ⟨2405726, by rfl⟩ : syracuseStep 3207635 = 4811453) B4811453
theorem B3609107 : Blo 1425532 3609107 := bstep (se 1 (by rfl) ⟨2706830, by rfl⟩ : syracuseStep 3609107 = 5413661) B5413661
theorem B3207743 : Blo 1425532 3207743 := bstep (se 1 (by rfl) ⟨2405807, by rfl⟩ : syracuseStep 3207743 = 4811615) B4811615
theorem B3207851 : Blo 1425532 3207851 := bstep (se 1 (by rfl) ⟨2405888, by rfl⟩ : syracuseStep 3207851 = 4811777) B4811777
theorem B6091463 : Blo 1425532 6091463 := bstep (se 1 (by rfl) ⟨4568597, by rfl⟩ : syracuseStep 6091463 = 9137195) B9137195
theorem B7221959 : Blo 1425532 7221959 := bstep (se 1 (by rfl) ⟨5416469, by rfl⟩ : syracuseStep 7221959 = 10832939) B10832939
theorem B43897601 : Blo 1425532 43897601 := bstep (se 2 (by rfl) ⟨16461600, by rfl⟩ : syracuseStep 43897601 = 32923201) B32923201
theorem B4059983 : Blo 1425532 4059983 := bstep (se 1 (by rfl) ⟨3044987, by rfl⟩ : syracuseStep 4059983 = 6089975) B6089975
theorem B5862223 : Blo 1425532 5862223 := bstep (se 1 (by rfl) ⟨4396667, by rfl⟩ : syracuseStep 5862223 = 8793335) B8793335
theorem B6091615 : Blo 1425532 6091615 := bstep (se 1 (by rfl) ⟨4568711, by rfl⟩ : syracuseStep 6091615 = 9137423) B9137423
theorem B2708471 : Blo 1425532 2708471 := bstep (se 1 (by rfl) ⟨2031353, by rfl⟩ : syracuseStep 2708471 = 4062707) B4062707
theorem B3208391 : Blo 1425532 3208391 := bstep (se 1 (by rfl) ⟨2406293, by rfl⟩ : syracuseStep 3208391 = 4812587) B4812587
theorem B10278103 : Blo 1425532 10278103 := bstep (se 1 (by rfl) ⟨7708577, by rfl⟩ : syracuseStep 10278103 = 15417155) B15417155
theorem B3208571 : Blo 1425532 3208571 := bstep (se 1 (by rfl) ⟨2406428, by rfl⟩ : syracuseStep 3208571 = 4812857) B4812857
theorem B2708873 : Blo 1425532 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B8123885 : Blo 1425532 8123885 := bstep (se 3 (by rfl) ⟨1523228, by rfl⟩ : syracuseStep 8123885 = 3046457) B3046457
theorem B3208697 : Blo 1425532 3208697 := bstep (se 2 (by rfl) ⟨1203261, by rfl⟩ : syracuseStep 3208697 = 2406523) B2406523
theorem B18282023 : Blo 1425532 18282023 := bstep (se 1 (by rfl) ⟨13711517, by rfl⟩ : syracuseStep 18282023 = 27423035) B27423035
theorem B3208787 : Blo 1425532 3208787 := bstep (se 1 (by rfl) ⟨2406590, by rfl⟩ : syracuseStep 3208787 = 4813181) B4813181
theorem B2405983 : Blo 1425532 2405983 := bstep (se 1 (by rfl) ⟨1804487, by rfl⟩ : syracuseStep 2405983 = 3608975) B3608975
theorem B3208967 : Blo 1425532 3208967 := bstep (se 1 (by rfl) ⟨2406725, by rfl⟩ : syracuseStep 3208967 = 4813451) B4813451
theorem B2406199 : Blo 1425532 2406199 := bstep (se 1 (by rfl) ⟨1804649, by rfl⟩ : syracuseStep 2406199 = 3609299) B3609299
theorem B5412689 : Blo 1425532 5412689 := bstep (se 2 (by rfl) ⟨2029758, by rfl⟩ : syracuseStep 5412689 = 4059517) B4059517
theorem B44546183 : Blo 1425532 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B2406665 : Blo 1425532 2406665 := bstep (se 2 (by rfl) ⟨902499, by rfl⟩ : syracuseStep 2406665 = 1804999) B1804999
theorem B3610889 : Blo 1425532 3610889 := bstep (se 2 (by rfl) ⟨1354083, by rfl⟩ : syracuseStep 3610889 = 2708167) B2708167
theorem B2709769 : Blo 1425532 2709769 := bstep (se 2 (by rfl) ⟨1016163, by rfl⟩ : syracuseStep 2709769 = 2032327) B2032327
theorem B4061465 : Blo 1425532 4061465 := bstep (se 2 (by rfl) ⟨1523049, by rfl⟩ : syracuseStep 4061465 = 3046099) B3046099
theorem B3209579 : Blo 1425532 3209579 := bstep (se 1 (by rfl) ⟨2407184, by rfl⟩ : syracuseStep 3209579 = 4814369) B4814369
theorem B5487031 : Blo 1425532 5487031 := bstep (se 1 (by rfl) ⟨4115273, by rfl⟩ : syracuseStep 5487031 = 8230547) B8230547
theorem B4815287 : Blo 1425532 4815287 := bstep (se 1 (by rfl) ⟨3611465, by rfl⟩ : syracuseStep 4815287 = 7222931) B7222931
theorem B7707109 : Blo 1425532 7707109 := bstep (se 4 (by rfl) ⟨722541, by rfl⟩ : syracuseStep 7707109 = 1445083) B1445083
theorem B3209723 : Blo 1425532 3209723 := bstep (se 1 (by rfl) ⟨2407292, by rfl⟩ : syracuseStep 3209723 = 4814585) B4814585
theorem B1604191 : Blo 1425532 1604191 := bstep (se 1 (by rfl) ⟨1203143, by rfl⟩ : syracuseStep 1604191 = 2406287) B2406287
theorem B3611243 : Blo 1425532 3611243 := bstep (se 1 (by rfl) ⟨2708432, by rfl⟩ : syracuseStep 3611243 = 5416865) B5416865
theorem B3209849 : Blo 1425532 3209849 := bstep (se 2 (by rfl) ⟨1203693, by rfl⟩ : syracuseStep 3209849 = 2407387) B2407387
theorem B10566283 : Blo 1425532 10566283 := bstep (se 1 (by rfl) ⟨7924712, by rfl⟩ : syracuseStep 10566283 = 15849425) B15849425
theorem B3209903 : Blo 1425532 3209903 := bstep (se 1 (by rfl) ⟨2407427, by rfl⟩ : syracuseStep 3209903 = 4814855) B4814855
theorem B3209975 : Blo 1425532 3209975 := bstep (se 1 (by rfl) ⟨2407481, by rfl⟩ : syracuseStep 3209975 = 4814963) B4814963
theorem B41720579 : Blo 1425532 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B16071443 : Blo 1425532 16071443 := bstep (se 1 (by rfl) ⟨12053582, by rfl⟩ : syracuseStep 16071443 = 24107165) B24107165
theorem B59390749 : Blo 1425532 59390749 := bstep (se 3 (by rfl) ⟨11135765, by rfl⟩ : syracuseStep 59390749 = 22271531) B22271531
theorem B3210155 : Blo 1425532 3210155 := bstep (se 1 (by rfl) ⟨2407616, by rfl⟩ : syracuseStep 3210155 = 4815233) B4815233
theorem B13007789 : Blo 1425532 13007789 := bstep (se 3 (by rfl) ⟨2438960, by rfl⟩ : syracuseStep 13007789 = 4877921) B4877921
theorem B2407657 : Blo 1425532 2407657 := bstep (se 2 (by rfl) ⟨902871, by rfl⟩ : syracuseStep 2407657 = 1805743) B1805743
theorem B3611891 : Blo 1425532 3611891 := bstep (se 1 (by rfl) ⟨2708918, by rfl⟩ : syracuseStep 3611891 = 5417837) B5417837
theorem B2407711 : Blo 1425532 2407711 := bstep (se 1 (by rfl) ⟨1805783, by rfl⟩ : syracuseStep 2407711 = 3611567) B3611567
theorem B3661193 : Blo 1425532 3661193 := bstep (se 2 (by rfl) ⟨1372947, by rfl⟩ : syracuseStep 3661193 = 2745895) B2745895
theorem B7224713 : Blo 1425532 7224713 := bstep (se 2 (by rfl) ⟨2709267, by rfl⟩ : syracuseStep 7224713 = 5418535) B5418535
theorem B1523143 : Blo 1425532 1523143 := bstep (se 1 (by rfl) ⟨1142357, by rfl⟩ : syracuseStep 1523143 = 2284715) B2284715
theorem B3210695 : Blo 1425532 3210695 := bstep (se 1 (by rfl) ⟨2408021, by rfl⟩ : syracuseStep 3210695 = 4816043) B4816043
theorem B2031097 : Blo 1425532 2031097 := bstep (se 2 (by rfl) ⟨761661, by rfl⟩ : syracuseStep 2031097 = 1523323) B1523323
theorem B5144057 : Blo 1425532 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B14630483 : Blo 1425532 14630483 := bstep (se 1 (by rfl) ⟨10972862, by rfl⟩ : syracuseStep 14630483 = 21945725) B21945725
theorem B2408123 : Blo 1425532 2408123 := bstep (se 1 (by rfl) ⟨1806092, by rfl⟩ : syracuseStep 2408123 = 3612185) B3612185
theorem B3612347 : Blo 1425532 3612347 := bstep (se 1 (by rfl) ⟨2709260, by rfl⟩ : syracuseStep 3612347 = 5418521) B5418521
theorem B1605343 : Blo 1425532 1605343 := bstep (se 1 (by rfl) ⟨1204007, by rfl⟩ : syracuseStep 1605343 = 2408015) B2408015
theorem B6856451 : Blo 1425532 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B7216937 : Blo 1425532 7216937 := bstep (se 2 (by rfl) ⟨2706351, by rfl⟩ : syracuseStep 7216937 = 5412703) B5412703
theorem B3211055 : Blo 1425532 3211055 := bstep (se 1 (by rfl) ⟨2408291, by rfl⟩ : syracuseStep 3211055 = 4816583) B4816583
theorem B1785655 : Blo 1425532 1785655 := bstep (se 1 (by rfl) ⟨1339241, by rfl⟩ : syracuseStep 1785655 = 2678483) B2678483
theorem B5414951 : Blo 1425532 5414951 := bstep (se 1 (by rfl) ⟨4061213, by rfl⟩ : syracuseStep 5414951 = 8122427) B8122427
theorem B4571275 : Blo 1425532 4571275 := bstep (se 1 (by rfl) ⟨3428456, by rfl⟩ : syracuseStep 4571275 = 6856913) B6856913
theorem B19521755 : Blo 1425532 19521755 := bstep (se 1 (by rfl) ⟨14641316, by rfl⟩ : syracuseStep 19521755 = 29282633) B29282633
theorem B1425639 : Blo 1425532 1425639 := bstep (se 1 (by rfl) ⟨1069229, by rfl⟩ : syracuseStep 1425639 = 2138459) B2138459
theorem B4817177 : Blo 1425532 4817177 := bstep (se 2 (by rfl) ⟨1806441, by rfl⟩ : syracuseStep 4817177 = 3612883) B3612883
theorem B2138399 : Blo 1425532 2138399 := bstep (se 1 (by rfl) ⟨1603799, by rfl⟩ : syracuseStep 2138399 = 3207599) B3207599
theorem B2138423 : Blo 1425532 2138423 := bstep (se 1 (by rfl) ⟨1603817, by rfl⟩ : syracuseStep 2138423 = 3207635) B3207635
theorem B3613025 : Blo 1425532 3613025 := bstep (se 2 (by rfl) ⟨1354884, by rfl⟩ : syracuseStep 3613025 = 2709769) B2709769
theorem B2138495 : Blo 1425532 2138495 := bstep (se 1 (by rfl) ⟨1603871, by rfl⟩ : syracuseStep 2138495 = 3207743) B3207743
theorem B1425791 : Blo 1425532 1425791 := bstep (se 1 (by rfl) ⟨1069343, by rfl⟩ : syracuseStep 1425791 = 2138687) B2138687
theorem B4817339 : Blo 1425532 4817339 := bstep (se 1 (by rfl) ⟨3613004, by rfl⟩ : syracuseStep 4817339 = 7226009) B7226009
theorem B2138567 : Blo 1425532 2138567 := bstep (se 1 (by rfl) ⟨1603925, by rfl⟩ : syracuseStep 2138567 = 3207851) B3207851
theorem B17351111 : Blo 1425532 17351111 := bstep (se 1 (by rfl) ⟨13013333, by rfl⟩ : syracuseStep 17351111 = 26026667) B26026667
theorem B1425871 : Blo 1425532 1425871 := bstep (se 1 (by rfl) ⟨1069403, by rfl⟩ : syracuseStep 1425871 = 2138807) B2138807
theorem B2286073 : Blo 1425532 2286073 := bstep (se 2 (by rfl) ⟨857277, by rfl⟩ : syracuseStep 2286073 = 1714555) B1714555
theorem B2408953 : Blo 1425532 2408953 := bstep (se 2 (by rfl) ⟨903357, by rfl⟩ : syracuseStep 2408953 = 1806715) B1806715
theorem B4571711 : Blo 1425532 4571711 := bstep (se 1 (by rfl) ⟨3428783, by rfl⟩ : syracuseStep 4571711 = 6857567) B6857567
theorem B1426023 : Blo 1425532 1426023 := bstep (se 1 (by rfl) ⟨1069517, by rfl⟩ : syracuseStep 1426023 = 2139035) B2139035
theorem B18268901 : Blo 1425532 18268901 := bstep (se 4 (by rfl) ⟨1712709, by rfl⟩ : syracuseStep 18268901 = 3425419) B3425419
theorem B2138921 : Blo 1425532 2138921 := bstep (se 2 (by rfl) ⟨802095, by rfl⟩ : syracuseStep 2138921 = 1604191) B1604191
theorem B2138927 : Blo 1425532 2138927 := bstep (se 1 (by rfl) ⟨1604195, by rfl⟩ : syracuseStep 2138927 = 3208391) B3208391
theorem B61735729 : Blo 1425532 61735729 := bstep (se 2 (by rfl) ⟨23150898, by rfl⟩ : syracuseStep 61735729 = 46301797) B46301797
theorem B1426287 : Blo 1425532 1426287 := bstep (se 1 (by rfl) ⟨1069715, by rfl⟩ : syracuseStep 1426287 = 2139431) B2139431
theorem B2139047 : Blo 1425532 2139047 := bstep (se 1 (by rfl) ⟨1604285, by rfl⟩ : syracuseStep 2139047 = 3208571) B3208571
theorem B1426343 : Blo 1425532 1426343 := bstep (se 1 (by rfl) ⟨1069757, by rfl⟩ : syracuseStep 1426343 = 2139515) B2139515
theorem B5415923 : Blo 1425532 5415923 := bstep (se 1 (by rfl) ⟨4061942, by rfl⟩ : syracuseStep 5415923 = 8123885) B8123885
theorem B2139131 : Blo 1425532 2139131 := bstep (se 1 (by rfl) ⟨1604348, by rfl⟩ : syracuseStep 2139131 = 3208697) B3208697
theorem B1426427 : Blo 1425532 1426427 := bstep (se 1 (by rfl) ⟨1069820, by rfl⟩ : syracuseStep 1426427 = 2139641) B2139641
theorem B2139191 : Blo 1425532 2139191 := bstep (se 1 (by rfl) ⟨1604393, by rfl⟩ : syracuseStep 2139191 = 3208787) B3208787
theorem B1426495 : Blo 1425532 1426495 := bstep (se 1 (by rfl) ⟨1069871, by rfl⟩ : syracuseStep 1426495 = 2139743) B2139743
theorem B7816297 : Blo 1425532 7816297 := bstep (se 2 (by rfl) ⟨2931111, by rfl⟩ : syracuseStep 7816297 = 5862223) B5862223
theorem B10830995 : Blo 1425532 10830995 := bstep (se 1 (by rfl) ⟨8123246, by rfl⟩ : syracuseStep 10830995 = 16246493) B16246493
theorem B2139311 : Blo 1425532 2139311 := bstep (se 1 (by rfl) ⟨1604483, by rfl⟩ : syracuseStep 2139311 = 3208967) B3208967
theorem B1426639 : Blo 1425532 1426639 := bstep (se 1 (by rfl) ⟨1069979, by rfl⟩ : syracuseStep 1426639 = 2139959) B2139959
theorem B26019073 : Blo 1425532 26019073 := bstep (se 2 (by rfl) ⟨9757152, by rfl⟩ : syracuseStep 26019073 = 19514305) B19514305
theorem B24380675 : Blo 1425532 24380675 := bstep (se 1 (by rfl) ⟨18285506, by rfl⟩ : syracuseStep 24380675 = 36571013) B36571013
theorem B1426843 : Blo 1425532 1426843 := bstep (se 1 (by rfl) ⟨1070132, by rfl⟩ : syracuseStep 1426843 = 2140265) B2140265
theorem B29697455 : Blo 1425532 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B2139719 : Blo 1425532 2139719 := bstep (se 1 (by rfl) ⟨1604789, by rfl⟩ : syracuseStep 2139719 = 3209579) B3209579
theorem B1427055 : Blo 1425532 1427055 := bstep (se 1 (by rfl) ⟨1070291, by rfl⟩ : syracuseStep 1427055 = 2140583) B2140583
theorem B2139815 : Blo 1425532 2139815 := bstep (se 1 (by rfl) ⟨1604861, by rfl⟩ : syracuseStep 2139815 = 3209723) B3209723
theorem B1427111 : Blo 1425532 1427111 := bstep (se 1 (by rfl) ⟨1070333, by rfl⟩ : syracuseStep 1427111 = 2140667) B2140667
theorem B20571893 : Blo 1425532 20571893 := bstep (se 5 (by rfl) ⟨964307, by rfl⟩ : syracuseStep 20571893 = 1928615) B1928615
theorem B2197243 : Blo 1425532 2197243 := bstep (se 1 (by rfl) ⟨1647932, by rfl⟩ : syracuseStep 2197243 = 3295865) B3295865
theorem B2139899 : Blo 1425532 2139899 := bstep (se 1 (by rfl) ⟨1604924, by rfl⟩ : syracuseStep 2139899 = 3209849) B3209849
theorem B1427195 : Blo 1425532 1427195 := bstep (se 1 (by rfl) ⟨1070396, by rfl⟩ : syracuseStep 1427195 = 2140793) B2140793
theorem B2139935 : Blo 1425532 2139935 := bstep (se 1 (by rfl) ⟨1604951, by rfl⟩ : syracuseStep 2139935 = 3209903) B3209903
theorem B1427231 : Blo 1425532 1427231 := bstep (se 1 (by rfl) ⟨1070423, by rfl⟩ : syracuseStep 1427231 = 2140847) B2140847
theorem B1427263 : Blo 1425532 1427263 := bstep (se 1 (by rfl) ⟨1070447, by rfl⟩ : syracuseStep 1427263 = 2140895) B2140895
theorem B2139983 : Blo 1425532 2139983 := bstep (se 1 (by rfl) ⟨1604987, by rfl⟩ : syracuseStep 2139983 = 3209975) B3209975
theorem B4573007 : Blo 1425532 4573007 := bstep (se 1 (by rfl) ⟨3429755, by rfl⟩ : syracuseStep 4573007 = 6859511) B6859511
theorem B27813719 : Blo 1425532 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B2140103 : Blo 1425532 2140103 := bstep (se 1 (by rfl) ⟨1605077, by rfl⟩ : syracuseStep 2140103 = 3210155) B3210155
theorem B1427439 : Blo 1425532 1427439 := bstep (se 1 (by rfl) ⟨1070579, by rfl⟩ : syracuseStep 1427439 = 2141159) B2141159
theorem B3426295 : Blo 1425532 3426295 := bstep (se 1 (by rfl) ⟨2569721, by rfl⟩ : syracuseStep 3426295 = 5139443) B5139443
theorem B24709373 : Blo 1425532 24709373 := bstep (se 3 (by rfl) ⟨4633007, by rfl⟩ : syracuseStep 24709373 = 9266015) B9266015
theorem B29264165 : Blo 1425532 29264165 := bstep (se 4 (by rfl) ⟨2743515, by rfl⟩ : syracuseStep 29264165 = 5487031) B5487031
theorem B2140457 : Blo 1425532 2140457 := bstep (se 2 (by rfl) ⟨802671, by rfl⟩ : syracuseStep 2140457 = 1605343) B1605343
theorem B2140463 : Blo 1425532 2140463 := bstep (se 1 (by rfl) ⟨1605347, by rfl⟩ : syracuseStep 2140463 = 3210695) B3210695
theorem B4811291 : Blo 1425532 4811291 := bstep (se 1 (by rfl) ⟨3608468, by rfl⟩ : syracuseStep 4811291 = 7216937) B7216937
theorem B2140703 : Blo 1425532 2140703 := bstep (se 1 (by rfl) ⟨1605527, by rfl⟩ : syracuseStep 2140703 = 3211055) B3211055
theorem B2141087 : Blo 1425532 2141087 := bstep (se 1 (by rfl) ⟨1605815, by rfl⟩ : syracuseStep 2141087 = 3211631) B3211631
theorem B2141135 : Blo 1425532 2141135 := bstep (se 1 (by rfl) ⟨1605851, by rfl⟩ : syracuseStep 2141135 = 3211703) B3211703
theorem B2141225 : Blo 1425532 2141225 := bstep (se 2 (by rfl) ⟨802959, by rfl⟩ : syracuseStep 2141225 = 1605919) B1605919
theorem B2141231 : Blo 1425532 2141231 := bstep (se 1 (by rfl) ⟨1605923, by rfl⟩ : syracuseStep 2141231 = 3211847) B3211847
theorem B2141255 : Blo 1425532 2141255 := bstep (se 1 (by rfl) ⟨1605941, by rfl⟩ : syracuseStep 2141255 = 3211883) B3211883
theorem B16247951 : Blo 1425532 16247951 := bstep (se 1 (by rfl) ⟨12185963, by rfl⟩ : syracuseStep 16247951 = 24371927) B24371927
theorem B29265067 : Blo 1425532 29265067 := bstep (se 1 (by rfl) ⟨21948800, by rfl⟩ : syracuseStep 29265067 = 43897601) B43897601
theorem B10276145 : Blo 1425532 10276145 := bstep (se 2 (by rfl) ⟨3853554, by rfl⟩ : syracuseStep 10276145 = 7707109) B7707109
theorem B1805647 : Blo 1425532 1805647 := bstep (se 1 (by rfl) ⟨1354235, by rfl⟩ : syracuseStep 1805647 = 2708471) B2708471
theorem B4812155 : Blo 1425532 4812155 := bstep (se 1 (by rfl) ⟨3609116, by rfl⟩ : syracuseStep 4812155 = 7218233) B7218233
theorem B5140031 : Blo 1425532 5140031 := bstep (se 1 (by rfl) ⟨3855023, by rfl⟩ : syracuseStep 5140031 = 7710047) B7710047
theorem B1805915 : Blo 1425532 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B8121971 : Blo 1425532 8121971 := bstep (se 1 (by rfl) ⟨6091478, by rfl⟩ : syracuseStep 8121971 = 12182957) B12182957
theorem B8122153 : Blo 1425532 8122153 := bstep (se 2 (by rfl) ⟨3045807, by rfl⟩ : syracuseStep 8122153 = 6091615) B6091615
theorem B10284907 : Blo 1425532 10284907 := bstep (se 1 (by rfl) ⟨7713680, by rfl⟩ : syracuseStep 10284907 = 15427361) B15427361
theorem B3608459 : Blo 1425532 3608459 := bstep (se 1 (by rfl) ⟨2706344, by rfl⟩ : syracuseStep 3608459 = 5412689) B5412689
theorem B5140367 : Blo 1425532 5140367 := bstep (se 1 (by rfl) ⟨3855275, by rfl⟩ : syracuseStep 5140367 = 7710551) B7710551
theorem B19525691 : Blo 1425532 19525691 := bstep (se 1 (by rfl) ⟨14644268, by rfl⟩ : syracuseStep 19525691 = 29288537) B29288537
theorem B2707643 : Blo 1425532 2707643 := bstep (se 1 (by rfl) ⟨2030732, by rfl⟩ : syracuseStep 2707643 = 4061465) B4061465
theorem B9523493 : Blo 1425532 9523493 := bstep (se 4 (by rfl) ⟨892827, by rfl⟩ : syracuseStep 9523493 = 1785655) B1785655
theorem B8122679 : Blo 1425532 8122679 := bstep (se 1 (by rfl) ⟨6092009, by rfl⟩ : syracuseStep 8122679 = 12184019) B12184019
theorem B8671859 : Blo 1425532 8671859 := bstep (se 1 (by rfl) ⟨6503894, by rfl⟩ : syracuseStep 8671859 = 13007789) B13007789
theorem B2708129 : Blo 1425532 2708129 := bstep (se 2 (by rfl) ⟨1015548, by rfl⟩ : syracuseStep 2708129 = 2031097) B2031097
theorem B4813559 : Blo 1425532 4813559 := bstep (se 1 (by rfl) ⟨3610169, by rfl⟩ : syracuseStep 4813559 = 7220339) B7220339
theorem B3207977 : Blo 1425532 3207977 := bstep (se 2 (by rfl) ⟨1202991, by rfl⟩ : syracuseStep 3207977 = 2405983) B2405983
theorem B10826621 : Blo 1425532 10826621 := bstep (se 3 (by rfl) ⟨2029991, by rfl⟩ : syracuseStep 10826621 = 4059983) B4059983
theorem B3429371 : Blo 1425532 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B8123429 : Blo 1425532 8123429 := bstep (se 4 (by rfl) ⟨761571, by rfl⟩ : syracuseStep 8123429 = 1523143) B1523143
theorem B9753655 : Blo 1425532 9753655 := bstep (se 1 (by rfl) ⟨7315241, by rfl⟩ : syracuseStep 9753655 = 14630483) B14630483
theorem B3208247 : Blo 1425532 3208247 := bstep (se 1 (by rfl) ⟨2406185, by rfl⟩ : syracuseStep 3208247 = 4812371) B4812371
theorem B3208265 : Blo 1425532 3208265 := bstep (se 2 (by rfl) ⟨1203099, by rfl⟩ : syracuseStep 3208265 = 2406199) B2406199
theorem B4814099 : Blo 1425532 4814099 := bstep (se 1 (by rfl) ⟨3610574, by rfl⟩ : syracuseStep 4814099 = 7221149) B7221149
theorem B3609947 : Blo 1425532 3609947 := bstep (se 1 (by rfl) ⟨2707460, by rfl⟩ : syracuseStep 3609947 = 5414921) B5414921
theorem B6174107 : Blo 1425532 6174107 := bstep (se 1 (by rfl) ⟨4630580, by rfl⟩ : syracuseStep 6174107 = 9261161) B9261161
theorem B9139655 : Blo 1425532 9139655 := bstep (se 1 (by rfl) ⟨6854741, by rfl⟩ : syracuseStep 9139655 = 13709483) B13709483
theorem B18290123 : Blo 1425532 18290123 := bstep (se 1 (by rfl) ⟨13717592, by rfl⟩ : syracuseStep 18290123 = 27435185) B27435185
theorem B2406071 : Blo 1425532 2406071 := bstep (se 1 (by rfl) ⟨1804553, by rfl⟩ : syracuseStep 2406071 = 3609107) B3609107
theorem B4060975 : Blo 1425532 4060975 := bstep (se 1 (by rfl) ⟨3045731, by rfl⟩ : syracuseStep 4060975 = 6091463) B6091463
theorem B4814639 : Blo 1425532 4814639 := bstep (se 1 (by rfl) ⟨3610979, by rfl⟩ : syracuseStep 4814639 = 7221959) B7221959
theorem B20551481 : Blo 1425532 20551481 := bstep (se 2 (by rfl) ⟨7706805, by rfl⟩ : syracuseStep 20551481 = 15413611) B15413611
theorem B5781497 : Blo 1425532 5781497 := bstep (se 2 (by rfl) ⟨2168061, by rfl⟩ : syracuseStep 5781497 = 4336123) B4336123
theorem B2709587 : Blo 1425532 2709587 := bstep (se 1 (by rfl) ⟨2032190, by rfl⟩ : syracuseStep 2709587 = 4064381) B4064381
theorem B14088377 : Blo 1425532 14088377 := bstep (se 2 (by rfl) ⟨5283141, by rfl⟩ : syracuseStep 14088377 = 10566283) B10566283
theorem B12188015 : Blo 1425532 12188015 := bstep (se 1 (by rfl) ⟨9141011, by rfl⟩ : syracuseStep 12188015 = 18282023) B18282023
theorem B316750661 : Blo 1425532 316750661 := bstep (se 4 (by rfl) ⟨29695374, by rfl⟩ : syracuseStep 316750661 = 59390749) B59390749
theorem B1604443 : Blo 1425532 1604443 := bstep (se 1 (by rfl) ⟨1203332, by rfl⟩ : syracuseStep 1604443 = 2406665) B2406665
theorem B2407259 : Blo 1425532 2407259 := bstep (se 1 (by rfl) ⟨1805444, by rfl⟩ : syracuseStep 2407259 = 3610889) B3610889
theorem B10836827 : Blo 1425532 10836827 := bstep (se 1 (by rfl) ⟨8127620, by rfl⟩ : syracuseStep 10836827 = 16255241) B16255241
theorem B13704137 : Blo 1425532 13704137 := bstep (se 2 (by rfl) ⟨5139051, by rfl⟩ : syracuseStep 13704137 = 10278103) B10278103
theorem B3210191 : Blo 1425532 3210191 := bstep (se 1 (by rfl) ⟨2407643, by rfl⟩ : syracuseStep 3210191 = 4815287) B4815287
theorem B3210209 : Blo 1425532 3210209 := bstep (se 2 (by rfl) ⟨1203828, by rfl⟩ : syracuseStep 3210209 = 2407657) B2407657
theorem B3210281 : Blo 1425532 3210281 := bstep (se 2 (by rfl) ⟨1203855, by rfl⟩ : syracuseStep 3210281 = 2407711) B2407711
theorem B2407495 : Blo 1425532 2407495 := bstep (se 1 (by rfl) ⟨1805621, by rfl⟩ : syracuseStep 2407495 = 3611243) B3611243
theorem B10714295 : Blo 1425532 10714295 := bstep (se 1 (by rfl) ⟨8035721, by rfl⟩ : syracuseStep 10714295 = 16071443) B16071443
theorem B3087727 : Blo 1425532 3087727 := bstep (se 1 (by rfl) ⟨2315795, by rfl⟩ : syracuseStep 3087727 = 4631591) B4631591
theorem B2407927 : Blo 1425532 2407927 := bstep (se 1 (by rfl) ⟨1805945, by rfl⟩ : syracuseStep 2407927 = 3611891) B3611891
theorem B2285119 : Blo 1425532 2285119 := bstep (se 1 (by rfl) ⟨1713839, by rfl⟩ : syracuseStep 2285119 = 3427679) B3427679
theorem B2440795 : Blo 1425532 2440795 := bstep (se 1 (by rfl) ⟨1830596, by rfl⟩ : syracuseStep 2440795 = 3661193) B3661193
theorem B4816475 : Blo 1425532 4816475 := bstep (se 1 (by rfl) ⟨3612356, by rfl⟩ : syracuseStep 4816475 = 7224713) B7224713
theorem B9264851 : Blo 1425532 9264851 := bstep (se 1 (by rfl) ⟨6948638, by rfl⟩ : syracuseStep 9264851 = 13897277) B13897277
theorem B1605415 : Blo 1425532 1605415 := bstep (se 1 (by rfl) ⟨1204061, by rfl⟩ : syracuseStep 1605415 = 2408123) B2408123
theorem B2408231 : Blo 1425532 2408231 := bstep (se 1 (by rfl) ⟨1806173, by rfl⟩ : syracuseStep 2408231 = 3612347) B3612347
theorem B4570967 : Blo 1425532 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B3612539 : Blo 1425532 3612539 := bstep (se 1 (by rfl) ⟨2709404, by rfl⟩ : syracuseStep 3612539 = 5418809) B5418809
theorem B13017127 : Blo 1425532 13017127 := bstep (se 1 (by rfl) ⟨9762845, by rfl⟩ : syracuseStep 13017127 = 19525691) B19525691
theorem B6095033 : Blo 1425532 6095033 := bstep (se 2 (by rfl) ⟨2285637, by rfl⟩ : syracuseStep 6095033 = 4571275) B4571275
theorem B3211451 : Blo 1425532 3211451 := bstep (se 1 (by rfl) ⟨2408588, by rfl⟩ : syracuseStep 3211451 = 4817177) B4817177
theorem B1425599 : Blo 1425532 1425599 := bstep (se 1 (by rfl) ⟨1069199, by rfl⟩ : syracuseStep 1425599 = 2138399) B2138399
theorem B6348995 : Blo 1425532 6348995 := bstep (se 1 (by rfl) ⟨4761746, by rfl⟩ : syracuseStep 6348995 = 9523493) B9523493
theorem B1425615 : Blo 1425532 1425615 := bstep (se 1 (by rfl) ⟨1069211, by rfl⟩ : syracuseStep 1425615 = 2138423) B2138423
theorem B5415119 : Blo 1425532 5415119 := bstep (se 1 (by rfl) ⟨4061339, by rfl⟩ : syracuseStep 5415119 = 8122679) B8122679
theorem B2408683 : Blo 1425532 2408683 := bstep (se 1 (by rfl) ⟨1806512, by rfl⟩ : syracuseStep 2408683 = 3613025) B3613025
theorem B1425663 : Blo 1425532 1425663 := bstep (se 1 (by rfl) ⟨1069247, by rfl⟩ : syracuseStep 1425663 = 2138495) B2138495
theorem B3211559 : Blo 1425532 3211559 := bstep (se 1 (by rfl) ⟨2408669, by rfl⟩ : syracuseStep 3211559 = 4817339) B4817339
theorem B1425711 : Blo 1425532 1425711 := bstep (se 1 (by rfl) ⟨1069283, by rfl⟩ : syracuseStep 1425711 = 2138567) B2138567
theorem B3047807 : Blo 1425532 3047807 := bstep (se 1 (by rfl) ⟨2285855, by rfl⟩ : syracuseStep 3047807 = 4571711) B4571711
theorem B37569005 : Blo 1425532 37569005 := bstep (se 3 (by rfl) ⟨7044188, by rfl⟩ : syracuseStep 37569005 = 14088377) B14088377
theorem B2138651 : Blo 1425532 2138651 := bstep (se 1 (by rfl) ⟨1603988, by rfl⟩ : syracuseStep 2138651 = 3207977) B3207977
theorem B1425947 : Blo 1425532 1425947 := bstep (se 1 (by rfl) ⟨1069460, by rfl⟩ : syracuseStep 1425947 = 2138921) B2138921
theorem B1425951 : Blo 1425532 1425951 := bstep (se 1 (by rfl) ⟨1069463, by rfl⟩ : syracuseStep 1425951 = 2138927) B2138927
theorem B7217747 : Blo 1425532 7217747 := bstep (se 1 (by rfl) ⟨5413310, by rfl⟩ : syracuseStep 7217747 = 10826621) B10826621
theorem B1426031 : Blo 1425532 1426031 := bstep (se 1 (by rfl) ⟨1069523, by rfl⟩ : syracuseStep 1426031 = 2139047) B2139047
theorem B3211937 : Blo 1425532 3211937 := bstep (se 2 (by rfl) ⟨1204476, by rfl⟩ : syracuseStep 3211937 = 2408953) B2408953
theorem B1426087 : Blo 1425532 1426087 := bstep (se 1 (by rfl) ⟨1069565, by rfl⟩ : syracuseStep 1426087 = 2139131) B2139131
theorem B2286247 : Blo 1425532 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B5415619 : Blo 1425532 5415619 := bstep (se 1 (by rfl) ⟨4061714, by rfl⟩ : syracuseStep 5415619 = 8123429) B8123429
theorem B2138831 : Blo 1425532 2138831 := bstep (se 1 (by rfl) ⟨1604123, by rfl⟩ : syracuseStep 2138831 = 3208247) B3208247
theorem B1426127 : Blo 1425532 1426127 := bstep (se 1 (by rfl) ⟨1069595, by rfl⟩ : syracuseStep 1426127 = 2139191) B2139191
theorem B2138843 : Blo 1425532 2138843 := bstep (se 1 (by rfl) ⟨1604132, by rfl⟩ : syracuseStep 2138843 = 3208265) B3208265
theorem B1426207 : Blo 1425532 1426207 := bstep (se 1 (by rfl) ⟨1069655, by rfl⟩ : syracuseStep 1426207 = 2139311) B2139311
theorem B16253783 : Blo 1425532 16253783 := bstep (se 1 (by rfl) ⟨12190337, by rfl⟩ : syracuseStep 16253783 = 24380675) B24380675
theorem B1426479 : Blo 1425532 1426479 := bstep (se 1 (by rfl) ⟨1069859, by rfl⟩ : syracuseStep 1426479 = 2139719) B2139719
theorem B82314305 : Blo 1425532 82314305 := bstep (se 2 (by rfl) ⟨30867864, by rfl⟩ : syracuseStep 82314305 = 61735729) B61735729
theorem B1426543 : Blo 1425532 1426543 := bstep (se 1 (by rfl) ⟨1069907, by rfl⟩ : syracuseStep 1426543 = 2139815) B2139815
theorem B2139257 : Blo 1425532 2139257 := bstep (se 2 (by rfl) ⟨802221, by rfl⟩ : syracuseStep 2139257 = 1604443) B1604443
theorem B79193213 : Blo 1425532 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B13714595 : Blo 1425532 13714595 := bstep (se 1 (by rfl) ⟨10285946, by rfl⟩ : syracuseStep 13714595 = 20571893) B20571893
theorem B1426599 : Blo 1425532 1426599 := bstep (se 1 (by rfl) ⟨1069949, by rfl⟩ : syracuseStep 1426599 = 2139899) B2139899
theorem B46269629 : Blo 1425532 46269629 := bstep (se 3 (by rfl) ⟨8675555, by rfl⟩ : syracuseStep 46269629 = 17351111) B17351111
theorem B1426623 : Blo 1425532 1426623 := bstep (se 1 (by rfl) ⟨1069967, by rfl⟩ : syracuseStep 1426623 = 2139935) B2139935
theorem B1426655 : Blo 1425532 1426655 := bstep (se 1 (by rfl) ⟨1069991, by rfl⟩ : syracuseStep 1426655 = 2139983) B2139983
theorem B3048671 : Blo 1425532 3048671 := bstep (se 1 (by rfl) ⟨2286503, by rfl⟩ : syracuseStep 3048671 = 4573007) B4573007
theorem B1426735 : Blo 1425532 1426735 := bstep (se 1 (by rfl) ⟨1070051, by rfl⟩ : syracuseStep 1426735 = 2140103) B2140103
theorem B10421729 : Blo 1425532 10421729 := bstep (se 2 (by rfl) ⟨3908148, by rfl⟩ : syracuseStep 10421729 = 7816297) B7816297
theorem B13706749 : Blo 1425532 13706749 := bstep (se 3 (by rfl) ⟨2570015, by rfl⟩ : syracuseStep 13706749 = 5140031) B5140031
theorem B1426971 : Blo 1425532 1426971 := bstep (se 1 (by rfl) ⟨1070228, by rfl⟩ : syracuseStep 1426971 = 2140457) B2140457
theorem B1426975 : Blo 1425532 1426975 := bstep (se 1 (by rfl) ⟨1070231, by rfl⟩ : syracuseStep 1426975 = 2140463) B2140463
theorem B39020089 : Blo 1425532 39020089 := bstep (se 2 (by rfl) ⟨14632533, by rfl⟩ : syracuseStep 39020089 = 29265067) B29265067
theorem B1427135 : Blo 1425532 1427135 := bstep (se 1 (by rfl) ⟨1070351, by rfl⟩ : syracuseStep 1427135 = 2140703) B2140703
theorem B211167107 : Blo 1425532 211167107 := bstep (se 1 (by rfl) ⟨158375330, by rfl⟩ : syracuseStep 211167107 = 316750661) B316750661
theorem B16467877 : Blo 1425532 16467877 := bstep (se 4 (by rfl) ⟨1543863, by rfl⟩ : syracuseStep 16467877 = 3087727) B3087727
theorem B1427391 : Blo 1425532 1427391 := bstep (se 1 (by rfl) ⟨1070543, by rfl⟩ : syracuseStep 1427391 = 2141087) B2141087
theorem B9136091 : Blo 1425532 9136091 := bstep (se 1 (by rfl) ⟨6852068, by rfl⟩ : syracuseStep 9136091 = 13704137) B13704137
theorem B2140127 : Blo 1425532 2140127 := bstep (se 1 (by rfl) ⟨1605095, by rfl⟩ : syracuseStep 2140127 = 3210191) B3210191
theorem B1427423 : Blo 1425532 1427423 := bstep (se 1 (by rfl) ⟨1070567, by rfl⟩ : syracuseStep 1427423 = 2141135) B2141135
theorem B2140139 : Blo 1425532 2140139 := bstep (se 1 (by rfl) ⟨1605104, by rfl⟩ : syracuseStep 2140139 = 3210209) B3210209
theorem B2140187 : Blo 1425532 2140187 := bstep (se 1 (by rfl) ⟨1605140, by rfl⟩ : syracuseStep 2140187 = 3210281) B3210281
theorem B1427483 : Blo 1425532 1427483 := bstep (se 1 (by rfl) ⟨1070612, by rfl⟩ : syracuseStep 1427483 = 2141225) B2141225
theorem B1427487 : Blo 1425532 1427487 := bstep (se 1 (by rfl) ⟨1070615, by rfl⟩ : syracuseStep 1427487 = 2141231) B2141231
theorem B1427503 : Blo 1425532 1427503 := bstep (se 1 (by rfl) ⟨1070627, by rfl⟩ : syracuseStep 1427503 = 2141255) B2141255
theorem B10831967 : Blo 1425532 10831967 := bstep (se 1 (by rfl) ⟨8123975, by rfl⟩ : syracuseStep 10831967 = 16247951) B16247951
theorem B3254393 : Blo 1425532 3254393 := bstep (se 2 (by rfl) ⟨1220397, by rfl⟩ : syracuseStep 3254393 = 2440795) B2440795
theorem B6850763 : Blo 1425532 6850763 := bstep (se 1 (by rfl) ⟨5138072, by rfl⟩ : syracuseStep 6850763 = 10276145) B10276145
theorem B2140553 : Blo 1425532 2140553 := bstep (se 2 (by rfl) ⟨802707, by rfl⟩ : syracuseStep 2140553 = 1605415) B1605415
theorem B3426911 : Blo 1425532 3426911 := bstep (se 1 (by rfl) ⟨2570183, by rfl⟩ : syracuseStep 3426911 = 5140367) B5140367
theorem B12192389 : Blo 1425532 12192389 := bstep (se 4 (by rfl) ⟨1143036, by rfl⟩ : syracuseStep 12192389 = 2286073) B2286073
theorem B1805095 : Blo 1425532 1805095 := bstep (se 1 (by rfl) ⟨1353821, by rfl⟩ : syracuseStep 1805095 = 2707643) B2707643
theorem B1805419 : Blo 1425532 1805419 := bstep (se 1 (by rfl) ⟨1354064, by rfl⟩ : syracuseStep 1805419 = 2708129) B2708129
theorem B7220663 : Blo 1425532 7220663 := bstep (se 1 (by rfl) ⟨5415497, by rfl⟩ : syracuseStep 7220663 = 10830995) B10830995
theorem B4116071 : Blo 1425532 4116071 := bstep (se 1 (by rfl) ⟨3087053, by rfl⟩ : syracuseStep 4116071 = 6174107) B6174107
theorem B12193415 : Blo 1425532 12193415 := bstep (se 1 (by rfl) ⟨9145061, by rfl⟩ : syracuseStep 12193415 = 18290123) B18290123
theorem B13700987 : Blo 1425532 13700987 := bstep (se 1 (by rfl) ⟨10275740, by rfl⟩ : syracuseStep 13700987 = 20551481) B20551481
theorem B18542479 : Blo 1425532 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B1806391 : Blo 1425532 1806391 := bstep (se 1 (by rfl) ⟨1354793, by rfl⟩ : syracuseStep 1806391 = 2709587) B2709587
theorem B13004873 : Blo 1425532 13004873 := bstep (se 2 (by rfl) ⟨4876827, by rfl⟩ : syracuseStep 13004873 = 9753655) B9753655
theorem B19509443 : Blo 1425532 19509443 := bstep (se 1 (by rfl) ⟨14632082, by rfl⟩ : syracuseStep 19509443 = 29264165) B29264165
theorem B3207527 : Blo 1425532 3207527 := bstep (se 1 (by rfl) ⟨2405645, by rfl⟩ : syracuseStep 3207527 = 4811291) B4811291
theorem B3208103 : Blo 1425532 3208103 := bstep (se 1 (by rfl) ⟨2406077, by rfl⟩ : syracuseStep 3208103 = 4812155) B4812155
theorem B2929657 : Blo 1425532 2929657 := bstep (se 2 (by rfl) ⟨1098621, by rfl⟩ : syracuseStep 2929657 = 2197243) B2197243
theorem B2405639 : Blo 1425532 2405639 := bstep (se 1 (by rfl) ⟨1804229, by rfl⟩ : syracuseStep 2405639 = 3608459) B3608459
theorem B4568393 : Blo 1425532 4568393 := bstep (se 2 (by rfl) ⟨1713147, by rfl⟩ : syracuseStep 4568393 = 3426295) B3426295
theorem B3609967 : Blo 1425532 3609967 := bstep (se 1 (by rfl) ⟨2707475, by rfl⟩ : syracuseStep 3609967 = 5414951) B5414951
theorem B13014503 : Blo 1425532 13014503 := bstep (se 1 (by rfl) ⟨9760877, by rfl⟩ : syracuseStep 13014503 = 19521755) B19521755
theorem B5781239 : Blo 1425532 5781239 := bstep (se 1 (by rfl) ⟨4335929, by rfl⟩ : syracuseStep 5781239 = 8671859) B8671859
theorem B12179267 : Blo 1425532 12179267 := bstep (se 1 (by rfl) ⟨9134450, by rfl⟩ : syracuseStep 12179267 = 18268901) B18268901
theorem B3209039 : Blo 1425532 3209039 := bstep (se 1 (by rfl) ⟨2406779, by rfl⟩ : syracuseStep 3209039 = 4813559) B4813559
theorem B3610615 : Blo 1425532 3610615 := bstep (se 1 (by rfl) ⟨2707961, by rfl⟩ : syracuseStep 3610615 = 5415923) B5415923
theorem B3209399 : Blo 1425532 3209399 := bstep (se 1 (by rfl) ⟨2407049, by rfl⟩ : syracuseStep 3209399 = 4814099) B4814099
theorem B2406631 : Blo 1425532 2406631 := bstep (se 1 (by rfl) ⟨1804973, by rfl⟩ : syracuseStep 2406631 = 3609947) B3609947
theorem B6093103 : Blo 1425532 6093103 := bstep (se 1 (by rfl) ⟨4569827, by rfl⟩ : syracuseStep 6093103 = 9139655) B9139655
theorem B1604047 : Blo 1425532 1604047 := bstep (se 1 (by rfl) ⟨1203035, by rfl⟩ : syracuseStep 1604047 = 2406071) B2406071
theorem B3209759 : Blo 1425532 3209759 := bstep (se 1 (by rfl) ⟨2407319, by rfl⟩ : syracuseStep 3209759 = 4814639) B4814639
theorem B3209993 : Blo 1425532 3209993 := bstep (se 2 (by rfl) ⟨1203747, by rfl⟩ : syracuseStep 3209993 = 2407495) B2407495
theorem B16472915 : Blo 1425532 16472915 := bstep (se 1 (by rfl) ⟨12354686, by rfl⟩ : syracuseStep 16472915 = 24709373) B24709373
theorem B4815773 : Blo 1425532 4815773 := bstep (se 3 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 4815773 = 1805915) B1805915
theorem B8125343 : Blo 1425532 8125343 := bstep (se 1 (by rfl) ⟨6094007, by rfl⟩ : syracuseStep 8125343 = 12188015) B12188015
theorem B34692097 : Blo 1425532 34692097 := bstep (se 2 (by rfl) ⟨13009536, by rfl⟩ : syracuseStep 34692097 = 26019073) B26019073
theorem B2407529 : Blo 1425532 2407529 := bstep (se 2 (by rfl) ⟨902823, by rfl⟩ : syracuseStep 2407529 = 1805647) B1805647
theorem B1604839 : Blo 1425532 1604839 := bstep (se 1 (by rfl) ⟨1203629, by rfl⟩ : syracuseStep 1604839 = 2407259) B2407259
theorem B7224551 : Blo 1425532 7224551 := bstep (se 1 (by rfl) ⟨5418413, by rfl⟩ : syracuseStep 7224551 = 10836827) B10836827
theorem B3210569 : Blo 1425532 3210569 := bstep (se 2 (by rfl) ⟨1203963, by rfl⟩ : syracuseStep 3210569 = 2407927) B2407927
theorem B3046825 : Blo 1425532 3046825 := bstep (se 2 (by rfl) ⟨1142559, by rfl⟩ : syracuseStep 3046825 = 2285119) B2285119
theorem B7142863 : Blo 1425532 7142863 := bstep (se 1 (by rfl) ⟨5357147, by rfl⟩ : syracuseStep 7142863 = 10714295) B10714295
theorem B10829537 : Blo 1425532 10829537 := bstep (se 2 (by rfl) ⟨4061076, by rfl⟩ : syracuseStep 10829537 = 8122153) B8122153
theorem B3210983 : Blo 1425532 3210983 := bstep (se 1 (by rfl) ⟨2408237, by rfl⟩ : syracuseStep 3210983 = 4816475) B4816475
theorem B5414633 : Blo 1425532 5414633 := bstep (se 2 (by rfl) ⟨2030487, by rfl⟩ : syracuseStep 5414633 = 4060975) B4060975
theorem B5414647 : Blo 1425532 5414647 := bstep (se 1 (by rfl) ⟨4060985, by rfl⟩ : syracuseStep 5414647 = 8121971) B8121971
theorem B6176567 : Blo 1425532 6176567 := bstep (se 1 (by rfl) ⟨4632425, by rfl⟩ : syracuseStep 6176567 = 9264851) B9264851
theorem B13713209 : Blo 1425532 13713209 := bstep (se 2 (by rfl) ⟨5142453, by rfl⟩ : syracuseStep 13713209 = 10284907) B10284907
theorem B1605487 : Blo 1425532 1605487 := bstep (se 1 (by rfl) ⟨1204115, by rfl⟩ : syracuseStep 1605487 = 2408231) B2408231
theorem B3047311 : Blo 1425532 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B2408359 : Blo 1425532 2408359 := bstep (se 1 (by rfl) ⟨1806269, by rfl⟩ : syracuseStep 2408359 = 3612539) B3612539
theorem B15417325 : Blo 1425532 15417325 := bstep (se 3 (by rfl) ⟨2890748, by rfl⟩ : syracuseStep 15417325 = 5781497) B5781497
theorem B2408521 : Blo 1425532 2408521 := bstep (se 2 (by rfl) ⟨903195, by rfl⟩ : syracuseStep 2408521 = 1806391) B1806391
theorem B4063355 : Blo 1425532 4063355 := bstep (se 1 (by rfl) ⟨3047516, by rfl⟩ : syracuseStep 4063355 = 6095033) B6095033
theorem B2138351 : Blo 1425532 2138351 := bstep (se 1 (by rfl) ⟨1603763, by rfl⟩ : syracuseStep 2138351 = 3207527) B3207527
theorem B3211577 : Blo 1425532 3211577 := bstep (se 2 (by rfl) ⟨1204341, by rfl⟩ : syracuseStep 3211577 = 2408683) B2408683
theorem B1425767 : Blo 1425532 1425767 := bstep (se 1 (by rfl) ⟨1069325, by rfl⟩ : syracuseStep 1425767 = 2138651) B2138651
theorem B1425887 : Blo 1425532 1425887 := bstep (se 1 (by rfl) ⟨1069415, by rfl⟩ : syracuseStep 1425887 = 2138831) B2138831
theorem B1425895 : Blo 1425532 1425895 := bstep (se 1 (by rfl) ⟨1069421, by rfl⟩ : syracuseStep 1425895 = 2138843) B2138843
theorem B2138729 : Blo 1425532 2138729 := bstep (se 2 (by rfl) ⟨802023, by rfl⟩ : syracuseStep 2138729 = 1604047) B1604047
theorem B2138735 : Blo 1425532 2138735 := bstep (se 1 (by rfl) ⟨1604051, by rfl⟩ : syracuseStep 2138735 = 3208103) B3208103
theorem B1426171 : Blo 1425532 1426171 := bstep (se 1 (by rfl) ⟨1069628, by rfl⟩ : syracuseStep 1426171 = 2139257) B2139257
theorem B9143063 : Blo 1425532 9143063 := bstep (se 1 (by rfl) ⟨6857297, by rfl⟩ : syracuseStep 9143063 = 13714595) B13714595
theorem B2032447 : Blo 1425532 2032447 := bstep (se 1 (by rfl) ⟨1524335, by rfl⟩ : syracuseStep 2032447 = 3048671) B3048671
theorem B3048329 : Blo 1425532 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B6947819 : Blo 1425532 6947819 := bstep (se 1 (by rfl) ⟨5210864, by rfl⟩ : syracuseStep 6947819 = 10421729) B10421729
theorem B8676335 : Blo 1425532 8676335 := bstep (se 1 (by rfl) ⟨6507251, by rfl⟩ : syracuseStep 8676335 = 13014503) B13014503
theorem B8127485 : Blo 1425532 8127485 := bstep (se 3 (by rfl) ⟨1523903, by rfl⟩ : syracuseStep 8127485 = 3047807) B3047807
theorem B8119511 : Blo 1425532 8119511 := bstep (se 1 (by rfl) ⟨6089633, by rfl⟩ : syracuseStep 8119511 = 12179267) B12179267
theorem B2139359 : Blo 1425532 2139359 := bstep (se 1 (by rfl) ⟨1604519, by rfl⟩ : syracuseStep 2139359 = 3209039) B3209039
theorem B1426751 : Blo 1425532 1426751 := bstep (se 1 (by rfl) ⟨1070063, by rfl⟩ : syracuseStep 1426751 = 2140127) B2140127
theorem B1426759 : Blo 1425532 1426759 := bstep (se 1 (by rfl) ⟨1070069, by rfl⟩ : syracuseStep 1426759 = 2140139) B2140139
theorem B1426791 : Blo 1425532 1426791 := bstep (se 1 (by rfl) ⟨1070093, by rfl⟩ : syracuseStep 1426791 = 2140187) B2140187
theorem B2139599 : Blo 1425532 2139599 := bstep (se 1 (by rfl) ⟨1604699, by rfl⟩ : syracuseStep 2139599 = 3209399) B3209399
theorem B1427035 : Blo 1425532 1427035 := bstep (se 1 (by rfl) ⟨1070276, by rfl⟩ : syracuseStep 1427035 = 2140553) B2140553
theorem B2139785 : Blo 1425532 2139785 := bstep (se 2 (by rfl) ⟨802419, by rfl⟩ : syracuseStep 2139785 = 1604839) B1604839
theorem B2139839 : Blo 1425532 2139839 := bstep (se 1 (by rfl) ⟨1604879, by rfl⟩ : syracuseStep 2139839 = 3209759) B3209759
theorem B8128259 : Blo 1425532 8128259 := bstep (se 1 (by rfl) ⟨6096194, by rfl⟩ : syracuseStep 8128259 = 12192389) B12192389
theorem B2139995 : Blo 1425532 2139995 := bstep (se 1 (by rfl) ⟨1604996, by rfl⟩ : syracuseStep 2139995 = 3209993) B3209993
theorem B5416895 : Blo 1425532 5416895 := bstep (se 1 (by rfl) ⟨4062671, by rfl⟩ : syracuseStep 5416895 = 8125343) B8125343
theorem B2140379 : Blo 1425532 2140379 := bstep (se 1 (by rfl) ⟨1605284, by rfl⟩ : syracuseStep 2140379 = 3210569) B3210569
theorem B7219529 : Blo 1425532 7219529 := bstep (se 2 (by rfl) ⟨2707323, by rfl⟩ : syracuseStep 7219529 = 5414647) B5414647
theorem B8128943 : Blo 1425532 8128943 := bstep (se 1 (by rfl) ⟨6096707, by rfl⟩ : syracuseStep 8128943 = 12193415) B12193415
theorem B2140649 : Blo 1425532 2140649 := bstep (se 2 (by rfl) ⟨802743, by rfl⟩ : syracuseStep 2140649 = 1605487) B1605487
theorem B7219691 : Blo 1425532 7219691 := bstep (se 1 (by rfl) ⟨5414768, by rfl⟩ : syracuseStep 7219691 = 10829537) B10829537
theorem B2140655 : Blo 1425532 2140655 := bstep (se 1 (by rfl) ⟨1605491, by rfl⟩ : syracuseStep 2140655 = 3210983) B3210983
theorem B21957169 : Blo 1425532 21957169 := bstep (se 2 (by rfl) ⟨8233938, by rfl⟩ : syracuseStep 21957169 = 16467877) B16467877
theorem B20556433 : Blo 1425532 20556433 := bstep (se 2 (by rfl) ⟨7708662, by rfl⟩ : syracuseStep 20556433 = 15417325) B15417325
theorem B8669915 : Blo 1425532 8669915 := bstep (se 1 (by rfl) ⟨6502436, by rfl⟩ : syracuseStep 8669915 = 13004873) B13004873
theorem B2140967 : Blo 1425532 2140967 := bstep (se 1 (by rfl) ⟨1605725, by rfl⟩ : syracuseStep 2140967 = 3211451) B3211451
theorem B2141039 : Blo 1425532 2141039 := bstep (se 1 (by rfl) ⟨1605779, by rfl⟩ : syracuseStep 2141039 = 3211559) B3211559
theorem B25046003 : Blo 1425532 25046003 := bstep (se 1 (by rfl) ⟨18784502, by rfl⟩ : syracuseStep 25046003 = 37569005) B37569005
theorem B4811831 : Blo 1425532 4811831 := bstep (se 1 (by rfl) ⟨3608873, by rfl⟩ : syracuseStep 4811831 = 7217747) B7217747
theorem B2141291 : Blo 1425532 2141291 := bstep (se 1 (by rfl) ⟨1605968, by rfl⟩ : syracuseStep 2141291 = 3211937) B3211937
theorem B30846419 : Blo 1425532 30846419 := bstep (se 1 (by rfl) ⟨23134814, by rfl⟩ : syracuseStep 30846419 = 46269629) B46269629
theorem B7220825 : Blo 1425532 7220825 := bstep (se 2 (by rfl) ⟨2707809, by rfl⟩ : syracuseStep 7220825 = 5415619) B5415619
theorem B3854159 : Blo 1425532 3854159 := bstep (se 1 (by rfl) ⟨2890619, by rfl⟩ : syracuseStep 3854159 = 5781239) B5781239
theorem B6090727 : Blo 1425532 6090727 := bstep (se 1 (by rfl) ⟨4568045, by rfl⟩ : syracuseStep 6090727 = 9136091) B9136091
theorem B46256129 : Blo 1425532 46256129 := bstep (se 2 (by rfl) ⟨17346048, by rfl⟩ : syracuseStep 46256129 = 34692097) B34692097
theorem B7221311 : Blo 1425532 7221311 := bstep (se 1 (by rfl) ⟨5415983, by rfl⟩ : syracuseStep 7221311 = 10831967) B10831967
theorem B4567175 : Blo 1425532 4567175 := bstep (se 1 (by rfl) ⟨3425381, by rfl⟩ : syracuseStep 4567175 = 6850763) B6850763
theorem B4813289 : Blo 1425532 4813289 := bstep (se 2 (by rfl) ⟨1804983, by rfl⟩ : syracuseStep 4813289 = 3609967) B3609967
theorem B10981943 : Blo 1425532 10981943 := bstep (se 1 (by rfl) ⟨8236457, by rfl⟩ : syracuseStep 10981943 = 16472915) B16472915
theorem B9523817 : Blo 1425532 9523817 := bstep (se 2 (by rfl) ⟨3571431, by rfl⟩ : syracuseStep 9523817 = 7142863) B7142863
theorem B4813775 : Blo 1425532 4813775 := bstep (se 1 (by rfl) ⟨3610331, by rfl⟩ : syracuseStep 4813775 = 7220663) B7220663
theorem B3609755 : Blo 1425532 3609755 := bstep (se 1 (by rfl) ⟨2707316, by rfl⟩ : syracuseStep 3609755 = 5414633) B5414633
theorem B4117711 : Blo 1425532 4117711 := bstep (se 1 (by rfl) ⟨3088283, by rfl⟩ : syracuseStep 4117711 = 6176567) B6176567
theorem B4814153 : Blo 1425532 4814153 := bstep (se 2 (by rfl) ⟨1805307, by rfl⟩ : syracuseStep 4814153 = 3610615) B3610615
theorem B17356169 : Blo 1425532 17356169 := bstep (se 2 (by rfl) ⟨6508563, by rfl⟩ : syracuseStep 17356169 = 13017127) B13017127
theorem B13006295 : Blo 1425532 13006295 := bstep (se 1 (by rfl) ⟨9754721, by rfl⟩ : syracuseStep 13006295 = 19509443) B19509443
theorem B4232663 : Blo 1425532 4232663 := bstep (se 1 (by rfl) ⟨3174497, by rfl⟩ : syracuseStep 4232663 = 6348995) B6348995
theorem B3610079 : Blo 1425532 3610079 := bstep (se 1 (by rfl) ⟨2707559, by rfl⟩ : syracuseStep 3610079 = 5415119) B5415119
theorem B3208841 : Blo 1425532 3208841 := bstep (se 2 (by rfl) ⟨1203315, by rfl⟩ : syracuseStep 3208841 = 2406631) B2406631
theorem B8124137 : Blo 1425532 8124137 := bstep (se 2 (by rfl) ⟨3046551, by rfl⟩ : syracuseStep 8124137 = 6093103) B6093103
theorem B10835855 : Blo 1425532 10835855 := bstep (se 1 (by rfl) ⟨8126891, by rfl⟩ : syracuseStep 10835855 = 16253783) B16253783
theorem B54876203 : Blo 1425532 54876203 := bstep (se 1 (by rfl) ⟨41157152, by rfl⟩ : syracuseStep 54876203 = 82314305) B82314305
theorem B52795475 : Blo 1425532 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B1603759 : Blo 1425532 1603759 := bstep (se 1 (by rfl) ⟨1202819, by rfl⟩ : syracuseStep 1603759 = 2405639) B2405639
theorem B3045595 : Blo 1425532 3045595 := bstep (se 1 (by rfl) ⟨2284196, by rfl⟩ : syracuseStep 3045595 = 4568393) B4568393
theorem B2406793 : Blo 1425532 2406793 := bstep (se 2 (by rfl) ⟨902547, by rfl⟩ : syracuseStep 2406793 = 1805095) B1805095
theorem B140778071 : Blo 1425532 140778071 := bstep (se 1 (by rfl) ⟨105583553, by rfl⟩ : syracuseStep 140778071 = 211167107) B211167107
theorem B3906209 : Blo 1425532 3906209 := bstep (se 2 (by rfl) ⟨1464828, by rfl⟩ : syracuseStep 3906209 = 2929657) B2929657
theorem B2169595 : Blo 1425532 2169595 := bstep (se 1 (by rfl) ⟨1627196, by rfl⟩ : syracuseStep 2169595 = 3254393) B3254393
theorem B2407225 : Blo 1425532 2407225 := bstep (se 2 (by rfl) ⟨902709, by rfl⟩ : syracuseStep 2407225 = 1805419) B1805419
theorem B2284607 : Blo 1425532 2284607 := bstep (se 1 (by rfl) ⟨1713455, by rfl⟩ : syracuseStep 2284607 = 3426911) B3426911
theorem B4062433 : Blo 1425532 4062433 := bstep (se 2 (by rfl) ⟨1523412, by rfl⟩ : syracuseStep 4062433 = 3046825) B3046825
theorem B3210515 : Blo 1425532 3210515 := bstep (se 1 (by rfl) ⟨2407886, by rfl⟩ : syracuseStep 3210515 = 4815773) B4815773
theorem B18275665 : Blo 1425532 18275665 := bstep (se 2 (by rfl) ⟨6853374, by rfl⟩ : syracuseStep 18275665 = 13706749) B13706749
theorem B1605019 : Blo 1425532 1605019 := bstep (se 1 (by rfl) ⟨1203764, by rfl⟩ : syracuseStep 1605019 = 2407529) B2407529
theorem B52026785 : Blo 1425532 52026785 := bstep (se 2 (by rfl) ⟨19510044, by rfl⟩ : syracuseStep 52026785 = 39020089) B39020089
theorem B16252325 : Blo 1425532 16252325 := bstep (se 4 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 16252325 = 3047311) B3047311
theorem B4816367 : Blo 1425532 4816367 := bstep (se 1 (by rfl) ⟨3612275, by rfl⟩ : syracuseStep 4816367 = 7224551) B7224551
theorem B2744047 : Blo 1425532 2744047 := bstep (se 1 (by rfl) ⟨2058035, by rfl⟩ : syracuseStep 2744047 = 4116071) B4116071
theorem B24723305 : Blo 1425532 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B9142139 : Blo 1425532 9142139 := bstep (se 1 (by rfl) ⟨6856604, by rfl⟩ : syracuseStep 9142139 = 13713209) B13713209
theorem B3211145 : Blo 1425532 3211145 := bstep (se 2 (by rfl) ⟨1204179, by rfl⟩ : syracuseStep 3211145 = 2408359) B2408359
theorem B9133991 : Blo 1425532 9133991 := bstep (se 1 (by rfl) ⟨6850493, by rfl⟩ : syracuseStep 9133991 = 13700987) B13700987
theorem B3211361 : Blo 1425532 3211361 := bstep (se 2 (by rfl) ⟨1204260, by rfl⟩ : syracuseStep 3211361 = 2408521) B2408521
theorem B1425567 : Blo 1425532 1425567 := bstep (se 1 (by rfl) ⟨1069175, by rfl⟩ : syracuseStep 1425567 = 2138351) B2138351
theorem B2138345 : Blo 1425532 2138345 := bstep (se 2 (by rfl) ⟨801879, by rfl⟩ : syracuseStep 2138345 = 1603759) B1603759
theorem B1425819 : Blo 1425532 1425819 := bstep (se 1 (by rfl) ⟨1069364, by rfl⟩ : syracuseStep 1425819 = 2138729) B2138729
theorem B6349211 : Blo 1425532 6349211 := bstep (se 1 (by rfl) ⟨4761908, by rfl⟩ : syracuseStep 6349211 = 9523817) B9523817
theorem B1425823 : Blo 1425532 1425823 := bstep (se 1 (by rfl) ⟨1069367, by rfl⟩ : syracuseStep 1425823 = 2138735) B2138735
theorem B6095375 : Blo 1425532 6095375 := bstep (se 1 (by rfl) ⟨4571531, by rfl⟩ : syracuseStep 6095375 = 9143063) B9143063
theorem B2032219 : Blo 1425532 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B5784223 : Blo 1425532 5784223 := bstep (se 1 (by rfl) ⟨4338167, by rfl⟩ : syracuseStep 5784223 = 8676335) B8676335
theorem B1426239 : Blo 1425532 1426239 := bstep (se 1 (by rfl) ⟨1069679, by rfl⟩ : syracuseStep 1426239 = 2139359) B2139359
theorem B1426399 : Blo 1425532 1426399 := bstep (se 1 (by rfl) ⟨1069799, by rfl⟩ : syracuseStep 1426399 = 2139599) B2139599
theorem B2139227 : Blo 1425532 2139227 := bstep (se 1 (by rfl) ⟨1604420, by rfl⟩ : syracuseStep 2139227 = 3208841) B3208841
theorem B1426523 : Blo 1425532 1426523 := bstep (se 1 (by rfl) ⟨1069892, by rfl⟩ : syracuseStep 1426523 = 2139785) B2139785
theorem B1426559 : Blo 1425532 1426559 := bstep (se 1 (by rfl) ⟨1069919, by rfl⟩ : syracuseStep 1426559 = 2139839) B2139839
theorem B5416091 : Blo 1425532 5416091 := bstep (se 1 (by rfl) ⟨4062068, by rfl⟩ : syracuseStep 5416091 = 8124137) B8124137
theorem B1426663 : Blo 1425532 1426663 := bstep (se 1 (by rfl) ⟨1069997, by rfl⟩ : syracuseStep 1426663 = 2139995) B2139995
theorem B1426919 : Blo 1425532 1426919 := bstep (se 1 (by rfl) ⟨1070189, by rfl⟩ : syracuseStep 1426919 = 2140379) B2140379
theorem B5490281 : Blo 1425532 5490281 := bstep (se 2 (by rfl) ⟨2058855, by rfl⟩ : syracuseStep 5490281 = 4117711) B4117711
theorem B5416577 : Blo 1425532 5416577 := bstep (se 2 (by rfl) ⟨2031216, by rfl⟩ : syracuseStep 5416577 = 4062433) B4062433
theorem B1427099 : Blo 1425532 1427099 := bstep (se 1 (by rfl) ⟨1070324, by rfl⟩ : syracuseStep 1427099 = 2140649) B2140649
theorem B1427103 : Blo 1425532 1427103 := bstep (se 1 (by rfl) ⟨1070327, by rfl⟩ : syracuseStep 1427103 = 2140655) B2140655
theorem B1427311 : Blo 1425532 1427311 := bstep (se 1 (by rfl) ⟨1070483, by rfl⟩ : syracuseStep 1427311 = 2140967) B2140967
theorem B2140025 : Blo 1425532 2140025 := bstep (se 2 (by rfl) ⟨802509, by rfl⟩ : syracuseStep 2140025 = 1605019) B1605019
theorem B1427359 : Blo 1425532 1427359 := bstep (se 1 (by rfl) ⟨1070519, by rfl⟩ : syracuseStep 1427359 = 2141039) B2141039
theorem B16697335 : Blo 1425532 16697335 := bstep (se 1 (by rfl) ⟨12523001, by rfl⟩ : syracuseStep 16697335 = 25046003) B25046003
theorem B1427527 : Blo 1425532 1427527 := bstep (se 1 (by rfl) ⟨1070645, by rfl⟩ : syracuseStep 1427527 = 2141291) B2141291
theorem B2140343 : Blo 1425532 2140343 := bstep (se 1 (by rfl) ⟨1605257, by rfl⟩ : syracuseStep 2140343 = 3210515) B3210515
theorem B20564279 : Blo 1425532 20564279 := bstep (se 1 (by rfl) ⟨15423209, by rfl⟩ : syracuseStep 20564279 = 30846419) B30846419
theorem B2140763 : Blo 1425532 2140763 := bstep (se 1 (by rfl) ⟨1605572, by rfl⟩ : syracuseStep 2140763 = 3211145) B3211145
theorem B6089327 : Blo 1425532 6089327 := bstep (se 1 (by rfl) ⟨4566995, by rfl⟩ : syracuseStep 6089327 = 9133991) B9133991
theorem B8120969 : Blo 1425532 8120969 := bstep (se 2 (by rfl) ⟨3045363, by rfl⟩ : syracuseStep 8120969 = 6090727) B6090727
theorem B30837419 : Blo 1425532 30837419 := bstep (se 1 (by rfl) ⟨23128064, by rfl⟩ : syracuseStep 30837419 = 46256129) B46256129
theorem B2141051 : Blo 1425532 2141051 := bstep (se 1 (by rfl) ⟨1605788, by rfl⟩ : syracuseStep 2141051 = 3211577) B3211577
theorem B4631879 : Blo 1425532 4631879 := bstep (se 1 (by rfl) ⟨3473909, by rfl⟩ : syracuseStep 4631879 = 6947819) B6947819
theorem B5418323 : Blo 1425532 5418323 := bstep (se 1 (by rfl) ⟨4063742, by rfl⟩ : syracuseStep 5418323 = 8127485) B8127485
theorem B11570779 : Blo 1425532 11570779 := bstep (se 1 (by rfl) ⟨8678084, by rfl⟩ : syracuseStep 11570779 = 17356169) B17356169
theorem B8670863 : Blo 1425532 8670863 := bstep (se 1 (by rfl) ⟨6503147, by rfl⟩ : syracuseStep 8670863 = 13006295) B13006295
theorem B2821775 : Blo 1425532 2821775 := bstep (se 1 (by rfl) ⟨2116331, by rfl⟩ : syracuseStep 2821775 = 4232663) B4232663
theorem B5418839 : Blo 1425532 5418839 := bstep (se 1 (by rfl) ⟨4064129, by rfl⟩ : syracuseStep 5418839 = 8128259) B8128259
theorem B14634917 : Blo 1425532 14634917 := bstep (se 4 (by rfl) ⟨1372023, by rfl⟩ : syracuseStep 14634917 = 2744047) B2744047
theorem B11571173 : Blo 1425532 11571173 := bstep (se 4 (by rfl) ⟨1084797, by rfl⟩ : syracuseStep 11571173 = 2169595) B2169595
theorem B35196983 : Blo 1425532 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B4813019 : Blo 1425532 4813019 := bstep (se 1 (by rfl) ⟨3609764, by rfl⟩ : syracuseStep 4813019 = 7219529) B7219529
theorem B5419295 : Blo 1425532 5419295 := bstep (se 1 (by rfl) ⟨4064471, by rfl⟩ : syracuseStep 5419295 = 8128943) B8128943
theorem B4813127 : Blo 1425532 4813127 := bstep (se 1 (by rfl) ⟨3609845, by rfl⟩ : syracuseStep 4813127 = 7219691) B7219691
theorem B93852047 : Blo 1425532 93852047 := bstep (se 1 (by rfl) ⟨70389035, by rfl⟩ : syracuseStep 93852047 = 140778071) B140778071
theorem B24367553 : Blo 1425532 24367553 := bstep (se 2 (by rfl) ⟨9137832, by rfl⟩ : syracuseStep 24367553 = 18275665) B18275665
theorem B5779943 : Blo 1425532 5779943 := bstep (se 1 (by rfl) ⟨4334957, by rfl⟩ : syracuseStep 5779943 = 8669915) B8669915
theorem B3207887 : Blo 1425532 3207887 := bstep (se 1 (by rfl) ⟨2405915, by rfl⟩ : syracuseStep 3207887 = 4811831) B4811831
theorem B10834883 : Blo 1425532 10834883 := bstep (se 1 (by rfl) ⟨8126162, by rfl⟩ : syracuseStep 10834883 = 16252325) B16252325
theorem B4813883 : Blo 1425532 4813883 := bstep (se 1 (by rfl) ⟨3610412, by rfl⟩ : syracuseStep 4813883 = 7220825) B7220825
theorem B2569439 : Blo 1425532 2569439 := bstep (se 1 (by rfl) ⟨1927079, by rfl⟩ : syracuseStep 2569439 = 3854159) B3854159
theorem B4814207 : Blo 1425532 4814207 := bstep (se 1 (by rfl) ⟨3610655, by rfl⟩ : syracuseStep 4814207 = 7221311) B7221311
theorem B2708903 : Blo 1425532 2708903 := bstep (se 1 (by rfl) ⟨2031677, by rfl⟩ : syracuseStep 2708903 = 4063355) B4063355
theorem B3044783 : Blo 1425532 3044783 := bstep (se 1 (by rfl) ⟨2283587, by rfl⟩ : syracuseStep 3044783 = 4567175) B4567175
theorem B4060793 : Blo 1425532 4060793 := bstep (se 2 (by rfl) ⟨1522797, by rfl⟩ : syracuseStep 4060793 = 3045595) B3045595
theorem B3208859 : Blo 1425532 3208859 := bstep (se 1 (by rfl) ⟨2406644, by rfl⟩ : syracuseStep 3208859 = 4813289) B4813289
theorem B7321295 : Blo 1425532 7321295 := bstep (se 1 (by rfl) ⟨5490971, by rfl⟩ : syracuseStep 7321295 = 10981943) B10981943
theorem B3209057 : Blo 1425532 3209057 := bstep (se 2 (by rfl) ⟨1203396, by rfl⟩ : syracuseStep 3209057 = 2406793) B2406793
theorem B3209183 : Blo 1425532 3209183 := bstep (se 1 (by rfl) ⟨2406887, by rfl⟩ : syracuseStep 3209183 = 4813775) B4813775
theorem B29276225 : Blo 1425532 29276225 := bstep (se 2 (by rfl) ⟨10978584, by rfl⟩ : syracuseStep 29276225 = 21957169) B21957169
theorem B2406503 : Blo 1425532 2406503 := bstep (se 1 (by rfl) ⟨1804877, by rfl⟩ : syracuseStep 2406503 = 3609755) B3609755
theorem B5413007 : Blo 1425532 5413007 := bstep (se 1 (by rfl) ⟨4059755, by rfl⟩ : syracuseStep 5413007 = 8119511) B8119511
theorem B27408577 : Blo 1425532 27408577 := bstep (se 2 (by rfl) ⟨10278216, by rfl⟩ : syracuseStep 27408577 = 20556433) B20556433
theorem B3209435 : Blo 1425532 3209435 := bstep (se 1 (by rfl) ⟨2407076, by rfl⟩ : syracuseStep 3209435 = 4814153) B4814153
theorem B2406719 : Blo 1425532 2406719 := bstep (se 1 (by rfl) ⟨1805039, by rfl⟩ : syracuseStep 2406719 = 3610079) B3610079
theorem B3209633 : Blo 1425532 3209633 := bstep (se 2 (by rfl) ⟨1203612, by rfl⟩ : syracuseStep 3209633 = 2407225) B2407225
theorem B2709929 : Blo 1425532 2709929 := bstep (se 2 (by rfl) ⟨1016223, by rfl⟩ : syracuseStep 2709929 = 2032447) B2032447
theorem B7223903 : Blo 1425532 7223903 := bstep (se 1 (by rfl) ⟨5417927, by rfl⟩ : syracuseStep 7223903 = 10835855) B10835855
theorem B3611263 : Blo 1425532 3611263 := bstep (se 1 (by rfl) ⟨2708447, by rfl⟩ : syracuseStep 3611263 = 5416895) B5416895
theorem B36584135 : Blo 1425532 36584135 := bstep (se 1 (by rfl) ⟨27438101, by rfl⟩ : syracuseStep 36584135 = 54876203) B54876203
theorem B2604139 : Blo 1425532 2604139 := bstep (se 1 (by rfl) ⟨1953104, by rfl⟩ : syracuseStep 2604139 = 3906209) B3906209
theorem B1523071 : Blo 1425532 1523071 := bstep (se 1 (by rfl) ⟨1142303, by rfl⟩ : syracuseStep 1523071 = 2284607) B2284607
theorem B34684523 : Blo 1425532 34684523 := bstep (se 1 (by rfl) ⟨26013392, by rfl⟩ : syracuseStep 34684523 = 52026785) B52026785
theorem B3210911 : Blo 1425532 3210911 := bstep (se 1 (by rfl) ⟨2408183, by rfl⟩ : syracuseStep 3210911 = 4816367) B4816367
theorem B16482203 : Blo 1425532 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B6094759 : Blo 1425532 6094759 := bstep (se 1 (by rfl) ⟨4571069, by rfl⟩ : syracuseStep 6094759 = 9142139) B9142139
theorem B1425563 : Blo 1425532 1425563 := bstep (se 1 (by rfl) ⟨1069172, by rfl⟩ : syracuseStep 1425563 = 2138345) B2138345
theorem B3612863 : Blo 1425532 3612863 := bstep (se 1 (by rfl) ⟨2709647, by rfl⟩ : syracuseStep 3612863 = 5419295) B5419295
theorem B36544769 : Blo 1425532 36544769 := bstep (se 2 (by rfl) ⟨13704288, by rfl⟩ : syracuseStep 36544769 = 27408577) B27408577
theorem B16245035 : Blo 1425532 16245035 := bstep (se 1 (by rfl) ⟨12183776, by rfl⟩ : syracuseStep 16245035 = 24367553) B24367553
theorem B4063583 : Blo 1425532 4063583 := bstep (se 1 (by rfl) ⟨3047687, by rfl⟩ : syracuseStep 4063583 = 6095375) B6095375
theorem B2138591 : Blo 1425532 2138591 := bstep (se 1 (by rfl) ⟨1603943, by rfl⟩ : syracuseStep 2138591 = 3207887) B3207887
theorem B61710821 : Blo 1425532 61710821 := bstep (se 4 (by rfl) ⟨5785389, by rfl⟩ : syracuseStep 61710821 = 11570779) B11570779
theorem B1426151 : Blo 1425532 1426151 := bstep (se 1 (by rfl) ⟨1069613, by rfl⟩ : syracuseStep 1426151 = 2139227) B2139227
theorem B2139239 : Blo 1425532 2139239 := bstep (se 1 (by rfl) ⟨1604429, by rfl⟩ : syracuseStep 2139239 = 3208859) B3208859
theorem B2139371 : Blo 1425532 2139371 := bstep (se 1 (by rfl) ⟨1604528, by rfl⟩ : syracuseStep 2139371 = 3209057) B3209057
theorem B1426683 : Blo 1425532 1426683 := bstep (se 1 (by rfl) ⟨1070012, by rfl⟩ : syracuseStep 1426683 = 2140025) B2140025
theorem B2139455 : Blo 1425532 2139455 := bstep (se 1 (by rfl) ⟨1604591, by rfl⟩ : syracuseStep 2139455 = 3209183) B3209183
theorem B1426895 : Blo 1425532 1426895 := bstep (se 1 (by rfl) ⟨1070171, by rfl⟩ : syracuseStep 1426895 = 2140343) B2140343
theorem B2139623 : Blo 1425532 2139623 := bstep (se 1 (by rfl) ⟨1604717, by rfl⟩ : syracuseStep 2139623 = 3209435) B3209435
theorem B2139755 : Blo 1425532 2139755 := bstep (se 1 (by rfl) ⟨1604816, by rfl⟩ : syracuseStep 2139755 = 3209633) B3209633
theorem B14640749 : Blo 1425532 14640749 := bstep (se 3 (by rfl) ⟨2745140, by rfl⟩ : syracuseStep 14640749 = 5490281) B5490281
theorem B1427175 : Blo 1425532 1427175 := bstep (se 1 (by rfl) ⟨1070381, by rfl⟩ : syracuseStep 1427175 = 2140763) B2140763
theorem B24389423 : Blo 1425532 24389423 := bstep (se 1 (by rfl) ⟨18292067, by rfl⟩ : syracuseStep 24389423 = 36584135) B36584135
theorem B1427367 : Blo 1425532 1427367 := bstep (se 1 (by rfl) ⟨1070525, by rfl⟩ : syracuseStep 1427367 = 2141051) B2141051
theorem B2140607 : Blo 1425532 2140607 := bstep (se 1 (by rfl) ⟨1605455, by rfl⟩ : syracuseStep 2140607 = 3210911) B3210911
theorem B10988135 : Blo 1425532 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B23464655 : Blo 1425532 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B2140907 : Blo 1425532 2140907 := bstep (se 1 (by rfl) ⟨1605680, by rfl⟩ : syracuseStep 2140907 = 3211361) B3211361
theorem B3853295 : Blo 1425532 3853295 := bstep (se 1 (by rfl) ⟨2889971, by rfl⟩ : syracuseStep 3853295 = 5779943) B5779943
theorem B13888741 : Blo 1425532 13888741 := bstep (se 4 (by rfl) ⟨1302069, by rfl⟩ : syracuseStep 13888741 = 2604139) B2604139
theorem B6851837 : Blo 1425532 6851837 := bstep (se 3 (by rfl) ⟨1284719, by rfl⟩ : syracuseStep 6851837 = 2569439) B2569439
theorem B7712297 : Blo 1425532 7712297 := bstep (se 2 (by rfl) ⟨2892111, by rfl⟩ : syracuseStep 7712297 = 5784223) B5784223
theorem B2707195 : Blo 1425532 2707195 := bstep (se 1 (by rfl) ⟨2030396, by rfl⟩ : syracuseStep 2707195 = 4060793) B4060793
theorem B19517483 : Blo 1425532 19517483 := bstep (se 1 (by rfl) ⟨14638112, by rfl⟩ : syracuseStep 19517483 = 29276225) B29276225
theorem B3608671 : Blo 1425532 3608671 := bstep (se 1 (by rfl) ⟨2706503, by rfl⟩ : syracuseStep 3608671 = 5413007) B5413007
theorem B13709519 : Blo 1425532 13709519 := bstep (se 1 (by rfl) ⟨10282139, by rfl⟩ : syracuseStep 13709519 = 20564279) B20564279
theorem B1806619 : Blo 1425532 1806619 := bstep (se 1 (by rfl) ⟨1354964, by rfl⟩ : syracuseStep 1806619 = 2709929) B2709929
theorem B7524733 : Blo 1425532 7524733 := bstep (se 3 (by rfl) ⟨1410887, by rfl⟩ : syracuseStep 7524733 = 2821775) B2821775
theorem B4059551 : Blo 1425532 4059551 := bstep (se 1 (by rfl) ⟨3044663, by rfl⟩ : syracuseStep 4059551 = 6089327) B6089327
theorem B20558279 : Blo 1425532 20558279 := bstep (se 1 (by rfl) ⟨15418709, by rfl⟩ : syracuseStep 20558279 = 30837419) B30837419
theorem B23123015 : Blo 1425532 23123015 := bstep (se 1 (by rfl) ⟨17342261, by rfl⟩ : syracuseStep 23123015 = 34684523) B34684523
theorem B5780575 : Blo 1425532 5780575 := bstep (se 1 (by rfl) ⟨4335431, by rfl⟩ : syracuseStep 5780575 = 8670863) B8670863
theorem B7714115 : Blo 1425532 7714115 := bstep (se 1 (by rfl) ⟨5785586, by rfl⟩ : syracuseStep 7714115 = 11571173) B11571173
theorem B22263113 : Blo 1425532 22263113 := bstep (se 2 (by rfl) ⟨8348667, by rfl⟩ : syracuseStep 22263113 = 16697335) B16697335
theorem B3208679 : Blo 1425532 3208679 := bstep (se 1 (by rfl) ⟨2406509, by rfl⟩ : syracuseStep 3208679 = 4813019) B4813019
theorem B3208751 : Blo 1425532 3208751 := bstep (se 1 (by rfl) ⟨2406563, by rfl⟩ : syracuseStep 3208751 = 4813127) B4813127
theorem B4232807 : Blo 1425532 4232807 := bstep (se 1 (by rfl) ⟨3174605, by rfl⟩ : syracuseStep 4232807 = 6349211) B6349211
theorem B7223255 : Blo 1425532 7223255 := bstep (se 1 (by rfl) ⟨5417441, by rfl⟩ : syracuseStep 7223255 = 10834883) B10834883
theorem B3209255 : Blo 1425532 3209255 := bstep (se 1 (by rfl) ⟨2406941, by rfl⟩ : syracuseStep 3209255 = 4813883) B4813883
theorem B3610727 : Blo 1425532 3610727 := bstep (se 1 (by rfl) ⟨2708045, by rfl⟩ : syracuseStep 3610727 = 5416091) B5416091
theorem B2709625 : Blo 1425532 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B4815017 : Blo 1425532 4815017 := bstep (se 2 (by rfl) ⟨1805631, by rfl⟩ : syracuseStep 4815017 = 3611263) B3611263
theorem B3209471 : Blo 1425532 3209471 := bstep (se 1 (by rfl) ⟨2407103, by rfl⟩ : syracuseStep 3209471 = 4814207) B4814207
theorem B2029855 : Blo 1425532 2029855 := bstep (se 1 (by rfl) ⟨1522391, by rfl⟩ : syracuseStep 2029855 = 3044783) B3044783
theorem B250272125 : Blo 1425532 250272125 := bstep (se 3 (by rfl) ⟨46926023, by rfl⟩ : syracuseStep 250272125 = 93852047) B93852047
theorem B3611051 : Blo 1425532 3611051 := bstep (se 1 (by rfl) ⟨2708288, by rfl⟩ : syracuseStep 3611051 = 5416577) B5416577
theorem B7223741 : Blo 1425532 7223741 := bstep (se 3 (by rfl) ⟨1354451, by rfl⟩ : syracuseStep 7223741 = 2708903) B2708903
theorem B4880863 : Blo 1425532 4880863 := bstep (se 1 (by rfl) ⟨3660647, by rfl⟩ : syracuseStep 4880863 = 7321295) B7321295
theorem B1604335 : Blo 1425532 1604335 := bstep (se 1 (by rfl) ⟨1203251, by rfl⟩ : syracuseStep 1604335 = 2406503) B2406503
theorem B1604479 : Blo 1425532 1604479 := bstep (se 1 (by rfl) ⟨1203359, by rfl⟩ : syracuseStep 1604479 = 2406719) B2406719
theorem B4815935 : Blo 1425532 4815935 := bstep (se 1 (by rfl) ⟨3611951, by rfl⟩ : syracuseStep 4815935 = 7223903) B7223903
theorem B5413979 : Blo 1425532 5413979 := bstep (se 1 (by rfl) ⟨4060484, by rfl⟩ : syracuseStep 5413979 = 8120969) B8120969
theorem B2030761 : Blo 1425532 2030761 := bstep (se 2 (by rfl) ⟨761535, by rfl⟩ : syracuseStep 2030761 = 1523071) B1523071
theorem B3087919 : Blo 1425532 3087919 := bstep (se 1 (by rfl) ⟨2315939, by rfl⟩ : syracuseStep 3087919 = 4631879) B4631879
theorem B3612215 : Blo 1425532 3612215 := bstep (se 1 (by rfl) ⟨2709161, by rfl⟩ : syracuseStep 3612215 = 5418323) B5418323
theorem B8126345 : Blo 1425532 8126345 := bstep (se 2 (by rfl) ⟨3047379, by rfl⟩ : syracuseStep 8126345 = 6094759) B6094759
theorem B3612559 : Blo 1425532 3612559 := bstep (se 1 (by rfl) ⟨2709419, by rfl⟩ : syracuseStep 3612559 = 5418839) B5418839
theorem B9756611 : Blo 1425532 9756611 := bstep (se 1 (by rfl) ⟨7317458, by rfl⟩ : syracuseStep 9756611 = 14634917) B14634917
theorem B2408575 : Blo 1425532 2408575 := bstep (se 1 (by rfl) ⟨1806431, by rfl⟩ : syracuseStep 2408575 = 3612863) B3612863
theorem B3612833 : Blo 1425532 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B24363179 : Blo 1425532 24363179 := bstep (se 1 (by rfl) ⟨18272384, by rfl⟩ : syracuseStep 24363179 = 36544769) B36544769
theorem B10830023 : Blo 1425532 10830023 := bstep (se 1 (by rfl) ⟨8122517, by rfl⟩ : syracuseStep 10830023 = 16245035) B16245035
theorem B13705519 : Blo 1425532 13705519 := bstep (se 1 (by rfl) ⟨10279139, by rfl⟩ : syracuseStep 13705519 = 20558279) B20558279
theorem B1425727 : Blo 1425532 1425727 := bstep (se 1 (by rfl) ⟨1069295, by rfl⟩ : syracuseStep 1425727 = 2138591) B2138591
theorem B41140547 : Blo 1425532 41140547 := bstep (se 1 (by rfl) ⟨30855410, by rfl⟩ : syracuseStep 41140547 = 61710821) B61710821
theorem B2408825 : Blo 1425532 2408825 := bstep (se 2 (by rfl) ⟨903309, by rfl⟩ : syracuseStep 2408825 = 1806619) B1806619
theorem B1426159 : Blo 1425532 1426159 := bstep (se 1 (by rfl) ⟨1069619, by rfl⟩ : syracuseStep 1426159 = 2139239) B2139239
theorem B1426247 : Blo 1425532 1426247 := bstep (se 1 (by rfl) ⟨1069685, by rfl⟩ : syracuseStep 1426247 = 2139371) B2139371
theorem B1426303 : Blo 1425532 1426303 := bstep (se 1 (by rfl) ⟨1069727, by rfl⟩ : syracuseStep 1426303 = 2139455) B2139455
theorem B2139113 : Blo 1425532 2139113 := bstep (se 2 (by rfl) ⟨802167, by rfl⟩ : syracuseStep 2139113 = 1604335) B1604335
theorem B2139119 : Blo 1425532 2139119 := bstep (se 1 (by rfl) ⟨1604339, by rfl⟩ : syracuseStep 2139119 = 3208679) B3208679
theorem B1426415 : Blo 1425532 1426415 := bstep (se 1 (by rfl) ⟨1069811, by rfl⟩ : syracuseStep 1426415 = 2139623) B2139623
theorem B2139167 : Blo 1425532 2139167 := bstep (se 1 (by rfl) ⟨1604375, by rfl⟩ : syracuseStep 2139167 = 3208751) B3208751
theorem B1426503 : Blo 1425532 1426503 := bstep (se 1 (by rfl) ⟨1069877, by rfl⟩ : syracuseStep 1426503 = 2139755) B2139755
theorem B2139305 : Blo 1425532 2139305 := bstep (se 2 (by rfl) ⟨802239, by rfl⟩ : syracuseStep 2139305 = 1604479) B1604479
theorem B2139503 : Blo 1425532 2139503 := bstep (se 1 (by rfl) ⟨1604627, by rfl⟩ : syracuseStep 2139503 = 3209255) B3209255
theorem B2139647 : Blo 1425532 2139647 := bstep (se 1 (by rfl) ⟨1604735, by rfl⟩ : syracuseStep 2139647 = 3209471) B3209471
theorem B166848083 : Blo 1425532 166848083 := bstep (se 1 (by rfl) ⟨125136062, by rfl⟩ : syracuseStep 166848083 = 250272125) B250272125
theorem B1427071 : Blo 1425532 1427071 := bstep (se 1 (by rfl) ⟨1070303, by rfl⟩ : syracuseStep 1427071 = 2140607) B2140607
theorem B7325423 : Blo 1425532 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B1427271 : Blo 1425532 1427271 := bstep (se 1 (by rfl) ⟨1070453, by rfl⟩ : syracuseStep 1427271 = 2140907) B2140907
theorem B5417563 : Blo 1425532 5417563 := bstep (se 1 (by rfl) ⟨4063172, by rfl⟩ : syracuseStep 5417563 = 8126345) B8126345
theorem B52046621 : Blo 1425532 52046621 := bstep (se 3 (by rfl) ⟨9758741, by rfl⟩ : syracuseStep 52046621 = 19517483) B19517483
theorem B4811561 : Blo 1425532 4811561 := bstep (se 2 (by rfl) ⟨1804335, by rfl⟩ : syracuseStep 4811561 = 3608671) B3608671
theorem B2706367 : Blo 1425532 2706367 := bstep (se 1 (by rfl) ⟨2029775, by rfl⟩ : syracuseStep 2706367 = 4059551) B4059551
theorem B2706473 : Blo 1425532 2706473 := bstep (se 2 (by rfl) ⟨1014927, by rfl⟩ : syracuseStep 2706473 = 2029855) B2029855
theorem B18271565 : Blo 1425532 18271565 := bstep (se 3 (by rfl) ⟨3425918, by rfl⟩ : syracuseStep 18271565 = 6851837) B6851837
theorem B2821871 : Blo 1425532 2821871 := bstep (se 1 (by rfl) ⟨2116403, by rfl⟩ : syracuseStep 2821871 = 4232807) B4232807
theorem B9760499 : Blo 1425532 9760499 := bstep (se 1 (by rfl) ⟨7320374, by rfl⟩ : syracuseStep 9760499 = 14640749) B14640749
theorem B2707681 : Blo 1425532 2707681 := bstep (se 2 (by rfl) ⟨1015380, by rfl⟩ : syracuseStep 2707681 = 2030761) B2030761
theorem B18518321 : Blo 1425532 18518321 := bstep (se 2 (by rfl) ⟨6944370, by rfl⟩ : syracuseStep 18518321 = 13888741) B13888741
theorem B15643103 : Blo 1425532 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B2568863 : Blo 1425532 2568863 := bstep (se 1 (by rfl) ⟨1926647, by rfl⟩ : syracuseStep 2568863 = 3853295) B3853295
theorem B3609319 : Blo 1425532 3609319 := bstep (se 1 (by rfl) ⟨2706989, by rfl⟩ : syracuseStep 3609319 = 5413979) B5413979
theorem B4117225 : Blo 1425532 4117225 := bstep (se 2 (by rfl) ⟨1543959, by rfl⟩ : syracuseStep 4117225 = 3087919) B3087919
theorem B3609593 : Blo 1425532 3609593 := bstep (se 2 (by rfl) ⟨1353597, by rfl⟩ : syracuseStep 3609593 = 2707195) B2707195
theorem B5141531 : Blo 1425532 5141531 := bstep (se 1 (by rfl) ⟨3856148, by rfl⟩ : syracuseStep 5141531 = 7712297) B7712297
theorem B26031269 : Blo 1425532 26031269 := bstep (se 4 (by rfl) ⟨2440431, by rfl⟩ : syracuseStep 26031269 = 4880863) B4880863
theorem B9139679 : Blo 1425532 9139679 := bstep (se 1 (by rfl) ⟨6854759, by rfl⟩ : syracuseStep 9139679 = 13709519) B13709519
theorem B2709055 : Blo 1425532 2709055 := bstep (se 1 (by rfl) ⟨2031791, by rfl⟩ : syracuseStep 2709055 = 4063583) B4063583
theorem B10032977 : Blo 1425532 10032977 := bstep (se 2 (by rfl) ⟨3762366, by rfl⟩ : syracuseStep 10032977 = 7524733) B7524733
theorem B15415343 : Blo 1425532 15415343 := bstep (se 1 (by rfl) ⟨11561507, by rfl⟩ : syracuseStep 15415343 = 23123015) B23123015
theorem B5142743 : Blo 1425532 5142743 := bstep (se 1 (by rfl) ⟨3857057, by rfl⟩ : syracuseStep 5142743 = 7714115) B7714115
theorem B14842075 : Blo 1425532 14842075 := bstep (se 1 (by rfl) ⟨11131556, by rfl⟩ : syracuseStep 14842075 = 22263113) B22263113
theorem B16259615 : Blo 1425532 16259615 := bstep (se 1 (by rfl) ⟨12194711, by rfl⟩ : syracuseStep 16259615 = 24389423) B24389423
theorem B4815503 : Blo 1425532 4815503 := bstep (se 1 (by rfl) ⟨3611627, by rfl⟩ : syracuseStep 4815503 = 7223255) B7223255
theorem B2407151 : Blo 1425532 2407151 := bstep (se 1 (by rfl) ⟨1805363, by rfl⟩ : syracuseStep 2407151 = 3610727) B3610727
theorem B3210011 : Blo 1425532 3210011 := bstep (se 1 (by rfl) ⟨2407508, by rfl⟩ : syracuseStep 3210011 = 4815017) B4815017
theorem B7707433 : Blo 1425532 7707433 := bstep (se 2 (by rfl) ⟨2890287, by rfl⟩ : syracuseStep 7707433 = 5780575) B5780575
theorem B2407367 : Blo 1425532 2407367 := bstep (se 1 (by rfl) ⟨1805525, by rfl⟩ : syracuseStep 2407367 = 3611051) B3611051
theorem B4815827 : Blo 1425532 4815827 := bstep (se 1 (by rfl) ⟨3611870, by rfl⟩ : syracuseStep 4815827 = 7223741) B7223741
theorem B3210623 : Blo 1425532 3210623 := bstep (se 1 (by rfl) ⟨2407967, by rfl⟩ : syracuseStep 3210623 = 4815935) B4815935
theorem B2408143 : Blo 1425532 2408143 := bstep (se 1 (by rfl) ⟨1806107, by rfl⟩ : syracuseStep 2408143 = 3612215) B3612215
theorem B4816745 : Blo 1425532 4816745 := bstep (se 2 (by rfl) ⟨1806279, by rfl⟩ : syracuseStep 4816745 = 3612559) B3612559
theorem B6504407 : Blo 1425532 6504407 := bstep (se 1 (by rfl) ⟨4878305, by rfl⟩ : syracuseStep 6504407 = 9756611) B9756611
theorem B2408555 : Blo 1425532 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B7217261 : Blo 1425532 7217261 := bstep (se 3 (by rfl) ⟨1353236, by rfl⟩ : syracuseStep 7217261 = 2706473) B2706473
theorem B3211433 : Blo 1425532 3211433 := bstep (se 2 (by rfl) ⟨1204287, by rfl⟩ : syracuseStep 3211433 = 2408575) B2408575
theorem B12345547 : Blo 1425532 12345547 := bstep (se 1 (by rfl) ⟨9259160, by rfl⟩ : syracuseStep 12345547 = 18518321) B18518321
theorem B27427031 : Blo 1425532 27427031 := bstep (se 1 (by rfl) ⟨20570273, by rfl⟩ : syracuseStep 27427031 = 41140547) B41140547
theorem B1605883 : Blo 1425532 1605883 := bstep (se 1 (by rfl) ⟨1204412, by rfl⟩ : syracuseStep 1605883 = 2408825) B2408825
theorem B1712575 : Blo 1425532 1712575 := bstep (se 1 (by rfl) ⟨1284431, by rfl⟩ : syracuseStep 1712575 = 2568863) B2568863
theorem B1426075 : Blo 1425532 1426075 := bstep (se 1 (by rfl) ⟨1069556, by rfl⟩ : syracuseStep 1426075 = 2139113) B2139113
theorem B1426079 : Blo 1425532 1426079 := bstep (se 1 (by rfl) ⟨1069559, by rfl⟩ : syracuseStep 1426079 = 2139119) B2139119
theorem B1426111 : Blo 1425532 1426111 := bstep (se 1 (by rfl) ⟨1069583, by rfl⟩ : syracuseStep 1426111 = 2139167) B2139167
theorem B1426203 : Blo 1425532 1426203 := bstep (se 1 (by rfl) ⟨1069652, by rfl⟩ : syracuseStep 1426203 = 2139305) B2139305
theorem B1426335 : Blo 1425532 1426335 := bstep (se 1 (by rfl) ⟨1069751, by rfl⟩ : syracuseStep 1426335 = 2139503) B2139503
theorem B5489633 : Blo 1425532 5489633 := bstep (se 2 (by rfl) ⟨2058612, by rfl⟩ : syracuseStep 5489633 = 4117225) B4117225
theorem B1426431 : Blo 1425532 1426431 := bstep (se 1 (by rfl) ⟨1069823, by rfl⟩ : syracuseStep 1426431 = 2139647) B2139647
theorem B111232055 : Blo 1425532 111232055 := bstep (se 1 (by rfl) ⟨83424041, by rfl⟩ : syracuseStep 111232055 = 166848083) B166848083
theorem B4883615 : Blo 1425532 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B41714941 : Blo 1425532 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B10839743 : Blo 1425532 10839743 := bstep (se 1 (by rfl) ⟨8129807, by rfl⟩ : syracuseStep 10839743 = 16259615) B16259615
theorem B2140007 : Blo 1425532 2140007 := bstep (se 1 (by rfl) ⟨1605005, by rfl⟩ : syracuseStep 2140007 = 3210011) B3210011
theorem B2140415 : Blo 1425532 2140415 := bstep (se 1 (by rfl) ⟨1605311, by rfl⟩ : syracuseStep 2140415 = 3210623) B3210623
theorem B6506999 : Blo 1425532 6506999 := bstep (se 1 (by rfl) ⟨4880249, by rfl⟩ : syracuseStep 6506999 = 9760499) B9760499
theorem B4336271 : Blo 1425532 4336271 := bstep (se 1 (by rfl) ⟨3252203, by rfl⟩ : syracuseStep 4336271 = 6504407) B6504407
theorem B7220015 : Blo 1425532 7220015 := bstep (se 1 (by rfl) ⟨5415011, by rfl⟩ : syracuseStep 7220015 = 10830023) B10830023
theorem B3427687 : Blo 1425532 3427687 := bstep (se 1 (by rfl) ⟨2570765, by rfl⟩ : syracuseStep 3427687 = 5141531) B5141531
theorem B17354179 : Blo 1425532 17354179 := bstep (se 1 (by rfl) ⟨13015634, by rfl⟩ : syracuseStep 17354179 = 26031269) B26031269
theorem B4812425 : Blo 1425532 4812425 := bstep (se 2 (by rfl) ⟨1804659, by rfl⟩ : syracuseStep 4812425 = 3609319) B3609319
theorem B10276577 : Blo 1425532 10276577 := bstep (se 2 (by rfl) ⟨3853716, by rfl⟩ : syracuseStep 10276577 = 7707433) B7707433
theorem B6688651 : Blo 1425532 6688651 := bstep (se 1 (by rfl) ⟨5016488, by rfl⟩ : syracuseStep 6688651 = 10032977) B10032977
theorem B3608489 : Blo 1425532 3608489 := bstep (se 2 (by rfl) ⟨1353183, by rfl⟩ : syracuseStep 3608489 = 2706367) B2706367
theorem B10276895 : Blo 1425532 10276895 := bstep (se 1 (by rfl) ⟨7707671, by rfl⟩ : syracuseStep 10276895 = 15415343) B15415343
theorem B3428495 : Blo 1425532 3428495 := bstep (se 1 (by rfl) ⟨2571371, by rfl⟩ : syracuseStep 3428495 = 5142743) B5142743
theorem B34697747 : Blo 1425532 34697747 := bstep (se 1 (by rfl) ⟨26023310, by rfl⟩ : syracuseStep 34697747 = 52046621) B52046621
theorem B3207707 : Blo 1425532 3207707 := bstep (se 1 (by rfl) ⟨2405780, by rfl⟩ : syracuseStep 3207707 = 4811561) B4811561
theorem B7524989 : Blo 1425532 7524989 := bstep (se 3 (by rfl) ⟨1410935, by rfl⟩ : syracuseStep 7524989 = 2821871) B2821871
theorem B16242119 : Blo 1425532 16242119 := bstep (se 1 (by rfl) ⟨12181589, by rfl⟩ : syracuseStep 16242119 = 24363179) B24363179
theorem B19789433 : Blo 1425532 19789433 := bstep (se 2 (by rfl) ⟨7421037, by rfl⟩ : syracuseStep 19789433 = 14842075) B14842075
theorem B3610241 : Blo 1425532 3610241 := bstep (se 2 (by rfl) ⟨1353840, by rfl⟩ : syracuseStep 3610241 = 2707681) B2707681
theorem B18274025 : Blo 1425532 18274025 := bstep (se 2 (by rfl) ⟨6852759, by rfl⟩ : syracuseStep 18274025 = 13705519) B13705519
theorem B2406395 : Blo 1425532 2406395 := bstep (se 1 (by rfl) ⟨1804796, by rfl⟩ : syracuseStep 2406395 = 3609593) B3609593
theorem B7223417 : Blo 1425532 7223417 := bstep (se 2 (by rfl) ⟨2708781, by rfl⟩ : syracuseStep 7223417 = 5417563) B5417563
theorem B6093119 : Blo 1425532 6093119 := bstep (se 1 (by rfl) ⟨4569839, by rfl⟩ : syracuseStep 6093119 = 9139679) B9139679
theorem B3210335 : Blo 1425532 3210335 := bstep (se 1 (by rfl) ⟨2407751, by rfl⟩ : syracuseStep 3210335 = 4815503) B4815503
theorem B1604767 : Blo 1425532 1604767 := bstep (se 1 (by rfl) ⟨1203575, by rfl⟩ : syracuseStep 1604767 = 2407151) B2407151
theorem B1604911 : Blo 1425532 1604911 := bstep (se 1 (by rfl) ⟨1203683, by rfl⟩ : syracuseStep 1604911 = 2407367) B2407367
theorem B3210551 : Blo 1425532 3210551 := bstep (se 1 (by rfl) ⟨2407913, by rfl⟩ : syracuseStep 3210551 = 4815827) B4815827
theorem B3612073 : Blo 1425532 3612073 := bstep (se 2 (by rfl) ⟨1354527, by rfl⟩ : syracuseStep 3612073 = 2709055) B2709055
theorem B12181043 : Blo 1425532 12181043 := bstep (se 1 (by rfl) ⟨9135782, by rfl⟩ : syracuseStep 12181043 = 18271565) B18271565
theorem B3210857 : Blo 1425532 3210857 := bstep (se 2 (by rfl) ⟨1204071, by rfl⟩ : syracuseStep 3210857 = 2408143) B2408143
theorem B3211163 : Blo 1425532 3211163 := bstep (se 1 (by rfl) ⟨2408372, by rfl⟩ : syracuseStep 3211163 = 4816745) B4816745
theorem B1605703 : Blo 1425532 1605703 := bstep (se 1 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 1605703 = 2408555) B2408555
theorem B2285663 : Blo 1425532 2285663 := bstep (se 1 (by rfl) ⟨1714247, by rfl⟩ : syracuseStep 2285663 = 3428495) B3428495
theorem B18284687 : Blo 1425532 18284687 := bstep (se 1 (by rfl) ⟨13713515, by rfl⟩ : syracuseStep 18284687 = 27427031) B27427031
theorem B2138471 : Blo 1425532 2138471 := bstep (se 1 (by rfl) ⟨1603853, by rfl⟩ : syracuseStep 2138471 = 3207707) B3207707
theorem B7226495 : Blo 1425532 7226495 := bstep (se 1 (by rfl) ⟨5419871, by rfl⟩ : syracuseStep 7226495 = 10839743) B10839743
theorem B12182683 : Blo 1425532 12182683 := bstep (se 1 (by rfl) ⟨9137012, by rfl⟩ : syracuseStep 12182683 = 18274025) B18274025
theorem B1426671 : Blo 1425532 1426671 := bstep (se 1 (by rfl) ⟨1070003, by rfl⟩ : syracuseStep 1426671 = 2140007) B2140007
theorem B1426943 : Blo 1425532 1426943 := bstep (se 1 (by rfl) ⟨1070207, by rfl⟩ : syracuseStep 1426943 = 2140415) B2140415
theorem B2139689 : Blo 1425532 2139689 := bstep (se 2 (by rfl) ⟨802383, by rfl⟩ : syracuseStep 2139689 = 1604767) B1604767
theorem B2139881 : Blo 1425532 2139881 := bstep (se 2 (by rfl) ⟨802455, by rfl⟩ : syracuseStep 2139881 = 1604911) B1604911
theorem B2140223 : Blo 1425532 2140223 := bstep (se 1 (by rfl) ⟨1605167, by rfl⟩ : syracuseStep 2140223 = 3210335) B3210335
theorem B2140367 : Blo 1425532 2140367 := bstep (se 1 (by rfl) ⟨1605275, by rfl⟩ : syracuseStep 2140367 = 3210551) B3210551
theorem B8120695 : Blo 1425532 8120695 := bstep (se 1 (by rfl) ⟨6090521, by rfl⟩ : syracuseStep 8120695 = 12181043) B12181043
theorem B2140571 : Blo 1425532 2140571 := bstep (se 1 (by rfl) ⟨1605428, by rfl⟩ : syracuseStep 2140571 = 3210857) B3210857
theorem B6851051 : Blo 1425532 6851051 := bstep (se 1 (by rfl) ⟨5138288, by rfl⟩ : syracuseStep 6851051 = 10276577) B10276577
theorem B2140775 : Blo 1425532 2140775 := bstep (se 1 (by rfl) ⟨1605581, by rfl⟩ : syracuseStep 2140775 = 3211163) B3211163
theorem B6851263 : Blo 1425532 6851263 := bstep (se 1 (by rfl) ⟨5138447, by rfl⟩ : syracuseStep 6851263 = 10276895) B10276895
theorem B4811507 : Blo 1425532 4811507 := bstep (se 1 (by rfl) ⟨3608630, by rfl⟩ : syracuseStep 4811507 = 7217261) B7217261
theorem B2140955 : Blo 1425532 2140955 := bstep (se 1 (by rfl) ⟨1605716, by rfl⟩ : syracuseStep 2140955 = 3211433) B3211433
theorem B296618813 : Blo 1425532 296618813 := bstep (se 3 (by rfl) ⟨55616027, by rfl⟩ : syracuseStep 296618813 = 111232055) B111232055
theorem B16460729 : Blo 1425532 16460729 := bstep (se 2 (by rfl) ⟨6172773, by rfl⟩ : syracuseStep 16460729 = 12345547) B12345547
theorem B2141177 : Blo 1425532 2141177 := bstep (se 2 (by rfl) ⟨802941, by rfl⟩ : syracuseStep 2141177 = 1605883) B1605883
theorem B5016659 : Blo 1425532 5016659 := bstep (se 1 (by rfl) ⟨3762494, by rfl⟩ : syracuseStep 5016659 = 7524989) B7524989
theorem B3255743 : Blo 1425532 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B13192955 : Blo 1425532 13192955 := bstep (se 1 (by rfl) ⟨9894716, by rfl⟩ : syracuseStep 13192955 = 19789433) B19789433
theorem B4337999 : Blo 1425532 4337999 := bstep (se 1 (by rfl) ⟨3253499, by rfl⟩ : syracuseStep 4337999 = 6506999) B6506999
theorem B55619921 : Blo 1425532 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B4813343 : Blo 1425532 4813343 := bstep (se 1 (by rfl) ⟨3610007, by rfl⟩ : syracuseStep 4813343 = 7220015) B7220015
theorem B18280997 : Blo 1425532 18280997 := bstep (se 4 (by rfl) ⟨1713843, by rfl⟩ : syracuseStep 18280997 = 3427687) B3427687
theorem B23138905 : Blo 1425532 23138905 := bstep (se 2 (by rfl) ⟨8677089, by rfl⟩ : syracuseStep 23138905 = 17354179) B17354179
theorem B3208283 : Blo 1425532 3208283 := bstep (se 1 (by rfl) ⟨2406212, by rfl⟩ : syracuseStep 3208283 = 4812425) B4812425
theorem B8918201 : Blo 1425532 8918201 := bstep (se 2 (by rfl) ⟨3344325, by rfl⟩ : syracuseStep 8918201 = 6688651) B6688651
theorem B2405659 : Blo 1425532 2405659 := bstep (se 1 (by rfl) ⟨1804244, by rfl⟩ : syracuseStep 2405659 = 3608489) B3608489
theorem B23131831 : Blo 1425532 23131831 := bstep (se 1 (by rfl) ⟨17348873, by rfl⟩ : syracuseStep 23131831 = 34697747) B34697747
theorem B2283433 : Blo 1425532 2283433 := bstep (se 2 (by rfl) ⟨856287, by rfl⟩ : syracuseStep 2283433 = 1712575) B1712575
theorem B3659755 : Blo 1425532 3659755 := bstep (se 1 (by rfl) ⟨2744816, by rfl⟩ : syracuseStep 3659755 = 5489633) B5489633
theorem B10828079 : Blo 1425532 10828079 := bstep (se 1 (by rfl) ⟨8121059, by rfl⟩ : syracuseStep 10828079 = 16242119) B16242119
theorem B2406827 : Blo 1425532 2406827 := bstep (se 1 (by rfl) ⟨1805120, by rfl⟩ : syracuseStep 2406827 = 3610241) B3610241
theorem B1604263 : Blo 1425532 1604263 := bstep (se 1 (by rfl) ⟨1203197, by rfl⟩ : syracuseStep 1604263 = 2406395) B2406395
theorem B4815611 : Blo 1425532 4815611 := bstep (se 1 (by rfl) ⟨3611708, by rfl⟩ : syracuseStep 4815611 = 7223417) B7223417
theorem B4062079 : Blo 1425532 4062079 := bstep (se 1 (by rfl) ⟨3046559, by rfl⟩ : syracuseStep 4062079 = 6093119) B6093119
theorem B2890847 : Blo 1425532 2890847 := bstep (se 1 (by rfl) ⟨2168135, by rfl⟩ : syracuseStep 2890847 = 4336271) B4336271
theorem B4816097 : Blo 1425532 4816097 := bstep (se 2 (by rfl) ⟨1806036, by rfl⟩ : syracuseStep 4816097 = 3612073) B3612073
theorem B12189791 : Blo 1425532 12189791 := bstep (se 1 (by rfl) ⟨9142343, by rfl⟩ : syracuseStep 12189791 = 18284687) B18284687
theorem B2891999 : Blo 1425532 2891999 := bstep (se 1 (by rfl) ⟨2168999, by rfl⟩ : syracuseStep 2891999 = 4337999) B4337999
theorem B1425647 : Blo 1425532 1425647 := bstep (se 1 (by rfl) ⟨1069235, by rfl⟩ : syracuseStep 1425647 = 2138471) B2138471
theorem B7708925 : Blo 1425532 7708925 := bstep (se 3 (by rfl) ⟨1445423, by rfl⟩ : syracuseStep 7708925 = 2890847) B2890847
theorem B6095101 : Blo 1425532 6095101 := bstep (se 3 (by rfl) ⟨1142831, by rfl⟩ : syracuseStep 6095101 = 2285663) B2285663
theorem B2138855 : Blo 1425532 2138855 := bstep (se 1 (by rfl) ⟨1604141, by rfl⟩ : syracuseStep 2138855 = 3208283) B3208283
theorem B4817663 : Blo 1425532 4817663 := bstep (se 1 (by rfl) ⟨3613247, by rfl⟩ : syracuseStep 4817663 = 7226495) B7226495
theorem B30851873 : Blo 1425532 30851873 := bstep (se 2 (by rfl) ⟨11569452, by rfl⟩ : syracuseStep 30851873 = 23138905) B23138905
theorem B53511029 : Blo 1425532 53511029 := bstep (se 5 (by rfl) ⟨2508329, by rfl⟩ : syracuseStep 53511029 = 5016659) B5016659
theorem B2139017 : Blo 1425532 2139017 := bstep (se 2 (by rfl) ⟨802131, by rfl⟩ : syracuseStep 2139017 = 1604263) B1604263
theorem B9135017 : Blo 1425532 9135017 := bstep (se 2 (by rfl) ⟨3425631, by rfl⟩ : syracuseStep 9135017 = 6851263) B6851263
theorem B1426459 : Blo 1425532 1426459 := bstep (se 1 (by rfl) ⟨1069844, by rfl⟩ : syracuseStep 1426459 = 2139689) B2139689
theorem B1426587 : Blo 1425532 1426587 := bstep (se 1 (by rfl) ⟨1069940, by rfl⟩ : syracuseStep 1426587 = 2139881) B2139881
theorem B5416105 : Blo 1425532 5416105 := bstep (se 2 (by rfl) ⟨2031039, by rfl⟩ : syracuseStep 5416105 = 4062079) B4062079
theorem B1426815 : Blo 1425532 1426815 := bstep (se 1 (by rfl) ⟨1070111, by rfl⟩ : syracuseStep 1426815 = 2140223) B2140223
theorem B1426911 : Blo 1425532 1426911 := bstep (se 1 (by rfl) ⟨1070183, by rfl⟩ : syracuseStep 1426911 = 2140367) B2140367
theorem B7218719 : Blo 1425532 7218719 := bstep (se 1 (by rfl) ⟨5414039, by rfl⟩ : syracuseStep 7218719 = 10828079) B10828079
theorem B1427047 : Blo 1425532 1427047 := bstep (se 1 (by rfl) ⟨1070285, by rfl⟩ : syracuseStep 1427047 = 2140571) B2140571
theorem B1427183 : Blo 1425532 1427183 := bstep (se 1 (by rfl) ⟨1070387, by rfl⟩ : syracuseStep 1427183 = 2140775) B2140775
theorem B1427303 : Blo 1425532 1427303 := bstep (se 1 (by rfl) ⟨1070477, by rfl⟩ : syracuseStep 1427303 = 2140955) B2140955
theorem B1427451 : Blo 1425532 1427451 := bstep (se 1 (by rfl) ⟨1070588, by rfl⟩ : syracuseStep 1427451 = 2141177) B2141177
theorem B2140937 : Blo 1425532 2140937 := bstep (se 2 (by rfl) ⟨802851, by rfl⟩ : syracuseStep 2140937 = 1605703) B1605703
theorem B37079947 : Blo 1425532 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B4567367 : Blo 1425532 4567367 := bstep (se 1 (by rfl) ⟨3425525, by rfl⟩ : syracuseStep 4567367 = 6851051) B6851051
theorem B3207545 : Blo 1425532 3207545 := bstep (se 2 (by rfl) ⟨1202829, by rfl⟩ : syracuseStep 3207545 = 2405659) B2405659
theorem B3207671 : Blo 1425532 3207671 := bstep (se 1 (by rfl) ⟨2405753, by rfl⟩ : syracuseStep 3207671 = 4811507) B4811507
theorem B10973819 : Blo 1425532 10973819 := bstep (se 1 (by rfl) ⟨8230364, by rfl⟩ : syracuseStep 10973819 = 16460729) B16460729
theorem B12178309 : Blo 1425532 12178309 := bstep (se 4 (by rfl) ⟨1141716, by rfl⟩ : syracuseStep 12178309 = 2283433) B2283433
theorem B8795303 : Blo 1425532 8795303 := bstep (se 1 (by rfl) ⟨6596477, by rfl⟩ : syracuseStep 8795303 = 13192955) B13192955
theorem B4879673 : Blo 1425532 4879673 := bstep (se 2 (by rfl) ⟨1829877, by rfl⟩ : syracuseStep 4879673 = 3659755) B3659755
theorem B3208895 : Blo 1425532 3208895 := bstep (se 1 (by rfl) ⟨2406671, by rfl⟩ : syracuseStep 3208895 = 4813343) B4813343
theorem B12187331 : Blo 1425532 12187331 := bstep (se 1 (by rfl) ⟨9140498, by rfl⟩ : syracuseStep 12187331 = 18280997) B18280997
theorem B10827593 : Blo 1425532 10827593 := bstep (se 2 (by rfl) ⟨4060347, by rfl⟩ : syracuseStep 10827593 = 8120695) B8120695
theorem B5945467 : Blo 1425532 5945467 := bstep (se 1 (by rfl) ⟨4459100, by rfl⟩ : syracuseStep 5945467 = 8918201) B8918201
theorem B16243577 : Blo 1425532 16243577 := bstep (se 2 (by rfl) ⟨6091341, by rfl⟩ : syracuseStep 16243577 = 12182683) B12182683
theorem B1604551 : Blo 1425532 1604551 := bstep (se 1 (by rfl) ⟨1203413, by rfl⟩ : syracuseStep 1604551 = 2406827) B2406827
theorem B3210407 : Blo 1425532 3210407 := bstep (se 1 (by rfl) ⟨2407805, by rfl⟩ : syracuseStep 3210407 = 4815611) B4815611
theorem B197745875 : Blo 1425532 197745875 := bstep (se 1 (by rfl) ⟨148309406, by rfl⟩ : syracuseStep 197745875 = 296618813) B296618813
theorem B3210731 : Blo 1425532 3210731 := bstep (se 1 (by rfl) ⟨2408048, by rfl⟩ : syracuseStep 3210731 = 4816097) B4816097
theorem B30842441 : Blo 1425532 30842441 := bstep (se 2 (by rfl) ⟨11565915, by rfl⟩ : syracuseStep 30842441 = 23131831) B23131831
theorem B2170495 : Blo 1425532 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B8126527 : Blo 1425532 8126527 := bstep (se 1 (by rfl) ⟨6094895, by rfl⟩ : syracuseStep 8126527 = 12189791) B12189791
theorem B2138363 : Blo 1425532 2138363 := bstep (se 1 (by rfl) ⟨1603772, by rfl⟩ : syracuseStep 2138363 = 3207545) B3207545
theorem B2138447 : Blo 1425532 2138447 := bstep (se 1 (by rfl) ⟨1603835, by rfl⟩ : syracuseStep 2138447 = 3207671) B3207671
theorem B8126801 : Blo 1425532 8126801 := bstep (se 2 (by rfl) ⟨3047550, by rfl⟩ : syracuseStep 8126801 = 6095101) B6095101
theorem B1425903 : Blo 1425532 1425903 := bstep (se 1 (by rfl) ⟨1069427, by rfl⟩ : syracuseStep 1425903 = 2138855) B2138855
theorem B3211775 : Blo 1425532 3211775 := bstep (se 1 (by rfl) ⟨2408831, by rfl⟩ : syracuseStep 3211775 = 4817663) B4817663
theorem B1426011 : Blo 1425532 1426011 := bstep (se 1 (by rfl) ⟨1069508, by rfl⟩ : syracuseStep 1426011 = 2139017) B2139017
theorem B11575973 : Blo 1425532 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B3253115 : Blo 1425532 3253115 := bstep (se 1 (by rfl) ⟨2439836, by rfl⟩ : syracuseStep 3253115 = 4879673) B4879673
theorem B2139263 : Blo 1425532 2139263 := bstep (se 1 (by rfl) ⟨1604447, by rfl⟩ : syracuseStep 2139263 = 3208895) B3208895
theorem B16237745 : Blo 1425532 16237745 := bstep (se 2 (by rfl) ⟨6089154, by rfl⟩ : syracuseStep 16237745 = 12178309) B12178309
theorem B7218395 : Blo 1425532 7218395 := bstep (se 1 (by rfl) ⟨5413796, by rfl⟩ : syracuseStep 7218395 = 10827593) B10827593
theorem B2139401 : Blo 1425532 2139401 := bstep (se 2 (by rfl) ⟨802275, by rfl⟩ : syracuseStep 2139401 = 1604551) B1604551
theorem B29263517 : Blo 1425532 29263517 := bstep (se 3 (by rfl) ⟨5486909, by rfl⟩ : syracuseStep 29263517 = 10973819) B10973819
theorem B1427291 : Blo 1425532 1427291 := bstep (se 1 (by rfl) ⟨1070468, by rfl⟩ : syracuseStep 1427291 = 2140937) B2140937
theorem B2140271 : Blo 1425532 2140271 := bstep (se 1 (by rfl) ⟨1605203, by rfl⟩ : syracuseStep 2140271 = 3210407) B3210407
theorem B2140487 : Blo 1425532 2140487 := bstep (se 1 (by rfl) ⟨1605365, by rfl⟩ : syracuseStep 2140487 = 3210731) B3210731
theorem B1927999 : Blo 1425532 1927999 := bstep (se 1 (by rfl) ⟨1445999, by rfl⟩ : syracuseStep 1927999 = 2891999) B2891999
theorem B5139283 : Blo 1425532 5139283 := bstep (se 1 (by rfl) ⟨3854462, by rfl⟩ : syracuseStep 5139283 = 7708925) B7708925
theorem B6090011 : Blo 1425532 6090011 := bstep (se 1 (by rfl) ⟨4567508, by rfl⟩ : syracuseStep 6090011 = 9135017) B9135017
theorem B4812479 : Blo 1425532 4812479 := bstep (se 1 (by rfl) ⟨3609359, by rfl⟩ : syracuseStep 4812479 = 7218719) B7218719
theorem B7221473 : Blo 1425532 7221473 := bstep (se 2 (by rfl) ⟨2708052, by rfl⟩ : syracuseStep 7221473 = 5416105) B5416105
theorem B197759717 : Blo 1425532 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B131830583 : Blo 1425532 131830583 := bstep (se 1 (by rfl) ⟨98872937, by rfl⟩ : syracuseStep 131830583 = 197745875) B197745875
theorem B7927289 : Blo 1425532 7927289 := bstep (se 2 (by rfl) ⟨2972733, by rfl⟩ : syracuseStep 7927289 = 5945467) B5945467
theorem B20567915 : Blo 1425532 20567915 := bstep (se 1 (by rfl) ⟨15425936, by rfl⟩ : syracuseStep 20567915 = 30851873) B30851873
theorem B35674019 : Blo 1425532 35674019 := bstep (se 1 (by rfl) ⟨26755514, by rfl⟩ : syracuseStep 35674019 = 53511029) B53511029
theorem B5863535 : Blo 1425532 5863535 := bstep (se 1 (by rfl) ⟨4397651, by rfl⟩ : syracuseStep 5863535 = 8795303) B8795303
theorem B12179645 : Blo 1425532 12179645 := bstep (se 3 (by rfl) ⟨2283683, by rfl⟩ : syracuseStep 12179645 = 4567367) B4567367
theorem B8124887 : Blo 1425532 8124887 := bstep (se 1 (by rfl) ⟨6093665, by rfl⟩ : syracuseStep 8124887 = 12187331) B12187331
theorem B10829051 : Blo 1425532 10829051 := bstep (se 1 (by rfl) ⟨8121788, by rfl⟩ : syracuseStep 10829051 = 16243577) B16243577
theorem B20561627 : Blo 1425532 20561627 := bstep (se 1 (by rfl) ⟨15421220, by rfl⟩ : syracuseStep 20561627 = 30842441) B30842441
theorem B1425575 : Blo 1425532 1425575 := bstep (se 1 (by rfl) ⟨1069181, by rfl⟩ : syracuseStep 1425575 = 2138363) B2138363
theorem B1425631 : Blo 1425532 1425631 := bstep (se 1 (by rfl) ⟨1069223, by rfl⟩ : syracuseStep 1425631 = 2138447) B2138447
theorem B7717315 : Blo 1425532 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B1426175 : Blo 1425532 1426175 := bstep (se 1 (by rfl) ⟨1069631, by rfl⟩ : syracuseStep 1426175 = 2139263) B2139263
theorem B1426267 : Blo 1425532 1426267 := bstep (se 1 (by rfl) ⟨1069700, by rfl⟩ : syracuseStep 1426267 = 2139401) B2139401
theorem B23782679 : Blo 1425532 23782679 := bstep (se 1 (by rfl) ⟨17837009, by rfl⟩ : syracuseStep 23782679 = 35674019) B35674019
theorem B3909023 : Blo 1425532 3909023 := bstep (se 1 (by rfl) ⟨2931767, by rfl⟩ : syracuseStep 3909023 = 5863535) B5863535
theorem B1426847 : Blo 1425532 1426847 := bstep (se 1 (by rfl) ⟨1070135, by rfl⟩ : syracuseStep 1426847 = 2140271) B2140271
theorem B8119763 : Blo 1425532 8119763 := bstep (se 1 (by rfl) ⟨6089822, by rfl⟩ : syracuseStep 8119763 = 12179645) B12179645
theorem B1426991 : Blo 1425532 1426991 := bstep (se 1 (by rfl) ⟨1070243, by rfl⟩ : syracuseStep 1426991 = 2140487) B2140487
theorem B5416591 : Blo 1425532 5416591 := bstep (se 1 (by rfl) ⟨4062443, by rfl⟩ : syracuseStep 5416591 = 8124887) B8124887
theorem B7219367 : Blo 1425532 7219367 := bstep (se 1 (by rfl) ⟨5414525, by rfl⟩ : syracuseStep 7219367 = 10829051) B10829051
theorem B13707751 : Blo 1425532 13707751 := bstep (se 1 (by rfl) ⟨10280813, by rfl⟩ : syracuseStep 13707751 = 20561627) B20561627
theorem B5417867 : Blo 1425532 5417867 := bstep (se 1 (by rfl) ⟨4063400, by rfl⟩ : syracuseStep 5417867 = 8126801) B8126801
theorem B2141183 : Blo 1425532 2141183 := bstep (se 1 (by rfl) ⟨1605887, by rfl⟩ : syracuseStep 2141183 = 3211775) B3211775
theorem B10825163 : Blo 1425532 10825163 := bstep (se 1 (by rfl) ⟨8118872, by rfl⟩ : syracuseStep 10825163 = 16237745) B16237745
theorem B4812263 : Blo 1425532 4812263 := bstep (se 1 (by rfl) ⟨3609197, by rfl⟩ : syracuseStep 4812263 = 7218395) B7218395
theorem B19509011 : Blo 1425532 19509011 := bstep (se 1 (by rfl) ⟨14631758, by rfl⟩ : syracuseStep 19509011 = 29263517) B29263517
theorem B6852377 : Blo 1425532 6852377 := bstep (se 2 (by rfl) ⟨2569641, by rfl⟩ : syracuseStep 6852377 = 5139283) B5139283
theorem B351548221 : Blo 1425532 351548221 := bstep (se 3 (by rfl) ⟨65915291, by rfl⟩ : syracuseStep 351548221 = 131830583) B131830583
theorem B4060007 : Blo 1425532 4060007 := bstep (se 1 (by rfl) ⟨3045005, by rfl⟩ : syracuseStep 4060007 = 6090011) B6090011
theorem B3208319 : Blo 1425532 3208319 := bstep (se 1 (by rfl) ⟨2406239, by rfl⟩ : syracuseStep 3208319 = 4812479) B4812479
theorem B10835369 : Blo 1425532 10835369 := bstep (se 2 (by rfl) ⟨4063263, by rfl⟩ : syracuseStep 10835369 = 8126527) B8126527
theorem B4814315 : Blo 1425532 4814315 := bstep (se 1 (by rfl) ⟨3610736, by rfl⟩ : syracuseStep 4814315 = 7221473) B7221473
theorem B131839811 : Blo 1425532 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B2168743 : Blo 1425532 2168743 := bstep (se 1 (by rfl) ⟨1626557, by rfl⟩ : syracuseStep 2168743 = 3253115) B3253115
theorem B2570665 : Blo 1425532 2570665 := bstep (se 2 (by rfl) ⟨963999, by rfl⟩ : syracuseStep 2570665 = 1927999) B1927999
theorem B13711943 : Blo 1425532 13711943 := bstep (se 1 (by rfl) ⟨10283957, by rfl⟩ : syracuseStep 13711943 = 20567915) B20567915
theorem B84557749 : Blo 1425532 84557749 := bstep (se 5 (by rfl) ⟨3963644, by rfl⟩ : syracuseStep 84557749 = 7927289) B7927289
theorem B10289753 : Blo 1425532 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B18277001 : Blo 1425532 18277001 := bstep (se 2 (by rfl) ⟨6853875, by rfl⟩ : syracuseStep 18277001 = 13707751) B13707751
theorem B2138879 : Blo 1425532 2138879 := bstep (se 1 (by rfl) ⟨1604159, by rfl⟩ : syracuseStep 2138879 = 3208319) B3208319
theorem B2606015 : Blo 1425532 2606015 := bstep (se 1 (by rfl) ⟨1954511, by rfl⟩ : syracuseStep 2606015 = 3909023) B3909023
theorem B468730961 : Blo 1425532 468730961 := bstep (se 2 (by rfl) ⟨175774110, by rfl⟩ : syracuseStep 468730961 = 351548221) B351548221
theorem B87893207 : Blo 1425532 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B1427455 : Blo 1425532 1427455 := bstep (se 1 (by rfl) ⟨1070591, by rfl⟩ : syracuseStep 1427455 = 2141183) B2141183
theorem B3427553 : Blo 1425532 3427553 := bstep (se 2 (by rfl) ⟨1285332, by rfl⟩ : syracuseStep 3427553 = 2570665) B2570665
theorem B2706671 : Blo 1425532 2706671 := bstep (se 1 (by rfl) ⟨2030003, by rfl⟩ : syracuseStep 2706671 = 4060007) B4060007
theorem B15855119 : Blo 1425532 15855119 := bstep (se 1 (by rfl) ⟨11891339, by rfl⟩ : syracuseStep 15855119 = 23782679) B23782679
theorem B4812911 : Blo 1425532 4812911 := bstep (se 1 (by rfl) ⟨3609683, by rfl⟩ : syracuseStep 4812911 = 7219367) B7219367
theorem B7222121 : Blo 1425532 7222121 := bstep (se 2 (by rfl) ⟨2708295, by rfl⟩ : syracuseStep 7222121 = 5416591) B5416591
theorem B3208175 : Blo 1425532 3208175 := bstep (se 1 (by rfl) ⟨2406131, by rfl⟩ : syracuseStep 3208175 = 4812263) B4812263
theorem B13006007 : Blo 1425532 13006007 := bstep (se 1 (by rfl) ⟨9754505, by rfl⟩ : syracuseStep 13006007 = 19509011) B19509011
theorem B4568251 : Blo 1425532 4568251 := bstep (se 1 (by rfl) ⟨3426188, by rfl⟩ : syracuseStep 4568251 = 6852377) B6852377
theorem B112743665 : Blo 1425532 112743665 := bstep (se 2 (by rfl) ⟨42278874, by rfl⟩ : syracuseStep 112743665 = 84557749) B84557749
theorem B7223579 : Blo 1425532 7223579 := bstep (se 1 (by rfl) ⟨5417684, by rfl⟩ : syracuseStep 7223579 = 10835369) B10835369
theorem B5413175 : Blo 1425532 5413175 := bstep (se 1 (by rfl) ⟨4059881, by rfl⟩ : syracuseStep 5413175 = 8119763) B8119763
theorem B3209543 : Blo 1425532 3209543 := bstep (se 1 (by rfl) ⟨2407157, by rfl⟩ : syracuseStep 3209543 = 4814315) B4814315
theorem B9141295 : Blo 1425532 9141295 := bstep (se 1 (by rfl) ⟨6855971, by rfl⟩ : syracuseStep 9141295 = 13711943) B13711943
theorem B3611911 : Blo 1425532 3611911 := bstep (se 1 (by rfl) ⟨2708933, by rfl⟩ : syracuseStep 3611911 = 5417867) B5417867
theorem B7216775 : Blo 1425532 7216775 := bstep (se 1 (by rfl) ⟨5412581, by rfl⟩ : syracuseStep 7216775 = 10825163) B10825163
theorem B2891657 : Blo 1425532 2891657 := bstep (se 2 (by rfl) ⟨1084371, by rfl⟩ : syracuseStep 2891657 = 2168743) B2168743
theorem B1425919 : Blo 1425532 1425919 := bstep (se 1 (by rfl) ⟨1069439, by rfl⟩ : syracuseStep 1425919 = 2138879) B2138879
theorem B2138783 : Blo 1425532 2138783 := bstep (se 1 (by rfl) ⟨1604087, by rfl⟩ : syracuseStep 2138783 = 3208175) B3208175
theorem B75162443 : Blo 1425532 75162443 := bstep (se 1 (by rfl) ⟨56371832, by rfl⟩ : syracuseStep 75162443 = 112743665) B112743665
theorem B2139695 : Blo 1425532 2139695 := bstep (se 1 (by rfl) ⟨1604771, by rfl⟩ : syracuseStep 2139695 = 3209543) B3209543
theorem B1804447 : Blo 1425532 1804447 := bstep (se 1 (by rfl) ⟨1353335, by rfl⟩ : syracuseStep 1804447 = 2706671) B2706671
theorem B10570079 : Blo 1425532 10570079 := bstep (se 1 (by rfl) ⟨7927559, by rfl⟩ : syracuseStep 10570079 = 15855119) B15855119
theorem B7711085 : Blo 1425532 7711085 := bstep (se 3 (by rfl) ⟨1445828, by rfl⟩ : syracuseStep 7711085 = 2891657) B2891657
theorem B4811183 : Blo 1425532 4811183 := bstep (se 1 (by rfl) ⟨3608387, by rfl⟩ : syracuseStep 4811183 = 7216775) B7216775
theorem B6949373 : Blo 1425532 6949373 := bstep (se 3 (by rfl) ⟨1303007, by rfl⟩ : syracuseStep 6949373 = 2606015) B2606015
theorem B6859835 : Blo 1425532 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B12184667 : Blo 1425532 12184667 := bstep (se 1 (by rfl) ⟨9138500, by rfl⟩ : syracuseStep 12184667 = 18277001) B18277001
theorem B312487307 : Blo 1425532 312487307 := bstep (se 1 (by rfl) ⟨234365480, by rfl⟩ : syracuseStep 312487307 = 468730961) B468730961
theorem B8670671 : Blo 1425532 8670671 := bstep (se 1 (by rfl) ⟨6503003, by rfl⟩ : syracuseStep 8670671 = 13006007) B13006007
theorem B3608783 : Blo 1425532 3608783 := bstep (se 1 (by rfl) ⟨2706587, by rfl⟩ : syracuseStep 3608783 = 5413175) B5413175
theorem B6091001 : Blo 1425532 6091001 := bstep (se 2 (by rfl) ⟨2284125, by rfl⟩ : syracuseStep 6091001 = 4568251) B4568251
theorem B3208607 : Blo 1425532 3208607 := bstep (se 1 (by rfl) ⟨2406455, by rfl⟩ : syracuseStep 3208607 = 4812911) B4812911
theorem B4814747 : Blo 1425532 4814747 := bstep (se 1 (by rfl) ⟨3611060, by rfl⟩ : syracuseStep 4814747 = 7222121) B7222121
theorem B9140141 : Blo 1425532 9140141 := bstep (se 3 (by rfl) ⟨1713776, by rfl⟩ : syracuseStep 9140141 = 3427553) B3427553
theorem B58595471 : Blo 1425532 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B12188393 : Blo 1425532 12188393 := bstep (se 2 (by rfl) ⟨4570647, by rfl⟩ : syracuseStep 12188393 = 9141295) B9141295
theorem B4815719 : Blo 1425532 4815719 := bstep (se 1 (by rfl) ⟨3611789, by rfl⟩ : syracuseStep 4815719 = 7223579) B7223579
theorem B4815881 : Blo 1425532 4815881 := bstep (se 2 (by rfl) ⟨1805955, by rfl⟩ : syracuseStep 4815881 = 3611911) B3611911
theorem B1425855 : Blo 1425532 1425855 := bstep (se 1 (by rfl) ⟨1069391, by rfl⟩ : syracuseStep 1425855 = 2138783) B2138783
theorem B2139071 : Blo 1425532 2139071 := bstep (se 1 (by rfl) ⟨1604303, by rfl⟩ : syracuseStep 2139071 = 3208607) B3208607
theorem B20562893 : Blo 1425532 20562893 := bstep (se 3 (by rfl) ⟨3855542, by rfl⟩ : syracuseStep 20562893 = 7711085) B7711085
theorem B1426463 : Blo 1425532 1426463 := bstep (se 1 (by rfl) ⟨1069847, by rfl⟩ : syracuseStep 1426463 = 2139695) B2139695
theorem B18531661 : Blo 1425532 18531661 := bstep (se 3 (by rfl) ⟨3474686, by rfl⟩ : syracuseStep 18531661 = 6949373) B6949373
theorem B7046719 : Blo 1425532 7046719 := bstep (se 1 (by rfl) ⟨5285039, by rfl⟩ : syracuseStep 7046719 = 10570079) B10570079
theorem B4573223 : Blo 1425532 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B208324871 : Blo 1425532 208324871 := bstep (se 1 (by rfl) ⟨156243653, by rfl⟩ : syracuseStep 208324871 = 312487307) B312487307
theorem B39063647 : Blo 1425532 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B3207455 : Blo 1425532 3207455 := bstep (se 1 (by rfl) ⟨2405591, by rfl⟩ : syracuseStep 3207455 = 4811183) B4811183
theorem B8123111 : Blo 1425532 8123111 := bstep (se 1 (by rfl) ⟨6092333, by rfl⟩ : syracuseStep 8123111 = 12184667) B12184667
theorem B5780447 : Blo 1425532 5780447 := bstep (se 1 (by rfl) ⟨4335335, by rfl⟩ : syracuseStep 5780447 = 8670671) B8670671
theorem B2405855 : Blo 1425532 2405855 := bstep (se 1 (by rfl) ⟨1804391, by rfl⟩ : syracuseStep 2405855 = 3608783) B3608783
theorem B4060667 : Blo 1425532 4060667 := bstep (se 1 (by rfl) ⟨3045500, by rfl⟩ : syracuseStep 4060667 = 6091001) B6091001
theorem B2405929 : Blo 1425532 2405929 := bstep (se 2 (by rfl) ⟨902223, by rfl⟩ : syracuseStep 2405929 = 1804447) B1804447
theorem B801732725 : Blo 1425532 801732725 := bstep (se 5 (by rfl) ⟨37581221, by rfl⟩ : syracuseStep 801732725 = 75162443) B75162443
theorem B3209831 : Blo 1425532 3209831 := bstep (se 1 (by rfl) ⟨2407373, by rfl⟩ : syracuseStep 3209831 = 4814747) B4814747
theorem B6093427 : Blo 1425532 6093427 := bstep (se 1 (by rfl) ⟨4570070, by rfl⟩ : syracuseStep 6093427 = 9140141) B9140141
theorem B8125595 : Blo 1425532 8125595 := bstep (se 1 (by rfl) ⟨6094196, by rfl⟩ : syracuseStep 8125595 = 12188393) B12188393
theorem B3210479 : Blo 1425532 3210479 := bstep (se 1 (by rfl) ⟨2407859, by rfl⟩ : syracuseStep 3210479 = 4815719) B4815719
theorem B3210587 : Blo 1425532 3210587 := bstep (se 1 (by rfl) ⟨2407940, by rfl⟩ : syracuseStep 3210587 = 4815881) B4815881
theorem B26042431 : Blo 1425532 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B2138303 : Blo 1425532 2138303 := bstep (se 1 (by rfl) ⟨1603727, by rfl⟩ : syracuseStep 2138303 = 3207455) B3207455
theorem B5415407 : Blo 1425532 5415407 := bstep (se 1 (by rfl) ⟨4061555, by rfl⟩ : syracuseStep 5415407 = 8123111) B8123111
theorem B1426047 : Blo 1425532 1426047 := bstep (se 1 (by rfl) ⟨1069535, by rfl⟩ : syracuseStep 1426047 = 2139071) B2139071
theorem B3048815 : Blo 1425532 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B534488483 : Blo 1425532 534488483 := bstep (se 1 (by rfl) ⟨400866362, by rfl⟩ : syracuseStep 534488483 = 801732725) B801732725
theorem B2139887 : Blo 1425532 2139887 := bstep (se 1 (by rfl) ⟨1604915, by rfl⟩ : syracuseStep 2139887 = 3209831) B3209831
theorem B24708881 : Blo 1425532 24708881 := bstep (se 2 (by rfl) ⟨9265830, by rfl⟩ : syracuseStep 24708881 = 18531661) B18531661
theorem B5417063 : Blo 1425532 5417063 := bstep (se 1 (by rfl) ⟨4062797, by rfl⟩ : syracuseStep 5417063 = 8125595) B8125595
theorem B2140319 : Blo 1425532 2140319 := bstep (se 1 (by rfl) ⟨1605239, by rfl⟩ : syracuseStep 2140319 = 3210479) B3210479
theorem B2140391 : Blo 1425532 2140391 := bstep (se 1 (by rfl) ⟨1605293, by rfl⟩ : syracuseStep 2140391 = 3210587) B3210587
theorem B13708595 : Blo 1425532 13708595 := bstep (se 1 (by rfl) ⟨10281446, by rfl⟩ : syracuseStep 13708595 = 20562893) B20562893
theorem B3853631 : Blo 1425532 3853631 := bstep (se 1 (by rfl) ⟨2890223, by rfl⟩ : syracuseStep 3853631 = 5780447) B5780447
theorem B2707111 : Blo 1425532 2707111 := bstep (se 1 (by rfl) ⟨2030333, by rfl⟩ : syracuseStep 2707111 = 4060667) B4060667
theorem B138883247 : Blo 1425532 138883247 := bstep (se 1 (by rfl) ⟨104162435, by rfl⟩ : syracuseStep 138883247 = 208324871) B208324871
theorem B3207905 : Blo 1425532 3207905 := bstep (se 2 (by rfl) ⟨1202964, by rfl⟩ : syracuseStep 3207905 = 2405929) B2405929
theorem B37582501 : Blo 1425532 37582501 := bstep (se 4 (by rfl) ⟨3523359, by rfl⟩ : syracuseStep 37582501 = 7046719) B7046719
theorem B8124569 : Blo 1425532 8124569 := bstep (se 2 (by rfl) ⟨3046713, by rfl⟩ : syracuseStep 8124569 = 6093427) B6093427
theorem B1603903 : Blo 1425532 1603903 := bstep (se 1 (by rfl) ⟨1202927, by rfl⟩ : syracuseStep 1603903 = 2405855) B2405855
theorem B1425535 : Blo 1425532 1425535 := bstep (se 1 (by rfl) ⟨1069151, by rfl⟩ : syracuseStep 1425535 = 2138303) B2138303
theorem B2138537 : Blo 1425532 2138537 := bstep (se 2 (by rfl) ⟨801951, by rfl⟩ : syracuseStep 2138537 = 1603903) B1603903
theorem B2138603 : Blo 1425532 2138603 := bstep (se 1 (by rfl) ⟨1603952, by rfl⟩ : syracuseStep 2138603 = 3207905) B3207905
theorem B2032543 : Blo 1425532 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B1426591 : Blo 1425532 1426591 := bstep (se 1 (by rfl) ⟨1069943, by rfl⟩ : syracuseStep 1426591 = 2139887) B2139887
theorem B5416379 : Blo 1425532 5416379 := bstep (se 1 (by rfl) ⟨4062284, by rfl⟩ : syracuseStep 5416379 = 8124569) B8124569
theorem B1426879 : Blo 1425532 1426879 := bstep (se 1 (by rfl) ⟨1070159, by rfl⟩ : syracuseStep 1426879 = 2140319) B2140319
theorem B1426927 : Blo 1425532 1426927 := bstep (se 1 (by rfl) ⟨1070195, by rfl⟩ : syracuseStep 1426927 = 2140391) B2140391
theorem B92588831 : Blo 1425532 92588831 := bstep (se 1 (by rfl) ⟨69441623, by rfl⟩ : syracuseStep 92588831 = 138883247) B138883247
theorem B9139063 : Blo 1425532 9139063 := bstep (se 1 (by rfl) ⟨6854297, by rfl⟩ : syracuseStep 9139063 = 13708595) B13708595
theorem B2569087 : Blo 1425532 2569087 := bstep (se 1 (by rfl) ⟨1926815, by rfl⟩ : syracuseStep 2569087 = 3853631) B3853631
theorem B3609481 : Blo 1425532 3609481 := bstep (se 2 (by rfl) ⟨1353555, by rfl⟩ : syracuseStep 3609481 = 2707111) B2707111
theorem B34723241 : Blo 1425532 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B3610271 : Blo 1425532 3610271 := bstep (se 1 (by rfl) ⟨2707703, by rfl⟩ : syracuseStep 3610271 = 5415407) B5415407
theorem B356325655 : Blo 1425532 356325655 := bstep (se 1 (by rfl) ⟨267244241, by rfl⟩ : syracuseStep 356325655 = 534488483) B534488483
theorem B16472587 : Blo 1425532 16472587 := bstep (se 1 (by rfl) ⟨12354440, by rfl⟩ : syracuseStep 16472587 = 24708881) B24708881
theorem B3611375 : Blo 1425532 3611375 := bstep (se 1 (by rfl) ⟨2708531, by rfl⟩ : syracuseStep 3611375 = 5417063) B5417063
theorem B50110001 : Blo 1425532 50110001 := bstep (se 2 (by rfl) ⟨18791250, by rfl⟩ : syracuseStep 50110001 = 37582501) B37582501
theorem B1425691 : Blo 1425532 1425691 := bstep (se 1 (by rfl) ⟨1069268, by rfl⟩ : syracuseStep 1425691 = 2138537) B2138537
theorem B1425735 : Blo 1425532 1425735 := bstep (se 1 (by rfl) ⟨1069301, by rfl⟩ : syracuseStep 1425735 = 2138603) B2138603
theorem B21963449 : Blo 1425532 21963449 := bstep (se 2 (by rfl) ⟨8236293, by rfl⟩ : syracuseStep 21963449 = 16472587) B16472587
theorem B10840229 : Blo 1425532 10840229 := bstep (se 4 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 10840229 = 2032543) B2032543
theorem B12185417 : Blo 1425532 12185417 := bstep (se 2 (by rfl) ⟨4569531, by rfl⟩ : syracuseStep 12185417 = 9139063) B9139063
theorem B4812641 : Blo 1425532 4812641 := bstep (se 2 (by rfl) ⟨1804740, by rfl⟩ : syracuseStep 4812641 = 3609481) B3609481
theorem B13701797 : Blo 1425532 13701797 := bstep (se 4 (by rfl) ⟨1284543, by rfl⟩ : syracuseStep 13701797 = 2569087) B2569087
theorem B475100873 : Blo 1425532 475100873 := bstep (se 2 (by rfl) ⟨178162827, by rfl⟩ : syracuseStep 475100873 = 356325655) B356325655
theorem B23148827 : Blo 1425532 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B3610919 : Blo 1425532 3610919 := bstep (se 1 (by rfl) ⟨2708189, by rfl⟩ : syracuseStep 3610919 = 5416379) B5416379
theorem B2406847 : Blo 1425532 2406847 := bstep (se 1 (by rfl) ⟨1805135, by rfl⟩ : syracuseStep 2406847 = 3610271) B3610271
theorem B2407583 : Blo 1425532 2407583 := bstep (se 1 (by rfl) ⟨1805687, by rfl⟩ : syracuseStep 2407583 = 3611375) B3611375
theorem B61725887 : Blo 1425532 61725887 := bstep (se 1 (by rfl) ⟨46294415, by rfl⟩ : syracuseStep 61725887 = 92588831) B92588831
theorem B33406667 : Blo 1425532 33406667 := bstep (se 1 (by rfl) ⟨25055000, by rfl⟩ : syracuseStep 33406667 = 50110001) B50110001
theorem B9134531 : Blo 1425532 9134531 := bstep (se 1 (by rfl) ⟨6850898, by rfl⟩ : syracuseStep 9134531 = 13701797) B13701797
theorem B7226819 : Blo 1425532 7226819 := bstep (se 1 (by rfl) ⟨5420114, by rfl⟩ : syracuseStep 7226819 = 10840229) B10840229
theorem B41150591 : Blo 1425532 41150591 := bstep (se 1 (by rfl) ⟨30862943, by rfl⟩ : syracuseStep 41150591 = 61725887) B61725887
theorem B14642299 : Blo 1425532 14642299 := bstep (se 1 (by rfl) ⟨10981724, by rfl⟩ : syracuseStep 14642299 = 21963449) B21963449
theorem B22271111 : Blo 1425532 22271111 := bstep (se 1 (by rfl) ⟨16703333, by rfl⟩ : syracuseStep 22271111 = 33406667) B33406667
theorem B8123611 : Blo 1425532 8123611 := bstep (se 1 (by rfl) ⟨6092708, by rfl⟩ : syracuseStep 8123611 = 12185417) B12185417
theorem B3208427 : Blo 1425532 3208427 := bstep (se 1 (by rfl) ⟨2406320, by rfl⟩ : syracuseStep 3208427 = 4812641) B4812641
theorem B3209129 : Blo 1425532 3209129 := bstep (se 2 (by rfl) ⟨1203423, by rfl⟩ : syracuseStep 3209129 = 2406847) B2406847
theorem B316733915 : Blo 1425532 316733915 := bstep (se 1 (by rfl) ⟨237550436, by rfl⟩ : syracuseStep 316733915 = 475100873) B475100873
theorem B15432551 : Blo 1425532 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B2407279 : Blo 1425532 2407279 := bstep (se 1 (by rfl) ⟨1805459, by rfl⟩ : syracuseStep 2407279 = 3610919) B3610919
theorem B1605055 : Blo 1425532 1605055 := bstep (se 1 (by rfl) ⟨1203791, by rfl⟩ : syracuseStep 1605055 = 2407583) B2407583
theorem B2138951 : Blo 1425532 2138951 := bstep (se 1 (by rfl) ⟨1604213, by rfl⟩ : syracuseStep 2138951 = 3208427) B3208427
theorem B4817879 : Blo 1425532 4817879 := bstep (se 1 (by rfl) ⟨3613409, by rfl⟩ : syracuseStep 4817879 = 7226819) B7226819
theorem B2139419 : Blo 1425532 2139419 := bstep (se 1 (by rfl) ⟨1604564, by rfl⟩ : syracuseStep 2139419 = 3209129) B3209129
theorem B19523065 : Blo 1425532 19523065 := bstep (se 2 (by rfl) ⟨7321149, by rfl⟩ : syracuseStep 19523065 = 14642299) B14642299
theorem B10831481 : Blo 1425532 10831481 := bstep (se 2 (by rfl) ⟨4061805, by rfl⟩ : syracuseStep 10831481 = 8123611) B8123611
theorem B2140073 : Blo 1425532 2140073 := bstep (se 2 (by rfl) ⟨802527, by rfl⟩ : syracuseStep 2140073 = 1605055) B1605055
theorem B6089687 : Blo 1425532 6089687 := bstep (se 1 (by rfl) ⟨4567265, by rfl⟩ : syracuseStep 6089687 = 9134531) B9134531
theorem B14847407 : Blo 1425532 14847407 := bstep (se 1 (by rfl) ⟨11135555, by rfl⟩ : syracuseStep 14847407 = 22271111) B22271111
theorem B3209705 : Blo 1425532 3209705 := bstep (se 2 (by rfl) ⟨1203639, by rfl⟩ : syracuseStep 3209705 = 2407279) B2407279
theorem B27433727 : Blo 1425532 27433727 := bstep (se 1 (by rfl) ⟨20575295, by rfl⟩ : syracuseStep 27433727 = 41150591) B41150591
theorem B211155943 : Blo 1425532 211155943 := bstep (se 1 (by rfl) ⟨158366957, by rfl⟩ : syracuseStep 211155943 = 316733915) B316733915
theorem B10288367 : Blo 1425532 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B1425967 : Blo 1425532 1425967 := bstep (se 1 (by rfl) ⟨1069475, by rfl⟩ : syracuseStep 1425967 = 2138951) B2138951
theorem B3211919 : Blo 1425532 3211919 := bstep (se 1 (by rfl) ⟨2408939, by rfl⟩ : syracuseStep 3211919 = 4817879) B4817879
theorem B1426279 : Blo 1425532 1426279 := bstep (se 1 (by rfl) ⟨1069709, by rfl⟩ : syracuseStep 1426279 = 2139419) B2139419
theorem B1426715 : Blo 1425532 1426715 := bstep (se 1 (by rfl) ⟨1070036, by rfl⟩ : syracuseStep 1426715 = 2140073) B2140073
theorem B2139803 : Blo 1425532 2139803 := bstep (se 1 (by rfl) ⟨1604852, by rfl⟩ : syracuseStep 2139803 = 3209705) B3209705
theorem B6858911 : Blo 1425532 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B9898271 : Blo 1425532 9898271 := bstep (se 1 (by rfl) ⟨7423703, by rfl⟩ : syracuseStep 9898271 = 14847407) B14847407
theorem B7220987 : Blo 1425532 7220987 := bstep (se 1 (by rfl) ⟨5415740, by rfl⟩ : syracuseStep 7220987 = 10831481) B10831481
theorem B18289151 : Blo 1425532 18289151 := bstep (se 1 (by rfl) ⟨13716863, by rfl⟩ : syracuseStep 18289151 = 27433727) B27433727
theorem B4059791 : Blo 1425532 4059791 := bstep (se 1 (by rfl) ⟨3044843, by rfl⟩ : syracuseStep 4059791 = 6089687) B6089687
theorem B26030753 : Blo 1425532 26030753 := bstep (se 2 (by rfl) ⟨9761532, by rfl⟩ : syracuseStep 26030753 = 19523065) B19523065
theorem B281541257 : Blo 1425532 281541257 := bstep (se 2 (by rfl) ⟨105577971, by rfl⟩ : syracuseStep 281541257 = 211155943) B211155943
theorem B1426535 : Blo 1425532 1426535 := bstep (se 1 (by rfl) ⟨1069901, by rfl⟩ : syracuseStep 1426535 = 2139803) B2139803
theorem B4572607 : Blo 1425532 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B12192767 : Blo 1425532 12192767 := bstep (se 1 (by rfl) ⟨9144575, by rfl⟩ : syracuseStep 12192767 = 18289151) B18289151
theorem B2706527 : Blo 1425532 2706527 := bstep (se 1 (by rfl) ⟨2029895, by rfl⟩ : syracuseStep 2706527 = 4059791) B4059791
theorem B2141279 : Blo 1425532 2141279 := bstep (se 1 (by rfl) ⟨1605959, by rfl⟩ : syracuseStep 2141279 = 3211919) B3211919
theorem B17353835 : Blo 1425532 17353835 := bstep (se 1 (by rfl) ⟨13015376, by rfl⟩ : syracuseStep 17353835 = 26030753) B26030753
theorem B6598847 : Blo 1425532 6598847 := bstep (se 1 (by rfl) ⟨4949135, by rfl⟩ : syracuseStep 6598847 = 9898271) B9898271
theorem B4813991 : Blo 1425532 4813991 := bstep (se 1 (by rfl) ⟨3610493, by rfl⟩ : syracuseStep 4813991 = 7220987) B7220987
theorem B187694171 : Blo 1425532 187694171 := bstep (se 1 (by rfl) ⟨140770628, by rfl⟩ : syracuseStep 187694171 = 281541257) B281541257
theorem B4399231 : Blo 1425532 4399231 := bstep (se 1 (by rfl) ⟨3299423, by rfl⟩ : syracuseStep 4399231 = 6598847) B6598847
theorem B6096809 : Blo 1425532 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B8128511 : Blo 1425532 8128511 := bstep (se 1 (by rfl) ⟨6096383, by rfl⟩ : syracuseStep 8128511 = 12192767) B12192767
theorem B1804351 : Blo 1425532 1804351 := bstep (se 1 (by rfl) ⟨1353263, by rfl⟩ : syracuseStep 1804351 = 2706527) B2706527
theorem B1427519 : Blo 1425532 1427519 := bstep (se 1 (by rfl) ⟨1070639, by rfl⟩ : syracuseStep 1427519 = 2141279) B2141279
theorem B11569223 : Blo 1425532 11569223 := bstep (se 1 (by rfl) ⟨8676917, by rfl⟩ : syracuseStep 11569223 = 17353835) B17353835
theorem B125129447 : Blo 1425532 125129447 := bstep (se 1 (by rfl) ⟨93847085, by rfl⟩ : syracuseStep 125129447 = 187694171) B187694171
theorem B3209327 : Blo 1425532 3209327 := bstep (se 1 (by rfl) ⟨2406995, by rfl⟩ : syracuseStep 3209327 = 4813991) B4813991
theorem B5865641 : Blo 1425532 5865641 := bstep (se 2 (by rfl) ⟨2199615, by rfl⟩ : syracuseStep 5865641 = 4399231) B4399231
theorem B83419631 : Blo 1425532 83419631 := bstep (se 1 (by rfl) ⟨62564723, by rfl⟩ : syracuseStep 83419631 = 125129447) B125129447
theorem B2139551 : Blo 1425532 2139551 := bstep (se 1 (by rfl) ⟨1604663, by rfl⟩ : syracuseStep 2139551 = 3209327) B3209327
theorem B5419007 : Blo 1425532 5419007 := bstep (se 1 (by rfl) ⟨4064255, by rfl⟩ : syracuseStep 5419007 = 8128511) B8128511
theorem B7712815 : Blo 1425532 7712815 := bstep (se 1 (by rfl) ⟨5784611, by rfl⟩ : syracuseStep 7712815 = 11569223) B11569223
theorem B16258157 : Blo 1425532 16258157 := bstep (se 3 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 16258157 = 6096809) B6096809
theorem B2405801 : Blo 1425532 2405801 := bstep (se 2 (by rfl) ⟨902175, by rfl⟩ : syracuseStep 2405801 = 1804351) B1804351
theorem B10838771 : Blo 1425532 10838771 := bstep (se 1 (by rfl) ⟨8129078, by rfl⟩ : syracuseStep 10838771 = 16258157) B16258157
theorem B1426367 : Blo 1425532 1426367 := bstep (se 1 (by rfl) ⟨1069775, by rfl⟩ : syracuseStep 1426367 = 2139551) B2139551
theorem B10283753 : Blo 1425532 10283753 := bstep (se 2 (by rfl) ⟨3856407, by rfl⟩ : syracuseStep 10283753 = 7712815) B7712815
theorem B3910427 : Blo 1425532 3910427 := bstep (se 1 (by rfl) ⟨2932820, by rfl⟩ : syracuseStep 3910427 = 5865641) B5865641
theorem B55613087 : Blo 1425532 55613087 := bstep (se 1 (by rfl) ⟨41709815, by rfl⟩ : syracuseStep 55613087 = 83419631) B83419631
theorem B3612671 : Blo 1425532 3612671 := bstep (se 1 (by rfl) ⟨2709503, by rfl⟩ : syracuseStep 3612671 = 5419007) B5419007
theorem B1603867 : Blo 1425532 1603867 := bstep (se 1 (by rfl) ⟨1202900, by rfl⟩ : syracuseStep 1603867 = 2405801) B2405801
theorem B2138489 : Blo 1425532 2138489 := bstep (se 2 (by rfl) ⟨801933, by rfl⟩ : syracuseStep 2138489 = 1603867) B1603867
theorem B7225847 : Blo 1425532 7225847 := bstep (se 1 (by rfl) ⟨5419385, by rfl⟩ : syracuseStep 7225847 = 10838771) B10838771
theorem B2408447 : Blo 1425532 2408447 := bstep (se 1 (by rfl) ⟨1806335, by rfl⟩ : syracuseStep 2408447 = 3612671) B3612671
theorem B2606951 : Blo 1425532 2606951 := bstep (se 1 (by rfl) ⟨1955213, by rfl⟩ : syracuseStep 2606951 = 3910427) B3910427
theorem B37075391 : Blo 1425532 37075391 := bstep (se 1 (by rfl) ⟨27806543, by rfl⟩ : syracuseStep 37075391 = 55613087) B55613087
theorem B6855835 : Blo 1425532 6855835 := bstep (se 1 (by rfl) ⟨5141876, by rfl⟩ : syracuseStep 6855835 = 10283753) B10283753
theorem B1425659 : Blo 1425532 1425659 := bstep (se 1 (by rfl) ⟨1069244, by rfl⟩ : syracuseStep 1425659 = 2138489) B2138489
theorem B4817231 : Blo 1425532 4817231 := bstep (se 1 (by rfl) ⟨3612923, by rfl⟩ : syracuseStep 4817231 = 7225847) B7225847
theorem B1737967 : Blo 1425532 1737967 := bstep (se 1 (by rfl) ⟨1303475, by rfl⟩ : syracuseStep 1737967 = 2606951) B2606951
theorem B24716927 : Blo 1425532 24716927 := bstep (se 1 (by rfl) ⟨18537695, by rfl⟩ : syracuseStep 24716927 = 37075391) B37075391
theorem B9141113 : Blo 1425532 9141113 := bstep (se 2 (by rfl) ⟨3427917, by rfl⟩ : syracuseStep 9141113 = 6855835) B6855835
theorem B1605631 : Blo 1425532 1605631 := bstep (se 1 (by rfl) ⟨1204223, by rfl⟩ : syracuseStep 1605631 = 2408447) B2408447
theorem B3211487 : Blo 1425532 3211487 := bstep (se 1 (by rfl) ⟨2408615, by rfl⟩ : syracuseStep 3211487 = 4817231) B4817231
theorem B2140841 : Blo 1425532 2140841 := bstep (se 2 (by rfl) ⟨802815, by rfl⟩ : syracuseStep 2140841 = 1605631) B1605631
theorem B24376301 : Blo 1425532 24376301 := bstep (se 3 (by rfl) ⟨4570556, by rfl⟩ : syracuseStep 24376301 = 9141113) B9141113
theorem B2317289 : Blo 1425532 2317289 := bstep (se 2 (by rfl) ⟨868983, by rfl⟩ : syracuseStep 2317289 = 1737967) B1737967
theorem B65911805 : Blo 1425532 65911805 := bstep (se 3 (by rfl) ⟨12358463, by rfl⟩ : syracuseStep 65911805 = 24716927) B24716927
theorem B1427227 : Blo 1425532 1427227 := bstep (se 1 (by rfl) ⟨1070420, by rfl⟩ : syracuseStep 1427227 = 2140841) B2140841
theorem B6179437 : Blo 1425532 6179437 := bstep (se 3 (by rfl) ⟨1158644, by rfl⟩ : syracuseStep 6179437 = 2317289) B2317289
theorem B2140991 : Blo 1425532 2140991 := bstep (se 1 (by rfl) ⟨1605743, by rfl⟩ : syracuseStep 2140991 = 3211487) B3211487
theorem B16250867 : Blo 1425532 16250867 := bstep (se 1 (by rfl) ⟨12188150, by rfl⟩ : syracuseStep 16250867 = 24376301) B24376301
theorem B43941203 : Blo 1425532 43941203 := bstep (se 1 (by rfl) ⟨32955902, by rfl⟩ : syracuseStep 43941203 = 65911805) B65911805
theorem B1427327 : Blo 1425532 1427327 := bstep (se 1 (by rfl) ⟨1070495, by rfl⟩ : syracuseStep 1427327 = 2140991) B2140991
theorem B10833911 : Blo 1425532 10833911 := bstep (se 1 (by rfl) ⟨8125433, by rfl⟩ : syracuseStep 10833911 = 16250867) B16250867
theorem B8239249 : Blo 1425532 8239249 := bstep (se 2 (by rfl) ⟨3089718, by rfl⟩ : syracuseStep 8239249 = 6179437) B6179437
theorem B29294135 : Blo 1425532 29294135 := bstep (se 1 (by rfl) ⟨21970601, by rfl⟩ : syracuseStep 29294135 = 43941203) B43941203
theorem B43942661 : Blo 1425532 43942661 := bstep (se 4 (by rfl) ⟨4119624, by rfl⟩ : syracuseStep 43942661 = 8239249) B8239249
theorem B7222607 : Blo 1425532 7222607 := bstep (se 1 (by rfl) ⟨5416955, by rfl⟩ : syracuseStep 7222607 = 10833911) B10833911
theorem B19529423 : Blo 1425532 19529423 := bstep (se 1 (by rfl) ⟨14647067, by rfl⟩ : syracuseStep 19529423 = 29294135) B29294135
theorem B29295107 : Blo 1425532 29295107 := bstep (se 1 (by rfl) ⟨21971330, by rfl⟩ : syracuseStep 29295107 = 43942661) B43942661
theorem B13019615 : Blo 1425532 13019615 := bstep (se 1 (by rfl) ⟨9764711, by rfl⟩ : syracuseStep 13019615 = 19529423) B19529423
theorem B4815071 : Blo 1425532 4815071 := bstep (se 1 (by rfl) ⟨3611303, by rfl⟩ : syracuseStep 4815071 = 7222607) B7222607
theorem B19530071 : Blo 1425532 19530071 := bstep (se 1 (by rfl) ⟨14647553, by rfl⟩ : syracuseStep 19530071 = 29295107) B29295107
theorem B8679743 : Blo 1425532 8679743 := bstep (se 1 (by rfl) ⟨6509807, by rfl⟩ : syracuseStep 8679743 = 13019615) B13019615
theorem B3210047 : Blo 1425532 3210047 := bstep (se 1 (by rfl) ⟨2407535, by rfl⟩ : syracuseStep 3210047 = 4815071) B4815071
theorem B2140031 : Blo 1425532 2140031 := bstep (se 1 (by rfl) ⟨1605023, by rfl⟩ : syracuseStep 2140031 = 3210047) B3210047
theorem B5786495 : Blo 1425532 5786495 := bstep (se 1 (by rfl) ⟨4339871, by rfl⟩ : syracuseStep 5786495 = 8679743) B8679743
theorem B13020047 : Blo 1425532 13020047 := bstep (se 1 (by rfl) ⟨9765035, by rfl⟩ : syracuseStep 13020047 = 19530071) B19530071
theorem B1426687 : Blo 1425532 1426687 := bstep (se 1 (by rfl) ⟨1070015, by rfl⟩ : syracuseStep 1426687 = 2140031) B2140031
theorem B8680031 : Blo 1425532 8680031 := bstep (se 1 (by rfl) ⟨6510023, by rfl⟩ : syracuseStep 8680031 = 13020047) B13020047
theorem B3857663 : Blo 1425532 3857663 := bstep (se 1 (by rfl) ⟨2893247, by rfl⟩ : syracuseStep 3857663 = 5786495) B5786495
theorem B5786687 : Blo 1425532 5786687 := bstep (se 1 (by rfl) ⟨4340015, by rfl⟩ : syracuseStep 5786687 = 8680031) B8680031
theorem B10287101 : Blo 1425532 10287101 := bstep (se 3 (by rfl) ⟨1928831, by rfl⟩ : syracuseStep 10287101 = 3857663) B3857663
theorem B6858067 : Blo 1425532 6858067 := bstep (se 1 (by rfl) ⟨5143550, by rfl⟩ : syracuseStep 6858067 = 10287101) B10287101
theorem B15431165 : Blo 1425532 15431165 := bstep (se 3 (by rfl) ⟨2893343, by rfl⟩ : syracuseStep 15431165 = 5786687) B5786687
theorem B9144089 : Blo 1425532 9144089 := bstep (se 2 (by rfl) ⟨3429033, by rfl⟩ : syracuseStep 9144089 = 6858067) B6858067
theorem B10287443 : Blo 1425532 10287443 := bstep (se 1 (by rfl) ⟨7715582, by rfl⟩ : syracuseStep 10287443 = 15431165) B15431165
theorem B6096059 : Blo 1425532 6096059 := bstep (se 1 (by rfl) ⟨4572044, by rfl⟩ : syracuseStep 6096059 = 9144089) B9144089
theorem B27433181 : Blo 1425532 27433181 := bstep (se 3 (by rfl) ⟨5143721, by rfl⟩ : syracuseStep 27433181 = 10287443) B10287443
theorem B4064039 : Blo 1425532 4064039 := bstep (se 1 (by rfl) ⟨3048029, by rfl⟩ : syracuseStep 4064039 = 6096059) B6096059
theorem B18288787 : Blo 1425532 18288787 := bstep (se 1 (by rfl) ⟨13716590, by rfl⟩ : syracuseStep 18288787 = 27433181) B27433181
theorem B24385049 : Blo 1425532 24385049 := bstep (se 2 (by rfl) ⟨9144393, by rfl⟩ : syracuseStep 24385049 = 18288787) B18288787
theorem B2709359 : Blo 1425532 2709359 := bstep (se 1 (by rfl) ⟨2032019, by rfl⟩ : syracuseStep 2709359 = 4064039) B4064039
theorem B16256699 : Blo 1425532 16256699 := bstep (se 1 (by rfl) ⟨12192524, by rfl⟩ : syracuseStep 16256699 = 24385049) B24385049
theorem B1806239 : Blo 1425532 1806239 := bstep (se 1 (by rfl) ⟨1354679, by rfl⟩ : syracuseStep 1806239 = 2709359) B2709359
theorem B4816637 : Blo 1425532 4816637 := bstep (se 3 (by rfl) ⟨903119, by rfl⟩ : syracuseStep 4816637 = 1806239) B1806239
theorem B10837799 : Blo 1425532 10837799 := bstep (se 1 (by rfl) ⟨8128349, by rfl⟩ : syracuseStep 10837799 = 16256699) B16256699
theorem B3211091 : Blo 1425532 3211091 := bstep (se 1 (by rfl) ⟨2408318, by rfl⟩ : syracuseStep 3211091 = 4816637) B4816637
theorem B7225199 : Blo 1425532 7225199 := bstep (se 1 (by rfl) ⟨5418899, by rfl⟩ : syracuseStep 7225199 = 10837799) B10837799
theorem B2140727 : Blo 1425532 2140727 := bstep (se 1 (by rfl) ⟨1605545, by rfl⟩ : syracuseStep 2140727 = 3211091) B3211091
theorem B4816799 : Blo 1425532 4816799 := bstep (se 1 (by rfl) ⟨3612599, by rfl⟩ : syracuseStep 4816799 = 7225199) B7225199
theorem B1427151 : Blo 1425532 1427151 := bstep (se 1 (by rfl) ⟨1070363, by rfl⟩ : syracuseStep 1427151 = 2140727) B2140727
theorem B3211199 : Blo 1425532 3211199 := bstep (se 1 (by rfl) ⟨2408399, by rfl⟩ : syracuseStep 3211199 = 4816799) B4816799
theorem B2140799 : Blo 1425532 2140799 := bstep (se 1 (by rfl) ⟨1605599, by rfl⟩ : syracuseStep 2140799 = 3211199) B3211199
theorem B1427199 : Blo 1425532 1427199 := bstep (se 1 (by rfl) ⟨1070399, by rfl⟩ : syracuseStep 1427199 = 2140799) B2140799

theorem C0 (j : ℕ) (h1 : 356383 ≤ j) (h2 : j ≤ 356882) : Blo 1425532 (4 * j + 3) := by
  interval_cases j
  · exact B1425535
  · exact B1425539
  · exact B1425543
  · exact B1425547
  · exact B1425551
  · exact B1425555
  · exact B1425559
  · exact B1425563
  · exact B1425567
  · exact B1425571
  · exact B1425575
  · exact B1425579
  · exact B1425583
  · exact B1425587
  · exact B1425591
  · exact B1425595
  · exact B1425599
  · exact B1425603
  · exact B1425607
  · exact B1425611
  · exact B1425615
  · exact B1425619
  · exact B1425623
  · exact B1425627
  · exact B1425631
  · exact B1425635
  · exact B1425639
  · exact B1425643
  · exact B1425647
  · exact B1425651
  · exact B1425655
  · exact B1425659
  · exact B1425663
  · exact B1425667
  · exact B1425671
  · exact B1425675
  · exact B1425679
  · exact B1425683
  · exact B1425687
  · exact B1425691
  · exact B1425695
  · exact B1425699
  · exact B1425703
  · exact B1425707
  · exact B1425711
  · exact B1425715
  · exact B1425719
  · exact B1425723
  · exact B1425727
  · exact B1425731
  · exact B1425735
  · exact B1425739
  · exact B1425743
  · exact B1425747
  · exact B1425751
  · exact B1425755
  · exact B1425759
  · exact B1425763
  · exact B1425767
  · exact B1425771
  · exact B1425775
  · exact B1425779
  · exact B1425783
  · exact B1425787
  · exact B1425791
  · exact B1425795
  · exact B1425799
  · exact B1425803
  · exact B1425807
  · exact B1425811
  · exact B1425815
  · exact B1425819
  · exact B1425823
  · exact B1425827
  · exact B1425831
  · exact B1425835
  · exact B1425839
  · exact B1425843
  · exact B1425847
  · exact B1425851
  · exact B1425855
  · exact B1425859
  · exact B1425863
  · exact B1425867
  · exact B1425871
  · exact B1425875
  · exact B1425879
  · exact B1425883
  · exact B1425887
  · exact B1425891
  · exact B1425895
  · exact B1425899
  · exact B1425903
  · exact B1425907
  · exact B1425911
  · exact B1425915
  · exact B1425919
  · exact B1425923
  · exact B1425927
  · exact B1425931
  · exact B1425935
  · exact B1425939
  · exact B1425943
  · exact B1425947
  · exact B1425951
  · exact B1425955
  · exact B1425959
  · exact B1425963
  · exact B1425967
  · exact B1425971
  · exact B1425975
  · exact B1425979
  · exact B1425983
  · exact B1425987
  · exact B1425991
  · exact B1425995
  · exact B1425999
  · exact B1426003
  · exact B1426007
  · exact B1426011
  · exact B1426015
  · exact B1426019
  · exact B1426023
  · exact B1426027
  · exact B1426031
  · exact B1426035
  · exact B1426039
  · exact B1426043
  · exact B1426047
  · exact B1426051
  · exact B1426055
  · exact B1426059
  · exact B1426063
  · exact B1426067
  · exact B1426071
  · exact B1426075
  · exact B1426079
  · exact B1426083
  · exact B1426087
  · exact B1426091
  · exact B1426095
  · exact B1426099
  · exact B1426103
  · exact B1426107
  · exact B1426111
  · exact B1426115
  · exact B1426119
  · exact B1426123
  · exact B1426127
  · exact B1426131
  · exact B1426135
  · exact B1426139
  · exact B1426143
  · exact B1426147
  · exact B1426151
  · exact B1426155
  · exact B1426159
  · exact B1426163
  · exact B1426167
  · exact B1426171
  · exact B1426175
  · exact B1426179
  · exact B1426183
  · exact B1426187
  · exact B1426191
  · exact B1426195
  · exact B1426199
  · exact B1426203
  · exact B1426207
  · exact B1426211
  · exact B1426215
  · exact B1426219
  · exact B1426223
  · exact B1426227
  · exact B1426231
  · exact B1426235
  · exact B1426239
  · exact B1426243
  · exact B1426247
  · exact B1426251
  · exact B1426255
  · exact B1426259
  · exact B1426263
  · exact B1426267
  · exact B1426271
  · exact B1426275
  · exact B1426279
  · exact B1426283
  · exact B1426287
  · exact B1426291
  · exact B1426295
  · exact B1426299
  · exact B1426303
  · exact B1426307
  · exact B1426311
  · exact B1426315
  · exact B1426319
  · exact B1426323
  · exact B1426327
  · exact B1426331
  · exact B1426335
  · exact B1426339
  · exact B1426343
  · exact B1426347
  · exact B1426351
  · exact B1426355
  · exact B1426359
  · exact B1426363
  · exact B1426367
  · exact B1426371
  · exact B1426375
  · exact B1426379
  · exact B1426383
  · exact B1426387
  · exact B1426391
  · exact B1426395
  · exact B1426399
  · exact B1426403
  · exact B1426407
  · exact B1426411
  · exact B1426415
  · exact B1426419
  · exact B1426423
  · exact B1426427
  · exact B1426431
  · exact B1426435
  · exact B1426439
  · exact B1426443
  · exact B1426447
  · exact B1426451
  · exact B1426455
  · exact B1426459
  · exact B1426463
  · exact B1426467
  · exact B1426471
  · exact B1426475
  · exact B1426479
  · exact B1426483
  · exact B1426487
  · exact B1426491
  · exact B1426495
  · exact B1426499
  · exact B1426503
  · exact B1426507
  · exact B1426511
  · exact B1426515
  · exact B1426519
  · exact B1426523
  · exact B1426527
  · exact B1426531
  · exact B1426535
  · exact B1426539
  · exact B1426543
  · exact B1426547
  · exact B1426551
  · exact B1426555
  · exact B1426559
  · exact B1426563
  · exact B1426567
  · exact B1426571
  · exact B1426575
  · exact B1426579
  · exact B1426583
  · exact B1426587
  · exact B1426591
  · exact B1426595
  · exact B1426599
  · exact B1426603
  · exact B1426607
  · exact B1426611
  · exact B1426615
  · exact B1426619
  · exact B1426623
  · exact B1426627
  · exact B1426631
  · exact B1426635
  · exact B1426639
  · exact B1426643
  · exact B1426647
  · exact B1426651
  · exact B1426655
  · exact B1426659
  · exact B1426663
  · exact B1426667
  · exact B1426671
  · exact B1426675
  · exact B1426679
  · exact B1426683
  · exact B1426687
  · exact B1426691
  · exact B1426695
  · exact B1426699
  · exact B1426703
  · exact B1426707
  · exact B1426711
  · exact B1426715
  · exact B1426719
  · exact B1426723
  · exact B1426727
  · exact B1426731
  · exact B1426735
  · exact B1426739
  · exact B1426743
  · exact B1426747
  · exact B1426751
  · exact B1426755
  · exact B1426759
  · exact B1426763
  · exact B1426767
  · exact B1426771
  · exact B1426775
  · exact B1426779
  · exact B1426783
  · exact B1426787
  · exact B1426791
  · exact B1426795
  · exact B1426799
  · exact B1426803
  · exact B1426807
  · exact B1426811
  · exact B1426815
  · exact B1426819
  · exact B1426823
  · exact B1426827
  · exact B1426831
  · exact B1426835
  · exact B1426839
  · exact B1426843
  · exact B1426847
  · exact B1426851
  · exact B1426855
  · exact B1426859
  · exact B1426863
  · exact B1426867
  · exact B1426871
  · exact B1426875
  · exact B1426879
  · exact B1426883
  · exact B1426887
  · exact B1426891
  · exact B1426895
  · exact B1426899
  · exact B1426903
  · exact B1426907
  · exact B1426911
  · exact B1426915
  · exact B1426919
  · exact B1426923
  · exact B1426927
  · exact B1426931
  · exact B1426935
  · exact B1426939
  · exact B1426943
  · exact B1426947
  · exact B1426951
  · exact B1426955
  · exact B1426959
  · exact B1426963
  · exact B1426967
  · exact B1426971
  · exact B1426975
  · exact B1426979
  · exact B1426983
  · exact B1426987
  · exact B1426991
  · exact B1426995
  · exact B1426999
  · exact B1427003
  · exact B1427007
  · exact B1427011
  · exact B1427015
  · exact B1427019
  · exact B1427023
  · exact B1427027
  · exact B1427031
  · exact B1427035
  · exact B1427039
  · exact B1427043
  · exact B1427047
  · exact B1427051
  · exact B1427055
  · exact B1427059
  · exact B1427063
  · exact B1427067
  · exact B1427071
  · exact B1427075
  · exact B1427079
  · exact B1427083
  · exact B1427087
  · exact B1427091
  · exact B1427095
  · exact B1427099
  · exact B1427103
  · exact B1427107
  · exact B1427111
  · exact B1427115
  · exact B1427119
  · exact B1427123
  · exact B1427127
  · exact B1427131
  · exact B1427135
  · exact B1427139
  · exact B1427143
  · exact B1427147
  · exact B1427151
  · exact B1427155
  · exact B1427159
  · exact B1427163
  · exact B1427167
  · exact B1427171
  · exact B1427175
  · exact B1427179
  · exact B1427183
  · exact B1427187
  · exact B1427191
  · exact B1427195
  · exact B1427199
  · exact B1427203
  · exact B1427207
  · exact B1427211
  · exact B1427215
  · exact B1427219
  · exact B1427223
  · exact B1427227
  · exact B1427231
  · exact B1427235
  · exact B1427239
  · exact B1427243
  · exact B1427247
  · exact B1427251
  · exact B1427255
  · exact B1427259
  · exact B1427263
  · exact B1427267
  · exact B1427271
  · exact B1427275
  · exact B1427279
  · exact B1427283
  · exact B1427287
  · exact B1427291
  · exact B1427295
  · exact B1427299
  · exact B1427303
  · exact B1427307
  · exact B1427311
  · exact B1427315
  · exact B1427319
  · exact B1427323
  · exact B1427327
  · exact B1427331
  · exact B1427335
  · exact B1427339
  · exact B1427343
  · exact B1427347
  · exact B1427351
  · exact B1427355
  · exact B1427359
  · exact B1427363
  · exact B1427367
  · exact B1427371
  · exact B1427375
  · exact B1427379
  · exact B1427383
  · exact B1427387
  · exact B1427391
  · exact B1427395
  · exact B1427399
  · exact B1427403
  · exact B1427407
  · exact B1427411
  · exact B1427415
  · exact B1427419
  · exact B1427423
  · exact B1427427
  · exact B1427431
  · exact B1427435
  · exact B1427439
  · exact B1427443
  · exact B1427447
  · exact B1427451
  · exact B1427455
  · exact B1427459
  · exact B1427463
  · exact B1427467
  · exact B1427471
  · exact B1427475
  · exact B1427479
  · exact B1427483
  · exact B1427487
  · exact B1427491
  · exact B1427495
  · exact B1427499
  · exact B1427503
  · exact B1427507
  · exact B1427511
  · exact B1427515
  · exact B1427519
  · exact B1427523
  · exact B1427527
  · exact B1427531

theorem solution (m : ℕ) (hlo : 1425532 ≤ m) (hhi : m ≤ 1427532) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 356383 ≤ j := by omega
    have hj2 : j ≤ 356882 := by omega
    have hb : Blo 1425532 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
